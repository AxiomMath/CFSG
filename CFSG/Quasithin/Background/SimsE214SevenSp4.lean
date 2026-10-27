module

public import CFSG.Quasithin.Background.SimsE214SevenSec
public import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.Quasithin.Background.SmithB42Sp4Ident

public section

namespace CFSG.Quasithin.SimsE2

namespace E214S

open CFSG.Quasithin CFSG.Quasithin.B42Sp4 CFSG.QuasithinUnique.Setup.X7b
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section Rep

variable {F : Type} [Field F] [CharP F 2] [Fintype F]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem finrank_eq_four_of_card_lt {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) [Fact (repOf π).IsIrreducible]
    (hnt : ∃ g, repOf π g ≠ 1) (hcard : Nat.card M < 2 ^ (8 * f)) :
    Module.finrank (EndRing (repOf π)) M = 4 := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sp4_descent hF hf hnt
  have : Module.Finite (EndRing (repOf π)) M := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, S, hSne, hS, -, hshift, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing (repOf π)) M)
  have hfd : f ≤ S.card * d := by
    have h := n_le_card_mul (n := 2 * f) (d := 2 * d) (by omega) (by omega)
      (fun i hi => Finset.mem_range.mp (hS hi)) hSne hshift
    have h2 : 2 * f ≤ 2 * (S.card * d) := by
      calc 2 * f ≤ S.card * (2 * d) := h
        _ = 2 * (S.card * d) := by ring
    omega
  have hM : Nat.card M = 2 ^ (d * 4 ^ S.card) := by
    rw [natCard_eq_pow_finrank (ρ := repOf π), hDcard, hdimW, ← pow_mul]
  rw [hM] at hcard
  have h1 : d * 4 ^ S.card < 8 * f := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hcard
  rw [hdimW]
  have hs1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  by_contra hne
  have hs2 : 2 ≤ S.card := by
    by_contra h
    have h' : S.card = 1 := by omega
    rw [h', pow_one] at hne
    exact hne rfl
  have h8 := Nat.mul_le_mul_left d (eight_mul_le_four_pow hs2)
  nlinarith

theorem exists_apply_eq_of_card_lt {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) [Fact (repOf π).IsIrreducible]
    (hnt : ∃ g, repOf π g ≠ 1) (hcard : Nat.card M < 2 ^ (8 * f)) {w₁ w₂ : M} (h₁ : w₁ ≠ 0)
    (h₂ : w₂ ≠ 0) : ∃ g : antiSp F, π g w₁ = w₂ := by
  obtain ⟨i, φ, hφ⟩ :=
    exists_natural_of_four hF hf π hnt (finrank_eq_four_of_card_lt hF hf π hnt hcard)
  have hu : φ w₁ ≠ 0 := fun h => h₁ (φ.injective (h.trans φ.map_zero.symm))
  have hv : φ w₂ ≠ 0 := fun h => h₂ (φ.injective (h.trans φ.map_zero.symm))
  obtain ⟨y, hy⟩ := antiSp_exists_mulVec_eq hu hv
  refine ⟨(minorAut F ^ i).symm y, φ.injective ?_⟩
  rw [hφ, MulEquiv.apply_symm_apply, hy]

omit [Fintype F] in
theorem exists_apply_eq_of_irr_lt [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    {Q : Type} [CommGroup Q] [Finite Q] (hQ : ∀ q : Q, q * q = 1) (ρ : antiSp F →* MulAut Q)
    (hirr : ∀ Y : Subgroup Q, (∀ γ, ∀ q ∈ Y, ρ γ q ∈ Y) → Y = ⊥ ∨ Y = ⊤) (hnt : ρ ≠ 1)
    (hcard : Nat.card Q < 2 ^ (8 * f)) {q₁ q₂ : Q} (h₁ : q₁ ≠ 1) (h₂ : q₂ ≠ 1) :
    ∃ γ : antiSp F, ρ γ q₁ = q₂ := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  have hFf : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hF
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hQ
  let π : antiSp F →* (W ≃ₗ[ZMod 2] W) := (binPsi θ).toMonoidHom.comp ρ
  have hπ : ∀ γ w, π γ w = binPsi θ (ρ γ) w := fun _ _ => rfl
  have hirrQ : ∀ Y : Subgroup Q, (∀ l ∈ ρ.range, ∀ v ∈ Y, l v ∈ Y) → Y = ⊥ ∨ Y = ⊤ :=
    fun Y hY => hirr Y fun γ q hq => hY _ ⟨γ, rfl⟩ q hq
  have hirrW : ∀ U : Submodule (ZMod 2) W, (∀ γ, ∀ u ∈ U, π γ u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirrQ U ?_
    rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩ u hu
    exact hU γ u hu
  have hWQ : Nat.card W = Nat.card Q :=
    (Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)).symm
  have : Nontrivial Q := nontrivial_of_ne q₁ 1 h₁
  have : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hWQ]
    exact Finite.one_lt_card)
  have : Fact (repOf π).IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (repOf π)).mpr ⟨inferInstance, hirrW⟩⟩
  have hntπ : ∃ γ, repOf π γ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hnt
    ext γ q
    have h2 : π γ = π 1 :=
      LinearEquiv.toLinearMap_injective ((hall γ).trans (map_one (repOf π)).symm)
    rw [map_one] at h2
    have h3 : ρ γ = 1 := by
      apply (binPsi θ).injective
      rw [map_one]
      exact h2
    rw [h3]
    rfl
  have hw : ∀ q : Q, q ≠ 1 → Multiplicative.toAdd (θ q) ≠ 0 := by
    intro q hq h0
    apply hq
    have h1 : θ q = 1 := Multiplicative.toAdd.injective h0
    rwa [MulEquiv.map_eq_one_iff] at h1
  obtain ⟨γ, hγ⟩ := exists_apply_eq_of_card_lt hFf hf π hntπ (hWQ.trans_lt hcard)
    (hw q₁ h₁) (hw q₂ h₂)
  refine ⟨γ, θ.injective (Multiplicative.toAdd.injective ?_)⟩
  rw [← B42L2.toAdd_binPsi, ← hπ]
  exact hγ

end Rep

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem Sec.exists_conj_of_antiSp {I P Z J : Subgroup Γ} (hS : Sec I P Z J)
    [(Z.subgroupOf P).Normal] [(J.subgroupOf I).Normal] {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    (e : ↥I ⧸ J.subgroupOf I ≃* antiSp F) (hnt : ∃ i ∈ I, ∃ y ∈ P, i * y * i⁻¹ * y⁻¹ ∉ Z)
    (hcard : Z.relIndex P < 2 ^ (8 * f)) {x b : Γ} (hx : x ∈ P) (hxZ : x ∉ Z) (hb : b ∈ P)
    (hbZ : b ∉ Z) : ∃ i ∈ I, (i * b * i⁻¹)⁻¹ * x ∈ Z := by
  letI : CommGroup (↥P ⧸ Z.subgroupOf P) :=
    { (inferInstance : Group (↥P ⧸ Z.subgroupOf P)) with mul_comm := hS.comm_quot }
  let ρ : antiSp F →* MulAut (↥P ⧸ Z.subgroupOf P) := hS.starAct.comp e.symm.toMonoidHom
  have hρ : ∀ i : I, ρ (e (i : ↥I ⧸ J.subgroupOf I)) = hS.act i := by
    intro i
    show hS.starAct (e.symm (e _)) = _
    rw [MulEquiv.symm_apply_apply, hS.starAct_mk]
  have hirr : ∀ Y : Subgroup (↥P ⧸ Z.subgroupOf P), (∀ γ, ∀ q ∈ Y, ρ γ q ∈ Y) →
      Y = ⊥ ∨ Y = ⊤ := by
    intro Y hY
    refine hS.irr_quot Y fun i q hq => ?_
    rw [← hρ]
    exact hY _ q hq
  have hnt' : ρ ≠ 1 := by
    intro h1
    obtain ⟨i, hi, y, hy, hyZ⟩ := hnt
    apply hyZ
    have h2 : hS.act ⟨i, hi⟩ = 1 := by rw [← hρ, h1, MonoidHom.one_apply]
    exact (Dih.conjSecAut_eq_one_iff ⟨i, hi⟩).1 h2 y hy
  have h1 : ((⟨b, hb⟩ : P) : ↥P ⧸ Z.subgroupOf P) ≠ 1 := fun h => hbZ ((Sec.mk_eq_one_iff _).1 h)
  have h2 : ((⟨x, hx⟩ : P) : ↥P ⧸ Z.subgroupOf P) ≠ 1 := fun h => hxZ ((Sec.mk_eq_one_iff _).1 h)
  obtain ⟨γ, hγ⟩ := exists_apply_eq_of_irr_lt hF hf hS.sq_quot ρ hirr hnt' hcard h1 h2
  obtain ⟨i', hi'⟩ := e.surjective γ
  obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective i'
  rw [← hi', hρ] at hγ
  exact ⟨i, i.2, hS.conj_mem_of_act hx hb hγ⟩

end E214S

end CFSG.Quasithin.SimsE2
