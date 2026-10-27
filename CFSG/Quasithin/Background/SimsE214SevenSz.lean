module

public import CFSG.Quasithin.Background.SimsE214SevenSec
public import CFSG.Quasithin.Background.SmithB45SzNat

public section

namespace CFSG.Quasithin.SimsE2

namespace E214S

open CFSG.Quasithin CFSG.Quasithin.B45Sz CFSG.QuasithinUnique.Setup.X7b
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.Blueprint

section Rep

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem sz_finrank_eq_four_of_card
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (π : ↥(suzukiGroup a K) →* (M ≃ₗ[ZMod 2] M))
    [Fact (repOfG π).IsIrreducible] (hnt : ∃ g, repOfG π g ≠ 1)
    (hcard : Nat.card M = 2 ^ (4 * (2 * a + 1))) :
    Module.finrank (EndRing (repOfG π)) M = 4 := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sz_descent hK hnt
  have : Module.Finite (EndRing (repOfG π)) M := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιK, ιD, A, hAne, hA, -, hshift, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing (repOfG π)) M)
  have hfd := le_card_mul_of_shiftSet hA hAne hd1 hshift
  have hM : Nat.card M = 2 ^ (d * 4 ^ A.card) := by
    rw [natCard_eq_pow_finrank (ρ := repOfG π), hDcard, hdimW, ← pow_mul]
  rw [hM] at hcard
  have h1 : d * 4 ^ A.card = 4 * (2 * a + 1) := Nat.pow_right_injective le_rfl hcard
  rw [hdimW]
  have hs1 : 1 ≤ A.card := Finset.card_pos.mpr hAne
  by_contra hne
  have hs2 : 2 ≤ A.card := by
    by_contra h
    have h' : A.card = 1 := by omega
    rw [h', pow_one] at hne
    exact hne rfl
  have h8 := Nat.mul_le_mul_left d (B42Sp4.eight_mul_le_four_pow hs2)
  nlinarith

theorem sz_exists_natural (hK : Nat.card K = 2 ^ (2 * a + 1))
    (π : ↥(suzukiGroup a K) →* (M ≃ₗ[ZMod 2] M)) [Fact (repOfG π).IsIrreducible]
    (hnt : ∃ g, repOfG π g ≠ 1) (hdim : Module.finrank (EndRing (repOfG π)) M = 4) :
    ∃ φ : M ≃+ (Fin 4 → K), ∀ g w,
      φ (π g w) = (glMat (g : GL (Fin 4) K)).mulVec (φ w) := by
  obtain ⟨c, φ, hφ⟩ := sz_exists_natural_of_four hK π hnt hdim
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 c
  let φ' : M ≃+ (Fin 4 → K) := φ.trans (AddEquiv.piCongrRight fun _ : Fin 4 => σ.symm.toAddEquiv)
  refine ⟨φ', fun g w => ?_⟩
  funext j
  have h1 := congrFun (hφ g w) j
  show σ.symm (φ (π g w) j) = _
  rw [h1, Matrix.mulVec, dotProduct, map_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [map_mul, Matrix.map_apply]
  have hσ : σ.symm (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) j c' ^ 2 ^ c) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) j c' := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  rw [hσ]
  rfl

end Rep

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem Sec.isNaturalSection_of_sz {I P Z J : Subgroup Γ}
    (hS : Sec I P Z J) [(Z.subgroupOf P).Normal] [(J.subgroupOf I).Normal] {a : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : ↥I ⧸ J.subgroupOf I ≃* ↥(suzukiGroup a K))
    (hnt : ∃ i ∈ I, ∃ y ∈ P, i * y * i⁻¹ * y⁻¹ ∉ Z)
    (hcard : Z.relIndex P = 2 ^ (4 * (2 * a + 1))) :
    IsNaturalSection I P Z J (suzukiGroup a K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  letI : CommGroup (↥P ⧸ Z.subgroupOf P) :=
    { (inferInstance : Group (↥P ⧸ Z.subgroupOf P)) with mul_comm := hS.comm_quot }
  let ρ : ↥(suzukiGroup a K) →* MulAut (↥P ⧸ Z.subgroupOf P) :=
    hS.starAct.comp e.symm.toMonoidHom
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
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hS.sq_quot
  let π : ↥(suzukiGroup a K) →* (W ≃ₗ[ZMod 2] W) := (binPsi θ).toMonoidHom.comp ρ
  have hπ : ∀ γ w, π γ w = binPsi θ (ρ γ) w := fun _ _ => rfl
  have hirrQ : ∀ Y : Subgroup (↥P ⧸ Z.subgroupOf P), (∀ l ∈ ρ.range, ∀ v ∈ Y, l v ∈ Y) →
      Y = ⊥ ∨ Y = ⊤ :=
    fun Y hY => hirr Y fun γ q hq => hY _ ⟨γ, rfl⟩ q hq
  have hirrW : ∀ U : Submodule (ZMod 2) W, (∀ γ, ∀ u ∈ U, repOfG π γ u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirrQ U ?_
    rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩ u hu
    exact hU γ u hu
  have hWQ : Nat.card W = Nat.card (↥P ⧸ Z.subgroupOf P) :=
    (Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)).symm
  have hQnt : Nontrivial (↥P ⧸ Z.subgroupOf P) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have h2 := hS.two_dvd_card
    have h0 : 0 < Nat.card (↥P ⧸ Z.subgroupOf P) := Nat.card_pos
    have := Nat.le_of_dvd h0 h2
    omega
  have : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hWQ]
    exact Finite.one_lt_card)
  have : Fact (repOfG π).IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (repOfG π)).mpr ⟨inferInstance, hirrW⟩⟩
  have hntπ : ∃ γ, repOfG π γ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hnt'
    ext γ q
    have h2 : π γ = π 1 :=
      LinearEquiv.toLinearMap_injective ((hall γ).trans (map_one (repOfG π)).symm)
    rw [map_one] at h2
    have h3 : ρ γ = 1 := by
      apply (binPsi θ).injective
      rw [map_one]
      exact h2
    rw [h3]
    rfl
  have hdim := sz_finrank_eq_four_of_card hK π hntπ (hWQ.trans hcard)
  obtain ⟨φ, hφ⟩ := sz_exists_natural hK π hntπ hdim
  let ρI : ↥I →* ↥(suzukiGroup a K) := e.toMonoidHom.comp (QuotientGroup.mk' (J.subgroupOf I))
  have hρI : ∀ i : I, ρI i = e (i : ↥I ⧸ J.subgroupOf I) := fun _ => rfl
  let ψ : ↥P →* Multiplicative (Fin 4 → K) :=
    ((AddEquiv.toMultiplicative φ).toMonoidHom.comp θ.toMonoidHom).comp
      (QuotientGroup.mk' (Z.subgroupOf P))
  have hψ : ∀ u : P, ψ u =
      Multiplicative.ofAdd (φ (Multiplicative.toAdd (θ (u : ↥P ⧸ Z.subgroupOf P))))  :=
    fun _ => rfl
  refine ⟨hS.ZP, hS.JI, hS.IP, hS.IZ, ρI, ψ, e.surjective.comp (QuotientGroup.mk'_surjective _),
    ?_, ?_, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, hρI, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  · intro y
    obtain ⟨w, hw⟩ := φ.surjective (Multiplicative.toAdd y)
    obtain ⟨q, hq⟩ := θ.surjective (Multiplicative.ofAdd w)
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨u, ?_⟩
    rw [hψ, hq, toAdd_ofAdd, hw, ofAdd_toAdd]
  · ext u
    rw [MonoidHom.mem_ker, hψ, ← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq,
      ← map_zero φ, φ.apply_eq_iff_eq, ← toAdd_one, Multiplicative.toAdd.apply_eq_iff_eq,
      MulEquiv.map_eq_one_iff, Sec.mk_eq_one_iff, Subgroup.mem_subgroupOf]
  · intro i u v huv
    have hv : v = ⟨(i : Γ) * u * (i : Γ)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hS.IP i.2) u).mp u.2⟩ := Subtype.ext huv
    have hmk : (v : ↥P ⧸ Z.subgroupOf P) = ρ (ρI i) (u : ↥P ⧸ Z.subgroupOf P) := by
      rw [hρI, hρ, hS.act_mk, hv]
    rw [hψ, hψ, toAdd_ofAdd, hmk, ← B42L2.toAdd_binPsi θ, ← hπ, hφ]

end E214S

end CFSG.Quasithin.SimsE2
