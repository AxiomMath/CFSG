module

public import CFSG.RankThree.PartOne.SEITZ11.G2SevenGen
public import CFSG.RankThree.PartOne.SEITZ3.PlaneCount
public import CFSG.RankThree.PartOne.KE.A1Centralizer

public section

namespace CFSG.RankThree.PartOne.SEITZ11.G2Seven

open Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.SEITZ3

theorem exists_quadratic_ext {K : Type} [Field K] [Finite K] :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (_ : Algebra K K₂) (σ : K₂ ≃+* K₂),
      Module.finrank K K₂ = 2 ∧ ∀ c, σ c = c ^ Nat.card K := by
  have : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime :=
    ⟨(CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
      (CharP.ringChar_ne_zero_of_finite K)⟩
  exact ⟨FiniteField.Extension K (ringChar K) 2, inferInstance, inferInstance, inferInstance,
    (FiniteField.Extension.frob K (ringChar K) 2).toRingEquiv,
    FiniteField.finrank_extension K (ringChar K) 2, fun c => by simp⟩

section Generic

variable {G G' : Type*} [Group G] [Group G']

theorem cenGen_map (ε : G ≃* G') (E : Subgroup G) :
    cenGen (E.map ε.toMonoidHom) = ε '' cenGen E := by
  ext k
  constructor
  · rintro ⟨x, ⟨x₀, hx₀, rfl⟩, hx1, hk⟩
    refine ⟨ε.symm k, ⟨x₀, hx₀, ?_, ?_⟩, by simp⟩
    · rintro rfl
      exact hx1 (map_one _)
    · apply ε.injective
      simpa using hk
  · rintro ⟨k₀, ⟨x₀, hx₀, hx1, hk⟩, rfl⟩
    refine ⟨ε x₀, ⟨x₀, hx₀, rfl⟩, ?_, ?_⟩
    · intro h
      exact hx1 (ε.injective (by simpa using h))
    · rw [← map_mul, ← map_mul, hk]

theorem closure_cenGen_eq_top_of_map (ε : G ≃* G') (E : Subgroup G)
    (h : closure (cenGen (E.map ε.toMonoidHom)) = ⊤) : closure (cenGen E) = ⊤ := by
  rw [cenGen_map] at h
  have h1 : closure (⇑ε.toMonoidHom '' cenGen E) = ⊤ := h
  rw [← MonoidHom.map_closure] at h1
  have h2 := congrArg (Subgroup.comap ε.toMonoidHom) h1
  rwa [Subgroup.comap_map_eq_self_of_injective ε.injective, Subgroup.comap_top] at h2

theorem plane_conj [Finite G] {p : ℕ} [Fact p.Prime] (S₀ : Sylow p G) {T : Subgroup G}
    (hS₀T : (S₀ : Subgroup G) ≤ T) {E : Subgroup G} (hE : ∀ x ∈ T, x ^ p = 1 → x ∈ E)
    (hEc : Nat.card E = p ^ 2) {F : Subgroup G} (hF : ∀ x ∈ F, x ^ p = 1)
    (hFc : Nat.card F = p ^ 2) : ∃ h : G, F = cj E h := by
  have hFp : IsPGroup p F := IsPGroup.of_card (n := 2) hFc
  obtain ⟨S', hS'⟩ := hFp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S₀ S'
  have hle : F ≤ cj E h := by
    intro x hx
    have hx' : x ∈ (S' : Subgroup G) := hS' hx
    rw [← hh, Sylow.coe_subgroup_smul] at hx'
    have h1 : h⁻¹ * x * h ∈ (S₀ : Subgroup G) := by
      have := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hx'
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using this
    rw [mem_cj]
    refine hE _ (hS₀T h1) ?_
    have hxp := hF x hx
    calc (h⁻¹ * x * h) ^ p = h⁻¹ * x ^ p * h := by
          simpa [inv_inv] using conj_pow (a := h⁻¹) (b := x) (i := p)
      _ = 1 := by rw [hxp]; simp
  exact ⟨h, Subgroup.eq_of_le_of_card_ge hle (by rw [card_cj, hEc, hFc])⟩

end Generic

section Torus

variable {L : Type} [Field L]

@[expose] def chiHom (β : Fin Tag.G2.rank → ℤ) : (Fin Tag.G2.rank → Lˣ) →* Lˣ where
  toFun a := rootChar a β
  map_one' := by simp [rootChar]
  map_mul' a b := by simp [rootChar, mul_zpow, Finset.prod_mul_distrib]

@[expose] def torsionParams (L : Type) [Field L] (p : ℕ) : Subgroup (Fin Tag.G2.rank → Lˣ) :=
  Subgroup.pi Set.univ fun _ => rootsOfUnity p L

theorem mem_torsionParams {p : ℕ} {a : Fin Tag.G2.rank → Lˣ} :
    a ∈ torsionParams L p ↔ ∀ i, a i ^ p = 1 := by
  simp [torsionParams, Subgroup.mem_pi]

theorem exists_ker [Finite L] {p : ℕ} (hp : p.Prime) (hcard : Nat.card (torsionParams L p) = p ^ 2)
    (β : Fin Tag.G2.rank → ℤ) :
    ∃ a ∈ torsionParams L p, a ≠ 1 ∧ rootChar a β = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  set f : torsionParams L p →* Lˣ := (chiHom β).comp (torsionParams L p).subtype with hf
  have hrange : f.range ≤ rootsOfUnity p L := by
    rintro _ ⟨a, rfl⟩
    have ha := mem_torsionParams.1 a.2
    show (chiHom β) a.1 ^ p = 1
    rw [← map_pow]
    have : (a.1 ^ p : Fin Tag.G2.rank → Lˣ) = 1 := funext fun i => ha i
    rw [this, map_one]
  have h1 : Nat.card f.range ≤ p :=
    (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity L p)
  have h2 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hcard] at h2
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have hp2 := hp.two_le
  have h3 : p ≤ Nat.card f.ker := by
    by_contra h
    push Not at h
    nlinarith
  have h4 : 1 < Nat.card f.ker := by omega
  have h5 := (Subgroup.one_lt_card_iff_ne_bot f.ker).1 h4
  obtain ⟨⟨a, ha⟩, hne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h5
  exact ⟨a.1, a.2, fun h => hne (Subtype.ext (Subtype.ext h)), MonoidHom.mem_ker.1 ha⟩

end Torus


section Consumer

theorem closure_cenGen_adjointG2_odd_qplus_eq_top
    (X : Type) [Field X] [Finite X] (hX : Odd (Nat.card X)) (h11 : 11 ≤ Nat.card X)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card X + 1)
    (E₁ : Subgroup (adjointGroup Tag.G2 X)) (hE₁p : ∀ x ∈ E₁, x ^ p = 1)
    (hE₁c : Nat.card E₁ = p ^ 2) :
    Subgroup.closure (cenGen E₁) = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₂, hF₂, hfin₂, hAlg, σ, hdeg, hσ⟩ := exists_quadratic_ext (K := X)
  obtain ⟨g, z, hg, -, hzdef, ⟨hz, hw⟩, hΓ, -, -, ⟨S₀, hS₀⟩, ⟨E, hEmem, hEle, hEcard, -, -⟩,
      -, -, hcent⟩ :=
    odd_G2_qplus_toral_Sylow_and_fixed_root_centralizers X hX hp (by omega) hpq K₂ hdeg σ hσ
  have hGEN := g2_qplus_generation hX (by omega) K₂ hdeg σ hσ hg hzdef hz hw
  have : Finite (ModGL Tag.G2 K₂) := finite_modGL
  let Γ : Subgroup (ModGL Tag.G2 K₂) := conjEntrywiseImage X g
  have hEΓ : E ≤ Γ := fun x hx => (hEle hx).2
  have hmapE : (torsionParams K₂ p).map (rootDiagUnitHom Tag.G2 K₂) = E := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine (hEmem _).2 ⟨rootDiagUnit_mem_torusGroup_G2 a, ?_⟩
      show rootDiagUnit Tag.G2 a ^ p = 1
      have hap : a ^ p = 1 := funext fun i => mem_torsionParams.1 ha i
      rw [rootDiagUnit_pow, hap, rootDiagUnit_one]
    · intro hx
      obtain ⟨hxT, hxp⟩ := (hEmem x).1 hx
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
      refine ⟨a, ?_, rfl⟩
      have h1 : rootDiagUnit Tag.G2 (a ^ p) = rootDiagUnit Tag.G2 (1 : Fin Tag.G2.rank → K₂ˣ) := by
        rw [← rootDiagUnit_pow, hxp, rootDiagUnit_one]
      have h2 : a ^ p = 1 := rootDiagUnit_injective h1
      exact mem_torsionParams.2 fun i => congrFun h2 i
  have hcardAp : Nat.card (torsionParams K₂ p) = p ^ 2 := by
    rw [← hEcard, ← hmapE]
    exact (Subgroup.card_map_of_injective rootDiagUnit_injective).symm
  have hroot : ∀ β, IsRoot Tag.G2 β → ∀ r ∈ rootRankOneGroup Tag.G2 K₂ β ⊓ Γ,
      ∃ hrΓ : r ∈ Γ, (⟨r, hrΓ⟩ : Γ) ∈ cenGen (E.subgroupOf Γ) := by
    intro β hβ r hr
    obtain ⟨a, haT, ha1, hachar⟩ := exists_ker hp hcardAp β
    have hxE : rootDiagUnit Tag.G2 a ∈ E := hmapE ▸ ⟨a, haT, rfl⟩
    have hxTΓ := hEle hxE
    have hxp : rootDiagUnit Tag.G2 a ^ p = 1 := ((hEmem _).1 hxE).2
    have hx1 : rootDiagUnit Tag.G2 a ≠ 1 := fun h =>
      ha1 (rootDiagUnit_injective (h.trans rootDiagUnit_one.symm))
    have hord : orderOf (rootDiagUnit Tag.G2 a) = p := orderOf_eq_prime hxp hx1
    obtain ⟨-, hne⟩ := hcent a hxTΓ hord
    have hker : rootCharKernel a ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨β, hβ, hachar⟩
    obtain ⟨α, hα, hkerα, hcomm, -⟩ := hne hker
    have hβα : β = α ∨ β = -α := by
      have : β ∈ rootCharKernel a := ⟨hβ, hachar⟩
      rw [hkerα] at this
      simpa using this
    have hRβ : rootRankOneGroup Tag.G2 K₂ β = rootRankOneGroup Tag.G2 K₂ α := by
      rcases hβα with rfl | rfl
      · rfl
      · exact CFSG.RankThree.PartOne.KE.rootRankOneGroup_neg hα
    have hrD : r ∈ ⁅Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.G2 a},
        Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.G2 a}⁆ := by
      rw [hcomm, ← hRβ]
      exact hr
    obtain ⟨hrΓ, hrc⟩ := commutator_self_le _ hrD
    refine ⟨hrΓ, ⟨_, hxTΓ.2⟩, hxE, ?_, ?_⟩
    · intro h
      exact hx1 (congrArg Subtype.val h)
    · exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hrc _ rfl).symm)
  have hC : closure (cenGen (E.subgroupOf Γ)) = ⊤ := by
    set C := closure (cenGen (E.subgroupOf Γ)) with hCdef
    have hRle : ⨆ α : {α : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 α},
        rootRankOneGroup Tag.G2 K₂ α.1 ⊓ Γ ≤ C.map Γ.subtype := by
      refine iSup_le fun α => ?_
      intro r hr
      obtain ⟨hrΓ, hrc⟩ := hroot α.1 α.2 r hr
      exact ⟨⟨r, hrΓ⟩, subset_closure hrc, rfl⟩
    rw [eq_top_iff]
    intro γ _
    have h1 : (γ : ModGL Tag.G2 K₂) ∈ ⨆ α : {α : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 α},
        rootRankOneGroup Tag.G2 K₂ α.1 ⊓ Γ := by
      rw [hGEN]
      exact γ.2
    obtain ⟨c, hc, hcγ⟩ := hRle h1
    have : c = γ := Subtype.ext hcγ
    exact this ▸ hc
  let ψ : ModGL Tag.G2 X →* ModGL Tag.G2 K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap X K₂))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := Tag.G2) (algebraMap X K₂))
  let ε : adjointGroup Tag.G2 X ≃* Γ := Subgroup.equivMapOfInjective (adjointGroup Tag.G2 X) ψ hψ
  refine closure_cenGen_eq_top_of_map ε E₁ ?_
  have hF : ∀ y ∈ E₁.map ε.toMonoidHom, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₁p x hx, map_one]
  have hFc : Nat.card (E₁.map ε.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective ε.injective]
    exact hE₁c
  have hEc : Nat.card (E.subgroupOf Γ) = p ^ 2 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΓ).toEquiv
  obtain ⟨h, hFh⟩ := plane_conj S₀ hS₀ (E := E.subgroupOf Γ) (fun x hxT hxp => by
    have h1 : (x : ModGL Tag.G2 K₂) ∈ torusGroup Tag.G2 K₂ ⊓ Γ := hxT
    have h2 : (x : ModGL Tag.G2 K₂) ^ p = 1 := by
      have := congrArg Subtype.val hxp
      simpa using this
    exact (hEmem _).2 ⟨h1.1, h2⟩) hEc hF hFc
  rw [hFh, closure_cenGen_cj, hC, Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective]

end Consumer

end CFSG.RankThree.PartOne.SEITZ11.G2Seven
