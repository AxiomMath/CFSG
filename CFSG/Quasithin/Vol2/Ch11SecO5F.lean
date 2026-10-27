module

public import CFSG.Quasithin.Vol2.Ch11SecE43Out
public import CFSG.Quasithin.Vol2.Ch11SecO5D
public import CFSG.Quasithin.Vol2.Ch11SecO5E
public import CFSG.Quasithin.Background.DicksonPerfectPSL2

public section

namespace CFSG.Quasithin.Vol2.Ch11.O5

open CFSG.GorensteinWalter

theorem exists_eq_pgl2InnerAutPSL2 {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p) (hodd : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (β : MulAut (PSL2 F)) : ∃ g : PGL2 F, β = pgl2InnerAutPSL2 F hodd hcard g := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨γ, hγ⟩ := pGammaL2ToMulAutPSL2_surjective F (p := p) (f := 1) (by rw [hF, pow_one])
    hodd hcard β
  have hσ := SecG.O5.ringEquiv_eq_one_of_card_prime hp hF γ.right
  refine ⟨γ.left, ?_⟩
  rw [← hγ]
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right γ]
  rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr, hσ, map_one, mul_one]

theorem eq_one_of_fix {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hF : Nat.card F = p) {B : Subgroup (PSL2 F)}
    (hB : B = ⊤ ∨ Nonempty (↥B ≃* alternatingGroup (Fin 5))) {β : MulAut (PSL2 F)}
    (hβ : ∀ x ∈ B, β x = x) : β = 1 := by
  rcases hB with rfl | hB
  · ext x
    exact hβ x (Subgroup.mem_top x)
  obtain ⟨eB⟩ := hB
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [hF, pow_one]⟩
  have hcard : 3 < Nat.card F := by omega
  obtain ⟨g, rfl⟩ := exists_eq_pgl2InnerAutPSL2 hp hF hodd hcard β
  have hinj : Function.Injective
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hg : g = 1 := by
    apply eq_one_of_commute_alt5 hodd hcard
      ((B.equivMapOfInjective _ hinj).symm.trans eB)
    rintro _ ⟨x, hx, rfl⟩
    have h := toPGL_pgl2InnerAutPSL2_apply F hodd hcard g x
    rw [hβ x hx] at h
    calc g * Matrix.ProjectiveSpecialLinearGroup.toPGL x =
        g * Matrix.ProjectiveSpecialLinearGroup.toPGL x * g⁻¹ * g := by group
      _ = Matrix.ProjectiveSpecialLinearGroup.toPGL x * g := by rw [← h]
  rw [hg, map_one]

theorem perfect_cases {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p) {B : Subgroup (PSL2 F)} (hperf : ⁅B, B⁆ = B) (hne : B ≠ ⊥) :
    B = ⊤ ∨ Nonempty (↥B ≃* alternatingGroup (Fin 5)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  let φ : ZMod p ≃+* F := ZMod.ringEquivOfPrime F hp (by rwa [← Nat.card_eq_fintype_card])
  let e : PSL2 F ≃* PSL2 (ZMod p) := psl2RingEquiv φ.symm
  have hperf' : ⁅B.map e.toMonoidHom, B.map e.toMonoidHom⁆ = B.map e.toMonoidHom := by
    rw [← Subgroup.map_commutator, hperf]
  have hne' : B.map e.toMonoidHom ≠ ⊥ := fun h =>
    hne ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h)
  rcases Dickson.perfect_subgroup_psl2_prime hp2 _ hperf' hne' with h | ⟨⟨eA⟩, -⟩
  · left
    rw [← Subgroup.comap_map_eq_self_of_injective
      (show Function.Injective e.toMonoidHom from e.injective) B, h, Subgroup.comap_top]
  · exact Or.inr ⟨(B.equivMapOfInjective e.toMonoidHom e.injective).trans eA⟩

theorem eq_bot_of_isPGroup_two {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hns : ¬ Group.IsSolvable Q) {N : Subgroup Q} (hNn : N.Normal) (hN : IsPGroup 2 N) :
    N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hNn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    subst h
    have hQ : IsPGroup 2 Q := hN.of_equiv Subgroup.topEquiv
    have := hQ.isNilpotent
    exact hns inferInstance

theorem isSimpleGroup_of_cases {F : Type} [Field F] [Finite F] {p : ℕ} (h5 : 5 ≤ p)
    (hF : Nat.card F = p) {B : Subgroup (PSL2 F)}
    (hB : B = ⊤ ∨ Nonempty (↥B ≃* alternatingGroup (Fin 5))) : IsSimpleGroup B := by
  rcases hB with rfl | hB
  · have : IsSimpleGroup (PSL2 F) :=
      BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega)) (Or.inr (by omega))
    exact (Subgroup.topEquiv : (⊤ : Subgroup (PSL2 F)) ≃* PSL2 F).isSimpleGroup
  · obtain ⟨eB⟩ := hB
    exact eB.isSimpleGroup

end CFSG.Quasithin.Vol2.Ch11.O5

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.GorensteinWalter Ch11.O5

theorem l2pSignalizerFact_holds : L2pSignalizerFact := by
  intro G _ _ K L₁ R p n hp h11 hn hK hL₁K hperf ⟨F₂, _, _, hF₂, ⟨eL⟩⟩ _ hRK hRL hRL₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hK
  have hFp : Nat.card F = p := by simpa using hF
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* PSL2 F :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  let π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' _
  let ψ : ↥L₁ →* PSL2 F := e.toMonoidHom.comp (π.comp (Subgroup.inclusion hL₁K))
  have hψ : ∀ l : ↥L₁, ψ l = e (QuotientGroup.mk ⟨l, hL₁K l.2⟩) := fun _ => rfl
  have hL₁p : Group.IsPerfect L₁ := Subgroup.isPerfect_iff.mpr hperf
  have hSL : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F₂) :=
    ⟨⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, 1, fun h => by
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F₂ =>
        (A : Matrix (Fin 2) (Fin 2) F₂) 0 1) h
      simp at this⟩⟩
  have : Nontrivial (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) := eL.toEquiv.nontrivial
  have : Nontrivial ↥L₁ := (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L₁)).nontrivial
  have hBperf : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    have : Group.IsPerfect ψ.range := Group.IsPerfect.ofSurjective ψ.rangeRestrict_surjective
    exact Subgroup.isPerfect_iff.mp this
  have hBne : ψ.range ≠ ⊥ := by
    intro h
    have h2 : IsPGroup 2 ↥L₁ := by
      intro l
      have hl : ψ l = 1 := by
        have : ψ l ∈ ψ.range := ⟨l, rfl⟩
        rwa [h, Subgroup.mem_bot] at this
      rw [hψ, map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff] at hl
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, hl⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg (fun x : CFSG.pCore 2 ↥K => ((x : ↥K) : G)) hk
      simpa using this
    have := h2.isNilpotent
    exact Group.IsPerfect.not_isNilpotent (↥L₁) inferInstance
  have hB := perfect_cases hp (by omega) hFp hBperf hBne
  have hBs : IsSimpleGroup ψ.range := isSimpleGroup_of_cases (by omega) hFp hB
  have hBns : ¬ Group.IsSolvable ψ.range := by
    have : Group.IsPerfect ψ.range := Subgroup.isPerfect_iff.mpr hBperf
    have : Nontrivial ψ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hBne
    exact Group.IsPerfect.not_isSolvable _
  have hO : ∀ x ∈ pCoreOf 2 L₁, x ∈ pCoreOf 2 K := by
    intro x hx
    have hxL : x ∈ L₁ := Subgroup.map_subtype_le _ hx
    have hxO : (⟨x, hxL⟩ : ↥L₁) ∈ CFSG.pCore 2 ↥L₁ := by
      rw [← SecD.pCoreOf_subgroupOf]
      exact hx
    have hN := eq_bot_of_isPGroup_two hBns
      (Subgroup.Normal.map CFSG.pCore_normal ψ.rangeRestrict ψ.rangeRestrict_surjective)
      (CFSG.pCore_isPGroup.map ψ.rangeRestrict)
    have h1 : ψ.rangeRestrict ⟨x, hxL⟩ = 1 := by
      have : ψ.rangeRestrict ⟨x, hxL⟩ ∈ (CFSG.pCore 2 ↥L₁).map ψ.rangeRestrict :=
        ⟨_, hxO, rfl⟩
      rwa [hN, Subgroup.mem_bot] at this
    have h2 : ψ ⟨x, hxL⟩ = 1 := congrArg Subtype.val h1
    rw [hψ, map_eq_one_iff _ e.injective] at h2
    exact (SecE.mk_eq_one_iff K ⟨x, hL₁K hxL⟩).mp h2
  have hR : ∀ (r : G) (hr : r ∈ R), SecE.normAut K ⟨r, hRK hr⟩ = 1 := by
    intro r hr
    set β := SecE.normAut K ⟨r, hRK hr⟩
    have hfix : ∀ l : ↥L₁, β (QuotientGroup.mk ⟨l, hL₁K l.2⟩) = QuotientGroup.mk ⟨l, hL₁K l.2⟩ := by
      intro l
      rw [SecE.normAut_mk, QuotientGroup.eq, ← SecD.pCoreOf_subgroupOf, Subgroup.mem_subgroupOf]
      have hc : r * (l : G) * r⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 K :=
        hO _ (hRL₁ (Subgroup.commutator_mem_commutator hr l.2))
      have hn := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (K.inv_mem (hL₁K l.2))) _).mp
        ((pCoreOf 2 K).inv_mem hc)
      have e1 : (l : G)⁻¹ * (r * (l : G) * r⁻¹ * (l : G)⁻¹)⁻¹ * (l : G)⁻¹⁻¹ =
          (r * (l : G) * r⁻¹)⁻¹ * l := by group
      rw [e1] at hn
      simpa using hn
    have hβ' : MulAut.congr e β = 1 := by
      refine eq_one_of_fix hp (by omega) hFp hB ?_
      rintro _ ⟨l, rfl⟩
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hψ,
        MulEquiv.symm_apply_apply, hfix]
    apply (MulAut.congr e).injective
    rw [hβ', map_one]
  rw [Subgroup.commutator_le]
  intro r hr k hk
  rw [commutatorElement_def]
  exact (SecE.normAut_eq_one_iff K ⟨r, hRK hr⟩).mp (hR r hr) k hk

end CFSG.Quasithin.Vol2.Ch11.SecD
