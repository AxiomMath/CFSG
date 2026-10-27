module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveLieGen
public import CFSG.Quasithin.H13.NQCatBND4
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm

public section

namespace CFSG.Quasithin.H13.FiveNorm.LieD4

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.QuasithinUnique

variable {K : Type} [Field K]

theorem powOver_twistedGroup
    [Finite K] [CharP K 2]
    {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (hK4 : ∃ s : Finset K, s.card = 4)
    (hF4 : ∃ s : Finset (fixedField σ), s.card = 4) :
    PowOver (twistedGroup σ) (CFSG.LieType.Steinberg.posUnipotent (twistedDatum σ))
      (Nat.card K - 1) := by
  intro H hUH hH x hx
  have hB := NQCat.BN.le_borel_of_isSolvable (twistedDatum_isCTGroupDatum σ hσ)
    (twistedDatum_steinbergExtras σ hσ) (NQCat.BN.rankOne_not_solvable_d4 hσ hK4 hF4) hUH hH hx
  have htB := borel_twisted_le σ hB
  rw [mem_comap] at htB
  have hnB := NQCat.BN.borel_adjDatum_le d4 htB
  have htU : ((x ^ (Nat.card K - 1) : twistedGroup σ) : adjointGroup d4 K) ∈
      (nativeData d4 K).U := by
    rw [Subgroup.coe_pow]
    exact pow_mem_of_mem_sup RootGroupData.H_le_normalizer_U
      (fun t ht => (nativeRootSubgroups d4 K).pow_card_sub_one_eq_one ht) hnB
  have h62 := iSup_rootGroup_inf_twistFixed_le σ (f := htHom)
    (fun v => by rw [htHom_apply, htHom_apply, ht_rho])
    (Ψ := {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧ 0 < ht γ}) (fun α hα => hα)
    (fun α hα β hβ hr => ⟨hr, by rw [ht_add]; linarith [hα.2, hβ.2]⟩)
    (fun α hα => ⟨isRoot_rho hα.1, by rw [ht_rho]; exact hα.2⟩)
    (mem_inf.2 ⟨nativeU_le htU, twistedGroup_le_twistFixed σ (x ^ (Nat.card K - 1)).2⟩)
  rw [NQCat.BN.posUnipotent_twisted_eq, mem_subgroupOf]
  refine (iSup₂_le fun β hβ => ?_ : ⨆ β ∈ proj '' {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧
    0 < ht γ}, twistedRootSubgroupD4 σ β ≤ _) h62
  obtain ⟨α, hα, rfl⟩ := hβ
  exact le_iSup₂_of_le (f := fun (β : Fin (Tag.rank .G2) → ℤ)
    (_ : β ∈ {β : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 β ∧ 0 < ht β}) =>
      twistedRootSubgroupD4 σ β) (proj α) ⟨isRoot_proj hα.1, by rw [ht_proj]; exact hα.2⟩
    le_rfl

theorem fiveRigid_quot_of_is3D4
    {X : Type} [Group X]
    (hX : CFSG.Quasithin.Is3D4 2 2 X) : FiveRigid (X ⧸ Subgroup.center X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, _, _, hK, σ, hσc, ⟨e⟩⟩ := hX
  have hK3 : Nat.card K = (2 ^ 2) ^ 3 := hK
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := 2 * 3) (by omega) (by rw [hK3, ← pow_mul])
  have hq : 2 ≤ 2 ^ 2 := by norm_num
  have hσ := sigma_three_of_card hK3 hσc
  have hK4 : ∃ s : Finset K, s.card = 4 :=
    Vol2Native.A312L.exists_finset_card_four (hK3 ▸ four_le_pow_three hq)
  have hFcard : Nat.card (fixedField σ) = 2 ^ 2 := by
    have h1 := card_orbitField_D4_orientation (K := K) Nat.prime_two (f := 2) (by omega) hK3
      (r := 1) (Or.inl rfl) (σ := σ) (fun c => by rw [pow_one]; exact hσc c) ⟨1, by decide⟩
    have h2 : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
    rw [h2, pow_one] at h1
    have e2 : orbitField TwistTag.D4 K σ ⟨1, by decide⟩ = fixedField σ := by
      ext c
      rw [mem_orbitField, h2, pow_one, RingHom.mem_eqLocusField, RingHom.id_apply]
    rw [← e2]
    exact h1
  have hF4 : ∃ s : Finset (fixedField σ), s.card = 4 :=
    NQCat.exists_finset_card_four_of_card le_rfl hFcard
  set e₁ := twistedGroupEquivDerived σ hq hK3 hσc
  set π : twistedGroup σ →* DerivedCentralQuotient (twistedFixedGroup .D4 K σ) :=
    (QuotientGroup.mk' _).comp e₁.toMonoidHom with hπ
  have hπs : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp e₁.surjective
  have hker : π.ker ≤ center (twistedGroup σ) := by
    intro x hx
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    rw [mem_center_iff]
    intro y
    apply e₁.injective
    rw [map_mul, map_mul]
    exact mem_center_iff.mp hx (e₁ y)
  have hpow := (powOver_twistedGroup hσ hK4 hF4).map_of_ker_le_center π hπs hker
  obtain ⟨Q, hQ⟩ := NQCat.BN.exists_sylow_posUnipotent_d4 hσ hK4 hF4
  have hU₀ := NQCat.BN.isSylowTwoOf_map π hπs (hQ ▸ isSylowTwoOf_top_of_sylow Q)
  have hbij : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  let σ' : K ≃+* K := RingEquiv.ofBijective σ hbij
  have hσ' : ∀ c, σ' c = c ^ (2 ^ 2) := hσc
  obtain ⟨-, -, ⟨Θ, -, -, hkerΘ, -⟩, -, hcardAut, -, hZC, ⟨iso⟩⟩ :=
    even_triality_exact_automorphism_normal_form (f := 2) (by norm_num) K hK3 σ' hσ'
  have hinn : FiveInner (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) := by
    refine fiveInner_of_hom Θ (fun α hα => ?_)
      (eq_one_of_pow_five_eq_one (by rw [hcardAut]; norm_num))
    have hmem : α ∈ Θ.ker := hα
    rw [hkerΘ] at hmem
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, hx.symm⟩
  have hno : NoFiveOver (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) :=
    noFiveOver_of_powOver (isSylowTwoOf_map_mulEquiv iso hU₀) (by rw [hK3]; norm_num)
      (hpow.map_equiv iso)
  have hP : FiveRigid (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) := ⟨hZC, hinn, hno⟩
  obtain ⟨-, ⟨e'⟩⟩ := nonempty_quotCenter_equiv (e.trans iso) hP.1
  exact fiveRigid_of_mulEquiv e'.symm hP

end CFSG.Quasithin.H13.FiveNorm.LieD4
