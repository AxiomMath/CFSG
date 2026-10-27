module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenFourBFam
public import CFSG.LocalAnalysis.WeakClosure81.ElevenFourBAltGp
public import CFSG.CGT.PushingUpLit.Glue.BlockJ

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_or_eq_top_of_forall_isTwoPow_mem_of_one_le {A : Type} [Group A] [Finite A] {m : ℕ}
    (hm : 1 ≤ m) (φ : A ≃* alternatingGroup (Fin (2 * m + 1))) {S : Subgroup A}
    (hS : Nonempty (S ≃* alternatingGroup (Fin (2 * m)))) {D : Subgroup A}
    (hD : ∀ x ∈ S, (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ D) : D ≤ S ∨ D = ⊤ := by
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hm1 : m = 1 := by omega
    subst hm1
    have hcard : Nat.card A = 3 := by
      rw [Nat.card_congr φ.toEquiv]
      haveI : Nontrivial (Fin (2 * 1 + 1)) := Fin.nontrivial_iff_two_le.mpr (by norm_num)
      rw [nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    haveI : Fact (Nat.card A).Prime := ⟨by rw [hcard]; exact Nat.prime_three⟩
    rcases D.eq_bot_or_eq_top_of_prime_card with h | h
    · left; rw [h]; exact bot_le
    · exact Or.inr h
  · exact le_or_eq_top_of_forall_isTwoPow_mem hm2 φ hS hD

theorem le_centralizer_of_sup_pCoreOf_eq {K Q E U : Subgroup G} (hE : IsBTBlock K Q E)
    (hX : IsShortGroup ↥E) (hU2 : IsPGroup 2 U) (hUN : U ≤ Subgroup.normalizer (E : Set G))
    (hsup : E ⊓ Subgroup.centralizer (U : Set G) ⊔ pCoreOf 2 E = E) :
    E ≤ Subgroup.centralizer (U : Set G) := by
  have hW : oTwoIn E = pCoreOf 2 E := Glue.oTwoIn_eq_pCoreOf' E
  have hab : ∀ x ∈ oTwoIn E, ∀ y ∈ oTwoIn E, x * y = y * x := by
    rw [hW]; exact hE.elemAbelian.1
  have hperf : ⁅oTwoIn E, E⁆ = oTwoIn E := by
    rw [hW]; exact hE.perfect
  set D : Subgroup G := E ⊓ Subgroup.centralizer (U : Set G) with hDdef
  have hsup' : D ⊔ pCoreOf 2 E = E := by rw [hDdef]; exact hsup
  have hDN : D ≤ Subgroup.normalizer (oTwoIn E : Set G) := fun x hx =>
    CFSG.CGT.PushingUpLit.normalizer_le_normalizer_oTwoIn E (Subgroup.le_normalizer hx.1)
  have hmem : ∀ e ∈ E, ∃ d ∈ D, ∃ r ∈ oTwoIn E, d * r = e := by
    intro e he
    have he' : e ∈ (D : Set G) * (oTwoIn E : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right D (oTwoIn E) hDN, hW, hsup']
      exact he
    exact Set.mem_mul.mp he'
  have hc : ∀ i ∈ U, ∀ e ∈ E, i * e * i⁻¹ * e⁻¹ ∈ oTwoIn E := by
    intro i hi e he
    obtain ⟨d, hd, r, hr, rfl⟩ := hmem e he
    have hid : i * d = d * i := Subgroup.mem_centralizer_iff.1 hd.2 i hi
    have hir : i * r * i⁻¹ ∈ oTwoIn E := conj_mem_oTwoIn (hUN hi) hr
    have hcomm : i * r * i⁻¹ * r⁻¹ ∈ oTwoIn E := mul_mem hir (inv_mem hr)
    have hconj : i * (d * r) * i⁻¹ * (d * r)⁻¹ =
        d * (i * r * i⁻¹ * r⁻¹) * d⁻¹ := by
      calc i * (d * r) * i⁻¹ * (d * r)⁻¹
          = (i * d) * r * i⁻¹ * (d * r)⁻¹ := by group
        _ = (d * i) * r * i⁻¹ * (d * r)⁻¹ := by rw [hid]
        _ = d * (i * r * i⁻¹ * r⁻¹) * d⁻¹ := by group
    rw [hconj]
    exact conj_mem_oTwoIn (Subgroup.le_normalizer hd.1) hcomm
  have hcen : ∀ i ∈ U, ∀ w ∈ oTwoIn E, i * w * i⁻¹ = w :=
    Glue.centralizes_oTwoIn_of_commutator_le hX hab hperf hU2 hUN hc
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro i hi
  obtain ⟨d, hd, r, hr, rfl⟩ := hmem e he
  have hid : i * d = d * i := Subgroup.mem_centralizer_iff.1 hd.2 i hi
  have hri : i * r = r * i := by
    calc i * r = (i * r * i⁻¹) * i := by group
      _ = r * i := by rw [hcen i hi r hr]
  calc i * (d * r) = (i * d) * r := by group
    _ = (d * i) * r := by rw [hid]
    _ = d * (i * r) := by group
    _ = d * (r * i) := by rw [hri]
    _ = (d * r) * i := by group

theorem sup_pCoreOf_eq_or_le_of_alt {C E : Subgroup G} {U : Set G} {m : ℕ} (hm : 1 ≤ m)
    (hEalt : IsNaturalAltModule ↥E m)
    (hC : Nonempty ((((C ⊓ E).subgroupOf E).map (QuotientGroup.mk' (pCore 2 ↥E))) ≃*
      alternatingGroup (Fin (2 * m))))
    (hcent : ∀ x ∈ C ⊓ E, (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ Subgroup.centralizer U) :
    E ⊓ Subgroup.centralizer U ⊔ pCoreOf 2 E = E ∨
      E ⊓ Subgroup.centralizer U ≤ C ⊓ E ⊔ pCoreOf 2 E := by
  obtain ⟨φ, -⟩ := hEalt
  let π : ↥E →* ↥E ⧸ pCore 2 ↥E := QuotientGroup.mk' (pCore 2 ↥E)
  let S : Subgroup (↥E ⧸ pCore 2 ↥E) := ((C ⊓ E).subgroupOf E).map π
  let D' : Subgroup ↥E := (E ⊓ Subgroup.centralizer U).subgroupOf E
  have hSdef : S = ((C ⊓ E).subgroupOf E).map π := rfl
  have hD'def : D' = (E ⊓ Subgroup.centralizer U).subgroupOf E := rfl
  have h2 : ∀ x ∈ S, (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ D'.map π := by
    intro y hy hk
    have hyf : y ∈ (π.comp ((C ⊓ E).subgroupOf E).subtype).range := by
      rw [hSdef, Subgroup.mem_map] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      exact ⟨⟨z, hz⟩, hzy⟩
    obtain ⟨x, hx, hxord⟩ := exists_isTwoPow_preimage
      (π.comp ((C ⊓ E).subgroupOf E).subtype) hyf hk
    obtain ⟨j, hj⟩ := hxord
    have hord : orderOf ((x : ↥E) : G) = 2 ^ j := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hj]
    have hxC : ((x : ↥E) : G) ∈ C ⊓ E := Subgroup.mem_subgroupOf.1 x.2
    have hxcen : ((x : ↥E) : G) ∈ Subgroup.centralizer U := hcent _ hxC ⟨j, hord⟩
    have hxD : (x : ↥E) ∈ D' :=
      Subgroup.mem_subgroupOf.mpr ⟨(x : ↥E).2, hxcen⟩
    exact Subgroup.mem_map.mpr ⟨(x : ↥E), hxD, hx⟩
  have hC' : Nonempty (S ≃* alternatingGroup (Fin (2 * m))) := hC
  have hres : D'.map π ≤ S ∨ D'.map π = ⊤ :=
    le_or_eq_top_of_forall_isTwoPow_mem_of_one_le hm φ hC' h2
  have hmapD : D'.map E.subtype = E ⊓ Subgroup.centralizer U := by
    rw [hD'def]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_left
  have hmapC : ((C ⊓ E).subgroupOf E).map E.subtype = C ⊓ E :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hmapP : (pCore 2 ↥E).map E.subtype = pCoreOf 2 E := rfl
  rcases hres with h | h
  · right
    have hle : D' ≤ (C ⊓ E).subgroupOf E ⊔ pCore 2 ↥E := by
      have h1 : D' ≤ S.comap π :=
        (Subgroup.le_comap_map (f := π) D').trans (Subgroup.comap_mono h)
      rwa [hSdef, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
    have h2' : (E ⊓ Subgroup.centralizer U) ≤ C ⊓ E ⊔ pCoreOf 2 E := by
      have hmap := Subgroup.map_mono (f := E.subtype) hle
      rw [Subgroup.map_sup, hmapC, hmapP] at hmap
      rwa [hmapD] at hmap
    exact h2'
  · left
    have htop : D' ⊔ pCore 2 ↥E = ⊤ := by
      have h1 := Subgroup.comap_map_eq π D'
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have htopmap : (⊤ : Subgroup ↥E).map E.subtype = E := by
      rw [← MonoidHom.range_eq_map E.subtype, Subgroup.range_subtype]
    have h2' := congrArg (Subgroup.map E.subtype) htop
    rw [Subgroup.map_sup, hmapD, hmapP] at h2'
    rw [htopmap] at h2'
    exact h2'

theorem le_centralizer_of_alt {K Q E Y U : Subgroup G} {𝒢 : Set (Subgroup G)}
    (h : IsBHSFamily K Q 𝒢) (hK : CharTwo K) (hQ : IsSylowOf 2 Q K) (hne : cStarIn K Q ≠ K)
    (hE : E ∈ 𝒢)
    (halt : ∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥E m ∧
      Nonempty ((((cStarIn K Q ⊓ E).subgroupOf E).map (QuotientGroup.mk' (pCore 2 ↥E))) ≃*
        alternatingGroup (Fin (2 * m))))
    (hU2 : IsPGroup 2 U) (hUN : U ≤ Subgroup.normalizer (E : Set G))
    (hcent : ∀ x ∈ cStarIn K Q ⊓ E, (∃ k : ℕ, orderOf x = 2 ^ k) →
      x ∈ Subgroup.centralizer (U : Set G))
    (hYE : Y ≤ E) (hYU : Y ≤ Subgroup.centralizer (U : Set G)) (hYC : ¬ Y ≤ cStarIn K Q) :
    E ≤ Subgroup.centralizer (U : Set G) := by
  obtain ⟨m, hm, hEalt, hC⟩ := halt
  rcases sup_pCoreOf_eq_or_le_of_alt (C := cStarIn K Q) (U := (U : Set G)) hm hEalt hC hcent
    with h1 | h1
  · exact le_centralizer_of_sup_pCoreOf_eq (h.isBlock E hE) (h.inClassX hK hQ hE).1 hU2 hUN h1
  · exfalso
    have hP : pCoreOf 2 E ≤ cStarIn K Q := h.pCoreOf_le_cStarIn hQ hne hE
    refine hYC (calc Y ≤ E ⊓ Subgroup.centralizer (U : Set G) := le_inf hYE hYU
      _ ≤ cStarIn K Q ⊓ E ⊔ pCoreOf 2 E := h1
      _ ≤ cStarIn K Q := sup_le inf_le_left hP)

end CFSG.LocalAnalysis.WeakClosure81
