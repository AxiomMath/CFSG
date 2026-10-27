module

public import CFSG.Quasithin.EmptyFaithful.S1422LocBasic
public import CFSG.Quasithin.EmptyFaithful.S1422LocQ8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

section Elementary

variable {G : Type*} [Group G]

theorem sq_commutes_of_relIndex_two {A B : Subgroup G} (hidx : A.relIndex B = 2)
    {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hgB : g ∈ Subgroup.normalizer (B : Set G))
    (hcA : ∀ a ∈ A, g * a = a * g) (hA2 : ∀ a ∈ A, a * a = 1) :
    ∀ b ∈ B, g * g * b = b * (g * g) := by
  intro b hb
  by_cases hbA : b ∈ A
  · calc g * g * b = g * (g * b) := by rw [mul_assoc]
      _ = g * (b * g) := by rw [hcA b hbA]
      _ = g * b * g := by rw [mul_assoc]
      _ = b * g * g := by rw [hcA b hbA]
      _ = b * (g * g) := by rw [mul_assoc]
  · have hcB : g * b * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hgB b).mp hb
    have hcA' : g * b * g⁻¹ ∉ A := fun h => hbA ((Subgroup.mem_normalizer_iff.mp hgA b).mpr h)
    have h1 : (g * b * g⁻¹) * b⁻¹ ∈ A := by
      obtain ⟨a, ha⟩ := (Subgroup.index_eq_two_iff).mp (show (A.subgroupOf B).index = 2 from hidx)
      have hb' : (⟨b, hb⟩ : B) ∉ A.subgroupOf B := fun h => hbA (Subgroup.mem_subgroupOf.mp h)
      have hc' : (⟨g * b * g⁻¹, hcB⟩ : B) ∉ A.subgroupOf B := fun h =>
        hcA' (Subgroup.mem_subgroupOf.mp h)
      have e1 : (⟨b, hb⟩ : B) * a ∈ A.subgroupOf B := ((ha ⟨b, hb⟩).resolve_right
        (fun h => hb' h.1)).1
      have e2 : (⟨g * b * g⁻¹, hcB⟩ : B) * a ∈ A.subgroupOf B := ((ha ⟨g * b * g⁻¹, hcB⟩).resolve_right
        (fun h => hc' h.1)).1
      have := (A.subgroupOf B).mul_mem e2 ((A.subgroupOf B).inv_mem e1)
      have e3 : ((⟨g * b * g⁻¹, hcB⟩ : B) * a) * ((⟨b, hb⟩ : B) * a)⁻¹ =
          ⟨(g * b * g⁻¹) * b⁻¹, B.mul_mem hcB (B.inv_mem hb)⟩ := by
        apply Subtype.ext
        simp [mul_assoc]
      rw [e3] at this
      exact Subgroup.mem_subgroupOf.mp this
    obtain ⟨a', ha'⟩ : ∃ a' : G, a' = (g * b * g⁻¹) * b⁻¹ := ⟨_, rfl⟩
    rw [← ha'] at h1
    have hga' : g * a' * g⁻¹ = a' := by
      have := hcA a' h1
      rw [this]; group
    have hc : g * b * g⁻¹ = a' * b := by rw [ha']; group
    have h2 : g * (g * b * g⁻¹) * g⁻¹ = b := by
      have e1 : g * (g * b * g⁻¹) * g⁻¹ = (g * a' * g⁻¹) * (g * b * g⁻¹) := by
        calc g * (g * b * g⁻¹) * g⁻¹ = g * (a' * b) * g⁻¹ := by rw [← hc]
          _ = (g * a' * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e1, hga', hc, ← mul_assoc, hA2 a' h1, one_mul]
    calc g * g * b = (g * (g * b * g⁻¹) * g⁻¹) * (g * g) := by group
      _ = b * (g * g) := by rw [h2]

theorem commutes_of_sq_commutes_of_odd {g s : G} (hodd : Odd (orderOf g))
    (h : g * g * s = s * (g * g)) : g * s = s * g := by
  obtain ⟨k, hk⟩ := hodd
  have hg1 : g ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
  have hg : g = (g * g) ^ (k + 1) := by
    calc g = g ^ (2 * k + 1) * g := by rw [hg1, one_mul]
      _ = g ^ (2 * k + 1 + 1) := (pow_succ g (2 * k + 1)).symm
      _ = g ^ (2 * (k + 1)) := by rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      _ = (g * g) ^ (k + 1) := by rw [pow_mul, sq]
  have hc : Commute (g * g) s := h
  rw [hg]
  exact ((hc.pow_left (k + 1)).eq)

theorem eq_of_isPGroup_of_sylow_le [Finite G] (P : Sylow 2 G) {N : Subgroup G}
    (hPN : (P : Subgroup G) ≤ N) (hN : IsPGroup 2 N) : N = P := by
  obtain ⟨Q, hNQ⟩ := hN.exists_le_sylow
  have hcard : Nat.card (Q : Subgroup G) = Nat.card (P : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hPQ : (P : Subgroup G) = Q := Subgroup.eq_of_le_of_card_ge (hPN.trans hNQ) hcard.le
  exact le_antisymm (hPQ ▸ hNQ) hPN

theorem elemAbelian_comm {E : Subgroup G} (h : IsElemAbelian 2 E) :
    ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem elemAbelian_sq {E : Subgroup G} (h : IsElemAbelian 2 E) : ∀ e ∈ E, e * e = 1 := fun e he => by
  simpa [sq] using h.2 e he

theorem isPGroup_two_of_odd_eq_one [Finite G] {N : Subgroup G}
    (h : ∀ g ∈ N, Odd (orderOf g) → g = 1) :
    IsPGroup 2 N := by
  intro x
  obtain ⟨g, hg⟩ := x
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 2 (by norm_num)
  have hdvd : 2 ^ a ∣ orderOf g := ⟨m, hord⟩
  have hs : orderOf (g ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) hdvd, hord]
    simp
  have hodd : Odd (orderOf (g ^ 2 ^ a)) := by rw [hs]; exact Nat.odd_iff.mpr (by omega)
  have h1 : g ^ 2 ^ a = 1 := h _ (N.pow_mem hg _) hodd
  exact ⟨a, Subtype.ext (by simpa using h1)⟩

theorem conjSubgroup_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) (g : G) :
    IsElemAbelian 2 (conjSubgroup E g) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨e1, he1, h1⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨e2, he2, h2⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← h1, ← h2, ← map_mul, ← map_mul, elemAbelian_comm hE _ he1 _ he2]
  · obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hE.2 e he, map_one]

theorem card_conjSubgroup (E : Subgroup G) (g : G) : Nat.card (conjSubgroup E g) = Nat.card E :=
  (Nat.card_congr (Subgroup.equivMapOfInjective E (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective).toEquiv).symm

theorem conjSubgroup_le {U E : Subgroup G} (hEU : E ≤ U) {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) : conjSubgroup E g ≤ U := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have h1 := hEU hx
  have h2 := Subgroup.mem_normalizer_iff.mp hg (g * x * g⁻¹)
  have : g * x * g⁻¹ ∈ U := h1
  have hg' : g⁻¹ ∈ Subgroup.normalizer (U : Set G) := (Subgroup.normalizer (U : Set G)).inv_mem hg
  have h3 := (Subgroup.mem_normalizer_iff.mp hg' (g * x * g⁻¹)).mp this
  simpa [mul_assoc] using h3

theorem index_le_ncard_of_normalizer_eq [Finite G] {K T U E : Subgroup G}
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) (hEU : E ≤ U)
    (hEa : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hN : ∀ g ∈ K, g ∈ Subgroup.normalizer (E : Set G) → g ∈ T)
    (hTE : T ≤ Subgroup.normalizer (E : Set G)) :
    (T.subgroupOf K).index ≤
      {E' : Subgroup G | E' ≤ U ∧ IsElemAbelian 2 E' ∧ Nat.card E' = 8}.ncard := by
  classical
  let S : Set (Subgroup G) := {E' | E' ≤ U ∧ IsElemAbelian 2 E' ∧ Nat.card E' = 8}
  have hmem : ∀ g : G, g ∈ K → conjSubgroup E g ∈ S := fun g hg =>
    ⟨conjSubgroup_le hEU (hKU hg), conjSubgroup_isElemAbelian hEa g, by
      rw [card_conjSubgroup]; exact hE8⟩
  let F : ↥K → S := fun g => ⟨conjSubgroup E (g : G)⁻¹, hmem _ (K.inv_mem g.2)⟩
  have hFeq : ∀ g g' : ↥K, F g = F g' ↔ (g : G)⁻¹ * g' ∈ T := by
    intro g g'
    constructor
    · intro h
      have h1 : conjSubgroup E (g : G)⁻¹ = conjSubgroup E (g' : G)⁻¹ := congrArg Subtype.val h
      have h2 : conjSubgroup E ((g : G)⁻¹ * g') = E := by
        have := congrArg (fun A => conjSubgroup A (g' : G)) h1
        simp only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at this
        exact this
      apply hN
      · exact K.mul_mem (K.inv_mem g.2) g'.2
      · exact conjSubgroup_eq_iff_mem_normalizer.mp h2
    · intro h
      apply Subtype.ext
      show conjSubgroup E (g : G)⁻¹ = conjSubgroup E (g' : G)⁻¹
      have hnorm : ((g : G)⁻¹ * g')⁻¹ ∈ Subgroup.normalizer (E : Set G) := hTE (T.inv_mem h)
      have e : (g' : G)⁻¹ = ((g : G)⁻¹ * g')⁻¹ * (g : G)⁻¹ := by group
      rw [e, ← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr hnorm]
  let f : ↥K ⧸ T.subgroupOf K → S := Quotient.lift F (fun g g' hgg' => by
    have : (g : G)⁻¹ * g' ∈ T := Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.leftRel_apply (s := T.subgroupOf K)).mp hgg')
    exact (hFeq g g').mpr this)
  have hf : Function.Injective f := by
    intro q q' h
    induction q using QuotientGroup.induction_on with | H g => ?_
    induction q' using QuotientGroup.induction_on with | H g' => ?_
    have h1 : F g = F g' := h
    have h2 := (hFeq g g').mp h1
    exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr h2)
  have hfin : (↑S : Set (Subgroup G)).Finite := Set.toFinite _
  calc (T.subgroupOf K).index = Nat.card (↥K ⧸ T.subgroupOf K) := rfl
    _ ≤ Nat.card S := Nat.card_le_card_of_injective f hf
    _ = S.ncard := Nat.card_coe_set_eq S

end Elementary

section U

variable {G : Type*} [Group G]

theorem q8Sq_facts {U E : Subgroup G} (hU : IsQ8Sq ↥U) (hEU : E ≤ U)
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE8 : Nat.card E = 8) :
    (∀ x ∈ U, (∀ e ∈ E, x * e = e * x) → x ∈ E) ∧ (∀ u ∈ U, ∀ e ∈ E, u * e * u⁻¹ ∈ E) := by
  obtain ⟨hcard, A, B, ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩ := hU
  let d : S143.Q8SqData ↥U := ⟨A, B, hAB, hgen, eA, eB, hcard⟩
  have hE'ab : ∀ a ∈ E.subgroupOf U, ∀ b ∈ E.subgroupOf U, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hab _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))
  have hE'8 : Nat.card (E.subgroupOf U) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEU).toEquiv]; exact hE8
  refine ⟨fun x hx hxe => ?_, fun u hu e he => ?_⟩
  · have := S1422Loc.mem_of_commutes_abelian_eight d (E.subgroupOf U) hE'ab hE'8
      (x := ⟨x, hx⟩) (fun e he => Subtype.ext (hxe _ (Subgroup.mem_subgroupOf.mp he)))
    exact Subgroup.mem_subgroupOf.mp this
  · have := S1422Loc.conj_mem_of_abelian_eight d (E.subgroupOf U) hE'ab hE'8 ⟨u, hu⟩
      (e := ⟨e, hEU he⟩) (Subgroup.mem_subgroupOf.mpr he)
    exact Subgroup.mem_subgroupOf.mp this

theorem ncard_elemAbelian_eight_le {U : Subgroup G} (hU : IsQ8Sq ↥U) :
    {E : Subgroup G | E ≤ U ∧ IsElemAbelian 2 E ∧ Nat.card E = 8}.ncard ≤ 6 := by
  obtain ⟨hcard, A, B, ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩ := hU
  let d : S143.Q8SqData ↥U := ⟨A, B, hAB, hgen, eA, eB, hcard⟩
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine (Set.ncard_le_ncard_of_injOn (fun E : Subgroup G => E.subgroupOf U) ?_ ?_
    (Set.toFinite _)).trans (S1422Loc.ncard_elemAbelianEight_le d)
  · rintro E ⟨hEU, hEa, hE8⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb
      exact Subtype.ext (elemAbelian_comm hEa _ (Subgroup.mem_subgroupOf.mp ha) _
        (Subgroup.mem_subgroupOf.mp hb))
    · intro e he
      exact Subtype.ext (elemAbelian_sq hEa _ (Subgroup.mem_subgroupOf.mp he))
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEU).toEquiv]; exact hE8
  · rintro E ⟨hEU, -⟩ E' ⟨hEU', -⟩ h
    have := (Subgroup.subgroupOf_inj).mp h
    rwa [inf_of_le_left hEU, inf_of_le_left hEU'] at this


end U

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

theorem normalizer_le_M (S : Setting1422 T M Y H) {E : Subgroup G} (hE2 : IsPGroup 2 E)
    (hE1 : E ≠ ⊥) (hYT : Y ⊔ T ≤ Subgroup.normalizer (E : Set G)) :
    Subgroup.normalizer (E : Set G) ≤ M := by
  have hloc : IsTwoLocal (Subgroup.normalizer (E : Set G)) := ⟨E, hE1, hE2, rfl⟩
  obtain ⟨K, hK, hle⟩ := exists_maxTwoLocal_ge hloc
  have hKM : K = M := S.data.unique.2 K ⟨hK, hYT.trans hle⟩
  exact hKM ▸ hle

theorem eq_one_of_odd_E (S : Setting1422 T M Y H) {U E : Subgroup G}
    (hU : IsQ8Sq ↥U) (hEU : E ≤ U) (hEa : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hYT : Y ⊔ T ≤ Subgroup.normalizer (E : Set G)) (hVE : VZ T M ≤ E)
    (hCU : ∀ x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G), Odd (orderOf x) →
      (∀ u ∈ U, x * u = u * x) → x = 1)
    {g : G} (hgMc : g ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) (hgE : g ∈ Subgroup.normalizer (E : Set G))
    (hodd : Odd (orderOf g)) : g = 1 := by
  have hEab := elemAbelian_comm hEa
  have hE2 := elemAbelian_sq hEa
  obtain ⟨hC, hN⟩ := q8Sq_facts hU hEU hEab hE8
  have hEp : IsPGroup 2 E := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [hE8]; norm_num
  have hE1 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE8
    omega
  have hgM : g ∈ M := S.normalizer_le_M hEp hE1 hYT hgE
  obtain ⟨z, hz, hz1, hz2, hZ⟩ := S.exists_z
  have hzV : z ∈ VZ T M := le_conjClosure _ _ hz
  have hzE : z ∈ E := hVE hzV
  have hgz : g * z = z * g := mem_Mc_comm hz hgMc
  have hgV : g ∈ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _ hgM
  have hV4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hzp : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime hz2 hz1
  have hzV' : Subgroup.zpowers z ≤ VZ T M := (Subgroup.zpowers_le).mpr hzV
  have hidxV : (Subgroup.zpowers z).relIndex (VZ T M) = 2 := by
    have := card_eq_card_mul_relIndex hzV'
    rw [hV4, hzp] at this
    omega
  have hcz : ∀ a ∈ Subgroup.zpowers z, g * a = a * g := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_right (show Commute g z from hgz) n).eq
  have hgzp : g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    Subgroup.centralizer_le_normalizer (Subgroup.zpowers z : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun a ha => (hcz a ha).symm)
  have hsqz : ∀ a ∈ Subgroup.zpowers z, a * a = 1 := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_add, ← two_mul, zpow_mul]
    have h2 : z ^ (2 : ℤ) = 1 := by exact_mod_cast hz2
    rw [h2, one_zpow]
  have hgV2 := sq_commutes_of_relIndex_two hidxV hgzp hgV hcz hsqz
  have hgVc : ∀ v ∈ VZ T M, g * v = v * g := fun v hv =>
    commutes_of_sq_commutes_of_odd hodd (hgV2 v hv)
  have hVE' : VZ T M ≤ E := hVE
  have hidxE : (VZ T M).relIndex E = 2 := by
    have := card_eq_card_mul_relIndex hVE'
    rw [hE8, hV4] at this
    omega
  have hgE2 := sq_commutes_of_relIndex_two hidxE hgV hgE hgVc (fun a ha => hE2 a (hVE ha))
  have hgEc : ∀ e ∈ E, g * e = e * g := fun e he =>
    commutes_of_sq_commutes_of_odd hodd (hgE2 e he)
  have hgU2 : ∀ u ∈ U, g * g * u = u * (g * g) := by
    intro u hu
    have hgu : g * u * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hgU u).mp hu
    set w : G := u⁻¹ * (g * u * g⁻¹) with hw
    have hwU : w ∈ U := U.mul_mem (U.inv_mem hu) hgu
    have hwc : ∀ e ∈ E, w * e = e * w := by
      intro e he
      have h1 : u * e * u⁻¹ ∈ E := hN u hu e he
      have h2 : g * (u * e * u⁻¹) * g⁻¹ = u * e * u⁻¹ := by
        rw [hgEc _ h1]; group
      have h3 : g * e = e * g := hgEc e he
      have h4 : (g * u * g⁻¹) * e = (u * e * u⁻¹) * (g * u * g⁻¹) := by
        calc (g * u * g⁻¹) * e = g * u * (g⁻¹ * e * g) * g⁻¹ := by group
          _ = g * u * e * g⁻¹ := by
            have : g⁻¹ * e * g = e := by
              calc g⁻¹ * e * g = g⁻¹ * (e * g) := by rw [mul_assoc]
                _ = g⁻¹ * (g * e) := by rw [h3]
                _ = e := by group
            rw [this]
          _ = (g * (u * e * u⁻¹) * g⁻¹) * (g * u * g⁻¹) := by group
          _ = (u * e * u⁻¹) * (g * u * g⁻¹) := by rw [h2]
      calc w * e = u⁻¹ * ((g * u * g⁻¹) * e) := by rw [hw, mul_assoc]
        _ = u⁻¹ * ((u * e * u⁻¹) * (g * u * g⁻¹)) := by rw [h4]
        _ = e * (u⁻¹ * (g * u * g⁻¹)) := by group
        _ = e * w := by rw [hw]
    have hwE : w ∈ E := hC w hwU hwc
    have hww : w * w = 1 := hE2 w hwE
    have hgw : g * w = w * g := hgEc w hwE
    have hguw : g * u * g⁻¹ = u * w := by rw [hw]; group
    have hgwg : g * w * g⁻¹ = w := by rw [hgw]; group
    have : g * (g * u * g⁻¹) * g⁻¹ = u := by
      rw [hguw]
      calc g * (u * w) * g⁻¹ = (g * u * g⁻¹) * (g * w * g⁻¹) := by group
        _ = (u * w) * w := by rw [hguw, hgwg]
        _ = u * (w * w) := by rw [mul_assoc]
        _ = u := by rw [hww, mul_one]
    calc g * g * u = (g * (g * u * g⁻¹) * g⁻¹) * (g * g) := by group
      _ = u * (g * g) := by rw [this]
  have hgUc : ∀ u ∈ U, g * u = u * g := fun u hu =>
    commutes_of_sq_commutes_of_odd hodd (hgU2 u hu)
  exact hCU g hgMc hodd hgUc


theorem relIndex_T_Mc_le (S : Setting1422 T M Y H) {U E : Subgroup G}
    (hU : IsQ8Sq ↥U) (hEU : E ≤ U) (hEa : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hYT : Y ⊔ T ≤ Subgroup.normalizer (E : Set G)) (hVE : VZ T M ≤ E)
    (hMcU : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Subgroup.normalizer (U : Set G))
    (hCU : ∀ x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G), Odd (orderOf x) →
      (∀ u ∈ U, x * u = u * x) → x = 1) :
    (T.subgroupOf (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))).index ≤ 6 := by
  have hTE : T ≤ Subgroup.normalizer (E : Set G) := le_sup_right.trans hYT
  have hN : ∀ g ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G),
      g ∈ Subgroup.normalizer (E : Set G) → g ∈ T := by
    set N : Subgroup G := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊓
      Subgroup.normalizer (E : Set G) with hNdef
    have hTN : T ≤ N := le_inf S.T_le_Mc hTE
    have hNp : IsPGroup 2 N := isPGroup_two_of_odd_eq_one fun g hg hodd =>
      S.eq_one_of_odd_E hU hEU hEa hE8 hYT hVE hCU hg.1 (hMcU hg.1) hg.2 hodd
    obtain ⟨P, hP⟩ := S.exists_sylow
    have hNP : N = P := eq_of_isPGroup_of_sylow_le P (hP ▸ hTN) hNp
    intro g hgMc hgE
    have hgN : g ∈ N := ⟨hgMc, hgE⟩
    rw [hNP, hP] at hgN
    exact hgN
  exact (index_le_ncard_of_normalizer_eq hMcU hEU hEa hE8 hN hTE).trans
    (ncard_elemAbelian_eight_le hU)

theorem eq_Mc_of_E (S : Setting1422 T M Y H) {U E : Subgroup G}
    (hU : IsQ8Sq ↥U) (hEU : E ≤ U) (hEa : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hYT : Y ⊔ T ≤ Subgroup.normalizer (E : Set G)) (hVE : VZ T M ≤ E)
    (hMcU : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Subgroup.normalizer (U : Set G))
    (hCU : ∀ x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G), Odd (orderOf x) →
      (∀ u ∈ U, x * u = u * x) → x = 1)
    (hidxH : (T.subgroupOf H).index = 3) :
    H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hmul := Subgroup.relIndex_mul_relIndex T H _ S.T_le_H S.H_le_centralizer
  have hle := S.relIndex_T_Mc_le hU hEU hEa hE8 hYT hVE hMcU hCU
  obtain ⟨P, hP⟩ := S.exists_sylow
  have hTK : ¬ 2 ∣ (T.subgroupOf (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))).index := by
    have h := not_dvd_index_subgroupOf_of_sylow P (hP.le.trans S.T_le_Mc)
    rwa [hP] at h
  have hodd := odd_relIndex_of_le S.T_le_H S.H_le_centralizer hTK
  have h3 : T.relIndex H = 3 := hidxH
  have hr : T.relIndex (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤ 6 := hle
  rw [← hmul, h3] at hr
  have h1 : H.relIndex (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) = 1 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  exact le_antisymm S.H_le_centralizer (Subgroup.relIndex_eq_one.mp h1)

end Setting1422

end CFSG.Quasithin
