module

public import CFSG.Timmesfeld.Exceptional.CaseIConnected

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem commute_or_conj_eq_of_collinear (hD : IsRootInvolutionSet D)
    (hsing : ∀ x ∈ D, rootSet D x = {x}) (hQ : CommLambda D) {c a p : G} (hc : c ∈ D)
    (ha : a ∈ D) (hp : p ∈ D) (hca : Commute c a) (hcaD : c * a ∈ D) (hcp : Commute c p)
    (hcpD : c * p ∈ D) : a * p * a = p ∨ a * p * a = c * p := by
  rcases commute_or_orderOf_mul_eq_four_or_odd hD ha hp with hap | h4 | ⟨hodd, -⟩
  · left
    rw [hap.eq, mul_assoc, hD.mul_self_eq_one ha, mul_one]
  · right
    have hmem := hQ c hc a ha p hp hca hcaD hcp hcpD h4
    rw [hsing c hc, Set.mem_singleton_iff] at hmem
    obtain ⟨-, -, -, hpap⟩ := sq_mem_of_orderOf_eq_four hD hp ha
      (by rw [orderOf_mul_comm_eq]; exact h4)
    rw [show a * p * a = p * (p * a) ^ 2 from hpap,
      Bridge.mul_sq_comm_of_orderOf_eq_four hD ha hp h4, hmem]
    exact hcp.eq.symm
  · left
    have hpcD : p * c ∈ D := by rw [← hcp.eq]; exact hcpD
    have h1 := eq_of_collinear_of_odd hD hc hcp.symm hpcD ha hca.symm hodd
    rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hp, mul_assoc, hD.mul_self_eq_one hp, mul_one]

theorem orderOf_sq_mul_eq_four_of_commute (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {a x α : G} (ha : a ∈ D) (hx : x ∈ D) (hα : α ∈ D)
    (hax : ¬ Commute a x) (hodd : Odd (orderOf (a * x))) (haα : Commute a α)
    (h4 : orderOf (α * x) = 4) : orderOf ((α * x) ^ 2 * a) = 4 := by
  obtain ⟨hβD, hαβ, hxβ, hxαx⟩ := sq_mem_of_orderOf_eq_four hD hα hx h4
  have hα2 := hD.mul_self_eq_one hα
  have hx2 := hD.mul_self_eq_one hx
  have ha2 := hD.mul_self_eq_one ha
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hβD ha with hβa | h4' | ⟨hoddβ, -⟩
  · exfalso
    have hα' : Commute a (x * α * x) := by
      rw [hxαx]
      exact haα.mul_right hβa.symm
    have h1 : Commute (x * a * x) α := by
      have := (Commute.conj_iff x).2 hα'
      rwa [hD.inv_eq hx, show x * (x * α * x) * x = (x * x) * α * (x * x) by group, hx2,
        one_mul, mul_one] at this
    have h2 : Commute ((a * x) ^ 2) α := by
      rw [show (a * x) ^ 2 = a * (x * a * x) by rw [pow_two]; group]
      exact haα.mul_left h1
    obtain ⟨k, hk⟩ := Bridge.mem_zpowers_sq_of_odd hodd
    have h3 : Commute (a * x) α := by rw [← hk]; exact h2.pow_left k
    have h5 : Commute x α := by
      have := haα.symm.mul_right h3.symm
      rw [← mul_assoc, ha2, one_mul] at this
      exact this.symm
    have := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one hα2 hx2).1 h5.symm)
    rw [h4] at this
    exact absurd this (by norm_num)
  · exact h4'
  · exfalso
    have hβαD : (α * x) ^ 2 * α ∈ D := by
      rw [← hαβ.eq]; exact mul_sq_mem_of_orderOf_eq_four hclass hD hα hx h4
    have hoddaβ : Odd (orderOf (a * (α * x) ^ 2)) := by rwa [orderOf_mul_comm_eq]
    have h1 := eq_of_collinear_of_odd hD hα hαβ.symm hβαD ha haα hoddaβ
    apply hax
    rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hβD]
    exact hxβ.symm

theorem orderOf_eq_three_of_plane (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ y ∈ D, rootSet D y = {y}) (hQ : CommLambda D)
    (hP1 : ExcP1 D) {c z w x a : G} (hc : c ∈ D) (hz : z ∈ D) (hw : w ∈ D) (hx : x ∈ D)
    (ha : a ∈ D) (hcz : Commute c z) (hcw : Commute c w) (hzw : Commute z w)
    (hczD : c * z ∈ D) (hcwD : c * w ∈ D) (hzwD : z * w ∈ D) (hczwD : c * z * w ∈ D)
    (hcx : ¬ Commute c x) (hoddcx : Odd (orderOf (c * x))) (hzx : orderOf (z * x) = 4)
    (hca : Commute c a) (hcaD : c * a ∈ D) (hax : ¬ Commute a x)
    (hoddax : Odd (orderOf (a * x))) : orderOf (a * x) = 3 := by
  have hc2 := hD.mul_self_eq_one hc
  have hx2 := hD.mul_self_eq_one hx
  have hcx3 : orderOf (c * x) = 3 := hP1 c hc x hx hcx hoddcx z hz hcz hczD hzx
  have h3 : ∀ p ∈ D, Commute z p → z * p ∈ D → ¬ Commute p x → Odd (orderOf (p * x)) →
      orderOf (p * x) = 3 := fun p hp hzp hzpD hpx hoddp =>
    hP1 p hp x hx hpx hoddp z hz hzp.symm (by rw [← hzp.eq]; exact hzpD) hzx
  have hnc : ∀ p ∈ D, Commute c p → c * p ∈ D → ¬ Commute p x :=
    fun p hp hcp hcpD => not_commute_of_collinear hD hc hx hcx hoddcx hp hcp hcpD
  have hline : ∀ p ∈ D, Commute c p → c * p ∈ D → Commute z p → z * p ∈ D →
      orderOf (p * x) = 4 ∨ orderOf (c * p * x) = 4 := by
    intro p hp hcp hcpD hzp hzpD
    have hcpc : Commute c (c * p) := (Commute.refl c).mul_right hcp
    have hccpD : c * (c * p) ∈ D := by rw [← mul_assoc, hc2, one_mul]; exact hp
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hp hx with h | h | ⟨hp1, hp2⟩
    · exact absurd h (hnc p hp hcp hcpD)
    · exact .inl h
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hcpD hx with h' | h' | ⟨hq1, -⟩
    · exact absurd h' (hnc _ hcpD hcpc hccpD)
    · exact .inr h'
    exact (false_of_orderOf_three_three_of_line hc2 (hD.mul_self_eq_one hp) hx2 hcp hcx3
      (h3 p hp hzp hzpD hp2 hp1) hq1).elim
  have key : ∀ α ∈ D, Commute a α → orderOf (α * x) = 4 → orderOf (a * x) = 3 := by
    intro α hα haα h4
    have hβa := orderOf_sq_mul_eq_four_of_commute hclass hD ha hx hα hax hoddax haα h4
    obtain ⟨hβD, -, hxβ, -⟩ := sq_mem_of_orderOf_eq_four hD hα hx h4
    have h4' : orderOf (x * α) = 4 := by rw [orderOf_mul_comm_eq]; exact h4
    have hxβD : x * (α * x) ^ 2 ∈ D := by
      rw [Bridge.mul_sq_comm_of_orderOf_eq_four hD hx hα h4']
      exact mul_sq_mem_of_orderOf_eq_four hclass hD hx hα h4'
    rw [orderOf_mul_comm_eq]
    exact hP1 x hx a ha (fun h => hax h.symm) (by rwa [orderOf_mul_comm_eq]) _ hβD hxβ hxβD hβa
  have hcomm_of : ∀ p : G, a * p * a = p → Commute a p := fun p hp => by
    rw [Commute, SemiconjBy]
    calc a * p = a * p * a * a := by rw [mul_assoc (a * p), hD.mul_self_eq_one ha, mul_one]
      _ = p * a := by rw [hp]
  rcases commute_or_conj_eq_of_collinear hD hsing hQ hc ha hz hca hcaD hcz hczD with haz | haz
  · exact key z hz (hcomm_of z haz) hzx
  have hconj_c : a * c * a = c := by rw [hca.symm.eq, mul_assoc, hD.mul_self_eq_one ha, mul_one]
  have hconj_mul : ∀ p q : G, a * (p * q) * a = (a * p * a) * (a * q * a) := fun p q => by
    rw [show a * p * a * (a * q * a) = a * p * (a * a) * q * a by group, hD.mul_self_eq_one ha,
      mul_one]; group
  rcases commute_or_conj_eq_of_collinear hD hsing hQ hc ha hw hca hcaD hcw hcwD with haw | haw
  ·
    rcases hline w hw hcw hcwD hzw hzwD with h | h
    · exact key w hw (hcomm_of w haw) h
    · refine key _ hcwD (hcomm_of _ ?_) h
      rw [hconj_mul, hconj_c, haw]
  ·
    have hazw : a * (z * w) * a = z * w := by
      rw [hconj_mul, haz, haw, show c * z * (c * w) = (c * c) * z * w by
        rw [mul_assoc c z, ← mul_assoc z c, ← hcz.eq]; group, hc2, one_mul]
    have hczw : Commute c (z * w) := hcz.mul_right hcw
    have hzzw : Commute z (z * w) := (Commute.refl z).mul_right hzw
    have hzzwD : z * (z * w) ∈ D := by
      rw [← mul_assoc, hD.mul_self_eq_one hz, one_mul]; exact hw
    rcases hline _ hzwD hczw (by rw [← mul_assoc]; exact hczwD) hzzw hzzwD with h | h
    · exact key _ hzwD (hcomm_of _ hazw) h
    · refine key _ (by rw [← mul_assoc]; exact hczwD) (hcomm_of _ ?_) h
      rw [hconj_mul, hconj_c, hazw]

@[expose] def ExcPlaneLine (D : Set G) : Prop :=
  ∀ c ∈ D, ∀ z ∈ D, Commute c z → c * z ∈ D →
    ∃ w ∈ D, Commute c w ∧ Commute z w ∧ c * w ∈ D ∧ z * w ∈ D ∧ c * z * w ∈ D

theorem orderOf_eq_three_of_planeLine (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ y ∈ D, rootSet D y = {y}) (hQ : CommLambda D)
    (hP1 : ExcP1 D) (hC : ExcCollConnected D) (hPL : ExcPlaneLine D) {d x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x))) :
    orderOf (d * x) = 3 := by
  by_contra h3
  let S : Set G := {a | a ∈ D ∧ ¬ Commute a x ∧ Odd (orderOf (a * x)) ∧
    ∀ y ∈ D, Commute a y → a * y ∈ D → orderOf (y * x) ≠ 4}
  have hdS : d ∈ S :=
    ⟨hd, hdx, hodd, fun y hy hdy hdyD h4 => h3 (hP1 d hd x hx hdx hodd y hy hdy hdyD h4)⟩
  have hncl : ¬ ∀ a ∈ S, ∀ c ∈ D, Commute a c → a * c ∈ D → c ∈ S := fun hcl =>
    (hC S (fun a ha => ha.1) ⟨d, hdS⟩ hcl hx).2.1 (Commute.refl x)
  simp only [not_forall] at hncl
  obtain ⟨a, ⟨ha, hax, hoddax, haS⟩, c, hc, hac, hacD, hcS⟩ := hncl
  have hcx : ¬ Commute c x := not_commute_of_collinear hD ha hx hax hoddax hc hac hacD
  have hoddcx : Odd (orderOf (c * x)) := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hc hx with h | h | ⟨h, -⟩
    · exact absurd h hcx
    · exact absurd h (haS c hc hac hacD)
    · exact h
  obtain ⟨z, hz, hcz, hczD, hzx⟩ : ∃ z ∈ D, Commute c z ∧ c * z ∈ D ∧ orderOf (z * x) = 4 := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    exact hcS ⟨hc, hcx, hoddcx, fun y hy hcy hcyD h4 => hno y hy hcy hcyD h4⟩
  have hcx3 := hP1 c hc x hx hcx hoddcx z hz hcz hczD hzx
  obtain ⟨w, hw, hcw, hzw, hcwD, hzwD, hczwD⟩ := hPL c hc z hz hcz hczD
  have hax3 := orderOf_eq_three_of_plane hclass hD hsing hQ hP1 hc hz hw hx ha hcz hcw hzw hczD
    hcwD hzwD hczwD hcx hoddcx hzx hac.symm (by rw [← hac.eq]; exact hacD) hax hoddax
  have haac : Commute a (a * c) := (Commute.refl a).mul_right hac
  have haacD : a * (a * c) ∈ D := by rw [← mul_assoc, hD.mul_self_eq_one ha, one_mul]; exact hc
  refine haS _ hacD haac haacD ?_
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hacD hx with h | h | ⟨h, -⟩
  · exact absurd h (not_commute_of_collinear hD ha hx hax hoddax hacD haac haacD)
  · exact h
  · exact (false_of_orderOf_three_three_of_line (hD.mul_self_eq_one ha) (hD.mul_self_eq_one hc)
      (hD.mul_self_eq_one hx) hac hax3 hcx3 h).elim

theorem exists_plane_of_not_normalize [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hPQ : ExcPQ D) {p q y : G} (hp : p ∈ D) (hq : q ∈ D)
    (hy : y ∈ D) (hpq : Commute p q) (hpqD : p * q ∈ D) (hpy : Commute p y)
    (hyq : y * q * y ≠ q) (hyq' : y * q * y ≠ p * q) :
    ∃ s ∈ D, Commute p s ∧ Commute q s ∧ p * s ∈ D ∧ q * s ∈ D ∧ p * q * s ∈ D := by
  have hy2 := hD.mul_self_eq_one hy
  have h4 : orderOf (q * y) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hq hy with h | h | ⟨h, -⟩
    · exact absurd (by rw [← h.eq, mul_assoc, hy2, mul_one]) hyq
    · exact h
    · exfalso
      have hqpD : q * p ∈ D := by rw [← hpq.eq]; exact hpqD
      have hodd : Odd (orderOf (y * q)) := by rwa [orderOf_mul_comm_eq]
      have h1 := eq_of_collinear_of_odd hD hp hpq.symm hqpD hy hpy.symm hodd
      exact hyq (by rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hq, mul_assoc,
        hD.mul_self_eq_one hq, mul_one])
  obtain ⟨hsD, hqs, -, hyqy⟩ := sq_mem_of_orderOf_eq_four hD hq hy h4
  have hqsD : q * (q * y) ^ 2 ∈ D := by
    rw [← hyqy]; simpa [hD.inv_eq hy] using conj_mem_of_isClass hclass y hq
  refine ⟨_, hsD, (hpq.mul_right hpy).pow_right 2, hqs, ?_, hqsD, ?_⟩
  ·
    have hqQ : q ∈ twoCore p := mem_map_pCore_centralizer hclass hD hp hq hpq.symm
      (Or.inl (by rw [← hpq.eq]; exact hpqD))
    have hsQ : (q * y) ^ 2 ∈ twoCore p := by
      have h1 := conj_mem_twoCore hpy.symm hqQ
      rw [show (q * y) ^ 2 = q * (y * q * y⁻¹) by rw [pow_two, hD.inv_eq hy]; group]
      exact (twoCore p).mul_mem hqQ h1
    by_contra hpsD
    refine hPQ p hp _ hsD (commute_of_mem_twoCore hsQ).symm ?_ hpsD hsQ
    intro hsp
    apply hyq'
    rw [show y * q * y = q * (q * y) ^ 2 from hyqy, hsp]
    exact hpq.eq.symm
  ·
    rw [mul_assoc, ← hyqy]
    have := conj_mem_of_isClass hclass y hpqD
    rwa [hD.inv_eq hy, show y * (p * q) * y = p * (y * q * y) by
      rw [← mul_assoc, ← hpy.eq]; group] at this

@[expose] def IsWeakTILine (D : Set G) (c z : G) : Prop :=
  (∀ y ∈ D, Commute c y → y * z * y = z ∨ y * z * y = c * z) ∧
    (∀ y ∈ D, Commute z y → y * c * y = c ∨ y * c * y = c * z) ∧
    (∀ y ∈ D, Commute (c * z) y → y * c * y = c ∨ y * c * y = z)

@[expose] def ExcTILinePlane (D : Set G) : Prop :=
  ∀ c ∈ D, ∀ z ∈ D, Commute c z → c * z ∈ D → IsWeakTILine D c z →
    ∃ w ∈ D, Commute c w ∧ Commute z w ∧ c * w ∈ D ∧ z * w ∈ D ∧ c * z * w ∈ D

theorem planeLine_of_tiLinePlane [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hPQ : ExcPQ D) (hTI : ExcTILinePlane D) :
    ExcPlaneLine D := by
  intro c hc z hz hcz hczD
  by_cases hW : IsWeakTILine D c z
  · exact hTI c hc z hz hcz hczD hW
  have hc2 := hD.mul_self_eq_one hc
  have hzcD : z * c ∈ D := by rw [← hcz.eq]; exact hczD
  simp only [IsWeakTILine, not_and_or, not_forall, not_or] at hW
  rcases hW with ⟨y, hy, hcy, hyz, hyz'⟩ | ⟨y, hy, hzy, hyc, hyc'⟩ | ⟨y, hy, hczy, hyc, hyc'⟩
  · exact exists_plane_of_not_normalize hclass hD hPQ hc hz hy hcz hczD hcy hyz hyz'
  · obtain ⟨s, hs, hzs, hcs, hzsD, hcsD, hzcsD⟩ := exists_plane_of_not_normalize hclass hD hPQ hz
      hc hy hcz.symm hzcD hzy hyc (by rw [← hcz.eq]; exact hyc')
    exact ⟨s, hs, hcs, hzs, hcsD, hzsD, by rw [hcz.eq]; exact hzcsD⟩
  · have hczc : Commute (c * z) c := (Commute.refl c).mul_left hcz.symm
    have hczcD : c * z * c = z := by rw [mul_assoc, ← hcz.eq, ← mul_assoc, hc2, one_mul]
    obtain ⟨s, hs, hczs, hcs, hczsD, hcsD, hczcsD⟩ := exists_plane_of_not_normalize hclass hD hPQ
      hczD hc hy hczc (by rw [hczcD]; exact hz) hczy hyc (by rw [hczcD]; exact hyc')
    rw [hczcD] at hczcsD
    have hzs : Commute z s := by
      have := hczs.mul_left hcs
      rwa [hczcD] at this
    exact ⟨s, hs, hcs, hzs, hcsD, hczcsD, hczsD⟩

end CFSG.Timmesfeld.Moufang
