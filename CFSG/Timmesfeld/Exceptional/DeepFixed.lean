module

public import CFSG.Timmesfeld.Exceptional.DeepMain

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang CFSG.Certificates

variable {G : Type*} [Group G] {D : Set G}

theorem false_of_commute_offLines (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x}) (hQ : CommLambda D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D) (hP1 : ExcP1 D)
    (hW1 : ∀ c ∈ D, ∀ p ∈ D, p ∉ nbhd D c 3 → ¬ ThreeNear D c p) {c p : G} (hc : c ∈ D)
    (hp : p ∈ D) (hp4 : p ∈ nbhd D c 4) (hp3 : p ∉ nbhd D c 3) {x : Fin 2 → G}
    (hx : ∀ i, x i ∈ collinearSet D p) (hx3 : ∀ i, x i ∈ nbhd D c 3) (h10 : x 1 ≠ x 0)
    (h10' : x 1 ≠ p * x 0) {q : G} (hq : q ∈ offLines D p x) (hzq : Commute (zEl p c x) q) :
    False := by
  have hcfg := lineConfig_of_two_near hclass hD hNL hNP hPl hP1 hc hp hp4 hp3 hx hx3 h10 h10'
  obtain ⟨⟨hqD, hpq, hpqD⟩, hqx⟩ := hq
  have hq2 : q ∉ nbhd D c 2 := fun h => hp3 (mem_nbhd_succ_of_commute hp h hpq)
  obtain ⟨-, hodd⟩ := (not_mem_nbhd_two_iff hD hNL hc hqD).1 hq2
  have hW1' : ∀ i, ¬ ThreeNear D (zPt p c x i) (yPt p c x (farZ i)) := fun i =>
    hW1 _ (zPt_mem hclass hp i) _ (yPt_mem hD hp hx (farZ i)).1
      (zPt_facts hclass hD hNL hNP hP1 hcfg hp hx i).2.2.2
  obtain ⟨hY, hW, hZ⟩ := deep_relations hclass hD hsing hQ hNL hNP hPl hP1 hcfg hp hx
    ⟨hqD, hpq, hpqD⟩ hqx hW1'
  exact hD.ne_one hqD (eq_one_of_relations hcfg hzq (hD.mul_self_eq_one hqD) hpq hY hW hZ hodd)

end CFSG.Timmesfeld.Moufang.Deep
