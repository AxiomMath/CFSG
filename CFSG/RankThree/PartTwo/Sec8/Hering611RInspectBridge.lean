module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFBridge
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofTransport
import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section Bridge


variable {G : Type} [Group G] [Finite G]

@[expose] def HasA6Cent (K : Subgroup G) (c : G) : Prop :=
  ∃ hcN : c ∈ Subgroup.normalizer (K : Set G),
    Item426.thetaAut K hcN ^ 3 = 1 ∧ Item426.thetaAut K hcN ≠ 1 ∧
      ∃ P : Subgroup (K ⧸ aschbacherSolvableCore 3 K),
        P ∈ thetaComponentsIn (Item426.fixSub (Item426.thetaAut K hcN)) ∧
        Nonempty (P ⧸ aschbacherSolvableCore 3 P ≃* alternatingGroup (Fin 6))

variable {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G} {S K : Subgroup G}

theorem hasA6Cent_of_cfg (h45 : Sec4.Item4_5) (C : Hering611.Cfg611 G A c L E T d S K) :
    HasA6Cent K c := Hering611.exists_bridge h45 C

theorem alt47_of_cfg (h47 : Sec4.Item4_7) (C : Hering611.Cfg611 G A c L E T d S K) {x : G}
    (hxA : x ∈ A) (hout : InducesOuterTheta x K) : Alt47 K x := by
  have hst := C.standing
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := C.mem_S.1.1
  have hdA : d ∈ A := C.mem_E.2 C.d_mem.1
  have hd1 : d ≠ 1 := fun h => C.d_not_mem (h ▸ Subgroup.one_mem _)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact KFacts.not_inducesOuterTheta_one K hout
  have hKd : K ∈ thetaComponentsAt 3 d := lZeroStarAt_subset A d C.mem_K
  set M := Subgroup.centralizer ({d} : Set G) with hM
  have hM4 : SectionFourHyp M := hst.toTheoremFourHyp.sectionFourHyp
    (Sec6.centralizer_ne_top_of_ne_one hst.toTheoremFourHyp hd1)
  obtain ⟨K', hK', rfl⟩ := hKd
  set d' : M := ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hd'
  have hd'Z : d' ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hd'o : orderOf d' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hd3 hd1
  have h3 : 3 ∣ Nat.card (Subgroup.center M) := by
    rw [← hd'o, show orderOf d' = orderOf (⟨d', hd'Z⟩ : Subgroup.center M) from
      (Subgroup.orderOf_mk d' hd'Z).symm]
    exact orderOf_dvd_natCard _
  set x' : M :=
    ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm d hdA x hxA).symm⟩ with hx'
  have hx'o : orderOf x' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hx3 hx1
  have hout' : InducesOuterTheta x' K' :=
    (Item82OneProof.inducesOuterTheta_sub_iff M K' x').mpr hout
  exact Item82OneProof.alt47_map M K' x' (h47 M hM4 h3 K' hK' x' hx'o hout')

end Bridge

section Inner

theorem inner_data {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) {α : MulAut X}
    (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {g : X} (hg : MulAut.conj g = α) {P : Subgroup X}
    (hPC : P ≤ Item426.fixSub α) : g ^ 3 = 1 ∧ g ≠ 1 ∧ ∀ p ∈ P, p * g = g * p := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow, hg, hα3]
    have h2 : g ^ 3 ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun γ : MulAut X => γ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g ^ 3 = g ^ 3 * y * (g ^ 3)⁻¹ * g ^ 3 := by rw [this]
        _ = g ^ 3 * y := by group
    rwa [hZ, Subgroup.mem_bot] at h2
  · rintro rfl
    apply hα1
    rw [← hg, map_one]
  · intro p hp
    have h1 : α p = p := hPC hp
    rw [← hg, MulAut.conj_apply] at h1
    calc p * g = g * p * g⁻¹ * g := by rw [h1]
      _ = g * p := by group

end Inner

end CFSG.RankThree.PartTwo.Sec8.Hering611R
