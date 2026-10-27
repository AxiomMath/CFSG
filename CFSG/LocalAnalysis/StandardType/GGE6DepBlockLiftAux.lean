module

public import CFSG.LocalAnalysis.StandardType.GGE6KGLayerDefs
import CFSG.Assembly.Subnormal
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem commutator_le_self {H : Type*} [Group H] (P : Subgroup H) : ⁅P, P⁆ ≤ P := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)

private theorem subnormal_subgroupOf_of_le {G : Type*} [Group G] {B L K : Subgroup G}
    (hLK : L ≤ K) (h : (B.subgroupOf K).IsSubnormal) : (B.subgroupOf L).IsSubnormal := by
  have h' : ((B.subgroupOf K).subgroupOf (L.subgroupOf K)).IsSubnormal := h.subgroupOf
  let e : L.subgroupOf K ≃* L := Subgroup.subgroupOfEquivOfLe hLK
  have h'' := h'.comap e.symm.toMonoidHom
  convert h'' using 1
  ext z
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  rfl

theorem exists_largest_perfect_subgroup {H : Type*} [Group H] (X : Subgroup H) :
    ∃ E : Subgroup H, E ≤ X ∧ ⁅E, E⁆ = E ∧
      ∀ P : Subgroup H, P ≤ X → ⁅P, P⁆ = P → P ≤ E := by
  refine ⟨sSup {P : Subgroup H | P ≤ X ∧ ⁅P, P⁆ = P}, ?_, ?_, ?_⟩
  · exact sSup_le fun P hP => hP.1
  · refine le_antisymm ?_ (sSup_le fun M hM => ?_)
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact (sSup {P : Subgroup H | P ≤ X ∧ ⁅P, P⁆ = P}).mul_mem
        ((sSup {P : Subgroup H | P ≤ X ∧ ⁅P, P⁆ = P}).mul_mem
          ((sSup {P : Subgroup H | P ≤ X ∧ ⁅P, P⁆ = P}).mul_mem ha hb)
          ((sSup {P : Subgroup H | P ≤ X ∧ ⁅P, P⁆ = P}).inv_mem ha))
        ((sSup {P : Subgroup H | P ≤ X ∧ ⁅P, P⁆ = P}).inv_mem hb)
    · calc M = ⁅M, M⁆ := hM.2.symm
        _ ≤ ⁅sSup {P : Subgroup H | P ≤ X ∧ ⁅P, P⁆ = P},
              sSup {P : Subgroup H | P ≤ X ∧ ⁅P, P⁆ = P}⁆ :=
            Subgroup.commutator_mono (le_sSup hM) (le_sSup hM)
  · intro P hPX hP
    exact le_sSup ⟨hPX, hP⟩

theorem map_eq_of_largest_perfect {L' R : Type*} [Group L'] [Finite L'] [Group R]
    (ψ : L' →* R) (hψ : Function.Surjective ψ) {ER : Subgroup R} (hER : ⁅ER, ER⁆ = ER)
    {E : Subgroup L'} (hle : E ≤ ER.comap ψ)
    (hmax : ∀ P : Subgroup L', P ≤ ER.comap ψ → ⁅P, P⁆ = P → P ≤ E) : E.map ψ = ER := by
  classical
  set S : Set (Subgroup L') := {P : Subgroup L' | P ≤ ER.comap ψ ∧ P.map ψ = ER}
  have hnonempty : ER.comap ψ ∈ S :=
    ⟨le_rfl, Subgroup.map_comap_eq_self_of_surjective hψ ER⟩
  have hex : ∃ n, ∃ P : Subgroup L', P ∈ S ∧ Nat.card P = n :=
    ⟨_, ER.comap ψ, hnonempty, rfl⟩
  obtain ⟨P, hPS, hPcard⟩ := Nat.find_spec hex
  have hmin : ∀ P' : Subgroup L', P' ∈ S → P' ≤ P → P' = P := by
    intro P' hP'S hle'
    have hcard : Nat.card P ≤ Nat.card P' := by
      rw [hPcard]
      exact Nat.find_min' hex ⟨P', hP'S, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hle' hcard
  have hcommS : ⁅P, P⁆ ∈ S := by
    refine ⟨(commutator_le_self P).trans hPS.1, ?_⟩
    simpa [Subgroup.map_commutator, hPS.2] using hER
  have hPperf : ⁅P, P⁆ = P := hmin ⁅P, P⁆ hcommS (commutator_le_self P)
  have hPE : P ≤ E := hmax P hPS.1 hPperf
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    exact hle
  · calc ER = P.map ψ := hPS.2.symm
      _ ≤ E.map ψ := Subgroup.map_mono hPE

theorem isQuasisimple_of_map_eq {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R)
    (hker : ψ.ker ≤ Subgroup.center L') {E : Subgroup L'} {ER : Subgroup R}
    (hperf : ⁅E, E⁆ = E) (hmap : E.map ψ = ER) (hER : CFSG.IsQuasisimple ↥ER) :
    CFSG.Assembly.IsQuasisimple ↥E := by
  rw [← hmap] at hER
  have hperf' : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hperf
  have hf : Function.Surjective (ψ.subgroupMap E) := ψ.subgroupMap_surjective E
  have hker' : (ψ.subgroupMap E).ker ≤ Subgroup.center ↥E := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : ψ (x : L') = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxc : (x : L') ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr hx1)
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxc (y : L'))
  have hqE : CFSG.IsQuasisimple ↥E :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperf' (ψ.subgroupMap E) hf hker').mpr hER
  exact ⟨hqE.1.commutator_eq_top, hqE.2.1⟩

theorem eq_of_isComponentOf_of_le {H : Type*} [Group H] [Finite H] {C E J : Subgroup H}
    (hEC : E ≤ C) (hE : CFSG.Assembly.IsQuasisimple ↥E) (hJ : CFSG.Assembly.IsComponentOf J C)
    (hJE : J ≤ E) : J = E := by
  obtain ⟨hJC, hJsub, hJq⟩ := hJ
  have hJsubK : (J.subgroupOf C).IsSubnormal := hJsub.subgroupOf
  have hKsub : (J.subgroupOf E).IsSubnormal := subnormal_subgroupOf_of_le hEC hJsubK
  have hKsub' : CFSG.Open.IsSubnormal (J.subgroupOf E) ⊤ :=
    CFSG.Assembly.isSubnormal_iff_open.mp (CFSG.Assembly.IsSubnormal.of_mathlib hKsub)
  have hperfJ : Group.IsPerfect ↥J := ⟨hJq.1⟩
  have hKperf : Group.IsPerfect (J.subgroupOf E) := by
    letI : Group.IsPerfect ↥J := hperfJ
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hJE).symm.toMonoidHom) (MulEquiv.surjective _)
  haveI : Group.IsPerfect (J.subgroupOf E) := hKperf
  rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top
    hE (J.subgroupOf E) hKsub' with hKbot | hKtop
  · exfalso
    have hJbot : J = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro j hj
      have hmem : (⟨j, hJE hj⟩ : ↥E) ∈ J.subgroupOf E := Subgroup.mem_subgroupOf.mpr hj
      rw [hKbot] at hmem
      exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem)
    haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJq.2
    exact not_subsingleton (↥J ⧸ Subgroup.center ↥J) (by rw [hJbot]; infer_instance)
  · refine le_antisymm hJE ?_
    intro e he
    have hmem : (⟨e, he⟩ : ↥E) ∈ J.subgroupOf E := by
      rw [hKtop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem

end CFSG.StandardType

end
