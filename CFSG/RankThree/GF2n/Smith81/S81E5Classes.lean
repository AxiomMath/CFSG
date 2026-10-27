module

public import CFSG.RankThree.GF2n.Smith81.S81TCond
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE7
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinCard
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCIso

public section


namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.SeitzReduction

theorem tOp_perm {K : Type} [Field K] {S T : List Rt} (hS : SOrth S) (hST : S.Perm T) :
    tOp K S = tOp K T := by
  have hpair : S.Pairwise fun β γ =>
      Commute ((1 : Module.End K (V K)) + e7Data.rootOp K β) (1 + e7Data.rootOp K γ) :=
    hS.2.1.imp_of_mem fun {β γ} hβ hγ hβγ => by
      have hc : Commute (e7Data.rootOp K β) (e7Data.rootOp K γ) :=
        rootOp_comm (hS.root hβ) (hS.root hγ) (le_of_eq (hS.2.2 β hβ γ hγ hβγ).symm)
      exact (Commute.one_left _).add_left ((Commute.one_right _).add_right hc)
  unfold tOp
  exact (hST.map _).prod_eq' (List.pairwise_map.mpr hpair)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable def tSm (S : List Rt) : e7Data_valid.minGroup K := ⟨tS K S, tS_mem S⟩

theorem tSm_cons (β : Rt) (S : List Rt) :
    (tSm (β :: S) : e7Data_valid.minGroup K) = e7Data_valid.xm K β 1 * tSm S :=
  Subtype.ext (tS_cons β S)

theorem e7Isogeny_tSm {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β) :
    e7Isogeny K (tSm S) =
      ⟨(S.map fun σ => pinnedX .E7 K σ 1).prod, list_prod_map_pinnedX_mem_adjointGroup S⟩ := by
  induction S with
  | nil =>
    apply Subtype.ext
    change ((e7Isogeny K 1 : adjointGroup .E7 K) : ModGL .E7 K) = _
    rw [map_one]
    rfl
  | cons β S ih =>
    have hβ : IsRoot .E7 β := hS β (List.mem_cons_self ..)
    have ih' := ih fun γ hγ => hS γ (List.mem_cons_of_mem _ hγ)
    apply Subtype.ext
    rw [tSm_cons, map_mul, Subgroup.coe_mul, ih',
      CFSG.StandardType.GGFinModel.ggE7_isogeny_xm_pinned K hβ 1]
    simp only [List.map_cons, List.prod_cons]

theorem sOrth_of_mem_e5Reps {S : List Rt} (hS : S ∈ e5Reps) : SOrth S :=
  (e5Reps_cond S hS).elim sOrth_of_K12 sOrth_of_K3

theorem exists_e5Reps_of_mem_innerRepsE7 {r : adjointGroup .E7 K} (hr : r ∈ innerRepsE7 K) :
    ∃ S ∈ e5Reps, ∃ F : List Rt, tOp K F = tOp K S ∧ r = e7Isogeny K (tSm F) := by
  have hroots : ∀ {S : List Rt}, S ∈ e5Reps → ∀ β ∈ S, IsRoot .E7 β := fun hS _ hβ =>
    (sOrth_of_mem_e5Reps hS).root hβ
  simp only [innerRepsE7, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have hS : S5x ∈ e5Reps := by simp [e5Reps]
    have hx : S5x = [highRoot .E7] := by
      unfold S5x
      congr 1
    refine ⟨S5x, hS, [highRoot .E7], by rw [hx], ?_⟩
    rw [e7Isogeny_tSm (by rw [← hx]; exact hroots hS)]
    apply Subtype.ext
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  · have hS : S5y ∈ e5Reps := by simp [e5Reps]
    exact ⟨S5y, hS, S5y, rfl, (e7Isogeny_tSm (hroots hS)).symm⟩
  · have hS : S5z ∈ e5Reps := by simp [e5Reps]
    exact ⟨S5z, hS, S5z, rfl, (e7Isogeny_tSm (hroots hS)).symm⟩
  · have hS : S5u ∈ e5Reps := by simp [e5Reps]
    exact ⟨S5u, hS, S5u, rfl, (e7Isogeny_tSm (hroots hS)).symm⟩
  · have hS : S5v ∈ e5Reps := by simp [e5Reps]
    have hperm : S5v.Perm oddDerivE7VFrame := by
      unfold S5v oddDerivE7VFrame
      exact List.Perm.cons _ (List.reverse_perm _).symm
    refine ⟨S5v, hS, oddDerivE7VFrame, (tOp_perm (sOrth_of_mem_e5Reps hS) hperm).symm, ?_⟩
    exact (e7Isogeny_tSm fun β hβ => hroots hS β (hperm.mem_iff.mpr hβ)).symm

end CFSG.RankThree.GF2n.Smith81.MinuscT

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.MinuscT
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.SeitzReduction

theorem e5InvolClasses_holds : E5InvolClassesStatement := by
  intro K _ _ _ _ t ht ht2 ht1
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ht
  set u' : e7Data_valid.minGroup K := ⟨u, hu⟩ with hu'
  have hinj := CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.e7Isogeny_injective K
  have hu2 : u' * u' = 1 := by
    apply Subtype.ext
    apply (vAut K).injective
    simpa using ht2
  have hu1 : u' ≠ 1 := by
    intro h
    apply ht1
    have h' : u = 1 := congrArg Subtype.val h
    simp [h']
  have hφ2 : (e7Isogeny K u') ^ 2 = 1 := by rw [pow_two, ← map_mul, hu2, map_one]
  have hφ1 : e7Isogeny K u' ≠ 1 := fun h => hu1 (hinj (h.trans (map_one _).symm))
  obtain ⟨a, ha⟩ := exists_conj_mem_innerRepsE7 hφ2 hφ1
  obtain ⟨b, rfl⟩ := e7Isogeny_surjective K a
  rw [← map_inv, ← map_mul, ← map_mul] at ha
  obtain ⟨S, hS, F, hFS, hF⟩ := exists_e5Reps_of_mem_innerRepsE7 ha
  have hb : b * u' * b⁻¹ = tSm F := hinj hF
  have hbu : (b : (Module.End K (V K))ˣ) * u * (b : (Module.End K (V K))ˣ)⁻¹ = tS K F :=
    congrArg Subtype.val hb
  refine ⟨(vAut K).toMonoidHom b, Subgroup.mem_map_of_mem _ b.2, S, hS, fun v => ?_⟩
  have hconj : (vAut K).toMonoidHom b * (vAut K).toMonoidHom u * ((vAut K).toMonoidHom b)⁻¹ =
      vAut K (tS K F) := by
    rw [← hbu]
    simp [map_mul, map_inv]
  rw [hconj, vAut_apply, tS_val, hFS]

end CFSG.RankThree.GF2n.Smith81
