module

public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.Quasithin.SzN17

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement IsMulCommutative

theorem map_mem_cComp_of_ne_bot {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q] (f : G →* Q)
    {X Y : Subgroup G} (hY : Y ∈ cComp X) (hne : Y.map f ≠ ⊥) : Y.map f ∈ cComp (X.map f) := by
  have hYX : Y ≤ X := le_of_mem_cComp hY
  refine ⟨hne, ?_, A3.subnormal_map f (subnormal_of_mem_cComp hY), ?_⟩
  · rw [← Subgroup.map_commutator, perfect_of_mem_cComp hY]
  · intro K' hK'lt hK'ne hK'perf hK'sub
    have hCsub : IsSubnormal (K'.comap f ⊓ X) X :=
      A3.subnormal_inf_right (A3.subnormal_comap f hK'sub) (Subgroup.le_comap_map f X)
    set C : Subgroup G := K'.comap f ⊓ X with hC
    have hZsub : IsSubnormal (Y ⊓ C) X :=
      A3.subnormal_trans (A3.subnormal_inf_right (subnormal_of_mem_cComp hY) (inf_le_right : C ≤ X))
        hCsub
    have hmapZ : (Y ⊓ C).map f = K' := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact hy.2.1
      · intro k hk
        obtain ⟨y, hy, rfl⟩ := hK'lt.le hk
        exact ⟨y, ⟨hy, hk, hYX hy⟩, rfl⟩
    have hZ0sub : IsSubnormal (perfectCore (Y ⊓ C)) X := A3.subnormal_perfectCore hZsub
    have hmapcore : (perfectCore (Y ⊓ C)).map f = K' := by
      rw [map_perfectCore, hmapZ, perfectCore_eq_self_of_perfect hK'perf]
    have hcore_ne : perfectCore (Y ⊓ C) ≠ ⊥ := by
      intro h
      apply hK'ne
      rw [← hmapcore, h, Subgroup.map_bot]
    have hcore_le : perfectCore (Y ⊓ C) ≤ Y := (perfectCore_le _).trans inf_le_left
    by_cases hcoreY : perfectCore (Y ⊓ C) = Y
    · rw [hcoreY] at hmapcore
      exact hK'lt.ne hmapcore.symm
    · exact not_subnormal_of_mem_cComp hY (lt_of_le_of_ne hcore_le hcoreY) hcore_ne
        (perfectCore_perfect _) hZ0sub

theorem autOn_mem_cComp {G : Type} [Group G] [Finite G] {U J L : Subgroup G}
    (hJU : J ≤ Subgroup.normalizer (U : Set G)) (hL : L ∈ cComp J) (hne : autOn L U ≠ ⊥) :
    autOn L U ∈ cComp (autOn J U) := by
  have h1 := A312.mem_cComp_subgroupOf hJU hL
  unfold autOn at hne ⊢
  exact map_mem_cComp_of_ne_bot (conjAct U) h1 hne


section B53

variable {G : Type} [Group G] [Finite G] {W I : Subgroup G} [IsMulCommutative ↥W]

theorem b53Hyp_of_normal (hIW : I ≤ Subgroup.normalizer (W : Set G)) (hS : SQTKGroup ↥I)
    (hO2 : pCoreOf 2 (autOn I W) = ⊥) {Js : Subgroup (MulAut ↥W)} (hJX : Js ≤ autOn I W)
    (hJn : (Js.subgroupOf (autOn I W)).Normal) (hffJ : Js = ffJ Js) : B53Hyp Js := by
  set X := autOn I W with hX
  have hQ : pCoreOf 2 Js = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 Js X hJX hJn
    rw [hO2] at this
    exact le_bot_iff.1 this
  set ρ := InternalSec.autOnHom hIW with hρ
  set H : Subgroup ↥I := (Js.subgroupOf X).comap ρ with hH
  let f : ↥H →* ↥Js :=
    { toFun := fun h => ⟨((ρ (h : ↥I) : ↥X) : MulAut ↥W), h.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    rintro ⟨j, hj⟩
    obtain ⟨y, hy⟩ := InternalSec.autOnHom_surjective hIW ⟨j, hJX hj⟩
    refine ⟨⟨y, ?_⟩, ?_⟩
    · show ρ y ∈ Js.subgroupOf X
      rw [Subgroup.mem_subgroupOf, hy]
      exact hj
    · apply Subtype.ext
      show ((ρ y : ↥X) : MulAut ↥W) = j
      rw [hy]
  refine ⟨hQ, hffJ, ↥H, inferInstance, inferInstance, f.ker, inferInstance,
    InternalSec.sqtkGroup_subgroup hS H, ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm⟩⟩

theorem autOn_thompsonJ_le_ffJ_self (hWe : IsElemAbelian 2 W) (hWI : W ≤ I)
    (hIN : I ≤ Subgroup.normalizer (W : Set G)) :
    autOn (thompsonJ I) W ≤ ffJ (autOn (thompsonJ I) W) := by
  set J : Subgroup G := thompsonJ I with hJ
  have hAJ : ∀ A : Subgroup G, IsMaxElemAbelian I A → autOn A W ≤ ffJ (autOn J W) := by
    intro A hA
    by_cases hAC : A ≤ Subgroup.centralizer (W : Set G)
    · have h0 : autOn A W = ⊥ := autI_eq_bot_of_le_centralizer hWe hAC
      rw [h0]
      exact bot_le
    · have hoff : IsFFOffender I W A := ⟨hA, hAC⟩
      have hoffI := offenderImages_isFFStarOffender hWe hWI hIN ⟨A, hoff, rfl⟩
      have hAJle : autOn A W ≤ autOn J W :=
        InternalSec.autOn_le_autOn_of_le (le_iSup₂_of_le A hA le_rfl)
      exact B6.le_ffJ ⟨hAJle, hoffI.2.1, hoffI.2.2.1, hoffI.2.2.2⟩
  set D : Subgroup G := ((ffJ (autOn J W)).comap (conjAct W)).map
    (Subgroup.normalizer (W : Set G)).subtype with hD
  have hJD : J ≤ D := by
    refine iSup₂_le fun A hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (W : Set G) := hIN (hA.1 ha)
    exact ⟨⟨a, haN⟩, hAJ A hA (Setup.mem_autOn_iff.2 ⟨⟨a, haN⟩, ha, rfl⟩), rfl⟩
  intro φ hφ
  obtain ⟨⟨g, hgN⟩, hgJ, rfl⟩ := Setup.mem_autOn_iff.1 hφ
  obtain ⟨n, hn, hng⟩ := hJD hgJ
  have hnn : n = ⟨g, hgN⟩ := Subtype.ext hng
  rw [hnn] at hn
  exact hn

end B53

section Theta

variable {G : Type} [Group G]

theorem autOn_closure_orderThree {W Yp S : Subgroup G}
    (hY : Yp = Subgroup.closure {x | x ∈ S ∧ orderOf x = 3})
    (hYN : Yp ≤ Subgroup.normalizer (W : Set G)) :
    autOn Yp W = Subgroup.closure {y | y ∈ autOn Yp W ∧ orderOf y = 3} := by
  refine le_antisymm (fun y hy => ?_) ((Subgroup.closure_le _).2 fun y hy => hy.1)
  obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hy
  have key : ∀ (x : G) (hx : x ∈ Subgroup.closure {x | x ∈ S ∧ orderOf x = 3}),
      conjAct W ⟨x, hYN (hY ▸ hx)⟩ ∈
        Subgroup.closure {y | y ∈ autOn Yp W ∧ orderOf y = 3} := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hxS =>
      by_cases h1 : conjAct W ⟨x, hYN (hY ▸ Subgroup.subset_closure hxS)⟩ = 1
      · rw [h1]; exact one_mem _
      · have hxYp : x ∈ Yp := hY ▸ Subgroup.subset_closure hxS
        have hdvd : orderOf (conjAct W ⟨x, hYN (hY ▸ Subgroup.subset_closure hxS)⟩) ∣ 3 := by
          have := orderOf_map_dvd (conjAct W) (⟨x, hYN (hY ▸ Subgroup.subset_closure hxS)⟩ :
            ↥(Subgroup.normalizer (W : Set G)))
          rwa [Subgroup.orderOf_mk, hxS.2] at this
        have h3 : orderOf (conjAct W ⟨x, hYN (hY ▸ Subgroup.subset_closure hxS)⟩) = 3 := by
          rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.1 h) h1
          · exact h
        exact Subgroup.subset_closure ⟨Setup.mem_autOn_iff.2 ⟨_, hxYp, rfl⟩, h3⟩
    | one =>
      have : (⟨1, hYN (hY ▸ one_mem _)⟩ : ↥(Subgroup.normalizer (W : Set G))) = 1 := rfl
      rw [this, map_one]
      exact one_mem _
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, hYN (hY ▸ mul_mem hx hy)⟩ : ↥(Subgroup.normalizer (W : Set G))) =
          ⟨x, hYN (hY ▸ hx)⟩ * ⟨y, hYN (hY ▸ hy)⟩ := rfl
      rw [this, map_mul]
      exact mul_mem ihx ihy
    | inv x hx ih =>
      have : (⟨x⁻¹, hYN (hY ▸ inv_mem hx)⟩ : ↥(Subgroup.normalizer (W : Set G))) =
          (⟨x, hYN (hY ▸ hx)⟩)⁻¹ := rfl
      rw [this, map_inv]
      exact inv_mem ih
  have hg' : (g : G) ∈ Subgroup.closure {x | x ∈ S ∧ orderOf x = 3} := hY ▸ hg
  have := key (g : G) hg'
  exact this

end Theta

end CFSG.Quasithin.SzN17
