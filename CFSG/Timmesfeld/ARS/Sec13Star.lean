module

public import CFSG.Timmesfeld.ARS.Sec13Centralizer

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem conjSet_lambdaSet (hR : IsRootClass R) (X : Subgroup G) (g : G) :
    conjSet (lambdaSet R X) g = lambdaSet R (conjSub X g) := by
  ext Y
  rw [mem_conjSet]
  constructor
  · intro hY
    have := conjSub_mem_lambdaSet hR hY g
    rwa [Plane.conjSub_inv_conjSub] at this
  · intro hY
    have := conjSub_mem_lambdaSet hR hY g⁻¹
    rwa [Plane.conjSub_conjSub_inv] at this

theorem conjSet_insert_insert_inter (hR : IsRootClass R) {A B : Subgroup G} {g : G}
    (hB : conjSub B g = B) (hA : conjSub A g = A) :
    conjSet (insert B (insert A (lambdaSet R B ∩ lambdaSet R A))) g =
      insert B (insert A (lambdaSet R B ∩ lambdaSet R A)) := by
  have hinj : Function.Injective fun X : Subgroup G => conjSub X g := fun X Y h => by
    have := congrArg (fun Z => conjSub Z g⁻¹) h
    simpa only [Plane.conjSub_conjSub_inv] using this
  rw [conjSet, Set.image_insert_eq, Set.image_insert_eq, Set.image_inter hinj, ← conjSet,
    ← conjSet, conjSet_lambdaSet hR, conjSet_lambdaSet hR, hA, hB]

section General

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (h8 : Sec8 R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
include h hA h8 hmax hA₀

omit hmax in
theorem eq_or_mem_lambdaSet_of_inter_eq_empty {B D Y : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hD : D ∈ lambdaStar R A A₀) (hBD : B ≠ D)
    (hemp : deltaSet R A A₀ B ∩ deltaSet R A A₀ D = ∅) (hYB : Y ∈ lambdaSet R B)
    (hYD : Y ∈ lambdaSet R D) : Y = A ∨ Y ∈ lambdaSet R A := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hBR : B ∈ R := hB.1.1.1
  have hDR : D ∈ R := hD.1.1.1
  have hYR : Y ∈ R := hYB.1.1
  have hYA : Commuting A Y := by
    rw [commuting_iff_commutator_eq_bot, eq_bot_iff, ← inf_eq_bot hR hiso hBR hDR hBD]
    refine le_inf ?_ ?_
    · rw [← (Q_eq_M h hBR).2.2.1]
      exact Subgroup.commutator_mono (QD.le_M (mem_lambdaSet_comm hA hB.1)) (QD.le_M hYB)
    · rw [← (Q_eq_M h hDR).2.2.1]
      exact Subgroup.commutator_mono (QD.le_M (mem_lambdaSet_comm hA hD.1)) (QD.le_M hYD)
  by_cases hYA' : Y = A
  · exact Or.inl hYA'
  by_contra hYl
  obtain ⟨hY'Δ, ⟨m, hm, hYm⟩, -⟩ :=
    sup_inf_levi_mem_leviSet h hA h8.2 hA₀ ⟨hYR, hYA', hYA⟩ (not_or.1 hYl).2
  rw [← hYm] at hY'Δ
  have hmA : conjSub A m = A := conjSub_eq_self_iff.2 ((isPGroup_M hR hA).2.1 hm)
  have hfix : ∀ {X : Subgroup G}, X ∈ lambdaStar R A A₀ → Y ∈ lambdaSet R X →
      conjSub X m = X := by
    intro X hX hYX
    have h1 : conjSub X m ∈ lambdaSet R A := by
      have := conjSub_mem_lambdaSet hR hX.1 m
      rwa [hmA] at this
    have h2 : conjSub X m ∈ lambdaSet R (conjSub Y m) :=
      conjSub_mem_lambdaSet hR (mem_lambdaSet_comm hX.1.1.1 hYX) m
    have h3 := mem_lambdaStar_of_mem_lambdaSet hR hA₀ hY'Δ h1 h2
    have hle : conjSub X m ≤ A ⊔ X := by
      have h4 : ⁅X, M R A⁆ ≤ A :=
        (Subgroup.commutator_mono (QD.le_M hX.1) le_rfl).trans (Q_eq_M h hA).2.2.1.le
      exact (conjSub_le_commutator_sup (A := X) hm).trans (sup_le_sup_right h4 _)
    exact eq_of_le_sup_of_mem_lambdaStar h hA hA₀ hX h3 hle
  have hYmB : conjSub Y m ∈ lambdaSet R B := by
    have := conjSub_mem_lambdaSet hR hYB m
    rwa [hfix hB hYB] at this
  have hYmD : conjSub Y m ∈ lambdaSet R D := by
    have := conjSub_mem_lambdaSet hR hYD m
    rwa [hfix hD hYD] at this
  have hmem : conjSub Y m ∈ deltaSet R A A₀ B ∩ deltaSet R A A₀ D :=
    ⟨⟨hY'Δ, hYmB⟩, hY'Δ, hYmD⟩
  rw [hemp] at hmem
  exact hmem

theorem insert_insert_inter_eq {B D : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hD : D ∈ lambdaStar R A A₀) (hDB : D ∈ lambdaSet R B)
    (hemp : deltaSet R A A₀ B ∩ deltaSet R A A₀ D = ∅) :
    insert B (insert D (lambdaSet R B ∩ lambdaSet R D)) =
      insert B (insert A (lambdaSet R B ∩ lambdaSet R A)) := by
  have := h.finite
  have hR := h.root
  have hBR : B ∈ R := hB.1.1.1
  have hBD : B ≠ D := fun e => hDB.1.2.1 e.symm
  have hsub : insert B (insert D (lambdaSet R B ∩ lambdaSet R D)) ⊆
      insert B (insert A (lambdaSet R B ∩ lambdaSet R A)) := by
    rintro Y (rfl | rfl | ⟨hYB, hYD⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨hDB, hD.1⟩)
    · rcases eq_or_mem_lambdaSet_of_inter_eq_empty h hA h8 hA₀ hB hD hBD hemp hYB hYD with
        h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨hYB, h1⟩)
  refine hsub.antisymm' ?_ |>.symm
  have hBne : sigmaSet R B ≠ lambdaSet R B := (Sec8.of_mem hR hA hBR h8).2
  obtain ⟨c, hc, hcD⟩ := exists_mem_centralGroup_conjSub_eq_of_isSigmaMaximal h hBR hBne
    (isSigmaMaximal_centralGroup_of_mem hR hA hBR hmax) (mem_lambdaSet_comm hA hB.1) hDB
  have hcB : conjSub B c = B := conjSub_of_forall_commute fun b hb =>
    ((commuting_centralGroup (R := R) B) b hb c hc).symm
  have hinj : Function.Injective fun X : Subgroup G => conjSub X c := fun X Y h => by
    have := congrArg (fun Z => conjSub Z c⁻¹) h
    simpa only [Plane.conjSub_conjSub_inv] using this
  have himage : conjSet (insert B (insert A (lambdaSet R B ∩ lambdaSet R A))) c =
      insert B (insert D (lambdaSet R B ∩ lambdaSet R D)) := by
    rw [conjSet, Set.image_insert_eq, Set.image_insert_eq, Set.image_inter hinj, ← conjSet,
      ← conjSet, conjSet_lambdaSet hR, conjSet_lambdaSet hR, hcB, hcD]
  have hcard : (insert B (insert A (lambdaSet R B ∩ lambdaSet R A))).ncard =
      (insert B (insert D (lambdaSet R B ∩ lambdaSet R D))).ncard := by
    rw [← himage, conjSet, Set.ncard_image_of_injective _ hinj]
  exact (Set.eq_of_subset_of_ncard_le hsub hcard.le (Set.toFinite _)).symm.le

end General

namespace Sec13

variable {A A₀ : Subgroup G} (hS : Sec13 R A A₀)
include hS

theorem mem_lambdaStar_of_le_sup {B D P : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hD : D ∈ lambdaStar R A A₀) (hDB : D ∈ lambdaSet R B) (hP : P ∈ R) (hPle : P ≤ B ⊔ D) :
    P ∈ lambdaStar R A A₀ := by
  obtain ⟨-, -, -, -, -, -, hline⟩ := hS.exists_commutator_eq_of_mem_lambdaSet hB hD hDB
  exact hline P hP (sup_comm B D ▸ hPle)

theorem eq_or_mem_lambdaSet_of_inter_eq_empty {B D Y : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hD : D ∈ lambdaStar R A A₀) (hBD : B ≠ D)
    (hemp : deltaSet R A A₀ B ∩ deltaSet R A A₀ D = ∅) (hYB : Y ∈ lambdaSet R B)
    (hYD : Y ∈ lambdaSet R D) : Y = A ∨ Y ∈ lambdaSet R A :=
  _root_.CFSG.Timmesfeld.ARS.eq_or_mem_lambdaSet_of_inter_eq_empty hS.hyp hS.mem hS.sec8 hS.opp
    hB hD hBD hemp hYB hYD

theorem insert_insert_inter_eq {B D : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hD : D ∈ lambdaStar R A A₀) (hDB : D ∈ lambdaSet R B)
    (hemp : deltaSet R A A₀ B ∩ deltaSet R A A₀ D = ∅) :
    insert B (insert D (lambdaSet R B ∩ lambdaSet R D)) =
      insert B (insert A (lambdaSet R B ∩ lambdaSet R A)) :=
  _root_.CFSG.Timmesfeld.ARS.insert_insert_inter_eq hS.hyp hS.mem hS.sec8 hS.max hS.opp hB hD
    hDB hemp

theorem exists_mem_omegaSet_psiSet {B D : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hD : D ∈ lambdaStar R A A₀) (hDB : D ∈ lambdaSet R B) :
    ∃ E ∈ omegaSet R B, A ∈ psiSet R E ∧ D ∈ psiSet R E := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hA₀ := hS.opp
  have hBR : B ∈ R := hB.1.1.1
  have hDR : D ∈ R := hD.1.1.1
  have hline : ∀ X ∈ R, X ≤ B ⊔ D → X ∈ lambdaSet R A := fun X hX hXle =>
    (hS.mem_lambdaStar_of_le_sup hB hD hDB hX hXle).1
  have hpl := plane hR hiso hA hBR hDB hline
  have hDAB : ¬ D ≤ A ⊔ B := fun hle =>
    hDB.1.2.1 (eq_of_le_sup_of_mem_lambdaStar hS.hyp hA hA₀ hB hD hle)
  obtain ⟨W, hWR, hWle, hWA, hWB⟩ := exists_mem_le_sup_ne_ne hR hiso hA hB.1 A B
  have hWN : W ≤ A ⊔ B ⊔ D := hWle.trans le_sup_left
  have hDN : D ≤ A ⊔ B ⊔ D := le_sup_right
  have hWD : W ≠ D := fun e => hDAB (e ▸ hWle)
  obtain ⟨T, hTR, hT⟩ := Plane.exists_isElationGroup_of_le hR hiso hA hBR hDB hline hWR hWN hDR
    hDN hWD
  have hsupAW : A ⊔ W = A ⊔ B := (mem_lambdaSet_of_le_sup hR hiso hA hB.1 hA le_sup_left hWR hWle
    hWA.symm).2
  have hAWD : ¬ A ≤ W ⊔ D := by
    intro hle
    have hDW : D ∈ lambdaSet R W := hpl.2.2.2.2.1 W hWR hWN D hDR hDN hWD
    have h1 := (mem_lambdaSet_of_le_sup hR hiso hWR hDW hWR le_sup_left hA hle hWA).2
    apply hDAB
    calc D ≤ W ⊔ D := le_sup_right
      _ = W ⊔ A := h1.symm
      _ = A ⊔ B := by rw [sup_comm, hsupAW]
  obtain ⟨t, ht, hAt⟩ := hT.2.2.2 A hA (le_sup_left.trans le_sup_left) hAWD B hBR
    (le_sup_right.trans hsupAW.symm.le) hWB.symm
  have htt : t * t = 1 := hR.mul_self T hTR t ht
  have hBt : conjSub B t = A := by
    rw [← hAt, ← conjSub_mul, htt, conjSub_one]
  have hDt : conjSub D t = D := conjSub_of_forall_commute fun d hd =>
    (hT.2.2.1 d (Subgroup.mem_sup_right hd) t ht).symm
  refine ⟨conjSub A₀ t, ⟨hR.conjSub_mem hA₀.1 t, ?_⟩, ⟨hA, ?_⟩, ⟨hDR, ?_⟩⟩
  · have := Opposite.conj hA₀.2 t
    rwa [hAt] at this
  · have := Sec3.special_conjSub hR hB.2.2 t
    rwa [hBt] at this
  · have := Sec3.special_conjSub hR hD.2.2 t
    rwa [hDt] at this

theorem deltaSet_inter_nonempty_of_mem_lambdaSet {B D : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hD : D ∈ lambdaStar R A A₀) (hDB : D ∈ lambdaSet R B) :
    (deltaSet R A A₀ B ∩ deltaSet R A A₀ D).Nonempty := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hBR : B ∈ R := hB.1.1.1
  have hDR : D ∈ R := hD.1.1.1
  rw [Set.nonempty_iff_ne_empty]
  intro hemp
  have hΛ := hS.insert_insert_inter_eq hB hD hDB hemp
  obtain ⟨E, hE, hAE, hDE⟩ := hS.exists_mem_omegaSet_psiSet hB hD hDB
  have hS' := hS.of_mem_omegaSet hBR hE
  have hAB : A ∈ lambdaSet R B := mem_lambdaSet_comm hA hB.1
  have hAs : A ∈ lambdaStar R B E := ⟨hAB, hAE⟩
  have hDs : D ∈ lambdaStar R B E := ⟨hDB, hDE⟩
  obtain ⟨Y, hY, hAYD⟩ := exists_commutator_eq_of_mem_lambdaStar hS'.hyp hBR hS'.sec8.2 hE hAs hDs
    (mem_lambdaSet_comm hA hD.1)
  have hsAY : Special R A Y := special_of_commutator_mem_of_mem_leviSet hS'.hyp hBR hAs hY
    (hAYD ▸ hDR)
  have hYD : Y ∈ lambdaSet R D := by
    have := (mem_lambdaSet_commutator hR hiso hA hY.1.1 hsAY).2
    rwa [hAYD] at this
  obtain ⟨-, X, hX, hYX, hAX⟩ :=
    exists_opposite_of_mem_lambdaStar hS'.hyp hBR hS'.sec8.2 hE hY hAs hsAY
  have hgen := hS'.gen_inter_lambdaSet_sup_eq_levi hX hY hYX.symm
  set Λ := insert B (insert A (lambdaSet R B ∩ lambdaSet R A)) with hΛdef
  have hstab : levi R B E ≤ stabSet Λ := by
    rw [← hgen]
    refine sup_le (gen_le fun Z hZ => fun z hz => mem_stabSet.2 ?_) fun y hy => mem_stabSet.2 ?_
    · have hZA := commuting_of_mem_deltaSet_of_mem_lambdaSet hS'.hyp hBR hE hAs
        ⟨hX, mem_lambdaSet_comm hX.1.1 hAX⟩ hZ.1 hZ.2
      exact conjSet_insert_insert_inter hR
        (conjSub_of_forall_commute fun b hb => (hZ.1.1.2.2 b hb z hz).symm)
        (conjSub_of_forall_commute fun a ha => (hZA z hz a ha))
    · rw [← hΛ]
      exact conjSet_insert_insert_inter hR
        (conjSub_of_forall_commute fun b hb => (hY.1.2.2 b hb y hy).symm)
        (conjSub_of_forall_commute fun d hd => (hYD.1.2.2 d hd y hy).symm)
  have hcomm : Commuting A (M R B) := by
    rw [M_eq_gen_lambdaStar hS'.hyp hBR hE, commuting_iff_le_centralizer]
    refine gen_le fun C hC => ?_
    obtain ⟨v, hv, rfl⟩ :=
      exists_mem_levi_conjSub_eq_of_isSigmaMaximal hS'.hyp hBR hS'.sec8.2 hS'.max hE hAs hC
    have hmem : conjSub A v ∈ Λ := by
      rw [← mem_stabSet.1 (hstab hv)]
      exact conjSub_mem_conjSet (Or.inr (Or.inl rfl)) v
    rcases hmem with h1 | h1 | h1
    · exact absurd h1 hC.1.1.2.1
    · rw [h1]; exact commuting_iff_le_centralizer.1 (hR.commuting_self hA)
    · exact commuting_iff_le_centralizer.1 h1.2.1.2.2
  have hmem : A ∈ {X | X ∈ R ∧ Commuting X (M R B)} := ⟨hA, hcomm⟩
  rw [(Q_eq_M hS.hyp hBR).2.2.2.1, Set.mem_singleton_iff] at hmem
  exact hB.1.1.2.1 hmem.symm

theorem exists_conjSub_ne_inter_nonempty {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    ∃ X ∈ leviSet R A A₀, ∃ x ∈ X, conjSub B x ≠ B ∧
      (deltaSet R A A₀ B ∩ conjSet (deltaSet R A A₀ B) x).Nonempty := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  obtain ⟨X, hX, hBX⟩ := exists_mem_leviSet_special hS.hyp hS.mem hS.sec8.2 hS.opp hB
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX.1.1
  have hxV : x ∈ levi R A A₀ := le_gen hX hx
  have hne : conjSub B x ≠ B := Sec3.conjSub_ne_of_special hR hiso hX.1.1 hB.1.1.1 hBX.symm hx hx1
  have hBx : conjSub B x ∈ lambdaStar R A A₀ := conjSub_mem_lambdaStar_of_mem_levi hR hB hxV
  have hBxB : conjSub B x ∈ lambdaSet R B := by
    have hle : conjSub B x ≤ B ⊔ ⁅B, X⁆ :=
      (conjSub_le_commutator_sup (A := B) hx).trans (sup_comm _ _).le
    obtain ⟨-, hCB, -⟩ := commutator_mem_lambdaStar hS.hyp hS.mem hS.sec8.2 hS.opp hB hX hBX
    exact (mem_lambdaSet_of_le_sup hR hiso hB.1.1.1 hCB hB.1.1.1 le_sup_left
      hBx.1.1.1 hle hne.symm).1
  refine ⟨X, hX, x, hx, hne, ?_⟩
  rw [conjSet_deltaSet hR hxV]
  exact hS.deltaSet_inter_nonempty_of_mem_lambdaSet hB hBx hBxB

end Sec13

end CFSG.Timmesfeld.ARS
