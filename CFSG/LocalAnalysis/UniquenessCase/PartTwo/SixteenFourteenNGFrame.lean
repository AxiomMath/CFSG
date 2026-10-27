module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {T : Type} [CommGroup T] [Finite T]

theorem s1614_rk_add_le {U C Y : Subgroup T} (hUC : U ≤ C) :
    rk ↥U + rk ↥(C ⊓ Y) ≤ rk ↥C + rk ↥(U ⊓ Y) := by
  have h1 := rk_sup_add_rk_inf U (C ⊓ Y)
  have h2 : rk ↥(U ⊔ C ⊓ Y) ≤ rk ↥C := rk_mono (sup_le hUC inf_le_left)
  have h3 : U ⊓ (C ⊓ Y) = U ⊓ Y := by rw [← inf_assoc, inf_eq_left.2 hUC]
  rw [h3] at h1
  omega

theorem s1614_rk_fixV_iSup {κ : Type} [Fintype κ] {B : κ → Subgroup T} (hind : iSupIndep B)
    {φ : MulAut T} (hφ : ∀ j, (B j).map φ.toMonoidHom ≤ B j) :
    rk ↥(fixV (Subgroup.zpowers φ) ⊓ (⨆ j, B j)) =
      ∑ j, rk ↥(fixV (Subgroup.zpowers φ) ⊓ B j) := by
  classical
  have hstab : ∀ {W : Subgroup T}, W.map φ.toMonoidHom ≤ W →
      ∀ x ∈ Subgroup.zpowers φ, ∀ w ∈ W, x w ∈ W := by
    intro W hW x hx w hw
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, φ ^ n = x :=
      (Submonoid.mem_powers_iff x φ).mp ((mem_powers_iff_mem_zpowers (x := φ) (y := x)).mpr hx)
    clear hx
    induction n with
    | zero => simpa using hw
    | succ n ih =>
      have h1 : (φ ^ (n + 1)) w = φ ((φ ^ n) w) := by rw [pow_succ']; rfl
      rw [h1]
      exact hW ⟨_, ih, rfl⟩
  have hmapB : ∀ j, (B j).map (commHom φ) ≤ B j := by
    rintro j _ ⟨w, hw, rfl⟩
    exact (B j).mul_mem (hφ j ⟨w, hw, rfl⟩) ((B j).inv_mem hw)
  have hS : (⨆ j, B j).map φ.toMonoidHom ≤ ⨆ j, B j := by
    rw [Subgroup.map_iSup]
    exact iSup_mono fun j => hφ j
  have hindg : iSupIndep (fun j => (B j).map (commHom φ)) := hind.mono hmapB
  have hSsum : rk ↥(⨆ j, B j) = ∑ j, rk ↥(B j) := by
    have h := rk_iSup_biSup_eq_sum B hind Finset.univ
    have e : (⨆ i ∈ (Finset.univ : Finset κ), B i) = ⨆ j, B j := by simp
    rwa [e] at h
  have hgsum : rk ↥(⨆ j, (B j).map (commHom φ)) = ∑ j, rk ↥((B j).map (commHom φ)) := by
    have h := rk_iSup_biSup_eq_sum (fun j => (B j).map (commHom φ)) hindg Finset.univ
    have e : (⨆ i ∈ (Finset.univ : Finset κ), (B i).map (commHom φ)) =
        ⨆ j, (B j).map (commHom φ) := by simp
    rwa [e] at h
  have hS1 := rk_commSub_add_rk_inf_fixV (hstab hS)
  have hcS : commSub (⨆ j, B j) (Subgroup.zpowers φ) = ⨆ j, (B j).map (commHom φ) := by
    rw [commSub_zpowers_eq_map (hstab hS), Subgroup.map_iSup]
  have hj : ∀ j, rk ↥((B j).map (commHom φ)) + rk ↥(B j ⊓ fixV (Subgroup.zpowers φ)) =
      rk ↥(B j) := by
    intro j
    have := rk_commSub_add_rk_inf_fixV (hstab (hφ j))
    rwa [commSub_zpowers_eq_map (hstab (hφ j))] at this
  rw [hcS, hgsum, hSsum] at hS1
  have hsum : ∑ j, rk ↥((B j).map (commHom φ)) + ∑ j, rk ↥(B j ⊓ fixV (Subgroup.zpowers φ)) =
      ∑ j, rk ↥(B j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hj j
  have hc : ∀ j, rk ↥(fixV (Subgroup.zpowers φ) ⊓ B j) =
      rk ↥(B j ⊓ fixV (Subgroup.zpowers φ)) := fun j => by rw [inf_comm]
  have hc' : rk ↥(fixV (Subgroup.zpowers φ) ⊓ (⨆ j, B j)) =
      rk ↥((⨆ j, B j) ⊓ fixV (Subgroup.zpowers φ)) := by rw [inf_comm]
  rw [hc', Finset.sum_congr rfl fun j _ => hc j]
  omega

theorem s1614_rk_fixV_normalizing {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hind : iSupIndep Y) (hsup : ⨆ i, Y i = ⊤) {φ : MulAut T}
    (hφ : ∀ i, (Y i).map φ.toMonoidHom ≤ Y i) {m : ℕ}
    (hm : ∀ i, rk ↥(fixV (Subgroup.zpowers φ) ⊓ Y i) ≤ m) :
    rk ↥(fixV (Subgroup.zpowers φ)) ≤ Fintype.card ι * m := by
  have h := s1614_rk_fixV_iSup hind hφ
  rw [hsup, inf_top_eq] at h
  rw [h]
  calc ∑ i, rk ↥(fixV (Subgroup.zpowers φ) ⊓ Y i) ≤ ∑ _i : ι, m :=
        Finset.sum_le_sum fun i _ => hm i
    _ = Fintype.card ι * m := by simp

theorem s1614_rk_fixV_swap {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hind : iSupIndep Y) (hsup : ⨆ i, Y i = ⊤) {d : ℕ} (hrk : ∀ i, rk ↥(Y i) = d)
    {φ : MulAut T} {a b : ι} (hab : a ≠ b) (hφa : (Y a).map φ.toMonoidHom = Y b)
    (hφb : (Y b).map φ.toMonoidHom = Y a)
    (hφ : ∀ i, i ≠ a → i ≠ b → (Y i).map φ.toMonoidHom = Y i) {m : ℕ}
    (hm : ∀ i, i ≠ a → i ≠ b → rk ↥(fixV (Subgroup.zpowers φ) ⊓ Y i) ≤ m) :
    rk ↥(fixV (Subgroup.zpowers φ)) ≤ d + (Fintype.card ι - 2) * m := by
  classical
  set C := fixV (Subgroup.zpowers φ) with hCdef
  let κ := {i : ι // i ≠ a ∧ i ≠ b}
  set P : Subgroup T := Y a ⊔ Y b with hP
  set Q : Subgroup T := ⨆ i : κ, Y i.1 with hQ
  have hdab : Disjoint (Y a) (Y b) := hind.pairwiseDisjoint hab
  have hS : Disjoint ({a, b} : Set ι) {i | i ≠ a ∧ i ≠ b} := by
    rw [Set.disjoint_left]
    rintro i (rfl | rfl) h
    · exact h.1 rfl
    · exact h.2 rfl
  have hPset : (⨆ i ∈ ({a, b} : Set ι), Y i) = P := by
    rw [hP, iSup_pair]
  have hQset : (⨆ i ∈ {i : ι | i ≠ a ∧ i ≠ b}, Y i) = Q := by
    rw [hQ, iSup_subtype']
    rfl
  have hPQ : Disjoint P Q := by
    rw [← hPset, ← hQset]
    exact hind.disjoint_biSup_biSup' hS (Set.toFinite _)
  have hPQtop : P ⊔ Q = ⊤ := by
    rw [← hPset, ← hQset, ← iSup_union, ← hsup]
    have hU : ({a, b} : Set ι) ∪ {i | i ≠ a ∧ i ≠ b} = Set.univ := by
      ext i
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
        Set.mem_univ, iff_true]
      tauto
    rw [hU]
    simp
  have hPφ : P.map φ.toMonoidHom ≤ P := by
    rw [hP, Subgroup.map_sup, hφa, hφb, sup_comm]
  have hQφ : Q.map φ.toMonoidHom ≤ Q := by
    rw [hQ, Subgroup.map_iSup]
    exact iSup_mono fun i => (hφ i.1 i.2.1 i.2.2).le
  have hB2 : iSupIndep (fun c : Bool => if c then P else Q) := by
    rw [iSupIndep_pair (i := true) (j := false) (by decide) (by decide)]
    simpa using hPQ
  have hB2stab : ∀ c : Bool, ((if c then P else Q) : Subgroup T).map φ.toMonoidHom ≤
      (if c then P else Q) := by
    intro c
    cases c
    · simpa using hQφ
    · simpa using hPφ
  have h2 := s1614_rk_fixV_iSup hB2 hB2stab
  have hsup2 : (⨆ c : Bool, (if c then P else Q : Subgroup T)) = ⊤ := by
    rw [iSup_bool_eq]
    simpa using hPQtop
  rw [hsup2, inf_top_eq, Fintype.sum_bool] at h2
  have h2' : rk ↥C = rk ↥(C ⊓ P) + rk ↥(C ⊓ Q) := by simpa using h2
  have hQ2 := s1614_rk_fixV_iSup (B := fun i : κ => Y i.1) (hind.comp Subtype.val_injective)
    (φ := φ) (fun i => (hφ i.1 i.2.1 i.2.2).le)
  have hQsum : rk ↥(C ⊓ Q) ≤ (Fintype.card ι - 2) * m := by
    rw [hQ, hQ2]
    calc ∑ i : κ, rk ↥(C ⊓ Y i.1) ≤ ∑ _i : κ, m :=
          Finset.sum_le_sum fun i _ => hm i.1 i.2.1 i.2.2
      _ = Fintype.card κ * m := by simp
      _ = (Fintype.card ι - 2) * m := by
          congr 1
          rw [Fintype.card_subtype]
          have : Finset.univ.filter (fun i : ι => i ≠ a ∧ i ≠ b) = Finset.univ \ {a, b} := by
            ext i
            simp
          rw [this, Finset.card_univ_diff, Finset.card_pair hab]
  have hYbC : C ⊓ Y b = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyC, hyB⟩ := hy
    have hyfix : φ y = y := mem_fixV_zpowers_iff_apply.mp hyC
    have hyA : y ∈ Y a := by
      have h : φ y ∈ (Y b).map φ.toMonoidHom := Subgroup.mem_map.2 ⟨y, hyB, rfl⟩
      rw [hφb] at h
      rwa [hyfix] at h
    have hyAB : y ∈ Y a ⊓ Y b := ⟨hyA, hyB⟩
    rw [hdab.eq_bot, Subgroup.mem_bot] at hyAB
    exact hyAB
  have hinf : (C ⊓ P) ⊓ Y b = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨⟨hxC, -⟩, hxB⟩ := hx
    have hxCB : x ∈ C ⊓ Y b := ⟨hxC, hxB⟩
    rw [hYbC, Subgroup.mem_bot] at hxCB
    exact hxCB
  have hrkP : rk ↥P = 2 * d := by
    have h : rk ↥P + rk ↥(Y a ⊓ Y b) = rk ↥(Y a) + rk ↥(Y b) := rk_sup_add_rk_inf (Y a) (Y b)
    rw [hdab.eq_bot, rk_bot] at h
    have := hrk a
    have := hrk b
    omega
  have hCP : rk ↥(C ⊓ P) ≤ d := by
    have h1 := rk_sup_add_rk_inf (C ⊓ P) (Y b)
    rw [hinf, rk_bot] at h1
    have h2 : rk ↥((C ⊓ P) ⊔ Y b) ≤ rk ↥P := rk_mono (sup_le inf_le_right le_sup_right)
    have := hrk b
    omega
  omega

theorem s1614_frame (hT : ∀ t : T, t ^ 2 = 1) {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hind : iSupIndep Y) (hinj : Function.Injective Y) (hsup : ⨆ i, Y i = ⊤) {d e : ℕ}
    (hrk : ∀ i, rk ↥(Y i) = d) (hd : 2 ≤ d) (he : e ≤ d + 1)
    (hn : 3 ≤ Fintype.card ι) {φ : MulAut T} (hperm : ∀ i, ∃ j, (Y i).map φ.toMonoidHom = Y j)
    (hC : e ≤ rkIdx (fixV (Subgroup.zpowers φ)) + 1) {U : Subgroup T}
    (hUC : U ≤ fixV (Subgroup.zpowers φ)) (hU : rkIdx U ≤ e) : ∃ c : ι, U ⊓ Y c ≠ ⊥ := by
  classical
  by_contra hcon
  have hcon' : ∀ c, U ⊓ Y c = ⊥ := fun c => by
    by_contra h
    exact hcon ⟨c, h⟩
  have hrkT : rk T = Fintype.card ι * d := by
    have h1 := rk_iSup_biSup_eq_sum Y hind Finset.univ
    have h2 : (⨆ i ∈ (Finset.univ : Finset ι), Y i : Subgroup T) = ⊤ := by
      rw [← hsup]
      simp
    rw [h2, rk_top] at h1
    rw [h1]
    simp [hrk]
  have hCU : rkIdx (fixV (Subgroup.zpowers φ)) ≤ rkIdx U := rkIdx_anti hUC
  have hrkC := rk_add_rkIdx (fixV (Subgroup.zpowers φ))
  have hrkU := rk_add_rkIdx U
  have hblock : ∀ i, rk ↥(fixV (Subgroup.zpowers φ) ⊓ Y i) ≤
      rkIdx U - rkIdx (fixV (Subgroup.zpowers φ)) := by
    intro i
    have h := s1614_rk_add_le (Y := Y i) hUC
    rw [hcon' i, rk_bot] at h
    omega
  have hlt : rkIdx (fixV (Subgroup.zpowers φ)) < 2 * d := by omega
  have hδ : rkIdx U - rkIdx (fixV (Subgroup.zpowers φ)) = 0 ∨
      rkIdx U - rkIdx (fixV (Subgroup.zpowers φ)) = 1 := by omega
  obtain ⟨n, hn'⟩ : ∃ n, Fintype.card ι = n + 3 := ⟨Fintype.card ι - 3, by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  have hnd : (n + 3) * (d' + 2) = n * d' + 2 * n + 3 * d' + 6 := by ring
  have hnd' : Fintype.card ι * (d' + 2) = n * d' + 2 * n + 3 * d' + 6 := by rw [hn', hnd]
  rcases s16n9b_case4_rank_moved hT hind hinj hrk hperm hlt with
    hid | ⟨a, b, hab, hφa, hφb, hφ⟩
  · have h := s1614_rk_fixV_normalizing hind hsup (fun i => (hid i).le) hblock
    rcases hδ with h0 | h1
    · rw [h0] at h
      simp only [mul_zero] at h
      omega
    · rw [h1, hn'] at h
      simp only [mul_one] at h
      rw [hn'] at hrkT
      omega
  · have h := s1614_rk_fixV_swap hind hsup hrk hab hφa hφb hφ (m := rkIdx U -
      rkIdx (fixV (Subgroup.zpowers φ))) (fun i _ _ => hblock i)
    rcases hδ with h0 | h1
    · rw [h0] at h
      simp only [mul_zero, add_zero] at h
      omega
    · rw [h1, hn'] at h
      simp only [mul_one] at h
      rw [hn'] at hrkT
      omega

theorem s1614_frame_hrow (hT : ∀ t : T, t ^ 2 = 1) {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hind : iSupIndep Y) (hinj : Function.Injective Y) (hsup : ⨆ i, Y i = ⊤) {d e : ℕ}
    (hrk : ∀ i, rk ↥(Y i) = d) (hd : 2 ≤ d) (he : e ≤ d + 1)
    (hn : 3 ≤ Fintype.card ι) {φ : MulAut T} (hperm : ∀ i, ∃ j, (Y i).map φ.toMonoidHom = Y j)
    (hC : e ≤ rkIdx (fixV (Subgroup.zpowers φ)) + 1) {X : Subgroup (MulAut T)} {p : ℕ}
    (hB : ∀ i, ∃ B : Subgroup (MulAut T), B ≤ X ∧ IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧
      ∀ y ∈ Y i, y ∈ fixV B)
    {W : Subgroup T} (hWC : W ≤ fixV (Subgroup.zpowers φ)) (hW : rkIdx W ≤ e) :
    ∃ z ∈ W, z ≠ 1 ∧ ∃ B : Subgroup (MulAut T), B ≤ X ∧ IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧
      z ∈ fixV B := by
  obtain ⟨c, hc⟩ := s1614_frame hT hind hinj hsup hrk hd he hn hperm hC hWC hW
  obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc
  obtain ⟨B, hBX, hBp, hBc, hBfix⟩ := hB c
  refine ⟨z.1, z.2.1, fun h => hz (Subtype.ext h), B, hBX, hBp, hBc, hBfix _ z.2.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
