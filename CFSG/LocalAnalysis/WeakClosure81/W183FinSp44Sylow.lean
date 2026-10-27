module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44ModelAut
import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44SylowK
import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def inU (m : Nat) : Bool := m == uMat (e2 m 0 1) (e2 m 0 2) (e2 m 0 3) (e2 m 1 2)

private theorem w183finSp44_e2_lt (m i j : Nat) : e2 m i j < 4 := by
  unfold e2
  exact Nat.and_lt_two_pow (m >>> (2 * (4 * i + j))) (n := 2) (by norm_num)

private theorem w183finSp44_inU_eq (m : Nat) :
    inU m = true ↔ m = uMat (e2 m 0 1) (e2 m 0 2) (e2 m 0 3) (e2 m 1 2) := by
  simp [inU, beq_iff_eq]

private theorem w183finSp44_mem_Pel_iff {x : El} :
    x ∈ Pel ↔ ∃ a ∈ List.range 4, ∃ b ∈ List.range 4, ∃ c ∈ List.range 4,
      ∃ d ∈ List.range 4, ∃ j ∈ List.range 4, (uMat a b c d, j) = x := by
  simp only [Pel, List.mem_flatMap, List.mem_map]

private theorem w183finSp44_inU_uMat : ∀ a ∈ List.range 4, ∀ b ∈ List.range 4,
    ∀ c ∈ List.range 4, ∀ d ∈ List.range 4, inU (uMat a b c d) = true := by
  decide +kernel

private theorem w183finSp44_mem_Pel_of_inU {m j : Nat} (hm : inU m = true) (hj : j < 4) :
    (m, j) ∈ Pel := by
  have hm' := (w183finSp44_inU_eq m).mp hm
  rw [hm']
  simp only [Pel, List.mem_flatMap, List.mem_map]
  exact ⟨e2 m 0 1, List.mem_range.mpr (w183finSp44_e2_lt m 0 1),
    e2 m 0 2, List.mem_range.mpr (w183finSp44_e2_lt m 0 2),
    e2 m 0 3, List.mem_range.mpr (w183finSp44_e2_lt m 0 3),
    e2 m 1 2, List.mem_range.mpr (w183finSp44_e2_lt m 1 2), j, List.mem_range.mpr hj, rfl⟩

private theorem w183finSp44_mem_Pel_iff_inU {x : El} :
    x ∈ Pel ↔ inU x.1 = true ∧ x.2 < 4 := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, c, hc, d, hd, j, hj, hEq⟩ := w183finSp44_mem_Pel_iff.mp hx
    rw [← hEq]
    exact ⟨w183finSp44_inU_uMat a ha b hb c hc d hd, List.mem_range.mp hj⟩
  · rintro ⟨h1, h2⟩
    exact w183finSp44_mem_Pel_of_inU h1 h2

theorem U_mul : ∀ a ∈ List.range 4, ∀ b ∈ List.range 4, ∀ c ∈ List.range 4, ∀ d ∈ List.range 4,
    ∀ a' ∈ List.range 4, ∀ b' ∈ List.range 4, ∀ c' ∈ List.range 4, ∀ d' ∈ List.range 4,
      inU (mmul (uMat a b c d) (uMat a' b' c' d')) = true := by
  have pick : ∀ {f : Nat → Bool}, (List.range 4).all f = true → ∀ x < 4, f x = true :=
    fun h x hx => List.all_eq_true.mp h x (List.mem_range.mpr hx)
  have hX : ((List.range 4).all fun a => (List.range 4).all fun b => (List.range 4).all fun c =>
      (List.range 4).all fun d => (List.range 4).all fun p => (List.range 4).all fun q =>
        inU (mmul (uMat a b c d) (uMat 0 p q 0))) = true := by decide +kernel
  have hY : ((List.range 4).all fun a => (List.range 4).all fun b => (List.range 4).all fun c =>
      (List.range 4).all fun d => (List.range 4).all fun x =>
        inU (mmul (uMat a b c d) (uMat x 0 0 0))) = true := by decide +kernel
  have hZ : ((List.range 4).all fun a => (List.range 4).all fun b => (List.range 4).all fun c =>
      (List.range 4).all fun d => (List.range 4).all fun x =>
        inU (mmul (uMat a b c d) (uMat 0 0 0 x))) = true := by decide +kernel
  have hF : ((List.range 4).all fun a => (List.range 4).all fun b => (List.range 4).all fun c =>
      (List.range 4).all fun d => uMat a b c d ==
        mmul (mmul (uMat 0 (b ^^^ gmul a d) (c ^^^ gmul a (b ^^^ gmul a d)) 0) (uMat a 0 0 0))
          (uMat 0 0 0 d)) = true := by decide +kernel
  have lift : ∀ g, (∀ a < 4, ∀ b < 4, ∀ c < 4, ∀ d < 4, inU (mmul (uMat a b c d) g) = true) →
      ∀ X, inU X = true → inU (mmul X g) = true := fun g hg X hX => by
    rw [(w183finSp44_inU_eq X).mp hX]
    exact hg _ (w183finSp44_e2_lt X 0 1) _ (w183finSp44_e2_lt X 0 2) _
      (w183finSp44_e2_lt X 0 3) _ (w183finSp44_e2_lt X 1 2)
  have hgm : ∀ x < 4, ∀ y < 4, gmul x y < 2 ^ 2 := fun x hx y hy => by
    rw [gmul_eq_K x y hx hy]
    unfold gmulK
    exact Nat.and_lt_two_pow _ (by norm_num)
  intro a ha b hb c hc d hd a' ha' b' hb' c' hc' d' hd'
  have ha'4 := List.mem_range.mp ha'
  have hd'4 := List.mem_range.mp hd'
  have hp : b' ^^^ gmul a' d' < 4 :=
    Nat.xor_lt_two_pow (n := 2) (List.mem_range.mp hb') (hgm a' ha'4 d' hd'4)
  have hq : c' ^^^ gmul a' (b' ^^^ gmul a' d') < 4 :=
    Nat.xor_lt_two_pow (n := 2) (List.mem_range.mp hc') (hgm a' ha'4 _ hp)
  have hfac := beq_iff_eq.mp (pick (pick (pick (pick hF a' ha'4) b' (List.mem_range.mp hb')) c'
    (List.mem_range.mp hc')) d' hd'4)
  rw [hfac, ← mmul_assoc_K, ← mmul_assoc_K]
  refine lift _ (fun a ha b hb c hc d hd => pick (pick (pick (pick (pick hZ a ha) b hb) c hc) d hd)
    d' hd'4) _ (lift _ (fun a ha b hb c hc d hd =>
      pick (pick (pick (pick (pick hY a ha) b hb) c hc) d hd) a' ha'4) _
    (lift _ (fun a ha b hb c hc d hd =>
      pick (pick (pick (pick (pick (pick hX a ha) b hb) c hc) d hd) _ hp) _ hq) _
      (w183finSp44_inU_uMat a ha b hb c hc d hd)))

theorem rho_U : ∀ a ∈ List.range 4, ∀ b ∈ List.range 4, ∀ c ∈ List.range 4, ∀ d ∈ List.range 4,
    inU (rho (uMat a b c d)) = true := by
  decide +kernel

private theorem w183finSp44_inU_mul {m n : Nat} (hm : inU m = true) (hn : inU n = true) :
    inU (mmul m n) = true := by
  rw [(w183finSp44_inU_eq m).mp hm, (w183finSp44_inU_eq n).mp hn]
  exact U_mul _ (List.mem_range.mpr (w183finSp44_e2_lt m 0 1)) _
    (List.mem_range.mpr (w183finSp44_e2_lt m 0 2)) _
    (List.mem_range.mpr (w183finSp44_e2_lt m 0 3)) _
    (List.mem_range.mpr (w183finSp44_e2_lt m 1 2)) _
    (List.mem_range.mpr (w183finSp44_e2_lt n 0 1)) _
    (List.mem_range.mpr (w183finSp44_e2_lt n 0 2)) _
    (List.mem_range.mpr (w183finSp44_e2_lt n 0 3)) _
    (List.mem_range.mpr (w183finSp44_e2_lt n 1 2))

private theorem w183finSp44_inU_rho {m : Nat} (hm : inU m = true) : inU (rho m) = true := by
  rw [(w183finSp44_inU_eq m).mp hm]
  exact rho_U _ (List.mem_range.mpr (w183finSp44_e2_lt m 0 1)) _
    (List.mem_range.mpr (w183finSp44_e2_lt m 0 2)) _
    (List.mem_range.mpr (w183finSp44_e2_lt m 0 3)) _
    (List.mem_range.mpr (w183finSp44_e2_lt m 1 2))

private theorem w183finSp44_inU_rhoPow : ∀ (n : Nat) {m : Nat}, inU m = true →
    inU (rhoPow n m) = true
  | 0, _, hm => hm
  | n + 1, _, hm => w183finSp44_inU_rhoPow n (w183finSp44_inU_rho hm)

theorem Pel_valid : ∀ x ∈ Pel, validB x = true :=
  List.all_eq_true.mp pel_length_valid.2

theorem Pel_closed : ∀ x ∈ Pel, ∀ y ∈ Pel, gmulE x y ∈ Pel := by
  intro x hx y hy
  rw [w183finSp44_mem_Pel_iff_inU] at hx hy ⊢
  exact ⟨w183finSp44_inU_mul hx.1 (w183finSp44_inU_rhoPow x.2 hy.1),
    Nat.mod_lt _ (by norm_num)⟩

private theorem w183finSp44_inU_invE : ∀ x ∈ Pel, inU (invE x).1 = true := by
  have h : (Pel.all fun x => inU (invEK x).1) = true := by decide +kernel
  rw [invE_eq_K]
  exact List.all_eq_true.mp h

theorem Pel_inv : ∀ x ∈ Pel, invE x ∈ Pel := by
  intro x hx
  rw [w183finSp44_mem_Pel_iff_inU]
  exact ⟨w183finSp44_inU_invE x hx, Nat.mod_lt _ (by norm_num)⟩

noncomputable def Psub : Subgroup (MulAut S4) := Subgroup.closure (autOf '' {x | x ∈ Pel})

private def w183finSp44_autImage : Subgroup (MulAut S4) where
  carrier := {α | ∃ x ∈ Pel, autOf x = α}
  one_mem' := ⟨oneE, w183finSp44_mem_Pel_of_inU (by decide) (by norm_num), autOf_oneE⟩
  mul_mem' := by
    rintro α β ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨gmulE x y, Pel_closed x hx y hy,
      autOf_gmulE (Pel_valid x hx) (Pel_valid y hy)⟩
  inv_mem' := by
    rintro α ⟨x, hx, rfl⟩
    exact ⟨invE x, Pel_inv x hx, autOf_invE (Pel_valid x hx)⟩

theorem mem_Psub_iff (α : MulAut S4) : α ∈ Psub ↔ ∃ x ∈ Pel, autOf x = α := by
  have hle : Psub ≤ w183finSp44_autImage := by
    rw [Psub]
    refine (Subgroup.closure_le w183finSp44_autImage).mpr ?_
    rintro α ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hge : w183finSp44_autImage ≤ Psub := by
    rintro α ⟨x, hx, rfl⟩
    exact Subgroup.subset_closure ⟨x, hx, rfl⟩
  exact ⟨fun h => hle h, fun h => hge h⟩

private def w183finSp44_pelKey (x : El) : Nat :=
  e2 x.1 0 1 + 4 * (e2 x.1 0 2 + 4 * (e2 x.1 0 3 + 4 * (e2 x.1 1 2 + 4 * x.2)))

private theorem w183finSp44_pel_nodup : Pel.Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup w183finSp44_pelKey (by decide +kernel)

theorem card_Psub : Nat.card Psub = 1024 := by
  have hset : (Psub : Set (MulAut S4)) = autOf '' {x : El | x ∈ Pel} := by
    ext α
    exact mem_Psub_iff α
  have hinj : Set.InjOn autOf {x : El | x ∈ Pel} :=
    fun x hx y hy h => autOf_inj (Pel_valid x hx) (Pel_valid y hy) h
  have hfin : ({x : El | x ∈ Pel} : Set El).Finite := by
    have h : ({x : El | x ∈ Pel} : Set El) = ↑(Pel.toFinset) := by
      ext x
      simp
    rw [h]
    exact Finset.finite_toSet _
  have hpel : ({x : El | x ∈ Pel} : Set El).ncard = 1024 := by
    have h : ({x : El | x ∈ Pel} : Set El) = ↑(Pel.toFinset) := by
      ext x
      simp
    rw [Set.ncard_eq_toFinset_card _ hfin]
    have hto : hfin.toFinset = Pel.toFinset := by
      apply Finset.coe_injective
      rw [Set.Finite.coe_toFinset hfin, h]
    rw [hto, List.toFinset_card_of_nodup w183finSp44_pel_nodup, pel_length_valid.1]
  calc Nat.card Psub = (Psub : Set (MulAut S4)).ncard := rfl
    _ = (autOf '' {x : El | x ∈ Pel}).ncard := by rw [hset]
    _ = ({x : El | x ∈ Pel} : Set El).ncard := hinj.ncard_image
    _ = 1024 := hpel

theorem Psub_sylow : IsSylowIn 2 Psub ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 10) ?_, ?_⟩
  · rw [card_Psub]
    norm_num
  · rw [Subgroup.relIndex_top_right]
    have h1 : Psub.index * Nat.card Psub = Nat.card (MulAut S4) :=
      Subgroup.index_mul_card (H := Psub)
    rw [card_Psub, card_autS4] at h1
    have h2 : Psub.index = 3825 :=
      Nat.mul_right_cancel (m := 1024) (by norm_num) (by rw [h1])
    rw [h2]
    norm_num

theorem mem_Psub_inner_iff (α : MulAut S4) :
    α ∈ Psub ⊓ innAutOf S4 ↔ ∃ x ∈ Pel, x.2 = 0 ∧ autOf x = α := by
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hP, hI⟩
    obtain ⟨x, hx, hxα⟩ := (mem_Psub_iff α).mp hP
    exact ⟨x, hx, (autOf_inner_iff (Pel_valid x hx)).mp (hxα ▸ hI), hxα⟩
  · rintro ⟨x, hx, h0, hxα⟩
    exact ⟨(mem_Psub_iff α).mpr ⟨x, hx, hxα⟩,
      hxα ▸ (autOf_inner_iff (Pel_valid x hx)).mpr h0⟩

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
