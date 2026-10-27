module

public import CFSG.Quasithin.Background.SmithB51LnTopC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix Module
open scoped Matrix

theorem arith_excl {a b n : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b ≤ n) (hn : n ≤ 5)
    (h : 2 * a + b ≤ a * b) : False := by
  have ha5 : a ≤ 4 := by omega
  have hb5 : b ≤ 4 := by omega
  interval_cases a <;> interval_cases b <;> omega

section Copies

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)} {n : ℕ}

theorem rank_bounds {X : Subgroup V} {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hX : RealM L X ⊥ π mat)
    (hAL : A ≤ L) (hA2 : IsPGroup 2 ↥A) (hAne : A ≠ ⊥) (hquad : IsQuadratic A) :
    (n - finrank (ZMod 2) (fixN (pre π A))) + finrank (ZMod 2) (commN (pre π A)) ≤ n ∧
      rk A ≤ (n - finrank (ZMod 2) (fixN (pre π A))) * finrank (ZMod 2) (commN (pre π A)) ∧
      1 ≤ n - finrank (ZMod 2) (fixN (pre π A)) ∧ 1 ≤ finrank (ZMod 2) (commN (pre π A)) ∧
      n - finrank (ZMod 2) (fixD (pre π A)) = finrank (ZMod 2) (commN (pre π A)) := by
  have hπ : Function.Bijective π := ⟨hX.injective (Or.inl rfl), hX.1⟩
  have h1 := Submodule.finrank_mono (hX.commN_le_fixN hquad)
  have h2 := finrank_fixN_le (pre π A)
  have h3 := rk_le_mul_pre hπ hAL hA2
  have h4 := finrank_fixM_lt hπ (Or.inl rfl) hAL hAne
  have h5 := finrank_fixM_lt hπ (Or.inr rfl) hAL hAne
  have h6 := finrank_fixD_add (pre π A)
  rw [fixM_mat] at h4
  rw [fixM_dmat] at h5
  exact ⟨by omega, h3, by omega, by omega, by omega⟩

omit [Finite V] in
theorem directSum_cons {k : ℕ} {I : Fin k → Subgroup V} {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    {X : Subgroup V} (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    (hXI : X ⊓ (⨆ i, I i) = ⊥) (hsum : X ⊔ (⨆ i, I i) = ⊤) (hI : ∀ i, RealM L (I i) ⊥ π mat)
    (hX : RealM L X ⊥ π mat) :
    DirectSumOfCopies L ⊤ ⊥ (FFModel.nat (StatedSL n (ZMod 2))) (k + 1) := by
  set J : Fin (k + 1) → Subgroup V := Fin.cons X I with hJ
  have hJ0 : J 0 = X := by rw [hJ, Fin.cons_zero]
  have hJs : ∀ i, J i.succ = I i := fun i => by rw [hJ, Fin.cons_succ]
  have hsupJ : (⨆ i, J i) = X ⊔ ⨆ i, I i := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      induction i using Fin.cases with
      | zero => rw [hJ0]; exact le_sup_left
      | succ j => rw [hJs]; exact (le_iSup I j).trans le_sup_right
    · refine sup_le ?_ (iSup_le fun j => ?_)
      · rw [← hJ0]; exact le_iSup J 0
      · rw [← hJs]; exact le_iSup J j.succ
  refine ⟨J, π, fun i => bot_le, fun i => ?_, ?_, fun i => ?_⟩
  · rw [bot_sup_eq]
    induction i using Fin.cases with
    | zero =>
      rw [hJ0, eq_bot_iff, ← hXI]
      refine inf_le_inf_left _ (iSup₂_le fun j hj => ?_)
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
      rw [hJs]
      exact le_iSup I j'
    | succ i' =>
      have hle : (⨆ (j : Fin (k + 1)) (_ : j ≠ i'.succ), J j) ≤
          X ⊔ ⨆ (j : Fin k) (_ : j ≠ i'), I j := by
        refine iSup₂_le fun j hj => ?_
        induction j using Fin.cases with
        | zero => rw [hJ0]; exact le_sup_left
        | succ j' =>
          have hj' : j' ≠ i' := fun h => hj (h ▸ rfl)
          rw [hJs]
          exact (le_iSup₂_of_le (f := fun (j : Fin k) (_ : j ≠ i') => I j) j' hj' le_rfl).trans
            le_sup_right
      rw [hJs, eq_bot_iff]
      rintro y ⟨hy1, hy2⟩
      obtain ⟨x, hx, z, hz, hxz⟩ := Subgroup.mem_sup.1 (hle hy2)
      have hzI : z ∈ ⨆ i, I i :=
        (iSup₂_le fun j _ => le_iSup I j : (⨆ (j : Fin k) (_ : j ≠ i'), I j) ≤ ⨆ i, I i) hz
      have hyI : y ∈ ⨆ i, I i := le_iSup I i' hy1
      have hx1 : x ∈ X ⊓ ⨆ i, I i := ⟨hx, by
        rw [eq_mul_inv_of_mul_eq hxz]
        exact Subgroup.mul_mem _ hyI (Subgroup.inv_mem _ hzI)⟩
      rw [hXI, Subgroup.mem_bot] at hx1
      rw [hx1, one_mul] at hxz
      have : y ∈ I i' ⊓ ⨆ (j : Fin k) (_ : j ≠ i'), I j := ⟨hy1, hxz ▸ hz⟩
      rw [hind i'] at this
      exact this
  · rw [bot_sup_eq, hsupJ, hsum]
  · induction i using Fin.cases with
    | zero => rw [hJ0]; exact realM_mat_iff.1 hX
    | succ i' => rw [hJs]; exact realM_mat_iff.1 (hI i')

theorem top_copies (hB492 : AsB492Split) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hn : n = 4 ∨ n = 5) (hA : IsFFStarMin G A) (hAL : A ≤ L) {U₀ : Subgroup V} (hU₀top : U₀ ≠ ⊤)
    {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hRtop : RealM L ⊤ U₀ π mat) {k : ℕ} (hk1 : 1 ≤ k)
    {I : Fin k → Subgroup V} {π₀ : ↥(StatedSL n (ZMod 2)) →* ↥L} (hI : ∀ i, RealM L (I i) ⊥ π₀ mat)
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥) (hsum : ⨆ i, I i = U₀) :
    SumNatDual L ⊤ n ∨ ∃ k', 1 ≤ k' ∧ k' ≤ n - 1 ∧
      DirectSumOfCopies L ⊤ ⊥ (FFModel.nat (StatedSL n (ZMod 2))) k' := by
  have hquad : IsQuadratic A := B1_4_3 hV hA
  have hA2 : IsPGroup 2 ↥A := hA.1.2.2.1.isPGroup
  have hAne : A ≠ ⊥ := hA.1.2.1
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hn5 : n ≤ 5 := by rcases hn with rfl | rfl <;> norm_num
  have hπ₀ : Function.Bijective π₀ := ⟨(hI ⟨0, hk1⟩).injective (Or.inl rfl), (hI ⟨0, hk1⟩).1⟩
  obtain ⟨hab, hrk, ha1, hb1, hD⟩ := rank_bounds (hI ⟨0, hk1⟩) hAL hA2 hAne hquad
  have hinv : ∀ i, ∀ b ∈ A, ∀ x ∈ I i, b x ∈ I i :=
    fun i b hb x hx => (hI i).2.2.1 ⟨b, hAL hb⟩ x hx
  have hU₀ : rkSub A U₀ = k * (n - finrank (ZMod 2) (fixN (pre π₀ A))) := by
    rw [← hsum, rkSub_iSup I hinv hind, Finset.sum_congr rfl (fun i _ => (hI i).rkSub_eq hAL),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, fixM_mat]
  have e1 := rkSub_ge_sec hV (le_top : U₀ ≤ ⊤) (le_stabSub_top A)
  have e2 := rkSub_top A
  have e3 := rkIdx_fixV_le_rk hV hA.1
  rcases hRtop.align hn3 (Or.inl rfl) hπ₀ with hT | hT
  ·
    have et := hT.rkIdx_fixV_autSec hAL
    rw [fixM_mat] at et
    have hk : k + 1 ≤ n - 1 := by
      have h1 : (k + 1) * (n - finrank (ZMod 2) (fixN (pre π₀ A))) ≤
          finrank (ZMod 2) (commN (pre π₀ A)) * (n - finrank (ZMod 2) (fixN (pre π₀ A))) := by
        rw [add_mul, one_mul, mul_comm (finrank (ZMod 2) (commN (pre π₀ A)))]
        omega
      have h2 := Nat.le_of_mul_le_mul_right h1 ha1
      omega
    have hT' : RealM L ⊤ (⨆ i ∈ (Finset.univ : Finset (Fin k)), I i) π₀ mat :=
      hT.congr_sub rfl (by simp [hsum])
    obtain ⟨X, hXinv, -, hXU, hXU'⟩ :=
      split_copies hB492 hV h hn hA.1 hAL hquad hI hind Finset.univ ⊤ hT'
    have hUniv : (⨆ i ∈ (Finset.univ : Finset (Fin k)), I i) = U₀ := by simp [hsum]
    rw [hUniv] at hXU hXU'
    have hRX : RealM L X ⊥ π₀ mat := hT.complement le_top (by rw [sup_comm, hXU'])
      (by rw [inf_comm, hXU]) (fun l x hx => hXinv l l.2 x hx)
    right
    exact ⟨k + 1, by omega, hk, directSum_cons hind (by rw [hsum]; exact hXU)
      (by rw [hsum]; exact hXU') hI hRX⟩
  ·
    have et := hT.rkIdx_fixV_autSec hAL
    rw [fixM_dmat, hD] at et
    have hk : k = 1 := by
      by_contra hk2
      have hk2 : 2 ≤ k := by omega
      have h1 := Nat.mul_le_mul_right (n - finrank (ZMod 2) (fixN (pre π₀ A))) hk2
      exact arith_excl ha1 hb1 hab hn5 (by omega)
    subst hk
    have hI0 : I ⟨0, hk1⟩ = U₀ := by
      rw [← hsum]
      exact le_antisymm (le_iSup I _) (iSup_le fun i => by rw [Subsingleton.elim i ⟨0, hk1⟩])
    have h1 : RealM L U₀ ⊥ π₀ mat := (hI ⟨0, hk1⟩).congr_sub hI0 rfl
    have hn2 : 2 ≤ n := by omega
    have hnc : ¬ commSub ⊤ L ≤ ⊥ := fun hle => hU₀top (by
      have := hRtop.commSub_sup (Or.inl rfl) hn2
      rwa [le_bot_iff.1 hle, bot_sup_eq] at this)
    have c : SecCtx G L A ⊤ ⊥ := ⟨hA.1.1, hA.1.2.2.1, hAne, bot_le,
      sup_le (le_stabSub_top L) (le_stabSub_top A), stabSub_bot_le _, hnc⟩
    obtain ⟨X, hXinv, -, -, hXU, hXU'⟩ := split_sec hB492 hV h hn hA.1 hAL hquad c h1 (Or.inr hT)
    have hRX : RealM L X ⊥ π₀ dmat := hT.complement le_top (by rw [sup_comm, hXU'])
      (by rw [inf_comm, hXU]) (fun l x hx => hXinv l l.2 x hx)
    left
    exact ⟨hn, π₀, U₀, X, ⟨by rw [sup_comm, hXU'], by rw [inf_comm, hXU]⟩, realM_mat_iff.1 h1,
      realM_dmat_iff.1 hRX⟩

theorem top_sumNatDual_false (hV : ∀ v : V, v ^ 2 = 1) (hn : n = 4 ∨ n = 5)
    (hA : IsFFStarMin G A) (hAL : A ≤ L) {U₀ : Subgroup V} {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (hRtop : RealM L ⊤ U₀ π mat) {m : ℕ} (hS : SumNatDual L U₀ m) : False := by
  obtain ⟨hm, π₀, U₁, U₂, ⟨hsup, hinf⟩, h1, h2⟩ := hS
  have hR1 := realM_mat_iff.2 h1
  have hR2 := realM_dmat_iff.2 h2
  have hπ₀ : Function.Bijective π₀ := ⟨hR1.injective (Or.inl rfl), hR1.1⟩
  have hπ : Function.Bijective π := ⟨hRtop.injective (Or.inl rfl), hRtop.1⟩
  have hmn := eq_of_equiv_sl hm hn
    ((MulEquiv.ofBijective π₀ hπ₀).trans (MulEquiv.ofBijective π hπ).symm)
  subst hmn
  have hquad : IsQuadratic A := B1_4_3 hV hA
  have hA2 : IsPGroup 2 ↥A := hA.1.2.2.1.isPGroup
  have hm3 : 3 ≤ m := by rcases hm with rfl | rfl <;> norm_num
  have hm5 : m ≤ 5 := by rcases hm with rfl | rfl <;> norm_num
  obtain ⟨hab, hrk, ha1, hb1, hD⟩ := rank_bounds hR1 hAL hA2 hA.1.2.1 hquad
  have hinv1 : ∀ b ∈ A, ∀ x ∈ U₁, b x ∈ U₁ := fun b hb x hx => hR1.2.2.1 ⟨b, hAL hb⟩ x hx
  have hinv2 : ∀ b ∈ A, ∀ x ∈ U₂, b x ∈ U₂ := fun b hb x hx => hR2.2.2.1 ⟨b, hAL hb⟩ x hx
  have hU₀ := rkSub_sup hinv1 hinv2 hinf
  rw [hsup, hR1.rkSub_eq hAL, hR2.rkSub_eq hAL, fixM_mat, fixM_dmat, hD] at hU₀
  have e1 := rkSub_ge_sec hV (le_top : U₀ ≤ ⊤) (le_stabSub_top A)
  have e2 := rkSub_top A
  have e3 := rkIdx_fixV_le_rk hV hA.1
  rcases hRtop.align hm3 (Or.inl rfl) hπ₀ with hT | hT
  · have et := hT.rkIdx_fixV_autSec hAL
    rw [fixM_mat] at et
    exact arith_excl ha1 hb1 hab hm5 (by omega)
  · have et := hT.rkIdx_fixV_autSec hAL
    rw [fixM_dmat, hD] at et
    have key : 2 * finrank (ZMod 2) (commN (pre π₀ A)) + (m - finrank (ZMod 2) (fixN (pre π₀ A))) ≤
        finrank (ZMod 2) (commN (pre π₀ A)) * (m - finrank (ZMod 2) (fixN (pre π₀ A))) := by
      rw [Nat.mul_comm (finrank (ZMod 2) (commN (pre π₀ A)))]
      omega
    exact arith_excl hb1 ha1 (by omega) hm5 key

theorem top_structure (hB492 : AsB492Split) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hn : n = 4 ∨ n = 5) (hA : IsFFStarMin G A) (hAL : A ≤ L) {U₀ : Subgroup V} (hU₀top : U₀ ≠ ⊤)
    {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hRtop : RealM L ⊤ U₀ π mat)
    (hstr : (∃ π₀ : ↥(StatedSL n (ZMod 2)) →* ↥L, RealM L U₀ ⊥ π₀ mat) ∨
      (∃ m, SumNatDual L U₀ m) ∨
      (∃ m, (m = 4 ∨ m = 5) ∧ ∃ k, 1 ≤ k ∧ k ≤ m - 1 ∧
        DirectSumOfCopies L U₀ ⊥ (FFModel.nat (StatedSL m (ZMod 2))) k)) :
    SumNatDual L ⊤ n ∨ ∃ k', 1 ≤ k' ∧ k' ≤ n - 1 ∧
      DirectSumOfCopies L ⊤ ⊥ (FFModel.nat (StatedSL n (ZMod 2))) k' := by
  have hπ : Function.Bijective π := ⟨hRtop.injective (Or.inl rfl), hRtop.1⟩
  rcases hstr with ⟨π₀, hR₀⟩ | ⟨m, hS⟩ | ⟨m, hm, k, hk1, -, I, π₀, -, hind, hsum, hreal⟩
  · refine top_copies hB492 hV h hn hA hAL hU₀top hRtop (k := 1) le_rfl (I := fun _ => U₀)
      (fun _ => hR₀) (fun i => ?_) (by simp)
    have : (⨆ (j : Fin 1) (_ : j ≠ i), (fun _ => U₀) j) = ⊥ := by
      refine le_bot_iff.1 (iSup₂_le fun j hj => absurd (Subsingleton.elim j i) hj)
    rw [this, inf_bot_eq]
  · exact absurd hS fun hS => top_sumNatDual_false hV hn hA hAL hRtop hS
  · have hR := fun i => realM_mat_iff.2 (hreal i)
    have hπ₀ : Function.Bijective π₀ := ⟨(hR ⟨0, hk1⟩).injective (Or.inl rfl), (hR ⟨0, hk1⟩).1⟩
    have hmn := eq_of_equiv_sl hm hn
      ((MulEquiv.ofBijective π₀ hπ₀).trans (MulEquiv.ofBijective π hπ).symm)
    subst hmn
    refine top_copies hB492 hV h hn hA hAL hU₀top hRtop hk1 hR (fun i => ?_) ?_
    · have := hind i
      rwa [bot_sup_eq] at this
    · rwa [bot_sup_eq] at hsum

end Copies

end CFSG.Quasithin.B5.Ln
