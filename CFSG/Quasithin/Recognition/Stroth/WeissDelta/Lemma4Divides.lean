module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4Transfer

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

theorem ClosedGoodPath.stab_shift (W : ClosedGoodPath H Γ) (k : ℤ) :
    (W.shift k).stab = W.stab := by
  ext g
  constructor
  · intro hg
    rw [ClosedGoodPath.mem_stab_iff] at hg ⊢
    intro j
    have h := hg (j - k)
    rw [ClosedGoodPath.shift_x] at h
    rwa [show j - k + k = j by ring] at h
  · intro hg
    rw [ClosedGoodPath.mem_stab_iff] at hg ⊢
    intro i
    have h := hg (i + k)
    rw [ClosedGoodPath.shift_x]
    exact h

theorem ClosedGoodPath.kernelAt_shift (W : ClosedGoodPath H Γ) (k : ℤ) :
    (W.shift k).kernelAt 0 = W.kernelAt k := by
  rw [ClosedGoodPath.kernelAt, ClosedGoodPath.kernelAt, ClosedGoodPath.shift_x,
    ClosedGoodPath.stab_shift]
  simp

private theorem ClosedGoodPath.exists_smul_x_two_mul (W : ClosedGoodPath H Γ)
    (hloc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v)
    (m : ℕ) : ∃ g : H, g • W.x 0 = W.x (2 * (m : ℤ)) := by
  induction m with
  | zero => exact ⟨1, by simp⟩
  | succ m ih =>
      obtain ⟨g, hg⟩ := ih
      have hadj1 : Γ.Adj (W.x (2 * (m : ℤ) + 1)) (W.x (2 * (m : ℤ))) :=
        (W.adj (2 * (m : ℤ))).symm
      have hadj2 : Γ.Adj (W.x (2 * (m : ℤ) + 1)) (W.x (2 * (m : ℤ) + 2)) := by
        have h := W.adj (2 * (m : ℤ) + 1)
        rwa [show 2 * (m : ℤ) + 1 + 1 = 2 * (m : ℤ) + 2 by ring] at h
      obtain ⟨h, hw, hu⟩ := hloc _ _ _ hadj1 hadj2
      refine ⟨h * g, ?_⟩
      rw [mul_smul, hg, hu]
      rw [show 2 * (m : ℤ) + 2 = 2 * ((m + 1 : ℕ) : ℤ) by push_cast; ring]

private theorem ClosedGoodPath.exists_smul_x_two_mul_int (W : ClosedGoodPath H Γ)
    (hloc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v)
    (k : ℤ) : ∃ g : H, g • W.x 0 = W.x (2 * k) := by
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m : ℤ) :=
      ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
    subst hm
    simpa using W.exists_smul_x_two_mul hloc m
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, -k = (m : ℤ) :=
      ⟨(-k).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hkm : k = -(m : ℤ) := by omega
    obtain ⟨g, hg⟩ := (W.shift (2 * k)).exists_smul_x_two_mul hloc m
    have hg' : g • W.x (2 * k) = W.x 0 := by
      have h1 : (W.shift (2 * k)).x 0 = W.x (2 * k) := by
        rw [ClosedGoodPath.shift_x]
        simp
      have h2 : (W.shift (2 * k)).x (2 * (m : ℤ)) = W.x 0 := by
        rw [ClosedGoodPath.shift_x]
        rw [show 2 * (m : ℤ) + 2 * k = 0 by omega]
      rw [← h1, ← h2]
      exact hg
    refine ⟨g⁻¹, ?_⟩
    calc
      g⁻¹ • W.x 0 = g⁻¹ • (g • W.x (2 * k)) := by rw [hg']
      _ = W.x (2 * k) := by rw [inv_smul_smul]

private theorem ClosedGoodPath.hasThirdFix_add_nat [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (W : ClosedGoodPath H Γ) {K : Subgroup H} (hKW : K ≤ W.stab)
    (i : ℤ) (m : ℕ) :
    W.HasThirdFix K (i + (m : ℤ) * (n : ℤ)) ↔ W.HasThirdFix K i := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : W.HasThirdFix K (i + ((m + 1 : ℕ) : ℤ) * (n : ℤ)) ↔
          W.HasThirdFix K (i + (m : ℤ) * (n : ℤ)) := by
        have h := W.hasThirdFix_add_iff hn hM hW hKW (i + (m : ℤ) * (n : ℤ))
        rw [show i + ((m + 1 : ℕ) : ℤ) * (n : ℤ) =
          i + (m : ℤ) * (n : ℤ) + (n : ℤ) by push_cast; ring]
        exact h.symm
      exact hstep.trans ih

private theorem ClosedGoodPath.hasThirdFix_sub_nat [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (W : ClosedGoodPath H Γ) {K : Subgroup H} (hKW : K ≤ W.stab)
    (i : ℤ) (m : ℕ) :
    W.HasThirdFix K (i - (m : ℤ) * (n : ℤ)) ↔ W.HasThirdFix K i := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : W.HasThirdFix K (i - ((m + 1 : ℕ) : ℤ) * (n : ℤ)) ↔
          W.HasThirdFix K (i - (m : ℤ) * (n : ℤ)) := by
        have h := W.hasThirdFix_add_iff hn hM hW hKW
          (i - ((m + 1 : ℕ) : ℤ) * (n : ℤ))
        rwa [show i - ((m + 1 : ℕ) : ℤ) * (n : ℤ) + (n : ℤ) =
          i - (m : ℤ) * (n : ℤ) by push_cast; ring] at h
      exact hstep.trans ih

private theorem ClosedGoodPath.hasThirdFix_add_int [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (W : ClosedGoodPath H Γ) {K : Subgroup H} (hKW : K ≤ W.stab)
    (i k : ℤ) :
    W.HasThirdFix K (i + k * (n : ℤ)) ↔ W.HasThirdFix K i := by
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m : ℤ) :=
      ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
    subst hm
    simpa using W.hasThirdFix_add_nat hn hM hW hKW i m
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, -k = (m : ℤ) :=
      ⟨(-k).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hkm : k = -(m : ℤ) := by omega
    rw [hkm, show i + -(m : ℤ) * (n : ℤ) = i - (m : ℤ) * (n : ℤ) by ring]
    exact W.hasThirdFix_sub_nat hn hM hW hKW i m

private theorem ClosedGoodPath.hasThirdFix_reflect_core [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (W : ClosedGoodPath H Γ) {K : Subgroup H} (hKW : K ≤ W.stab) {i j : ℤ}
    (hij : i - (n : ℤ) < j) (hji : j < i)
    (hi : W.HasThirdFix K i) (hj : W.HasThirdFix K j) :
    W.HasThirdFix K (2 * i - j - (n : ℤ)) := by
  classical
  obtain ⟨z, hzadj, hzleft, hzright, hzfix⟩ := hi
  let p : GPath Γ n := W.window i n
  have hp : p.NoBack := W.window_noBack i n
  have hp0 : p 0 = W.x i := by
    show W.window i n 0 = W.x i
    rw [ClosedGoodPath.window_apply W i (Nat.zero_le n)]
    simp
  have hprevn : p.rev n = W.x i := by
    rw [GPath.rev_apply _ le_rfl, Nat.sub_self, hp0]
  have hprev1 : p.rev (n - 1) = W.x (i + 1) := by
    rw [GPath.rev_apply _ (by omega : n - 1 ≤ n), show n - (n - 1) = 1 by omega,
      ClosedGoodPath.window_apply W i (by omega : 1 ≤ n)]
    norm_num
  have hy : Γ.Adj (p.rev n) (W.x (i - 1)) := by
    rw [hprevn]
    have h := W.adj (i - 1)
    rw [show i - 1 + 1 = i by ring] at h
    exact h.symm
  have hy' : Γ.Adj (p.rev n) z := by rw [hprevn]; exact hzadj
  have hne : W.x (i - 1) ≠ p.rev (n - 1) := by
    rw [hprev1]
    have h := W.ne_add_two (i - 1)
    rwa [show i - 1 + 2 = i + 1 by ring] at h
  have hne' : z ≠ p.rev (n - 1) := by rw [hprev1]; exact hzright
  obtain ⟨u, hu_smul, -⟩ :=
    pathRootGroup_regular_of_weissFree hn hM hW hp.rev hy hy' hne hne'
  have hu_mem_rev : (u : H) ∈ pathRootGroup H Γ p.rev := u.2
  have hu_mem : (u : H) ∈ pathRootGroup H Γ p := by
    rw [← pathRootGroup_rev_eq p]
    exact hu_mem_rev
  have hu_p0 : (u : H) • W.x i = W.x i := by
    have h := smul_path_eq_self_of_mem_pathRootGroup hn hu_mem 0 (Nat.zero_le n)
    rwa [hp0] at h
  have hKrev : K ≤ GPath.stabPath (H := H) p.rev := by
    rw [GPath.stabPath_rev]
    exact le_trans hKW (ClosedGoodPath.stab_le_stabPath_window W i n)
  have hKb' : ∀ g ∈ K, g • W.x (i - 1) = W.x (i - 1) :=
    fun g hgK => ClosedGoodPath.mem_stab_iff.mp (hKW hgK) _
  have hcore := forall_smul_smul_eq_iff_commute hn hW hp.rev hKrev
    (b := W.x (i - 1)) hy hne hKb' (u := (u : H)) hu_mem_rev
  have hcomm : ∀ g ∈ K, g * (u : H) = (u : H) * g := by
    refine hcore.mp ?_
    intro g hgK
    simpa [mul_smul, hu_smul] using hzfix g hgK
  have ha_int : ((i - j).toNat : ℤ) = i - j :=
    Int.toNat_of_nonneg (by omega)
  let a : ℕ := (i - j).toNat
  have ha_cast : (a : ℤ) = i - j := ha_int
  have ha_pos : 0 < a := by omega
  have ha_lt_n : a < n := by omega
  have han : a ≤ n := by omega
  have hcast : ((n - a : ℕ) : ℤ) = (n : ℤ) - (a : ℤ) := Nat.cast_sub han
  let P1 : GPath Γ a := (u : H) • W.window j a
  let P2 : GPath Γ (n - a) := (W.window (2 * i - j - (n : ℤ)) (n - a)).rev
  have hP1a : P1 a = W.x i := by
    change ((u : H) • W.window j a) a = W.x i
    rw [GPath.smul_apply, ClosedGoodPath.window_apply W j (le_refl a)]
    rw [show j + (a : ℤ) = i by omega, hu_p0]
  have hP2_0 : P2 0 = W.x i := by
    change (W.window (2 * i - j - (n : ℤ)) (n - a)).rev 0 = W.x i
    rw [GPath.rev_apply _ (Nat.zero_le (n - a)), Nat.sub_zero,
      ClosedGoodPath.window_apply W (2 * i - j - (n : ℤ)) (le_refl (n - a))]
    congr 1
    omega
  let qfull : GPath Γ (a + (n - a)) :=
    GPath.append P1 P2 (hP1a.trans hP2_0.symm)
  let q : GPath Γ n := GPath.castLength (by omega : a + (n - a) = n) qfull
  have hqfull : qfull = GPath.append P1 P2 (hP1a.trans hP2_0.symm) := rfl
  have hq0 : q 0 = (u : H) • W.x j := by
    rw [show q 0 = qfull 0 from rfl, hqfull,
      GPath.append_apply_left P1 P2 _ (by omega : 0 ≤ a)]
    change ((u : H) • W.window j a) 0 = (u : H) • W.x j
    rw [GPath.smul_apply, ClosedGoodPath.window_apply W j (Nat.zero_le a)]
    simp
  have hq1 : q 1 = (u : H) • W.x (j + 1) := by
    rw [show q 1 = qfull 1 from rfl, hqfull,
      GPath.append_apply_left P1 P2 _ (by omega : 1 ≤ a)]
    change ((u : H) • W.window j a) 1 = (u : H) • W.x (j + 1)
    rw [GPath.smul_apply, ClosedGoodPath.window_apply W j (by omega : 1 ≤ a)]
    norm_num
  have hqn : q n = W.x (2 * i - j - (n : ℤ)) := by
    rw [show q n = qfull n from rfl, hqfull,
      GPath.append_apply_right P1 P2 _ (by omega : a ≤ n)]
    change (W.window (2 * i - j - (n : ℤ)) (n - a)).rev (n - a) =
      W.x (2 * i - j - (n : ℤ))
    rw [GPath.rev_apply _ le_rfl, Nat.sub_self,
      ClosedGoodPath.window_apply W (2 * i - j - (n : ℤ)) (Nat.zero_le (n - a))]
    simp
  have hqn1 : q (n - 1) = W.x (2 * i - j - (n : ℤ) + 1) := by
    rw [show q (n - 1) = qfull (n - 1) from rfl, hqfull,
      GPath.append_apply_right P1 P2 _ (by omega : a ≤ n - 1)]
    change (W.window (2 * i - j - (n : ℤ)) (n - a)).rev ((n - 1) - a) =
      W.x (2 * i - j - (n : ℤ) + 1)
    rw [GPath.rev_apply _ (by omega : (n - 1) - a ≤ n - a),
      show n - a - ((n - 1) - a) = 1 by omega,
      ClosedGoodPath.window_apply W (2 * i - j - (n : ℤ)) (by omega : 1 ≤ n - a)]
    norm_num
  have hP1nb : P1.NoBack := by
    change ((u : H) • W.window j a).NoBack
    exact GPath.smul_noBack (W.window_noBack j a)
  have hP2nb : P2.NoBack := by
    change (W.window (2 * i - j - (n : ℤ)) (n - a)).rev.NoBack
    exact (W.window_noBack (2 * i - j - (n : ℤ)) (n - a)).rev
  have hcross : P1 (a - 1) ≠ P2 1 := by
    have h1 : P1 (a - 1) = z := by
      change ((u : H) • W.window j a) (a - 1) = z
      rw [GPath.smul_apply, ClosedGoodPath.window_apply W j (by omega : a - 1 ≤ a)]
      rw [show j + ((a - 1 : ℕ) : ℤ) = i - 1 by omega, hu_smul]
    have h2 : P2 1 = W.x (i - 1) := by
      change (W.window (2 * i - j - (n : ℤ)) (n - a)).rev 1 = W.x (i - 1)
      rw [GPath.rev_apply _ (by omega : 1 ≤ n - a),
        ClosedGoodPath.window_apply W (2 * i - j - (n : ℤ)) (by omega : n - a - 1 ≤ n - a)]
      congr 1
      omega
    rw [h1, h2]
    exact hzleft
  have hqnb : q.NoBack := by
    have h0 : qfull.NoBack := GPath.noBack_append P1 P2 _ hP1nb hP2nb
      ha_pos (by omega : 0 < n - a) hcross
    exact GPath.castLength_noBack _ h0
  have hKq : K ≤ GPath.stabPath (H := H) q := by
    intro g hgK
    rw [GPath.mem_stabPath_iff]
    intro t ht
    rw [show q t = qfull t from rfl, hqfull]
    by_cases hta : t ≤ a
    · rw [GPath.append_apply_left P1 P2 _ hta]
      change g • (((u : H) • W.window j a) t) = ((u : H) • W.window j a) t
      rw [GPath.smul_apply, ClosedGoodPath.window_apply W j hta]
      rw [show g • ((u : H) • W.x (j + (t : ℤ))) =
        (u : H) • (g • W.x (j + (t : ℤ))) by
        rw [← mul_smul, hcomm g hgK, mul_smul]]
      rw [ClosedGoodPath.mem_stab_iff.mp (hKW hgK)]
    · have hat : a ≤ t := by omega
      rw [GPath.append_apply_right P1 P2 _ hat]
      change g • ((W.window (2 * i - j - (n : ℤ)) (n - a)).rev (t - a)) =
        (W.window (2 * i - j - (n : ℤ)) (n - a)).rev (t - a)
      rw [GPath.rev_apply _ (by omega : t - a ≤ n - a),
        ClosedGoodPath.window_apply W (2 * i - j - (n : ℤ))
          (by omega : (n - a) - (t - a) ≤ n - a)]
      rw [ClosedGoodPath.mem_stab_iff.mp (hKW hgK)]
  have hnear : ∃ w, Γ.Adj (q 0) w ∧ w ≠ q 1 ∧
      w ≠ (u : H) • W.x (j - 1) ∧ ∀ g ∈ K, g • w = w := by
    obtain ⟨zj, hzjadj, hzjleft, hzjright, hzjfix⟩ := hj
    refine ⟨(u : H) • zj, ?_, ?_, ?_, ?_⟩
    · rw [hq0]
      exact (GraphAction.adj_smul (u : H) (W.x j) zj).mpr hzjadj
    · rw [hq1]
      intro heq
      apply hzjright
      have h := congrArg (fun v => (u : H)⁻¹ • v) heq
      simpa using h
    · intro heq
      apply hzjleft
      have h := congrArg (fun v => (u : H)⁻¹ • v) heq
      simpa using h
    · intro g hgK
      rw [← mul_smul, hcomm g hgK, mul_smul, hzjfix g hgK]
  have hb : Γ.Adj (q n) (W.x (2 * i - j - (n : ℤ) - 1)) := by
    rw [hqn]
    have h := W.adj (2 * i - j - (n : ℤ) - 1)
    rw [show 2 * i - j - (n : ℤ) - 1 + 1 = 2 * i - j - (n : ℤ) by ring] at h
    exact h.symm
  have hb1 : W.x (2 * i - j - (n : ℤ) - 1) ≠ q (n - 1) := by
    rw [hqn1]
    have h := W.ne_add_two (2 * i - j - (n : ℤ) - 1)
    rwa [show 2 * i - j - (n : ℤ) - 1 + 2 = 2 * i - j - (n : ℤ) + 1 by ring] at h
  have hKa : ∀ g ∈ K, g • ((u : H) • W.x (j - 1)) = (u : H) • W.x (j - 1) := by
    intro g hgK
    rw [← mul_smul, hcomm g hgK, mul_smul,
      ClosedGoodPath.mem_stab_iff.mp (hKW hgK)]
  have hKb : ∀ g ∈ K, g • W.x (2 * i - j - (n : ℤ) - 1) =
      W.x (2 * i - j - (n : ℤ) - 1) :=
    fun g hgK => ClosedGoodPath.mem_stab_iff.mp (hKW hgK) _
  have hnearA : Γ.Adj (q 0) ((u : H) • W.x (j - 1)) := by
    rw [hq0]
    exact (GraphAction.adj_smul (Γ := Γ) (u : H) (W.x j) (W.x (j - 1))).mpr (by
      have h := W.adj (j - 1)
      rw [show j - 1 + 1 = j by ring] at h
      exact h.symm)
  have hnearA1 : ((u : H) • W.x (j - 1)) ≠ q 1 := by
    rw [hq1]
    intro heq
    have h := congrArg (fun v => (u : H)⁻¹ • v) heq
    have h' : W.x (j - 1) = W.x (j + 1) := by simpa using h
    have hne := W.ne_add_two (j - 1)
    rw [show j - 1 + 2 = j + 1 by ring] at hne
    exact hne h'
  have hmain := exists_fix_iff_of_noBack hn hM hW hqnb hKq hnearA hnearA1 hb hb1 hKa hKb
  obtain ⟨w, hwadj, hw1, hw2, hwfix⟩ := hmain.mp hnear
  refine ⟨w, ?_, ?_, ?_, hwfix⟩
  · rwa [hqn] at hwadj
  · exact hw2
  · rwa [hqn1] at hw1

theorem ClosedGoodPath.hasThirdFix_reflect [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (W : ClosedGoodPath H Γ) {K : Subgroup H} (hKW : K ≤ W.stab) {i j : ℤ}
    (hi : W.HasThirdFix K i) (hj : W.HasThirdFix K j) : W.HasThirdFix K (2 * i - j) := by
  classical
  have hnpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast (by omega : 0 < n)
  set r : ℤ := (j - i) % (n : ℤ) with hrdef
  set q : ℤ := (j - i) / (n : ℤ) with hqdef
  have hdecomp : (n : ℤ) * q + r = j - i := Int.mul_ediv_add_emod (j - i) (n : ℤ)
  have hr_nonneg : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hnpos)
  have hr_lt : r < (n : ℤ) := Int.emod_lt_of_pos _ hnpos
  by_cases hr0 : r = 0
  · have htarget : 2 * i - j = i + (-q) * (n : ℤ) := by
      have hji : j = i + q * (n : ℤ) := by linarith
      rw [hji]
      ring
    rw [htarget]
    exact (W.hasThirdFix_add_int hn hM hW hKW i (-q)).mpr hi
  · have hrpos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
    set a : ℤ := q + 1 with hadef
    set i' : ℤ := i + a * (n : ℤ) with hi'def
    have hoffset : i' - j = (n : ℤ) - r := by
      rw [hi'def, hadef, hqdef]
      linarith
    have hgt : j < i' := by linarith
    have hlt : i' - (n : ℤ) < j := by linarith
    have hi' : W.HasThirdFix K i' :=
      (W.hasThirdFix_add_int hn hM hW hKW i a).mpr hi
    have hcore := W.hasThirdFix_reflect_core hn hM hW hKW hlt hgt hi' hj
    have hfin : W.HasThirdFix K (2 * i' - j) := by
      have h := (W.hasThirdFix_add_iff hn hM hW hKW (2 * i' - j - (n : ℤ))).mp hcore
      rwa [show 2 * i' - j - (n : ℤ) + (n : ℤ) = 2 * i' - j by ring] at h
    have hrel : 2 * i' - j = (2 * i - j) + (2 * a) * (n : ℤ) := by
      rw [hi'def]
      ring
    rw [hrel] at hfin
    exact (W.hasThirdFix_add_int hn hM hW hKW (2 * i - j) (2 * a)).mp hfin

private theorem ClosedGoodPath.hasThirdFix_neg [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (W : ClosedGoodPath H Γ) {K : Subgroup H} (hKW : K ≤ W.stab)
    (h0 : W.HasThirdFix K 0) {t : ℤ} (ht : W.HasThirdFix K t) :
    W.HasThirdFix K (-t) := by
  have h := W.hasThirdFix_reflect hn hM hW hKW h0 ht
  simpa using h

private theorem ClosedGoodPath.hasThirdFix_sub_two_mul [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (W : ClosedGoodPath H Γ) {K : Subgroup H} (hKW : K ≤ W.stab)
    (h0 : W.HasThirdFix K 0) {t h : ℤ} (ht : W.HasThirdFix K t)
    (hh : W.HasThirdFix K h) : W.HasThirdFix K (t - 2 * h) := by
  have hnt := W.hasThirdFix_neg hn hM hW hKW h0 ht
  have hnh := W.hasThirdFix_neg hn hM hW hKW h0 hh
  have hres := W.hasThirdFix_reflect hn hM hW hKW (i := -h) (j := -t) hnh hnt
  rw [show 2 * (-h) - (-t) = t - 2 * h by ring] at hres
  exact hres

private theorem ClosedGoodPath.hasThirdFix_mul_nat [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (W : ClosedGoodPath H Γ) {K : Subgroup H} (hKW : K ≤ W.stab)
    (h0 : W.HasThirdFix K 0) {d : ℕ} (hd : W.HasThirdFix K (d : ℤ)) (m : ℕ) :
    W.HasThirdFix K ((m : ℤ) * (d : ℤ)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      rcases Nat.lt_or_ge m 2 with hm | hm
      · interval_cases m
        · simpa using h0
        · simpa using hd
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
        have hk : W.HasThirdFix K ((k : ℤ) * (d : ℤ)) := ih k (by omega)
        have hk1 : W.HasThirdFix K (((k + 1 : ℕ) : ℤ) * (d : ℤ)) :=
          ih (k + 1) (by omega)
        have hres := W.hasThirdFix_reflect hn hM hW hKW
          (i := ((k + 1 : ℕ) : ℤ) * (d : ℤ)) (j := (k : ℤ) * (d : ℤ)) hk1 hk
        have h' : W.HasThirdFix K (((k + 2 : ℕ) : ℤ) * (d : ℤ)) := by
          convert hres using 2
          push_cast
          ring
        exact h'

private theorem ClosedGoodPath.hasThirdFix_mul_int [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (W : ClosedGoodPath H Γ) {K : Subgroup H} (hKW : K ≤ W.stab)
    (h0 : W.HasThirdFix K 0) {d : ℕ} (hd : W.HasThirdFix K (d : ℤ)) (k : ℤ) :
    W.HasThirdFix K (k * (d : ℤ)) := by
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m : ℤ) :=
      ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
    subst hm
    simpa using W.hasThirdFix_mul_nat hn hM hW hKW h0 hd m
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, -k = (m : ℤ) :=
      ⟨(-k).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hkm : k = -(m : ℤ) := by omega
    have hmul := W.hasThirdFix_mul_nat hn hM hW hKW h0 hd m
    have hneg := W.hasThirdFix_neg hn hM hW hKW h0 hmul
    rwa [hkm, show -(m : ℤ) * (d : ℤ) = -((m : ℤ) * (d : ℤ)) by ring]

theorem ClosedGoodPath.exists_hasThirdFix_iff_dvd [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (W : ClosedGoodPath H Γ) {K : Subgroup H} (hKW : K ≤ W.stab)
    (hK0 : K ≤ fixingSubgroup H (Γ.neighborSet (W.x 0))) :
    ∃ d : ℕ, 0 < d ∧ d ∣ n ∧ ∀ i : ℤ, W.HasThirdFix K i ↔ (d : ℤ) ∣ i := by
  classical
  have h0 : W.HasThirdFix K 0 := by
    obtain ⟨z, hzadj, hz1, hz2⟩ := h3 (W.x 0) (W.x (-1)) (W.x 1)
      (by
        have h := W.adj (-1)
        rw [show (-1 : ℤ) + 1 = 0 by ring] at h
        exact h.symm)
      (W.adj 0)
    exact ⟨z, hzadj, hz1, hz2,
      fun g hgK => (mem_fixingSubgroup_iff H).mp (hK0 hgK) z hzadj⟩
  have hnmem : W.HasThirdFix K ((n : ℤ)) := by
    have h := (W.hasThirdFix_add_iff hn hM hW hKW 0).mp h0
    simpa using h
  have h_exists : ∃ m : ℕ, 0 < m ∧ W.HasThirdFix K ((m : ℤ)) :=
    ⟨n, by omega, hnmem⟩
  set d : ℕ := Nat.find h_exists with hddef
  have hd_spec : 0 < d ∧ W.HasThirdFix K ((d : ℤ)) := by
    rw [hddef]
    exact Nat.find_spec h_exists
  have hd_pos : 0 < d := hd_spec.1
  have hd_mem : W.HasThirdFix K ((d : ℤ)) := hd_spec.2
  have hd_min : ∀ m : ℕ, m < d → ¬ (0 < m ∧ W.HasThirdFix K ((m : ℤ))) := by
    intro m hm
    exact Nat.find_min h_exists (by rwa [hddef] at hm)
  have hforward : ∀ i : ℤ, W.HasThirdFix K i → (d : ℤ) ∣ i := by
    intro i hiS
    set D : ℤ := 2 * (d : ℤ) with hDdef
    have hDpos : 0 < D := by rw [hDdef]; omega
    set q : ℤ := i / D with hqdef
    set r : ℤ := i % D with hrdef
    have hdecomp : D * q + r = i := Int.mul_ediv_add_emod i D
    have hr_nonneg : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hDpos)
    have hr_lt : r < D := Int.emod_lt_of_pos _ hDpos
    have hq_mem : W.HasThirdFix K ((d : ℤ) * q) := by
      rw [mul_comm]
      exact W.hasThirdFix_mul_int hn hM hW hKW h0 hd_mem q
    have hr_mem : W.HasThirdFix K r := by
      have hsub := W.hasThirdFix_sub_two_mul hn hM hW hKW h0 hiS hq_mem
      have hDq : 2 * ((d : ℤ) * q) = D * q := by rw [hDdef]; ring
      have hr_eq : i - 2 * ((d : ℤ) * q) = r := by rw [hDq]; linarith
      rwa [hr_eq] at hsub
    rcases lt_trichotomy r 0 with hrneg | hrzer | hrpos
    · exact absurd hr_nonneg (not_le.mpr hrneg)
    · refine ⟨2 * q, ?_⟩
      rw [← hdecomp, hrzer, hDdef]
      ring
    · rcases lt_trichotomy r (d : ℤ) with hrlt | hreq | hrgt
      · exfalso
        have hr_cast : (((r.toNat : ℕ) : ℤ)) = r := Int.toNat_of_nonneg (le_of_lt hrpos)
        have hm_pos : 0 < r.toNat := by
          have h : (0 : ℤ) < ((r.toNat : ℕ) : ℤ) := by rw [hr_cast]; exact hrpos
          exact_mod_cast h
        have hm_lt : r.toNat < d := by
          have h : ((r.toNat : ℕ) : ℤ) < (d : ℤ) := by rw [hr_cast]; exact hrlt
          exact_mod_cast h
        exact (hd_min r.toNat hm_lt) ⟨hm_pos, by rw [hr_cast]; exact hr_mem⟩
      · refine ⟨2 * q + 1, ?_⟩
        rw [← hdecomp, hreq, hDdef]
        ring
      · exfalso
        have hr'_mem : W.HasThirdFix K (D - r) := by
          have h := W.hasThirdFix_reflect hn hM hW hKW (i := (d : ℤ)) (j := r) hd_mem hr_mem
          rwa [show 2 * (d : ℤ) - r = D - r by rw [hDdef]] at h
        have hr'_pos : 0 < D - r := by linarith
        have hr'_lt : D - r < (d : ℤ) := by linarith
        have hr'_cast : ((((D - r).toNat : ℕ) : ℤ)) = D - r :=
          Int.toNat_of_nonneg (le_of_lt hr'_pos)
        have hm_pos : 0 < (D - r).toNat := by
          have h : (0 : ℤ) < ((((D - r).toNat : ℕ) : ℤ)) := by rw [hr'_cast]; exact hr'_pos
          exact_mod_cast h
        have hm_lt : (D - r).toNat < d := by
          have h : ((((D - r).toNat : ℕ) : ℤ)) < (d : ℤ) := by rw [hr'_cast]; exact hr'_lt
          exact_mod_cast h
        exact (hd_min (D - r).toNat hm_lt) ⟨hm_pos, by rw [hr'_cast]; exact hr'_mem⟩
  have hback : ∀ i : ℤ, (d : ℤ) ∣ i → W.HasThirdFix K i := by
    intro i hdiv
    obtain ⟨k, rfl⟩ := hdiv
    rw [mul_comm]
    exact W.hasThirdFix_mul_int hn hM hW hKW h0 hd_mem k
  have hdvd : d ∣ n := Int.ofNat_dvd.mp (hforward (n : ℤ) hnmem)
  exact ⟨d, hd_pos, hdvd, fun i => ⟨hforward i, hback i⟩⟩

theorem ClosedGoodPath.kernelAt_eq_of_le [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w) (hL : ∀ z, LocalFacts H Γ z)
    (hloc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v)
    (W : ClosedGoodPath H Γ) (k : ℤ)
    (h : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (W.x (2 * k)))) :
    W.kernelAt (2 * k) = W.kernelAt 0 := by
  obtain ⟨c, hc⟩ := W.exists_smul_x_two_mul_int hloc k
  obtain ⟨g, hg⟩ := ClosedGoodPath.exists_smul_eq hn hM hW hne hL hloc W (W.shift (2 * k))
    ⟨c, by simpa using hc⟩
  have hker : (W.shift (2 * k)).kernelAt 0 =
      (W.kernelAt 0).map (MulAut.conj g).toMonoidHom :=
    ClosedGoodPath.kernelAt_eq_map_conj W (W.shift (2 * k)) hg 0
  have hshift : (W.shift (2 * k)).kernelAt 0 = W.kernelAt (2 * k) :=
    W.kernelAt_shift (2 * k)
  have hcard : Nat.card ↥(W.kernelAt (2 * k)) ≤ Nat.card ↥(W.kernelAt 0) := by
    rw [← hshift, hker,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hle : W.kernelAt 0 ≤ W.kernelAt (2 * k) := by
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨h hx, hx.2⟩
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem ClosedGoodPath.kernelAt_eq_bot_of_le_succ {n : ℕ} (hW : WeissFree H Γ n)
    (W : ClosedGoodPath H Γ) (k : ℤ)
    (h1 : W.kernelAt k ≤ fixingSubgroup H (Γ.neighborSet (W.x (k + 1)))) :
    W.kernelAt k = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hg0 : g ∈ fixingSubgroup H (Γ.neighborSet (W.x k)) := hg.1
  have hgall : ∀ i : ℤ, g • W.x i = W.x i :=
    ClosedGoodPath.mem_stab_iff.mp hg.2
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    let p : GPath Γ 0 := W.window k 0
    have hp : p.NoBack := W.window_noBack k 0
    have hp0 : p 0 = W.x k := by
      show W.window k 0 0 = W.x k
      rw [ClosedGoodPath.window_apply W k (Nat.zero_le 0)]
      simp
    have hp1 : p 1 = W.x k := by
      show W.window k 0 1 = W.x k
      simp [ClosedGoodPath.window]
    refine Subgroup.mem_bot.mpr (hW p hp g ?_ ?_ ?_)
    · intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      rw [hp0]
      exact hgall k
    · intro w hw
      rw [hp0] at hw
      exact (mem_fixingSubgroup_iff H).mp hg0 w hw
    · intro w hw
      rw [hp1] at hw
      exact (mem_fixingSubgroup_iff H).mp hg0 w hw
  · let p : GPath Γ n := W.window k n
    have hp : p.NoBack := W.window_noBack k n
    have hp0 : p 0 = W.x k := by
      show W.window k n 0 = W.x k
      rw [ClosedGoodPath.window_apply W k (Nat.zero_le n)]
      simp
    have hp1 : p 1 = W.x (k + 1) := by
      show W.window k n 1 = W.x (k + 1)
      rw [ClosedGoodPath.window_apply W k (by omega : 1 ≤ n)]
      norm_num
    refine Subgroup.mem_bot.mpr (hW p hp g ?_ ?_ ?_)
    · intro i hi
      rw [ClosedGoodPath.window_apply W k hi]
      exact hgall (k + (i : ℤ))
    · intro w hw
      rw [hp0] at hw
      exact (mem_fixingSubgroup_iff H).mp hg0 w hw
    · intro w hw
      rw [hp1] at hw
      exact (mem_fixingSubgroup_iff H).mp (h1 hg) w hw

end CFSG.Quasithin.Stroth.WeissDelta

end
