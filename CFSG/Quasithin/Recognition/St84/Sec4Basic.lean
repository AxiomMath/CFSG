module

public import CFSG.Quasithin.Recognition.St84.Sec4Setup
public import CFSG.Quasithin.Recognition.St84.Gen.Sec6LeafGen

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)
variable {r : ℕ}

theorem mem_fixSet_iff_le_Gi (U : Subgroup G) (j : ℤ) :
    j ∈ X.fixSet U ↔ U ≤ X.Gi j := by
  constructor
  · intro h g hg
    exact MulAction.mem_stabilizer_iff.mpr (h g hg)
  · intro h g hg
    exact MulAction.mem_stabilizer_iff.mp (h hg)

theorem arcStab_eq_K_sup_pCoreOf {m r' : ℤ} (hmr : m < r') :
    X.arcStab m r' = X.K ⊔ pCoreOf 2 (X.arcStab m r') := by
  have hK : X.K ≤ X.arcStab m r' := X.K_le_GT.trans (X.GT_le_arcStab m r')
  have hA : X.arcStab m r' ≤ X.Gi (r' - 1) ⊓ X.Gi ((r' - 1) + 1) := by
    rw [show r' - 1 + 1 = r' by ring]
    exact le_inf (X.arcStab_le_Gi_right_pred hmr) (X.arcStab_le_Gi_right hmr)
  exact ((X.pCoreOf_eq_inf_edgeSylow (r' - 1) hK hA).2).symm

private theorem adj_vert_iff {i j : ℤ} :
    Γ.Adj (X.vert i) (X.vert j) ↔ j = i + 1 ∨ i = j + 1 := by
  constructor
  · intro h
    have hd : Γ.dist (X.vert i) (X.vert j) = 1 := dist_eq_one_iff_adj.mpr h
    rcases le_total i j with hij | hji
    · left
      have hdi := Line.dist_eq X.hyp.isTree X.line hij
      rw [hd] at hdi
      have h1 : ((j - i).toNat : ℤ) = 1 := by exact_mod_cast hdi.symm
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)] at h1
      omega
    · right
      have hdi := Line.dist_eq X.hyp.isTree X.line hji
      rw [dist_comm, hd] at hdi
      have h1 : ((i - j).toNat : ℤ) = 1 := by exact_mod_cast hdi.symm
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hji)] at h1
      omega
  · rintro (rfl | rfl)
    · exact X.adj i
    · exact (X.adj j).symm

private theorem int_step_const {σ : ℤ → ℤ} (hinj : Function.Injective σ)
    (hstep : ∀ i : ℤ, σ (i + 1) = σ i + 1 ∨ σ (i + 1) = σ i - 1) :
    ∀ i : ℤ, σ (i + 1) - σ i = σ 1 - σ 0 := by
  have hsame : ∀ i : ℤ, σ (i + 2) - σ (i + 1) = σ (i + 1) - σ i := by
    intro i
    have h1 := hstep i
    have h2 : σ (i + 2) = σ (i + 1) + 1 ∨ σ (i + 2) = σ (i + 1) - 1 := by
      simpa [show i + 1 + 1 = i + 2 by ring] using hstep (i + 1)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · omega
    · exfalso
      have hz : σ (i + 2) = σ i := by omega
      exact absurd (hinj hz) (by omega)
    · exfalso
      have hz : σ (i + 2) = σ i := by omega
      exact absurd (hinj hz) (by omega)
    · omega
  have hpos_nat : ∀ n : ℕ, σ ((n : ℤ) + 1) - σ (n : ℤ) = σ 1 - σ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have h := hsame (n : ℤ)
        rw [show ((n + 1 : ℕ) : ℤ) + 1 = (n : ℤ) + 2 by push_cast; ring,
          show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, h]
        exact ih
  have hneg_nat : ∀ n : ℕ, σ (-(n : ℤ) + 1) - σ (-(n : ℤ)) = σ 1 - σ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have h := hsame (-(n : ℤ) - 1)
        rw [show -(n : ℤ) - 1 + 2 = -(n : ℤ) + 1 by ring,
          show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring] at h
        rw [show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by push_cast; ring,
          show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 by push_cast; ring]
        rw [← h]
        exact ih
  intro i
  rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
  · exact hpos_nat n
  · exact hneg_nat n

private theorem int_path_aut {σ : ℤ → ℤ} (hinj : Function.Injective σ)
    (hstep : ∀ i : ℤ, σ (i + 1) = σ i + 1 ∨ σ (i + 1) = σ i - 1) :
    (∀ k : ℤ, σ k = σ 0 + k) ∨ (∀ k : ℤ, σ k = σ 0 - k) := by
  have hconst := int_step_const hinj hstep
  rcases hstep 0 with h0 | h0
  · left
    have h0' : σ 1 = σ 0 + 1 := by simpa using h0
    have hd : ∀ i : ℤ, σ (i + 1) - σ i = 1 := by
      intro i
      have h := hconst i
      rw [h0'] at h
      omega
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
        have h := hd (n : ℤ)
        push_cast at h ⊢
        omega
    | pred n ih =>
        have h := hd (-(n : ℤ) - 1)
        have h' : σ (-(n : ℤ)) - σ (-(n : ℤ) - 1) = 1 := by simpa using h
        omega
  · right
    have h0' : σ 1 = σ 0 - 1 := by simpa using h0
    have hd : ∀ i : ℤ, σ (i + 1) - σ i = -1 := by
      intro i
      have h := hconst i
      rw [h0'] at h
      omega
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
        have h := hd (n : ℤ)
        push_cast at h ⊢
        omega
    | pred n ih =>
        have h := hd (-(n : ℤ) - 1)
        have h' : σ (-(n : ℤ)) - σ (-(n : ℤ) - 1) = -1 := by simpa using h
        omega

theorem GT_eq_K_of_odd (H : X.Sec4Hyp s r) : X.GT = X.K := by
  have hQT : X.QT = ⊥ := by
    have hbot := inf_eq_bot_of_odd_of_isPGroup (A := X.GT) (B := X.QT) H.odd_GT
      (pCoreOf_isPGroup' X.GT)
    rw [show X.GT ⊓ X.QT = X.QT from inf_eq_right.mpr X.QT_le_GT] at hbot
    exact hbot
  rw [(X.GT_eq_K_sup_QT).1, hQT, sup_bot_eq]

private theorem normalizer_K_action (H : X.Sec4Hyp s r) {x : G}
    (hx : x ∈ Subgroup.normalizer (X.K : Set G)) :
    ∃ (c : ℤ) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ Even c ∧
      ∀ k : ℤ, x • X.vert k = X.vert (ε * k + c) := by
  have h0 : 2 ≤ X.n 0 := H.two_le_n 0
  have h1 : 2 ≤ X.n 1 := H.two_le_n 1
  have hfix : ∀ i : ℤ, (∀ k ∈ X.K, k • (x • X.vert i) = x • X.vert i) := by
    intro i k hk
    have hkx : x⁻¹ * k * x ∈ X.K := (Subgroup.mem_normalizer_iff''.mp hx k).mp hk
    calc k • (x • X.vert i) = (k * x) • X.vert i := (mul_smul k x _).symm
      _ = (x * (x⁻¹ * k * x)) • X.vert i := by
          rw [show k * x = x * (x⁻¹ * k * x) by group]
      _ = x • ((x⁻¹ * k * x) • X.vert i) := mul_smul x _ _
      _ = x • X.vert i := by rw [X.K_fix _ hkx i]
  let σ : ℤ → ℤ := fun i =>
    Classical.choose (X.mem_range_of_fixed_K h0 h1 (x • X.vert i) (hfix i))
  have hσ : ∀ i : ℤ, X.vert (σ i) = x • X.vert i := by
    intro i
    exact Classical.choose_spec (X.mem_range_of_fixed_K h0 h1 (x • X.vert i) (hfix i))
  have hinj : Function.Injective σ := by
    intro i j hij
    have hsm : x • X.vert i = x • X.vert j := by rw [← hσ i, ← hσ j, hij]
    exact X.vert_injective (MulAction.injective x hsm)
  have hadjσ : ∀ i j : ℤ, (σ j = σ i + 1 ∨ σ i = σ j + 1) ↔ (j = i + 1 ∨ i = j + 1) := by
    intro i j
    have h1' : Γ.Adj (X.vert (σ i)) (X.vert (σ j)) ↔ Γ.Adj (X.vert i) (X.vert j) := by
      rw [hσ i, hσ j]
      exact X.hyp.adj_smul x (X.vert i) (X.vert j)
    rw [X.adj_vert_iff (i := σ i) (j := σ j), X.adj_vert_iff (i := i) (j := j)] at h1'
    exact h1'
  have heven : Even (σ 0) :=
    X.even_of_even_dist (σ 0)
      (by rw [hσ 0]; exact X.hyp.preservesParts x (X.vert 0))
  have hstep : ∀ i : ℤ, σ (i + 1) = σ i + 1 ∨ σ (i + 1) = σ i - 1 := by
    intro i
    have h := (hadjσ i (i + 1)).mpr (Or.inl rfl)
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  rcases int_path_aut hinj hstep with hlin | hlin
  · refine ⟨σ 0, 1, Or.inl rfl, heven, ?_⟩
    intro k
    rw [← hσ k, hlin k]
    congr 1
    ring
  · refine ⟨σ 0, -1, Or.inr rfl, heven, ?_⟩
    intro k
    rw [← hσ k, hlin k]
    congr 1
    ring

theorem reflection_of_not_mem (H : X.Sec4Hyp s r) {i : ℤ} {x : G}
    (hx : x ∈ X.Gi i ⊓ Subgroup.normalizer (X.K : Set G)) (hxK : x ∉ X.K) :
    ∀ m : ℤ, x • X.vert (i + m) = X.vert (i - m) := by
  obtain ⟨c, ε, hε, -, hact⟩ := X.normalizer_K_action H hx.2
  have hfixi : x • X.vert i = X.vert i := MulAction.mem_stabilizer_iff.mp hx.1
  have hci : ε * i + c = i := by
    have h := hact i
    rw [hfixi] at h
    have h' := X.vert_injective h
    omega
  rcases hε with hε1 | hεm
  · exfalso
    have hc0 : c = 0 := by rw [hε1] at hci; omega
    apply hxK
    rw [← X.GT_eq_K_of_odd H, Setup.GT, Fan86.mem_fixSet]
    intro v hv
    obtain ⟨k, rfl⟩ := hv
    have h := hact k
    rw [hε1, hc0] at h
    simpa using h
  · intro m
    rw [hεm] at hci
    have h := hact (i + m)
    rw [hεm] at h
    have hnum : -1 * (i + m) + c = i - m := by omega
    rwa [hnum] at h

theorem reflection_of_smul_succ (H : X.Sec4Hyp s r) {i : ℤ} {x : G}
    (hx : x ∈ X.Gi i ⊓ Subgroup.normalizer (X.K : Set G))
    (hmove : x • X.vert (i + 1) = X.vert (i - 1)) :
    ∀ m : ℤ, x • X.vert (i + m) = X.vert (i - m) := by
  refine X.reflection_of_not_mem H hx fun hxK => ?_
  have heq : X.vert (i - 1) = X.vert (i + 1) := by
    rw [← hmove, X.K_fix x hxK (i + 1)]
  exact (by omega : i - 1 ≠ i + 1) (X.vert_injective heq)

theorem exists_reflection (H : X.Sec4Hyp s r) (i : ℤ) :
    ∃ t ∈ X.Gi i ⊓ Subgroup.normalizer (X.K : Set G),
      ∀ m : ℤ, t • X.vert (i + m) = X.vert (i - m) := by
  have hadjL : Γ.Adj (X.vert i) (X.vert (i - 1)) := X.toTrack.adj_pred i
  obtain ⟨t, ht, htm⟩ := X.exists_normalizer_K_move (H := X.Gi i) i (X.K_le_Gi i) le_rfl
    (fun a b ha hb => X.hyp.locTrans ha hb) hadjL (X.adj i)
    (fun k hk => X.K_fix k hk (i - 1)) (fun k hk => X.K_fix k hk (i + 1))
  exact ⟨t, ht, X.reflection_of_smul_succ H ht htm⟩

theorem conjSub_arcStab_of_reflection {i a c : ℤ} {t : G}
    (href : ∀ m : ℤ, t • X.vert (i + m) = X.vert (i - m)) :
    conjSub t (X.arcStab a c) = X.arcStab (2 * i - c) (2 * i - a) := by
  unfold Setup.arcStab
  rw [conjSub_fixSet]
  congr 1
  ext v
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨w, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨2 * i - j, ?_, ?_⟩
    · rw [Set.mem_Icc] at hj ⊢
      omega
    · have h := href (j - i)
      rw [show i + (j - i) = j by ring,
        show i - (j - i) = 2 * i - j by ring] at h
      exact h.symm
  · rintro ⟨j, hj, rfl⟩
    refine ⟨X.vert (2 * i - j), ⟨2 * i - j, ?_, rfl⟩, ?_⟩
    · rw [Set.mem_Icc] at hj ⊢
      omega
    · have h := href (i - j)
      rwa [show i + (i - j) = 2 * i - j by ring,
        show i - (i - j) = j by ring] at h

theorem conjSub_edgeSylow_swap {g : G} {i j : ℤ}
    (h0 : g • X.vert i = X.vert (j + 1)) (h1 : g • X.vert (i + 1) = X.vert j) :
    conjSub g (X.edgeSylow i) = X.edgeSylow j := by
  have h0' : X.Gi (j + 1) = conjSub g (X.Gi i) := by
    unfold Setup.Gi
    rw [← h0, stabilizer_smul_eq_conjSub]
  have h1' : X.Gi j = conjSub g (X.Gi (i + 1)) := by
    unfold Setup.Gi
    rw [← h1, stabilizer_smul_eq_conjSub]
  calc conjSub g (X.edgeSylow i)
      = conjSub g (pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1))) := rfl
    _ = pCoreOf 2 (conjSub g (X.Gi i ⊓ X.Gi (i + 1))) := (pCoreOf_conjSub g _).symm
    _ = pCoreOf 2 (conjSub g (X.Gi i) ⊓ conjSub g (X.Gi (i + 1))) := by rw [conjSub_inf]
    _ = pCoreOf 2 (X.Gi (j + 1) ⊓ X.Gi j) := by rw [← h0', ← h1']
    _ = X.edgeSylow j := by rw [inf_comm]

theorem rightTransAt_iff (H : X.Sec4Hyp s r) {m r' : ℤ} (h : m < r') :
    X.RightTransAt m r' ↔
      ¬ pCoreOf 2 (X.arcStab m r') ≤ MulAction.stabilizer G (X.vert (r' + 1)) := by
  constructor
  · intro htr hle
    have hA : X.arcStab m r' = X.K ⊔ pCoreOf 2 (X.arcStab m r') :=
      X.arcStab_eq_K_sup_pCoreOf h
    have hfix : X.arcStab m r' ≤ MulAction.stabilizer G (X.vert (r' + 1)) := by
      rw [hA]
      exact sup_le (X.K_le_Gi (r' + 1)) hle
    have hne : X.vert (r' - 1) ≠ X.vert (r' + 1) := X.toTrack.ne_pred_succ r'
    have hpos : 0 < (Γ.neighborSet (X.vert r') \
        {X.vert (r' - 1), X.vert (r' + 1)}).ncard := by
      rw [ncard_neighborSet_diff_two X.hyp (α := X.vert r') (β := X.vert (r' - 1))
        (γ := X.vert (r' + 1)) (X.toTrack.adj_pred r') (X.adj r') hne]
      change 0 < 2 ^ X.n r' - 1
      have h2 : 4 ≤ 2 ^ X.n r' := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ X.n r' := Nat.pow_le_pow_right (by norm_num) (H.two_le_n r')
      omega
    obtain ⟨b, hb⟩ : ∃ b : V, b ∈ Γ.neighborSet (X.vert r') \
        {X.vert (r' - 1), X.vert (r' + 1)} :=
      Set.nonempty_of_ncard_ne_zero hpos.ne'
    rw [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
    obtain ⟨hbadj, hb1, hb2⟩ := hb
    rw [SimpleGraph.mem_neighborSet] at hbadj
    obtain ⟨g, hgA, hg⟩ := htr (X.vert (r' + 1)) b (X.adj r') hne.symm hbadj hb1
    have hgfix : g • X.vert (r' + 1) = X.vert (r' + 1) :=
      MulAction.mem_stabilizer_iff.mp (hfix hgA)
    exact hb2 (hg.symm.trans hgfix)
  · intro hnot
    by_contra hsing
    exact hnot ((X.pCoreOf_arcStab_le_Q_right m r' h hsing).trans
      ((X.Q_le_Gi_adj r').trans inf_le_right))

theorem leftTransAt_iff (H : X.Sec4Hyp s r) {m r' : ℤ} (h : m < r') :
    X.LeftTransAt m r' ↔
      ¬ pCoreOf 2 (X.arcStab m r') ≤ MulAction.stabilizer G (X.vert (m - 1)) := by
  constructor
  · intro htr hle
    have hA : X.arcStab m r' = X.K ⊔ pCoreOf 2 (X.arcStab m r') :=
      X.arcStab_eq_K_sup_pCoreOf h
    have hfix : X.arcStab m r' ≤ MulAction.stabilizer G (X.vert (m - 1)) := by
      rw [hA]
      exact sup_le (X.K_le_Gi (m - 1)) hle
    have hne : X.vert (m - 1) ≠ X.vert (m + 1) := X.toTrack.ne_pred_succ m
    have hpos : 0 < (Γ.neighborSet (X.vert m) \
        {X.vert (m - 1), X.vert (m + 1)}).ncard := by
      rw [ncard_neighborSet_diff_two X.hyp (α := X.vert m) (β := X.vert (m - 1))
        (γ := X.vert (m + 1)) (X.toTrack.adj_pred m) (X.adj m) hne]
      change 0 < 2 ^ X.n m - 1
      have h2 : 4 ≤ 2 ^ X.n m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ X.n m := Nat.pow_le_pow_right (by norm_num) (H.two_le_n m)
      omega
    obtain ⟨b, hb⟩ : ∃ b : V, b ∈ Γ.neighborSet (X.vert m) \
        {X.vert (m - 1), X.vert (m + 1)} :=
      Set.nonempty_of_ncard_ne_zero hpos.ne'
    rw [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
    obtain ⟨hbadj, hb1, hb2⟩ := hb
    rw [SimpleGraph.mem_neighborSet] at hbadj
    have hadjL : Γ.Adj (X.vert m) (X.vert (m - 1)) := X.toTrack.adj_pred m
    obtain ⟨g, hgA, hg⟩ := htr (X.vert (m - 1)) b hadjL hne hbadj hb2
    have hgfix : g • X.vert (m - 1) = X.vert (m - 1) :=
      MulAction.mem_stabilizer_iff.mp (hfix hgA)
    exact hb1 (hg.symm.trans hgfix)
  · intro hnot
    by_contra hsing
    exact hnot ((X.pCoreOf_arcStab_le_Q_left m r' h hsing).trans
      ((X.Q_le_Gi_adj m).trans inf_le_left))

theorem Qg_ne_bot (H : X.Sec4Hyp s r) : X.Qg r ≠ ⊥ := by
  have hnot : ¬ X.Qg r ≤ MulAction.stabilizer G (X.vert ((r : ℤ) + 1)) :=
    (X.rightTransAt_iff H H.longReg.1.1).mp H.longReg.1.2.2.1
  exact fun hbot => hnot (by rw [hbot]; exact bot_le)

theorem mem_fixSet_reflection_iff {P : Subgroup G} {x : G} {c : ℤ}
    (hPconj : conjSub x P = P) (hact : ∀ j : ℤ, x • X.vert j = X.vert (2 * c - j)) :
    ∀ j : ℤ, j ∈ X.fixSet P ↔ (2 * c - j) ∈ X.fixSet P := by
  have hactinv : ∀ j : ℤ, x⁻¹ • X.vert j = X.vert (2 * c - j) := by
    intro j
    have h2 : x • X.vert (2 * c - j) = X.vert j := by
      have h := hact (2 * c - j)
      rwa [show 2 * c - (2 * c - j) = j by ring] at h
    rw [← h2, inv_smul_smul]
  intro j
  constructor
  · intro hj p hp
    have hq : x⁻¹ * p * x ∈ P := CFSG.Quasithin.mem_conjSub.mp (by rw [hPconj]; exact hp)
    have hp_eq : p = x * (x⁻¹ * p * x) * x⁻¹ := by group
    rw [hp_eq, mul_smul, mul_smul]
    have h1 : x⁻¹ • X.vert (2 * c - j) = X.vert j := by
      have h := hactinv (2 * c - j)
      rwa [show 2 * c - (2 * c - j) = j by ring] at h
    rw [h1, hj _ hq, hact]
  · intro hj p hp
    have hq : x⁻¹ * p * x ∈ P := CFSG.Quasithin.mem_conjSub.mp (by rw [hPconj]; exact hp)
    have hp_eq : p = x * (x⁻¹ * p * x) * x⁻¹ := by group
    rw [hp_eq, mul_smul, mul_smul, hactinv]
    rw [hj _ hq]
    have h := hact (2 * c - j)
    rwa [show 2 * c - (2 * c - j) = j by ring] at h

private theorem fixSet_Z_symm (H : X.Sec4Hyp s r) (i j : ℤ) :
    j ∈ X.fixSet (X.Z i) ↔ (2 * i - j) ∈ X.fixSet (X.Z i) := by
  obtain ⟨t, ht, htref⟩ := X.exists_reflection H i
  have htj : ∀ k : ℤ, t • X.vert k = X.vert (2 * i - k) := fun k => by
    have h := htref (k - i)
    rwa [show i + (k - i) = k by ring, show i - (k - i) = 2 * i - k by ring] at h
  exact X.mem_fixSet_reflection_iff (X.Z_normal i t ht.1) htj j

theorem exists_hasB (H : X.Sec4Hyp s r) (i : ℤ) : ∃ d : ℕ, X.HasB i d := by
  have hZne : X.Z i ≠ ⊥ := X.Z_ne_bot_of i (X.Q_ne_bot H.char i)
  have hZ2 : IsPGroup 2 ↥(X.Z i) :=
    (pCoreOf_isPGroup' (X.Gi i)).to_le (X.Z_le_Q i)
  have hi_mem : i ∈ X.fixSet (X.Z i) := by
    rw [X.mem_fixSet_iff_le_Gi]
    exact X.Z_le_Gi i
  rcases fixSet_trichotomy X.hyp.isTree X.hyp.adj_smul X.hyp.finite_stab X.toTrack (X.Z i)
    with huniv | hempty | ⟨a, b, hab, hIcc⟩
  · exfalso
    have hZGT : X.Z i ≤ X.GT := X.le_GT_of_fixSet_eq_univ huniv
    have hbot := inf_eq_bot_of_odd_of_isPGroup (A := X.GT) (B := X.Z i) H.odd_GT hZ2
    have hle : X.Z i ≤ X.GT ⊓ X.Z i := le_inf hZGT le_rfl
    rw [hbot] at hle
    exact hZne (le_bot_iff.mp hle)
  · rw [hempty] at hi_mem
    simp at hi_mem
  · have hiI : i ∈ Set.Icc a b := by rw [← hIcc]; exact hi_mem
    rw [Set.mem_Icc] at hiI
    have ha_mem : a ∈ X.fixSet (X.Z i) := by rw [hIcc]; exact Set.left_mem_Icc.mpr hab
    have hb_mem : b ∈ X.fixSet (X.Z i) := by rw [hIcc]; exact Set.right_mem_Icc.mpr hab
    have hsymm := X.fixSet_Z_symm H i
    have h1 : a ≤ 2 * i - b := by
      have h := (hsymm b).mp hb_mem
      rw [hIcc, Set.mem_Icc] at h
      exact h.1
    have h2 : 2 * i - a ≤ b := by
      have h := (hsymm a).mp ha_mem
      rw [hIcc, Set.mem_Icc] at h
      exact h.2
    have habsum : a + b = 2 * i := by omega
    have hd_nonneg : 0 ≤ b - i := by omega
    let d : ℕ := (b - i).toNat
    have hdc : (d : ℤ) = b - i := Int.toNat_of_nonneg hd_nonneg
    have hb_eq : b = i + d := by omega
    have ha_eq : a = i - d := by omega
    refine ⟨d, ?_, ?_, ?_⟩
    · intro j hj
      have hjle : (j.natAbs : ℤ) ≤ (d : ℤ) := by exact_mod_cast hj
      have hmem : i + j ∈ X.fixSet (X.Z i) := by
        rw [hIcc, Set.mem_Icc]
        rcases Int.natAbs_eq j with h | h <;> omega
      exact (X.mem_fixSet_iff_le_Gi (X.Z i) (i + j)).mp hmem
    · intro h
      have hmem : i + d + 1 ∈ X.fixSet (X.Z i) := (X.mem_fixSet_iff_le_Gi _ _).mpr h
      rw [hIcc, Set.mem_Icc] at hmem
      omega
    · intro h
      have hmem : i - d - 1 ∈ X.fixSet (X.Z i) := (X.mem_fixSet_iff_le_Gi _ _).mpr h
      rw [hIcc, Set.mem_Icc] at hmem
      omega

theorem hasB_iff_of_even {i j : ℤ} (hij : Even (i - j)) (d : ℕ) :
    X.HasB i d ↔ X.HasB j d := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, i - j = 2 * m := by
    obtain ⟨k, hk⟩ := hij
    exact ⟨k, by omega⟩
  have hZ : X.Z i = conjSub (X.τ ^ m) (X.Z j) := by
    rw [show i = j + 2 * m by omega, X.Z_add]
  have hGi : ∀ k : ℤ, X.Gi (i + k) = conjSub (X.τ ^ m) (X.Gi (j + k)) := by
    intro k
    rw [show i + k = (j + k) + 2 * m by omega, X.Gi_add]
  have hiff : ∀ {A B : Subgroup G},
      A ≤ B ↔ conjSub (X.τ ^ m) A ≤ conjSub (X.τ ^ m) B :=
    fun {_ _} => (Subgroup.map_le_map_iff_of_injective (MulAut.conj _).injective).symm
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      have h := h1 k hk
      rw [hZ, hGi k] at h
      exact hiff.mpr h
    · intro h
      apply h2
      rw [hZ, show i + (d : ℤ) + 1 = (j + (d : ℤ) + 1) + 2 * m by omega, X.Gi_add]
      exact hiff.mp h
    · intro h
      apply h3
      rw [hZ, show i - (d : ℤ) - 1 = (j - (d : ℤ) - 1) + 2 * m by omega, X.Gi_add]
      exact hiff.mp h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      have h := h1 k hk
      rw [hZ, hGi k]
      exact hiff.mp h
    · intro h
      apply h2
      rw [hZ, show i + (d : ℤ) + 1 = (j + (d : ℤ) + 1) + 2 * m by omega, X.Gi_add] at h
      exact hiff.mpr h
    · intro h
      apply h3
      rw [hZ, show i - (d : ℤ) - 1 = (j - (d : ℤ) - 1) + 2 * m by omega, X.Gi_add] at h
      exact hiff.mpr h

theorem hasB_swap {i : ℤ} {d : ℕ} : X.swap.HasB i d ↔ X.HasB (1 - i) d := by
  unfold HasB
  simp only [Setup.swap_Z, Setup.swap_Gi]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have h := h1 (-j) (by simpa using hj)
      rwa [show (1 : ℤ) - (i + -j) = 1 - i + j by ring] at h
    · convert h3 using 2
      ring
    · convert h2 using 2
      ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have h := h1 (-j) (by simpa using hj)
      rwa [show (1 : ℤ) - i + -j = 1 - (i + j) by ring] at h
    · convert h3 using 2
      ring
    · convert h2 using 2
      ring

theorem fixSet_Z {d : ℕ} (i : ℤ) (hd : X.HasB i d) :
    X.fixSet (X.Z i) = Set.Icc (i - d) (i + d) := by
  apply Set.Subset.antisymm
  · intro j hj
    have hjGi : X.Z i ≤ X.Gi j := (X.mem_fixSet_iff_le_Gi (X.Z i) j).mp hj
    have hZi : X.Z i ≤ X.Gi i := X.Z_le_Gi i
    rw [Set.mem_Icc]
    constructor
    · by_contra hlt
      rw [not_le] at hlt
      have hmid : X.Z i ≤ X.Gi (i - (d : ℤ) - 1) := by
        intro z hz
        exact X.mem_Gi_of_between (hjGi hz) (hZi hz) (by omega) (by omega)
      exact hd.2.2 hmid
    · by_contra hlt
      rw [not_le] at hlt
      have hmid : X.Z i ≤ X.Gi (i + (d : ℤ) + 1) := by
        intro z hz
        exact X.mem_Gi_of_between (hZi hz) (hjGi hz) (by omega) (by omega)
      exact hd.2.1 hmid
  · intro j hj
    rw [Set.mem_Icc] at hj
    rw [X.mem_fixSet_iff_le_Gi]
    have hnat : (((j - i).natAbs : ℕ) : ℤ) ≤ (d : ℤ) := by
      rcases Int.natAbs_eq (j - i) with h | h <;> omega
    have hle : (j - i).natAbs ≤ d := by exact_mod_cast hnat
    have h := hd.1 (j - i) hle
    simpa [show i + (j - i) = j by ring] using h

theorem Z_le_Q_of_lt {i : ℤ} {d : ℕ} (hd : X.HasB i d) {j : ℤ}
    (hj : (j - i).natAbs < d) : X.Z i ≤ X.Q j := by
  have hdpos : 0 < d := by omega
  have hbound : ((j - i).natAbs : ℤ) < (d : ℤ) := by exact_mod_cast hj
  rcases lt_or_ge j i with hji | hij
  · have hnonpos : j - i ≤ 0 := by omega
    have hcast : ((j - i).natAbs : ℤ) = -(j - i) := by
      rcases Int.natAbs_eq (j - i) with h | h <;> omega
    have hZi : X.Z i ≤ X.Gi (i - d) := by
      have h := hd.1 (-(d : ℤ)) (by simp)
      rwa [show i + -(d : ℤ) = i - (d : ℤ) by ring] at h
    refine X.Z_le_Q_of_le_Gi i (i - d) j hZi (Or.inr ?_)
    constructor
    · rw [min_eq_right (by omega)]
      omega
    · rw [max_eq_left (by omega)]
      omega
  · rcases eq_or_lt_of_le hij with rfl | hij'
    · exact X.Z_le_Q i
    · have hnonneg : 0 ≤ j - i := by omega
      have hcast : ((j - i).natAbs : ℤ) = j - i := by
        rcases Int.natAbs_eq (j - i) with h | h <;> omega
      have hZi : X.Z i ≤ X.Gi (i + d) := by
        have h := hd.1 (d : ℤ) (by simp)
        simpa using h
      refine X.Z_le_Q_of_le_Gi i (i + d) j hZi (Or.inr ?_)
      constructor
      · rw [min_eq_left (by omega)]
        omega
      · rw [max_eq_right (by omega)]
        omega

theorem not_Z_le_Q_edge {i : ℤ} {d : ℕ} (hd : X.HasB i d) :
    ¬ X.Z i ≤ X.Q (i + d) ∧ ¬ X.Z i ≤ X.Q (i - d) := by
  constructor
  · intro hle
    exact hd.2.1 (fun z hz => ((X.Q_le_Gi_adj (i + d)) (hle hz)).2)
  · intro hle
    exact hd.2.2 (fun z hz => ((X.Q_le_Gi_adj (i - d)) (hle hz)).1)

theorem le_r_of_fixes (H : X.Sec4Hyp s r) {U : Subgroup G} (hU : IsPGroup 2 U) (hne : U ≠ ⊥)
    {a : ℤ} {k : ℕ} (hfix : U ≤ X.arcStab a (a + k)) : k ≤ r := by
  by_contra hk
  rw [not_le] at hk
  have hlong := H.longReg.2 a k hk
  have hUK : U ≤ X.K := by
    rw [← X.GT_eq_K_of_odd H]
    exact hfix.trans (le_of_eq hlong)
  have hbot : X.K ⊓ U = ⊥ :=
    inf_eq_bot_of_odd_of_isPGroup (A := X.K) (B := U) X.odd_card_K hU
  have hle : U ≤ X.K ⊓ U := le_inf hUK le_rfl
  rw [hbot] at hle
  exact hne (le_bot_iff.mp hle)

private theorem card_eq_two_pow_of_K_invariant (H : X.Sec4Hyp s r) {a : ℤ} {W : Subgroup G}
    (hWE : W ≤ X.edgeSylow a) (hWK : X.K ≤ Subgroup.normalizer (W : Set G))
    (hWne : W ≠ ⊥) (hWQ : W ⊓ X.Q a = ⊥) : Nat.card W = 2 ^ X.n a := by
  have hsup := X.sup_Q_eq_edgeSylow_of_left_gen a (inf_le_left.trans hWK) hWE
    (fun h => hWne (by rwa [inf_eq_left.mpr h] at hWQ))
  have hWGi : W ≤ X.Gi a := hWE.trans ((X.isSylowTwoOf_edgeSylow a).1.trans inf_le_left)
  have hWnorm : W ≤ Subgroup.normalizer (X.Q a : Set G) :=
    hWGi.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi a))
  have hcard : Nat.card (X.edgeSylow a) = Nat.card (X.Q a) * Nat.card W := by
    rw [← hsup, sup_comm]
    exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (X.Q a) W
      hWnorm (by rwa [disjoint_iff, inf_comm])
  have hrel : (X.Q a).relIndex (X.edgeSylow a) = 2 ^ X.n a :=
    X.relIndex_Q_edgeSylow a
  have hcard2 : (X.Q a).relIndex (X.edgeSylow a) * Nat.card (X.Q a) =
      Nat.card (X.edgeSylow a) := by
    have h := Subgroup.relIndex_mul_card (X.Q a) (X.edgeSylow a)
    rwa [inf_eq_left.mpr (X.Q_le_edgeSylow_left a)] at h
  haveI : Finite ↥(X.Q a) := finite_of_le_stabilizer X.hyp (H := X.Q a) (X.Q_le_Gi a)
  have hQpos : 0 < Nat.card (X.Q a) := Nat.card_pos
  have heq : 2 ^ X.n a * Nat.card (X.Q a) = Nat.card W * Nat.card (X.Q a) := by
    rw [← hrel, hcard2, hcard, mul_comm]
  rw [Nat.eq_of_mul_eq_mul_right hQpos heq]

theorem pCoreOf_arcStab_r (H : X.Sec4Hyp s r) (a : ℤ)
    (hne : pCoreOf 2 (X.arcStab a (a + r)) ≠ ⊥) :
    Nat.card (pCoreOf 2 (X.arcStab a (a + r))) = 2 ^ X.n a ∧
      pCoreOf 2 (X.arcStab a (a + r)) ⊓ X.Q a = ⊥ ∧
      pCoreOf 2 (X.arcStab a (a + r)) ⊓ X.Q (a + r) = ⊥ ∧
      X.LeftTransAt a (a + r) ∧ X.RightTransAt a (a + r) := by
  set A := X.arcStab a (a + r) with hAdef
  set P := pCoreOf 2 A with hPdef
  have hr : (0 : ℤ) < (r : ℤ) := H.longReg.1.1
  have hlt : a < a + (r : ℤ) := by omega
  have hKA : X.K ≤ A := X.K_le_GT.trans (X.GT_le_arcStab a (a + (r : ℤ)))
  have hA_edge : A ≤ X.Gi a ⊓ X.Gi (a + 1) :=
    le_inf (X.arcStab_le_Gi_left hlt) (X.arcStab_le_Gi_left_succ hlt)
  have hP_eq : P = A ⊓ X.edgeSylow a :=
    (X.pCoreOf_eq_inf_edgeSylow a hKA hA_edge).1
  have hP_edge : P ≤ X.edgeSylow a := by rw [hP_eq]; exact inf_le_right
  have hPK : X.K ≤ Subgroup.normalizer (P : Set G) :=
    hKA.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A)
  have hPA : P ≤ A := CFSG.LieType.BorelTits.pCoreOf_le 2 A
  have hPinfQa : P ⊓ X.Q a = ⊥ := by
    by_contra hcon
    have hU2 : IsPGroup 2 ↥(P ⊓ X.Q a) := (pCoreOf_isPGroup' A).to_le inf_le_left
    have hUfix : P ⊓ X.Q a ≤ X.arcStab (a - 1) (a + (r : ℤ)) := by
      rw [X.arcStab_eq_inf (show a - 1 ≤ a + (r : ℤ) by omega)]
      refine le_inf ?_ ?_
      · intro z hz
        exact ((X.Q_le_Gi_adj a) (Subgroup.mem_inf.mp hz).2).1
      · intro z hz
        exact (X.arcStab_le_Gi_right hlt) (hPA (Subgroup.mem_inf.mp hz).1)
    have hfix' : P ⊓ X.Q a ≤
        X.arcStab (a - 1) ((a - 1) + ((r + 1 : ℕ) : ℤ)) := by
      rw [show a - 1 + ((r + 1 : ℕ) : ℤ) = a + (r : ℤ) by push_cast; ring]
      exact hUfix
    have hle := X.le_r_of_fixes H hU2 hcon hfix'
    omega
  have hPinfQb : P ⊓ X.Q (a + r) = ⊥ := by
    by_contra hcon
    have hU2 : IsPGroup 2 ↥(P ⊓ X.Q (a + r)) := (pCoreOf_isPGroup' A).to_le inf_le_left
    have hUfix : P ⊓ X.Q (a + (r : ℤ)) ≤ X.arcStab a (a + (r : ℤ) + 1) := by
      rw [X.arcStab_eq_inf (show a ≤ a + (r : ℤ) + 1 by omega)]
      refine le_inf ?_ ?_
      · intro z hz
        exact (X.arcStab_le_Gi_left hlt) (hPA (Subgroup.mem_inf.mp hz).1)
      · intro z hz
        exact ((X.Q_le_Gi_adj (a + (r : ℤ))) (Subgroup.mem_inf.mp hz).2).2
    have hfix' : P ⊓ X.Q (a + r) ≤ X.arcStab a (a + ((r + 1 : ℕ) : ℤ)) := by
      rw [show a + ((r + 1 : ℕ) : ℤ) = a + (r : ℤ) + 1 by push_cast; ring]
      exact hUfix
    have hle := X.le_r_of_fixes H hU2 hcon hfix'
    omega
  have hcard : Nat.card P = 2 ^ X.n a :=
    X.card_eq_two_pow_of_K_invariant H hP_edge hPK hne hPinfQa
  have hLeft : X.LeftTransAt a (a + (r : ℤ)) := by
    rw [X.leftTransAt_iff H hlt]
    change ¬ P ≤ MulAction.stabilizer G (X.vert (a - 1))
    intro hle
    have hfix : P ≤ X.arcStab (a - 1) (a + (r : ℤ)) := by
      rw [X.arcStab_eq_inf (show a - 1 ≤ a + (r : ℤ) by omega)]
      exact le_inf hle (hPA.trans (X.arcStab_le_Gi_right hlt))
    have hfix' : P ≤ X.arcStab (a - 1) ((a - 1) + ((r + 1 : ℕ) : ℤ)) := by
      rw [show a - 1 + ((r + 1 : ℕ) : ℤ) = a + (r : ℤ) by push_cast; ring]
      exact hfix
    have hle' := X.le_r_of_fixes H (pCoreOf_isPGroup' A) hne hfix'
    omega
  have hRight : X.RightTransAt a (a + (r : ℤ)) := by
    rw [X.rightTransAt_iff H hlt]
    change ¬ P ≤ MulAction.stabilizer G (X.vert (a + (r : ℤ) + 1))
    intro hle
    have hfix : P ≤ X.arcStab a (a + (r : ℤ) + 1) := by
      rw [X.arcStab_eq_inf (show a ≤ a + (r : ℤ) + 1 by omega)]
      exact le_inf (hPA.trans (X.arcStab_le_Gi_left hlt)) hle
    have hfix' : P ≤ X.arcStab a (a + ((r + 1 : ℕ) : ℤ)) := by
      rw [show a + ((r + 1 : ℕ) : ℤ) = a + (r : ℤ) + 1 by push_cast; ring]
      exact hfix
    have hle' := X.le_r_of_fixes H (pCoreOf_isPGroup' A) hne hfix'
    omega
  exact ⟨hcard, hPinfQa, hPinfQb, hLeft, hRight⟩

theorem le_pCoreOf_arcStab_r (H : X.Sec4Hyp s r) {U : Subgroup G} {a : ℤ}
    (hU2 : IsPGroup 2 U) (hfix : U ≤ X.arcStab a (a + r)) :
    U ≤ pCoreOf 2 (X.arcStab a (a + r)) := by
  set A := X.arcStab a (a + r) with hAdef
  have hlt : a < a + (r : ℤ) := by
    have := H.longReg.1.1
    omega
  have hKA : X.K ≤ A := X.K_le_GT.trans (X.GT_le_arcStab a (a + (r : ℤ)))
  have hA : A ≤ X.Gi a ⊓ X.Gi (a + 1) :=
    le_inf (X.arcStab_le_Gi_left hlt) (X.arcStab_le_Gi_left_succ hlt)
  haveI : Finite ↥(X.Gi a ⊓ X.Gi (a + 1)) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi a ⊓ X.Gi (a + 1)) inf_le_left
  rw [(X.pCoreOf_eq_inf_edgeSylow a hKA hA).1]
  exact le_inf hfix (le_of_normal_isSylowTwoOf (X.isSylowTwoOf_edgeSylow a)
    (X.edgeSylow_subgroupOf_normal a) (hfix.trans hA) hU2)

theorem eq_of_le_pCoreOf_arcStab_r (H : X.Sec4Hyp s r) {U : Subgroup G} {a : ℤ}
    (hK : X.K ≤ Subgroup.normalizer (U : Set G)) (hne : U ≠ ⊥)
    (hle : U ≤ pCoreOf 2 (X.arcStab a (a + r))) :
    U = pCoreOf 2 (X.arcStab a (a + r)) := by
  have hPne : pCoreOf 2 (X.arcStab a (a + r)) ≠ ⊥ := by
    intro hbot
    exact hne (le_bot_iff.mp (hbot ▸ hle))
  obtain ⟨hcardP, hPinfQa, -, -, -⟩ := X.pCoreOf_arcStab_r H a hPne
  set A := X.arcStab a (a + r) with hAdef
  set P := pCoreOf 2 A with hPdef
  have hr : (0 : ℤ) < (r : ℤ) := H.longReg.1.1
  have hlt : a < a + (r : ℤ) := by omega
  have hKA : X.K ≤ A := X.K_le_GT.trans (X.GT_le_arcStab a (a + (r : ℤ)))
  have hA_edge : A ≤ X.Gi a ⊓ X.Gi (a + 1) :=
    le_inf (X.arcStab_le_Gi_left hlt) (X.arcStab_le_Gi_left_succ hlt)
  have hP_edge : P ≤ X.edgeSylow a := by
    rw [hPdef, (X.pCoreOf_eq_inf_edgeSylow a hKA hA_edge).1]
    exact inf_le_right
  have hU_edge : U ≤ X.edgeSylow a := hle.trans hP_edge
  have hUinfQ : U ⊓ X.Q a = ⊥ := by
    refine le_bot_iff.mp ?_
    calc U ⊓ X.Q a ≤ P ⊓ X.Q a := inf_le_inf_right _ hle
      _ = ⊥ := hPinfQa
  have hcardU : Nat.card U = 2 ^ X.n a :=
    X.card_eq_two_pow_of_K_invariant H hU_edge hK hne hUinfQ
  haveI hAfin : Finite ↥A := finite_of_le_stabilizer X.hyp (H := A) (X.arcStab_le_Gi_left hlt)
  haveI hPfin : Finite ↥P := Finite.of_injective
    (Subgroup.inclusion (CFSG.LieType.BorelTits.pCoreOf_le 2 A))
    (Subgroup.inclusion_injective _)
  have hcardle : Nat.card P ≤ Nat.card U := by rw [hcardP, hcardU]
  exact Subgroup.eq_of_le_of_card_ge hle hcardle

private theorem isElemAbelian_of_invariant_eq_top {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] {P K : Subgroup G} (hP2 : IsPGroup p P) [Finite ↥P]
    (hPne : P ≠ ⊥) (hKP : K ≤ Subgroup.normalizer (P : Set G))
    (hmax : ∀ U : Subgroup G, U ≤ P → K ≤ Subgroup.normalizer (U : Set G) →
      U ≠ ⊥ → U = P) :
    IsElemAbelian p P := by
  let C : Subgroup ↥P := Subgroup.center ↥P
  let Ω : Subgroup ↥C := CFSG.omega₁ ↥C (p := p)
  let V : Subgroup ↥P := Ω.map C.subtype
  let U : Subgroup G := V.map P.subtype
  haveI hCchar : C.Characteristic := Subgroup.centerCharacteristic
  haveI hΩchar : Ω.Characteristic := CFSG.omega₁_characteristic ↥C
  haveI hVchar : V.Characteristic :=
    Subgroup.characteristic_of_characteristic_of_characteristic
  have hC2 : IsPGroup p ↥C := hP2.to_subgroup C
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
  haveI hCnt : Nontrivial ↥C := hP2.center_nontrivial
  have hCdiv : p ∣ Nat.card ↥C := by
    rcases hC2.card_eq_or_dvd with h | h
    · have h1 : 1 < Nat.card ↥C := Finite.one_lt_card
      omega
    · exact h
  have hVne : V ≠ ⊥ := CFSG.omega₁_map_subtype_ne_bot C p hCdiv
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hVne
    exact (Subgroup.map_eq_bot_iff_of_injective (H := V) (f := P.subtype)
      P.subtype_injective).mp hbot
  have hUle : U ≤ P := Subgroup.map_subtype_le V
  have hKU : K ≤ Subgroup.normalizer (U : Set G) :=
    hKP.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic V)
  have hUeq : U = P := hmax U hUle hKU hUne
  haveI hΩelem : CFSG.IsElementaryAbelian p ↥Ω :=
    CFSG.IsElementaryAbelian.omega₁_of_isMulCommutative ↥C
  have hkey : ∀ x ∈ P, x ^ p = 1 ∧ ∀ y ∈ P, x * y = y * x := by
    intro x hx
    have hxU : x ∈ U := hUeq.symm ▸ hx
    obtain ⟨y, hyV, rfl⟩ := Subgroup.mem_map.mp hxU
    obtain ⟨z, hzΩ, rfl⟩ := Subgroup.mem_map.mp hyV
    have hzp : z ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian z hzΩ
    constructor
    · simpa using congrArg (fun w : ↥C => ((w : ↥P) : G)) hzp
    · intro w hw
      have hc := Subgroup.mem_center_iff.mp z.2 (⟨w, hw⟩ : ↥P)
      exact (congrArg (fun t : ↥P => (t : G)) hc).symm
  rw [F7.isElemAbelian_iff]
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    exact (hkey x hx).2 y hy
  · intro x hx
    exact (hkey x hx).1

theorem isElemAbelian_pCoreOf_arcStab_r (H : X.Sec4Hyp s r) (a : ℤ) :
    IsElemAbelian 2 (pCoreOf 2 (X.arcStab a (a + r))) := by
  set A := X.arcStab a (a + r) with hAdef
  set P := pCoreOf 2 A with hPdef
  by_cases hbot : P = ⊥
  · rw [hbot, F7.isElemAbelian_iff]
    exact ⟨fun x hx y hy => by rw [Subgroup.mem_bot.mp hx, Subgroup.mem_bot.mp hy],
      fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩
  · have hlt : a < a + (r : ℤ) := by
      have := H.longReg.1.1
      omega
    haveI hAfin : Finite ↥A :=
      finite_of_le_stabilizer X.hyp (H := A) (X.arcStab_le_Gi_left hlt)
    haveI hPfin : Finite ↥P := Finite.of_injective
      (Subgroup.inclusion (CFSG.LieType.BorelTits.pCoreOf_le 2 A))
      (Subgroup.inclusion_injective _)
    have hP2 : IsPGroup 2 P := by
      rw [hPdef]
      exact pCoreOf_isPGroup' A
    have hPK : X.K ≤ Subgroup.normalizer (P : Set G) := by
      have hKA : X.K ≤ A := X.K_le_GT.trans (X.GT_le_arcStab a (a + (r : ℤ)))
      simpa [hPdef] using hKA.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A)
    exact isElemAbelian_of_invariant_eq_top hP2 hbot hPK
      (fun U hUle hKnorm hUne => X.eq_of_le_pCoreOf_arcStab_r H hKnorm hUne hUle)

theorem Ki_fpf_pCoreOf_arcStab_r (H : X.Sec4Hyp s r) (a : ℤ) {k : G} (hk : k ∈ X.Ki a)
    (hk1 : k ≠ 1) :
    ∀ u ∈ pCoreOf 2 (X.arcStab a (a + r)), k * u = u * k → u = 1 := by
  intro u hu hcomm
  by_contra hu1
  have hr : (0 : ℤ) < (r : ℤ) := by
    have h5 := H.five_le
    have hle := H.le_r
    omega
  have hlt : a < a + (r : ℤ) := by omega
  have hPA : pCoreOf 2 (X.arcStab a (a + (r : ℤ))) ≤ X.arcStab a (a + (r : ℤ)) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have huA : u ∈ X.arcStab a (a + (r : ℤ)) := hPA hu
  have hua : u ∈ X.Gi a := X.arcStab_le_Gi_left hlt huA
  have hua1 : u ∈ X.Gi (a + 1) := X.arcStab_le_Gi_left_succ hlt huA
  have hkn : 2 ≤ X.n a := H.two_le_n a
  have hufix_a : u • X.vert a = X.vert a := MulAction.mem_stabilizer_iff.mp hua
  have hufix_a1 : u • X.vert (a + 1) = X.vert (a + 1) :=
    MulAction.mem_stabilizer_iff.mp hua1
  have hadjL : Γ.Adj (X.vert a) (X.vert (a - 1)) := by
    have h := (X.adj (a - 1)).symm
    rwa [show a - 1 + 1 = a by ring] at h
  have hadjL' : Γ.Adj (X.vert a) (u • X.vert (a - 1)) := by
    have h := (X.hyp.adj_smul u (X.vert a) (X.vert (a - 1))).2 hadjL
    rwa [hufix_a] at h
  have hkfix : k • (u • X.vert (a - 1)) = u • X.vert (a - 1) := by
    rw [← mul_smul, hcomm, mul_smul, X.K_fix k hk.1 (a - 1)]
  have hufix_am1 : u • X.vert (a - 1) = X.vert (a - 1) := by
    rcases (X.torus_fixed a hkn hk hk1 (u • X.vert (a - 1)) hadjL').mp hkfix with h | h
    · exact h
    · exfalso
      have heq : u • X.vert (a - 1) = u • X.vert (a + 1) := by rw [h, hufix_a1]
      have h2 : X.vert (a - 1) = X.vert (a + 1) := by
        have h3 := congrArg (fun v => u⁻¹ • v) heq
        simpa using h3
      exact absurd (X.vert_injective h2) (by omega)
  have huAm1 : u ∈ X.Gi (a - 1) := MulAction.mem_stabilizer_iff.mpr hufix_am1
  have huAr : u ∈ X.Gi (a + (r : ℤ)) := X.arcStab_le_Gi_right hlt huA
  have hzp : Subgroup.zpowers u ≤ X.arcStab (a - 1) ((a - 1) + ((r + 1 : ℕ) : ℤ)) := by
    rw [show a - 1 + ((r + 1 : ℕ) : ℤ) = a + (r : ℤ) by push_cast; ring,
      X.arcStab_eq_inf (show a - 1 ≤ a + (r : ℤ) by omega)]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨huAm1, huAr⟩)
  have hP2 : IsPGroup 2 (Subgroup.zpowers u) :=
    (pCoreOf_isPGroup' (X.arcStab a (a + (r : ℤ)))).to_le (Subgroup.zpowers_le.mpr hu)
  have hPne : Subgroup.zpowers u ≠ ⊥ := by
    intro hbot
    have : u ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers u
    exact hu1 (Subgroup.mem_bot.mp this)
  have hle := X.le_r_of_fixes H hP2 hPne hzp
  omega

end Setup

end CFSG.Quasithin.St84
