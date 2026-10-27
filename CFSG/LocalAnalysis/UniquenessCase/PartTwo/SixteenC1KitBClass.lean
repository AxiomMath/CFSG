module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitBStruct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code CFSG.LargeExtraspecial.O62.Check
open scoped Pointwise

private theorem s16c1b_A_getD_mem (i : Fin 3) : s16c1b_A.getD i.val [] ∈ s16c1b_A := by
  fin_cases i <;> decide

private theorem s16c1b_A_props {L : List ℕ} (hL : L ∈ s16c1b_A) :
    one ∈ L ∧ (∀ x ∈ L, mul x x = one) ∧ (∀ x ∈ L, ∀ y ∈ L, mul x y ∈ L) := by
  have h := s16c1b_checkA_ok
  simp only [s16c1b_checkA, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨-, hone⟩, hinv⟩, hmul⟩ := h.2 L hL
  refine ⟨List.contains_iff_mem.mp hone, ?_, ?_⟩
  · intro x hx
    exact beq_iff_eq.mp (hinv x hx).2
  · intro x hx y hy
    exact List.contains_iff_mem.mp (hmul x hx y hy)

@[expose] noncomputable def s16c1b_Asub (i : Fin 3) : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) where
  carrier := {g | ∃ c ∈ s16c1b_A.getD i.val [], Coded g c}
  one_mem' := by
    obtain ⟨hone, -, -⟩ := s16c1b_A_props (s16c1b_A_getD_mem i)
    exact ⟨one, hone, coded_one⟩
  mul_mem' := by
    obtain ⟨-, -, hmul⟩ := s16c1b_A_props (s16c1b_A_getD_mem i)
    rintro g h ⟨a, ha, hga⟩ ⟨b, hb, hhb⟩
    exact ⟨mul a b, hmul a ha b hb, hga.mul hhb⟩
  inv_mem' := by
    obtain ⟨-, hinv, -⟩ := s16c1b_A_props (s16c1b_A_getD_mem i)
    rintro g ⟨a, ha, hga⟩
    refine ⟨a, ha, ?_⟩
    have hsq : Coded (g * g) (mul a a) := hga.mul hga
    rw [hinv a ha] at hsq
    have hgg : g * g = 1 := (hsq.eq_iff coded_one).mpr rfl
    rw [inv_eq_of_mul_eq_one_right hgg]
    exact hga

@[expose] noncomputable def s16c1b_Qsub : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) := ⨆ i : Fin 3, s16c1b_Asub i

@[expose] def s16c1b_SpanCoded (A : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (xs : List ℕ) : Prop :=
  ∀ c : ℕ, c ∈ spanC xs ↔ ∃ g ∈ A, Coded g c

inductive s16c1b_Reach : List ℕ → Prop
  | nil : s16c1b_Reach []
  | cons {xs : List ℕ} {x : ℕ} : s16c1b_Reach xs → x ∈ s16c1b_S0.filter isInv →
      s16c1b_extOK xs x = true → s16c1b_Reach (x :: xs)

private theorem s16c1b_A_length : s16c1b_A.length = 3 := by
  have h := s16c1b_checkA_ok
  simp only [s16c1b_checkA, Bool.and_eq_true] at h
  exact beq_iff_eq.mp h.1

private def s16c1b_nodeTest (xs : List ℕ) : Bool :=
  xs.isEmpty || !s16c1b_a2Prop xs || s16c1b_inA (spanC xs)

private theorem s16c1b_dfs_zero (invs xs : List ℕ) :
    s16c1b_dfs invs 0 xs =
      (s16c1b_nodeTest xs && invs.all fun x => !s16c1b_extOK xs x) := rfl

private theorem s16c1b_dfs_succ (invs xs : List ℕ) (n : ℕ) :
    s16c1b_dfs invs (n + 1) xs =
      (s16c1b_nodeTest xs &&
        invs.all fun x => !s16c1b_extOK xs x || s16c1b_dfs invs n (x :: xs)) := rfl

private theorem s16c1b_dfs_nodeTest {invs : List ℕ} {n : ℕ} {xs : List ℕ}
    (h : s16c1b_dfs invs n xs = true) : s16c1b_nodeTest xs = true := by
  cases n with
  | zero => rw [s16c1b_dfs_zero] at h; exact (Bool.and_eq_true_iff.mp h).1
  | succ n => rw [s16c1b_dfs_succ] at h; exact (Bool.and_eq_true_iff.mp h).1

private theorem s16c1b_dfs_reach {invs : List ℕ} (hinvs : invs = s16c1b_S0.filter isInv)
    (xs : List ℕ) (h : s16c1b_Reach xs) :
    xs.length ≤ 4 ∧ s16c1b_dfs invs (4 - xs.length) xs = true := by
  induction h with
  | nil =>
    exact ⟨by simp, by simpa [s16c1b_checkClassify, hinvs] using s16c1b_checkClassify_ok⟩
  | @cons xs x hreach hx hext ih =>
    obtain ⟨hlen, hdfs⟩ := ih
    have hx' : x ∈ invs := by rw [hinvs]; exact hx
    have hle3 : xs.length ≤ 3 := by
      by_contra hlt
      have h4 : xs.length = 4 := by omega
      have h0 : s16c1b_dfs invs 0 xs = true := by simpa [h4] using hdfs
      rw [s16c1b_dfs_zero] at h0
      have hall := (Bool.and_eq_true_iff.mp h0).2
      have hxfalse : (!s16c1b_extOK xs x) = true := List.all_eq_true.mp hall x hx'
      simp [hext] at hxfalse
    refine ⟨by simp; omega, ?_⟩
    have hpos : 1 ≤ 4 - xs.length := by omega
    obtain ⟨m, hm⟩ : ∃ m, 4 - xs.length = m + 1 := ⟨4 - xs.length - 1, by omega⟩
    have hdfs' : s16c1b_dfs invs (m + 1) xs = true := by rwa [hm] at hdfs
    rw [s16c1b_dfs_succ] at hdfs'
    have hall := (Bool.and_eq_true_iff.mp hdfs').2
    have hxstep : (!s16c1b_extOK xs x || s16c1b_dfs invs m (x :: xs)) = true :=
      List.all_eq_true.mp hall x hx'
    have hnot : (!s16c1b_extOK xs x) = false := by simp [hext]
    rw [hnot, Bool.false_or] at hxstep
    rw [show 4 - (x :: xs).length = m by simp; omega]
    exact hxstep

theorem s16c1b_reach_spec {xs : List ℕ} (h : s16c1b_Reach xs) :
    (xs.isEmpty || !s16c1b_a2Prop xs || s16c1b_inA (spanC xs)) = true ∧ xs.length ≤ 4 := by
  obtain ⟨hlen, hdfs⟩ := s16c1b_dfs_reach rfl xs h
  exact ⟨by simpa [s16c1b_nodeTest] using s16c1b_dfs_nodeTest hdfs, hlen⟩

private theorem s16c1b_exists_code (g : V₀ ≃ₗ[ZMod 2] V₀) : ∃ c, Coded g c := by
  have hinj : Function.Injective (fun m : Fin (2 ^ 36) => mat m.val) := by
    intro m m' h
    exact Fin.ext (Code.eq_of_mat_eq m.isLt m'.isLt h)
  have hcard : Fintype.card (Fin (2 ^ 36)) =
      Fintype.card (Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    rw [Fintype.card_fin]
    show 2 ^ 36 = Fintype.card (Fin 6 → Fin 6 → ZMod 2)
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    norm_num
  have hsurj : Function.Surjective (fun m : Fin (2 ^ 36) => mat m.val) := by
    by_contra hns
    have hlt := Fintype.card_lt_of_injective_not_surjective _ hinj hns
    omega
  obtain ⟨m, hm⟩ := hsurj (LinearMap.toMatrix' (g : V₀ →ₗ[ZMod 2] V₀))
  exact ⟨m.val, hm.symm, m.isLt⟩

theorem s16c1b_eq_Asub_of_inA {A : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {xs : List ℕ}
    (hspan : s16c1b_SpanCoded A xs) (hin : s16c1b_inA (spanC xs) = true) :
    ∃ i : Fin 3, A = s16c1b_Asub i := by
  obtain ⟨a, ha, hcond⟩ := List.any_eq_true.mp hin
  obtain ⟨hsub1, hsub2⟩ := Bool.and_eq_true_iff.mp hcond
  have hset : ∀ c, c ∈ spanC xs ↔ c ∈ a := by
    intro c
    exact ⟨fun hc => List.contains_iff_mem.mp (List.all_eq_true.mp hsub1 c hc),
      fun hc => List.contains_iff_mem.mp (List.all_eq_true.mp hsub2 c hc)⟩
  obtain ⟨i, hi, haeq⟩ := List.mem_iff_getElem.mp ha
  have hi3 : i < 3 := by have := s16c1b_A_length; omega
  have hgetD : s16c1b_A.getD i [] = a := by
    rw [List.getD_eq_getElem s16c1b_A [] hi]; exact haeq
  refine ⟨⟨i, hi3⟩, ?_⟩
  ext g
  show g ∈ A ↔ ∃ c ∈ s16c1b_A.getD i [], Coded g c
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := s16c1b_exists_code g
    exact ⟨c, by rw [hgetD]; exact (hset c).mp ((hspan c).mpr ⟨g, hg, hc⟩), hc⟩
  · rintro ⟨c, hc, hgc⟩
    have hcspan : c ∈ spanC xs := (hset c).mpr (hgetD ▸ hc)
    obtain ⟨h, hhA, hhc⟩ := (hspan c).mp hcspan
    rwa [(hgc.eq_iff hhc).mpr rfl]

private theorem s16c1b_mul_assoc (a b c : ℕ) : mul (mul a b) c = mul a (mul b c) := by
  apply Code.eq_of_mat_eq (mul_lt _ _) (mul_lt _ _)
  rw [mat_mul, mat_mul, mat_mul, mat_mul, Matrix.mul_assoc]

private theorem s16c1b_mul_one {a : ℕ} (ha : a < 2 ^ 36) : mul a one = a := by
  apply Code.eq_of_mat_eq (mul_lt _ _) ha
  rw [mat_mul, mat_one, Matrix.mul_one]

private theorem s16c1b_one_mul {a : ℕ} (ha : a < 2 ^ 36) : mul one a = a := by
  apply Code.eq_of_mat_eq (mul_lt _ _) ha
  rw [mat_mul, mat_one, Matrix.one_mul]

private theorem s16c1b_mul_one_eq_one_mul (a : ℕ) : mul a one = mul one a := by
  apply Code.eq_of_mat_eq (mul_lt _ _) (mul_lt _ _)
  rw [mat_mul, mat_mul, mat_one, Matrix.mul_one, Matrix.one_mul]

private theorem s16c1b_comm_iff (a b : ℕ) : comm a b = true ↔ mul a b = mul b a := by
  simp [Check.comm]

private theorem s16c1b_spanC_lt : ∀ {xs : List ℕ} {c : ℕ}, c ∈ spanC xs → c < 2 ^ 36
  | [], c, hc => by
    simp only [spanC, List.mem_singleton] at hc
    rw [hc]; exact one_lt
  | x :: xs, c, hc => by
    rw [spanC_cons] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact s16c1b_spanC_lt hc
    · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hc
      exact mul_lt d x

private theorem s16c1b_one_mem_spanC : ∀ xs : List ℕ, one ∈ spanC xs
  | [] => by simp [spanC]
  | x :: xs => by
    rw [spanC_cons]
    exact List.mem_append_left _ (s16c1b_one_mem_spanC xs)

private theorem s16c1b_comm_spanC {x : ℕ} :
    ∀ {xs : List ℕ}, (∀ y ∈ xs, comm x y = true) → ∀ b ∈ spanC xs, comm x b = true
  | [], _, b, hb => by
    simp only [spanC, List.mem_singleton] at hb
    rw [hb, s16c1b_comm_iff]
    exact s16c1b_mul_one_eq_one_mul x
  | y :: xs, h, b, hb => by
    rw [spanC_cons] at hb
    rcases List.mem_append.mp hb with hb | hb
    · exact s16c1b_comm_spanC (fun z hz => h z (List.mem_cons_of_mem _ hz)) b hb
    · obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      rw [s16c1b_comm_iff]
      rw [← s16c1b_mul_assoc x b' y,
        (s16c1b_comm_iff x b').mp
          (s16c1b_comm_spanC (fun z hz => h z (List.mem_cons_of_mem _ hz)) b' hb'),
        s16c1b_mul_assoc b' x y,
        (s16c1b_comm_iff x y).mp (h y List.mem_cons_self),
        ← s16c1b_mul_assoc b' y x]

private theorem s16c1b_spanC_mul_closed :
    ∀ {xs : List ℕ}, s16c1b_Reach xs → ∀ a ∈ spanC xs, ∀ b ∈ spanC xs, mul a b ∈ spanC xs
  | _, .nil, a, ha, b, hb => by
    simp only [spanC, List.mem_singleton] at ha hb
    rw [ha, hb]
    rw [s16c1b_mul_one one_lt]
    simp [spanC]
  | _, .cons (xs := xs) (x := x) hreach hx hext, a, ha, b, hb => by
    have ih := s16c1b_spanC_mul_closed hreach
    obtain ⟨-, hxinv⟩ := List.mem_filter.mp hx
    have hxx : mul x x = one := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hxinv).1
    have hcommall : (xs.all fun y => comm x y) = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hext).1).2
    have hxcomm : ∀ d ∈ spanC xs, comm x d = true :=
      s16c1b_comm_spanC (fun y hy => List.all_eq_true.mp hcommall y hy)
    rw [spanC_cons] at ha hb
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · exact List.mem_append_left _ (ih a ha b hb)
    · obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      rw [← s16c1b_mul_assoc a b' x]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨mul a b', ih a ha b' hb', rfl⟩)
    · obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      rw [s16c1b_mul_assoc a' x b, (s16c1b_comm_iff x b).mp (hxcomm b hb),
        ← s16c1b_mul_assoc a' b x]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨mul a' b, ih a' ha' b hb, rfl⟩)
    · obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      rw [s16c1b_mul_assoc a' x (mul b' x), ← s16c1b_mul_assoc x b' x,
        (s16c1b_comm_iff x b').mp (hxcomm b' hb'), s16c1b_mul_assoc b' x x, hxx,
        s16c1b_mul_one (s16c1b_spanC_lt hb')]
      exact List.mem_append_left _ (ih a' ha' b' hb')

private theorem s16c1b_spanC_mono {l' : List ℕ}
    (hclosed : ∀ a ∈ spanC l', ∀ b ∈ spanC l', mul a b ∈ spanC l') :
    ∀ (l : List ℕ), (∀ d ∈ l, d ∈ spanC l') → ∀ e ∈ spanC l, e ∈ spanC l'
  | [], _, e, he => by
    simp only [spanC, List.mem_singleton] at he
    rw [he]; exact s16c1b_one_mem_spanC l'
  | d :: l, h, e, he => by
    rw [spanC_cons] at he
    rcases List.mem_append.mp he with he | he
    · exact s16c1b_spanC_mono hclosed l (fun y hy => h y (List.mem_cons_of_mem _ hy)) e he
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      exact hclosed e' (s16c1b_spanC_mono hclosed l (fun y hy => h y (List.mem_cons_of_mem _ hy))
        e' he') d (h d List.mem_cons_self)

private theorem s16c1b_isInv_of_coded {x : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ} (hx : Coded x c)
    (h2 : x ^ 2 = 1) (h1 : x ≠ 1) : isInv c = true := by
  have hsq : Coded (x * x) (mul c c) := hx.mul hx
  rw [← pow_two, h2] at hsq
  have e1 : mul c c = one := (hsq.eq_iff coded_one).mp rfl
  have e2 : c ≠ one := fun h => h1 ((hx.eq_iff coded_one).mpr h)
  simp [isInv, e1, e2]

private theorem s16c1b_comm_of_coded {x y : V₀ ≃ₗ[ZMod 2] V₀} {a b : ℕ} (hx : Coded x a)
    (hy : Coded y b) (h : x * y = y * x) : comm a b = true := by
  have e := ((hx.mul hy).eq_iff (hy.mul hx)).mp h
  simp [Check.comm, e]

private theorem s16c1b_forall₂_exists {l₁ : List (V₀ ≃ₗ[ZMod 2] V₀)} {l₂ : List ℕ}
    (h : List.Forall₂ Coded l₁ l₂) : ∀ c ∈ l₂, ∃ g ∈ l₁, Coded g c := by
  induction h with
  | nil => intro c hc; simp at hc
  | cons hab _ ih =>
    intro c hc
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨g, hg, hgc⟩ := ih c hc
      exact ⟨g, List.mem_cons_of_mem _ hg, hgc⟩

private theorem s16c1b_mem_spanC_self :
    ∀ {xs : List ℕ} {d : ℕ}, d ∈ xs → d < 2 ^ 36 → d ∈ spanC xs
  | [], d, hd, _ => by simp at hd
  | x :: xs, d, hd, hdlt => by
    rw [spanC_cons]
    rw [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact List.mem_append_right _
        (List.mem_map.mpr ⟨one, s16c1b_one_mem_spanC xs, s16c1b_one_mul hdlt⟩)
    · exact List.mem_append_left _ (s16c1b_mem_spanC_self hd hdlt)

private noncomputable def s16c1b_codeElem (A : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (c : ℕ) :
    V₀ ≃ₗ[ZMod 2] V₀ := by
  classical
  exact if h : ∃ g ∈ A, Coded g c then Classical.choose h else 1

private theorem s16c1b_codeElem_spec {A : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {c : ℕ}
    (h : ∃ g ∈ A, Coded g c) :
    s16c1b_codeElem A c ∈ A ∧ Coded (s16c1b_codeElem A c) c := by
  unfold s16c1b_codeElem
  rw [dif_pos h]
  exact Classical.choose_spec h

private noncomputable def s16c1b_greedy (A : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) :
    List ℕ → List ℕ → List (V₀ ≃ₗ[ZMod 2] V₀) → List ℕ × List (V₀ ≃ₗ[ZMod 2] V₀)
  | [], cs, gs => (cs, gs)
  | c :: L, cs, gs =>
      if c ∈ (spanC cs).toFinset then s16c1b_greedy A L cs gs
      else s16c1b_greedy A L (c :: cs) (s16c1b_codeElem A c :: gs)

private def s16c1b_greedyOK (A : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (L cs : List ℕ)
    (gs : List (V₀ ≃ₗ[ZMod 2] V₀)) : Prop :=
  let res := s16c1b_greedy A L cs gs
  s16c1b_Reach res.1 ∧ List.Forall₂ Coded res.2 res.1 ∧ (∀ g ∈ res.2, g ∈ A) ∧
    (∀ c ∈ L, c ∈ (spanC res.1).toFinset) ∧
    (∀ d ∈ cs, d ∈ res.1) ∧ (∀ g ∈ gs, g ∈ res.2)

private theorem s16c1b_greedy_spec (A : Subgroup (V₀ ≃ₗ[ZMod 2] V₀))
    (hinvA : ∀ g ∈ A, g ^ 2 = 1) (hcommAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ (L cs : List ℕ) (gs : List (V₀ ≃ₗ[ZMod 2] V₀)),
    (∀ c ∈ L, ∃ g ∈ A, Coded g c) →
    (∀ c ∈ L, c ∈ s16c1b_S0) →
    L.SortedLE →
    s16c1b_Reach cs → List.Forall₂ Coded gs cs →
    (∀ g ∈ gs, g ∈ A) → (∀ d ∈ cs, ∃ g ∈ A, Coded g d) →
    (∀ d ∈ cs, ∀ e ∈ L, d ≤ e) →
    s16c1b_greedyOK A L cs gs := by
  have hcommA : ∀ d e, (∃ g ∈ A, Coded g d) → (∃ g ∈ A, Coded g e) → comm d e = true := by
    rintro d e ⟨gd, hgdA, hgd⟩ ⟨ge, hgeA, hge⟩
    exact s16c1b_comm_of_coded hgd hge (hcommAb gd hgdA ge hgeA)
  intro L
  induction L with
  | nil =>
    intro cs gs hL hL0 hsort hreach hforall hgsA hcsA hbound
    exact ⟨hreach, hforall, hgsA, by simp, fun d hd => hd, fun g hg => hg⟩
  | cons c L ih =>
    intro cs gs hL hL0 hsort hreach hforall hgsA hcsA hbound
    have hL' : ∀ e ∈ L, ∃ g ∈ A, Coded g e := fun e he => hL e (List.mem_cons_of_mem _ he)
    have hL0' : ∀ e ∈ L, e ∈ s16c1b_S0 := fun e he => hL0 e (List.mem_cons_of_mem _ he)
    have hsort' : L.SortedLE := (List.sortedLE_cons.mp hsort).2
    have hgreedy : s16c1b_greedy A (c :: L) cs gs =
        (if c ∈ (spanC cs).toFinset then s16c1b_greedy A L cs gs
          else s16c1b_greedy A L (c :: cs) (s16c1b_codeElem A c :: gs)) := rfl
    by_cases hc : c ∈ (spanC cs).toFinset
    · have hbound' : ∀ d ∈ cs, ∀ e ∈ L, d ≤ e :=
        fun d hd e he => hbound d hd e (List.mem_cons_of_mem _ he)
      have hres := ih cs gs hL' hL0' hsort' hreach hforall hgsA hcsA hbound'
      dsimp only [s16c1b_greedyOK]
      rw [hgreedy, if_pos hc]
      refine ⟨hres.1, hres.2.1, hres.2.2.1, ?_, hres.2.2.2.2.1, hres.2.2.2.2.2⟩
      intro e he
      rcases List.mem_cons.mp he with hec | he
      · rw [hec]
        refine List.mem_toFinset.mpr (s16c1b_spanC_mono (s16c1b_spanC_mul_closed hres.1) cs
          (fun d hd => s16c1b_mem_spanC_self (hres.2.2.2.2.1 d hd)
            (hcsA d hd).choose_spec.2.2) c (List.mem_toFinset.mp hc))
      · exact hres.2.2.2.1 e he
    · have hcA : ∃ g ∈ A, Coded g c := hL c List.mem_cons_self
      have hcA' := hcA
      obtain ⟨gc, hgcA, hgcc⟩ := hcA'
      have hcmem : c ∉ spanC cs := fun h => hc (List.mem_toFinset.mpr h)
      have hclt : c < 2 ^ 36 := hgcc.2
      have hcInv : isInv c = true := by
        refine s16c1b_isInv_of_coded hgcc (hinvA gc hgcA) ?_
        intro h1
        exact hcmem (by rw [(hgcc.eq_iff coded_one).mp h1]; exact s16c1b_one_mem_spanC cs)
      have hext : s16c1b_extOK cs c = true := by
        rw [s16c1b_extOK]
        simp only [Bool.and_eq_true_iff, List.all_eq_true, decide_eq_true_eq,
          List.contains_iff_mem]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro d hd
          have hle : d ≤ c := hbound d hd c List.mem_cons_self
          have hne : d ≠ c := by
            intro hdc
            exact hcmem (hdc ▸ s16c1b_mem_spanC_self hd (hcsA d hd).choose_spec.2.2)
          omega
        · intro d hd
          exact hcommA c d hcA (hcsA d hd)
        · simpa [List.contains_iff_mem] using hcmem
      have hreach' : s16c1b_Reach (c :: cs) :=
        s16c1b_Reach.cons hreach (List.mem_filter.mpr ⟨hL0 c List.mem_cons_self, hcInv⟩) hext
      have hforall' : List.Forall₂ Coded (s16c1b_codeElem A c :: gs) (c :: cs) :=
        List.Forall₂.cons (s16c1b_codeElem_spec hcA).2 hforall
      have hgsA' : ∀ g ∈ s16c1b_codeElem A c :: gs, g ∈ A := by
        intro g hg
        rcases List.mem_cons.mp hg with hgc | hg
        · rw [hgc]
          exact (s16c1b_codeElem_spec hcA).1
        · exact hgsA g hg
      have hcsA' : ∀ d ∈ c :: cs, ∃ g ∈ A, Coded g d := by
        intro d hd
        rcases List.mem_cons.mp hd with hdc | hd
        · rw [hdc]
          exact ⟨s16c1b_codeElem A c, (s16c1b_codeElem_spec hcA).1,
            (s16c1b_codeElem_spec hcA).2⟩
        · exact hcsA d hd
      have hbound' : ∀ d ∈ c :: cs, ∀ e ∈ L, d ≤ e := by
        intro d hd e he
        rcases List.mem_cons.mp hd with hdc | hd
        · rw [hdc]
          exact (List.sortedLE_cons.mp hsort).1 e he
        · exact hbound d hd e (List.mem_cons_of_mem _ he)
      have hres := ih (c :: cs) (s16c1b_codeElem A c :: gs) hL' hL0' hsort' hreach'
        hforall' hgsA' hcsA' hbound'
      dsimp only [s16c1b_greedyOK]
      rw [hgreedy, if_neg hc]
      refine ⟨hres.1, hres.2.1, hres.2.2.1, ?_, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.mp he with hec | he
        · rw [hec]
          exact List.mem_toFinset.mpr
            (s16c1b_mem_spanC_self (hres.2.2.2.2.1 c List.mem_cons_self) hclt)
        · exact hres.2.2.2.1 e he
      · intro d hd
        exact hres.2.2.2.2.1 d (List.mem_cons_of_mem _ hd)
      · intro g hg
        exact hres.2.2.2.2.2 g (List.mem_cons_of_mem _ hg)

theorem s16c1b_exists_basis {A : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} (hA : A ≤ s16c1b_S₀)
    (hne : A ≠ ⊥)
    (hel : (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a ^ 2 = 1) :
    ∃ xs : List ℕ, s16c1b_Reach xs ∧ xs ≠ [] ∧ s16c1b_SpanCoded A xs := by
  classical
  set L₀ : List ℕ := (s16c1b_S0.filter fun c => ∃ g ∈ A, Coded g c).mergeSort (· ≤ ·) with hL₀
  have hL₀mem : ∀ c ∈ L₀, c ∈ s16c1b_S0.filter (fun c => ∃ g ∈ A, Coded g c) := by
    intro c hc
    rw [hL₀] at hc
    exact (List.mergeSort_perm _ _).mem_iff.mp hc
  have hL : ∀ c ∈ L₀, ∃ g ∈ A, Coded g c :=
    fun c hc => decide_eq_true_eq.mp (List.mem_filter.mp (hL₀mem c hc)).2
  have hL0 : ∀ c ∈ L₀, c ∈ s16c1b_S0 := fun c hc => (List.mem_filter.mp (hL₀mem c hc)).1
  have hsort : L₀.SortedLE := by rw [hL₀]; exact List.sortedLE_mergeSort
  have hres := s16c1b_greedy_spec A hel.2 hel.1 L₀ [] [] hL hL0 hsort s16c1b_Reach.nil
    List.Forall₂.nil (by simp) (by simp) (by simp)
  set xs : List ℕ := (s16c1b_greedy A L₀ [] []).1 with hxs
  set gs : List (V₀ ≃ₗ[ZMod 2] V₀) := (s16c1b_greedy A L₀ [] []).2 with hgs
  have hReach : s16c1b_Reach xs := hres.1
  have hforall : List.Forall₂ Coded gs xs := hres.2.1
  have hgsA : ∀ g ∈ gs, g ∈ A := hres.2.2.1
  have hspanL : ∀ c ∈ L₀, c ∈ spanC xs :=
    fun c hc => List.mem_toFinset.mp (hres.2.2.2.1 c hc)
  have hne_nil : xs ≠ [] := by
    intro hnil
    have hex : ∃ g ∈ A, g ≠ 1 := by
      by_contra h
      apply hne
      exact le_antisymm (fun g hg => by
        rw [Subgroup.mem_bot]
        by_contra hg1
        exact h ⟨g, hg, hg1⟩) bot_le
    obtain ⟨g, hgA, hg1⟩ := hex
    obtain ⟨c, hcS0, hgc⟩ := s16c1b_S₀_spec.2.2.1 g (hA hgA)
    have hcL : c ∈ L₀ := by
      rw [hL₀]
      exact (List.mergeSort_perm _ _).mem_iff.mpr
        (List.mem_filter.mpr ⟨hcS0, decide_eq_true_eq.mpr ⟨g, hgA, hgc⟩⟩)
    have hcspan := hspanL c hcL
    rw [hnil] at hcspan
    simp only [spanC, List.mem_singleton] at hcspan
    exact hg1 ((hgc.eq_iff coded_one).mpr hcspan)
  refine ⟨xs, hReach, hne_nil, ?_⟩
  intro c
  constructor
  · intro hc
    obtain ⟨g, hg, hgc⟩ := s16c1b_forall₂_exists (forall₂_spanG hforall) c hc
    exact ⟨g, spanG_subset (E := A) (fun x hx => hgsA x hx) g hg, hgc⟩
  · rintro ⟨g, hgA, hgc⟩
    obtain ⟨c', hcS0, hgc'⟩ := s16c1b_S₀_spec.2.2.1 g (hA hgA)
    have hc'L : c' ∈ L₀ := by
      rw [hL₀]
      exact (List.mergeSort_perm _ _).mem_iff.mpr
        (List.mem_filter.mpr ⟨hcS0, decide_eq_true_eq.mpr ⟨g, hgA, hgc'⟩⟩)
    have hc'span := hspanL c' hc'L
    rwa [← (hgc.eq_iff hgc').mp rfl] at hc'span

open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code CFSG.LargeExtraspecial.O62.Check

private theorem s16c1b_and_xor (a b c : ℕ) :
    (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

private theorem s16c1b_shiftr_xor (I J : ℕ) :
    (I ^^^ J) >>> 1 = (I >>> 1) ^^^ (J >>> 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_xor]

private theorem s16c1b_mod_two_succ (a : ℕ) : ((a + 1) % 2 == 1) = !(a % 2 == 1) := by
  rw [Nat.add_mod]
  rcases Nat.mod_two_eq_zero_or_one a with h | h <;> rw [h] <;> decide

private theorem s16c1b_par_succ (m I k : ℕ) :
    s16c1b_par m I (k + 1) =
      (s16c1b_par m I k ^^ (I &&& m).testBit k) := by
  unfold s16c1b_par
  rw [List.range_succ, List.filter_append, List.length_append, List.filter_singleton]
  cases hc : (I &&& m).testBit k
  · simp only [hc, Bool.cond_false, List.length_nil, Nat.add_zero, Bool.xor_false]
  · simp only [hc, Bool.cond_true, List.length_cons, List.length_nil, Nat.add_zero,
      Bool.xor_true]
    rw [s16c1b_mod_two_succ]

private theorem s16c1b_par_xor (m I J k : ℕ) :
    s16c1b_par m (I ^^^ J) k = (s16c1b_par m I k ^^ s16c1b_par m J k) := by
  induction k with
  | zero => unfold s16c1b_par; simp
  | succ k ih =>
    rw [s16c1b_par_succ, s16c1b_par_succ, s16c1b_par_succ, ih, s16c1b_and_xor, Nat.testBit_xor]
    cases (s16c1b_par m I k) <;> cases (s16c1b_par m J k) <;>
      cases (I &&& m).testBit k <;> cases (J &&& m).testBit k <;> rfl


private theorem s16c1b_foldl_and_testBit (L : List ℕ) (p : ℕ → Bool) (f : ℕ → ℕ) (w acc : ℕ) :
    (L.foldl (fun acc j => if p j then acc &&& f j else acc) acc).testBit w =
      (acc.testBit w && L.all (fun j => !p j || (f j).testBit w)) := by
  induction L generalizing acc with
  | nil => simp
  | cons I L ih =>
    rw [List.foldl_cons]
    cases hp : p I
    · rw [if_neg (by decide), ih acc]
      simp [List.all_cons, hp]
    · rw [if_pos (by decide), ih (acc &&& f I)]
      simp [List.all_cons, hp, Nat.testBit_and, Bool.and_assoc]

private theorem s16c1b_maskOver_testBit (xs : List ℕ) (p : ℕ → Bool) (w : ℕ) :
    (s16c1b_maskOver xs p).testBit w =
      (decide (w < 64) && (List.range (2 ^ xs.length)).all
        (fun I => !p I || (s16c1b_fixM (s16c1b_prodSub xs I)).testBit w)) := by
  unfold s16c1b_maskOver
  rw [s16c1b_foldl_and_testBit]
  simp only [Nat.testBit_two_pow_sub_one]

private theorem s16c1b_foldl_or_testBit (L : List ℕ) (p : ℕ → Bool) (g : ℕ → ℕ) (w acc : ℕ) :
    (L.foldl (fun acc j => if p j then acc ||| g j else acc) acc).testBit w =
      (acc.testBit w || L.any (fun j => p j && (g j).testBit w)) := by
  induction L generalizing acc with
  | nil => simp
  | cons I L ih =>
    rw [List.foldl_cons]
    cases hp : p I
    · rw [if_neg (by decide), ih acc]
      simp [List.any_cons, hp]
    · rw [if_pos (by decide), ih (acc ||| g I)]
      simp [List.any_cons, hp, Nat.testBit_or, Bool.or_assoc]

private theorem s16c1b_one_shiftl_testBit (I w : ℕ) :
    (1 <<< I).testBit w = decide (w = I) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
  simp [eq_comm]

private theorem s16c1b_any_one_shiftl (p : ℕ → Bool) (w : ℕ) :
    ((List.range 64).any (fun I => p I && (1 <<< I).testBit w)) =
      (decide (w < 64) && p w) := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_range, s16c1b_one_shiftl_testBit, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨I, hI, hpI, hwI⟩
    subst hwI
    exact ⟨hI, hpI⟩
  · rintro ⟨hw, hpw⟩
    exact ⟨w, hw, hpw, rfl⟩

private theorem s16c1b_fixMask_testBit (c w : ℕ) :
    (s16c1b_fixMask c).testBit w = (decide (w < 64) && (act c w == w)) := by
  unfold s16c1b_fixMask
  rw [s16c1b_foldl_or_testBit]
  simp only [Nat.zero_testBit, Bool.false_or, s16c1b_any_one_shiftl]

private theorem s16c1b_vec_inj {a b : ℕ} (ha : a < 64) (hb : b < 64) (h : vec a = vec b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · have h1 := congrFun h ⟨i, hi⟩
    simp only [vec, bitZ] at h1
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · have hai : a < 2 ^ i := by
      calc a < 64 := ha
        _ = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hbi : b < 2 ^ i := by
      calc b < 64 := hb
        _ = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt hai, Nat.testBit_eq_false_of_lt hbi]

private theorem s16c1b_fixM_one : s16c1b_fixM one = 2 ^ 64 - 1 := by
  unfold s16c1b_fixM
  simp

private theorem s16c1b_fixM_of_mem {c : ℕ} (hc : c ∈ s16c1b_S0.filter isInv) :
    s16c1b_fixM c = s16c1b_fixMask c := by
  have hmem : (c, s16c1b_fixMask c) ∈ s16c1b_tab := by
    unfold s16c1b_tab
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  have hsome : ∃ q, s16c1b_tab.find? (fun p => p.1 == c) = some q := by
    by_contra h
    have hn : s16c1b_tab.find? (fun p => p.1 == c) = none := by
      cases hf : s16c1b_tab.find? (fun p => p.1 == c) with
      | none => rfl
      | some q => exact absurd ⟨q, hf⟩ h
    rw [List.find?_eq_none] at hn
    exact hn (c, s16c1b_fixMask c) hmem (by simp)
  obtain ⟨q, hq⟩ := hsome
  have hq1 : q.1 = c := by simpa using List.find?_some hq
  obtain ⟨x, hx, hxq⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hq)
  have hxq' : q = (x, s16c1b_fixMask x) := hxq.symm
  have hx1 : x = c := by
    have := hq1
    rw [hxq'] at this
    exact this
  have hqeq : q = (c, s16c1b_fixMask c) := by rw [hxq', hx1]
  cases hc1 : (c == one)
  · unfold s16c1b_fixM
    simp only [hc1, Bool.cond_false, Bool.false_eq_true, if_false]
    rw [hq, hqeq]
    rfl
  · exact absurd (beq_iff_eq.mp hc1) (by
      obtain ⟨-, hci⟩ := List.mem_filter.mp hc
      simp only [isInv, Bool.and_eq_true, bne_iff_ne] at hci
      exact hci.2)

private theorem s16c1b_act_eq_iff {g : V₀ ≃ₗ[ZMod 2] V₀} {c w : ℕ} (hgc : Coded g c)
    (hw : w < 64) : act c w = w ↔ g (vec w) = vec w := by
  have h1 : vec (act c w) = g (vec w) := by
    rw [vec_act, ← hgc.1, LinearMap.toMatrix'_mulVec]
    rfl
  constructor
  · intro h; rw [← h1, h]
  · intro h
    apply s16c1b_vec_inj (act_lt c w) hw
    rw [h1, h]

private theorem s16c1b_mem_S0_lt {c : ℕ} (hc : c ∈ s16c1b_S0) : c < 2 ^ 36 := by
  obtain ⟨g, -, hgc⟩ := s16c1b_S₀_spec.2.2.2 c hc
  exact hgc.2

private theorem s16c1b_Reach_mem_S0 {xs : List ℕ} (h : s16c1b_Reach xs) :
    ∀ y ∈ xs, y ∈ s16c1b_S0 := by
  induction h with
  | nil => intro y hy; simp at hy
  | @cons xs x _ hx _ ih =>
    intro y hy
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact (List.mem_filter.mp hx).1
    · exact ih y hy

private theorem s16c1b_prodSub_bound {xs : List ℕ} (h : s16c1b_Reach xs) (j : ℕ) :
    xs.getD j 0 < 2 ^ 36 := by
  rcases lt_or_ge j xs.length with hj | hj
  · rw [List.getD_eq_getElem xs 0 hj]
    exact s16c1b_mem_S0_lt (s16c1b_Reach_mem_S0 h _ (List.getElem_mem hj))
  · rw [List.getD_eq_default _ _ hj]
    norm_num

private theorem s16c1b_testBit_two_mul (I j : ℕ) : (2 * I).testBit (j + 1) = I.testBit j := by
  change (2 ^ 1 * I).testBit (j + 1) = I.testBit j
  rw [Nat.testBit_two_pow_mul, decide_eq_true (by omega : j + 1 ≥ (1:ℕ)), Bool.true_and,
    Nat.add_sub_cancel_right]

private theorem s16c1b_testBit_two_mul_zero (I : ℕ) : (2 * I).testBit 0 = false := by
  change (2 ^ 1 * I).testBit 0 = false
  rw [Nat.testBit_two_pow_mul, decide_eq_false (by omega : ¬ (0:ℕ) ≥ 1), Bool.false_and]

private theorem s16c1b_testBit_two_mul_one_zero (I : ℕ) : (2 * I + 1).testBit 0 = true := by
  change (2 ^ 1 * I + 1).testBit 0 = true
  rw [Nat.testBit_two_pow_mul_add I (show (1:ℕ) < 2^1 by norm_num),
    if_pos (by omega : (0:ℕ) < 1), Nat.testBit_one_zero]

private theorem s16c1b_testBit_two_mul_one_succ (I j : ℕ) :
    (2 * I + 1).testBit (j + 1) = I.testBit j := by
  change (2 ^ 1 * I + 1).testBit (j + 1) = I.testBit j
  rw [Nat.testBit_two_pow_mul_add I (show (1:ℕ) < 2^1 by norm_num),
    if_neg (by omega : ¬ (j + 1) < 1), Nat.add_sub_cancel_right]

private theorem s16c1b_shiftr_two_mul (I : ℕ) : (2 * I) >>> 1 = I := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, Nat.add_comm 1 j]
  exact s16c1b_testBit_two_mul I j

private theorem s16c1b_shiftr_two_mul_one (I : ℕ) : (2 * I + 1) >>> 1 = I := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, Nat.add_comm 1 j]
  exact s16c1b_testBit_two_mul_one_succ I j

private theorem s16c1b_foldl_prodSub_lt (L : List ℕ) (xs : List ℕ) (I acc : ℕ)
    (hacc : acc < 2 ^ 36) :
    (L.foldl (fun acc i => if I.testBit i then mul acc (xs.getD i 0) else acc) acc) < 2 ^ 36 := by
  induction L generalizing acc with
  | nil => exact hacc
  | cons i L ih =>
    rw [List.foldl_cons]
    by_cases hb : I.testBit i = true
    · rw [if_pos hb]
      exact ih (mul acc (xs.getD i 0)) (mul_lt acc _)
    · rw [if_neg hb]
      exact ih acc hacc

private theorem s16c1b_prodSub_lt (xs : List ℕ) (I : ℕ) : s16c1b_prodSub xs I < 2 ^ 36 := by
  unfold s16c1b_prodSub
  exact s16c1b_foldl_prodSub_lt (List.range xs.length) xs I one one_lt

private theorem s16c1b_foldl_mul_left (L : List ℕ) (b : ℕ → Bool) (e : ℕ → ℕ)
    (he : ∀ j, e j < 2 ^ 36) (x : ℕ) (hx : x < 2 ^ 36) :
    (L.foldl (fun acc j => if b j then mul acc (e j) else acc) x) =
      mul x (L.foldl (fun acc j => if b j then mul acc (e j) else acc) one) := by
  induction L generalizing x with
  | nil => rw [List.foldl_nil, List.foldl_nil]; exact (s16c1b_mul_one hx).symm
  | cons j L ih =>
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hb : b j = true
    · rw [if_pos hb, if_pos hb]
      rw [ih (mul x (e j)) (mul_lt x (e j)), ih (mul one (e j)) (mul_lt one (e j))]
      rw [s16c1b_one_mul (he j), s16c1b_mul_assoc]
    · rw [if_neg hb, if_neg hb]
      rw [ih x hx]

private theorem s16c1b_prodSub_cons (x : ℕ) (xs : List ℕ) (I : ℕ) (hx : x < 2 ^ 36)
    (hxs : ∀ j, xs.getD j 0 < 2 ^ 36) :
    s16c1b_prodSub (x :: xs) I =
      (if I.testBit 0 then mul x (s16c1b_prodSub xs (I >>> 1))
        else s16c1b_prodSub xs (I >>> 1)) := by
  unfold s16c1b_prodSub
  rw [show (x :: xs).length = xs.length + 1 by simp, List.range_succ_eq_map, List.foldl_cons,
    List.foldl_map]
  have h0 : (if I.testBit 0 then mul one ((x :: xs).getD 0 0) else one) =
      (if I.testBit 0 then x else one) := by
    by_cases hb : I.testBit 0 = true <;> simp [hb, s16c1b_one_mul hx]
  rw [h0]
  have hinner : (fun acc j => if I.testBit (j + 1) then mul acc ((x :: xs).getD (j + 1) 0)
      else acc) = (fun acc j => if (I >>> 1).testBit j then mul acc (xs.getD j 0) else acc) := by
    funext acc j
    simp only [List.getD_cons_succ, Nat.testBit_shiftRight, Nat.add_comm]
  rw [hinner]
  by_cases hb : I.testBit 0 = true
  · rw [if_pos hb, if_pos hb]
    exact s16c1b_foldl_mul_left (List.range xs.length) (fun j => (I >>> 1).testBit j)
      (fun j => xs.getD j 0) hxs x hx
  · rw [if_neg hb, if_neg hb]

private theorem s16c1b_prodSub_nil (I : ℕ) : s16c1b_prodSub [] I = one := by
  unfold s16c1b_prodSub
  rw [List.length_nil, List.range_zero, List.foldl_nil]

private theorem s16c1b_prodSub_mem_spanC {xs : List ℕ} (h : s16c1b_Reach xs) :
    ∀ I, s16c1b_prodSub xs I ∈ spanC xs := by
  induction h with
  | nil =>
    intro I
    rw [s16c1b_prodSub_nil I]
    exact s16c1b_one_mem_spanC []
  | @cons xs x hreach hx hext ih =>
    intro I
    have hxlt : x < 2 ^ 36 := s16c1b_mem_S0_lt (List.mem_filter.mp hx).1
    rw [s16c1b_prodSub_cons x xs I hxlt (s16c1b_prodSub_bound hreach)]
    by_cases hb : I.testBit 0 = true
    · rw [if_pos hb]
      have hcomm : (xs.all fun y => comm x y) = true :=
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hext).1).2
      have hcx : mul x (s16c1b_prodSub xs (I >>> 1)) =
          mul (s16c1b_prodSub xs (I >>> 1)) x := by
        rw [← s16c1b_comm_iff]
        exact s16c1b_comm_spanC (fun y hy => List.all_eq_true.mp hcomm y hy)
          (s16c1b_prodSub xs (I >>> 1)) (ih (I >>> 1))
      rw [hcx]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨s16c1b_prodSub xs (I >>> 1), ih _, rfl⟩)
    · rw [if_neg hb]
      exact List.mem_append_left _ (ih (I >>> 1))

private theorem s16c1b_comm_prodSub {xs : List ℕ} (h : s16c1b_Reach xs) {x : ℕ}
    (hcomm : (xs.all fun y => comm x y) = true) (I : ℕ) :
    mul x (s16c1b_prodSub xs I) = mul (s16c1b_prodSub xs I) x := by
  rw [← s16c1b_comm_iff]
  exact s16c1b_comm_spanC (fun y hy => List.all_eq_true.mp hcomm y hy)
    (s16c1b_prodSub xs I) (s16c1b_prodSub_mem_spanC h I)

private theorem s16c1b_mul_mul_x_eq {x P Q : ℕ} (hQ : mul x Q = mul Q x)
    (hPQ : mul x (mul P Q) = mul (mul P Q) x) :
    mul P (mul x Q) = mul x (mul P Q) := by
  calc mul P (mul x Q) = mul P (mul Q x) := by rw [hQ]
    _ = mul (mul P Q) x := by rw [← s16c1b_mul_assoc]
    _ = mul x (mul P Q) := hPQ.symm

private theorem s16c1b_mul_xx_yy {x P Q : ℕ} (hx : mul x x = one)
    (hQ : mul x Q = mul Q x) (hPQ : mul x (mul P Q) = mul (mul P Q) x) :
    mul (mul x P) (mul x Q) = mul P Q := by
  rw [s16c1b_mul_assoc x P (mul x Q), s16c1b_mul_mul_x_eq hQ hPQ,
    ← s16c1b_mul_assoc x x (mul P Q), hx, s16c1b_one_mul (mul_lt P Q)]

private theorem s16c1b_prodSub_mul {xs : List ℕ} (h : s16c1b_Reach xs) :
    ∀ I J, mul (s16c1b_prodSub xs I) (s16c1b_prodSub xs J) = s16c1b_prodSub xs (I ^^^ J) := by
  induction h with
  | nil =>
    intro I J
    rw [s16c1b_prodSub_nil I, s16c1b_prodSub_nil J, s16c1b_prodSub_nil (I ^^^ J),
      s16c1b_mul_one one_lt]
  | @cons xs x hreach hx hext ih =>
    intro I J
    have hxlt : x < 2 ^ 36 := s16c1b_mem_S0_lt (List.mem_filter.mp hx).1
    have hxsb := s16c1b_prodSub_bound hreach
    have hxinv : mul x x = one := by
      obtain ⟨-, hxi⟩ := List.mem_filter.mp hx
      simp only [isInv, Bool.and_eq_true] at hxi
      exact beq_iff_eq.mp hxi.1
    have hcommall : (xs.all fun y => comm x y) = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hext).1).2
    have hcommP : ∀ K, mul x (s16c1b_prodSub xs K) = mul (s16c1b_prodSub xs K) x :=
      fun K => s16c1b_comm_prodSub hreach hcommall K
    rw [s16c1b_prodSub_cons x xs I hxlt hxsb, s16c1b_prodSub_cons x xs J hxlt hxsb,
      s16c1b_prodSub_cons x xs (I ^^^ J) hxlt hxsb, s16c1b_shiftr_xor, Nat.testBit_xor,
      ← ih (I >>> 1) (J >>> 1)]
    cases hI : I.testBit 0 <;> cases hJ : J.testBit 0 <;>
      simp only [Bool.false_xor, Bool.xor_false, Bool.true_xor, Bool.xor_true, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, reduceIte]
    all_goals
      first
      | rfl
      | rw [s16c1b_mul_xx_yy hxinv (hcommP (J >>> 1))
          (by rw [ih (I >>> 1) (J >>> 1)]; exact hcommP ((I >>> 1) ^^^ (J >>> 1)))]
      | rw [s16c1b_mul_mul_x_eq (hcommP (J >>> 1))
          (by rw [ih (I >>> 1) (J >>> 1)]; exact hcommP ((I >>> 1) ^^^ (J >>> 1)))]
      | rw [s16c1b_mul_assoc]

private theorem s16c1b_prodSub_surj {xs : List ℕ} (h : s16c1b_Reach xs) :
    ∀ c ∈ spanC xs, ∃ I, I < 2 ^ xs.length ∧ s16c1b_prodSub xs I = c := by
  induction h with
  | nil =>
    intro c hc
    simp only [spanC, List.mem_singleton] at hc
    exact ⟨0, by simp, by rw [hc]; exact s16c1b_prodSub_nil 0⟩
  | @cons xs x hreach hx hext ih =>
    intro c hc
    have hxlt : x < 2 ^ 36 := s16c1b_mem_S0_lt (List.mem_filter.mp hx).1
    have hxsb := s16c1b_prodSub_bound hreach
    rw [spanC_cons] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨I', hI'lt, hI'eq⟩ := ih c hc
      refine ⟨2 * I', ?_, ?_⟩
      · rw [show (x :: xs).length = xs.length + 1 by simp, Nat.pow_succ']
        exact Nat.mul_lt_mul_of_pos_left hI'lt (by norm_num)
      · rw [s16c1b_prodSub_cons x xs (2 * I') hxlt hxsb,
          if_neg (by rw [s16c1b_testBit_two_mul_zero]; decide), s16c1b_shiftr_two_mul, hI'eq]
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      obtain ⟨I', hI'lt, hI'eq⟩ := ih c' hc'
      have hxcomm : mul x c' = mul c' x := by
        rw [← s16c1b_comm_iff]
        exact s16c1b_comm_spanC
          (fun y hy => List.all_eq_true.mp
            ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hext).1).2) y hy) c' hc'
      refine ⟨2 * I' + 1, ?_, ?_⟩
      · rw [show (x :: xs).length = xs.length + 1 by simp, Nat.pow_succ']
        have h1 : 2 * I' < 2 * 2 ^ xs.length :=
          Nat.mul_lt_mul_of_pos_left hI'lt (by norm_num)
        omega
      · rw [s16c1b_prodSub_cons x xs (2 * I' + 1) hxlt hxsb,
          if_pos (s16c1b_testBit_two_mul_one_zero I'), s16c1b_shiftr_two_mul_one, hI'eq, hxcomm]


private theorem s16c1b_prodSub_zero (xs : List ℕ) : s16c1b_prodSub xs 0 = one := by
  have h : ∀ L : List ℕ,
      L.foldl (fun acc i => if (0 : ℕ).testBit i then mul acc (xs.getD i 0) else acc) one =
        one := by
    intro L
    induction L with
    | nil => rw [List.foldl_nil]
    | cons i L ih =>
      rw [List.foldl_cons, if_neg (by rw [Nat.zero_testBit]; decide), ih]
  unfold s16c1b_prodSub
  exact h (List.range xs.length)

private theorem s16c1b_or_not_iff (a b : Bool) : (!a || b) = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp

private theorem s16c1b_fixM_testBit_of_coded {g : V₀ ≃ₗ[ZMod 2] V₀} {c w : ℕ}
    (hgc : Coded g c) (hcS0 : c ∈ s16c1b_S0) (hinv : mul c c = one) (hw : w < 64) :
    (s16c1b_fixM c).testBit w = true ↔ g (vec w) = vec w := by
  by_cases hc : c = one
  · subst hc
    have hg1 : g = 1 := (hgc.eq_iff coded_one).mpr rfl
    have hb : (2 ^ 64 - 1 : ℕ).testBit w = true := by
      rw [Nat.testBit_two_pow_sub_one]; simp [hw]
    rw [s16c1b_fixM_one, hg1]
    exact ⟨fun _ => rfl, fun _ => hb⟩
  · have hmem : c ∈ s16c1b_S0.filter isInv := by
      rw [List.mem_filter]
      exact ⟨hcS0, by simp [isInv, hinv, hc]⟩
    rw [s16c1b_fixM_of_mem hmem, s16c1b_fixMask_testBit,
      show decide (w < 64) = true from by simp [hw], Bool.true_and, beq_iff_eq]
    exact s16c1b_act_eq_iff hgc hw

theorem s16c1b_a2Prop_of_fix {A : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {xs : List ℕ} (hA : A ≤ s16c1b_S₀)
    (hxs : s16c1b_Reach xs) (hspan : s16c1b_SpanCoded A xs)
    (hfix : ∀ B : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), B ≤ A → E3.mQuot A B < 2 →
      fixV (B.map s16c1b_κ) = fixV (A.map s16c1b_κ)) :
    s16c1b_a2Prop xs = true := by
  classical
  let gI : ℕ → V₀ ≃ₗ[ZMod 2] V₀ := fun I =>
    Classical.choose ((hspan (s16c1b_prodSub xs I)).mp (s16c1b_prodSub_mem_spanC hxs I))
  have hGI : ∀ I, Coded (gI I) (s16c1b_prodSub xs I) := fun I =>
    (Classical.choose_spec ((hspan (s16c1b_prodSub xs I)).mp (s16c1b_prodSub_mem_spanC hxs I))).2
  have hgIA : ∀ I, gI I ∈ A := fun I =>
    (Classical.choose_spec ((hspan (s16c1b_prodSub xs I)).mp (s16c1b_prodSub_mem_spanC hxs I))).1
  have hgI_mul : ∀ I J, gI (I ^^^ J) = gI I * gI J := by
    intro I J
    exact ((hGI (I ^^^ J)).eq_iff ((hGI I).mul (hGI J))).mpr
      (s16c1b_prodSub_mul hxs I J).symm
  have hgI_zero : gI 0 = 1 := by
    have h1 : Coded (gI 0) one := by rw [← s16c1b_prodSub_zero xs]; exact hGI 0
    exact (h1.eq_iff coded_one).mpr rfl
  have hgI_inv : ∀ I, gI I * gI I = 1 := by
    intro I
    rw [← hgI_mul I I, Nat.xor_self, hgI_zero]
  have hcS0 : ∀ I, s16c1b_prodSub xs I ∈ s16c1b_S0 := by
    intro I
    obtain ⟨d, hd, hgd⟩ := s16c1b_S₀_spec.2.2.1 (gI I) (hA (hgIA I))
    have hcd : s16c1b_prodSub xs I = d := ((hGI I).eq_iff hgd).mp rfl
    rwa [hcd]
  have hinvC : ∀ I, mul (s16c1b_prodSub xs I) (s16c1b_prodSub xs I) = one := by
    intro I
    exact (((hGI I).mul (hGI I)).eq_iff coded_one).mp (hgI_inv I)
  have hmask : ∀ (p : ℕ → Bool) {w : ℕ}, w < 64 →
      ((s16c1b_maskOver xs p).testBit w = true ↔
        ∀ I ∈ List.range (2 ^ xs.length), p I = true → gI I (vec w) = vec w) := by
    intro p w hw
    rw [s16c1b_maskOver_testBit]
    have hd : decide (w < 64) = true := by simp [hw]
    rw [hd, Bool.true_and, List.all_eq_true]
    constructor
    · intro h I hI hp
      exact (s16c1b_fixM_testBit_of_coded (hGI I) (hcS0 I) (hinvC I) hw).mp
        ((s16c1b_or_not_iff (p I) _).mp (h I hI) hp)
    · intro h I hI
      exact (s16c1b_or_not_iff (p I) _).mpr fun hp =>
        (s16c1b_fixM_testBit_of_coded (hGI I) (hcS0 I) (hinvC I) hw).mpr (h I hI hp)
  have hAeq : ∀ g, g ∈ A ↔ ∃ I ∈ List.range (2 ^ xs.length), g = gI I := by
    intro g
    constructor
    · intro hg
      obtain ⟨c, hcS0', hgc⟩ := s16c1b_S₀_spec.2.2.1 g (hA hg)
      have hcspan : c ∈ spanC xs := (hspan c).mpr ⟨g, hg, hgc⟩
      obtain ⟨I, hIlt, hIeq⟩ := s16c1b_prodSub_surj hxs c hcspan
      exact ⟨I, List.mem_range.mpr hIlt, (hgc.eq_iff (hGI I)).mpr hIeq.symm⟩
    · rintro ⟨I, -, rfl⟩
      exact hgIA I
  rw [s16c1b_a2Prop, List.all_eq_true]
  intro m hm
  by_cases hm0 : m = 0
  · subst hm0
    rfl
  · have hmk : m < 2 ^ xs.length := List.mem_range.mp hm
    have hm0b : (m == 0) = false := by
      cases h : (m == 0)
      · rfl
      · exact absurd (beq_iff_eq.mp h) hm0
    rw [hm0b, Bool.false_or, beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro w
    by_cases hw : w < 64
    · have hfixA : (s16c1b_maskOver xs (fun _ => true)).testBit w = true ↔
          Multiplicative.ofAdd (vec w) ∈ fixV (A.map s16c1b_κ) := by
        rw [hmask (fun _ => true) hw]
        constructor
        · intro h
          rw [mem_fixV]
          rintro x hx
          obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
          refine congrArg Multiplicative.ofAdd ?_
          obtain ⟨I, hI, rfl⟩ := (hAeq g).mp hg
          exact h I hI rfl
        · intro h I hI _
          have hx : s16c1b_κ (gI I) ∈ A.map s16c1b_κ :=
            Subgroup.mem_map.mpr ⟨gI I, hgIA I, rfl⟩
          have h1 := (mem_fixV.mp h) (s16c1b_κ (gI I)) hx
          exact Multiplicative.ofAdd.injective h1
      let S' : Set (V₀ ≃ₗ[ZMod 2] V₀) :=
        {g | ∃ I ∈ List.range (2 ^ xs.length), s16c1b_par m I xs.length = false ∧ g = gI I}
      let Bm : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) := Subgroup.closure S'
      have hBmA : Bm ≤ A := by
        change Subgroup.closure S' ≤ A
        rw [Subgroup.closure_le]
        rintro g ⟨I, -, hpar, rfl⟩
        exact hgIA I
      have hfixB : (s16c1b_maskOver xs (fun I => !s16c1b_par m I xs.length)).testBit w = true ↔
          Multiplicative.ofAdd (vec w) ∈ fixV (Bm.map s16c1b_κ) := by
        rw [hmask (fun I => !s16c1b_par m I xs.length) hw]
        constructor
        · intro h
          rw [mem_fixV]
          rintro x hx
          obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
          refine congrArg Multiplicative.ofAdd ?_
          have hle : Bm ≤ MulAction.stabilizer (V₀ ≃ₗ[ZMod 2] V₀) (vec w) := by
              change Subgroup.closure S' ≤ MulAction.stabilizer (V₀ ≃ₗ[ZMod 2] V₀) (vec w)
              rw [Subgroup.closure_le]
              rintro g' ⟨I, hI, hpar, rfl⟩
              exact MulAction.mem_stabilizer_iff.mpr (h I hI (by rw [hpar]; rfl))
          exact MulAction.mem_stabilizer_iff.mp (hle hg)
        · intro h I hI hpar'
          have hpar : s16c1b_par m I xs.length = false := by
            simpa [Bool.not_eq_true] using hpar'
          have hx : s16c1b_κ (gI I) ∈ Bm.map s16c1b_κ :=
            Subgroup.mem_map.mpr ⟨gI I, Subgroup.subset_closure ⟨I, hI, hpar, rfl⟩, rfl⟩
          have h1 := (mem_fixV.mp h) (s16c1b_κ (gI I)) hx
          exact Multiplicative.ofAdd.injective h1
      have hmq : E3.mQuot A Bm < 2 := by
        by_cases hpar : ∃ I ∈ List.range (2 ^ xs.length), s16c1b_par m I xs.length = true
        · obtain ⟨I0, hI0, hpar0⟩ := hpar
          have hI0lt : I0 < 2 ^ xs.length := List.mem_range.mp hI0
          have hg0comm : ∀ h ∈ Bm, gI I0 * h = h * gI I0 := by
            have hle : Bm ≤ Subgroup.centralizer ({gI I0} : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
              change Subgroup.closure S' ≤ Subgroup.centralizer ({gI I0} : Set (V₀ ≃ₗ[ZMod 2] V₀))
              rw [Subgroup.closure_le]
              rintro g' ⟨I, -, hparI, rfl⟩
              change gI I ∈ Subgroup.centralizer ({gI I0} : Set (V₀ ≃ₗ[ZMod 2] V₀))
              rw [Subgroup.mem_centralizer_iff]
              intro y hy
              rw [Set.mem_singleton_iff] at hy
              subst hy
              rw [← hgI_mul I0 I, ← hgI_mul I I0, Nat.xor_comm]
            intro h hh
            exact (Subgroup.mem_centralizer_iff.mp (hle hh)) (gI I0) (Set.mem_singleton (gI I0))
          have hunion : (A : Set (V₀ ≃ₗ[ZMod 2] V₀)) ⊆
              (Bm : Set (V₀ ≃ₗ[ZMod 2] V₀)) ∪
                (Bm : Set (V₀ ≃ₗ[ZMod 2] V₀)) * ({gI I0} : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
            intro g hg
            obtain ⟨I, hI, rfl⟩ := (hAeq g).mp hg
            have hIlt : I < 2 ^ xs.length := List.mem_range.mp hI
            cases hparI : s16c1b_par m I xs.length
            · exact Or.inl (Subgroup.subset_closure ⟨I, hI, hparI, rfl⟩)
            · have hI' : s16c1b_par m (I ^^^ I0) xs.length = false := by
                rw [s16c1b_par_xor, hparI, hpar0]; rfl
              have hmem : gI (I ^^^ I0) ∈ Bm :=
                Subgroup.subset_closure ⟨I ^^^ I0,
                  List.mem_range.mpr (Nat.xor_lt_two_pow hIlt hI0lt), hI', rfl⟩
              have heq : gI I = gI (I ^^^ I0) * gI I0 := by
                change gI I = gI (I ^^^ I0) * gI I0
                rw [hgI_mul I I0, mul_assoc, hgI_inv I0, mul_one]
              rw [heq]
              exact Or.inr ⟨gI (I ^^^ I0), hmem, gI I0, rfl, rfl⟩
          by_cases hg0B : gI I0 ∈ Bm
          · have hAB : A = Bm := by
              apply le_antisymm _ hBmA
              intro g hg
              rcases hunion hg with hgB | hgB
              · exact hgB
              · obtain ⟨b1, hb1, c, hc, hbc⟩ := hgB
                rw [Set.mem_singleton_iff] at hc
                subst hc
                rw [← hbc]
                exact Bm.mul_mem hb1 hg0B
            rw [E3.mQuot, hAB, Subgroup.relIndex_self]
            simp
          · have hrel : Bm.relIndex A = 2 := by
              rw [Subgroup.relIndex_eq_two_iff']
              refine ⟨gI I0, hgIA I0, ?_⟩
              intro b hb
              rcases hunion hb with hbB | hbB
              · refine Or.inr ⟨hbB, ?_⟩
                intro hgb
                apply hg0B
                have h2 : (gI I0 * b) * b⁻¹ ∈ Bm := Bm.mul_mem hgb (Bm.inv_mem hbB)
                rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
              · obtain ⟨b1, hb1, c, hc, hbc⟩ := hbB
                rw [Set.mem_singleton_iff] at hc
                subst hc
                refine Or.inl ⟨?_, ?_⟩
                · rw [← hbc, ← mul_assoc, hg0comm b1 hb1, mul_assoc, hgI_inv I0, mul_one]
                  exact hb1
                · intro hb'
                  apply hg0B
                  have h2 : b1⁻¹ * b ∈ Bm := Bm.mul_mem (Bm.inv_mem hb1) hb'
                  rwa [← hbc, ← mul_assoc, inv_mul_cancel, one_mul] at h2
            rw [E3.mQuot, hrel]
            norm_num
        · have hAB : A ≤ Bm := by
            intro g hg
            obtain ⟨I, hI, rfl⟩ := (hAeq g).mp hg
            have hparI : s16c1b_par m I xs.length = false := by
              cases h : s16c1b_par m I xs.length
              · rfl
              · exact absurd ⟨I, hI, h⟩ hpar
            exact Subgroup.subset_closure ⟨I, hI, hparI, rfl⟩
          have hAB' : A = Bm := le_antisymm hAB hBmA
          rw [E3.mQuot, hAB', Subgroup.relIndex_self]
          simp
      have hfixm := hfix Bm hBmA hmq
      rw [Bool.eq_iff_iff, hfixB, hfixA, hfixm]
    · rw [s16c1b_maskOver_testBit, s16c1b_maskOver_testBit]
      have hwf : decide (w < 64) = false := by simp [hw]
      rw [hwf, Bool.false_and, Bool.false_and]
theorem s16c1b_classify {A : Subgroup (MulAut (Multiplicative V₀))}
    (hA : A ∈ E3.aSet 2 s16c1b_ΩM) (hAS : A ≤ s16c1b_SM) :
    ∃ i : Fin 3, A = (s16c1b_Asub i).map s16c1b_κ := by
  set A' : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) := A.comap s16c1b_κ ⊓ s16c1b_S₀ with hA'
  have hA'S : A' ≤ s16c1b_S₀ := inf_le_right
  have hAmap : A'.map s16c1b_κ = A := by
    apply le_antisymm
    · rintro x ⟨g, hg, rfl⟩
      exact (Subgroup.mem_inf.mp hg).1
    · intro a ha
      obtain ⟨g, hg, hga⟩ := Subgroup.mem_map.mp (hAS ha)
      refine ⟨g, Subgroup.mem_inf.mpr ⟨?_, hg⟩, hga⟩
      show s16c1b_κ g ∈ A
      rw [hga]
      exact ha
  have hne : A' ≠ ⊥ := by
    intro hbot
    apply hA.2.1
    rw [← hAmap, hbot, Subgroup.map_bot]
    rfl
  have hel : (∀ a ∈ A', ∀ b ∈ A', a * b = b * a) ∧ ∀ a ∈ A', a ^ 2 = 1 := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb
      have hac : s16c1b_κ a ∈ A := (Subgroup.mem_inf.mp ha).1
      have hbc : s16c1b_κ b ∈ A := (Subgroup.mem_inf.mp hb).1
      apply s16c1b_κ_injective
      change s16c1b_κ (a * b) = s16c1b_κ (b * a)
      rw [map_mul, map_mul]
      exact hA.2.2.1.1 (s16c1b_κ a) hac (s16c1b_κ b) hbc
    · intro a ha
      have hac : s16c1b_κ a ∈ A := (Subgroup.mem_inf.mp ha).1
      apply s16c1b_κ_injective
      change s16c1b_κ (a ^ 2) = s16c1b_κ 1
      rw [map_pow, map_one]
      exact hA.2.2.1.2 (s16c1b_κ a) hac
  have hfix : ∀ B : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), B ≤ A' → E3.mQuot A' B < 2 →
      fixV (B.map s16c1b_κ) = fixV (A'.map s16c1b_κ) := by
    intro B hB hquot
    have hBmap : B.map s16c1b_κ ≤ A := by rw [← hAmap]; exact Subgroup.map_mono hB
    have hrel : (B.map s16c1b_κ).relIndex (A'.map s16c1b_κ) = B.relIndex A' :=
      Subgroup.relIndex_map_map_of_injective B A' s16c1b_κ_injective
    have hmq : E3.mQuot A (B.map s16c1b_κ) < 2 := by
      rw [← hAmap]
      show E3.mQuot (A'.map s16c1b_κ) (B.map s16c1b_κ) < 2
      simpa [E3.mQuot, hrel] using hquot
    have h := hA.2.2.2 (B.map s16c1b_κ) hBmap hmq
    rw [← hAmap] at h
    exact h
  obtain ⟨xs, hxs, hxsne, hspan⟩ := s16c1b_exists_basis hA'S hne hel
  have ha2 : s16c1b_a2Prop xs = true := s16c1b_a2Prop_of_fix hA'S hxs hspan hfix
  have hinA : s16c1b_inA (spanC xs) = true := by
    have hnt := (s16c1b_reach_spec hxs).1
    have hempty : xs.isEmpty = false := by
      cases xs with
      | nil => exact absurd rfl hxsne
      | cons _ _ => rfl
    rw [hempty, ha2] at hnt
    simpa using hnt
  obtain ⟨i, hi⟩ := s16c1b_eq_Asub_of_inA hspan hinA
  exact ⟨i, by rw [← hAmap, hi]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

