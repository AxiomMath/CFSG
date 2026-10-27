module

public import CFSG.LocalAnalysis.StandardType.GGDepASmall

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private instance l05nPCFactFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private lemma l05nPC_form_apply {p N : ℕ} (f v : GGDepAE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot]

private lemma l05nPC_refl_apply {p N : ℕ} (c f v : GGDepAE p N) :
    ggDepARefl c f v = v - ggDepAdot f v • c := by
  simp [ggDepARefl, l05nPC_form_apply]

private lemma l05nPC_dot_sub {p N : ℕ} (a v w : GGDepAE p N) :
    ggDepAdot a (v - w) = ggDepAdot a v - ggDepAdot a w := by
  rw [← l05nPC_form_apply a (v - w), map_sub, l05nPC_form_apply a v, l05nPC_form_apply a w]

private lemma l05nPC_dot_add {p N : ℕ} (a v w : GGDepAE p N) :
    ggDepAdot a (v + w) = ggDepAdot a v + ggDepAdot a w := by
  rw [← l05nPC_form_apply a (v + w), map_add, l05nPC_form_apply a v, l05nPC_form_apply a w]

private lemma l05nPC_dot_smul {p N : ℕ} (a : GGDepAE p N) (k : ZMod p) (v : GGDepAE p N) :
    ggDepAdot a (k • v) = k * ggDepAdot a v := by
  rw [← l05nPC_form_apply a (k • v), map_smul, l05nPC_form_apply a v]
  simp

private lemma l05nPC_dot_sub_left {p N : ℕ} (a b v : GGDepAE p N) :
    ggDepAdot (a - b) v = ggDepAdot a v - ggDepAdot b v := by
  simp only [ggDepAdot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma l05nPC_dot_smul_left {p N : ℕ} (k : ZMod p) (a v : GGDepAE p N) :
    ggDepAdot (k • a) v = k * ggDepAdot a v := by
  simp only [ggDepAdot, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]

private lemma l05nPC_refl_invol {p N : ℕ} (c f : GGDepAE p N) (h : ggDepAdot f c = 2) :
    ggDepARefl c f * ggDepARefl c f = 1 := by
  apply LinearMap.ext; intro v
  ext j
  have hone : (1 : Module.End (ZMod p) (GGDepAE p N)) v = v := rfl
  simp only [Module.End.mul_apply, l05nPC_refl_apply, Pi.sub_apply, Pi.smul_apply,
    l05nPC_dot_sub, l05nPC_dot_smul, h]
  rw [hone]
  ring

private lemma l05nPC_refl_conj {p N : ℕ} (c f gc gf : GGDepAE p N)
    (h : ggDepAdot gf gc = 2) :
    ggDepARefl gc gf * ggDepARefl c f * ggDepARefl gc gf =
      ggDepARefl (c - ggDepAdot gf c • gc) (f - ggDepAdot f gc • gf) := by
  apply LinearMap.ext; intro v
  ext j
  simp only [Module.End.mul_apply, l05nPC_refl_apply, Pi.sub_apply, Pi.smul_apply,
    l05nPC_dot_sub, l05nPC_dot_smul, l05nPC_dot_sub_left, l05nPC_dot_smul_left, h]
  ring

private lemma l05nPC_form_ne_zero {p N : ℕ} (f : GGDepAE p N) (hf : f ≠ 0) :
    ggDepAform f ≠ 0 := by
  intro h
  apply hf
  ext j
  have h1 := congrArg (fun g : GGDepAE p N →ₗ[ZMod p] ZMod p => g (Pi.single j 1)) h
  rw [l05nPC_form_apply] at h1
  have h2 : ggDepAdot f (Pi.single j 1) = f j := by
    rw [ggDepAdot, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [h2] at h1
  simpa using h1

private lemma l05nPC_range_smulRight {p N : ℕ} [Fact p.Prime] (d f : GGDepAE p N)
    (hf : ggDepAform f ≠ 0) :
    LinearMap.range ((ggDepAform f).smulRight d) = Submodule.span (ZMod p) {d} := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    have hex : ∃ v, ggDepAform f v ≠ 0 := by
      by_contra hcon
      exact hf (LinearMap.ext fun v => not_not.mp (not_exists.mp hcon v))
    obtain ⟨v, hv⟩ := hex
    refine ⟨(ggDepAform f v)⁻¹ • v, ?_⟩
    rw [LinearMap.smulRight_apply, map_smul, smul_eq_mul, inv_mul_cancel₀ hv, one_smul]

private lemma l05nPC_isTv_one_add {p N : ℕ} [Fact p.Prime] (d f : GGDepAE p N)
    (hfd : ggDepAdot f d = 0) (hd : d ≠ 0) (hf : f ≠ 0) :
    GGDepAIsTv (1 + (ggDepAform f).smulRight d) := by
  constructor
  · have hsub : (1 + (ggDepAform f).smulRight d) - LinearMap.id =
        (ggDepAform f).smulRight d := by
      ext v; simp
    rw [hsub, l05nPC_range_smulRight d f (l05nPC_form_ne_zero f hf)]
    exact finrank_span_singleton hd
  · intro w
    have hg : ∀ x, (1 + (ggDepAform f).smulRight d) x = x + ggDepAdot f x • d := by
      intro x; simp [l05nPC_form_apply]
    rw [hg, hg]
    simp only [l05nPC_dot_add, l05nPC_dot_sub, l05nPC_dot_smul, hfd, mul_zero, zero_smul,
      add_zero, add_sub_cancel_left]

private lemma l05nPC_refl_mul_same {p N : ℕ} (c f1 f2 : GGDepAE p N)
    (h1 : ggDepAdot f1 c = 2) (h2 : ggDepAdot f2 c = 2) :
    ggDepARefl c f1 * ggDepARefl c f2 =
      1 + (ggDepAform (f2 - f1)).smulRight c := by
  apply LinearMap.ext; intro v
  ext j
  have hone : (1 : Module.End (ZMod p) (GGDepAE p N)) v = v := rfl
  simp only [Module.End.mul_apply, l05nPC_refl_apply, LinearMap.add_apply,
    LinearMap.smulRight_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    l05nPC_dot_sub, l05nPC_dot_smul, l05nPC_dot_sub_left, l05nPC_form_apply, h1, h2]
  rw [hone]
  ring

private lemma l05nPC_refl_mul_prop {p N : ℕ} [Fact p.Prime] (c1 c2 f1 f2 : GGDepAE p N)
    (k : ZMod p) (h1 : ggDepAdot f1 c1 = 2) (hf : f2 = k • f1) (hk0 : k ≠ 0)
    (hk : ggDepAdot f1 c2 = k⁻¹ * 2) :
    ggDepARefl c1 f1 * ggDepARefl c2 f2 =
      1 + (ggDepAform f1).smulRight (c1 - k • c2) := by
  subst hf
  apply LinearMap.ext; intro v
  ext j
  have hone : (1 : Module.End (ZMod p) (GGDepAE p N)) v = v := rfl
  simp only [Module.End.mul_apply, l05nPC_refl_apply, LinearMap.add_apply,
    LinearMap.smulRight_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    l05nPC_dot_sub, l05nPC_dot_smul, l05nPC_dot_smul_left, l05nPC_dot_sub_left,
    l05nPC_form_apply, h1]
  rw [hone, hk]
  field_simp
  ring

private structure l05nPCWit where
  g1 : Fin 5
  w1 : List (Fin 5)
  g2 : Fin 5
  w2 : List (Fin 5)

private def l05nPCdot (a v : GGDepAE 5 5) : ZMod 5 :=
  a 0 * v 0 + a 1 * v 1 + a 2 * v 2 + a 3 * v 3 + a 4 * v 4

private lemma l05nPCdot_eq (a v : GGDepAE 5 5) : l05nPCdot a v = ggDepAdot a v := by
  simp [l05nPCdot, ggDepAdot, Fin.sum_univ_five]

private def l05nPChTab : Fin 4 → GGDepAE 5 5 :=
  ![![1, 4, 0, 0, 0], ![0, 1, 4, 0, 0], ![0, 0, 1, 4, 0], ![1, 1, 1, 2, 0]]

private def l05nPCaTab : Fin 4 → GGDepAE 5 5 :=
  ![![1, 4, 0, 0, 0], ![0, 1, 4, 0, 0], ![0, 0, 1, 4, 0], ![0, 0, 0, 1, 0]]

private lemma l05nPChTab_eq (i : Fin 4) : l05nPChTab i = ggDepAh 5 5 i := by
  fin_cases i <;> decide +kernel

private lemma l05nPCaTab_eq (i : Fin 4) : l05nPCaTab i = ggDepAα 5 5 i := by
  fin_cases i <;> decide +kernel

private def l05nPCxTab : GGDepAE 5 5 := ![0, 0, 0, 0, 1]

private lemma l05nPCxTab_eq : l05nPCxTab = ggDepAx 5 5 := by decide +kernel

private def l05nPCcvals : List (Fin 4) := [0, 1, 2, 3]

private lemma l05nPCmem_cvals : ∀ c : Fin 4, c ∈ l05nPCcvals := by decide +kernel

private def l05nPCgenPair (ha aa : GGDepAE 5 5) (i : Fin 5) :
    GGDepAE 5 5 × GGDepAE 5 5 :=
  if h : i.val < 4 then (ggDepAh 5 5 ⟨i.val, h⟩, ggDepAα 5 5 ⟨i.val, h⟩) else (ha, aa)

private def l05nPCpairConj (p gp : GGDepAE 5 5 × GGDepAE 5 5) :
    GGDepAE 5 5 × GGDepAE 5 5 :=
  (p.1 - l05nPCdot gp.2 p.1 • gp.1, p.2 - l05nPCdot p.2 gp.1 • gp.2)

private def l05nPCpairWord (p : GGDepAE 5 5 × GGDepAE 5 5) (w : List (Fin 5))
    (pairs : Fin 5 → GGDepAE 5 5 × GGDepAE 5 5) : GGDepAE 5 5 × GGDepAE 5 5 :=
  w.foldr (fun g acc => l05nPCpairConj acc (pairs g)) p

private def l05nPCfirstNZ (c : GGDepAE 5 5) : Option (Fin 5) :=
  (List.finRange 5).find? (fun j => c j != 0)

private def l05nPCnormalize (p : GGDepAE 5 5 × GGDepAE 5 5) :
    GGDepAE 5 5 × GGDepAE 5 5 :=
  match l05nPCfirstNZ p.1 with
  | none => p
  | some j => ((p.1 j)⁻¹ • p.1, (p.1 j) • p.2)

private def l05nPCprop (f1 f2 : GGDepAE 5 5) : Option (ZMod 5) :=
  match l05nPCfirstNZ f1 with
  | none => none
  | some j =>
      if (List.finRange 5).all (fun i => (f2 j * (f1 j)⁻¹) * f1 i == f2 i) then
        some (f2 j * (f1 j)⁻¹)
      else none

private def l05nPCtestPairN (q1 q2 : GGDepAE 5 5 × GGDepAE 5 5) : Bool :=
  (q1.1 == q2.1 && q1.2 != q2.2) ||
    match l05nPCprop q1.2 q2.2 with
    | some k => (k != 0) && (k⁻¹ • q1.1 != q2.1)
    | none => false

private def l05nPCtestPair (p1 p2 : GGDepAE 5 5 × GGDepAE 5 5) : Bool :=
  l05nPCtestPairN (l05nPCnormalize p1) (l05nPCnormalize p2)

private def l05nPCwitTest (w : l05nPCWit) (ha aa : GGDepAE 5 5) : Bool :=
  let pairs := l05nPCgenPair ha aa
  l05nPCtestPair (l05nPCpairWord (pairs w.g1) w.w1 pairs)
    (l05nPCpairWord (pairs w.g2) w.w2 pairs)

private def l05nPCztoint (m : ZMod 5) : ℤ := if m = 4 then -1 else if m = 3 then -2 else 0

private instance l05nPCDecPat (N : ℕ) (b c0 : Fin (N - 1)) (m n : ℤ) :
    Decidable (GGDepAPat N b c0 m n) := by
  unfold GGDepAPat
  infer_instance

private def l05nPCpatB (b c0 : Fin 4) (m n : ZMod 5) : Bool :=
  decide (GGDepAPat 5 b c0 (l05nPCztoint m) (l05nPCztoint n))

private def l05nPCwitList (b c0 : Fin 4) (m n : ZMod 5) : List l05nPCWit :=
  match b.val, c0.val, m.val, n.val with
  | 0, 1, 3, 4 => [⟨0, [4, 1], 0, [1]⟩, ⟨0, [4, 3, 2, 1], 1, [0, 1, 4, 2]⟩, ⟨0, [1, 4], 0, [4]⟩,
      ⟨0, [2, 1, 4, 3, 2, 1], 1, [4, 1, 0, 4, 3, 2]⟩, ⟨0, [4], 0, []⟩]
  | 0, 1, 4, 3 => [⟨0, [4, 1], 0, [1]⟩, ⟨0, [2, 1, 4, 3, 2, 1], 1, [4, 1, 0, 4, 3, 2]⟩,
      ⟨0, [4, 3, 2, 1], 1, [0, 1, 4, 2]⟩, ⟨0, [4], 0, []⟩, ⟨0, [1, 4], 0, [4]⟩]
  | 0, 1, 4, 4 => [⟨0, [4, 1], 0, [1]⟩, ⟨0, [], 4, []⟩,
      ⟨0, [2, 0, 1, 4, 3, 2, 1], 1, [4, 1, 0, 4, 3, 2]⟩, ⟨0, [0, 4, 1], 0, [4, 1]⟩, ⟨0, [4], 0, []⟩]
  | 0, 2, 4, 4 => [⟨0, [4, 2, 1], 0, [2, 1]⟩, ⟨0, [2, 4, 3, 2, 1], 0, [3, 1, 2, 4]⟩]
  | 0, 3, 3, 4 => [⟨0, [4, 3, 2, 1], 0, [3, 2, 1]⟩, ⟨0, [4, 2, 3, 4, 1], 1, [3, 0, 4, 3, 2]⟩,
      ⟨0, [4, 3, 2, 1], 2, [3, 0, 4, 3]⟩, ⟨0, [2, 3, 4], 3, [1, 0, 4]⟩, ⟨0, [4], 0, []⟩]
  | 0, 3, 4, 3 => [⟨0, [4, 3, 2, 1], 0, [3, 2, 1]⟩, ⟨0, [2, 3, 4], 3, [1, 0, 4]⟩,
      ⟨0, [4, 2, 3, 4, 1], 1, [3, 0, 4, 3, 2]⟩, ⟨0, [4], 0, []⟩, ⟨0, [4, 3, 2, 1], 2, [3, 0, 4, 3]⟩]
  | 0, 3, 4, 4 => [⟨0, [4, 3, 2, 1], 0, [3, 2, 1]⟩, ⟨0, [3, 1, 0, 4], 2, [4, 0, 4, 3]⟩,
      ⟨0, [1, 0, 4, 2, 1], 2, [3, 4, 0, 4, 3]⟩, ⟨0, [4], 0, []⟩]
  | 3, 0, 3, 4 => [⟨3, [4], 3, []⟩, ⟨0, [4, 3, 2, 1], 0, [3, 2, 1]⟩,
      ⟨0, [1, 0, 4, 2, 1], 2, [3, 4, 0, 4, 3]⟩, ⟨0, [4, 3, 2, 1], 0, [3, 0, 4, 1]⟩,
      ⟨0, [2, 3, 4], 3, [1, 0, 4]⟩]
  | 3, 0, 4, 3 => [⟨3, [4], 3, []⟩, ⟨0, [4, 3, 2, 1], 0, [3, 0, 4, 1]⟩,
      ⟨0, [4, 3, 2, 1], 0, [3, 2, 1]⟩, ⟨0, [2, 3, 4], 3, [1, 0, 4]⟩,
      ⟨0, [1, 0, 4, 2, 1], 2, [3, 4, 0, 4, 3]⟩]
  | 3, 0, 4, 4 => [⟨3, [4], 3, []⟩, ⟨0, [4, 3, 2, 1], 0, [3, 2, 1]⟩,
      ⟨0, [2, 3, 4, 1], 3, [4, 3, 0, 4]⟩, ⟨0, [4, 2, 3, 4, 1], 1, [3, 0, 4, 3, 2]⟩]
  | 3, 1, 4, 4 => [⟨3, [4], 3, []⟩, ⟨1, [4, 3, 2], 1, [3, 2]⟩,
      ⟨0, [1, 4, 3, 2, 1], 0, [2, 3, 4, 1]⟩, ⟨0, [2, 3, 4, 1], 1, [4, 3, 4]⟩,
      ⟨0, [1, 4, 2, 1], 2, [3, 4, 3]⟩]
  | 3, 2, 3, 4 => [⟨3, [4], 3, []⟩, ⟨2, [4, 3], 2, [3]⟩, ⟨0, [4, 3, 2, 1], 1, [3, 2, 4, 2]⟩,
      ⟨2, [3, 4], 2, [4]⟩, ⟨0, [1, 2, 4, 3, 2, 1], 0, [4, 2, 3, 4, 2, 1]⟩]
  | 3, 2, 4, 3 => [⟨3, [4], 3, []⟩, ⟨2, [3, 4], 2, [4]⟩, ⟨2, [4, 3], 2, [3]⟩,
      ⟨0, [1, 2, 4, 3, 2, 1], 0, [4, 2, 3, 4, 2, 1]⟩, ⟨0, [4, 3, 2, 1], 1, [3, 2, 4, 2]⟩]
  | 3, 2, 4, 4 => [⟨3, [4], 3, []⟩, ⟨2, [4, 3], 2, [3]⟩,
      ⟨0, [0, 1, 2, 4, 3, 2, 1], 1, [3, 4, 2, 3, 4, 2]⟩, ⟨2, [3, 4, 3], 2, [4, 3]⟩]
  | _, _, _, _ => []

private def l05nPCzvals : List (ZMod 5) := [0, 1, 2, 3, 4]

private lemma l05nPCmem_zvals : ∀ x : ZMod 5, x ∈ l05nPCzvals := by decide +kernel

private def l05nPCallVecs : List (GGDepAE 5 5) :=
  l05nPCzvals.flatMap fun a =>
    l05nPCzvals.flatMap fun b =>
      l05nPCzvals.flatMap fun c =>
        l05nPCzvals.flatMap fun d =>
          l05nPCzvals.map fun e => ![a, b, c, d, e]

private lemma l05nPCmem_allVecs (v : GGDepAE 5 5) : v ∈ l05nPCallVecs := by
  rw [l05nPCallVecs, List.mem_flatMap]
  refine ⟨v 0, l05nPCmem_zvals _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨v 1, l05nPCmem_zvals _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨v 2, l05nPCmem_zvals _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨v 3, l05nPCmem_zvals _, ?_⟩
  rw [List.mem_map]
  refine ⟨v 4, l05nPCmem_zvals _, ?_⟩
  ext j
  fin_cases j <;> rfl

private def l05nPChaB (b c0 : Fin 4) (n : ZMod 5) (ha : GGDepAE 5 5) : Bool :=
  l05nPCcvals.all fun c =>
    c == b || (l05nPCdot (l05nPCaTab c) ha == (if c = c0 then n else 0))

private def l05nPCaaB (b c0 : Fin 4) (m : ZMod 5) (aa : GGDepAE 5 5) : Bool :=
  l05nPCcvals.all fun c =>
    c == b || (l05nPCdot aa (l05nPChTab c) == (if c = c0 then m else 0))

private def l05nPChaSol (b c0 : Fin 4) (n : ZMod 5) : List (GGDepAE 5 5) :=
  l05nPCallVecs.filter (l05nPChaB b c0 n)

private def l05nPCaaSol (b c0 : Fin 4) (m : ZMod 5) : List (GGDepAE 5 5) :=
  l05nPCallVecs.filter (l05nPCaaB b c0 m)

private lemma l05nPChaB_of (b c0 : Fin 4) (n : ZMod 5) (ha : GGDepAE 5 5)
    (h : ∀ c : Fin 4, c ≠ b →
      l05nPCdot (ggDepAα 5 5 c) ha = (if c = c0 then n else 0)) :
    l05nPChaB b c0 n ha = true := by
  rw [l05nPChaB, List.all_eq_true]
  intro c _
  by_cases hcb : c = b
  · simp [hcb]
  · rw [Bool.or_eq_true]
    right
    rw [l05nPCaTab_eq]
    exact beq_iff_eq.mpr (h c hcb)

private lemma l05nPCaaB_of (b c0 : Fin 4) (m : ZMod 5) (aa : GGDepAE 5 5)
    (h : ∀ c : Fin 4, c ≠ b →
      l05nPCdot aa (ggDepAh 5 5 c) = (if c = c0 then m else 0)) :
    l05nPCaaB b c0 m aa = true := by
  rw [l05nPCaaB, List.all_eq_true]
  intro c _
  by_cases hcb : c = b
  · simp [hcb]
  · rw [Bool.or_eq_true]
    right
    rw [l05nPChTab_eq]
    exact beq_iff_eq.mpr (h c hcb)

private def l05nPCcheck (b c0 : Fin 4) (m n : ZMod 5) (wits : List l05nPCWit) : Bool :=
  (l05nPChaSol b c0 n).all fun ha =>
    (l05nPCaaSol b c0 m).all fun aa =>
      if l05nPCdot aa ha == 2 && l05nPCdot aa l05nPCxTab != 0 then
        wits.any (fun w => l05nPCwitTest w ha aa)
      else true

private lemma l05nPCfirstNZ_zero : l05nPCfirstNZ (0 : GGDepAE 5 5) = none := by
  decide +kernel

private lemma l05nPCfirstNZ_spec (c : GGDepAE 5 5) (j : Fin 5)
    (h : l05nPCfirstNZ c = some j) : c j ≠ 0 := by
  have := List.find?_some h
  simpa using this

private lemma l05nPC_refl_smul (c f : GGDepAE 5 5) (lam : ZMod 5) (hlam : lam ≠ 0) :
    ggDepARefl (lam⁻¹ • c) (lam • f) = ggDepARefl c f := by
  apply LinearMap.ext; intro v
  rw [l05nPC_refl_apply, l05nPC_refl_apply, l05nPC_dot_smul_left, smul_smul]
  congr 1
  rw [mul_assoc, mul_comm (ggDepAdot f v) lam⁻¹, ← mul_assoc, mul_inv_cancel₀ hlam, one_mul]

private lemma l05nPCnormalize_refl (p : GGDepAE 5 5 × GGDepAE 5 5) :
    ggDepARefl (l05nPCnormalize p).1 (l05nPCnormalize p).2 = ggDepARefl p.1 p.2 := by
  unfold l05nPCnormalize
  split
  · rfl
  · rename_i j hj
    exact l05nPC_refl_smul p.1 p.2 (p.1 j) (l05nPCfirstNZ_spec p.1 j hj)

private lemma l05nPCnormalize_dot (p : GGDepAE 5 5 × GGDepAE 5 5) :
    ggDepAdot (l05nPCnormalize p).2 (l05nPCnormalize p).1 = ggDepAdot p.2 p.1 := by
  unfold l05nPCnormalize
  split
  · rfl
  · rename_i j hj
    rw [l05nPC_dot_smul_left, l05nPC_dot_smul]
    rw [show p.1 j * ((p.1 j)⁻¹ * ggDepAdot p.2 p.1) = ggDepAdot p.2 p.1 by
      rw [← mul_assoc, mul_inv_cancel₀ (l05nPCfirstNZ_spec p.1 j hj), one_mul]]

private lemma l05nPCprop_ne_zero (f1 f2 : GGDepAE 5 5) (k : ZMod 5)
    (h : l05nPCprop f1 f2 = some k) : f1 ≠ 0 := by
  intro hf
  rw [hf] at h
  simp [l05nPCprop, l05nPCfirstNZ_zero] at h

private lemma l05nPCprop_spec (f1 f2 : GGDepAE 5 5) (k : ZMod 5)
    (h : l05nPCprop f1 f2 = some k) : f2 = k • f1 := by
  unfold l05nPCprop at h
  cases hf1 : l05nPCfirstNZ f1 with
  | none => rw [hf1] at h; simp at h
  | some j =>
      rw [hf1] at h
      dsimp only at h
      by_cases hk : (List.finRange 5).all
          (fun i => (f2 j * (f1 j)⁻¹) * f1 i == f2 i) = true
      · rw [if_pos hk] at h
        have hk' : k = f2 j * (f1 j)⁻¹ := (Option.some.inj h).symm
        rw [hk']
        ext i
        have hi := (List.all_eq_true.mp hk) i (List.mem_finRange i)
        exact (beq_iff_eq.mp hi).symm
      · rw [if_neg hk] at h; simp at h

private theorem l05nPCtestPairN_sound (q1 q2 : GGDepAE 5 5 × GGDepAE 5 5)
    (h1 : ggDepAdot q1.2 q1.1 = 2) (h2 : ggDepAdot q2.2 q2.1 = 2)
    (ht : l05nPCtestPairN q1 q2 = true) :
    GGDepAIsTv (ggDepARefl q1.1 q1.2 * ggDepARefl q2.1 q2.2) := by
  rw [l05nPCtestPairN, Bool.or_eq_true] at ht
  rcases ht with hAB | hprop
  · rw [Bool.and_eq_true] at hAB
    have hc : q1.1 = q2.1 := beq_iff_eq.mp hAB.1
    have hf : q1.2 ≠ q2.2 := bne_iff_ne.mp hAB.2
    rw [← hc] at h2 ⊢
    rw [l05nPC_refl_mul_same q1.1 q1.2 q2.2 h1 h2]
    refine l05nPC_isTv_one_add q1.1 (q2.2 - q1.2) ?_ ?_ ?_
    · rw [l05nPC_dot_sub_left, h1, h2, sub_self]
    · intro h0; rw [h0] at h1; simp [ggDepAdot] at h1
      exact (by decide : (0 : ZMod 5) ≠ 2) h1
    · exact sub_ne_zero.mpr hf.symm
  · cases hpk : l05nPCprop q1.2 q2.2 with
    | none => rw [hpk] at hprop; simp at hprop
    | some k =>
        rw [hpk, Bool.and_eq_true] at hprop
        have hk0 : k ≠ 0 := bne_iff_ne.mp hprop.1
        have hneq : k⁻¹ • q1.1 ≠ q2.1 := bne_iff_ne.mp hprop.2
        have hf2 : q2.2 = k • q1.2 := l05nPCprop_spec q1.2 q2.2 k hpk
        have hf1nz : q1.2 ≠ 0 := l05nPCprop_ne_zero q1.2 q2.2 k hpk
        have hdot2 : ggDepAdot q1.2 q2.1 = k⁻¹ * 2 := by
          have hk : k * ggDepAdot q1.2 q2.1 = 2 := by
            rw [← h2, hf2, l05nPC_dot_smul_left]
          rw [← hk, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
        have hd : q1.1 - k • q2.1 ≠ 0 := by
          intro h0
          apply hneq
          rw [sub_eq_zero.mp h0, smul_smul, inv_mul_cancel₀ hk0, one_smul]
        rw [l05nPC_refl_mul_prop q1.1 q2.1 q1.2 q2.2 k h1 hf2 hk0 hdot2]
        refine l05nPC_isTv_one_add (q1.1 - k • q2.1) q1.2 ?_ hd hf1nz
        rw [l05nPC_dot_sub, l05nPC_dot_smul, h1, hdot2, ← mul_assoc, mul_inv_cancel₀ hk0,
          one_mul, sub_self]

private theorem l05nPCtestPair_sound (p1 p2 : GGDepAE 5 5 × GGDepAE 5 5)
    (h1 : ggDepAdot p1.2 p1.1 = 2) (h2 : ggDepAdot p2.2 p2.1 = 2)
    (ht : l05nPCtestPair p1 p2 = true) :
    GGDepAIsTv (ggDepARefl p1.1 p1.2 * ggDepARefl p2.1 p2.2) := by
  rw [← l05nPCnormalize_refl p1, ← l05nPCnormalize_refl p2]
  exact l05nPCtestPairN_sound (l05nPCnormalize p1) (l05nPCnormalize p2)
    (by rw [l05nPCnormalize_dot]; exact h1)
    (by rw [l05nPCnormalize_dot]; exact h2) ht

private def l05nPCgen (ha aa : GGDepAE 5 5) (i : Fin 5) :
    Module.End (ZMod 5) (GGDepAE 5 5) :=
  ggDepARefl (l05nPCgenPair ha aa i).1 (l05nPCgenPair ha aa i).2

private def l05nPCwordEnd (g : Fin 5 → Module.End (ZMod 5) (GGDepAE 5 5))
    (w : List (Fin 5)) : Module.End (ZMod 5) (GGDepAE 5 5) :=
  (w.map g).prod

private lemma l05nPCwordEnd_cons (g : Fin 5 → Module.End (ZMod 5) (GGDepAE 5 5))
    (a : Fin 5) (w : List (Fin 5)) :
    l05nPCwordEnd g (a :: w) = g a * l05nPCwordEnd g w := by
  simp [l05nPCwordEnd]

private def l05nPCwordEndInv (g : Fin 5 → Module.End (ZMod 5) (GGDepAE 5 5))
    (w : List (Fin 5)) : Module.End (ZMod 5) (GGDepAE 5 5) :=
  (w.reverse.map g).prod

private lemma l05nPCwordEndInv_cons (g : Fin 5 → Module.End (ZMod 5) (GGDepAE 5 5))
    (a : Fin 5) (w : List (Fin 5)) :
    l05nPCwordEndInv g (a :: w) = l05nPCwordEndInv g w * g a := by
  simp [l05nPCwordEndInv]

private lemma l05nPCpairWord_cons (p : GGDepAE 5 5 × GGDepAE 5 5) (a : Fin 5)
    (w : List (Fin 5)) (pairs : Fin 5 → GGDepAE 5 5 × GGDepAE 5 5) :
    l05nPCpairWord p (a :: w) pairs =
      l05nPCpairConj (l05nPCpairWord p w pairs) (pairs a) := by
  simp [l05nPCpairWord]

private lemma l05nPC_pair_i : ∀ i : Fin 4,
    ggDepAdot (ggDepAα 5 5 i) (ggDepAh 5 5 i) = 2 := by
  decide +kernel

private lemma l05nPC_genPair_dot (ha aa : GGDepAE 5 5) (h2 : ggDepAdot aa ha = 2)
    (j : Fin 5) :
    ggDepAdot (l05nPCgenPair ha aa j).2 (l05nPCgenPair ha aa j).1 = 2 := by
  unfold l05nPCgenPair
  split
  · exact l05nPC_pair_i _
  · exact h2

private lemma l05nPCpairConj_dot (p gp : GGDepAE 5 5 × GGDepAE 5 5)
    (hp : ggDepAdot p.2 p.1 = 2) (hgp : ggDepAdot gp.2 gp.1 = 2) :
    ggDepAdot (l05nPCpairConj p gp).2 (l05nPCpairConj p gp).1 = 2 := by
  change ggDepAdot (p.2 - l05nPCdot p.2 gp.1 • gp.2)
    (p.1 - l05nPCdot gp.2 p.1 • gp.1) = 2
  rw [l05nPCdot_eq, l05nPCdot_eq]
  rw [l05nPC_dot_sub, l05nPC_dot_sub_left, l05nPC_dot_smul_left, l05nPC_dot_smul,
    l05nPC_dot_sub_left, l05nPC_dot_smul_left, hp, hgp]
  ring

private lemma l05nPCpairWord_dot (p : GGDepAE 5 5 × GGDepAE 5 5) (w : List (Fin 5))
    (pairs : Fin 5 → GGDepAE 5 5 × GGDepAE 5 5)
    (hp : ggDepAdot p.2 p.1 = 2)
    (hpair : ∀ j, ggDepAdot (pairs j).2 (pairs j).1 = 2) :
    ggDepAdot (l05nPCpairWord p w pairs).2 (l05nPCpairWord p w pairs).1 = 2 := by
  induction w generalizing p with
  | nil => simpa [l05nPCpairWord] using hp
  | cons a w ih =>
      rw [l05nPCpairWord_cons]
      exact l05nPCpairConj_dot (l05nPCpairWord p w pairs) (pairs a) (ih p hp) (hpair a)

private lemma l05nPCpairConj_refl (p gp : GGDepAE 5 5 × GGDepAE 5 5)
    (h : ggDepAdot gp.2 gp.1 = 2) :
    ggDepARefl gp.1 gp.2 * ggDepARefl p.1 p.2 * ggDepARefl gp.1 gp.2 =
      ggDepARefl (l05nPCpairConj p gp).1 (l05nPCpairConj p gp).2 := by
  change ggDepARefl gp.1 gp.2 * ggDepARefl p.1 p.2 * ggDepARefl gp.1 gp.2 =
      ggDepARefl (p.1 - l05nPCdot gp.2 p.1 • gp.1) (p.2 - l05nPCdot p.2 gp.1 • gp.2)
  rw [l05nPCdot_eq, l05nPCdot_eq]
  exact l05nPC_refl_conj p.1 p.2 gp.1 gp.2 h

private lemma l05nPCpairWord_refl (g : Fin 5 → Module.End (ZMod 5) (GGDepAE 5 5))
    (pairs : Fin 5 → GGDepAE 5 5 × GGDepAE 5 5) (w : List (Fin 5))
    (p : GGDepAE 5 5 × GGDepAE 5 5)
    (hgen : ∀ j, g j = ggDepARefl (pairs j).1 (pairs j).2)
    (hpair : ∀ j, ggDepAdot (pairs j).2 (pairs j).1 = 2) :
    l05nPCwordEnd g w * ggDepARefl p.1 p.2 * l05nPCwordEndInv g w =
      ggDepARefl (l05nPCpairWord p w pairs).1 (l05nPCpairWord p w pairs).2 := by
  induction w generalizing p with
  | nil => simp [l05nPCwordEnd, l05nPCwordEndInv, l05nPCpairWord]
  | cons a w ih =>
      rw [l05nPCwordEnd_cons, l05nPCwordEndInv_cons, l05nPCpairWord_cons]
      have hassoc : g a * l05nPCwordEnd g w * ggDepARefl p.1 p.2 * (l05nPCwordEndInv g w * g a) =
          g a * (l05nPCwordEnd g w * ggDepARefl p.1 p.2 * l05nPCwordEndInv g w) * g a := by
        simp only [mul_assoc]
      rw [hassoc, ih p, hgen a]
      exact l05nPCpairConj_refl (l05nPCpairWord p w pairs) (pairs a) (hpair a)

private theorem l05nPCwitTest_sound (w : l05nPCWit) (ha aa : GGDepAE 5 5)
    (h2 : ggDepAdot aa ha = 2) (ht : l05nPCwitTest w ha aa = true) :
    GGDepAIsTv
      ((l05nPCwordEnd (l05nPCgen ha aa) w.w1 * l05nPCgen ha aa w.g1 *
          l05nPCwordEndInv (l05nPCgen ha aa) w.w1) *
        (l05nPCwordEnd (l05nPCgen ha aa) w.w2 * l05nPCgen ha aa w.g2 *
          l05nPCwordEndInv (l05nPCgen ha aa) w.w2)) := by
  have hgen : ∀ j, l05nPCgen ha aa j =
      ggDepARefl (l05nPCgenPair ha aa j).1 (l05nPCgenPair ha aa j).2 := fun _ => rfl
  have hpair : ∀ j, ggDepAdot (l05nPCgenPair ha aa j).2 (l05nPCgenPair ha aa j).1 = 2 :=
    fun j => l05nPC_genPair_dot ha aa h2 j
  have e1 := l05nPCpairWord_refl (l05nPCgen ha aa) (l05nPCgenPair ha aa) w.w1
    (l05nPCgenPair ha aa w.g1) hgen hpair
  have e2 := l05nPCpairWord_refl (l05nPCgen ha aa) (l05nPCgenPair ha aa) w.w2
    (l05nPCgenPair ha aa w.g2) hgen hpair
  rw [hgen w.g1, hgen w.g2, e1, e2]
  exact l05nPCtestPair_sound _ _
    (l05nPCpairWord_dot _ _ _ (hpair w.g1) hpair)
    (l05nPCpairWord_dot _ _ _ (hpair w.g2) hpair)
    (by simpa [l05nPCwitTest] using ht)

private lemma l05nPCztoint_cast (m : ℤ) (hm : m = -1 ∨ m = -2) :
    l05nPCztoint (m : ZMod 5) = m := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma l05nPCpatB_of_pat (b c0 : Fin 4) (m n : ℤ) (h : GGDepAPat 5 b c0 m n) :
    l05nPCpatB b c0 (m : ZMod 5) (n : ZMod 5) = true := by
  unfold l05nPCpatB
  rw [decide_eq_true_eq]
  have hm : m = -1 ∨ m = -2 := by
    have h' := h; unfold GGDepAPat at h'; omega
  have hn : n = -1 ∨ n = -2 := by
    have h' := h; unfold GGDepAPat at h'; omega
  rw [l05nPCztoint_cast m hm, l05nPCztoint_cast n hn]
  exact h

private theorem l05nPC_cells_b0 :
    ∀ (c0 : Fin 4) (m n : ZMod 5), l05nPCpatB 0 c0 m n = true →
      l05nPCcheck 0 c0 m n (l05nPCwitList 0 c0 m n) = true := by
  decide +kernel

private theorem l05nPC_cells_b1 :
    ∀ (c0 : Fin 4) (m n : ZMod 5), l05nPCpatB 1 c0 m n = true →
      l05nPCcheck 1 c0 m n (l05nPCwitList 1 c0 m n) = true := by
  decide +kernel

private theorem l05nPC_cells_b2 :
    ∀ (c0 : Fin 4) (m n : ZMod 5), l05nPCpatB 2 c0 m n = true →
      l05nPCcheck 2 c0 m n (l05nPCwitList 2 c0 m n) = true := by
  decide +kernel

private theorem l05nPC_cells_b3 :
    ∀ (c0 : Fin 4) (m n : ZMod 5), l05nPCpatB 3 c0 m n = true →
      l05nPCcheck 3 c0 m n (l05nPCwitList 3 c0 m n) = true := by
  decide +kernel

private theorem l05nPC_all_cells :
    ∀ (b c0 : Fin 4) (m n : ZMod 5),
      l05nPCpatB b c0 m n = true →
      l05nPCcheck b c0 m n (l05nPCwitList b c0 m n) = true := by
  intro b c0 m n h
  fin_cases b
  · exact l05nPC_cells_b0 c0 m n h
  · exact l05nPC_cells_b1 c0 m n h
  · exact l05nPC_cells_b2 c0 m n h
  · exact l05nPC_cells_b3 c0 m n h

theorem ggDepA_cells_5_5 : GGDepASmallCells 5 5 := by
  intro b c0 m n hpat ha αa hpair h2 hx
  have hpatB := l05nPCpatB_of_pat b c0 m n hpat
  have hcheck := l05nPC_all_cells b c0 (m : ZMod 5) (n : ZMod 5) hpatB
  have hha : ha ∈ l05nPChaSol b c0 (n : ZMod 5) :=
    List.mem_filter.mpr ⟨l05nPCmem_allVecs ha,
      l05nPChaB_of b c0 (n : ZMod 5) ha (fun c hc => by rw [l05nPCdot_eq]; exact (hpair c hc).2)⟩
  have haa : αa ∈ l05nPCaaSol b c0 (m : ZMod 5) :=
    List.mem_filter.mpr ⟨l05nPCmem_allVecs αa,
      l05nPCaaB_of b c0 (m : ZMod 5) αa (fun c hc => by rw [l05nPCdot_eq]; exact (hpair c hc).1)⟩
  rw [l05nPCcheck, List.all_eq_true] at hcheck
  have h1 := hcheck ha hha
  rw [List.all_eq_true] at h1
  have h2' := h1 αa haa
  have hcond : (l05nPCdot αa ha == 2 && l05nPCdot αa l05nPCxTab != 0) = true := by
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr (by rw [l05nPCdot_eq]; exact h2),
      bne_iff_ne.mpr (by rw [l05nPCdot_eq, l05nPCxTab_eq]; exact hx)⟩
  rw [hcond] at h2'
  simp only [if_true] at h2'
  rw [List.any_eq_true] at h2'
  obtain ⟨w, hwmem, hwtest⟩ := h2'
  let g1 : Fin 5 → Module.End (ZMod 5) (GGDepAE 5 5) := l05nPCgen ha αa
  have hclos : ∀ i : Fin 5, g1 i ∈ Submonoid.closure
      (Set.range (fun i : Fin 4 => ggDepARefl (ggDepAh 5 5 i) (ggDepAα 5 5 i)) ∪
        {ggDepARefl ha αa}) := by
    intro i
    change l05nPCgen ha αa i ∈ _
    unfold l05nPCgen l05nPCgenPair
    split
    · rename_i h
      exact Submonoid.subset_closure (Or.inl ⟨⟨i.val, h⟩, rfl⟩)
    · exact Submonoid.subset_closure (Or.inr rfl)
  have hword : ∀ w : List (Fin 5), l05nPCwordEnd g1 w ∈ Submonoid.closure
      (Set.range (fun i : Fin 4 => ggDepARefl (ggDepAh 5 5 i) (ggDepAα 5 5 i)) ∪
        {ggDepARefl ha αa}) := by
    intro w
    induction w with
    | nil => exact Submonoid.one_mem _
    | cons a w ih =>
        rw [l05nPCwordEnd_cons]
        exact Submonoid.mul_mem _ (hclos a) ih
  have hwordInv : ∀ w : List (Fin 5), l05nPCwordEndInv g1 w ∈ Submonoid.closure
      (Set.range (fun i : Fin 4 => ggDepARefl (ggDepAh 5 5 i) (ggDepAα 5 5 i)) ∪
        {ggDepARefl ha αa}) := by
    intro w
    induction w with
    | nil => exact Submonoid.one_mem _
    | cons a w ih =>
        rw [l05nPCwordEndInv_cons]
        exact Submonoid.mul_mem _ ih (hclos a)
  refine ⟨(l05nPCwordEnd g1 w.w1 * g1 w.g1 * l05nPCwordEndInv g1 w.w1) *
      (l05nPCwordEnd g1 w.w2 * g1 w.g2 * l05nPCwordEndInv g1 w.w2), ?_, ?_⟩
  · exact Submonoid.mul_mem _
      (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hword w.w1) (hclos w.g1)) (hwordInv w.w1))
      (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hword w.w2) (hclos w.g2)) (hwordInv w.w2))
  · exact l05nPCwitTest_sound w ha αa h2 hwtest

end CFSG.StandardType
