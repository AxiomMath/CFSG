module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

variable {Y : Type} [Group Y] [Finite Y]

theorem ker_of_card (f : Multiplicative (Fin 4 → ZMod 3) →* Y) (h27 : Nat.card f.range = 27)
    (hconst : ∀ t : ZMod 3, f (Multiplicative.ofAdd fun _ => t) = 1) :
    ∀ v, f v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t := by
  have hcardG : Nat.card (Multiplicative (Fin 4 → ZMod 3)) = 81 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun]
    norm_num
  have hker : Nat.card f.ker = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have hq : Nat.card (Multiplicative (Fin 4 → ZMod 3) ⧸ f.ker) = 27 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, h27]
    rw [hcardG, hq] at h
    omega
  let φ : Multiplicative (ZMod 3) →* Multiplicative (Fin 4 → ZMod 3) :=
    AddMonoidHom.toMultiplicative
      { toFun := fun t _ => t
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Multiplicative.toAdd.injective
    simpa [φ, AddMonoidHom.coe_toMultiplicative] using
      congrFun (congrArg Multiplicative.toAdd hab) 0
  have hcardC : Nat.card φ.range = 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
    simp
  have hC_le : φ.range ≤ f.ker := by
    rintro x ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    have hy : φ y = Multiplicative.ofAdd (fun _ : Fin 4 => Multiplicative.toAdd y) := rfl
    rw [hy]
    exact hconst (Multiplicative.toAdd y)
  have hCeq : φ.range = f.ker :=
    Subgroup.eq_of_le_of_card_ge hC_le (by rw [hcardC, hker])
  intro v
  rw [← MonoidHom.mem_ker, ← hCeq]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Multiplicative.toAdd y, ?_⟩
    rw [← hy]
    rfl
  · rintro ⟨t, ht⟩
    refine ⟨Multiplicative.ofAdd t, ?_⟩
    rw [show φ (Multiplicative.ofAdd t) =
        Multiplicative.ofAdd (fun _ : Fin 4 => t) from rfl,
      ← ofAdd_toAdd v, ht]

private lemma sum_four_const (t : ZMod 3) : (∑ _ : Fin 4, t) = t := by
  decide +revert

private lemma sum_sub_sum_const (a : Fin 4 → ZMod 3) :
    (∑ j, (a j - ∑ k, a k)) = 0 := by
  decide +revert

private lemma sum_single_eq (v : Fin 4 → ZMod 3) :
    (∑ i, Pi.single i (v i)) = v := by
  decide +revert

private lemma neg_eq_add_self (p : Fin 4 → ZMod 3) : -p = p + p := by
  decide +revert

private lemma neg_eq_add_self_zmod (x : ZMod 3) : -x = x + x := by
  decide +revert

private lemma map_const_eq_one {c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    (h₀k : ∀ v, c₀ v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t)
    (t : ZMod 3) : c₀ (Multiplicative.ofAdd (fun _ : Fin 4 => t)) = 1 :=
  (h₀k _).mpr ⟨t, rfl⟩

private lemma map_sub_const {c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    (h₀k : ∀ v, c₀ v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t)
    (a : Fin 4 → ZMod 3) :
    c₀ (Multiplicative.ofAdd (fun j => a j - ∑ k, a k)) =
      c₀ (Multiplicative.ofAdd a) := by
  have h : (fun j => a j - ∑ k, a k) = a + fun _ : Fin 4 => -(∑ k, a k) := by
    funext j
    show a j - (∑ k, a k) = a j + -(∑ k, a k)
    rw [sub_eq_add_neg]
    rfl
  rw [h, ofAdd_add, map_mul, map_const_eq_one h₀k, mul_one]

private lemma exists_lift_column {A : Subgroup Y}
    {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y} (hc : IsSumZeroCoords A c)
    (h₀r : c₀.range = A) (i : Fin 4) :
    ∃ w : Fin 4 → ZMod 3,
      c₀ (Multiplicative.ofAdd w) = c (Multiplicative.ofAdd (Pi.single i 1)) := by
  have hAi : c (Multiplicative.ofAdd (Pi.single i 1)) ∈ A := by
    rw [← hc.1]; exact ⟨_, rfl⟩
  rw [← h₀r] at hAi
  obtain ⟨x, hx⟩ := hAi
  exact ⟨Multiplicative.toAdd x, by simpa using hx⟩

private lemma action_eq_of_columns_zero {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    {N : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3)} (hN0 : N 0 = 0) :
    c (Multiplicative.ofAdd (0 : Fin 4 → ZMod 3)) = c₀ (Multiplicative.ofAdd (N 0)) := by
  rw [hN0]
  simp

private lemma action_eq_of_columns_add {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    {N : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3)}
    (hNadd : ∀ p q, N (p + q) = N p + N q) {p q : Fin 4 → ZMod 3}
    (hp : c (Multiplicative.ofAdd p) = c₀ (Multiplicative.ofAdd (N p)))
    (hq : c (Multiplicative.ofAdd q) = c₀ (Multiplicative.ofAdd (N q))) :
    c (Multiplicative.ofAdd (p + q)) = c₀ (Multiplicative.ofAdd (N (p + q))) := by
  rw [hNadd p q, ofAdd_add, map_mul, hp, hq, ofAdd_add, map_mul]

private lemma action_eq_of_columns_neg {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    {N : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3)} (hNneg : ∀ p, N (-p) = N p + N p)
    {p : Fin 4 → ZMod 3} (hp : c (Multiplicative.ofAdd p) = c₀ (Multiplicative.ofAdd (N p))) :
    c (Multiplicative.ofAdd (-p)) = c₀ (Multiplicative.ofAdd (N (-p))) := by
  have hpp : -p = p + p := neg_eq_add_self p
  calc c (Multiplicative.ofAdd (-p))
      = c (Multiplicative.ofAdd (p + p)) := by rw [hpp]
    _ = c (Multiplicative.ofAdd p) * c (Multiplicative.ofAdd p) := by rw [ofAdd_add, map_mul]
    _ = c₀ (Multiplicative.ofAdd (N p)) * c₀ (Multiplicative.ofAdd (N p)) := by rw [hp]
    _ = c₀ (Multiplicative.ofAdd (N p) * Multiplicative.ofAdd (N p)) := by rw [map_mul]
    _ = c₀ (Multiplicative.ofAdd (N p + N p)) := by rw [ofAdd_add]
    _ = c₀ (Multiplicative.ofAdd (N (-p))) := by rw [hNneg p]

private lemma action_eq_of_columns_generator {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    {N : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3)}
    (h₀k : ∀ v, c₀ v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t)
    {M : Fin 4 → Fin 4 → ZMod 3} {w : Fin 4 → Fin 4 → ZMod 3}
    (hMdef : ∀ j i, M j i = w i j - ∑ k, w i k)
    (hw : ∀ i, c₀ (Multiplicative.ofAdd (w i)) = c (Multiplicative.ofAdd (Pi.single i 1)))
    (i : Fin 4) (hN : N (Pi.single i (1 : ZMod 3)) = fun j => M j i) :
    c (Multiplicative.ofAdd (Pi.single i 1)) = c₀ (Multiplicative.ofAdd (N (Pi.single i 1))) := by
  rw [hN]
  have hMi : (fun j => M j i) = fun j => w i j - ∑ k, w i k := by funext j; rw [hMdef]
  rw [hMi, map_sub_const h₀k (w i), hw i]

private lemma action_eq_of_columns_single {T : AddSubgroup (Fin 4 → ZMod 3)}
    (hgen : ∀ i : Fin 4, Pi.single i (1 : ZMod 3) ∈ T) (i : Fin 4) (a : ZMod 3) :
    Pi.single i a ∈ T := by
  have h1 : (Pi.single i a : Fin 4 → ZMod 3) =
      a.val • (Pi.single i (1 : ZMod 3) : Fin 4 → ZMod 3) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [ZMod.natCast_zmod_val]
    · rw [Pi.single_eq_of_ne hj, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]
  rw [h1]
  exact nsmul_mem (hgen i) a.val

private lemma action_eq_of_columns {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    (h₀k : ∀ v, c₀ v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t)
    {M : Fin 4 → Fin 4 → ZMod 3} {w : Fin 4 → Fin 4 → ZMod 3}
    (hMdef : ∀ j i, M j i = w i j - ∑ k, w i k)
    (hw : ∀ i, c₀ (Multiplicative.ofAdd (w i)) = c (Multiplicative.ofAdd (Pi.single i 1))) :
    ∀ v : Fin 4 → ZMod 3, c (Multiplicative.ofAdd v) =
      c₀ (Multiplicative.ofAdd fun j => ∑ i, M j i * v i) := by
  intro v
  let N : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3) := fun v j => ∑ i, M j i * v i
  change c (Multiplicative.ofAdd v) = c₀ (Multiplicative.ofAdd (N v))
  have hN0 : N 0 = 0 := by funext j; simp [N]
  have hNadd : ∀ p q, N (p + q) = N p + N q := fun p q => by
    funext j; simp only [N, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hNneg : ∀ p, N (-p) = N p + N p := fun p => by
    funext j
    simp only [N, Pi.neg_apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [neg_eq_add_self_zmod (p i), mul_add])
  let T : AddSubgroup (Fin 4 → ZMod 3) :=
    { carrier := {u | c (Multiplicative.ofAdd u) = c₀ (Multiplicative.ofAdd (N u))}
      zero_mem' := action_eq_of_columns_zero hN0
      add_mem' := fun {p q} hp hq => action_eq_of_columns_add hNadd hp hq
      neg_mem' := fun {p} hp => action_eq_of_columns_neg hNneg hp }
  have hgen : ∀ i : Fin 4, Pi.single i (1 : ZMod 3) ∈ T := by
    intro i
    have hNi : N (Pi.single i 1) = fun j => M j i := by
      funext j
      simp only [N]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    exact action_eq_of_columns_generator h₀k hMdef hw i hNi
  have hsingle : ∀ (i : Fin 4) (a : ZMod 3), Pi.single i a ∈ T :=
    action_eq_of_columns_single hgen
  rw [show v = ∑ i, Pi.single i (v i) from (sum_single_eq v).symm]
  exact sum_mem (fun i _ => hsingle i (v i))

private lemma row_sum_eq_zero {A : Subgroup Y}
    {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y} (hc : IsSumZeroCoords A c)
    (h₀k : ∀ v, c₀ v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t)
    {M : Fin 4 → Fin 4 → ZMod 3}
    (hM : ∀ v : Fin 4 → ZMod 3, c (Multiplicative.ofAdd v) =
      c₀ (Multiplicative.ofAdd fun j => ∑ i, M j i * v i))
    (hcol : ∀ i, ∑ j, M j i = 0) : ∀ j, ∑ i, M j i = 0 := by
  have hr : (fun j => ∑ i, M j i) = fun j => ∑ i, M j i * (1 : ZMod 3) := by
    funext j; simp
  have hc0r : c₀ (Multiplicative.ofAdd (fun j => ∑ i, M j i)) = 1 := by
    rw [hr, ← hM (fun _ : Fin 4 => (1 : ZMod 3))]
    exact (hc.2.1 _).mpr ⟨1, rfl⟩
  obtain ⟨t, ht⟩ := (h₀k _).mp hc0r
  have ht' : (fun j => ∑ i, M j i) = fun _ => t := by simpa using ht
  have hsum : (∑ j, (∑ i, M j i)) = t := by rw [ht', sum_four_const]
  have hsum0 : (∑ j, (∑ i, M j i)) = 0 := by
    rw [Finset.sum_comm]; simp [hcol]
  have ht0 : t = 0 := by rw [← hsum, hsum0]
  intro j
  rw [show ∑ i, M j i = t from congrFun ht' j]
  exact ht0

private lemma inj_of_action {A : Subgroup Y}
    {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y} (hc : IsSumZeroCoords A c)
    {M : Fin 4 → Fin 4 → ZMod 3}
    (hM : ∀ v : Fin 4 → ZMod 3, c (Multiplicative.ofAdd v) =
      c₀ (Multiplicative.ofAdd fun j => ∑ i, M j i * v i)) :
    ∀ w : Fin 4 → ZMod 3, (∑ i, w i) = 0 →
      (∀ j, ∑ i, M j i * w i = 0) → w = 0 := by
  intro w' hw' hzero
  have hN0 : (fun j => ∑ i, M j i * w' i) = 0 := by
    funext j; simpa using hzero j
  have hcw : c (Multiplicative.ofAdd w') = 1 := by
    rw [hM w', hN0]; simp
  obtain ⟨t, ht⟩ := (hc.2.1 _).mp hcw
  have ht' : w' = fun _ => t := by simpa using ht
  have hsum : (∑ i, w' i) = t := by rw [ht', sum_four_const]
  have ht0 : t = 0 := by rw [← hsum, hw']
  rw [ht', ht0]
  rfl

theorem compare_columns {A : Subgroup Y} {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    (hc : IsSumZeroCoords A c) (h₀r : c₀.range = A)
    (h₀k : ∀ v, c₀ v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t) :
    ∃ M : Fin 4 → Fin 4 → ZMod 3,
      (∀ v : Fin 4 → ZMod 3, c (Multiplicative.ofAdd v) =
        c₀ (Multiplicative.ofAdd fun j => ∑ i, M j i * v i)) ∧
      (∀ j, ∑ i, M j i = 0) ∧ (∀ i, ∑ j, M j i = 0) ∧
      (∀ w : Fin 4 → ZMod 3, ∑ i, w i = 0 → (∀ j, ∑ i, M j i * w i = 0) → w = 0) := by
  classical
  choose w hw using fun i => exists_lift_column hc h₀r i
  let M : Fin 4 → Fin 4 → ZMod 3 := fun j i => w i j - ∑ k, w i k
  have hMdef : ∀ j i, M j i = w i j - ∑ k, w i k := fun _ _ => rfl
  have hM := action_eq_of_columns h₀k hMdef hw
  have hcol : ∀ i, ∑ j, M j i = 0 := fun i => by
    simpa only [hMdef] using sum_sub_sum_const (w i)
  exact ⟨M, hM, row_sum_eq_zero hc h₀k hM hcol, hcol, inj_of_action hc hM⟩

private lemma sum_sum_mul_eq_zero (M : Fin 4 → Fin 4 → ZMod 3)
    (hcol : ∀ i, ∑ j, M j i = 0) (v : Fin 4 → ZMod 3) (τ : Equiv.Perm (Fin 4)) :
    (∑ j, ∑ i, M (τ j) i * v i) = 0 := by
  rw [Finset.sum_comm]
  rw [show (∑ i, ∑ j, M (τ j) i * v i) = ∑ i, ∑ j, M j i * v i from
    Finset.sum_congr rfl (fun i _ => Equiv.sum_comp τ (fun j => M j i * v i))]
  simp [← Finset.sum_mul, hcol]

private lemma eq_of_const_ker {c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    (h₀k : ∀ v, c₀ v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t)
    {F G : Fin 4 → ZMod 3} (hF : (∑ j, F j) = 0) (hG : (∑ j, G j) = 0)
    (heq : c₀ (Multiplicative.ofAdd F) = c₀ (Multiplicative.ofAdd G)) : F = G := by
  have hdiff : (Multiplicative.ofAdd (F - G) : Multiplicative (Fin 4 → ZMod 3)) =
      Multiplicative.ofAdd F * (Multiplicative.ofAdd G)⁻¹ := by
    rw [show F - G = F + -G from sub_eq_add_neg F G, ofAdd_add, ofAdd_neg]
  have hker : c₀ (Multiplicative.ofAdd (F - G)) = 1 := by
    have h1 : c₀ (Multiplicative.ofAdd F * (Multiplicative.ofAdd G)⁻¹) =
        c₀ (Multiplicative.ofAdd F) * (c₀ (Multiplicative.ofAdd G))⁻¹ := by
      rw [map_mul]
      exact congrArg (fun x => c₀ (Multiplicative.ofAdd F) * x)
        (map_inv c₀ (Multiplicative.ofAdd G))
    rw [hdiff, h1, heq, mul_inv_cancel]
  obtain ⟨t, ht⟩ := (h₀k _).mp hker
  have ht' : F - G = fun _ => t := by simpa using ht
  have hsum : (∑ j, (F - G) j) = t := by rw [ht', sum_four_const]
  have hsum0 : (∑ j, (F - G) j) = 0 := by
    have h : (∑ j, (F j - G j)) = (∑ j, F j) - (∑ j, G j) :=
      Finset.sum_sub_distrib (s := Finset.univ) (f := F) (g := G)
    rw [show (∑ j, (F - G) j) = ∑ j, (F j - G j) from rfl, h, hF, hG, sub_self]
  have ht0 : t = 0 := by rw [← hsum, hsum0]
  funext j
  exact sub_eq_zero.mp (by simpa [ht0] using congrFun ht' j)

private lemma mem_normalizer_of_conj {A : Subgroup Y}
    {c : Multiplicative (Fin 4 → ZMod 3) →* Y} (hc : IsSumZeroCoords A c) {n : Y}
    (τ : Equiv.Perm (Fin 4))
    (hn : ∀ v, n * c v * n⁻¹ =
      c (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (τ i))) :
    n ∈ Subgroup.normalizer (A : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hh' : h ∈ c.range := by rwa [hc.1]
    obtain ⟨v, rfl⟩ := hh'
    rw [hn v, ← hc.1]
    exact ⟨_, rfl⟩
  · intro hh
    have hh' : n * h * n⁻¹ ∈ c.range := by rwa [hc.1]
    obtain ⟨w, hw⟩ := hh'
    have hw1 : h = n⁻¹ * c w * n := by rw [hw]; group
    have hx : c (Multiplicative.ofAdd (fun i => Multiplicative.toAdd w (τ.symm i))) =
        n⁻¹ * c w * n := by
      have hstep := hn (Multiplicative.ofAdd (fun i => Multiplicative.toAdd w (τ.symm i)))
      have hcomp : (fun i => Multiplicative.toAdd (Multiplicative.ofAdd
          (fun i => Multiplicative.toAdd w (τ.symm i))) (τ i)) = Multiplicative.toAdd w := by
        funext i; simp
      rw [hcomp, ofAdd_toAdd] at hstep
      rw [← hstep]; group
    rw [hw1, ← hc.1]
    exact ⟨Multiplicative.ofAdd (fun i => Multiplicative.toAdd w (τ.symm i)), hx⟩

private lemma matrix_eq_of_single (M : Fin 4 → Fin 4 → ZMod 3)
    (ρ σ : Equiv.Perm (Fin 4))
    (hFG : ∀ v : Fin 4 → ZMod 3,
      (fun j => ∑ i, M j i * v (σ.symm i)) = fun j => ∑ i, M (ρ j) i * v i) :
    ∀ j i, M j (σ i) = M (ρ j) i := by
  intro j i
  have h := congrFun (hFG (Pi.single i (1 : ZMod 3))) j
  have hF : (∑ k, M j k * (Pi.single i (1 : ZMod 3) : Fin 4 → ZMod 3) (σ.symm k)) =
      M j (σ i) := by
    rw [Finset.sum_eq_single (σ i)]
    · simp
    · intro c _ hc
      have hne : σ.symm c ≠ i := fun hci => hc (by
        have := congrArg σ hci
        simpa using this)
      rw [Pi.single_eq_of_ne hne, mul_zero]
    · intro hσ; exact absurd (Finset.mem_univ (σ i)) hσ
  have hG : (∑ k, M (ρ j) k * (Pi.single i (1 : ZMod 3) : Fin 4 → ZMod 3) k) =
      M (ρ j) i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hc; rw [Pi.single_eq_of_ne hc, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hF, hG] at h
  exact h

theorem compare_intertwine {A : Subgroup Y} {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    (hc : IsSumZeroCoords A c) (h₀r : c₀.range = A)
    (h₀k : ∀ v, c₀ v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t)
    (h₀n : ∀ n ∈ Subgroup.normalizer (A : Set Y), ∃ ρ : Equiv.Perm (Fin 4), ∀ v,
      n * c₀ v * n⁻¹ = c₀ (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (ρ i)))
    (M : Fin 4 → Fin 4 → ZMod 3)
    (hM : ∀ v : Fin 4 → ZMod 3, c (Multiplicative.ofAdd v) =
      c₀ (Multiplicative.ofAdd fun j => ∑ i, M j i * v i))
    (hrow : ∀ j, ∑ i, M j i = 0) (hcol : ∀ i, ∑ j, M j i = 0) :
    ∀ σ : Equiv.Perm (Fin 4), ∃ ρ : Equiv.Perm (Fin 4), ∀ j i, M j (σ i) = M (ρ j) i := by
  intro σ
  obtain ⟨n, hn⟩ := hc.2.2.2 σ.symm
  obtain ⟨ρ, hρ⟩ := h₀n n (mem_normalizer_of_conj hc σ.symm hn)
  refine ⟨ρ, matrix_eq_of_single M ρ σ ?_⟩
  intro v
  have hF : (∑ j, ∑ i, M j i * v (σ.symm i)) = 0 := by
    simpa using sum_sum_mul_eq_zero M hcol (fun i => v (σ.symm i)) (Equiv.refl (Fin 4))
  have hG : (∑ j, ∑ i, M (ρ j) i * v i) = 0 := sum_sum_mul_eq_zero M hcol v ρ
  have heq : c₀ (Multiplicative.ofAdd (fun j => ∑ i, M j i * v (σ.symm i))) =
      c₀ (Multiplicative.ofAdd (fun j => ∑ i, M (ρ j) i * v i)) := by
    calc c₀ (Multiplicative.ofAdd (fun j => ∑ i, M j i * v (σ.symm i)))
        = c (Multiplicative.ofAdd (fun i => v (σ.symm i))) :=
          (hM (fun i => v (σ.symm i))).symm
      _ = n * c (Multiplicative.ofAdd v) * n⁻¹ := by
          simpa using (hn (Multiplicative.ofAdd v)).symm
      _ = n * c₀ (Multiplicative.ofAdd (fun j => ∑ i, M j i * v i)) * n⁻¹ := by rw [hM v]
      _ = c₀ (Multiplicative.ofAdd (fun j => (fun j => ∑ i, M j i * v i) (ρ j))) := hρ _
      _ = c₀ (Multiplicative.ofAdd (fun j => ∑ i, M (ρ j) i * v i)) := rfl
  exact eq_of_const_ker h₀k hF hG heq

private lemma card_filter_sum_zero :
    ((Finset.univ : Finset (Fin 4 → ZMod 3)).filter (fun w => ∑ i, w i = 0)).card = 27 := by
  decide +kernel

private lemma card_filter_eq_zero (j : Fin 4) :
    ((Finset.univ : Finset (Fin 4 → ZMod 3)).filter
      (fun y => y j = 0 ∧ ∑ k, y k = 0)).card = 9 := by
  decide +revert

private lemma card_filter_eq_eq (j₁ j₂ : Fin 4) (h : j₁ ≠ j₂) :
    ((Finset.univ : Finset (Fin 4 → ZMod 3)).filter
      (fun y => y j₁ = y j₂ ∧ ∑ k, y k = 0)).card = 9 := by
  decide +revert

private lemma mapM_injOn (M : Fin 4 → Fin 4 → ZMod 3)
    (hinj : ∀ w : Fin 4 → ZMod 3, ∑ i, w i = 0 → (∀ j, ∑ i, M j i * w i = 0) → w = 0)
    {a b : Fin 4 → ZMod 3} (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0)
    (hab : (fun j => ∑ i, M j i * a i) = fun j => ∑ i, M j i * b i) : a = b := by
  have h1 : (∑ i, (a - b) i) = 0 := by
    have h : (∑ i, (a i - b i)) = (∑ i, a i) - (∑ i, b i) :=
      Finset.sum_sub_distrib (s := Finset.univ) (f := a) (g := b)
    rw [show (∑ i, (a - b) i) = ∑ i, (a i - b i) from by simp only [Pi.sub_apply],
      h, ha, hb, sub_self]
  have h2 : ∀ j, ∑ i, M j i * (a - b) i = 0 := by
    intro j
    have hsub : (∑ i, M j i * (a - b) i) =
        (∑ i, M j i * a i) - (∑ i, M j i * b i) := by
      have h : (∑ i, (M j i * a i - M j i * b i)) =
          (∑ i, M j i * a i) - (∑ i, M j i * b i) :=
        Finset.sum_sub_distrib (s := Finset.univ) (f := fun i => M j i * a i)
          (g := fun i => M j i * b i)
      rw [show (∑ i, M j i * (a - b) i) = ∑ i, (M j i * a i - M j i * b i) from
        Finset.sum_congr rfl (fun i _ => by rw [Pi.sub_apply, mul_sub]), h]
    rw [hsub, show (∑ i, M j i * a i) = (∑ i, M j i * b i) from congrFun hab j, sub_self]
  exact sub_eq_zero.mp (hinj (a - b) h1 h2)

theorem rows_nonzero_inj (M : Fin 4 → Fin 4 → ZMod 3) (hcol : ∀ i, ∑ j, M j i = 0)
    (hinj : ∀ w : Fin 4 → ZMod 3, ∑ i, w i = 0 → (∀ j, ∑ i, M j i * w i = 0) → w = 0) :
    (∀ j, M j ≠ 0) ∧ Function.Injective M := by
  classical
  let S : Finset (Fin 4 → ZMod 3) := Finset.univ.filter (fun w => ∑ i, w i = 0)
  let mapM : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3) := fun w j => ∑ i, M j i * w i
  have hS : S.card = 27 := card_filter_sum_zero
  have hmemS : ∀ {w : Fin 4 → ZMod 3}, w ∈ S → ∑ i, w i = 0 := by
    intro w hw
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact hw
  have hmap_sum : ∀ w ∈ S, (∑ k, mapM w k) = 0 := by
    intro w hw
    rw [show (∑ k, mapM w k) = ∑ k, ∑ i, M k i * w i from rfl, Finset.sum_comm]
    simp [← Finset.sum_mul, hcol]
  have hinjS : (S : Set (Fin 4 → ZMod 3)).InjOn mapM := by
    intro a ha b hb hab
    exact mapM_injOn M hinj (hmemS ha) (hmemS hb) hab
  refine ⟨?_, ?_⟩
  · intro j hj
    have hT : ((Finset.univ : Finset (Fin 4 → ZMod 3)).filter
        (fun y => y j = 0 ∧ ∑ k, y k = 0)).card = 9 := card_filter_eq_zero j
    have himg : Set.MapsTo mapM (S : Set (Fin 4 → ZMod 3))
        (((Finset.univ : Finset (Fin 4 → ZMod 3)).filter
          (fun y => y j = 0 ∧ ∑ k, y k = 0)) : Set (Fin 4 → ZMod 3)) := by
      intro w hw
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · simp [mapM, hj]
      · exact hmap_sum w hw
    have := Finset.card_le_card_of_injOn mapM himg hinjS
    rw [hS, hT] at this
    omega
  · intro j₁ j₂ hj
    by_contra hne
    have hT : ((Finset.univ : Finset (Fin 4 → ZMod 3)).filter
        (fun y => y j₁ = y j₂ ∧ ∑ k, y k = 0)).card = 9 := card_filter_eq_eq j₁ j₂ hne
    have himg : Set.MapsTo mapM (S : Set (Fin 4 → ZMod 3))
        (((Finset.univ : Finset (Fin 4 → ZMod 3)).filter
          (fun y => y j₁ = y j₂ ∧ ∑ k, y k = 0)) : Set (Fin 4 → ZMod 3)) := by
      intro w hw
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · simp [mapM, hj]
      · exact hmap_sum w hw
    have := Finset.card_le_card_of_injOn mapM himg hinjS
    rw [hS, hT] at this
    omega

private lemma zmod_mul_sub_neg (ε a b : ZMod 3) :
    ε * (a - b) = -ε * b - -ε * a := by
  decide +revert

theorem compare_coords {A : Subgroup Y} {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    (hc : IsSumZeroCoords A c) (h₀r : c₀.range = A)
    (h₀k : ∀ v, c₀ v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t)
    (h₀n : ∀ n ∈ Subgroup.normalizer (A : Set Y), ∃ ρ : Equiv.Perm (Fin 4), ∀ v,
      n * c₀ v * n⁻¹ = c₀ (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (ρ i))) :
    ∃ (ε : ZMod 3) (τ : Equiv.Perm (Fin 4)), ε ≠ 0 ∧ ∀ v,
      c v = c₀ (Multiplicative.ofAdd fun i => ε * Multiplicative.toAdd v (τ i)) := by
  obtain ⟨M, hM, hrow, hcol, hinj⟩ := compare_columns hc h₀r h₀k
  have hinv : ∀ (σ : Equiv.Perm (Fin 4)) (j : Fin 4), ∃ j', ∀ i, M j (σ i) = M j' i := by
    intro σ j
    obtain ⟨ρ, hρ⟩ := compare_intertwine hc h₀r h₀k h₀n M hM hrow hcol σ
    exact ⟨ρ j, hρ j⟩
  obtain ⟨hne, hinjM⟩ := rows_nonzero_inj M hcol hinj
  obtain ⟨ε₁, τ, hε₁, hMrow⟩ := weights_of_invariant M hrow hne hinjM hinv
  refine ⟨-ε₁, τ, neg_ne_zero.mpr hε₁, ?_⟩
  intro v
  have key : ∀ w : Fin 4 → ZMod 3,
      c (Multiplicative.ofAdd w) = c₀ (Multiplicative.ofAdd fun i => -ε₁ * w (τ i)) := by
    intro w
    have hrowval : ∀ j, (∑ i, M j i * w i) = ε₁ * ((∑ i, w i) - w (τ j)) := by
      intro j
      calc (∑ i, M j i * w i)
          = ∑ i, (if i = τ j then (0 : ZMod 3) else ε₁) * w i :=
              Finset.sum_congr rfl (fun i _ => by rw [hMrow j i])
        _ = ∑ i, (if i = τ j then (0 : ZMod 3) else ε₁ * w i) :=
              Finset.sum_congr rfl (fun i _ => by by_cases h : i = τ j <;> simp [h])
        _ = (∑ i, ε₁ * w i) - ∑ i, (if i = τ j then ε₁ * w i else 0) := by
              have h : (∑ i, (ε₁ * w i - (if i = τ j then ε₁ * w i else 0))) =
                  (∑ i, ε₁ * w i) - ∑ i, (if i = τ j then ε₁ * w i else 0) :=
                Finset.sum_sub_distrib (s := Finset.univ) (f := fun i => ε₁ * w i)
                  (g := fun i => if i = τ j then ε₁ * w i else 0)
              rw [← h]
              exact Finset.sum_congr rfl (fun i _ => by
                by_cases hh : i = τ j <;> simp [hh] <;> ring)
        _ = ε₁ * (∑ i, w i) - ε₁ * w (τ j) := by
              rw [Finset.mul_sum, Finset.sum_ite_eq']
              simp
        _ = ε₁ * ((∑ i, w i) - w (τ j)) := by ring
    have hsumtau : (∑ k, -ε₁ * w (τ k)) = -ε₁ * (∑ k, w k) := by
      rw [Equiv.sum_comp τ (fun k => -ε₁ * w k), Finset.mul_sum]
    have hMw : (fun j => ∑ i, M j i * w i) =
        fun j => (-ε₁ * w (τ j)) - ∑ k, (-ε₁ * w (τ k)) := by
      funext j
      rw [hrowval j, hsumtau]
      exact zmod_mul_sub_neg ε₁ (∑ i, w i) (w (τ j))
    rw [hM w, hMw, map_sub_const h₀k (fun i => -ε₁ * w (τ i))]
  simpa using key (Multiplicative.toAdd v)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
