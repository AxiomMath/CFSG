module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherMaximalParabolics
import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec19.KS1919U48Proof

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

theorem sum_bar_mul_partner {r ε : ℕ} {h : UnitaryFieldData p f K} (g : hypSU h r ε)
    (a b : HypIndex r ε) :
    ∑ c, h.bar (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) c a) *
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (hypPartner c) b =
        hypGram r ε K a b := by
  have h1 := congrFun (congrFun (mem_hypSU.mp g.2).1 a) b
  rw [Matrix.mul_assoc, Matrix.mul_apply] at h1
  simpa [hypGram_mul_apply] using h1

theorem mulVec_mem_of_mem_isoStabilizer {r ε : ℕ} {h : UnitaryFieldData p f K}
    {W : Submodule K (HypIndex r ε → K)} {g : hypSU h r ε} (hg : g ∈ isoStabilizer h r ε W)
    {v : HypIndex r ε → K} (hv : v ∈ W) :
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ W := by
  rw [← mem_isoStabilizer.mp hg]
  exact Submodule.smul_mem_pointwise_smul v g W hv

theorem entry_eq_zero_of_mem_isoStabilizer {r ε : ℕ} {h : UnitaryFieldData p f K} (hε : ε ≤ 1)
    {i : ℕ} (hi : i ≤ 2 * r + ε) {g : hypSU h r ε}
    (hg : g ∈ isoStabilizer h r ε (hypFlag h r ε i)) {a c : HypIndex r ε}
    (hc : fullPos c < i) (ha : i ≤ fullPos a) :
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a c = 0 := by
  have hv : (Pi.single c (1 : K) : HypIndex r ε → K) ∈ hypFlag h r ε i := by
    rw [hypFlag_eq_posFlag h hε hi]
    intro b hb
    have : b ≠ c := by
      rintro rfl
      omega
    simp [this]
  have h1 := mulVec_mem_of_mem_isoStabilizer hg hv
  rw [hypFlag_eq_posFlag h hε hi] at h1
  have h2 := h1 a ha
  rwa [mulVec_single_one, col_apply] at h2

theorem det_eq_prod_diag {m R : Type*} [Fintype m] [DecidableEq m] [CommRing R]
    {M : Matrix m m R} {b : m → ℕ} (hb : Function.Injective b) (hM : M.BlockTriangular b) :
    M.det = ∏ a, M a a := by
  rw [hM.det, Finset.prod_image fun x _ y _ hxy => hb hxy]
  refine Finset.prod_congr rfl fun a _ => ?_
  have : Subsingleton {x // b x = b a} := ⟨fun x y => Subtype.ext (hb (x.2.trans y.2.symm))⟩
  rw [Matrix.det_eq_elem_of_subsingleton _ ⟨a, rfl⟩]
  rfl

theorem prod_diag (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K) :
    ∏ a, M a a = M (.inl 0) (.inl 0) * M (.inl 1) (.inl 1) *
      (M (.inr (.inr 0)) (.inr (.inr 0)) * M (.inr (.inr 1)) (.inr (.inr 1))) := by
  simp [Fintype.prod_sum_type, Fin.prod_univ_two]

theorem eq_one_of_mem_hypUnitriangular {h : UnitaryFieldData p f K} (hp3 : p ≠ 3)
    {g : hypSU h 2 0} (hg : g ∈ hypUnitriangular h 2 0) (h3 : g ^ 3 = 1) : g = 1 := by
  set u : hypUnitriangular h 2 0 := ⟨g, hg⟩
  have hu3 : u ^ 3 = 1 := Subtype.ext h3
  have h1 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  have h2 : orderOf u ∣ (p ^ f) ^ 6 := by
    have := orderOf_dvd_natCard u
    rwa [card_hypUnitriangular h (by norm_num)] at this
  have hcop : Nat.Coprime 3 ((p ^ f) ^ 6) :=
    Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _
      ((Nat.coprime_primes Nat.prime_three h.prime).mpr (Ne.symm hp3)))
  have h4 : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h4)

theorem three_ne_zero_of_ne (h : UnitaryFieldData p f K) (hp3 : p ≠ 3) : (3 : K) ≠ 0 := by
  have : CharP K p := h.charP
  intro h0
  have : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).mp (by exact_mod_cast h0)
  exact hp3 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp this)

theorem card_le_nine_of_hom [Finite K] (h3 : (3 : K) ≠ 0) {G : Type*} [Group G]
    {Q : Subgroup G} (Φ : Q →* GL (Fin 2) K) (B : Subgroup G) (hBQ : B ≤ Q)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hexp : ∀ x ∈ B, x ^ 3 = 1)
    (hker : ∀ x (hx : x ∈ B), Φ ⟨x, hBQ hx⟩ = 1 → x = 1) : Nat.card B ≤ 9 := by
  set ψ : B →* GL (Fin 2) K := Φ.comp (Subgroup.inclusion hBQ) with hψ
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact (Subgroup.mem_bot).mpr (Subtype.ext (hker x x.2 hx))
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hc : ∀ g ∈ ψ.range, ∀ g' ∈ ψ.range, g * g' = g' * g := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, show x * y = y * x from Subtype.ext (hcomm x x.2 y y.2)]
  have he : ∀ g ∈ ψ.range, g ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow, show x ^ 3 = 1 from Subtype.ext (hexp x x.2), map_one]
  have := CFSG.RankThree.PartOne.LIT.card_le_pow_card_gl Nat.prime_three
    (by exact_mod_cast h3) ψ.range hc he
  simpa using this

def topBlock (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => M (.inl i) (.inl j)

theorem topBlock_mul {M N : Matrix (HypIndex 2 0) (HypIndex 2 0) K}
    (hN : ∀ i j : Fin 2, N (.inr (.inr j)) (.inl i) = 0) :
    topBlock (M * N) = topBlock M * topBlock N := by
  ext i j
  simp [topBlock, Matrix.mul_apply, Fintype.sum_sum_type, hN]

theorem entry_eq_zero_of_mem_isoStabilizer_two {h : UnitaryFieldData p f K} {g : hypSU h 2 0}
    (hg : g ∈ isoStabilizer h 2 0 (hypFlag h 2 0 2)) (i j : Fin 2) :
    ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (.inr (.inr j))
      (.inl i) = 0 :=
  entry_eq_zero_of_mem_isoStabilizer (by norm_num) (by norm_num) hg
    (by fin_cases i <;> simp [fullPos]) (by fin_cases j <;> simp [fullPos])

variable (h : UnitaryFieldData p f K) in
noncomputable def topBlockHom : isoStabilizer h 2 0 (hypFlag h 2 0 2) →* GL (Fin 2) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => topBlock (((g : hypSU h 2 0) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      map_one' := by
        ext i j
        simp [topBlock, one_apply]
      map_mul' := fun _ g' => topBlock_mul (entry_eq_zero_of_mem_isoStabilizer_two g'.2) }

theorem mem_hypUnitriangular_of_topBlock {h : UnitaryFieldData p f K} {g : hypSU h 2 0}
    (hg : g ∈ isoStabilizer h 2 0 (hypFlag h 2 0 2))
    (h1 : topBlock (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) = 1) :
    g ∈ hypUnitriangular h 2 0 := by
  have hz := entry_eq_zero_of_mem_isoStabilizer_two hg
  have ht : ∀ i j : Fin 2, ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      (.inl i) (.inl j) = if i = j then 1 else 0 := fun i j => by
    have := congrFun (congrFun h1 i) j
    simpa [topBlock, one_apply] using this
  have hb : ∀ k l : Fin 2, ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      (.inr (.inr k)) (.inr (.inr l)) = if k = l then 1 else 0 := by
    intro k l
    have := sum_bar_mul_partner g (.inl k) (.inr (.inr l))
    fin_cases k <;> simpa [Fintype.sum_sum_type, Fin.sum_univ_two, hz, ht] using this
  rw [mem_hypUnitriangular]
  refine ⟨fun a c hac => ?_, fun a => ?_⟩
  · fin_cases a <;> fin_cases c <;> simp [fullPos] at hac <;> simp [hz, ht, hb]
  · fin_cases a <;> simp [ht, hb]

theorem card_le_nine_of_le_isoStabilizer_two (h : UnitaryFieldData p f K) (hp3 : p ≠ 3)
    (B : Subgroup (hypSU h 2 0)) (hB : B ≤ isoStabilizer h 2 0 (hypFlag h 2 0 2))
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hexp : ∀ x ∈ B, x ^ 3 = 1) :
    Nat.card B ≤ 9 := by
  have := h.finite
  refine card_le_nine_of_hom (three_ne_zero_of_ne h hp3) (topBlockHom h) B hB hcomm hexp
    fun x hx hΦ => ?_
  refine eq_one_of_mem_hypUnitriangular hp3 ?_ (hexp x hx)
  refine mem_hypUnitriangular_of_topBlock (hB hx) ?_
  have := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) hΦ
  simpa [topBlockHom] using this

def midIdx : Fin 2 → HypIndex 2 0 := ![.inl 1, .inr (.inr 1)]

def midBlock (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => M (midIdx i) (midIdx j)

theorem midBlock_mul {M N : Matrix (HypIndex 2 0) (HypIndex 2 0) K}
    (hM : ∀ a, a ≠ .inl 0 → M a (.inl 0) = 0)
    (hN : ∀ b, b ≠ .inr (.inr 0) → N (.inr (.inr 0)) b = 0) :
    midBlock (M * N) = midBlock M * midBlock N := by
  have h1 := hM (.inl 1) (by decide)
  have h2 := hM (.inr (.inr 1)) (by decide)
  have h3 := hN (.inl 1) (by decide)
  have h4 := hN (.inr (.inr 1)) (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [midBlock, midIdx, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h1, h2,
      h3, h4]

theorem corner_mul {M N : Matrix (HypIndex 2 0) (HypIndex 2 0) K}
    (hN : ∀ a, a ≠ .inl 0 → N a (.inl 0) = 0) :
    (M * N) (.inl 0) (.inl 0) = M (.inl 0) (.inl 0) * N (.inl 0) (.inl 0) := by
  have h1 := hN (.inl 1) (by decide)
  have h2 := hN (.inr (.inr 0)) (by decide)
  have h3 := hN (.inr (.inr 1)) (by decide)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h1, h2, h3]

theorem col_eq_zero_of_mem_isoStabilizer_one {h : UnitaryFieldData p f K} {g : hypSU h 2 0}
    (hg : g ∈ isoStabilizer h 2 0 (hypFlag h 2 0 1)) (a : HypIndex 2 0) (ha : a ≠ .inl 0) :
    ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) a (.inl 0) = 0 := by
  refine entry_eq_zero_of_mem_isoStabilizer (by norm_num) (by norm_num) hg (by simp [fullPos]) ?_
  fin_cases a <;> simp [fullPos] at ha ⊢

theorem bar_mul_row_of_mem_isoStabilizer_one {h : UnitaryFieldData p f K} {g : hypSU h 2 0}
    (hg : g ∈ isoStabilizer h 2 0 (hypFlag h 2 0 1)) (b : HypIndex 2 0) :
    h.bar (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (.inl 0)
      (.inl 0)) * ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
        (.inr (.inr 0)) b = hypGram 2 0 K (.inl 0) b := by
  have hc := col_eq_zero_of_mem_isoStabilizer_one hg
  have h1 := hc (.inl 1) (by decide)
  have h2 := hc (.inr (.inr 0)) (by decide)
  have h3 := hc (.inr (.inr 1)) (by decide)
  have := sum_bar_mul_partner g (.inl 0) b
  simpa [Fintype.sum_sum_type, Fin.sum_univ_two, h1, h2, h3] using this

theorem row_eq_zero_of_mem_isoStabilizer_one {h : UnitaryFieldData p f K} {g : hypSU h 2 0}
    (hg : g ∈ isoStabilizer h 2 0 (hypFlag h 2 0 1)) (b : HypIndex 2 0)
    (hb : b ≠ .inr (.inr 0)) :
    ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (.inr (.inr 0)) b =
      0 := by
  have h1 := bar_mul_row_of_mem_isoStabilizer_one hg b
  have h2 := bar_mul_row_of_mem_isoStabilizer_one hg (.inr (.inr 0))
  rw [hypGram_apply, ite_eq_right (by simpa using hb)] at h1
  rw [hypGram_apply, ite_eq_left (by simp)] at h2
  exact (mul_eq_zero.mp h1).resolve_left (left_ne_zero_of_mul_eq_one h2)

variable (h : UnitaryFieldData p f K) in
noncomputable def midBlockHom : isoStabilizer h 2 0 (hypFlag h 2 0 1) →* GL (Fin 2) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => midBlock (((g : hypSU h 2 0) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [midBlock, midIdx, one_apply]
      map_mul' := fun g g' => midBlock_mul (col_eq_zero_of_mem_isoStabilizer_one g.2)
        (row_eq_zero_of_mem_isoStabilizer_one g'.2) }

variable (h : UnitaryFieldData p f K) in
noncomputable def cornerHom : isoStabilizer h 2 0 (hypFlag h 2 0 1) →* K where
  toFun g := ((g : hypSU h 2 0) : GL (HypIndex 2 0) K) (.inl 0) (.inl 0)
  map_one' := by simp
  map_mul' _ g' := corner_mul (col_eq_zero_of_mem_isoStabilizer_one g'.2)

theorem eq_one_of_bar_eq (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2) {α : K}
    (h3 : α ^ 3 = 1) (hbar : h.bar α = α) : α = 1 := by
  have h2 : h.bar α = α ^ 2 := by
    rw [h.bar_apply, ← Nat.div_add_mod (p ^ f) 3, hq, pow_add, pow_mul, h3, one_pow, one_mul]
  have hα0 : α ≠ 0 := by
    rintro rfl
    norm_num at h3
  have : α * (α - 1) = 0 := by
    rw [mul_sub, mul_one, ← sq, ← h2, hbar, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hα0)

theorem mem_hypUnitriangular_of_midBlock {h : UnitaryFieldData p f K} (hq : p ^ f % 3 = 2)
    {g : hypSU h 2 0} (hg : g ∈ isoStabilizer h 2 0 (hypFlag h 2 0 1)) (hg3 : g ^ 3 = 1)
    (h1 : midBlock (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) = 1) :
    g ∈ hypUnitriangular h 2 0 := by
  have hc := col_eq_zero_of_mem_isoStabilizer_one hg
  have hr := row_eq_zero_of_mem_isoStabilizer_one hg
  have hbr := bar_mul_row_of_mem_isoStabilizer_one hg (.inr (.inr 0))
  rw [hypGram_apply, ite_eq_left (by simp)] at hbr
  have hm : ∀ i j : Fin 2, ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      (midIdx i) (midIdx j) = if i = j then 1 else 0 := fun i j => by
    have := congrFun (congrFun h1 i) j
    simpa [midBlock, one_apply] using this
  have m00 := hm 0 0
  have m01 := hm 0 1
  have m10 := hm 1 0
  have m11 := hm 1 1
  simp only [midIdx] at m00 m01 m10 m11
  simp at m00 m01 m10 m11
  have c1 := hc (.inl 1) (by decide)
  have c2 := hc (.inr (.inr 0)) (by decide)
  have c3 := hc (.inr (.inr 1)) (by decide)
  have r1 := hr (.inl 0) (by decide)
  have r2 := hr (.inl 1) (by decide)
  have r3 := hr (.inr (.inr 1)) (by decide)
  have hlow : (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)).BlockTriangular
      fullPos := by
    intro a c hac
    fin_cases a <;> fin_cases c <;> simp [fullPos] at hac <;> assumption
  have hα3 : (cornerHom h ⟨g, hg⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨g, hg⟩ : isoStabilizer h 2 0 (hypFlag h 2 0 1)) ^ 3 = 1 from
      Subtype.ext hg3, map_one]
  change ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (.inl 0)
    (.inl 0) ^ 3 = 1 at hα3
  have hdet := (mem_hypSU.mp g.2).2
  rw [det_eq_prod_diag fullPos_injective hlow, prod_diag, m00, m11, mul_one, mul_one] at hdet
  have hδ0 : ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      (.inr (.inr 0)) (.inr (.inr 0)) ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  have hbar : h.bar (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      (.inl 0) (.inl 0)) = ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      (.inl 0) (.inl 0) :=
    mul_right_cancel₀ hδ0 (hbr.trans hdet.symm)
  have hα := eq_one_of_bar_eq h hq hα3 hbar
  rw [hα, one_mul] at hdet
  rw [mem_hypUnitriangular]
  refine ⟨hlow, fun a => ?_⟩
  fin_cases a <;> simp [m00, m11, hα, hdet]

theorem card_le_nine_of_le_isoStabilizer_one (h : UnitaryFieldData p f K) (hp3 : p ≠ 3)
    (hq : p ^ f % 3 = 2) (B : Subgroup (hypSU h 2 0))
    (hB : B ≤ isoStabilizer h 2 0 (hypFlag h 2 0 1))
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hexp : ∀ x ∈ B, x ^ 3 = 1) :
    Nat.card B ≤ 9 := by
  have := h.finite
  refine card_le_nine_of_hom (three_ne_zero_of_ne h hp3) (midBlockHom h) B hB hcomm hexp
    fun x hx hΦ => ?_
  refine eq_one_of_mem_hypUnitriangular hp3 ?_ (hexp x hx)
  refine mem_hypUnitriangular_of_midBlock hq (hB hx) (hexp x hx) ?_
  have := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) hΦ
  simpa [midBlockHom] using this

theorem card_le_nine_of_le_isoStabilizer (h : UnitaryFieldData p f K) (hp3 : p ≠ 3)
    (hq : p ^ f % 3 = 2) {W : Submodule K (HypIndex 2 0 → K)} (hW0 : W ≠ ⊥)
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 0 x y = 0) (B : Subgroup (hypSU h 2 0))
    (hB : B ≤ isoStabilizer h 2 0 W)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hexp : ∀ x ∈ B, x ^ 3 = 1) :
    Nat.card B ≤ 9 := by
  obtain ⟨hd1, hd2, g, hg⟩ := exists_smul_hypFlag_eq h (by norm_num) hW0 hW
  set d := Module.finrank K W with hd
  set B' := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'
  have hcard : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hB'le : B' ≤ isoStabilizer h 2 0 (hypFlag h 2 0 d) := by
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hB
    rwa [isoStabilizer_map_conj, ← hg, inv_smul_smul] at this
  have hcomm' : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hexp' : ∀ x ∈ B', x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  rw [← hcard]
  obtain hd' | hd' : d = 1 ∨ d = 2 := by omega
  · rw [hd'] at hB'le
    exact card_le_nine_of_le_isoStabilizer_one h hp3 hq B' hB'le hcomm' hexp'
  · rw [hd'] at hB'le
    exact card_le_nine_of_le_isoStabilizer_two h hp3 B' hB'le hcomm' hexp'

theorem card_le_nine_of_le_parabolic (h : UnitaryFieldData 2 f K) (hf : Odd f)
    {P : Subgroup (hypPSU h 2 0)} (hP : P ≠ ⊤) (T : Sylow 2 (hypPSU h 2 0))
    (hTP : Subgroup.normalizer ((T : Subgroup (hypPSU h 2 0)) : Set (hypPSU h 2 0)) ≤ P)
    (B : Subgroup (hypPSU h 2 0)) (hBP : B ≤ P)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hexp : ∀ x ∈ B, x ^ 3 = 1) :
    Nat.card B ≤ 9 := by
  have hq : 2 ^ f % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hf
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  obtain ⟨M, hM, hPM⟩ := (eq_top_or_exists_le_coatom P).resolve_left hP
  have hMmax : M ∈ maximalParabolics h 2 0 := ⟨hM, _, ⟨T, rfl⟩, hTP.trans hPM⟩
  rw [(unitary_maximal_parabolics h (by norm_num) (by norm_num)).1] at hMmax
  obtain ⟨W, ⟨hW0, hW⟩, rfl⟩ := hMmax
  have hodd : Odd (2 ^ f + 1) :=
    (Nat.even_pow.mpr ⟨even_two, by obtain ⟨k, rfl⟩ := hf; omega⟩).add_one
  have hZ : hypScalars h 2 0 = ⊥ := by
    rw [← Subgroup.card_eq_one, card_hypScalars h (by norm_num)]
    exact (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) : Nat.Coprime (2 ^ 2) _)
  have hinj : Function.Injective (hypProj h 2 0) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_hypProj, hZ]
  set B₁ := B.comap (hypProj h 2 0) with hB₁
  have hcard : Nat.card B₁ = Nat.card B := by
    rw [← Subgroup.card_map_of_injective hinj, hB₁,
      Subgroup.map_comap_eq_self_of_surjective (hypProj_surjective h 2 0)]
  have hB₁W : B₁ ≤ isoStabilizer h 2 0 W := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hBP.trans hPM hx
    rwa [← hinj hxy]
  have hcomm₁ : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x := fun x hx y hy =>
    hinj (by rw [map_mul, map_mul]; exact hcomm _ hx _ hy)
  have hexp₁ : ∀ x ∈ B₁, x ^ 3 = 1 := fun x hx =>
    hinj (by rw [map_pow, map_one]; exact hexp _ hx)
  rw [← hcard]
  exact card_le_nine_of_le_isoStabilizer h (by norm_num) hq hW0 hW B₁ hB₁W hcomm₁ hexp₁

end CFSG.RankThree.PartTwo.Sec19.KS1919U48Proof
