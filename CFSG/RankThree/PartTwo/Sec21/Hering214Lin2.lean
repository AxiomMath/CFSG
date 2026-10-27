module

public import CFSG.RankThree.PartTwo.Sec21.Hering214Syl
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.RankThree.PartTwo.Sec21.Hering214L3Std

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Assembly (IsElemAbelian)

section Out

variable {K : Type} [Field K] [Finite K]

theorem exists_conjAut_of_pow_three_eq_one (hσ : ∀ σ : K ≃+* K, σ = 1) {n : ℕ} (hn : 3 ≤ n)
    {α : MulAut (projectiveSL n K)} (hα : α ^ 3 = 1) :
    ∃ A : GL (Fin n) K, α = conjAut n K A := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
  obtain ⟨hmul, -, -, hδδ, hδc, -⟩ := standard_automorphism_transport (K := K) (n := n)
  have hσ1 : fieldAut n K σ = 1 := by rw [hσ σ]; exact map_one _
  rw [hσ1, mul_one] at hα ⊢
  interval_cases ε
  · exact ⟨A, by simp⟩
  · have hα2 : (conjAut n K A * dualAut n K ^ 1) ^ 2 =
        conjAut n K (A * Matrix.GeneralLinearGroup.inverseTranspose A) := by
      rw [pow_one, sq]
      calc conjAut n K A * dualAut n K * (conjAut n K A * dualAut n K) =
          conjAut n K A * (dualAut n K * conjAut n K A * dualAut n K) := by
            simp only [mul_assoc]
        _ = conjAut n K A * conjAut n K (Matrix.GeneralLinearGroup.inverseTranspose A) := by
            rw [hδc]
        _ = conjAut n K (A * Matrix.GeneralLinearGroup.inverseTranspose A) := hmul _ _
    refine ⟨(A * Matrix.GeneralLinearGroup.inverseTranspose A)⁻¹, ?_⟩
    rw [map_inv, ← hα2]
    rw [eq_inv_iff_mul_eq_one, ← pow_succ']
    exact hα

end Out

section Explicit

variable {S Y : Type} [Group S] [Group Y] [Finite Y]

theorem exists_pow_mul_pow_of_mem_closure {H : Type*} [Group H] {a b : H} (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (hab : a * b = b * a) {x : H}
    (hx : x ∈ Subgroup.closure ({a, b} : Set H)) : ∃ i j : ℕ, x = a ^ i * b ^ j := by
  have hba : b * a = a * b := hab.symm
  have hcomm : ∀ (i j : ℕ), b ^ j * a ^ i = a ^ i * b ^ j := fun i j =>
    ((Commute.pow_pow (Commute.symm (show Commute a b from hab)) j i)).eq
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul y z _ _ hy hz =>
    obtain ⟨i, j, rfl⟩ := hy
    obtain ⟨k, l, rfl⟩ := hz
    refine ⟨i + k, j + l, ?_⟩
    calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by
          simp only [mul_assoc]
      _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [hcomm k j]
      _ = a ^ (i + k) * b ^ (j + l) := by rw [pow_add, pow_add]; simp only [mul_assoc]
  | inv y _ hy =>
    obtain ⟨i, j, rfl⟩ := hy
    refine ⟨2 * i, 2 * j, ?_⟩
    have hai : (a ^ i)⁻¹ = a ^ (2 * i) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, ha3, one_pow]
    have hbj : (b ^ j)⁻¹ = b ^ (2 * j) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hb3, one_pow]
    rw [_root_.mul_inv_rev, hai, hbj, hcomm]

@[expose] def Four4 (u₁ u₂ w : S) : Prop := w = 1 ∨ w = u₁ ∨ w = u₂ ∨ w = u₁ * u₂

theorem Four4.left (u₁ u₂ : S) : Four4 u₁ u₂ u₁ := Or.inr (Or.inl rfl)

theorem Four4.right (u₁ u₂ : S) : Four4 u₁ u₂ u₂ := Or.inr (Or.inr (Or.inl rfl))

theorem Four4.mul (u₁ u₂ : S) : Four4 u₁ u₂ (u₁ * u₂) := Or.inr (Or.inr (Or.inr rfl))

theorem eInvFourFact_of_explicit (ι : S →* Y) (hι : Function.Injective ι)
    (hZ : Subgroup.center Y = ⊥)
    (hout : ∀ α : MulAut Y, α ^ 3 = 1 → ∃ y : Y, α = MulAut.conj y)
    (hsyl : ∀ P : Sylow 3 Y, Nat.card P = 9)
    {a b u₁ u₂ : S} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hdist : ∀ i j k l : Fin 3, a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) →
      i = k ∧ j = l)
    (hu₁ : u₁ * u₁ = 1) (hu₂ : u₂ * u₂ = 1) (hu : u₁ * u₂ = u₂ * u₁) (hu₁1 : u₁ ≠ 1)
    (hu₂1 : u₂ ≠ 1) (hu₁₂ : u₁ ≠ u₂) {va₁ va₂ vb₁ vb₂ : S}
    (hva₁ : Four4 u₁ u₂ va₁) (hva₂ : Four4 u₁ u₂ va₂) (hvb₁ : Four4 u₁ u₂ vb₁)
    (hvb₂ : Four4 u₁ u₂ vb₂) (ha₁ : a * u₁ = va₁ * a) (ha₂ : a * u₂ = va₂ * a)
    (hb₁ : b * u₁ = vb₁ * b) (hb₂ : b * u₂ = vb₂ * b) (hmove : a * u₁ ≠ u₁ * a) :
    EInvFourFact Y := by
  have hconj : ∀ (g t v : S), g * t = v * g → g * t * g⁻¹ = v := fun g t v h => by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have haw : Four4 u₁ u₂ (a * u₁ * a⁻¹) ∧ Four4 u₁ u₂ (a * u₂ * a⁻¹) := by
    rw [hconj a u₁ va₁ ha₁, hconj a u₂ va₂ ha₂]
    exact ⟨hva₁, hva₂⟩
  have hbw : Four4 u₁ u₂ (b * u₁ * b⁻¹) ∧ Four4 u₁ u₂ (b * u₂ * b⁻¹) := by
    rw [hconj b u₁ vb₁ hb₁, hconj b u₂ vb₂ hb₂]
    exact ⟨hvb₁, hvb₂⟩
  have hmove' : a * u₁ * a⁻¹ ≠ u₁ := fun h => hmove (mul_inv_eq_iff_eq_mul.mp h)
  have hia3 : ι a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hib3 : ι b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hiab : ι a * ι b = ι b * ι a := by rw [← map_mul, ← map_mul, hab]
  have hiu₁ : ι u₁ * ι u₁ = 1 := by rw [← map_mul, hu₁, map_one]
  have hiu₂ : ι u₂ * ι u₂ = 1 := by rw [← map_mul, hu₂, map_one]
  have hiu : ι u₁ * ι u₂ = ι u₂ * ι u₁ := by rw [← map_mul, ← map_mul, hu]
  have hiu₁1 : ι u₁ ≠ 1 := fun h => hu₁1 (hι (by rw [h, map_one]))
  have hiu₂1 : ι u₂ ≠ 1 := fun h => hu₂1 (hι (by rw [h, map_one]))
  have hiu₁₂ : ι u₁ ≠ ι u₂ := fun h => hu₁₂ (hι h)
  set E₀ : Subgroup Y := Subgroup.closure ({ι a, ι b} : Set Y) with hE₀
  set W₀ : Subgroup Y := Subgroup.closure ({ι u₁, ι u₂} : Set Y) with hW₀
  have hE₀exp : ∀ x ∈ E₀, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := exists_pow_mul_pow_of_mem_closure hia3 hib3 hiab hx
    rw [Commute.mul_pow (Commute.pow_pow hiab i j), ← pow_mul, ← pow_mul, mul_comm i 3,
      mul_comm j 3, pow_mul, pow_mul, hia3, hib3, one_pow, one_pow, one_mul]
  have hE₀card : 9 ≤ Nat.card E₀ := by
    let f : Fin 3 × Fin 3 → E₀ := fun p => ⟨ι a ^ (p.1 : ℕ) * ι b ^ (p.2 : ℕ),
      Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _
          (Set.mem_singleton _))) _)⟩
    have hf : Function.Injective f := by
      rintro ⟨i, j⟩ ⟨k, l⟩ h
      have h1 : ι a ^ (i : ℕ) * ι b ^ (j : ℕ) = ι a ^ (k : ℕ) * ι b ^ (l : ℕ) :=
        congrArg Subtype.val h
      have h2 : a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) := by
        apply hι
        simpa [map_mul, map_pow] using h1
      obtain ⟨rfl, rfl⟩ := hdist i j k l h2
      rfl
    have := Nat.card_le_card_of_injective f hf
    simpa [Nat.card_prod] using this
  have hmemW : ∀ t : S, Four4 u₁ u₂ t → ι t ∈ W₀ := by
    intro t ht
    rcases ht with rfl | rfl | rfl | rfl
    · rw [map_one]; exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · rw [map_mul]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hmapW : ∀ g : S, Four4 u₁ u₂ (g * u₁ * g⁻¹) → Four4 u₁ u₂ (g * u₂ * g⁻¹) →
      ∀ w ∈ W₀, ι g * w * (ι g)⁻¹ ∈ W₀ := by
    intro g h1 h2 w hw
    have hle : W₀.map (MulAut.conj (ι g)).toMonoidHom ≤ W₀ := by
      rw [hW₀, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with rfl | hx
      · have := hmemW _ h1
        simpa [MulAut.conj_apply] using this
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        have := hmemW _ h2
        simpa [MulAut.conj_apply] using this
    exact hle ⟨w, hw, rfl⟩
  have hinv : ∀ e ∈ E₀, ∀ w ∈ W₀, e * w * e⁻¹ ∈ W₀ := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact hmapW a haw.1 haw.2
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hmapW b hbw.1 hbw.2
    | one => intro w hw; simpa using hw
    | mul x y _ _ hx hy =>
      intro w hw
      have := hx _ (hy w hw)
      simpa [mul_assoc] using this
    | inv x _ hx =>
      intro w hw
      let f : W₀ → W₀ := fun v => ⟨x * v * x⁻¹, hx v v.2⟩
      have hfinj : Function.Injective f := by
        intro v v' h
        have h' : x * (v : Y) * x⁻¹ = x * (v' : Y) * x⁻¹ := congrArg Subtype.val h
        exact Subtype.ext (by simpa using h')
      obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hfinj) ⟨w, hw⟩
      have hv' : x * v * x⁻¹ = w := congrArg Subtype.val hv
      have : x⁻¹ * w * (x⁻¹)⁻¹ = v := by
        rw [← hv']; group
      rw [this]
      exact v.2
  have hW₀ab : IsElemAbelian 2 W₀ := isElemAbelian_closure_pair hiu₁ hiu₂ hiu
  have hW₀4 : Nat.card W₀ = 4 := card_closure_pair hiu₁ hiu₂ hiu hiu₁1 hiu₂1 hiu₁₂
  refine eInvFourFact_of_sylow hZ hout hsyl hE₀card hE₀exp hW₀ab hW₀4 hinv ?_
  refine ⟨ι a, Subgroup.subset_closure (Set.mem_insert _ _), ι u₁,
    Subgroup.subset_closure (Set.mem_insert _ _), fun h => hmove' (hι ?_)⟩
  rw [map_mul, map_mul, map_inv]
  exact h

end Explicit

section Two

variable {K : Type} [Field K] [Finite K]

theorem subsingleton_units_of_natCard_eq_two (hK : Nat.card K = 2) : Subsingleton Kˣ :=
  (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, hK])).1

theorem eq_zero_or_eq_one_of_natCard_eq_two (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  haveI := subsingleton_units_of_natCard_eq_two hK
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    have h : Units.mk0 x hx = 1 := Subsingleton.elim _ _
    simpa using congrArg Units.val h

theorem ringEquiv_eq_one_of_natCard_eq_two (hK : Nat.card K = 2) (σ : K ≃+* K) : σ = 1 := by
  ext x
  rcases eq_zero_or_eq_one_of_natCard_eq_two hK x with rfl | rfl
  · simp
  · simp

theorem charP_two_of_natCard_eq_two (hK : Nat.card K = 2) : CharP K 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hK)

theorem det_eq_one_of_natCard_eq_two (hK : Nat.card K = 2) {n : ℕ} (A : GL (Fin n) K) :
    Matrix.GeneralLinearGroup.det A = 1 := by
  haveI := subsingleton_units_of_natCard_eq_two hK
  exact Subsingleton.elim _ _

theorem scalars_eq_bot_of_natCard_eq_two (hK : Nat.card K = 2) {n : ℕ} (hn : 1 ≤ n) :
    scalars n K = ⊥ := by
  have h := card_scalars_dvd (K := K) hn
  rw [hK] at h
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp h)

theorem center_projectiveSL_eq_bot (hK : Nat.card K = 2) {n : ℕ} (hn : 1 ≤ n) :
    Subgroup.center (projectiveSL n K) = ⊥ := by
  have hsc := scalars_eq_bot_of_natCard_eq_two hK hn
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨g, rfl⟩ := proj_surjective n K y
  rw [Subgroup.mem_bot]
  have hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 := Subgroup.mem_center_iff.mp hy (proj n K h)
    rw [← map_mul, ← map_mul, proj_eq_proj_iff, hsc, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  rw [← scalars_eq_center, hsc, Subgroup.mem_bot] at hg
  rw [hg, map_one]

theorem inner_of_pow_three_eq_one (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    {α : MulAut (projectiveSL n K)} (hα : α ^ 3 = 1) :
    ∃ y : projectiveSL n K, α = MulAut.conj y := by
  obtain ⟨A, rfl⟩ :=
    exists_conjAut_of_pow_three_eq_one (ringEquiv_eq_one_of_natCard_eq_two hK) hn hα
  obtain ⟨y, hy⟩ := conjAut_mem_range_conj_of_det_eq_pow (A := A) (μ := 1)
    (by rw [det_eq_one_of_natCard_eq_two hK A, one_pow])
  exact ⟨y, hy.symm⟩

@[expose] noncomputable def embedTwo (K : Type) [Field K] [CharP K 2] (n : ℕ) :
    SpecialLinearGroup (Fin n) (ZMod 2) →* projectiveSL n K :=
  (proj n K).comp (SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) K))

theorem embedTwo_injective [CharP K 2] (hK : Nat.card K = 2) {n : ℕ} (hn : 1 ≤ n) :
    Function.Injective (embedTwo K n) := by
  intro g h hgh
  have h1 := proj_eq_proj_iff.mp hgh
  rw [scalars_eq_bot_of_natCard_eq_two hK hn, Subgroup.mem_bot, inv_mul_eq_one] at h1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h2 := congrArg (fun A : SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j)
    h1
  exact (ZMod.castHom (dvd_refl 2) K).injective (by simpa using h2)

end Two

section Orders

variable {K : Type} [Field K] [Finite K]

theorem card_specialLinearGroup_four (hK : Nat.card K = 2) :
    Nat.card (SpecialLinearGroup (Fin 4) K) = 20160 := by
  rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).toEquiv]
  exact CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two hK

theorem card_specialLinearGroup_five (hK : Nat.card K = 2) :
    Nat.card (SpecialLinearGroup (Fin 5) K) = 9999360 := by
  rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 K).toEquiv]
  exact CFSG.Open.StatedAPI.card_statedSL_five_of_card_eq_two hK

theorem card_sylow_three_four (hK : Nat.card K = 2) (P : Sylow 3 (projectiveSL 4 K)) :
    Nat.card P = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (projectiveSL 4 K) = 20160 := by
    rw [card_projectiveSL, scalars_eq_bot_of_natCard_eq_two hK (by norm_num), Subgroup.card_bot,
      Nat.div_one]
    exact card_specialLinearGroup_four hK
  rw [P.card_eq_multiplicity, hcard, Nat.factorization_def _ Nat.prime_three]
  have : padicValNat 3 20160 = 2 := by decide +kernel
  rw [this]
  norm_num

theorem card_sylow_three_five (hK : Nat.card K = 2) (P : Sylow 3 (projectiveSL 5 K)) :
    Nat.card P = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (projectiveSL 5 K) = 9999360 := by
    rw [card_projectiveSL, scalars_eq_bot_of_natCard_eq_two hK (by norm_num), Subgroup.card_bot,
      Nat.div_one]
    exact card_specialLinearGroup_five hK
  rw [P.card_eq_multiplicity, hcard, Nat.factorization_def _ Nat.prime_three]
  have : padicValNat 3 9999360 = 2 := by decide +kernel
  rw [this]
  norm_num

end Orders

section LinTwo

variable {K : Type} [Field K] [Finite K]

theorem eInvFourFact_projectiveSL_two (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    (hsyl : ∀ P : Sylow 3 (projectiveSL n K), Nat.card P = 9)
    {a b u₁ u₂ : SpecialLinearGroup (Fin n) (ZMod 2)} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a)
    (hdist : ∀ i j k l : Fin 3, a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) →
      i = k ∧ j = l)
    (hu₁ : u₁ * u₁ = 1) (hu₂ : u₂ * u₂ = 1) (hu : u₁ * u₂ = u₂ * u₁) (hu₁1 : u₁ ≠ 1)
    (hu₂1 : u₂ ≠ 1) (hu₁₂ : u₁ ≠ u₂)
    {va₁ va₂ vb₁ vb₂ : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hva₁ : Four4 u₁ u₂ va₁) (hva₂ : Four4 u₁ u₂ va₂) (hvb₁ : Four4 u₁ u₂ vb₁)
    (hvb₂ : Four4 u₁ u₂ vb₂) (ha₁ : a * u₁ = va₁ * a) (ha₂ : a * u₂ = va₂ * a)
    (hb₁ : b * u₁ = vb₁ * b) (hb₂ : b * u₂ = vb₂ * b) (hmove : a * u₁ ≠ u₁ * a) :
    EInvFourFact (projectiveSL n K) := by
  haveI := charP_two_of_natCard_eq_two hK
  exact eInvFourFact_of_explicit (embedTwo K n) (embedTwo_injective hK (by omega))
    (center_projectiveSL_eq_bot hK (by omega)) (fun α hα => inner_of_pow_three_eq_one hK hn hα)
    hsyl ha3 hb3 hab hdist hu₁ hu₂ hu hu₁1 hu₂1 hu₁₂ hva₁ hva₂ hvb₁ hvb₂ ha₁ ha₂ hb₁ hb₂ hmove

end LinTwo

section Data

theorem det_eq_one_of_mul_eq_one_two {n : ℕ} (A B : Matrix (Fin n) (Fin n) (ZMod 2))
    (h : A * B = 1) : A.det = 1 := by
  have h1 : A.det * B.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  revert h1
  generalize A.det = x
  generalize B.det = y
  revert x y
  decide

@[expose] def A4 : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def B4 : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

@[expose] def U4 : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def V4 : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![1, 0, 0, 1; 0, 1, 1, 1; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def A5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def B5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1]

@[expose] def U5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 1, 0, 0; 0, 1, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def V5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 1, 0; 0, 1, 1, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def sA4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨A4, det_eq_one_of_mul_eq_one_two A4 (A4 * A4) (by decide)⟩

@[expose] def sB4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨B4, det_eq_one_of_mul_eq_one_two B4 (B4 * B4) (by decide)⟩

@[expose] def sU4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨U4, det_eq_one_of_mul_eq_one_two U4 U4 (by decide)⟩

@[expose] def sV4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨V4, det_eq_one_of_mul_eq_one_two V4 V4 (by decide)⟩

@[expose] def sA5 : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨A5, det_eq_one_of_mul_eq_one_two A5 (A5 * A5) (by decide)⟩

@[expose] def sB5 : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨B5, det_eq_one_of_mul_eq_one_two B5 (B5 * B5) (by decide)⟩

@[expose] def sU5 : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨U5, det_eq_one_of_mul_eq_one_two U5 U5 (by decide)⟩

@[expose] def sV5 : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨V5, det_eq_one_of_mul_eq_one_two V5 V5 (by decide)⟩

variable {K : Type} [Field K] [Finite K]

theorem eInvFourFact_projectiveSL_four (hK : Nat.card K = 2) :
    EInvFourFact (projectiveSL 4 K) :=
  eInvFourFact_projectiveSL_two hK (n := 4) (by norm_num) (card_sylow_three_four hK)
    (a := sA4) (b := sB4) (u₁ := sU4) (u₂ := sV4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (va₁ := sV4) (va₂ := sU4 * sV4) (vb₁ := sU4 * sV4) (vb₂ := sU4)
    (Four4.right _ _) (Four4.mul _ _) (Four4.mul _ _) (Four4.left _ _)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem eInvFourFact_projectiveSL_five (hK : Nat.card K = 2) :
    EInvFourFact (projectiveSL 5 K) :=
  eInvFourFact_projectiveSL_two hK (n := 5) (by norm_num) (card_sylow_three_five hK)
    (a := sA5) (b := sB5) (u₁ := sU5) (u₂ := sV5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (va₁ := sV5) (va₂ := sU5 * sV5) (vb₁ := sU5 * sV5) (vb₂ := sU5)
    (Four4.right _ _) (Four4.mul _ _) (Four4.mul _ _) (Four4.left _ _)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Data

section Model

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem exists_mulEquiv_projectiveSL_of_psl_two_one {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSL n 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (X ≃* projectiveSL n K) := by
  obtain ⟨-, K, hF, hfin, hK, ⟨e⟩⟩ := h
  exact ⟨K, hF, hfin, by rw [hK, pow_one], ⟨e.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))⟩⟩

theorem eInvFourFact_of_psl_two_one {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 4 2 1 ∨ StatedClassicalModel X .PSL 5 2 1) :
    EInvFourFact X := by
  rcases h with h | h
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_psl_two_one h
    exact EInvFourFact.of_mulEquiv e (eInvFourFact_projectiveSL_four hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_psl_two_one h
    exact EInvFourFact.of_mulEquiv e (eInvFourFact_projectiveSL_five hK)

end Model

end CFSG.RankThree.PartTwo.Sec21.Hering214
