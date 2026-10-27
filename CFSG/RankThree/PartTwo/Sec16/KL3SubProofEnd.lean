module

public import CFSG.RankThree.PartTwo.Sec16.KL3SubProofUT
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.Milestones.LR_Brauer_Suzuki_central_involution

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace KL3SubProof

open Matrix

section Groups

variable {X : Type*} [Group X]

theorem mul_comm_of_forall_sq_eq_one (h : ∀ x : X, x ^ 2 = 1) (a b : X) : a * b = b * a := by
  have hinv : ∀ x : X, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (by rw [← pow_two, h])
  calc a * b = (a * b)⁻¹ := (hinv _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv, hinv]

theorem three_dvd_card_of_conj_orbit [Finite X] (S : Subgroup X) {t u v : X}
    (hS : ∀ s ∈ S, s * t * s⁻¹ = t ∨ s * t * s⁻¹ = u ∨ s * t * s⁻¹ = v)
    (hu : ∃ s ∈ S, s * t * s⁻¹ = u) (hv : ∃ s ∈ S, s * t * s⁻¹ = v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v) : 3 ∣ Nat.card S := by
  set G0 : Subgroup (ConjAct X) := S.map (ConjAct.toConjAct : X ≃* ConjAct X).toMonoidHom
    with hG0
  have hmem : ∀ y : X, y ∈ MulAction.orbit G0 t ↔ ∃ s ∈ S, s * t * s⁻¹ = y := by
    intro y
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hg
      exact ⟨s, hs, (ConjAct.toConjAct_smul s t).symm⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨ConjAct.toConjAct s, Subgroup.mem_map.mpr ⟨s, hs, rfl⟩⟩,
        ConjAct.toConjAct_smul s t⟩
  have horbit : MulAction.orbit G0 t = {t, u, v} := by
    ext y
    rw [hmem]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rcases hS s hs with h | h | h <;> rw [h] <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨1, S.one_mem, by group⟩
      · exact hu
      · exact hv
  have hcard : (MulAction.orbit G0 t).ncard = 3 := by
    rw [horbit, Set.ncard_eq_three]
    exact ⟨t, u, v, htu, htv, huv, rfl⟩
  have hidx := MulAction.index_stabilizer G0 t
  rw [hcard] at hidx
  have hdvd : 3 ∣ Nat.card G0 := hidx ▸ Subgroup.index_dvd_card _
  rwa [hG0, Subgroup.card_map_of_injective (ConjAct.toConjAct : X ≃* ConjAct X).injective]
    at hdvd

end Groups

variable {K : Type} [Field K]

theorem utm_eq_elat_col (α γ : K) :
    utm α 0 γ = 1 + vecMulVec (Pi.single 0 1) ![0, α, γ] := by
  ext i j
  rw [Matrix.add_apply, vecMulVec_apply]
  fin_cases i <;> fin_cases j <;> simp [utm]

theorem utm_eq_elat_row (β γ : K) :
    utm 0 β γ = 1 + vecMulVec ![γ, β, 0] (Pi.single 2 1) := by
  ext i j
  rw [Matrix.add_apply, vecMulVec_apply]
  fin_cases i <;> fin_cases j <;> simp [utm]

theorem conj_utm_col {g : GL (Fin 3) K} (hg : g ∈ colSub K) (α γ : K) :
    ∃ α' γ' : K, (g : Matrix (Fin 3) (Fin 3) K) * utm α 0 γ *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = utm α' 0 γ' := by
  have hgi : g⁻¹ ∈ colSub K := (colSub K).inv_mem hg
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hi1, hi2⟩ := hgi
  have hgg : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set w := (![0, α, γ] : Fin 3 → K) ᵥ* ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hw
  have hw0 : w 0 = 0 := by
    simp only [hw, vecMul, dotProduct, Fin.sum_univ_three, hi1, hi2, mul_zero, add_zero]
    simp
  have hge : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 =
      (g : Matrix (Fin 3) (Fin 3) K) 0 0 • Pi.single 0 1 := by
    rw [mulVec_single_one]
    ext i
    fin_cases i <;> simp [hg1, hg2]
  refine ⟨(g : Matrix (Fin 3) (Fin 3) K) 0 0 * w 1, (g : Matrix (Fin 3) (Fin 3) K) 0 0 * w 2, ?_⟩
  rw [utm_eq_elat_col, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgg, mul_vecMulVec,
    vecMulVec_mul, hge, ← hw, utm_eq_elat_col]
  congr 1
  ext i j
  fin_cases j <;> simp [vecMulVec_apply, hw0] <;> ring

theorem conj_utm_row {g : GL (Fin 3) K} (hg : g ∈ rowSub K) (β γ : K) :
    ∃ β' γ' : K, (g : Matrix (Fin 3) (Fin 3) K) * utm 0 β γ *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = utm 0 β' γ' := by
  have hgi : g⁻¹ ∈ rowSub K := (rowSub K).inv_mem hg
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hi1, hi2⟩ := hgi
  have hgg : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set w := (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (![γ, β, 0] : Fin 3 → K) with hw
  have hw2 : w 2 = 0 := by
    simp only [hw, mulVec, dotProduct, Fin.sum_univ_three, hg1, hg2, zero_mul, zero_add]
    simp
  have hge : (Pi.single 2 1 : Fin 3 → K) ᵥ* ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 • Pi.single 2 1 := by
    rw [single_one_vecMul]
    have hi1' := hi1
    have hi2' := hi2
    rw [Matrix.coe_units_inv] at hi1' hi2'
    ext i
    fin_cases i <;> simp [hi1', hi2']
  refine ⟨((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 * w 1,
    ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 * w 0, ?_⟩
  rw [utm_eq_elat_row, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgg, mul_vecMulVec,
    vecMulVec_mul, hge, ← hw, utm_eq_elat_row]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply, hw2] <;> ring

theorem mem_colSub_of_conj_eq {g t z : GL (Fin 3) K} {α γ c : K} (hα : α ≠ 0)
    (ht : (t : Matrix (Fin 3) (Fin 3) K) = utm α 0 γ) (hz : (z : Matrix (Fin 3) (Fin 3) K) =
      utm 0 0 c) (h : g⁻¹ * t * g = z) : g ∈ colSub K := by
  have htg : (t : Matrix (Fin 3) (Fin 3) K) * g = g * z := by
    rw [← h, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have hzc : (z : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec (Pi.single 0 1) ![0, 0, c] := by
    rw [hz, utm_eq_elat_col]
  rw [ht, utm_eq_elat_col, hzc, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    add_right_inj, vecMulVec_mul, mul_vecMulVec] at htg
  have hφ : (![0, α, γ] : Fin 3 → K) ᵥ* (g : Matrix (Fin 3) (Fin 3) K) ≠ 0 := by
    intro h0
    have := congrArg (fun v => v ᵥ* ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h0
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.vecMul_one, Matrix.zero_vecMul] at this
    have h1 := congrFun this 1
    simp at h1
    exact hα h1
  obtain ⟨d, hd⟩ := exists_eq_smul_of_vecMulVec_eq (Pi.single_ne_zero_iff.mpr one_ne_zero) hφ htg
  have h1 := congrFun hd 1
  have h2 := congrFun hd 2
  rw [mulVec_single_one] at h1 h2
  simp at h1 h2
  exact ⟨h1, h2⟩

theorem mem_rowSub_of_conj_eq {g t z : GL (Fin 3) K} {β γ c : K} (hβ : β ≠ 0)
    (ht : (t : Matrix (Fin 3) (Fin 3) K) = utm 0 β γ) (hz : (z : Matrix (Fin 3) (Fin 3) K) =
      utm 0 0 c) (h : g⁻¹ * t * g = z) : g ∈ rowSub K := by
  have htg : (t : Matrix (Fin 3) (Fin 3) K) * g = g * z := by
    rw [← h, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have hzc : (z : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec ![c, 0, 0] (Pi.single 2 1) := by
    rw [hz, utm_eq_elat_row]
  rw [ht, utm_eq_elat_row, hzc, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    add_right_inj, vecMulVec_mul, mul_vecMulVec] at htg
  have ha : (![0, β, γ] : Fin 3 → K) ≠ 0 := by
    intro h0
    have := congrFun h0 1
    simp at this
    exact hβ this
  have ha' : (![γ, β, 0] : Fin 3 → K) ≠ 0 := by
    intro h0
    have := congrFun h0 1
    simp at this
    exact hβ this
  have hφ : (Pi.single 2 1 : Fin 3 → K) ᵥ* (g : Matrix (Fin 3) (Fin 3) K) ≠ 0 := by
    intro h0
    have := congrArg (fun v => v ᵥ* ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h0
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.vecMul_one, Matrix.zero_vecMul] at this
    exact Pi.single_ne_zero_iff.mpr one_ne_zero this
  obtain ⟨d, hd⟩ := exists_eq_smul_of_vecMulVec_eq' ha' hφ htg
  have h0 := congrFun hd 0
  have h1 := congrFun hd 1
  have h2 := congrFun hd 2
  rw [single_one_vecMul] at h0 h1 h2
  simp at h0 h1 h2
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at h2
  exact ⟨h0.resolve_left hd0, h1.resolve_left hd0⟩

variable [CharP K 2]

theorem utm_conj (a b c α β γ : K) :
    utm a b c * utm α β γ * utm a b (c + a * b) = utm α β (γ + α * b + a * β) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [utm_mul, utm_mul]
  have e1 : a + α + a = α := by linear_combination a * h2
  have e2 : b + β + b = β := by linear_combination b * h2
  have e3 : c + a * β + γ + (a + α) * b + (c + a * b) = γ + α * b + a * β := by
    linear_combination (c + a * b) * h2
  rw [e1, e2, e3]

theorem utm_comm (a b c a' b' c' : K) :
    utm a' b' c' * utm a b c * utm a' b' (c' + a' * b') * utm a b (c + a * b) =
      utm 0 0 (a' * b + a * b') := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [utm_conj, utm_mul]
  have e1 : a + a = 0 := by linear_combination a * h2
  have e2 : b + b = 0 := by linear_combination b * h2
  have e3 : c + a * b' + a' * b + a * b + (c + a * b) = a' * b + a * b' := by
    linear_combination (c + a * b) * h2
  rw [e1, e2, e3]

@[expose] def IsZUT (M : Matrix (Fin 3) (Fin 3) K) : Prop := IsUT M ∧ M 0 1 = 0 ∧ M 1 2 = 0

omit [CharP K 2] in
theorem isZUT_utm (c : K) : IsZUT (utm 0 0 c) := ⟨isUT_utm 0 0 c, by simp, by simp⟩

theorem false_of_unitriangular {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (h3 : ¬ 3 ∣ Nat.card X) (ρ : X →* GL (Fin 3) K) (hρ : Function.Injective ρ)
    (P : Sylow 2 X) (hP : ¬ IsMulCommutative (P : Subgroup X))
    (hUT : ∀ p ∈ (P : Subgroup X), IsUT ((ρ p : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hZ : ∀ u v : X, IsZUT ((ρ u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →
      IsZUT ((ρ v : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → u ≠ 1 → v ≠ 1 → u = v) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  set m : X → Matrix (Fin 3) (Fin 3) K := fun x => ((ρ x : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) with hmdef
  have hm_mul : ∀ x y, m (x * y) = m x * m y := fun x y => by
    simp only [hmdef, map_mul, Units.val_mul]
  have hm_one : m 1 = 1 := by simp only [hmdef, map_one, Units.val_one]
  have hm_inj : ∀ x y, m x = m y → x = y := fun x y h => hρ (Units.ext h)
  have hm_eq_one : ∀ x, m x = 1 → x = 1 := fun x h => hm_inj x 1 (by rw [h, hm_one])
  have hm_inv : ∀ x, IsUT (m x) →
      m x⁻¹ = utm (m x 0 1) (m x 1 2) (m x 0 2 + m x 0 1 * m x 1 2) := by
    intro x hx
    simp only [hmdef, map_inv]
    exact IsUT.coe_inv hx
  have hQ2 : IsPGroup 2 ((utSub K).comap ρ) := by
    intro g
    refine ⟨2, Subtype.ext (hρ ?_)⟩
    have h4 := pow_four_eq_one_of_mem_utSub (K := K) g.2
    simpa [map_pow] using h4
  have hmemP : ∀ x, IsUT (m x) → x ∈ (P : Subgroup X) := by
    intro x hx
    have heq : (utSub K).comap ρ = (P : Subgroup X) := P.is_maximal' hQ2 (fun p hp => hUT p hp)
    rw [← heq]
    exact hx
  have hPUT : ∀ y ∈ (P : Subgroup X), IsUT (m y) := hUT
  obtain ⟨x0, hx0P, hx0sq⟩ : ∃ x ∈ (P : Subgroup X), x ^ 2 ≠ 1 := by
    by_contra h
    push Not at h
    apply hP
    have hsq : ∀ y : (P : Subgroup X), y ^ 2 = 1 := fun y =>
      Subtype.ext (by rw [Subgroup.coe_pow]; exact h y y.2)
    exact ⟨⟨mul_comm_of_forall_sq_eq_one hsq⟩⟩
  have hx0U := hPUT x0 hx0P
  set a := m x0 0 1 with ha
  set b := m x0 1 2 with hb
  set c := m x0 0 2 with hc
  have hmx0 : m x0 = utm a b c := hx0U.eq_utm
  have hmx0i : m x0⁻¹ = utm a b (c + a * b) := hm_inv x0 hx0U
  set z := x0 ^ 2 with hzdef
  have hzP : z ∈ (P : Subgroup X) := (P : Subgroup X).pow_mem hx0P 2
  have hmz : m z = utm 0 0 (a * b) := by rw [hzdef, pow_two, hm_mul, hmx0, utm_mul_self]
  have hab : a * b ≠ 0 := by
    intro h0
    apply hx0sq
    apply hm_eq_one
    rw [hmz, h0, utm_zero]
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
  have hz1 : z ≠ 1 := hx0sq
  have hzZ : IsZUT (m z) := hmz ▸ isZUT_utm _
  have hZz : ∀ y, IsZUT (m y) → y = 1 ∨ y = z := by
    intro y hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (hZ y z hy hzZ hy1 hz1)
  have hzz : z * z = 1 := by
    apply hm_eq_one
    rw [hm_mul, hmz, utm_zero_zero_mul_self]
  have hzcomm : ∀ y, IsUT (m y) → z * y = y * z := by
    intro y hy
    apply hm_inj
    rw [hm_mul, hm_mul, hmz, hy.eq_utm, utm_mul, utm_mul]
    congr 1 <;> ring
  set val : X → K := fun y => m y 0 1 * b + a * m y 1 2 with hval
  have hcomm_m : ∀ y, IsUT (m y) → m (y * x0 * y⁻¹ * x0⁻¹) = utm 0 0 (val y) := by
    intro y hy
    obtain ⟨a', b', c', hy'⟩ : ∃ a' b' c' : K, m y = utm a' b' c' := ⟨_, _, _, hy.eq_utm⟩
    have hyi : m y⁻¹ = utm a' b' (c' + a' * b') := by
      rw [hm_inv y hy, hy']
      simp
    rw [hm_mul, hm_mul, hm_mul, hy', hmx0, hyi, hmx0i, utm_comm, hval]
    simp [hy']
  have hval_cases : ∀ y, IsUT (m y) → val y = 0 ∨ val y = a * b := by
    intro y hy
    rcases hZz _ (hcomm_m y hy ▸ isZUT_utm _) with h | h
    · left
      have := congrArg m h
      rw [hcomm_m y hy, hm_one, utm_eq_one_iff] at this
      exact this.2.2
    · right
      have := congrArg m h
      rw [hcomm_m y hy, hmz] at this
      exact (utm_inj this).2.2
  have hcomm_iff : ∀ y, IsUT (m y) → (x0 * y = y * x0 ↔ val y = 0) := by
    intro y hy
    constructor
    · intro h
      have h1 : y * x0 * y⁻¹ * x0⁻¹ = 1 := by
        rw [← h]
        group
      have := congrArg m h1
      rw [hcomm_m y hy, hm_one, utm_eq_one_iff] at this
      exact this.2.2
    · intro h
      have h1 : m (y * x0 * y⁻¹ * x0⁻¹) = m 1 := by
        rw [hcomm_m y hy, h, utm_zero, hm_one]
      have h2 := hm_inj _ _ h1
      have h3 : y * x0 = x0 * y := by
        calc y * x0 = (y * x0 * y⁻¹ * x0⁻¹) * (x0 * y) := by group
          _ = x0 * y := by rw [h2, one_mul]
      exact h3.symm
  have hval_mul : ∀ y y', IsUT (m y) → IsUT (m y') → val (y * y') = val y + val y' := by
    intro y y' hy hy'
    simp only [hval, hm_mul]
    rw [hy.eq_utm, hy'.eq_utm, utm_mul]
    simp
    ring
  set Q : Subgroup X := Subgroup.centralizer ({x0} : Set X) ⊓ (P : Subgroup X) with hQdef
  have hmemQ : ∀ y, y ∈ Q ↔ y ∈ (P : Subgroup X) ∧ val y = 0 := by
    intro y
    rw [hQdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (hcomm_iff y (hPUT y h2)).mp (h1 x0 rfl)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1⟩
      rintro _ rfl
      exact (hcomm_iff y (hPUT y h1)).mpr h2
  have hQP : Q ≤ (P : Subgroup X) := inf_le_right
  have hQelts : ∀ y ∈ Q, y = 1 ∨ y = z ∨ y = x0 ∨ y = z * x0 := by
    intro y hyQ
    obtain ⟨hyP, hyv⟩ := (hmemQ y).mp hyQ
    have hy := hPUT y hyP
    obtain ⟨a', b', c', hy'⟩ : ∃ a' b' c' : K, m y = utm a' b' c' := ⟨_, _, _, hy.eq_utm⟩
    have hv : a' * b + a * b' = 0 := by
      have : val y = a' * b + a * b' := by simp [hval, hy']
      rw [← this, hyv]
    by_cases ha' : a' = 0
    · have hb' : b' = 0 := by
        subst ha'
        have : a * b' = 0 := by linear_combination hv
        exact (mul_eq_zero.mp this).resolve_left ha0
      rcases hZz y ⟨hy, by simp [hy', ha'], by simp [hy', hb']⟩ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    ·
      have hy2 : m (y * y) = utm 0 0 (a' * b') := by rw [hm_mul, hy', utm_mul_self]
      have hE1 : a' * b = a * b' := by linear_combination hv - a * b' * h2K
      rcases hZz (y * y) (hy2 ▸ isZUT_utm _) with h | h
      · exfalso
        have h0 : a' * b' = 0 := by
          have := congrArg m h
          rw [hy2, hm_one, utm_eq_one_iff] at this
          exact this.2.2
        have : a' * a' * b = 0 := by linear_combination a' * hE1 + a * h0
        rcases mul_eq_zero.mp this with h' | h'
        · exact ha' (mul_self_eq_zero.mp h')
        · exact hb0 h'
      · have h0 : a' * b' = a * b := by
          have := congrArg m h
          rw [hy2, hmz] at this
          exact (utm_inj this).2.2
        have hsq : (a' + a) * (a' + a) * b = 0 := by
          linear_combination a' * hE1 + a * h0 + (a * a' * b + a * a * b) * h2K
        have haa : a' + a = 0 := by
          rcases mul_eq_zero.mp hsq with h' | h'
          · exact mul_self_eq_zero.mp h'
          · exact absurd h' hb0
        have ha'a : a' = a := by linear_combination haa - a * h2K
        have hb'b : b' = b := by
          rw [ha'a] at hE1
          have : a * (b' - b) = 0 := by linear_combination -hE1
          exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha0)
        have hyx : IsZUT (m (y * x0⁻¹)) := by
          rw [hm_mul, hy', hmx0i, utm_mul, ha'a, hb'b]
          refine ⟨isUT_utm _ _ _, ?_, ?_⟩
          · simp only [utm_apply_zero_one]
            linear_combination a * h2K
          · simp only [utm_apply_one_two]
            linear_combination b * h2K
        rcases hZz (y * x0⁻¹) hyx with h' | h'
        · right; right; left
          calc y = y * x0⁻¹ * x0 := by group
            _ = x0 := by rw [h', one_mul]
        · right; right; right
          calc y = y * x0⁻¹ * x0 := by group
            _ = z * x0 := by rw [h']
  have hx0z : x0 * z = z * x0 := by
    rw [hzdef]
    exact (pow_mul_comm' x0 2).symm
  have hQinv : ∀ y ∈ Q, y ^ 2 = 1 → y ≠ 1 → y = z := by
    intro y hyQ hy2 hy1
    rcases hQelts y hyQ with h | h | h | h
    · exact absurd h hy1
    · exact h
    · rw [h] at hy2
      exact absurd hy2 hx0sq
    · exfalso
      apply hx0sq
      have e : (z * x0) ^ 2 = z := by
        rw [pow_two, mul_assoc, ← mul_assoc x0 z x0, hx0z, mul_assoc z x0 x0, ← mul_assoc z z,
          hzz, one_mul, hzdef, pow_two]
      rw [h] at hy2
      rw [← e, hy2]
  obtain ⟨y0, hy0P, hy0Q⟩ : ∃ y0 ∈ (P : Subgroup X), y0 ∉ Q := by
    by_contra h
    push Not at h
    apply hP
    have hpow : ∀ y : (P : Subgroup X), ∃ k : ℕ, (y : X) = x0 ^ k := by
      intro y
      rcases hQelts y (h y y.2) with h' | h' | h' | h'
      · exact ⟨0, by rw [h', pow_zero]⟩
      · exact ⟨2, by rw [h', hzdef]⟩
      · exact ⟨1, by rw [h', pow_one]⟩
      · exact ⟨3, by rw [h', hzdef, ← pow_succ]⟩
    refine ⟨⟨fun u v => ?_⟩⟩
    obtain ⟨k, hk⟩ := hpow u
    obtain ⟨l, hl⟩ := hpow v
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hk, hl, ← pow_add, ← pow_add, add_comm]
  have hvy0 : val y0 = a * b := by
    rcases hval_cases y0 (hPUT y0 hy0P) with h | h
    · exact absurd ((hmemQ y0).mpr ⟨hy0P, h⟩) hy0Q
    · exact h
  have hindex : Q.relIndex (P : Subgroup X) = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨y0, hy0P⟩, fun w => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    have hwU := hPUT w w.2
    have hwy : (w : X) * y0 ∈ (P : Subgroup X) := (P : Subgroup X).mul_mem w.2 hy0P
    rw [hmemQ, hmemQ, hval_mul _ _ hwU (hPUT y0 hy0P), hvy0]
    simp only [hwy, w.2, true_and]
    rcases hval_cases w hwU with h | h
    · rw [h, zero_add]
      exact Or.inr ⟨rfl, hab⟩
    · rw [h]
      exact Or.inl ⟨by linear_combination (a * b) * h2K, hab⟩
  by_cases hinv : ∃ t ∈ (P : Subgroup X), t ^ 2 = 1 ∧ t ≠ 1 ∧ t ∉ Q
  · obtain ⟨t, htP, ht2, ht1, htQ⟩ := hinv
    have htord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
    obtain ⟨g, hg⟩ : ∃ g : X, g⁻¹ * t * g ∈ Q := by
      by_contra hno
      push Not at hno
      obtain ⟨N, hN, hNsq, htN⟩ :=
        CFSG.Quasithin.thompson_transfer_exists_normal P hQP hindex htord hno
      have := hN
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
      · apply hx0sq
        have := hNsq x0
        rw [hb, Subgroup.mem_bot] at this
        exact this
      · exact htN (ht ▸ Subgroup.mem_top t)
    have hgz : g⁻¹ * t * g = z := by
      apply hQinv _ hg
      · have e : (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g := by
          rw [pow_two, pow_two]
          group
        rw [e, ht2]
        group
      · intro h
        apply ht1
        calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group
    have htU := hPUT t htP
    obtain ⟨α, β, γ, hmt⟩ : ∃ α β γ : K, m t = utm α β γ := ⟨_, _, _, htU.eq_utm⟩
    have hαβ : α * β = 0 := by
      have := congrArg m ht2
      rw [pow_two, hm_mul, hmt, utm_mul_self, hm_one, utm_eq_one_iff] at this
      exact this.2.2
    have hvt : α * b + a * β = a * b := by
      have hv : val t = α * b + a * β := by simp [hval, hmt]
      rcases hval_cases t htU with h | h
      · exact absurd ((hmemQ t).mpr ⟨htP, h⟩) htQ
      · rw [← hv, h]
    have hmti : m t⁻¹ = utm α β (γ + α * β) := by
      rw [hm_inv t htU, hmt]
      simp
    have htz : t ≠ t * z := fun h => hz1 (by
      calc z = t⁻¹ * (t * z) := by group
        _ = 1 := by rw [← h]; group)
    have htz' : t * z ≠ z := fun h => ht1 (by
      calc t = t * z * z⁻¹ := by group
        _ = 1 := by rw [h]; group)
    have hS3 : ∀ S : Subgroup X, 3 ∣ Nat.card S → False := fun S hS =>
      h3 (hS.trans (Subgroup.card_subgroup_dvd_card S))
    by_cases hβ : β = 0
    ·
      have hαa : α = a := by
        rw [hβ, mul_zero, add_zero] at hvt
        exact mul_right_cancel₀ hb0 hvt
      have hmt0 : m t = utm α 0 γ := by rw [hmt, hβ]
      set S0 := (colSub K).comap ρ with hS0
      have hgS0 : g ∈ S0 := by
        show ρ g ∈ colSub K
        refine mem_colSub_of_conj_eq (hαa ▸ ha0) hmt0 hmz ?_
        rw [← map_inv, ← map_mul, ← map_mul, hgz]
      have hx0S0 : x0 ∈ S0 := by
        show ρ x0 ∈ colSub K
        exact ⟨hx0U.2.2.2.1, hx0U.2.2.2.2.1⟩
      have htz0 : t ≠ z := by
        intro h
        have := congrFun (congrFun (congrArg m h) 0) 1
        rw [hmt0, hmz] at this
        simp only [utm_apply_zero_one] at this
        exact ha0 (hαa ▸ this)
      apply hS3 S0
      refine three_dvd_card_of_conj_orbit S0 (u := t * z) (v := z) ?_ ?_ ⟨g⁻¹, S0.inv_mem hgS0,
        by rw [inv_inv, hgz]⟩ htz htz0 htz'
      · intro s hs
        obtain ⟨α', γ', hconj⟩ := conj_utm_col (show ρ s ∈ colSub K from hs) α γ
        have hm' : m (s * t * s⁻¹) = utm α' 0 γ' := by
          rw [hm_mul, hm_mul, ← hconj, ← hmt0]
          simp only [hmdef, map_inv]
        have hy1 : s * t * s⁻¹ ≠ 1 := fun h => ht1 (by
          calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
            _ = 1 := by rw [h]; group)
        by_cases hα' : α' = 0
        · right; right
          rcases hZz _ (by rw [hm', hα']; exact isZUT_utm γ') with h | h
          · exact absurd h hy1
          · exact h
        · have hyU : IsUT (m (s * t * s⁻¹)) := hm' ▸ isUT_utm _ _ _
          have hvy : val (s * t * s⁻¹) = α' * b := by simp [hval, hm']
          have hα'a : α' = a := by
            rcases hval_cases _ hyU with h | h
            · rw [hvy] at h
              exact absurd ((mul_eq_zero.mp h).resolve_right hb0) hα'
            · rw [hvy] at h
              exact mul_right_cancel₀ hb0 h
          have hyt : IsZUT (m (s * t * s⁻¹ * t⁻¹)) := by
            rw [hm_mul, hm', hmti, hβ, utm_mul, hα'a, ← hαa]
            refine ⟨isUT_utm _ _ _, ?_, ?_⟩
            · simp only [utm_apply_zero_one]
              linear_combination α * h2K
            · simp
          rcases hZz _ hyt with h | h
          · left
            calc s * t * s⁻¹ = s * t * s⁻¹ * t⁻¹ * t := by group
              _ = t := by rw [h, one_mul]
          · right; left
            calc s * t * s⁻¹ = s * t * s⁻¹ * t⁻¹ * t := by group
              _ = z * t := by rw [h]
              _ = t * z := hzcomm t htU
      · refine ⟨x0, hx0S0, hm_inj _ _ ?_⟩
        rw [hm_mul, hm_mul, hmx0, hmt0, hmx0i, hm_mul, hmt0, hmz, utm_conj, utm_mul, hαa]
        congr 1 <;> ring
    ·
      have hα0 : α = 0 := (mul_eq_zero.mp hαβ).resolve_right hβ
      have hβb : β = b := by
        rw [hα0, zero_mul, zero_add] at hvt
        exact mul_left_cancel₀ ha0 hvt
      have hmt0 : m t = utm 0 β γ := by rw [hmt, hα0]
      set S1 := (rowSub K).comap ρ with hS1
      have hgS1 : g ∈ S1 := by
        show ρ g ∈ rowSub K
        refine mem_rowSub_of_conj_eq hβ hmt0 hmz ?_
        rw [← map_inv, ← map_mul, ← map_mul, hgz]
      have hx0S1 : x0 ∈ S1 := by
        show ρ x0 ∈ rowSub K
        exact ⟨hx0U.2.2.2.2.1, hx0U.2.2.2.2.2⟩
      have htz0 : t ≠ z := by
        intro h
        have := congrFun (congrFun (congrArg m h) 1) 2
        rw [hmt0, hmz] at this
        simp only [utm_apply_one_two] at this
        exact hβ this
      apply hS3 S1
      refine three_dvd_card_of_conj_orbit S1 (u := t * z) (v := z) ?_ ?_ ⟨g⁻¹, S1.inv_mem hgS1,
        by rw [inv_inv, hgz]⟩ htz htz0 htz'
      · intro s hs
        obtain ⟨β', γ', hconj⟩ := conj_utm_row (show ρ s ∈ rowSub K from hs) β γ
        have hm' : m (s * t * s⁻¹) = utm 0 β' γ' := by
          rw [hm_mul, hm_mul, ← hconj, ← hmt0]
          simp only [hmdef, map_inv]
        have hy1 : s * t * s⁻¹ ≠ 1 := fun h => ht1 (by
          calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
            _ = 1 := by rw [h]; group)
        by_cases hβ' : β' = 0
        · right; right
          rcases hZz _ (by rw [hm', hβ']; exact isZUT_utm γ') with h | h
          · exact absurd h hy1
          · exact h
        · have hyU : IsUT (m (s * t * s⁻¹)) := hm' ▸ isUT_utm _ _ _
          have hvy : val (s * t * s⁻¹) = a * β' := by simp [hval, hm']
          have hβ'b : β' = b := by
            rcases hval_cases _ hyU with h | h
            · rw [hvy] at h
              exact absurd ((mul_eq_zero.mp h).resolve_left ha0) hβ'
            · rw [hvy] at h
              exact mul_left_cancel₀ ha0 h
          have hyt : IsZUT (m (s * t * s⁻¹ * t⁻¹)) := by
            rw [hm_mul, hm', hmti, hα0, utm_mul, hβ'b, ← hβb]
            refine ⟨isUT_utm _ _ _, ?_, ?_⟩
            · simp
            · simp only [utm_apply_one_two]
              linear_combination β * h2K
          rcases hZz _ hyt with h | h
          · left
            calc s * t * s⁻¹ = s * t * s⁻¹ * t⁻¹ * t := by group
              _ = t := by rw [h, one_mul]
          · right; left
            calc s * t * s⁻¹ = s * t * s⁻¹ * t⁻¹ * t := by group
              _ = z * t := by rw [h]
              _ = t * z := hzcomm t htU
      · refine ⟨x0, hx0S1, hm_inj _ _ ?_⟩
        rw [hm_mul, hm_mul, hmx0, hmt0, hmx0i, hm_mul, hmt0, hmz, utm_conj, utm_mul, hβb]
        congr 1 <;> ring
  ·
    push Not at hinv
    have hunique : ∀ u ∈ (P : Subgroup X), u ^ 2 = 1 → u ≠ 1 → u = z := fun u hu hu2 hu1 =>
      hQinv u (hinv u hu hu2 hu1) hu2 hu1
    have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions
        (P : Subgroup X) := by
      intro u v _
      have key : ∀ w : CFSG.DisconnectedInvolutionGraph.Helpers.Involution (P : Subgroup X),
          ((w : (P : Subgroup X)) : X) = z := by
        intro w
        have hw2 : ((w : (P : Subgroup X)) : X) ^ 2 = 1 := by
          have := pow_orderOf_eq_one (w : (P : Subgroup X))
          rw [w.2] at this
          exact congrArg Subtype.val this
        have hw1 : ((w : (P : Subgroup X)) : X) ≠ 1 := by
          intro h
          have h1 : (w : (P : Subgroup X)) = 1 := Subtype.ext h
          have := w.2
          rw [h1, orderOf_one] at this
          exact absurd this (by norm_num)
        exact hunique _ (w : (P : Subgroup X)).2 hw2 hw1
      exact Subtype.ext (Subtype.ext ((key u).trans (key v).symm))
    have hnonab : ∃ u v : (P : Subgroup X), u * v ≠ v * u := by
      by_contra h
      push Not at h
      exact hP ⟨⟨h⟩⟩
    obtain ⟨e, he1, ⟨φ⟩⟩ :=
      CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_nonabelian_quaternion
        (G := (P : Subgroup X)) P.isPGroup' hrank hnonab
    have hq : Nonempty ((P : Subgroup X) ≃* QuaternionGroup (2 ^ (e + 2 - 2))) := by
      rw [Nat.add_sub_cancel]
      exact ⟨φ.symm⟩
    have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
    obtain ⟨hne, hcen⟩ :=
      CFSG.Milestones.brauer_suzuki_central_involution (e + 2) (by omega) P hq z hzP hzord
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore X) with hb | ht
    · apply hP
      have hzc : z ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro w
        have := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk w)
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hb,
          Subgroup.mem_bot] at this
        calc w * z = w * z * ((w * z)⁻¹ * (z * w)) := by rw [this, mul_one]
          _ = z * w := by group
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hcb | hct
      · rw [hcb, Subgroup.mem_bot] at hzc
        exact absurd hzc hz1
      · refine ⟨⟨fun u v => Subtype.ext ?_⟩⟩
        have hu : (u : X) ∈ Subgroup.center X := hct ▸ Subgroup.mem_top _
        exact (Subgroup.mem_center_iff.mp hu (v : X)).symm
    · apply hne
      rw [QuotientGroup.eq_one_iff, ht]
      exact Subgroup.mem_top z

end KL3SubProof

end CFSG.RankThree.PartTwo.Sec16
