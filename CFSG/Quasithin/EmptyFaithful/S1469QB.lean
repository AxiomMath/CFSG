module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 CFSG.LieType.BorelTits
open Matrix MatrixGroups Matrix.SpecialLinearGroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private def lin2Twist (c x : G) : G := c * x * c⁻¹ * x⁻¹

omit [Finite G] in
private theorem lin2Twist_mul (c x y : G) : lin2Twist c (x * y) = lin2Twist c x * (x * lin2Twist c y * x⁻¹) := by
  unfold lin2Twist; group

omit [Finite G] in
private theorem lin2Twist_one (c : G) : lin2Twist c 1 = 1 := by simp [lin2Twist]

omit [Finite G] in
private theorem lin2Twist_eq_one_iff {c x : G} : lin2Twist c x = 1 ↔ c * x = x * c := by
  unfold lin2Twist
  constructor
  · intro h
    calc c * x = (c * x * c⁻¹ * x⁻¹) * (x * c) := by group
      _ = x * c := by rw [h, one_mul]
  · intro h
    rw [h]; group

omit [Finite G] in
private theorem lin2Twist_three (c y : G) :
    lin2Twist c (y * y * y) =
      lin2Twist c y * (y * lin2Twist c y * y⁻¹) * ((y * y) * lin2Twist c y * (y * y)⁻¹) := by
  unfold lin2Twist; group

private def lin2SlDiag {F : Type} [Field F] (a : F) (ha : a ≠ 0) : SL(2, F) :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha]⟩

private theorem lin2SlDiag_val {F : Type} [Field F] (a : F) (ha : a ≠ 0) :
    (lin2SlDiag a ha : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, a⁻¹] := rfl

private theorem lin2SlWeyl_conj_slDiag {F : Type} [Field F] (a : F) (ha : a ≠ 0) :
    ((slWeyl (1 : F) one_ne_zero * lin2SlDiag a ha * (slWeyl (1 : F) one_ne_zero)⁻¹ : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F) = !![a⁻¹, 0; 0, a] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, slWeyl_val, lin2SlDiag_val, Matrix.adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [Finite G] in
private theorem le_of_mem_not_normalizer {L P X : Subgroup G} {n : ℕ} (hn : 0 < n)
    (hlin : IsLin2Type L n) (hP : IsSylowTwoOf P L) (hPX : P ≤ X) {w : G} (hwL : w ∈ L)
    (hwX : w ∈ X) (hwN : w ∉ Subgroup.normalizer (P : Set G)) : L ≤ X := by
  by_contra hLX
  exact hwN (inf_le_normalizer_of_isLin2Type hn hlin hP hPX hLX ⟨hwL, hwX⟩)

omit [Finite G] in
private theorem mem_blockZ_of_comm_of_upper {L P : Subgroup G} {n : ℕ} {F : Type} [Field F]
    [Fintype F] (A : Adapted L P n F) {d u : G} (hdL : d ∈ L)
    (hup : (A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (ha1 : (A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 1) (hu : u ∈ blockU L)
    (hc : d * u * d⁻¹ * u⁻¹ ∈ blockZ L) : u ∈ blockZ L := by
  have hcU : d * u * d⁻¹ * u⁻¹ ∈ blockU L :=
    Subgroup.mul_mem _ (mem_blockU_conj hdL hu) (Subgroup.inv_mem _ hu)
  have h1 := (A.mem_blockZ_iff hcU).1 hc
  have e : (⟨d * u * d⁻¹ * u⁻¹, hcU⟩ : blockU L) =
      ⟨d * u * d⁻¹, mem_blockU_conj hdL hu⟩ * ⟨u, hu⟩⁻¹ := rfl
  rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, A.toAdd_beta_conj ⟨d, hdL⟩ hu] at h1
  set v : Fin 2 → F := Multiplicative.toAdd (A.β ⟨u, hu⟩) with hv
  have hdet := apply_zero_zero_mul_apply_one_one hup
  have ha' : (A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 1 := by
    intro h5
    rw [h5, mul_one] at hdet
    exact ha1 hdet
  have h1_1 := congrFun h1 1
  have h1_0 := congrFun h1 0
  obtain ⟨hm0, hm1⟩ := mulVec_of_apply_one_zero hup v
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, hm1] at h1_1
  have hv1 : v 1 = 0 := by
    have : ((A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) * v 1 = 0 := by
      linear_combination h1_1
    rcases mul_eq_zero.1 this with h6 | h6
    · exact absurd (sub_eq_zero.1 h6) ha'
    · exact h6
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, hm0, hv1, mul_zero, add_zero] at h1_0
  have hv0 : v 0 = 0 := by
    have : ((A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) * v 0 = 0 := by
      linear_combination h1_0
    rcases mul_eq_zero.1 this with h6 | h6
    · exact absurd (sub_eq_zero.1 h6) ha1
    · exact h6
  refine (A.mem_blockZ_iff hu).2 ?_
  funext i
  fin_cases i
  · exact hv0
  · exact hv1

omit [Finite G] in
private theorem mem_of_two_pow_of_pow_three_mem {U : Subgroup G} {d : G} {a : ℕ} (hd : d ^ 2 ^ a = 1)
    (h3 : d * d * d ∈ U) : d ∈ U := by
  have hne : 2 ^ a % 3 ≠ 0 := by
    intro h
    have h' : 3 ∣ 2 ^ a := Nat.dvd_of_mod_eq_zero h
    have := Nat.prime_three.dvd_of_dvd_pow h'
    omega
  have hq := Nat.div_add_mod (2 ^ a) 3
  have hpow : ∀ k : ℕ, (d * d * d) ^ k = d ^ (3 * k) := fun k => by
    rw [pow_mul, show d ^ 3 = d * d * d by simp [pow_succ]]
  have h3q : d ^ (3 * (2 ^ a / 3)) ∈ U := by
    rw [← hpow]; exact Subgroup.pow_mem _ h3 _
  have hmod : 2 ^ a % 3 = 1 ∨ 2 ^ a % 3 = 2 := by omega
  rcases hmod with h1 | h2
  · have e : d ^ (3 * (2 ^ a / 3)) * d = 1 := by
      rw [← pow_succ, ← hd]; congr 1; omega
    have : d = (d ^ (3 * (2 ^ a / 3)))⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [this]; exact Subgroup.inv_mem _ h3q
  · have e : d ^ (3 * (2 ^ a / 3)) * (d * d) = 1 := by
      rw [← pow_two, ← pow_add, ← hd]; congr 1; omega
    have hd2 : d * d = (d ^ (3 * (2 ^ a / 3)))⁻¹ := eq_inv_of_mul_eq_one_right e
    have hd2U : d * d ∈ U := by rw [hd2]; exact Subgroup.inv_mem _ h3q
    have : d = (d * d * d) * (d * d)⁻¹ := by group
    rw [this]; exact Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ hd2U)

theorem lin2_commute_of_borel {L P : Subgroup G} {n : ℕ} {c : G} (hn : 1 < n) (hsh : IsShort2 L)
    (hlin : IsLin2Type L n) (hP : IsSylowTwoOf P L)
    (hcQ : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L)
    (hcB : ∀ b ∈ L, b ∈ Subgroup.normalizer (P : Set G) → c * b = b * c) :
    ∀ x ∈ L, c * x = x * c := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, ⟨A⟩⟩ := exists_adapted (by omega : 0 < n) hlin hP
  have h2 : (2 : F) = 0 := two_eq_zero_of_card (by omega) A.card_eq
  have hneg : (-1 : F) = 1 := neg_eq_self_of_two_eq_zero h2 1
  have hQP : pCoreOf 2 L ≤ P := hP.pCoreOf_le
  have hPL : P ≤ L := hP.le
  have hQL : pCoreOf 2 L ≤ L := pCoreOf_le 2 L
  have hT0 : ∀ b ∈ L, b ∈ Subgroup.normalizer (P : Set G) → lin2Twist c b = 1 :=
    fun b hb hbN => lin2Twist_eq_one_iff.2 (hcB b hb hbN)
  have hTP : ∀ p ∈ P, lin2Twist c p = 1 := fun p hp => hT0 p (hPL hp) (Subgroup.le_normalizer hp)
  have hTQ : ∀ q ∈ pCoreOf 2 L, lin2Twist c q = 1 := fun q hq => hTP q (hQP hq)
  have hTL : ∀ x ∈ L, lin2Twist c x ∈ pCoreOf 2 L := hcQ
  have hUQ : blockU L ≤ pCoreOf 2 L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) := hsh.2.2.1.1
  have hUcomm : ∀ e ∈ blockU L, ∀ d ∈ pCoreOf 2 L, d * e = e * d := fun e he d hd =>
    Subgroup.mem_centralizer_iff.mp (hUQ he).2 d hd
  have hQU : ∀ d ∈ pCoreOf 2 L, ∀ l ∈ L, l * d * l⁻¹ * d⁻¹ ∈ blockU L := by
    intro d hd l hl
    have h : ⁅d, l⁆ ∈ blockU L := Subgroup.commutator_mem_commutator hd hl
    have h' : (⁅d, l⁆)⁻¹ ∈ blockU L := Subgroup.inv_mem _ h
    have e : (⁅d, l⁆)⁻¹ = l * d * l⁻¹ * d⁻¹ := by rw [commutatorElement_def]; group
    rwa [e] at h'
  obtain ⟨a, ha0, ha1⟩ : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, A.card_eq] at h1
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h5 := Finset.card_le_two (a := (0 : F)) (b := 1)
    omega
  obtain ⟨u0, hu0⟩ := A.α_surj (slUpper (1 : F))
  obtain ⟨w0, hw0⟩ := A.α_surj (slWeyl (1 : F) one_ne_zero)
  obtain ⟨t0, ht0⟩ := A.α_surj (lin2SlDiag a ha0)
  have hu0P : (u0 : G) ∈ P := (A.mem_P u0).2 (by rw [hu0]; exact slUpper_mem_slUni 1)
  have hwN : (w0 : G) ∉ Subgroup.normalizer (P : Set G) := by
    intro h
    have := (A.normalizer_iff w0).1 h
    rw [hw0, slWeyl_val] at this
    simp at this
  have htN : (t0 : G) ∈ Subgroup.normalizer (P : Set G) := by
    refine (A.normalizer_iff t0).2 ?_
    rw [ht0, lin2SlDiag_val]
    simp
  have hwL : (w0 : G) ∈ L := w0.2
  have huL : (u0 : G) ∈ L := u0.2
  have htL : (t0 : G) ∈ L := t0.2
  set y : G := (w0 : G) * (u0 : G) with hy
  have hyL : y ∈ L := L.mul_mem hwL huL
  have hy3 : y * y * y ∈ pCoreOf 2 L := by
    have h3 : A.α (w0 * u0 * (w0 * u0) * (w0 * u0)) = 1 := by
      simp only [map_mul, hw0, hu0]
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [slWeyl_val, slUpper_val, Matrix.mul_apply, Fin.sum_univ_two, hneg] <;>
        linear_combination h2
    exact (A.mem_pCoreOf_iff (w0 * u0 * (w0 * u0) * (w0 * u0))).2 h3
  have hTy3 : lin2Twist c (y * y * y) = 1 := hTQ _ hy3
  set m : G := lin2Twist c (w0 : G) with hm
  have hTy : lin2Twist c y = m := by
    rw [hy, lin2Twist_mul, hTP _ hu0P]
    simp [hm]
  have hmQ : m ∈ pCoreOf 2 L := hTL _ hwL
  have hrel : (y * m * y⁻¹ * m⁻¹) * ((y * y) * m * (y * y)⁻¹ * m⁻¹) * (m * m * m) = 1 := by
    have h := lin2Twist_three c y
    rw [hTy3, hTy] at h
    set e₁ := y * m * y⁻¹ * m⁻¹ with he₁
    set e₂ := (y * y) * m * (y * y)⁻¹ * m⁻¹ with he₂
    have he₁U : e₁ ∈ blockU L := hQU m hmQ y hyL
    have he₂U : e₂ ∈ blockU L := hQU m hmQ (y * y) (L.mul_mem hyL hyL)
    have hd1 : m * e₁ = e₁ * m := hUcomm e₁ he₁U m hmQ
    have hd2 : m * e₂ = e₂ * m := hUcomm e₂ he₂U m hmQ
    have h1 : y * m * y⁻¹ = e₁ * m := by rw [he₁]; group
    have h2' : (y * y) * m * (y * y)⁻¹ = e₂ * m := by rw [he₂]; group
    rw [h1, h2'] at h
    have key : m * (e₁ * m) * (e₂ * m) = e₁ * e₂ * (m * m * m) := by
      calc m * (e₁ * m) * (e₂ * m) = (m * e₁) * (m * e₂) * m := by group
        _ = (e₁ * m) * (e₂ * m) * m := by rw [hd1, hd2]
        _ = e₁ * (m * e₂) * m * m := by group
        _ = e₁ * (e₂ * m) * m * m := by rw [hd2]
        _ = e₁ * e₂ * (m * m * m) := by group
    rw [← key]
    exact h.symm
  have hmU : m ∈ blockU L := by
    have h3 : m * m * m ∈ blockU L := by
      have he₁U : y * m * y⁻¹ * m⁻¹ ∈ blockU L := hQU m hmQ y hyL
      have he₂U : (y * y) * m * (y * y)⁻¹ * m⁻¹ ∈ blockU L := hQU m hmQ (y * y) (L.mul_mem hyL hyL)
      have : m * m * m = ((y * m * y⁻¹ * m⁻¹) * ((y * y) * m * (y * y)⁻¹ * m⁻¹))⁻¹ :=
        eq_inv_of_mul_eq_one_right hrel
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ he₁U he₂U)
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨m, hmQ⟩
    have hk' : m ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact mem_of_two_pow_of_pow_three_mem hk' h3
  obtain ⟨s0, hs0⟩ : ∃ s0 : L, s0 = w0 * t0 * w0⁻¹ := ⟨_, rfl⟩
  have hscoe : (s0 : G) = (w0 : G) * (t0 : G) * (w0 : G)⁻¹ := by rw [hs0]; rfl
  have hsL : (s0 : G) ∈ L := s0.2
  have hαs : (A.α s0 : Matrix (Fin 2) (Fin 2) F) = !![a⁻¹, 0; 0, a] := by
    rw [hs0, map_mul, map_mul, map_inv, hw0, ht0]
    exact lin2SlWeyl_conj_slDiag a ha0
  have hsN : (s0 : G) ∈ Subgroup.normalizer (P : Set G) := by
    refine (A.normalizer_iff s0).2 ?_
    rw [hαs]
    simp
  have hcs : c * (s0 : G) = (s0 : G) * c := hcB _ hsL hsN
  have hct : c * (t0 : G) = (t0 : G) * c := hcB _ htL htN
  have hms : m * (s0 : G) * m⁻¹ = (s0 : G) := by
    have e1 : m * (w0 : G) = c * (w0 : G) * c⁻¹ := by rw [hm]; unfold lin2Twist; group
    have e2 : c * (t0 : G) * c⁻¹ = (t0 : G) := by rw [hct]; group
    have e3 : c * (s0 : G) * c⁻¹ = (s0 : G) := by rw [hcs]; group
    calc m * (s0 : G) * m⁻¹ = (m * (w0 : G)) * (t0 : G) * (m * (w0 : G))⁻¹ := by
          rw [hscoe]; group
      _ = (c * (w0 : G) * c⁻¹) * (c * (t0 : G) * c⁻¹) * (c * (w0 : G) * c⁻¹)⁻¹ := by
          rw [e1, e2]
      _ = c * (s0 : G) * c⁻¹ := by rw [hscoe]; group
      _ = (s0 : G) := e3
  have hcomm_s : (s0 : G) * m * (s0 : G)⁻¹ * m⁻¹ = 1 := by
    have h1 : m * (s0 : G) = (s0 : G) * m := by
      calc m * (s0 : G) = m * (s0 : G) * m⁻¹ * m := by group
        _ = (s0 : G) * m := by rw [hms]
    calc (s0 : G) * m * (s0 : G)⁻¹ * m⁻¹ = (m * (s0 : G)) * (s0 : G)⁻¹ * m⁻¹ := by rw [h1]
      _ = 1 := by group
  have hmZ : m ∈ blockZ L := by
    refine mem_blockZ_of_comm_of_upper A (d := (s0 : G)) (u := m) hsL ?_ ?_ hmU ?_
    · rw [show (⟨(s0 : G), hsL⟩ : L) = s0 from rfl, hαs]; simp
    · rw [show (⟨(s0 : G), hsL⟩ : L) = s0 from rfl, hαs]
      simpa using ha1
    · rw [hcomm_s]; exact (blockZ L).one_mem
  have hZcent : ∀ l ∈ L, ∀ z ∈ blockZ L, l * z * l⁻¹ = z := fun l hl z hz => by
    have hzc : z ∈ Subgroup.centralizer (L : Set G) := (show z ∈ blockU L ⊓
      Subgroup.centralizer (L : Set G) from hz).2
    have h := Subgroup.mem_centralizer_iff.mp hzc l hl
    rw [h]; group
  have hm1 : m = 1 := by
    have e1 : y * m * y⁻¹ = m := hZcent y hyL m hmZ
    have e2 : (y * y) * m * (y * y)⁻¹ = m := hZcent (y * y) (L.mul_mem hyL hyL) m hmZ
    rw [e1, e2] at hrel
    simp at hrel
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨m, hmQ⟩
    have hk' : m ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have := mem_of_two_pow_of_pow_three_mem (U := (⊥ : Subgroup G)) hk' (by rw [hrel]; exact Subgroup.one_mem _)
    simpa using this
  let X₄ : Subgroup G :=
    { carrier := {x | x ∈ L ∧ lin2Twist c x = 1}
      mul_mem' := fun {x y} hx hy => ⟨L.mul_mem hx.1 hy.1, by
        rw [lin2Twist_mul, hx.2, hy.2]; simp⟩
      one_mem' := ⟨L.one_mem, lin2Twist_one c⟩
      inv_mem' := fun {x} hx => ⟨L.inv_mem hx.1, by
        have h := lin2Twist_mul c x x⁻¹
        rw [mul_inv_cancel, lin2Twist_one, hx.2, one_mul] at h
        have h' : x * lin2Twist c x⁻¹ * x⁻¹ = 1 := h.symm
        calc lin2Twist c x⁻¹ = x⁻¹ * (x * lin2Twist c x⁻¹ * x⁻¹) * x := by group
          _ = 1 := by rw [h']; group⟩ }
  have hPX : P ≤ X₄ := fun p hp => ⟨hPL hp, hTP p hp⟩
  have hLX : L ≤ X₄ :=
    le_of_mem_not_normalizer (by omega) hlin hP hPX hwL ⟨hwL, hm1⟩ hwN
  intro x hx
  exact lin2Twist_eq_one_iff.1 (hLX hx).2

end CFSG.Quasithin
