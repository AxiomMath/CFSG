module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zzG

public section

namespace CFSG.Quasithin.H13.S127.Mod

theorem cpat_bits : ∀ c₁ c₂ c₃ : Bool,
    ((if c₁ then 1 else 0) + (if c₂ then 2 else 0) + (if c₃ then 4 else 0) : ℕ).testBit 0 = c₁ ∧
    ((if c₁ then 1 else 0) + (if c₂ then 2 else 0) + (if c₃ then 4 else 0) : ℕ).testBit 1 = c₂ ∧
    ((if c₁ then 1 else 0) + (if c₂ then 2 else 0) + (if c₃ then 4 else 0) : ℕ).testBit 2 = c₃ ∧
    ((if c₁ then 1 else 0) + (if c₂ then 2 else 0) + (if c₃ then 4 else 0) : ℕ) < 8 ∧
    (((if c₁ then 1 else 0) + (if c₂ then 2 else 0) + (if c₃ then 4 else 0) : ℕ) = 7 →
      c₁ = true ∧ c₂ = true ∧ c₃ = true) := by decide

end CFSG.Quasithin.H13.S127.Mod

namespace CFSG.Quasithin.H13.S127

variable {G : Type} [Group G]

@[expose] def Comm (A B : Subgroup G) : Prop := ∀ x ∈ A, ∀ y ∈ B, x * y = y * x

theorem comm_conj_iff (a x y : G) :
    a * x * a⁻¹ * (a * y * a⁻¹) = a * y * a⁻¹ * (a * x * a⁻¹) ↔ x * y = y * x := by
  rw [show a * x * a⁻¹ * (a * y * a⁻¹) = a * (x * y) * a⁻¹ by group,
    show a * y * a⁻¹ * (a * x * a⁻¹) = a * (y * x) * a⁻¹ by group]
  constructor
  · intro e
    exact mul_left_cancel (mul_right_cancel e)
  · intro e
    rw [e]

theorem comm_central {p q x y : G} (hqx : q * x = x * q) (hpy : p * y = y * p)
    (hpq : p * q = q * p) : p * x * (q * y) = q * y * (p * x) ↔ x * y = y * x := by
  rw [show p * x * (q * y) = p * q * (x * y) by
      rw [mul_assoc p x, ← mul_assoc x q, ← hqx]; group,
    show q * y * (p * x) = p * q * (y * x) by
      rw [mul_assoc q y, ← mul_assoc y p, ← hpy, hpq]; group]
  constructor
  · intro e
    exact mul_left_cancel e
  · intro e
    rw [e]

theorem comm_closure {S S' : Set G} (h : ∀ x ∈ S, ∀ y ∈ S', x * y = y * x) :
    Comm (Subgroup.closure S) (Subgroup.closure S') := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S' := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => (h x hx y hy).symm
  rw [← Subgroup.centralizer_closure] at h1
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (h1 hx) y hy).symm

section Seven

variable {x : G} (hx : x ^ 7 = 1) (v : G)
include hx

omit hx in
@[expose] def vk (x v : G) (k : Fin 7) : G := x ^ (k : ℕ) * v * (x ^ (k : ℕ))⁻¹

theorem pow_mod_seven (n : ℕ) : x ^ n = x ^ (n % 7) := by
  conv_lhs => rw [← Nat.div_add_mod n 7, pow_add, pow_mul, hx, one_pow, one_mul]

theorem pow_add_fin (i d : Fin 7) : x ^ ((i + d : Fin 7) : ℕ) = x ^ (i : ℕ) * x ^ (d : ℕ) := by
  rw [Fin.val_add, ← pow_mod_seven hx, pow_add]

theorem vk_add (i d : Fin 7) : vk x v (i + d) = x ^ (i : ℕ) * vk x v d * (x ^ (i : ℕ))⁻¹ := by
  simp only [vk, pow_add_fin hx]
  group

omit hx in
theorem vk_zero : vk x v 0 = v := by simp [vk]

theorem commute_vk (i j : Fin 7) :
    vk x v i * vk x v j = vk x v j * vk x v i ↔
      v * vk x v (j - i) = vk x v (j - i) * v := by
  have hi : vk x v i = x ^ (i : ℕ) * v * (x ^ (i : ℕ))⁻¹ := rfl
  have hj : vk x v j = x ^ (i : ℕ) * vk x v (j - i) * (x ^ (i : ℕ))⁻¹ := by
    rw [← vk_add hx, add_sub_cancel]
  rw [hi, hj]
  constructor
  · intro e
    have e2 : (x ^ (i : ℕ))⁻¹ * (x ^ (i : ℕ) * v * (x ^ (i : ℕ))⁻¹ *
        (x ^ (i : ℕ) * vk x v (j - i) * (x ^ (i : ℕ))⁻¹)) * x ^ (i : ℕ) =
        (x ^ (i : ℕ))⁻¹ * (x ^ (i : ℕ) * vk x v (j - i) * (x ^ (i : ℕ))⁻¹ *
        (x ^ (i : ℕ) * v * (x ^ (i : ℕ))⁻¹)) * x ^ (i : ℕ) := by rw [e]
    have l : ∀ a b : G, (x ^ (i : ℕ))⁻¹ * (x ^ (i : ℕ) * a * (x ^ (i : ℕ))⁻¹ *
        (x ^ (i : ℕ) * b * (x ^ (i : ℕ))⁻¹)) * x ^ (i : ℕ) = a * b := fun a b => by group
    rw [l, l] at e2
    exact e2
  · intro e
    calc x ^ (i : ℕ) * v * (x ^ (i : ℕ))⁻¹ * (x ^ (i : ℕ) * vk x v (j - i) * (x ^ (i : ℕ))⁻¹)
        = x ^ (i : ℕ) * (v * vk x v (j - i)) * (x ^ (i : ℕ))⁻¹ := by group
      _ = x ^ (i : ℕ) * (vk x v (j - i) * v) * (x ^ (i : ℕ))⁻¹ := by rw [e]
      _ = _ := by group

theorem commute_vk_neg (d : Fin 7) :
    v * vk x v (-d) = vk x v (-d) * v ↔ v * vk x v d = vk x v d * v := by
  have h1 := commute_vk hx v d 0
  have h2 := commute_vk hx v 0 d
  rw [zero_sub, vk_zero] at h1
  rw [sub_zero, vk_zero] at h2
  rw [← h1, ← h2]
  exact ⟨fun e => e.symm, fun e => e.symm⟩

end Seven

end CFSG.Quasithin.H13.S127

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S127 S127.Mod
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

omit [Finite G] s in
theorem comm_conj {x a : G} (hVc : ∀ p ∈ V, ∀ q ∈ V, p * q = q * p) (haV : a ∈ V)
    (ha2 : a * a = 1) (hxN : x ∈ Subgroup.normalizer (V : Set G)) (hx2 : x * x ∈ V) :
    x * (a * x * a⁻¹) = a * x * a⁻¹ * x := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hp : x * a * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxN a).mp haV
  have hq : x⁻¹ * a * x ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) a).mp haV
    simpa using this
  have hxa : x * x * a = a * (x * x) := hVc _ hx2 _ haV
  have hpq : x * a * x⁻¹ = x⁻¹ * a * x := by
    calc x * a * x⁻¹ = x⁻¹ * (x * x * a) * x⁻¹ := by group
      _ = x⁻¹ * (a * (x * x)) * x⁻¹ := by rw [hxa]
      _ = x⁻¹ * a * x := by group
  have hpV : (x * a * x⁻¹)⁻¹ ∈ V := V.inv_mem hp
  have he : x * (x⁻¹ * a * x * a⁻¹) * x⁻¹ = x⁻¹ * a * x * a⁻¹ := by
    calc x * (x⁻¹ * a * x * a⁻¹) * x⁻¹ = a * (x * a * x⁻¹)⁻¹ := by group
      _ = (x * a * x⁻¹)⁻¹ * a := hVc _ haV _ hpV
      _ = (x⁻¹ * a * x)⁻¹ * a := by rw [hpq]
      _ = x⁻¹ * a⁻¹ * x * a := by group
      _ = x⁻¹ * a * x * a⁻¹ := by rw [hai]
  calc x * (a * x * a⁻¹) = x * (x * (x⁻¹ * a * x * a⁻¹)) := by group
    _ = x * (x * (x⁻¹ * a * x * a⁻¹) * x⁻¹ * x) := by group
    _ = x * (x⁻¹ * a * x * a⁻¹ * x) := by rw [he]
    _ = a * x * a⁻¹ * x := by group

theorem false_of_e8
    [IsMulCommutative ↥V]
    (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8)
    (hCV : Subgroup.centralizer (V : Set G) = V)
    (hM : Subgroup.normalizer (L : Set G) = L ⊔ T) : False := by
  classical
  have h := s.setting.hyp
  obtain ⟨g, hgH, hg7, hgnot, hgcov⟩ := s.exists_seven h1222 hC hne hT hbig hCV hM
  have hzV := s.z_mem_V
  have hcz : C.cd ⟨z, hzV⟩ ∈ p1c := by
    have := s.mem
    rw [V1_eq h hC] at this
    exact (C.mem_subG ⟨z, hzV⟩).1 this
  have hcz0 : C.cd ⟨z, hzV⟩ ≠ 0 := fun e => s.ne_one (congrArg Subtype.val (C.cd_eq_zero.1 e))
  obtain ⟨cv, hcv, hcv0, hcvz⟩ := p1c_other _ hcz hcz0
  set v : G := (C.dc cv : G) with hv
  have hvV1 : v ∈ V1 T L V := by
    rw [V1_eq h hC, C.mem_subG, C.cd_dc cv (p1c_lt cv hcv)]
    exact hcv
  have hvV : v ∈ V := (inf_le_left : V1 T L V ≤ V) hvV1
  have hV2 : ∀ x ∈ V, x * x = 1 := fun x hx => by
    rw [← pow_two]; exact S127.sq_eq_one_of_mem h.hyp hx
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((S127.card_eq_of_1222 h1222 h).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hHz : ∀ y ∈ H714 T L V z, y * z = z * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (s.H_le_Gz h1222 hy)
  have hUH := s.H_le_normalizer_U h1222
  have hV1U : V1 T L V ≤ U714 T L V z := le_conjClosure _ _
  have hUT := (s.U_le_T h1222).1
  have hUN := s.U_le_normalizer_V h1222
  have hgkH : ∀ k : ℕ, g ^ k ∈ H714 T L V z := fun k => Subgroup.pow_mem _ hgH k
  set w := vk g v with hw
  have hwU : ∀ k, w k ∈ U714 T L V z := fun k =>
    (Subgroup.mem_normalizer_iff.mp (hUH (hgkH k)) v).mp (hV1U hvV1)
  have hw2 : ∀ k, w k * w k = 1 := fun k => by
    show g ^ (k : ℕ) * v * (g ^ (k : ℕ))⁻¹ * (g ^ (k : ℕ) * v * (g ^ (k : ℕ))⁻¹) = 1
    calc g ^ (k : ℕ) * v * (g ^ (k : ℕ))⁻¹ * (g ^ (k : ℕ) * v * (g ^ (k : ℕ))⁻¹) =
        g ^ (k : ℕ) * (v * v) * (g ^ (k : ℕ))⁻¹ := by group
      _ = 1 := by rw [hV2 v hvV, mul_one, mul_inv_cancel]
  have hwz : ∀ k, w k * z = z * w k := fun k => hHz _ (T_le_H (hUT (hwU k)))
  have hgz : ∀ k : ℕ, g ^ k * z * (g ^ k)⁻¹ = z := fun k => by
    rw [hHz _ (hgkH k), mul_inv_cancel_right]
  have hgen : ∀ y ∈ H714 T L V z, ∀ x ∈ V1 T L V, ∃ k : Fin 7, y * x * y⁻¹ = 1 ∨
      y * x * y⁻¹ = z ∨ y * x * y⁻¹ = w k ∨ y * x * y⁻¹ = z * w k := by
    intro y hy x hx
    obtain ⟨k, hk7, hkN⟩ := hgcov y hy
    set n := (g ^ k)⁻¹ * y with hn
    have hyn : y = g ^ k * n := by rw [hn]; group
    have hnx : n * x * n⁻¹ ∈ V1 T L V := (Subgroup.mem_normalizer_iff.mp hkN x).mp hx
    refine ⟨⟨k, hk7⟩, ?_⟩
    have e : y * x * y⁻¹ = g ^ k * (n * x * n⁻¹) * (g ^ k)⁻¹ := by rw [hyn]; group
    rcases s.V1_cases hC hcv hcv0 hcvz hnx with e2 | e2 | e2 | e2 <;> rw [e, e2]
    · left; group
    · right; left; exact hgz k
    · right; right; left; rfl
    · right; right; right
      show g ^ k * (z * v) * (g ^ k)⁻¹ = z * (g ^ k * v * (g ^ k)⁻¹)
      calc g ^ k * (z * v) * (g ^ k)⁻¹ = (g ^ k * z * (g ^ k)⁻¹) * (g ^ k * v * (g ^ k)⁻¹) := by
            group
        _ = z * (g ^ k * v * (g ^ k)⁻¹) := by rw [hgz k]
  have hv1 : v ≠ 1 := fun e => hcv0 (by
    rw [← C.cd_dc cv (p1c_lt cv hcv)]
    exact C.cd_eq_zero.2 (Subtype.ext e))
  have hvz : v ≠ z := fun e => hcvz (by
    rw [← C.cd_dc cv (p1c_lt cv hcv)]
    exact congrArg C.cd (Subtype.ext e))
  have hzz : z * z = 1 := hV2 z hzV
  have hnorm : ∀ n ∈ H714 T L V z, (n * v * n⁻¹ = v ∨ n * v * n⁻¹ = z * v) →
      n ∈ Subgroup.normalizer (V1 T L V : Set G) := by
    intro n hn hnv
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hnz : n * z * n⁻¹ = z := by rw [hHz n hn, mul_inv_cancel_right]
    rcases s.V1_cases hC hcv hcv0 hcvz hx with e | e | e | e <;> rw [e]
    · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
    · rw [hnz]; exact s.mem
    · rcases hnv with e2 | e2 <;> rw [e2]
      · exact hvV1
      · exact Subgroup.mul_mem _ s.mem hvV1
    · have e3 : n * (z * v) * n⁻¹ = (n * z * n⁻¹) * (n * v * n⁻¹) := by group
      rw [e3, hnz]
      rcases hnv with e2 | e2 <;> rw [e2]
      · exact Subgroup.mul_mem _ s.mem hvV1
      · rw [← mul_assoc, hzz, one_mul]; exact hvV1
  have huniq : ∀ j j' : Fin 7, (w j = w j' ∨ w j = z * w j') → j = j' := by
    have key : ∀ j j' : Fin 7, j' < j → ¬ (w j = w j' ∨ w j = z * w j') := by
      intro j j' hlt hcase
      set n := (g ^ (j' : ℕ))⁻¹ * g ^ (j : ℕ) with hn
      have hnH : n ∈ H714 T L V z := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hgkH _)) (hgkH _)
      have hn' : n = g ^ ((j : ℕ) - j') := by
        rw [hn, ← pow_sub_mul_pow g (le_of_lt hlt), pow_mul_comm, inv_mul_cancel_left]
      have hnv : n * v * n⁻¹ = v ∨ n * v * n⁻¹ = z * v := by
        have e1 : n * v * n⁻¹ = (g ^ (j' : ℕ))⁻¹ * w j * g ^ (j' : ℕ) := by
          rw [hn, hw]; simp only [vk]; group
        rcases hcase with e | e
        · left
          rw [e1, e]
          simp only [hw, vk]
          group
        · right
          rw [e1, e]
          simp only [hw, vk]
          have : (g ^ (j' : ℕ))⁻¹ * z * g ^ (j' : ℕ) = z := by
            have := hgz j'
            calc (g ^ (j' : ℕ))⁻¹ * z * g ^ (j' : ℕ) =
                (g ^ (j' : ℕ))⁻¹ * (g ^ (j' : ℕ) * z * (g ^ (j' : ℕ))⁻¹) * g ^ (j' : ℕ) := by
                  rw [this]
              _ = z := by group
          calc (g ^ (j' : ℕ))⁻¹ * (z * (g ^ (j' : ℕ) * v * (g ^ (j' : ℕ))⁻¹)) * g ^ (j' : ℕ) =
              ((g ^ (j' : ℕ))⁻¹ * z * g ^ (j' : ℕ)) * v := by group
            _ = z * v := by rw [this]
      have hN := hnorm n hnH hnv
      rw [hn'] at hN
      exact hgnot _ (by omega) (by omega) hN
    intro j j' hcase
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · exfalso
      apply key j' j hlt
      rcases hcase with e | e
      · exact Or.inl e.symm
      · right
        rw [e, ← mul_assoc, hzz, one_mul]
    · exact heq
    · exact absurd hcase (key j j' hgt)
  let c : Fin 7 → Prop := fun d => v * w d = w d * v
  have hc0 : c 0 := by
    show v * vk g v 0 = vk g v 0 * v
    rw [vk_zero]
  have hcneg : ∀ d, c (-d) ↔ c d := fun d => commute_vk_neg hg7 v d
  have hcij : ∀ i j : Fin 7, w i * w j = w j * w i ↔ c (j - i) := fun i j => commute_vk hg7 v i j
  set b : ℕ := (if c 1 then 1 else 0) + (if c 2 then 2 else 0) + (if c 3 then 4 else 0) with hb
  obtain ⟨hb0, hb1, hb2, hb8, hb7⟩ := cpat_bits (decide (c 1)) (decide (c 2)) (decide (c 3))
  have hbdef : b = (if decide (c 1) then 1 else 0) + (if decide (c 2) then 2 else 0) +
      (if decide (c 3) then 4 else 0) := by simp [hb]
  rw [← hbdef] at hb0 hb1 hb2 hb8 hb7
  have hcp : ∀ d : Fin 7, cpat b d = true ↔ c d := by
    intro d
    fin_cases d
    · simp only [cpat]; exact ⟨fun _ => hc0, fun _ => trivial⟩
    · simp only [cpat]
      show b.testBit 0 = true ↔ c 1
      rw [hb0]; simp
    · simp only [cpat]
      show b.testBit 1 = true ↔ c 2
      rw [hb1]; simp
    · simp only [cpat]
      show b.testBit 2 = true ↔ c 3
      rw [hb2]; simp
    · simp only [cpat]
      show b.testBit 2 = true ↔ c 4
      rw [hb2, ← hcneg 4, show (-4 : Fin 7) = 3 by decide]; simp
    · simp only [cpat]
      show b.testBit 1 = true ↔ c 5
      rw [hb1, ← hcneg 5, show (-5 : Fin 7) = 2 by decide]; simp
    · simp only [cpat]
      show b.testBit 0 = true ↔ c 6
      rw [hb0, ← hcneg 6, show (-6 : Fin 7) = 1 by decide]; simp
  by_cases hall : b = 7
  ·
    obtain ⟨h1, h2, h3⟩ := hb7 hall
    have hc : ∀ d, c d := by
      intro d
      have := (hcp d).1
      apply this
      fin_cases d <;> simp [cpat, hb0, hb1, hb2, h1, h2, h3]
    have hle : U714 T L V z ≤ Subgroup.closure ({z} ∪ Set.range w) := by
      rw [← s.conjClosure_eq h1222]
      refine conjClosure_le fun y hy x hx => ?_
      obtain ⟨k, hk⟩ := hgen y hy x hx
      rcases hk with e | e | e | e <;> rw [e]
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Or.inl rfl)
      · exact Subgroup.subset_closure (Or.inr ⟨k, rfl⟩)
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
          (Subgroup.subset_closure (Or.inr ⟨k, rfl⟩))
    have hcomm : ∀ x ∈ ({z} ∪ Set.range w : Set G), ∀ y ∈ ({z} ∪ Set.range w : Set G),
        x * y = y * x := by
      rintro x (rfl | ⟨i, rfl⟩) y (rfl | ⟨j, rfl⟩)
      · rfl
      · exact (hwz j).symm
      · exact hwz i
      · exact (hcij i j).2 (hc _)
    have hab := comm_closure hcomm
    obtain ⟨u, huU, huN, hu⟩ := s.exists_U_code h1222 hC hne hT hbig i1_mem_e8
    set v₁ := C.dc 10 with hv₁
    have hv₁c : C.cd v₁ = 10 := C.cd_dc 10 (by norm_num)
    have hv₁V1 : (v₁ : G) ∈ V1 T L V := by
      rw [V1_eq h hC]
      exact (C.mem_subG v₁).2 (hv₁c ▸ mem_p1c_10)
    have hcomm' := hab u (hle huU) v₁ (hle (hV1U hv₁V1))
    have h2 : C.cd ⟨u * v₁ * u⁻¹, (Subgroup.mem_normalizer_iff.1 huN v₁).1 v₁.2⟩ = 15 := by
      rw [cd_conj C huN v₁, hu, hv₁c, i1_app_10]
    have h3 : (⟨u * v₁ * u⁻¹, (Subgroup.mem_normalizer_iff.1 huN v₁).1 v₁.2⟩ : ↥V) = v₁ :=
      Subtype.ext (show u * v₁ * u⁻¹ = v₁ by rw [hcomm', mul_inv_cancel_right])
    rw [h3, hv₁c] at h2
    exact absurd h2 (by norm_num)
  ·
    have hb7' : b < 7 := by omega
    apply s.not_le_cTil h1222
    intro a ha
    have haH : a ∈ H714 T L V z := V_le_H714 T L V z ha
    have ha2 : a * a = 1 := hV2 a ha
    have hperm : ∀ k : Fin 7, ∃ j : Fin 7, a * w k * a⁻¹ = w j ∨ a * w k * a⁻¹ = z * w j := by
      intro k
      obtain ⟨j, hj⟩ := hgen (a * g ^ (k : ℕ)) (Subgroup.mul_mem _ haH (hgkH _)) v hvV1
      have e : a * g ^ (k : ℕ) * v * (a * g ^ (k : ℕ))⁻¹ = a * w k * a⁻¹ := by
        simp only [hw, vk]; group
      rw [e] at hj
      refine ⟨j, ?_⟩
      have hne1 : a * w k * a⁻¹ ≠ 1 := fun e1 => by
        have : w k = 1 := by
          calc w k = a⁻¹ * (a * w k * a⁻¹) * a := by group
            _ = 1 := by rw [e1]; group
        apply hv1
        calc v = (g ^ (k : ℕ))⁻¹ * w k * g ^ (k : ℕ) := by simp only [hw, vk]; group
          _ = 1 := by rw [this]; group
      have hnez : a * w k * a⁻¹ ≠ z := fun e1 => by
        have : w k = z := by
          calc w k = a⁻¹ * (a * w k * a⁻¹) * a := by group
            _ = a⁻¹ * (z * a) := by rw [e1]; group
            _ = a⁻¹ * (a * z) := by rw [hHz a haH]
            _ = z := by group
        apply hvz
        calc v = (g ^ (k : ℕ))⁻¹ * w k * g ^ (k : ℕ) := by simp only [hw, vk]; group
          _ = (g ^ (k : ℕ))⁻¹ * (z * g ^ (k : ℕ)) := by rw [this]; group
          _ = (g ^ (k : ℕ))⁻¹ * (g ^ (k : ℕ) * z) := by rw [hHz _ (hgkH _)]
          _ = z := by group
      rcases hj with e1 | e1 | e1 | e1
      · exact absurd e1 hne1
      · exact absurd e1 hnez
      · exact Or.inl e1
      · exact Or.inr e1
    choose π hπ using hperm
    have haz : a * z = z * a := hHz a haH
    have hconj : ∀ k, ∃ ε : Bool, a * w k * a⁻¹ = (if ε then z else 1) * w (π k) := by
      intro k
      rcases hπ k with e | e
      · exact ⟨false, by rw [e]; simp⟩
      · exact ⟨true, by rw [e]; simp⟩
    have hzε : ∀ (ε : Bool) (y : G), (y = 1 ∨ y = z) → ∀ k, y * w k = w k * y := by
      intro ε y hy k
      rcases hy with rfl | rfl
      · simp
      · exact (hwz k).symm
    have hπ0 : π 0 = 0 := by
      have hav : a * w 0 * a⁻¹ = w 0 := by
        show a * vk g v 0 * a⁻¹ = vk g v 0
        rw [vk_zero, hVc a ha v hvV, mul_inv_cancel_right]
      rcases hπ 0 with e | e
      · exact (huniq _ _ (Or.inl (hav.symm.trans e))).symm
      · exact (huniq _ _ (Or.inr (hav.symm.trans e))).symm
    have hπinj : Function.Injective π := by
      intro k k' hkk
      apply huniq
      have h1 := hπ k
      have h2 := hπ k'
      rw [← hkk] at h2
      have key : ∀ y : G, a * y * a⁻¹ = a * w k' * a⁻¹ → y = w k' := fun y e => by
        have := congrArg (fun q => a⁻¹ * q * a) e
        simpa [mul_assoc] using this
      have keyz : ∀ y : G, a * y * a⁻¹ = z * (a * w k' * a⁻¹) → y = z * w k' := fun y e => by
        have e2 : a * y * a⁻¹ = a * (z * w k') * a⁻¹ := by
          rw [e]
          calc z * (a * w k' * a⁻¹) = (z * a) * w k' * a⁻¹ := by group
            _ = a * (z * w k') * a⁻¹ := by rw [← haz]; group
        have := congrArg (fun q => a⁻¹ * q * a) e2
        simpa [mul_assoc] using this
      rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2
      · exact Or.inl (key _ (e1.trans e2.symm))
      · right
        apply keyz
        rw [e1, e2, ← mul_assoc, hzz, one_mul]
      · right
        apply keyz
        rw [e1, e2]
      · exact Or.inl (key _ (e1.trans e2.symm))
    have hζ : ∀ (ε : Bool) (q : G), q ∈ U714 T L V z →
        (if ε then z else 1) * q = q * (if ε then z else 1) := by
      intro ε q hq
      cases ε
      · simp
      · exact (hHz q (T_le_H (hUT hq))).symm
    have hζζ : ∀ ε δ : Bool, (if ε then z else 1) * (if δ then z else 1) =
        (if δ then z else 1) * (if ε then z else 1) := by
      intro ε δ; cases ε <;> cases δ <;> simp
    have hπc : ∀ i j : Fin 7, c (π j - π i) ↔ c (j - i) := by
      intro i j
      rw [← hcij, ← hcij]
      obtain ⟨ε, hε⟩ := hconj i
      obtain ⟨δ, hδ⟩ := hconj j
      rw [← comm_conj_iff a (w i) (w j), hε, hδ,
        comm_central (hζ δ _ (hwU _)) (hζ ε _ (hwU _)) (hζζ ε δ)]
    have hπm : ∀ k : Fin 7, π k ≠ k → c (π k - k) := by
      intro k _
      rw [← hcij]
      obtain ⟨ε, hε⟩ := hconj k
      have h1 := comm_conj hVc ha ha2 (hUN (hwU k)) (by rw [hw2]; exact V.one_mem)
      rw [hε] at h1
      have hzk : (if ε then z else 1) * w k = w k * (if ε then z else 1) := by
        cases ε
        · simp
        · exact (hwz k).symm
      have : w k * w (π k) = w (π k) * w k := by
        have e2 : (if ε then z else 1) * (w k * w (π k)) =
            (if ε then z else 1) * (w (π k) * w k) := by
          calc (if ε then z else 1) * (w k * w (π k)) =
              w k * ((if ε then z else 1) * w (π k)) := by rw [← mul_assoc, hzk, mul_assoc]
            _ = (if ε then z else 1) * w (π k) * w k := h1
            _ = (if ε then z else 1) * (w (π k) * w k) := by rw [mul_assoc]
        exact mul_left_cancel e2
      exact this
    have hπne : ∀ i : Fin 6, π i.succ ≠ 0 := fun i e =>
      Fin.succ_ne_zero i (hπinj (e.trans hπ0.symm))
    let f : Fin 6 → Fin 6 := fun i => (π i.succ).pred (hπne i)
    have hfinj : Function.Injective f := by
      intro i j hij
      have : π i.succ = π j.succ := by
        have := congrArg Fin.succ hij
        simpa [f, Fin.succ_pred] using this
      exact Fin.succ_injective _ (hπinj this)
    set l := (List.finRange 6).map f with hl
    have hlnd : l.Nodup := (List.nodup_finRange 6).map hfinj
    have hlperm : l ∈ perms6 := by
      rw [perms6, List.mem_permutations]
      refine (List.perm_ext_iff_of_nodup hlnd (List.nodup_finRange 6)).2 fun x => ?_
      constructor
      · exact fun _ => List.mem_finRange x
      · intro _
        obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.mp hfinj) x
        exact List.mem_map.2 ⟨i, List.mem_finRange i, hi⟩
    have hfl : fl l = f := by
      funext i
      simp [fl, hl, List.getD_eq_getElem?_getD]
    have hext : ∀ k : Fin 7, ext7 f k = π k := by
      intro k
      unfold ext7
      split_ifs with hk
      · rw [show k = 0 from Fin.ext hk, hπ0]
      · have hk' : (⟨k.val - 1, by omega⟩ : Fin 6).succ = k := Fin.ext (by simp; omega)
        simp only [f, hk', Fin.succ_pred]
    have hOK : cycOK b (fl l) = true := by
      rw [hfl]
      simp only [cycOK, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
      intro i j
      rw [hext, hext]
      cases hb1' : cpat b (π j - π i) <;> cases hb2' : cpat b (j - i)
      · rfl
      · exact absurd ((hπc i j).2 ((hcp _).1 hb2')) (by rw [← hcp]; simp [hb1'])
      · exact absurd ((hπc i j).1 ((hcp _).1 hb1')) (by rw [← hcp]; simp [hb2'])
      · rfl
    have hMoved : cycMoved b (fl l) = true := by
      rw [hfl]
      simp only [cycMoved, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
        beq_iff_eq]
      intro k
      rw [hext]
      by_cases hk : π k = k
      · exact Or.inl hk
      · exact Or.inr ((hcp _).2 (hπm k hk))
    have hlid := cert55_cyc l hlperm b hb7' hOK hMoved
    have hπid : ∀ k, π k = k := by
      intro k
      by_cases hk : k = 0
      · rw [hk, hπ0]
      · have hfid : ∀ i, f i = i := by
          intro i
          have := congrArg (fun l' => l'.getD i 0) hlid
          simpa [hl, List.getD_eq_getElem?_getD] using this
        have hk' : ¬ (k : ℕ) = 0 := fun h0 => hk (Fin.ext h0)
        rw [← hext k]
        unfold ext7
        simp only [hk', ↓reduceDIte, hfid]
        exact Fin.ext (by simp; omega)
    have hzc : ∀ u ∈ U714 T L V z, u * z = z * u := fun u hu => hHz u (T_le_H (hUT hu))
    let S : Subgroup G :=
      { carrier := {u | u ∈ U714 T L V z ∧ a * u * a⁻¹ * u⁻¹ ∈ Subgroup.zpowers z}
        mul_mem' := by
          rintro u u' ⟨hu, hcu⟩ ⟨hu', hcu'⟩
          refine ⟨Subgroup.mul_mem _ hu hu', ?_⟩
          obtain ⟨m, hm⟩ := hcu'
          have e : a * (u * u') * a⁻¹ * (u * u')⁻¹ =
              (a * u * a⁻¹ * u⁻¹) * (u * (a * u' * a⁻¹ * u'⁻¹) * u⁻¹) := by group
          rw [e, ← hm]
          have hzu : u * z ^ m * u⁻¹ = z ^ m := by
            rw [(Commute.zpow_right (hzc u hu) m).eq, mul_inv_cancel_right]
          rw [hzu]
          exact Subgroup.mul_mem _ hcu (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) m)
        one_mem' := ⟨Subgroup.one_mem _, by simp⟩
        inv_mem' := by
          rintro u ⟨hu, hcu⟩
          refine ⟨Subgroup.inv_mem _ hu, ?_⟩
          obtain ⟨m, hm⟩ := hcu
          have e : a * u⁻¹ * a⁻¹ * u⁻¹⁻¹ = u⁻¹ * (a * u * a⁻¹ * u⁻¹)⁻¹ * u := by group
          rw [e, ← hm, ← zpow_neg]
          have : u⁻¹ * z ^ (-m) * u = z ^ (-m) := by
            have hc := (Commute.zpow_right (hzc u hu) (-m)).eq
            calc u⁻¹ * z ^ (-m) * u = u⁻¹ * (z ^ (-m) * u) := by group
              _ = u⁻¹ * (u * z ^ (-m)) := by rw [hc]
              _ = z ^ (-m) := by group
          rw [this]
          exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) _ }
    have hsub : conjClosure (V1 T L V) (H714 T L V z) ≤ S := by
      refine conjClosure_le fun y hy x hx => ?_
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hUH hy) x).mp (hV1U hx), ?_⟩
      obtain ⟨k, hk⟩ := hgen y hy x hx
      have hwk : a * w k * a⁻¹ * (w k)⁻¹ ∈ Subgroup.zpowers z := by
        rcases hπ k with e | e <;> rw [e, hπid k]
        · rw [mul_inv_cancel]; exact Subgroup.one_mem _
        · rw [mul_inv_cancel_right]; exact Subgroup.mem_zpowers z
      rcases hk with e | e | e | e <;> rw [e]
      · simp
      · rw [haz, mul_inv_cancel_right, mul_inv_cancel]; exact Subgroup.one_mem _
      · exact hwk
      · obtain ⟨m, hm⟩ := hwk
        have hzm : z * z ^ m = z ^ m * z := (Commute.zpow_right (Commute.refl z) m).eq
        have e2 : a * (z * w k) * a⁻¹ * (z * w k)⁻¹ = z * (a * w k * a⁻¹ * (w k)⁻¹) * z⁻¹ := by
          calc a * (z * w k) * a⁻¹ * (z * w k)⁻¹ = (a * z) * w k * a⁻¹ * (w k)⁻¹ * z⁻¹ := by
                group
            _ = z * (a * w k * a⁻¹ * (w k)⁻¹) * z⁻¹ := by rw [haz]; group
        rw [e2, ← hm, hzm, mul_inv_cancel_right]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) m
    refine ⟨haH, fun u hu => ?_⟩
    exact (hsub ((s.conjClosure_eq h1222).symm ▸ hu)).2

end CFSG.Quasithin.H13.S127.L715.Set714
