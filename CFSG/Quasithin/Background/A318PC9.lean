module

public import CFSG.Quasithin.Background.A318PC6
public import CFSG.Quasithin.Background.A318PC8

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

section Diag

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem diagE_mem_glPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {u : Kˣ}
    (hu : (u : K) ^ 3 = 1) : diagE u ∈ glPi π 3 (p ^ f) K := by
  cases π
  · have h := hK.unitary
    rw [mem_glPi_false h]
    have hn := pow_succ_eq_one_of_modThree hq hu
    have h1 : h.bar (u : K) * (u : K) = 1 := by rw [h.bar_apply, ← pow_succ]; exact hn
    rw [coe_diagE]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, h1]
  · exact mem_glPi_true _ _

end Diag

section Lift

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool} {e : ↥S ≃* slPi π 3 (p ^ f) K}

omit [Finite X] in
theorem exists_lift_mem_sup (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {x : X}
    {y : GL (Fin 3) K} (hxy : IsPGLAt e x y)
    (hnon : ¬ ∃ l ∈ slPi π 3 (p ^ f) K, ∃ z ∈ zPi π 3 (p ^ f) K, y = l * z)
    {h : GL (Fin 3) K} (hh : h ∈ glPi π 3 (p ^ f) K) :
    ∃ a ∈ S ⊔ Subgroup.zpowers x, IsPGLAt e a h := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨k, -, l, hl, z, hz, rfl⟩ := exists_decomp_glPi hK hq hτ hτ1 hxy.1 hnon hh
  have hzs : z ∈ StatedScalars (Fin 3) K :=
    (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).2
  have hzH : z ∈ glPi π 3 (p ^ f) K := (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).1
  have hlS : ((e.symm ⟨l, hl⟩ : ↥S) : X) ∈ S ⊔ Subgroup.zpowers x :=
    Subgroup.mem_sup_left (e.symm ⟨l, hl⟩).2
  have hxk : x ^ k ∈ S ⊔ Subgroup.zpowers x :=
    pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) k
  have hlift : IsPGLAt e (((e.symm ⟨l, hl⟩ : ↥S) : X) * x ^ k) (l * y ^ k) :=
    isPGLAt_mul e (isPGLAt_symm hπ ⟨l, hl⟩) (isPGLAt_pow hxy k)
  exact ⟨_, mul_mem hlS hxk, isPGLAt_mul_scalar hlift hzs hzH⟩

theorem false_of_cube_one_diagE (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2)
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (e : ↥S ≃* slPi π 3 (p ^ f) K) {u : Kˣ}
    (hu3 : (u : K) ^ 3 = 1) (hu1 : u ≠ 1) {w : X} (hw3 : w ^ 3 = 1)
    (hw : IsPGLAt e w (diagE u)) : False := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hwS : w ∉ S := by
    intro hwS
    have h1 := isPGLAt_of_mem e hπ hwS
    obtain ⟨s, hs⟩ := isPGLAt_inv_mul_mem hK hq h1 hw
    have hD : diagE u = (e ⟨w, hwS⟩ : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) s := by
      rw [hs]
      group
    have hw3' : (e ⟨w, hwS⟩ : GL (Fin 3) K) ^ 3 = 1 := by
      have : (⟨w, hwS⟩ : ↥S) ^ 3 = 1 := Subtype.ext hw3
      have h2 : (e ⟨w, hwS⟩) ^ 3 = 1 := by rw [← map_pow, this, map_one]
      exact congrArg Subtype.val h2
    have hdetw : GeneralLinearGroup.det (e ⟨w, hwS⟩ : GL (Fin 3) K) = 1 :=
      Units.ext (by
        rw [GeneralLinearGroup.val_det_apply, Units.val_one]
        exact ((mem_slPi_iff hπ).1 (e ⟨w, hwS⟩).2).2)
    have hs3 : GeneralLinearGroup.scalar (Fin 3) (s ^ 3) = 1 := by
      have h3 := diagE_pow_three hu3
      have hc : Commute (e ⟨w, hwS⟩ : GL (Fin 3) K) (GeneralLinearGroup.scalar (Fin 3) s) :=
        commute_of_mem_statedScalars ⟨s, rfl⟩ (e ⟨w, hwS⟩ : GL (Fin 3) K)
      rw [hD, hc.mul_pow, hw3', one_mul, ← map_pow] at h3
      exact h3
    have hs3' : s ^ 3 = 1 := by
      apply scalar_injective_three (K := K)
      rw [hs3, map_one]
    have hdet : u = s ^ 3 := by
      have := congrArg GeneralLinearGroup.det hD
      rwa [det_diagE, map_mul, hdetw, one_mul, det_scalar_three] at this
    exact hu1 (hdet.trans hs3')
  have hw1 : w ≠ 1 := fun h => hwS (h ▸ S.one_mem)
  have hword : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  exact false_of_diagonal hX hword hwS hK hq e hw (g := 1) (one_mem _) (D := diagE u)
    (d := ![(u : K), 1, 1]) (by simp) (coe_diagE u)

end Lift

section Native

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool}

omit [Finite X] in
theorem normal_centralizer_of_normal : (Subgroup.centralizer (S : Set X)).Normal := by
  constructor
  intro c hc g
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := by simpa using hSn.conj_mem s hs g⁻¹
  have := hc _ hs'
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [this]
    _ = g * c * g⁻¹ * s := by group

omit [Finite X] in
theorem exists_diagE_element [Finite X] (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2)
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (e : ↥S ≃* slPi π 3 (p ^ f) K) {x : X}
    (hx : orderOf x = 3) {y : GL (Fin 3) K} (hxy : IsPGLAt e x y)
    (hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hnon : ¬ ∃ l ∈ slPi π 3 (p ^ f) K, ∃ z ∈ zPi π 3 (p ^ f) K, y = l * z) {u : Kˣ}
    (hu3 : (u : K) ^ 3 = 1) (hu1 : u ≠ 1) :
    ∃ j ∈ S ⊔ Subgroup.zpowers x, IsPGLAt e j (diagE u) ∧
      j ^ 3 ∈ (Subgroup.center ↥S).map S.subtype ∧ j ^ 3 ≠ 1 ∧
      ∀ c ∈ Subgroup.centralizer (S : Set X), (c * j) ^ 3 ≠ 1 := by
  have hDH : diagE u ∈ glPi π 3 (p ^ f) K := diagE_mem_glPi hK hq hu3
  obtain ⟨j, hjA, hj⟩ := exists_lift_mem_sup hK hq hxy hnon hDH
  have hno : ∀ c ∈ Subgroup.centralizer (S : Set X), (c * j) ^ 3 ≠ 1 := by
    intro c hc hcj
    have hc1 : IsPGLAt e c 1 := isPGLAt_of_mem_centralizer e hc
    have h2 := isPGLAt_mul e hc1 hj
    rw [one_mul] at h2
    exact false_of_cube_one_diagE hX hK hq e hu3 hu1 hcj h2
  have hj3C : j ^ 3 ∈ Subgroup.centralizer (S : Set X) := by
    have h1' := isPGLAt_pow hj 3
    rw [diagE_pow_three hu3] at h1'
    exact mem_centralizer_of_isPGLAt_scalar h1' (one_mem _)
  have hj3A : j ^ 3 ∈ S ⊔ Subgroup.zpowers x := pow_mem hjA 3
  have hj3S : j ^ 3 ∈ S := mem_of_mem_sup_of_centralizes hK hq hx hxy hy3 hnon hj3A hj3C
  refine ⟨j, hjA, hj, ⟨⟨j ^ 3, hj3S⟩, Subgroup.mem_center_iff.2 fun s =>
    Subtype.ext ((Subgroup.mem_centralizer_iff.1 hj3C) s s.2), rfl⟩, ?_, hno⟩
  have := hno 1 (one_mem _)
  simpa using this

theorem centralizer_le_S_native
    (hQ : CFSG.IsQuasisimple ↥S) (hS2 : 2 ≤ CFSG.Open.pRank 3 S)
    (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) (e : ↥S ≃* slPi π 3 (p ^ f) K)
    (hZ : Nat.card (Subgroup.center ↥S) = 3) (hP : CFSG.pPrimeCore 3 X = ⊥) {x : X}
    (hx : orderOf x = 3) (hxS : x ∉ S) :
    ∀ c : X, (∀ s ∈ S, c * s = s * c) → c ∈ S := by
  classical
  obtain ⟨y, hxy, hy3, -, hnon, -, -⟩ := central_type_iii hQ hS2 hX hK hq hq2 e hx hxS
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set C : Subgroup X := Subgroup.centralizer (S : Set X) with hC
  have hCn : C.Normal := normal_centralizer_of_normal
  set Z : Subgroup X := (Subgroup.center ↥S).map S.subtype with hZdef
  have hZn : Z.Normal := normal_map_center
  have hZmem : ∀ a ∈ C, a ∈ S → a ∈ Z := fun a haC haS =>
    ⟨⟨a, haS⟩, Subgroup.mem_center_iff.2 fun s =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 haC) s s.2), rfl⟩
  have hZC : Z ≤ C := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨s, hs⟩)
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Subgroup.card_map_of_injective S.subtype_injective, hZ]
  have h1 : ∀ c ∈ C, orderOf c = 3 → c ∈ Z := fun c hcC hc3 =>
    hZmem c hcC (mem_of_centralizes_of_orderOf_three hS2 hX hc3
      (fun s hs => ((Subgroup.mem_centralizer_iff.1 hcC) s hs).symm))
  have hu3 : ((Units.mk0 τ hτ0 : Kˣ) : K) ^ 3 = 1 := hτ
  have hu1 : (Units.mk0 τ hτ0 : Kˣ) ≠ 1 := fun h => hτ1 (congrArg Units.val h)
  obtain ⟨j, -, -, hj3Z, hj3ne, hno⟩ := exists_diagE_element hX hK hq e hx hxy hy3 hnon hu3 hu1
  have h3 := three_elements_mem_of_arith hZC hZcard h1 hj3Z hj3ne hno
  have hZc : ∀ z ∈ Z, ∀ c ∈ C, c * z = z * c := by
    rintro _ ⟨z₀, -, rfl⟩ c hc
    exact ((Subgroup.mem_centralizer_iff.1 hc) z₀ z₀.2).symm
  have hCZ := normal_le_of_three_elements hZC hZcard hZc h3 hP
  intro c hc
  have hcC : c ∈ C := Subgroup.mem_centralizer_iff.2 fun s hs => (hc s hs).symm
  obtain ⟨z, -, hz⟩ := hCZ hcC
  rw [← hz]
  exact z.2

end Native

end A318P

end CFSG.Quasithin
