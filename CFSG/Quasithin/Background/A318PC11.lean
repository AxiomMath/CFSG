module

public import CFSG.Quasithin.Background.A318PC9
public import CFSG.Quasithin.Background.A318PL3Lin

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

section Act

variable {X : Type} [Group X] {S : Subgroup X} [hSn : S.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool}

variable (S) in
@[expose] def toNormalizer : X →* Subgroup.normalizer (S : Set X) where
  toFun g := ⟨g, mem_normalizer_of_normal g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem slAct_one_apply (e : ↥S ≃* slPi π 3 (p ^ f) K) (s : slPi π 3 (p ^ f) K) :
    slAct e ⟨(1 : X), mem_normalizer_of_normal 1⟩ s = s := by
  have : (⟨(1 : X), mem_normalizer_of_normal 1⟩ : Subgroup.normalizer (S : Set X)) = 1 := rfl
  rw [this, map_one, MulAut.one_apply]

theorem isPGLAt_conj_of_field {e : ↥S ≃* slPi π 3 (p ^ f) K} {g j : X} {σ : K ≃+* K}
    (hg : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨g, mem_normalizer_of_normal g⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL σ s)
    {A : GL (Fin 3) K} (hA : frobGL σ A = A) (hj : IsPGLAt e j A) :
    IsPGLAt e (g * j * g⁻¹) A := by
  refine ⟨hj.1, fun s => ?_⟩
  set s' := slAct e ⟨g⁻¹, mem_normalizer_of_normal g⁻¹⟩ s with hs'
  have h1 : slAct e ⟨g, mem_normalizer_of_normal g⟩ s' = s := by
    have hmul : (⟨g * g⁻¹, mem_normalizer_of_normal _⟩ : Subgroup.normalizer (S : Set X)) =
        ⟨1, mem_normalizer_of_normal 1⟩ := Subtype.ext (mul_inv_cancel g)
    have := slAct_mul_apply e g g⁻¹ s
    rw [hmul, slAct_one_apply] at this
    exact this.symm
  have h2 : frobGL σ (s' : GL (Fin 3) K) = (s : GL (Fin 3) K) := by
    rw [← hg s', h1]
  have h3 : slAct e ⟨g * j * g⁻¹, mem_normalizer_of_normal _⟩ s =
      slAct e ⟨g, mem_normalizer_of_normal g⟩ (slAct e ⟨j, mem_normalizer_of_normal j⟩ s') := by
    rw [slAct_mul_apply e (g * j) g⁻¹ s, slAct_mul_apply e g j s']
  rw [h3, hg, hj.2 s', map_mul, map_mul, map_inv, hA, h2]

theorem coe_slAct_mul_of_field {e : ↥S ≃* slPi π 3 (p ^ f) K} {g j' : X} {σ : K ≃+* K}
    (hg : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨g, mem_normalizer_of_normal g⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL σ s)
    {B : GL (Fin 3) K} (hj' : IsPGLAt e j' B) (s : slPi π 3 (p ^ f) K) :
    ((slAct e ⟨j' * g, mem_normalizer_of_normal _⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      B * frobGL σ s * B⁻¹ := by
  rw [slAct_mul_apply e j' g s, hj'.2, hg]

theorem slAct_cube_of_field {e : ↥S ≃* slPi π 3 (p ^ f) K} {g : X} {σ : K ≃+* K}
    (hσ : orderOf σ = 3)
    (hg : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨g, mem_normalizer_of_normal g⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL σ s)
    (s : slPi π 3 (p ^ f) K) :
    slAct e ⟨g ^ 3, mem_normalizer_of_normal _⟩ s = s := by
  have hc : (⟨g ^ 3, mem_normalizer_of_normal _⟩ : Subgroup.normalizer (S : Set X)) =
      ⟨g * (g * g), mem_normalizer_of_normal _⟩ := Subtype.ext (pow_three g)
  have h2 : slAct e ⟨g ^ 3, mem_normalizer_of_normal _⟩ s =
      slAct e ⟨g, mem_normalizer_of_normal g⟩ (slAct e ⟨g, mem_normalizer_of_normal g⟩
        (slAct e ⟨g, mem_normalizer_of_normal g⟩ s)) := by
    rw [hc, slAct_mul_apply e g (g * g) s, slAct_mul_apply e g g s]
  apply Subtype.ext
  rw [h2, hg, hg, hg]
  exact frobGL_three hσ _

end Act

section PureField

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool}

theorem false_of_pure_field
    (hQ : CFSG.IsQuasisimple ↥S) (hS2 : 2 ≤ CFSG.Open.pRank 3 S)
    (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) (e : ↥S ≃* slPi π 3 (p ^ f) K)
    (hZ : Nat.card (Subgroup.center ↥S) = 3)
    (hCS : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c ∈ S) {x : X} (hx : orderOf x = 3)
    (hxS : x ∉ S) {g : X} {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (hg : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨g, mem_normalizer_of_normal g⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL σ s)
    (hgH : g ∉ S ⊔ Subgroup.zpowers x) : False := by
  classical
  obtain ⟨y, hxy, hy3, -, hnon, -, -⟩ := central_type_iii hQ hS2 hX hK hq hq2 e hx hxS
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hu3 : ((Units.mk0 τ hτ0 : Kˣ) : K) ^ 3 = 1 := hτ
  have hu1 : (Units.mk0 τ hτ0 : Kˣ) ≠ 1 := fun h => hτ1 (congrArg Units.val h)
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hστ : σ τ = τ := ringEquiv_fix_cube_root hσ3 hτ hτ1
  obtain ⟨j, hjA, hj, hj3Z, hj3ne, -⟩ := exists_diagE_element hX hK hq e hx hxy hy3 hnon hu3 hu1
  set Z : Subgroup X := (Subgroup.center ↥S).map S.subtype with hZdef
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Subgroup.card_map_of_injective S.subtype_injective, hZ]
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => by
    have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    rw [hZcard] at this
    exact congrArg Subtype.val this
  have hZmem : ∀ a ∈ Subgroup.centralizer (S : Set X), a ∈ Z := fun a haC =>
    ⟨⟨a, hCS a (fun s hs => ((Subgroup.mem_centralizer_iff.1 haC) s hs).symm)⟩,
      Subgroup.mem_center_iff.2 fun s =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.1 haC) s s.2), rfl⟩
  have hg3C : g ^ 3 ∈ Subgroup.centralizer (S : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 := conj_eq_of_slAct_eq e (g ^ 3) (e ⟨t, ht⟩) (slAct_cube_of_field hσ hg _)
    have h2 : ((e.symm (e ⟨t, ht⟩) : ↥S) : X) = t := by rw [MulEquiv.symm_apply_apply]
    rw [h2] at h1
    calc t * g ^ 3 = (g ^ 3 * t * (g ^ 3)⁻¹) * g ^ 3 := by rw [h1]
      _ = g ^ 3 * t := by group
  have hg3Z : g ^ 3 ∈ Z := hZmem _ hg3C
  have hA : frobGL σ (diagE (Units.mk0 τ hτ0)) = diagE (Units.mk0 τ hτ0) := by
    apply Units.ext
    rw [coe_frobGL, coe_diagE]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [hστ]
  have hconj := isPGLAt_conj_of_field hg hA hj
  have hcZ : j⁻¹ * (g * j * g⁻¹) ∈ Z := by
    have h1 := isPGLAt_mul e (isPGLAt_inv hj) hconj
    rw [inv_mul_cancel] at h1
    exact hZmem _ (mem_centralizer_of_isPGLAt_scalar h1 (one_mem _))
  have hj3ord : orderOf (j ^ 3) = 3 := orderOf_eq_prime (hZ3 _ hj3Z) hj3ne
  have hZeq : Z = Subgroup.zpowers (j ^ 3) :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hj3Z)
      (by rw [Nat.card_zpowers, hj3ord, hZcard])).symm
  have hjo : orderOf j = 9 := orderOf_eq_nine hZcard hj3Z hj3ne
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hZeq ▸ hcZ)
  obtain ⟨i', hi'⟩ := Subgroup.mem_zpowers_iff.1 (hZeq ▸ hg3Z)
  have hz3 : ∀ m : ℤ, (j ^ 3) ^ m = j ^ (3 * m) := fun m => by
    rw [_root_.zpow_mul]
    simp
  have hyr : g * j * g⁻¹ = j ^ (1 + 3 * i) := by
    have h1 : g * j * g⁻¹ = j * (j ^ 3) ^ i := by rw [hi]; group
    rw [h1, hz3, _root_.zpow_add, zpow_one]
  have hys : g ^ 3 = j ^ (3 * i') := by rw [← hz3, hi']
  have hmax : orderOf g ≤ 3 ^ 2 := by
    have h9 : g ^ 9 = 1 := by
      have := hZ3 _ hg3Z
      rw [← pow_mul] at this
      exact this
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h9)
  obtain ⟨a, ha⟩ := exists_cube_eq_one (m := 2) (by norm_num) (by rw [hjo]; norm_num) hyr hys hmax
  obtain ⟨n, hn⟩ : ∃ n : ℕ, j ^ a = j ^ n := by
    refine ⟨(a % 9).toNat, ?_⟩
    have h1 : j ^ (a % (orderOf j : ℤ)) = j ^ a := zpow_mod_orderOf j a
    rw [hjo] at h1
    have h2 : (a % ((9 : ℕ) : ℤ)) = (((a % 9).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      rfl
    rw [← h1, h2, zpow_natCast]
  set w : X := j ^ n * g with hw
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← hn]
    exact ha
  have hwS : w ∉ S := by
    intro hwS
    apply hgH
    have h1 : j ^ n ∈ S ⊔ Subgroup.zpowers x := pow_mem hjA n
    have h2 : g = (j ^ n)⁻¹ * w := by rw [hw]; group
    rw [h2]
    exact mul_mem (inv_mem h1) (Subgroup.mem_sup_left hwS)
  have hw1 : w ≠ 1 := fun h => hwS (h ▸ S.one_mem)
  have hword : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  obtain ⟨u', a₀, b₀, hu'τ, ha₀, hb₀, ha3, hb3, hab, ha1, hb1, hba, hba2⟩ :=
    exists_E9_slPi hK hq hτ hτ1 (g := 1) (one_mem _)
  have hjn : IsPGLAt e (j ^ n) (diagE (Units.mk0 τ hτ0) ^ n) := isPGLAt_pow hj n
  have hστu' : σ (u' : K) = u' := by rw [hu'τ]; exact hστ
  have hDcomm : Commute (diagE (Units.mk0 τ hτ0)) (diagTau hτ) :=
    commute_of_coe_diagonal (coe_diagE _) (coe_diagTau_eq_diagonal hτ)
  refine false_of_slPi_pair hX hword hwS e ha3 hb3 hab ha1 hb1 hba hba2 ?_ ?_
  · apply Subtype.ext
    rw [coe_slAct_mul_of_field hg hjn a₀, ha₀, frobGL_scalar hστu',
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u' _).eq, mul_inv_cancel_right]
  · apply Subtype.ext
    rw [coe_slAct_mul_of_field hg hjn b₀, hb₀, one_mul, inv_one, mul_one, frobGL_diagTau hτ hστ,
      (hDcomm.pow_left n).eq, mul_inv_cancel_right]

end PureField

end A318P

end CFSG.Quasithin
