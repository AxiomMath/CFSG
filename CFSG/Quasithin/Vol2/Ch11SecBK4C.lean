module

public import CFSG.Quasithin.Vol2.Ch11SecBK4B
public import CFSG.Quasithin.Vol2.Ch11G2Q8InvField
public import CFSG.Quasithin.Background.SmithB42G2Rank

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall
open CFSG.Open (quasithinG2 IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

namespace BK4

theorem card_mul_card_fix_le {K M : Type} [Field K] [Finite K] [AddCommGroup M] [Module K M]
    [Finite M] (T : M →+ M) (σ : K →+* K) (hT : ∀ (c : K) (x : M), T (c • x) = σ c • T x)
    {x₀ : M} (hx₀ : T x₀ ≠ x₀) (hKM : Nat.card K ^ 2 ≤ Nat.card M) :
    Nat.card K * Nat.card {x : M // T x = x} ≤ Nat.card M := by
  by_cases hσ : ∃ θ, σ θ ≠ θ
  · obtain ⟨θ, hθ⟩ := hσ
    have h1 := G2Q8.card_fix_sq_le T σ hθ hT
    have h2 : (Nat.card K * Nat.card {x : M // T x = x}) ^ 2 ≤ Nat.card M ^ 2 := by
      rw [mul_pow, sq (Nat.card M)]
      exact Nat.mul_le_mul hKM h1
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h2
  · simp only [not_exists, ne_eq, not_not] at hσ
    let ψ : {x : M // T x = x} × K → M := fun p => p.1.1 + p.2 • x₀
    have hψ : Function.Injective ψ := by
      rintro ⟨⟨y, hy⟩, c⟩ ⟨⟨y', hy'⟩, c'⟩ h
      simp only [ψ] at h
      have hcc : c = c' := by
        by_contra hne
        have e1 : (c - c') • x₀ = y' - y := by
          rw [sub_smul, sub_eq_sub_iff_add_eq_add, add_comm, ← h, add_comm]
        have e2 : T ((c - c') • x₀) = (c - c') • T x₀ := by rw [hT, hσ]
        rw [e1, map_sub, hy, hy'] at e2
        have e3 : (c - c') • T x₀ = (c - c') • x₀ := by rw [← e2, e1]
        have hc : (c - c') ≠ 0 := sub_ne_zero.mpr hne
        exact hx₀ (smul_right_injective M hc e3)
      subst hcc
      have hyy : y = y' := add_right_cancel h
      subst hyy
      rfl
    have h1 := Nat.card_le_card_of_injective ψ hψ
    rwa [Nat.card_prod, mul_comm] at h1

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ} {K : Type} [Field K]

section Conj

variable [IsMulCommutative ↥V]

theorem exists_semilinear_conjV {D : FFModel} {M : Type} [AddCommGroup M] [Module K M]
    {LM : KGNat.LinModel D K M} {π : D.Gam →* ↥(autOn L V)} {f : ↥V → M}
    (hf : KGNat.IsCoord LM (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    {x₀ : M} (hx₀ : x₀ ≠ 0) {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) :
    ∃ (T : M →+ M) (σ : K →+* K), (∀ (c : K) (y : M), T (c • y) = σ c • T y) ∧
      ∀ w, f (SecA.conjV V x hxV w) = T (f w) := by
  have hxL' : x⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hxL
  have hxV' : x⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hxV
  have hinv : (SecA.conjV V x hxV)⁻¹ = SecA.conjV V x⁻¹ hxV' := (SecA.conjV_inv V hxV).symm
  have hτZ : ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V,
      SecA.conjV V x hxV z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V :=
    fun z hz => G2Q8.conjV_mem_centralizer hxL hxV hz
  have hτZ' : ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V,
      (SecA.conjV V x hxV)⁻¹ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V := by
    intro z hz
    rw [hinv]
    exact G2Q8.conjV_mem_centralizer hxL' hxV' hz
  have hτH' : ∀ h ∈ autOn L V, (SecA.conjV V x hxV)⁻¹ * h * SecA.conjV V x hxV ∈ autOn L V := by
    intro h hh
    have := G2Q8.conjV_mul_conjV_inv_mem hxL' hxV' hh
    rwa [← hinv, inv_inv] at this
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear hcomm hx₀ _ hτZ hτZ' hτH'
  exact ⟨hf.autMap _ hτZ, σ, hσ, fun w => (hf.autMap_apply _ hτZ w).symm⟩

omit [Field K] in
theorem card_fun_three [Finite K] (hK : Nat.card K = 2 ^ n) :
    Nat.card (Fin 3 → K) = 2 ^ (3 * n) := by
  rw [Nat.card_fun, Nat.card_fin, hK, ← pow_mul, mul_comm]

omit [Field K] in
theorem card_fun_four [Finite K] (hK : Nat.card K = 2 ^ n) :
    Nat.card (Fin 2 ⊕ Fin 2 → K) = 2 ^ (4 * n) := by
  rw [Nat.card_fun, Nat.card_sum, Nat.card_fin, hK, ← pow_mul, mul_comm]

omit [Field K] in
theorem card_fun_six [Finite K] (hK : Nat.card K = 2 ^ n) :
    Nat.card (Ix3 → K) = 2 ^ (6 * n) := by
  rw [Nat.card_fun, Nat.card_sum, Nat.card_fin, hK, ← pow_mul, mul_comm]

theorem le_rkIdx_sl3 [Finite G] [Finite K] (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V) (hK : Nat.card K = 2 ^ n)
    {π : ↥(StatedSL 3 K) →* ↥(autOn L V)} {f : ↥V → (Fin 3 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSL 3 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx : x ∉ Subgroup.centralizer (V : Set G)) :
    n ≤ rkIdx (fixV (Subgroup.zpowers (SecA.conjV V x hxV))) := by
  obtain ⟨T, σ, hσ, hT⟩ := exists_semilinear_conjV hf
    (fun T hT => KGNat.commutant_statedSL (by norm_num) T hT) (x₀ := ![1, 0, 0])
    (fun h => one_ne_zero (congrFun h 0)) hxV hxL
  obtain ⟨y, hy⟩ : ∃ y, T y ≠ y := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hx (mem_centralizer_of_sl3 hLV hVL hf hxV hxL fun v => by rw [hT, h])
  have hM := card_fun_three hK
  have h1 := card_mul_card_fix_le T σ hσ hy (by
    rw [hM, hK, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : Nat.card {z : Fin 3 → K // T z = z} ≤ 2 ^ (2 * n) := by
    rw [hM, hK, show 3 * n = n + 2 * n by ring, pow_add] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  have h3 := le_rkIdx_add hV hf (C := fixV (Subgroup.zpowers (SecA.conjV V x hxV)))
    (fun w hw => by rw [← hT, mem_fixV_zpowers.mp hw]) hM h2
  omega

theorem le_rkIdx_sp4 [Finite G] [Finite K] (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V) (hK : Nat.card K = 2 ^ n)
    {π : ↥(StatedSp 2 K) →* ↥(autOn L V)} {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSp 2 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx : x ∉ Subgroup.centralizer (V : Set G)) :
    n ≤ rkIdx (fixV (Subgroup.zpowers (SecA.conjV V x hxV))) := by
  obtain ⟨T, σ, hσ, hT⟩ := exists_semilinear_conjV hf
    (fun T hT => KGNat.commutant_statedSp T hT) (x₀ := KGNat.vec4 (1 : K) 0 0 0)
    (fun h => one_ne_zero (congrFun h (.inl 0))) hxV hxL
  obtain ⟨y, hy⟩ : ∃ y, T y ≠ y := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hx (mem_centralizer_of_sp4 hLV hVL hf hxV hxL fun v => by rw [hT, h])
  have hM := card_fun_four hK
  have h1 := card_mul_card_fix_le T σ hσ hy (by
    rw [hM, hK, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : Nat.card {z : Fin 2 ⊕ Fin 2 → K // T z = z} ≤ 2 ^ (3 * n) := by
    rw [hM, hK, show 4 * n = n + 3 * n by ring, pow_add] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  have h3 := le_rkIdx_add hV hf (C := fixV (Subgroup.zpowers (SecA.conjV V x hxV)))
    (fun w hw => by rw [← hT, mem_fixV_zpowers.mp hw]) hM h2
  omega

theorem le_rkIdx_g2 [Finite G] [Finite K] [CharP K 2] (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V) (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)}
    {f : ↥V → (Ix3 → K)} (hf : KGNat.IsCoord (G2Q8.lmG K) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx : x ∉ Subgroup.centralizer (V : Set G))
    (hx2 : SecA.conjV V x hxV * SecA.conjV V x hxV = 1) :
    2 * n ≤ rkIdx (fixV (Subgroup.zpowers (SecA.conjV V x hxV))) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨c, γ, σ, hc, hact⟩ := G2Q8.exists_smul_frob_conjV
    (X := Subgroup.normalizer (L : Set G)) hf hc0 hc1 hK hn inf_le_left (e := x) ⟨hxL, hxV⟩
  let T : (Ix3 → K) →+ (Ix3 → K) :=
    { toFun := fun y => c • g2Act γ (G2Q8.frobQ (σ : K →+* K) y)
      map_zero' := by
        have : G2Q8.frobQ (σ : K →+* K) 0 = 0 := funext fun j => map_zero σ
        rw [this, map_zero, smul_zero]
      map_add' := fun y y' => by
        have : G2Q8.frobQ (σ : K →+* K) (y + y') =
            G2Q8.frobQ (σ : K →+* K) y + G2Q8.frobQ (σ : K →+* K) y' :=
          funext fun j => map_add σ (y j) (y' j)
        simp only [this, map_add, smul_add] }
  have hT : ∀ w, f (SecA.conjV V x hxV w) = T (f w) := hact
  have hsemi : ∀ (a : K) (y : Ix3 → K), T (a • y) = (σ : K →+* K) a • T y := by
    intro a y
    show c • g2Act γ (G2Q8.frobQ (σ : K →+* K) (a • y)) =
      (σ : K →+* K) a • (c • g2Act γ (G2Q8.frobQ (σ : K →+* K) y))
    rw [G2Q8.frobQ_smul, G2Q8.g2Act_smul, smul_comm]
  have hM := card_fun_six hK
  have hbound : Nat.card {z : Ix3 → K // T z = z} ≤ 2 ^ (4 * n) := by
    by_cases hσ : ∃ θ, σ θ ≠ θ
    · obtain ⟨θ, hθ⟩ := hσ
      have h1 := G2Q8.card_fix_sq_le T (σ : K →+* K) hθ hsemi
      rw [hM, show 6 * n = 3 * n * 2 by ring, pow_mul] at h1
      have h3 := (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
      exact h3.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    · simp only [not_exists, ne_eq, not_not] at hσ
      have hT' : ∀ y, T y = c • g2Act γ y := fun y => by
        show c • g2Act γ (G2Q8.frobQ (σ : K →+* K) y) = _
        congr 2
        exact funext fun j => hσ (y j)
      have hsq : ∀ y, c • g2Act γ (c • g2Act γ y) = y := by
        intro y
        obtain ⟨w, rfl⟩ := hf.surj y
        have h1 := congrArg (fun φ : MulAut ↥V => f (φ w)) hx2
        simp only [MulAut.mul_apply, MulAut.one_apply] at h1
        rwa [hT, hT, hT', hT'] at h1
      have hγγ : ∀ y, g2Act (γ * γ) y = (c * c)⁻¹ • y := by
        intro y
        have h1 := hsq y
        rw [G2Q8.g2Act_smul, smul_smul, ← G2Q8.g2Act_mul_apply] at h1
        calc g2Act (γ * γ) y = (c * c)⁻¹ • ((c * c) • g2Act (γ * γ) y) := by
              rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hc), one_smul]
          _ = (c * c)⁻¹ • y := by rw [h1]
      have hcc : (c * c)⁻¹ = 1 := G2Q8.scalar_eq_one hγγ
      have hc1' : c = 1 := by
        have hcc' : c * c = 1 := by
          have := congrArg (·⁻¹) hcc
          simpa using this
        have h4 : (c + 1) * (c + 1) = 0 := by linear_combination hcc' + (1 + c) * h2
        have h5 := mul_self_eq_zero.mp h4
        linear_combination h5 - h2
      have hγ2 : γ * γ = 1 := G2Q8.cayley_eq_one fun y => by rw [hγγ, hcc, one_smul]
      have hγ1 : γ ≠ 1 := by
        rintro rfl
        refine hx (mem_centralizer_of_g2 hLV hVL hf hc0 hc1 hxV hxL fun v => ?_)
        rw [hT, hT', hc1', one_smul, map_one]
        rfl
      have h1 := B42G2.card_fixQ_le hγ2 hγ1
      rw [hK, ← pow_mul, mul_comm] at h1
      refine le_trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_))) h1
      rw [G2Q8.mem_fixQ, hT', hc1', one_smul]
  have h3 := le_rkIdx_add hV hf (C := fixV (Subgroup.zpowers (SecA.conjV V x hxV)))
    (fun w hw => by rw [← hT, mem_fixV_zpowers.mp hw]) hM hbound
  omega

end Conj

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
