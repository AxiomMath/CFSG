module

public import CFSG.Quasithin.Vol2.Ch11SecBK4C
public import CFSG.Quasithin.Vol2.Ch11SecBK7D
public import CFSG.Quasithin.Vol2.Ch11G2Q8Weyl
public import CFSG.Quasithin.Vol2.Ch11G2Q8Siegel

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix
open CFSG.Open (quasithinG2 IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL coe_uSL uSL_mul uSL_zero)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.Quasithin.Vol2.KGNat (spJ)
open scoped IsMulCommutative

namespace BK4

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def dg3 {a : K} (ha : a ≠ 0) : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal ![a, a⁻¹ * a⁻¹, a], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp⟩

theorem coe_dg3 {a : K} (ha : a ≠ 0) :
    ((dg3 ha : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![a, a⁻¹ * a⁻¹, a] := rfl

theorem dg3_mulVec {a : K} (ha : a ≠ 0) (x : Fin 3 → K) :
    ((dg3 ha : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      ![a * x 0, a⁻¹ * a⁻¹ * x 1, a * x 2] := by
  rw [coe_dg3]
  funext i
  fin_cases i <;> simp [Matrix.mulVec_diagonal]

theorem uSL_mulVec (x : Fin 3 → K) :
    ((uSL 0 1 0 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      ![x 0 + x 2, x 1, x 2] := by
  funext i
  fin_cases i <;>
    simp [coe_uSL, CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

theorem dg3_comm {a : K} (ha : a ≠ 0) : uSL 0 1 0 * dg3 ha = dg3 ha * uSL 0 1 0 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_dg3]
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat, Matrix.mul_apply, Matrix.diagonal]

variable [IsMulCommutative ↥V]

theorem exists_rkIdx_le_sl3 [Finite G] [Finite K] [CharP K 2] (hV : IsElemAbelian 2 V)
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {π : ↥(StatedSL 3 K) →* ↥(autOn L V)}
    {f : ↥V → (Fin 3 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSL 3 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) :
    ∃ t ∈ autOn L V, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) ≤ n := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨a, ha0, ha1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
  set e := specialLinearGroupEquivStatedSL 3 K with he
  set A₀ : SpecialLinearGroup (Fin 3) K := uSL 0 1 0 with hA₀
  have hlin : ∀ (A : SpecialLinearGroup (Fin 3) K) (x : Fin 3 → K),
      (KGNat.linModelNat (StatedSL 3 K)).lin (e A) x = (A : Matrix (Fin 3) (Fin 3) K) *ᵥ x :=
    fun A x => KGNat.linModelNat_lin _ _ _
  set t : MulAut ↥V := ((π (e A₀) : ↥(autOn L V)) : MulAut ↥V) with ht
  have hZ : ∀ h ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, h z = z :=
    fun h hh z hz => SecA.autOn_fixes_cV h hh z hz
  have hfix : ∀ w : ↥V, (A₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ f w = f w → t w = w := by
    intro w hw
    refine fix_of_comm hf hZ (S := {e (dg3 ha0)}) (fun δ hδ => ?_) (fun x hx => ?_)
      (by rw [hlin]; exact hw)
    · have hδ' : δ = e (dg3 ha0) := hδ
      subst hδ'
      show e A₀ * e (dg3 ha0) = e (dg3 ha0) * e A₀
      rw [← map_mul, ← map_mul, hA₀, dg3_comm]
    · rw [hlin, uSL_mulVec] at hx
      have hx2 : x 2 = 0 := by
        have := congrFun hx 0
        simp only [Matrix.cons_val_zero] at this
        exact add_eq_left.mp this
      have hb1 : a⁻¹ * a⁻¹ - 1 ≠ 0 := by
        intro h
        have haa : a * a = 1 :=
          calc a * a = a * a * (a⁻¹ * a⁻¹) := by rw [sub_eq_zero.mp h, mul_one]
            _ = (a * a⁻¹) * (a * a⁻¹) := by ring
            _ = 1 := by rw [mul_inv_cancel₀ ha0, one_mul]
        have h3 : (a - 1) * (a - 1) = 0 := by linear_combination haa + (1 - a) * h2
        exact ha1 (sub_eq_zero.mp (mul_self_eq_zero.mp h3))
      have ha1' : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
      refine AddSubgroup.subset_closure ⟨e (dg3 ha0), rfl,
        ![x 0 / (a - 1), x 1 / (a⁻¹ * a⁻¹ - 1), 0], ?_, ?_⟩
      · rw [hlin, uSL_mulVec]
        funext i
        fin_cases i <;> simp
      · have key : ∀ b y : K, b - 1 ≠ 0 → b * (y / (b - 1)) - y / (b - 1) = y := by
          intro b y hb
          field_simp
        rw [hlin, dg3_mulVec]
        funext i
        fin_cases i
        · show x 0 = a * (x 0 / (a - 1)) - x 0 / (a - 1)
          exact (key a (x 0) ha1').symm
        · show x 1 = a⁻¹ * a⁻¹ * (x 1 / (a⁻¹ * a⁻¹ - 1)) - x 1 / (a⁻¹ * a⁻¹ - 1)
          exact (key _ (x 1) hb1).symm
        · show x 2 = a * 0 - 0
          rw [hx2, mul_zero, sub_zero]
  have hA2 : A₀ * A₀ = 1 := by
    rw [hA₀, uSL_mul]
    simp only [CharTwo.add_self_eq_zero, mul_zero, uSL_zero]
  have hA1 : A₀ ≠ 1 := by
    intro h
    have h1 := congrArg (fun B : SpecialLinearGroup (Fin 3) K =>
      (B : Matrix (Fin 3) (Fin 3) K) 0 2) h
    simp [hA₀, coe_uSL, CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat] at h1
  have ht1 : t ≠ 1 := by
    intro h
    apply hA1
    apply e.injective
    apply hf.injective_nat
    apply Subtype.ext
    rw [map_one, map_one]
    exact h
  have ht2 : t ^ 2 = 1 := by
    rw [sq, ht, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hA2, map_one, map_one]
    rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨t, (π (e A₀)).2, orderOf_eq_prime ht2 ht1, ?_⟩
  set T : (Fin 3 → K) →+ (Fin 3 → K) :=
    ((KGNat.linModelNat (StatedSL 3 K)).lin (e A₀)).toAddMonoidHom with hT
  have hTx : ∀ x, T x = (A₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ x := fun x => hlin A₀ x
  have hC : preFix hf T ≤ fixV (Subgroup.zpowers t) := fun w hw =>
    mem_fixV_zpowers.mpr (hfix w (by rw [← hTx]; exact hw))
  have hcard : 2 ^ (2 * n) ≤ Nat.card {x : Fin 3 → K // T x = x} := by
    let ψ : K × K → {x : Fin 3 → K // T x = x} := fun p => ⟨![p.1, p.2, 0], by
      rw [hTx, uSL_mulVec]
      funext i
      fin_cases i <;> simp⟩
    have hψ : Function.Injective ψ := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
      have h1 := congrArg (fun y : {x : Fin 3 → K // T x = x} => y.1 0) h
      have h2 := congrArg (fun y : {x : Fin 3 → K // T x = x} => y.1 1) h
      simp only [ψ, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
      rw [h1, h2]
    have h1 := Nat.card_le_card_of_injective ψ hψ
    rwa [Nat.card_prod, hK, ← pow_add, show n + n = 2 * n by ring] at h1
  have h3 := rkIdx_add_le hV hf hC (card_fun_three hK) hcard
  omega

theorem exists_rkIdx_le_sp4 [Finite G] [Finite K] [CharP K 2] (hV : IsElemAbelian 2 V)
    (hK : Nat.card K = 2 ^ n) {π : ↥(StatedSp 2 K) →* ↥(autOn L V)}
    {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSp 2 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) :
    ∃ t ∈ autOn L V, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) ≤ n := by
  set e₀ : Fin 2 ⊕ Fin 2 → K := KGNat.vec4 1 0 0 0 with he₀
  have hB : ∀ x : Fin 2 ⊕ Fin 2 → K, Matrix.toBilin' (spJ K) x e₀ = x (.inr 0) := fun x => by
    rw [K7.bil_comm, he₀, KGNat.spB_e0]
  set γ₀ : ↥(StatedSp 2 K) := K7.trv e₀ 1 with hγ₀
  set t : MulAut ↥V := ((π γ₀ : ↥(autOn L V)) : MulAut ↥V) with ht
  have hZ : ∀ h ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, h z = z :=
    fun h hh z hz => SecA.autOn_fixes_cV h hh z hz
  set T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K) :=
    ((KGNat.linModelNat (StatedSp 2 K)).lin γ₀).toAddMonoidHom with hT
  have hTx : ∀ x, T x = x + Matrix.toBilin' (spJ K) x e₀ • e₀ := fun x => by
    rw [← one_mul (Matrix.toBilin' (spJ K) x e₀), ← K7.trv_mulVec]
    rfl
  have hγ2 : γ₀ * γ₀ = 1 := by rw [hγ₀, K7.trv_mul, CharTwo.add_self_eq_zero, K7.trv_zero]
  have hγ1 : γ₀ ≠ 1 := by
    intro h
    have h1 := hTx (KGNat.vec4 0 0 1 0)
    have h2 : T (KGNat.vec4 0 0 1 0) = KGNat.vec4 0 0 1 0 := by
      show (KGNat.linModelNat (StatedSp 2 K)).lin γ₀ _ = _
      rw [KGNat.linModelNat_lin, h]
      simp
    rw [h2, hB] at h1
    have h3 := congrFun h1 (.inl 0)
    simp [KGNat.vec4, he₀] at h3
  have ht1 : t ≠ 1 := by
    intro h
    apply hγ1
    apply hf.injective_nat
    apply Subtype.ext
    rw [map_one]
    exact h
  have ht2 : t ^ 2 = 1 := by
    rw [sq, ht, ← Subgroup.coe_mul, ← map_mul, hγ2, map_one]
    rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨t, (π γ₀).2, orderOf_eq_prime ht2 ht1, ?_⟩
  have hC : preFix hf T ≤ fixV (Subgroup.zpowers t) := by
    intro w hw
    have hw' : T (f w) = f w := hw
    rw [hTx, add_eq_left, smul_eq_zero] at hw'
    have hw0 : f w (.inr 0) = 0 := by
      rcases hw' with hw' | hw'
      · rwa [hB] at hw'
      · exact absurd (congrFun hw' (.inl 0)) (by simp [he₀, KGNat.vec4])
    exact mem_fixV_zpowers.mpr (K7.trv_e0_fix hf hZ 1 hw0)
  have hcard : 2 ^ (3 * n) ≤ Nat.card {x : Fin 2 ⊕ Fin 2 → K // T x = x} := by
    let ψ : K × K × K → {x : Fin 2 ⊕ Fin 2 → K // T x = x} := fun p =>
      ⟨KGNat.vec4 p.1 p.2.1 0 p.2.2, by
        rw [hTx, hB]
        simp [KGNat.vec4]⟩
    have hψ : Function.Injective ψ := by
      rintro ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ h
      have h1 := congrArg (fun y : {x : Fin 2 ⊕ Fin 2 → K // T x = x} => y.1 (.inl 0)) h
      have h2 := congrArg (fun y : {x : Fin 2 ⊕ Fin 2 → K // T x = x} => y.1 (.inl 1)) h
      have h3 := congrArg (fun y : {x : Fin 2 ⊕ Fin 2 → K // T x = x} => y.1 (.inr 1)) h
      simp only [ψ, KGNat.vec4] at h1 h2 h3
      simp at h1 h2 h3
      rw [h1, h2, h3]
    have h1 := Nat.card_le_card_of_injective ψ hψ
    rwa [Nat.card_prod, Nat.card_prod, hK, ← pow_add, ← pow_add,
      show n + (n + n) = 3 * n by ring] at h1
  have h3 := rkIdx_add_le hV hf hC (card_fun_four hK) hcard
  omega

theorem exists_rkIdx_le_g2 [Finite G] [Finite K] [CharP K 2] (hV : IsElemAbelian 2 V)
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)} {f : ↥V → (Ix3 → K)}
    (hf : KGNat.IsCoord (G2Q8.lmG K) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) :
    ∃ t ∈ autOn L V, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) ≤ 2 * n := by
  obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  have hZ : ∀ h ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, h z = z :=
    fun h hh z hz => SecA.autOn_fixes_cV h hh z hz
  set t : MulAut ↥V := ((G2Q8.rhoG hc0 hc1 π (G2Q8.tL 1) : ↥(autOn L V)) : MulAut ↥V) with ht
  have ht1 : t ≠ 1 := by
    intro h
    apply G2Q8.tL_one_ne_one (K := K)
    apply (G2Q8.rhoG_bijective hf hc0 hc1).1
    apply Subtype.ext
    rw [map_one]
    exact h
  have ht2 : t ^ 2 = 1 := by
    rw [sq, ht, ← Subgroup.coe_mul, ← map_mul, G2Q8.tL_mul_self, map_one]
    rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨t, (G2Q8.rhoG hc0 hc1 π (G2Q8.tL 1)).2, orderOf_eq_prime ht2 ht1, ?_⟩
  set T : (Ix3 → K) →+ (Ix3 → K) := g2Act (G2Q8.tL (1 : K)) with hT
  have hC : preFix hf T ≤ fixV (Subgroup.zpowers t) := fun w hw =>
    mem_fixV_zpowers.mpr (G2Q8.rhoG_fix hK hn hf hc0 hc1 hsq hZ hw)
  have hcard : 2 ^ (4 * n) ≤ Nat.card {x : Ix3 → K // T x = x} := by
    let ψ : K × K × K × K → {x : Ix3 → K // T x = x} := fun p =>
      ⟨q6 p.1 p.2.1 0 0 p.2.2.1 p.2.2.2, G2Q8.g2Act_tL_of_inC 1 ⟨rfl, rfl⟩⟩
    have hψ : Function.Injective ψ := by
      rintro ⟨a₁, b₁, c₁, d₁⟩ ⟨a₂, b₂, c₂, d₂⟩ h
      have h1 := congrArg (fun y : {x : Ix3 → K // T x = x} => y.1 (.inl 0)) h
      have h2 := congrArg (fun y : {x : Ix3 → K // T x = x} => y.1 (.inl 1)) h
      have h3 := congrArg (fun y : {x : Ix3 → K // T x = x} => y.1 (.inr 1)) h
      have h4 := congrArg (fun y : {x : Ix3 → K // T x = x} => y.1 (.inr 2)) h
      simp only [ψ, G2Q8.q6_apply_inl0, G2Q8.q6_apply_inl1, G2Q8.q6_apply_inr1,
        G2Q8.q6_apply_inr2] at h1 h2 h3 h4
      rw [h1, h2, h3, h4]
    have h1 := Nat.card_le_card_of_injective ψ hψ
    rwa [Nat.card_prod, Nat.card_prod, Nat.card_prod, hK, ← pow_add, ← pow_add, ← pow_add,
      show n + (n + (n + n)) = 4 * n by ring] at h1
  have h3 := rkIdx_add_le hV hf hC (card_fun_six hK) hcard
  omega

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
