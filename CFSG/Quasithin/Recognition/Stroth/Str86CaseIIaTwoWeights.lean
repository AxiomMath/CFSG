module

public import CFSG.GroupTheory.ChiefSectionPGroup
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaEquality
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoFilt

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mul_add_one_mem {K : Type} [Field K] [Fintype K] [CharP K 2]
    (W : AddSubgroup K) {lam c : K} (hlam : lam ≠ 1) (hW : ∀ x ∈ W, lam * x ∈ W)
    (hK2 : 2 ≤ Fintype.card K) (hc : (lam + 1) * c ∈ W) : c ∈ W := by
  classical
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hone : (1 : K) + 1 = 0 := by
    rw [← two_mul]
    simpa using h2
  have ha0 : lam + 1 ≠ 0 := by
    intro h
    exact hlam (add_right_cancel (h.trans hone.symm))
  have hpow : ∀ n : ℕ, (lam + 1) ^ n * ((lam + 1) * c) ∈ W := by
    intro n
    induction n with
    | zero => simpa using hc
    | succ n ih =>
        have hstep : (lam + 1) ^ (n + 1) * ((lam + 1) * c) =
            lam * ((lam + 1) ^ n * ((lam + 1) * c)) +
              ((lam + 1) ^ n * ((lam + 1) * c)) := by
          rw [pow_succ]
          ring
        rw [hstep]
        exact W.add_mem (hW _ ih) ih
  have hcard : (lam + 1) ^ (Fintype.card K - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one (lam + 1) ha0
  have hExp : Fintype.card K - 1 = (Fintype.card K - 2) + 1 := by omega
  have hfinal : (lam + 1) ^ (Fintype.card K - 2) * ((lam + 1) * c) = c := by
    calc (lam + 1) ^ (Fintype.card K - 2) * ((lam + 1) * c)
        = ((lam + 1) ^ (Fintype.card K - 2) * (lam + 1)) * c := by ring
      _ = (lam + 1) ^ ((Fintype.card K - 2) + 1) * c := by rw [pow_succ]
      _ = (lam + 1) ^ (Fintype.card K - 1) * c := by rw [← hExp]
      _ = c := by rw [hcard, one_mul]
  rw [← hfinal]
  exact hpow (Fintype.card K - 2)

theorem inf_str86U2_eq_p {S U₂ N p P : Subgroup G}
    (hPN : P ≤ N) (hpP : p ≤ P) (hpU₂ : p ≤ U₂)
    (hU₂C : U₂ ≤ Subgroup.centralizer (S : Set G))
    (hp : p = N ⊓ Subgroup.centralizer (S : Set G)) :
    P ⊓ U₂ = p := by
  refine le_antisymm ?_ (le_inf hpP hpU₂)
  intro x hx
  obtain ⟨hxP, hxU₂⟩ := Subgroup.mem_inf.mp hx
  rw [hp]
  exact Subgroup.mem_inf.mpr ⟨hPN hxP, hU₂C hxU₂⟩

theorem str86_caseIIa_two_u1_not_le
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    {N : Subgroup G} (hNne : N ≠ ⊥) (hNZ : N ≤ Z1 L1 L2 S)
    (hNP1 : P1 L1 L2 S ≤ Subgroup.normalizer (N : Set G)) :
    ¬ N ≤ str86U1 ⁅N, S⁆ L2 S := by
  classical
  let H : Subgroup G := L2 ⊔ S
  let P : Subgroup G := ⁅N, S⁆
  let U₁ : Subgroup G := str86U1 P L2 S
  let U_N : Subgroup G := str86UN N L2 S
  let U : Subgroup G := str86U L1 L2 S
  have hm2 : 2 ≤ m := CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hm
  have hVU3 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hQ1Q2 : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    str86_pCoreOf_sup_pCoreOf hF.toW hSB (Or.inr hVU3) hm2 hm
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hQ2H : H ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    str86_l2sup_le_normalizer_q2 (L1 := L1) (L2 := L2) (S := S)
  have hU_N_ne : U_N ≠ ⊥ := by
    intro hbot
    have hNle : N ≤ U_N := le_conjClosure N H
    exact hNne (le_bot_iff.mp (hbot ▸ hNle))
  have hUQ2 : U ≤ Q2 L1 L2 S := by
    refine conjClosure_le ?_
    intro h hh z hz
    exact (Subgroup.mem_normalizer_iff.mp (hQ2H hh) z).mp (hZ hz)
  have hUNU : U_N ≤ U := str86UN_le_str86U (L1 := L1) hNZ
  have hUN_le_Q2 : U_N ≤ Q2 L1 L2 S := hUNU.trans hUQ2
  have hQ1_normS : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hQ2_normS : S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hs_decomp : ∀ s ∈ S, ∃ q1 ∈ Q1 L1 L2 S, ∃ q2 ∈ Q2 L1 L2 S, q1 * q2 = s := by
    intro s hs
    letI : ((Q1 L1 L2 S).subgroupOf S).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hQ1_normS
    have hmem : (⟨s, hs⟩ : ↥S) ∈ ((Q1 L1 L2 S).subgroupOf S) ⊔ ((Q2 L1 L2 S).subgroupOf S) := by
      have hsub : ((Q1 L1 L2 S).subgroupOf S) ⊔ ((Q2 L1 L2 S).subgroupOf S) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQ1S hQ2S, hQ1Q2, Subgroup.subgroupOf_self]
      rw [hsub]
      exact Subgroup.mem_top _
    obtain ⟨q1, hq1, q2, hq2, hq12⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := (Q1 L1 L2 S).subgroupOf S)
        (t := (Q2 L1 L2 S).subgroupOf S) (x := ⟨s, hs⟩)).mp hmem
    refine ⟨(q1 : G), Subgroup.mem_subgroupOf.mp hq1, (q2 : G),
      Subgroup.mem_subgroupOf.mp hq2, ?_⟩
    have := congrArg Subtype.val hq12
    simpa using this
  let C : Subgroup G := ⁅U_N, Q2 L1 L2 S⁆
  have hH_comm_norm : H ≤ Subgroup.normalizer (C : Set G) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_commutator
      (str86UN_normalizes (N := N) (L2 := L2) (S := S)) hQ2H
  have hP_le_comm : P ≤ C := by
    rw [Subgroup.commutator_le]
    intro n hn s hs
    obtain ⟨q1, hq1, q2, hq2, hq12⟩ := hs_decomp s hs
    have hnU : n ∈ U_N := le_conjClosure N H hn
    have hq1C : q1 ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
      Q1_le_centralizer_Z1 L1 L2 S hq1
    have hcomm1 : ⁅n, q1⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.mp hq1C n (hNZ hn)
    have hq1H : q1 ∈ H := (le_sup_right : S ≤ H) (hQ1S hq1)
    have hq2comm : ⁅n, q2⁆ ∈ C :=
      Subgroup.commutator_mem_commutator hnU hq2
    rw [← hq12, CFSG.commutator_mul_right, hcomm1, one_mul]
    exact (Subgroup.mem_normalizer_iff.mp (hH_comm_norm hq1H) _).mp hq2comm
  have hU₁_le_comm : U₁ ≤ C :=
    conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp (hH_comm_norm hh) z).mp (hP_le_comm hz)
  intro hN_le_U₁
  have hU₁_normal : H ≤ Subgroup.normalizer (U₁ : Set G) :=
    str86U1_normalizes (P := P) (L2 := L2) (S := S)
  have hUN_le_U₁ : U_N ≤ U₁ :=
    conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp (hU₁_normal hh) z).mp (hN_le_U₁ hz)
  have hUN_le_comm : U_N ≤ C := hUN_le_U₁.trans hU₁_le_comm
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hQ2p : IsPGroup 2 (Q2 L1 L2 S) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P2 L1 L2 S)
  have hQ2_le_H : Q2 L1 L2 S ≤ H := hQ2S.trans (le_sup_right : S ≤ H)
  have hQ2_norm_UN : Q2 L1 L2 S ≤ Subgroup.normalizer (U_N : Set G) :=
    hQ2_le_H.trans (str86UN_normalizes (N := N) (L2 := L2) (S := S))
  have hlt : C < U_N := by
    have h := CFSG.GroupTheory.commutator_sup_lt_of_isPGroup
      (p := 2) (X := U_N) (Q := Q2 L1 L2 S) (V := ⊥)
      hUN_le_Q2 hQ2p hQ2_norm_UN
      (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
      bot_le hU_N_ne.symm
    simpa using h
  exact (not_le_of_gt hlt) hUN_le_comm


theorem str86_two_weights_section {S N p P U₁ U₂ U : Subgroup G} {Kb : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    (hk : 2 ≤ k) (hKcard : Nat.card K = (2 ^ k) ^ 2)
    {Φ : Additive ↥N ≃+ (Fin 3 → K)} {χ₂ χ₃ : ↥Kb →* Kˣ}
    (hN : IsElemAbelian 2 N)
    (hPN : P ≤ N) (hpP : p ≤ P) (hpU₂ : p ≤ U₂) (hPleU₁ : P ≤ U₁)
    (hp : p = N ⊓ Subgroup.centralizer (S : Set G))
    (hcent : ∀ n : ↥N, ((n : G) ∈ Subgroup.centralizer (S : Set G) ↔
      Φ (Additive.ofMul n) 1 = 0 ∧ Φ (Additive.ofMul n) 2 = 0))
    (hPmem : ∀ n : ↥N, ((n : G) ∈ P ↔ Φ (Additive.ofMul n) 2 = 0))
    (hinf : P ⊓ U₂ = p)
    (hUab : IsElemAbelian 2 U) (hNU : N ≤ U) (hPU : P ≤ U)
    (hU₁U : U₁ ≤ U) (hU₂U : U₂ ≤ U)
    (hKbN : Kb ≤ Subgroup.normalizer (N : Set G))
    (hKbP : Kb ≤ Subgroup.normalizer (P : Set G))
    (hKbU₁ : Kb ≤ Subgroup.normalizer (U₁ : Set G))
    (hKbU₂ : Kb ≤ Subgroup.normalizer (U₂ : Set G))
    (hact : ∀ (d : ↥Kb) (n n' : ↥N), (n' : G) = (d : G) * n * (d : G)⁻¹ →
      Φ (Additive.ofMul n') 2 = Φ (Additive.ofMul n) 2 * (χ₃ d : K) ∧
      (Φ (Additive.ofMul n) 2 = 0 →
        Φ (Additive.ofMul n') 1 = Φ (Additive.ofMul n) 1 * (χ₂ d : K)) ∧
      (Φ (Additive.ofMul n) 1 = 0 → Φ (Additive.ofMul n) 2 = 0 →
        Φ (Additive.ofMul n') = Φ (Additive.ofMul n)))
    (hNnotU₁ : ¬ N ≤ U₁)
    (hrelP : p.relIndex P = (2 ^ k) ^ 2) :
    (∀ d : ↥Kb, ((∀ y ∈ U₂ ⊔ P, ⁅(d : G), y⁆ ∈ U₂) ↔ (χ₂ d : K) = 1)) ∧
    (∀ d : ↥Kb,
      ((∀ y ∈ U₂ ⊔ P, ⁅(d : G), y⁆ ∈ U₂ → y ∈ U₂) ↔ (χ₂ d : K) ≠ 1)) ∧
    (∀ d : ↥Kb, ((∀ y ∈ N ⊔ U₁, ⁅(d : G), y⁆ ∈ U₁) ↔ (χ₃ d : K) = 1)) ∧
    (∀ d : ↥Kb,
      ((∀ y ∈ N ⊔ U₁, ⁅(d : G), y⁆ ∈ U₁ → y ∈ U₁) ↔ (χ₃ d : K) ≠ 1)) ∧
    p.relIndex P = (2 ^ k) ^ 2 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hone : (1 : K) + 1 = 0 := by
    rw [← two_mul]
    simpa using h2K
  have htwo : ∀ x : K, x + x = 0 := by
    intro x
    rw [← two_mul, h2K, zero_mul]
  have hchi2_add_one_iff : ∀ d : ↥Kb, (χ₂ d : K) + 1 = 0 ↔ (χ₂ d : K) = 1 := by
    intro d
    constructor
    · intro h
      exact add_right_cancel (h.trans hone.symm)
    · intro h
      rw [h, hone]
  have hchi3_add_one_iff : ∀ d : ↥Kb, (χ₃ d : K) + 1 = 0 ↔ (χ₃ d : K) = 1 := by
    intro d
    constructor
    · intro h
      exact add_right_cancel (h.trans hone.symm)
    · intro h
      rw [h, hone]
  have hK2 : 2 ≤ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, hKcard]
    have hk4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    nlinarith
  have phi_mul : ∀ a b : ↥N,
      Φ (Additive.ofMul (a * b)) = Φ (Additive.ofMul a) + Φ (Additive.ofMul b) := by
    intro a b
    change Φ (Additive.ofMul a + Additive.ofMul b) =
      Φ (Additive.ofMul a) + Φ (Additive.ofMul b)
    exact map_add Φ _ _
  have phi_apply_mul : ∀ (a b : ↥N) (i : Fin 3),
      (Φ (Additive.ofMul (a * b))) i =
        (Φ (Additive.ofMul a)) i + (Φ (Additive.ofMul b)) i := by
    intro a b i
    rw [phi_mul]
    rfl
  have hinvN : ∀ n : ↥N, n⁻¹ = n := by
    intro n
    have h2 : n * n = 1 := by
      refine Subtype.ext ?_
      simpa [pow_two] using hN.2 (n : G) n.2
    exact inv_eq_of_mul_eq_one_right h2
  have hUcomm : ∀ {a b : G}, a ∈ U → b ∈ U → a * b = b * a := by
    intro a b ha hb
    exact congrArg Subtype.val (hUab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcomm_mem_normalizer : ∀ (A : Subgroup G) {d x : G},
      d ∈ Subgroup.normalizer (A : Set G) → x ∈ A → ⁅d, x⁆ ∈ A := by
    intro A d x hd hx
    rw [commutatorElement_def]
    exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp hd x).mp hx) (A.inv_mem hx)
  let conjN : ↥Kb → ↥N → ↥N := fun d n =>
    ⟨(d : G) * (n : G) * (d : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hKbN d.2) (n : G)).mp n.2⟩
  have hP_comm_mem_p : ∀ (d : ↥Kb) (x : G) (hxP : x ∈ P),
      (⁅(d : G), x⁆ ∈ p) ↔
        (Φ (Additive.ofMul ⟨x, hPN hxP⟩) 1 = 0 ∨ (χ₂ d : K) = 1) := by
    intro d x hxP
    let xn : ↥N := ⟨x, hPN hxP⟩
    have hx2 : Φ (Additive.ofMul xn) 2 = 0 := (hPmem xn).mp hxP
    let dxn : ↥N := conjN d xn
    have hdxP : (dxn : G) ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hKbP d.2) x).mp hxP
    have hdx2 : Φ (Additive.ofMul dxn) 2 = 0 := (hPmem dxn).mp hdxP
    have hdx1 : Φ (Additive.ofMul dxn) 1 =
        Φ (Additive.ofMul xn) 1 * (χ₂ d : K) :=
      (hact d xn dxn rfl).2.1 hx2
    let cn : ↥N := dxn * xn
    have hcomm_eq : ⁅(d : G), x⁆ = (cn : G) := by
      have hxinv : x⁻¹ = x := congrArg Subtype.val (hinvN xn)
      rw [commutatorElement_def, hxinv]
      simp [cn, dxn, xn, conjN]
    have hcn2 : Φ (Additive.ofMul cn) 2 = 0 := by
      change Φ (Additive.ofMul (dxn * xn)) 2 = 0
      rw [phi_apply_mul, hdx2, hx2, add_zero]
    have hcn1 : Φ (Additive.ofMul cn) 1 =
        Φ (Additive.ofMul xn) 1 * (χ₂ d : K) +
          Φ (Additive.ofMul xn) 1 := by
      change Φ (Additive.ofMul (dxn * xn)) 1 = _
      rw [phi_apply_mul, hdx1]
    have hfac : Φ (Additive.ofMul cn) 1 =
        Φ (Additive.ofMul xn) 1 * ((χ₂ d : K) + 1) := by
      rw [hcn1, mul_add, mul_one]
    have hmem : (cn : G) ∈ p ↔
        Φ (Additive.ofMul xn) 1 * ((χ₂ d : K) + 1) = 0 := by
      rw [hp]
      constructor
      · intro h
        obtain ⟨-, hc⟩ := Subgroup.mem_inf.mp h
        have h1 := (hcent cn).mp hc |>.1
        rwa [hfac] at h1
      · intro h1
        refine Subgroup.mem_inf.mpr ⟨cn.2, (hcent cn).mpr ⟨?_, hcn2⟩⟩
        rw [hfac]
        exact h1
    rw [hcomm_eq, hmem]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ((hchi2_add_one_iff d).mp h1)
    · rintro (h1 | h1)
      · rw [h1, zero_mul]
      · rw [(hchi2_add_one_iff d).mpr h1, mul_zero]
  have hP_comm_mem_U₂ : ∀ (d : ↥Kb) (x : G) (hxP : x ∈ P),
      (⁅(d : G), x⁆ ∈ U₂) ↔
        (Φ (Additive.ofMul ⟨x, hPN hxP⟩) 1 = 0 ∨ (χ₂ d : K) = 1) := by
    intro d x hxP
    have hcommP : ⁅(d : G), x⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKbP d.2) x).mp hxP)
        (P.inv_mem hxP)
    have hiff : (⁅(d : G), x⁆ ∈ U₂) ↔ (⁅(d : G), x⁆ ∈ p) := by
      rw [← hinf]
      exact ⟨fun h => ⟨hcommP, h⟩, fun h => h.2⟩
    rw [hiff]
    exact hP_comm_mem_p d x hxP
  have hY₂_decomp : ∀ y ∈ U₂ ⊔ P, ∃ u ∈ U₂, ∃ x ∈ P, u * x = y := by
    intro y hy
    exact CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun u hu x hx => hUcomm (hU₂U hu) (hPU hx)) hy
  have hY₁_decomp : ∀ y ∈ N ⊔ U₁, ∃ n ∈ N, ∃ u ∈ U₁, n * u = y := by
    intro y hy
    exact CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun n hn u hu => hUcomm (hNU hn) (hU₁U hu)) hy
  have hp_lt_P : p < P := by
    refine lt_of_le_of_ne hpP ?_
    intro hEq
    have hrel : p.relIndex P = 1 := by rw [hEq, Subgroup.relIndex_self]
    rw [hrel] at hrelP
    have hq2 : (2 ^ k) ^ 2 ≠ 1 := by
      have hk4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      nlinarith
    exact hq2 hrelP.symm
  obtain ⟨-, x₀, hx₀P, hx₀p⟩ := SetLike.lt_iff_le_and_exists.mp hp_lt_P
  have hx₀1 : Φ (Additive.ofMul ⟨x₀, hPN hx₀P⟩) 1 ≠ 0 := by
    intro h1
    apply hx₀p
    rw [hp]
    exact Subgroup.mem_inf.mpr ⟨hPN hx₀P,
      (hcent ⟨x₀, hPN hx₀P⟩).mpr ⟨h1, (hPmem ⟨x₀, hPN hx₀P⟩).mp hx₀P⟩⟩
  have hχ2triv : ∀ d : ↥Kb,
      ((∀ y ∈ U₂ ⊔ P, ⁅(d : G), y⁆ ∈ U₂) ↔ (χ₂ d : K) = 1) := by
    intro d
    constructor
    · intro hall
      have hxU₂ : ⁅(d : G), x₀⁆ ∈ U₂ := hall x₀ (Subgroup.mem_sup_right hx₀P)
      rcases (hP_comm_mem_U₂ d x₀ hx₀P).mp hxU₂ with h1 | hchi
      · exact absurd h1 hx₀1
      · exact hchi
    · intro hchi y hy
      obtain ⟨u, hu, x, hx, hux⟩ := hY₂_decomp y hy
      have hdxP : ⁅(d : G), x⁆ ∈ P := by
        rw [commutatorElement_def]
        exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKbP d.2) x).mp hx)
          (P.inv_mem hx)
      have hux_comm : u * ⁅(d : G), x⁆ = ⁅(d : G), x⁆ * u :=
        hUcomm (hU₂U hu) (hPU hdxP)
      have hcomm_ux : u * ⁅(d : G), x⁆ * u⁻¹ = ⁅(d : G), x⁆ := by
        rw [hux_comm]
        group
      have hy_eq : ⁅(d : G), y⁆ = ⁅(d : G), u⁆ * ⁅(d : G), x⁆ := by
        rw [← hux, CFSG.commutator_mul_right]
        calc ⁅(d : G), u⁆ * u * ⁅(d : G), x⁆ * u⁻¹ =
            ⁅(d : G), u⁆ * (u * ⁅(d : G), x⁆ * u⁻¹) := by group
          _ = ⁅(d : G), u⁆ * ⁅(d : G), x⁆ := by rw [hcomm_ux]
      rw [hy_eq]
      exact U₂.mul_mem (hcomm_mem_normalizer U₂ (hKbU₂ d.2) hu)
        ((hP_comm_mem_U₂ d x hx).mpr (Or.inr hchi))
  have hχ2fpf : ∀ d : ↥Kb,
      ((∀ y ∈ U₂ ⊔ P, ⁅(d : G), y⁆ ∈ U₂ → y ∈ U₂) ↔ (χ₂ d : K) ≠ 1) := by
    intro d
    constructor
    · intro hall hchi
      have hxU₂ : ⁅(d : G), x₀⁆ ∈ U₂ :=
        (hχ2triv d).mpr hchi x₀ (Subgroup.mem_sup_right hx₀P)
      have hx₀U₂ : x₀ ∈ U₂ := hall x₀ (Subgroup.mem_sup_right hx₀P) hxU₂
      exact hx₀p (by rw [← hinf]; exact ⟨hx₀P, hx₀U₂⟩)
    · intro hchi y hy hcomm
      obtain ⟨u, hu, x, hx, hux⟩ := hY₂_decomp y hy
      have hdxP : ⁅(d : G), x⁆ ∈ P := by
        rw [commutatorElement_def]
        exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKbP d.2) x).mp hx)
          (P.inv_mem hx)
      have hux_comm : u * ⁅(d : G), x⁆ = ⁅(d : G), x⁆ * u :=
        hUcomm (hU₂U hu) (hPU hdxP)
      have hcomm_ux : u * ⁅(d : G), x⁆ * u⁻¹ = ⁅(d : G), x⁆ := by
        rw [hux_comm]
        group
      have hy_eq : ⁅(d : G), y⁆ = ⁅(d : G), u⁆ * ⁅(d : G), x⁆ := by
        rw [← hux, CFSG.commutator_mul_right]
        calc ⁅(d : G), u⁆ * u * ⁅(d : G), x⁆ * u⁻¹ =
            ⁅(d : G), u⁆ * (u * ⁅(d : G), x⁆ * u⁻¹) := by group
          _ = ⁅(d : G), u⁆ * ⁅(d : G), x⁆ := by rw [hcomm_ux]
      have hd_u : ⁅(d : G), u⁆ ∈ U₂ := hcomm_mem_normalizer U₂ (hKbU₂ d.2) hu
      have hcomm_yx : (⁅(d : G), y⁆ ∈ U₂) ↔ (⁅(d : G), x⁆ ∈ U₂) := by
        rw [hy_eq]
        constructor
        · intro h
          have hsplit : ⁅(d : G), x⁆ =
              ⁅(d : G), u⁆⁻¹ * (⁅(d : G), u⁆ * ⁅(d : G), x⁆) := by
            group
          rw [hsplit]
          exact U₂.mul_mem (U₂.inv_mem hd_u) h
        · intro h
          exact U₂.mul_mem hd_u h
      rcases (hP_comm_mem_U₂ d x hx).mp (hcomm_yx.mp hcomm) with h1 | hchi'
      · have hxmem : x ∈ p := by
          rw [hp]
          exact Subgroup.mem_inf.mpr ⟨hPN hx,
            (hcent ⟨x, hPN hx⟩).mpr ⟨h1, (hPmem ⟨x, hPN hx⟩).mp hx⟩⟩
        rw [← hux]
        exact U₂.mul_mem hu (hpU₂ hxmem)
      · exact absurd hchi' hchi
  let W : Subgroup G := N ⊓ U₁
  let W₀ : AddSubgroup K :=
    { carrier := {c : K | ∃ n : ↥N, (n : G) ∈ W ∧ Φ (Additive.ofMul n) 2 = c}
      zero_mem' := by
        refine ⟨1, W.one_mem, ?_⟩
        simp
      add_mem' := by
        intro c d hc hd
        obtain ⟨n, hn, rfl⟩ := hc
        obtain ⟨m, hm, rfl⟩ := hd
        refine ⟨n * m, W.mul_mem hn hm, ?_⟩
        rw [phi_apply_mul]
      neg_mem' := by
        intro c hc
        obtain ⟨n, hn, rfl⟩ := hc
        refine ⟨n, hn, ?_⟩
        rw [show -(Φ (Additive.ofMul n) 2) = Φ (Additive.ofMul n) 2 from by
          rw [neg_eq_iff_add_eq_zero, htwo]] }
  have hW₀_mem : ∀ c : K, c ∈ W₀ ↔
      ∃ n : ↥N, (n : G) ∈ W ∧ Φ (Additive.ofMul n) 2 = c := fun _ => Iff.rfl
  have hW_mem_iff : ∀ n : ↥N, ((n : G) ∈ W ↔ Φ (Additive.ofMul n) 2 ∈ W₀) := by
    intro n
    constructor
    · intro hn
      exact ⟨n, hn, rfl⟩
    · intro hn
      obtain ⟨m, hmW, hm2⟩ := (hW₀_mem (Φ (Additive.ofMul n) 2)).mp hn
      let q : ↥N := n * m⁻¹
      have hq2 : Φ (Additive.ofMul q) 2 = 0 := by
        change Φ (Additive.ofMul (n * m⁻¹)) 2 = 0
        rw [hinvN m, phi_apply_mul, hm2, htwo]
      have hqP : (q : G) ∈ P := (hPmem q).mpr hq2
      have hqW : (q : G) ∈ W := ⟨hPN hqP, hPleU₁ hqP⟩
      have hmm : m * m = 1 := by
        simpa [hinvN m] using mul_inv_cancel m
      have hqm : q * m = n := by
        change n * m⁻¹ * m = n
        rw [hinvN m, mul_assoc, hmm, mul_one]
      have hval : ((q * m : ↥N) : G) = (n : G) := congrArg Subtype.val hqm
      rw [← hval]
      exact W.mul_mem hqW hmW
  have hP_W : P ≤ W := le_inf hPN hPleU₁
  have hW₀_mul : ∀ (d : ↥Kb) {c : K}, c ∈ W₀ → (χ₃ d : K) * c ∈ W₀ := by
    intro d c hc
    obtain ⟨m, hmW, hm2⟩ := (hW₀_mem c).mp hc
    refine ⟨conjN d m, ?_, ?_⟩
    · exact ⟨(conjN d m).2,
        (Subgroup.mem_normalizer_iff.mp (hKbU₁ d.2) (m : G)).mp hmW.2⟩
    · rw [(hact d m (conjN d m) rfl).1, hm2, mul_comm]
  have hW₀_ne_top : W₀ ≠ ⊤ := by
    intro htop
    apply hNnotU₁
    intro n hn
    have hmem : Φ (Additive.ofMul ⟨n, hn⟩) 2 ∈ W₀ := by
      rw [htop]
      exact AddSubgroup.mem_top _
    exact (hW_mem_iff ⟨n, hn⟩).mpr hmem |>.2
  have hW₀_inv : ∀ (d : ↥Kb), (χ₃ d : K) ≠ 1 →
      ∀ c : K, c * ((χ₃ d : K) + 1) ∈ W₀ → c ∈ W₀ := by
    intro d hd c hc
    exact mem_of_mul_add_one_mem (W := W₀) (lam := (χ₃ d : K)) hd
      (fun x hx => by simpa [mul_comm] using hW₀_mul d hx) hK2 (by simpa [mul_comm] using hc)
  have hN_comm_W_iff : ∀ (d : ↥Kb) (n : ↥N),
      (⁅(d : G), (n : G)⁆ ∈ W) ↔
        Φ (Additive.ofMul n) 2 * ((χ₃ d : K) + 1) ∈ W₀ := by
    intro d n
    let dn : ↥N := conjN d n
    let cn : ↥N := dn * n
    have hcomm_eq : ⁅(d : G), (n : G)⁆ = (cn : G) := by
      have hninv : (n : G)⁻¹ = n := congrArg Subtype.val (hinvN n)
      rw [commutatorElement_def, hninv]
      simp [cn, dn, conjN]
    have hcn2 : Φ (Additive.ofMul cn) 2 =
        Φ (Additive.ofMul n) 2 * (χ₃ d : K) + Φ (Additive.ofMul n) 2 := by
      change Φ (Additive.ofMul (dn * n)) 2 = _
      rw [phi_apply_mul, (hact d n dn rfl).1]
    have hfac : Φ (Additive.ofMul cn) 2 =
        Φ (Additive.ofMul n) 2 * ((χ₃ d : K) + 1) := by
      rw [hcn2, mul_add, mul_one]
    rw [hcomm_eq, hW_mem_iff cn, hfac]
  have hχ3_triv_reduce : ∀ d : ↥Kb,
      ((∀ y ∈ N ⊔ U₁, ⁅(d : G), y⁆ ∈ U₁) ↔
        (∀ n : ↥N, Φ (Additive.ofMul n) 2 * ((χ₃ d : K) + 1) ∈ W₀)) := by
    intro d
    constructor
    · intro hall n
      have hnY : (n : G) ∈ N ⊔ U₁ := Subgroup.mem_sup_left n.2
      have hdnU₁ : ⁅(d : G), (n : G)⁆ ∈ U₁ := hall (n : G) hnY
      exact (hN_comm_W_iff d n).mp
        ⟨hcomm_mem_normalizer N (hKbN d.2) n.2, hdnU₁⟩
    · intro hall y hy
      obtain ⟨n, hn, u, hu, hnu⟩ := hY₁_decomp y hy
      let nN : ↥N := ⟨n, hn⟩
      have hdnW : ⁅(d : G), (n : G)⁆ ∈ W := (hN_comm_W_iff d nN).mpr (hall nN)
      have hnu_comm : n * ⁅(d : G), u⁆ = ⁅(d : G), u⁆ * n :=
        hUcomm (hNU hn) (hU₁U (hcomm_mem_normalizer U₁ (hKbU₁ d.2) hu))
      have hcomm_nu : n * ⁅(d : G), u⁆ * n⁻¹ = ⁅(d : G), u⁆ := by
        rw [hnu_comm]
        group
      have hy_eq : ⁅(d : G), y⁆ = ⁅(d : G), (n : G)⁆ * ⁅(d : G), u⁆ := by
        rw [← hnu, CFSG.commutator_mul_right]
        calc ⁅(d : G), (n : G)⁆ * n * ⁅(d : G), u⁆ * n⁻¹ =
            ⁅(d : G), (n : G)⁆ * (n * ⁅(d : G), u⁆ * n⁻¹) := by group
          _ = ⁅(d : G), (n : G)⁆ * ⁅(d : G), u⁆ := by rw [hcomm_nu]
      rw [hy_eq]
      exact U₁.mul_mem (Subgroup.mem_inf.mp hdnW).2
        (hcomm_mem_normalizer U₁ (hKbU₁ d.2) hu)
  have hχ3_fpf_reduce : ∀ d : ↥Kb,
      ((∀ y ∈ N ⊔ U₁, ⁅(d : G), y⁆ ∈ U₁ → y ∈ U₁) ↔
        (∀ n : ↥N, Φ (Additive.ofMul n) 2 * ((χ₃ d : K) + 1) ∈ W₀ →
          Φ (Additive.ofMul n) 2 ∈ W₀)) := by
    intro d
    constructor
    · intro hall n hn
      have hdnW : ⁅(d : G), (n : G)⁆ ∈ W := (hN_comm_W_iff d n).mpr hn
      have hnU₁ : (n : G) ∈ U₁ := hall (n : G) (Subgroup.mem_sup_left n.2)
        (Subgroup.mem_inf.mp hdnW).2
      exact (hW_mem_iff n).mp ⟨n.2, hnU₁⟩
    · intro hall y hy hcomm
      obtain ⟨n, hn, u, hu, hnu⟩ := hY₁_decomp y hy
      let nN : ↥N := ⟨n, hn⟩
      have hnu_comm : n * ⁅(d : G), u⁆ = ⁅(d : G), u⁆ * n :=
        hUcomm (hNU hn) (hU₁U (hcomm_mem_normalizer U₁ (hKbU₁ d.2) hu))
      have hcomm_nu : n * ⁅(d : G), u⁆ * n⁻¹ = ⁅(d : G), u⁆ := by
        rw [hnu_comm]
        group
      have hy_eq : ⁅(d : G), y⁆ = ⁅(d : G), (n : G)⁆ * ⁅(d : G), u⁆ := by
        rw [← hnu, CFSG.commutator_mul_right]
        calc ⁅(d : G), (n : G)⁆ * n * ⁅(d : G), u⁆ * n⁻¹ =
            ⁅(d : G), (n : G)⁆ * (n * ⁅(d : G), u⁆ * n⁻¹) := by group
          _ = ⁅(d : G), (n : G)⁆ * ⁅(d : G), u⁆ := by rw [hcomm_nu]
      have hdu : ⁅(d : G), u⁆ ∈ U₁ :=
        hcomm_mem_normalizer U₁ (hKbU₁ d.2) hu
      have hcomm_ny : (⁅(d : G), y⁆ ∈ U₁) ↔ (⁅(d : G), (n : G)⁆ ∈ U₁) := by
        rw [hy_eq]
        constructor
        · intro h
          have hsplit : ⁅(d : G), (n : G)⁆ =
              (⁅(d : G), (n : G)⁆ * ⁅(d : G), u⁆) * ⁅(d : G), u⁆⁻¹ := by
            group
          rw [hsplit]
          exact U₁.mul_mem h (U₁.inv_mem hdu)
        · intro h
          exact U₁.mul_mem h hdu
      have hdnW : ⁅(d : G), (n : G)⁆ ∈ W :=
        ⟨hcomm_mem_normalizer N (hKbN d.2) hn, hcomm_ny.mp hcomm⟩
      have hnW : (n : G) ∈ W :=
        (hW_mem_iff nN).mpr (hall nN ((hN_comm_W_iff d nN).mp hdnW))
      rw [← hnu]
      exact U₁.mul_mem (Subgroup.mem_inf.mp hnW).2 hu
  obtain ⟨c₀, hc₀⟩ : ∃ c : K, c ∉ W₀ := by
    have hlt : W₀ < ⊤ := lt_of_le_of_ne le_top hW₀_ne_top
    obtain ⟨-, c, -, hc⟩ := SetLike.lt_iff_le_and_exists.mp hlt
    exact ⟨c, hc⟩
  have hχ3triv : ∀ d : ↥Kb,
      ((∀ y ∈ N ⊔ U₁, ⁅(d : G), y⁆ ∈ U₁) ↔ (χ₃ d : K) = 1) := by
    intro d
    rw [hχ3_triv_reduce d]
    constructor
    · intro hall
      by_contra hne
      have ha0 : (χ₃ d : K) + 1 ≠ 0 := fun h => hne ((hchi3_add_one_iff d).mp h)
      let n : ↥N := (Φ.symm (Pi.single 2 (c₀ * ((χ₃ d : K) + 1)⁻¹))).toMul
      have hn2 : Φ (Additive.ofMul n) 2 = c₀ * ((χ₃ d : K) + 1)⁻¹ := by
        have h : Φ (Additive.ofMul n) = Pi.single 2 (c₀ * ((χ₃ d : K) + 1)⁻¹) := by
          simpa [n] using Φ.apply_symm_apply (Pi.single 2 (c₀ * ((χ₃ d : K) + 1)⁻¹))
        rw [h]
        simp
      have hprod : Φ (Additive.ofMul n) 2 * ((χ₃ d : K) + 1) = c₀ := by
        rw [hn2, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
      have := hall n
      rw [hprod] at this
      exact hc₀ this
    · intro hchi n
      rw [hchi, hone, mul_zero]
      exact W₀.zero_mem
  have hχ3fpf : ∀ d : ↥Kb,
      ((∀ y ∈ N ⊔ U₁, ⁅(d : G), y⁆ ∈ U₁ → y ∈ U₁) ↔ (χ₃ d : K) ≠ 1) := by
    intro d
    rw [hχ3_fpf_reduce d]
    constructor
    · intro hall hchi
      let n : ↥N := (Φ.symm (Pi.single 2 c₀)).toMul
      have hn2 : Φ (Additive.ofMul n) 2 = c₀ := by
        have h : Φ (Additive.ofMul n) = Pi.single 2 c₀ := by
          simpa [n] using Φ.apply_symm_apply (Pi.single 2 c₀)
        rw [h]
        simp
      have hprod : Φ (Additive.ofMul n) 2 * ((χ₃ d : K) + 1) = 0 := by
        rw [hchi, hone, mul_zero]
      have hprodW : Φ (Additive.ofMul n) 2 * ((χ₃ d : K) + 1) ∈ W₀ := by
        rw [hprod]
        exact W₀.zero_mem
      have hmem : Φ (Additive.ofMul n) 2 ∈ W₀ := hall n hprodW
      rw [hn2] at hmem
      exact hc₀ hmem
    · intro hne n hprod
      exact hW₀_inv d hne (Φ (Additive.ofMul n) 2) hprod
  exact ⟨hχ2triv, hχ2fpf, hχ3triv, hχ3fpf, hrelP⟩

end CFSG.Quasithin.Stroth
