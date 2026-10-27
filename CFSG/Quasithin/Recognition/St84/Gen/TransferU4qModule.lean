module

public import CFSG.Quasithin.Recognition.St84.Gen.TransferU4qBasic
public import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel

import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLineVertex
import CFSG.Quasithin.Recognition.St84.Gen.TransferEdgeHyp
import CFSG.Quasithin.H13.L32NLem14324g

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups commutatorElement

variable {H : Type} [Group H] [Finite H] {L1 L2 S : Subgroup H} {m n f : ℕ}

private theorem u4q_scalar_eq_one_of_pow_two {K : Type} [Field K] [Fintype K]
    {L1 L2 S : Subgroup H} {f : ℕ} (c₂ : U4qCoordRight L1 L2 S f K)
    (hU : UnitaryFieldData 2 f K) {t : H} {k : ℕ}
    (ht : t ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set H))
    (htL : ∀ x ∈ L2, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 L2)
    (htk : t ^ 2 ^ k = 1) :
    ∃ s : hU.fixedField, (s : K) = 1 ∧
      ∀ u v : ↥(pCoreOf 2 L2), (v : H) = t * u * t⁻¹ →
        Multiplicative.toAdd (c₂.β v) = (s : K) • Multiplicative.toAdd (c₂.β u) := by
  classical
  obtain ⟨s, -, hscalar⟩ := c₂.exists_smul_of_conj hU ht htL
  obtain ⟨u0, hu0⟩ := (c₂.range_iff (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K)).mpr (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp)
  let Qβ := pCoreOf 2 L2
  let φ := Qβ.normalizerMonoidHom
  let ψ : MulAut ↥Qβ := φ ⟨t, ht⟩
  have hψ : ∀ u : ↥Qβ, ((ψ u : ↥Qβ) : H) = t * (u : H) * t⁻¹ := fun u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Qβ ⟨t, ht⟩ u
  have hstep : ∀ u : ↥Qβ, Multiplicative.toAdd (c₂.β (ψ u)) =
      (s : K) • Multiplicative.toAdd (c₂.β u) := fun u => hscalar u (ψ u) (hψ u)
  have hiter : ∀ (n : ℕ) (u : ↥Qβ),
      Multiplicative.toAdd (c₂.β ((ψ ^ n) u)) = (s : K) ^ n •
        Multiplicative.toAdd (c₂.β u) := by
    intro n
    induction n with
    | zero =>
        intro u
        simp
    | succ n ih =>
        intro u
        rw [pow_succ, MulAut.mul_apply, ih (ψ u), hstep u, smul_smul]
        congr 1
        rw [pow_add, pow_one]
  have hψpow : ψ ^ 2 ^ k = 1 := by
    have hmem : (⟨t, ht⟩ : ↥(Subgroup.normalizer (Qβ : Set H))) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simpa using htk
    have h2 : φ ((⟨t, ht⟩ : ↥(Subgroup.normalizer (Qβ : Set H))) ^ 2 ^ k) = φ 1 :=
      congrArg φ hmem
    rw [map_pow, map_one] at h2
    simpa [ψ] using h2
  have hiterk := hiter (2 ^ k) u0
  rw [hψpow] at hiterk
  simp only [MulAut.one_apply] at hiterk
  rw [hu0] at hiterk
  have hspow : (s : K) ^ 2 ^ k = 1 := by
    have h := congrFun (congrFun hiterk 0) 0
    simpa [Matrix.smul_apply] using h.symm
  haveI : CharP K 2 := hU.charP
  have hsK : (s : K) = 1 := by
    have h0 : ((s : K) - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow, hspow, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).mp h0)
  exact ⟨s, hsK, hscalar⟩

private theorem u4q_commute_of_scalar_eq_one {K : Type} [Field K]
    {L1 L2 S : Subgroup H} {f : ℕ} (c₂ : U4qCoordRight L1 L2 S f K) {t : H} {s : K}
    (hs : s = 1)
    (hscalar : ∀ u v : ↥(pCoreOf 2 L2), (v : H) = t * u * t⁻¹ →
      Multiplicative.toAdd (c₂.β v) = s • Multiplicative.toAdd (c₂.β u))
    (ht : t ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set H)) :
    ∀ x ∈ pCoreOf 2 L2, t * x = x * t := by
  intro x hx
  let u : ↥(pCoreOf 2 L2) := ⟨x, hx⟩
  let v : ↥(pCoreOf 2 L2) :=
    ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht x).mp hx⟩
  have hv : (v : H) = t * u * t⁻¹ := rfl
  have hβ : c₂.β v = c₂.β u := by
    have h := hscalar u v hv
    rw [hs, one_smul] at h
    exact Multiplicative.toAdd.injective h
  have hxeq : t * x * t⁻¹ = x := congrArg Subtype.val (c₂.injective_β hβ)
  calc t * x = t * x * t⁻¹ * t := by group
    _ = x * t := by rw [hxeq]

theorem f112ll_u4q_commute_pCoreOf_right (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) {c : H} (hcS : c ∈ S)
    (hcβ : c ∈ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))) :
    ∀ x ∈ pCoreOf 2 (f112saP2' L1 L2 S), c * x = x * c := by
  classical
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hQβ : pCoreOf 2 Lβ = pCoreOf 2 (f112saP2' L1 L2 S) :=
    CFSG.Quasithin.pCoreOf_oTwoPrime (f112saP2' L1 L2 S)
  have hH : Hyp111 Lα Lβ T := f112ll_hyp111_edge hF hm hn h1 h2
  have hS : Nat.card T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have hd' : U4qLocalData Lα Lβ T f := hd
  obtain ⟨K, hKfield, hKfintype, ⟨c₂⟩⟩ := hd'.exists_coordRight hH hS
  letI : Field K := hKfield
  letI : Fintype K := hKfintype
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hd'.one_le, c₂.card⟩
  have hcNβ : c ∈ Subgroup.normalizer (pCoreOf 2 Lβ : Set H) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lβ
      (mem_trivOTwoQuot.mp hcβ).1
  have hcLβ : ∀ x ∈ Lβ, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 Lβ :=
    (mem_trivOTwoQuot.mp hcβ).2
  obtain ⟨k, hk⟩ := hF.1.h1.pgroup ⟨c, hcS⟩
  have hck : c ^ 2 ^ k = 1 := by
    simpa using congrArg (fun x : ↥S => (x : H)) hk
  obtain ⟨s, hs, hscalar⟩ := u4q_scalar_eq_one_of_pow_two c₂ hU hcNβ hcLβ hck
  have hcomm := u4q_commute_of_scalar_eq_one c₂ hs hscalar hcNβ
  intro x hx
  rw [← hQβ] at hx
  exact hcomm x hx

private theorem u4q_commute_pCoreOf_right_of_triv {K : Type} [Field K] [Fintype K]
    {L1 L2 S : Subgroup H} {f : ℕ} (hD : U4qLocalData L1 L2 S f)
    (hH : Hyp111 L1 L2 S) (hS : Nat.card S = 2 ^ (6 * f))
    (c₂ : U4qCoordRight L1 L2 S f K) (hU : UnitaryFieldData 2 f K) {t : H}
    (ht : t ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set H))
    (htL : ∀ x ∈ L2, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 L2) (htL1 : t ∈ L1) :
    ∀ x ∈ pCoreOf 2 L2, t * x = x * t := by
  classical
  obtain ⟨s, -, hscalar⟩ := c₂.exists_smul_of_conj hU ht htL
  obtain ⟨z, hzβ⟩ := (c₂.range_iff (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K)).mpr (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp)
  have hzZ : (z : H) ∈ centerOf (pCoreOf 2 L1) :=
    (c₂.mem_center_iff z).mpr (by rw [hzβ]; simp)
  have hzQβ : (z : H) ∈ pCoreOf 2 L2 := hD.center_le_right hH hS hzZ
  have htz : t * (z : H) * t⁻¹ = (z : H) := by
    have h : (z : H) * t = t * (z : H) :=
      Subgroup.mem_centralizer_iff.mp (hD.center_left htL1) (z : H) hzZ
    rw [h.symm, mul_inv_cancel_right]
  let zβ : ↥(pCoreOf 2 L2) := ⟨(z : H), hzQβ⟩
  let vβ : ↥(pCoreOf 2 L2) :=
    ⟨t * (z : H) * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht (z : H)).mp hzQβ⟩
  have hv : (vβ : H) = t * (zβ : H) * t⁻¹ := rfl
  have hs := hscalar zβ vβ hv
  have hvz : vβ = zβ := Subtype.ext htz
  rw [hvz] at hs
  have hzβ' : Multiplicative.toAdd (c₂.β zβ) = !![1, 0; 0, 0] := by
    simpa [zβ] using hzβ
  have hsK : (s : K) = 1 := by
    have h := congrFun (congrFun hs 0) 0
    rw [hzβ'] at h
    simpa [Matrix.smul_apply] using h.symm
  exact u4q_commute_of_scalar_eq_one c₂ hsK hscalar ht

private theorem u4q_alpha_eq_one_of_commute_right {F : Type*} [Field F] [Fintype F]
    {L1 L2 S : Subgroup H} {f : ℕ} (c₁ : U4qCoordLeft L1 L2 S f F)
    {t : H} (ht : t ∈ L1) (htodd : Odd (orderOf t))
    (hcentβ : ∀ x ∈ pCoreOf 2 L2, t * x = x * t) :
    c₁.α ⟨t, ht⟩ = 1 := by
  classical
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa [Nat.card_eq_fintype_card] using c₁.card)
  obtain ⟨u, hu⟩ := c₁.surjective_β
    (Multiplicative.ofAdd (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F))
  have hu' : Multiplicative.toAdd (c₁.β u) = !![1, 0; 0, 0] := by
    rw [hu]
    rfl
  have huQβ : (u : H) ∈ pCoreOf 2 L2 :=
    (c₁.mem_inf_iff u).mpr (by
      rw [hu']
      ext j
      fin_cases j <;> rfl)
  have htu : t * (u : H) * t⁻¹ = (u : H) := by
    have h := hcentβ (u : H) huQβ
    rw [h, mul_inv_cancel_right]
  have heq := c₁.equivariant (⟨t, ht⟩ : ↥L1) u u (by exact htu.symm)
  let A : Matrix (Fin 2) (Fin 2) F := (c₁.α ⟨t, ht⟩ : Matrix (Fin 2) (Fin 2) F)
  have hAeq : A * !![1, 0; 0, 0] = !![1, 0; 0, 0] := by
    have h := heq
    rw [hu'] at h
    exact h.symm
  have hA00 : A 0 0 = 1 := by
    have h := congrFun (congrFun hAeq 0) 0
    simpa [A, Matrix.mul_apply, Fin.sum_univ_two] using h
  have hA10 : A 1 0 = 0 := by
    have h := congrFun (congrFun hAeq 1) 0
    simpa [A, Matrix.mul_apply, Fin.sum_univ_two] using h
  have hA11 : A 1 1 = 1 := by
    have hdet : A.det = 1 := (c₁.α ⟨t, ht⟩).2
    rw [Matrix.det_fin_two, hA00, hA10, mul_zero, sub_zero, one_mul] at hdet
    exact hdet
  have hA2 : A * A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hA00, hA10, hA11,
        CharTwo.add_self_eq_zero]
  have hα2 : (c₁.α ⟨t, ht⟩) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [A, pow_two] using hA2
  have hαodd : Odd (orderOf (c₁.α ⟨t, ht⟩)) := by
    have hdvd : orderOf (c₁.α ⟨t, ht⟩) ∣ orderOf (⟨t, ht⟩ : ↥L1) :=
      orderOf_map_dvd c₁.α ⟨t, ht⟩
    rw [← Subgroup.orderOf_coe] at hdvd
    exact htodd.of_dvd_nat hdvd
  have hα1 : c₁.α ⟨t, ht⟩ = 1 := by
    have hdvd2 : orderOf (c₁.α ⟨t, ht⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one hα2
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.mpr hαodd) hdvd2)
  exact hα1

private theorem u4q_eq_one_of_odd_of_mem_pCoreOf {L1 L2 S : Subgroup H} {f : ℕ}
    (hD : U4qLocalData L1 L2 S f) {t : H} (htodd : Odd (orderOf t))
    (htQ : t ∈ pCoreOf 2 L1) : t = 1 := by
  have hdvd : orderOf t ∣ 2 ^ (5 * f) := by
    have h := Subgroup.orderOf_dvd_natCard (pCoreOf 2 L1) htQ
    rwa [hD.card_left] at h
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd
      ((Nat.coprime_two_right.mpr htodd).pow_right (5 * f)) hdvd)

private theorem u4q_eq_one_of_odd_of_commute_right {F : Type*} [Field F] [Fintype F]
    {L1 L2 S : Subgroup H} {f : ℕ} (c₁ : U4qCoordLeft L1 L2 S f F)
    (hD : U4qLocalData L1 L2 S f) {t : H} (ht : t ∈ L1) (htodd : Odd (orderOf t))
    (hcentβ : ∀ x ∈ pCoreOf 2 L2, t * x = x * t) : t = 1 := by
  have hα1 := u4q_alpha_eq_one_of_commute_right c₁ ht htodd hcentβ
  have htQα : t ∈ pCoreOf 2 L1 := (c₁.eq_one_iff ⟨t, ht⟩).mp hα1
  exact u4q_eq_one_of_odd_of_mem_pCoreOf hD htodd htQα

theorem f112ll_u4q_eq_one_of_mem_trivOTwoQuot_right (hF : F112HypW L1 L2 S) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) {d : H} (hdα : d ∈ oTwoPrime (f112saP1' L1 L2 S))
    (hdodd : Odd (orderOf d)) (hdβ : d ∈ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))) :
    d = 1 := by
  classical
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hH : Hyp111 Lα Lβ T := f112ll_hyp111_edge hF hm hn h1 h2
  have hS : Nat.card T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have hd' : U4qLocalData Lα Lβ T f := hd
  obtain ⟨K, hKfield, hKfintype, ⟨c₂⟩⟩ := hd'.exists_coordRight hH hS
  letI : Field K := hKfield
  letI : Fintype K := hKfintype
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hd'.one_le, c₂.card⟩
  obtain ⟨F, hFfield, hFfintype, ⟨c₁⟩⟩ := hd'.exists_coordLeft hH hS
  letI : Field F := hFfield
  letI : Fintype F := hFfintype
  have hdNβ : d ∈ Subgroup.normalizer (pCoreOf 2 Lβ : Set H) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lβ
      (mem_trivOTwoQuot.mp hdβ).1
  have hdLβ : ∀ x ∈ Lβ, d * x * d⁻¹ * x⁻¹ ∈ pCoreOf 2 Lβ :=
    (mem_trivOTwoQuot.mp hdβ).2
  have hcentβ := u4q_commute_pCoreOf_right_of_triv hd' hH hS c₂ hU hdNβ hdLβ hdα
  exact u4q_eq_one_of_odd_of_commute_right c₁ hd' hdα hdodd hcentβ

private theorem u4q_exists_additive_map_of_triv {G : Type*} [Group G]
    {L1 L2 S : Subgroup G} {f : ℕ} {F : Type*} [Field F]
    (c₁ : U4qCoordLeft L1 L2 S f F) {c : G}
    {ψ : MulAut ↥(pCoreOf 2 L1)}
    (hψ : ∀ u : ↥(pCoreOf 2 L1), ((ψ u : ↥(pCoreOf 2 L1)) : G) = c * u * c⁻¹)
    (hcZ : c ∈ Subgroup.normalizer (centerOf (pCoreOf 2 L1) : Set G)) :
    ∃ y : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F,
      ∀ u : ↥(pCoreOf 2 L1),
        y (Multiplicative.toAdd (c₁.β u)) = Multiplicative.toAdd (c₁.β (ψ u)) := by
  classical
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [c₁.card]; exact pow_ne_zero _ two_ne_zero)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa [Nat.card_eq_fintype_card] using c₁.card)
  let Q := pCoreOf 2 L1
  have hker : ∀ u : ↥Q, c₁.β u = 1 → c₁.β (ψ u) = 1 := by
    intro u hu
    have hu' : u ∈ c₁.β.ker := hu
    rw [c₁.ker_β, Subgroup.mem_subgroupOf] at hu'
    have hψu : ψ u ∈ c₁.β.ker := by
      rw [c₁.ker_β, Subgroup.mem_subgroupOf, hψ]
      exact (Subgroup.mem_normalizer_iff.mp hcZ u).mp hu'
    exact hψu
  choose sec hsec using fun X => c₁.surjective_β X
  have hwd : ∀ u : ↥Q, c₁.β (ψ (sec (c₁.β u))) = c₁.β (ψ u) := by
    intro u
    have h1 : c₁.β ((sec (c₁.β u))⁻¹ * u) = 1 := by rw [map_mul, map_inv, hsec, inv_mul_cancel]
    have h2 := hker _ h1
    rw [map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one] at h2
    exact h2
  let y : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F :=
    AddMonoidHom.mk' (fun X => Multiplicative.toAdd (c₁.β (ψ (sec (Multiplicative.ofAdd X)))))
      (by
        intro X Z
        have e : Multiplicative.ofAdd (X + Z) =
            c₁.β (sec (Multiplicative.ofAdd X) * sec (Multiplicative.ofAdd Z)) := by
          rw [map_mul, hsec, hsec, ofAdd_add]
        simp only [e]
        rw [hwd, map_mul, map_mul, toAdd_mul])
  refine ⟨y, ?_⟩
  intro u
  change Multiplicative.toAdd (c₁.β (ψ (sec (Multiplicative.ofAdd
    (Multiplicative.toAdd (c₁.β u)))))) = _
  rw [ofAdd_toAdd, hwd]

private theorem u4q_additive_map_commutes_left {G : Type*} [Group G]
    {L1 L2 S : Subgroup G} {f : ℕ} {F : Type*} [Field F]
    (c₁ : U4qCoordLeft L1 L2 S f F) {c : G}
    {ψ : MulAut ↥(pCoreOf 2 L1)}
    (hψ : ∀ u : ↥(pCoreOf 2 L1), ((ψ u : ↥(pCoreOf 2 L1)) : G) = c * u * c⁻¹)
    (hcL : c ∈ Subgroup.normalizer (L1 : Set G))
    (hcQ : ∀ x ∈ L1, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L1)
    (y : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F)
    (hy : ∀ u : ↥(pCoreOf 2 L1),
      y (Multiplicative.toAdd (c₁.β u)) = Multiplicative.toAdd (c₁.β (ψ u))) :
    ∀ (g : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F),
      y ((g : Matrix (Fin 2) (Fin 2) F) * X) = (g : Matrix (Fin 2) (Fin 2) F) * y X := by
  intro g X
  obtain ⟨x, rfl⟩ := c₁.surjective_α g
  obtain ⟨u, hu⟩ := c₁.surjective_β (Multiplicative.ofAdd X)
  have hu' : Multiplicative.toAdd (c₁.β u) = X := by
    rw [hu]
    rfl
  rw [← hu']
  let w : ↥(pCoreOf 2 L1) := ⟨(x : G) * u * (x : G)⁻¹,
    CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf x.2 u.2⟩
  let z : ↥L1 := ⟨c * (x : G) * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcL (x : G)).mp x.2⟩
  have hαz : c₁.α z = c₁.α x := by
    have hq : ((z * x⁻¹ : ↥L1) : G) ∈ pCoreOf 2 L1 := by
      simpa [z] using hcQ (x : G) x.2
    have e := (c₁.eq_one_iff (z * x⁻¹)).mpr hq
    rwa [map_mul, map_inv, mul_inv_eq_one] at e
  rw [← c₁.equivariant x u w rfl, hy, hy, ← hαz]
  refine c₁.equivariant z (ψ u) (ψ w) ?_
  rw [hψ, hψ]
  change c * ((x : G) * u * (x : G)⁻¹) * c⁻¹ =
    c * (x : G) * c⁻¹ * (c * u * c⁻¹) * (c * (x : G) * c⁻¹)⁻¹
  group

private theorem u4q_exists_mul_beta_of_triv {G : Type*} [Group G] {L1 L2 S : Subgroup G} {f : ℕ}
    {F : Type*} [Field F] (c₁ : U4qCoordLeft L1 L2 S f F) {c : G}
    {ψ : MulAut ↥(pCoreOf 2 L1)}
    (hψ : ∀ u : ↥(pCoreOf 2 L1), ((ψ u : ↥(pCoreOf 2 L1)) : G) = c * u * c⁻¹)
    (hcL : c ∈ Subgroup.normalizer (L1 : Set G))
    (hcZ : c ∈ Subgroup.normalizer (centerOf (pCoreOf 2 L1) : Set G))
    (hcQ : ∀ x ∈ L1, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L1) :
    ∃ M : Matrix (Fin 2) (Fin 2) F, ∀ u : ↥(pCoreOf 2 L1),
      Multiplicative.toAdd (c₁.β (ψ u)) = Multiplicative.toAdd (c₁.β u) * M := by
  classical
  classical
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [c₁.card]; exact pow_ne_zero _ two_ne_zero)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa [Nat.card_eq_fintype_card] using c₁.card)
  obtain ⟨y, hy⟩ := u4q_exists_additive_map_of_triv c₁ hψ hcZ
  have hycomm := u4q_additive_map_commutes_left c₁ hψ hcL hcQ y hy
  refine ⟨y 1, fun u => ?_⟩
  rw [← hy]
  exact CFSG.Quasithin.H13.L14324.eq_mul_of_comm_left y hycomm _

private theorem u4q_right_mul_matrix_eq_one {F : Type*} [Field F]
    {L1 L2 S : Subgroup H} {f : ℕ} (c₁ : U4qCoordLeft L1 L2 S f F)
    {c : H} {ψ : MulAut ↥(pCoreOf 2 L1)}
    (hψ : ∀ u : ↥(pCoreOf 2 L1), ((ψ u : ↥(pCoreOf 2 L1)) : H) = c * u * c⁻¹)
    (hcommβ : ∀ x ∈ pCoreOf 2 L2, c * x = x * c)
    {M : Matrix (Fin 2) (Fin 2) F}
    (hM : ∀ u : ↥(pCoreOf 2 L1),
      Multiplicative.toAdd (c₁.β (ψ u)) = Multiplicative.toAdd (c₁.β u) * M) :
    M = 1 := by
  have hfix : ∀ X : Matrix (Fin 2) (Fin 2) F, X 1 = 0 → X * M = X := by
    intro X hX
    obtain ⟨u, hu⟩ := c₁.surjective_β (Multiplicative.ofAdd X)
    have hu' : Multiplicative.toAdd (c₁.β u) = X := by
      rw [hu]
      rfl
    have huQβ : (u : H) ∈ pCoreOf 2 L2 :=
      (c₁.mem_inf_iff u).mpr (by rw [hu']; exact hX)
    have hcu : c * (u : H) * c⁻¹ = (u : H) := by
      have h := hcommβ (u : H) huQβ
      rw [h, mul_inv_cancel_right]
    have hψu : ψ u = u := Subtype.ext (by rw [hψ]; exact hcu)
    have h := hM u
    rw [hψu, hu'] at h
    exact h.symm
  have hE00 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) * M = !![1, 0; 0, 0] :=
    hfix _ (by ext j; fin_cases j <;> rfl)
  have hE01 : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) * M = !![0, 1; 0, 0] :=
    hfix _ (by ext j; fin_cases j <;> rfl)
  have hM00 : M 0 0 = 1 := by
    have h := congrFun (congrFun hE00 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hM01 : M 0 1 = 0 := by
    have h := congrFun (congrFun hE00 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hM10 : M 1 0 = 0 := by
    have h := congrFun (congrFun hE01 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hM11 : M 1 1 = 1 := by
    have h := congrFun (congrFun hE01 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hM00, hM01, hM10, hM11]

private theorem u4q_commutator_mem_center_of_mul_matrix_eq_one {F : Type*} [Field F]
    {L1 L2 S : Subgroup H} {f : ℕ} (c₁ : U4qCoordLeft L1 L2 S f F)
    {c : H} {ψ : MulAut ↥(pCoreOf 2 L1)}
    (hψ : ∀ u : ↥(pCoreOf 2 L1), ((ψ u : ↥(pCoreOf 2 L1)) : H) = c * u * c⁻¹)
    {M : Matrix (Fin 2) (Fin 2) F}
    (hM : ∀ u : ↥(pCoreOf 2 L1),
      Multiplicative.toAdd (c₁.β (ψ u)) = Multiplicative.toAdd (c₁.β u) * M)
    (hM1 : M = 1) :
    ∀ x ∈ pCoreOf 2 L1, c * x * c⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 L1) := by
  intro x hx
  let x' : ↥(pCoreOf 2 L1) := ⟨x, hx⟩
  have h := hM x'
  rw [hM1, Matrix.mul_one] at h
  have hker : (ψ x' * x'⁻¹ : ↥(pCoreOf 2 L1)) ∈ c₁.β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_one, h]
    exact add_neg_cancel _
  rw [c₁.ker_β, Subgroup.mem_subgroupOf] at hker
  have hval : ((ψ x' * x'⁻¹ : ↥(pCoreOf 2 L1)) : H) = c * x * c⁻¹ * x⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hψ]
  rw [hval] at hker
  exact hker

theorem f112ll_u4q_commutator_mem_center_left (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) {c : H} (hcS : c ∈ S)
    (hcα : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)))
    (hcβ : c ∈ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))) :
    ∀ x ∈ pCoreOf 2 (f112saP1' L1 L2 S), ⁅c, x⁆ ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) := by
  classical
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  let Qα := pCoreOf 2 Lα
  have hQα : Qα = pCoreOf 2 (f112saP1' L1 L2 S) :=
    CFSG.Quasithin.pCoreOf_oTwoPrime (f112saP1' L1 L2 S)
  have hQβ : pCoreOf 2 Lβ = pCoreOf 2 (f112saP2' L1 L2 S) :=
    CFSG.Quasithin.pCoreOf_oTwoPrime (f112saP2' L1 L2 S)
  have hH : Hyp111 Lα Lβ T := f112ll_hyp111_edge hF hm hn h1 h2
  have hS : Nat.card T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have hd' : U4qLocalData Lα Lβ T f := hd
  obtain ⟨F, hFfield, hFfintype, ⟨c₁⟩⟩ := hd'.exists_coordLeft hH hS
  letI : Field F := hFfield
  letI : Fintype F := hFfintype
  have hcL : c ∈ Subgroup.normalizer (Lα : Set H) := (mem_trivOTwoQuot.mp hcα).1
  have hcN : c ∈ Subgroup.normalizer (Qα : Set H) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lα hcL
  have hcZ : c ∈ Subgroup.normalizer (centerOf Qα : Set H) :=
    CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf Qα hcN
  have hcQ : ∀ x ∈ Lα, c * x * c⁻¹ * x⁻¹ ∈ Qα := (mem_trivOTwoQuot.mp hcα).2
  let ψ : MulAut ↥Qα := Qα.normalizerMonoidHom ⟨c, hcN⟩
  have hψ : ∀ u : ↥Qα, ((ψ u : ↥Qα) : H) = c * (u : H) * c⁻¹ := fun u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Qα ⟨c, hcN⟩ u
  obtain ⟨M, hM⟩ := u4q_exists_mul_beta_of_triv c₁ hψ hcL hcZ hcQ
  have hcommβ : ∀ x ∈ pCoreOf 2 Lβ, c * x = x * c := by
    intro x hx
    exact f112ll_u4q_commute_pCoreOf_right hF hm hn h1 h2 hd hcS hcβ x (hQβ ▸ hx)
  have hM1 := u4q_right_mul_matrix_eq_one c₁ hψ hcommβ hM
  intro x hx
  have hx' : x ∈ Qα := by rwa [hQα]
  rw [commutatorElement_def, ← hQα]
  exact u4q_commutator_mem_center_of_mul_matrix_eq_one c₁ hψ hM hM1 x hx'

end CFSG.Quasithin.F112R.St84

end
