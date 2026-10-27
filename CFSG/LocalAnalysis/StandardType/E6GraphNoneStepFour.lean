module

public import CFSG.LocalAnalysis.StandardType.E6GraphNoneFrobIndex
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepFourMatrix
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZWeyl
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted

public section

namespace CFSG.StandardType.E6GraphNoneSteps

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.CrossChar

private noncomputable def weylMat (w : WeylGroup TwistTag.E6.tag) :
    Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
  fun i j => (w⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) j

private theorem weylMat_mul (w w' : WeylGroup TwistTag.E6.tag) :
    weylMat (w * w') = weylMat w * weylMat w' := by
  ext i l
  change ((w * w')⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) l =
    ∑ j, (w⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) j *
      (w'⁻¹ • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) l
  rw [mul_inv_rev, mul_smul, smul_eq_sum_single w'⁻¹]
  simp [Finset.sum_apply]

private theorem weylMat_one : weylMat 1 = 1 := by
  ext i j
  change ((1 : WeylGroup TwistTag.E6.tag)⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) j =
    (1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) i j
  rw [inv_one, one_smul, Matrix.one_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

private theorem weylMat_pow (w : WeylGroup TwistTag.E6.tag) (k : ℕ) :
    weylMat (w ^ k) = weylMat w ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, weylMat_one]
  | succ k ih => rw [pow_succ, pow_succ, weylMat_mul, ih]

private noncomputable abbrev Wω (ω : List (Fin TwistTag.E6.tag.rank)) : Matrix (Fin 6) (Fin 6) ℤ :=
  weylMat ((coxeterSystem TwistTag.E6.tag).wordProd ω)

private theorem Wω_pow_orderOf (ω : List (Fin TwistTag.E6.tag.rank)) :
    Wω ω ^ orderOf ((coxeterSystem TwistTag.E6.tag).wordProd ω) = 1 := by
  have h := weylMat_pow ((coxeterSystem TwistTag.E6.tag).wordProd ω)
    (orderOf ((coxeterSystem TwistTag.E6.tag).wordProd ω))
  rw [pow_orderOf_eq_one, weylMat_one] at h
  exact h.symm

section E6Torus

variable {L : Type} [Field L]

private theorem conjW (ω : List (Fin TwistTag.E6.tag.rank)) (a : Fin 6 → Lˣ) :
    weylWord (τ := TwistTag.E6.tag) L ω * rootDiagUnit TwistTag.E6.tag a *
        (weylWord (τ := TwistTag.E6.tag) L ω)⁻¹ = rootDiagUnit TwistTag.E6.tag (powM (Wω ω) a) :=
  weylWord_conj_rootDiagUnit ω a

private theorem conjP (a : Fin 6 → Lˣ) :
    diagramMap TwistTag.E6 L * rootDiagUnit TwistTag.E6.tag a * (diagramMap TwistTag.E6 L)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (fun i : Fin 6 => a (rho6 i)) := by
  rw [E6_diagramMap_mul_rootDiagUnit, mul_inv_cancel_right]
  congr 1
  funext i
  rw [E6_perm_symm]
  fin_cases i <;> rfl

private theorem frobD (Fr : L →+* L) (q : ℕ) (hFr : ∀ c, Fr c = c ^ q) (a : Fin 6 → Lˣ) :
    Units.map (entrywiseHom Fr) (rootDiagUnit TwistTag.E6.tag a) =
      rootDiagUnit TwistTag.E6.tag (a ^ (q : ℤ)) := by
  refine (units_map_entrywiseHom_rootDiagUnit (t := TwistTag.E6) Fr a).trans ?_
  congr 1
  funext i
  apply Units.ext
  change Fr (a i : L) = ((a i ^ (q : ℤ) : Lˣ) : L)
  rw [hFr, zpow_natCast, Units.val_pow_eq_pow_val]

private theorem powM_comm_rho (ω : List (Fin TwistTag.E6.tag.rank))
    (hn : weylWord (τ := TwistTag.E6.tag) L ω ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    (a : Fin 6 → Lˣ) :
    powM (Wω ω) (fun i => a (rho6 i)) = fun i => powM (Wω ω) a (rho6 i) := by
  set n := weylWord (τ := TwistTag.E6.tag) L ω
  have hP := diagramMap_mul_of_mem_twistedFixedGroup hn
  apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := TwistTag.E6.tag)
  have e1 := conjW (L := L) ω (fun i : Fin 6 => a (rho6 i))
  have e2 := conjW (L := L) ω a
  have e3 := conjP (L := L) (powM (Wω ω) a)
  have e4 := conjP (L := L) a
  refine e1.symm.trans (Eq.trans ?_ e3)
  rw [← e4]
  calc n * (diagramMap TwistTag.E6 L * rootDiagUnit TwistTag.E6.tag a *
        (diagramMap TwistTag.E6 L)⁻¹) * n⁻¹
      = (n * diagramMap TwistTag.E6 L) * rootDiagUnit TwistTag.E6.tag a *
          (n * diagramMap TwistTag.E6 L)⁻¹ := by group
    _ = (diagramMap TwistTag.E6 L * n) * rootDiagUnit TwistTag.E6.tag a *
          (diagramMap TwistTag.E6 L * n)⁻¹ := by rw [hP]
    _ = diagramMap TwistTag.E6 L * (n * rootDiagUnit TwistTag.E6.tag a * n⁻¹) *
          (diagramMap TwistTag.E6 L)⁻¹ := by group
    _ = _ := congrArg (fun X => diagramMap TwistTag.E6 L * X * (diagramMap TwistTag.E6 L)⁻¹) e2

end E6Torus

private noncomputable def antiFixedParams (L : Type) [Field L]
    (ω : List (Fin TwistTag.E6.tag.rank)) (e : ℤ) : Subgroup (Fin 6 → Lˣ) where
  carrier := {a | (fun i => a (rho6 i)) = a⁻¹ ∧ powM (Wω ω) (a ^ e) = a}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · funext i
      have h1 := congrFun ha1 i
      have h2 := congrFun hb1 i
      simp only [Pi.mul_apply, Pi.inv_apply, mul_inv] at h1 h2 ⊢
      rw [h1, h2]
    · rw [mul_zpow, powM_mul, ha2, hb2]
  one_mem' := ⟨by funext i; simp, by
    rw [one_zpow]; funext i; simp [powM]⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · funext i
      have h1 := congrFun ha1 i
      simp only [Pi.inv_apply] at h1 ⊢
      rw [h1]
    · rw [inv_zpow, powM_inv, ha2]

private theorem four_le_card_antiFixedParams {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (ω : List (Fin TwistTag.E6.tag.rank)) (e : ℤ)
    (hn : weylWord (τ := TwistTag.E6.tag) L ω ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    (he : Even e) (h4 : 4 ≤ |e|) :
    4 ≤ Nat.card (antiFixedParams L ω e) := by
  have hc := powM_comm_rho (L := L) ω hn
  have hW := Wω_pow_orderOf ω
  have hk : 0 < orderOf ((coxeterSystem TwistTag.E6.tag).wordProd ω) := orderOf_pos _
  have hS := natCard_antiFixed L (Wω ω) hc hk hW he (by omega : 1 ≤ |e|)
  have h9 : (4 : ℤ) ≤ (|e| - 1) ^ 2 := by
    have h3 : (3 : ℤ) ≤ |e| - 1 := by omega
    nlinarith [sq_nonneg (|e| - 1)]
  have hSeq : Nat.card (antiFixedParams L ω e) =
      Nat.card {a : Fin 6 → Lˣ //
        (fun i => a (rho6 i)) = a⁻¹ ∧ powM (Wω ω) (a ^ e) = a} := rfl
  rw [hSeq]
  exact_mod_cast h9.trans hS.2

private noncomputable def conjParams {L : Type} [Field L] (g : ModGL TwistTag.E6.tag L) :
    (Fin 6 → Lˣ) →* ModGL TwistTag.E6.tag L where
  toFun a := g * rootDiagUnit TwistTag.E6.tag a * g⁻¹
  map_one' := by rw [E6_rootDiagUnit_one, mul_one, mul_inv_cancel]
  map_mul' a b := by rw [E6_rootDiagUnit_mul]; group

private theorem conjParams_injective {L : Type} [Field L]
    (g : ModGL TwistTag.E6.tag L) : Function.Injective (conjParams g) := by
  intro a b h
  change g * rootDiagUnit TwistTag.E6.tag a * g⁻¹ =
    g * rootDiagUnit TwistTag.E6.tag b * g⁻¹ at h
  exact CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := TwistTag.E6.tag)
    (mul_left_cancel (mul_right_cancel h))

private theorem conjParams_commute {L : Type} [Field L]
    (g : ModGL TwistTag.E6.tag L) (a b : Fin 6 → Lˣ) :
    Commute (conjParams g a) (conjParams g b) := by
  have hd : rootDiagUnit TwistTag.E6.tag a * rootDiagUnit TwistTag.E6.tag b =
      rootDiagUnit TwistTag.E6.tag b * rootDiagUnit TwistTag.E6.tag a := by
    rw [← E6_rootDiagUnit_mul, ← E6_rootDiagUnit_mul, mul_comm]
  change g * rootDiagUnit TwistTag.E6.tag a * g⁻¹ *
      (g * rootDiagUnit TwistTag.E6.tag b * g⁻¹) =
    g * rootDiagUnit TwistTag.E6.tag b * g⁻¹ *
      (g * rootDiagUnit TwistTag.E6.tag a * g⁻¹)
  calc g * rootDiagUnit TwistTag.E6.tag a * g⁻¹ *
        (g * rootDiagUnit TwistTag.E6.tag b * g⁻¹)
      = g * (rootDiagUnit TwistTag.E6.tag a * rootDiagUnit TwistTag.E6.tag b) * g⁻¹ := by
        group
    _ = g * (rootDiagUnit TwistTag.E6.tag b * rootDiagUnit TwistTag.E6.tag a) * g⁻¹ := by
        rw [hd]
    _ = g * rootDiagUnit TwistTag.E6.tag b * g⁻¹ *
        (g * rootDiagUnit TwistTag.E6.tag a * g⁻¹) := by group

private theorem conjParams_diagramMap_inv {L : Type} [Field L]
    {g : ModGL TwistTag.E6.tag L}
    (hgP : g ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    {a : Fin 6 → Lˣ} (ha1 : (fun i => a (rho6 i)) = a⁻¹) :
    diagramMap TwistTag.E6 L * conjParams g a * (diagramMap TwistTag.E6 L)⁻¹ =
      conjParams g a⁻¹ := by
  change diagramMap TwistTag.E6 L * (g * rootDiagUnit TwistTag.E6.tag a * g⁻¹) *
      (diagramMap TwistTag.E6 L)⁻¹ = g * rootDiagUnit TwistTag.E6.tag a⁻¹ * g⁻¹
  have hP := diagramMap_mul_of_mem_twistedFixedGroup hgP
  have hd := conjP (L := L) a
  rw [ha1] at hd
  calc diagramMap TwistTag.E6 L * (g * rootDiagUnit TwistTag.E6.tag a * g⁻¹) *
        (diagramMap TwistTag.E6 L)⁻¹
      = (diagramMap TwistTag.E6 L * g) * rootDiagUnit TwistTag.E6.tag a *
          (diagramMap TwistTag.E6 L * g)⁻¹ := by group
    _ = (g * diagramMap TwistTag.E6 L) * rootDiagUnit TwistTag.E6.tag a *
          (g * diagramMap TwistTag.E6 L)⁻¹ := by rw [hP]
    _ = g * (diagramMap TwistTag.E6 L * rootDiagUnit TwistTag.E6.tag a *
          (diagramMap TwistTag.E6 L)⁻¹) * g⁻¹ := by group
    _ = g * rootDiagUnit TwistTag.E6.tag a⁻¹ * g⁻¹ := by
        rw [hd]
        rfl

private theorem e6_conjParams_mem_fixed {K L : Type} [Field K] [Finite K] [Field L]
    [IsAlgClosed L] [CharP L 2] [Algebra K L] (Fr : L →+* L) (q : ℕ) (hFr : ∀ c, Fr c = c ^ q)
    {g : ModGL TwistTag.E6.tag L} (hg : g ∈ adjointGroup TwistTag.E6.tag L)
    (ω : List (Fin TwistTag.E6.tag.rank))
    (hlang : Units.map (entrywiseHom Fr) g =
      g * weylWord (τ := TwistTag.E6.tag) L ω)
    (a : Fin 6 → Lˣ) (ha : powM (Wω ω) (a ^ (q : ℤ)) = a) :
    conjParams g a ∈ adjointGroup TwistTag.E6.tag L ∧
      Units.map (entrywiseHom Fr) (conjParams g a) = conjParams g a := by
  refine ⟨?_, ?_⟩
  · change g * rootDiagUnit TwistTag.E6.tag a * g⁻¹ ∈ adjointGroup TwistTag.E6.tag L
    exact mul_mem (mul_mem hg
      (rootDiagUnit_mem_adjointGroup_of_isAlgClosed (τ := TwistTag.E6.tag) a)) (inv_mem hg)
  · change Units.map (entrywiseHom Fr) (g * rootDiagUnit TwistTag.E6.tag a * g⁻¹) =
      g * rootDiagUnit TwistTag.E6.tag a * g⁻¹
    rw [map_mul, map_mul, map_inv, hlang, frobD Fr q hFr]
    have hconj := (conjW (L := L) ω (a ^ (q : ℤ))).trans
      (congrArg (rootDiagUnit TwistTag.E6.tag) ha)
    calc g * weylWord (τ := TwistTag.E6.tag) L ω *
          rootDiagUnit TwistTag.E6.tag (a ^ (q : ℤ)) *
          (g * weylWord (τ := TwistTag.E6.tag) L ω)⁻¹
        = g * (weylWord (τ := TwistTag.E6.tag) L ω *
            rootDiagUnit TwistTag.E6.tag (a ^ (q : ℤ)) *
            (weylWord (τ := TwistTag.E6.tag) L ω)⁻¹) * g⁻¹ := by group
      _ = _ := congrArg (fun X => g * X * g⁻¹) hconj

theorem e6_step4 {K : Type} [Field K] [Finite K] {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    [Algebra K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (hbij : Function.Bijective Fr)
    (hq : 4 ≤ Nat.card K) (hqe : Even (Nat.card K))
    {g : ModGL TwistTag.E6.tag L} (hg : g ∈ adjointGroup TwistTag.E6.tag L)
    (hgP : g ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    (ω : List (Fin TwistTag.E6.tag.rank))
    (hn : weylWord (τ := TwistTag.E6.tag) L ω ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    (hlang : Units.map (entrywiseHom Fr) g = g * weylWord (τ := TwistTag.E6.tag) L ω) :
    ∃ z ∈ (adjointGroup TwistTag.E6.tag K).map (baseChangeGL (algebraMap K L)),
      (∀ a : Fin 6 → Lˣ, Commute z (g * rootDiagUnit TwistTag.E6.tag a * g⁻¹)) ∧
      diagramMap TwistTag.E6 L * z * (diagramMap TwistTag.E6 L)⁻¹ ≠ z := by
  set q := Nat.card K
  let S := antiFixedParams L ω (q : ℤ)
  have hS : 4 ≤ Nat.card S := four_le_card_antiFixedParams (L := L) ω (q : ℤ) hn
    (by exact_mod_cast hqe) (by rw [Nat.abs_cast]; exact_mod_cast hq)
  set M := S.map (conjParams g)
  have hMcard : 4 ≤ Nat.card M := by
    rw [Subgroup.card_map_of_injective (conjParams_injective g)]
    exact hS
  have hM : ∀ x ∈ M, x ∈ adjointGroup Tag.E6 L ∧ Units.map (entrywiseHom Fr) x = x := by
    rintro _ ⟨a, ⟨-, ha⟩, rfl⟩
    exact e6_conjParams_mem_fixed (K := K) Fr q hFr hg ω hlang a ha
  obtain ⟨m, hmM, hm1, hmC⟩ := e6_frobFixed_exists_ne_one_mem Fr hFr hbij M hM hMcard
  obtain ⟨a, ⟨ha1, -⟩, rfl⟩ := hmM
  refine ⟨conjParams g a, hmC, fun b => conjParams_commute g a b, fun heq => hm1 ?_⟩
  have hη := conjParams_diagramMap_inv hgP ha1
  rw [hη] at heq
  have haa : a⁻¹ = a := conjParams_injective g heq
  have ha : a = 1 := funext fun i => units_sq_eq_one (L := L) (a i) (by
    rw [sq]; nth_rw 1 [← haa]; exact inv_mul_cancel (a i))
  rw [ha]
  exact map_one (conjParams g)

private theorem twE6_conjParams_mem_fixed {K L : Type} [Field K] [Field L]
    [IsAlgClosed L] [CharP L 2] [Algebra K L]
    {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {g : ModGL TwistTag.E6.tag L} (hg : g ∈ adjointGroup TwistTag.E6.tag L)
    (hgP : g ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    (ω : List (Fin TwistTag.E6.tag.rank))
    (hn' : weylWord (τ := TwistTag.E6.tag) L ω ∈
      twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    (hlang : Units.map (entrywiseHom Fr) g =
      g * weylWord (τ := TwistTag.E6.tag) L ω)
    {a : Fin 6 → Lˣ} (ha1 : (fun i => a (rho6 i)) = a⁻¹)
    (ha : powM (Wω ω) (a ^ (-(q : ℤ))) = a) :
    conjParams g a ∈ twistedFixedGroup TwistTag.E6 L Fr := by
  refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).2 ⟨?_, ?_⟩
  · change g * rootDiagUnit TwistTag.E6.tag a * g⁻¹ ∈ adjointGroup TwistTag.E6.tag L
    exact mul_mem (mul_mem hg
      (rootDiagUnit_mem_adjointGroup_of_isAlgClosed (τ := TwistTag.E6.tag) a)) (inv_mem hg)
  · change twistHom TwistTag.E6 L Fr (g * rootDiagUnit TwistTag.E6.tag a * g⁻¹) =
      g * rootDiagUnit TwistTag.E6.tag a * g⁻¹
    rw [twistHom_apply, map_mul, map_mul, map_inv, hlang, frobD Fr q hFr]
    have hP := diagramMap_mul_of_mem_twistedFixedGroup hgP
    have hPn := diagramMap_mul_of_mem_twistedFixedGroup hn'
    have hrho : (fun i : Fin 6 => (a ^ (q : ℤ)) (rho6 i)) = a ^ (-(q : ℤ)) := by
      funext i
      have h1 := congrFun ha1 i
      simp only [Pi.inv_apply] at h1
      simp only [Pi.pow_apply, h1, inv_zpow', zpow_neg]
    have hd := (conjP (L := L) (a ^ (q : ℤ))).trans
      (congrArg (rootDiagUnit TwistTag.E6.tag) hrho)
    have hconj := (conjW (L := L) ω (a ^ (-(q : ℤ)))).trans
      (congrArg (rootDiagUnit TwistTag.E6.tag) ha)
    set n' := weylWord (τ := TwistTag.E6.tag) L ω
    set P := diagramMap TwistTag.E6 L
    calc P * (g * n' * rootDiagUnit TwistTag.E6.tag (a ^ (q : ℤ)) * (g * n')⁻¹) * P⁻¹
        = (P * g) * n' * rootDiagUnit TwistTag.E6.tag (a ^ (q : ℤ)) * n'⁻¹ * (P * g)⁻¹ := by
          group
      _ = (g * P) * n' * rootDiagUnit TwistTag.E6.tag (a ^ (q : ℤ)) * n'⁻¹ * (g * P)⁻¹ := by
          rw [hP]
      _ = g * (P * n') * rootDiagUnit TwistTag.E6.tag (a ^ (q : ℤ)) * (P * n')⁻¹ * g⁻¹ := by
          group
      _ = g * (n' * P) * rootDiagUnit TwistTag.E6.tag (a ^ (q : ℤ)) * (n' * P)⁻¹ * g⁻¹ := by
          rw [hPn]
      _ = g * (n' * (P * rootDiagUnit TwistTag.E6.tag (a ^ (q : ℤ)) * P⁻¹) * n'⁻¹) * g⁻¹ := by
          group
      _ = g * (n' * rootDiagUnit TwistTag.E6.tag (a ^ (-(q : ℤ))) * n'⁻¹) * g⁻¹ :=
          congrArg (fun X => g * (n' * X * n'⁻¹) * g⁻¹) hd
      _ = _ := congrArg (fun X => g * X * g⁻¹) hconj

theorem twE6_step4 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n)) {L : Type}
    [Field L] [Algebra K L] [IsAlgClosure K L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {g : ModGL TwistTag.E6.tag L} (hg : g ∈ adjointGroup TwistTag.E6.tag L)
    (hgP : g ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    (ω : List (Fin TwistTag.E6.tag.rank))
    (hn' : weylWord (τ := TwistTag.E6.tag) L ω ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    (hlang : Units.map (entrywiseHom Fr) g = g * weylWord (τ := TwistTag.E6.tag) L ω) :
    ∃ z ∈ (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL (algebraMap K L)),
      (∀ a : Fin 6 → Lˣ, Commute z (g * rootDiagUnit TwistTag.E6.tag a * g⁻¹)) ∧
      diagramMap TwistTag.E6 L * z * (diagramMap TwistTag.E6 L)⁻¹ ≠ z := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Fintype.card K = 2 ^ (n * 2) := by rw [Fintype.card_eq_nat_card, hK, pow_mul]
  have : CharP K 2 := charP_of_card_eq_prime_pow hK'
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set q := 2 ^ n with hqdef
  have hq : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hqe : Even q := (Nat.even_pow' (by omega)).2 even_two
  let S := antiFixedParams L ω (-(q : ℤ))
  have hS : 4 ≤ Nat.card S := four_le_card_antiFixedParams (L := L) ω (-(q : ℤ)) hn'
    (by rw [even_neg]; exact_mod_cast hqe)
    (by rw [abs_neg, Nat.abs_cast]; exact_mod_cast hq)
  set M := S.map (conjParams g)
  have hMcard : 4 ≤ Nat.card M := by
    rw [Subgroup.card_map_of_injective (conjParams_injective g)]
    exact hS
  have hM : M ≤ twistedFixedGroup TwistTag.E6 L Fr := by
    rintro _ ⟨a, ⟨ha1, ha⟩, rfl⟩
    exact twE6_conjParams_mem_fixed (K := K) (q := q) hFr hg hgP ω hn' hlang ha1 ha
  obtain ⟨m, hmM, hm1, hmC⟩ := twE6_frobFixed_exists_ne_one_mem (by omega) hK hσ hFr M hM hMcard
  obtain ⟨a, ⟨ha1, -⟩, rfl⟩ := hmM
  refine ⟨conjParams g a, hmC, fun b => conjParams_commute g a b, fun heq => hm1 ?_⟩
  have hη := conjParams_diagramMap_inv hgP ha1
  rw [hη] at heq
  have haa : a⁻¹ = a := conjParams_injective g heq
  have ha : a = 1 := funext fun i => units_sq_eq_one (L := L) (a i) (by
    rw [sq]; nth_rw 1 [← haa]; exact inv_mul_cancel (a i))
  rw [ha]
  exact map_one (conjParams g)

end CFSG.StandardType.E6GraphNoneSteps
