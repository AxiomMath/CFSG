module

public import CFSG.RankThree.PartOne.SEITZ8.D4Z
public import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4

variable {K : Type} [Field K]

section Ker

variable [CharP K 2] {σ : K →+* K}

@[expose] def Nker (σ : K →+* K) : Subgroup (twistedGroup σ) where
  carrier := {x | ∀ v : RootModule d4 K, ((x : adjointGroup d4 K) • v) - v ∈ Zsub K}
  mul_mem' := fun {x y} hx hy v => by
    have e : ((x * y : twistedGroup σ) : adjointGroup d4 K) • v - v =
        ((x : adjointGroup d4 K) • (((y : adjointGroup d4 K) • v) - v)) +
          (((x : adjointGroup d4 K) • v) - v) := by
      simp only [Subgroup.coe_mul, mul_smul, smul_sub]
      abel
    rw [e, adjointGroup_fix_Z _ (hy v)]
    exact (Zsub K).add_mem (hy v) (hx v)
  one_mem' := fun v => by
    simp only [OneMemClass.coe_one, one_smul, sub_self]
    exact (Zsub K).zero_mem
  inv_mem' := fun {x} hx v => by
    have e : ((x⁻¹ : twistedGroup σ) : adjointGroup d4 K) • v - v =
        ((x⁻¹ : twistedGroup σ) : adjointGroup d4 K) • (v - (x : adjointGroup d4 K) • v) := by
      rw [smul_sub, Subgroup.coe_inv, inv_smul_smul]
    have h1 : v - (x : adjointGroup d4 K) • v ∈ Zsub K := by
      have := (Zsub K).neg_mem (hx v)
      rwa [neg_sub] at this
    rw [e, adjointGroup_fix_Z _ h1]
    exact h1

theorem Nker_normal : (Nker σ).Normal where
  conj_mem := fun n hn g v => by
    have e : ((g * n * g⁻¹ : twistedGroup σ) : adjointGroup d4 K) • v - v =
        (g : adjointGroup d4 K) • (((n : adjointGroup d4 K) • (((g⁻¹ : twistedGroup σ) :
          adjointGroup d4 K) • v)) - ((g⁻¹ : twistedGroup σ) : adjointGroup d4 K) • v) := by
      rw [smul_sub, Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul, Subgroup.coe_inv,
        smul_inv_smul]
    rw [e, adjointGroup_fix_Z _ (hn _)]
    exact hn _

end Ker

section Simple

variable [CharP K 2] [Finite K]
  {σ : K →+* K} {q : ℕ}
  (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q)

omit [CharP K 2] in
include hq hK hσq in
theorem isSimple_twistedGroup : IsSimpleGroup (twistedGroup σ) := by
  have hQ := twistedGroup_isQuasisimple_of_card hq hK hσq
  have hZ := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card
    hq hK hσq
  have : IsSimpleGroup (twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)) := hQ.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

include hq hK hσq in
theorem eq_one_of_Z (a : twistedGroup σ) (ha : a ∈ Nker σ) : a = 1 := by
  have hs := isSimple_twistedGroup hq hK hσq
  have : (Nker σ).Normal := Nker_normal
  rcases hs.eq_bot_or_eq_top_of_normal (Nker σ) with h | h
  · rw [h] at ha
    exact Subgroup.mem_bot.1 ha
  · exfalso
    have hσ3 : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hK hσq
    have hx : (xe 2 1 : adjointGroup d4 K) ∈ twistedGroup σ :=
      twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj (isRoot_d4 (by norm_num : 2 < 24)))
        (xPar_mem_of_fixed hσ3 (isRoot_d4 (by norm_num : 2 < 24)) (by decide) (map_one σ))
    have hmem : (⟨xe 2 1, hx⟩ : twistedGroup σ) ∈ Nker σ := h ▸ Subgroup.mem_top _
    have h1 := hmem (rv 8)
    simp only at h1
    rw [xe2_smul_rv8] at h1
    have h2 := h1.1 (d4Root 2)
    have e : rv 8 + hVec d4 K (nd 2) + rv 2 - rv 8 = hVec d4 K (nd 2) + rv 2 := by abel
    rw [e, coordAt_add, coordAt_hVec, zero_add, rv, coordAt_rootVec_self (isRoot_d4 (by norm_num))]
      at h2
    exact one_ne_zero h2

include hq hK hσq in
theorem eq_of_ratMod (δ : K →+* K) {k : Subfield K} (hk : ∀ c ∈ k, δ c = c)
    (g g' : twistedGroup σ)
    (hg' : ∀ b : Label d4, (g' : adjointGroup d4 K) • (Finsupp.single b (1 : K) :
      RootModule d4 K) = Finsupp.mapRange δ δ.map_zero ((g : adjointGroup d4 K) •
        (Finsupp.single b (1 : K) : RootModule d4 K)))
    (hrat : ∀ b : Label d4, RatMod k ((g : adjointGroup d4 K) •
      (Finsupp.single b (1 : K) : RootModule d4 K))) : g' = g := by
  have hbasis : ∀ b : Label d4, (((g⁻¹ * g' : twistedGroup σ) : adjointGroup d4 K) •
      (Finsupp.single b (1 : K) : RootModule d4 K)) - Finsupp.single b (1 : K) ∈ Zsub K := by
    intro b
    set y : RootModule d4 K := (g : adjointGroup d4 K) • (Finsupp.single b (1 : K) :
      RootModule d4 K) with hy
    have e1 : (Finsupp.single b (1 : K) : RootModule d4 K) =
        ((g⁻¹ : twistedGroup σ) : adjointGroup d4 K) • y := by
      rw [hy, Subgroup.coe_inv, inv_smul_smul]
    have e2 : ((g⁻¹ * g' : twistedGroup σ) : adjointGroup d4 K) •
        (Finsupp.single b (1 : K) : RootModule d4 K) =
          ((g⁻¹ : twistedGroup σ) : adjointGroup d4 K) • Finsupp.mapRange δ δ.map_zero y := by
      rw [Subgroup.coe_mul, mul_smul, hg' b]
    have hz := mapRange_sub_mem_Z δ hk (hrat b)
    have e3 : ((g⁻¹ * g' : twistedGroup σ) : adjointGroup d4 K) •
        (Finsupp.single b (1 : K) : RootModule d4 K) - Finsupp.single b (1 : K) =
          ((g⁻¹ : twistedGroup σ) : adjointGroup d4 K) •
            (Finsupp.mapRange δ δ.map_zero y - y) := by
      rw [e2, smul_sub, ← e1]
    rw [e3, adjointGroup_fix_Z _ hz]
    exact hz
  have hall : ∀ v : RootModule d4 K, ((g⁻¹ * g' : twistedGroup σ) : adjointGroup d4 K) • v - v ∈
      Zsub K := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero =>
      simp only [smul_zero, sub_zero]
      exact (Zsub K).zero_mem
    | add x y hx hy =>
      have e : ((g⁻¹ * g' : twistedGroup σ) : adjointGroup d4 K) • (x + y) - (x + y) =
          (((g⁻¹ * g' : twistedGroup σ) : adjointGroup d4 K) • x - x) +
            (((g⁻¹ * g' : twistedGroup σ) : adjointGroup d4 K) • y - y) := by
        rw [smul_add]
        abel
      rw [e]
      exact (Zsub K).add_mem hx hy
    | single b r =>
      have e : ((g⁻¹ * g' : twistedGroup σ) : adjointGroup d4 K) • (Finsupp.single b r :
          RootModule d4 K) - Finsupp.single b r =
          r • (((g⁻¹ * g' : twistedGroup σ) : adjointGroup d4 K) •
            (Finsupp.single b (1 : K) : RootModule d4 K) - Finsupp.single b (1 : K)) := by
        have h1 : (Finsupp.single b r : RootModule d4 K) = r • Finsupp.single b (1 : K) := by
          simp
        rw [h1, smul_smul_comm', smul_sub]
      rw [e]
      exact (Zsub K).smul_mem r (hbasis b)
  have := eq_one_of_Z hq hK hσq (g⁻¹ * g') hall
  exact (inv_mul_eq_one.1 this).symm

end Simple

end CFSG.RankThree.PartOne.SEITZ8
