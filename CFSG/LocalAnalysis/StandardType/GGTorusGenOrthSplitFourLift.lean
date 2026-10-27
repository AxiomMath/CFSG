module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthSplitFourFactors
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthPieces

public section

namespace CFSG.StandardType.OrthTorusGen

open Module Multiplicative QuadraticMap Polynomial
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LayerCores CFSG.StandardType.LayerFacts
open CFSG.StandardType.SevOm

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] [CharP K 2] in
theorem exists_lift_of_mem_orthDerived {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {t : fixedSpace x ≃ₗ[K] fixedSpace x}
    (ht : t ∈ orthDerived (Q.comp (fixedSpace x).subtype)) :
    ∃ (g : V ≃ₗ[K] V) (hg : g ∈ supportedBlock Q x (X - 1)),
      fixRho hx ⟨g, hg⟩ = t ∧ g ∈ orthDerived Q := by
  have htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) :=
    orthDerived_le_orthogonalGroup ht
  rw [← range_fixRho hx] at htO
  obtain ⟨g, rfl⟩ := htO
  refine ⟨g.1, g.2, rfl, ?_⟩
  have ht' : restrictFixed Q x g ∈ orthDerived (Q.comp (fixedSpace x).subtype) := ht
  exact hx.supportedFixedDerived_le_orthDerived (mem_supportedFixedDerived.mpr ⟨g.2, ht'⟩)

omit [Finite K] in
theorem frameDelta_mem_supportedBlock (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (s : Multiplicative (Fin r → ZMod p)) {k : Fin r} (hk : toAdd s k = 0) :
    F.ι (frameDelta k) ∈ supportedBlock Q (F.ι s) (X - 1) := by
  have hzE : ∀ c ∈ E, F.ι (frameDelta k) * c = c * F.ι (frameDelta k) := by
    intro c hc
    obtain ⟨s', rfl⟩ := F.exists_eq hc
    rw [← map_mul, ← map_mul]
    exact congrArg F.ι (mul_comm _ _)
  refine mem_supportedBlock_of_vanishes hQ hp hp2 hEΩ F s hk
    (hEΩ (F.mem (frameDelta k))) hzE fun v hv => ?_
  exact (F.fix (frameDelta k) v).mpr fun j hj u hu => by
    have hjk : j = k := by
      by_contra hne
      exact hj (by rw [toAdd_ofAdd]; exact Pi.single_eq_of_ne hne 1)
    exact hv u (hjk ▸ hu)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem frame_apply_eq_pow_of_mem_fixedSpace [NeZero p] (F : SevOm.Frame Q p E r)
    {s : Multiplicative (Fin r → ZMod p)} {k : Fin r} (hothers : ∀ j, j ≠ k → toAdd s j ≠ 0)
    (t : Multiplicative (Fin r → ZMod p)) {w : V} (hw : w ∈ fixedSpace (F.ι s)) :
    F.ι t w = (F.ι (frameDelta k) ^ (toAdd t k).val) w := by
  set m := (toAdd t k).val with hm
  set t' := t * (frameDelta k ^ m)⁻¹ with ht'
  have htk : toAdd t' k = 0 := by
    rw [ht', toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply,
      Pi.smul_apply, Pi.single_eq_same, hm, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val,
      add_neg_cancel]
  have h1 : F.ι t = F.ι (frameDelta k) ^ m * F.ι t' := by
    have hcomm : Commute (F.ι (frameDelta k)) (F.ι t) :=
      Commute.map (mul_comm (frameDelta k) t) F.ι
    rw [ht', map_mul, map_inv, map_pow, ← mul_assoc, (hcomm.pow_left m).eq, mul_assoc,
      mul_inv_cancel, mul_one]
  have h2 : F.ι t' w = w := by
    rw [F.fix t' w]
    intro j hj u hu
    have hjk : j ≠ k := fun h => hj (h ▸ htk)
    exact (F.fix s w).mp (mem_fixedSpace.mp hw) j (hothers j hjk) u hu
  rw [h1, LinearEquiv.mul_apply, h2]

omit [Finite K] [CharP K 2] in
theorem exists_eq_pow_of_mem_supportedBlock [NeZero p] (F : SevOm.Frame Q p E r)
    {s : Multiplicative (Fin r → ZMod p)} (hx : OddOrderIsometry Q p (F.ι s)) {k : Fin r}
    (hothers : ∀ j, j ≠ k → toAdd s j ≠ 0)
    (hτ : F.ι (frameDelta k) ∈ supportedBlock Q (F.ι s) (X - 1))
    {c : V ≃ₗ[K] V} (hc : c ∈ E) (hcX : c ∈ supportedBlock Q (F.ι s) (X - 1)) :
    ∃ m : ℕ, c = F.ι (frameDelta k) ^ m := by
  obtain ⟨t, rfl⟩ := F.exists_eq hc
  refine ⟨(toAdd t k).val, ?_⟩
  have hpow : F.ι (frameDelta k) ^ (toAdd t k).val ∈ supportedBlock Q (F.ι s) (X - 1) :=
    Subgroup.pow_mem (supportedBlock Q (F.ι s) (X - 1)) hτ _
  have heq : fixRho hx ⟨F.ι t, hcX⟩ =
      fixRho hx ⟨F.ι (frameDelta k) ^ (toAdd t k).val, hpow⟩ := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [coe_fixRho, coe_fixRho]
    exact frame_apply_eq_pow_of_mem_fixedSpace F hothers t w.2
  exact congrArg Subtype.val (fixRho_injective hx heq)

omit [Finite K] [CharP K 2] in
theorem commute_frame_of_commute_fixRho [NeZero p] (hEΩ : E ≤ orthDerived Q)
    (F : SevOm.Frame Q p E r) {s : Multiplicative (Fin r → ZMod p)}
    (hx : OddOrderIsometry Q p (F.ι s)) {k : Fin r} (hothers : ∀ j, j ≠ k → toAdd s j ≠ 0)
    (hτ : F.ι (frameDelta k) ∈ supportedBlock Q (F.ι s) (X - 1))
    {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q (F.ι s) (X - 1))
    (hgτ : fixRho hx ⟨g, hg⟩ * fixRho hx ⟨F.ι (frameDelta k), hτ⟩ =
      fixRho hx ⟨F.ι (frameDelta k), hτ⟩ * fixRho hx ⟨g, hg⟩) :
    ∀ c ∈ E, g * c = c * g := by
  intro c hc
  obtain ⟨t, rfl⟩ := F.exists_eq hc
  have hcX : F.ι t ∈ isometryCentralizer Q (F.ι s) :=
    Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup (hEΩ hc),
      Subgroup.mem_centralizer_singleton_iff.mpr (by
        rw [← map_mul, ← map_mul]
        exact congrArg F.ι (mul_comm t s))⟩
  have hres : resFix (F.ι s) ⟨F.ι t, (Subgroup.mem_inf.mp hcX).2⟩ =
      fixRho hx ⟨F.ι (frameDelta k), hτ⟩ ^ (toAdd t k).val := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [coe_resFix, ← map_pow, coe_fixRho, Subgroup.coe_pow]
    exact frame_apply_eq_pow_of_mem_fixedSpace F hothers t w.2
  have hconj := fixRho_conj hx hcX ⟨g, hg⟩
  rw [hres] at hconj
  have hcomm : Commute (fixRho hx ⟨g, hg⟩) (fixRho hx ⟨F.ι (frameDelta k), hτ⟩) := hgτ
  have hcancel : fixRho hx ⟨F.ι (frameDelta k), hτ⟩ ^ (toAdd t k).val *
      fixRho hx ⟨g, hg⟩ *
      (fixRho hx ⟨F.ι (frameDelta k), hτ⟩ ^ (toAdd t k).val)⁻¹ = fixRho hx ⟨g, hg⟩ := by
    rw [← (hcomm.pow_right (toAdd t k).val).eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [hcancel] at hconj
  have hEq : F.ι t * g * (F.ι t)⁻¹ = g :=
    congrArg Subtype.val (fixRho_injective hx hconj)
  have h2 : F.ι t * g = g * F.ι t := by
    have h3 := congrArg (· * F.ι t) hEq
    simpa [mul_assoc] using h3
  exact h2.symm

omit [Finite K] [CharP K 2] in
theorem mem_zpowers_of_commute_fixRho [NeZero p] (hEΩ : E ≤ orthDerived Q)
    (F : SevOm.Frame Q p E r)
    (hmax : ∀ g ∈ orthDerived Q, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E)
    {s : Multiplicative (Fin r → ZMod p)} (hx : OddOrderIsometry Q p (F.ι s)) {k : Fin r}
    (hothers : ∀ j, j ≠ k → toAdd s j ≠ 0)
    (hτ : F.ι (frameDelta k) ∈ supportedBlock Q (F.ι s) (X - 1))
    {h : fixedSpace (F.ι s) ≃ₗ[K] fixedSpace (F.ι s)}
    (hD : h ∈ orthDerived (Q.comp (fixedSpace (F.ι s)).subtype))
    (hhτ : h * fixRho hx ⟨F.ι (frameDelta k), hτ⟩ = fixRho hx ⟨F.ι (frameDelta k), hτ⟩ * h)
    (hhp : h ^ p = 1) :
    h ∈ Subgroup.zpowers (fixRho hx ⟨F.ι (frameDelta k), hτ⟩) := by
  obtain ⟨g, hg, hfix, hgO⟩ := exists_lift_of_mem_orthDerived hx hD
  have hgcomm : ∀ c ∈ E, g * c = c * g :=
    commute_frame_of_commute_fixRho hEΩ F hx hothers hτ hg (by rw [hfix]; exact hhτ)
  have hgp : g ^ p = 1 := by
    have h1 : fixRho hx (⟨g, hg⟩ ^ p) = 1 := by
      rw [map_pow, hfix, hhp]
    have h2 : (⟨g, hg⟩ : ↥(supportedBlock Q (F.ι s) (X - 1))) ^ p = 1 :=
      fixRho_injective hx h1
    simpa using congrArg Subtype.val h2
  have hgE : g ∈ E := hmax g hgO hgcomm hgp
  obtain ⟨m, hm⟩ := exists_eq_pow_of_mem_supportedBlock F hx hothers hτ hgE hg
  have hsub : (⟨g, hg⟩ : ↥(supportedBlock Q (F.ι s) (X - 1))) =
      ⟨F.ι (frameDelta k), hτ⟩ ^ m := by
    refine Subtype.ext ?_
    simpa only [Subgroup.coe_pow, Subtype.coe_mk] using hm
  have hh : h = fixRho hx ⟨F.ι (frameDelta k), hτ⟩ ^ m := by
    rw [← hfix, hsub, map_pow]
  exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by rw [zpow_natCast, ← hh]⟩

end CFSG.StandardType.OrthTorusGen
