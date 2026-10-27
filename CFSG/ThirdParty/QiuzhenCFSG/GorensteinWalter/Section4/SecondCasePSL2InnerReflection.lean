module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2OddInnerFixingKleinFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuotientCenterAutomorphism
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The projective-linear consumer for Section 4 equation (4)

The semilinear field-projection calculation is deliberately kept separate
from this file.  Here we consume its exact endpoint: every odd element of
`F` induces an inner automorphism on `E / Z(E)`.  The reflected torus then
fixes two distinct commuting involutions, so the inner representative is
trivial; perfectness lifts the quotient action to `E`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem action_pow_local
    {G : Type u} [Group G]
    {E M : Subgroup G} (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) (α : E ≃* E)
    (hα : ∀ x : E, α x =
      ⟨f * (x : G) * f⁻¹, hE.2 f hf (x : G) x.2⟩)
    (n : ℕ) (x : E) :
    (α ^ n) x =
      ⟨f ^ n * (x : G) * (f ^ n)⁻¹,
        hE.2 (f ^ n) (M.pow_mem hf n) (x : G) x.2⟩ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      change (α ^ n) (α x) = _
      rw [ih]
      rw [hα]
      apply Subtype.ext
      simp
      group

/-- If the induced actions of an odd subgroup on the component quotient are
inner, the reflected torus forces the subgroup to centralize the component. -/
public theorem secondCase_psl2_odd_subgroup_centralizes_component_of_inner_reflection
    {G : Type u} [Group G] [Finite G]
    (E M F : Subgroup G)
    (hEcomp : IsComponentOf E M)
    (hEnorm : IsNormalIn E M)
    (hFleM : F ≤ M)
    (hFodd : Odd (Nat.card F))
    (t s : E)
    (htI : IsInvolution (t : G)) (hsI : IsInvolution (s : G))
    (hts : t ≠ s) (htsComm : Commute (t : E) (s : E))
    (hZodd : Odd (Nat.card (Subgroup.center E)))
    (hFcentT : F ≤ Subgroup.centralizer ({(t : G)} : Set G))
    (hFcentS : F ≤ Subgroup.centralizer ({(s : G)} : Set G))
    (T : Subgroup (E ⧸ Subgroup.center E))
    (hTinv : ∀ x : E ⧸ Subgroup.center E, x ∈ T →
      QuotientGroup.mk' (Subgroup.center E) s * x *
        (QuotientGroup.mk' (Subgroup.center E) s)⁻¹ = x⁻¹)
    (hTcontain : ∀ X : Subgroup (E ⧸ Subgroup.center E),
      (∀ x : E ⧸ Subgroup.center E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (Subgroup.center E) t} :
            Set (E ⧸ Subgroup.center E)) → X ≤ T)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (eQ : Nonempty ((E ⧸ Subgroup.center E) ≃* PSL2 K))
    (hinner : ∀ f : G, (hf : f ∈ F) →
      ∃ α : E ≃* E,
        (∀ x : E, α x =
          ⟨f * (x : G) * f⁻¹,
            hEnorm.2 f (hFleM hf) (x : G) x.2⟩) ∧
        ∃ a : PSL2 K,
          MulAut.congr eQ.some
            (quotientCenterAutomorphism E α) = MulAut.conj a) :
    F ≤ Subgroup.centralizer (E : Set G) := by
  classical
  let : Group.IsPerfect E := (Group.isPerfect_def).2 hEcomp.2.2.2.1
  let q : E →* E ⧸ Subgroup.center E :=
    QuotientGroup.mk' (Subgroup.center E)
  intro f hfF
  have hfM : f ∈ M := hFleM hfF
  obtain ⟨α, hα, a, hαinner⟩ := hinner f hfF
  let φ : MulAut (PSL2 K) :=
    MulAut.congr eQ.some (quotientCenterAutomorphism E α)
  have hforder : Odd (orderOf f) := by
    exact Odd.of_dvd_nat hFodd (Subgroup.orderOf_dvd_natCard F hfF)
  have hfpow : f ^ orderOf f = 1 := pow_orderOf_eq_one f
  have hαpow : α ^ orderOf f = 1 := by
    apply MulEquiv.ext
    intro x
    have hx := action_pow_local f hfM hEnorm α hα (orderOf f) x
    apply Subtype.ext
    simpa [hfpow] using congrArg Subtype.val hx
  have hφpow : φ ^ orderOf f = 1 := by
    dsimp [φ]
    rw [← map_pow, ← map_pow, hαpow]
    apply MulEquiv.ext
    intro x
    simp
  have hφinner : φ = MulAut.conj a := hαinner
  have hαt : α t = t := by
    apply Subtype.ext
    rw [hα t]
    change f * (t : G) * f⁻¹ = (t : G)
    have hcomm :=
      Subgroup.mem_centralizer_singleton_iff.mp (hFcentT hfF)
    rw [hcomm]
    simp
  have hαs : α s = s := by
    apply Subtype.ext
    rw [hα s]
    change f * (s : G) * f⁻¹ = (s : G)
    have hcomm :=
      Subgroup.mem_centralizer_singleton_iff.mp (hFcentS hfF)
    rw [hcomm]
    simp
  have hφt : φ (eQ.some (q t)) = eQ.some (q t) := by
    dsimp [φ]
    rw [MulAut.congr_apply]
    simp
    rw [quotientCenterAutomorphism_apply_mk]
    rw [hαt]
  have hφs : φ (eQ.some (q s)) = eQ.some (q s) := by
    dsimp [φ]
    rw [MulAut.congr_apply]
    simp
    rw [quotientCenterAutomorphism_apply_mk]
    rw [hαs]
  have hqtI : IsInvolution (eQ.some (q t)) := by
    constructor
    · intro h
      have hq : q t = 1 := eQ.some.injective (by simpa using h)
      have htZ : (t : E) ∈ Subgroup.center E :=
        (QuotientGroup.eq_one_iff (N := Subgroup.center E) t).mp hq
      have ht2 : (t : E) ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using htI.2
      have htne : (t : E) ≠ 1 := by
        intro ht1
        apply htI.1
        exact congrArg Subtype.val ht1
      have hord2 : orderOf (t : E) = 2 :=
        orderOf_eq_prime (p := 2) ht2 htne
      have h2dvd : 2 ∣ Nat.card (Subgroup.center E) := by
        have hdvd : orderOf (t : E) ∣ Nat.card (Subgroup.center E) :=
          Subgroup.orderOf_dvd_natCard (Subgroup.center E) htZ
        simpa [hord2] using hdvd
      exact hZodd.not_two_dvd_nat h2dvd
    · have ht2 : (t : E) ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using htI.2
      have hq2 : (q t) ^ 2 = 1 := by
        rw [← map_pow, ht2]
        simp
      simpa using congrArg eQ.some hq2
  have hqsI : IsInvolution (eQ.some (q s)) := by
    constructor
    · intro h
      have hq : q s = 1 := eQ.some.injective (by simpa using h)
      have hsZ : (s : E) ∈ Subgroup.center E :=
        (QuotientGroup.eq_one_iff (N := Subgroup.center E) s).mp hq
      have hs2 : (s : E) ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using hsI.2
      have hsne : (s : E) ≠ 1 := by
        intro hs1
        apply hsI.1
        exact congrArg Subtype.val hs1
      have hord2 : orderOf (s : E) = 2 :=
        orderOf_eq_prime (p := 2) hs2 hsne
      have h2dvd : 2 ∣ Nat.card (Subgroup.center E) := by
        have hdvd : orderOf (s : E) ∣ Nat.card (Subgroup.center E) :=
          Subgroup.orderOf_dvd_natCard (Subgroup.center E) hsZ
        simpa [hord2] using hdvd
      exact hZodd.not_two_dvd_nat h2dvd
    · have hs2 : (s : E) ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using hsI.2
      have hq2 : (q s) ^ 2 = 1 := by
        rw [← map_pow, hs2]
        simp
      simpa using congrArg eQ.some hq2
  have hqts : eQ.some (q t) ≠ eQ.some (q s) := by
    intro h
    have hq : q t = q s := eQ.some.injective (by simpa using h)
    have hz : (t : E) * (s : E)⁻¹ ∈ Subgroup.center E := by
      have h := (QuotientGroup.eq_iff_div_mem.mp hq)
      rwa [div_eq_mul_inv] at h
    have htsc : Commute (t : E) ((s : E)⁻¹) := htsComm.inv_right
    have ht2 : (t : E) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using htI.2
    have hs2 : (s : E) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hsI.2
    have hs2' : ((s : E)⁻¹) ^ 2 = 1 := by
      rw [inv_pow, hs2]
      simp
    have hzsq : ((t : E) * (s : E)⁻¹) ^ 2 = 1 := by
      rw [htsc.mul_pow 2]
      rw [ht2, hs2']
      simp
    have hord2 : orderOf ((t : E) * (s : E)⁻¹) ∣ 2 :=
      (orderOf_dvd_iff_pow_eq_one (x := (t : E) * (s : E)⁻¹) (n := 2)).2 hzsq
    have hordZ : orderOf ((t : E) * (s : E)⁻¹) ∣
        Nat.card (Subgroup.center E) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center E) hz
    have hord1 : orderOf ((t : E) * (s : E)⁻¹) = 1 := by
      have hcop : Nat.Coprime 2 (Nat.card (Subgroup.center E)) :=
        Nat.coprime_two_left.mpr hZodd
      have hdvd : orderOf ((t : E) * (s : E)⁻¹) ∣ 1 := by
        simpa [hcop.gcd_eq_one] using (Nat.dvd_gcd hord2 hordZ)
      exact Nat.dvd_one.mp hdvd
    have hz1 : (t : E) * (s : E)⁻¹ = 1 :=
      (orderOf_eq_one_iff (x := (t : E) * (s : E)⁻¹)).1 hord1
    have hts' : (t : E) = (s : E) := by
      calc
        (t : E) = (t : E) * (s : E)⁻¹ * (s : E) := by group
        _ = (s : E) := by rw [hz1]; simp
    exact hts hts'
  have hqcomm : Commute (eQ.some (q t)) (eQ.some (q s)) := by
    change eQ.some (q t) * eQ.some (q s) = eQ.some (q s) * eQ.some (q t)
    calc
      eQ.some (q t) * eQ.some (q s) = eQ.some (q t * q s) :=
        (map_mul eQ.some (q t) (q s)).symm
      _ = eQ.some (q (t * s)) := congrArg eQ.some (map_mul q t s).symm
      _ = eQ.some (q (s * t)) := congrArg eQ.some (congrArg q htsComm)
      _ = eQ.some (q s * q t) := congrArg eQ.some (map_mul q s t)
      _ = eQ.some (q s) * eQ.some (q t) := map_mul eQ.some (q s) (q t)
  have hinnerEq : φ = 1 := by
    apply psl2_odd_inner_fixing_commuting_involutions_eq_one K hK φ
      (orderOf f) hforder hφpow (eQ.some (q t)) (eQ.some (q s))
      hqtI hqsI hqts hqcomm hφt hφs
    exact ⟨a, hφinner⟩
  have hqα : ∀ x : E, q (α x) = q x := by
    intro x
    have hx := congrArg
      (fun z : MulAut (PSL2 K) => z (eQ.some (q x))) hinnerEq
    have hx' : (quotientCenterAutomorphism E α) (q x) = q x := by
      have hw : eQ.some ((quotientCenterAutomorphism E α) (q x)) =
          eQ.some (q x) := by
        simpa [φ, MulAut.congr_apply] using hx
      exact eQ.some.injective hw
    rwa [quotientCenterAutomorphism_apply_mk] at hx'
  have hdelta : ∀ x : E, α x * x⁻¹ ∈ Subgroup.center E := by
    intro x
    apply (QuotientGroup.eq_one_iff (N := Subgroup.center E)
      (α x * x⁻¹)).mp
    change q (α x * x⁻¹) = 1
    rw [map_mul, hqα, map_inv]
    simp
  have hαeq : α = MulEquiv.refl E :=
    perfect_central_automorphism_eq inferInstance α (MulEquiv.refl E) hdelta
  intro x hxE
  have hxα := congrArg (fun ψ : E ≃* E => ψ ⟨x, hxE⟩) hαeq
  have hxα' : f * x * f⁻¹ = x := by
    have hval : (α ⟨x, hxE⟩ : G) = x := by
      have hsub : α ⟨x, hxE⟩ = ⟨x, hxE⟩ := by
        simpa using hxα
      exact congrArg Subtype.val hsub
    simpa [hα] using hval
  exact (mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hxα')).symm

end CFSG.GorensteinWalter
