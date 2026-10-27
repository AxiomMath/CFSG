module


public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel

namespace CFSG
end CFSG
open CFSG

/-!
# Action lemmas for the proper step of Proposition 8.4

The key source argument identifies the regular `S₀`-set with `S₀` itself and
then takes `Y`-fixed points.  The lemmas below state that argument directly in
terms of actions, without choosing such an identification.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u v

/-- If `S` acts regularly on `A` and `Y` normalizes `S`, then the elements of
`S` centralizing `Y` act regularly on the `Y`-fixed part of `A`.

The existence proof conjugates the unique transporter by each `y ∈ Y`;
uniqueness forces the transporter to commute with `y`. -/
public theorem isRegularOn_inf_centralizer_fixedPoints
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    (S Y : Subgroup X) (A : Set Omega)
    (hreg : IsRegularOn S A)
    (hnorm : Y ≤ Subgroup.normalizer (S : Set X)) :
    IsRegularOn (S ⊓ Subgroup.centralizer (Y : Set X))
      {omega : Omega |
        omega ∈ A ∧ omega ∈ fixedPointsOfSubgroup X Omega Y} := by
  intro alpha beta halpha hbeta
  obtain ⟨s, hs, hsuniq⟩ := hreg halpha.1 hbeta.1
  have hsC : (s : X) ∈ Subgroup.centralizer (Y : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hyY
    have hyNorm : y ∈ Subgroup.normalizer (S : Set X) := hnorm hyY
    have hconjS : y * (s : X) * y⁻¹ ∈ S :=
      ((Subgroup.mem_normalizer_iff.mp hyNorm) (s : X)).mp s.property
    let sy : S := ⟨y * (s : X) * y⁻¹, hconjS⟩
    have hyAlpha : y • alpha = alpha := halpha.2 y hyY
    have hyBeta : y • beta = beta := hbeta.2 y hyY
    have hyInvAlpha : y⁻¹ • alpha = alpha := by
      calc
        y⁻¹ • alpha = y⁻¹ • (y • alpha) := by rw [hyAlpha]
        _ = alpha := by simp
    have hsy : (sy : X) • alpha = beta := by
      dsimp [sy]
      rw [mul_smul, mul_smul, hyInvAlpha, hs, hyBeta]
    have hsyEq : sy = s := hsuniq sy hsy
    have hconjEq : y * (s : X) * y⁻¹ = (s : X) :=
      congrArg Subtype.val hsyEq
    have hmul := congrArg (fun z : X => z * y) hconjEq
    simpa [mul_assoc] using hmul
  let sc : ↥(S ⊓ Subgroup.centralizer (Y : Set X)) :=
    ⟨(s : X), s.property, hsC⟩
  refine ⟨sc, hs, ?_⟩
  intro g hg
  apply Subtype.ext
  exact congrArg (fun z : S => (z : X))
    (hsuniq ⟨(g : X), g.property.1⟩ hg)

/-- Specialization of
`isRegularOn_inf_centralizer_fixedPoints` to nested fixed-point sets. -/
public theorem isRegularOn_inf_centralizer_fixedPoints_of_le
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    (S Y₀ Y : Subgroup X) (alpha : Omega)
    (hY₀Y : Y₀ ≤ Y)
    (hreg : IsRegularOn S
      {omega : Omega |
        omega ∈ fixedPointsOfSubgroup X Omega Y₀ ∧ omega ≠ alpha})
    (hnorm : Y ≤ Subgroup.normalizer (S : Set X)) :
    IsRegularOn (S ⊓ Subgroup.centralizer (Y : Set X))
      {omega : Omega |
        omega ∈ fixedPointsOfSubgroup X Omega Y ∧ omega ≠ alpha} := by
  have h := isRegularOn_inf_centralizer_fixedPoints S Y
    {omega : Omega |
      omega ∈ fixedPointsOfSubgroup X Omega Y₀ ∧ omega ≠ alpha}
    hreg hnorm
  apply (show
    {omega : Omega |
        (omega ∈ fixedPointsOfSubgroup X Omega Y₀ ∧ omega ≠ alpha) ∧
          omega ∈ fixedPointsOfSubgroup X Omega Y} =
      {omega : Omega |
        omega ∈ fixedPointsOfSubgroup X Omega Y ∧ omega ≠ alpha} by
      ext omega
      constructor
      · rintro ⟨⟨_hY₀, hne⟩, hY⟩
        exact ⟨hY, hne⟩
      · rintro ⟨hY, hne⟩
        refine ⟨⟨?_, hne⟩, hY⟩
        intro y hyY₀
        exact hY y (hY₀Y hyY₀)).symm ▸ h

/-- An element centralizing `Y` preserves the `Y`-fixed points of every
`X`-set. -/
public theorem smul_mem_fixedPointsOfSubgroup_of_mem_centralizer
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    {Y : Subgroup X} {f : X} {omega : Omega}
    (hf : f ∈ Subgroup.centralizer (Y : Set X))
    (homega : omega ∈ fixedPointsOfSubgroup X Omega Y) :
    f • omega ∈ fixedPointsOfSubgroup X Omega Y := by
  intro y hyY
  have hcomm : y * f = f * y :=
    (Subgroup.mem_centralizer_iff.mp hf) y hyY
  calc
    y • (f • omega) = (y * f) • omega := by rw [mul_smul]
    _ = (f * y) • omega := by rw [hcomm]
    _ = f • (y • omega) := by rw [mul_smul]
    _ = f • omega := by rw [homega y hyY]

/-- A regular subgroup of a base-point stabilizer, together with one element
moving the base point into its regular orbit, generates enough motion for
double transitivity. -/
public theorem isTwoTransitiveOn_of_regularOn_compl_singleton
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    (F S : Subgroup X) (A : Set Omega) (alpha beta : Omega) (t : X)
    (hSF : S ≤ F)
    (hSfix : S ≤ MulAction.stabilizer X alpha)
    (hstable : ∀ (f : F) ⦃omega : Omega⦄,
      omega ∈ A → (f : X) • omega ∈ A)
    (halpha : alpha ∈ A) (hbeta : beta ∈ A) (hbetaNe : beta ≠ alpha)
    (hreg : IsRegularOn S {omega : Omega | omega ∈ A ∧ omega ≠ alpha})
    (htF : t ∈ F) (htalpha : t • alpha = beta) :
    IsTwoTransitiveOn F A := by
  have hfromBase : ∀ ⦃gamma : Omega⦄, gamma ∈ A →
      ∃ f : F, (f : X) • alpha = gamma := by
    intro gamma hgamma
    by_cases hgammaAlpha : gamma = alpha
    · refine ⟨1, ?_⟩
      simpa [hgammaAlpha]
    · obtain ⟨s, hs, _hsuniq⟩ :=
        hreg ⟨hbeta, hbetaNe⟩ ⟨hgamma, hgammaAlpha⟩
      let f : F := ⟨(s : X) * t, F.mul_mem (hSF s.property) htF⟩
      refine ⟨f, ?_⟩
      change ((s : X) * t) • alpha = gamma
      rw [mul_smul, htalpha, hs]
  have htrans : IsTransitiveOn F A := by
    intro a b ha hb
    obtain ⟨fa, hfa⟩ := hfromBase ha
    obtain ⟨fb, hfb⟩ := hfromBase hb
    let f : F := fb * fa⁻¹
    refine ⟨f, ?_⟩
    change ((fb : X) * (fa : X)⁻¹) • a = b
    rw [mul_smul, ← hfa]
    simp [hfb]
  intro a b c d ha hb hc hd hab hcd
  obtain ⟨p, hpa⟩ := htrans ha halpha
  obtain ⟨q, hqc⟩ := htrans hc halpha
  have hpbA : (p : X) • b ∈ A := hstable p hb
  have hqdA : (q : X) • d ∈ A := hstable q hd
  have hpbNe : (p : X) • b ≠ alpha := by
    intro hpb
    apply hab
    exact MulAction.injective (p : X) (hpa.trans hpb.symm)
  have hqdNe : (q : X) • d ≠ alpha := by
    intro hqd
    apply hcd
    exact MulAction.injective (q : X) (hqc.trans hqd.symm)
  obtain ⟨s, hs, _hsuniq⟩ :=
    hreg ⟨hpbA, hpbNe⟩ ⟨hqdA, hqdNe⟩
  let f : F := q⁻¹ * ⟨(s : X), hSF s.property⟩ * p
  refine ⟨f, ?_, ?_⟩
  · change (((q : X)⁻¹ * (s : X)) * (p : X)) • a = c
    rw [mul_smul, mul_smul, hpa]
    have hsAlpha : (s : X) • alpha = alpha :=
      MulAction.mem_stabilizer_iff.mp (hSfix s.property)
    rw [hsAlpha, ← hqc]
    simp
  · change (((q : X)⁻¹ * (s : X)) * (p : X)) • b = d
    rw [mul_smul, mul_smul, hs]
    simp

/-- Regularity of `S` on the nonbase points gives the standard factorization
of the point stabilizer by `S` and the two-point stabilizer. -/
public theorem pointStabilizer_eq_mul_twoPointStabilizer_of_regularOn
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    (F S : Subgroup X) (A : Set Omega) (alpha beta : Omega)
    (hSF : S ≤ F)
    (hSfix : S ≤ MulAction.stabilizer X alpha)
    (hstable : ∀ (f : F) ⦃omega : Omega⦄,
      omega ∈ A → (f : X) • omega ∈ A)
    (hbeta : beta ∈ A) (hbetaNe : beta ≠ alpha)
    (hreg : IsRegularOn S {omega : Omega | omega ∈ A ∧ omega ≠ alpha}) :
    ((F ⊓ MulAction.stabilizer X alpha : Subgroup X) : Set X) =
      (S : Set X) *
        ((F ⊓ MulAction.stabilizer X alpha ⊓
          MulAction.stabilizer X beta : Subgroup X) : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    let xf : F := ⟨x, hx.1⟩
    have hxbetaA : x • beta ∈ A := hstable xf hbeta
    have hxbetaNe : x • beta ≠ alpha := by
      intro heq
      apply hbetaNe
      have hxalpha : x • alpha = alpha :=
        MulAction.mem_stabilizer_iff.mp hx.2
      exact MulAction.injective x (heq.trans hxalpha.symm)
    obtain ⟨s, hs, _hsuniq⟩ :=
      hreg ⟨hbeta, hbetaNe⟩ ⟨hxbetaA, hxbetaNe⟩
    let b : X := (s : X)⁻¹ * x
    have hbF : b ∈ F := F.mul_mem (F.inv_mem (hSF s.property)) hx.1
    have hbAlpha : b ∈ MulAction.stabilizer X alpha := by
      apply MulAction.mem_stabilizer_iff.mpr
      dsimp [b]
      have hsalpha : (s : X) • alpha = alpha :=
        MulAction.mem_stabilizer_iff.mp (hSfix s.property)
      calc
        ((s : X)⁻¹ * x) • alpha =
            (s : X)⁻¹ • (x • alpha) := by rw [mul_smul]
        _ = (s : X)⁻¹ • alpha := by
          rw [MulAction.mem_stabilizer_iff.mp hx.2]
        _ = (s : X)⁻¹ • ((s : X) • alpha) := by rw [hsalpha]
        _ = alpha := by simp
    have hbBeta : b ∈ MulAction.stabilizer X beta := by
      apply MulAction.mem_stabilizer_iff.mpr
      dsimp [b]
      rw [mul_smul, ← hs]
      simp
    rw [Set.mem_mul]
    refine ⟨(s : X), s.property, b, ⟨⟨hbF, hbAlpha⟩, hbBeta⟩, ?_⟩
    simp [b]
  · intro x hx
    rw [Set.mem_mul] at hx
    rcases hx with ⟨s, hsS, b, hb, rfl⟩
    exact ⟨F.mul_mem (hSF hsS) hb.1.1,
      (MulAction.stabilizer X alpha).mul_mem (hSfix hsS) hb.1.2⟩

/-- A normalizer preserves the fixed-point set of the subgroup it
normalizes. -/
public theorem smul_mem_fixedPointsOfSubgroup_of_mem_normalizer
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    {Y : Subgroup X} {n : X} {omega : Omega}
    (hn : n ∈ Subgroup.normalizer (Y : Set X))
    (homega : omega ∈ fixedPointsOfSubgroup X Omega Y) :
    n • omega ∈ fixedPointsOfSubgroup X Omega Y := by
  intro y hyY
  have hy' : n⁻¹ * y * n ∈ Y :=
    ((Subgroup.mem_normalizer_iff''.mp hn) y).mp hyY
  calc
    y • (n • omega) = n • ((n⁻¹ * y * n) • omega) := by
      simp [smul_smul, mul_assoc]
    _ = n • omega := by rw [homega _ hy']

/-- Two-transitivity of a centralizing subgroup factors the full normalizer
through the two-point stabilizer. -/
public theorem normalizer_eq_mul_normalizerIn_of_twoTransitiveOn
    {X : Type u} [Group X]
    (M Y F : Subgroup X) {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (hYD : Y ≤ M ⊓ rightConjugate M t)
    (hFC : F ≤ Subgroup.centralizer (Y : Set X))
    (htwo : IsTwoTransitiveOn F
      (fixedPointsOfSubgroup X (conjugateCosetSpace M) Y)) :
    ((Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X) =
      (F : Set X) *
        (normalizerIn (M ⊓ rightConjugate M t) Y : Set X) := by
  let N : Subgroup X := Subgroup.normalizer (Y : Set X)
  let D : Subgroup X := M ⊓ rightConjugate M t
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hYM : Y ≤ M := hYD.trans inf_le_left
  have halpha : alpha ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) Y :=
    theorem4b_baseCoset_mem_fixedPoints hYM
  have hbeta : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) Y := by
    intro y hyY
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact (hYD hyY).2
  have halphaBeta : alpha ≠ beta := by
    intro h
    apply htM
    simpa [alpha, beta] using QuotientGroup.eq.mp h
  have hFleN : F ≤ N :=
    hFC.trans (centralizer_le_normalizer Y)
  have htwoPoint :
      N ⊓ MulAction.stabilizer X alpha ⊓
          MulAction.stabilizer X beta = normalizerIn D Y := by
    rw [show MulAction.stabilizer X alpha = M by
      simpa [alpha] using baseCoset_stabilizer M]
    rw [show MulAction.stabilizer X beta = rightConjugate M t by
      simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t]
    ext x
    change ((x ∈ N ∧ x ∈ M) ∧ x ∈ rightConjugate M t) ↔
      ((x ∈ M ∧ x ∈ rightConjugate M t) ∧ x ∈ N)
    constructor
    · rintro ⟨⟨hxN, hxM⟩, hxt⟩
      exact ⟨⟨hxM, hxt⟩, hxN⟩
    · rintro ⟨⟨hxM, hxt⟩, hxN⟩
      exact ⟨⟨hxN, hxM⟩, hxt⟩
  apply Set.Subset.antisymm
  · intro n hnN
    have hnAlpha : n • alpha ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M) Y :=
      smul_mem_fixedPointsOfSubgroup_of_mem_normalizer hnN halpha
    have hnBeta : n • beta ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M) Y :=
      smul_mem_fixedPointsOfSubgroup_of_mem_normalizer hnN hbeta
    have hnNe : n • alpha ≠ n • beta := by
      intro h
      exact halphaBeta (MulAction.injective n h)
    obtain ⟨f, hfAlpha, hfBeta⟩ :=
      htwo halpha hbeta hnAlpha hnBeta halphaBeta hnNe
    let d : X := (f : X)⁻¹ * n
    have hdN : d ∈ N :=
      N.mul_mem (N.inv_mem (hFleN f.property)) hnN
    have hdAlpha : d ∈ MulAction.stabilizer X alpha := by
      apply MulAction.mem_stabilizer_iff.mpr
      dsimp [d]
      rw [mul_smul, ← hfAlpha]
      simp
    have hdBeta : d ∈ MulAction.stabilizer X beta := by
      apply MulAction.mem_stabilizer_iff.mpr
      dsimp [d]
      rw [mul_smul, ← hfBeta]
      simp
    have hdD : d ∈ normalizerIn D Y := by
      rw [← htwoPoint]
      exact ⟨⟨hdN, hdAlpha⟩, hdBeta⟩
    rw [Set.mem_mul]
    refine ⟨(f : X), f.property, d, hdD, ?_⟩
    simp [d]
  · intro x hx
    rw [Set.mem_mul] at hx
    rcases hx with ⟨f, hfF, d, hdD, rfl⟩
    exact N.mul_mem (hFleN hfF) hdD.2

/-- Regularity on the nonbase fixed points factors the normalizer inside the
base stabilizer through the two-point stabilizer. -/
public theorem normalizerIn_eq_mul_normalizerIn_of_regularOn
    {X : Type u} [Group X]
    (M Y S : Subgroup X) {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (hYD : Y ≤ M ⊓ rightConjugate M t)
    (hSle : S ≤ normalizerIn M Y)
    (hreg : IsRegularOn S
      {omega : conjugateCosetSpace M |
        omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y ∧
          omega ≠ QuotientGroup.mk 1}) :
    (normalizerIn M Y : Set X) =
      (S : Set X) *
        (normalizerIn (M ⊓ rightConjugate M t) Y : Set X) := by
  let N : Subgroup X := Subgroup.normalizer (Y : Set X)
  let D : Subgroup X := M ⊓ rightConjugate M t
  let A : Set (conjugateCosetSpace M) :=
    fixedPointsOfSubgroup X (conjugateCosetSpace M) Y
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hSF : S ≤ N := fun _ hs => (hSle hs).2
  have hSfix : S ≤ MulAction.stabilizer X alpha := by
    intro s hs
    rw [show MulAction.stabilizer X alpha = M by
      simpa [alpha] using baseCoset_stabilizer M]
    exact (hSle hs).1
  have hstable : ∀ (n : N) ⦃omega : conjugateCosetSpace M⦄,
      omega ∈ A → (n : X) • omega ∈ A := by
    intro n omega homega
    exact smul_mem_fixedPointsOfSubgroup_of_mem_normalizer
      n.property homega
  have hbeta : beta ∈ A := by
    intro y hyY
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact (hYD hyY).2
  have hbetaNe : beta ≠ alpha := by
    intro h
    apply htM
    simpa [alpha, beta] using QuotientGroup.eq.mp h.symm
  have hfactor :=
    pointStabilizer_eq_mul_twoPointStabilizer_of_regularOn
      N S A alpha beta hSF hSfix hstable hbeta hbetaNe (by
        simpa [A, alpha] using hreg)
  have hpoint : N ⊓ MulAction.stabilizer X alpha = normalizerIn M Y := by
    rw [show MulAction.stabilizer X alpha = M by
      simpa [alpha] using baseCoset_stabilizer M]
    ext x
    change (x ∈ N ∧ x ∈ M) ↔ (x ∈ M ∧ x ∈ N)
    exact and_comm
  have htwoPoint :
      N ⊓ MulAction.stabilizer X alpha ⊓
          MulAction.stabilizer X beta = normalizerIn D Y := by
    rw [show MulAction.stabilizer X alpha = M by
      simpa [alpha] using baseCoset_stabilizer M]
    rw [show MulAction.stabilizer X beta = rightConjugate M t by
      simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t]
    ext x
    change ((x ∈ N ∧ x ∈ M) ∧ x ∈ rightConjugate M t) ↔
      ((x ∈ M ∧ x ∈ rightConjugate M t) ∧ x ∈ N)
    constructor
    · rintro ⟨⟨hxN, hxM⟩, hxt⟩
      exact ⟨⟨hxM, hxt⟩, hxN⟩
    · rintro ⟨⟨hxM, hxt⟩, hxN⟩
      exact ⟨⟨hxN, hxM⟩, hxt⟩
  rw [htwoPoint, hpoint] at hfactor
  exact hfactor

/-- Pull regularity back along a homomorphism whose restriction to the acting
subgroup is injective and has the prescribed image. -/
public theorem regularOn_compHom_of_subgroup_bijective
    {G : Type u} {Q : Type v} {Omega : Type*}
    [Group G] [Group Q] [MulAction Q Omega]
    (f : G →* Q) (S : Subgroup G) (R : Subgroup Q)
    (hmap : S.map f = R)
    (hinj : Function.Injective (f.comp S.subtype))
    {A : Set Omega} (hreg : IsRegularOn R A) :
    letI : MulAction G Omega := MulAction.compHom Omega f
    IsRegularOn S A := by
  letI : MulAction G Omega := MulAction.compHom Omega f
  intro a b ha hb
  obtain ⟨r, hr, huniq⟩ := hreg ha hb
  have hrmap : (r : Q) ∈ S.map f := by
    rw [hmap]
    exact r.property
  rcases Subgroup.mem_map.mp hrmap with ⟨s, hsS, hfs⟩
  let sS : S := ⟨s, hsS⟩
  refine ⟨sS, ?_, ?_⟩
  · change f s • a = b
    rw [hfs]
    exact hr
  · intro t ht
    have hftR : f (t : G) ∈ R := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem f t.property
    let tR : R := ⟨f (t : G), hftR⟩
    have htR : (tR : Q) • a = b := by
      change f (t : G) • a = b
      exact ht
    have htReq : tR = r := huniq tR htR
    apply hinj
    change f (t : G) = f (sS : G)
    calc
      f (t : G) = (tR : Q) := rfl
      _ = (r : Q) := congrArg Subtype.val htReq
      _ = f (sS : G) := hfs.symm

/-- Pull a regular action on non-base cosets back along a surjective group
homomorphism whose kernel lies in the source stabilizer. -/
public theorem coset_isRegularOn_of_surjective
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    (f : G →* Q) (_hf : Function.Surjective f)
    (B S : Subgroup G) (R : Subgroup Q)
    (hker : f.ker ≤ B)
    (hmap : S.map f = R)
    (hinj : Function.Injective (f.comp S.subtype))
    (hreg : IsRegularOn R
      {q : Q ⧸ B.map f | q ≠ QuotientGroup.mk 1}) :
    IsRegularOn S
      {q : G ⧸ B | q ≠ QuotientGroup.mk 1} := by
  let Omega := Q ⧸ B.map f
  letI : MulAction G Omega := MulAction.compHom Omega f
  have hregPull : IsRegularOn S
      {q : Omega | q ≠ QuotientGroup.mk 1} :=
    regularOn_compHom_of_subgroup_bijective f S R hmap hinj hreg
  have hstabilizer :
      MulAction.stabilizer G (QuotientGroup.mk 1 : Omega) = B := by
    calc
      MulAction.stabilizer G (QuotientGroup.mk 1 : Omega) =
          (MulAction.stabilizer Q
            (QuotientGroup.mk 1 : Omega)).comap f :=
        stabilizer_compHom f (QuotientGroup.mk 1 : Omega)
      _ = (B.map f).comap f := by
        rw [baseCoset_stabilizer (B.map f)]
      _ = B := Subgroup.comap_map_eq_self hker
  rw [← hstabilizer]
  exact regularOn_quotient_stabilizer S
    (QuotientGroup.mk 1 : Omega) hregPull

/-- Transport regularity from non-base stabilizer cosets to the corresponding
non-base points of the ambient orbit. -/
public theorem regularOn_orbit_of_coset
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    (F : Subgroup X) (alpha : Omega) (S : Subgroup F)
    (hreg : IsRegularOn S
      {q : F ⧸ pointStabilizerIn F alpha |
        q ≠ QuotientGroup.mk 1}) :
    IsRegularOn (S.map F.subtype)
      {omega : Omega |
        InOrbit F alpha omega ∧ omega ≠ alpha} := by
  letI : MulAction F Omega := MulAction.compHom Omega F.subtype
  intro a b ha hb
  rcases ha.1 with ⟨fa, hfa⟩
  rcases hb.1 with ⟨fb, hfb⟩
  let qa : F ⧸ MulAction.stabilizer F alpha := QuotientGroup.mk fa
  let qb : F ⧸ MulAction.stabilizer F alpha := QuotientGroup.mk fb
  have hqa : qa ≠ QuotientGroup.mk 1 := by
    intro hq
    apply ha.2
    have himage := congrArg
      (MulAction.ofQuotientStabilizer F alpha) hq
    calc
      a = (fa : X) • alpha := hfa.symm
      _ = alpha := by
        simpa [qa, MulAction.compHom_smul_def] using himage
  have hqb : qb ≠ QuotientGroup.mk 1 := by
    intro hq
    apply hb.2
    have himage := congrArg
      (MulAction.ofQuotientStabilizer F alpha) hq
    calc
      b = (fb : X) • alpha := hfb.symm
      _ = alpha := by
        simpa [qb, MulAction.compHom_smul_def] using himage
  obtain ⟨s, hs, huniq⟩ := hreg hqa hqb
  let sx : S.map F.subtype :=
    ⟨((s : S) : F), Subgroup.mem_map_of_mem F.subtype s.property⟩
  refine ⟨sx, ?_, ?_⟩
  · have himage :
        (s : S) • ((fa : F) • alpha) = (fb : F) • alpha := by
      have hsF : (s : F) • qa = qb := hs
      calc
        (s : S) • ((fa : F) • alpha) =
            MulAction.ofQuotientStabilizer F alpha (s • qa) :=
          (MulAction.ofQuotientStabilizer_smul F alpha s qa).symm
        _ = MulAction.ofQuotientStabilizer F alpha qb :=
          congrArg (MulAction.ofQuotientStabilizer F alpha) hsF
        _ = (fb : F) • alpha := by rfl
    change (((s : S) : F) : X) • a = b
    rw [← hfa, ← hfb]
    change ((s : S) : X) • ((fa : F) • alpha) = (fb : F) • alpha
    exact himage
  · intro z hz
    rcases Subgroup.mem_map.mp z.property with ⟨s0, hs0S, hs0z⟩
    let s0 : S := ⟨s0, hs0S⟩
    have hs0move : s0 • qa = qb := by
      change (s0 : F) • qa = qb
      apply MulAction.injective_ofQuotientStabilizer F alpha
      rw [MulAction.ofQuotientStabilizer_smul]
      change (s0 : F) • ((fa : F) • alpha) = (fb : F) • alpha
      change ((s0 : F) : X) • ((fa : F) : X) • alpha =
        ((fb : F) : X) • alpha
      rw [hfa, hfb]
      have hzval : (z : X) = ((s0 : F) : X) := by
        simpa using hs0z.symm
      rw [← hzval]
      exact hz
    have hs0eq : s0 = s := huniq s0 hs0move
    apply Subtype.ext
    calc
      (z : X) = ((s0 : F) : X) := by simpa using hs0z.symm
      _ = (((s : S) : F) : X) := by
        exact congrArg (fun r : S => (((r : S) : F) : X)) hs0eq
      _ = (sx : X) := rfl

end CFSG.BenderSuzuki
