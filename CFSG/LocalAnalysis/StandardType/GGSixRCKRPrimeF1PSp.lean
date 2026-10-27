module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepAPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

private theorem rckRPf1sp_odd_order {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n f : ℕ} (φ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X)
    (hφk : φ.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    {d : X} (hdp : d ^ p = 1)
    (s₀ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hs₀ : ∀ u, d⁻¹ * φ u * d = φ (s₀ * u * s₀⁻¹)) :
    Odd (orderOf (s₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) := by
  let F := GaloisField 2 f
  let s : GL (Fin n ⊕ Fin n) F := (s₀ : GL (Fin n ⊕ Fin n) F)
  change Odd (orderOf s)
  have hsP : s ∈ CFSG.Open.StatedSp n F := s₀.2
  have hsLift : IsGLLift (CFSG.Open.StatedSp n F).subtype φ s d :=
    fun u => ⟨s₀ * u * s₀⁻¹, rfl, hs₀ u⟩
  have hspow : IsGLLift (CFSG.Open.StatedSp n F).subtype φ (s ^ p) (d ^ p) :=
    hsLift.pow p
  have hspow1 : IsGLLift (CFSG.Open.StatedSp n F).subtype φ (s ^ p) 1 := by
    rwa [hdp] at hspow
  have hspowP : s ^ p ∈ CFSG.Open.StatedSp n F := Subgroup.pow_mem _ hsP p
  have hs_pow : s ^ p = 1 :=
    sASp_lift_unique n F φ hφk hspowP (Subgroup.one_mem _) hspow1
      (isGLLift_one (j := (CFSG.Open.StatedSp n F).subtype) (ψ := φ))
  have hdvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hs_pow
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  rcases hp.eq_one_or_self_of_dvd (orderOf s) hdvd with h | h
  · rw [h]
    exact odd_one
  · rw [h]
    exact hpodd

theorem rckF1_PSp
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K J : Subgroup X} {d : X}
    (hdp : d ^ p = 1) {n f : ℕ} (hf : 1 ≤ f) (φ : (ggU .PSp n f).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (hdN : d ∈ Subgroup.normalizer (K : Set X)) (hdID : GGPsiInnerDiag (ggU .PSp n f).D φ d)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) :
    ∃ s : GL (Fin n ⊕ Fin n) (GaloisField 2 f), s ∈ CFSG.Open.StatedSp n (GaloisField 2 f) ∧
      IsGLLift (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype φ s d ∧ Odd (orderOf s) ∧
      ∃ ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f),
        IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) ε ∧
        (∃ e, IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e ∧ e * ε = e ∧
          (e = ε ∨ (e ≠ ε ∧ formAdj (RingHom.id (GaloisField 2 f)) (Matrix.fromBlocks 0 1 (-1) 0 :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e ≠ e ∧
            ε = e + formAdj (RingHom.id (GaloisField 2 f)) (Matrix.fromBlocks 0 1 (-1) 0 :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e))) ∧
        ∃ J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f)),
          IsComponentOf J'
            ⁅glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε,
              glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε⁆ ∧
          J'.map φ = J := by
  let F := GaloisField 2 f
  have hφkU : φ.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp n F) := hφk
  have hdID' : GGPsiInnerDiag (Symplectic.rootDatum n F) φ d := hdID
  have hbN : d ∈ Subgroup.normalizer (φ.range : Set X) := by
    rw [hφr]
    exact hdN
  obtain ⟨s₀, hs₀⟩ := exists_conj_eq_PSp n F φ hφkU hbN hdID'
  let s : GL (Fin n ⊕ Fin n) F := (s₀ : GL (Fin n ⊕ Fin n) F)
  have hsP : s ∈ CFSG.Open.StatedSp n F := s₀.2
  have hsLift : IsGLLift (CFSG.Open.StatedSp n F).subtype φ s d :=
    fun u => ⟨s₀ * u * s₀⁻¹, rfl, hs₀ u⟩
  have hsodd : Odd (orderOf s) := rckRPf1sp_odd_order hp hp2 φ hφkU hdp s₀ hs₀
  let D : Subgroup X := Subgroup.zpowers d
  let P : GL (Fin n ⊕ Fin n) F → Prop := fun s' => s' ∈ Subgroup.zpowers s
  have hDcent : Subgroup.centralizer (D : Set X) =
      Subgroup.centralizer ({d} : Set X) := by
    change Subgroup.centralizer ((Subgroup.zpowers d : Set X)) = _
    rw [Subgroup.zpowers_eq_closure d]
    exact Subgroup.centralizer_closure ({d} : Set X)
  have hJ' : IsComponentOf J (φ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [hφr, hDcent]
    exact hJ
  have hpowD : ∀ x ∈ Subgroup.closure ({d} : Set X), x ^ p = 1 := by
    intro x hx
    rw [← Subgroup.zpowers_eq_closure d] at hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    calc (d ^ k) ^ p = (d ^ k) ^ (p : ℤ) := by rw [zpow_natCast]
      _ = d ^ (k * (p : ℤ)) := by rw [← zpow_mul]
      _ = d ^ ((p : ℤ) * k) := by rw [mul_comm]
      _ = (d ^ (p : ℤ)) ^ k := by rw [zpow_mul]
      _ = (d ^ p) ^ k := by rw [zpow_natCast]
      _ = 1 := by rw [hdp, one_zpow]
  have hlift : ∀ d' ∈ D, ∃ s' : GL (Fin n ⊕ Fin n) F,
      P s' ∧ IsGLLift (CFSG.Open.StatedSp n F).subtype φ s' d' := by
    intro d' hd'
    change d' ∈ Subgroup.zpowers d at hd'
    rw [Subgroup.zpowers_eq_closure d] at hd'
    induction hd' using Subgroup.closure_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨s, Subgroup.mem_zpowers s, hsLift⟩
    | one => exact ⟨1, Subgroup.one_mem _, isGLLift_one⟩
    | mul x y hx hy ihx ihy =>
        obtain ⟨sx, hsxP, hsxL⟩ := ihx
        obtain ⟨sy, hsyP, hsyL⟩ := ihy
        exact ⟨sy * sx, Subgroup.mul_mem _ hsyP hsxP, hsxL.mul hsyL⟩
    | inv x hx ihx =>
        obtain ⟨sx, hsxP, hsxL⟩ := ihx
        refine ⟨sx ^ (p - 1), Subgroup.pow_mem _ hsxP (p - 1), ?_⟩
        have hxpow : x ^ p = 1 := hpowD x hx
        have hxinv : x ^ (p - 1) = x⁻¹ := by
          have hmul : x * x ^ (p - 1) = 1 := by
            have h1p : 1 ≤ p := Nat.succ_le_of_lt hp.pos
            rw [← pow_succ', Nat.sub_add_cancel h1p, hxpow]
          exact eq_inv_of_mul_eq_one_right hmul
        have h := hsxL.pow (p - 1)
        rwa [hxinv] at h
  obtain ⟨J', hJ'comp, hJ'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift (j := (CFSG.Open.StatedSp n F).subtype)
      (hj := Subgroup.subtype_injective _) (ψ := φ) (hψ := hφkU) (P := P)
      (D := D) (J := J) hJ' hlift
  let Sset : Set (GL (Fin n ⊕ Fin n) F) :=
    {s' | P s' ∧ ∃ d' ∈ D, IsGLLift (CFSG.Open.StatedSp n F).subtype φ s' d'}
  have hcl : Subgroup.closure Sset = Subgroup.zpowers s := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
    · rw [Subgroup.zpowers_eq_closure, Subgroup.closure_le, Set.singleton_subset_iff]
      exact Subgroup.subset_closure
        ⟨Subgroup.mem_zpowers s, d, Subgroup.mem_zpowers d, hsLift⟩
  have hcent : Subgroup.centralizer Sset =
      Subgroup.centralizer ({s} : Set (GL (Fin n ⊕ Fin n) F)) := by
    rw [← Subgroup.centralizer_closure Sset, hcl, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
  have hJ'compS : IsComponentOf J' ((Subgroup.centralizer Sset).comap
      (CFSG.Open.StatedSp n F).subtype) := hJ'comp
  have hJ'comp' : IsComponentOf J'
      ((Subgroup.centralizer ({s} : Set (GL (Fin n ⊕ Fin n) F))).comap
        (CFSG.Open.StatedSp n F).subtype) := by
    rwa [hcent] at hJ'compS
  have hS : ∀ a ∈ ({s} : Set (GL (Fin n ⊕ Fin n) F)),
      ∀ b ∈ ({s} : Set (GL (Fin n ⊕ Fin n) F)), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl s
  obtain ⟨ε, hε, hcomp⟩ :=
    exists_isComponentOf_glBlockCentralizer_PSp n F
      ({s} : Set (GL (Fin n ⊕ Fin n) F)) hS hJ'comp'
  have hSU : ∀ s' ∈ ({s} : Set (GL (Fin n ⊕ Fin n) F)),
      s' ∈ CFSG.Open.StatedSp n F := by
    intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    subst s'
    exact hsP
  obtain ⟨e, heprim, heε, hsplit⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_PSp n f
      ({s} : Set (GL (Fin n ⊕ Fin n) F)) hSU hS hε
  exact ⟨s, hsP, hsLift, hsodd, ε, hε, ⟨e, heprim, heε, hsplit⟩, J', hcomp, hJ'map⟩

end CFSG.StandardType.RCKRP
