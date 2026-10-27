module

public import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner

public section

namespace CFSG.StandardType.TwE6D5Core

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn

section Fix


open CFSG.HardMathSupport.Solomon.Coordinator

private theorem fixSubgroup_twistedE6InndiagConj {K : Type} [Field K] {σ : K ≃+* K}
    {t : ModGL TwistTag.E6.tag K} (ht : t ∈ twistedE6InndiagGL K σ) :
    fixSubgroup (twistedE6InndiagConj K σ ⟨t, ht⟩) =
      (Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
        (twistedE6RootGroup K σ) := by
  ext c
  rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  have e : twistedE6InndiagConj K σ ⟨t, ht⟩ c = c ↔
      (c : ModGL TwistTag.E6.tag K) * t = t * c := by
    rw [Subtype.ext_iff]
    change t * (c : ModGL TwistTag.E6.tag K) * t⁻¹ = c ↔ _
    rw [mul_inv_eq_iff_eq_mul, eq_comm]
  exact e

end Fix

section RootDiag


private theorem rootDiagUnit_ne_one_of_ncard_eq_40 {L : Type} [Field L]
    {a : Fin Tag.E6.rank → Lˣ} (hk : (kernelRoots (rootCharHom a)).ncard = 40) :
    rootDiagUnit Tag.E6 a ≠ 1 := by
  intro h
  have ha : a = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective (by rw [h, rootDiagUnit_one])
  have hset : kernelRoots (rootCharHom a) = {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α} := by
    rw [kernelRoots_rootCharHom, ha]
    ext γ
    simp [rootChar]
  have h72 : (kernelRoots (rootCharHom a)).ncard = 72 := by
    rw [hset, show {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α} = ↑(rootFinset Tag.E6) from
      Set.ext fun v => (mem_rootFinset).symm, Set.ncard_coe_finset, card_rootFinset]
    rfl
  omega

end RootDiag

section Component


open CFSG.HardMathSupport.Solomon.Coordinator

theorem exists_map_eq_rationalComponent_d5
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (S : LangSetup Tag.E6 (AlgebraicClosure K) 5) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hSq : S.D.q = 2 ^ 1) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hΦ : S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr)
    (hL : ringChar (AlgebraicClosure K) = 2)
    (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
    (hι : Function.Injective ι) (hrange : ι.range = S.Γ)
    {t : ModGL TwistTag.E6.tag K} (ht : t ∈ twistedE6InndiagGL K σ)
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (hk : (kernelRoots (rootCharHom a)).ncard = 40)
    (hconj : ∀ c, ι (twistedE6InndiagConj K σ ⟨t, ht⟩ c) =
      rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹)
    {D : Subgroup ↥(twistedE6RootGroup K σ)}
    (hD : CFSG.Open.IsComponentOf D
      ((Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
        (twistedE6RootGroup K σ))) :
    ∃ i : KernelComponent (rootCharHom a),
      D.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧ DStrongModel D 5 2 1 := by
  classical
  have h1 := rootDiagUnit_ne_one_of_ncard_eq_40 hk
  have hfix := fixSubgroup_twistedE6InndiagConj (K := K) (σ := σ) ht
  have hK : CFSG.Open.IsComponentOf D (fixSubgroup (twistedE6InndiagConj K σ ⟨t, ht⟩)) := by
    rw [hfix]
    exact hD
  have hFr' : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hSq]; exact hFr c
  have h3q : 3 ∣ S.D.q + 1 := by rw [hSq]; norm_num
  have h3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := fun h =>
    absurd (ringChar.dvd h) (by rw [hL]; norm_num)
  have hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i) := fun i =>
    Or.inl (d5_class_strongModel S hFr' hΦ h3 hT hap h3q hk i).choose_spec.choose_spec.2.2.2.1
  obtain ⟨i, -, hmap⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S Nat.prime_three
      ι hι hrange (twistedE6InndiagConj K σ ⟨t, ht⟩) hconj hT hap h1 hTame hK
  obtain ⟨r, e, hr, hq, hmodel⟩ := d5_class_strongModel S hFr' hΦ h3 hT hap h3q hk i
  have hr2 : r = 2 := by rw [← hr, hL]
  have he : e = 1 :=
    Nat.pow_right_injective (le_refl 2) (by simpa [hr2] using hq.symm.trans hSq)
  rw [hr2, he] at hmodel
  refine ⟨i, hmap, DStrongModel.of_equiv ?_ hmodel⟩
  exact (Subgroup.equivMapOfInjective D ι hι).trans (MulEquiv.subgroupCongr hmap)

end Component

end CFSG.StandardType.TwE6D5Core

end
