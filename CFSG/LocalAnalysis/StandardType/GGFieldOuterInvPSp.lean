module

public import CFSG.LocalAnalysis.StandardType.GGFieldOuterModel
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpFieldInv
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpHolds
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneRank
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueBasic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21
open CFSG.Open (IsElemAbelian)

private theorem ggFieldOuterInvPSp_false_of_component {G : Type} [Group G]
    {X L : Subgroup G} (hX : Group.IsSolvable ↥X) (hL : CFSG.Assembly.IsComponentOf L X) :
    False := by
  haveI : Group.IsSolvable ↥X := hX
  have hLsol : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hL.1)
      (Subgroup.inclusion_injective hL.1)
  haveI : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  haveI := hL.2.2.2
  haveI : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  exact Group.IsPerfect.not_isSolvable ↥L hLsol

theorem ggFieldOuterInvModel_statedSp {n : ℕ} (K : Type) [Field K] [Finite K] [CharP K 2] :
    GGFieldOuterInvModel (StatedSp n K) := by
  intro p b α hp hp2 hb1 hbp hE hα2 hout hαb hL hfix
  rcases hE with ⟨E, hEab, hbE, h4, hmax⟩
  obtain ⟨L₁, hL₁⟩ := hL
  have hpF : (p : K) ≠ 0 := by
    intro h0
    have hdvd : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd).symm
  by_cases hn : n ≤ 3
  · have hcard : Nat.card E ≤ p ^ n :=
      SpJoin.card_le_pow_of_isElemAbelian (F := K) hp hp2 hpF E hEab
    have hp4 : p ^ 4 ≤ p ^ n := h4.trans hcard
    have hpn : p ^ n ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos hn
    have hp43 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact absurd (hp4.trans hpn) (not_le.mpr hp43)
  · have hn4 : 4 ≤ n := by omega
    letI : Fintype K := Fintype.ofFinite K
    obtain ⟨σ, hσord, h, hαeq⟩ :=
      CFSG.SeitzReduction.SymplecticPilot.exists_eq_conj_fieldSp_of_not_inner
        (r := n) (K := K) (by omega) hα2 (by
          rw [MonoidHom.mem_range]
          rintro ⟨c, hc⟩
          exact hout c hc.symm)
    have hσsq : σ * σ = 1 := by
      have h := pow_orderOf_eq_one σ
      rwa [hσord, pow_two] at h
    have hσ2 : ∀ x : K, σ (σ x) = x := by
      intro x
      have h := congrArg (fun e : K ≃+* K => e x) hσsq
      simpa [RingAut.mul_apply] using h
    have hσne : σ ≠ RingEquiv.refl K := by
      intro h1
      have h2 : orderOf σ = 1 := by rw [h1]; exact orderOf_one
      omega
    let A : GL (Fin n ⊕ Fin n) K :=
      (h : GL (Fin n ⊕ Fin n) K) * ((h : GL (Fin n ⊕ Fin n) K).map σ.toRingHom)⁻¹
    have hcoe : ∀ g : StatedSp n K,
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp n K σ g :
            GL (Fin n ⊕ Fin n) K) =
          (g : GL (Fin n ⊕ Fin n) K).map σ.toRingHom := by
      intro g
      exact Units.ext (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp σ g)
    have hmap2 : ∀ x : GL (Fin n ⊕ Fin n) K,
        (x.map σ.toRingHom).map σ.toRingHom = x := by
      intro x
      have hcomp : σ.toRingHom.comp σ.toRingHom = RingHom.id K := by
        ext y
        exact hσ2 y
      have h := congrArg
        (fun f : GL (Fin n ⊕ Fin n) K →* GL (Fin n ⊕ Fin n) K => f x)
        (Matrix.GeneralLinearGroup.map_comp σ.toRingHom σ.toRingHom)
      rw [hcomp, Matrix.GeneralLinearGroup.map_id] at h
      simpa using h.symm
    have hA_mem : A ∈ StatedSp n K := by
      have h1 : ((h : GL (Fin n ⊕ Fin n) K).map σ.toRingHom)⁻¹ ∈ StatedSp n K :=
        inv_mem (CFSG.Open.StatedAPI.map_mem_statedSp (n := n) σ.toRingHom h.2)
      exact mul_mem h.2 h1
    have hAσ : A.map σ.toRingHom = A⁻¹ := by
      change ((h : GL (Fin n ⊕ Fin n) K) *
        ((h : GL (Fin n ⊕ Fin n) K).map σ.toRingHom)⁻¹).map σ.toRingHom =
        ((h : GL (Fin n ⊕ Fin n) K) *
          ((h : GL (Fin n ⊕ Fin n) K).map σ.toRingHom)⁻¹)⁻¹
      rw [map_mul, map_inv, hmap2 (h : GL (Fin n ⊕ Fin n) K), mul_inv_rev, inv_inv]
    have hAinv_map : (A⁻¹).map σ.toRingHom = A := by
      rw [map_inv, hAσ, inv_inv]
    have hinv : ∀ x : GL (Fin n ⊕ Fin n) K,
        A * (A * x.map σ.toRingHom * A⁻¹).map σ.toRingHom * A⁻¹ = x := by
      intro x
      have h1 : (A * x.map σ.toRingHom * A⁻¹).map σ.toRingHom = A⁻¹ * x * A := by
        rw [map_mul, map_mul, map_inv, hAσ, hmap2 x, inv_inv]
      rw [h1]
      group
    have hαg : ∀ g : StatedSp n K,
        ((α g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
          A * (g : GL (Fin n ⊕ Fin n) K).map σ.toRingHom * A⁻¹ := by
      intro g
      have h1 : α g =
          (h * (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp n K σ h)⁻¹) *
            CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp n K σ g *
            (h * (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp n K σ h)⁻¹)⁻¹ := by
        rw [hαeq]
        simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply,
          map_mul, map_inv]
        group
      rw [h1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcoe h, hcoe g, A]
    have hborder : orderOf (b : GL (Fin n ⊕ Fin n) K) = p := by
      haveI : Fact p.Prime := ⟨hp⟩
      change orderOf ((Subgroup.subtype (StatedSp n K)) b) = p
      rw [orderOf_injective (Subgroup.subtype (StatedSp n K))
        (Subgroup.subtype_injective _) b]
      exact orderOf_eq_prime hbp hb1
    have hodd : Odd (orderOf (b : GL (Fin n ⊕ Fin n) K)) :=
      hborder.symm ▸ hp.odd_of_ne_two hp2
    have hfix_target : ∀ g ∈ Subgroup.centralizer ({(b : GL (Fin n ⊕ Fin n) K)} : Set _) ⊓
        StatedSp n K, A * g.map σ.toRingHom * A⁻¹ = g := by
      intro g hg
      have hg' : (⟨g, hg.2⟩ : StatedSp n K) ∈
          Subgroup.centralizer ({b} : Set (StatedSp n K)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp hg.1
      have h := congrArg (fun x : StatedSp n K => (x : GL (Fin n ⊕ Fin n) K))
        (hfix ⟨g, hg.2⟩ hg')
      rw [hαg] at h
      exact h
    have hcomm :=
      CFSG.StandardType.ClassicalBlocks.isMulCommutative_centralizer_of_fieldInv_Sp
        (K := K) (n := n) σ hσne A hA_mem hinv (b : GL (Fin n ⊕ Fin n) K) b.2 hodd
        hfix_target
    haveI hsol : Group.IsSolvable
        ↥(Subgroup.centralizer ({(b : GL (Fin n ⊕ Fin n) K)} : Set _) ⊓ StatedSp n K) :=
      Group.isSolvable_of_comm (fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2))
    let f : ↥(Subgroup.centralizer ({b} : Set (StatedSp n K))) →*
        ↥(Subgroup.centralizer ({(b : GL (Fin n ⊕ Fin n) K)} : Set _) ⊓ StatedSp n K) :=
      { toFun := fun x => ⟨(x.1 : GL (Fin n ⊕ Fin n) K), by
          refine ⟨?_, x.1.2⟩
          show (x.1 : GL (Fin n ⊕ Fin n) K) ∈
            Subgroup.centralizer ({(b : GL (Fin n ⊕ Fin n) K)} : Set _)
          rw [Subgroup.mem_centralizer_singleton_iff]
          simpa only [Subgroup.coe_mul] using
            congrArg (fun z : StatedSp n K => (z : GL (Fin n ⊕ Fin n) K))
              (Subgroup.mem_centralizer_singleton_iff.mp x.2)⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun x y => Subtype.ext rfl }
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun z : ↥(Subgroup.centralizer ({(b : GL (Fin n ⊕ Fin n) K)} : Set _) ⊓
          StatedSp n K) => (z : GL (Fin n ⊕ Fin n) K)) hxy
    exact ggFieldOuterInvPSp_false_of_component
      (Group.isSolvable_of_isSolvable_injective (f := f) hf) hL₁

theorem ggFieldOuterInvModelAt_PSp
    : GGFieldOuterInvModelAt .PSp := by
  intro n f _ hrank _hF
  have hn : 2 ≤ n := hrank
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨(ggU .PSp n f).K, inferInstance, MonoidHom.id _, Function.surjective_id, ?_, ?_⟩
  · rw [MonoidHom.ker_id]
    exact (AutPSp.center_eq_bot (n := n) (K := GaloisField 2 f)).symm
  · exact ggFieldOuterInvModel_statedSp (n := n) (K := GaloisField 2 f)

theorem ggFieldOuterInvAt_PSp
    : GGFieldOuterInvAt .PSp :=
  ggFieldOuterInvAt_of_model (Or.inl rfl) ggFieldOuterInvModelAt_PSp fun h => nomatch h

end CFSG.StandardType
