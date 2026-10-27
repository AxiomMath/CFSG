module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.LieType.Chevalley.OddToralInvolutionComponents
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem ntpD4_layer
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L) (hpair : OrderThreeOutsideConnected S a n)
    (hker : (rootCharKernel a).ncard = 24) (i : KernelComponent (rootCharHom a))
    (hi : ∀ j : KernelComponent (rootCharHom a), j = i)
    (K : Subgroup (ModGL .E6 L))
    (hK : IsComponentOf K (S.Γ ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n : Subgroup (ModGL .E6 L)) :
        Set (ModGL .E6 L)))) :
    (∀ γ ∈ rootCharKernel a, S.ρ γ ∈ rootCharKernel a) ∧
    K ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
    (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj n).toMonoidHom =
      rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
    IsComponentOf K (rationalComponent S.ρ S.Γ (rootCharHom a) i ⊓
      Subgroup.centralizer ({n} : Set (ModGL .E6 L))) := by
  classical
  obtain ⟨hap, hT, h1, hnM, _hn3, hcommd, -⟩ := hpair
  have hntc : n ∈ toralCentralizer .E6 L a := by
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hnM).1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcommd.symm
  have hstab : ∀ γ ∈ rootCharKernel a, S.ρ γ ∈ rootCharKernel a :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rho_mem_kernelRoots_of_mem_torus S hT
  have hcomp_eq : componentRoots (rootCharHom a) i = rootCharKernel a := by
    ext α
    constructor
    · rintro ⟨hα, -⟩
      exact hα
    · intro hα
      exact ⟨hα, hi (⟦⟨α, hα⟩⟧ : KernelComponent (rootCharHom a))⟩
  have hrat : rationalRoots S.ρ (rootCharHom a) i = rootCharKernel a := by
    apply le_antisymm
    · rintro γ ⟨k, δ, hδ, rfl⟩
      induction k with
      | zero => simpa using (hcomp_eq ▸ hδ)
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hstab _ ih
    · intro γ hγ
      exact ⟨0, γ, hcomp_eq.symm ▸ hγ, rfl⟩
  have hΓmap : S.Γ.map (MulAut.conj n).toMonoidHom = S.Γ := by
    have hmodel : S.D.model.map (MulAut.conj n).toMonoidHom = S.D.model := by
      simpa only [CFSG.ClassicalInvolution.Balance.LocalBalance.conjSub] using
        CFSG.ClassicalInvolution.Balance.LocalBalance.conjSub_eq_of_mem_normalizer
          (Subgroup.le_normalizer hnM)
    change ⁅S.D.model, S.D.model⁆.map (MulAut.conj n).toMonoidHom = ⁅S.D.model, S.D.model⁆
    rw [Subgroup.map_commutator, hmodel]
  have hYmap : (rootSpan .E6 L (rootCharKernel a)).map (MulAut.conj n).toMonoidHom =
      rootSpan .E6 L (rootCharKernel a) := by
    simpa only [CFSG.ClassicalInvolution.Balance.LocalBalance.conjSub] using
      CFSG.ClassicalInvolution.Balance.LocalBalance.conjSub_eq_of_mem_normalizer
        (toralCentralizer_le_normalizer_rootSpan a hntc)
  have hspan : (rationalSpan S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj n).toMonoidHom =
      rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    unfold rationalSpan
    rw [hrat, Subgroup.map_inf _ _ _ (MulAut.conj n).injective, hYmap, hΓmap]
  have hnorm : (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj n).toMonoidHom =
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [rationalComponent, Subgroup.map_commutator, hspan]
  have hKq : CFSG.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥K).mpr hK.2.2)
  have hperfK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 hKq.1
  have hKΓ : K ≤ S.Γ := hK.1.trans inf_le_left
  have hKcent : K ≤ Subgroup.centralizer
      ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n : Subgroup (ModGL .E6 L)) :
        Set (ModGL .E6 L)) := hK.1.trans inf_le_right
  have hsub_d : ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) ⊆
      ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n : Subgroup (ModGL .E6 L)) :
        Set (ModGL .E6 L)) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hsub_n : ({n} : Set (ModGL .E6 L)) ⊆
      ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n : Subgroup (ModGL .E6 L)) :
        Set (ModGL .E6 L)) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
  have hKd : K ≤ Subgroup.centralizer ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) :=
    hKcent.trans (Subgroup.centralizer_le hsub_d)
  have hKn : K ≤ Subgroup.centralizer ({n} : Set (ModGL .E6 L)) :=
    hKcent.trans (Subgroup.centralizer_le hsub_n)
  have hRd : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      Subgroup.centralizer ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) := by
    unfold rationalComponent
    refine (Subgroup.commutator_le_self _).trans ?_
    unfold rationalSpan
    rw [hrat]
    exact inf_le_left.trans (rootSpan_le_centralizer a (fun _ hα => hα))
  have hcent_sup : Subgroup.centralizer ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) ⊓
      Subgroup.centralizer ({n} : Set (ModGL .E6 L)) ≤
      Subgroup.centralizer
        ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n :
          Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) := by
    intro x hx
    obtain ⟨hxd, hxn⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hA : (Subgroup.zpowers (rootDiagUnit .E6 a) : Subgroup (ModGL .E6 L)) ≤
        Subgroup.centralizer ({x} : Set (ModGL .E6 L)) := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxd).symm
    have hB : (Subgroup.zpowers n : Subgroup (ModGL .E6 L)) ≤
        Subgroup.centralizer ({x} : Set (ModGL .E6 L)) := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxn).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hA hB) hy)
  have hKX : K ≤ toralCentralizer .E6 L a :=
    le_inf (hKΓ.trans ((Subgroup.commutator_le_self S.D.model).trans inf_le_left)) hKd
  have hKY : K ≤ rootSpan .E6 L (rootCharKernel a) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_rootSpan_kernel
      Nat.prime_three a hap hKX hperfK
  have hKspan : K ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    refine le_inf ?_ hKΓ
    rw [hrat]
    exact hKY
  have hKR : K ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [rationalComponent, ← hperfK]
    exact Subgroup.commutator_mono hKspan hKspan
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    intro h
    have h2 : (2 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 2
    have h3 : (3 : L) = 0 := by exact_mod_cast h
    have : (1 : L) = 0 := by
      calc (1 : L) = 3 - 2 := by norm_num
        _ = 0 := by rw [h3, h2]; simp
    exact one_ne_zero this
  have hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    rcases CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_tame_of_prime S
        (p := 3) Nat.prime_three h3L (fun h => absurd h (by decide)) hT hap h1 i with hq | hsolv
    · exact hq
    · exfalso
      haveI : Group.IsSolvable ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := hsolv
      have hKsolv : Group.IsSolvable ↥K :=
        Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion hKR) (Subgroup.inclusion_injective hKR)
      haveI := hKsolv
      haveI hKnt : Nontrivial ↥K := by
        haveI := hK.2.2.2.toNontrivial
        exact (QuotientGroup.mk_surjective (s := Subgroup.center ↥K)).nontrivial
      have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥K
      rw [hK.2.2.1] at hlt
      exact lt_irrefl _ hlt
  have hRΓ : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ S.Γ :=
    (Subgroup.commutator_le_self _).trans inf_le_right
  have hle : K ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i ⊓
      Subgroup.centralizer ({n} : Set (ModGL .E6 L)) := le_inf hKR hKn
  have hHK : rationalComponent S.ρ S.Γ (rootCharHom a) i ⊓
      Subgroup.centralizer ({n} : Set (ModGL .E6 L)) ≤
      S.Γ ⊓ Subgroup.centralizer
        ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n : Subgroup (ModGL .E6 L)) :
          Set (ModGL .E6 L)) :=
    le_inf (inf_le_left.trans hRΓ)
      ((le_inf (inf_le_left.trans hRd) inf_le_right).trans hcent_sup)
  have hcomp : IsComponentOf K (rationalComponent S.ρ S.Γ (rootCharHom a) i ⊓
      Subgroup.centralizer ({n} : Set (ModGL .E6 L))) := by
    refine ⟨hle, ?_, hK.2.2⟩
    have h1 : CFSG.Assembly.IsSubnormal K
        (S.Γ ⊓ Subgroup.centralizer
          ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n :
            Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L))) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open K _).mpr hK.2.1
    have h2 := h1.inf_of_le hHK
    rw [inf_eq_left.mpr hle] at h2
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open K _).mp h2
  exact ⟨hstab, hKR, hnorm, hq, hcomp⟩

end CFSG.StandardType.NTPlane

end
