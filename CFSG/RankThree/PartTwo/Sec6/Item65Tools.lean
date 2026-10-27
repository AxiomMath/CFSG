module

public import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GroupTheory.FrobeniusNormalComplement
import CFSG.RankThree.PartTwo.Sec5.Bender.Core
import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec6.Item612Core
public import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_inf_centralizer_sup_theta_of_isPGroup {L D : Subgroup G} (hD3 : IsPGroup 3 D)
    (hDC : D ≤ thetaQuotCentralizer L) :
    L ≤ (L ⊓ Subgroup.centralizer (D : Set G)) ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hθ3 : ¬ 3 ∣ Nat.card θL := (theta_solvable_and_not_dvd L).2
  intro l hl
  set α : D →* MulAut G := MulAut.conj.comp D.subtype
  obtain ⟨y, hy, hyfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hD3 α θL
    hθ3 l).2 (by
      intro a x hx
      change l⁻¹ * ((a : G) * x * (a : G)⁻¹) ∈ θL
      have ha := hDC a.2
      have h1 : l⁻¹ * ((a : G) * l * (a : G)⁻¹) ∈ θL := (mem_thetaQuotCentralizer_iff.mp ha).2 l hl
      have h2 : (a : G) * (l⁻¹ * x) * (a : G)⁻¹ ∈ θL :=
        (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_theta L
          (thetaQuotCentralizer_le_normalizer L ha)) _).mp hx
      have h3 := θL.mul_mem h1 h2
      rwa [show l⁻¹ * ((a : G) * l * (a : G)⁻¹) * ((a : G) * (l⁻¹ * x) * (a : G)⁻¹) =
        l⁻¹ * ((a : G) * x * (a : G)⁻¹) by group] at h3)
  have hyL : y ∈ L := by
    have := L.mul_mem hl (theta_le L hy)
    simpa using this
  have hyD : y ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : a * y * a⁻¹ = y := hyfix ⟨a, ha⟩
    calc a * y = (a * y * a⁻¹) * a := by group
      _ = y * a := by rw [h1]
  rw [show l = y * (y⁻¹ * l) by group]
  refine Subgroup.mul_mem_sup ⟨hyL, hyD⟩ ?_
  have := inv_mem hy
  simpa using this

theorem le_residual_inf_centralizer_sup_theta {L D : Subgroup G} (hLp : Group.IsPerfect L)
    (hD3 : IsPGroup 3 D) (hDC : D ≤ thetaQuotCentralizer L) :
    L ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) L :=
  le_perfectResidual_sup hLp (inf_le_left.trans (le_normalizer_theta L))
    (le_inf_centralizer_sup_theta_of_isPGroup hD3 hDC)

omit [Finite G] in
theorem inSubgroup_perfectResidual_le (X : Subgroup G) : inSubgroup perfectResidual X ≤ X :=
  Subgroup.map_subtype_le _

theorem isQuasisimple_residual_inf_centralizer {L D : Subgroup G} (hLp : Group.IsPerfect L)
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)) (hD3 : IsPGroup 3 D)
    (hDC : D ≤ thetaQuotCentralizer L) :
    IsQuasisimple (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G)) ⧸
      aschbacherSolvableCore 3
        (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G)))) := by
  set Z := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G)) with hZ
  have hZL : Z ≤ L := (inSubgroup_perfectResidual_le _).trans inf_le_left
  set ρ : Z →* L ⧸ aschbacherSolvableCore 3 L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hZL)
  have hcov := le_residual_inf_centralizer_sup_theta hLp hD3 hDC
  have hsurj : Function.Surjective ρ := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) q
    have hl : (l : G) ∈ (Z : Set G) * (inSubgroup (aschbacherSolvableCore 3) L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Z _
        (hZL.trans (le_normalizer_theta L))]
      exact hcov l.2
    obtain ⟨z, hz, t, ht, hzt⟩ := hl
    refine ⟨⟨z, hz⟩, ?_⟩
    change QuotientGroup.mk' (aschbacherSolvableCore 3 L) (Subgroup.inclusion hZL ⟨z, hz⟩) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) l
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨t', ht', rfl⟩ := ht
    have : (Subgroup.inclusion hZL ⟨z, hz⟩)⁻¹ * l = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hzt]
      simp
    rw [this]
    exact ht'
  have hker : ∀ z : Z, z ∈ ρ.ker ↔ (z : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    intro z
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' (aschbacherSolvableCore 3 L) (Subgroup.inclusion hZL z) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      have : w = Subgroup.inclusion hZL z := Subtype.ext hwz
      rwa [← this]
  have hθsol := (theta_solvable_and_not_dvd L).1
  have hθ3 := (theta_solvable_and_not_dvd L).2
  set ι : ρ.ker →* inSubgroup (aschbacherSolvableCore 3) L :=
    { toFun := fun z => ⟨((z : Z) : G), (hker z).mp z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg Subtype.val hxy
    exact h
  have hsol : Group.IsSolvable ρ.ker := Group.isSolvable_of_isSolvable_injective hι
  have hle : ρ.ker.map Z.subtype ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hker z).mp hz
  have h3 : ¬ 3 ∣ Nat.card ρ.ker := fun h => by
    have h' := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective Z.subtype_injective] at h'
    exact hθ3 (h.trans h')
  exact Sec14.isQuasisimple_quotient_theta_of_surjective hLq ρ hsurj hsol h3

theorem residual_inf_centralizer_ne_bot {L D : Subgroup G} (hLp : Group.IsPerfect L)
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)) (hD3 : IsPGroup 3 D)
    (hDC : D ≤ thetaQuotCentralizer L) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G)) ≠ ⊥ := by
  intro h
  have hcov := le_residual_inf_centralizer_sup_theta hLp hD3 hDC
  rw [h, bot_sup_eq] at hcov
  have hLθ : L ≤ inSubgroup (aschbacherSolvableCore 3) L := hcov
  have hsub : Subsingleton (L ⧸ aschbacherSolvableCore 3 L) := by
    refine ⟨fun x y => ?_⟩
    induction x using QuotientGroup.induction_on with
    | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
    rw [QuotientGroup.eq]
    have hm := hLθ (L.mul_mem (inv_mem x.2) y.2)
    obtain ⟨w, hw, hwe⟩ := hm
    have : w = x⁻¹ * y := Subtype.ext (by simpa using hwe)
    rwa [← this]
  exact (not_nontrivial_iff_subsingleton.mpr hsub) (CFSG.LocalCores.isQuasisimple_nontrivial hLq)

theorem mem_thetaComponentsIn_of {M Y : Subgroup G} (hYM : Y ≤ M) (hYp : Group.IsPerfect Y)
    (hsn : (Y.subgroupOf M).IsSubnormal) (hYq : IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y)) :
    Y ∈ thetaComponentsIn M := by
  refine mem_thetaComponentsIn_iff.mpr ⟨hYM, ?_, hsn, ?_⟩
  · have := hYp
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hYM).symm.toMonoidHom) (MulEquiv.surjective _)
  · set e := (Subgroup.subgroupOfEquivOfLe hYM).symm
    exact LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three e)) hYq

theorem le_of_isPerfect_of_le_sup_theta {M K P : Subgroup G} (hK : K ∈ thetaComponentsIn M)
    (hP : Group.IsPerfect P) (hPK : P ≤ K ⊔ inSubgroup (aschbacherSolvableCore 3) M) : P ≤ K := by
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  have hPM : P ≤ M := hPK.trans (sup_le hKM (theta_le M))
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 M)
  have hres := perfectResidual_comap_map_of_mem_thetaComponents Nat.prime_three hK'
  have hP' : Group.IsPerfect (P.subgroupOf M) := by
    have := hP
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hPM).symm.toMonoidHom) (MulEquiv.surjective _)
  have hle : P.subgroupOf M ≤ ((K.subgroupOf M).map π).comap π := by
    intro y hy
    have hyK : (y : G) ∈ K ⊔ inSubgroup (aschbacherSolvableCore 3) M := hPK hy
    have hy' : (y : G) ∈ (K : Set G) * (inSubgroup (aschbacherSolvableCore 3) M : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right K _
        (hKM.trans (le_normalizer_theta M))]
      exact hyK
    obtain ⟨k, hk, t, ht, hkt⟩ := hy'
    obtain ⟨t', ht', rfl⟩ := ht
    refine ⟨⟨k, hKM hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (⟨k, hKM hk⟩ : M)⁻¹ * y = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hkt]
      simp
    rw [this]
    exact ht'
  have h1 := le_inSubgroup_perfectResidual_of_isPerfect hP' hle
  rw [hres] at h1
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (h1 (Subgroup.mem_subgroupOf.mpr (show
    ((⟨x, hPM hx⟩ : M) : G) ∈ P from hx)))

theorem exists_le_mem_thetaComponentsIn (h48 : Sec4.Item4_8) {M : Subgroup G}
    (hM : SectionFourHyp M) {A : Subgroup G} (hAM : A ≤ M) (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsIn (M ⊓ Subgroup.centralizer {x})) :
    ∃ K ∈ thetaComponentsIn M, Y ≤ K := by
  obtain ⟨hYC, hYθ⟩ := mem_thetaComponentsIn_iff.mp hY
  have hYM : Y ≤ M := hYC.trans inf_le_left
  set x' : M := ⟨x, hAM hxA⟩ with hx'
  have hCeq : Subgroup.centralizer ({x'} : Set M) =
      (M ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf M := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  set ψ : (M ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≃*
      Subgroup.centralizer ({x'} : Set M) :=
    (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans (MulEquiv.subgroupCongr hCeq.symm)
  have hψ : ∀ z, ((ψ z : M) : G) = z := fun z => rfl
  set T := (Y.subgroupOf (M ⊓ Subgroup.centralizer ({x} : Set G))).map ψ.toMonoidHom with hT
  have hTθ : T ∈ thetaComponents 3 (Subgroup.centralizer ({x'} : Set M)) :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three ψ hYθ
  have hTY : T.map (Subgroup.centralizer ({x'} : Set M)).subtype = Y.subgroupOf M := by
    ext w
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (by simpa [hψ] using Subgroup.mem_subgroupOf.mp hy)
    · intro hw
      have hwY : (w : G) ∈ Y := Subgroup.mem_subgroupOf.mp hw
      have hwC : (w : G) ∈ M ⊓ Subgroup.centralizer ({x} : Set G) := hYC hwY
      refine ⟨ψ ⟨w, hwC⟩, ⟨⟨w, hwC⟩, Subgroup.mem_subgroupOf.mpr hwY, rfl⟩, ?_⟩
      apply Subtype.ext
      rfl
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hA' : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf M) := by
    refine ⟨⟨⟨fun y z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.mp y.2) _ (Subgroup.mem_subgroupOf.mp z.2)
    · exact Subtype.ext (by simpa using hA.2 _ (Subgroup.mem_subgroupOf.mp hy))
  have hAn' : ∃ n : ℕ, 3 ≤ n ∧ Nat.card (A.subgroupOf M) = 3 ^ n := by
    obtain ⟨n, hn, hcard⟩ := hAn
    exact ⟨n, hn, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, hcard]⟩
  have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  obtain ⟨K', hK', hYK'⟩ := h48 M hM (A.subgroupOf M) hA' hAn' x'
    (Subgroup.mem_subgroupOf.mpr hxA) hx'1 (Y.subgroupOf M) ⟨T, hTθ, hTY⟩
  refine ⟨K'.map M.subtype, ⟨K', hK', rfl⟩, fun y hy => ?_⟩
  exact ⟨⟨y, hYM hy⟩, hYK' (Subgroup.mem_subgroupOf.mpr hy), rfl⟩

theorem commutator_le_theta_of_ne {H : Type} [Group H] [Finite H] {K K' : Subgroup H}
    (hK : K ∈ thetaComponents 3 H) (hK' : K' ∈ thetaComponents 3 H) (hne : K ≠ K') :
    ⁅K, K'⁆ ≤ aschbacherSolvableCore 3 H := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H)
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) Nat.prime_three
  have hc := isComponent_map_of_mem_thetaComponents Nat.prime_three hK
  have hc' := isComponent_map_of_mem_thetaComponents Nat.prime_three hK'
  have hne' : K.map π ≠ K'.map π := fun h => hne (hbij.injOn hK hK' h)
  have hcomm := (LocalCores.distinct_components_commute hc hc').resolve_left hne'
  rw [← Subgroup.map_commutator] at hcomm
  rw [← QuotientGroup.ker_mk' (aschbacherSolvableCore 3 H)]
  exact (Subgroup.map_eq_bot_iff _).mp hcomm

theorem le_normalizer_of_isPerfect_le {H : Type} [Group H] [Finite H] {K Y V : Subgroup H}
    (hK : K ∈ thetaComponents 3 H) (hYK : Y ≤ K) (hYp : Group.IsPerfect Y) (hY1 : Y ≠ ⊥)
    (hVsol : Group.IsSolvable V) (hYV : Y ≤ Subgroup.normalizer (V : Set H)) :
    V ≤ Subgroup.normalizer (K : Set H) := by
  intro v hv
  by_contra hvK
  set σ := MulAut.conj v
  set Kv := K.map σ.toMonoidHom with hKvdef
  have hKv : Kv ∈ thetaComponents 3 H := map_mulEquiv_mem_thetaComponents Nat.prime_three σ hK
  have hne : K ≠ Kv := by
    intro h
    apply hvK
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact h.symm
  have hcomm := commutator_le_theta_of_ne hKv hK hne.symm
  set N := aschbacherSolvableCore 3 H with hN
  have hNn : N.Normal := aschbacherSolvableCore_normal 3 H
  set Yv := Y.map σ.toMonoidHom with hYvdef
  have hYvKv : Yv ≤ Kv := Subgroup.map_mono hYK
  have hYvp : Group.IsPerfect Yv := by
    have := hYp
    exact Group.IsPerfect.ofSurjective
      (f := (Y.equivMapOfInjective σ.toMonoidHom σ.injective).toMonoidHom) (MulEquiv.surjective _)
  have hdec : ∀ z ∈ Yv, ∃ u ∈ V, ∃ y ∈ Y, z = u * y := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : y * v⁻¹ * y⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hYV hy) v⁻¹).mp (V.inv_mem hv)
    refine ⟨v * (y * v⁻¹ * y⁻¹), V.mul_mem hv h1, y, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, σ]
    group
  have hzV : ∀ z ∈ Yv, z ∈ Subgroup.normalizer (V : Set H) := by
    intro z hz
    obtain ⟨u, hu, y, hy, rfl⟩ := hdec z hz
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hu) (hYV hy)
  have hYvW : Yv ≤ V ⊔ N := by
    rw [← commutator_self_eq_of_isPerfect hYvp, Subgroup.commutator_le]
    intro z₁ hz₁ z₂ hz₂
    obtain ⟨u, hu, y, hy, rfl⟩ := hdec z₂ hz₂
    have h1 : ⁅z₁, u⁆ ∈ V := by
      rw [commutatorElement_def]
      exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hzV z₁ hz₁) u).mp hu) (V.inv_mem hu)
    have h2 : ⁅z₁, y⁆ ∈ N := hcomm (Subgroup.commutator_mem_commutator (hYvKv hz₁) (hYK hy))
    have h3 : u * ⁅z₁, y⁆ * u⁻¹ ∈ N := hNn.conj_mem _ h2 u
    have e : ⁅z₁, u * y⁆ = ⁅z₁, u⁆ * (u * ⁅z₁, y⁆ * u⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h3)
  have hWsol : Group.IsSolvable (V ⊔ N : Subgroup H) := by
    have hNsol : Group.IsSolvable N :=
      (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).1
    have hVN : V ≤ Subgroup.normalizer (N : Set H) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hNn]
      exact le_top
    have h := isSolvable_sup_of_le_normalizer hVN hNsol hVsol
    rwa [sup_comm] at h
  have hYvsol : Group.IsSolvable Yv :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYvW)
      (Subgroup.inclusion_injective _)
  have hYvbot : Yv = ⊥ := by
    by_contra hne'
    have : Nontrivial Yv := (Subgroup.nontrivial_iff_ne_bot Yv).mpr hne'
    have := hYvp
    exact Group.IsPerfect.not_isSolvable Yv hYvsol
  apply hY1
  rw [hYvdef] at hYvbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ σ.injective).mp hYvbot

theorem le_normalizer_of_isPerfect_le_of_mem_thetaComponentsIn {M K Y V : Subgroup G}
    (hK : K ∈ thetaComponentsIn M) (hYK : Y ≤ K) (hYp : Group.IsPerfect Y) (hY1 : Y ≠ ⊥)
    (hVM : V ≤ M) (hVsol : Group.IsSolvable V) (hYV : Y ≤ Subgroup.normalizer (V : Set G)) :
    V ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  have hYM : Y ≤ M := hYK.trans hKM
  have hY'p : Group.IsPerfect (Y.subgroupOf M) := by
    have := hYp
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hYM).symm.toMonoidHom) (MulEquiv.surjective _)
  have hY'1 : Y.subgroupOf M ≠ ⊥ := by
    intro h
    apply hY1
    rw [← Subgroup.map_subgroupOf_eq_of_le hYM, h, Subgroup.map_bot]
  have hV'sol : Group.IsSolvable (V.subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hVM).toMonoidHom) (MulEquiv.injective _)
  have h := le_normalizer_of_isPerfect_le hK' (Subgroup.subgroupOf_mono M hYK) hY'p hY'1 hV'sol
    (subgroupOf_le_normalizer_subgroupOf hYV)
  intro v hv
  have hv' := h (Subgroup.mem_subgroupOf.mpr (show ((⟨v, hVM hv⟩ : M) : G) ∈ V from hv))
  have := Subgroup.le_normalizer_map M.subtype ⟨⟨v, hVM hv⟩, hv', rfl⟩
  rwa [Subgroup.map_subgroupOf_eq_of_le hKM] at this

theorem exists_invariant_two_subgroup_not_le_theta_of_le {L E F V : Subgroup G}
    (hE3 : IsPGroup 3 E) (hEL : E ≤ Subgroup.normalizer (L : Set G)) (hV2 : IsPGroup 2 V)
    (hEV : E ≤ Subgroup.normalizer (V : Set G)) (hVL : V ≤ Subgroup.normalizer (L : Set G))
    (hVLC : V ≤ L ⊔ thetaQuotCentralizer L) (hFE : F ≤ E) (hVF : V ≤ ⁅V, F⁆)
    (hVC : ¬ V ≤ thetaQuotCentralizer L) :
    ∃ U ∈ invariantPiSubgroups L E (piOf 2),
      ¬ ⁅U, F⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set C := thetaQuotCentralizer L with hC
  have hθN := normalizer_le_normalizer_theta L
  have hCN := normalizer_le_normalizer_thetaQuotCentralizer L
  have hθC := theta_le_thetaQuotCentralizer L
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  set Y := (V ⊔ C) ⊓ L with hY
  set Z := C ⊓ L with hZ
  have hZY : Z ≤ Y := inf_le_inf_right L le_sup_right
  have hYL : Y ≤ L := inf_le_right
  have hYZ : Y ≤ Subgroup.normalizer (Z : Set G) :=
    (le_inf (hYL.trans (hLN.trans hCN)) (hYL.trans hLN)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hYpow : ∀ y ∈ Y, ∃ k : ℕ, y ^ (2 ^ k) ∈ Z := by
    intro y hy
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hV2 (hVL.trans hCN) hy.1
    exact ⟨k, hk, L.pow_mem hy.2 _⟩
  obtain ⟨R⟩ : Nonempty (Sylow 2 Y) := inferInstance
  set RG := (R : Subgroup Y).map Y.subtype with hRG
  have hRGY : RG ≤ Y := Subgroup.map_subtype_le _
  have hRG2 : IsPGroup 2 RG := R.isPGroup'.map Y.subtype
  have hYRZ : Y ≤ RG ⊔ Z := le_sylow_sup_of_forall_pow_mem hZY hYZ hYpow R
  set W := RG ⊔ θL with hW
  have hWL : W ≤ L := sup_le (hRGY.trans hYL) (theta_le L)
  have hRGW : RG ≤ Subgroup.normalizer (W : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro r hr x hx
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hr) x).mp
        hx)
    · intro r hr x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_theta L (hYL (hRGY hr))) x).mp hx)
  have hZW : Z ≤ Subgroup.normalizer (W : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro z hz x hx
      have hxL : x ∈ L := hYL (hRGY hx)
      have h1 := (mem_thetaQuotCentralizer_iff.mp hz.1).2 x hxL
      rw [show z * x * z⁻¹ = x * (x⁻¹ * (z * x * z⁻¹)) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right h1)
    · intro z hz x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta L hz.2)
        x).mp hx)
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := hYRZ.trans (sup_le hRGW hZW)
  have hEC : E ≤ Subgroup.normalizer (C : Set G) := hEL.trans hCN
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) := by
    have h1 : E ≤ Subgroup.normalizer ((V ⊔ C : Subgroup G) : Set G) := by
      apply le_normalizer_sup_of_conj
      · intro e he x hx
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hEV he) x).mp hx)
      · intro e he x hx
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hEC he) x).mp hx)
    exact (le_inf h1 hEL).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hEW : E ≤ Subgroup.normalizer (W : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro e he x hx
      set Re := RG.map (MulAut.conj e).toMonoidHom
      have hReY : Re ≤ Y := by
        rintro _ ⟨w, hw, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hEY he) w).mp (hRGY hw)
      obtain ⟨y, hyY, hle⟩ := exists_le_conj_sylow R hReY (hRG2.map _)
      have h1 : e * x * e⁻¹ ∈ RG.map (MulAut.conj y).toMonoidHom := hle ⟨x, hx, rfl⟩
      obtain ⟨w, hw, hwx⟩ := h1
      have h2 : y * w * y⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hYW hyY) w).mp (Subgroup.mem_sup_left hw)
      change y * w * y⁻¹ = e * x * e⁻¹ at hwx
      rw [← hwx]
      exact h2
    · intro e he x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hθN (hEL he)) x).mp hx)
  have hW3 : ¬ 3 ∣ Nat.card W := not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hRG2
    ((hRGY.trans hYL).trans (le_normalizer_theta L)) (theta_solvable_and_not_dvd L).2
  obtain ⟨Q, hEQ⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      3 Nat.prime_three E W hE3 hW3 hEW 2 Nat.prime_two
  set U := (Q : Subgroup W).map W.subtype with hU
  have hUW : U ≤ W := Subgroup.map_subtype_le _
  have hU2 : IsPGroup 2 U := Q.isPGroup'.map W.subtype
  refine ⟨U, (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨hUW.trans hWL, hU2, hEQ⟩,
    fun hUE => hVC ?_⟩
  have hWpow : ∀ w ∈ W, ∃ k : ℕ, w ^ (2 ^ k) ∈ θL := fun w hw =>
    exists_pow_mem_of_mem_sup hRG2 ((hRGY.trans hYL).trans (le_normalizer_theta L)) hw
  have hWU : W ≤ U ⊔ θL := le_sylow_sup_of_forall_pow_mem le_sup_right
    (sup_le ((hRGY.trans hYL).trans (le_normalizer_theta L)) Subgroup.le_normalizer) hWpow Q
  have hVYC : V ≤ Y ⊔ C := by
    intro v hv
    have hv' : v ∈ (L : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L C (hLN.trans hCN)]
      exact hVLC hv
    obtain ⟨l, hl, z, hz, rfl⟩ := hv'
    have hlY : l ∈ Y :=
      ⟨by rw [show l = (l * z) * z⁻¹ by group]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right (inv_mem hz)),
        hl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlY) (Subgroup.mem_sup_right hz)
  have hVUC : V ≤ U ⊔ C := by
    refine hVYC.trans (sup_le (hYRZ.trans (sup_le ?_ ?_)) le_sup_right)
    · exact (le_sup_left.trans hWU).trans (sup_le le_sup_left (hθC.trans le_sup_right))
    · exact inf_le_left.trans le_sup_right
  have hUCN : U ≤ Subgroup.normalizer (C : Set G) :=
    ((hUW.trans hWL).trans hLN).trans hCN
  calc V ≤ ⁅V, F⁆ := hVF
    _ ≤ ⁅U ⊔ C, F⁆ := Subgroup.commutator_mono hVUC le_rfl
    _ ≤ ⁅U, F⁆ ⊔ C := commutator_sup_le_of_le_normalizer hUCN (hFE.trans hEC)
    _ ≤ C := sup_le (hUE.trans hθC) le_rfl

theorem exists_pow_three_eq_one_not_mem_center {Z : Type} [Group Z] [Finite Z]
    (hZp : Group.IsPerfect Z) (hZ3 : 3 ∣ Nat.card Z) :
    ∃ e : Z, e ^ 3 = 1 ∧ e ∉ Subgroup.center Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hfrob : ∀ Q : Subgroup Z, IsPGroup 3 Q →
      IsPGroup 3 (Subgroup.normalizer (Q : Set Z) ⧸
        (Subgroup.centralizer (Q : Set Z)).subgroupOf (Subgroup.normalizer (Q : Set Z))) := by
    intro Q hQ
    by_cases hQ1 : Q = ⊥
    · subst hQ1
      have htop : (Subgroup.centralizer ((⊥ : Subgroup Z) : Set Z)).subgroupOf
          (Subgroup.normalizer ((⊥ : Subgroup Z) : Set Z)) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
        rw [hy, one_mul, mul_one]
      exact IsPGroup.of_card (n := 0) (by
        rw [pow_zero, ← Subgroup.index_eq_card, htop, Subgroup.index_top])
    · obtain ⟨D, -, -, hDexp, -, hkey⟩ :=
        CFSG.RankThree.PartTwo.Sec5.Bender.exists_critical_faithful (p := 3) (by norm_num) hQ hQ1
      have hDZ : ∀ K : Subgroup Z, K ≤ Subgroup.centralizer (D : Set Z) := by
        intro K k _
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        exact (Subgroup.mem_center_iff.mp (hcon d (hDexp d hd)) k).symm
      refine CFSG.SectionRank.Ccomm.isPGroup_of_forall_prime_orderOf fun x ℓ hℓ hx => ?_
      by_contra hℓ3
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
      have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
      obtain ⟨b, m, hm3, hbm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hg0 3 (by norm_num)
      have hmdvd : m ∣ orderOf g := ⟨3 ^ b, by rw [hbm, mul_comm]⟩
      have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h => hm3 (by rw [h]; exact dvd_zero 3))
      have hdiv : orderOf g / m = 3 ^ b := by
        rw [hbm, Nat.mul_div_cancel _ hm0]
      have hord : orderOf (g ^ (3 ^ b)) = m := by
        rw [← hdiv]
        exact orderOf_pow_orderOf_div hg0 hmdvd
      set h := g ^ (3 ^ b) with hh
      set K := Subgroup.zpowers ((h : Subgroup.normalizer (Q : Set Z)) : Z) with hK
      have hK3 : ¬ 3 ∣ Nat.card K := by
        rw [hK, Nat.card_zpowers, Subgroup.orderOf_coe, hord]
        exact hm3
      have hKN : K ≤ Subgroup.normalizer (Q : Set Z) := by
        rw [hK, Subgroup.zpowers_le]
        exact h.2
      have hKC := hkey K hK3 hKN (hDZ K)
      have hhC : ((h : Subgroup.normalizer (Q : Set Z)) : Z) ∈ Subgroup.centralizer (Q : Set Z) :=
        hKC (Subgroup.mem_zpowers _)
      have h1 : QuotientGroup.mk' _ h = (1 : Subgroup.normalizer (Q : Set Z) ⧸
          (Subgroup.centralizer (Q : Set Z)).subgroupOf (Subgroup.normalizer (Q : Set Z))) := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hhC
      rw [hh, map_pow] at h1
      have h2 : orderOf (QuotientGroup.mk' _ g : Subgroup.normalizer (Q : Set Z) ⧸
          (Subgroup.centralizer (Q : Set Z)).subgroupOf (Subgroup.normalizer (Q : Set Z))) ∣
            3 ^ b := orderOf_dvd_of_pow_eq_one h1
      rw [hx] at h2
      have h3 : ℓ ∣ 3 := hℓ.dvd_of_dvd_pow h2
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h3)
  obtain ⟨N, hNn, hNcop, k, hk⟩ :=
    ((CFSG.GroupTheory.frobenius_normal_p_complement 3).1).mpr hfrob
  have hq3 : IsPGroup 3 (Z ⧸ N) := IsPGroup.of_card (n := k) (by
    rw [← Subgroup.index_eq_card, hk])
  have hqp : Group.IsPerfect (Z ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hNtop : N = ⊤ := by
    by_contra hne
    have : Nontrivial (Z ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    have : Group.IsNilpotent (Z ⧸ N) := hq3.isNilpotent
    exact Group.IsPerfect.not_isSolvable (Z ⧸ N) inferInstance
  rw [hNtop, Subgroup.card_top] at hNcop
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hNcop.symm hZ3

theorem exists_pow_three_eq_one_not_mem {Z B : Subgroup G} (hZp : Group.IsPerfect Z)
    (hZ3 : 3 ∣ Nat.card Z) (hBZ : B ≤ Subgroup.centralizer (Z : Set G)) :
    ∃ e ∈ Z, e ^ 3 = 1 ∧ e ∉ B := by
  obtain ⟨e, he3, heZ⟩ := exists_pow_three_eq_one_not_mem_center hZp hZ3
  refine ⟨e, e.2, by simpa using congrArg Subtype.val he3, fun heB => heZ ?_⟩
  rw [Subgroup.mem_center_iff]
  intro z
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp (hBZ heB) z z.2)

omit [Finite G] in
theorem le_normalizer_residual (X : Subgroup G) :
    X ≤ Subgroup.normalizer (inSubgroup perfectResidual X : Set G) :=
  Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

omit [Finite G] in
theorem isSubnormal_residual_subgroupOf {M X : Subgroup G} (hX : (X.subgroupOf M).IsSubnormal) :
    ((inSubgroup perfectResidual X).subgroupOf M).IsSubnormal := by
  have hRX : inSubgroup perfectResidual X ≤ X := inSubgroup_perfectResidual_le X
  have hle : (inSubgroup perfectResidual X).subgroupOf M ≤ X.subgroupOf M :=
    Subgroup.subgroupOf_mono M hRX
  refine Subgroup.IsSubnormal.trans hle ?_ hX
  apply Subgroup.Normal.isSubnormal
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hk' : (k : G) ∈ X := Subgroup.mem_subgroupOf.mp hk
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (le_normalizer_residual X hk') h

theorem residual_inf_centralizer_mem_thetaComponentsIn {a : G} {L D : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 a) (hD3 : IsPGroup 3 D) (hDC : D ≤ thetaQuotCentralizer L) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G)) ∈
      thetaComponentsIn (Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer {a}) := by
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsIn_iff.mp hL
  set M := Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer {a} with hM
  set X := L ⊓ Subgroup.centralizer (D : Set G) with hX
  have hXM : X ≤ M := le_inf inf_le_right (inf_le_left.trans hLC)
  have hXsn : (X.subgroupOf M).IsSubnormal := by
    have heq : X.subgroupOf M =
        (L.subgroupOf (Subgroup.centralizer {a})).comap
          (Subgroup.inclusion (inf_le_right : M ≤ Subgroup.centralizer {a})) := by
      ext m
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion]
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, m.2.1⟩
    rw [heq]
    exact hL'.2.1.comap _
  exact mem_thetaComponentsIn_of ((inSubgroup_perfectResidual_le X).trans hXM)
    (isPerfect_inSubgroup_perfectResidual X) (isSubnormal_residual_subgroupOf hXsn)
    (isQuasisimple_residual_inf_centralizer (isPerfect_of_mem_thetaComponentsAt hL)
      (isQuasisimple_of_mem_thetaComponentsAt hL) hD3 hDC)

theorem exists_card_eq_of_mem_partTwoF {A : Subgroup G} (hA : A ∈ partTwoF G) :
    ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (Sec5.isPGroup_of_isElemAbelian hA.1).exists_card_eq
  obtain ⟨E, hE, hEA⟩ := hA.2.2
  have hdvd : 3 ^ 3 ∣ 3 ^ n := by
    rw [← hn, show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2.1]
    exact Subgroup.card_dvd_of_le hEA
  exact ⟨n, (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd, hn⟩

omit [Finite G] in
theorem centralizer_zpowers_eq (b : G) :
    Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) =
      Subgroup.centralizer ({b} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem exists_mem_thetaComponentsAt_residual_le (h48 : Sec4.Item4_8) (hG : PartTwoStanding G)
    {A : Subgroup G} (hA : A ∈ partTwoF G) {a b : G} (haA : a ∈ A) (ha1 : a ≠ 1) (hbA : b ∈ A)
    (hb1 : b ≠ 1) {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 a)
    (hb : b ∈ thetaQuotCentralizer L) :
    ∃ K ∈ thetaComponentsAt 3 b,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) ≤ K := by
  have hAab := hA.1
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hD3 : IsPGroup 3 (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_three hb3
  have hDC : Subgroup.zpowers b ≤ thetaQuotCentralizer L := Subgroup.zpowers_le.mpr hb
  have hY := residual_inf_centralizer_mem_thetaComponentsIn hL hD3 hDC
  rw [centralizer_zpowers_eq] at hY
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))
  have hM : SectionFourHyp (Subgroup.centralizer ({b} : Set G)) :=
    hG.toTheoremFourHyp.sectionFourHyp (centralizer_ne_top_of_ne_one hG.toTheoremFourHyp hb1)
  obtain ⟨K, hK, hJK⟩ := exists_le_mem_thetaComponentsIn h48 hM hAb hAab
    (exists_card_eq_of_mem_partTwoF hA) haA ha1 hY
  refine ⟨K, hK, le_of_isPerfect_of_le_sup_theta hK (isPerfect_inSubgroup_perfectResidual _) ?_⟩
  refine (le_perfectResidual_sup (isPerfect_inSubgroup_perfectResidual _)
    (inf_le_right.trans (le_normalizer_theta _)) (inSubgroup_perfectResidual_le _)).trans ?_
  exact sup_le_sup_right hJK _

theorem le_thetaQuotCentralizer_of_residual_eq {b : G} {L B K : Subgroup G}
    (hBC : B ≤ thetaQuotCentralizer L)
    (hBb : B ≤ Subgroup.centralizer {b}) (hK : K ∈ thetaComponentsAt 3 b)
    (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (heq : inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) = K) :
    B ≤ thetaQuotCentralizer K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.centralizer ({b} : Set G) with hH
  set θH := inSubgroup (aschbacherSolvableCore 3) H with hθH
  set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set J := inSubgroup perfectResidual (L ⊓ H) with hJ
  have hJLH : J ≤ L ⊓ H := inSubgroup_perfectResidual_le _
  have hJK : J ≤ K := heq ▸ inSubgroup_perfectResidual_mono le_sup_left
  have hKJ : K ≤ J ⊔ θH := by
    rw [← heq]
    exact le_perfectResidual_sup (isPerfect_inSubgroup_perfectResidual _)
      (inf_le_right.trans (le_normalizer_theta H)) (inSubgroup_perfectResidual_le _)
  have hθKeq : θK = K ⊓ θH := theta_eq_inf_of_mem_thetaComponentsAt hK
  have hdec : ∀ k ∈ K, ∃ j ∈ J, ∃ t ∈ θK, k = j * t := by
    intro k hk
    have hk' : k ∈ (J : Set G) * (θH : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right J θH
        ((hJLH.trans inf_le_right).trans (le_normalizer_theta H))]
      exact hKJ hk
    obtain ⟨j, hj, t, ht, rfl⟩ := hk'
    refine ⟨j, hj, t, ?_, rfl⟩
    rw [hθKeq]
    refine ⟨?_, ht⟩
    have := K.mul_mem (K.inv_mem (hJK hj)) hk
    simpa using this
  have hJθ : J ⊓ θL ≤ θK := by
    set N := (J ⊓ θL) ⊔ θK with hN
    have hθKK : θK ≤ K := theta_le K
    have hNK : N ≤ K := sup_le (inf_le_left.trans hJK) hθKK
    have hJN : J ≤ Subgroup.normalizer (N : Set G) := by
      apply le_normalizer_sup_of_conj
      · intro j hj x hx
        refine Subgroup.mem_sup_left ⟨?_, ?_⟩
        · exact J.mul_mem (J.mul_mem hj hx.1) (J.inv_mem hj)
        · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta L (hJLH hj).1) x).mp hx.2
      · intro j hj x hx
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta K (hJK hj)) x).mp hx)
    have hθKN : θK ≤ Subgroup.normalizer (N : Set G) := by
      apply le_normalizer_sup_of_conj
      · intro t ht x hx
        have hxK : x ∈ K := hJK hx.1
        have h1 : x⁻¹ * t * x⁻¹⁻¹ ∈ θK :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta K (K.inv_mem hxK)) t).mp ht
        rw [show t * x * t⁻¹ = x * ((x⁻¹ * t * x⁻¹⁻¹) * t⁻¹) by group]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
          (Subgroup.mem_sup_right (θK.mul_mem h1 (θK.inv_mem ht)))
      · intro t ht x hx
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta K (theta_le K ht)) x).mp hx)
    have hKN : K ≤ Subgroup.normalizer (N : Set G) := by
      intro k hk
      obtain ⟨j, hj, t, ht, rfl⟩ := hdec k hk
      exact Subgroup.mul_mem _ (hJN hj) (hθKN ht)
    have hJθN : J ⊓ θL ≤ Subgroup.normalizer (θK : Set G) :=
      (inf_le_left.trans hJK).trans (le_normalizer_theta K)
    have hsolθL := (theta_solvable_and_not_dvd L).1
    have hsolJθ : Group.IsSolvable (J ⊓ θL : Subgroup G) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_right)
        (Subgroup.inclusion_injective _)
    have hNsol : Group.IsSolvable N := by
      have h := isSolvable_sup_of_le_normalizer hJθN (theta_solvable_and_not_dvd K).1 hsolJθ
      rwa [sup_comm] at h
    have hN3 : ¬ 3 ∣ Nat.card N := by
      have h3 : ¬ 3 ∣ Nat.card (J ⊓ θL : Subgroup G) := fun h =>
        (theta_solvable_and_not_dvd L).2 (h.trans (Subgroup.card_dvd_of_le inf_le_right))
      exact not_dvd_card_sup Nat.prime_three hJθN h3 (theta_solvable_and_not_dvd K).2
    exact le_sup_left.trans (le_theta_of_normal hNK hKN hNsol hN3)
  intro β hβ
  have hβK := hBK hβ
  have hβL := thetaQuotCentralizer_le_normalizer L (hBC hβ)
  refine mem_thetaQuotCentralizer_iff.mpr ⟨hβK, fun k hk => ?_⟩
  obtain ⟨j, hj, t, ht, rfl⟩ := hdec k hk
  have hβJ : β * j * β⁻¹ ∈ J := by
    have hβLH : β ∈ Subgroup.normalizer ((L ⊓ H : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hβL, Subgroup.le_normalizer (hBb hβ)⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _ hβLH) j).mp hj
  have h1 : j⁻¹ * (β * j * β⁻¹) ∈ θK := by
    refine hJθ ⟨J.mul_mem (J.inv_mem hj) hβJ, ?_⟩
    exact (mem_thetaQuotCentralizer_iff.mp (hBC hβ)).2 j (hJLH hj).1
  have h2 : β * t * β⁻¹ ∈ θK :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_theta K hβK) t).mp ht
  have e : (j * t)⁻¹ * (β * (j * t) * β⁻¹) = t⁻¹ * (j⁻¹ * (β * j * β⁻¹)) * (β * t * β⁻¹) := by
    group
  rw [e]
  exact θK.mul_mem (θK.mul_mem (θK.inv_mem ht) h1) h2

theorem theta_eq_inf_of_mem_thetaComponentsIn {M K : Subgroup G} (hK : K ∈ thetaComponentsIn M) :
    inSubgroup (aschbacherSolvableCore 3) K = K ⊓ inSubgroup (aschbacherSolvableCore 3) M := by
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  have h1 := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hK'.2.1
  have h2 := congrArg (Subgroup.map M.subtype) h1
  have e1 := map_inSubgroup_theta_of_injective M.subtype M.subtype_injective (K.subgroupOf M)
  rw [Subgroup.map_subgroupOf_eq_of_le hKM] at e1
  rw [e1, Subgroup.map_inf_eq _ _ M.subtype M.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hKM] at h2
  exact h2

theorem le_normalizer_of_mem_thetaComponentsIn_of_item4_5 (h45 : Sec4.Item4_5) {M : Subgroup G}
    (hM : SectionFourHyp M) {E : Subgroup G} (hEM : E ≤ M) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card E = 3 ^ n) :
    ∀ K ∈ thetaComponentsIn M, E ≤ Subgroup.normalizer (K : Set G) := by
  rintro _ ⟨K', hK', rfl⟩
  have hcomm : ∀ y ∈ E, ∀ z ∈ E, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hE' : CFSG.Assembly.IsElemAbelian 3 (E.subgroupOf M) := by
    refine ⟨⟨⟨fun y z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.mp y.2) _ (Subgroup.mem_subgroupOf.mp z.2)
    · exact Subtype.ext (by simpa using hE.2 _ (Subgroup.mem_subgroupOf.mp hy))
  have hE3 : IsPGroup 3 (E.subgroupOf M) := Sec5.isPGroup_of_isElemAbelian hE'
  obtain ⟨n, hn, hcard⟩ := hEn
  have h := h45 M hM (E.subgroupOf M) hE3 (Or.inr ⟨hE', n, hn, by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hcard]⟩) K' hK'
  intro e he
  exact Subgroup.le_normalizer_map M.subtype ⟨⟨e, hEM he⟩, h (Subgroup.mem_subgroupOf.mpr he), rfl⟩

theorem eq_of_mem_thetaComponentsIn_of_le {M K₁ K₂ P : Subgroup G}
    (hK₁ : K₁ ∈ thetaComponentsIn M) (hK₂ : K₂ ∈ thetaComponentsIn M) (hP : Group.IsPerfect P)
    (hP1 : P ≠ ⊥) (hP₁ : P ≤ K₁) (hP₂ : P ≤ K₂) : K₁ = K₂ := by
  obtain ⟨hK₁M, hK₁'⟩ := mem_thetaComponentsIn_iff.mp hK₁
  obtain ⟨hK₂M, hK₂'⟩ := mem_thetaComponentsIn_iff.mp hK₂
  have hPM : P ≤ M := hP₁.trans hK₁M
  have hP' : Group.IsPerfect (P.subgroupOf M) := by
    have := hP
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hPM).symm.toMonoidHom) (MulEquiv.surjective _)
  have hP'1 : P.subgroupOf M ≠ ⊥ := by
    intro h
    apply hP1
    rw [← Subgroup.map_subgroupOf_eq_of_le hPM, h, Subgroup.map_bot]
  have h := theta_component_eq_of_perfect_le Nat.prime_three hK₁' hK₂' hP'1 hP'
    (Subgroup.subgroupOf_mono M hP₁) (Subgroup.subgroupOf_mono M hP₂)
  rw [← Subgroup.map_subgroupOf_eq_of_le hK₁M, ← Subgroup.map_subgroupOf_eq_of_le hK₂M, h]

omit [Finite G] in
theorem centralizer_sup_eq (H K : Subgroup G) :
    Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) =
      Subgroup.centralizer (H : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))
  · rintro x ⟨hxH, hxK⟩
    rw [Subgroup.mem_centralizer_iff]
    have hle : H ⊔ K ≤ Subgroup.centralizer ({x} : Set G) := sup_le
      (fun h hh => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxH h hh))
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxK k hk))
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem exists_centralizer_eq_inf {B : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) {a : G} (haB : a ∈ B) (ha1 : a ≠ 1) :
    ∃ a' ∈ B, a' ≠ 1 ∧ a' ∉ Subgroup.zpowers a ∧
      Subgroup.centralizer (B : Set G) =
        Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({a'} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hB.2 a haB) ha1
  have hza : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha3]
  have hlt : Subgroup.zpowers a < B := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr haB) fun h => ?_
    rw [h, hB9] at hza
    norm_num at hza
  obtain ⟨a', ha'B, ha'z⟩ := IsConcreteLE.exists_of_lt hlt
  have ha'1 : a' ≠ 1 := fun h => ha'z (h ▸ Subgroup.one_mem _)
  have hzab : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers a) :=
    Sec5.isElemAbelian_of_le hB (Subgroup.zpowers_le.mpr haB)
  obtain ⟨-, hcard⟩ := Sec5.isElemAbelian_sup_zpowers hzab ha'z (hB.2 a' ha'B) (fun x hx =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, Subgroup.zpowers_le.mpr haB hx⟩ ⟨a', ha'B⟩))
  have hBeq : Subgroup.zpowers a ⊔ Subgroup.zpowers a' = B :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr haB) (Subgroup.zpowers_le.mpr ha'B))
      (by rw [hcard, hza, hB9])
  refine ⟨a', ha'B, ha'1, ha'z, ?_⟩
  rw [← hBeq, centralizer_sup_eq, centralizer_zpowers_eq, centralizer_zpowers_eq]

end CFSG.RankThree.PartTwo.Sec6
