module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Thm90Q
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank

section Y

variable {Y : Type} [Group Y] [Finite Y]

theorem comm_mem_of_ne {p : ℕ} (hp : p.Prime) {L₁ L₂ : Subgroup Y}
    (hL₁ : L₁ ∈ thetaComponents p Y) (hL₂ : L₂ ∈ thetaComponents p Y) (hne : L₁ ≠ L₂)
    {a b : Y} (ha : a ∈ L₁) (hb : b ∈ L₂) :
    a * b * a⁻¹ * b⁻¹ ∈ aschbacherSolvableCore p Y := by
  set N := aschbacherSolvableCore p Y
  set π := QuotientGroup.mk' N
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := Y) hp
  have hK₁ := isComponent_map_of_mem_thetaComponents hp hL₁
  have hK₂ := isComponent_map_of_mem_thetaComponents hp hL₂
  have hKne : L₁.map π ≠ L₂.map π := fun h => hne (hbij.injOn hL₁ hL₂ h)
  have hcomm := (LocalCores.distinct_components_commute hK₁ hK₂).resolve_left hKne
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have h1 : π b * π a = π a * π b :=
    Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_map_of_mem π ha)) (π b)
      (Subgroup.mem_map_of_mem π hb)
  refine (QuotientGroup.eq_one_iff _).mp ?_
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv]
  refine mul_inv_eq_one.mpr ?_
  rw [show (a : Y ⧸ N) * (b : Y ⧸ N) = (b : Y ⧸ N) * (a : Y ⧸ N) from h1.symm,
    mul_inv_cancel_right]

theorem mem_thetaQuotCentralizer_iff' {Λ : Subgroup Y} {x : Y} :
    x ∈ Sec4.thetaQuotCentralizer Λ ↔ ∃ hx : x ∈ Subgroup.normalizer (Λ : Set Y),
      Sec4.thetaQuotMulAut ↥Λ (Λ.normalizerMonoidHom ⟨x, hx⟩) = 1 := by
  constructor
  · rintro ⟨⟨x', hx'⟩, hk, rfl⟩
    exact ⟨hx', hk⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem comm_mem_of_mem_thetaQuotCentralizer {Λ : Subgroup Y} (hΛ : Λ.IsSubnormal) {x : Y}
    (hx : x ∈ Sec4.thetaQuotCentralizer Λ) {m : Y} (hm : m ∈ Λ) :
    x * m * x⁻¹ * m⁻¹ ∈ aschbacherSolvableCore 3 Y := by
  obtain ⟨hxN, hx1⟩ := mem_thetaQuotCentralizer_iff'.mp hx
  have h1 := congrArg (fun σ : MulAut (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ) =>
    σ ((⟨m, hm⟩ : ↥Λ) : ↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ)) hx1
  simp only [Sec4.thetaQuotMulAut_mk, MulAut.one_apply] at h1
  have h2 := QuotientGroup.eq.mp h1
  rw [aschbacherSolvableCore_eq_subgroupOf Nat.prime_three hΛ, Subgroup.mem_subgroupOf] at h2
  change (x * m * x⁻¹)⁻¹ * m ∈ aschbacherSolvableCore 3 Y at h2
  have h4 : m * ((x * m * x⁻¹)⁻¹ * m)⁻¹ * m⁻¹ ∈ aschbacherSolvableCore 3 Y :=
    Subgroup.Normal.conj_mem inferInstance _ ((aschbacherSolvableCore 3 Y).inv_mem h2) m
  have h5 : m * ((x * m * x⁻¹)⁻¹ * m)⁻¹ * m⁻¹ = x * m * x⁻¹ * m⁻¹ := by group
  rwa [h5] at h4

theorem false_of_acts {J : Type} [Group J] (hJ : J2Facts J) (hK9 : K9For J)
    (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover) (hY : SectionFourHyp Y)
    {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y) {c : Y}
    (hcN : c ∈ Subgroup.normalizer (Λ : Set Y)) (hc3 : c ^ 3 = 1)
    (hc : c ∉ Sec4.thetaQuotCentralizer Λ) {M : Subgroup Y}
    (hMc : M ≤ Subgroup.centralizer ({c} : Set Y))
    (hMsub : (M.subgroupOf (Subgroup.centralizer ({c} : Set Y))).IsSubnormal)
    (hMperf : Group.IsPerfect M) (hMΛ : M ≤ Λ) (φ : M →* J) (hφ : Function.Surjective φ) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θY := aschbacherSolvableCore 3 Y with hθY
  set θΛ := aschbacherSolvableCore 3 ↥Λ with hθΛ
  have hθΛY : θΛ = θY.subgroupOf Λ :=
    aschbacherSolvableCore_eq_subgroupOf Nat.prime_three hΛ.2.1
  let τ : MulAut ↥Λ := Λ.normalizerMonoidHom ⟨c, hcN⟩
  have hτ : ∀ l : ↥Λ, ((τ l : ↥Λ) : Y) = c * (l : Y) * c⁻¹ := fun l => rfl
  have hτ3 : τ ^ 3 = 1 := by
    have h : (⟨c, hcN⟩ : Subgroup.normalizer (Λ : Set Y)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    rw [← map_pow, h, map_one]
  let σ : MulAut (↥Λ ⧸ θΛ) := Sec4.thetaQuotMulAut ↥Λ τ
  have hσmk : ∀ l : ↥Λ, σ (l : ↥Λ ⧸ θΛ) = ((τ l : ↥Λ) : ↥Λ ⧸ θΛ) := fun l => rfl
  have hσ3 : σ ^ 3 = 1 := by rw [← map_pow, hτ3, map_one]
  have hσ1 : σ ≠ 1 := fun h => hc (mem_thetaQuotCentralizer_iff'.mpr ⟨hcN, h⟩)
  have hθτ : ∀ n ∈ θΛ, τ n ∈ θΛ := fun n hn => by
    have h := Sec4.map_aschbacherSolvableCore τ
    have h' : τ n ∈ (aschbacherSolvableCore 3 ↥Λ).map (τ : ↥Λ →* ↥Λ) :=
      Subgroup.mem_map_of_mem (τ : ↥Λ →* ↥Λ) hn
    rw [h] at h'
    exact h'
  have hfix : fixedSubgroup σ = (fixedSubgroup τ).map (QuotientGroup.mk' θΛ) := by
    refine le_antisymm (fun y hy => ?_) ?_
    · obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
      have h1' : σ (l : ↥Λ ⧸ θΛ) = (l : ↥Λ ⧸ θΛ) := mem_fixedSubgroup.mp hy
      rw [hσmk] at h1'
      have h2' : l⁻¹ * τ l ∈ θΛ := QuotientGroup.eq.mp h1'.symm
      obtain ⟨n, hn, hnfix⟩ := exists_mul_fixed (p := 3) τ hτ3 θΛ hθτ
        three_not_dvd_card_aschbacherSolvableCore l h2'
      refine ⟨l * n, mem_fixedSubgroup.mpr hnfix, ?_⟩
      change ((l * n : ↥Λ) : ↥Λ ⧸ θΛ) = (l : ↥Λ ⧸ θΛ)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, mul_one]
    · rintro _ ⟨l, hl, rfl⟩
      refine mem_fixedSubgroup.mpr ?_
      change σ (l : ↥Λ ⧸ θΛ) = (l : ↥Λ ⧸ θΛ)
      rw [hσmk, mem_fixedSubgroup.mp hl]
  set P : Subgroup (↥Λ ⧸ θΛ) := (M.subgroupOf Λ).map (QuotientGroup.mk' θΛ) with hP
  have hMfix : M.subgroupOf Λ ≤ fixedSubgroup τ := fun m hm => by
    have hmc : (m : Y) * c = c * (m : Y) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hMc (Subgroup.mem_subgroupOf.mp hm))
    refine mem_fixedSubgroup.mpr (Subtype.ext ?_)
    rw [hτ, ← hmc, mul_inv_cancel_right]
  have hPfix : ∀ y ∈ P, σ y = y := by
    rintro _ ⟨m, hm, rfl⟩
    have h : (QuotientGroup.mk' θΛ) m ∈ fixedSubgroup σ := by
      rw [hfix]
      exact Subgroup.mem_map_of_mem _ (hMfix hm)
    exact mem_fixedSubgroup.mp h
  have hMΛperf : Group.IsPerfect (M.subgroupOf Λ) := by
    have := hMperf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hMΛ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hMΛ).symm.surjective
  haveI : Group.IsPerfect (M.subgroupOf Λ) := hMΛperf
  have hPperf : Group.IsPerfect P := Group.IsPerfect.map (QuotientGroup.mk' θΛ)
  have hsub1 : SubnormalIn M (Subgroup.centralizer ({c} : Set Y)) := hMsub
  have hsub2 := SubnormalIn.subgroupOf Λ (inf_le_right : Subgroup.centralizer ({c} : Set Y) ⊓ Λ ≤ Λ)
    (SubnormalIn.inf Λ hsub1)
  rw [inf_eq_left.mpr hMΛ] at hsub2
  have hcent : (Subgroup.centralizer ({c} : Set Y) ⊓ Λ).subgroupOf Λ = fixedSubgroup τ := by
    ext l
    constructor
    · intro hl
      have hlc : (l : Y) * c = c * (l : Y) :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hl)).1
      refine mem_fixedSubgroup.mpr (Subtype.ext ?_)
      rw [hτ, ← hlc, mul_inv_cancel_right]
    · intro hl
      have hl' : c * (l : Y) * c⁻¹ = l := by
        have := congrArg Subtype.val (mem_fixedSubgroup.mp hl)
        rwa [hτ] at this
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, l.2⟩)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (l : Y) * c = (c * (l : Y) * c⁻¹) * c := by rw [hl']
        _ = c * (l : Y) := inv_mul_cancel_right _ _
  rw [hcent] at hsub2
  have hsub3 : SubnormalIn P (fixedSubgroup σ) := by
    rw [hfix]
    exact SubnormalIn.map hMfix (QuotientGroup.mk' θΛ) hsub2
  haveI hθsol : Group.IsSolvable θY :=
    (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).1
  have hker0 : θY.subgroupOf M ≤ φ.ker :=
    hJ.le_ker_of_normalizes M θY hθsol
      (fun m _ k hk => Subgroup.Normal.conj_mem inferInstance k hk m) φ hφ
  let φ' : ↥(M.subgroupOf Λ) →* J := φ.comp (Subgroup.subgroupOfEquivOfLe hMΛ).toMonoidHom
  have hφ' : Function.Surjective φ' := hφ.comp (Subgroup.subgroupOfEquivOfLe hMΛ).surjective
  have hker : ((QuotientGroup.mk' θΛ).subgroupMap (M.subgroupOf Λ)).ker ≤ φ'.ker := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm ⊢
    have h1' : (QuotientGroup.mk' θΛ) (m : ↥Λ) = 1 := congrArg Subtype.val hm
    have h2' : (m : ↥Λ) ∈ θΛ := (QuotientGroup.eq_one_iff _).mp h1'
    rw [hθΛY, Subgroup.mem_subgroupOf] at h2'
    have h3 : (⟨((m : ↥Λ) : Y), Subgroup.mem_subgroupOf.mp m.2⟩ : ↥M) ∈ θY.subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr h2'
    exact hker0 h3
  obtain ⟨ψ, hψ⟩ := exists_lift_of_surjective _ (MonoidHom.subgroupMap_surjective _ _) φ' hker
  have hψs : Function.Surjective ψ := by
    intro j
    obtain ⟨m, rfl⟩ := hφ' j
    exact ⟨_, hψ m⟩
  have hX : CFSG.IsQuasisimple (↥Λ ⧸ θΛ) := hΛ.2.2
  have hS : SectionFourHyp ((↥Λ ⧸ θΛ) ⧸ Subgroup.center (↥Λ ⧸ θΛ)) :=
    Sec4.Item41Narrow.sectionFourHyp_quotient_center h1 h2
      (Sec4.Item41Narrow.sectionFourHyp_thetaQuotient h1 hY hΛ) hX
  exact false_of_perfect_fixed hJ hK9 hX hS σ hσ3 hσ1 P hPfix hPperf hsub3 ψ hψs

theorem false_of_two_points {J : Type} [Group J] (hJ : J2Facts J) (hK9 : K9For J)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (hY : SectionFourHyp Y)
    {A : Subgroup Y} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    {c c' d : Y} (hc : c ∈ A) (hc' : c' ∈ A) (hc1 : c ≠ 1) (hc1' : c' ≠ 1)
    (hd : d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers c')
    {M M' : Subgroup Y} (hM : M ∈ thetaComponentsAt 3 c) (hM' : M' ∈ thetaComponentsAt 3 c')
    (hdM : d ∈ M) (hdM' : d ∈ M') (φ : M →* J) (hφ : Function.Surjective φ)
    (hφd : φ ⟨d, hdM⟩ ≠ 1) (φ' : M' →* J) (hφ' : Function.Surjective φ') : False := by
  have hApG : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 (g : Y) g.2)⟩
  have hn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n := ⟨3, le_rfl, by rw [hA27]; norm_num⟩
  obtain ⟨Λ₁, hΛ₁, hMΛ₁⟩ := h48 Y hY A hA hn c hc hc1 M hM
  obtain ⟨Λ₂, hΛ₂, hMΛ₂⟩ := h48 Y hY A hA hn c' hc' hc1' M' hM'
  have hAN : ∀ Λ ∈ thetaComponents 3 Y, A ≤ Subgroup.normalizer (Λ : Set Y) := fun Λ hΛ =>
    h45 Y hY A hApG (Or.inr ⟨hA, hn⟩) Λ hΛ
  haveI hθY : (aschbacherSolvableCore 3 Y).Normal := inferInstance
  have hθsol : Group.IsSolvable (aschbacherSolvableCore 3 Y) :=
    (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).1
  have crit : (∀ m : M, (d : Y) * m * (d : Y)⁻¹ * (m : Y)⁻¹ ∈ aschbacherSolvableCore 3 Y) →
      False := fun hcomm =>
    hφd (hJ.eq_one_of_commutators_mem M (aschbacherSolvableCore 3 Y) hθsol
      (fun m _ k hk => Subgroup.Normal.conj_mem inferInstance k hk m) φ hφ ⟨d, hdM⟩ hcomm)
  have hΛeq : Λ₁ = Λ₂ := by
    by_contra hne
    exact crit fun m => comm_mem_of_ne Nat.prime_three hΛ₂ hΛ₁ (Ne.symm hne) (hMΛ₂ hdM')
      (hMΛ₁ m.2)
  rw [← hΛeq] at hΛ₂ hMΛ₂
  obtain ⟨hMc, hMsub, hMperf⟩ := thetaComponentsAt_facts hM
  obtain ⟨hMc', hMsub', hMperf'⟩ := thetaComponentsAt_facts hM'
  by_cases hcc : c ∈ Sec4.thetaQuotCentralizer Λ₁
  · by_cases hcc' : c' ∈ Sec4.thetaQuotCentralizer Λ₁
    · have hdT : d ∈ Sec4.thetaQuotCentralizer Λ₁ :=
        (sup_le (Subgroup.zpowers_le.mpr hcc) (Subgroup.zpowers_le.mpr hcc')) hd
      exact crit fun m => comm_mem_of_mem_thetaQuotCentralizer hΛ₁.2.1 hdT (hMΛ₁ m.2)
    · exact false_of_acts hJ hK9 h1 h2 hY hΛ₁ (hAN Λ₁ hΛ₁ hc') (hA.2 c' hc') hcc' hMc' hMsub'
        hMperf' hMΛ₂ φ' hφ'
  · exact false_of_acts hJ hK9 h1 h2 hY hΛ₁ (hAN Λ₁ hΛ₁ hc) (hA.2 c hc) hcc hMc hMsub hMperf
      hMΛ₁ φ hφ

end Y

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90
