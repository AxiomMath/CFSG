module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofSigma
import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProofUni
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ProofMat
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ProofUni
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ProofFix
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ProofLift
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ProofAut
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec14.Item148OneRepair CFSG.RankThree.PartTwo.Sec14.Item148Res9

namespace Item148Res9

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem thetaQuotMulAut_compAction_of_mem (L : Subgroup Γ) {y : Γ} (hy : y ∈ L) :
    thetaQuotMulAut L (compAction L ⟨y, Subgroup.le_normalizer hy⟩) =
      MulAut.conj ((⟨y, hy⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rw [thetaQuotMulAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem eq_one_of_linear {M : Type} [Group M] {K : Type} [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] (h3 : (3 : K) ≠ 0) (e : M ≃* projectiveSL 3 K) {β : MulAut M}
    (hβD : MulAut.congr e β ∈ linearAutGroup 3 K) {n : ℕ} (hn : (n : K) ≠ 0) (hβn : β ^ n = 1)
    (R : Subgroup M) (hR : IsPGroup p R) (hfix : ∀ r ∈ R, β r = r) {u v : M} (hu : u ∈ R)
    (hv : v ∈ R) (huv : u * v ≠ v * u) : β = 1 := by
  obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.mp hβD
  have h1 := conjAut_eq_one_of_fixes p h3 B hn (by rw [hB, ← map_pow, hβn, map_one])
    (R.map e.toMonoidHom) (hR.map _) (by
      rintro _ ⟨r, hr, rfl⟩
      rw [hB]
      change MulAut.congr e β (e r) = e r
      rw [congr_apply_apply148, hfix r hr]) (Subgroup.mem_map_of_mem _ hu)
    (Subgroup.mem_map_of_mem _ hv) (by
      intro h
      apply huv
      apply e.injective
      simpa using h)
  rw [hB] at h1
  exact (MulAut.congr e).injective (h1.trans (map_one _).symm)

theorem eq_one_of_unitary {M : Type} [Group M] {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (h3 : (3 : K) ≠ 0) (e : M ≃* unitaryPSU h 3) {β : MulAut M}
    (hβD : MulAut.congr e β ∈ (psuConj h).range) {n : ℕ} (hn : (n : K) ≠ 0) (hβn : β ^ n = 1)
    (R : Subgroup M) (hR : IsPGroup p R) (hfix : ∀ r ∈ R, β r = r) {u v : M} (hu : u ∈ R)
    (hv : v ∈ R) (huv : u * v ≠ v * u) : β = 1 := by
  obtain ⟨B, hB⟩ := hβD
  have h1 := psuConj_eq_one_of_fixes h h3 B hn (by rw [hB, ← map_pow, hβn, map_one])
    (R.map e.toMonoidHom) (hR.map _) (by
      rintro _ ⟨r, hr, rfl⟩
      rw [hB]
      change MulAut.congr e β (e r) = e r
      rw [congr_apply_apply148, hfix r hr]) (Subgroup.mem_map_of_mem _ hu)
    (Subgroup.mem_map_of_mem _ hv) (by
      intro h'
      apply huv
      apply e.injective
      simpa using h')
  rw [hB] at h1
  exact (MulAut.congr e).injective (h1.trans (map_one _).symm)

theorem three_ne_zero_of_charP {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp3 : p ≠ 3) : (3 : K) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h')

end Item148Res9

theorem kf148InnerSection_holds : KF148InnerSection := by
  intro Γ _ _ L E K N z p f e' _ hf he' hLp hLiso hEN hE hE27 hcent hz1 hzE hKL hKp hEK hNK
    hKN hEN' X _ hX ψ hψ hker a ha
  have hp : p.Prime := Fact.out
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h0 : 3 ^ (f * e') % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by positivity))
    rcases hLiso with ⟨hq, -⟩ | ⟨hq, -⟩ <;> omega
  have ha3 : a ^ 3 = 1 := hE.2 a ha
  have haK : a ∈ Subgroup.normalizer (K : Set Γ) := hEK ha
  have haN : a ∈ Subgroup.normalizer (N : Set Γ) := hEN' ha
  by_cases hin : IsInnerAut (sectionAut ψ hψ hker haK haN)
  · exact exists_mem_of_isInnerAut_sectionAut ψ hψ hker haK haN hin
  exfalso
  have hα3 := sectionAut_pow_three ψ hψ hker haK haN ha3
  obtain ⟨R, hRp, hRfix, u, hu, v, hv, huv⟩ :=
    exists_fixed_nonabelian_of_isoLThreeMinusPi hf hX hα3 hin
  set U : Subgroup Γ := (R.comap ψ).map K.subtype with hU
  have hmemU : ∀ x : K, (x : Γ) ∈ U ↔ ψ x ∈ R := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hUK : U ≤ K := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hNU : N ≤ U := by
    intro n hn
    have h1 := (hmemU ⟨n, hNK hn⟩).mpr
    refine h1 ?_
    rw [(hker ⟨n, hNK hn⟩).mpr hn]
    exact R.one_mem
  have hUN : U ≤ Subgroup.normalizer (N : Set Γ) := hUK.trans hKN
  have hUp : ∀ y ∈ U, ∃ k : ℕ, y ^ (p ^ k) ∈ N := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hRp ⟨ψ y, hy⟩
    refine ⟨k, ?_⟩
    have h1 : ψ (y ^ (p ^ k)) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    rw [hker] at h1
    simpa using h1
  have hconjK : ∀ x ∈ K, a * x * a⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp haK x).mp hx
  have hψa : ∀ x : K, ψ x ∈ R → ψ ⟨a * x * a⁻¹, hconjK x x.2⟩ = ψ x := by
    intro x hx
    rw [← sectionAut_apply' ψ hψ hker haK haN (x := x) rfl]
    exact hRfix _ hx
  have hfixU : ∀ y ∈ U, a * y * a⁻¹ * y⁻¹ ∈ N := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : ψ (⟨a * y * a⁻¹, hconjK y y.2⟩ * y⁻¹) = 1 := by
      rw [map_mul, hψa y hy, map_inv, mul_inv_cancel]
    rw [hker] at h1
    simpa using h1
  have haU : a ∈ Subgroup.normalizer (U : Set Γ) := by
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨y, hy, rfl⟩
    refine (hmemU ⟨_, hconjK y y.2⟩).mpr ?_
    rw [hψa y hy]
    exact hy
  obtain ⟨b, hbU, ⟨s, hbs⟩, P, hPU, hPp, hlift⟩ :=
    exists_centralizing_lift hNU hUN hp3 hUp haU haN ha3 hfixU
  obtain ⟨ku, rfl⟩ := hψ u
  obtain ⟨kv, rfl⟩ := hψ v
  obtain ⟨c₁, hc₁P, hc₁b, hc₁⟩ := hlift _ ((hmemU ku).mpr hu)
  obtain ⟨c₂, hc₂P, hc₂b, hc₂⟩ := hlift _ ((hmemU kv).mpr hv)
  have hc₁K : c₁ ∈ K := hUK (hPU hc₁P)
  have hc₂K : c₂ ∈ K := hUK (hPU hc₂P)
  have hψc : ∀ {c : Γ} (hc : c ∈ K) {k : K}, c⁻¹ * k ∈ N → ψ ⟨c, hc⟩ = ψ k := by
    intro c hc k hck
    have h1 : ψ (⟨c, hc⟩⁻¹ * k) = 1 := (hker _).mpr hck
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have hψc₁ := hψc hc₁K hc₁
  have hψc₂ := hψc hc₂K hc₂
  have : Group.IsPerfect K := hKp
  have hKθ : ∀ x : K, (x : Γ) ∈ thetaIn L → (x : Γ) ∈ N := fun x hx =>
    mem_of_mem_thetaIn hKL hf hX ψ hψ hker hx
  have hy : a⁻¹ * b ∈ L := hKL (hUK hbU)
  have hbL : b ∈ Subgroup.normalizer (L : Set Γ) := by
    have : b = a * (a⁻¹ * b) := by group
    rw [this]
    exact Subgroup.mul_mem _ (hEN ha) (Subgroup.le_normalizer hy)
  set β := thetaQuotMulAut L (compAction L ⟨b, hbL⟩) with hβ
  have hβdecomp : β = thetaQuotMulAut L (compAction L ⟨a, hEN ha⟩) *
      MulAut.conj ((⟨a⁻¹ * b, hy⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
    rw [← thetaQuotMulAut_compAction_of_mem L hy, ← map_mul, ← map_mul, hβ]
    congr 2
    apply Subtype.ext
    change b = a * (a⁻¹ * b)
    group
  set u' : L ⧸ aschbacherSolvableCore 3 L := QuotientGroup.mk (⟨c₁, hKL hc₁K⟩ : L) with hu'
  set v' : L ⧸ aschbacherSolvableCore 3 L := QuotientGroup.mk (⟨c₂, hKL hc₂K⟩ : L) with hv'
  have hβfix : ∀ {c : Γ} (hc : c ∈ L), b * c = c * b →
      β ((⟨c, hc⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((⟨c, hc⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
    intro c hc hcb
    rw [hβ, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    change b * c * b⁻¹ = c
    rw [hcb, mul_inv_cancel_right]
  set Pb : Subgroup Γ := P ⊓ Subgroup.centralizer {b} with hPb
  set Rb : Subgroup (L ⧸ aschbacherSolvableCore 3 L) :=
    (Pb.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) with hRb
  have hRbp : IsPGroup p Rb := by
    refine IsPGroup.map (fun x => ?_) _
    obtain ⟨k, hk⟩ := hPp ⟨(x : L), (Subgroup.mem_subgroupOf.mp x.2).1⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hmemPb : ∀ {c : Γ}, c ∈ P → b * c = c * b → c ∈ Pb := fun hcP hcb =>
    ⟨hcP, Subgroup.mem_centralizer_singleton_iff.mpr hcb.symm⟩
  have hu'R : u' ∈ Rb :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hmemPb hc₁P hc₁b))
  have hv'R : v' ∈ Rb :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hmemPb hc₂P hc₂b))
  have hRbfix : ∀ r ∈ Rb, β r = r := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_subgroupOf.mp hx
    have hxb : b * (x : Γ) = x * b :=
      (Subgroup.mem_centralizer_singleton_iff.mp hx'.2).symm
    exact hβfix x.2 hxb
  have huv' : u' * v' ≠ v' * u' := by
    intro h
    rw [hu', hv', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      ← mem_thetaIn_iff] at h
    have h1 := hKθ ⟨_, K.mul_mem (K.inv_mem (K.mul_mem hc₁K hc₂K)) (K.mul_mem hc₂K hc₁K)⟩ h
    have h2 : ψ ((⟨c₁, hc₁K⟩ * ⟨c₂, hc₂K⟩)⁻¹ * (⟨c₂, hc₂K⟩ * ⟨c₁, hc₁K⟩)) = 1 :=
      (hker _).mpr h1
    rw [map_mul, map_inv, inv_mul_eq_one, map_mul, map_mul, hψc₁, hψc₂] at h2
    exact huv h2
  have hβn : β ^ (3 ^ s) = 1 := by
    rw [hβ, ← map_pow, ← map_pow]
    have : (⟨b, hbL⟩ : Subgroup.normalizer (L : Set Γ)) ^ (3 ^ s) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hbs)
    rw [this, map_one, map_one]
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hin
    have hyK : a⁻¹ * b ∈ K := hUK hbU
    refine ⟨(ψ ⟨a⁻¹ * b, hyK⟩)⁻¹, ?_⟩
    ext w
    obtain ⟨x, rfl⟩ := hψ w
    set y : K := ⟨a⁻¹ * b, hyK⟩ with hydef
    set x' : K := y⁻¹ * x * y with hx'
    have hbx' : b * x' * b⁻¹ ∈ K := by
      have : b * (x' : Γ) * b⁻¹ = a * x * a⁻¹ := by
        simp only [hx', hydef, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this]
      exact hconjK x x.2
    have h2 := congrArg (fun φ : MulAut (L ⧸ aschbacherSolvableCore 3 L) =>
      φ ((⟨x', hKL x'.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)) h1
    simp only [MulAut.one_apply] at h2
    rw [hβ, thetaQuotMulAut_mk, QuotientGroup.eq, ← mem_thetaIn_iff] at h2
    have h3 := hKθ ⟨_, K.mul_mem (K.inv_mem hbx') x'.2⟩ h2
    have h4 : ψ (⟨_, hbx'⟩⁻¹ * x') = 1 := (hker _).mpr h3
    rw [map_mul, map_inv, inv_mul_eq_one] at h4
    rw [MulAut.conj_apply, inv_inv, ← map_inv, ← map_mul, ← map_mul,
      sectionAut_apply' ψ hψ hker haK haN (x := x) (y := ⟨_, hbx'⟩) (by
        simp only [hx', hydef, Subgroup.coe_mul, Subgroup.coe_inv]
        group), h4]
  have hLb : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hfe : 1 ≤ f * e' := Nat.mul_le_mul hf he'
  have hZL : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    kf148CenterL3 _ hLb (Or.inl ⟨p, f * e', inferInstance, hfe, hLiso⟩)
  have hmemD : ∀ {M : Type} [Group M] (eM : L ⧸ aschbacherSolvableCore 3 L ≃* M)
      {D : Subgroup (MulAut M)}, AutFacts148 M D → MulAut.congr eM β ∈ D := by
    intro M _ eM D hD
    rw [hβdecomp, map_mul]
    refine D.mul_mem (inducedAut_mem_of_autFacts148 hEN hE hE27 hcent hz1 hzE eM hD ha) ?_
    rw [congr_mulAutConj]
    exact hD.conj_mem _
  have h3n : ∀ {F : Type} [Field F] [CharP F p], ((3 ^ s : ℕ) : F) ≠ 0 := by
    intro F _ _
    rw [Nat.cast_pow]
    exact pow_ne_zero _ (three_ne_zero_of_charP p hp3)
  rcases hLiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  ·
    obtain ⟨ψm⟩ := nonempty_projSL_mulEquiv 3 (GaloisField p (f * e'))
    set eM := φ.trans ψm with heM
    have hcard : Nat.card (GaloisField p (f * e')) = p ^ (f * e') :=
      GaloisField.card p _ (by omega)
    have hZP : Subgroup.center (projectiveSL 3 (GaloisField p (f * e'))) = ⊥ :=
      center_eq_bot_of_mulEquiv148 eM.symm hZL
    have hD := autFacts148_linear hp hfe hcard hq hZP
    exact hβ1 (eq_one_of_linear p (three_ne_zero_of_charP p hp3) eM (hmemD eM hD) h3n hβn Rb
      hRbp hRbfix hu'R hv'R huv')
  ·
    have h : UnitaryFieldData p (f * e') (GaloisField p (2 * (f * e'))) :=
      ⟨hp, hfe, GaloisField.card p _ (by omega)⟩
    obtain ⟨φ'⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    set eM := φ.trans φ'.symm with heM
    by_cases hQ2 : 2 < p ^ (f * e')
    · have hZP : Subgroup.center (unitaryPSU h 3) = ⊥ := center_eq_bot_of_mulEquiv148 eM.symm hZL
      have hD := autFacts148_unitary h hq hQ2 hZP
      exact hβ1 (eq_one_of_unitary h (three_ne_zero_of_charP p hp3) eM (hmemD eM hD) h3n hβn Rb
        hRbp hRbfix hu'R hv'R huv')
    ·
      have hQ : p ^ (f * e') = 2 := by
        have h2 : 2 ≤ p ^ (f * e') := hp.two_le.trans (Nat.le_self_pow (by omega) p)
        omega
      obtain ⟨hp2, hfe1⟩ := eq_two_one_of_pow_eq_two hp hQ
      subst hp2
      rw [hfe1] at φ
      have hsol : Group.IsSolvable (L ⧸ aschbacherSolvableCore 3 L) := by
        have := isSolvable_projSU_two
        exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
      have hnt : ¬ Nontrivial (L ⧸ aschbacherSolvableCore 3 L) := fun _ =>
        Group.IsPerfect.not_isSolvable _ hsol
      rw [not_nontrivial_iff_subsingleton] at hnt
      exact huv' (Subsingleton.elim _ _)

theorem step148KTypeSigmaThree_holds : Step148KTypeSigmaThree :=
  Item148Res6.step148KTypeSigmaThree_of kf148InnerSection_holds

theorem step148KTypeSigma_holds : Step148KTypeSigma :=
  step148KTypeSigma_of step148KTypeSigmaThree_holds

section Step


theorem step148One_holds :
    Step148One :=
  step148One_of_sigma step148KTypeSigma_holds

end Step

end CFSG.RankThree.PartTwo.Sec14
