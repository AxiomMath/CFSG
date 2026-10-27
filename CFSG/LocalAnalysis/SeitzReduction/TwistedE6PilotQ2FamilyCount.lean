module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilySections
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldFamily

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Generic

variable {H M : Type*} [Group H] [Group M]

theorem map_perfectCore_centralizer_eq [Finite H] [Finite M] (f : H →* M)
    (hker : f.ker ≤ center H) (X : Subgroup H) {MN : Subgroup M} (hMN : ⁅MN, MN⁆ = MN)
    (hMNf : MN ≤ f.range) (hMNX : MN ≤ centralizer ((X.map f : Subgroup M) : Set M))
    (hmax : ∀ Q : Subgroup M, ⁅Q, Q⁆ = Q → Q ≤ f.range →
      Q ≤ centralizer ((X.map f : Subgroup M) : Set M) → Q ≤ MN) :
    (perfectCore (centralizer (X : Set H))).map f = MN := by
  apply le_antisymm
  · refine hmax _ ?_ (map_le_range _ _) ?_
    · rw [← Subgroup.map_commutator, perfectCore_perfect]
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (perfectCore_le _ hy) x hx]
  · set P₁ := perfectCore (MN.comap f) with hP₁
    have hP₁perf : ⁅P₁, P₁⁆ = P₁ := perfectCore_perfect _
    have hP₁map : P₁.map f = MN := by
      rw [hP₁, CFSG.Quasithin.map_perfectCore, Subgroup.map_comap_eq_self hMNf,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect hMN]
    have hcent := le_centralizer_comap_of_perfect_ovl f hker hP₁perf
    have hX : X ≤ (centralizer ((P₁.map f : Subgroup M) : Set M)).comap f := by
      intro x hx
      rw [mem_comap, mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe, hP₁map] at hy
      exact (mem_centralizer_iff.1 (hMNX hy) (f x) ⟨x, hx, rfl⟩).symm
    have hP₁X : P₁ ≤ centralizer (X : Set H) := hcent.trans (centralizer_le hX)
    rw [← hP₁map]
    exact Subgroup.map_mono (le_perfectCore_of_perfect hP₁X hP₁perf)

variable {G : Type*} [Group G]

theorem QCover.E_le_of_card [Finite G] (c : QCover G M) (hE : ⁅c.E, c.E⁆ = c.E)
    {Mc : Subgroup M} (hMc : ∀ y : c.E, c.p y ∈ Mc) (hZ : center Mc = ⊥) {G₀ : Subgroup G}
    (R : Subgroup G₀) (hRE : R.map G₀.subtype ≤ c.E) (f : G₀ →* M) (hf : R.map f = Mc) :
    c.E ≤ G₀ := by
  let ι : R →* c.E := (G₀.subtype.comp R.subtype).codRestrict c.E fun r => hRE ⟨r, r.2, rfl⟩
  let pR : R →* M := c.p.comp ι
  let fR : R →* M := f.comp R.subtype
  have hfR : fR.range = Mc := by
    rw [MonoidHom.range_comp, range_subtype, hf]
  have hker : pR.ker ≤ fR.ker := by
    intro z hz
    have hzc : ι z ∈ center c.E := c.ker_le hz
    have hzR : ∀ r : R, r * z = z * r := fun r => by
      have h := congrArg Subtype.val (mem_center_iff.1 hzc (ι r))
      apply Subtype.ext
      apply Subtype.ext
      exact h
    have hmem : fR z ∈ Mc := hfR ▸ ⟨z, rfl⟩
    have hc : (⟨fR z, hmem⟩ : Mc) ∈ center Mc := by
      rw [mem_center_iff]
      rintro ⟨g, hg⟩
      rw [← hfR] at hg
      obtain ⟨r, rfl⟩ := hg
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul, hzR r]
    rw [hZ, mem_bot] at hc
    exact congrArg Subtype.val hc
  have hcard : Nat.card Mc ≤ Nat.card pR.range := by
    rw [← hfR, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange fR).toEquiv,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivRange pR).toEquiv]
    change fR.ker.index ≤ pR.ker.index
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker)
  have : Finite Mc := by
    rw [← hfR]
    exact Finite.of_surjective _ fR.rangeRestrict_surjective
  have hrange : pR.range = Mc :=
    Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨r, rfl⟩; exact hMc _) hcard
  have hTop : ⁅(⊤ : Subgroup c.E), (⊤ : Subgroup c.E)⁆ = ⊤ :=
    (Subgroup.isPerfect_iff.2 hE).commutator_eq_top
  have hall : ∀ g : c.E, ∃ h ∈ (R.map G₀.subtype).subgroupOf c.E, c.p h = c.p g := by
    intro g
    have hg : c.p g ∈ pR.range := hrange ▸ hMc g
    obtain ⟨r, hr⟩ := hg
    exact ⟨ι r, mem_subgroupOf.2 ⟨r, r.2, rfl⟩, hr⟩
  have htop := E6Pilot.eq_top_of_forall_exists_map_eq_of_perfect hTop c.ker_le hall
  intro x hx
  have hx' : (⟨x, hx⟩ : c.E) ∈ (R.map G₀.subtype).subgroupOf c.E := htop ▸ mem_top _
  obtain ⟨r, -, hr⟩ := mem_subgroupOf.1 hx'
  have hrx : (r : G) = x := hr
  rw [← hrx]
  exact r.2

end Generic

section Levi


variable {K : Type} [Field K]

theorem center_subsystemGroup_setA [CharP K 2] (h2 : (2 : K) = 0) :
    center (subsystemGroup TwistTag.E6.tag K setA) = ⊥ := by
  have hmem : ∀ B, realize h2 B ∈ subsystemGroup TwistTag.E6.tag K setA := fun B => by
    rw [← E6GraphLevi.range_realize h2]
    exact ⟨B, rfl⟩
  set f := (realize h2).codRestrict _ hmem with hf
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← E6GraphLevi.range_realize h2] at hy
    obtain ⟨B, rfl⟩ := hy
    exact ⟨B, rfl⟩
  have hker : f.ker ≤ center (SpecialLinearGroup (Fin 6) K) := by
    rw [hf, MonoidHom.ker_codRestrict]
    exact ker_realize_le_center' h2
  rw [CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple
    (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 5 K (by norm_num)) hsurj hker, eq_bot_iff]
  rintro _ ⟨B, hB, rfl⟩
  rw [mem_bot]
  exact Subtype.ext (center_le_ker_realize h2 hB)

theorem subsystemGroup_setA_perfect (h2 : (2 : K) = 0) :
    ⁅subsystemGroup TwistTag.E6.tag K setA, subsystemGroup TwistTag.E6.tag K setA⁆ =
      subsystemGroup TwistTag.E6.tag K setA := by
  have hP := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := K) (n := 6)
    (by norm_num)
  rw [← E6GraphLevi.range_realize h2, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
    ← commutator_def, hP.commutator_eq_top]

theorem center_map_conj_subsystemGroup_setA [CharP K 2] (h2 : (2 : K) = 0)
    (m : ModGL TwistTag.E6.tag K) :
    center ((subsystemGroup TwistTag.E6.tag K setA).map (MulAut.conj m).toMonoidHom) = ⊥ :=
  F4Pilot.center_eq_bot_congr ((subsystemGroup TwistTag.E6.tag K setA).equivMapOfInjective _
    (MulAut.conj m).injective) (center_subsystemGroup_setA h2)

theorem le_map_conj_subsystemGroup_of_perfect {k : Type} [Field k] [Finite k] [Finite K]
    [CharP K 2] (hk : Nat.card k = 2) (hK : Nat.card K = 2 ^ 2) (ι : k →+* K)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup ι) (hA : Nat.card A = 3)
    {m : ModGL TwistTag.E6.tag K} (hm : m ∈ adjointGroup TwistTag.E6.tag K)
    {Q : Subgroup (ModGL TwistTag.E6.tag K)} (hQ : ⁅Q, Q⁆ = Q)
    (hQC : Q ≤ adjointGroup TwistTag.E6.tag K)
    (hQA : Q ≤ centralizer ((A.map (MulAut.conj m).toMonoidHom : Subgroup _) :
      Set (ModGL TwistTag.E6.tag K))) :
    Q ≤ (subsystemGroup TwistTag.E6.tag K setA).map (MulAut.conj m).toMonoidHom := by
  obtain ⟨a, haA, ha3⟩ := exists_orderOf_eq_three_of_card hA
  set Q' := Q.map (MulAut.conj m⁻¹).toMonoidHom with hQ'
  have hQ'perf : ⁅Q', Q'⁆ = Q' := by rw [hQ', ← Subgroup.map_commutator, hQ]
  have hQ'C : Q' ≤ adjointGroup TwistTag.E6.tag K := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact mul_mem (mul_mem (inv_mem hm) (hQC hx)) hm
  have hQ'a : Q' ≤ centralizer ({a} : Set (ModGL TwistTag.E6.tag K)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    have h1 := mem_centralizer_iff.1 (hQA hx) (m * a * m⁻¹) ⟨a, haA, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc a * (m⁻¹ * x * m) = m⁻¹ * ((m * a * m⁻¹) * x) * m := by group
      _ = m⁻¹ * (x * (m * a * m⁻¹)) * m := by rw [h1]
      _ = m⁻¹ * x * m * a := by group
  have hle := le_subsystemGroup_of_perfect_of_le_centralizer hk hK ι (hAJ haA) ha3 hQ'perf hQ'C
    hQ'a
  intro x hx
  refine ⟨m⁻¹ * x * m, hle ⟨x, hx, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem highCover_p_symm [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (h2 : (2 : K) = 0)
    (Φ : SpecialLinearGroup (Fin 6) K →* G) (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (hN1 : ∀ B : SpecialLinearGroup (Fin 6) K, B ∈ unitarySL σ →
      ∀ hC : realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ,
        Φ B = ((e.symm ⟨realize h2 B, hC⟩ : L) : G))
    {y : graphFixedRootGroup TwistTag.E6 K σ} (hy : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ) :
    ∃ hyE : ((e.symm y : L) : G) ∈ (highCover h2 Φ hΦ).E,
      (highCover h2 Φ hΦ).p ⟨_, hyE⟩ = y := by
  have hy' := hy
  rw [su6Levi, (subsystemGroup_inf_eq_map_realize hK hσ h2).1] at hy'
  obtain ⟨B, hB, hBy⟩ := hy'
  have hC : realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ := hBy ▸ y.2
  have hval : ((e.symm y : L) : G) = Φ B := by
    rw [hN1 B hB hC]
    congr 2
    exact Subtype.ext hBy.symm
  refine ⟨hval ▸ ⟨B, rfl⟩, ?_⟩
  exact (QCover.ofParam_p' Φ (realize h2) (hΦ.trans (center_le_ker_realize h2))
    (ker_realize_le_center' h2) hval.symm _).trans hBy

end Levi

section Core


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem nbCover_E_le [Finite K] [CharP K 2] (hk : Nat.card k = 2)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAJ : A ≤ thetaRankOneGroup (algebraMap k K)) (hA : Nat.card A = 3) (h2 : (2 : K) = 0)
    (hX : FieldCoverParamX σ h2 e t (modelToG e A)) (m : graphFixedRootGroup TwistTag.E6 K σ)
    (hmD : A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom ≤ su6Levi σ)
    {G₀ : Subgroup G} (f : G₀ →* ModGL TwistTag.E6.tag K) (hker : f.ker ≤ center G₀)
    (hrange : f.range = adjointGroup TwistTag.E6.tag K)
    (hEX : (highCover h2 hX.Φ hX.ker_le).E ≤ G₀)
    (hfp : ∀ y (hy : y ∈ (highCover h2 hX.Φ hX.ker_le).E),
      f ⟨y, hEX hy⟩ = (highCover h2 hX.Φ hX.ker_le).p ⟨y, hy⟩) :
    (nbCover e h2 hX.Φ hX.ker_le m).E ≤ G₀ := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  set Y := A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom with hY
  have hmadj : (m : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    ((graphFixedRootGroup_le TwistTag.E6 K σ).trans inf_le_left) m.2
  have hXE : ∀ x ∈ modelToG e Y, ∃ hxE : x ∈ (highCover h2 hX.Φ hX.ker_le).E,
      (highCover h2 hX.Φ hX.ker_le).p ⟨x, hxE⟩ ∈ Y := fun x hx =>
    mem_highCover_of_mem_modelToG hK hσ e h2 hX.Φ hX.ker_le hX.N1 hmD hx
  have hXG₀ : modelToG e Y ≤ G₀ := fun x hx => hEX (hXE x hx).1
  set X := (modelToG e Y).subgroupOf G₀ with hXdef
  have hXf : X.map f = Y := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : G) ∈ modelToG e Y := mem_subgroupOf.1 hx
      obtain ⟨hxE, hpx⟩ := hXE _ hx'
      rw [show f x = f ⟨x, hEX hxE⟩ from rfl, hfp _ hxE]
      exact hpx
    · intro y hy
      have hyC : y ∈ graphFixedRootGroup TwistTag.E6 K σ := (hmD hy).2
      obtain ⟨hyE, hpy⟩ := highCover_p_symm hK hσ e h2 hX.Φ hX.ker_le hX.N1 (y := ⟨y, hyC⟩)
        (hmD hy)
      refine ⟨⟨_, hEX hyE⟩, mem_subgroupOf.2 (symm_mem_modelToG e (x := ⟨y, hyC⟩) hy), ?_⟩
      rw [hfp _ hyE, hpy]
  set MN := (subsystemGroup TwistTag.E6.tag K setA).map
    (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom with hMN
  have hMNperf : ⁅MN, MN⁆ = MN := by
    rw [hMN, ← Subgroup.map_commutator, subsystemGroup_setA_perfect h2]
  have hMNadj : MN ≤ adjointGroup TwistTag.E6.tag K := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hmadj (subsystemGroup_le_adjointGroup_E6 setA hx)) (inv_mem hmadj)
  have hMNY : MN ≤ centralizer (Y : Set (ModGL TwistTag.E6.tag K)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h1 := mem_centralizer_iff.1
      (subsystemGroup_le_centralizer_thetaRankOneGroup h2 (algebraMap k K) hx) a (hAJ ha)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (m : ModGL TwistTag.E6.tag K) * a * (m : ModGL TwistTag.E6.tag K)⁻¹ *
          ((m : ModGL TwistTag.E6.tag K) * x * (m : ModGL TwistTag.E6.tag K)⁻¹) =
        (m : ModGL TwistTag.E6.tag K) * (a * x) * (m : ModGL TwistTag.E6.tag K)⁻¹ := by group
      _ = (m : ModGL TwistTag.E6.tag K) * (x * a) * (m : ModGL TwistTag.E6.tag K)⁻¹ := by
        rw [h1]
      _ = (m : ModGL TwistTag.E6.tag K) * x * (m : ModGL TwistTag.E6.tag K)⁻¹ *
          ((m : ModGL TwistTag.E6.tag K) * a * (m : ModGL TwistTag.E6.tag K)⁻¹) := by group
  have hRmap : (perfectCore (centralizer (X : Set G₀))).map f = MN := by
    refine map_perfectCore_centralizer_eq f hker X hMNperf (hMNadj.trans hrange.symm.le)
      (by rw [hXf]; exact hMNY) fun Q hQ hQf hQX => ?_
    rw [hXf] at hQX
    exact le_map_conj_subsystemGroup_of_perfect hk hK' (algebraMap k K) hAJ hA hmadj hQ
      (hQf.trans hrange.le) hQX
  refine QCover.E_le_of_card (nbCover e h2 hX.Φ hX.ker_le m) ?_ (Mc := MN) ?_
    (center_map_conj_subsystemGroup_setA h2 _) (perfectCore (centralizer (X : Set G₀))) ?_ f
    hRmap
  · rw [nbCover_E_eq_centralizerPerfectCore e h2 hX m]
    exact perfectCore_perfect _
  · intro y
    exact nbCover_image_le e h2 hX.Φ hX.ker_le m ⊤
      ((nbCover e h2 hX.Φ hX.ker_le m).mem_image (mem_top (y : G)) y.2)
  · rw [nbCover_E_eq_centralizerPerfectCore e h2 hX m]
    refine le_perfectCore_of_perfect ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      rw [mem_centralizer_iff]
      intro x hx
      have hxX : (⟨x, hXG₀ hx⟩ : G₀) ∈ X := mem_subgroupOf.2 hx
      exact congrArg Subtype.val (mem_centralizer_iff.1 (perfectCore_le _ hr) _ hxX)
    · rw [← Subgroup.map_commutator, perfectCore_perfect]

end Core

end CFSG.SeitzReduction.TwistedE6Pilot
