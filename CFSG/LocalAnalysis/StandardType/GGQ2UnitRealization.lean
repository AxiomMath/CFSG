module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitRealizationStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitFrameRange
import CFSG.LocalAnalysis.StandardType.GGQ2UnitAssembly
import CFSG.LocalAnalysis.StandardType.GGQ2UnitBlockDiag
import CFSG.LocalAnalysis.StandardType.GGQ2CoverComponents
import CFSG.LocalAnalysis.StandardType.GGQ2SpRealization
import CFSG.GroupTheory.InnerCentralizerProjection

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.StandardType.GGQ2Frame.CoverComponents

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {G : Type} [Group G] {H E : Subgroup G} {N : ℕ} {K : Type} [Field K]
  {hEN : E ≤ Subgroup.normalizer (H : Set G)} {ζ : Multiplicative (ZMod 3) →* Kˣ}

@[expose] def UnitFrame.rep (fr : UnitFrame H E hEN K N ζ) (b : ↥E) : UnitRaw.W N :=
  Classical.choose ((UnitRaw.oneLine N).mkQ_surjective (fr.ι (Additive.ofMul b)))

theorem UnitFrame.mkQ_rep (fr : UnitFrame H E hEN K N ζ) (b : ↥E) :
    (UnitRaw.oneLine N).mkQ (fr.rep b) = fr.ι (Additive.ofMul b) :=
  Classical.choose_spec ((UnitRaw.oneLine N).mkQ_surjective (fr.ι (Additive.ofMul b)))

theorem UnitFrame.rep_mem_normalizer (fr : UnitFrame H E hEN K N ζ) (b : ↥E) :
    diagOf ζ (fr.rep b) ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
  (fr.intertwine b (fr.rep b) (fr.mkQ_rep b)).fst

@[expose] def UnitFrame.rhoFun (fr : UnitFrame H E hEN K N ζ) (b : ↥E) :
    MulAut (LargeEvenProj (unitarySU 2 1 K N)) :=
  TableB.projConj _ ⟨diagOf ζ (fr.rep b), fr.rep_mem_normalizer b⟩

theorem UnitFrame.pi_conj_eq_rhoFun (fr : UnitFrame H E hEN K N ζ) (b : ↥E) (h : ↥H) :
    fr.π (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h) = fr.rhoFun b (fr.π h) :=
  (fr.intertwine b (fr.rep b) (fr.mkQ_rep b)).snd h

private theorem ura_ext (fr : UnitFrame H E hEN K N ζ)
    {φ ψ : MulAut (LargeEvenProj (unitarySU 2 1 K N))} (h : ∀ x : ↥H, φ (fr.π x) = ψ (fr.π x)) :
    φ = ψ := by
  ext y
  obtain ⟨x, rfl⟩ := fr.surj y
  exact h x

@[expose] def UnitFrame.rho (fr : UnitFrame H E hEN K N ζ) :
    ↥E →* MulAut (LargeEvenProj (unitarySU 2 1 K N)) where
  toFun := fr.rhoFun
  map_one' := by
    apply ura_ext fr
    intro x
    have h1 : (⟨((1 : ↥E) : G), hEN (1 : ↥E).2⟩ : Subgroup.normalizer (H : Set G)) = 1 := rfl
    rw [← fr.pi_conj_eq_rhoFun, h1, map_one, MulAut.one_apply, MulAut.one_apply]
  map_mul' a b := by
    apply ura_ext fr
    intro x
    have hab : (⟨((a * b : ↥E) : G), hEN (a * b).2⟩ : Subgroup.normalizer (H : Set G)) =
        ⟨(a : G), hEN a.2⟩ * ⟨(b : G), hEN b.2⟩ := rfl
    rw [MulAut.mul_apply, ← fr.pi_conj_eq_rhoFun, ← fr.pi_conj_eq_rhoFun, ← fr.pi_conj_eq_rhoFun,
      hab, map_mul, MulAut.mul_apply]

theorem UnitFrame.rho_apply (fr : UnitFrame H E hEN K N ζ) (b : ↥E) : fr.rho b = fr.rhoFun b :=
  rfl

theorem UnitFrame.equivariantAut (fr : UnitFrame H E hEN K N ζ) :
    EquivariantAut hEN fr.π fr.rho :=
  fun b h => fr.pi_conj_eq_rhoFun b h

theorem UnitFrame.equivariantAut_restrict (fr : UnitFrame H E hEN K N ζ) {A : Subgroup G}
    (hAE : A ≤ E) :
    EquivariantAut (hAE.trans hEN) fr.π (fr.rho.comp (Subgroup.inclusion hAE)) :=
  fun a h => fr.equivariantAut (Subgroup.inclusion hAE a) h

theorem UnitFrame.rho_eq (fr : UnitFrame H E hEN K N ζ) (b : ↥E) {w : UnitRaw.W N}
    (hw : (UnitRaw.oneLine N).mkQ w = fr.ι (Additive.ofMul b))
    (hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) :
    fr.rho b = TableB.projConj _ ⟨diagOf ζ w, hD⟩ := by
  apply ura_ext fr
  intro x
  rw [← fr.equivariantAut b x]
  exact (fr.intertwine b w hw).snd x

theorem UnitFrame.rho_eq_conj (fr : UnitFrame H E hEN K N ζ) (b : ↥E) (hb : (b : G) ∈ H) :
    fr.rho b = MulAut.conj (fr.π ⟨b, hb⟩) := by
  apply ura_ext fr
  intro x
  have h2 : H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ x = ⟨b, hb⟩ * x * (⟨b, hb⟩ : ↥H)⁻¹ :=
    Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe H _ x)
  rw [← fr.equivariantAut b x, MulAut.conj_apply, h2, map_mul, map_mul, map_inv]

theorem UnitFrame.fixedSub_rho_restrict (fr : UnitFrame H E hEN K N ζ) {A : Subgroup G}
    (hAE : A ≤ E) :
    fixedSub (fr.rho.comp (Subgroup.inclusion hAE)) = diagFix ζ N (fr.image A) := by
  ext y
  rw [mem_fixedSub, mem_diagFix]
  constructor
  · intro hy w hw hD
    obtain ⟨b, hbA, hbw⟩ := (fr.mem_image A _).mp hw
    have h1 := hy ⟨b, hbA⟩
    rwa [MonoidHom.comp_apply,
      show Subgroup.inclusion hAE ⟨(b : G), hbA⟩ = b from Subtype.ext rfl,
      fr.rho_eq b hbw.symm hD] at h1
  · intro hy a
    rw [MonoidHom.comp_apply, fr.rho_apply]
    exact hy _ ((fr.mem_image A _).mpr ⟨Subgroup.inclusion hAE a, a.2, (fr.mkQ_rep _).symm⟩) _

theorem UnitFrame.not_three_dvd_card_ker (fr : UnitFrame H E hEN K N ζ)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) : ¬ 3 ∣ Nat.card fr.π.ker :=
  fun h => not_three_dvd_card_center hC3 (h.trans (Subgroup.card_dvd_of_le fr.ker_le))

private theorem ura_eq_one_of_pow_three {C : Subgroup G} (hC : ¬ 3 ∣ Nat.card ↥C) {c : G}
    (hc : c ∈ C) (h3 : c ^ 3 = 1) : c = 1 := by
  have hord3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hord : orderOf c ∣ Nat.card ↥C := Subgroup.orderOf_dvd_natCard C hc
  rcases (Nat.dvd_prime Nat.prime_three).mp hord3 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ hord) hC

theorem UnitCtx.mem_of_sum_eq_zero [Finite G] [Finite K] (ctx : UnitCtx H E hEN K N ζ)
    (hUF : UnitaryFieldData 2 1 K) (b : ↥E) {w : UnitRaw.W N}
    (hbw : (UnitRaw.oneLine N).mkQ w = ctx.fr.ι (Additive.ofMul b)) (hw : ∑ i, w i = 0) :
    ∃ hb : (b : G) ∈ H, ctx.fr.π ⟨b, hb⟩ =
      LargeEvenProjMk _ ⟨diagOf ζ w, diagOf_mem_unitarySU ζ hUF hw⟩ := by
  obtain ⟨g, hg3, hπg, hgc⟩ := ctx.fr.exists_lift_centralizing hUF ctx.hC3 hw
  set s := LargeEvenProjMk (unitarySU 2 1 K N) ⟨diagOf ζ w, diagOf_mem_unitarySU ζ hUF hw⟩
    with hs
  have hbN : (b : G) ∈ Subgroup.normalizer (H : Set G) := hEN b.2
  have hρb : ctx.fr.rho b = MulAut.conj s := by
    rw [ctx.fr.rho_eq b hbw (Subgroup.le_normalizer (diagOf_mem_unitarySU ζ hUF hw)),
      TableB.projConj_of_mem _ _ (diagOf_mem_unitarySU ζ hUF hw)]
    rfl
  set c : G := (b : G) * (g : G)⁻¹ with hc
  have hcN : c ∈ Subgroup.normalizer (H : Set G) :=
    Subgroup.mul_mem _ hbN (Subgroup.inv_mem _ (Subgroup.le_normalizer g.2))
  have hcen : ∀ x ∈ H, c * x * c⁻¹ * x⁻¹ ∈ (Subgroup.center ↥H).map H.subtype := by
    intro x hx
    set y : ↥H := g⁻¹ * ⟨x, hx⟩ * g with hy
    have hval : (H.normalizerMonoidHom ⟨(b : G), hbN⟩ y : G) = c * x * c⁻¹ := by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hy, hc]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hcx : c * x * c⁻¹ ∈ H := hval ▸ (H.normalizerMonoidHom ⟨(b : G), hbN⟩ y).2
    have hz : H.normalizerMonoidHom ⟨(b : G), hbN⟩ y = ⟨c * x * c⁻¹, hcx⟩ := Subtype.ext hval
    have hπ : ctx.fr.π ⟨c * x * c⁻¹, hcx⟩ = ctx.fr.π ⟨x, hx⟩ := by
      rw [← hz, ctx.fr.equivariantAut b y, hρb, MulAut.conj_apply, hy, map_mul, map_mul, map_inv,
        hπg]
      group
    have hk : (⟨c * x * c⁻¹, hcx⟩ : ↥H) * (⟨x, hx⟩ : ↥H)⁻¹ ∈ ctx.fr.π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, mul_inv_cancel]
    exact ⟨_, ctx.fr.ker_le hk, rfl⟩
  have hperf : Group.IsPerfect ↥H := Group.isPerfect_def.2 ctx.hHp
  have hcC : c ∈ Subgroup.centralizer (H : Set G) :=
    mem_centralizer_of_commutator_mem_center hperf hcN hcen
  have hbg : Commute (b : G) (g : G) := (Subgroup.mem_centralizer_iff.mp hgc (b : G) b.2)
  have hb3 : (b : G) ^ 3 = 1 := ctx.hEab.2 (b : G) b.2
  have hg3' : (g : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hg3
  have hc3 : c ^ 3 = 1 := by
    rw [hc, (hbg.inv_right).mul_pow, hb3, inv_pow, hg3', inv_one, one_mul]
  have hc1 : c = 1 := ura_eq_one_of_pow_three ctx.hC3 hcC hc3
  have hbg' : (b : G) = g := by
    rw [hc] at hc1
    exact mul_inv_eq_one.mp hc1
  refine ⟨hbg' ▸ g.2, ?_⟩
  rw [← hπg]
  exact congrArg ctx.fr.π (Subtype.ext hbg')

theorem unitComponentOccursIff_of (hCov : IsComponentOfCoverIffAut)
    (hM1 : UnitIsComponentOfDiagFixIff) : UnitComponentOccursIff := by
  intro G _ _ H E N K _ _ hEN ζ ctx A hAE X
  have hp : IsPGroup 3 ↥A := fun a =>
    ⟨1, Subtype.ext (by simpa using ctx.hEab.2 (a : G) (hAE a.2))⟩
  rw [hCov (hAE.trans hEN) ctx.fr.π (ctx.fr.rho.comp (Subgroup.inclusion hAE)) hp ctx.fr.surj
    ctx.fr.ker_le (ctx.fr.not_three_dvd_card_ker ctx.hC3) ctx.hHp
    (ctx.fr.equivariantAut_restrict hAE) X, ctx.fr.fixedSub_rho_restrict hAE]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨S, hS, hocc, rfl⟩ := (hM1 ζ N ctx.hK ctx.hζ ctx.hN _ Y).1 hY
    exact ⟨S, hS, hocc, rfl⟩
  · rintro ⟨S, hS, hocc, rfl⟩
    exact ⟨blockPSU S, (hM1 ζ N ctx.hK ctx.hζ ctx.hN _ _).2 ⟨S, hS, hocc, rfl⟩, rfl⟩

theorem unitComponentCentEq_of (hCom : CommuteCoverIffAut)
    (hM4 : UnitBlockPerfect) : UnitComponentCentEq := by
  have hM2 := @unitBlockFixIff_holds
  intro G _ _ H E N K _ _ hEN ζ ctx S hS
  have hUF : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [ctx.hK]; norm_num) le_rfl
  obtain ⟨hmap, hperf⟩ := SpPlacement.derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le
    (hM4 N ctx.hK ctx.hN S hS)
  have hXtop : commutator ↥(⁅(blockPSU (K := K) S).comap ctx.fr.π,
      (blockPSU (K := K) S).comap ctx.fr.π⁆) = ⊤ :=
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hperf)
  have hb : ∀ b : ↥E, (b : G) ∈ Subgroup.centralizer (ctx.fr.component S : Set G) ↔
      ctx.fr.ι (Additive.ofMul b) ∈ UnitRaw.cent S := by
    intro b
    have key := hCom hEN ctx.fr.π ctx.fr.rho ctx.fr.ker_le ctx.fr.equivariantAut _ hXtop b
    rw [hmap, ctx.fr.rho_eq b (ctx.fr.mkQ_rep b) (diagOf_mem_normalizer ζ hUF _)] at key
    rw [← ctx.fr.mkQ_rep b,
      ← hM2 ζ N ctx.hK ctx.hζ ctx.hN S hS _ (diagOf_mem_normalizer ζ hUF _), ← key,
      Subgroup.mem_centralizer_iff, UnitFrame.component]
    constructor
    · intro h x hx
      exact (h (x : G) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)).symm
    · intro h g hg
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
      exact (h x hx).symm
  ext v
  rw [ctx.fr.mem_image, Submodule.mem_inf, ctx.fr.mem_image]
  constructor
  · rintro ⟨b, hbC, rfl⟩
    exact ⟨(hb b).1 hbC, b, b.2, rfl⟩
  · rintro ⟨hv, b, -, rfl⟩
    exact ⟨b, (hb b).2 hv, rfl⟩

theorem unitComponentInsideEq_of (hM4 : UnitBlockPerfect) :
    UnitComponentInsideEq := by
  have hM3 := @unitBlockConjIff_holds
  intro G _ _ H E N K _ _ hEN ζ ctx S hS
  have hUF : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [ctx.hK]; norm_num) le_rfl
  have hY := hM4 N ctx.hK ctx.hN S hS
  have hb : ∀ b : ↥E, (b : G) ∈ ctx.fr.component S ↔
      ctx.fr.ι (Additive.ofMul b) ∈ UnitRaw.inside S := by
    intro b
    constructor
    · intro hbX
      have hbH : (b : G) ∈ H := ctx.fr.component_le S hbX
      obtain ⟨x, hx, hxb⟩ := Subgroup.mem_map.mp hbX
      have hx' : x = ⟨b, hbH⟩ := Subtype.ext hxb
      have hπx : ctx.fr.π ⟨b, hbH⟩ ∈ blockPSU (K := K) S := by
        rw [← hx']
        have h1 := Subgroup.mem_map_of_mem ctx.fr.π hx
        rwa [(SpPlacement.derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le hY).1] at h1
      rw [← ctx.fr.mkQ_rep b]
      refine (hM3 ζ N ctx.hK ctx.hζ ctx.hN S hS _ (diagOf_mem_normalizer ζ hUF _)).1
        ⟨_, hπx, ?_⟩
      rw [← ctx.fr.rho_eq b (ctx.fr.mkQ_rep b), ctx.fr.rho_eq_conj b hbH]
    · intro hv
      obtain ⟨w, hwv, hwS, hw0⟩ := (UnitRaw.mem_inside_iff S _).mp hv
      obtain ⟨hbH, hπb⟩ := ctx.mem_of_sum_eq_zero hUF b hwv hw0
      have he3 : (⟨b, hbH⟩ : ↥H) ^ 3 = 1 :=
        Subtype.ext (by simpa using ctx.hEab.2 (b : G) b.2)
      have key := memDerivedComapIff_holds ctx.fr.π ctx.fr.surj ctx.fr.ker_le
        (ctx.fr.not_three_dvd_card_ker ctx.hC3) _ hY ⟨b, hbH⟩ he3
      have hmem : ctx.fr.π ⟨b, hbH⟩ ∈ blockPSU (K := K) S := by
        rw [hπb]
        exact Subgroup.mem_map_of_mem _ (diagOf_mem_blockSU hUF ζ hwS hw0)
      exact Subgroup.mem_map.mpr ⟨⟨b, hbH⟩, key.2 hmem, rfl⟩
  ext v
  rw [ctx.fr.mem_image, Submodule.mem_inf, ctx.fr.mem_image]
  constructor
  · rintro ⟨b, hbX, rfl⟩
    exact ⟨(hb b).1 hbX, b, b.2, rfl⟩
  · rintro ⟨hv, b, -, rfl⟩
    exact ⟨b, (hb b).2 hv, rfl⟩

theorem unitComponentMarked_of (hM4 : UnitBlockPerfect) (hM5 : UnitBlockMarked) :
    UnitComponentMarked := by
  intro G _ _ H E N K _ _ hEN ζ ctx S hS
  obtain ⟨hmap, hperf⟩ := SpPlacement.derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le
    (hM4 N ctx.hK ctx.hN S hS)
  have hY : LargeEvenMarking ↥((⁅(blockPSU (K := K) S).comap ctx.fr.π,
      (blockPSU (K := K) S).comap ctx.fr.π⁆).map ctx.fr.π)
      (fun lab _ _ _ _ _ => lab = UnitRaw.label S) := by
    rw [hmap]
    exact hM5 N ctx.hK ctx.hN S hS
  have hX := (SCFourCover.largeEvenMarking_map_iff ctx.fr.ker_le hperf
    (fun lab => lab = UnitRaw.label S)).2 hY
  exact largeEvenMarking_congr ((⁅(blockPSU (K := K) S).comap ctx.fr.π,
    (blockPSU (K := K) S).comap ctx.fr.π⁆).equivMapOfInjective H.subtype
      H.subtype_injective).symm (fun _ _ _ _ _ _ h => h) hX

end

end CFSG.StandardType.GGQ2Frame.UnitPlacement

end
