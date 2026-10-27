module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpStatements
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

namespace CFSG.StandardType.GGQ2Frame.SpPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.SpBlocks CFSG.StandardType.GGQ2Frame.CoverComponents
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem commutatorElement_mul_center {X : Type*} [Group X] {z w : X}
    (hz : z ∈ Subgroup.center X) (hw : w ∈ Subgroup.center X) (a b : X) :
    ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' : ∀ g, g * z = z * g := Subgroup.mem_center_iff.mp hz
  have hw' : ∀ g, g * w = w * g := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (b * w * z) * z⁻¹ * a⁻¹ * (b * w)⁻¹ := by rw [hz' (b * w)]; group
    _ = a * (b * (a⁻¹ * w)) * w⁻¹ * b⁻¹ := by rw [hw' a⁻¹]; group
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem derived_comap_perfect {X R : Type*} [Group X] [Group R] (π : X →* R)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X) {Y : Subgroup R}
    (hY : ⁅Y, Y⁆ = Y) :
    (⁅Y.comap π, Y.comap π⁆).map π = Y ∧
      ⁅⁅Y.comap π, Y.comap π⁆, ⁅Y.comap π, Y.comap π⁆⁆ = ⁅Y.comap π, Y.comap π⁆ := by
  have hmap : (⁅Y.comap π, Y.comap π⁆).map π = Y := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ, hY]
  refine ⟨hmap, le_antisymm ?_ ?_⟩
  · refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  · have hlift : ∀ g ∈ Y.comap π, ∃ d ∈ ⁅Y.comap π, Y.comap π⁆,
        d⁻¹ * g ∈ Subgroup.center X := by
      intro g hg
      have hg' : π g ∈ (⁅Y.comap π, Y.comap π⁆).map π := by
        rw [hmap]
        exact hg
      obtain ⟨d, hd, hdg⟩ := Subgroup.mem_map.mp hg'
      refine ⟨d, hd, hker ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdg, inv_mul_cancel]
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    obtain ⟨d₁, hd₁, hz₁⟩ := hlift g₁ hg₁
    obtain ⟨d₂, hd₂, hz₂⟩ := hlift g₂ hg₂
    have hc := commutatorElement_mul_center hz₁ hz₂ d₁ d₂
    rw [mul_inv_cancel_left, mul_inv_cancel_left] at hc
    rw [hc]
    exact Subgroup.commutator_mem_commutator hd₁ hd₂

theorem ycode_perfect (h7 : SpIsQuasisimpleYcode) {K : Type} [Field K] [Finite K] [CharP K 2]
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} {m : ℕ} (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {c : PlaneRaw.Code m} (hc : PlaneRaw.admissible .symplectic c) :
    ⁅Ycode ζ m c, Ycode ζ m c⁆ = Ycode ζ m c :=
  Subgroup.isPerfect_iff.1 (h7 ζ m hK hζ c hc).1

variable {G : Type} [Group G] {H E : Subgroup G} {m : ℕ} {K : Type} [Field K]
  {hEN : E ≤ Subgroup.normalizer (H : Set G)}
  {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}

theorem SpFrame.rho_eq_tau (fr : SpFrame H E hEN K m ζ) (e : ↥E) :
    fr.rho e = tau ζ m (fr.coord (Additive.ofMul e)) :=
  rfl

theorem SpFrame.equivariant (fr : SpFrame H E hEN K m ζ) : Equivariant hEN fr.π fr.rho := by
  intro a h
  obtain ⟨u, rfl⟩ := fr.τ.surjective a
  have hu : fr.rho (fr.τ u) = spPlaneTorus m ζ u := by
    simp [SpFrame.rho]
  rw [hu]
  exact fr.intertwine u h

theorem SpFrame.equivariant_restrict (fr : SpFrame H E hEN K m ζ) {A : Subgroup G}
    (hAE : A ≤ E) : Equivariant (hAE.trans hEN) fr.π (fr.rho.comp (Subgroup.inclusion hAE)) :=
  fun a h => fr.equivariant (Subgroup.inclusion hAE a) h

theorem SpFrame.not_three_dvd_card_ker (fr : SpFrame H E hEN K m ζ)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥H)) : ¬ 3 ∣ Nat.card fr.π.ker :=
  fun h => hZ3 (h.trans (Subgroup.card_dvd_of_le fr.ker_le))

theorem SpFrame.pi_eq_rho [CharP K 2] (fr : SpFrame H E hEN K m ζ) (e : ↥E) (he : (e : G) ∈ H) :
    fr.π ⟨e, he⟩ = fr.rho e := by
  have hcen : (fr.rho e)⁻¹ * fr.π ⟨e, he⟩ ∈ Subgroup.center ↥(StatedSp m K) := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨h, rfl⟩ := fr.surj r
    have h1 := fr.equivariant e h
    have h2 : H.normalizerMonoidHom ⟨(e : G), hEN e.2⟩ h = ⟨e, he⟩ * h * (⟨e, he⟩ : ↥H)⁻¹ :=
      Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe H _ h)
    rw [h2, map_mul, map_mul, map_inv] at h1
    calc fr.π h * ((fr.rho e)⁻¹ * fr.π ⟨e, he⟩)
        = (fr.rho e)⁻¹ * (fr.rho e * fr.π h * (fr.rho e)⁻¹) * fr.π ⟨e, he⟩ := by group
      _ = (fr.rho e)⁻¹ * (fr.π ⟨e, he⟩ * fr.π h * (fr.π ⟨e, he⟩)⁻¹) * fr.π ⟨e, he⟩ := by
          rw [h1]
      _ = (fr.rho e)⁻¹ * fr.π ⟨e, he⟩ * fr.π h := by group
  rw [CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := K) m,
    Subgroup.mem_bot] at hcen
  exact (inv_mul_eq_one.mp hcen).symm

theorem SpFrame.mem_range_rho_iff (fr : SpFrame H E hEN K m ζ) {A : Subgroup G} (hAE : A ≤ E)
    (r : ↥(StatedSp m K)) :
    r ∈ (fr.rho.comp (Subgroup.inclusion hAE)).range ↔
      ∃ u ∈ ggLinImage (p := 3) fr.coord A, r = tau ζ m u := by
  constructor
  · intro hr
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hr
    refine ⟨fr.coord (Additive.ofMul (Subgroup.inclusion hAE a)), ?_, rfl⟩
    rw [mem_ggLinImage]
    simp
  · rintro ⟨u, hu, rfl⟩
    rw [mem_ggLinImage] at hu
    refine MonoidHom.mem_range.mpr ⟨⟨_, hu⟩, ?_⟩
    have hinc : Subgroup.inclusion hAE ⟨_, hu⟩ = Additive.toMul (fr.coord.symm u) :=
      Subtype.ext rfl
    rw [MonoidHom.comp_apply, hinc, SpFrame.rho_eq_tau]
    simp

theorem SpFrame.centralizer_range_rho (fr : SpFrame H E hEN K m ζ) {A : Subgroup G}
    (hAE : A ≤ E) :
    Subgroup.centralizer (((fr.rho.comp (Subgroup.inclusion hAE)).range :
        Subgroup ↥(StatedSp m K)) : Set ↥(StatedSp m K)) =
      (Subgroup.centralizer (torusSet ζ m (ggLinImage (p := 3) fr.coord A))).comap
        (StatedSp m K).subtype := by
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · rintro hg t ⟨u, hu, rfl⟩
    exact congrArg Subtype.val (hg (tau ζ m u) ((fr.mem_range_rho_iff hAE _).2 ⟨u, hu, rfl⟩))
  · intro hg r hr
    obtain ⟨u, hu, rfl⟩ := (fr.mem_range_rho_iff hAE r).1 hr
    exact Subtype.ext (hg _ ⟨u, hu, rfl⟩)

theorem SpFrame.component_eq (fr : SpFrame H E hEN K m ζ) (c : PlaneRaw.Code m) :
    fr.component c =
      (⁅(Ycode ζ m c).comap fr.π, (Ycode ζ m c).comap fr.π⁆).map H.subtype :=
  rfl

theorem spComponentOccursIff_of (hCov : IsComponentOfCoverIff)
    (h8 : SpIsComponentOfCentralizerTorusSetIff) : SpComponentOccursIff := by
  intro G _ _ H E m K _ _ _ hEN ζ ctx A hAE X
  have hp : IsPGroup 3 ↥A := fun a =>
    ⟨1, Subtype.ext (by simpa using ctx.hEab.2 (a : G) (hAE a.2))⟩
  rw [hCov (hAE.trans hEN) ctx.fr.π (ctx.fr.rho.comp (Subgroup.inclusion hAE)) hp ctx.fr.surj
    ctx.fr.ker_le (ctx.fr.not_three_dvd_card_ker ctx.hZ3) ctx.hHp
    (ctx.fr.equivariant_restrict hAE) X, ctx.fr.centralizer_range_rho hAE]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨c, hc, hocc, rfl⟩ := (h8 ζ m ctx.hK ctx.hζ _ Y).1 hY
    exact ⟨c, hc, hocc, rfl⟩
  · rintro ⟨c, hc, hocc, rfl⟩
    exact ⟨Ycode ζ m c, (h8 ζ m ctx.hK ctx.hζ _ _).2 ⟨c, hc, hocc, rfl⟩, rfl⟩

theorem spComponentCentEq_of (hCom : CommuteCoverIff) (h7 : SpIsQuasisimpleYcode)
    (h9 : SpTauCommuteYcodeIff) : SpComponentCentEq := by
  intro G _ _ H E m K _ _ _ hEN ζ ctx c hc
  obtain ⟨hmap, hperf⟩ := derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le
    (ycode_perfect h7 ctx.hK ctx.hζ hc)
  have hXtop : commutator ↥(⁅(Ycode ζ m c).comap ctx.fr.π, (Ycode ζ m c).comap ctx.fr.π⁆) = ⊤ :=
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hperf)
  ext v
  rw [mem_ggLinImage]
  set e : ↥E := Additive.toMul (ctx.fr.coord.symm v) with he
  have hv : ctx.fr.coord (Additive.ofMul e) = v := by simp [he]
  have key := hCom hEN ctx.fr.π ctx.fr.rho ctx.fr.ker_le ctx.fr.equivariant _ hXtop e
  rw [hmap, SpFrame.rho_eq_tau, hv] at key
  refine Iff.trans ?_ (key.trans (h9 ζ m ctx.hK ctx.hζ c hc v))
  rw [Subgroup.mem_centralizer_iff, SpFrame.component_eq]
  constructor
  · intro h x hx
    exact (h (x : G) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)).symm
  · intro h g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact (h x hx).symm

theorem spComponentInsideEq_of (hMem : MemDerivedComapIff) (h7 : SpIsQuasisimpleYcode)
    (h9 : SpTauMemYcodeIff) : SpComponentInsideEq := by
  intro G _ _ H E m K _ _ _ hEN ζ ctx c hc
  have hY := ycode_perfect h7 ctx.hK ctx.hζ hc
  ext v
  rw [mem_ggLinImage]
  set e : ↥E := Additive.toMul (ctx.fr.coord.symm v) with he
  have hv : ctx.fr.coord (Additive.ofMul e) = v := by simp [he]
  have heH : (e : G) ∈ H := ctx.hEH e.2
  have he3 : (⟨e, heH⟩ : ↥H) ^ 3 = 1 :=
    Subtype.ext (by simpa using ctx.hEab.2 (e : G) e.2)
  have key := hMem ctx.fr.π ctx.fr.surj ctx.fr.ker_le (ctx.fr.not_three_dvd_card_ker ctx.hZ3)
    _ hY ⟨e, heH⟩ he3
  rw [ctx.fr.pi_eq_rho e heH, SpFrame.rho_eq_tau, hv] at key
  refine Iff.trans ?_ (key.trans (h9 ζ m ctx.hK ctx.hζ c hc v))
  rw [SpFrame.component_eq]
  constructor
  · intro h
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp h
    have hx' : x = ⟨e, heH⟩ := Subtype.ext hxe
    rw [← hx']
    exact hx
  · intro h
    exact Subgroup.mem_map.mpr ⟨⟨e, heH⟩, h, rfl⟩

theorem spComponentMarked_of (h7 : SpIsQuasisimpleYcode) (h10 : SpMarkedYcode) :
    SpComponentMarked := by
  intro G _ _ H E m K _ _ _ hEN ζ ctx c hc
  obtain ⟨hmap, hperf⟩ := derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le
    (ycode_perfect h7 ctx.hK ctx.hζ hc)
  have hY : LargeEvenMarking ↥((⁅(Ycode ζ m c).comap ctx.fr.π,
      (Ycode ζ m c).comap ctx.fr.π⁆).map ctx.fr.π)
      (fun lab _ _ _ _ _ => lab = PlaneRaw.label .symplectic c) := by
    rw [hmap]
    exact h10 ζ m ctx.hK ctx.hζ c hc
  have hX := (SCFourCover.largeEvenMarking_map_iff ctx.fr.ker_le hperf
    (fun lab => lab = PlaneRaw.label .symplectic c)).2 hY
  exact largeEvenMarking_congr ((⁅(Ycode ζ m c).comap ctx.fr.π,
    (Ycode ζ m c).comap ctx.fr.π⁆).equivMapOfInjective H.subtype H.subtype_injective).symm
    (fun _ _ _ _ _ _ h => h) hX

end CFSG.StandardType.GGQ2Frame.SpPlacement

end
