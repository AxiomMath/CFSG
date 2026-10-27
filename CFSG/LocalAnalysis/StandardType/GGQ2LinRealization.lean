module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2SpRealization

public section

namespace CFSG.StandardType.GGQ2Frame.LinPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.LinBlocks CFSG.StandardType.GGQ2Frame.CoverComponents
open CFSG.StandardType.GGQ2Frame.SpPlacement (derived_comap_perfect)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ycode_perfect (h7 : LinIsQuasisimpleYcode) {K : Type} [Field K] [Finite K] [CharP K 2]
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} {t : ℕ} {ε : Fin 2}
    (hK : Nat.card K = 2) (hζ : Function.Injective ζ) {c : PlaneRaw.Code t}
    (hc : PlaneRaw.admissible (.linear ε) c) :
    ⁅Ycode ζ t ε c, Ycode ζ t ε c⁆ = Ycode ζ t ε c :=
  Subgroup.isPerfect_iff.1 (h7 ζ t ε hK hζ c hc).1

theorem center_gl_eq_bot_of_card_two {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (hK : Nat.card K = 2) : Subgroup.center (GL ι K) = ⊥ := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hsub : Subsingleton Kˣ := by
    rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_units, ← Nat.card_eq_fintype_card,
      hK]
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
  rintro _ ⟨u, rfl⟩
  rw [Subsingleton.elim u 1, map_one]
  exact Subgroup.one_mem _

variable {G : Type} [Group G] {H E : Subgroup G} {t : ℕ} {ε : Fin 2} {K : Type} [Field K]
  {hEN : E ≤ Subgroup.normalizer (H : Set G)}
  {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}

theorem LinFrame.rho_eq_tau (fr : LinFrame H E hEN K t ε ζ) (e : ↥E) :
    fr.rho e = tau ζ t ε (fr.coord (Additive.ofMul e)) :=
  rfl

theorem LinFrame.equivariant (fr : LinFrame H E hEN K t ε ζ) : Equivariant hEN fr.π fr.rho := by
  intro a h
  obtain ⟨u, rfl⟩ := fr.τ.surjective a
  have hu : fr.rho (fr.τ u) = linTorus ζ t ε u := by
    simp [LinFrame.rho]
  rw [hu]
  exact fr.intertwine u h

theorem LinFrame.equivariant_restrict (fr : LinFrame H E hEN K t ε ζ) {A : Subgroup G}
    (hAE : A ≤ E) : Equivariant (hAE.trans hEN) fr.π (fr.rho.comp (Subgroup.inclusion hAE)) :=
  fun a h => fr.equivariant (Subgroup.inclusion hAE a) h

theorem LinFrame.not_three_dvd_card_ker (fr : LinFrame H E hEN K t ε ζ)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥H)) : ¬ 3 ∣ Nat.card fr.π.ker :=
  fun h => hZ3 (h.trans (Subgroup.card_dvd_of_le fr.ker_le))

theorem LinFrame.pi_eq_rho [Finite K] (hK : Nat.card K = 2) (fr : LinFrame H E hEN K t ε ζ)
    (e : ↥E) (he : (e : G) ∈ H) : fr.π ⟨e, he⟩ = fr.rho e := by
  have hcen : (fr.rho e)⁻¹ * fr.π ⟨e, he⟩ ∈ Subgroup.center (GL (LinIdx t ε) K) := by
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
  rw [center_gl_eq_bot_of_card_two hK, Subgroup.mem_bot] at hcen
  exact (inv_mul_eq_one.mp hcen).symm

theorem LinFrame.mem_range_rho_iff (fr : LinFrame H E hEN K t ε ζ) {A : Subgroup G}
    (hAE : A ≤ E) (r : GL (LinIdx t ε) K) :
    r ∈ (fr.rho.comp (Subgroup.inclusion hAE)).range ↔
      ∃ u ∈ ggLinImage (p := 3) fr.coord A, r = tau ζ t ε u := by
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
    rw [MonoidHom.comp_apply, hinc, LinFrame.rho_eq_tau]
    simp

theorem LinFrame.centralizer_range_rho (fr : LinFrame H E hEN K t ε ζ) {A : Subgroup G}
    (hAE : A ≤ E) :
    Subgroup.centralizer (((fr.rho.comp (Subgroup.inclusion hAE)).range :
        Subgroup (GL (LinIdx t ε) K)) : Set (GL (LinIdx t ε) K)) =
      Subgroup.centralizer (torusSet ζ t ε (ggLinImage (p := 3) fr.coord A)) := by
  have hset : (((fr.rho.comp (Subgroup.inclusion hAE)).range : Subgroup (GL (LinIdx t ε) K)) :
      Set (GL (LinIdx t ε) K)) = torusSet ζ t ε (ggLinImage (p := 3) fr.coord A) :=
    Set.ext fun r => fr.mem_range_rho_iff hAE r
  rw [hset]

theorem LinFrame.component_eq (fr : LinFrame H E hEN K t ε ζ) (c : PlaneRaw.Code t) :
    fr.component c =
      (⁅(Ycode ζ t ε c).comap fr.π, (Ycode ζ t ε c).comap fr.π⁆).map H.subtype :=
  rfl

theorem linComponentOccursIff_of (hCov : IsComponentOfCoverIff)
    (h8 : LinIsComponentOfCentralizerTorusSetIff) : LinComponentOccursIff := by
  intro G _ _ H E t ε K _ _ _ hEN ζ ctx A hAE X
  have hp : IsPGroup 3 ↥A := fun a =>
    ⟨1, Subtype.ext (by simpa using ctx.hEab.2 (a : G) (hAE a.2))⟩
  rw [hCov (hAE.trans hEN) ctx.fr.π (ctx.fr.rho.comp (Subgroup.inclusion hAE)) hp ctx.fr.surj
    ctx.fr.ker_le (ctx.fr.not_three_dvd_card_ker ctx.hZ3) ctx.hHp
    (ctx.fr.equivariant_restrict hAE) X, ctx.fr.centralizer_range_rho hAE]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨c, hc, hocc, rfl⟩ := (h8 ζ t ε ctx.hK ctx.hζ _ Y).1 hY
    exact ⟨c, hc, hocc, rfl⟩
  · rintro ⟨c, hc, hocc, rfl⟩
    exact ⟨Ycode ζ t ε c, (h8 ζ t ε ctx.hK ctx.hζ _ _).2 ⟨c, hc, hocc, rfl⟩, rfl⟩

theorem linComponentCentEq_of (hCom : CommuteCoverIff) (h7 : LinIsQuasisimpleYcode)
    (h9 : LinTauCommuteYcodeIff) : LinComponentCentEq := by
  intro G _ _ H E t ε K _ _ _ hEN ζ ctx c hc
  have hadm : PlaneRaw.admissible (.linear ε) c := hc
  obtain ⟨hmap, hperf⟩ := derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le
    (ycode_perfect h7 ctx.hK ctx.hζ hadm)
  have hXtop : commutator ↥(⁅(Ycode ζ t ε c).comap ctx.fr.π, (Ycode ζ t ε c).comap ctx.fr.π⁆) =
      ⊤ :=
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hperf)
  ext v
  rw [mem_ggLinImage]
  set e : ↥E := Additive.toMul (ctx.fr.coord.symm v) with he
  have hv : ctx.fr.coord (Additive.ofMul e) = v := by simp [he]
  have key := hCom hEN ctx.fr.π ctx.fr.rho ctx.fr.ker_le ctx.fr.equivariant _ hXtop e
  rw [hmap, LinFrame.rho_eq_tau, hv] at key
  refine Iff.trans ?_ (key.trans (h9 ζ t ε ctx.hK ctx.hζ c hadm v))
  rw [Subgroup.mem_centralizer_iff, LinFrame.component_eq]
  constructor
  · intro h x hx
    exact (h (x : G) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)).symm
  · intro h g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact (h x hx).symm

theorem linComponentInsideEq_of (hMem : MemDerivedComapIff) (h7 : LinIsQuasisimpleYcode)
    (h9 : LinTauMemYcodeIff) : LinComponentInsideEq := by
  intro G _ _ H E t ε K _ _ _ hEN ζ ctx c hc
  have hadm : PlaneRaw.admissible (.linear ε) c := hc
  have hY := ycode_perfect h7 ctx.hK ctx.hζ hadm
  ext v
  rw [mem_ggLinImage]
  set e : ↥E := Additive.toMul (ctx.fr.coord.symm v) with he
  have hv : ctx.fr.coord (Additive.ofMul e) = v := by simp [he]
  have heH : (e : G) ∈ H := ctx.hEH e.2
  have he3 : (⟨e, heH⟩ : ↥H) ^ 3 = 1 :=
    Subtype.ext (by simpa using ctx.hEab.2 (e : G) e.2)
  have key := hMem ctx.fr.π ctx.fr.surj ctx.fr.ker_le (ctx.fr.not_three_dvd_card_ker ctx.hZ3)
    _ hY ⟨e, heH⟩ he3
  rw [ctx.fr.pi_eq_rho ctx.hK e heH, LinFrame.rho_eq_tau, hv] at key
  refine Iff.trans ?_ (key.trans (h9 ζ t ε ctx.hK ctx.hζ c hadm v))
  rw [LinFrame.component_eq]
  constructor
  · intro h
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp h
    have hx' : x = ⟨e, heH⟩ := Subtype.ext hxe
    rw [← hx']
    exact hx
  · intro h
    exact Subgroup.mem_map.mpr ⟨⟨e, heH⟩, h, rfl⟩

theorem linComponentMarked_of (h7 : LinIsQuasisimpleYcode) (h10 : LinMarkedYcode) :
    LinComponentMarked := by
  intro G _ _ H E t ε K _ _ _ hEN ζ ctx c hc
  have hadm : PlaneRaw.admissible (.linear ε) c := hc
  obtain ⟨hmap, hperf⟩ := derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le
    (ycode_perfect h7 ctx.hK ctx.hζ hadm)
  have hY : LargeEvenMarking ↥((⁅(Ycode ζ t ε c).comap ctx.fr.π,
      (Ycode ζ t ε c).comap ctx.fr.π⁆).map ctx.fr.π)
      (fun lab _ _ _ _ _ => lab = PlaneRaw.label (.linear ε) c) := by
    rw [hmap]
    exact h10 ζ t ε ctx.hK ctx.hζ c hadm
  have hX := (SCFourCover.largeEvenMarking_map_iff ctx.fr.ker_le hperf
    (fun lab => lab = PlaneRaw.label (.linear ε) c)).2 hY
  exact largeEvenMarking_congr ((⁅(Ycode ζ t ε c).comap ctx.fr.π,
    (Ycode ζ t ε c).comap ctx.fr.π⁆).equivMapOfInjective H.subtype H.subtype_injective).symm
    (fun _ _ _ _ _ _ h => h) hX

end CFSG.StandardType.GGQ2Frame.LinPlacement
