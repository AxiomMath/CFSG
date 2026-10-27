module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthAmbient
public import CFSG.LocalAnalysis.StandardType.GGQ2CoverComponents
public import CFSG.LocalAnalysis.StandardType.GGQ2SpRealization
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthTauMemOmega

public section

namespace CFSG.StandardType.GGQ2Frame.OrthPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.OrthBlocks CFSG.StandardType.GGQ2Frame.CoverComponents
open CFSG.StandardType.GGQ2Frame.SpPlacement (derived_comap_perfect)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {hEN : E ≤ Subgroup.normalizer (H : Set G)}
  {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}

private def appendLift : (Fin t → Multiplicative (ZMod 3)) →*
    (Fin (t + δ.val) → Multiplicative (ZMod 3)) where
  toFun u := Fin.append u 1
  map_one' := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_mul' u v := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Pi.mul_apply]

private noncomputable def rhoGL (fr : OrthFrame H E hEN K t δ ζ) :
    ↥E →* GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K :=
  (StatedSp (t + δ.val) K).subtype.comp
    ((spPlaneTorus (t + δ.val) ζ).comp
      ((appendLift (t := t) (δ := δ)).comp fr.τ.symm.toMonoidHom))

omit [Finite G] [Finite K] [CharP K 2] in
private theorem coe_rhoGL (fr : OrthFrame H E hEN K t δ ζ) (e : ↥E) :
    (rhoGL fr e : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      otau ζ t δ (fr.coord (Additive.ofMul e)) := by
  have harg : appendLift (t := t) (δ := δ) (fr.τ.symm.toMonoidHom e) =
      fun i => Multiplicative.ofAdd ((liftV t δ (fr.coord (Additive.ofMul e))) i) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [appendLift, liftV, OrthFrame.coord]
    · simp [appendLift, liftV]
  simp only [rhoGL, MonoidHom.comp_apply, otau, SpBlocks.tau]
  rw [harg]
  rfl

noncomputable def OrthFrame.rho (fr : OrthFrame H E hEN K t δ ζ)
    (hK : Nat.card K = 2) : ↥E →* ↥(omegaQ (K := K) t δ) :=
  (rhoGL fr).codRestrict (omegaQ (K := K) t δ) fun e => by
    show rhoGL fr e ∈ omegaQ (K := K) t δ
    rw [coe_rhoGL]
    exact orthTauMemOmega_holds ζ t δ hK _

omit [Finite G] in
theorem OrthFrame.coe_rho (fr : OrthFrame H E hEN K t δ ζ)
    (hK : Nat.card K = 2) (e : ↥E) :
    ((fr.rho hK e : ↥(omegaQ (K := K) t δ)) :
      GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      otau ζ t δ (fr.coord (Additive.ofMul e)) := by
  show (rhoGL fr e : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      otau ζ t δ (fr.coord (Additive.ofMul e))
  exact coe_rhoGL fr e

omit [Finite G] in
theorem OrthFrame.rho_eq_otau (fr : OrthFrame H E hEN K t δ ζ)
    (hK : Nat.card K = 2) (u : PlaneRaw.V t) :
    fr.rho hK (Additive.toMul (fr.coord.symm u)) =
      ⟨otau ζ t δ u, orthTauMemOmega_holds ζ t δ hK u⟩ := by
  apply Subtype.ext
  rw [OrthFrame.coe_rho, ofMul_toMul, AddEquiv.apply_symm_apply]

omit [Finite G] in
private theorem equivariant (fr : OrthFrame H E hEN K t δ ζ)
    (hK : Nat.card K = 2) : Equivariant hEN fr.π (fr.rho hK) := by
  intro a h
  obtain ⟨u, rfl⟩ := fr.τ.surjective a
  apply Subtype.ext
  have hcoord : fr.coord (Additive.ofMul (fr.τ u)) =
      fun i => Multiplicative.toAdd (u i) := by
    funext i
    simp [OrthFrame.coord]
  have hv : Additive.toMul (fr.coord.symm
      (fun i => Multiplicative.toAdd (u i))) = fr.τ u := by
    rw [← hcoord, AddEquiv.symm_apply_apply]
    rfl
  have hre : fr.rho hK (fr.τ u) =
      ⟨otau ζ t δ (fun i => Multiplicative.toAdd (u i)),
        orthTauMemOmega_holds ζ t δ hK _⟩ := by
    rw [← hv, fr.rho_eq_otau hK (fun i => Multiplicative.toAdd (u i))]
  rw [hre]
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using fr.intertwine u h

omit [Finite G] [Finite K] [CharP K 2] in
theorem OrthFrame.not_three_dvd_card_ker (fr : OrthFrame H E hEN K t δ ζ)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥H)) : ¬ 3 ∣ Nat.card fr.π.ker :=
  fun h => hZ3 (h.trans (Subgroup.card_dvd_of_le fr.ker_le))

omit [Finite G] [Finite K] [CharP K 2] in
private theorem component_eq (fr : OrthFrame H E hEN K t δ ζ) (c : PlaneRaw.Code t) :
    fr.component c =
      (⁅(oYcode ζ t δ c).comap fr.π, (oYcode ζ t δ c).comap fr.π⁆).map H.subtype :=
  rfl

omit [Finite G] in
private theorem mem_range_rho_iff (fr : OrthFrame H E hEN K t δ ζ)
    (hK : Nat.card K = 2) {A : Subgroup G} (hAE : A ≤ E) (r : ↥(omegaQ (K := K) t δ)) :
    r ∈ ((fr.rho hK).comp (Subgroup.inclusion hAE)).range ↔
      ∃ u ∈ ggLinImage (p := 3) fr.coord A,
        r = ⟨otau ζ t δ u, orthTauMemOmega_holds ζ t δ hK u⟩ := by
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
    rw [MonoidHom.comp_apply, hinc, fr.rho_eq_otau hK u]

omit [Finite G] in
private theorem centralizer_range_rho (fr : OrthFrame H E hEN K t δ ζ)
    (hK : Nat.card K = 2) {A : Subgroup G} (hAE : A ≤ E) :
    Subgroup.centralizer (((fr.rho hK).comp (Subgroup.inclusion hAE)).range :
        Subgroup ↥(omegaQ (K := K) t δ)) =
      (Subgroup.centralizer (oTorusSet ζ t δ (ggLinImage (p := 3) fr.coord A))).comap
        (omegaQ (K := K) t δ).subtype := by
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · rintro hg x hx
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    exact congrArg Subtype.val (hg ⟨otau ζ t δ u, orthTauMemOmega_holds ζ t δ hK u⟩
      ((mem_range_rho_iff fr hK hAE _).2 ⟨u, hu, rfl⟩))
  · intro hg r hr
    obtain ⟨u, hu, rfl⟩ := (mem_range_rho_iff fr hK hAE r).1 hr
    exact Subtype.ext (hg (otau ζ t δ u)
      ⟨liftV t δ u, Submodule.mem_map.mpr ⟨u, hu, rfl⟩, rfl⟩)

omit [Finite G] in
theorem OrthFrame.pi_eq_rho (fr : OrthFrame H E hEN K t δ ζ)
    (hK : Nat.card K = 2) (ht : 4 ≤ t) (e : ↥E) (he : (e : G) ∈ H) :
    fr.π ⟨e, he⟩ = fr.rho hK e := by
  have hs : (Even t ∧ 3 ≤ t + δ.val) ∨ (Odd t ∧ 2 ≤ t + δ.val) := by
    rcases Nat.even_or_odd t with hev | hod
    · exact Or.inl ⟨hev, by omega⟩
    · exact Or.inr ⟨hod, by omega⟩
  have hcen : (fr.rho hK e)⁻¹ * fr.π ⟨e, he⟩ ∈
      Subgroup.center ↥(omegaQ (K := K) t δ) := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨h, rfl⟩ := fr.surj r
    have h1 := equivariant fr hK e h
    have h2 : H.normalizerMonoidHom ⟨(e : G), hEN e.2⟩ h =
        ⟨e, he⟩ * h * (⟨e, he⟩ : ↥H)⁻¹ :=
      Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe H _ h)
    rw [h2, map_mul, map_mul, map_inv] at h1
    calc fr.π h * ((fr.rho hK e)⁻¹ * fr.π ⟨e, he⟩)
        = (fr.rho hK e)⁻¹ * (fr.rho hK e * fr.π h *
            (fr.rho hK e)⁻¹) * fr.π ⟨e, he⟩ := by group
      _ = (fr.rho hK e)⁻¹ * (fr.π ⟨e, he⟩ * fr.π h *
            (fr.π ⟨e, he⟩)⁻¹) * fr.π ⟨e, he⟩ := by rw [h1]
      _ = (fr.rho hK e)⁻¹ * fr.π ⟨e, he⟩ * fr.π h := by group
  rw [center_omegaQ_eq_bot hK t δ hs, Subgroup.mem_bot] at hcen
  exact (inv_mul_eq_one.mp hcen).symm

omit [Finite G] in
theorem ycode_perfect (h7 : OrthIsQuasisimpleYcode) (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {c : PlaneRaw.Code t}
    (hc : PlaneRaw.admissible (.orthogonal δ) c) :
    ⁅oYcode ζ t δ c, oYcode ζ t δ c⁆ = oYcode ζ t δ c :=
  Subgroup.isPerfect_iff.1 (h7 ζ t δ hK hζ c hc).1

omit [Finite G] in
private theorem rho_commute_ycode_iff (hK : Nat.card K = 2)
    (u : PlaneRaw.V t) (c : PlaneRaw.Code t) :
    (∀ y ∈ oYcode ζ t δ c,
        (⟨otau ζ t δ u, orthTauMemOmega_holds ζ t δ hK u⟩ : ↥(omegaQ (K := K) t δ)) * y =
          y * ⟨otau ζ t δ u, orthTauMemOmega_holds ζ t δ hK u⟩) ↔
      ∀ g ∈ oYcode ζ t δ c,
        otau ζ t δ u * (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
          (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ u := by
  constructor
  · intro h g hg
    exact congrArg Subtype.val (h g hg)
  · intro h g hg
    exact Subtype.ext (h g hg)

omit [Finite G] in
private theorem mem_mapped_ycode_iff (hK : Nat.card K = 2)
    (u : PlaneRaw.V t) (c : PlaneRaw.Code t) :
    (⟨otau ζ t δ u, orthTauMemOmega_holds ζ t δ hK u⟩ : ↥(omegaQ (K := K) t δ)) ∈ oYcode ζ t δ c ↔
      otau ζ t δ u ∈ (oYcode ζ t δ c).map (omegaQ (K := K) t δ).subtype := by
  constructor
  · intro h
    exact Subgroup.mem_map.mpr ⟨_, h, rfl⟩
  · rintro ⟨y, hy, hye⟩
    have h1 : (⟨otau ζ t δ u, orthTauMemOmega_holds ζ t δ hK u⟩ : ↥(omegaQ (K := K) t δ)) = y :=
      Subtype.ext hye.symm
    rw [h1]
    exact hy

theorem orthComponentOccursIff_of
    (hC : OrthIsComponentOfCentralizerTorusSetIff) : OrthComponentOccursIff := by
  intro G _ _ H E t δ K _ _ _ hEN ζ ctx A hAE X
  have hp : IsPGroup 3 ↥A := fun a =>
    ⟨1, Subtype.ext (by simpa using ctx.hEab.2 (a : G) (hAE a.2))⟩
  have heq : Equivariant (hAE.trans hEN) ctx.fr.π
      ((ctx.fr.rho ctx.hK).comp (Subgroup.inclusion hAE)) :=
    fun a h => equivariant ctx.fr ctx.hK (Subgroup.inclusion hAE a) h
  rw [isComponentOfCoverIff_holds (hAE.trans hEN) ctx.fr.π
    ((ctx.fr.rho ctx.hK).comp (Subgroup.inclusion hAE)) hp ctx.fr.surj ctx.fr.ker_le
    (ctx.fr.not_three_dvd_card_ker ctx.hZ3) ctx.hHp heq X,
    centralizer_range_rho ctx.fr ctx.hK hAE]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨c, hc, hocc, rfl⟩ := (hC ζ t δ ctx.hK ctx.hζ _ Y).1 hY
    exact ⟨c, ⟨ctx.ht, hc⟩, hocc, rfl⟩
  · rintro ⟨c, hc, hocc, rfl⟩
    exact ⟨oYcode ζ t δ c,
      (hC ζ t δ ctx.hK ctx.hζ _ _).2 ⟨c, hc.2, hocc, rfl⟩, rfl⟩

theorem orthComponentCentEq_of (h7 : OrthIsQuasisimpleYcode)
    (h9 : OrthTauCommuteYcodeIff) : OrthComponentCentEq := by
  intro G _ _ H E t δ K _ _ _ hEN ζ ctx c hc
  have hadm : PlaneRaw.admissible (.orthogonal δ) c := hc.2
  obtain ⟨hmap, hperf⟩ := derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le
    (ycode_perfect h7 ctx.hK ctx.hζ hadm)
  have hXtop : commutator ↥(⁅(oYcode ζ t δ c).comap ctx.fr.π,
      (oYcode ζ t δ c).comap ctx.fr.π⁆) = ⊤ :=
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hperf)
  ext v
  rw [mem_ggLinImage]
  set e : ↥E := Additive.toMul (ctx.fr.coord.symm v) with he
  have hv : ctx.fr.coord (Additive.ofMul e) = v := by
    rw [he, ofMul_toMul, AddEquiv.apply_symm_apply]
  have hre : ctx.fr.rho ctx.hK e = ⟨otau ζ t δ v, orthTauMemOmega_holds ζ t δ ctx.hK v⟩ := by
    rw [he, ctx.fr.rho_eq_otau ctx.hK v]
  have key := commuteCoverIff_holds hEN ctx.fr.π (ctx.fr.rho ctx.hK)
    ctx.fr.ker_le (equivariant ctx.fr ctx.hK) _ hXtop e
  rw [hmap, hre] at key
  have hkey : (∀ x ∈ ⁅(oYcode ζ t δ c).comap ctx.fr.π,
        (oYcode ζ t δ c).comap ctx.fr.π⁆,
        (e : G) * (x : G) = (x : G) * (e : G)) ↔
      v ∈ PlaneRaw.cent (.orthogonal δ) c :=
    key.trans ((rho_commute_ycode_iff ctx.hK v c).trans
      (h9 ζ t δ ctx.hK ctx.hζ c hadm v))
  refine Iff.trans ?_ hkey
  rw [Subgroup.mem_centralizer_iff, component_eq]
  constructor
  · intro h x hx
    exact (h (x : G) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)).symm
  · intro h g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact (h x hx).symm

theorem orthComponentInsideEq_of (h7 : OrthIsQuasisimpleYcode)
    (h9 : OrthTauMemYcodeIff) : OrthComponentInsideEq := by
  intro G _ _ H E t δ K _ _ _ hEN ζ ctx c hc
  have hadm : PlaneRaw.admissible (.orthogonal δ) c := hc.2
  have hY := ycode_perfect h7 ctx.hK ctx.hζ hadm
  ext v
  rw [mem_ggLinImage]
  set e : ↥E := Additive.toMul (ctx.fr.coord.symm v) with he
  have hv : ctx.fr.coord (Additive.ofMul e) = v := by
    rw [he, ofMul_toMul, AddEquiv.apply_symm_apply]
  have heH : (e : G) ∈ H := ctx.hEH e.2
  have he3 : (⟨e, heH⟩ : ↥H) ^ 3 = 1 :=
    Subtype.ext (by simpa using ctx.hEab.2 (e : G) e.2)
  have hre : ctx.fr.rho ctx.hK e = ⟨otau ζ t δ v, orthTauMemOmega_holds ζ t δ ctx.hK v⟩ := by
    rw [he, ctx.fr.rho_eq_otau ctx.hK v]
  have key := memDerivedComapIff_holds ctx.fr.π ctx.fr.surj ctx.fr.ker_le
    (ctx.fr.not_three_dvd_card_ker ctx.hZ3) (oYcode ζ t δ c) hY ⟨e, heH⟩ he3
  rw [ctx.fr.pi_eq_rho ctx.hK ctx.ht e heH, hre] at key
  have hkey : (⟨e, heH⟩ : ↥H) ∈
      ⁅(oYcode ζ t δ c).comap ctx.fr.π, (oYcode ζ t δ c).comap ctx.fr.π⁆ ↔
        v ∈ PlaneRaw.inside (.orthogonal δ) c :=
    key.trans ((mem_mapped_ycode_iff ctx.hK v c).trans
      (h9 ζ t δ ctx.hK ctx.hζ c hadm v))
  refine Iff.trans ?_ hkey
  rw [component_eq]
  constructor
  · intro h
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp h
    have hx' : x = ⟨e, heH⟩ := Subtype.ext hxe
    rw [← hx']
    exact hx
  · intro h
    exact Subgroup.mem_map.mpr ⟨⟨e, heH⟩, h, rfl⟩

theorem orthComponentMarked_of (h7 : OrthIsQuasisimpleYcode) (h10 : OrthMarkedYcode) :
    OrthComponentMarked := by
  intro G _ _ H E t δ K _ _ _ hEN ζ ctx c hc
  have hadm : PlaneRaw.admissible (.orthogonal δ) c := hc.2
  obtain ⟨hmap, hperf⟩ := derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le
    (ycode_perfect h7 ctx.hK ctx.hζ hadm)
  have hY : LargeEvenMarking ↥((⁅(oYcode ζ t δ c).comap ctx.fr.π,
      (oYcode ζ t δ c).comap ctx.fr.π⁆).map ctx.fr.π)
      (fun lab _ _ _ _ _ => lab = PlaneRaw.label (.orthogonal δ) c) := by
    rw [hmap]
    exact h10 ζ t δ ctx.hK ctx.hζ c hadm
  have hX := (SCFourCover.largeEvenMarking_map_iff ctx.fr.ker_le hperf
    (fun lab => lab = PlaneRaw.label (.orthogonal δ) c)).2 hY
  exact largeEvenMarking_congr ((⁅(oYcode ζ t δ c).comap ctx.fr.π,
    (oYcode ζ t δ c).comap ctx.fr.π⁆).equivMapOfInjective H.subtype
      H.subtype_injective).symm (fun _ _ _ _ _ _ h => h) hX

end CFSG.StandardType.GGQ2Frame.OrthPlacement
