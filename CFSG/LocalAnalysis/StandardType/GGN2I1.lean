module

public import CFSG.LocalAnalysis.StandardType.GGN2Defs
public import CFSG.LocalAnalysis.StandardType.GGN2I1Core
public import CFSG.LocalAnalysis.StandardType.GGTPNI1
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UGroup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltrn2i1a_inLambda2_D41 : LargeEvenInLambda2 (⟨.D, 4, 1⟩ : LargeEvenLabel) := by
  simp [LargeEvenInLambda2]

private theorem ltrn2i1a_eq_D41_of_ggLabelIso {lab : LargeEvenLabel}
    (hiso : GGLabelIso lab ⟨.D, 4, 1⟩) : lab = ⟨.D, 4, 1⟩ := by
  rcases hiso with h | h | h | h | h | h | h | h
  · exact h
  · exact absurd h.2.1 (by decide)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.rank h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by simp)

private theorem ltrn2i1a_conj_injective {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot]
  have hxc : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun f : MulAut G => f y) hx
    rw [MulAut.one_apply, MulAut.conj_apply] at h
    have h' : x * y = y * x := by
      have := congrArg (fun t => t * x) h
      simpa [mul_assoc] using this
    exact h'.symm
  rw [hZ, Subgroup.mem_bot] at hxc
  exact hxc

private theorem ltrn2i1a_isElemAbelian_range_of_comm {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    (hcomm : ∀ a b : X, a * b = b * a) (hexp : ∀ a : X, a ^ p = 1) (f : X →* Y) :
    IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨a, rfl⟩⟩ := u
    obtain ⟨_, ⟨b, rfl⟩⟩ := v
    apply Subtype.ext
    change f a * f b = f b * f a
    rw [← map_mul, ← map_mul, hcomm a b]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hexp a, map_one]

private theorem ltrn2i1a_ggInducedAut_conj {X : Type*} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (g : X) :
    ggInducedAut θ (MulAut.conj g : MulAut X) =
      (MulAut.conj (θ (QuotientGroup.mk' (Subgroup.center X) g)) : MulAut R) := by
  ext w
  obtain ⟨q, rfl⟩ := θ.surjective w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
  have hx : (QuotientGroup.mk' (Subgroup.center X)) x = ((x : X) : X ⧸ Subgroup.center X) :=
    congrFun (QuotientGroup.coe_mk' (Subgroup.center X)) x
  rw [hx, ggInducedAut_apply, MulAut.conj_apply]
  have hxm : ((g * x * g⁻¹ : X) : X ⧸ Subgroup.center X) =
      (QuotientGroup.mk' (Subgroup.center X) g) *
        (QuotientGroup.mk' (Subgroup.center X) x) *
        (QuotientGroup.mk' (Subgroup.center X) g)⁻¹ := by
    change QuotientGroup.mk' (Subgroup.center X) (g * x * g⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  rw [hxm, map_mul, map_mul, map_inv, MulAut.conj_apply]
  rfl

theorem ggI1PairRankOn_n2 :
    GGI1PairRankOn GGPairN2 := by
  intro p hp hp2 L _ _ J y E labL labJ hΛL hΛJ hP hhasL hhasJ hy hyE hEab hcomp hfix hmark
  obtain ⟨hp3, hlabL, hlabJ⟩ := hP
  subst hp3
  subst hlabL
  subst hlabJ
  obtain ⟨hperf, lab, hΛlab, hraw⟩ := hmark
  have hhas_lab : GGHasLabel lab (L ⧸ Subgroup.center L) :=
    largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, hθ⟩ := hq
      obtain ⟨θ, -⟩ := hθ
      exact ⟨θ⟩) hraw
  have hiso := ggLabelRigidInput_holds lab ⟨.D, 4, 1⟩ (L ⧸ Subgroup.center L)
    hΛlab ltrn2i1a_inLambda2_D41 hhas_lab hhasL
  have hlab : lab = ⟨.D, 4, 1⟩ := ltrn2i1a_eq_D41_of_ggLabelIso hiso
  subst hlab
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeOmegaPlus] at hraw
  obtain ⟨k, hkfield, hkfin, hkcard, hQR⟩ := hraw
  letI : Field k := hkfield
  letI : Finite k := hkfin
  let R : Type := LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k 4))
  have hQR' : IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : L ⧸ Subgroup.center L ≃* R,
        GGInducedInn E θ (LargeEvenInnSet R) := hQR
  obtain ⟨hsimple, hnonab, θ, hind⟩ := hQR'
  let R₀ := L ⧸ Subgroup.center L
  let q : L →* R₀ := QuotientGroup.mk' (Subgroup.center L)
  haveI : Group.IsPerfect L := ⟨hperf⟩
  haveI : Finite R₀ := Finite.of_surjective q (QuotientGroup.mk'_surjective _)
  have hZR₀ : Subgroup.center R₀ = ⊥ := by
    change Subgroup.center (L ⧸ Subgroup.center L) = ⊥
    exact Group.IsPerfect.center_quotient_center_eq_bot (G := L)
  have hZR : Subgroup.center R = ⊥ := by
    rw [← Subgroup.map_center_eq θ, hZR₀, Subgroup.map_bot]
  have hconj_injR : Function.Injective (MulAut.conj : R →* MulAut R) :=
    ltrn2i1a_conj_injective hZR
  have hconjθ_inj :
      Function.Injective (fun s : R₀ => (MulAut.conj : R →* MulAut R) (θ s)) := by
    intro a b hab
    exact θ.injective (hconj_injR hab)
  have hinner : ∀ e : E, ∃ s : R₀, ggInducedAut θ ((e : E) : MulAut L) = MulAut.conj (θ s) := by
    intro e
    obtain ⟨s, hs⟩ := hind ((e : E) : MulAut L) e.2
    exact ⟨θ.symm s, by rw [MulEquiv.apply_symm_apply]; exact hs.symm⟩
  let φFun : E → R₀ := fun e => Classical.choose (hinner e)
  have hφFunspec : ∀ e : E,
      ggInducedAut θ ((e : E) : MulAut L) = MulAut.conj (θ (φFun e)) :=
    fun e => Classical.choose_spec (hinner e)
  have hφFun_one : φFun 1 = 1 := by
    apply hconjθ_inj
    calc MulAut.conj (θ (φFun 1))
        = ggInducedAut θ ((1 : E) : MulAut L) := (hφFunspec 1).symm
      _ = 1 := map_one _
      _ = MulAut.conj (θ (1 : R₀)) := by rw [map_one, map_one]
  have hφFun_mul : ∀ e f : E, φFun (e * f) = φFun e * φFun f := by
    intro e f
    apply hconjθ_inj
    calc MulAut.conj (θ (φFun (e * f)))
        = ggInducedAut θ (((e * f : E) : MulAut L)) := (hφFunspec (e * f)).symm
      _ = ggInducedAut θ ((e : E) : MulAut L) * ggInducedAut θ ((f : E) : MulAut L) :=
            map_mul _ _ _
      _ = MulAut.conj (θ (φFun e)) * MulAut.conj (θ (φFun f)) := by
            rw [hφFunspec e, hφFunspec f]
      _ = MulAut.conj (θ (φFun e * φFun f)) := by rw [map_mul, map_mul]
  let φ : E →* R₀ :=
    { toFun := φFun
      map_one' := hφFun_one
      map_mul' := hφFun_mul }
  have hφspec : ∀ e : E, ggInducedAut θ ((e : E) : MulAut L) = MulAut.conj (θ (φ e)) :=
    fun e => hφFunspec e
  let yE : E := ⟨y, hyE⟩
  let F : Subgroup R₀ := φ.range
  let r : R₀ := φ yE
  have hyE3 : yE ^ 3 = 1 := Subtype.ext (by simpa using hEab.2 y hyE)
  have hr3 : r ^ 3 = 1 := by
    change (φ yE) ^ 3 = 1
    rw [← map_pow φ yE 3, hyE3, map_one]
  have hr1 : r ≠ 1 := by
    intro h1
    apply hy
    apply ggInducedAut_injective_of_perfect hperf θ
    rw [map_one, hφspec yE, show φ yE = 1 from h1, map_one, map_one]
  have hF : IsElemAbelian 3 F :=
    ltrn2i1a_isElemAbelian_range_of_comm
      (fun a b => hEab.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hEab.2 (a : MulAut L) a.2)) φ
  have hrF : r ∈ F := ⟨yE, rfl⟩
  have hK₀ : Assembly.IsComponentOf (J.map q) (Subgroup.centralizer ({r} : Set R₀)) := by
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : L, q y₀ = r := QuotientGroup.mk'_surjective _ r
    have hconjy₀ : ggInducedAut θ (MulAut.conj y₀ : MulAut L) = ggInducedAut θ y := by
      rw [ltrn2i1a_ggInducedAut_conj, hy₀, hφspec yE]
    have hyconj : MulAut.conj y₀ = y :=
      ggInducedAut_injective_of_perfect hperf θ hconjy₀
    have hcent0 : Subgroup.centralizer ({y₀} : Set L) = ggAutFixedSubgroup y := by
      ext z
      rw [Subgroup.mem_centralizer_singleton_iff, mem_ggAutFixedSubgroup]
      constructor
      · intro hz
        rw [← hyconj, MulAut.conj_apply, show y₀ * z = z * y₀ from hz.symm]
        group
      · intro hz
        have h1 : MulAut.conj y₀ z = z := by rw [hyconj]; exact hz
        rw [MulAut.conj_apply] at h1
        calc z * y₀ = (y₀ * z * y₀⁻¹) * y₀ := by rw [h1]
          _ = y₀ * z := by group
    have hJcomp0 : Assembly.IsComponentOf J (Subgroup.centralizer ({y₀} : Set L)) := by
      rw [hcent0]
      exact hcomp
    have hopen : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({y₀} : Set L)) :=
      (isComponentOf_iff_open).mp hJcomp0
    have hKopen := TableCRes.isComponentOf_map_centralizer_central (Z := Subgroup.center L)
      le_rfl ({y₀} : Set L) hopen
    have hset : q '' ({y₀} : Set L) = {r} := by
      rw [Set.image_singleton, hy₀]
    have hK' : Assembly.IsComponentOf (J.map q)
        (Subgroup.centralizer (q '' ({y₀} : Set L))) :=
      (isComponentOf_iff_open).mpr hKopen
    rwa [hset] at hK'
  have hKlab : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel)
      (↥(J.map q) ⧸ Subgroup.center ↥(J.map q)) := by
    obtain ⟨eJ⟩ := TableCRes.centerQuot_equiv_map_central (Z := Subgroup.center L) (J := J)
      le_rfl (show Group.IsPerfect ↥J from ⟨hcomp.2.2.1⟩)
    exact ggHasLabel_of_mulEquiv eJ hhasJ
  have hFK : ∀ e ∈ F, ∀ j ∈ J.map q, e * j = j * e := by
    intro e he j hj
    obtain ⟨a, rfl⟩ := he
    obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.mp hj
    have hfix_a : (a : MulAut L) j₀ = j₀ := hfix (a : E) a.2 j₀ hj₀
    have h1 : ggInducedAut θ ((a : E) : MulAut L) (θ (q j₀)) = θ (q j₀) := by
      change ggInducedAut θ ((a : E) : MulAut L)
          (θ ((j₀ : L) : L ⧸ Subgroup.center L)) = θ ((j₀ : L) : L ⧸ Subgroup.center L)
      rw [ggInducedAut_apply, hfix_a]
    have h2 : MulAut.conj (θ (φ a)) (θ (q j₀)) = θ (q j₀) := by
      rw [← hφspec a]
      exact h1
    have h3 : θ (φ a) * θ (q j₀) = θ (q j₀) * θ (φ a) := by
      rw [MulAut.conj_apply] at h2
      calc θ (φ a) * θ (q j₀)
          = (θ (φ a) * θ (q j₀) * (θ (φ a))⁻¹) * θ (φ a) := by group
        _ = θ (q j₀) * θ (φ a) := by rw [h2]
    apply θ.injective
    rw [map_mul, map_mul]
    exact h3
  have hcore : F ≤ Subgroup.zpowers r :=
    ggN2I1_core (R := R₀) hhasL hr3 hr1 hK₀ hKlab hF hrF hFK
  intro e he
  let eE : E := ⟨e, he⟩
  have heF : φ eE ∈ F := ⟨eE, rfl⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hcore heF)
  refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
  have hkey : ggInducedAut θ (e : MulAut L) = (ggInducedAut θ y) ^ m := by
    rw [hφspec eE, ← hm, map_zpow, map_zpow, ← hφspec yE]
  exact (ggInducedAut_injective_of_perfect hperf θ) (by rw [map_zpow, hkey])

end CFSG.StandardType

end
