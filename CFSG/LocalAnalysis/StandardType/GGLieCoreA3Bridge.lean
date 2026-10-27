module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3Defs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreBridge
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3KnownForms

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Minuscule
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

open scoped commutatorElement

private theorem ggLieA3Br_mem_center_of_commutators {A : Type} [Group A]
    (hperf : commutator A = ⊤) {N : Subgroup A} (hN : N ≤ Subgroup.center A) {x : A}
    (hx : ∀ z, ⁅x, z⁆ ∈ N) : x ∈ Subgroup.center A := by
  haveI : Group.IsPerfect A := ⟨hperf⟩
  have hstep : x ∈ Subgroup.upperCentralSeriesStep (Subgroup.center A) := fun z => hN (hx z)
  have h2 : Subgroup.upperCentralSeries A 2 = Subgroup.center A :=
    Group.IsPerfect.upperCentralSeries_eq_center A (by norm_num)
  refine h2 ▸ ?_
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro z
  rw [Subgroup.upperCentralSeries_one]
  exact hstep z

private noncomputable def ggLieA3Br_range_quotCenter_equiv {A B : Type} [Group A] [Group B]
    (f : A →* B) (hperf : commutator A = ⊤) (hker : f.ker ≤ Subgroup.center A) :
    f.range ⧸ Subgroup.center f.range ≃* A ⧸ Subgroup.center A := by
  let g : A →* f.range ⧸ Subgroup.center f.range :=
    (QuotientGroup.mk' (Subgroup.center f.range)).comp f.rangeRestrict
  have hgker : g.ker = Subgroup.center A := by
    ext a
    rw [MonoidHom.mem_ker]
    constructor
    · intro ha
      refine ggLieA3Br_mem_center_of_commutators hperf hker (fun z => ?_)
      have hza : f.rangeRestrict a ∈ Subgroup.center f.range :=
        (QuotientGroup.eq_one_iff _).mp ha
      have hcomm : f.rangeRestrict z * f.rangeRestrict a =
          f.rangeRestrict a * f.rangeRestrict z :=
        Subgroup.mem_center_iff.mp hza (f.rangeRestrict z)
      refine MonoidHom.mem_ker.mpr ?_
      rw [map_commutatorElement]
      refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
      simpa only [MonoidHom.coe_rangeRestrict, Subgroup.coe_mul] using
        (congrArg (fun x : f.range => (x : B)) hcomm).symm
    · intro ha
      show (QuotientGroup.mk' (Subgroup.center f.range)) (f.rangeRestrict a) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      obtain ⟨a', rfl⟩ := MonoidHom.rangeRestrict_surjective f y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp ha a']
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center f.range) y
    obtain ⟨a, rfl⟩ := MonoidHom.rangeRestrict_surjective f x
    exact ⟨a, rfl⟩
  have e := QuotientGroup.quotientKerEquivOfSurjective g hgsurj
  exact (((QuotientGroup.quotientMulEquivOfEq hgker).symm).trans e).symm

private theorem ggLieA3Br_caseK {X : Type} [Group X] {t : StatedLieTag} {G₀ D J : Subgroup X}
    (θ : ↥G₀ →* ModGL (langTag t) GGL) (hθker : θ.ker = Subgroup.center ↥G₀)
    (h9 : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (h10 : GGSixLSevenA3Case J) :
    GGSixLSevenA3Case ((J.subgroupOf G₀).map θ) := by
  have hJG₀ : J ≤ G₀ := h9.1.trans inf_le_left
  have hperf : commutator ↥J = ⊤ := h9.2.2.1
  let θJ : ↥J →* ModGL (langTag t) GGL := θ.comp (Subgroup.inclusion hJG₀)
  have hkerθJ : θJ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [Subgroup.mem_center_iff]
    intro j'
    have hcen : Subgroup.inclusion hJG₀ j ∈ Subgroup.center ↥G₀ := by
      rw [← hθker]
      exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hj)
    have hcomm := Subgroup.mem_center_iff.mp hcen (Subgroup.inclusion hJG₀ j')
    exact Subtype.ext (by simpa using congrArg Subtype.val hcomm)
  have hK : (J.subgroupOf G₀).map θ = θJ.range := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, hx⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j.1, hJG₀ j.2⟩, j.2, rfl⟩
  have hcase : GGSixLSevenA3Case θJ.range := by
    unfold GGSixLSevenA3Case at h10 ⊢
    exact LieModel.of_mulEquiv (ggLieA3Br_range_quotCenter_equiv θJ hperf hkerθJ).symm h10
  exact hK.symm ▸ hcase

private theorem ggLieA3Br_conj_action {X : Type} [Group X] {t : StatedLieTag} {G₀ : Subgroup X}
    (θ : ↥G₀ →* ModGL (langTag t) GGL) {d : X}
    (hdN : d ∈ Subgroup.normalizer (G₀ : Set X))
    {a : ModGL (langTag t) GGL}
    (hpart : ∀ x : ↥G₀, ∀ hx : d * (x : X) * d⁻¹ ∈ G₀,
      θ ⟨d * (x : X) * d⁻¹, hx⟩ = a * θ x * a⁻¹)
    (g : ↥G₀) (x : ↥G₀) :
    θ ⟨(g : X) * d * (g : X)⁻¹ * (x : X) * ((g : X) * d * (g : X)⁻¹)⁻¹,
        (Subgroup.mem_normalizer_iff.mp
          (mul_mem (mul_mem (Subgroup.le_normalizer g.2) hdN)
            (inv_mem (Subgroup.le_normalizer g.2))) x).mp x.2⟩ =
      (θ g * a * (θ g)⁻¹) * θ x * (θ g * a * (θ g)⁻¹)⁻¹ := by
  have hu : (g : X) * d * (g : X)⁻¹ ∈ Subgroup.normalizer (G₀ : Set X) :=
    mul_mem (mul_mem (Subgroup.le_normalizer g.2) hdN) (inv_mem (Subgroup.le_normalizer g.2))
  set y : ↥G₀ := g⁻¹ * x * g with hy_def
  have hyd : d * (y : X) * d⁻¹ ∈ G₀ :=
    (Subgroup.mem_normalizer_iff.mp hdN (y : X)).mp y.2
  have hmem : (g : X) * d * (g : X)⁻¹ * (x : X) * ((g : X) * d * (g : X)⁻¹)⁻¹ ∈ G₀ :=
    (Subgroup.mem_normalizer_iff.mp hu x).mp x.2
  have heq : (⟨(g : X) * d * (g : X)⁻¹ * (x : X) * ((g : X) * d * (g : X)⁻¹)⁻¹, hmem⟩ : ↥G₀)
      = g * (⟨d * (y : X) * d⁻¹, hyd⟩ : ↥G₀) * g⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy_def]
    group
  rw [heq, map_mul, map_mul, map_inv, hpart y hyd]
  have hyθ : θ y = (θ g)⁻¹ * θ x * θ g := by
    rw [hy_def, map_mul, map_mul, map_inv]
  rw [hyθ]
  group

private theorem ggLieA3Br_center_e6_two :
    Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 1)) = ⊥ := by
  have h := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6
    (k := GaloisField 2 1)).1
  rw [GaloisField.card 2 1 (by norm_num)] at h
  refine Subgroup.eq_bot_of_card_eq _ ?_
  simpa using h

private theorem ggLieA3Br_known
    (hB : GGLieBridge) (h : GGLieA3Alg) (t : StatedLieTag)
    (ht : t = .E6 ∨ t = .F4 ∨ t = .twistedE6) : GGSixA3ConjKnown t := by
  intro X _ _ n f ψ G₀ D J h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hExc : GGExcFive t := by rcases ht with rfl | rfl | rfl <;> simp [GGExcFive]
  have hf : 1 ≤ f := (LieModel.admissible h3).2.1
  have hbundle : GGLieBridgeHyp t n f 3 ψ G₀ D :=
    ggLieBridgeHyp_of_a3Hyp (t := t) (X := X) (n := n) (f := f) (ψ := ψ) (G₀ := G₀)
      (D := D) (J := J) ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨θ, A, hθker, hθrange, hAfix, hAel, hAcard, hpart, hpart2, hcomp⟩ :=
    hB 3 t n f ψ G₀ D J Nat.prime_three (by decide) hExc hf hbundle
  let K : Subgroup (ModGL (langTag t) GGL) := (J.subgroupOf G₀).map θ
  have hKcomp : IsComponentOf K (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
      Subgroup.centralizer (A : Set (ModGL (langTag t) GGL))) := hcomp h9
  have hKcase : GGSixLSevenA3Case K := ggLieA3Br_caseK θ hθker h9 h10
  have hcardA : Nat.card A = 3 ^ 2 := by rw [hAcard, h8]
  have hAlg := h t ht f hf A K hAfix hAel hcardA hKcomp hKcase
  rcases ht with rfl | rfl | rfl
  ·
    obtain ⟨hf1, h, hh, hconj⟩ := hAlg.1 rfl
    subst hf1
    have hZuniv : Subgroup.center (ggU .E6 n 1).K = ⊥ := ggLieA3Br_center_e6_two
    have hψker : ψ.ker = ⊥ :=
      le_antisymm (h2.trans (le_of_eq hZuniv)) bot_le
    have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hψker
    have hcenterG₀ : Subgroup.center ↥G₀ = ⊥ := by
      have hmap := Subgroup.map_center_eq
        ((MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr h1))
      rw [hZuniv] at hmap
      simpa using hmap.symm
    have hθinj : Function.Injective θ := by
      rw [← MonoidHom.ker_eq_bot_iff θ, hθker]
      exact hcenterG₀
    have hJG₀ : J ≤ G₀ := h9.1.trans inf_le_left
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hθrange.symm ▸ hh)
    refine ⟨g.1, g.2, ?_⟩
    rintro y ⟨d, hd, rfl⟩
    obtain ⟨a, ha, hpartd⟩ := hpart d hd
    have hhah : h * a * h⁻¹ ∈ K := by
      have hmem : (MulAut.conj h).toMonoidHom a ∈ K := hconj ⟨a, ha, rfl⟩
      simpa using hmem
    change h * a * h⁻¹ ∈ (J.subgroupOf G₀).map θ at hhah
    rw [Subgroup.mem_map] at hhah
    obtain ⟨x₀, hx₀, hx₀eq⟩ := hhah
    let j : ↥J := ⟨(x₀ : X), hx₀⟩
    have hjθ : θ ⟨(j : X), hJG₀ j.2⟩ = h * a * h⁻¹ := hx₀eq
    have hgdgN : g.1 * d * g.1⁻¹ ∈ Subgroup.normalizer (G₀ : Set X) :=
      mul_mem (mul_mem (Subgroup.le_normalizer g.2) (h5 hd))
        (inv_mem (Subgroup.le_normalizer g.2))
    have hact : ∀ x : ↥G₀, ∀ hx : g.1 * d * g.1⁻¹ * (x : X) * (g.1 * d * g.1⁻¹)⁻¹ ∈ G₀,
        θ ⟨g.1 * d * g.1⁻¹ * (x : X) * (g.1 * d * g.1⁻¹)⁻¹, hx⟩ =
          (h * a * h⁻¹) * θ x * (h * a * h⁻¹)⁻¹ := by
      intro x hx
      have h1 := ggLieA3Br_conj_action θ (h5 hd) hpartd g x
      rw [hg] at h1
      exact h1
    have hcN : (j : X)⁻¹ * (g.1 * d * g.1⁻¹) ∈ Subgroup.normalizer (G₀ : Set X) :=
      mul_mem (inv_mem (Subgroup.le_normalizer (hJG₀ j.2))) hgdgN
    have hcC : (j : X)⁻¹ * (g.1 * d * g.1⁻¹) ∈ Subgroup.centralizer (G₀ : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hmem : (j : X)⁻¹ * (g.1 * d * g.1⁻¹) * (z : X) *
          ((j : X)⁻¹ * (g.1 * d * g.1⁻¹))⁻¹ ∈ G₀ :=
        (Subgroup.mem_normalizer_iff.mp hcN (z : X)).mp hz
      have hcx : (⟨(j : X)⁻¹ * (g.1 * d * g.1⁻¹) * (z : X) *
            ((j : X)⁻¹ * (g.1 * d * g.1⁻¹))⁻¹, hmem⟩ : ↥G₀) = ⟨(z : X), hz⟩ := by
        apply hθinj
        have hmemu : g.1 * d * g.1⁻¹ * (z : X) * (g.1 * d * g.1⁻¹)⁻¹ ∈ G₀ :=
          (Subgroup.mem_normalizer_iff.mp hgdgN (z : X)).mp hz
        have heq : (⟨(j : X)⁻¹ * (g.1 * d * g.1⁻¹) * (z : X) *
              ((j : X)⁻¹ * (g.1 * d * g.1⁻¹))⁻¹, hmem⟩ : ↥G₀) =
            (⟨(j : X), hJG₀ j.2⟩ : ↥G₀)⁻¹ *
              ⟨g.1 * d * g.1⁻¹ * (z : X) * (g.1 * d * g.1⁻¹)⁻¹, hmemu⟩ *
              (⟨(j : X), hJG₀ j.2⟩ : ↥G₀) := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [heq, map_mul, map_mul, map_inv, hact ⟨z, hz⟩ hmemu, hjθ]
        group
      have hcxX : (j : X)⁻¹ * (g.1 * d * g.1⁻¹) * (z : X) *
          ((j : X)⁻¹ * (g.1 * d * g.1⁻¹))⁻¹ = (z : X) := congrArg Subtype.val hcx
      calc (z : X) * ((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) =
          ((j : X)⁻¹ * (g.1 * d * g.1⁻¹) * (z : X) *
            ((j : X)⁻¹ * (g.1 * d * g.1⁻¹))⁻¹) * ((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) := by
            rw [hcxX]
        _ = ((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) * (z : X) := by group
    have hd3 : d ^ 3 = 1 := h7.2 d hd
    have hu3 : (g.1 * d * g.1⁻¹) ^ 3 = 1 := by
      rw [show g.1 * d * g.1⁻¹ = (MulAut.conj g.1) d from (MulAut.conj_apply g.1 d).symm,
        ← map_pow, hd3, map_one]
    have hjc : Commute (j : X) ((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) :=
      Subgroup.mem_centralizer_iff.mp hcC (j : X) (hJG₀ j.2)
    have hj3c3 : (j : X) ^ 3 * ((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) ^ 3 = 1 := by
      rw [← hjc.mul_pow 3]
      have : (j : X) * ((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) = g.1 * d * g.1⁻¹ := by group
      rw [this, hu3]
    have hj3_eq : (j : X) ^ 3 = (((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) ^ 3)⁻¹ := by
      calc (j : X) ^ 3 = (j : X) ^ 3 * 1 := by rw [mul_one]
        _ = (j : X) ^ 3 * (((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) ^ 3 *
              (((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) ^ 3)⁻¹) := by rw [mul_inv_cancel, mul_one]
        _ = ((j : X) ^ 3 * ((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) ^ 3) *
              (((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) ^ 3)⁻¹ := by group
        _ = 1 * (((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) ^ 3)⁻¹ := by rw [hj3c3]
        _ = (((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) ^ 3)⁻¹ := by rw [one_mul]
    have hj3_center : (⟨(j : X) ^ 3, pow_mem (hJG₀ j.2) 3⟩ : ↥G₀) ∈
        Subgroup.center ↥G₀ := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply Subtype.ext
      show (z : X) * (j : X) ^ 3 = (j : X) ^ 3 * (z : X)
      have hc3C : (((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) ^ 3)⁻¹ ∈
          Subgroup.centralizer (G₀ : Set X) :=
        inv_mem (pow_mem hcC 3)
      have hz := Subgroup.mem_centralizer_iff.mp hc3C (z : X) z.2
      rw [hj3_eq]
      exact hz
    have hj3_one : (j : X) ^ 3 = 1 := by
      have h := hj3_center
      rw [hcenterG₀] at h
      exact congrArg Subtype.val (Subgroup.mem_bot.mp h)
    have hc3 : ((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) ^ 3 = 1 := by
      have := hj3c3
      rw [hj3_one] at this
      simpa using this
    have hc1 : (j : X)⁻¹ * (g.1 * d * g.1⁻¹) = 1 := by
      have hord3 : orderOf ((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) ∣ 3 :=
        orderOf_dvd_iff_pow_eq_one.mpr hc3
      have hordC : orderOf ((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) ∣
          Nat.card (Subgroup.centralizer (G₀ : Set X)) :=
        Subgroup.orderOf_dvd_natCard _ hcC
      rcases Nat.prime_three.eq_one_or_self_of_dvd
        (orderOf ((j : X)⁻¹ * (g.1 * d * g.1⁻¹))) hord3 with h | h
      · exact orderOf_eq_one_iff.mp h
      · exfalso
        exact h4 (h ▸ hordC)
    have hu_eq : g.1 * d * g.1⁻¹ = (j : X) := by
      have hju : (j : X) * ((j : X)⁻¹ * (g.1 * d * g.1⁻¹)) = g.1 * d * g.1⁻¹ := by
        group
      rw [← hju, hc1, mul_one]
    change g.1 * d * g.1⁻¹ ∈ J
    rw [hu_eq]
    exact j.2
  · exact (hAlg.2 (Or.inl rfl)).elim
  · exact (hAlg.2 (Or.inr rfl)).elim

theorem ggSixA3ConjKnownTags_of_alg
    (hB : GGLieBridge) (h : GGLieA3Alg) : GGSixA3ConjKnownTags :=
  ⟨ggLieA3Br_known hB h .E6 (Or.inl rfl), ggLieA3Br_known hB h .F4 (Or.inr (Or.inl rfl)),
    ggLieA3Br_known hB h .twistedE6 (Or.inr (Or.inr rfl))⟩

end CFSG.StandardType.LieCore
