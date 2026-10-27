module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHolds
public import CFSG.LocalAnalysis.StandardType.GGFinModelRoots
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate13604
public import Certificates.Certificate13605
public import Certificates.Certificate13691
public import Certificates.Certificate13720
public import Certificates.Certificate13721
public import Certificates.Certificate13722
public import Certificates.Certificate13723
public import Certificates.Certificate13724

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open scoped commutatorElement
open CFSG.StandardType.LieCore

private theorem a6glue_exists_complement
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {D D₀ : Subgroup X} (hD0le : D₀ ≤ D) (hEA : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) :
    ∃ D' : Subgroup X, D' ≤ D ∧ D₀ ⊓ D' = ⊥ ∧ D₀ ⊔ D' = D := by
  classical
  by_cases h0 : D₀ = ⊥
  · exact ⟨D, le_rfl, by rw [h0]; simp, by rw [h0]; simp⟩
  by_cases hD : D₀ = D
  · exact ⟨⊥, bot_le, by rw [hD]; simp, by rw [hD]; simp⟩
  have hcardD0le : Nat.card ↥D₀ ≤ Nat.card ↥D :=
    Nat.card_le_card_of_injective (fun x : ↥D₀ => (⟨x.1, hD0le x.2⟩ : ↥D))
      (fun a b h => Subtype.ext (congrArg (fun z : ↥D => (z : X)) h))
  have hdiv : Nat.card D₀ ∣ p ^ 2 := by
    have h1 : Nat.card ↥(D₀.subgroupOf D) ∣ Nat.card ↥D := Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD0le).toEquiv] at h1
    rwa [hDc] at h1
  have hx : ∃ x ∈ D₀, x ≠ 1 := by
    by_contra h
    push Not at h
    exact h0 ((Subgroup.eq_bot_iff_forall D₀).mpr h)
  obtain ⟨x, hxmem, hxne⟩ := hx
  have : Fact p.Prime := ⟨hp⟩
  have hxord : orderOf x = p := orderOf_eq_prime (hEA.2 x (hD0le hxmem)) hxne
  have hzx_le : Subgroup.zpowers x ≤ D₀ := Subgroup.zpowers_le.mpr hxmem
  have hp_le : p ≤ Nat.card ↥D₀ := by
    have h1 : Nat.card ↥(Subgroup.zpowers x) ≤ Nat.card ↥D₀ :=
      Nat.card_le_card_of_injective (fun y : ↥(Subgroup.zpowers x) => (⟨y.1, hzx_le y.2⟩ : ↥D₀))
        (fun a b h => Subtype.ext (congrArg (fun z : ↥D₀ => (z : X)) h))
    rwa [Nat.card_zpowers, hxord] at h1
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).mp hdiv
  have hk1 : k = 1 := by
    interval_cases k
    · rw [pow_zero] at hk_eq
      have := hp.two_le
      omega
    · rfl
    · exfalso
      apply hD
      refine Subgroup.eq_of_le_of_card_ge hD0le ?_
      rw [hDc, hk_eq]
  have hcardD0 : Nat.card ↥D₀ = p := by rw [hk_eq, hk1, pow_one]
  have hdex : ∃ d ∈ D, d ∉ D₀ := by
    by_contra h
    push Not at h
    exact hD (le_antisymm hD0le h)
  obtain ⟨d, hdD, hdD0⟩ := hdex
  have hdne : d ≠ 1 := fun h => hdD0 (h ▸ D₀.one_mem)
  have hD'le : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.mpr hdD
  have hD'card : Nat.card ↥(Subgroup.zpowers d) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hEA.2 d hdD) hdne
  refine ⟨Subgroup.zpowers d, hD'le, ?_, ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    by_contra hy1
    have hyD' : y ∈ Subgroup.zpowers d := hy.2
    have hyord : orderOf y = p := orderOf_eq_prime (hEA.2 y (hD'le hyD')) hy1
    have hzy_le : Subgroup.zpowers y ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hyD'
    have hzy_card : Nat.card ↥(Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hyord]
    have heq : Subgroup.zpowers y = Subgroup.zpowers d := by
      refine Subgroup.eq_of_le_of_card_ge hzy_le ?_
      rw [hzy_card, hD'card]
    have hdmem : d ∈ Subgroup.zpowers y := by
      rw [heq]; exact Subgroup.mem_zpowers d
    exact hdD0 ((Subgroup.zpowers_le.mpr hy.1) hdmem)
  · have hHle : D₀ ⊔ Subgroup.zpowers d ≤ D := sup_le hD0le hD'le
    have hHdvd : Nat.card ↥(D₀ ⊔ Subgroup.zpowers d) ∣ p ^ 2 := by
      have h1 : Nat.card ↥((D₀ ⊔ Subgroup.zpowers d).subgroupOf D) ∣ Nat.card ↥D :=
        Subgroup.card_subgroup_dvd_card _
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv] at h1
      rwa [hDc] at h1
    have hHne1 : Nat.card ↥(D₀ ⊔ Subgroup.zpowers d) ≠ 1 := by
      intro h1
      have hsub : Subsingleton ↥(D₀ ⊔ Subgroup.zpowers d) := (Nat.card_eq_one_iff_unique.mp h1).1
      have hdmem : d ∈ D₀ ⊔ Subgroup.zpowers d :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
      have hEq : (⟨d, hdmem⟩ : ↥(D₀ ⊔ Subgroup.zpowers d)) =
          ⟨1, (D₀ ⊔ Subgroup.zpowers d).one_mem⟩ := Subsingleton.elim _ _
      exact hdne (Subtype.ext_iff.mp hEq)
    have hHneP : Nat.card ↥(D₀ ⊔ Subgroup.zpowers d) ≠ p := by
      intro hP
      have heqH : D₀ = D₀ ⊔ Subgroup.zpowers d :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hP, hcardD0])
      have hdmem : d ∈ D₀ ⊔ Subgroup.zpowers d :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
      rw [← heqH] at hdmem
      exact hdD0 hdmem
    obtain ⟨j, hj_le, hj_eq⟩ := (Nat.dvd_prime_pow hp).mp hHdvd
    have hj : j = 2 := by
      interval_cases j
      · rw [pow_zero] at hj_eq
        exact absurd hj_eq hHne1
      · rw [pow_one] at hj_eq
        exact absurd hj_eq hHneP
      · rfl
    refine Subgroup.eq_of_le_of_card_ge hHle ?_
    rw [hDc, hj_eq, hj]

private theorem a6glue_mem_center_of_commutators {A : Type} [Group A]
    (hperf : commutator A = ⊤) {N : Subgroup A} (hN : N ≤ Subgroup.center A) {x : A}
    (hx : ∀ z, ⁅x, z⁆ ∈ N) : x ∈ Subgroup.center A := by
  have : Group.IsPerfect A := ⟨hperf⟩
  have hstep : x ∈ Subgroup.upperCentralSeriesStep (Subgroup.center A) := fun z => hN (hx z)
  have h2 : Subgroup.upperCentralSeries A 2 = Subgroup.center A :=
    Group.IsPerfect.upperCentralSeries_eq_center A (by norm_num)
  refine h2 ▸ ?_
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro z
  rw [Subgroup.upperCentralSeries_one]
  exact hstep z

private noncomputable def a6glue_range_quotCenter_equiv {A B : Type} [Group A] [Group B]
    (f : A →* B) (hperf : commutator A = ⊤) (hker : f.ker ≤ Subgroup.center A) :
    f.range ⧸ Subgroup.center f.range ≃* A ⧸ Subgroup.center A := by
  let g : A →* f.range ⧸ Subgroup.center f.range :=
    (QuotientGroup.mk' (Subgroup.center f.range)).comp f.rangeRestrict
  have hgker : g.ker = Subgroup.center A := by
    ext a
    rw [MonoidHom.mem_ker]
    constructor
    · intro ha
      refine a6glue_mem_center_of_commutators hperf hker (fun z => ?_)
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

theorem a6glue_reduce
    {t : StatedLieTag} (ht : GGExcFive t)
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ D J : Subgroup X} (hr : ψ.range = G₀) (hk : ψ.ker ≤ Subgroup.center (ggU t n f).K)
    (hLie : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hDn : D ≤ Subgroup.normalizer (G₀ : Set X))
    (hdiag : ∀ d ∈ D, GGPsiInnerDiag (ggU t n f).D ψ d) (hEA : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X))) :
    1 ≤ f ∧ ∃ A K : Subgroup (ModGL (langTag t) GGL), A ≤ ggFixGp t f ∧ IsElemAbelian p A ∧
      Nat.card A ≤ p ^ 2 ∧
      IsComponentOf K (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
        Subgroup.centralizer (A : Set (ModGL (langTag t) GGL))) ∧
      Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* (↥K ⧸ Subgroup.center ↥K)) := by
  classical
  have hf : 1 ≤ f := (LieModel.admissible hLie).2.1
  refine ⟨hf, ?_⟩
  set D₀ : Subgroup X := D ⊓ Subgroup.centralizer (G₀ : Set X) with hD₀
  have hD0le : D₀ ≤ D := inf_le_left
  obtain ⟨D', hD'le, hD0inf, hD0sup⟩ := a6glue_exists_complement hp hD0le hEA hDc
  have hEA' : IsElemAbelian p D' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hEA.2 x (hD'le hx)⟩
    exact Subtype.ext (congrArg (fun z : ↥D => (z : X))
      ((hEA.1).is_comm.comm ⟨a, hD'le a.2⟩ ⟨b, hD'le b.2⟩))
  have hD'C : D' ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ := by
    have h1 : D' ⊓ Subgroup.centralizer (G₀ : Set X) ≤
        D ⊓ Subgroup.centralizer (G₀ : Set X) :=
      le_inf (le_trans inf_le_left hD'le) inf_le_right
    rw [← hD₀] at h1
    have h2 : D' ⊓ Subgroup.centralizer (G₀ : Set X) ≤ D₀ ⊓ D' := le_inf h1 inf_le_left
    rw [hD0inf] at h2
    exact le_bot_iff.mp h2
  have hG0C0 : G₀ ≤ Subgroup.centralizer (D₀ : Set X) :=
    Subgroup.le_centralizer_iff.mpr inf_le_right
  have hCeq : G₀ ⊓ Subgroup.centralizer (D' : Set X) =
      G₀ ⊓ Subgroup.centralizer (D : Set X) := by
    refine le_antisymm ?_ ?_
    · refine le_inf inf_le_left ?_
      intro g hg
      have hg0 : g ∈ Subgroup.centralizer (D₀ : Set X) := hG0C0 hg.1
      have hg' : g ∈ Subgroup.centralizer (D' : Set X) := hg.2
      rw [← hD0sup, Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_union] at hh
      rcases hh with hh | hh
      · exact Subgroup.mem_centralizer_iff.mp hg0 h hh
      · exact Subgroup.mem_centralizer_iff.mp hg' h hh
    · refine le_inf inf_le_left ?_
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_iff.mp hg.2 h (hD'le hh)
  have hJG : J ≤ G₀ := fun x hx => (hJ.1 hx).1
  have hJ' : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D' : Set X)) := by
    rw [hCeq]; exact hJ
  have hbundle : GGLieBridgeHyp t n f p ψ G₀ D' :=
    ⟨hr, hk, hLie, (fun d hd => hDn (hD'le hd)), (fun d hd => hdiag d (hD'le hd)),
      hEA', hD'C⟩
  obtain ⟨θ, A, hθker, hθrange, hAfix, hAel, hAcard, -, -, hcomp⟩ :=
    ggLieBridge_holds p t n f ψ G₀ D' J hp hp2 ht hf hbundle
  let K : Subgroup (ModGL (langTag t) GGL) := (J.subgroupOf G₀).map θ
  have hKcomp : IsComponentOf K (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
      Subgroup.centralizer (A : Set (ModGL (langTag t) GGL))) := hcomp hJ'
  have hAcard_le : Nat.card A ≤ p ^ 2 := by
    rw [hAcard]
    calc Nat.card D' ≤ Nat.card D :=
          Nat.card_le_card_of_injective (fun x : ↥D' => (⟨x.1, hD'le x.2⟩ : ↥D))
            (fun a b h => Subtype.ext (congrArg (fun z : ↥D => (z : X)) h))
      _ = p ^ 2 := hDc
  have hcenter : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥K ⧸ Subgroup.center ↥K) := by
    let φ : ↥J →* ModGL (langTag t) GGL := θ.comp (Subgroup.inclusion hJG)
    have hrange : φ.range = K := by
      rw [MonoidHom.range_comp]
      rw [show K = Subgroup.map θ (J.subgroupOf G₀) from rfl]
      congr 1
      ext y
      constructor
      · intro hy
        obtain ⟨x, rfl⟩ := hy
        exact x.2
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    have hker : φ.ker ≤ Subgroup.center ↥J := by
      intro a ha
      rw [MonoidHom.mem_ker] at ha
      rw [Subgroup.mem_center_iff]
      intro b
      apply Subtype.ext
      have ha' : Subgroup.inclusion hJG a ∈ Subgroup.center ↥G₀ := by
        rw [← hθker]
        exact ha
      exact congrArg (fun z : ↥G₀ => (z : X))
        (Subgroup.mem_center_iff.mp ha' (Subgroup.inclusion hJG b))
    have e := a6glue_range_quotCenter_equiv φ (hJ.2.2).1 hker
    rw [hrange] at e
    exact ⟨e.symm⟩
  exact ⟨A, K, hAfix, hAel, hAcard_le, hKcomp, hcenter⟩

end CFSG.StandardType.A6Red
