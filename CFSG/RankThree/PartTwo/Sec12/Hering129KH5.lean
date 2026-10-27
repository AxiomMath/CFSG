module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KH4
import CFSG.RankThree.PartTwo.Sec12.Hering129KEa

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.Open (StatedScalars)
open Matrix (ProjGenLinGroup)


namespace Hering129KH5

variable {P : Type} [Group P] [Finite P] {Yh Bh : Subgroup P} {xh bh ch : P}
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem autIn_eq_range_comp {G : Type*} [Group G] (H X : Subgroup G) :
    Sec4.autIn H X = (X.normalizerMonoidHom.comp (Subgroup.inclusion
      (inf_le_right : H ⊓ Subgroup.normalizer (X : Set G) ≤
        Subgroup.normalizer (X : Set G)))).range := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

theorem normalizerMonoidHom_eq_one_iff {G : Type*} [Group G] (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    H.normalizerMonoidHom ⟨g, hg⟩ = 1 ↔ ∀ x ∈ H, g * x * g⁻¹ = x := by
  constructor
  · intro h x hx
    have h1 : ((H.normalizerMonoidHom ⟨g, hg⟩ ⟨x, hx⟩ : H) : G) =
        (((1 : MulAut H) ⟨x, hx⟩ : H) : G) := by
      rw [h]
    rw [MulAut.one_apply, Sec4.normalizerMonoidHom_apply_coe] at h1
    exact h1
  · intro h
    refine MulEquiv.ext fun ⟨x, hx⟩ => Subtype.ext ?_
    rw [MulAut.one_apply, Sec4.normalizerMonoidHom_apply_coe]
    exact h x hx

theorem statedScalars_le_ker_mk (K : Type) [Field K] :
    StatedScalars (Fin 3) K ≤
      (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).ker := by
  have hSZ : StatedScalars (Fin 3) K = Subgroup.center (GL (Fin 3) K) :=
    Matrix.GeneralLinearGroup.center_eq_range_scalar.symm
  rw [ProjGenLinGroup.ker_mk, hSZ]

noncomputable def psiAct [Yh.Normal] (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    [Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K))]
    (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K)) (A' : Subgroup P)
    (hA' : ∀ a ∈ A', ∃ y, Sec4.IsPGLAtP e a y) : A' →* ProjGenLinGroup (Fin 3) K :=
  (QuotientGroup.lift (StatedScalars (Fin 3) K)
    (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K)
    (statedScalars_le_ker_mk K)).comp (Sec4.pglHomP hK hq A' hA')

theorem psiAct_apply [Yh.Normal] (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    [Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K))]
    (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K)) (A' : Subgroup P)
    (hA' : ∀ a ∈ A', ∃ y, Sec4.IsPGLAtP e a y) (a : A') {y : GL (Fin 3) K}
    (hy : Sec4.IsPGLAtP e a y) :
    psiAct hK hq e A' hA' a = ProjGenLinGroup.mk y := by
  have h1 : Sec4.pglHomP hK hq A' hA' a = (QuotientGroup.mk y : GL (Fin 3) K ⧸
      StatedScalars (Fin 3) K) := Sec4.pglHomP_apply a hy
  rw [psiAct, MonoidHom.comp_apply, h1, QuotientGroup.lift_mk]

theorem psiAct_of_mem [Yh.Normal] (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    [Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K))]
    (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K)) (A' : Subgroup P)
    (hA' : ∀ a ∈ A', ∃ y, Sec4.IsPGLAtP e a y) {l : P} (hlA : l ∈ A') (hl : l ∈ Yh) :
    psiAct hK hq e A' hA' ⟨l, hlA⟩ =
      ((e ⟨l, hl⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  obtain ⟨s, hs, hsl⟩ := Subgroup.mem_map.mp (e ⟨l, hl⟩).2
  have hy : Sec4.IsPGLAtP e l s := Sec4.isPGLAtP_of_mem e hπ hl hs hsl.symm
  rw [psiAct_apply hK hq e A' hA' ⟨l, hlA⟩ hy]
  exact hsl

theorem psiAct_eq_one [Yh.Normal] (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    [Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K))]
    (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K)) (A' : Subgroup P)
    (hA' : ∀ a ∈ A', ∃ y, Sec4.IsPGLAtP e a y) (a : A')
    (ha : (a : P) ∈ Subgroup.centralizer (Yh : Set P)) :
    psiAct hK hq e A' hA' a = 1 := by
  have h1 : Sec4.pglHomP hK hq A' hA' a = 1 := (Sec4.pglHomP_eq_one_iff a).mpr ha
  rw [psiAct, MonoidHom.comp_apply, h1, map_one]

theorem psiAct_conj [Yh.Normal] (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    [Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K))]
    (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K))
    (hact : ∀ g ∈ Yh ⊔ Bh, ∃ y, Sec4.IsPGLAtP e g y) (g : ↥(Yh ⊔ Bh)) (x : ↥Yh)
    (hgx : (g : P) * (x : P) * (g : P)⁻¹ ∈ Yh) :
    psiAct hK hq e (Yh ⊔ Bh) hact g *
        ((e x : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) *
      (psiAct hK hq e (Yh ⊔ Bh) hact g)⁻¹ =
      ((e ⟨(g : P) * (x : P) * (g : P)⁻¹, hgx⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) := by
  obtain ⟨y', hy'⟩ := hact g.1 g.2
  rw [psiAct_apply hK hq e (Yh ⊔ Bh) hact g hy']
  exact (Hering129KH3.conj_compat e hy' x.2).symm

theorem nonempty_autIn_of_lift {G M : Type} [Group G] [Group M] {Y A : Subgroup G} [Y.Normal]
    {Lh : Subgroup M} (e : ↥Y ≃* ↥Lh) {ψ : ↥A →* M} {R : Subgroup M}
    (hconj : ∀ (g : ↥A) (x : ↥Y) (hgx : (g : G) * (x : G) * (g : G)⁻¹ ∈ Y),
      ψ g * ((e x : ↥Lh) : M) * (ψ g)⁻¹ = ((e ⟨(g : G) * (x : G) * (g : G)⁻¹, hgx⟩ : ↥Lh) : M))
    (hψR : ∀ g : ↥A, ψ g ∈ R) (hsurj : ∀ r ∈ R, ∃ g : ↥A, ψ g = r)
    {F : Subgroup M} [Finite F] (hFL : F ≤ Lh) {Ft : Subgroup G}
    (hFt : ∀ {x : G}, x ∈ Ft ↔ ∃ hx : x ∈ Y, ((e ⟨x, hx⟩ : ↥Lh) : M) ∈ F) :
    Nonempty (Sec4.autIn A Ft ≃* Sec4.autIn R F) := by
  haveI : Finite (F : Set M) := ‹Finite F›
  have hlift : ∀ z ∈ F, ∃ x : ↥Y, ((e x : ↥Lh) : M) = z ∧ (x : G) ∈ Ft := by
    intro z hz
    obtain ⟨x, hx⟩ := e.surjective ⟨z, hFL hz⟩
    have hxz : ((e x : ↥Lh) : M) = z := congrArg Subtype.val hx
    refine ⟨x, hxz, hFt.mpr ⟨x.2, ?_⟩⟩
    rw [← hxz] at hz
    exact hz
  have hi : ∀ g : ↥A, (g : G) ∈ Subgroup.normalizer (Ft : Set G) →
      ψ g ∈ Subgroup.normalizer (F : Set M) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨x, hxz, hxFt⟩ := hlift z hz
    have hgx : (g : G) * (x : G) * (g : G)⁻¹ ∈ Ft :=
      (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp hxFt
    obtain ⟨hgxY, hgxF⟩ := hFt.mp hgx
    have h1 : ψ g * ((e x : ↥Lh) : M) * (ψ g)⁻¹ =
        ((e ⟨(g : G) * (x : G) * (g : G)⁻¹, hgxY⟩ : ↥Lh) : M) := hconj g x hgxY
    rw [← hxz, h1]
    exact hgxF
  have hj : ∀ g : ↥A, ψ g ∈ Subgroup.normalizer (F : Set M) →
      (g : G) ∈ Subgroup.normalizer (Ft : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨hhY, hhF⟩ := hFt.mp hh
      have hgY : (g : G) * h * (g : G)⁻¹ ∈ Y :=
        Subgroup.Normal.conj_mem (inferInstance : Y.Normal) h hhY _
      apply hFt.mpr ⟨hgY, ?_⟩
      have h1 : ψ g * ((e ⟨h, hhY⟩ : ↥Lh) : M) * (ψ g)⁻¹ =
          ((e ⟨(g : G) * h * (g : G)⁻¹, hgY⟩ : ↥Lh) : M) := hconj g ⟨h, hhY⟩ hgY
      rw [← h1]
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp hhF
    · intro hh
      obtain ⟨hgY, hgF⟩ := hFt.mp hh
      have hhY : h ∈ Y := by
        have h2 := Subgroup.Normal.conj_mem (inferInstance : Y.Normal) _ hgY (g : G)⁻¹
        convert h2 using 1
        group
      apply hFt.mpr ⟨hhY, ?_⟩
      have h1 : ψ g * ((e ⟨h, hhY⟩ : ↥Lh) : M) * (ψ g)⁻¹ =
          ((e ⟨(g : G) * h * (g : G)⁻¹, hgY⟩ : ↥Lh) : M) := hconj g ⟨h, hhY⟩ hgY
      rw [← h1] at hgF
      exact (Subgroup.mem_normalizer_iff.mp hg _).mpr hgF
  have hkey : ∀ g : ↥A, ((∀ x ∈ Ft, (g : G) * x * (g : G)⁻¹ = x) ↔
      ∀ z ∈ F, ψ g * z * (ψ g)⁻¹ = z) := by
    intro g
    constructor
    · intro hc z hz
      obtain ⟨x, hxz, hxFt⟩ := hlift z hz
      have hgxY : (g : G) * (x : G) * (g : G)⁻¹ ∈ Y :=
        Subgroup.Normal.conj_mem (inferInstance : Y.Normal) (x : G) x.2 _
      have h1 : (g : G) * (x : G) * (g : G)⁻¹ = (x : G) := hc (x : G) hxFt
      have h2 : ψ g * ((e x : ↥Lh) : M) * (ψ g)⁻¹ =
          ((e ⟨(g : G) * (x : G) * (g : G)⁻¹, hgxY⟩ : ↥Lh) : M) := hconj g x hgxY
      have h3 : (⟨(g : G) * (x : G) * (g : G)⁻¹, hgxY⟩ : ↥Y) = x := Subtype.ext h1
      have h4 : ((e ⟨(g : G) * (x : G) * (g : G)⁻¹, hgxY⟩ : ↥Lh) : M) =
          ((e x : ↥Lh) : M) := by
        rw [h3]
      rw [← hxz, h2, h4]
    · intro hc x hx
      obtain ⟨hxY, hxF⟩ := hFt.mp hx
      have hgxY : (g : G) * x * (g : G)⁻¹ ∈ Y :=
        Subgroup.Normal.conj_mem (inferInstance : Y.Normal) x hxY _
      have h2 : ψ g * ((e ⟨x, hxY⟩ : ↥Lh) : M) * (ψ g)⁻¹ =
          ((e ⟨(g : G) * x * (g : G)⁻¹, hgxY⟩ : ↥Lh) : M) := hconj g ⟨x, hxY⟩ hgxY
      have h4 : ((e ⟨(g : G) * x * (g : G)⁻¹, hgxY⟩ : ↥Lh) : M) =
          ((e ⟨x, hxY⟩ : ↥Lh) : M) := by
        rw [← h2]
        exact hc _ hxF
      have h5 : (e ⟨(g : G) * x * (g : G)⁻¹, hgxY⟩ : ↥Lh) = e ⟨x, hxY⟩ := Subtype.ext h4
      have h6 := e.injective h5
      exact congrArg Subtype.val h6
  have hN1 : A ⊓ Subgroup.normalizer (Ft : Set G) ≤ Subgroup.normalizer (Ft : Set G) :=
    inf_le_right
  have hN2 : R ⊓ Subgroup.normalizer (F : Set M) ≤ Subgroup.normalizer (F : Set M) :=
    inf_le_right
  have hN1A : A ⊓ Subgroup.normalizer (Ft : Set G) ≤ A := inf_le_left
  let f₁ : ↥(A ⊓ Subgroup.normalizer (Ft : Set G)) →* MulAut ↥Ft :=
    Ft.normalizerMonoidHom.comp (Subgroup.inclusion hN1)
  let f₂ : ↥(R ⊓ Subgroup.normalizer (F : Set M)) →* MulAut ↥F :=
    F.normalizerMonoidHom.comp (Subgroup.inclusion hN2)
  let α : ↥(A ⊓ Subgroup.normalizer (Ft : Set G)) →* ↥(R ⊓ Subgroup.normalizer (F : Set M)) :=
    (ψ.comp (Subgroup.inclusion hN1A)).codRestrict _ (fun x => Subgroup.mem_inf.mpr
      ⟨hψR (Subgroup.inclusion hN1A x), hi (Subgroup.inclusion hN1A x)
        (Subgroup.mem_inf.mp x.2).2⟩)
  have hα : Function.Surjective α := by
    rintro ⟨r, hr⟩
    obtain ⟨g, hg⟩ := hsurj r (Subgroup.mem_inf.mp hr).1
    have hgN : (g : G) ∈ Subgroup.normalizer (Ft : Set G) :=
      hj g (by rw [hg]; exact (Subgroup.mem_inf.mp hr).2)
    exact ⟨⟨(g : G), Subgroup.mem_inf.mpr ⟨g.2, hgN⟩⟩, Subtype.ext hg⟩
  have hker : (f₂.comp α).ker = f₁.ker := by
    ext ⟨g, hg⟩
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have hgA : g ∈ A := (Subgroup.mem_inf.mp hg).1
    have hgN : g ∈ Subgroup.normalizer (Ft : Set G) := (Subgroup.mem_inf.mp hg).2
    have e1 : f₁ ⟨g, hg⟩ = 1 ↔ ∀ x ∈ Ft, g * x * g⁻¹ = x :=
      normalizerMonoidHom_eq_one_iff Ft hgN
    have e2 : f₂ (α ⟨g, hg⟩) = 1 ↔ ∀ z ∈ F, ψ ⟨g, hgA⟩ * z * (ψ ⟨g, hgA⟩)⁻¹ = z :=
      normalizerMonoidHom_eq_one_iff F (Subgroup.mem_inf.mp (α ⟨g, hg⟩).2).2
    exact e2.trans ((hkey ⟨g, hgA⟩).symm.trans e1.symm)
  obtain ⟨φ⟩ := Hering129KEa.nonempty_range_mulEquiv f₁ f₂ α hα hker
  exact ⟨(MulEquiv.subgroupCongr (autIn_eq_range_comp A Ft)).trans
    (φ.trans (MulEquiv.subgroupCongr (autIn_eq_range_comp R F)).symm)⟩

theorem nonempty_autIn_liftSub [Yh.Normal] (hD : HessData Yh Bh xh bh ch)
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K))
    (hact : ∀ g ∈ Yh ⊔ Bh, ∃ y, Sec4.IsPGLAtP e g y) {y : GL (Fin 3) K}
    (hy : Sec4.IsPGLAtP e bh y) {F : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hF : PglHess π p f K y
      ((e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) F) :
    Nonempty (Sec4.autIn (Yh ⊔ Bh) (Hering129KH4.liftSub e F) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨hFL, -, hFcard, -, -, -, -, -, -, hAut⟩ := hF
  have hq2 : 2 < p ^ f := by
    have h2le : 2 ≤ p ^ f :=
      le_trans hK.prime.two_le (Nat.le_self_pow (by have := hK.one_le; omega) p)
    by_contra hcon
    have h2 : p ^ f = 2 := by omega
    cases π with
    | true =>
      have hq1 : p ^ f % 3 = 1 := hq
      omega
    | false =>
      haveI : Group.IsSolvable (projImage (Sec4.slPi false 3 (p ^ f) K)) :=
        Sec13.isSolvable_projImage_slPi_two hK h2
      haveI : Group.IsSolvable ↥Yh :=
        Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      exact Hering129KH2.not_isSolvable_of_hessData hD inferInstance
  haveI : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    Sec13.isPerfect_projImage_slPi hK hq2
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hFcard]; norm_num)
  obtain ⟨R, hR⟩ : ∃ R : Subgroup (ProjGenLinGroup (Fin 3) K),
      R = projImage (Sec4.slPi π 3 (p ^ f) K) ⊔ Subgroup.zpowers (ProjGenLinGroup.mk y) :=
    ⟨_, rfl⟩
  rw [← hR] at hAut
  have hLR : projImage (Sec4.slPi π 3 (p ^ f) K) ≤ R := by
    rw [hR]
    exact le_sup_left
  have hzR : Subgroup.zpowers (ProjGenLinGroup.mk y) ≤ R := by
    rw [hR]
    exact le_sup_right
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥(Yh ⊔ Bh) →* ProjGenLinGroup (Fin 3) K,
      ψ = psiAct hK hq e (Yh ⊔ Bh) hact := ⟨_, rfl⟩
  have hxB : xh ∈ Bh := by
    rw [hD.gen]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers xh))
  have hbB : bh ∈ Bh := by
    rw [hD.gen]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers bh))
  have hcB : ch ∈ Bh := by
    rw [hD.gen]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ch)
  have hxA : xh ∈ Yh ⊔ Bh := Subgroup.mem_sup_right hxB
  have hbA : bh ∈ Yh ⊔ Bh := Subgroup.mem_sup_right hbB
  have hcA : ch ∈ Yh ⊔ Bh := Subgroup.mem_sup_left hD.cY
  have hψL : ∀ (l : P) (hl : l ∈ Yh) (hlA : l ∈ Yh ⊔ Bh),
      ψ ⟨l, hlA⟩ = ((e ⟨l, hl⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) := by
    intro l hl hlA
    rw [hψ]
    exact psiAct_of_mem hK hq e (Yh ⊔ Bh) hact hlA hl
  have hψbh : ψ ⟨bh, hbA⟩ = ProjGenLinGroup.mk y := by
    rw [hψ]
    exact psiAct_apply hK hq e (Yh ⊔ Bh) hact ⟨bh, hbA⟩ hy
  have hψxh : ψ ⟨xh, hxA⟩ = 1 := by
    rw [hψ]
    exact psiAct_eq_one hK hq e (Yh ⊔ Bh) hact ⟨xh, hxA⟩
      (Subgroup.mem_centralizer_iff.mpr fun h _ => (hD.xcent h).symm)
  have hψch : ψ ⟨ch, hcA⟩ = ((e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) := hψL ch hD.cY hcA
  have hT : Yh ⊔ Bh ≤ (R.comap ψ).map (Yh ⊔ Bh).subtype := by
    have hmem : ∀ (g : P) (hg : g ∈ Yh ⊔ Bh), ψ ⟨g, hg⟩ ∈ R →
        g ∈ (R.comap ψ).map (Yh ⊔ Bh).subtype := fun g hg h =>
      Subgroup.mem_map.mpr ⟨⟨g, hg⟩, Subgroup.mem_comap.mpr h, rfl⟩
    have hBT : Bh ≤ (R.comap ψ).map (Yh ⊔ Bh).subtype := by
      have hx : Subgroup.zpowers xh ≤ (R.comap ψ).map (Yh ⊔ Bh).subtype :=
        Subgroup.zpowers_le.mpr (hmem xh hxA (by rw [hψxh]; exact R.one_mem))
      have hb : Subgroup.zpowers bh ≤ (R.comap ψ).map (Yh ⊔ Bh).subtype :=
        Subgroup.zpowers_le.mpr
          (hmem bh hbA (by rw [hψbh]; exact hzR (Subgroup.mem_zpowers _)))
      have hc : Subgroup.zpowers ch ≤ (R.comap ψ).map (Yh ⊔ Bh).subtype :=
        Subgroup.zpowers_le.mpr
          (hmem ch hcA (by rw [hψch]; exact hLR (e ⟨ch, hD.cY⟩).2))
      intro β hβ
      have hβ' := hβ
      rw [hD.gen] at hβ'
      exact (sup_le (sup_le hx hb) hc) hβ'
    refine sup_le ?_ hBT
    intro l hl
    exact hmem l (Subgroup.mem_sup_left hl)
      (by rw [hψL l hl (Subgroup.mem_sup_left hl)]; exact hLR (e ⟨l, hl⟩).2)
  have hψR : ∀ g : ↥(Yh ⊔ Bh), ψ g ∈ R := by
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp (hT g.2)
    have hxg' : x = g := Subtype.ext hxg
    rw [← hxg']
    exact Subgroup.mem_comap.mp hx
  have hsurj : ∀ r ∈ R, ∃ g : ↥(Yh ⊔ Bh), ψ g = r := by
    have hle : R ≤ ψ.range := by
      rw [hR]
      refine sup_le ?_ ?_
      · intro m hm
        obtain ⟨x, hx⟩ := e.surjective ⟨m, hm⟩
        refine MonoidHom.mem_range.mpr ⟨⟨x.1, Subgroup.mem_sup_left x.2⟩, ?_⟩
        rw [hψL x.1 x.2 (Subgroup.mem_sup_left x.2)]
        exact congrArg Subtype.val hx
      · rw [Subgroup.zpowers_le]
        exact MonoidHom.mem_range.mpr ⟨⟨bh, hbA⟩, hψbh⟩
    intro r hr
    exact MonoidHom.mem_range.mp (hle hr)
  have hconj : ∀ (g : ↥(Yh ⊔ Bh)) (x : ↥Yh) (hgx : (g : P) * (x : P) * (g : P)⁻¹ ∈ Yh),
      ψ g * ((e x : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) *
        (ψ g)⁻¹ = ((e ⟨(g : P) * (x : P) * (g : P)⁻¹, hgx⟩ :
          projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) := by
    intro g x hgx
    rw [hψ]
    exact psiAct_conj hK hq e hact g x hgx
  obtain ⟨φ⟩ := nonempty_autIn_of_lift (Ft := Hering129KH4.liftSub e F) e hconj hψR hsurj hFL
    (fun {x} => Hering129KH4.mem_liftSub e F)
  obtain ⟨χ⟩ := hAut
  exact ⟨φ.trans χ⟩

end Hering129KH5

end CFSG.RankThree.PartTwo.Sec12
