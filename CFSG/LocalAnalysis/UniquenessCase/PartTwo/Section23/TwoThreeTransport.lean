module

public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

noncomputable def barSubHom {A : Subgroup G} (hA : IsElemAbelian 2 A) (X : Subgroup G)
    (hX : X ≤ stabTil ⊥ A) : ↥X →* ↥(barSub ⊥ A hA X) :=
  ((actTil ⊥ A hA).comp (Subgroup.inclusion hX)).codRestrict (barSub ⊥ A hA X)
    (fun x => actTil_mem_barSub ⊥ A hA x.2 (hX x.2))

theorem barSubHom_apply {A : Subgroup G} (hA : IsElemAbelian 2 A) (X : Subgroup G)
    (hX : X ≤ stabTil ⊥ A) (x : ↥X) :
    ((barSubHom hA X hX x : ↥(barSub ⊥ A hA X)) : MulAut (Vtil ⊥ A hA)) =
      actTil ⊥ A hA ⟨(x : G), hX x.2⟩ := by
  simp only [barSubHom, MonoidHom.codRestrict_apply, MonoidHom.comp_apply]
  rfl

theorem barSubHom_surjective {A : Subgroup G} (hA : IsElemAbelian 2 A) (X : Subgroup G)
    (hX : X ≤ stabTil ⊥ A) : Function.Surjective (barSubHom hA X hX) := by
  intro φ
  obtain ⟨g, hgX, hg⟩ := (mem_barSub ⊥ A hA X (φ : MulAut (Vtil ⊥ A hA))).1 φ.2
  refine ⟨⟨g, hgX⟩, Subtype.ext ?_⟩
  have hgg : (⟨(g : G), hX hgX⟩ : ↥(stabTil ⊥ A)) = g := Subtype.ext rfl
  rw [barSubHom_apply, hgg]
  exact hg

theorem barSubHom_ker {A : Subgroup G} (hA : IsElemAbelian 2 A) (X : Subgroup G)
    (hX : X ≤ stabTil ⊥ A) :
    (barSubHom hA X hX).ker = (X ⊓ Subgroup.centralizer (A : Set G)).subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    have h1 : actTil ⊥ A hA ⟨(x : G), hX x.2⟩ = 1 := by
      simpa [barSubHom_apply hA X hX x] using congrArg Subtype.val h
    have h2 := (actTil_eq_one_iff ⊥ A hA ⟨(x : G), hX x.2⟩).1 h1
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h3 : (x : G) * a * (x : G)⁻¹ * a⁻¹ = 1 := Subgroup.mem_bot.1 (h2 a ha)
    have h4 : (x : G) * a * (x : G)⁻¹ = a := mul_inv_eq_one.1 h3
    calc a * (x : G) = ((x : G) * a * (x : G)⁻¹) * (x : G) := by rw [h4]
      _ = (x : G) * a := by group
  · rintro ⟨hxX, hxc⟩
    apply Subtype.ext
    show actTil ⊥ A hA ⟨(x : G), hX x.2⟩ = 1
    refine (actTil_eq_one_iff ⊥ A hA _).2 fun a ha => ?_
    rw [Subgroup.mem_bot]
    have hcomm : a * (x : G) = (x : G) * a :=
      Subgroup.mem_centralizer_iff.mp hxc a ha
    rw [← hcomm]
    group

theorem barSub_commutator {A X : Subgroup G} (hA : IsElemAbelian 2 A)
    (hX : X ≤ stabTil ⊥ A) (hperf : ⁅X, X⁆ = X) :
    ⁅barSub ⊥ A hA X, barSub ⊥ A hA X⁆ = barSub ⊥ A hA X := by
  let Y := barSub ⊥ A hA X
  let ψ := barSubHom hA X hX
  have hψ : Function.Surjective ψ := barSubHom_surjective hA X hX
  have htop : ((⊤ : Subgroup ↥X).map ψ) = ⊤ := Subgroup.map_top_of_surjective ψ hψ
  have hXperf : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = ⊤ := by
    refine Subgroup.map_injective (Subgroup.subtype_injective X) ?_
    rw [Subgroup.map_commutator]
    simp only [Subgroup.map_top, Subgroup.range_subtype, hperf]
  have htopY : ((⊤ : Subgroup ↥Y).map Y.subtype) = Y := by
    ext x
    simp
  have hYperf : ⁅(⊤ : Subgroup ↥Y), (⊤ : Subgroup ↥Y)⁆ = ⊤ := by
    calc ⁅(⊤ : Subgroup ↥Y), (⊤ : Subgroup ↥Y)⁆
        = ⁅(⊤ : Subgroup ↥X).map ψ, (⊤ : Subgroup ↥X).map ψ⁆ := by rw [htop]
      _ = (⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆).map ψ :=
          (Subgroup.map_commutator _ _ ψ).symm
      _ = ⊤ := by rw [hXperf, htop]
  calc ⁅Y, Y⁆ = ⁅(⊤ : Subgroup ↥Y).map Y.subtype, (⊤ : Subgroup ↥Y).map Y.subtype⁆ := by
        rw [htopY]
    _ = (⁅(⊤ : Subgroup ↥Y), (⊤ : Subgroup ↥Y)⁆).map Y.subtype :=
        (Subgroup.map_commutator _ _ Y.subtype).symm
    _ = Y := by rw [hYperf, htopY]

theorem odd_card_center_bar2 (X : Type) [Group X] [Finite X] (hO2 : CFSG.pCore 2 X = ⊥) :
    Odd (Nat.card (Subgroup.center X)) :=
  CFSG.CGT.Timmesfeld75.odd_card_center fun N hN h2 => by
    have hNle : N ≤ CFSG.pCore 2 X := le_sSup ⟨hN, h2⟩
    exact le_bot_iff.mp (hO2 ▸ hNle)

theorem barSub_pCoreOf_eq_bot_of_isComponentOf {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h208 : S20_8 D) (h1930 : H1930 D) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) {K : Subgroup G} (hK : K ∈ calC c.L) :
    barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥ := by
  have hsub : IsSubnormal c.L c.N := (Ctx23L.N_facts c h208 h1930).2.2.1
  have hpKL : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 c.L :=
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hK.1
  have hpLN : CFSG.Open.pCoreOf 2 c.L ≤ CFSG.Open.pCoreOf 2 c.N :=
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hsub
  have hpK : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 c.N := hpKL.trans hpLN
  have hAC : A ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 c.N : Set G) :=
    hAV.trans (Ctx23L.V_le_centralizer_pCore c)
  refine le_bot_iff.mp fun φ hφ => ?_
  obtain ⟨g, hg, rfl⟩ := (mem_barSub ⊥ A hA _ φ).1 hφ
  refine (actTil_eq_one_iff ⊥ A hA g).2 fun a ha => ?_
  rw [Subgroup.mem_bot]
  have hcomm : (g : G) * a = a * (g : G) :=
    Subgroup.mem_centralizer_iff.mp (hAC ha) (g : G) (hpK hg)
  calc (g : G) * a * (g : G)⁻¹ * a⁻¹ = a * a⁻¹ := by rw [hcomm]; group
    _ = 1 := by group

private theorem barSub_ne_bot_of_not_le_centralizer {A K : Subgroup G}
    (hA : IsElemAbelian 2 A) (hKstab : K ≤ stabTil ⊥ A)
    (hfaith : ¬ K ≤ Subgroup.centralizer (A : Set G)) : barSub ⊥ A hA K ≠ ⊥ := by
  intro hbot
  apply hfaith
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hmem : actTil ⊥ A hA ⟨k, hKstab hk⟩ ∈ barSub ⊥ A hA K :=
    actTil_mem_barSub ⊥ A hA hk (hKstab hk)
  rw [hbot, Subgroup.mem_bot] at hmem
  have h3 : k * a * k⁻¹ * a⁻¹ = 1 :=
    (actTil_eq_one_iff ⊥ A hA ⟨k, hKstab hk⟩).1 hmem a ha
  have h4 : k * a * k⁻¹ = a := mul_inv_eq_one.1 h3
  calc a * k = (k * a * k⁻¹) * k := by rw [h4]
    _ = k * a := by group

theorem isComponentOf_barSub {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h208 : S20_8 D) (h1930 : H1930 D) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAV : A ≤ c.V) (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) {K : Subgroup G}
    (hK : K ∈ calC c.L) (hfaith : ¬ K ≤ Subgroup.centralizer (A : Set G)) :
    IsComponentOf (barSub ⊥ A hA K) (barSub ⊥ A hA c.N) := by
  have hKN : K ≤ c.N := (A3.subnormal_le hK.1).trans (Ctx23L.L_le_N c)
  have hNbot : c.N ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp
  have hKstab : K ≤ stabTil ⊥ A := hKN.trans (le_inf hAN hNbot)
  have hsubK : IsSubnormal K c.N :=
    A3.subnormal_trans hK.1 (Ctx23L.N_facts c h208 h1930).2.2.1
  refine ⟨barSub_mono ⊥ A hA hKN, ?_, ?_⟩
  · exact TwelveTwentyThree.isSubnormal_barSub (V₀ := ⊥) hA hsubK
  · exact TwelveTwentyThree.isQuasisimple_barSub (V₀ := ⊥) hA hKstab hK.2.2
      (barSub_pCoreOf_eq_bot_of_isComponentOf c h208 h1930 hA hAV hK)
      (barSub_ne_bot_of_not_le_centralizer hA hKstab hfaith)

theorem isSylowIn_barSub {A S X : Subgroup G} (hA : IsElemAbelian 2 A)
    (hSX : S ≤ X) (hX : X ≤ stabTil ⊥ A) (hS : IsSylowIn 2 S X) :
    IsSylowIn 2 (barSub ⊥ A hA S) (barSub ⊥ A hA X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y := barSub ⊥ A hA X
  let ψ := barSubHom hA X hX
  have hψ : Function.Surjective ψ := barSubHom_surjective hA X hX
  let P' : Sylow 2 ↥Y := hS.toSylow.mapSurjective (f := ψ) hψ
  have hP' : IsSylowIn 2 ((P' : Subgroup ↥Y).map Y.subtype) Y :=
    isSylowIn_of_card_eq (Subgroup.map_subtype_le _) (by
      rw [Subgroup.card_map_of_injective Y.subtype_injective, Sylow.card_eq_multiplicity P'])
  have hEq : ((P' : Subgroup ↥Y).map Y.subtype) = barSub ⊥ A hA S := by
    rw [show P' = hS.toSylow.mapSurjective (f := ψ) hψ from rfl,
      Sylow.coe_mapSurjective (f := ψ) hψ, Subgroup.map_map]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [CFSG.Quasithin.IsSylowIn.coe_toSylow] at hx
      exact actTil_mem_barSub ⊥ A hA (Subgroup.mem_subgroupOf.mp hx) (hX x.2)
    · intro z hz
      obtain ⟨g, hgS, rfl⟩ := (mem_barSub ⊥ A hA S z).1 hz
      refine ⟨⟨(g : G), hSX hgS⟩, ?_, ?_⟩
      · rw [CFSG.Quasithin.IsSylowIn.coe_toSylow]
        exact Subgroup.mem_subgroupOf.mpr hgS
      · show actTil ⊥ A hA ⟨(g : G), hX (hSX hgS)⟩ = actTil ⊥ A hA g
        exact congrArg (actTil ⊥ A hA) (Subtype.ext rfl)
  rwa [hEq] at hP'

theorem isKGroup_barSub {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hN : c.N ≤ stabTil ⊥ A)
    (hNtop : c.N ≠ ⊤) : CFSG.Open.IsKGroup ↥(barSub ⊥ A hA c.N) := by
  have hK : CFSG.Open.IsKGroup ↥c.N := D.standing.kProper.isKGroup c.N hNtop
  have hsub : CFSG.Open.IsKGroup ↥(c.N.subgroupOf (stabTil ⊥ A)) :=
    hK.of_injective (Subgroup.subgroupOfEquivOfLe hN).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hN).injective
  exact hsub.of_surjective ((actTil ⊥ A hA).subgroupMap (c.N.subgroupOf (stabTil ⊥ A)))
    (MonoidHom.subgroupMap_surjective _ _)

private theorem not_le_centralizer_of_sup_conj {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A K : Subgroup G} (hAne : A ≠ ⊥) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom) :
    ¬ K ≤ Subgroup.centralizer (A : Set G) := by
  intro hKcent
  have hTnormA : D.T ≤ Subgroup.normalizer (A : Set G) :=
    (le_sup_right : D.T ≤ c.L ⊔ D.T).trans ((Ctx23L.sup_le_N D Ch c).trans hAN)
  have hLcent : c.L ≤ Subgroup.centralizer (A : Set G) := by
    rw [hgen]
    refine iSup_le fun t => ?_
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hta : (t : G)⁻¹ * a * (t : G) ∈ A := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hTnormA (D.T.inv_mem t.2)) a).mp ha
      simpa using h1
    have hck := Subgroup.mem_centralizer_iff.mp (hKcent hk) ((t : G)⁻¹ * a * (t : G)) hta
    have hconj := congrArg (fun z : G => (t : G) * z * (t : G)⁻¹) hck
    simpa [mul_assoc] using hconj
  have hAcent : A ≤ Subgroup.centralizer (c.L : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hLcent hl a ha).symm
  exact hAne (le_bot_iff.mp ((le_inf hAV hAcent).trans_eq (Ctx23L.fixed_L_eq_bot c)))

theorem isComponentOf_barSub_of_sup_conj {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h208 : S20_8 D) (h1930 : H1930 D) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAV : A ≤ c.V) (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hAne : A ≠ ⊥)
    {K : Subgroup G} (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom) :
    IsComponentOf (barSub ⊥ A hA K) (barSub ⊥ A hA c.N) :=
  isComponentOf_barSub c h208 h1930 hA hAV hAN hK
    (not_le_centralizer_of_sup_conj c hAne hAV hAN hgen)

theorem lieModel_barSub_of_isSimpleGroup {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hKstab : K ≤ stabTil ⊥ A) (h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥)
    (hK1 : barSub ⊥ A hA K ≠ ⊥) (hsimple : IsSimpleGroup (Bar2 K))
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel (Bar2 K) t n p f) :
    CFSG.Blueprint.LieModel ↥(barSub ⊥ A hA K) t n p f := by
  let q := barSubBar2Hom (V₀ := ⊥) hA hKstab h2
  have hq : Function.Surjective q := barSubBar2Hom_surjective hA hKstab h2
  have hker : q.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top q.ker with hb | ht
    · exact hb
    · exfalso
      apply hK1
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hxq⟩ := hq ⟨y, hy⟩
      have hx : x ∈ q.ker := ht ▸ Subgroup.mem_top x
      rw [MonoidHom.mem_ker] at hx
      have h1 : (⟨y, hy⟩ : ↥(barSub ⊥ A hA K)) = 1 := by rw [← hxq, hx]
      simpa using congrArg Subtype.val h1
  have e : Bar2 K ≃* ↥(barSub ⊥ A hA K) := by
    have e0 := QuotientGroup.quotientKerEquivOfSurjective q hq
    exact ((QuotientGroup.quotientMulEquivOfEq hker).trans QuotientGroup.quotientBot).symm.trans e0
  exact CFSG.Blueprint.LieModel.of_mulEquiv e h

theorem isSL3_barSub {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hKstab : K ≤ stabTil ⊥ A) (h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥)
    (hK1 : barSub ⊥ A hA K ≠ ⊥) {n : ℕ} (h : IsSL3 (Bar2 K) n) :
    IsSL3 ↥(barSub ⊥ A hA K) n := by
  let q := barSubBar2Hom (V₀ := ⊥) hA hKstab h2
  have hq : Function.Surjective q := barSubBar2Hom_surjective hA hKstab h2
  have hnt : ∃ k : Bar2 K, q k ≠ 1 := by
    haveI : Nontrivial ↥(barSub ⊥ A hA K) := (Subgroup.nontrivial_iff_ne_bot _).2 hK1
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥(barSub ⊥ A hA K))
    obtain ⟨k, hk⟩ := hq g
    exact ⟨k, fun h1 => hg (by rw [← hk, h1])⟩
  have hqC : CFSG.IsQuasisimple (Bar2 K) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff (Bar2 K)).2.2.1.mpr h.1
  have hker : q.ker ≤ Subgroup.center (Bar2 K) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hqC hnt
  refine ⟨(CFSG.Foundations.SteinbergCA.quasisimple_iff ↥(barSub ⊥ A hA K)).2.2.1.mp
    (CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hqC (φ := q) hq hnt), ?_⟩
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hqC hq hker) h.2

theorem isSU3_barSub {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hKstab : K ≤ stabTil ⊥ A) (h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥)
    (hK1 : barSub ⊥ A hA K ≠ ⊥) {n : ℕ} (h : IsSU3 (Bar2 K) n) :
    IsSU3 ↥(barSub ⊥ A hA K) n := by
  let q := barSubBar2Hom (V₀ := ⊥) hA hKstab h2
  have hq : Function.Surjective q := barSubBar2Hom_surjective hA hKstab h2
  have hnt : ∃ k : Bar2 K, q k ≠ 1 := by
    haveI : Nontrivial ↥(barSub ⊥ A hA K) := (Subgroup.nontrivial_iff_ne_bot _).2 hK1
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥(barSub ⊥ A hA K))
    obtain ⟨k, hk⟩ := hq g
    exact ⟨k, fun h1 => hg (by rw [← hk, h1])⟩
  have hqC : CFSG.IsQuasisimple (Bar2 K) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff (Bar2 K)).2.2.1.mpr h.1
  have hker : q.ker ≤ Subgroup.center (Bar2 K) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hqC hnt
  refine ⟨(CFSG.Foundations.SteinbergCA.quasisimple_iff ↥(barSub ⊥ A hA K)).2.2.1.mp
    (CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hqC (φ := q) hq hnt), ?_⟩
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hqC hq hker) h.2

end CFSG.LocalAnalysis.UniquenessCase.UC22
