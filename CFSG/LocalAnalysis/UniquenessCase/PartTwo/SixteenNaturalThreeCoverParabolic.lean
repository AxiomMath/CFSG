module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3PermLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ImageOTwoQuotNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Par
public import CFSG.Foundations.MaxOrderThompsonImage

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s168e3_exists_cover_prime_free
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {B : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcomp : IsComponentOf B (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup B)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* B) →
      ¬ p ∣ Nat.card (Subgroup.center Q)) :
    ∃ Y : Subgroup G, Y ∈ calC D.M ∧ Y ≤ D.M ∧
      barSub V₀ V hV Y = B ∧
      ¬ p ∣ Nat.card ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
  classical
  have h125 : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  have hms : D.M ≤ stabTil V₀ V := c.m_le_stabTil
  have hMn : D.M ≤ normalizer (V : Set G) := h125.pairFacts.le_normalizer
  obtain ⟨Y, hYmem, hYbar, ⟨eK⟩⟩ :=
    exists_calC_cover_of_simple_component h125 c.std.h127 c.std.h119 hcomp hsimple
  have hYM : Y ≤ D.M := A3.subnormal_le hYmem.1
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 h125
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M Y
  have hCcomp : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hYmem
  have hCq : CFSG.Open.IsQuasisimple ↥C := A3.isQuasisimple_iff_open.mp hCcomp.1
  obtain ⟨eBar, -⟩ := UC22.uc22p22l_barImage_equiv hYmem
  have hcenterImage : (Subgroup.center (Bar2 Y)).map eBar.toMonoidHom =
      Subgroup.center C := Subgroup.map_center_eq eBar
  have eC : (C ⧸ Subgroup.center C) ≃* B :=
    ((QuotientGroup.congr (Subgroup.center (Bar2 Y)) (Subgroup.center C) eBar
      hcenterImage).symm).trans eK
  have hcenterp : ¬ p ∣ Nat.card (Subgroup.center C) := hcover C hCq ⟨eC⟩
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  let χC : ↥Y →* ↥C :=
    { toFun := fun y =>
        ⟨π ⟨(y : G), hYM y.2⟩,
          Subgroup.mem_map.mpr ⟨⟨(y : G), hYM y.2⟩, y.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        exact map_one π
      map_mul' := by
        intro a b
        apply Subtype.ext
        simpa using map_mul π (⟨(a : G), hYM a.2⟩ : ↥D.M)
          (⟨(b : G), hYM b.2⟩ : ↥D.M) }
  let α : ↥Y →* MulAut (Vtil V₀ V hV) := (ψ.comp C.subtype).comp χC
  have hα_eq : ∀ y : ↥Y,
      α y = actTil V₀ V hV ⟨(y : G), hms (hYM y.2)⟩ := by
    intro y
    change ψ (π ⟨(y : G), hYM y.2⟩) = _
    exact hψ ⟨(y : G), hYM y.2⟩
  have hχCker2 : IsPGroup 2 ↥χC.ker := by
    have h := (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).comap_of_injective
      (Subgroup.inclusion hYM) (Subgroup.inclusion_injective hYM)
    have hker_eq : χC.ker = (CFSG.pCore 2 ↥D.M).comap (Subgroup.inclusion hYM) := by
      ext y
      rw [MonoidHom.mem_ker]
      constructor
      · intro hy
        have hy' : π ⟨(y : G), hYM y.2⟩ = 1 := Subtype.ext_iff.mp hy
        exact (QuotientGroup.eq_one_iff (⟨(y : G), hYM y.2⟩ : ↥D.M)).mp hy'
      · intro hy
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff (⟨(y : G), hYM y.2⟩ : ↥D.M)).mpr hy
    rw [hker_eq]
    exact h
  let N : Subgroup ↥Y := α.ker
  have hN_eq : N = (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y := by
    ext y
    rw [show N = α.ker from rfl, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hy
      have hact : actTil V₀ V hV ⟨(y : G), hms (hYM y.2)⟩ = 1 := by
        rw [← hα_eq y]
        exact hy
      exact ⟨y.2, (mem_cTilde_iff hV hMn).2
        ⟨hYM y.2, ⟨hms (hYM y.2), hact⟩⟩⟩
    · rintro ⟨-, hyCT⟩
      obtain ⟨-, hgs, hact⟩ := (mem_cTilde_iff hV hMn).1 hyCT
      rw [hα_eq y]
      exact hact
  have hNcard : Nat.card ↥N = Nat.card ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
    rw [hN_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  let η : ↥N →* ↥(Subgroup.center C) :=
    { toFun := fun n =>
        ⟨χC (n : ↥Y), by
          have hn : α (n : ↥Y) = 1 := n.2
          have hmem : χC (n : ↥Y) ∈ (ψ.comp C.subtype).ker := by
            rw [MonoidHom.mem_ker]
            exact hn
          have hkerC : (ψ.comp C.subtype).ker = Subgroup.center C :=
            ker_comp_subtype_eq_center_of_mem_calC h125 hYmem hYbar hsimple ψ hψ
          rwa [hkerC] at hmem⟩
      map_one' := by
        apply Subtype.ext
        exact map_one χC
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul χC (a : ↥Y) (b : ↥Y) }
  have hηker2 : IsPGroup 2 ↥η.ker := by
    have hle : η.ker ≤ χC.ker.subgroupOf N := by
      intro n hn
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact congrArg Subtype.val hn
    exact (hχCker2.comap_subtype).to_le hle
  have hηkerp : ¬ p ∣ Nat.card ↥η.ker := by
    obtain ⟨k, hk⟩ := hηker2.exists_card_eq
    intro hker
    rw [hk] at hker
    have hpdvd2 : p ∣ 2 := hp.dvd_of_dvd_pow hker
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdvd2)
  have hηrangep : ¬ p ∣ Nat.card ↥η.range := by
    have hdvd : Nat.card ↥η.range ∣ Nat.card ↥(Subgroup.center C) := by
      simpa using Subgroup.card_dvd_of_le (le_top : η.range ≤ ⊤)
    intro hrange
    exact hcenterp (hrange.trans hdvd)
  have hNp : ¬ p ∣ Nat.card ↥N := by
    have hcard := Subgroup.card_ker_mul_card_range η
    intro hN
    have hprod : p ∣ Nat.card ↥η.ker * Nat.card ↥η.range := by
      rw [hcard]
      exact hN
    rcases (hp.dvd_mul).1 hprod with h | h
    · exact hηkerp h
    · exact hηrangep h
  refine ⟨Y, hYmem, hYM, hYbar, ?_⟩
  rw [← hNcard]
  exact hNp

theorem s168e3_exists_normal_cover_prime_free
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {B : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcomp : IsComponentOf B (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup B)
    (hnorm : Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      (B : Set (MulAut (Vtil V₀ V hV))))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* B) →
      ¬ p ∣ Nat.card (Subgroup.center Q)) :
    ∃ Y : Subgroup G, Y ∈ calC D.M ∧ Y ≤ D.M ∧
      (Y.subgroupOf D.M).Normal ∧
      barSub V₀ V hV Y = B ∧
      ¬ p ∣ Nat.card ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
  classical
  have h125 : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  have hms : D.M ≤ stabTil V₀ V := c.m_le_stabTil
  obtain ⟨Y, hYmem, hYM, hYbar, hNp⟩ :=
    s168e3_exists_cover_prime_free c hcomp hsimple hp hp2 hcover
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 h125
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M Y
  have hYnorm : (Y.subgroupOf D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYM]
    intro m hm
    have hmA : ψ (QuotientGroup.mk ⟨m, hm⟩) ∈ Mbar D.M V₀ V hV := by
      rw [hψ ⟨m, hm⟩]
      exact actTil_mem_barSub V₀ V hV hm (hms hm)
    have hmNormB : ψ (QuotientGroup.mk ⟨m, hm⟩) ∈
        Subgroup.normalizer (B : Set (MulAut (Vtil V₀ V hV))) :=
      hnorm hmA
    have hmNormC : (QuotientGroup.mk ⟨m, hm⟩ : Bar2 D.M) ∈
        Subgroup.normalizer (C : Set (Bar2 D.M)) :=
      mem_normalizer_barImage_of_map_mem_normalizer h125 hYmem hYbar hsimple ψ hψ hmNormB
    exact S17.mem_normalizer_of_mem_normalizer_imageOTwoQuot hYmem hm (by
      simpa [C, S17.K1Nine, CFSG.Quasithin.imageOTwoQuot, UC22.barImage] using hmNormC)
  exact ⟨Y, hYmem, hYM, hYnorm, hYbar, hNp⟩

theorem s168e3_exists_normal_cover_three_free
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hnorm : Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q)) :
    ∃ Y : Subgroup G, Y ∈ calC D.M ∧ Y ≤ D.M ∧
      (Y.subgroupOf D.M).Normal ∧
      barSub V₀ V hV Y = lBar V₀ V hV L ∧
      ¬ 3 ∣ Nat.card ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
  exact s168e3_exists_normal_cover_prime_free (B := lBar V₀ V hV L) (p := 3)
    c hcomp hsimple hnorm Nat.prime_three (by norm_num) hcover

theorem s168e3_exists_permuting_of_normal_subgroup_three_free
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {C : Subgroup G} (hCM : C ≤ D.M)
    (hCnorm : (C.subgroupOf D.M).Normal)
    (hC3 : ¬ 3 ∣ Nat.card ↥(C ⊓ F11.CTilde D.M V₀ V))
    {J : Subgroup (MulAut (Vtil V₀ V hV))}
    (hTJ : barSub V₀ V hV D.T ≤ J)
    (hJL : J ≤ barSub V₀ V hV C ⊔ barSub V₀ V hV D.T)
    {a : ℕ}
    (hJcard : Nat.card ↥J = 3 ^ a * Nat.card ↥(barSub V₀ V hV D.T))
    (ha : 2 ≤ a)
    (hJexp : ∀ x ∈ J, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧
      Nat.card ↥Y = 3 ^ a ∧ (∀ y ∈ Y, y ^ 3 = 1) ∧
      ¬ IsCyclic ↥Y ∧ Permutes Y D.T := by
  classical
  have hFact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h125 : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  have hms : D.M ≤ stabTil V₀ V := c.m_le_stabTil
  have hMn : D.M ≤ normalizer (V : Set G) := h125.pairFacts.le_normalizer
  let S : Subgroup G := C ⊔ D.T
  have hCS : C ≤ S := le_sup_left
  have hDTS : D.T ≤ S := le_sup_right
  have hSM : S ≤ D.M := sup_le hCM D.sylowM.le
  let N : Subgroup ↥S := C.subgroupOf S
  have hNnorm : N.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCS]
    exact hSM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hCM).1 hCnorm)
  have hNnormI : N.Normal := hNnorm
  let T' : Subgroup ↥S := D.T.subgroupOf S
  have hT'2 : IsPGroup 2 ↥T' := D.sylowM.isPGroup.comap_subtype
  have hT'syl : ¬ 2 ∣ T'.index := by
    have hodd : ¬ 2 ∣ D.T.index := by
      have h2 := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowG).2.2
      rwa [Subgroup.relIndex_top_right] at h2
    have hdvd : D.T.relIndex S ∣ D.T.index := Subgroup.relIndex_dvd_index_of_le hDTS
    intro hdiv
    exact hodd (hdiv.trans hdvd)
  let φ : ↥S →* MulAut (Vtil V₀ V hV) :=
    (barHom V₀ V hV hms).comp (Subgroup.inclusion hSM)
  have hNsupT : N ⊔ T' = ⊤ := by
    rw [show N = C.subgroupOf S from rfl, show T' = D.T.subgroupOf S from rfl,
      ← Subgroup.subgroupOf_sup hCS hDTS]
    exact Subgroup.subgroupOf_self S
  have hquot2 : IsPGroup 2 (↥S ⧸ N) := by
    let q := QuotientGroup.mk' N
    have hNmap : N.map q = ⊥ := by
      have h := Subgroup.map_ker_self (f := q)
      rw [QuotientGroup.ker_mk'] at h
      exact h
    have hmap : T'.map q = ⊤ := by
      calc
        T'.map q = (⊥ : Subgroup (↥S ⧸ N)) ⊔ T'.map q := by rw [bot_sup_eq]
        _ = N.map q ⊔ T'.map q := by rw [hNmap]
        _ = (N ⊔ T').map q := (Subgroup.map_sup N T' q).symm
        _ = ⊤ := by
          rw [hNsupT, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    have htop : IsPGroup 2 ↥(T'.map q) := hT'2.map q
    rw [hmap] at htop
    exact htop.of_equiv Subgroup.topEquiv
  have hR_eq : φ.ker = (F11.CTilde D.M V₀ V).subgroupOf S := by
    show ((barHom V₀ V hV hms).comp (Subgroup.inclusion hSM)).ker = _
    rw [← MonoidHom.comap_ker, ker_barHom V₀ V hV hMn hms,
      Subgroup.comap_inclusion_subgroupOf hSM]
  let R : Subgroup ↥S := φ.ker
  have hRN : R ⊓ N = (C ⊓ F11.CTilde D.M V₀ V).subgroupOf S := by
    rw [show R = φ.ker from rfl, hR_eq]
    rw [show N = C.subgroupOf S from rfl,
      show (F11.CTilde D.M V₀ V).subgroupOf S =
        (F11.CTilde D.M V₀ V).comap S.subtype from rfl,
      show C.subgroupOf S = C.comap S.subtype from rfl,
      ← Subgroup.comap_inf, inf_comm]
    rfl
  have hRNcard : Nat.card ↥(R ⊓ N) =
      Nat.card ↥(C ⊓ F11.CTilde D.M V₀ V) := by
    rw [hRN]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hCS)).toEquiv
  have hkerq_card : Nat.card ↥((QuotientGroup.mk' N).comp R.subtype).ker =
      Nat.card ↥(R ⊓ N) := by
    have hker_eq : ((QuotientGroup.mk' N).comp R.subtype).ker =
        (R ⊓ N).subgroupOf R := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      change N.subgroupOf R = (R ⊓ N).subgroupOf R
      rw [← Subgroup.inf_subgroupOf_left (H := N) (K := R), inf_comm]
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hkerq3 : ¬ 3 ∣ Nat.card ↥((QuotientGroup.mk' N).comp R.subtype).ker := by
    rw [hkerq_card, hRNcard]
    exact hC3
  have hrange2 : IsPGroup 2 ↥((QuotientGroup.mk' N).comp R.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hquot2.to_subgroup (R.map (QuotientGroup.mk' N))
  have hker3 : ¬ 3 ∣ Nat.card ↥φ.ker := by
    have hcard := Subgroup.card_ker_mul_card_range
      ((QuotientGroup.mk' N).comp R.subtype)
    have hrange3 : ¬ 3 ∣ Nat.card ↥((QuotientGroup.mk' N).comp R.subtype).range := by
      obtain ⟨k, hk⟩ := hrange2.exists_card_eq
      intro h3
      rw [hk] at h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    intro h3R
    have h3prod : 3 ∣
        Nat.card ↥((QuotientGroup.mk' N).comp R.subtype).ker *
          Nat.card ↥((QuotientGroup.mk' N).comp R.subtype).range := by
      rw [hcard]
      exact h3R
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3prod with h | h
    · exact hkerq3 h
    · exact hrange3 h
  have hT'map : T'.map φ = barSub V₀ V hV D.T := by
    show (D.T.subgroupOf S).map
      ((barHom V₀ V hV hms).comp (Subgroup.inclusion hSM)) = barSub V₀ V hV D.T
    have hmap1 : (D.T.subgroupOf S).map (Subgroup.inclusion hSM) =
        D.T.subgroupOf D.M := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨(x : G), hDTS (Subgroup.mem_subgroupOf.mp hx)⟩, hx, Subtype.ext rfl⟩
    have hmap2 : (D.T.subgroupOf D.M).map (Subgroup.inclusion hms) =
        D.T.subgroupOf (stabTil V₀ V) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨(x : G), D.sylowM.le (Subgroup.mem_subgroupOf.mp hx)⟩, hx,
          Subtype.ext rfl⟩
    rw [← Subgroup.map_map, hmap1]
    rw [barHom, ← Subgroup.map_map, hmap2]
    rfl
  have hφrange : φ.range = barSub V₀ V hV C ⊔ barSub V₀ V hV D.T := by
    have hφeq : φ = (actTil V₀ V hV).comp
        (Subgroup.inclusion (hSM.trans hms)) := by
      ext x
      rfl
    rw [hφeq, MonoidHom.range_comp, Subgroup.inclusion_range]
    change (S.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV) = _
    rw [show S = C ⊔ D.T from rfl]
    rw [Subgroup.subgroupOf_sup (hCM.trans hms) (D.sylowM.le.trans hms),
      Subgroup.map_sup]
    rfl
  have hJrange : J ≤ φ.range := by
    rw [hφrange]
    exact hJL
  have hTJ' : T'.map φ ≤ J := by
    rw [hT'map]
    exact hTJ
  have hTbar2 : IsPGroup 2 ↥(barSub V₀ V hV D.T) := by
    rw [← hT'map]
    exact hT'2.map φ
  obtain ⟨x, hx⟩ := IsPGroup.iff_card.mp hTbar2
  have hJcard' : Nat.card ↥J = 2 ^ x * 3 ^ a := by
    rw [hJcard, hx, mul_comm]
  obtain ⟨Y', hY'3, hY'card, hY'perm, hY'mapJ⟩ :=
    s16h_exists_permuting_three_of_ker φ hT'2 hT'syl hJrange hTJ' hJcard' hker3
  have hcop : Nat.Coprime 3 (Nat.card ↥φ.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hker3
  have hinj : Function.Injective (φ.comp Y'.subtype) :=
    CFSG.injective_comp_subtype_of_coprime_card_ker φ hcop hY'3
  have hY'exp : ∀ z ∈ Y', z ^ 3 = 1 := by
    intro z hz
    have hzJ : φ z ∈ J := Subgroup.mem_comap.mp (hY'mapJ hz)
    obtain ⟨n, hn⟩ := hY'3 ⟨z, hz⟩
    have hzn : (z : ↥S) ^ 3 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    have hφpow : (φ z) ^ 3 ^ n = 1 := by
      rw [← map_pow, hzn, map_one]
    have hφ3 : (φ z) ^ 3 = 1 := hJexp (φ z) hzJ n hφpow
    have hz3 : (⟨z, hz⟩ : ↥Y') ^ 3 = 1 := by
      apply hinj
      rw [map_pow]
      change φ (z : ↥S) ^ 3 = φ (1 : ↥S)
      rw [hφ3, map_one]
    simpa using congrArg Subtype.val hz3
  let Y : Subgroup G := Y'.map S.subtype
  have hYM : Y ≤ D.M := (Subgroup.map_subtype_le Y').trans hSM
  have hY3 : IsPGroup 3 ↥Y := hY'3.map S.subtype
  have hYcard : Nat.card ↥Y = 3 ^ a := by
    rw [show Y = Y'.map S.subtype from rfl,
      Subgroup.card_map_of_injective S.subtype_injective, hY'card]
  have hYexp : ∀ y ∈ Y, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [← map_pow, hY'exp z hz, map_one]
  have hYnc : ¬ IsCyclic ↥Y := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Y)
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      show (g : G) ^ 3 = 1
      exact hYexp (g : G) g.2
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hg3
    have hdvd' : 3 ^ a ∣ 3 := by
      rw [hg, hYcard] at hdvd
      exact hdvd
    have hle : 3 ^ a ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd'
    have h9 : 9 ≤ 3 ^ a := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  have hperm : Permutes Y D.T := by
    show (Y : Set G) * (D.T : Set G) = (D.T : Set G) * (Y : Set G)
    have hYcoe : (Y : Set G) = S.subtype '' (Y' : Set ↥S) := by
      change (Y'.map S.subtype : Set G) = S.subtype '' (Y' : Set ↥S)
      rw [Subgroup.coe_map]
    have hTmapS : T'.map S.subtype = D.T := Subgroup.map_subgroupOf_eq_of_le hDTS
    have hTcoe : (D.T : Set G) = S.subtype '' (T' : Set ↥S) := by
      rw [← hTmapS, Subgroup.coe_map]
    rw [hYcoe, hTcoe, ← Set.image_mul, ← Set.image_mul, hY'perm]
  exact ⟨Y, hYM, hY3, hYcard, hYexp, hYnc, hperm⟩

theorem s168e3_exists_permuting_of_parabolic_three_free
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q))
    {a : ℕ}
    (hP : T3Parab (lBar V₀ V hV L) (barSub V₀ V hV D.T) a)
    (ha : 2 ≤ a) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧
      Nat.card ↥Y = 3 ^ a ∧ (∀ y ∈ Y, y ^ 3 = 1) ∧
      ¬ IsCyclic ↥Y ∧ Permutes Y D.T := by
  classical
  obtain ⟨Yc, hYcmem, hYcM, hYcnorm, hYcbar, hYc3⟩ :=
    s168e3_exists_normal_cover_three_free c hcomp hsimple hT.normal hcover
  obtain ⟨J, hTJ, hJL, hJcard, hJexp⟩ := hP
  have hJL' : J ≤ barSub V₀ V hV Yc ⊔ barSub V₀ V hV D.T := by
    rw [← hYcbar] at hJL
    exact hJL
  exact s168e3_exists_permuting_of_normal_subgroup_three_free c hYcM hYcnorm hYc3
    hTJ hJL' hJcard ha hJexp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
