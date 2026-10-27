module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7
import CFSG.Adapters.LieModelSmallOrders
import CFSG.Adapters.LieModelSimple
import CFSG.GroupTheory.ConjTransport
import CFSG.GH74.Uniqueness.SU.KI1r4L82
import CFSG.RankThree.PartOne.AUTSL.Interface
import CFSG.RankThree.PartTwo.Sec4.Ronan148LCubeLift
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open scoped Pointwise
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover (projRad)

private theorem exists_e16_of_projectiveSL {K : Type} [Field K] [Finite K] {T : Type} [Group T]
    (e : T ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K)
    (hcard : Nat.card K = 4) :
    ∃ E : Subgroup T, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  have hR : CFSG.IsElementaryAbelian 2 (projRad K 0) := by
    refine CFSG.IsElementaryAbelian.of_forall (fun a ha b hb => ?_) (fun a ha => ?_)
    · exact CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.commute_of_mem_projRad 0 ha hb
    · simpa [pow_two] using
        CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.sq_eq_one_of_mem_projRad hcard 0 ha
  refine ⟨(projRad K 0).map e.symm.toMonoidHom, ?_, ?_⟩
  · exact hR.map e.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.symm.injective,
      CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.card_projRad (k := K) 0, hcard]

private theorem exists_e16_of_isL3 {T : Type} [Group T] (h : IsL3 T 2) :
    ∃ E : Subgroup T, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨K, hF, hFin, hcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel h
  exact @exists_e16_of_projectiveSL K hF hFin T _ e (by rw [hcard]; norm_num)

private theorem not_isSolvable_of_isL3 {T : Type} [Group T] (h : IsL3 T 2) :
    ¬ Group.IsSolvable T := by
  intro hsol
  have hsimple : IsSimpleGroup T := LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  have hcomm : ∀ a b : T, a * b = b * a :=
    (@IsSimpleGroup.comm_iff_isSolvable T _ hsimple).2 hsol
  obtain ⟨E, hE, hEcard⟩ := exists_e16_of_isL3 h
  have hEn : E.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hgx : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcomm g x]
        _ = x := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rwa [hgx]
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal T _ hsimple E hEn with hbot | htop
  · rw [hbot, Subgroup.card_bot] at hEcard
    omega
  · rw [htop, Subgroup.card_top] at hEcard
    have hcardT : Nat.card T = 20160 := LieModel.card_psl_three_four h
    omega

private theorem card_dvd_of_section {Q : Type} [Group Q] {X Y : Subgroup Q} (hYX : Y ≤ X)
    {N : Subgroup ↥Y} [N.Normal] (hL3 : IsL3 (↥Y ⧸ N) 2) : 20160 ∣ Nat.card X := by
  have hcard : Nat.card (↥Y ⧸ N) = 20160 := LieModel.card_psl_three_four hL3
  calc 20160 = Nat.card (↥Y ⧸ N) := hcard.symm
    _ ∣ Nat.card ↥Y := Subgroup.card_quotient_dvd_card N
    _ ∣ Nat.card X := Subgroup.card_dvd_of_le hYX

private theorem map_section {Q G : Type} [Group Q] [Group G] {f : Q →* G}
    (hf : Function.Injective f) {Y : Subgroup Q} {N : Subgroup ↥Y} [hN : N.Normal]
    (hL3 : IsL3 (↥Y ⧸ N) 2) {X : Subgroup Q} (hYX : Y ≤ X) :
    HasL34Section (X.map f) := by
  let e : ↥Y ≃* ↥(Y.map f) := Subgroup.equivMapOfInjective Y f hf
  let K : Subgroup ↥(Y.map f) := N.map e.toMonoidHom
  have hK : K.Normal := hN.map e.toMonoidHom e.surjective
  refine ⟨Y.map f, Subgroup.map_mono hYX, K, hK, ?_⟩
  exact LieModel.of_mulEquiv
    (@QuotientGroup.congr (↥Y) (↥(Y.map f)) _ _ N K hN hK e rfl) hL3

private theorem comap_section {Q G : Type} [Group Q] [Group G] {f : Q →* G} {X : Subgroup G}
    {Y : Subgroup G} (hYX : Y ≤ X) {N : Subgroup ↥Y} [hN : N.Normal]
    (hL3 : IsL3 (↥Y ⧸ N) 2) (hX : X ≤ f.range) : HasL34Section (X.comap f) := by
  let Z : Subgroup Q := Y.comap f
  let fZ : ↥Z →* ↥Y := f.subgroupComap Y
  have hfZ : Function.Surjective fZ := by
    intro y
    obtain ⟨q, hq⟩ := hX (hYX y.2)
    refine ⟨⟨q, ?_⟩, ?_⟩
    · show f q ∈ Y
      rw [hq]
      exact y.2
    · ext
      exact hq
  let g : ↥Z →* ↥Y ⧸ N := (QuotientGroup.mk' N).comp fZ
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective N).comp hfZ
  refine ⟨Z, Subgroup.comap_mono hYX, g.ker, inferInstance, ?_⟩
  exact LieModel.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective g hg).symm hL3

private theorem not_solvable_of_section_map_bot {G : Type} [Group G] {N : Subgroup G} [N.Normal]
    {Y : Subgroup G} {M : Subgroup ↥Y} [M.Normal] (hL3 : IsL3 (↥Y ⧸ M) 2)
    (hsol : Group.IsSolvable (G ⧸ N))
    (hbot : (N.comap Y.subtype).map (QuotientGroup.mk' M) = ⊥) : False := by
  let H0 : Subgroup ↥Y := N.comap Y.subtype
  let ψ : ↥Y →* (↥Y ⧸ M) := QuotientGroup.mk' M
  have hH0n : H0.Normal := Subgroup.normal_subgroupOf
  have hH0leM : H0 ≤ M := by
    have hle := (Subgroup.map_eq_bot_iff H0 (f := ψ)).mp hbot
    simpa [ψ] using hle
  let φ : ↥Y →* (G ⧸ N) := (QuotientGroup.mk' N).comp Y.subtype
  have hH0eq : H0 = φ.ker := by
    ext x
    simp [H0, φ, Subgroup.mem_subgroupOf]
  have hYsol : Group.IsSolvable (↥Y ⧸ H0) := by
    have he : (↥Y ⧸ H0) ≃* ↥φ.range :=
      (@QuotientGroup.quotientMulEquivOfEq (↥Y) _ H0 φ.ker hH0n (MonoidHom.normal_ker φ)
        hH0eq).trans (QuotientGroup.quotientKerEquivRange φ)
    exact Group.isSolvable_of_surjective (f := he.symm.toMonoidHom) he.symm.surjective
  have hH0leMker : H0 ≤ ψ.ker := by simpa [ψ] using hH0leM
  have hQsol : Group.IsSolvable (↥Y ⧸ M) :=
    Group.isSolvable_of_surjective
      (f := @QuotientGroup.lift (↥Y) (↥Y ⧸ M) _ _ H0 hH0n ψ hH0leMker)
      (@QuotientGroup.lift_surjective_of_surjective (↥Y) (↥Y ⧸ M) _ _ H0 hH0n ψ
        (QuotientGroup.mk'_surjective M) hH0leMker)
  exact not_isSolvable_of_isL3 hL3 hQsol

theorem HasL34Section.card_dvd {Q : Type} [Group Q] {X : Subgroup Q} (h : HasL34Section X) :
    20160 ∣ Nat.card X := by
  obtain ⟨Y, hYX, N, hN, hL3⟩ := h
  exact @card_dvd_of_section Q _ X Y hYX N hN hL3

theorem HasL34Section.mono {Q : Type} [Group Q] {X Z : Subgroup Q} (hXZ : X ≤ Z)
    (h : HasL34Section X) : HasL34Section Z := by
  obtain ⟨Y, hYX, N, hN, hL3⟩ := h
  exact ⟨Y, hYX.trans hXZ, N, hN, hL3⟩

theorem HasL34Section.map {Q G : Type} [Group Q] [Group G] {f : Q →* G}
    (hf : Function.Injective f) {X : Subgroup Q} (h : HasL34Section X) :
    HasL34Section (X.map f) := by
  obtain ⟨Y, hYX, N, hN, hL3⟩ := h
  exact @map_section Q G _ _ f hf Y N hN hL3 X hYX

theorem HasL34Section.comap {Q G : Type} [Group Q] [Group G] {f : Q →* G} {X : Subgroup G}
    (hX : X ≤ f.range) (h : HasL34Section X) : HasL34Section (X.comap f) := by
  obtain ⟨Y, hYX, N, hN, hL3⟩ := h
  exact @comap_section Q G _ _ f X Y hYX N hN hL3 hX

private theorem hasL34Section_of_section_map_top {G : Type} [Group G] {N : Subgroup G} [N.Normal]
    {Y : Subgroup G} {M : Subgroup ↥Y} [M.Normal] (hL3 : IsL3 (↥Y ⧸ M) 2)
    (htop : (N.comap Y.subtype).map (QuotientGroup.mk' M) = ⊤) : HasL34Section N := by
  let H0 : Subgroup ↥Y := N.comap Y.subtype
  let ψ : ↥Y →* (↥Y ⧸ M) := QuotientGroup.mk' M
  have hH0leN : H0.map Y.subtype ≤ N := by
    simp [H0]
  have hQsec : HasL34Section (⊤ : Subgroup (↥Y ⧸ M)) := by
    refine ⟨⊤, le_top, ⊥, inferInstance, ?_⟩
    exact LieModel.of_mulEquiv
      ((QuotientGroup.quotientBot (G := ↥(⊤ : Subgroup (↥Y ⧸ M)))).trans
        Subgroup.topEquiv).symm hL3
  have hsurj : Function.Surjective (ψ.comp H0.subtype) := by
    intro x
    have hx : x ∈ H0.map ψ := by rw [htop]; exact Subgroup.mem_top x
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨⟨y, hy⟩, hxy⟩
  have hsecH0 : HasL34Section (⊤ : Subgroup ↥H0) := by
    have hc := HasL34Section.comap (f := ψ.comp H0.subtype)
      (X := (⊤ : Subgroup (↥Y ⧸ M)))
      (by rw [MonoidHom.range_eq_top_of_surjective _ hsurj]) hQsec
    simpa [Subgroup.comap_top] using hc
  have hsecG : HasL34Section (H0.map Y.subtype) := by
    have hinj : Function.Injective (Y.subtype.comp H0.subtype) :=
      (Subgroup.subtype_injective Y).comp (Subgroup.subtype_injective H0)
    have hc := HasL34Section.map (f := Y.subtype.comp H0.subtype) hinj hsecH0
    have hmap : (⊤ : Subgroup ↥H0).map (Y.subtype.comp H0.subtype) = H0.map Y.subtype := by
      rw [← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
    rwa [hmap] at hc
  exact HasL34Section.mono hH0leN hsecG

private theorem of_solvable_quotient_aux {G : Type} [Group G] {N : Subgroup G} [N.Normal]
    {Y : Subgroup G} {M : Subgroup ↥Y} [M.Normal] (hsol : Group.IsSolvable (G ⧸ N))
    (hL3 : IsL3 (↥Y ⧸ M) 2) : HasL34Section N := by
  let ψ : ↥Y →* (↥Y ⧸ M) := QuotientGroup.mk' M
  let H0 : Subgroup ↥Y := N.comap Y.subtype
  have hH0n : H0.Normal := Subgroup.normal_subgroupOf
  have hsimple : IsSimpleGroup (↥Y ⧸ M) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3
  have hmapn : (H0.map ψ).Normal := hH0n.map ψ (QuotientGroup.mk'_surjective M)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (↥Y ⧸ M) _ hsimple (H0.map ψ) hmapn with
    hbot | htop
  · exact False.elim (not_solvable_of_section_map_bot hL3 hsol hbot)
  · exact hasL34Section_of_section_map_top hL3 htop

theorem HasL34Section.of_solvable_quotient {G : Type} [Group G] {N : Subgroup G} [N.Normal]
    (hsol : Group.IsSolvable (G ⧸ N)) (h : HasL34Section (⊤ : Subgroup G)) :
    HasL34Section N := by
  obtain ⟨Y, -, M, hM, hL3⟩ := h
  exact @of_solvable_quotient_aux G _ N _ Y M hM hsol hL3

open CFSG.ComponentClassification.OuterAutomorphisms (Outer) in
theorem not_hasL34Section_mulAut_of_isSolvable_outer {X : Type} [Group X]
    (hsol : Group.IsSolvable (Outer X)) (h : ¬ HasL34Section (⊤ : Subgroup X)) :
    ¬ HasL34Section (⊤ : Subgroup (MulAut X)) := by
  intro hA
  have hInner : HasL34Section
      (CFSG.ComponentClassification.OuterAutomorphisms.inner X) :=
    HasL34Section.of_solvable_quotient
      (N := CFSG.ComponentClassification.OuterAutomorphisms.inner X) hsol hA
  have hpre : HasL34Section
      ((CFSG.ComponentClassification.OuterAutomorphisms.inner X).comap
        (MulAut.conj : X →* MulAut X)) :=
    HasL34Section.comap (f := MulAut.conj) le_rfl hInner
  have htop : (CFSG.ComponentClassification.OuterAutomorphisms.inner X).comap
      (MulAut.conj : X →* MulAut X) = ⊤ := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner,
      MonoidHom.comap_range_self]
  rw [htop] at hpre
  exact h hpre

private theorem not_hasL34Section_aux {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (h : ∀ R : Subgroup G, R ≤ S → Nat.card (↥R ⧸ frattini ↥R) ≤ 8)
    {Y : Subgroup G} {M : Subgroup ↥Y} [M.Normal] (hL3 : IsL3 (↥Y ⧸ M) 2) : False := by
  let ψ : ↥Y →* (↥Y ⧸ M) := QuotientGroup.mk' M
  obtain ⟨E, hE, hEcard⟩ := exists_e16_of_isL3 hL3
  have hEpg : IsPGroup 2 E := @CFSG.IsElementaryAbelian.isPGroup 2 ↥E _ hE
  obtain ⟨P, hPpg, hPmap⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148L.exists_isPGroup_map_eq_of_surjective
      (p := 2) (f := ψ) (E := E) (QuotientGroup.mk'_surjective M) hEpg
  let θP : ↥P →* ↥E :=
    (MulEquiv.subgroupCongr hPmap).toMonoidHom.comp (ψ.subgroupMap P)
  have hθP : Function.Surjective θP :=
    (MulEquiv.subgroupCongr hPmap).surjective.comp (MonoidHom.subgroupMap_surjective ψ P)
  let PG : Subgroup G := P.map Y.subtype
  let θPG : ↥PG →* ↥E :=
    θP.comp (Subgroup.equivMapOfInjective P Y.subtype Y.subtype_injective).symm.toMonoidHom
  have hθPG : Function.Surjective θPG :=
    hθP.comp (Subgroup.equivMapOfInjective P Y.subtype Y.subtype_injective).symm.surjective
  obtain ⟨g, hg⟩ := CFSG.GroupTheory.exists_map_conj_le_sylow S (hPpg.map Y.subtype)
  let R : Subgroup G := PG.map (MulAut.conj g).toMonoidHom
  have hRle : R ≤ S := hg
  let e : ↥PG ≃* ↥R :=
    Subgroup.equivMapOfInjective PG (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let ρ : ↥R →* ↥E := θPG.comp e.symm.toMonoidHom
  have hρ : Function.Surjective ρ := hθPG.comp e.symm.surjective
  have hcomm : ∀ a b : ↥E, a * b = b * a := fun a b => hE.toIsMulCommutative.is_comm.comm a b
  have hsq : ∀ a : ↥E, a * a = 1 := by
    have hdvd : Monoid.exponent ↥E ∣ 2 := @CFSG.IsElementaryAbelian.exponent_dvd_p 2 ↥E _ hE
    have hpow : ∀ a : ↥E, a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hdvd
    exact fun a => by simpa [pow_two] using hpow a
  have hge : Nat.card ↥E ≤ Nat.card (↥R ⧸ frattini ↥R) := by
    have hcard := CFSG.GH74.Uniqueness.SU.K.R4.L82.card_range_le_frattini_quot
      (hPpg.map Y.subtype |>.map (MulAut.conj g).toMonoidHom) hcomm hsq ρ
    rwa [MonoidHom.range_eq_top_of_surjective ρ hρ, Subgroup.card_top] at hcard
  have hle := h R hRle
  omega

theorem not_hasL34Section_of_card_frattini_le_eight {G : Type} [Group G] [Finite G]
    (S : Sylow 2 G) (h : ∀ R : Subgroup G, R ≤ S → Nat.card (↥R ⧸ frattini ↥R) ≤ 8) :
    ¬ HasL34Section (⊤ : Subgroup G) := by
  rintro ⟨Y, -, M, hM, hL3⟩
  exact @not_hasL34Section_aux G _ _ S h Y M hM hL3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
