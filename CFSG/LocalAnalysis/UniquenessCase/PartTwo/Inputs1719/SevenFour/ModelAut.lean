module

public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.GH74.Uniqueness.SU.KI1r3Fam
import CFSG.GH74.Uniqueness.SU.KI1r3FamL2
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL2OddGroup
import CFSG.StronglyEmbedded.UniqueCosetEnd
import CFSG.Adapters.GeneralizedFitting
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

open Subgroup CFSG.Quasithin
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G] {Y L : Subgroup G} {p e : ℕ}

private theorem center_eq_bot_of_mulEquiv_l2 {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    (e : K ≃* CFSG.GH74.GLS.IVK.L2 F) : Subgroup.center K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have h1 : MulAut.conj z = MulAut.conj (1 : K) := by
    ext x
    rw [MulAut.conj_apply, MulAut.conj_apply, one_mul, inv_one, mul_one,
      ← Subgroup.mem_center_iff.1 hz x, mul_assoc, mul_inv_cancel, mul_one]
  exact CFSG.GH74.GLS.IVK.conj_injective_of_L2 e h1

private theorem centralizer_genFitting_eq_bot {K : Subgroup ↥Y}
    (hK : K = CFSG.generalizedFitting ↥Y) (hFmap : K.map Y.subtype = L)
    (hcenter : Subgroup.center ↥L = ⊥) :
    Subgroup.centralizer (K : Set ↥Y) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hyK : y ∈ K := by
    have h1 := CFSG.Adapters.generalized_fitting_self_centralizing ↥Y
    rw [CFSG.Adapters.genFittingFStar_eq_foundations] at h1
    rw [hK] at hy ⊢
    exact h1 hy
  have hyL : (y : G) ∈ L := by
    rw [← hFmap]
    exact ⟨y, hyK, rfl⟩
  have hcent : (⟨(y : G), hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨z, hzK, hzw⟩ : ∃ z ∈ K, ((z : ↥Y) : G) = (w : G) := by
      have hw : (w : G) ∈ K.map Y.subtype := by rw [hFmap]; exact w.2
      obtain ⟨z, hz, hzw⟩ := hw
      exact ⟨z, hz, hzw⟩
    have hcomm : z * y = y * z := Subgroup.mem_centralizer_iff.1 hy z hzK
    apply Subtype.ext
    show (w : G) * (y : G) = (y : G) * (w : G)
    rw [← hzw]
    simpa using congrArg Subtype.val hcomm
  have h1 : (⟨(y : G), hyL⟩ : ↥L) = 1 := by
    simpa [hcenter] using hcent
  have h2 : (y : G) = ((1 : ↥Y) : G) := by
    simpa using congrArg Subtype.val h1
  exact Subtype.ext h2


private theorem eq_of_isSylowIn_of_inf_ne_bot {F : Type} [Field F] [Finite F] {p f : ℕ}
    {L : Subgroup G} (ψ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F) (hcard : Nat.card F = p ^ f)
    (hp : p.Prime) (_hp2 : p ≠ 2) {E₁ E₂ : Subgroup G}
    (h₁ : IsSylowIn p E₁ L) (h₂ : IsSylowIn p E₂ L) (hne : E₁ ⊓ E₂ ≠ ⊥) : E₁ = E₂ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ E₁ ⊓ E₂, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hne ((Subgroup.eq_bot_iff_forall _).2 h)
  have hxL : x ∈ L := h₁.le (Subgroup.mem_inf.1 hx).1
  have hcardL : (Nat.card ↥L).factorization p =
      (Nat.card (CFSG.GorensteinWalter.PSL2 F)).factorization p := by
    rw [Nat.card_congr ψ.toEquiv]
  have key : ∀ E : Subgroup G, IsSylowIn p E L →
      Nat.card ((E.subgroupOf L).map (ψ : ↥L →* CFSG.GorensteinWalter.PSL2 F)) =
        p ^ (Nat.card (CFSG.GorensteinWalter.PSL2 F)).factorization p := by
    intro E hE
    rw [Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE.le).toEquiv, hE.card_eq, hcardL]
  let P₁ : Sylow p (CFSG.GorensteinWalter.PSL2 F) :=
    Sylow.ofCard _ (key E₁ h₁)
  let P₂ : Sylow p (CFSG.GorensteinWalter.PSL2 F) :=
    Sylow.ofCard _ (key E₂ h₂)
  have hmem₁ : (ψ ⟨x, hxL⟩) ∈ (P₁ : Subgroup (CFSG.GorensteinWalter.PSL2 F)) := by
    rw [show (P₁ : Subgroup (CFSG.GorensteinWalter.PSL2 F)) = _ from Sylow.coe_ofCard _ _,
      Subgroup.mem_map]
    exact ⟨⟨x, hxL⟩, (Subgroup.mem_inf.1 hx).1, rfl⟩
  have hmem₂ : (ψ ⟨x, hxL⟩) ∈ (P₂ : Subgroup (CFSG.GorensteinWalter.PSL2 F)) := by
    rw [show (P₂ : Subgroup (CFSG.GorensteinWalter.PSL2 F)) = _ from Sylow.coe_ofCard _ _,
      Subgroup.mem_map]
    exact ⟨⟨x, hxL⟩, (Subgroup.mem_inf.1 hx).2, rfl⟩
  have hx1' : (ψ ⟨x, hxL⟩) ≠ 1 := by
    intro h1
    apply hx1
    have h2 : (⟨x, hxL⟩ : ↥L) = 1 := ψ.injective (by rw [h1]; exact (map_one ψ).symm)
    exact congrArg Subtype.val h2
  have heq : P₁ = P₂ := CFSG.Walter.JT.psl2_sylow_p_ti hcard P₁ P₂ hmem₁ hmem₂ hx1'
  have hEeq : (E₁.subgroupOf L).map (ψ : ↥L →* CFSG.GorensteinWalter.PSL2 F) =
      (E₂.subgroupOf L).map (ψ : ↥L →* CFSG.GorensteinWalter.PSL2 F) := by
    rw [← show (P₁ : Subgroup (CFSG.GorensteinWalter.PSL2 F)) = _ from Sylow.coe_ofCard _ _,
      ← show (P₂ : Subgroup (CFSG.GorensteinWalter.PSL2 F)) = _ from Sylow.coe_ofCard _ _, heq]
  have hsub : E₁.subgroupOf L = E₂.subgroupOf L := Subgroup.map_injective ψ.injective hEeq
  have h2 := (Subgroup.subgroupOf_inj (K := L)).1 hsub
  rwa [inf_eq_left.2 h₁.le, inf_eq_left.2 h₂.le] at h2

private theorem f6_isPGL2_of_mulEquiv_pgl {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    {q : ℕ} (hF : Nat.card F = q) (e : X ≃* CFSG.GorensteinWalter.PGL2 F) :
    CFSG.Quasithin.F6.IsPGL2 q X := by
  have hcs : Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) =
      CFSG.Open.StatedScalars (Fin 2) F := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rfl
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨e.trans (QuotientGroup.quotientMulEquivOfEq hcs)⟩⟩

theorem field_type_of_not_mem (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hF : UC22.Fstar Y = L) (hM : LieModel ↥L .PSL 2 p e) (hp2 : p ≠ 2) {t : G} (htY : t ∈ Y)
    (ht : orderOf t = 2) (htL : t ∉ L)
    (hA : ¬ ∃ A : Subgroup G, A ≤ Y ∧ L ≤ A ∧ t ∈ A ∧ F6.IsPGL2 (p ^ e) ↥A) :
    Even e ∧ ∃ E : Subgroup G, IsSylowIn p E L ∧ t ∈ normalizer (E : Set G) ∧
      Nat.card ↥(E ⊓ centralizer {t}) = p ^ (e / 2) := by
  classical
  obtain ⟨hp, he1, -, hp3, F, hfieldF, hfinF, hcardF, ePSL⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hM
  obtain ⟨ePSL⟩ := ePSL
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hoddF : Odd (Nat.card F) := hcardF ▸ hpodd.pow
  have hp3le : 3 ≤ p := by have := hp.two_le; omega
  have hgt3 : 3 < Nat.card F := by
    rw [hcardF]
    have h1 : p ≤ p ^ e := Nat.le_self_pow (by omega) p
    omega
  have hL2F : CFSG.GH74.GLS.IVK.L2Field F := ⟨hoddF, hgt3⟩
  let e' : ↥L ≃* CFSG.GH74.GLS.IVK.L2 F :=
    ePSL.trans (CFSG.GH74.GLS.IVK.L2.equivPSL F).symm
  have hcenterL : Subgroup.center ↥L = ⊥ := center_eq_bot_of_mulEquiv_l2 e'
  let K : Subgroup ↥Y := CFSG.generalizedFitting ↥Y
  have hKnormal : K.Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥Y)).2
  have : K.Normal := hKnormal
  have hFmap : K.map Y.subtype = L := by
    rw [show K = CFSG.Open.genFittingFStar ↥Y from
      (CFSG.Adapters.genFittingFStar_eq_foundations ↥Y).symm]
    exact hF
  have hcen : Subgroup.centralizer (K : Set ↥Y) = ⊥ :=
    centralizer_genFitting_eq_bot rfl hFmap hcenterL
  let eAut : K ≃* CFSG.GH74.GLS.IVK.L2 F :=
    (Subgroup.equivMapOfInjective K Y.subtype Y.subtype_injective).trans
      ((MulEquiv.subgroupCongr hFmap).trans e')
  let α : MulAut K := MulAut.conjNormal (H := K) ⟨t, htY⟩
  have ht2 : (⟨t, htY⟩ : ↥Y) ^ 2 = 1 := by
    apply Subtype.ext
    show t ^ 2 = 1
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hα2 : α ^ 2 = 1 := by
    have hα : (α : MulAut K) = MulAut.conjNormal (H := K) ⟨t, htY⟩ := rfl
    rw [hα, ← map_pow, ht2, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have hmem : (⟨t, htY⟩ : ↥Y) ∈ Subgroup.centralizer (K : Set ↥Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h2 : (⟨t, htY⟩ : ↥Y) * k * ⟨t, htY⟩⁻¹ = k := by
        have h3 := congrArg (fun f : MulAut K => (f ⟨k, hk⟩ : ↥Y)) h1
        simpa [α, MulAut.conjNormal_apply] using h3
      calc k * ⟨t, htY⟩ = ((⟨t, htY⟩ : ↥Y) * k * ⟨t, htY⟩⁻¹) * ⟨t, htY⟩ := by rw [h2]
        _ = ⟨t, htY⟩ * k := by group
    rw [hcen] at hmem
    have h4 : (⟨t, htY⟩ : ↥Y) = 1 := Subgroup.mem_bot.1 hmem
    have h5 : t = 1 := congrArg Subtype.val h4
    rw [h5, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hαord : orderOf α = 2 := orderOf_eq_prime hα2 hα1
  have hkey : α ∉ CFSG.GH74.GLS.IVK.innDiagSub eAut := by
    intro hαD
    by_cases hαI : α ∈ CFSG.GH74.GLS.IVK.innAut K
    ·
      have hmem := CFSG.StronglyEmbedded.UniqueCoset.mem_of_conjNormal_mem_inner
        (F := K) hcen (g := (⟨t, htY⟩ : ↥Y)) hαI
      have : t ∈ L := by
        rw [← hFmap]
        exact ⟨⟨t, htY⟩, hmem, rfl⟩
      exact htL this
    ·
      obtain ⟨ePGL⟩ := CFSG.GH74.Uniqueness.SU.K.R3.nonempty_equiv_pgl2_innAut_sup_zpowers
        eAut hL2F α hαD hαI
      have hKInputs : CFSG.GH74.Uniqueness.SU.K.IsPGL2
          ↥(CFSG.GH74.GLS.IVK.innAut K ⊔ Subgroup.zpowers α) p e :=
        ⟨F, hfieldF, hfinF, hcardF, ⟨ePGL⟩⟩
      have hstep := CFSG.GH74.Uniqueness.SU.K.R3.isPGL2_sup_zpowers_of_aut
        (H := ↥Y) (x := (⟨t, htY⟩ : ↥Y)) hcen hKInputs
      obtain ⟨F', hfieldF', hfinF', hcardF', ⟨ePGL'⟩⟩ := hstep
      have hmapS : (CFSG.generalizedFitting ↥Y ⊔ Subgroup.zpowers (⟨t, htY⟩ : ↥Y)).map
            Y.subtype = L ⊔ Subgroup.zpowers t := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, show CFSG.generalizedFitting ↥Y = K from rfl,
          hFmap]
        rfl
      have hAisPGL : F6.IsPGL2 (p ^ e) ↥(L ⊔ Subgroup.zpowers t) := by
        refine f6_isPGL2_of_mulEquiv_pgl hcardF' ?_
        exact (MulEquiv.subgroupCongr hmapS).symm.trans
          (((Subgroup.equivMapOfInjective _ Y.subtype Y.subtype_injective).symm).trans ePGL')
      have hAY : L ⊔ Subgroup.zpowers t ≤ Y := sup_le hLY (Subgroup.zpowers_le.2 htY)
      exact hA ⟨L ⊔ Subgroup.zpowers t, hAY, le_sup_left,
        Subgroup.mem_sup_right (Subgroup.mem_zpowers t), hAisPGL⟩
  obtain ⟨F₀, hfieldF₀, hfinF₀, hq₀, ⟨ePGL₀⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec20.L2OddGroup.isPGL2_fixedSubgroup_of_not_mem_innDiagSub
      eAut hαord hkey
  have hq₀' : Nat.card F₀ ^ 2 = p ^ e := by rw [hq₀, hcardF]
  have hdvd : Nat.card F₀ ∣ p ^ e := by
    rw [← hq₀', pow_two]
    exact dvd_mul_right _ _
  obtain ⟨k, -, hkcard⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have h2k : 2 * k = e := by
    have h1 : p ^ (2 * k) = p ^ e := by
      rw [← hq₀', hkcard, ← pow_mul, Nat.mul_comm k 2]
    exact Nat.pow_right_injective hp.two_le h1
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hkcard
      have h1 : 1 < Nat.card F₀ := Finite.one_lt_card
      omega
    · exact h0
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨⟨k, by omega⟩, ?_⟩
  let C : Subgroup G := L ⊓ Subgroup.centralizer ({t} : Set G)
  have hCmap : (CFSG.GH74.GLS.fixedSubgroup K α).map (Y.subtype.comp K.subtype) = C := by
    ext x
    constructor
    · rintro ⟨kk, hkk, rfl⟩
      have h3 : ((MulAut.conjNormal (H := K) ⟨t, htY⟩) kk : ↥Y) = (kk : ↥Y) := by
        rw [show MulAut.conjNormal (H := K) ⟨t, htY⟩ = α from rfl]
        exact congrArg Subtype.val hkk
      have h4 : (⟨t, htY⟩ : ↥Y) * (kk : ↥Y) * (⟨t, htY⟩ : ↥Y)⁻¹ = (kk : ↥Y) := by
        rw [← MulAut.conjNormal_apply]
        exact h3
      have h5 : t * ((Y.subtype.comp K.subtype) kk : G) * t⁻¹ =
          ((Y.subtype.comp K.subtype) kk : G) := by
        simpa using congrArg Subtype.val h4
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [← hFmap]
        exact Subgroup.mem_map_of_mem Y.subtype kk.2
      · rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact (mul_inv_eq_iff_eq_mul).mp h5
    · intro hx
      obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨kk, hkx⟩ : ∃ kk : ↥K, Y.subtype (K.subtype kk) = x := by
        have h1 : x ∈ K.map Y.subtype := by rw [hFmap]; exact hxL
        obtain ⟨a, ha, hax⟩ := h1
        exact ⟨⟨a, ha⟩, hax⟩
      refine ⟨kk, ?_, hkx⟩
      have hxt : t * x * t⁻¹ = x := by
        rw [Subgroup.mem_centralizer_iff] at hxC
        exact (mul_inv_eq_iff_eq_mul).mpr (hxC t (by rw [Set.mem_singleton_iff]))
      apply Subtype.ext
      show ((MulAut.conjNormal (H := K) ⟨t, htY⟩) kk : ↥Y) = (kk : ↥Y)
      rw [MulAut.conjNormal_apply]
      apply Subtype.ext
      show t * ((kk : ↥K) : G) * t⁻¹ = ((kk : ↥K) : G)
      have hkx' : ((kk : ↥K) : G) = x := hkx
      rw [hkx']
      exact hxt
  have hcardC : Nat.card C = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := by
    rw [← hCmap,
      Subgroup.card_map_of_injective (f := Y.subtype.comp K.subtype)
        (fun a b h => K.subtype_injective (Y.subtype_injective h)),
      Nat.card_congr ePGL₀.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula F₀]
  have hfactC : (Nat.card C).factorization p = k := by
    rw [hcardC, hkcard]
    have hpos : 0 < (p ^ k) ^ 2 - 1 := by
      have h2 : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      have h3 : 4 ≤ (p ^ k) ^ 2 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ (p ^ k) ^ 2 := Nat.pow_le_pow_left h2 2
      omega
    rw [Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
      Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd, add_zero]
    intro hdvd
    have h1 : p ∣ (p ^ k) ^ 2 := by
      have h0 : p ∣ p ^ k := dvd_pow_self p (by omega)
      rw [pow_two]
      exact dvd_mul_of_dvd_left h0 _
    have h2 := Nat.dvd_sub h1 hdvd
    rw [Nat.sub_sub_self (by omega)] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  obtain ⟨S⟩ : Nonempty (Sylow p ↥C) := Sylow.nonempty
  let P₀ : Subgroup G := (S : Subgroup ↥C).map C.subtype
  have hP₀card : Nat.card P₀ = p ^ k := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity, hfactC]
  have hP₀ : IsSylowIn p P₀ C :=
    isSylowIn_of_card_eq (Subgroup.map_subtype_le _) (by rw [hP₀card, hfactC])
  have hP₀L : P₀ ≤ L := hP₀.le.trans inf_le_left
  obtain ⟨E, hE, hP₀E⟩ := exists_isSylowIn_ge p hP₀L hP₀.isPGroup
  have hLconj : L.map (MulAut.conj t).toMonoidHom = L := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hx
      obtain ⟨l, hl, rfl⟩ := hx
      have h := hLn.conj_mem (⟨l, hLY hl⟩ : ↥Y) (Subgroup.mem_subgroupOf.2 hl) (⟨t, htY⟩ : ↥Y)
      simpa [MulAut.conj_apply, Subgroup.mem_subgroupOf] using h
    · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have hE' : IsSylowIn p (E.map (MulAut.conj t).toMonoidHom) L := by
    have h := (CFSG.Quasithin.E1.isSylowIn_map_mulEquiv (MulAut.conj t)
      (P := E) (H := L)).2 hE
    rwa [hLconj] at h
  have hP₀ne : P₀ ≠ ⊥ := by
    intro h0
    have h1 : Nat.card P₀ = 1 := by rw [h0, Subgroup.card_bot]
    rw [hP₀card] at h1
    have h2 : 1 < p ^ k := by
      calc 1 < p := hp.one_lt
        _ ≤ p ^ k := Nat.le_self_pow (by omega) p
    omega
  have hEtP₀ : P₀ ≤ E.map (MulAut.conj t).toMonoidHom := by
    intro y hy
    refine ⟨y, hP₀E hy, ?_⟩
    have hyc : y ∈ Subgroup.centralizer ({t} : Set G) := hP₀.le.trans inf_le_right hy
    rw [Subgroup.mem_centralizer_iff] at hyc
    have h1 : t * y = y * t := hyc t (by rw [Set.mem_singleton_iff])
    show t * y * t⁻¹ = y
    exact (mul_inv_eq_iff_eq_mul).mpr h1
  have hne : E.map (MulAut.conj t).toMonoidHom ⊓ E ≠ ⊥ := by
    intro hbot
    have hle : P₀ ≤ (⊥ : Subgroup G) := hbot ▸ le_inf hEtP₀ hP₀E
    exact hP₀ne (le_antisymm hle bot_le)
  have hEti : E.map (MulAut.conj t).toMonoidHom = E :=
    eq_of_isSylowIn_of_inf_ne_bot ePSL hcardF hp hp2 hE' hE hne
  have hnorm : t ∈ normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hEti
  refine ⟨E, hE, hnorm, ?_⟩
  have hcentE : E ⊓ Subgroup.centralizer ({t} : Set G) = P₀ := by
    have hDC : E ⊓ Subgroup.centralizer ({t} : Set G) ≤ C :=
      le_inf (inf_le_left.trans hE.le) inf_le_right
    have hP₀D : P₀ ≤ E ⊓ Subgroup.centralizer ({t} : Set G) :=
      le_inf hP₀E (hP₀.le.trans inf_le_right)
    have hDdvdE : Nat.card ↥(E ⊓ Subgroup.centralizer ({t} : Set G)) ∣
        p ^ (Nat.card ↥L).factorization p := by
      rw [← hE.card_eq]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hDdvdE
    have hjdvd : p ^ j ∣ Nat.card C := by
      rw [← hj]
      exact Subgroup.card_dvd_of_le hDC
    have hjk : j ≤ k := by
      have h1 : j ≤ (Nat.card C).factorization p :=
        (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hjdvd
      omega
    exact (Subgroup.eq_of_le_of_card_ge hP₀D
      (by rw [hj, hP₀card]; exact Nat.pow_le_pow_right hp.pos hjk)).symm
  rw [hcentE, hP₀card]
  congr 1
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
