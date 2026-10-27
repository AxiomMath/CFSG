module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight72Pair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 calC)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eight72_sp_of_pair_fixed {D : Data G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h76p : Section7.Conclusion76 D.M p)
    {K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ calC D.M) (h₂ : K₂ ∈ calC D.M) (hne : K₁ ≠ K₂)
    (hZ₁ : center (Bar2 K₁) = ⊥) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hd₁ : r ∣ Nat.card K₁) (hd₂ : r ∣ Nat.card K₂)
    (hcyc₁ : ∀ S : Sylow r (Bar2 K₁), IsCyclic (S : Subgroup (Bar2 K₁)))
    (hcyc₂ : ∀ S : Sylow r (Bar2 K₂), IsCyclic (S : Subgroup (Bar2 K₂)))
    (hRN : ∀ R : Subgroup G, IsSylowOf r R D.M →
      R ≤ normalizer (K₁ : Set G) ∧ R ≤ normalizer (K₂ : Set G))
    {B : Subgroup G} (hBM : B ≤ D.M) (hBel : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2)
    (hBN₁ : B ≤ normalizer (K₁ : Set G)) (hBN₂ : B ≤ normalizer (K₂ : Set G))
    {V₁ : Subgroup (Bar2 K₁)} {V₂ : Subgroup (Bar2 K₂)} (hV₁ : Nat.card V₁ = r)
    (hV₂ : Nat.card V₂ = r)
    (hBV₁ : ∀ b (hb : b ∈ B), ∀ v ∈ V₁, UC6S846.rhoL K₁ ⟨b, hBN₁ hb⟩ v = v)
    (hBV₂ : ∀ b (hb : b ∈ B), ∀ v ∈ V₂, UC6S846.rhoL K₂ ⟨b, hBN₂ hb⟩ v = v) :
    IsStronglyPEmbedded r D.M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hns := UC6S846.not_solvable_of_mem_calC h₁
  by_cases hrσ : r ∈ D.sig
  · exact UC6S846.sp_of_mem_sig hSg hns hrσ
  have : Fact r.Prime := ⟨hr⟩
  have hK₁M : K₁ ≤ D.M := h₁.1.le
  have hK₂M : K₂ ≤ D.M := h₂.1.le
  have hK₁N₂ : K₁ ≤ normalizer (K₂ : Set G) := PartTwo.calC_le_normalizer_of_ne h₂ h₁ hne.symm
  have hK₂N₁ : K₂ ≤ normalizer (K₁ : Set G) := PartTwo.calC_le_normalizer_of_ne h₁ h₂ hne
  obtain ⟨R₀, hR₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf r D.M
  have hR₀N₁ : R₀ ≤ normalizer (K₁ : Set G) := (hRN R₀ hR₀).1
  have hR₀N₂ : R₀ ≤ normalizer (K₂ : Set G) := (hRN R₀ hR₀).2
  set J : Subgroup G := D.M ⊓ normalizer (K₁ : Set G) ⊓ normalizer (K₂ : Set G)
  have hJM : J ≤ D.M := inf_le_left.trans inf_le_left
  have hJN₁ : J ≤ normalizer (K₁ : Set G) := inf_le_left.trans inf_le_right
  have hJN₂ : J ≤ normalizer (K₂ : Set G) := inf_le_right
  have hR₀J : R₀ ≤ J := le_inf (le_inf hR₀.le hR₀N₁) hR₀N₂
  have hR₀Jsyl : IsSylowOf r R₀ J := hR₀.of_le hR₀J hJM
  obtain ⟨a₁, a₂, ha₁, ha₂, ha₁o, ha₂o, hER₀, hEel₀, hEcard₀⟩ :=
    eight72_exists_pair h₁ h₂ hne hZ₁ hr hr2 hd₁ hd₂ hR₀Jsyl
      (le_inf (le_inf hK₁M Subgroup.le_normalizer) hK₁N₂)
      (le_inf (le_inf hK₂M hK₂N₁) Subgroup.le_normalizer) hJN₁ hJN₂
  set abar₁ : Bar2 K₁ := QuotientGroup.mk (⟨a₁, ha₁⟩ : ↥K₁) with habar₁def
  set abar₂ : Bar2 K₂ := QuotientGroup.mk (⟨a₂, ha₂⟩ : ↥K₂) with habar₂def
  have habar₁ord : orderOf abar₁ = r := by
    have hdvd : orderOf abar₁ ∣ r := by
      have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)) (⟨a₁, ha₁⟩ : ↥K₁)
      rw [QuotientGroup.mk'_apply, Subgroup.orderOf_mk, ha₁o] at h
      exact h
    rcases (Nat.dvd_prime hr).1 hdvd with h | h
    · exfalso
      have hone : abar₁ = 1 := orderOf_eq_one_iff.1 h
      rw [habar₁def] at hone
      have hmem : (⟨a₁, ha₁⟩ : ↥K₁) ∈ CFSG.pCore 2 ↥K₁ :=
        (QuotientGroup.eq_one_iff (⟨a₁, ha₁⟩ : ↥K₁)).1 hone
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K₁) ⟨_, hmem⟩
      have hk' : (⟨a₁, ha₁⟩ : ↥K₁) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h2 : r ∣ 2 ^ k := by
        have h3 := orderOf_dvd_of_pow_eq_one hk'
        rwa [Subgroup.orderOf_mk, ha₁o] at h3
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    · exact h
  have habar₂ord : orderOf abar₂ = r := by
    have hdvd : orderOf abar₂ ∣ r := by
      have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥K₂)) (⟨a₂, ha₂⟩ : ↥K₂)
      rw [QuotientGroup.mk'_apply, Subgroup.orderOf_mk, ha₂o] at h
      exact h
    rcases (Nat.dvd_prime hr).1 hdvd with h | h
    · exfalso
      have hone : abar₂ = 1 := orderOf_eq_one_iff.1 h
      rw [habar₂def] at hone
      have hmem : (⟨a₂, ha₂⟩ : ↥K₂) ∈ CFSG.pCore 2 ↥K₂ :=
        (QuotientGroup.eq_one_iff (⟨a₂, ha₂⟩ : ↥K₂)).1 hone
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K₂) ⟨_, hmem⟩
      have hk' : (⟨a₂, ha₂⟩ : ↥K₂) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h2 : r ∣ 2 ^ k := by
        have h3 := orderOf_dvd_of_pow_eq_one hk'
        rwa [Subgroup.orderOf_mk, ha₂o] at h3
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    · exact h
  have hconj₁ : ∃ h : Bar2 K₁, (Subgroup.zpowers abar₁).map (MulAut.conj h).toMonoidHom = V₁ := by
    have hP₁ : IsPGroup r V₁ := IsPGroup.of_card (n := 1) (by rw [hV₁, pow_one])
    have hP₂ : IsPGroup r (Subgroup.zpowers abar₁) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, habar₁ord, pow_one])
    obtain ⟨T₀, hT₀⟩ := hP₁.exists_le_sylow
    obtain ⟨T₁, hT₁⟩ := hP₂.exists_le_sylow
    obtain ⟨j, hj⟩ := MulAction.exists_smul_eq (Bar2 K₁) T₁ T₀
    have hT : (T₀ : Subgroup (Bar2 K₁)) =
        (T₁ : Subgroup (Bar2 K₁)).map (MulAut.conj j).toMonoidHom := by
      rw [← hj, Sylow.coe_subgroup_smul]
      rfl
    have hcompA : (MulAut.conj j⁻¹).toMonoidHom.comp (MulAut.conj j).toMonoidHom =
        MonoidHom.id (Bar2 K₁) := by
      ext x
      show (MulAut.conj j⁻¹) ((MulAut.conj j) x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    have hV₁T : V₁.map (MulAut.conj j⁻¹).toMonoidHom ≤ (T₁ : Subgroup (Bar2 K₁)) := by
      rw [hT] at hT₀
      calc V₁.map (MulAut.conj j⁻¹).toMonoidHom
          ≤ ((T₁ : Subgroup (Bar2 K₁)).map (MulAut.conj j).toMonoidHom).map
              (MulAut.conj j⁻¹).toMonoidHom := Subgroup.map_mono hT₀
        _ = ((T₁ : Subgroup (Bar2 K₁))).map ((MulAut.conj j⁻¹).toMonoidHom.comp
              (MulAut.conj j).toMonoidHom) := Subgroup.map_map _ _ _
        _ = (T₁ : Subgroup (Bar2 K₁)) := by rw [hcompA, Subgroup.map_id]
    have hcard : Nat.card ((Subgroup.zpowers abar₁).subgroupOf (T₁ : Subgroup (Bar2 K₁))) =
        Nat.card ((V₁.map (MulAut.conj j⁻¹).toMonoidHom).subgroupOf
          (T₁ : Subgroup (Bar2 K₁))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁T).toEquiv, Nat.card_zpowers,
        habar₁ord, Subgroup.card_map_of_injective (MulAut.conj j⁻¹).injective, hV₁]
    have : IsCyclic ↥(T₁ : Subgroup (Bar2 K₁)) := hcyc₁ T₁
    have heq : (Subgroup.zpowers abar₁).subgroupOf (T₁ : Subgroup (Bar2 K₁)) =
        (V₁.map (MulAut.conj j⁻¹).toMonoidHom).subgroupOf (T₁ : Subgroup (Bar2 K₁)) :=
      (IsCyclic.subgroup_eq_iff_card_eq (G := (T₁ : Subgroup (Bar2 K₁)))).mpr hcard
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hT₁, inf_of_le_left hV₁T] at heq
    refine ⟨j, ?_⟩
    rw [heq, Subgroup.map_map]
    have hcompB : (MulAut.conj j).toMonoidHom.comp (MulAut.conj j⁻¹).toMonoidHom =
        MonoidHom.id (Bar2 K₁) := by
      ext x
      show (MulAut.conj j) ((MulAut.conj j⁻¹) x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hcompB, Subgroup.map_id]
  have hconj₂ : ∃ h : Bar2 K₂, (Subgroup.zpowers abar₂).map (MulAut.conj h).toMonoidHom = V₂ := by
    have hP₁ : IsPGroup r V₂ := IsPGroup.of_card (n := 1) (by rw [hV₂, pow_one])
    have hP₂ : IsPGroup r (Subgroup.zpowers abar₂) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, habar₂ord, pow_one])
    obtain ⟨T₀, hT₀⟩ := hP₁.exists_le_sylow
    obtain ⟨T₁, hT₁⟩ := hP₂.exists_le_sylow
    obtain ⟨j, hj⟩ := MulAction.exists_smul_eq (Bar2 K₂) T₁ T₀
    have hT : (T₀ : Subgroup (Bar2 K₂)) =
        (T₁ : Subgroup (Bar2 K₂)).map (MulAut.conj j).toMonoidHom := by
      rw [← hj, Sylow.coe_subgroup_smul]
      rfl
    have hcompA : (MulAut.conj j⁻¹).toMonoidHom.comp (MulAut.conj j).toMonoidHom =
        MonoidHom.id (Bar2 K₂) := by
      ext x
      show (MulAut.conj j⁻¹) ((MulAut.conj j) x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    have hV₂T : V₂.map (MulAut.conj j⁻¹).toMonoidHom ≤ (T₁ : Subgroup (Bar2 K₂)) := by
      rw [hT] at hT₀
      calc V₂.map (MulAut.conj j⁻¹).toMonoidHom
          ≤ ((T₁ : Subgroup (Bar2 K₂)).map (MulAut.conj j).toMonoidHom).map
              (MulAut.conj j⁻¹).toMonoidHom := Subgroup.map_mono hT₀
        _ = ((T₁ : Subgroup (Bar2 K₂))).map ((MulAut.conj j⁻¹).toMonoidHom.comp
              (MulAut.conj j).toMonoidHom) := Subgroup.map_map _ _ _
        _ = (T₁ : Subgroup (Bar2 K₂)) := by rw [hcompA, Subgroup.map_id]
    have hcard : Nat.card ((Subgroup.zpowers abar₂).subgroupOf (T₁ : Subgroup (Bar2 K₂))) =
        Nat.card ((V₂.map (MulAut.conj j⁻¹).toMonoidHom).subgroupOf
          (T₁ : Subgroup (Bar2 K₂))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₂T).toEquiv, Nat.card_zpowers,
        habar₂ord, Subgroup.card_map_of_injective (MulAut.conj j⁻¹).injective, hV₂]
    have : IsCyclic ↥(T₁ : Subgroup (Bar2 K₂)) := hcyc₂ T₁
    have heq : (Subgroup.zpowers abar₂).subgroupOf (T₁ : Subgroup (Bar2 K₂)) =
        (V₂.map (MulAut.conj j⁻¹).toMonoidHom).subgroupOf (T₁ : Subgroup (Bar2 K₂)) :=
      (IsCyclic.subgroup_eq_iff_card_eq (G := (T₁ : Subgroup (Bar2 K₂)))).mpr hcard
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hT₁, inf_of_le_left hV₂T] at heq
    refine ⟨j, ?_⟩
    rw [heq, Subgroup.map_map]
    have hcompB : (MulAut.conj j).toMonoidHom.comp (MulAut.conj j⁻¹).toMonoidHom =
        MonoidHom.id (Bar2 K₂) := by
      ext x
      show (MulAut.conj j) ((MulAut.conj j⁻¹) x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hcompB, Subgroup.map_id]
  obtain ⟨h₁q, hh₁q⟩ := hconj₁
  obtain ⟨h₂q, hh₂q⟩ := hconj₂
  obtain ⟨k₁, hk₁⟩ := QuotientGroup.mk_surjective h₁q
  obtain ⟨k₂, hk₂⟩ := QuotientGroup.mk_surjective h₂q
  set c : G := (k₁ : G) * (k₂ : G)
  have hcM : c ∈ D.M := D.M.mul_mem (hK₁M k₁.2) (hK₂M k₂.2)
  have hcN₁ : c ∈ normalizer (K₁ : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer k₁.2) (hK₂N₁ k₂.2)
  have hcN₂ : c ∈ normalizer (K₂ : Set G) :=
    Subgroup.mul_mem _ (hK₁N₂ k₁.2) (Subgroup.le_normalizer k₂.2)
  set a'₁ : G := MulAut.conj c a₁ with ha'₁def
  set a'₂ : G := MulAut.conj c a₂ with ha'₂def
  have ha'₁K : a'₁ ∈ K₁ := by
    rw [ha'₁def, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.1 hcN₁ a₁).1 ha₁
  have ha'₂K : a'₂ ∈ K₂ := by
    rw [ha'₂def, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.1 hcN₂ a₂).1 ha₂
  set O : Subgroup G := pCoreOf 2 D.M with hOdef
  have hMO : D.M ≤ normalizer (O : Set G) := by
    rw [hOdef]
    exact Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf D.M)
  set R' : Subgroup G := R₀.map (MulAut.conj c).toMonoidHom with hR'def
  have hR'M : R' ≤ D.M := by
    rw [hR'def]
    rintro _ ⟨x, hx, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem hcM (hR₀.le hx)) (D.M.inv_mem hcM)
  have hR'syl : IsSylowOf r R' D.M := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hR'M ?_
    rw [hR'def, Subgroup.card_map_of_injective (MulAut.conj c).injective, hR₀.card_eq]
  set E' : Subgroup G := Subgroup.zpowers a'₁ ⊔ Subgroup.zpowers a'₂ with hE'def
  have hE'eq : E' = (Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂).map
      (MulAut.conj c).toMonoidHom := by
    rw [hE'def, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hE'card : Nat.card E' = r ^ 2 := by
    rw [hE'eq, Subgroup.card_map_of_injective (MulAut.conj c).injective, hEcard₀]
  have hE'el : IsElemAbelian r E' := by
    rw [hE'eq]
    exact UC6S846.isElemAbelian_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj c).injective).symm hEel₀
  have hE'Z : E' ≤ R' ⊓ centralizer (R' : Set G) := by
    intro x hx
    have hx' : x ∈ (Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂).map
        (MulAut.conj c).toMonoidHom := by rw [← hE'eq]; exact hx
    obtain ⟨e, he, rfl⟩ := hx'
    have heR : e ∈ R₀ := (Subgroup.mem_inf.1 (hER₀ he)).1
    have heC : e ∈ centralizer (R₀ : Set G) := (Subgroup.mem_inf.1 (hER₀ he)).2
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hR'def]
      exact Subgroup.mem_map_of_mem _ heR
    · rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨r₀, hr₀, rfl⟩
      rw [Subgroup.mem_centralizer_iff] at heC
      calc (MulAut.conj c).toMonoidHom r₀ * (MulAut.conj c).toMonoidHom e
          = (MulAut.conj c).toMonoidHom (r₀ * e) := (map_mul _ r₀ e).symm
        _ = (MulAut.conj c).toMonoidHom (e * r₀) := by rw [heC r₀ hr₀]
        _ = (MulAut.conj c).toMonoidHom e * (MulAut.conj c).toMonoidHom r₀ := map_mul _ e r₀
  have hE'M : E' ≤ D.M := hE'Z.trans (inf_le_left.trans hR'M)
  have hfix₂ : UC6S846.rhoL K₁ ⟨(k₂ : G), hK₂N₁ k₂.2⟩ = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [MulAut.one_apply]
      refine (UC6S846.rhoL_fix_iff K₁ ⟨(k₂ : G), hK₂N₁ k₂.2⟩ y).2 ?_
      have hmem : ⁅(k₂ : G), (y : G)⁆ ∈ pCoreOf 2 K₁ := by
        have h1 : ⁅(k₂ : G), (y : G)⁆ ∈ ⁅K₂, K₁⁆ :=
          Subgroup.commutator_mem_commutator k₂.2 y.2
        rw [Subgroup.commutator_comm] at h1
        exact (PartTwo.calC_commutator_le_of_ne h₁ h₂ hne h1).1
      simpa [commutatorElement_def] using hmem
  have hfix₁ : UC6S846.rhoL K₂ ⟨(k₁ : G), hK₁N₂ k₁.2⟩ = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [MulAut.one_apply]
      refine (UC6S846.rhoL_fix_iff K₂ ⟨(k₁ : G), hK₁N₂ k₁.2⟩ y).2 ?_
      have hmem : ⁅(k₁ : G), (y : G)⁆ ∈ pCoreOf 2 K₂ := by
        have h1 : ⁅(k₁ : G), (y : G)⁆ ∈ ⁅K₁, K₂⁆ :=
          Subgroup.commutator_mem_commutator k₁.2 y.2
        exact (PartTwo.calC_commutator_le_of_ne h₁ h₂ hne h1).2
      simpa [commutatorElement_def] using hmem
  have hrho₁ : UC6S846.rhoL K₁ ⟨c, hcN₁⟩ = MulAut.conj h₁q := by
    have hsplit : (⟨c, hcN₁⟩ : ↥(normalizer (K₁ : Set G))) =
        ⟨(k₁ : G), Subgroup.le_normalizer k₁.2⟩ * ⟨(k₂ : G), hK₂N₁ k₂.2⟩ :=
      Subtype.ext rfl
    rw [hsplit, map_mul, hfix₂, mul_one, UC6S846.rhoL_inner K₁ (k₁ : G) k₁.2]
    rw [← hk₁]
  have hrho₂ : UC6S846.rhoL K₂ ⟨c, hcN₂⟩ = MulAut.conj h₂q := by
    have hsplit : (⟨c, hcN₂⟩ : ↥(normalizer (K₂ : Set G))) =
        ⟨(k₁ : G), hK₁N₂ k₁.2⟩ * ⟨(k₂ : G), Subgroup.le_normalizer k₂.2⟩ :=
      Subtype.ext rfl
    rw [hsplit, map_mul, hfix₁, one_mul, UC6S846.rhoL_inner K₂ (k₂ : G) k₂.2]
    rw [← hk₂]
  have himg₁ : (QuotientGroup.mk (⟨a'₁, ha'₁K⟩ : ↥K₁) : Bar2 K₁) = MulAut.conj h₁q abar₁ := by
    have h2 : (QuotientGroup.mk (⟨a'₁, ha'₁K⟩ : ↥K₁) : Bar2 K₁) =
        UC6S846.rhoL K₁ ⟨c, hcN₁⟩ abar₁ := by
      rw [habar₁def, UC6S846.rhoL_mk]
      rfl
    rw [h2, hrho₁]
  have himg₂ : (QuotientGroup.mk (⟨a'₂, ha'₂K⟩ : ↥K₂) : Bar2 K₂) = MulAut.conj h₂q abar₂ := by
    have h2 : (QuotientGroup.mk (⟨a'₂, ha'₂K⟩ : ↥K₂) : Bar2 K₂) =
        UC6S846.rhoL K₂ ⟨c, hcN₂⟩ abar₂ := by
      rw [habar₂def, UC6S846.rhoL_mk]
      rfl
    rw [h2, hrho₂]
  have himgV₁ : (QuotientGroup.mk (⟨a'₁, ha'₁K⟩ : ↥K₁) : Bar2 K₁) ∈ V₁ := by
    rw [himg₁, ← hh₁q]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers abar₁)
  have himgV₂ : (QuotientGroup.mk (⟨a'₂, ha'₂K⟩ : ↥K₂) : Bar2 K₂) ∈ V₂ := by
    rw [himg₂, ← hh₂q]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers abar₂)
  have hBA₁ : ∀ b ∈ B, b * a'₁ * b⁻¹ * a'₁⁻¹ ∈ O := by
    intro b hb
    have hfix : UC6S846.rhoL K₁ ⟨b, hBN₁ hb⟩ (QuotientGroup.mk (⟨a'₁, ha'₁K⟩ : ↥K₁)) =
        QuotientGroup.mk (⟨a'₁, ha'₁K⟩ : ↥K₁) := hBV₁ b hb _ himgV₁
    exact UC22.uc22p22r_pCoreOf_le_of_isSubnormal h₁.1
      ((UC6S846.rhoL_fix_iff K₁ ⟨b, hBN₁ hb⟩ ⟨a'₁, ha'₁K⟩).1 hfix)
  have hBA₂ : ∀ b ∈ B, b * a'₂ * b⁻¹ * a'₂⁻¹ ∈ O := by
    intro b hb
    have hfix : UC6S846.rhoL K₂ ⟨b, hBN₂ hb⟩ (QuotientGroup.mk (⟨a'₂, ha'₂K⟩ : ↥K₂)) =
        QuotientGroup.mk (⟨a'₂, ha'₂K⟩ : ↥K₂) := hBV₂ b hb _ himgV₂
    exact UC22.uc22p22r_pCoreOf_le_of_isSubnormal h₂.1
      ((UC6S846.rhoL_fix_iff K₂ ⟨b, hBN₂ hb⟩ ⟨a'₂, ha'₂K⟩).1 hfix)
  have hcommE : ∀ e ∈ E', ∀ b ∈ B, e * b * e⁻¹ * b⁻¹ ∈ O := by
    intro e he b hb
    let S : Subgroup G :=
      { carrier := {g | g ∈ D.M ∧ g * b * g⁻¹ * b⁻¹ ∈ O}
        mul_mem' := fun {g h} hg hh => ⟨D.M.mul_mem hg.1 hh.1, by
          have h1 := (Subgroup.mem_normalizer_iff.1 (hMO hg.1) _).1 hh.2
          have hkey : g * h * b * (g * h)⁻¹ * b⁻¹ =
              (g * (h * b * h⁻¹ * b⁻¹) * g⁻¹) * (g * b * g⁻¹ * b⁻¹) := by group
          rw [hkey]
          exact O.mul_mem h1 hg.2⟩
        one_mem' := ⟨D.M.one_mem, by simp⟩
        inv_mem' := fun {g} hg => ⟨D.M.inv_mem hg.1, by
          have h1 :=
            (Subgroup.mem_normalizer_iff.1 (hMO (D.M.inv_mem hg.1)) _).1 (O.inv_mem hg.2)
          have hkey : g⁻¹ * b * g⁻¹⁻¹ * b⁻¹ = g⁻¹ * (g * b * g⁻¹ * b⁻¹)⁻¹ * g⁻¹⁻¹ := by
            group
          rw [hkey]
          exact h1⟩ }
    have hSmem : ∀ g : G, g ∈ S ↔ g ∈ D.M ∧ g * b * g⁻¹ * b⁻¹ ∈ O := fun g => Iff.rfl
    have ha'₁S : a'₁ ∈ S := by
      refine (hSmem a'₁).2 ⟨hK₁M ha'₁K, ?_⟩
      have h := O.inv_mem (hBA₁ b hb)
      have hkey : (b * a'₁ * b⁻¹ * a'₁⁻¹)⁻¹ = a'₁ * b * a'₁⁻¹ * b⁻¹ := by group
      rwa [hkey] at h
    have ha'₂S : a'₂ ∈ S := by
      refine (hSmem a'₂).2 ⟨hK₂M ha'₂K, ?_⟩
      have h := O.inv_mem (hBA₂ b hb)
      have hkey : (b * a'₂ * b⁻¹ * a'₂⁻¹)⁻¹ = a'₂ * b * a'₂⁻¹ * b⁻¹ := by group
      rwa [hkey] at h
    have hE'S : E' ≤ S := sup_le (Subgroup.zpowers_le.2 ha'₁S) (Subgroup.zpowers_le.2 ha'₂S)
    exact ((hSmem e).1 (hE'S he)).2
  obtain ⟨B', hB'C, hB'le, ⟨eB⟩⟩ := UC6S846.exists_centralizing_copy hr hr2 hp hp2 O B E'
    (UC6S846.isPGroup_pCoreOf D.M) (hBM.trans hMO) (hE'M.trans hMO) hBel.isPGroup
    hE'el.isPGroup hcommE
  have hB'M : B' ≤ D.M := hB'le.trans (sup_le hBM (Subgroup.map_subtype_le _))
  have hB'el : IsElemAbelian p B' := UC6S846.isElemAbelian_of_mulEquiv eB hBel
  have hB'c : Nat.card B' = p ^ 2 := by rw [Nat.card_congr eB.toEquiv, hBc]
  have hΓ := h76p r hr E' hE'M hE'el hE'card
    (lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hp (le_inf hB'M hB'C) hB'el hB'c))
    (fun X hXE _ => lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hp
      (le_inf hB'M (hB'C.trans ((Subgroup.centralizer_le hXE).trans
        (Subgroup.centralizer_le_normalizer _)))) hB'el hB'c))
  exact h614 (UC6S846.sig_subset_sig1 hSg hns) r hr hr2 hrσ R' hR'syl E' hE'Z hE'el hE'card hΓ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
