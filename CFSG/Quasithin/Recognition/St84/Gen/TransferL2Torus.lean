module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2Inner
import CFSG.Quasithin.Vol2.Ch5Sec1Hall
public import CFSG.Quasithin.Recognition.St84.Gen.SL2TorusAut
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining
import CFSG.Walter.Cited.SuzukiHyp
public import CFSG.GroupTheory.ConjActionModPCore

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

private theorem coprime_natCard_sub_one {F : Type} [Field F] [Finite F] :
    Nat.Coprime (Nat.card F) (Nat.card F - 1) := by
  have h1 : 1 ≤ Nat.card F := Nat.card_pos
  have hsub : Nat.card F - 1 + 1 = Nat.card F := Nat.sub_add_cancel h1
  have h := (Nat.coprime_self_add_right (m := Nat.card F - 1) (n := 1)).mpr
    (Nat.coprime_one_right _)
  rw [hsub, Nat.coprime_comm] at h
  exact h

private theorem inf_utri_eq_bot_of_card {F : Type} [Field F] [Finite F] [CharP F 2]
    {E : Subgroup (SL(2, F))} (hcard : Nat.card E = Nat.card F - 1) :
    utri F ⊓ E = ⊥ := by
  refine Subgroup.inf_eq_bot_of_coprime ?_
  rw [card_utri, hcard]
  exact coprime_natCard_sub_one

private theorem sup_utri_eq_borel_of_card {F : Type} [Field F] [Finite F] [CharP F 2]
    {E : Subgroup (SL(2, F))} (hE : E ≤ borel F) (hcard : Nat.card E = Nat.card F - 1) :
    utri F ⊔ E = borel F := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le utri_le_borel hE) ?_
  have hdvd : Nat.card ↥(utri F ⊔ E) ∣ Nat.card ↥(borel F) :=
    Subgroup.card_dvd_of_le (sup_le utri_le_borel hE)
  have h1 : Nat.card (utri F) ∣ Nat.card ↥(utri F ⊔ E) :=
    Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card E ∣ Nat.card ↥(utri F ⊔ E) :=
    Subgroup.card_dvd_of_le le_sup_right
  have hcop : Nat.Coprime (Nat.card (utri F)) (Nat.card E) := by
    rw [card_utri, hcard]
    exact coprime_natCard_sub_one
  have hprod : Nat.card (utri F) * Nat.card E ∣ Nat.card ↥(utri F ⊔ E) :=
    hcop.mul_dvd_of_dvd_of_dvd h1 h2
  have hb : Nat.card (borel F) = Nat.card (utri F) * Nat.card E := by
    rw [card_borel, card_utri, hcard]
  have heq : Nat.card ↥(utri F ⊔ E) = Nat.card (borel F) := by
    rw [hb]
    exact Nat.dvd_antisymm (by rwa [hb] at hdvd) hprod
  exact le_of_eq heq.symm

private theorem relIndex_utri_borel {F : Type} [Field F] [Finite F] [CharP F 2] :
    (utri F).relIndex (borel F) = Nat.card F - 1 := by
  have h := Subgroup.relIndex_mul_card (H := utri F) (K := borel F)
  rw [inf_of_le_left utri_le_borel, card_utri, card_borel] at h
  have hpos : 0 < Nat.card F := Nat.card_pos
  have h' : Nat.card F * ((utri F).relIndex (borel F)) = Nat.card F * (Nat.card F - 1) := by
    rw [mul_comm (Nat.card F), h]
  exact Nat.eq_of_mul_eq_mul_left hpos h'

private theorem odd_relIndex_utri_borel {F : Type} [Field F] [Finite F] [CharP F 2] :
    Odd ((utri F).relIndex (borel F)) := by
  rw [relIndex_utri_borel]
  obtain ⟨n, hn1, hn⟩ := exists_natCard_eq_two_pow (F := F)
  rw [hn]
  exact Nat.Even.sub_odd Nat.one_le_two_pow
    (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two hn1.ne') odd_one

private theorem exists_conj_sylow_torus {F : Type} [Field F] [Finite F] [CharP F 2]
    {P E : Subgroup (SL(2, F))} (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index)
    (hE : E ≤ Subgroup.normalizer (P : Set (SL(2, F))))
    (hEcard : Nat.card E = Nat.card F - 1) :
    ∃ g : SL(2, F),
      P.map (MulAut.conj g).toMonoidHom = utri F ∧
      E.map (MulAut.conj g).toMonoidHom = torus F := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P' : Sylow 2 (SL(2, F)) := IsPGroup.toSylow hP hidx
  obtain ⟨h, hh⟩ := exists_conjSubgroup_utri_eq_of_sylow P'
  have hP' : (P' : Subgroup (SL(2, F))) = P := IsPGroup.toSylow_coe hP hidx
  have hh' : (utri F).map (MulAut.conj h).toMonoidHom = P := by
    change (utri F).map (MulAut.conj h).toMonoidHom = (P' : Subgroup (SL(2, F))) at hh
    rwa [hP'] at hh
  have hPmap : P.map (MulAut.conj h⁻¹).toMonoidHom = utri F := by
    have h' : P.map (MulAut.conj h).symm.toMonoidHom = utri F :=
      (Subgroup.map_symm_eq_iff_map_eq (e := MulAut.conj h) (H := P) (K := utri F)).mpr hh'
    have hinv : MulAut.conj h⁻¹ = (MulAut.conj h).symm := by
      rw [← MulAut.inv_def, ← map_inv]
    rw [hinv]
    exact h'
  let g : SL(2, F) := h⁻¹
  let E' : Subgroup (SL(2, F)) := E.map (MulAut.conj g).toMonoidHom
  have hE'le : E' ≤ borel F := by
    have h := (Subgroup.map_mono hE).trans (Subgroup.le_normalizer_map (MulAut.conj g).toMonoidHom)
    rwa [hPmap, normalizer_utri] at h
  have hE'card : Nat.card E' = Nat.card F - 1 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEcard]
  have hE'inf : utri F ⊓ E' = ⊥ := inf_utri_eq_bot_of_card hE'card
  have hE'sup : utri F ⊔ E' = borel F := sup_utri_eq_borel_of_card hE'le hE'card
  obtain ⟨x, hxUtri, hxE⟩ :=
    CFSG.Quasithin.H13.exists_mem_conj_of_complements
      (P := utri F) (Y := borel F) (E₁ := torus F) (E₂ := E')
      utri_le_borel (by rw [normalizer_utri]) isPGroup_utri odd_relIndex_utri_borel
      torus_le_borel inf_utri_torus borel_eq_sup.symm hE'le hE'inf hE'sup
  have hcomp : ∀ a b : SL(2, F),
      (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj (a * b)).toMonoidHom := by
    intro a b
    apply MonoidHom.ext
    intro y
    show a * (b * y * b⁻¹) * a⁻¹ = (a * b) * y * (a * b)⁻¹
    group
  refine ⟨x⁻¹ * g, ?_, ?_⟩
  · rw [show (MulAut.conj (x⁻¹ * g)).toMonoidHom =
        (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom from (hcomp _ _).symm,
      ← Subgroup.map_map, hPmap]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer ((utri F).inv_mem hxUtri))
  · rw [show (MulAut.conj (x⁻¹ * g)).toMonoidHom =
        (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom from (hcomp _ _).symm,
      ← Subgroup.map_map, show E.map (MulAut.conj g).toMonoidHom = E' from rfl, hxE,
      Subgroup.map_map, hcomp, inv_mul_cancel, map_one]
    change (torus F).map (MonoidHom.id (SL(2, F))) = torus F
    rw [Subgroup.map_id]

theorem relIndex_normalizer_of_isL2Quot {L T : Subgroup G} [Finite ↥L] {n : ℕ}
    (hn : 1 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) :
    (T.subgroupOf L).relIndex
      (Subgroup.normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L)) = 2 ^ n - 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup ↥L := CFSG.pCore 2 ↥L
  let S : Subgroup ↥L := T.subgroupOf L
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' P
  have hPleS : P ≤ S := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (IsSylowTwoOf.pCoreOf_le hT ((CFSG.mem_openPCoreOf_iff (H := L) x).mpr hx))
  have hS2 : IsPGroup 2 S :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  have hSodd : ¬ 2 ∣ S.index := hT.2.2
  have hSbar2 : IsPGroup 2 (S.map π) := hS2.map π
  have hkerπ : π.ker = P := QuotientGroup.ker_mk' P
  have hker_le : π.ker ≤ S := by rw [hkerπ]; exact hPleS
  have hSbaridx : (S.map π).index = S.index :=
    Subgroup.index_map_eq (H := S) (f := π) (QuotientGroup.mk'_surjective P) hker_le
  have hSbarodd : ¬ 2 ∣ (S.map π).index := by rw [hSbaridx]; exact hSodd
  have hpair : IsL2Pair (oTwoQuot ↥L) (S.map π) (2 ^ n) :=
    IsL2Pair.of_psl_isPGroup (by omega) hq hSbar2 hSbarodd
  have hrelbar : (S.map π).relIndex
      (Subgroup.normalizer ((S.map π : Subgroup (oTwoQuot ↥L)) : Set (oTwoQuot ↥L))) =
      2 ^ n - 1 := hpair.relIndex_normalizer
  have hNmap : (Subgroup.normalizer (S : Set ↥L)).map π =
      Subgroup.normalizer ((S.map π : Subgroup (oTwoQuot ↥L)) : Set (oTwoQuot ↥L)) := by
    have hcomap : (Subgroup.normalizer
        ((S.map π : Subgroup (oTwoQuot ↥L)) : Set (oTwoQuot ↥L))).comap π =
        Subgroup.normalizer (S : Set ↥L) := by
      rw [Subgroup.comap_normalizer_eq_of_surjective _
        (QuotientGroup.mk'_surjective P), Subgroup.comap_map_eq_self hker_le]
    rw [← hcomap, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective P)]
  have hrel : S.relIndex (Subgroup.normalizer (S : Set ↥L)) = 2 ^ n - 1 := by
    have h := Subgroup.relIndex_map_map π S (Subgroup.normalizer (S : Set ↥L))
    rw [hNmap, sup_eq_left.mpr hker_le,
      sup_eq_left.mpr (hker_le.trans Subgroup.le_normalizer)] at h
    rw [← h]
    exact hrelbar
  exact hrel

theorem exists_le_normalizer_card_eq_of_isL2Quot {L T : Subgroup G} [Finite ↥L] {n : ℕ}
    (hn : 1 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) :
    ∃ D : Subgroup G, D ≤ L ⊓ Subgroup.normalizer (T : Set G) ∧ Nat.card D = 2 ^ n - 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Subgroup ↥L := T.subgroupOf L
  have hS2 : IsPGroup 2 S :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  have hrel : S.relIndex (Subgroup.normalizer (S : Set ↥L)) = 2 ^ n - 1 :=
    relIndex_normalizer_of_isL2Quot hn hq hT
  have hoddrel : Odd (S.relIndex (Subgroup.normalizer (S : Set ↥L))) := by
    rw [hrel]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two (by omega)) odd_one
  have hcop : Nat.Coprime (Nat.card S) (S.relIndex (Subgroup.normalizer (S : Set ↥L))) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hS2
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hoddrel)
  obtain ⟨E, hEY, -, -, hEcard, -⟩ :=
    CFSG.Quasithin.H13.exists_complement_of_coprime (G := ↥L)
      (P := S) (Y := Subgroup.normalizer (S : Set ↥L)) Subgroup.le_normalizer le_rfl hcop
  have hmapNorm : (Subgroup.normalizer (S : Set ↥L)).map L.subtype =
      Subgroup.normalizer (T : Set G) ⊓ L := by
    rw [← Subgroup.subgroupOf_normalizer_eq hT.1, Subgroup.subgroupOf_map_subtype]
  have hDle : E.map L.subtype ≤ Subgroup.normalizer (T : Set G) ⊓ L :=
    (Subgroup.map_mono hEY).trans (le_of_eq hmapNorm)
  refine ⟨E.map L.subtype, ?_, ?_⟩
  · simpa [inf_comm] using hDle
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hEcard, hrel]

private theorem card_map_subgroupOf_eq_of_isL2Quot {L D : Subgroup G} [Finite ↥L] {n : ℕ}
    {H : Type*} [Group H] (α : ↥L →* H)
    (hαker : α.ker = (pCoreOf 2 L).subgroupOf L) (hDleL : D ≤ L)
    (hDcard : Nat.card D = 2 ^ n - 1) (hn : 1 ≤ n) :
    Nat.card ((D.subgroupOf L).map α) = 2 ^ n - 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup G := pCoreOf 2 L
  have hQleL : Q ≤ L := CFSG.openPCoreOf_le 2 L
  have hQp : IsPGroup 2 Q :=
    (CFSG.pCore_isPGroup (G := ↥L) (p := 2)).map L.subtype
  haveI : Finite ↥Q :=
    Finite.of_injective (Subgroup.inclusion hQleL) (Subgroup.inclusion_injective hQleL)
  have hoddSub : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two (by omega)) odd_one
  have hDQ : D ⊓ Q = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQp
    rw [hDcard, hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hoddSub)
  have hDinfker : D.subgroupOf L ⊓ α.ker = ⊥ := by
    rw [hαker]
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    have hx' : (x : G) ∈ D ⊓ Q := hx
    rw [hDQ, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  rw [CFSG.Walter.Suzuki.card_map_of_inf_ker_eq_bot α (D.subgroupOf L) hDinfker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleL).toEquiv, hDcard]

private theorem exists_image_sylow_torus_data {L T D : Subgroup G} [Finite ↥L] {n : ℕ}
    (hn : 1 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L)
    (hD : D ≤ L ⊓ Subgroup.normalizer (T : Set G)) (hDcard : Nat.card D = 2 ^ n - 1) :
    ∃ α : ↥L →* SL(2, GaloisField 2 n),
      Function.Surjective α ∧ α.ker = (pCoreOf 2 L).subgroupOf L ∧
      IsPGroup 2 ((T.subgroupOf L).map α) ∧
      ¬ 2 ∣ ((T.subgroupOf L).map α).index ∧
      (D.subgroupOf L).map α ≤
        Subgroup.normalizer (((T.subgroupOf L).map α :
          Subgroup (SL(2, GaloisField 2 n))) : Set (SL(2, GaloisField 2 n))) ∧
      Nat.card ((D.subgroupOf L).map α) = Nat.card (GaloisField 2 n) - 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 n
  let Q : Subgroup G := pCoreOf 2 L
  let S : Subgroup ↥L := T.subgroupOf L
  obtain ⟨α, hα, hαker'⟩ := exists_surjective_SL2_of_isL2Quot hq
  have hαker : α.ker = Q.subgroupOf L := by
    rw [hαker', CFSG.openPCoreOf_subgroupOf]
  have hQT : Q ≤ T := IsSylowTwoOf.pCoreOf_le hT
  have hQleL : Q ≤ L := CFSG.openPCoreOf_le 2 L
  have hDleL : D ≤ L := fun x hx => (Subgroup.mem_inf.mp (hD hx)).1
  have hDleT : D ≤ Subgroup.normalizer (T : Set G) :=
    fun x hx => (Subgroup.mem_inf.mp (hD hx)).2
  have hS2 : IsPGroup 2 S :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  have hSodd : ¬ 2 ∣ S.index := hT.2.2
  have hker_le : α.ker ≤ S := by
    rw [hαker]
    exact Subgroup.subgroupOf_mono L hQT
  have hPp : IsPGroup 2 (S.map α) := hS2.map α
  have hidx : ¬ 2 ∣ (S.map α).index := by
    rw [Subgroup.index_map_eq (H := S) hα hker_le]
    exact hSodd
  have hDsubN : D.subgroupOf L ≤ Subgroup.normalizer (S : Set ↥L) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hT.1]
    exact Subgroup.subgroupOf_mono L hDleT
  have hE_le : (D.subgroupOf L).map α ≤
      Subgroup.normalizer ((S.map α : Subgroup (SL(2, F))) : Set (SL(2, F))) :=
    (Subgroup.map_mono hDsubN).trans (Subgroup.le_normalizer_map α)
  have hFcard : Nat.card F = 2 ^ n := GaloisField.card 2 n (by omega)
  have hEcard : Nat.card ((D.subgroupOf L).map α) = Nat.card F - 1 := by
    rw [card_map_subgroupOf_eq_of_isL2Quot α hαker hDleL hDcard hn, hFcard]
  exact ⟨α, hα, hαker, hPp, hidx, hE_le, hEcard⟩

theorem exists_conj_SL2_of_isL2Quot {L T D : Subgroup G} [Finite ↥L] {n : ℕ}
    (hn : 1 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L)
    (hD : D ≤ L ⊓ Subgroup.normalizer (T : Set G)) (hDcard : Nat.card D = 2 ^ n - 1) :
    ∃ γ : ↥L →* SL(2, GaloisField 2 n),
      Function.Surjective γ ∧ γ.ker = (pCoreOf 2 L).subgroupOf L ∧
      (T.subgroupOf L).map γ = utri (GaloisField 2 n) ∧
      (D.subgroupOf L).map γ = torus (GaloisField 2 n) := by
  classical
  obtain ⟨α, hα, hαker, hPp, hidx, hE_le, hEcard⟩ :=
    exists_image_sylow_torus_data hn hq hT hD hDcard
  obtain ⟨g, hPg, hEg⟩ := exists_conj_sylow_torus hPp hidx hE_le hEcard
  let γ : ↥L →* SL(2, GaloisField 2 n) := (MulAut.conj g).toMonoidHom.comp α
  refine ⟨γ, (MulAut.conj g).surjective.comp hα, ?_, ?_, ?_⟩
  · rw [show γ = (MulAut.conj g).toMonoidHom.comp α from rfl,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective, hαker]
  · rw [show γ = (MulAut.conj g).toMonoidHom.comp α from rfl, ← Subgroup.map_map, hPg]
  · rw [show γ = (MulAut.conj g).toMonoidHom.comp α from rfl, ← Subgroup.map_map, hEg]

private theorem conjModPCore_eq_one_of_exists_torus_conj {L D : Subgroup G} [Finite ↥L]
    (hDleL : D ≤ L) (hoddD : Odd (Nat.card D)) {c : G} (hc2 : ∃ m, c ^ (2 ^ m) = 1)
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) (hcD : ∀ d ∈ D, c * d = d * c)
    (ht : ∃ t ∈ D, ∀ l ∈ L, (t⁻¹ * c) * l * (t⁻¹ * c)⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    CFSG.GroupTheory.conjModPCore 2 L (Subgroup.normalizer (L : Set G)) le_rfl
      ⟨c, hcL⟩ = 1 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  obtain ⟨t, htD, ht⟩ := ht
  have htN : t ∈ N := Subgroup.le_normalizer (hDleL htD)
  have hhN : t⁻¹ * c ∈ N := N.mul_mem (N.inv_mem htN) hcL
  let φ : ↥N →* MulAut (oTwoQuot ↥L) := CFSG.GroupTheory.conjModPCore 2 L N le_rfl
  have hhmem : t⁻¹ * c ∈ (φ.ker).map N.subtype := by
    rw [CFSG.GroupTheory.mem_map_ker_conjModPCore_iff]
    exact ⟨hhN, fun x hx => ht x hx⟩
  have hhker : (⟨t⁻¹ * c, hhN⟩ : ↥N) ∈ φ.ker := by
    rw [← Subgroup.mem_map_iff_mem (f := N.subtype) (Subgroup.subtype_injective N)]
    exact hhmem
  have hh_eq : (⟨t⁻¹ * c, hhN⟩ : ↥N) = (⟨t, htN⟩ : ↥N)⁻¹ * ⟨c, hcL⟩ := by
    apply Subtype.ext
    rfl
  have hφeq : φ ⟨c, hcL⟩ = φ ⟨t, htN⟩ := by
    have hhker' : φ ⟨t⁻¹ * c, hhN⟩ = 1 := MonoidHom.mem_ker.mp hhker
    have h := congrArg φ hh_eq
    simp only [hhker', map_mul, map_inv, map_one] at h
    have h' : φ ⟨t, htN⟩ = φ ⟨c, hcL⟩ := by
      calc φ ⟨t, htN⟩ = φ ⟨t, htN⟩ * 1 := (mul_one _).symm
        _ = φ ⟨t, htN⟩ * ((φ ⟨t, htN⟩)⁻¹ * φ ⟨c, hcL⟩) := by rw [← h]
        _ = φ ⟨c, hcL⟩ := by group
    exact h'.symm
  obtain ⟨m, hm⟩ := hc2
  have hφc_pow : φ ⟨c, hcL⟩ ^ (2 ^ m) = 1 := by
    rw [← map_pow]
    have hpow : (⟨c, hcL⟩ : ↥N) ^ (2 ^ m) = 1 := by
      apply Subtype.ext
      simpa using hm
    rw [hpow, map_one]
  have hdivc : orderOf (φ ⟨c, hcL⟩) ∣ 2 ^ m :=
    orderOf_dvd_iff_pow_eq_one.mpr hφc_pow
  have hdivt0 : orderOf (φ ⟨t, htN⟩) ∣ orderOf (⟨t, htN⟩ : ↥N) :=
    orderOf_map_dvd φ _
  have hdivt : orderOf (φ ⟨t, htN⟩) ∣ orderOf t := by
    rwa [← Subgroup.orderOf_coe (⟨t, htN⟩ : ↥N)] at hdivt0
  have hodd_t : Odd (orderOf t) := by
    have hdvd : orderOf t ∣ Nat.card D := by
      have h := orderOf_dvd_natCard (⟨t, htD⟩ : ↥D)
      rwa [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat hoddD hdvd
  have hcop : Nat.Coprime (2 ^ m) (orderOf t) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd_t)
  have hdivc' : orderOf (φ ⟨t, htN⟩) ∣ 2 ^ m := by
    rw [← hφeq]
    exact hdivc
  have horder_one : orderOf (φ ⟨t, htN⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdivc' hdivt
  have hφt_one : φ ⟨t, htN⟩ = 1 := orderOf_eq_one_iff.mp horder_one
  have hφc_one : φ ⟨c, hcL⟩ = 1 := by rw [hφeq, hφt_one]
  simpa [φ, N] using hφc_one

private theorem commutator_mem_pCoreOf_of_conjModPCore_eq_one {L : Subgroup G} {c : G}
    (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hφc_one : CFSG.GroupTheory.conjModPCore 2 L (Subgroup.normalizer (L : Set G)) le_rfl
      ⟨c, hcL⟩ = 1) :
    ∀ l ∈ L, ⁅c, l⁆ ∈ pCoreOf 2 L := by
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let φ : ↥N →* MulAut (oTwoQuot ↥L) := CFSG.GroupTheory.conjModPCore 2 L N le_rfl
  have hcN : c ∈ N := hcL
  have hφc_one' : φ ⟨c, hcL⟩ = 1 := by simpa [φ, N] using hφc_one
  have hcker' : (⟨c, hcL⟩ : ↥N) ∈ φ.ker := MonoidHom.mem_ker.mpr hφc_one'
  have hcker : c ∈ (φ.ker).map N.subtype := by
    simpa using Subgroup.mem_map_of_mem N.subtype hcker'
  have hcomm := (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 L N le_rfl).mp hcker
  intro l hl
  simpa [commutatorElement_def] using hcomm.2 l hl

private theorem commutator_mem_pCoreOf_of_exists_torus_conj {L D : Subgroup G} [Finite ↥L]
    (hDleL : D ≤ L) (hoddD : Odd (Nat.card D)) {c : G} (hc2 : ∃ m, c ^ (2 ^ m) = 1)
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) (hcD : ∀ d ∈ D, c * d = d * c)
    (ht : ∃ t ∈ D, ∀ l ∈ L, (t⁻¹ * c) * l * (t⁻¹ * c)⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    ∀ l ∈ L, ⁅c, l⁆ ∈ pCoreOf 2 L :=
  commutator_mem_pCoreOf_of_conjModPCore_eq_one hcL
    (conjModPCore_eq_one_of_exists_torus_conj hDleL hoddD hc2 hcL hcD ht)

theorem commutator_mem_pCoreOf_of_centralizes_torus {L T D : Subgroup G} [Finite ↥L] {n : ℕ}
    (hn : 2 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L)
    (hD : D ≤ L ⊓ Subgroup.normalizer (T : Set G)) (hDcard : Nat.card D = 2 ^ n - 1)
    {c : G} (hc2 : ∃ m, c ^ (2 ^ m) = 1) (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hcT : c ∈ Subgroup.normalizer (T : Set G)) (hcD : ∀ d ∈ D, c * d = d * c) :
    ∀ l ∈ L, ⁅c, l⁆ ∈ pCoreOf 2 L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 n
  obtain ⟨γ, hγsurj, hγker, hSγ, hDγ⟩ :=
    exists_conj_SL2_of_isL2Quot (by omega : 1 ≤ n) hq hT hD hDcard
  have hDleL : D ≤ L := fun x hx => (Subgroup.mem_inf.mp (hD hx)).1
  have hFcard : Nat.card F = 2 ^ n := GaloisField.card 2 n (by omega)
  have hFbig : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcQ : c ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hcL
  have hcTfix : ∀ t ∈ D, c * t * c⁻¹ = t := by
    intro t ht
    have hcomm : c * t = t * c := hcD t ht
    rw [hcomm]
    group
  obtain ⟨t, htD, ht⟩ :=
    exists_mem_torus_conj_mem_of_normalizes (F := F) hFbig (L := L) (Q := pCoreOf 2 L)
      (U' := T) (T' := D) γ hγsurj hγker hSγ hDleL hDγ hcL hcQ hcT hcTfix
  have hoddD : Odd (Nat.card D) := by
    rw [hDcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two (by omega)) odd_one
  exact commutator_mem_pCoreOf_of_exists_torus_conj hDleL hoddD hc2 hcL hcD ⟨t, htD, ht⟩

end CFSG.Quasithin.F112R.St84
