module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch10SecQ3CQ
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Bar
public import CFSG.Quasithin.Vol2.Ch9Sec3FFBList

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Vol2.Ch10.SecB.C11AmS
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

section Psi

variable {Y KY U : Subgroup G}

theorem ker_barMap_le (hKYY : KY ≤ Y) (hred : IsTwoReducedIn Y U) :
    (barMap hKYY).ker ≤ (InternalSec.autOnHom (hKYY.trans hred.2.1)).ker := by
  intro k hk
  have hO2 : pCoreOf 2 (autOn Y U) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have h1 := InternalSec.pCore_le_ker_autOnHom hred.2.1 hO2
  have hx : Subgroup.inclusion hKYY k ∈ CFSG.pCore 2 ↥Y := by
    have h0 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (Subgroup.inclusion hKYY k) = 1 :=
      congrArg Subtype.val hk
    exact (QuotientGroup.eq_one_iff _).1 h0
  exact (InternalSec.mem_ker_autOnHom _ _).2 ((InternalSec.mem_ker_autOnHom hred.2.1 _).1 (h1 hx))

@[expose] noncomputable def psi (hKYY : KY ≤ Y) (hred : IsTwoReducedIn Y U) :
    ↥(modO2Image Y KY) →* ↥(autOn KY U) :=
  (QuotientGroup.lift (barMap hKYY).ker (InternalSec.autOnHom (hKYY.trans hred.2.1))
    (ker_barMap_le hKYY hred)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _ (barMap_surjective hKYY)).symm.toMonoidHom

theorem psi_barMap (hKYY : KY ≤ Y) (hred : IsTwoReducedIn Y U) (k : ↥KY) :
    psi hKYY hred (barMap hKYY k) = InternalSec.autOnHom (hKYY.trans hred.2.1) k := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective _ (barMap_surjective hKYY)).symm
      (barMap hKYY k) = (k : ↥KY ⧸ (barMap hKYY).ker) := by
    apply (QuotientGroup.quotientKerEquivOfSurjective _ (barMap_surjective hKYY)).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  simp only [psi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]

theorem psi_surjective (hKYY : KY ≤ Y) (hred : IsTwoReducedIn Y U) :
    Function.Surjective (psi hKYY hred) := by
  intro x
  obtain ⟨k, rfl⟩ := InternalSec.autOnHom_surjective (hKYY.trans hred.2.1) x
  exact ⟨barMap hKYY k, psi_barMap hKYY hred k⟩

theorem oddCore_characteristic' (X : Type*) [Group X] [Finite X] :
    (CFSG.oddCore X).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨hN.1.map φ.toMonoidHom φ.surjective, ?_⟩
  rw [Subgroup.card_map_of_injective φ.injective]
  exact hN.2

@[expose] noncomputable def rStar (hKYY : KY ≤ Y) (hred : IsTwoReducedIn Y U) :
    Subgroup (MulAut ↥U) :=
  ((CFSG.oddCore ↥(modO2Image Y KY)).map (psi hKYY hred)).map (autOn KY U).subtype

theorem rStar_subgroupOf (hKYY : KY ≤ Y) (hred : IsTwoReducedIn Y U) :
    (rStar hKYY hred).subgroupOf (autOn KY U) =
      (CFSG.oddCore ↥(modO2Image Y KY)).map (psi hKYY hred) :=
  Subgroup.comap_map_eq_self_of_injective (autOn KY U).subtype_injective _

theorem card_rStar_dvd (hKYY : KY ≤ Y) (hred : IsTwoReducedIn Y U) :
    Nat.card ↥(rStar hKYY hred) ∣ Nat.card ↥(CFSG.oddCore ↥(modO2Image Y KY)) := by
  rw [rStar, Subgroup.card_map_of_injective (autOn KY U).subtype_injective]
  exact Subgroup.card_map_dvd _ _

theorem isNilpotent_rStar (hKYY : KY ≤ Y) (hred : IsTwoReducedIn Y U)
    (hO : Group.IsNilpotent ↥(CFSG.oddCore ↥(modO2Image Y KY))) :
    Group.IsNilpotent ↥(rStar hKYY hred) := by
  set H := CFSG.oddCore ↥(modO2Image Y KY)
  have h1 : Group.IsNilpotent ↥(H.map (psi hKYY hred)) :=
    Group.nilpotent_of_surjective _ ((psi hKYY hred).subgroupMap_surjective H)
  set e := (H.map (psi hKYY hred)).equivMapOfInjective _ (autOn KY U).subtype_injective
  exact Group.nilpotent_of_surjective e.toMonoidHom e.surjective

theorem le_normalizer_rStar [Finite G] (hKYY : KY ≤ Y) (hred : IsTwoReducedIn Y U)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) :
    autOn Y U ≤ Subgroup.normalizer (rStar hKYY hred : Set (MulAut ↥U)) := by
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hred.2.1
  have hnorm : (KY.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKYY).mpr hYKY
  have hKYn : (modO2Image Y KY).Normal :=
    hnorm.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) (QuotientGroup.mk'_surjective _)
  have hchar := oddCore_characteristic' ↥(modO2Image Y KY)
  have key : ∀ x ∈ autOn Y U, ∀ r ∈ rStar hKYY hred, x * r * x⁻¹ ∈ rStar hKYY hred := by
    intro x hx r hr
    obtain ⟨g, hgY, rfl⟩ := Setup.mem_autOn_iff.1 hx
    obtain ⟨s, ⟨o, ho, rfl⟩, rfl⟩ := hr
    obtain ⟨k, rfl⟩ := barMap_surjective hKYY o
    have hgk : (g : G) * k * (g : G)⁻¹ ∈ KY := (Subgroup.mem_normalizer_iff.mp (hYKY hgY) k).mp k.2
    set k' : ↥KY := ⟨_, hgk⟩ with hk'
    set gb : ↥Y ⧸ CFSG.pCore 2 ↥Y := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨g, hgY⟩ with hgb
    have hbar : barMap hKYY k' = MulAut.conjNormal gb (barMap hKYY k) := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      show QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (Subgroup.inclusion hKYY k') =
        gb * QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (Subgroup.inclusion hKYY k) * gb⁻¹
      rw [hgb, ← map_mul, ← map_inv, ← map_mul]
      congr 1
    have hmem : barMap hKYY k' ∈ CFSG.oddCore ↥(modO2Image Y KY) := by
      rw [hbar]
      exact (Subgroup.characteristic_iff_le_comap.mp hchar (MulAut.conjNormal gb)) ho
    refine ⟨psi hKYY hred (barMap hKYY k'), ⟨_, hmem, rfl⟩, ?_⟩
    rw [psi_barMap, psi_barMap]
    show conjAct U (Subgroup.inclusion hKYN k') =
      conjAct U g * conjAct U (Subgroup.inclusion hKYN k) * (conjAct U g)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext rfl)
  exact le_normalizer_of_conj key

end Psi

section Thompson

variable [Finite G]

theorem commutator_le_centralizer_of_ffJ {S L Y W : Subgroup G} [IsMulCommutative ↥W]
    (hWe : IsElemAbelian 2 W) (hred : IsTwoReducedIn Y W) (hSY : IsSylowTwoOf S Y) (hLY : L ≤ Y)
    (h : ⁅autOn L W, ffJ (autOn Y W)⁆ = ⊥) :
    ⁅L, thompsonJ S⁆ ≤ Subgroup.centralizer (W : Set G) := by
  have hTW : S ≤ Subgroup.normalizer (W : Set G) := hSY.1.trans hred.2.1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  have hbot : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      autOn A W ≤ Subgroup.centralizer (autOn L W : Set (MulAut ↥W)) := by
    intro A hA
    by_cases hAC : A ≤ Subgroup.centralizer (W : Set G)
    · have h0 : autOn A W = ⊥ := autI_eq_bot_of_le_centralizer hWe hAC
      rw [h0]
      exact bot_le
    · have hoff : IsFFOffender Y W A := ⟨isMaxElemAbelian_of_isSylowTwoOf hSY hA, hAC⟩
      have hle : autOn A W ≤ ffJ (autOn Y W) :=
        B6.le_ffJ (offenderImages_isFFStarOffender hWe hred.1 hred.2.1 ⟨A, hoff, rfl⟩)
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.mp (h hk) x (hle hx)).symm
  set S' : Subgroup G :=
    ((Subgroup.centralizer (autOn L W : Set (MulAut ↥W))).comap (conjAct W)).map
      (Subgroup.normalizer (W : Set G)).subtype with hS'
  have hJS' : thompsonJ S ≤ S' := by
    refine iSup₂_le fun A hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (W : Set G) := hTW (hA.1 ha)
    exact ⟨⟨a, haN⟩, hbot A hA (Setup.mem_autOn_iff.2 ⟨⟨a, haN⟩, ha, rfl⟩), rfl⟩
  rw [Subgroup.commutator_le]
  intro k hk j hj
  obtain ⟨g, hg, rfl⟩ := hJS' hj
  have hkN : k ∈ Subgroup.normalizer (W : Set G) := hred.2.1 (hLY hk)
  have hkA : conjAct W ⟨k, hkN⟩ ∈ autOn L W := Setup.mem_autOn_iff.2 ⟨⟨k, hkN⟩, hk, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hg) _ hkA
  have h1 : conjAct W ⁅(⟨k, hkN⟩ : Subgroup.normalizer (W : Set G)), g⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc
  exact A4.conjAct_eq_one_iff.mp h1

end Thompson

section List

theorem le_seven_of_dvd {p a b c d : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
    p ≤ 7 := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)).trans (by norm_num)
      · exact (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)).trans (by norm_num)
    · exact (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)).trans (by norm_num)
  · exact Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)

theorem false_of_b56_prime {X : Type} [Group X] [Finite X] (h : B56QuasisimpleList X)
    (hq : CFSG.IsQuasisimple X) (h60 : 60 ∣ Nat.card X) (h16 : ¬ 16 ∣ Nat.card X) {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) (hpX : p ∣ Nat.card X) : False := by
  have h16' : ∀ n, 4 ≤ n → ∀ m, Nat.card X = 2 ^ n * m → False := fun n hn m hm =>
    h16 (hm ▸ Dvd.dvd.mul_right ((show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 hn) m)
  have hle : ∀ a b c d, Nat.card X = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d → False := fun a b c d h =>
    absurd (le_seven_of_dvd hp (h ▸ hpX)) (by omega)
  rcases FFB.b56_card_cases h hq h60 with ⟨n, hn, hc⟩ | ⟨n, hn, hc⟩ | ⟨n, hn, hc⟩ |
    ⟨n, hn, hc⟩ | hc | he | hc | he4 | hc
  · rcases Nat.lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · exact hle 1 1 0 0 (by rw [hc]; norm_num)
      · exact hle 2 1 1 0 (by rw [hc]; norm_num)
      · exact hle 3 2 0 1 (by rw [hc]; norm_num)
    · exact h16' n h4 _ hc
  · rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n
      exact hle 3 1 0 1 (by rw [hc]; norm_num)
    · exact h16' (3 * n) (by omega) _ hc
  · exact h16' (4 * n) (by omega) _ hc
  · exact h16' (6 * n) (by omega) _ hc
  · exact hle 3 2 1 0 (by rw [hc]; norm_num)
  · obtain ⟨e⟩ := he
    exact hle 3 2 1 1 (by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7 (by norm_num)]
      decide)
  · exact hle 3 3 1 0 (by rw [hc]; norm_num)
  · obtain ⟨e⟩ := he4
    exact h16' 6 (by norm_num) 315 (by
      rw [Nat.card_congr e.toEquiv, card_statedSL_four_zmod1527d]
      norm_num)
  · exact h16' 10 (by norm_num) _ hc

end List

end CFSG.Quasithin.H13.Ch9.KGFF
