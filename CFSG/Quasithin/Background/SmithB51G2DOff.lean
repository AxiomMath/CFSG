module

public import CFSG.Quasithin.Background.SmithB51G2DExcl
public import CFSG.Quasithin.Background.SmithB51P5Basic
public import CFSG.Quasithin.Background.B5Irr
public import CFSG.Quasithin.Background.B5P4Num

public section

namespace CFSG.Quasithin.B5.G2D

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem card_comap_of_surjective {G H : Type*} [Group G] [Group H] [Finite G] {ψ : G →* H}
    (hψ : Function.Surjective ψ) (F : Subgroup H) :
    Nat.card (F.comap ψ) = Nat.card ψ.ker * Nat.card F := by
  have h1 := B1More.card_map_mul_card_inf_ker (F.comap ψ) ψ
  rw [Subgroup.map_comap_eq_self_of_surjective hψ,
    inf_eq_right.2 (Subgroup.ker_le_comap ψ F)] at h1
  rw [← h1, mul_comm]

variable {V : Type} [CommGroup V]

theorem ffJ_le (X : Subgroup (MulAut V)) : ffJ X ≤ X :=
  iSup₂_le fun _ hA => hA.1

theorem exists_sylow_le [Finite V] {G A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hA : IsPGroup 2 A) : ∃ T, IsSylowTwoOf T G ∧ A ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA' : IsPGroup 2 (A.subgroupOf G) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAG).symm
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥G).map G.subtype, ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩,
    fun a ha => ⟨⟨a, hAG ha⟩, hQ ha, rfl⟩⟩
  have : ((Q : Subgroup ↥G).map G.subtype).subgroupOf G = (Q : Subgroup ↥G) :=
    Subgroup.comap_map_eq_self_of_injective G.subtype_injective _
  rw [this]
  exact Q.not_dvd_index

@[expose] def fixMod (A : Subgroup (MulAut V)) (U C : Subgroup V) : Subgroup V where
  carrier := {u | u ∈ U ∧ ∀ a ∈ A, a u * u⁻¹ ∈ C}
  mul_mem' := fun {u w} hu hw => ⟨U.mul_mem hu.1 hw.1, fun a ha => by
    have : a (u * w) * (u * w)⁻¹ = (a u * u⁻¹) * (a w * w⁻¹) := by
      rw [map_mul, mul_inv, mul_mul_mul_comm]
    rw [this]
    exact C.mul_mem (hu.2 a ha) (hw.2 a ha)⟩
  one_mem' := ⟨U.one_mem, fun a _ => by simp [C.one_mem]⟩
  inv_mem' := fun {u} hu => ⟨U.inv_mem hu.1, fun a ha => by
    have : a u⁻¹ * u⁻¹⁻¹ = (a u * u⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv, inv_inv, mul_comm]
    rw [this]
    exact C.inv_mem (hu.2 a ha)⟩

variable [Finite V]

theorem card_fixMod {M A : Subgroup (MulAut V)} {U C : Subgroup V} (hCU : C ≤ U)
    (hMU : M ≤ stabSub U) (hMC : M ≤ stabSub C) (hAM : A ≤ M) :
    Nat.card (fixMod A U C) = Nat.card C * Nat.card (fixV (autSec A U C)) := by
  set qU : ↥U →* Sec U C := QuotientGroup.mk' (C.subgroupOf U) with hqU
  have hqs : Function.Surjective qU := QuotientGroup.mk'_surjective _
  have hker : Nat.card qU.ker = Nat.card C := by
    rw [hqU, QuotientGroup.ker_mk']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCU).toEquiv
  have hmap := map_secHom_eq_autSec M hMU hMC hAM
  have key : ∀ u : ↥U, qU u ∈ fixV (autSec A U C) ↔ ∀ a ∈ A, a (u : V) * (u : V)⁻¹ ∈ C := by
    intro u
    have hact : ∀ a (ha : a ∈ A), (qU ⟨a u, (hMU (hAM ha) u).2 u.2⟩ = qU u ↔
        a (u : V) * (u : V)⁻¹ ∈ C) := by
      intro a ha
      rw [hqU, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        have h2 := C.inv_mem h1
        simpa [mul_comm] using h2
      · intro h1
        have h2 := C.inv_mem h1
        simpa [mul_comm] using h2
    constructor
    · intro hu a ha
      have h1 : secHom M hMU hMC ⟨a, hAM ha⟩ ∈ autSec A U C := by
        rw [← hmap]
        exact ⟨⟨a, hAM ha⟩, ha, rfl⟩
      have h2 := hu _ h1
      rw [hqU, QuotientGroup.mk'_apply, secHom_mk] at h2
      exact (hact a ha).1 h2
    · intro hu φ hφ
      rw [← hmap] at hφ
      obtain ⟨g, hg, rfl⟩ := hφ
      rw [hqU, QuotientGroup.mk'_apply, secHom_mk]
      exact (hact g hg).2 (hu g hg)
  have heq : fixMod A U C = ((fixV (autSec A U C)).comap qU).map U.subtype := by
    ext v
    constructor
    · rintro ⟨hvU, hv⟩
      exact ⟨⟨v, hvU⟩, (key ⟨v, hvU⟩).2 hv, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, (key u).1 hu⟩
  rw [heq, Subgroup.card_map_of_injective U.subtype_injective, card_comap_of_surjective hqs, hker]

omit [CommGroup V] [Finite V] in
theorem card_mul_card_fixV_le_of_q_one {S : Type} [CommGroup S] [Finite S]
    (hS : ∀ s : S, s ^ 2 = 1) {X B : Subgroup (MulAut S)} (hB : IsFFStarOffender X B)
    (hq : qOf X = ((1 : ℚ) : WithTop ℚ)) : Nat.card B * Nat.card (fixV B) ≤ Nat.card S := by
  have h1 := qOf_le_rAV_of_offender hS hB
  rw [hq, WithTop.coe_le_coe] at h1
  have hbpos : 0 < rk B := hB.isA2.rk_pos
  unfold rAV at h1
  rw [le_div_iff₀ (by exact_mod_cast hbpos), one_mul] at h1
  have h2 : rk B ≤ rkIdx (fixV B) := by exact_mod_cast h1
  have h3 := rk_add_rkIdx (fixV B)
  rw [card_eq_two_pow_of_isPGroup hB.2.2.1.isPGroup, card_eq_two_pow hS, ← pow_add,
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hS)]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

variable {G L : Subgroup (MulAut V)}

@[expose] def G2Orders (L : Subgroup (MulAut V)) (n : ℕ) : Prop :=
  (n = 1 ∧ Nat.card L = 6048) ∨
    (2 ≤ n ∧ Nat.card L = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)))

theorem sylow_facts (hIdent : AsB42Ident) (h42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤) {n : ℕ} (hn : 1 ≤ n)
    (hcardS : Nat.card (Sec (commV L) (fixV L ⊓ commV L)) = (2 ^ n) ^ 6) (hL : G2Orders L n)
    {T : Subgroup (MulAut V)} (hT : IsSylowTwoOf T G) :
    qOf (autSec (L ⊔ T) (commV L) (fixV L ⊓ commV L)) = ((1 : ℚ) : WithTop ℚ) ∧
      (∀ B, IsFFStarOffender (autSec (L ⊔ T) (commV L) (fixV L ⊓ commV L)) B →
        Nat.card B = 2 ^ (3 * n)) ∧
      G2Natural (ffJ (autSec (L ⊔ T) (commV L) (fixV L ⊓ commV L))) ⊤ ⊥ n := by
  have hHyp := b4Hyp_section' hV h hU hT.1 hT.2.1 (C := fixV L ⊓ commV L) rfl
  obtain ⟨hUC, -, hGU, hGC, hfL, -⟩ := secConfig hV h hU hT (C := fixV L ⊓ commV L) rfl
  have hLG := le_G h
  have hΛ : Nat.card (autSec L (commV L) (fixV L ⊓ commV L)) = Nat.card L :=
    (Nat.card_congr (secEquiv L (hLG.trans hGU) (hLG.trans hGC) hfL).toEquiv).symm
  have hS2 := sq_eq_one_sec hV (commV L) (fixV L ⊓ commV L)
  have hΛ' : (n = 1 ∧ Nat.card (autSec L (commV L) (fixV L ⊓ commV L)) = 6048) ∨
      (2 ≤ n ∧ Nat.card (autSec L (commV L) (fixV L ⊓ commV L)) =
        (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1))) := by
    rw [hΛ]
    exact hL
  have hcase : ∀ B, IsFFStarOffender (autSec (L ⊔ T) (commV L) (fixV L ⊓ commV L)) B →
      qOf (autSec (L ⊔ T) (commV L) (fixV L ⊓ commV L)) = ((1 : ℚ) : WithTop ℚ) ∧
        Nat.card B = 2 ^ (3 * n) ∧
        G2Natural (ffJ (autSec (L ⊔ T) (commV L) (fixV L ⊓ commV L))) ⊤ ⊥ n := fun B hB =>
    case4_of_b42 hIdent hS2 hHyp hB (h42 _ hS2 _ _ hHyp B hB) hn hcardS hΛ'
  obtain ⟨-, -, -, B₀, -, hB₀⟩ := exists_section_offender' hV h hU hT (C := fixV L ⊓ commV L) rfl
  obtain ⟨hq, -, hJ⟩ := hcase B₀ hB₀
  exact ⟨hq, fun B hB => (hcase B hB).2.1, hJ⟩

theorem offender_sec (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤)
    {T : Subgroup (MulAut V)} (hT : IsSylowTwoOf T G)
    (hq : qOf (autSec (L ⊔ T) (commV L) (fixV L ⊓ commV L)) = ((1 : ℚ) : WithTop ℚ))
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) (hAT : A ≤ T) :
    IsFFStarOffender (autSec (L ⊔ T) (commV L) (fixV L ⊓ commV L))
      (autSec A (commV L) (fixV L ⊓ commV L)) := by
  set C := fixV L ⊓ commV L with hC
  obtain ⟨hUC, -, hGU, hGC, -, -⟩ := secConfig hV h hU hT hC
  have hMG : L ⊔ T ≤ G := sup_le (le_G h) hT.1
  have hAM' : IsFFStarOffender (L ⊔ T) A :=
    ⟨hAT.trans le_sup_right, hA.2.1, hA.2.2.1, hA.2.2.2⟩
  obtain ⟨-, hcomm, hlt, -⟩ := irr_data hU
  have hS : ¬ commSub (commV L) (quasithinGenFitting (L ⊔ T)) ≤ C := by
    rw [genFitting_sup_eq h hT.1 hT.2.1, hcomm]
    intro hle
    have h1 : C = commV L := le_antisymm inf_le_right hle
    rw [hC, inf_comm] at h1
    rw [h1] at hlt
    exact lt_irrefl _ hlt
  have hqs : CFSG.IsQuasisimple ↥(quasithinGenFitting (L ⊔ T)) := by
    rw [genFitting_sup_eq h hT.1 hT.2.1]
    exact quasi_L h
  obtain ⟨-, -, hq1⟩ := B1_5_8 hV hAM' (W := commV L) (U := C) hUC (hMG.trans hGU)
    (hMG.trans hGC) hqs (pCoreOf_sup_eq_bot h hT.1 hT.2.1) hS
  exact (hq1 hq).1

theorem offender_facts (hIdent : AsB42Ident) (h42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤) {n : ℕ} (hn : 1 ≤ n)
    (hcardS : Nat.card (Sec (commV L) (fixV L ⊓ commV L)) = (2 ^ n) ^ 6) (hL : G2Orders L n)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) :
    commV L ⊔ fixV A = ⊤ ∧ Nat.card A = 2 ^ (3 * n) ∧
      fixMod A (commV L) (fixV L ⊓ commV L) = commV L ⊓ fixV A ∧
      Nat.card (fixMod A (commV L) (fixV L ⊓ commV L)) =
        Nat.card ↥(fixV L ⊓ commV L) * 2 ^ (3 * n) := by
  set C := fixV L ⊓ commV L with hC
  obtain ⟨T, hT, hAT⟩ := exists_sylow_le hA.1 hA.2.2.1.isPGroup
  obtain ⟨hUC, -, hGU, hGC, -, hfM⟩ := secConfig hV h hU hT hC
  obtain ⟨hq, hcard, -⟩ := sylow_facts hIdent h42 hV h hU hn hcardS hL hT
  have hLG := le_G h
  have hMG : L ⊔ T ≤ G := sup_le hLG hT.1
  have hMU : L ⊔ T ≤ stabSub (commV L) := hMG.trans hGU
  have hMC : L ⊔ T ≤ stabSub C := hMG.trans hGC
  have hAM : A ≤ L ⊔ T := hAT.trans le_sup_right
  have hAM' : IsFFStarOffender (L ⊔ T) A := ⟨hAM, hA.2.1, hA.2.2.1, hA.2.2.2⟩
  have hoff := offender_sec hV h hU hT hq hA hAT
  have hcardB := hcard _ hoff
  have hcardA : Nat.card A = Nat.card (autSec A (commV L) C) := by
    rw [← map_secHom_eq_autSec (L ⊔ T) hMU hMC hAM,
      Subgroup.card_map_of_injective ((MonoidHom.ker_eq_bot_iff _).1
        (ker_secHom_eq_bot (L ⊔ T) hMU hMC hfM))]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv.symm
  have hBF := card_mul_card_fixV_le_of_q_one (sq_eq_one_sec hV (commV L) C) hoff hq
  have hY := card_fixMod hUC hMU hMC hAM
  have hUcard : Nat.card (commV L) = Nat.card (Sec (commV L) C) * Nat.card C := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf (commV L))]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv
  have hle : commV L ⊓ fixV A ≤ fixMod A (commV L) C := by
    intro u hu
    refine ⟨hu.1, fun a ha => ?_⟩
    rw [hu.2 a ha, mul_inv_cancel]
    exact C.one_mem
  have hcardle : Nat.card ↥(commV L ⊓ fixV A) ≤ Nat.card (fixMod A (commV L) C) :=
    Subgroup.card_le_of_le hle
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hkey : Nat.card A * Nat.card (fixMod A (commV L) C) ≤ Nat.card (commV L) := by
    rw [hY, hUcard, hcardA]
    calc Nat.card (autSec A (commV L) C) * (Nat.card C * Nat.card (fixV (autSec A (commV L) C)))
        = Nat.card C * (Nat.card (autSec A (commV L) C) *
          Nat.card (fixV (autSec A (commV L) C))) := by ring
      _ ≤ Nat.card C * Nat.card (Sec (commV L) C) := Nat.mul_le_mul_left _ hBF
      _ = _ := by ring
  obtain ⟨hsup, heq⟩ := P5.sup_fixV_eq_top_of_card_le hA (U := commV L)
    ((Nat.mul_le_mul_left _ hcardle).trans hkey)
  have hge : Nat.card (fixMod A (commV L) C) ≤ Nat.card ↥(commV L ⊓ fixV A) := by
    rw [← heq] at hkey
    exact Nat.le_of_mul_le_mul_left hkey hApos
  have hfixeq : fixMod A (commV L) C = commV L ⊓ fixV A :=
    (Subgroup.eq_of_le_of_card_ge hle hge).symm
  refine ⟨hsup, by rw [hcardA, hcardB], hfixeq, ?_⟩
  rw [hfixeq]
  have h1 : Nat.card A * Nat.card ↥(commV L ⊓ fixV A) =
      Nat.card A * (Nat.card C * 2 ^ (3 * n)) := by
    rw [heq, hUcard, hcardS, hcardA, hcardB]
    ring
  exact Nat.eq_of_mul_eq_mul_left hApos h1

end CFSG.Quasithin.B5.G2D
