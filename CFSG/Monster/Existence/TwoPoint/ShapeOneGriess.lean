module

public import CFSG.Monster.Existence.TwoPoint.ShapeOne
public import CFSG.Monster.Existence.TwoPoint.StdE6Model
public import CFSG.Monster.Existence.AssemblyHS
import all CFSG.Monster.Existence.TwoA

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.LieType.Chevalley.C2E6Std

theorem centToDA_eq_one_iff (c : cent tGriess) :
    centToDA c = 1 ↔ (c : MGriess) = 1 ∨ (c : MGriess) = tGriess := by
  have h1 : centToDA c = piA (centTEquiv c) := rfl
  rw [h1, piA_eq_one_iff]
  constructor
  · rintro (h | h)
    · left
      have h2 : c = 1 := centTEquiv.injective (h.trans (map_one centTEquiv).symm)
      rw [h2]
      rfl
    · right
      rw [← centTEquiv_self] at h
      rw [centTEquiv.injective h]
  · rintro (h | h)
    · left
      rw [show c = 1 from Subtype.ext h, map_one]
    · right
      rw [show c = ⟨tGriess, self_mem_cent tGriess⟩ from Subtype.ext h, centTEquiv_self]

theorem uGriess_mul_tGriess : uGriess * tGriess = tGriess * uGriess :=
  tGriess_mul_uGriess.symm

theorem centToDA_uIn : centToDA (uIn uGriess_mul_tGriess) = uHatA := by
  rw [uHatA_eq]
  show piA (centTEquiv _) = piA uA
  congr 1

theorem tGriess_ne_one : tGriess ≠ 1 := by
  intro h
  have := orderOf_tGriess
  rw [h, orderOf_one] at this
  norm_num at this

theorem uGriess_ne_one : uGriess ≠ 1 := by
  intro h
  have h2 : rhoEquiv rTwo = rhoEquiv 1 :=
    (congrArg Subtype.val h).trans Short.rhoEquiv_one.symm
  exact ne_one_of_isShortCoord isShortCoord_rTwo (rhoEquiv_injective h2)

theorem uGriess_ne_tGriess : uGriess ≠ tGriess := by
  intro h
  have h2 : uStar = tStar := congrArg Subtype.val h
  have h3 : rhoEquiv rOneTwo = rhoEquiv 1 := by
    rw [← uStar_mul_tStar, h2, Short.rhoEquiv_one]
    exact rhoEquiv_mul_self_DQ (deltaPair 0 1)
  exact ne_one_of_isShortCoord isShortCoord_rOneTwo (rhoEquiv_injective h3)

noncomputable def centUHatEquivBar :
    ↥(Subgroup.centralizer ({uHatA} : Set DA)) ≃* ↥(Subgroup.centralizer ({uBar} : Set Cbar)) :=
  centralizerUHatEquiv mem_Cgen_of_conj_uA_uncond

variable (K : Subgroup ↥(Subgroup.centralizer ({uBar} : Set Cbar)))

@[expose] noncomputable def kDA :
    Subgroup DA :=
  (K.map centUHatEquivBar.symm.toMonoidHom).map (Subgroup.centralizer ({uHatA} : Set DA)).subtype

noncomputable def kDAEquiv :
    ↥(kDA K) ≃* ↥K :=
  ((Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm).trans
    ((Subgroup.equivMapOfInjective _ _ centUHatEquivBar.symm.injective).symm)

theorem kDA_le :
    kDA K ≤ Subgroup.centralizer ({uHatA} : Set DA) :=
  Subgroup.map_subtype_le _

theorem commutator_kDA
    (hperf : ⁅K, K⁆ = K) : ⁅kDA K, kDA K⁆ = kDA K := by
  rw [kDA, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hperf]

theorem natCard_center_kDA :
    Nat.card ↥(Subgroup.center ↥(kDA K)) =
    Nat.card ↥(Subgroup.center ↥K) :=
  Nat.card_congr (Subgroup.centerCongr (kDAEquiv K)).toEquiv

noncomputable def kDAQuotEquiv :
    ↥(kDA K) ⧸ Subgroup.center ↥(kDA K) ≃* ↥K ⧸ Subgroup.center ↥K :=
  QuotientGroup.congr _ _ (kDAEquiv K) (center_map_mulEquiv (kDAEquiv K))

theorem twoPointShape_tGriess_uGriess
    (hperf : ⁅K, K⁆ = K)
    (hZ : Nat.card ↥(Subgroup.center ↥K) = 2)
    (hE : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* ↥stdGroup))
    (hcard : Nat.card ↥(cent2 tGriess uGriess) = 4 * Nat.card ↥stdGroup) :
    TwoPointShape (cent2 tGriess uGriess) 1 := by
  obtain ⟨e⟩ := hE
  have hKcard : Nat.card ↥K = 2 * Nat.card ↥stdGroup := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K), hZ,
      Nat.card_congr e.toEquiv, mul_comm]
  have hKDA : Nat.card ↥(kDA K) = Nat.card ↥K := Nat.card_congr (kDAEquiv K).toEquiv
  have D : ShapeOneData tGriess uGriess centToDA (kDA K) :=
    { hau := uGriess_mul_tGriess
      hker := centToDA_eq_one_iff
      hπ := centToDA_surjective
      ha := tGriess_mul_self
      ha1 := tGriess_ne_one
      hu2 := uGriess_mul_self
      hu1 := uGriess_ne_one
      hua := uGriess_ne_tGriess
      hK := by rw [centToDA_uIn]; exact kDA_le K
      hperf := commutator_kDA K hperf
      hcard := by rw [hcard, hKDA, hKcard]; ring
      hZ := by rw [natCard_center_kDA, hZ] }
  exact D.twoPointShape_one (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    ((kDAQuotEquiv K).trans e).symm lieModel_stdGroup)

end CFSG.Monster.Existence
