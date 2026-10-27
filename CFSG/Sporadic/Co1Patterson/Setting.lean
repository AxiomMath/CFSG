module

public import CFSG.Sporadic.Co1Patterson.Defs
public import CFSG.Sporadic.Co1Patterson.SettingOmega
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.FS77PSU
public import CFSG.LargeExtraspecial.S14W4LocLeaf
public import CFSG.LargeExtraspecial.S14C13Model
public import CFSG.Monster.GMS.TwoCentral

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.GroupTheory.WeirSylow

theorem card_timmesfeldOmegaPlus_four : Nat.card (timmesfeldOmegaPlus 4) = 174182400 := by
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 4 (ZMod 2)
  have h8 : finrank (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) = 2 * 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  obtain ⟨e⟩ := nonempty_omegaGroup_equiv_omegaPlus hQ h8 (by norm_num)
    (isPlusType_quadPlus (ZMod 2) 4)
  rw [← Nat.card_congr e.toEquiv]
  have h2 := CFSG.LargeExtraspecial.S12DW.card_orthogonalGroup_eq hQ
  rcases natCard_orthogonalGroup_of_finrank_eight hQ h8 with ⟨-, h⟩ | ⟨h, -⟩
  · omega
  · exact absurd (isPlusType_quadPlus (ZMod 2) 4) h

variable {X : Type} [Group X] [Finite X] {t : X}

theorem width_setting (h : PattersonCo1Hyp X t) : (setting h).width = 4 :=
  Bridge.width_ofFStar h.orderOf_eq h.extraspecial (h.card.trans (by norm_num))

theorem card_centralizer (h : PattersonCo1Hyp X t) :
    Nat.card (centralizer ({t} : Set X)) = 89181388800 := by
  obtain ⟨φ, hφ, hker⟩ := h.quotient
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
    card_timmesfeldOmegaPlus_four, hker, h.card] at h1
  rw [h1]
  norm_num

theorem card_Mbar (h : PattersonCo1Hyp X t) : Nat.card (setting h).Mbar = 174182400 := by
  obtain ⟨e⟩ := Bridge.nonempty_mulEquiv_Mbar_ofFStar h.orderOf_eq h.extraspecial h.quotient
  rw [Nat.card_congr e.toEquiv, card_timmesfeldOmegaPlus_four]

theorem Mbar_map_eq_omega (h : PattersonCo1Hyp X t) :
    (setting h).Mbar.map (setting h).O.subtype = timmesfeldOmega (setting h).q :=
  map_Mbar_eq_omega_of_card _ (width_setting h) (card_Mbar h)

theorem isPlusType (h : PattersonCo1Hyp X t) :
    CFSG.GroupTheory.WeirSylow.IsPlusType (setting h).q :=
  isPlusType_of_card _ (width_setting h) (card_Mbar h)

theorem exists_sylow (h : PattersonCo1Hyp X t) :
    ∃ S : Sylow 2 X, t ∈ (S : Subgroup X) ∧ (S : Subgroup X) ≤ centralizer ({t} : Set X) := by
  have hQ : IsExtraspecialPGroup 2 (CFSG.pCore 2 (centralizer ({t} : Set X))) :=
    (setting h).Q_eq_pCore ▸ (setting h).extraspecial
  have hcon : centralizer (CFSG.pCore 2 (centralizer ({t} : Set X)) :
      Set (centralizer ({t} : Set X))) ≤ CFSG.pCore 2 (centralizer ({t} : Set X)) :=
    (setting h).Q_eq_pCore ▸ (setting h).centralizer_le
  obtain ⟨P, hP⟩ := CFSG.Monster.GMS.exists_sylow_center_map_eq_zpowers h.orderOf_eq hQ hcon
  have ht : t ∈ (center (P : Subgroup X)).map (P : Subgroup X).subtype := by
    rw [hP]
    exact mem_zpowers t
  obtain ⟨c, hc, hct⟩ := ht
  refine ⟨P, hct ▸ c.2, fun x hx => mem_centralizer_singleton_iff.mpr ?_⟩
  have := congrArg Subtype.val (mem_center_iff.mp hc ⟨x, hx⟩)
  simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at this hct
  rw [← hct]
  exact this

theorem notWeaklyClosed (h35 : AschbacherSmith35Input)
    (h : PattersonCo1Hyp X t) : NotWeaklyClosed h := by
  by_contra hw
  have hwc : ∀ g : X, g * (setting h).z * g⁻¹ ∈ (setting h).QG →
      g * (setting h).z * g⁻¹ = (setting h).z := fun g hg => by
    by_contra hne
    exact hw ⟨g, hg, hne⟩
  have : IsSimpleGroup X := h.simple
  have h21 : 2 ^ 21 ∣ Nat.card (centralizer ({t} : Set X)) :=
    ⟨42525, by rw [card_centralizer h]; norm_num⟩
  rcases h35 X (setting h) (by rw [width_setting h]; norm_num) hwc with he | ⟨-, he⟩
  · rw [width_setting h] at he
    obtain ⟨e⟩ := he
    have := FS77.two_pow_le_of_mulEquiv_timmesfeldPSU (by norm_num) e _ h21
    norm_num at this
  · obtain ⟨e⟩ := he
    have hX := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
      (h21.trans (Subgroup.card_subgroup_dvd_card _))
    rw [Nat.card_congr e.toEquiv, factorization_card_Co2] at hX
    omega

theorem isConj_of_mem_QG (h : PattersonCo1Hyp X t) (hw : NotWeaklyClosed h) {u : X}
    (hu : u ∈ (setting h).QG) (hu2 : orderOf u = 2) : IsConj t u := by
  obtain ⟨g, hg, hne⟩ := hw
  have h8 := finrank_Qt_of_width_four _ (width_setting h)
  exact isConj_of_mem_QG_of_omega (setting h) (by omega) (Mbar_map_eq_omega h) hg hne hu hu2

theorem exists_swap (h : PattersonCo1Hyp X t) (hw : NotWeaklyClosed h) {u : X}
    (hu : u ∈ (setting h).QG) (hu2 : orderOf u = 2) (hut : u ≠ t) :
    ∃ g : X, g * t * g⁻¹ = u ∧ g * u * g⁻¹ = t := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_mem_QG h hw hu hu2)
  obtain ⟨g, -, hg⟩ := (setting h).exists_swap hc hu hut
  exact ⟨g, hg⟩

end CFSG.Sporadic.Co1Patterson
