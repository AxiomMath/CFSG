module

public import CFSG.Quasithin.Background.E6EightSmall
public import CFSG.Quasithin.Background.GoldschmidtTDE68Rk
public import CFSG.Quasithin.Background.GoldschmidtTDE68Cmp
public import CFSG.Quasithin.Background.GoldschmidtTDE68Syl

public section

namespace CFSG.Quasithin.E6.Alt

open Subgroup CFSG.Quasithin.E6.Bar CFSG.QuasithinUnique

variable {Y : Type} [Group Y] [Finite Y] {G : Type} [Group G] [Finite G] {D : Subgroup G}
  {m : ℕ} {L : Subgroup Y}

omit [Finite Y] [Finite G] in
theorem odd_card_center (hZ : Nat.card ↥(Subgroup.center ↥L) = 1 ∨
    Nat.card ↥(Subgroup.center ↥L) = 3) : Odd (Nat.card ↥(Subgroup.center ↥L)) := by
  rcases hZ with h | h <;> rw [h] <;> decide

theorem altRank_of_iso (hM : AltModel G D) (hD8 : Nat.card D = 8) (hm : Odd m)
    (hG : Nat.card G = 8 * m) {A R : Subgroup Y} (φ : Qbar L ≃* G)
    (hZ : Nat.card ↥(Subgroup.center ↥L) = 1 ∨ Nat.card ↥(Subgroup.center ↥L) = 3)
    (h : E68BaseHyp L A R) :
    (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A ≤ 4 ∧
      ((A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A = 4 →
        L ≤ ⨆ (a : Y) (_ : a ∈ A ∧ a ∉ Subgroup.centralizer (L : Set Y)),
          L ⊓ Subgroup.centralizer ({a} : Set Y)) := by
  have hodd := odd_card_center hZ
  have hperf : Group.IsPerfect ↥L := h.quasisimple.1
  obtain ⟨e, he⟩ := exists_iso_imgBar_eq hm hG hodd φ h.sylow D hD8
  have hcomm : ∀ a ∈ A, ∀ r ∈ R, a * r = r * a := fun a ha r hr =>
    Subgroup.mem_centralizer_iff.1 (h.centralizer hr) a ha
  exact ⟨relIndex_le_four hM e hperf he h.normalizer h.le h.elemAbelian.2 hcomm,
    fun h4 => le_iSup_of_relIndex_eq_four hM e hperf he h.normalizer h.le h.elemAbelian.2 hcomm
      hodd h4⟩

theorem card_comp_of_iso (hM : AltModel G D) (hD8 : Nat.card D = 8) (hm : Odd m)
    (hG : Nat.card G = 8 * m) {R K : Subgroup Y} {u : Y} (φ : Qbar L ≃* G)
    (hZ : Nat.card ↥(Subgroup.center ↥L) = 1 ∨ Nat.card ↥(Subgroup.center ↥L) = 3)
    (h : E68CentHyp L R u) (hK : IsComponentIn K (L ⊓ Subgroup.centralizer ({u} : Set Y))) :
    Nat.card ↥K = 60 := by
  have hodd := odd_card_center hZ
  have hperf : Group.IsPerfect ↥L := h.quasisimple.1
  obtain ⟨e, he⟩ := exists_iso_imgBar_eq hm hG hodd φ h.sylow D hD8
  have hS : CentSetup e R D u :=
    ⟨hperf, he, h.normalizer, h.mem, h.central, h.sq, h.not_mem⟩
  have hZ3 : Nat.card ↥(Subgroup.center ↥L) ∣ 3 := by
    rcases hZ with h | h
    · rw [h]
      exact one_dvd 3
    · rw [h]
  rcases hM.cases _ hS.indHom_mem with hs | ⟨N, -, hN, hNle⟩
  · exact (false_of_solvable hS hs hK.2.1).elim
  · exact card_comp_eq_sixty hS hZ3 N hN hNle hK.1 hK.2.1

theorem false_of_comp_of_iso (hM : ∀ β ∈ InvSet D, Group.IsSolvable ↥(fixedSub β))
    (hD8 : Nat.card D = 8) (hm : Odd m) (hG : Nat.card G = 8 * m) {R K : Subgroup Y} {u : Y}
    (φ : Qbar L ≃* G)
    (hZ : Nat.card ↥(Subgroup.center ↥L) = 1 ∨ Nat.card ↥(Subgroup.center ↥L) = 3)
    (h : E68CentHyp L R u) (hK : IsComponentIn K (L ⊓ Subgroup.centralizer ({u} : Set Y))) :
    False := by
  have hodd := odd_card_center hZ
  have hperf : Group.IsPerfect ↥L := h.quasisimple.1
  obtain ⟨e, he⟩ := exists_iso_imgBar_eq hm hG hodd φ h.sylow D hD8
  have hS : CentSetup e R D u :=
    ⟨hperf, he, h.normalizer, h.mem, h.central, h.sq, h.not_mem⟩
  exact false_of_solvable hS (hM _ hS.indHom_mem) hK.2.1

end CFSG.Quasithin.E6.Alt
