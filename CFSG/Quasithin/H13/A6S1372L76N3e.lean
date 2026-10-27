module

public import CFSG.Quasithin.H13.GoldschmidtSp62Base
public import CFSG.Quasithin.H13.GoldschmidtI51

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Blueprint CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.H13.U3
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
  (nonempty_mulEquiv_statedSp_of_lieModel)

namespace A6L76N3

theorem not_seven_dvd_card_centralizer {X : Type} [Group X]
    (hX : LieModel X .PSp 3 2 1) {d : X} (hd : orderOf d = 2) :
    ¬ 7 ∣ Nat.card ↥(Subgroup.centralizer ({d} : Set X)) := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_statedSp_of_lieModel hX
  have hd' : orderOf (φ d) = 2 := (MulEquiv.orderOf_eq φ d).trans hd
  rw [← card_centralizer_map_equiv φ d]
  obtain ⟨i, g, hg⟩ := exists_conj_of_sylow_classes SH_isPGroup SH_index exists_conj_of_mem_SH hd'
  rw [hg, card_centralizer_conj, centralizer_tH_eq, card_XH]
  fin_cases i <;> decide

theorem false_of_c3System {G : Type} [Group G] [Finite G]
    {Es : Fin 3 → Subgroup G} (hsys : IsDSystemIn .C3 Es) {z : G} (hz : orderOf z = 2)
    (hzE : z ∈ Es 2) (hzC : Es 2 ≤ Subgroup.centralizer ({z} : Set G))
    (h7 : 7 ∣ Nat.card ↥(Es 2)) : False := by
  set E := Es 0 ⊔ Es 1 ⊔ Es 2 with hE
  have h2E : Es 2 ≤ E := le_sup_right
  have hLie : LieModel ↥E .PSp 3 2 1 :=
    (stmtI_5_1_holds ↥E .C3 _ hsys.isDSystem).2 rfl
  set z' : ↥E := ⟨z, h2E hzE⟩ with hz'
  have hz2 : orderOf z' = 2 := by
    rw [← Subgroup.orderOf_coe z']
    exact hz
  apply not_seven_dvd_card_centralizer hLie hz2
  have hle : (Es 2).subgroupOf E ≤ Subgroup.centralizer ({z'} : Set ↥E) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.mp (hzC hx)
    simpa using this
  have hcard : Nat.card ↥((Es 2).subgroupOf E) = Nat.card ↥(Es 2) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h2E).toEquiv
  exact (hcard ▸ h7).trans (Subgroup.card_dvd_of_le hle)

end A6L76N3

end CFSG.Quasithin.H13.A6
