module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocI
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocG

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem card_zpowers_sup_le (h : Ctx T M g A t d x) :
    Nat.card ↥(Subgroup.zpowers (u0Of d x) ⊔ Subgroup.zpowers (wOfX d x)) ≤ 8 := by
  have hu₀U := u0Of_mem_U h.c h.c18 h.hD h.hd4 h.hx h.hx3 h.hΓ
  have hu₀z := u0Of_sq h.c h.hD h.hd4 h.hx h.hx3
  have hdd := dd_facts h.hd4
  have hw2 := wOfX_sq h.c h.hD h.hd4 h.hx h.hx3
  have hcomm : u0Of d x * wOfX d x = wOfX d x * u0Of d x :=
    Subgroup.mem_centralizer_singleton_iff.mp (mem_K0_of_mem_U_comm h hu₀U rfl).2
  have hA : Subgroup.zpowers (u0Of d x) ≤
      Subgroup.centralizer (Subgroup.zpowers (wOfX d x) : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute (wOfX d x) (u0Of d x) from hcomm.symm) j).eq
  have hprod := card_sup_mul_card_inf_of_le_centralizer hA
  have h4 : orderOf (u0Of d x) = 4 :=
    orderOf_eq_four_of_sq (by rw [hu₀z]; exact hdd.2) (by rw [hu₀z]; exact hdd.1)
  have h2 : Nat.card ↥(Subgroup.zpowers (wOfX d x)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2))
  rw [Nat.card_zpowers, h4] at hprod
  have hpos : 0 < Nat.card ↥(Subgroup.zpowers (u0Of d x) ⊓ Subgroup.zpowers (wOfX d x)) :=
    Nat.card_pos
  nlinarith

theorem Bw_card_of_ctx (h : Ctx T M g A t d x) : Nat.card ↥(Bw T d x) ∣ 16 := by
  obtain ⟨m, hm⟩ := (Bw_pGroup_of_ctx h).exists_card_eq
  have hmul := Subgroup.relIndex_mul_card (qOf T) (Bw T d x)
  have hle : Nat.card ↥(qOf T ⊓ Bw T d x) ≤ 8 :=
    (Subgroup.card_le_of_le (by rw [inf_comm]; exact Bw_inf_Q_of_ctx h)).trans
      (card_zpowers_sup_le h)
  have hrel := Bw_relIndex_of_ctx h
  have h16 : Nat.card ↥(Bw T d x) ≤ 16 := by rw [← hmul]; nlinarith
  rw [hm] at h16 ⊢
  have hm4 : m ≤ 4 := by
    by_contra hcon
    have : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (pow_dvd_pow 2 hm4).trans (by norm_num)

theorem wp0_of_ctx (h : Ctx T M g A t d x) : Wp0 T d x where
  card_Tw := card_Tw_eq h
  card_Cw := card_Cw_eq h
  K0_normal := K0_normal_of_ctx T d x
  K0_contains_z := K0_contains_z_of_ctx h
  Bw_pGroup := Bw_pGroup_of_ctx h
  Bw_card := Bw_card_of_ctx h
  Bw_inf_Q := Bw_inf_Q_of_ctx h
  Bw_relIndex := Bw_relIndex_of_ctx h
  Bw_invol := Bw_invol_of_ctx h

end InspW2

end S143

end CFSG.Quasithin
