module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2KRed
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Tr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3WFrat
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P2K

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

structure KleinU (D : D10Set L α) (u : G) : Prop where
  mem : u ∈ D.calpha
  sq : u * u = 1
  not_mem : u ∉ Subgroup.zpowers (L.z α)
  fix0 : u ∈ nbrStab Γ G (D.delta 0)

theorem z_not_mem_nbrStab_delta (F : FanTree Γ G) (h71c : Fan71c F L) (i : Fin 5) :
    L.z α ∉ nbrStab Γ G (D.delta i) := by
  intro hz
  obtain ⟨ν, hν, hνξ⟩ := F.exists_adj_ne (D.delta i) (D.xi i)
  have hd : Γ.dist α ν = 5 := by
    have := IsTree.dist_succ_of_ne F.isTree (D.adj_xi_delta i).symm hν (fun h => hνξ h.symm)
      (w := α) (by rw [D.dist_start_xi F i, D.dist_delta F i])
    rw [this, D.dist_delta F i]
  have h1 := mem_nbrStab.1 hz ν hν
  have h2 := (h71c.z_smul_eq_iff D.val ν).1 h1
  omega

theorem calpha_comm_x_pow {c : G} (hc : c ∈ D.calpha) (n : ℕ) : c * D.x ^ n = D.x ^ n * c := by
  have h1 : D.x * c = c * D.x :=
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 D.x (by simp)
  have hcomm : Commute c D.x := h1.symm
  exact (hcomm.pow_right n).eq

theorem calpha_le_edge (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) {c : G}
    (hc : c ∈ D.calpha) (i : Fin 5) :
    c ∈ MulAction.stabilizer G (D.delta i) ⊓ MulAction.stabilizer G (D.xi i) :=
  ⟨MulAction.mem_stabilizer_iff.2 (D.fix_of_mem_calpha F h71a h71c hc i (m := 4) le_rfl),
    MulAction.mem_stabilizer_iff.2 (D.fix_of_mem_calpha F h71a h71c hc i (m := 3) (by norm_num))⟩

theorem z_mem_edge (F : FanTree Γ G) (h71c : Fan71c F L) (i : Fin 5) :
    L.z α ∈ MulAction.stabilizer G (D.delta i) ⊓ MulAction.stabilizer G (D.xi i) := by
  refine ⟨(h71c.z_mem_stabilizer_iff D.val _).2 ?_, (h71c.z_mem_stabilizer_iff D.val _).2 ?_⟩
  · rw [D.dist_delta F i]
  · rw [D.dist_start_xi F i]
    norm_num

theorem exists_kleinU (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L)
    (h75 : Fan75 F L) (hk : ∀ c ∈ D.calpha, c * c = 1) (h4 : Nat.card ↥D.calpha = 4) :
    ∃ u, KleinU D u := by
  obtain ⟨u, hu, hnz⟩ := exists_not_mem_zpowers D F h71c h75 h4
  have hz := Sec8P3.z_mem_calpha_of_fan75 D h71c h75
  have hz2 : L.z α * L.z α = 1 := L.z_mul_self D.val
  by_cases hK : u ∈ nbrStab Γ G (D.delta 0)
  · exact ⟨u, hu, hk u hu, hnz, hK⟩
  · have hnzu : u * L.z α ∉ Subgroup.zpowers (L.z α) := fun h => hnz (by
      have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.mem_zpowers (L.z α)))
      simpa using this)
    refine ⟨u * L.z α, mul_mem hu hz, hk _ (mul_mem hu hz), hnzu, ?_⟩
    exact F.mul_mem_nbrStab_of_sq_eq_one (D.adj_xi_delta 0).symm
      (calpha_le_edge D F h71a h71c hu 0) (z_mem_edge D F h71c 0) (hk u hu) hz2 hK
      (z_not_mem_nbrStab_delta D F h71c 0)

variable {D}

theorem klein_cases (F : FanTree Γ G) (h71c : Fan71c F L) (h75 : Fan75 F L) {u : G}
    (hu : KleinU D u) (h4 : Nat.card ↥D.calpha = 4) :
    ∀ c ∈ D.calpha, c = 1 ∨ c = L.z α ∨ c = u ∨ c = u * L.z α := by
  classical
  have hfin := Sec8P3.finite_calpha D F
  have hz := Sec8P3.z_mem_calpha_of_fan75 D h71c h75
  have hz1 : L.z α ≠ 1 := L.z_ne_one D.val
  have hz2 : L.z α * L.z α = 1 := L.z_mul_self D.val
  have hu1 : u ≠ 1 := fun h => hu.not_mem (h ▸ one_mem _)
  have huz : u ≠ L.z α := fun h => hu.not_mem (h ▸ Subgroup.mem_zpowers _)
  have huz1 : u * L.z α ≠ 1 := fun h => hu.not_mem (by
    have : u = (L.z α)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
  have hzuz : L.z α ≠ u * L.z α := fun h =>
    hu1 (mul_right_cancel (show 1 * L.z α = u * L.z α by rw [one_mul]; exact h)).symm
  have huuz : u ≠ u * L.z α := fun h =>
    hz1 (mul_left_cancel (show u * 1 = u * L.z α by rw [mul_one]; exact h)).symm
  have hmem : u * L.z α ∈ D.calpha := mul_mem hu.mem hz
  have : Fintype ↥D.calpha := Fintype.ofFinite _
  let a : ↥D.calpha := ⟨L.z α, hz⟩
  let b : ↥D.calpha := ⟨u, hu.mem⟩
  let e : ↥D.calpha := ⟨u * L.z α, hmem⟩
  let T : Finset ↥D.calpha := {1, a, b, e}
  have hT : T.card = 4 := by
    have n1 : (1 : ↥D.calpha) ∉ ({a, b, e} : Finset ↥D.calpha) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hz1 (congrArg Subtype.val h).symm,
        fun h => hu1 (congrArg Subtype.val h).symm,
        fun h => huz1 (congrArg Subtype.val h).symm⟩
    have n2 : a ∉ ({b, e} : Finset ↥D.calpha) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => huz (congrArg Subtype.val h).symm, fun h => hzuz (congrArg Subtype.val h)⟩
    have n3 : b ∉ ({e} : Finset ↥D.calpha) := by
      simp only [Finset.mem_singleton]
      exact fun h => huuz (congrArg Subtype.val h)
    show (insert 1 (insert a (insert b {e})) : Finset ↥D.calpha).card = 4
    rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
      Finset.card_insert_of_notMem n3, Finset.card_singleton]
  have hall : T = Finset.univ :=
    Finset.eq_univ_of_card T (by rw [hT, Fintype.card_eq_nat_card, h4])
  intro c hc
  have hcT : (⟨c, hc⟩ : ↥D.calpha) ∈ T := hall ▸ Finset.mem_univ _
  simp only [T, Finset.mem_insert, Finset.mem_singleton] at hcT
  rcases hcT with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

theorem KleinU.mem_nbrStab_alpha (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L)
    {u : G} (hu : KleinU D u) (i : Fin 5) : u ∈ nbrStab Γ G (D.alpha i) :=
  F.fix_two_nbrs (D.adj_alpha_xi i) (D.adj_beta_alpha i).symm (D.xi_ne_beta i)
    (D.fix_of_mem_calpha F h71a h71c hu.mem i (m := 3) (by norm_num))
    (D.fix_of_mem_calpha F h71a h71c hu.mem i (m := 1) (by norm_num))

theorem KleinU.mem_nbrStab {u : G} (hu : KleinU D u) : u ∈ nbrStab Γ G α :=
  (Subgroup.mem_inf.1 hu.mem).1

end Sec8P2K

end CFSG.Quasithin.Fan86
