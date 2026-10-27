module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P63Lin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P65Ray

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62 P63

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P65

theorem exists_five_elt (F : FanTree Γ G) {α p q : V} (hv5 : valence Γ α = 5) (hp : Γ.Adj α p)
    (hq : Γ.Adj α q) (hpq : p ≠ q) {a b : G} (ha : a ∈ MulAction.stabilizer G α)
    (hb : b ∈ MulAction.stabilizer G α) (hap : a • p = p) (hbq : b • q = q)
    (haK : a ∉ nbrStab Γ G α) (hbK : b ∉ nbrStab Γ G α) :
    ∃ x ∈ Subgroup.closure ({a, b} : Set G), orderOf x = 5 := by
  classical
  by_contra hcon
  push Not at hcon
  set N := Subgroup.closure ({a, b} : Set G) with hN
  have hNle : N ≤ MulAction.stabilizer G α := by
    rw [hN, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ha
    · exact hb
  have hfin : Finite (MulAction.stabilizer G α) := F.loc_finite α
  have hfinN : Finite N :=
    Finite.of_injective (Subgroup.inclusion hNle) (Subgroup.inclusion_injective _)
  have h5 : ¬ 5 ∣ Nat.card N := by
    intro hd
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 5 hd
    exact hcon x x.2 (by rw [Subgroup.orderOf_coe]; exact hx)
  obtain ⟨k, hk⟩ := F.exists_card_stabilizer α
  have hdvd : Nat.card N ∣ 2 ^ k := by
    have h1 : Nat.card N ∣ Nat.card (MulAction.stabilizer G α) := Subgroup.card_dvd_of_le hNle
    rw [hk, hv5] at h1
    have hcop : Nat.Coprime (Nat.card N) 5 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5).symm
    exact hcop.dvd_of_dvd_mul_left h1
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hP : IsPGroup 2 N := IsPGroup.of_card hn
  obtain ⟨w, hw, hwfix⟩ := F.exists_fixed_nbr_of_two_group α N hNle (fun g hg => by
    obtain ⟨m, hm⟩ := hP ⟨g, hg⟩
    refine ⟨m, ?_⟩
    have : g ^ 2 ^ m = 1 := congrArg Subtype.val hm
    rw [this]
    exact one_mem _)
  have haw : a • w = w := hwfix a (Subgroup.subset_closure (Or.inl rfl))
  have hbw : b • w = w := hwfix b (Subgroup.subset_closure (Or.inr rfl))
  have h1 : w = p := by
    by_contra hne
    exact P63.moves_of_fix F ha hp hw (Ne.symm hne) hap haK haw
  have h2 : w = q := by
    by_contra hne
    exact P63.moves_of_fix F hb hq hw (Ne.symm hne) hbq hbK hbw
  exact hpq (h1.symm.trans h2)

variable {L : ZLab Γ G} {ℓ : Line Γ} {j : ℤ}

theorem lineData_rev (F : FanTree Γ G) (D : LineData L ℓ j) : LineData L ℓ.rev (-j) := by
  refine ⟨?_, fun c i hc => ?_⟩
  · have h1 : valence Γ (ℓ.vert j) ≠ valence Γ (ℓ.vert (j - 1)) :=
      F.alternating _ _ (ℓ.adj_pred j)
    have h2 : valence Γ (ℓ.vert (j - 1)) = 3 ∨ valence Γ (ℓ.vert (j - 1)) = 5 := F.valence _
    have h3 := D.val_five_j F
    have e : ℓ.rev.vert (-j + 1) = ℓ.vert (j - 1) := by
      rw [Line.rev_vert]
      congr 1
      ring
    rw [e]
    omega
  · have hc' : valence Γ (ℓ.vert (-c)) = 5 := hc
    exact (D.fix (-c) (-i) hc').trans
      ⟨fun h => ⟨by omega, by omega⟩, fun h => ⟨by omega, by omega⟩⟩

theorem exists_side_elt (F : FanTree Γ G) (D : LineData L ℓ j) :
    ∃ a : G, a ∈ MulAction.stabilizer G (ℓ.vert j) ∧ a ∉ nbrStab Γ G (ℓ.vert j) ∧
      a • ℓ.vert (j + 1) = ℓ.vert (j + 1) ∧
      ∀ g ∈ MulAction.stabilizer G (ℓ.vert (j + 4)), g * a = a * g :=
  ⟨L.z (ℓ.vert (j + 4)), D.a_mem_stab_j F, D.a_not_mem_nbrStab_j F,
    D.a_fix F (by omega) (by omega), fun _ hg => z_comm (D.val_five_j4 F) hg⟩

theorem exists_x0_bound (F : FanTree Γ G) (D : LineData L ℓ j) :
    ∃ x₀ ∈ MulAction.stabilizer G (ℓ.vert j), orderOf x₀ = 5 ∧
      (Subgroup.centralizer ({x₀} : Set G)).relIndex (nbrStab Γ G (ℓ.vert j)) ≤
        16 * ((nbrStab Γ G (ℓ.vert j)).relIndex (MulAction.stabilizer G (ℓ.vert j) ⊓
          MulAction.stabilizer G (ℓ.vert (j + 1)))) ^ 2 := by
  have hv5 : valence Γ (ℓ.vert j) = 5 := D.val_five_j F
  obtain ⟨a, haS, haK, haF, haC⟩ := exists_side_elt F D
  obtain ⟨b, hbS, hbK, hbF, hbC⟩ := exists_side_elt F (lineData_rev F D)
  have e0 : ℓ.rev.vert (-j) = ℓ.vert j := by rw [Line.rev_vert, neg_neg]
  have e1 : ℓ.rev.vert (-j + 1) = ℓ.vert (j - 1) := by
    rw [Line.rev_vert]
    congr 1
    ring
  have e4 : ℓ.rev.vert (-j + 4) = ℓ.vert (j - 4) := by
    rw [Line.rev_vert]
    congr 1
    ring
  rw [e0] at hbS hbK
  rw [e1] at hbF
  rw [e4] at hbC
  have hpq : ℓ.vert (j + 1) ≠ ℓ.vert (j - 1) := by
    have := ℓ.nb (j - 1)
    rw [show j - 1 + 2 = j + 1 by omega] at this
    exact this.symm
  obtain ⟨x₀, hx₀, hx₀o⟩ := exists_five_elt F hv5 (ℓ.adj j) (ℓ.adj_pred j) hpq haS hbS haF hbF
    haK hbK
  have hKfin : Finite (nbrStab Γ G (ℓ.vert j)) := F.finite_nbrStab _
  have hU : (MulAction.stabilizer G (ℓ.vert (j + 4)) ⊓ MulAction.stabilizer G (ℓ.vert (j - 4))) ⊓
      nbrStab Γ G (ℓ.vert j) ≤ Subgroup.centralizer ({x₀} : Set G) := by
    rintro u ⟨⟨hu1, hu2⟩, -⟩
    have hcen : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        exact haC u hu1
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        exact hbC u hu2
    have := Subgroup.mem_centralizer_iff.1 (hcen hx₀) u rfl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact this.symm
  refine ⟨x₀, ?_, hx₀o, ?_⟩
  · have : Subgroup.closure ({a, b} : Set G) ≤ MulAction.stabilizer G (ℓ.vert j) := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact haS
      · exact hbS
    exact this hx₀
  have hra := ray_bound F ℓ j hv5
  have hrb := ray_bound F ℓ.rev (-j) (by rw [e0]; exact hv5)
  have hh : (nbrStab Γ G (ℓ.vert j)).relIndex (MulAction.stabilizer G (ℓ.vert j) ⊓
      MulAction.stabilizer G (ℓ.vert (j - 1))) =
      (nbrStab Γ G (ℓ.vert j)).relIndex (MulAction.stabilizer G (ℓ.vert j) ⊓
        MulAction.stabilizer G (ℓ.vert (j + 1))) :=
    F.relIndex_edge_eq (ℓ.adj j) (ℓ.adj_pred j) rfl
  rw [e0, e1, e4, hh] at hrb
  calc (Subgroup.centralizer ({x₀} : Set G)).relIndex (nbrStab Γ G (ℓ.vert j))
      ≤ ((MulAction.stabilizer G (ℓ.vert (j + 4)) ⊓ MulAction.stabilizer G (ℓ.vert (j - 4))) ⊓
          nbrStab Γ G (ℓ.vert j)).relIndex (nbrStab Γ G (ℓ.vert j)) :=
        Subgroup.relIndex_le_of_le_left hU (FanTree.relIndex_ne_zero_of_finite _ _)
    _ = (MulAction.stabilizer G (ℓ.vert (j + 4)) ⊓
          MulAction.stabilizer G (ℓ.vert (j - 4))).relIndex (nbrStab Γ G (ℓ.vert j)) :=
        Subgroup.inf_relIndex_right _ _
    _ ≤ (MulAction.stabilizer G (ℓ.vert (j + 4))).relIndex (nbrStab Γ G (ℓ.vert j)) *
          (MulAction.stabilizer G (ℓ.vert (j - 4))).relIndex (nbrStab Γ G (ℓ.vert j)) :=
        Subgroup.relIndex_inf_le
    _ ≤ (4 * (nbrStab Γ G (ℓ.vert j)).relIndex (MulAction.stabilizer G (ℓ.vert j) ⊓
          MulAction.stabilizer G (ℓ.vert (j + 1)))) *
        (4 * (nbrStab Γ G (ℓ.vert j)).relIndex (MulAction.stabilizer G (ℓ.vert j) ⊓
          MulAction.stabilizer G (ℓ.vert (j + 1)))) := Nat.mul_le_mul hra hrb
    _ = 16 * ((nbrStab Γ G (ℓ.vert j)).relIndex (MulAction.stabilizer G (ℓ.vert j) ⊓
          MulAction.stabilizer G (ℓ.vert (j + 1)))) ^ 2 := by ring

end P65

end CFSG.Quasithin.Fan86
