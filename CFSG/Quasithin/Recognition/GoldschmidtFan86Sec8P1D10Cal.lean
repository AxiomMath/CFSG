module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Ord
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Dist

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem ZLab.calpha_eq_stab {L : ZLab Γ G} {F : FanTree Γ G} (h71a : Fan71a F L)
    (h : Fan71c F L) (P : Arc Γ 8) (hv : valence Γ (P.vert 0) = 5) (hne : P.vert 0 ≠ P.vert 8) :
    L.calpha P = P.stab G := by
  have hv8 : valence Γ (P.vert 8) = 5 := valence_of_dist_even F hv (by
    rw [Arc.dist_eq F.isTree P 8 le_rfl])
  obtain ⟨⟨e⟩, hcent⟩ := h71a P hv
  have hab : L.z (P.vert 0) ≠ L.z (P.vert 8) := fun h' => hne (h.z_injective hv hv8 h')
  have ha : L.z (P.vert 0) ∈ Subgroup.closure ({L.z (P.vert 0), L.z (P.vert 8)} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hb : L.z (P.vert 8) ∈ Subgroup.closure ({L.z (P.vert 0), L.z (P.vert 8)} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hu := d5_prod (e ⟨_, ha⟩) (e ⟨_, hb⟩)
    (by rw [← map_mul, ← map_one e]; exact congrArg e (Subtype.ext (L.z_mul_self hv)))
    (by rw [← map_mul, ← map_one e]; exact congrArg e (Subtype.ext (L.z_mul_self hv8)))
    (fun h1 => L.z_ne_one hv (congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))))
    (fun h1 => L.z_ne_one hv8 (congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))))
    (fun h1 => hab (congrArg Subtype.val (e.injective h1)))
  have hX5 : (⟨_, ha⟩ * ⟨_, hb⟩ : Subgroup.closure ({L.z (P.vert 0), L.z (P.vert 8)} : Set G)) ^ 5
      = 1 := by
    apply e.injective
    rw [map_pow, map_mul, map_one]
    exact hu.1
  have hX1 : (⟨_, ha⟩ * ⟨_, hb⟩ : Subgroup.closure ({L.z (P.vert 0), L.z (P.vert 8)} : Set G))
      ≠ 1 := fun h1 => hu.2 (by rw [← map_mul, h1, map_one])
  have hord : orderOf (L.z (P.vert 0) * L.z (P.vert 8)) = 5 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h5 := orderOf_eq_prime hX5 hX1
    rw [← h5, ← Subgroup.orderOf_coe]
    rfl
  exact hcent _ (Subgroup.mul_mem _ ha hb) hord

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem exists_arc8 (F : FanTree Γ G) (h : Fan71c F L) {i j : Fin 5} (hij : i ≠ j) :
    ∃ P : Arc Γ 8, P.vert 0 = D.delta i ∧ P.vert 4 = α ∧ P.vert 8 = D.delta j ∧
      (∀ m, m ≤ 4 → P.vert m = (D.P i).vert (4 - m)) ∧
      (∀ m, m ≤ 4 → P.vert (4 + m) = (D.P j).vert m) := by
  have hb : (D.P i).vert 1 ≠ (D.P j).vert 1 := fun h' => hij (D.beta_injective F h h')
  have hr : ∀ k, k ≤ 4 → (Arc.rev (D.P i)).vert k = (D.P i).vert (4 - k) :=
    fun k _ => Arc.rev_vert _ k
  have hjn : (Arc.rev (D.P i)).vert 4 = (D.P j).vert 0 := by
    rw [hr 4 le_rfl, Nat.sub_self, D.start, D.start]
  have hnb : 1 ≤ 4 → 1 ≤ 4 → (Arc.rev (D.P i)).vert (4 - 1) ≠ (D.P j).vert 1 := fun _ _ => by
    rw [hr 3 (by norm_num)]
    exact hb
  refine ⟨Arc.append (Arc.rev (D.P i)) (D.P j) hjn hnb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Arc.append_vert_le _ _ _ _ (Nat.zero_le 4), hr 0 (Nat.zero_le 4)]
    rfl
  · rw [Arc.append_vert_le _ _ _ _ le_rfl, hr 4 le_rfl, Nat.sub_self, D.start]
  · rw [Arc.append_vert_ge _ _ _ _ (Nat.le_add_right 4 4), Nat.add_sub_cancel_left]
    rfl
  · intro m hm
    rw [Arc.append_vert_le _ _ _ _ hm, hr m hm]
  · intro m hm
    rw [Arc.append_vert_ge _ _ _ _ (Nat.le_add_right 4 m), Nat.add_sub_cancel_left]

theorem calpha_eq_stab (F : FanTree Γ G) (h71a : Fan71a F L) (h : Fan71c F L) :
    ∃ P : Arc Γ 8, P.vert 0 = D.delta 2 ∧ P.vert 4 = α ∧ P.vert 8 = D.delta 0 ∧
      D.calpha = P.stab G := by
  obtain ⟨P, h0, h4, h8, -, -⟩ := D.exists_arc8 F h (i := 2) (j := 0) (by decide)
  refine ⟨P, h0, h4, h8, ?_⟩
  have hne : P.vert 0 ≠ P.vert 8 := by
    rw [h0, h8]
    intro h'
    exact absurd (D.delta_injective h') (by decide)
  have := ZLab.calpha_eq_stab h71a h P (by rw [h0]; exact D.valence_delta F 2) hne
  rw [← this]
  show nbrStab Γ G α ⊓ Subgroup.centralizer ({D.x} : Set G) =
    nbrStab Γ G (P.vert 4) ⊓ Subgroup.centralizer
      ({L.z (P.vert 0) * L.z (P.vert 8)} : Set G)
  rw [h0, h8, h4]
  rfl

theorem fix_of_mem_calpha (F : FanTree Γ G) (h71a : Fan71a F L) (h : Fan71c F L) {c : G}
    (hc : c ∈ D.calpha) (i : Fin 5) {m : ℕ} (hm : m ≤ 4) : c • (D.P i).vert m = (D.P i).vert m := by
  obtain ⟨P, h0, h4, h8, hP⟩ := D.calpha_eq_stab F h71a h
  rw [hP] at hc
  have hfix := (Arc.mem_stab G).1 hc
  have hd2 : c • D.delta 2 = D.delta 2 := by
    have := hfix 0 (by norm_num)
    rwa [h0] at this
  have hd0 : c • D.delta 0 = D.delta 0 := by
    have := hfix 8 le_rfl
    rwa [h8] at this
  have hcx : c * D.x⁻¹ = D.x⁻¹ * c := by
    obtain ⟨-, hcx⟩ := Subgroup.mem_inf.1 (hP ▸ hc : c ∈ D.calpha)
    have := Subgroup.mem_centralizer_iff.1 hcx D.x (by simp)
    calc c * D.x⁻¹ = D.x⁻¹ * (D.x * c) * D.x⁻¹ := by group
      _ = D.x⁻¹ * (c * D.x) * D.x⁻¹ := by rw [this]
      _ = D.x⁻¹ * c := by group
  have hall : ∀ n : ℕ, c • (D.x⁻¹ ^ n) • D.delta 0 = (D.x⁻¹ ^ n) • D.delta 0 := by
    intro n
    have hcn : c * D.x⁻¹ ^ n = D.x⁻¹ ^ n * c := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', ← mul_assoc, hcx, mul_assoc, ih, mul_assoc]
    rw [← mul_smul, hcn, mul_smul, hd0]
  have hdi : c • D.delta i = D.delta i := by
    open Fin.NatCast in
    have hi : D.delta i = (D.x⁻¹ ^ i.val) • D.delta 0 := by
      have hn : ∀ n : ℕ, (D.x⁻¹ ^ n) • D.delta 0 = D.delta (0 + (n : Fin 5)) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', mul_smul, ih, D.x_inv_smul_delta F h]
          congr 1
          open Fin.CommRing in
          push_cast
          ring
      rw [hn, Fin.cast_val_eq_self, zero_add]
    rw [hi]
    exact hall i.val
  have hstab : c • α = α := by
    have := hfix 4 (by norm_num)
    rwa [h4] at this
  refine smul_vert_eq_of_ends F (D.P i) (D.P i) c ?_ ?_ m hm
  · rw [D.start, hstab]
  · exact hdi

theorem z_mem_calpha (F : FanTree Γ G) (h : Fan71c F L) (h512 : Fan512 F L) :
    L.z α ∈ D.calpha := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · refine mem_nbrStab.2 fun w hw => ?_
    exact (mem_ballStab.1 (h512.2.1 α D.val)) w (by rw [dist_eq_one_iff_adj.2 hw]; norm_num)
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact L.comm_z_of_mem_stabilizer D.val (D.x_mem_stabilizer F h)

end D10Set

end CFSG.Quasithin.Fan86
