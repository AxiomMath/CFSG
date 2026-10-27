
module

public import CFSG.Sporadic.Schreier.J4SLocalNodesBase1

public import CFSG.Sporadic.Schreier.J4SGL
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem fam_J4_local_subgroup_order :
    Nat.card K = 244823040 ∧ (∀ k ∈ K, (∀ n ∈ N, k * n * k⁻¹ = n) → k = 1) ∧
      N ≤ H ∧ K ≤ H ∧ (N.subgroupOf H).Normal ∧ N ⊓ K = ⊥ ∧ N ⊔ K = H ∧
      Nat.card H = 501397585920 ∧ CFSG.IsElementaryAbelian 2 N ∧ Nat.card N = 2048 := by
  refine ⟨card_K, fun k hk hc => ?_, N_le_H, K_le_H, N_normal_in_H, by rw [inf_comm, K_inf_N],
    N_sup_K, card_H, N_isElementaryAbelian, by rw [card_N]; norm_num⟩
  have h1 : ρK ⟨k, hk⟩ = 1 := by
    refine MulEquiv.ext fun n => Subtype.ext ?_
    rw [ρK_apply, MulAut.one_apply]
    exact hc n n.2
  have := ρK_injective (h1.trans (map_one ρK).symm)
  rwa [Subgroup.mk_eq_one] at this

theorem R3E_J4_exact_local_eleven_dimensional_binary_action :
    (∀ a < 2048, η (app11 xColumns a) = x * η a * x⁻¹ ∧ η (app11 yColumns a) = y * η a * y⁻¹) ∧
      ∃ ρ : K →* GL (Fin 11) (ZMod 2),
        (∀ (k : K) (a : Fin 11 → ZMod 2),
          etaV ((ρ k : Matrix (Fin 11) (Fin 11) (ZMod 2)) *ᵥ a) = k * etaV a * (k : J)⁻¹) ∧
        (ρ ⟨x, x_mem_K⟩ : Matrix (Fin 11) (Fin 11) (ZMod 2)) = colsMatrix xColumns ∧
        (ρ ⟨y, y_mem_K⟩ : Matrix (Fin 11) (Fin 11) (ZMod 2)) = colsMatrix yColumns ∧
        Function.Injective ρ :=
  ⟨fun a _ => ⟨(x_conj_η a).symm, (y_conj_η a).symm⟩, ρGL, etaV_ρGL, ρGL_x, ρGL_y,
    ρGL_injective⟩

theorem QT_unique_J4_local_normal_module_irreducible :
    (∀ n ∈ N, n = 1 ∨ n ∈ conjOrbit K (η 1) ∨ n ∈ conjOrbit K (η 14)) ∧
      conjOrbit K (η 1) ⊆ N ∧ conjOrbit K (η 14) ⊆ N ∧
      (conjOrbit K (η 1)).ncard = 1771 ∧ (conjOrbit K (η 14)).ncard = 276 ∧
      (1 : J) ∉ conjOrbit K (η 1) ∧ (1 : J) ∉ conjOrbit K (η 14) ∧
      Disjoint (conjOrbit K (η 1)) (conjOrbit K (η 14)) ∧
      (∀ D : Subgroup J, D ≤ N → (D.subgroupOf H).Normal → D = ⊥ ∨ D = N) ∧
      Subgroup.centralizer (N : Set J) ⊓ H = N := by
  have hnz1 := pts_ne_zero_of_reach η_one_ne_one reach1
  have hnz14 := pts_ne_zero_of_reach (s := 14) (fun h => by
    have := η_injOn (i := 14) (k := 0) (by norm_num) (by norm_num) (h.trans η_zero.symm)
    omega) reach14
  refine ⟨fun n hn => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun D hDN hD => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := exists_η_eq hn
    rcases cover a ha with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact Or.inl η_zero
    · exact Or.inr (Or.inl (conjOrbit_one ▸ ⟨i, hi, rfl⟩))
    · exact Or.inr (Or.inr (conjOrbit_fourteen ▸ ⟨i, hi, rfl⟩))
  · rintro _ ⟨k, hk, rfl⟩
    exact conj_mem_N_of_mem_K hk (η_mem_N 1)
  · rintro _ ⟨k, hk, rfl⟩
    exact conj_mem_N_of_mem_K hk (η_mem_N 14)
  · rw [conjOrbit_one]
    exact ncard_enum (fun i hi => bfsOK_lt orb1_ok hi) fun i hi k hk => bfsOK_ne orb1_ok hi hk
  · rw [conjOrbit_fourteen]
    exact ncard_enum (fun i hi => bfsOK_lt orb14_ok hi) fun i hi k hk => bfsOK_ne orb14_ok hi hk
  · rw [conjOrbit_one]
    rintro ⟨i, hi, e⟩
    rw [← η_zero] at e
    exact hnz1 i hi (η_injOn (bfsOK_lt orb1_ok hi) (by norm_num) e.symm)
  · rw [conjOrbit_fourteen]
    rintro ⟨i, hi, e⟩
    rw [← η_zero] at e
    exact hnz14 i hi (η_injOn (bfsOK_lt orb14_ok hi) (by norm_num) e.symm)
  · rw [Set.disjoint_left]
    intro m h1 h14
    have e := (conjOrbit_eq_of_mem h1).symm.trans (conjOrbit_eq_of_mem h14)
    have hc1 : (conjOrbit K (η 1)).ncard = 1771 := by
      rw [conjOrbit_one]
      exact ncard_enum (fun i hi => bfsOK_lt orb1_ok hi) fun i hi k hk => bfsOK_ne orb1_ok hi hk
    have hc14 : (conjOrbit K (η 14)).ncard = 276 := by
      rw [conjOrbit_fourteen]
      exact ncard_enum (fun i hi => bfsOK_lt orb14_ok hi) fun i hi k hk =>
        bfsOK_ne orb14_ok hi hk
    rw [e, hc14] at hc1
    norm_num at hc1
  · refine eq_bot_or_eq_N hDN fun k hk d hd => ?_
    have := hD.conj_mem ⟨d, N_le_H (hDN hd)⟩ (Subgroup.mem_subgroupOf.2 hd) ⟨k, K_le_H hk⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this
  · refine le_antisymm (fun h hh => ?_) (le_inf (fun n hn => ?_) N_le_H)
    · have h1 : ρH ⟨h, hh.2⟩ = 1 := by
        refine MulEquiv.ext fun n => Subtype.ext ?_
        rw [ρH_apply, MulAut.one_apply]
        have hc := Subgroup.mem_centralizer_iff.1 hh.1 n n.2
        rw [← hc, mul_inv_cancel_right]
      have h2 : (⟨h, hh.2⟩ : H) ∈ N.subgroupOf H := by
        rw [← ker_ρH]
        exact h1
      exact Subgroup.mem_subgroupOf.1 h2
    · have : IsMulCommutative N := N_isElementaryAbelian.toIsMulCommutative
      exact Subgroup.mem_centralizer_iff.2 fun m hm => setLike_mul_comm hm hn

end CFSG.Sporadic.J4Schreier
