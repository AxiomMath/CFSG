module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Tr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3WChar
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Rel
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Cal

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)

theorem relIndex_nbrStab_eq_twenty (h65 : Fan65 F) {α : V} (hα : Fan86.valence Γ α = 5) :
    (nbrStab Γ G α).relIndex (MulAction.stabilizer G α) = 20 := by
  obtain ⟨β, hαβ⟩ := F.exists_adj α
  have h4 := F.relIndex_edge_eq_four h65 hα hαβ
  have hE : (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β).relIndex
      (MulAction.stabilizer G α) = 5 := by
    rw [Subgroup.inf_relIndex_left, F.relIndex_stabilizer_eq_valence hαβ le_rfl
      (fun u w hu hw => F.loc_trans α u w hu hw), hα]
  have hKE : nbrStab Γ G α ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := fun g hg =>
    ⟨F.nbrStab_le_stabilizer α hg, MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg β hαβ)⟩
  have hmul := Subgroup.relIndex_mul_relIndex (nbrStab Γ G α)
    (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) (MulAction.stabilizer G α) hKE inf_le_left
  rw [hE, h4] at hmul
  omega

theorem card_nbrStab_eq (h65 : Fan65 F) {L : ZLab Γ G} (h : Fan71c F L) {α : V}
    (D : D10Set L α) : Nat.card (nbrStab Γ G α) = 2 ^ 8 * Nat.card D.calpha := by
  have h1 := h65.1 α D.val D.x (D.x_mem_stabilizer F h) (D.orderOf_x F)
  have h2 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({D.x} : Set G))
    (K := nbrStab Γ G α)
  rw [h1, show Subgroup.centralizer ({D.x} : Set G) ⊓ nbrStab Γ G α = D.calpha from
    inf_comm _ _] at h2
  exact h2.symm

theorem card_stabilizer_eq (h65 : Fan65 F) {L : ZLab Γ G} (h : Fan71c F L) {α : V}
    (D : D10Set L α) :
    Nat.card (MulAction.stabilizer G α) = 20 * (2 ^ 8 * Nat.card D.calpha) := by
  have h3 := Subgroup.relIndex_mul_card (H := nbrStab Γ G α) (K := MulAction.stabilizer G α)
  rw [F.relIndex_nbrStab_eq_twenty h65 D.val, inf_of_le_left (F.nbrStab_le_stabilizer α)] at h3
  rw [← h3, F.card_nbrStab_eq h65 h D]

end FanTree

namespace ZLab

variable {L : ZLab Γ G}

theorem orderOf_z {v : V} (hv : valence Γ v = 5) : orderOf (L.z v) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact L.z_mul_self hv) (L.z_ne_one hv)

end ZLab

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem calpha_eq_zpowers_z (F : FanTree Γ G) (h : Fan71c F L) (h512 : Fan512 F L)
    (hc : Nat.card D.calpha = 2) : D.calpha = Subgroup.zpowers (L.z α) := by
  have hfin : Finite D.calpha := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  refine ((Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers (L.z α)) (K := D.calpha)
    ((Subgroup.zpowers_le).2 (D.z_mem_calpha F h h512)) ?_)).symm
  have h2 := L.orderOf_z D.val
  rw [Nat.card_zpowers]
  omega

theorem sq_eq_z_of_card_four (F : FanTree Γ G) (h : Fan71c F L) (h512 : Fan512 F L) {c : G}
    (hgen : D.calpha = Subgroup.zpowers c) (hc : Nat.card D.calpha = 4) : c ^ 2 = L.z α := by
  have hord : orderOf c = 4 := by rw [← Nat.card_zpowers, ← hgen, hc]
  have hz : L.z α ∈ Subgroup.zpowers c := hgen ▸ D.z_mem_calpha F h h512
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hz2 : L.z α ^ 2 = 1 := by rw [pow_two]; exact L.z_mul_self D.val
  have hz1 : L.z α ≠ 1 := L.z_ne_one D.val
  have hmod : c ^ (k % 4) = L.z α := by
    rw [← hk]
    have := zpow_mod_orderOf c k
    rwa [hord, Nat.cast_ofNat] at this
  have h0 : 0 ≤ k % 4 := Int.emod_nonneg _ (by norm_num)
  have h4 : k % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hne : ∀ n : ℕ, 0 < n → n < 4 → c ^ n ≠ 1 := fun n hn hn4 h1 => by
    have := orderOf_le_of_pow_eq_one hn h1
    omega
  generalize k % 4 = m at hmod h0 h4
  interval_cases m
  · exact absurd (by simpa using hmod) hz1.symm
  · exfalso
    have h1 : c = L.z α := by simpa using hmod
    exact hne 2 (by norm_num) (by norm_num) (by rw [h1]; exact hz2)
  · simpa using hmod
  · exfalso
    have h3 : c ^ 3 = L.z α := by simpa using hmod
    have h6 : c ^ 6 = 1 := by
      calc c ^ 6 = (c ^ 3) ^ 2 := by rw [← pow_mul]
        _ = L.z α ^ 2 := by rw [h3]
        _ = 1 := hz2
    have := orderOf_dvd_of_pow_eq_one h6
    rw [hord] at this
    omega

end D10Set

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem c_mem_calpha : S.c ∈ S.D.calpha := by
  rw [S.gen]
  exact Subgroup.mem_zpowers _

theorem c_mem_nbrStab : S.c ∈ nbrStab Γ G S.α := (Subgroup.mem_inf.1 S.c_mem_calpha).1

theorem c_commutes_x : S.D.x * S.c = S.c * S.D.x :=
  Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 S.c_mem_calpha).2 S.D.x (by simp)

theorem c_mem_stabilizer (F : FanTree Γ G) : S.c ∈ MulAction.stabilizer G S.α :=
  F.nbrStab_le_stabilizer S.α S.c_mem_nbrStab

theorem conj_c_mem_calpha (F : FanTree Γ G) : S.w⁻¹ * S.c * S.w ∈ S.D.calpha := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have hw : S.w⁻¹ • S.α = S.α := inv_smul_eq_iff.2 (MulAction.mem_stabilizer_iff.1
      S.w_mem_stabilizer).symm
    have := nbrStab_conj_mem F hw S.c_mem_nbrStab
    simpa using this
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hx2 : S.D.x ^ 2 * (S.w⁻¹ * S.c * S.w) = (S.w⁻¹ * S.c * S.w) * S.D.x ^ 2 := by
      rw [← S.x_w]
      calc S.w⁻¹ * S.D.x * S.w * (S.w⁻¹ * S.c * S.w) = S.w⁻¹ * (S.D.x * S.c) * S.w := by group
        _ = S.w⁻¹ * (S.c * S.D.x) * S.w := by rw [S.c_commutes_x]
        _ = _ := by group
    have hx : S.D.x = (S.D.x ^ 2) ^ 3 := by
      rw [← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_add, S.D.x_pow_five, one_mul, pow_one]
    have h3 := (Commute.pow_left (show Commute (S.D.x ^ 2) (S.w⁻¹ * S.c * S.w) from hx2) 3).eq
    rwa [← hx] at h3

theorem conj_c (F : FanTree Γ G) (hc : Nat.card S.D.calpha = 4) :
    S.w⁻¹ * S.c * S.w = S.c ∨ S.w⁻¹ * S.c * S.w = S.c⁻¹ := by
  have hord : orderOf S.c = 4 := by rw [← Nat.card_zpowers, ← S.gen, hc]
  have hmem := S.conj_c_mem_calpha F
  rw [S.gen] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hord' : orderOf (S.w⁻¹ * S.c * S.w) = 4 := by
    have := (MulAut.conj S.w⁻¹).orderOf_eq S.c
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this, hord]
  have hmod : S.c ^ (k % 4) = S.w⁻¹ * S.c * S.w := by
    rw [← hk]
    have := zpow_mod_orderOf S.c k
    rwa [hord, Nat.cast_ofNat] at this
  have h0 : 0 ≤ k % 4 := Int.emod_nonneg _ (by norm_num)
  have h4 : k % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hc4 : S.c ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one S.c
  generalize k % 4 = m at hmod h0 h4
  interval_cases m
  · exfalso
    have h1 : S.w⁻¹ * S.c * S.w = 1 := by simpa using hmod.symm
    rw [h1, orderOf_one] at hord'
    omega
  · left
    simpa using hmod.symm
  · exfalso
    have h2 : S.c ^ 2 = S.w⁻¹ * S.c * S.w := by simpa using hmod
    have h4' : (S.w⁻¹ * S.c * S.w) ^ 2 = 1 := by
      rw [← h2, ← pow_mul]
      exact hc4
    have := orderOf_dvd_of_pow_eq_one h4'
    rw [hord'] at this
    omega
  · right
    have h3 : S.c ^ 3 = S.w⁻¹ * S.c * S.w := by simpa using hmod
    rw [← h3]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact hc4

theorem p1cRel_of (F : FanTree Γ G) (h : Fan71c F L) (h71a : Fan71a F L) (h512 : Fan512 F L)
    (h83c : Fan83c F L) (hc4 : Nat.card S.D.calpha = 4) :
    P1cRel S.D.x (L.z S.α) S.c S.yEta S.zMu1 where
  c2 := S.D.sq_eq_z_of_card_four F h h512 S.gen hc4
  yc := fun j => by
    have hne : S.D.calpha ≠ Subgroup.zpowers (L.z S.α) := by
      intro heq
      have h2 : Nat.card (Subgroup.zpowers (L.z S.α)) = 2 := by
        rw [Nat.card_zpowers]
        exact L.orderOf_z S.D.val
      rw [heq, h2] at hc4
      omega
    have hZ := S.D.isZ2Pair_translate F h S.isBeta.pair j
    have hcl := h83c S.α S.D hne j _ _ hZ
    have hyeq : S.yEta j = L.z (S.D.delta j) * L.z ((S.D.x ^ j.val)⁻¹ • S.η') :=
      S.D.y_eq F h (S.valence_eta' F) j
    rw [← hyeq] at hcl
    have hmem : fcomm (S.yEta j) S.c ∈ Subgroup.zpowers (L.z (S.D.alpha j)) := by
      rw [← hcl]
      exact Subgroup.subset_closure ⟨S.c, S.c_mem_calpha, rfl⟩
    have hzj : L.z (S.D.alpha j) * L.z (S.D.alpha j) = 1 := L.z_mul_self (S.D.valence_alpha F j)
    by_contra hne1
    have hone : fcomm (S.yEta j) S.c = 1 := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
      rcases zpow_invol hzj n with h1 | h1
      · rw [← hn, h1]
      · exact absurd (by rw [← hn, h1]; rfl) hne1
    have hcomm : Commute (S.yEta j) S.c := mul_comm_of_fcomm_eq_one hone
    have hall : Subgroup.closure {g | ∃ c' ∈ S.D.calpha, g = fcomm (S.yEta j) c'} ≤ ⊥ := by
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨c', hc', rfl⟩
      rw [S.gen] at hc'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
      exact fcomm_eq_one_of_mul_comm (hcomm.zpow_right k).eq
    rw [hcl] at hall
    have hz1 : L.z (S.D.alpha j) ∈ (⊥ : Subgroup G) := hall (Subgroup.mem_zpowers _)
    exact L.z_ne_one (S.D.valence_alpha F j) (Subgroup.mem_bot.1 hz1)
  zc := fun j => by
    have hfix := S.D.fix_of_mem_calpha F h71a h S.c_mem_calpha j (m := 2) (by norm_num)
    have := (h.comm_z_iff (S.D.valence_alpha F j) S.c).2 hfix
    exact fcomm_eq_one_of_mul_comm this.symm
  xc := fcomm_eq_one_of_mul_comm S.c_commutes_x
  cza := fcomm_eq_one_of_mul_comm (L.comm_z_of_mem_stabilizer S.D.val (S.c_mem_stabilizer F))

end Sec9Cfg

end CFSG.Quasithin.Fan86
