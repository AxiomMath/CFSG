module

public import CFSG.RankThree.PartTwo.Sec21.FF84S36TiA

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

variable {G : Type} [Group G] [Finite G]

theorem S36_cen_b_form {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t) {x : G}
    (hxb : x ∈ Cen b) : ∃ k : ℤ, ∃ l ∈ L, x = b ^ k * l := by
  have htt : t * t = 1 := by rw [← sq]; exact S36_sq_of_orderOf_two d.ht
  have hLC : L ≤ Cen b := d.sec.hyp.hLC
  have hb3 : orderOf b = 3 := d.sec.hyp.ord
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb3
    norm_num at hb3
  have hxN : x ∈ Nor (Subgroup.zpowers b) := S36_cen_le_nor b hxb
  rw [← d.hN] at hxN
  have hD : Subgroup.closure ({b, t} : Set G) ≤ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rcases hy with rfl | rfl
    · intro l hl; exact (S36_comm_of_cen (hLC hl)).symm
    · intro l hl; exact Subgroup.mem_centralizer_iff.1 d.htL l hl
  have hLN : Subgroup.closure ({b, t} : Set G) ≤ Nor L :=
    hD.trans (Subgroup.centralizer_le_normalizer _)
  have hx' : x ∈ ((Subgroup.closure ({b, t} : Set G) ⊔ L : Subgroup G) : Set G) := hxN
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLN, Set.mem_mul] at hx'
  obtain ⟨g, hg, l, hl, hgl⟩ := hx'
  have hcx : Commute b x := S36_comm_of_cen hxb
  have hcl : Commute b l := S36_comm_of_cen (hLC hl)
  have hgeq : g = x * l⁻¹ := by rw [← hgl]; group
  have hcg : Commute b g := by rw [hgeq]; exact hcx.mul_right hcl.inv_right
  obtain ⟨k, hk | hk⟩ := S36_closure_bt htt d.htb hg
  · exact ⟨k, l, hl, by rw [← hgl, hk]⟩
  ·
    exfalso
    rw [hk] at hcg
    have hct : Commute b t := by
      have e : t = t * b ^ k * (b ^ k)⁻¹ := by group
      rw [e]
      exact hcg.mul_right ((Commute.refl b).zpow_right k).inv_right
    have h1 : t * b * t⁻¹ = b := by rw [← hct.eq, mul_inv_cancel_right]
    have hbinv : b = b⁻¹ := h1.symm.trans d.htb
    have hbb : b * b = 1 := mul_eq_one_iff_eq_inv.2 hbinv
    have hcube : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
    apply hb1
    calc b = b ^ 3 * (b * b)⁻¹ := by group
      _ = 1 := by rw [hcube, hbb, inv_one, mul_one]

theorem S36_cen_b_two {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t)
    (h31 : FF84_3_1) {x : G} (hxb : x ∈ Cen b) {N : ℕ} (hN : x ^ N = 1)
    (hcop : Nat.Coprime N 3) : x ∈ L := by
  have hZ : Subgroup.center L = ⊥ := (h31 G b L B b₁ b₂ d.sec).2
  have hbL : Subgroup.zpowers b ⊓ L = ⊥ := zpowers_inf_eq_bot d.sec hZ
  have hb3 : orderOf b = 3 := d.sec.hyp.ord
  have hcube : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  have hLC : L ≤ Cen b := d.sec.hyp.hLC
  obtain ⟨k, l, hl, rfl⟩ := S36_cen_b_form d hxb
  have hcl : Commute b l := S36_comm_of_cen (hLC hl)
  have hc : Commute (b ^ k) l := hcl.zpow_left k
  have hpow : (b ^ k) ^ N * l ^ N = 1 := by rw [← hc.mul_pow]; exact hN
  have hu : (b ^ k) ^ N = (l ^ N)⁻¹ := eq_inv_of_mul_eq_one_left hpow
  have huL : (b ^ k) ^ N ∈ L := by rw [hu]; exact L.inv_mem (L.pow_mem hl N)
  have huZ : (b ^ k) ^ N ∈ Subgroup.zpowers b :=
    pow_mem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k) N
  have hu1 : (b ^ k) ^ N = 1 := by
    have hmem := Subgroup.mem_inf.2 ⟨huZ, huL⟩
    rw [hbL] at hmem
    exact Subgroup.mem_bot.1 hmem
  have h3 : (b ^ k) ^ 3 = 1 := zpow_cube' hcube k
  have hord1 : orderOf (b ^ k) ∣ N := orderOf_dvd_of_pow_eq_one hu1
  have hord2 : orderOf (b ^ k) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hone : orderOf (b ^ k) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord1 hcop) hord2
  have hbk : b ^ k = 1 := orderOf_eq_one_iff.1 hone
  rw [hbk, one_mul]
  exact hl

theorem S36_op2_map_le (c : G ≃* G) (H : Subgroup G) :
    Op 2 (H.map c.toMonoidHom) ≤ (Op 2 H).map c.toMonoidHom := by
  set W := Op 2 (H.map c.toMonoidHom) with hW
  have hWle : W ≤ H.map c.toMonoidHom := S36_op2_le _
  have hWp : IsPGroup 2 ↥(W.map c.symm.toMonoidHom) := IsPGroup.map (S36_op2_isPGroup _) _
  have hNH : W.map c.symm.toMonoidHom ≤ H := by
    rintro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨h, hh, hhw⟩ := Subgroup.mem_map.1 (hWle hw)
    have : c.symm w = h := by
      rw [← hhw]; simp
    show c.symm w ∈ H
    rw [this]
    exact hh
  have hN : ((W.map c.symm.toMonoidHom).subgroupOf H).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨w, hw, hwn⟩ := Subgroup.mem_map.1 hn
    have hgc : c (g : G) ∈ H.map c.toMonoidHom := Subgroup.mem_map_of_mem _ g.2
    have hcon := S36_op2_conj hgc hw
    refine Subgroup.mem_map.2 ⟨_, hcon, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hwn]
    simp [map_mul, map_inv]
  have hle := S36_op2_of_normal hNH hN hWp
  intro x hx
  have hx' : c.symm x ∈ W.map c.symm.toMonoidHom := Subgroup.mem_map_of_mem _ hx
  have hcs := hle hx'
  exact Subgroup.mem_map.2 ⟨c.symm x, hcs, by simp⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
