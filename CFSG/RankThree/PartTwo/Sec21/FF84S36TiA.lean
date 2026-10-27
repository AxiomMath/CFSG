module

public import CFSG.RankThree.PartTwo.Sec21.FF84S34
public import CFSG.RankThree.PartTwo.Sec21.FF84S36Gen

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

variable {G : Type} [Group G] [Finite G]

theorem S36_closure_bt {b t : G} (htt : t * t = 1) (htb : t * b * t⁻¹ = b⁻¹) {g : G}
    (hg : g ∈ Subgroup.closure ({b, t} : Set G)) :
    ∃ k : ℤ, g = b ^ k ∨ g = t * b ^ k := by
  have hbt : ∀ k : ℤ, b ^ k * t = t * b ^ (-k) := by
    intro k
    have h := conj_zpow (a := t) (b := b) (i := -k)
    rw [htb] at h
    have hc : (b⁻¹) ^ (-k) = b ^ k := by rw [inv_zpow, zpow_neg, inv_inv]
    rw [hc] at h
    have ht' : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, htt]
    rw [ht'] at h
    calc b ^ k * t = (t * b ^ (-k) * t) * t := by rw [← h]
      _ = t * b ^ (-k) := by simp only [mul_assoc, htt, mul_one]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, Or.inl (zpow_one x).symm⟩
    · exact ⟨0, Or.inr (by simp)⟩
  | one => exact ⟨0, Or.inl (zpow_zero b).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k, hk | hk⟩ := hx <;> obtain ⟨m, hm | hm⟩ := hy <;> subst hk <;> subst hm
    · exact ⟨k + m, Or.inl (zpow_add b k m).symm⟩
    · refine ⟨m - k, Or.inr ?_⟩
      calc b ^ k * (t * b ^ m) = (b ^ k * t) * b ^ m := by group
        _ = t * b ^ (m - k) := by
          rw [hbt]; rw [mul_assoc, ← zpow_add]; congr 2; ring
    · exact ⟨k + m, Or.inr (by rw [mul_assoc, ← zpow_add])⟩
    · refine ⟨m - k, Or.inl ?_⟩
      calc t * b ^ k * (t * b ^ m) = (t * (b ^ k * t)) * b ^ m := by group
        _ = (t * (t * b ^ (-k))) * b ^ m := by rw [hbt]
        _ = (t * t) * (b ^ (-k) * b ^ m) := by group
        _ = b ^ (m - k) := by rw [htt, one_mul, ← zpow_add]; congr 1; ring
  | inv x _ hx =>
    obtain ⟨k, hk | hk⟩ := hx <;> subst hk
    · exact ⟨-k, Or.inl (zpow_neg b k).symm⟩
    · refine ⟨k, Or.inr ?_⟩
      have hsq : t * b ^ k * (t * b ^ k) = 1 := by
        calc t * b ^ k * (t * b ^ k) = (t * (b ^ k * t)) * b ^ k := by group
          _ = (t * (t * b ^ (-k))) * b ^ k := by rw [hbt]
          _ = (t * t) * (b ^ (-k) * b ^ k) := by group
          _ = 1 := by rw [htt, ← zpow_add]; simp
      exact inv_eq_of_mul_eq_one_right hsq

theorem S36_invol_cen_mem_L {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t)
    (h31 : FF84_3_1) {x : G} (hxb : x ∈ Cen b) (hx2 : x * x = 1) : x ∈ L := by
  have hZ : Subgroup.center L = ⊥ := (h31 G b L B b₁ b₂ d.sec).2
  have hbL : Subgroup.zpowers b ⊓ L = ⊥ := zpowers_inf_eq_bot d.sec hZ
  have htt : t * t = 1 := by rw [← sq]; exact S36_sq_of_orderOf_two d.ht
  have hb3 : orderOf b = 3 := d.sec.hyp.ord
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb3
    norm_num at hb3
  have hcube : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  have hLC : L ≤ Cen b := d.sec.hyp.hLC
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
  ·
    subst hk
    have hbk : Commute (b ^ k) l := hcl.zpow_left k
    have hsq : (b ^ k * b ^ k) * (l * l) = 1 := by
      calc (b ^ k * b ^ k) * (l * l) = b ^ k * (b ^ k * l) * l := by group
        _ = b ^ k * (l * b ^ k) * l := by rw [hbk.eq]
        _ = b ^ k * l * (b ^ k * l) := by group
        _ = 1 := by rw [hgl]; exact hx2
    have hu : b ^ k * b ^ k = (l * l)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    have huL : b ^ k * b ^ k ∈ L := by rw [hu]; exact L.inv_mem (L.mul_mem hl hl)
    have huZ : b ^ k * b ^ k ∈ Subgroup.zpowers b := by
      rw [← zpow_add]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _
    have hu1 : b ^ k * b ^ k = 1 := by
      have hmem : b ^ k * b ^ k ∈ Subgroup.zpowers b ⊓ L := Subgroup.mem_inf.2 ⟨huZ, huL⟩
      rw [hbL] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hcube' : (b ^ k) ^ 3 = 1 := zpow_cube' hcube k
    have hk1 : b ^ k = 1 := by
      calc b ^ k = (b ^ k) ^ 3 * (b ^ k * b ^ k)⁻¹ := by group
        _ = 1 := by rw [hcube', hu1, inv_one, mul_one]
    rw [hk1, one_mul] at hgl
    rw [← hgl]
    exact hl
  ·
    subst hk
    exfalso
    have hct : Commute b t := by
      have e : t = t * b ^ k * (b ^ k)⁻¹ := by group
      rw [e]
      exact hcg.mul_right ((Commute.refl b).zpow_right k).inv_right
    have h1 : t * b * t⁻¹ = b := by rw [← hct.eq, mul_inv_cancel_right]
    have hbinv : b = b⁻¹ := h1.symm.trans d.htb
    have hbb : b * b = 1 := mul_eq_one_iff_eq_inv.2 hbinv
    apply hb1
    calc b = b ^ 3 * (b * b)⁻¹ := by group
      _ = 1 := by rw [hcube, hbb, inv_one, mul_one]

theorem S36_monomial_conj {b t bk bj n : G} (htt : t * t = 1) (htb : t * b * t⁻¹ = b⁻¹)
    (htk : t * bk = bk * t) (htj : t * bj = bj * t)
    (hnb : n * b * n⁻¹ = bk) (hnk : n * bk * n⁻¹ = b) (hnj : n * bj * n⁻¹ = bj) :
    (n * t * n⁻¹) * (n * t * n⁻¹) = 1 ∧ (n * t * n⁻¹) * b * (n * t * n⁻¹)⁻¹ = b ∧
      (n * t * n⁻¹) * bk * (n * t * n⁻¹)⁻¹ = bk⁻¹ ∧
      (n * t * n⁻¹) * bj * (n * t * n⁻¹)⁻¹ = bj := by
  have e1 : n⁻¹ * b * n = bk := by rw [← hnk]; group
  have e2 : n⁻¹ * bk * n = b := by rw [← hnb]; group
  have e3 : n⁻¹ * bj * n = bj := by
    calc n⁻¹ * bj * n = n⁻¹ * (n * bj * n⁻¹) * n := by rw [hnj]
      _ = bj := by group
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (n * t * n⁻¹) * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
      _ = 1 := by rw [htt]; group
  · calc (n * t * n⁻¹) * b * (n * t * n⁻¹)⁻¹ = n * (t * (n⁻¹ * b * n)) * t⁻¹ * n⁻¹ := by group
      _ = n * (t * bk) * t⁻¹ * n⁻¹ := by rw [e1]
      _ = n * (bk * t) * t⁻¹ * n⁻¹ := by rw [htk]
      _ = n * bk * n⁻¹ := by group
      _ = b := hnk
  · calc (n * t * n⁻¹) * bk * (n * t * n⁻¹)⁻¹ = n * (t * (n⁻¹ * bk * n)) * t⁻¹ * n⁻¹ := by group
      _ = n * (t * b) * t⁻¹ * n⁻¹ := by rw [e2]
      _ = n * (t * b * t⁻¹) * n⁻¹ := by group
      _ = n * b⁻¹ * n⁻¹ := by rw [htb]
      _ = (n * b * n⁻¹)⁻¹ := by group
      _ = bk⁻¹ := by rw [hnb]
  · calc (n * t * n⁻¹) * bj * (n * t * n⁻¹)⁻¹ = n * (t * (n⁻¹ * bj * n)) * t⁻¹ * n⁻¹ := by group
      _ = n * (t * bj) * t⁻¹ * n⁻¹ := by rw [e3]
      _ = n * (bj * t) * t⁻¹ * n⁻¹ := by rw [htj]
      _ = n * bj * n⁻¹ := by group
      _ = bj := hnj

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
