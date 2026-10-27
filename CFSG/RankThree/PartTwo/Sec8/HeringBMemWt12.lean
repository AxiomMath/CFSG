module

public import CFSG.RankThree.PartTwo.Sec8.HeringBMemVec
public import CFSG.RankThree.PartTwo.Sec8.HeringBMemLin
public import CFSG.RankThree.PartTwo.Sec8.HeringBMemFree

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringBMem

open CFSG.RankThree.PartTwo.Sec8.Item8KFacts3 CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
  CFSG.RankThree.PartTwo.Sec4.Item434Kit CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

theorem vAct_comm' {q z : H6} (h : q * z = z * q) (y : Fin 6 → ZMod 2) :
    vAct z (vAct q y) = vAct q (vAct z y) := by
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, ← map_mul, ← h]

theorem rank_one_of_decomp {Q : Subgroup H6} {z : H6} (hQ8 : Nat.card Q = 8) (hzQ : z ∈ Q)
    (hz1 : z ≠ 1) (hz : ∀ q ∈ Q, q ≠ 1 → q = z ∨ q ^ 2 = z) (l : Fin 3)
    (hSm : ∀ q ∈ Q, ∀ y ∈ Pl l, vAct q y ∈ Pl l)
    (hBg : ∀ q ∈ Q, ∀ y ∈ Pp l, vAct q y ∈ Pp l) :
    ∃ a : Fin 6 → ZMod 2, a ≠ 0 ∧ ∀ y, vAct z y = y ∨ vAct z y = y + a := by
  classical
  have hcomm : ∀ q ∈ Q, q * z = z * q := (quat_z_central hQ8 hzQ hz1 hz).2
  have hF1 : ∀ y ∈ Pl l, vAct z y = y :=
    fixed_of_card_lt_eight vAct hQ8 hzQ hz hz1 (Pl l) hSm (by rw [card_Pl]; norm_num)
  set S : Finset (Fin 6 → ZMod 2) := (Pp l).filter fun y => ¬ vAct z y = y with hS
  have hSinv : ∀ q ∈ Q, ∀ y ∈ S, vAct q y ∈ S := by
    intro q hq y hy
    obtain ⟨hyB, hyz⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_filter.mpr ⟨hBg q hq y hyB, fun h => hyz ?_⟩
    rw [vAct_comm' (hcomm q hq)] at h
    exact (vAct q).injective h
  have h8 : 8 ∣ S.card :=
    eight_dvd_card_of_free vAct hQ8 hz S hSinv (fun y hy => (Finset.mem_filter.mp hy).2)
  have hlt : S.card < 16 := by
    have h := Finset.card_lt_card (s := S) (t := Pp l)
      ⟨Finset.filter_subset _ _, fun hsub => by
        have h0 := (Finset.mem_filter.mp (hsub (zero_mem_Pp l))).2
        exact h0 (vAct_zero z)⟩
    rwa [card_Pp] at h
  have hne : S.card ≠ 0 := by
    intro h0
    have hSe : S = ∅ := Finset.card_eq_zero.mp h0
    have hB : ∀ b ∈ Pp l, vAct z b = b := by
      intro b hb
      by_contra hbz
      have : b ∈ S := Finset.mem_filter.mpr ⟨hb, hbz⟩
      rw [hSe] at this
      exact Finset.notMem_empty b this
    have hall : ∀ y, vAct z y = y := by
      intro y
      obtain ⟨s, hs, b, hb, rfl⟩ := decomp_plane l y
      rw [vAct_add, hF1 s hs, hB b hb]
    apply hz1
    apply vAct_injective
    exact Equiv.ext fun y => by rw [hall y, map_one, Equiv.Perm.one_apply]
  have hS8 : S.card = 8 := by
    obtain ⟨k, hk⟩ := h8
    omega
  have hK : ((Pp l).filter fun b => vAct z b = b).card = 8 := by
    have h := Finset.card_filter_add_card_filter_not (s := Pp l) (fun b => vAct z b = b)
    rw [card_Pp] at h
    have : (Pp l).filter (fun b => ¬ vAct z b = b) = S := rfl
    rw [this, hS8] at h
    omega
  exact rank_one_of_half (fun y => vAct z y) (vAct_add z) (Pl l) (Pp l) (decomp_plane l) hF1
    (fun b hb b' hb' => Pp_add hb hb') (card_Pp l) hK


theorem no_wt12 {x : Fin 3 → ZMod 3} {Q : Subgroup H6} {z : H6}
    (hx : (∃ k, x k ≠ 0 ∧ ∀ i, i ≠ k → x i = 0) ∨ (∃ l, x l = 0 ∧ ∀ i, i ≠ l → x i ≠ 0))
    (hQv : ∀ q ∈ Q, q * vecElt zH x = vecElt zH x * q) (hQ8 : Nat.card Q = 8) (hzQ : z ∈ Q)
    (hz1 : z ≠ 1) (hz : ∀ q ∈ Q, q ≠ 1 → q = z ∨ q ^ 2 = z) : False := by
  classical
  have hcomm : ∀ q ∈ Q, ∀ y, wAct x (vAct q y) = vAct q (wAct x y) := by
    intro q hq y
    have h := vAct_comm' (hQv q hq) y
    rwa [vAct_vecElt, vAct_vecElt] at h
  obtain ⟨l, hSm, hBg⟩ : ∃ l : Fin 3, (∀ q ∈ Q, ∀ y ∈ Pl l, vAct q y ∈ Pl l) ∧
      (∀ q ∈ Q, ∀ y ∈ Pp l, vAct q y ∈ Pp l) := by
    have hsub : ∀ q ∈ Q, ∀ y₁, vAct q (wAct x y₁ - y₁) = wAct x (vAct q y₁) - vAct q y₁ := by
      intro q hq y₁
      rw [vAct_sub, hcomm q hq]
    rcases hx with ⟨k, hk, hk0⟩ | ⟨l, hl, hl0⟩
    · obtain ⟨hPl, hPp⟩ := wt1_check x k hk hk0
      refine ⟨k, fun q hq y hy => ?_, fun q hq y hy => ?_⟩
      · rw [hPl, Finset.mem_image] at hy ⊢
        obtain ⟨y₁, -, rfl⟩ := hy
        exact ⟨vAct q y₁, Finset.mem_univ _, (hsub q hq y₁).symm⟩
      · rw [hPp, Finset.mem_filter] at hy ⊢
        exact ⟨Finset.mem_univ _, by rw [hcomm q hq, hy.2]⟩
    · obtain ⟨hPl, hPp⟩ := wt2_check x l hl hl0
      refine ⟨l, fun q hq y hy => ?_, fun q hq y hy => ?_⟩
      · rw [hPl, Finset.mem_filter] at hy ⊢
        exact ⟨Finset.mem_univ _, by rw [hcomm q hq, hy.2]⟩
      · rw [hPp, Finset.mem_image] at hy ⊢
        obtain ⟨y₁, -, rfl⟩ := hy
        exact ⟨vAct q y₁, Finset.mem_univ _, (hsub q hq y₁).symm⟩
  obtain ⟨a, ha, hr⟩ := rank_one_of_decomp hQ8 hzQ hz1 hz l hSm hBg
  obtain ⟨xq, hxq, hx1, hxz⟩ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ z := by
    by_contra hcon
    push Not at hcon
    have hsub : (Q : Set H6) ⊆ {1, z} := by
      intro q hq
      by_cases h1 : q = 1
      · exact Or.inl h1
      · exact Or.inr (hcon q hq h1)
    have h2 : Nat.card Q ≤ 2 := by
      have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h4 : ({1, z} : Set H6).ncard ≤ 2 := by
        refine (Set.ncard_insert_le 1 {z}).trans ?_
        rw [Set.ncard_singleton]
      rw [← Nat.card_coe_set_eq] at h3 h4
      exact h3.trans h4
    omega
  have hsq : xq * xq = z := by
    rcases hz xq hxq hx1 with h | h
    · exact absurd h hxz
    · rw [← pow_two]
      exact h
  have hZ : ∀ y, vAct z y = vAct xq (vAct xq y) := fun y => by
    rw [← hsq, map_mul, Equiv.Perm.mul_apply]
  refine tv_core bF bF_add_left bF_add_right bF_symm bF_self bF_nondeg (⇑(vAct xq))
    (vAct_add xq) (vAct xq).injective (bF_vAct xq) a ha (fun y => ?_) ?_
  · rw [← hZ]
    exact hr y
  · by_contra hcon
    push Not at hcon
    apply hz1
    apply vAct_injective
    exact Equiv.ext fun y => by rw [hZ, show vAct xq (vAct xq y) = y from hcon y, map_one,
      Equiv.Perm.one_apply]

end CFSG.RankThree.PartTwo.Sec8.HeringBMem
