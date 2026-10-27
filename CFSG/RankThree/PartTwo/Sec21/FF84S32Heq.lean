module

public import CFSG.RankThree.PartTwo.Sec21.FF84S32Cd
public import CFSG.GH74.GLS.Balance.Bender.T59
public import CFSG.RankThree.PartTwo.Sec21.FF84S32Fus

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.GH74.GLS.Balance (IsSylowIn)
open CFSG.Assembly (InCatalog)

section Helpers
variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_of_card {p : ℕ} [Fact p.Prime] {P N : Subgroup G} (hPN : P ≤ N) {a m : ℕ}
    (hP : Nat.card P = p ^ a) (hN : Nat.card N = p ^ a * m) (hm : ¬ p ∣ m) : IsSylowIn p P N := by
  refine ⟨hPN, IsPGroup.of_card hP, fun S hSN hS => ?_⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS
  have hdvd : p ^ k ∣ p ^ a * m := hN ▸ hk ▸ Subgroup.card_dvd_of_le hSN
  have hcop : Nat.Coprime (p ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hm)
  rw [hk, hP]
  exact Nat.le_of_dvd (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) a) (hcop.dvd_of_dvd_mul_right hdvd)

theorem nor_cenS {A : Subgroup G} {g x : G} (hg : g ∈ Nor A) (hx : x ∈ CenS A) :
    g * x * g⁻¹ ∈ CenS A := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : g⁻¹ * a * g ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * a * g)).2 (by
      rw [show g * (g⁻¹ * a * g) * g⁻¹ = a by group]; exact ha)
    exact this
  have hc := Subgroup.mem_centralizer_iff.1 hx _ ha'
  rw [show a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ by group,
    show (g * x * g⁻¹) * a = g * (x * (g⁻¹ * a * g)) * g⁻¹ by group, hc]

theorem K_le_O3 {K H : Subgroup G} (hKH : K ≤ H) (hKs : IsSimpleGroup ↥K) (h60 : Nat.card K = 60) :
    K ≤ O3 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : O3 K ≤ O3 H := Subgroup.closure_mono (fun x hx => ⟨hKH hx.1, hx.2⟩)
  haveI := O3_normal_sub K
  have hne : (O3 K).subgroupOf K ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 (by rw [h60]; norm_num)
    intro hbot
    have hx1 : (x : G) ∈ O3 K :=
      Subgroup.subset_closure ⟨x.2, by rw [Subgroup.orderOf_coe, hx]; norm_num⟩
    have : x ∈ (O3 K).subgroupOf K := hx1
    rw [hbot, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hx
    norm_num at hx
  have htop := (hKs.eq_bot_or_eq_top_of_normal _).resolve_left hne
  exact (Subgroup.subgroupOf_eq_top.1 htop).trans hT

end Helpers

section Main
variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem zpowers_inf_zpowers_d (h : FF84Sec3 b L B b₁ b₂) :
    Subgroup.zpowers (b₁ * b₂ ^ 2) ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxd, hxb⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hdx : b₁ * b₂ ^ 2 ∈ Subgroup.zpowers x :=
    mem_zpowers_of_mem_zpowers_ne_one hxd (d_pow3 h) (d_ne_one h) hx1
  exact d_notin_zpowers_b h
    ((Subgroup.zpowers_le.2 hxb) hdx)

theorem card_zpowers_d (h : FF84Sec3 b L B b₁ b₂) :
    Nat.card ↥(Subgroup.zpowers (b₁ * b₂ ^ 2)) = 3 := by
  rw [Nat.card_zpowers, orderOf_eq_prime (d_pow3 h) (d_ne_one h)]

theorem card_zpowers_b (h : FF84Sec3 b L B b₁ b₂) : Nat.card ↥(Subgroup.zpowers b) = 3 := by
  rw [Nat.card_zpowers, h.hyp.ord]

theorem O3_ne_top (h : FF84Sec3 b L B b₁ b₂) : O3 (Cen (b₁ * b₂)) ≠ ⊤ := by
  intro htop
  exact c_notin_O3 h (htop ▸ Subgroup.mem_top _)

theorem S2_H_eq (hQ : LemmaQ) (h : FF84Sec3 b L B b₁ b₂)
    (hX : Opp 3 (Cen b) = ⊥) (hZ : Subgroup.center L = ⊥) :
    setMul (Opp 3 (Cen (b₁ * b₂))) (Nor (Subgroup.zpowers b) ⊓ O3 (Cen (b₁ * b₂))) =
      O3 (Cen (b₁ * b₂)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hKle, hK60, hKs, hdK, -, -, hKinv⟩ := M1_K h hZ
  obtain ⟨hsylP, hcH⟩ := S2_Sylow_H h
  obtain ⟨hbH, hdH⟩ := S2_mem_H h
  set H := O3 (Cen (b₁ * b₂)) with hH
  set S := Opp 3 (Cen (b₁ * b₂)) with hS
  set P := Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2) with hP
  have hKL : K ≤ L := hKle.trans inf_le_left
  have hKc : K ≤ Cen (b₁ * b₂) := hKle.trans inf_le_right
  have hKb : K ≤ Cen b := hKL.trans h.hyp.hLC
  have hKH : K ≤ H := K_le_O3 hKc hKs hK60
  have hSH' : Opp 3 H = S := (B_Opp_O3 (Cen (b₁ * b₂))).symm
  have hSH : S ≤ H := by
    rw [← hSH']; exact Opp3_le _
  have hKgroup : CFSG.KCore.KGroupNonab InCatalog ↥H := B_kgroup h.hyp.iii H (O3_ne_top h)
  have hKcen : K ≤ H ⊓ CenS (Subgroup.zpowers b) := by
    refine le_inf hKH ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 (hKb hx)
    exact (Commute.zpow_left (show Commute b x from hxb.symm) j).eq
  have hKnorm : (K.subgroupOf (H ⊓ CenS (Subgroup.zpowers b))).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨hgH, hgC⟩ := Subgroup.mem_inf.1 g.2
    have hgb : (g : G) ∈ Cen b := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hgC b (Subgroup.mem_zpowers b)).symm
    have hgc : (g : G) ∈ Cen (b₁ * b₂) := O3_le _ hgH
    have := hKinv g (Subgroup.mem_inf.2 ⟨hgb, hgc⟩)
    have hmem : (g : G) * (k : G) * (g : G)⁻¹ ∈ conjBy (g : G) K :=
      Subgroup.mem_map.2 ⟨k, hk, by simp⟩
    rw [this] at hmem
    simpa using hmem
  have hQres := hQ G H P (Subgroup.zpowers (b₁ * b₂ ^ 2)) (Subgroup.zpowers b) K hKgroup hsylP
    (card_P h) le_sup_right le_sup_left (card_zpowers_d h) (card_zpowers_b h)
    (zpowers_inf_zpowers_d h) hKcen hKnorm hK60 hKs (Subgroup.zpowers_le.2 hdK) (S2_not_conj h)
  rw [hSH'] at hQres
  obtain ⟨hMH, hMn⟩ := hQres
  have hSsyl : IsSylowIn 3 (⊥ : Subgroup G) S := by
    refine isSylowIn_of_card bot_le (a := 0) (m := Nat.card S) ?_ ?_ ?_
    · simp
    · simp
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (card_Opp3_coprime _)
  have hdsyl : IsSylowIn 3 (Subgroup.zpowers (b₁ * b₂ ^ 2)) K := by
    refine isSylowIn_of_card (Subgroup.zpowers_le.2 hdK) (a := 1) (m := 20) ?_ ?_ ?_
    · rw [card_zpowers_d h]; norm_num
    · rw [hK60]; norm_num
    · norm_num
  have hsylM : IsSylowIn 3 (Subgroup.zpowers (b₁ * b₂ ^ 2)) (K ⊔ S) := by
    have := CFSG.GH74.GLS.Balance.BenderExt.isSylowIn_sup_of_le_normalizer (p := 3)
      (N := S) (M₀ := K) (M := S ⊔ K) (P := ⊥) (R := Subgroup.zpowers (b₁ * b₂ ^ 2)) rfl
      (fun k hk => mem_Nor_Opp3 (hKc hk)) hSsyl hdsyl (fun x _ => Subgroup.mem_centralizer_iff.2 (fun y hy => by
        simp at hy; subst hy; simp))
    rw [bot_sup_eq, sup_comm] at this
    exact this
  have hfr1 := CFSG.GH74.GLS.Balance.t59_frattini (p := 3) (X := H) (N := K ⊔ S)
    (P := Subgroup.zpowers (b₁ * b₂ ^ 2)) hMH hMn hsylM
  set N₁ := H ⊓ Nor (Subgroup.zpowers (b₁ * b₂ ^ 2)) with hN₁
  set C₁ := H ⊓ CenS (Subgroup.zpowers (b₁ * b₂ ^ 2)) with hC₁
  set W := Nor (Subgroup.zpowers b) ⊓ H with hW
  have hC₁N₁ : C₁ ≤ N₁ :=
    inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hC₁norm : (C₁.subgroupOf N₁).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hgH, hgN⟩ := Subgroup.mem_inf.1 g.2
    refine Subgroup.mem_inf.2 ⟨?_, nor_cenS hgN hxC⟩
    have := mul_mem (mul_mem hgH hxH) (inv_mem hgH)
    simpa using this
  have hPC₁ : IsSylowIn 3 P C₁ := by
    obtain ⟨hPH, hP2, hPmax⟩ := isSylowOf_iff_isSylowIn.1 hsylP
    refine ⟨?_, hP2, fun T hT hT3 => hPmax T (hT.trans inf_le_left) hT3⟩
    refine le_inf hPH ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((comm_of_mem_B h (P_le_B h hx) (d_mem_B h)).zpow_right j).eq.symm
  have hfr2 := CFSG.GH74.GLS.Balance.t59_frattini (p := 3) (X := N₁) (N := C₁) (P := P)
    hC₁N₁ hC₁norm hPC₁
  have hC₁W : C₁ ≤ W := by
    intro x hx
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨?_, hxH⟩
    have hxd : x ∈ Cen (b₁ * b₂ ^ 2) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hxC _ (Subgroup.mem_zpowers _)).symm
    exact (M2_norm h hZ).2 (cen_E_of_cen_c_d h (O3_le _ hxH) hxd)
  have hN₁W : N₁ ≤ W := by
    refine hfr2.trans (sup_le hC₁W ?_)
    intro x hx
    obtain ⟨hxN, hxP⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨S2_N_P_le h hxP, (Subgroup.mem_inf.1 hxN).1⟩
  have hKW : K ≤ W := le_inf (fun x hx =>
    mem_nor_zpowers_of_conj (Or.inl (mem_Cen_iff.1 (hKb hx)))) hKH
  have hWS : W ≤ Nor S := fun w hw => mem_Nor_Opp3 (O3_le _ (Subgroup.mem_inf.1 hw).2)
  have hHle : H ≤ S ⊔ W := by
    refine hfr1.trans (sup_le (sup_le (hKW.trans le_sup_right) le_sup_left) ?_)
    exact hN₁W.trans le_sup_right
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left S W hWS
  ext x
  constructor
  · rintro ⟨s, hs, w, hw, rfl⟩
    exact mul_mem (hSH hs) (Subgroup.mem_inf.1 hw).2
  · intro hx
    have : x ∈ ((S ⊔ W : Subgroup G) : Set G) := hHle hx
    rw [hcoe] at this
    obtain ⟨s, hs, w, hw, hsw⟩ := this
    exact ⟨s, hs, w, hw, hsw.symm⟩

end Main

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
