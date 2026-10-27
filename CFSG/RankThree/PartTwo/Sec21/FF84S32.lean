module

public import CFSG.RankThree.PartTwo.Sec21.FF84S32Heq
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaQ
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaHHolds

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.GH74.GLS.Balance (IsSylowIn)

section Helpers
variable {G : Type} [Group G] [Finite G]

theorem closure_pair_eq_sup (x y : G) :
    Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · exact sup_le (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))
      (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))

theorem mem_Nor_closure_pair {x y g : G} (hgx : g ∈ Nor (Subgroup.zpowers x))
    (hgy : g ∈ Nor (Subgroup.zpowers y)) : g ∈ Nor (Subgroup.closure ({x, y} : Set G)) := by
  have key : ∀ g : G, g ∈ Nor (Subgroup.zpowers x) → g ∈ Nor (Subgroup.zpowers y) →
      ∀ k ∈ Subgroup.closure ({x, y} : Set G), g * k * g⁻¹ ∈ Subgroup.closure ({x, y} : Set G) := by
    intro g hgx hgy k hk
    induction hk using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · exact (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)) :
          Subgroup.zpowers z ≤ _) ((Subgroup.mem_normalizer_iff.1 hgx z).1 (Subgroup.mem_zpowers z))
      · have hz : z ∈ ({x, z} : Set G) := by simp
        exact (Subgroup.zpowers_le.2 (Subgroup.subset_closure hz) :
          Subgroup.zpowers z ≤ _) ((Subgroup.mem_normalizer_iff.1 hgy z).1 (Subgroup.mem_zpowers z))
    | one => simp
    | mul u v _ _ hu hv =>
      rw [show g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) by group]
      exact mul_mem hu hv
    | inv u _ hu =>
      rw [show g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ by group]
      exact inv_mem hu
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨key g hgx hgy k, fun hk => ?_⟩
  have := key g⁻¹ (inv_mem hgx) (inv_mem hgy) _ hk
  simpa [mul_assoc] using this

theorem Cen_eq_CenS_zpowers (x : G) : Cen x = CenS (Subgroup.zpowers x) := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have : Commute x g := (Subgroup.mem_centralizer_singleton_iff.1 hg).symm
    exact (Commute.zpow_left this j).eq
  · intro hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hg x (Subgroup.mem_zpowers x)).symm

theorem mem_Nor_Cen_of_Nor_zpowers {x g : G} (hg : g ∈ Nor (Subgroup.zpowers x)) :
    g ∈ Nor (Cen x) := by
  have key : ∀ g : G, g ∈ Nor (Subgroup.zpowers x) → ∀ y ∈ Cen x, g * y * g⁻¹ ∈ Cen x := by
    intro g hg y hy
    rw [Cen_eq_CenS_zpowers] at hy ⊢
    exact nor_cenS hg hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem Opp3_conj_of_nor (K : Subgroup G) {h : G} (hh : h ∈ Nor K) :
    ∀ m ∈ Opp 3 K, h * m * h⁻¹ ∈ Opp 3 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro m hm
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hm
  let α : MulAut K := K.normalizerMonoidHom ⟨h, hh⟩
  have hmap := pPrimeCore_map_iso 3 α
  have hmem : α y ∈ pPrimeCore 3 K := by
    rw [← hmap]
    exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩
  refine Subgroup.mem_map.2 ⟨α y, hmem, ?_⟩
  have h5 : ((α y : K) : G) = h * (y : G) * h⁻¹ := by
    show ((K.normalizerMonoidHom ⟨h, hh⟩ y : K) : G) = h * (y : G) * h⁻¹
    simp
  exact h5

theorem mem_Nor_Opp3_of_Nor {K : Subgroup G} {g : G} (hg : g ∈ Nor K) : g ∈ Nor (Opp 3 K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨Opp3_conj_of_nor K hg m, fun hm => ?_⟩
  have := Opp3_conj_of_nor K (inv_mem hg) _ hm
  simpa [mul_assoc] using this

theorem conj_mem_O3 {X : Subgroup G} {y : G} (hy : ∀ x ∈ X, y * x * y⁻¹ ∈ X) :
    ∀ g ∈ O3 X, y * g * y⁻¹ ∈ O3 X := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    have hord : orderOf (y * x * y⁻¹) = orderOf x :=
      orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective x
    exact ⟨hy x hx.1, by rw [hord]; exact hx.2⟩
  | one => simp
  | mul u v _ _ hu hv =>
    rw [show y * (u * v) * y⁻¹ = (y * u * y⁻¹) * (y * v * y⁻¹) by group]
    exact mul_mem hu hv
  | inv u _ hu =>
    rw [show y * u⁻¹ * y⁻¹ = (y * u * y⁻¹)⁻¹ by group]
    exact inv_mem hu

end Helpers

section Main
variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem zpow_c (h : FF84Sec3 b L B b₁ b₂) (i : ℤ) :
    (b₁ * b₂) ^ i = b ^ (0 : ℤ) * b₁ ^ i * b₂ ^ i := by
  have hc : Commute b₁ b₂ := comm_of_mem_B h (mem_B_b₁ h) (mem_B_b₂ h)
  rw [hc.mul_zpow]
  simp

theorem K0_conj_c (h : FF84Sec3 b L B b₁ b₂) {n : G}
    (hn : n ∈ Nor (Subgroup.closure ({b, b₁ * b₂} : Set G))) :
    n * (b₁ * b₂) * n⁻¹ ∈ Subgroup.zpowers (b₁ * b₂) := by
  have hcK : b₁ * b₂ ∈ Subgroup.closure ({b, b₁ * b₂} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hx : n * (b₁ * b₂) * n⁻¹ ∈ Subgroup.closure ({b, b₁ * b₂} : Set G) :=
    (Subgroup.mem_normalizer_iff.1 hn _).1 hcK
  rw [closure_pair_eq_sup] at hx
  obtain ⟨i, j, hij⟩ := exists_zpow_mul_of_mem_sup (comm_of_mem_B h (mem_B_b h) (c_mem_B h)) hx
  have hxB : n * (b₁ * b₂) * n⁻¹ ∈ B := by
    rw [hij]
    exact mul_mem (Subgroup.zpow_mem _ (mem_B_b h) _) (Subgroup.zpow_mem _ (c_mem_B h) _)
  obtain ⟨m, hm, hmc⟩ := h.fus (b₁ * b₂) (c_mem_B h) _ hxB n rfl
  have hv := h.mono.2.2.1 m hm b₁ (by simp)
  have hw := h.mono.2.2.1 m hm b₂ (by simp)
  have hvw : (m * b₁ * m⁻¹) * (m * b₂ * m⁻¹) = n * (b₁ * b₂) * n⁻¹ := by rw [← hmc]; group
  have hne : m * b₁ * m⁻¹ ≠ m * b₂ * m⁻¹ := by
    intro e
    have e' : b₁ = b₂ := by
      calc b₁ = m⁻¹ * (m * b₁ * m⁻¹) * m := by group
        _ = m⁻¹ * (m * b₂ * m⁻¹) * m := by rw [e]
        _ = b₂ := by group
    exact b₁b₂inv_ne_one h (by rw [e']; group)
  have hi : (3 : ℤ) ∣ i := by
    by_contra hi
    obtain ⟨a, c, d, hva, hcase⟩ := six_coord hv
    obtain ⟨a', c', d', hwa, hcase'⟩ := six_coord hw
    have hco : b ^ (a + a') * b₁ ^ (c + c') * b₂ ^ (d + d') =
        b ^ (i + 0) * b₁ ^ (0 + j) * b₂ ^ (0 + j) := by
      rw [← cmul h, ← hva, ← hwa, hvw, hij, zpow_c h, ← cmul h]
      simp
    obtain ⟨e1, e2, e3⟩ := (ceq h).1 hco
    rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hcase' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      first | omega | exact hne (hva.trans hwa.symm)
  rw [hij, zpow_eq_one_of_dvd3 (pow3_of_mem_B h (mem_B_b h)) hi, one_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

theorem nor_K0_le_nor_c (h : FF84Sec3 b L B b₁ b₂) :
    Nor (Subgroup.closure ({b, b₁ * b₂} : Set G)) ≤ Nor (Subgroup.zpowers (b₁ * b₂)) := by
  intro n hn
  have h1 := K0_conj_c h hn
  have h2 := K0_conj_c h (inv_mem hn)
  exact M2_mem_nor_zpowers n (b₁ * b₂) h1 h2

theorem Cen_le_nor_c (x : G) : Cen x ≤ Nor (Subgroup.zpowers x) := fun g hg =>
  mem_nor_zpowers_of_conj (Or.inl (mem_Cen_iff.1 hg))

theorem S2_final (hQ : LemmaQ) (h : FF84Sec3 b L B b₁ b₂)
    (hX : Opp 3 (Cen b) = ⊥) (hZ : Subgroup.center L = ⊥) :
    setMul (Opp 3 (Cen (b₁ * b₂))) (Nor (Subgroup.closure {b, b₁ * b₂})) =
      Nor (Subgroup.zpowers (b₁ * b₂)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHeq := S2_H_eq hQ h hX hZ
  obtain ⟨hsylP, -⟩ := S2_Sylow_H h
  set S := Opp 3 (Cen (b₁ * b₂)) with hS
  set H := O3 (Cen (b₁ * b₂)) with hH
  set K₀ := Subgroup.closure ({b, b₁ * b₂} : Set G) with hK₀
  set Y := Nor (Subgroup.zpowers (b₁ * b₂)) with hY
  have hbK : ∀ g, g ∈ Nor (Subgroup.zpowers b) → g ∈ Nor (Subgroup.zpowers (b₁ * b₂)) →
      g ∈ Nor K₀ := fun g h1 h2 => mem_Nor_closure_pair h1 h2
  ext x
  constructor
  · rintro ⟨s, hs, n, hn, rfl⟩
    exact mul_mem (Cen_le_nor_c _ (Opp3_le _ hs)) (nor_K0_le_nor_c h hn)
  · intro hx
    have hHY : H ≤ Y := (O3_le _).trans (Cen_le_nor_c _)
    have hHn : (H.subgroupOf Y).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hgN : (g : G) ∈ Nor (Cen (b₁ * b₂)) := mem_Nor_Cen_of_Nor_zpowers g.2
      exact conj_mem_O3 (fun x hx => (Subgroup.mem_normalizer_iff.1 hgN x).1 hx) _ hn
    have hfr := CFSG.GH74.GLS.Balance.t59_frattini (p := 3) (X := Y) (N := H)
      (P := Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2)) hHY hHn
      (isSylowOf_iff_isSylowIn.1 hsylP)
    have hT1 : H ≤ S ⊔ Nor K₀ := by
      intro y hy
      have : y ∈ setMul S (Nor (Subgroup.zpowers b) ⊓ H) := by rw [hHeq]; exact hy
      obtain ⟨s, hs, w, hw, rfl⟩ := this
      obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
      exact mul_mem (Subgroup.mem_sup_left hs)
        (Subgroup.mem_sup_right (hbK w hw1 (Cen_le_nor_c _ (O3_le _ hw2))))
    have hT2 : Y ⊓ Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2)) ≤ S ⊔ Nor K₀ := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
      exact Subgroup.mem_sup_right (hbK y (S2_N_P_le h hy2) hy1)
    have hxT : x ∈ S ⊔ Nor K₀ := (sup_le hT1 hT2) (hfr hx)
    have hle : Nor K₀ ≤ Nor S := fun n hn =>
      mem_Nor_Opp3_of_Nor (mem_Nor_Cen_of_Nor_zpowers (nor_K0_le_nor_c h hn))
    have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left S (Nor K₀) hle
    have : x ∈ ((S ⊔ Nor K₀ : Subgroup G) : Set G) := hxT
    rw [hcoe] at this
    obtain ⟨s, hs, n, hn, hsn⟩ := this
    exact ⟨s, hs, n, hn, hsn.symm⟩

end Main

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21

theorem ff84_3_2_of (h31 : FF84_3_1) (hKF1 : FF84KF1) (hKS : FF84KSOut) : FF84_3_2 := by
  intro G _ _ b L B b₁ b₂ hs S
  obtain ⟨hX, hZ⟩ := h31 G b L B b₁ b₂ hs
  obtain ⟨h2, hel⟩ := S3.S2_elemab lemmaH_holds hs hX hZ
  exact ⟨h2, hel, S3.S2_Cb hs hX hZ, S3.S2_final (lemmaQ_of hKF1 hKS) hs hX hZ⟩

end CFSG.RankThree.PartTwo.Sec21.FF84

end
