module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityModel

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration

section Generic

variable {K : Type*} [Group K]

theorem fixed_conj_iff (c k : K) : MulAut.conj c k = k ↔ k ∈ Subgroup.centralizer {c} := by
  rw [Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem centralizer_le_planeClosure {E : Subgroup (MulAut K)} {c : K}
    (he : (MulAut.conj c : MulAut K) ∈ E) (he1 : (MulAut.conj c : MulAut K) ≠ 1) :
    Subgroup.centralizer {c} ≤ planeClosure E := fun k hk =>
  mem_planeClosure_of_fixed he he1 ((fixed_conj_iff c k).mpr hk)

end Generic

section Core

variable {G : Type*} [Group G]

theorem core_central_conj {H : Type*} [Group H] {z : H} (hz : z ∈ Subgroup.center H) (g : H) :
    z * g * z⁻¹ = g := by
  rw [Subgroup.mem_center_iff] at hz
  rw [← hz g, mul_inv_cancel_right]

theorem core_comm_left {H : Type*} [Group H] (b : H) {k : H} (hk : k ∈ Subgroup.center H)
    (v : H) : b * k * v * (b * k)⁻¹ * v⁻¹ = b * v * b⁻¹ * v⁻¹ := by
  rw [mul_inv_rev]
  calc b * k * v * (k⁻¹ * b⁻¹) * v⁻¹ = b * (k * v * k⁻¹) * b⁻¹ * v⁻¹ := by
        simp only [mul_assoc]
    _ = b * v * b⁻¹ * v⁻¹ := by rw [core_central_conj hk v]

theorem core_comm_right {H : Type*} [Group H] (u : H) {b k : H} (hk : k ∈ Subgroup.center H) :
    u * (b * k) * u⁻¹ * (b * k)⁻¹ = u * b * u⁻¹ * b⁻¹ := by
  rw [mul_inv_rev]
  calc u * (b * k) * u⁻¹ * (k⁻¹ * b⁻¹) = u * b * (k * u⁻¹ * k⁻¹) * b⁻¹ := by
        simp only [mul_assoc]
    _ = u * b * u⁻¹ * b⁻¹ := by rw [core_central_conj hk u⁻¹]

theorem core_commutator_le {H : Type*} [Group H] {S : Subgroup H}
    (h : ∀ u : H, ∃ b ∈ S, ∃ k ∈ Subgroup.center H, u = b * k) : commutator H ≤ S := by
  show ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ S
  refine Subgroup.commutator_le.mpr ?_
  intro u _ v _
  obtain ⟨b1, hb1, k1, hk1, rfl⟩ := h u
  obtain ⟨b2, hb2, k2, hk2, rfl⟩ := h v
  rw [commutatorElement_def, core_comm_left b1 hk1, core_comm_right b1 hk2]
  exact S.mul_mem (S.mul_mem (S.mul_mem hb1 hb2) (S.inv_mem hb1)) (S.inv_mem hb2)

theorem core_sup_normalizes {A B : Subgroup G} (hnorm : ∀ g ∈ A, ∀ h ∈ B, g * h * g⁻¹ ∈ B)
    (g : G) (hg : g ∈ A ⊔ B) (h : G) (hh : h ∈ B) : g * h * g⁻¹ ∈ B := by
  have hA : A ≤ Subgroup.normalizer (B : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hnorm x hx y hy, fun hy => ?_⟩
    have hy' : x * y * x⁻¹ ∈ B := hy
    have h2 := hnorm x⁻¹ (A.inv_mem hx) _ hy'
    have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rw [e] at h2
    exact h2
  have hB : B ≤ Subgroup.normalizer (B : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => B.mul_mem (B.mul_mem hx hy) (B.inv_mem hx), fun hy => ?_⟩
    have hy' : x * y * x⁻¹ ∈ B := hy
    have h2 := B.mul_mem (B.mul_mem (B.inv_mem hx) hy') hx
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rw [e] at h2
    exact h2
  have hle : A ⊔ B ≤ Subgroup.normalizer (B : Set G) := sup_le hA hB
  exact (Subgroup.mem_normalizer_iff.mp (hle hg) h).mp hh

theorem core_subgroupOf_normal {A B N : Subgroup G}
    (hnorm : ∀ g ∈ A, ∀ h ∈ B, g * h * g⁻¹ ∈ B) (hNle : N ≤ A ⊔ B) :
    (B.subgroupOf N).Normal := by
  refine ⟨fun b hb g => ?_⟩
  have h1 : (g : G) * (b : G) * (g : G)⁻¹ ∈ B :=
    core_sup_normalizes hnorm (g : G) (hNle g.2) (b : G) (Subgroup.mem_subgroupOf.mp hb)
  exact Subgroup.mem_subgroupOf.mpr h1

theorem core_B_le_N {B N C : Subgroup G} (hBC : B ≤ C)
    (hNcomm : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ N) (hperf : commutator ↥B = ⊤) :
    B ≤ N := by
  have hsub : commutator ↥B ≤ N.subgroupOf B := by
    show ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ ≤ N.subgroupOf B
    refine Subgroup.commutator_le.mpr ?_
    intro h _ k _
    rw [Subgroup.mem_subgroupOf, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hNcomm _ (hBC h.2) _ (hBC k.2)
  rw [hperf] at hsub
  intro b hb
  exact Subgroup.mem_subgroupOf.mp (hsub (Subgroup.mem_top (⟨b, hb⟩ : ↥B)))

theorem core_not_centralizer_le_sup {A B : Subgroup G} {a : G}
    (hBC : B ≤ Subgroup.centralizer ({a} : Set G))
    (hnorm : ∀ g ∈ A, ∀ h ∈ B, g * h * g⁻¹ ∈ B)
    (hperf : commutator ↥B = ⊤)
    (hnonab : ∃ u ∈ B, ∃ v ∈ B, u * v ≠ v * u)
    (hcentB : ∀ x ∈ B, (∀ g ∈ B, g * x = x * g) → x ^ 3 = 1 → x = 1)
    (hD : Group.IsSolvable (Subgroup.centralizer ({a} : Set G)) ∨
      ∃ N : Subgroup G, N ≤ Subgroup.centralizer ({a} : Set G) ∧
        (∀ x ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Subgroup.centralizer ({a} : Set G),
          x * y * x⁻¹ * y⁻¹ ∈ N) ∧
        CFSG.IsQuasisimple N ∧ ∃ x ∈ N, (∀ n ∈ N, x * n = n * x) ∧ x ≠ 1 ∧ x ^ 3 = 1) :
    ¬ Subgroup.centralizer ({a} : Set G) ≤ A ⊔ B := by
  intro hle
  rcases hD with hsolv | ⟨N, hNC, hNcomm, hq, x, hxN, hxc, hx1, hx3⟩
  ·
    haveI : Group.IsSolvable ↥B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBC)
    have hne : (⊤ : Subgroup ↥B) ≠ ⊥ := by
      intro htop
      obtain ⟨u, hu, v, hv, huv⟩ := hnonab
      have h1 : (⟨u, hu⟩ : ↥B) ∈ (⊥ : Subgroup ↥B) := by
        rw [← htop]; exact Subgroup.mem_top _
      have h2 : (⟨v, hv⟩ : ↥B) ∈ (⊥ : Subgroup ↥B) := by
        rw [← htop]; exact Subgroup.mem_top _
      rw [Subgroup.mem_bot] at h1 h2
      have hu1 : u = 1 := congrArg Subtype.val h1
      have hv1 : v = 1 := congrArg Subtype.val h2
      apply huv
      rw [hu1, hv1]
    have hlt : commutator ↥B < ⊤ := Group.IsSolvable.commutator_lt_of_ne_bot hne
    rw [hperf] at hlt
    exact lt_irrefl _ hlt
  ·
    obtain ⟨hcomm', hsimp⟩ := hq
    have hcommN : commutator ↥N = ⊤ := Group.isPerfect_def.mp hcomm'
    have hSimple : IsSimpleGroup (↥N ⧸ Subgroup.center ↥N) := hsimp.1
    have hNle : N ≤ A ⊔ B := fun g hg => hle (hNC hg)
    have hBN : B ≤ N := core_B_le_N hBC hNcomm hperf
    have hBnorm : (B.subgroupOf N).Normal := core_subgroupOf_normal hnorm hNle
    haveI hMnorm : ((B.subgroupOf N).map (QuotientGroup.mk' (Subgroup.center ↥N))).Normal :=
      Subgroup.Normal.map hBnorm (QuotientGroup.mk' (Subgroup.center ↥N))
        (QuotientGroup.mk'_surjective (Subgroup.center ↥N))
    rcases hSimple.eq_bot_or_eq_top_of_normal
        ((B.subgroupOf N).map (QuotientGroup.mk' (Subgroup.center ↥N))) with hM | hM
    ·
      obtain ⟨u, hu, v, hv, huv⟩ := hnonab
      have hmem : (⟨u, hBN hu⟩ : ↥N) ∈ B.subgroupOf N := Subgroup.mem_subgroupOf.mpr hu
      have h1 : QuotientGroup.mk' (Subgroup.center ↥N) (⟨u, hBN hu⟩ : ↥N) ∈
          (B.subgroupOf N).map (QuotientGroup.mk' (Subgroup.center ↥N)) :=
        Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center ↥N)) hmem
      rw [hM, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have hcv := Subgroup.mem_center_iff.mp h1 (⟨v, hBN hv⟩ : ↥N)
      apply huv
      exact (congrArg Subtype.val hcv).symm
    ·
      have hdec : ∀ w : ↥N, ∃ b ∈ B.subgroupOf N, ∃ k ∈ Subgroup.center ↥N, w = b * k := by
        intro w
        have hw : QuotientGroup.mk' (Subgroup.center ↥N) w ∈
            (B.subgroupOf N).map (QuotientGroup.mk' (Subgroup.center ↥N)) := by
          rw [hM]; exact Subgroup.mem_top _
        obtain ⟨b, hbB, hbw⟩ := Subgroup.mem_map.mp hw
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hbw
        exact ⟨b, hbB, b⁻¹ * w, QuotientGroup.eq.mp hbw, (mul_inv_cancel_left b w).symm⟩
      have hsub : commutator ↥N ≤ B.subgroupOf N := core_commutator_le hdec
      rw [hcommN] at hsub
      have hNB : N ≤ B := by
        intro n hn
        exact Subgroup.mem_subgroupOf.mp (hsub (Subgroup.mem_top (⟨n, hn⟩ : ↥N)))
      have hxB : x ∈ B := hNB hxN
      have hxcB : ∀ g ∈ B, g * x = x * g := fun g hg => (hxc g (hBN hg)).symm
      exact hx1 (hcentB x hxB hxcB hx3)

end Core

section Model

variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem conj_tau_fixed (a k : C0 σ) :
    (MulAut.conj a * tauAut σ : MulAut (C0 σ)) k = k ↔ a * tauAut σ k = k * a := by
  rw [MulAut.mul_apply, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]

end Model

end CFSG.RankThree.PartTwo.Sec19
