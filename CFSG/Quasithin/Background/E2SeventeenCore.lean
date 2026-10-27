module

public import CFSG.Quasithin.Background.E2SeventeenW

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

variable {G : Type*} [Group G] [Finite G]

theorem six_mul_card_le {ι : Type*} [Fintype ι] {P Z : Subgroup G} (S : ι → Subgroup G)
    (hSP : ∀ i, S i ≤ P) (hZP : Z ≤ P) (hZS : ∀ i, Z ≤ S i) (hS8 : ∀ i, Nat.card (S i) = 8)
    (hZ2 : Nat.card Z = 2) (hP : Nat.card P = 32) (hint : ∀ i j, i ≠ j → S i ⊓ S j ≤ Z) :
    6 * Fintype.card ι ≤ 30 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let fs : Subgroup G → Finset G := fun K => Finset.univ.filter (· ∈ K)
  have hfs : ∀ K : Subgroup G, (fs K).card = Nat.card K := fun K => by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hfsle : ∀ {K L : Subgroup G}, K ≤ L → fs K ⊆ fs L := fun hKL g hg => by
    simp only [fs, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact hKL hg
  let D : ι → Finset G := fun i => fs (S i) \ fs Z
  have hD : ∀ i, (D i).card = 6 := fun i => by
    have h1 : (fs (S i) \ fs Z).card + (fs Z).card = (fs (S i)).card :=
      Finset.card_sdiff_add_card_eq_card (hfsle (hZS i))
    have h2 : (fs (S i)).card = 8 := by rw [hfs, hS8]
    have h3 : (fs Z).card = 2 := by rw [hfs, hZ2]
    show (fs (S i) \ fs Z).card = 6
    omega
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint D := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro g hgi hgj
    simp only [D, fs, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      at hgi hgj
    exact hgi.2 (hint i j hij ⟨hgi.1, hgj.1⟩)
  have hsub : Finset.univ.biUnion D ⊆ fs P \ fs Z := by
    intro g hg
    rw [Finset.mem_biUnion] at hg
    obtain ⟨i, -, hgi⟩ := hg
    simp only [D, fs, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hgi ⊢
    exact ⟨hSP i hgi.1, hgi.2⟩
  have hcardU : (Finset.univ.biUnion D).card = 6 * Fintype.card ι := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun i _ => hD i)]
    simp [mul_comm, Finset.card_univ]
  have hcardP : (fs P \ fs Z).card = 30 := by
    have h1 : (fs P \ fs Z).card + (fs Z).card = (fs P).card :=
      Finset.card_sdiff_add_card_eq_card (hfsle hZP)
    have h2 : (fs P).card = 32 := by rw [hfs, hP]
    have h3 : (fs Z).card = 2 := by rw [hfs, hZ2]
    omega
  calc 6 * Fintype.card ι = (Finset.univ.biUnion D).card := hcardU.symm
    _ ≤ (fs P \ fs Z).card := Finset.card_le_card hsub
    _ = 30 := hcardP

namespace Setting17

variable {H T M V U : Subgroup G} {x z : G}

theorem zK (s : Setting17 H T M V U x z) : z ∈ twoResidual H :=
  mem_twoResidual_of_odd' s.dp.zH s.dp.zodd

theorem z3' (s : Setting17 H T M V U x z) : z ^ 3 = 1 := by
  rw [← s.z3]
  exact pow_orderOf_eq_one z

theorem isInv_of_mem (s : Setting17 H T M V U x z) {h : G} (hh : h ∈ Subgroup.zpowers z)
    (h1 : h ≠ 1) : IsInv H x h :=
  ⟨Subgroup.zpowers_le.2 s.dp.zH hh, Odd.of_dvd_nat s.dp.zodd (orderOf_dvd_of_mem_zpowers hh),
    h1, conj_eq_inv_of_mem_zpowers s.dp.xz hh⟩

theorem zpowers_le_I (s : Setting17 H T M V U x z) : Subgroup.zpowers z ≤ dpI V z :=
  Subgroup.zpowers_le.2 s.dp.zI

theorem cjSub_le_I (_s : Setting17 H T M V U x z) {h : G} (hh : h ∈ dpI V z) :
    cjSub h V ≤ dpI V z := by
  have h1 : cjSub h V ≤ cjSub h (dpI V z) := cjSub_mono le_sup_left
  rwa [cjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hh)] at h1

theorem Z0_le_P (s : Setting17 H T M V U x z) : Z0 H V ≤ dpP H V U z :=
  s.Z0_le_U.trans le_sup_left

theorem comm_z_mem_P (s : Setting17 H T M V U x z) {y : G} (hy : y ∈ s.W) :
    z * y * z⁻¹ * y⁻¹ ∈ dpP H V U z := by
  have hzH := s.dp.zH
  have hzx : x * (z * x * z⁻¹) = z := by
    have h1 : x * (z * x * z⁻¹) = (x * z * x⁻¹) * z⁻¹ := by rw [s.xinv]; group
    rw [h1, s.dp.xz]
    have h2 : z⁻¹ * z⁻¹ * z⁻¹ = 1 := by
      have : z⁻¹ * z⁻¹ * z⁻¹ = (z ^ 3)⁻¹ := by rw [pow_three]; group
      rw [this, s.z3', inv_one]
    calc z⁻¹ * z⁻¹ = z⁻¹ * z⁻¹ * z⁻¹ * z := by group
      _ = z := by rw [h2, one_mul]
  have hy' : z⁻¹ * y * z ∈ s.W := by simpa using s.conj_mem_W (H.inv_mem hzH) hy
  have hA : (z * x * z⁻¹) * y * (z * x * z⁻¹)⁻¹ * y⁻¹ ∈ dpA H V U z := by
    rw [s.dp.Aeq, mem_cjSub]
    have h1 := s.x_comm_mem hy'
    have e : z⁻¹ * ((z * x * z⁻¹) * y * (z * x * z⁻¹)⁻¹ * y⁻¹) * z =
        x * (z⁻¹ * y * z) * x⁻¹ * (z⁻¹ * y * z)⁻¹ := by group
    rw [e]
    exact h1
  have hxP : x ∈ Subgroup.normalizer (dpP H V U z : Set G) :=
    s.dp.IP (Subgroup.mem_sup_left s.dp.xV)
  have e : z * y * z⁻¹ * y⁻¹ = x * ((z * x * z⁻¹) * y * (z * x * z⁻¹)⁻¹ * y⁻¹) * x⁻¹ *
      (x * y * x⁻¹ * y⁻¹) := by
    conv_lhs => rw [← hzx]
    group
  rw [e]
  exact (dpP H V U z).mul_mem ((Subgroup.mem_normalizer_iff.mp hxP _).mp
    (Subgroup.mem_sup_right hA)) (Subgroup.mem_sup_left (s.x_comm_mem hy))

theorem mul_comm_inv_mem (s : Setting17 H T M V U x z) {u : G} (hu : u ∈ U) :
    u * (z * (z * u * z⁻¹) * z⁻¹ * (z * u * z⁻¹)⁻¹)⁻¹ ∈ Z0 H V := by
  have hn := s.dp.norm_mem s.z3 hu
  rw [s.Zeq] at hn
  have hzz : z * z = z⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, show z * z * z = z ^ 3 by rw [pow_three, mul_assoc]]
    exact s.z3'
  have hb2 : (z⁻¹ * u * z) * (z⁻¹ * u * z) = 1 := by
    have h2 : u * u = 1 := by simpa [pow_two] using s.dp.elem.2 u (s.dp.UV hu)
    calc (z⁻¹ * u * z) * (z⁻¹ * u * z) = z⁻¹ * (u * u) * z := by group
      _ = 1 := by rw [h2]; group
  have e1 : z * (z * u * z⁻¹) * z⁻¹ = z⁻¹ * u * z := by
    calc z * (z * u * z⁻¹) * z⁻¹ = (z * z) * u * (z * z)⁻¹ := by group
      _ = z⁻¹ * u * z := by rw [hzz, inv_inv]
  rw [e1]
  have e2 : u * (z⁻¹ * u * z * (z * u * z⁻¹)⁻¹)⁻¹ =
      u * (z * u * z⁻¹) * (z⁻¹ * u * z) * ((z⁻¹ * u * z) * (z⁻¹ * u * z))⁻¹ := by group
  rw [e2, hb2, inv_one, mul_one]
  exact hn

theorem conj_U_le_P (s : Setting17 H T M V U x z) {w : G} (hw : IsInv H x w) :
    cjSub w U ≤ dpP H V U z := by
  intro y hy
  rw [mem_cjSub] at hy
  have hwH : w ∈ H := hw.1
  have hwK : w ∈ twoResidual H := mem_twoResidual_of_odd' hwH hw.2.1
  obtain ⟨u, hu, hyu⟩ : ∃ u ∈ U, y = w * u * w⁻¹ := ⟨_, hy, by group⟩
  rw [hyu]
  obtain ⟨a, ha⟩ : ∃ a, a = z * u * z⁻¹ := ⟨_, rfl⟩
  have haW : a ∈ s.W := s.gen_mem_W s.zK (by rw [ha, mem_cjSub]; simpa [mul_assoc] using hu)
  have hζ := s.mul_comm_inv_mem hu
  rw [← ha] at hζ
  obtain ⟨ζ, hζdef⟩ : ∃ ζ, ζ = u * (z * a * z⁻¹ * a⁻¹)⁻¹ := ⟨_, rfl⟩
  rw [← hζdef] at hζ
  have hη := s.comm_conj_mem s.zK hwK haW
  obtain ⟨η, hηdef⟩ : ∃ η, η = (z * w) * a * (z * w)⁻¹ * ((w * z) * a * (w * z)⁻¹)⁻¹ :=
    ⟨_, rfl⟩
  rw [← hηdef] at hη
  have ha'W : w * a * w⁻¹ ∈ s.W := s.conj_mem_W hwH haW
  have hu_eq : u = ζ * (z * a * z⁻¹ * a⁻¹) := by rw [hζdef]; group
  have e : w * u * w⁻¹ = (w * ζ * w⁻¹) *
      (η⁻¹ * (z * (w * a * w⁻¹) * z⁻¹ * (w * a * w⁻¹)⁻¹)) := by
    rw [hu_eq, hηdef]
    group
  rw [e, s.le_center hwH hζ]
  exact (dpP H V U z).mul_mem (s.Z0_le_P hζ) ((dpP H V U z).mul_mem
    (s.Z0_le_P ((Z0 H V).inv_mem hη)) (s.comm_z_mem_P ha'W))

theorem conj_conj_le (s : Setting17 H T M V U x z) {w h : G} (hw : w ∈ twoResidual H)
    (hh : h ∈ twoResidual H) : cjSub (w⁻¹ * h * w) U ≤ cjSub h U := by
  intro y hy
  rw [mem_cjSub] at hy ⊢
  obtain ⟨u, hu, hyu⟩ : ∃ u ∈ U, y = (w⁻¹ * h * w) * u * (w⁻¹ * h * w)⁻¹ := ⟨_, hy, by group⟩
  have hθ := s.comm_conj_mem hh hw (s.U_le_W hu)
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = (h * w) * u * (h * w)⁻¹ * ((w * h) * u * (w * h)⁻¹)⁻¹ :=
    ⟨_, rfl⟩
  rw [← hθdef] at hθ
  have hwH : w ∈ H := twoResidual_le H hw
  have hhH : h ∈ H := twoResidual_le H hh
  have e : h⁻¹ * y * h = (h⁻¹ * (w⁻¹ * θ * w⁻¹⁻¹) * h⁻¹⁻¹) * u := by
    rw [hyu, hθdef]
    group
  rw [e, s.le_center (H.inv_mem hhH) (by rw [s.le_center (H.inv_mem hwH) hθ]; exact hθ),
    s.le_center (H.inv_mem hwH) hθ]
  exact U.mul_mem (s.Z0_le_U hθ) hu

theorem inter_le (s : Setting17 H T M V U x z) {g : G} (hg : g ∈ twoResidual H)
    (hgV : cjSub g V ≠ V) : U ⊓ cjSub g U ≤ Z0 H V := by
  rcases s.inf_eq hg with h | h
  · exact absurd h hgV
  · rw [← h]
    exact inf_le_inf s.dp.UV (cjSub_mono s.dp.UV)

theorem inter_conj (s : Setting17 H T M V U x z) {g g' : G} (hg : g ∈ H)
    (h : U ⊓ cjSub (g⁻¹ * g') U ≤ Z0 H V) : cjSub g U ⊓ cjSub g' U ≤ Z0 H V := by
  have hg' : cjSub g' U = cjSub g (cjSub (g⁻¹ * g') U) := by
    rw [← cjSub_mul, mul_inv_cancel_left]
  have hZ : cjSub g (Z0 H V) = Z0 H V := cjSub_eq_of_mem_normalizer
    (B6.mem_normalizer_of_forall_mem (fun ζ hζ => by rw [s.le_center hg hζ]; exact hζ)
      (fun ζ hζ => by
        have h1 := s.le_center (H.inv_mem hg) hζ
        rw [inv_inv] at h1
        rw [h1]
        exact hζ))
  rw [hg', ← cjSub_inf, ← hZ]
  exact cjSub_mono h

theorem conj_le_I (s : Setting17 H T M V U x z) {w : G} (hw : IsInv H x w) :
    cjSub w V ≤ dpI V z := by
  by_contra hnot
  have hwH : w ∈ H := hw.1
  have hwK : w ∈ twoResidual H := mem_twoResidual_of_odd' hwH hw.2.1
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hzpowK : ∀ i : ℕ, z ^ i ∈ twoResidual H := fun i => (twoResidual H).pow_mem s.zK i
  have hzpowI : ∀ i : ℕ, z ^ i ∈ dpI V z := fun i => (dpI V z).pow_mem s.dp.zI i
  set P := dpP H V U z with hP
  have hUcard : Nat.card U = 8 := by
    have := s.dp.cardV
    rw [s.V16] at this
    omega
  have hPcard : Nat.card P = 32 := by
    obtain ⟨-, -, -, hext, -⟩ := s.dp.stage_one (by rw [s.z3]; exact Nat.prime_three) s.V16 s.q32
    rw [hext.2.1]
    norm_num
  let S : Fin 3 × Fin 2 → Subgroup G := fun p => cjSub (z ^ (p.1 : ℕ) * w ^ (p.2 : ℕ)) U
  have hwpow : ∀ b : Fin 2, cjSub (w ^ (b : ℕ)) U ≤ P := by
    intro b
    fin_cases b
    · simp only [pow_zero, cjSub_one]
      exact le_sup_left
    · simp only [pow_one]
      exact s.conj_U_le_P hw
  have hSP : ∀ p, S p ≤ P := by
    intro p
    have h1 : cjSub (z ^ (p.1 : ℕ)) P = P :=
      cjSub_eq_of_mem_normalizer (s.dp.IP (hzpowI _))
    show cjSub (z ^ (p.1 : ℕ) * w ^ (p.2 : ℕ)) U ≤ P
    rw [cjSub_mul, ← h1]
    exact cjSub_mono (hwpow p.2)
  have hgH : ∀ p : Fin 3 × Fin 2, z ^ (p.1 : ℕ) * w ^ (p.2 : ℕ) ∈ H := fun p =>
    H.mul_mem (hKH (hzpowK _)) (H.pow_mem hwH _)
  have hZS : ∀ p, Z0 H V ≤ S p := by
    intro p
    have hZ : cjSub (z ^ (p.1 : ℕ) * w ^ (p.2 : ℕ)) (Z0 H V) = Z0 H V :=
      cjSub_eq_of_mem_normalizer (B6.mem_normalizer_of_forall_mem
        (fun ζ hζ => by rw [s.le_center (hgH p) hζ]; exact hζ)
        (fun ζ hζ => by
          have h1 := s.le_center (H.inv_mem (hgH p)) hζ
          rw [inv_inv] at h1
          rw [h1]
          exact hζ))
    show Z0 H V ≤ cjSub (z ^ (p.1 : ℕ) * w ^ (p.2 : ℕ)) U
    rw [← hZ]
    exact cjSub_mono s.Z0_le_U
  have hS8 : ∀ p, Nat.card (S p) = 8 := fun p => by
    show Nat.card (cjSub (z ^ (p.1 : ℕ) * w ^ (p.2 : ℕ)) U) = 8
    rw [card_cjSub, hUcard]
  have hzinj : ∀ i j : Fin 3, i ≠ j → (z ^ (i : ℕ))⁻¹ * z ^ (j : ℕ) ≠ 1 := by
    intro i j hij h1
    apply hij
    have h2 : z ^ (i : ℕ) = z ^ (j : ℕ) := inv_mul_eq_one.1 h1
    have hi : (i : ℕ) < orderOf z := by rw [s.z3]; exact i.2
    have hj : (j : ℕ) < orderOf z := by rw [s.z3]; exact j.2
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj h2)
  have hzmem : ∀ i j : ℕ, (z ^ i)⁻¹ * z ^ j ∈ Subgroup.zpowers z := fun i j =>
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers z i))
      (Subgroup.npow_mem_zpowers z j)
  have hnotV : ∀ h ∈ Subgroup.zpowers z, cjSub (h * w) V ≠ V := by
    intro h hh he
    apply hnot
    have h1 : cjSub w V = cjSub h⁻¹ V := by
      calc cjSub w V = cjSub (h⁻¹ * (h * w)) V := by rw [inv_mul_cancel_left]
        _ = cjSub h⁻¹ (cjSub (h * w) V) := cjSub_mul _ _ _
        _ = cjSub h⁻¹ V := by rw [he]
    rw [h1]
    exact s.cjSub_le_I (s.zpowers_le_I (Subgroup.inv_mem _ hh))
  have hint : ∀ p q : Fin 3 × Fin 2, p ≠ q → S p ⊓ S q ≤ Z0 H V := by
    rintro ⟨i, b⟩ ⟨j, c⟩ hpq
    show cjSub (z ^ (i : ℕ) * w ^ (b : ℕ)) U ⊓ cjSub (z ^ (j : ℕ) * w ^ (c : ℕ)) U ≤ Z0 H V
    refine s.inter_conj (hgH (i, b)) ?_
    fin_cases b <;> fin_cases c
    ·
      have hij : i ≠ j := fun h => hpq (by rw [h])
      simp only [pow_zero, mul_one]
      have hh := s.isInv_of_mem (hzmem i j) (hzinj i j hij)
      exact s.inter_le ((twoResidual H).mul_mem ((twoResidual H).inv_mem (hzpowK _))
        (hzpowK _)) (s.conj_ne hh)
    ·
      simp only [pow_zero, mul_one, pow_one]
      have hk : (z ^ (i : ℕ))⁻¹ * (z ^ (j : ℕ) * w) ∈ twoResidual H :=
        (twoResidual H).mul_mem ((twoResidual H).inv_mem (hzpowK _))
          ((twoResidual H).mul_mem (hzpowK _) hwK)
      refine s.inter_le hk ?_
      rw [← mul_assoc]
      exact hnotV _ (hzmem i j)
    ·
      simp only [pow_zero, mul_one, pow_one]
      have hk : (z ^ (i : ℕ) * w)⁻¹ * z ^ (j : ℕ) ∈ twoResidual H :=
        (twoResidual H).mul_mem ((twoResidual H).inv_mem
          ((twoResidual H).mul_mem (hzpowK _) hwK)) (hzpowK _)
      refine s.inter_le hk ?_
      intro he
      apply hnotV ((z ^ (j : ℕ))⁻¹ * z ^ (i : ℕ)) (hzmem j i)
      have e : (z ^ (j : ℕ))⁻¹ * z ^ (i : ℕ) * w = ((z ^ (i : ℕ) * w)⁻¹ * z ^ (j : ℕ))⁻¹ := by
        group
      rw [e]
      calc cjSub ((z ^ (i : ℕ) * w)⁻¹ * z ^ (j : ℕ))⁻¹ V
          = cjSub ((z ^ (i : ℕ) * w)⁻¹ * z ^ (j : ℕ))⁻¹
              (cjSub ((z ^ (i : ℕ) * w)⁻¹ * z ^ (j : ℕ)) V) := by rw [he]
        _ = cjSub (((z ^ (i : ℕ) * w)⁻¹ * z ^ (j : ℕ))⁻¹ *
              ((z ^ (i : ℕ) * w)⁻¹ * z ^ (j : ℕ))) V := (cjSub_mul _ _ _).symm
        _ = V := by rw [inv_mul_cancel, cjSub_one]
    ·
      have hij : i ≠ j := fun h => hpq (by rw [h])
      simp only [pow_one]
      have hh := s.isInv_of_mem (hzmem i j) (hzinj i j hij)
      have hhK : (z ^ (i : ℕ))⁻¹ * z ^ (j : ℕ) ∈ twoResidual H :=
        (twoResidual H).mul_mem ((twoResidual H).inv_mem (hzpowK _)) (hzpowK _)
      have e : (z ^ (i : ℕ) * w)⁻¹ * (z ^ (j : ℕ) * w) =
          w⁻¹ * ((z ^ (i : ℕ))⁻¹ * z ^ (j : ℕ)) * w := by group
      rw [e]
      exact (inf_le_inf_left U (s.conj_conj_le hwK hhK)).trans (s.inter_le hhK (s.conj_ne hh))
  have h6 := six_mul_card_le S hSP s.Z0_le_P hZS hS8 s.Z0_card hPcard hint
  simp at h6

theorem mem_K_mul_T (s : Setting17 H T M V U x z) {g : G} (hg : g ∈ H) :
    ∃ k ∈ twoResidual H, ∃ t ∈ T, k * t = g := by
  have hTK : T ≤ Subgroup.normalizer (twoResidual H : Set G) :=
    s.dp.TH.trans (le_normalizer_twoResidual H)
  have h1 : g ∈ ((twoResidual H ⊔ T : Subgroup G) : Set G) := by
    rw [sup_comm, sup_twoResidual_eq s.mp.isSylow]
    exact hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTK] at h1
  obtain ⟨k, hk, t, ht, e⟩ := h1
  exact ⟨k, hk, t, ht, e⟩

theorem conjClosure_eq (s : Setting17 H T M V U x z) : conjClosure V H = dpI V z := by
  apply le_antisymm
  · rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨g, hg, v, hv, rfl⟩
    obtain ⟨k, hk, t, ht, rfl⟩ := s.mem_K_mul_T hg
    have htv : t * v * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (s.dp.TV ht) v).mp hv
    have hmem : k * (t * v * t⁻¹) * k⁻¹ ∈ cjSub k V := by
      rw [mem_cjSub]
      simpa [mul_assoc] using htv
    have e : k * t * v * (k * t)⁻¹ = k * (t * v * t⁻¹) * k⁻¹ := by group
    rw [SetLike.mem_coe, e]
    obtain ⟨i, hi, hki⟩ := s.conjV hk
    rw [hki] at hmem
    rcases hi with rfl | hi
    · rw [cjSub_one] at hmem
      exact Subgroup.mem_sup_left hmem
    · exact s.conj_le_I hi hmem
  · refine sup_le (fun v hv => Subgroup.subset_closure ⟨1, H.one_mem, v, hv, by group⟩)
      fun y hy => Subgroup.subset_closure ⟨z, s.dp.zH, z⁻¹ * y * z, mem_cjSub.1 hy, by group⟩

end Setting17

theorem e217Concl_of_isSolvable {Γ : Type} [Group Γ] [Finite Γ] {H T M V : Subgroup Γ}
    (h : Hyp28 H T M V) (hchar : CharTwo H)
    (hq : qhatOf (autI h.elem H) = (((3 : ℚ) / 2 : ℚ) : WithTop ℚ))
    (hres : twoResidual M ≤ Subgroup.centralizer (V : Set Γ)) (hV16 : Nat.card V = 2 ^ 4)
    (hsolv : Group.IsSolvable H) : E217Concl H T V := by
  obtain ⟨U, x, z₀, d₀⟩ := DihedralPair.exists_of_isSolvable h.minParabolic hsolv hchar h.le_T
    h.normal_T h.elem h.not_le_pCoreOf
  obtain ⟨z, -, hp, d⟩ := d₀.exists_prime_orderOf
  have hq' : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI d.elem H) := hq.symm.le
  obtain ⟨hz3, hZ2, hCA, hext, hIP, φ, hφs, hφk⟩ := d.stage_one hp hV16 hq'
  have hUQ := d.le_pCoreOf hz3 hV16 hZ2 hCA
  have s : Setting17 H T M V U x z :=
    ⟨d, h.minParabolic, hsolv, hres, hV16, hq', hz3, hZ2, hCA, hUQ⟩
  have hY := s.conjClosure_eq
  unfold E217Concl
  simp only []
  rw [hY]
  exact Or.inl ⟨dpP H V U z, d.PR.trans inf_le_left, hIP, hext, φ, hφs, hφk⟩

theorem e217Statement_of_nonsolvable (hns : E217Nonsolvable) : E217Statement := by
  intro Γ _ _ H T M V h hchar hTI hq hres hV16
  by_cases hsolv : Group.IsSolvable H
  · exact e217Concl_of_isSolvable h hchar hq hres hV16 hsolv
  · exact hns Γ H T M V h hchar hTI hq hres hV16 hsolv

end E2

end CFSG.Quasithin
