module

public import CFSG.OddTranspositions.PartFour.LineFibres
public import CFSG.OddTranspositions.PartFour.SeventeenTwo

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

theorem dvd_of_two_pow_add_one_dvd {n s : ℕ} (hn : 0 < n) (h : 2 ^ n + 1 ∣ 2 ^ (2 * s) - 1) :
    n ∣ s := by
  have h2n : 2 ^ n + 1 ∣ 2 ^ (2 * n) - 1 := by
    have h1 := Nat.sq_sub_sq (2 ^ n) 1
    rw [one_pow, ← pow_mul, mul_comm n 2] at h1
    rw [h1]
    exact dvd_mul_right _ _
  have hg : 2 ^ n + 1 ∣ 2 ^ (2 * Nat.gcd n s) - 1 := by
    rw [← Nat.gcd_mul_left, ← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd h2n h
  by_contra hns
  have hlt : Nat.gcd n s < n := lt_of_le_of_ne (Nat.gcd_le_left s hn)
    (fun he => hns (he ▸ Nat.gcd_dvd_right n s))
  have hle : 2 * Nat.gcd n s ≤ n := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left n s
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · simp only [mul_zero] at hk
        omega
      · simp only [zero_add, mul_one] at hk
        omega
      · omega
    calc 2 * Nat.gcd n s ≤ Nat.gcd n s * k := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hk2
      _ = n := hk.symm
  have hpos : 0 < 2 ^ (2 * Nat.gcd n s) - 1 := by
    have : 0 < Nat.gcd n s := Nat.gcd_pos_of_pos_left s hn
    have : 1 < 2 ^ (2 * Nat.gcd n s) := Nat.one_lt_two_pow (by omega)
    omega
  have h3 := Nat.le_of_dvd hpos hg
  have h4 : 2 ^ (2 * Nat.gcd n s) ≤ 2 ^ n := Nat.pow_le_pow_right Nat.two_pos hle
  omega

theorem orbitPower_ncard_image_eq_of_fiber {A B C : Type*} {s : Set A}
    {f : A → B} {g : A → C}
    (h : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    (f '' s).ncard = (g '' s).ncard := by
  classical
  have hex : ∀ b ∈ f '' s, ∃ x ∈ s, f x = b := by
    rintro b ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  let F : (b : B) → b ∈ f '' s → A := fun b hb => Classical.choose (hex b hb)
  have hF1 : ∀ (b : B) (hb : b ∈ f '' s), F b hb ∈ s :=
    fun b hb => (Classical.choose_spec (hex b hb)).1
  have hF2 : ∀ (b : B) (hb : b ∈ f '' s), f (F b hb) = b :=
    fun b hb => (Classical.choose_spec (hex b hb)).2
  let φ : (f '' s : Set B) → (g '' s : Set C) := fun p =>
    ⟨g (F p.1 p.2), F p.1 p.2, hF1 p.1 p.2, rfl⟩
  have hφinj : Function.Injective φ := by
    intro p q hpq
    have h1 : g (F p.1 p.2) = g (F q.1 q.2) := congrArg Subtype.val hpq
    have h2 : f (F p.1 p.2) = f (F q.1 q.2) :=
      (h _ (hF1 p.1 p.2) _ (hF1 q.1 q.2)).mpr h1
    have h3 : p.1 = q.1 := by
      rw [← hF2 p.1 p.2, ← hF2 q.1 q.2]
      exact h2
    exact Subtype.ext h3
  have hφsurj : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, hx, rfl⟩ := hb
    refine ⟨⟨f x, ⟨x, hx, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact (h _ (hF1 (f x) ⟨x, hx, rfl⟩) x hx).mp (hF2 (f x) ⟨x, hx, rfl⟩)
  exact Set.ncard_congr' (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem orbitPower_inv_mul_conj_mem_Malpha (hC : HypothesisC D)
    {b y y' : Halpha D hC.alpha}
    (hy : y ∈ CFSG.pCore 2 (Halpha D hC.alpha))
    (hy' : y' ∈ CFSG.pCore 2 (Halpha D hC.alpha)) :
    ((y : G) * b * (y : G)⁻¹)⁻¹ * ((y' : G) * b * (y' : G)⁻¹) ∈
      Malpha D hC.alpha := by
  let H := Halpha D hC.alpha
  have hyR : y ∈ CFSG.solvableRadical H := CFSG.pCore_le_solvableRadical 2 H hy
  have hy'R : y' ∈ CFSG.solvableRadical H := CFSG.pCore_le_solvableRadical 2 H hy'
  have hu : y⁻¹ * y' ∈ CFSG.solvableRadical H :=
    (CFSG.solvableRadical H).mul_mem ((CFSG.solvableRadical H).inv_mem hyR) hy'R
  have hconj : b⁻¹ * (y⁻¹ * y') * b ∈ CFSG.solvableRadical H := by
    simpa using (inferInstance : (CFSG.solvableRadical H).Normal).conj_mem
      (y⁻¹ * y') hu b⁻¹
  have hprod : y * (b⁻¹ * (y⁻¹ * y') * b) * y'⁻¹ ∈ CFSG.solvableRadical H :=
    (CFSG.solvableRadical H).mul_mem
      ((CFSG.solvableRadical H).mul_mem hyR hconj)
      ((CFSG.solvableRadical H).inv_mem hy'R)
  refine Subgroup.mem_map.mpr ⟨y * (b⁻¹ * (y⁻¹ * y') * b) * y'⁻¹, hprod, ?_⟩
  simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem orbitPower_cimg_eq_of_conj_eq (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {b y y' : Halpha D hC.alpha} (hb : (b : G) ∈ β)
    (hg : y * b * y⁻¹ = y' * b * y'⁻¹) :
    cimg (y : G) β = cimg (y' : G) β := by
  have hEqG : (y : G) * b * (y : G)⁻¹ = (y' : G) * b * (y' : G)⁻¹ :=
    congrArg Subtype.val hg
  have hclass1 : cimg (y : G) β ∈ blockClass hC.alpha :=
    cimg_mem_blockClass_iff.mpr hβ.1
  have hclass2 : cimg (y' : G) β ∈ blockClass hC.alpha :=
    cimg_mem_blockClass_iff.mpr hβ.1
  have hmeet : (cimg (y : G) β ∩ cimg (y' : G) β).Nonempty :=
    ⟨(y : G) * b * (y : G)⁻¹, ⟨b, hb, rfl⟩, by rw [hEqG]; exact ⟨b, hb, rfl⟩⟩
  exact eq_of_mem_of_mem_blockClass hC.isBlock_alpha hclass1 hclass2 hmeet

theorem orbitPower_conj_eq_of_cimg_eq (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b y y' : Halpha D hC.alpha}
    (hb : (b : G) ∈ β)
    (hy : y ∈ CFSG.pCore 2 (Halpha D hC.alpha))
    (hy' : y' ∈ CFSG.pCore 2 (Halpha D hC.alpha))
    (hconj : cimg (y : G) β = cimg (y' : G) β) :
    y * b * y⁻¹ = y' * b * y'⁻¹ := by
  have hγ : cimg (y : G) β ∈ Dalpha D hC.alpha :=
    conj_mem_Dalpha_of_mem_normalizer hC.setup.normal hβ
      (Halpha_le_normalizer_block D hC.alpha y.2)
  have hbγ : (y : G) * b * (y : G)⁻¹ ∈ cimg (y : G) β := ⟨b, hb, rfl⟩
  have hbγ' : (y' : G) * b * (y' : G)⁻¹ ∈ cimg (y : G) β := by
    rw [hconj]
    exact ⟨b, hb, rfl⟩
  have hcc' : ((y : G) * b * (y : G)⁻¹)⁻¹ *
      ((y' : G) * b * (y' : G)⁻¹) ∈ Malpha D hC.alpha :=
    orbitPower_inv_mul_conj_mem_Malpha hC (b := b) hy hy'
  have hEqG := eq_of_mem_of_inv_mul_mem_Malpha h89 h113 hC hrad hW hn3 hHns
    hγ hbγ hbγ' hcc'
  exact Subtype.ext hEqG

theorem ncard_orbit_Malpha_eq_ncard_conj (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β) :
    ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard =
      ((fun y => y * b * y⁻¹) ''
        (CFSG.pCore 2 (Halpha D hC.alpha) : Set (Halpha D hC.alpha))).ncard := by
  classical
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  let M := Malpha D hC.alpha
  have himage : (fun x : G => cimg x β) '' (M : Set G) =
      (fun y : H => cimg (y : G) β) '' (Q : Set H) := by
    apply Set.Subset.antisymm
    · rintro S ⟨x, hx, rfl⟩
      obtain ⟨y, hyQ, hye⟩ :=
        exists_mem_pCore_cimg_eq h113 hC hrad hn3 hHns hβ hx
      exact ⟨y, hyQ, hye⟩
    · rintro S ⟨y, hyQ, rfl⟩
      exact ⟨(y : G), Subgroup.mem_map.mpr
        ⟨y, CFSG.pCore_le_solvableRadical 2 H hyQ, rfl⟩, rfl⟩
  rw [himage]
  refine orbitPower_ncard_image_eq_of_fiber (s := (Q : Set H))
    (f := fun y : H => cimg (y : G) β) (g := fun y : H => y * b * y⁻¹) ?_
  intro y hyQ y' hy'Q
  exact ⟨fun hc => orbitPower_conj_eq_of_cimg_eq h89 h113 hC hrad hW hn3 hHns
      hβ hb hyQ hy'Q hc,
    fun hg => orbitPower_cimg_eq_of_conj_eq hC hβ hb hg⟩

theorem orbitPower_solvableRadical_le_center_of_fix (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hfix : ∀ {δ : Set G}, δ ∈ Dalpha D hC.alpha →
      ∀ x ∈ Malpha D hC.alpha, cimg x δ = δ) :
    CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha) := by
  let H := Halpha D hC.alpha
  intro x hx
  have hxM : (x : G) ∈ Malpha D hC.alpha := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro h
  have hxfix : ∀ d ∈ DstarH hC, x * d * x⁻¹ = d := by
    intro d hd
    obtain ⟨δ, hδ, hdδ⟩ := (mem_DstarH_iff hC).mp hd
    have hxd : (x : G) * (d : G) * (x : G)⁻¹ ∈ δ := by
      have hmem : (x : G) * (d : G) * (x : G)⁻¹ ∈ cimg (x : G) δ :=
        ⟨(d : G), hdδ, rfl⟩
      rwa [hfix hδ (x : G) hxM] at hmem
    have hcc' : (d : G)⁻¹ * ((x : G) * (d : G) * (x : G)⁻¹) ∈
        Malpha D hC.alpha := by
      refine Subgroup.mem_map.mpr ⟨d⁻¹ * x * d * x⁻¹, ?_, ?_⟩
      · have h1 : d⁻¹ * x * d ∈ CFSG.solvableRadical H := by
          simpa using (inferInstance : (CFSG.solvableRadical H).Normal).conj_mem x hx d⁻¹
        exact (CFSG.solvableRadical H).mul_mem h1 ((CFSG.solvableRadical H).inv_mem hx)
      · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
        group
    have hEqG := eq_of_mem_of_inv_mul_mem_Malpha h89 h113 hC hrad hW hn3 hHns
      hδ hdδ hxd hcc'
    exact Subtype.ext hEqG.symm
  have hclosure : Subgroup.closure (DstarH hC) ≤ Subgroup.centralizer ({x} : Set H) := by
    rw [Subgroup.closure_le]
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc d * x = (x * d * x⁻¹) * x := by rw [hxfix d hd]
        _ = x * d := by group)
  have hh : h ∈ Subgroup.closure (DstarH hC) := by
    rw [DstarH_closure_eq_top hC]
    exact Subgroup.mem_top h
  exact Subgroup.mem_centralizer_singleton_iff.mp (hclosure hh)

theorem one_lt_ncard_orbit_Malpha (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    1 < ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard := by
  classical
  let H := Halpha D hC.alpha
  by_contra hlt
  push Not at hlt
  have hfix : ∀ {δ : Set G}, δ ∈ Dalpha D hC.alpha →
      ∀ x ∈ Malpha D hC.alpha, cimg x δ = δ := by
    intro δ hδ x hx
    have hTle : ((fun y : G => cimg y δ) '' (Malpha D hC.alpha : Set G)).ncard ≤ 1 := by
      rw [ncard_orbit_Malpha_eq hC hβ hδ]
      exact hlt
    have hxT : cimg x δ ∈
        (fun y : G => cimg y δ) '' (Malpha D hC.alpha : Set G) := ⟨x, hx, rfl⟩
    have hδT : δ ∈ (fun y : G => cimg y δ) '' (Malpha D hC.alpha : Set G) :=
      ⟨1, Subgroup.one_mem _, by simp [cimg]⟩
    exact (Set.ncard_le_one_iff (Set.toFinite _)).mp hTle hxT hδT
  exact hMZ (orbitPower_solvableRadical_le_center_of_fix h89 h113 hC hrad hW hn3 hHns hfix)

theorem exists_ncard_orbit_Malpha_eq_two_pow (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    ∃ s : ℕ, ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ s := by
  classical
  obtain ⟨b, hb⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
  let bH : Halpha D hC.alpha := ⟨b, Subgroup.subset_closure ⟨β, hβ, hb⟩⟩
  have hbH : (bH : G) ∈ β := hb
  rw [ncard_orbit_Malpha_eq_ncard_conj h89 h113 hC hrad hW hn3 hHns hβ hbH]
  let Q := CFSG.pCore 2 (Halpha D hC.alpha)
  let φ : Q →* MulAut (Halpha D hC.alpha) := MulAut.conj.comp Q.subtype
  let _ : MulAction Q (Halpha D hC.alpha) := MulAction.compHom (Halpha D hC.alpha) φ
  have horb : (fun y : Halpha D hC.alpha => y * bH * y⁻¹) ''
      (Q : Set (Halpha D hC.alpha)) = MulAction.orbit Q bH := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
  obtain ⟨s, hs⟩ := IsPGroup.card_orbit
    (CFSG.pCore_isPGroup (G := Halpha D hC.alpha) (p := 2)) bH
  refine ⟨s, ?_⟩
  rw [horb, ← Nat.card_coe_set_eq]
  exact hs

end CFSG.OddTranspositions.PartFour
