module

public import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.Torsion37

open CFSG CFSG.RankThree.GroupTheory Subgroup
open scoped commutatorElement

theorem qd32_facts {G : Type} [Group G] {R : Subgroup G} (h : Nonempty (R ≃* QD32)) :
    IsExtraspecialPGroup 2 R ∧ Nat.card R = 32 ∧
      ∃ s ∈ R, orderOf s = 2 ∧ s ∉ inSubgroup Subgroup.center R := by
  obtain ⟨e⟩ := h
  obtain ⟨hcard, hext, hgen, -⟩ :=
    SteinbergBY.quaternion_dihedral_extraspecial_involution_generation
  have hR32 : Nat.card R = 32 := by rw [Nat.card_congr e.toEquiv]; exact hcard
  have hRext : IsExtraspecialPGroup 2 R := isExtraspecialPGroup_of_mulEquiv e.symm hext
  refine ⟨hRext, hR32, ?_⟩
  by_contra hno
  have hctr : ∀ g : R, orderOf g = 2 → g ∈ Subgroup.center R := by
    intro g hg
    by_contra hgc
    apply hno
    refine ⟨(g : G), g.2, by rw [Subgroup.orderOf_coe]; exact hg, ?_⟩
    rintro ⟨y, hy, hyg⟩
    exact hgc (by rw [Subtype.ext hyg] at hy; exact hy)
  have hall : ∀ y ∈ Subgroup.closure {g : QD32 | orderOf g = 2}, e.symm y ∈ Subgroup.center R := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      refine hctr _ ?_
      rw [MulEquiv.orderOf_eq]
      exact hx
    | one => rw [map_one]; exact one_mem _
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  have hctop : Subgroup.center R = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have := hall (e x) (by rw [hgen]; exact mem_top _)
    rwa [MulEquiv.symm_apply_apply] at this
  have hcomm : commutator R = ⊥ := (commutator_eq_bot_iff_center_eq_top R).mpr hctop
  have hbt : (⊥ : Subgroup R) = ⊤ := by rw [← hcomm, hRext.2.1, hctop]
  have hone : Nat.card R = 1 := by
    rw [← Subgroup.card_top, ← hbt, Subgroup.card_bot]
  omega

@[expose, instance_reducible] def conjAct {G : Type} [Group G] {A R : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) : MulAction A R where
  smul a r := ⟨a * r * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hAR a.2) r).mp r.2⟩
  one_smul r := Subtype.ext (by change (1 : G) * r * (1 : G)⁻¹ = r; simp)
  mul_smul a b r := Subtype.ext (by
    change ((a * b : A) : G) * r * ((a * b : A) : G)⁻¹ =
      (a : G) * ((b : G) * r * (b : G)⁻¹) * (a : G)⁻¹
    simp [mul_assoc])

theorem comm_sq_of_conj {G : Type*} [Group G] (r g y : G) (hyy : y * y = 1)
    (h1 : g * r * g⁻¹ = y * r) (h2 : g * y * g⁻¹ = y) : (g * g) * r = r * (g * g) := by
  have : (g * g) * r * (g * g)⁻¹ = r := by
    calc (g * g) * r * (g * g)⁻¹ = g * (g * r * g⁻¹) * g⁻¹ := by group
      _ = g * (y * r) * g⁻¹ := by rw [h1]
      _ = (g * y * g⁻¹) * (g * r * g⁻¹) := by group
      _ = y * (y * r) := by rw [h2, h1]
      _ = (y * y) * r := by group
      _ = r := by rw [hyy]; group
  calc (g * g) * r = ((g * g) * r * (g * g)⁻¹) * (g * g) := by group
    _ = r * (g * g) := by rw [this]

theorem comm_of_comm_sq {G : Type*} [Group G] (r g : G) (h5 : g ^ 5 = 1)
    (h : (g * g) * r = r * (g * g)) : g * r = r * g := by
  have h4 : (g * g) ^ 3 = g := by
    rw [← pow_two, ← pow_mul]
    calc g ^ (2 * 3) = g ^ 5 * g := by rw [← pow_succ]
      _ = g := by rw [h5, one_mul]
  have hc : Commute (g * g) r := h
  have := (hc.pow_left 3).eq
  rw [h4] at this
  exact this

theorem exists_fixed_point_free_of_commutator {G : Type} [Group G] [Finite G] {A R : Subgroup G}
    (hA : Nat.card A = 5) (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRA : ⁅R, A⁆ = R)
    (hR : IsExtraspecialPGroup 2 R) (hR32 : Nat.card R = 32) :
    ∃ a ∈ A, ∀ r ∈ R, r ∉ inSubgroup Subgroup.center R →
      ⁅a, r⁆ ∉ inSubgroup Subgroup.center R := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hApg : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  let _ : MulAction A R := conjAct hAR
  have hmod := hApg.card_modEq_card_fixedPoints R
  set CA : Subgroup R := (centralizer (A : Set G)).subgroupOf R with hCA
  have hfix : MulAction.fixedPoints A R = (CA : Set R) := by
    ext r
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, hCA, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h g hg
      have := congrArg Subtype.val (h ⟨g, hg⟩)
      change g * r * g⁻¹ = r at this
      calc g * r = g * r * g⁻¹ * g := by group
        _ = r * g := by rw [this]
    · intro h a
      apply Subtype.ext
      change (a : G) * r * (a : G)⁻¹ = r
      rw [h a a.2]
      group
  have hcardfix : Nat.card (MulAction.fixedPoints A R) = Nat.card CA := by
    rw [hfix]; rfl
  have hdvd : Nat.card CA ∣ 32 := hR32 ▸ Subgroup.card_subgroup_dvd_card CA
  have hmod' : 32 ≡ Nat.card CA [MOD 5] := by rw [← hR32, ← hcardfix]; exact hmod
  have hc : Nat.card CA = 2 ∨ Nat.card CA = 32 := by
    obtain ⟨c, hc⟩ : ∃ c, c = Nat.card CA := ⟨_, rfl⟩
    rw [← hc] at hdvd hmod' ⊢
    have hle : c ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hmod'
    interval_cases c <;> omega
  have hZcard : Nat.card (Subgroup.center R) = 2 := hR.2.2.2
  have hc2 : Nat.card CA = 2 := by
    rcases hc with h | h
    · exact h
    · exfalso
      have htop : CA = ⊤ := Subgroup.eq_top_of_card_eq CA (by rw [h, hR32])
      have hRle : R ≤ centralizer (A : Set G) := by
        intro r hr
        have : (⟨r, hr⟩ : R) ∈ CA := htop ▸ mem_top _
        exact (Subgroup.mem_subgroupOf.mp this)
      have hbot : ⁅R, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRle
      have h1 : Nat.card R = 1 := by
        rw [← hRA, hbot]
        exact Subgroup.card_bot
      omega
  have huniq : ∀ x y : Subgroup.center R, x ≠ 1 → y ≠ 1 → x = y := by
    intro x y hx hy
    obtain ⟨w, hw, hwu⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center R)).mp hZcard
    rw [hwu x hx, hwu y hy]
  have hZle : Subgroup.center R ≤ CA := by
    intro z hz
    rw [hCA, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro g hg
    have hgn := Subgroup.mem_normalizer_iff.mp (hAR hg)
    have hgn' := Subgroup.mem_normalizer_iff.mp (hAR (Subgroup.inv_mem A hg))
    let z' : R := ⟨g * z * g⁻¹, (hgn z).mp z.2⟩
    have hz'c : z' ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy' : g⁻¹ * y * g ∈ R := by
        have := (hgn' y).mp y.2
        simpa using this
      have hzc := Subgroup.mem_center_iff.mp hz ⟨g⁻¹ * y * g, hy'⟩
      have hzc' : (g⁻¹ * y * g) * (z : G) = (z : G) * (g⁻¹ * y * g) := congrArg Subtype.val hzc
      apply Subtype.ext
      change (y : G) * (g * z * g⁻¹) = g * z * g⁻¹ * y
      calc (y : G) * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hzc']
        _ = g * z * g⁻¹ * y := by group
    by_cases hz1 : z = 1
    · simp [hz1]
    · have hzz : (⟨z, hz⟩ : Subgroup.center R) ≠ 1 := fun h =>
        hz1 (by simpa using congrArg Subtype.val h)
      have hz'1 : (⟨z', hz'c⟩ : Subgroup.center R) ≠ 1 := by
        intro h
        apply hz1
        have h1 : z' = 1 := by simpa using congrArg Subtype.val h
        have h2 : g * (z : G) * g⁻¹ = 1 := congrArg Subtype.val h1
        have : (z : G) = 1 := by
          calc (z : G) = g⁻¹ * (g * z * g⁻¹) * g := by group
            _ = 1 := by rw [h2]; group
        exact Subtype.ext this
      have := huniq _ _ hz'1 hzz
      have h3 : g * (z : G) * g⁻¹ = z :=
        congrArg (fun w : Subgroup.center R => ((w : R) : G)) this
      calc g * (z : G) = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h3]
  have hCAeq : CA = Subgroup.center R :=
    (Subgroup.eq_of_le_of_card_ge hZle (by rw [hc2, hZcard])).symm
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hA]; norm_num)
  obtain ⟨a, ha1⟩ := exists_ne (1 : A)
  refine ⟨a, a.2, ?_⟩
  intro r hr hrZ hcomm
  apply hrZ
  obtain ⟨y, hy, hyc⟩ := hcomm
  have hyc' : (y : G) = ⁅(a : G), r⁆ := hyc
  have hyCA : y ∈ CA := hZle hy
  have hyA : ∀ g ∈ A, g * (y : G) = (y : G) * g := by
    have := Subgroup.mem_subgroupOf.mp hyCA
    rw [Subgroup.mem_centralizer_iff] at this
    exact this
  have hyy : (y : G) * y = 1 := by
    have h := pow_card_eq_one' (G := Subgroup.center R) (x := ⟨y, hy⟩)
    rw [hZcard] at h
    have := congrArg (fun w : Subgroup.center R => ((w : R) : G)) h
    simpa [pow_two] using this
  have h1 : (a : G) * r * (a : G)⁻¹ = (y : G) * r := by
    rw [hyc', commutatorElement_def]; group
  have h2 : (a : G) * (y : G) * (a : G)⁻¹ = (y : G) := by
    calc (a : G) * (y : G) * (a : G)⁻¹ = (y : G) * a * (a : G)⁻¹ := by rw [hyA a a.2]
      _ = (y : G) := by group
  have h3 := comm_sq_of_conj r (a : G) (y : G) hyy h1 h2
  have ha5 : (a : G) ^ 5 = 1 := by
    have h := pow_card_eq_one' (G := A) (x := a)
    rw [hA] at h
    simpa using congrArg (fun w : A => (w : G)) h
  have hra : (a : G) * r = r * a := comm_of_comm_sq r (a : G) ha5 h3
  have hAall : ∀ g ∈ A, g * r = r * g := by
    intro g hg
    have hgen := zpowers_eq_top_of_prime_card (p := 5) (G := A) hA ha1
    have hmem : (⟨g, hg⟩ : A) ∈ Subgroup.zpowers a := by rw [hgen]; exact mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : (a : G) ^ k = g := congrArg Subtype.val hk
    rw [← hk']
    have hc : Commute (a : G) r := hra
    exact (hc.zpow_left k).eq
  have hrCA : (⟨r, hr⟩ : R) ∈ CA := by
    rw [hCA, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    exact hAall
  rw [hCAeq] at hrCA
  exact ⟨⟨r, hr⟩, hrCA, rfl⟩

end CFSG.RankThree.PartOne.Torsion37
