module

public import CFSG.RankThree.PartOne.S11d.Sec109Common
public import CFSG.RankThree.PartOne.S11d.ThreeRank
public import CFSG.RankThree.PartOne.S12.Sec12TwoAssembly

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

namespace Sec109

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L B : Subgroup G}
  {n : ℕ}

theorem Config.centralizer_inf_L (h : Config p A c L B n) :
    centralizer (B : Set G) ⊓ L = B := by
  obtain ⟨b₁, b₂, x₁, x₂, x, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCL⟩ :=
    h.structure_B
  exact hCL

theorem Config.B_le_L (h : Config p A c L B n) : B ≤ L := by
  rw [h.B_eq]
  exact inf_le_right

theorem Config.exists_two_subgroup (h : Config p A c L B n) :
    ∃ S : Subgroup G, S ≤ L ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ normalizer (S : Set G) ∧
      S = ⁅S, A⁆ := by
  obtain ⟨-, S, hSL, hS1, hS2, hAS, hSA⟩ := (sectionTenZeroStar_subset p A).1 h.L_mem.1
  exact ⟨S, hSL, hS1, hS2, hAS, hSA⟩

theorem Config.exists_x3 (h : Config p A c L B n) :
    ∃ (x : G) (lam : ℤ), x ∈ L ∧ x ≠ 1 ∧ x ∈ normalizer (B : Set G) ∧ x ^ 3 = 1 ∧
      ¬ (7 : ℤ) ∣ lam - 1 ∧ ∀ b ∈ B, x * b * x⁻¹ = b ^ lam := by
  obtain ⟨b₁, b₂, x₁, x₂, x, -, -, -, -, -, hx₁L, hx₂L, hx₁N, hx₂N, hox₁, hox₂, hx₁₂, -, -,
    hxcl, hx1, ⟨lam, hlam, hx⟩, -⟩ := h.structure_B
  have hx₁3 : x₁ ^ 3 = 1 := hox₁ ▸ pow_orderOf_eq_one x₁
  have hx₂3 : x₂ ^ 3 = 1 := hox₂ ▸ pow_orderOf_eq_one x₂
  have hcomm : Commute x₁ x₂ := hx₁₂
  have hle : Subgroup.closure ({x₁, x₂} : Set G) ≤ zpowers x₁ ⊔ zpowers x₂ := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_sup_left (mem_zpowers _)
    · exact Subgroup.mem_sup_right (mem_zpowers _)
  obtain ⟨s, t, hst⟩ := (S11d.mem_zpowers_sup_zpowers_iff hcomm).mp (hle hxcl)
  have hx3 : x ^ 3 = 1 := by
    have hz3 : ∀ (u : G) (s : ℤ), u ^ 3 = 1 → (u ^ s) ^ 3 = 1 := fun u s hu => by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
    have hc2 : Commute (x₁ ^ s) (x₂ ^ t) := Commute.zpow_zpow hcomm s t
    rw [hst, hc2.mul_pow, hz3 _ _ hx₁3, hz3 _ _ hx₂3, one_mul]
  refine ⟨x, lam, ?_, hx1, ?_, hx3, hlam, hx⟩
  · have hle' : Subgroup.closure ({x₁, x₂} : Set G) ≤ L := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact hx₁L
      · exact hx₂L
    exact hle' hxcl
  · have hle' : Subgroup.closure ({x₁, x₂} : Set G) ≤ normalizer (B : Set G) := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact hx₁N
      · exact hx₂N
    exact hle' hxcl

theorem Config.zpow_ne_self (h : Config p A c L B n) {b : G} (hb : b ∈ A) (hb1 : b ≠ 1)
    {lam : ℤ} (hlam : ¬ (7 : ℤ) ∣ lam - 1) : b ^ lam ≠ b := by
  intro heq
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf b = p := orderOf_eq_prime (h.pow_p_eq_one hb) hb1
  have h1 : b ^ (lam - 1) = 1 := by
    rw [zpow_sub, zpow_one, heq, mul_inv_cancel]
  have h2 : (orderOf b : ℤ) ∣ lam - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hord, h.p_eq] at h2
  exact hlam h2

theorem Config.mem_of_mem_centralizer (h : Config p A c L B n) {u : G}
    (hu : u ∈ centralizer (A : Set G)) (hup : u ^ p = 1) : u ∈ A := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := sectionTenSetup_three_lt h.setup
  have hev : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq h.setup).le
  have hcA : c ∈ A := h.c_mem
  have huc : u ∈ centralizer ({c} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp hu c hcA).symm
  have huN : u ∈ normalizer (L : Set G) :=
    mem_normalizer_of_mem_centralizer_thetaComponentsAt hp hp3 hev h.L_mem.2 huc hup
  obtain ⟨l, hlL, hl⟩ := S11d.exists_inner_of_pow_prime h.model hp (by omega) huN (a := 1)
    (by simpa using hup)
  have hBL : B ≤ L := h.B_le_L
  have hlB : l ∈ B := by
    have hmem : l ∈ centralizer (B : Set G) ⊓ L := by
      refine ⟨mem_centralizer_iff.mpr fun b hb => ?_, hlL⟩
      have h1 := hl b (hBL hb)
      have h2 : u * b * u⁻¹ = b := by
        have := mem_centralizer_iff.mp hu b (h.B_le_A hb)
        rw [← this]
        group
      rw [h2] at h1
      calc b * l = (l * b * l⁻¹) * l := by rw [← h1]
        _ = l * b := by group
    rwa [h.centralizer_inf_L] at hmem
  have hlA : l ∈ A := h.B_le_A hlB
  set z : G := l⁻¹ * u with hz
  have hzL : z ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro g hg
    have h1 := hl g hg
    calc g * (l⁻¹ * u) = l⁻¹ * (l * g * l⁻¹) * u := by group
      _ = l⁻¹ * (u * g * u⁻¹) * u := by rw [h1]
      _ = (l⁻¹ * u) * g := by group
  have hzA : z ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    have h1 : a * l⁻¹ = l⁻¹ * a := h.A_comm a ha l⁻¹ (A.inv_mem hlA)
    have h2 : a * u = u * a := mem_centralizer_iff.mp hu a ha
    calc a * (l⁻¹ * u) = (a * l⁻¹) * u := by group
      _ = (l⁻¹ * a) * u := by rw [h1]
      _ = l⁻¹ * (a * u) := by group
      _ = l⁻¹ * (u * a) := by rw [h2]
      _ = (l⁻¹ * u) * a := by group
  have hzp : z ^ p = 1 := by
    have hcomm : Commute l⁻¹ u := mem_centralizer_iff.mp hu l⁻¹ (A.inv_mem hlA)
    rw [hz, hcomm.mul_pow, inv_pow, h.pow_p_eq_one hlA, hup]
    simp
  have hzmem : z ∈ A := by
    by_contra hzn
    have hz1 : z ≠ 1 := fun h1 => hzn (h1 ▸ A.one_mem)
    obtain ⟨S, hSL, hS1, hS2, hAS, -⟩ := h.exists_two_subgroup
    have hHloc : IsTwoLocal (normalizer (S : Set G)) := ⟨S, hS1, hS2, rfl⟩
    have hPQ : A ⊓ zpowers z = ⊥ := Sec12Two.inf_zpowers_eq_bot hp hzp hzn
    have hP : IsElemAbelian p A :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).mp h.A_elem
    have hQ : IsElemAbelian p (zpowers z) :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp
        (IsElementaryAbelian.zpowers_of_pow_eq_one hzp)
    have hcomm : ∀ x ∈ A, ∀ y ∈ zpowers z, Commute x y := by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
      exact Commute.zpow_right (show Commute x z from mem_centralizer_iff.mp hzA x hx) i
    have hQH : zpowers z ≤ normalizer (S : Set G) := by
      have hzS : z ∈ centralizer (S : Set G) :=
        centralizer_le (SetLike.coe_subset_coe.mpr hSL) hzL
      exact (zpowers_le).mpr (centralizer_le_normalizer _ hzS)
    have hcard : Nat.card (zpowers z) = p ^ 1 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1, pow_one]
    have h4 := Sec12Two.le_pRank_of_commute_of_inf_eq_bot hp hP hQ hcomm hPQ
      (a := 3) (b := 1) h.A_card hcard hAS hQH
    have h5 := Sec12Two.pRank_le_evenRank_of_isTwoLocal hp (by omega) hHloc
    omega
  have hu' : u = l * z := by rw [hz]; group
  rw [hu']
  exact A.mul_mem hlA hzmem

theorem Config.mem_normalizer_L (h : Config p A c L B n) (hqL : CFSG.IsQuasisimple ↥L) {b y : G}
    (hbB : b ∈ B) (hb1 : b ≠ 1) (hy : y ∈ normalizer (zpowers c : Set G))
    (hyb : y * b = b * y) : y ∈ normalizer (L : Set G) := by
  have hp := h.prime
  by_contra hyL
  set L' : Subgroup G := L.map (MulAut.conj y).toMonoidHom with hL'
  have hL'c : L' ∈ thetaComponentsAt p c :=
    Sec12TwoAssembly.conj_mem_thetaComponentsAt hp hy h.L_mem.2
  have hne : L' ≠ L := fun heq => hyL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
  have hbL : b ∈ L := h.B_le_L hbB
  have hbL' : b ∈ L' := by
    refine Subgroup.mem_map.mpr ⟨b, hbL, ?_⟩
    change y * b * y⁻¹ = b
    rw [hyb]
    group
  have hcent := Sec12TwoAssembly.le_centralizer_of_mem_thetaComponentsAt_ne hp hL'c h.L_mem.2 hqL
    hne (B := zpowers b) ((zpowers_le).mpr hbL') ((zpowers_le).mpr (le_normalizer hbL))
  have hbc : b ∈ centralizer (L : Set G) := hcent (mem_zpowers b)
  have hcenter : Subgroup.center ↥L = ⊥ := (lnTwoOuter ↥L n h.model).1
  have hmem : (⟨b, hbL⟩ : L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp hbc g g.2)
  rw [hcenter, Subgroup.mem_bot] at hmem
  exact hb1 (congrArg Subtype.val hmem)

end Sec109

end CFSG.RankThree.PartOne
