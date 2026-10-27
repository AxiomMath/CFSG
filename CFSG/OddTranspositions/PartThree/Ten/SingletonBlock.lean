module

public import CFSG.OddTranspositions.PartThree.Ten.SwapImage
import CFSG.OddTranspositions.PartThree.Ten.SwapKlein
import CFSG.OddTranspositions.PartThree.Ten.DalphaBlocks
import CFSG.OddTranspositions.PartThree.Ten.CentralSymSplit
import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.OddTranspositions.FusionStep
import CFSG.Timmesfeld.Bridge.Asc72ZQuot
import CFSG.OddTranspositions.SecondKindCoset

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72

theorem mul_self_eq_one_of_mem_closure {X : Type*} [Group X] {s : Set X}
    (hsq : ∀ x ∈ s, x * x = 1) (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) {g : X}
    (hg : g ∈ Subgroup.closure s) : g * g = 1 := by
  have hcomm : IsMulCommutative (Subgroup.closure s) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x :=
      congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [ihx, inv_one]

theorem exists_sylow_of_commuting_involutions {X : Type*} [Group X] {s : Set X}
    (hsq : ∀ x ∈ s, x * x = 1) (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    ∃ S : Sylow 2 X, s ⊆ (S : Set X) := by
  have hP : IsPGroup 2 (Subgroup.closure s) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    have := mul_self_eq_one_of_mem_closure hsq hc g.2
    simpa [pow_two] using this
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  exact ⟨S, fun x hx => hS (Subgroup.subset_closure hx)⟩

theorem eq_one_of_mem_center_of_pCore_eq_bot {H : Type*} [Group H]
    (hQ : CFSG.pCore 2 H = ⊥) {m : H} (hm : m ∈ Subgroup.center H) (hmm : m * m = 1) :
    m = 1 := by
  have hnorm : (Subgroup.zpowers m).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hm)
  have hdd : m ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two, hmm]
  have hp : IsPGroup 2 (Subgroup.zpowers m) := CentralQuot.isPGroup_zpowers_of_pow hdd
  have hle : Subgroup.zpowers m ≤ CFSG.pCore 2 H := le_sSup ⟨hnorm, hp⟩
  rw [hQ] at hle
  exact Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers m))

theorem eq_of_tenHom_eq {G : Type} [Group G] [Finite G] {D : Set G} (hC : HypothesisC D)
    {f n : ℕ} (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)
    (hQ : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {a b : Halpha D hC.alpha} (ha : a * a = 1)
    (hb : b * b = 1) (h : tenHom hC e a = tenHom hC e b) : a = b := by
  have hm : a⁻¹ * b ∈ Subgroup.center (Halpha D hC.alpha) := by
    rw [← tenHom_ker hC e, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hba : b * a = a * b := by
    have h1 := Subgroup.mem_center_iff.1 hm a
    rw [mul_inv_cancel_left, hai] at h1
    calc b * a = (a * b * a) * a := by rw [← h1]
      _ = a * b * (a * a) := by group
      _ = a * b := by rw [ha, mul_one]
  have hmm : (a⁻¹ * b) * (a⁻¹ * b) = 1 := by
    rw [hai]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  exact inv_mul_eq_one.1 (eq_one_of_mem_center_of_pCore_eq_bot hQ hm hmm)

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_commuting_lifts (hC : HypothesisC D) {f n : ℕ} (hf : 2 ≤ f) (hn : 5 ≤ n)
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)
    (hQ : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) :
    ∃ a b₁ b₂ b₃ : Halpha D hC.alpha, a ∈ DstarH hC ∧ b₁ ∈ DstarH hC ∧ b₂ ∈ DstarH hC ∧
      b₃ ∈ DstarH hC ∧
      (∀ x ∈ ({a, b₁, b₂, b₃} : Set (Halpha D hC.alpha)),
        ∀ y ∈ ({a, b₁, b₂, b₃} : Set (Halpha D hC.alpha)), x * y = y * x) ∧
      b₁ ≠ a ∧ b₂ ≠ a ∧ b₃ ≠ a ∧ a = b₁ * b₂ * b₃ := by
  have hSodd : IsOddTransp (DstarH hC) := DstarH_isOddTransp hC
  obtain ⟨v, x₁, x₂, x₃, hv, hx₁, hx₂, hx₃, hprod, c01, c02, c03, c12, c13, c23, n01, n02, n03,
    n12, n13, n23⟩ := SwapKlein.exists_swap_triple hf (by omega : 2 ≤ n)
  have hlift : ∀ w ∈ WreathEndgame.swapSet f n, ∃ y ∈ DstarH hC, tenHom hC e y = w := by
    intro w hw
    rw [← tenHom_image_DstarH hC hf hn e] at hw
    obtain ⟨y, hy, hyw⟩ := hw
    exact ⟨y, hy, hyw⟩
  obtain ⟨a, ha, rfl⟩ := hlift v hv
  obtain ⟨b₁, hb₁, rfl⟩ := hlift x₁ hx₁
  obtain ⟨b₂, hb₂, rfl⟩ := hlift x₂ hx₂
  obtain ⟨b₃, hb₃, rfl⟩ := hlift x₃ hx₃
  have hcom : ∀ {x y : Halpha D hC.alpha}, x ∈ DstarH hC → y ∈ DstarH hC →
      Commute (tenHom hC e x) (tenHom hC e y) → tenHom hC e x ≠ tenHom hC e y → x * y = y * x :=
    fun hx hy hc hne => CentralSymSplit.commute_of_map_commute (tenHom hC e) hSodd hx hy hc.eq hne
  have h01 := hcom ha hb₁ c01 n01
  have h02 := hcom ha hb₂ c02 n02
  have h03 := hcom ha hb₃ c03 n03
  have h12 := hcom hb₁ hb₂ c12 n12
  have h13 := hcom hb₁ hb₃ c13 n13
  have h23 := hcom hb₂ hb₃ c23 n23
  have hT4 : ∀ x ∈ ({a, b₁, b₂, b₃} : Set (Halpha D hC.alpha)),
      ∀ y ∈ ({a, b₁, b₂, b₃} : Set (Halpha D hC.alpha)), x * y = y * x := by
    rintro x (rfl | rfl | rfl | rfl) y (rfl | rfl | rfl | rfl) <;>
      first
      | rfl
      | assumption
      | exact (by assumption : _ * _ = _ * _).symm
  have hT4sq : ∀ x ∈ ({a, b₁, b₂, b₃} : Set (Halpha D hC.alpha)), x * x = 1 := by
    rintro x (rfl | rfl | rfl | rfl)
    exacts [hSodd.mul_self_eq_one ha, hSodd.mul_self_eq_one hb₁, hSodd.mul_self_eq_one hb₂,
      hSodd.mul_self_eq_one hb₃]
  have hmem : b₁ * b₂ * b₃ ∈ Subgroup.closure ({a, b₁, b₂, b₃} : Set (Halpha D hC.alpha)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
  refine ⟨a, b₁, b₂, b₃, ha, hb₁, hb₂, hb₃, hT4, fun h => n01 (congrArg (tenHom hC e) h.symm),
    fun h => n02 (congrArg (tenHom hC e) h.symm), fun h => n03 (congrArg (tenHom hC e) h.symm),
    ?_⟩
  refine eq_of_tenHom_eq hC e hQ (hSodd.mul_self_eq_one ha)
    (mul_self_eq_one_of_mem_closure hT4sq hT4 hmem) ?_
  rw [map_mul, map_mul]
  exact hprod.symm

theorem false_of_commuting_lifts (hC : HypothesisC D)
    (hnot : ¬ hC.alpha ⊆ (Halpha D hC.alpha : Set G)) (hα : hC.alpha = {hC.d})
    {a b₁ b₂ b₃ : Halpha D hC.alpha} (ha : a ∈ DstarH hC) (hb₁ : b₁ ∈ DstarH hC)
    (hb₂ : b₂ ∈ DstarH hC) (hb₃ : b₃ ∈ DstarH hC)
    (hT4 : ∀ x ∈ ({a, b₁, b₂, b₃} : Set (Halpha D hC.alpha)),
      ∀ y ∈ ({a, b₁, b₂, b₃} : Set (Halpha D hC.alpha)), x * y = y * x)
    (hne₁ : b₁ ≠ a) (hne₂ : b₂ ≠ a) (hne₃ : b₃ ≠ a) (hprodH : a = b₁ * b₂ * b₃) : False := by
  have hodd := hC.setup.oddT
  have hSodd : IsOddTransp (DstarH hC) := DstarH_isOddTransp hC
  have hT4sq : ∀ x ∈ ({a, b₁, b₂, b₃} : Set (Halpha D hC.alpha)), x * x = 1 := by
    rintro x (rfl | rfl | rfl | rfl)
    exacts [hSodd.mul_self_eq_one ha, hSodd.mul_self_eq_one hb₁, hSodd.mul_self_eq_one hb₂,
      hSodd.mul_self_eq_one hb₃]
  have hDmem : ∀ x : Halpha D hC.alpha, x ∈ DstarH hC → (x : G) ∈ D := fun x hx =>
    DalphaStar_subset hC.isBlock_alpha hx
  have hcommu : ∀ x : Halpha D hC.alpha, Commute (x : G) hC.d := fun x =>
    WreathEndgame.commute_d_of_mem_Halpha hC x.2
  set T4 : Set (Halpha D hC.alpha) := {a, b₁, b₂, b₃} with hT4def
  set s : Set G := insert hC.d (((↑) : Halpha D hC.alpha → G) '' T4) with hsdef
  have hs_sq : ∀ x ∈ s, x * x = 1 := by
    rintro x (rfl | ⟨y, hy, rfl⟩)
    · exact hodd.mul_self_eq_one hC.hd
    · exact congrArg Subtype.val (hT4sq y hy)
  have hs_comm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    rintro x (rfl | ⟨x', hx', rfl⟩) y (rfl | ⟨y', hy', rfl⟩)
    · rfl
    · exact (hcommu y').eq.symm
    · exact (hcommu x').eq
    · exact congrArg Subtype.val (hT4 x' hx' y' hy')
  obtain ⟨S, hS⟩ := exists_sylow_of_commuting_involutions hs_sq hs_comm
  have hmemS : ∀ x ∈ T4, (x : G) ∈ (S : Set G) := fun x hx => hS (Or.inr ⟨x, hx, rfl⟩)
  have huS : hC.d ∈ (S : Set G) := hS (Or.inl rfl)
  have haS : (a : G) ∈ (S : Set G) ∩ D := ⟨hmemS a (by simp [hT4def]), hDmem a ha⟩
  have huSD : hC.d ∈ (S : Set G) ∩ D := ⟨huS, hC.hd⟩
  obtain ⟨h, hh, hhe⟩ := sylow_inter_D_transitive hC.setup.isClass hodd S haS huSD
  have key : ∀ b ∈ T4, b ∈ DstarH hC → b ≠ a → h * (b : G) * h⁻¹ ∈ Halpha D hC.alpha := by
    intro b hbT hbS hne
    have hbS' : (b : G) ∈ (S : Set G) ∩ D := ⟨hmemS b hbT, hDmem b hbS⟩
    have hz : h * (b : G) * h⁻¹ ∈ (S : Set G) ∩ D :=
      (Subgroup.mem_set_normalizer_iff.1 hh _).1 hbS'
    have hzu : h * (b : G) * h⁻¹ ≠ hC.d := by
      intro h'
      rw [← hhe] at h'
      exact hne (Subtype.ext (mul_left_cancel (mul_right_cancel h')))
    have hzc : Commute (h * (b : G) * h⁻¹) hC.d :=
      hodd.commute_of_isPGroup S.isPGroup' hz.2 hC.hd hz.1 huS
    exact Subgroup.subset_closure (mem_DalphaStar_of_alpha_eq_singleton hC hα hz.2 hzu hzc)
  have hz1 := key b₁ (by simp [hT4def]) hb₁ hne₁
  have hz2 := key b₂ (by simp [hT4def]) hb₂ hne₂
  have hz3 := key b₃ (by simp [hT4def]) hb₃ hne₃
  have huH : hC.d ∈ Halpha D hC.alpha := by
    have hprodG : (a : G) = (b₁ : G) * b₂ * b₃ := congrArg Subtype.val hprodH
    have hd : hC.d = (h * (b₁ : G) * h⁻¹) * (h * (b₂ : G) * h⁻¹) * (h * (b₃ : G) * h⁻¹) := by
      rw [← hhe, hprodG]
      group
    rw [hd]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hz1 hz2) hz3
  refine hnot fun x hx => ?_
  rw [hα, Set.mem_singleton_iff] at hx
  rw [hx]
  exact huH

theorem false_of_alpha_eq_singleton (hC : HypothesisC D) {f n : ℕ} (hf : 2 ≤ f) (hn : 5 ≤ n)
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)
    (hQ : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥)
    (hnot : ¬ hC.alpha ⊆ (Halpha D hC.alpha : Set G)) (hα : hC.alpha = {hC.d}) : False := by
  obtain ⟨a, b₁, b₂, b₃, ha, hb₁, hb₂, hb₃, hT4, hne₁, hne₂, hne₃, hprodH⟩ :=
    exists_commuting_lifts hC hf hn e hQ
  exact false_of_commuting_lifts hC hnot hα ha hb₁ hb₂ hb₃ hT4 hne₁ hne₂ hne₃ hprodH

end CFSG.OddTranspositions.PartThree

end
