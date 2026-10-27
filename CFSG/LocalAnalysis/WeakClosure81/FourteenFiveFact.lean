module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveAxis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace FourteenFive

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

private theorem mem_zpowers_eq_one_or_self {v y : G} (h2 : v * v = 1)
    (hy : y ∈ Subgroup.zpowers v) : y = 1 ∨ y = v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hv2 : v ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
    exact h2
  rcases Int.even_or_odd' k with ⟨j, hk | hk⟩
  · left
    rw [hk, zpow_mul, hv2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, hv2, one_zpow, one_mul, zpow_one]

private theorem exists_mul_of_mem_sup_of_isMulCommutative {H K L : Subgroup G}
    [IsMulCommutative L] (hH : H ≤ L) (hK : K ≤ L) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ y ∈ H, ∃ z ∈ K, y * z = x := by
  have hxL : x ∈ L := (sup_le hH hK) hx
  have hx' : (⟨x, hxL⟩ : ↥L) ∈ H.subgroupOf L ⊔ K.subgroupOf L := by
    rw [← Subgroup.subgroupOf_sup hH hK]
    exact Subgroup.mem_subgroupOf.2 hx
  rw [Subgroup.mem_sup_of_normal_right] at hx'
  obtain ⟨y, hy, z, hz, hyz⟩ := hx'
  exact ⟨(y : G), Subgroup.mem_subgroupOf.1 hy, (z : G), Subgroup.mem_subgroupOf.1 hz,
    by simpa using congrArg Subtype.val hyz⟩

section Certified


theorem exists_mul_mem_normalizer_F (h15 : Hyp15 M V₀ V) (h : Hyp65 n M V₀ V g)
    (hV₀K : ¬ V₀ ≤ KOf M V g) (hn : (UOf M V g).relIndex V = 2)
    (hD : M ≤ normalizer ((Z0Of M V₀ g : Subgroup G) : Set G)) {v₂ : G} (hv₂ : v₂ ∈ V₀)
    (hv₂D : v₂ ∉ Z0Of M V₀ g) :
    ∀ m ∈ M, ∃ a ∈ F11.CTilde M V₀ V, (∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ Z0Of M V₀ g) ∧
      ∃ y ∈ M ⊓ normalizer ((NOf M V g ⊔ zpowers v₂ : Subgroup G) : Set G), m = a * y := by
  classical
  have hM : M ≤ Subgroup.normalizer (V : Set G) := by rw [h.normalizer_eq]
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := by rw [h.normalizer₀]
  haveI hVcomm : IsMulCommutative ↥V := h.elemAbelian.1
  have hV₂self : v₂ * v₂ = 1 := h.elemAbelian.mul_self_eq_one (h.le hv₂)
  have hrel : ((Z0Of M V₀ g).subgroupOf V₀).index = 2 := relIndex_Z0_eq_two h hV₀K hn
  have hU_inf_V₀ : UOf M V g ⊓ V₀ = Z0Of M V₀ g := by
    unfold UOf Z0Of
    rw [inf_assoc, inf_comm (conjSubgroup M g) V₀, ← inf_assoc, inf_eq_right.mpr h.le]
  have hv₂U : v₂ ∉ UOf M V g := by
    intro hvu
    exact hv₂D (by rw [← hU_inf_V₀]; exact ⟨hvu, hv₂⟩)
  obtain ⟨I, hIV, hV₀I, hIidx, haxis⟩ := exists_axis h15 h hV₀K hn
  have hNleV : NOf M V g ≤ V := inf_le_left.trans inf_le_left
  have hzv₂V₀ : Subgroup.zpowers v₂ ≤ V₀ := Subgroup.zpowers_le.2 hv₂
  have hV₂bot : Z0Of M V₀ g ⊓ Subgroup.zpowers v₂ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyD, hyz⟩ := Subgroup.mem_inf.1 hy
    rcases mem_zpowers_eq_one_or_self hV₂self hyz with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hyD) hv₂D
  have hV₁₂ : Z0Of M V₀ g ⊔ Subgroup.zpowers v₂ = V₀ := by
    apply le_antisymm
    · exact sup_le inf_le_left hzv₂V₀
    · intro y hyV₀
      by_cases hyD : y ∈ Z0Of M V₀ g
      · exact Subgroup.mem_sup_left hyD
      · have hv₂invD : v₂⁻¹ ∉ Z0Of M V₀ g :=
          fun hh => hv₂D ((Z0Of M V₀ g).inv_mem_iff.1 hh)
        have hmul : y * v₂⁻¹ ∈ Z0Of M V₀ g := by
          have h' := (Subgroup.mul_mem_iff_of_index_two (H := (Z0Of M V₀ g).subgroupOf V₀)
            hrel (a := (⟨y, hyV₀⟩ : V₀)) (b := (⟨v₂⁻¹, V₀.inv_mem hv₂⟩ : V₀))).2
            (iff_of_false hyD hv₂invD)
          simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using h'
        have hy_eq : y = (y * v₂⁻¹) * v₂ := by group
        rw [hy_eq]
        exact Subgroup.mul_mem_sup hmul (Subgroup.mem_zpowers v₂)
  have hF : NOf M V g ⊔ Subgroup.zpowers v₂ ∈
      FourteenTwo.FamV V₀ (Subgroup.zpowers v₂) V := by
    refine ⟨sup_le hNleV (hzv₂V₀.trans h.le), ?_, ?_⟩
    · rw [sup_assoc, sup_eq_right.mpr hzv₂V₀, sup_comm]
      exact (h.V_eq_V₀_sup_N hV₀K).symm
    · apply le_antisymm
      · intro x hx
        obtain ⟨hxF, hxV₀⟩ := Subgroup.mem_inf.1 hx
        obtain ⟨e, heE, b, hbB, heb⟩ :=
          exists_mul_of_mem_sup_of_isMulCommutative hNleV (hzv₂V₀.trans h.le) hxF
        have hbV₀ : b ∈ V₀ := hzv₂V₀ hbB
        have heV₀ : e ∈ V₀ := by
          have heq : e = x * b⁻¹ := by rw [← heb]; group
          rw [heq]
          exact V₀.mul_mem hxV₀ (V₀.inv_mem hbV₀)
        have he1 : e = 1 := by
          have hmem : e ∈ NOf M V g ⊓ V₀ := ⟨heE, heV₀⟩
          rw [inf_comm, h.V₀_inf_N] at hmem
          exact Subgroup.mem_bot.1 hmem
        rw [he1, one_mul] at heb
        rw [← heb]
        exact hbB
      · intro x hx
        exact Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_right hx, hzv₂V₀ hx⟩
  have hA_I : ∀ z ∈ Z0Of M V₀ g,
      ∃ a ∈ FourteenTwo.CFixQuot (FourteenTwo.PSub M V₀ V) (Z0Of M V₀ g) V,
        FourteenTwo.InducesTransvection V I z a := by
    intro z hz
    obtain ⟨a, haP, haT, haV⟩ := haxis z hz
    have haM : a ∈ M := cTilde_le_M M V₀ V (Subgroup.mem_inf.1 haP).1
    exact ⟨a, ⟨haP, hD haM, haV⟩, haT⟩
  have hprod := FourteenTwo.fourteen_two_product (M := M) (V₀ := V₀)
    (V₁ := Z0Of M V₀ g) (V₂ := Subgroup.zpowers v₂) (V := V)
    (A := FourteenTwo.CFixQuot (FourteenTwo.PSub M V₀ V) (Z0Of M V₀ g) V)
    (W := I) (F := NOf M V g ⊔ Subgroup.zpowers v₂)
    h.elemAbelian h.le inf_le_left hV₂bot hV₁₂ hM hM₀ hD
    (h15.h6.conjGenerated h15.ne_bot) (fun a ha => ha.1) (fun a ha v hv => ha.2.2 v hv)
    hIV hV₀I hIidx hA_I hF
  intro m hm
  set w : G := m * v₂ * m⁻¹ with hwdef
  set z : G := w * v₂⁻¹ with hzdef
  have hwV₀ : w ∈ V₀ := (Subgroup.mem_normalizer_iff.1 (hM₀ hm) v₂).1 hv₂
  have hwD : w ∉ Z0Of M V₀ g := by
    intro hw
    have h1 : v₂ ∈ conjSubgroup (Z0Of M V₀ g) m := by
      rw [mem_conjSubgroup_iff, ← hwdef]
      exact hw
    rw [conjSubgroup_eq_iff_mem_normalizer.2 (hD hm)] at h1
    exact hv₂D h1
  have hzD : z ∈ Z0Of M V₀ g := by
    have hv₂invD : v₂⁻¹ ∉ Z0Of M V₀ g :=
      fun hh => hv₂D ((Z0Of M V₀ g).inv_mem_iff.1 hh)
    have h' := (Subgroup.mul_mem_iff_of_index_two (H := (Z0Of M V₀ g).subgroupOf V₀) hrel
      (a := (⟨w, hwV₀⟩ : V₀)) (b := (⟨v₂⁻¹, V₀.inv_mem hv₂⟩ : V₀))).2
      (iff_of_false hwD hv₂invD)
    rw [hzdef]
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using h'
  have hzv₂ : z * v₂ = w := by rw [hzdef]; group
  obtain ⟨c, hcC, hcT⟩ := exists_transvection_Y h hV₀K hn hzD
  have hcM : c ∈ M := hcC.2
  have hcw : c * v₂ * c⁻¹ = w := by
    rw [hcT.2 v₂ (h.le hv₂) hv₂U, hzv₂]
  have hfix : (c⁻¹ * m) * v₂ * (c⁻¹ * m)⁻¹ = v₂ := by
    calc (c⁻¹ * m) * v₂ * (c⁻¹ * m)⁻¹ = c⁻¹ * (m * v₂ * m⁻¹) * c := by group
      _ = c⁻¹ * w * c := by rw [hwdef]
      _ = v₂ := by rw [← hcw]; group
  have hcomm : Commute (c⁻¹ * m) v₂ := by
    show (c⁻¹ * m) * v₂ = v₂ * (c⁻¹ * m)
    calc (c⁻¹ * m) * v₂ = ((c⁻¹ * m) * v₂ * (c⁻¹ * m)⁻¹) * (c⁻¹ * m) := by group
      _ = v₂ * (c⁻¹ * m) := by rw [hfix]
  have hnormV₂ : c⁻¹ * m ∈ Subgroup.normalizer (Subgroup.zpowers v₂ : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    exact (hcomm.zpow_right k).eq.symm
  have hmem_prod : c⁻¹ * m ∈ ((M ⊓ Subgroup.normalizer (Subgroup.zpowers v₂ : Set G)
      : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨M.mul_mem (M.inv_mem hcM) hm, hnormV₂⟩
  rw [hprod] at hmem_prod
  obtain ⟨p, hpA, yy, hyy, hpy⟩ := Set.mem_mul.1 hmem_prod
  obtain ⟨hpP, -, hpC⟩ := hpA
  refine ⟨c * p, (F11.CTilde M V₀ V).mul_mem (h.Y_le_cTilde hcC)
    (Subgroup.mem_inf.1 hpP).1, ⟨?_, yy, ?_, ?_⟩⟩
  · intro v hv
    have hpv : p * v * p⁻¹ * v⁻¹ ∈ Z0Of M V₀ g := hpC v hv
    have hcv : c * v * c⁻¹ * v⁻¹ ∈ Z0Of M V₀ g := by
      have h1 : ⁅c, v⁆ ∈ ⁅YOf M V₀ g, V⁆ := Subgroup.commutator_mem_commutator hcC hv
      have h2 := h.commutator_Y_V_le_Z0 h1
      simpa only [commutatorElement_def] using h2
    have hcpv : c * (p * v * p⁻¹ * v⁻¹) * c⁻¹ ∈ Z0Of M V₀ g :=
      (Subgroup.mem_normalizer_iff.1 (hD hcM) _).1 hpv
    have heq : (c * p) * v * (c * p)⁻¹ * v⁻¹ =
        (c * (p * v * p⁻¹ * v⁻¹) * c⁻¹) * (c * v * c⁻¹ * v⁻¹) := by group
    rw [heq]
    exact (Z0Of M V₀ g).mul_mem hcpv hcv
  · exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hyy).1.1, (Subgroup.mem_inf.1 hyy).2⟩
  · have hmul : m = (c * p) * yy := by
      rw [mul_assoc, hpy]
      group
    exact hmul

theorem exists_mem_normalizer_F_iff (h15 : Hyp15 M V₀ V) (h : Hyp65 n M V₀ V g)
    (hV₀K : ¬ V₀ ≤ KOf M V g) (hn : (UOf M V g).relIndex V = 2)
    (hD : M ≤ normalizer ((Z0Of M V₀ g : Subgroup G) : Set G)) {v₂ : G} (hv₂ : v₂ ∈ V₀)
    (hv₂D : v₂ ∉ Z0Of M V₀ g) {x : G} (hx : x ∈ F11.CTilde M V₀ V) :
    ∃ y ∈ F11.CTilde M V₀ V ⊓ normalizer ((NOf M V g ⊔ zpowers v₂ : Subgroup G) : Set G),
      ∀ v ∈ V, (y * v * y⁻¹ * v⁻¹ ∈ Z0Of M V₀ g ↔ x * v * x⁻¹ * v⁻¹ ∈ Z0Of M V₀ g) := by
  obtain ⟨a, haCT, haV, y, hy, hxy⟩ :=
    exists_mul_mem_normalizer_F h15 h hV₀K hn hD hv₂ hv₂D x (cTilde_le_M M V₀ V hx)
  have hy_eq : y = a⁻¹ * x := by rw [hxy]; group
  have hyCT : y ∈ F11.CTilde M V₀ V := by
    rw [hy_eq]
    exact (F11.CTilde M V₀ V).mul_mem ((F11.CTilde M V₀ V).inv_mem haCT) hx
  refine ⟨y, Subgroup.mem_inf.2 ⟨hyCT, (Subgroup.mem_inf.1 hy).2⟩, ?_⟩
  have haD : a ∈ Subgroup.normalizer (Z0Of M V₀ g : Set G) :=
    hD (cTilde_le_M M V₀ V haCT)
  have hconjD : ∀ w : G, a⁻¹ * w * a ∈ Z0Of M V₀ g ↔ w ∈ Z0Of M V₀ g := by
    intro w
    have h' := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ haD) w
    rw [inv_inv] at h'
    exact h'.symm
  intro v hv
  have hvaD : a⁻¹ * v * a * v⁻¹ ∈ Z0Of M V₀ g := by
    have h1 : a * (a⁻¹ * v * a * v⁻¹) * a⁻¹ = (a * v * a⁻¹ * v⁻¹)⁻¹ := by group
    have hmem : a * (a⁻¹ * v * a * v⁻¹) * a⁻¹ ∈ Z0Of M V₀ g := by
      rw [h1]
      exact (Z0Of M V₀ g).inv_mem (haV v hv)
    have h' := mem_conjSubgroup_iff.2 hmem
    rwa [conjSubgroup_eq_iff_mem_normalizer.2 haD] at h'
  have heq : y * v * y⁻¹ * v⁻¹ =
      (a⁻¹ * (x * v * x⁻¹ * v⁻¹) * a) * (a⁻¹ * v * a * v⁻¹) := by
    rw [hy_eq]
    group
  rw [heq]
  constructor
  · intro hh
    have h1 : a⁻¹ * (x * v * x⁻¹ * v⁻¹) * a ∈ Z0Of M V₀ g := by
      have h2 : a⁻¹ * (x * v * x⁻¹ * v⁻¹) * a =
          ((a⁻¹ * (x * v * x⁻¹ * v⁻¹) * a) * (a⁻¹ * v * a * v⁻¹)) *
            (a⁻¹ * v * a * v⁻¹)⁻¹ := by group
      rw [h2]
      exact (Z0Of M V₀ g).mul_mem hh ((Z0Of M V₀ g).inv_mem hvaD)
    exact (hconjD (x * v * x⁻¹ * v⁻¹)).1 h1
  · intro hh
    exact (Z0Of M V₀ g).mul_mem ((hconjD (x * v * x⁻¹ * v⁻¹)).2 hh) hvaD

end Certified

end FourteenFive

end CFSG.LocalAnalysis.WeakClosure81
