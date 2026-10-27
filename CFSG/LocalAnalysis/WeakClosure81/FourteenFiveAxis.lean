module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveTrans

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace FourteenFive

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

private theorem mul_mem_axis {U U' V : Subgroup G}
    (hU : (U.subgroupOf V).index = 2) (hU' : (U'.subgroupOf V).index = 2)
    {v w : G} (hvV : v ∈ V) (hwV : w ∈ V)
    (hv : v ∈ U ↔ v ∈ U') (hw : w ∈ U ↔ w ∈ U') :
    v * w ∈ U ↔ v * w ∈ U' := by
  have h1 : v * w ∈ U ↔ (v ∈ U ↔ w ∈ U) := by
    have := Subgroup.mul_mem_iff_of_index_two hU (a := (⟨v, hvV⟩ : V)) (b := (⟨w, hwV⟩ : V))
    simpa [Subgroup.mem_subgroupOf] using this
  have h2 : v * w ∈ U' ↔ (v ∈ U' ↔ w ∈ U') := by
    have := Subgroup.mul_mem_iff_of_index_two hU' (a := (⟨v, hvV⟩ : V)) (b := (⟨w, hwV⟩ : V))
    simpa [Subgroup.mem_subgroupOf] using this
  rw [h1, h2]
  tauto

private theorem iff_not_of_not_iff {p q : Prop} (h : ¬ (p ↔ q)) : p ↔ ¬ q := by
  classical
  rw [not_iff] at h
  exact ⟨fun hp hq => (h.mpr hq) hp, fun hq => by_contra fun hp => hq (h.mp hp)⟩

private def axisCarrier (U U' V : Subgroup G) : Set G :=
  {v | v ∈ V ∧ (v ∈ U ↔ v ∈ U')}

private def axisSubgroup (U U' V : Subgroup G)
    (hU : (U.subgroupOf V).index = 2) (hU' : (U'.subgroupOf V).index = 2) : Subgroup G where
  carrier := axisCarrier U U' V
  one_mem' := by
    refine ⟨V.one_mem, ?_⟩
    simp
  mul_mem' := by
    rintro v w ⟨hvV, hv⟩ ⟨hwV, hw⟩
    exact ⟨V.mul_mem hvV hwV, mul_mem_axis hU hU' hvV hwV hv hw⟩
  inv_mem' := by
    rintro v ⟨hvV, hv⟩
    refine ⟨V.inv_mem hvV, ?_⟩
    exact ((Subgroup.inv_mem_iff (H := U)).trans hv).trans
      (Subgroup.inv_mem_iff (H := U')).symm

private theorem mul_mem_of_notMem_of_notMem {W H : Subgroup G}
    (hWH : H.relIndex W = 2) {a b : G} (haW : a ∈ W) (hbW : b ∈ W)
    (haH : a ∉ H) (hbH : b ∉ H) : a * b ∈ H := by
  have h := Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf W)
    (show (H.subgroupOf W).index = 2 from hWH)
    (a := (⟨a, haW⟩ : W)) (b := (⟨b, hbW⟩ : W))
  have h' : (⟨a, haW⟩ : W) * ⟨b, hbW⟩ ∈ H.subgroupOf W := by
    rw [h]
    exact iff_of_false haH hbH
  simpa [Subgroup.mem_subgroupOf] using h'

private theorem conj_eq_of_mem_centralizer {W : Subgroup G} {x w : G}
    (hx : x ∈ Subgroup.centralizer (W : Set G)) (hw : w ∈ W) : x * w * x⁻¹ = w := by
  have h := Subgroup.mem_centralizer_iff.1 hx w hw
  calc x * w * x⁻¹ = w * x * x⁻¹ := by rw [← h]
    _ = w := by group

private theorem UOf_inf_V₀ (h : Hyp65 n M V₀ V g) :
    UOf M V g ⊓ V₀ = Z0Of M V₀ g := by
  unfold UOf Z0Of
  rw [inf_assoc, inf_comm (conjSubgroup M g) V₀, ← inf_assoc, inf_eq_right.mpr h.le]

private theorem conjUOf_inf_V₀ (h : Hyp65 n M V₀ V g) {k : G}
    (hk₀ : conjSubgroup V₀ k = V₀) :
    conjSubgroup (UOf M V g) k ⊓ V₀ = conjSubgroup (Z0Of M V₀ g) k := by
  rw [← UOf_inf_V₀ h, E3.conjSubgroup_inf, hk₀]

private theorem inducesTransvection_conj {V U : Subgroup G} {z z' c x : G}
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) (hz' : x⁻¹ * z * x = z')
    (hc : FourteenTwo.InducesTransvection V U z c) :
    FourteenTwo.InducesTransvection V (conjSubgroup U x) z' (x⁻¹ * c * x) := by
  constructor
  · intro w hw
    have hxwx : x * w * x⁻¹ ∈ U := mem_conjSubgroup_iff.1 hw
    have h1 : c * (x * w * x⁻¹) * c⁻¹ = x * w * x⁻¹ := hc.1 _ hxwx
    calc x⁻¹ * c * x * w * (x⁻¹ * c * x)⁻¹
        = x⁻¹ * (c * (x * w * x⁻¹) * c⁻¹) * x := by group
      _ = x⁻¹ * (x * w * x⁻¹) * x := by rw [h1]
      _ = w := by group
  · intro v hvV hvNot
    have hxv : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hxN v).1 hvV
    have hxvNot : x * v * x⁻¹ ∉ U := fun h => hvNot (mem_conjSubgroup_iff.2 h)
    have h1 : c * (x * v * x⁻¹) * c⁻¹ = z * (x * v * x⁻¹) := hc.2 _ hxv hxvNot
    calc x⁻¹ * c * x * v * (x⁻¹ * c * x)⁻¹
        = x⁻¹ * (c * (x * v * x⁻¹) * c⁻¹) * x := by group
      _ = x⁻¹ * (z * (x * v * x⁻¹)) * x := by rw [h1]
      _ = z' * v := by
            rw [show x⁻¹ * (z * (x * v * x⁻¹)) * x = (x⁻¹ * z * x) * v by group, hz']

private theorem inducesTransvection_mul {V U U' I : Subgroup G} {z c c' : G}
    (hIV : I ≤ V) (hI : ∀ v ∈ V, v ∈ I ↔ (v ∈ U ↔ v ∈ U'))
    (hc : FourteenTwo.InducesTransvection V U z c)
    (hc' : FourteenTwo.InducesTransvection V U' z c')
    (hzU : z ∈ U) (hzU' : z ∈ U') (hz2 : z * z = 1) :
    FourteenTwo.InducesTransvection V I z (c * c') := by
  constructor
  · intro w hw
    have hwV : w ∈ V := hIV hw
    have hwUU : w ∈ U ↔ w ∈ U' := (hI w hwV).1 hw
    by_cases hU : w ∈ U
    · have hU' : w ∈ U' := hwUU.mp hU
      calc c * c' * w * (c * c')⁻¹ = c * (c' * w * c'⁻¹) * c⁻¹ := by group
        _ = c * w * c⁻¹ := by rw [hc'.1 w hU']
        _ = w := hc.1 w hU
    · have hU' : w ∉ U' := fun h => hU (hwUU.mpr h)
      calc c * c' * w * (c * c')⁻¹ = c * (c' * w * c'⁻¹) * c⁻¹ := by group
        _ = c * (z * w) * c⁻¹ := by rw [hc'.2 w hwV hU']
        _ = z * (z * w) := by
              rw [show c * (z * w) * c⁻¹ = (c * z * c⁻¹) * (c * w * c⁻¹) by group,
                hc.1 z hzU, hc.2 w hwV hU]
        _ = w := by rw [← mul_assoc, hz2, one_mul]
  · intro v hvV hvNot
    have hvUU : ¬ (v ∈ U ↔ v ∈ U') := fun h => hvNot ((hI v hvV).2 h)
    by_cases hU : v ∈ U
    · have hU' : v ∉ U' := fun h => hvUU ⟨fun _ => h, fun _ => hU⟩
      calc c * c' * v * (c * c')⁻¹ = c * (c' * v * c'⁻¹) * c⁻¹ := by group
        _ = c * (z * v) * c⁻¹ := by rw [hc'.2 v hvV hU']
        _ = z * (c * v * c⁻¹) := by
              rw [show c * (z * v) * c⁻¹ = (c * z * c⁻¹) * (c * v * c⁻¹) by group,
                hc.1 z hzU]
        _ = z * v := by rw [hc.1 v hU]
    · by_cases hU' : v ∈ U'
      · calc c * c' * v * (c * c')⁻¹ = c * (c' * v * c'⁻¹) * c⁻¹ := by group
          _ = c * v * c⁻¹ := by rw [hc'.1 v hU']
          _ = z * v := hc.2 v hvV hU
      · exact absurd ((hI v hvV).2 ⟨fun h => absurd h hU, fun h => absurd h hU'⟩) hvNot

section Certified


theorem exists_axis (h15 : Hyp15 M V₀ V) (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g)
    (hn : (UOf M V g).relIndex V = 2) :
    ∃ I : Subgroup G, I ≤ V ∧ V₀ ≤ I ∧ I.relIndex V = 2 ∧
      ∀ z ∈ Z0Of M V₀ g, ∃ a ∈ FourteenTwo.PSub M V₀ V,
        FourteenTwo.InducesTransvection V I z a ∧
          ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ Z0Of M V₀ g := by
  classical
  obtain ⟨x, hxM, hxUne⟩ := exists_mem_centralizer_conj_ne h15 h hV₀K hn
  have hxMem : x ∈ M := hxM.1
  have hxC : x ∈ Subgroup.centralizer (V₀ : Set G) := hxM.2
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := by
    rw [h.normalizer_eq]; exact hxMem
  have hxV₀ : ∀ w ∈ V₀, x * w * x⁻¹ = w := fun w hw => conj_eq_of_mem_centralizer hxC hw
  have hUidx : ((UOf M V g).subgroupOf V).index = 2 := by
    show (UOf M V g).relIndex V = 2
    exact hn
  have hU'V : conjSubgroup (UOf M V g) x ≤ V := by
    have h1 : conjSubgroup (UOf M V g) x ≤ conjSubgroup V x :=
      conjSubgroup_mono inf_le_left x
    rwa [conjSubgroup_eq_iff_mem_normalizer.2 hxN] at h1
  have hU'idx : ((conjSubgroup (UOf M V g) x).subgroupOf V).index = 2 := by
    have h1 := E3.relIndex_conjSubgroup (UOf M V g) V x
    rw [conjSubgroup_eq_iff_mem_normalizer.2 hxN] at h1
    show (conjSubgroup (UOf M V g) x).relIndex V = 2
    rw [h1, hn]
  have hdiff : ∃ v ∈ V, ¬ (v ∈ UOf M V g ↔ v ∈ conjSubgroup (UOf M V g) x) := by
    by_cases hle : UOf M V g ≤ conjSubgroup (UOf M V g) x
    · have hnotle : ¬ conjSubgroup (UOf M V g) x ≤ UOf M V g :=
        fun hle' => hxUne (le_antisymm hle' hle)
      obtain ⟨v, hvU', hvU⟩ := SetLike.not_le_iff_exists.1 hnotle
      exact ⟨v, hU'V hvU', fun h => hvU (h.mpr hvU')⟩
    · obtain ⟨v, hvU, hvU'⟩ := SetLike.not_le_iff_exists.1 hle
      exact ⟨v, (Subgroup.mem_inf.1 hvU).1, fun h => hvU' (h.mp hvU)⟩
  obtain ⟨v₀, hv₀V, hv₀diff⟩ := hdiff
  let I : Subgroup G :=
    axisSubgroup (UOf M V g) (conjSubgroup (UOf M V g) x) V hUidx hU'idx
  have hIV : I ≤ V := fun v hv => hv.1
  have hImem : ∀ v ∈ V, v ∈ I ↔ (v ∈ UOf M V g ↔ v ∈ conjSubgroup (UOf M V g) x) :=
    fun v hv => ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  have hV₀I : V₀ ≤ I := by
    intro w hw
    refine ⟨h.le hw, ?_⟩
    rw [mem_conjSubgroup_iff, hxV₀ w hw]
  have hIidx : I.relIndex V = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨v₀, hv₀V, fun hI => hv₀diff ((hImem v₀ hv₀V).1 hI), ?_⟩
    intro b hbV
    by_cases hbI : b ∈ I
    · exact Or.inr hbI
    · refine Or.inl ((hImem (b * v₀) (V.mul_mem hbV hv₀V)).2 ?_)
      have hbUU : ¬ (b ∈ UOf M V g ↔ b ∈ conjSubgroup (UOf M V g) x) :=
        fun hcontra => hbI ((hImem b hbV).2 hcontra)
      have hcoe : (↑((⟨b, hbV⟩ : V) * (⟨v₀, hv₀V⟩ : V)) : G) = b * v₀ := by
        rw [Subgroup.coe_mul]
      have h1 : (↑((⟨b, hbV⟩ : V) * (⟨v₀, hv₀V⟩ : V)) : G) ∈ UOf M V g ↔
          (b ∈ UOf M V g ↔ v₀ ∈ UOf M V g) := by
        have h := Subgroup.mul_mem_iff_of_index_two hUidx
          (a := (⟨b, hbV⟩ : V)) (b := (⟨v₀, hv₀V⟩ : V))
        rw [Subgroup.mem_subgroupOf] at h
        exact h
      have h2 : (↑((⟨b, hbV⟩ : V) * (⟨v₀, hv₀V⟩ : V)) : G) ∈
          conjSubgroup (UOf M V g) x ↔
          (b ∈ conjSubgroup (UOf M V g) x ↔ v₀ ∈ conjSubgroup (UOf M V g) x) := by
        have h := Subgroup.mul_mem_iff_of_index_two hU'idx
          (a := (⟨b, hbV⟩ : V)) (b := (⟨v₀, hv₀V⟩ : V))
        rw [Subgroup.mem_subgroupOf] at h
        exact h
      rw [← hcoe, h1, h2]
      rw [iff_not_of_not_iff hbUU, iff_not_of_not_iff hv₀diff]
      exact not_iff_not
  refine ⟨I, hIV, hV₀I, hIidx, ?_⟩
  intro z hz
  obtain ⟨c, hcC, hcT⟩ := exists_transvection_Y h hV₀K hn hz
  let c' : G := x⁻¹ * c * x
  let a : G := c * c'
  have hzx : x⁻¹ * z * x = z := by
    calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
      _ = x⁻¹ * (x * z) := by rw [Subgroup.mem_centralizer_iff.1 hxC z hz.1]
      _ = z := by group
  have hc'T : FourteenTwo.InducesTransvection V (conjSubgroup (UOf M V g) x) z c' :=
    inducesTransvection_conj hxN hzx hcT
  have hzU : z ∈ UOf M V g := h.Z0_le_U hz
  have hzU' : z ∈ conjSubgroup (UOf M V g) x := by
    rw [mem_conjSubgroup_iff, conj_eq_of_mem_centralizer hxC hz.1]
    exact hzU
  have hz2 : z * z = 1 := h.elemAbelian.mul_self_eq_one (h.le hz.1)
  have hT : FourteenTwo.InducesTransvection V I z a :=
    inducesTransvection_mul hIV hImem hcT hc'T hzU hzU' hz2
  have hcCT : c ∈ F11.CTilde M V₀ V := h.Y_le_cTilde hcC
  have hcM : c ∈ M := hcC.2
  have hCTnormal : ((F11.CTilde M V₀ V).subgroupOf M).Normal :=
    cTilde_subgroupOf_normal h.elemAbelian h.normalizer_eq.symm.le h.normalizer₀.symm.le
  have hCTnorm : M ≤ Subgroup.normalizer (F11.CTilde M V₀ V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M M V₀ V)).mp hCTnormal
  have hc'CT : c' ∈ F11.CTilde M V₀ V := by
    show x⁻¹ * c * x ∈ F11.CTilde M V₀ V
    have hconj : conjSubgroup (F11.CTilde M V₀ V) x = F11.CTilde M V₀ V :=
      conjSubgroup_eq_iff_mem_normalizer.2 (hCTnorm hxMem)
    have hmem : x⁻¹ * c * x ∈ conjSubgroup (F11.CTilde M V₀ V) x := by
      rw [mem_conjSubgroup_iff]
      have h : x * (x⁻¹ * c * x) * x⁻¹ = c := by group
      rw [h]
      exact hcCT
    rwa [hconj] at hmem
  refine ⟨a, ?_, hT, ?_⟩
  · show a ∈ F11.CTilde M V₀ V ⊓ (M ⊓ Subgroup.centralizer (V₀ : Set G))
    refine ⟨(F11.CTilde M V₀ V).mul_mem hcCT hc'CT, ?_, ?_⟩
    · exact M.mul_mem hcM (M.mul_mem (M.mul_mem (M.inv_mem hxMem) hcM) hxMem)
    · refine Subgroup.mem_centralizer_iff.2 ?_
      intro w hw
      have h1 : a * w * a⁻¹ = w := hT.1 w (hV₀I hw)
      calc w * a = (a * w * a⁻¹) * a := by rw [h1]
        _ = a * w := by group
  · intro v hvV
    by_cases hvI : v ∈ I
    · have h1 : a * v * a⁻¹ = v := hT.1 v hvI
      rw [h1]
      simpa using (Z0Of M V₀ g).one_mem
    · have h1 : a * v * a⁻¹ = z * v := hT.2 v hvV hvI
      rw [h1]
      have h2 : z * v * v⁻¹ = z := by group
      rw [h2]
      exact hz

theorem exists_cTilde_conj_eq (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g)
    (hn : (UOf M V g).relIndex V = 2) {k : G} (hk : k ∈ M)
    (hkD : conjSubgroup (Z0Of M V₀ g) k ≠ Z0Of M V₀ g) :
    ∃ x ∈ F11.CTilde M V₀ V, conjSubgroup (Z0Of M V₀ g) x = conjSubgroup (Z0Of M V₀ g) k := by
  classical
  let D := Z0Of M V₀ g
  let U := UOf M V g
  let D' := conjSubgroup D k
  have hk₀ : k ∈ Subgroup.normalizer (V₀ : Set G) := by rw [h.normalizer₀]; exact hk
  have hk₀conj : conjSubgroup V₀ k = V₀ := conjSubgroup_eq_iff_mem_normalizer.2 hk₀
  have hrel : D.relIndex V₀ = 2 := relIndex_Z0_eq_two h hV₀K hn
  have hrel' : D'.relIndex V₀ = 2 := by
    have h1 := E3.relIndex_conjSubgroup D V₀ k
    rw [hk₀conj, hrel] at h1
    exact h1
  have hD'le : D' ≤ V₀ := by
    intro y hy
    have h1 : y ∈ conjSubgroup V₀ k := conjSubgroup_mono inf_le_left k hy
    rwa [hk₀conj] at h1
  have hnotle : ¬ D ≤ D' := by
    intro hle
    have hcard : Nat.card D' ≤ Nat.card D := le_of_eq (E3.card_conjSubgroup D k)
    exact hkD (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  obtain ⟨v₁, hv₁D, hv₁D'⟩ := SetLike.not_le_iff_exists.1 hnotle
  have hnotle' : ¬ D' ≤ D := by
    intro hle
    have hcard : Nat.card D ≤ Nat.card D' := le_of_eq (E3.card_conjSubgroup D k).symm
    exact hkD (Subgroup.eq_of_le_of_card_ge hle hcard)
  obtain ⟨v₂, hv₂D', hv₂D⟩ := SetLike.not_le_iff_exists.1 hnotle'
  have hv₁V₀ : v₁ ∈ V₀ := (Subgroup.mem_inf.1 hv₁D).1
  have hv₂V₀ : v₂ ∈ V₀ := hD'le hv₂D'
  have hkv₂D : k * v₂ * k⁻¹ ∈ D := mem_conjSubgroup_iff.1 hv₂D'
  obtain ⟨c, hcC, hcT⟩ := exists_transvection_Y h hV₀K hn hv₁D
  obtain ⟨c'', hc''C, hc''T⟩ := exists_transvection_Y h hV₀K hn hkv₂D
  let c' : G := k⁻¹ * c'' * k
  let x : G := c' * c
  have hkN : k ∈ Subgroup.normalizer (V : Set G) := by rw [h.normalizer_eq]; exact hk
  have hc'T : FourteenTwo.InducesTransvection V (conjSubgroup U k) v₂ c' :=
    inducesTransvection_conj hkN (by show k⁻¹ * (k * v₂ * k⁻¹) * k = v₂; group) hc''T
  have hcCT : c ∈ F11.CTilde M V₀ V := h.Y_le_cTilde hcC
  have hc''CT : c'' ∈ F11.CTilde M V₀ V := h.Y_le_cTilde hc''C
  have hCTnormal : ((F11.CTilde M V₀ V).subgroupOf M).Normal :=
    cTilde_subgroupOf_normal h.elemAbelian h.normalizer_eq.symm.le h.normalizer₀.symm.le
  have hCTnorm : M ≤ Subgroup.normalizer (F11.CTilde M V₀ V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M M V₀ V)).mp hCTnormal
  have hc'CT : c' ∈ F11.CTilde M V₀ V := by
    show k⁻¹ * c'' * k ∈ F11.CTilde M V₀ V
    have hconj : conjSubgroup (F11.CTilde M V₀ V) k = F11.CTilde M V₀ V :=
      conjSubgroup_eq_iff_mem_normalizer.2 (hCTnorm hk)
    have hmem : k⁻¹ * c'' * k ∈ conjSubgroup (F11.CTilde M V₀ V) k := by
      rw [mem_conjSubgroup_iff]
      have h : k * (k⁻¹ * c'' * k) * k⁻¹ = c'' := by group
      rw [h]
      exact hc''CT
    rwa [hconj] at hmem
  have hxCT : x ∈ F11.CTilde M V₀ V := (F11.CTilde M V₀ V).mul_mem hc'CT hcCT
  have hkey : ∀ y ∈ D', x * y * x⁻¹ ∈ D := by
    intro y hyD'
    have hyV₀ : y ∈ V₀ := hD'le hyD'
    have hyV : y ∈ V := h.le hyV₀
    by_cases hyD : y ∈ D
    · have hyU : y ∈ U := h.Z0_le_U hyD
      have hyUk : y ∈ conjSubgroup U k := conjSubgroup_mono h.Z0_le_U k hyD'
      have h1 : c * y * c⁻¹ = y := hcT.1 y hyU
      have h2 : c' * y * c'⁻¹ = y := hc'T.1 y hyUk
      have heq : x * y * x⁻¹ = y := by
        calc x * y * x⁻¹ = c' * (c * y * c⁻¹) * c'⁻¹ := by
              show (c' * c) * y * (c' * c)⁻¹ = c' * (c * y * c⁻¹) * c'⁻¹; group
          _ = c' * y * c'⁻¹ := by rw [h1]
          _ = y := h2
      rw [heq]
      exact hyD
    · have hyU : y ∉ U := by
        intro hyU
        exact hyD (by
          have hmem : y ∈ U ⊓ V₀ := ⟨hyU, hyV₀⟩
          rwa [UOf_inf_V₀ h] at hmem)
      have h1 : c * y * c⁻¹ = v₁ * y := hcT.2 y hyV hyU
      have hvyD' : v₁ * y ∉ D' := by
        intro hvy
        have hv₁mem : v₁ ∈ D' := by
          have heq : v₁ = (v₁ * y) * y⁻¹ := by group
          rw [heq]
          exact D'.mul_mem hvy (D'.inv_mem hyD')
        exact hv₁D' hv₁mem
      have hvyUk : v₁ * y ∉ conjSubgroup U k := by
        intro hvy
        have hmem : v₁ * y ∈ conjSubgroup U k ⊓ V₀ :=
          ⟨hvy, V₀.mul_mem hv₁V₀ hyV₀⟩
        rw [conjUOf_inf_V₀ h hk₀conj] at hmem
        exact hvyD' hmem
      have hvyV : v₁ * y ∈ V := h.le (V₀.mul_mem hv₁V₀ hyV₀)
      have h2 : c' * (v₁ * y) * c'⁻¹ = v₂ * (v₁ * y) := hc'T.2 (v₁ * y) hvyV hvyUk
      have hvyD : v₂ * y ∈ D :=
        mul_mem_of_notMem_of_notMem hrel hv₂V₀ hyV₀ hv₂D hyD
      have hcomm₁ : v₁ * y = y * v₁ := h.elemAbelian.comm (h.le hv₁V₀) (h.le hyV₀)
      have heq : x * y * x⁻¹ = v₂ * (v₁ * y) := by
        calc x * y * x⁻¹ = c' * (c * y * c⁻¹) * c'⁻¹ := by
              show (c' * c) * y * (c' * c)⁻¹ = c' * (c * y * c⁻¹) * c'⁻¹; group
          _ = c' * (v₁ * y) * c'⁻¹ := by rw [h1]
          _ = v₂ * (v₁ * y) := h2
      rw [heq, hcomm₁, ← mul_assoc]
      exact D.mul_mem hvyD hv₁D
  have hxD'x : conjSubgroup D' x⁻¹ ≤ D := by
    intro z hz
    have hzy : x⁻¹ * z * x ∈ D' := by
      have h := mem_conjSubgroup_iff.1 hz
      simpa using h
    have hzeq : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
    have hmem := hkey (x⁻¹ * z * x) hzy
    rwa [hzeq] at hmem
  have hcardD' : Nat.card (conjSubgroup D' x⁻¹) = Nat.card D := by
    rw [E3.card_conjSubgroup D' x⁻¹, E3.card_conjSubgroup D k]
  have hEq : conjSubgroup D' x⁻¹ = D :=
    Subgroup.eq_of_le_of_card_ge hxD'x hcardD'.ge
  have hxDx : conjSubgroup D x = conjSubgroup D k := by
    have h1 : conjSubgroup (conjSubgroup D' x⁻¹) x = D' := by
      rw [conjSubgroup_conjSubgroup D' x⁻¹ x, inv_mul_cancel, conjSubgroup_one]
    rw [hEq] at h1
    exact h1
  exact ⟨x, hxCT, hxDx⟩

end Certified

end FourteenFive

end CFSG.LocalAnalysis.WeakClosure81
