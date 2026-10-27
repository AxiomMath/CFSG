module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveFact
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveDual
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveComp
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace FourteenFive

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem commutator_mem_Z0 (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g)
    (hn : (UOf M V g).relIndex V = 2)
    (hD : M ≤ normalizer ((Z0Of M V₀ g : Subgroup G) : Set G)) {x : G} (hx : x ∈ M) {v : G}
    (hv : v ∈ V₀) : x * v * x⁻¹ * v⁻¹ ∈ Z0Of M V₀ g := by
  let D : Subgroup G := Z0Of M V₀ g
  have hrel : (D.subgroupOf V₀).index = 2 := relIndex_Z0_eq_two h hV₀K hn
  have hxN₀ : x ∈ Subgroup.normalizer (V₀ : Set G) := by rw [h.normalizer₀]; exact hx
  have hxvV₀ : x * v * x⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hxN₀ v).1 hv
  have hxD : x ∈ Subgroup.normalizer (D : Set G) := hD hx
  by_cases hvD : v ∈ D
  · exact D.mul_mem ((Subgroup.mem_normalizer_iff.1 hxD v).1 hvD) (D.inv_mem hvD)
  · have hconj_back : x * v * x⁻¹ ∈ D → v ∈ D := by
      intro hw
      have hxinv : x⁻¹ ∈ Subgroup.normalizer (D : Set G) := Subgroup.inv_mem _ hxD
      have h := (Subgroup.mem_normalizer_iff.1 hxinv (x * v * x⁻¹)).1 hw
      rwa [show x⁻¹ * (x * v * x⁻¹) * (x⁻¹)⁻¹ = v by group] at h
    have hxvD : x * v * x⁻¹ ∉ D := fun hw => hvD (hconj_back hw)
    have hmem := (Subgroup.mul_mem_iff_of_index_two hrel
      (a := (⟨x * v * x⁻¹, hxvV₀⟩ : V₀)) (b := (⟨v⁻¹, V₀.inv_mem hv⟩ : V₀))).2
      (iff_of_false (fun hh => hxvD (Subgroup.mem_subgroupOf.1 hh))
        (fun hh => hvD (D.inv_mem_iff.1 (Subgroup.mem_subgroupOf.1 hh))))
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subtype.coe_mk] using hmem

theorem mem_V₀_of_forall_commutator_mem (h15 : Hyp15 M V₀ V) (h : Hyp65 n M V₀ V g)
    (hD : M ≤ normalizer ((Z0Of M V₀ g : Subgroup G) : Set G))
    (hnot : ¬ ⁅F11.CTilde M V₀ V, V⁆ ≤ Z0Of M V₀ g) {v : G} (hv : v ∈ V)
    (hvD : ∀ x ∈ F11.CTilde M V₀ V, x * v * x⁻¹ * v⁻¹ ∈ Z0Of M V₀ g) : v ∈ V₀ := by
  classical
  let D : Subgroup G := Z0Of M V₀ g
  let C : Subgroup G := F11.CTilde M V₀ V
  let W : Subgroup G :=
    { carrier := {w | w ∈ V ∧ ∀ x ∈ C, x * w * x⁻¹ * w⁻¹ ∈ D}
      one_mem' := ⟨V.one_mem, fun x _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haV, ha⟩ ⟨hbV, hb⟩
        refine ⟨V.mul_mem haV hbV, fun x hxC => ?_⟩
        have haxbV : ⁅x, b⁆ ∈ V := h.le (by
          have hbV₀ : x * b * x⁻¹ * b⁻¹ ∈ V₀ :=
            (show x * b * x⁻¹ * b⁻¹ ∈ V₀ ⊓ conjSubgroup M g from hb x hxC).1
          simpa only [commutatorElement_def] using hbV₀)
        have heq : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
            (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹) := by
          rw [← commutatorElement_def x (a * b), ← commutatorElement_def x a,
            ← commutatorElement_def x b, commutatorElement_mul_right_eq_mul_conj]
          have hcomm : a * ⁅x, b⁆ = ⁅x, b⁆ * a := h.elemAbelian.comm haV haxbV
          have h2 : a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ := by
            rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
          rw [show ⁅x, a⁆ * a * ⁅x, b⁆ * a⁻¹ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) by group,
            h2]
        rw [heq]
        exact D.mul_mem (ha x hxC) (hb x hxC)
      inv_mem' := by
        rintro a ⟨haV, ha⟩
        refine ⟨V.inv_mem haV, fun x hxC => ?_⟩
        have hsq : a * a = 1 := h.elemAbelian.mul_self_eq_one haV
        have haa : a⁻¹ = a := inv_eq_of_mul_eq_one_right hsq
        simpa [haa] using ha x hxC }
  have hWV : W ≤ V := fun w hw => hw.1
  have hWN : ∀ y ∈ M, ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    intro y hy w hw
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := by rw [h.normalizer_eq]; exact hy
    have hyC : y ∈ Subgroup.normalizer (F11.CTilde M V₀ V : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M M V₀ V)).1
        (cTilde_subgroupOf_normal h.elemAbelian h.normalizer_eq.symm.le h.normalizer₀.symm.le) hy
    have hyD : y ∈ Subgroup.normalizer (D : Set G) := hD hy
    refine ⟨(Subgroup.mem_normalizer_iff.1 hyN w).1 hw.1, fun x hxC => ?_⟩
    have hx' : y⁻¹ * x * y ∈ C := (Subgroup.mem_normalizer_iff''.1 hyC x).1 hxC
    have hinner : (y⁻¹ * x * y) * w * (y⁻¹ * x * y)⁻¹ * w⁻¹ ∈ D := hw.2 _ hx'
    have heq : x * (y * w * y⁻¹) * x⁻¹ * (y * w * y⁻¹)⁻¹ =
        y * ((y⁻¹ * x * y) * w * (y⁻¹ * x * y)⁻¹ * w⁻¹) * y⁻¹ := by group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.1 hyD _).1 hinner
  have hMW : M ≤ Subgroup.normalizer (W : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact hWN m hm w hw
    · intro hw
      have h1 := hWN m⁻¹ (M.inv_mem hm) (m * w * m⁻¹) hw
      have h2 : m⁻¹ * (m * w * m⁻¹) * (m⁻¹)⁻¹ = w := by group
      rwa [h2] at h1
  have hWV₀ : W ≤ V₀ := by
    by_contra hnotW
    have hWV_eq : W = V :=
      eq_of_normalizer_of_not_le_of_conjGenerated (h15.h6.conjGenerated h15.ne_bot) hWV hMW hnotW
    have hcomm_le : ⁅C, V⁆ ≤ D := by
      rw [Subgroup.commutator_le]
      intro x hxC v hv
      have hvW : v ∈ W := hWV_eq ▸ hv
      simpa only [commutatorElement_def] using hvW.2 x hxC
    exact hnot hcomm_le
  exact hWV₀ ⟨hv, hvD⟩

section Certified


theorem exists_cTilde_mul_mem_normalizer_N (h15 : Hyp15 M V₀ V) (h : Hyp65 n M V₀ V g)
    (hV₀K : ¬ V₀ ≤ KOf M V g) (hn : (UOf M V g).relIndex V = 2)
    (hD : M ≤ normalizer ((Z0Of M V₀ g : Subgroup G) : Set G))
    (hnot : ¬ ⁅F11.CTilde M V₀ V, V⁆ ≤ Z0Of M V₀ g) {v₂ : G} (hv₂ : v₂ ∈ V₀)
    (hv₂D : v₂ ∉ Z0Of M V₀ g) {k : G}
    (hk : k ∈ M ⊓ normalizer ((NOf M V g ⊔ zpowers v₂ : Subgroup G) : Set G)) :
    ∃ y ∈ F11.CTilde M V₀ V, ∃ e ∈ M ⊓ normalizer (NOf M V g : Set G), k = y * e := by
  classical
  have hE_le_V : NOf M V g ≤ V := by rw [NOf, UOf]; exact inf_le_left.trans inf_le_left
  have hv₂V : v₂ ∈ V := h.le hv₂
  have hv₂sq : v₂ * v₂ = 1 := h.elemAbelian.mul_self_eq_one hv₂V
  have hv₂_ne_one : v₂ ≠ 1 := by
    intro h1
    exact hv₂D (h1.symm ▸ (Z0Of M V₀ g).one_mem)
  have hkM : k ∈ M := hk.1
  have hkF : k ∈ Subgroup.normalizer ((NOf M V g ⊔ zpowers v₂ : Subgroup G) : Set G) := hk.2
  have hk₀ : k ∈ Subgroup.normalizer (V₀ : Set G) := by rw [h.normalizer₀]; exact hkM
  have hkv₂ : k * v₂ * k⁻¹ = v₂ := by
    have hmem : k * v₂ * k⁻¹ ∈ (NOf M V g ⊔ zpowers v₂) ⊓ V₀ :=
      ⟨(Subgroup.mem_normalizer_iff.1 hkF v₂).1
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers v₂)),
        (Subgroup.mem_normalizer_iff.1 hk₀ v₂).1 hv₂⟩
    rw [sup_zpowers_inf_eq h.elemAbelian h.le hE_le_V h.V₀_inf_N hv₂] at hmem
    rcases (mem_zpowers_iff_of_mul_self_eq_one hv₂sq).1 hmem with h1 | h1
    · exfalso
      have hz : v₂ = 1 := by
        calc v₂ = k⁻¹ * (k * v₂ * k⁻¹) * k := by group
          _ = k⁻¹ * 1 * k := by rw [h1]
          _ = 1 := by group
      exact hv₂_ne_one hz
    · exact h1
  have hk'v₂ : k⁻¹ * v₂ * k = v₂ := by
    calc k⁻¹ * v₂ * k = k⁻¹ * (k * v₂ * k⁻¹) * k := by rw [hkv₂]
      _ = v₂ := by group
  have hk'F : k⁻¹ ∈ Subgroup.normalizer ((NOf M V g ⊔ zpowers v₂ : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ hkF
  have hEE' : ∀ e ∈ NOf M V g, e ∉ conjSubgroup (NOf M V g) k⁻¹ →
      e * v₂ ∈ conjSubgroup (NOf M V g) k⁻¹ := by
    intro e he he'
    have hk'eF : k⁻¹ * e * k ∈ NOf M V g ⊔ zpowers v₂ := by
      have h := (Subgroup.mem_normalizer_iff.1 hk'F e).1 (Subgroup.mem_sup_left he)
      simpa [inv_inv] using h
    obtain ⟨e₁, he₁, hx | hx⟩ := (mem_sup_zpowers_iff h.elemAbelian hE_le_V hv₂V).1 hk'eF
    · have hmem : e ∈ conjSubgroup (NOf M V g) k⁻¹ := by
        rw [mem_conjSubgroup_iff, inv_inv]
        rw [hx]; exact he₁
      exact absurd hmem he'
    · have heq : k⁻¹ * (e * v₂) * k = e₁ := by
        rw [show k⁻¹ * (e * v₂) * k = (k⁻¹ * e * k) * (k⁻¹ * v₂ * k) by group,
          hx, hk'v₂, mul_assoc, hv₂sq, mul_one]
      rw [mem_conjSubgroup_iff, inv_inv, heq]
      exact he₁
  by_cases hleE : NOf M V g ≤ conjSubgroup (NOf M V g) k⁻¹
  · have hcard : Nat.card (conjSubgroup (NOf M V g) k⁻¹) = Nat.card (NOf M V g) :=
      CFSG.Quasithin.E3.card_conjSubgroup _ _
    have hEq : conjSubgroup (NOf M V g) k⁻¹ = NOf M V g :=
      (Subgroup.eq_of_le_of_card_ge hleE (le_of_eq hcard)).symm
    have hknormE : k ∈ Subgroup.normalizer (NOf M V g : Set G) := by
      rw [Subgroup.mem_normalizer_iff'']
      intro h
      constructor
      · intro hh
        have hh' : h ∈ conjSubgroup (NOf M V g) k⁻¹ := by rwa [← hEq] at hh
        rwa [mem_conjSubgroup_iff, inv_inv] at hh'
      · intro hh
        have hh' : h ∈ conjSubgroup (NOf M V g) k⁻¹ := by
          rw [mem_conjSubgroup_iff, inv_inv]; exact hh
        rwa [hEq] at hh'
    exact ⟨1, (F11.CTilde M V₀ V).one_mem, k, ⟨hkM, hknormE⟩, by rw [one_mul]⟩
  · obtain ⟨e₀, he₀, he₀'⟩ := SetLike.not_le_iff_exists.1 hleE
    let W : Subgroup G := V₀ ⊔ (NOf M V g ⊓ conjSubgroup (NOf M V g) k⁻¹)
    have hWrel : W.relIndex V = 2 :=
      relIndex_sup_inf_eq_two h.elemAbelian h.le hE_le_V h.V₀_inf_N
        (h.V_eq_V₀_sup_N hV₀K).symm hv₂ hEE' he₀ he₀'
    have hW_le_V : W ≤ V := sup_le h.le (inf_le_left.trans hE_le_V)
    have hV₀W : V₀ ≤ W := le_sup_left
    obtain ⟨x, hxC, hxker⟩ := exists_mem_forall_commutator_mem_iff
      (V := V) (V₀ := V₀) (D := Z0Of M V₀ g) (H := F11.CTilde M V₀ V) (W := W)
      h.elemAbelian h.le inf_le_left (relIndex_Z0_eq_two h hV₀K hn)
      (fun x hx v hv => (FourteenTwo.mem_cTilde_iff_comm.1 hx).2.2 v hv)
      (fun x hx v hv => commutator_mem_Z0 h hV₀K hn hD (cTilde_le_M M V₀ V hx) hv)
      (fun v hv hvD => mem_V₀_of_forall_commutator_mem h15 h hD hnot hv hvD)
      hW_le_V hV₀W hWrel
    obtain ⟨y, hy, hyker⟩ := exists_mem_normalizer_F_iff h15 h hV₀K hn hD hv₂ hv₂D hxC
    have hyE : ∀ e ∈ NOf M V g, y * e * y⁻¹ ∈ conjSubgroup (NOf M V g) k⁻¹ := by
      intro e he
      have heV : e ∈ V := hE_le_V he
      have hyC : y ∈ F11.CTilde M V₀ V := hy.1
      have hyF : y ∈ Subgroup.normalizer
          ((NOf M V g ⊔ zpowers v₂ : Subgroup G) : Set G) := hy.2
      have hyM : y ∈ M := cTilde_le_M M V₀ V hyC
      have hyN : y ∈ Subgroup.normalizer (V : Set G) := by rw [h.normalizer_eq]; exact hyM
      have hyeF : y * e * y⁻¹ ∈ NOf M V g ⊔ zpowers v₂ :=
        (Subgroup.mem_normalizer_iff.1 hyF e).1 (Subgroup.mem_sup_left he)
      have hyeV : y * e * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hyN e).1 heV
      have hyeV₀ : y * e * y⁻¹ * e⁻¹ ∈ V₀ :=
        (FourteenTwo.mem_cTilde_iff_comm.1 hyC).2.2 e heV
      have hcFV : y * e * y⁻¹ * e⁻¹ ∈ (NOf M V g ⊔ zpowers v₂) ⊓ V₀ :=
        ⟨(NOf M V g ⊔ zpowers v₂).mul_mem hyeF
          (Subgroup.mem_sup_left ((NOf M V g).inv_mem he)), hyeV₀⟩
      rw [sup_zpowers_inf_eq h.elemAbelian h.le hE_le_V h.V₀_inf_N hv₂] at hcFV
      have hcFV' : y * e * y⁻¹ * e⁻¹ = 1 ∨ y * e * y⁻¹ * e⁻¹ = v₂ :=
        (mem_zpowers_iff_of_mul_self_eq_one hv₂sq).1 hcFV
      have hckey : y * e * y⁻¹ * e⁻¹ ∈ Z0Of M V₀ g ↔
          e ∈ conjSubgroup (NOf M V g) k⁻¹ := by
        rw [hyker e heV]
        exact (hxker e heV).trans
          (mem_sup_inf_iff h.elemAbelian h.le hE_le_V h.V₀_inf_N he)
      by_cases he' : e ∈ conjSubgroup (NOf M V g) k⁻¹
      · have hcD : y * e * y⁻¹ * e⁻¹ ∈ Z0Of M V₀ g := hckey.2 he'
        have hc_eq : y * e * y⁻¹ * e⁻¹ = 1 := by
          rcases hcFV' with h1 | h1
          · exact h1
          · exact absurd (h1 ▸ hcD) hv₂D
        have hye_eq : y * e * y⁻¹ = e := by
          have h2 : y * e * y⁻¹ = (y * e * y⁻¹ * e⁻¹) * e := by group
          rw [hc_eq] at h2
          simpa using h2
        rw [hye_eq]; exact he'
      · have hcD : y * e * y⁻¹ * e⁻¹ ∉ Z0Of M V₀ g := fun hh => he' (hckey.1 hh)
        have hc_eq : y * e * y⁻¹ * e⁻¹ = v₂ := by
          rcases hcFV' with h1 | h1
          · exact absurd (h1.symm ▸ (Z0Of M V₀ g).one_mem) hcD
          · exact h1
        have hye_eq : y * e * y⁻¹ = e * v₂ := by
          have h2 : y * e * y⁻¹ = (y * e * y⁻¹ * e⁻¹) * e := by group
          rw [hc_eq] at h2
          rw [h2, h.elemAbelian.comm hv₂V heV]
        rw [hye_eq]
        exact hEE' e he he'
    have hconj_le : conjSubgroup (NOf M V g) y⁻¹ ≤ conjSubgroup (NOf M V g) k⁻¹ := by
      intro w hw
      rw [mem_conjSubgroup_iff] at hw
      have hw' : y⁻¹ * w * y ∈ NOf M V g := by simpa [inv_inv] using hw
      have hw_eq : w = y * (y⁻¹ * w * y) * y⁻¹ := by group
      rw [hw_eq]
      exact hyE (y⁻¹ * w * y) hw'
    have hcardY : Nat.card (conjSubgroup (NOf M V g) y⁻¹) = Nat.card (NOf M V g) :=
      CFSG.Quasithin.E3.card_conjSubgroup _ _
    have hcardK : Nat.card (conjSubgroup (NOf M V g) k⁻¹) = Nat.card (NOf M V g) :=
      CFSG.Quasithin.E3.card_conjSubgroup _ _
    have hEq : conjSubgroup (NOf M V g) y⁻¹ = conjSubgroup (NOf M V g) k⁻¹ :=
      Subgroup.eq_of_le_of_card_ge hconj_le (le_of_eq (hcardK.trans hcardY.symm))
    have hnorm : y⁻¹ * k ∈ Subgroup.normalizer (NOf M V g : Set G) := by
      rw [← conjSubgroup_eq_iff_mem_normalizer]
      rw [← conjSubgroup_conjSubgroup, hEq, conjSubgroup_conjSubgroup, inv_mul_cancel,
        conjSubgroup_one]
    exact ⟨y, hy.1, y⁻¹ * k,
      ⟨M.mul_mem (M.inv_mem (cTilde_le_M M V₀ V hy.1)) hkM, hnorm⟩, by group⟩

theorem commutator_cTilde_le (h15 : Hyp15 M V₀ V) (h : Hyp65 n M V₀ V g)
    (hV₀K : ¬ V₀ ≤ KOf M V g) (hn : (UOf M V g).relIndex V = 2)
    (hD : M ≤ normalizer ((Z0Of M V₀ g : Subgroup G) : Set G)) :
    ⁅F11.CTilde M V₀ V, V⁆ ≤ V₀ ⊓ conjSubgroup M g := by
  by_contra hnot
  have hnot' : ¬ ⁅F11.CTilde M V₀ V, V⁆ ≤ Z0Of M V₀ g := by
    rw [Z0Of]; exact hnot
  have hD2 : (Z0Of M V₀ g).relIndex V₀ = 2 := relIndex_Z0_eq_two h hV₀K hn
  have hnotV₀ : ¬ V₀ ≤ Z0Of M V₀ g := by
    intro hle
    have h1 : (Z0Of M V₀ g).relIndex V₀ = 1 := Subgroup.relIndex_eq_one.2 hle
    rw [hD2] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨v₂, hv₂, hv₂D⟩ := SetLike.not_le_iff_exists.1 hnotV₀
  refine false_of_forall_eq_mul h15 h hV₀K ?_
  intro m hm
  obtain ⟨a, haC, -, k, hk, hmk⟩ :=
    exists_mul_mem_normalizer_F h15 h hV₀K hn hD hv₂ hv₂D m hm
  obtain ⟨y, hyC, e, he, hke⟩ :=
    exists_cTilde_mul_mem_normalizer_N h15 h hV₀K hn hD hnot' hv₂ hv₂D hk
  exact ⟨a * y, (F11.CTilde M V₀ V).mul_mem haC hyC, e, he, by rw [hmk, hke]; group⟩

end Certified

end FourteenFive

end CFSG.LocalAnalysis.WeakClosure81
