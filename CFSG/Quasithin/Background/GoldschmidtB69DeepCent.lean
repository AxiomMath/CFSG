module

public import CFSG.Quasithin.Background.B69Cnt

public section

namespace CFSG.Quasithin

open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V]

theorem commute_of_centSec {A L : Subgroup (MulAut V)} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) {a : MulAut V} (ha : a ∈ A)
    (haTr : a ∈ centSec W (fixV L)) : ∀ l ∈ L, a * l = l * a := by
  obtain ⟨hinv, hcomm, hlt, -⟩ := mem_irrPlus_top_iff.1 hW
  have hLW : L ≤ stabSub W := B1.le_stabSub_of_invariant hinv
  have hLU : L ≤ stabSub (fixV L) := B1.le_stabSub_of_invariant (isInv_fixV L)
  have ha'Tr : a⁻¹ ∈ centSec W (fixV L) := (centSec W (fixV L)).inv_mem haTr
  have hc : ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ L ⊓ centSec W (fixV L) := by
    intro l hl
    refine ⟨L.mul_mem (hAn a ha l hl) (L.inv_mem hl), ?_⟩
    have h1 : l * a⁻¹ * l⁻¹ ∈ centSec W (fixV L) :=
      conj_mem_centSec (hLW hl) (hLU hl) ha'Tr
    have h2 := (centSec W (fixV L)).mul_mem haTr h1
    simpa [mul_assoc] using h2
  set L₁ : Subgroup ↥L := (centSec W (fixV L)).subgroupOf L with hL₁
  have : L₁.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hL₁, Subgroup.mem_subgroupOf] at hx ⊢
    have := conj_mem_centSec (h := (g : MulAut V)) (hLW g.2) (hLU g.2) hx
    simpa using this
  have hL₁ne : L₁ ≠ ⊤ := by
    intro htop
    have hLTr : ∀ x ∈ L, x ∈ centSec W (fixV L) := fun x hx => by
      have : (⟨x, hx⟩ : ↥L) ∈ L₁ := by rw [htop]; trivial
      exact this
    have hle : commSub W L ≤ W ⊓ fixV L := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      exact ⟨W.mul_mem (hinv x hx w hw) (W.inv_mem hw), (hLTr x hx).2 w hw⟩
    rw [hcomm] at hle
    have : W ⊓ fixV L = W := le_antisymm inf_le_left hle
    rw [this] at hlt
    exact lt_irrefl _ hlt
  have hcent : L₁ ≤ Subgroup.center ↥L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hL L₁ hL₁ne
  have hperf : Group.IsPerfect ↥L := ⟨hL.1⟩
  let φ : ↥L →* ↥L :=
    { toFun := fun l => ⟨a * l * a⁻¹, hAn a ha l l.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp [mul_assoc] }
  have hφ : ∀ l : ↥L, l⁻¹ * φ l ∈ Subgroup.center ↥L := by
    rintro ⟨x, hx⟩
    have hmem : (⟨a * x * a⁻¹ * x⁻¹, (hc x hx).1⟩ : ↥L) ∈ L₁ := (hc x hx).2
    have hz := hcent hmem
    have : (⟨x, hx⟩ : ↥L)⁻¹ * φ ⟨x, hx⟩ = ⟨a * x * a⁻¹ * x⁻¹, (hc x hx).1⟩ := by
      have hz' := Subgroup.mem_center_iff.mp hz ⟨x, hx⟩
      apply Subtype.ext
      have h5 : x * (a * x * a⁻¹ * x⁻¹) = a * x * a⁻¹ * x⁻¹ * x := congrArg Subtype.val hz'
      show x⁻¹ * (a * x * a⁻¹) = a * x * a⁻¹ * x⁻¹
      calc x⁻¹ * (a * x * a⁻¹) = x⁻¹ * ((a * x * a⁻¹ * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (a * x * a⁻¹ * x⁻¹)) := by rw [h5]
        _ = a * x * a⁻¹ * x⁻¹ := by group
    rw [this]
    exact hz
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    φ hφ
  intro l hl
  have h6 : a * l * a⁻¹ = l :=
    congrArg (fun f : ↥L →* ↥L => ((f ⟨l, hl⟩ : ↥L) : MulAut V)) hid
  calc a * l = (a * l * a⁻¹) * a := by group
    _ = l * a := by rw [h6]

theorem mem_centSec_of_commute (hV : ∀ v : V, v ^ 2 = 1) {A L : Subgroup (MulAut V)}
    (hAel : IsElemAbelian2 A) (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hWA : ∀ b ∈ A, ∀ w ∈ W, b w ∈ W) {a : MulAut V}
    (ha : a ∈ A) (hal : ∀ l ∈ L, a * l = l * a) : a ∈ centSec W (fixV L) := by
  obtain ⟨hinv, -, hlt, hirr⟩ := mem_irrPlus_top_iff.1 hW
  have haW : a ∈ stabSub W := B1.le_stabSub_of_invariant hWA ha
  have haU : ∀ w ∈ fixV L, a w ∈ fixV L := B1Red.fixV_inv_of_normalizes hAn a ha
  have haa : a * a = 1 := by rw [← sq]; exact hAel.2 a ha
  have ha2 : ∀ w : V, a (a w) = w := fun w => by
    have := congrArg (fun g : MulAut V => g w) haa
    simpa using this
  have hinv2 : ∀ w : V, w⁻¹ = w := fun w => by
    have := hV w
    rw [sq] at this
    exact inv_eq_of_mul_eq_one_right this
  let J : Subgroup V :=
    { carrier := {w | w ∈ W ∧ a w * w⁻¹ ∈ fixV L}
      one_mem' := ⟨W.one_mem, by simp⟩
      mul_mem' := fun {x y} hx hy => ⟨W.mul_mem hx.1 hy.1, by
        have e : a (x * y) * (x * y)⁻¹ = (a x * x⁻¹) * (a y * y⁻¹) := by
          rw [map_mul, mul_inv_rev]
          ac_rfl
        rw [e]
        exact (fixV L).mul_mem hx.2 hy.2⟩
      inv_mem' := fun {x} hx => ⟨W.inv_mem hx.1, by
        have e : a x⁻¹ * (x⁻¹)⁻¹ = (a x * x⁻¹)⁻¹ := by
          simp only [map_inv, mul_inv_rev, inv_inv]
          exact mul_comm _ _
        rw [e]
        exact (fixV L).inv_mem hx.2⟩ }
  have hJinv : ∀ x ∈ L, ∀ w ∈ J, x w ∈ J := by
    intro x hx w hw
    refine ⟨hinv x hx w hw.1, ?_⟩
    have h1 : a (x w) = x (a w) := congrArg (fun g : MulAut V => g w) (hal x hx)
    have e : a (x w) * (x w)⁻¹ = x (a w * w⁻¹) := by
      rw [h1, map_mul, map_inv]
    rw [e]
    exact isInv_fixV L x hx _ hw.2
  have hle : W ⊓ fixV L ≤ J := fun w hw =>
    ⟨hw.1, (fixV L).mul_mem (haU w hw.2) ((fixV L).inv_mem hw.2)⟩
  have hJW : J ≤ W := fun w hw => hw.1
  rcases hirr J hJinv hle hJW with hJ | hJ
  · exfalso
    obtain ⟨w, hwW, hwU⟩ := IsConcreteLE.exists_of_lt hlt
    have hwU' : w ∉ fixV L := fun h => hwU ⟨hwW, h⟩
    by_cases hcase : a w * w⁻¹ ∈ fixV L
    · have hwJ : w ∈ J := ⟨hwW, hcase⟩
      rw [hJ] at hwJ
      exact hwU' hwJ.2
    · have hyW : w * a w ∈ W := W.mul_mem hwW (hWA a ha w hwW)
      have hyJ : w * a w ∈ J := by
        refine ⟨hyW, ?_⟩
        have e : a (w * a w) * (w * a w)⁻¹ = 1 := by
          rw [map_mul, ha2, mul_inv_rev, mul_mul_mul_comm, mul_inv_cancel, mul_inv_cancel,
            one_mul]
        rw [e]
        exact (fixV L).one_mem
      rw [hJ] at hyJ
      apply hcase
      have e : a w * w⁻¹ = w * a w := by rw [hinv2 w, mul_comm]
      rw [e]
      exact hyJ.2
  · exact ⟨haW, fun w hw => by
      have hwJ : w ∈ J := by rw [hJ]; exact hw
      exact hwJ.2⟩

theorem inf_centSec_le (hV : ∀ v : V, v ^ 2 = 1) {A L : Subgroup (MulAut V)}
    (hAel : IsElemAbelian2 A) (hL : CFSG.Open.IsQuasisimple ↥L)
    (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) {W₁ W₂ : Subgroup V}
    (h₁ : W₁ ∈ IrrPlus L (⊤ : Subgroup V)) (h₂ : W₂ ∈ IrrPlus L (⊤ : Subgroup V))
    (hA₂ : ∀ b ∈ A, ∀ w ∈ W₂, b w ∈ W₂) :
    A ⊓ centSec W₁ (fixV L) ≤ centSec W₂ (fixV L) := fun _ ha =>
  mem_centSec_of_commute hV hAel hAn h₂ hA₂ ha.1 (commute_of_centSec hL hAn h₁ ha.1 ha.2)

end B69

end CFSG.Quasithin
