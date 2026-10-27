module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Claim1
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem relIndex_le_two_of_forall {H J : Subgroup G}
    (h : ∀ a ∈ J, ∀ b ∈ J, a ∉ H → b ∉ H → a * b⁻¹ ∈ H) : H.relIndex J ≤ 2 := by
  by_cases hJ : J ≤ H
  · rw [Subgroup.relIndex_eq_one.mpr hJ]; norm_num
  · rw [IsConcreteLE.not_le_iff_exists] at hJ
    obtain ⟨a, haJ, haH⟩ := hJ
    have : (H.subgroupOf J).index = 2 := by
      rw [Subgroup.index_eq_two_iff']
      refine ⟨⟨a, haJ⟩, fun b => ?_⟩
      by_cases hb : (b : G) ∈ H
      · have : a * (b : G) ∉ H := fun hab => haH (by simpa using H.mul_mem hab (H.inv_mem hb))
        simp [Subgroup.mem_subgroupOf, hb, this]
      · have hb' : (b : G)⁻¹ ∉ H := fun hh => hb (by simpa using H.inv_mem hh)
        have := h a haJ (b : G)⁻¹ (J.inv_mem b.2) haH hb'
        simp only [inv_inv] at this
        simp [Subgroup.mem_subgroupOf, hb, this]
    exact this.le

theorem elemAbelian_comm {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem comm_mem_of_normalizer {E : Subgroup G} {x w : G} (hx : x ∈ Subgroup.normalizer (E : Set G))
    (hw : w ∈ E) : ⁅w, x⁆ ∈ E := by
  have h1 : x * w⁻¹ * x⁻¹ ∈ E := by
    have := (Subgroup.mem_normalizer_iff.mp hx w⁻¹).mp (E.inv_mem hw)
    exact this
  have : ⁅w, x⁆ = w * (x * w⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]; exact E.mul_mem hw h1

theorem commutator_mul_of_abelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {x v w : G}
    (hx : x ∈ Subgroup.normalizer (E : Set G)) (hv : v ∈ E) (hw : w ∈ E) :
    ⁅v * w, x⁆ = ⁅w, x⁆ * ⁅v, x⁆ := by
  have h1 : ⁅v * w, x⁆ = v * ⁅w, x⁆ * v⁻¹ * ⁅v, x⁆ := by
    simp only [commutatorElement_def]; group
  have h2 := elemAbelian_comm hE hv (comm_mem_of_normalizer hx hw)
  rw [h1, h2]; simp [mul_assoc]

def commKernel (E V Zm : Subgroup G) (x : G) (hE : IsElemAbelian 2 E)
    (hx : x ∈ Subgroup.normalizer (E : Set G)) (hV : V ≤ E) : Subgroup G where
  carrier := {v | v ∈ V ∧ ⁅v, x⁆ ∈ Zm}
  one_mem' := by simp [V.one_mem, Zm.one_mem]
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨V.mul_mem ha hb, ?_⟩
    rw [commutator_mul_of_abelian hE hx (hV ha) (hV hb)]
    exact Zm.mul_mem hb' ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨V.inv_mem ha, ?_⟩
    have := commutator_mul_of_abelian hE hx (hV (V.inv_mem ha)) (hV ha)
    rw [inv_mul_cancel] at this
    have h0 : ⁅(1 : G), x⁆ = 1 := by simp
    rw [h0] at this
    have h1 : ⁅(a⁻¹ : G), x⁆ = (⁅a, x⁆)⁻¹ := eq_inv_of_mul_eq_one_right this.symm
    rw [h1]; exact Zm.inv_mem ha'


theorem commutator_inv_of_abelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {x v : G}
    (hx : x ∈ Subgroup.normalizer (E : Set G)) (hv : v ∈ E) : ⁅v⁻¹, x⁆ = (⁅v, x⁆)⁻¹ := by
  have := commutator_mul_of_abelian hE hx (E.inv_mem hv) hv
  rw [inv_mul_cancel] at this
  have h0 : ⁅(1 : G), x⁆ = 1 := by simp
  rw [h0] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem mem_sup_exists_mul_of_comm {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {y : G} (hy : y ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  let S : Subgroup G :=
    { carrier := {y | ∃ a ∈ A, ∃ b ∈ B, y = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have := hc a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [this.symm]
          _ = _ := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have := hc a ha b hb
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := (Commute.inv_inv (show Commute a b from this)).eq.symm }
  have : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact this hy


theorem eq_of_card_le_two {Z : Subgroup G} [Finite G] (hZ : Nat.card Z ≤ 2) {a b : G}
    (ha : a ∈ Z) (hb : b ∈ Z) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  by_contra hab
  let f : Fin 3 → Z := ![1, ⟨a, ha⟩, ⟨b, hb⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f, Subtype.ext_iff] at hij ⊢ <;>
      first | rfl | (exfalso; simp_all)
  have := Nat.card_le_card_of_injective f hf
  simp at this
  omega

theorem exists_comm_kernel_relIndex_le_four [Finite G] {Wm W0 Zm Za V : Subgroup G} {x : G}
    (hWab : IsElemAbelian 2 Wm) (hx : x ∈ Subgroup.normalizer (Wm : Set G))
    (hW0i : W0.relIndex Wm ≤ 2) (hZm : Zm ≤ Wm) (hZa : Za ≤ Wm)
    (hZacard : Nat.card Za ≤ 2) (hcomm : ∀ w ∈ W0, ⁅w, x⁆ ∈ Zm ⊔ Za) (hV : V ≤ Wm) :
    ∃ K : Subgroup G, (∀ v, v ∈ K ↔ v ∈ V ∧ ⁅v, x⁆ ∈ Zm) ∧ K.relIndex V ≤ 4 := by
  refine ⟨commKernel Wm V Zm x hWab hx hV, fun v => Iff.rfl, ?_⟩
  set K := commKernel Wm V Zm x hWab hx hV with hK
  have hKmem : ∀ v, v ∈ K ↔ v ∈ V ∧ ⁅v, x⁆ ∈ Zm := fun v => Iff.rfl
  set K1 := K ⊓ W0 with hK1
  have hK1V : K1 ≤ V ⊓ W0 := fun v hv => ⟨((hKmem v).mp hv.1).1, hv.2⟩
  have h1 : K.relIndex V ≤ K1.relIndex V :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (relIndex_ne_zero' _ _))
      (Subgroup.relIndex_dvd_of_le_left V (inf_le_left : K1 ≤ K))
  have h2 : K1.relIndex (V ⊓ W0) * (V ⊓ W0).relIndex V = K1.relIndex V :=
    Subgroup.relIndex_mul_relIndex _ _ _ hK1V inf_le_left
  have h3 : (V ⊓ W0).relIndex V ≤ 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_le_of_le_right hV (relIndex_ne_zero' _ _)).trans hW0i
  have h4 : K1.relIndex (V ⊓ W0) ≤ 2 := by
    apply relIndex_le_two_of_forall
    rintro a ⟨haV, haW⟩ b ⟨hbV, hbW⟩ haK hbK
    have haZ : ⁅a, x⁆ ∉ Zm := fun h => haK ⟨(hKmem a).mpr ⟨haV, h⟩, haW⟩
    have hbZ : ⁅b, x⁆ ∉ Zm := fun h => hbK ⟨(hKmem b).mpr ⟨hbV, h⟩, hbW⟩
    obtain ⟨ma, hma, ta, hta, hea⟩ := mem_sup_exists_mul_of_comm
      (fun m hm t ht => elemAbelian_comm hWab (hZm hm) (hZa ht)) (hcomm a haW)
    obtain ⟨mb, hmb, tb, htb, heb⟩ := mem_sup_exists_mul_of_comm
      (fun m hm t ht => elemAbelian_comm hWab (hZm hm) (hZa ht)) (hcomm b hbW)
    have hta1 : ta ≠ 1 := by
      rintro rfl; exact haZ (by rw [hea]; simpa using hma)
    have htb1 : tb ≠ 1 := by
      rintro rfl; exact hbZ (by rw [heb]; simpa using hmb)
    have htab := eq_of_card_le_two hZacard hta htb hta1 htb1
    have hbinv : ⁅b⁻¹, x⁆ = (⁅b, x⁆)⁻¹ := commutator_inv_of_abelian hWab hx (hV hbV)
    have hea' : ⁅a, x⁆ = ma * tb := by rw [hea, htab]
    have hc := elemAbelian_comm hWab (hZm (Zm.mul_mem (Zm.inv_mem hmb) hma)) (hZa htb)
    refine ⟨(hKmem _).mpr ⟨V.mul_mem haV (V.inv_mem hbV), ?_⟩, W0.mul_mem haW (W0.inv_mem hbW)⟩
    rw [commutator_mul_of_abelian hWab hx (hV haV) (hV (V.inv_mem hbV)), hbinv, hea', heb]
    have : (mb * tb)⁻¹ * (ma * tb) = mb⁻¹ * ma := by
      calc (mb * tb)⁻¹ * (ma * tb) = tb⁻¹ * ((mb⁻¹ * ma) * tb) := by group
        _ = tb⁻¹ * (tb * (mb⁻¹ * ma)) := by rw [hc]
        _ = mb⁻¹ * ma := by group
    rw [this]
    exact Zm.mul_mem (Zm.inv_mem hmb) hma
  rw [← h2] at h1
  have := Nat.mul_le_mul h4 h3
  omega

end CFSG.Quasithin.Kleidman.F53Hss36
