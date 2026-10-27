module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.E2Pair

public section

namespace CFSG.Quasithin.Res2

open CFSG.Open CFSG.QuasithinUnique B6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

omit [Finite G] in
theorem sq_eq_one_of_mem_conjSub_B (h : E2.Pair X T M V g) {a : G}
    (ha : a ∈ conjSub g (kerIn M X ⊓ V)) : a ^ 2 = 1 := by
  have h1 := h.elem.2 _ (mem_conjSub.mp ((conjSub g).monotone inf_le_right ha))
  have h2 : (g⁻¹ * a * g) ^ 2 = g⁻¹ * a ^ 2 * g := by
    have := conj_pow (a := g⁻¹) (b := a) (i := 2)
    simpa using this
  rw [h2] at h1
  have := congrArg (fun w => g * w * g⁻¹) h1
  simpa [mul_assoc] using this

theorem commutator_eq_bot_of_relIndex_two (h : E2.Pair X T M V g)
    (h2 : (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) = 2) :
    ⁅kerIn M X ⊓ V, conjSub g (kerIn M X ⊓ V)⁆ = ⊥ := by
  set B := kerIn M X ⊓ V with hB
  set A := conjSub g B with hA
  set Z := V ⊓ conjSub g V with hZ
  have hAP : A ≤ pCoreOf 2 X := h.A_le_pCoreOf
  have hAX : A ≤ X := hAP.trans (pCoreOf_le 2 X)
  have hBX : B ≤ X := h.B_le_pCoreOf.trans (pCoreOf_le 2 X)
  have hZB : Z ≤ B := h.inf_conj_le_kerIn_inf
  have hc : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z := fun z hz x hx => h.mem_center hz hx
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro b hb a ha
  rw [Subgroup.mem_bot, commutatorElement_def]
  by_cases haZ : a ∈ Z
  · have e : a * b = b * a := hc a haZ b (hBX hb)
    rw [← e]
    group
  by_cases hbZ : b ∈ Z
  · have e : b * a = a * b := hc b hbZ a (hAX ha)
    rw [e]
    group
  have hBA : B ⊓ A = Z := h.B_inf_A
  have haB : a ∉ B := fun haB => haZ (by rw [← hBA]; exact ⟨haB, ha⟩)
  have hP : a ∈ B ⊔ A := Subgroup.mem_sup_right ha
  obtain ⟨v, hvV, hcZ⟩ : ∃ v ∈ V, v * a * v⁻¹ * a⁻¹ ∉ Z := by
    by_contra hcon
    refine haB (h.mem_B_of_commutator_mem_Z hP fun v hv => ?_)
    by_contra hvZ
    exact hcon ⟨v, hv, hvZ⟩
  set c := v * a * v⁻¹ * a⁻¹ with hcdef
  have hcB : c ∈ B := h.commutator_mem_B hvV (hAP ha)
  have hcav : c * a = v * a * v⁻¹ := by rw [hcdef]; group
  have hca2 : (c * a) ^ 2 = 1 := by
    rw [hcav]
    calc (v * a * v⁻¹) ^ 2 = v * a ^ 2 * v⁻¹ := conj_pow
      _ = 1 := by rw [sq_eq_one_of_mem_conjSub_B h ha]; group
  obtain ⟨z, hz, e⟩ := h.exists_swap hcB ha
  have hsq : (c * a) ^ 2 = z := by
    calc (c * a) ^ 2 = c * (a * c) * a := by rw [pow_two]; group
      _ = c * (c * a * z) * a := by rw [e]
      _ = c * c * a * (z * a) := by group
      _ = c * c * a * (a * z) := by rw [hc z hz a (hAX ha)]
      _ = c ^ 2 * a ^ 2 * z := by rw [pow_two, pow_two]; group
      _ = z := by rw [h.elem.2 c hcB.2, sq_eq_one_of_mem_conjSub_B h ha]; group
  have hz1 : z = 1 := hsq.symm.trans hca2
  have hca : a * c = c * a := by rw [e, hz1, mul_one]
  have hidx : (Z.subgroupOf B).index = 2 := h2
  have hcb : (⟨b, hb⟩ : B)⁻¹ * ⟨c, hcB⟩ ∈ Z.subgroupOf B := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    have hb' : (⟨b, hb⟩ : B)⁻¹ ∉ Z.subgroupOf B := fun hm => hbZ (by
      have := Subgroup.inv_mem _ hm
      simpa [Subgroup.mem_subgroupOf] using this)
    have hc' : (⟨c, hcB⟩ : B) ∉ Z.subgroupOf B := fun hm => hcZ (Subgroup.mem_subgroupOf.mp hm)
    exact iff_of_false hb' hc'
  have hw : b⁻¹ * c ∈ Z := Subgroup.mem_subgroupOf.mp hcb
  set w := b⁻¹ * c with hwdef
  have hwa : w⁻¹ * a * w = a := by
    have := hc w hw a (hAX ha)
    calc w⁻¹ * a * w = w⁻¹ * (a * w) := by group
      _ = w⁻¹ * (w * a) := by rw [this]
      _ = a := by group
  have hb2 : b = c * w⁻¹ := by rw [hwdef]; group
  calc b * a * b⁻¹ * a⁻¹ = (c * w⁻¹) * a * (c * w⁻¹)⁻¹ * a⁻¹ := by rw [← hb2]
    _ = c * (w⁻¹ * a * w) * c⁻¹ * a⁻¹ := by group
    _ = c * a * c⁻¹ * a⁻¹ := by rw [hwa]
    _ = 1 := by rw [← hca]; group

end CFSG.Quasithin.Res2
