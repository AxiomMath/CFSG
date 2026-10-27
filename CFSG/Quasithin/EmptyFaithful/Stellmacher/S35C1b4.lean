module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1b3

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.C1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_functional {V Z : Subgroup G} (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hZV : Z ≤ V) {c : G} (hc : c ∈ V) (hcZ : c ∉ Z) :
    ∃ l0 : G → ZMod 2, (∀ x ∈ V, ∀ y ∈ V, l0 (x * y) = l0 x + l0 y) ∧ (∀ z ∈ Z, l0 z = 0) ∧
      l0 c = 1 := by
  classical
  set S : Set (Subgroup G) := {H | H ≤ V ∧ Z ≤ H ∧ c ∉ H} with hS
  have hne : S.Nonempty := ⟨Z, hZV, le_rfl, hcZ⟩
  obtain ⟨H, hHS, hmax⟩ := S.toFinite.exists_maximalFor id S hne
  obtain ⟨hHV, hZH, hcH⟩ := hHS
  have hsq : ∀ x ∈ V, x * x = 1 := fun x hx => by rw [← pow_two]; exact hV2 x hx
  have key : ∀ x ∈ V, x ∉ H → ∃ h ∈ H, c = x * h := by
    intro x hx hxH
    by_contra hcon
    push Not at hcon
    have hxc : ∀ h ∈ H, x * h = h * x := fun h hh => hV x hx h (hHV hh)
    let H' : Subgroup G :=
      { carrier := {y | y ∈ H ∨ ∃ h ∈ H, y = x * h}
        one_mem' := Or.inl H.one_mem
        mul_mem' := by
          rintro a b (ha | ⟨h, hh, rfl⟩) (hb | ⟨h', hh', rfl⟩)
          · exact Or.inl (H.mul_mem ha hb)
          · exact Or.inr ⟨a * h', H.mul_mem ha hh', by
            calc a * (x * h') = (a * x) * h' := by group
              _ = (x * a) * h' := by rw [hxc a ha]
              _ = x * (a * h') := by group⟩
          · refine Or.inr ⟨h * b, H.mul_mem hh hb, by group⟩
          · refine Or.inl ?_
            have e : x * h * (x * h') = h * h' := by
              calc x * h * (x * h') = x * (h * x) * h' := by group
                _ = x * (x * h) * h' := by rw [hxc h hh]
                _ = (x * x) * h * h' := by group
                _ = h * h' := by rw [hsq x hx]; group
            rw [e]; exact H.mul_mem hh hh'
        inv_mem' := by
          rintro a (ha | ⟨h, hh, rfl⟩)
          · exact Or.inl (H.inv_mem ha)
          · refine Or.inr ⟨h⁻¹, H.inv_mem hh, ?_⟩
            have e : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
            rw [mul_inv_rev, e]
            exact (hxc h⁻¹ (H.inv_mem hh)).symm }
    have hHH' : H ≤ H' := fun y hy => Or.inl hy
    have hH'V : H' ≤ V := by
      rintro y (hy | ⟨h, hh, rfl⟩)
      · exact hHV hy
      · exact V.mul_mem hx (hHV hh)
    by_cases hcH' : c ∈ H'
    · rcases hcH' with h | ⟨h, hh, hch⟩
      · exact hcH h
      · exact hcon h hh hch
    · have hH'S : H' ∈ S := ⟨hH'V, hZH.trans hHH', hcH'⟩
      have := hmax hH'S (show id H ≤ id H' from hHH')
      exact hxH (this (Or.inr ⟨1, H.one_mem, by simp⟩))
  refine ⟨fun y => if y ∈ H then 0 else 1, ?_, ?_, ?_⟩
  · intro x hx y hy
    by_cases hxH : x ∈ H <;> by_cases hyH : y ∈ H
    · simp [hxH, hyH, H.mul_mem hxH hyH]
    · have : x * y ∉ H := fun h => hyH (by simpa using H.mul_mem (H.inv_mem hxH) h)
      simp [hxH, hyH, this]
    · have : x * y ∉ H := fun h => hxH (by simpa using H.mul_mem h (H.inv_mem hyH))
      simp [hxH, hyH, this]
    · obtain ⟨h1, hh1, hc1⟩ := key x hx hxH
      obtain ⟨h2, hh2, hc2⟩ := key y hy hyH
      have hxy : x * y ∈ H := by
        have hx' : x = c * h1⁻¹ := eq_mul_inv_of_mul_eq hc1.symm
        have hy' : y = c * h2⁻¹ := eq_mul_inv_of_mul_eq hc2.symm
        have hcc : c * h1⁻¹ = h1⁻¹ * c := hV c hc _ (V.inv_mem (hHV hh1))
        have e : x * y = (c * c) * h1⁻¹ * h2⁻¹ := by
          calc x * y = c * (h1⁻¹ * c) * h2⁻¹ := by rw [hx', hy']; group
            _ = c * (c * h1⁻¹) * h2⁻¹ := by rw [hcc]
            _ = (c * c) * h1⁻¹ * h2⁻¹ := by group
        rw [e, hsq c hc, one_mul]
        exact H.mul_mem (H.inv_mem hh1) (H.inv_mem hh2)
      have : (1 : ZMod 2) + 1 = 0 := by decide
      simp [hxH, hyH, hxy, this]
  · intro z hz
    simp [hZH hz]
  · simp [hcH]

theorem collapse {F V C Z : Subgroup G}
    (hq : Nonempty (OTwoQuot F ≃* Equiv.Perm (Fin 5)))
    (hFV : F ≤ Subgroup.normalizer (V : Set G))
    (hV2 : ∀ x ∈ V, x ^ 2 = 1) (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hZC : Z ≤ C) (_hZc : ∀ z ∈ Z, ∀ f ∈ F, f * z = z * f)
    (hC : C = V ⊓ Subgroup.centralizer (oTwoRes F : Set G))
    (hQ : ⁅V, pCoreOf 2 F⁆ ≤ Z)
    (hVL : V ≤ ⁅V, oTwoRes F⁆)
    (ho : IsOrthSec F C V) : C ≤ Z := by
  intro c hcC
  by_contra hcZ
  have hCV : C ≤ V := hC ▸ inf_le_left
  have hZV : Z ≤ V := hZC.trans hCV
  have hCL : ∀ c ∈ C, ∀ a ∈ oTwoRes F, a * c = c * a := fun c hc a ha =>
    Subgroup.mem_centralizer_iff.mp (hC ▸ hc : c ∈ V ⊓ Subgroup.centralizer (oTwoRes F : Set G)).2
      a ha
  have hQ' : ∀ x ∈ V, ∀ q ∈ pCoreOf 2 F, ⁅x, q⁆ ∈ Z := fun x hx q hq' =>
    hQ (Subgroup.commutator_mem_commutator hx hq')
  obtain ⟨l0, h0, h0Z, h0c⟩ := exists_functional hV2 hV hZV (hCV hcC) hcZ
  obtain ⟨l, hadd, hlC, hinv⟩ :=
    exists_invariant_functional hq hCV hZV hCL hQ' ho l0 h0 h0Z
  have hl1 : l 1 = 0 := by
    have h := hadd 1 V.one_mem 1 V.one_mem
    rw [mul_one] at h
    exact add_eq_left.mp h.symm
  let K : Subgroup G :=
    { carrier := {x | x ∈ V ∧ l x = 0}
      one_mem' := ⟨V.one_mem, hl1⟩
      mul_mem' := fun {x y} hx hy => ⟨V.mul_mem hx.1 hy.1, by rw [hadd x hx.1 y hy.1, hx.2, hy.2,
        add_zero]⟩
      inv_mem' := fun {x} hx => ⟨V.inv_mem hx.1, by
        have h := hadd x hx.1 x⁻¹ (V.inv_mem hx.1)
        rw [mul_inv_cancel, hl1, hx.2, zero_add] at h
        exact h.symm⟩ }
  have hle : ⁅V, oTwoRes F⁆ ≤ K := by
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨v, hv, a, ha, rfl⟩
    have hva : a * v⁻¹ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hFV (oTwoRes_le F ha)) v⁻¹).mp (V.inv_mem hv)
    have e : ⁅v, a⁆ = v * (a * v⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
    refine ⟨by rw [e]; exact V.mul_mem hv hva, ?_⟩
    show l ⁅v, a⁆ = 0
    rw [e, hadd v hv _ hva, hinv a ha v⁻¹ (V.inv_mem hv)]
    have h := hadd v hv v⁻¹ (V.inv_mem hv)
    rw [mul_inv_cancel, hl1] at h
    exact h.symm
  have hcK := hle (hVL (hCV hcC))
  have := hcK.2
  rw [hlC c hcC, h0c] at this
  exact one_ne_zero this

end CFSG.Quasithin.F53.Stellmacher.S35.C1
