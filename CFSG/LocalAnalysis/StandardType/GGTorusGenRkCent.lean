module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem card_inf_centralizer_eq
    {p : ℕ} (hp : p.Prime) {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hP : GGTableBPosition p L' E I θ hE)
    (hC : E ⊓ Subgroup.centralizer (L' : Set M) ≠ ⊥) :
    Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) = p := by
  obtain ⟨-, hEA, -, -, h5, -⟩ := hP
  have hCE : (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) ≤ E := inf_le_left
  have hcyc : IsCyclic (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) :=
    h5 _ (hCE.trans le_sup_left) inf_le_right
      (isPGroup_of_isElemAbelian (isElemAbelian_mono hEA hCE))
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hEA.2 g (hCE g.2))
  have horder : orderOf g = Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hg_ne : orderOf g ≠ 1 := by
    intro h1
    apply hC
    apply le_antisymm _ bot_le
    intro x hx
    have hxmem : (⟨x, hx⟩ : ↥(E ⊓ Subgroup.centralizer (L' : Set M))) ∈ Subgroup.zpowers g :=
      hg ⟨x, hx⟩
    rw [orderOf_eq_one_iff.mp h1, Subgroup.zpowers_one_eq_bot] at hxmem
    have hx1 : (⟨x, hx⟩ : ↥(E ⊓ Subgroup.centralizer (L' : Set M))) = 1 :=
      Subgroup.mem_bot.mp hxmem
    exact congrArg Subtype.val hx1
  rw [← horder]
  rcases Nat.Prime.eq_one_or_self_of_dvd hp (orderOf g) (orderOf_dvd_of_pow_eq_one hgp) with
    h1 | hp'
  · exact absurd h1 hg_ne
  · exact hp'

theorem exists_mul_of_complement_position
    {p : ℕ} (hp : p.Prime) {M : Type} [Group M] [Finite M] {L' E E₁ : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hpos : GGTableBPosition p L' E I θ hE)
    (hC : E ⊓ Subgroup.centralizer (L' : Set M) ≠ ⊥) (hE₁E : E₁ ≤ E)
    (hE₁C : E₁ ⊓ Subgroup.centralizer (L' : Set M) = ⊥) (hcard : Nat.card E = p * Nat.card E₁) :
    (∀ x ∈ E, ∃ e₁ ∈ E₁, ∃ z ∈ E ⊓ Subgroup.centralizer (L' : Set M), x = e₁ * z) ∧
      L' ⊓ Subgroup.centralizer (E₁ : Set M) ≤ Subgroup.centralizer (E : Set M) := by
  have hcomm : ∀ x y : E, x * y = y * x := fun x y => hpos.2.1.1.is_comm.comm x y
  let C : Subgroup M := E ⊓ Subgroup.centralizer (L' : Set M)
  have hCdef : C = E ⊓ Subgroup.centralizer (L' : Set M) := rfl
  have hCE : C ≤ E := by rw [hCdef]; exact inf_le_left
  have hCcard : Nat.card C = p := by
    rw [hCdef]
    exact card_inf_centralizer_eq hp hpos hC
  have hE₁C' : E₁ ⊓ C = ⊥ := by
    rw [hCdef]
    apply le_antisymm _ bot_le
    intro x hx
    have hx' : x ∈ E₁ ⊓ Subgroup.centralizer (L' : Set M) := ⟨hx.1, hx.2.2⟩
    rw [hE₁C] at hx'
    exact hx'
  let φ : E₁ × C →* E :=
    { toFun := fun a => ⟨a.1.1 * a.2.1, E.mul_mem (hE₁E a.1.2) a.2.2.1⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (a.1.1 * b.1.1) * (a.2.1 * b.2.1) = (a.1.1 * a.2.1) * (b.1.1 * b.2.1)
        have hcomm' : b.1.1 * a.2.1 = a.2.1 * b.1.1 := by
          have h := hcomm ⟨b.1.1, hE₁E b.1.2⟩ ⟨a.2.1, a.2.2.1⟩
          simpa using congrArg Subtype.val h
        calc (a.1.1 * b.1.1) * (a.2.1 * b.2.1)
            = a.1.1 * (b.1.1 * (a.2.1 * b.2.1)) := mul_assoc _ _ _
          _ = a.1.1 * ((b.1.1 * a.2.1) * b.2.1) :=
                congrArg (fun z => a.1.1 * z) (mul_assoc _ _ _).symm
          _ = a.1.1 * ((a.2.1 * b.1.1) * b.2.1) :=
                congrArg (fun z => a.1.1 * (z * b.2.1)) hcomm'
          _ = a.1.1 * (a.2.1 * (b.1.1 * b.2.1)) :=
                congrArg (fun z => a.1.1 * z) (mul_assoc _ _ _)
          _ = (a.1.1 * a.2.1) * (b.1.1 * b.2.1) := (mul_assoc _ _ _).symm) }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have hM : a.1.1 * a.2.1 = b.1.1 * b.2.1 := congrArg Subtype.val hab
    have h1 : b.1.1⁻¹ * a.1.1 = b.2.1 * a.2.1⁻¹ := by
      calc b.1.1⁻¹ * a.1.1
          = b.1.1⁻¹ * (a.1.1 * a.2.1) * a.2.1⁻¹ := by group
        _ = b.1.1⁻¹ * (b.1.1 * b.2.1) * a.2.1⁻¹ := by rw [hM]
        _ = b.2.1 * a.2.1⁻¹ := by group
    have hmem : b.1.1⁻¹ * a.1.1 ∈ E₁ ⊓ C := by
      constructor
      · exact E₁.mul_mem (E₁.inv_mem b.1.2) a.1.2
      · rw [h1]
        exact C.mul_mem b.2.2 (C.inv_mem a.2.2)
    have hprod1 : b.1.1⁻¹ * a.1.1 = 1 := by
      have h := hmem
      rw [hE₁C'] at h
      simpa using h
    have ha1val : a.1.1 = b.1.1 := by
      have h := congrArg (fun x => b.1.1 * x) hprod1
      simpa using h
    have ha1 : a.1 = b.1 := Subtype.ext ha1val
    have h2 : a.1.1 * a.2.1 = a.1.1 * b.2.1 := by
      rw [← ha1val] at hM
      exact hM
    have ha2 : a.2 = b.2 := Subtype.ext (mul_left_cancel h2)
    exact Prod.ext ha1 ha2
  have hrange : Nat.card φ.range = Nat.card E := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφinj, Subgroup.card_top,
      Nat.card_prod, hCcard, hcard]
    exact Nat.mul_comm _ _
  have hφtop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq φ.range hrange
  have hdecomp : ∀ x ∈ E, ∃ e₁ ∈ E₁, ∃ z ∈ C, x = e₁ * z := by
    intro x hx
    have hxrange : (⟨x, hx⟩ : E) ∈ φ.range := by rw [hφtop]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_range] at hxrange
    obtain ⟨a, ha⟩ := hxrange
    refine ⟨a.1.1, a.1.2, a.2.1, a.2.2, ?_⟩
    have hval : (φ a).1 = x := congrArg Subtype.val ha
    rw [← hval]
    rfl
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨e₁, he₁, z, hz, hxz⟩ := hdecomp x hx
    exact ⟨e₁, he₁, z, hCdef ▸ hz, hxz⟩
  · intro x hx
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro e he
    obtain ⟨e₁, he₁, z, hz, rfl⟩ := hdecomp e he
    have hzx : z * x = x * z := (hz.2 x hxL).symm
    have he₁x : e₁ * x = x * e₁ := hxC e₁ he₁
    calc (e₁ * z) * x = e₁ * (z * x) := mul_assoc _ _ _
      _ = e₁ * (x * z) := by rw [hzx]
      _ = (e₁ * x) * z := (mul_assoc _ _ _).symm
      _ = (x * e₁) * z := by rw [he₁x]
      _ = x * (e₁ * z) := mul_assoc _ _ _

end CFSG.StandardType
