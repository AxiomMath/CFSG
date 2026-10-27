module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtV2InQSev2
public import CFSG.Quasithin.EmptyFaithful.S151ZY

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

namespace V2InQ

variable {G : Type} [Group G] [Finite G]

theorem ybar_facts {T M V Z₁ V₂ : Subgroup G} {hVe : IsElemAbelian 2 V}
    (d : Seven7Data V M T hVe) (hZV : Z₁ ≤ V) (hWV : V₂ ≤ V) (hsplit : Z₁ ⊔ V₂ = V)
    (hZc : Nat.card Z₁ = 4) (hWc : Nat.card V₂ = 16) {c : G}
    (hcN : c ∈ Subgroup.normalizer (V : Set G))
    (hcP : conjAct V ⟨c, hcN⟩ ∈ oTwoUpper (autOn M V)) (hcZ : ∀ a ∈ Z₁, c * a * c⁻¹ = a)
    (hcW : ∀ a ∈ V₂, c * a * c⁻¹ ∈ V₂) (hfpf : ∀ a ∈ V₂, c * a * c⁻¹ = a → a = 1)
    {y : MulAut ↥V} (hy : y = conjAct V ⟨c, hcN⟩) :
    y ^ 3 = 1 ∧ @fixOf ↥V (commGroupOfElemAbelian hVe) y = Z₁.subgroupOf V ∧
      @fixOf ↥V (commGroupOfElemAbelian hVe) y ≠ ⊥ ∧
      Nat.card (@fixOf ↥V (commGroupOfElemAbelian hVe) y) = 4 ∧
      (@normOf ↥V (commGroupOfElemAbelian hVe) y).ker = V₂.subgroupOf V ∧ y ≠ 1 ∧
      y ∉ frattiniIn (oTwoUpper (autOn M V)) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hyP : y ∈ oTwoUpper (autOn M V) := hy ▸ hcP
  have hy3 : y ^ 3 = 1 := d.ctx.exp_P y hyP
  have hsup : Z₁.subgroupOf V ⊔ V₂.subgroupOf V = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hZV hWV, hsplit, Subgroup.subgroupOf_self]
  have hZ : ∀ a ∈ Z₁.subgroupOf V, y a = a := by
    intro a ha
    apply Subtype.ext
    rw [hy, conj_coe_apply]
    exact hcZ a ha
  have hfpf' : ∀ a ∈ V₂.subgroupOf V, y a = a → a = 1 := by
    intro a ha hya
    have h1 : c * (a : G) * c⁻¹ = a := by
      have := congrArg (fun u : ↥V => (u : G)) hya
      simpa [hy, conj_coe_apply] using this
    exact Subtype.ext (hfpf a ha h1)
  have hW : ∀ a ∈ V₂.subgroupOf V, y a ∈ V₂.subgroupOf V := by
    intro a ha
    show ((y a : ↥V) : G) ∈ V₂
    rw [hy, conj_coe_apply]
    exact hcW a ha
  have hfix : fixOf y = Z₁.subgroupOf V := fixOf_eq_of_split hsup hZ hfpf'
  have hcardZ : Nat.card (Z₁.subgroupOf V) = 4 := by rw [card_subgroupOf_of_le hZV, hZc]
  have hZne : Z₁.subgroupOf V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardZ
    omega
  have hWne : V₂.subgroupOf V ≠ ⊥ := by
    intro h
    have := card_subgroupOf_of_le hWV (X := V₂)
    rw [h, Subgroup.card_bot, hWc] at this
    omega
  have hy1 : y ≠ 1 := by
    intro h1
    obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hWne
    apply ha1
    exact Subtype.ext (hfpf' a ha (by rw [h1]; rfl))
  refine ⟨hy3, hfix, by rw [hfix]; exact hZne, by rw [hfix]; exact hcardZ,
    ker_normOf_eq_of_split hsup hy3 d.ctx.sq hZ hfpf' hW, hy1, ?_⟩
  intro hyZ
  obtain ⟨j, hj⟩ := SevenGen.Z_pow d.ctx d.gen hyZ
  by_cases h3 : 3 ∣ j
  · apply hy1
    obtain ⟨j', rfl⟩ := h3
    rw [hj, pow_mul, SevenGen.z3 d.ctx d.gen, one_pow]
  · obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZne
    have hya : (d.z ^ j) a = a := by
      rw [← hj]
      exact hZ a ha
    exact ha1 (Subtype.ext
      (fpf_pow_of_fpf (SevenGen.z3 d.ctx d.gen) (SevenGen.fpf_z' d.ctx d.gen) h3 a hya))

end V2InQ

end CFSG.Quasithin
