module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModPair
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModNorm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open

variable {V : Type} [CommGroup V]

theorem c23a_modPair_rankLe [Finite V] {Mb L₁ L₂ : Subgroup (MulAut V)}
    {E₁ E₂ Z₁ Z₂ : Subgroup V} (h : C23AModPair Mb L₁ L₂ E₁ E₂ Z₁ Z₂)
    {A : Subgroup (MulAut V)} (hA : A ≤ Mb) (hel : IsElemAbelian 2 A)
    (hnorm : ∀ a ∈ A, ∀ e ∈ E₁, a e ∈ E₁) (hcent : ∀ a ∈ A, ∀ y ∈ E₂, a y = y) :
    rk ↥A ≤ 2 := by
  classical
  obtain ⟨D⟩ := h.blk₁.nat
  have hnonSwap : ∀ a ∈ A, a ∈ Subgroup.normalizer (L₁ : Set (MulAut V)) ∧
      (∀ e ∈ E₁, a e ∈ E₁) := by
    intro a ha
    rcases h.perm a (hA ha) with ⟨hL₁, _, hE₁, _⟩ | ⟨hswap₁, _⟩
    · exact ⟨hL₁, hE₁⟩
    · exfalso
      have hsub : E₁ ≤ E₂ := by
        intro e he
        have hae : a e ∈ E₂ := hswap₁ e he
        have hfix : a e = e := by
          have ha2 : a * a = 1 := by rw [← pow_two]; exact hel.2 a ha
          have h1 : a (a e) = e := by
            have := congrArg (fun z : MulAut V => z e) ha2
            simpa [MulAut.mul_apply] using this
          exact (h1.symm.trans (hcent a ha (a e) hae)).symm
        rw [← hfix]
        exact hae
      have hE₁Z : E₁ ≤ Z₁ := le_trans (le_inf le_rfl hsub) h.inf₁
      have hcardle : Nat.card ↥E₁ ≤ Nat.card ↥Z₁ := Subgroup.card_le_of_le hE₁Z
      have hcardE : Nat.card ↥E₁ = 2 ^ 3 * Nat.card ↥Z₁ := c23a_block_card_eq h.blk₁
      have hZpos : 0 < Nat.card ↥Z₁ := Nat.card_pos
      have hlt : Nat.card ↥Z₁ < 2 ^ 3 * Nat.card ↥Z₁ := by
        simpa using Nat.mul_lt_mul_of_pos_right (show (1 : ℕ) < 2 ^ 3 by norm_num) hZpos
      have hlt' : Nat.card ↥Z₁ < Nat.card ↥E₁ := by
        rw [hcardE]
        exact hlt
      exact absurd hlt' (not_lt_of_ge hcardle)
  have hLE : ∀ l ∈ L₁, ∀ e ∈ E₁, l e ∈ E₁ := by
    intro l hl e he
    obtain ⟨γ, hγ⟩ := D.surj ⟨l, hl⟩
    have hcoe : ((D.ρ γ : ↥L₁) : MulAut V) = l := congrArg Subtype.val hγ
    rw [← hcoe]
    exact D.inv γ e he
  have huniq : ∀ (l l' : ↥L₁), (∀ e ∈ E₁, (l : MulAut V) e = (l' : MulAut V) e) → l = l' := by
    intro l l' hll'
    have hmem : (l : MulAut V)⁻¹ * (l' : MulAut V) ∈ L₁ := L₁.mul_mem (L₁.inv_mem l.2) l'.2
    have hfix : ∀ e ∈ E₁, ((l : MulAut V)⁻¹ * (l' : MulAut V)) e = e := by
      intro e he
      rw [MulAut.mul_apply, ← hll' e he, MulAut.inv_apply_self]
    have h1 := c23a_eq_one_of_fix h.blk₁ hmem hfix
    have h2 : (l' : MulAut V) = (l : MulAut V) := by
      have h := congrArg (fun z : MulAut V => (l : MulAut V) * z) h1
      simpa using h
    exact Subtype.ext h2.symm
  have key : ∀ a : ↥A, ∃ l : ↥L₁, ∀ e ∈ E₁, (a : MulAut V) e = (l : MulAut V) e := by
    intro a
    obtain ⟨hL₁, hE₁⟩ := hnonSwap (a : MulAut V) a.2
    obtain ⟨l, hl, h⟩ := c23a_normalizer_act h.blk₁ hL₁ hE₁
    exact ⟨⟨l, hl⟩, h⟩
  let f : ↥A → ↥L₁ := fun a => Classical.choose (key a)
  have hf : ∀ a : ↥A, ∀ e ∈ E₁, (a : MulAut V) e = (f a : MulAut V) e :=
    fun a => Classical.choose_spec (key a)
  have f_mul : ∀ a b : ↥A, f (a * b) = f a * f b := by
    intro a b
    apply huniq
    intro e he
    have hbmem : (f b : MulAut V) e ∈ E₁ := hLE (f b) (f b).2 e he
    calc (f (a * b) : MulAut V) e
        = ((a * b : ↥A) : MulAut V) e := by rw [hf (a * b) e he]
      _ = (a : MulAut V) ((b : MulAut V) e) := by
            rw [Subgroup.coe_mul, MulAut.mul_apply]
      _ = (a : MulAut V) ((f b : MulAut V) e) := by rw [hf b e he]
      _ = (f a : MulAut V) ((f b : MulAut V) e) := hf a ((f b : MulAut V) e) hbmem
      _ = ((f a * f b : ↥L₁) : MulAut V) e := by rw [Subgroup.coe_mul, MulAut.mul_apply]
  have f_one : f 1 = 1 := by
    apply huniq
    intro e he
    simpa using (hf 1 e he).symm
  let φ : ↥A →* ↥L₁ :=
    { toFun := f
      map_one' := f_one
      map_mul' := f_mul }
  have hinj : Function.Injective φ := by
    intro a b hab
    have hab' : ((φ a : ↥L₁) : MulAut V) = ((φ b : ↥L₁) : MulAut V) := congrArg Subtype.val hab
    have hax : ∀ x ∈ E₁, (a : MulAut V) x = (b : MulAut V) x := by
      intro x hx
      rw [hf a x hx, hf b x hx]
      exact DFunLike.congr_fun hab' x
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    have hv : v ∈ E₁ ⊔ E₂ := by rw [h.sup]; exact Subgroup.mem_top v
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hv
    calc (a : MulAut V) (x * y)
        = (a : MulAut V) x * (a : MulAut V) y := map_mul (a : MulAut V) x y
      _ = (b : MulAut V) x * (b : MulAut V) y := by
            rw [hax x hx, hcent a a.2 y hy, hcent b b.2 y hy]
      _ = (b : MulAut V) (x * y) := (map_mul (b : MulAut V) x y).symm
  let A' : Subgroup (MulAut V) := (⊤ : Subgroup ↥A).map (L₁.subtype.comp φ)
  have hA' : A' ≤ L₁ := by
    rintro x ⟨a, _, rfl⟩
    exact (φ a).2
  have helTop : IsElemAbelian 2 (⊤ : Subgroup ↥A) := by
    have h := hel.subgroupOf A
    rw [Subgroup.subgroupOf_self] at h
    exact h
  have hel' : IsElemAbelian 2 A' := IsElemAbelian.map helTop (L₁.subtype.comp φ)
  have hcomp : Function.Injective (L₁.subtype.comp φ) := by
    intro a b hab
    exact hinj (Subtype.ext hab)
  have hcard : Nat.card ↥A' = Nat.card ↥A :=
    (Subgroup.card_map_of_injective (f := L₁.subtype.comp φ) hcomp).trans Subgroup.card_top
  have hle := c23a_rk_le_two_of_le h.blk₁ hA' hel'
  unfold rk at hle ⊢
  rw [hcard] at hle
  exact hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
