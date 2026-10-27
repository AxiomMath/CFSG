module

public import CFSG.Quasithin.H13.A6S13826c
public import CFSG.Quasithin.Background.SmithB42Alt6Norm

public section

namespace CFSG.Quasithin.H13.A6

open Equiv Equiv.Perm CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B42Alt6
open CFSG.Quasithin.S143
open scoped Pointwise

namespace A6Md

variable {S : Type} [CommGroup S]

theorem card_sup_mul_inf (A B : Subgroup S) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have : B.Normal := Subgroup.normal_of_isMulCommutative B
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : B ≤ A ⊔ B)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem natural_of_isIrr [Finite S] (hS : ∀ s : S, s * s = 1) {L : Subgroup (MulAut S)}
    (ιL : ↥L ≃* alternatingGroup (Fin 6)) {M : Subgroup S} (hM : XMod.IsIrr ↥L M)
    (hMfix : ∀ m ∈ M, (∀ l ∈ L, l m = m) → m = 1) (hcard : Nat.card M < 2 ^ 16) :
    Nat.card M = 16 := by
  classical
  have hinv : ∀ k ∈ L, ∀ m ∈ M, k m ∈ M := fun k hk m hm => hM.1 ⟨k, hk⟩ m hm
  have hKs : L ≤ stabSub M := fun k hk u => ⟨fun h => by
      have := hinv k⁻¹ (L.inv_mem hk) _ h
      simpa using this, fun h => hinv k hk u h⟩
  set r : ↥L →* MulAut ↥M := (resHom M).comp (Subgroup.inclusion hKs) with hr
  have hsimp : IsSimpleGroup ↥L := by
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact ιL.isSimpleGroup
  have hMne : M ≠ ⊥ := hM.2.1.ne'
  have hrinj : Function.Injective r := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal r.ker with h | h
    · exact h
    · exfalso
      apply hMne
      rw [eq_bot_iff]
      intro m hm
      refine hMfix m hm fun k hk => ?_
      have h1 : r ⟨k, hk⟩ = 1 := (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top _)
      exact congrArg (fun φ : MulAut ↥M => ((φ ⟨m, hm⟩ : ↥M) : S)) h1
  set LM : Subgroup (MulAut ↥M) := r.range with hLM
  let eK : ↥L ≃* ↥LM := MonoidHom.ofInjective hrinj
  let ιM : ↥LM ≃* alternatingGroup (Fin 6) := eK.symm.trans ιL
  have hSM : ∀ s : ↥M, s * s = 1 := fun s => Subtype.ext (hS s)
  have hirrM : XMod.IsIrrSec ↥LM (⊥ : Subgroup ↥M) ⊤ := by
    refine ⟨?_, fun J hJ _ _ => ?_⟩
    · rw [bot_lt_iff_ne_bot]
      intro h
      apply hMne
      rw [eq_bot_iff]
      intro m hm
      have : (⟨m, hm⟩ : ↥M) ∈ (⊤ : Subgroup ↥M) := trivial
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    · have hJ' : XMod.IsInv ↥L (J.map M.subtype) := by
        rintro ⟨k, hk⟩ _ ⟨j, hj, rfl⟩
        exact ⟨r ⟨k, hk⟩ j, hJ ⟨r ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩⟩ j hj, rfl⟩
      rcases hM.2.2 _ hJ' bot_le (Subgroup.map_subtype_le J) with h | h
      · left
        rw [eq_bot_iff]
        intro j hj
        have : (j : S) ∈ J.map M.subtype := ⟨j, hj, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.2 (Subtype.ext this)
      · right
        rw [eq_top_iff]
        intro j _
        have : (j : S) ∈ J.map M.subtype := by rw [h]; exact j.2
        obtain ⟨j', hj', hjj⟩ := this
        rwa [Subtype.ext hjj] at hj'
  obtain ⟨N⟩ := exists_n6Model hSM ιM hirrM hcard
  exact N.card_eq

theorem natural_of_card_le [Finite S] (hS : ∀ s : S, s * s = 1) {G L : Subgroup (MulAut S)}
    (C : Ctx G L) (hfix : fixV L = ⊥)
    (hirr : ∀ J : Subgroup S, (∀ g ∈ G, ∀ y ∈ J, g y ∈ J) → J = ⊥ ∨ J = ⊤)
    (hne : (⊤ : Subgroup S) ≠ ⊥) (hcard : Nat.card S ≤ 2 ^ 6) :
    Nat.card S = 16 ∧ XMod.IsIrr ↥L (⊤ : Subgroup S) := by
  classical
  obtain ⟨ι⟩ := C.iso
  have hMfix : ∀ M : Subgroup S, ∀ m ∈ M, (∀ l ∈ L, l m = m) → m = 1 := by
    intro M m _ h
    have : m ∈ fixV L := fun l hl => h l hl
    rw [hfix] at this
    exact this
  obtain ⟨M, -, hM⟩ := A6Hm.exists_isIrr_le (A := ↥L) (XMod.isInv_top (A := ↥L) (Q := S)) hne
  have hM16 : Nat.card M = 16 :=
    natural_of_isIrr hS ι hM (hMfix M) (lt_of_le_of_lt (Subgroup.card_le_card_group M)
      (lt_of_le_of_lt hcard (by norm_num)))
  by_cases hMt : M = ⊤
  · refine ⟨?_, hMt ▸ hM⟩
    rw [← hM16, hMt, Subgroup.card_top]
  · exfalso
    obtain ⟨g, hg, hgM⟩ : ∃ g ∈ G, ¬ (∀ y ∈ M, g y ∈ M) := by
      by_contra h
      push Not at h
      rcases hirr M h with h0 | h1
      · exact hM.2.1.ne' h0
      · exact hMt h1
    set M' : Subgroup S := M.map (g : MulAut S).toMonoidHom with hM'
    have hM'inv : XMod.IsInv ↥L M' := by
      rintro ⟨l, hl⟩ _ ⟨m, hm, rfl⟩
      refine ⟨(g⁻¹ * l * g) m, hM.1 ⟨g⁻¹ * l * g, ?_⟩ m hm, ?_⟩
      · have := C.normal g⁻¹ (G.inv_mem hg) l hl
        simpa using this
      · show g ((g⁻¹ * l * g) m) = l (g m)
        simp
    have hM'c : Nat.card M' = 16 := by
      rw [hM', Subgroup.card_map_of_injective (g : MulAut S).injective, hM16]
    have hMM' : M ⊓ M' = ⊥ := by
      rcases hM.2.2 (M ⊓ M') (hM.1.inf hM'inv) bot_le inf_le_left with h | h
      · exact h
      · exfalso
        have hle : M ≤ M' := h ▸ inf_le_right
        have heq : M = M' := Subgroup.eq_of_le_of_card_ge hle (by rw [hM16, hM'c])
        apply hgM
        intro y hy
        rw [heq]
        exact ⟨y, hy, rfl⟩
    have h1 := card_sup_mul_inf M M'
    rw [hMM', Subgroup.card_bot, mul_one, hM16, hM'c] at h1
    have h2 := Subgroup.card_le_card_group (M ⊔ M')
    rw [h1] at h2
    have := h2.trans hcard
    norm_num at this

theorem natural_of_index_le [Finite S] (hS : ∀ s : S, s * s = 1) {G L : Subgroup (MulAut S)}
    (C : Ctx G L) (hfix : fixV L = ⊥)
    (hirr : ∀ J : Subgroup S, (∀ g ∈ G, ∀ y ∈ J, g y ∈ J) → J = ⊥ ∨ J = ⊤)
    (hne : (⊤ : Subgroup S) ≠ ⊥) {B : Subgroup (MulAut S)} (hBG : B ≤ G) (hB1 : B ≠ ⊥)
    (hB : IsElemAbelian2 B) (hle : (fixV B).index ≤ Nat.card B) :
    Nat.card S = 16 ∧ XMod.IsIrr ↥L (⊤ : Subgroup S) :=
  natural_of_card_le hS C hfix hirr hne (card_le_of_index_le C hfix hBG hB1 hB hle)

theorem natural_of_index_le_sq [Finite S]
    (hS : ∀ s : S, s * s = 1) {G L T : Subgroup (MulAut S)} (C : Ctx G L) (hfix : fixV L = ⊥)
    (hirr : ∀ J : Subgroup S, (∀ g ∈ G, ∀ y ∈ J, g y ∈ J) → J = ⊥ ∨ J = ⊤)
    (hne : (⊤ : Subgroup S) ≠ ⊥) (hT2 : IsPGroup 2 T) (hTG : T ≤ G) (hGLT : G ≤ L ⊔ T)
    {c : MulAut S} (hcL : c ∈ L) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hcc : ∀ t ∈ T, ∃ k ∈ L, t⁻¹ * c * t = k * c * k⁻¹ ∨ t⁻¹ * c * t = k * c⁻¹ * k⁻¹)
    {B : Subgroup (MulAut S)} (hBG : B ≤ G) (hB1 : B ≠ ⊥)
    (hB : IsElemAbelian2 B) (hle : (fixV B).index ≤ Nat.card B ^ 2) :
    Nat.card S = 16 ∧ XMod.IsIrr ↥L (⊤ : Subgroup S) := by
  classical
  obtain ⟨ι⟩ := C.iso
  have hcard := card_le_of_index_le_sq C hfix hBG hB1 hB hle
  have hS2 : ∀ y : S, y ^ 2 = 1 := fun y => by rw [pow_two]; exact hS y
  have hTL : ∀ t ∈ T, ∀ k ∈ L, t * k * t⁻¹ ∈ L := fun t ht k hk => C.normal t (hTG ht) k hk
  have hirr' : ∀ J : Subgroup S, (∀ k ∈ L, ∀ y ∈ J, k y ∈ J) → (∀ t ∈ T, ∀ y ∈ J, t y ∈ J) →
      J = ⊥ ∨ J = ⊤ := by
    intro J hJL hJT
    refine hirr J fun g hg y hy => ?_
    have hgLT : g ∈ L ⊔ T := hGLT hg
    let St : Subgroup (MulAut S) :=
      { carrier := {x | ∀ y ∈ J, x y ∈ J ∧ x⁻¹ y ∈ J}
        one_mem' := fun y hy => ⟨hy, hy⟩
        mul_mem' := fun {a b} ha hb y hy => ⟨(ha _ (hb y hy).1).1, by
          rw [mul_inv_rev]; exact (hb _ (ha y hy).2).2⟩
        inv_mem' := fun {a} ha y hy => ⟨(ha y hy).2, by rw [inv_inv]; exact (ha y hy).1⟩ }
    have hLT : L ⊔ T ≤ St := sup_le
      (fun k hk y hy => ⟨hJL k hk y hy, hJL k⁻¹ (L.inv_mem hk) y hy⟩)
      (fun t ht y hy => ⟨hJT t ht y hy, hJT t⁻¹ (T.inv_mem ht) y hy⟩)
    exact (hLT hgLT y hy).1
  have hMfix : ∀ M : Subgroup S, ∀ m ∈ M, (∀ l ∈ L, l m = m) → m = 1 := by
    intro M m _ h
    have : m ∈ fixV L := fun l hl => h l hl
    rw [hfix] at this
    exact this
  have hirrL : XMod.IsIrr ↥L (⊤ : Subgroup S) := by
    refine A6Hm.isIrr_top_of_homog hS2 hT2 hTL hirr' hne fun M hM t => ?_
    have hsm : (t • M : Subgroup S) = (t : MulAut S) • M := rfl
    rw [hsm]
    obtain ⟨k₀, hk₀, hk₀c⟩ := hcc t t.2
    refine A6Hm.iso_smul_of_class hS ι hM (hMfix M)
      (lt_of_le_of_lt (Subgroup.card_le_card_group M) (lt_of_le_of_lt hcard (by norm_num)))
      (fun k hk => ?_) hcL hc3 hc1 hk₀ hk₀c
    have := hTL (t : MulAut S)⁻¹ (T.inv_mem t.2) k hk
    simpa using this
  refine ⟨?_, hirrL⟩
  have h16 := natural_of_isIrr hS ι hirrL (hMfix ⊤)
    (by rw [Subgroup.card_top]; exact lt_of_le_of_lt hcard (by norm_num))
  rwa [Subgroup.card_top] at h16

theorem n6_fix_ge_eight : ∀ σ : Perm (Fin 6),
    8 ≤ (Finset.univ.filter fun v : N6 => n6Act σ v = v).card →
      σ = 1 ∨ ∃ i j : Fin 6, i ≠ j ∧ σ = swap i j := by
  decide +kernel

theorem n6_swap_agree : ∀ i j k l : Fin 6, i ≠ j → k ≠ l → swap i j ≠ swap k l →
    (Finset.univ.filter fun v : N6 =>
      n6Act (swap i j) v * v⁻¹ = n6Act (swap k l) v * v⁻¹).card < 8 := by
  decide +kernel

theorem card_fix_ge_eight [Finite S] (hS : ∀ s : S, s * s = 1) (hcard : Nat.card S = 16)
    {f : S →* S} {z : S} (hf : ∀ v, f v = 1 ∨ f v = z) : 8 ≤ Nat.card f.ker := by
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hS z
  have hrange : Nat.card f.range ≤ 2 := by
    have hle : f.range ≤ Subgroup.zpowers z := by
      rintro _ ⟨v, rfl⟩
      rcases hf v with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact Subgroup.mem_zpowers z
    calc Nat.card f.range ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hle
      _ = orderOf z := Nat.card_zpowers z
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hz2
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hcard] at h1
  have h2 : 16 ≤ Nat.card f.ker * 2 := by
    calc 16 = Nat.card f.ker * Nat.card f.range := h1.symm
      _ ≤ Nat.card f.ker * 2 := Nat.mul_le_mul_left _ hrange
  omega

@[expose] def commMap (g : MulAut S) : S →* S where
  toFun v := g v * v⁻¹
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, mul_inv_rev]; ac_rfl

theorem commMap_apply (g : MulAut S) (v : S) : commMap g v = g v * v⁻¹ := rfl

theorem card_le_two_of_center [Finite S] (hS : ∀ s : S, s * s = 1) {G L : Subgroup (MulAut S)}
    (C : Ctx G L) (M : N6Model L) {B : Subgroup (MulAut S)} (hBG : B ≤ G) {z : S}
    (hz : ∀ b ∈ B, ∀ v : S, b v * v⁻¹ = 1 ∨ b v * v⁻¹ = z) : Nat.card B ≤ 2 := by
  classical
  obtain ⟨ι⟩ := C.iso
  have hcard := M.card_eq
  have hz2 : z * z = 1 := hS z
  have hσ : ∀ b ∈ B, ∃ σ, M.ρ σ = b ∧ (σ = 1 ∨ ∃ i j : Fin 6, i ≠ j ∧ σ = swap i j) := by
    intro b hb
    obtain ⟨σ, hσ⟩ := M.le_range hS ι (show b ∈ Subgroup.normalizer (L : Set (MulAut S)) from
      Subgroup.mem_normalizer_iff.2 fun l => ⟨fun hl => C.normal b (hBG hb) l hl, fun hl => by
        have := C.normal b⁻¹ (G.inv_mem (hBG hb)) _ hl
        simpa [mul_assoc] using this⟩)
    refine ⟨σ, hσ, n6_fix_ge_eight σ ?_⟩
    have h8 := card_fix_ge_eight hS hcard (f := commMap b) (z := z) (hz b hb)
    calc 8 ≤ Nat.card (commMap b).ker := h8
      _ = (Finset.univ.filter fun w : N6 => n6Act σ w = w).card := by
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
        refine Nat.card_congr (M.Θ.toEquiv.subtypeEquiv fun v => ?_)
        rw [MonoidHom.mem_ker, commMap_apply, mul_inv_eq_one]
        show b v = v ↔ n6Act σ (M.Θ v) = M.Θ v
        rw [← M.Θ_ρ, hσ]
        exact ⟨fun h => by rw [h], fun h => M.Θ.injective h⟩
  have key : ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ 1 → b₂ ≠ 1 → b₁ = b₂ := by
    intro b₁ hb₁ b₂ hb₂ h1 h2
    obtain ⟨σ₁, rfl, hσ₁⟩ := hσ b₁ hb₁
    obtain ⟨σ₂, rfl, hσ₂⟩ := hσ b₂ hb₂
    rcases hσ₁ with rfl | ⟨i, j, hij, rfl⟩
    · exact absurd (map_one M.ρ) h1
    rcases hσ₂ with rfl | ⟨k, l, hkl, rfl⟩
    · exact absurd (map_one M.ρ) h2
    by_contra hne
    have hsw : swap i j ≠ swap k l := fun h => hne (by rw [h])
    set f : S →* S := commMap (M.ρ (swap i j)) * (commMap (M.ρ (swap k l)))⁻¹ with hfdef
    have hf : ∀ v, f v = 1 ∨ f v = z := by
      intro v
      have e : f v = commMap (M.ρ (swap i j)) v * (commMap (M.ρ (swap k l)) v)⁻¹ := rfl
      rw [e, commMap_apply, commMap_apply]
      rcases hz _ hb₁ v with ha | ha <;> rcases hz _ hb₂ v with hb | hb <;> rw [ha, hb]
      · left; simp
      · right; rw [one_mul]; exact inv_eq_of_mul_eq_one_right hz2
      · right; simp
      · left; exact mul_inv_cancel z
    have h8 := card_fix_ge_eight hS hcard hf
    have hlt := n6_swap_agree i j k l hij hkl hsw
    have heq : Nat.card f.ker = (Finset.univ.filter fun w : N6 =>
        n6Act (swap i j) w * w⁻¹ = n6Act (swap k l) w * w⁻¹).card := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      refine Nat.card_congr (M.Θ.toEquiv.subtypeEquiv fun v => ?_)
      rw [MonoidHom.mem_ker]
      have e : f v = commMap (M.ρ (swap i j)) v * (commMap (M.ρ (swap k l)) v)⁻¹ := rfl
      rw [e, mul_inv_eq_one, commMap_apply, commMap_apply]
      show _ ↔ n6Act (swap i j) (M.Θ v) * (M.Θ v)⁻¹ = n6Act (swap k l) (M.Θ v) * (M.Θ v)⁻¹
      rw [← M.Θ_ρ, ← M.Θ_ρ, ← map_inv, ← map_mul, ← map_mul]
      exact ⟨fun h => by rw [h], fun h => M.Θ.injective h⟩
    omega
  by_cases hB : ∃ b₀ ∈ B, b₀ ≠ 1
  · obtain ⟨b₀, hb₀, hb₀1⟩ := hB
    have hle : B ≤ Subgroup.zpowers b₀ := by
      intro b hb
      by_cases hb1 : b = 1
      · rw [hb1]; exact one_mem _
      · rw [key b hb b₀ hb₀ hb1 hb₀1]; exact Subgroup.mem_zpowers b₀
    have h2 : b₀ ^ 2 = 1 := by
      have := (hσ b₀ hb₀)
      obtain ⟨σ, hσb, hσ1 | ⟨i, j, -, rfl⟩⟩ := this
      · rw [← hσb, hσ1, map_one, one_pow]
      · rw [← hσb, ← map_pow, pow_two, swap_mul_self, map_one]
    calc Nat.card B ≤ Nat.card (Subgroup.zpowers b₀) := Subgroup.card_le_of_le hle
      _ = orderOf b₀ := Nat.card_zpowers b₀
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) h2
  · push Not at hB
    have : B = ⊥ := eq_bot_iff.2 fun b hb => Subgroup.mem_bot.2 (hB b hb)
    rw [this, Subgroup.card_bot]
    norm_num

end A6Md

end CFSG.Quasithin.H13.A6
