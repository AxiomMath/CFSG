module

public import CFSG.Quasithin.Background.F918T9
public import CFSG.Quasithin.Background.F918U2
public import CFSG.Quasithin.Background.F918U6
public import CFSG.Quasithin.Background.F918U7
public import CFSG.Quasithin.Background.F918U8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option exponentiation.threshold 2048

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

attribute [local irreducible] D35Chk.invMask D35Chk.cmTab D35Chk.fxTab D35Chk.fdTab D35Chk.nbTab D35Chk.full

private theorem isSub_land {a b : ℕ} (ha : D35Chk.IsSub a) (hb : D35Chk.IsSub b) :
    D35Chk.IsSub (a &&& b) := by
  refine ⟨Nat.and_lt_two_pow a hb.1, fun c d hc hd => ?_⟩
  rw [Nat.testBit_and, Bool.and_eq_true] at hc hd ⊢
  exact ⟨ha.2 c d hc.1 hd.1, hb.2 c d hc.2 hd.2⟩

private theorem testBit_full (c : ℕ) : D35Chk.full.testBit c = decide (c < 1024) := by
  unfold D35Chk.full
  simp only [Nat.sub_eq, Nat.pow_eq]
  exact Nat.testBit_two_pow_sub_one 1024 c

private theorem isSub_full : D35Chk.IsSub D35Chk.full ∧ D35Chk.full.testBit 0 = true := by
  refine ⟨⟨?_, fun c d hc hd => ?_⟩, ?_⟩
  · unfold D35Chk.full
    simp only [Nat.sub_eq, Nat.pow_eq]
    exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos
  · rw [testBit_full] at hc hd ⊢
    simp only [decide_eq_true_eq] at hc hd ⊢
    exact Nat.xor_lt_two_pow (n := 10) hc hd
  · rw [testBit_full]
    decide

private theorem card_le_pivot {α : Type*} [Finite α] {S : ℕ} (hS : D35Chk.IsSub S)
    (h0 : S.testBit 0 = true) (f : α → ℕ) (hf : Function.Injective f)
    (hmem : ∀ a, S.testBit (f a) = true) : Nat.card α ≤ 2 ^ D35Chk.pivotDim S := by
  have hlt : ∀ a, f a < 1024 := by
    intro a
    by_contra hge
    have hge := Nat.le_of_not_lt hge
    have hS' : S < 2 ^ f a :=
      lt_of_lt_of_le hS.1 (Nat.pow_le_pow_right Nat.two_pos hge)
    have := Nat.testBit_lt_two_pow hS'
    rw [hmem a] at this
    exact Bool.noConfusion this
  have hcard := D35Chk.card_filter_eq_two_pow_pivotDim hS h0
  let g : α → ((Finset.range 1024).filter fun c => S.testBit c = true) :=
    fun a => ⟨f a, by simp [hlt a, hmem a]⟩
  have hg : Function.Injective g := fun a b h => hf (congrArg Subtype.val h)
  calc Nat.card α ≤ Nat.card ((Finset.range 1024).filter fun c => S.testBit c = true) :=
        Nat.card_le_card_of_injective g hg
    _ = ((Finset.range 1024).filter fun c => S.testBit c = true).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = 2 ^ D35Chk.pivotDim S := hcard

private structure Corr (E F : Subgroup ↥(StatedSL 5 (ZMod 2))) (nd : D35Chk.Node) : Prop where
  reach : D35Chk.Reach nd
  le : F ≤ E
  card : Nat.card F = 2 ^ nd.m
  fs : ∀ B : ↥(altMat 5),
    (∀ g ∈ F, mat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (mat g)ᵀ = B) →
      nd.FS.testBit (D35Chk.codeOfMat (B : Matrix (Fin 5) (Fin 5) (ZMod 2))) = true
  fd : ∀ B : ↥(altMat 5),
    (∀ g ∈ F, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B) →
      nd.FD.testBit (D35Chk.codeOfMat (B : Matrix (Fin 5) (Fin 5) (ZMod 2))) = true
  subS : D35Chk.IsSub nd.FS ∧ nd.FS.testBit 0 = true
  subD : D35Chk.IsSub nd.FD ∧ nd.FD.testBit 0 = true
  cand : ∀ x ∈ E, x ∉ F → (∀ y ∈ F, codeOf x ≤ codeOf (x * y)) → nd.M.testBit (codeOf x) = true

private theorem exists_min_code {S : Set ↥(StatedSL 5 (ZMod 2))} (hS : S.Nonempty) :
    ∃ g ∈ S, ∀ y ∈ S, codeOf g ≤ codeOf y := by
  classical
  have h : ∃ n, ∃ x ∈ S, codeOf x = n := ⟨_, hS.some, hS.some_mem, rfl⟩
  obtain ⟨x, hx, hxn⟩ := Nat.find_spec h
  refine ⟨x, hx, fun y hy => ?_⟩
  rw [hxn]
  exact Nat.find_min' h ⟨y, hy, rfl⟩

private theorem corr_root {E : Subgroup ↥(StatedSL 5 (ZMod 2))} (hEU : E ≤ unitri5)
    (hsq : ∀ a ∈ E, a * a = 1) : Corr E ⊥ D35Chk.root where
  reach := Relation.ReflTransGen.refl
  le := bot_le
  card := by
    show Nat.card (⊥ : Subgroup ↥(StatedSL 5 (ZMod 2))) = 2 ^ 0
    rw [Subgroup.card_bot]
    rfl
  fs := fun B _ => by
    show D35Chk.full.testBit _ = true
    rw [testBit_full]
    simpa using codeOfMat_lt _
  fd := fun B _ => by
    show D35Chk.full.testBit _ = true
    rw [testBit_full]
    simpa using codeOfMat_lt _
  subS := isSub_full
  subD := isSub_full
  cand := fun x hxE hxF _ => by
    show D35Chk.invMask.testBit (codeOf x) = true
    rw [D35Chk.testBit_invMask]
    exact ⟨codeOf_lt x, isInv_codeOf (hEU hxE) (hsq x hxE) (by simpa using hxF)⟩

private theorem Corr.step {E F : Subgroup ↥(StatedSL 5 (ZMod 2))} {nd : D35Chk.Node} [Finite E]
    (hEU : E ≤ unitri5) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1)
    (hC : Corr E F nd) (hne : ∃ x ∈ E, x ∉ F) :
    ∃ (F' : Subgroup ↥(StatedSL 5 (ZMod 2))) (nd' : D35Chk.Node), Corr E F' nd' ∧
      Nat.card F < Nat.card F' := by
  classical
  obtain ⟨g, ⟨hgE, hgF⟩, hgmin⟩ := exists_min_code
    (S := {x | x ∈ E ∧ x ∉ F}) (by obtain ⟨x, hx, hxF⟩ := hne; exact ⟨x, hx, hxF⟩)
  have hgU : g ∈ unitri5 := hEU hgE
  have hg2 : g * g = 1 := hsq g hgE
  have hg1 : g ≠ 1 := fun h => hgF (h ▸ F.one_mem)
  have hinv : D35Chk.isInv (codeOf g) = true := isInv_codeOf hgU hg2 hg1
  have hlt : codeOf g < 1024 := codeOf_lt g
  have hcg0 : codeOf g ≠ 0 := fun h => hg1 (eq_one_of_codeOf_eq_zero hgU h)
  have hcoset : ∀ y ∈ F, codeOf g ≤ codeOf (g * y) := by
    intro y hy
    refine hgmin _ ⟨E.mul_mem hgE (hC.le hy), fun h => hgF ?_⟩
    simpa using F.mul_mem h (F.inv_mem hy)
  have hM : nd.M.testBit (codeOf g) = true := hC.cand g hgE hgF hcoset
  obtain ⟨F', hFF', hgF', hF'E, hcard⟩ := exists_ext hC.le hcomm hsq hgE hgF
  have hfx : (D35Chk.look D35Chk.fxTab 1024 (codeOf g)) =
      D35Chk.kerMask (D35Chk.packRows (D35Chk.fixCol (codeOf g))) := D35Chk.look_fxTab hlt hinv
  have hfd : (D35Chk.look D35Chk.fdTab 1024 (codeOf g)) =
      D35Chk.kerMask (D35Chk.packRows (D35Chk.fixColD (codeOf g))) := D35Chk.look_fdTab hlt hinv
  have hcm : (D35Chk.look D35Chk.cmTab 1024 (codeOf g)) =
      D35Chk.kerMask (D35Chk.packRows (D35Chk.commCol (codeOf g))) := D35Chk.look_cmTab hlt hinv
  refine ⟨F', D35Chk.childOf nd (codeOf g), ⟨?_, hF'E, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Relation.ReflTransGen.tail hC.reach ⟨codeOf g, hM, rfl⟩
  · rw [hcard, hC.card]
    show 2 * 2 ^ nd.m = 2 ^ (nd.m + 1)
    rw [pow_succ]
    ring
  · intro B hB
    have h1 := hC.fs B (fun y hy => hB y (hFF' hy))
    have h2 := testBit_fixCol hgU (hB g hgF')
    rw [← hfx] at h2
    show (Nat.land nd.FS (D35Chk.look D35Chk.fxTab 1024 (codeOf g))).testBit _ = true
    rw [Nat.land_eq, Nat.testBit_and, h1, h2]
    rfl
  · intro B hB
    have h1 := hC.fd B (fun y hy => hB y (hFF' hy))
    have h2 := testBit_fixColD hgU hg2 (hB g hgF')
    rw [← hfd] at h2
    show (Nat.land nd.FD (D35Chk.look D35Chk.fdTab 1024 (codeOf g))).testBit _ = true
    rw [Nat.land_eq, Nat.testBit_and, h1, h2]
    rfl
  · have hs : D35Chk.IsSub (D35Chk.look D35Chk.fxTab 1024 (codeOf g)) ∧
        (D35Chk.look D35Chk.fxTab 1024 (codeOf g)).testBit 0 = true := by
      rw [hfx]
      exact D35Chk.isSub_kerMask _
    refine ⟨isSub_land hC.subS.1 hs.1, ?_⟩
    show (Nat.land nd.FS (D35Chk.look D35Chk.fxTab 1024 (codeOf g))).testBit 0 = true
    rw [Nat.land_eq, Nat.testBit_and, hC.subS.2, hs.2]
    rfl
  · have hs : D35Chk.IsSub (D35Chk.look D35Chk.fdTab 1024 (codeOf g)) ∧
        (D35Chk.look D35Chk.fdTab 1024 (codeOf g)).testBit 0 = true := by
      rw [hfd]
      exact D35Chk.isSub_kerMask _
    refine ⟨isSub_land hC.subD.1 hs.1, ?_⟩
    show (Nat.land nd.FD (D35Chk.look D35Chk.fdTab 1024 (codeOf g))).testBit 0 = true
    rw [Nat.land_eq, Nat.testBit_and, hC.subD.2, hs.2]
    rfl
  · intro x hxE hxF' hmin'
    have hxF : x ∉ F := fun h => hxF' (hFF' h)
    have hxU : x ∈ unitri5 := hEU hxE
    have h1 : codeOf g < codeOf x := by
      rcases (hgmin x ⟨hxE, hxF⟩).lt_or_eq with h | h
      · exact h
      · exact absurd (codeOf_inj hgU hxU h) (fun hgx => hxF' (hgx ▸ hgF'))
    have h2 : nd.M.testBit (codeOf x) = true :=
      hC.cand x hxE hxF (fun y hy => hmin' y (hFF' hy))
    have h3 : (D35Chk.look D35Chk.cmTab 1024 (codeOf g)).testBit (codeOf x) = true := by
      rw [hcm]
      exact testBit_commCol hgU hxU (hcomm g hgE x hxE)
    have h4 : (D35Chk.look D35Chk.nbTab 1024 (D35Chk.topBit (codeOf g))).testBit (codeOf x) = true := by
      rw [D35Chk.topBit_eq_log2 (Nat.pos_of_ne_zero hcg0)
        (lt_of_lt_of_le hlt (by decide : 1024 ≤ 2 ^ 1024))]
      have hlog : Nat.log2 (codeOf g) < 10 := (Nat.log2_lt hcg0).2 hlt
      rw [D35Chk.testBit_look_nbTab hlog]
      refine ⟨codeOf_lt x, ?_⟩
      by_contra hbit
      have hbit' : (codeOf x).testBit (Nat.log2 (codeOf g)) = true := by simpa using hbit
      exact absurd (hmin' g hgF') (not_le.2 (codeOf_mul_lt hxU hgU hg1 hbit'))
    show (Nat.land (Nat.land (Nat.shiftLeft (Nat.shiftRight nd.M (Nat.add (codeOf g) 1))
      (Nat.add (codeOf g) 1)) (D35Chk.look D35Chk.cmTab 1024 (codeOf g)))
      (D35Chk.look D35Chk.nbTab 1024 (D35Chk.topBit (codeOf g)))).testBit (codeOf x) = true
    have e : codeOf g + 1 + (codeOf x - (codeOf g + 1)) = codeOf x := by omega
    simp only [Nat.land_eq, Nat.shiftLeft_eq', Nat.shiftRight_eq', Nat.add_eq, Nat.testBit_and,
      Nat.testBit_shiftLeft, Nat.testBit_shiftRight, e, h2, h3, h4, Bool.and_true]
    simpa using h1
  · rw [hcard]
    have : 0 < Nat.card F := Nat.card_pos
    omega

private theorem exists_corr_top {E : Subgroup ↥(StatedSL 5 (ZMod 2))} [Finite E] (hEU : E ≤ unitri5)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1) :
    ∀ (n : ℕ) (F : Subgroup ↥(StatedSL 5 (ZMod 2))) (nd : D35Chk.Node),
      Nat.card E ≤ Nat.card F + n → Corr E F nd → ∃ nd', Corr E E nd' := by
  intro n
  induction n with
  | zero =>
    intro F nd hle hC
    obtain rfl : F = E := Subgroup.eq_of_le_of_card_ge hC.le (by omega)
    exact ⟨nd, hC⟩
  | succ n ih =>
    intro F nd hle hC
    by_cases hEF : ∃ x ∈ E, x ∉ F
    · obtain ⟨F', nd', hC', hlt⟩ := Corr.step hEU hcomm hsq hC hEF
      exact ih F' nd' (by omega) hC'
    · obtain rfl : F = E := le_antisymm hC.le (fun x hx => by
        by_contra hx'
        exact hEF ⟨x, hx, hx'⟩)
      exact ⟨nd, hC⟩

theorem d35InspExtSqU_of_chk (h : D35Chk.run = true) : D35InspExtSqU := by
  intro E hEU hEne hcomm hsq ⟨hS, hD⟩
  have : Finite ↥(StatedSL 5 (ZMod 2)) := inferInstance
  have : Finite E := inferInstance
  obtain ⟨nd, hnd⟩ := exists_corr_top hEU hcomm hsq (Nat.card E) ⊥ D35Chk.root
    (by omega) (corr_root hEU hsq)
  have hok := D35Chk.run_sound h nd hnd.reach
  have hm : nd.m ≠ 0 := by
    intro h0
    apply hEne
    apply Subgroup.eq_bot_of_card_eq
    rw [hnd.card, h0]
    rfl
  have hinj : ∀ {P : ↥(altMat 5) → Prop}, Function.Injective
      (fun B : {B : ↥(altMat 5) // P B} => D35Chk.codeOfMat (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2))) := by
    intro P B C hBC
    apply Subtype.ext
    apply Subtype.ext
    have h1 := bm_altSum_codeOfMat B.1.2
    have h2 := bm_altSum_codeOfMat C.1.2
    simp only at hBC
    rw [← h1, ← h2, hBC]
  have hcS : Nat.card {B : ↥(altMat 5) //
      ∀ g ∈ E, mat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (mat g)ᵀ = B} ≤
        2 ^ D35Chk.pivotDim nd.FS :=
    card_le_pivot hnd.subS.1 hnd.subS.2 _ hinj (fun B => hnd.fs B.1 B.2)
  have hcD : Nat.card {B : ↥(altMat 5) //
      ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B} ≤
        2 ^ D35Chk.pivotDim nd.FD :=
    card_le_pivot hnd.subD.1 hnd.subD.2 _ hinj (fun B => hnd.fd B.1 B.2)
  have h1 : 10 ≤ nd.m + D35Chk.pivotDim nd.FS := by
    by_contra hlt
    have hlt := Nat.lt_of_not_ge hlt
    have : Nat.card E * Nat.card {B : ↥(altMat 5) //
        ∀ g ∈ E, mat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (mat g)ᵀ = B} < 2 ^ 10 :=
      calc _ ≤ 2 ^ nd.m * 2 ^ D35Chk.pivotDim nd.FS := Nat.mul_le_mul hnd.card.le hcS
        _ = 2 ^ (nd.m + D35Chk.pivotDim nd.FS) := (pow_add _ _ _).symm
        _ < 2 ^ 10 := Nat.pow_lt_pow_right Nat.one_lt_two hlt
    omega
  have h2 : 10 ≤ nd.m + D35Chk.pivotDim nd.FD := by
    by_contra hlt
    have hlt := Nat.lt_of_not_ge hlt
    have : Nat.card E * Nat.card {B : ↥(altMat 5) //
        ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B} < 2 ^ 10 :=
      calc _ ≤ 2 ^ nd.m * 2 ^ D35Chk.pivotDim nd.FD := Nat.mul_le_mul hnd.card.le hcD
        _ = 2 ^ (nd.m + D35Chk.pivotDim nd.FD) := (pow_add _ _ _).symm
        _ < 2 ^ 10 := Nat.pow_lt_pow_right Nat.one_lt_two hlt
    omega
  unfold D35Chk.nodeOK at hok
  have hb : Nat.beq nd.m 0 = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hm (Nat.eq_of_beq_eq_true hb)
  have hb1 : Nat.ble 10 (Nat.add nd.m (D35Chk.pivotDim nd.FS)) = true := by simpa [Nat.ble_eq] using h1
  have hb2 : Nat.ble 10 (Nat.add nd.m (D35Chk.pivotDim nd.FD)) = true := by simpa [Nat.ble_eq] using h2
  rw [hb, hb1, hb2] at hok
  exact Bool.noConfusion hok

theorem d35InspUniq_of_chk (h8 : D35InspUniq8) (h : D35Chk.run = true) : D35InspUniq :=
  d35InspUniq_of_U h8 (d35InspExtSqU_of_chk h)

end CFSG.Quasithin
