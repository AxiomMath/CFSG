module

public import CFSG.Quasithin.Background.FLc6Grp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open

variable {G : Type} [Group G]

namespace P0Setup

set_option synthInstance.maxSize 2000 in
theorem blk2_sq_mem (B β β' : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (hB : B = blk2T2 ∨ B = blk2T2 * blk2T2) (h : β * β' = 1) :
    β * β = 1 ∨ β * β * B = 1 ∨ β * β * (B * B) = 1 := by
  revert B β β'
  decide

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W)

structure HasL2 (l : ↥L) : Prop where
  odd : Odd (orderOf (l : G))
  mem : D.α l ∈ Qn n 2
  blk_eq : ∀ {P Q : Fin n}, P.val + 1 = 2 → Q.val = 2 →
    (blk P Q (D.α l) = blk2T2 ∨ blk P Q (D.α l) = blk2T2 * blk2T2)

include D

theorem exists_hasL2 [Finite G] (hn : n = 4 ∨ n = 5) : ∃ l : ↥L, D.HasL2 l := by
  have h3 : 3 ≤ n := by omega
  have h2n : 2 + 1 < n := by omega
  obtain ⟨-, hT2, -⟩ := node_compute hn h3
  obtain ⟨l, hodd, hl⟩ := D.exists_odd_lift hT2
  have hα : D.α l ∈ Qn n 2 := by
    rcases hl with h | h
    · rw [h]; exact T2_mem_Qn h3
    · rw [h]; exact (Qn n 2).mul_mem (T2_mem_Qn h3) (T2_mem_Qn h3)
  refine ⟨l, hodd, hα, fun {P Q} hP hQ => ?_⟩
  have e : blk P Q (D.α l) = blk (ix 1 (by omega) : Fin n) (ix 2 (by omega) : Fin n) (D.α l) := by
    have h1 : P = ix 1 (by omega) := Fin.ext (by show P.val = 1; omega)
    have h2 : Q = ix 2 (by omega) := Fin.ext (by show Q.val = 2; omega)
    rw [h1, h2]
  rw [e]
  have hP0 : (ix 1 (by omega) : Fin n).val + 1 = 2 := rfl
  have hQ0 : (ix 2 (by omega) : Fin n).val = 2 := rfl
  rcases hl with h | h
  · left
    rw [h]
    exact blk_T2 hn h3
  · right
    rw [h, blk_mul_Qn (by norm_num) h2n hP0 hQ0 (T2_mem_Qn h3) (T2_mem_Qn h3), blk_T2 hn h3]

theorem sq_mul_pow_mem_qNode [Finite G] (hn : n = 4 ∨ n = 5) {l₂ : ↥L} (hl : D.HasL2 l₂) {x : G}
    (hx : x ∈ parab (L ⊔ S) n W 2) : ∃ j : ℕ, x ^ 2 * (l₂ : G) ^ j ∈ qNode L S n W := by
  have h2n : 2 + 1 < n := by omega
  have hP : (ix 1 (by omega) : Fin n).val + 1 = 2 := rfl
  have hQ : (ix 2 (by omega) : Fin n).val = 2 := rfl
  set P : Fin n := ix 1 (by omega) with hPdef
  set Q : Fin n := ix 2 (by omega) with hQdef
  have hne : P ≠ Q := fun h => by rw [h] at hP; omega
  obtain ⟨l, c, hc, hxl⟩ := D.decomp (mem_parab.1 hx).1
  have hd : Dec L S UL x l := ⟨c, hc, hxl⟩
  have hα : D.α l ∈ Qn n 2 := D.alpha_mem_Qn hx hd
  have hββ : blk P Q (D.α l) * blk P Q (D.α l)⁻¹ = 1 := by
    rw [← blk_mul_Qn (by norm_num) h2n hP hQ hα ((Qn n 2).inv_mem hα), mul_inv_cancel]
    exact blk_one hne
  have hB := hl.blk_eq hP hQ
  have hl₂P : (l₂ : G) ∈ parab (L ⊔ S) n W 2 := D.mem_parab_of_alpha l₂ hl.mem
  have hkey : ∀ j : ℕ, blk P Q (D.α (l ^ 2 * l₂ ^ j)) =
      (blk P Q (D.α l)) ^ 2 * (blk P Q (D.α l₂)) ^ j := fun j => by
    rw [map_mul, map_pow, map_pow,
      blk_mul_Qn (by norm_num) h2n hP hQ ((Qn n 2).pow_mem hα 2) ((Qn n 2).pow_mem hl.mem j),
      blk_pow_Qn (by norm_num) h2n hP hQ hα, blk_pow_Qn (by norm_num) h2n hP hQ hl.mem]
  have hmem : ∀ j : ℕ, blk P Q (D.α (l ^ 2 * l₂ ^ j)) = 1 → x ^ 2 * (l₂ : G) ^ j ∈ qNode L S n W :=
    fun j hj => by
      have hdg : Dec L S UL (x ^ 2 * (l₂ : G) ^ j) (l ^ 2 * l₂ ^ j) :=
        D.dec_mul (D.dec_pow hd 2) (D.dec_pow (dec_self l₂) j)
      have hgP : x ^ 2 * (l₂ : G) ^ j ∈ parab (L ⊔ S) n W 2 :=
        (parab (L ⊔ S) n W 2).mul_mem ((parab (L ⊔ S) n W 2).pow_mem hx 2)
          ((parab (L ⊔ S) n W 2).pow_mem hl₂P j)
      exact D.Ebk_le_pCoreOf (i := 2) (by norm_num) h2n hP hQ
        ((D.mem_Ebk (i := 2) (by norm_num) h2n hP hQ).2 ⟨hgP, _, hdg, hj⟩)
  rcases blk2_sq_mem _ _ _ hB hββ with h | h | h
  · refine ⟨0, hmem 0 ?_⟩
    rw [hkey, pow_zero, mul_one, pow_two]
    exact h
  · refine ⟨1, hmem 1 ?_⟩
    rw [hkey, pow_one, pow_two]
    exact h
  · refine ⟨2, hmem 2 ?_⟩
    rw [hkey, pow_two, pow_two]
    exact h

theorem yNode_le_sup_zpowers [Finite G] (hn : n = 4 ∨ n = 5) {l₂ : ↥L} (hl : D.HasL2 l₂) :
    yNode L S n W 2 ≤ qNode L S n W ⊔ Subgroup.zpowers (l₂ : G) := by
  refine oTwoUpper_le_of_pow_mem fun x hx => ⟨1, ?_⟩
  obtain ⟨j, hj⟩ := D.sq_mul_pow_mem_qNode hn hl hx
  have e : x ^ 2 ^ 1 = (x ^ 2 * (l₂ : G) ^ j) * ((l₂ : G) ^ j)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hj)
    (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j)))

theorem inf_centralizer_UL_le_qNode [Finite G] (hn : n = 4 ∨ n = 5) {x : G}
    (hx : x ∈ parab (L ⊔ S) n W 2) (hc : x ∈ Subgroup.centralizer (UL : Set G)) :
    x ∈ qNode L S n W := by
  have h2n : 2 + 1 < n := by omega
  have hP : (ix 1 (by omega) : Fin n).val + 1 = 2 := rfl
  have hQ : (ix 2 (by omega) : Fin n).val = 2 := rfl
  set P : Fin n := ix 1 (by omega) with hPdef
  set Q : Fin n := ix 2 (by omega) with hQdef
  have hne : P ≠ Q := fun h => by rw [h] at hP; omega
  obtain ⟨l, c, hc', hxl⟩ := D.decomp (mem_parab.1 hx).1
  have hlc : (l : G) ∈ Subgroup.centralizer (UL : Set G) := by
    have e : (l : G) = x * c⁻¹ := by rw [hxl]; group
    rw [e]
    exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hc'.1)
  have hb : blk P Q (D.α l) = 1 := by
    rw [D.alpha_eq_one_of_mem_centralizer hlc]
    exact blk_one hne
  exact D.Ebk_le_pCoreOf (i := 2) (by norm_num) h2n hP hQ
    ((D.mem_Ebk (i := 2) (by norm_num) h2n hP hQ).2 ⟨hx, l, ⟨c, hc', hxl⟩, hb⟩)

theorem pCoreOf_le_qNode_of_mem [Finite G] (hn : n = 4 ∨ n = 5) {C : Subgroup G}
    (hCH : C ≤ gNode L S n W ⊓ Subgroup.normalizer (W 1 : Set G)) {l₂ : ↥L} (hl : D.HasL2 l₂)
    (hlC : (l₂ : G) ∈ C) : pCoreOf 2 C ≤ qNode L S n W := by
  have h2n : 2 + 1 < n := by omega
  have hαl₂ : D.α l₂ ∈ Qn n 2 := hl.mem
  have hP : (ix 1 (by omega) : Fin n).val + 1 = 2 := rfl
  have hQ : (ix 2 (by omega) : Fin n).val = 2 := rfl
  set P : Fin n := ix 1 (by omega) with hPdef
  set Q : Fin n := ix 2 (by omega) with hQdef
  have hne : P ≠ Q := fun h => by rw [h] at hP; omega
  have ht := hl.blk_eq hP hQ
  intro b hb
  have hbH := pCoreOf_le 2 _ hb
  have hbP : b ∈ parab (L ⊔ S) n W 2 := D.inf_le_parab (hCH hbH)
  obtain ⟨lb, cb, hcb, hbl⟩ := D.decomp (mem_parab.1 hbP).1
  have hdb : Dec L S UL b lb := ⟨cb, hcb, hbl⟩
  have hdl₂ : Dec L S UL (l₂ : G) l₂ := dec_self l₂
  have hb' : (l₂ : G) * b * (l₂ : G)⁻¹ ∈ pCoreOf 2 C :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hlC) b).1 hb
  have hx : b * ((l₂ : G) * b * (l₂ : G)⁻¹) ∈ pCoreOf 2 C := Subgroup.mul_mem _ hb hb'
  have hg2 := pCoreOf_isPGroup 2 C
  have hbP2 : ∃ k : ℕ, b ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hg2 ⟨b, hb⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxP2 : ∃ k : ℕ, (b * ((l₂ : G) * b * (l₂ : G)⁻¹)) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hg2 ⟨_, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxP : b * ((l₂ : G) * b * (l₂ : G)⁻¹) ∈ parab (L ⊔ S) n W 2 :=
    D.inf_le_parab (hCH (pCoreOf_le 2 _ hx))
  have hdconj : Dec L S UL ((l₂ : G) * b * (l₂ : G)⁻¹) (l₂ * lb * l₂⁻¹) :=
    D.dec_mul (D.dec_mul hdl₂ hdb) (D.dec_inv hdl₂)
  have hdx : Dec L S UL (b * ((l₂ : G) * b * (l₂ : G)⁻¹)) (lb * (l₂ * lb * l₂⁻¹)) :=
    D.dec_mul hdb hdconj
  have hm : blk P Q (D.α lb) * blk P Q (D.α lb) = 1 :=
    D.blk_sq_of_two_elt h2n hP hQ hbP hdb hbP2
  have hM := D.blk_sq_of_two_elt h2n hP hQ hxP hdx hxP2
  have hαb : D.α lb ∈ Qn n 2 := D.alpha_mem_Qn hbP hdb
  have hαi : (D.α l₂)⁻¹ ∈ Qn n 2 := (Qn n 2).inv_mem hαl₂
  have hblkM : blk P Q (D.α (lb * (l₂ * lb * l₂⁻¹))) =
      blk P Q (D.α lb) * (blk P Q (D.α l₂) * blk P Q (D.α lb) * blk P Q (D.α l₂)⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv,
      blk_mul_Qn (by norm_num) h2n hP hQ hαb ((Qn n 2).mul_mem ((Qn n 2).mul_mem hαl₂ hαb) hαi),
      blk_mul_Qn (by norm_num) h2n hP hQ ((Qn n 2).mul_mem hαl₂ hαb) hαi,
      blk_mul_Qn (by norm_num) h2n hP hQ hαl₂ hαb]
  have htt : blk P Q (D.α l₂)⁻¹ * blk P Q (D.α l₂) = 1 := by
    rw [← blk_mul_Qn (by norm_num) h2n hP hQ hαi hαl₂, inv_mul_cancel]
    exact blk_one hne
  rw [hblkM] at hM
  have hm1 : blk P Q (D.α lb) = 1 :=
    blk2_key (blk P Q (D.α l₂)) (blk P Q (D.α l₂)⁻¹) (blk P Q (D.α lb)) ht htt hm hM
  have hbE : b ∈ D.Ebk (i := 2) (by norm_num) h2n (P := P) (Q := Q) hP hQ :=
    (D.mem_Ebk (i := 2) (by norm_num) h2n hP hQ).2 ⟨hbP, lb, hdb, hm1⟩
  exact D.Ebk_le_pCoreOf (i := 2) (by norm_num) h2n hP hQ hbE

end P0Setup

end CFSG.Quasithin.FLc
