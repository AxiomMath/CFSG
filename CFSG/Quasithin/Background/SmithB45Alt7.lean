module

public import CFSG.Quasithin.Background.SmithB45Alt7Class
public import CFSG.Quasithin.Background.SmithB45Alt7Row
public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57TranspMain

public section

namespace CFSG.Quasithin

namespace B45Alt7

open Equiv Equiv.Perm CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem card_le_of_cubic (C : Bridge.Alt57.Ctx G L 7)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) (ι : ↥L ≃* A7) (e : ↥G →* Perm (Fin 7))
    (hinj : Function.Injective e)
    (hL : ∀ l : ↥L, e ⟨(l : MulAut V), C.le_G l.2⟩ = (ι l : Perm (Fin 7)))
    {A : Subgroup (MulAut V)} (hA : IsA2 G A) (hidx : (fixV A).index ≤ Nat.card A ^ 2) :
    Nat.card V ≤ 2 ^ 12 := by
  obtain ⟨hAG, hA1, hAe⟩ := hA
  set A' : Subgroup ↥G := A.subgroupOf G with hA'
  set B : Subgroup (Perm (Fin 7)) := A'.map e with hB
  have hB1 : B ≠ ⊥ := by
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
    have ha' : (⟨(a : MulAut V), hAG a.2⟩ : ↥G) ∈ A' := Subgroup.mem_subgroupOf.2 a.2
    have hne : e ⟨(a : MulAut V), hAG a.2⟩ ≠ 1 := by
      intro h
      apply ha1
      have h3 : (⟨(a : MulAut V), hAG a.2⟩ : ↥G) = 1 := hinj (by rw [h, map_one])
      have h4 : (a : MulAut V) = 1 := congrArg Subtype.val h3
      exact Subtype.ext h4
    intro h
    have hmem : e ⟨(a : MulAut V), hAG a.2⟩ ∈ B := Subgroup.mem_map.2 ⟨_, ha', rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hne hmem
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hAe.1 _ (Subgroup.mem_subgroupOf.1 ha') _ (Subgroup.mem_subgroupOf.1 hb')
  have hB2 : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_mul]
    have : a' * a' = 1 := by
      apply Subtype.ext
      have := hAe.2 _ (Subgroup.mem_subgroupOf.1 ha')
      simpa [pow_two] using this
    rw [this, map_one]
  have hBcard : Nat.card B = Nat.card A := by
    rw [hB, Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv
  obtain ⟨r, f, hf, hbound, hcl⟩ := B42A57.gen7 hB1 hBc hB2
  have hle := B42Alt7.card_le_index_pow C hirr A ι e hinj hL f hf hcl
  calc Nat.card V ≤ (fixV A).index ^ r := hle
    _ ≤ (Nat.card A ^ 2) ^ r := Nat.pow_le_pow_left hidx r
    _ = (Nat.card B ^ r) ^ 2 := by rw [hBcard, ← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (2 ^ 6) ^ 2 := Nat.pow_le_pow_left hbound 2
    _ = 2 ^ 12 := by norm_num

end B45Alt7

open B45Alt7 in
theorem asB45Alt7_holds : AsB45Alt7 := by
  intro V _ _ hV G L hHyp hP h1 h2
  classical
  have C := B42Alt7.ctx_of_b4Hyp hHyp hP
  have hirrS : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤ := hHyp.2.2.2
  obtain ⟨ι, e, hinj, hL, hconj⟩ := QuasithinUnique.B42A57.exists_embedding C
  obtain ⟨A, hA, -, hidx⟩ := B45Alt.exists_cubic_of_qhatOf_le_two hV h2
  have hcard := card_le_of_cubic C hirrS ι e hinj hL hA hidx
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h3 : Additive.toMul (2 • x) = 1 := by
      rw [toMul_nsmul]
      exact hV _
    exact toMul_eq_one.1 h3
  have hirr := HatA6.irr_of_b4Hyp hHyp
  have hfix := HatA6.fixV_eq_bot_of_b4Hyp hHyp
  rcases classify ι hirr hfix hcard with ⟨β, hβ⟩ | ⟨E, hEL, hEe, hE4, hEV⟩
  · have hGL : G ≤ L := by
      by_contra hne
      exact absurd h1 (not_lt.2 (qhatOf_le_one_of_not_le hV C ι e hinj hL hconj β hβ hne))
    have hGeq : G = L := le_antisymm hGL C.le_G
    have hq := kq_eq_of_coreEquiv hβ hV
    refine Or.inl (Or.inl ⟨?_, ?_, ?_⟩)
    · exact QuasithinUnique.B42A57.realizesMod_of_equivariant (FFModel.altDn_isActionModel 7)
        QuasithinUnique.B42A57.altDn7_ker L ι.symm.toMonoidHom ι.symm.surjective β
        fun γ s => hβ γ s
    · rw [hGeq]
      exact hq.1
    · rw [hGeq]
      exact hq.2
  · exfalso
    exact absurd h1 (not_lt.2 (B45Alt.qhatOf_le_one_of_four hV (hEL.trans C.le_G) hEe hE4 hEV))

end CFSG.Quasithin
