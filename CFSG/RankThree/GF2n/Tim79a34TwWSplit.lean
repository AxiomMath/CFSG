module

public import CFSG.RankThree.GF2n.Tim79a34TwDefs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

theorem twistedWSplit_exists_mul_eq_of_mem_sup {G : Type} [Group G] {S T : Subgroup G}
    (hcomm : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a) {x : G} (hx : x ∈ S ⊔ T) :
    ∃ a ∈ S, ∃ b ∈ T, a * b = x := by
  let K : Subgroup G :=
    { carrier := {x | ∃ a ∈ S, ∃ b ∈ T, a * b = x}
      one_mem' := ⟨1, S.one_mem, 1, T.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, S.mul_mem ha₁ ha₂, b₁ * b₂, T.mul_mem hb₁ hb₂, ?_⟩
        calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
          _ = a₁ * (b₁ * a₂) * b₂ := by rw [hcomm a₂ ha₂ b₁ hb₁]
          _ = a₁ * b₁ * (a₂ * b₂) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, S.inv_mem ha, b⁻¹, T.inv_mem hb, ?_⟩
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
          _ = (a * b)⁻¹ := by rw [hcomm a ha b hb] }
  have hK : S ⊔ T ≤ K :=
    sup_le (fun a ha => ⟨a, ha, 1, T.one_mem, mul_one a⟩)
      (fun b hb => ⟨1, S.one_mem, b, hb, one_mul b⟩)
  exact hK hx

theorem twistedWSplit_card_eq_mul {G : Type} [Group G] {W S T : Subgroup G}
    (hS : S ≤ W) (hT : T ≤ W) (hcomm : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a)
    (hsup : S ⊔ T = W) (hinf : S ⊓ T = ⊥) :
    Nat.card ↥W = Nat.card ↥S * Nat.card ↥T := by
  let f : ↥S × ↥T → ↥W := fun p => ⟨p.1.1 * p.2.1, W.mul_mem (hS p.1.2) (hT p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      have h' : a * b = a' * b' := congrArg Subtype.val h
      have e : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h']
          _ = b' * b⁻¹ := by group
      have hmem : a'⁻¹ * a ∈ S ⊓ T :=
        Subgroup.mem_inf.mpr ⟨S.mul_mem (S.inv_mem ha') ha, by
          rw [e]; exact T.mul_mem hb' (T.inv_mem hb)⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      have hB : b' * b⁻¹ = 1 := e.symm.trans hmem
      have hA : a' = a := inv_mul_eq_one.mp hmem
      have hB' : b' = b := mul_inv_eq_one.mp hB
      subst hA hB'
      rfl
    · rintro ⟨x, hx⟩
      have hx' : x ∈ S ⊔ T := by rw [hsup]; exact hx
      obtain ⟨a, ha, b, hb, hab⟩ := twistedWSplit_exists_mul_eq_of_mem_sup hcomm hx'
      exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, Subtype.ext hab⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem twistedWSplit_holds : TwistedWSplitStatement := by
  intro G _ _ M V Q P H hs hsplit
  have hc : MinCex M V Q P H := hs.mc.toMinCex
  obtain ⟨g, hg, u, hu, w, hw, hn⟩ := MinCex.exists_noncomm_conj hc hs.data
  obtain ⟨-, hsup, hinf⟩ := hsplit.1 g hg ⟨u, hu, w, hw, hn⟩
  have hgH : g ∈ H := xOf_le_H hc.V_le_H hg
  have h1 : Nat.card ↥(wOf V H) =
      Nat.card ↥(P ⊓ wOf V H) * Nat.card ↥(conjSubgroup g V ⊓ wOf V H) :=
    twistedWSplit_card_eq_mul inf_le_right inf_le_right
      (fun a ha b hb => hc.wOf_isElemAbelian.comm (Subgroup.mem_inf.mp ha).2
        (Subgroup.mem_inf.mp hb).2) hsup hinf
  have hW : conjSubgroup g (wOf V H) = wOf V H :=
    mem_normalizer_iff_conjSubgroup_eq.mp (H_le_normalizer_wOf V H hgH)
  have hconj : conjSubgroup g (V ⊓ wOf V H) = conjSubgroup g V ⊓ wOf V H := by
    unfold conjSubgroup at hW ⊢
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hW]
  have h2 : Nat.card ↥(conjSubgroup g V ⊓ wOf V H) = Nat.card ↥(V ⊓ wOf V H) := by
    rw [← hconj]
    exact CFSG.CGT.Timmesfeld75.card_conjSubgroup g (V ⊓ wOf V H)
  rw [h1, h2]

end CFSG.RankThree.GF2n.Tim79a
