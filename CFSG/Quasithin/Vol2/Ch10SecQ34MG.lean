module

public import CFSG.Quasithin.Vol2.Ch10SecQ34MF
public import CFSG.Quasithin.Background.FFC4Five

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

namespace C10P34

theorem permMod_mul_self (m : G6.PermMod 5) : m * m = 1 := by
  apply Multiplicative.toAdd.injective
  ext i
  simp only [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem false_of_card_two {F : Subgroup ↥(G6.coreMod 5)} (hF : Nat.card F = 2)
    {m : ↥(G6.coreMod 5)} (hmF : m ∈ F) (hm1 : m ≠ 1)
    (hinv : ∀ c : Perm (Fin 5), c = swap 0 1 * swap 1 2 ∨ c = swap 2 3 * swap 3 4 →
      ∀ n ∈ F, (⟨G6.permAct 5 c n, G6.permAct_mem_coreMod c n.2⟩ : ↥(G6.coreMod 5)) ∈ F) :
    False := by
  have hm2 : m * m = 1 := Subtype.ext (permMod_mul_self (m : G6.PermMod 5))
  have hord : orderOf m = 2 := orderOf_eq_prime (by rw [sq, hm2]) hm1
  have hFz : F = Subgroup.zpowers m := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmF) ?_).symm
    rw [hF, Nat.card_zpowers, hord]
  have hfix : ∀ c : Perm (Fin 5), c = swap 0 1 * swap 1 2 ∨ c = swap 2 3 * swap 3 4 →
      G6.permAct 5 c (m : G6.PermMod 5) = m := by
    intro c hc
    set m' : ↥(G6.coreMod 5) := ⟨G6.permAct 5 c m, G6.permAct_mem_coreMod c m.2⟩ with hm'
    have h1 : m' ∈ Subgroup.zpowers m := hFz ▸ hinv c hc m hmF
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hk' : m ^ k = 1 ∨ m ^ k = m := by
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, zpow_two, hm2, one_zpow]
      · right
        rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_one, zpow_mul, zpow_two, hm2,
          one_zpow, mul_one]
    rcases hk' with h | h
    · exfalso
      apply hm1
      have h2 : m' = 1 := hk ▸ h
      have h3 : G6.permAct 5 c (m : G6.PermMod 5) = 1 := congrArg Subtype.val h2
      exact Subtype.ext ((MulEquiv.map_eq_one_iff _).mp h3)
    · exact congrArg Subtype.val (hk.symm.trans h)
  apply hm1
  have h0 := fixed_alt5 (Multiplicative.toAdd (m : G6.PermMod 5)) m.2
    (fun i => by
      have := congrArg (fun z : G6.PermMod 5 => Multiplicative.toAdd z i) (hfix _ (Or.inl rfl))
      simpa [G6.permAct_apply] using this)
    (fun i => by
      have := congrArg (fun z : G6.PermMod 5 => Multiplicative.toAdd z i) (hfix _ (Or.inr rfl))
      simpa [G6.permAct_apply] using this)
  exact Subtype.ext (Multiplicative.toAdd.injective h0)

theorem exists_core_hom {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {Z : Subgroup V}
    {π : ↥(alternatingGroup (Fin 5)) →* ↥H} (hπ : (FFModel.altDn 5).RealizesVia H ⊤ Z π) :
    ∃ B : V →* ↥(G6.coreMod 5), Function.Surjective B ∧ (∀ w, B w = 1 ↔ w ∈ Z) ∧
      ∀ (γ : ↥(alternatingGroup (Fin 5))) (w : V),
        ((B (((π γ : ↥H) : MulAut V) w) : ↥(G6.coreMod 5)) : G6.PermMod 5) =
          G6.permAct 5 (γ : Perm (Fin 5)) (B w) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.RealizesVia.secMap FFC.altDn_ker_five hπ
  let g : V → ↥(G6.coreMod 5) := fun w =>
    ⟨(((f ⟨w, Subgroup.mem_top w⟩ : ↥(FFModel.altDn 5).sec) : (FFModel.altDn 5).Amb) :
      G6.PermMod 5), (f ⟨w, Subgroup.mem_top w⟩).2⟩
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_ }, ?_, ?_, ?_⟩
  · apply Subtype.ext
    exact congrArg Subtype.val (map_one f)
  · intro a b
    apply Subtype.ext
    exact congrArg Subtype.val (map_mul f ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩)
  · intro m
    obtain ⟨u, hu⟩ := hfs ⟨(m : G6.PermMod 5), m.2⟩
    refine ⟨u, Subtype.ext ?_⟩
    exact congrArg Subtype.val hu
  · intro w
    rw [← hfk ⟨w, Subgroup.mem_top w⟩]
    constructor
    · intro h
      exact Subtype.ext (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext (congrArg Subtype.val h)
  · intro γ w
    exact hfe γ ⟨w, Subgroup.mem_top w⟩ (Subgroup.mem_top _)

end C10P34

end CFSG.Quasithin.Vol2.Ch10.SecB
