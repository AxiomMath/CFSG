module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeDatumDef

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4

theorem fixed_equiv_centralizer {π : Bool} {p f : ℕ} {K : Type} [Field K] {y : GL (Fin 3) K}
    {β' : MulAut (slPi π 3 (p ^ f) K)}
    (hβ' : ∀ s, ((β' s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = y * s * y⁻¹) :
    Nonempty (↥(fixedSub β') ≃* ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y})) := by
  have hmem : ∀ s : slPi π 3 (p ^ f) K, s ∈ fixedSub β' ↔
      (s : GL (Fin 3) K) ∈ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) := by
    intro s
    rw [mem_fixedSub, ← Subtype.coe_inj, hβ' s, Subgroup.mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  let f₁ : fixedSub β' →* ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) :=
    { toFun := fun s => ⟨((s : slPi π 3 (p ^ f) K) : GL (Fin 3) K),
        Subgroup.mem_inf.mpr ⟨(s : slPi π 3 (p ^ f) K).2, (hmem s).mp s.2⟩⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  refine ⟨MulEquiv.ofBijective f₁ ⟨fun a b hab => ?_, ?_⟩⟩
  · have h := congrArg (fun x : ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) =>
      (x : GL (Fin 3) K)) hab
    exact Subtype.ext (Subtype.ext h)
  · rintro ⟨g, hg⟩
    obtain ⟨hgS, hgc⟩ := Subgroup.mem_inf.mp hg
    exact ⟨⟨⟨g, hgS⟩, (hmem ⟨g, hgS⟩).mpr hgc⟩, rfl⟩

theorem exists_cube_one_conj {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) {y : GL (Fin 3) K}
    (hy : ∃ g ∈ glPi π 3 (p ^ f) K, g⁻¹ * y * g = diagTau hτ)
    {β' : MulAut (slPi π 3 (p ^ f) K)}
    (hβ' : ∀ s, ((β' s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = y * s * y⁻¹) :
    ∃ v : slPi π 3 (p ^ f) K, v ^ 3 = 1 ∧ β' = MulAut.conj v := by
  obtain ⟨g, hg, hgy⟩ := hy
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hyeq : y = g * diagTau hτ * g⁻¹ := eq_conj_of_inv_conj hgy
  have hyS : y ∈ slPi π 3 (p ^ f) K := by
    rw [hyeq]
    exact conj_mem_slPi hπ hg (diagTau_mem_slPi hπ hq' hτ)
  have hy3 : y ^ 3 = 1 := by
    rw [hyeq]
    calc (g * diagTau hτ * g⁻¹) ^ 3 = g * diagTau hτ ^ 3 * g⁻¹ := by
          simp only [pow_three]
          group
      _ = 1 := by rw [diagTau_pow_three hτ]; group
  refine ⟨⟨y, hyS⟩, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hy3), ?_⟩
  refine MulEquiv.ext fun s => Subtype.ext ?_
  rw [hβ' s, MulAut.conj_apply]
  rfl

theorem odd_card_of_char_two {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hp : p = 2) {G : Type} [Group G]
    (hG : Nonempty (G ≃* Multiplicative (ZMod (qSubPi π (p ^ f))) ×
      Multiplicative (ZMod (qSubPi π (p ^ f))))) : Odd (Nat.card G) := by
  obtain ⟨e⟩ := hG
  subst hp
  have hf := hK.one_le
  have h2 : 2 ^ f % 2 = 0 := Nat.pow_mod 2 f 2 ▸ (by simp [Nat.pos_iff_ne_zero.mp hf])
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hN : Odd (qSubPi π (2 ^ f)) := by
    cases π
    · change Odd (2 ^ f + 1)
      rw [Nat.odd_iff]
      omega
    · change Odd (2 ^ f - 1)
      rw [Nat.odd_iff]
      omega
  haveI : NeZero (qSubPi π (2 ^ f)) := ⟨hN.pos.ne'⟩
  have hA : Nat.card (Multiplicative (ZMod (qSubPi π (2 ^ f)))) = qSubPi π (2 ^ f) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, hA]
  exact hN.mul hN

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
