module

public import CFSG.Quasithin.H13.L32A753h
public import CFSG.Quasithin.Background.SmithB42U33

public section

namespace CFSG.Quasithin.H13.M3330

open CFSG.Open CFSG.Quasithin Orbit

variable {V : Type} [CommGroup V]

theorem exists_coord
    {X K : Subgroup (MulAut V)}
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V))) (hnat : G2NaturalDerived K ⊤ ⊥ 1) :
    ∃ e : V ≃* ModQ,
      K.map (MulAut.congr e).toMonoidHom = (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) ∧
        ∀ x ∈ X, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range := by
  obtain ⟨e, hKe⟩ := B42U33.exists_equiv_of_g2NaturalDerived hnat
  refine ⟨e, hKe, fun x hx => ?_⟩
  set φ := (MulAut.congr e).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  refine normalizer_two_Q _ fun h => ?_
  obtain ⟨h', rfl⟩ := (MulAut.congr e).surjective h
  rw [← hKe, ← map_inv, ← map_mul, ← map_mul]
  change φ h' ∈ K.map φ ↔ φ (_ * h' * _) ∈ K.map φ
  rw [Subgroup.mem_map_iff_mem hφinj, Subgroup.mem_map_iff_mem hφinj]
  exact (Subgroup.mem_normalizer_iff.mp (hXN hx) h')

theorem card_fixV_le_eight
    {e : V ≃* ModQ}
    {X K : Subgroup (MulAut V)}
    (hKe : K.map (MulAut.congr e).toMonoidHom = (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)))
    (hX : ∀ x ∈ X, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range) {b : MulAut V} (hbX : b ∈ X)
    (hbK : b ∉ K) (hb2 : b ^ 2 = 1) : Nat.card (fixV (Subgroup.zpowers b)) ≤ 8 := by
  obtain ⟨γ, hγ⟩ := hX b hbX
  have hγD : γ ∉ g2Derived (ZMod 2) := by
    intro hγ'
    have h1 : MulAut.congr e b ∈ K.map (MulAut.congr e).toMonoidHom := by
      rw [hKe, ← hγ]
      exact ⟨γ, hγ', rfl⟩
    obtain ⟨κ, hκ, hκe⟩ := h1
    exact hbK ((MulAut.congr e).injective hκe ▸ hκ)
  have hγ2 : γ ^ 2 = 1 :=
    g2QAct_injective (by rw [map_pow, hγ, ← map_pow, hb2, map_one, map_one])
  have hcard := L32A.M753.card_fixV_le_eight hγD hγ2
  have hzp : (Subgroup.zpowers γ).map (g2QAct (ZMod 2)) =
      (Subgroup.zpowers b).map (MulAut.congr e).toMonoidHom := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, hγ]
    rfl
  rwa [hzp, B1Red.fixV_map_congr',
    Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] at hcard

theorem normal_sE8 : ∀ e < 8,
    (∀ j < 64, ∀ i ∈ sE8.getD e [], ∃ k ∈ sE8.getD e [], mmul (sM j) (sM i) = mmul (sM k) (sM j)) →
    (o0Codes.filter fun c => !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c).length =
      8 → e = 2 := by
  decide +kernel

theorem eq_of_idx {F F' : Subgroup ↥(quasithinG2 (ZMod 2))} (hF : F ≤ sSubG) (hF' : F' ≤ sSubG)
    (h : ∀ l, l ∈ idx F ↔ l ∈ idx F') : F = F' := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 (hF hx)
    exact (mem_idx.1 ((h i).1 (mem_idx.2 ⟨hi, hx⟩))).2
  · intro hx
    obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 (hF' hx)
    exact (mem_idx.1 ((h i).2 (mem_idx.2 ⟨hi, hx⟩))).2

theorem idx_eq_of_normal {F : Subgroup ↥(quasithinG2 (ZMod 2))} (hF : F ≤ sSubG)
    (hF2 : ∀ b ∈ F, b ^ 2 = 1) (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (h8 : (idx F).card = 8)
    (hN : ∀ s ∈ sSubG, ∀ x ∈ F, s * x * s⁻¹ ∈ F)
    (hfix : Nat.card (fixV (F.map (g2QAct (ZMod 2)))) = 8) :
    ∀ l, l ∈ idx F ↔ l ∈ sE8.getD 2 [] := by
  classical
  obtain ⟨e, he, hiff⟩ := idx_eq_sE8 hF hF2 hFc h8.ge
  have hN' : ∀ j < 64, ∀ i ∈ sE8.getD e [], ∃ k ∈ sE8.getD e [],
      mmul (sM j) (sM i) = mmul (sM k) (sM j) := by
    intro j hj i hi
    have hiF := (mem_idx.1 ((hiff i).2 hi))
    have hjS : sEltG j ∈ sSubG := mem_sSubG.2 ⟨j, hj, rfl⟩
    have hc := hN _ hjS _ hiF.2
    obtain ⟨k, hk, hke⟩ := mem_sSubG.1 (hF hc)
    have hkF : k ∈ idx F := mem_idx.2 ⟨hk, hke ▸ hc⟩
    refine ⟨k, (hiff k).1 hkF, ?_⟩
    have e1 : sElt j * sElt i = sElt k * sElt j := by
      have := congrArg Subtype.val hke
      change sElt k = sElt j * sElt i * (sElt j)⁻¹ at this
      rw [this, inv_mul_cancel_right]
    rw [← matCode_mul_sElt hj hiF.1, e1, matCode_mul_sElt hk hj]
  let P : ℕ → Bool := fun c => decide (∀ i ∈ idx F, fixQB (sM i) c = true)
  have hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx F, fixQB (sM i) c.1 = true := fun c => by
    simp [P]
  have hC := card_fixV_Q hF P hP
  have hfilter : (o0Codes.filter fun c => !c.testBit 0 && P c) =
      o0Codes.filter fun c => !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c := by
    refine List.filter_congr fun c _ => ?_
    congr 1
    simp only [P]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, List.all_eq_true]
    exact forall_congr' fun i => imp_congr (hiff i) Iff.rfl
  rw [hfix, hfilter] at hC
  have he2 := normal_sE8 e he hN' hC.symm
  subst he2
  exact hiff

end CFSG.Quasithin.H13.M3330
