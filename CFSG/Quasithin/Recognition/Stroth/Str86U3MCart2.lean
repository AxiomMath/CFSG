module

public import CFSG.Quasithin.Recognition.Stroth.Str86U3MCart

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise commutatorElement Matrix

variable {V : Type} [CommGroup V] [Finite V]

noncomputable section

theorem binaryNaturalSU3_exists_normalizer_mod_fix {k : ℕ} (hk : 2 ≤ k)
    {L : Subgroup (MulAut V)} (hL : BinaryNaturalSU3 L ⊤ ⊥ k)
    {T : Subgroup (MulAut V)} (hTL : T ≤ L) (hT : IsPGroup 2 T)
    (hTc : (2 ^ k) ^ 3 ≤ Nat.card T)
    {u : MulAut V} (huT : u ∈ T) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    (2 ^ k) ^ 2 ≤ (fixV (Subgroup.zpowers u)).index ∧
      ∀ w₁ w₂ : V, u w₁ ≠ w₁ → u w₂ ≠ w₂ →
        ∃ n ∈ L ⊓ Subgroup.normalizer (T : Set (MulAut V)), u (n w₁ * w₂⁻¹) = n w₁ * w₂⁻¹ := by
  obtain ⟨K, hKfield, hKfin, hKcard, π, hπ⟩ := hL
  letI : Field K := hKfield
  letI : Finite K := hKfin
  let Γ : Subgroup (GL (Fin 3) K) := StatedSU 3 (2 ^ k) K
  obtain ⟨e, he⟩ := H.exists_mulEquiv_of_realizesVia (Γ := Γ) hπ
  let e' : MulAut V ≃* MulAut (H.StdMod (Fin 3) K) := MulAut.congr e
  have hLmap : L.map e'.toMonoidHom = H.natImage Γ :=
    H.map_congrHom_eq_natImage Γ hπ.1 e he
  let T' : Subgroup (MulAut (H.StdMod (Fin 3) K)) := T.map e'.toMonoidHom
  let u' : MulAut (H.StdMod (Fin 3) K) := e' u
  have hT'le : T' ≤ H.natImage Γ := by
    rw [← hLmap]
    exact Subgroup.map_mono hTL
  have hT' : IsPGroup 2 T' := hT.map e'.toMonoidHom
  have hcardT' : Nat.card T' = Nat.card T :=
    Subgroup.card_map_of_injective e'.injective
  have hTc' : (2 ^ k) ^ 3 ≤ Nat.card T' := by
    rw [hcardT']
    exact hTc
  have huT' : u' ∈ T' := Subgroup.mem_map_of_mem e'.toMonoidHom huT
  have hu2' : u' * u' = 1 := by
    dsimp [u']
    rw [← map_mul, hu2, map_one]
  have hu1' : u' ≠ 1 := by
    intro h
    apply hu1
    have h' : e' u = e' 1 := by simpa [u'] using h
    exact e'.injective h'
  obtain ⟨hidx', htrans'⟩ :=
    natImage_statedSU_exists_normalizer_mod_fix (K := K) (k := k) hk hKcard
      hT'le hT' hTc' huT' hu2' hu1'
  have hidx_eq : (fixV (Subgroup.zpowers u')).index =
      (fixV (Subgroup.zpowers u)).index := by
    have hzp : Subgroup.zpowers u' = (Subgroup.zpowers u).map e'.toMonoidHom := by
      dsimp [u']
      exact (MonoidHom.map_zpowers e'.toMonoidHom u).symm
    rw [hzp, fixV_map_congr_equiv e (Subgroup.zpowers u)]
    exact Subgroup.index_map_equiv (fixV (Subgroup.zpowers u)) e
  refine ⟨?_, ?_⟩
  · calc (2 ^ k) ^ 2 ≤ (fixV (Subgroup.zpowers u')).index := hidx'
      _ = (fixV (Subgroup.zpowers u)).index := hidx_eq
  · intro w₁ w₂ hw₁ hw₂
    have hu'_apply : ∀ z : V, u' (e z) = e (u z) := by
      intro z
      change (H.congrHom e) u (e z) = e (u z)
      rw [H.congrHom_apply]
      simp
    have h1 : u' (e w₁) ≠ e w₁ := by
      intro h
      apply hw₁
      apply e.injective
      rw [← hu'_apply, h]
    have h2 : u' (e w₂) ≠ e w₂ := by
      intro h
      apply hw₂
      apply e.injective
      rw [← hu'_apply, h]
    obtain ⟨n', hn', heq⟩ := htrans' (e w₁) (e w₂) h1 h2
    let n : MulAut V := e'.symm n'
    have hn'_eq : e' n = n' := e'.apply_symm_apply n'
    have hnL : n ∈ L := by
      have hnmap : n' ∈ L.map e'.toMonoidHom := by
        rw [hLmap]
        exact hn'.1
      simpa [n] using
        (Subgroup.mem_map_equiv (f := e') (K := L) (x := n')).mp hnmap
    have hNmap : (Subgroup.normalizer (T : Set (MulAut V))).map e'.toMonoidHom =
        Subgroup.normalizer (T' : Set (MulAut (H.StdMod (Fin 3) K))) := by
      dsimp [T']
      exact Subgroup.map_equiv_normalizer_eq T e'
    have hnN : n ∈ Subgroup.normalizer (T : Set (MulAut V)) := by
      have hnpre : n' ∈ (Subgroup.normalizer (T : Set (MulAut V))).map e'.toMonoidHom := by
        rw [hNmap]
        exact hn'.2
      simpa [n] using
        (Subgroup.mem_map_equiv (f := e')
          (K := Subgroup.normalizer (T : Set (MulAut V))) (x := n')).mp hnpre
    refine ⟨n, ⟨hnL, hnN⟩, ?_⟩
    apply e.injective
    have hn'_z : n' (e w₁) = e (n w₁) := by
      rw [← hn'_eq]
      change (H.congrHom e) n (e w₁) = e (n w₁)
      rw [H.congrHom_apply]
      simp
    have hz : e (n w₁ * w₂⁻¹) = n' (e w₁) * (e w₂)⁻¹ := by
      rw [map_mul, map_inv, hn'_z]
    rw [← hu'_apply, hz]
    exact heq

end

end CFSG.Quasithin.Stroth

end
