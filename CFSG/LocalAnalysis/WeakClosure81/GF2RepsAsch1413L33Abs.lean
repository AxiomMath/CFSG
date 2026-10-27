module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Gen
public import CFSG.LocalAnalysis.WeakClosure81.W18Asch66
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413Free

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.Quasithin Subgroup

theorem asch1413_L33_false {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {ρ : Q →* MulAut V} (hρ : Function.Injective ρ)
    {A X : Subgroup Q} (hq : IsQuadraticOn ρ A) {z i : Q} (hzA : z ∈ A) (hii : i * i = z)
    (hi : i ∈ ⨆ c ∈ centralizer ({z} : Set Q), A.map (MulAut.conj c).toMonoidHom)
    (hX : Nat.card X = 9) (hXz : ∀ x ∈ X, z * x * z⁻¹ = x⁻¹)
    (hXi : ∀ x ∈ X, i * x * i⁻¹ ∈ X) : False := by
  let A' : Subgroup (MulAut V) := A.map ρ
  let X' : Subgroup (MulAut V) := X.map ρ
  let z' : MulAut V := ρ z
  let i' : MulAut V := ρ i
  have hq' : IsQuadratic A' := by
    rw [IsQuadratic, commV, Subgroup.closure_le]
    rintro w ⟨x, hx, v, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    refine (mem_fixV (X := A') (v := ρ a v * v⁻¹)).mpr ?_
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    exact hq a ha b' hb' v
  have hX'card : Nat.card X' = 9 := by
    rw [show Nat.card X' = Nat.card X from Subgroup.card_map_of_injective hρ, hX]
  have hX'odd : Odd (Nat.card X') := by rw [hX'card]; decide
  have hz' : ∀ x' ∈ X', z' * x' * z'⁻¹ = x'⁻¹ := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
    simpa [z', map_mul, map_inv] using congrArg ρ (hXz x hx)
  have hi' : i' * i' = z' := by
    have h := congrArg ρ hii
    simpa [i', z', map_mul] using h
  have hiX' : ∀ x' ∈ X', i' * x' * i'⁻¹ ∈ X' := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
    refine Subgroup.mem_map.mpr ⟨i * x * i⁻¹, hXi x hx, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  have hi'Q : i' ∈ Asch6.quadY ⊤ A' z' := by
    have hle : (⨆ c ∈ centralizer ({z} : Set Q), A.map (MulAut.conj c).toMonoidHom) ≤
        (Asch6.quadY ⊤ A' z').comap ρ := by
      refine iSup₂_le fun c hc => ?_
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_comap]
      have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      have hcomm : ρ c * z' = z' * ρ c := by
        show ρ c * ρ z = ρ z * ρ c
        rw [← map_mul, ← map_mul, hcz]
      have hmem : (MulAut.conj (ρ c)) (ρ a) ∈ A'.map (MulAut.conj (ρ c)).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨ρ a, Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩
      have hlequad : A'.map (MulAut.conj (ρ c)).toMonoidHom ≤ Asch6.quadY ⊤ A' z' :=
        le_iSup_of_le (ρ c) (le_iSup_of_le trivial (le_iSup_of_le hcomm le_rfl))
      have hρ : ρ ((MulAut.conj c).toMonoidHom a) = (MulAut.conj (ρ c)) (ρ a) := by
        change ρ (MulAut.conj c a) = MulAut.conj (ρ c) (ρ a)
        rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
      rw [hρ]
      exact hlequad hmem
    exact hle hi
  have hfix : ∀ w ∈ commV (Subgroup.zpowers z'), i' w = w :=
    Asch6.fixes_commV_quadY hq' (Subgroup.mem_map.mpr ⟨z, hzA, rfl⟩) i' hi'Q
  have hbot : X' = ⊥ := eq_bot_of_inverted_free hV hX'odd hz' hi' hiX' hfix
  rw [hbot, Subgroup.card_bot] at hX'card
  exact absurd hX'card (by decide)

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
