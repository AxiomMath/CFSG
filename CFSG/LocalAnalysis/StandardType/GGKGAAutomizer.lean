module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative

namespace KGA

theorem kga_card_automizer {L' : Type} [Group L'] [Finite L'] {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut L')} (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hsgn : ∀ i : Fin k, ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ))
    (hsp : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn))) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 2 ^ k * k.factorial := by
  classical
  let V := Fin k → Multiplicative (ZMod p)
  let ΘA : MulAut V ≃* MulAut ↥A := MulAut.congr Θ
  let H : Subgroup (MulAut L') := (MulAut.conj : L' →* MulAut L').range
  have hiff : ∀ φ : MulAut ↥A, φ ∈ ggAutomizer H A ↔ IsSignedPerm ⇑(ΘA.symm φ) := by
    intro φ
    constructor
    · intro hφ
      rw [mem_ggAutomizer_iff] at hφ
      obtain ⟨g, hgH, hgN, hgapply⟩ := hφ
      rw [MonoidHom.mem_range] at hgH
      obtain ⟨n, rfl⟩ := hgH
      have hEq : φ = ggConjAut A hgN := by
        refine MulEquiv.ext fun b => Subtype.ext ?_
        rw [ggConjAut_apply, hgapply]
      rw [hEq]
      exact hsp n hgN
    · intro hφs
      have hs : ∀ i, sgnAut i ∈ (ggAutomizer H A).comap ΘA.toMonoidHom := by
        intro i
        obtain ⟨n, hn, hEq⟩ := hsgn i
        rw [Subgroup.mem_comap]
        change ΘA (sgnAut i) ∈ ggAutomizer H A
        rw [← hEq]
        exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
      have ht : ∀ a b : Fin k, a ≠ b →
          permAut (Equiv.swap a b) ∈ (ggAutomizer H A).comap ΘA.toMonoidHom := by
        intro a b _
        obtain ⟨n, hn, hEq⟩ := hperm (Equiv.swap a b)
        rw [Subgroup.mem_comap]
        change ΘA (permAut (Equiv.swap a b)) ∈ ggAutomizer H A
        rw [← hEq]
        exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
      have hmem := mem_of_isSignedPerm hs ht hφs
      rw [Subgroup.mem_comap] at hmem
      change ΘA (ΘA.symm φ) ∈ ggAutomizer H A at hmem
      rwa [MulEquiv.apply_symm_apply] at hmem
  let S := {u : MulAut V // IsSignedPerm ⇑u}
  have hcard1 : Nat.card ↥(ggAutomizer H A) = Nat.card S := by
    refine Nat.card_congr ?_
    refine Equiv.ofBijective
      (fun φ : ↥(ggAutomizer H A) => (⟨ΘA.symm φ.1, (hiff φ.1).mp φ.2⟩ : S)) ?_
    constructor
    · intro φ ψ h
      refine Subtype.ext ?_
      have h1 : ΘA.symm φ.1 = ΘA.symm ψ.1 := congrArg Subtype.val h
      have := congrArg ΘA h1
      simpa [MulEquiv.apply_symm_apply] using this
    · rintro ⟨u, hu⟩
      refine ⟨⟨ΘA u, (hiff (ΘA u)).mpr ?_⟩, ?_⟩
      · simpa [MulEquiv.symm_apply_apply] using hu
      · refine Subtype.ext ?_
        simp [MulEquiv.symm_apply_apply]
  let Sign := {ε : ZMod p // ε = 1 ∨ ε = -1}
  have hSign : Nat.card Sign = 2 := by
    rw [Nat.card_eq_two_iff' (⟨1, Or.inl rfl⟩ : Sign)]
    refine ⟨⟨-1, Or.inr rfl⟩, ?_, ?_⟩
    · intro h
      have h1 : (-1 : ZMod p) = 1 := Subtype.ext_iff.mp h
      have h2 : (2 : ZMod p) = 0 := by
        have hh : (-1 : ZMod p) + 1 = 0 := neg_add_cancel 1
        rw [h1] at hh
        rw [show (1 : ZMod p) + 1 = 2 by ring] at hh
        exact hh
      exact coord_two_ne_zero hp hp2 h2
    · intro y hy
      refine Subtype.ext ?_
      rcases y.2 with h | h
      · exact absurd (Subtype.ext h) hy
      · exact h
  let F : Equiv.Perm (Fin k) × (Fin k → Sign) → S :=
    fun x => ⟨permAut x.1 * diagAut (fun i => (x.2 i : ZMod p))
        (fun i => coord_sign_mul_self (x.2 i).2),
      isSignedPerm_permAut_mul_diagAut x.1 _ (fun i => (x.2 i).2)⟩
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      have hval : permAut x.1 * diagAut (fun i => (x.2 i : ZMod p))
            (fun i => coord_sign_mul_self (x.2 i).2) =
          permAut y.1 * diagAut (fun i => (y.2 i : ZMod p))
            (fun i => coord_sign_mul_self (y.2 i).2) := congrArg Subtype.val hxy
      have h1 : ∀ i, x.1 i = y.1 i ∧ (x.2 i : ZMod p) = (y.2 i : ZMod p) := by
        intro i
        have hc := congrArg (fun u : MulAut V => u (Pi.mulSingle i (ofAdd 1))) hval
        rw [MulAut.mul_apply, MulAut.mul_apply, diagAut_mulSingle, permAut_mulSingle,
          diagAut_mulSingle, permAut_mulSingle, mul_one, mul_one] at hc
        exact mulSingle_ofAdd_eq_iff (coord_sign_ne_zero hp (x.2 i).2) hc
      refine Prod.ext (Equiv.ext fun i => (h1 i).1) (funext fun i => Subtype.ext (h1 i).2)
    · rintro ⟨u, hu⟩
      obtain ⟨π, ε, hε, hπ⟩ := hu
      refine ⟨(π, fun i => ⟨ε i, hε i⟩), ?_⟩
      refine Subtype.ext ?_
      refine MulEquiv.ext fun f => ?_
      refine eq_of_toAdd_perm_eq π fun i => ?_
      rw [MulAut.mul_apply, permAut_apply, Function.comp_apply, Equiv.Perm.coe_inv,
        Equiv.symm_apply_apply, diagAut_apply, toAdd_ofAdd]
      exact (hπ f i).symm
  let e2 := Equiv.ofBijective F hF
  have hcard2 : Nat.card S = 2 ^ k * k.factorial := by
    calc Nat.card S = Nat.card (Equiv.Perm (Fin k) × (Fin k → Sign)) := (Nat.card_congr e2).symm
      _ = Nat.card (Equiv.Perm (Fin k)) * Nat.card (Fin k → Sign) := Nat.card_prod _ _
      _ = k.factorial * 2 ^ k := by
        rw [Nat.card_perm, Nat.card_fin, Nat.card_fun, Nat.card_fin, hSign]
      _ = 2 ^ k * k.factorial := Nat.mul_comm _ _
  exact hcard1.trans hcard2

end KGA

end CFSG.StandardType

end
