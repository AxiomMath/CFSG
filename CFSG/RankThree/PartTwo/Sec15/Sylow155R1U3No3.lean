module

public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProof

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec11.LSSolvableProof
open Module

theorem l2EvenSolvableMinDegree_no3 :
  ∀ (f : ℕ), 6 ≤ f → ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
    ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
      ∀ (N : Subgroup X) [N.Normal], Group.IsSolvable N →
        Nonempty (X ⧸ N ≃* projSL 2 (GaloisField 2 f)) →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
        (ρ : X →* (V →ₗ[ZMod p] V)), (∃ x, ρ x ≠ 1) → 7 ≤ Module.finrank (ZMod p) V := by
  intro f hf p _ hp5 X _ _ hperf N _ hN hiso
  obtain ⟨e⟩ := hiso
  have hp2 : p ≠ 2 := by omega
  have : IsSimpleGroup (projSL 2 (GaloisField 2 f)) := isSimpleGroup_projSL (by omega)
  have hsimple : IsSimpleGroup (X ⧸ N) := MulEquiv.isSimpleGroup e
  have hsmallX := @index_lt_eq_top X _ _ hperf N _ hN f hf e
  suffices H : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      [Module.Finite (ZMod p) V] (ρ : X →* (V →ₗ[ZMod p] V)),
      Module.finrank (ZMod p) V = n → (∃ x, ρ x ≠ 1) → 7 ≤ n by
    intro V _ _ _ ρ hρ
    exact H _ V ρ rfl hρ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ ρ hn hρ
  have hVnt : Nontrivial V := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    obtain ⟨x, hx⟩ := hρ
    exact hx (LinearMap.ext fun v => Subsingleton.elim _ _)
  by_cases hirr : IsIrreducibleRep ρ
  ·
    have hKN : ρ.ker ≤ N := @ker_le_of_perfect X _ hperf N _ hN hsimple _ _ ρ hρ
    have : Group.IsPerfect X := hperf
    set ρbar : X ⧸ ρ.ker →* (V →ₗ[ZMod p] V) := QuotientGroup.lift ρ.ker ρ (fun _ hx => hx)
      with hρbar
    have hinj : Function.Injective ρbar := liftKer_injective ρ
    set M : Subgroup (X ⧸ ρ.ker) := N.map (QuotientGroup.mk' ρ.ker) with hM
    have hMsolv : Group.IsSolvable M := by
      have : Group.IsSolvable N := hN
      refine Group.isSolvable_of_surjective
        (f := ((QuotientGroup.mk' ρ.ker).comp N.subtype).codRestrict M (fun x => ⟨x, x.2, rfl⟩))
        ?_
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    set e' : (X ⧸ ρ.ker) ⧸ M ≃* projSL 2 (GaloisField 2 f) :=
      (QuotientGroup.quotientQuotientEquivQuotient ρ.ker N hKN).trans e with he'
    have hsmallY : ∀ J : Subgroup (X ⧸ ρ.ker), J.Normal → J.index < 262080 → J = ⊤ := by
      intro J hJ hidx
      have h1 : (J.comap (QuotientGroup.mk' ρ.ker)).index = J.index :=
        Subgroup.index_comap_of_surjective J (QuotientGroup.mk'_surjective ρ.ker)
      have h2 := hsmallX (J.comap (QuotientGroup.mk' ρ.ker)) (hJ.comap _) (h1 ▸ hidx)
      rw [eq_top_iff]
      intro q _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ρ.ker q
      have : x ∈ J.comap (QuotientGroup.mk' ρ.ker) := by rw [h2]; exact Subgroup.mem_top x
      exact this
    have hirr' : IsIrreducibleRep ρbar := by
      intro W hW
      apply hirr W
      intro x v hv
      have := hW (QuotientGroup.mk' ρ.ker x) v hv
      rwa [hρbar, QuotientGroup.mk'_apply, QuotientGroup.lift_mk] at this
    rw [← hn]
    exact seven_le_finrank_of_irreducible hf hp2 M hMsolv e' hsmallY ρbar hinj hirr'
  ·
    obtain ⟨W, hW, hW0, hWt⟩ : ∃ W : Submodule (ZMod p) V, (∀ x, ∀ v ∈ W, ρ x v ∈ W) ∧
        W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra hall
      push Not at hall
      exact hirr fun W hW => by
        by_cases h0 : W = ⊥
        · exact Or.inl h0
        · exact Or.inr (hall W hW h0)
    let ρW : X →* (W →ₗ[ZMod p] W) :=
      { toFun := fun x => (ρ x).restrict (p := W) (q := W) (hW x)
        map_one' := by
          apply LinearMap.ext
          intro w
          apply Subtype.ext
          simp
        map_mul' := fun x y => by
          apply LinearMap.ext
          intro w
          apply Subtype.ext
          simp }
    let ρQ : X →* ((V ⧸ W) →ₗ[ZMod p] (V ⧸ W)) :=
      { toFun := fun x => W.mapQ W (ρ x) (fun v hv => hW x v hv)
        map_one' := by
          apply Submodule.linearMap_qext
          apply LinearMap.ext
          intro v
          simp
        map_mul' := fun x y => by
          apply Submodule.linearMap_qext
          apply LinearMap.ext
          intro v
          simp }
    have hWlt : Module.finrank (ZMod p) W < n := hn ▸ Submodule.finrank_lt hWt
    have hQlt : Module.finrank (ZMod p) (V ⧸ W) < n := by
      have h1 := W.finrank_quotient_add_finrank
      have h2 : 0 < Module.finrank (ZMod p) W := by
        rw [Module.finrank_pos_iff]
        exact Submodule.nontrivial_iff_ne_bot.mpr hW0
      omega
    by_cases hρW : ∃ x, ρW x ≠ 1
    · have h1 := ih _ hWlt W ρW rfl hρW
      have h2 : Module.finrank (ZMod p) W ≤ n := hn ▸ Submodule.finrank_le W
      omega
    by_cases hρQ : ∃ x, ρQ x ≠ 1
    · have h1 := ih _ hQlt (V ⧸ W) ρQ rfl hρQ
      omega
    exfalso
    push Not at hρW hρQ
    have hfixW : ∀ x, ∀ w ∈ W, ρ x w = w := by
      intro x w hw
      have := congrArg (fun φ : W →ₗ[ZMod p] W => ((φ ⟨w, hw⟩ : W) : V)) (hρW x)
      simpa [ρW] using this
    have hfixQ : ∀ x v, ρ x v - v ∈ W := by
      intro x v
      have := congrArg (fun φ : (V ⧸ W) →ₗ[ZMod p] (V ⧸ W) => φ (Submodule.Quotient.mk v))
        (hρQ x)
      simp only [ρQ, MonoidHom.coe_mk, OneHom.coe_mk, Submodule.mapQ_apply,
        Module.End.one_apply] at this
      exact (Submodule.Quotient.eq W).mp this
    have hcomm : ∀ x y, ρ x * ρ y = ρ y * ρ x := by
      intro x y
      apply LinearMap.ext
      intro v
      rw [Module.End.mul_apply, Module.End.mul_apply]
      have ha := hfixQ x v
      have hb := hfixQ y v
      have e1 : ρ y v = v + (ρ y v - v) := by abel
      have e2 : ρ x v = v + (ρ x v - v) := by abel
      rw [e1, map_add, hfixW x _ hb, e2, map_add, hfixW y _ ha]
      abel
    have hker : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ ρ.ker := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, hcomm x y,
        mul_assoc (ρ y), ← map_mul, mul_inv_cancel, map_one, mul_one, ← map_mul,
        mul_inv_cancel, map_one]
    have htop : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top
    rw [htop] at hker
    obtain ⟨x, hx⟩ := hρ
    exact hx (hker (Subgroup.mem_top x))

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
