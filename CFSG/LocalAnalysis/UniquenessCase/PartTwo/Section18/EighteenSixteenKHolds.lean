module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UTorus
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFixW
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC

theorem k_K_SU4_nonsingPoint_holds :
    ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (p n : ℕ),
      2 ≤ n → IsSUn ↥H 4 n → NatSUn H ⊤ ⊥ 4 n →
        p.Prime → (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] →
          ∀ (F : Type) [Field F] [Finite F], Nat.card F = (2 ^ n) ^ 2 →
            ∀ (ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F))
              (ψ : W ≃* Multiplicative (Fin 4 → F)),
              NatCoordsSU4 H n F ε ψ → ∀ v : W,
                (∑ i, (Multiplicative.toAdd (ψ v)) i ^ (2 ^ n + 1)) ≠ 0 →
                  ∃ E : Subgroup (MulAut W), E ≤ H ∧ IsPGroup p E ∧ ¬ IsCyclic E ∧
                    ∀ e ∈ E, e v = v := by
  intro W _ _ H p n hn2 _hSUn hNat hp hcong F _ _ hFcard ε ψ hψ v hv
  classical
  have hpq : p ∣ 2 ^ n + 1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong
  obtain ⟨E', hE'S, hE'a, hE'card, hE'fix⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_stab_elemAbelian_nonsing (F := F) (n := n) (p := p)
      hp hpq hFcard (w := Multiplicative.toAdd (ψ v)) hv
  let S : Subgroup (GL (Fin 4) F) := StatedSU 4 (2 ^ n) F
  let f : ↥S →* MulAut W := H.subtype.comp ε.symm.toMonoidHom
  let E : Subgroup (MulAut W) := (E'.subgroupOf S).map f
  have hEH : E ≤ H := by
    rintro _ ⟨y, -, rfl⟩
    exact (ε.symm y).2
  have hEa : IsElemAbelian p E := (hE'a.subgroupOf S).map f
  have hEcard : Nat.card ↥E = p ^ 2 := by
    have h2 : Nat.card ↥(E'.subgroupOf S) = Nat.card ↥E' := by
      calc Nat.card ↥(E'.subgroupOf S) =
            Nat.card ↥((E'.subgroupOf S).map S.subtype) :=
            (Subgroup.card_map_of_injective (K := E'.subgroupOf S) (f := S.subtype)
              S.subtype_injective).symm
        _ = Nat.card ↥E' := by rw [Subgroup.map_subgroupOf_eq_of_le hE'S]
    calc Nat.card ↥E = Nat.card ↥(E'.subgroupOf S) := by
          change Nat.card ↥((E'.subgroupOf S).map f) = Nat.card ↥(E'.subgroupOf S)
          exact Subgroup.card_map_of_injective (K := E'.subgroupOf S) (f := f)
            (H.subtype_injective.comp ε.symm.injective)
      _ = Nat.card ↥E' := h2
      _ = p ^ 2 := hE'card
  refine ⟨E, hEH, hEa.isPGroup, ?_, ?_⟩
  · exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_not_isCyclic_of_card_sq hp hEa hEcard
  · intro e he
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 he
    have hy' : (y : GL (Fin 4) F) ∈ E' := (Subgroup.mem_subgroupOf).1 hy
    have h1 : ψ ((f y : MulAut W) v) = ψ v := by
      change ψ (((ε.symm y : ↥H) : MulAut W) v) = ψ v
      rw [hψ (ε.symm y) v, MulEquiv.apply_symm_apply]
      rw [hE'fix (y : GL (Fin 4) F) hy']
      simp
    exact ψ.injective h1

theorem k_K_Omega6Minus_nonsingPoint_holds :
    ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (p n : ℕ),
      2 ≤ n → IsOmegaMinus ↥H 6 n →
        ∀ (W' : Subgroup W) (hW' : StableUnder H W') (hN : NatOmegaMinus H W' ⊥ 6 n),
        p.Prime → (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] →
          ∀ (F : Type) [Field F] [Finite F] (b c : F), Nat.card F = 2 ^ n →
            (∀ s : F, s ^ 2 + b * s + c ≠ 0) →
              ∀ (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
                (ψ : W' ≃*
                  Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
                NatCoordsOmegaMinusOn H W' hW' F b c ε ψ →
                  ∀ v : W',
                    StatedQuadMinus 3 F b c (Multiplicative.toAdd (ψ v)) ≠ 0 →
                      ∃ E : Subgroup (MulAut W), E ≤ H ∧ IsPGroup p E ∧ ¬ IsCyclic E ∧
                        ∀ e ∈ E, (e : MulAut W) (v : W) = (v : W) := by
  intro W _ _ H p n hn2 _hO W' hW' _hN hp hcong F _ _ b c hF hirr ε ψ hψ v hv
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := n) hF
  have hn1 : 1 ≤ n := by omega
  obtain ⟨M⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.nonempty_normModel (F := F) (b := b) (c := c) hirr hF hn1
  have hpq : p ∣ Nat.card F + 1 := by
    rw [hF]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong
  obtain ⟨E', hE'S, hE'a, hE'card, hE'fix⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_stab_nonsing M hirr hp hpq
      (w := Multiplicative.toAdd (ψ v)) hv
  let S : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :=
    StatedOmega (StatedQuadMinus 3 F b c)
  let f : ↥S →* MulAut W := H.subtype.comp ε.symm.toMonoidHom
  let E : Subgroup (MulAut W) := (E'.subgroupOf S).map f
  have hEH : E ≤ H := by
    rintro _ ⟨y, -, rfl⟩
    exact (ε.symm y).2
  have hEa : IsElemAbelian p E := (hE'a.subgroupOf S).map f
  have hEcard : Nat.card ↥E = p ^ 2 := by
    have h2 : Nat.card ↥(E'.subgroupOf S) = Nat.card ↥E' := by
      calc Nat.card ↥(E'.subgroupOf S) =
            Nat.card ↥((E'.subgroupOf S).map S.subtype) :=
            (Subgroup.card_map_of_injective (K := E'.subgroupOf S) (f := S.subtype)
              S.subtype_injective).symm
        _ = Nat.card ↥E' := by rw [Subgroup.map_subgroupOf_eq_of_le hE'S]
    calc Nat.card ↥E = Nat.card ↥(E'.subgroupOf S) := by
          change Nat.card ↥((E'.subgroupOf S).map f) = Nat.card ↥(E'.subgroupOf S)
          exact Subgroup.card_map_of_injective (K := E'.subgroupOf S) (f := f)
            (H.subtype_injective.comp ε.symm.injective)
      _ = Nat.card ↥E' := h2
      _ = p ^ 2 := hE'card
  refine ⟨E, hEH, hEa.isPGroup, ?_, ?_⟩
  · exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_not_isCyclic_of_card_sq hp hEa hEcard
  · intro e he
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 he
    have hy' : (y : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) ∈ E' :=
      (Subgroup.mem_subgroupOf).1 hy
    have hmem : (f y : MulAut W) (v : W) ∈ W' :=
      hW' (f y) (hEH (Subgroup.mem_map.2 ⟨y, hy, rfl⟩)) (v : W) v.2
    have hsub : (⟨(f y : MulAut W) (v : W), hmem⟩ : W') =
        ⟨((ε.symm y : ↥H) : MulAut W) (v : W),
          hW' ((ε.symm y : ↥H) : MulAut W) (ε.symm y).2 (v : W) v.2⟩ :=
      Subtype.ext rfl
    have h1 : (⟨(f y : MulAut W) (v : W), hmem⟩ : W') = v := by
      apply ψ.injective
      rw [hsub, hψ (ε.symm y) v, MulEquiv.apply_symm_apply]
      rw [hE'fix (y : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) hy']
      simp
    exact congrArg Subtype.val h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
