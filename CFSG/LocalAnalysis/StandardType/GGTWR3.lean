module

public import CFSG.LocalAnalysis.StandardType.GGTWUpTwoW
public import CFSG.LocalAnalysis.StandardType.GGTWSmallADefs
public import CFSG.LocalAnalysis.StandardType.GGTWUpOf
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTWR3_false
    (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom 4) (hLift : GGTBTorLiftAFrom 4)
    (hW : GGTBWNormLabelInput) (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open)
    (hJ2S : GGTBJTwoNodeSmallInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hC : GGTWSmallCells) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt (fun q labJ labL => ggRowTwoNodeSmallJA q labJ labL ∧
      Nat.card ↥Bs = q ^ (labL.rank + 1) ∧ labL.rank ≠ 5) p J L)
    (hxL : x ∉ L) (hK : GGResTwoNodeSideDatum p Bs K J) : False := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  obtain ⟨labJ0, labX0, hJΛ0, hXΛ0, hJl0, hXl0, hrowJA0, hcard0, hrankne0⟩ := hrow
  have hrowA : GGResRowAt ggRowTwoNodeSmallJA p J L :=
    ⟨labJ0, labX0, hJΛ0, hXΛ0, hJl0, hXl0, hrowJA0⟩
  have hrow' := ggTWSmallA_row_narrow hp2 hrowA
  obtain ⟨N, labJ, labX, hcell, hJΛ, hXΛ, hJl, hXl, hrowSmall, hAtag, hJtag, hXrank, hJrank,
    hdatL, _hHL⟩ :=
    ggTWSmall_rowdata (r₀ := 4) (by norm_num) hRig hT hLift hW (fun _ => hR) (fun _ => hTw)
      hH hrow' hxL
  have hpN : p ∣ N := by
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num
  have hN5 : 5 ≤ N := by
    rcases hcell with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hN' : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10 := by
    rcases hcell with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hrow2 : ggRowTwoNode p labJ labX := hrowSmall.1
  have h4X : 4 ≤ labX.rank := ggTWSmallA_rank_ge Fact.out hp2 hJΛ hJtag hrow2
  have hiso : GGLabelIso labX0 labX := hRig labX0 labX _ hXΛ0 hXΛ hXl0 hXl
  have hEq : labX0 = labX := ggTWR_iso_eq hiso hAtag h4X
  have hCard : Nat.card ↥Bs = p ^ N := by
    rw [hEq] at hcard0
    rwa [hXrank] at hcard0
  have hrankne : labX.rank ≠ 5 := by rw [← hEq]; exact hrankne0
  have hNne6 : N ≠ 6 := by
    intro h6
    rw [h6] at hXrank
    exact hrankne (by omega)
  have hLd : GGResTwoNodeSideDatum p Bs L J :=
    (hJ2S G p B Bs x L D J y K hH).1 (l6a_xdatum_of_A hdatL) hrowA
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i1a, i2a, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hb, hcardΛa, hWML, hIntL, hWMK, hIntK, hlin, hrefl, hpairL, hpairK, hfLex, _hfKex,
    hclosL, hclosK, hdel, _hclosJ⟩ :=
    ggResTwoNodeDatum_of_sides_card_two ggWeylSimpleSystemsConjInput_holds hp2 hLd hK
  letI := i1; letI := i2; letI := i1a; letI := i2a; letI := i3; letI := i4
  obtain ⟨fL, hfL⟩ := hfLex
  obtain ⟨ΛL, i1L, i2L, ML0, CL0, VL, i3L, i4L, ιL, φL0, hL0, αL0, eL, hMLeqL, hWML0,
    hIntL0, hlinL0, hreflL0, hpairL0, hfL0ex, _hclosL0⟩ := hdatL
  letI := i1L; letI := i2L; letI := i3L; letI := i4L
  obtain ⟨fL0, hfL0⟩ := hfL0ex
  have hN2 : 2 ≤ N - 1 := by omega
  obtain ⟨e, hMLeq⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 1) hp2 hN2 hBs (ggAutomizer L Bs)
      (Λ₁ := ΛL) (M₁ := ML0) eL hMLeqL hWML0 fL0 φL0 hfL0 hreflL0
      (Λ₂ := Λ) (M₂ := ML) hWML fL (fun i => φ (Sum.inl i)) (fun i => hfL i)
      (fun i => hrefl (Sum.inl i))
  obtain ⟨pos, e', hMLeq', hInJ⟩ := ggTW_positions hN5 e hMLeq hb hdel
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  let xV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  have hdep : ¬ LinearIndependent (ZMod p) (fun i : Λ => h (Sum.inl i)) :=
    ggXDatumA_dep hFix hp2 hH hx hxL hN5 hpN e' hMLeq' hIntL
      (ι := ι) (φ := fun i : Λ => φ (Sum.inl i)) (h := fun i : Λ => h (Sum.inl i))
      (α := fun i : Λ => α (Sum.inl i)) (hφ := fun i w => hlin (Sum.inl i) w)
      (hpair := fun i j => hpairL i j) (hAL := hclosL)
  have hframe : GGDepAFrame p N (fun i : Fin (N - 1) => h (Sum.inl (e' i)))
      (fun i : Fin (N - 1) => α (Sum.inl (e' i))) xV :=
    ggXDatumA_frame hFix hp2 hH hx hN5 hpN e' hMLeq' hIntL
      (ι := ι) (φ := fun i : Λ => φ (Sum.inl i)) (h := fun i : Λ => h (Sum.inl i))
      (α := fun i : Λ => α (Sum.inl i)) (hφ := fun i w => hlin (Sum.inl i) w)
      (hpair := fun i j => hpairL i j) (hAL := hclosL) (hdep := hdep)
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hfinrank : Module.finrank (ZMod p) V = N := by
    haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
    have hVcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
      rwa [Nat.card_zmod] at h
    have hcardV : Nat.card V = Nat.card ↥Bs := by
      rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
      exact (Nat.card_congr ι.toEquiv).symm
    have heq : p ^ Module.finrank (ZMod p) V = p ^ N := by
      rw [← hVcard, hcardV, hCard]
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le heq
  have hnt : ∀ g ∈ Subgroup.closure (Set.range fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o)),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    intro g hg
    obtain ⟨ψ, hψ, hψg⟩ := l05nUO_exists_psi (p := p) ι φ g hg
    rw [← hψg]
    exact ggTT_nt_sup hH ι (by rw [l05nUO_sup_eq φ hclosL hclosK]; exact hψ)
  let ΦK : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
  have hex : ∃ a : Λa, α (Sum.inr a) xV ≠ 0 := by
    by_contra hno
    push Not at hno
    have hAKrange : Set.range ΦK =
        Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
          Set.range (fun a : Λa => φ (Sum.inr a)) := by
      ext z
      constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | inl j => exact Or.inl ⟨j, rfl⟩
        | inr a => exact Or.inr ⟨a, rfl⟩
      · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
        · exact ⟨Sum.inl j, rfl⟩
        · exact ⟨Sum.inr a, rfl⟩
    have hAK' : ggAutomizer K Bs = Subgroup.closure (Set.range ΦK) := by
      rw [hclosK, ← hAKrange]
    have hxker : ∀ i : Λ, α (Sum.inl i) xV = 0 := by
      intro i
      simpa using hframe.x_ker (e'.symm i)
    have hfixgen : ∀ o : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa, ΦK o ⟨x, hx⟩ = ⟨x, hx⟩ := by
      intro o
      apply (ggLin_fix_iff (p := p) ι (ΦK o) (⟨x, hx⟩ : ↥Bs)).mpr
      cases o with
      | inl j =>
          show ggLin (p := p) ι (φ (Sum.inl j.1)) xV = xV
          rw [hlin (Sum.inl j.1) xV, hxker j.1, zero_smul, sub_zero]
      | inr a =>
          show ggLin (p := p) ι (φ (Sum.inr a)) xV = xV
          rw [hlin (Sum.inr a) xV, hno a, zero_smul, sub_zero]
    have hfix : ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      intro ψ hψ
      rw [hAK'] at hψ
      exact ggFixed_of_mem_closure ΦK (⟨x, hx⟩ : ↥Bs) hfixgen ψ hψ
    exact ggTT_not_fixed hFixK hH hx hfix
  have hcells : GGTWDCells1 p N := by
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hC.2.2.1.1
    · exact absurd rfl hNne6
    · exact hC.1.1
    · exact hC.2.2.2.1.1
    · exact hC.2.1.1
  exact ggTWUp_false_twoW hp3 hN' hcells hb hcardΛa hInJ hWMK hIntK hlin hframe hfinrank
    hpairK hnt hex

end CFSG.StandardType

end
