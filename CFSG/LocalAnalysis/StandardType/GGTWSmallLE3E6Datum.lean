module

public import CFSG.LocalAnalysis.StandardType.GGTWSmallADefs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3NodesKeep
public import CFSG.LocalAnalysis.StandardType.GGPZCartanRank
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGDepED4Align
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggLE3Small_E6_L
    (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom 4) (hLift : GGTBTorLiftAFrom 4)
    (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open) (hJ2S : GGTBJTwoNodeSmallInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt (fun q labJ labK => ggRowTwoNodeSmallJA q labJ labK ∧ labK.rank = 5) p J K)
    (hL3 : GGResLeviSideDatumLE3 p Bs L J) (hL2 : ¬ GGResTwoNodeSideDatum p Bs L J)
    (hp3 : p = 3) (hcard : Nat.card ↥Bs = 3 ^ 6) :
    GGResXDatumE6Core p Bs L ∧ GGResXDatumA p Bs K 5 := by
  classical
  subst hp3
  have hp : (3 : ℕ).Prime := Fact.out
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrowJA_and⟩ := hrow
  have hrowJA : ggRowTwoNodeSmallJA 3 labJ labK := hrowJA_and.1
  have hKrow5 : labK.rank = 5 := hrowJA_and.2
  have hrowSmall : ggRowTwoNodeSmall 3 labJ labK := hrowJA.1
  have hJtag : labJ.tag = .A ∨ labJ.tag = .twA := hrowJA.2
  have hrow2 : ggRowTwoNode 3 labJ labK := hrowSmall.1
  have hKle9 : labK.rank ≤ 9 := hrowSmall.2
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have h4K : 4 ≤ labK.rank := ggTWSmallA_rank_ge hp hp2 hJΛ hJtag hrow2
  obtain ⟨-, hKtag, hKrank_eq, hdvdK, hKtdvdM⟩ := l05nQD_row_facts hrow2 h4K
  have hN : labK.rank + 1 = 5 ∨ labK.rank + 1 = 6 ∨ labK.rank + 1 = 7 ∨
      labK.rank + 1 = 9 ∨ labK.rank + 1 = 10 := by
    rcases l05nQD_cell hp hp2 h4K hKle9 hdvdK with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      omega
  have hrowK0 : GGResRowAt ggRowTwoNodeSmallJA 3 J K :=
    ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrowJA⟩
  have hrowK : GGResRowAt ggRowTwoNode 3 J K :=
    ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrow2⟩
  have hKdatum : GGResXDatumA 3 Bs K (labK.rank + 1 - 1) :=
    ggTWSmall_rowdata_K (r₀ := 4) (N := labK.rank + 1) (le_refl 4) hRig hT hLift
      (fun _ => hR) (fun _ => hTw) hH hN (by omega) hJΛ hJl hJtag (by omega) hrowK
  have hKdatum5 : GGResXDatumA 3 Bs K 5 := by
    simpa [hKrow5] using hKdatum
  have hKside : GGResTwoNodeSideDatum 3 Bs K J :=
    (hJ2S G 3 B Bs x L D J y K hH).2 (l6a_xdatum_of_A hKdatum) hrowK0
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hx1 : x ≠ 1 := by
    intro h1
    have h := hH.1.orderOf_x
    rw [h1, orderOf_one] at h
    exact (Fact.out : (3 : ℕ).Prime).one_lt.ne' h.symm
  have hfixx := ggRC_automizer_fixes_y hxBs hLx
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, hcard6, hWM, hC, hlin, hrefl, hpair,
    hfex, hclos⟩ :=
    ggLE3_three_nodes_keep hp2 hBs (N := 6) (by norm_num) hKdatum5 hKside hL3 hL2
  obtain ⟨f, hf⟩ := hfex
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  let z : V := ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  have hz0 : z ≠ 0 := by
    intro h0
    apply hx1
    have h1 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 := ι.injective (by simpa [z] using h0)
    have h2 : (⟨x, hxBs⟩ : ↥Bs) = 1 := by simpa using congrArg Additive.toMul h1
    exact congrArg Subtype.val h2
  have hzα : ∀ i, α i z = 0 := by
    intro i
    have hmem : φ i ∈ ggAutomizer L Bs := by
      rw [hclos]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hfix : ggLin (p := 3) ι (φ i) z = z :=
      (ggLin_fix_iff (p := 3) ι (φ i) (⟨x, hxBs⟩ : ↥Bs)).mp (hfixx (φ i) hmem)
    have h3 := hlin i z
    rw [hfix] at h3
    have h1 : α i z • h i = 0 := sub_eq_self.mp h3.symm
    have h4 : α i z * (2 : ZMod 3) = 0 := by
      have := congrArg (α i) h1
      rw [map_smul, smul_eq_mul, hpair i i, hC.1 i, map_zero] at this
      simpa using this
    rcases mul_eq_zero.mp h4 with h | h
    · exact h
    · exact absurd h (by
        have h0 : (2 : ZMod 3).val = 0 := (ZMod.val_eq_zero _).mpr h
        rw [ZMod.val_ofNat] at h0
        norm_num at h0)
  have hfinrank : Module.finrank (ZMod 3) V = 6 := by
    have hVcard : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
      rwa [Nat.card_zmod] at h
    have hcardV : Nat.card V = Nat.card ↥Bs := by
      rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
      exact (Nat.card_congr ι.toEquiv).symm
    have heq : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 6 := by rw [← hVcard, hcardV, hcard]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) heq
  have hdimn : Module.finrank (ZMod 3) V ≤ Fintype.card Λ := by omega
  rcases ggIntCartan_A_or_E6_of_finrank_le hWM hC hp2 h α hpair hz0 hzα hdimn with
    ⟨n, e, -, hpd, -⟩ | ⟨-, e, he⟩
  · exfalso
    have hcn : Fintype.card Λ = n := by
      rw [← Fintype.card_fin n]
      exact (Fintype.card_congr e).symm
    omega
  · have hM6 : M = CoxeterMatrix.E₆.reindex e := ggIntCartan_E6_coxeter_reindex hC e he
    exact ⟨⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM6, hWM, hC, hlin, hrefl, hpair,
      ⟨f, hf⟩, hclos⟩, hKdatum5⟩

end CFSG.StandardType

end
