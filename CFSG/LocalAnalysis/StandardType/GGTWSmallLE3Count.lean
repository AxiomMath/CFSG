module

public import CFSG.LocalAnalysis.StandardType.GGTWSmallADefs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Count
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge
public import CFSG.LocalAnalysis.StandardType.GGRowKFrame
public import CFSG.LocalAnalysis.StandardType.GGTWR3
public import CFSG.LocalAnalysis.StandardType.GGTWSmallAL
public import CFSG.LocalAnalysis.StandardType.GGDepED4LE3Close
public import CFSG.LocalAnalysis.StandardType.GGDepED4LE3Up7
public import CFSG.LocalAnalysis.StandardType.GGKSmall7Leaf
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepConsumer
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6DepConsumer
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimDefs
import CFSG.LocalAnalysis.StandardType.GGTWR2
import CFSG.LocalAnalysis.StandardType.GGTWHLNormalizer
import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineFrameShared
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineConsumerK
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineDepTwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGNineDepKFixLine
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallDepK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggBstarComm_map_subtype_le {G : Type} [Group G] {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    (ggBstarComm K Bs).map Bs.subtype ≤ K := by
  rw [Subgroup.map_le_iff_le_comap]
  unfold ggBstarComm
  rw [Subgroup.closure_le]
  rintro c ⟨b, φ, hφ, rfl⟩
  change ((b⁻¹ * φ b : ↥Bs) : G) ∈ K
  obtain ⟨g, hgK, -, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  have hb : (b : G)⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.inv_mem _ (hN b.2)
  have hconj : (b : G)⁻¹ * g * b ∈ K := by
    have h := (Subgroup.mem_normalizer_iff.mp hb g).mp hgK
    simpa using h
  have hcoe : (((b⁻¹ * φ b : ↥Bs) : G)) = ((b : G)⁻¹ * g * b) * g⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hφg b]
    group
  rw [hcoe]
  exact K.mul_mem hconj (K.inv_mem hgK)

theorem ggLE3Small_count_L
    (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom 4) (hLift : GGTBTorLiftAFrom 4)
    (hW : GGTBWNormLabelInput) (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open)
    (hJ2S : GGTBJTwoNodeSmallInput) (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowTwoNodeSmallJA p J L) (hxL : x ∉ L)
    (hK3 : GGResLeviSideDatumLE3 p Bs K J) (hK2 : ¬ GGResTwoNodeSideDatum p Bs K J) :
    p = 3 ∧ Nat.card ↥Bs = 3 ^ 6 ∧
      GGResRowAt (fun q labJ labL => ggRowTwoNodeSmallJA q labJ labL ∧ labL.rank = 5) p J L := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hrow' := ggTWSmallA_row_narrow hp2 hrow
  obtain ⟨N, labJ, labX, hcell, hJΛ, hXΛ, hJl, hXl, hrowSmall, hAtag, hJtag, hXrank, hJrank,
    hdatL, hHL⟩ :=
    ggTWSmall_rowdata (r₀ := 4) (by norm_num) hRig hT hLift hW (fun _ => hR) (fun _ => hTw) hH
      hrow' hxL
  have hpN : p ∣ N := by
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num
  have hN5 : 5 ≤ N := by
    rcases hcell with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hx1 : x ≠ 1 := by
    intro h1
    have h := hH.1.orderOf_x
    rw [h1, orderOf_one] at h
    exact (Fact.out : p.Prime).one_lt.ne' h.symm
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hyBs : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hy1 : y ≠ 1 := ggRC_y_ne_one hH
  have hfixL := hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K
    hH.2.2.2.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2
  have hfixy := ggRC_automizer_fixes_y hyBs hKy
  have hLd : GGResTwoNodeSideDatum p Bs L J :=
    (hJ2S G p B Bs x L D J y K hH).1 (l6a_xdatum_of_A hdatL) hrow
  have hle : Nat.card ↥Bs ≤ p ^ N :=
    ggLE3_card_le_of_fix (N := N) (by omega) hdatL hxp hfixL
  have h3card := ggLE3_three_card hp2 hBs hN5 hpN hdatL hLd hK3 hK2 hyBs hy1 hfixy
  rcases h3card with ⟨hp3, hN6, hcard⟩ | hbound
  · exact ⟨hp3, hcard, ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hrowSmall, hJtag⟩, by omega⟩⟩
  · exfalso
    have hlt : p ^ N < p ^ (N + 1) :=
      Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
    omega

theorem ggLE3Small_count_K
    (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom 4) (hLift : GGTBTorLiftAFrom 4)
    (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open) (hJ2S : GGTBJTwoNodeSmallInput)
    (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeSmallJA p J K)
    (hL3 : GGResLeviSideDatumLE3 p Bs L J) (hL2 : ¬ GGResTwoNodeSideDatum p Bs L J) :
    (p = 3 ∧ Nat.card ↥Bs = 3 ^ 6 ∧
        GGResRowAt (fun q labJ labK => ggRowTwoNodeSmallJA q labJ labK ∧ labK.rank = 5) p J K) ∨
      GGResRowAt (fun q labJ labK => ggRowTwoNodeSmallJA q labJ labK ∧
        Nat.card ↥Bs = q ^ (labK.rank + 2)) p J K := by
  have hrowK0 : GGResRowAt ggRowTwoNodeSmallJA p J K := hrow
  obtain ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrowJA⟩ := hrow
  have hrowSmall : ggRowTwoNodeSmall p labJ labK := hrowJA.1
  have hJtag : labJ.tag = .A ∨ labJ.tag = .twA := hrowJA.2
  have hrow2 : ggRowTwoNode p labJ labK := hrowSmall.1
  have hKle9 : labK.rank ≤ 9 := hrowSmall.2
  have hp : p.Prime := hH.1.tableB_facts.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have h4K : 4 ≤ labK.rank := ggTWSmallA_rank_ge hp hp2 hJΛ hJtag hrow2
  obtain ⟨-, hKtag, hKrank_eq, hdvdK, hKtdvdM⟩ := l05nQD_row_facts hrow2 h4K
  have hN : labK.rank + 1 = 5 ∨ labK.rank + 1 = 6 ∨ labK.rank + 1 = 7 ∨
      labK.rank + 1 = 9 ∨ labK.rank + 1 = 10 := by
    rcases l05nQD_cell hp hp2 h4K hKle9 hdvdK with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      omega
  have hrowK : GGResRowAt ggRowTwoNode p J K :=
    ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrow2⟩
  have hKdatum : GGResXDatumA p Bs K (labK.rank + 1 - 1) :=
    ggTWSmall_rowdata_K (r₀ := 4) (N := labK.rank + 1) (le_refl 4) hRig hT hLift
      (fun _ => hR) (fun _ => hTw) hH hN (by omega) hJΛ hJl hJtag (by omega) hrowK
  have hKside : GGResTwoNodeSideDatum p Bs K J :=
    (hJ2S G p B Bs x L D J y K hH).2 (l6a_xdatum_of_A hKdatum) hrowK0
  have hN5 : 5 ≤ labK.rank + 1 := by rcases hN with h | h | h | h | h <;> omega
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hx1 : x ≠ 1 := by
    intro h1
    have h := hH.1.orderOf_x
    rw [h1, orderOf_one] at h
    exact (Fact.out : p.Prime).one_lt.ne' h.symm
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  have hfixL := hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K
    hH.2.2.2.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2
  have hfixx := ggRC_automizer_fixes_y hxBs hLx
  have h3card := ggLE3_three_card_fixY hp2 hBs hN5 hdvdK
    (by simpa [Nat.add_sub_cancel] using hKdatum) hKside hL3 hL2 hxBs hx1 hxp hfixx hfixL
  rcases h3card with ⟨hp3, hN6, hcard⟩ | hcard
  · exact Or.inl ⟨hp3, hcard, ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrowJA, by omega⟩⟩
  · refine Or.inr ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrowJA, ?_⟩
    rw [hcard]

theorem ggLE3Small_card_K_false (hDim : GGTwoNodeRowDimKnown)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt (fun q labJ labK => ggRowTwoNodeSmallJA q labJ labK ∧
      Nat.card ↥Bs = q ^ (labK.rank + 2)) p J K) : False := by
  obtain ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, ⟨hrowJA, hcard⟩⟩ := hrow
  have hrow2 : ggRowTwoNode p labJ labK := hrowJA.1.1
  have hJtag : labJ.tag = .A ∨ labJ.tag = .twA := hrowJA.2
  have hp : p.Prime := hH.1.tableB_facts.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have h4K : 4 ≤ labK.rank := ggTWSmallA_rank_ge hp hp2 hJΛ hJtag hrow2
  obtain ⟨-, -, -, hdvdK, -⟩ := l05nQD_row_facts hrow2 h4K
  have hle : Nat.card ↥Bs ≤ p ^ (labK.rank + 1) :=
    hDim G p B Bs x L D J y K (labK.rank + 1) hH
      ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrow2, rfl⟩ hp2 (by omega) hdvdK
  have hlt : p ^ (labK.rank + 1) < p ^ (labK.rank + 2) :=
    Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

theorem ggTWSmallA_K_twoA
    (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom 4) (hLift : GGTBTorLiftAFrom 4)
    (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open) (hJ2S : GGTBJTwoNodeSmallInput)
    (hC : GGTWSmallCells) (hPZ : GGPZInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hMult : GGTWMultLeaves) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt (fun q labJ labK => ggRowTwoNodeSmallJA q labJ labK ∧
      Nat.card ↥Bs = q ^ labK.rank) p J K)
    (hyK : y ∉ K) (hL : GGResTwoNodeSideDatum p Bs L J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  obtain ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrowJA, hc⟩ := hrow
  have hrowK0 : GGResRowAt ggRowTwoNodeSmallJA p J K :=
    ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrowJA⟩
  have hrowSmall : ggRowTwoNodeSmall p labJ labK := hrowJA.1
  have hJtag : labJ.tag = .A ∨ labJ.tag = .twA := hrowJA.2
  have hrow2 : ggRowTwoNode p labJ labK := hrowSmall.1
  have hKle9 : labK.rank ≤ 9 := hrowSmall.2
  have hp : p.Prime := hH.1.tableB_facts.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have h4K : 4 ≤ labK.rank := ggTWSmallA_rank_ge hp hp2 hJΛ hJtag hrow2
  obtain ⟨-, hKtag, hKrank_eq, hdvdK, hKtdvdM⟩ := l05nQD_row_facts hrow2 h4K
  have hN : labK.rank + 1 = 5 ∨ labK.rank + 1 = 6 ∨ labK.rank + 1 = 7 ∨
      labK.rank + 1 = 9 ∨ labK.rank + 1 = 10 := by
    rcases l05nQD_cell hp hp2 h4K hKle9 hdvdK with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      omega
  have hrowK : GGResRowAt ggRowTwoNode p J K :=
    ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrow2⟩
  have hKdatum : GGResXDatumA p Bs K (labK.rank + 1 - 1) :=
    ggTWSmall_rowdata_K (r₀ := 4) (N := labK.rank + 1) (le_refl 4) hRig hT hLift
      (fun _ => hR) (fun _ => hTw) hH hN (by omega) hJΛ hJl hJtag (by omega) hrowK
  have hKside : GGResTwoNodeSideDatum p Bs K J :=
    (hJ2S G p B Bs x L D J y K hH).2 (l6a_xdatum_of_A hKdatum) hrowK0
  have hN5 : 5 ≤ labK.rank + 1 := by rcases hN with h | h | h | h | h <;> omega
  obtain ⟨n, hLA⟩ :=
    ggTWR2_xdatumA_L hRig hT hLift hR hTw hJ2S hH
      ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrowJA, hc⟩ hL
  have hA : GGTWAligned p (labK.rank + 1) 2 Bs K J L :=
    ggTW_align_two (N := labK.rank + 1) hp2 hBs hN5 hKdatum hLA hKside hL
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  have hJdvd : p ∣ labJ.rank + 3 := by
    rw [hKrank_eq] at hdvdK
    have he : labJ.rank + 2 + 1 = labJ.rank + 3 := by omega
    rwa [he] at hdvdK
  have hpnot : ¬ p ∣ labJ.rank + 1 := by
    intro hd
    have hsub : p ∣ (labJ.rank + 3) - (labJ.rank + 1) := Nat.dvd_sub hJdvd hd
    have he : (labJ.rank + 3) - (labJ.rank + 1) = 2 := by omega
    rw [he] at hsub
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hsub)
  have hZJ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J) := by
    refine hMult ↥J p labJ hp2 hJΛ hJperf hJl ?_
    rcases hrow2 with ⟨hA', hq, hpJ, _⟩ | ⟨htw, hq, hpJ, _⟩ | ⟨hD, -, -, -⟩ |
      ⟨htwD, -, -, -⟩
    · exact Or.inl ⟨hA', hpnot⟩
    · exact Or.inr (Or.inl ⟨htw, hpnot, hq⟩)
    · exfalso
      have htagD : labJ.tag = .D := by simpa using congrArg LargeEvenLabel.tag hD
      rcases hJtag with h | h <;> rw [htagD] at h <;> exact absurd h (by decide)
    · exfalso
      have htagD : labJ.tag = .D := by simpa using congrArg LargeEvenLabel.tag htwD
      rcases hJtag with h | h <;> rw [htagD] at h <;> exact absurd h (by decide)
  have hCard : Nat.card ↥Bs = p ^ (labK.rank + 1 - 1) := by
    simpa using hc
  have hXrank : labK.rank = (labK.rank + 1) - 1 := by omega
  have hJrank : labJ.rank = (labK.rank + 1) - 3 := by omega
  exact ggTWSmallA_close_K (N := labK.rank + 1) hC hPZ hFix hFixK (Or.inr rfl) hp3 hdvdK hN
    hH hyK hJΛ hKΛ hJl hKl hrowSmall hKtag hXrank hJrank hZJ hCard
    (fun _ => ggTWHLAt_nbr_of_autWeylThree hH (hA.autWeylThree_L (by omega)))
    (fun _ => ggTWHLAt_base_of_autWeylThree hH (hA.autWeylThree_K hN5 (by norm_num)))
    hA

theorem ggResTwoNodeLE3Small_of_count
    (hD1 : GGSmallD1Input) (hD2 : GGSmallD2Input) (hLNC : GGLNoncyclicInput)
    (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom 4)
    (hLift : GGTBTorLiftAFrom 4) (hW : GGTBWNormLabelInput) (hR : GGTBXDatumResInput)
    (hTw : GGTWTwA5Open) (hJ2S : GGTBJTwoNodeSmallInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hC : GGTWSmallCells) (hPZ : GGPZInput)
    (hMult : GGTWMultLeaves) (hLoc : GGE6D4TwoNodeLocalInput) (hCells : GGDepED4LowCells)
    (hPZE : GGPZE6Input) (hA5 : LR6A5DepAll) (hOrb : GGResCentBoundInput) (hAll : LR6E6All)
    (hDep : LR6E6DepAll) (hOrbK : GGResCentBoundNbrInput) (hUse : ZS.UseInput)
    (hDim : GGTwoNodeRowDimKnown) (hTCJ : GGTCJKnown) (hX : GGResXDichotomyInput)
    (hNineK : GGNineDepKFixLine) (hAll9 : LR6NineAll) :
    GGResTwoNodeLE3SmallInput := by
  intro G _ _ p B Bs x L D J y K hH hp hF hS hE hP
  rcases hP with ⟨hrowL, hxL, hK3⟩ | ⟨hrowK, hyK, hL3⟩
  · rcases GGResRowAt.smallA_or_E hrowL with hrowA | hrowD
    · by_cases hKA2 : GGResTwoNodeSideDatum p Bs K J ∧ ∃ n : ℕ, GGResXDatumA p Bs K n
      · obtain ⟨n, hKA⟩ := hKA2.2
        exact ggTWSmallA_L_twoA hRig hT hLift hW hR hTw hJ2S hC hPZ hFix hFixK hMult hH
          hrowA hxL hKA2.1 hKA
      · by_cases hK2 : GGResTwoNodeSideDatum p Bs K J
        · rcases ggTWR23_K_typeA_or hRig hT hLift hW hR hTw hJ2S hFix hFixK hC hH
            hrowA hxL hK2 with hKA | ⟨hp3, hcard, hrow5⟩
          · exact absurd ⟨hK2, hKA⟩ hKA2
          · exact ggTwoNodeA5DepL hA5 hOrb hRig hT hLift hW hR hTw hFix hFixK hH hrow5 hxL hK3
              hp3 hcard
        · obtain ⟨hp3, hcard, hrow5⟩ :=
            ggLE3Small_count_L hRig hT hLift hW hR hTw hJ2S hFix hH hrowA hxL hK3 hK2
          exact ggTwoNodeA5DepL hA5 hOrb hRig hT hLift hW hR hTw hFix hFixK hH hrow5 hxL hK3 hp3
            hcard
    · by_cases h7 : Nat.card ↥Bs = 3 ^ 7
      · exact (ggDepED4_false_LE3_L7 hLoc hFix hFixK hH hrowD hxL hK3 h7).elim
      · exact (ggDepED4_false_LE3_L hCells hLoc hFix hFixK hPZE hH hrowD hxL hK3 h7).elim
  · rcases GGResRowAt.smallA_or_E hrowK with hrowA | hrowD
    · obtain ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hr⟩ := hrowA
      by_cases hL2 : GGResTwoNodeSideDatum p Bs L J
      · by_cases hc : Nat.card ↥Bs = p ^ labK.rank
        · exact ggTWSmallA_K_twoA hRig hT hLift hR hTw hJ2S hC hPZ hFix hFixK hMult hH
            ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hr, hc⟩ hyK hL2
        · by_cases hI : GGResXDatumAIndep p Bs K labK.rank
          · exfalso
            have hp : p.Prime := hH.1.tableB_facts.1
            have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
            have h4K : 4 ≤ labK.rank := ggTWSmallA_rank_ge hp hp2 hJΛ hr.2 hr.1.1
            obtain ⟨-, -, -, hdvdK, -⟩ := l05nQD_row_facts hr.1.1 h4K
            have hKle9 : labK.rank ≤ 9 := hr.1.2
            exact ggTwoNodeKIndep_false_of_not_mem (N := labK.rank + 1)
              (ggIndepFixLineLin_of_zs hUse)
              (ggTwoNodeKFixLineFrameInput_of_shared hTCJ hRig hFix hFixK.1 hDim hX)
              hH hF hS hE ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hr.1.1, rfl⟩ hp2
              (by omega) (by omega) hdvdK hyK (by simpa only [Nat.add_sub_cancel] using hI)
          ·
            have hp : p.Prime := hH.1.tableB_facts.1
            have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
            have h4K : 4 ≤ labK.rank := ggTWSmallA_rank_ge hp hp2 hJΛ hr.2 hr.1.1
            obtain ⟨-, hKtag, hKrank_eq, hdvdK, hKtdvdM⟩ := l05nQD_row_facts hr.1.1 h4K
            have hN : labK.rank + 1 = 5 ∨ labK.rank + 1 = 6 ∨ labK.rank + 1 = 7 ∨
                labK.rank + 1 = 9 ∨ labK.rank + 1 = 10 := by
              rcases l05nQD_cell hp hp2 h4K hr.1.2 hdvdK with
                ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
            have hrowK2 : GGResRowAt ggRowTwoNode p J K :=
              ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hr.1.1⟩
            have hKd : GGResXDatumA p Bs K (labK.rank + 1 - 1) :=
              ggTWSmall_rowdata_K (r₀ := 4) (N := labK.rank + 1) (le_refl 4) hRig hT hLift
                (fun _ => hR) (fun _ => hTw) hH hN (by omega) hJΛ hJl hr.2 (by omega) hrowK2
            have hyD : y ∈ D := by
              rw [hH.2.2.2.2.1.2.1]
              exact Subgroup.subset_closure (by simp)
            have hy : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
            have hKs : GGResTwoNodeSideDatum p Bs K J :=
              (hJ2S G p B Bs x L D J y K hH).2 (l6a_xdatum_of_A hKd)
                ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hr⟩
            have hrowN : GGResRowAt
                (fun _ labJ labX => ggRowTwoNode p labJ labX ∧ labX.rank + 1 = labK.rank + 1)
                p J K :=
              ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hr.1.1, rfl⟩
            by_cases h39 : p = 3 ∧ labK.rank = 8
            ·
              have hp3 : p = 3 := h39.1
              have hrank8 : labK.rank = 8 := h39.2
              have hrowNine : GGResRowAt ggRowTwoNodeNine p J K :=
                ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hr.1.1, hp3, hrank8⟩
              have hBsN : Bs ≤ Subgroup.normalizer (K : Set G) :=
                GGInnerDiagOn.le_normalizer (hH.2.2.1.2 y K hH.2.2.2.2.1)
              have hnc : y ∉ (ggBstarComm K Bs).map Bs.subtype :=
                fun hyc => hyK (ggBstarComm_map_subtype_le hBsN hyc)
              have hKd8 : GGResXDatumA p Bs K 8 := by simpa [hrank8] using hKd
              exact ggTwoNodeNineDepK_two_of_orbK hAll9 hOrbK hFix hp3 hH hy
                (fun b hb => hNineK G p B Bs x L D J y K hH hF hS hE hrowNine hnc hL2 hKd8 b hb)
                hKd8 hnc hL2
            · by_cases h36 : p = 3 ∧ labK.rank = 5
              · by_cases hfixK : ∀ b : ↥Bs,
                    (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y
                ·
                  have hp3 : p = 3 := h36.1
                  have hrank5 : labK.rank = 5 := h36.2
                  have hKd5 : GGResXDatumA p Bs K 5 := by simpa [hrank5] using hKd
                  have hKd5' := hKd5
                  obtain ⟨Λ, i1, i2, MK, CK, V, i3, i4, ι, φ, h, α, e, hMK, hWMK, hCK,
                    hlin, hrefl, hpair, ⟨f, hf⟩, hclos⟩ := hKd5
                  letI := i1; letI := i2; letI := i3; letI := i4
                  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
                  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
                  have hpN6 : p ∣ 6 := by rw [hp3]; norm_num
                  have hdep : ¬ LinearIndependent (ZMod p) h :=
                    ggXDatumA_dep_K hp2 hH hy hyK hfixK (N := 6) (by norm_num) hpN6 e hMK
                      hCK hlin hpair hclos
                  have Fdep : GGDepAFrame p 6 (fun i : Fin 5 => h (e i))
                      (fun i : Fin 5 => α (e i)) (ι (Additive.ofMul ⟨y, hy⟩)) :=
                    ggXDatumA_frame_K hp2 hH hy hfixK (N := 6) (by norm_num) hpN6 e hMK
                      hCK hlin hpair hclos hdep
                  have hfin : Module.finrank (ZMod p) V = 5 ∨
                      Module.finrank (ZMod p) V = 6 := by
                    obtain ⟨hb1, hb2⟩ := ggDepA_finrank_bounds Fdep
                    omega
                  have hcardV : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V := by
                    have hVB : Nat.card ↥Bs = Nat.card V := card_eq_of_ggLin ι
                    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
                    rw [Nat.card_zmod] at h
                    rw [hVB, h]
                  have hp5 : Nat.card ↥Bs ≠ p ^ 5 := by simpa [hrank5] using hc
                  have hcard : Nat.card ↥Bs = 3 ^ 6 := by
                    have hpow : p ^ Module.finrank (ZMod p) V = 3 ^ 6 := by
                      rcases hfin with hf6 | hf6
                      · exfalso
                        exact hp5 (by rw [hcardV, hf6])
                      · rw [hf6, hp3]
                    rwa [hcardV]
                  exact ggTwoNodeA5DepK_core hA5 hOrbK hFix hp3 hH hy hcard hKd5' hyK hfixK hL3
                ·
                  have hcell1 : (p = 5 ∧ labK.rank + 1 = 5) ∨ (p = 3 ∧ labK.rank + 1 = 6) ∨
                      (p = 7 ∧ labK.rank + 1 = 7) ∨ (p = 5 ∧ labK.rank + 1 = 10) :=
                    Or.inr (Or.inl ⟨h36.1, by omega⟩)
                  exact absurd (fun b hb =>
                    ggTwoNodeDepKFixLine_of_lin (ggIndepFixLineLin_of_zs hUse) hFix hFixK.1 hDim
                      hLNC (hD1 p (labK.rank + 1) hcell1) hH hrowN hp2
                      (by omega) hdvdK hKs hL2 hKd b hb) hfixK
              ·
                rcases l05nQD_cell hp hp2 h4K hr.1.2 hdvdK with h55 | h36' | h77 | h39' | h510
                · exact (ggTwoNodeSmallDepK_false hOrbK hFix hp2 hH hy hyK
                    (hD2 p (labK.rank + 1) (Or.inl h55)).1
                    (hD2 p (labK.rank + 1) (Or.inl h55)).2 (by omega) hdvdK
                    (by simpa only [Nat.add_sub_cancel] using hc) hKd
                    (fun b hb => ggTwoNodeDepKFixLine_of_lin (ggIndepFixLineLin_of_zs hUse) hFix
                      hFixK.1 hDim hLNC
                      (hD1 p (labK.rank + 1) (Or.inl h55)) hH hrowN hp2 (by omega) hdvdK hKs
                      hL2 hKd b hb) hKs hL2).elim
                · exact absurd (⟨h36'.1, by omega⟩ : p = 3 ∧ labK.rank = 5) h36
                · exact (ggTwoNodeSmallDepK_false hOrbK hFix hp2 hH hy hyK
                    (hD2 p (labK.rank + 1) (Or.inr (Or.inl h77))).1
                    (hD2 p (labK.rank + 1) (Or.inr (Or.inl h77))).2 (by omega) hdvdK
                    (by simpa only [Nat.add_sub_cancel] using hc) hKd
                    (fun b hb => ggTwoNodeDepKFixLine_of_lin (ggIndepFixLineLin_of_zs hUse) hFix
                      hFixK.1 hDim hLNC
                      (hD1 p (labK.rank + 1) (Or.inr (Or.inr (Or.inl h77)))) hH hrowN hp2 (by omega) hdvdK
                      hKs hL2 hKd b hb) hKs hL2).elim
                · exact absurd (⟨h39'.1, by omega⟩ : p = 3 ∧ labK.rank = 8) h39
                · exact (ggTwoNodeSmallDepK_false hOrbK hFix hp2 hH hy hyK
                    (hD2 p (labK.rank + 1) (Or.inr (Or.inr h510))).1
                    (hD2 p (labK.rank + 1) (Or.inr (Or.inr h510))).2 (by omega) hdvdK
                    (by simpa only [Nat.add_sub_cancel] using hc) hKd
                    (fun b hb => ggTwoNodeDepKFixLine_of_lin (ggIndepFixLineLin_of_zs hUse) hFix
                      hFixK.1 hDim hLNC
                      (hD1 p (labK.rank + 1) (Or.inr (Or.inr (Or.inr h510)))) hH hrowN hp2
                      (by omega) hdvdK hKs hL2 hKd b hb) hKs hL2).elim
      · rcases ggLE3Small_count_K hRig hT hLift hR hTw hJ2S hFix hH
          ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hr⟩ hL3 hL2 with
          ⟨hp3, hcard, hrow5⟩ | hrowc
        · exact ggTwoNodeE6L_LE3 hAll hDep hOrb hOrbK hRig hT hLift hR hTw hJ2S hFix hFixK hH hrow5
            hL3 hL2 hp3 hcard
        · exact (ggLE3Small_card_K_false hDim hH hrowc).elim
    · by_cases h7 : Nat.card ↥Bs = 3 ^ 7
      · exact ggResTwoNodeLE3K7_weyl hUse hAll hOrb hFix hFixK hLoc hH hrowD hL3 h7
      · exact (ggDepED4_false_LE3_K hCells hLoc hFix hFixK hPZE hH hrowD hyK hL3 h7).elim

end CFSG.StandardType

end
