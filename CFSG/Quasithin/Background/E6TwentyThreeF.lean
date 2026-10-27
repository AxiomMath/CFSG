module

public import CFSG.Quasithin.Background.C1PackC129Set
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E6SixSeven
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.Quasithin.Background.C2Basic

public section

namespace CFSG.Quasithin.E6.A3Push

open CFSG.QuasithinUnique CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSubnormal_trans {A B C : Subgroup G} (h₁ : IsSubnormal A B) (h₂ : IsSubnormal B C) :
    IsSubnormal A C :=
  h₁.trans h₂

theorem mem_normalizer_of_mem_pCoreOf {H B : Subgroup G} (hB : IsBlock2 H B) {y : G}
    (hy : y ∈ pCoreOf 2 H) : y ∈ Subgroup.normalizer (B : Set G) := by
  have hn := (C1Pack.isBlock2_normal_sup_pCore hB).2
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).1 hn)
    (le_sup_right (a := B) hy)

theorem commutator_mem_blockQ_of_mem_pCoreOf {H B : Subgroup G} (hB : IsBlock2 H B) {y b : G}
    (hy : y ∈ pCoreOf 2 H) (hb : b ∈ B) : b * y * b⁻¹ * y⁻¹ ∈ blockQ B := by
  rw [C1Pack.blockQ_eq_inf_pCoreOf hB]
  have hyN := mem_normalizer_of_mem_pCoreOf hB hy
  have hbH : b ∈ H := hB.2.1 hb
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h1 : y * b⁻¹ * y⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hyN b⁻¹).mp (inv_mem hb)
    rw [show b * y * b⁻¹ * y⁻¹ = b * (y * b⁻¹ * y⁻¹) by group]
    exact mul_mem hb h1
  · have hON : b ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      le_normalizer_pCoreOf 2 H hbH
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp hON y).mp hy) (inv_mem hy)

theorem charTwo_of_pCoreOf_le {K X : Subgroup G} (hK : CharTwo K) (hOX : pCoreOf 2 K ≤ X)
    (hXK : X ≤ K) : CharTwo X := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hK hXK hOX

omit [Finite G] in
theorem isChi0Block_map_conj {K B : Subgroup G} (hB : IsChi0Block K B) {k : G} (hk : k ∈ K) :
    IsChi0Block K (B.map (MulAut.conj k).toMonoidHom) := by
  obtain ⟨hb, htype⟩ := hB
  refine ⟨IsBlock2.conjByElt_of_mem hb hk, ?_⟩
  rcases htype with ⟨n, hn, hlin⟩ | h3 | h5
  · exact Or.inl ⟨n, hn, Lin2.IsLin2Type.map_equiv hlin (MulAut.conj k)⟩
  · exact Or.inr (Or.inl (L238.IsAltType.map_equiv h3 (MulAut.conj k)))
  · exact Or.inr (Or.inr (L238.IsAltType.map_equiv h5 (MulAut.conj k)))

@[expose] def chi0BlocksOutside (K Q M : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ C1GN.chiBlocksOutside K Q M ∧ IsChi0Block K B}

theorem le_normalizer_sSup_chi0Blocks {K Q M : Subgroup G} (hK : CharTwo K) (hSQ : IsSQTKTC K)
    (hQ : IsSylowTwoOf Q K) (hQM : Q ≤ M) :
    K ≤ Subgroup.normalizer ((sSup (chi0BlocksOutside K Q M) : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : ∀ g ∈ K, (sSup (chi0BlocksOutside K Q M)).map (MulAut.conj g).toMonoidHom ≤
      sSup (chi0BlocksOutside K Q M) := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun B hB => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨C1Pack.conj_mem_chiBlocksOutside hK hSQ hQ hQM hB.1 hg, ?_⟩
    exact isChi0Block_map_conj hB.2 hg
  refine le_antisymm (hle k hk) ?_
  intro y hy
  have h := hle k⁻¹ (inv_mem hk) ⟨y, hy, rfl⟩
  refine ⟨(MulAut.conj k⁻¹).toMonoidHom y, h, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem inf_centralizer_le_of_chi0Blocks (hC129 : ASC129Statement G) {K Q M : Subgroup G}
    (hK : CharTwo K) (hSQ : IsSQTKIn K) (hQ : IsSylowTwoOf Q K) (hQM : Q ≤ M)
    (hcgs : cgsIn K Q ≤ M) :
    K ⊓ Subgroup.centralizer ((sSup (chi0BlocksOutside K Q M) : Subgroup G) : Set G) ≤ M := by
  classical
  have hSQ' : IsSQTKTC K := C1GN.isSQTKTC_iff_sqtkGroup.mpr hSQ
  set B0 : Subgroup G := sSup (chi0BlocksOutside K Q M) with hB0
  set N : Subgroup G := K ⊓ Subgroup.centralizer (B0 : Set G) with hN
  have hKB0 := le_normalizer_sSup_chi0Blocks hK hSQ' hQ hQM
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ K, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
      intro g hg n hn
      obtain ⟨hnK, hnC⟩ := Subgroup.mem_inf.mp hn
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg hnK) (inv_mem hg), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hb' : g⁻¹ * b * g ∈ B0 := by
        have := (Subgroup.mem_normalizer_iff.mp (hKB0 (inv_mem hg)) b).mp hb
        simpa using this
      have h := (Subgroup.mem_centralizer_iff.mp hnC) _ hb'
      calc b * (g * n * g⁻¹) = g * ((g⁻¹ * b * g) * n) * g⁻¹ := by group
        _ = g * (n * (g⁻¹ * b * g)) * g⁻¹ := by rw [h]
        _ = g * n * g⁻¹ * b := by group
    intro n
    refine ⟨key k hk n, fun h => ?_⟩
    have := key k⁻¹ (inv_mem hk) _ h
    simpa [mul_assoc] using this
  have hNK : N ≤ K := inf_le_left
  have hQK : Q ≤ K := hQ.1
  set X : Subgroup G := N ⊔ Q with hX
  have hXK : X ≤ K := sup_le hNK hQK
  have hOQ : pCoreOf 2 K ≤ Q := IsSylowTwoOf.pCoreOf_le hQ
  have hXc : CharTwo X := charTwo_of_pCoreOf_le hK (hOQ.trans le_sup_right) hXK
  have hXs : IsSQTKIn X := IsSQTKIn.mono hSQ hXK
  have hQX : IsSylowTwoOf Q X := Lin2.isSylowTwoOf_of_le_of_le hQ le_sup_right hXK
  have hcgsX : cgsIn X Q ≤ X ⊓ M :=
    le_inf (cgsIn_le X Q) ((E6.cgsIn_mono hXK).trans hcgs)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := hC129 X Q (X ⊓ M) hXs hXc hQX hcgsX inf_le_left
  have hLbM : ∀ i, Lb i ≤ M := by
    intro i
    by_contra hiM
    obtain ⟨hch, -, hJ⟩ := hLb i
    have hLN : Lb i ≤ N :=
      Vol2Native.L239.le_of_isShort2_of_le_sup hQ.isPGroup (hQK.trans hKN) hch.1.1 hch.1.2.1
    have hsubX : IsSubnormal (Lb i) X := IsBlock2.isSubnormal hch.1
    have hsubN : IsSubnormal (Lb i) N := A4.subnormal_of_le_of_le hsubX hLN le_sup_left
    have hNn : IsSubnormal N K := IsSubnormal.step hNK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN) (IsSubnormal.refl K)
    have hsubK : IsSubnormal (Lb i) K := isSubnormal_trans hsubN hNn
    have hblK : IsBlock2 K (Lb i) :=
      ⟨hch.1.1, hLN.trans hNK, (isSubnormal_iff_subgroupOf (hLN.trans hNK)).mp hsubK⟩
    have hmem : Lb i ∈ chi0BlocksOutside K Q M :=
      ⟨⟨C1GN.isChiBlock_of_isChi0Block hblK hch, hJ, hiM⟩, ⟨hblK, hch.2⟩⟩
    have hLB0 : Lb i ≤ B0 := le_sSup hmem
    have hab : ∀ y ∈ Lb i, ∀ z ∈ Lb i, y * z = z * y := fun y hy z hz =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hLN hz)).2) y (hLB0 hy)
    obtain ⟨hlt, -⟩ := hch.1.1.2.2.2.2
    apply (lt_irrefl (blockU (Lb i)))
    calc blockU (Lb i) ≤ blockZ (Lb i) := by
          intro u hu
          refine Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
          exact hab y hy u ((C1.blockU_le_blockQ hch.1.1).trans (C1.blockQ_le _) hu)
      _ < blockU (Lb i) := hlt
  intro g hg
  have hgX : g ∈ X := (le_sup_left : N ≤ N ⊔ Q) hg
  obtain ⟨m, hm, y, hy, rfl⟩ := hprod g hgX
  refine M.mul_mem hm.2 (Subgroup.list_prod_mem (K := M) fun z hz => ?_)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hz
  exact hLbM j (hy j)

end CFSG.Quasithin.E6.A3Push
