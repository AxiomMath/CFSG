module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameK
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTPFrameK_of_nbr {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    (hM : GGE6DepModelKnown) (hLB : GGLBalanceInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hinn : GGInnerDiagAll 3 B Bs x L D J)
    (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJp : 3 ∣ Nat.card ↥J) {y' : G}
    {K' : Subgroup G} (hnbr' : GGNbr 3 B x D J y' K') {lab₀ : LargeEvenLabel}
    (hlab₀ : GGE6DepLabel lab₀) (hΛ : LargeEvenInLambda2 lab₀) (hcardBs : Nat.card Bs = 3 ^ 6)
    (hK'lab : GGHasLabel lab₀ (↥K' ⧸ Subgroup.center ↥K')) :
    LargeEvenMarking ↥K' (fun lab _ _ _ _ _ => lab = lab₀) ∧ J ≤ K' ∧
      Bs ⊓ Subgroup.centralizer (K' : Set G) = Subgroup.zpowers y' ∧
      ∃ κ : Additive ↥Bs →+ E6Dep.Vec6, E6Dep.GGE6DepKFrame Bs K' y' κ := by
  classical
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC := hcfg.2.1.2.2.2
  have hinnK' : GGInnerDiagOn Bs K' := hinn.2 y' K' hnbr'
  have hy'B : y' ∈ B := hnbr'.1.2.1
  have hy'Bs : y' ∈ Bs := hcfg.2.1.1 hy'B
  have hy1 : y' ≠ 1 := hnbr'.1.2.2.1
  have hKy' : K' ≤ Subgroup.centralizer ({y'} : Set G) := hnbr'.1.2.2.2.1
  have hy'Kc : y' ∈ Subgroup.centralizer (K' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKy' hk)
  have hxK' : x ∉ Subgroup.centralizer (K' : Set G) := by
    intro hx
    apply hnbr'.2.2.2
    have hle : Subgroup.zpowers x ≤ Subgroup.centralizer (K' : Set G) :=
      Subgroup.zpowers_le.mpr hx
    rw [Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle]
    exact bot_le
  have hJK : J ≤ K' := le_of_ggNbr hLB hcfg.1 hcfg.2.2 hJp hnbr'
  have hker : Bs ⊓ Subgroup.centralizer (K' : Set G) = Subgroup.zpowers y' :=
    GGNbr.bstar_inf_centralizer_eq_zpowers hcfg hnbr' hCJ hJK
  let P₀ : LargeEvenMarkProp ↥K' := fun lab' _ _ I _ θ =>
    lab' = lab₀ ∧ Bs ≤ Subgroup.normalizer (K' : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ
  have hmark₀ : LargeEvenMarking ↥K' P₀ :=
    ggInnerDiagOn_relabel hRig hinnK' hΛ hK'lab
  have hmark : LargeEvenMarking ↥K' (fun lab _ _ _ _ _ => lab = lab₀) :=
    largeEvenMarking_mono (P := P₀) (by
      intro lab R _ I F θ h
      exact h.1) hmark₀
  obtain ⟨κ, hκ⟩ :=
    ggE6Dep_frameK hRig hM hy1 hBs hSC hcardBs hlab₀ hmark hinnK' hker
  exact ⟨hmark, hJK, hker, κ, hκ⟩

end CFSG.StandardType

end
