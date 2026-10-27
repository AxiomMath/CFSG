module

public import CFSG.RankThree.GF2n.Tim81.Sec5.TwoPoint
public import CFSG.RankThree.GF2n.Tim81.Sec6.Stmts
public import CFSG.GroupTheory.Commutator.SupNormalizer
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen
import CFSG.RankThree.GF2n.Tim81.Sec6.KWModule

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.QuotMod
open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

private theorem sq_eq_one_of_mem_sigmaSet (hS : Sec6Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) : ∀ u ∈ U, u * u = 1 := by
  obtain ⟨g, rfl, -⟩ := hU
  intro u hu
  have hE := CFSG.CGT.Timmesfeld75.isElemAbelian_conjSubgroup
    hS.sec5.toRootHyp.toHyp.elem g
  simpa [pow_two] using hE.2 u hu

private theorem stmt63_n_eq {q n n₀ : ℕ} (hq : 1 < q)
    (h : q ^ (2 * n + 1) = q ^ (2 * n₀ + 1)) : n = n₀ := by
  have hmn : 2 * n + 1 = 2 * n₀ + 1 := Nat.pow_right_injective hq h
  omega

private theorem mem_normalizer_kOf_of_commutator_mem {H : Subgroup G} {u : G}
    (huH : ∀ x ∈ H, ⁅u, x⁆ ∈ kOf V H) (hu2 : u * u = 1) :
    u ∈ Subgroup.normalizer (kOf V H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have h1 : ⁅u, k⁆ ∈ kOf V H := huH k (kOf_le V H hk)
    rw [show u * k * u⁻¹ = ⁅u, k⁆ * k by rw [commutatorElement_def]; group]
    exact (kOf V H).mul_mem h1 hk
  · intro hk
    have hxK : u * k * u⁻¹ ∈ kOf V H := hk
    have h1 : ⁅u, u * k * u⁻¹⁆ ∈ kOf V H := huH _ (kOf_le V H hxK)
    have h2 : ⁅u, u * k * u⁻¹⁆ * (u * k * u⁻¹) ∈ kOf V H :=
      (kOf V H).mul_mem h1 hxK
    have h3 : ⁅u, u * k * u⁻¹⁆ * (u * k * u⁻¹) = k := by
      rw [commutatorElement_def]
      rw [show u * (u * k * u⁻¹) * u⁻¹ * (u * k * u⁻¹)⁻¹ * (u * k * u⁻¹) =
        (u * u) * k * (u * u)⁻¹ by group, hu2]
      group
    rwa [h3] at h2

private structure Stmt63Basic (M V : Subgroup G) (g g' : G) (U U' : Subgroup G) : Prop where
  hU : U ∈ sigmaSet M V
  hU' : U' ∈ sigmaSet M V
  hVg : conjSubgroup g V ∈ sigmaSet M V
  hVg' : conjSubgroup g' V ∈ sigmaSet M V
  hSH : Sec45Shape M V (hOf M V g) g
  hSH' : Sec45Shape M V (hOf M V g') g'
  hPU : ⁅Pc M V, U⁆ ≤ Pc M V ⊓ Subgroup.centralizer (U' : Set G)
  hPU' : ⁅Pc M V, U'⁆ ≤ Pc M V ⊓ Subgroup.centralizer (U : Set G)
  hU'_le_centU : U' ≤ Subgroup.centralizer (U : Set G)
  hP_central : Pc M V ⊓ Subgroup.centralizer (U : Set G) =
    Pc M V ⊓ kOf V (hOf M V g)
  hP_central' : Pc M V ⊓ Subgroup.centralizer (U' : Set G) =
    Pc M V ⊓ kOf V (hOf M V g')
  hy : ∃ y ∈ hOf M V g, conjSubgroup y V = U ∧ conjSubgroup y V ≠ V
  hy' : ∃ y' ∈ hOf M V g', conjSubgroup y' V = U' ∧ conjSubgroup y' V ≠ V

private theorem stmt63_basic (hS : Sec6Hyp M V) {U U' : Subgroup G} {g g' : G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hUg : U = conjSubgroup g V) (hUg' : U' = conjSubgroup g' V)
    (hcomm : ⁅U, U'⁆ = ⊥) : Stmt63Basic M V g g' U U' := by
  have hU0 : U ∈ sigmaSet M V := hU
  have hU'0 : U' ∈ sigmaSet M V := hU'
  have hVg : conjSubgroup g V ∈ sigmaSet M V := by rwa [hUg] at hU
  have hVg' : conjSubgroup g' V ∈ sigmaSet M V := by rwa [hUg'] at hU' 
  have hSH : Sec45Shape M V (hOf M V g) g := hS.sec5.shape hVg
  have hSH' : Sec45Shape M V (hOf M V g') g' := hS.sec5.shape hVg'
  have h513 := hS.res.s513 M V hS.sec5
  have hcomm' : ⁅U', U⁆ = ⊥ := by rwa [Subgroup.commutator_comm]
  have hPU : ⁅Pc M V, U⁆ ≤ Pc M V ⊓ Subgroup.centralizer (U' : Set G) := by
    rcases h513 U hU U' hU' with ⟨-, h⟩ | ⟨hL2, -⟩
    · exact h
    · exfalso
      exact (IsL2Gen.commutator_ne_bot hL2) hcomm
  have hPU' : ⁅Pc M V, U'⁆ ≤ Pc M V ⊓ Subgroup.centralizer (U : Set G) := by
    rcases h513 U' hU' U hU with ⟨-, h⟩ | ⟨hL2, -⟩
    · exact h
    · exfalso
      exact (IsL2Gen.commutator_ne_bot hL2) hcomm'
  have hU'_le_centU : U' ≤ Subgroup.centralizer (U : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm'
  obtain ⟨y, hyH, -, hVy, -⟩ :=
    hS.sec5.toRootHyp.exists_mem_conj_eq_of_eq_sup hSH.Pc_le hSH.hH
  have hyU : conjSubgroup y V = U := by rw [← hVy, ← hUg]
  have hyV_ne : conjSubgroup y V ≠ V := by
    rw [hyU]
    exact ne_of_mem_sigmaSet hS.sec5.toRootHyp hU
  have hP_central : Pc M V ⊓ Subgroup.centralizer (U : Set G) =
      Pc M V ⊓ kOf V (hOf M V g) := by
    rw [← hyU]
    exact hSH.Pc_inf_centralizer_conj hS.sec5.toRootHyp hyH hyV_ne
  obtain ⟨y', hy'H', -, hVy', -⟩ :=
    hS.sec5.toRootHyp.exists_mem_conj_eq_of_eq_sup hSH'.Pc_le hSH'.hH
  have hy'U' : conjSubgroup y' V = U' := by rw [← hVy', ← hUg']
  have hy'V_ne : conjSubgroup y' V ≠ V := by
    rw [hy'U']
    exact ne_of_mem_sigmaSet hS.sec5.toRootHyp hU'
  have hP_central' : Pc M V ⊓ Subgroup.centralizer (U' : Set G) =
      Pc M V ⊓ kOf V (hOf M V g') := by
    rw [← hy'U']
    exact hSH'.Pc_inf_centralizer_conj hS.sec5.toRootHyp hy'H' hy'V_ne
  refine ⟨hU0, hU'0, hVg, hVg', hSH, hSH', hPU, hPU', hU'_le_centU,
    hP_central, hP_central', ?_, ?_⟩
  · exact ⟨y, hyH, hyU, hyV_ne⟩
  · exact ⟨y', hy'H', hy'U', hy'V_ne⟩

private theorem stmt63_n2_false (hS : Sec6Hyp M V) {H : Subgroup G} {g : G}
    (hSH : Sec45Shape M V H g) {U' : Subgroup G}
    (htwo : ∀ u' ∈ U', (∀ x ∈ H, ⁅u', x⁆ ∈ kOf V H) ∧
      u' ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G))
    (hKU'_not_le : ¬ ⁅kOf V H, U'⁆ ≤ Tim79a.xOf V H)
    (hKcard2 : Nat.card (kOf V H) = Nat.card V ^ 4)
    (hWcard : Nat.card (Tim79a.xOf V H) = Nat.card V ^ 4) : False := by
  have hW_le_K : Tim79a.xOf V H ≤ kOf V H := by
    rw [kOf]
    refine le_inf (Tim79a.xOf_le_H (hS.sec5.toRootHyp.toHyp.le_Pc.trans hSH.Pc_le)) ?_
    rw [Subgroup.le_centralizer_iff_isMulCommutative]
    exact (hSH.isElemAbelian hS.sec5.toRootHyp).1
  have hK_eq_W : kOf V H = Tim79a.xOf V H := by
    exact (Subgroup.eq_of_le_of_card_ge hW_le_K (by rw [hKcard2, hWcard])).symm
  have hU'_le_centW : U' ≤ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
    fun u hu => (htwo u hu).2
  have hWU'_eq_bot : ⁅Tim79a.xOf V H, U'⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hU'_le_centW
  exact hKU'_not_le (by rw [hK_eq_W, hWU'_eq_bot]; exact bot_le)

private theorem stmt63_n3_false (hS : Sec6Hyp M V) {H : Subgroup G} {g : G}
    (hSH : Sec45Shape M V H g) {F : Type} [Field F] [Fintype F] [CharP F 2]
    {l : ℕ} {hl : Fintype.card F = 2 ^ (2 * l)} {ψ : HBar V H ≃* SL(2, F)}
    (hw : Sec45ShapeWith M V H F l hl ψ) {U' : Subgroup G}
    (hU' : U' ∈ sigmaSet M V)
    (htwo : ∀ u' ∈ U', (∀ x ∈ H, ⁅u', x⁆ ∈ kOf V H) ∧
      u' ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G))
    (hKU'_not_le : ¬ ⁅kOf V H, U'⁆ ≤ Tim79a.xOf V H)
    (hKcard3 : Nat.card (kOf V H) = Nat.card V ^ 8)
    (hWcard : Nat.card (Tim79a.xOf V H) = Nat.card V ^ 4) : False := by
  have hKU'_le' : ⁅kOf V H, U'⁆ ≤ Tim79a.xOf V H := by
    refine (Subgroup.commutator_le).mpr ?_
    intro k hk u' hu'U'
    have hu'2 : u' * u' = 1 := sq_eq_one_of_mem_sigmaSet hS hU' u' hu'U'
    have hu'K : u' ∈ Subgroup.normalizer (kOf V H : Set G) :=
      mem_normalizer_kOf_of_commutator_mem (htwo u' hu'U').1 hu'2
    have hu'W : u' ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
      Subgroup.centralizer_le_normalizer (Tim79a.xOf V H : Set G)
        (htwo u' hu'U').2
    have hcomm := Sec45Shape.commutator_mem_xOf_of_mul_self_mem hS.sec5.toRootHyp hSH hw
      hu'K hu'W (htwo u' hu'U').1 (by rw [hu'2]; exact (kOf V H).one_mem) hKcard3
      hWcard k hk
    rw [show ⁅k, u'⁆ = ⁅u', k⁆⁻¹ from (commutatorElement_inv u' k).symm]
    exact (Tim79a.xOf V H).inv_mem hcomm
  exact hKU'_not_le hKU'_le'

private theorem stmt63_step4_false (hS : Sec6Hyp M V) {H : Subgroup G} {g : G}
    (hSH : Sec45Shape M V H g) {U U' : Subgroup G}
    (hP_central : Pc M V ⊓ Subgroup.centralizer (U : Set G) = Pc M V ⊓ kOf V H)
    (hP_split : Pc M V = (Pc M V ⊓ Subgroup.centralizer (U : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (U' : Set G)))
    (hCU_eq : Pc M V ⊓ Subgroup.centralizer (U : Set G) =
      Pc M V ⊓ Subgroup.centralizer (U' : Set G)) : False := by
  have hP_eq_CPU : Pc M V = Pc M V ⊓ Subgroup.centralizer (U : Set G) := by
    calc Pc M V = (Pc M V ⊓ Subgroup.centralizer (U : Set G)) ⊔
          (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) := hP_split
      _ = (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) ⊔
          (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) := by rw [hCU_eq]
      _ = Pc M V ⊓ Subgroup.centralizer (U' : Set G) := sup_idem _
      _ = Pc M V ⊓ Subgroup.centralizer (U : Set G) := by rw [hCU_eq]
  have hP_le_K : Pc M V ≤ kOf V H := by
    have h : Pc M V = Pc M V ⊓ kOf V H := by
      rw [← hP_central]
      exact hP_eq_CPU
    exact inf_eq_left.mp h.symm
  have hb4 := hSH.card_Pc_inf_kOf hS.sec5.toRootHyp
  rw [inf_eq_left.mpr hP_le_K] at hb4
  have hq2 : Nat.card V ^ 2 = 1 := by
    have hb4' : Nat.card ↥(Pc M V) * Nat.card V ^ 2 =
        Nat.card ↥(Pc M V) * 1 := by
      rw [mul_one]
      exact hb4
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥(Pc M V))) hb4'
  have hq1 : Nat.card V = 1 := by
    rcases Nat.pow_eq_one.mp hq2 with h | h
    · exact h
    · omega
  have hq4 := hS.sec5.toRootHyp.four_le_card
  omega

private theorem stmt63_commutator_P_U'_eq (hS : Sec6Hyp M V)
    {H H' : Subgroup G} {g g' : G} (hSH : Sec45Shape M V H g)
    (hSH' : Sec45Shape M V H' g') {U U' : Subgroup G} {y' : G}
    (hPU' : ⁅Pc M V, U'⁆ ≤ Pc M V ⊓ Subgroup.centralizer (U : Set G))
    (hy'H' : y' ∈ H') (hy'U' : conjSubgroup y' V = U') (hy'V_ne : conjSubgroup y' V ≠ V)
    (hP_central : Pc M V ⊓ Subgroup.centralizer (U : Set G) = Pc M V ⊓ kOf V H)
    (hP_split : Pc M V = (Pc M V ⊓ Subgroup.centralizer (U : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (U' : Set G)))
    (hKU'_le : ⁅kOf V H, U'⁆ ≤ Tim79a.xOf V H) :
    ⁅Pc M V, U'⁆ = Pc M V ⊓ Tim79a.xOf V H := by
  have hB_le_normA : Pc M V ⊓ Subgroup.centralizer (U' : Set G) ≤
      Subgroup.normalizer
        (Pc M V ⊓ Subgroup.centralizer (U : Set G) : Set G) := by
    intro b hb
    have hbP : b ∈ Pc M V := (Subgroup.mem_inf.mp hb).1
    change b ∈ Subgroup.normalizer
      ((Pc M V ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G)
    rw [hP_central]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hbP, le_normalizer_kOf V H (hSH.Pc_le hbP)⟩
  have hB_le_centU' : Pc M V ⊓ Subgroup.centralizer (U' : Set G) ≤
      Subgroup.centralizer (U' : Set G) := inf_le_right
  have hP_U'_eq : ⁅Pc M V, U'⁆ =
      ⁅Pc M V ⊓ Subgroup.centralizer (U : Set G), U'⁆ := by
    conv_lhs => rw [hP_split]
    exact CFSG.commutator_sup_eq_commutator_left
      (A := Pc M V ⊓ Subgroup.centralizer (U : Set G))
      (B := Pc M V ⊓ Subgroup.centralizer (U' : Set G)) (U := U')
      hB_le_normA hB_le_centU'
  have hPU'_le_W : ⁅Pc M V, U'⁆ ≤ Pc M V ⊓ Tim79a.xOf V H := by
    rw [hP_U'_eq, hP_central]
    refine le_inf ?_ ?_
    · exact (Subgroup.commutator_mono inf_le_left le_rfl).trans (hPU'.trans inf_le_left)
    · exact (Subgroup.commutator_mono inf_le_right le_rfl).trans hKU'_le
  have hPU'_eq_W' : ⁅Pc M V, U'⁆ = Pc M V ⊓ Tim79a.xOf V H' := by
    rw [← hy'U']
    exact hSH'.commutator_Pc_conj_eq hS.sec5.toRootHyp hy'H' hy'V_ne
  have hcardW : Nat.card ↥(Pc M V ⊓ Tim79a.xOf V H) = Nat.card V ^ 3 :=
    hSH.card_inf_Pc_xOf hS.sec5.toRootHyp
  have hcardW' : Nat.card ↥(Pc M V ⊓ Tim79a.xOf V H') = Nat.card V ^ 3 :=
    hSH'.card_inf_Pc_xOf hS.sec5.toRootHyp
  have hcard : Nat.card ↥(⁅Pc M V, U'⁆) =
      Nat.card ↥(Pc M V ⊓ Tim79a.xOf V H) := by
    rw [hPU'_eq_W', hcardW', hcardW]
  exact Subgroup.eq_of_le_of_card_ge hPU'_le_W (by rw [hcard])

private theorem stmt63_PK_eq (hS : Sec6Hyp M V)
    {H H' : Subgroup G} {g g' : G} (hSH : Sec45Shape M V H g)
    (hSH' : Sec45Shape M V H' g') {U U' : Subgroup G} {y y' : G}
    (hPU' : ⁅Pc M V, U'⁆ ≤ Pc M V ⊓ Subgroup.centralizer (U : Set G))
    (hyH : y ∈ H) (hyU : conjSubgroup y V = U) (hyV_ne : conjSubgroup y V ≠ V)
    (hy'H' : y' ∈ H') (hy'U' : conjSubgroup y' V = U') (hy'V_ne : conjSubgroup y' V ≠ V)
    (hP_central : Pc M V ⊓ Subgroup.centralizer (U : Set G) = Pc M V ⊓ kOf V H)
    (hP_split : Pc M V = (Pc M V ⊓ Subgroup.centralizer (U : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (U' : Set G)))
    (hKU'_le : ⁅kOf V H, U'⁆ ≤ Tim79a.xOf V H) :
    Pc M V ⊓ kOf V H = Pc M V ⊓ kOf V H' := by
  have hPU'_eq_W := stmt63_commutator_P_U'_eq hS hSH hSH' hPU' hy'H' hy'U' hy'V_ne
    hP_central hP_split hKU'_le
  have hPU_eq_W : ⁅Pc M V, U⁆ = Pc M V ⊓ Tim79a.xOf V H := by
    rw [← hyU]
    exact hSH.commutator_Pc_conj_eq hS.sec5.toRootHyp hyH hyV_ne
  have hPU_eq : ⁅Pc M V, U⁆ = ⁅Pc M V, U'⁆ := by rw [hPU_eq_W, ← hPU'_eq_W]
  have hCP_U : Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U⁆ : Subgroup G) : Set G) =
      Pc M V ⊓ kOf V H := by
    simpa [hyU] using
      hSH.Pc_inf_centralizer_commutator hS.sec5.toRootHyp hyH hyV_ne
  have hCP_U' : Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U'⁆ : Subgroup G) : Set G) =
      Pc M V ⊓ kOf V H' := by
    simpa [hy'U'] using
      hSH'.Pc_inf_centralizer_commutator hS.sec5.toRootHyp hy'H' hy'V_ne
  have hPK_eq : Pc M V ⊓ kOf V H = Pc M V ⊓ kOf V H' := by
    rw [← hCP_U, ← hCP_U', hPU_eq]
  exact hPK_eq

private theorem stmt63_centralizers_eq (hS : Sec6Hyp M V)
    {H H' : Subgroup G} {g g' : G} (hSH : Sec45Shape M V H g)
    (hSH' : Sec45Shape M V H' g') {U U' : Subgroup G} {y y' : G}
    (hPU' : ⁅Pc M V, U'⁆ ≤ Pc M V ⊓ Subgroup.centralizer (U : Set G))
    (hyH : y ∈ H) (hyU : conjSubgroup y V = U) (hyV_ne : conjSubgroup y V ≠ V)
    (hy'H' : y' ∈ H') (hy'U' : conjSubgroup y' V = U') (hy'V_ne : conjSubgroup y' V ≠ V)
    (hP_central : Pc M V ⊓ Subgroup.centralizer (U : Set G) = Pc M V ⊓ kOf V H)
    (hP_central' : Pc M V ⊓ Subgroup.centralizer (U' : Set G) = Pc M V ⊓ kOf V H')
    (hP_split : Pc M V = (Pc M V ⊓ Subgroup.centralizer (U : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (U' : Set G)))
    (hKU'_le : ⁅kOf V H, U'⁆ ≤ Tim79a.xOf V H) :
    Pc M V ⊓ Subgroup.centralizer (U : Set G) =
      Pc M V ⊓ Subgroup.centralizer (U' : Set G) := by
  have hPK_eq := stmt63_PK_eq hS hSH hSH' hPU' hyH hyU hyV_ne
    hy'H' hy'U' hy'V_ne hP_central hP_split hKU'_le
  rw [hP_central, hP_central', hPK_eq]

theorem Sec6Hyp.twoPoint_of_commute (hS : Sec6Hyp M V) {H : Subgroup G} {g : G}
    (hSH : Sec45Shape M V H g) {U U' : Subgroup G} (hU' : U' ∈ sigmaSet M V)
    (hU'_le_centU : U' ≤ Subgroup.centralizer (U : Set G))
    (hPU' : ⁅Pc M V, U'⁆ ≤ Pc M V ⊓ Subgroup.centralizer (U : Set G))
    (hP_central : Pc M V ⊓ Subgroup.centralizer (U : Set G) = Pc M V ⊓ kOf V H)
    (hUg : U = conjSubgroup g V) :
    ∀ u' ∈ U', (∀ x ∈ H, ⁅u', x⁆ ∈ kOf V H) ∧
      u' ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) := by
  intro u' hu'U'
  have hu'M : u' ∈ M := (hS.sec5.le_M_of_mem_sigmaSet hU').1 hu'U'
  have hu'2 : u' ^ 2 ^ 1 = 1 := by
    have h := sq_eq_one_of_mem_sigmaSet hS hU' u' hu'U'
    simpa [pow_two] using h
  have hu'C : u' ∈ Subgroup.centralizer (U : Set G) := hU'_le_centU hu'U'
  have hu'N : u' ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.centralizer_le_normalizer (U : Set G) hu'C
  have hnormU : Subgroup.normalizer (U : Set G) = conjSubgroup g M := by
    rw [hUg]
    change Subgroup.normalizer ((V : Subgroup G).map (MulAut.conj g).toMonoidHom : Set G) =
      (M : Subgroup G).map (MulAut.conj g).toMonoidHom
    rw [← Subgroup.map_normalizer_eq_of_bijective V (MulAut.conj g).bijective,
      hS.sec5.toRootHyp.toHyp.normalizer_eq]
  have hu'M_g : u' ∈ conjSubgroup g M := by
    rw [← hnormU]
    exact hu'N
  have hu'Pc : u' ∈ Subgroup.normalizer (conjSubgroup g (Pc M V) : Set G) := by
    have h := (hS.sec5.root g).toHyp.le_normalizer_Pc hu'M_g
    rwa [Pc_conjSubgroup] at h
  have hu'P : ∀ p ∈ Pc M V, ⁅u', p⁆ ∈ kOf V H := by
    intro p hp
    have hmem : ⁅p, u'⁆ ∈ ⁅Pc M V, U'⁆ :=
      Subgroup.commutator_mem_commutator hp hu'U'
    have hmem' := hPU' hmem
    have hmem'' : ⁅p, u'⁆ ∈ Pc M V ⊓ Subgroup.centralizer (U : Set G) := hmem'
    rw [hP_central] at hmem''
    have hmemK : ⁅p, u'⁆ ∈ kOf V H := hmem''.2
    rw [show ⁅u', p⁆ = ⁅p, u'⁆⁻¹ from (commutatorElement_inv p u').symm]
    exact (kOf V H).inv_mem hmemK
  have hu'Kcomm : ∀ x ∈ H, ⁅u', x⁆ ∈ kOf V H :=
    Sec45Shape.commutator_mem_kOf_of_fix_Pc hS.sec5.toRootHyp hSH
      hu'M hu'P hu'Pc
  have hu'W : u' ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
    Sec45Shape.mem_centralizer_xOf_of_fix_Pc hS.sec5.toRootHyp hSH
      hu'M hu'P hu'Pc hu'2
  exact ⟨hu'Kcomm, hu'W⟩

theorem Sec6Hyp.stmt63 (hS : Sec6Hyp M V) (h61 : Sec6.Stmt61b M V) : ∀ n : ℕ, Nat.card ↥(Pc M V) = Nat.card V ^ (2 * n + 1) → n ≤ 3 → NoCommPair M V := by
  intro n hnP hn3
  obtain ⟨n₀, hn₀2, hn₀P, hKcard⟩ := h61
  have hn_eq : n = n₀ := by
    apply stmt63_n_eq (q := Nat.card V)
    · have := hS.sec5.toRootHyp.four_le_card
      omega
    · exact hnP.symm.trans hn₀P
  subst n
  have hn_cases : n₀ = 2 ∨ n₀ = 3 := by omega
  intro U hU U' hU' hcomm
  obtain ⟨g, hUg, hHg⟩ := hU
  obtain ⟨g', hUg', hHg'⟩ := hU'
  have hU0 : U ∈ sigmaSet M V := ⟨g, hUg, hHg⟩
  have hU'0 : U' ∈ sigmaSet M V := ⟨g', hUg', hHg'⟩
  obtain ⟨-, -, hVg, hVg', hSH, hSH', hPU, hPU', hU'_le_centU,
    hP_central, hP_central', hy, hy'⟩ :=
    stmt63_basic hS hU0 hU'0 hUg hUg' hcomm
  obtain ⟨y, hyH, hyU, hyV_ne⟩ := hy
  obtain ⟨y', hy'H', hy'U', hy'V_ne⟩ := hy'
  have htwo := hS.twoPoint_of_commute hSH hU'0 hU'_le_centU hPU' hP_central hUg
  have h58 := hS.res.s58 M V hS.sec5 g g' hVg' hVg (by rwa [← hUg, ← hUg'])
  rcases h58 with hHeq | hPsplit
  · obtain ⟨p, hpP, hp⟩ := hS.res.i5a M V hS.sec5 (hOf M V g) g y' hSH (by
        rw [hHeq]
        exact hy'H')
      (by rw [hy'U']; exact ne_of_mem_sigmaSet hS.sec5.toRootHyp hU'0)
    refine ⟨p, hpP, ?_⟩
    rw [← hy'U', hUg]
    exact hp
  · have hP_split : Pc M V = (Pc M V ⊓ Subgroup.centralizer (U : Set G)) ⊔
        (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) := by
      simpa [← hUg, ← hUg'] using hPsplit
    exfalso
    by_cases hKU'_le : ⁅kOf V (hOf M V g), U'⁆ ≤ Tim79a.xOf V (hOf M V g)
    · have hCU_eq := stmt63_centralizers_eq hS hSH hSH' hPU' hyH hyU hyV_ne
        hy'H' hy'U' hy'V_ne hP_central hP_central' hP_split hKU'_le
      exact stmt63_step4_false hS hSH hP_central hP_split hCU_eq
    · obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hSH.shape
      letI := hField
      letI := hFintype
      letI := hCharP
      have hWcard : Nat.card (Tim79a.xOf V (hOf M V g)) = Nat.card V ^ 4 := by
        rw [hw.card_W, hw.card_V, ← pow_mul]
        congr 1
        omega
      rcases hn_cases with rfl | rfl
      · have hK := (hKcard g hVg).2.2
        have hKcard2 : Nat.card (kOf V (hOf M V g)) = Nat.card V ^ 4 := by
          simpa using hK
        exact stmt63_n2_false hS hSH htwo hKU'_le hKcard2 hWcard
      · have hK := (hKcard g hVg).2.2
        have hKcard3 : Nat.card (kOf V (hOf M V g)) = Nat.card V ^ 8 := by
          simpa using hK
        exact stmt63_n3_false hS hSH hw hU'0 htwo hKU'_le hKcard3 hWcard

end CFSG.RankThree.GF2n.Tim81
