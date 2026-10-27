module

public import CFSG.Quasithin.MS93.S4A441C2
import CFSG.Quasithin.MS93.S4A441WMod
import CFSG.Quasithin.MS93.S4A432S
import CFSG.Quasithin.MS93.S45Vtx
public import CFSG.Quasithin.MS93.S46Gen
public import CFSG.Quasithin.MS93.S4A431F

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement MatrixGroups

namespace W441

private theorem relIndex_sup_le_card {H : Type*} [Group H] {A Z : Subgroup H} [Finite A]
    (hAZ : A ≤ Subgroup.normalizer (Z : Set H)) : Z.relIndex (A ⊔ Z) ≤ Nat.card A := by
  refine Nat.card_le_card_of_surjective
    (fun a : ↥A => ((⟨a, Subgroup.mem_sup_left a.2⟩ : ↥(A ⊔ Z)) :
      ↥(A ⊔ Z) ⧸ Z.subgroupOf (A ⊔ Z))) fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H x =>
    have hx : (x : H) ∈ ((A ⊔ Z : Subgroup H) : Set H) := x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A Z hAZ] at hx
    obtain ⟨a, ha, z, hz, haz⟩ := hx
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    have haz' : a * z = (x : H) := haz
    rw [← haz', inv_mul_cancel_left]
    exact hz

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

private theorem map_conj_eq {α μ : Vtx (puAmalgam h.le)} {k : (puAmalgam h.le).Universal}
    (hk : k ∈ stab (puAmalgam h.le) α) :
    (⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α).map
        (MulAut.conj k).toMonoidHom =
      ⁅ZM (puAmalgam h.le) (k • μ), Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α := by
  rw [Subgroup.map_sup, Subgroup.map_commutator, ← zm_smul,
    MS93.map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ α hk),
    MS93.map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ α hk)]

theorem ltil_le_normalizer (hfull : IsSL3Full M T L) {α α' μ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hN : ∀ k ∈ stab (puAmalgam h.le) α, ZM (puAmalgam h.le) α' ≤ Subgroup.normalizer
      ((⁅ZM (puAmalgam h.le) (k • μ), Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal)) :
    Ltil h.le L α ≤ Subgroup.normalizer
      ((⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) := by
  set X := ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α with hX
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h20 hb0 hc
  have hC : conjCl (stab (puAmalgam h.le) α) (ZM _ α') ≤
      Subgroup.normalizer (X : Set (puAmalgam h.le).Universal) := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨z, hz, rfl⟩
    have h1 := hN g⁻¹ (inv_mem hg) hz
    rw [← map_conj_eq h (inv_mem hg), ← Subgroup.map_equiv_normalizer_eq, mem_map_conj,
      inv_inv] at h1
    exact h1
  exact (S46.ltil_le_of_normal h hfull hc.1 (adj_geo_one_of_isCritical _ hb0 hc)
    (conjCl_le_of_le hZs) (le_normalizer_conjCl _ _) (le_conjCl _ _)
    (zm_le_qv_geo_one _ h20 hb0 hc) (ms22_iii _ h20 hb0 h.centHyp hc).2.2).trans hC

private theorem commutator_zm_qv_le_vv {α μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hd : (puAmalgam h.le).treeGraph.dist α μ ≤ 2) :
    ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ Vv (puAmalgam h.le) α := by
  have hZ : ZM (puAmalgam h.le) μ ≤ Vv _ α :=
    le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist α ρ ≤ 2}) => Zv (puAmalgam h.le) ρ) μ hd
      (zv_of_isMVtx _ hμ).ge
  exact (Subgroup.commutator_mono hZ le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab _ α).trans (stab_le_normalizer_vv h α)))

theorem relIndex_le {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) (hb : 2 < critDist (puAmalgam h.le))
    {α μ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hμ : IsMVtx _ μ)
    (hd : (puAmalgam h.le).treeGraph.dist α μ = 2) :
    (ZM (puAmalgam h.le) α).relIndex
        (⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α) ≤
      Fintype.card F ^ 2 := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  set β := geo (puAmalgam h.le) α μ 1 with hβ
  have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one _ (by omega)
  have hβμ : (puAmalgam h.le).treeGraph.Adj β μ :=
    SimpleGraph.dist_eq_one_iff_adj.mp (by rw [hβ, dist_geo_right _ (by omega), hd])
  have hle : ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ Usup (puAmalgam h.le) μ β := by
    rw [Usup, zv_of_isMVtx _ hμ]
    exact Subgroup.commutator_mono le_rfl (qv_le_qv _ h.hyp20 hα hαβ)
  have hUs : Usup (puAmalgam h.le) μ β ≤ stab _ μ := by
    rw [Usup, Subgroup.commutator_le]
    intro a ha c hc
    have ha' : a ∈ stab (puAmalgam h.le) μ := by
      rw [zv_of_isMVtx _ hμ] at ha
      exact qv_le_stab _ μ (zm_le_qv_self _ hμ h.critDist_pos ha)
    have hc' : c ∈ stab (puAmalgam h.le) μ := qv_le_stab_of_adj _ hβμ hc
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha' hc')
      (Subgroup.inv_mem _ ha')) (Subgroup.inv_mem _ hc')
  have := finite_stab h hμ
  have : Finite ↥(Usup (puAmalgam h.le) μ β) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hUs)
  have : Finite ↥⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hN : ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    (((commutator_zm_qv_le_vv h hμ hd.le).trans (vv_le_qv h hb hα)).trans
      (qv_le_stab _ α)).trans (stab_le_normalizer_zm _ α)
  calc _ ≤ Nat.card ↥⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ := relIndex_sup_le_card hN
    _ ≤ Nat.card ↥(Usup (puAmalgam h.le) μ β) := Subgroup.card_le_of_le hle
    _ ≤ Fintype.card F ^ 2 := card_usup_le_sq h hfull hφ hμ hβμ.symm

theorem commutator_mem_zm {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) (hb : 4 < critDist (puAmalgam h.le))
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {X : Subgroup (puAmalgam h.le).Universal}
    (hXL : Ltil h.le L α ≤ Subgroup.normalizer (X : Set (puAmalgam h.le).Universal))
    (hZX : ZM (puAmalgam h.le) α ≤ X) (hXV : X ≤ Vv (puAmalgam h.le) α)
    (hcard : (ZM (puAmalgam h.le) α).relIndex X ≤ Fintype.card F ^ 2)
    {l : (puAmalgam h.le).Universal} (hl : l ∈ Ltil h.le L α) {v : (puAmalgam h.le).Universal}
    (hv : v ∈ X) : ⁅l, v⁆ ∈ ZM (puAmalgam h.le) α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨n, hn⟩ := hφ.1
  have : CharP F 2 := FFC.charP_two_of_card_pow (by rw [Nat.card_eq_fintype_card, hn])
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero] at hn
      exact absurd hn (Fintype.one_lt_card (α := F)).ne'
    · exact h0
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hα
  have hLs : Ltil h.le L α ≤ stab _ α := ltil_le_stab h α
  have := finite_stab h hα
  have : Finite ↥(Ltil h.le L α) := Finite.of_injective _ (Subgroup.inclusion_injective hLs)
  have hXs : X ≤ stab _ α := hXV.trans ((vv_le_qv h (by omega) hα).trans (qv_le_stab _ α))
  have : Finite ↥X := Finite.of_injective _ (Subgroup.inclusion_injective hXs)
  set θ : ↥(Ltil h.le L α) →* SL(3, F) := (toSL3 ψ).comp (Subgroup.inclusion hLs) with hθ
  have hθs : Function.Surjective θ := by
    intro g
    obtain ⟨l, hl, hlg⟩ := exists_ltil_toSL3_eq h hfull hα hψs hψ g
    exact ⟨⟨l, hl⟩, hlg⟩
  have hker : IsPGroup 2 θ.ker := by
    intro k
    have hkQ : ((k : ↥(Ltil h.le L α)) : (puAmalgam h.le).Universal) ∈ Qv _ α :=
      (S46.toSL3_eq_one_iff_mem_qv h hφ hα hψ _).mp (MonoidHom.mem_ker.mp k.2)
    obtain ⟨m, hm⟩ := S46.isPGroup_qv_of_isMVtx h hα ⟨_, hkQ⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hm
    simpa using this
  have hE := S45.isElemAbelian_vi _ h.hyp20 h.critDist_pos (δ := α) (i := 2) (by omega)
  have hcomm := vv_comm_eq_bot h hb hα
  refine W441.commutator_mem_of_perfect hXL ((hLs.trans (stab_le_normalizer_zm _ α))) hZX
    (fun v hv w hw => ?_) (fun v hv => ?_) (ltil_perfect h hα) hn hn1 θ hθs hker hcard hl hv
  · have h1 := Subgroup.commutator_mem_commutator (hXV hv) (hXV hw)
    rw [hcomm, Subgroup.mem_bot] at h1
    rw [h1]
    exact (ZM _ α).one_mem
  · rw [← pow_two, hE.2 v (hXV hv)]
    exact (ZM _ α).one_mem

end Vertex

end W441

namespace C441

theorem s441C2Wlog_holds : S441C2Wlog := by
  intro G _ _ M T L h F _ _ φ hH hb α α' μ hc _ hconj x hx _ hxB
  by_contra hcon
  push Not at hcon
  have hφ := hH.2.2
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hα : IsMVtx _ α := hc.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨g, hgμ, hgα⟩ := hconj
  have hdμ : (puAmalgam h.le).treeGraph.dist α μ = 2 := by
    have h1 := MS93.dist_smul (puAmalgam h.le) g μ α
    rw [hgμ, hgα] at h1
    rw [tdist_comm, ← h1, dist_geo _ (by omega)]
  have hμ : IsMVtx _ μ := by
    have : μ = g⁻¹ • α := by rw [← hgμ, inv_smul_smul]
    rw [this, isMVtx_smul]
    exact hα
  have hXV : ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      Vv (puAmalgam h.le) α :=
    sup_le (W441.commutator_zm_qv_le_vv h hμ hdμ.le) (zm_le_vv h hα)
  apply hxB
  rw [mem_bloc_iff h (by omega) hα]
  refine ⟨hXV (Subgroup.mem_sup_left hx), fun l hl => ?_⟩
  rw [← commutatorElement_inv]
  exact inv_mem (W441.commutator_mem_zm h hφ hb hα (W441.ltil_le_normalizer h hfull hc hcon)
    le_sup_right hXV (W441.relIndex_le h hφ (by omega) hα hμ hdμ) hl (Subgroup.mem_sup_left hx))

end C441

end CFSG.Quasithin.MS93.S4A
