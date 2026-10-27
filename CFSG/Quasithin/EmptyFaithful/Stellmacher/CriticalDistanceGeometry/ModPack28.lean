module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Statements
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Index
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.FaithfulY
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.OffenderB10
public import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits

namespace F53.Stellmacher

@[expose] def ModPack28 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X Q P R Y A : Subgroup G),
    Q = pCoreOf 2 X → Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)) →
    IsSylowTwoOf P X → Q ≤ R → R ≤ P → P ≤ Subgroup.normalizer (R : Set G) → Q.relIndex R = 4 →
    IsElemAbelian 2 Y → Y ≤ Q → X ≤ Subgroup.normalizer (Y : Set G) →
    X ⊓ Subgroup.centralizer (Y : Set G) = Q →
    A ≤ R → IsElemAbelian 2 A → ¬ A ≤ Q →
    (Y ⊓ Subgroup.centralizer (A : Set G)).relIndex Y ≤ (A ⊓ Q).relIndex A →
    (∀ g ∈ R, g ^ 2 ∈ Q) ∧ ¬ (Y ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (X : Set G))

section At

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem isElemAbelian_quasithinOmegaOneCenter (T : Subgroup G) :
    IsElemAbelian 2 (quasithinOmegaOneCenter T) := by
  have hle : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun _ hx => hx.1
  have hcomm : ∀ a ∈ quasithinOmegaOneCenter T, ∀ b ∈ quasithinOmegaOneCenter T,
      a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hle hb).2 a (hle ha).1
  refine ⟨isMulCommutative_subgroup_iff.mpr hcomm, fun x hx => ?_⟩
  exact (mem_quasithinOmegaOneCenter_iff.mp hx).2.2

theorem hss28ModAt_of_modPack28 (hmp : ModPack28) (hA : F53Amalgam H M S) : Hss28ModAt H M := by
  intro δ ν hν hvδ hle hJ hfaith
  have hvν : vtype ν = true := by
    have := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj δ ν from hν)
    rw [hvδ] at this
    simpa using this
  have hδν : δ ∈ nbrs ν := SimpleGraph.Adj.symm (show (graph (H ⊔ M) H M).Adj δ ν from hν)
  set Y : Subgroup G := quasithinOmegaOneCenter (Qv δ) with hY
  have hYQ : Y ≤ Qv δ := fun y hy => (mem_quasithinOmegaOneCenter_iff.mp hy).1
  have hQν : Qv ν ≤ stab δ ⊓ stab ν :=
    le_inf (Qv_le_stab_of_mem_nbrs hA hδν) (pCoreOf_le 2 _)
  have hQPδ : Qv δ ≤ stab δ ⊓ stab ν := Qv_le_inf hA hν
  have hYabel : IsElemAbelian 2 Y := isElemAbelian_quasithinOmegaOneCenter _
  obtain ⟨A, hAmax, hAQ⟩ : ∃ A : Subgroup G, IsMaxElemAbelian (Qv ν) A ∧ ¬ A ≤ Qv δ := by
    by_contra hcon
    push Not at hcon
    exact hJ (iSup_le fun A => iSup_le fun hA' => hcon A hA')
  have hoff := EmptyFaithful.Stellmacher.OrdinaryProofs.offender_index_le_of_isMaxElemAbelian hAmax
    (hYQ.trans hle) hYabel
  have hQC : Qv δ ≤ Subgroup.centralizer (Y : Set G) := by
    rw [← hfaith]; exact inf_le_right
  have hAC : A ⊓ Qv δ ≤ A ⊓ Subgroup.centralizer (Y : Set G) := inf_le_inf_left _ hQC
  have h8 : (Qv δ).relIndex (stab δ ⊓ stab ν) = 8 := relIndex_Qv_inf_false hA hν hvδ
  have h2 : (Qv ν).relIndex (stab ν ⊓ stab δ) = 2 := relIndex_Qv_inf_true hA hδν hvν
  rw [inf_comm] at h2
  have hmul := Subgroup.relIndex_mul_relIndex (Qv δ) (Qv ν) (stab δ ⊓ stab ν) hle hQν
  rw [h8, h2] at hmul
  have h4 : (Qv δ).relIndex (Qv ν) = 4 := by omega
  obtain ⟨hsq, hnc⟩ := hmp G (stab δ) (Qv δ) (stab δ ⊓ stab ν) (Qv ν) Y A rfl
    (quot_stab_five hA hvδ) (sylow_stab_inf_left hA hν) hle hQν
    (inf_le_right.trans (le_normalizer_pCoreOf 2 (stab ν))) h4 hYabel hYQ
    ((le_normalizer_pCoreOf 2 (stab δ)).trans (normalizer_le_normalizer_omegaOneCenter _))
    hfaith (hAmax.1) hAmax.2.1 hAQ
    (hoff.trans (Subgroup.relIndex_le_of_le_left hAC (Subgroup.index_ne_zero_of_finite (H := (A ⊓ Qv δ).subgroupOf A))))
  refine ⟨hsq, fun hcen => hnc fun y hy => ?_⟩
  obtain ⟨hyY, hyP⟩ := Subgroup.mem_inf.mp hy
  have hyPδν : y ∈ stab δ ⊓ stab ν := hQPδ (hYQ hyY)
  have hy2 : y ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hyY).2.2
  have hyΩ : y ∈ quasithinOmegaOneCenter (stab δ ⊓ stab ν) :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hyPδν, hyP, hy2⟩
  exact (hcen hyΩ).2

end At

theorem Hss28Mod_of_modPack28 (hmp : ModPack28) : ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S → Hss28ModAt H M :=
  
  fun _ _ _ _ _ _ hA => hss28ModAt_of_modPack28 hmp hA

end F53.Stellmacher

end CFSG.Quasithin
