module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav
  CFSG.RankThree.PartOne.KE

noncomputable section

private theorem twTr_mem_normalizer_commutator {G : Type} [Group G] {M : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (M : Set G)) :
    x ∈ Subgroup.normalizer ((⁅M, M⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  have hx' : Subgroup.map (MulAut.conj x).toMonoidHom M = M := hx
  calc (⁅M, M⁆).map (MulAut.conj x).toMonoidHom
      = ⁅M.map (MulAut.conj x).toMonoidHom, M.map (MulAut.conj x).toMonoidHom⁆ := by
        rw [Subgroup.map_commutator]
    _ = ⁅M, M⁆ := by rw [hx']


theorem le_normalizer_codeComponent {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {m : Fin 6} (γ : ExcRaw.Root m → Fin τ.rank → ℤ)
    (hγ : ∀ i, IsRoot τ (γ i)) (c : Finset (ExcRaw.Root m)) :
    fullThreeTorus S ≤ Subgroup.normalizer (codeComponent S γ c : Set (ModGL τ L)) := by
  have hroots : ∀ α ∈ codeRoots γ c, IsRoot τ α := by
    rintro δ ⟨i, -, rfl | rfl⟩
    · exact hγ i
    · exact isRoot_neg_iff.mpr (hγ i)
  intro x hx
  have hxT : x ∈ S.D.torus := hx.1
  have hxtg : x ∈ torusGroup τ L :=
    (mem_twistedTorusOf (n := S.D.n) (Φ := S.D.Φ)).1 hxT |>.1
  have hroot : x ∈ Subgroup.normalizer (rootSpan τ L (codeRoots γ c) : Set (ModGL τ L)) :=
    CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hroots hxtg
  have hΓ : x ∈ Subgroup.normalizer (S.Γ : Set (ModGL τ L)) :=
    twTr_mem_normalizer_commutator (Subgroup.le_normalizer (LangDatum.torus_le_model S.D hxT))
  have hinf : x ∈ Subgroup.normalizer
      ((rootSpan τ L (codeRoots γ c) ⊓ S.Γ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hroot, hΓ⟩
  exact twTr_mem_normalizer_commutator hinf

theorem exists_compNormal_modelFrame_of_core {m : Fin 6} {τ : Tag} (hO : ExcCoreOccurs m τ)
    (hM : ExcCoreMarked m τ) (hC : ExcCoreCent m τ) (hI : ExcCoreInside m τ)
    (hN : ExcCoreNormalizer m τ) (hA : ExcCoreAmbient m τ)
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) (hS : NegLangTwo S)
    {T₀ : Subgroup (ModGL τ L)} (d : ExcCoordDatum S T₀ m) :
    ∃ mf : ModelFrame S.Γ T₀ (excRaw m), mf.CompNormal := by
  refine ⟨{ coord := d.coord
            component := codeComponent S d.γ
            component_le := fun c _ => codeComponent_le_Γ S d.γ c
            marked := hM S hS d
            occurs_iff := hO S hS d
            cent_eq := hC S hS d
            inside_eq := hI S hS d
            normalizer_eq := hN S hS d
            ambientNormalizer_eq := hA S hS d }, ?_⟩
  intro c _
  exact d.le_fullThreeTorus.trans (le_normalizer_codeComponent S d.γ d.isRoot c)

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
