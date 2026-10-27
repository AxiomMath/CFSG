module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Pump
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Norm
public import CFSG.Mathlib.GroupTheory.ThreeComponentCover
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxClaim

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

theorem gLBConj_eq_of_mulEquiv_nineJ
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    {M : Subgroup G} (hM : GLAPComponent 3 (Subgroup.centralizer ({B.b 2} : Set G)) M)
    (he : Nonempty (↥(nineJ K (B.b 2)) ≃* (↥M ⧸ GLAPPrimeCore 3 ↥M)))
    {t : G} (ht : t ∈ Subgroup.centralizer ({B.b 2} : Set G)) : GLBConj t M = M := by
  obtain ⟨e⟩ := he
  by_contra hne
  have hJcore : GLAPPrimeCore 3 ↥(nineJ K (B.b 2)) = ⊥ :=
    nineJ_primeCore_eq_bot hstd hB hrec
  have iso : (↥(nineJ K (B.b 2)) ⧸ GLAPPrimeCore 3 ↥(nineJ K (B.b 2))) ≃*
      ((↥M ⧸ GLAPPrimeCore 3 ↥M) ⧸ (⊥ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M))) :=
    (QuotientGroup.quotientMulEquivOfEq hJcore).trans
      ((QuotientGroup.quotientBot).trans (e.trans (QuotientGroup.quotientBot).symm))
  exact false_of_three_component_diagonal hstd hB hrec hfus hM ht hne (Z := ⊥) bot_le ⟨iso⟩

theorem conj_mem_nineJ_sup_of_mem_dQ
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    {L : Subgroup G} (hL : GLAPComponent 3 (Subgroup.centralizer ({B.b 2} : Set G)) L)
    (hbd : b₀ ∈ dQ L)
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({b₀} : Set G)) (nineJ K (B.b 2)))
    {g : G} (hg : g ∈ Subgroup.centralizer ({B.b 2} : Set G)) {x : G}
    (hx : x ∈ nineJ K (B.b 2)) :
    g * x * g⁻¹ ∈
      nineJ K (B.b 2) ⊔ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) := by
  have hb3 : b₀ ^ 3 = 1 := by
    rw [← hstd.2.1.1]
    exact pow_orderOf_eq_one b₀
  have hLJ : L ≤ nineJ K (B.b 2) ⊔
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) :=
    CFSG.GroupTheory.le_sup_glaPPrimeCoreOf_of_glaPComponent_of_mem_dQ hL hb3 hbd hJ
  have hJL : nineJ K (B.b 2) ≤ L := hJ.1.trans inf_le_left
  have hON : L ≤ Subgroup.normalizer
      (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) : Set G) :=
    hL.1.trans (CFSG.LocalAnalysis.GLTheoremB.le_normalizer_glaPPrimeCoreOf 3 _)
  have hsup : nineJ K (B.b 2) ⊔ GLAPPrimeCoreOf 3 L = L := by
    refine le_antisymm (sup_le hJL (Subgroup.map_subtype_le _)) fun l hl => ?_
    have hmem : l ∈ ((nineJ K (B.b 2) ⊔
        GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) : Subgroup G) : Set G) :=
      hLJ hl
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hJL.trans hON)] at hmem
    obtain ⟨j, hj, o, ho, rfl⟩ := Set.mem_mul.mp hmem
    have hoL : o ∈ L := by simpa using L.mul_mem (L.inv_mem (hJL hj)) hl
    exact Subgroup.mul_mem_sup hj
      (CFSG.LocalAnalysis.GLTheoremA.L62.inf_glaPPrimeCoreOf_le Nat.prime_three hON ⟨hoL, ho⟩)
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.cover_facts Nat.prime_three hJL hsup
  have iso : Nonempty (↥(nineJ K (B.b 2)) ≃* (↥L ⧸ GLAPPrimeCore 3 ↥L)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq (nineJ_primeCore_eq_bot hstd hB hrec)).trans
      QuotientGroup.quotientBot).symm.trans e⟩
  have hconj : GLBConj g⁻¹ L = L :=
    gLBConj_eq_of_mulEquiv_nineJ hstd hB hrec hfus hL iso
      (Subgroup.inv_mem (Subgroup.centralizer ({B.b 2} : Set G)) hg)
  have hxL : g * x * g⁻¹ ∈ L := by
    rw [← hconj, CFSG.LocalAnalysis.GLTheoremB.mem_gLBConj]
    convert hJL hx using 1
    group
  exact hLJ hxL

theorem t5Nine92Norm_of_pumpupTrivial
    (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h : ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E → KProper
        InCatalog G → IsCharTwoType G → ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → RecOutTwD5 B b₀ →
        Fus42 B b₀ → Odd (Nat.card ↥(Subgroup.centralizer (E : Set G))) → ∀ L : Subgroup G,
        GLAPComponent 3 (Subgroup.centralizer ({B.b 2} : Set G)) L → b₀ ∈ Subgroup.normalizer (L :
        Set G) → GLAPComponent 3 (L ⊓ Subgroup.centralizer ({b₀} : Set G)) (nineJ K (B.b 2)) → b₀ ∈
        dQ L) : T5Nine92Norm := by
  intro G _ _ b₀ K E hstd hKproper hchar B hB hrec hfus hodd g hg x hx
  obtain ⟨L, hL, -, hb0N, hJ⟩ :=
    exists_pComponent_centralizer_b_two hstd hKproper hchar hB hrec hfus hSch
  have hbd : b₀ ∈ dQ L :=
    h G b₀ K E hstd hKproper hchar B hB hrec hfus hodd L hL hb0N hJ
  exact conj_mem_nineJ_sup_of_mem_dQ hstd hB hrec hfus hL hbd hJ hg hx

end CFSG.StandardType.FrameRoute.FS81

end
