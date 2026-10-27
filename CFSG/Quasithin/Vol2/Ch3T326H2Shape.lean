module

public import CFSG.Quasithin.Vol2.Ch8Sec3L0Cent
public import CFSG.Quasithin.Vol2.Ch11SecA02Simple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Vol2.Ch10T326CFsuB
public import CFSG.Quasithin.Vol2.Ch7Bridge326

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem nonempty_quot_equiv_autOn_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnot : ¬ T ≤ Subgroup.normalizer (L : Set G)) {X : Type} [Group X] [IsSimpleGroup X]
    (e : ↥(autOn L (fsuVM T L I)) ≃* X) : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* X) := by
  have hA : IsSimpleGroup ↥(autOn L (fsuVM T L I)) := e.isSimpleGroup
  have hLs := isSimpleGroup_of_not_normal h37 h38 hfsu.simple hfsu.nonabelian hfsu.qtke
    hfsu.faithful hnot
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  let ψ : ↥L →* ↥(autOn L (fsuVM T L I)) :=
    ((conjAct (fsuVM T L I)).comp (Subgroup.inclusion hLN)).codRestrict _
      fun l => ⟨Subgroup.inclusion hLN l, l.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker_le : ψ.ker ≤ CFSG.pCore 2 ↥L := by
    intro l hl
    have hC : (l : G) ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
      A4.conjAct_eq_one_iff.mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hl))
    rw [← subgroupOf_pCoreOf, Subgroup.mem_subgroupOf, ← inf_pCoreOf_fsuL0 hfsu.maximal.1]
    exact ⟨l.2, fsuL0_inf_centralizer_le_of_fsu h37 h38 hfsu hnot ⟨le_fsuL0 T L l.2, hC⟩⟩
  have hle_ker : CFSG.pCore 2 ↥L ≤ ψ.ker := by
    have hn : ((CFSG.pCore 2 ↥L).map ψ).Normal :=
      (inferInstance : (CFSG.pCore 2 ↥L).Normal).map ψ hψs
    rcases hA.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥L).map ψ) with hb | ht
    · exact fun x hx => (Subgroup.map_eq_bot_iff _).mp hb hx
    · exfalso
      obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L))
      apply hab
      have hall : ∀ q : ↥L ⧸ CFSG.pCore 2 ↥L, q = 1 := by
        intro q
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
        have hl : ψ l ∈ (CFSG.pCore 2 ↥L).map ψ := by rw [ht]; exact Subgroup.mem_top _
        obtain ⟨o, ho, hol⟩ := hl
        have hk : o⁻¹ * l ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hol, inv_mul_cancel]
        have := (CFSG.pCore 2 ↥L).mul_mem ho (hker_le hk)
        rw [mul_inv_cancel_left] at this
        exact (QuotientGroup.eq_one_iff l).mpr this
      rw [hall a, hall b]
  have hker : ψ.ker = CFSG.pCore 2 ↥L := le_antisymm hker_le hle_ker
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).trans e)⟩

theorem shape701_of_concl326ThreeIv
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hlt : L < fsuL0 T L) [IsMulCommutative ↥(fsuVM T L I)] (h4 : Concl326ThreeIv T L I) :
    Shape701 L := by
  obtain ⟨n, -, -, -, -, hlie, -⟩ := h4
  have hn := two_le_of_lieModel_psl_two hlie
  rcases hlie with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hK2 : Nat.card K = 2 ^ n := by simpa using hcard
    have : CharP K 2 := by
      have : Fintype K := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK2])
    have hs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
      Vol2.Ch11.SecA.isSimpleGroup_SL_two hK2 hn
    have hnot : ¬ T ≤ Subgroup.normalizer (L : Set G) := fun hT =>
      hlt.ne (le_antisymm (le_conjClosure L T) (conjClosure_le fun _ hg z hz =>
        (Subgroup.mem_normalizer_iff.mp (hT hg) z).mp hz))
    obtain ⟨e'⟩ := nonempty_quot_equiv_autOn_of_fsu h37 h38 hfsu hnot
      (e.trans (Setup.Family.statedProjSL_two_equiv K))
    exact Or.inl ⟨n, hn, K, inferInstance, inferInstance, hK2, ⟨e'⟩⟩
  all_goals exact absurd h0 (by norm_num)

theorem stmt7_0_1_shapeC_of (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hshape : Stmt7_0_1_shape) : Stmt7_0_1_shapeC := by
  intro G _ _ T L I hfsu hlt h3
  rcases h3 with ⟨x, hx, h3⟩ | ⟨_, h4⟩
  · exact hshape G T L (CFSG.conjugate I x) (fsu_conjugate hfsu hx) hlt h3
  · exact shape701_of_concl326ThreeIv h37 h38 hfsu hlt h4

end CFSG.Quasithin.H13
