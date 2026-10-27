module

public import CFSG.Quasithin.Vol2.Ch10SecABasicCent
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem commutator_conjugate_le_centralizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ Subgroup.centralizer (L : Set G) := by
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hU := (ha t ht htn).2.2
  intro x hx
  rw [← conjugate_commutator_fsuVM (le_fsuM T L ht), mem_conjugate_iff] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have htn' : t⁻¹ ∉ Subgroup.normalizer (L : Set G) := fun h =>
    htn (by simpa using (Subgroup.normalizer _).inv_mem h)
  have hl' : t * l * t⁻¹ ∈ CFSG.conjugate L t := by
    rw [← conjugate_eq_of_not_mem h37 h38 hyp ht htn (T.inv_mem ht) htn', mem_conjugate_iff]
    simpa [mul_assoc] using hl
  have hc := Subgroup.mem_centralizer_iff.mp (hU hx) _ hl'
  have := congrArg (fun y => t⁻¹ * y * t) hc
  simpa [mul_assoc] using this

theorem stmt10_1_1_structure (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I) :
    fsuVM T L I ≤ fsuM T L ∧ IsPrimeReduced 2 ((fsuVM T L I).subgroupOf (fsuM T L)) ∧
    ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) →
      fsuVM T L I = ⁅fsuVM T L I, L⁆ ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ∧
      ⁅fsuVM T L I, L⁆ ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G) ∧
      ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ Subgroup.centralizer (L : Set G) ∧
      (⁅fsuVM T L I, L⁆ ⊔ fsuCVM T L I) ⊓ (⁅fsuVM T L I, CFSG.conjugate L t⁆ ⊔ fsuCVM T L I) =
        fsuCVM T L I := by
  obtain ⟨hVM, hR2⟩ := h322 G T L I hyp.fsu
  refine ⟨hVM, hR2, fun t ht htn => ?_⟩
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  obtain ⟨-, hinf, hU⟩ := ha t ht htn
  have hconj : CFSG.conjugate (fsuUL T L I) t = ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
    conjugate_commutator_fsuVM (le_fsuM T L ht)
  rw [hconj] at hinf
  exact ⟨fsuVM_eq_sup h37 h38 hyp ht htn, hU,
    commutator_conjugate_le_centralizer h37 h38 hyp ht htn, hinf⟩

theorem nonempty_quot_equiv_of_autOn (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {X : Type} [Group X]
    [IsSimpleGroup X] (e : ↥(autOn L (fsuVM T L I)) ≃* X) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* X) := by
  have hA : IsSimpleGroup ↥(autOn L (fsuVM T L I)) := e.isSimpleGroup
  have hLs := isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.faithful hyp.not_normal
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
    rw [← subgroupOf_pCoreOf, Subgroup.mem_subgroupOf, ← inf_pCoreOf_fsuL0 hyp.fsu.maximal.1]
    exact ⟨l.2, fsuL0_inf_centralizer_le h37 h38 hyp ⟨le_fsuL0 T L l.2, hC⟩⟩
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

end CFSG.Quasithin.Vol2.Ch10.SecA
