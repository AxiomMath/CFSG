module

public import CFSG.Quasithin.Vol2.Ch10SecB5Three
public import CFSG.Quasithin.Vol2.Ch10SecA1011C
public import CFSG.Quasithin.Vol2.Ch10SecBSetup
public import CFSG.Quasithin.Vol2.Ch10StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem le_fsuM_of_unique (hU : IsUniqueM (fsuL0 T L ⊔ T1 T L) (fsuM T L)) {X : Subgroup G}
    (hX : fsuL0 T L ⊔ T1 T L ≤ X) (hX2 : pCoreOf 2 X ≠ ⊥) : X ≤ fsuM T L := by
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hX2
  have h := hU.2 M' ⟨hM'.1, hX.trans hM'.2⟩
  rw [← h]
  exact hM'.2

theorem T1_le_normalizer_conjugate (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) :
    T1 T L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) := by
  intro s hs
  have hts : t * s * t⁻¹ ∈ T1 T L :=
    (Subgroup.mem_normalizer_iff.mp (T1_normal h37 h38 hyp ht) s).mp hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [SecA.mem_conjugate_iff, SecA.mem_conjugate_iff]
  have hN := Subgroup.mem_normalizer_iff.mp hts.2 (t * h * t⁻¹)
  have e : t * (s * h * s⁻¹) * t⁻¹ = t * s * t⁻¹ * (t * h * t⁻¹) * (t * s * t⁻¹)⁻¹ := by group
  rw [e]
  exact hN

omit [Finite G] in
theorem pCoreOf_normalizer_ne_bot' {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    pCoreOf 2 (Subgroup.normalizer (P : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  apply hP1
  refine le_bot_iff.mp (h ▸ ?_)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hP

theorem two_of_unique (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I)
    (hU : IsUniqueM (fsuL0 T L ⊔ T1 T L) (fsuM T L)) :
    (∀ K : Subgroup G, IsLi T L K → Subgroup.normalizer (Vi T L I K : Set G) ≤ fsuM T L) ∧
      Subgroup.normalizer (L : Set G) ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hloc := hyp.fsu.maximal.1
  have htM : t ∈ fsuM T L := le_fsuM T L ht
  have hL0 := SecA.fsuL0_eq_sup h37 h38 hyp ht htn
  obtain ⟨-, -, h1, -⟩ := h1011 G T L I hyp
  obtain ⟨-, hV1, hV2, -⟩ := h1 t ht htn
  have hMN := SecA.fsuM_le_normalizer_fsuVM T L I
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_fsuM T L)).trans hMN
  have hLtN : CFSG.conjugate L t ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_fsuM T L)).trans hMN
  have hT1V : T1 T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    inf_le_left.trans (SecA.le_normalizer_fsuVM T L I)
  have hN1 : fsuL0 T L ⊔ T1 T L ≤
      Subgroup.normalizer ((⁅fsuVM T L I, L⁆ : Subgroup G) : Set G) := by
    rw [hL0]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact SecA.le_normalizer_commutator hLN Subgroup.le_normalizer
    · exact (Subgroup.le_centralizer_iff.mp hV1).trans (Subgroup.centralizer_le_normalizer _)
    · exact SecA.le_normalizer_commutator hT1V inf_le_right
  have hN2 : fsuL0 T L ⊔ T1 T L ≤
      Subgroup.normalizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
    rw [hL0]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (Subgroup.le_centralizer_iff.mp hV2).trans (Subgroup.centralizer_le_normalizer _)
    · exact SecA.le_normalizer_commutator hLtN Subgroup.le_normalizer
    · exact SecA.le_normalizer_commutator hT1V (T1_le_normalizer_conjugate h37 h38 hyp ht)
  have hV1ne : ⁅fsuVM T L I, L⁆ ≠ ⊥ := SecA.commutator_fsuVM_ne_bot hyp.fsu
  have hV2ne : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≠ ⊥ := by
    rw [← SecA.conjugate_commutator_fsuVM htM]
    intro h
    apply hV1ne
    rw [SecA.conjugate_eq_map] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj t⁻¹).injective).mp h
  have hp : ∀ K : Subgroup G, K ≤ fsuM T L → IsPGroup 2 ↥⁅fsuVM T L I, K⁆ := fun K hK =>
    (SecA.isPGroup_fsuVM hyp).to_le
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hK.trans hMN))
  have hLM : L ≤ fsuM T L := (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_fsuM T L)
  have hLtM : CFSG.conjugate L t ≤ fsuM T L :=
    (SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_fsuM T L)
  refine ⟨fun K hK => ?_, ?_⟩
  · rcases hK with rfl | ⟨t', ht', ht'n, rfl⟩
    · exact le_fsuM_of_unique hU hN1 (pCoreOf_normalizer_ne_bot' (hp _ hLM) hV1ne)
    · rw [SecA.conjugate_eq_of_not_mem h37 h38 hyp ht htn ht' ht'n]
      exact le_fsuM_of_unique hU hN2 (pCoreOf_normalizer_ne_bot' (hp _ hLtM) hV2ne)
  · refine le_fsuM_of_unique hU (sup_le (SecA.fsuL0_le_normalizer hloc) inf_le_right) ?_
    intro h
    apply SecA.pCoreOf_ne_bot_of_faithful hyp.fsu.faithful
    refine le_bot_iff.mp (h ▸ ?_)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans Subgroup.le_normalizer)
      (SecA.normalizer_le_normalizer_pCoreOf L) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

end CFSG.Quasithin.Vol2.Ch10.SecB
