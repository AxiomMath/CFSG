module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qModel
import CFSG.Quasithin.Recognition.GoldschmidtF112RG24
import CFSG.Quasithin.Background.F1AmalgamRestrict
public import CFSG.Quasithin.Recognition.St84.Gen.U4qVFact

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.U4Par

section Transport

theorem pCoreOf_le_perfectCore_of_mulEquiv {X Y : Type} [Group X] [Group Y]
    [Finite X] [Finite Y] {A : Subgroup X} {N : Subgroup Y} (e : ↥A ≃* ↥N)
    (hN : pCoreOf 2 N ≤ perfectCore N) : pCoreOf 2 A ≤ perfectCore A := by
  intro a ha
  have haA : a ∈ A := CFSG.LieType.BorelTits.pCoreOf_le 2 A ha
  have hmem : ((e ⟨a, haA⟩ : ↥N) : Y) ∈ perfectCore N :=
    hN ((mem_pCoreOf_iff_of_mulEquiv e 2 ⟨a, haA⟩).mp ha)
  exact (CFSG.Quasithin.F1.mem_perfectCore_iff_of_equiv e ⟨a, haA⟩).mpr hmem

private noncomputable def vertexMulEquiv {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    {P : Subgroup X} {M : Subgroup Y} {Q : Subgroup Z} (e : ↥P ≃* ↥M) (ψ : Y ≃* Z)
    (h : M.map ψ.toMonoidHom = Q) : ↥P ≃* ↥Q :=
  e.trans ((M.equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
    (MulEquiv.subgroupCongr h))

end Transport

theorem u4q_ident_psu {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}
    (hf : 2 ≤ f) (hA : IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 f)) :
    Group.IsSolvable ↥(bigB L1 L2 S) ∧
      pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ perfectCore (L1 ⊔ bigB L1 L2 S) ∧
      pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ perfectCore (L2 ⊔ bigB L1 L2 S) ∧
      ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K),
        (Nonempty (↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ≃* ↥(radQ h)) ∧
          Nonempty (↥(perfectCore (L2 ⊔ bigB L1 L2 S)) ≃* ↥(perfectCore (parP2 h)))) ∨
        Nonempty (↥(perfectCore (L2 ⊔ bigB L1 L2 S)) ≃* ↥(perfectCore (parP h))) := by
  classical
  obtain ⟨Y, _, hY, T, M1, M2, hpair, ⟨iso⟩⟩ := hA
  have hY' : CFSG.Blueprint.LieModel Y .PSU 4 2 f := hY
  obtain ⟨K, _, h, ⟨e⟩⟩ := exists_hypSU_equiv_of_lieModel hY'
  haveI hSU : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  obtain ⟨hsolv, -, -⟩ := isSolvable_inf_and_vFact_of_isYAmalgamPair hY' hf hpair
  haveI : Group.IsSolvable (RankTwoAmalgam.ofSubgroups M1 M2).G12 := hsolv
  haveI : Group.IsSolvable
      ↥((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)) :=
    Group.isSolvable_of_isSolvable_injective (f := iso.φ12.toMonoidHom) iso.φ12.injective
  have hB : Group.IsSolvable ↥(bigB L1 L2 S) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (le_inf le_sup_right le_sup_right :
        bigB L1 L2 S ≤ (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)))
      (Subgroup.inclusion_injective _)
  have hpair0 : IsYAmalgamPair (T.map e.symm.toMonoidHom)
      (M1.map e.symm.toMonoidHom) (M2.map e.symm.toMonoidHom) :=
    IsYAmalgamPair.map e.symm hpair
  obtain ⟨c, -, hc⟩ := IsSylowTwoOf.exists_conj hpair0.1 (isSylowTwoOf_hypUnitriangular h)
  have hpair1 : IsYAmalgamPair (hypUnitriangular h 2 0)
      ((M1.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom)
      ((M2.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom) := by
    have h' := IsYAmalgamPair.map (MulAut.conj c) hpair0
    rwa [← hc] at h'
  have hV := eq_parP_or_parP2_of_isYAmalgamPair h hpair1 rfl
  have hbase1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(M1.map e.symm.toMonoidHom) :=
    iso.φ1.trans (M1.equivMapOfInjective e.symm.toMonoidHom e.symm.injective)
  have hbase2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(M2.map e.symm.toMonoidHom) :=
    iso.φ2.trans (M2.equivMapOfInjective e.symm.toMonoidHom e.symm.injective)
  rcases hV with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    let ε1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(parP h) := vertexMulEquiv hbase1 (MulAut.conj c) h1
    let ε2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(parP2 h) := vertexMulEquiv hbase2 (MulAut.conj c) h2
    have ho1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ perfectCore (L1 ⊔ bigB L1 L2 S) :=
      pCoreOf_le_perfectCore_of_mulEquiv ε1 (by
        rw [U4qModel.pCoreOf_parP_eq h hf]
        exact radQ_le_perfectCore h hf)
    have ho2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ perfectCore (L2 ⊔ bigB L1 L2 S) :=
      pCoreOf_le_perfectCore_of_mulEquiv ε2 (by
        rw [U4qModel.pCoreOf_parP2_eq h hf]
        exact radQ2_le_perfectCore_parP2 h hf)
    exact ⟨hB, ho1, ho2, K, inferInstance, h, Or.inl
      ⟨⟨(pCoreOfMulEquiv ε1 2).trans
          (MulEquiv.subgroupCongr (U4qModel.pCoreOf_parP_eq h hf))⟩,
        nonempty_perfectCore_mulEquiv ε2⟩⟩
  ·
    let ε1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(parP2 h) := vertexMulEquiv hbase1 (MulAut.conj c) h1
    let ε2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(parP h) := vertexMulEquiv hbase2 (MulAut.conj c) h2
    have ho1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ perfectCore (L1 ⊔ bigB L1 L2 S) :=
      pCoreOf_le_perfectCore_of_mulEquiv ε1 (by
        rw [U4qModel.pCoreOf_parP2_eq h hf]
        exact radQ2_le_perfectCore_parP2 h hf)
    have ho2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ perfectCore (L2 ⊔ bigB L1 L2 S) :=
      pCoreOf_le_perfectCore_of_mulEquiv ε2 (by
        rw [U4qModel.pCoreOf_parP_eq h hf]
        exact radQ_le_perfectCore h hf)
    exact ⟨hB, ho1, ho2, K, inferInstance, h,
      Or.inr (nonempty_perfectCore_mulEquiv ε2)⟩

end CFSG.Quasithin.F112R
