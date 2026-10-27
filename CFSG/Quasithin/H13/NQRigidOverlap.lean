module

public import CFSG.Quasithin.H13.NQRigidOverlapResidual
public import CFSG.Quasithin.H13.NQRigidOverlapWitness
public import CFSG.Quasithin.H13.NQRigidOverlapSylow
public import CFSG.Quasithin.H13.NQRigidThompson

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)

section Sylow

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem inf_le_normalizer_sylow (h : QTNQ T L M) {H : Subgroup G} (hTH : T ≤ H)
    (hHN : H ⊓ (CFSG.solvableRadical L).map L.subtype ≤
      normalizer ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G)) :
    H ⊓ M ≤ normalizer ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (CFSG.solvableRadical L).map L.subtype with hN
  set S := T ⊓ N with hS
  have hNL : N ≤ L := map_subtype_le _
  have hMN : M ≤ normalizer (N : Set G) := by
    rw [h.eq_normalizer]
    exact LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hTM : IsSylowOf 2 T M := CFSG.ABGLocalTools.isSylowOf_iff.mpr
    ⟨h.t_le, h.sylow.1, fun h2 => h.sylow.2 (h2.trans (relIndex_dvd_index_of_le h.t_le))⟩
  have hSN : IsSylowOf 2 S N := hTM.inf_of_le_normalizer (hNL.trans h.l_le) hMN
  have hS2 : IsPGroup 2 S := h.sylow.1.to_le inf_le_left
  have hSHN : S ≤ H ⊓ N := le_inf (inf_le_left.trans hTH) inf_le_right
  intro i hi
  obtain ⟨hiH, hiM⟩ := mem_inf.mp hi
  set P := S.map (MulAut.conj i).toMonoidHom with hP
  have hPHN : P ≤ H ⊓ N := by
    rintro _ ⟨s, hs, rfl⟩
    have hs' := hSHN hs
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mem_inf.mpr ⟨mul_mem (mul_mem hiH (mem_inf.mp hs').1) (inv_mem hiH),
      (mem_normalizer_iff.mp (hMN hiM) s).mp (mem_inf.mp hs').2⟩
  have hP2 : IsPGroup 2 P := hS2.map _
  have hSP : IsPGroup 2 ↥(S ⊔ P) := IsPGroup.to_sup_of_normal_left' hS2 hP2 (hPHN.trans hHN)
  have hSPN : S ⊔ P ≤ N := sup_le inf_le_right (hPHN.trans inf_le_right)
  have heq := hSN.eq_of_le le_sup_left hSPN hSP
  have hPS : P ≤ S := heq ▸ le_sup_right
  have hcard : Nat.card P = Nat.card S :=
    card_map_of_injective (f := (MulAut.conj i).toMonoidHom) (MulAut.conj i).injective
  have hPeq : P = S := eq_of_le_of_card_ge hPS hcard.ge
  exact mem_normalizer_iff_map_conj_eq.mpr hPeq

end Sylow

theorem stmtOverlapNormalizesOriginalK_of_singleton
    (hWS : FactWitnessSingleton) : StmtOverlapNormalizesOriginalK := by
  intro G _ _ T L M h H hTH hH2 hHM
  refine ⟨le_normalizer_originalK h (inf_le_right.trans h.eq_normalizer.le)
    (inf_le_normalizer_sylow h hTH (radical_inf_le_normalizer_sylow h hTH
      fun q hq hq5 X₀ hX => not_le_of_witness hWS h hTH hH2 hHM hq hq5 hX)),
    oTwoUpper_originalK_sup h⟩

end CFSG.Quasithin.H13.NQRigid
