module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_c

namespace CFSG
end CFSG
open CFSG
/-! # Theorem 4.18(e) from BG Section 4 -/

universe u

section Main

open scoped FixedPoints

public theorem CFSG.theorem_4_18_e {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hsolv : IsSolvable G) (hodd : Odd (Nat.card G)) (hp_mem : p ∣ Nat.card G)
    (hrank : primeRank p G ≤ 2) :
    Nat.Coprime p (Nat.card (G ⧸ Op_p'p p G)) ∧ IsMulCommutative (G ⧸ Op_p'p p G) := by
  let D : Subgroup G := derivedSubgroup G
  let M : Subgroup G := pPrimeCore p G
  let q : G →* (G ⧸ M) := QuotientGroup.mk' M
  let Dbar : Subgroup (G ⧸ M) := D.map q
  have hDquot_p : IsPGroup p (↥D ⧸ pPrimeCore p (↥D)) := by
    exact isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
      (p := p) (H := ↥D) (theorem_4_18_c (G := G) (p := p) hsolv hodd hp_mem hrank)
  have hcoreD_le_coreG : (pPrimeCore p (↥D)).map D.subtype ≤ M :=
    pPrimeCore_map_subtype_le_pPrimeCore_of_normal (p := p) D
  let ψ0 : D →* Dbar :=
    (q.comp D.subtype).codRestrict Dbar (by
      intro x
      exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩)
  have hcoreD_le_ker : pPrimeCore p (↥D) ≤ ψ0.ker := by
    intro x hx
    apply Subtype.ext
    change q (x : G) = 1
    apply (QuotientGroup.eq_one_iff (N := M) (x := (x : G))).2
    exact hcoreD_le_coreG (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  let ψ : D ⧸ pPrimeCore p (↥D) →* Dbar := QuotientGroup.lift (pPrimeCore p (↥D)) ψ0 hcoreD_le_ker
  have hψ0_surj : Function.Surjective ψ0 := by
    intro y
    rcases y.property with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    simpa [ψ0] using hxy
  have hψ_surj : Function.Surjective ψ :=
    QuotientGroup.lift_surjective_of_surjective
      (N := pPrimeCore p (↥D)) (φ := ψ0) hψ0_surj hcoreD_le_ker
  have hDbar_p : IsPGroup p Dbar := IsPGroup.of_surjective (hG := hDquot_p) ψ hψ_surj
  have hDbar_le_pCore : Dbar ≤ pCore p (G ⧸ M) := le_sSup ⟨by infer_instance, hDbar_p⟩
  have hder_le_op : D ≤ Op_p'p p G := by
    intro x hx
    change q x ∈ pCore p (G ⧸ M)
    exact hDbar_le_pCore (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hcomm_le : _root_.commutator G ≤ Op_p'p p G := by
    change derivedSeries G 1 ≤ Op_p'p p G at hder_le_op
    rw [derivedSeries_one] at hder_le_op
    exact hder_le_op
  have hQcomm : IsMulCommutative (G ⧸ Op_p'p p G) := by
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Op_p'p p G)).2 hcomm_le
  have hM_le_Op : M ≤ Op_p'p p G := by
    intro x hx
    change q x ∈ pCore p (G ⧸ M)
    have hx1 : q x = 1 := (QuotientGroup.eq_one_iff (N := M) (x := x)).2 hx
    simp [hx1]
  have hmap_op : (Op_p'p p G).map q = pCore p (G ⧸ M) := by
    dsimp [Op_p'p, q, M]
    simpa using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p G))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p G))
        (H := pCore p (G ⧸ pPrimeCore p G)))
  let e1 : (G ⧸ M) ⧸ (Op_p'p p G).map q ≃* G ⧸ Op_p'p p G :=
    QuotientGroup.quotientQuotientEquivQuotient (N := M) (M := Op_p'p p G) hM_le_Op
  let e2 : (G ⧸ M) ⧸ pCore p (G ⧸ M) ≃* (G ⧸ M) ⧸ (Op_p'p p G).map q :=
    QuotientGroup.quotientMulEquivOfEq hmap_op.symm
  let e : (G ⧸ M) ⧸ pCore p (G ⧸ M) ≃* G ⧸ Op_p'p p G := e2.trans e1
  let qbar : G ⧸ M →* (G ⧸ M) ⧸ pCore p (G ⧸ M) := QuotientGroup.mk' (pCore p (G ⧸ M))
  have hQbar_core_bot : pCore p ((G ⧸ M) ⧸ pCore p (G ⧸ M)) = ⊥ := by
    have hmap :
        (pCore p (G ⧸ M)).map qbar = pCore p ((G ⧸ M) ⧸ pCore p (G ⧸ M)) := by
      simpa [qbar] using
        pCore_map_mk'_eq_of_normal_isPGroup (G := G ⧸ M) (p := p)
          (pCore p (G ⧸ M)) (pCore_isPGroup (G := G ⧸ M) (p := p))
    calc
      pCore p ((G ⧸ M) ⧸ pCore p (G ⧸ M)) = (pCore p (G ⧸ M)).map qbar := hmap.symm
      _ = ⊥ := by
        simp [qbar]
  have hpCore_map :
      (pCore p ((G ⧸ M) ⧸ pCore p (G ⧸ M))).map e.toMonoidHom =
        pCore p (G ⧸ Op_p'p p G) := by
    simpa using
      (pCore_map_iso
        (G := (G ⧸ M) ⧸ pCore p (G ⧸ M))
        (G' := G ⧸ Op_p'p p G) (p := p) (f := e))
  have hQcore_bot : pCore p (G ⧸ Op_p'p p G) = ⊥ := by
    have hmap_bot :
        (pCore p ((G ⧸ M) ⧸ pCore p (G ⧸ M))).map e.toMonoidHom = ⊥ := by
      simp [hQbar_core_bot]
    rw [hpCore_map] at hmap_bot
    exact hmap_bot
  have hQnot_dvd : ¬ p ∣ Nat.card (G ⧸ Op_p'p p G) := by
    intro hp_dvd_Q
    letI : IsMulCommutative (G ⧸ Op_p'p p G) := hQcomm
    letI : CommGroup (G ⧸ Op_p'p p G) := IsMulCommutative.instCommGroup
    let S : Sylow p (G ⧸ Op_p'p p G) :=
      Classical.choice (inferInstance : Nonempty (Sylow p (G ⧸ Op_p'p p G)))
    have hS_le_core : (S : Subgroup (G ⧸ Op_p'p p G)) ≤ pCore p (G ⧸ Op_p'p p G) := by
      exact le_sSup
        ⟨Subgroup.normal_of_isMulCommutative (H := (S : Subgroup (G ⧸ Op_p'p p G))),
          S.isPGroup'⟩
    have hS_eq_bot : (S : Subgroup (G ⧸ Op_p'p p G)) = ⊥ := by
      refine le_antisymm ?_ bot_le
      exact hS_le_core.trans (by simp [hQcore_bot])
    have hp_dvd_index : p ∣ (S : Subgroup (G ⧸ Op_p'p p G)).index := by
      simpa [hS_eq_bot, Subgroup.index_bot] using hp_dvd_Q
    exact S.not_dvd_index hp_dvd_index
  refine ⟨?_, hQcomm⟩
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hQnot_dvd

end Main
