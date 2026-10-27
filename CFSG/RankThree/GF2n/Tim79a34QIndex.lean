module

public import CFSG.RankThree.GF2n.Tim79a34TwoEnd
public import CFSG.RankThree.GF2n.Tim79a34TwBound

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G]

noncomputable def mulAutToPermNe (V : Type) [Group V] :
    MulAut V →* Equiv.Perm {v : V // v ≠ 1} where
  toFun α :=
    { toFun := fun v => ⟨α v, fun h => v.2 (α.injective (by rw [h, map_one]))⟩
      invFun := fun v => ⟨α.symm v, fun h => v.2 (α.symm.injective (by rw [h, map_one]))⟩
      left_inv := fun v => Subtype.ext (α.symm_apply_apply v)
      right_inv := fun v => Subtype.ext (α.apply_symm_apply v) }
  map_one' := by
    ext v
    rfl
  map_mul' α β := by
    ext v
    rfl

theorem mulAutToPermNe_injective (V : Type) [Group V] :
    Function.Injective (mulAutToPermNe V) := by
  intro α β h
  ext v
  by_cases hv : v = 1
  · rw [hv, map_one, map_one]
  · have := congrArg (fun σ => ((σ ⟨v, hv⟩ : {v : V // v ≠ 1}) : V)) h
    simpa [mulAutToPermNe] using this

variable [Finite G] {M V Q P H : Subgroup G}

theorem relIndex_P_Q_le_two (hc : MinCex M V Q P H) (hV : Nat.card ↥V = 4) :
    P.relIndex Q ≤ 2 := by
  classical
  haveI : Fintype ↥V := Fintype.ofFinite _
  haveI : Fintype {v : ↥V // v ≠ 1} := Fintype.ofFinite _
  have hQM : Q ≤ M := hc.hQ ▸ (inSubgroup_pCore_two M).2.1
  have hQN : Q ≤ Subgroup.normalizer (V : Set G) := by
    have := hc.normalizer_eq
    rw [this]
    exact hQM
  set φ : ↥Q →* Equiv.Perm {v : ↥V // v ≠ 1} :=
    (mulAutToPermNe ↥V).comp ((Subgroup.normalizerMonoidHom V).comp
      (Subgroup.inclusion hQN)) with hφ
  have hker : φ.ker = P.subgroupOf Q := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hc.hP, hφ]
    simp only [MonoidHom.comp_apply]
    rw [← map_one (mulAutToPermNe ↥V), (mulAutToPermNe_injective ↥V).eq_iff, ← MonoidHom.mem_ker,
      Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    simp [Subgroup.mem_inf, x.2]
  have hQ2 : IsPGroup 2 ↥Q := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).1
  have hR2 : IsPGroup 2 ↥φ.range := hQ2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hidx : P.relIndex Q = Nat.card ↥φ.range := by
    unfold Subgroup.relIndex
    rw [← hker, Subgroup.index_ker]
  have hdvd : Nat.card ↥φ.range ∣ 6 := by
    have h1 := Subgroup.card_subgroup_dvd_card φ.range
    have h2 : Nat.card (Equiv.Perm {v : ↥V // v ≠ 1}) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      have h3 : Fintype.card ↥V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hV
      have h4 : Fintype.card {v : ↥V // v ≠ 1} = 3 := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
        omega
      rw [h4]
      rfl
    rwa [h2] at h1
  rw [hidx, hk] at *
  by_contra hcon
  have hk2 : 2 ≤ k := by
    by_contra hk1
    interval_cases k <;> simp_all
  have h5 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
  have h4 : 4 ∣ 6 := dvd_trans h5 hdvd
  omega

theorem sec34QIndexStatement_holds : Sec34QIndexStatement := by
  intro G _ _ M V Q P H hH _
  have hc := hH.setup.mc.toMinCex
  have h := twb_card_barOf_mul (V := V) (H := H) (K := V) hc.V_le_H
  have e1 : Nat.card ↥(barOf V H V) = 2 := hH.q_two
  have e2 : Nat.card ↥(V ⊓ wOf V H) = 2 := by rw [hH.module]; exact hH.q_two
  rw [e1, e2] at h
  exact relIndex_P_Q_le_two hc (by omega)

end CFSG.RankThree.GF2n.Tim79a
