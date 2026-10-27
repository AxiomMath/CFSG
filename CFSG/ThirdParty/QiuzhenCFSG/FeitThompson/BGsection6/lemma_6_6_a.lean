module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.lemma_6_5_b

namespace CFSG
end CFSG
open CFSG

open scoped MatrixGroups Pointwise TensorProduct

/-! # Lemma 6.6(a) from BG Section 6 -/

public theorem CFSG.lemma_6_6_a
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {p : ℕ} [Fact p.Prime] (hpl : HasPLengthOne (p := p) G) {S : Sylow p G} :
    (S ≤ Op_p'p p G) ∧ (pPrimeCore p G ⊔ S = Op_p'p p G) ∧
      (pPrimeCore p G ⊔ Subgroup.normalizer (S : Subgroup G) = ⊤) := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let L : Subgroup G := Op_p'p p G
  have hM_le_L : M ≤ L := by
    intro x hx
    change QuotientGroup.mk' M x ∈ pCore p (G ⧸ M)
    have hx1 : QuotientGroup.mk' M x = 1 :=
      (QuotientGroup.eq_one_iff (N := M) (x := x)).2 hx
    simp [hx1]
  have hS_le_pElems : (S : Subgroup G) ≤ pElementsSubgroup p G := by
    intro x hxS
    refine Subgroup.subset_closure ?_
    rcases
        (IsPGroup.iff_orderOf (p := p) (G := ↥(S : Subgroup G))).1 S.isPGroup' ⟨x, hxS⟩ with
      ⟨n, hn⟩
    exact ⟨n, by simpa [Subgroup.orderOf_coe] using hn⟩
  have hS_le_L : (S : Subgroup G) ≤ L := by
    exact hS_le_pElems.trans (pElementsSubgroup_le_Op_p'p_of_hasPLengthOne (G := G) (p := p) hpl)
  have hM_sup_S_eq_L : M ⊔ S = L := by
    let Msub : Subgroup L := M.subgroupOf L
    let q : L →* L ⧸ Msub := QuotientGroup.mk' Msub
    let q0 : G →* G ⧸ M := QuotientGroup.mk' M
    let ψ0 : L →* pCore p (G ⧸ M) :=
      (q0.comp L.subtype).codRestrict (pCore p (G ⧸ M)) (by
        intro x
        exact x.property)
    have hMsub_eq_ker : Msub = ψ0.ker := by
      ext x
      change (x : G) ∈ M ↔ ψ0 x = 1
      constructor
      · intro hx
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff (N := M) (x := (x : G))).2 hx
      · intro hx
        have hx' : q0 (x : G) = 1 := congrArg Subtype.val hx
        exact (QuotientGroup.eq_one_iff (N := M) (x := (x : G))).1 hx'
    have hquot_p_aux : IsPGroup p (L ⧸ ψ0.ker) := by
      let ψ : L ⧸ ψ0.ker →* pCore p (G ⧸ M) := QuotientGroup.kerLift ψ0
      have hψinj : Function.Injective ψ := QuotientGroup.kerLift_injective ψ0
      exact IsPGroup.of_injective (hG := pCore_isPGroup (p := p) (G := G ⧸ M)) (ϕ := ψ) hψinj
    have hquot_p : IsPGroup p (L ⧸ Msub) := by
      let e : (L ⧸ Msub) ≃* (L ⧸ ψ0.ker) :=
        QuotientGroup.congr (G' := Msub) (H' := ψ0.ker) (MulEquiv.refl L) (by
          simp [hMsub_eq_ker])
      exact hquot_p_aux.of_equiv e.symm
    let Ssub : Sylow p L := S.subtype hS_le_L
    have hsup_sub : Msub ⊔ (Ssub : Subgroup L) = ⊤ := by
      have hmap_top : ((Ssub : Subgroup L).map q) = ⊤ := by
        let Qbar : Sylow p (L ⧸ Msub) :=
          Ssub.mapSurjective (f := q) (hf := QuotientGroup.mk'_surjective Msub)
        have hQbar_not_dvd :
            ¬ p ∣ ((Qbar : Subgroup (L ⧸ Msub)).index) := by
          exact Qbar.not_dvd_index
        have hQbar_index_pow :
            ∃ n : ℕ, ((Qbar : Subgroup (L ⧸ Msub)).index) = p ^ n := by
          exact hquot_p.index (Qbar : Subgroup (L ⧸ Msub))
        have hQbar_index_one : ((Qbar : Subgroup (L ⧸ Msub)).index) = 1 := by
          rcases hQbar_index_pow with ⟨n, hn⟩
          rcases n with _ | n
          · simp [hn]
          · exfalso
            apply hQbar_not_dvd
            rw [hn]
            exact dvd_pow_self p (Nat.succ_ne_zero _)
        have hQbar_top : (Qbar : Subgroup (L ⧸ Msub)) = ⊤ := by
          exact (Subgroup.index_eq_one).1 hQbar_index_one
        simpa [Qbar, q] using hQbar_top
      calc
        Msub ⊔ (Ssub : Subgroup L) = (((Ssub : Subgroup L).map q).comap q) := by
          simp [q]
        _ = ⊤ := by simp [hmap_top]
    have hsup_eq :
        (M ⊔ S).subgroupOf L = M.subgroupOf L ⊔ ((S.subtype hS_le_L : Sylow p L) : Subgroup L) := by
      simpa using
        (Subgroup.subgroupOf_sup (A := M) (A' := (S : Subgroup G)) (B := L) hM_le_L hS_le_L)
    apply le_antisymm
    · exact sup_le hM_le_L hS_le_L
    · intro x hxL
      have hxsub : (⟨x, hxL⟩ : L) ∈ (M ⊔ S).subgroupOf L := by
        rw [hsup_eq, hsup_sub]
        simp
      exact hxsub
  have hM_sup_norm_eq_top : M ⊔ Subgroup.normalizer (S : Subgroup G) = ⊤ := by
    have hFr : Subgroup.normalizer (S : Subgroup G) ⊔ L = ⊤ := by
      simpa using (Sylow.normalizer_sup_eq_top' (p := p) (N := L) S hS_le_L)
    apply top_le_iff.mp
    rw [← hFr]
    refine sup_le ?_ ?_
    · exact le_sup_right
    · rw [← hM_sup_S_eq_L]
      exact sup_le le_sup_left (le_sup_of_le_right Subgroup.le_normalizer)
  exact ⟨hS_le_L, hM_sup_S_eq_L, hM_sup_norm_eq_top⟩
