module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorusEdge

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

open CosetGeom (graph stab ballStab nbrs vtype γ₀ γ₁ Vv)

namespace Setting

variable {L₁ L₂ S Z : Subgroup G}

theorem isPGroup_Vv (hs : Setting L₁ L₂ S Z)
    {y : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)} (hy : vtype y = true) :
    IsPGroup 2 (Vv Z y) :=
  (pCoreOf_isPGroup 2 (stab y)).to_le (lemma63_2' hs.toCritAmalgam hy).2.1

theorem eq_of_nbrs_eq (hs : Setting L₁ L₂ S Z) {q i : ℕ} (hK : IsBenderQuot (oTwoQuot ↥L₂) q i)
    {y y' : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)} (hy : vtype y = true)
    (hy' : vtype y' = true) (h : nbrs y = nbrs y') : y = y' := by
  by_contra hne
  have hN : P₂ L₁ L₂ S ≤ Subgroup.normalizer (Z : Set G) :=
    hs.centralizes.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
  have hV : Vv Z y = Vv Z y' := by
    cases y with
    | inl x => simp [CosetGeom.vtype] at hy
    | inr a =>
      cases y' with
      | inl x => simp [CosetGeom.vtype] at hy'
      | inr b =>
        rw [CosetGeom.Vv_inr, CosetGeom.Vv_inr]
        refine le_antisymm (iSup₂_le fun x hx => le_iSup₂_of_le x ?_ le_rfl)
          (iSup₂_le fun x hx => le_iSup₂_of_le x ?_ le_rfl)
        · exact (Set.ext_iff.mp h (Sum.inl x)).mp hx
        · exact (Set.ext_iff.mp h.symm (Sum.inl x)).mp hx
  obtain ⟨e, he⟩ := CosetGeom.exists_adj y
  have he_false : vtype e = false := by
    have hne' := CosetGeom.vtype_ne_of_adj (show (graph (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S)
      (P₁ L₁ L₂ S)).Adj y e from he)
    rw [hy] at hne'
    cases hv : vtype e with
    | false => rfl
    | true => exact absurd hv.symm hne'
  have hye : y ∈ nbrs e := CosetGeom.mem_nbrs_symm he
  have hy'e : y' ∈ nbrs e := CosetGeom.mem_nbrs_symm (h ▸ he)
  obtain ⟨L, hL⟩ := hs.exists_benderLocal hK he_false
  have hVa : ∀ a ∈ nbrs e, Vv Z a = Vv Z y := by
    intro a ha
    by_cases hay : a = y
    · rw [hay]
    · obtain ⟨g, hgst, hgsmul⟩ := hL.exists_smul_eq_of_ne (δ := y) (ε := y') (ε' := a)
        hye hy'e ha (Ne.symm hne) hay
      calc
        Vv Z a = Vv Z (g • y') := by rw [hgsmul]
        _ = conjSub (g : G) (Vv Z y') := CosetGeom.Vv_smul hN g y'
        _ = conjSub (g : G) (Vv Z y) := by rw [hV]
        _ = Vv Z (g • y) := (CosetGeom.Vv_smul hN g y).symm
        _ = Vv Z y := by rw [CosetGeom.smul_eq_of_mem_stab hgst.2]
  have hstab_e : stab e ≤ Subgroup.normalizer (Vv Z y : Set G) := by
    intro g hg
    obtain ⟨hgG, hge⟩ := CosetGeom.mem_stab.mp hg
    let g' : ↥(L₁ ⊔ L₂ ⊔ S) := ⟨g, hgG⟩
    have hge' : g' • e = e := hge
    have h1 : (graph (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)).Adj (g' • y) (g' • e) :=
      (CosetGeom.smul_adj g').mpr he
    rw [hge'] at h1
    have hgy : g' • y ∈ nbrs e := h1.symm
    have h := hVa (g' • y) hgy
    rw [CosetGeom.Vv_smul hN g' y] at h
    exact CosetGeom.mem_normalizer_of_conjSub_eq h
  have hstab_y : stab y ≤ Subgroup.normalizer (Vv Z y : Set G) :=
    CosetGeom.stab_le_normalizer_Vv hN y
  have hNorm : L₁ ⊔ L₂ ⊔ S ≤ Subgroup.normalizer (Vv Z y : Set G) :=
    (stab_sup_stab_eq hs.toCritAmalgam he_false hye).symm.le.trans
      (sup_le hstab_e hstab_y)
  have hVyG : Vv Z y ≤ L₁ ⊔ L₂ ⊔ S :=
    ((lemma63_2' hs.toCritAmalgam hy).2.1.trans (pCoreOf_le 2 (stab y))).trans
      (CosetGeom.stab_le y)
  have hcore : Vv Z y ≤ pCoreOf 2 (L₁ ⊔ L₂ ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVyG hNorm (isPGroup_Vv hs hy)
  have hbot : Vv Z y = ⊥ := by
    rw [hs.toCritAmalgam.amalgam.o2_trivial] at hcore
    exact le_bot_iff.mp hcore
  have hVve_ne : Vv Z e ≠ ⊥ := by
    intro hbe
    obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ he_false
    rw [hg, Zv_smul_γ₀ hs.toCritAmalgam g] at hbe
    exact hs.ne_bot ((conjSub_eq_bot_iff (g : G)).mp hbe)
  have hle : Vv Z e ≤ Vv Z y := Vv_le_Vv_of_mem_nbrs hy he
  rw [hbot] at hle
  exact hVve_ne (le_bot_iff.mp hle)

end Setting

end CFSG.Quasithin.F112Crit

end
