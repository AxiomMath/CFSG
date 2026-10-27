module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNYam

public section

namespace CFSG.Quasithin.Stroth

open CFSG.GH74.BNPair CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.BN

private theorem twoPrimeResidualOf_map_le {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (H : Subgroup A) :
    (SimsG4.twoPrimeResidualOf H).map e.toMonoidHom ≤
      SimsG4.twoPrimeResidualOf (H.map e.toMonoidHom) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
  let eH : ↥H ≃* ↥(H.map e.toMonoidHom) := MulEquiv.subgroupMap e H
  have hw' : eH w ∈ SimsG4.twoPrimeResidual ↥(H.map e.toMonoidHom) := by
    rw [SimsG4.twoPrimeResidual, Subgroup.mem_sInf]
    intro K hK
    have hK' : (K.comap eH.toMonoidHom).Normal ∧
        Odd (K.comap eH.toMonoidHom).index := by
      refine ⟨hK.1.comap eH.toMonoidHom, ?_⟩
      rw [Subgroup.index_comap_of_surjective (f := eH.toMonoidHom) (H := K) eH.surjective]
      exact hK.2
    exact (Subgroup.mem_sInf.mp hw) (K.comap eH.toMonoidHom) hK'
  exact Subgroup.mem_map.mpr ⟨eH w, hw', rfl⟩

theorem twoPrimeResidualOf_map_equiv {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (H : Subgroup A) :
    SimsG4.twoPrimeResidualOf (H.map e.toMonoidHom) =
      (SimsG4.twoPrimeResidualOf H).map e.toMonoidHom := by
  refine le_antisymm ?_ (twoPrimeResidualOf_map_le e H)
  have h1 : (SimsG4.twoPrimeResidualOf (H.map e.toMonoidHom)).map e.symm.toMonoidHom ≤
      SimsG4.twoPrimeResidualOf ((H.map e.toMonoidHom).map e.symm.toMonoidHom) :=
    twoPrimeResidualOf_map_le e.symm (H.map e.toMonoidHom)
  have h2 : (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
    rw [Subgroup.map_map,
      show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ by
        ext x
        simp,
      Subgroup.map_id]
  rw [h2] at h1
  have h3 := Subgroup.map_mono (f := e.toMonoidHom) h1
  rw [Subgroup.map_map,
    show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ by
      ext x
      simp,
    Subgroup.map_id] at h3
  exact h3

private theorem isSylowTwoOf_top_map_equiv' {G G₀ : Type} [Group G] [Group G₀]
    (e : G ≃* G₀) {U : Subgroup G} (hU : IsSylowTwoOf U ⊤) :
    IsSylowTwoOf (U.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hU.2.1.map e.toMonoidHom, ?_⟩
  rw [show ((U.map e.toMonoidHom).subgroupOf ⊤).index =
      (U.map e.toMonoidHom).index from Subgroup.relIndex_top_right _,
    Subgroup.index_map_of_bijective e.bijective U]
  have := hU.2.2
  rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right _] at this

theorem exists_mulEquiv_map_eq_of_isSylowTwoOf_top
    {G G₀ : Type} [Group G] [Group G₀] [Finite G]
    (e : G ≃* G₀) {U : Subgroup G} {U₀ : Subgroup G₀}
    (hU : IsSylowTwoOf U ⊤) (hU₀ : IsSylowTwoOf U₀ ⊤) :
    ∃ e' : G ≃* G₀, U.map e'.toMonoidHom = U₀ := by
  classical
  haveI : Finite G₀ := Finite.of_equiv G e.toEquiv
  have hUmap : IsSylowTwoOf (U.map e.toMonoidHom) ⊤ :=
    isSylowTwoOf_top_map_equiv' e hU
  have hidx : ∀ S : Subgroup G₀, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  obtain ⟨g, hg⟩ : ∃ g : G₀,
      (U.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = U₀ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let P : Sylow 2 G₀ := hUmap.2.1.toSylow (hidx _ hUmap)
    let Q : Sylow 2 G₀ := hU₀.2.1.toSylow (hidx _ hU₀)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G₀ P Q
    refine ⟨g, ?_⟩
    have h := congrArg (fun T : Sylow 2 G₀ => (T : Subgroup G₀)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    have hP : (P : Subgroup G₀) = U.map e.toMonoidHom := IsPGroup.toSylow_coe _ _
    have hQ : (Q : Subgroup G₀) = U₀ := IsPGroup.toSylow_coe _ _
    change (P : Subgroup G₀).map (MulAut.conj g).toMonoidHom = (Q : Subgroup G₀) at h
    simpa [hP, hQ] using h
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have h := hg
  change (U.map e.toMonoidHom).map
    (MulDistribMulAction.toMonoidHom G₀ (MulAut.conj g)) = U₀ at h
  have heq : (e.trans (MulAut.conj g)).toMonoidHom =
      (MulDistribMulAction.toMonoidHom G₀ (MulAut.conj g)).comp e.toMonoidHom := by
    ext x
    rfl
  rw [heq, ← Subgroup.map_map]
  exact h

theorem map_parabolic_eq_or {G G₀ : Type} [Group G] [Group G₀]
    {n : ℕ} (R : RankTwoSystem G n) (R₀ : RankTwoSystem G₀ n)
    (e : G ≃* G₀) (heB : R.B.map e.toMonoidHom = R₀.B) (i : Bool) :
    (P R i).map e.toMonoidHom = R₀.P₁ ∨ (P R i).map e.toMonoidHom = R₀.P₂ := by
  have hBA : R₀.B ≤ (P R i).map e.toMonoidHom := by
    rw [← heB]
    exact Subgroup.map_mono (B_le_P R i)
  have hA_ne_B : (P R i).map e.toMonoidHom ≠ R₀.B := by
    intro h
    have hPB : P R i = R.B :=
      Subgroup.map_injective (f := e.toMonoidHom)
        (show Function.Injective (e : G → G₀) from e.injective) (h.trans heB.symm)
    exact not_le_P R i (by
      rw [hPB]
      exact B_le_P R (!i))
  have hA_ne_top : (P R i).map e.toMonoidHom ≠ ⊤ := by
    intro h
    have htop : (⊤ : Subgroup G).map e.toMonoidHom = ⊤ := Subgroup.map_equiv_top e
    exact P_ne_top R i (Subgroup.map_injective e.injective (h.trans htop.symm))
  rcases eq_B_or_P_or_top R₀ hBA with h | ⟨j, hj⟩ | h
  · exact absurd h hA_ne_B
  · cases j
    · exact Or.inr (by simpa [P_false] using hj)
    · exact Or.inl (by simpa [P_true] using hj)
  · exact absurd h hA_ne_top

private theorem borelResidualSplit_of_map_parabolics {G G₀ : Type} [Group G] [Group G₀]
    {n : ℕ} (R : RankTwoSystem G n) (R₀ : RankTwoSystem G₀ n)
    (e : G ≃* G₀) (heB : R.B.map e.toMonoidHom = R₀.B)
    (hsplit : BorelResidualSplit R₀)
    (h : (R.P₁.map e.toMonoidHom = R₀.P₁ ∧ R.P₂.map e.toMonoidHom = R₀.P₂) ∨
      (R.P₁.map e.toMonoidHom = R₀.P₂ ∧ R.P₂.map e.toMonoidHom = R₀.P₁)) :
    BorelResidualSplit R := by
  rcases h with ⟨he1, he2⟩ | ⟨he1, he2⟩
  · refine (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom)
      (show Function.Injective (e : G → G₀) from e.injective)).mp ?_
    rw [heB, Subgroup.map_sup,
      Subgroup.map_inf _ _ _ e.injective, Subgroup.map_inf _ _ _ e.injective,
      ← twoPrimeResidualOf_map_equiv e R.P₁, ← twoPrimeResidualOf_map_equiv e R.P₂, he1, he2]
    exact hsplit
  · refine (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom)
      (show Function.Injective (e : G → G₀) from e.injective)).mp ?_
    rw [heB, Subgroup.map_sup,
      Subgroup.map_inf _ _ _ e.injective, Subgroup.map_inf _ _ _ e.injective,
      ← twoPrimeResidualOf_map_equiv e R.P₁, ← twoPrimeResidualOf_map_equiv e R.P₂, he1, he2]
    exact hsplit.trans (le_of_eq (sup_comm _ _))

theorem borelResidualSplitTransport : BorelResidualSplitTransport := by
  intro G G₀ _ _ hG n R R₀ he0 hRU hRU₀ hsplit
  obtain ⟨e0⟩ := he0
  obtain ⟨e, heU⟩ := exists_mulEquiv_map_eq_of_isSylowTwoOf_top e0 hRU hRU₀
  have heB : R.B.map e.toMonoidHom = R₀.B := by
    rw [← normalizer_U_eq_B R, Subgroup.map_equiv_normalizer_eq, heU,
      normalizer_U_eq_B R₀]
  have hP1_mem : R.P₁.map e.toMonoidHom = R₀.P₁ ∨
      R.P₁.map e.toMonoidHom = R₀.P₂ := by
    simpa [P_true] using map_parabolic_eq_or R R₀ e heB true
  have hP2_mem : R.P₂.map e.toMonoidHom = R₀.P₁ ∨
      R.P₂.map e.toMonoidHom = R₀.P₂ := by
    simpa [P_false] using map_parabolic_eq_or R R₀ e heB false
  have hswap : (R.P₁.map e.toMonoidHom = R₀.P₁ ∧
        R.P₂.map e.toMonoidHom = R₀.P₂) ∨
      (R.P₁.map e.toMonoidHom = R₀.P₂ ∧
        R.P₂.map e.toMonoidHom = R₀.P₁) := by
    rcases hP1_mem with h1 | h1 <;> rcases hP2_mem with h2 | h2
    · exact absurd (Subgroup.map_injective e.injective (h1.trans h2.symm)) (P₁_ne_P₂ R)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (Subgroup.map_injective e.injective (h1.trans h2.symm)) (P₁_ne_P₂ R)
  exact borelResidualSplit_of_map_parabolics R R₀ e heB hsplit hswap

end CFSG.Quasithin.Stroth
