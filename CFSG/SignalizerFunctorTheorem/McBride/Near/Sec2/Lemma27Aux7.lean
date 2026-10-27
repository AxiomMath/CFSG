module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux4
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.PrimeTwo

public section

open CFSG.Open
open scoped Pointwise
open CFSG.SignalizerFunctorTheorem.Nonsolvable (simpleComponents IsASimple)
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem isDirectProduct_of_subset {S T : Set (Subgroup Γ)} {K : Subgroup Γ}
    (hK : IsDirectProduct S K) (hTS : T ⊆ S) : IsDirectProduct T (sSup T) where
  commute J hJ L hL hne x hx y hy := hK.commute J (hTS hJ) L (hTS hL) hne x hx y hy
  indep J hJ := by
    have h1 := hK.indep (hTS hJ)
    exact h1.mono_right (sSup_le_sSup (Set.sdiff_subset_sdiff_left hTS))
  sSup_eq := rfl

omit [Finite Γ] in
theorem simple_of_mem_lcal {K J : Subgroup Γ} (hJ : J ∈ lcal K) :
    IsSimpleGroup J ∧ ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x := by
  obtain ⟨-, -, hJs, hnc⟩ := mem_lcal_iff.mp hJ
  refine ⟨hJs, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hnc (isMulCommutative_iff.mpr fun x y => Subtype.ext (hcon x x.2 y y.2))

omit [Finite Γ] in
theorem subset_mul_of_split {R L M W Z : Subgroup Γ} (hdp : IsDirectPair L M R)
    (hLWZ : L ≤ W ∨ L ≤ Z) (hM1 : (M : Set Γ) ⊆ (W : Set Γ) * (Z : Set Γ))
    (hM2 : (M : Set Γ) ⊆ (Z : Set Γ) * (W : Set Γ)) :
    (R : Set Γ) ⊆ (W : Set Γ) * (Z : Set Γ) ∧ (R : Set Γ) ⊆ (Z : Set Γ) * (W : Set Γ) := by
  have hR : ∀ r ∈ R, ∃ l ∈ L, ∃ m ∈ M, r = l * m := by
    intro r hr
    have : r ∈ L ⊔ M := hdp.sup_eq ▸ hr
    obtain ⟨l, hl, m, hm, rfl⟩ := (mem_sup_iff_of_commute hdp.commute).mp this
    exact ⟨l, hl, m, hm, rfl⟩
  have hcm : ∀ l ∈ L, ∀ m ∈ M, l * m = m * l := fun l hl m hm => (hdp.commute l hl m hm).eq
  constructor
  · intro r hr
    obtain ⟨l, hl, m, hm, rfl⟩ := hR r hr
    obtain ⟨w, hw, z, hz, hwz⟩ := hM1 hm
    rcases hLWZ with h | h
    · exact ⟨l * w, mul_mem (h hl) hw, z, hz, by rw [← hwz]; group⟩
    · refine ⟨w, hw, z * l, mul_mem hz (h hl), ?_⟩
      rw [hcm l hl m hm, ← hwz]; group
  · intro r hr
    obtain ⟨l, hl, m, hm, rfl⟩ := hR r hr
    obtain ⟨z, hz, w, hw, hzw⟩ := hM2 hm
    rcases hLWZ with h | h
    · refine ⟨z, hz, w * l, mul_mem hw (h hl), ?_⟩
      rw [hcm l hl m hm, ← hzw]; group
    · exact ⟨l * z, mul_mem (h hl) hz, w, hw, by rw [← hzw]; group⟩

theorem ne_two_of_mem_lcal {p : ℕ} {R J : Subgroup Γ} (hcop : Nat.Coprime p (Nat.card R))
    (hJ : J ∈ lcal R) : p ≠ 2 := by
  rintro rfl
  have hsolv : Group.IsSolvable R :=
    CFSG.SignalizerFunctorTheorem.isSolvable_of_coprime_two R hcop
  obtain ⟨hJR, -, hJs, hnc⟩ := mem_lcal_iff.mp hJ
  have : Group.IsSolvable J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJR)
  have := hJs
  exact hnc (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))

theorem diagSetting_orbitClosure {p : ℕ} {A R J : Subgroup Γ} (hp : p.Prime)
    (hA : IsElemAbelian p A) (hAR : A ≤ Subgroup.normalizer (R : Set Γ)) (hJ : J ∈ lcal R) :
    DiagSetting p A (orbitClosure J A) ∧ lcal (orbitClosure J A) = L514.conjOrbit A J := by
  have hL := L514.isDirectProduct_conjOrbit hAR hJ
  have hsub := L514.conjOrbit_subset_lcal hAR hJ
  have hlcal : lcal (orbitClosure J A) = L514.conjOrbit A J :=
    lcal_eq_of_isDirectProduct hL fun D hD => simple_of_mem_lcal (hsub hD)
  refine ⟨⟨hp, hA, fun a ha => L514.mem_normalizer_orbitClosure ha, hlcal ▸ hL,
    hlcal ▸ ⟨J, L514.self_mem_conjOrbit A J⟩, ?_⟩, hlcal⟩
  rw [hlcal]
  exact fun J₁ h₁ J₂ h₂ => L514.exists_conj_of_mem_conjOrbit h₁ h₂

theorem mul_of_semisimple {p : ℕ} (hp : p.Prime) {A B R₀ : Subgroup Γ} (hA : IsElemAbelian p A)
    (hB : B ≤ A) (hR₀ : IsDirectProduct (lcal R₀) R₀)
    (hAR₀ : A ≤ Subgroup.normalizer (R₀ : Set Γ)) (hcop : Nat.Coprime p (Nat.card R₀))
    (hcyc : ∀ J ∈ lcal R₀, ∃ n ∈ A, A ⊓ Subgroup.normalizer (J : Set Γ) ≤
      (A ⊓ Subgroup.centralizer (orbitClosure J A : Set Γ)) ⊔ Subgroup.zpowers n) :
    ∀ (n : ℕ) (T : Set (Subgroup Γ)), T ⊆ lcal R₀ →
      (∀ J ∈ T, ∀ a ∈ A, J.map (MulAut.conj a).toMonoidHom ∈ T) → T.ncard = n →
      ((sSup T : Subgroup Γ) : Set Γ) ⊆
        (wSub A B (sSup T) : Set Γ) * (cenIn (sSup T) (B : Set Γ) : Set Γ) ∧
      ((sSup T : Subgroup Γ) : Set Γ) ⊆
        (cenIn (sSup T) (B : Set Γ) : Set Γ) * (wSub A B (sSup T) : Set Γ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hTS hTst hTn
  rcases T.eq_empty_or_nonempty with rfl | ⟨J, hJT⟩
  · have h : (sSup (∅ : Set (Subgroup Γ)) : Subgroup Γ) = ⊥ := sSup_empty
    rw [h]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    · rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
      subst hx
      exact ⟨1, one_mem _, 1, one_mem _, one_mul 1⟩
  have hJR : J ∈ lcal R₀ := hTS hJT
  set O := L514.conjOrbit A J with hO
  have hOT : O ⊆ T := by
    rintro _ ⟨a, ha, rfl⟩
    exact hTst J hJT a ha
  set T' := T \ O with hT'
  have hT'S : T' ⊆ lcal R₀ \ O := fun x hx => ⟨hTS hx.1, hx.2⟩
  have hT'st : ∀ J' ∈ T', ∀ a ∈ A, J'.map (MulAut.conj a).toMonoidHom ∈ T' := by
    intro J' hJ' a ha
    refine ⟨hTst J' hJ'.1 a ha, fun hmem => hJ'.2 ?_⟩
    have := L514.map_conj_mem_conjOrbit hmem (inv_mem ha)
    rwa [L514.map_conj_map_conj_inv] at this
  have hdp := isDirectPair_orbitClosure_outsideOrbit' hR₀ hAR₀ hJR
  have hM : sSup T' ≤ L514.outsideOrbit R₀ A J := sSup_le_sSup hT'S
  have hsup : sSup T = orbitClosure J A ⊔ sSup T' := by
    rw [L514.orbitClosure_eq_sSup, ← sSup_union]
    congr 1
    exact (Set.union_sdiff_cancel hOT).symm
  have hdpT : IsDirectPair (orbitClosure J A) (sSup T') (sSup T) :=
    ⟨fun x hx y hy => hdp.commute x hx y (hM hy),
      eq_bot_iff.mpr ((inf_le_inf_left _ hM).trans hdp.inf_eq_bot.le), hsup.symm⟩
  have hlt : T'.ncard < n := by
    rw [← hTn]
    refine Set.ncard_lt_ncard (lt_of_le_of_ne Set.sdiff_subset fun h => ?_) (Set.toFinite T)
    have : J ∈ T' := by rw [h]; exact hJT
    exact this.2 (L514.self_mem_conjOrbit A J)
  have hIH := ih _ hlt T' (hT'S.trans Set.sdiff_subset) hT'st rfl
  obtain ⟨hDS, hlcalL⟩ := diagSetting_orbitClosure hp hA hAR₀ hJR
  have hLT : orbitClosure J A ≤ sSup T := hdpT.sup_eq ▸ le_sup_left
  have hcycL : CycStab A (orbitClosure J A) := by
    intro J' hJ'
    rw [hlcalL] at hJ'
    have hJ'R : J' ∈ lcal R₀ := L514.conjOrbit_subset_lcal hAR₀ hJR hJ'
    obtain ⟨n', hn'A, hn'⟩ := hcyc J' hJ'R
    refine ⟨n', hn'A, ?_⟩
    rw [orbitClosure_eq_of_mem hJ'] at hn'
    exact hn'
  have hcopL : Nat.Coprime p (Nat.card R₀) := hcop
  have hp2 : p ≠ 2 := ne_two_of_mem_lcal hcop hJR
  have hL := le_wSub_or_le_cenIn_of_diagSetting hp2 _ A (orbitClosure J A) B hDS hcycL hB rfl
  have hLWZ : orbitClosure J A ≤ wSub A B (sSup T) ∨
      orbitClosure J A ≤ cenIn (sSup T) (B : Set Γ) := by
    rcases hL with h | h
    · exact Or.inl (h.trans (wSub_mono A B hLT))
    · exact Or.inr (h.trans (cenIn_mono_left hLT _))
  have hM1 : ((sSup T' : Subgroup Γ) : Set Γ) ⊆
      (wSub A B (sSup T) : Set Γ) * (cenIn (sSup T) (B : Set Γ) : Set Γ) := by
    refine hIH.1.trans (Set.mul_subset_mul ?_ ?_)
    · exact fun x hx => wSub_mono A B (hsup ▸ le_sup_right) hx
    · exact fun x hx => cenIn_mono_left (hsup ▸ le_sup_right) _ hx
  have hM2 : ((sSup T' : Subgroup Γ) : Set Γ) ⊆
      (cenIn (sSup T) (B : Set Γ) : Set Γ) * (wSub A B (sSup T) : Set Γ) := by
    refine hIH.2.trans (Set.mul_subset_mul ?_ ?_)
    · exact fun x hx => cenIn_mono_left (hsup ▸ le_sup_right) _ hx
    · exact fun x hx => wSub_mono A B (hsup ▸ le_sup_right) hx
  exact subset_mul_of_split hdpT hLWZ hM1 hM2

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
