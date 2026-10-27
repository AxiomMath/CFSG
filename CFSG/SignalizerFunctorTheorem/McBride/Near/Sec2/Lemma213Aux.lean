module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210gAux

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma213

variable {Γ : Type*} [Group Γ]

theorem admits_cenIn {Q X Y : Subgroup Γ} (hX : Admits Q X) (hY : Admits Q Y) :
    Admits Q (cenIn X (Y : Set Γ)) := by
  refine Thm210.le_normalizer_of_conj_mem fun q hq x hx => ?_
  obtain ⟨hxX, hxY⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hX hq) x).1 hxX, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : q⁻¹ * y * q ∈ Y := (Subgroup.mem_normalizer_iff''.1 (hY hq) y).1 hy
  have h1 := Subgroup.mem_centralizer_iff.1 hxY _ hy'
  calc y * (q * x * q⁻¹) = q * ((q⁻¹ * y * q) * x) * q⁻¹ := by group
    _ = q * (x * (q⁻¹ * y * q)) * q⁻¹ := by rw [h1]
    _ = (q * x * q⁻¹) * y := by group

theorem centralizer_bot : Subgroup.centralizer ((⊥ : Subgroup Γ) : Set Γ) = ⊤ :=
  Subgroup.centralizer_eq_top_iff_subset.mpr fun x hx => by
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
    rw [hx]
    exact Subgroup.one_mem _

theorem ne_bot_of_mem_lcal {X J : Subgroup Γ} (hJ : J ∈ lcal X) : J ≠ ⊥ := by
  rintro rfl
  obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJ
  exact hnc inferInstance

theorem eq_one_of_forall_commute {J : Subgroup Γ} (hJs : IsSimpleGroup ↥J)
    (hnc : ¬ IsMulCommutative ↥J) {z : ↥J} (hz : ∀ t : ↥J, t * z = z * t) : z = 1 := by
  have h := Diagonal.center_eq_bot (exists_mul_ne_of_not_isMulCommutative hnc)
  have hmem : z ∈ Subgroup.center ↥J := Subgroup.mem_center_iff.mpr hz
  rwa [h, Subgroup.mem_bot] at hmem

theorem isDirectPair_cenIn {K₁ K₂ K A : Subgroup Γ} (h : IsDirectPair K₁ K₂ K)
    (h₁ : Admits A K₁) (h₂ : Admits A K₂) :
    IsDirectPair (cenIn K₁ (A : Set Γ)) (cenIn K₂ (A : Set Γ)) (cenIn K (A : Set Γ)) where
  commute x hx y hy := h.commute x (Subgroup.mem_inf.1 hx).1 y (Subgroup.mem_inf.1 hy).1
  inf_eq_bot := le_bot_iff.1 ((inf_le_inf inf_le_left inf_le_left).trans h.inf_eq_bot.le)
  sup_eq := by
    refine le_antisymm (sup_le (inf_le_inf_right _ (le_sup_left.trans h.sup_eq.le))
      (inf_le_inf_right _ (le_sup_right.trans h.sup_eq.le))) ?_
    intro d hd
    obtain ⟨hdK, hdA⟩ := Subgroup.mem_inf.1 hd
    rw [← h.sup_eq] at hdK
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_sup_iff_of_commute h.commute).1 hdK
    have key : ∀ a ∈ A, a * k₁ * a⁻¹ = k₁ ∧ a * k₂ * a⁻¹ = k₂ := by
      intro a ha
      have huv : (a * k₁ * a⁻¹) * (a * k₂ * a⁻¹) = k₁ * k₂ := by
        have h1 : a * (k₁ * k₂) * a⁻¹ = k₁ * k₂ := by
          rw [mul_inv_eq_iff_eq_mul]
          exact (Subgroup.mem_centralizer_iff.1 hdA a ha)
        rw [← h1]
        group
      have hu : a * k₁ * a⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.1 (h₁ ha) k₁).1 hk₁
      have hv : a * k₂ * a⁻¹ ∈ K₂ := (Subgroup.mem_normalizer_iff.1 (h₂ ha) k₂).1 hk₂
      have e : k₁⁻¹ * (a * k₁ * a⁻¹) = k₂ * (a * k₂ * a⁻¹)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc k₁⁻¹ * (a * k₁ * a⁻¹) * (a * k₂ * a⁻¹)
            = k₁⁻¹ * ((a * k₁ * a⁻¹) * (a * k₂ * a⁻¹)) := by group
          _ = k₂ := by rw [huv]; group
      have hmem : k₁⁻¹ * (a * k₁ * a⁻¹) ∈ K₁ ⊓ K₂ :=
        Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hk₁) hu, e ▸ mul_mem hk₂ (inv_mem hv)⟩
      rw [h.inf_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have hu1 : a * k₁ * a⁻¹ = k₁ := hmem.symm
      refine ⟨hu1, ?_⟩
      have : k₁ * k₂ = k₁ * (a * k₂ * a⁻¹) := by
        calc k₁ * k₂ = (a * k₁ * a⁻¹) * (a * k₂ * a⁻¹) := huv.symm
          _ = k₁ * (a * k₂ * a⁻¹) := by rw [hu1]
      exact (mul_left_cancel this).symm
    refine Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨hk₁, ?_⟩) (Subgroup.mem_inf.2 ⟨hk₂, ?_⟩)
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact mul_inv_eq_iff_eq_mul.1 (key a ha).1
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact mul_inv_eq_iff_eq_mul.1 (key a ha).2

section Finite

variable [Finite Γ] {L : Set (Subgroup Γ)} {K : Subgroup Γ}

theorem le_projIn_self (hK : IsDirectProduct L K) {J : Subgroup Γ} (hJ : J ∈ L) :
    J ≤ projIn L J J := fun t ht =>
  (hK.mem_projIn_iff hJ).2 ⟨⟨t, hK.le hJ ht⟩, ht, hK.coord_of_mem hJ ht⟩

theorem coord_eq_one_of_commute (hK : IsDirectProduct L K) {J : Subgroup Γ} (hJ : J ∈ L)
    (hJs : IsSimpleGroup ↥J) (hJnc : ¬ IsMulCommutative ↥J) {P : Subgroup Γ}
    (hP : J ≤ projIn L J P) {y : Γ} (hyK : y ∈ K) (hy : ∀ p ∈ P, p * y = y * p) :
    hK.coord hJ ⟨y, hyK⟩ = 1 := by
  refine eq_one_of_forall_commute hJs hJnc fun t => ?_
  obtain ⟨u, huP, hut⟩ := (hK.mem_projIn_iff hJ).1 (hP t.2)
  have hcomm : u * ⟨y, hyK⟩ = ⟨y, hyK⟩ * u := Subtype.ext (hy u huP)
  have h1 := congrArg (hK.coord hJ) hcomm
  rw [map_mul, map_mul] at h1
  have hu : hK.coord hJ u = t := Subtype.ext hut
  rwa [hu] at h1

theorem cenIn_sSup_eq (hK : IsDirectProduct L K)
    (hL : ∀ J ∈ L, IsSimpleGroup ↥J ∧ ¬ IsMulCommutative ↥J) {T : Set (Subgroup Γ)} (hT : T ⊆ L) :
    cenIn K ((sSup T : Subgroup Γ) : Set Γ) = sSup (L \ T) := by
  refine le_antisymm (fun y hy => ?_) (le_inf (hK.sSup_diff_le _ Set.sdiff_subset) ?_)
  · obtain ⟨hyK, hyc⟩ := Subgroup.mem_inf.1 hy
    refine hK.mem_of_coord_mem hyK fun J hJ => ?_
    by_cases hJT : J ∈ T
    · have h1 : hK.coord hJ ⟨y, hyK⟩ = 1 :=
        coord_eq_one_of_commute hK hJ (hL J hJ).1 (hL J hJ).2 (P := J) (le_projIn_self hK hJ) hyK
          fun p hp => Subgroup.mem_centralizer_iff.1 hyc p (le_sSup hJT hp)
      rw [h1]
      exact one_mem _
    · exact le_sSup (show J ∈ L \ T from ⟨hJ, hJT⟩) (hK.coord hJ ⟨y, hyK⟩).2
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Thm210g.commute_sSup_sSup hK hT Set.sdiff_subset Set.disjoint_sdiff_right x hx y hy).eq

theorem projIn_map_conj_le (hK : IsDirectProduct L K) {z : Γ}
    (hz : ∀ J ∈ L, J.map (MulAut.conj z).toMonoidHom ∈ L)
    (hz' : ∀ J ∈ L, J.map (MulAut.conj z⁻¹).toMonoidHom ∈ L) {X : Subgroup Γ}
    (hzX : z ∈ Subgroup.normalizer (X : Set Γ)) {J : Subgroup Γ} (hJ : J ∈ L) :
    projIn L (J.map (MulAut.conj z).toMonoidHom) X ≤
      (projIn L J X).map (MulAut.conj z).toMonoidHom := by
  intro x hx
  obtain ⟨y, hyX, hyx⟩ := (hK.mem_projIn_iff (hz J hJ)).1 hx
  have hy'K : z⁻¹ * (y : Γ) * z ∈ K := by
    simpa using hK.conj_mem hz' y.2
  have hy'X : z⁻¹ * (y : Γ) * z ∈ X := (Subgroup.mem_normalizer_iff''.1 hzX _).1 hyX
  have h1 := hK.coord_conj hz hJ hy'K
  have e : (⟨z * (z⁻¹ * (y : Γ) * z) * z⁻¹, hK.conj_mem hz hy'K⟩ : K) = y :=
    Subtype.ext (by group)
  rw [e] at h1
  refine ⟨((hK.coord hJ ⟨z⁻¹ * (y : Γ) * z, hy'K⟩ : J) : Γ), ?_, ?_⟩
  · exact (hK.mem_projIn_iff hJ).2 ⟨⟨z⁻¹ * (y : Γ) * z, hy'K⟩, hy'X, rfl⟩
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hyx]
    exact h1.symm

theorem isPerfect_projIn (hK : IsDirectProduct L K) {J : Subgroup Γ} (hJ : J ∈ L)
    {W : Subgroup Γ} (hWK : W ≤ K) [Group.IsPerfect ↥W] : Group.IsPerfect ↥(projIn L J W) :=
  Group.IsPerfect.ofSurjective (f := Thm210.projInHom hK hJ hWK)
    (Thm210.projInHom_surjective hK hJ hWK)

theorem projIn_eq_bot_or_not_isSolvable (hK : IsDirectProduct L K) {J : Subgroup Γ} (hJ : J ∈ L)
    {W : Subgroup Γ} (hWK : W ≤ K) [Group.IsPerfect ↥W] :
    projIn L J W = ⊥ ∨ ¬ Group.IsSolvable ↥(projIn L J W) := by
  have := isPerfect_projIn hK hJ hWK (W := W)
  rcases eq_or_ne (projIn L J W) ⊥ with h | h
  · exact Or.inl h
  · have : Nontrivial ↥(projIn L J W) := (Subgroup.nontrivial_iff_ne_bot _).2 h
    exact Or.inr (Group.IsPerfect.not_isSolvable _)

end Finite

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma213
