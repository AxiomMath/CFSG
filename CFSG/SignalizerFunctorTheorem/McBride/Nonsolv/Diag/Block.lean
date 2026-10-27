module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Subdirect
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Setup

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag

variable {G : Type*} [Group G]

theorem map_conj_one (J : Subgroup G) : J.map (MulAut.conj (1 : G)).toMonoidHom = J := by
  ext x
  simp

theorem mem_normalizer_of_map_conj_eq {J : Subgroup G} {g g' : G}
    (h : J.map (MulAut.conj g).toMonoidHom = J.map (MulAut.conj g').toMonoidHom) :
    g'⁻¹ * g ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 := L514.map_conj_map_conj J g g'⁻¹
  rw [h, L514.map_conj_map_conj_inv] at h1
  exact h1.symm

theorem conj_mem_sSup_diff_map_iff {S : Set (Subgroup G)} {c : G}
    (hc : ∀ J ∈ S, J.map (MulAut.conj c).toMonoidHom ∈ S)
    (hc' : ∀ J ∈ S, J.map (MulAut.conj c⁻¹).toMonoidHom ∈ S) {J : Subgroup G} {y : G} :
    c * y * c⁻¹ ∈ sSup (S \ {J.map (MulAut.conj c).toMonoidHom}) ↔ y ∈ sSup (S \ {J}) := by
  constructor
  · intro h
    have h1 := IsDirectProduct.map_conj_sSup_diff_le (S := S) c⁻¹
      (J.map (MulAut.conj c).toMonoidHom) hc'
    rw [L514.map_conj_map_conj_inv] at h1
    have h2 := h1 ⟨_, h, rfl⟩
    simpa [mul_assoc] using h2
  · intro h
    exact IsDirectProduct.map_conj_sSup_diff_le (S := S) c J hc ⟨y, h, rfl⟩

theorem sSup_inf_sSup_diff_le {S T : Set (Subgroup G)} {K : Subgroup G}
    (hK : IsDirectProduct S K) (hTS : T ⊆ S) {J : Subgroup G} (hJ : J ∈ T) :
    sSup T ⊓ sSup (S \ {J}) ≤ sSup (T \ {J}) := by
  have hJS : J ∈ S := hTS hJ
  have hsub : T \ {J} ⊆ S \ {J} := Set.sdiff_subset_sdiff_left hTS
  have hT : sSup T = J ⊔ sSup (T \ {J}) := by
    conv_lhs => rw [← Set.union_sdiff_cancel (Set.singleton_subset_iff.mpr hJ)]
    rw [sSup_union, sSup_singleton]
  intro z hz
  obtain ⟨hzT, hzS⟩ := Subgroup.mem_inf.mp hz
  rw [hT] at hzT
  obtain ⟨j, hj, l, hl, rfl⟩ := (mem_sup_iff_of_commute fun x hx y hy =>
    hK.commute_sSup_diff hJS x hx y (sSup_le_sSup hsub hy)).mp hzT
  have hjS : j ∈ sSup (S \ {J}) := by
    have := mul_mem hzS (inv_mem (sSup_le_sSup hsub hl))
    simpa using this
  have hj1 : j = 1 := by
    have h1 : j ∈ J ⊓ sSup (S \ {J}) := ⟨hj, hjS⟩
    rw [(hK.indep hJS).eq_bot, Subgroup.mem_bot] at h1
    exact h1
  rw [hj1, one_mul]
  exact hl

theorem projIn_singleton_le (J X : Subgroup G) : projIn {J} J X ≤ X := by
  refine (Subgroup.closure_le X).mpr ?_
  rintro j ⟨-, l, hl, hjl⟩
  have hl1 : l = 1 := by
    rw [Set.sdiff_self, sSup_empty, Subgroup.mem_bot] at hl
    exact hl
  simpa [hl1] using hjl

theorem projIn_mono {S : Set (Subgroup G)} (J : Subgroup G) {X Y : Subgroup G} (h : X ≤ Y) :
    projIn S J X ≤ projIn S J Y :=
  proj_mono h

theorem exists_mul_mem_of_projIn_eq [Finite G] {S : Set (Subgroup G)} {K C : Subgroup G}
    (hK : IsDirectProduct S K) {J : Subgroup G} (hJ : J ∈ S) (hC : projIn S J C = J) {y : G}
    (hy : y ∈ K) : ∃ c ∈ C, c⁻¹ * y ∈ sSup (S \ {J}) := by
  have hpair := hK.isDirectPair hJ
  have hy' : y ∈ J ⊔ sSup (S \ {J}) := hpair.sup_eq ▸ hy
  obtain ⟨j, hj, l, hl, rfl⟩ := (mem_sup_iff_of_commute hpair.commute).mp hy'
  have hj' : j ∈ projIn S J C := by
    rw [hC]
    exact hj
  obtain ⟨-, l', hl', hjl'⟩ := (mem_proj_iff (hK.commute_sSup_diff hJ)).mp hj'
  refine ⟨j * l', hjl', ?_⟩
  have h1 : (j * l')⁻¹ * (j * l) = l'⁻¹ * l := by group
  rw [h1]
  exact mul_mem (inv_mem hl') hl

@[expose] def SameBlock (S : Set (Subgroup G)) (Y J J' : Subgroup G) : Prop :=
  ∀ y ∈ Y, y ∈ sSup (S \ {J}) ↔ y ∈ sSup (S \ {J'})

theorem SameBlock.refl (S : Set (Subgroup G)) (Y J : Subgroup G) : SameBlock S Y J J :=
  fun _ _ => Iff.rfl

theorem SameBlock.symm {S : Set (Subgroup G)} {Y J J' : Subgroup G} (h : SameBlock S Y J J') :
    SameBlock S Y J' J :=
  fun y hy => (h y hy).symm

theorem SameBlock.trans {S : Set (Subgroup G)} {Y J J' J'' : Subgroup G}
    (h : SameBlock S Y J J') (h' : SameBlock S Y J' J'') : SameBlock S Y J J'' :=
  fun y hy => (h y hy).trans (h' y hy)

theorem SameBlock.map_conj {S : Set (Subgroup G)} {Y J J' : Subgroup G} {c : G}
    (hc : ∀ K ∈ S, K.map (MulAut.conj c).toMonoidHom ∈ S)
    (hc' : ∀ K ∈ S, K.map (MulAut.conj c⁻¹).toMonoidHom ∈ S)
    (hcY : c ∈ Subgroup.normalizer (Y : Set G)) (h : SameBlock S Y J J') :
    SameBlock S Y (J.map (MulAut.conj c).toMonoidHom) (J'.map (MulAut.conj c).toMonoidHom) := by
  intro y hy
  obtain ⟨y₀, hy₀, rfl⟩ : ∃ y₀ ∈ Y, y = c * y₀ * c⁻¹ := by
    refine ⟨c⁻¹ * y * c, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hcY) y).mp hy
    simpa using this
  rw [conj_mem_sSup_diff_map_iff hc hc', conj_mem_sSup_diff_map_iff hc hc']
  exact h _ hy₀

theorem mem_sSup_diff_of_mem_block {S : Set (Subgroup G)} {K Y : Subgroup G}
    (hK : IsDirectProduct S K) {P : Set (Set (Subgroup G))} (hU : ⋃₀ P = S)
    (hdisj : P.PairwiseDisjoint id) (hdp : IsDirectProduct ((fun T => Y ⊓ sSup T) '' P) Y)
    {T : Set (Subgroup G)} (hT : T ∈ P) (hdiag : IsDiagonal T (Y ⊓ sSup T))
    {J J' : Subgroup G} (hJ : J ∈ T) (hJ' : J' ∈ T) {y : G} (hy : y ∈ Y)
    (hyJ : y ∈ sSup (S \ {J})) : y ∈ sSup (S \ {J'}) := by
  have hTS : T ⊆ S := hU ▸ Set.subset_sUnion_of_mem hT
  have hD : Y ⊓ sSup T ∈ (fun T => Y ⊓ sSup T) '' P := ⟨T, hT, rfl⟩
  have hrest : sSup (((fun T => Y ⊓ sSup T) '' P) \ {Y ⊓ sSup T}) ≤ sSup (S \ T) := by
    refine sSup_le ?_
    rintro _ ⟨⟨T', hT'P, rfl⟩, hne⟩
    have hTT' : T' ≠ T := fun h => hne (by rw [h]; rfl)
    have hsub : T' ⊆ S \ T := fun x hx =>
      ⟨hU ▸ Set.mem_sUnion_of_mem hx hT'P,
        fun hxT => Set.disjoint_left.mp (hdisj hT'P hT hTT') hx hxT⟩
    exact inf_le_right.trans (sSup_le_sSup hsub)
  have hy' : y ∈ (Y ⊓ sSup T) ⊔ sSup (((fun T => Y ⊓ sSup T) '' P) \ {Y ⊓ sSup T}) := by
    rw [(hdp.isDirectPair hD).sup_eq]
    exact hy
  obtain ⟨d, hd, e, he, rfl⟩ := (mem_sup_iff_of_commute (hdp.commute_sSup_diff hD)).mp hy'
  have heJ : e ∈ sSup (S \ {J}) :=
    sSup_le_sSup (Set.sdiff_subset_sdiff_right (Set.singleton_subset_iff.mpr hJ)) (hrest he)
  have heJ' : e ∈ sSup (S \ {J'}) :=
    sSup_le_sSup (Set.sdiff_subset_sdiff_right (Set.singleton_subset_iff.mpr hJ')) (hrest he)
  have hdJ : d ∈ sSup (S \ {J}) := by
    have := mul_mem hyJ (inv_mem heJ)
    simpa using this
  have hdT : d ∈ sSup (T \ {J}) :=
    sSup_inf_sSup_diff_le hK hTS hJ ⟨(Subgroup.mem_inf.mp hd).2, hdJ⟩
  have hd1 : d = 1 := by
    have h1 : d ∈ (Y ⊓ sSup T) ⊓ sSup (T \ {J}) := ⟨hd, hdT⟩
    rw [(hdiag.2 J hJ).1, Subgroup.mem_bot] at h1
    exact h1
  rw [hd1, one_mul]
  exact heJ'

theorem exists_le_or_sameBlock [Finite G] {K Y : Subgroup G} (hK : IsSemisimple K) (hYK : Y ≤ K)
    (hY : ∀ J ∈ lcal K, projIn (lcal K) J Y = J) {J₀ : Subgroup G} (hJ₀ : J₀ ∈ lcal K) :
    J₀ ≤ Y ∨ ∃ J₁ ∈ lcal K, J₁ ≠ J₀ ∧ SameBlock (lcal K) Y J₀ J₁ := by
  obtain ⟨P, -, hU, hdisj, hdp, hdiag⟩ := exists_partition_isDiagonal hK hYK hY
  have hKdp := hK.isDirectProduct_lcal
  obtain ⟨T, hTP, hJ₀T⟩ : J₀ ∈ ⋃₀ P := hU ▸ hJ₀
  by_cases hT : T = {J₀}
  · left
    subst hT
    have h1 := ((hdiag _ hTP).2 J₀ (Set.mem_singleton J₀)).2
    calc J₀ = projIn {J₀} J₀ (Y ⊓ sSup {J₀}) := h1.symm
      _ ≤ Y ⊓ sSup {J₀} := projIn_singleton_le _ _
      _ ≤ Y := inf_le_left
  · right
    obtain ⟨J₁, hJ₁T, hne⟩ : ∃ J₁ ∈ T, J₁ ≠ J₀ := by
      by_contra hcon
      push Not at hcon
      exact hT (Set.eq_singleton_iff_unique_mem.mpr ⟨hJ₀T, hcon⟩)
    refine ⟨J₁, hU ▸ Set.mem_sUnion_of_mem hJ₁T hTP, hne, fun y hy => ⟨fun h => ?_, fun h => ?_⟩⟩
    · exact mem_sSup_diff_of_mem_block hKdp hU hdisj hdp hTP (hdiag T hTP) hJ₀T hJ₁T hy h
    · exact mem_sSup_diff_of_mem_block hKdp hU hdisj hdp hTP (hdiag T hTP) hJ₁T hJ₀T hy h

theorem le_centralizer_of_forall_sameBlock [Finite G] {S : Set (Subgroup G)} {K Y : Subgroup G}
    {a : G} (hK : IsDirectProduct S K)
    (ha : ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S)
    (ha' : ∀ J ∈ S, J.map (MulAut.conj a⁻¹).toMonoidHom ∈ S) (hYK : Y ≤ K)
    (hC : K ⊓ Subgroup.centralizer {a} ≤ Y)
    (hproj : ∀ J ∈ S, projIn S J (K ⊓ Subgroup.centralizer {a}) = J)
    (hsame : ∀ J ∈ S, SameBlock S Y J (J.map (MulAut.conj a).toMonoidHom)) :
    Y ≤ Subgroup.centralizer {a} := by
  intro y hyY
  have hyK : y ∈ K := hYK hyY
  have hayK : a * y * a⁻¹ ∈ K := hK.conj_mem ha hyK
  have key : ∀ J ∈ S,
      y⁻¹ * (a * y * a⁻¹) ∈ sSup (S \ {J.map (MulAut.conj a).toMonoidHom}) := by
    intro J hJ
    obtain ⟨c, hcC, hz⟩ := exists_mul_mem_of_projIn_eq hK hJ (hproj J hJ) hyK
    have hcY : c ∈ Y := hC hcC
    have hca : c * a = a * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hcC).2
    have hzY : c⁻¹ * y ∈ Y := mul_mem (inv_mem hcY) hyY
    have hz' : c⁻¹ * y ∈ sSup (S \ {J.map (MulAut.conj a).toMonoidHom}) :=
      (hsame J hJ _ hzY).mp hz
    have hz'' : a * (c⁻¹ * y) * a⁻¹ ∈ sSup (S \ {J.map (MulAut.conj a).toMonoidHom}) :=
      (conj_mem_sSup_diff_map_iff ha ha').mpr hz
    have hcac : c * a * c⁻¹ = a := by rw [hca, mul_inv_cancel_right]
    have heq : y⁻¹ * (a * y * a⁻¹) = (c⁻¹ * y)⁻¹ * (a * (c⁻¹ * y) * a⁻¹) :=
      calc y⁻¹ * (a * y * a⁻¹) = y⁻¹ * (c * a * c⁻¹) * y * a⁻¹ := by rw [hcac]; group
        _ = (c⁻¹ * y)⁻¹ * (a * (c⁻¹ * y) * a⁻¹) := by group
    rw [heq]
    exact mul_mem (inv_mem hz') hz''
  have key' : ∀ J ∈ S, y⁻¹ * (a * y * a⁻¹) ∈ sSup (S \ {J}) := by
    intro J hJ
    have h1 := key _ (ha' J hJ)
    have h2 : (J.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom = J := by
      simpa using L514.map_conj_map_conj_inv J a⁻¹
    rwa [h2] at h1
  have hwK : y⁻¹ * (a * y * a⁻¹) ∈ K := mul_mem (inv_mem hyK) hayK
  have hw1 : y⁻¹ * (a * y * a⁻¹) = 1 := by
    have h1 : (⟨_, hwK⟩ : K) = 1 := hK.ext_coord fun J hJ => by
      rw [map_one]
      exact (hK.coord_eq_one_iff hJ ⟨_, hwK⟩).mpr (key' J hJ)
    exact congrArg Subtype.val h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : y = a * y * a⁻¹ := inv_mul_eq_one.mp hw1
  calc y * a = (a * y * a⁻¹) * a := by rw [← h1]
    _ = a * y := by group

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag
