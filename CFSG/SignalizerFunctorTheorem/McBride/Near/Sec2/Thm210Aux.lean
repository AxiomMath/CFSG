module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Transport
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210

variable {Γ : Type*} [Group Γ]

theorem fittingSubgroupOf_conj_mem {H : Subgroup Γ} {c : Γ} (hc : c ∈ H) {x : Γ}
    (hx : x ∈ CFSG.fittingSubgroupOf H) : c * x * c⁻¹ ∈ CFSG.fittingSubgroupOf H := by
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr ⟨⟨c, hc⟩ * x' * ⟨c, hc⟩⁻¹,
    (CFSG.fittingSubgroup_normal (G := ↥H)).conj_mem x' hx' ⟨c, hc⟩, rfl⟩

theorem le_normalizer_fittingSubgroupOf (H : Subgroup Γ) :
    H ≤ Subgroup.normalizer (CFSG.fittingSubgroupOf H : Set Γ) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => fittingSubgroupOf_conj_mem hc hx, fun hx => ?_⟩
  have := fittingSubgroupOf_conj_mem (inv_mem hc) hx
  simpa [mul_assoc] using this

theorem le_fittingSubgroupOf_of_nilpotent {H N : Subgroup Γ} (hNH : N ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set Γ)) (hnil : Group.IsNilpotent N) :
    N ≤ CFSG.fittingSubgroupOf H := by
  have hnorm : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hN
  have hnil' : Group.IsNilpotent (N.subgroupOf H) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hle : N.subgroupOf H ≤ CFSG.fittingSubgroup ↥H := le_sSup ⟨hnorm, hnil'⟩
  intro x hx
  exact ⟨⟨x, hNH hx⟩, hle hx, rfl⟩

theorem isNilpotent_fittingSubgroupOf [Finite Γ] (H : Subgroup Γ) :
    Group.IsNilpotent (CFSG.fittingSubgroupOf H) := by
  have : Group.IsNilpotent (CFSG.fittingSubgroup ↥H) := inferInstance
  exact Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective)

theorem fittingSubgroupOf_map_of_injective {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    (hφ : Function.Injective φ) (H : Subgroup X) :
    CFSG.fittingSubgroupOf (H.map φ) = (CFSG.fittingSubgroupOf H).map φ := by
  let e : H ≃* H.map φ := Subgroup.equivMapOfInjective H φ hφ
  have h1 := fittingSubgroup_map_equiv e
  have h2 : (H.map φ).subtype.comp e.toMonoidHom = φ.comp H.subtype := by
    ext x
    rfl
  unfold CFSG.fittingSubgroupOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

theorem fittingSubgroupOf_conj_mem_of_mem_normalizer {H : Subgroup Γ} {a : Γ}
    (ha : a ∈ Subgroup.normalizer (H : Set Γ)) {x : Γ} (hx : x ∈ CFSG.fittingSubgroupOf H) :
    a * x * a⁻¹ ∈ CFSG.fittingSubgroupOf H := by
  have h1 := fittingSubgroupOf_map_of_injective (MulAut.conj a).toMonoidHom
    (MulAut.conj a).injective H
  have hmap : H.map (MulAut.conj a).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ha
  rw [hmap] at h1
  rw [h1]
  exact ⟨x, hx, rfl⟩

theorem isSolvable_pi_of_finite {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, Group.IsSolvable (G i)] : Group.IsSolvable (∀ i, G i) := by
  cases nonempty_fintype ι
  have hle : ∀ k : ℕ, derivedSeries (∀ i, G i) k ≤
      Subgroup.pi Set.univ (fun i => derivedSeries (G i) k) := by
    intro k
    induction k with
    | zero =>
      simp only [derivedSeries_zero]
      rw [Subgroup.pi_top]
    | succ k ih =>
      rw [derivedSeries_succ]
      calc ⁅derivedSeries (∀ i, G i) k, derivedSeries (∀ i, G i) k⁆
          ≤ ⁅Subgroup.pi Set.univ (fun i => derivedSeries (G i) k),
              Subgroup.pi Set.univ (fun i => derivedSeries (G i) k)⁆ :=
            Subgroup.commutator_mono ih ih
        _ ≤ Subgroup.pi Set.univ (fun i => ⁅derivedSeries (G i) k, derivedSeries (G i) k⁆) :=
            Subgroup.commutator_pi_pi_le _ _
        _ = Subgroup.pi Set.univ (fun i => derivedSeries (G i) (k + 1)) := by
            simp_rw [derivedSeries_succ]
  choose n hn using fun i => (inferInstance : Group.IsSolvable (G i)).solvable
  refine ⟨⟨Finset.univ.sup n, ?_⟩⟩
  rw [eq_bot_iff]
  refine (hle _).trans ?_
  rw [le_bot_iff, Subgroup.pi_eq_bot_iff]
  intro i
  rw [eq_bot_iff, ← hn i]
  exact derivedSeries_antitone (G i) (Finset.le_sup (f := n) (Finset.mem_univ i))

section DirectProduct

variable {S : Set (Subgroup Γ)} {L : Subgroup Γ}

theorem isDirectProduct_image (hL : IsDirectProduct S L) (T : Subgroup Γ → Subgroup Γ)
    (hT : ∀ J ∈ S, T J ≤ J) :
    IsDirectProduct {K | ∃ J ∈ S, K = T J} (sSup {K | ∃ J ∈ S, K = T J}) where
  commute := by
    rintro _ ⟨J₁, hJ₁, rfl⟩ _ ⟨J₂, hJ₂, rfl⟩ hne x hx y hy
    have hJ : J₁ ≠ J₂ := fun h => hne (h ▸ rfl)
    exact hL.commute J₁ hJ₁ J₂ hJ₂ hJ x (hT J₁ hJ₁ hx) y (hT J₂ hJ₂ hy)
  indep := by
    rintro _ ⟨J, hJ, rfl⟩
    refine Disjoint.mono (hT J hJ) ?_ (hL.indep hJ)
    refine sSup_le ?_
    rintro _ ⟨⟨J', hJ', rfl⟩, hne⟩
    have hJJ' : J' ≠ J := fun h => hne (h ▸ rfl)
    exact (hT J' hJ').trans (le_sSup ⟨hJ', hJJ'⟩)
  sSup_eq := rfl

variable [Finite Γ]

theorem mem_sSup_image_iff (hL : IsDirectProduct S L) {T : Subgroup Γ → Subgroup Γ}
    (hT : ∀ J ∈ S, T J ≤ J) {x : Γ} :
    x ∈ sSup {K | ∃ J ∈ S, K = T J} ↔
      ∃ hx : x ∈ L, ∀ (J : Subgroup Γ) (hJ : J ∈ S), ((hL.coord hJ ⟨x, hx⟩ : J) : Γ) ∈ T J := by
  constructor
  · intro hx
    let Q : Subgroup ↥L := ⨅ J : S, ((T J.1).subgroupOf J.1).comap (hL.coord J.2)
    have hle : sSup {K | ∃ J ∈ S, K = T J} ≤ Q.map L.subtype := by
      refine sSup_le ?_
      rintro _ ⟨J', hJ', rfl⟩ y hy
      refine ⟨⟨y, hL.le hJ' (hT J' hJ' hy)⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_iInf]
      rintro ⟨J, hJ⟩
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      by_cases h : J' = J
      · subst h
        have := hL.coord_of_mem hJ (hT J' hJ' hy)
        simpa [this] using hy
      · have := hL.coord_of_mem_ne hJ hJ' h (hT J' hJ' hy)
        simp [this]
    obtain ⟨y, hyQ, rfl⟩ := hle hx
    refine ⟨y.2, fun J hJ => ?_⟩
    have := Subgroup.mem_iInf.mp hyQ ⟨J, hJ⟩
    rwa [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at this
  · rintro ⟨hx, h⟩
    refine hL.mem_of_coord_mem hx (M := sSup {K | ∃ J ∈ S, K = T J}) fun J hJ => ?_
    have hTJ : T J ≤ sSup {K | ∃ J ∈ S, K = T J} := le_sSup ⟨J, hJ, rfl⟩
    exact hTJ (h J hJ)

theorem le_sSup_image_iff (hL : IsDirectProduct S L) {T : Subgroup Γ → Subgroup Γ}
    (hT : ∀ J ∈ S, T J ≤ J) {X : Subgroup Γ} :
    X ≤ sSup {K | ∃ J ∈ S, K = T J} ↔ X ≤ L ∧ ∀ J ∈ S, projIn S J X ≤ T J := by
  constructor
  · intro hX
    refine ⟨fun x hx => ((mem_sSup_image_iff hL hT).mp (hX hx)).1, fun J hJ x hx => ?_⟩
    obtain ⟨y, hyX, rfl⟩ := (hL.mem_projIn_iff hJ).mp hx
    obtain ⟨_, h⟩ := (mem_sSup_image_iff hL hT).mp (hX hyX)
    exact h J hJ
  · rintro ⟨hXL, h⟩ x hx
    refine (mem_sSup_image_iff hL hT).mpr ⟨hXL hx, fun J hJ => ?_⟩
    exact h J hJ ((hL.mem_projIn_iff hJ).mpr ⟨⟨x, hXL hx⟩, hx, rfl⟩)

@[expose] noncomputable def projInHom (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S)
    {X : Subgroup Γ} (hXL : X ≤ L) : ↥X →* ↥(projIn S J X) :=
  (J.subtype.comp ((hL.coord hJ).comp (Subgroup.inclusion hXL))).codRestrict (projIn S J X)
    fun x => (hL.mem_projIn_iff hJ).mpr ⟨⟨x, hXL x.2⟩, x.2, rfl⟩

theorem projInHom_apply (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S)
    {X : Subgroup Γ} (hXL : X ≤ L) (x : X) :
    ((projInHom hL hJ hXL x : projIn S J X) : Γ) = ((hL.coord hJ ⟨x, hXL x.2⟩ : J) : Γ) :=
  rfl

theorem projInHom_surjective (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S)
    {X : Subgroup Γ} (hXL : X ≤ L) : Function.Surjective (projInHom hL hJ hXL) := by
  intro z
  obtain ⟨y, hyX, hy⟩ := (hL.mem_projIn_iff hJ).mp z.2
  exact ⟨⟨y, hyX⟩, Subtype.ext hy⟩

theorem isSolvable_projIn (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S)
    {X : Subgroup Γ} (hXL : X ≤ L) (hX : Group.IsSolvable X) :
    Group.IsSolvable (projIn S J X) :=
  Group.isSolvable_of_surjective (projInHom_surjective hL hJ hXL)

theorem isNilpotent_projIn (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S)
    {X : Subgroup Γ} (hXL : X ≤ L) (hX : Group.IsNilpotent X) :
    Group.IsNilpotent (projIn S J X) :=
  Group.nilpotent_of_surjective _ (projInHom_surjective hL hJ hXL)

theorem isMulCommutative_projIn (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S)
    {X : Subgroup Γ} (hXL : X ≤ L) (hX : IsMulCommutative X) :
    IsMulCommutative (projIn S J X) := by
  rw [isMulCommutative_iff]
  intro a b
  obtain ⟨a', rfl⟩ := projInHom_surjective hL hJ hXL a
  obtain ⟨b', rfl⟩ := projInHom_surjective hL hJ hXL b
  rw [← map_mul, ← map_mul, mul_comm' a' b']

theorem projIn_conj_mem (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S)
    {Y X : Subgroup Γ} (hYX : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X) :
    ∀ c ∈ projIn S J Y, ∀ z ∈ projIn S J X, c * z * c⁻¹ ∈ projIn S J X := by
  intro c hc z hz
  obtain ⟨y, hyY, rfl⟩ := (hL.mem_projIn_iff hJ).mp hc
  obtain ⟨x, hxX, rfl⟩ := (hL.mem_projIn_iff hJ).mp hz
  refine (hL.mem_projIn_iff hJ).mpr ⟨y * x * y⁻¹, ?_, ?_⟩
  · exact hYX y hyY x hxX
  · simp

theorem projInHom_injective_pi (hL : IsDirectProduct S L) {H : Subgroup Γ} (hHL : H ≤ L) :
    Function.Injective
      (MonoidHom.pi (fun J : S => projInHom hL J.2 hHL) :
        ↥H →* ((J : S) → ↥(projIn S J.1 H))) := by
  intro x y hxy
  have h : (⟨x, hHL x.2⟩ : L) = ⟨y, hHL y.2⟩ := by
    refine hL.ext_coord fun J hJ => ?_
    have h1 := congrArg Subtype.val (congrFun hxy ⟨J, hJ⟩)
    exact Subtype.ext h1
  exact Subtype.ext (congrArg (Subtype.val : L → Γ) h)

theorem isSolvable_of_forall_projIn (hL : IsDirectProduct S L) {H : Subgroup Γ} (hHL : H ≤ L)
    (h : ∀ J ∈ S, Group.IsSolvable (projIn S J H)) : Group.IsSolvable H := by
  have : Finite S := Set.toFinite S
  have : ∀ J : S, Group.IsSolvable ↥(projIn S J.1 H) := fun J => h J.1 J.2
  have : Group.IsSolvable ((J : S) → ↥(projIn S J.1 H)) := isSolvable_pi_of_finite
  exact Group.isSolvable_of_isSolvable_injective (projInHom_injective_pi hL hHL)

theorem isNilpotent_of_forall_projIn (hL : IsDirectProduct S L) {H : Subgroup Γ} (hHL : H ≤ L)
    (h : ∀ J ∈ S, Group.IsNilpotent (projIn S J H)) : Group.IsNilpotent H := by
  have : Finite S := Set.toFinite S
  have : ∀ J : S, Group.IsNilpotent ↥(projIn S J.1 H) := fun J => h J.1 J.2
  let φ : ↥H →* ((J : S) → ↥(projIn S J.1 H)) :=
    MonoidHom.pi (fun J : S => projInHom hL J.2 hHL)
  have hφ : Function.Injective φ := projInHom_injective_pi hL hHL
  exact Group.nilpotent_of_mulEquiv (MonoidHom.ofInjective hφ).symm

theorem isMulCommutative_of_forall_projIn (hL : IsDirectProduct S L) {H : Subgroup Γ}
    (hHL : H ≤ L) (h : ∀ J ∈ S, IsMulCommutative (projIn S J H)) : IsMulCommutative H := by
  rw [isMulCommutative_iff]
  intro a b
  apply projInHom_injective_pi hL hHL
  funext J
  rw [map_mul, map_mul, Pi.mul_apply, Pi.mul_apply]
  have := h J.1 J.2
  exact mul_comm' _ _

end DirectProduct

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210
