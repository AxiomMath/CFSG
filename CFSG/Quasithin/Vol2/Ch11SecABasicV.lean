module

public import CFSG.Quasithin.Vol2.Ch11SecABasic
public import CFSG.Quasithin.Background.BlueprintB2Reduced
public import CFSG.Quasithin.Vol2.Ch11StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem le_normalizer_conjClosure_of_le' {Z H K : Subgroup G}
    (hZ : K ≤ Subgroup.normalizer (Z : Set G)) (hH : H ≤ Subgroup.normalizer (K : Set G)) :
    K ≤ Subgroup.normalizer (conjClosure Z H : Set G) := by
  have key : ∀ k ∈ K, ∀ x ∈ conjClosure Z H, k * x * k⁻¹ ∈ conjClosure Z H := by
    intro k hk x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hx
      have hk' : h⁻¹ * k * h ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (hH (H.inv_mem hh)) k).mp hk
        simpa using this
      have hz' : (h⁻¹ * k * h) * z * (h⁻¹ * k * h)⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hZ hk') z).mp hz
      have := mem_conjClosure hh hz'
      simpa [mul_assoc] using this
    | one => simp
    | mul x y _ _ ihx ihy =>
      simpa [mul_assoc] using (conjClosure Z H).mul_mem ihx ihy
    | inv x _ ihx =>
      simpa [mul_assoc] using (conjClosure Z H).inv_mem ihx
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key k hk x, fun hx => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hx
  simpa [mul_assoc] using this

theorem open_pCore_eq (p : ℕ) (X : Type*) [Group X] : CFSG.Open.pCore p X = CFSG.pCore p X :=
  (CFSG.pCore_eq_open X p).symm

variable [Finite G]

theorem reducedAggregate_props (X : Subgroup G) :
    (∀ x ∈ reducedAggregate X, x ^ 2 = 1) ∧
      (∀ x ∈ reducedAggregate X, ∀ y ∈ reducedAggregate X, x * y = y * x) ∧
      reducedAggregate X ≤ pCoreOf 2 X ∧
      X ≤ Subgroup.normalizer (reducedAggregate X : Set G) := by
  obtain ⟨hN, -, hZ⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥X) 2
  have hmem : ∀ x ∈ reducedAggregate X, ∃ x' : ↥X, x' ∈ CFSG.pCore 2 ↥X ∧
      (∀ k ∈ CFSG.pCore 2 ↥X, k * x' = x' * k) ∧ x' ^ 2 = 1 ∧ (x' : G) = x := by
    rintro x ⟨x', hx', rfl⟩
    obtain ⟨h1, h2, h3⟩ := BlueprintB2.mem_centerTorsion_iff.mp (hZ hx')
    exact ⟨x', h1, h2, h3, rfl⟩
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_, ?_, ?_⟩
  · obtain ⟨x', -, -, h3, rfl⟩ := hmem x hx
    rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
  · obtain ⟨x', hx1, -, -, rfl⟩ := hmem x hx
    obtain ⟨y', -, hy2, -, rfl⟩ := hmem y hy
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hy2 x' hx1]
  · refine Subgroup.map_mono fun x' hx' => ?_
    exact (BlueprintB2.mem_centerTorsion_iff.mp (hZ hx')).1
  · have hsub : (reducedAggregate X).subgroupOf X = primeReducedAggregate (↥X) 2 :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    have : ((reducedAggregate X).subgroupOf X).Normal := by
      rw [hsub]
      exact hN
    exact Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le _)

variable {T L I : Subgroup G} {n : ℕ}

theorem fsuV_le_reducedAggregate (h : Hyp11 G T L I n) :
    fsuV T I ≤ reducedAggregate (L ⊔ T) := by
  have hN := (reducedAggregate_props (L ⊔ T)).2.2.2
  refine conjClosure_le fun t ht z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_sup_right ht)) z).mp
    (h.fsu.irrPlus.1 hz)

theorem fsuV_le_T (h : Hyp11 G T L I n) : fsuV T I ≤ T := by
  have hS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right
  exact (fsuV_le_reducedAggregate h).trans ((reducedAggregate_props (L ⊔ T)).2.2.1.trans
    (pCoreOf_two_le_of_sylowIn hS.1 hS.2.1 hS.2.2))

theorem isElemAbelian_fsuV (h : Hyp11 G T L I n) : IsElemAbelian 2 (fsuV T I) := by
  obtain ⟨hsq, hcomm, -⟩ := reducedAggregate_props (L ⊔ T)
  have hV := fsuV_le_reducedAggregate h
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (hV a.2) _ (hV b.2))⟩⟩, fun x hx => hsq x (hV hx)⟩

theorem isPGroup_fsuV (h : Hyp11 G T L I n) : IsPGroup 2 (fsuV T I) := fun g =>
  ⟨1, Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 g g.2)⟩

theorem fsuV_ne_bot (h : Hyp11 G T L I n) : fsuV T I ≠ ⊥ := fun hV =>
  h.fsu.irrPlus.2.1 (le_bot_iff.mp (hV ▸ le_conjClosure I T))

omit [Finite G] in
theorem T_le_normalizer_fsuV (T I : Subgroup G) :
    T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
  le_normalizer_conjClosure I T

theorem L_le_normalizer_fsuV (h : Hyp11 G T L I n) :
    L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
  have hLI : L ≤ Subgroup.normalizer (I : Set G) :=
    (le_conjClosure L T).trans h.fsu.irrPlus.2.2.1
  exact le_normalizer_conjClosure_of_le' hLI h.normal

theorem fsuV_le_normalizer_L (h : Hyp11 G T L I n) :
    fsuV T I ≤ Subgroup.normalizer (L : Set G) :=
  (fsuV_le_T h).trans h.normal

theorem normalizer_fsuV_le (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) :
    Subgroup.normalizer (fsuV T I : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  normalizer_le_of_isPGroup h331 h (isPGroup_fsuV h) (fsuV_ne_bot h)
    (sup_le (L_le_normalizer_fsuV h) (T_le_normalizer_fsuV T I))

namespace IsVi

variable {i : ℕ} {U : Subgroup G}

omit [Finite G] in
theorem cV_le (hU : IsVi T L I n i U) : fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≤ U :=
  hU.1.1

omit [Finite G] in
theorem le_fsuV (hU : IsVi T L I n i U) : U ≤ fsuV T I :=
  hU.1.2.1

omit [Finite G] in
theorem le_normalizer (hU : IsVi T L I n i U) : T ≤ Subgroup.normalizer (U : Set G) :=
  hU.2

omit [Finite G] in
theorem isEndStable (hU : IsVi T L I n i U) :
    IsEndStable L (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) U :=
  hU.1.2.2.1

omit [Finite G] in
theorem relIndex_eq (hU : IsVi T L I n i U) :
    (fsuV T I ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ (n * i) :=
  hU.1.2.2.2.1

theorem ne_bot (h : Hyp11 G T L I n) (hU : IsVi T L I n i U) (hi : 1 ≤ i) : U ≠ ⊥ := by
  rintro rfl
  have h1 := relIndex_eq hU
  rw [Subgroup.relIndex_bot_right] at h1
  have h2 : 1 < 2 ^ (n * i) := Nat.one_lt_two_pow (Nat.mul_ne_zero (by have := h.one_lt; omega)
    (by omega))
  omega

end IsVi

theorem kind_cases (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n := by
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  rcases hk with ⟨K, hF, hK, hc, he, -⟩ | ⟨K, hF, hK, hc, he, -⟩ | ⟨K, hF, hK, hc, he, -⟩
  · exact Or.inl ⟨K, hF, hK, hc, he⟩
  · exact Or.inr (Or.inl ⟨K, hF, hK, hc, he⟩)
  · exact Or.inr (Or.inr ⟨K, hF, hK, hc, he⟩)

end CFSG.Quasithin.Vol2.Ch11.SecA
