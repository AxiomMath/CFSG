module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNLift
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

variable {X X' : Type} [Group X] [Group X'] (e : X ≃* X')

namespace NGM

theorem map_symm_map (H : Subgroup X) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  ext x
  rw [mem_map_equiv, mem_map_equiv, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

theorem exists_eq_map (H : Subgroup X') : ∃ K : Subgroup X, H = K.map e.toMonoidHom :=
  ⟨H.map e.symm.toMonoidHom, by simpa using (map_symm_map e.symm H).symm⟩

theorem map_le_map_equiv_iff {H K : Subgroup X} :
    H.map e.toMonoidHom ≤ K.map e.toMonoidHom ↔ H ≤ K :=
  map_le_map_iff_of_injective e.injective

theorem map_inf_equiv (H K : Subgroup X) :
    (H ⊓ K).map e.toMonoidHom = H.map e.toMonoidHom ⊓ K.map e.toMonoidHom :=
  map_inf_eq H K _ e.injective

theorem map_normalizer_equiv (H : Subgroup X) :
    (normalizer (H : Set X)).map e.toMonoidHom =
      normalizer ((H.map e.toMonoidHom : Subgroup X') : Set X') :=
  map_equiv_normalizer_eq H e

theorem map_centralizer_equiv (H : Subgroup X) :
    (centralizer (H : Set X)).map e.toMonoidHom =
      centralizer ((H.map e.toMonoidHom : Subgroup X') : Set X') := by
  ext x
  rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hx y hy
    rw [SetLike.mem_coe, mem_map_equiv] at hy
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact hx _ hy
  · intro hx y hy
    have h1 := hx (e y) (by rw [SetLike.mem_coe, mem_map_equiv, MulEquiv.symm_apply_apply]; exact hy)
    have h2 := congrArg e.symm h1
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at h2

theorem map_coreIn_equiv (K H : Subgroup X) :
    (coreIn K H).map e.toMonoidHom = coreIn (K.map e.toMonoidHom) (H.map e.toMonoidHom) := by
  ext x
  rw [mem_map_equiv, mem_coreIn, mem_coreIn, mem_map_equiv]
  refine and_congr_right fun _ => ⟨fun hx h hh => ?_, fun hx h hh => ?_⟩
  · rw [mem_map_equiv] at hh ⊢
    have h1 := hx _ hh
    rwa [map_mul, map_mul, map_inv]
  · have h1 := hx (e h) (by rw [mem_map_equiv, MulEquiv.symm_apply_apply]; exact hh)
    rw [mem_map_equiv, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply] at h1
    exact h1

theorem map_pCoreOf_equiv (p : ℕ) (K : Subgroup X) :
    (pCoreOf p K).map e.toMonoidHom = pCoreOf p (K.map e.toMonoidHom) :=
  NFA6.pCoreOf_map e.injective p K

theorem relIndex_map_equiv (H K : Subgroup X) :
    (H.map e.toMonoidHom).relIndex (K.map e.toMonoidHom) = H.relIndex K :=
  relIndex_map_map_of_injective H K e.injective

theorem card_map_equiv (H : Subgroup X) : Nat.card (H.map e.toMonoidHom) = Nat.card H :=
  card_map_of_injective e.injective

theorem isElemAbelian_map_equiv_iff {p : ℕ} {A : Subgroup X} :
    IsElemAbelian p (A.map e.toMonoidHom) ↔ IsElemAbelian p A :=
  ⟨fun h => by simpa only [map_symm_map] using h.map e.symm.toMonoidHom, fun h => h.map _⟩

theorem normal_map_equiv_iff {K : Subgroup X} : (K.map e.toMonoidHom).Normal ↔ K.Normal :=
  MulEquiv.normal_map_iff

theorem isSimpleGroup_map_equiv {H : Subgroup X} (h : IsSimpleGroup H) :
    IsSimpleGroup (H.map e.toMonoidHom) :=
  (H.equivMapOfInjective _ e.injective).isSimpleGroup_congr.mp h

theorem map_conj_equiv (n : X) (A : Subgroup X) :
    (A.map (MulAut.conj n).toMonoidHom).map e.toMonoidHom =
      (A.map e.toMonoidHom).map (MulAut.conj (e n)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem isSylowIn_map_equiv {p : ℕ} {P H : Subgroup X} (h : IsSylowIn p P H) :
    IsSylowIn p (P.map e.toMonoidHom) (H.map e.toMonoidHom) :=
  NFA6.isSylowIn_of_map e.symm.injective (by rwa [map_symm_map, map_symm_map])

theorem map_nineFrattini_equiv (Z : Subgroup X) :
    (nineFrattini Z).map e.toMonoidHom = nineFrattini (Z.map e.toMonoidHom) := by
  unfold nineFrattini
  rw [← NFW.map_frattini_mulEquiv (Z.equivMapOfInjective _ e.injective), map_map, map_map]
  rfl

theorem irredOnFrattiniQuot_map_equiv {S Z : Subgroup X} (h : IrredOnFrattiniQuot S Z) :
    IrredOnFrattiniQuot (S.map e.toMonoidHom) (Z.map e.toMonoidHom) := by
  refine ⟨?_, fun Y hΦY hYZ hinv => ?_⟩
  · rw [← map_nineFrattini_equiv]
    exact (map_lt_map_iff_of_injective e.injective).mpr h.1
  · obtain ⟨Y, rfl⟩ := exists_eq_map e Y
    rw [← map_nineFrattini_equiv, map_le_map_equiv_iff] at hΦY
    rw [map_le_map_equiv_iff] at hYZ
    have hinv' : ∀ s ∈ S ⊓ normalizer (Z : Set X), ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := by
      intro s hs y hy
      have hs' : e s ∈ S.map e.toMonoidHom ⊓
          normalizer ((Z.map e.toMonoidHom : Subgroup X') : Set X') := by
        rw [← map_normalizer_equiv, ← map_inf_equiv]
        exact mem_map_of_mem _ hs
      have h1 := hinv (e s) hs' (e y) (mem_map_of_mem _ hy)
      rwa [← map_inv, ← map_mul, ← map_mul, mem_map_equiv, MulEquiv.symm_apply_apply] at h1
    rw [← map_nineFrattini_equiv]
    rcases h.2 Y hΦY hYZ hinv' with h1 | h1
    · exact Or.inl (by rw [h1])
    · exact Or.inr (by rw [h1])

theorem twoPTwoIrred_map_equiv {K S Y : Subgroup X} {p : ℕ} (h : TwoPTwoIrred K S Y p) :
    TwoPTwoIrred (K.map e.toMonoidHom) (S.map e.toMonoidHom) (Y.map e.toMonoidHom) p :=
  ⟨NFA6.twoPTwo_of_map (ι := e.symm.toMonoidHom) e.symm.injective
      (by simpa only [map_symm_map] using h.toTwoPTwo),
    irredOnFrattiniQuot_map_equiv e h.irred⟩

theorem twoPTwoIrred_inf_map_equiv {K T Y : Subgroup X} {p : ℕ} (h : TwoPTwoIrred K (K ⊓ T) Y p) :
    TwoPTwoIrred (K.map e.toMonoidHom) (K.map e.toMonoidHom ⊓ T.map e.toMonoidHom)
      (Y.map e.toMonoidHom) p := by
  rw [← map_inf_equiv]
  exact twoPTwoIrred_map_equiv e h

theorem map_core_equiv (T A : Subgroup X) :
    (coreIn (T ⊓ centralizer (A : Set X)) T).map e.toMonoidHom =
      coreIn (T.map e.toMonoidHom ⊓ centralizer ((A.map e.toMonoidHom : Subgroup X') : Set X'))
        (T.map e.toMonoidHom) := by
  rw [map_coreIn_equiv, map_inf_equiv, map_centralizer_equiv]

theorem map_sup_normalizer_equiv (K T : Subgroup X) :
    (K ⊔ (T ⊓ normalizer ((K ⊓ T : Subgroup X) : Set X))).map e.toMonoidHom =
      K.map e.toMonoidHom ⊔ (T.map e.toMonoidHom ⊓
        normalizer ((K.map e.toMonoidHom ⊓ T.map e.toMonoidHom : Subgroup X') : Set X')) := by
  rw [Subgroup.map_sup, map_inf_equiv, map_normalizer_equiv, map_inf_equiv]

theorem nonorm_map_equiv {A K T : Subgroup X}
    (h : ∀ R : Subgroup X, A ≤ R → R ≤ K ⊓ T →
      ¬ K ⊔ (T ⊓ normalizer ((K ⊓ T : Subgroup X) : Set X)) ≤ normalizer (R : Set X)) :
    ∀ R : Subgroup X', A.map e.toMonoidHom ≤ R → R ≤ K.map e.toMonoidHom ⊓ T.map e.toMonoidHom →
      ¬ K.map e.toMonoidHom ⊔ (T.map e.toMonoidHom ⊓ normalizer
        ((K.map e.toMonoidHom ⊓ T.map e.toMonoidHom : Subgroup X') : Set X')) ≤
          normalizer (R : Set X') := by
  intro R hAR hRK hle
  obtain ⟨R, rfl⟩ := exists_eq_map e R
  rw [map_le_map_equiv_iff] at hAR
  rw [← map_inf_equiv, map_le_map_equiv_iff] at hRK
  rw [← map_sup_normalizer_equiv, ← map_normalizer_equiv, map_le_map_equiv_iff] at hle
  exact h R hAR hRK hle

end NGM

open NGM

theorem IsGood915.map_equiv {L1 L2 : Subgroup X} {y : X} (h : IsGood915 L1 L2 y) :
    IsGood915 (L1.map e.toMonoidHom) (L2.map e.toMonoidHom) (e y) :=
  ⟨by rw [MulEquiv.orderOf_eq]; exact h.1,
    h.2.imp (fun h1 => mem_map_of_mem e.toMonoidHom h1) (fun h2 => mem_map_of_mem e.toMonoidHom h2)⟩

theorem IsGood915.swap {L1 L2 : Subgroup X} {y : X} (h : IsGood915 L1 L2 y) :
    IsGood915 L2 L1 y :=
  ⟨h.1, h.2.symm⟩

theorem IsGood915.swap_iff {L1 L2 : Subgroup X} {y : X} : IsGood915 L1 L2 y ↔ IsGood915 L2 L1 y :=
  ⟨IsGood915.swap, IsGood915.swap⟩

theorem NGM.exists_good_map_equiv {L1 L2 K : Subgroup X} (h : ∃ y ∈ K, IsGood915 L1 L2 y) :
    ∃ y ∈ K.map e.toMonoidHom, IsGood915 (L1.map e.toMonoidHom) (L2.map e.toMonoidHom) y := by
  obtain ⟨y, hy, hg⟩ := h
  exact ⟨e y, mem_map_of_mem e.toMonoidHom hy, hg.map_equiv e⟩

theorem FiveWit.map_equiv {L1 L2 T A H R Lh : Subgroup X} (h : FiveWit L1 L2 T A H R Lh) :
    FiveWit (L1.map e.toMonoidHom) (L2.map e.toMonoidHom) (T.map e.toMonoidHom)
      (A.map e.toMonoidHom) (H.map e.toMonoidHom) (R.map e.toMonoidHom)
      (Lh.map e.toMonoidHom) where
  le := map_mono h.le
  R_le := map_mono h.R_le
  R_norm := by rw [← map_normalizer_equiv]; exact map_mono h.R_norm
  R_le_T := map_mono h.R_le_T
  idx := by rw [relIndex_map_equiv]; exact h.idx
  core := by rw [← map_core_equiv]; exact map_mono h.core
  Lh_le := map_mono h.Lh_le
  Lh_norm := by rw [← map_normalizer_equiv]; exact map_mono h.Lh_norm
  simple := isSimpleGroup_map_equiv e h.simple
  inter := by rw [← map_inf_equiv, h.inter, Subgroup.map_bot]
  cent := by rw [← map_centralizer_equiv, ← map_inf_equiv]; exact map_mono h.cent
  good := exists_good_map_equiv e h.good
  pair := by
    obtain ⟨n, hn, hp, a, ha, b, hb, hab⟩ := h.pair
    refine ⟨e n, mem_map_of_mem e.toMonoidHom hn, ?_, e a, mem_map_of_mem e.toMonoidHom ha,
      e b, mem_map_of_mem e.toMonoidHom hb, ?_⟩
    · rw [← map_conj_equiv, ← Subgroup.map_sup]
      exact hp.map _
    · intro h'
      apply hab
      apply e.injective
      simpa only [map_mul, map_inv] using h'

theorem FiveWit.swap {L1 L2 T A H R Lh : Subgroup X} (h : FiveWit L1 L2 T A H R Lh) :
    FiveWit L2 L1 T A H R Lh :=
  { h with good := h.good.imp fun _ hy => ⟨hy.1, hy.2.swap⟩ }

theorem FiveWit.swap_iff {L1 L2 T A H R Lh : Subgroup X} :
    FiveWit L1 L2 T A H R Lh ↔ FiveWit L2 L1 T A H R Lh :=
  ⟨FiveWit.swap, FiveWit.swap⟩

theorem SevenWit.map_equiv {L1 L2 T A K Y : Subgroup X} (h : SevenWit L1 L2 T A K Y) :
    SevenWit (L1.map e.toMonoidHom) (L2.map e.toMonoidHom) (T.map e.toMonoidHom)
      (A.map e.toMonoidHom) (K.map e.toMonoidHom) (Y.map e.toMonoidHom) where
  le := map_mono h.le
  irr := twoPTwoIrred_inf_map_equiv e h.irr
  core := by rw [← map_core_equiv]; exact map_mono h.core
  nonorm := nonorm_map_equiv e h.nonorm
  good := exists_good_map_equiv e h.good

theorem SevenWit.swap {L1 L2 T A K Y : Subgroup X} (h : SevenWit L1 L2 T A K Y) :
    SevenWit L2 L1 T A K Y :=
  { h with good := h.good.imp fun _ hy => ⟨hy.1, hy.2.swap⟩ }

theorem SevenWit.swap_iff {L1 L2 T A K Y : Subgroup X} :
    SevenWit L1 L2 T A K Y ↔ SevenWit L2 L1 T A K Y :=
  ⟨SevenWit.swap, SevenWit.swap⟩

theorem Kill761.map_equiv {U K : Subgroup X} (h : Kill761 U K) :
    Kill761 (U.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  obtain ⟨R, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨R.map e.toMonoidHom, ?_, map_mono h2, ?_, ?_, ?_, ?_⟩
  · rw [← map_pCoreOf_equiv]
    exact map_mono h1
  · rw [← map_normalizer_equiv]
    exact map_mono h3
  · rw [← map_pCoreOf_equiv, relIndex_map_equiv]
    exact h4
  · rintro _ ⟨a, ha, rfl⟩ hax
    rw [← map_pCoreOf_equiv]
    refine mem_map_of_mem _ (h5 a ha fun x hx => ?_)
    have h7 := hax (e x) (mem_map_of_mem e.toMonoidHom hx)
    rw [← map_pCoreOf_equiv, MulEquiv.coe_toMonoidHom, ← map_commutatorElement, mem_map_equiv,
      MulEquiv.symm_apply_apply] at h7
    exact h7
  · rw [← map_pCoreOf_equiv, relIndex_map_equiv]
    exact h6

theorem Kill763.map_equiv {U K : Subgroup X} (h : Kill763 U K) :
    Kill763 (U.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  obtain ⟨h0, Y, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨?_, Y.map e.toMonoidHom, ?_, map_mono h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pCoreOf_equiv, relIndex_map_equiv]
    exact h0
  · rw [← map_pCoreOf_equiv]
    exact map_mono h1
  · rw [← map_normalizer_equiv]
    exact map_mono h3
  · rw [← map_pCoreOf_equiv, ← map_commutator, ← Subgroup.map_sup]
    exact map_mono h4
  · rintro _ ⟨a, ha, rfl⟩ hay
    rw [← map_pCoreOf_equiv]
    refine mem_map_of_mem _ (h5 a ha fun y hy => ?_)
    have h9 := hay (e y) (mem_map_of_mem e.toMonoidHom hy)
    rw [← map_pCoreOf_equiv, MulEquiv.coe_toMonoidHom, ← map_commutatorElement, mem_map_equiv,
      MulEquiv.symm_apply_apply] at h9
    exact h9
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_pCoreOf_equiv, ← map_pow]
    exact mem_map_of_mem _ (h6 y hy)
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_pCoreOf_equiv, ← map_commutatorElement]
    exact mem_map_of_mem _ (h7 y hy z hz)
  · rw [← map_pCoreOf_equiv, relIndex_map_equiv]
    exact h8

theorem KillWit.map_equiv {L1 L2 T U K Y : Subgroup X} (h : KillWit L1 L2 T U K Y) :
    KillWit (L1.map e.toMonoidHom) (L2.map e.toMonoidHom) (T.map e.toMonoidHom)
      (U.map e.toMonoidHom) (K.map e.toMonoidHom) (Y.map e.toMonoidHom) where
  le := map_mono h.le
  irr := twoPTwoIrred_inf_map_equiv e h.irr
  nonorm := nonorm_map_equiv e h.nonorm
  good := exists_good_map_equiv e h.good
  kill := by
    rcases h.kill with h1 | h1 | h1
    · left
      rw [← map_pCoreOf_equiv]
      exact map_mono h1
    · exact Or.inr (Or.inl (h1.map_equiv e))
    · exact Or.inr (Or.inr (h1.map_equiv e))

theorem KillWit.swap {L1 L2 T U K Y : Subgroup X} (h : KillWit L1 L2 T U K Y) :
    KillWit L2 L1 T U K Y :=
  { h with good := h.good.imp fun _ hy => ⟨hy.1, hy.2.swap⟩ }

theorem KillWit.swap_iff {L1 L2 T U K Y : Subgroup X} :
    KillWit L1 L2 T U K Y ↔ KillWit L2 L1 T U K Y :=
  ⟨KillWit.swap, KillWit.swap⟩

theorem NGM.table_map_equiv {L1 L2 T A : Subgroup X}
    (h : (∃ H R Lh : Subgroup X, FiveWit L1 L2 T A H R Lh) ∨
      ∃ K Y : Subgroup X, SevenWit L1 L2 T A K Y) :
    (∃ H R Lh : Subgroup X', FiveWit (L1.map e.toMonoidHom) (L2.map e.toMonoidHom)
        (T.map e.toMonoidHom) (A.map e.toMonoidHom) H R Lh) ∨
      ∃ K Y : Subgroup X', SevenWit (L1.map e.toMonoidHom) (L2.map e.toMonoidHom)
        (T.map e.toMonoidHom) (A.map e.toMonoidHom) K Y := by
  rcases h with ⟨H, R, Lh, hw⟩ | ⟨K, Y, hw⟩
  · exact Or.inl ⟨_, _, _, hw.map_equiv e⟩
  · exact Or.inr ⟨_, _, hw.map_equiv e⟩

theorem NGM.close_map_equiv {L1 L2 T U : Subgroup X}
    (h : (∃ H R Lh : Subgroup X, FiveWit L1 L2 T U H R Lh) ∨
      ∃ K Y : Subgroup X, KillWit L1 L2 T U K Y) :
    (∃ H R Lh : Subgroup X', FiveWit (L1.map e.toMonoidHom) (L2.map e.toMonoidHom)
        (T.map e.toMonoidHom) (U.map e.toMonoidHom) H R Lh) ∨
      ∃ K Y : Subgroup X', KillWit (L1.map e.toMonoidHom) (L2.map e.toMonoidHom)
        (T.map e.toMonoidHom) (U.map e.toMonoidHom) K Y := by
  rcases h with ⟨H, R, Lh, hw⟩ | ⟨K, Y, hw⟩
  · exact Or.inl ⟨_, _, _, hw.map_equiv e⟩
  · exact Or.inr ⟨_, _, hw.map_equiv e⟩

include e in
theorem NGM.pair_map_equiv
    (h : ∀ x : X, orderOf x = 2 → ∃ n : X,
      IsPGroup 2 (closure {x, n * x * n⁻¹}) ∧ x * (n * x * n⁻¹) ≠ (n * x * n⁻¹) * x) :
    ∀ x : X', orderOf x = 2 → ∃ n : X',
      IsPGroup 2 (closure {x, n * x * n⁻¹}) ∧ x * (n * x * n⁻¹) ≠ (n * x * n⁻¹) * x := by
  intro x' hx
  obtain ⟨x, rfl⟩ := e.surjective x'
  rw [MulEquiv.orderOf_eq] at hx
  obtain ⟨n, hp, hne⟩ := h x hx
  refine ⟨e n, ?_, ?_⟩
  · have h1 : closure {e x, e n * e x * (e n)⁻¹} =
        (closure {x, n * x * n⁻¹}).map e.toMonoidHom := by
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
      simp
    rw [h1]
    exact hp.map _
  · intro h'
    apply hne
    apply e.injective
    simpa only [map_mul, map_inv] using h'

theorem NineFifteenBarFacts.map_equiv [Finite X] [Finite X'] {L1 L2 T : Subgroup X}
    (h : NineFifteenBarFacts X L1 L2 T) :
    NineFifteenBarFacts X' (L1.map e.toMonoidHom) (L2.map e.toMonoidHom) (T.map e.toMonoidHom)
    where
  le_of_normal := by
    intro K hK ⟨x, hxK, hx2⟩
    obtain ⟨K, rfl⟩ := exists_eq_map e K
    rw [← Subgroup.map_sup, map_le_map_equiv_iff]
    refine h.le_of_normal K ((normal_map_equiv_iff e).mp hK) ⟨e.symm x, ?_, ?_⟩
    · rwa [← mem_map_equiv]
    · rwa [MulEquiv.orderOf_eq]
  cent := by rw [← Subgroup.map_sup, ← map_centralizer_equiv, h.cent, Subgroup.map_bot]
  three := by
    obtain ⟨y, hy, hy3⟩ := h.three
    exact ⟨e y, mem_map_of_mem e.toMonoidHom hy, by rw [MulEquiv.orderOf_eq]; exact hy3⟩
  pair := pair_map_equiv e h.pair
  table := by
    intro A hAT hAe hA4
    obtain ⟨A, rfl⟩ := exists_eq_map e A
    rw [map_le_map_equiv_iff] at hAT
    rw [isElemAbelian_map_equiv_iff] at hAe
    rw [card_map_equiv] at hA4
    exact table_map_equiv e (h.table A hAT hAe hA4)
  close := by
    intro U E hUE hET hTE hEe hU4
    obtain ⟨U, rfl⟩ := exists_eq_map e U
    obtain ⟨E, rfl⟩ := exists_eq_map e E
    rw [map_le_map_equiv_iff] at hUE hET
    rw [← map_normalizer_equiv, map_le_map_equiv_iff] at hTE
    rw [isElemAbelian_map_equiv_iff] at hEe
    rw [card_map_equiv] at hU4
    exact close_map_equiv e (h.close U E hUE hET hTE hEe hU4)

theorem NineFifteenBarFacts.of_map_equiv [Finite X] [Finite X'] {L1 L2 T : Subgroup X}
    (h : NineFifteenBarFacts X' (L1.map e.toMonoidHom) (L2.map e.toMonoidHom)
      (T.map e.toMonoidHom)) :
    NineFifteenBarFacts X L1 L2 T := by
  simpa only [map_symm_map] using h.map_equiv e.symm

end CFSG.LocalAnalysis.WeakClosure81
