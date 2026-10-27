module

public import CFSG.Quasithin.H13.U4ParAmalgam
public import CFSG.Quasithin.H13.U4ParLine
public import CFSG.Quasithin.H13.U4ParCore
public import CFSG.Quasithin.H13.U4ParModel
public import CFSG.Quasithin.Background.F1Lemma10
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherMaximalParabolics
import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherBorelOvergroups

public section

namespace CFSG.Quasithin.H13.U4Par

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

section Transport

variable {G Y : Type} [Group G] [Group Y] {ψ : G →* Y}

theorem pCoreOf_map_of_inj (hψ : Function.Injective ψ) (p : ℕ) (X : Subgroup G) :
    pCoreOf p (X.map ψ) = (pCoreOf p X).map ψ := by
  let e : ↥X ≃* ↥(X.map ψ) := X.equivMapOfInjective ψ hψ
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem centerOf_map_of_inj (hψ : Function.Injective ψ) (X : Subgroup G) :
    centerOf (X.map ψ) = (centerOf X).map ψ := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, Subgroup.mem_centralizer_iff.mpr fun x' hx' => hψ ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc (ψ x') (Subgroup.mem_map_of_mem ψ hx')
    rw [← map_mul, ← map_mul] at this
    exact this
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem ψ hx, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨x', hx', rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc x' hx']

theorem comm_map_iff (hψ : Function.Injective ψ) (X : Subgroup G) :
    (∀ a ∈ X.map ψ, ∀ b ∈ X.map ψ, a * b = b * a) ↔ (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) := by
  constructor
  · intro hc a ha b hb
    apply hψ
    rw [map_mul, map_mul]
    exact hc _ (Subgroup.mem_map_of_mem ψ ha) _ (Subgroup.mem_map_of_mem ψ hb)
  · rintro hc _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]

theorem isMaxIn_map_iff (hψ : Function.Injective ψ) (A : Subgroup G) :
    IsMaxIn (A.map ψ) ψ.range ↔ IsCoatom A := by
  have hr : ψ.range = (⊤ : Subgroup G).map ψ := MonoidHom.range_eq_map ψ
  constructor
  · rintro ⟨hlt, hmax⟩
    refine ⟨fun htop => hlt.ne (by rw [htop, hr]), fun B hAB => ?_⟩
    rcases hmax (B.map ψ) (Subgroup.map_mono hAB.le) (Subgroup.map_le_range ψ B) with e | e
    · exact absurd (Subgroup.map_injective hψ e) hAB.ne'
    · rw [hr] at e
      exact Subgroup.map_injective hψ e
  · rintro ⟨hne, hmax⟩
    refine ⟨lt_of_le_of_ne (Subgroup.map_le_range ψ A) fun e => hne ?_, fun A' hA hA' => ?_⟩
    · rw [hr] at e
      exact Subgroup.map_injective hψ e
    · have hA'eq : (A'.comap ψ).map ψ = A' := Subgroup.map_comap_eq_self hA'
      have hle : A ≤ A'.comap ψ := Subgroup.map_le_iff_le_comap.mp hA
      rcases hle.lt_or_eq with hlt | heq
      · right
        rw [← hA'eq, hmax _ hlt, ← hr]
      · left
        rw [← hA'eq, ← heq]

theorem inf_normalizer_map (hψ : Function.Injective ψ) (U : Subgroup G) :
    ψ.range ⊓ Subgroup.normalizer ((U.map ψ : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (U : Set G)).map ψ := by
  ext y
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨g, rfl⟩, hy⟩
    refine ⟨g, ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro u
    have e : ψ g * ψ u * (ψ g)⁻¹ = ψ (g * u * g⁻¹) := by simp [map_mul, map_inv]
    have := hy (ψ u)
    rw [e, Subgroup.mem_map_iff_mem hψ, Subgroup.mem_map_iff_mem hψ] at this
    exact this
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, ?_⟩
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨g * u * g⁻¹, (hg u).mp hu, by simp [map_mul, map_inv]⟩
    · rintro ⟨u, hu, hu'⟩
      refine ⟨g⁻¹ * u * g, ?_, ?_⟩
      · rw [SetLike.mem_coe, hg]
        simpa [mul_assoc] using hu
      · rw [map_mul, map_mul, map_inv, hu']
        group

end Transport

theorem normal_of_index_le_two {Y : Type} [Group Y] [Finite Y] {H : Subgroup Y}
    (hidx : H.index ≤ 2) : H.Normal := by
  have hpos : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : H.index = 1 ∨ H.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one.mp h1]
    infer_instance
  · exact Subgroup.normal_of_index_eq_two h2

theorem false_of_isSpecialPow_of_comm {Y : Type} [Group Y] {Q : Subgroup Y} {q : ℕ} (hq : 2 ≤ q)
    (hc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hs : IsSpecialPow 2 q 2 ↥Q) : False := by
  obtain ⟨-, hcard, hz⟩ := hs
  have htop : Subgroup.center ↥Q = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc _ y.2 _ x.2)
  rw [htop, Subgroup.card_top, hcard] at hz
  have h5 : q < q ^ (1 + 2 * 2) :=
    calc q = q ^ 1 := (pow_one q).symm
      _ < q ^ (1 + 2 * 2) := Nat.pow_lt_pow_right (by omega) (by norm_num)
  rw [hz] at h5
  exact lt_irrefl _ h5

section Model

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem isSimpleGroup_hypSU : IsSimpleGroup (hypSU h 2 0) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_hypSU_equiv_statedProj h
  have hK : Nat.card K = (2 ^ m) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  rw [e.isSimpleGroup_congr]
  exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 m hK 4
    (by norm_num) fun hq => absurd (Prod.mk.inj hq).1 (by norm_num)

theorem zRad_ne_bot : zRad h ≠ ⊥ := by
  intro e
  have hc := card_zRad h
  rw [e, Subgroup.card_bot] at hc
  have h1 : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h.one_le
  omega

theorem exists_radQ_ne_comm : ∃ a ∈ radQ h, ∃ b ∈ radQ h, a * b ≠ b * a := by
  by_contra hcon
  have hc : ∀ a ∈ radQ h, ∀ b ∈ radQ h, a * b = b * a := fun a ha b hb =>
    by_contra fun hne => hcon ⟨a, ha, b, hb, hne⟩
  apply zRad_ne_bot h
  rw [← commutator_radQ h, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact hc b hb a ha

theorem not_isPGroup_hypSU : ¬ IsPGroup 2 (hypSU h 2 0) := by
  intro hp
  have := finite_hypSU h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, -, b, -, hab⟩ := exists_radQ_ne_comm h
  have : Nontrivial (hypSU h 2 0) := ⟨⟨a * b, b * a, hab⟩⟩
  have hc := hp.center_nontrivial
  have := isSimpleGroup_hypSU h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (hypSU h 2 0)) with h0 | h0
  · rw [h0] at hc
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hc rfl
  · have ha : a ∈ Subgroup.center (hypSU h 2 0) := h0 ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem isCoatom_parP : IsCoatom (parP h) :=
  ⟨UnitaryHigher.isoStabilizer_hypFlag_ne_top h (by norm_num) le_rfl (by norm_num),
    fun A hA => (UnitaryHigher.eq_of_isoStabilizer_hypFlag_le h (by norm_num) (by norm_num) le_rfl
      (by norm_num) A hA.le).resolve_left hA.ne'⟩

theorem isCoatom_parP2 : IsCoatom (parP2 h) :=
  ⟨UnitaryHigher.isoStabilizer_hypFlag_ne_top h (by norm_num) (by norm_num) le_rfl,
    fun A hA => (UnitaryHigher.eq_of_isoStabilizer_hypFlag_le h (by norm_num) (by norm_num)
      (by norm_num) le_rfl A hA.le).resolve_left hA.ne'⟩

theorem parP_ne_parP2 : parP h ≠ parP2 h := by
  intro e
  have hmem : levHom h (slL h) ∈ parP2 h := e ▸ levHom_le_parP h ⟨slL h, rfl⟩
  have := ((mem_parP2_iff h _).mp hmem).2.2.2
  rw [coe_levHom, levMat_apply] at this
  simp [slMat, slL] at this

theorem eq_parP_or_eq_parP2 {A : Subgroup (hypSU h 2 0)} (hA : IsCoatom A)
    (hBA : hypBorel h 2 0 ≤ A) : A = parP h ∨ A = parP2 h := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  obtain ⟨hI, hAI, -, -⟩ :=
    UnitaryHigher.unitary_Borel_overgroups h (by norm_num) (by norm_num) hc hc0 A hBA
  have hle : ∀ d ∈ UnitaryHigher.overgroupCuts 0 h c hc A,
      A ≤ UnitaryHigher.isoStabilizer h 2 0 (hypFlag h 2 0 d) := by
    intro d hd g hg
    rw [hAI] at hg
    exact UnitaryHigher.mem_isoStabilizer.mpr (UnitaryHigher.mem_flagStabilizer.mp hg d hd)
  by_cases h1 : 1 ∈ UnitaryHigher.overgroupCuts 0 h c hc A
  · left
    exact (((hA.le_iff.mp (hle 1 h1)).resolve_left (isCoatom_parP h).1)).symm
  · by_cases h2 : 2 ∈ UnitaryHigher.overgroupCuts 0 h c hc A
    · right
      exact (((hA.le_iff.mp (hle 2 h2)).resolve_left (isCoatom_parP2 h).1)).symm
    · exfalso
      have hI0 : UnitaryHigher.overgroupCuts 0 h c hc A = ∅ := by
        ext i
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hi
        obtain ⟨hi1, hi2⟩ := hI hi
        interval_cases i
        · exact h1 hi
        · exact h2 hi
      apply hA.1
      rw [hAI, hI0, UnitaryHigher.flagStabilizer_empty]

theorem zRad_le_radQ2 : zRad h ≤ radQ2 h := by
  rintro g ⟨c, -, hg⟩
  change IsQ2Mat _
  rw [hg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [sMat_apply]

theorem radQ2_isPGroup : IsPGroup 2 (radQ2 h) := by
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  apply hypSU_ext
  have := h.charP
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := g.2
  change ((((g : hypSU h 2 0) ^ 2 : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = 1
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, sq]
  ext i j
  rw [Matrix.mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, CharTwo.add_self_eq_zero]

theorem radQ_le_pCoreOf_parP : radQ h ≤ pCoreOf 2 (parP h) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (radQ_le_parP h)
    (parP_le_normalizer_radQ h) (radQ_isPGroup h)

theorem radQ2_le_pCoreOf_parP2 : radQ2 h ≤ pCoreOf 2 (parP2 h) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (radQ2_le_parP2 h)
    (parP2_le_normalizer_radQ2 h) (radQ2_isPGroup h)

theorem pCoreOf_parP_ne_bot : pCoreOf 2 (parP h) ≠ ⊥ := fun e =>
  zRad_ne_bot h (eq_bot_iff.mpr ((zRad_le_radQ h).trans ((radQ_le_pCoreOf_parP h).trans e.le)))

theorem pCoreOf_parP2_ne_bot : pCoreOf 2 (parP2 h) ≠ ⊥ := fun e =>
  zRad_ne_bot h (eq_bot_iff.mpr ((zRad_le_radQ2 h).trans ((radQ2_le_pCoreOf_parP2 h).trans e.le)))

end Model

section Recog

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K) {Y : Type} [Group Y]

theorem exists_conj_eq_sylow [Finite Y] {T : Subgroup Y} (hT : IsSylowTwoOf T ⊤)
    {ψ : hypSU h 2 0 →* Y} (hψ : Function.Injective ψ) (hn : ψ.range.Normal) :
    ∃ ψ' : hypSU h 2 0 →* Y, Function.Injective ψ' ∧ ψ'.range = ψ.range ∧
      (hypUnitriangular h 2 0).map ψ' = T ⊓ ψ.range := by
  have := h.finite
  have := finite_hypSU h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨PU, hPU⟩ := (unitary_order_and_Sylow (r := 2) (ε := 0) h (by norm_num) (by norm_num)).2.1
  have hTidx : ¬ 2 ∣ T.index := by
    have e : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    rw [← e]
    exact hT.2.2
  obtain ⟨T', hT'⟩ := (PU.2.map ψ).exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y T' (hT.2.1.toSylow hTidx)
  have hconjT : ∀ x ∈ (T' : Subgroup Y), y * x * y⁻¹ ∈ T := by
    intro x hx
    have h1 := Subgroup.smul_mem_pointwise_smul x (MulAut.conj y) (T' : Subgroup Y) hx
    rw [← Sylow.coe_subgroup_smul, hy] at h1
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  refine ⟨(MulAut.conj y).toMonoidHom.comp ψ, (MulAut.conj y).injective.comp hψ, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨g, rfl⟩
      exact hn.conj_mem _ ⟨g, rfl⟩ y
    · intro hz
      obtain ⟨g, hg⟩ := hn.conj_mem z hz y⁻¹
      refine ⟨g, ?_⟩
      change y * ψ g * y⁻¹ = z
      rw [hg]
      group
  · set ψ' := (MulAut.conj y).toMonoidHom.comp ψ with hψ'def
    have hψ' : Function.Injective ψ' := (MulAut.conj y).injective.comp hψ
    have hrange : ψ'.range = ψ.range := by
      ext z
      constructor
      · rintro ⟨g, rfl⟩
        exact hn.conj_mem _ ⟨g, rfl⟩ y
      · intro hz
        obtain ⟨g, hg⟩ := hn.conj_mem z hz y⁻¹
        refine ⟨g, ?_⟩
        change y * ψ g * y⁻¹ = z
        rw [hg]
        group
    have hle : (hypUnitriangular h 2 0).map ψ' ≤ T ⊓ ψ.range := by
      rintro _ ⟨u, hu, rfl⟩
      refine ⟨hconjT _ (hT' ⟨u, by rw [hPU]; exact hu, rfl⟩), ?_⟩
      rw [← hrange]
      exact ⟨u, rfl⟩
    have hS : IsPGroup 2 ((T ⊓ ψ.range).comap ψ') :=
      (hT.2.1.to_le inf_le_left).comap_of_injective ψ' hψ'
    have hUS : (PU : Subgroup (hypSU h 2 0)) ≤ (T ⊓ ψ.range).comap ψ' := by
      rw [hPU]
      exact Subgroup.map_le_iff_le_comap.mp hle
    have heq := PU.is_maximal' hS hUS
    have hTR : T ⊓ ψ.range ≤ ψ'.range := hrange ▸ inf_le_right
    rw [← hPU]
    change Subgroup.map ψ' PU.toSubgroup = T ⊓ ψ.range
    rw [← heq, Subgroup.map_comap_eq_self hTR]

theorem recog_aux [Finite Y] (hm : 2 ≤ m) (ψ : hypSU h 2 0 →* Y) (hψ : Function.Injective ψ)
    (hidx : ψ.range.index ≤ 2) {T M₁ M : Subgroup Y} (hpair : IsYAmalgamPair T M₁ M)
    (hU : (hypUnitriangular h 2 0).map ψ = T ⊓ ψ.range)
    (hsp : IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (perfectCore M))) :
    M = Subgroup.normalizer (((parP h).map ψ : Subgroup Y) : Set Y) ∧
      M ⊓ ψ.range = (parP h).map ψ ∧
      perfectCore M = (perfectCore (parP h)).map ψ ∧
      pCoreOf 2 (perfectCore M) = (radQ h).map ψ := by
  have := h.finite
  have := finite_hypSU h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : ψ.range.Normal := normal_of_index_le_two hidx
  have hB : ψ.range ⊓ Subgroup.normalizer ((T ⊓ ψ.range : Subgroup Y) : Set Y) =
      (hypBorel h 2 0).map ψ := by
    rw [← hU, inf_normalizer_map hψ,
      UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)]
  have hsimple : ∀ N : Subgroup Y, N ≤ ψ.range → ψ.range ≤ Subgroup.normalizer (N : Set Y) →
      N = ⊥ ∨ N = ψ.range := by
    intro N hN hnN
    have := isSimpleGroup_hypSU h
    have hNn : (N.comap ψ).Normal := ⟨fun n hn g => by
      have := (Subgroup.mem_normalizer_iff.mp (hnN ⟨g, rfl⟩) (ψ n)).mp hn
      simpa [Subgroup.mem_comap, map_mul, map_inv] using this⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap ψ) with h0 | h0
    · left
      rw [← Subgroup.map_comap_eq_self hN, h0, Subgroup.map_bot]
    · right
      rw [← Subgroup.map_comap_eq_self hN, h0, ← MonoidHom.range_eq_map]
  have hnot2 : ¬ IsPGroup 2 ψ.range := fun hp =>
    not_isPGroup_hypSU h (hp.of_injective ψ.rangeRestrict
      (MonoidHom.rangeRestrict_injective_iff.mpr hψ))
  let P : Fin 2 → Subgroup Y := ![(parP h).map ψ, (parP2 h).map ψ]
  have hP0 : P 0 = (parP h).map ψ := rfl
  have hP1 : P 1 = (parP2 h).map ψ := rfl
  have hBP : ∀ i, ψ.range ⊓ Subgroup.normalizer ((T ⊓ ψ.range : Subgroup Y) : Set Y) ≤ P i := by
    intro i
    rw [hB]
    fin_cases i
    · exact Subgroup.map_mono (UnitaryHigher.hypBorel_le_isoStabilizer h le_rfl (by norm_num))
    · exact Subgroup.map_mono (UnitaryHigher.hypBorel_le_isoStabilizer h (by norm_num) le_rfl)
  have hPmax : ∀ i, IsMaxIn (P i) ψ.range := by
    intro i
    fin_cases i
    · exact (isMaxIn_map_iff hψ _).mpr (isCoatom_parP h)
    · exact (isMaxIn_map_iff hψ _).mpr (isCoatom_parP2 h)
  have hPuniq : ∀ A : Subgroup Y, IsMaxIn A ψ.range →
      ψ.range ⊓ Subgroup.normalizer ((T ⊓ ψ.range : Subgroup Y) : Set Y) ≤ A → ∃ i, A = P i := by
    intro A hA hBA
    rw [hB] at hBA
    have hA' : A = (A.comap ψ).map ψ := (Subgroup.map_comap_eq_self hA.1.le).symm
    have hco : IsCoatom (A.comap ψ) := (isMaxIn_map_iff hψ _).mp (hA' ▸ hA)
    have hBA' : hypBorel h 2 0 ≤ A.comap ψ := Subgroup.map_le_iff_le_comap.mp hBA
    rcases eq_parP_or_eq_parP2 h hco hBA' with e | e
    · refine ⟨0, ?_⟩
      rw [hP0, hA', e]
    · refine ⟨1, ?_⟩
      rw [hP1, hA', e]
  have hne : P 0 ≠ P 1 := by
    rw [hP0, hP1]
    intro e
    exact parP_ne_parP2 h (Subgroup.map_injective hψ e)
  have hO : ∀ i, pCoreOf 2 (P i) ≠ ⊥ := by
    intro i
    fin_cases i
    · change pCoreOf 2 ((parP h).map ψ) ≠ ⊥
      rw [pCoreOf_map_of_inj hψ, Ne, Subgroup.map_eq_bot_iff_of_injective _ hψ]
      exact pCoreOf_parP_ne_bot h
    · change pCoreOf 2 ((parP2 h).map ψ) ≠ ⊥
      rw [pCoreOf_map_of_inj hψ, Ne, Subgroup.map_eq_bot_iff_of_injective _ hψ]
      exact pCoreOf_parP2_ne_bot h
  have hcore0 : pCoreOf 2 (perfectCore (P 0)) = (radQ h).map ψ := by
    rw [hP0, ← map_perfectCore, pCoreOf_map_of_inj hψ, pCoreOf_perfectCore_parP h hm]
  have hcore1 : ∀ a ∈ pCoreOf 2 (perfectCore (P 1)), ∀ b ∈ pCoreOf 2 (perfectCore (P 1)),
      a * b = b * a := by
    rw [hP1, ← map_perfectCore, pCoreOf_map_of_inj hψ, comm_map_iff hψ]
    exact fun a ha b hb => pCoreOf_perfectCore_parP2_comm h ha hb
  have hswap : ∀ x : Y, (P 0).map (MulAut.conj x).toMonoidHom ≠ P 1 := by
    intro x e
    have hinj : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
    have hc := hcore1
    rw [← e, ← map_perfectCore, pCoreOf_map_of_inj hinj, hcore0, comm_map_iff hinj,
      comm_map_iff hψ] at hc
    obtain ⟨a, ha, b, hb, hab⟩ := exists_radQ_ne_comm h
    exact hab (hc a ha b hb)
  obtain ⟨i, hMi, hMY, hcoreM⟩ := eq_normalizer_of_isYAmalgamPair hidx hsimple hnot2 hpair P hBP
    hPmax hPuniq hne hO hswap
  fin_cases i
  · change M = Subgroup.normalizer (((P 0 : Subgroup Y)) : Set Y) at hMi
    change M ⊓ ψ.range = P 0 at hMY
    change perfectCore M = perfectCore (P 0) at hcoreM
    refine ⟨hMi, hMY, ?_, ?_⟩
    · rw [hcoreM, hP0, map_perfectCore]
    · rw [hcoreM, hcore0]
  · exfalso
    change perfectCore M = perfectCore (P 1) at hcoreM
    have hq : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h.one_le
    rw [hcoreM] at hsp
    exact false_of_isSpecialPow_of_comm hq hcore1 hsp

theorem recog [Finite Y] (hm : 2 ≤ m) (ψ : hypSU h 2 0 →* Y) (hψ : Function.Injective ψ)
    (hidx : ψ.range.index ≤ 2) {T M₁ M : Subgroup Y} (hpair : IsYAmalgamPair T M₁ M)
    (hsp : IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (perfectCore M))) :
    ∃ ψ' : hypSU h 2 0 →* Y, Function.Injective ψ' ∧ ψ'.range = ψ.range ∧
      M = Subgroup.normalizer (((parP h).map ψ' : Subgroup Y) : Set Y) ∧
      M ⊓ ψ.range = (parP h).map ψ' ∧
      perfectCore M = (perfectCore (parP h)).map ψ' ∧
      pCoreOf 2 (perfectCore M) = (radQ h).map ψ' := by
  obtain ⟨ψ', hψ', hrange, hU⟩ :=
    exists_conj_eq_sylow h hpair.1 hψ (normal_of_index_le_two hidx)
  rw [← hrange] at hidx hU ⊢
  exact ⟨ψ', hψ', rfl, recog_aux h hm ψ' hψ' hidx hpair hU hsp⟩

end Recog

theorem exists_embedding {Y : Type} [Group Y] {m : ℕ}
    (hY : CFSG.Blueprint.LieModel Y .PSU 4 2 m ∨
      ∃ (Y₀ : Type) (_ : Group Y₀) (ι : Y₀ →* Y), CFSG.Blueprint.LieModel Y₀ .PSU 4 2 m ∧
        Function.Injective ι ∧ ι.range.index = 2) :
    Finite Y ∧ ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 m K)
      (ψ : hypSU h 2 0 →* Y), Function.Injective ψ ∧ ψ.range.index ≤ 2 := by
  rcases hY with hY | ⟨Y₀, _, ι, hY₀, hι, hidx⟩
  · obtain ⟨K, _, h, ⟨e⟩⟩ := exists_hypSU_equiv_of_lieModel hY
    have := h.finite
    have := finite_hypSU h
    refine ⟨Finite.of_equiv _ e.toEquiv, K, inferInstance, h, e.toMonoidHom, e.injective, ?_⟩
    rw [MonoidHom.range_eq_top.mpr e.surjective, Subgroup.index_top]
    norm_num
  · obtain ⟨K, _, h, ⟨e⟩⟩ := exists_hypSU_equiv_of_lieModel hY₀
    have := h.finite
    have := finite_hypSU h
    have : Finite Y₀ := Finite.of_equiv _ e.toEquiv
    have hrange : (ι.comp e.toMonoidHom).range = ι.range := by
      ext z
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨e g, rfl⟩
      · rintro ⟨y₀, rfl⟩
        exact ⟨e.symm y₀, by simp⟩
    have hYfin : Finite Y := by
      have h1 := Subgroup.card_mul_index ι.range
      have : Finite ι.range := Finite.of_surjective _ ι.rangeRestrict_surjective
      have h2 : Nat.card ι.range ≠ 0 := Nat.card_pos.ne'
      apply Nat.finite_of_card_ne_zero
      rw [← h1, hidx]
      exact mul_ne_zero h2 (by norm_num)
    refine ⟨hYfin, K, inferInstance, h, ι.comp e.toMonoidHom, hι.comp e.injective, ?_⟩
    rw [hrange, hidx]

theorem recog_of {Y : Type} [Group Y] {m : ℕ} (hm : 2 ≤ m) {T M₁ M : Subgroup Y}
    (hY : CFSG.Blueprint.LieModel Y .PSU 4 2 m ∨
      ∃ (Y₀ : Type) (_ : Group Y₀) (ι : Y₀ →* Y), CFSG.Blueprint.LieModel Y₀ .PSU 4 2 m ∧
        Function.Injective ι ∧ ι.range.index = 2)
    (hpair : IsYAmalgamPair T M₁ M)
    (hsp : IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (perfectCore M))) :
    Finite Y ∧ ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 m K)
      (ψ : hypSU h 2 0 →* Y), Function.Injective ψ ∧ ψ.range.index ≤ 2 ∧
        M = Subgroup.normalizer (((parP h).map ψ : Subgroup Y) : Set Y) ∧
        M ⊓ ψ.range = (parP h).map ψ ∧
        perfectCore M = (perfectCore (parP h)).map ψ ∧
        pCoreOf 2 (perfectCore M) = (radQ h).map ψ := by
  obtain ⟨hfin, K, _, h, ψ, hψ, hidx⟩ := exists_embedding hY
  refine ⟨hfin, K, inferInstance, h, ?_⟩
  obtain ⟨ψ', hψ', hrange, hrest⟩ := recog h hm ψ hψ hidx hpair hsp
  rw [← hrange] at hrest hidx
  exact ⟨ψ', hψ', hidx, hrest⟩

end CFSG.Quasithin.H13.U4Par
