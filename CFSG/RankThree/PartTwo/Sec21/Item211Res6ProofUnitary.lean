module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofUniExt
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofGraph
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly (IsElemAbelian)
open Item211Lie2Proof Item211Res5Proof

section UniTransfer

variable {p f : ℕ} {K : Type} [Field K] [Finite K]

variable (h : UnitaryFieldData p f K) in
@[expose] noncomputable def gammaExt (hq : 2 < p ^ f) (T : Subgroup (MulAut (unitaryPSU h 3))) :
    Subgroup (MulAut (projectiveSL 3 K)) where
  carrier := {u | ∃ t ∈ T, u = extAut h hq t ∨ u = extAut h hq t * gammaAut h}
  mul_mem' := by
    rintro _ _ ⟨t, ht, rfl | rfl⟩ ⟨s, hs, rfl | rfl⟩
    · exact ⟨t * s, T.mul_mem ht hs, Or.inl (map_mul _ t s).symm⟩
    · exact ⟨t * s, T.mul_mem ht hs, Or.inr (by rw [map_mul, mul_assoc])⟩
    · refine ⟨t * s, T.mul_mem ht hs, Or.inr ?_⟩
      rw [map_mul, mul_assoc, gammaAut_comm hq s, mul_assoc]
    · refine ⟨t * s, T.mul_mem ht hs, Or.inl ?_⟩
      calc extAut h hq t * gammaAut h * (extAut h hq s * gammaAut h) =
          extAut h hq t * (gammaAut h * extAut h hq s) * gammaAut h := by group
        _ = extAut h hq t * extAut h hq s * (gammaAut h * gammaAut h) := by
            rw [gammaAut_comm hq s]; group
        _ = extAut h hq (t * s) := by rw [gammaAut_mul_self, mul_one, map_mul]
  one_mem' := ⟨1, T.one_mem, Or.inl (map_one _).symm⟩
  inv_mem' := by
    rintro _ ⟨t, ht, rfl | rfl⟩
    · exact ⟨t⁻¹, T.inv_mem ht, Or.inl (map_inv _ t).symm⟩
    · refine ⟨t⁻¹, T.inv_mem ht, Or.inr ?_⟩
      have hγ : (gammaAut h)⁻¹ = gammaAut h := inv_eq_of_mul_eq_one_left gammaAut_mul_self
      rw [mul_inv_rev, hγ, ← gammaAut_comm hq t⁻¹, map_inv]

variable {h : UnitaryFieldData p f K} {hq : 2 < p ^ f} {T : Subgroup (MulAut (unitaryPSU h 3))}

theorem extAut_mem_gammaExt {t : MulAut (unitaryPSU h 3)} (ht : t ∈ T) :
    extAut h hq t ∈ gammaExt h hq T :=
  ⟨t, ht, Or.inl rfl⟩

theorem gammaAut_mem_gammaExt : gammaAut h ∈ gammaExt h hq T :=
  ⟨1, T.one_mem, Or.inr (by rw [map_one, one_mul])⟩

theorem gammaExt_isPGroup (hT2 : IsPGroup 2 T) : IsPGroup 2 (gammaExt h hq T) := by
  rintro ⟨u, t, ht, hu⟩
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k + 1, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  have hΦ : extAut h hq t ^ 2 ^ (k + 1) = 1 := by
    rw [← map_pow, pow_succ, pow_mul, htk, one_pow, map_one]
  rcases hu with rfl | rfl
  · exact hΦ
  · rw [(show Commute (gammaAut h) (extAut h hq t) from gammaAut_comm hq t).symm.mul_pow, hΦ,
      one_mul, pow_succ, pow_mul',
      sq, gammaAut_mul_self, one_pow]

theorem gammaExt_le_centralizer {D : Subgroup (MulAut (unitaryPSU h 3))}
    (hTD : T ≤ Subgroup.centralizer (D : Set (MulAut (unitaryPSU h 3)))) :
    gammaExt h hq T ≤ Subgroup.centralizer ((D.map (extAut h hq) : Subgroup _) :
      Set (MulAut (projectiveSL 3 K))) := by
  rintro _ ⟨t, ht, rfl | rfl⟩ <;> rw [Subgroup.mem_centralizer_iff] <;>
    rintro _ ⟨d, hd, rfl⟩ <;> have h1 := Subgroup.mem_centralizer_iff.mp (hTD ht) d hd
  · rw [← map_mul, ← map_mul, h1]
  · calc extAut h hq d * (extAut h hq t * gammaAut h) =
        extAut h hq (d * t) * gammaAut h := by rw [map_mul, mul_assoc]
      _ = extAut h hq (t * d) * gammaAut h := by rw [h1]
      _ = extAut h hq t * (extAut h hq d * gammaAut h) := by rw [map_mul, mul_assoc]
      _ = extAut h hq t * (gammaAut h * extAut h hq d) := by rw [gammaAut_comm hq d]
      _ = extAut h hq t * gammaAut h * extAut h hq d := by rw [mul_assoc]

theorem exists_eq_extAut_conj (hq3 : p ^ f % 3 = 2) {v : MulAut (projectiveSL 3 K)}
    (hv : v ∈ innP K) (hvγ : v * gammaAut h = gammaAut h * v) :
    ∃ y : unitaryPSU h 3, v = extAut h hq (MulAut.conj y) := by
  obtain ⟨g, rfl⟩ := hv
  have h1 : MulAut.conj (gammaAut h g) = MulAut.conj g := by
    rw [← mul_conj_mul_inv', ← hvγ, mul_inv_cancel_right]
  obtain ⟨y, hy⟩ := mem_range_of_gammaAut_eq hq3 (conj_injective_three h1)
  exact ⟨y, by rw [extAut_conj, hy]⟩

omit [Finite K] in
theorem innP_le_semilinear : innP K ≤ semilinearAutGroup 3 K := by
  rintro _ ⟨g, rfl⟩
  obtain ⟨g', rfl⟩ := proj_surjective 3 K g
  rw [← conjAut_toGL]
  exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)

theorem gammaExt_inf_innP (hq3 : p ^ f % 3 = 2) :
    gammaExt h hq T ⊓ innP K =
      (T ⊓ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range).map
        (extAut h hq) := by
  ext u
  constructor
  · rintro ⟨⟨t, ht, rfl | rfl⟩, hu⟩
    · obtain ⟨y, hy⟩ := exists_eq_extAut_conj (hq := hq) hq3 hu (gammaAut_comm hq t).symm
      exact ⟨t, ⟨ht, ⟨y, (extAut_injective hq hy).symm⟩⟩, rfl⟩
    · exfalso
      apply gammaAut_not_mem_semilinear (h := h)
      have e : gammaAut h = (extAut h hq t)⁻¹ * (extAut h hq t * gammaAut h) := by group
      rw [e]
      exact mul_mem (inv_mem (extAut_mem_semilinear hq t)) (innP_le_semilinear hu)
  · rintro ⟨t, ⟨ht, ⟨y, rfl⟩⟩, rfl⟩
    refine ⟨extAut_mem_gammaExt ht, ?_⟩
    rw [extAut_conj]
    exact ⟨_, rfl⟩

theorem innP_inf_centralizer_gammaExt (hq3 : p ^ f % 3 = 2) :
    innP K ⊓ Subgroup.centralizer (gammaExt h hq T : Set (MulAut (projectiveSL 3 K))) =
      ((MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range ⊓
        Subgroup.centralizer (T : Set (MulAut (unitaryPSU h 3)))).map (extAut h hq) := by
  ext v
  constructor
  · rintro ⟨hv, hvc⟩
    have hvγ : v * gammaAut h = gammaAut h * v :=
      (Subgroup.mem_centralizer_iff.mp hvc _ gammaAut_mem_gammaExt).symm
    obtain ⟨y, rfl⟩ := exists_eq_extAut_conj (hq := hq) hq3 hv hvγ
    refine ⟨MulAut.conj y, Subgroup.mem_inf.mpr ⟨⟨y, rfl⟩, ?_⟩, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro t ht
    apply extAut_injective hq
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hvc _ (extAut_mem_gammaExt ht)
  · rintro ⟨x, ⟨⟨y, rfl⟩, hxc⟩, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨by rw [extAut_conj]; exact ⟨_, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl | rfl⟩
    · rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxc t ht]
    · have ht' := Subgroup.mem_centralizer_iff.mp hxc t ht
      calc extAut h hq t * gammaAut h * extAut h hq (MulAut.conj y) =
          extAut h hq t * (gammaAut h * extAut h hq (MulAut.conj y)) := by group
        _ = extAut h hq (t * MulAut.conj y) * gammaAut h := by
            rw [gammaAut_comm hq, map_mul]; group
        _ = extAut h hq (MulAut.conj y * t) * gammaAut h := by rw [ht']
        _ = extAut h hq (MulAut.conj y) * (extAut h hq t * gammaAut h) := by
            rw [map_mul]; group

theorem threeClosureIn_gammaExt (hq3 : p ^ f % 3 = 2) :
    threeClosureIn (innP K) (gammaExt h hq T) =
      (threeClosureIn (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range T).map
        (extAut h hq) := by
  rw [threeClosureIn, threeClosureIn, MonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨hv, hv3⟩
    rw [innP_inf_centralizer_gammaExt hq3] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    apply extAut_injective hq
    rw [map_pow, hv3, map_one]
  · rintro ⟨x, ⟨hx, hx3⟩, rfl⟩
    refine ⟨?_, by rw [← map_pow, hx3, map_one]⟩
    rw [innP_inf_centralizer_gammaExt hq3]
    exact ⟨x, hx, rfl⟩

theorem outerCentConcl_of_gammaExt (hq3 : p ^ f % 3 = 2)
    (hU : OuterCentConcl (innP K) (gammaExt h hq T)) :
    OuterCentConcl (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range T := by
  have hN := threeClosureIn_gammaExt (T := T) (hq := hq) hq3
  have hinj := extAut_injective (h := h) hq
  refine ⟨fun P hPN hP2 hNP x hx n hn => ?_, fun P hP hP2 => ?_⟩
  · have hle : threeClosureIn (innP K) (gammaExt h hq T) ≤
        Subgroup.normalizer ((P.map (extAut h hq) : Subgroup _) :
          Set (MulAut (projectiveSL 3 K))) := by
      rw [hN]
      rintro _ ⟨m, hm, rfl⟩
      exact Subgroup.le_normalizer_map (extAut h hq) ⟨m, hNP hm, rfl⟩
    have := hU.1 (P.map (extAut h hq)) (by rw [hN]; exact Subgroup.map_mono hPN) (hP2.map _)
      hle (extAut h hq x) ⟨x, hx, rfl⟩ (extAut h hq n) (by rw [hN]; exact ⟨n, hn, rfl⟩)
    apply hinj
    rw [map_mul, map_mul]
    exact this
  · have hPmap : P.map (extAut h hq) ≤ innP K ⊓
        Subgroup.centralizer (gammaExt h hq T : Set (MulAut (projectiveSL 3 K))) ⊓
        Subgroup.centralizer (threeClosureIn (innP K) (gammaExt h hq T) :
          Set (MulAut (projectiveSL 3 K))) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxIT, hxN⟩ := hP hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [innP_inf_centralizer_gammaExt hq3]
        exact ⟨x, hxIT, rfl⟩
      · rw [hN]
        refine Subgroup.mem_centralizer_iff.mpr ?_
        rintro _ ⟨n, hn, rfl⟩
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxN n hn]
    have hcyc := hU.2 _ hPmap (hP2.map _)
    exact isCyclic_of_surjective (Subgroup.equivMapOfInjective P _ hinj).symm.toMonoidHom
      (MulEquiv.surjective _)

theorem nonabelian_gammaExt (hq3 : p ^ f % 3 = 2)
    (hnab : ¬ (∀ a ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range ⊓
        Subgroup.centralizer ((T ⊓ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range :
          Subgroup (MulAut (unitaryPSU h 3))) : Set (MulAut (unitaryPSU h 3))),
      ∀ b ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range ⊓
        Subgroup.centralizer ((T ⊓ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range :
          Subgroup (MulAut (unitaryPSU h 3))) : Set (MulAut (unitaryPSU h 3))),
      a * b = b * a)) :
    ¬ (∀ a ∈ innP K ⊓ Subgroup.centralizer
        ((gammaExt h hq T ⊓ innP K : Subgroup (MulAut (projectiveSL 3 K))) :
          Set (MulAut (projectiveSL 3 K))),
      ∀ b ∈ innP K ⊓ Subgroup.centralizer
        ((gammaExt h hq T ⊓ innP K : Subgroup (MulAut (projectiveSL 3 K))) :
          Set (MulAut (projectiveSL 3 K))),
      a * b = b * a) := by
  intro hall
  apply hnab
  have hmem : ∀ x ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range ⊓
      Subgroup.centralizer ((T ⊓ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range :
        Subgroup (MulAut (unitaryPSU h 3))) : Set (MulAut (unitaryPSU h 3))),
      extAut h hq x ∈ innP K ⊓ Subgroup.centralizer
        ((gammaExt h hq T ⊓ innP K : Subgroup (MulAut (projectiveSL 3 K))) :
          Set (MulAut (projectiveSL 3 K))) := by
    rintro _ ⟨⟨y, rfl⟩, hxc⟩
    refine Subgroup.mem_inf.mpr ⟨by rw [extAut_conj]; exact ⟨_, rfl⟩, ?_⟩
    rw [gammaExt_inf_innP hq3]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxc t ht]
  intro a ha b hb
  apply extAut_injective hq
  rw [map_mul, map_mul]
  exact hall _ (hmem a ha) _ (hmem b hb)

end UniTransfer

end Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open Item211Res6Proof

theorem ks211L3OuterCentUnitary_holds : KS211L3OuterCentUnitary := by
  intro p f K _ h hp3 hq3 D T hDe hD9 hT2 _ hTD hnab _
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hq : 2 < p ^ f :=
    lt_of_lt_of_le (by omega) (Nat.le_self_pow (by have := h.one_le; omega) p)
  have hK3 : Nat.card K % 3 = 1 := by
    rw [h.card, pow_mul', Nat.pow_mod, hq3]
  change OuterCentConcl (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range T
  refine outerCentConcl_of_gammaExt (hq := hq) hq3 ?_
  have hU2 := gammaExt_isPGroup (hq := hq) hT2
  by_cases hR : T ⊓ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range = ⊥
  · have hRU : gammaExt h hq T ⊓ innP K = ⊥ := by
      rw [gammaExt_inf_innP hq3, hR, Subgroup.map_bot]
    exact outerCentConcl_of_not_semilinear hp3 hU2 hRU gammaAut_mem_gammaExt
      gammaAut_not_mem_semilinear
  · have hRU : gammaExt h hq T ⊓ innP K ≠ ⊥ := by
      rw [gammaExt_inf_innP hq3]
      intro h0
      exact hR ((Subgroup.map_eq_bot_iff_of_injective _ (extAut_injective hq)).mp h0)
    exact outerCentConcl_of_inf_ne_bot hp3 hK3 (isElemAbelian_map hDe (extAut h hq))
      (by rw [Subgroup.card_map_of_injective (extAut_injective hq)]; exact hD9) hU2
      (gammaExt_le_centralizer hTD) (nonabelian_gammaExt hq3 hnab) hRU

theorem ks211L3PlusUnitaryOuter_holds : KS211L3PlusUnitaryOuter :=
  ks211L3PlusUnitaryOuter_of_cent ks211L3OuterCentUnitary_holds

end CFSG.RankThree.PartTwo.Sec21
