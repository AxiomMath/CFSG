module

public import CFSG.Quasithin.H13.L32A756a
public import CFSG.Quasithin.H13.L32A756c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G}

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem zα_le_U_of_comm (C : Ctx753 T L V K)
    (hD : ⁅centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (conjClosure V (hz T V))
      (conjSub ((k : G) * g) (conjClosure V (hz T V))),
      conjSub ((k : G) * g) (conjClosure V (hz T V))⁆ ≠ ⊥) :
    conjSub ((k : G) * g) (fsuV1 T V) ≤ conjClosure V (hz T V) := by
  have hcard : Nat.card ↥(conjSub ((k : G) * g) (fsuV1 T V)) = 2 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact C.card_V1
  rcases HypF98.eq_bot_or_eq_of_card_eq_two hcard (comm_D_le (g := g) (k := k)) with hb | he
  · exact absurd hb hD
  · rw [← he]
    refine (Subgroup.commutator_mono (centralizerMod_le_left _ _ _) le_rfl).trans ?_
    exact (N.comm_le' C).trans inf_le_left

end Not1471

namespace Ctx753

theorem mem_zα (C : Ctx753 T L V K) {x z : G} (hz1 : z ∈ fsuV1 T V) (hzne : z ≠ 1) {w : G}
    (hw : w ∈ conjSub x (fsuV1 T V)) : w = 1 ∨ w = x * z * x⁻¹ := by
  have hw' := mem_conjSub.1 hw
  rcases M755.eq_one_or_eq_of_card_two C.card_V1 hz1 hzne hw' with h | h
  · left
    have : w = x * (x⁻¹ * w * x) * x⁻¹ := by group
    rw [this, h]; group
  · right
    have : w = x * (x⁻¹ * w * x) * x⁻¹ := by group
    rw [this, h]

theorem mem_Gα_of_comm (C : Ctx753 T L V K) {x z c : G} (hz1 : z ∈ fsuV1 T V) (hzne : z ≠ 1)
    (hc : c * (x * z * x⁻¹) = (x * z * x⁻¹) * c) : c ∈ conjSub x (hz T V) := by
  rw [show hz T V = Subgroup.centralizer (fsuV1 T V : Set G) from rfl, ← conjSub_centralizer,
    Subgroup.mem_centralizer_iff]
  intro w hw
  rcases C.mem_zα hz1 hzne hw with rfl | rfl
  · simp
  · exact hc.symm

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem exists_K_of_derived (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    {a : ↥(quasithinG2 (ZMod 2))} (ha : a ∈ g2Derived (ZMod 2)) : ∃ k' ∈ K, C.ΦG E k' = a := by
  rw [← C.map_Φ_K E] at ha
  obtain ⟨k', hk', hke⟩ := ha
  exact ⟨k', Subgroup.mem_subgroupOf.mp hk', by rw [C.ΦG_eq E k'.2]; exact hke⟩

theorem eq_bot_of_derived_norm (hG : M755.G2Facts) {X : Subgroup ↥(quasithinG2 (ZMod 2))}
    (hXS : X ≤ sSubG) (hX2 : ∀ x ∈ X, x ^ 2 = 1) (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hN : ∀ d ∈ g2Derived (ZMod 2), ∀ x ∈ X, d * x * d⁻¹ ∈ X) : X = ⊥ := by
  by_contra hX1
  have hN0 : ∀ i ∈ M755.innerS, ∀ x ∈ X, sEltG i * x * (sEltG i)⁻¹ ∈ X := fun i hi =>
    hN _ ((hG.inner_iff i (M755.innerS_lt i hi)).2 hi)
  have hNz : ∀ x ∈ X, M755.z1 * x * M755.z1⁻¹ ∈ X := hN _ M755.z1_mem
  have h2 : (2 : ℕ) ∈ idx X := by
    rcases M755.idx_B0_or_A0 hXS hX2 hXc hX1 hN0 hNz with h | h
    · exact (h 2).2 (by decide)
    · exact (h 2).2 (by decide)
  have hA0 : ∀ l ∈ idx X, l ∈ [0, 2, 4, 6, 8, 10, 12, 14] := by
    rcases M755.idx_B0_or_A0 hXS hX2 hXc hX1 hN0 hNz with h | h
    · intro l hl
      have := (h l).1 hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      omega
    · exact fun l hl => (h l).1 hl
  have hz2 := hN _ (wordGG_mem_derived [2]) _ (mem_idx.1 h2).2
  have hconj : wordGG [2] * sEltG 2 * (wordGG [2])⁻¹ = sEltG 43 := by
    have hw : ∀ t ∈ [2], t = 1 ∨ t = 2 := by decide
    have e : wordGG [2] * sEltG 2 = sEltG 43 * wordGG [2] := by
      apply Subtype.ext
      apply linearEquiv_eq_of_matCode
      rw [Subgroup.coe_mul, Subgroup.coe_mul, matCode_mul, matCode_mul, M755.matCode_wordGG' hw,
        matCode_sEltG (by norm_num), matCode_sEltG (by norm_num)]
      exact M755.zC2_conj
    rw [e, mul_inv_cancel_right]
  have h43 : (43 : ℕ) ∈ idx X := mem_idx.2 ⟨by norm_num, hconj ▸ hz2⟩
  exact absurd (hA0 43 h43) (by decide)

theorem θ_zα_ne_one (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
    (N : Not1471 T L V (hz T V) γ γ' g k) {z : G} (hz1 : z ∈ fsuV1 T V) (hzne : z ≠ 1)
    (hZU : conjSub ((k : G) * g) (fsuV1 T V) ≤ conjClosure V (hz T V)) :
    C.θG e (((k : G) * g) * z * ((k : G) * g)⁻¹) ≠ 1 := by
  set x := (k : G) * g with hx
  set zα := x * z * x⁻¹ with hzα
  intro hθ
  have hzαU : zα ∈ conjClosure V (hz T V) := hZU (mul_mem_conjSub hz1)
  have hV1U : fsuV1 T V ≤ conjClosure V (hz T V) :=
    (inf_le_left : fsuV1 T V ≤ V).trans (le_conjClosure V _)
  have hc : ∀ h ∈ hz T V, zα⁻¹ * (h * zα * h⁻¹) ∈ fsuV1 T V := fun h hh =>
    C.mem_V1_of_θG E hh hzαU (by rw [C.θG_conj E hh hzαU, hθ, map_one])
  have hK : K ≤ Subgroup.centralizer ({zα} : Set G) := by
    rw [← C.kz_eq]
    refine oTwoUpper_le_of_pow_mem fun h hh => ⟨1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro w rfl
    have hc' := hc h hh
    set c := zα⁻¹ * (h * zα * h⁻¹) with hcdef
    have e1 : h * zα * h⁻¹ = zα * c := by rw [hcdef]; group
    have hcc : h * c * h⁻¹ = c := C.conj_V1 hh hc'
    have hc2 : c * c = 1 := by
      have := F7.isElemAbelian_pow_eq_one C.hF98.F911_3 (hV1U hc')
      rwa [pow_two] at this
    have e2 : (h * h) * zα * (h * h)⁻¹ = zα := by
      calc (h * h) * zα * (h * h)⁻¹ = h * (h * zα * h⁻¹) * h⁻¹ := by group
        _ = h * (zα * c) * h⁻¹ := by rw [e1]
        _ = (h * zα * h⁻¹) * (h * c * h⁻¹) := by group
        _ = zα * c * c := by rw [e1, hcc]
        _ = zα := by rw [mul_assoc, hc2, mul_one]
    rw [pow_one, pow_two]
    calc zα * (h * h) = ((h * h) * zα * (h * h)⁻¹) * (h * h) := by rw [e2]
      _ = (h * h) * zα := by group
  have hKN : ∀ c ∈ K, ∀ u ∈ conjSub x (conjClosure V (hz T V)),
      c * u * c⁻¹ ∈ conjSub x (conjClosure V (hz T V)) := by
    intro c hc u hu
    have hcG : c ∈ conjSub x (hz T V) := C.mem_Gα_of_comm hz1 hzne
      ((Subgroup.mem_centralizer_iff.mp (hK hc) zα rfl).symm)
    exact (Subgroup.mem_normalizer_iff.mp
      (conjSub_le_normalizer (le_normalizer_conjClosure V (hz T V)) x hcG) u).mp hu
  have hUαT := N.uα_le_T C
  have hUαH := N.uα_le_hz C
  have hUαe : IsElemAbelian 2 (conjSub x (conjClosure V (hz T V))) :=
    F7.isElemAbelian_conjSub C.hF98.F911_3
  obtain ⟨hX2, hXc⟩ := C.ΦX_elem E hUαH hUαe
  have hX : C.ΦX E (conjSub x (conjClosure V (hz T V))) = ⊥ := by
    refine eq_bot_of_derived_norm hG (C.ΦX_le_sSubG E hUαT) hX2 hXc fun d hd a ha => ?_
    obtain ⟨c, hcK, rfl⟩ := C.exists_K_of_derived E hd
    obtain ⟨u, hu, rfl⟩ := (C.mem_ΦX E hUαH).1 ha
    have hcH := C.le_hz hcK
    rw [C.mem_ΦX E hUαH]
    refine ⟨c * u * c⁻¹, hKN c hcK u hu, ?_⟩
    rw [C.ΦG_mul E (mul_mem hcH (hUαH hu)) (inv_mem hcH), C.ΦG_mul E hcH (hUαH hu),
      C.ΦG_inv E hcH]
  have hcard := C.card_ΦX E hUαH
  rw [hX, Subgroup.card_bot] at hcard
  exact absurd hcard.symm (ne_of_gt (N.one_lt_relIndex C))

end Ctx753

end CFSG.Quasithin.H13.L32A
