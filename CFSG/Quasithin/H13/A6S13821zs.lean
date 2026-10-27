module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F9Eighteen

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem relIndex_ne_zero' (A B : Subgroup G) : A.relIndex B ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem f918_6_core {T V L V₁ Vp H K : Subgroup G} (h : HypF918 T V L V₁ Vp H K)
    {W : Subgroup G} (hV₁W : V₁ ≤ W) (hWU : W ≤ conjClosure Vp H)
    (hWN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (W : Set G))
    (hWK : tildeOf V₁ W ≤ tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆)
    (ha : tildeOf V₁ W ≠ tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆) :
    ∃ B : Subgroup G, IsF918B T L V₁ Vp H (conjClosure K T) B ∧
      2 * (centralizerMod V₁ W B).relIndex W ≤ ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 := by
  obtain ⟨B, hB, -⟩ := h.F918_2
  obtain ⟨hBL, hq, hfaith⟩ := hB
  have hBT : B ≤ T := hBL.trans h.pCoreOf_L₁T_le_T
  have hBX : B ≤ conjClosure K T ⊔ T := hBT.trans le_sup_right
  have hUW : conjClosure Vp H ≤ Subgroup.normalizer (W : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le h.toHypF98.F911_3 hWU
  have hBNW : B ≤ Subgroup.normalizer (W : Set G) := hBX.trans hWN
  have hnt2 : ¬ ∀ k ∈ conjClosure K T, ∀ u ∈ conjClosure Vp H, k * u * k⁻¹ * u⁻¹ ∈ W := by
    intro hall
    have hle : ⁅conjClosure Vp H, conjClosure K T⁆ ≤ W := by
      refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
      have := W.inv_mem (hall k hk u hu)
      have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ := by group
      rwa [e] at this
    exact ha (le_antisymm hWK (secImg_mono hle))
  obtain ⟨-, hf2⟩ := h.central_kernel_and_faithful hBT hfaith hWN h.K₀T_le_normalizer_U hnt2
  have hmul := (relIndex_mul_le_relIndex hV₁W hWU hUW hBNW (B := B)).trans hq.2.2.2.2
  have hnt2' : ¬ ∀ b ∈ B, ∀ e ∈ conjClosure Vp H, b * e * b⁻¹ * e⁻¹ ∈ W := fun hall =>
    hq.2.2.1 fun b hb => hf2 b hb fun e he => hall b hb e he
  have hc2 : 2 ≤ (centralizerMod W (conjClosure Vp H) B).relIndex (conjClosure Vp H) := by
    have hne1 : (centralizerMod W (conjClosure Vp H) B).relIndex (conjClosure Vp H) ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      apply hnt2'
      intro b hb e he
      have h2 := (h1 he).2.2 b hb
      have e' : b * e * b⁻¹ * e⁻¹ = (e * b * e⁻¹ * b⁻¹)⁻¹ := by group
      rw [e']
      exact W.inv_mem h2
    have hne0 : (centralizerMod W (conjClosure Vp H) B).relIndex (conjClosure Vp H) ≠ 0 :=
      (relIndex_ne_zero' _ _)
    omega
  refine ⟨B, ⟨hBL, hq, hfaith⟩, ?_⟩
  calc 2 * (centralizerMod V₁ W B).relIndex W
      ≤ (centralizerMod W (conjClosure Vp H) B).relIndex (conjClosure Vp H) *
          (centralizerMod V₁ W B).relIndex W := Nat.mul_le_mul_right _ hc2
    _ = (centralizerMod V₁ W B).relIndex W *
          (centralizerMod W (conjClosure Vp H) B).relIndex (conjClosure Vp H) := mul_comm _ _
    _ ≤ ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 := hmul

theorem relIndex_mul_le_sup {V₁ I I' J C C' B : Subgroup G} (hV₁I : V₁ ≤ I) (hIJ : I ≤ J)
    (hI'J : I' ≤ J) (hJI : J ≤ Subgroup.normalizer (I : Set G))
    (hBI : B ≤ Subgroup.normalizer (I : Set G)) (hBI' : B ≤ Subgroup.normalizer (I' : Set G))
    (hV₁C : V₁ ≤ C) (hIC : I ≤ Subgroup.normalizer (C : Set G))
    (hI'C' : I' ≤ Subgroup.normalizer (C' : Set G)) (hII' : I ⊓ I' ≤ C') :
    (centralizerMod C I B).relIndex I * (centralizerMod C' I' B).relIndex I' ≤
      (centralizerMod V₁ J B).relIndex J := by
  have h1 := relIndex_mul_le_relIndex hV₁I hIJ hJI hBI (B := B)
  have h2 : (centralizerMod C I B).relIndex I ≤ (centralizerMod V₁ I B).relIndex I := by
    refine Subgroup.relIndex_le_of_le_left (fun x hx => ?_) (relIndex_ne_zero' _ _)
    exact ⟨hx.1, hIC hx.1, fun b hb => hV₁C (hx.2.2 b hb)⟩
  have h3 : (centralizerMod C' I' B).relIndex I' ≤ (centralizerMod I J B).relIndex J := by
    have hle : centralizerMod I J B ⊓ I' ≤ centralizerMod C' I' B := by
      rintro x ⟨⟨-, -, hx⟩, hxI'⟩
      refine ⟨hxI', hI'C' hxI', fun b hb => hII' ⟨hx b hb, ?_⟩⟩
      have h4 : b * x⁻¹ * b⁻¹ ∈ I' :=
        (Subgroup.mem_normalizer_iff.mp (hBI' hb) _).mp (I'.inv_mem hxI')
      have e : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
      rw [e]
      exact I'.mul_mem hxI' h4
    calc (centralizerMod C' I' B).relIndex I'
        ≤ (centralizerMod I J B ⊓ I').relIndex I' :=
          Subgroup.relIndex_le_of_le_left hle (relIndex_ne_zero' _ _)
      _ = (centralizerMod I J B).relIndex I' := Subgroup.inf_relIndex_right _ _
      _ ≤ (centralizerMod I J B).relIndex J :=
          Subgroup.relIndex_le_of_le_right hI'J (relIndex_ne_zero' _ _)
  exact (Nat.mul_le_mul h2 h3).trans h1

omit [Finite G] in
theorem centralizerMod_conjSub_eq {V₁ C' I' B Q : Subgroup G} {c : G} (hV₁C : V₁ ≤ C')
    (hBc : ∀ b ∈ B, c * b * c⁻¹ * b⁻¹ ∈ Q)
    (hQ : ∀ q ∈ Q, ∀ u ∈ I', q * u * q⁻¹ * u⁻¹ ∈ V₁)
    (hBI : B ≤ Subgroup.normalizer (I' : Set G)) :
    centralizerMod C' I' (conjSub c B) = centralizerMod C' I' B := by
  have key : ∀ x ∈ I', ∀ b ∈ B,
      (x * (c * b * c⁻¹) * x⁻¹ * (c * b * c⁻¹)⁻¹ ∈ C' ↔ x * b * x⁻¹ * b⁻¹ ∈ C') := by
    intro x hx b hb
    set q := c * b * c⁻¹ * b⁻¹ with hq
    have hqQ : q ∈ Q := hBc b hb
    have hw : x * b * x⁻¹ * b⁻¹ ∈ I' := by
      have h4 : b * x⁻¹ * b⁻¹ ∈ I' :=
        (Subgroup.mem_normalizer_iff.mp (hBI hb) _).mp (I'.inv_mem hx)
      have e : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
      rw [e]
      exact I'.mul_mem hx h4
    have h1 : x * q * x⁻¹ * q⁻¹ ∈ V₁ := by
      have := V₁.inv_mem (hQ q hqQ x hx)
      have e : (q * x * q⁻¹ * x⁻¹)⁻¹ = x * q * x⁻¹ * q⁻¹ := by group
      rwa [e] at this
    have h2 := hQ q hqQ _ hw
    have e : x * (c * b * c⁻¹) * x⁻¹ * (c * b * c⁻¹)⁻¹ =
        (x * q * x⁻¹ * q⁻¹) * ((q * (x * b * x⁻¹ * b⁻¹) * q⁻¹ * (x * b * x⁻¹ * b⁻¹)⁻¹) *
          (x * b * x⁻¹ * b⁻¹)) := by
      rw [hq]; group
    rw [e]
    constructor
    · intro h
      have h3 := C'.mul_mem (C'.inv_mem (hV₁C h1)) h
      rw [← mul_assoc, inv_mul_cancel, one_mul] at h3
      have h5 := C'.mul_mem (C'.inv_mem (hV₁C h2)) h3
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h5
    · intro h
      exact C'.mul_mem (hV₁C h1) (C'.mul_mem (hV₁C h2) h)
  ext x
  constructor
  · rintro ⟨hxI, hxN, hx⟩
    refine ⟨hxI, hxN, fun b hb => (key x hxI b hb).mp (hx _ (mul_mem_conjSub hb))⟩
  · rintro ⟨hxI, hxN, hx⟩
    refine ⟨hxI, hxN, fun b' hb' => ?_⟩
    have hb := mem_conjSub.mp hb'
    have e : b' = c * (c⁻¹ * b' * c) * c⁻¹ := by group
    rw [e]
    exact (key x hxI _ hb).mpr (hx _ hb)

omit [Finite G] in
theorem relIndex_centralizerMod_conjSub {V₁ C I B Q : Subgroup G} {c : G}
    (hV₁C : V₁ ≤ conjSub c C) (hBc : ∀ b ∈ B, c * b * c⁻¹ * b⁻¹ ∈ Q)
    (hQ : ∀ q ∈ Q, ∀ u ∈ conjSub c I, q * u * q⁻¹ * u⁻¹ ∈ V₁)
    (hBI : B ≤ Subgroup.normalizer ((conjSub c I : Subgroup G) : Set G)) :
    (centralizerMod (conjSub c C) (conjSub c I) B).relIndex (conjSub c I) =
      (centralizerMod C I B).relIndex I := by
  rw [← centralizerMod_conjSub_eq hV₁C hBc hQ hBI, ← conjSub_centralizerMod]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective

end CFSG.Quasithin.H13.A6.A6S20
