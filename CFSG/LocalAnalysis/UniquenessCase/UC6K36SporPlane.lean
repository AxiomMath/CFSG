module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

namespace Spor

section Group

variable {K : Type*} [Group K]

@[expose] def centSet (A : Subgroup K) : Set K :=
  {k | ∃ a ∈ A, a ≠ 1 ∧ a * k = k * a}

@[expose] def PlaneOK (A : Subgroup K) : Prop :=
  Subgroup.closure (centSet A) = ⊤ ∨
    ((∀ N : Subgroup K, N ≤ Subgroup.closure (centSet A) → IsPGroup 2 N →
        Subgroup.closure (centSet A) ≤ normalizer (N : Set K) → N = ⊥) ∧
      ∀ α : MulAut K, (∀ k ∈ Subgroup.closure (centSet A), α k = k) → Odd (orderOf α))

theorem planeFix_map_conj (hZ : Subgroup.center K = ⊥) (A : Subgroup K) :
    planeFix (A.map (MulAut.conj : K →* MulAut K)) = centSet A := by
  ext k
  constructor
  · rintro ⟨ε, ⟨a, ha, rfl⟩, hε1, hεk⟩
    refine ⟨a, ha, fun h1 => hε1 (by rw [h1, map_one]), ?_⟩
    rw [MulAut.conj_apply] at hεk
    calc a * k = (a * k * a⁻¹) * a := by group
      _ = k * a := by rw [hεk]
  · rintro ⟨a, ha, ha1, hak⟩
    refine ⟨MulAut.conj a, ⟨a, ha, rfl⟩, fun h1 => ha1 (conj_injective hZ (h1.trans (map_one _).symm)), ?_⟩
    rw [MulAut.conj_apply, hak, mul_inv_cancel_right]

theorem image_centSet (σ : MulAut K) (A : Subgroup K) :
    σ '' centSet A = centSet (A.map σ.toMonoidHom) := by
  ext k
  constructor
  · rintro ⟨x, ⟨a, ha, ha1, hax⟩, rfl⟩
    refine ⟨σ a, ⟨a, ha, rfl⟩, fun h1 => ha1 (σ.injective (h1.trans (map_one σ).symm)), ?_⟩
    rw [← map_mul, ← map_mul, hax]
  · rintro ⟨b, ⟨a, ha, rfl⟩, hb1, hbk⟩
    refine ⟨σ.symm k, ⟨a, ha, fun h1 => hb1 (by rw [h1]; exact map_one σ), ?_⟩, σ.apply_symm_apply k⟩
    apply σ.injective
    rw [map_mul, map_mul, σ.apply_symm_apply]
    exact hbk

theorem planeOK_map (σ : MulAut K) {A : Subgroup K} (h : PlaneOK A) : PlaneOK (A.map σ.toMonoidHom) := by
  have hH : Subgroup.closure (centSet (A.map σ.toMonoidHom)) = (Subgroup.closure (centSet A)).map σ.toMonoidHom := by
    rw [MonoidHom.map_closure, ← image_centSet]
    rfl
  rcases h with hgen | ⟨hX1, hX2⟩
  · left
    rw [hH, hgen, Subgroup.map_top_of_surjective _ σ.surjective]
  · right
    rw [hH]
    refine ⟨fun N hN hN2 hNn => ?_, fun α hα => ?_⟩
    ·
      set N' : Subgroup K := N.map σ.symm.toMonoidHom with hN'
      have hNN' : N = N'.map σ.toMonoidHom := by
        rw [hN', Subgroup.map_map]
        convert (Subgroup.map_id N).symm
        ext x
        simp
      have hN'H : N' ≤ Subgroup.closure (centSet A) := by
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨y, hy, rfl⟩ := hN hx
        simpa using hy
      have hN'2 : IsPGroup 2 N' := hN2.map _
      have hN'n : Subgroup.closure (centSet A) ≤ normalizer (N' : Set K) := by
        intro h hh
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have hσh : σ h ∈ normalizer (N : Set K) := hNn ⟨h, hh, rfl⟩
        have key := (Subgroup.mem_normalizer_iff.1 hσh) (σ x)
        constructor
        · rintro ⟨y, hy, rfl⟩
          refine ⟨σ (h * σ.symm y * h⁻¹), ?_, by simp⟩
          have : σ h * y * (σ h)⁻¹ ∈ N := by
            have := (Subgroup.mem_normalizer_iff.1 hσh y).1 hy
            exact this
          simpa [map_mul, map_inv] using this
        · rintro ⟨y, hy, hyx⟩
          refine ⟨σ x, ?_, by simp⟩
          have hx : h * x * h⁻¹ = σ.symm y := hyx.symm
          have : σ (h * x * h⁻¹) ∈ N := by rw [hx]; simpa using hy
          rw [map_mul, map_mul, map_inv] at this
          exact key.2 this
      have := hX1 N' hN'H hN'2 hN'n
      rw [hNN', this, Subgroup.map_bot]
    ·
      have hβ : ∀ k ∈ Subgroup.closure (centSet A), (σ⁻¹ * α * σ) k = k := by
        intro k hk
        have := hα (σ k) ⟨k, hk, rfl⟩
        change σ.symm (α (σ k)) = k
        rw [this, MulEquiv.symm_apply_apply]
      have hodd := hX2 _ hβ
      have : orderOf (σ⁻¹ * α * σ) = orderOf α := by
        have h1 : σ⁻¹ * α * σ = MulAut.conj σ⁻¹ α := by rw [MulAut.conj_apply, inv_inv]
        rw [h1]
        exact orderOf_injective (MulAut.conj σ⁻¹).toMonoidHom (MulAut.conj σ⁻¹).injective α
      rwa [this] at hodd

theorem planeGenOrExc_of_planeOK [Finite K] (hZ : Subgroup.center K = ⊥) {p : ℕ}
    (hinner : ∀ ε : MulAut K, ε ^ p = 1 → ε ∈ (MulAut.conj : K →* MulAut K).range)
    (h : ∀ A : Subgroup K, IsElemAbelian p A → Nat.card A = p ^ 2 → PlaneOK A) : PlaneGenOrExc K p := by
  intro Ē hE hEc
  have hEr : Ē ≤ (MulAut.conj : K →* MulAut K).range := fun ε hε => hinner ε (hE.2 ε hε)
  set A : Subgroup K := Ē.comap (MulAut.conj : K →* MulAut K) with hA
  have hAE : A.map (MulAut.conj : K →* MulAut K) = Ē := Subgroup.map_comap_eq_self hEr
  have hinj := conj_injective hZ
  have hAc : Nat.card A = p ^ 2 := by
    rw [← hEc, ← hAE, Subgroup.card_map_of_injective hinj]
  have hAe : IsElemAbelian p A := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      have := hE.1.is_comm.comm ⟨MulAut.conj (x : K), x.2⟩ ⟨MulAut.conj (y : K), y.2⟩
      simpa [map_mul] using congrArg Subtype.val this
    · apply hinj
      rw [map_pow, map_one]
      exact hE.2 _ hx
  rcases h A hAe hAc with hgen | ⟨hX1, hX2⟩
  · left
    rw [← hAE, planeFix_map_conj hZ, hgen]
  · right
    rw [← hAE, planeFix_map_conj hZ]
    exact ⟨hX1, hX2⟩

theorem planeOK_of_sylow [Finite K] {p : ℕ} [Fact p.Prime] (E : Sylow p K)
    (h : ∀ A : Subgroup K, A ≤ E → IsElemAbelian p A → Nat.card A = p ^ 2 → PlaneOK A) :
    ∀ A : Subgroup K, IsElemAbelian p A → Nat.card A = p ^ 2 → PlaneOK A := by
  intro A hAe hAc
  have hAp : IsPGroup p A := IsPGroup.of_card hAc
  obtain ⟨T, hAT⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K E T
  have hTE : (T : Subgroup K) = (E : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  set A' : Subgroup K := A.map (MulAut.conj g⁻¹).toMonoidHom with hA'
  have hA'E : A' ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    have hxT := hAT hx
    rw [hTE] at hxT
    obtain ⟨y, hy, rfl⟩ := hxT
    have hyy : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom y) = y := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [hyy]
    exact hy
  have hA'e : IsElemAbelian p A' := CFSG.Open.IsElemAbelian.map hAe _
  have hA'c : Nat.card A' = p ^ 2 := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hAc]
  have hok := planeOK_map (MulAut.conj g) (h A' hA'E hA'e hA'c)
  have hAA : A'.map (MulAut.conj g).toMonoidHom = A := by
    rw [hA', Subgroup.map_map]
    convert Subgroup.map_id A
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rwa [hAA] at hok

theorem mem_range_conj_of_card_mulAut_le [Finite K] (hZ : Subgroup.center K = ⊥)
    (hA : Nat.card (MulAut K) ≤ 2 * Nat.card K) {p : ℕ} (hp : Odd p) (ε : MulAut K) (hε : ε ^ p = 1) :
    ε ∈ (MulAut.conj : K →* MulAut K).range := by
  set I := (MulAut.conj : K →* MulAut K).range with hI
  have hIc : Nat.card I = Nat.card K := by
    rw [hI, ← Nat.card_congr (MonoidHom.ofInjective (conj_injective hZ)).toEquiv]
  have hidx : I.index ≤ 2 := by
    have h1 := I.card_mul_index
    rw [hIc] at h1
    have hK : 0 < Nat.card K := Nat.card_pos
    by_contra hc
    push Not at hc
    have : 3 * Nat.card K ≤ Nat.card (MulAut K) := by
      rw [← h1, mul_comm]
      exact Nat.mul_le_mul_left _ hc
    omega
  have hipos : 0 < I.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  interval_cases hix : I.index
  · rw [Subgroup.index_eq_one] at hix
    rw [hix]
    exact Subgroup.mem_top ε
  · obtain ⟨m, rfl⟩ := hp
    have hsq : ε ^ 2 ∈ I := Subgroup.sq_mem_of_index_two hix ε
    have : ε = (ε ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hε, one_mul]
    rw [this]
    exact I.pow_mem hsq _

theorem planeGenOrExc_of_not_dvd [Finite K] (hZ : Subgroup.center K = ⊥) {p : ℕ}
    (hinner : ∀ ε : MulAut K, ε ^ p = 1 → ε ∈ (MulAut.conj : K →* MulAut K).range)
    (hp : ¬ p ^ 2 ∣ Nat.card K) : PlaneGenOrExc K p := by
  intro Ē hE hEc
  exfalso
  apply hp
  have hEr : Ē ≤ (MulAut.conj : K →* MulAut K).range := fun ε hε => hinner ε (hE.2 ε hε)
  have hd : Nat.card Ē ∣ Nat.card (MulAut.conj : K →* MulAut K).range := Subgroup.card_dvd_of_le hEr
  rwa [hEc, ← Nat.card_congr (MonoidHom.ofInjective (conj_injective hZ)).toEquiv] at hd

end Group

theorem planeGenOrExc_of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') {p : ℕ}
    (h : PlaneGenOrExc K p) : PlaneGenOrExc K' p := by
  intro Ē' hE' hEc'
  set c : MulAut K' ≃* MulAut K := MulAut.congr e.symm with hc
  set Ē : Subgroup (MulAut K) := Ē'.map c.toMonoidHom with hĒ
  have hEe : IsElemAbelian p Ē := CFSG.Open.IsElemAbelian.map hE' _
  have hEc : Nat.card Ē = p ^ 2 := by rw [hĒ, Subgroup.card_map_of_injective c.injective, hEc']
  have hfix : planeFix Ē = e.symm '' planeFix Ē' := by
    ext k
    constructor
    · rintro ⟨ε, ⟨ε', hε', rfl⟩, hε1, hεk⟩
      refine ⟨e k, ⟨ε', hε', fun h1 => hε1 (by rw [h1]; exact map_one c), ?_⟩, e.symm_apply_apply k⟩
      have : e.symm (ε' (e k)) = k := hεk
      have h2 := congrArg e this
      simpa using h2
    · rintro ⟨k', ⟨ε', hε', hε1, hεk⟩, rfl⟩
      refine ⟨c ε', ⟨ε', hε', rfl⟩, fun h1 => hε1 (c.injective (h1.trans (map_one c).symm)), ?_⟩
      change e.symm (ε' (e (e.symm k'))) = e.symm k'
      rw [e.apply_symm_apply, hεk]
  have hcl : Subgroup.closure (planeFix Ē) = (Subgroup.closure (planeFix Ē')).map e.symm.toMonoidHom := by
    rw [hfix, MonoidHom.map_closure]
    rfl
  rcases h Ē hEe hEc with hgen | ⟨hX1, hX2⟩
  · left
    have h1 : (Subgroup.closure (planeFix Ē')).map e.symm.toMonoidHom = ⊤ := hcl ▸ hgen
    rw [eq_top_iff]
    intro k _
    have : e.symm k ∈ (Subgroup.closure (planeFix Ē')).map e.symm.toMonoidHom := h1 ▸ Subgroup.mem_top _
    obtain ⟨k', hk', hkk⟩ := this
    have : k' = k := e.symm.injective hkk
    rwa [← this]
  · right
    refine ⟨fun N hN hN2 hNn => ?_, fun α hα => ?_⟩
    · have hN' := hX1 (N.map e.symm.toMonoidHom) (by rw [hcl]; exact Subgroup.map_mono hN) (hN2.map _) (by
        rw [hcl]
        rintro _ ⟨h', hh', rfl⟩
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have key := Subgroup.mem_normalizer_iff.1 (hNn hh') (e x)
        constructor
        · rintro ⟨y, hy, rfl⟩
          refine ⟨h' * y * h'⁻¹, (Subgroup.mem_normalizer_iff.1 (hNn hh') y).1 hy, by simp⟩
        · rintro ⟨y, hy, hyx⟩
          refine ⟨e x, key.2 ?_, by simp⟩
          have hyx' : e.symm y = e.symm h' * x * (e.symm h')⁻¹ := hyx
          have : h' * e x * h'⁻¹ = y := by
            apply e.symm.injective
            rw [hyx']
            simp [map_mul, map_inv]
          rw [this]
          exact hy)
      rw [Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective] at hN'
      exact hN'
    · have hβ : ∀ k ∈ Subgroup.closure (planeFix Ē), c α k = k := by
        intro k hk
        rw [hcl] at hk
        obtain ⟨k', hk', rfl⟩ := hk
        change e.symm (α (e (e.symm k'))) = e.symm k'
        rw [e.apply_symm_apply, hα k' hk']
      have hodd := hX2 (c α) hβ
      have hord : orderOf (c α) = orderOf α := orderOf_injective c.toMonoidHom c.injective α
      rwa [hord] at hodd

end Spor

end CFSG.LocalAnalysis.UniquenessCase.UCK
