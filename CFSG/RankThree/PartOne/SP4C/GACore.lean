module

public import CFSG.RankThree.PartOne.SP4C.WeylTorus
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even

public section

namespace CFSG.RankThree.PartOne.SP4C

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.LieType.Universal.Unitary Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Lin2.Five (tauAut tauAut_proj projEquiv tauAut_not_mem_E)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.PartTwo.KFacts

variable {p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def spQe (K : Type) [Field K] [Finite K] [CharP K 2] :
    ↥(spRev K) ≃* StatedProj (StatedSp 2 K) :=
  (spRevEquiv K).symm.trans (projEquiv K)

theorem spQe_apply (t : ↥(spRev K)) : spQe K t = proj 2 K ((spRevEquiv K).symm t) := rfl

@[expose] noncomputable def toRev (α : MulAut (StatedProj (StatedSp 2 K))) : MulAut ↥(spRev K) :=
  (spQe K).trans (α.trans (spQe K).symm)

theorem spQe_toRev (α : MulAut (StatedProj (StatedSp 2 K))) (t : ↥(spRev K)) :
    spQe K (toRev α t) = α (spQe K t) := by
  simp [toRev]

theorem spQe_tauRev (t : ↥(spRev K)) : spQe K (tauRev t) = tauAut (spQe K t) := by
  rw [spQe_apply, symm_tauRev, spQe_apply, tauAut_proj]
  rfl

theorem spQe_fieldRev (σ : K ≃+* K) (t : ↥(spRev K)) :
    spQe K (fieldRev σ t) = fieldAut 2 K σ (spQe K t) := by
  rw [spQe_apply, symm_fieldRev, spQe_apply, fieldAut_proj]

theorem conj_spQe (m t : ↥(spRev K)) :
    MulAut.conj (spQe K m) (spQe K t) = spQe K (m * t * m⁻¹) := by
  simp [MulAut.conj_apply]

theorem exists_decomp (α : MulAut (StatedProj (StatedSp 2 K))) :
    ∃ (m : ↥(spRev K)) (σ : K ≃+* K),
      (∃ A : gsp 2 K, α = conjAut 2 K A * fieldAut 2 K σ ∧
        ∀ t, toRev α t = m * fieldRev σ t * m⁻¹) ∨
      (∃ A : gsp 2 K, α = conjAut 2 K A * fieldAut 2 K σ * tauAut ∧
        ∀ t, toRev α t = m * fieldRev σ (tauRev t) * m⁻¹) := by
  obtain ⟨A, σ, e, he, hα⟩ := exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow α
  obtain ⟨x, hx⟩ := conjAut_mem_inner_of_charTwo A
  obtain ⟨m, rfl⟩ := (spQe K).surjective x
  refine ⟨m, σ, ?_⟩
  have hconj : ∀ t : ↥(spRev K), conjAut 2 K A (spQe K t) = spQe K (m * t * m⁻¹) := by
    intro t
    rw [← hx]
    exact conj_spQe m t
  interval_cases e
  · left
    refine ⟨A, by simpa using hα, fun t => ?_⟩
    apply (spQe K).injective
    rw [spQe_toRev, hα]
    simp only [pow_zero, mul_one, MulAut.mul_apply]
    rw [← spQe_fieldRev, hconj]
  · right
    refine ⟨A, by simpa using hα, fun t => ?_⟩
    apply (spQe K).injective
    rw [spQe_toRev, hα]
    simp only [pow_one, MulAut.mul_apply]
    rw [← spQe_tauRev, ← spQe_fieldRev, hconj]

theorem exists_preimage_of_maps {M : Type*} [Group M] [Finite M] (f : M ≃* M) (T : Subgroup M)
    (h : ∀ t ∈ T, f t ∈ T) : ∀ t' ∈ T, ∃ t ∈ T, f t = t' := by
  have hle : T.map f.toMonoidHom ≤ T := by
    rintro _ ⟨t, ht, rfl⟩
    exact h t ht
  have hcard : Nat.card T ≤ Nat.card (T.map f.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective f.injective]
  have heq : T.map f.toMonoidHom = T := Subgroup.eq_of_le_of_card_ge hle hcard
  intro t' ht'
  rw [← heq] at ht'
  obtain ⟨t, ht, rfl⟩ := ht'
  exact ⟨t, ht, rfl⟩

theorem mem_normalizer_of (g : ↥(spRev K) ≃* ↥(spRev K)) (hg : ∀ t ∈ Tsub p K, g t ∈ Tsub p K)
    {m : ↥(spRev K)} (hm : ∀ t ∈ Tsub p K, m * g t * m⁻¹ ∈ Tsub p K) :
    m ∈ Subgroup.normalizer (Tsub p K : Set ↥(spRev K)) := by
  have h1 : ∀ t' ∈ Tsub p K, m * t' * m⁻¹ ∈ Tsub p K := by
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := exists_preimage_of_maps g (Tsub p K) hg t' ht'
    exact hm t ht
  have h2 := exists_preimage_of_maps (MulAut.conj m) (Tsub p K) h1
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact h1 h
  · intro hh
    obtain ⟨t, ht, hth⟩ := h2 _ hh
    have : t = h := by
      have h3 : m * t * m⁻¹ = m * h * m⁻¹ := hth
      simpa using h3
    rw [← this]
    exact ht

omit [CharP K 2] in
theorem sigVec_pow (σ : K ≃+* K) : ∃ k : ℤ, ∀ v : D8Mod p K, sigVec σ v = v ^ k := by
  obtain ⟨k, hk⟩ := MonoidHom.map_cyclic (restrictRootsOfUnity σ p)
  refine ⟨k, fun v => ?_⟩
  refine Prod.ext ?_ ?_
  · exact hk v.1
  · exact hk v.2

omit [Finite K] [CharP K 2] in
theorem d8Act_diag_ne (γ : DihedralGroup 4) {z : rootsOfUnity p K} (hz : z ≠ 1) :
    (d8Act γ (z, z)).1 ≠ 1 ∧ (d8Act γ (z, z)).2 ≠ 1 := by
  rcases γ with i | i
  · have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl
    · rw [d8Act_r_zero]; exact ⟨hz, hz⟩
    · rw [d8Act_r_one]; simp [hz]
    · rw [d8Act_r_two]; simp [hz]
    · rw [d8Act_r_three]; simp [hz]
  · have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl
    · rw [d8Act_sr_zero]; simp [hz]
    · rw [d8Act_sr_one]; simp [hz]
    · rw [d8Act_sr_two]; simp [hz]
    · rw [d8Act_sr_three]; simp [hz]

omit [Finite K] [CharP K 2] in
theorem d8Act_axis (γ : DihedralGroup 4) (a : rootsOfUnity p K) :
    (d8Act γ (a, 1)).1 = 1 ∨ (d8Act γ (a, 1)).2 = 1 := by
  rcases γ with i | i
  · have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl
    · rw [d8Act_r_zero]; simp
    · rw [d8Act_r_one]; simp
    · rw [d8Act_r_two]; simp
    · rw [d8Act_r_three]; simp
  · have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl
    · rw [d8Act_sr_zero]; simp
    · rw [d8Act_sr_one]; simp
    · rw [d8Act_sr_two]; simp
    · rw [d8Act_sr_three]; simp

theorem ga_core (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (α : MulAut (StatedProj (StatedSp 2 K))) (hT : ∀ t ∈ Tsub p K, toRev α t ∈ Tsub p K) :
    (∃ (γ : DihedralGroup 4) (k : ℤ), ∀ v : D8Mod p K,
        toRev α (torC p K v) = torC p K (d8Act γ (v ^ k))) ↔
      ∃ (A : gsp 2 K) (σ : K ≃+* K), α = conjAut 2 K A * fieldAut 2 K σ := by
  classical
  obtain ⟨m, σ, hcase⟩ := exists_decomp α
  have hmemT : ∀ t ∈ Tsub p K, ∃ v : D8Mod p K, t = torC p K v := fun t ht =>
    ⟨(torT p K).symm ⟨t, ht⟩,
      (congrArg (fun x : ↥(Tsub p K) => (x : ↥(spRev K)))
        ((torT p K).apply_symm_apply ⟨t, ht⟩)).symm⟩
  rcases hcase with ⟨A, hα, hθ⟩ | ⟨A, hα, hθ⟩
  ·
    have hnorm : m ∈ Subgroup.normalizer (Tsub p K : Set ↥(spRev K)) := by
      refine mem_normalizer_of (fieldRev σ) (fun t ht => ?_) (fun t ht => ?_)
      · obtain ⟨v, rfl⟩ := hmemT t ht
        rw [fieldRev_torC]
        exact torC_mem _
      · rw [← hθ]
        exact hT t ht
    obtain ⟨γ, hγ⟩ := exists_weyl hp hp2 hζ hnorm
    obtain ⟨k, hk⟩ := sigVec_pow (K := K) (p := p) σ
    refine iff_of_true ⟨γ, k, fun v => ?_⟩ ⟨A, σ, hα⟩
    rw [hθ, fieldRev_torC, hγ, hk]
  ·
    have hnorm : m ∈ Subgroup.normalizer (Tsub p K : Set ↥(spRev K)) := by
      refine mem_normalizer_of (tauRev.trans (fieldRev σ)) (fun t ht => ?_) (fun t ht => ?_)
      · obtain ⟨v, rfl⟩ := hmemT t ht
        show fieldRev σ (tauRev (torC p K v)) ∈ Tsub p K
        rw [tauRev_torC, fieldRev_torC]
        exact torC_mem _
      · have := hT t ht
        rw [hθ] at this
        exact this
    obtain ⟨γ, hγ⟩ := exists_weyl hp hp2 hζ hnorm
    refine iff_of_false ?_ ?_
    · rintro ⟨γ', k', hk'⟩
      obtain ⟨ζ, hζ⟩ := hζ
      have hζp : ζ ^ p = 1 := hζ.pow_eq_one
      let z₀ : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζp⟩
      have hz₀ : z₀ ≠ 1 := by
        intro h
        have h0 : ζ = 1 := congrArg Subtype.val h
        rw [h0] at hζ
        have := hζ.eq_orderOf
        rw [orderOf_one] at this
        exact hp.ne_one this
      have h1 := hk' (z₀, 1)
      rw [hθ, tauRev_torC, fieldRev_torC, hγ] at h1
      have h2 := torC_injective h1
      have hM : Mvec p K (z₀, 1) = (z₀, z₀) := by
        refine Prod.ext ?_ ?_ <;> simp [Mvec]
      have e1 : ((z₀, 1) : D8Mod p K) ^ k' = (z₀ ^ k', 1) := by
        refine Prod.ext ?_ ?_ <;> simp
      have e2 : sigVec σ ((z₀, z₀) : D8Mod p K) =
          (restrictRootsOfUnity σ p z₀, restrictRootsOfUnity σ p z₀) := rfl
      rw [hM, e1, e2] at h2
      have hz : restrictRootsOfUnity σ p z₀ ≠ 1 := by
        intro h
        have h' : Units.map (σ : K →* K) (z₀ : Kˣ) = 1 := congrArg Subtype.val h
        apply hz₀
        apply Subtype.ext
        show (z₀ : Kˣ) = 1
        apply Units.map_injective (f := (σ : K →* K)) σ.injective
        rw [map_one]
        exact h'
      obtain ⟨hl1, hl2⟩ := d8Act_diag_ne γ hz
      rcases d8Act_axis γ' (z₀ ^ k') with h | h
      · exact hl1 ((congrArg Prod.fst h2).trans h)
      · exact hl2 ((congrArg Prod.snd h2).trans h)
    · rintro ⟨A', σ', hα'⟩
      apply tauAut_not_mem_E (F := K)
      have hE1 : conjAut 2 K A * fieldAut 2 K σ ∈ spSemilinearAutGroup 2 K :=
        mem_spSemilinearAutGroup_iff.2 ⟨A, σ, rfl⟩
      have hE2 : conjAut 2 K A' * fieldAut 2 K σ' ∈ spSemilinearAutGroup 2 K :=
        mem_spSemilinearAutGroup_iff.2 ⟨A', σ', rfl⟩
      have : (tauAut : MulAut (StatedProj (StatedSp 2 K))) =
          (conjAut 2 K A * fieldAut 2 K σ)⁻¹ * (conjAut 2 K A' * fieldAut 2 K σ') := by
        rw [← hα', hα]
        group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hE1) hE2

end CFSG.RankThree.PartOne.SP4C
