module

public import CFSG.Quasithin.EmptyFaithful.S146zRSL2Set

public section

namespace CFSG.Quasithin.S146zU.UD3

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Inf

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G}

theorem inf_le_pCoreOf (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ 5) (hmax : PMaximal T M 5)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    ∀ x ∈ T, x ∈ conjClosure (oTwoUpper H) (mcOf T) → x ∈ pCoreOf 2 H := by
  classical
  have hF4 : 4 ≤ Nat.card (GaloisField 2 4) := by
    rw [SBc16.card_galoisField16]; norm_num
  have hpF : 5 ∣ Nat.card (GaloisField 2 4) - 1 := by
    rw [SBc16.card_galoisField16]; norm_num
  obtain ⟨hsG, ⟨e1⟩, hF⟩ := q_sl2_setup h36 hlist iS S hred hmax hK₁ hsT hsN hKz hF4 hpF e
  have hKle := q_hatK_le hK₁ hsG hKz
  have hSyl := q_hatT_sylow S
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans (S.le_mcOf hred.isHTM)
  have hK₂ : conjSub s K₁ ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hK₁ hsG
  intro x hxT hxK
  have hxG : x ∈ mcOf T := hTG hxT
  refine q_mem_pCoreOf_of_mem S hred (Uh := imageOTwoQuot (mcOf T) T ⊓
      (imageOTwoQuot (mcOf T) K₁ ⊔ imageOTwoQuot (mcOf T) (conjSub s K₁)))
    hSyl.2.1.to_inf_left (q_hat_normalizes_U_sl2 S hred hF hF4 e1.symm hKle) hxT hxG ?_
  refine ⟨⟨_, Subgroup.mem_subgroupOf.mpr hxT, rfl⟩, ?_⟩
  rw [← q_image_sup (le_of_mem_cComp hK₁) (le_of_mem_cComp hK₂), ← hKz]
  exact ⟨⟨x, hxG⟩, Subgroup.mem_subgroupOf.mpr hxK, rfl⟩

theorem commutator_mem_pCoreOf (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ 5) (hmax : PMaximal T M 5)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    ∀ k₁ ∈ K₁, ∀ k₂ ∈ conjSub s K₁, k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ pCoreOf 2 (mcOf T) := by
  classical
  have hF4 : 4 ≤ Nat.card (GaloisField 2 4) := by
    rw [SBc16.card_galoisField16]; norm_num
  have hpF : 5 ∣ Nat.card (GaloisField 2 4) - 1 := by
    rw [SBc16.card_galoisField16]; norm_num
  obtain ⟨hsG, -, hF⟩ := q_sl2_setup h36 hlist iS S hred hmax hK₁ hsT hsN hKz hF4 hpF e
  have hK₂ : conjSub s K₁ ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hK₁ hsG
  intro k₁ hk₁ k₂ hk₂
  have hk₁G : k₁ ∈ mcOf T := le_of_mem_cComp hK₁ hk₁
  have hk₂G : k₂ ∈ mcOf T := le_of_mem_cComp hK₂ hk₂
  have hcomm := hF.comm (qPi (mcOf T) ⟨k₁, hk₁G⟩)
    ⟨⟨k₁, hk₁G⟩, Subgroup.mem_subgroupOf.mpr hk₁, rfl⟩ (qPi (mcOf T) ⟨k₂, hk₂G⟩)
    ⟨⟨k₂, hk₂G⟩, Subgroup.mem_subgroupOf.mpr hk₂, rfl⟩
  have h1 : qPi (mcOf T) ((⟨k₁, hk₁G⟩ : ↥(mcOf T)) * ⟨k₂, hk₂G⟩ * (⟨k₁, hk₁G⟩ : ↥(mcOf T))⁻¹ *
      (⟨k₂, hk₂G⟩ : ↥(mcOf T))⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  exact Subgroup.mem_map.mpr ⟨_, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

theorem isSylowTwoOf_inf_K₁ (S : Setting146 G T M) (hred : IsRedCE T M H PQ 5)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hK₂ : conjSub s K₁ ∈ cComp (mcOf T))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁) :
    IsSylowTwoOf (T ⊓ K₁) K₁ := by
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans (S.le_mcOf hred.isHTM)
  have hT : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_le151 S.hyp.sylow hTG
  have hKzG : conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T := SBc13.kz_le_mcOf S hred
  have h1 : IsSylowTwoOf (T ⊓ conjClosure (oTwoUpper H) (mcOf T))
      (conjClosure (oTwoUpper H) (mcOf T)) :=
    B6.isSylowTwoOf_inf_normal hT hKzG (le_normalizer_conjClosure _ _)
  have hK₁Kz : K₁ ≤ conjClosure (oTwoUpper H) (mcOf T) := hKz ▸ le_sup_left
  have hKzn : conjClosure (oTwoUpper H) (mcOf T) ≤ Subgroup.normalizer (K₁ : Set G) :=
    hKz ▸ SBc16.sup_le_normalizer_of_mem_cComp hK₁ hK₂
  have h2 := B6.isSylowTwoOf_inf_normal h1 hK₁Kz hKzn
  rwa [inf_assoc, inf_eq_right.mpr hK₁Kz] at h2

end Inf

section Invol

theorem exists_involution_of_surjective {K Y : Type*} [Group K] [Group Y] [Finite Y]
    (f : K →* Y) (hf : Function.Surjective f) (hY : 2 ∣ Nat.card Y) {A : Subgroup K}
    (hA : ¬ 2 ∣ A.index) (hA2 : ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k = 1) :
    ∃ a ∈ A, f a ≠ 1 ∧ f a ^ 2 = 1 := by
  classical
  have h1 : ∃ a ∈ A, f a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ f.ker := fun a ha => MonoidHom.mem_ker.mpr (hcon a ha)
    have h2 : f.ker.index ∣ A.index := Subgroup.index_dvd_of_le hle
    have h3 : f.ker.index = Nat.card Y := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective f hf, Subgroup.card_top]
    exact hA ((h3 ▸ hY).trans h2)
  obtain ⟨a₀, ha₀, hfa₀⟩ := h1
  obtain ⟨k, hk⟩ := hA2 a₀ ha₀
  have hord : orderOf (f a₀) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
  obtain ⟨j, -, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exfalso
      apply hfa₀
      rw [h0, pow_zero] at hjo
      exact orderOf_eq_one_iff.mp hjo
    · exact h0
  refine ⟨a₀ ^ 2 ^ (j - 1), A.pow_mem ha₀ _, ?_, ?_⟩
  · rw [map_pow]
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hjo] at h1
    have h2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h1
    omega
  · have e2 : (2 : ℕ) ^ (j - 1) * 2 = orderOf (f a₀) := by
      rw [hjo, ← pow_succ, Nat.sub_add_cancel hj1]
    rw [map_pow, ← pow_mul, e2]
    exact pow_orderOf_eq_one _

end Invol

end CFSG.Quasithin.S146zU.UD3
