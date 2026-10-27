module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

private theorem he42y_pow_three_of_pow_nine (p : GL2) (h : p ^ 9 = 1) : p ^ 3 = 1 := by
  have h6 : p ^ 6 = 1 := by
    have := pow_card_eq_one' (x := p) (G := GL2)
    rwa [CFSG.Quasithin.A94.HeJ.card_GL2] at this
  have h' := (pow_gcd_eq_one (a := p) (m := 9) (n := 6)).mpr ⟨h, h6⟩
  simpa using h'

theorem HeSetup.stepY (S : HeSetup G) : ∃ y₁ y₂ : G, YSpec S y₁ y₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hg3 : S.g ^ 3 = 1 := S.hD.g_pow_three S.hxN S.hxa S.hx3
  have hg1 : S.g ≠ 1 := S.hD.g_ne_one S.hxN S.hxa S.hx3
  obtain ⟨P, hP⟩ : ∃ P : Subgroup ↥S.N, Nat.card P = 3 ^ 2 :=
    Sylow.exists_subgroup_card_pow_prime 3 (by rw [S.hD.cardN]; norm_num)
  have hPcomm : ∀ a b : P, a * b = b * a :=
    fun a b => (IsPGroup.isMulCommutative_of_card_eq_prime_sq hP).is_comm.comm a b
  have hker : ∀ z : ↥S.N, z ∈ P → S.rho z = 1 → z = 1 := by
    intro z hzP hz
    have hzJ : (z : G) ∈ S.A ⊔ S.A' := by
      have hk : z ∈ (S.hD.hT.rho S.N S.hD.hK.norm).ker := MonoidHom.mem_ker.mpr hz
      rw [S.hD.hT.ker_rho S.hD.hK, Subgroup.mem_subgroupOf] at hk
      exact hk
    have h256 : orderOf (z : G) ∣ 256 := by
      have h := orderOf_dvd_natCard (⟨(z : G), hzJ⟩ : ↥(S.A ⊔ S.A'))
      rw [S.hD.cardJ, Subgroup.orderOf_mk] at h
      exact h
    have h9 : orderOf (z : G) ∣ 9 := by
      have h := orderOf_dvd_natCard (⟨z, hzP⟩ : ↥P)
      rw [hP, Subgroup.orderOf_mk] at h
      rw [Subgroup.orderOf_coe]
      norm_num at h
      exact h
    have h1 : orderOf (z : G) = 1 := by
      have h := Nat.dvd_gcd h256 h9
      rw [show Nat.gcd 256 9 = 1 by norm_num] at h
      exact Nat.dvd_one.mp h
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  obtain ⟨φ, hφ⟩ : ∃ φ : P →* GL2 × GL2, ∀ z : P, φ z = S.rho (z : ↥S.N) :=
    ⟨S.rho.comp P.subtype, fun z => rfl⟩
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [hφ] at ha
    exact Subtype.ext (hker a.1 a.2 ha)
  obtain ⟨T, hT⟩ : ∃ T : Finset (GL2 × GL2),
      T = Finset.univ.filter (fun q : GL2 × GL2 => q.1 ^ 3 = 1 ∧ q.2 ^ 3 = 1) := ⟨_, rfl⟩
  have hTcard : T.card = 9 := by
    rw [hT]
    decide +kernel
  have hTmem : ∀ q : GL2 × GL2, q ∈ T ↔ q.1 ^ 3 = 1 ∧ q.2 ^ 3 = 1 := by
    intro q
    rw [hT, Finset.mem_filter]
    simp
  have hrange : (Set.range φ).ncard = 9 := by
    have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hφinj, Set.ncard_univ, hP, h9]
  have hsub : Set.range φ ⊆ (T : Set (GL2 × GL2)) := by
    rintro _ ⟨z, rfl⟩
    rw [Finset.mem_coe, hTmem]
    have hz9P : z ^ 9 = 1 := by
      have h := orderOf_dvd_natCard z
      rw [hP] at h
      norm_num at h
      exact orderOf_dvd_iff_pow_eq_one.mp h
    have hz9 : (z : ↥S.N) ^ 9 = 1 := by
      have := congrArg (fun q : P => (q : ↥S.N)) hz9P
      simpa using this
    have hφ9 : φ z ^ 9 = 1 := by
      rw [hφ, ← map_pow, hz9, map_one]
    have h1 : (φ z).1 ^ 9 = 1 := by simpa using congrArg Prod.fst hφ9
    have h2 : (φ z).2 ^ 9 = 1 := by simpa using congrArg Prod.snd hφ9
    exact ⟨he42y_pow_three_of_pow_nine _ h1, he42y_pow_three_of_pow_nine _ h2⟩
  have heq : Set.range φ = (T : Set (GL2 × GL2)) :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [Set.ncard_coe_finset, hTcard, hrange]))
  obtain ⟨z₁, hz₁⟩ : (S.g, (1 : GL2)) ∈ Set.range φ := by
    rw [heq, Finset.mem_coe, hTmem]
    exact ⟨hg3, one_pow 3⟩
  obtain ⟨z₂, hz₂⟩ : ((1 : GL2), S.g) ∈ Set.range φ := by
    rw [heq, Finset.mem_coe, hTmem]
    exact ⟨one_pow 3, hg3⟩
  have hord : ∀ z : P, φ z ^ 3 = 1 → φ z ≠ 1 → orderOf ((z : ↥S.N) : G) = 3 := by
    intro z h3 hne
    have hr : S.rho ((z : ↥S.N) ^ 3) = 1 := by
      rw [map_pow, ← hφ]
      exact h3
    have hz3 : (z : ↥S.N) ^ 3 = 1 := hker _ (P.pow_mem z.2 3) hr
    have hne' : (z : ↥S.N) ≠ 1 := by
      intro h
      apply hne
      rw [hφ, h, map_one]
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hz3 hne'
  have hz₁N : S.rho (z₁ : ↥S.N) = (S.g, 1) := (hφ z₁).symm.trans hz₁
  have hz₂N : S.rho (z₂ : ↥S.N) = (1, S.g) := (hφ z₂).symm.trans hz₂
  refine ⟨((z₁ : ↥S.N) : G), ((z₂ : ↥S.N) : G), ?_⟩
  refine ⟨(z₁ : ↥S.N).2, (z₂ : ↥S.N).2, ?_, ?_, ?_, ?_, ?_⟩
  · apply hord z₁
    · rw [hz₁]
      exact Prod.ext (by simpa using hg3) (by simp)
    · rw [hz₁]
      intro h
      exact hg1 (congrArg Prod.fst h)
  · apply hord z₂
    · rw [hz₂]
      exact Prod.ext (by simp) (by simpa using hg3)
    · rw [hz₂]
      intro h
      exact hg1 (congrArg Prod.snd h)
  · have h := congrArg (fun q : P => ((q : ↥S.N) : G)) (hPcomm z₁ z₂)
    simpa using h
  · rw [S.rhoG_of_mem (z₁ : ↥S.N).2]
    exact hz₁N
  · rw [S.rhoG_of_mem (z₂ : ↥S.N).2]
    exact hz₂N

end CFSG.Quasithin.A94.He42
