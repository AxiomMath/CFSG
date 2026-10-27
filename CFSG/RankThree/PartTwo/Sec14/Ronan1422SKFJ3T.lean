module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFJ3S6
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

theorem kf1422_mem_normalizer_of_map {S G : Type*} [Group S] [Group G] (ι : S →* G)
    (hι : Function.Injective ι) (A : Subgroup S) (t : S)
    (ht : ι t ∈ Subgroup.normalizer ((A.map ι : Subgroup G) : Set G)) :
    t ∈ Subgroup.normalizer (A : Set S) := by
  rw [Subgroup.mem_normalizer_iff] at ht ⊢
  intro n
  have h := ht (ι n)
  have e : ι t * ι n * (ι t)⁻¹ = ι (t * n * t⁻¹) := by simp only [map_mul, map_inv]
  rw [e] at h
  simpa only [SetLike.mem_coe, Subgroup.mem_map_iff_mem hι] using h

theorem kf1422_map_le_centralizer {S G : Type*} [Group S] [Group G] (ι : S →* G)
    {K : Subgroup S} {c : S} (hK : K ≤ Subgroup.centralizer ({c} : Set S)) :
    K.map ι ≤ Subgroup.centralizer ({ι c} : Set G) := by
  rintro _ ⟨k, hk, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  have hkc : c * k = k * c := Subgroup.mem_centralizer_iff.mp (hK hk) c (Set.mem_singleton c)
  rw [← map_mul, ← map_mul, hkc]

theorem kf1422_normalizerMonoidHom_val {S : Type*} [Group S] (K : Subgroup S)
    (n : Subgroup.normalizer (K : Set S)) (k : K) :
    ((K.normalizerMonoidHom n k : K) : S) = (n : S) * (k : S) * (n : S)⁻¹ :=
  rfl

theorem kf1422_sq_mem_of_index_le_two {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (hne : H.index ≠ 0) (hle : H.index ≤ 2) (g : G) : g ^ 2 ∈ H := by
  have hpow : g ^ H.index ∈ H := Subgroup.pow_index_mem H g
  rcases (show H.index = 1 ∨ H.index = 2 by omega) with h1 | h1
  · rw [h1, pow_one] at hpow
    exact H.pow_mem hpow 2
  · rw [h1] at hpow
    exact hpow

theorem kf1422_inner_of_pow_three
    (β : MulAut ↥CFSG.Sporadic.Schreier.j3P) (hβ : β ^ 3 = 1) :
    ∃ y : ↥CFSG.Sporadic.Schreier.j3P, β = MulAut.conj y := by
  obtain ⟨_, -, -, -, hcard⟩ :=
    CFSG.Sporadic.SmallOddCore.ctuc_j3_full_automorphism_permutation_model
  have hfin : Finite (MulAut ↥CFSG.Sporadic.Schreier.j3P) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hne : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥CFSG.Sporadic.Schreier.j3P).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hle : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥CFSG.Sporadic.Schreier.j3P).index ≤ 2 := by
    rw [Subgroup.index_eq_card]
    exact CFSG.Sporadic.SmallOddCore.j3_outer_card_le
  have hsq := kf1422_sq_mem_of_index_le_two _ hne hle β
  have hβeq : β = (β ^ 2)⁻¹ := by
    calc β = β ^ 3 * (β ^ 2)⁻¹ := by group
      _ = (β ^ 2)⁻¹ := by rw [hβ, one_mul]
  have hβin : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥CFSG.Sporadic.Schreier.j3P := by
    rw [hβeq]
    exact Subgroup.inv_mem _ hsq
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hβin
  exact ⟨y, hy.symm⟩

theorem kf1422_exists_embedding {S : Type*} [Group S] (φ : S ≃* ↥CFSG.Sporadic.Schreier.j3P) :
    ∃ ι : S →* Equiv.Perm (Fin 6156), Function.Injective ι ∧
      (∀ s : S, ι s ∈ CFSG.Sporadic.Schreier.j3P) ∧
      ∀ x ∈ CFSG.Sporadic.Schreier.j3P, ∃ s : S, ι s = x :=
  ⟨CFSG.Sporadic.Schreier.j3P.subtype.comp φ.toMonoidHom,
    fun a b hab => φ.injective (Subtype.ext hab),
    fun s => (φ s).2,
    fun x hx => ⟨φ.symm ⟨x, hx⟩, congrArg Subtype.val (φ.apply_symm_apply ⟨x, hx⟩)⟩⟩

theorem kf1422_of_embedding {S : Type*} [Group S] (ι : S →* Equiv.Perm (Fin 6156))
    (hι : Function.Injective ι) (hιP : ∀ s : S, ι s ∈ CFSG.Sporadic.Schreier.j3P)
    (hιS : ∀ x ∈ CFSG.Sporadic.Schreier.j3P, ∃ s : S, ι s = x) (h : J3PermConfig)
    (E K : Subgroup S) (c : S) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 27) (hcE : c ∈ E) (hc1 : c ≠ 1)
    (hKc : K ≤ Subgroup.centralizer ({c} : Set S))
    (ψ : Nonempty (↥K ≃* alternatingGroup (Fin 6)))
    (hEK : Nat.card (E ⊓ K : Subgroup S) = 9) :
    ∃ t : S, ∃ ht : t ∈ Subgroup.normalizer (K : Set S),
      t ∈ Subgroup.normalizer (E : Set S) ∧
      t ∈ Subgroup.normalizer (Subgroup.zpowers c : Set S) ∧
      ¬ IsS6Type ↥K (K.normalizerMonoidHom ⟨t, ht⟩) := by
  have hE'P : E.map ι ≤ CFSG.Sporadic.Schreier.j3P := by
    rintro _ ⟨x, -, rfl⟩
    exact hιP x
  have hK'P : K.map ι ≤ CFSG.Sporadic.Schreier.j3P := by
    rintro _ ⟨x, -, rfl⟩
    exact hιP x
  have hE' : CFSG.Assembly.IsElemAbelian 3 (E.map ι) := CFSG.Open.IsElemAbelian.map hE ι
  have hE'card : Nat.card (E.map ι) = 27 := by
    rw [Subgroup.card_map_of_injective hι, hEcard]
  have hc'mem : ι c ∈ E.map ι := Subgroup.mem_map_of_mem ι hcE
  have hc'ne : ι c ≠ 1 := fun h1 => hc1 (hι (h1.trans (map_one ι).symm))
  have hK'cent : K.map ι ≤ Subgroup.centralizer ({ι c} : Set (Equiv.Perm (Fin 6156))) :=
    kf1422_map_le_centralizer ι hKc
  obtain ⟨ψ0⟩ := ψ
  have hK'A6 : Nonempty (↥(K.map ι) ≃* alternatingGroup (Fin 6)) :=
    ⟨(Subgroup.equivMapOfInjective K ι hι).symm.trans ψ0⟩
  have hE'K' : Nat.card (E.map ι ⊓ K.map ι : Subgroup (Equiv.Perm (Fin 6156))) = 9 := by
    rw [← Subgroup.map_inf_eq E K ι hι, Subgroup.card_map_of_injective hι, hEK]
  obtain ⟨t', ht'P, ht'K, ht'E, ht'c, ht'pow⟩ :=
    h (E.map ι) (K.map ι) (ι c) hE'P hK'P hE' hE'card hc'mem hc'ne hK'cent hK'A6 hE'K'
  obtain ⟨s, hs⟩ := hιS t' ht'P
  have hK : s ∈ Subgroup.normalizer (K : Set S) :=
    kf1422_mem_normalizer_of_map ι hι K s (by rw [hs]; exact ht'K)
  have hEN : s ∈ Subgroup.normalizer (E : Set S) :=
    kf1422_mem_normalizer_of_map ι hι E s (by rw [hs]; exact ht'E)
  have hZ : s ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup S) : Set S) :=
    kf1422_mem_normalizer_of_map ι hι _ s (by rw [hs, MonoidHom.map_zpowers]; exact ht'c)
  refine ⟨s, hK, hEN, hZ, ?_⟩
  have hBcard : Nat.card ((E ⊓ K).subgroupOf K) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : E ⊓ K ≤ K)).toEquiv).trans hEK
  have hB3 : ∀ b ∈ (E ⊓ K).subgroupOf K, b ^ 3 = 1 := by
    intro b hb
    have hbE : (b : S) ∈ E := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hb)).1
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 _ hbE
  have hpow : ∀ (n : ℕ) (k : K),
      ((K.normalizerMonoidHom ⟨s, hK⟩ ^ n) k : S) = s ^ n * (k : S) * (s ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [pow_succ (K.normalizerMonoidHom ⟨s, hK⟩) n, MulAut.mul_apply, ih,
        kf1422_normalizerMonoidHom_val]
      dsimp only
      group
  have hαB : ∀ b ∈ (E ⊓ K).subgroupOf K,
      K.normalizerMonoidHom ⟨s, hK⟩ b ∈ (E ⊓ K).subgroupOf K := by
    intro b hb
    obtain ⟨hbE, hbK⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hb)
    rw [Subgroup.mem_subgroupOf, kf1422_normalizerMonoidHom_val, Subgroup.mem_inf]
    exact ⟨(Subgroup.mem_normalizer_iff.mp hEN (b : S)).mp hbE,
      (Subgroup.mem_normalizer_iff.mp hK (b : S)).mp hbK⟩
  have h4 : ∀ b ∈ (E ⊓ K).subgroupOf K, (K.normalizerMonoidHom ⟨s, hK⟩ ^ 4) b = b⁻¹ := by
    intro b hb
    have hbEK : (b : S) ∈ E ⊓ K := Subgroup.mem_subgroupOf.mp hb
    have hmem : ι (b : S) ∈ E.map ι ⊓ K.map ι := by
      rw [← Subgroup.map_inf_eq E K ι hι]
      exact Subgroup.mem_map_of_mem ι hbEK
    have key := ht'pow (ι (b : S)) hmem
    apply Subtype.ext
    apply hι
    rw [hpow 4 b, map_mul, map_mul, map_inv, map_pow, hs, Subgroup.coe_inv, map_inv]
    exact key
  exact not_isS6Type_of_pow_four_inv hBcard hB3 hαB h4

theorem kf1422J3_of
    (h : J3PermConfig) :
    KF1422J3 := by
  intro S _ _ hS
  obtain ⟨e⟩ := hS
  obtain ⟨φ⟩ : Nonempty (S ≃* ↥CFSG.Sporadic.Schreier.j3P) :=
    ⟨e.trans CFSG.Sporadic.Schreier.j3PermEquiv⟩
  have hcardS : Nat.card S = 50232960 := by
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Schreier.card_j3P]
  obtain ⟨ι, hι, hιP, hιS⟩ := kf1422_exists_embedding φ
  refine ⟨hcardS, ?_, ?_⟩
  · intro α hα
    obtain ⟨y, hy⟩ := kf1422_inner_of_pow_three (MulAut.congr φ α)
      (by rw [← map_pow, hα, map_one])
    refine ⟨φ.symm y, ?_⟩
    apply (MulAut.congr φ).injective
    rw [hy, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
  · intro E hE hEcard c hcE hc1 K hKc _hKN ψ hEK
    exact kf1422_of_embedding ι hι hιP hιS h E K c hE hEcard hcE hc1 hKc ψ hEK

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
