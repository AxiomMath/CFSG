module

public import CFSG.RankThree.PartTwo.Sec11.Item116EiiO
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedSylowConjugacy
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ElementaryCore
public import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
public import CFSG.RankThree.PartTwo.Sec11.Item116ResidueT

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem exists_invariant_sylow_swap (h : ResidueConfig G A c L a R Y d) {n : G}
    (hnW : n ∈ Subgroup.normalizer (A : Set G)) (hna : n * a * n⁻¹ = a⁻¹) :
    ∃ (S : Subgroup G) (y : G), S ≤ thetaCent a ∧ IsPGroup 2 S ∧
      ¬ 2 ∣ S.relIndex (thetaCent a) ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      y ∈ thetaCent a ∧ (∀ x ∈ A, y * x = x * y) ∧
      y⁻¹ * n ∈ Subgroup.normalizer (S : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have haA := h.a_mem
  have hA3 : IsPGroup 3 A :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_isPGroup 3 A hAe
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) :=
    CFSG.RankThreeEvenClassification.Helpers.commutative_plane_le_element_centralizer A hAe.1 a haA
  have hCθ : Subgroup.normalizer ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((thetaCent a : Subgroup G) : Set G) :=
    Sec6.normalizer_le_normalizer_theta _
  have hAθ : A ≤ Subgroup.normalizer ((thetaCent a : Subgroup G) : Set G) :=
    hAC.trans (Subgroup.le_normalizer.trans hCθ)
  have hθ3 : ¬ 3 ∣ Nat.card (thetaCent a) := not_three_dvd_card_inSubgroup_theta _
  have hna' : n * a * n⁻¹ ∈ Subgroup.zpowers a := by
    rw [hna]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hna1 : n * a * n⁻¹ ≠ 1 := fun h1 => h.a_ne_one (by
    calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  have hnC : n ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
    refine GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq ?_
    rw [map_centralizer_singleton, MulAut.conj_apply]
    exact TheoremO.centralizer_eq_of_zpowers_eq
      (TheoremO.zpowers_eq_of_mem_of_ne_one (hexp a haA) hna' hna1)
  have hnθ : n ∈ Subgroup.normalizer ((thetaCent a : Subgroup G) : Set G) := hCθ hnC
  have hconjA : ∀ x ∈ A, n⁻¹ * x * n ∈ A := by
    intro x hx
    have hn' : n⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hnW
    have hiff := Subgroup.mem_normalizer_iff.mp hn' x
    rw [inv_inv] at hiff
    exact hiff.mp hx
  obtain ⟨S₀, hS₀A⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      3 Nat.prime_three A (thetaCent a) hA3 hθ3 hAθ 2 Nat.prime_two
  obtain ⟨f, hf_surj, hf⟩ : ∃ f : thetaCent a →* thetaCent a, Function.Surjective f ∧
      ∀ x : thetaCent a, ((f x : thetaCent a) : G) = n * (x : G) * n⁻¹ :=
    ⟨((thetaCent a).normalizerMonoidHom ⟨n, hnθ⟩).toMonoidHom,
      ((thetaCent a).normalizerMonoidHom ⟨n, hnθ⟩).surjective,
      fun x => by simp [Subgroup.normalizerMonoidHom_apply_apply_coe]⟩
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Sylow 2 (thetaCent a),
      (S₁ : Subgroup (thetaCent a)) = (S₀ : Subgroup (thetaCent a)).map f :=
    ⟨S₀.mapSurjective hf_surj, Sylow.coe_mapSurjective hf_surj S₀⟩
  have hS₁G : (S₁ : Subgroup (thetaCent a)).map (thetaCent a).subtype =
      ((S₀ : Subgroup (thetaCent a)).map (thetaCent a).subtype).map
        (MulAut.conj n).toMonoidHom := by
    rw [hS₁, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [hf]
  have hS₁A : A ≤ Subgroup.normalizer
      (((S₁ : Subgroup (thetaCent a)).map (thetaCent a).subtype : Subgroup G) : Set G) := by
    rw [hS₁G]
    intro x hx
    have hm : n⁻¹ * x * n ∈ A := hconjA x hx
    have hinv : ((S₀ : Subgroup (thetaCent a)).map (thetaCent a).subtype).map
        (MulAut.conj (n⁻¹ * x * n)).toMonoidHom =
        (S₀ : Subgroup (thetaCent a)).map (thetaCent a).subtype :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hS₀A hm)
    have key : (((S₀ : Subgroup (thetaCent a)).map (thetaCent a).subtype).map
        (MulAut.conj n).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        ((S₀ : Subgroup (thetaCent a)).map (thetaCent a).subtype).map
          (MulAut.conj n).toMonoidHom := by
      rw [← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul _ x n,
        show x * n = n * (n⁻¹ * x * n) by group,
        CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul _ n (n⁻¹ * x * n), hinv]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr key
  obtain ⟨y, hy, hyconj⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_centralizing_conjugator_of_normalized_sylows
      3 Nat.prime_three 2 Nat.prime_two A (thetaCent a) hA3 hθ3 hAθ S₀ S₁ hS₀A hS₁A
  set S : Subgroup G := (S₀ : Subgroup (thetaCent a)).map (thetaCent a).subtype with hSdef
  refine ⟨S, y, Subgroup.map_subtype_le _, S₀.isPGroup'.map _, ?_, hS₀A,
    (Subgroup.mem_inf.mp hy).1, ?_, ?_⟩
  · have hrel : S.relIndex (thetaCent a) = (S₀ : Subgroup (thetaCent a)).index := by
      rw [hSdef, Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (thetaCent a).subtype_injective]
    rw [hrel]
    exact S₀.not_dvd_index
  · intro x hx
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2) x hx).symm
  · have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext g
      simp
    have hone : S.map (MulAut.conj (1 : G)).toMonoidHom = S := by
      rw [hid, Subgroup.map_id]
    have hfin : S.map (MulAut.conj (y⁻¹ * n)).toMonoidHom = S := by
      rw [CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul S y⁻¹ n, ← hS₁G, ← hyconj,
        ← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul S y⁻¹ y, inv_mul_cancel, hone]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfin

end Certified

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem exists_not_centralize_d (hP2b : Item116P2b) (hP2c : Item116P2c) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G)
    (hD8 : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c))
    {n' : G} (hnW : n' ∈ Subgroup.normalizer (A : Set G))
    (hnc : n' * c * n'⁻¹ ∈ Subgroup.zpowers d) (hnd : n' * d * n'⁻¹ ∈ Subgroup.zpowers c)
    (hna : n' * a * n'⁻¹ = a⁻¹) {S : Subgroup G} (hSθ : S ≤ thetaCent a) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex (thetaCent a)) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hn'S : n' ∈ Subgroup.normalizer (S : Set G)) :
    ∃ s ∈ S, d * s * d⁻¹ ≠ s := by
  by_contra! hcon
  have hθC : thetaCent a ≤ Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le _
  have hSC : S ≤ Subgroup.centralizer ({a} : Set G) := hSθ.trans hθC
  have hSfus : CFSG.Open.fusionIsSylowIn 2 S (thetaCent a) := by
    unfold CFSG.Open.fusionIsSylowIn
    refine ⟨hSθ, hS2, fun P hPθ hP2 hSP => ?_⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmul := Subgroup.relIndex_mul_relIndex S P (thetaCent a) hSP hPθ
    have hdvdθ : S.relIndex P ∣ S.relIndex (thetaCent a) :=
      ⟨P.relIndex (thetaCent a), hmul.symm⟩
    have hodd : ¬ 2 ∣ S.relIndex P := fun h2 => hSidx (dvd_trans h2 hdvdθ)
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP2
    have hdvdP : S.relIndex P ∣ 2 ^ m := by
      rw [← hm]
      exact Subgroup.relIndex_dvd_card (H := S) (K := P)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdP
    have hrel : S.relIndex P = 1 := by
      rcases k with _ | k
      · simpa using hk
      · exact absurd (show 2 ∣ S.relIndex P by
          rw [hk]
          exact dvd_pow_self 2 (Nat.succ_ne_zero k)) hodd
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel) hSP
  have hSA := not_Eii hP2b hP2c h45 (h.toSec11Std hT) h.inf_eq_zpowers h.normalizer_le
    h.isIrreducibleOn h.isSylowOf_top h.not_mem_zpowers hD8 hnW hnc hnd hna hSfus
  have haZ : a ∈ Subgroup.centralizer (S : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mp (hSC hs)
  have hdZ : d ∈ Subgroup.centralizer (S : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun s hs => (mul_inv_eq_iff_eq_mul.mp (hcon s hs)).symm
  have hc3 : c ^ 3 = 1 := (h.mem_partTwoF.1.2) c h.mem_A
  have hd1 : d ≠ 1 := fun h1 => h.not_mem_zpowers (by rw [h1]; exact Subgroup.one_mem _)
  have he1 : n' * d * n'⁻¹ ≠ 1 := by
    intro h1
    apply hd1
    calc d = n'⁻¹ * (n' * d * n'⁻¹) * n' := by group
      _ = 1 := by rw [h1]; group
  have hze : Subgroup.zpowers (n' * d * n'⁻¹) = Subgroup.zpowers c :=
    TheoremO.zpowers_eq_of_mem_of_ne_one hc3 hnd he1
  have hecent : ∀ s ∈ S, s * (n' * d * n'⁻¹) = (n' * d * n'⁻¹) * s := by
    intro s hs
    have ht : n'⁻¹ * s * n' ∈ S := by
      refine (Subgroup.mem_set_normalizer_iff.mp hn'S (n'⁻¹ * s * n')).mpr ?_
      rw [show n' * (n'⁻¹ * s * n') * n'⁻¹ = s by group]
      exact hs
    have hdt' : d * (n'⁻¹ * s * n') = (n'⁻¹ * s * n') * d :=
      mul_inv_eq_iff_eq_mul.mp (hcon _ ht)
    calc s * (n' * d * n'⁻¹) = n' * ((n'⁻¹ * s * n') * d) * n'⁻¹ := by group
      _ = n' * (d * (n'⁻¹ * s * n')) * n'⁻¹ := by rw [hdt']
      _ = (n' * d * n'⁻¹) * s := by group
  have heZ : n' * d * n'⁻¹ ∈ Subgroup.centralizer (S : Set G) :=
    Subgroup.mem_centralizer_iff.mpr hecent
  have hcZ : c ∈ Subgroup.centralizer (S : Set G) := by
    refine Subgroup.zpowers_le.mpr heZ ?_
    rw [hze]
    exact Subgroup.mem_zpowers c
  have hAZ : A ≤ Subgroup.centralizer (S : Set G) := by
    rw [← h.closure_eq, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact hcZ
    · rw [hx]; exact hdZ
    · rw [hx]; exact haZ
  have hSC' : S ≤ Subgroup.centralizer (A : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hAZ hx) s hs).symm
  exact hSA (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hSC')

end Certified

end CFSG.RankThree.PartTwo.Sec11
