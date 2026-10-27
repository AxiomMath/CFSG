module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.Monomial
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.RankThree.PartOne.N1322.MonoExtract

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix Equiv
open CFSG.HardMathSupport.Timmesfeld.LinearRank
open CFSG.HardMathSupport.Timmesfeld.Tables.Census
open CFSG.RankThree.PartOne.N1322

variable {K : Type} [Field K]

open CFSG.RepresentationTheory

theorem mono_eq_monoHom (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ) :
    (mono σ a : GL (Fin 3) K) =
      monoHom 3 K ⟨(fun i => a (σ⁻¹ i)), σ⟩ := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  have hperm : ((permGL 3 K σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      Pi.single j (1 : K) = Pi.single (σ j) 1 := by
    rw [coe_permGL, Matrix.permMatrix_mulVec]
    ext i
    simp only [Function.comp_apply, Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]
  have hdiag : (((CFSG.SectionRank.OddCover.diagHom 3 (fun i => a (σ⁻¹ i)) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single (σ j) (1 : K)) =
      Pi.single (σ j) (a j : K) := by
    ext i
    rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.mulVec_diagonal]
    by_cases hi : i = σ j
    · subst hi
      simp
    · simp [hi]
  rw [mono_mulVec_single, monoHom_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hperm, hdiag]

variable [Finite K]

theorem card_dvd_eighty_one_of_odd_transitive_monomial
    (hK : Nat.card K = 4) {J : Subgroup (GL (Fin 3) K)}
    (hmono : IsTransitiveMonomial J) (hodd : Odd (Nat.card J)) :
    Nat.card J ∣ 81 := by
  obtain ⟨P, hP⟩ := exists_frame hmono
  let J' : Subgroup (GL (Fin 3) K) := J.map (MulAut.conj P).toMonoidHom
  have hP' : MonoStd J' := hP
  have hJ'card : Nat.card J' = Nat.card J := by
    dsimp [J']
    rw [Subgroup.card_map_of_injective (MulAut.conj P).injective]
  have hle_range : J' ≤ (monoHom 3 K).range := by
    intro g hg
    obtain ⟨σ, a, rfl⟩ := hP'.isMono g hg
    exact ⟨⟨fun i => a (σ⁻¹ i), σ⟩, (mono_eq_monoHom σ a).symm⟩
  let S : Subgroup (MonoGroup 3 K) := J'.comap (monoHom 3 K)
  have hS_card : Nat.card S = Nat.card J := by
    have hmap : S.map (monoHom 3 K) = J' := Subgroup.map_comap_eq_self hle_range
    calc
      Nat.card S = Nat.card (S.map (monoHom 3 K)) :=
        (Subgroup.card_map_of_injective (f := monoHom 3 K) monoHom_injective).symm
      _ = Nat.card J' := by rw [hmap]
      _ = Nat.card J := hJ'card
  have hKunits : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]
  have hcardMono : Nat.card (MonoGroup 3 K) = 162 := by
    rw [card_monoGroup, hKunits]
    norm_num
  have hdiv : Nat.card J ∣ 162 := by
    rw [← hS_card, ← hcardMono]
    simpa using
      (Subgroup.card_dvd_of_le (show S ≤ (⊤ : Subgroup (MonoGroup 3 K)) from le_top))
  have hdvd : Nat.card J ∣ 2 * 81 := by
    simpa using hdiv
  exact (Odd.coprime_two_right hodd).dvd_of_dvd_mul_left hdvd

theorem exists_even_monomial_frame_of_card_eighty_one
    (hK : Nat.card K = 4) {J : Subgroup (GL (Fin 3) K)}
    (hmono : IsTransitiveMonomial J) (hcard : Nat.card J = 81) :
    ∃ P : GL (Fin 3) K, ∀ g : GL (Fin 3) K,
      g ∈ J.map (MulAut.conj P).toMonoidHom ↔
        ∃ σ : Equiv.Perm (Fin 3), σ ∈ alternatingGroup (Fin 3) ∧
          ∃ a : Fin 3 → Kˣ, g = mono σ a := by
  classical
  obtain ⟨P, hP⟩ := exists_frame hmono
  let J' : Subgroup (GL (Fin 3) K) := J.map (MulAut.conj P).toMonoidHom
  have hP' : MonoStd J' := hP
  have hJ'card : Nat.card J' = 81 := by
    dsimp [J']
    rw [Subgroup.card_map_of_injective (MulAut.conj P).injective, hcard]
  have hle_range : J' ≤ (monoHom 3 K).range := by
    intro g hg
    obtain ⟨σ, a, rfl⟩ := hP'.isMono g hg
    exact ⟨⟨fun i => a (σ⁻¹ i), σ⟩, (mono_eq_monoHom σ a).symm⟩
  let S : Subgroup (MonoGroup 3 K) := J'.comap (monoHom 3 K)
  have hS_card : Nat.card S = 81 := by
    have hmap : S.map (monoHom 3 K) = J' := Subgroup.map_comap_eq_self hle_range
    calc
      Nat.card S = Nat.card (S.map (monoHom 3 K)) :=
        (Subgroup.card_map_of_injective (f := monoHom 3 K) monoHom_injective).symm
      _ = Nat.card J' := by rw [hmap]
      _ = 81 := hJ'card
  let φ : S →* ℤˣ :=
    Equiv.Perm.sign.comp
      ((SemidirectProduct.rightHom : MonoGroup 3 K →* Equiv.Perm (Fin 3)).comp S.subtype)
  have hφ_card : Nat.card φ.range = 1 := by
    have hdvd81 : Nat.card φ.range ∣ 81 := by
      have h := Subgroup.card_range_dvd φ
      simpa [hS_card] using h
    have hdvd2 : Nat.card φ.range ∣ 2 := by
      have h := Subgroup.card_subgroup_dvd_card φ.range
      simpa [Nat.card_eq_fintype_card, Fintype.card_units_int] using h
    have hdvdgcd : Nat.card φ.range ∣ Nat.gcd 81 2 := Nat.dvd_gcd hdvd81 hdvd2
    rw [show Nat.gcd 81 2 = 1 by norm_num] at hdvdgcd
    exact Nat.dvd_one.mp hdvdgcd
  have hφ_triv : ∀ s : S, φ s = 1 := by
    intro s
    have hmem : φ s ∈ φ.range := ⟨s, rfl⟩
    rw [Subgroup.eq_bot_of_card_eq (H := φ.range) hφ_card, Subgroup.mem_bot] at hmem
    exact hmem
  have hright_even : ∀ s : S, (s : MonoGroup 3 K).right ∈ alternatingGroup (Fin 3) := by
    intro s
    rw [Equiv.Perm.mem_alternatingGroup]
    simpa [φ, SemidirectProduct.rightHom_eq_right] using hφ_triv s
  let E : Set (GL (Fin 3) K) :=
    {g | ∃ σ : Equiv.Perm (Fin 3), σ ∈ alternatingGroup (Fin 3) ∧
      ∃ a : Fin 3 → Kˣ, g = mono σ a}
  have hJ'leE : (J' : Set (GL (Fin 3) K)) ⊆ E := by
    intro g hg
    obtain ⟨s, hs⟩ := hle_range hg
    have hsS : s ∈ S := by
      rw [Subgroup.mem_comap]
      rwa [hs]
    have hbridge : mono s.right (fun j => s.left (s.right j)) = monoHom 3 K s := by
      rw [mono_eq_monoHom]
      congr 1
      exact SemidirectProduct.ext (by funext i; simp) rfl
    refine ⟨s.right, hright_even ⟨s, hsS⟩, fun j => s.left (s.right j), ?_⟩
    rw [← hs]
    exact hbridge.symm
  have hE81 : Nat.card E = 81 := by
    let F : (alternatingGroup (Fin 3) × (Fin 3 → Kˣ)) → E := fun x =>
      ⟨mono x.1.1 x.2, ⟨x.1.1, x.1.2, x.2, rfl⟩⟩
    have hFinj : Function.Injective F := by
      rintro ⟨⟨σ, hσ⟩, a⟩ ⟨⟨τ, hτ⟩, b⟩ h
      have h' : mono σ a = mono τ b := congrArg Subtype.val h
      obtain ⟨rfl, rfl⟩ := mono_injective h'
      rfl
    have hFsurj : Function.Surjective F := by
      rintro ⟨g, σ, hσ, a, rfl⟩
      exact ⟨⟨⟨σ, hσ⟩, a⟩, rfl⟩
    let e : (alternatingGroup (Fin 3) × (Fin 3 → Kˣ)) ≃ E :=
      Equiv.ofBijective F ⟨hFinj, hFsurj⟩
    have hcardE : Nat.card E =
        Nat.card (alternatingGroup (Fin 3) × (Fin 3 → Kˣ)) :=
      (Nat.card_congr e).symm
    have hKunits : Nat.card Kˣ = 3 := by
      rw [Nat.card_units, hK]
    rw [hcardE, Nat.card_prod, Nat.card_fun, nat_card_alternatingGroup, hKunits]
    norm_num
  have hEncard : E.ncard = 81 := by
    rw [← Nat.card_coe_set_eq]
    exact hE81
  have hJ'ncard : (J' : Set (GL (Fin 3) K)).ncard = 81 := by
    rw [← Nat.card_coe_set_eq]
    exact hJ'card
  have hset : (J' : Set (GL (Fin 3) K)) = E :=
    Set.eq_of_subset_of_ncard_le hJ'leE (by rw [hEncard, hJ'ncard])
  refine ⟨P, ?_⟩
  intro g
  change g ∈ (J' : Set (GL (Fin 3) K)) ↔ g ∈ E
  rw [hset]

theorem card_eq_twenty_seven_or_eighty_one_of_odd_monomial_irreducible_rank
    (hK : Nat.card K = 4) {J : Subgroup (GL (Fin 3) K)}
    (hmono : IsTransitiveMonomial J) (hodd : Odd (Nat.card J))
    (hirr : IsIrreducibleMatrixRep J.subtype)
    (hrank : 2 ≤ CFSG.Open.pRank 3 J) :
    Nat.card J = 27 ∨ Nat.card J = 81 := by
  have hdvd : Nat.card J ∣ 81 :=
    card_dvd_eighty_one_of_odd_transitive_monomial hK hmono hodd
  have hdvd' : Nat.card J ∣ 3 ^ 4 := by simpa using hdvd
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd'
  interval_cases k
  · have hcyc : IsCyclic J := by
      apply isCyclic_of_card_dvd_prime (p := 3)
      rw [hcard]
      norm_num
    have hle : CFSG.Open.pRank 3 J ≤ 1 :=
      CFSG.SectionRank.pRank_le_one_of_isCyclic (p := 3) (by norm_num) hcyc
    omega
  · have hcyc : IsCyclic J := by
      apply isCyclic_of_card_dvd_prime (p := 3)
      rw [hcard]
      norm_num
    have hle : CFSG.Open.pRank 3 J ≤ 1 :=
      CFSG.SectionRank.pRank_le_one_of_isCyclic (p := 3) (by norm_num) hcyc
    omega
  · have hcard9 : Nat.card J = 3 ^ 2 := by simpa using hcard
    have hcommJ : ∀ a b : J, a * b = b * a :=
      IsPGroup.commutative_of_card_eq_prime_sq (p := 3) hcard9
    have hcomm : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a :=
      fun a ha b hb => congrArg Subtype.val (hcommJ ⟨a, ha⟩ ⟨b, hb⟩)
    obtain ⟨hcyc, -, -⟩ :=
      cyclic_of_irreducible_of_commute (K := K) (n := 3) (by norm_num) hirr hcomm
    have hle : CFSG.Open.pRank 3 J ≤ 1 :=
      CFSG.SectionRank.pRank_le_one_of_isCyclic (p := 3) (by norm_num) hcyc
    omega
  · left
    rw [hcard]
    norm_num
  · right
    rw [hcard]
    norm_num

end CFSG.RankThree.SubgroupLists
