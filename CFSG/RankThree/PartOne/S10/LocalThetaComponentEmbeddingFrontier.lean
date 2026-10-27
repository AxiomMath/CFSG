module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.LocalThetaQuotientNormalizationEmbedding
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PerfectCover.CentralQuotientPrimeSupport

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank

namespace LocalEmbeddingFrontier

variable {K : Type*} [Group K] [Finite K]

theorem not_dvd_card_of_not_dvd_card_central_quotient {p : ℕ} (hp : p.Prime)
    (hq : IsQuasisimple (K ⧸ aschbacherSolvableCore p K))
    (hS : ¬ p ∣ Nat.card ((K ⧸ aschbacherSolvableCore p K) ⧸
      Subgroup.center (K ⧸ aschbacherSolvableCore p K))) : ¬ p ∣ Nat.card K := by
  have : Group.IsPerfect (K ⧸ aschbacherSolvableCore p K) := hq.1
  have h1 := CFSG.RankThree.PerfectCover.perfect_central_quotient_prime_support hp hS
  have h2 := (solvable_prime_complement_core_characterization (H := K) hp).2.2.1
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore p K)]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  exacts [h1 h, h2 h]

theorem isSolvable_ker_central_quotient {p : ℕ} (hp : p.Prime) :
    Group.IsSolvable ((QuotientGroup.mk' (Subgroup.center (K ⧸ aschbacherSolvableCore p K))).comp
      (QuotientGroup.mk' (aschbacherSolvableCore p K))).ker := by
  set θ := aschbacherSolvableCore p K
  set Z := Subgroup.center (K ⧸ θ)
  set ψ := (QuotientGroup.mk' Z).comp (QuotientGroup.mk' θ)
  have hθs : Group.IsSolvable θ := (solvable_prime_complement_core_characterization hp).1
  have hθker : θ ≤ ψ.ker := fun t ht => by
    have h1 : (QuotientGroup.mk' θ) t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h1, map_one]
  let f : θ →* ψ.ker := Subgroup.inclusion hθker
  let g : ψ.ker →* Z := ((QuotientGroup.mk' θ).comp ψ.ker.subtype).codRestrict Z fun y => by
    have := y.2
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at this
    exact this
  have : Group.IsSolvable Z := Group.isSolvable_of_comm (fun a b => Subtype.ext
    (Subgroup.mem_center_iff.mp b.2 a))
  refine Group.isSolvable_of_ker_le_range f g fun y hy => ?_
  have hy1 : (QuotientGroup.mk' θ) (y : K) = 1 := congrArg Subtype.val hy
  exact ⟨⟨y, (QuotientGroup.eq_one_iff _).mp hy1⟩, Subtype.ext rfl⟩

theorem eq_top_of_pElements_le {p : ℕ} (hp : p.Prime) (hperf : Group.IsPerfect K)
    (hq : IsQuasisimple (K ⧸ aschbacherSolvableCore p K))
    (hS : p ∣ Nat.card ((K ⧸ aschbacherSolvableCore p K) ⧸
      Subgroup.center (K ⧸ aschbacherSolvableCore p K)))
    {Sub : Subgroup K} (hSub : ∀ y : K, (∃ k : ℕ, orderOf y = p ^ k) → y ∈ Sub) : Sub = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  set θ := aschbacherSolvableCore p K
  set Z := Subgroup.center (K ⧸ θ)
  set ψ := (QuotientGroup.mk' Z).comp (QuotientGroup.mk' θ) with hψdef
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective Z).comp (QuotientGroup.mk'_surjective θ)
  have hsimple : IsSimpleGroup ((K ⧸ θ) ⧸ Z) := hq.2.1
  set S₀ : Set K := {y | ∃ k : ℕ, orderOf y = p ^ k} with hS₀
  set U : Subgroup K := Subgroup.normalClosure S₀ with hU
  have hUSub : U ≤ Sub := by
    rw [hU, Subgroup.normalClosure, Subgroup.closure_le]
    intro z hz
    obtain ⟨a, ⟨k, hk⟩, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    refine hSub _ ⟨k, ?_⟩
    rw [← hk]
    exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a
  have hUn : (U.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (U.map ψ) with h0 | htop
  ·
    exfalso
    have hUker : U ≤ ψ.ker := (Subgroup.map_eq_bot_iff _).mp h0
    obtain P : Sylow p K := default
    have hPU : (P : Subgroup K) ≤ U := fun y hy => by
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨y, hy⟩
      exact Subgroup.subset_normalClosure ⟨k, by rwa [← Subgroup.orderOf_coe] at hk⟩
    have h1 : p ^ (Nat.card K).factorization p ∣ Nat.card ψ.ker := by
      rw [← P.card_eq_multiplicity]
      exact Subgroup.card_dvd_of_le (hPU.trans hUker)
    have h2 : p ∣ Nat.card (K ⧸ ψ.ker) := by
      rwa [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
    have h3 : p ^ ((Nat.card K).factorization p + 1) ∣ Nat.card K := by
      have h := mul_dvd_mul h1 h2
      rw [← pow_succ, mul_comm (Nat.card ψ.ker),
        ← Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker] at h
      exact h
    have h4 := (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp h3
    omega
  ·
    have hsup : U ⊔ ψ.ker = ⊤ := by
      have h := Subgroup.comap_map_eq ψ U
      rwa [htop, Subgroup.comap_top, eq_comm] at h
    have hKs : Group.IsSolvable ψ.ker := isSolvable_ker_central_quotient hp
    let χ : ψ.ker →* K ⧸ U := (QuotientGroup.mk' U).comp ψ.ker.subtype
    have hχ : Function.Surjective χ := by
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective U q
      obtain ⟨u, hu, w, hw, huw⟩ := Subgroup.mem_sup_of_normal_left.mp
        (hsup ▸ Subgroup.mem_top k : k ∈ U ⊔ ψ.ker)
      refine ⟨⟨w, hw⟩, ?_⟩
      have h1 : QuotientGroup.mk' U u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
      change QuotientGroup.mk' U w = QuotientGroup.mk' U k
      rw [← huw, map_mul, h1, one_mul]
    have hsol : Group.IsSolvable (K ⧸ U) := Group.isSolvable_of_surjective hχ
    have hperfQ : Group.IsPerfect (K ⧸ U) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' U) (QuotientGroup.mk'_surjective U)
    have hUtop : U = ⊤ := by
      by_contra hne
      obtain ⟨g, hg⟩ : ∃ g : K, g ∉ U := by
        by_contra hall
        push Not at hall
        exact hne (eq_top_iff.mpr fun g _ => hall g)
      have : Nontrivial (K ⧸ U) :=
        ⟨⟨(g : K ⧸ U), 1, fun h => hg ((QuotientGroup.eq_one_iff g).mp h)⟩⟩
      exact Group.IsPerfect.not_isSolvable (K ⧸ U) hsol
    exact top_le_iff.mp (hUtop ▸ hUSub)

end LocalEmbeddingFrontier

theorem local_theta_component_embedding_frontier_of
    (hnorm : SelectedPrimeElementsNormalizeThetaComponents)
    (hcop : PCoprimeLocalThetaComponentQuotientNormalizationFrontier) :
    LocalThetaComponentEmbeddingFrontier := by
  intro hS H _ _ hK hE p hp hp3 x hxo Y hY
  have hx : ∃ k : ℕ, orderOf x = p ^ k := ⟨1, by rw [pow_one]; exact hxo⟩
  have hpElt : ∀ g : H, (∃ k : ℕ, orderOf g = p ^ k) →
      ∀ J : Subgroup (H ⧸ aschbacherSolvableCore p H), IsComponent J →
        QuotientGroup.mk' (aschbacherSolvableCore p H) g ∈ Subgroup.normalizer (J : Set _) :=
    fun g hg J hJ => EmbeddingTransport.mk_mem_normalizer_of_mem_normalizer_thetaComponents hp
      (fun L hL => hnorm.1 H hE p hp hp3 g hg L hL) hJ
  refine local_theta_component_quotient_normalization_embedding hS H hK p hp x hx Y hY
    fun J hJ => ⟨hpElt x hx J hJ, ?_⟩
  obtain ⟨Y₀, hY₀, rfl⟩ := hY
  have hperf : Group.IsPerfect Y₀ := hY₀.1
  have hq := hY₀.2.2
  by_cases hdiv : p ∣ Nat.card ((Y₀ ⧸ aschbacherSolvableCore p Y₀) ⧸
      Subgroup.center (Y₀ ⧸ aschbacherSolvableCore p Y₀))
  ·
    set π := QuotientGroup.mk' (aschbacherSolvableCore p H)
    set ι := (Subgroup.centralizer ({x} : Set H)).subtype.comp Y₀.subtype
    have hall := LocalEmbeddingFrontier.eq_top_of_pElements_le hp hperf hq hdiv
      (Sub := ((Subgroup.normalizer (J : Set _)).comap π).comap ι)
      (fun y ⟨k, hk⟩ => hpElt _ ⟨k, by
        change orderOf (((y : Subgroup.centralizer ({x} : Set H)) : H)) = p ^ k
        rwa [Subgroup.orderOf_coe, Subgroup.orderOf_coe]⟩ J hJ)
    rintro _ ⟨y, ⟨y₀, hy₀, rfl⟩, rfl⟩
    have h : (⟨y₀, hy₀⟩ : Y₀) ∈ ((Subgroup.normalizer (J : Set _)).comap π).comap ι :=
      hall ▸ Subgroup.mem_top _
    exact h
  ·
    have hpY : ¬ p ∣ Nat.card (Y₀.map (Subgroup.centralizer ({x} : Set H)).subtype) := by
      rw [Subgroup.card_map_of_injective (Subgroup.centralizer ({x} : Set H)).subtype_injective]
      exact LocalEmbeddingFrontier.not_dvd_card_of_not_dvd_card_central_quotient hp hq hdiv
    exact hcop H hK hE p hp hp3 x hxo _ ⟨Y₀, hY₀, rfl⟩ hpY J hJ

end CFSG.RankThree.PartOne
