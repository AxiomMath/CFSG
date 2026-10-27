module

public import CFSG.RankThree.PartOne.KF.LayerCover
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalCores CFSG.RankThree.PartOne.KFU
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_layerCore_of_cover [Finite G] {p : ℕ} {A L : Subgroup G} {c : G} {P M : Type}
    [Group P] [Group M] [Finite M] [Finite P]
    (hp : p.Prime) (hp2 : p ≠ 2) (hAp : IsPGroup p ↥A) (hAel : IsElementaryAbelian p A)
    (hcL : L ≤ Subgroup.centralizer ({c} : Set G))
    (hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L))
    (ε : ↥L →* P) (q : M →* P) (hε : IsCentralPQuot p ε) (hq : IsCentralPQuot p q)
    {b : G} (hbA : b ∈ A) (hbL : b ∈ L) {bM : M} (hbMp : bM ^ p = 1)
    (hbb : ε ⟨b, hbL⟩ = q bM) {T₀ U : Subgroup M} (hT₀ : ∀ t ∈ T₀, t ^ p = 1)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = T₀.map q)
    (hKq : IsQuasisimple ↥(inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M))))
    (hKz : ¬ p ∣ Nat.card (Subgroup.center
      ↥(inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M)))))
    (hTK : Nat.card ↥(T₀ ⊓ inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M))) = p)
    (hU : U ≤ inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M)))
    (hU2 : IsPGroup 2 ↥U) (hTU : T₀ ≤ Subgroup.normalizer (U : Set M))
    (hnc : ∃ u ∈ U, ∃ t ∈ T₀, u * t ≠ t * u) :
    ∃ K : Subgroup G, K = kLayer L b ∧ IsQuasisimple ↥K ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥K) ∧ Nat.card ↥(A ⊓ K) = p ∧
      (∃ S : Subgroup G, S ≤ K ∧ S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧
        A ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A⁆) ∧
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃*
        ↥(inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M))) ⧸
          Subgroup.center ↥(inSubgroup perfectResidual
            (Subgroup.centralizer ({bM} : Set M)))) := by
  classical
  have hAe : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hAel.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  set b' : ↥L := ⟨b, hbL⟩ with hb'
  set KE : Subgroup ↥L := inSubgroup perfectResidual (Subgroup.centralizer ({b'} : Set ↥L))
    with hKE
  set KM := inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M)) with hKM
  have hbp : b ^ p = 1 := hAe b hbA
  have hb'p : b' ^ p = 1 := Subtype.ext (by simpa using hbp)
  have hKEq : IsQuasisimple ↥KE :=
    isQuasisimple_perfectResidual_centralizer hε hq hb'p hbMp hbb hKq
  have hmap : KE.map ε = KM.map q := map_perfectResidual_centralizer hε hq hb'p hbMp hbb
  obtain ⟨hkL, -⟩ := kLayer_eq_map_of_isQuasisimple hbL hKEq
  set K : Subgroup G := KE.map L.subtype with hK
  have eK : ↥KE ≃* ↥K := Subgroup.equivMapOfInjective KE L.subtype L.subtype_injective
  set A₀ : Subgroup ↥L := (A ⊓ L).subgroupOf L with hA₀
  have hA₀e : ∀ a ∈ A₀, a ^ p = 1 := fun a ha =>
    Subtype.ext (by simpa using hAe _ (Subgroup.mem_subgroupOf.1 ha).1)
  have hA₀c : A₀ ≤ Subgroup.centralizer ({b'} : Set ↥L) := fun a ha => by
    refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
    exact hAcomm _ (Subgroup.mem_subgroupOf.1 ha).1 _ hbA
  have hA₀n : A₀ ≤ Subgroup.normalizer (KE : Set ↥L) := fun a ha =>
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (Subgroup.le_normalizer (hA₀c ha))
  have hAK : Nat.card ↥(A ⊓ K) = p := by
    have h1 : A ⊓ K = (A₀ ⊓ KE).map L.subtype := by
      ext x
      constructor
      · rintro ⟨hxA, k, hk, rfl⟩
        exact ⟨k, ⟨Subgroup.mem_subgroupOf.2 ⟨hxA, k.2⟩, hk⟩, rfl⟩
      · rintro ⟨k, ⟨hkA₀, hkKE⟩, rfl⟩
        exact ⟨(Subgroup.mem_subgroupOf.1 hkA₀).1, k, hkKE, rfl⟩
    rw [h1, Subgroup.card_map_of_injective L.subtype_injective,
      card_inf_eq_card_map_inf hε hA₀e, hAT, hmap, ← card_inf_eq_card_map_inf hq hT₀]
    exact hTK
  obtain ⟨S₁, hS₁KE, hS₁2, hS₁n, x, hxS, a, haA₀, hxa⟩ :=
    exists_invariant_two_subgroup hε hq hmap hAT hA₀n hU hU2 hTU hT₀ hnc
  set S₁' : Subgroup G := S₁.map L.subtype with hS₁'
  have hS₁'K : S₁' ≤ K := Subgroup.map_mono hS₁KE
  have hS₁'p : IsPGroup 2 ↥S₁' :=
    hS₁2.of_surjective (L.subtype.subgroupMap S₁) (L.subtype.subgroupMap_surjective S₁)
  have hAL : A ⊓ L ≤ Subgroup.normalizer (S₁' : Set G) := by
    have hconj : ∀ g ∈ A ⊓ L, ∀ y ∈ S₁', g * y * g⁻¹ ∈ S₁' := by
      rintro g hg _ ⟨s, hs, rfl⟩
      have hgA₀ : (⟨g, hg.2⟩ : ↥L) ∈ A₀ := Subgroup.mem_subgroupOf.2 hg
      have := Subgroup.mem_normalizer_iff.1 (hS₁n hgA₀) s
      exact ⟨_, this.1 hs, rfl⟩
    intro g hg
    exact mem_normalizer_of_conj_mem (hconj g hg) (fun y hy => by
      have := hconj g⁻¹ ((A ⊓ L).inv_mem hg) y hy
      simpa using this)
  have hcn : ∀ y ∈ S₁', c * y * c⁻¹ = y ∧ c⁻¹ * y * c = y := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 : (s : G) * c = c * (s : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hcL s.2)
    change c * (s : G) * c⁻¹ = (s : G) ∧ c⁻¹ * (s : G) * c = (s : G)
    constructor
    · rw [← h1]
      group
    · rw [mul_assoc, h1]
      group
  have hcnorm : c ∈ Subgroup.normalizer (S₁' : Set G) :=
    mem_normalizer_of_conj_mem (fun y hy => by rw [(hcn y hy).1]; exact hy)
      (fun y hy => by rw [(hcn y hy).2]; exact hy)
  have hAn : A ≤ Subgroup.normalizer (S₁' : Set G) :=
    hA.trans (sup_le (Subgroup.zpowers_le.2 hcnorm) hAL)
  set S : Subgroup G := ⁅S₁', A⁆ with hS
  have hSle : S ≤ S₁' := Subgroup.le_normalizer_iff_commutator_le_left.1 hAn
  have hSA : A ≤ Subgroup.normalizer (S : Set G) := Subgroup.normalizer_commutator_ge_right S₁' A
  have hSp : IsPGroup 2 ↥S := hS₁'p.to_le hSle
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hx' : (x : G) ∈ S₁' := ⟨x, hxS, rfl⟩
    have ha' : (a : G) ∈ A := (Subgroup.mem_subgroupOf.1 haA₀).1
    have hmem : ⁅(x : G), (a : G)⁆ ∈ S := Subgroup.commutator_mem_commutator hx' ha'
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hxa (Subtype.ext hmem)
  have hcop : ¬ p ∣ Nat.card ↥S₁' := by
    obtain ⟨n, hn⟩ := hS₁'p.exists_card_eq
    rw [hn]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hSS : ⁅S, A⁆ = S :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp A S₁' hAp hcop hAn
  obtain ⟨e1⟩ := exists_centerQuotient_mulEquiv eK.symm
  obtain ⟨e2⟩ := exists_centerQuotientEquiv_perfectResidual_centralizer hε hq hb'p hbMp hbb
  refine ⟨K, hkL.symm, isQuasisimple_of_mulEquiv eK hKEq, ?_, hAK,
    ⟨S, hSle.trans hS₁'K, hSne, hSp, hSA, hSS.symm⟩, ⟨e1.trans e2⟩⟩
  rw [← card_center_mulEquiv eK]
  exact not_dvd_card_center_perfectResidual_centralizer hε hq hb'p hbMp hbb hp hKz

end CFSG.RankThree.PartOne
