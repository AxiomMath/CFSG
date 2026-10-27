module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KF.LayerCover

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalCores CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem layerData_of_cover [Finite G] {p : ℕ} {A L : Subgroup G} {P M : Type}
    [Group P] [Group M] [Finite M] [Finite P]
    (hp : p.Prime) (hAel : IsElementaryAbelian p A)
    (ε : ↥L →* P) (q : M →* P) (hε : IsCentralPQuot p ε) (hq : IsCentralPQuot p q)
    {b : G} (hbA : b ∈ A) (hbL : b ∈ L) {bM : M} (hbMp : bM ^ p = 1)
    (hbb : ε ⟨b, hbL⟩ = q bM) {T₀ : Subgroup M} (hT₀ : ∀ t ∈ T₀, t ^ p = 1)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = T₀.map q)
    (hKq : IsQuasisimple ↥(inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M))))
    (hKz : ¬ p ∣ Nat.card (Subgroup.center
      ↥(inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M)))))
    (hTK : Nat.card ↥(T₀ ⊓ inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M))) = p) :
    ∃ K : Subgroup G, K = kLayer L b ∧ IsQuasisimple ↥K ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥K) ∧ Nat.card ↥(A ⊓ K) = p ∧
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃*
        ↥(inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M))) ⧸
          Subgroup.center ↥(inSubgroup perfectResidual
            (Subgroup.centralizer ({bM} : Set M)))) ∧
      (Function.Injective ε → Function.Injective q →
        Nonempty (↥K ≃* ↥(inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M))))) := by
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
  obtain ⟨e1⟩ := exists_centerQuotient_mulEquiv eK.symm
  obtain ⟨e2⟩ := exists_centerQuotientEquiv_perfectResidual_centralizer hε hq hb'p hbMp hbb
  refine ⟨K, hkL.symm, isQuasisimple_of_mulEquiv eK hKEq, ?_, hAK, ⟨e1.trans e2⟩,
    fun hεi hqi => ⟨eK.symm.trans ((KE.equivMapOfInjective ε hεi).trans
      ((MulEquiv.subgroupCongr hmap).trans (KM.equivMapOfInjective q hqi).symm))⟩⟩
  rw [← card_center_mulEquiv eK]
  exact not_dvd_card_center_perfectResidual_centralizer hε hq hb'p hbMp hbb hp hKz

theorem statedModel_psl_two_of_layer {k : Type} [Field k] [Finite k] [CharP k 2] {g : ℕ}
    (hkg : Nat.card k = 2 ^ g) (hg : 2 ≤ g) {X Y : Type} [Group X] [Group Y] {D : Subgroup Y}
    {ι : Matrix.SpecialLinearGroup (Fin 2) k →* Y} (hι : Function.Injective ι) (hD : D = ι.range)
    (e : X ⧸ Subgroup.center X ≃* ↥D ⧸ Subgroup.center ↥D) :
    StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 2 g := by
  have h4g : 4 ≤ 2 ^ g := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  refine ⟨⟨Nat.prime_two, by omega, by norm_num, ?_, ?_⟩, k, inferInstance, inferInstance, hkg, ?_⟩
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · obtain ⟨e₃⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hD)
    obtain ⟨e₄⟩ := exists_centerQuotient_mulEquiv (MonoidHom.ofInjective hι).symm
    exact ⟨e.trans (e₃.trans (e₄.trans (projectiveSpecialLinearGroupEquivStatedProj 2 k)))⟩

end CFSG.RankThree.PartOne
