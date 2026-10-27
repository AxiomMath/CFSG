module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.RankThree.PartTwo.KFacts.K71Coprime

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem exists_isPGroup_map_eq_of_surjective {H K : Type*} [Group H] [Group K] [Finite H]
    {p : ℕ} [Fact p.Prime] {f : H →* K} (hf : Function.Surjective f) {E : Subgroup K}
    (hE : IsPGroup p E) : ∃ P : Subgroup H, IsPGroup p P ∧ P.map f = E := by
  set W := E.comap f with hW
  let ψ : W →* E := (f.comp W.subtype).codRestrict E fun w => w.2
  have hψ : Function.Surjective ψ := by
    intro e
    obtain ⟨x, hx⟩ := hf e
    exact ⟨⟨x, show f x ∈ E by rw [hx]; exact e.2⟩, Subtype.ext hx⟩
  obtain ⟨T⟩ : Nonempty (Sylow p W) := inferInstance
  have htop : ((T.mapSurjective hψ : Sylow p E) : Subgroup E) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hE.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨(T : Subgroup W).map W.subtype, T.isPGroup'.map _, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact w.2
  · intro e he
    have : (⟨e, he⟩ : E) ∈ (T : Subgroup W).map ψ := htop ▸ Subgroup.mem_top _
    obtain ⟨w, hw, hwe⟩ := this
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwe⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_centralizer_of_fixed_coset {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) {k : ℕ} (hak : a ^ 3 ^ k = 1) (k₀ : K)
    (hfix : Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨a, ha⟩)
      (k₀ : K ⧸ aschbacherSolvableCore 3 K) = k₀) :
    ∃ c : K, ((c : K ⧸ aschbacherSolvableCore 3 K) = k₀) ∧
      (c : G) ∈ Subgroup.centralizer ({a} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 K with hN
  set ν : Subgroup.normalizer (K : Set G) →* MulAut (K ⧸ N) :=
    (Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom with hν
  set A : Subgroup (Subgroup.normalizer (K : Set G)) := Subgroup.zpowers ⟨a, ha⟩ with hA
  have hA3 : IsPGroup 3 A := by
    rintro ⟨g, hg⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simp only [Subgroup.coe_pow, SubgroupClass.coe_zpow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hak, one_zpow]
  have hstab : ∀ b ∈ A, ν b (k₀ : K ⧸ N) = k₀ := by
    intro b hb
    have hle : A ≤ (MulAction.stabilizer (MulAut (K ⧸ N)) ((k₀ : K ⧸ N))).comap ν := by
      rw [hA, Subgroup.zpowers_le]
      show ν ⟨a, ha⟩ ∈ MulAction.stabilizer (MulAut (K ⧸ N)) ((k₀ : K ⧸ N))
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hfix
    have hmem := hle hb
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def] at hmem
    exact hmem
  have hcop : ¬ 3 ∣ Nat.card N := KFacts.not_three_dvd_card_aschbacherSolvableCore K
  obtain ⟨c, hc, hcfix⟩ := (Semidihedral.Principal.coprime_invariant_coset_fixed 3 hA3
    (K.normalizerMonoidHom.comp A.subtype) N hcop k₀).2 (by
      intro b x hx
      have hb := hstab b b.2
      rw [hν, MonoidHom.comp_apply, Sec4.thetaQuotMulAut_mk] at hb
      have h1 : k₀⁻¹ * (K.normalizerMonoidHom (b : Subgroup.normalizer (K : Set G))) k₀ ∈ N :=
        QuotientGroup.eq.mp hb.symm
      have h2 : (K.normalizerMonoidHom (b : Subgroup.normalizer (K : Set G))) (k₀⁻¹ * x) ∈ N := by
        have hmap : N.map
            ((K.normalizerMonoidHom (b : Subgroup.normalizer (K : Set G))) : K →* K) = N :=
          Sec4.map_aschbacherSolvableCore _
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ hx
      have h3 : k₀⁻¹ * (K.normalizerMonoidHom.comp A.subtype) b x =
          (k₀⁻¹ * (K.normalizerMonoidHom (b : Subgroup.normalizer (K : Set G))) k₀) *
            (K.normalizerMonoidHom (b : Subgroup.normalizer (K : Set G))) (k₀⁻¹ * x) := by
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv]
        group
      rw [h3]
      exact N.mul_mem h1 h2)
  refine ⟨c, (QuotientGroup.eq.mpr hc).symm, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := hcfix ⟨⟨a, ha⟩, Subgroup.mem_zpowers _⟩
  have h2 : a * (c : G) * a⁻¹ = c := congrArg Subtype.val h1
  calc (c : G) * a = a * c * a⁻¹ * a := by rw [h2]
    _ = a * c := by group

theorem exists_pGroup_le_centralizer_of_fixed {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) {k : ℕ} (hak : a ^ 3 ^ k = 1)
    (Q : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) (hQ : IsPGroup 3 Q)
    (hQa : ∀ q ∈ Q, Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨a, ha⟩) q = q) :
    ∃ Q' : Subgroup G, Q' ≤ K ⊓ Subgroup.centralizer ({a} : Set G) ∧ IsPGroup 3 Q' ∧
      Nat.card Q ≤ Nat.card Q' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 K with hN
  set C : Subgroup K := (K ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf K with hC
  set φ : C →* K ⧸ N := (QuotientGroup.mk' N).comp C.subtype with hφ
  set W : Subgroup C := Q.comap φ with hW
  let ψ : W →* Q := (φ.comp W.subtype).codRestrict Q fun w => w.2
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk_surjective (q : K ⧸ N)
    have hfix := hQa q q.2
    rw [← hk₀] at hfix
    obtain ⟨c, hcq, hca⟩ := exists_mem_centralizer_of_fixed_coset ha hak k₀ hfix
    have hcC : c ∈ C := Subgroup.mem_subgroupOf.mpr ⟨c.2, hca⟩
    have hcW : (⟨c, hcC⟩ : C) ∈ W := by
      show φ ⟨c, hcC⟩ ∈ Q
      have : φ ⟨c, hcC⟩ = (q : K ⧸ N) := by
        rw [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply, hcq, hk₀]
      rw [this]
      exact q.2
    refine ⟨⟨⟨c, hcC⟩, hcW⟩, Subtype.ext ?_⟩
    show φ ⟨c, hcC⟩ = (q : K ⧸ N)
    rw [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply, hcq, hk₀]
  obtain ⟨T⟩ : Nonempty (Sylow 3 W) := inferInstance
  have htop : ((T.mapSurjective hψ : Sylow 3 Q) : Subgroup Q) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  set Q' : Subgroup G := (((T : Subgroup W).map W.subtype).map C.subtype).map K.subtype with hQ'
  refine ⟨Q', ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨_, ⟨w, -, rfl⟩, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (w : C).2
  · exact ((T.isPGroup'.map _).map _).map _
  · have h1 : Nat.card Q' = Nat.card T := by
      rw [hQ', Subgroup.card_map_of_injective K.subtype_injective,
        Subgroup.card_map_of_injective C.subtype_injective,
        Subgroup.card_map_of_injective W.subtype_injective]
    have h2 : Nat.card Q = Nat.card ((T : Subgroup W).map ψ) := by
      rw [htop, Subgroup.card_top]
    rw [h1, h2]
    exact Nat.card_le_card_of_surjective (ψ.subgroupMap (T : Subgroup W))
      (ψ.subgroupMap_surjective (T : Subgroup W))

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
