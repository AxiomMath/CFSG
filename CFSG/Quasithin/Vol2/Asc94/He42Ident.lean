module

public import CFSG.Quasithin.Vol2.Asc94.He42Plane
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneCollineation
public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Fischer.F4
public import Certificates.Certificate2036
public import Certificates.Certificate2037
public import Certificates.Certificate2038
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.Quasithin.A94.He42Ident

open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.A94.He42Plane

theorem he42id_isSolvable_of_card_six (K : Type) [Group K] (h : Nat.card K = 6) :
    Group.IsSolvable K := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (G := K) (by rw [h]; norm_num)
  have hAcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hAcard, h] at this
    omega
  haveI : (Subgroup.zpowers x).Normal := Subgroup.normal_of_index_eq_two hidx
  have hq : Nat.card (K ⧸ Subgroup.zpowers x) = 2 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers x)
    rw [h, hAcard] at this
    omega
  haveI : IsCyclic (K ⧸ Subgroup.zpowers x) := isCyclic_of_prime_card hq
  exact Group.isSolvable_of_subgroup_quotient (Subgroup.zpowers x)

theorem he42id_eq_one_of_perfect_of_solvable {L K : Type} [Group L] [Group K]
    [Group.IsSolvable K] (hL : commutator L = ⊤) (f : L →* K) (g : L) : f g = 1 := by
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable K)
  have htop : ∀ m : ℕ, derivedSeries L m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [derivedSeries_succ, ih]; exact hL
  have hle := map_derivedSeries_le_derivedSeries f n
  rw [htop n, hn] at hle
  have hmem : f g ∈ (⊥ : Subgroup K) := hle ⟨g, trivial, rfl⟩
  exact Subgroup.mem_bot.1 hmem

theorem he42id_center_psl34 :
    Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 3) CFSG.Fischer.F4) = ⊥ := by
  obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := CFSG.Fischer.F4)
    (n := 3) (by norm_num) (Or.inl le_rfl)
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := CFSG.Fischer.F4) (n := 3)
    (by norm_num) (Or.inl le_rfl)
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · exact h
  · exfalso
    have hc := (commutator_eq_bot_iff_center_eq_top _).2 h
    have ht := hperf.commutator_eq_top
    rw [hc] at ht
    obtain ⟨g, hg⟩ := exists_ne (1 : Matrix.ProjectiveSpecialLinearGroup (Fin 3) CFSG.Fischer.F4)
    have hg' : g ∈ (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) CFSG.Fischer.F4)) :=
      trivial
    rw [← ht] at hg'
    exact hg (Subgroup.mem_bot.1 hg')

theorem he42id_natCard_F4 : Nat.card CFSG.Fischer.F4 = 2 ^ 2 := by
  rw [Nat.card_eq_fintype_card, CFSG.Fischer.F4.card]; norm_num

theorem he42id_stated_psl34 :
    CFSG.Open.StatedClassicalModel (Matrix.ProjectiveSpecialLinearGroup (Fin 3) CFSG.Fischer.F4)
      .PSL 3 2 2 :=
  ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, CFSG.Fischer.F4,
    inferInstance, inferInstance, he42id_natCard_F4,
    ⟨CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 CFSG.Fischer.F4⟩⟩

theorem he42id_map_symm_map {α β : Type} (e : α ≃ β) (X : Finset β) :
    (X.map e.symm.toEmbedding).map e.toEmbedding = X := by
  rw [Finset.map_map]
  ext x
  simp

theorem he42id_map_permCongr {α β : Type} (e : α ≃ β) (σ : Equiv.Perm α) (X : Finset β) :
    X.map (e.permCongr σ).toEmbedding =
      ((X.map e.symm.toEmbedding).map σ.toEmbedding).map e.toEmbedding := by
  rw [Finset.map_map, Finset.map_map]
  congr 1

theorem he42id_inc_smul {L : Type} [Group L] [Finite L] (L₁ L₂ : Subgroup L) (g : L)
    (p : L ⧸ L₁) (ℓ : L ⧸ L₂) : Inc L₁ L₂ (g • p) (g • ℓ) ↔ Inc L₁ L₂ p ℓ := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ℓ
  simp only [MulAction.Quotient.smul_coe, smul_eq_mul]
  constructor
  · rintro ⟨h, h1, h2⟩
    refine ⟨g⁻¹ * h, ?_, ?_⟩
    · rw [QuotientGroup.eq] at h1 ⊢
      convert h1 using 1
      group
    · rw [QuotientGroup.eq] at h2 ⊢
      convert h2 using 1
      group
  · rintro ⟨h, h1, h2⟩
    refine ⟨g * h, ?_, ?_⟩
    · rw [QuotientGroup.eq] at h1 ⊢
      convert h1 using 1
      group
    · rw [QuotientGroup.eq] at h2 ⊢
      convert h2 using 1
      group

theorem he42id_map_pts {L : Type} [Group L] [Finite L] (L₁ L₂ : Subgroup L) (g : L)
    (y : L ⧸ L₂) :
    (pts L₁ L₂ y).map (MulAction.toPerm g : Equiv.Perm (L ⧸ L₁)).toEmbedding =
      pts L₁ L₂ (g • y) := by
  ext q
  rw [Finset.mem_map]
  simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.toEmbedding_apply,
    MulAction.toPerm_apply]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (he42id_inc_smul L₁ L₂ g p y).2 hp
  · intro hq
    refine ⟨g⁻¹ • q, ?_, smul_inv_smul g q⟩
    rw [← he42id_inc_smul L₁ L₂ g (g⁻¹ • q) y, smul_inv_smul]
    exact hq

open Classical in
theorem he42id_perm_mem_blockAut {L : Type} [Group L] [Finite L] (L₁ L₂ : Subgroup L) (g : L) :
    (MulAction.toPerm g : Equiv.Perm (L ⧸ L₁)) ∈ blockAut (lineSet L₁ L₂) := by
  have key : ∀ (k : L) (B : Finset (L ⧸ L₁)), B ∈ lineSet L₁ L₂ →
      B.map (MulAction.toPerm k : Equiv.Perm (L ⧸ L₁)).toEmbedding ∈ lineSet L₁ L₂ := by
    intro k B hB
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hB
    rw [he42id_map_pts]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hcomp : ∀ (k : L) (C : Finset (L ⧸ L₁)),
      (C.map (MulAction.toPerm k : Equiv.Perm (L ⧸ L₁)).toEmbedding).map
        (MulAction.toPerm k⁻¹ : Equiv.Perm (L ⧸ L₁)).toEmbedding = C := by
    intro k C
    rw [Finset.map_map]
    ext x
    simp
  rw [mem_blockAut]
  intro B
  constructor
  · intro hB
    have h := key g⁻¹ _ hB
    rwa [hcomp g B] at h
  · exact key g B

theorem typeL34_of_plane
    {L : Type} [Group L] [Finite L] (L₁ L₂ B : Subgroup L)
    (hplane : IsSteinerPlane (lineSet L₁ L₂)) (hBcard : Nat.card B = 4)
    (hL₁ : Nat.card L₁ = 3840) (hBK : B ≤ L₁ ⊓ L₂) (hBcent : ∀ b ∈ B, ∀ g : L, b * g = g * b)
    (hker : ∀ g : L, (∀ p : L ⧸ L₁, g • p = p) → g ∈ B) (hperf : commutator L = ⊤) :
    Subgroup.center L = B ∧
      CFSG.ComponentClassification.AS81.TypeL34 (L ⧸ Subgroup.center L) := by
  have hBL₁ : ∀ b ∈ B, b ∈ L₁ := fun b hb => (hBK hb).1
  have hBnormal : B.Normal := ⟨fun n hn g => by
    have h1 : n * g = g * n := hBcent n hn g
    have h2 : g * n * g⁻¹ = n := by rw [← h1, mul_inv_cancel_right]
    rw [h2]
    exact hn⟩
  haveI := hBnormal
  set α : L →* Equiv.Perm (L ⧸ L₁) := MulAction.toPermHom L (L ⧸ L₁) with hα
  have hαapply : ∀ (g : L) (p : L ⧸ L₁), α g p = g • p := fun g p => rfl
  have hker_eq : α.ker = B := by
    ext g
    rw [MonoidHom.mem_ker, Equiv.Perm.ext_iff]
    constructor
    · intro hg
      apply hker g
      intro p
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
      have h := hg ↑x
      rw [hαapply, Equiv.Perm.one_apply] at h
      exact h
    · intro hg p
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
      rw [hαapply, Equiv.Perm.one_apply, MulAction.Quotient.smul_coe, smul_eq_mul, hBcent g hg x]
      refine QuotientGroup.eq.2 ?_
      have h1 : (x * g)⁻¹ * x = g⁻¹ := by group
      rw [h1]
      exact L₁.inv_mem (hBL₁ g hg)
  have hPcard : Nat.card (L ⧸ L₁) = 21 := by
    rw [Nat.card_eq_fintype_card, hplane.card_points]
  have hcardL : Nat.card L = 80640 := by
    have h := Subgroup.card_mul_index L₁
    rw [Subgroup.index_eq_card, hPcard, hL₁] at h
    omega
  have hcardQB : Nat.card (L ⧸ B) = 20160 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup B
    rw [hcardL, hBcard] at h
    omega
  obtain ⟨-, -, -, hcomp4, -, -, -, -, -, -, -, hcardS, -, hnorm, hrel⟩ :=
    pg24_unique_and_collineation_group.{0}
  classical
  obtain ⟨e, he⟩ := hcomp4 (lineSet L₁ L₂) hplane
  set ψ : L →* Equiv.Perm PG24Point := e.permCongrHom.toMonoidHom.comp α with hψdef
  have hψapply : ∀ g : L, ψ g = e.permCongr (MulAction.toPerm g) := fun g => rfl
  have hψmem : ∀ g : L, ψ g ∈ blockAut PG24Lines := by
    intro g
    rw [mem_blockAut]
    intro B'
    rw [hψapply, he42id_map_permCongr, ← he]
    rw [mem_blockAut.1 (he42id_perm_mem_blockAut L₁ L₂ g) (B'.map e.symm.toEmbedding), he,
      he42id_map_symm_map]
  haveI := hnorm
  set ψ' : L →* ↥(blockAut PG24Lines) := ψ.codRestrict (blockAut PG24Lines) hψmem with hψ'
  set S := (rhoGL.comp slHom).range with hS
  have hNcard : Nat.card (↥(blockAut PG24Lines) ⧸ S.subgroupOf (blockAut PG24Lines)) = 6 := by
    rw [← Subgroup.index_eq_card]
    exact hrel
  haveI : Group.IsSolvable (↥(blockAut PG24Lines) ⧸ S.subgroupOf (blockAut PG24Lines)) :=
    he42id_isSolvable_of_card_six _ hNcard
  have hf := he42id_eq_one_of_perfect_of_solvable hperf
    ((QuotientGroup.mk' (S.subgroupOf (blockAut PG24Lines))).comp ψ')
  have hψS : ∀ g : L, ψ g ∈ S := by
    intro g
    have h1 := hf g
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  set ψS : L →* S := ψ.codRestrict S hψS with hψS_def
  have hψker_iff : ∀ g : L, ψ g = 1 ↔ α g = 1 := fun g =>
    map_eq_one_iff e.permCongrHom e.permCongrHom.injective
  have hψSker : ψS.ker = B := by
    rw [← hker_eq]
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hψker_iff g]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      exact h'
    · intro h
      exact Subtype.ext h
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hcardS]; norm_num)
  have hrange : ψS.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψS).toEquiv, hψSker, hcardQB,
      hcardS]
  have hsurj : Function.Surjective ψS := MonoidHom.range_eq_top.1 hrange
  let e₁ : L ⧸ B ≃* S := (QuotientGroup.quotientMulEquivOfEq hψSker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψS hsurj)
  let e₂ : L ⧸ B ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) CFSG.Fischer.F4 :=
    e₁.trans rangeSLEquivPSL
  have hcenter : Subgroup.center L = B := by
    apply le_antisymm
    · intro z hz
      have hz' : (z : L ⧸ B) ∈ Subgroup.center (L ⧸ B) := by
        rw [Subgroup.mem_center_iff]
        intro x
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hz g]
      have h1 : e₂ (z : L ⧸ B) ∈ Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 3)
          CFSG.Fischer.F4) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := e₂.surjective y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz' x]
      rw [he42id_center_psl34, Subgroup.mem_bot] at h1
      have h2 : (z : L ⧸ B) = 1 := (map_eq_one_iff e₂ e₂.injective).1 h1
      exact (QuotientGroup.eq_one_iff z).1 h2
    · intro b hb
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hBcent b hb g).symm
  refine ⟨hcenter, ?_⟩
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
    (e₂.symm.trans (QuotientGroup.quotientMulEquivOfEq hcenter.symm)) he42id_stated_psl34

end CFSG.Quasithin.A94.He42Ident
