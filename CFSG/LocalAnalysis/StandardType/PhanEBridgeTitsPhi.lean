module

public import CFSG.LocalAnalysis.StandardType.PhanEBridgeTitsBlock

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {M : CoxeterMatrix (Fin n)}
  {G : Type} [Group G]

theorem PhanFamilyE.ι_mem_parab (S : PhanFamilyE K 2 f M G) {J : Set (Fin n)} {j : Fin n}
    (hj : j ∈ J) (A : Su K 2 f 2) : S.ι j A ∈ S.parab J :=
  S.lsup_le_parab J (S.ι_mem_lsup hj A)

theorem PhanFamilyE.parab_mono (S : PhanFamilyE K 2 f M G) {J J' : Set (Fin n)} (h : J ⊆ J') :
    S.parab J ≤ S.parab J' :=
  sup_le_sup_left (biSup_mono fun _ hj => h hj) _

@[expose] def PhanFamilyE.Good.IsPhi {S : PhanFamilyE K 2 f M G} (hg : S.Good) {Y : Type}
    [Group Y] (F : PhanFamilyE K 2 f M Y) (J : Set (Fin n)) (φ : S.parab J →* Y) : Prop :=
  (∀ t : S.torus, φ ⟨t, S.torus_le_parab J t.2⟩ = hg.phiT F t) ∧
    ∀ (j : Fin n) (hj : j ∈ J) (A : Su K 2 f 2), φ ⟨S.ι j A, S.ι_mem_parab hj A⟩ = F.ι j A

private theorem hmbPhi_phiT_mTor {S : PhanFamilyE K 2 f M G} (hg : S.Good) {Y : Type}
    [Group Y] (F : PhanFamilyE K 2 f M Y) (t : Fin n → normOne (unitaryInvolution K 2 f))
    (h : S.mTor hg.simplyLaced t ∈ S.torus) :
    hg.phiT F ⟨S.mTor hg.simplyLaced t, h⟩ = F.mTor hg.simplyLaced t := by
  have hx : (MulEquiv.subgroupCongr (S.range_mTor hg.simplyLaced)).symm
        (⟨S.mTor hg.simplyLaced t, h⟩ : S.torus) =
      ⟨S.mTor hg.simplyLaced t, Set.mem_range_self t⟩ := Subtype.ext rfl
  change F.mTor hg.simplyLaced
    ((MonoidHom.ofInjective hg.mTor_injective).symm
      ((MulEquiv.subgroupCongr (S.range_mTor hg.simplyLaced)).symm
        (⟨S.mTor hg.simplyLaced t, h⟩ : S.torus))) = F.mTor hg.simplyLaced t
  rw [hx]
  exact congrArg (F.mTor hg.simplyLaced) (ofInjective_symm_apply_self hg.mTor_injective t _)

private theorem hmbPhi_conj_relation (hK : Nat.card K = (2 ^ f) ^ 2)
    {S : PhanFamilyE K 2 f M G} (hg : S.Good) {Y : Type} [Group Y]
    (F : PhanFamilyE K 2 f M Y) {J : Set (Fin n)} {φN : S.lsup J →* Y}
    (hφN : S.IsBlockHom F J φN) (hNT : S.torus ≤ Subgroup.normalizer (S.lsup J : Set G)) :
    ∀ (t : S.torus) (x : S.lsup J),
      hg.phiT F t * φN x * (hg.phiT F t)⁻¹ = φN (conjAutOfNormalizer hNT t x) := by
  intro t x
  let S₀ : Set G := ⋃ j ∈ J, ((S.ι j).range : Set G)
  have hSH : S₀ ⊆ (S.lsup J : Set G) := fun y hy => by
    obtain ⟨j, hj, hy'⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨A, rfl⟩ := Set.mem_range.mp hy'
    exact S.ι_mem_lsup hj A
  have hSN : Subgroup.closure {x : S.lsup J | (x : G) ∈ S₀} = ⊤ :=
    closure_eq_top_of_le_closure hSH (iSup₂_le fun j hj y hy =>
      Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨j, hj, hy⟩))
  have hST : Subgroup.closure (Set.univ : Set S.torus) = ⊤ := Subgroup.closure_univ
  refine forall_conj_of_gens hNT φN (hg.phiT F) hSN hST ?_ t x
  intro t' _ x' hx
  obtain ⟨j, hj, A, hA⟩ : ∃ j ∈ J, ∃ A : Su K 2 f 2, S.ι j A = (x' : G) := by
    obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨j, hj, Set.mem_range.mp hy⟩
  have hx' : x' = ⟨S.ι j A, S.ι_mem_lsup hj A⟩ := Subtype.ext hA.symm
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin n → normOne (unitaryInvolution K 2 f),
      S.mTor hg.simplyLaced τ = (t' : G) := by
    have ht : (t' : G) ∈ (S.mTor hg.simplyLaced).range := by
      rw [S.range_mTor hg.simplyLaced]; exact t'.2
    exact Set.mem_range.mp ht
  have ht' : t' = ⟨S.mTor hg.simplyLaced τ, hτ.symm ▸ t'.2⟩ := Subtype.ext hτ.symm
  have e1 : hg.phiT F t' = F.mTor hg.simplyLaced τ := by
    rw [ht']
    exact hmbPhi_phiT_mTor hg F τ _
  have e2 : (conjAutOfNormalizer hNT t' x' : S.lsup J) =
      ⟨S.ι j (conjDiag hK ![rhoE M j τ, 1] A), S.ι_mem_lsup hj _⟩ := by
    refine Subtype.ext ?_
    rw [coe_conjAutOfNormalizer, hx']
    change (t' : G) * S.ι j A * (t' : G)⁻¹ = S.ι j (conjDiag hK ![rhoE M j τ, 1] A)
    rw [ht']
    exact PhanFamilyE.mTor_conj_ι hK S hg.simplyLaced τ j A
  rw [e1, e2, hx', hφN j hj A, hφN j hj]
  exact PhanFamilyE.mTor_conj_ι hK F hg.simplyLaced τ j A

private theorem hmbPhi_isPhi_restrict {S : PhanFamilyE K 2 f M G} (hg : S.Good) {Y : Type}
    [Group Y] {F : PhanFamilyE K 2 f M Y} {J J' : Set (Fin n)} (h : J' ⊆ J)
    {φ : S.parab J →* Y} (hφ : hg.IsPhi F J φ) :
    hg.IsPhi F J' (φ.comp (Subgroup.inclusion (S.parab_mono h))) :=
  ⟨fun t => hφ.1 t, fun j hj A => hφ.2 j (h hj) A⟩

theorem PhanFamilyE.Good.exists_isPhi (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {S : PhanFamilyE K 2 f M G} (hg : S.Good) {Y : Type} [Group Y] (F : PhanFamilyE K 2 f M Y)
    {J : Set (Fin n)} (hJ : J.encard ≤ 2) : ∃ φ : S.parab J →* Y, hg.IsPhi F J φ := by
  have hNT : S.torus ≤ Subgroup.normalizer (S.lsup J : Set G) :=
    le_normalizer_iSup₂ S.torus J (fun j => (S.ι j).range)
      (fun j => PhanFamilyE.torus_le_normalizer hK S hg.simplyLaced j)
  obtain ⟨φN, hφN⟩ := hg.exists_blockHom hK hq F hJ
  obtain ⟨φ, hφL, hφT⟩ := exists_hom_sup_of_normalizes' hNT φN (hg.phiT F)
    (fun g hN hT => hg.blockHom_agree hJ hφN g hN hT)
    (fun t x => hmbPhi_conj_relation hK hg F hφN hNT t x)
  refine ⟨φ, fun t => hφT t, fun j hj A => ?_⟩
  exact (hφL ⟨S.ι j A, S.ι_mem_lsup hj A⟩).trans (hφN j hj A)

theorem PhanFamilyE.Good.isPhi_unique {S : PhanFamilyE K 2 f M G} (hg : S.Good) {Y : Type}
    [Group Y] {F : PhanFamilyE K 2 f M Y} {J : Set (Fin n)} {φ₁ φ₂ : S.parab J →* Y}
    (h₁ : hg.IsPhi F J φ₁) (h₂ : hg.IsPhi F J φ₂) : φ₁ = φ₂ := by
  let S₀ : Set G := ((S.mTor hg.simplyLaced).range : Set G) ∪
    ⋃ j ∈ J, ((S.ι j).range : Set G)
  have hS₀ : S₀ ⊆ (S.parab J : Set G) := by
    rintro x (hx | hx)
    · exact S.torus_le_parab J (by rwa [← S.range_mTor hg.simplyLaced])
    · obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.1 hx
      obtain ⟨A, rfl⟩ := Set.mem_range.mp hy
      exact S.ι_mem_parab hj A
  have hle : S.parab J ≤ Subgroup.closure S₀ :=
    sup_le
      (fun x hx => Subgroup.subset_closure (Or.inl (by rwa [S.range_mTor hg.simplyLaced])))
      (iSup₂_le fun j hj y hy =>
        Subgroup.subset_closure (Or.inr (Set.mem_iUnion₂.2 ⟨j, hj, hy⟩)))
  refine hom_ext_of_le_closure φ₁ φ₂ hS₀ hle ?_
  rintro x (hx | hx)
  · obtain ⟨τ, rfl⟩ := Set.mem_range.mp hx
    have hmem : S.mTor hg.simplyLaced τ ∈ S.torus := by
      rw [← S.range_mTor hg.simplyLaced]
      exact Set.mem_range_self τ
    exact (h₁.1 ⟨S.mTor hg.simplyLaced τ, hmem⟩).trans
      (h₂.1 ⟨S.mTor hg.simplyLaced τ, hmem⟩).symm
  · obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨A, rfl⟩ := Set.mem_range.mp hy
    exact (h₁.2 j hj A).trans (h₂.2 j hj A).symm

theorem PhanFamilyE.Good.exists_phi_family (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {S : PhanFamilyE K 2 f M G} (hg : S.Good) {Y : Type} [Group Y] (F : PhanFamilyE K 2 f M Y) :
    ∃ φ : ∀ J : Set (Fin n), J.encard ≤ 2 → S.parab J →* Y,
      (∀ (J : Set (Fin n)) (hJ : J.encard ≤ 2), hg.IsPhi F J (φ J hJ)) ∧
      ∀ (J J' : Set (Fin n)) (hJ : J.encard ≤ 2) (hJ' : J'.encard ≤ 2), J' ⊆ J →
        ∀ (g : G) (hgJ' : g ∈ S.parab J') (hgJ : g ∈ S.parab J),
          φ J' hJ' ⟨g, hgJ'⟩ = φ J hJ ⟨g, hgJ⟩ := by
  choose φ hφ using fun (J : Set (Fin n)) (hJ : J.encard ≤ 2) =>
    hg.exists_isPhi hK hq F hJ
  refine ⟨φ, hφ, fun J J' hJ hJ' h g hgJ' hgJ => ?_⟩
  have hcomp := hg.isPhi_unique (hφ J' hJ') (hmbPhi_isPhi_restrict hg h (hφ J hJ))
  exact DFunLike.congr_fun hcomp ⟨g, hgJ'⟩

end CFSG.ClassicalInvolution.Phan.PhanE
