module

public import CFSG.LocalAnalysis.StandardType.PhanEBridgeTitsTor

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {M : CoxeterMatrix (Fin n)}
  {G : Type} [Group G]

@[expose] noncomputable def PhanFamilyE.lsup (S : PhanFamilyE K 2 f M G) (J : Set (Fin n)) :
    Subgroup G :=
  ⨆ j ∈ J, (S.ι j).range

theorem PhanFamilyE.ι_mem_lsup (S : PhanFamilyE K 2 f M G) {J : Set (Fin n)} {j : Fin n}
    (hj : j ∈ J) (A : Su K 2 f 2) : S.ι j A ∈ S.lsup J :=
  (le_biSup (fun j => (S.ι j).range) hj) ⟨A, rfl⟩

theorem PhanFamilyE.lsup_le_parab (S : PhanFamilyE K 2 f M G) (J : Set (Fin n)) :
    S.lsup J ≤ S.parab J :=
  le_sup_right

@[expose] def PhanFamilyE.IsBlockHom {Y : Type} [Group Y] (S : PhanFamilyE K 2 f M G)
    (F : PhanFamilyE K 2 f M Y) (J : Set (Fin n)) (φN : S.lsup J →* Y) : Prop :=
  ∀ (j : Fin n) (hj : j ∈ J) (A : Su K 2 f 2), φN ⟨S.ι j A, S.ι_mem_lsup hj A⟩ = F.ι j A

private noncomputable def hmbBlock_rangeHom {S : PhanFamilyE K 2 f M G} (hg : S.Good)
    {Y : Type} [Group Y] (F : PhanFamilyE K 2 f M Y) (i : Fin n) :
    (S.ι i).range →* Y :=
  (F.ι i).comp (MonoidHom.ofInjective (hg.inj i)).symm.toMonoidHom

private theorem hmbBlock_rangeHom_apply {S : PhanFamilyE K 2 f M G} (hg : S.Good)
    {Y : Type} [Group Y] (F : PhanFamilyE K 2 f M Y) (i : Fin n)
    (x : (S.ι i).range) (A : Su K 2 f 2) (h : (x : G) = S.ι i A) :
    hmbBlock_rangeHom hg F i x = F.ι i A := by
  obtain ⟨x, hx⟩ := x
  subst h
  simp only [hmbBlock_rangeHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ofInjective_symm_apply_self]

private theorem hmbBlock_lsup_singleton {S : PhanFamilyE K 2 f M G} (i : Fin n) :
    S.lsup {i} = (S.ι i).range := by
  change (⨆ j ∈ ({i} : Set (Fin n)), (S.ι j).range) = (S.ι i).range
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun j hj => ?_
    rw [Set.mem_singleton_iff] at hj
    subst j
    exact le_rfl
  · exact le_biSup (fun j => (S.ι j).range) (Set.mem_singleton i)

private theorem hmbBlock_lsup_pair {S : PhanFamilyE K 2 f M G} (a b : Fin n) :
    S.lsup {a, b} = (S.ι a).range ⊔ (S.ι b).range := by
  change (⨆ j ∈ ({a, b} : Set (Fin n)), (S.ι j).range) = _
  exact iSup_pair (f := fun j => (S.ι j).range)

private theorem hmbBlock_left_apply {S : PhanFamilyE K 2 f M G} {a b : Fin n} (hab : a < b)
    (h3 : M a b = 3) (A : Su K 2 f 2) :
    S.θ a b (embSUid (unitaryInvolution K 2 f) 2 A) = S.ι a A :=
  DFunLike.congr_fun (S.left a b hab h3) A

private theorem hmbBlock_right_apply {S : PhanFamilyE K 2 f M G} {a b : Fin n} (hab : a < b)
    (h3 : M a b = 3) (A : Su K 2 f 2) :
    S.θ a b (embSUid (unitaryInvolution K 2 f) 0 A) = S.ι b A :=
  DFunLike.congr_fun (S.right a b hab h3) A

private theorem hmbBlock_lsup_le_theta {S : PhanFamilyE K 2 f M G} {a b : Fin n}
    (hab : a < b) (h3 : M a b = 3) : S.lsup {a, b} ≤ (S.θ a b).range := by
  change (⨆ j ∈ ({a, b} : Set (Fin n)), (S.ι j).range) ≤ (S.θ a b).range
  refine iSup₂_le fun j hj => ?_
  rcases hj with hj | hj
  · subst j
    rintro _ ⟨A, rfl⟩
    exact ⟨embSUid (unitaryInvolution K 2 f) 2 A, hmbBlock_left_apply hab h3 A⟩
  · rw [Set.mem_singleton_iff] at hj
    subst j
    rintro _ ⟨A, rfl⟩
    exact ⟨embSUid (unitaryInvolution K 2 f) 0 A, hmbBlock_right_apply hab h3 A⟩

private theorem hmbBlock_exists_blockHom_singleton {S : PhanFamilyE K 2 f M G} (hg : S.Good)
    {Y : Type} [Group Y] (F : PhanFamilyE K 2 f M Y) (i : Fin n) :
    ∃ φN : S.lsup {i} →* Y, S.IsBlockHom F {i} φN := by
  refine ⟨(F.ι i).comp ((MonoidHom.ofInjective (hg.inj i)).symm.toMonoidHom.comp
    (MulEquiv.subgroupCongr (hmbBlock_lsup_singleton i)).toMonoidHom), ?_⟩
  intro j hj A
  rw [Set.mem_singleton_iff] at hj
  subst j
  exact congrArg (F.ι i) (ofInjective_symm_apply_self (hg.inj i) A _)

private theorem hmbBlock_exists_blockHom_edge {S : PhanFamilyE K 2 f M G} (hg : S.Good)
    {Y : Type} [Group Y] (F : PhanFamilyE K 2 f M Y) {a b : Fin n} (hab : a < b)
    (h3 : M a b = 3) :
    ∃ φN : S.lsup {a, b} →* Y, S.IsBlockHom F {a, b} φN := by
  have hle := hmbBlock_lsup_le_theta (S := S) hab h3
  let ψ : S.lsup {a, b} →* Y :=
    ((F.θ a b).comp (MonoidHom.ofInjective (hg.θ_inj a b hab h3)).symm.toMonoidHom).comp
      (Subgroup.inclusion hle)
  have hψ : ∀ (x : S.lsup {a, b}) (B : Su K 2 f 3), (x : G) = S.θ a b B →
      ψ x = F.θ a b B := by
    intro x B hxB
    obtain ⟨x, hx⟩ := x
    subst hxB
    exact congrArg (F.θ a b) (ofInjective_symm_apply_self (hg.θ_inj a b hab h3) B _)
  refine ⟨ψ, fun j hj A => ?_⟩
  rcases hj with hj | hj
  · subst j
    refine (hψ _ (embSUid (unitaryInvolution K 2 f) 2 A) ?_).trans ?_
    · exact (hmbBlock_left_apply hab h3 A).symm
    · exact DFunLike.congr_fun (F.left a b hab h3) A
  · rw [Set.mem_singleton_iff] at hj
    subst j
    refine (hψ _ (embSUid (unitaryInvolution K 2 f) 0 A) ?_).trans ?_
    · exact (hmbBlock_right_apply hab h3 A).symm
    · exact DFunLike.congr_fun (F.right a b hab h3) A

private theorem hmbBlock_exists_blockHom_far {S : PhanFamilyE K 2 f M G} (hg : S.Good)
    {Y : Type} [Group Y] (F : PhanFamilyE K 2 f M Y) {a b : Fin n} (hab : a ≠ b)
    (h2 : M a b = 2) :
    ∃ φN : S.lsup {a, b} →* Y, S.IsBlockHom F {a, b} φN := by
  have hcomm : ∀ x ∈ (S.ι a).range, ∀ y ∈ (S.ι b).range, x * y = y * x := by
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact S.comm a b h2 A B
  have hNT : (S.ι b).range ≤ Subgroup.normalizer ((S.ι a).range : Set G) :=
    le_trans (fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx y hy)
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨φ, hφ1, hφ2⟩ := exists_hom_sup_of_normalizes hNT (hmbBlock_rangeHom hg F a)
    (hmbBlock_rangeHom hg F b)
    (fun g hN hT => by
      have hg1 : g ∈ (S.ι a).range ⊓ (S.ι b).range := ⟨hN, hT⟩
      rw [hg.disj a b hab, Subgroup.mem_bot] at hg1
      subst hg1
      have e1 : (⟨1, hN⟩ : (S.ι a).range) = 1 := rfl
      have e2 : (⟨1, hT⟩ : (S.ι b).range) = 1 := rfl
      rw [e1, e2, map_one, map_one])
    (fun t n => by
      obtain ⟨_, B, rfl⟩ := t
      obtain ⟨_, A, rfl⟩ := n
      have hc : conjAutOfNormalizer hNT ⟨S.ι b B, B, rfl⟩ ⟨S.ι a A, A, rfl⟩ =
          ⟨S.ι a A, A, rfl⟩ := by
        refine Subtype.ext ?_
        rw [coe_conjAutOfNormalizer]
        exact mul_inv_eq_iff_eq_mul.2 (hcomm _ ⟨A, rfl⟩ _ ⟨B, rfl⟩).symm
      rw [hc, hmbBlock_rangeHom_apply hg F b _ B rfl,
        hmbBlock_rangeHom_apply hg F a _ A rfl]
      exact mul_inv_eq_iff_eq_mul.2 (F.comm a b h2 A B).symm)
  refine ⟨φ.comp (MulEquiv.subgroupCongr (hmbBlock_lsup_pair a b)).toMonoidHom, ?_⟩
  intro j hj A
  rcases hj with hj | hj
  · subst hj
    exact (hφ1 ⟨S.ι j A, A, rfl⟩).trans (hmbBlock_rangeHom_apply hg F j _ A rfl)
  · rw [Set.mem_singleton_iff] at hj
    subst hj
    exact (hφ2 ⟨S.ι j A, A, rfl⟩).trans (hmbBlock_rangeHom_apply hg F j _ A rfl)

theorem PhanFamilyE.Good.exists_blockHom (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {S : PhanFamilyE K 2 f M G} (hg : S.Good) {Y : Type} [Group Y] (F : PhanFamilyE K 2 f M Y)
    {J : Set (Fin n)} (hJ : J.encard ≤ 2) : ∃ φN : S.lsup J →* Y, S.IsBlockHom F J φN := by
  rcases hJ.lt_or_eq with h | h
  · have h1 : J.encard ≤ 1 := by
      have : (2 : ℕ∞) = 1 + 1 := by norm_num
      rw [this] at h
      exact (ENat.lt_add_one_iff (by simp)).1 h
    rcases Set.encard_le_one_iff_eq.1 h1 with rfl | ⟨a, rfl⟩
    · exact ⟨1, fun j hj => absurd hj (by simp)⟩
    · exact hmbBlock_exists_blockHom_singleton hg F a
  · obtain ⟨a, b, hab, rfl⟩ := Set.encard_eq_two.1 h
    by_cases h3 : M a b = 3
    · rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact hmbBlock_exists_blockHom_edge hg F hlt h3
      · have h3' : M b a = 3 := (M.symmetric b a).trans h3
        obtain ⟨φN, hφN⟩ := hmbBlock_exists_blockHom_edge hg F hgt h3'
        have hpair : S.lsup {a, b} = S.lsup {b, a} := by rw [Set.pair_comm]
        refine ⟨φN.comp (MulEquiv.subgroupCongr hpair).toMonoidHom, ?_⟩
        intro j hj A
        exact hφN j (by rwa [Set.pair_comm b a]) A
    · have h2 : M a b = 2 := (hg.simplyLaced a b hab).resolve_right h3
      exact hmbBlock_exists_blockHom_far hg F hab h2

theorem PhanFamilyE.Good.blockHom_agree {S : PhanFamilyE K 2 f M G} (hg : S.Good) {Y : Type}
    [Group Y] {F : PhanFamilyE K 2 f M Y} {J : Set (Fin n)} (hJ : J.encard ≤ 2)
    {φN : S.lsup J →* Y} (hφ : S.IsBlockHom F J φN) (g : G) (hN : g ∈ S.lsup J)
    (hT : g ∈ S.torus) : φN ⟨g, hN⟩ = hg.phiT F ⟨g, hT⟩ := by
  let TJ : Subgroup G := ⨆ j : J, (S.nodeTor (j : Fin n)).range
  have hTJe : TJ = ⨆ j ∈ J, (S.nodeTor j).range :=
    iSup_subtype'' J (fun j => (S.nodeTor j).range)
  have hleN : TJ ≤ S.lsup J := by
    rw [hTJe]
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨x, rfl⟩
    exact S.ι_mem_lsup hj (torusTwo (unitaryInvolution K 2 f) x)
  have hleT : TJ ≤ S.torus := by
    rw [hTJe]
    change (⨆ j ∈ J, (S.nodeTor j).range) ≤ ⨆ i, (S.nodeTor i).range
    exact iSup₂_le fun j _ => le_iSup (fun i => (S.nodeTor i).range) j
  have hmem : g ∈ TJ := by
    have h := hg.torus_inf J hJ
    rw [← hTJe] at h
    rw [← h]
    exact ⟨hN, hT⟩
  let φ₁ : TJ →* Y := φN.comp (Subgroup.inclusion hleN)
  let φ₂ : TJ →* Y := (hg.phiT F).comp (Subgroup.inclusion hleT)
  let S₀ : Set G := ⋃ j ∈ J, ((S.nodeTor j).range : Set G)
  have hSH : S₀ ⊆ TJ := by
    rw [hTJe]
    intro x hx
    obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨y, rfl⟩ := hy
    exact (le_biSup (fun j => (S.nodeTor j).range) hj) ⟨y, rfl⟩
  have hTJle : TJ ≤ Subgroup.closure S₀ := by
    rw [hTJe]
    exact iSup₂_le fun j hj x hx => Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨j, hj, hx⟩)
  have hgen : φ₁ = φ₂ := by
    refine hom_ext_of_le_closure (S := S₀) φ₁ φ₂ hSH hTJle ?_
    intro x hx
    obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨y, rfl⟩ := hy
    have e1 : φ₁ ⟨S.nodeTor j y, hSH hx⟩ = F.nodeTor j y :=
      hφ j hj (torusTwo (unitaryInvolution K 2 f) y)
    have e2 : φ₂ ⟨S.nodeTor j y, hSH hx⟩ = F.nodeTor j y :=
      hg.phiT_nodeTor F j y (hleT (hSH hx))
    rw [e1, e2]
  have hφeq : φ₁ ⟨g, hmem⟩ = φ₂ ⟨g, hmem⟩ := by rw [hgen]
  have h1 : φ₁ ⟨g, hmem⟩ = φN ⟨g, hN⟩ := by
    change φN ⟨g, hleN hmem⟩ = φN ⟨g, hN⟩
    exact congrArg φN (Subtype.ext rfl)
  have h2 : φ₂ ⟨g, hmem⟩ = hg.phiT F ⟨g, hT⟩ := by
    change hg.phiT F ⟨g, hleT hmem⟩ = hg.phiT F ⟨g, hT⟩
    exact congrArg (hg.phiT F) (Subtype.ext rfl)
  rw [h1, h2] at hφeq
  exact hφeq

end CFSG.ClassicalInvolution.Phan.PhanE
