module

public import CFSG.Quasithin.EmptyFaithful.S1421Surv
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceDefs
public import CFSG.Quasithin.Background.A3ComponentsCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1421Elim

variable {G : Type} [Group G]

theorem isSolvable_of_isSolvable_oTwoQuot [Finite G] {H : Subgroup G}
    (h : Group.IsSolvable (OTwoQuot H)) : Group.IsSolvable ↥H := by
  have : (CFSG.Open.pCore 2 ↥H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have : Group.IsSolvable (CFSG.Open.pCore 2 ↥H) := by
    have := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥H) 2).isNilpotent
    infer_instance
  have : Group.IsSolvable (↥H ⧸ CFSG.Open.pCore 2 ↥H) := h
  exact Group.isSolvable_of_subgroup_quotient (CFSG.Open.pCore 2 ↥H)

theorem not_isSolvable_oTwoQuot_of_mem_cComp [Finite G] {K1 X : Subgroup G}
    (hK1 : K1 ∈ cComp X) : ¬ Group.IsSolvable (OTwoQuot K1) :=
  fun h => not_isSolvable_of_mem_cComp hK1 (isSolvable_of_isSolvable_oTwoQuot h)

theorem isSolvable_of_le_of_isSolvable {K X : Subgroup G} (hKX : K ≤ X)
    (hX : Group.IsSolvable ↥X) : Group.IsSolvable ↥K :=
  Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKX)

theorem not_isBlock2_of_oTwoQuot_perm3 {L : Subgroup G}
    (hS3 : Nonempty (OTwoQuot L ≃* Equiv.Perm (Fin 3))) : ¬ IsBlock2 L L := by
  rintro ⟨hshort, -, -⟩
  obtain ⟨e⟩ := hS3
  let φ : ↥L →* ℤˣ :=
    Equiv.Perm.sign.comp (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)))
  have : φ.ker.Normal := MonoidHom.normal_ker φ
  have hp : IsPGroup 2 (↥L ⧸ φ.ker) := by
    intro g
    refine ⟨1, ?_⟩
    induction g using QuotientGroup.induction_on with
    | H x =>
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
      exact Int.units_sq _
  have htop : φ.ker = ⊤ := hshort.1 φ.ker hp
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥L) (e.symm (Equiv.swap 0 1))
  have h1 : φ x = 1 := by
    have : x ∈ φ.ker := htop ▸ Subgroup.mem_top x
    exact this
  have h2 : φ x = -1 := by
    simp only [φ, MonoidHom.comp_apply, hx, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulEquiv.apply_symm_apply]
    exact Equiv.Perm.sign_swap (by decide)
  rw [h1] at h2
  exact absurd h2 (by decide)

theorem eq_one_of_isL2Quot_of_perm3 (hF : ListedGroupFacts) {L : Subgroup G}
    (hS3 : Nonempty (OTwoQuot L ≃* Equiv.Perm (Fin 3))) {f : ℕ} (hf : 1 ≤ f)
    (h : IsL2Quot f (OTwoQuot L)) : f = 1 := by
  by_contra hne
  exact hF.l2_ne_perm3 f (by omega) _ h hS3

theorem false_of_isL2Quot_of_perm3 (hF : ListedGroupFacts) {L : Subgroup G}
    (hS3 : Nonempty (OTwoQuot L ≃* Equiv.Perm (Fin 3))) {f : ℕ} (hf : 2 ≤ f)
    (h : IsL2Quot f (OTwoQuot L)) : False :=
  hF.l2_ne_perm3 f hf _ h hS3

theorem le_normalizer_of_card_center_eq_two [Finite G] {L Z : Subgroup G}
    (hcard : Nat.card (Subgroup.center ↥(pCoreOf 2 L)) = 2) (hZ2 : Nat.card Z = 2)
    (hZP : Z ≤ pCoreOf 2 L) (hZc : Z ≤ Subgroup.centralizer (pCoreOf 2 L : Set G)) :
    L ≤ Subgroup.normalizer (Z : Set G) := by
  set P := pCoreOf 2 L with hP
  have hle : Z ≤ (Subgroup.center ↥P).map P.subtype := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hZP hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hZc hx g.1 g.2)
  have hcardZ : Nat.card ((Subgroup.center ↥P).map P.subtype) = 2 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hcard]
  have hZeq : Z = (Subgroup.center ↥P).map P.subtype :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardZ, hZ2])
  rw [hZeq]
  exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

end S1421Elim

open S1421Elim

section Elim

variable {G : Type} [Group G] [Finite G]

theorem f112_unswapped_legacyBare {K1 L2 S : Subgroup G} (hF : ListedGroupFacts)
    (hK1 : K1 ∈ cComp (K1 ⊔ S)) (hS3 : Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3)))
    (hl : F112ListBare K1 L2 S) : F112SurvivorLegacyBare K1 L2 S := by
  have hnsK : ¬ Group.IsSolvable ↥K1 := not_isSolvable_of_mem_cComp hK1
  have hnsQ : ¬ Group.IsSolvable (OTwoQuot K1) := not_isSolvable_oTwoQuot_of_mem_cComp hK1
  have hblk : ¬ IsBlock2 L2 L2 := not_isBlock2_of_oTwoQuot_perm3 hS3
  have hnsKS : ¬ Group.IsSolvable ↥(K1 ⊔ S) := fun h =>
    hnsK (isSolvable_of_le_of_isSolvable le_sup_left h)
  unfold F112ListBare at hl
  unfold F112SurvivorLegacyBare
  dsimp only at hl ⊢
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  ·
    exfalso
    obtain ⟨f, hf, -, h⟩ := h1
    rcases h with ⟨-, -, -, hb, -⟩ | ⟨-, ⟨e⟩, -⟩
    · exact hblk hb
    · exact hnsK (hF.perm4_solvable _ ⟨e⟩)
  ·
    exfalso
    obtain ⟨f, hf, -, h⟩ := h2
    rcases h with ⟨-, -, -, hb, -⟩ | ⟨-, ⟨e⟩, -⟩
    · exact hblk hb
    · exact hnsKS (hF.z2perm4_solvable _ ⟨e⟩)
  ·
    exfalso
    obtain ⟨f, hf, -, hq1, hq2, -⟩ := h3
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 hf hq2
    subst this
    exact hnsQ (hF.l2_one_solvable _ hq1)
  ·
    obtain ⟨f, hf, hA, hq1, hsp, hq2, hcard⟩ := h4
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 hf hq2
    subst this
    exact Or.inl ⟨hA, hq1, hsp, hq2, hcard⟩
  ·
    exfalso
    obtain ⟨a, -, ⟨e⟩, -, hq2, -⟩ := h5
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 (by omega) hq2
    have ha : a = 0 := by omega
    subst ha
    exact hnsQ (hF.sz0_solvable _ ⟨e⟩)
  ·
    exfalso
    obtain ⟨f, hf, -, -, -, -, hq2, -⟩ := h6
    exact false_of_isL2Quot_of_perm3 hF hS3 (by omega) hq2
  ·
    exfalso
    obtain ⟨-, -, -, hq2, -⟩ := h7
    exact false_of_isL2Quot_of_perm3 hF hS3 (by norm_num) hq2
  ·
    exfalso
    obtain ⟨-, hq1, -⟩ := h8
    exact hnsQ (hF.l2_one_solvable _ hq1)
  ·
    exfalso
    obtain ⟨-, hq, -⟩ := h9
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact hnsQ (hF.dihedral5_solvable _ ⟨e⟩)
    · exact hnsQ (hF.sz0_solvable _ ⟨e⟩)
  ·
    exact Or.inr (Or.inl h10)
  ·
    exact Or.inr (Or.inr h11)
  ·
    exfalso
    obtain ⟨-, hq1, -⟩ := h12
    exact hnsQ (hF.l2_one_solvable _ hq1)
  ·
    exfalso
    obtain ⟨-, hq1, -⟩ := h13
    exact hnsQ (hF.l2_one_solvable _ hq1)

theorem f112_swapped_legacyBare {K1 L2 S : Subgroup G} (hF : ListedGroupFacts)
    (hK1 : K1 ∈ cComp (K1 ⊔ S)) (hS3 : Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3)))
    (hsolv : Group.IsSolvable ↥(L2 ⊔ S))
    (Zs : Subgroup G) (hZ2 : Nat.card Zs = 2) (hZP : Zs ≤ pCoreOf 2 L2)
    (hZc : Zs ≤ Subgroup.centralizer (pCoreOf 2 L2 : Set G))
    (hZn : ¬ L2 ≤ Subgroup.normalizer (Zs : Set G)) (hl : F112ListBare L2 K1 S) : False := by
  have hnsK : ¬ Group.IsSolvable ↥K1 := not_isSolvable_of_mem_cComp hK1
  have hnsQ : ¬ Group.IsSolvable (OTwoQuot K1) := not_isSolvable_oTwoQuot_of_mem_cComp hK1
  have hblk : ¬ IsBlock2 L2 L2 := not_isBlock2_of_oTwoQuot_perm3 hS3
  have hnsKS : ¬ Group.IsSolvable ↥(K1 ⊔ S) := fun h =>
    hnsK (isSolvable_of_le_of_isSolvable le_sup_left h)
  unfold F112ListBare at hl
  dsimp only at hl
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  ·
    obtain ⟨f, hf, -, h⟩ := h1
    rcases h with ⟨-, hb, -, -, -⟩ | ⟨-, -, ⟨e⟩⟩
    · exact hblk hb
    · exact hnsK (hF.perm4_solvable _ ⟨e⟩)
  ·
    obtain ⟨f, hf, -, h⟩ := h2
    rcases h with ⟨-, hb, -, -, -⟩ | ⟨-, -, ⟨e⟩⟩
    · exact hblk hb
    · exact hnsKS (hF.z2perm4_solvable _ ⟨e⟩)
  ·
    obtain ⟨f, hf, -, hq1, hq2, -⟩ := h3
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 hf hq1
    subst this
    exact hnsQ (hF.l2_one_solvable _ hq2)
  ·
    obtain ⟨f, hf, -, hq1, -⟩ := h4
    exact false_of_isL2Quot_of_perm3 hF hS3 (by omega) hq1
  ·
    obtain ⟨a, -, ⟨e⟩, -⟩ := h5
    exact hF.sz_ne_perm3 a _ ⟨e⟩ hS3
  ·
    obtain ⟨f, hf, -, hq1, hsp, -⟩ := h6
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 hf hq1
    subst this
    have hc : Nat.card (Subgroup.center ↥(pCoreOf 2 L2)) = 2 := by
      have := hsp.2.2
      rwa [pow_one] at this
    exact hZn (le_normalizer_of_card_center_eq_two hc hZ2 hZP hZc)
  ·
    obtain ⟨-, ⟨F, _, _, hFc, ⟨e⟩⟩, -⟩ := h7
    exact hF.su3_ne_perm3 _ F hFc ⟨e⟩ hS3
  ·
    obtain ⟨-, -, hq2, -⟩ := h8
    exact hnsQ (hF.l2_one_solvable _ hq2)
  ·
    obtain ⟨-, hq, -⟩ := h9
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact hF.dihedral5_ne_perm3 _ ⟨e⟩ hS3
    · exact hF.sz_ne_perm3 0 _ ⟨e⟩ hS3
  ·
    obtain ⟨-, hq1, -⟩ := h10
    exact false_of_isL2Quot_of_perm3 hF hS3 (by norm_num) hq1
  ·
    obtain ⟨-, ⟨e⟩, -⟩ := h11
    have : Group.IsSolvable (OTwoQuot (L2 ⊔ S)) := inferInstance
    exact hF.perm5_not_solvable _ ⟨e⟩ this
  ·
    obtain ⟨-, -, -, hq2, -⟩ := h12
    exact hnsQ (hF.l2_one_solvable _ hq2)
  ·
    obtain ⟨-, -, -, hq2, -⟩ := h13
    exact hnsQ (hF.l2_one_solvable _ hq2)

theorem f112_unswapped {K1 L2 S : Subgroup G} (hF : ListedGroupFacts)
    (hK1 : K1 ∈ cComp (K1 ⊔ S)) (hS3 : Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3)))
    (hl : F112List K1 L2 S) : F112Survivor K1 L2 S := by
  have hnsK : ¬ Group.IsSolvable ↥K1 := not_isSolvable_of_mem_cComp hK1
  have hnsQ : ¬ Group.IsSolvable (OTwoQuot K1) := not_isSolvable_oTwoQuot_of_mem_cComp hK1
  have hblk : ¬ IsBlock2 L2 L2 := not_isBlock2_of_oTwoQuot_perm3 hS3
  have hnsKS : ¬ Group.IsSolvable ↥(K1 ⊔ S) := fun h =>
    hnsK (isSolvable_of_le_of_isSolvable le_sup_left h)
  unfold F112List at hl
  unfold F112Survivor
  dsimp only at hl ⊢
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  ·
    exfalso
    obtain ⟨f, hf, -, h⟩ := h1
    rcases h with ⟨-, -, -, hb, -⟩ | ⟨-, ⟨e⟩, -⟩
    · exact hblk hb
    · exact hnsKS (hF.perm4_solvable _ ⟨e⟩)
  ·
    exfalso
    obtain ⟨f, hf, -, h⟩ := h2
    rcases h with ⟨-, -, -, hb, -⟩ | ⟨-, ⟨e⟩, -⟩
    · exact hblk hb
    · exact hnsKS (hF.z2perm4_solvable _ ⟨e⟩)
  ·
    exfalso
    obtain ⟨f, hf, -, hq1, hq2, -⟩ := h3
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 hf hq2
    subst this
    exact hnsQ (hF.l2_one_solvable _ hq1)
  ·
    obtain ⟨f, hf, hA, hq1, hsp, hq2, hcard⟩ := h4
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 hf hq2
    subst this
    exact Or.inl ⟨hA, hq1, hsp, hq2, hcard⟩
  ·
    exfalso
    obtain ⟨a, -, hsz, -, hq2, -⟩ := h5
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 (by omega) hq2
    have ha : a = 0 := by omega
    subst ha
    rcases hsz with ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · exact hnsQ (hF.sz0_solvable _ ⟨e⟩)
    · exact hnsQ (hF.dihedral5_solvable _ ⟨e⟩)
  ·
    exfalso
    obtain ⟨-, -, -, -, -, hb, -⟩ := h6
    exact hblk hb
  ·
    exfalso
    obtain ⟨-, -, -, hq2, -⟩ := h7
    exact false_of_isL2Quot_of_perm3 hF hS3 (by norm_num) hq2
  ·
    exfalso
    obtain ⟨-, hq1, -⟩ := h8
    exact hnsQ (hF.l2_one_solvable _ hq1)
  ·
    exfalso
    obtain ⟨-, hq, -⟩ := h9
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact hnsQ (hF.dihedral5_solvable _ ⟨e⟩)
    · exact hnsQ (hF.sz0_solvable _ ⟨e⟩)
  ·
    exact Or.inr (Or.inl h10)
  ·
    exact Or.inr (Or.inr h11)
  ·
    exfalso
    obtain ⟨-, hq1, -⟩ := h12
    exact hnsQ (hF.l2_one_solvable _ hq1)
  ·
    exfalso
    obtain ⟨-, hq1, -⟩ := h13
    exact hnsQ (hF.l2_one_solvable _ hq1)

theorem f112_swapped {K1 L2 S : Subgroup G} (hF : ListedGroupFacts)
    (hK1 : K1 ∈ cComp (K1 ⊔ S)) (hS3 : Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3)))
    (hsolv : Group.IsSolvable ↥(L2 ⊔ S))
    (Zs : Subgroup G) (hZ2 : Nat.card Zs = 2)
    (hZP : Zs ≤ pCoreOf 2 (L2 ⊔ bigB K1 L2 S))
    (hZc : Zs ≤ Subgroup.centralizer (pCoreOf 2 (L2 ⊔ bigB K1 L2 S) : Set G))
    (hZn : ¬ L2 ≤ Subgroup.normalizer (Zs : Set G)) (hl : F112List L2 K1 S) : False := by
  have hnsK : ¬ Group.IsSolvable ↥K1 := not_isSolvable_of_mem_cComp hK1
  have hnsQ : ¬ Group.IsSolvable (OTwoQuot K1) := not_isSolvable_oTwoQuot_of_mem_cComp hK1
  have hblk : ¬ IsBlock2 L2 L2 := not_isBlock2_of_oTwoQuot_perm3 hS3
  have hnsKS : ¬ Group.IsSolvable ↥(K1 ⊔ S) := fun h =>
    hnsK (isSolvable_of_le_of_isSolvable le_sup_left h)
  unfold F112List at hl
  dsimp only at hl
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  ·
    obtain ⟨f, hf, -, h⟩ := h1
    rcases h with ⟨-, hb, -, -, -⟩ | ⟨-, -, ⟨e⟩⟩
    · exact hblk hb
    · exact hnsKS (hF.perm4_solvable _ ⟨e⟩)
  ·
    obtain ⟨f, hf, -, h⟩ := h2
    rcases h with ⟨-, hb, -, -, -⟩ | ⟨-, -, ⟨e⟩⟩
    · exact hblk hb
    · exact hnsKS (hF.z2perm4_solvable _ ⟨e⟩)
  ·
    obtain ⟨f, hf, -, hq1, hq2, -⟩ := h3
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 hf hq1
    subst this
    exact hnsQ (hF.l2_one_solvable _ hq2)
  ·
    obtain ⟨f, hf, -, hq1, -⟩ := h4
    exact false_of_isL2Quot_of_perm3 hF hS3 (by omega) hq1
  ·
    obtain ⟨a, -, hsz, -⟩ := h5
    rcases hsz with ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · exact hF.sz_ne_perm3 a _ ⟨e⟩ hS3
    · exact hF.dihedral5_ne_perm3 _ ⟨e⟩ hS3
  ·
    obtain ⟨f, hf, -, hq1, hsp, -⟩ := h6
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 hf hq1
    subst this
    rw [bigB_comm K1 L2 S] at hsp
    have hc : Nat.card (Subgroup.center ↥(pCoreOf 2 (L2 ⊔ bigB K1 L2 S))) = 2 := by
      have := hsp.2.2
      rwa [pow_one] at this
    exact hZn (le_sup_left.trans (le_normalizer_of_card_center_eq_two hc hZ2 hZP hZc))
  ·
    obtain ⟨-, ⟨F, _, _, hFc, ⟨e⟩⟩, -⟩ := h7
    exact hF.su3_ne_perm3 _ F hFc ⟨e⟩ hS3
  ·
    obtain ⟨-, -, hq2, -⟩ := h8
    exact hnsQ (hF.l2_one_solvable _ hq2)
  ·
    obtain ⟨-, hq, -⟩ := h9
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact hF.dihedral5_ne_perm3 _ ⟨e⟩ hS3
    · exact hF.sz_ne_perm3 0 _ ⟨e⟩ hS3
  ·
    obtain ⟨-, hq1, -⟩ := h10
    exact false_of_isL2Quot_of_perm3 hF hS3 (by norm_num) hq1
  ·
    obtain ⟨-, ⟨e⟩, -⟩ := h11
    have : Group.IsSolvable (OTwoQuot (L2 ⊔ S)) := inferInstance
    exact hF.perm5_not_solvable _ ⟨e⟩ this
  ·
    obtain ⟨-, -, -, hq2, -⟩ := h12
    exact hnsQ (hF.l2_one_solvable _ hq2)
  ·
    obtain ⟨-, -, -, hq2, -⟩ := h13
    exact hnsQ (hF.l2_one_solvable _ hq2)

end Elim

theorem f112_survivor_legacyBare {G : Type} [Group G] [Finite G] {K1 L2 S : Subgroup G}
    (hF : ListedGroupFacts)
    (hK1 : K1 ∈ cComp (K1 ⊔ S))
    (hS3 : Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3)))
    (hsolv : Group.IsSolvable ↥(L2 ⊔ S))
    (Zs : Subgroup G) (hZ2 : Nat.card Zs = 2) (hZP : Zs ≤ pCoreOf 2 L2)
    (hZc : Zs ≤ Subgroup.centralizer (pCoreOf 2 L2 : Set G))
    (hZn : ¬ L2 ≤ Subgroup.normalizer (Zs : Set G))
    (h : ∃ L1' L2' : Subgroup G, ((L1' = K1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = K1)) ∧
      F112ListBare L1' L2' S) :
    F112SurvivorLegacyBare K1 L2 S := by
  obtain ⟨L1', L2', hor, hl⟩ := h
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at hl
    exact f112_unswapped_legacyBare hF hK1 hS3 hl
  · rw [h1, h2] at hl
    exact (f112_swapped_legacyBare hF hK1 hS3 hsolv Zs hZ2 hZP hZc hZn hl).elim

theorem f112_survivor {G : Type} [Group G] [Finite G] {K1 L2 S : Subgroup G}
    (hF : ListedGroupFacts)
    (hyp : Hyp111 K1 L2 S)
    (hqt : IsQuasithinSub (K1 ⊔ L2 ⊔ S))
    (hnorm : (S.subgroupOf (S ⊔ borelOf L2 S)).Normal)
    (hK1 : K1 ∈ cComp (K1 ⊔ S))
    (hS3 : Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3)))
    (hsolv : Group.IsSolvable ↥(L2 ⊔ S))
    (Zs : Subgroup G) (hZ2 : Nat.card Zs = 2)
    (hZP : Zs ≤ pCoreOf 2 (L2 ⊔ bigB K1 L2 S))
    (hZc : Zs ≤ Subgroup.centralizer (pCoreOf 2 (L2 ⊔ bigB K1 L2 S) : Set G))
    (hZn : ¬ L2 ≤ Subgroup.normalizer (Zs : Set G))
    (h : F112Concl K1 L2 S) : F112Survivor K1 L2 S := by
  obtain ⟨L1', L2', hor, -, hl, -⟩ := h
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at hl
    exact f112_unswapped hF hK1 hS3 hl
  · rw [h1, h2] at hl
    exact (f112_swapped hF hK1 hS3 hsolv Zs hZ2 hZP hZc hZn hl).elim

end CFSG.Quasithin
