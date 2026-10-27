module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Blk
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Odd
public import CFSG.Quasithin.EmptyFaithful.S1421QA15R
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem IsBenderQuot.of_mulEquiv {n : ℕ} {B B' : Type*} [Group B] [Group B'] (e : B ≃* B')
    (h : IsBenderQuot n B) : IsBenderQuot n B' := by
  rcases h with hL | ⟨a, ha, ⟨e1⟩⟩ | ⟨F, i1, i2, hF, ⟨e1⟩⟩ | ⟨F, i1, i2, hF, ⟨e1⟩⟩
  · obtain ⟨e1⟩ := hL
    exact Or.inl ⟨e.symm.trans e1⟩
  · exact Or.inr (Or.inl ⟨a, ha, ⟨e.symm.trans e1⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨F, i1, i2, hF, ⟨e.symm.trans e1⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨F, i1, i2, hF, ⟨e.symm.trans e1⟩⟩))

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.sylow_inf (c : Core3Ctx T M H K1 L M₁) : IsSylowTwoOf (sOf T K1 ⊓ L) L :=
  A4.isSylowTwoOf_inf_normal (isSylowTwoOf_g0 c.inM c.sylow) c.le_g0Of c.g0Of_le_normalizer

theorem Core3Ctx.bar_sylow (c : Core3Ctx T M H K1 L M₁) :
    IsSylowTwoOf (modO2Image L (sOf T K1 ⊓ L)) ⊤ :=
  isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf c.sylow_inf) _
    (QuotientGroup.mk'_surjective _)

theorem Core3Ctx.perfect_K1 (c : Core3Ctx T M H K1 L M₁) : ⁅K1, K1⁆ = K1 :=
  perfect_of_mem_cComp c.st.notation_.cComp_mem

theorem Core3Ctx.K1_ne_bot (c : Core3Ctx T M H K1 L M₁) : K1 ≠ ⊥ :=
  ne_bot_of_mem_cComp c.st.notation_.cComp_mem

theorem Core3Ctx.perfect_subgroupOf (c : Core3Ctx T M H K1 L M₁) :
    ⁅K1.subgroupOf L, K1.subgroupOf L⁆ = K1.subgroupOf L := by
  have : Group.IsPerfect ↥K1 := Subgroup.isPerfect_iff.2 c.perfect_K1
  have : Group.IsPerfect ↥(K1.subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe c.lt_L.le).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe c.lt_L.le).symm.surjective
  exact Subgroup.isPerfect_iff.1 this

theorem Core3Ctx.bar_perfect (c : Core3Ctx T M H K1 L M₁) :
    ⁅modO2Image L K1, modO2Image L K1⁆ = modO2Image L K1 := by
  unfold modO2Image
  rw [← Subgroup.map_commutator, c.perfect_subgroupOf]

theorem Core3Ctx.bar_ne_bot (c : Core3Ctx T M H K1 L M₁) : modO2Image L K1 ≠ ⊥ := by
  intro hbot
  have hle : K1.subgroupOf L ≤ CFSG.pCore 2 ↥L := by
    unfold modO2Image at hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  have h2 : IsPGroup 2 ↥(K1.subgroupOf L) := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).to_le hle
  have h2' : IsPGroup 2 ↥K1 :=
    h2.of_equiv (Subgroup.subgroupOfEquivOfLe c.lt_L.le)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hns := not_isSolvable_of_perfect_of_ne_bot c.perfect_K1 c.K1_ne_bot
  have hnil : Group.IsNilpotent ↥K1 := h2'.isNilpotent
  exact hns inferInstance

theorem Core3Ctx.bar_sup_ne_top (c : Core3Ctx T M H K1 L M₁) :
    modO2Image L K1 ⊔ modO2Image L (sOf T K1 ⊓ L) ≠ ⊤ := by
  intro htop
  have hker := pCore_le_subgroupOf_of_isSylowTwoOf c.sylow_inf
  have hsup : K1.subgroupOf L ⊔ (sOf T K1 ⊓ L).subgroupOf L = ⊤ := by
    have h1 : (K1.subgroupOf L ⊔ (sOf T K1 ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
      unfold modO2Image at htop
      rwa [← Subgroup.map_sup] at htop
    have h2 := congrArg (Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) h1
    rw [Subgroup.comap_map_eq, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
    rwa [sup_eq_left.mpr (hker.trans le_sup_right)] at h2
  have hSK' : (sOf T K1 ⊓ L).subgroupOf L ≤ Subgroup.normalizer (K1.subgroupOf L : Set ↥L) := by
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simpa [Subgroup.mem_subgroupOf] using
      Subgroup.mem_normalizer_iff.mp ((inf_le_right : sOf T K1 ≤ _) hs.1) (y : G)
  have hnorm : (K1.subgroupOf L).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le Subgroup.le_normalizer hSK'
  exact not_subnormal_of_mem_cComp c.mem c.lt_L c.K1_ne_bot c.perfect_K1
    (A3.subnormal_trans (A3.subnormal_of_normal c.lt_L.le hnorm) (subnormal_of_mem_cComp c.mem))

theorem Core3Ctx.bar_bender (c : Core3Ctx T M H K1 L M₁) :
    ∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot (modO2Image L K1)) := by
  obtain ⟨n, hn, hB⟩ := c.st.notation_.bender
  obtain ⟨e⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv c.lt_L.le
  refine ⟨n, hn, IsBenderQuot.of_mulEquiv ?_ hB⟩
  exact (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K1 2)).symm.trans
    (e.trans (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥(modO2Image L K1) 2)))

theorem Core3Ctx.bar_solvable (c : Core3Ctx T M H K1 L M₁) :
    Group.IsSolvable ↥(modO2Image L ((yOfL22 T M ⊔ sOf T K1) ⊓ L)) := by
  have hle : (yOfL22 T M ⊔ sOf T K1) ⊓ L ≤ yOfL22 T M ⊔ T :=
    inf_le_left.trans (sup_le_sup_left sOf_le_T _)
  have hDL : (yOfL22 T M ⊔ sOf T K1) ⊓ L ≤ L := inf_le_right
  have h1 : Group.IsSolvable ↥((yOfL22 T M ⊔ sOf T K1) ⊓ L) := by
    have := isSolvable_yOfL22_sup c.st
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have h2 : Group.IsSolvable ↥(((yOfL22 T M ⊔ sOf T K1) ⊓ L).subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hDL).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hDL).injective
  exact Group.isSolvable_of_surjective
    (f := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).subgroupMap _)
    (MonoidHom.subgroupMap_surjective _ _)

theorem Core3Ctx.le_normalizer_of_bar (c : Core3Ctx T M H K1 L M₁) (hY : yOfL22 T M ≤ L)
    (h : modO2Image L ((yOfL22 T M ⊔ sOf T K1) ⊓ L) ≤
      Subgroup.normalizer ((modO2Image L (sOf T K1 ⊓ L) : Subgroup _) : Set _)) :
    yOfL22 T M ≤ Subgroup.normalizer ((sOf T K1 ⊓ L : Subgroup G) : Set G) := by
  have hker := pCore_le_subgroupOf_of_isSylowTwoOf c.sylow_inf
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hmem : ∀ l : ↥L, π l ∈ modO2Image L (sOf T K1 ⊓ L) ↔ (l : G) ∈ sOf T K1 ⊓ L := by
    intro l
    have h1 := Subgroup.comap_map_eq_self (f := π) (H := (sOf T K1 ⊓ L).subgroupOf L)
      (by rw [hπ, QuotientGroup.ker_mk']; exact hker)
    have h2 : l ∈ Subgroup.comap π (modO2Image L (sOf T K1 ⊓ L)) ↔
        π l ∈ modO2Image L (sOf T K1 ⊓ L) := Iff.rfl
    unfold modO2Image at h2 ⊢
    rw [← h2, h1, Subgroup.mem_subgroupOf]
  intro y hy
  have hyL : y ∈ L := hY hy
  have hyD : y ∈ (yOfL22 T M ⊔ sOf T K1) ⊓ L := ⟨(le_sup_left : yOfL22 T M ≤ _) hy, hyL⟩
  have hyN : π ⟨y, hyL⟩ ∈ Subgroup.normalizer
      ((modO2Image L (sOf T K1 ⊓ L) : Subgroup _) : Set _) :=
    h ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.mpr hyD, rfl⟩
  rw [Subgroup.mem_normalizer_iff] at hyN ⊢
  have hconj : ∀ (s : G) (hsL : s ∈ L) (h1 : y * s * y⁻¹ ∈ L),
      π ⟨y, hyL⟩ * π ⟨s, hsL⟩ * (π ⟨y, hyL⟩)⁻¹ = π ⟨y * s * y⁻¹, h1⟩ := by
    intro s hsL h1
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  intro s
  constructor
  · intro hs
    have hsL : s ∈ L := hs.2
    have h1 : y * s * y⁻¹ ∈ L := L.mul_mem (L.mul_mem hyL hsL) (L.inv_mem hyL)
    have := (hyN (π ⟨s, hsL⟩)).mp ((hmem ⟨s, hsL⟩).mpr hs)
    rw [hconj s hsL h1] at this
    exact (hmem _).mp this
  · intro hs
    have h1 : y * s * y⁻¹ ∈ L := hs.2
    have hsL : s ∈ L := by
      have : s = y⁻¹ * (y * s * y⁻¹) * y := by group
      rw [this]
      exact L.mul_mem (L.mul_mem (L.inv_mem hyL) h1) hyL
    have hmemU : π ⟨y, hyL⟩ * π ⟨s, hsL⟩ * (π ⟨y, hyL⟩)⁻¹ ∈ modO2Image L (sOf T K1 ⊓ L) := by
      rw [hconj s hsL h1]
      exact (hmem _).mpr hs
    exact (hmem ⟨s, hsL⟩).mp ((hyN (π ⟨s, hsL⟩)).mpr hmemU)

end S1421

end CFSG.Quasithin
