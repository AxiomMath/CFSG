module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7NoBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246DoubleBlocks
public import CFSG.Quasithin.Background.C58Blocks

public section

namespace CFSG.Quasithin.C58NS.Emb

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem noCharNormal_of_noCommonNormal {T₁ P : Subgroup G}
    (hNC : C5.NoCommonNormal T₁ P (Subgroup.normalizer (T₁ : Set G))) (C : Subgroup G)
    (hC1 : C ≠ ⊥) (hCT : C ≤ T₁) (hCc : (C.subgroupOf T₁).Characteristic) :
    ¬ P ≤ Subgroup.normalizer (C : Set G) := fun hPC =>
  hNC C hCT hC1 hPC (normalizer_le_normalizer_of_characteristic hCT hCc)

omit [Finite G] in
theorem omegaOneCenter_ne_bot [Finite G] {T : Subgroup G} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    quasithinOmegaOneCenter T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
  have hcen : Nontrivial (Subgroup.center T) := hT2.center_nontrivial
  have hcard : 2 ∣ Nat.card (Subgroup.center T) := by
    rcases (hT2.to_subgroup (Subgroup.center T)).card_eq_or_dvd with h1 | h2
    · exact absurd h1 (Finite.one_lt_card).ne'
    · exact h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2 hcard
  intro hbot
  have hx2 : (x : T) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  have hxmem : ((x : T) : G) ∈ quasithinOmegaOneCenter T := by
    apply Subgroup.subset_closure
    refine ⟨⟨(x : T).2, ?_⟩, by simpa using congrArg Subtype.val hx2⟩
    refine Subgroup.mem_centralizer_iff.2 fun t ht => ?_
    have := Subgroup.mem_center_iff.1 x.2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  rw [hbot] at hxmem
  have hx1 : (x : T) = 1 := Subtype.ext (Subgroup.mem_bot.1 hxmem)
  have : (x : Subgroup.center T) = 1 := Subtype.ext hx1
  have h1 : orderOf x = 1 := by rw [this, orderOf_one]
  rw [hx] at h1
  omega

theorem not_le_centralizer_omega_of_noCharNormal {T K : Subgroup G} (hT2 : IsPGroup 2 T)
    (hT1 : T ≠ ⊥)
    (hnc : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      ¬ K ⊔ T ≤ Subgroup.normalizer (C : Set G)) :
    ¬ K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro hKZ
  refine hnc _ (omegaOneCenter_ne_bot hT2 hT1) (L246C127.omegaOneCenter_le_self T)
    (L246C127.characteristic_omegaOneCenter T) ?_
  exact sup_le (hKZ.trans (Subgroup.centralizer_le_normalizer _))
    ((L246C127.le_centralizer_omegaOneCenter T).trans (Subgroup.centralizer_le_normalizer _))

theorem pushUpObstruction_of {X T₁ P M : Subgroup G} (hmin : MinParabolic P T₁ M)
    (hcharP : CharTwo P) (hPX : P ≤ X) (hSQ : CFSG.SectionRank.IsSQTKCat ↥X)
    (hnc : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T₁ → (C.subgroupOf T₁).Characteristic →
      ¬ P ≤ Subgroup.normalizer (C : Set G)) :
    PushUpObstruction T₁ P := by
  have hPu : P ∈ uFamHat P T₁ := by
    refine ⟨⟨le_rfl, hmin.lt, ?_⟩, hmin.not_normal⟩
    have h : maxOver P T₁ = {M} := hmin.uniqueMax
    rw [h]
    exact Set.ncard_singleton _
  exact ⟨hmin.isSylow, hcharP, L238.isMinimalParabolic_of_mem_uFamHat hmin.isSylow hPu,
    L246A7.isSQTKCat_of_le hPX hSQ, fun C hC1 hCT hCc => hnc C hC1 hCT hCc⟩

theorem commutator_thompsonJ_eq_of_minParabolicBlocks (hMB : MinParabolicBlocks)
    {T₁ K₁ : Subgroup G} (hK : IsShort2 K₁) (hT₁K : T₁ ≤ Subgroup.normalizer (K₁ : Set G))
    (hobs : PushUpObstruction T₁ (K₁ ⊔ T₁)) : ⁅K₁, thompsonJ T₁⁆ = K₁ := by
  have hT2 : IsPGroup 2 T₁ := hobs.sylow.2.1
  obtain ⟨L, hL, hLJ, hPL, -⟩ := hMB G T₁ (K₁ ⊔ T₁) hobs
  have hO2 : oTwoUpper (K₁ ⊔ T₁) ≤ K₁ := C58.oTwoUpper_le_of_le_sup le_rfl hT2 hT₁K
  have hLK : L ≤ K₁ := by
    rw [C1Pack.isShort2_eq_oTwoUpper hL.1.1]
    exact (oTwoUpper_mono hL.1.2.1).trans hO2
  have hKJ : K₁ ≤ conjJoin T₁ L := by
    rw [C1Pack.isShort2_eq_oTwoUpper hK]
    refine (oTwoUpper_mono (le_sup_left : K₁ ≤ K₁ ⊔ T₁)).trans ?_
    exact C58.oTwoUpper_le_of_le_sup hPL.le hT2 L246Double.le_normalizer_conjJoin
  have hJT : thompsonJ T₁ ≤ T₁ := (C1GN.thompsonJ_le_baum T₁).trans (C1GN.baum_le T₁)
  refine le_antisymm (C1GN.commutator_le_of_le_normalizer (hJT.trans hT₁K)) ?_
  refine hKJ.trans (iSup_le fun s => ?_)
  have hsN : (s : G) ∈ Subgroup.normalizer (T₁ : Set G) := Subgroup.le_normalizer s.2
  have hJs : (thompsonJ T₁).map (MulAut.conj (s : G)).toMonoidHom = thompsonJ T₁ :=
    cjSub_thompsonJ hsN
  have hKs : K₁.map (MulAut.conj (s : G)).toMonoidHom = K₁ := by
    have := conjSubgroup_eq_iff_mem_normalizer.mpr (inv_mem (hT₁K s.2))
    simpa [conjSubgroup] using this
  calc L.map (MulAut.conj (s : G)).toMonoidHom
      = ⁅L, thompsonJ T₁⁆.map (MulAut.conj (s : G)).toMonoidHom := by rw [hLJ]
    _ = ⁅L.map (MulAut.conj (s : G)).toMonoidHom, thompsonJ T₁⁆ := by
        rw [Subgroup.map_commutator, hJs]
    _ ≤ ⁅K₁, thompsonJ T₁⁆ := by
        refine Subgroup.commutator_mono ?_ le_rfl
        rw [← hKs]
        exact Subgroup.map_mono hLK

end CFSG.Quasithin.C58NS.Emb
