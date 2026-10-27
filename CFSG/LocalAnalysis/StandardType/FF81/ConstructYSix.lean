module

public import CFSG.LocalAnalysis.StandardType.FF81.CurtisA2Linear
public import CFSG.LocalAnalysis.StandardType.FF81.ConstructYBlocks
public import CFSG.LocalAnalysis.StandardType.FF81.ConstructYLin
import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23 B12_sup_B23 blockSL2)
open scoped MatrixGroups

theorem center_specialLinearGroup_zmod_two (m : ℕ) : Subgroup.center SL(m + 1, ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 r with rfl | rfl
  · rw [Fintype.card_fin, zero_pow (Nat.succ_ne_zero m)] at hr
    exact absurd hr zero_ne_one
  · rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hA, map_one]
    rfl

theorem A2System.exists_injective_marking {G : Type} [Group G] {m : ℕ} (hm : 3 ≤ m)
    {U : Fin m → Subgroup G} {X : Subgroup G} (h : A2System adjA U X) :
    ∃ ψ : SL(m + 1, ZMod 2) →* G, Function.Injective ψ ∧ ψ.range = X ∧
      ∀ i, (blockSL2 (ZMod 2) m i).range.map ψ = U i := by
  obtain ⟨ψ0, hsurj, hker, hblk, -, -⟩ :=
    exists_marking_of_a2System_linear m hm ↥X (fun i => (U i).subgroupOf X) h.subgroupOf
  have hle : ∀ i, U i ≤ X := fun i => h.2.1 ▸ le_iSup U i
  refine ⟨X.subtype.comp ψ0, ?_, ?_, fun i => ?_⟩
  · have hinj0 : Function.Injective ψ0 := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans (center_specialLinearGroup_zmod_two m).le
    exact X.subtype_injective.comp hinj0
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · rw [← Subgroup.map_map, hblk i, Subgroup.subgroupOf_map_subtype, inf_of_le_left (hle i)]

theorem LinearBlockStandardPair.exists_conj_two {G : Type} [Group G] {W U V : Subgroup G}
    (h : LinearBlockStandardPair (ZMod 2) W U V) :
    ∃ β ∈ U ⊔ V, U.map (MulAut.conj β).toMonoidHom = V := by
  obtain ⟨θ, c, -, -, himg⟩ := h
  set β' : SL(3, ZMod 2) := c⁻¹ * Blocks.swap3 * c with hβ'
  have hmap : ∀ H : Subgroup SL(3, ZMod 2),
      ((H.map (MulAut.conj c⁻¹).toMonoidHom).map θ).map (MulAut.conj (θ β')).toMonoidHom =
        ((H.map (MulAut.conj Blocks.swap3).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
    intro H
    simp only [Subgroup.map_map]
    congr 1
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hβ']
    simp only [map_mul, map_inv, inv_inv]
    group
  have htop : (B12 (ZMod 2)).map (MulAut.conj c⁻¹).toMonoidHom ⊔
      (B23 (ZMod 2)).map (MulAut.conj c⁻¹).toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, B12_sup_B23,
      Subgroup.map_top_of_surjective _ (MulAut.conj c⁻¹).surjective]
  have hmem : θ β' ∈ ((B12 (ZMod 2)).map (MulAut.conj c⁻¹).toMonoidHom ⊔
      (B23 (ZMod 2)).map (MulAut.conj c⁻¹).toMonoidHom).map θ :=
    Subgroup.mem_map_of_mem θ (htop ▸ Subgroup.mem_top β')
  rw [Subgroup.map_sup] at hmem
  rcases himg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨θ β', h1 ▸ h2 ▸ hmem, ?_⟩
    rw [← h1, ← h2, hmap, Blocks.map_swap3_B12]
  · refine ⟨θ β', ?_, ?_⟩
    · rw [h1, h2] at hmem
      exact sup_comm (V) (U) ▸ hmem
    · rw [← h1, ← h2, hmap, Blocks.map_swap3_B23]

theorem map_conj_eq_of_mem_normalizer {G : Type} [Group G] {H : Subgroup G} {β : G}
    (hβ : β ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj β).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.mem_normalizer_iff.1 hβ]
  constructor <;> intro hx <;> convert hx using 1 <;> group

variable {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G} {K : ℕ → Subgroup G}
  {t : G}

theorem HypA.centralizer_conj_le_normalizer (hA : HypA G n b L) (α : G) :
    Subgroup.centralizer ({α * b * α⁻¹} : Set G) ≤
      Subgroup.normalizer ((L.map (MulAut.conj α).toMonoidHom : Subgroup G) : Set G) := by
  intro x hx
  have hy : α⁻¹ * x * α ∈ Subgroup.normalizer (L : Set G) := by
    apply hA.nor
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc α⁻¹ * x * α * b = α⁻¹ * (x * (α * b * α⁻¹)) * α := by group
      _ = α⁻¹ * ((α * b * α⁻¹) * x) * α := by rw [hx]
      _ = b * (α⁻¹ * x * α) := by group
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro h
  simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [hy (α⁻¹ * h * α)]
  constructor <;> intro hh <;> convert hh using 1 <;> group

theorem FrameSystem.commute_one_six (hA : HypA G 6 b L) (hF : FrameSystem 6 b L K t) :
    ∀ a ∈ K 1, ∀ c ∈ K 6, a * c = c * a := by
  obtain ⟨ψL, hψLinj, hψLrange, hψLblk⟩ := hF.sysL.exists_injective_marking (by norm_num)
  obtain ⟨ψ7, -, hψ7range, hψ7blk⟩ := hF.sysL'.exists_injective_marking (by norm_num)
  obtain ⟨g, -, hgL, hgc⟩ := hF.tau
  set α : G := ψ7 Blocks.rev7 with hαdef
  have hαmem : α ∈ L.map (MulAut.conj g).toMonoidHom := hgL ▸ hψ7range ▸ ⟨_, rfl⟩
  have hcomp : (MulAut.conj α).toMonoidHom.comp ψ7 =
      ψ7.comp (MulAut.conj Blocks.rev7).toMonoidHom := by
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hαdef, map_mul,
      map_inv]
  have hconj : ∀ k : Fin 6, ((k : ℕ) = 2 ∨ (k : ℕ) = 3 ∨ (k : ℕ) = 4) →
      (K (k : ℕ)).map (MulAut.conj α).toMonoidHom = K (4 - (k : ℕ)) := by
    intro k hk
    rw [← hψ7blk k, Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Blocks.map_rev7_range_block k hk, hψ7blk]
  have h2 : (K 2).map (MulAut.conj α).toMonoidHom = K 2 := hconj 2 (Or.inl rfl)
  have h3 : (K 3).map (MulAut.conj α).toMonoidHom = K 1 := hconj 3 (Or.inr (Or.inl rfl))
  have h4 : (K 4).map (MulAut.conj α).toMonoidHom = K 0 := hconj 4 (Or.inr (Or.inr rfl))
  set ψ4 : SL(6 + 1, ZMod 2) →* G := (MulAut.conj α).toMonoidHom.comp ψL with hψ4
  have hψ4inj : Function.Injective ψ4 := (MulAut.conj α).injective.comp hψLinj
  have hψ4blk : ∀ i : Fin 6,
      (blockSL2 (ZMod 2) 6 i).range.map ψ4 = (K ((i : ℕ) + 2)).map (MulAut.conj α).toMonoidHom := by
    intro i
    rw [hψ4, ← Subgroup.map_map, hψLblk i]
  have hblk0 : (blockSL2 (ZMod 2) 6 0).range.map ψ4 = K 2 := (hψ4blk 0).trans h2
  have hblk1 : (blockSL2 (ZMod 2) 6 1).range.map ψ4 = K 1 := (hψ4blk 1).trans h3
  have hblk2 : (blockSL2 (ZMod 2) 6 2).range.map ψ4 = K 0 := (hψ4blk 2).trans h4
  have hαα : α * α = 1 := by rw [hαdef, ← map_mul, Blocks.rev7_mul_self, map_one]
  have hb0 : b ∈ K 0 := by rw [hF.K0]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hbα : α * b * α⁻¹ ∈ K 4 := by
    have h04 : (K 0).map (MulAut.conj α).toMonoidHom = K 4 := by
      rw [← h4, Subgroup.map_map]
      convert Subgroup.map_id (K 4)
      ext1 x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      rw [← mul_assoc, ← mul_assoc, hαα, one_mul, mul_assoc, ← mul_inv_rev, hαα, inv_one,
        mul_one]
    rw [← h04]
    exact ⟨b, hb0, rfl⟩
  have hK7 : K 7 ≤ L.map (MulAut.conj α).toMonoidHom := by
    intro k hk
    have hkL : k ∈ L := hF.le_L (by norm_num) (by norm_num) hk
    have hcomm : α * k = k * α := (hgc k hk α hαmem).symm
    refine ⟨k, hkL, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨W, hW⟩ := hF.sysL.2.2.2 (5 : Fin 6) (4 : Fin 6) (Or.inr rfl)
  obtain ⟨β, hβmem, hβ⟩ := LinearBlockStandardPair.exists_conj_two hW
  replace hβmem : β ∈ K 7 ⊔ K 6 := hβmem
  replace hβ : (K 7).map (MulAut.conj β).toMonoidHom = K 6 := hβ
  have hK4c : ∀ j : Fin 6, ((j : ℕ) = 4 ∨ (j : ℕ) = 5) →
      ∀ x ∈ K ((j : ℕ) + 2), ∀ y ∈ K 4, x * y = y * x := by
    intro j hj x hx y hy
    exact hF.sysL.2.2.1 j (2 : Fin 6) (fun h => by rcases hj with hj | hj <;> simp_all [Fin.ext_iff])
      (by unfold adjA; simp only [Fin.val_two]; omega) x hx y hy
  have hβc : β ∈ Subgroup.centralizer ({α * b * α⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hle : K 7 ⊔ K 6 ≤ Subgroup.centralizer ({α * b * α⁻¹} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hK4c 5 (Or.inr rfl) x hx _ hbα
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hK4c 4 (Or.inl rfl) x hx _ hbα
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hβmem)
  have hβN := hA.centralizer_conj_le_normalizer α hβc
  have hK6 : K 6 ≤ L.map (MulAut.conj α).toMonoidHom := by
    rw [← hβ, ← map_conj_eq_of_mem_normalizer hβN]
    exact Subgroup.map_mono hK7
  intro a ha c hc
  have hcL4 : c ∈ ψ4.range := by
    rw [hψ4, MonoidHom.range_comp, hψLrange]
    exact hK6 hc
  obtain ⟨x, rfl⟩ := hcL4
  have hcK2 : ∀ y ∈ K 2, ψ4 x * y = y * ψ4 x := fun y hy =>
    hF.sysL.2.2.1 (4 : Fin 6) (0 : Fin 6) (by decide) (by unfold adjA; decide) _ hc y hy
  have hcK0 : ∀ y ∈ K 0, ψ4 x * y = y * ψ4 x := fun y hy =>
    (hF.comm_L y hy _ (hF.le_L (by norm_num) (by norm_num) hc)).symm
  have hx0 : ∀ A, Commute x (blockSL2 (ZMod 2) 6 ⟨0, by omega⟩ A) := fun A => hψ4inj (by
    rw [map_mul, map_mul]
    exact hcK2 _ (hblk0 ▸ ⟨_, ⟨A, rfl⟩, rfl⟩))
  have hx2 : ∀ A, Commute x (blockSL2 (ZMod 2) 6 ⟨0 + 2, by omega⟩ A) := fun A => hψ4inj (by
    rw [map_mul, map_mul]
    exact hcK0 _ (hblk2 ▸ ⟨_, ⟨A, rfl⟩, rfl⟩))
  rw [← hblk1] at ha
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
  have hx1 := Blocks.commute_blockSL2_succ x 0 (by omega) hx0 hx2 A
  rw [← map_mul, ← map_mul]
  exact congrArg ψ4 hx1.eq.symm

theorem FrameSystem.yLab_six
    (hC : CurtisA2) (hA : HypA G 6 b L) (hF : FrameSystem 6 b L K t) :
    YLab 6 (⨆ i : Fin (6 + 2), K (i : ℕ)) :=
  hF.yLab_of_commute hC (Or.inr rfl) (hF.commute_one_six hA)

end CFSG.StandardType.FF81
