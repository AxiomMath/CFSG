module

public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Transport
public import CFSG.Quasithin.Vol2.Ch10SecEBlockA5
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS12

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] noncomputable def rhoL {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    ↥L →* ↥(autOn L V) :=
  ((conjAct V).comp (Subgroup.inclusion hLV)).codRestrict (autOn L V) fun l =>
    SecA.mem_autOn_iff'.mpr ⟨⟨l, hLV l.2⟩, l.2, rfl⟩

theorem coe_rhoL_apply {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) (l : ↥L)
    (v : ↥V) : ((((rhoL hLV l : ↥(autOn L V)) : MulAut ↥V) v : ↥V) : G) = l * v * (l : G)⁻¹ := by
  show ((conjAct V (⟨(l : G), hLV l.2⟩ : Subgroup.normalizer (V : Set G)) v : ↥V) : G) = _
  exact SecA.coe_conjAct_apply' (⟨(l : G), hLV l.2⟩ : Subgroup.normalizer (V : Set G)) v

theorem rhoL_surjective {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (rhoL hLV) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hgL, rfl⟩ := SecA.mem_autOn_iff'.mp hφ
  exact ⟨⟨g, hgL⟩, Subtype.ext rfl⟩

variable [Finite G] {T L I : Subgroup G}

theorem isAltType_of_blockU_eq (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I)
    (h2 : Ch10.Case10_1_1Two T L I) (hU : blockU L = fsuUL T L I) : IsAltType L 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨e⟩, hcU, π, hπ⟩ := h2
  have hLV : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) := SecC.le_normalizer_fsuUL T L I
  have hπi : Function.Injective π := hπ.injective_of_faithful (FFC.altDn_faithful (by norm_num))
  let eπ := MulEquiv.ofBijective π ⟨hπi, hπ.1⟩
  let α : ↥L →* alternatingGroup (Fin 5) := eπ.symm.toMonoidHom.comp (rhoL hLV)
  have hαs : Function.Surjective α := eπ.symm.surjective.comp (rhoL_surjective hLV)
  have hπα : ∀ l : ↥L, π (α l) = rhoL hLV l := fun l => eπ.apply_symm_apply _
  have hOC : pCoreOf 2 L ≤ Subgroup.centralizer (fsuVM T L I : Set G) :=
    SecE.pCoreOf_L_le_centralizer h37 h38 h3228 hyp (Or.inr ⟨⟨e⟩, hcU, π, hπ⟩)
  have hVV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hle : CFSG.pCore 2 ↥L ≤ α.ker := by
    intro l hl
    have hlO : (l : G) ∈ pCoreOf 2 L := by
      have h1 : l ∈ (pCoreOf 2 L).subgroupOf L := by rw [subgroupOf_pCoreOf]; exact hl
      exact Subgroup.mem_subgroupOf.mp h1
    have hρ : rhoL hLV l = 1 := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      rw [coe_rhoL_apply]
      have hc := Subgroup.mem_centralizer_iff.mp (hOC hlO) v (hVV v.2)
      show (l : G) * v * (l : G)⁻¹ = v
      rw [← hc]
      group
    rw [MonoidHom.mem_ker]
    show eπ.symm (rhoL hLV l) = 1
    rw [hρ, map_one]
  have hcard : Nat.card α.ker = Nat.card (CFSG.pCore 2 ↥L) := by
    have h1 := (α.ker).card_mul_index
    have h2 := (CFSG.pCore 2 ↥L).card_mul_index
    have h3 : (α.ker).index = 60 := by
      rw [Subgroup.index, ← SecB.card_alt5]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv
    have h4 : (CFSG.pCore 2 ↥L).index = 60 := by
      rw [Subgroup.index, ← SecB.card_alt5]
      exact Nat.card_congr e.toEquiv
    rw [h3] at h1
    rw [h4] at h2
    omega
  have hαk : α.ker = CFSG.pCore 2 ↥L :=
    (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm
  obtain ⟨β₀, hβs, hβk, hβe⟩ := SecE.RealizesVia.coordSec SecE.altDn_five_ker hπ
  let ι : ↥(blockU L) ≃* ↥(⊤ : Subgroup ↥(fsuUL T L I)) :=
    (MulEquiv.subgroupCongr hU).trans Subgroup.topEquiv.symm
  have hι : ∀ u : ↥(blockU L), (((ι u : ↥(⊤ : Subgroup ↥(fsuUL T L I))) : ↥(fsuUL T L I)) :
      G) = u := fun _ => rfl
  refine ⟨α, hαs, hαk, (L246.coreEquiv 5).toMonoidHom.comp (β₀.comp ι.toMonoidHom),
    (L246.coreEquiv 5).surjective.comp (hβs.comp ι.surjective), ?_, ?_⟩
  · have hZ : blockZ L = ⊥ := by
      rw [blockZ, hU]
      exact SecF.fsuUL_inf_centralizer_eq_bot ⟨⟨e⟩, hcU, π, hπ⟩
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hZ, Subgroup.mem_bot]
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      MonoidHom.comp_apply, hβk, Subgroup.mem_bot]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  · intro ℓ u v hv i
    have hmem : (((π (α ℓ) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))
        ((ι u : ↥(⊤ : Subgroup ↥(fsuUL T L I))) : ↥(fsuUL T L I))) ∈
        (⊤ : Subgroup ↥(fsuUL T L I)) := Subgroup.mem_top _
    have h1 := hβe (α ℓ) (ι u) hmem
    have h2 : (⟨(((π (α ℓ) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))
        ((ι u : ↥(⊤ : Subgroup ↥(fsuUL T L I))) : ↥(fsuUL T L I))), hmem⟩ :
        ↥(⊤ : Subgroup ↥(fsuUL T L I))) = ι v := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hπα, coe_rhoL_apply, hι, hι, hv]
      rfl
    rw [h2] at h1
    have h4 : ((β₀ (ι v)).1 : G6.PermMod 5) =
        G6.permAct 5 ((α ℓ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))
          ((β₀ (ι u)).1 : G6.PermMod 5) := h1
    have h3 : Multiplicative.toAdd ((β₀ (ι v)).1 : G6.PermMod 5) i =
        Multiplicative.toAdd ((β₀ (ι u)).1 : G6.PermMod 5)
          (((α ℓ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i) := by
      rw [h4]
      rfl
    exact h3

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
