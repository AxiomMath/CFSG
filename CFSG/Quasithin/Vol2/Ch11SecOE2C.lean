module

public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.H13.A6Realize
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE2

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem isAltBlockType_of_isA6Block {L : Subgroup G} (h : H13.IsA6Block L) :
    IsAltBlockType L 6 := by
  classical
  obtain ⟨hshort, ⟨e⟩, hcomm, π, hπ⟩ := h
  have hLN : L ≤ normalizer (blockU L : Set G) := C1.le_normalizer_blockU L
  have hπi : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
  set πe : ↥(alternatingGroup (Fin 6)) ≃* ↥(autOn L (blockU L)) :=
    MulEquiv.ofBijective π ⟨hπi, hπ.1⟩
  set φ : ↥L →* ↥(autOn L (blockU L)) := H13.A6.autOnHom hLN
  have hφs : Function.Surjective φ := H13.A6.autOnHom_surjective hLN
  have hφv : ∀ (l : ↥L) (u : ↥(blockU L)),
      (((φ l : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) u : G) = l * u * (l : G)⁻¹ :=
    fun l u => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  set α : ↥L →* ↥(alternatingGroup (Fin 6)) := πe.symm.toMonoidHom.comp φ with hα
  have hαs : Function.Surjective α := πe.symm.surjective.comp hφs
  have hπα : ∀ l : ↥L, π (α l) = φ l := fun l => πe.apply_symm_apply (φ l)
  have hU : blockU L ≤ blockQ L ⊓ centralizer (blockQ L : Set G) := hshort.2.2.1.1
  have hle : CFSG.pCore 2 ↥L ≤ α.ker := by
    intro l hl
    rw [hα, MonoidHom.ker_comp_of_injective _ _ πe.symm.injective, MonoidHom.mem_ker]
    refine Subtype.ext (MulEquiv.ext fun u => Subtype.ext ?_)
    show (((φ l : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) u : G) = (u : G)
    rw [hφv]
    have hlQ : (l : G) ∈ blockQ L := by
      show (l : G) ∈ pCoreOf 2 L
      rw [pCoreOf]
      exact ⟨l, hl, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 (hU u.2).2 l hlQ
    calc (l : G) * u * (l : G)⁻¹ = u * l * (l : G)⁻¹ := by rw [h1]
      _ = u := by group
  have hker : α.ker = CFSG.pCore 2 ↥L := by
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have h1 : α.ker.index = (CFSG.pCore 2 ↥L).index := by
      rw [Subgroup.index, Subgroup.index,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv,
        Nat.card_congr e.toEquiv]
    have hi : (CFSG.pCore 2 ↥L).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : Nat.card α.ker * (CFSG.pCore 2 ↥L).index =
        Nat.card (CFSG.pCore 2 ↥L) * (CFSG.pCore 2 ↥L).index := by
      rw [← h1, Subgroup.card_mul_index, h1, Subgroup.card_mul_index]
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) h2).le
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := id hπ
  let β₁ : ↥(blockU L) →* ↥(G6.coreMod 6) ⧸ C124.altKer 6 :=
    β.comp Subgroup.topEquiv.symm.toMonoidHom
  have hβ₁s : Function.Surjective β₁ := fun y => by
    obtain ⟨u, hu⟩ := hβs y
    exact ⟨u, hu⟩
  have hβ₁k : ∀ u : ↥(blockU L), β₁ u = 1 ↔ u ∈ (blockZ L).subgroupOf (blockU L) :=
    fun u => hβk (Subgroup.topEquiv.symm u)
  refine ⟨hshort, α, hαs, hker, (C124.altQuotEquiv 6 (by norm_num)).toMonoidHom.comp β₁,
    (C124.altQuotEquiv 6 (by norm_num)).surjective.comp hβ₁s, ?_, ?_⟩
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
    exact hβ₁k u
  · intro ℓ u v huv x hx
    set m : ↥(G6.coreMod 6) := (C124.coreEvenEquiv 6).symm (Multiplicative.ofAdd x) with hm
    have hum : β₁ u = QuotientGroup.mk m := by
      apply (C124.altQuotEquiv 6 (by norm_num)).injective
      rw [C124.altQuotEquiv_mk]
      apply Multiplicative.toAdd.injective
      rw [C124.altHeartHom_apply, hm, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      exact hx.symm
    have hv : (⟨((π (α ℓ) : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) u,
        Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥(blockU L))) = Subgroup.topEquiv.symm v := by
      apply Subtype.ext
      apply Subtype.ext
      show (((π (α ℓ) : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) u : G) = (v : G)
      rw [hπα, hφv, huv, InvMemClass.coe_inv]
    have hβv := hβe (α ℓ) (Subgroup.topEquiv.symm u) m (Subgroup.mem_top _)
      (G6.permAct_mem_coreMod _ m.2) hum
    have hβv' : β₁ v = QuotientGroup.mk (⟨G6.permAct 6
        ((α ℓ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) m,
          G6.permAct_mem_coreMod _ m.2⟩ : ↥(G6.coreMod 6)) := by
      show β (Subgroup.topEquiv.symm v) = _
      rw [← hv]
      exact hβv
    show (QuotientAddGroup.mk (permWeight 6 ((α ℓ : ↥(alternatingGroup (Fin 6))) :
        Equiv.Perm (Fin 6)) x) : AltHeart 6) =
      Multiplicative.toAdd (C124.altQuotEquiv 6 (by norm_num) (β₁ v))
    rw [hβv', C124.altQuotEquiv_mk, C124.altHeartHom_apply]
    rfl

theorem alt6_not_comm : ∃ a b : ↥(alternatingGroup (Fin 6)), a * b ≠ b * a := by
  decide +kernel

omit [Finite G] in
theorem isHatA6Block_of {L : Subgroup G} (h : H13.IsHatA6Block L) :
    CFSG.Quasithin.IsHatA6Block L := by
  obtain ⟨hshort, ⟨hperf, hZ3, ⟨e⟩⟩, hU6, hC⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨a, b, hab⟩ := alt6_not_comm
  refine ⟨hshort, ⟨⟨hperf, e.isSimpleGroup, e.symm a, e.symm b, fun hc => hab ?_⟩, hZ3, ⟨e⟩⟩,
    hU6, hC⟩
  simpa using congrArg e hc

end CFSG.Quasithin.Vol2.Ch11.OE2
