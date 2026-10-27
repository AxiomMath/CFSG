module

public import CFSG.Quasithin.MS93.S32U

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

section IrrSecG

@[expose] def IrrSecG (L A B : Subgroup G) : Prop :=
  A < B ∧ ∀ J : Subgroup G, L ≤ Subgroup.normalizer (J : Set G) → A ≤ J → J ≤ B → J = A ∨ J = B

variable [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem irrSecG_toG {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G))
    {A B : Subgroup (IntMod V hV)} (h : XMod.IsIrrSec ↥(autI hV K) A B) :
    IrrSecG K (C124.toG hV A) (C124.toG hV B) := by
  refine ⟨?_, fun J hJ hAJ hJB => ?_⟩
  · exact lt_of_le_of_ne ((C124.toG_le_iff hV).mpr h.1.le)
      fun he => h.1.ne ((C124.toG_inj hV).mp he)
  · set J' : Subgroup (IntMod V hV) := J.comap (C124.valHom hV)
    have hJV : J ≤ V := hJB.trans (C124.toG_le hV B)
    have hJJ' : C124.toG hV J' = J := by
      rw [C124.toG, Subgroup.map_comap_eq, inf_eq_right]
      intro g hg
      exact ⟨IntMod.mk hV ⟨g, hJV hg⟩, rfl⟩
    have hinv : XMod.IsInv ↥(autI hV K) J' := by
      rw [C124.isInv_iff hV hK, hJJ']
      intro g hg w hw
      exact (Subgroup.mem_normalizer_iff.mp (hJ hg) w).mp hw
    rw [← hJJ'] at hAJ hJB ⊢
    rcases h.2 J' hinv ((C124.toG_le_iff hV).mp hAJ) ((C124.toG_le_iff hV).mp hJB) with he | he
    · exact Or.inl (by rw [he])
    · exact Or.inr (by rw [he])

end IrrSecG

section CommXq

variable [Finite G] {M T L : Subgroup G}

theorem toG_commV_Xq (h : PUHyp M T L) :
    C124.toG h.isElemAbelian_Xq (commV (autI h.isElemAbelian_Xq L)) = ⁅Xq M, L⁆ := by
  rw [C124.toG_commV _ ((isSecW_Xq h).L_le_normalizer h), Subgroup.commutator_comm]

theorem toG_fixV_Xq (h : PUHyp M T L) :
    C124.toG h.isElemAbelian_Xq (fixV (autI h.isElemAbelian_Xq L)) = Zq M L :=
  toG_fixV _ ((isSecW_Xq h).L_le_normalizer h)

omit [Finite G] in
theorem commutator_Xq_le (M L : Subgroup G) (hLM : L ≤ M) : ⁅Xq M, L⁆ ≤ Xq M :=
  commutator_le_left_of_le_normalizer (hLM.trans (le_normalizer_Xq M))

theorem Uq_le_commutator_Xq (h : PUHyp M T L) : Uq M T L ≤ ⁅Xq M, L⁆ :=
  Subgroup.commutator_mono h.Z0q_le_Xq le_rfl

theorem commutator_Xq_comm (h : PUHyp M T L) : ⁅⁅Xq M, L⁆, L⁆ = ⁅Xq M, L⁆ :=
  (commutator_eq_commutator_commutator (Xq_le M) h.L_le (le_normalizer_Xq M) h.le_normalizer
    h.perfect).symm

theorem Xq_le_centralizer (h : PUHyp M T L) {U : Subgroup G} (hU : U ≤ Xq M) :
    Xq M ≤ Subgroup.centralizer (U : Set G) := fun x hx =>
  Subgroup.mem_centralizer_iff.mpr fun u hu =>
    congrArg Subtype.val (h.isElemAbelian_Xq.1.1.1 ⟨u, hU hu⟩ ⟨x, hx⟩)

theorem commutator_sup_le (h : PUHyp M T L) {A C U : Subgroup G} (hA : A ≤ Xq M)
    (hC : C ≤ Xq M) (hCL : C ≤ Subgroup.centralizer (L : Set G)) (hU : U ≤ Xq M)
    (hAU : ⁅A, L⁆ ≤ U) : ⁅A ⊔ C, L⁆ ≤ U := by
  have hDn : Xq M ≤ Subgroup.normalizer (U : Set G) :=
    ((Xq_le_centralizer h) hU).trans (Subgroup.centralizer_le_normalizer _)
  have hLn : Xq M ≤ Subgroup.normalizer (L : Set G) := (Xq_le M).trans h.le_normalizer
  have hS : A ⊔ C ≤ relCent (Xq M) L U hDn hLn := by
    refine sup_le (fun a ha => ⟨hA ha, fun l hl => hAU
      (Subgroup.commutator_mem_commutator ha hl)⟩) (fun c hc => ⟨hC hc, fun l hl => ?_⟩)
    have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.mp (hCL hc) l hl).symm
    rw [commutatorElement_def, hcl, mul_inv_cancel_right, mul_inv_cancel]
    exact U.one_mem
  rw [Subgroup.commutator_le]
  intro x hx l hl
  exact (hS hx).2 l hl

theorem commutator_Xq_eq_of_irrSecG (h : PUHyp M T L)
    (hirr : IrrSecG L (⁅Xq M, L⁆ ⊓ Zq M L) ⁅Xq M, L⁆) : ⁅Xq M, L⁆ = Uq M T L := by
  set U' := ⁅Xq M, L⁆
  have hU'X : U' ≤ Xq M := commutator_Xq_le M L h.L_le
  have hUn : L ≤ Subgroup.normalizer (Uq M T L : Set G) := (isSecW_Uq h).L_le_normalizer h
  have hU'n : L ≤ Subgroup.normalizer (U' : Set G) :=
    h.L_le.trans (le_normalizer_commutator (le_normalizer_Xq M) h.le_normalizer)
  have hCn : L ≤ Subgroup.normalizer ((U' ⊓ Zq M L : Subgroup G) : Set G) :=
    le_normalizer_inf hU'n (h.L_le.trans (le_normalizer_Zq h.le_normalizer))
  have hJn : L ≤ Subgroup.normalizer ((Uq M T L ⊔ (U' ⊓ Zq M L) : Subgroup G) : Set G) :=
    B2F.le_normalizer_sup hUn hCn
  rcases hirr.2 _ hJn le_sup_right (sup_le (Uq_le_commutator_Xq h) inf_le_left) with he | he
  · exfalso
    have hUZ : Uq M T L ≤ Zq M L := (le_sup_left.trans he.le).trans inf_le_right
    apply (isSecW_Uq h).not_le
    rw [← Subgroup.le_centralizer_iff]
    exact hUZ.trans inf_le_right
  · refine le_antisymm ?_ (Uq_le_commutator_Xq h)
    calc U' = ⁅U', L⁆ := (commutator_Xq_comm h).symm
      _ = ⁅Uq M T L ⊔ (U' ⊓ Zq M L), L⁆ := by rw [he]
      _ ≤ Uq M T L := (commutator_sup_le h) h.Uq_le_Xq (inf_le_left.trans hU'X)
          (inf_le_right.trans inf_le_right) h.Uq_le_Xq (le_of_eq h.Uq_comm)

end CommXq

end CFSG.Quasithin.MS93.S32
