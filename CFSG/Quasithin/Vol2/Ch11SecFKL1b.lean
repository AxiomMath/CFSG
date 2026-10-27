module

public import CFSG.Quasithin.Vol2.Ch11SecFKL1
public import CFSG.Quasithin.Vol2.Ch11SecFOblY
public import CFSG.Quasithin.Vol2.Ch11SecFU2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ V₃ : Subgroup G}

omit [Finite G] in
theorem le_centralizer_sup {A B : Subgroup G} (hA : A ≤ Subgroup.centralizer (A : Set G))
    (hB : B ≤ Subgroup.centralizer (B : Set G)) (hBA : B ≤ Subgroup.centralizer (A : Set G)) :
    A ⊔ B ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := Subgroup.le_centralizer_iff.mp hBA
  refine sup_le ?_ ?_ <;> rw [Subgroup.le_centralizer_iff]
  · exact sup_le hA hBA
  · exact sup_le hAB hB

theorem false_of_kOf_ne (hF : Sp4Facts) (hZC : FactSp4ZCent) (hVL1 : FactSp4VL1)
    (hObl : Obl11_5_7Sp4Y) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1113 : Stmt11_1_3)
    (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    (hW : ¬ IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))))
    (hK : KOf L V₁ V₁ ≠ LOf L V₁) (hO : pCoreOf 2 L = fsuV T I) : False := by
  have hWK := commutator_conjClosure_kOf_le hF hZC hVL1 h1102 h1103 h1113 h1141 h1143 h1154 h1156
    h hV₁ hV₂ hV₃ hk hO
  have hY := hObl G T L I n V₁ V₃ h hV₁ hV₃ hk hW hK hO hWK
  set W := conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) with hWdef
  set U := conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) with hUdef
  set V := fsuV T I with hVdef
  have hVW : V ≤ W := le_conjClosure_self _ _
  have hUC := conjClosure_V₃_le_centralizer hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁
    hV₂ hV₃ hk
  have hG₁U : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_conjClosure _ _
  have hKN : KOf L V₁ V₁ ≤ Subgroup.normalizer ((V ⊔ U : Subgroup G) : Set G) := by
    intro x hx
    have hxU := hG₁U (kOf_le_normalizer_V₁ L V₁ hx)
    have hxU' := hG₁U (kOf_le_normalizer_V₁ L V₁ ((KOf L V₁ V₁).inv_mem hx))
    have hc : ∀ y ∈ KOf L V₁ V₁, ∀ p ∈ V, ⁅p, y⁆ ∈ U := fun y hy p hp =>
      hWK (Subgroup.commutator_mem_commutator (hVW hp) hy)
    refine SecD.mem_normalizer_of_conj (conj_sup_le_of_commutator hxU (hc x hx)) ?_
    have h1 := conj_sup_le_of_commutator hxU' (hc _ ((KOf L V₁ V₁).inv_mem hx))
    simpa using h1
  have hMN : Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer ((V ⊔ U : Subgroup G) : Set G) :=
    SecD.le_normalizer_sup (inf_normalizer_V₁_le_normalizer_fsuV h1103 h hV₁)
      (inf_le_right.trans hG₁U)
  have hG₁N : Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer ((V ⊔ U : Subgroup G) : Set G) := by
    intro g hg
    obtain ⟨x, hx, m, hm, rfl⟩ := exists_decomp h1143 h hV₁ g hg
    exact Subgroup.mul_mem _ (sup_le hKN hY hx) (hMN hm)
  have hWVU : W ≤ V ⊔ U := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₁N hg) v).mp (Subgroup.mem_sup_left hv)
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val ((SecA.isElemAbelian_fsuV h).1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hUW : U ≤ W := conjClosure_mono (SecA.IsVi.le_fsuV hV₃) le_rfl
  have hUU : U ≤ Subgroup.centralizer (U : Set G) :=
    hUC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUW))
  have hUV : U ≤ Subgroup.centralizer (V : Set G) :=
    hUC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVW))
  apply hW
  refine isMulCommutative_of_le_centralizer (hWVU.trans ?_)
  exact (le_centralizer_sup hVC hUU hUV).trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWVU))

end CFSG.Quasithin.Vol2.Ch11.SecF
