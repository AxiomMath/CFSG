module

public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.Background.G2SL3Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem commutator_inter3_le_of {U I VL V₁ : Subgroup G} {g h : G}
    (hI : I = U ⊔ rconj U g ⊔ rconj U h) (hIVL : I ≤ Subgroup.normalizer (VL : Set G))
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ V₁) (hV₁VL : V₁ ≤ VL)
    (hgV : rconj V₁ g ≤ VL) (hhV : rconj V₁ h ≤ VL) :
    ⁅U ⊓ rconj U g ⊓ rconj U h, I⁆ ≤ VL := by
  have hUI : U ≤ I := by rw [hI]; exact le_sup_left.trans le_sup_left
  have hUgI : rconj U g ≤ I := by rw [hI]; exact le_sup_right.trans le_sup_left
  have hUhI : rconj U h ≤ I := by rw [hI]; exact le_sup_right
  rw [Subgroup.commutator_le]
  intro x hx
  let Z : Subgroup G :=
    { carrier := {y | y ∈ I ∧ x * y * x⁻¹ * y⁻¹ ∈ VL}
      one_mem' := ⟨I.one_mem, by simp⟩
      mul_mem' := by
        rintro y z ⟨hyI, hy⟩ ⟨hzI, hz⟩
        refine ⟨I.mul_mem hyI hzI, ?_⟩
        have h1 : y * (x * z * x⁻¹ * z⁻¹) * y⁻¹ ∈ VL :=
          (Subgroup.mem_normalizer_iff.1 (hIVL hyI) _).1 hz
        have : x * (y * z) * x⁻¹ * (y * z)⁻¹ =
            (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
        rw [this]
        exact VL.mul_mem hy h1
      inv_mem' := by
        rintro y ⟨hyI, hy⟩
        refine ⟨I.inv_mem hyI, ?_⟩
        have h1 : y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y ∈ VL := by
          have := (Subgroup.mem_normalizer_iff.1 (hIVL (I.inv_mem hyI)) _).1 (VL.inv_mem hy)
          simpa [mul_assoc] using this
        have : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y := by group
        rw [this]
        exact h1 }
  have hIZ : I ≤ Z := by
    rw [hI]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro y hy
      exact ⟨hUI hy, hV₁VL (hcomm x hx.1.1 y hy)⟩
    · intro y hy
      refine ⟨hUgI hy, hgV ?_⟩
      have hx2 : g * x * g⁻¹ ∈ U := mem_rconj.1 hx.1.2
      have hy2 : g * y * g⁻¹ ∈ U := mem_rconj.1 hy
      rw [mem_rconj]
      have h1 := hcomm _ hx2 _ hy2
      have : g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ =
          (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
      rwa [this]
    · intro y hy
      refine ⟨hUhI hy, hhV ?_⟩
      have hx2 : h * x * h⁻¹ ∈ U := mem_rconj.1 hx.2
      have hy2 : h * y * h⁻¹ ∈ U := mem_rconj.1 hy
      rw [mem_rconj]
      have h1 := hcomm _ hx2 _ hy2
      have : h * (x * y * x⁻¹ * y⁻¹) * h⁻¹ =
          (h * x * h⁻¹) * (h * y * h⁻¹) * (h * x * h⁻¹)⁻¹ * (h * y * h⁻¹)⁻¹ := by group
      rwa [this]
  intro y hy
  exact (hIZ hy).2

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L3Setting n V V₁ L T H)

include S

omit [Finite G] in
theorem V_le_rconj_U {k : G} (hk : k ∈ L) : V ≤ rconj (conjClosure V H) k := by
  intro v hv
  rw [mem_rconj]
  exact le_conjClosure V H ((Subgroup.mem_normalizer_iff.1 (S.D.hnorm hk) v).1 hv)

omit [Finite G] in
theorem rconj_V₁_le_V {k : G} (hk : k ∈ L) : rconj V₁ k ≤ V := by
  intro y hy
  rw [mem_rconj] at hy
  have h1 : k * y * k⁻¹ ∈ V := S.hyp.base.le_V hy
  exact (Subgroup.mem_normalizer_iff.1 (S.D.hnorm hk) y).2 h1

theorem commutator_inter3_le_V {I : Subgroup G} {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hI : I = conjClosure V H ⊔ rconj (conjClosure V H) g ⊔ rconj (conjClosure V H) h)
    (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) :
    ⁅conjClosure V H ⊓ rconj (conjClosure V H) g ⊓ rconj (conjClosure V H) h, I⁆ ≤ V := by
  have hI' : I = L ⊔ conjClosure V H := hI.trans (S.G25_two_aux hg hh hV)
  have hIV : I ≤ Subgroup.normalizer (V : Set G) := hI' ▸ S.LU_le_normV
  exact commutator_inter3_le_of hI hIV (fun x hx y hy => S.hyp.base.G22_commutator_mem hx hy)
    S.hyp.base.le_V (S.rconj_V₁_le_V hg) (S.rconj_V₁_le_V hh)

end L3Setting

namespace AlmostSpecialL3Hyp

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialL3Hyp n V V₁ L T H)

include hyp

theorem G25_five {U I : Subgroup G} (hU : U = conjClosure V H) {g h : G} (hg : g ∈ L)
    (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    (hI : I = U ⊔ rconj U g ⊔ rconj U h) :
    ⁅U ⊓ rconj U g ⊓ rconj U h, I⁆ ≤ V := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L3Setting n V V₁ L T H := ⟨hyp, D⟩
  subst hU
  exact St.commutator_inter3_le_V hg hh hI hV

theorem G25_four {U I S W : Subgroup G} (hU : U = conjClosure V H) {g h : G} (hg : g ∈ L)
    (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    (hI : I = U ⊔ rconj U g ⊔ rconj U h) (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S) :
    V ≤ U ⊓ rconj U g ⊓ rconj U h ∧
      U ⊓ rconj U g ⊓ rconj U h ≤ (W ⊓ rconj W g) ⊔ (W ⊓ rconj W h) ⊔ (rconj W g ⊓ rconj W h) ∧
      (W ⊓ rconj W g) ⊔ (W ⊓ rconj W h) ⊔ (rconj W g ⊓ rconj W h) ≤ S ∧
      V ≤ centerOf S ∧ I ≤ Subgroup.normalizer (V : Set G) ∧
      I ≤ Subgroup.normalizer ((U ⊓ rconj U g ⊓ rconj U h : Subgroup G) : Set G) ∧
      I ≤ Subgroup.normalizer (S : Set G) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L3Setting n V V₁ L T H := ⟨hyp, D⟩
  subst hU
  subst hS
  subst hW
  have hI' : I = L ⊔ conjClosure V H := hI.trans (St.G25_two_aux hg hh hV)
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := sx_facts_gen hI' St.U_le_T
    St.hyp.base.G22_three.2 St.hyp.base.T_le_normL St.hyp.base.sylow_LT
  have hLI : L ≤ I := hI' ▸ le_sup_left
  have hUI : conjClosure V H ≤ I := hI' ▸ le_sup_right
  have hgI : g ∈ I := hLI hg
  have hhI : h ∈ I := hLI hh
  have hIV : I ≤ Subgroup.normalizer (V : Set G) := hI' ▸ St.LU_le_normV
  have hVS₂ : V ≤ conjClosure V H ⊓ rconj (conjClosure V H) g ⊓ rconj (conjClosure V H) h :=
    le_inf (le_inf (le_conjClosure V H) (St.V_le_rconj_U hg)) (St.V_le_rconj_U hh)
  have hc := St.commutator_inter3_le_V hg hh hI hV
  have hS₂N : I ≤ Subgroup.normalizer
      ((conjClosure V H ⊓ rconj (conjClosure V H) g ⊓ rconj (conjClosure V H) h : Subgroup G) :
        Set G) := by
    refine le_normalizer_of_conj_mem fun y hy x hx => ?_
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ V := hc (Subgroup.commutator_mem_commutator hx hy)
    have h2 : y * x * y⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ * x := by group
    rw [h2]
    exact Subgroup.mul_mem _ (hVS₂ (V.inv_mem h1)) hx
  have hS₂U : conjClosure V H ⊓ rconj (conjClosure V H) g ⊓ rconj (conjClosure V H) h ≤
      conjClosure V H := inf_le_left.trans inf_le_left
  have hS₂S : conjClosure V H ⊓ rconj (conjClosure V H) g ⊓ rconj (conjClosure V H) h ≤
      pCoreOf 2 I :=
    le_pCoreOf_of_le_normalizer 2 (hS₂U.trans hUI) hS₂N (St.isPGroup_U.to_le hS₂U)
  have hS₂W : conjClosure V H ⊓ rconj (conjClosure V H) g ⊓ rconj (conjClosure V H) h ≤
      conjClosure V H ⊓ pCoreOf 2 I := le_inf hS₂U hS₂S
  have hS₂Wg : conjClosure V H ⊓ rconj (conjClosure V H) g ⊓ rconj (conjClosure V H) h ≤
      rconj (conjClosure V H ⊓ pCoreOf 2 I) g := by
    intro x hx
    exact mem_rconj.2 ⟨mem_rconj.1 hx.1.2, hINorm g hgI x (hS₂S hx)⟩
  have hWSx : conjClosure V H ⊓ pCoreOf 2 I ≤ pCoreOf 2 I := inf_le_right
  have hWgSx : rconj (conjClosure V H ⊓ pCoreOf 2 I) g ≤ pCoreOf 2 I :=
    rconj_inf_le_Sx hgI hINorm
  refine ⟨hVS₂, ?_, ?_, ?_, hIV, hS₂N, le_normalizer_pCoreOf 2 I⟩
  · exact (le_inf hS₂W hS₂Wg).trans (le_sup_left.trans le_sup_left)
  · exact sup_le (sup_le (inf_le_left.trans hWSx) (inf_le_left.trans hWSx))
      (inf_le_left.trans hWgSx)
  · have hVS' : V ≤ pCoreOf 2 I :=
      le_pCoreOf_of_le_normalizer 2 ((le_conjClosure V H).trans hUI) hIV St.isPGroup_V
    intro v hv
    refine ⟨hVS' hv, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
    have h1 := St.O_centralizes_V s (hSxO hs) v hv
    calc s * v = (s * v * s⁻¹) * s := by group
      _ = v * s := by rw [h1]

end AlmostSpecialL3Hyp

end CFSG.Quasithin
