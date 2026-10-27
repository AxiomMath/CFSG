module

public import CFSG.Quasithin.MS93.RedHyp
public import CFSG.Quasithin.MS93.S32Cent

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_sup_le_of {U C L : Subgroup G} (hUL : ⁅U, L⁆ ≤ U)
    (hCU : C ≤ Subgroup.normalizer (U : Set G)) (hCL : ⁅C, L⁆ ≤ U) : ⁅U ⊔ C, L⁆ ≤ U := by
  let K : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (U : Set G) ∧ ∀ l ∈ L, ⁅x, l⁆ ∈ U}
      mul_mem' := by
        rintro x y ⟨hx, hxl⟩ ⟨hy, hyl⟩
        refine ⟨Subgroup.mul_mem _ hx hy, fun l hl => ?_⟩
        have e : ⁅x * y, l⁆ = x * ⁅y, l⁆ * x⁻¹ * ⁅x, l⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact U.mul_mem ((Subgroup.mem_normalizer_iff.mp hx _).mp (hyl l hl)) (hxl l hl)
      one_mem' := ⟨Subgroup.one_mem _, fun l _ => by simp⟩
      inv_mem' := by
        rintro x ⟨hx, hxl⟩
        refine ⟨Subgroup.inv_mem _ hx, fun l hl => ?_⟩
        have e : ⁅x⁻¹, l⁆ = x⁻¹ * ⁅x, l⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) _).mp
          (U.inv_mem (hxl l hl)) }
  have hUK : U ≤ K := fun u hu =>
    ⟨Subgroup.le_normalizer hu, fun l hl => hUL (Subgroup.commutator_mem_commutator hu hl)⟩
  have hCK : C ≤ K := fun c hc =>
    ⟨hCU hc, fun l hl => hCL (Subgroup.commutator_mem_commutator hc hl)⟩
  rw [Subgroup.commutator_le]
  intro x hx l hl
  exact (sup_le hUK hCK hx).2 l hl

variable [Finite G] {M T L : Subgroup G}

theorem PUHyp.Z0q_le_T (h : PUHyp M T L) : Z0q M T ≤ T :=
  h.Z0q_le_pCoreOf.trans h.pCore_le

theorem PUHyp.map_Z0q_le_pCoreOf (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (φ : MulAut ↥T) :
    ((Z0q M T).subgroupOf T).map φ.toMonoidHom ≤ (pCoreOf 2 M).subgroupOf T := by
  set X := puAmalgam h.le
  have hM : IsMVtx X (X.ofB (SemidirectProduct.inr φ) • baseA X) :=
    (PU.isMVtx_smul X _ _).2 (PU.isMVtx_baseA X)
  have h1 : X.treeGraph.Adj (X.ofB (SemidirectProduct.inr φ) • baseA X) (baseB X) :=
    ((puAmalgam.adj_baseB_iff_mulAut h.le _).2 ⟨φ, rfl⟩).symm
  have h2 : X.treeGraph.Adj (baseB X) (baseA X) := (adj_baseA_baseB X).symm
  have hd : X.treeGraph.dist (X.ofB (SemidirectProduct.inr φ) • baseA X) (baseA X) <
      critDist X := by
    have := SimpleGraph.dist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
      SimpleGraph.Walk.nil))
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
    omega
  have hle := zm_le_qv_of_dist_lt X hM hd
  rw [puAmalgam.zm_ofB_inr_smul_baseA h.le h.Z0q_le_T φ,
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le, imM_of_le h.le h.pCore_le] at hle
  have hinj : Function.Injective (puAmalgam.ofT h.le) :=
    X.ofB_injective.comp SemidirectProduct.inl_injective
  exact (Subgroup.map_le_map_iff_of_injective hinj).1 hle

theorem PUHyp.charClosureIn_le_pCoreOf (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le)) :
    charClosureIn T (Z0q M T) ≤ pCoreOf 2 M := by
  rw [charClosureIn, Subgroup.map_le_iff_le_comap]
  exact iSup_le fun φ => h.map_Z0q_le_pCoreOf hb φ

theorem PUHyp.charClosureIn_ne_bot (h : PUHyp M T L) : charClosureIn T (Z0q M T) ≠ ⊥ := by
  intro hbot
  have h1 : omegaOneCenterOf T ≤ charClosureIn T (Z0q M T) :=
    (omegaOneCenterOf_le_Z0q M T h.le).trans (le_charClosureIn h.Z0q_le_T)
  rw [hbot, le_bot_iff] at h1
  exact PU.omegaOneCenterOf_ne_bot h.isPGroup h.ne_bot h1

theorem PUHyp.vq_not_le_charClosure (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le)) :
    ¬ Vq M L ≤ charClosureIn T (Z0q M T) := by
  intro hV
  set W := charClosureIn T (Z0q M T) with hW
  have hWQ : W ≤ pCoreOf 2 M := h.charClosureIn_le_pCoreOf hb
  have key : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W := by
    intro l hl w hw
    have hc : l * w * l⁻¹ * w⁻¹ ∈ Vq M L := by
      have := Subgroup.commutator_mem_commutator hl (hWQ hw)
      rw [Subgroup.commutator_comm] at this
      simpa [commutatorElement_def] using this
    have := W.mul_mem (hV hc) hw
    simpa [mul_assoc] using this
  refine h.noChar W (charClosureIn_le T _) h.charClosureIn_ne_bot
    (charClosureIn_characteristic T _) ?_
  rw [h.eq_sup]
  refine sup_le (fun l hl => ?_) (le_normalizer_of_characteristic (charClosureIn_le T _)
    (charClosureIn_characteristic T _))
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨key l hl w, fun hw => ?_⟩
  have := key l⁻¹ (inv_mem hl) _ hw
  simpa [mul_assoc] using this

theorem PUHyp.Uq_le_Vq (h : PUHyp M T L) : Uq M T L ≤ Vq M L :=
  Subgroup.commutator_mono h.Z0q_le_pCoreOf le_rfl

theorem PUHyp.commutator_vq (h : PUHyp M T L) : ⁅Vq M L, L⁆ = Vq M L :=
  (commutator_eq_commutator_commutator (pCoreOf_le' M) h.L_le (le_normalizer_pCoreOf M)
    h.le_normalizer h.perfect).symm

theorem PUHyp.commutator_uq (h : PUHyp M T L) : ⁅Uq M T L, L⁆ = Uq M T L :=
  (commutator_eq_commutator_commutator (Z0q_le M T) h.L_le (le_normalizer_Z0q M T)
    h.le_normalizer h.perfect).symm

theorem PUHyp.uq_ne_bot (h : PUHyp M T L) : Uq M T L ≠ ⊥ := by
  intro hU
  apply h.not_le_centralizer_Z0q
  rw [← Subgroup.le_centralizer_iff, ← Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hU

theorem PUHyp.false_of_two_lt_critDist (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {C : Subgroup G} (hCV : C ≤ Vq M L) (hCL : C ≤ Subgroup.centralizer (L : Set G))
    (hirr : ∀ W : Subgroup G, C ≤ W → W ≤ Vq M L → L ≤ Subgroup.normalizer (W : Set G) →
      ⁅W, L⁆ ⊔ C = W → W = C ∨ W = Vq M L) : False := by
  set U := Uq M T L with hUdef
  have hLU : L ≤ Subgroup.normalizer (U : Set G) := h.L_le.trans (le_normalizer_Uq h.le_normalizer)
  have hLC : L ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.le_centralizer_iff.mp hCL).trans (Subgroup.centralizer_le_normalizer _)
  have hCU : C ≤ Subgroup.normalizer (U : Set G) :=
    (hCV.trans (Vq_le h.L_le)).trans (le_normalizer_Uq h.le_normalizer)
  have hcomm : ⁅U ⊔ C, L⁆ ≤ U :=
    commutator_sup_le_of (commutator_le_left_of_le_normalizer hLU) hCU
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hCL).le.trans bot_le)
  have hfix : ⁅U ⊔ C, L⁆ ⊔ C = U ⊔ C := by
    refine le_antisymm (sup_le (hcomm.trans le_sup_left) le_sup_right) (sup_le ?_ le_sup_right)
    calc U = ⁅U, L⁆ := h.commutator_uq.symm
      _ ≤ ⁅U ⊔ C, L⁆ := Subgroup.commutator_mono le_sup_left le_rfl
      _ ≤ ⁅U ⊔ C, L⁆ ⊔ C := le_sup_left
  rcases hirr (U ⊔ C) le_sup_right (sup_le h.Uq_le_Vq hCV) (le_normalizer_sup hLU hLC) hfix
    with hWC | hWV
  · apply h.uq_ne_bot
    rw [← h.commutator_uq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (le_sup_left.trans hWC.le).trans hCL
  · apply h.vq_not_le_charClosure hb
    calc Vq M L = ⁅Vq M L, L⁆ := h.commutator_vq.symm
      _ = ⁅U ⊔ C, L⁆ := by rw [← hWV]
      _ ≤ U := hcomm
      _ ≤ Z0q M T := Uq_le_Z0q h.L_le
      _ ≤ charClosureIn T (Z0q M T) := le_charClosureIn h.Z0q_le_T

end CFSG.Quasithin.MS93
