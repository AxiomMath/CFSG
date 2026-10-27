module

public import CFSG.Quasithin.MS93.S46R468N1
public import CFSG.Quasithin.MS93.S46R468FFSec
public import CFSG.Quasithin.MS93.S46R468B3

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix MatrixGroups

section General

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem le_normalizer_ptQ {x : Vtx X} {P K : Subgroup X.Universal} (hK : K ≤ stab X x)
    (hKP : K ≤ Subgroup.normalizer (P : Set X.Universal)) :
    K ≤ Subgroup.normalizer (ptQ X x P : Set X.Universal) :=
  le_normalizer_of_map_conj_le fun k hk => by
    rw [← ptQ_smul, MulAction.mem_stabilizer_iff.mp (hK hk),
      map_conj_eq_of_mem_normalizer (hKP hk)]

end General

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem qv_le_normalizer_of_le_usup (h464 : I464) (c : Hyp46 M T L φ)
    {γ β : Vtx (puAmalgam c.pu.le)} (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hPU : P ≤ Usup (puAmalgam c.pu.le) γ β) :
    Qv (puAmalgam c.pu.le) β ≤ Subgroup.normalizer (P : Set (puAmalgam c.pu.le).Universal) :=
  fun t ht => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun _ ha =>
    (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β
      (h464 G M T L F φ c γ β hγ hγβ (hPU ha))) t ht).symm)

theorem relIndex_ptQ_qv (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {γ β : Vtx (puAmalgam c.pu.le)} (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) γ β P) :
    (ptQ (puAmalgam c.pu.le) γ P).relIndex (Qv _ β) = Fintype.card F := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hPZ : P ≤ ZM (puAmalgam c.pu.le) γ :=
    (le_uloc_of_isPtOn c hγ hP).trans (uloc_le_zm c.pu hfull hγ)
  have hmul := Subgroup.relIndex_mul_relIndex (Qv (puAmalgam c.pu.le) γ)
    (Qv _ β ⊓ ptQ _ γ P) (Qv _ β) (le_inf (qv_le_qv _ c.pu.hyp20 hγ hγβ) (qv_le_ptQ c hγ hPZ))
    inf_le_left
  rw [relIndex_qv_inf_ptQ h464 h465 h466a c hγ hγβ hP, h466a G M T L F φ c γ β hγ hγβ, sq] at hmul
  rw [← Subgroup.inf_relIndex_right, inf_comm]
  exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos hmul

theorem BadConf.natural_pencil (h464 : I464) (h465 : I465) (h466a : I466a)
    {c : Hyp46 M T L φ} {α₀ α₀' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α₀ α₀')
    {α β γ : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) {δ p P R : Subgroup (puAmalgam c.pu.le).Universal}
    (hδ : IsPtOn (puAmalgam c.pu.le) α β δ) (hp : IsPtOn (puAmalgam c.pu.le) α β p)
    (hP : IsPtOn (puAmalgam c.pu.le) γ β P) (hR : IsPtOn (puAmalgam c.pu.le) γ β R) (hPR : P ≠ R)
    (hY : pencil (puAmalgam c.pu.le) γ P ≤ Qv (puAmalgam c.pu.le) β ⊓ ptQ _ α p)
    (hU : Qv (puAmalgam c.pu.le) β ⊓ ptQ _ γ R ≤ ptSub (puAmalgam c.pu.le) α δ ⊔ Qv _ γ)
    {ψ : ↥(stab (puAmalgam c.pu.le) γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψU : IsSumOfNaturalModulesVia (stab _ γ) (Uloc c.pu.le L γ) ⊥ ψ false 1)
    (hPc : ∀ u : ↥(Uloc c.pu.le L γ), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
      natVec hψU u ∈ pt0)
    (hT : natImage ψ (Qv (puAmalgam c.pu.le) β) = qLn) :
    (∀ k ∈ ptL (puAmalgam c.pu.le) γ ψ, Odd (orderOf k) →
        ∀ v ∈ pencil (puAmalgam c.pu.le) γ P, ⁅k, v⁆ ∈ ptSub (puAmalgam c.pu.le) γ P) ∨
      ∃ (N : Subgroup (puAmalgam c.pu.le).Universal) (βv : ↥N →* Multiplicative (Fin 2 → F)),
        ptSub (puAmalgam c.pu.le) γ P ≤ N ∧ N ≤ pencil (puAmalgam c.pu.le) γ P ∧
        Function.Surjective βv ∧
        (∀ x : ↥N, βv x = 1 ↔ (x : (puAmalgam c.pu.le).Universal) ∈ ptSub _ γ P) ∧
        (∀ k ∈ ptL (puAmalgam c.pu.le) γ ψ, Odd (orderOf k) →
          ∀ v ∈ pencil (puAmalgam c.pu.le) γ P, ⁅k, v⁆ ∈ N) ∧
        ∀ (k : ↥(ptL (puAmalgam c.pu.le) γ ψ)) (u v : ↥N),
          (v : (puAmalgam c.pu.le).Universal) = k * u * k⁻¹ →
          Multiplicative.toAdd (βv v) =
            (ptTheta ψ k : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (βv u) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hchar : CharP F 2 := charP_two_of_isSL3FullVia c.via
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hγβ).mp hγ
  have hPU := le_uloc_of_isPtOn c hγ hP
  have hPZ : P ≤ ZM (puAmalgam c.pu.le) γ := hPU.trans (uloc_le_zm c.pu hfull hγ)
  have hPUβ : P ≤ Usup (puAmalgam c.pu.le) γ β := by
    obtain ⟨_, _, _, he⟩ := hP
    rw [he]
    exact inf_le_left
  set K := ptL (puAmalgam c.pu.le) γ ψ with hKdef
  set Y := pencil (puAmalgam c.pu.le) γ P with hYdef
  set U := ptSub (puAmalgam c.pu.le) γ P with hUdef
  set X := ptSub (puAmalgam c.pu.le) α δ with hXdef
  have hKs : K ≤ stab (puAmalgam c.pu.le) γ := ptL_le_stab ψ
  have hKP : K ≤ Subgroup.normalizer (P : Set _) := ptL_le_normalizer c hψU hPU hPc
  have : Finite ↥K := I466b.finite_of_le_stab c.pu hγ hKs
  have : Finite ↥Y :=
    I466b.finite_of_le_stab c.pu hγ ((pencil_le_vv c hγ P).trans (vv_le_stab_self c γ))
  have hXT : X ≤ Qv (puAmalgam c.pu.le) β := (ptSub_le_pencil α δ).trans (pencil_le_qv c hα hαβ δ)
  have hTK : Qv (puAmalgam c.pu.le) β ≤ K := qv_le_ptL hγβ hT
  have hXK : X ≤ K := hXT.trans hTK
  have hTQ : Qv (puAmalgam c.pu.le) β ≤ Subgroup.normalizer (ptQ (puAmalgam c.pu.le) γ P : Set _) :=
    le_normalizer_ptQ (qv_le_stab_of_adj _ hγβ.symm)
      (qv_le_normalizer_of_le_usup h464 c hγ hγβ hPUβ)
  have hXidx : (ptQ (puAmalgam c.pu.le) γ P).relIndex X = Fintype.card F := by
    have hs : ptQ (puAmalgam c.pu.le) γ P ≤ stab _ γ := fun t ht => (mem_ptQ.mp ht).1
    refine le_antisymm ?_ ?_
    · rw [← relIndex_ptQ_qv h464 h465 h466a c hγ hγβ hP]
      exact Subgroup.relIndex_le_of_le_right hXT
        (relIndex_ne_zero_of_le_stab c hγ (qv_le_stab_of_adj _ hγβ.symm) _)
    · rw [← S46.relIndex_sup_of_le_normalizer (hXT.trans hTQ)]
      have hQγP : Qv (puAmalgam c.pu.le) γ ≤ ptQ _ γ P := qv_le_ptQ c hγ hPZ
      have hle : (Qv (puAmalgam c.pu.le) β ⊓ ptQ _ γ R) ⊔ ptQ _ γ P ≤ X ⊔ ptQ _ γ P :=
        sup_le (hU.trans (sup_le le_sup_left (hQγP.trans le_sup_right))) le_sup_right
      have hfin : (ptQ (puAmalgam c.pu.le) γ P).relIndex (X ⊔ ptQ _ γ P) ≠ 0 :=
        relIndex_ne_zero_of_le_stab c hγ (sup_le (hXT.trans (qv_le_stab_of_adj _ hγβ.symm)) hs) _
      refine le_trans ?_ (Subgroup.relIndex_le_of_le_right hle hfin)
      rw [S46.relIndex_sup_of_le_normalizer (inf_le_left.trans hTQ), ← Subgroup.inf_relIndex_right]
      have he : ptQ (puAmalgam c.pu.le) γ P ⊓ (Qv _ β ⊓ ptQ _ γ R) = Qv _ γ :=
        le_antisymm (le_trans (le_inf inf_le_left (inf_le_right.trans inf_le_right))
          (ptQ_inf_ptQ_le_qv h464 h465 c hγ hγβ hP hR hPR))
          (le_inf hQγP (le_inf (qv_le_qv _ c.pu.hyp20 hγ hγβ)
            (qv_le_ptQ c hγ ((le_uloc_of_isPtOn c hγ hR).trans (uloc_le_zm c.pu hfull hγ)))))
      rw [he, relIndex_qv_inf_ptQ h464 h465 h466a c hγ hγβ hR]
  have hXc : Nat.card ((X.subgroupOf K).map (ptTheta ψ)) = Nat.card F := by
    rw [card_map_ptTheta c hγ hψU hPU hPc hXK, hXidx, Nat.card_eq_fintype_card]
  have hXp : IsPGroup 2 ((X.subgroupOf K).map (ptTheta ψ)) := by
    have h1 : IsPGroup 2 ↥X := (isPGroup_qv _ c.pu.hyp20 hβ).to_le hXT
    exact (h1.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm).map _
  have hKV : K ≤ Subgroup.normalizer (Y : Set _) := le_normalizer_pencil hKs hKP
  have hKZ : K ≤ Subgroup.normalizer (U : Set _) := le_normalizer_ptSub hKs hKP
  have hZV : U ≤ Y := ptSub_le_pencil γ P
  have hVc : ∀ v ∈ Y, ∀ w ∈ Y, ⁅v, w⁆ ∈ U := fun v hv w hw =>
    zm_le_ptSub c hγ hP (sup_le hPZ (zloc_le_zm c.pu hfull hγ)
      (commutator_pencil_pencil_le h464 h465 h466a c hγ hγβ hP
        (Subgroup.commutator_mem_commutator hv hw)))
  have hV2 : ∀ v ∈ Y, v * v ∈ U := fun v hv => mul_self_mem_ptSub h464 h465 h466a c hγ hγβ hP hv
  have hker : ∀ k : ↥K, ptTheta ψ k = 1 →
      ∀ v ∈ Y, ⁅(k : (puAmalgam c.pu.le).Universal), v⁆ ∈ U := by
    intro k hk v hv
    have hkQ := (ptTheta_eq_one_iff c hγ hψU hPU hPc k).mp hk
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (hB.commutator_pencil_ptQ_le_ptSub h464 h465 h466a hγ hγβ hP
      (Subgroup.commutator_mem_commutator hv hkQ))
  have hXV : U.relIndex (⁅Y, X⁆ ⊔ U) ≤ Fintype.card F :=
    relIndex_commutator_pencil_ptSub_le h464 h465 h466a c hα hαβ hγ hγβ hδ hp hP hR hPR hY hU
  exact natural_comm_of_ff hn (ptTheta ψ) (ptTheta_surjective hψs) hKV hKZ hZV hVc hV2 hker hXK
    hXp hXc hXV

end CFSG.Quasithin.MS93.S46R
