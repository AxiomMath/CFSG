module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwap

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section NormalClosure

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem isQuasisimple_unitaryBlock {N : Finset (Fin n)} (hN3 : 3 ≤ N.card)
    (hNq : (N.card, 2 ^ f) ≠ (3, 2)) : CFSG.Open.IsQuasisimple (unitaryBlock h N) := by
  have hq : CFSG.IsQuasisimple (unitaryBlock h N) :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv (unitaryBlockEquiv h N)
      (isQuasisimple_unitarySU h hN3 hNq)
  have := hq.1
  exact ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩

variable {G : Type*} [Group G] {L : Subgroup G} {h} {e : L ≃* unitaryPSU h n} {t : G}
  {X : Subgroup G} {N : Finset (Fin n)}

theorem SwapNeighbourParam.range_le (P : SwapNeighbourParam e t X N) (hN3 : 3 ≤ N.card)
    (hNq : (N.card, 2 ^ f) ≠ (3, 2)) {H : Subgroup G} (hLH : L ≤ H) {i j : Fin n} (hij : i ≠ j)
    (hi : i ∈ N) (hj : j ∈ N) (hH : P.fst {i, j} ≤ H) : P.Ψ.range ≤ H := by
  set Y : Subgroup (unitaryBlock h N) := H.comap (P.Ψ.comp (MonoidHom.inl _ _)) with hY
  have hdiag : ∀ g : unitaryBlock h N, P.Ψ (g, g) ∈ H := fun g => by
    rw [P.diag]
    exact hLH (e.symm _).2
  have hnorm : Y.Normal := ⟨fun y hy g => by
    rw [hY, mem_comap] at hy ⊢
    have hsplit : (MonoidHom.inl (unitaryBlock h N) (unitaryBlock h N)) (g * y * g⁻¹) =
        (g, g) * (y, 1) * (g, g)⁻¹ := by
      ext <;> simp
    rw [MonoidHom.comp_apply, hsplit, map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (hdiag g) hy) (inv_mem (hdiag g))⟩
  have hmem : ∀ {x : unitaryBlock h N}, (x : unitarySU 2 f K n) ∈ unitaryBlock h {i, j} → x ∈ Y :=
    fun hx => hH (P.apply_inl_mem_fst hx)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
    (isQuasisimple_unitaryBlock h hN3 hNq) Y with hc | htop
  · exfalso
    obtain ⟨κ, hκN, hκ⟩ := exists_norm_eq_one_ne_one h
    set κ' : (Units.map h.normHom).ker := ⟨κ, h.mem_ker_normUnits.2 hκN⟩ with hκ'
    have hw₀ := permSU_swap_mem_unitaryBlock h i j
    have hd₀ := torusDiagSU_unitaryRootTorusHom_mem_unitaryBlock h hij κ'
    have hijN := SwapNeighbourParam.pair_subset_of_mem hi hj
    set w : unitaryBlock h N := ⟨_, unitaryBlock_mono h hijN hw₀⟩ with hw
    set d : unitaryBlock h N := ⟨_, unitaryBlock_mono h hijN hd₀⟩ with hd
    obtain ⟨k, hkN, hkij⟩ : ∃ k ∈ N, k ∉ ({i, j} : Finset (Fin n)) := by
      refine Finset.exists_mem_notMem_of_card_lt_card ?_
      rw [Finset.card_pair hij]
      omega
    have hki : k ≠ i := fun hk => hkij (hk ▸ Finset.mem_insert_self _ _)
    have hkj : k ≠ j := fun hk => hkij (hk ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hcY : w * d * w⁻¹ * d⁻¹ ∈ Y :=
      mul_mem (mul_mem (mul_mem (hmem hw₀) (hmem hd₀)) (inv_mem (hmem hw₀))) (inv_mem (hmem hd₀))
    have hσ₀ := permSU_swap_mem_unitaryBlock h i k
    set σ : unitaryBlock h N :=
      ⟨_, unitaryBlock_mono h (SwapNeighbourParam.pair_subset_of_mem hi hkN) hσ₀⟩ with hσ
    have hcomm := congrArg (fun z : unitaryBlock h N => (z : unitarySU 2 f K n))
      ((mem_center_iff.1 (hc hcY)) σ)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcomm
    exact permSU_swap_mul_commutator_ne h hij hki.symm hkj.symm (κ := κ') hκ hcomm
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    have hx : P.Ψ (x, 1) ∈ H := (show x ∈ Y from htop ▸ mem_top x)
    have hy : P.Ψ (y, 1) ∈ H := (show y ∈ Y from htop ▸ mem_top y)
    have hsplit : ((x, y) : unitaryBlock h N × unitaryBlock h N) =
        (x, 1) * ((y, 1)⁻¹ * (y, y)) := by
      ext <;> simp
    rw [hsplit, map_mul, map_mul, map_inv]
    exact mul_mem hx (mul_mem (inv_mem hy) (hdiag y))

end NormalClosure

section Global

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

theorem le_swapGlobal [Finite G] (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) (hnf : (n, f) ≠ (6, 1))
    {t : G}
    (hparam : ∀ (a b : Fin n) (hab : a ≠ b),
      Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin n)))) : L ≤ swapGlobal e := by
  obtain ⟨G₁, -, -, hsup, -, hsurj⟩ := exists_swapFactors_unitaryRootTorus e hn hnf hparam
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hsurj y hy
  rw [← hsup]
  exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨x, hx, rfl⟩)

theorem swapGlobal_le_iSup_neighbourCore (e : L ≃* unitaryPSU h n)
    (hn : (swapCore n f).card + 3 ≤ n) :
    swapGlobal e ≤ ⨆ (a : Fin n) (b : Fin n) (hab : a ≠ b), neighbourCore e hab := by
  refine iSup_le fun x => ?_
  obtain ⟨a, b, hab, ha, hb⟩ := LinearPilot.exists_two_index_notMem
    (S := insert (x : Fin n) (swapCore n f)) (by rw [Finset.card_insert_of_notMem x.2]; omega)
  exact (pieceCore_le_neighbourCore e hab (subset_compl_pair_iff.2 ⟨ha, hb⟩)).trans
    (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl)))

theorem swapGlobal_eq_iSup_neighbourCore [Finite G] (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n)
    (hnf : (n, f) ≠ (6, 1)) {t : G}
    (hparam : ∀ (a b : Fin n) (hab : a ≠ b),
      Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin n)))) :
    swapGlobal e = ⨆ (a : Fin n) (b : Fin n) (hab : a ≠ b), neighbourCore e hab := by
  obtain ⟨hA2, hAn, hAq, -⟩ := swapCore_hypotheses h hn hnf
  refine le_antisymm (swapGlobal_le_iSup_neighbourCore e (by omega)) ?_
  have hLG := le_swapGlobal e hn hnf hparam
  obtain ⟨x₀, -, hx₀⟩ : ∃ x ∈ (Finset.univ : Finset (Fin n)), x ∉ swapCore n f :=
    Finset.exists_mem_notMem_of_card_lt_card
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  have hpieceJ : ∀ J : Finset (Fin n), J.card = (swapCore n f).card + 1 →
      pieceCore e J ≤ swapGlobal e := by
    intro J hJ
    obtain ⟨ρ, hρ⟩ := exists_perm_map_eq_of_card_eq
      ((Finset.card_insert_of_notMem hx₀).trans hJ.symm)
    obtain ⟨w, hw, hI, -⟩ := exists_pieceCore_map_conj h e ρ
    have h0 : pieceCore e (insert x₀ (swapCore n f)) ≤ swapGlobal e :=
      le_iSup (fun x : {x : Fin n // x ∉ swapCore n f} =>
        pieceCore e (insert (x : Fin n) (swapCore n f))) ⟨x₀, hx₀⟩
    have hwn : w ∈ normalizer (swapGlobal e : Set G) := le_normalizer (hLG hw)
    rw [← hρ, (hI _).1, ← F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1 hwn]
    exact map_mono h0
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  obtain ⟨P⟩ := hparam a b hab
  obtain ⟨J, hJN, hJ⟩ : ∃ J ⊆ ({a, b}ᶜ : Finset (Fin n)), J.card = (swapCore n f).card + 1 :=
    Finset.exists_subset_card_eq (by rw [card_compl_pair hab]; omega)
  obtain ⟨i, hiJ, j, hjJ, hij⟩ : ∃ i ∈ J, ∃ j ∈ J, i ≠ j := Finset.one_lt_card.1 (by omega)
  have hJq : (J.card, 2 ^ f) ≠ (3, 2) := by rw [hJ]; exact hAq
  have hperf := commutator_unitaryBlock_eq_of_three_le h (by omega) hJq
  have hfst : P.fst {i, j} ≤ swapGlobal e := by
    have hM := P.pieceCore_eq_fst_sup_snd hJN (by omega)
      (two_le_card_compl_of_subset_compl_pair hab hJN) hperf
      (modelToG_unitaryRootTorus_le e hab hJN)
    exact (P.fst_mono (SwapNeighbourParam.pair_subset_of_mem hiJ hjJ)).trans
      ((le_sup_left.trans hM.symm.le).trans (hpieceJ J hJ))
  rw [neighbourCore_def, ← P.range_eq]
  refine P.range_le (by rw [card_compl_pair hab]; omega) ?_ hLG hij (hJN hiJ) (hJN hjJ) hfst
  rw [card_compl_pair hab]
  intro h'
  have := congrArg Prod.fst h'
  simp only at this
  omega

theorem exists_swapFactors_iSup_neighbourCore [Finite G] (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n)
    (hnf : (n, f) ≠ (6, 1)) {t : G}
    (hparam : ∀ (a b : Fin n) (hab : a ≠ b),
      Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin n)))) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        ⨆ (a : Fin n) (b : Fin n) (hab : a ≠ b), neighbourCore e hab ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  rw [← swapGlobal_eq_iSup_neighbourCore e hn hnf hparam]
  exact exists_swapFactors_unitaryRootTorus e hn hnf hparam

@[expose] noncomputable def swapNeighbourJoin (e : L ≃* unitaryPSU h n) : Subgroup G :=
  ⨆ (a : Fin n) (b : Fin n) (hab : a ≠ b), neighbourCore e hab

theorem swapNeighbourJoin_def (e : L ≃* unitaryPSU h n) :
    swapNeighbourJoin e = ⨆ (a : Fin n) (b : Fin n) (hab : a ≠ b), neighbourCore e hab :=
  rfl

end Global

end CFSG.SeitzReduction.UnitaryPilot
