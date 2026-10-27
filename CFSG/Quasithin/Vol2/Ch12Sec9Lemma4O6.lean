module

public import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

namespace L1294O

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

theorem commutator_le_of_relIndex_le_two {G : Type*} [Group G] [Finite G] {Γ O : Subgroup G}
    (hidx : Γ.relIndex O ≤ 2) : ⁅O, O⁆ ≤ Γ := by
  have h0 : (Γ.subgroupOf O).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : (Γ.subgroupOf O).index ≤ 2 := hidx
  have hsq : ∀ x ∈ O, x ^ 2 ∈ Γ := by
    intro x hx
    rcases (by omega : (Γ.subgroupOf O).index = 1 ∨ (Γ.subgroupOf O).index = 2) with h1 | h2
    · have hmem : (⟨x ^ 2, O.pow_mem hx 2⟩ : O) ∈ Γ.subgroupOf O := by
        rw [Subgroup.index_eq_one.1 h1]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hmem
    · have h4 := Subgroup.sq_mem_of_index_two h2 (⟨x, hx⟩ : O)
      rw [Subgroup.mem_subgroupOf] at h4
      simpa using h4
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  have e : a * b * a⁻¹ * b⁻¹ = a ^ 2 * (a⁻¹ * b) ^ 2 * (b⁻¹) ^ 2 := by
    simp only [pow_two]
    group
  rw [e]
  exact Γ.mul_mem (Γ.mul_mem (hsq a ha) (hsq _ (O.mul_mem (O.inv_mem ha) hb)))
    (hsq _ (O.inv_mem hb))

theorem scalars_eq_bot {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    scalars (ZMod 2) V = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := (mem_scalars).1 hg
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  ·
    refine (Subgroup.mem_bot).2 (LinearEquiv.ext fun v => ?_)
    have h1 : v = 0 := g.injective (by rw [hc v, zero_smul, map_zero])
    rw [h1, map_zero]
    rfl
  · exact (Subgroup.mem_bot).2 (LinearEquiv.ext fun v => by rw [hc v, one_smul]; rfl)

theorem exists_simple_le {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} (hB : ∀ v, (∀ w, B v w = 0) → v = 0)
    {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (h5 : G112Concl5 B Γ) :
    ∃ Ω : Subgroup (V ≃ₗ[ZMod 2] V), Ω ≤ Γ ∧ IsSimpleGroup ↥Ω ∧ Nat.card Ω = 20160 ∧
      Nat.card Γ ≤ 40320 := by
  classical
  obtain ⟨hdim, q, hqadd, hqsmul, ⟨S, hSd, hSq⟩, hΓO, hidx⟩ := h5
  have hFD : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hfin : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective
  have hpolar : ∀ x y, QuadraticMap.polar q x y = B x y := fun x y => by
    rw [QuadraticMap.polar, hqadd]
    ring
  let Q : QuadraticForm (ZMod 2) V := QuadraticMap.ofPolar q
    (fun a x => by rw [hqsmul, smul_eq_mul])
    (fun x x' y => by rw [hpolar, hpolar, hpolar, LinearMap.map_add₂])
    (fun a x y => by rw [hpolar, hpolar, LinearMap.map_smul₂])
  have hQnd : (polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun x hx =>
      hB x fun w => by rw [← hpolar]; exact hx w
  have hSQ : ∀ x ∈ S, Q x = 0 := fun x hx => hSq x hx
  have hOeq : orthogonalSubgroupOf q = TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.ext fun γ => by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      exact Iff.rfl
  have hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 40320 := by
    obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hQnd (n := 3)
      (by rw [hdim]) ⟨S, by rw [hSd, hdim], hSQ⟩
    have h1 := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_congr e
    have h2 := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := ZMod 2) 2
    rw [← h1] at h2
    have h3 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 40320 := by
      rw [h2]
      simp [Finset.prod_Icc_succ_top]
    exact_mod_cast h3
  obtain ⟨b, hbQ, hbef, hbee, -, -⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.orthogonal_geometry_split_Witt_flags hQnd (r := 3)
      (by omega) ⟨S, hSd, hSQ⟩).1 0 (Nat.zero_le 3) (fun _ => ⊥)
      (fun i hi => by simp only [finrank_bot]; omega)
      (fun i hi => absurd hi (Nat.not_lt_zero i))
      (fun x hx => by rw [(Submodule.mem_bot _).1 hx, QuadraticMap.map_zero])
  let pair : Fin 3 → HypPair Q := fun i =>
    ⟨b (.inl i), b (.inr i), (hbQ i).1, (hbQ i).2, by rw [hbef i i]; simp⟩
  let P : ℕ → HypPair Q := fun i => if h : i < 3 then pair ⟨i, h⟩ else pair 0
  have hPi : ∀ i (h : i < 3), P i = pair ⟨i, h⟩ := fun i h => by simp only [P, h, dite_true]
  have hPo : ∀ i j, i < 3 → j < 3 → i ≠ j → (P i).Orth (P j) := by
    intro i j hi hj hij
    rw [hPi i hi, hPi j hj]
    have hne : (⟨i, hi⟩ : Fin 3) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Fin.val h)
    refine ⟨(hbee _ _).1, ?_, ?_, (hbee _ _).2⟩
    · show polar Q (b (.inl ⟨i, hi⟩)) (b (.inr ⟨j, hj⟩)) = 0
      rw [hbef]
      simp [hne]
    · show polar Q (b (.inr ⟨i, hi⟩)) (b (.inl ⟨j, hj⟩)) = 0
      rw [polar_comm, hbef]
      simp [Ne.symm hne]
  have htail : ∀ x ∈ tailSpace P 3, x = 0 := by
    intro x hx
    have hx' := mem_tailSpace.1 hx
    apply eq_zero_of_polar_eq_zero hQnd
    intro y
    have h0 : polarBilin Q x = 0 := b.ext fun k => by
      rw [polarBilin_apply_apply, LinearMap.zero_apply, polar_comm]
      rcases k with i | i
      · have := (hx' i i.2).1
        rw [hPi i i.2] at this
        exact this
      · have := (hx' i i.2).2
        rw [hPi i i.2] at this
        exact this
    simpa using LinearMap.congr_fun h0 y
  have hA : ∀ x ∈ tailSpace P 3, Q x = 0 → x = 0 := fun x hx _ => htail x hx
  have hA' : ∀ x ∈ tailSpace P 3, x ≠ 0 → ∀ y ∈ tailSpace P 3, polar Q x y = 0 →
      ∃ c : ZMod 2, y = c • x := fun x hx hx0 => absurd (htail x hx) hx0
  have h2 : (2 : ZMod 2) = 0 := rfl
  have hcomm := commutator_orthogonalGroup_eq_of_two_eq_zero hPo hQnd h2 hA hA' le_rfl
  have hidx2 := CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_eq_two_mul hQnd
    (hPo 0 1 (by norm_num) (by norm_num) (by norm_num)) ⟨S, hSd, hSQ⟩
    (orthogonalGroup_le_closure_of_two_eq_zero hPo hQnd h2 hA hA' (by norm_num))
  have hsimple : IsSimpleGroup (ProjElementary Q) :=
    isSimpleGroup_projElementary hQnd (T := S) (by rw [hSd]) hSQ
  have hZ : (scalars (ZMod 2) V).subgroupOf (elementaryGroup Q) = ⊥ := by
    rw [scalars_eq_bot, Subgroup.bot_subgroupOf]
  have hE : IsSimpleGroup ↥(elementaryGroup Q) :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).isSimpleGroup
  refine ⟨elementaryGroup Q, ?_, hE, by omega, ?_⟩
  · rw [← hcomm]
    rw [hOeq] at hidx
    exact commutator_le_of_relIndex_le_two hidx
  · rw [← hO]
    exact Subgroup.card_le_of_le (hOeq ▸ hΓO)

end L1294O

end CFSG.Quasithin.H13
