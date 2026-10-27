module

public import CFSG.Quasithin.Background.RonanG25GroupDefs
public import CFSG.Quasithin.Background.RonanG25Chains
public import CFSG.Quasithin.Background.RonanG25Transport
public import CFSG.Quasithin.Background.RonanG25Central

public section

namespace CFSG.Quasithin.RonanG25

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

section GroupV

variable {G : Type} [Group G] [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G}

theorem g25v_diag_odd {F : Type} [Field F] [Finite F] [CharP F 2] {c : F} (hc : c ≠ 0) :
    ∃ d : SL(3, F), d ∈ Pt (vE F 0) ∧ Odd (orderOf d) ∧ d • vE F 0 = c • vE F 0 := by
  obtain ⟨d, hd⟩ : ∃ d : SL(3, F), (d : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![c, c⁻¹, 1] :=
    ⟨⟨Matrix.diagonal ![c, c⁻¹, 1], by
      rw [Matrix.det_diagonal, Fin.prod_univ_three]
      simp [hc]⟩, rfl⟩
  have hPt : d ∈ Pt (vE F 0) := by
    rw [mem_Pt_e0, hd]
    simp
  have hsmul : d • vE F 0 = c • vE F 0 := by
    ext i
    rw [smul_single_one, hd]
    fin_cases i <;> simp
  have hc1 : c ^ (Nat.card F - 1) = 1 := by
    haveI : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one c hc
  have hdk : d ^ (Nat.card F - 1) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hd, Matrix.diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hc1, inv_pow]
  have hodd : Odd (Nat.card F - 1) := by
    obtain ⟨k, hk⟩ := card_F_even (F := F)
    have : 0 < Nat.card F := Nat.card_pos
    exact ⟨k - 1, by omega⟩
  exact ⟨d, hPt, Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hdk), hsmul⟩

theorem g25v_l1_of_odd (St : L3Setting n V V₁ L T H) {A : SL(3, GaloisField 2 n)}
    (hA : A ∈ Pt (vE (GaloisField 2 n) 0)) (ho : Odd (orderOf A)) :
    ∃ a : ↥L, (a : G) ∈ lOne L V₁ ∧ St.D.θ a = A := by
  have hmem : A ∈ oTwoUpper (((L ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf L).map St.D.θ) := by
    rw [St.map_theta_N]
    exact mem_oTwoUpper_of_odd hA ho
  rw [oTwoUpper_map St.D.θ] at hmem
  obtain ⟨a₁, ha₁, ha₁θ⟩ := hmem
  refine ⟨a₁, ?_, ha₁θ⟩
  have h3 := oTwoUpper_map L.subtype ((L ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf L)
  have h4 : ((L ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf L).map L.subtype =
      L ⊓ Subgroup.normalizer (V₁ : Set G) := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 inf_le_left
  rw [h4] at h3
  have h5 : (a₁ : G) ∈ (oTwoUpper ((L ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf L)).map
      L.subtype := ⟨a₁, ha₁, rfl⟩
  rw [← h3] at h5
  exact h5

theorem exists_l1_torus (St : L3Setting n V V₁ L T H) {c : GaloisField 2 n} (hc : c ≠ 0) :
    ∃ a : ↥L, (a : G) ∈ lOne L V₁ ∧
      St.D.θ a • vE (GaloisField 2 n) 0 = c • vE (GaloisField 2 n) 0 := by
  obtain ⟨d, hdPt, hdodd, hdsmul⟩ := g25v_diag_odd (F := GaloisField 2 n) hc
  obtain ⟨a, ha, haθ⟩ := g25v_l1_of_odd St hdPt hdodd
  exact ⟨a, ha, by rw [haθ]; exact hdsmul⟩

theorem l1Rep (St : L3Setting n V V₁ L T H) : L1Rep (rho St.D) :=
  { stab := fun x =>
      St.theta_mem_Pt_of_normalizer ⟨(x : G), lOne_le_L x.2⟩ (lOne_le_normalizer x.2)
    blk := fun M hM => by
      obtain ⟨a, ha, haθ⟩ := St.exists_l1_blk M hM
      exact ⟨⟨(a : G), ha⟩, haθ⟩
    torus := fun c hc => by
      obtain ⟨a, ha, haθ⟩ := exists_l1_torus St hc
      exact ⟨⟨(a : G), ha⟩, haθ⟩ }

theorem g25v_pre_bot {E : Type} [AddCommGroup E] {B : Subgroup G}
    {φ : ↥B →* Multiplicative E} (hφ : Function.Injective φ) : pre B φ ⊥ = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyB, h⟩ := mem_pre.1 hy
  have h1 : φ ⟨y, hyB⟩ = 1 :=
    Multiplicative.toAdd.injective ((AddSubgroup.mem_bot.1 h).trans toAdd_one.symm)
  have h2 : (⟨y, hyB⟩ : ↥B) = 1 := hφ (h1.trans (map_one φ).symm)
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h2

theorem g25v_pre_top {E : Type} [AddCommGroup E] {B : Subgroup G}
    {φ : ↥B →* Multiplicative E} : pre B φ ⊤ = B := by
  apply le_antisymm (pre_le _)
  intro y hy
  exact mem_pre.2 ⟨hy, AddSubgroup.mem_top _⟩

theorem chain_V_group (St : L3Setting n V V₁ L T H) {ord : Bool} :
    ChainCounts (GaloisField 2 n) (lOne L V₁) ord ⊥ V 1
      (if 2 < Nat.card (GaloisField 2 n) then 1 else 0) := by
  have hinj : Function.Injective St.D.ψ.toMonoidHom := fun a b h => St.D.ψ.injective h
  have hN : ∀ e : Fin 3 → GaloisField 2 n,
      e ∈ (⊤ : AddSubgroup (Fin 3 → GaloisField 2 n)) ↔
        ∃ y : ↥V, St.D.ψ.toMonoidHom y = Multiplicative.ofAdd e := fun e =>
    ⟨fun _ => ⟨St.D.ψ.symm (Multiplicative.ofAdd e), St.D.ψ.apply_symm_apply _⟩,
      fun _ => AddSubgroup.mem_top _⟩
  have hE : Equivariant (lOne L V₁) V St.D.ψ.toMonoidHom (actV (rho St.D)) :=
    { normalizes := fun x hx y hy =>
        (Subgroup.mem_normalizer_iff.1 (St.D.hnorm (lOne_le_L hx)) y).1 hy
      equiv := fun x y y' h => by
        have hxL : (x : G) ∈ L := lOne_le_L x.2
        have h2 : conjAct V ⟨(x : G), St.D.hnorm hxL⟩ y = y' :=
          Subtype.ext (by rw [conjAct_coe_apply]; exact h)
        have h1 : St.D.ψ y' = natAct3 (St.D.θ ⟨(x : G), hxL⟩) (St.D.ψ y) := by
          rw [← h2]
          exact St.D.equiv ⟨(x : G), hxL⟩ y
        show St.D.ψ y' = Multiplicative.ofAdd (actV (rho St.D) x (Multiplicative.toAdd (St.D.ψ y)))
        rw [h1, natAct3_apply]
        rfl }
  have hT : ChainCounts (GaloisField 2 n) (lOne L V₁) ord
      (pre V St.D.ψ.toMonoidHom ⊥) (pre V St.D.ψ.toMonoidHom ⊤) 1
      (if 2 < Nat.card (GaloisField 2 n) then 1 else 0) :=
    ModChain.transport hN hE (chain_V (l1Rep St)) le_top
  rw [g25v_pre_bot hinj, g25v_pre_top] at hT
  exact hT

theorem chain_V_S₂_group (St : L3Setting n V V₁ L T H) {g h : G} (hsub : SubFacts V L H g h)
    {ord : Bool} : ChainCounts (GaloisField 2 n) (lOne L V₁) ord V (gS₂ V H g h) 0 0 := by
  have hXLU : lOne L V₁ ≤ L ⊔ conjClosure V H :=
    lOne_le_L.trans (le_sup_left : L ≤ L ⊔ conjClosure V H)
  have hA : Inv (lOne L V₁) V := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1 (hsub.I_V (hXLU hx)) y).1 hy
  have hB : Inv (lOne L V₁) (gS₂ V H g h) := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1 (hsub.I_S₂ (hXLU hx)) y).1 hy
  have hS₂S : gS₂ V H g h ≤ gS V H L := hsub.S₂_le_S₃.trans hsub.S₃_le_S
  have hnorm : ∀ y ∈ gS₂ V H g h, ∀ z ∈ V, y * z * y⁻¹ ∈ V := by
    intro y hy z hz
    have hzc : z ∈ gS V H L ⊓ Subgroup.centralizer (gS V H L : Set G) := hsub.V_le_center hz
    have hc : y * z = z * y := Subgroup.mem_centralizer_iff.1 hzc.2 y (hS₂S hy)
    rw [hc]
    simpa using hz
  have hcen : FactorCentral (lOne L V₁) V (gS₂ V H g h) := by
    intro x hx y hy
    have hcomm : ⁅y, x⁆ ∈ ⁅gS₂ V H g h, L ⊔ conjClosure V H⁆ :=
      Subgroup.commutator_mem_commutator hy (hXLU hx)
    have h1 : ⁅y, x⁆ ∈ V := hsub.comm hcomm
    have e : x * y * x⁻¹ * y⁻¹ = ⁅y, x⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact V.inv_mem h1
  have h2 : ∀ y ∈ gS₂ V H g h, ∃ k : ℕ, y ^ 2 ^ k ∈ V := by
    intro y hy
    have hyU : y ∈ conjClosure V H :=
      (inf_le_left.trans inf_le_left : gS₂ V H g h ≤ conjClosure V H) hy
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem St.isPGroup_U hyU
    exact ⟨k, by rw [hk]; exact V.one_mem⟩
  exact exists_chain_central hsub.V_le_S₂ hA hB hnorm hcen h2

end GroupV

end CFSG.Quasithin.RonanG25
