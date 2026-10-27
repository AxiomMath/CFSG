module

public import CFSG.RankThree.GF2n.Tim81.Sec5.S51S52
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

theorem Sec5.Stmt57.le_of_commute (h57 : Sec5.Stmt57 M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V) (hc : ⁅U, U'⁆ = ⊥) :
    ⁅Pc M V, U⁆ ≤ Pc M V ⊓ Subgroup.centralizer (U' : Set G) := by
  rcases h57 U hU U' hU' with ⟨h, -⟩ | ⟨-, hL2⟩ | ⟨-, -, hne⟩
  · exact h
  · exact absurd hc (IsL2Gen.commutator_ne_bot hL2)
  · exact absurd hc hne

theorem Sec5Hyp.exists_sigma_data (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) :
    ∃ g y : G, Sec45Shape M V (hOf M V g) g ∧ y ∈ hOf M V g ∧ U = conjSubgroup g V ∧
      conjSubgroup g V = conjSubgroup y V ∧ conjSubgroup y V ≠ V ∧
      ⁅Pc M V, U⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V g) ∧
      Pc M V ⊓ Subgroup.centralizer (U : Set G) = Pc M V ⊓ kOf V (hOf M V g) ∧
      Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U⁆ : Subgroup G) : Set G) =
        Pc M V ⊓ kOf V (hOf M V g) := by
  classical
  obtain ⟨g, hUeq, hHg⟩ := hU
  have hUg : conjSubgroup g V ∈ sigmaSet M V := ⟨g, rfl, hHg⟩
  have hSg := hS.shape hUg
  obtain ⟨y, hyH, -, hVy, -⟩ :=
    hS.toRootHyp.exists_mem_conj_eq_of_eq_sup hSg.Pc_le hSg.hH
  have hyV : conjSubgroup y V ≠ V := fun hc =>
    ne_of_mem_sigmaSet hS.toRootHyp hUg (hVy.trans hc)
  have hE : ⁅Pc M V, U⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V g) := by
    rw [hUeq, hVy]
    exact Sec45Shape.commutator_Pc_conj_eq hS.toRootHyp hSg hyH hyV
  have hC : Pc M V ⊓ Subgroup.centralizer (U : Set G) = Pc M V ⊓ kOf V (hOf M V g) := by
    rw [hUeq, hVy]
    exact hSg.Pc_inf_centralizer_conj hS.toRootHyp hyH hyV
  have hCE : Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U⁆ : Subgroup G) : Set G) =
      Pc M V ⊓ kOf V (hOf M V g) := by
    rw [hE]
    exact hSg.Pc_inf_centralizer_inf_xOf hS.toRootHyp
  exact ⟨g, y, hSg, hyH, hUeq, hVy, hyV, hE, hC, hCE⟩

theorem Sec5Hyp.Pc_inf_centralizer_eq_commutator (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) :
    Pc M V ⊓ Subgroup.centralizer (U : Set G) =
      Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U⁆ : Subgroup G) : Set G) := by
  obtain ⟨g, y, -, -, -, -, -, -, hC, hCE⟩ := hS.exists_sigma_data hU
  rw [hC, hCE]

theorem Sec5Hyp.card_commutator_Pc (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) :
    Nat.card ↥⁅Pc M V, U⁆ = Nat.card V ^ 3 := by
  obtain ⟨g, -, -, hcard, -, -, -, -⟩ := hS.commutator_facts_of_mem_sigmaSet hU
  exact hcard

theorem Sec5Hyp.card_Pc_inf_centralizer (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) :
    Nat.card ↥(Pc M V ⊓ Subgroup.centralizer (U : Set G)) * Nat.card V ^ 2 =
      Nat.card ↥(Pc M V) := by
  rw [hS.Pc_inf_centralizer_eq_commutator hU]
  obtain ⟨g, -, -, -, hcard, -, -, -⟩ := hS.commutator_facts_of_mem_sigmaSet hU
  exact hcard

theorem Sec5Hyp.V_le_commutator (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) : V ≤ ⁅Pc M V, U⁆ := by
  obtain ⟨g, -, -, -, -, hVE, -, -⟩ := hS.commutator_facts_of_mem_sigmaSet hU
  exact hVE

theorem Sec5Hyp.commutator_le_Pc (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) : ⁅Pc M V, U⁆ ≤ Pc M V := by
  obtain ⟨g, -, hE, -, -, -, -, -⟩ := hS.commutator_facts_of_mem_sigmaSet hU
  rw [hE]
  exact inf_le_left

theorem Sec5Hyp.commutator_Pc_eq_V (hS : Sec5Hyp M V)
    (hne : (sigmaSet M V).Nonempty) : ⁅Pc M V, Pc M V⁆ = V := by
  obtain ⟨U, hU⟩ := hne
  obtain ⟨g, y, hSg, -, -, -, -, -, -, -⟩ := hS.exists_sigma_data hU
  exact hSg.commutator_Pc hS.toRootHyp

theorem Hyp.mul_self_eq_one_of_mem_conj (h : Hyp M V) {g x : G}
    (hx : x ∈ conjSubgroup g V) : x * x = 1 := by
  have hV : Assembly.IsElemAbelian 2 (conjSubgroup g V) :=
    h.elem.map (MulAut.conj g).toMonoidHom
  simpa [pow_two] using hV.2 x hx

theorem Hyp.commute_of_mem_conj (h : Hyp M V) {g x y : G}
    (hx : x ∈ conjSubgroup g V) (hy : y ∈ conjSubgroup g V) : x * y = y * x := by
  have hV : Assembly.IsElemAbelian 2 (conjSubgroup g V) :=
    h.elem.map (MulAut.conj g).toMonoidHom
  exact congrArg Subtype.val (hV.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem Sec5Hyp.shape_conj_self (hS : Sec5Hyp M V) {c : G}
    (hc : conjSubgroup c V ∈ sigmaSet M V) :
    Sec45Shape (conjSubgroup c M) (conjSubgroup c V) (hOf M V c) c⁻¹ := by
  have hV : V ∈ sigmaSet (conjSubgroup c M) (conjSubgroup c V) :=
    (hS.mem_sigmaSet_iff_self_mem (g := c)).mp hc
  have hshape : Sec45Shape (conjSubgroup c M) (conjSubgroup c V)
      (hOf (conjSubgroup c M) (conjSubgroup c V) c⁻¹) c⁻¹ :=
    (hS.conj c).shape (g := c⁻¹) (by
      rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
      exact hV)
  have hOf_eq : hOf (conjSubgroup c M) (conjSubgroup c V) c⁻¹ = hOf M V c := by
    unfold hOf
    rw [Pc_conjSubgroup,
      show conjSubgroup c⁻¹ (conjSubgroup c (Pc M V)) = Pc M V by
        rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]]
    exact sup_comm _ _
  rwa [hOf_eq] at hshape

theorem Sec5Hyp.eq_V_or_mem_fSet_or_eq_commutator (hS : Sec5Hyp M V)
    {U : Subgroup G} (hU : U ∈ sigmaSet M V) {X : Subgroup G} (hVX : V ≤ X)
    (hXE : X ≤ ⁅Pc M V, U⁆)
    (hX : ∀ x ∈ X, x ∉ V → ∃ A ∈ fSet M V, x ∈ A ∧ A ≤ X) :
    X = V ∨ X ∈ fSet M V ∨ X = ⁅Pc M V, U⁆ := by
  classical
  by_cases hXV : X = V
  · exact Or.inl hXV
  right
  obtain ⟨x₁, hx₁X, hx₁V⟩ :=
    SetLike.exists_of_lt (lt_of_le_of_ne hVX (fun h => hXV h.symm))
  obtain ⟨A₁, hA₁, hx₁A₁, hA₁X⟩ := hX x₁ hx₁X hx₁V
  by_cases hA₁eq : A₁ = X
  · exact Or.inl (hA₁eq ▸ hA₁)
  have hVA₁ : V ≤ A₁ := by
    obtain ⟨-, -, U₀, -, x₀, -, hEq⟩ := hA₁
    rw [hEq]
    exact le_sup_left
  obtain ⟨x₂, hx₂X, hx₂A₁⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hA₁X hA₁eq)
  have hx₂V : x₂ ∉ V := fun h => hx₂A₁ (hVA₁ h)
  obtain ⟨A₂, hA₂, hx₂A₂, hA₂X⟩ := hX x₂ hx₂X hx₂V
  have hcap : A₁ ⊓ A₂ = V := by
    rcases hS.stmt51e A₁ hA₁ A₂ hA₂ with heq | hcap
    · exact absurd (heq ▸ hx₂A₂) hx₂A₁
    · exact hcap
  obtain ⟨g, y, hSg, -, -, -, -, hE, -, -⟩ := hS.exists_sigma_data hU
  have hEab : ∀ a ∈ ⁅Pc M V, U⁆, ∀ b ∈ ⁅Pc M V, U⁆, a * b = b * a := by
    intro a ha b hb
    have ha' : a ∈ Tim79a.xOf V (hOf M V g) := by rw [hE] at ha; exact ha.2
    have hb' : b ∈ Tim79a.xOf V (hOf M V g) := by rw [hE] at hb; exact hb.2
    exact congrArg Subtype.val ((hSg.isElemAbelian hS.toRootHyp).1.is_comm.comm
      ⟨a, ha'⟩ ⟨b, hb'⟩)
  have hnorm : A₁ ≤ Subgroup.normalizer (A₂ : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    have hcomm := hEab a (hA₁X.trans hXE ha) b (hA₂X.trans hXE hb)
    have hEq : a * b * a⁻¹ = b := by
      calc a * b * a⁻¹ = b * a * a⁻¹ := by rw [hcomm]
        _ = b := by group
    rwa [hEq]
  have hcard := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (A := A₁) (B := A₂) hnorm
  rw [hcap, hA₁.2.1, hA₂.2.1] at hcard
  have hcardSup : Nat.card ↥(A₁ ⊔ A₂) = Nat.card V ^ 3 := by
    have h1 : Nat.card ↥(A₁ ⊔ A₂) * Nat.card V =
        Nat.card V ^ 2 * Nat.card V ^ 2 := hcard
    have h2 : Nat.card V ^ 2 * Nat.card V ^ 2 = Nat.card V ^ 3 * Nat.card V := by
      ring
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hsupX : A₁ ⊔ A₂ = X := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hA₁X hA₂X) ?_
    calc Nat.card ↥X ≤ Nat.card ↥⁅Pc M V, U⁆ := Subgroup.card_le_of_le hXE
      _ = Nat.card V ^ 3 := hS.card_commutator_Pc hU
      _ = Nat.card ↥(A₁ ⊔ A₂) := hcardSup.symm
  have hXeqE : X = ⁅Pc M V, U⁆ := by
    refine Subgroup.eq_of_le_of_card_ge hXE ?_
    rw [← hsupX, hcardSup, hS.card_commutator_Pc hU]
  exact Or.inr hXeqE

theorem Sec45Shape.mem_Pc_of_commutator_mem (h : RootHyp M V) {H : Subgroup G} {h₀ : G}
    (hS : Sec45Shape M V H h₀) {b : G} (hbM : b ∈ M) (hbV : b ∈ Subgroup.centralizer (V : Set G))
    (hbP : ∀ p ∈ Pc M V, ⁅p, b⁆ ∈ V) : b ∈ Pc M V := by
  let Y : Subgroup G :=
    { carrier := {c | c ∈ M ∧ ∀ p ∈ Pc M V, ⁅p, c⁆ ∈ V}
      one_mem' := ⟨M.one_mem, fun p _ => by simp⟩
      mul_mem' := by
        rintro c d ⟨hcM, hc⟩ ⟨hdM, hd⟩
        refine ⟨M.mul_mem hcM hdM, fun p hp => ?_⟩
        have hpc : ⁅p, c⁆ ∈ V := hc p hp
        have hpd : ⁅p, d⁆ ∈ V := hd p hp
        have hconj : c * ⁅p, d⁆ * c⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp (h.toHyp.le_normalizer hcM) _).mp hpd
        rw [commutatorElement_mul_right_eq_mul_conj,
          show ⁅p, c⁆ * c * ⁅p, d⁆ * c⁻¹ = ⁅p, c⁆ * (c * ⁅p, d⁆ * c⁻¹) by group]
        exact V.mul_mem hpc hconj
      inv_mem' := by
        rintro c ⟨hcM, hc⟩
        refine ⟨M.inv_mem hcM, fun p hp => ?_⟩
        have hpc : ⁅p, c⁆ ∈ V := hc p hp
        have hconj : c⁻¹ * ⁅p, c⁆⁻¹ * c ∈ V := by
          simpa using (Subgroup.mem_normalizer_iff.mp
            (h.toHyp.le_normalizer (M.inv_mem hcM)) _).mp (V.inv_mem hpc)
        rw [commutatorElement_inv_right, ← commutatorElement_inv]
        exact hconj }
  have hbY : b ∈ Y := ⟨hbM, hbP⟩
  have hzp : Subgroup.zpowers b ≤ Y := Subgroup.zpowers_le.mpr hbY
  have hcomm_le : ⁅Pc M V, Subgroup.zpowers b⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro p hp z hz
    exact (hzp hz).2 p hp
  exact hS.le_Pc_of_commutator_le h (X := Subgroup.zpowers b)
    (Subgroup.zpowers_le.mpr hbM) (Subgroup.zpowers_le.mpr hbV) hcomm_le
    (Subgroup.mem_zpowers b)

theorem RootHyp.isHMember_sup_conj_comm (h : RootHyp M V) (a b : G) :
    IsHMember (conjSubgroup a M) (conjSubgroup a V)
        (conjSubgroup a (Pc M V) ⊔ conjSubgroup b (Pc M V)) ↔
      IsHMember (conjSubgroup b M) (conjSubgroup b V)
        (conjSubgroup a (Pc M V) ⊔ conjSubgroup b (Pc M V)) := by
  let c := a⁻¹ * b
  have hX : conjSubgroup a (Pc M V) ⊔ conjSubgroup b (Pc M V) =
      conjSubgroup a (hOf M V c) := by
    rw [hOf, conjSubgroup_sup]
    congr 1
    rw [show b = a * c by rw [show c = a⁻¹ * b from rfl]; group]
    exact (CGT.Timmesfeld75.conjSubgroup_conjSubgroup a c (Pc M V)).symm
  have hOf_inv : hOf M V c⁻¹ = conjSubgroup c⁻¹ (hOf M V c) := by
    unfold hOf
    rw [conjSubgroup_sup, CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one, sup_comm]
  have h1 : IsHMember (conjSubgroup a M) (conjSubgroup a V)
      (conjSubgroup a (Pc M V) ⊔ conjSubgroup b (Pc M V)) ↔
      IsHMember M V (hOf M V c) := by
    rw [hX]
    exact isHMember_conjSubgroup_iff a
  have h2 : IsHMember (conjSubgroup b M) (conjSubgroup b V)
      (conjSubgroup a (Pc M V) ⊔ conjSubgroup b (Pc M V)) ↔
      IsHMember M V (hOf M V c) := by
    have hb : conjSubgroup b⁻¹ (conjSubgroup a (hOf M V c)) = hOf M V c⁻¹ := by
      rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
        show b⁻¹ * a = c⁻¹ by rw [show c = a⁻¹ * b from rfl]; group]
      exact hOf_inv.symm
    have h3 : conjSubgroup b (hOf M V c⁻¹) = conjSubgroup a (hOf M V c) := by
      rw [← hb, CGT.Timmesfeld75.conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    rw [hX, ← h3]
    refine (isHMember_conjSubgroup_iff (M := M) (V := V) (L := hOf M V c⁻¹) b).trans ?_
    have hA := h.isHMember_hOf_conj_iff (g := c⁻¹)
    have hB : IsHMember (conjSubgroup c⁻¹ M) (conjSubgroup c⁻¹ V)
        (conjSubgroup c⁻¹ (hOf M V c)) ↔ IsHMember M V (hOf M V c) :=
      isHMember_conjSubgroup_iff (M := M) (V := V) (L := hOf M V c) c⁻¹
    rw [← hOf_inv] at hB
    exact hA.symm.trans hB
  exact h1.trans h2.symm

theorem Sec5Hyp.inf_Pc_eq_bot (hS : Sec5Hyp M V) {U : Subgroup G} (hU : U ∈ sigmaSet M V) :
    U ⊓ Pc M V = ⊥ := by
  obtain ⟨g, rfl, hH⟩ := hU
  exact RootHyp.conjSubgroup_inf_Pc_eq_bot hS.toRootHyp (H := hOf M V g) rfl hH.2.2

theorem Sec5Hyp.Pc_inf_normalizer_eq_centralizer (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) :
    Pc M V ⊓ Subgroup.normalizer (U : Set G) = Pc M V ⊓ Subgroup.centralizer (U : Set G) := by
  have h := hS.toRootHyp
  refine le_antisymm ?_ (inf_le_inf le_rfl (Subgroup.centralizer_le_normalizer _))
  intro x hx
  obtain ⟨hxP, hxN⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨hxP, ?_⟩
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
  intro u hu
  have hxM : x ∈ M := h.toHyp.Pc_le_M hxP
  have huM : u ∈ M := (hS.le_M_of_mem_sigmaSet hU).1 hu
  have hxuU : ⁅x, u⁆ ∈ U := by
    have h1 : x * u * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hxN u).mp hu
    have h2 : u⁻¹ ∈ U := U.inv_mem hu
    have h3 : x * u * x⁻¹ * u⁻¹ ∈ U := U.mul_mem h1 h2
    simpa [commutatorElement_def] using h3
  have hxuP : ⁅x, u⁆ ∈ Pc M V := by
    have h1 : u * x * u⁻¹ ∈ Pc M V :=
      (Subgroup.mem_normalizer_iff.mp (h.toHyp.le_normalizer_Pc huM) x).mp hxP
    have h2 : x⁻¹ ∈ Pc M V := (Pc M V).inv_mem hxP
    have h3 : u * x * u⁻¹ * x⁻¹ ∈ Pc M V := (Pc M V).mul_mem h1 h2
    have h4 : ⁅x, u⁆ = ⁅u, x⁆⁻¹ := (commutatorElement_inv (g₁ := u) (g₂ := x)).symm
    rw [h4]
    exact (Pc M V).inv_mem (by simpa [commutatorElement_def] using h3)
  have hmem : ⁅x, u⁆ ∈ U ⊓ Pc M V := Subgroup.mem_inf.mpr ⟨hxuU, hxuP⟩
  rw [hS.inf_Pc_eq_bot hU] at hmem
  exact Subgroup.mem_bot.mp hmem

end CFSG.RankThree.GF2n.Tim81

end
