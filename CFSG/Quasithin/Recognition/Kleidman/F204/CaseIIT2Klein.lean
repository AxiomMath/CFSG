module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPath
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIBase
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT2Alg
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalT2

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem fpf_Qv (F : Frame L1 L2 S D X) {w γ x : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hw : vtype w = true) (hγ : γ ∈ nbrs w) (hx : x ∈ nbrs w) (hxγ : x ≠ γ) {g : G}
    (hg : g ∈ Qv γ) (hgx : g ∈ stab x) : g ∈ Qv w := by
  have hA := Amal.of_frame F
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  obtain ⟨h, hh1, hh0⟩ := exists_edge_conj_true hw hγ
  have hadj : (graph (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)).Adj
      (γ₁ _ _ _) (h⁻¹ • x) := by
    have := (smul_adj h⁻¹).mpr hx
    rwa [← hh1, inv_smul_smul] at this
  obtain ⟨p, hp1, hp0⟩ := exists_stab_smul_eq adj_γ₀_γ₁.symm hadj
  have hpP : (p : G) ∈ P2 L1 L2 S := by
    have := mem_stab_of_smul_eq hp1; rwa [stab_γ₁ h₂] at this
  have hxeq : x = (h * p) • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) := by
    rw [mul_smul, hp0, smul_inv_smul]
  have hQγ : Qv γ = conjSub (h : G) (Q1 L1 L2 S) := by
    rw [← hh0, Qv_smul]; unfold Qv; rw [stab_γ₀ h₁]
  have hQw : Qv w = conjSub (h : G) (Q2 L1 L2 S) := by
    rw [← hh1, Qv_smul]; unfold Qv; rw [stab_γ₁ h₂]
  have hqQ1 : (h : G)⁻¹ * g * h ∈ Q1 L1 L2 S := by
    rw [hQγ] at hg; exact mem_conjSub.mp hg
  have hpB : (p : G) ∉ bigB L1 L2 S := by
    intro hB
    apply hxγ
    have hfix : p • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) = γ₀ _ _ _ := by
      apply smul_eq_of_mem_stab
      rw [stab_γ₀ h₁]
      exact (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hB
    rw [hxeq, mul_smul, hfix, hh0]
  have hq2P : (h : G)⁻¹ * g * h ∈ P2 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)
    (Q1_le_B F hqQ1)
  have hconj : (p : G)⁻¹ * ((h : G)⁻¹ * g * h) * p ∈ bigB L1 L2 S := by
    have hs : g ∈ stab ((h * p) • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) := by
      rw [← hxeq]; exact hgx
    rw [mem_stab_smul_γ₀ h₁] at hs
    have e : (((h * p : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G))⁻¹ * g *
        ((h * p : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G) =
        (p : G)⁻¹ * ((h : G)⁻¹ * g * h) * p := by simp [mul_assoc]
    rw [e] at hs
    have hP2 : (p : G)⁻¹ * ((h : G)⁻¹ * g * h) * p ∈ P2 L1 L2 S :=
      (P2 L1 L2 S).mul_mem ((P2 L1 L2 S).mul_mem ((P2 L1 L2 S).inv_mem hpP) hq2P) hpP
    rw [← hA.inf_eq]
    exact ⟨hs, hP2⟩
  have hq2 := Q1_inf_conj_le_Q2 F hpP hpB hqQ1 hconj
  rw [hQw]
  have := mem_conjSub_of_mem' (h := (h : G)) hq2
  have e : (h : G) * ((h : G)⁻¹ * g * h) * (h : G)⁻¹ = g := by group
  rwa [e] at this

theorem exists_nbr_ne_two (F : Frame L1 L2 S D X) {w x p : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (_hx : x ∈ nbrs w) (_hp : p ∈ nbrs w) : ∃ μ ∈ nbrs w, μ ≠ x ∧ μ ≠ p := by
  have hA := Amal.of_frame F
  by_contra hcon
  push Not at hcon
  have hsub : nbrs w ⊆ {x, p} := by
    intro μ hμ
    by_cases h1 : μ = x
    · exact Or.inl h1
    · exact Or.inr (hcon μ hμ h1)
  have h1 : (nbrs w).ncard ≤ ({x, p} : Set (Geo (P1 L1 L2 S) (P2 L1 L2 S))).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({x, p} : Set (Geo (P1 L1 L2 S) (P2 L1 L2 S))).ncard ≤ 2 := by
    have := Set.ncard_insert_le x ({p} : Set (Geo (P1 L1 L2 S) (P2 L1 L2 S)))
    rw [Set.ncard_singleton] at this
    exact this
  have h3 : Nat.card (nbrs w) = 5 := hA.card_nbrs w
  rw [Nat.card_coe_set_eq] at h3
  omega

theorem exists_stab_smul_nbr (F : Frame L1 L2 S D X) {w x p : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hw : vtype w = true) (hx : x ∈ nbrs w) (hp : p ∈ nbrs w) :
    ∃ q : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S), (q : G) ∈ stab w ∧ q • x = p := by
  have hA := Amal.of_frame F
  obtain ⟨μ, hμ, hμx, hμp⟩ := exists_nbr_ne_two F hx hp
  obtain ⟨q, hq, hqx⟩ := exists_Qv_smul_nbr F hw hμ hx hp (Ne.symm hμx) (Ne.symm hμp)
  refine ⟨q, ?_, hqx⟩
  exact hA.Qv_le_stab_of_mem_nbrs (show w ∈ nbrs μ from
    (show (graph _ _ _).Adj w μ from hμ).symm) hq

theorem klein_edge_gen (F : Frame L1 L2 S D X) {w x : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hw : vtype w = true) (hx : x ∈ nbrs w) :
    ∃ D' : Subgroup G, (∀ d ∈ D', d ^ 3 = 1) ∧ stab x ⊓ stab w = (Qv w ⊔ Qv x) ⊔ D' := by
  have hA := Amal.of_frame F
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  have hQ0 : Qv (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q1 L1 L2 S := by
    unfold Qv; rw [stab_γ₀ h₁]
  have hQ1 : Qv (γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q2 L1 L2 S := by
    unfold Qv; rw [stab_γ₁ h₂]
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge (show (graph _ _ _).Adj w x from hx)
  · exfalso
    have := vtype_smul g (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S))
    rw [hg0, hw, vtype_γ₀] at this
    exact Bool.noConfusion this
  · refine ⟨conjSub (g : G) D, ?_, ?_⟩
    · intro d hd
      have hd' : (g : G)⁻¹ * d * g ∈ D := mem_conjSub.mp hd
      have h3 := pow_three_of_mem_D F hd'
      have hcp := conj_pow (a := (g : G)⁻¹) (b := d) (i := 3)
      simp only [inv_inv] at hcp
      have : (g : G)⁻¹ * d ^ 3 * g = 1 := by rw [← hcp]; exact h3
      have e : d ^ 3 = (g : G) * ((g : G)⁻¹ * d ^ 3 * g) * (g : G)⁻¹ := by group
      rw [e, this]; group
    · have hsx : stab x = conjSub (g : G) (P1 L1 L2 S) := by
        rw [← hg0, stab_smul, stab_γ₀ h₁]
      have hsw : stab w = conjSub (g : G) (P2 L1 L2 S) := by
        rw [← hg1, stab_smul, stab_γ₁ h₂]
      have hqx : Qv x = conjSub (g : G) (Q1 L1 L2 S) := by rw [← hg0, Qv_smul, hQ0]
      have hqw : Qv w = conjSub (g : G) (Q2 L1 L2 S) := by rw [← hg1, Qv_smul, hQ1]
      have hS : conjSub (g : G) S = conjSub (g : G) (Q2 L1 L2 S) ⊔ conjSub (g : G) (Q1 L1 L2 S) := by
        rw [← conjSub_sup, show Q2 L1 L2 S ⊔ Q1 L1 L2 S = S from by rw [sup_comm]; exact Q1_sup_Q2 F]
      rw [hsx, hsw, ← conjSub_inf, hA.inf_eq, F.bigB_eq, conjSub_sup, hS, hqw, hqx]

theorem edge_trivial_mod (F : Frame L1 L2 S D X)
    (hZ : ∀ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype μ = true → Zv μ ≤ centerOf (stab μ))
    {w x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hw : vtype w = true) (hx : x ∈ nbrs w) {g : G}
    (hg : g ∈ stab x ⊓ stab w) {v : G} (hv : v ∈ Zv x) :
    g * v * g⁻¹ * v⁻¹ ∈ ⁅Vn w, Qv w⁆ := by
  have hA := Amal.of_frame F
  have hxf : vtype x = false := by
    have := vtype_ne_of_adj (show (graph _ _ _).Adj w x from hx)
    cases h : vtype x
    · rfl
    · exact absurd (hw.trans h.symm) this
  have hwx : w ∈ nbrs x := (show (graph _ _ _).Adj w x from hx).symm
  have hW0n : ∀ k ∈ stab w, ∀ y ∈ ⁅Vn w, Qv w⁆, k * y * k⁻¹ ∈ ⁅Vn w, Qv w⁆ := by
    intro k hk y hy
    refine conj_mem_commutator (fun a ha => ?_) (fun b hb => ?_) hy
    · exact (Subgroup.mem_normalizer_iff.mp (Amal.stab_le_normalizer_Vn' w hk) a).mp ha
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab w) hk) b).mp hb
  have hZn : ∀ k ∈ stab x, ∀ u ∈ Zv x, k * u * k⁻¹ ∈ Zv x := fun k hk u hu =>
    (Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv x hk) u).mp hu
  let N0 : Subgroup G :=
    { carrier := {k | k ∈ stab x ⊓ stab w ∧ ∀ u ∈ Zv x, k * u * k⁻¹ * u⁻¹ ∈ ⁅Vn w, Qv w⁆}
      mul_mem' := by
        rintro k1 k2 ⟨hk1, h1⟩ ⟨hk2, h2⟩
        refine ⟨Subgroup.mul_mem _ hk1 hk2, fun u hu => ?_⟩
        have e : k1 * k2 * u * (k1 * k2)⁻¹ * u⁻¹ =
            (k1 * (k2 * u * k2⁻¹ * u⁻¹) * k1⁻¹) * (k1 * u * k1⁻¹ * u⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (hW0n k1 (Subgroup.mem_inf.mp hk1).2 _ (h2 u hu)) (h1 u hu)
      one_mem' := ⟨Subgroup.one_mem _, fun u _ => by simp⟩
      inv_mem' := by
        rintro k ⟨hk, h1⟩
        refine ⟨Subgroup.inv_mem _ hk, fun u hu => ?_⟩
        have hu' : k⁻¹ * u * k ∈ Zv x := by
          have := hZn k⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hk).1) u hu
          simpa using this
        have h2 := Subgroup.inv_mem _ (h1 _ hu')
        have e : k⁻¹ * u * k⁻¹⁻¹ * u⁻¹ = (k * (k⁻¹ * u * k) * k⁻¹ * (k⁻¹ * u * k)⁻¹)⁻¹ := by
          group
        rw [e]; exact h2 }
  have hmemN0 : ∀ k, k ∈ N0 ↔ k ∈ stab x ⊓ stab w ∧
      ∀ u ∈ Zv x, k * u * k⁻¹ * u⁻¹ ∈ ⁅Vn w, Qv w⁆ := fun k => Iff.rfl
  obtain ⟨D', hD'3, hE⟩ := klein_edge_gen F hw hx
  have hQw : Qv w ≤ N0 := by
    intro k hk
    refine (hmemN0 k).mpr ⟨Subgroup.mem_inf.mpr ⟨hA.Qv_le_stab_of_mem_nbrs hx hk,
      pCoreOf_le 2 _ hk⟩, fun u hu => ?_⟩
    have : ⁅k, u⁆ ∈ ⁅Qv w, Vn w⁆ :=
      Subgroup.commutator_mem_commutator hk (hA.Zv_le_Vn hx hu)
    rw [Subgroup.commutator_comm] at this
    simpa [commutatorElement_def] using this
  have hQx : Qv x ≤ N0 := by
    intro k hk
    refine (hmemN0 k).mpr ⟨Subgroup.mem_inf.mpr ⟨pCoreOf_le 2 _ hk,
      hA.Qv_le_stab_of_mem_nbrs hwx hk⟩, fun u hu => ?_⟩
    have hc : u * k = k * u :=
      (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv x hu).2 k hk).symm
    have e : k * u * k⁻¹ * u⁻¹ = 1 := by rw [← hc]; group
    rw [e]; exact Subgroup.one_mem _
  have hD' : D' ≤ N0 := by
    intro d hd
    have hdE : d ∈ stab x ⊓ stab w := by rw [hE]; exact Subgroup.mem_sup_right hd
    refine (hmemN0 d).mpr ⟨hdE, fun u hu => ?_⟩
    have hc := three_centralizes_Zv F hxf (fun μ hμ => hZ μ (by
      have := vtype_ne_of_adj (show (graph _ _ _).Adj x μ from hμ)
      cases h : vtype μ
      · exact absurd (hxf.trans h.symm) this
      · rfl)) (Subgroup.mem_inf.mp hdE).1 (hD'3 d hd) u hu
    have e : d * u * d⁻¹ * u⁻¹ = 1 := by rw [hc]; group
    rw [e]; exact Subgroup.one_mem _
  have hg' : g ∈ (Qv w ⊔ Qv x) ⊔ D' := by rw [← hE]; exact hg
  exact ((hmemN0 g).mp ((sup_le (sup_le hQw hQx) hD') hg')).2 v hv

theorem four_points (F : Frame L1 L2 S D X) {w γ x : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hw : vtype w = true) (hγ : γ ∈ nbrs w) (hx : x ∈ nbrs w) (hxγ : x ≠ γ) {a b : G}
    (ha : a ∈ Qv γ) (hb : b ∈ Qv γ) (ha1 : a ∉ Qv w) (hb1 : b ∉ Qv w) (hba : b * a ∉ Qv w)
    (hbb : b * b ∈ Qv w) :
    ∃ A B : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S), (A : G) = a ∧ (B : G) = b ∧
      A • x ≠ x ∧ B • x ≠ x ∧ (B * A) • x ≠ x ∧ A • x ≠ B • x ∧ A • x ≠ (B * A) • x ∧
      B • x ≠ (B * A) • x ∧ A • x ≠ γ ∧ B • x ≠ γ ∧ (B * A) • x ≠ γ ∧
      A • x ∈ nbrs w ∧ B • x ∈ nbrs w ∧ (B * A) • x ∈ nbrs w := by
  have hA := Amal.of_frame F
  have hwγ : w ∈ nbrs γ := (show (graph _ _ _).Adj w γ from hγ).symm
  have haw : a ∈ stab w := hA.Qv_le_stab_of_mem_nbrs hwγ ha
  have hbw : b ∈ stab w := hA.Qv_le_stab_of_mem_nbrs hwγ hb
  obtain ⟨hGa, hfa⟩ := mem_stab.mp haw
  obtain ⟨hGb, hfb⟩ := mem_stab.mp hbw
  set A : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨a, hGa⟩ with hAdef
  set B : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨b, hGb⟩ with hBdef
  have hmemA : ∀ p ∈ nbrs w, A • p ∈ nbrs w := fun p hp => by
    have := (smul_adj A).mpr (show (graph _ _ _).Adj w p from hp)
    rwa [hfa] at this
  have hmemB : ∀ p ∈ nbrs w, B • p ∈ nbrs w := fun p hp => by
    have := (smul_adj B).mpr (show (graph _ _ _).Adj w p from hp)
    rwa [hfb] at this
  have haγ : a ∈ stab γ := pCoreOf_le 2 _ ha
  have hbγ : b ∈ stab γ := pCoreOf_le 2 _ hb
  have hAγ : A • γ = γ := smul_eq_of_mem_stab (g := A) haγ
  have hBγ : B • γ = γ := smul_eq_of_mem_stab (g := B) hbγ
  have hAx : A • x ∈ nbrs w := hmemA x hx
  have hBx : B • x ∈ nbrs w := hmemB x hx
  have hAxγ : A • x ≠ γ := fun h => hxγ (by
    have h1 : x = A⁻¹ • γ := by rw [← h, inv_smul_smul]
    rw [h1, inv_smul_eq_iff]; exact hAγ.symm)
  have hBxγ : B • x ≠ γ := fun h => hxγ (by
    have h1 : x = B⁻¹ • γ := by rw [← h, inv_smul_smul]
    rw [h1, inv_smul_eq_iff]; exact hBγ.symm)
  have hmBA : (B * A) • x = B • (A • x) := mul_smul B A x
  have hBAx : (B * A) • x ∈ nbrs w := by rw [hmBA]; exact hmemB _ hAx
  have hbaγ : b * a ∈ Qv γ := (Qv γ).mul_mem hb ha
  have hAxe : A • x ≠ x := fun h =>
    ha1 (fpf_Qv F hw hγ hx hxγ ha (mem_stab_of_smul_eq h))
  have hBxe : B • x ≠ x := fun h =>
    hb1 (fpf_Qv F hw hγ hx hxγ hb (mem_stab_of_smul_eq h))
  have hBAxe : (B * A) • x ≠ x := fun h =>
    hba (fpf_Qv F hw hγ hx hxγ hbaγ (by simpa using mem_stab_of_smul_eq h))
  refine ⟨A, B, rfl, rfl, hAxe, hBxe, hBAxe, ?_, ?_, ?_, hAxγ, hBxγ, ?_, hAx, hBx, hBAx⟩
  · intro h
    have h1 : (B⁻¹ * A) • x = x := by
      rw [mul_smul, h, inv_smul_smul]
    have hbaQ : b⁻¹ * a ∈ Qv γ := (Qv γ).mul_mem ((Qv γ).inv_mem hb) ha
    have hQ := fpf_Qv F hw hγ hx hxγ hbaQ (by simpa using mem_stab_of_smul_eq h1)
    apply hba
    have e : b * a = (b * b) * (b⁻¹ * a) := by group
    rw [e]; exact (Qv w).mul_mem hbb hQ
  · intro h
    rw [hmBA] at h
    have hneq : A • x ≠ γ := hAxγ
    exact hb1 (fpf_Qv F hw hγ hAx hAxγ hb (mem_stab_of_smul_eq (g := B) h.symm))
  · intro h
    rw [hmBA] at h
    exact hAxe (smul_left_cancel B h).symm
  · intro h
    have := congrArg (fun y => (B * A)⁻¹ • y) h
    simp only [hmBA] at this
    have hB2 : (B * A) • x = γ := h
    apply hxγ
    have h3 : (B * A) • γ = γ := by
      rw [mul_smul, hAγ, hBγ]
    have := congrArg (fun y => (B * A)⁻¹ • y) (hB2.trans h3.symm)
    simpa [inv_smul_smul] using this

section Key

variable (F : Frame L1 L2 S D X) (hb3 : 3 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S))
  (hZ : ∀ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype μ = true → Zv μ ≤ centerOf (stab μ))
include F hb3 hZ

theorem klein_key {w γ x : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hw : vtype w = true) (hγ : γ ∈ nbrs w) (hx : x ∈ nbrs w) (_hxγ : x ≠ γ)
    {a b : G} (ha : a ∈ Qv γ) (hb : b ∈ Qv γ) (ha1 : a ∉ Qv w) (hb1 : b ∉ Qv w)
    (hba : b * a ∉ Qv w) (hrel : ∀ v ∈ Vn w, ⁅⁅v, a⁆, b⁆ = 1) :
    ∀ p ∈ nbrs w, Zv p ≤ Zv x ⊔ ⁅Vn w, Qv w⁆ := by
  classical
  have hA := Amal.of_frame F
  have hbb : b * b ∈ Qv w := sq_mem_Qv_of_mem_nbrs F hw hγ hb
  have hMab := hA.isElemAbelian_Vn hb3 w
  have hcomm : ∀ u ∈ Vn w, ∀ v ∈ Vn w, u * v = v * u := fun u hu v hv =>
    isElemAbelian_comm hMab hu hv
  have hsq : ∀ u ∈ Vn w, u * u = 1 := fun u hu => by
    have := isElemAbelian_pow_eq_one hMab hu; simpa [sq] using this
  have hMn : ∀ g ∈ stab w, ∀ u ∈ Vn w, g * u * g⁻¹ ∈ Vn w := fun g hg u hu =>
    (Subgroup.mem_normalizer_iff.mp (Amal.stab_le_normalizer_Vn' w hg) u).mp hu
  have hQn : ∀ g ∈ stab w, ∀ u ∈ Qv w, g * u * g⁻¹ ∈ Qv w := fun g hg u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab w) hg) u).mp hu
  have hQs : Qv w ≤ stab w := pCoreOf_le 2 _
  have hW0n : ∀ k ∈ stab w, ∀ y ∈ ⁅Vn w, Qv w⁆, k * y * k⁻¹ ∈ ⁅Vn w, Qv w⁆ := fun k hk y hy =>
    conj_mem_commutator (fun u hu => hMn k hk u hu) (fun u hu => hQn k hk u hu) hy
  have hW0M : ⁅Vn w, Qv w⁆ ≤ Vn w := by
    rw [Subgroup.commutator_le]
    intro u hu q hq
    have : u * (q * u⁻¹ * q⁻¹) ∈ Vn w :=
      (Vn w).mul_mem hu (hMn q (hQs hq) u⁻¹ ((Vn w).inv_mem hu))
    simpa [commutatorElement_def, mul_assoc] using this
  let instCG : CommGroup ↥(Vn w) := { (inferInstance : Group ↥(Vn w)) with
    mul_comm := fun u v => Subtype.ext (hcomm u u.2 v v.2) }
  set N' : Subgroup ↥(Vn w) := (⁅Vn w, Qv w⁆).subgroupOf (Vn w) with hN'
  have hNn : N'.Normal := Subgroup.normal_of_isMulCommutative N'
  have hAq : ∀ q : ↥(Vn w) ⧸ N', q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H u =>
      have : u * u = 1 := Subtype.ext (hsq u u.2)
      rw [← QuotientGroup.mk_mul, this, QuotientGroup.mk_one]
  have : Finite ↥(nbrs w) := inferInstance
  have : Fintype ↥(nbrs w) := Fintype.ofFinite _
  have hΔ : Fintype.card ↥(nbrs w) = 5 := by
    rw [← Nat.card_eq_fintype_card]; exact hA.card_nbrs w
  have hfwd : ∀ v ∈ Zv x, ∀ g g' : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S), (g : G) ∈ stab w →
      (g' : G) ∈ stab w → g • x = g' • x →
      ((g : G) * v * (g : G)⁻¹)⁻¹ * ((g' : G) * v * (g' : G)⁻¹) ∈ ⁅Vn w, Qv w⁆ := by
    intro v hv g g' hg hg' hgg
    have hvM : v ∈ Vn w := hA.Zv_le_Vn hx hv
    set h : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := g'⁻¹ * g with hh
    have hhx : h • x = x := by rw [hh, mul_smul, hgg, inv_smul_smul]
    have hhst : (h : G) ∈ stab x ⊓ stab w := by
      refine Subgroup.mem_inf.mpr ⟨mem_stab_of_smul_eq hhx, ?_⟩
      have : (h : G) = (g' : G)⁻¹ * (g : G) := by simp [hh]
      rw [this]
      exact (stab w).mul_mem ((stab w).inv_mem hg') hg
    have e1 := edge_trivial_mod F hZ hw hx hhst hv
    have hhM : (h : G) * v * (h : G)⁻¹ ∈ Vn w := by
      refine hMn _ ?_ v hvM
      exact (Subgroup.mem_inf.mp hhst).2
    have hcv : v * ((h : G) * v * (h : G)⁻¹) = ((h : G) * v * (h : G)⁻¹) * v :=
      hcomm v hvM _ hhM
    have e2 : ((h : G) * v⁻¹ * (h : G)⁻¹) * v = ((h : G) * v * (h : G)⁻¹ * v⁻¹)⁻¹ := by
      have e3 : ((h : G) * v⁻¹ * (h : G)⁻¹) * v = ((h : G) * v * (h : G)⁻¹)⁻¹ * v := by group
      rw [e3]
      have e4 : ((h : G) * v * (h : G)⁻¹)⁻¹ * v = v * ((h : G) * v * (h : G)⁻¹)⁻¹ :=
        (Commute.inv_right (show Commute v ((h : G) * v * (h : G)⁻¹) from hcv)).eq.symm
      rw [e4]; group
    have e5 : ((g : G) * v * (g : G)⁻¹)⁻¹ * ((g' : G) * v * (g' : G)⁻¹) =
        (g' : G) * (((h : G) * v⁻¹ * (h : G)⁻¹) * v) * (g' : G)⁻¹ := by
      have hg2 : (g : G) = (g' : G) * (h : G) := by simp [hh]
      rw [hg2]; group
    rw [e5, e2]
    exact hW0n _ hg' _ (Subgroup.inv_mem _ e1)
  have hsel : ∀ q : ↥(nbrs w), ∃ g : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S), (g : G) ∈ stab w ∧ g • x = q.1 :=
    fun q => exists_stab_smul_nbr F hw hx q.2
  choose gs hgs1 hgs2 using hsel
  have hmain : ∀ v ∈ Zv x, ∀ q : ↥(nbrs w),
      v⁻¹ * ((gs q : G) * v * (gs q : G)⁻¹) ∈ ⁅Vn w, Qv w⁆ := by
    intro v hv
    have hvM : v ∈ Vn w := hA.Zv_le_Vn hx hv
    let f : ↥(nbrs w) → ↥(Vn w) ⧸ N' := fun q =>
      QuotientGroup.mk ⟨(gs q : G) * v * (gs q : G)⁻¹, hMn _ (hgs1 q) v hvM⟩
    have hfp : ∀ (g : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) (hg : (g : G) ∈ stab w) (q : ↥(nbrs w)),
        g • x = q.1 →
        (QuotientGroup.mk (⟨(g : G) * v * (g : G)⁻¹, hMn _ hg v hvM⟩ : ↥(Vn w)) :
          ↥(Vn w) ⧸ N') = f q := by
      intro g hg q hgq
      show _ = QuotientGroup.mk _
      rw [QuotientGroup.eq, hN', Subgroup.mem_subgroupOf]
      exact hfwd v hv g (gs q) hg (hgs1 q) (hgq.trans (hgs2 q).symm)
    have hone : (1 : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • x = x := one_smul _ _
    have hfx : f ⟨x, hx⟩ = QuotientGroup.mk ⟨v, hvM⟩ := by
      have := hfp 1 (by simp) ⟨x, hx⟩ hone
      rw [← this]
      congr 1
      exact Subtype.ext (by simp)
    have hrelf : ∀ γ' : ↥(nbrs w), γ'.1 ≠ x →
        ∏ r ∈ Finset.univ.erase γ', f r = 1 := by
      intro γ' hγ'x
      obtain ⟨k, hk, hkγ⟩ := exists_stab_smul_nbr F hw hγ γ'.2
      obtain ⟨a', ha'⟩ : ∃ a' : G, a' = (k : G) * a * (k : G)⁻¹ := ⟨_, rfl⟩
      obtain ⟨b', hb'⟩ : ∃ b' : G, b' = (k : G) * b * (k : G)⁻¹ := ⟨_, rfl⟩
      have hQγ' : Qv γ'.1 = conjSub (k : G) (Qv γ) := by rw [← hkγ, Qv_smul]
      have ha'Q : a' ∈ Qv γ'.1 := by rw [hQγ', ha']; exact mem_conjSub_of_mem' ha
      have hb'Q : b' ∈ Qv γ'.1 := by rw [hQγ', hb']; exact mem_conjSub_of_mem' hb
      have hnot : ∀ y : G, (k : G) * y * (k : G)⁻¹ ∈ Qv w → y ∈ Qv w := by
        intro y hy
        have := hQn ((k : G)⁻¹) ((stab w).inv_mem hk) _ hy
        have e : (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) * (k : G)⁻¹⁻¹ = y := by group
        rwa [e] at this
      have ha1' : a' ∉ Qv w := fun h => ha1 (hnot a (by rw [← ha']; exact h))
      have hb1' : b' ∉ Qv w := fun h => hb1 (hnot b (by rw [← hb']; exact h))
      have hba' : b' * a' ∉ Qv w := fun h => hba (hnot (b * a) (by
        have e : (k : G) * (b * a) * (k : G)⁻¹ = b' * a' := by rw [ha', hb']; group
        rw [e]; exact h))
      have hbb' : b' * b' ∈ Qv w := by
        have e : b' * b' = (k : G) * (b * b) * (k : G)⁻¹ := by rw [hb']; group
        rw [e]; exact hQn _ hk _ hbb
      have hwγ' : w ∈ nbrs γ'.1 := (show (graph _ _ _).Adj w γ'.1 from γ'.2).symm
      have ha'w : a' ∈ stab w := hA.Qv_le_stab_of_mem_nbrs hwγ' ha'Q
      have hb'w : b' ∈ stab w := hA.Qv_le_stab_of_mem_nbrs hwγ' hb'Q
      have hrel' : ∀ v' ∈ Vn w, ⁅⁅v', a'⁆, b'⁆ = 1 := by
        intro v' hv'
        have hv'' : (k : G)⁻¹ * v' * (k : G) ∈ Vn w := by
          have := hMn ((k : G)⁻¹) ((stab w).inv_mem hk) v' hv'
          simpa using this
        have h0 := hrel _ hv''
        have e : ⁅⁅v', a'⁆, b'⁆ =
            (k : G) * ⁅⁅(k : G)⁻¹ * v' * (k : G), a⁆, b⁆ * (k : G)⁻¹ := by
          rw [ha', hb']; simp only [commutatorElement_def]; group
        rw [e, h0]; group
      obtain ⟨A, B, hAa, hBb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
        four_points F hw γ'.2 hx hγ'x.symm ha'Q hb'Q ha1' hb1' hba' hbb'
      have hAs : (A : G) ∈ stab w := by rw [hAa]; exact ha'w
      have hBs : (B : G) ∈ stab w := by rw [hBb]; exact hb'w
      have hba'w : b' * a' ∈ stab w := (stab w).mul_mem hb'w ha'w
      have hBAs : ((B * A : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G) ∈ stab w := by
        rw [Subgroup.coe_mul, hAa, hBb]; exact hba'w
      let p0 : ↥(nbrs w) := ⟨x, hx⟩
      let p1 : ↥(nbrs w) := ⟨A • x, h10⟩
      let p2 : ↥(nbrs w) := ⟨B • x, h11⟩
      let p3 : ↥(nbrs w) := ⟨(B * A) • x, h12⟩
      have hf1 : f p1 = QuotientGroup.mk ⟨a' * v * a'⁻¹, hMn _ ha'w v hvM⟩ := by
        have := hfp A hAs p1 rfl
        rw [← this]; exact congrArg _ (Subtype.ext (by simp [hAa]))
      have hf2 : f p2 = QuotientGroup.mk ⟨b' * v * b'⁻¹, hMn _ hb'w v hvM⟩ := by
        have := hfp B hBs p2 rfl
        rw [← this]; exact congrArg _ (Subtype.ext (by simp [hBb]))
      have hf3 : f p3 = QuotientGroup.mk
          ⟨(b' * a') * v * (b' * a')⁻¹, hMn _ hba'w v hvM⟩ := by
        have := hfp (B * A) hBAs p3 rfl
        rw [← this]; exact congrArg _ (Subtype.ext (by simp [hAa, hBb]))
      have ht1M : a' * v * a'⁻¹ ∈ Vn w := hMn _ ha'w v hvM
      have ht2M : b' * v * b'⁻¹ ∈ Vn w := hMn _ hb'w v hvM
      have ht3M : (b' * a') * v * (b' * a')⁻¹ ∈ Vn w := hMn _ hba'w v hvM
      have hu := hrel' v hvM
      have hcm : Commute ⁅v, a'⁆ b' := commutatorElement_eq_one_iff_commute.mp hu
      have e6 : (b' * v * b'⁻¹) * ((b' * a') * v * (b' * a')⁻¹)⁻¹ =
          v * (a' * v * a'⁻¹)⁻¹ := by
        have h1 : b' * ⁅v, a'⁆ * b'⁻¹ = ⁅v, a'⁆ := by
          have hh := hcm.eq
          calc b' * ⁅v, a'⁆ * b'⁻¹ = (b' * ⁅v, a'⁆) * b'⁻¹ := rfl
            _ = (⁅v, a'⁆ * b') * b'⁻¹ := by rw [hh]
            _ = ⁅v, a'⁆ := by group
        have e7 : b' * ⁅v, a'⁆ * b'⁻¹ =
            (b' * v * b'⁻¹) * ((b' * a') * v * (b' * a')⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
        have e8 : ⁅v, a'⁆ = v * (a' * v * a'⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [← e7, h1, e8]
      have hi1 : (a' * v * a'⁻¹)⁻¹ = a' * v * a'⁻¹ := inv_eq_of_mul_eq_one_right (hsq _ ht1M)
      have hi3 : ((b' * a') * v * (b' * a')⁻¹)⁻¹ = (b' * a') * v * (b' * a')⁻¹ :=
        inv_eq_of_mul_eq_one_right (hsq _ ht3M)
      rw [hi1, hi3] at e6
      have hprod : v * (a' * v * a'⁻¹) * (b' * v * b'⁻¹) * ((b' * a') * v * (b' * a')⁻¹) = 1 := by
        have e9 : v * (a' * v * a'⁻¹) * (b' * v * b'⁻¹) * ((b' * a') * v * (b' * a')⁻¹) =
            (v * (a' * v * a'⁻¹)) * ((b' * v * b'⁻¹) * ((b' * a') * v * (b' * a')⁻¹)) := by
          group
        rw [e9, e6]; exact hsq _ ((Vn w).mul_mem hvM ht1M)
      have hmk : (QuotientGroup.mk ⟨v, hvM⟩ : ↥(Vn w) ⧸ N') *
          QuotientGroup.mk ⟨a' * v * a'⁻¹, ht1M⟩ * QuotientGroup.mk ⟨b' * v * b'⁻¹, ht2M⟩ *
          QuotientGroup.mk ⟨(b' * a') * v * (b' * a')⁻¹, ht3M⟩ = 1 := by
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        have : (⟨v, hvM⟩ * ⟨a' * v * a'⁻¹, ht1M⟩ * ⟨b' * v * b'⁻¹, ht2M⟩ *
            ⟨(b' * a') * v * (b' * a')⁻¹, ht3M⟩ : ↥(Vn w)) = 1 := Subtype.ext hprod
        rw [this, QuotientGroup.mk_one]
      have hp := prod_erase_four hΔ f (γ := γ') (p0 := p0) (p1 := p1) (p2 := p2) (p3 := p3)
        (fun h => h1 (congrArg Subtype.val h).symm) (fun h => h2 (congrArg Subtype.val h).symm)
        (fun h => h3 (congrArg Subtype.val h).symm) (fun h => h4 (congrArg Subtype.val h))
        (fun h => h5 (congrArg Subtype.val h)) (fun h => h6 (congrArg Subtype.val h))
        (fun h => hγ'x (congrArg Subtype.val h).symm) (fun h => h7 (congrArg Subtype.val h))
        (fun h => h8 (congrArg Subtype.val h)) (fun h => h9 (congrArg Subtype.val h))
      rw [hp, hfx, hf1, hf2, hf3]
      exact hmk
    have hconst := const_of_erase_prod hAq hΔ f ⟨x, hx⟩
      (fun γ' hne => hrelf γ' (fun h => hne (Subtype.ext h)))
    intro q
    have hq := hconst q
    rw [hfx] at hq
    have hq' : (QuotientGroup.mk ⟨(gs q : G) * v * (gs q : G)⁻¹, hMn _ (hgs1 q) v hvM⟩ :
        ↥(Vn w) ⧸ N') = QuotientGroup.mk ⟨v, hvM⟩ := hq
    rw [QuotientGroup.eq, hN', Subgroup.mem_subgroupOf] at hq'
    have := Subgroup.inv_mem _ hq'
    simpa [mul_inv_rev] using this
  intro p hp y hy
  have hZp : Zv p = conjSub ((gs ⟨p, hp⟩ : G)) (Zv x) := by
    have h : gs ⟨p, hp⟩ • x = p := hgs2 ⟨p, hp⟩
    calc Zv p = Zv (gs ⟨p, hp⟩ • x) := by rw [h]
      _ = conjSub ((gs ⟨p, hp⟩ : G)) (Zv x) := Zv_smul _ _
  rw [hZp, mem_conjSub] at hy
  have h1 := hmain ((gs ⟨p, hp⟩ : G)⁻¹ * y * (gs ⟨p, hp⟩ : G)) hy ⟨p, hp⟩
  have e : y = ((gs ⟨p, hp⟩ : G)⁻¹ * y * (gs ⟨p, hp⟩ : G)) *
      (((gs ⟨p, hp⟩ : G)⁻¹ * y * (gs ⟨p, hp⟩ : G))⁻¹ * ((gs ⟨p, hp⟩ : G) *
        ((gs ⟨p, hp⟩ : G)⁻¹ * y * (gs ⟨p, hp⟩ : G)) * (gs ⟨p, hp⟩ : G)⁻¹)) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right h1)

theorem klein_false {w γ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hw : vtype w = true) (hγ : γ ∈ nbrs w)
    {a b : G} (ha : a ∈ Qv γ) (hb : b ∈ Qv γ) (ha1 : a ∉ Qv w) (hb1 : b ∉ Qv w)
    (hba : b * a ∉ Qv w) (hrel : ∀ v ∈ Vn w, ⁅⁅v, a⁆, b⁆ = 1) : False := by
  have hA := Amal.of_frame F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, hxγ, -⟩ := exists_nbr_ne_two F hγ hγ
  have hxw : (graph _ _ _).Adj w x := hx
  have key := klein_key F hb3 hZ hw hγ hx hxγ ha hb ha1 hb1 hba hrel
  have hMQ : Vn w ≤ Qv w := iSup₂_le fun μ hμ =>
    Zv_le_Qv_of_mem_nbrs F ((show (graph _ _ _).Adj w μ from hμ).symm)
  have hHQ : Qv w ≤ Subgroup.normalizer (Zv x : Set G) := fun g hg =>
    hA.stab_le_normalizer_Zv x (hA.Qv_le_stab_of_mem_nbrs hx hg)
  have hle : Vn w ≤ Zv x ⊔ ⁅Vn w, Qv w⁆ := iSup₂_le fun p hp => key p hp
  have hMx : Vn w ≤ Zv x :=
    le_of_le_sup_commutator (pCoreOf_isPGroup 2 (stab w) : IsPGroup 2 (Qv w)) hMQ hHQ hle
  have hall : ∀ p ∈ nbrs w, Zv p = Zv x := by
    intro p hp
    obtain ⟨g, -, hgx⟩ := exists_stab_smul_nbr F hw hx hp
    have h1 : Zv p ≤ Zv x := (hA.Zv_le_Vn hp).trans hMx
    have h2 : Zv p = conjSub (g : G) (Zv x) := by
      calc Zv p = Zv (g • x) := by rw [hgx]
        _ = conjSub (g : G) (Zv x) := Zv_smul _ _
    exact Subgroup.eq_of_le_of_card_ge h1 (by rw [h2]; exact (card_conjSub (g : G) (Zv x)).ge)
  have hnp : stab w ≤ Subgroup.normalizer (Zv x : Set G) := by
    intro k hk
    obtain ⟨hG0, hfix⟩ := mem_stab.mp hk
    have hku : (⟨k, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • x ∈ nbrs w := by
      have := (smul_adj (⟨k, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S))).mpr hxw
      rwa [hfix] at this
    have e := Zv_smul (⟨k, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) x
    rw [hall _ hku] at e
    exact mem_normalizer_of_conjSub_eq e.symm
  have hwx : w ∈ nbrs x := hxw.symm
  have hU : Zv x ≤ stab w ⊓ stab x :=
    le_inf ((Zv_le_Qv_of_mem_nbrs F hwx).trans (pCoreOf_le 2 _))
      ((hA.Zv_le_Qv x).trans (pCoreOf_le 2 _))
  exact hA.Zv_ne_bot x (hA.eq_bot_of_normalizes_both hxw hU hnp (hA.stab_le_normalizer_Zv x))

end Key

end CFSG.Quasithin.Kleidman.F204
