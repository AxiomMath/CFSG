module

public import CFSG.RankThree.GF2n.Stroth80.Sec53dIndec
public import CFSG.RankThree.GF2n.Stroth80.Sec53FromFix
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.GF2n.Stroth80.Sec123Order
public import CFSG.RankThree.GF2n.Stroth80.Sec53cVone

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.comm_A2_LB_le_Z (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    {A₁ A₂ : Subgroup G} (hZA₂ : Z ≤ A₂)
    (hA₂V₁ : A₂ ≤ Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))
    (hA₁A₂ : A₁ ⊓ A₂ = Z)
    (hVA₁ : Vt M (LB M Q B) B Z t ≤ A₁)
    (hinv : ∀ l ∈ LB M Q B, conjSubgroup l A₂ = A₂) :
    ∀ l ∈ LB M Q B, ∀ a ∈ A₂, ⁅l, a⁆ ∈ Z := by
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set V1 : Subgroup G := Vone Q B (conjSubgroup r B) V with hV1def
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hV1Q : V1 ≤ Q := vone_le_Q hVQ
  have hQV : Q ≤ Subgroup.normalizer (V : Set G) := by
    refine sec8_le_normalizer_of_conj fun x hx y hy => ?_
    have hc' : ⁅x, y⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hx (hVQ hy)
    rw [show x * y * x⁻¹ = ⁅x, y⁆ * y by rw [commutatorElement_def]; group]
    exact V.mul_mem (sec39_Z_le_Vt hc') hy
  have hA2V : A₂ ⊓ V = Z := by
    refine le_antisymm ?_ (le_inf hZA₂ sec39_Z_le_Vt)
    rintro x ⟨hxA2, hxV⟩
    rw [← hA₁A₂]
    exact ⟨hVA₁ hxV, hxA2⟩
  have hQnormW : Q ≤ Subgroup.normalizer (V ⊓ QB B : Set G) := by
    intro q hq
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxV, hxQB⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hQV hq) x).mp hxV
    · have hQBconj : conjSubgroup q (QB B) = QB (conjSubgroup q B) := by
        rw [QB_conj]
      have hconjQB : conjSubgroup q (Q ⊓ QB B) = Q ⊓ QB B := by
        rw [conjSubgroup_inf, hc.conj_Q_eq (hc.hyp.Q_normal.1 hq), hQBconj]
        exact hc.conj_inf_QB_of_mem_Q hq
      have hx' : q * x * q⁻¹ ∈ conjSubgroup q (Q ⊓ QB B) :=
        ⟨x, ⟨hVQ hxV, hxQB⟩, rfl⟩
      rw [hconjQB] at hx'
      exact (Subgroup.mem_inf.mp hx').2
  intro l hl a ha
  have haV1 : a ∈ V1 := hA₂V₁ ha
  have hV1eq : V1 = (V1 ⊓ QB B) ⊔ V := by
    rw [hV1def, hVdef]
    exact Ctx.vone_eq_inf_QB_sup (hc := hc) (hs := hs) (t := t) (r := r)
  have ha' : a ∈ (V1 ⊓ QB B) ⊔ V := by rwa [← hV1eq]
  obtain ⟨c, hc_mem, v, hv, haeq⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer (H := V1 ⊓ QB B) (K := V)
      (fun y hy => hQV (inf_le_left.trans hV1Q hy)) ha'
  have hcV1 : c ∈ V1 := hc_mem.1
  have hcQB : c ∈ QB B := hc_mem.2
  have hcQ : c ∈ Q := vone_le_Q hVQ hcV1
  have hlc : ⁅l, c⁆ ∈ B ⊔ Z := by
    rw [sup_comm]
    exact hc.comm_LB_inf_QB_mem_sup hl ⟨hcQ, hcQB⟩
  have hlv : ⁅l, v⁆ ∈ Q ⊓ QB B := by
    refine hc.comm_LB_mem_inf hl (hVQ hv) ?_
    refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    have hbV : b ∈ V := hc.B_le_Vt hs.mem hb
    exact (congrArg (fun z : ↥V => (z : G))
      ((hc.Vt_isElemAbelian h35 hs.mem hs.notQ).1.is_comm.comm
        ⟨v, hv⟩ ⟨b, hbV⟩)).symm
  have hBZ : B ⊔ Z ≤ V ⊓ QB B :=
    sup_le (le_inf (hc.B_le_Vt hs.mem) hc.B_le_QB)
      (le_inf sec39_Z_le_Vt hc.Z_le_QB.1)
  have hlcW : ⁅l, c⁆ ∈ V ⊓ QB B := hBZ hlc
  have hlvV : ⁅l, v⁆ ∈ V := by
    have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) hs.mem hl
    have h1 : l * v * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt hs.mem hlR) v).mp hv
    rw [commutatorElement_def]
    exact V.mul_mem h1 (V.inv_mem hv)
  have hlvW : ⁅l, v⁆ ∈ V ⊓ QB B := ⟨hlvV, (Subgroup.mem_inf.mp hlv).2⟩
  have hconjlv : c * ⁅l, v⁆ * c⁻¹ ∈ V ⊓ QB B :=
    (Subgroup.mem_normalizer_iff.mp (hQnormW hcQ) ⁅l, v⁆).mp hlvW
  have hlaW : ⁅l, a⁆ ∈ V ⊓ QB B := by
    rw [← haeq, commutatorElement_mul_right_eq_mul_conj]
    simpa only [mul_assoc] using (V ⊓ QB B).mul_mem hlcW hconjlv
  have hlaA2 : ⁅l, a⁆ ∈ A₂ := by
    have hconj : conjSubgroup l A₂ = A₂ := hinv l hl
    have h1 : l * a * l⁻¹ ∈ A₂ := by
      rw [← hconj]
      exact ⟨a, ha, rfl⟩
    exact A₂.mul_mem h1 (A₂.inv_mem ha)
  rw [← hA2V]
  exact ⟨hlaA2, hlaW.1⟩

theorem Ctx.isIndecSec_vone_of_proj (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t) (hsp : SpNat hc t)
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    (hVW : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r)
    (hproj : ∀ A₁ A₂ : Subgroup G, Z ≤ A₁ → A₁ ≤ Sec8V1 M Q Z B t r →
      Z ≤ A₂ → A₂ ≤ Sec8V1 M Q Z B t r → A₁ ≠ Z → A₂ ≠ Z →
      A₁ ⊔ A₂ = Sec8V1 M Q Z B t r → A₁ ⊓ A₂ = Z →
      (∀ q ∈ Rt M (LB M Q B) t, conjSubgroup q A₁ = A₁ ∧ conjSubgroup q A₂ = A₂) →
      Vt M (LB M Q B) B Z t ≤ A₁ ∨ Vt M (LB M Q B) B Z t ≤ A₂) :
    IsIndecSec (Rt M (LB M Q B) t) (Vone Q B (conjSubgroup r B)
      (Vt M (LB M Q B) B Z t)) Z := by
  classical
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set V1 : Subgroup G := Vone Q B (conjSubgroup r B) V with hV1def
  have hVab : ∀ x ∈ V1, ∀ y ∈ V1, x * y = y * x := by
    intro x hx y hy
    have hxW : x ∈ Wt Q V1 := hVW hx
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxW).2 y hy).symm
  rintro ⟨A₁, A₂, hZA₁, hA₁V₁, hZA₂, hA₂V₁, hA₁ne, hA₂ne, hsup, hinf, hinv⟩
  have hfinish : ∀ {A B₂ : Subgroup G}, Z ≤ B₂ → B₂ ≠ Z → B₂ ≤ V1 → A ≤ V1 →
      A ⊓ B₂ = Z → V ≤ A → (∀ q ∈ Rt M (LB M Q B) t, conjSubgroup q B₂ = B₂) → False := by
    intro A B₂ hZB hBne hBV1 hAV1 hAB hVA hinvB
    have hcomm := Ctx.comm_A2_LB_le_Z (hc := hc) (hs := hs) (r := r)
      (h35 := h35) (A₁ := A) (A₂ := B₂) hZB hBV1 hAB hVA
      (fun l hl => hinvB l (le_Rt (LB M Q B) hs.mem hl))
    have hBQ : B₂ ≤ Q := hBV1.trans (vone_le_Q (hc.Vt_le_Q t))
    have hBCQt : B₂ ≤ CQt Q Z (LB M Q B) := by
      intro b hb
      exact ⟨hBQ hb, fun l hl => hcomm l hl b hb⟩
    have hBle' : B₂ ≤ (B ⊔ Z : Subgroup G) := by
      rw [h35] at hBCQt
      exact hBCQt
    have hBleV : B₂ ≤ V :=
      le_trans hBle' (sup_le (hc.B_le_Vt hs.mem) sec39_Z_le_Vt)
    have hBleA : B₂ ≤ A := hBleV.trans hVA
    have hBleZ : B₂ ≤ Z := by
      rw [← hAB]
      exact le_inf hBleA le_rfl
    exact hBne (le_antisymm hBleZ hZB)
  rcases hproj A₁ A₂ hZA₁ hA₁V₁ hZA₂ hA₂V₁ hA₁ne hA₂ne hsup hinf hinv with hVA₁ | hVA₂
  · exact hfinish hZA₂ hA₂ne hA₂V₁ hA₁V₁ hinf hVA₁ (fun q hq => (hinv q hq).2)
  · exact hfinish hZA₁ hA₁ne hA₁V₁ hA₂V₁ (by rw [inf_comm]; exact hinf) hVA₂
      (fun q hq => (hinv q hq).1)


theorem Ctx.vone_proj_of_card (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hsp : SpNat hc t) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ∀ A₁ A₂ : Subgroup G, Z ≤ A₁ → A₁ ≤ Sec8V1 M Q Z B t r →
      Z ≤ A₂ → A₂ ≤ Sec8V1 M Q Z B t r → A₁ ≠ Z → A₂ ≠ Z →
      A₁ ⊔ A₂ = Sec8V1 M Q Z B t r → A₁ ⊓ A₂ = Z →
      (∀ q ∈ Rt M (LB M Q B) t, conjSubgroup q A₁ = A₁ ∧ conjSubgroup q A₂ = A₂) →
      Vt M (LB M Q B) B Z t ≤ A₁ ∨ Vt M (LB M Q B) B Z t ≤ A₂ := by
  classical
  intro A₁ A₂ hZA₁ hA₁V hZA₂ hA₂V hA₁ne hA₂ne hsup hinf hinv
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set V1 : Subgroup G := Sec8V1 M Q Z B t r with hV1def
  obtain ⟨K, hK, hKf, hKc, m, hm, hrep⟩ := hsp
  letI := hK
  letI := hKf
  obtain ⟨e, -, he, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKc.trans he)
  have hV : SpMNat hc t m := ⟨K, hK, hKf, hKc, hrep⟩
  have hsp' : SpNat hc t := ⟨K, hK, hKf, hKc, m, hm, hrep⟩
  have hVV1 : V ≤ V1 := by
    rw [hV1def, hVdef]
    exact le_inf le_sup_right le_sup_right
  have hVW := stroth53VW_holds h34 hRoot h51 G M Q Z B hc n t hs hsp' r hr hplane
  have hVab : ∀ x ∈ V1, ∀ y ∈ V1, x * y = y * x := by
    intro x hx y hy
    have hxW : x ∈ Wt Q V1 := hVW (by rw [← hV1def]; exact hx)
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxW).2 y hy).symm
  have hVtInv : ∀ q ∈ Rt M (LB M Q B) t, conjSubgroup q V = V := by
    intro q hq
    rw [hVdef]
    exact conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem hq)
  have hUinv : ∀ (A : Subgroup G), (∀ q ∈ Rt M (LB M Q B) t, conjSubgroup q A = A) →
      ∀ q ∈ Rt M (LB M Q B) t, ∀ u ∈ V ⊓ A, q * u * q⁻¹ ∈ V ⊓ A := by
    intro A hA q hq u hu
    refine ⟨?_, ?_⟩
    · have hmem : q * u * q⁻¹ ∈ conjSubgroup q V := ⟨u, hu.1, rfl⟩
      rwa [hVtInv q hq] at hmem
    · have hmem : q * u * q⁻¹ ∈ conjSubgroup q A := ⟨u, hu.2, rfl⟩
      rwa [hA q hq] at hmem
  have hZU₁ : Z ≤ V ⊓ A₁ := le_inf (by rw [hVdef]; exact sec39_Z_le_Vt) hZA₁
  have hZU₂ : Z ≤ V ⊓ A₂ := le_inf (by rw [hVdef]; exact sec39_Z_le_Vt) hZA₂
  rcases hrep.eq_or_eq_of_invariant natIrred_statedSp addCommutantScalar_statedSp
    (R := Rt M (LB M Q B) t) (V := V) (Z := Z) (N := hc.CN t)
    hZU₁ inf_le_left (hUinv A₁ (fun q hq => (hinv q hq).1)) with hU₁ | hU₁
  · rcases hrep.eq_or_eq_of_invariant natIrred_statedSp addCommutantScalar_statedSp
      (R := Rt M (LB M Q B) t) (V := V) (Z := Z) (N := hc.CN t)
      hZU₂ inf_le_left (hUinv A₂ (fun q hq => (hinv q hq).2)) with hU₂ | hU₂
    ·
      have hcommV₁ : ∀ x ∈ V, ∀ y ∈ A₁, x * y = y * x :=
        fun x hx y hy => hVab x (hVV1 hx) y (hA₁V hy)
      have hcommV₂ : ∀ x ∈ V, ∀ y ∈ A₂, x * y = y * x :=
        fun x hx y hy => hVab x (hVV1 hx) y (hA₂V hy)
      have hcommA : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x :=
        fun x hx y hy => hVab x (hA₁V hx) y (hA₂V hy)
      have hcard₁ := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V A₁ hcommV₁).1
      rw [hU₁] at hcard₁
      have hcard₂ := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V A₂ hcommV₂).1
      rw [hU₂] at hcard₂
      have hsup₁ : V ⊔ A₁ ≤ V1 := sup_le hVV1 hA₁V
      have hsup₂ : V ⊔ A₂ ≤ V1 := sup_le hVV1 hA₂V
      have hle₁ : Nat.card ↥(V ⊔ A₁) ≤ Nat.card ↥V1 :=
        Nat.card_le_card_of_injective (fun x : ↥(V ⊔ A₁) => (⟨x.1, hsup₁ x.2⟩ : ↥V1))
          (by intro x y hxy; simpa using hxy)
      have hle₂ : Nat.card ↥(V ⊔ A₂) ≤ Nat.card ↥V1 :=
        Nat.card_le_card_of_injective (fun x : ↥(V ⊔ A₂) => (⟨x.1, hsup₂ x.2⟩ : ↥V1))
          (by intro x y hxy; simpa using hxy)
      have hcl := Ctx.card_vone_le (h34 := h34) (hRoot := hRoot) (h51 := h51)
        (hc := hc) (hs := hs) (m := m) (t := t) (hm := hm) (hV := hV)
        (r := r) (hr := hr) (hplane := hplane)
      have hA₁le : Nat.card ↥A₁ ≤ Nat.card Z * Nat.card Z := by
        have h1 : Nat.card ↥V * Nat.card ↥A₁ ≤ Nat.card ↥V * (Nat.card Z * Nat.card Z) := by
          calc Nat.card ↥V * Nat.card ↥A₁
              = Nat.card ↥(V ⊔ A₁) * Nat.card Z := hcard₁.symm
            _ ≤ Nat.card ↥V1 * Nat.card Z := Nat.mul_le_mul_right _ hle₁
            _ ≤ (Nat.card ↥V * Nat.card Z) * Nat.card Z := Nat.mul_le_mul_right _ hcl
            _ = Nat.card ↥V * (Nat.card Z * Nat.card Z) := by ring
        exact Nat.le_of_mul_le_mul_left h1 Nat.card_pos
      have hA₂le : Nat.card ↥A₂ ≤ Nat.card Z * Nat.card Z := by
        have h1 : Nat.card ↥V * Nat.card ↥A₂ ≤ Nat.card ↥V * (Nat.card Z * Nat.card Z) := by
          calc Nat.card ↥V * Nat.card ↥A₂
              = Nat.card ↥(V ⊔ A₂) * Nat.card Z := hcard₂.symm
            _ ≤ Nat.card ↥V1 * Nat.card Z := Nat.mul_le_mul_right _ hle₂
            _ ≤ (Nat.card ↥V * Nat.card Z) * Nat.card Z := Nat.mul_le_mul_right _ hcl
            _ = Nat.card ↥V * (Nat.card Z * Nat.card Z) := by ring
        exact Nat.le_of_mul_le_mul_left h1 Nat.card_pos
      have hcardA := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₁ A₂ hcommA).1
      rw [hsup, hinf] at hcardA
      have hV1le : Nat.card ↥V1 ≤ Nat.card Z ^ 3 := by
        have h2 : Nat.card ↥V1 * Nat.card Z ≤ Nat.card Z ^ 3 * Nat.card Z := by
          refine le_trans ?_ (Nat.mul_le_mul_right _ (le_refl _))
          calc Nat.card ↥V1 * Nat.card Z
              = Nat.card ↥A₁ * Nat.card ↥A₂ := hcardA
            _ ≤ (Nat.card Z * Nat.card Z) * (Nat.card Z * Nat.card Z) := Nat.mul_le_mul hA₁le hA₂le
            _ = Nat.card Z ^ 3 * Nat.card Z := by ring
        exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos
      have hVle : Nat.card ↥V ≤ Nat.card Z ^ 3 := by
        refine le_trans ?_ hV1le
        exact Nat.card_le_card_of_injective (fun x : ↥V => (⟨x.1, hVV1 x.2⟩ : ↥V1))
          (by intro x y hxy; simpa using hxy)
      have hVcard : Nat.card ↥V = Nat.card Z ^ (2 * m + 1) := by
        rw [hVdef]; exact SpMNat.card_V hV
      have hq2 : 1 < Nat.card Z := by have := hc.hyp.q4; omega
      have h5le : Nat.card Z ^ 5 ≤ Nat.card Z ^ (2 * m + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hlt : Nat.card Z ^ 3 < Nat.card Z ^ 5 :=
        Nat.pow_lt_pow_right hq2 (by norm_num)
      rw [hVcard] at hVle
      omega
    ·
      exact Or.inr (hU₂ ▸ inf_le_right)
  ·
    exact Or.inl (hU₁ ▸ inf_le_right)

theorem stroth53IndecVone_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) : Stroth53IndecVoneStatement := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane
  by_cases hE : Sec8V1 M Q Z B t r = Vt M (LB M Q B) B Z t
  · exact Ctx.isIndecSec_vone_of_eq (hc := hc) (hsp := hsp) (r := r) hE
  · have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
    have hVW := stroth53VW_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane
    exact Ctx.isIndecSec_vone_of_proj (h34 := h34) (h51 := h51) (hc := hc)
      (hs := hs) (hsp := hsp) (hr := hr) (hplane := hplane) (h35 := h35) (hVW := hVW)
      (fun A₁ A₂ hZA₁ hA₁V hZA₂ hA₂V hA₁ne hA₂ne hsup hinf hinv =>
        Ctx.vone_proj_of_card (h34 := h34) (hRoot := hRoot) (h51 := h51) (hc := hc)
          (hs := hs) (hsp := hsp) (hr := hr) (hplane := hplane)
          A₁ A₂ hZA₁ hA₁V hZA₂ hA₂V hA₁ne hA₂ne hsup hinf hinv)

end CFSG.RankThree.GF2n.Stroth80
