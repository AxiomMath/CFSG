module

public import CFSG.RankThree.GF2n.Stroth80.Sec53cProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sec5_commutator_le_of_prod {X N A B I : Subgroup G}
    (hprod : ∀ n ∈ N, ∃ a ∈ A, ∃ b ∈ B, n = a * b)
    (hA : ⁅X, A⁆ ≤ I) (hB : ⁅X, B⁆ ≤ I)
    (hAI : A ≤ Subgroup.normalizer (I : Set G)) : ⁅X, N⁆ ≤ I := by
  refine Subgroup.commutator_le.mpr fun x hx n hn => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := hprod n hn
  have h1 : ⁅x, b⁆ ∈ I := hB (Subgroup.commutator_mem_commutator hx hb)
  have h2 : ⁅x, a⁆ ∈ I := hA (Subgroup.commutator_mem_commutator hx ha)
  have h3 : a * ⁅x, b⁆ * a⁻¹ ∈ I :=
    (Subgroup.mem_normalizer_iff.mp (hAI ha) _).mp h1
  rw [show ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) by
    simp only [commutatorElement_def]; group]
  exact I.mul_mem h2 h3

theorem sec5_commutator_le_of_prod_left {W Q₁ Q₂ N I : Subgroup G}
    (hprod : ∀ w ∈ W, ∃ q₁ ∈ Q₁, ∃ q₂ ∈ Q₂, w = q₁ * q₂)
    (hQ₁I : Q₁ ≤ Subgroup.normalizer (I : Set G))
    (h₁ : ⁅Q₁, N⁆ ≤ I) (h₂ : ⁅Q₂, N⁆ ≤ I) : ⁅W, N⁆ ≤ I := by
  refine Subgroup.commutator_le.mpr fun w hw n hn => ?_
  obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := hprod w hw
  have h1 : ⁅q₂, n⁆ ∈ I := h₂ (Subgroup.commutator_mem_commutator hq₂ hn)
  have h2 : ⁅q₁, n⁆ ∈ I := h₁ (Subgroup.commutator_mem_commutator hq₁ hn)
  have h3 : q₁ * ⁅q₂, n⁆ * q₁⁻¹ ∈ I :=
    (Subgroup.mem_normalizer_iff.mp (hQ₁I hq₁) _).mp h1
  rw [show ⁅q₁ * q₂, n⁆ = q₁ * ⁅q₂, n⁆ * q₁⁻¹ * ⁅q₁, n⁆ by
    simp only [commutatorElement_def]; group]
  exact I.mul_mem h3 h2

theorem sec5_commutator_le_of_decomp {N A B W Q₁ Q₂ I : Subgroup G}
    (hN : ∀ n ∈ N, ∃ a ∈ A, ∃ b ∈ B, n = a * b)
    (hW : ∀ w ∈ W, ∃ q₁ ∈ Q₁, ∃ q₂ ∈ Q₂, w = q₁ * q₂)
    (hA₁ : ⁅Q₁, A⁆ ≤ I) (hA₂ : ⁅Q₂, A⁆ ≤ I)
    (hB₁ : ⁅Q₁, B⁆ ≤ I) (hB₂ : ⁅Q₂, B⁆ ≤ I)
    (hQ₁I : Q₁ ≤ Subgroup.normalizer (I : Set G))
    (hAI : A ≤ Subgroup.normalizer (I : Set G)) : ⁅W, N⁆ ≤ I :=
  sec5_commutator_le_of_prod hN
    (sec5_commutator_le_of_prod_left hW hQ₁I hA₁ hA₂)
    (sec5_commutator_le_of_prod_left hW hQ₁I hB₁ hB₂) hAI

variable [Finite G] {M Q Z B : Subgroup G}

theorem sec52a_comm_of_decomp (hc : Ctx M Q Z B) {n : ℕ} {t r : G}
    (hs : Sec5Hyp hc n t) (hr : r ∈ Rt M (LB M Q B) t)
    (hdec : ∀ x ∈ hc.CN t, ∃ a ∈ LB M Q B ⊓ hc.CN t,
      ∃ b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, x = a * b)
    (hprod : ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ∃ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t), x = a * b)
    (hboxB : ⁅QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      LB M Q B ⊓ hc.CN t⁆ ≤ Vt M (LB M Q B) B Z t)
    (hboxC : ⁅QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      LB M Q (conjSubgroup r B) ⊓ hc.CN t⁆ ≤ Vt M (LB M Q B) B Z t) :
    ⁅Wt Q (Vt M (LB M Q B) B Z t), hc.CN t⁆ ≤ Vt M (LB M Q B) B Z t := by
  have ht : t ∈ LB M Q B := hs.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  set V : Subgroup G := Vt M (LB M Q B) B Z t
  set W : Subgroup G := Wt Q V
  set N : Subgroup G := hc.CN t
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hQN : Q ≤ Subgroup.normalizer (V : Set G) :=
    (hc.Q_le_Rt ht).trans (hc.Rt_normalizes_Vt ht)
  have hLCleR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := by
    rw [hc.LB_conj hrM]
    intro x hx
    rw [mem_conjSubgroup] at hx
    have h1 : r * (r⁻¹ * x * r) * r⁻¹ ∈ Rt M (LB M Q B) t :=
      (Rt M (LB M Q B) t).mul_mem
        ((Rt M (LB M Q B) t).mul_mem hr
          ((le_Rt (G := G) (M := M) (L := LB M Q B) (t := t) ht) hx))
        ((Rt M (LB M Q B) t).inv_mem hr)
    rwa [show r * (r⁻¹ * x * r) * r⁻¹ = x by group] at h1
  have hAN : LB M Q B ⊓ N ≤ Subgroup.normalizer (V : Set G) := by
    intro x hx
    exact hc.Rt_normalizes_Vt ht
      ((le_Rt (G := G) (M := M) (L := LB M Q B) (t := t) ht) hx.1)
  have hQ₁N : QB B ⊓ W ≤ Subgroup.normalizer (V : Set G) :=
    ((inf_le_right : QB B ⊓ W ≤ W).trans (inf_le_left : W ≤ Q)).trans hQN
  have hZBV : (Z ⊔ B : Subgroup G) ≤ V :=
    sup_le sec39_Z_le_Vt (hc.B_le_Vt ht)
  have heasyB : ⁅QB B ⊓ W, LB M Q B ⊓ N⁆ ≤ V := by
    refine Subgroup.commutator_le.mpr fun a ha l hl => ?_
    have hla : ⁅l, a⁆ ∈ (Z ⊔ B : Subgroup G) :=
      hc.comm_LB_inf_QB_mem_sup hl.1 ⟨(inf_le_left : W ≤ Q) ha.2, ha.1⟩
    rw [← commutatorElement_inv]
    exact V.inv_mem (hZBV hla)
  have heasyC : ⁅QB (conjSubgroup r B) ⊓ W, LB M Q (conjSubgroup r B) ⊓ N⁆ ≤ V := by
    refine Subgroup.commutator_le.mpr fun a ha l hl => ?_
    have hla : ⁅l, a⁆ ∈ (Z ⊔ conjSubgroup r B : Subgroup G) :=
      hcC.comm_LB_inf_QB_mem_sup hl.1 ⟨(inf_le_left : W ≤ Q) ha.2, ha.1⟩
    have hCV : conjSubgroup r B ≤ V :=
      (le_sup_left : conjSubgroup r B ≤ conjSubgroup r B ⊔ Z).trans
        (hc.conj_Rt_le_Vt ht hr)
    have hZCV : (Z ⊔ conjSubgroup r B : Subgroup G) ≤ V :=
      sup_le sec39_Z_le_Vt hCV
    rw [← commutatorElement_inv]
    exact V.inv_mem (hZCV hla)
  exact sec5_commutator_le_of_decomp hdec hprod heasyB hboxB hboxC heasyC hQ₁N hAN

theorem sec53b_comm_of_decomp (hc : Ctx M Q Z B) {n : ℕ} {t r : G}
    (hs : Sec5Hyp hc n t) (hr : r ∈ Rt M (LB M Q B) t)
    (hdec : ∀ x ∈ hc.CN t, ∃ a ∈ LB M Q B ⊓ hc.CN t,
      ∃ b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, x = a * b)
    (hprod : ∀ x ∈ Sec8W1 M Q Z B t r,
      ∃ a ∈ QB B ⊓ Sec8W1 M Q Z B t r,
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r, x = a * b)
    (hboxB : ⁅QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r,
      LB M Q B ⊓ hc.CN t⁆ ≤ Sec8V1 M Q Z B t r)
    (hboxC : ⁅QB B ⊓ Sec8W1 M Q Z B t r,
      LB M Q (conjSubgroup r B) ⊓ hc.CN t⁆ ≤ Sec8V1 M Q Z B t r) :
    ⁅Sec8W1 M Q Z B t r, hc.CN t⁆ ≤ Sec8V1 M Q Z B t r := by
  have ht : t ∈ LB M Q B := hs.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  set V : Subgroup G := Vt M (LB M Q B) B Z t
  set V₁ : Subgroup G := Sec8V1 M Q Z B t r
  set W₁ : Subgroup G := Sec8W1 M Q Z B t r
  set N : Subgroup G := hc.CN t
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hV₁Q : V₁ ≤ Q := vone_le_Q hVQ
  have hVV₁ : V ≤ V₁ := le_inf le_sup_right le_sup_right
  have hZV₁ : Z ≤ V₁ := Z_le_vone
  have hBV₁ : B ≤ V₁ := (hc.B_le_Vt ht).trans hVV₁
  have hCV₁ : conjSubgroup r B ≤ V₁ :=
    (le_sup_left : conjSubgroup r B ≤ conjSubgroup r B ⊔ Z).trans
      ((hc.conj_Rt_le_Vt ht hr).trans hVV₁)
  have hQN : Q ≤ Subgroup.normalizer (V₁ : Set G) := hc.Q_le_normalizer_vone t
  have hLCleR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := by
    rw [hc.LB_conj hrM]
    intro x hx
    rw [mem_conjSubgroup] at hx
    have h1 : r * (r⁻¹ * x * r) * r⁻¹ ∈ Rt M (LB M Q B) t :=
      (Rt M (LB M Q B) t).mul_mem
        ((Rt M (LB M Q B) t).mul_mem hr
          ((le_Rt (G := G) (M := M) (L := LB M Q B) (t := t) ht) hx))
        ((Rt M (LB M Q B) t).inv_mem hr)
    rwa [show r * (r⁻¹ * x * r) * r⁻¹ = x by group] at h1
  have hLN : LB M Q B ≤ Subgroup.normalizer (V₁ : Set G) :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := LB M Q B) (K := V₁)).mpr
      (hc.comm_LB_vone_le_vone hs)
  have hAN : LB M Q B ⊓ N ≤ Subgroup.normalizer (V₁ : Set G) :=
    (inf_le_left : LB M Q B ⊓ N ≤ LB M Q B).trans hLN
  have hQ₁N : QB B ⊓ W₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    ((inf_le_right : QB B ⊓ W₁ ≤ W₁).trans (inf_le_left : W₁ ≤ Q)).trans hQN
  have hZBV₁ : (Z ⊔ B : Subgroup G) ≤ V₁ := sup_le hZV₁ hBV₁
  have heasyB : ⁅QB B ⊓ W₁, LB M Q B ⊓ N⁆ ≤ V₁ := by
    refine Subgroup.commutator_le.mpr fun a ha l hl => ?_
    have hla : ⁅l, a⁆ ∈ (Z ⊔ B : Subgroup G) :=
      hc.comm_LB_inf_QB_mem_sup hl.1 ⟨(inf_le_left : W₁ ≤ Q) ha.2, ha.1⟩
    rw [← commutatorElement_inv]
    exact V₁.inv_mem (hZBV₁ hla)
  have heasyC : ⁅QB (conjSubgroup r B) ⊓ W₁, LB M Q (conjSubgroup r B) ⊓ N⁆ ≤ V₁ := by
    refine Subgroup.commutator_le.mpr fun a ha l hl => ?_
    have hla : ⁅l, a⁆ ∈ (Z ⊔ conjSubgroup r B : Subgroup G) :=
      hcC.comm_LB_inf_QB_mem_sup hl.1 ⟨(inf_le_left : W₁ ≤ Q) ha.2, ha.1⟩
    have hZCV₁ : (Z ⊔ conjSubgroup r B : Subgroup G) ≤ V₁ := sup_le hZV₁ hCV₁
    rw [← commutatorElement_inv]
    exact V₁.inv_mem (hZCV₁ hla)
  exact sec5_commutator_le_of_decomp hdec hprod heasyB hboxB hboxC heasyC hQ₁N hAN

theorem sec52a_comm_of_51 (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t r : G}
    (hs : Sec5Hyp hc n t) (hOmega : OmegaNat hc t) (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hprod : ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ∃ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t), x = a * b)
    (hboxB : ⁅QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      LB M Q B ⊓ hc.CN t⁆ ≤ Vt M (LB M Q B) B Z t)
    (hboxC : ⁅QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      LB M Q (conjSubgroup r B) ⊓ hc.CN t⁆ ≤ Vt M (LB M Q B) B Z t) :
    ⁅Wt Q (Vt M (LB M Q B) B Z t), hc.CN t⁆ ≤ Vt M (LB M Q B) B Z t := by
  have hdec : ∀ x ∈ hc.CN t, ∃ a ∈ LB M Q B ⊓ hc.CN t,
      ∃ b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, x = a * b :=
    (h51 G M Q Z B hc n t hs (Or.inr hOmega) r hr hplane (conjSubgroup r B) (LB M Q B)
      (LB M Q (conjSubgroup r B)) (hc.CN t) (Rt M (LB M Q B) t)
      rfl rfl rfl rfl rfl).1
  exact sec52a_comm_of_decomp hc hs hr hdec hprod hboxB hboxC

theorem sec53b_comm_of_51 (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t r : G}
    (hs : Sec5Hyp hc n t) (hSp : SpNat hc t) (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hprod : ∀ x ∈ Sec8W1 M Q Z B t r,
      ∃ a ∈ QB B ⊓ Sec8W1 M Q Z B t r,
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r, x = a * b)
    (hboxB : ⁅QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r,
      LB M Q B ⊓ hc.CN t⁆ ≤ Sec8V1 M Q Z B t r)
    (hboxC : ⁅QB B ⊓ Sec8W1 M Q Z B t r,
      LB M Q (conjSubgroup r B) ⊓ hc.CN t⁆ ≤ Sec8V1 M Q Z B t r) :
    ⁅Sec8W1 M Q Z B t r, hc.CN t⁆ ≤ Sec8V1 M Q Z B t r := by
  have hdec : ∀ x ∈ hc.CN t, ∃ a ∈ LB M Q B ⊓ hc.CN t,
      ∃ b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, x = a * b :=
    (h51 G M Q Z B hc n t hs (Or.inl hSp) r hr hplane (conjSubgroup r B) (LB M Q B)
      (LB M Q (conjSubgroup r B)) (hc.CN t) (Rt M (LB M Q B) t)
      rfl rfl rfl rfl rfl).1
  exact sec53b_comm_of_decomp hc hs hr hdec hprod hboxB hboxC

end CFSG.RankThree.GF2n.Stroth80
