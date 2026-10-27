module

public import CFSG.Quasithin.EmptyFaithful.S151ZF
public import CFSG.Quasithin.EmptyFaithful.S151ZM
public import CFSG.Quasithin.Background.FLcMLEMat
public import CFSG.Quasithin.Background.FLcLn

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {A : Type} [Group A]

theorem corner_unique {n : ℕ} (hn : 2 ≤ n) {g g' : SLt n} (h1 : g ∈ Tgrp n 1)
    (h2 : g ∈ Tgrp n (n - 1)) (h1' : g' ∈ Tgrp n 1) (h2' : g' ∈ Tgrp n (n - 1)) (hg : g ≠ 1)
    (hg' : g' ≠ 1) : g = g' := by
  have hn0 : 0 < n := by omega
  have hn1 : n - 1 < n := by omega
  have hout : ∀ x : SLt n, x ∈ Tgrp n 1 → x ∈ Tgrp n (n - 1) → ∀ p q : Fin n,
      ¬ ((p : ℕ) = 0 ∧ (q : ℕ) = n - 1) → mat x p q = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) p q := by
    intro x hx1 hx2 p q hpq
    by_cases hA : (p : ℕ) < 1 ∧ 1 ≤ (q : ℕ)
    · have hB : ¬ ((p : ℕ) < n - 1 ∧ n - 1 ≤ (q : ℕ)) := by
        have := q.2
        omega
      exact hx2 p q hB
    · exact hx1 p q hA
  have hcorner : ∀ x : SLt n, x ∈ Tgrp n 1 → x ∈ Tgrp n (n - 1) → x ≠ 1 →
      mat x ⟨0, hn0⟩ ⟨n - 1, hn1⟩ = 1 := by
    intro x hx1 hx2 hx
    by_contra hne
    apply hx
    apply Subtype.ext
    ext p q
    by_cases hpq : (p : ℕ) = 0 ∧ (q : ℕ) = n - 1
    · have hp : p = ⟨0, hn0⟩ := Fin.ext hpq.1
      have hq : q = ⟨n - 1, hn1⟩ := Fin.ext hpq.2
      subst hp
      subst hq
      have h0 : mat x ⟨0, hn0⟩ ⟨n - 1, hn1⟩ = 0 := by
        rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) (mat x ⟨0, hn0⟩ ⟨n - 1, hn1⟩) with h | h
        · exact h
        · exact absurd h hne
      have hne' : (⟨0, hn0⟩ : Fin n) ≠ ⟨n - 1, hn1⟩ := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      show mat x ⟨0, hn0⟩ ⟨n - 1, hn1⟩ = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) ⟨0, hn0⟩ ⟨n - 1, hn1⟩
      rw [h0, Matrix.one_apply_ne hne']
    · exact hout x hx1 hx2 p q hpq
  apply Subtype.ext
  ext p q
  by_cases hpq : (p : ℕ) = 0 ∧ (q : ℕ) = n - 1
  · have hp : p = ⟨0, hn0⟩ := Fin.ext hpq.1
    have hq : q = ⟨n - 1, hn1⟩ := Fin.ext hpq.2
    subst hp
    subst hq
    show mat g ⟨0, hn0⟩ ⟨n - 1, hn1⟩ = mat g' ⟨0, hn0⟩ ⟨n - 1, hn1⟩
    rw [hcorner g h1 h2 hg, hcorner g' h1' h2' hg']
  · show mat g p q = mat g' p q
    rw [hout g h1 h2 p q hpq, hout g' h1' h2' p q hpq]

theorem mem_corner_of_commute_Ut {n : ℕ} (hn : 2 ≤ n) {b : SLt n}
    (hb : ∀ g ∈ Ut n, b * g = g * b) : b ∈ Tgrp n 1 ∧ b ∈ Tgrp n (n - 1) :=
  ⟨mem_Tgrp_of_commute le_rfl (by omega) fun t ht => hb t (Tgrp_le_Ut 1 ht),
    mem_Tgrp_of_commute (by omega) (by omega) fun t ht => hb t (Tgrp_le_Ut (n - 1) ht)⟩

theorem zl2_of_simple_Ln [Finite A] {L S : Subgroup A} {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e₀ : ↥L ≃* SLt n) (hSN : S ≤ Subgroup.normalizer (L : Set A))
    (hSyl : IsSylowTwoOf (S ⊓ L) L) : ZL2 S L := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨D⟩ := exists_borelIso (by omega) hSyl e₀
  have key : ∀ (a : A) (haS : a ∈ S), (∀ c ∈ S, ⁅a, c⁆ ∈ Subgroup.centralizer (L : Set A)) →
      ∃ b : SLt n, b ∈ Tgrp n 1 ∧ b ∈ Tgrp n (n - 1) ∧
        ∀ x : ↥L, D.e (L.normalizerMonoidHom ⟨a, hSN haS⟩ x) = b * D.e x * b⁻¹ := by
    intro a haS hcent
    have haN : a ∈ Subgroup.normalizer (L : Set A) := hSN haS
    have hφfix : ∀ u ∈ Ut n, D.autOf a haN u = u := by
      intro u hu
      rw [← D.hB] at hu
      obtain ⟨x, hx, rfl⟩ := hu
      have hxS : (x : A) ∈ S := (Subgroup.mem_subgroupOf.1 hx).1
      have hx' : L.normalizerMonoidHom ⟨a, haN⟩ x = x := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        have hcomm := hcent (x : A) hxS
        have hL1 : a * (x : A) * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haN _).mp x.2
        have hL2 : ⁅a, (x : A)⁆ ∈ L := by
          rw [commutatorElement_def]
          exact L.mul_mem hL1 (L.inv_mem x.2)
        have hz : (⟨⁅a, (x : A)⁆, hL2⟩ : ↥L) = 1 := by
          apply FLc.center_trivial_of_equiv D.e
          intro h
          apply Subtype.ext
          exact Subgroup.mem_centralizer_iff.mp hcomm (h : A) h.2
        have := congrArg Subtype.val hz
        simp only [commutatorElement_def] at this
        have h3 : a * (x : A) * a⁻¹ * (x : A)⁻¹ = 1 := this
        rwa [mul_inv_eq_one] at h3
      show D.autOf a haN (D.e x) = D.e x
      rw [D.autOf_e, hx']
    have hφU : (Ut n).map (D.autOf a haN).toMonoidHom = Ut n := by
      ext g
      constructor
      · rintro ⟨u, hu, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, hφfix u hu]
        exact hu
      · intro hg
        exact ⟨g, hg, hφfix g hg⟩
    rcases aut_dichotomy hn3 (D.autOf a haN) hφU with ⟨b, hbU, hbφ⟩ | hswap
    · have hbcomm : ∀ g ∈ Ut n, b * g = g * b := by
        intro g hg
        have h1 := hbφ g
        rw [hφfix g hg] at h1
        calc b * g = (b * g * b⁻¹) * b := by group
          _ = g * b := by rw [← h1]
      obtain ⟨h1, h2⟩ := mem_corner_of_commute_Ut (by omega) hbcomm
      refine ⟨b, h1, h2, fun x => ?_⟩
      rw [← D.autOf_e a haN x]
      exact hbφ _
    · exact (no_swap_of_fixes hn _ hφfix hswap).elim
  intro a b haS hbS haC ha2 hac hbC hb2 hbc
  obtain ⟨ba, hba1, hba2, hbaφ⟩ := key a haS hac
  obtain ⟨bb, hbb1, hbb2, hbbφ⟩ := key b hbS hbc
  have haN : a ∈ Subgroup.normalizer (L : Set A) := hSN haS
  have hbN : b ∈ Subgroup.normalizer (L : Set A) := hSN hbS
  have hne : ∀ (c : A) (hcS : c ∈ S) (d : SLt n), c ∉ Subgroup.centralizer (L : Set A) →
      (∀ x : ↥L, D.e (L.normalizerMonoidHom ⟨c, hSN hcS⟩ x) = d * D.e x * d⁻¹) → d ≠ 1 := by
    intro c hcS d hcC hd hd1
    apply hcC
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := hd ⟨h, hh⟩
    rw [hd1, one_mul, inv_one, mul_one] at h1
    have h2 : L.normalizerMonoidHom ⟨c, hSN hcS⟩ ⟨h, hh⟩ = ⟨h, hh⟩ := D.e.injective h1
    have h3 : c * h * c⁻¹ = h := congrArg Subtype.val h2
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hba1' : ba ≠ 1 := hne a haS ba haC hbaφ
  have hbb1' : bb ≠ 1 := hne b hbS bb hbC hbbφ
  have hbb : ba = bb := corner_unique (by omega) hba1 hba2 hbb1 hbb2 hba1' hbb1'
  subst hbb
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have e1 := hbaφ ⟨h, hh⟩
  have e2 := hbbφ ⟨h, hh⟩
  have e3 : L.normalizerMonoidHom ⟨a, haN⟩ ⟨h, hh⟩ = L.normalizerMonoidHom ⟨b, hbN⟩ ⟨h, hh⟩ :=
    D.e.injective (e1.trans e2.symm)
  have e4 : a * h * a⁻¹ = b * h * b⁻¹ := congrArg Subtype.val e3
  have e5 : h * (a⁻¹ * b) = (a⁻¹ * b) * h := by
    have e6 : a⁻¹ * (a * h * a⁻¹) * b = a⁻¹ * (b * h * b⁻¹) * b := by rw [e4]
    have e7 : h * (a⁻¹ * b) = a⁻¹ * (a * h * a⁻¹) * b := by group
    have e8 : a⁻¹ * (b * h * b⁻¹) * b = a⁻¹ * b * h := by group
    rw [e7, e6, e8]
  exact e5

variable {G : Type} [Group G]

theorem input15122ThreeEZL2_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (kN : L45NotA38Type) :
    Input15122ThreeEZL2 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h3E
  obtain ⟨htype, -, -, -⟩ := h3E
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hsyl : IsSylowTwoOf (S ⊓ L) L := hc.h20.sylow
  have htypeq : IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) :=
    htype.imp (isPSL_quotient_pCore (by norm_num)) (isPSL_quotient_pCore (by norm_num))
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
    · exact absurd h2 (kN G L htypeq)
  rcases htype with h | h
  · obtain ⟨e₀⟩ := nonempty_equiv_SLt_of_isPSL h
    exact zl2_of_simple_Ln (Or.inl rfl) e₀ hSN hsyl
  · obtain ⟨e₀⟩ := nonempty_equiv_SLt_of_isPSL h
    exact zl2_of_simple_Ln (Or.inr rfl) e₀ hSN hsyl

end CFSG.Quasithin
