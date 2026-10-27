module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGTWModel
public import CFSG.LocalAnalysis.StandardType.GGTWPat2
public import CFSG.LocalAnalysis.StandardType.GGTWPat1
public import CFSG.LocalAnalysis.StandardType.GGTWKillXfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nS2_refl_apply {p N : ℕ} (c f w : GGTWE p N) :
    ggTWRefl c f w = w - ggTWdot f w • c := by
  simp [ggTWRefl, ggDepARefl, ggDepAform, ggTWdot, ggDepAdot, LinearMap.smulRight_apply,
    smul_eq_mul]

private lemma l05nS2_dot_of_comp_symm {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (φ : Module.Dual (ZMod p) V) (θ : V ≃ₗ[ZMod p] GGTWE p N) :
    ∃ a : GGTWE p N, ∀ v : GGTWE p N, ggTWdot a v = φ (θ.symm v) := by
  classical
  refine ⟨fun i => φ (θ.symm.toLinearMap (fun j => if i = j then (1 : ZMod p) else 0)), ?_⟩
  intro v
  have hlin := LinearMap.pi_apply_eq_sum_univ (φ.comp θ.symm.toLinearMap) v
  have hcomp : φ (θ.symm v) = (φ.comp θ.symm.toLinearMap) v := rfl
  rw [hcomp, hlin]
  simp only [ggTWdot, ggDepAdot, LinearMap.comp_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

private lemma l05nS2_cartanA_mem (n : ℕ) (i j : Fin n) :
    CartanMatrix.A n i j = 2 ∨ CartanMatrix.A n i j = 0 ∨ CartanMatrix.A n i j = -1 := by
  by_cases hij : i = j
  · subst hij; exact Or.inl (by simp [CartanMatrix.A])
  · simp only [CartanMatrix.A, Matrix.of_apply, hij, ite_false]
    split_ifs <;> omega

private lemma l05nS2_cartanA_eq_two {n : ℕ} {i j : Fin n}
    (h : CartanMatrix.A n i j = 2) : i = j := by
  by_contra hij
  simp only [CartanMatrix.A, Matrix.of_apply, hij, ite_false] at h
  split_ifs at h <;> omega

private lemma l05nS2_reindex_trans {Γ Γ' Γ'' : Type*} (M : CoxeterMatrix Γ) (e : Γ ≃ Γ')
    (e' : Γ' ≃ Γ'') : (M.reindex e).reindex e' = M.reindex (e.trans e') := by
  ext a b
  simp [CoxeterMatrix.reindex_apply, Equiv.trans_apply]

private lemma l05nS2_intCartan_reindex {Γ Γ' : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) (ee : Γ' ≃ Γ) :
    GGIntCartan (M.reindex ee.symm) (C.submatrix ee ee) := by
  constructor
  · intro i
    simpa [Matrix.submatrix_apply] using hC.1 (ee i)
  · intro i j hij
    have hne : ee i ≠ ee j := fun h => hij (ee.injective h)
    simpa [CoxeterMatrix.reindex_apply, Matrix.submatrix_apply] using hC.2 (ee i) (ee j) hne

private theorem l05nS2_ggHLRoots_congr {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {Λ Λ' : Type} {r : Λ → V ≃ₗ[ZMod p] V} {r' : Λ' → V ≃ₗ[ZMod p] V}
    {h : Λ → V} {h' : Λ' → V} (hr : Set.range r = Set.range r')
    (hh : Set.range h = Set.range h') :
    ggHLRoots r h = ggHLRoots r' h' := by
  ext v
  constructor
  · rintro ⟨w, hw, i, rfl⟩
    refine ⟨w, ?_, ?_⟩
    · rwa [← hr]
    · obtain ⟨i', hi'⟩ : h i ∈ Set.range h' := by rw [← hh]; exact ⟨i, rfl⟩
      exact ⟨i', by rw [← hi']⟩
  · rintro ⟨w, hw, i', rfl⟩
    refine ⟨w, ?_, ?_⟩
    · rwa [hr]
    · obtain ⟨i, hi⟩ : h' i' ∈ Set.range h := by rw [hh]; exact ⟨i', rfl⟩
      exact ⟨i, by rw [← hi]⟩

private lemma l05nS2_two_ne_zero {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) :
    ((2 : ℤ) : ZMod p) ≠ 0 := by
  intro h
  have hdvd : (p : ℤ) ∣ (2 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp h
  have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
  have h3 : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  omega

theorem ggTWSurv2_cell {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hpN : p ∣ N)
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10)
    {pos : GGTWPos} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type} [Fintype Λa]
    [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)
      ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    {e : Fin (N - 1) ≃ Λ} {r : Λ ⊕ Λa → V ≃ₗ[ZMod p] V} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod p) V} {xV yV : V}
    (hb12 : b₁ ≠ b₂) (hcard : Nat.card Λa = 2)
    (hJiff : ∀ i : Fin (N - 1), ggTWInJ N pos i.val ↔ (e i ≠ b₁ ∧ e i ≠ b₂))
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hA2 : ∃ eK : Fin (N - 1) ≃ ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa),
      MK = (CoxeterMatrix.A (N - 1)).reindex eK)
    (hr : ∀ o w, r o w = w - α o w • h o)
    (hF : GGDepAFrame p N (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV)
    (hdim : Module.finrank (ZMod p) V = N - 1)
    (hpairK : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hHL : ∀ g ∈ Subgroup.closure (Set.range r), GGLinRefl g → g xV = xV →
      GGHLLines (ggHLRoots (fun i : Λ => r (Sum.inl i)) (fun i : Λ => h (Sum.inl i))) xV g)
    (hax : ∃ a : Λa, α (Sum.inr a) xV ≠ 0) (hyV : yV ≠ 0)
    (hfixJ : ∀ i : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, r (Sum.inl i.1) yV = yV)
    (hfixa : ∀ a : Λa, r (Sum.inr a) yV = yV) :
    ∃ (θ : V ≃ₗ[ZMod p] GGTWE p N) (a₁ a₂ : Λa) (c : Fin (N - 1))
      (c₂ : Option (Fin (N - 1)))
      (ha1 αa1 ha2 αa2 : GGTWE p N) (lam mu : ZMod p)
      (news : Set (GGTWE p N × GGTWE p N))
      (rN : GGTWE p N × GGTWE p N → V ≃ₗ[ZMod p] V),
      θ xV = ggTWx p N ∧
      ha1 = θ (h (Sum.inr a₁)) ∧
      ha2 = θ (h (Sum.inr a₂)) ∧
      a₁ ≠ a₂ ∧
      GGTWPat2 N pos c.val (c₂.map Fin.val) ∧
      GGTWPairs2 p N pos c c₂ ha1 αa1 ha2 αa2 ∧
      (ggTWdot αa1 (ggTWx p N) ≠ 0 ∨ ggTWdot αa2 (ggTWx p N) ≠ 0) ∧
      (lam ≠ 0 ∨ mu ≠ 0) ∧
      ggTWdot αa1 (lam • ggTWx p N + mu • ggTWz p N pos) = 0 ∧
      ggTWdot αa2 (lam • ggTWx p N + mu • ggTWz p N pos) = 0 ∧
      θ yV = lam • ggTWx p N + mu • ggTWz p N pos ∧
      news = {(ha1, αa1), (ha2, αa2)} ∧
      (∀ i v, θ (r (Sum.inl (e i)) v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v)) ∧
      (∀ t ∈ news, ∀ v, θ (rN t v) = ggTWRefl t.1 t.2 (θ v)) ∧
      (∀ v, θ (r (Sum.inr a₁) v) = ggTWRefl ha1 αa1 (θ v)) ∧
      (∀ v, θ (r (Sum.inr a₂) v) = ggTWRefl ha2 αa2 (θ v)) ∧
      Subgroup.closure (Set.range (fun i : Fin (N - 1) => r (Sum.inl (e i))) ∪ rN '' news) ≤
        Subgroup.closure (Set.range r) ∧
      (∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) => r (Sum.inl (e i))) ∪
          rN '' news),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
      (∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) => r (Sum.inl (e i))) ∪
          rN '' news),
        GGLinRefl g → g xV = xV →
          GGHLLines (ggHLRoots (fun i : Fin (N - 1) => r (Sum.inl (e i)))
            (fun i => θ.symm (ggTWh p N i))) xV g) ∧
      (ggHLRoots
          (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => r (Sum.inl (e i.1)))
            (fun t : ↥news => rN t.1))
          (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => θ.symm (ggTWh p N i.1))
            (fun t : ↥news => θ.symm t.1.1)) =
        ggHLRoots (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => r (o.map Subtype.val id))
          (fun o => h (o.map Subtype.val id))) ∧
      ¬ GGTWKill .frame p N pos news (lam • ggTWx p N + mu • ggTWz p N pos) := by
  classical
  have hN5 : 5 ≤ N := by omega
  obtain ⟨θ, hθx, hθh, hθα⟩ := ggTW_model_iso (p := p) (N := N) hN5 hdim hF
  obtain ⟨eK, heK⟩ := hA2
  let eJ : {c : Fin (N - 1) // ggTWInJ N pos c.val} ≃ {i : Λ // i ≠ b₁ ∧ i ≠ b₂} :=
    { toFun := fun c => ⟨e c.1, (hJiff c.1).mp c.2⟩
      invFun := fun i => ⟨e.symm i.1, (hJiff (e.symm i.1)).mpr (by simpa using i.2)⟩
      left_inv := by intro c; apply Subtype.ext; simp
      right_inv := by intro i; apply Subtype.ext; simp }
  let ee : ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) ≃
      ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) := Equiv.sumCongr eJ (Equiv.refl Λa)
  let MK' : CoxeterMatrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) :=
    MK.reindex ee.symm
  let CK' : Matrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)
      ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) ℤ := CK.submatrix ee ee
  have hMK' : MK' = (CoxeterMatrix.A (N - 1)).reindex (eK.trans ee.symm) := by
    show MK.reindex ee.symm = _
    rw [heK]
    exact l05nS2_reindex_trans (CoxeterMatrix.A (N - 1)) eK ee.symm
  have hWK' : GGIsWeylMatrix MK' :=
    Or.inl ⟨N - 1, eK.trans ee.symm, by omega, Or.inl hMK'⟩
  have hCK' : GGIntCartan MK' CK' := l05nS2_intCartan_reindex hCK ee
  have hcast : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      ((CK' (Sum.inl i) (Sum.inl j) : ℤ) : ZMod p) =
        ((CartanMatrix.A (N - 1) i.1 j.1 : ℤ) : ZMod p) := by
    intro i j
    have h1 := hpairK (Sum.inl (eJ i)) (Sum.inl (eJ j))
    simp only [Sum.map_inl, id_eq] at h1
    have h2 := hF.pair i.1 j.1
    have hval : CK' (Sum.inl i) (Sum.inl j) = CK (Sum.inl (eJ i)) (Sum.inl (eJ j)) := by
      simp [CK', ee, Matrix.submatrix_apply]
    rw [hval, ← h1]
    rw [show (eJ i).val = e i.1 from rfl, show (eJ j).val = e j.1 from rfl]
    exact h2
  have hJ' : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      CK' (Sum.inl i) (Sum.inl j) = CartanMatrix.A (N - 1) i.1 j.1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [hCK'.1 (Sum.inl i)]
      simp [CartanMatrix.A]
    · have hne : Sum.inl i ≠
          (Sum.inl j : ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)) :=
        fun h => hij (by injection h)
      have hpair : (CK' (Sum.inl i) (Sum.inl j) = 0 ∧ CK' (Sum.inl j) (Sum.inl i) = 0) ∨
          (CK' (Sum.inl i) (Sum.inl j) = -1 ∧ CK' (Sum.inl j) (Sum.inl i) = -1) ∨
          (CK' (Sum.inl i) (Sum.inl j) * CK' (Sum.inl j) (Sum.inl i) = 2 ∧
            CK' (Sum.inl i) (Sum.inl j) < 0 ∧ CK' (Sum.inl j) (Sum.inl i) < 0) ∨
          (CK' (Sum.inl i) (Sum.inl j) * CK' (Sum.inl j) (Sum.inl i) = 3 ∧
            CK' (Sum.inl i) (Sum.inl j) < 0 ∧ CK' (Sum.inl j) (Sum.inl i) < 0) := by
        rcases hCK'.2 (Sum.inl i) (Sum.inl j) hne with
          ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2, h3⟩ | ⟨-, h1, h2, h3⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))
      have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      have hb : CartanMatrix.A (N - 1) i.1 j.1 = 0 ∨
          CartanMatrix.A (N - 1) i.1 j.1 = -1 := by
        rcases l05nS2_cartanA_mem (N - 1) i.1 j.1 with h2 | h0 | hm1
        · exact absurd (l05nS2_cartanA_eq_two h2) hij'
        · exact Or.inl h0
        · exact Or.inr hm1
      have h1c := hcast i j
      have h2c : ((CK' (Sum.inl j) (Sum.inl i) : ℤ) : ZMod p) =
          ((CartanMatrix.A (N - 1) i.1 j.1 : ℤ) : ZMod p) := by
        rw [hcast j i, CFSG.ClassicalInvolution.ModelFacts.cartanA_symm (N - 1) j.1 i.1]
      exact (ggTW_cast_cartan_pair hp hpair hb h1c h2c).1
  obtain ⟨a₁, a₂, c, c₂, ha12, hpat2, hpair2, hp12, hp21, hp11, hp22⟩ :=
    ggTW_pattern2 hN5 pos hcard hWK' hCK' ⟨eK.trans ee.symm, hMK'⟩ hJ'
  set ha1 : GGTWE p N := θ (h (Sum.inr a₁)) with ha1_def
  set ha2 : GGTWE p N := θ (h (Sum.inr a₂)) with ha2_def
  obtain ⟨αa1, hαa1⟩ := l05nS2_dot_of_comp_symm (α (Sum.inr a₁)) θ
  obtain ⟨αa2, hαa2⟩ := l05nS2_dot_of_comp_symm (α (Sum.inr a₂)) θ
  have hh_ne : ∀ c : Fin (N - 1), ggTWInJ N pos c.val → h (Sum.inl (e c)) ≠ 0 := by
    intro c _ hzero
    have hp2 := l05nS2_two_ne_zero hp
    have hpair := hF.pair c c
    rw [hzero, map_zero] at hpair
    have hA : CartanMatrix.A (N - 1) c c = 2 := by simp [CartanMatrix.A]
    rw [hA] at hpair
    exact hp2 (by simpa using hpair.symm)
  have ha_ne : ∀ a : Λa, h (Sum.inr a) ≠ 0 := by
    intro a hzero
    have hp2 := l05nS2_two_ne_zero hp
    have hpair := hpairK (Sum.inr a) (Sum.inr a)
    simp only [Sum.map_inr, id_eq] at hpair
    rw [hzero, map_zero, hCK.1 (Sum.inr a)] at hpair
    exact hp2 (by simpa using hpair.symm)
  have hpair_main : ∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
      ggTWdot αa1 (ggTWh p N c') = (if c' = c then -1 else 0) ∧
        ggTWdot (ggTWα p N c') ha1 = (if c' = c then -1 else 0) ∧
        ggTWdot αa2 (ggTWh p N c') = (if some c' = c₂ then -1 else 0) ∧
        ggTWdot (ggTWα p N c') ha2 = (if some c' = c₂ then -1 else 0) := by
    intro c' hc'
    have hsymm : θ.symm (ggTWh p N c') = h (Sum.inl (e c')) := by
      rw [← hθh c']; exact LinearEquiv.symm_apply_apply θ _
    have hsymmα : ∀ v, ggTWdot (ggTWα p N c') (θ v) = α (Sum.inl (e c')) v :=
      fun v => (hθα c' v).symm
    have hne' : e c' ≠ b₁ ∧ e c' ≠ b₂ := (hJiff c').mp hc'
    have hdot1 : ggTWdot αa1 (ggTWh p N c') =
        (CK' (Sum.inr a₁) (Sum.inl ⟨c', hc'⟩) : ZMod p) := by
      rw [hαa1 (ggTWh p N c'), hsymm]
      rw [show CK' (Sum.inr a₁) (Sum.inl ⟨c', hc'⟩) =
          CK (Sum.inr a₁) (Sum.inl ⟨e c', hne'⟩) by simp [CK', ee, eJ, Matrix.submatrix_apply]]
      simpa only [Sum.map_inr, Sum.map_inl, Subtype.coe_mk, id_eq] using
        hpairK (Sum.inr a₁) (Sum.inl ⟨e c', hne'⟩)
    have hdot2 : ggTWdot (ggTWα p N c') ha1 =
        (CK' (Sum.inl ⟨c', hc'⟩) (Sum.inr a₁) : ZMod p) := by
      change ggTWdot (ggTWα p N c') (θ (h (Sum.inr a₁))) = _
      rw [hsymmα (h (Sum.inr a₁))]
      rw [show CK' (Sum.inl ⟨c', hc'⟩) (Sum.inr a₁) =
          CK (Sum.inl ⟨e c', hne'⟩) (Sum.inr a₁) by simp [CK', ee, eJ, Matrix.submatrix_apply]]
      simpa only [Sum.map_inl, Sum.map_inr, Subtype.coe_mk, id_eq] using
        hpairK (Sum.inl ⟨e c', hne'⟩) (Sum.inr a₁)
    have hdot3 : ggTWdot αa2 (ggTWh p N c') =
        (CK' (Sum.inr a₂) (Sum.inl ⟨c', hc'⟩) : ZMod p) := by
      rw [hαa2 (ggTWh p N c'), hsymm]
      rw [show CK' (Sum.inr a₂) (Sum.inl ⟨c', hc'⟩) =
          CK (Sum.inr a₂) (Sum.inl ⟨e c', hne'⟩) by simp [CK', ee, eJ, Matrix.submatrix_apply]]
      simpa only [Sum.map_inr, Sum.map_inl, Subtype.coe_mk, id_eq] using
        hpairK (Sum.inr a₂) (Sum.inl ⟨e c', hne'⟩)
    have hdot4 : ggTWdot (ggTWα p N c') ha2 =
        (CK' (Sum.inl ⟨c', hc'⟩) (Sum.inr a₂) : ZMod p) := by
      change ggTWdot (ggTWα p N c') (θ (h (Sum.inr a₂))) = _
      rw [hsymmα (h (Sum.inr a₂))]
      rw [show CK' (Sum.inl ⟨c', hc'⟩) (Sum.inr a₂) =
          CK (Sum.inl ⟨e c', hne'⟩) (Sum.inr a₂) by simp [CK', ee, eJ, Matrix.submatrix_apply]]
      simpa only [Sum.map_inl, Sum.map_inr, Subtype.coe_mk, id_eq] using
        hpairK (Sum.inl ⟨e c', hne'⟩) (Sum.inr a₂)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hdot1, (hpair2 ⟨c', hc'⟩).1]; simp
    · rw [hdot2, (hpair2 ⟨c', hc'⟩).2.1]; simp
    · rw [hdot3, (hpair2 ⟨c', hc'⟩).2.2.1]; simp
    · rw [hdot4, (hpair2 ⟨c', hc'⟩).2.2.2]; simp
  have hpair : GGTWPairs2 p N pos c c₂ ha1 αa1 ha2 αa2 := by
    refine ⟨hpair_main, ?_, ?_, ?_, ?_⟩
    · have h : ggTWdot αa1 ha2 = (CK' (Sum.inr a₁) (Sum.inr a₂) : ZMod p) := by
        change ggTWdot αa1 (θ (h (Sum.inr a₂))) = _
        rw [hαa1 (θ (h (Sum.inr a₂)))]
        change α (Sum.inr a₁) (θ.symm (θ (h (Sum.inr a₂)))) = _
        rw [LinearEquiv.symm_apply_apply]
        rw [show CK' (Sum.inr a₁) (Sum.inr a₂) = CK (Sum.inr a₁) (Sum.inr a₂) by
          simp [CK', ee, Matrix.submatrix_apply]]
        simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr a₁) (Sum.inr a₂)
      rw [h, hp12]; simp
    · have h : ggTWdot αa2 ha1 = (CK' (Sum.inr a₂) (Sum.inr a₁) : ZMod p) := by
        change ggTWdot αa2 (θ (h (Sum.inr a₁))) = _
        rw [hαa2 (θ (h (Sum.inr a₁)))]
        change α (Sum.inr a₂) (θ.symm (θ (h (Sum.inr a₁)))) = _
        rw [LinearEquiv.symm_apply_apply]
        rw [show CK' (Sum.inr a₂) (Sum.inr a₁) = CK (Sum.inr a₂) (Sum.inr a₁) by
          simp [CK', ee, Matrix.submatrix_apply]]
        simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr a₂) (Sum.inr a₁)
      rw [h, hp21]; simp
    · have h : ggTWdot αa1 ha1 = (CK' (Sum.inr a₁) (Sum.inr a₁) : ZMod p) := by
        change ggTWdot αa1 (θ (h (Sum.inr a₁))) = _
        rw [hαa1 (θ (h (Sum.inr a₁)))]
        change α (Sum.inr a₁) (θ.symm (θ (h (Sum.inr a₁)))) = _
        rw [LinearEquiv.symm_apply_apply]
        rw [show CK' (Sum.inr a₁) (Sum.inr a₁) = CK (Sum.inr a₁) (Sum.inr a₁) by
          simp [CK', ee, Matrix.submatrix_apply]]
        simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr a₁) (Sum.inr a₁)
      rw [h, hp11]; norm_num
    · have h : ggTWdot αa2 ha2 = (CK' (Sum.inr a₂) (Sum.inr a₂) : ZMod p) := by
        change ggTWdot αa2 (θ (h (Sum.inr a₂))) = _
        rw [hαa2 (θ (h (Sum.inr a₂)))]
        change α (Sum.inr a₂) (θ.symm (θ (h (Sum.inr a₂)))) = _
        rw [LinearEquiv.symm_apply_apply]
        rw [show CK' (Sum.inr a₂) (Sum.inr a₂) = CK (Sum.inr a₂) (Sum.inr a₂) by
          simp [CK', ee, Matrix.submatrix_apply]]
        simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr a₂) (Sum.inr a₂)
      rw [h, hp22]; norm_num
  have hxne : ggTWdot αa1 (ggTWx p N) ≠ 0 ∨ ggTWdot αa2 (ggTWx p N) ≠ 0 := by
    obtain ⟨a₀, ha₀⟩ := hax
    have hmem : a₀ = a₁ ∨ a₀ = a₂ := by
      have hcard2 : ({a₁, a₂} : Finset Λa).card = Fintype.card Λa := by
        rw [Finset.card_pair ha12, ← Nat.card_eq_fintype_card, hcard]
      have htop : ({a₁, a₂} : Finset Λa) = Finset.univ := Finset.eq_univ_of_card _ hcard2
      have : a₀ ∈ ({a₁, a₂} : Finset Λa) := by rw [htop]; exact Finset.mem_univ a₀
      simpa using this
    have hxV : θ.symm (ggTWx p N) = xV := by
      rw [← hθx]; exact LinearEquiv.symm_apply_apply θ _
    rcases hmem with h | h
    · left
      intro h0
      apply ha₀
      rw [h, ← hxV, ← hαa1 (ggTWx p N), h0]
    · right
      intro h0
      apply ha₀
      rw [h, ← hxV, ← hαa2 (ggTWx p N), h0]
  have hfixθ : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggTWdot (ggTWα p N c) (θ yV) = 0 := by
    intro c hc
    have hne : e c ≠ b₁ ∧ e c ≠ b₂ := (hJiff c).mp hc
    have hfix := hfixJ ⟨e c, hne⟩
    have h0 : α (Sum.inl (e c)) yV • h (Sum.inl (e c)) = 0 := by
      have h1 : yV - α (Sum.inl (e c)) yV • h (Sum.inl (e c)) = yV := by
        rw [← hr (Sum.inl (e c)) yV, hfix]
      have h2 : yV - α (Sum.inl (e c)) yV • h (Sum.inl (e c)) - yV = 0 := by
        rw [h1, sub_self]
      simpa using h2
    have hα0 : α (Sum.inl (e c)) yV = 0 := by
      rcases smul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (hh_ne c hc)
    rw [← hθα c yV]
    exact hα0
  obtain ⟨lam, mu, hy_eq⟩ := ggTW_fixedJ hpN hN5 pos (θ yV) hfixθ
  have hy_ne : lam • ggTWx p N + mu • ggTWz p N pos ≠ 0 := by
    intro hzero
    have h1 : θ yV = 0 := by rw [hy_eq, hzero]
    have h2 : yV = 0 := θ.injective (by rw [h1, map_zero])
    exact hyV h2
  have hlam : lam ≠ 0 ∨ mu ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact hy_ne (by rw [h.1, h.2, zero_smul, zero_smul, add_zero])
  have hfixa1 : ggTWdot αa1 (lam • ggTWx p N + mu • ggTWz p N pos) = 0 := by
    have h1 : ggTWdot αa1 (θ yV) = α (Sum.inr a₁) yV := by
      rw [hαa1 (θ yV)]; simp
    have h2 : α (Sum.inr a₁) yV = 0 := by
      have hfix := hfixa a₁
      have h0 : α (Sum.inr a₁) yV • h (Sum.inr a₁) = 0 := by
        have h3 : yV - α (Sum.inr a₁) yV • h (Sum.inr a₁) = yV := by
          rw [← hr (Sum.inr a₁) yV, hfix]
        have h4 : yV - α (Sum.inr a₁) yV • h (Sum.inr a₁) - yV = 0 := by
          rw [h3, sub_self]
        simpa using h4
      rcases smul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (ha_ne a₁)
    rw [← hy_eq, h1, h2]
  have hfixa2 : ggTWdot αa2 (lam • ggTWx p N + mu • ggTWz p N pos) = 0 := by
    have h1 : ggTWdot αa2 (θ yV) = α (Sum.inr a₂) yV := by
      rw [hαa2 (θ yV)]; simp
    have h2 : α (Sum.inr a₂) yV = 0 := by
      have hfix := hfixa a₂
      have h0 : α (Sum.inr a₂) yV • h (Sum.inr a₂) = 0 := by
        have h3 : yV - α (Sum.inr a₂) yV • h (Sum.inr a₂) = yV := by
          rw [← hr (Sum.inr a₂) yV, hfix]
        have h4 : yV - α (Sum.inr a₂) yV • h (Sum.inr a₂) - yV = 0 := by
          rw [h3, sub_self]
        simpa using h4
      rcases smul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (ha_ne a₂)
    rw [← hy_eq, h1, h2]
  have hrefl1 : ∀ v, θ (r (Sum.inr a₁) v) = ggTWRefl ha1 αa1 (θ v) := by
    intro v
    have h2 : α (Sum.inr a₁) v = ggTWdot αa1 (θ v) := by
      rw [hαa1 (θ v)]; simp
    rw [hr (Sum.inr a₁) v, map_sub, map_smul, h2, ← ha1_def]
    exact (l05nS2_refl_apply ha1 αa1 (θ v)).symm
  have hrefl2 : ∀ v, θ (r (Sum.inr a₂) v) = ggTWRefl ha2 αa2 (θ v) := by
    intro v
    have h2 : α (Sum.inr a₂) v = ggTWdot αa2 (θ v) := by
      rw [hαa2 (θ v)]; simp
    rw [hr (Sum.inr a₂) v, map_sub, map_smul, h2, ← ha2_def]
    exact (l05nS2_refl_apply ha2 αa2 (θ v)).symm
  let rF : Fin (N - 1) → V ≃ₗ[ZMod p] V := fun i => r (Sum.inl (e i))
  let news : Set (GGTWE p N × GGTWE p N) := {(ha1, αa1), (ha2, αa2)}
  let rN : GGTWE p N × GGTWE p N → V ≃ₗ[ZMod p] V := fun t =>
    if t = (ha1, αa1) then r (Sum.inr a₁)
    else if t = (ha2, αa2) then r (Sum.inr a₂) else 1
  have hrF : ∀ i v, θ (rF i v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v) := by
    intro i v
    have h2 : α (Sum.inl (e i)) v = ggTWdot (ggTWα p N i) (θ v) := hθα i v
    change θ (r (Sum.inl (e i)) v) = _
    rw [hr (Sum.inl (e i)) v, map_sub, map_smul, h2, hθh i]
    exact (l05nS2_refl_apply (ggTWh p N i) (ggTWα p N i) (θ v)).symm
  have hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggTWRefl t.1 t.2 (θ v) := by
    intro t ht v
    simp only [news, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · have h : rN (ha1, αa1) = r (Sum.inr a₁) := by simp [rN]
      rw [h]; exact hrefl1 v
    · by_cases h : (ha2, αa2) = (ha1, αa1)
      · have h' : rN (ha2, αa2) = r (Sum.inr a₁) := by simp [rN, h]
        rw [h', h]; exact hrefl1 v
      · have h' : rN (ha2, αa2) = r (Sum.inr a₂) := by simp [rN, h]
        rw [h']; exact hrefl2 v
  have hrangeF : Set.range rF ⊆ Set.range r := by
    rintro g ⟨i, rfl⟩
    exact ⟨Sum.inl (e i), rfl⟩
  have hrangeN : rN '' news ⊆ Set.range r := by
    rintro g ⟨t, ht, rfl⟩
    simp only [news, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact ⟨Sum.inr a₁, by simp [rN]⟩
    · by_cases h : (ha2, αa2) = (ha1, αa1)
      · exact ⟨Sum.inr a₁, by simp [rN, h]⟩
      · exact ⟨Sum.inr a₂, by simp [rN, h]⟩
  have hsub : Subgroup.closure (Set.range rF ∪ rN '' news) ≤ Subgroup.closure (Set.range r) :=
    Subgroup.closure_mono (by
      intro g hg
      rcases hg with hg | hg
      · exact hrangeF hg
      · exact hrangeN hg)
  have hnt' : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
    fun g hg => hnt g (hsub hg)
  have hroots : ggHLRoots rF (fun i : Fin (N - 1) => θ.symm (ggTWh p N i)) =
      ggHLRoots (fun i : Λ => r (Sum.inl i)) (fun i : Λ => h (Sum.inl i)) := by
    have hfun : (fun i : Fin (N - 1) => θ.symm (ggTWh p N i)) =
        (fun i => h (Sum.inl (e i))) := by
      funext i
      rw [← hθh i]
      exact LinearEquiv.symm_apply_apply θ _
    rw [hfun]
    apply l05nS2_ggHLRoots_congr
    · ext g; constructor
      · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
      · rintro ⟨l, rfl⟩; exact ⟨e.symm l, by simp [rF]⟩
    · ext g; constructor
      · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
      · rintro ⟨l, rfl⟩; exact ⟨e.symm l, by simp⟩
  have hHL' : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news), GGLinRefl g → g xV = xV →
      GGHLLines (ggHLRoots rF (fun i => θ.symm (ggTWh p N i))) xV g := by
    intro g hg hgr hgx
    rw [hroots]
    exact hHL g (hsub hg) hgr hgx
  have hkill : ¬ GGTWKill .frame p N pos news (lam • ggTWx p N + mu • ggTWz p N pos) :=
    ggTW_notKill_frame (p := p) (N := N) (by omega) θ hθx rF hrF news rN hrN hnt' hHL' pos
      (lam • ggTWx p N + mu • ggTWz p N pos)
  have hnews : news = {(ha1, αa1), (ha2, αa2)} := rfl
  have hmem : ∀ a : Λa, a = a₁ ∨ a = a₂ := by
    have hcard2 : ({a₁, a₂} : Finset Λa).card = Fintype.card Λa := by
      rw [Finset.card_pair ha12, ← Nat.card_eq_fintype_card, hcard]
    have htop : ({a₁, a₂} : Finset Λa) = Finset.univ := Finset.eq_univ_of_card _ hcard2
    intro a
    have : a ∈ ({a₁, a₂} : Finset Λa) := by rw [htop]; exact Finset.mem_univ a
    simpa using this
  let rO : ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ ↥news) → V ≃ₗ[ZMod p] V :=
    Sum.elim (fun i => rF i.1) (fun t => rN t.1)
  let hO : ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ ↥news) → V :=
    Sum.elim (fun i => θ.symm (ggTWh p N i.1)) (fun t => θ.symm t.1.1)
  let rK : ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) → V ≃ₗ[ZMod p] V :=
    fun o => r (o.map Subtype.val id)
  let hK : ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) → V := fun o => h (o.map Subtype.val id)
  have hrO : Set.range rO = Set.range rK := by
    ext x; constructor
    · rintro ⟨s, rfl⟩
      cases s with
      | inl c => exact ⟨Sum.inl ⟨e c.1, (hJiff c.1).mp c.2⟩, rfl⟩
      | inr t =>
          have ht : t.1 = (ha1, αa1) ∨ t.1 = (ha2, αa2) := by
            simpa only [news, Set.mem_insert_iff, Set.mem_singleton_iff] using t.2
          rcases ht with hh | hh
          · refine ⟨Sum.inr a₁, ?_⟩
            show r (Sum.inr a₁) = rN t.1
            rw [hh]; simp [rN]
          · by_cases hc : (ha2, αa2) = (ha1, αa1)
            · refine ⟨Sum.inr a₁, ?_⟩
              show r (Sum.inr a₁) = rN t.1
              rw [hh]; simp [rN, hc]
            · refine ⟨Sum.inr a₂, ?_⟩
              show r (Sum.inr a₂) = rN t.1
              rw [hh]; simp [rN, hc]
    · rintro ⟨o, rfl⟩
      cases o with
      | inl i =>
          refine ⟨Sum.inl ⟨e.symm i.1, (hJiff (e.symm i.1)).mpr ?_⟩, ?_⟩
          · rw [Equiv.apply_symm_apply]; exact i.2
          · show r (Sum.inl (e (e.symm i.1))) = r (Sum.inl i.1)
            rw [Equiv.apply_symm_apply]
      | inr a =>
          rcases hmem a with ha | ha
          · rw [ha]
            refine ⟨Sum.inr ⟨(ha1, αa1), by simp [news]⟩, ?_⟩
            show rN (ha1, αa1) = r (Sum.inr a₁)
            simp [rN]
          · rw [ha]
            by_cases hc : (ha2, αa2) = (ha1, αa1)
            · have hha : h (Sum.inr a₂) = h (Sum.inr a₁) := by
                apply θ.injective
                rw [← ha2_def, ← ha1_def]
                exact congrArg Prod.fst hc
              have hα : ∀ v, α (Sum.inr a₂) v = α (Sum.inr a₁) v := by
                intro v
                have h2 : (α (Sum.inr a₂)) v = ggTWdot αa2 (θ v) := by
                  rw [hαa2 (θ v), LinearEquiv.symm_apply_apply]
                have h1 : (α (Sum.inr a₁)) v = ggTWdot αa1 (θ v) := by
                  rw [hαa1 (θ v), LinearEquiv.symm_apply_apply]
                rw [h2, h1, show αa2 = αa1 from congrArg Prod.snd hc]
              have hr_eq : r (Sum.inr a₂) = r (Sum.inr a₁) := by
                ext v
                rw [hr (Sum.inr a₂) v, hr (Sum.inr a₁) v, hha, hα v]
              refine ⟨Sum.inr ⟨(ha1, αa1), by simp [news]⟩, ?_⟩
              show rN (ha1, αa1) = r (Sum.inr a₂)
              rw [hr_eq]; simp [rN]
            · refine ⟨Sum.inr ⟨(ha2, αa2), by simp [news]⟩, ?_⟩
              show rN (ha2, αa2) = r (Sum.inr a₂)
              simp [rN, hc]
  have hhO : Set.range hO = Set.range hK := by
    ext x; constructor
    · rintro ⟨s, rfl⟩
      cases s with
      | inl c =>
          refine ⟨Sum.inl ⟨e c.1, (hJiff c.1).mp c.2⟩, ?_⟩
          show h (Sum.inl (e c.1)) = θ.symm (ggTWh p N c.1)
          rw [← hθh c.1, LinearEquiv.symm_apply_apply]
      | inr t =>
          have ht : t.1 = (ha1, αa1) ∨ t.1 = (ha2, αa2) := by
            simpa only [news, Set.mem_insert_iff, Set.mem_singleton_iff] using t.2
          rcases ht with hh | hh
          · refine ⟨Sum.inr a₁, ?_⟩
            show h (Sum.inr a₁) = θ.symm t.1.1
            rw [hh]
            rw [show ha1 = θ (h (Sum.inr a₁)) from ha1_def, LinearEquiv.symm_apply_apply]
          · refine ⟨Sum.inr a₂, ?_⟩
            show h (Sum.inr a₂) = θ.symm t.1.1
            rw [hh]
            rw [show ha2 = θ (h (Sum.inr a₂)) from ha2_def, LinearEquiv.symm_apply_apply]
    · rintro ⟨o, rfl⟩
      cases o with
      | inl i =>
          refine ⟨Sum.inl ⟨e.symm i.1, (hJiff (e.symm i.1)).mpr ?_⟩, ?_⟩
          · rw [Equiv.apply_symm_apply]; exact i.2
          · show θ.symm (ggTWh p N (e.symm i.1)) = h (Sum.inl i.1)
            rw [← hθh (e.symm i.1), Equiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      | inr a =>
          rcases hmem a with ha | ha
          · rw [ha]
            refine ⟨Sum.inr ⟨(ha1, αa1), by simp [news]⟩, ?_⟩
            show θ.symm ha1 = h (Sum.inr a₁)
            rw [show ha1 = θ (h (Sum.inr a₁)) from ha1_def, LinearEquiv.symm_apply_apply]
          · rw [ha]
            refine ⟨Sum.inr ⟨(ha2, αa2), by simp [news]⟩, ?_⟩
            show θ.symm ha2 = h (Sum.inr a₂)
            rw [show ha2 = θ (h (Sum.inr a₂)) from ha2_def, LinearEquiv.symm_apply_apply]
  have hrootsO : ggHLRoots rO hO = ggHLRoots rK hK := l05nS2_ggHLRoots_congr hrO hhO
  refine ⟨θ, a₁, a₂, c, c₂, ha1, αa1, ha2, αa2, lam, mu, news, rN,
    hθx, ha1_def, ha2_def, ha12, hpat2, hpair, hxne, hlam, hfixa1, hfixa2, hy_eq, rfl,
    hrF, hrN, hrefl1, hrefl2, hsub, hnt', hHL', hrootsO, hkill⟩

theorem ggTWSurv2_of_vcfg {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hpN : p ∣ N)
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) (hv : GGTWVCfg p N 2) : GGTWSurv2 .frame p N := by
  classical
  unfold GGTWVCfg at hv
  obtain ⟨pos, V, instV, instMV, Λ, instΛ, instΛd, b₁, b₂, Λa, instΛa, instΛad, MK, CK, e, r, h,
    α, xV, yV, hb12, hcard, hJiff, hWK, hCK, hA2, hr, hF, hdim, hpairK, hnt, hHL, hax, hyV,
    hfixJ, hfixa⟩ := hv
  letI : AddCommGroup V := instV
  letI : Module (ZMod p) V := instMV
  letI : Fintype Λ := instΛ
  letI : DecidableEq Λ := instΛd
  letI : Fintype Λa := instΛa
  letI : DecidableEq Λa := instΛad
  obtain ⟨eK, heK⟩ := hA2 rfl
  obtain ⟨θ, a₁, a₂, c, c₂, ha1, αa1, ha2, αa2, lam, mu, news, rN, _hθx, _ha1, _ha2, _ha12,
    hpat2, hpair, hxne, hlam, hfixa1, hfixa2, _hy, hnews, _hrF, _hrN, _hrefl1, _hrefl2, _hsub,
    _hnt', _hHL', _hrootsO, hkill⟩ :=
    ggTWSurv2_cell (p := p) (N := N) (pos := pos) hp hpN hN hb12 hcard hJiff hWK hCK ⟨eK, heK⟩
      hr hF hdim hpairK hnt hHL hax hyV hfixJ hfixa
  exact ⟨pos, c, c₂, ha1, αa1, ha2, αa2, lam, mu, hpat2, hpair, hxne, hlam, hfixa1, hfixa2,
    by simpa [hnews] using hkill⟩

end CFSG.StandardType
