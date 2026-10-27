module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGTWModel
public import CFSG.LocalAnalysis.StandardType.GGTWPat1
public import CFSG.LocalAnalysis.StandardType.GGTWKillXfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nS1_refl_apply {p N : ℕ} (c f w : GGTWE p N) :
    ggTWRefl c f w = w - ggTWdot f w • c := by
  simp [ggTWRefl, ggDepARefl, ggDepAform, ggTWdot, ggDepAdot, LinearMap.smulRight_apply,
    smul_eq_mul]

private lemma l05nS1_dot_of_comp_symm {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (αa : Module.Dual (ZMod p) V) (θ : V ≃ₗ[ZMod p] GGTWE p N) :
    ∃ αa' : GGTWE p N, ∀ v : GGTWE p N, ggTWdot αa' v = αa (θ.symm v) := by
  classical
  refine ⟨fun i => αa (θ.symm.toLinearMap (fun j => if i = j then (1 : ZMod p) else 0)), ?_⟩
  intro v
  have hlin := LinearMap.pi_apply_eq_sum_univ (αa.comp θ.symm.toLinearMap) v
  have hcomp : αa (θ.symm v) = (αa.comp θ.symm.toLinearMap) v := rfl
  rw [hcomp, hlin]
  simp only [ggTWdot, ggDepAdot, LinearMap.comp_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

private theorem l05nS1_reindex_trans {ι κ ν : Type} (M : CoxeterMatrix ι) (e : ι ≃ κ)
    (f : κ ≃ ν) : (M.reindex e).reindex f = M.reindex (e.trans f) := by
  apply CoxeterMatrix.ext
  funext x y
  simp only [CoxeterMatrix.reindex_apply, Equiv.trans_apply, Equiv.symm_trans_apply]

private theorem l05nS1_weyl_reindex {ι κ : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M)
    (f : ι ≃ κ) : GGIsWeylMatrix (M.reindex f) := by
  rcases h with ⟨n, e, hn, h | ⟨hn, h⟩ | ⟨hn, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩
  · exact Or.inl ⟨n, e.trans f, hn, Or.inl (by rw [h, l05nS1_reindex_trans])⟩
  · exact Or.inl ⟨n, e.trans f, by omega, Or.inr (Or.inl ⟨hn, by rw [h, l05nS1_reindex_trans]⟩)⟩
  · exact Or.inl ⟨n, e.trans f, by omega,
      Or.inr (Or.inr ⟨hn, by rw [h, l05nS1_reindex_trans]⟩)⟩
  · exact Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nS1_reindex_trans]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nS1_reindex_trans]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f,
      by rw [h, l05nS1_reindex_trans]⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f,
      by rw [h, l05nS1_reindex_trans]⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans f,
      by rw [h, l05nS1_reindex_trans]⟩))))

private theorem l05nS1_intCartan_reindex {Γ Δ : Type} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (h : GGIntCartan M C) (e : Δ ≃ Γ) :
    GGIntCartan (M.reindex e.symm) (fun o o' => C (e o) (e o')) := by
  constructor
  · intro o
    simpa using h.1 (e o)
  · intro o o' hne
    have hene : e o ≠ e o' := fun hh => hne (e.injective hh)
    have hh := h.2 (e o) (e o') hene
    simpa only [CoxeterMatrix.reindex_apply, Equiv.symm_symm] using hh

private lemma l05nS1_hlroots_reindex {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι κ : Type} (e : ι ≃ κ) (r : κ → V ≃ₗ[ZMod p] V) (h : κ → V) :
    ggHLRoots (fun i : ι => r (e i)) (fun i : ι => h (e i)) = ggHLRoots r h := by
  ext v
  constructor
  · rintro ⟨w, hw, i, rfl⟩
    exact ⟨w, by
      rw [show Set.range (fun i : ι => r (e i)) = Set.range r from
        Function.Surjective.range_comp e.surjective r] at hw
      exact hw, e i, rfl⟩
  · rintro ⟨w, hw, i, rfl⟩
    exact ⟨w, by
      rw [show Set.range (fun i : ι => r (e i)) = Set.range r from
        Function.Surjective.range_comp e.surjective r]
      exact hw, e.symm i, by simp⟩

private lemma l05nS1_two_ne_zero {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) :
    ((2 : ℤ) : ZMod p) ≠ 0 := by
  intro h
  have hdvd : (p : ℤ) ∣ (2 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp h
  have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
  have h5 : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  omega

theorem ggTWSurv1_cell {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hpN : p ∣ N)
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10)
    {pos : GGTWPos} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type} [Fintype Λa]
    [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)
      ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    {e : Fin (N - 1) ≃ Λ} {r : Λ ⊕ Λa → V ≃ₗ[ZMod p] V} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod p) V} {xV yV : V}
    (hb : b₁ ≠ b₂) (hcard : Nat.card Λa = 1)
    (hJpos : ∀ i : Fin (N - 1), ggTWInJ N pos i.val ↔ (e i ≠ b₁ ∧ e i ≠ b₂))
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hr : ∀ o w, r o w = w - α o w • h o)
    (hF : GGDepAFrame p N (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV)
    (hdim : Module.finrank (ZMod p) V = N - 1)
    (hpairK : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hHL : ∀ g ∈ Subgroup.closure (Set.range r), GGLinRefl g → g xV = xV →
      GGHLLines (ggHLRoots (fun i : Λ => r (Sum.inl i)) (fun i : Λ => h (Sum.inl i))) xV g)
    (hxa : ∃ a : Λa, α (Sum.inr a) xV ≠ 0) (hy0 : yV ≠ 0)
    (hyJ : ∀ i : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, r (Sum.inl i.1) yV = yV)
    (hya : ∀ a : Λa, r (Sum.inr a) yV = yV) :
    ∃ (θ : V ≃ₗ[ZMod p] GGTWE p N) (a : Λa) (c0 : Fin (N - 1)) (m n : ℤ)
      (ha αa : GGTWE p N) (lam mu : ZMod p)
      (news : Set (GGTWE p N × GGTWE p N))
      (rN : GGTWE p N × GGTWE p N → V ≃ₗ[ZMod p] V),
      θ xV = ggTWx p N ∧
      (∀ i, θ (h (Sum.inl (e i))) = ggTWh p N i) ∧
      (∀ i v, α (Sum.inl (e i)) v = ggTWdot (ggTWα p N i) (θ v)) ∧
      ha = θ (h (Sum.inr a)) ∧
      GGTWPat1 N pos c0.val m n ∧
      GGTWPairs1 p N pos c0 m n ha αa ∧
      ggTWdot αa ha = 2 ∧
      ggTWdot αa (ggTWx p N) ≠ 0 ∧
      (lam ≠ 0 ∨ mu ≠ 0) ∧
      ggTWdot αa (lam • ggTWx p N + mu • ggTWz p N pos) = 0 ∧
      θ yV = lam • ggTWx p N + mu • ggTWz p N pos ∧
      news = {(ha, αa)} ∧
      (∀ i v, θ (r (Sum.inl (e i)) v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v)) ∧
      (∀ t ∈ news, ∀ v, θ (rN t v) = ggTWRefl t.1 t.2 (θ v)) ∧
      rN (ha, αa) = r (Sum.inr a) ∧
      (Set.range (fun i : Fin (N - 1) => r (Sum.inl (e i))) ∪ rN '' news ⊆ Set.range r) ∧
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
          (fun o => h (o.map Subtype.val id))) := by
  classical
  have hN5 : 5 ≤ N := by omega
  obtain ⟨a₀, ha₀⟩ := hxa
  obtain ⟨θ, hθx, hθh, hθα⟩ := ggTW_model_iso (p := p) (N := N) hN5 hdim hF
  haveI : Subsingleton Λa := (Nat.card_eq_one_iff_unique.mp hcard).1
  obtain ⟨a⟩ := (Nat.card_eq_one_iff_unique.mp hcard).2
  letI : Unique Λa := uniqueOfSubsingleton a
  let ha : GGTWE p N := θ (h (Sum.inr a))
  obtain ⟨αa, hαa_dot⟩ := l05nS1_dot_of_comp_symm (p := p) (N := N) (α (Sum.inr a)) θ
  let eJ : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ≃ {c : Fin (N - 1) // ggTWInJ N pos c.val} :=
    { toFun := fun i => ⟨e.symm i.1, (hJpos (e.symm i.1)).2 (by
          rw [Equiv.apply_symm_apply]; exact i.2)⟩
      invFun := fun c => ⟨e c.1, (hJpos c.1).1 c.2⟩
      left_inv := by intro i; ext; simp
      right_inv := by intro c; ext; simp }
  let F : ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ≃
      Option {c : Fin (N - 1) // ggTWInJ N pos c.val} :=
    { toFun := fun o => match o with
        | Sum.inl i => some (eJ i)
        | Sum.inr _ => none
      invFun := fun o => match o with
        | some c => Sum.inl (eJ.symm c)
        | none => Sum.inr a
      left_inv := by
        rintro (i | x)
        · show Sum.inl (eJ.symm (eJ i)) = Sum.inl i
          rw [Equiv.symm_apply_apply]
        · show Sum.inr a = Sum.inr x
          rw [Subsingleton.elim a x]
      right_inv := by
        rintro (_ | c)
        · rfl
        · show some (eJ (eJ.symm c)) = some c
          rw [Equiv.apply_symm_apply] }
  let MK' : CoxeterMatrix (Option {c : Fin (N - 1) // ggTWInJ N pos c.val}) := MK.reindex F
  let CK' : Matrix (Option {c : Fin (N - 1) // ggTWInJ N pos c.val})
      (Option {c : Fin (N - 1) // ggTWInJ N pos c.val}) ℤ :=
    fun o o' => CK (F.symm o) (F.symm o')
  have hWMK' : GGIsWeylMatrix MK' := l05nS1_weyl_reindex hWMK F
  have hCK' : GGIntCartan MK' CK' := l05nS1_intCartan_reindex hCK F.symm
  have hsomeF : ∀ c : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      F.symm (some c) = Sum.inl (eJ.symm c) := fun c => rfl
  have hnoneF : F.symm none = Sum.inr a := rfl
  have hsomeFe : ∀ (c : Fin (N - 1)) (hc : ggTWInJ N pos c.val),
      F.symm (some ⟨c, hc⟩) =
        Sum.inl (⟨e c, (hJpos c).1 hc⟩ : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}) := by
    intro c hc
    rw [hsomeF]
    exact congrArg Sum.inl (Subtype.ext rfl)
  have hJ' : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      (CK' (some i) (some j) : ZMod p) = (CartanMatrix.A (N - 1) i.1 j.1 : ZMod p) := by
    intro i j
    have hpk := hpairK (Sum.inl (eJ.symm i)) (Sum.inl (eJ.symm j))
    simp only [Sum.map_inl, id_eq] at hpk
    have h3 : (eJ.symm i).1 = e i.1 := rfl
    have h4 : (eJ.symm j).1 = e j.1 := rfl
    show (CK (F.symm (some i)) (F.symm (some j)) : ZMod p) =
      (CartanMatrix.A (N - 1) i.1 j.1 : ZMod p)
    rw [hsomeF i, hsomeF j, ← hpk, h3, h4]
    exact hF.pair i.1 j.1
  obtain ⟨c0, m, n, hpat, hbonds⟩ :=
    ggTW_pattern1_rows (p := p) (N := N) hp hN pos hWMK' hCK' hJ'
  have hpairs : GGTWPairs1 p N pos c0 m n ha αa := by
    intro c hc
    have hb := hbonds ⟨c, hc⟩
    constructor
    · have h1 : ggTWdot αa (ggTWh p N c) = α (Sum.inr a) (θ.symm (ggTWh p N c)) :=
        hαa_dot _
      rw [h1, show θ.symm (ggTWh p N c) = h (Sum.inl (e c)) from by
            rw [← hθh c, LinearEquiv.symm_apply_apply]]
      have hpk := hpairK (Sum.inr a) (Sum.inl (⟨e c, (hJpos c).1 hc⟩ :
        {i : Λ // i ≠ b₁ ∧ i ≠ b₂}))
      simp only [Sum.map_inr, Sum.map_inl, id_eq] at hpk
      have hck : CK' none (some ⟨c, hc⟩) =
          CK (Sum.inr a) (Sum.inl ⟨e c, (hJpos c).1 hc⟩) := by
        show CK (F.symm none) (F.symm (some ⟨c, hc⟩)) = _
        rw [hnoneF, hsomeFe c hc]
      rw [hpk, ← hck, hb.1]
      split_ifs <;> simp
    · have h1 : ggTWdot (ggTWα p N c) ha =
          ggTWdot (ggTWα p N c) (θ (h (Sum.inr a))) := rfl
      rw [h1, ← hθα c (h (Sum.inr a))]
      have hpk := hpairK (Sum.inl (⟨e c, (hJpos c).1 hc⟩ :
        {i : Λ // i ≠ b₁ ∧ i ≠ b₂})) (Sum.inr a)
      simp only [Sum.map_inr, Sum.map_inl, id_eq] at hpk
      have hck : CK' (some ⟨c, hc⟩) none =
          CK (Sum.inl ⟨e c, (hJpos c).1 hc⟩) (Sum.inr a) := by
        show CK (F.symm (some ⟨c, hc⟩)) (F.symm none) = _
        rw [hnoneF, hsomeFe c hc]
      rw [hpk, ← hck, hb.2]
      split_ifs <;> simp
  have hha : ggTWdot αa ha = 2 := by
    have h1 : ggTWdot αa ha = α (Sum.inr a) (θ.symm ha) := hαa_dot ha
    rw [h1]
    show α (Sum.inr a) (θ.symm (θ (h (Sum.inr a)))) = 2
    rw [LinearEquiv.symm_apply_apply]
    have hpk := hpairK (Sum.inr a) (Sum.inr a)
    simp only [Sum.map_inr, id_eq] at hpk
    rw [hpk, hCK.1]
    norm_num
  have hxne : ggTWdot αa (ggTWx p N) ≠ 0 := by
    have h1 : ggTWdot αa (ggTWx p N) = α (Sum.inr a) (θ.symm (ggTWx p N)) := hαa_dot _
    rw [h1, show θ.symm (ggTWx p N) = xV from by
          rw [← hθx, LinearEquiv.symm_apply_apply]]
    rw [show a = a₀ from Subsingleton.elim a a₀]
    exact ha₀
  have hfixJ : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggTWdot (ggTWα p N c) (θ yV) = 0 := by
    intro c hc
    rw [← hθα c yV]
    have hmem := (hJpos c).1 hc
    have hry : r (Sum.inl (e c)) yV = yV := hyJ ⟨e c, hmem⟩
    have hrw := hr (Sum.inl (e c)) yV
    rw [hry] at hrw
    have hzero : α (Sum.inl (e c)) yV • h (Sum.inl (e c)) = 0 := sub_eq_self.mp hrw.symm
    have hhne : h (Sum.inl (e c)) ≠ 0 := by
      intro h0
      have hp2 := l05nS1_two_ne_zero hp
      have hpair := hF.pair c c
      rw [h0, map_zero] at hpair
      rw [show CartanMatrix.A (N - 1) c c = 2 from by simp [CartanMatrix.A]] at hpair
      exact hp2 hpair.symm
    exact (smul_eq_zero.mp hzero).resolve_right hhne
  obtain ⟨lam, mu, hy_lam_mu⟩ := ggTW_fixedJ hpN hN5 pos (θ yV) hfixJ
  have hyne : θ yV ≠ 0 := by
    intro hzero
    exact hy0 (by simpa using congrArg θ.symm hzero)
  have hlam_mu_ne : lam ≠ 0 ∨ mu ≠ 0 := by
    by_contra hcon
    simp only [not_or, not_ne_iff] at hcon
    obtain ⟨hlam, hmu⟩ := hcon
    exact hyne (by rw [hy_lam_mu, hlam, hmu]; simp)
  have hfixa : α (Sum.inr a) yV = 0 := by
    have hry : r (Sum.inr a) yV = yV := hya a
    have hrw := hr (Sum.inr a) yV
    rw [hry] at hrw
    have hzero : α (Sum.inr a) yV • h (Sum.inr a) = 0 := sub_eq_self.mp hrw.symm
    have hhne : h (Sum.inr a) ≠ 0 := by
      intro h0
      have hp2 := l05nS1_two_ne_zero hp
      have hpk := hpairK (Sum.inr a) (Sum.inr a)
      simp only [Sum.map_inr, id_eq] at hpk
      rw [h0, map_zero, hCK.1] at hpk
      exact hp2 hpk.symm
    exact (smul_eq_zero.mp hzero).resolve_right hhne
  have hdoty : ggTWdot αa (lam • ggTWx p N + mu • ggTWz p N pos) = 0 := by
    have h1 : ggTWdot αa (lam • ggTWx p N + mu • ggTWz p N pos) =
        α (Sum.inr a) (θ.symm (lam • ggTWx p N + mu • ggTWz p N pos)) := hαa_dot _
    rw [h1, show θ.symm (lam • ggTWx p N + mu • ggTWz p N pos) = yV from by
          rw [← hy_lam_mu, LinearEquiv.symm_apply_apply]]
    exact hfixa
  let rF : Fin (N - 1) → V ≃ₗ[ZMod p] V := fun i => r (Sum.inl (e i))
  let news : Set (GGTWE p N × GGTWE p N) := {(ha, αa)}
  let rN : GGTWE p N × GGTWE p N → V ≃ₗ[ZMod p] V := fun _ => r (Sum.inr a)
  have hnews : news = {(ha, αa)} := rfl
  have hsub : Set.range rF ∪ rN '' news ⊆ Set.range r := by
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨i, rfl⟩
      exact ⟨Sum.inl (e i), rfl⟩
    · rcases hx with ⟨t, ht, rfl⟩
      exact ⟨Sum.inr a, rfl⟩
  have hrF : ∀ i v, θ (rF i v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v) := by
    intro i v
    show θ (r (Sum.inl (e i)) v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v)
    rw [hr (Sum.inl (e i)) v, map_sub, map_smul, hθh i, l05nS1_refl_apply, hθα i v]
  have hrNr : ∀ b : Λa, ∀ v, θ (r (Sum.inr b) v) = ggTWRefl ha αa (θ v) := by
    intro b v
    rw [Subsingleton.elim b a]
    show θ (r (Sum.inr a) v) = ggTWRefl ha αa (θ v)
    rw [hr (Sum.inr a) v, map_sub, map_smul, l05nS1_refl_apply]
    dsimp only [ha]
    rw [hαa_dot (θ v), LinearEquiv.symm_apply_apply]
  have hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggTWRefl t.1 t.2 (θ v) := by
    intro t ht v
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hrNr a v
  have hrNr_eq : rN (ha, αa) = r (Sum.inr a) := rfl
  have hnt' : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
    fun g hg => hnt g (Subgroup.closure_mono hsub hg)
  have hroots_eq : ggHLRoots rF (fun i => θ.symm (ggTWh p N i)) =
      ggHLRoots (fun i : Λ => r (Sum.inl i)) (fun i : Λ => h (Sum.inl i)) := by
    have h1 : (fun i : Fin (N - 1) => θ.symm (ggTWh p N i)) =
        fun i => h (Sum.inl (e i)) := by
      funext i
      rw [← hθh i, LinearEquiv.symm_apply_apply]
    rw [h1]
    exact l05nS1_hlroots_reindex e (fun i : Λ => r (Sum.inl i))
      (fun i : Λ => h (Sum.inl i))
  have hHL' : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news), GGLinRefl g →
      g xV = xV → GGHLLines (ggHLRoots rF (fun i => θ.symm (ggTWh p N i))) xV g := by
    intro g hg hrefl hgx
    rw [hroots_eq]
    exact hHL g (Subgroup.closure_mono hsub hg) hrefl hgx
  have hrootsO : ggHLRoots
      (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => r (Sum.inl (e i.1)))
        (fun t : ↥news => rN t.1))
      (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => θ.symm (ggTWh p N i.1))
        (fun t : ↥news => θ.symm t.1.1)) =
      ggHLRoots (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => r (o.map Subtype.val id))
        (fun o => h (o.map Subtype.val id)) := by
    let φ : ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ ↥news) ≃
        ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) :=
      { toFun := fun x => match x with
          | Sum.inl c => Sum.inl (eJ.symm c)
          | Sum.inr _ => Sum.inr a
        invFun := fun x => match x with
          | Sum.inl i => Sum.inl (eJ i)
          | Sum.inr _ => Sum.inr ⟨(ha, αa), by simp [news]⟩
        left_inv := by
          rintro (c | t)
          · show Sum.inl (eJ (eJ.symm c)) = Sum.inl c
            rw [Equiv.apply_symm_apply]
          · apply congrArg Sum.inr
            exact Subtype.ext (Set.mem_singleton_iff.mp t.2).symm
        right_inv := by
          rintro (i | b)
          · show Sum.inl (eJ.symm (eJ i)) = Sum.inl i
            rw [Equiv.symm_apply_apply]
          · apply congrArg Sum.inr
            exact Subsingleton.elim a b }
    have hf : (fun x : ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ ↥news) =>
        r ((φ x).map Subtype.val id)) =
        Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => r (Sum.inl (e i.1)))
          (fun t : ↥news => rN t.1) := by
      funext x
      rcases x with c | t
      · rfl
      · rfl
    have hh : (fun x : ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ ↥news) =>
        h ((φ x).map Subtype.val id)) =
        Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => θ.symm (ggTWh p N i.1))
          (fun t : ↥news => θ.symm t.1.1) := by
      funext x
      rcases x with c | t
      · show h (Sum.inl (eJ.symm c).1) = θ.symm (ggTWh p N c.1)
        have hc : (eJ.symm c).1 = e c.1 := rfl
        rw [hc, ← hθh c.1, LinearEquiv.symm_apply_apply]
      · show h (Sum.inr a) = θ.symm t.1.1
        have ht : t.1 = (ha, αa) := Set.mem_singleton_iff.mp t.2
        rw [ht, show ha = θ (h (Sum.inr a)) from rfl, LinearEquiv.symm_apply_apply]
    rw [← hf, ← hh]
    exact l05nS1_hlroots_reindex φ
      (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => r (o.map Subtype.val id))
      (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => h (o.map Subtype.val id))
  exact ⟨θ, a, c0, m, n, ha, αa, lam, mu, news, rN, hθx, hθh, hθα, rfl, hpat, hpairs, hha,
    hxne, hlam_mu_ne, hdoty, hy_lam_mu, hnews, hrF, hrN, hrNr_eq, hsub, hnt', hHL', hrootsO⟩

theorem ggTWSurv1_of_vcfg {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hpN : p ∣ N)
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) (hv : GGTWVCfg p N 1) :
    GGTWSurv1 .frame p N := by
  classical
  obtain ⟨pos, V, iV1, iV2, Λ, iΛ1, iΛ2, b₁, b₂, Λa, iΛa1, iΛa2, MK, CK, e, r, h, α,
    xV, yV, hb, hcard, hJpos, hWMK, hCK, _hk2, hr, hF, hdim, hpairK, hnt, hHL,
    ⟨a₀, ha₀⟩, hy0, hyJ, hya⟩ := hv
  letI := iV1
  letI := iV2
  letI := iΛ1
  letI := iΛ2
  letI := iΛa1
  letI := iΛa2
  obtain ⟨θ, a, c0, m, n, ha, αa, lam, mu, news, rN, hθx, _hθh, _hθα, _hha_eq, hpat, hpairs,
    hha, hxne, hlam_mu_ne, hdoty, hy_lam_mu, hnews, hrF, hrN, _hrNr_eq, hsub, hnt', hHL',
    _hrootsO⟩ :=
    ggTWSurv1_cell (p := p) (N := N) (pos := pos) hp hpN hN hb hcard hJpos hWMK hCK hr hF hdim
      hpairK hnt hHL ⟨a₀, ha₀⟩ hy0 hyJ hya
  let rF : Fin (N - 1) → V ≃ₗ[ZMod p] V := fun i => r (Sum.inl (e i))
  have hkill : ¬ GGTWKill .frame p N pos news
      (lam • ggTWx p N + mu • ggTWz p N pos) :=
    ggTW_notKill_frame (p := p) (N := N) (by omega : p ≠ 2) θ hθx rF hrF news rN
      hrN hnt' hHL' pos (lam • ggTWx p N + mu • ggTWz p N pos)
  refine ⟨pos, c0, m, n, ha, αa, lam, mu, hpat, hpairs, hha, hxne, hlam_mu_ne, hdoty, ?_⟩
  rwa [hnews] at hkill

end CFSG.StandardType

end
