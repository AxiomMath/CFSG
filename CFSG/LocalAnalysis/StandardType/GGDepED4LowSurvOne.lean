module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LowDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowModel
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nS1E_hlroots_reindex {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
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

private lemma l05nS1_fixedJ_aux : ∀ v : GGDepAE 3 6,
    (ggDepAdot (ggDepELα 1) v = 0 → ggDepAdot (ggDepELα 2) v = 0 →
      ggDepAdot (ggDepELα 3) v = 0 → ggDepAdot (ggDepELα 4) v = 0 →
      ∃ lam mu : ZMod 3, v = lam • ggDepELx + mu • ggDepELz) := by
  decide +kernel

private lemma l05nS1_fixedJ (v : GGDepAE 3 6)
    (hv : ∀ c : Fin 6, GGDepED4In c → ggDepAdot (ggDepELα c) v = 0) :
    ∃ lam mu : ZMod 3, v = lam • ggDepELx + mu • ggDepELz :=
  l05nS1_fixedJ_aux v
    (hv 1 (by unfold GGDepED4In; decide))
    (hv 2 (by unfold GGDepED4In; decide))
    (hv 3 (by unfold GGDepED4In; decide))
    (hv 4 (by unfold GGDepED4In; decide))

theorem ggDepELSurv1_cell {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    {e : Fin 6 ≃ Λ} {r : Λ ⊕ Λa → V ≃ₗ[ZMod 3] V} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V} {xV yV : V}
    (hb1 : b₁ = e 0) (hb2 : b₂ = e 5) (hcard : Nat.card Λa = 1)
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hr : ∀ o w, r o w = w - α o w • h o)
    (hF : GGDepEFrame 3 (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV)
    (hdim : Module.finrank (ZMod 3) V = 6)
    (hpairK : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hHL : ∀ g ∈ Subgroup.closure (Set.range r), GGLinRefl g → g xV = xV →
      GGHLLines (ggHLRoots (fun i : Λ => r (Sum.inl i)) (fun i : Λ => h (Sum.inl i))) xV g)
    (hxa : ∃ a : Λa, α (Sum.inr a) xV ≠ 0) (hy0 : yV ≠ 0)
    (hyJ : ∀ i : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, r (Sum.inl i.1) yV = yV)
    (hya : ∀ a : Λa, r (Sum.inr a) yV = yV) :
    ∃ (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (a : Λa) (c0 : Fin 6) (ha αa : GGDepAE 3 6)
      (lam mu : ZMod 3) (news : Set (GGDepAE 3 6 × GGDepAE 3 6))
      (rN : GGDepAE 3 6 × GGDepAE 3 6 → V ≃ₗ[ZMod 3] V),
      θ xV = ggDepELx ∧
      (∀ i, θ (h (Sum.inl (e i))) = ggDepELh i) ∧
      (∀ i v, α (Sum.inl (e i)) v = ggDepAdot (ggDepELα i) (θ v)) ∧
      ha = θ (h (Sum.inr a)) ∧
      GGDepED4Leaf c0 ∧ GGDepELPairs1 c0 ha αa ∧ ggDepAdot αa ha = 2 ∧
      ggDepAdot αa ggDepELx ≠ 0 ∧ (lam ≠ 0 ∨ mu ≠ 0) ∧
      ggDepAdot αa (lam • ggDepELx + mu • ggDepELz) = 0 ∧
      θ yV = lam • ggDepELx + mu • ggDepELz ∧
      news = {(ha, αa)} ∧
      (∀ i v, θ (r (Sum.inl (e i)) v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v)) ∧
      (∀ t ∈ news, ∀ v, θ (rN t v) = ggDepARefl t.1 t.2 (θ v)) ∧
      rN (ha, αa) = r (Sum.inr a) ∧
      (Set.range (fun i : Fin 6 => r (Sum.inl (e i))) ∪ rN '' news ⊆ Set.range r) ∧
      (∀ g ∈ Subgroup.closure (Set.range (fun i : Fin 6 => r (Sum.inl (e i))) ∪ rN '' news),
        ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
      (∀ g ∈ Subgroup.closure (Set.range (fun i : Fin 6 => r (Sum.inl (e i))) ∪ rN '' news),
        GGLinRefl g → g xV = xV →
          GGHLLines (ggHLRoots (fun i : Fin 6 => r (Sum.inl (e i)))
            (fun i => θ.symm (ggDepELh i))) xV g) ∧
      (ggHLRoots
          (Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => r (Sum.inl (e i.1)))
            (fun t : ↥news => rN t.1))
          (Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => θ.symm (ggDepELh i.1))
            (fun t : ↥news => θ.symm t.1.1)) =
        ggHLRoots (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => r (o.map Subtype.val id))
          (fun o => h (o.map Subtype.val id))) := by
  classical
  obtain ⟨a₀, ha₀⟩ := hxa
  haveI : Module.Finite (ZMod 3) V := by
    haveI : FiniteDimensional (ZMod 3) V :=
      FiniteDimensional.of_finrank_pos (by rw [hdim]; norm_num)
    infer_instance
  obtain ⟨θ, hθh, hθα, hθx⟩ := ggDepELModel_iso hF hdim
  haveI : Subsingleton Λa := (Nat.card_eq_one_iff_unique.mp hcard).1
  obtain ⟨a⟩ := (Nat.card_eq_one_iff_unique.mp hcard).2
  letI : Unique Λa := uniqueOfSubsingleton a
  let ha : GGDepAE 3 6 := θ (h (Sum.inr a))
  obtain ⟨αa, hαa_dot⟩ := l05nPT_dot_of_comp_symm (α (Sum.inr a)) θ
  have hEc : ∀ (c : Fin 6) (hc : GGDepED4In c), e c ≠ b₁ ∧ e c ≠ b₂ := by
    intro c hc
    exact ⟨fun hh => hc.1 (e.injective (hh.trans hb1)),
      fun hh => hc.2 (e.injective (hh.trans hb2))⟩
  let eJ : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ≃ {c : Fin 6 // GGDepED4In c} :=
    { toFun := fun i => ⟨e.symm i.1, by
        constructor
        · intro h0
          exact i.2.1 (by rw [← Equiv.apply_symm_apply e i.1, h0, ← hb1])
        · intro h5
          exact i.2.2 (by rw [← Equiv.apply_symm_apply e i.1, h5, ← hb2])⟩
      invFun := fun c => ⟨e c.1, hEc c.1 c.2⟩
      left_inv := by intro i; ext; simp
      right_inv := by intro c; ext; simp }
  let F : ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ≃ Option {c : Fin 6 // GGDepED4In c} :=
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
  let MK' : CoxeterMatrix (Option {c : Fin 6 // GGDepED4In c}) := MK.reindex F
  let CK' : Matrix (Option {c : Fin 6 // GGDepED4In c})
      (Option {c : Fin 6 // GGDepED4In c}) ℤ := fun o o' => CK (F.symm o) (F.symm o')
  have hWMK' : GGIsWeylMatrix MK' := l05nDP4_weyl_reindex hWMK F
  have hCK' : GGIntCartan MK' CK' := l05nBL_intCartan_reindex hCK F.symm
  have hsomeF : ∀ c : {c : Fin 6 // GGDepED4In c}, F.symm (some c) = Sum.inl (eJ.symm c) :=
    fun c => rfl
  have hnoneF : F.symm none = Sum.inr a := rfl
  have hsomeFe : ∀ (c : Fin 6) (hc : GGDepED4In c),
      F.symm (some ⟨c, hc⟩) = Sum.inl (⟨e c, hEc c hc⟩ : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}) := by
    intro c hc
    rw [hsomeF]
    exact congrArg Sum.inl (Subtype.ext rfl)
  have hJ' : ∀ i j : {c : Fin 6 // GGDepED4In c},
      (CK' (some i) (some j) : ZMod 3) = (CartanMatrix.E 6 i.1 j.1 : ZMod 3) := by
    intro i j
    have hpk := hpairK (Sum.inl (eJ.symm i)) (Sum.inl (eJ.symm j))
    simp only [Sum.map_inl, id_eq] at hpk
    show (CK (F.symm (some i)) (F.symm (some j)) : ZMod 3) =
      (CartanMatrix.E 6 i.1 j.1 : ZMod 3)
    rw [hsomeF i, hsomeF j, ← hpk, show (eJ.symm i).1 = e i.1 from rfl,
      show (eJ.symm j).1 = e j.1 from rfl]
    exact hF.pair i.1 j.1
  obtain ⟨c0, hleaf, hbonds⟩ := ggDepED4_pattern1 hWMK' hCK' hJ'
  have hpairs : GGDepELPairs1 c0 ha αa := by
    intro c hc
    constructor
    · have h1 : ggDepAdot αa (ggDepELh c) = α (Sum.inr a) (θ.symm (ggDepELh c)) :=
        hαa_dot _
      rw [h1, show θ.symm (ggDepELh c) = h (Sum.inl (e c)) from by
            rw [← hθh c, LinearEquiv.symm_apply_apply]]
      have hpk := hpairK (Sum.inr a) (Sum.inl (⟨e c, hEc c hc⟩ :
        {i : Λ // i ≠ b₁ ∧ i ≠ b₂}))
      simp only [Sum.map_inr, Sum.map_inl, id_eq] at hpk
      have hck : CK' none (some ⟨c, hc⟩) =
          CK (Sum.inr a) (Sum.inl ⟨e c, hEc c hc⟩) := by
        show CK (F.symm none) (F.symm (some ⟨c, hc⟩)) = _
        rw [hnoneF, hsomeFe c hc]
      rw [hpk, ← hck, (hbonds ⟨c, hc⟩).1]
      split_ifs <;> simp
    · have h1 : ggDepAdot (ggDepELα c) ha =
          ggDepAdot (ggDepELα c) (θ (h (Sum.inr a))) := rfl
      rw [h1, ← hθα c (h (Sum.inr a))]
      have hpk := hpairK (Sum.inl (⟨e c, hEc c hc⟩ :
        {i : Λ // i ≠ b₁ ∧ i ≠ b₂})) (Sum.inr a)
      simp only [Sum.map_inr, Sum.map_inl, id_eq] at hpk
      have hck : CK' (some ⟨c, hc⟩) none =
          CK (Sum.inl ⟨e c, hEc c hc⟩) (Sum.inr a) := by
        show CK (F.symm (some ⟨c, hc⟩)) (F.symm none) = _
        rw [hnoneF, hsomeFe c hc]
      rw [hpk, ← hck, (hbonds ⟨c, hc⟩).2]
      split_ifs <;> simp
  have hha : ggDepAdot αa ha = 2 := by
    have h1 : ggDepAdot αa ha = α (Sum.inr a) (θ.symm ha) := hαa_dot ha
    rw [h1]
    show α (Sum.inr a) (θ.symm (θ (h (Sum.inr a)))) = 2
    rw [LinearEquiv.symm_apply_apply]
    have hpk := hpairK (Sum.inr a) (Sum.inr a)
    simp only [Sum.map_inr, id_eq] at hpk
    rw [hpk, hCK.1]
    norm_num
  have hxne : ggDepAdot αa ggDepELx ≠ 0 := by
    have h1 : ggDepAdot αa ggDepELx = α (Sum.inr a) (θ.symm ggDepELx) := hαa_dot _
    rw [h1, show θ.symm ggDepELx = xV from by
          rw [← hθx, LinearEquiv.symm_apply_apply]]
    rw [show a = a₀ from Subsingleton.elim a a₀]
    exact ha₀
  have hfixJ : ∀ c : Fin 6, GGDepED4In c → ggDepAdot (ggDepELα c) (θ yV) = 0 := by
    intro c hc
    rw [← hθα c yV]
    have hry : r (Sum.inl (e c)) yV = yV := hyJ ⟨e c, hEc c hc⟩
    have hrw := hr (Sum.inl (e c)) yV
    rw [hry] at hrw
    have hzero : α (Sum.inl (e c)) yV • h (Sum.inl (e c)) = 0 := sub_eq_self.mp hrw.symm
    have hhne : h (Sum.inl (e c)) ≠ 0 := by
      intro h0
      have hp2 : (2 : ZMod 3) ≠ 0 := by decide
      have hpair := hF.pair c c
      rw [h0, map_zero] at hpair
      have hdiag : CartanMatrix.E 6 c c = 2 := by
        rw [CartanMatrix.E_six_eq]; fin_cases c <;> decide +kernel
      rw [hdiag] at hpair
      exact hp2 hpair.symm
    exact (smul_eq_zero.mp hzero).resolve_right hhne
  obtain ⟨lam, mu, hy_lam_mu⟩ := l05nS1_fixedJ (θ yV) hfixJ
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
      have hp2 : (2 : ZMod 3) ≠ 0 := by decide
      have hpk := hpairK (Sum.inr a) (Sum.inr a)
      simp only [Sum.map_inr, id_eq] at hpk
      rw [h0, map_zero, hCK.1] at hpk
      exact hp2 hpk.symm
    exact (smul_eq_zero.mp hzero).resolve_right hhne
  have hdoty : ggDepAdot αa (lam • ggDepELx + mu • ggDepELz) = 0 := by
    have h1 : ggDepAdot αa (lam • ggDepELx + mu • ggDepELz) =
        α (Sum.inr a) (θ.symm (lam • ggDepELx + mu • ggDepELz)) := hαa_dot _
    rw [h1, show θ.symm (lam • ggDepELx + mu • ggDepELz) = yV from by
          rw [← hy_lam_mu, LinearEquiv.symm_apply_apply]]
    exact hfixa
  let rF : Fin 6 → V ≃ₗ[ZMod 3] V := fun i => r (Sum.inl (e i))
  let news : Set (GGDepAE 3 6 × GGDepAE 3 6) := {(ha, αa)}
  let rN : GGDepAE 3 6 × GGDepAE 3 6 → V ≃ₗ[ZMod 3] V := fun _ => r (Sum.inr a)
  have hnews : news = {(ha, αa)} := rfl
  have hsub : Set.range rF ∪ rN '' news ⊆ Set.range r := by
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨i, rfl⟩
      exact ⟨Sum.inl (e i), rfl⟩
    · rcases hx with ⟨t, _, rfl⟩
      exact ⟨Sum.inr a, rfl⟩
  have hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v) := by
    intro i v
    show θ (r (Sum.inl (e i)) v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v)
    rw [hr (Sum.inl (e i)) v, map_sub, map_smul, hθh i, l05nPT_refl_apply, hθα i v]
  have hrNr : ∀ b : Λa, ∀ v, θ (r (Sum.inr b) v) = ggDepARefl ha αa (θ v) := by
    intro b v
    rw [Subsingleton.elim b a]
    show θ (r (Sum.inr a) v) = ggDepARefl ha αa (θ v)
    rw [hr (Sum.inr a) v, map_sub, map_smul, l05nPT_refl_apply]
    dsimp only [ha]
    rw [hαa_dot (θ v), LinearEquiv.symm_apply_apply]
  have hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggDepARefl t.1 t.2 (θ v) := by
    intro t ht v
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hrNr a v
  have hrNr_eq : rN (ha, αa) = r (Sum.inr a) := rfl
  have hnt' : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) :=
    fun g hg => hnt g (Subgroup.closure_mono hsub hg)
  have hroots_eq : ggHLRoots rF (fun i => θ.symm (ggDepELh i)) =
      ggHLRoots (fun i : Λ => r (Sum.inl i)) (fun i : Λ => h (Sum.inl i)) := by
    have h1 : (fun i : Fin 6 => θ.symm (ggDepELh i)) = fun i => h (Sum.inl (e i)) := by
      funext i
      rw [← hθh i, LinearEquiv.symm_apply_apply]
    rw [h1]
    exact l05nS1E_hlroots_reindex e (fun i : Λ => r (Sum.inl i))
      (fun i : Λ => h (Sum.inl i))
  have hHL' : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news), GGLinRefl g →
      g xV = xV → GGHLLines (ggHLRoots rF (fun i => θ.symm (ggDepELh i))) xV g := by
    intro g hg hrefl hgx
    rw [hroots_eq]
    exact hHL g (Subgroup.closure_mono hsub hg) hrefl hgx
  have hrootsO : ggHLRoots
      (Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => r (Sum.inl (e i.1)))
        (fun t : ↥news => rN t.1))
      (Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => θ.symm (ggDepELh i.1))
        (fun t : ↥news => θ.symm t.1.1)) =
      ggHLRoots (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => r (o.map Subtype.val id))
        (fun o => h (o.map Subtype.val id)) := by
    let φ : ({c : Fin 6 // GGDepED4In c} ⊕ ↥news) ≃
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
    have hf : (fun x : ({c : Fin 6 // GGDepED4In c} ⊕ ↥news) =>
        r ((φ x).map Subtype.val id)) =
        Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => r (Sum.inl (e i.1)))
          (fun t : ↥news => rN t.1) := by
      funext x
      rcases x with c | t
      · rfl
      · rfl
    have hh : (fun x : ({c : Fin 6 // GGDepED4In c} ⊕ ↥news) =>
        h ((φ x).map Subtype.val id)) =
        Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => θ.symm (ggDepELh i.1))
          (fun t : ↥news => θ.symm t.1.1) := by
      funext x
      rcases x with c | t
      · show h (Sum.inl (eJ.symm c).1) = θ.symm (ggDepELh c.1)
        rw [show (eJ.symm c).1 = e c.1 from rfl, ← hθh c.1,
          LinearEquiv.symm_apply_apply]
      · show h (Sum.inr a) = θ.symm t.1.1
        have ht : t.1 = (ha, αa) := Set.mem_singleton_iff.mp t.2
        rw [ht, show ha = θ (h (Sum.inr a)) from rfl, LinearEquiv.symm_apply_apply]
    rw [← hf, ← hh]
    exact l05nS1E_hlroots_reindex φ
      (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => r (o.map Subtype.val id))
      (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => h (o.map Subtype.val id))
  exact ⟨θ, a, c0, ha, αa, lam, mu, news, rN, hθx, hθh, hθα, rfl, hleaf, hpairs, hha, hxne,
    hlam_mu_ne, hdoty, hy_lam_mu, hnews, hrF, hrN, hrNr_eq, hsub, hnt', hHL', hrootsO⟩

end CFSG.StandardType

end
