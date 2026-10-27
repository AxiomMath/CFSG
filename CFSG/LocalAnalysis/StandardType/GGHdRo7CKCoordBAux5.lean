module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoKey
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTorus
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordBWeight
import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordBAux7
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.StandardType
open CFSG.Open
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7CKCoordAux_coord_transfer_core (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs K : Subgroup G} {y z : G}
    (n : ℕ) (hy : y ∈ Bs) (hz : z ∈ Bs ⊓ K)
    (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs) (hp3 : p = 3) (hn : 5 ≤ n)
    (h0 : τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨y, hy⟩)
    (hmodel : C2CoordModel p Bs K n τ)
    (hmem : ∀ f : Fin (n + 1) → Multiplicative (ZMod p), (τ f : G) ∈ K ↔ f 0 = 1)
    {m : ℕ} (φ : StatedSp m (GaloisField 2 1) →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = K)
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (t : StatedSp m (GaloisField 2 1)) (ht : F.tor c = t) (htz : φ t = z)
    (hE : E = (Bs ⊓ K).comap φ)
    (hsupp : (F.suppSet c).card = 2) :
    ∃ i j : Fin (n + 1), i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧
      ∀ l : Fin (n + 1), l ≠ 0 →
        (Multiplicative.toAdd (τ.symm ⟨z, hz.1⟩ l) ≠ 0 ↔ l = i ∨ l = j) := by
  subst hp3
  classical
  have hn0 : 0 < n := by omega
  have hζ3 : ζ ^ 3 = 1 :=
    hdRo7CKCoordAux_zeta_cube n τ φ hinj F c hE hsupp
  have hζne : ζ ≠ 1 :=
    hdRo7CKCoordAux_zeta_ne_one n hn0 τ hmem φ hinj hrange F c hE
  have hζ : IsPrimitiveRoot ζ 3 := by
    rw [IsPrimitiveRoot.iff_orderOf]
    exact orderOf_eq_prime hζ3 hζne
  have hs : F.s = n :=
    hdRo7CKCoordAux_s_eq n hn0 τ hmem φ hinj hrange F c hE hsupp
  let S : Subgroup G := Bs ⊓ K
  let T : (Fin F.s → ZMod 3) → ↥S := fun c =>
    ⟨(φ (F.tor c) : G), by
      simpa [S, Subgroup.mem_comap, hE] using F.tor_mem c⟩
  have hT_inj : Function.Injective T := by
    intro c c' h
    apply hdRo7CKCoordAux_tor_injective F hζ
    apply hinj
    exact Subtype.ext_iff.mp h
  have hT_surj : Function.Surjective T := by
    intro b
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact b.2.2)
    have htE : t ∈ E := by rw [hE, Subgroup.mem_comap, ht]; exact b.2
    obtain ⟨c, hc⟩ := F.mem_tor t htE
    exact ⟨c, Subtype.ext (by show φ (F.tor c) = b.1; rw [hc, ht])⟩
  let frameCoord : ↥S → (Fin F.s → ZMod 3) := fun b => Classical.choose (hT_surj b)
  have hframeCoord : ∀ b : ↥S, T (frameCoord b) = b := fun b => Classical.choose_spec (hT_surj b)
  let wtOn : ↥Bs → ℕ := fun b =>
    if h : (b : G) ∈ S then (F.suppSet (frameCoord ⟨b, h⟩)).card else 0
  let P : Subgroup (MulAut ↥Bs) :=
    { carrier := {a | ∀ b : ↥Bs, wtOn (a b) = wtOn b}
      one_mem' := by intro b; rfl
      mul_mem' := by
        intro a1 a2 h1 h2 b
        show wtOn ((a1 * a2) b) = wtOn b
        rw [MulAut.mul_apply, h1, h2]
      inv_mem' := by
        intro a ha b
        have h := ha (a⁻¹ b)
        rw [MulAut.apply_inv_self ↥Bs a b] at h
        exact h.symm }
  have hgen : ggInduced K Bs ⊆ ↑P := by
    rintro a ⟨g, hgK, hgN, hgact⟩
    intro b
    let Ψ : ↥S → ↥Bs := fun z => ⟨z.1, z.2.1⟩
    have hmapS : ∀ x : ↥Bs, (x : G) ∈ S → ((a x : ↥Bs) : G) ∈ S := by
      intro x hx
      rw [hgact x]
      exact ⟨(Subgroup.mem_normalizer_iff.mp hgN x).mp x.2,
        K.mul_mem (K.mul_mem hgK hx.2) (K.inv_mem hgK)⟩
    let Ξ : ↥S → ↥S := fun z => ⟨a (Ψ z), hmapS (Ψ z) z.2⟩
    have hΨ_inj : Function.Injective Ψ := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : ↥Bs => (z : G)) h)
    have hΞ_inj : Function.Injective Ξ := by
      intro x y h
      apply hΨ_inj
      apply a.injective
      apply Subtype.ext
      exact congrArg (fun z : ↥S => (z : G)) h
    have hΞ_surj : Function.Surjective Ξ := Finite.surjective_of_injective hΞ_inj
    by_cases hb : (b : G) ∈ S
    · have hb' : ((a b : ↥Bs) : G) ∈ S := hmapS b hb
      have hb₀ : T (frameCoord ⟨b, hb⟩) = ⟨b, hb⟩ := hframeCoord ⟨b, hb⟩
      have hb₁ : T (frameCoord ⟨(a b : ↥Bs), hb'⟩) = ⟨(a b : ↥Bs), hb'⟩ :=
        hframeCoord ⟨(a b : ↥Bs), hb'⟩
      obtain ⟨g', hg'⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hgK)
      have hconj : F.tor (frameCoord ⟨(a b : ↥Bs), hb'⟩)
          = g' * F.tor (frameCoord ⟨b, hb⟩) * g'⁻¹ := by
        apply hinj
        have h1 : φ (F.tor (frameCoord ⟨(a b : ↥Bs), hb'⟩)) = ((a b : ↥Bs) : G) :=
          Subtype.ext_iff.mp hb₁
        have h0 : φ (F.tor (frameCoord ⟨b, hb⟩)) = (b : G) := Subtype.ext_iff.mp hb₀
        rw [map_mul, map_mul, map_inv, hg', h1, h0, hgact b]
      have hgen1 := hdRo7CKCoordAux_spFixedDim_tor_gen F hζ (frameCoord ⟨(a b : ↥Bs), hb'⟩)
      have hgen0 := hdRo7CKCoordAux_spFixedDim_tor_gen F hζ (frameCoord ⟨b, hb⟩)
      rw [hconj, hdRo7CKCoordAux_spFixedDim_conj] at hgen1
      have hdpos : 0 < Module.finrank (GaloisField 2 1) L := Module.finrank_pos
      have hz : (F.zeroSet (frameCoord ⟨(a b : ↥Bs), hb'⟩)).card
          = (F.zeroSet (frameCoord ⟨b, hb⟩)).card := by
        have hEq : (F.zeroSet (frameCoord ⟨(a b : ↥Bs), hb'⟩)).card *
              Module.finrank (GaloisField 2 1) L
            = (F.zeroSet (frameCoord ⟨b, hb⟩)).card * Module.finrank (GaloisField 2 1) L :=
          hgen1.symm.trans hgen0
        exact Nat.mul_right_cancel hdpos hEq
      have hsuppc : (F.suppSet (frameCoord ⟨(a b : ↥Bs), hb'⟩)).card
          = (F.suppSet (frameCoord ⟨b, hb⟩)).card := by
        have h1 := hdRo7CKCoordAux_zeroSet_card_add_suppSet_card F
          (frameCoord ⟨(a b : ↥Bs), hb'⟩)
        have h0 := hdRo7CKCoordAux_zeroSet_card_add_suppSet_card F (frameCoord ⟨b, hb⟩)
        omega
      show wtOn (a b) = wtOn b
      dsimp only [wtOn]
      rw [dif_pos hb', dif_pos hb]
      exact hsuppc
    · have hb' : ¬ ((a b : ↥Bs) : G) ∈ S := by
        intro h
        obtain ⟨x, hx⟩ := hΞ_surj ⟨(a b : ↥Bs), h⟩
        have hx1 : a (Ψ x) = a b := Subtype.ext (congrArg (fun z : ↥S => (z : G)) hx)
        have hxb : Ψ x = b := a.injective hx1
        have hΨx : (Ψ x : G) = (b : G) := congrArg Subtype.val hxb
        exact hb (hΨx ▸ x.2)
      show wtOn (a b) = wtOn b
      dsimp only [wtOn]
      rw [dif_neg hb', dif_neg hb]
  have hAut : ggAutomizer K Bs ≤ P := (Subgroup.closure_le P).mpr hgen
  let ΨS : ↥S → ↥Bs := fun z => ⟨z.1, z.2.1⟩
  have hcoord0 : ∀ c : Fin F.s → ZMod 3, (τ.symm (ΨS (T c))) 0 = 1 := by
    intro c
    refine (hmem (τ.symm (ΨS (T c)))).mp ?_
    have h' : (ΨS (T c) : G) ∈ K := (T c).2.2
    simpa [ΨS] using h'
  have hT_mul : ∀ c c' : Fin F.s → ZMod 3, T (c + c') = T c * T c' := by
    intro c c'
    apply Subtype.ext
    change φ (F.tor (c + c')) = φ (F.tor c) * φ (F.tor c')
    rw [hdRo7CKCoordAux_tor_add F hζ3 c c', map_mul]
  let Bfun : (Fin F.s → ZMod 3) →+ (Fin n → ZMod 3) :=
    { toFun := fun c k => Multiplicative.toAdd (τ.symm (ΨS (T c)) (Fin.succ k))
      map_zero' := by
        funext k
        change Multiplicative.toAdd (τ.symm (ΨS (T 0)) (Fin.succ k)) = 0
        have hT0 : T 0 = 1 := by
          apply Subtype.ext
          change φ (F.tor 0) = (1 : G)
          rw [hdRo7CKCoordAux_tor_zero F, map_one]
        have hΨ0 : ΨS (T 0) = (1 : ↥Bs) := by
          rw [hT0]
          exact Subtype.ext rfl
        rw [hΨ0]
        simp
      map_add' := by
        intro c c'
        funext k
        change Multiplicative.toAdd (τ.symm (ΨS (T (c + c'))) (Fin.succ k)) =
          Multiplicative.toAdd (τ.symm (ΨS (T c)) (Fin.succ k)) +
            Multiplicative.toAdd (τ.symm (ΨS (T c')) (Fin.succ k))
        rw [hT_mul]
        rw [show ΨS (T c * T c') = ΨS (T c) * ΨS (T c') from rfl, map_mul]
        rfl }
  let B : (Fin F.s → ZMod 3) →ₗ[ZMod 3] (Fin n → ZMod 3) := AddMonoidHom.toZModLinearMap 3 Bfun
  have hB_inj : Function.Injective Bfun := by
    intro c c' h
    apply hT_inj
    apply Subtype.ext
    have hΨ : ΨS (T c) = ΨS (T c') := by
      apply τ.symm.injective
      funext i
      cases i using Fin.cases with
      | zero => rw [hcoord0 c, hcoord0 c']
      | succ k => exact Multiplicative.toAdd.injective (congrFun h k)
    exact congrArg (fun z : ↥Bs => (z : G)) hΨ
  have hB_surj : Function.Surjective Bfun := by
    intro u
    let f : Fin (n + 1) → Multiplicative (ZMod 3) :=
      Fin.cases 1 (fun k => Multiplicative.ofAdd (u k))
    have hf0 : f 0 = 1 := by simp [f, Fin.cases_zero]
    have hvK : (τ f : G) ∈ K := (hmem f).mpr hf0
    let v : ↥S := ⟨(τ f : G), (τ f).2, hvK⟩
    refine ⟨frameCoord v, ?_⟩
    funext k
    have hTv : T (frameCoord v) = v := hframeCoord v
    have hΨv : ΨS (T (frameCoord v)) = τ f := by rw [hTv]
    change Multiplicative.toAdd (τ.symm (ΨS (T (frameCoord v))) (Fin.succ k)) = u k
    simpa [hΨv, f, Fin.cases_succ]
  have hB_bij : Function.Bijective Bfun := ⟨hB_inj, hB_surj⟩
  let BL : (Fin F.s → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) :=
    LinearEquiv.ofBijective B hB_bij
  let u : Fin n → ZMod 3 :=
    fun k => Multiplicative.toAdd (τ.symm ⟨z, hz.1⟩ (Fin.succ k))
  have hBc : BL c = u := by
    funext k
    change Multiplicative.toAdd (τ.symm (ΨS (T c)) (Fin.succ k)) = u k
    have hTz : ΨS (T c) = ⟨z, hz.1⟩ := by
      apply Subtype.ext
      change φ (F.tor c) = z
      rw [ht, htz]
    rw [hTz]
  have hBLc : BL.symm u = c := by
    rw [← hBc]
    exact BL.symm_apply_apply c
  let e : Fin F.s ≃ Fin n := finCongr hs
  let E : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin F.s → ZMod 3) :=
    LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) e
  let β : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) := E.trans BL
  have hbetasymm : β.symm u = fun k => c (e.symm k) := by
    rw [show β.symm u = E.symm (BL.symm u) from rfl, hBLc]
    rfl
  have hcard : (Finset.univ.filter (fun k : Fin n => c (e.symm k) ≠ 0)).card =
      (Finset.univ.filter (fun j : Fin F.s => c j ≠ 0)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquiv e.symm (fun k => Iff.rfl))
  have hu : (Finset.univ.filter (fun k => β.symm u k ≠ 0)).card = 2 := by
    rw [hbetasymm, hcard]
    exact hsupp
  have hinv : ∀ (σ : Equiv.Perm (Fin n)) (cv : Fin n → ZMod 3),
      (∀ i, cv i = 1 ∨ cv i = -1) → ∀ u' : Fin n → ZMod 3,
        (Finset.univ.filter
          (fun k => β.symm (hdRo7CKCoordAux_signedPermAct σ cv u') k ≠ 0)).card =
        (Finset.univ.filter (fun k => β.symm u' k ≠ 0)).card := by
    intro σ cv hcv u'
    let σ' : Equiv.Perm (Fin (n + 1)) :=
      { toFun := fun i => Fin.cases 0 (fun k => Fin.succ (σ k)) i
        invFun := fun i => Fin.cases 0 (fun k => Fin.succ (σ.symm k)) i
        left_inv := by
          intro i
          cases i using Fin.cases with
          | zero => simp [Fin.cases_zero]
          | succ k => simp [Fin.cases_succ]
        right_inv := by
          intro i
          cases i using Fin.cases with
          | zero => simp [Fin.cases_zero]
          | succ k => simp [Fin.cases_succ] }
    let cv' : Fin (n + 1) → ZMod 3 := Fin.cases 1 (fun k => cv k)
    have hσ'0 : σ' 0 = 0 := by simp [σ', Fin.cases_zero]
    have hcv'0 : cv' 0 = 1 := by simp [cv', Fin.cases_zero]
    have hcv' : ∀ i, cv' i = 1 ∨ cv' i = -1 := by
      intro i
      cases i using Fin.cases with
      | zero => left; simp [cv', Fin.cases_zero]
      | succ k => simpa [cv', Fin.cases_succ] using hcv k
    have hε : ∀ i, cv' i * cv' i = 1 := fun i => SpCoord.coord_sign_mul_self (hcv' i)
    let gact : MulAut (Fin (n + 1) → Multiplicative (ZMod 3)) :=
      SpCoord.permAut σ' * SpCoord.diagAut cv' hε
    let a : MulAut ↥Bs := (τ.symm.trans gact).trans τ
    have ha_apply : ∀ f : Fin (n + 1) → Multiplicative (ZMod 3), a (τ f) = τ (gact f) := by
      intro f
      change τ (gact (τ.symm (τ f))) = τ (gact f)
      rw [MulEquiv.symm_apply_apply]
    have hformula : ∀ (f : Fin (n + 1) → Multiplicative (ZMod 3)) (i : Fin (n + 1)),
        Multiplicative.toAdd (τ.symm (a (τ f)) (σ' i)) =
          cv' i * Multiplicative.toAdd (f i) := by
      intro f i
      rw [ha_apply f, MulEquiv.symm_apply_apply]
      simp [gact, SpCoord.permAut_apply, SpCoord.diagAut_apply]
    have hha : a ∈ ggAutomizer K Bs :=
      (hmodel a).mpr ⟨σ', cv', hσ'0, hcv'0, hcv', hformula⟩
    have wtOn_apply : ∀ b : ↥S, wtOn (ΨS b) = (F.suppSet (frameCoord b)).card := by
      intro b
      dsimp only [wtOn]
      rw [dif_pos b.2]
    have wtOn_a : ∀ (b : ↥S) (hb' : ((a (ΨS b) : ↥Bs) : G) ∈ S),
        wtOn (a (ΨS b)) = (F.suppSet (frameCoord ⟨a (ΨS b), hb'⟩)).card := by
      intro b hb'
      dsimp only [wtOn]
      rw [dif_pos hb']
    let c_u : Fin F.s → ZMod 3 := BL.symm u'
    have hcu : BL c_u = u' := BL.apply_symm_apply u'
    have hfccu : frameCoord (T c_u) = c_u := by
      apply hT_inj
      rw [hframeCoord]
    have hBLfun : ∀ v : Fin F.s → ZMod 3, BL v = Bfun v := fun v => rfl
    have hact : ∀ (hb' : ((a (ΨS (T c_u)) : ↥Bs) : G) ∈ S),
        BL (frameCoord ⟨a (ΨS (T c_u)), hb'⟩) =
          hdRo7CKCoordAux_signedPermAct σ cv u' := by
      intro hb'
      rw [← hcu]
      funext k
      rw [hBLfun]
      change Multiplicative.toAdd
        (τ.symm (ΨS (T (frameCoord ⟨a (ΨS (T c_u)), hb'⟩))) (Fin.succ k)) =
        cv (σ.symm k) * Multiplicative.toAdd (τ.symm (ΨS (T c_u)) (Fin.succ (σ.symm k)))
      have hTfc : ΨS (T (frameCoord ⟨a (ΨS (T c_u)), hb'⟩)) = a (ΨS (T c_u)) := by
        rw [hframeCoord]
      rw [hTfc]
      have hf : τ (τ.symm (ΨS (T c_u))) = ΨS (T c_u) := MulEquiv.apply_symm_apply τ _
      have hσ'' : σ' (Fin.succ (σ.symm k)) = Fin.succ k := by simp [σ', Fin.cases_succ]
      have hcv'' : cv' (Fin.succ (σ.symm k)) = cv (σ.symm k) := by simp [cv', Fin.cases_succ]
      have hh := hformula (τ.symm (ΨS (T c_u))) (Fin.succ (σ.symm k))
      rw [hf, hσ'', hcv''] at hh
      rw [hh]
    have hEsupp : ∀ v : Fin F.s → ZMod 3,
        (Finset.univ.filter (fun k : Fin n => (E.symm v) k ≠ 0)).card =
        (Finset.univ.filter (fun j : Fin F.s => v j ≠ 0)).card := by
      intro v
      rw [show E.symm v = fun k => v (e.symm k) from rfl]
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      exact Fintype.card_congr (Equiv.subtypeEquiv e.symm (fun k => Iff.rfl))
    by_cases hab : ((a (ΨS (T c_u)) : ↥Bs) : G) ∈ S
    · have hc' := hact hab
      have hBL' : BL.symm (hdRo7CKCoordAux_signedPermAct σ cv u') =
          frameCoord ⟨a (ΨS (T c_u)), hab⟩ := by
        rw [← hc']
        exact BL.symm_apply_apply _
      have hP := hAut hha (ΨS (T c_u))
      rw [wtOn_a (T c_u) hab] at hP
      rw [wtOn_apply (T c_u), hfccu] at hP
      rw [show β.symm u' = E.symm c_u from rfl,
        show β.symm (hdRo7CKCoordAux_signedPermAct σ cv u')
            = E.symm (BL.symm (hdRo7CKCoordAux_signedPermAct σ cv u')) from rfl,
        hBL']
      rw [hEsupp (frameCoord ⟨a (ΨS (T c_u)), hab⟩), hEsupp c_u]
      simpa only [CFSG.StandardType.ChoiceTwo.SpFrame.suppSet] using hP
    · have hP := hAut hha (ΨS (T c_u))
      have hleft : wtOn (a (ΨS (T c_u))) = 0 := by
        dsimp only [wtOn]
        rw [dif_neg hab]
      rw [hleft, wtOn_apply (T c_u), hfccu] at hP
      have hP0 : (F.suppSet c_u).card = 0 := hP.symm
      have hcu0 : c_u = 0 := by
        funext i
        by_contra hi
        have : i ∈ F.suppSet c_u := F.mem_suppSet.mpr hi
        rw [Finset.card_eq_zero.mp hP0] at this
        simp at this
      have hu'0 : u' = 0 := by rw [← hcu, hcu0, map_zero]
      have hact0 : hdRo7CKCoordAux_signedPermAct σ cv u' = 0 := by
        rw [hu'0]
        funext l
        simp [hdRo7CKCoordAux_signedPermAct]
      rw [hact0, hu'0]
  have hmain : (Finset.univ.filter (fun i : Fin n => u i ≠ 0)).card = 2 :=
    hdRo7CKCoordAux_weight_two hn β hinv u hu
  obtain ⟨k1, k2, hkne, hksupp⟩ := Finset.card_eq_two.mp hmain
  have hmem : ∀ m : Fin n, u m ≠ 0 ↔ m = k1 ∨ m = k2 := by
    intro m
    have : m ∈ Finset.univ.filter (fun i : Fin n => u i ≠ 0) ↔ m = k1 ∨ m = k2 := by
      rw [hksupp, Finset.mem_insert, Finset.mem_singleton]
    simpa using this
  refine ⟨Fin.succ k1, Fin.succ k2, Fin.succ_ne_zero k1, Fin.succ_ne_zero k2,
    fun h => hkne (Fin.succ_inj.mp h), ?_⟩
  intro l hl
  have h1 : Multiplicative.toAdd (τ.symm ⟨z, hz.1⟩ l) = u (Fin.pred l hl) := by
    change Multiplicative.toAdd (τ.symm ⟨z, hz.1⟩ l) =
      Multiplicative.toAdd (τ.symm ⟨z, hz.1⟩ (Fin.succ (Fin.pred l hl)))
    rw [Fin.succ_pred]
  rw [h1, hmem (Fin.pred l hl), Fin.pred_eq_iff_eq_succ (i := l) hl,
    Fin.pred_eq_iff_eq_succ (i := l) hl]

end CFSG.StandardType.HdRo7C

end
