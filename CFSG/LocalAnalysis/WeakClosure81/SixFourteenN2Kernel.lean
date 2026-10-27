module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2FixedLine

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

theorem eq_smul_one_of_fixes_all_lines {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hfin : Module.finrank K V = 2)
    (g : V ≃ₗ[K] V) (h : ∀ L : LineOf (K := K) (V := V), lineMap g L = L) :
    ∃ c : K, ∀ v : V, g v = c • v := by
  classical
  have hdep : ∀ v : V, ¬ LinearIndependent K ![v, g v] := by
    intro v
    by_cases hv : v = 0
    · intro hli
      exact hli.ne_zero 0 (by simp [hv])
    · intro hli
      have hmem : g v ∈ Submodule.span K {v} := by
        let L : LineOf (K := K) (V := V) :=
          ⟨Submodule.span K {v}, finrank_span_singleton hv⟩
        have hL := h L
        have hmap : (Submodule.span K {v}).map (g : V →ₗ[K] V) =
            Submodule.span K {v} := by
          have hval := congrArg Subtype.val hL
          rwa [lineMap_apply g L] at hval
        rw [← hmap]
        exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self v)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      rw [LinearIndependent.pair_iff' hv] at hli
      exact hli c hc
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := (g : V →ₗ[K] V)) hdep
  refine ⟨c, fun v => ?_⟩
  have hv := congrArg (fun f : V →ₗ[K] V => f v) hc
  simpa using hv

theorem x_fixes_all_lines_of_transitive {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H : Subgroup (MulAut W)}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hxgen : X = Subgroup.zpowers x)
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (htrans : letI := galoisModule hw2 x hx3 hfix;
      ∀ L M : LineOf (K := GaloisField 2 2) (V := Additive W),
        ∃ h : ↥H, lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = M) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ L : LineOf (K := GaloisField 2 2) (V := Additive W),
      lineMap (hGaloisLinearEquiv hw2 x hx3 hfix x (by rfl)) L = L := by
  letI := galoisModule hw2 x hx3 hfix
  let gx := hGaloisLinearEquiv hw2 x hx3 hfix x (by rfl)
  let S : Set (LineOf (K := GaloisField 2 2) (V := Additive W)) :=
    {L | lineMap gx L = L}
  have hcard5 : Nat.card (LineOf (K := GaloisField 2 2) (V := Additive W)) = 5 :=
    card_f4Line hw2 x hx3 hfix hW
  have hScard : S.ncard = 2 ∨ S.ncard = 5 :=
    x_line_fixed_eq_two_or_five hw2 x hx3 hfix hW
  haveI : Finite (LineOf (K := GaloisField 2 2) (V := Additive W)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard5]; norm_num)
  have hline_trans : ∀ (e f : Additive W ≃ₗ[GaloisField 2 2] Additive W)
      (L : LineOf (K := GaloisField 2 2) (V := Additive W)),
      lineMap (e.trans f) L = lineMap f (lineMap e L) := by
    intro e f L
    change (e.trans f) • L = f • (e • L)
    rw [show e.trans f = f * e from (LinearEquiv.mul_eq_trans f e).symm]
    exact mul_smul f e L
  have hGE_congr : ∀ {a : MulAut W} (hc1 hc2 : a * x = x * a),
      hGaloisLinearEquiv hw2 x hx3 hfix a hc1 =
        hGaloisLinearEquiv hw2 x hx3 hfix a hc2 := by
    intro a hc1 hc2
    exact congrArg (fun hc => hGaloisLinearEquiv hw2 x hx3 hfix a hc)
      (Subsingleton.elim hc1 hc2)
  have hGE_congr_eq : ∀ {a b : MulAut W} (hab : a = b)
      (hc1 : a * x = x * a) (hc2 : b * x = x * b),
      hGaloisLinearEquiv hw2 x hx3 hfix a hc1 =
        hGaloisLinearEquiv hw2 x hx3 hfix b hc2 := by
    intro a b hab hc1 hc2
    subst b
    exact hGE_congr hc1 hc2
  have hS_univ : S = Set.univ := by
    rcases hScard with h2 | h5
    · exfalso
      have hne : S.Nonempty := by
        rw [Set.ncard_eq_two] at h2
        obtain ⟨L, M, hLM, hSeq⟩ := h2
        exact ⟨L, by rw [hSeq]; simp⟩
      obtain ⟨L₀, hL₀⟩ := hne
      have huniv : S = Set.univ := by
        apply Set.eq_univ_of_forall
        intro M
        obtain ⟨h, hh⟩ := htrans L₀ M
        let gh : Additive W ≃ₗ[GaloisField 2 2] Additive W :=
          HLinHom hw2 x hx3 hfix H hcommH h
        have hgh : gh = hGaloisLinearEquiv hw2 x hx3 hfix (h : MulAut W)
            (hcommH h h.2) := HLinHom_apply hw2 x hx3 hfix H hcommH h
        have hch : Commute (h : MulAut W) x := hcommH h h.2
        have hc1 : ((h : MulAut W) * x) * x = x * ((h : MulAut W) * x) :=
          (hch.mul_left (Commute.refl x)).eq
        have hc2 : (x * (h : MulAut W)) * x = x * (x * (h : MulAut W)) :=
          ((Commute.refl x).mul_left hch).eq
        have hmul1 := hGaloisLinearEquiv_mul hw2 x hx3 hfix (h : MulAut W) x
          (hcommH h h.2) (by rfl) hc1
        have hmul2 := hGaloisLinearEquiv_mul hw2 x hx3 hfix x (h : MulAut W)
          (by rfl) (hcommH h h.2) hc2
        have hcongr : hGaloisLinearEquiv hw2 x hx3 hfix
              ((h : MulAut W) * x) hc1 =
            hGaloisLinearEquiv hw2 x hx3 hfix
              (x * (h : MulAut W)) hc2 :=
          hGE_congr_eq (hcommH h h.2) hc1 hc2
        have hcomm_gh : gh.trans gx = gx.trans gh := by
          rw [hgh]
          calc (hGaloisLinearEquiv hw2 x hx3 hfix (h : MulAut W) (hcommH h h.2)).trans gx
              = hGaloisLinearEquiv hw2 x hx3 hfix
                  (x * (h : MulAut W)) hc2 := hmul2.symm
            _ = hGaloisLinearEquiv hw2 x hx3 hfix
                  ((h : MulAut W) * x) hc1 := hcongr.symm
            _ = gx.trans
                  (hGaloisLinearEquiv hw2 x hx3 hfix (h : MulAut W) (hcommH h h.2)) :=
                hmul1
        have hM : lineMap gx M = M := by
          rw [← hh]
          calc lineMap gx (lineMap gh L₀)
              = lineMap (gh.trans gx) L₀ := (hline_trans gh gx L₀).symm
            _ = lineMap (gx.trans gh) L₀ := by rw [hcomm_gh]
            _ = lineMap gh (lineMap gx L₀) := hline_trans gx gh L₀
            _ = lineMap gh L₀ := by rw [show lineMap gx L₀ = L₀ from hL₀]
        exact hM
      rw [huniv, Set.ncard_univ, hcard5] at h2
      omega
    · exact (Set.eq_univ_iff_ncard S).mpr (by rw [h5, hcard5])
  intro L
  have hL : L ∈ S := by rw [hS_univ]; exact Set.mem_univ L
  exact hL

theorem X_fixes_all_lines_of_transitive {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H : Subgroup (MulAut W)}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hxgen : X = Subgroup.zpowers x)
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (htrans : letI := galoisModule hw2 x hx3 hfix;
      ∀ L M : LineOf (K := GaloisField 2 2) (V := Additive W),
        ∃ h : ↥H, lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = M) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ (a : MulAut W) (_ha : a ∈ X)
      (L : LineOf (K := GaloisField 2 2) (V := Additive W)),
      lineMap (hGaloisLinearEquiv hw2 x hx3 hfix a (by
        have ha' : a ∈ Subgroup.zpowers x := by rwa [← hxgen]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha'
        rw [← hk]
        exact (Commute.zpow_self (a := x) (n := k)).eq)) L = L := by
  letI := galoisModule hw2 x hx3 hfix
  let gx := hGaloisLinearEquiv hw2 x hx3 hfix x (by rfl)
  have hxfix : ∀ L : LineOf (K := GaloisField 2 2) (V := Additive W),
      lineMap gx L = L :=
    x_fixes_all_lines_of_transitive hw2 x hx3 hfix hW hH hxgen hcommH htrans
  have hxX : x ∈ X := by
    rw [hxgen]
    exact Subgroup.mem_zpowers x
  have hcommX : ∀ (a : MulAut W) (_ha : a ∈ X), a * x = x * a := by
    intro a ha
    have ha' : a ∈ Subgroup.zpowers x := by rwa [← hxgen]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha'
    rw [← hk]
    exact (Commute.zpow_self (a := x) (n := k)).eq
  have hGE_congr : ∀ {a : MulAut W} (hc1 hc2 : a * x = x * a),
      hGaloisLinearEquiv hw2 x hx3 hfix a hc1 =
        hGaloisLinearEquiv hw2 x hx3 hfix a hc2 := by
    intro a hc1 hc2
    exact congrArg (fun hc => hGaloisLinearEquiv hw2 x hx3 hfix a hc)
      (Subsingleton.elim hc1 hc2)
  let Φ : ↥X →* (Additive W ≃ₗ[GaloisField 2 2] Additive W) :=
    { toFun := fun a => hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W) (hcommX a a.2)
      map_one' := by
        change hGaloisLinearEquiv hw2 x hx3 hfix (1 : MulAut W)
            (hcommX 1 (Subgroup.one_mem X)) =
          (1 : Additive W ≃ₗ[GaloisField 2 2] Additive W)
        rw [hGE_congr (hcommX 1 (Subgroup.one_mem X)) (by group)]
        exact hGaloisLinearEquiv_one hw2 x hx3 hfix (by group)
      map_mul' := by
        intro a b
        change hGaloisLinearEquiv hw2 x hx3 hfix
            ((a : MulAut W) * (b : MulAut W)) (hcommX (a * b) (X.mul_mem a.2 b.2)) =
          hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W) (hcommX a a.2) *
            hGaloisLinearEquiv hw2 x hx3 hfix (b : MulAut W) (hcommX b b.2)
        rw [hGE_congr (hcommX (a * b) (X.mul_mem a.2 b.2))
          (by
            have hca : Commute (a : MulAut W) x := hcommX a a.2
            have hcb : Commute (b : MulAut W) x := hcommX b b.2
            exact (hca.mul_left hcb).eq)]
        rw [hGaloisLinearEquiv_mul hw2 x hx3 hfix (a : MulAut W) (b : MulAut W)
          (hcommX a a.2) (hcommX b b.2) (hcommX (a * b) (X.mul_mem a.2 b.2))]
        rfl }
  let Λ : ↥X →* Equiv.Perm (LineOf (K := GaloisField 2 2) (V := Additive W)) :=
    (MulAction.toPermHom (Additive W ≃ₗ[GaloisField 2 2] Additive W)
      (LineOf (K := GaloisField 2 2) (V := Additive W))).comp Φ
  have hΛapply : ∀ (a : ↥X) (L : LineOf (K := GaloisField 2 2) (V := Additive W)),
      Λ a L = lineMap (Φ a) L := by
    intro a L
    rfl
  have hΛx : Λ ⟨x, hxX⟩ = 1 := by
    apply Equiv.ext
    intro L
    rw [hΛapply]
    change lineMap (Φ ⟨x, hxX⟩) L = L
    have hΦx : Φ ⟨x, hxX⟩ = gx := by
      change hGaloisLinearEquiv hw2 x hx3 hfix x (hcommX x hxX) =
        hGaloisLinearEquiv hw2 x hx3 hfix x (by rfl)
      exact hGE_congr (hcommX x hxX) (by rfl)
    rw [hΦx]
    exact hxfix L
  intro a ha L
  have hΛa : Λ ⟨a, ha⟩ = 1 := by
    have ha' : a ∈ Subgroup.zpowers x := by rwa [← hxgen]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha'
    have hsub : (⟨x, hxX⟩ : ↥X) ^ k = ⟨a, ha⟩ := by
      apply Subtype.ext
      simpa using hk
    rw [← hsub, map_zpow, hΛx, one_zpow]
  have hfin : lineMap (hGaloisLinearEquiv hw2 x hx3 hfix a (hcommX a ha)) L = L := by
    have h := congrArg
      (fun e : Equiv.Perm (LineOf (K := GaloisField 2 2) (V := Additive W)) => e L)
      hΛa
    rw [hΛapply] at h
    change lineMap (hGaloisLinearEquiv hw2 x hx3 hfix a (hcommX a ha)) L = L at h
    exact h
  rwa [hGE_congr (hcommX a ha) (by
    have ha' : a ∈ Subgroup.zpowers x := by rwa [← hxgen]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha'
    rw [← hk]
    exact (Commute.zpow_self (a := x) (n := k)).eq)] at hfin

theorem X_scalar_of_transitive {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H : Subgroup (MulAut W)}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hxgen : X = Subgroup.zpowers x)
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (htrans : letI := galoisModule hw2 x hx3 hfix;
      ∀ L M : LineOf (K := GaloisField 2 2) (V := Additive W),
        ∃ h : ↥H, lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = M) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ (a : MulAut W) (_ha : a ∈ X), ∃ c : GaloisField 2 2, ∀ v : Additive W,
      hGaloisLinearEquiv hw2 x hx3 hfix a (by
        have ha' : a ∈ Subgroup.zpowers x := by rwa [← hxgen]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha'
        rw [← hk]
        exact (Commute.zpow_self (a := x) (n := k)).eq) v = c • v := by
  letI := galoisModule hw2 x hx3 hfix
  intro a ha
  refine eq_smul_one_of_fixes_all_lines
    (finrank_galoisModule hw2 x hx3 hfix hW)
    (hGaloisLinearEquiv hw2 x hx3 hfix a (by
      have ha' : a ∈ Subgroup.zpowers x := by rwa [← hxgen]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha'
      rw [← hk]
      exact (Commute.zpow_self (a := x) (n := k)).eq)) ?_
  intro L
  exact X_fixes_all_lines_of_transitive hw2 x hx3 hfix hW hH hxgen hcommH htrans a ha L

end CFSG.LocalAnalysis.WeakClosure81
