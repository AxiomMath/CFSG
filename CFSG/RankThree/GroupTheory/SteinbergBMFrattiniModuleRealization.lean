module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniMaschke
public import CFSG.RankThree.GroupTheory.SteinbergBMTwoCommutatorLift
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem smul_mem_actionCommutator_of_normal {L X : Type*} [Group L] [Group X]
    [MulDistribMulAction L X] {N : Subgroup L} (hN : N.Normal) {V : Subgroup X}
    (hV : ∀ l : L, ∀ x ∈ V, l • x ∈ V) (l : L) {x : X} (hx : x ∈ actionCommutator N V) :
    l • x ∈ actionCommutator N V := by
  have hle : actionCommutator N V ≤
      (actionCommutator N V).comap (MulDistribMulAction.toMonoidHom X l) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨v, hv, n, rfl⟩
    change l • (v⁻¹ * (n • v)) ∈ actionCommutator N V
    have hn : l * (n : L) * l⁻¹ ∈ N := hN.conj_mem _ n.2 l
    have e : l • (v⁻¹ * (n • v)) = (l • v)⁻¹ * ((⟨l * n * l⁻¹, hn⟩ : N) • (l • v)) := by
      rw [smul_mul', smul_inv']
      change (l • v)⁻¹ * (l • ((n : L) • v)) = (l • v)⁻¹ * ((l * n * l⁻¹) • (l • v))
      rw [smul_smul, smul_smul, inv_mul_cancel_right]
    rw [e]
    exact gen_mem_actionCommutator (hV l v hv) _
  exact hle hx

theorem invariant_frattini_module_realization {q : ℕ} (hq : q.Prime) {L D : Type*} [Group L]
    [Group D] [Finite L] [Finite D] [MulDistribMulAction L D] (hD : IsPGroup q D)
    (hL : ¬ q ∣ Nat.card L) :
    letI : MulDistribMulAction L (D ⧸ frattini D) :=
      CFSG.quotientMulDistribMulAction (A := L) (G := D) (frattini D)
        (CFSG.isInvariant_of_characteristic (A := L) (G := D) (frattini D))
    ∀ W : Subgroup (D ⧸ frattini D), W ≠ ⊥ → (∀ l : L, ∀ w ∈ W, l • w ∈ W) →
      (∀ W' : Subgroup (D ⧸ frattini D), W' ≤ W → (∀ l : L, ∀ w ∈ W', l • w ∈ W') →
        W' = ⊥ ∨ W' = W) →
      ∃ X : Subgroup D, (∀ l : L, ∀ x ∈ X, l • x ∈ X) ∧
        X.map (QuotientGroup.mk' (frattini D)) = W ∧
        X ⊓ frattini D = (frattini X).map X.subtype ∧
        (∃ e : X ⧸ frattini X ≃* W, (∀ x : X, (e x : D ⧸ frattini D) = (x : D)) ∧
          ∀ (l : L) (x : X) (hlx : l • (x : D) ∈ X),
            (e (⟨l • (x : D), hlx⟩ : X) : D ⧸ frattini D) = l • (e x : D ⧸ frattini D)) ∧
        (∀ l : L, (∀ x ∈ X, l • x = x) ↔ ∀ w ∈ W, l • w = w) ∧
        (∀ X' : Subgroup D, X' ≤ X → (∀ l : L, ∀ x ∈ X', l • x ∈ X') →
          X'.map (QuotientGroup.mk' (frattini D)) = W → X' = X) ∧
        ∀ N : Subgroup L, N.Normal → (∃ n ∈ N, ∃ w ∈ W, n • w ≠ w) →
          actionCommutator N X = X := by
  let : MulDistribMulAction L (D ⧸ frattini D) :=
    CFSG.quotientMulDistribMulAction (A := L) (G := D) (frattini D)
      (CFSG.isInvariant_of_characteristic (A := L) (G := D) (frattini D))
  intro W hW1 hWinv hWirr
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q D) := ⟨hD⟩
  set Φ := frattini D with hΦdef
  have hΦinv : CFSG.IsInvariant L D Φ :=
    CFSG.isInvariant_of_characteristic (A := L) (G := D) Φ
  let : MulAction.QuotientAction L Φ := CFSG.quotientAction_of_isInvariant (A := L) Φ hΦinv
  set π := QuotientGroup.mk' Φ with hπdef
  have hπL : ∀ (l : L) (x : D), π (l • x) = l • π x := fun l x =>
    (MulAction.Quotient.smul_coe (H := Φ) l x).symm
  have hcop : Nat.Coprime q (Nat.card L) := (Nat.Prime.coprime_iff_not_dvd hq).mpr hL
  have hFcomm : IsMulCommutative (D ⧸ Φ) :=
    (CFSG.isElementaryAbelian_quotient_frattini (p := q) (R := D)).toIsMulCommutative
  set T : Set (Subgroup D) := {X | (∀ l : L, ∀ x ∈ X, l • x ∈ X) ∧ X.map π = W} with hT
  have hTne : W.comap π ∈ T := ⟨fun l x hx => by
      show π (l • x) ∈ W
      rw [hπL]
      exact hWinv l _ hx,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Φ) W⟩
  obtain ⟨X, ⟨hXinv, hXW⟩, hXmin'⟩ :=
    (measure fun X : Subgroup D => Nat.card X).wf.has_min T ⟨_, hTne⟩
  have hXmin : ∀ X' : Subgroup D, X' ≤ X → (∀ l : L, ∀ x ∈ X', l • x ∈ X') → X'.map π = W →
      X' = X := fun X' hX'X hX'inv hX'W =>
    eq_of_le_of_card_ge hX'X (not_lt.mp (hXmin' X' ⟨hX'inv, hX'W⟩))
  have : CFSG.IsInvariant L D X := ⟨fun l g => ⟨fun hg => hXinv l g hg, fun hg => by
    have := hXinv l⁻¹ _ hg
    rwa [inv_smul_smul] at this⟩⟩
  have hXq : IsPGroup q X := hD.to_subgroup X
  have : Fact (IsPGroup q X) := ⟨hXq⟩
  have hcommker : _root_.commutator X ≤ (π.comp X.subtype).ker := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hFcomm.is_comm.comm _ _
  have hΦXker : frattini X ≤ (π.comp X.subtype).ker := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := q), closure_le]
    rintro y (hy | ⟨z, rfl⟩)
    · exact hcommker hy
    · show π ((z ^ q : X) : D) = 1
      rw [coe_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (CFSG.pth_power_mem_frattini_of_isPGroup (p := q) _)
  have hΦX : (frattini X).map X.subtype ≤ X ⊓ Φ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, (QuotientGroup.eq_one_iff _).mp (hΦXker hx)⟩
  set W₀ : Subgroup X := Φ.comap X.subtype with hW₀
  have hW₀n : W₀.Normal := Subgroup.Normal.comap inferInstance X.subtype
  obtain ⟨W₂, -, hW₂inv, hsup, hinf⟩ := exists_invariant_complement_section (p := q) (A := L)
    (P := X) hcop (N := frattini X) (W := W₀) (fun x hx => (hΦX ⟨x, hx, rfl⟩).2)
    (fun x => CFSG.pth_power_mem_frattini_of_isPGroup (p := q) x)
    (fun x y => CFSG.commutator_le_frattini_of_isPGroup (p := q)
      (commutator_mem_commutator (mem_top x) (mem_top y)))
    (fun l x hx => ((CFSG.isInvariant_of_characteristic (A := L) (G := X) (frattini X)).invariant
      l x).1 hx)
    (fun l x hx => (hΦinv.invariant l x).1 hx)
  have hW₂'inv : ∀ l : L, ∀ x ∈ W₂.map X.subtype, l • x ∈ W₂.map X.subtype := by
    rintro l _ ⟨y, hy, rfl⟩
    exact ⟨l • y, hW₂inv l y hy, rfl⟩
  have hW₂W : (W₂.map X.subtype).map π = W := by
    refine le_antisymm ((map_mono (map_subtype_le W₂)).trans hXW.le) ?_
    rw [← hXW]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (⟨x, hx⟩ : X) ∈ ((W₀ ⊔ W₂ : Subgroup X) : Set X) := by
      rw [hsup]
      exact mem_top _
    rw [normal_mul W₀ W₂] at hx'
    obtain ⟨y, hy, z, hz, hyz⟩ := hx'
    refine ⟨z, ⟨z, hz, rfl⟩, ?_⟩
    have hxyz : x = (y : D) * z := (congrArg Subtype.val hyz).symm
    show π (z : D) = π x
    have hπy : π (y : D) = 1 := (QuotientGroup.eq_one_iff _).mpr hy
    rw [hxyz, map_mul, hπy, one_mul]
  have hW₂top : W₂ = ⊤ := by
    have h := hXmin _ (map_subtype_le W₂) hW₂'inv hW₂W
    apply map_injective X.subtype_injective
    rw [h, ← MonoidHom.range_eq_map, range_subtype]
  rw [hW₂top, inf_top_eq] at hinf
  have hXΦ : X ⊓ Φ = (frattini X).map X.subtype := by
    rw [← hinf, hW₀, map_comap_eq, range_subtype, inf_comm]
  have hfW : ∀ x : X, (π.comp X.subtype) x ∈ W := fun x => hXW ▸ ⟨x, x.2, rfl⟩
  set f : X →* W := (π.comp X.subtype).codRestrict W hfW with hfdef
  have hfs : Function.Surjective f := by
    rintro ⟨w, hw⟩
    rw [← hXW] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    exact ⟨⟨x, hx⟩, rfl⟩
  have hfker : f.ker = frattini X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : π (x : D) = 1 := congrArg Subtype.val h
      have h2 : (x : D) ∈ X ⊓ Φ := ⟨x.2, (QuotientGroup.eq_one_iff _).mp h1⟩
      rw [hXΦ] at h2
      obtain ⟨y, hy, hyx⟩ := h2
      rwa [← Subtype.ext hyx]
    · intro hx
      exact Subtype.ext (hΦXker hx)
  set e : X ⧸ frattini X ≃* W := (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs) with hedef
  have he : ∀ x : X, (e x : D ⧸ Φ) = (x : D) := fun x => rfl
  refine ⟨X, hXinv, hXW, hXΦ, ⟨e, he, fun l x hlx => ?_⟩,
    fun l => ⟨fun hl w hw => ?_, fun hl => ?_⟩, hXmin, fun N hN ⟨n, hn, w, hw, hnw⟩ => ?_⟩
  ·
    rw [he, he]
    exact hπL l x
  ·
    rw [← hXW] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    rw [← hπL, hl x hx]
  ·
    set σ := MulDistribMulAction.toMulAut L X l with hσ
    have hkerK := CFSG.GroupTheory.frattini_automorphism_kernel (p := q) hXq
    have hσker : σ ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
        (frattini X)).ker := by
      rw [MonoidHom.mem_ker]
      ext y
      induction y using QuotientGroup.induction_on with
      | H x =>
        rw [hkerK.1 σ x, MulAut.one_apply]
        apply e.injective
        apply Subtype.ext
        rw [he, he]
        show π (l • (x : D)) = π x
        rw [hπL]
        exact hl _ (hXW ▸ ⟨x, x.2, rfl⟩)
    obtain ⟨k, hk⟩ := hkerK.2 ⟨σ, hσker⟩
    have hσk : σ ^ q ^ k = 1 := congrArg Subtype.val hk
    have hσo : σ ^ orderOf l = 1 := by
      rw [hσ, ← map_pow, pow_orderOf_eq_one, map_one]
    have hcopk : Nat.Coprime (q ^ k) (orderOf l) :=
      Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard l) hcop)
    have hσ1 : σ = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcopk
      (orderOf_dvd_of_pow_eq_one hσk) (orderOf_dvd_of_pow_eq_one hσo))
    intro x hx
    have h := congrArg (fun τ : MulAut X => ((τ ⟨x, hx⟩ : X) : D)) hσ1
    exact h
  ·
    have hWNinv : ∀ a : N, ∀ v ∈ W, a • v ∈ W := fun a v hv => hWinv a v hv
    have hWN : actionCommutator N W = W := by
      rcases hWirr (actionCommutator N W) (actionCommutator_le_of_invariant hWNinv)
        (fun l v hv => smul_mem_actionCommutator_of_normal hN hWinv l hv) with h | h
      · exfalso
        apply hnw
        have hgen := gen_mem_actionCommutator (A := N) hw ⟨n, hn⟩
        rw [h, mem_bot] at hgen
        have h' : w⁻¹ * ((n : L) • w) = 1 := hgen
        rw [inv_mul_eq_one] at h'
        exact h'.symm
      · exact h
    refine hXmin _ (actionCommutator_le_of_invariant fun a x hx => hXinv a x hx)
      (fun l x hx => smul_mem_actionCommutator_of_normal hN hXinv l hx) ?_
    rw [map_actionCommutator (A := N) π (fun a x => hπL a x), hXW, hWN]

end CFSG.RankThree.GroupTheory.SteinbergBM
