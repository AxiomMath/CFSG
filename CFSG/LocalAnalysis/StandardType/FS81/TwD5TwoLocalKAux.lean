module

public import CFSG.LocalAnalysis.StandardType.FS81.OrthMaxTorus
public import CFSG.LocalAnalysis.StandardType.FS81.RowElemAbOrth
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthModels
public import CFSG.LinearAlgebra.CoprimeActions.BinaryFixedVectors
public import CFSG.ClassicalGroups.Orthogonal.InvariantPairing
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.S12.LA126Aux
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap

public section

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.GroupTheory.WeirSylow CFSG.LieType.Universal.Spin
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

@[expose] noncomputable def planeProj (Q : QuadraticForm (ZMod 2) V) (p : V × V) (x : V) : V :=
  rot Q p.1 p.2 x + rot Q p.1 p.2 (rot Q p.1 p.2 x)

theorem planeSpan_le_omegaSpace {p : V × V} (hp : MinusPair Q p.1 p.2) :
    planeSpan p ≤ omegaSpace (rot Q p.1 p.2) := by
  refine Submodule.span_le.2 ?_
  intro z hz
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · refine mem_omegaSpace.2 ?_
    have h1 : rot Q p.1 p.2 (rot Q p.1 p.2 p.1) = p.1 + p.2 := by
      rw [rot_apply_left hp, rot_apply_right hp]
    rw [h1, rot_apply_left hp]
    linear_combination (norm := module) vec_add_self p.1 + vec_add_self p.2
  · refine mem_omegaSpace.2 ?_
    have h1 : rot Q p.1 p.2 (rot Q p.1 p.2 p.2) = p.1 := by
      rw [rot_apply_right hp, map_add, rot_apply_left hp, rot_apply_right hp]
      linear_combination (norm := module) vec_add_self p.2
    rw [h1, rot_apply_right hp]
    linear_combination (norm := module) vec_add_self p.1 + vec_add_self p.2

theorem planeProj_add (p : V × V) (x y : V) :
    planeProj Q p (x + y) = planeProj Q p x + planeProj Q p y := by
  simp only [planeProj, map_add]
  abel

theorem planeProj_eq_zero_of_polar_eq_zero {p : V × V} (hp : MinusPair Q p.1 p.2) {x : V}
    (h1 : polar Q x p.1 = 0) (h2 : polar Q x p.2 = 0) : planeProj Q p x = 0 := by
  rw [planeProj]
  simp only [rot_apply_of_perp hp h1 h2]
  exact vec_add_self x

theorem planeProj_eq_self_of_mem_planeSpan {p : V × V} (hp : MinusPair Q p.1 p.2) {x : V}
    (hx : x ∈ planeSpan p) : planeProj Q p x = x := by
  rw [planeProj, omegaSpace_rel (planeSpan_le_omegaSpace hp hx)]
  linear_combination (norm := module) vec_add_self (rot Q p.1 p.2 x)

theorem planeProj_mem_planeSpan {p : V × V} (hp : MinusPair Q p.1 p.2) (x : V) :
    planeProj Q p x ∈ planeSpan p := by
  have hmem : rot Q p.1 p.2 x + x ∈ planeSpan p := by
    have h := rot_sub_mem_span hp x
    rwa [sub_eq_add_neg, vec_neg] at h
  have heq : planeProj Q p x = rot Q p.1 p.2 (rot Q p.1 p.2 x + x) := by
    rw [planeProj, map_add]
    abel
  rw [heq]
  simpa using rot_pow_mem_planeSpan hp 1 hmem

theorem polar_eq_zero_of_mem_planeSpan_of_pairPerp {p q : V × V} (hpq : PairPerp Q p q)
    {u : V} (hu : u ∈ planeSpan p) : polar Q u q.1 = 0 ∧ polar Q u q.2 = 0 := by
  obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p u).1 hu
  simp [polar_add_left, polar_smul_left, hpq.1, hpq.2.1, hpq.2.2.1, hpq.2.2.2]

theorem rot_apply_linear_combo {p : V × V} (hp : MinusPair Q p.1 p.2) (c d : ZMod 2) :
    rot Q p.1 p.2 (c • p.1 + d • p.2) = d • p.1 + (c + d) • p.2 := by
  rw [map_add, map_smul, map_smul, rot_apply_left hp, rot_apply_right hp]
  module

theorem planeSpan_le_of_mem_of_rot_mem {p : V × V} (hp : MinusPair Q p.1 p.2)
    {S : Submodule (ZMod 2) V} {y : V} (hyp : y ∈ planeSpan p) (hy0 : y ≠ 0)
    (hyS : y ∈ S) (hryS : rot Q p.1 p.2 y ∈ S) : planeSpan p ≤ S := by
  obtain ⟨c, d, hcd⟩ := (mem_planeSpan_iff p y).1 hyp
  have hrot : rot Q p.1 p.2 y = d • p.1 + (c + d) • p.2 := by
    rw [← hcd, rot_apply_linear_combo hp]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have ha : p.1 ∈ S := by
    rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases d with rfl | rfl
    · simp only [zero_smul, add_zero] at hcd
      exact absurd hcd.symm hy0
    · simp only [zero_smul, one_smul, zero_add] at hcd hrot
      rw [show p.1 = rot Q p.1 p.2 y + y by
        rw [hrot, ← hcd, add_assoc, vec_add_self, add_zero]]
      exact S.add_mem hryS hyS
    · simp only [zero_smul, one_smul, zero_add, add_zero] at hcd hrot
      rw [hcd]
      exact hyS
    · simp only [zero_smul, one_smul, add_zero, h11] at hcd hrot
      rw [← hrot]
      exact hryS
  have hb : p.2 ∈ S := by
    rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases d with rfl | rfl
    · simp only [zero_smul, add_zero] at hcd
      exact absurd hcd.symm hy0
    · simp only [zero_smul, one_smul, zero_add] at hcd hrot
      rw [hcd]
      exact hyS
    · simp only [zero_smul, one_smul, zero_add, add_zero] at hcd hrot
      rw [← hrot]
      exact hryS
    · simp only [zero_smul, one_smul, add_zero, h11] at hcd hrot
      rw [show p.2 = y + rot Q p.1 p.2 y by
        rw [hrot, ← hcd, add_comm (p.1 + p.2) p.1, ← add_assoc, vec_add_self, zero_add]]
      exact S.add_mem hyS hryS
  refine Submodule.span_le.2 ?_
  intro z hz
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact ha
  · exact hb

theorem sum_planeProj_eq_self {l : List (V × V)} (hl : IsFrame Q l) :
    ∀ x ∈ Wspan l, x = (l.map (fun p => planeProj Q p x)).sum := by
  induction l with
  | nil =>
    intro x hx
    rw [Wspan_nil, Submodule.mem_bot] at hx
    simp [hx]
  | cons p l ih =>
    intro x hx
    obtain ⟨hp, hperp, hl'⟩ := isFrame_cons.1 hl
    rw [Wspan_cons] at hx
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    have hpu : planeProj Q p u = u := planeProj_eq_self_of_mem_planeSpan hp hu
    have hpw : planeProj Q p w = 0 := by
      obtain ⟨h1, h2⟩ := polar_Wspan_eq_zero hperp hw
      exact planeProj_eq_zero_of_polar_eq_zero hp (by rwa [polar_comm]) (by rwa [polar_comm])
    have huq : ∀ q ∈ l, planeProj Q q u = 0 := by
      intro q hq
      obtain ⟨h1, h2⟩ := polar_eq_zero_of_mem_planeSpan_of_pairPerp (hperp q hq) hu
      exact planeProj_eq_zero_of_polar_eq_zero (hl.pair q (List.mem_cons_of_mem _ hq)) h1 h2
    have hmap : l.map (fun q => planeProj Q q (u + w)) = l.map (fun q => planeProj Q q w) := by
      apply List.map_congr_left
      intro q hq
      rw [planeProj_add, huq q hq, zero_add]
    rw [List.map_cons, List.sum_cons, hmap, planeProj_add, hpu, hpw, add_zero,
      ← ih hl' w hw]

theorem eq_zero_of_forall_polar_eq_zero {l : List (V × V)} (hl : IsFrame Q l)
    (hspan : Wspan l = ⊤) {S : Submodule (ZMod 2) V}
    (hSinv : ∀ p ∈ l, ∀ x ∈ S, rot Q p.1 p.2 x ∈ S) {x : V} (hxS : x ∈ S)
    (hxper : ∀ y ∈ S, polar Q x y = 0) : x = 0 := by
  have hsum := sum_planeProj_eq_self hl x (by rw [hspan]; exact Submodule.mem_top)
  rw [hsum]
  have hzero : ∀ p ∈ l, planeProj Q p x = 0 := by
    intro p hp
    by_contra hne
    have heS : planeProj Q p x ∈ S := by
      rw [planeProj]
      exact S.add_mem (hSinv p hp x hxS) (hSinv p hp _ (hSinv p hp x hxS))
    have hplane : planeSpan p ≤ S :=
      planeSpan_le_of_mem_of_rot_mem (hl.pair p hp) (planeProj_mem_planeSpan (hl.pair p hp) x)
        hne heS (hSinv p hp _ heS)
    exact hne (planeProj_eq_zero_of_polar_eq_zero (hl.pair p hp)
      (hxper p.1 (hplane (left_mem_planeSpan p)))
      (hxper p.2 (hplane (right_mem_planeSpan p))))
  have hmap : l.map (fun p => planeProj Q p x) = l.map (fun _ => (0 : V)) := by
    apply List.map_congr_left
    intro p hp
    exact hzero p hp
  have hsum0 : (l.map (fun _ => (0 : V))).sum = 0 := by
    induction l with
    | nil => rfl
    | cons p l ih => simp [List.sum_cons]
  rw [hmap, hsum0]

theorem card_le_three_pow_pred_of_normalizes [FiniteDimensional (ZMod 2) V]
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n)
    (htype : IsPlusType Q ↔ Even n)
    {A T : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hAΩ : A ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) (hA : IsElemAbelian 3 A)
    (hTΩ : T ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) (hT2 : IsPGroup 2 T) (hTne : T ≠ ⊥)
    (hN : A ≤ Subgroup.normalizer (T : Set (V ≃ₗ[ZMod 2] V))) :
    Nat.card A ≤ 3 ^ (n - 1) := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun e f h => LinearEquiv.ext (congrFun h))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hΩO : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.commutator_le_self _
  have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hAΩ.trans hΩO
  have hTO : T ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hTΩ.trans hΩO
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using orth_card_elemAb3_le hQ hdim hAO hA
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
  by_contra hcon
  push Not at hcon
  have hle : Nat.card A ≤ 3 ^ n := orth_card_elemAb3_le hQ hdim hAO hA
  obtain ⟨k, hk⟩ := hA.isPGroup.exists_card_eq
  have hk1 : n - 1 < k := by
    rw [hk] at hcon
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hcon
  have hk2 : k ≤ n := by
    rw [hk] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
  have hkn : k = n := by omega
  have hcard : Nat.card A = 3 ^ n := by rw [hk, hkn]
  have hmax : ∀ E' : Subgroup (V ≃ₗ[ZMod 2] V),
      E' ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      IsElemAbelian 3 E' → A ≤ E' → E' = A := by
    intro E' hE'Ω hE' hAE'
    have h1 : Nat.card E' ≤ 3 ^ n := orth_card_elemAb3_le hQ hdim (hE'Ω.trans hΩO) hE'
    have h2 : Nat.card E' ≤ Nat.card A := by rw [hcard]; exact h1
    exact (Subgroup.eq_of_le_of_card_ge hAE' h2).symm
  obtain ⟨l, hl, hlen, hAe⟩ := fs81_orth_maxElemAb3_eq_torus hQ hdim htype hAΩ hA hmax
  have hspan : Wspan l = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hl.finrank_Wspan, hlen, hdim]
  have hSinv : ∀ p ∈ l, ∀ x ∈ CFSG.RankThree.PartOne.LA126.fixedSubmodule T,
      rot Q p.1 p.2 x ∈ CFSG.RankThree.PartOne.LA126.fixedSubmodule T := by
    intro p hp x hx
    rw [CFSG.RankThree.PartOne.LA126.mem_fixedSubmodule] at hx ⊢
    intro t ht
    have hmemA : rot Q p.1 p.2 ∈ A := by
      rw [hAe]
      exact rot_mem_torus hp
    have hconj : (rot Q p.1 p.2)⁻¹ * (t : V ≃ₗ[ZMod 2] V) * rot Q p.1 p.2 ∈ T := by
      have h := Subgroup.le_normalizer_iff.mp hN _ (inv_mem hmemA) _ ht
      simpa using h
    have hmul : (t : V ≃ₗ[ZMod 2] V) * rot Q p.1 p.2 =
        rot Q p.1 p.2 *
          ((rot Q p.1 p.2)⁻¹ * (t : V ≃ₗ[ZMod 2] V) * rot Q p.1 p.2) := by
      group
    have hfix : ((rot Q p.1 p.2)⁻¹ * (t : V ≃ₗ[ZMod 2] V) * rot Q p.1 p.2) x = x :=
      hx _ hconj
    calc (t : V ≃ₗ[ZMod 2] V) (rot Q p.1 p.2 x)
        = ((t : V ≃ₗ[ZMod 2] V) * rot Q p.1 p.2) x := rfl
      _ = (rot Q p.1 p.2 * ((rot Q p.1 p.2)⁻¹ * (t : V ≃ₗ[ZMod 2] V) *
            rot Q p.1 p.2)) x := by rw [hmul]
      _ = rot Q p.1 p.2 x := by rw [LinearEquiv.mul_apply, hfix]
  let ρ : T →* Module.End (ZMod 2) V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp T.subtype
  have hSne : CFSG.RankThree.PartOne.LA126.fixedSubmodule T ≠ ⊥ := by
    obtain ⟨v, -, hv0, hvfix⟩ :=
      CFSG.LinearAlgebra.CoprimeActions.BinaryFixedVectors.exists_fixed hT2
        ρ ⊤ (fun _ => le_top) (by simp)
    intro hbot
    have hvS : v ∈ CFSG.RankThree.PartOne.LA126.fixedSubmodule T := by
      rw [CFSG.RankThree.PartOne.LA126.mem_fixedSubmodule]
      exact fun y hy => hvfix ⟨y, hy⟩
    rw [hbot] at hvS
    exact hv0 (by simpa using hvS)
  have hSne_top : CFSG.RankThree.PartOne.LA126.fixedSubmodule T ≠ ⊤ := by
    intro htop
    obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
    apply ht
    apply Subtype.ext
    ext v
    have hv : v ∈ CFSG.RankThree.PartOne.LA126.fixedSubmodule T := by
      rw [htop]
      exact Submodule.mem_top
    rw [CFSG.RankThree.PartOne.LA126.mem_fixedSubmodule] at hv
    simpa using hv t t.2
  let Sperp : Submodule (ZMod 2) V := perpOf Q (CFSG.RankThree.PartOne.LA126.fixedSubmodule T)
  have hSperp_ne : Sperp ≠ ⊥ := by
    have hlt : finrank (ZMod 2) (CFSG.RankThree.PartOne.LA126.fixedSubmodule T) <
        finrank (ZMod 2) V := by
      simpa using Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hSne_top)
    have hfr : finrank (ZMod 2) Sperp =
        finrank (ZMod 2) V - finrank (ZMod 2) (CFSG.RankThree.PartOne.LA126.fixedSubmodule T) :=
      LinearMap.BilinForm.finrank_orthogonal hQ _
    intro hbot
    rw [hbot, finrank_bot] at hfr
    omega
  have hSperp_inv : ∀ t : T,
      Sperp ≤ Sperp.comap (ρ t) := by
    intro t x hx
    rw [Submodule.mem_comap]
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
    intro s hs
    rw [QuadraticMap.polarBilin_apply_apply]
    have hst : (t : V ≃ₗ[ZMod 2] V) s = s :=
      (CFSG.RankThree.PartOne.LA126.mem_fixedSubmodule.1 hs) t t.2
    change polar Q s ((t : V ≃ₗ[ZMod 2] V) x) = 0
    have hiso : polar Q ((t : V ≃ₗ[ZMod 2] V) s) ((t : V ≃ₗ[ZMod 2] V) x) = polar Q s x :=
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hTO t.2) s x
    rw [hst] at hiso
    rw [hiso]
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.1 hx) s hs
    rwa [QuadraticMap.polarBilin_apply_apply] at h
  obtain ⟨w, hwSperp, hw0, hwfix⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.BinaryFixedVectors.exists_fixed hT2
      ρ Sperp hSperp_inv hSperp_ne
  have hwS : w ∈ CFSG.RankThree.PartOne.LA126.fixedSubmodule T := by
    rw [CFSG.RankThree.PartOne.LA126.mem_fixedSubmodule]
    exact fun y hy => hwfix ⟨y, hy⟩
  have hwperp : ∀ y ∈ CFSG.RankThree.PartOne.LA126.fixedSubmodule T, polar Q w y = 0 := by
    intro y hy
    rw [polar_comm]
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.1 hwSperp) y hy
    rwa [QuadraticMap.polarBilin_apply_apply] at h
  exact hw0 (eq_zero_of_forall_polar_eq_zero hl hspan hSinv hwS hwperp)

theorem nondegenerate_quadMinus_five :
    (polarBilin (quadMinus 5 (ZMod 2) 1 1)).Nondegenerate :=
  CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 5 (ZMod 2)
    (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)

theorem isPlusType_quadMinus_five_iff :
    IsPlusType (quadMinus 5 (ZMod 2) 1 1) ↔ Even 5 :=
  ⟨fun h => absurd h (not_isPlusType_quadMinus (by norm_num)
      (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)),
    fun h => absurd h (by decide : ¬ Even 5)⟩

theorem quadMinus_five_card_le
    {A T : Subgroup ((Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2))}
    (hAΩ : A ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 5 (ZMod 2) 1 1),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 5 (ZMod 2) 1 1)⁆)
    (hA : IsElemAbelian 3 A)
    (hTΩ : T ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 5 (ZMod 2) 1 1),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 5 (ZMod 2) 1 1)⁆)
    (hT2 : IsPGroup 2 T) (hTne : T ≠ ⊥)
    (hN : A ≤ Subgroup.normalizer (T : Set _)) :
    Nat.card A ≤ 3 ^ 4 := by
  have hdim : finrank (ZMod 2) (Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2) = 2 * 5 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have h := card_le_three_pow_pred_of_normalizes (Q := quadMinus 5 (ZMod 2) 1 1)
    nondegenerate_quadMinus_five hdim isPlusType_quadMinus_five_iff hAΩ hA hTΩ hT2 hTne hN
  simpa using h

end CFSG.StandardType.FrameRoute.FS81

end
