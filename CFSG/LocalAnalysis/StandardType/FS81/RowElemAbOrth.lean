module

public import CFSG.LocalAnalysis.StandardType.FS81.RowElemAb
public import CFSG.LocalAnalysis.StandardType.FS81.OrthMaxTorus
public import CFSG.LocalAnalysis.StandardType.GGFrameFSxOrth
public import CFSG.RankThree.Literature.FSmithOrthogonal
public import CFSG.RankThree.OrthogonalInvolutions.Witt
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.Open CFSG.Assembly CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section Space

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem orth_card_elemAb3_le (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ n := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨l, hl, hEl⟩ := exists_frame_top hQ hEO hE
  have hW := Submodule.finrank_le (Wspan l)
  rw [hl.finrank_Wspan, hdim] at hW
  calc Nat.card E ≤ Nat.card (torus Q l) := Subgroup.card_le_of_le hEl
    _ = 3 ^ l.length := card_torus hl
    _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

private noncomputable def frameVec {n : ℕ} (l : List (V × V)) (hl : l.length = n) :
    Fin n × Bool → V :=
  fun p => if p.2 then (l[p.1.val]'(by have := p.1.2; omega)).2
    else (l[p.1.val]'(by have := p.1.2; omega)).1

omit [FiniteDimensional (ZMod 2) V] in
private theorem frameVec_Q {n : ℕ} {l : List (V × V)} (hf : IsFrame Q l) (hl : l.length = n)
    (p : Fin n × Bool) : Q (frameVec l hl p) = 1 := by
  have hp := hf.pair _ (List.getElem_mem (l := l) (n := p.1.val) (by have := p.1.2; omega))
  unfold frameVec
  split_ifs
  · exact hp.qb
  · exact hp.qa

omit [FiniteDimensional (ZMod 2) V] in
private theorem frameVec_polar {n : ℕ} {l : List (V × V)} (hf : IsFrame Q l) (hl : l.length = n)
    (p q : Fin n × Bool) :
    polar Q (frameVec l hl p) (frameVec l hl q) =
      if p.1 = q.1 then (if p.2 = q.2 then 0 else 1) else 0 := by
  obtain ⟨i, b⟩ := p
  obtain ⟨j, c⟩ := q
  by_cases hij : i = j
  · subst hij
    have hp := hf.pair _ (List.getElem_mem (l := l) (n := i.val) (by have := i.2; omega))
    cases b <;> cases c <;> simp [frameVec, hp.aa, hp.ab, hp.ba, hp.bb]
  · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hperp : PairPerp Q (l[i.val]'(by have := i.2; omega)) (l[j.val]'(by have := j.2; omega)) := by
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact List.pairwise_iff_getElem.1 hf.perp _ _ _ _ h
      · exact (List.pairwise_iff_getElem.1 hf.perp _ _ _ _ h).symm
    obtain ⟨h1, h2, h3, h4⟩ := hperp
    cases b <;> cases c <;> simp [frameVec, hij, h1, h2, h3, h4]

omit [FiniteDimensional (ZMod 2) V] in
private theorem frameVec_linearIndependent {n : ℕ} {l : List (V × V)} (hf : IsFrame Q l)
    (hl : l.length = n) : LinearIndependent (ZMod 2) (frameVec l hl) := by
  rw [Fintype.linearIndependent_iff]
  intro x hx p
  have hsum : polar Q (∑ q, x q • frameVec l hl q) (frameVec l hl (p.1, !p.2)) =
      ∑ q, x q * polar Q (frameVec l hl q) (frameVec l hl (p.1, !p.2)) := by
    simp only [← QuadraticMap.polarBilin_apply_apply, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
  have hone : ∀ q, polar Q (frameVec l hl q) (frameVec l hl (p.1, !p.2)) =
      if q = p then 1 else 0 := by
    intro q
    rw [frameVec_polar hf hl]
    obtain ⟨i, b⟩ := p
    obtain ⟨j, c⟩ := q
    by_cases hji : j = i
    · subst hji
      cases b <;> cases c <;> simp
    · simp [hji]
  simp only [hone, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    at hsum
  rw [hx, polar_zero_left] at hsum
  exact hsum.symm

theorem exists_isometry_frame (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    {l l' : List (V × V)} (hf : IsFrame Q l) (hf' : IsFrame Q l') (hl : l.length = n)
    (hl' : l'.length = n) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, l.map (fun q => (g q.1, g q.2)) = l' := by
  set e := Fintype.equivFin (Fin n × Bool)
  obtain ⟨g, hg, hgu⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hQ (frameVec l hl ∘ e.symm) (frameVec l' hl' ∘ e.symm)
    ((frameVec_linearIndependent hf hl).comp _ e.symm.injective)
    ((frameVec_linearIndependent hf' hl').comp _ e.symm.injective)
    (fun i => by simp only [Function.comp, frameVec_Q hf hl, frameVec_Q hf' hl'])
    (fun i j => by simp only [Function.comp, frameVec_polar hf hl, frameVec_polar hf' hl'])
  have hgv : ∀ p, g (frameVec l hl p) = frameVec l' hl' p := fun p => by
    simpa using hgu (e p)
  refine ⟨g, hg, List.ext_getElem (by simp [hl, hl']) fun i h1 h2 => ?_⟩
  rw [List.getElem_map]
  have hi : i < n := by rw [← hl']; exact h2
  have ha := hgv (⟨i, hi⟩, false)
  have hb := hgv (⟨i, hi⟩, true)
  simp only [frameVec, Bool.false_eq_true, ite_false, ite_true] at ha hb
  exact Prod.ext ha hb

omit [FiniteDimensional (ZMod 2) V] in
theorem torus_map_conj {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (l : List (V × V)) :
    (torus Q l).map (MulAut.conj g).toMonoidHom = torus Q (l.map fun q => (g q.1, g q.2)) := by
  rw [torus, torus, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [rotSet, Set.mem_image, Set.mem_setOf_eq, List.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, conj_rot hg p.1 p.2⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨rot Q p.1 p.2, ⟨p, hp, rfl⟩, conj_rot hg p.1 p.2⟩

theorem torus_map_conj_reflect {a b : V} {l : List (V × V)} (hf : IsFrame Q ((a, b) :: l)) :
    (torus Q ((a, b) :: l)).map (MulAut.conj (reflect Q a)).toMonoidHom = torus Q ((a, b) :: l) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨-, hperp, -⟩ := isFrame_cons.1 hf
  have hle : (torus Q ((a, b) :: l)).map (MulAut.conj (reflect Q a)).toMonoidHom ≤
      torus Q ((a, b) :: l) := by
    rw [torus, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases List.mem_cons.1 hq with rfl | hq
    · have hinv : reflect Q a * rot Q a b * (reflect Q a)⁻¹ = (rot Q a b)⁻¹ := by
        simp only [rot, reflect_inv, mul_inv_rev]
        rw [← mul_assoc, reflect_mul_self, one_mul]
      rw [hinv]
      exact inv_mem (rot_mem_torus List.mem_cons_self)
    · obtain ⟨h1, h2, -, -⟩ := hperp q hq
      have hc : Commute (reflect Q a) (rot Q q.1 q.2) :=
        (reflect_commute_of_polar_eq_zero h1).mul_right (reflect_commute_of_polar_eq_zero h2)
      rw [hc.eq, mul_inv_cancel_right]
      exact rot_mem_torus (List.mem_cons_of_mem _ hq)
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj _).injective])

theorem mul_reflect_mem_commutator (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgΩ : g ∉ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {a : V} (ha : Q a = 1) :
    g * reflect Q a ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ h6] at hgΩ ⊢
  rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup] at hgΩ ⊢
  have hr := reflect_mem_orthogonalGroup Q a
  refine ⟨mul_mem hg hr, ?_⟩
  have hodd : Odd (finrank (ZMod 2) (CFSG.RankThree.OrthogonalInvolutions.commSpace g)) :=
    Nat.not_even_iff_odd.1 fun h => hgΩ ⟨hg, h⟩
  have hmul := CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQ hg hr
  rw [CFSG.RankThree.Literature.FSmith.finrank_commSpace_reflect hQ ha, Nat.cast_one,
    (ZMod.natCast_eq_one_iff_odd).2 hodd] at hmul
  rw [← ZMod.natCast_eq_zero_iff_even, hmul]
  decide

theorem orth_conj_elemAb3 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hn : 3 ≤ n)
    (hdim : finrank (ZMod 2) V = 2 * n) (htype : IsPlusType Q ↔ Even n)
    {E E' : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEΩ : E ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hE'Ω : E' ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hE : IsElemAbelian 3 E) (hE' : IsElemAbelian 3 E') (hc : Nat.card E = 3 ^ n)
    (hc' : Nat.card E' = 3 ^ n) :
    ∃ k ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      E'.map (MulAut.conj k).toMonoidHom = E := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hmax : ∀ {F : Subgroup (V ≃ₗ[ZMod 2] V)}, IsElemAbelian 3 F → Nat.card F = 3 ^ n →
      ∀ F' : Subgroup (V ≃ₗ[ZMod 2] V),
        F' ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
        IsElemAbelian 3 F' → F ≤ F' → F' = F := by
    intro F hF hFc F' hF'Ω hF' hle
    exact (Subgroup.eq_of_le_of_card_ge hle (by
      rw [hFc]
      exact orth_card_elemAb3_le hQ hdim (hF'Ω.trans (Subgroup.commutator_le_self _)) hF')).symm
  obtain ⟨l, hl, hlen, rfl⟩ := fs81_orth_maxElemAb3_eq_torus hQ hdim htype hEΩ hE (hmax hE hc)
  obtain ⟨l', hl', hlen', rfl⟩ :=
    fs81_orth_maxElemAb3_eq_torus hQ hdim htype hE'Ω hE' (hmax hE' hc')
  obtain ⟨g, hg, hgl⟩ := exists_isometry_frame hQ hl' hl hlen' hlen
  have hconj := torus_map_conj hg l'
  rw [hgl] at hconj
  obtain ⟨⟨a, b⟩, l₀, rfl⟩ := List.exists_cons_of_length_pos (l := l') (by omega)
  have ha : Q a = 1 := (hl'.pair _ List.mem_cons_self).qa
  by_cases hgΩ : g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆
  · exact ⟨g, hgΩ, hconj⟩
  · refine ⟨g * reflect Q a, mul_reflect_mem_commutator hQ (by omega) hg hgΩ ha, ?_⟩
    have hcomp : (MulAut.conj (g * reflect Q a)).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (MulAut.conj (reflect Q a)).toMonoidHom :=
      MonoidHom.ext fun x => by simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, ← Subgroup.map_map, torus_map_conj_reflect hl', hconj]

theorem orth_rowFacts_of_range {M : Type} [Group M] (ψ : M →* (V ≃ₗ[ZMod 2] V))
    (hψ : Function.Injective ψ)
    (hrange : ψ.range =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hn : 3 ≤ n)
    (hdim : finrank (ZMod 2) V = 2 * n) (htype : IsPlusType Q ↔ Even n) :
    (∀ E : Subgroup M, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ n) ∧
      (∀ E E' : Subgroup M, IsElemAbelian 3 E → IsElemAbelian 3 E' → Nat.card E = 3 ^ n →
        Nat.card E' = 3 ^ n → ∃ c : M, E'.map (MulAut.conj c).toMonoidHom = E) := by
  have hcard : ∀ E : Subgroup M, Nat.card (E.map ψ) = Nat.card E := fun E =>
    Subgroup.card_map_of_injective hψ
  have hle : ∀ E : Subgroup M, E.map ψ ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    fun E => hrange ▸ Subgroup.map_le_range ψ E
  refine ⟨fun E hE => ?_, fun E E' hE hE' hc hc' => ?_⟩
  · rw [← hcard E]
    exact orth_card_elemAb3_le hQ hdim ((hle E).trans (Subgroup.commutator_le_self _)) (hE.map ψ)
  · obtain ⟨k, hk, hkE⟩ := orth_conj_elemAb3 hQ hn hdim htype (hle E) (hle E') (hE.map ψ)
      (hE'.map ψ) (by rw [hcard, hc]) (by rw [hcard, hc'])
    obtain ⟨c, rfl⟩ : k ∈ ψ.range := hrange ▸ hk
    refine ⟨c, Subgroup.map_injective hψ ?_⟩
    rw [Subgroup.map_map, ← hkE, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext fun x => by simp [MulAut.conj_apply]

end Space

theorem statedOmega_rowFacts {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} {Q₀ : (ι → ZMod 2) → ZMod 2} (hQ₀ : ⇑Q = Q₀)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hn : 3 ≤ n)
    (hdim : Fintype.card ι = 2 * n) (htype : IsPlusType Q ↔ Even n) :
    (∀ E : Subgroup ↥(StatedOmega Q₀), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ n) ∧
      (∀ E E' : Subgroup ↥(StatedOmega Q₀), IsElemAbelian 3 E → IsElemAbelian 3 E' →
        Nat.card E = 3 ^ n → Nat.card E' = 3 ^ n →
          ∃ c : ↥(StatedOmega Q₀), E'.map (MulAut.conj c).toMonoidHom = E) := by
  refine orth_rowFacts_of_range ((toLinEquiv ι (ZMod 2)).toMonoidHom.comp (StatedOmega Q₀).subtype)
    ((toLinEquiv ι (ZMod 2)).injective.comp Subtype.val_injective) ?_ hQ hn
    (by rw [Module.finrank_fintype_fun_eq_card, hdim]) htype
  rw [MonoidHom.range_comp, Subgroup.range_subtype, statedOmega_eq_comap hQ₀]
  exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι (ZMod 2)).surjective _

theorem rowFacts_of_statedOmega {G : Type} [Group G] [Finite G] {K A : Subgroup G}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} {Q₀ : (ι → ZMod 2) → ZMod 2}
    (φ : ↥K ≃* ↥(StatedOmega Q₀)) (hQ₀ : ⇑Q = Q₀)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hn : 3 ≤ n)
    (hdim : Fintype.card ι = 2 * n) (htype : IsPlusType Q ↔ Even n)
    (hAK : A ≤ K) (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ n) :
    (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' ≤ 3 ^ n) ∧
      (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' = 3 ^ n →
        ∃ k ∈ K, A'.map (MulAut.conj k).toMonoidHom = A) := by
  obtain ⟨h1, h2⟩ := statedOmega_rowFacts hQ₀ hQ hn hdim htype
  exact rowElemAb3_of_mulEquiv φ h1 h2 hAK hA hAcard

theorem rowElemAb3_D6 {G : Type} [Group G] [Finite G] {K A : Subgroup G}
    (hrow : IsRow Row.D6 K) (hZ : Subgroup.center K = ⊥) (hAK : A ≤ K)
    (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ Row.D6.n) :
    (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' ≤ 3 ^ Row.D6.n) ∧
      (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' = 3 ^ Row.D6.n →
        ∃ k ∈ K, A'.map (MulAut.conj k).toMonoidHom = A) := by
  have hm : LargeEvenMarking ↥K
      (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h => by
      obtain ⟨hn, ⟨-, ht, hr⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩ := h
      · exact ⟨ht, hr, hn⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)) hrow
  obtain ⟨φ⟩ := nonempty_mulEquiv_omegaPlusSix_of_marking hm hZ
  exact rowFacts_of_statedOmega φ (CFSG.LieType.Universal.Spin.coe_quadPlus 6 (ZMod 2))
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 (ZMod 2)) (n := 6)
    (by norm_num) (by simp) ⟨fun _ => by decide, fun _ => isPlusType_quadPlus (ZMod 2) 6⟩
    hAK hA hAcard

theorem rowElemAb3_twD7 {G : Type} [Group G] [Finite G] {K A : Subgroup G}
    (hrow : IsRow Row.twD7 K) (hZ : Subgroup.center K = ⊥) (hAK : A ≤ K)
    (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ Row.twD7.n) :
    (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' ≤ 3 ^ Row.twD7.n) ∧
      (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' = 3 ^ Row.twD7.n →
        ∃ k ∈ K, A'.map (MulAut.conj k).toMonoidHom = A) := by
  have hm : LargeEvenMarking ↥K
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h => by
      obtain ⟨hn, ⟨h, -⟩ | ⟨-, ht, hr⟩ | ⟨h, -⟩⟩ := h
      · exact absurd h (by decide)
      · exact ⟨ht, hr, hn⟩
      · exact absurd h (by decide)) hrow
  obtain ⟨φ⟩ := nonempty_mulEquiv_omegaMinusSeven_of_marking hm hZ
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by
    intro s
    fin_cases s <;> decide
  have hnd : (QuadraticMap.polarBilin
      (CFSG.LieType.Universal.Spin.quadMinus 7 (ZMod 2) 1 1)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 7 (ZMod 2) hirr
  have hnp : ¬ IsPlusType (CFSG.LieType.Universal.Spin.quadMinus 7 (ZMod 2) 1 1) :=
    not_isPlusType_quadMinus (by norm_num) hirr
  have hcard : Fintype.card (Fin (7 - 1) ⊕ Fin (7 - 1) ⊕ Fin 2) = 2 * 7 := by simp
  exact rowFacts_of_statedOmega φ (CFSG.LieType.Universal.Spin.coe_quadMinus 7 (ZMod 2) 1 1) hnd
    (n := 7) (by norm_num) hcard ⟨fun h => absurd h hnp, fun h => absurd h (by decide)⟩
    hAK hA hAcard

theorem exists_orth_model_of_isRow {G : Type} [Group G] {K : Subgroup G} {r : Row}
    (hr : r ≠ Row.E7) (hK : IsRow r K) (hZ : Subgroup.center K = ⊥) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧ Fintype.card ι = 2 * r.n ∧
      (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even r.n) ∧
      Nonempty (↥K ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆) := by
  cases r with
  | D6 =>
    have hm : LargeEvenMarking ↥K
        (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) := by
      refine largeEvenMarking_mono ?_ (by simpa only [IsRow] using hK)
      intro lab R _ I F θ h
      obtain ⟨hn, h | h | h⟩ := h
      · exact ⟨h.2.1, h.2.2, hn⟩
      · exact absurd h.1 (by decide)
      · exact absurd h.1 (by decide)
    obtain ⟨e⟩ := nonempty_mulEquiv_omegaPlusSix_of_marking hm hZ
    refine ⟨Fin 6 ⊕ Fin 6, inferInstance, inferInstance,
      CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2), ?_, ?_, ?_, ?_⟩
    · exact CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 (ZMod 2)
    · simp [Row.n]
    · exact ⟨fun _ => by simp only [Row.n]; decide,
        fun _ => CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus (ZMod 2) 6⟩
    · exact ⟨e.trans (CFSG.LieType.ChevTwo.statedOmegaEquivDerived
        (Q := StatedQuadPlus 6 (ZMod 2))
        (q := CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2))
        (CFSG.LieType.Universal.Spin.coe_quadPlus 6 (ZMod 2)))⟩
  | twD7 =>
    have hm : LargeEvenMarking ↥K
        (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) := by
      refine largeEvenMarking_mono ?_ (by simpa only [IsRow] using hK)
      intro lab R _ I F θ h
      obtain ⟨hn, h | h | h⟩ := h
      · exact absurd h.1 (by decide)
      · exact ⟨h.2.1, h.2.2, hn⟩
      · exact absurd h.1 (by decide)
    obtain ⟨e⟩ := nonempty_mulEquiv_omegaMinusSeven_of_marking hm hZ
    refine ⟨Fin 6 ⊕ Fin 6 ⊕ Fin 2, inferInstance, inferInstance,
      CFSG.LieType.Universal.Spin.quadMinus 7 (ZMod 2) 1 1, ?_, ?_, ?_, ?_⟩
    · exact CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 7 (ZMod 2)
        (CFSG.LieType.ChevTwo.hirr_one_one)
    · simp [Row.n]
    · exact ⟨fun h => absurd h (CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by norm_num)
          CFSG.LieType.ChevTwo.hirr_one_one), fun h => absurd h (by simp only [Row.n]; decide)⟩
    · exact ⟨e.trans (CFSG.LieType.ChevTwo.statedOmegaEquivDerived
        (Q := StatedQuadMinus 7 (ZMod 2) 1 1)
        (q := CFSG.LieType.Universal.Spin.quadMinus 7 (ZMod 2) 1 1)
        (CFSG.LieType.Universal.Spin.coe_quadMinus 7 (ZMod 2) 1 1))⟩
  | E7 => exact absurd rfl hr

end CFSG.StandardType.FrameRoute.FS81

end
