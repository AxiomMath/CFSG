module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.D2Basic
import CFSG.Quasithin.Background.FFC2Core
import CFSG.Quasithin.EmptyFaithful.R3c23NatSym

public section

namespace CFSG.Quasithin

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
@[expose] def a5w_perm (θ : W ≃* ↥(G6.coreMod 5)) : Equiv.Perm (Fin 5) →* MulAut W :=
  (MulAut.congr θ.symm).toMonoidHom.comp (G6.coreAct 5)

omit [Finite W] in
theorem a5w_perm_apply (θ : W ≃* ↥(G6.coreMod 5)) (s : Equiv.Perm (Fin 5)) (w : W) :
    a5w_perm θ s w = θ.symm (G6.coreAct 5 s (θ w)) := rfl

theorem a5w_ker : (FFModel.altDn 5).ker = ⊥ := R3c23.Sym5.ker_symDn

omit [Finite W] in
theorem a5w_exists_equiv {L : Subgroup (MulAut W)} (hnat : AlternatingNatural L ⊤ ⊥ 5) :
    ∃ θ : W ≃* ↥(G6.coreMod 5), L = (alternatingGroup (Fin 5)).map (a5w_perm θ) := by
  obtain ⟨π, hπs, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := hnat
  have hK : (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec = ⊥ := by
    rw [a5w_ker]
    exact Subgroup.bot_subgroupOf _
  let ε : ↥(FFModel.altDn 5).sec ⧸ (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec →*
      ↥(FFModel.altDn 5).sec := QuotientGroup.lift _ (MonoidHom.id _) (by rw [hK]; exact bot_le)
  have hε : ∀ m : ↥(FFModel.altDn 5).sec, ε (QuotientGroup.mk m) = m := fun m => rfl
  let θ0 : ↥(⊤ : Subgroup W) →* ↥(G6.coreMod 5) := ε.comp β
  have hθinj : Function.Injective θ0 := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : β u = 1 := by
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
      have hεu : θ0 u = m := (congrArg ε hm.symm).trans (hε m)
      have h2 : m = 1 := hεu.symm.trans hu
      rw [← hm, h2]
      exact QuotientGroup.mk_one _
    have h3 : (u : W) ∈ (⊥ : Subgroup W) := (hβk u).1 h1
    exact Subtype.ext (Subgroup.mem_bot.1 h3)
  have hθsurj : Function.Surjective θ0 := by
    intro m
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
    exact ⟨u, (congrArg ε hu).trans (hε m)⟩
  let θ : W ≃* ↥(G6.coreMod 5) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective θ0 ⟨hθinj, hθsurj⟩)
  have hθ : ∀ (a : ↥(alternatingGroup (Fin 5))) (w : W),
      θ (((π a : ↥L) : MulAut W) w) = G6.coreAct 5 (a : Equiv.Perm (Fin 5)) (θ w) := by
    intro a w
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, trivial⟩)
    have hm' : (FFModel.altDn 5).act a (m : (FFModel.altDn 5).Amb) ∈ (FFModel.altDn 5).sec :=
      hsec a m m.2
    have key := hβe a ⟨w, trivial⟩ m trivial hm' hm.symm
    have hεu : θ0 ⟨w, trivial⟩ = m := (congrArg ε hm.symm).trans (hε m)
    refine (congrArg ε key).trans ?_
    refine Eq.trans (b := G6.coreAct 5 (a : Equiv.Perm (Fin 5)) m) rfl ?_
    exact congrArg (⇑(G6.coreAct 5 (a : Equiv.Perm (Fin 5)))) hεu.symm
  refine ⟨θ, ?_⟩
  have hπ : ∀ a : ↥(alternatingGroup (Fin 5)),
      ((π a : ↥L) : MulAut W) = a5w_perm θ (a : Equiv.Perm (Fin 5)) := by
    intro a
    ext w
    rw [a5w_perm_apply, ← hθ a w]
    simp
  ext g
  rw [Subgroup.mem_map]
  constructor
  · intro hg
    have hπs' : ∀ y : ↥L, ∃ a : ↥(alternatingGroup (Fin 5)), π a = y := hπs
    obtain ⟨a, ha⟩ := hπs' ⟨g, hg⟩
    exact ⟨(a : Equiv.Perm (Fin 5)), a.2, by rw [← hπ a, ha]⟩
  · rintro ⟨s, hs, rfl⟩
    rw [← hπ ⟨s, hs⟩]
    exact (π ⟨s, hs⟩).2

omit [Finite W] in
theorem a5w_perm_injective (θ : W ≃* ↥(G6.coreMod 5)) : Function.Injective (a5w_perm θ) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  refine R3c23.Sym5.fc_faithful s fun f hf i => ?_
  have h : ∀ x : ↥(G6.coreMod 5), G6.coreAct 5 s x = x := fun x => by
    have := congrArg (fun g : MulAut W => θ (g (θ.symm x))) hs
    simpa [a5w_perm_apply] using this
  exact congrFun (congrArg (fun y : ↥(G6.coreMod 5) => Multiplicative.toAdd (y : G6.PermMod 5))
    (h ⟨Multiplicative.ofAdd f, G6.mem_coreMod.mpr hf⟩)) i

omit [Finite W] in
theorem a5w_sq (θ : W ≃* ↥(G6.coreMod 5)) (v : W) : v ^ 2 = 1 := by
  apply θ.injective
  rw [map_pow, map_one, sq]
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  exact h2 _

@[expose] def a5w_pairV (i j : Fin 5) : Fin 5 → ZMod 2 :=
  fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)

theorem a5w_sum_pairV (i j : Fin 5) : ∑ k, a5w_pairV i j k = 0 := by
  revert i j
  decide +kernel

@[expose] def a5w_pairM (i j : Fin 5) : ↥(G6.coreMod 5) :=
  ⟨Multiplicative.ofAdd (a5w_pairV i j), G6.mem_coreMod.mpr (a5w_sum_pairV i j)⟩

theorem a5w_pairM_ne_one : a5w_pairM 0 1 ≠ 1 := by
  intro h
  have h' := congrFun
    (congrArg (fun y : ↥(G6.coreMod 5) => Multiplicative.toAdd (y : G6.PermMod 5)) h) 0
  revert h'
  decide +kernel

theorem a5w_pairM_self (i : Fin 5) : a5w_pairM i i = 1 := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext k
  show a5w_pairV i i k = 0
  revert i k
  decide +kernel

theorem a5w_pairM_comm (i j : Fin 5) : a5w_pairM j i = a5w_pairM i j := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext k
  show a5w_pairV j i k = a5w_pairV i j k
  revert i j k
  decide +kernel

theorem a5w_gen : ∀ f : Fin 5 → ZMod 2, ∑ i, f i = 0 →
    ∃ a b c d : Fin 5, ∀ i, f i = a5w_pairV a b i + a5w_pairV c d i := by
  decide +kernel

theorem a5w_coreAct_pairM (σ : Equiv.Perm (Fin 5)) (i j : Fin 5) :
    G6.coreAct 5 σ (a5w_pairM i j) = a5w_pairM (σ i) (σ j) := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext k
  show a5w_pairV i j (σ⁻¹ k) = a5w_pairV (σ i) (σ j) k
  simp [a5w_pairV, Equiv.symm_apply_eq]

@[expose] def a5w_c3 : Equiv.Perm (Fin 5) := Equiv.swap 2 3 * Equiv.swap 3 4

@[expose] def a5w_dt : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

theorem a5w_c3_mem : a5w_c3 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem a5w_dt_mem : a5w_dt ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem a5w_fix_pair : ∀ y : Fin 5 → ZMod 2, ∑ i, y i = 0 →
    (∀ i, y (a5w_c3⁻¹ i) = y i) → (∀ i, y (a5w_dt⁻¹ i) = y i) →
    y = 0 ∨ y = a5w_pairV 0 1 := by
  decide +kernel

theorem a5w_pair_transitive : ∀ i j : Fin 5, i ≠ j →
    ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ σ 0 = i ∧ σ 1 = j := by
  decide +kernel

theorem a5w_schur (c : ↥(G6.coreMod 5) ≃* ↥(G6.coreMod 5))
    (hc : ∀ a ∈ alternatingGroup (Fin 5), ∀ x, c (G6.coreAct 5 a x) = G6.coreAct 5 a (c x)) :
    ∀ x, c x = x := by
  have h1a : G6.coreAct 5 a5w_c3 (a5w_pairM 0 1) = a5w_pairM 0 1 := by
    rw [a5w_coreAct_pairM]
    have e0 : a5w_c3 0 = 0 := by decide +kernel
    have e1 : a5w_c3 1 = 1 := by decide +kernel
    rw [e0, e1]
  have h2a : G6.coreAct 5 a5w_dt (a5w_pairM 0 1) = a5w_pairM 0 1 := by
    rw [a5w_coreAct_pairM]
    have e0 : a5w_dt 0 = 1 := by decide +kernel
    have e1 : a5w_dt 1 = 0 := by decide +kernel
    rw [e0, e1, a5w_pairM_comm]
  have hv1 : G6.coreAct 5 a5w_c3 (c (a5w_pairM 0 1)) = c (a5w_pairM 0 1) := by
    rw [← hc _ a5w_c3_mem, h1a]
  have hv2 : G6.coreAct 5 a5w_dt (c (a5w_pairM 0 1)) = c (a5w_pairM 0 1) := by
    rw [← hc _ a5w_dt_mem, h2a]
  have hcases := a5w_fix_pair (Multiplicative.toAdd ((c (a5w_pairM 0 1) : ↥(G6.coreMod 5)) :
      G6.PermMod 5)) (G6.mem_coreMod.mp (c (a5w_pairM 0 1)).2)
    (fun i => congrFun
      (congrArg (fun y : ↥(G6.coreMod 5) => Multiplicative.toAdd (y : G6.PermMod 5)) hv1) i)
    (fun i => congrFun
      (congrArg (fun y : ↥(G6.coreMod 5) => Multiplicative.toAdd (y : G6.PermMod 5)) hv2) i)
  have hfix : c (a5w_pairM 0 1) = a5w_pairM 0 1 := by
    rcases hcases with h | h
    · exfalso
      have h1 : c (a5w_pairM 0 1) = 1 :=
        Subtype.ext (Multiplicative.toAdd.injective (h.trans rfl))
      exact a5w_pairM_ne_one (c.injective (h1.trans (map_one c).symm))
    · exact Subtype.ext (Multiplicative.toAdd.injective h)
  have hpair : ∀ i j, c (a5w_pairM i j) = a5w_pairM i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [a5w_pairM_self, map_one]
    · obtain ⟨σ, hsign, hσ0, hσ1⟩ := a5w_pair_transitive i j hij
      have hσ : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hsign
      have e1 : G6.coreAct 5 σ (a5w_pairM 0 1) = a5w_pairM i j := by
        rw [a5w_coreAct_pairM, hσ0, hσ1]
      rw [← e1, hc σ hσ, hfix]
  intro x
  obtain ⟨a, b, e, d, h⟩ := a5w_gen (Multiplicative.toAdd (x : G6.PermMod 5))
    (G6.mem_coreMod.mp x.2)
  have hx : x = a5w_pairM a b * a5w_pairM e d := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    exact h i
  rw [hx, map_mul, hpair, hpair]

theorem a5w_normalizer_eq {θ : W ≃* ↥(G6.coreMod 5)} {L : Subgroup (MulAut W)}
    (hL : L = (alternatingGroup (Fin 5)).map (a5w_perm θ)) :
    Subgroup.normalizer (L : Set (MulAut W)) = (a5w_perm θ).range := by
  have hinj := a5w_perm_injective θ
  have hmem : ∀ g : MulAut W, g ∈ L ↔ ∃ a ∈ alternatingGroup (Fin 5), a5w_perm θ a = g := by
    intro g
    rw [hL, Subgroup.mem_map]
  refine FFC.eq_of_card_mulAut_le (L := L) (H := (a5w_perm θ).range) ?_ ?_ ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨a, -, rfl⟩ := (hmem g).1 hg
    exact ⟨a, rfl⟩
  · rintro _ ⟨s, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmem, hmem]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨s * a * s⁻¹, (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem a ha s,
        by simp [map_mul, map_inv]⟩
    · rintro ⟨a, ha, hh⟩
      refine ⟨s⁻¹ * a * s, ?_, ?_⟩
      · simpa using (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem a ha s⁻¹
      · rw [map_mul, map_mul, hh, map_inv]
        group
  · intro h
    have hm : a5w_perm θ (Equiv.swap 0 1) ∈ L := by
      rw [← h]
      exact ⟨_, rfl⟩
    obtain ⟨a, ha, hae⟩ := (hmem _).1 hm
    have : a = Equiv.swap 0 1 := hinj hae
    rw [this, Equiv.Perm.mem_alternatingGroup] at ha
    revert ha
    decide
  · intro g hg l hl
    exact (Subgroup.mem_normalizer_iff.1 hg l).1 hl
  · intro g hg hcomm
    have hcx : ∀ x : ↥(G6.coreMod 5), (MulAut.congr θ g) x = θ (g (θ.symm x)) := fun x => rfl
    have hc : ∀ a ∈ alternatingGroup (Fin 5), ∀ x : ↥(G6.coreMod 5),
        (MulAut.congr θ g) (G6.coreAct 5 a x) = G6.coreAct 5 a ((MulAut.congr θ g) x) := by
      intro a ha x
      have h1 := congrArg (fun f : MulAut W => θ (f (θ.symm x)))
        (hcomm (a5w_perm θ a) ((hmem _).2 ⟨a, ha, rfl⟩))
      simpa [hcx, a5w_perm_apply] using h1
    have h2 := a5w_schur (MulAut.congr θ g) hc
    refine MulEquiv.ext fun w => ?_
    have h3 := h2 (θ w)
    rw [hcx, MulEquiv.symm_apply_apply] at h3
    exact θ.injective h3
  · subst hL
    let e : ↥(alternatingGroup (Fin 5)) ≃* ↥((alternatingGroup (Fin 5)).map (a5w_perm θ)) :=
      Subgroup.equivMapOfInjective _ _ hinj
    rw [← Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_congr e.toEquiv]
    exact FFC.card_mulAut_alternating_le (Or.inl rfl)

theorem a5w_card_le (θ : W ≃* ↥(G6.coreMod 5)) {E : Subgroup (MulAut W)}
    (hES : E ≤ (a5w_perm θ).range) (hE : IsElemAbelian2 E) :
    Nat.card ↥E * Nat.card ↥(fixV E) ≤ Nat.card W := by
  have d : R3c23.Sym5.RealizationData (a5w_perm θ).range (⊤ : Subgroup W) ⊥ :=
    { π := (a5w_perm θ).rangeRestrict
      β := (θ.toMonoidHom).comp (Subgroup.topEquiv : ↥(⊤ : Subgroup W) ≃* W).toMonoidHom
      surj_π := (a5w_perm θ).rangeRestrict_surjective
      surj_β := fun x => ⟨⟨θ.symm x, trivial⟩, by simp⟩
      CW := bot_le
      Winv := fun _ _ _ => trivial
      ker_β := fun u => by simp [Subgroup.mem_bot]
      equiv := fun σ u => by
        show θ (a5w_perm θ σ (u : W)) = _
        rw [a5w_perm_apply, MulEquiv.apply_symm_apply]
        rfl }
  have h := d.natCount E hES hE
  have e1 : R3c23.fixMod E ⊤ ⊥ = fixV E := by
    ext w
    simp [R3c23.mem_fixMod, mem_fixV, mul_inv_eq_one]
  rw [e1] at h
  simpa using h

theorem a5w_rk_le {E : Subgroup (MulAut W)} (hV : ∀ v : W, v ^ 2 = 1) (hE : IsElemAbelian2 E)
    (h : Nat.card ↥E * Nat.card ↥(fixV E) ≤ Nat.card W) : rk ↥E ≤ rkIdx (fixV E) := by
  have hEc : Nat.card ↥E = 2 ^ rk ↥E :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one fun x : ↥E =>
      Subtype.ext (by simpa using hE.2 x x.2))
  have hFc : Nat.card ↥(fixV E) = 2 ^ rk ↥(fixV E) := card_eq_two_pow hV (fixV E)
  have hWc : Nat.card W = 2 ^ rk W := by
    have := card_eq_two_pow hV ⊤
    rwa [Subgroup.card_top, rk_top] at this
  rw [hEc, hFc, hWc, ← pow_add] at h
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h
  have h3 := rk_add_rkIdx (fixV E)
  omega

theorem alt5_weight {L E : Subgroup (MulAut W)} (hnat : AlternatingNatural L ⊤ ⊥ 5)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : IsElemAbelian2 E) :
    rk ↥E ≤ rkIdx (fixV E) := by
  obtain ⟨θ, hL⟩ := a5w_exists_equiv hnat
  have hES : E ≤ (a5w_perm θ).range := (a5w_normalizer_eq hL) ▸ hEN
  exact a5w_rk_le (a5w_sq θ) hE (a5w_card_le θ hES hE)

end CFSG.Quasithin
