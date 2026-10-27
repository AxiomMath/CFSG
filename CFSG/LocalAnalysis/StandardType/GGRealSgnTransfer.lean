module

public import CFSG.LocalAnalysis.StandardType.GGRealSgnDefs
public import CFSG.LocalAnalysis.StandardType.GGKGForkTransfer
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

private theorem ggRealSgn_lift_conj_mul_inv {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (Λ : R →* MulAut L') {n : L'} {w : R} (hΛn : Λ (ψ n) = MulAut.conj n) (hw : ψ n = w)
    (e : R) : Λ (w * e * w⁻¹) = MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ := by
  have h : Λ w = MulAut.conj n := by rw [← hw, hΛn]
  rw [← h, ← map_mul, ← map_inv, ← map_mul]

private theorem ggRealSgn_lift_conj_inv_mul {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (Λ : R →* MulAut L') {n : L'} {w : R} (hΛn : Λ (ψ n) = MulAut.conj n) (hw : ψ n = w)
    (e : R) : Λ (w⁻¹ * e * w) = (MulAut.conj n)⁻¹ * Λ e * MulAut.conj n := by
  have h : Λ w = MulAut.conj n := by rw [← hw, hΛn]
  rw [← h, ← map_inv, ← map_mul, ← map_mul]

private theorem ggRealSgn_map_centralizer {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (S : Set R) :
    (Subgroup.centralizer S).map e.toMonoidHom = Subgroup.centralizer (e '' S) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h z ⟨x, hx, rfl⟩
    have h' := h x hx
    calc e x * y = e (x * e.symm y) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = e (e.symm y * x) := by rw [h']
      _ = y * e x := by rw [map_mul, MulEquiv.apply_symm_apply]
  · intro h x hx
    have h' := h (e x) ⟨x, hx, rfl⟩
    calc x * e.symm y = e.symm (e x * y) := by rw [map_mul, MulEquiv.symm_apply_apply]
      _ = e.symm (y * e x) := by rw [h']
      _ = e.symm y * x := by rw [map_mul, MulEquiv.symm_apply_apply]

private theorem ggRealSgn_injective_toMonoidHom {R R' : Type} [Group R] [Group R'] (e : R ≃* R') :
    Function.Injective e.toMonoidHom := by
  intro a b h
  exact e.injective (by simpa using h)

private theorem ggRealSgn_weylElt {p : ℕ} {L' R : Type} [Group L'] [Finite L'] [Group R]
    {ψ : L' →* R} {Λ : R →* MulAut L'} {A : Subgroup (MulAut L')} {E : Subgroup R}
    (hp : p.Prime) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hcpL : ¬ p ∣ Nat.card (Subgroup.center L'))
    (hΛeq : ∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x)
    (hAΛ : ∀ a ∈ A, ∃ e, Λ e = a)
    (hEmem : ∀ e : R, e ∈ E ↔ Λ e ∈ A) (hEab : IsElemAbelian p E)
    {n' : L'} {w : R} (hn' : ψ n' = w) (hψwu : ∀ e ∈ E, w * e * w⁻¹ ∈ E) :
    GGTorusWeylElt p A n' := by
  intro a ha
  obtain ⟨e, rfl⟩ := hAΛ a ha
  have heE : e ∈ E := (hEmem e).mpr ha
  obtain ⟨x, hx, hxp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (hEab.2 e heE)
  have hΛxe : Λ e = MulAut.conj x := hΛeq hx
  set u : L' := n' * x * n'⁻¹ with hu
  have hψu : ψ u = w * e * w⁻¹ := by rw [hu, map_mul, map_mul, map_inv, hn', hx]
  have hup : u ^ p = 1 := by rw [hu, conj_pow, hxp, mul_one, mul_inv_cancel]
  have hxu : x * u = u * x := by
    have hcommψ : ψ x * ψ u = ψ u * ψ x := by
      rw [hx, hψu]
      exact TableB.IsElemAbelian.comm hEab heE (hψwu e heE)
    exact commute_of_lift_pow_eq_one hp hker hcpL hcommψ hup
  have hux : n' * (Λ e n')⁻¹ = u * x⁻¹ := by
    rw [hΛxe, MulAut.conj_apply, hu]
    group
  have huxp : (u * x⁻¹) ^ p = 1 := by
    have hc : Commute u x := hxu.symm
    rw [(hc.inv_right).mul_pow, hup, inv_pow, hxp, inv_one, mul_one]
  refine ⟨?_, fun a' ha' => ?_⟩
  · rw [hux, huxp]
  · obtain ⟨e', rfl⟩ := hAΛ a' ha'
    have he'E : e' ∈ E := (hEmem e').mpr ha'
    obtain ⟨x', hx', hx'p⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (hEab.2 e' he'E)
    have hΛx' : Λ e' = MulAut.conj x' := hΛeq hx'
    have hψux : ψ (u * x⁻¹) ∈ E := by
      rw [map_mul, map_inv, hψu, hx]
      exact E.mul_mem (hψwu e heE) (E.inv_mem heE)
    have hcommψ : ψ x' * ψ (u * x⁻¹) = ψ (u * x⁻¹) * ψ x' := by
      rw [hx']
      exact TableB.IsElemAbelian.comm hEab he'E hψux
    have hcx' : x' * (u * x⁻¹) = (u * x⁻¹) * x' :=
      commute_of_lift_pow_eq_one hp hker hcpL hcommψ huxp
    rw [hux, hΛx', MulAut.conj_apply]
    calc x' * (u * x⁻¹) * x'⁻¹ = ((u * x⁻¹) * x') * x'⁻¹ := by rw [hcx']
      _ = u * x⁻¹ := by group

private theorem ggRealSgn_conj_mem_normalizer {L' R : Type} [Group L'] [Finite L'] [Group R]
    {ψ : L' →* R} {Λ : R →* MulAut L'} {A : Subgroup (MulAut L')} {E : Subgroup R}
    (hΛeq : ∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x)
    (hAΛ : ∀ a ∈ A, ∃ e, Λ e = a)
    (hEmem : ∀ e : R, e ∈ E ↔ Λ e ∈ A)
    {n' : L'} {w : R} (hn' : ψ n' = w) (hwE : w ∈ Subgroup.normalizer (E : Set R)) :
    MulAut.conj n' ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  refine mem_normalizer_of_forall_conj_mem fun b hb => ?_
  obtain ⟨e, rfl⟩ := hAΛ b hb
  have hwinv : w⁻¹ ∈ Subgroup.normalizer (E : Set R) := Subgroup.inv_mem _ hwE
  have hwe : w⁻¹ * e * w ∈ E := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp hwinv e).mp ((hEmem e).mpr hb)
  rw [← ggRealSgn_lift_conj_inv_mul Λ (hΛeq rfl) hn' e]
  exact (hEmem (w⁻¹ * e * w)).mp hwe

private theorem ggRealSgn_conjComm_map {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {E : Subgroup R} {w₀ : R} (h : GGKGConjCommAt E w₀) :
    GGKGConjCommAt (E.map e.toMonoidHom) (e w₀) := by
  intro u hu x hx
  obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
  have hu₀ : e.symm u ∈ Subgroup.normalizer (E : Set R) := by
    rw [Subgroup.mem_normalizer_iff] at hu ⊢
    intro y
    have hy : ∀ z : R, e z ∈ E.map e.toMonoidHom ↔ z ∈ E :=
      fun z => Subgroup.mem_map_iff_mem e.injective
    constructor
    · intro hyE
      have h1 : e (e.symm u * y * (e.symm u)⁻¹) ∈ E.map e.toMonoidHom := by
        simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using
          (hu (e y)).mp ((hy y).mpr hyE)
      exact (hy (e.symm u * y * (e.symm u)⁻¹)).mp h1
    · intro hyE
      have h2 : e y ∈ E.map e.toMonoidHom :=
        (hu (e y)).mpr (by
          simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using
            (hy (e.symm u * y * (e.symm u)⁻¹)).mpr hyE)
      exact (hy y).mp h2
  have hh := congrArg e (h (e.symm u) hu₀ x₀ hx₀)
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom] using hh

theorem ggTorusSgnComponents_of_sgnComponentDatum {p r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} (hp : p.Prime)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R) (h : GGKGSgnComponentDatum p r R) :
    GGTorusSgnComponents p r R I := by
  classical
  intro L' _ _ ψ A hTB φ hφauto hφrefl hcommφ
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, h3, hsc⟩ := hTB
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ', hφ'I, hφ'⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ' ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ', ih]
    have hφp : φ' ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ' hφ'I hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ' l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hEmem : ∀ e : R, e ∈ E ↔ Λ e ∈ A := by
    intro e
    rw [hE]
    exact Subgroup.mem_comap
  have hΦmem : ∀ e : E, Λ (e : R) ∈ A := fun e => Subgroup.mem_comap.mp (hE ▸ e.2)
  let Φfun : E → A := fun e => (⟨Λ (e : R), hΦmem e⟩ : A)
  have hΦfun_val : ∀ e : E, (Φfun e : MulAut L') = Λ (e : R) := fun e => rfl
  have hΦbij : Function.Bijective Φfun := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective Φfun hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn n, hn] at h1
    exact h1
  have h3' : p ^ 3 ≤ Nat.card E := hcardE ▸ h3
  have hr' : p ^ r ≤ Nat.card E := hcardE ▸ hr
  obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hφauto
  have hvφ : φ = ggConjAut A hcN := MulEquiv.ext fun b => Subtype.ext (hvc b)
  set w₀ : R := ψ n with hw₀
  have hΛw0 : Λ w₀ = MulAut.conj n := by rw [hw₀, hΛn n]
  have hconj : ∀ e : R, Λ (w₀ * e * w₀⁻¹) = MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ :=
    fun e => ggRealSgn_lift_conj_mul_inv Λ (hΛn n) hw₀.symm e
  have hnorm : w₀ ∈ Subgroup.normalizer (E : Set R) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      have h2 : MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hcN (Λ e)).mp ((hEmem e).mp he)
      rwa [← hconj e] at h2
    · intro he
      have h2 : MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ ∈ A := by
        rw [← hconj e]
        exact he
      exact (Subgroup.mem_normalizer_iff.mp hcN (Λ e)).mpr h2
  have hinv : ∀ e ∈ E, w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹ = e := by
    intro e he
    refine hΛinj ?_
    have hconj2 : ggConjAut A hcN ^ 2 = 1 := by rw [← hvφ, hφrefl.1]
    have hpow : (MulAut.conj n) ^ 2 * Λ e * ((MulAut.conj n) ^ 2)⁻¹ = Λ e := by
      have h1 : (((ggConjAut A hcN ^ 2) ⟨Λ e, (hEmem e).mp he⟩ : ↥A) : MulAut L') = Λ e := by
        rw [hconj2]
        rfl
      rwa [ggConjAut_pow_apply A hcN 2 ⟨Λ e, (hEmem e).mp he⟩] at h1
    calc Λ (w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹)
        = MulAut.conj n * (MulAut.conj n * Λ e * (MulAut.conj n)⁻¹) *
            (MulAut.conj n)⁻¹ := by
          rw [map_mul, map_mul, hconj e, map_inv, hΛw0]
      _ = (MulAut.conj n) ^ 2 * Λ e * ((MulAut.conj n) ^ 2)⁻¹ := by
          rw [pow_two]
          group
      _ = Λ e := hpow
  have hfixcard : Nat.card {e : E // w₀ * (e : R) * w₀⁻¹ = e} * p = Nat.card E := by
    rw [show Nat.card {e : E // w₀ * (e : R) * w₀⁻¹ = e} =
        Nat.card {b : A // φ b = b} from
      Nat.card_congr (Equiv.subtypeEquiv
        (Equiv.ofBijective Φfun hΦbij) (fun e => ?_))]
    · rw [hφrefl.2, hcardE]
    · constructor
      · intro he
        apply Subtype.ext
        rw [Equiv.coe_ofBijective, hvc, hΦfun_val e, ← hconj (e : R), he]
      · intro hb
        have h1 : MulAut.conj n * Λ (e : R) * (MulAut.conj n)⁻¹ = Λ (e : R) := by
          have h2 := congrArg (fun b : ↥A => ((b : ↥A) : MulAut L')) hb
          rw [Equiv.coe_ofBijective] at h2
          rw [hvc, hΦfun_val e] at h2
          exact h2
        rw [← hconj (e : R)] at h1
        exact hΛinj h1
  have hrefl : GGKGIsReflAt p E w₀ := ⟨hnorm, hinv, hfixcard⟩
  have hcomm : GGKGConjCommAt E w₀ := by
    intro u hu e he
    obtain ⟨m, rfl⟩ := hψ u
    have hψwu : ∀ x ∈ E, ψ m * x * (ψ m)⁻¹ ∈ E := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp hu x).mp hx
    have hW : GGTorusWeylElt p A m :=
      ggRealSgn_weylElt hp hψ hker hcpL hΛeq hAΛ hEmem hEab rfl hψwu
    have hmN : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
      ggRealSgn_conj_mem_normalizer hΛeq hAΛ hEmem rfl hu
    have hc := hcommφ m hmN hW
    have hc' : ggConjAut A hmN * ggConjAut A hcN * (ggConjAut A hmN)⁻¹ * ggConjAut A hcN
        = ggConjAut A hcN * (ggConjAut A hmN * ggConjAut A hcN * (ggConjAut A hmN)⁻¹) := by
      simpa only [hvφ, Commute, SemiconjBy] using hc
    have hcval := congrArg (fun f : MulAut ↥A =>
      ((f ⟨Λ e, (hEmem e).mp he⟩ : ↥A) : MulAut L')) hc'
    have hLval :
        ((ggConjAut A hmN * ggConjAut A hcN * (ggConjAut A hmN)⁻¹ * ggConjAut A hcN)
            ⟨Λ e, (hEmem e).mp he⟩ : MulAut L')
          = (MulAut.conj m * MulAut.conj n * (MulAut.conj m)⁻¹ * MulAut.conj n) * Λ e *
            (MulAut.conj m * MulAut.conj n * (MulAut.conj m)⁻¹ * MulAut.conj n)⁻¹ := by
      simp only [MulAut.mul_apply, ggConjAut_apply]
      rw [inv_apply_of_forall (fun b => ggConjAut_apply A hmN b)]
      simp only [ggConjAut_apply]
      group
    have hRval :
        ((ggConjAut A hcN * (ggConjAut A hmN * ggConjAut A hcN * (ggConjAut A hmN)⁻¹))
            ⟨Λ e, (hEmem e).mp he⟩ : MulAut L')
          = (MulAut.conj n * MulAut.conj m * MulAut.conj n * (MulAut.conj m)⁻¹) * Λ e *
            (MulAut.conj n * MulAut.conj m * MulAut.conj n * (MulAut.conj m)⁻¹)⁻¹ := by
      simp only [MulAut.mul_apply, ggConjAut_apply]
      rw [inv_apply_of_forall (fun b => ggConjAut_apply A hmN b)]
      dsimp only
      group
    have hpform : Λ (ψ m * w₀ * (ψ m)⁻¹) =
        MulAut.conj m * MulAut.conj n * (MulAut.conj m)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hΛn m, hΛw0]
    refine hΛinj ?_
    calc Λ ((ψ m * w₀ * (ψ m)⁻¹) * (w₀ * e * w₀⁻¹) * (ψ m * w₀ * (ψ m)⁻¹)⁻¹)
        = (MulAut.conj m * MulAut.conj n * (MulAut.conj m)⁻¹ * MulAut.conj n) * Λ e *
            (MulAut.conj m * MulAut.conj n * (MulAut.conj m)⁻¹ * MulAut.conj n)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hpform, hconj e]
          group
      _ = ((ggConjAut A hmN * ggConjAut A hcN * (ggConjAut A hmN)⁻¹ * ggConjAut A hcN)
            ⟨Λ e, (hEmem e).mp he⟩ : MulAut L') := hLval.symm
      _ = ((ggConjAut A hcN * (ggConjAut A hmN * ggConjAut A hcN * (ggConjAut A hmN)⁻¹))
            ⟨Λ e, (hEmem e).mp he⟩ : MulAut L') := hcval
      _ = (MulAut.conj n * MulAut.conj m * MulAut.conj n * (MulAut.conj m)⁻¹) * Λ e *
            (MulAut.conj n * MulAut.conj m * MulAut.conj n * (MulAut.conj m)⁻¹)⁻¹ := hRval
      _ = Λ (w₀ * ((ψ m * w₀ * (ψ m)⁻¹) * e * (ψ m * w₀ * (ψ m)⁻¹)⁻¹) * w₀⁻¹) := by
          rw [hconj ((ψ m * w₀ * (ψ m)⁻¹) * e * (ψ m * w₀ * (ψ m)⁻¹)⁻¹),
            map_mul, map_mul, map_inv, hpform]
          group
  obtain ⟨w, hw, J, hwJ, hJcomp, hpJ⟩ := h E hEab h3' hr' hscE w₀ hrefl hcomm
  set F : Subgroup R := E ⊓ Subgroup.centralizer ({w} : Set R) with hF
  set C : Subgroup R := Subgroup.centralizer (F : Set R) with hC
  have hJcompC : IsComponentOf J C := by
    simpa only [hC, hF] using hJcomp
  have hYmap : (C.comap ψ).map ψ = C := Subgroup.map_comap_eq_self_of_surjective hψ C
  have hn : (((C.comap ψ).map ψ).subgroupOf C).Normal := by
    rw [hYmap, Subgroup.subgroupOf_self]
    infer_instance
  have hc : ⁅C, C⁆ ≤ (C.comap ψ).map ψ := by
    rw [hYmap]
    simpa only [sup_idem] using Subgroup.commutator_le_sup C C
  obtain ⟨Q', hQ'comp_open, hQ'map⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T123CB.exists_component_lift_of_commutator_le ψ
      (fun g hg => hker hg) (le_of_eq hYmap) hn hc (CFSG.Assembly.isComponentOf_iff_open.mp hJcompC)
  have hQ'comp : IsComponentOf Q' (C.comap ψ) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hQ'comp_open
  have hpQ' : p ∣ Nat.card Q' := by
    have hdvd : Nat.card J ∣ Nat.card Q' := by
      rw [← hQ'map]
      exact Subgroup.card_map_dvd Q' ψ
    exact hpJ.trans hdvd
  obtain ⟨n', hn'Q', hn'⟩ : ∃ n' ∈ Q', ψ n' = w := by
    have hwQ' : w ∈ Q'.map ψ := by rw [hQ'map]; exact hwJ
    exact Subgroup.mem_map.mp hwQ'
  have hΛw : Λ w = MulAut.conj n' := by rw [← hn', hΛn n']
  have hHypCent : ggHypCent A n' = C.comap ψ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro f hf
      obtain ⟨hfE, hfw⟩ := Subgroup.mem_inf.mp hf
      have hfw' : w * f = f * w := (Subgroup.mem_centralizer_singleton_iff.mp hfw).symm
      have hcommconj : MulAut.conj n' * Λ f = Λ f * MulAut.conj n' := by
        refine mul_inv_eq_iff_eq_mul.mp ?_
        rw [← ggRealSgn_lift_conj_mul_inv Λ (hΛn n') hn' f,
          show w * f * w⁻¹ = f by rw [hfw']; group]
      have hxfix : x ∈ ggFix (Λ f) :=
        Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx (Λ f))
          ⟨show Λ f ∈ A from hfE, hcommconj⟩
      have h1 : f * ψ x * f⁻¹ = ψ x := by
        have h1' : Λ f x = x := mem_ggFix.mp hxfix
        rw [← hΛmap, h1']
      have h2 : f * ψ x = ψ x * f := by
        calc f * ψ x = (f * ψ x * f⁻¹) * f := by group
          _ = ψ x * f := by rw [h1]
      exact h2
    · intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hx
      rw [ggHypCent]
      refine Subgroup.mem_iInf.mpr fun a => Subgroup.mem_iInf.mpr fun ha => ?_
      obtain ⟨e, rfl⟩ := hAΛ a ha.1
      have heE : e ∈ E := show Λ e ∈ A from ha.1
      have hwe : w * e = e * w := by
        have h1 : (MulAut.conj n' * Λ e) * (MulAut.conj n')⁻¹ = Λ e :=
          mul_inv_eq_iff_eq_mul.mpr ha.2
        rw [← ggRealSgn_lift_conj_mul_inv Λ (hΛn n') hn' e] at h1
        exact mul_inv_eq_iff_eq_mul.mp (hΛinj h1)
      have heF : e ∈ F := ⟨heE, Subgroup.mem_centralizer_singleton_iff.mpr hwe.symm⟩
      rw [mem_ggFix]
      obtain ⟨xe, hxe, hxep⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (hEab.2 e heE)
      have hcx : x * xe = xe * x :=
        commute_of_lift_pow_eq_one hp hker hcpL (by rw [hxe]; exact (hx e heF).symm) hxep
      rw [hΛeq hxe, MulAut.conj_apply]
      calc xe * x * xe⁻¹ = (x * xe) * xe⁻¹ := by rw [hcx]
        _ = x := by group
  have hψwu : ∀ e ∈ E, w * e * w⁻¹ ∈ E := by
    intro e he
    rw [hw e he]
    exact (Subgroup.mem_normalizer_iff.mp hnorm e).mp he
  have hWeyl : GGTorusWeylElt p A n' :=
    ggRealSgn_weylElt hp hψ hker hcpL hΛeq hAΛ hEmem hEab hn' hψwu
  have hwE : w ∈ Subgroup.normalizer (E : Set R) := by
    have : Finite R := Finite.of_surjective ψ hψ
    have hle : E.map (MulAut.conj w).toMonoidHom ≤ E := by
      rw [Subgroup.map_le_iff_le_comap]
      intro e he
      change w * e * w⁻¹ ∈ E
      exact hψwu e he
    have hcard : Nat.card (E.map (MulAut.conj w).toMonoidHom) = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj w).injective
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hle hcard.ge)
  have hn'N : MulAut.conj n' ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    ggRealSgn_conj_mem_normalizer hΛeq hAΛ hEmem hn' hwE
  have hconjAut : ggConjAut A hn'N = φ := by
    rw [show φ = ggConjAut A hcN from hvφ]
    refine MulEquiv.ext fun b => Subtype.ext ?_
    obtain ⟨e, he⟩ := hAΛ (b : MulAut L') b.2
    have heE : e ∈ E := show Λ e ∈ A from he ▸ b.2
    rw [ggConjAut_apply, ggConjAut_apply, ← he,
      ← ggRealSgn_lift_conj_mul_inv Λ (hΛn n') hn' e, hw e heE, hconj e]
  exact ⟨n', hn'N, Q', hWeyl, hconjAut, hn'Q', by rw [hHypCent]; exact hQ'comp, hpQ'⟩

theorem ggKGSgnComponentDatum_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : GGKGSgnComponentDatum p r R') : GGKGSgnComponentDatum p r R := by
  intro E hEab h3 hr hsc
  let E' : Subgroup R' := E.map e.toMonoidHom
  have hEab' : IsElemAbelian p E' := CFSG.Open.IsElemAbelian.map hEab e.toMonoidHom
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (ggRealSgn_injective_toMonoidHom e)
  have h3' : p ^ 3 ≤ Nat.card E' := by rw [hcardE']; exact h3
  have hr' : p ^ r ≤ Nat.card E' := by rw [hcardE']; exact hr
  have hsc' : ∀ g : R', (∀ e' ∈ E', g * e' = e' * g) → g ^ p = 1 → g ∈ E' := by
    intro g hg hgp
    have hcomm : ∀ x ∈ E, e.symm g * x = x * e.symm g := by
      intro x hx
      have h1 : e x ∈ E' := Subgroup.mem_map_of_mem e.toMonoidHom hx
      have h2 : g * e x = e x * g := hg (e x) h1
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h2
    have hge : e.symm g ∈ E := hsc (e.symm g) hcomm (by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hgp, map_one])
    rw [← MulEquiv.apply_symm_apply e g]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hge
  have hAt : GGKGSgnComponentDatumAt p E' := h E' hEab' h3' hr' hsc'
  intro w₀ hw₀ hcomm₀
  have hw₀' : GGKGIsReflAt p E' (e w₀) :=
    hw₀.map e.toMonoidHom (ggRealSgn_injective_toMonoidHom e)
  have hcomm₀' : GGKGConjCommAt E' (e w₀) := ggRealSgn_conjComm_map e hcomm₀
  obtain ⟨w', hw'formula, J', hw'J', hJ'comp, hpJ'⟩ := hAt (e w₀) hw₀' hcomm₀'
  let w : R := e.symm w'
  have hew : e w = w' := e.apply_symm_apply w'
  let J : Subgroup R := J'.comap e.toMonoidHom
  have hCmap : (Subgroup.centralizer
        ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R)).map e.toMonoidHom =
      Subgroup.centralizer
        ((E' ⊓ Subgroup.centralizer ({w'} : Set R') : Subgroup R') : Set R') := by
    rw [ggRealSgn_map_centralizer]
    congr 1
    change ⇑e.toMonoidHom '' ↑(E ⊓ Subgroup.centralizer ({w} : Set R)) =
      ↑(Subgroup.map e.toMonoidHom E ⊓ Subgroup.centralizer ({w'} : Set R'))
    rw [← Subgroup.coe_map e.toMonoidHom (E ⊓ Subgroup.centralizer ({w} : Set R)),
      Subgroup.map_inf _ _ _ (ggRealSgn_injective_toMonoidHom e)]
    rw [ggRealSgn_map_centralizer e ({w} : Set R), Set.image_singleton, hew]
  have hcomp' : Assembly.IsComponentOf J'
      (Subgroup.map e.toMonoidHom (Subgroup.centralizer
        ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R))) := by
    rw [hCmap]
    exact hJ'comp
  have hJcomp : Assembly.IsComponentOf (J'.comap e.toMonoidHom)
      (Subgroup.centralizer ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R)) :=
    (isComponentOf_comap_of_injective e.toMonoidHom (ggRealSgn_injective_toMonoidHom e) hcomp').1
  have hJmap : (J'.comap e.toMonoidHom).map e.toMonoidHom = J' :=
    (isComponentOf_comap_of_injective e.toMonoidHom (ggRealSgn_injective_toMonoidHom e) hcomp').2
  refine ⟨w, ?_, J'.comap e.toMonoidHom, ?_, hJcomp, ?_⟩
  · intro a ha
    have ha' : e a ∈ E' := Subgroup.mem_map_of_mem e.toMonoidHom ha
    have h' : w' * e a * w'⁻¹ = e w₀ * e a * (e w₀)⁻¹ := hw'formula (e a) ha'
    apply e.injective
    simp only [map_mul, map_inv]
    rw [hew]
    exact h'
  · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hew]
    exact hw'J'
  · rw [← Subgroup.card_map_of_injective (ggRealSgn_injective_toMonoidHom e)
      (K := J'.comap e.toMonoidHom), hJmap]
    exact hpJ'

end CFSG.StandardType

end
