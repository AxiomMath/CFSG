module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPoint
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

theorem sq_surj_K (a : K) : ∃ b : K, b ^ 2 = a :=
  Finite.surjective_of_injective (f := fun x : K => x ^ 2) CharTwo.sq_injective a

theorem qf_add {Q : QuadraticForm K V} (hQ : Q.polarBilin = F) (x y : V) :
    Q (x + y) = Q x + Q y + F x y := by
  rw [← hQ, QuadraticMap.polarBilin_apply_apply]
  exact QuadraticMap.map_add _ x y

theorem qf_smul {Q : QuadraticForm K V} (c : K) (x : V) : Q (c • x) = c ^ 2 * Q x := by
  rw [QuadraticMap.map_smul, smul_eq_mul, sq]

theorem polarBilin_symm' {Q : QuadraticForm K V} (hQ : Q.polarBilin = F) (x y : V) :
    F x y = F y x := by
  rw [← hQ, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
  exact QuadraticMap.polar_comm _ x y

theorem exists_linear_sqrt (dl : V → K) (hadd : ∀ v w : V, dl (v + w) = dl v + dl w)
    (hsmul : ∀ (c : K) (v : V), dl (c • v) = c ^ 2 * dl v) :
    ∃ φ : V →ₗ[K] K, ∀ v, φ v ^ 2 = dl v := by
  have hsq' : ∀ a : K, ∃ b : K, b ^ 2 = a := sq_surj_K
  choose σ hσ using hsq'
  obtain ⟨φ0, hφ0⟩ : ∃ φ0 : V → K, ∀ v, φ0 v = σ (dl v) :=
    ⟨fun v => σ (dl v), fun v => rfl⟩
  have hsq : ∀ v, φ0 v ^ 2 = dl v := fun v => by rw [hφ0, hσ]
  have hadd' : ∀ v w : V, φ0 (v + w) = φ0 v + φ0 w := by
    intro v w
    apply CharTwo.sq_inj.mp
    rw [CharTwo.add_sq, hsq, hsq, hsq, hadd]
  have hsmul' : ∀ (c : K) (v : V), φ0 (c • v) = c * φ0 v := by
    intro c v
    apply CharTwo.sq_inj.mp
    rw [hsq, hsmul, mul_pow, hsq]
  exact ⟨{ toFun := φ0
           map_add' := hadd'
           map_smul' := fun c v => by rw [hsmul' c v, RingHom.id_apply, smul_eq_mul] },
    fun v => hsq v⟩

theorem exists_vec_of_linear (hnd : F.Nondegenerate) (hsymm : ∀ x y : V, F x y = F y x)
    (φ : V →ₗ[K] K) : ∃ u : V, ∀ v, F v u = φ v := by
  obtain ⟨u, hu⟩ := (LinearMap.BilinForm.toDual F hnd).surjective φ
  refine ⟨u, fun v => ?_⟩
  rw [hsymm, ← LinearMap.BilinForm.toDual_def hnd, hu]

theorem quadForm_sub_eq_sq (hnd : F.Nondegenerate) (Q Q' : QuadraticForm K V)
    (hQ : Q.polarBilin = F) (hQ' : Q'.polarBilin = F) :
    ∃ u : V, ∀ v, Q' v = Q v + (F v u) ^ 2 := by
  have hadd : ∀ v w : V, Q' (v + w) - Q (v + w) = (Q' v - Q v) + (Q' w - Q w) := by
    intro v w
    rw [qf_add hQ', qf_add hQ]
    ring
  have hsmul : ∀ (c : K) (v : V), Q' (c • v) - Q (c • v) = c ^ 2 * (Q' v - Q v) := by
    intro c v
    rw [qf_smul, qf_smul]
    ring
  obtain ⟨φ, hφ⟩ := exists_linear_sqrt (fun v => Q' v - Q v) hadd hsmul
  obtain ⟨u, hu⟩ := exists_vec_of_linear hnd (polarBilin_symm' hQ) φ
  refine ⟨u, fun v => ?_⟩
  have h1 : Q' v - Q v = F v u ^ 2 := by
    rw [hu v]
    exact (hφ v).symm
  linear_combination h1

theorem quadForm_eq_of_elationFull (hnd : F.Nondegenerate) (halt : F.IsAlt)
    (hdim : 3 ≤ Module.finrank K V) {e f : V} (hef : F e f = 1) {D : Set (V ≃ₗ[K] V)}
    (hD : D ⊆ pointRad F e) (hfull : ElationFull F D e) {Q Q' : QuadraticForm K V}
    (hQ : Q.polarBilin = F) (hQ' : Q'.polarBilin = F)
    (hDQ : ∀ g ∈ D, ∀ v, Q (g v) = Q v) (hDQ' : ∀ g ∈ D, ∀ v, Q' (g v) = Q' v) :
    ∃ c : K, ∀ v, Q' v = Q v + c * (F v e) ^ 2 := by
  obtain ⟨u, hu⟩ := quadForm_sub_eq_sq hnd Q Q' hQ hQ'
  have hinv : ∀ g ∈ D, ∀ v, F (g v) u = F v u := by
    intro g hg v
    have a1 := hu (g v)
    rw [hDQ' g hg v, hDQ g hg v] at a1
    have h1 : F (g v) u ^ 2 = F v u ^ 2 := by linear_combination hu v - a1
    exact CharTwo.sq_inj.mp h1
  have hωu : ∀ g ∈ D, F (g f - f) u = 0 := by
    intro g hg
    simp only [map_sub, LinearMap.sub_apply, hinv g hg f, sub_self]
  have he_u : F e u = 0 := by
    by_contra hne
    have hvan : ∀ g ∈ D, ∀ y : V, F y e = 0 → F (g f - f) y = 0 := by
      intro g hg y hy
      have h1 := hinv g hg y
      rw [pointRad_apply_perp halt hef (hD hg) y hy] at h1
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul] at h1
      have h2 : F (g f - f) y * F e u = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2).resolve_right hne
    have hperp : ∀ ω : V, F ω e = 0 → ∀ y : V, F y e = 0 → F ω y = 0 := by
      intro ω hω y hy
      obtain ⟨g, hg, c, hgc⟩ := ElationFull.om hnd halt hef hD hfull hω
      have h1 : F (g f - f) y = F ω y := by
        rw [hgc]
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [form_comm halt e y, hy, mul_zero, add_zero]
      rw [← h1]
      exact hvan g hg y hy
    obtain ⟨ω, hω, hne'⟩ :=
      exists_perp_not_mem_span (F := F) hdim (ne_zero_of_form_eq_one hef)
    obtain ⟨c, hc⟩ := perp_perp hnd halt e ω (fun y hy => hperp ω hω y hy)
    exact hne' c hc
  have hperpu : ∀ ω : V, F ω e = 0 → F ω u = 0 := by
    intro ω hω
    obtain ⟨g, hg, c, hgc⟩ := ElationFull.om hnd halt hef hD hfull hω
    have h1 := hωu g hg
    rw [hgc] at h1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, he_u,
      mul_zero, add_zero] at h1
    exact h1
  have hperp_u : ∀ v : V, F v e = 0 → F u v = 0 := by
    intro v hv
    rw [form_comm halt u v]
    exact hperpu v hv
  obtain ⟨c', hc'⟩ := perp_perp hnd halt e u hperp_u
  refine ⟨c' ^ 2, fun v => ?_⟩
  rw [hu v, hc']
  simp only [map_smul, smul_eq_mul]
  ring

theorem qf_elation (halt : F.IsAlt) {e f ω : V} {Q : QuadraticForm K V} (hQ : Q.polarBilin = F)
    (he : Q e = 0) (hω : F ω e = 0) (v : V) :
    Q (elationEquiv halt e f ω hω v) = Q v + (F v e) ^ 2 * (Q ω + F f ω) := by
  rw [elationEquiv_apply, qf_add hQ, qf_add hQ, qf_smul, qf_smul, he]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hω]
  linear_combination (F v e * F v ω) * (two_eq_zero_K (K := K))

theorem pointRad_mem_orth_iff (halt : F.IsAlt) {e f : V} (hef : F e f = 1)
    {Q : QuadraticForm K V} (hQ : Q.polarBilin = F) (he : Q e = 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ pointRadSubgroup F e) :
    g ∈ orthSubgroup Q ↔ Q (g f - f) = F f (g f - f) := by
  have hωe : F (g f - f) e = 0 := pointRad_om_perp hg
  have hfe : F f e = 1 := by
    rw [form_comm halt]
    exact hef
  have hgf : g f = f + (g f - f) := by abel
  have hgeq : g = elationEquiv halt e f (g f - f) hωe := by
    apply pointRad_ext halt hef hg (elationEquiv_mem halt hef hωe)
    rw [elationEquiv_f halt hef hωe]
    exact hgf
  have hkey : ∀ v, Q (g v) = Q v + (F v e) ^ 2 * (Q (g f - f) + F f (g f - f)) := by
    intro v
    have h1 : g v = elationEquiv halt e f (g f - f) hωe v :=
      congrArg (fun h : V ≃ₗ[K] V => h v) hgeq
    rw [h1]
    exact qf_elation halt hQ he hωe v
  constructor
  · intro hmem
    have hmem' : ∀ v, Q (g v) = Q v := hmem
    have h1 := hmem' f
    rw [hkey f, hfe] at h1
    linear_combination h1 - (F f (g f - f)) * (two_eq_zero_K (K := K))
  · intro h
    change ∀ v, Q (g v) = Q v
    intro v
    rw [hkey v, h]
    linear_combination ((F v e) ^ 2 * F f (g f - f)) * (two_eq_zero_K (K := K))

theorem exists_quadForm_of_a (halt : F.IsAlt) {e f : V} (hef : F e f = 1) (a : V → K)
    (ha1 : ∀ (c : K) (w : V), F w e = 0 → F w f = 0 → a (c • w) = c ^ 2 * a w)
    (ha2 : ∀ w w' : V, F w e = 0 → F w f = 0 → F w' e = 0 → F w' f = 0 →
      a (w + w') = a w + a w' + F w w') :
    ∃ Q : QuadraticForm K V, Q.polarBilin = F ∧
      ∀ v, Q v = F v e * F v f + a (v + F v f • e + F v e • f) := by
  have hfe : F f e = 1 := by
    rw [form_comm halt]
    exact hef
  have hee : F e e = 0 := form_self halt e
  have hff : F f f = 0 := form_self halt f
  have hpe : ∀ v : V, F (v + F v f • e + F v e • f) e = 0 := by
    intro v
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hee,
      hfe]
    linear_combination (F v e) * (two_eq_zero_K (K := K))
  have hpf : ∀ v : V, F (v + F v f • e + F v e • f) f = 0 := by
    intro v
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hef,
      hff]
    linear_combination (F v f) * (two_eq_zero_K (K := K))
  have hpadd : ∀ v w : V, v + w + F (v + w) f • e + F (v + w) e • f =
      (v + F v f • e + F v e • f) + (w + F w f • e + F w e • f) := by
    intro v w
    simp only [map_add, LinearMap.add_apply, add_smul]
    module
  have hpsmul : ∀ (c : K) (v : V), c • v + F (c • v) f • e + F (c • v) e • f =
      c • (v + F v f • e + F v e • f) := by
    intro c v
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    module
  have hpbil : ∀ v w : V, F (v + F v f • e + F v e • f) (w + F w f • e + F w e • f) =
      F v w + F v e * F w f + F v f * F w e := by
    intro v w
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hee,
      hff, hef, hfe, form_comm halt e w, form_comm halt f w]
    linear_combination (F v e * F w f + F v f * F w e) * (two_eq_zero_K (K := K))
  obtain ⟨q, hq⟩ : ∃ q : V → K, ∀ v, q v = F v e * F v f + a (v + F v f • e + F v e • f) :=
    ⟨fun v => F v e * F v f + a (v + F v f • e + F v e • f), fun v => rfl⟩
  have hqsmul : ∀ (c : K) (v : V), q (c • v) = c ^ 2 * q v := by
    intro c v
    rw [hq (c • v), hq v, hpsmul c v, ha1 c _ (hpe v) (hpf v)]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hqadd : ∀ v w : V, q (v + w) = q v + q w + F v w := by
    intro v w
    rw [hq (v + w), hq v, hq w, hpadd v w, ha2 _ _ (hpe v) (hpf v) (hpe w) (hpf w),
      hpbil v w]
    simp only [map_add, LinearMap.add_apply]
    linear_combination (F v e * F w f + F v f * F w e) * (two_eq_zero_K (K := K))
  obtain ⟨Q, hQ⟩ : ∃ Q : QuadraticForm K V, ∀ v, Q v = q v :=
    ⟨{ toFun := q
       toFun_smul := fun c v => by rw [hqsmul c v, smul_eq_mul, sq]
       exists_companion' := ⟨F, hqadd⟩ }, fun v => rfl⟩
  refine ⟨Q, ?_, fun v => (hQ v).trans (hq v)⟩
  refine LinearMap.ext₂ fun x y => ?_
  have h1 := QuadraticMap.map_add ⇑Q x y
  rw [hQ (x + y), hQ x, hQ y] at h1
  rw [QuadraticMap.polarBilin_apply_apply]
  linear_combination hqadd x y - h1

end CFSG.RankThree.GF2n.Stroth80.Classify
