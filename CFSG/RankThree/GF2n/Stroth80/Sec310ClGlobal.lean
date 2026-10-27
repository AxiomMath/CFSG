module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClScalar
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPairDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClGraph

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

theorem mem_ElPts_iff {H : Subgroup (V ≃ₗ[K] V)} (e : V) :
    e ∈ ElPts F H ↔ e ≠ 0 ∧ ElationFull F ((H : Set _) ∩ pointRad F e) e :=
  Iff.rfl

theorem pointRad_set_smul {e : V} {c : K} (hc : c ≠ 0) :
    pointRad F (c • e) = pointRad F e := by
  unfold pointRad
  rw [pointRad_smul hc]

theorem ElPts_invariant {H : Subgroup (V ≃ₗ[K] V)} (hH : H ≤ sympSubgroup F) {g : V ≃ₗ[K] V}
    (hg : g ∈ H) {y : V} (hy : y ∈ ElPts F H) : g y ∈ ElPts F H := by
  obtain ⟨hy0, hyf⟩ := (mem_ElPts_iff y).mp hy
  refine (mem_ElPts_iff (g y)).mpr ⟨fun h => hy0 (g.injective (by rw [h, map_zero])), ?_⟩
  exact elationFull_conj hH hyf hg

theorem ElPts_smul {H : Subgroup (V ≃ₗ[K] V)} {c : K} (hc : c ≠ 0) {e : V}
    (he : e ∈ ElPts F H) : c • e ∈ ElPts F H := by
  obtain ⟨he0, hef⟩ := (mem_ElPts_iff e).mp he
  refine (mem_ElPts_iff (c • e)).mpr ⟨smul_ne_zero hc he0, ?_⟩
  rw [pointRad_set_smul hc]
  exact (elationFull_smul hc).mpr hef

theorem quadForm_smul_zero (Q : QuadraticForm K V) {c : K} {e : V} (he : Q e = 0) :
    Q (c • e) = 0 := by
  rw [QuadraticMap.map_smul, he, smul_zero]

theorem pairing_normalize {e r : V} (h : F e r ≠ 0) : F e ((F e r)⁻¹ • r) = 1 := by
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ h]

theorem exists_partner_ElPts {H : Subgroup (V ≃ₗ[K] V)} (hnd : F.Nondegenerate)
    (hspan : Submodule.span K (ElPts F H) = ⊤) {e₀ : V} (he₀ : e₀ ∈ ElPts F H) :
    ∃ r ∈ ElPts F H, F e₀ r ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact ((mem_ElPts_iff e₀).mp he₀).1 (eq_zero_of_perp_span hnd hspan hcon)

theorem exists_global_form (hnd : F.Nondegenerate) (halt : F.IsAlt)
    {H : Subgroup (V ≃ₗ[K] V)} (hH : H ≤ sympSubgroup F) (hne : (ElPts F H).Nonempty)
    (hspan : Submodule.span K (ElPts F H) = ⊤)
    (hF1 : ∀ e f : V, e ∈ ElPts F H → f ∈ ElPts F H → F e f = 1 → ∃ Q, PairForm F H e f Q)
    (hsame : ∀ e f s : V, e ∈ ElPts F H → f ∈ ElPts F H → s ∈ ElPts F H → F e f = 1 →
      F e s = 1 → ∀ Q Q' : QuadraticForm K V, PairForm F H e f Q → PairForm F H e s Q' → Q = Q') :
    ∃ Q : QuadraticForm K V, Q.polarBilin = F ∧
      ∀ e ∈ ElPts F H, Q e = 0 ∧ H ⊓ pointRadSubgroup F e ≤ orthSubgroup Q := by
  obtain ⟨e₀, he₀⟩ := hne
  obtain ⟨r, hr, hrne⟩ := exists_partner_ElPts hnd hspan he₀
  obtain ⟨f₀, hf₀def⟩ : ∃ x : V, x = (F e₀ r)⁻¹ • r := ⟨_, rfl⟩
  have hf₀ : f₀ ∈ ElPts F H := by
    rw [hf₀def]
    exact ElPts_smul (inv_ne_zero hrne) hr
  have hef₀ : F e₀ f₀ = 1 := by
    rw [hf₀def]
    exact pairing_normalize hrne
  obtain ⟨Q, hQ⟩ := hF1 e₀ f₀ he₀ hf₀ hef₀
  unfold PairForm at hQ
  obtain ⟨P, hP⟩ : ∃ P : V → Prop, ∀ e, P e ↔ (e ∈ ElPts F H ∧ Q e = 0 ∧
      H ⊓ pointRadSubgroup F e ≤ orthSubgroup Q ∧ ∃ r ∈ ElPts F H, F e r ≠ 0 ∧ Q r = 0 ∧
        H ⊓ pointRadSubgroup F r ≤ orthSubgroup Q) :=
    ⟨fun e => e ∈ ElPts F H ∧ Q e = 0 ∧
      H ⊓ pointRadSubgroup F e ≤ orthSubgroup Q ∧ ∃ r ∈ ElPts F H, F e r ≠ 0 ∧ Q r = 0 ∧
        H ⊓ pointRadSubgroup F r ≤ orthSubgroup Q, fun e => Iff.rfl⟩
  have hadj : ∀ e e' : V, P e → e' ∈ ElPts F H → F e e' ≠ 0 → P e' := by
    intro e e' hPe he' hee'
    obtain ⟨he, heQ, heH, r₀, hr₀, hr₀e, hr₀Q, hr₀H⟩ := (hP e).mp hPe
    obtain ⟨r₁, hr₁def⟩ : ∃ x : V, x = (F e r₀)⁻¹ • r₀ := ⟨_, rfl⟩
    have hr₁ : r₁ ∈ ElPts F H := by
      rw [hr₁def]
      exact ElPts_smul (inv_ne_zero hr₀e) hr₀
    have hF₁ : F e r₁ = 1 := by
      rw [hr₁def]
      exact pairing_normalize hr₀e
    have hQr₁ : Q r₁ = 0 := by
      rw [hr₁def]
      exact quadForm_smul_zero Q hr₀Q
    have hHr₁ : H ⊓ pointRadSubgroup F r₁ ≤ orthSubgroup Q := by
      rw [hr₁def, pointRad_smul (inv_ne_zero hr₀e)]
      exact hr₀H
    have hpair₁ : PairForm F H e r₁ Q := by
      unfold PairForm
      exact ⟨hQ.1, heQ, hQr₁, heH, hHr₁⟩
    obtain ⟨e'', he''def⟩ : ∃ x : V, x = (F e e')⁻¹ • e' := ⟨_, rfl⟩
    have he'' : e'' ∈ ElPts F H := by
      rw [he''def]
      exact ElPts_smul (inv_ne_zero hee') he'
    have hF'' : F e e'' = 1 := by
      rw [he''def]
      exact pairing_normalize hee'
    obtain ⟨Q'', hQ''⟩ := hF1 e e'' he he'' hF''
    have hQQ : Q = Q'' := hsame e r₁ e'' he hr₁ he'' hF₁ hF'' Q Q'' hpair₁ hQ''
    have hpair'' : PairForm F H e e'' Q := by
      rw [hQQ]
      exact hQ''
    unfold PairForm at hpair''
    obtain ⟨-, -, hQe'', -, hHe''⟩ := hpair''
    have hscale : (F e e') • e'' = e' := by
      rw [he''def, smul_smul, mul_inv_cancel₀ hee', one_smul]
    refine (hP e').mpr ⟨he', ?_, ?_, e, he, ?_, ?_, ?_⟩
    · rw [← hscale]
      exact quadForm_smul_zero Q hQe''
    · rw [← hscale, pointRad_smul hee']
      exact hHe''
    · rw [form_comm halt]
      exact hee'
    · exact heQ
    · exact heH
  have hPall : ∀ x, Relation.ReflTransGen
      (fun a b => a ∈ ElPts F H ∧ b ∈ ElPts F H ∧ F a b ≠ 0) e₀ x → P x := by
    intro x hx
    induction hx with
    | refl =>
      exact (hP e₀).mpr ⟨he₀, hQ.2.1, hQ.2.2.2.1, f₀, hf₀, (by rw [hef₀]; exact one_ne_zero),
        hQ.2.2.1, hQ.2.2.2.2⟩
    | tail _ hbc ih =>
      obtain ⟨-, hcS, hbc0⟩ := hbc
      exact hadj _ _ ih hcS hbc0
  have hconn := connected_of_elationFull hnd halt hH (ElPts F H)
    (fun y hy => ((mem_ElPts_iff y).mp hy).1)
    (fun g hg y hy => ElPts_invariant hH hg hy) hspan he₀ ((mem_ElPts_iff e₀).mp he₀).2
  refine ⟨Q, hQ.1, fun e he => ?_⟩
  obtain ⟨-, hQe, hHe, -⟩ := (hP e).mp (hPall e (hconn e he))
  exact ⟨hQe, hHe⟩

end CFSG.RankThree.GF2n.Stroth80.Classify
