module

public import CFSG.Quasithin.Background.RonanE43Out
public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.Quasithin.RonanE43

open Equiv Equiv.Perm CFSG.ComponentClassification CFSG.Quasithin.SteinbergCB

@[expose] def KleinP3 (q₁ q₂ : Perm (Fin 5)) : Prop :=
  ∀ σ : Perm (Fin 5), Perm.sign σ ≠ 1 → σ * σ = 1 → σ * q₁ = q₁ * σ → σ * q₂ = q₂ * σ → False

instance (q₁ q₂ : Perm (Fin 5)) : Decidable (KleinP3 q₁ q₂) := by
  unfold KleinP3
  infer_instance

@[expose] def KleinP2 (q₁ : Perm (Fin 5)) : Prop :=
  ∀ q₂ : Perm (Fin 5), Perm.sign q₂ = 1 → q₂ ≠ 1 → q₂ ≠ q₁ → q₂ * q₂ = 1 →
    q₁ * q₂ = q₂ * q₁ → KleinP3 q₁ q₂

instance (q₁ : Perm (Fin 5)) : Decidable (KleinP2 q₁) := by
  unfold KleinP2
  infer_instance

theorem kleinP2_all : ∀ q₁ : Perm (Fin 5), Perm.sign q₁ = 1 → q₁ ≠ 1 → q₁ * q₁ = 1 →
    KleinP2 q₁ := by
  decide +kernel

theorem no_odd_involution_centralizes_klein :
    ∀ q₁ : Perm (Fin 5), Perm.sign q₁ = 1 → q₁ ≠ 1 → q₁ * q₁ = 1 →
    ∀ q₂ : Perm (Fin 5), Perm.sign q₂ = 1 → q₂ ≠ 1 → q₂ ≠ q₁ → q₂ * q₂ = 1 →
      q₁ * q₂ = q₂ * q₁ →
    ∀ σ : Perm (Fin 5), Perm.sign σ ≠ 1 → σ * σ = 1 → σ * q₁ = q₁ * σ →
      σ * q₂ = q₂ * σ → False :=
  fun q₁ h1 h2 h3 q₂ h4 h5 h6 h7 h8 => kleinP2_all q₁ h1 h2 h3 q₂ h4 h5 h6 h7 h8

theorem center_eq_bot_of_A5 {N : Type*} [Group N] (e : N ≃* alternatingGroup (Fin 5)) :
    Subgroup.center N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have h1 : e z ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g']
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at h1
  exact e.injective (h1.trans (map_one e).symm)

theorem card_le_four_of_A5 {K : Type} [Group K] [Finite K] (N : Subgroup K) [hN : N.Normal]
    (e : ↥N ≃* alternatingGroup (Fin 5)) (h2 : ∀ x : K, ∃ n : ℕ, x ^ 2 ^ n ∈ N)
    (hO2 : CFSG.pCore 2 K = ⊥) {E : Subgroup K} (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ 4 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center ↥N = ⊥ := center_eq_bot_of_A5 e
  let ψ : K →* MulAut ↥N := MulAut.conjNormal
  have hψapp : ∀ (k : K) (n : ↥N), ((ψ k n : ↥N) : K) = k * (n : K) * k⁻¹ :=
    fun k n => MulAut.conjNormal_apply k n
  have hψker : ψ.ker = ⊥ := by
    have hp : IsPGroup 2 ψ.ker := by
      intro c
      obtain ⟨n, hn⟩ := h2 (c : K)
      have hcn : ((c : K) ^ 2 ^ n) ∈ (ψ.ker : Subgroup K) := ψ.ker.pow_mem c.2 _
      have hcomm : ⟨(c : K) ^ 2 ^ n, hn⟩ ∈ Subgroup.center ↥N := by
        rw [Subgroup.mem_center_iff]
        intro m
        have h1 : ψ ((c : K) ^ 2 ^ n) = 1 := hcn
        have h2' := congrArg (fun f : MulAut ↥N => ((f m : ↥N) : K)) h1
        simp only [hψapp, MulAut.one_apply] at h2'
        apply Subtype.ext
        show (m : K) * (c : K) ^ 2 ^ n = (c : K) ^ 2 ^ n * (m : K)
        exact (mul_inv_eq_iff_eq_mul.mp h2').symm
      rw [hZ, Subgroup.mem_bot] at hcomm
      refine ⟨n, Subtype.ext ?_⟩
      have := congrArg Subtype.val hcomm
      simpa using this
    have hle : ψ.ker ≤ CFSG.pCore 2 K := CFSG.LieType.BorelTits.le_pCore 2 inferInstance hp
    rw [hO2] at hle
    exact le_bot_iff.mp hle
  have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hψker
  have hψN : ∀ k : K, ψ k ∈ OuterAutomorphisms.inner ↥N → k ∈ N := by
    intro k hk
    obtain ⟨m, hm⟩ := hk
    have : ψ (m : K) = MulAut.conj m := by
      ext n
      rw [hψapp]
      simp [MulAut.conj_apply]
    have hkm : k = (m : K) := hψinj (by rw [← hm, this])
    rw [hkm]
    exact m.2
  have hψinner : ∀ n : ↥N, ψ (n : K) ∈ OuterAutomorphisms.inner ↥N := fun n =>
    ⟨n, by ext x; rw [hψapp]; simp [MulAut.conj_apply]⟩
  have hNidx : N.index ∣ 2 := by
    have hcomap : (OuterAutomorphisms.inner ↥N).comap ψ = N := by
      ext k
      exact ⟨hψN k, fun hk => hψinner ⟨k, hk⟩⟩
    have h1 : N.index = (OuterAutomorphisms.inner ↥N).relIndex ψ.range := by
      have h3 := Subgroup.index_comap (OuterAutomorphisms.inner ↥N) ψ
      rw [hcomap] at h3
      exact h3
    have h2' : (OuterAutomorphisms.inner ↥N).index = (OuterAutomorphisms.inner (alternatingGroup (Fin 5))).index := by
      have := card_outer_eq_of_mulEquiv e
      rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card] at this
      exact this
    rw [h1]
    exact (Subgroup.relIndex_dvd_index_of_normal _ _).trans
      (h2'.symm ▸ index_inner_dvd_two (Or.inl rfl))
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := hE.2
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE2 x x.2)⟩
  have hN60 : Nat.card ↥N = 60 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  set Q : Subgroup K := N ⊓ E with hQ
  have hQ2 : IsPGroup 2 Q := hEp.to_le inf_le_right
  have hQ4 : Nat.card Q ≤ 4 := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hQ2
    have hdvd : Nat.card Q ∣ 60 := by
      rw [← hN60]
      exact Subgroup.card_dvd_of_le inf_le_left
    by_contra hlt
    push Not at hlt
    rw [hm] at hlt hdvd
    have hm3 : 3 ≤ m := by
      by_contra h
      push Not at h
      interval_cases m <;> omega
    have : 2 ^ 3 ∣ 2 ^ m := pow_dvd_pow 2 hm3
    have h8 : 8 ∣ 60 := by simpa using this.trans hdvd
    omega
  have hrdvd : N.relIndex E ∣ 2 := (Subgroup.relIndex_dvd_index_of_normal N E).trans hNidx
  have hEQ : N.relIndex E * Nat.card ↥(N ⊓ E) = Nat.card E :=
    Subgroup.relIndex_mul_card (H := N) (K := E)
  by_contra hE4
  push Not at hE4
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hEp
  have hr : N.relIndex E = 2 ∧ Nat.card Q = 4 := by
    have hrle : N.relIndex E ≤ 2 := Nat.le_of_dvd (by norm_num) hrdvd
    have hrpos : 0 < N.relIndex E := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hE8 : Nat.card E ≤ 8 := by
      rw [← hEQ]
      calc N.relIndex E * Nat.card ↥(N ⊓ E) ≤ 2 * 4 := Nat.mul_le_mul hrle hQ4
        _ = 8 := rfl
    have hm' : Nat.card E = 8 := by
      rw [hm] at hE4 hE8 ⊢
      have : m = 3 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · interval_cases m <;> omega
        · have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
          omega
      subst this
      rfl
    rw [hm'] at hEQ
    have hQc : Nat.card ↥(N ⊓ E) = Nat.card Q := rfl
    interval_cases h : N.relIndex E
    · rw [hQc] at hEQ; omega
    · rw [hQc] at hEQ; omega
  obtain ⟨hr2, hQ4'⟩ := hr
  obtain ⟨t, htE, htN⟩ : ∃ t ∈ E, t ∉ N := by
    by_contra hcon
    push Not at hcon
    have : N.relIndex E = 1 := Subgroup.relIndex_eq_one.mpr fun x hx => hcon x hx
    omega
  obtain ⟨q₁, hq₁Q, hq₁⟩ : ∃ q₁ ∈ Q, q₁ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).mpr hcon
    rw [this, Subgroup.card_bot] at hQ4'
    omega
  have hq₁2 : q₁ * q₁ = 1 := by rw [← pow_two]; exact hE2 q₁ hq₁Q.2
  obtain ⟨q₂, hq₂Q, hq₂z⟩ : ∃ q₂ ∈ Q, q₂ ∉ Subgroup.zpowers q₁ := by
    by_contra hcon
    push Not at hcon
    have hle : Q ≤ Subgroup.zpowers q₁ := fun x hx => hcon x hx
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have hord : orderOf q₁ = 2 := by
      refine orderOf_eq_prime ?_ hq₁
      rw [pow_two]; exact hq₁2
    rw [hord] at h1
    omega
  have hq₂ : q₂ ≠ 1 := fun h => hq₂z (h ▸ Subgroup.one_mem _)
  have hq₂₁ : q₂ ≠ q₁ := fun h => hq₂z (h ▸ Subgroup.mem_zpowers _)
  have hq₂2 : q₂ * q₂ = 1 := by rw [← pow_two]; exact hE2 q₂ hq₂Q.2
  have hq₁₂ : q₁ * q₂ = q₂ * q₁ := hEcomm q₁ hq₁Q.2 q₂ hq₂Q.2
  let φ : MulAut (alternatingGroup (Fin 5)) := MulAut.congr e (ψ t)
  obtain ⟨σ, hσ⟩ := conjPerm_surjective (n := 5) (Or.inl rfl) φ
  have hφ : ∀ (q : K) (hq : q ∈ N), t * q = q * t →
      σ * ((e ⟨q, hq⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
        ((e ⟨q, hq⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) * σ := by
    intro q hq htq
    have h1 : ψ t ⟨q, hq⟩ = ⟨q, hq⟩ := by
      apply Subtype.ext
      rw [hψapp]
      show t * q * t⁻¹ = q
      rw [htq]; group
    have h2' : φ (e ⟨q, hq⟩) = e ⟨q, hq⟩ := by
      show (e.symm.trans ((ψ t).trans e)) (e ⟨q, hq⟩) = _
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h1]
    have h3 : ((φ (e ⟨q, hq⟩) : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
        ((e ⟨q, hq⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by rw [h2']
    rw [← hσ, conjPerm_apply] at h3
    calc σ * ((e ⟨q, hq⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5))
        = σ * ((e ⟨q, hq⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) * σ⁻¹ * σ := by group
      _ = ((e ⟨q, hq⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) * σ := by rw [h3]
  have htt : t * t = 1 := by rw [← pow_two]; exact hE2 t htE
  have hσ2 : σ * σ = 1 := by
    apply conjPerm_injective (n := 5) (by norm_num)
    rw [map_mul, hσ, map_one]
    show MulAut.congr e (ψ t) * MulAut.congr e (ψ t) = 1
    rw [← map_mul, ← map_mul, htt, map_one, map_one]
  have hσodd : Perm.sign σ ≠ 1 := by
    intro hs
    have hσA : σ ∈ alternatingGroup (Fin 5) := Perm.mem_alternatingGroup.mpr hs
    have hinn : φ ∈ OuterAutomorphisms.inner (alternatingGroup (Fin 5)) := by
      rw [← map_conjPerm_alternatingGroup 5, ← hσ]
      exact ⟨σ, hσA, rfl⟩
    rw [← OuterAutomorphisms.inner_map_congr e] at hinn
    obtain ⟨x, hx, hxφ⟩ := hinn
    have hxψ : x = ψ t := (MulAut.congr e).injective hxφ
    exact htN (hψN t (hxψ ▸ hx))
  have hq₁A : Perm.sign ((e ⟨q₁, hq₁Q.1⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = 1 :=
    Perm.mem_alternatingGroup.mp (e ⟨q₁, hq₁Q.1⟩).2
  have hq₂A : Perm.sign ((e ⟨q₂, hq₂Q.1⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = 1 :=
    Perm.mem_alternatingGroup.mp (e ⟨q₂, hq₂Q.1⟩).2
  have hne1 : ∀ (q : K) (hq : q ∈ N), q ≠ 1 →
      ((e ⟨q, hq⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) ≠ 1 := by
    intro q hq hq1 h
    apply hq1
    have h' : (e ⟨q, hq⟩ : alternatingGroup (Fin 5)) = 1 := Subtype.ext h
    have := e.injective (h'.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hsq : ∀ (q : K) (hq : q ∈ N), q * q = 1 →
      ((e ⟨q, hq⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) *
        ((e ⟨q, hq⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = 1 := by
    intro q hq hq2
    have : (e ⟨q, hq⟩ : alternatingGroup (Fin 5)) * e ⟨q, hq⟩ = 1 := by
      rw [← map_mul, ← map_one e]
      congr 1
      exact Subtype.ext hq2
    exact congrArg Subtype.val this
  have hcm : ((e ⟨q₁, hq₁Q.1⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) *
      ((e ⟨q₂, hq₂Q.1⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
        ((e ⟨q₂, hq₂Q.1⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) *
        ((e ⟨q₁, hq₁Q.1⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
    have : (e ⟨q₁, hq₁Q.1⟩ : alternatingGroup (Fin 5)) * e ⟨q₂, hq₂Q.1⟩ =
        e ⟨q₂, hq₂Q.1⟩ * e ⟨q₁, hq₁Q.1⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hq₁₂
    exact congrArg Subtype.val this
  have hdist : ((e ⟨q₂, hq₂Q.1⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) ≠
      ((e ⟨q₁, hq₁Q.1⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
    intro h
    apply hq₂₁
    have h' : (e ⟨q₂, hq₂Q.1⟩ : alternatingGroup (Fin 5)) = e ⟨q₁, hq₁Q.1⟩ := Subtype.ext h
    have := e.injective h'
    exact congrArg Subtype.val this
  exact no_odd_involution_centralizes_klein _ hq₁A (hne1 q₁ hq₁Q.1 hq₁) (hsq q₁ hq₁Q.1 hq₁2)
    _ hq₂A (hne1 q₂ hq₂Q.1 hq₂) hdist (hsq q₂ hq₂Q.1 hq₂2) hcm σ hσodd hσ2
    (hφ q₁ hq₁Q.1 (hEcomm t htE q₁ hq₁Q.2))
    (hφ q₂ hq₂Q.1 (hEcomm t htE q₂ hq₂Q.2))

end CFSG.Quasithin.RonanE43
