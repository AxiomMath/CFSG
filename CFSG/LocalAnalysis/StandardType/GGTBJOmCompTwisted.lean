module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmAutomizer
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBFrameChange

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth TypeBDatum TypeDDatum
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

private lemma tbjT_conj_diagAut_permAut_apply {s : Fin r → ZMod p} (hs : ∀ i, s i * s i = 1)
    (σ : Equiv.Perm (Fin r)) (f : Fin r → Multiplicative (ZMod p)) (j : Fin r) :
    (MulAut.conj (diagAut s hs) (permAut (p := p) σ)) f j =
      ofAdd (s j * (s (σ⁻¹ j) * toAdd (f (σ⁻¹ j)))) := by
  simp only [MulAut.conj_apply, tbjA_diagAut_inv, MulAut.mul_apply, permAut_apply,
    Function.comp_apply, diagAut_apply, toAdd_ofAdd]

private lemma tbjT_conj_diagAut_swap_apply_eq {s : Fin r → ZMod p} (hs : ∀ i, s i * s i = 1)
    {i k : Fin r} (hik : i ≠ k) (hc : s i * s k = 1) (f : Fin r → Multiplicative (ZMod p)) :
    MulAut.conj (diagAut s hs) (permAut (p := p) (Equiv.swap i k)) f =
      permAut (p := p) (Equiv.swap i k) f := by
  funext l
  rw [tbjT_conj_diagAut_permAut_apply hs (Equiv.swap i k) f l, permAut_apply,
    Function.comp_apply, Equiv.swap_inv]
  by_cases hli : l = i
  · rw [hli]
    rw [Equiv.swap_apply_left, show s i * (s k * toAdd (f k)) = toAdd (f k) from by
      rw [← mul_assoc, hc, one_mul], ofAdd_toAdd]
  · by_cases hlk : l = k
    · rw [hlk]
      rw [Equiv.swap_apply_right, show s k * (s i * toAdd (f i)) = toAdd (f i) from by
        rw [← mul_assoc, mul_comm (s k) (s i), hc, one_mul], ofAdd_toAdd]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlk,
        show s l * (s l * toAdd (f l)) = toAdd (f l) from by
          rw [← mul_assoc, hs l, one_mul], ofAdd_toAdd]

private lemma tbjT_dinv_apply_self {i k : Fin r} (hik : i ≠ k)
    (f : Fin r → Multiplicative (ZMod p)) : dinv i k f i = (f i)⁻¹ := by
  rw [dinv, Function.update_self, Function.update_of_ne hik]

private lemma tbjT_dinv_apply_other {i k : Fin r} (hik : i ≠ k)
    (f : Fin r → Multiplicative (ZMod p)) : dinv i k f k = (f k)⁻¹ := by
  rw [dinv, Function.update_of_ne (Ne.symm hik), Function.update_self]

private lemma tbjT_dinv_apply_of_ne {i k j : Fin r} (hji : j ≠ i) (hjk : j ≠ k)
    (f : Fin r → Multiplicative (ZMod p)) : dinv i k f j = f j := by
  rw [dinv, Function.update_of_ne hji, Function.update_of_ne hjk]

private lemma tbjT_conj_diagAut_swap_apply_dinv {s : Fin r → ZMod p}
    (hs : ∀ i, s i * s i = 1) {i k : Fin r} (hik : i ≠ k) (hc : s i * s k = -1)
    (f : Fin r → Multiplicative (ZMod p)) :
    MulAut.conj (diagAut s hs) (permAut (p := p) (Equiv.swap i k)) f =
      permAut (p := p) (Equiv.swap i k) (dinv i k f) := by
  funext l
  rw [tbjT_conj_diagAut_permAut_apply hs (Equiv.swap i k) f l, permAut_apply,
    Function.comp_apply, Equiv.swap_inv]
  by_cases hli : l = i
  · rw [hli]
    rw [Equiv.swap_apply_left, show s i * (s k * toAdd (f k)) = -toAdd (f k) from by
      rw [← mul_assoc, hc, neg_one_mul], tbjT_dinv_apply_other hik f, ofAdd_neg, ofAdd_toAdd]
  · by_cases hlk : l = k
    · rw [hlk]
      rw [Equiv.swap_apply_right, show s k * (s i * toAdd (f i)) = -toAdd (f i) from by
        rw [← mul_assoc, mul_comm (s k) (s i), hc, neg_one_mul], tbjT_dinv_apply_self hik f,
        ofAdd_neg, ofAdd_toAdd]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlk,
        show s l * (s l * toAdd (f l)) = toAdd (f l) from by
          rw [← mul_assoc, hs l, one_mul], tbjT_dinv_apply_of_ne hli hlk f, ofAdd_toAdd]

theorem TBJOmData.torusAut_twisted_of_blockData [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q)
    {f₀ : Fin r → Multiplicative (ZMod p)} {J : Subgroup ↥(orthDerived Q)}
    (hJc : J ≤ Subgroup.centralizer ({Δ.τΩ hA f₀} : Set ↥(orthDerived Q)))
    {a : ZMod p} (ha : a ≠ 0) {P : Fin r → Prop}
    (hP : ∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a)
    (hswap : ∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
      ∃ n ∈ J, ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (permAut (Equiv.swap i k) f))
    (hmixed : ∀ i k : Fin r, P i → P k → toAdd (f₀ i) = a → toAdd (f₀ k) = -a →
      ∃ n ∈ J, ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (permAut (Equiv.swap i k) (dinv i k f)))
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f} ≤ p ^ r) :
    ∃ (S : Finset (Fin r)) (s : Fin r → ZMod p) (hs : ∀ i, s i * s i = 1), 3 ≤ S.card ∧
      Δ.torusAut hA J = twistedPermAut r p S s hs ∧
      ∀ f : Fin r → Multiplicative (ZMod p), (∀ σ ∈ Δ.torusAut hA J, σ f = f) →
        ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f := by
  classical
  set S : Finset (Fin r) := Finset.univ.filter P with hSdef
  set s : Fin r → ZMod p := (fun i => if P i then toAdd (f₀ i) / a else 1) with hsdef
  have hmemS : ∀ i, i ∈ S ↔ P i := by
    intro i
    rw [hSdef]
    simp
  have hs : ∀ i, s i * s i = 1 := by
    intro i
    simp only [hsdef]
    by_cases hi : P i
    · rw [if_pos hi]
      rcases hP i hi with h | h <;> rw [h]
      · rw [div_self ha, one_mul]
      · rw [neg_div, div_self ha]
        ring
    · rw [if_neg hi, one_mul]
  have hf₀ : ∀ i ∈ S, toAdd (f₀ i) = a * s i := by
    intro i hi
    have hiP : P i := (hmemS i).mp hi
    simp only [hsdef]
    rw [if_pos hiP, ← mul_div_assoc, mul_div_cancel_left₀ _ ha]
  have h3 : 3 ≤ S.card := by
    have h := tbjA_three_le_card_class_of_ne_zero (Fact.out : p.Prime) (Δ.τΩ hA) f₀ J a P ha
      hP hcent hcount
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hSdef] at h
  have hub : Δ.torusAut hA J ≤ twistedPermAut r p S s hs := by
    rintro σ ⟨n, hnJ, hnσ⟩
    obtain ⟨π, ε, hε, hu⟩ := tbjA_isSignedPerm_of_induced Δ hA ⟨n, hnJ, hnσ⟩
    have hfix₀ : σ f₀ = f₀ := by
      apply tbjA_tauOmega_injective Δ hA
      have hcomm := (Subgroup.mem_centralizer_iff.mp (hJc hnJ)) (Δ.τΩ hA f₀)
        (Set.mem_singleton (Δ.τΩ hA f₀))
      rw [← hnσ f₀, ← hcomm]
      group
    have hfix : ∀ i, toAdd (f₀ (π i)) = ε i * toAdd (f₀ i) := fun i => by
      have h := hu f₀ i
      rwa [hfix₀] at h
    have hnotS : ∀ i ∉ S, π i = i ∧ ε i = 1 := by
      intro i hi
      have hiP : ¬ P i := fun h => hi ((hmemS i).mpr h)
      let f : Fin r → Multiplicative (ZMod p) := Pi.mulSingle i (ofAdd (1 : ZMod p))
      have hf_def : f = Pi.mulSingle i (ofAdd (1 : ZMod p)) := rfl
      have hfP : ∀ j, P j → toAdd (f j) = 0 * toAdd (f₀ j) := by
        intro j hj
        have hji : j ≠ i := fun h => hiP (h ▸ hj)
        rw [hf_def, Pi.mulSingle_eq_of_ne hji, toAdd_one, zero_mul]
      have hσf : σ f = f := by
        apply tbjA_tauOmega_injective Δ hA
        have hcomm := hcent f ⟨0, hfP⟩ n hnJ
        rw [← hnσ f, ← hcomm]
        group
      have hval : (if π i = i then (1 : ZMod p) else 0) = ε i := by
        have h := hu f i
        rw [hσf, hf_def] at h
        rw [toAdd_mulSingle i (π i) 1, toAdd_mulSingle i i 1] at h
        simpa using h
      have hpi : π i = i := by
        by_contra hne
        rw [if_neg hne] at hval
        exact (coord_sign_ne_zero (Fact.out : p.Prime) (hε i)) hval.symm
      refine ⟨hpi, ?_⟩
      rw [hpi, if_pos rfl] at hval
      exact hval.symm
    exact tbjA_mem_twistedPermAut_of S s hs hε (fun i hi => (hnotS i hi).1)
      (fun i hi => (hnotS i hi).2) hu ha hf₀ hfix
  have hlb : twistedPermAut r p S s hs ≤ Δ.torusAut hA J := by
    rw [twistedPermAut, Subgroup.map_le_iff_le_comap, permSupportedAut, Subgroup.closure_le]
    rintro u ⟨i, hiS, k, hkS, hik, rfl⟩
    change MulAut.conj (diagAut s hs) (permAut (p := p) (Equiv.swap i k)) ∈ Δ.torusAut hA J
    have hPi : P i := (hmemS i).mp hiS
    have hPk : P k := (hmemS k).mp hkS
    have hf0i : toAdd (f₀ i) = a * s i := hf₀ i hiS
    have hf0k : toAdd (f₀ k) = a * s k := hf₀ k hkS
    by_cases hss : s i = s k
    · have hc : s i * s k = 1 := by rw [hss, hs k]
      have hconj : MulAut.conj (diagAut s hs) (permAut (p := p) (Equiv.swap i k)) =
          permAut (p := p) (Equiv.swap i k) :=
        MulEquiv.ext fun f => tbjT_conj_diagAut_swap_apply_eq hs hik hc f
      obtain ⟨n, hnJ, hn⟩ := hswap i k hik hPi hPk (by rw [hf0i, hf0k, hss])
      exact ⟨n, hnJ, fun f => by rw [hconj]; exact hn f⟩
    · have hsik : s i * s k = -1 := by
        have hsq : (s i * s k) * (s i * s k) = 1 := by
          rw [show (s i * s k) * (s i * s k) = (s i * s i) * (s k * s k) by ring,
            hs i, hs k, one_mul]
        rcases sign_of_sq_one hsq with h | h
        · exfalso
          apply hss
          calc s i = s i * 1 := (mul_one _).symm
            _ = s i * (s k * s k) := by rw [hs k]
            _ = (s i * s k) * s k := by ring
            _ = 1 * s k := by rw [h]
            _ = s k := one_mul _
        · exact h
      rcases sign_of_sq_one (hs i) with hsi | hsi
      · have hsk : s k = -1 := by
          have h := hsik
          rw [hsi, one_mul] at h
          exact h
        have hia : toAdd (f₀ i) = a := by rw [hf0i, hsi, mul_one]
        have hka : toAdd (f₀ k) = -a := by rw [hf0k, hsk, mul_neg, mul_one]
        have hconj : ∀ f, MulAut.conj (diagAut s hs) (permAut (p := p) (Equiv.swap i k)) f =
            permAut (p := p) (Equiv.swap i k) (dinv i k f) :=
          fun f => tbjT_conj_diagAut_swap_apply_dinv hs hik hsik f
        obtain ⟨n, hnJ, hn⟩ := hmixed i k hPi hPk hia hka
        exact ⟨n, hnJ, fun f => by rw [hconj f]; exact hn f⟩
      · have hsk : s k = 1 := by
          have h := hsik
          rw [hsi, neg_one_mul] at h
          exact neg_injective h
        have hia : toAdd (f₀ i) = -a := by rw [hf0i, hsi, mul_neg, mul_one]
        have hka : toAdd (f₀ k) = a := by rw [hf0k, hsk, mul_one]
        have hc' : s k * s i = -1 := by rw [mul_comm, hsik]
        have hconj' : ∀ f,
            MulAut.conj (diagAut s hs) (permAut (p := p) (Equiv.swap k i)) f =
              permAut (p := p) (Equiv.swap k i) (dinv k i f) :=
          fun f => tbjT_conj_diagAut_swap_apply_dinv hs (Ne.symm hik) hc' f
        obtain ⟨n, hnJ, hn⟩ := hmixed k i hPk hPi hka hia
        have hmem' : MulAut.conj (diagAut s hs) (permAut (p := p) (Equiv.swap k i)) ∈
            Δ.torusAut hA J := ⟨n, hnJ, fun f => by rw [hconj' f]; exact hn f⟩
        rwa [Equiv.swap_comm k i] at hmem'
  have hEq : Δ.torusAut hA J = twistedPermAut r p S s hs := le_antisymm hub hlb
  refine ⟨S, s, hs, h3, hEq, ?_⟩
  intro f hf j hj
  have hf' : ∀ σ ∈ twistedPermAut r p S s hs, σ f = f := by
    intro σ hσ
    rw [← hEq] at hσ
    exact hf σ hσ
  obtain ⟨m, hm⟩ := tbjA_fixed_of_mem_twistedPermAut (S := S) s hs hf'
  refine hcent f ⟨m / a, fun i hi => ?_⟩ j hj
  have hiS : i ∈ S := (hmemS i).mpr hi
  have h1 : toAdd (f i) = m * s i := hm i hiS
  have h2 : toAdd (f₀ i) = a * s i := hf₀ i hiS
  have hcalc : (m / a) * (a * s i) = m * s i := by
    rw [← mul_assoc, div_mul_cancel₀ m ha]
  rw [h1, h2]
  exact hcalc.symm

end OrthTorus

end CFSG.StandardType

end
