module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUNorm
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.QuasithinUnique.B113Lie.Sp CFSG.StandardType.GGOppRadSpU

private lemma su_exists_ne_zero_ne_one {F : Type} [Field F] [Finite F] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) : ∃ μ : F, μ ≠ 0 ∧ μ ≠ 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hcard4 : 4 ≤ Nat.card F := by
    have hf1 : 1 ≤ f := by
      by_contra h
      have hf0 : f = 0 := by omega
      rw [hf0] at hc
      norm_num at hc
      have h1 : 1 < Fintype.card F := Fintype.one_lt_card
      rw [hc] at h1
      exact absurd h1 (lt_irrefl 1)
    calc 4 = (2 ^ 1) ^ 2 := by norm_num
      _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hf1) 2
      _ = Nat.card F := hc.symm
  have hlt : ({0, 1} : Finset F).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ]
    have hpair : ({0, 1} : Finset F).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    rw [hpair, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨μ, -, hμ⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨μ, ?_, ?_⟩
  · intro h; exact hμ (by simp [h])
  · intro h; exact hμ (by simp [h])

private theorem su_eq_span_pair_of_isTotallyIsotropic_invariant {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {U : Submodule F (Fin n → F)}
    (hUiso : (suH hc n).IsTotallyIsotropic U) (hU0 : U ≠ ⊥)
    (hUinv : ∀ q ∈ Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)),
        ∀ u ∈ U, natRep (SU (unitaryInvolution F 2 f) n) q u ∈ U) :
    U = Submodule.span F {v, w} := by
  set A : Submodule F (Fin n → F) := Submodule.span F {v, w} with hA
  have hAiso : (suH hc n).IsTotallyIsotropic A := by
    rw [hA]; exact suFrame_isTotallyIsotropic hfr
  have hvA : v ∈ A := by rw [hA]; exact Submodule.subset_span (by simp)
  have hwA : w ∈ A := by rw [hA]; exact Submodule.subset_span (by simp)
  have hUA : U ≤ (suH hc n).perp A := by
    intro u hu
    rw [(suH hc n).mem_perp]
    intro a ha
    by_contra hau
    have haiso : (suH hc n).β a a = 0 := hAiso ha a ha
    obtain ⟨t, ht⟩ := exists_SU_transvection (unitaryInvolution F 2 f)
      (unitaryInvolution_involutive hc) (n := n) haiso
    have ht' : ∀ z : Fin n → F, natRep (SU (unitaryInvolution F 2 f) n) t z =
        z + (suH hc n).β a z • a := ht
    have hav : (suH hc n).β a v = 0 := (suH hc n).refl v a (hAiso ha v hvA)
    have haw : (suH hc n).β a w = 0 := (suH hc n).refl w a (hAiso ha w hwA)
    have htN : t ∈ Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) := by
      rw [mem_normalizer_suPair_iff hfr]
      left
      refine ⟨1, 1, ?_, ?_⟩
      · rw [ht', hav, zero_smul, add_zero]; simp
      · rw [ht', haw, zero_smul, add_zero]; simp
    have hmem : (suH hc n).β a u • a ∈ U := by
      have h1 := hUinv t htN u hu
      rw [ht'] at h1
      have h2 := Submodule.sub_mem U h1 hu
      rwa [add_sub_cancel_left] at h2
    have haU : a ∈ U := (Submodule.smul_mem_iff (p := U) (x := a) hau).mp hmem
    exact hau ((suH hc n).refl u a (hUiso haU u hu))
  have hUA' : U ≤ A := by
    intro u hu
    by_contra huA
    have huPerp : u ∈ (suH hc n).perp A := hUA hu
    have hx_exists : ∃ y ∈ (suH hc n).perp A, (suH hc n).β y u ≠ 0 := by
      by_contra h
      apply huA
      rw [← (suH hc n).perp_perp A]
      rw [(suH hc n).mem_perp]
      intro y hy
      by_contra hyu
      exact h ⟨y, hy, hyu⟩
    obtain ⟨y, hyPerp, hyu⟩ := hx_exists
    set lam : F := unitaryInvolution F 2 f ((suH hc n).β y u)⁻¹ with hlam
    have hlamu : (suH hc n).β (lam • y) u = 1 := by
      rw [(suH hc n).smul_left, hlam]
      change unitaryInvolution F 2 f (unitaryInvolution F 2 f ((suH hc n).β y u)⁻¹) *
        (suH hc n).β y u = 1
      rw [unitaryInvolution_involutive hc, inv_mul_cancel₀ hyu]
    set y' : Fin n → F := lam • y with hy'
    have hy'Perp : y' ∈ (suH hc n).perp A := by
      rw [hy']; exact Submodule.smul_mem _ _ hyPerp
    have hy'u : (suH hc n).β y' u = 1 := by rw [hy']; exact hlamu
    have hy'y'_fix : unitaryInvolution F 2 f ((suH hc n).β y' y') = (suH hc n).β y' y' :=
      (suForm_symm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) y' y').symm
    obtain ⟨c, hc_eq⟩ := exists_add_unitaryInvolution_eq hc hy'y'_fix
    have hc_eq' : c + (suH hc n).σ c = (suH hc n).β y' y' := hc_eq
    set x : Fin n → F := y' + c • u with hx
    have hxPerp : x ∈ (suH hc n).perp A := by
      rw [hx]
      exact Submodule.add_mem _ hy'Perp (Submodule.smul_mem _ _ huPerp)
    have hxx : (suH hc n).β x x = 0 := by
      rw [hx, ReflForm.β_add_smul_add_smul (suH hc n) y' y' u c c]
      have huy' : (suH hc n).β u y' = 1 := by
        have h : (suH hc n).β u y' = (suH hc n).σ ((suH hc n).β y' u) :=
          suForm_symm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) y' u
        rw [hy'u, map_one] at h
        exact h
      have huu : (suH hc n).β u u = 0 := hUiso hu u hu
      rw [hy'u, huy', huu]
      rw [mul_one, mul_one, mul_zero, add_zero]
      rw [add_assoc, hc_eq']
      exact CharTwo.add_self_eq_zero _
    have hxu : (suH hc n).β x u = 1 := by
      have huu : (suH hc n).β u u = 0 := hUiso hu u hu
      rw [hx, (suH hc n).add_left, hy'u, (suH hc n).smul_left, huu, mul_zero, add_zero]
    obtain ⟨t, ht⟩ := exists_SU_transvection (unitaryInvolution F 2 f)
      (unitaryInvolution_involutive hc) (n := n) hxx
    have ht' : ∀ z : Fin n → F, natRep (SU (unitaryInvolution F 2 f) n) t z =
        z + (suH hc n).β x z • x := ht
    have hxv : (suH hc n).β x v = 0 := (suH hc n).refl v x (hxPerp v hvA)
    have hxw : (suH hc n).β x w = 0 := (suH hc n).refl w x (hxPerp w hwA)
    have htN : t ∈ Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) := by
      rw [mem_normalizer_suPair_iff hfr]
      left
      refine ⟨1, 1, ?_, ?_⟩
      · rw [ht', hxv, zero_smul, add_zero]; simp
      · rw [ht', hxw, zero_smul, add_zero]; simp
    have hmem : (suH hc n).β x u • x ∈ U := by
      have h1 := hUinv t htN u hu
      rw [ht'] at h1
      have h2 := Submodule.sub_mem U h1 hu
      rwa [add_sub_cancel_left] at h2
    have hxu_ne : (suH hc n).β x u ≠ 0 := by rw [hxu]; exact one_ne_zero
    have hxU : x ∈ U := (Submodule.smul_mem_iff (p := U) (x := x) hxu_ne).mp hmem
    have h0 : (suH hc n).β x u = 0 := (suH hc n).refl u x (hUiso hxU u hu)
    rw [hxu] at h0
    exact one_ne_zero h0
  have hAU : A ≤ U := by
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have huA : u ∈ A := hUA' huU
    rw [hA, Submodule.mem_span_pair] at huA
    obtain ⟨a, b, hu_eq⟩ := huA
    obtain ⟨μ, hμ0, hμ1⟩ := su_exists_ne_zero_ne_one hc
    obtain ⟨g, hgv, hgw, -, -, -⟩ := exists_mem_SU_torus hfr (μ := μ) (ν := μ⁻¹)
      hμ0 (inv_ne_zero hμ0) (by rw [mul_inv_cancel₀ hμ0, map_one])
    have hgN : g ∈ Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) := by
      rw [mem_normalizer_suPair_iff hfr]
      exact Or.inl ⟨μ, μ⁻¹, hgv, hgw⟩
    have hμinvμ : μ⁻¹ - μ ≠ 0 := by
      intro h
      have h1 : μ⁻¹ = μ := sub_eq_zero.mp h
      have h2 : μ * μ = 1 := by
        calc μ * μ = μ * μ⁻¹ := by rw [h1]
          _ = 1 := mul_inv_cancel₀ hμ0
      exact hμ1 (eq_one_of_mul_self_eq_one h2)
    have hkey : natRep (SU (unitaryInvolution F 2 f) n) g u - μ • u =
        (b * (μ⁻¹ - μ)) • w := by
      rw [← hu_eq, map_add, map_smul, map_smul, hgv, hgw]
      module
    have hsub : natRep (SU (unitaryInvolution F 2 f) n) g u - μ • u ∈ U :=
      Submodule.sub_mem U (hUinv g hgN u huU) (Submodule.smul_mem U μ huU)
    rw [hkey] at hsub
    have hswap : v ∈ U ↔ w ∈ U := by
      constructor
      · intro hvU
        obtain ⟨s, hsv, hsw, -, -, -⟩ := exists_mem_SU_swap hfr
        have hsN : s ∈ Subgroup.normalizer
            (suPair (unitaryInvolution F 2 f) n v w :
              Set ↥(SU (unitaryInvolution F 2 f) n)) := by
          rw [mem_normalizer_suPair_iff hfr]
          exact Or.inr ⟨1, 1, by rw [hsv]; simp, by rw [hsw]; simp⟩
        have h1 := hUinv s hsN v hvU
        rwa [hsv] at h1
      · intro hwU
        obtain ⟨s, hsv, hsw, -, -, -⟩ := exists_mem_SU_swap hfr
        have hsN : s ∈ Subgroup.normalizer
            (suPair (unitaryInvolution F 2 f) n v w :
              Set ↥(SU (unitaryInvolution F 2 f) n)) := by
          rw [mem_normalizer_suPair_iff hfr]
          exact Or.inr ⟨1, 1, by rw [hsv]; simp, by rw [hsw]; simp⟩
        have h1 := hUinv s hsN w hwU
        rwa [hsw] at h1
    have hboth : v ∈ U ∧ w ∈ U := by
      by_cases hb : b = 0
      · have hua : u = a • v := by rw [← hu_eq, hb, zero_smul, add_zero]
        have ha0 : a ≠ 0 := by
          intro ha; apply hu0; rw [hua, ha, zero_smul]
        have hvU : v ∈ U := by
          have hmem : a • v ∈ U := by rw [← hua]; exact huU
          exact (Submodule.smul_mem_iff (p := U) (x := v) ha0).mp hmem
        exact ⟨hvU, hswap.mp hvU⟩
      · have hcoef : b * (μ⁻¹ - μ) ≠ 0 := mul_ne_zero hb hμinvμ
        have hwU : w ∈ U := (Submodule.smul_mem_iff (p := U) (x := w) hcoef).mp hsub
        exact ⟨hswap.mpr hwU, hwU⟩
    intro z hz
    rw [hA, Submodule.mem_span_pair] at hz
    obtain ⟨p, q, rfl⟩ := hz
    exact Submodule.add_mem U (Submodule.smul_mem U p hboth.1) (Submodule.smul_mem U q hboth.2)
  exact le_antisymm hUA' hAU

theorem pCoreOf_normalizer_suPair_le_suStabRad {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    pCoreOf 2 (Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n))) ≤
      suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr) := by
  intro g hg
  set N : Subgroup ↥(SU (unitaryInvolution F 2 f) n) :=
    Subgroup.normalizer
      (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) with hN
  set R : Subgroup ↥(SU (unitaryInvolution F 2 f) n) := pCoreOf 2 N with hR
  by_cases hR0 : R = ⊥
  · rw [hR0] at hg
    have hg1 : g = 1 := Subgroup.mem_bot.mp hg
    rw [hg1]
    unfold suStabRad
    rw [mem_rad]
    exact ⟨fun w _ => by simp, fun v _ => by simp⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hR2 : IsPGroup 2 R := GGRootNorm.isPGroup_pCoreOf N
    have hnorm : N ≤ Subgroup.normalizer (R : Set ↥(SU (unitaryInvolution F 2 f) n)) :=
      GGRootNorm.le_normalizer_pCoreOf N
    have hU1 : isoSeq (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) R 1 ≠ ⊥ :=
      isoSeq_one_ne_bot (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) 2
        (isIsometric_natRep_SU (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) n)
        (natRep_injective (SU (unitaryInvolution F 2 f) n)) R hR2 hR0
    have hU1inv : ∀ q ∈ N,
        ∀ u ∈ isoSeq (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) R 1,
        natRep (SU (unitaryInvolution F 2 f) n) q u ∈
          isoSeq (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) R 1 :=
      fun q hq u hu => apply_mem_isoSeq (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n))
        (isIsometric_natRep_SU (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) n)
        R 1 (hnorm hq) hu
    rw [hN] at hU1inv
    have hU1eq : isoSeq (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) R 1 =
        Submodule.span F {v, w} :=
      su_eq_span_pair_of_isTotallyIsotropic_invariant hfr
        (U := isoSeq (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) R 1)
        (isoSeq_isTotallyIsotropic (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) R 1)
        hU1 hU1inv
    have hvne : v ≠ 0 := by
      intro h0
      have h1 : (suH hc n).β v w' = 1 := hfr.1
      rw [h0, (suH hc n).β_zero_left] at h1
      exact zero_ne_one h1
    haveI : Nontrivial (Fin n → F) := ⟨⟨v, 0, hvne⟩⟩
    have hd1 : 1 ≤ Module.finrank F (Fin n → F) := Module.finrank_pos
    set W : Submodule F (Fin n → F) :=
      isoSeq (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) R
        (Module.finrank F (Fin n → F)) with hWdef
    have hU1leW : isoSeq (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) R 1 ≤ W := by
      rw [hWdef]
      exact isoSeq_mono (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) R hd1
    have hW0 : W ≠ ⊥ := by
      intro hbot
      apply hU1
      rw [hbot] at hU1leW
      exact le_bot_iff.mp hU1leW
    have hWinv : ∀ q ∈ N, ∀ u ∈ W,
        natRep (SU (unitaryInvolution F 2 f) n) q u ∈ W := by
      intro q hq u hu
      rw [hWdef] at hu ⊢
      exact apply_mem_isoSeq (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n))
        (isIsometric_natRep_SU (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) n)
        R _ (hnorm hq) hu
    rw [hN] at hWinv
    have hWiso : (suH hc n).IsTotallyIsotropic W := by
      rw [hWdef]
      exact isoSeq_isTotallyIsotropic (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) R _
    have hWeq : W = Submodule.span F {v, w} :=
      su_eq_span_pair_of_isTotallyIsotropic_invariant hfr (U := W) hWiso hW0 hWinv
    unfold suStabRad
    rw [mem_rad]
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · have hw1 : w ∈ isoSeq (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) R 1 := by
        rw [← hU1eq] at hw
        exact hw
      have h1 := isoSeq_triv (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) R 0 hg hw1
      rw [isoSeq_zero, Submodule.mem_bot] at h1
      exact sub_eq_zero.mp h1
    · have hv' : v ∈ (suH hc n).perp W := by
        rw [hWeq]
        exact hv
      have h1 := isoSeq_middle_triv (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) 2
        (isIsometric_natRep_SU (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) n)
        R hR2 hg hv'
      rw [← hWdef, hWeq] at h1
      exact h1

end CFSG.StandardType.LieKnownR2.Short
