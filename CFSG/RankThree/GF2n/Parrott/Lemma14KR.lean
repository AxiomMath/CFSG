module

public import CFSG.RankThree.GF2n.Parrott.Lemma14KBasic
public import CFSG.RankThree.GF2n.Parrott.MemJOfIndexTwo
public import CFSG.RankThree.GF2n.Parrott.QA45InvolutionClasses
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Module.ZMod
import all CFSG.RankThree.GF2n.Parrott.Section2Products

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open Module

section F2

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

theorem exists_mem_bilin_ne_zero_of_semilinear_involution (N : Submodule (ZMod 2) M)
    (hN : finrank (ZMod 2) N ≤ 4)
    (B : LinearMap.BilinForm (ZMod 2) M) (hBsymm : ∀ a ∈ N, ∀ b ∈ N, B a b = B b a)
    (hBnd : ∀ a ∈ N, (∀ b ∈ N, B a b = 0) → a = 0)
    (s t u : M →ₗ[ZMod 2] M) (hsinj : Function.Injective s)
    (hsN : ∀ a ∈ N, s a ∈ N) (htN : ∀ a ∈ N, t a ∈ N) (huN : ∀ a ∈ N, u a ∈ N)
    (hs3 : ∀ a ∈ N, a + s a + s (s a) = 0)
    (hBs : ∀ a ∈ N, ∀ b ∈ N, B (s a) (s b) = B a b)
    (hBu : ∀ a ∈ N, ∀ b ∈ N, B (u a) (u b) = B a b)
    (htt : ∀ a ∈ N, t (t a) = a) (huu : ∀ a ∈ N, u (u a) = a)
    (htu : ∀ a ∈ N, t (u a) = u (t a)) (hts : ∀ a ∈ N, t (s a) = s (t a))
    (hus : ∀ a ∈ N, u (s a) = s (s (u a)))
    (hq : ∀ a ∈ N, u a = a → B a (s a) = 0)
    (ht : ∃ a ∈ N, t a ≠ a) :
    ∃ a ∈ N, B a (t (u a)) ≠ 0 := by
  classical
  have h2 : ∀ x : M, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hZ : ∀ c : ZMod 2, c + c = 0 := by decide
  have heq_of_add : ∀ x y : M, x + y = 0 → x = y := fun x y hxy => by
    have : x + y = y + y := by rw [hxy, h2]
    exact add_right_cancel this
  have hss : ∀ a ∈ N, s (s a) = a + s a := fun a ha => by
    apply heq_of_add
    rw [add_comm]
    exact hs3 a ha
  have hsss : ∀ a ∈ N, s (s (s a)) = a := fun a ha => by
    rw [hss (s a) (hsN a ha), hss a ha, add_left_comm, h2, add_zero]
  let U : Submodule (ZMod 2) M := N ⊓ LinearMap.eqLocus u LinearMap.id
  have hmemU : ∀ {a : M}, a ∈ U ↔ a ∈ N ∧ u a = a := fun {a} => by
    simp [U, LinearMap.mem_eqLocus]
  have hUN : U ≤ N := inf_le_left
  have hdec : ∀ v ∈ N, ∃ p ∈ U, ∃ q ∈ U, v = p + s q := by
    intro v hv
    have huv : u v ∈ N := huN v hv
    have hq' : v + u v ∈ U := by
      refine hmemU.mpr ⟨N.add_mem hv huv, ?_⟩
      rw [map_add, huu v hv, add_comm]
    refine ⟨v + s (v + u v), hmemU.mpr ⟨N.add_mem hv (hsN _ (hUN hq')), ?_⟩, v + u v, hq', ?_⟩
    · rw [map_add, map_add, map_add, hus v hv, hus (u v) huv, huu v hv,
        hss (u v) huv, hss v hv]
      have e1 := h2 (u v)
      calc u v + (u v + s (u v) + (v + s v))
          = (u v + u v) + v + (s v + s (u v)) := by abel
        _ = v + (s v + s (u v)) := by rw [e1, zero_add]
    · rw [add_assoc, h2, add_zero]
  have hiso : ∀ p ∈ U, ∀ p' ∈ U, B p p' = 0 := by
    intro p hp p' hp'
    obtain ⟨hpN, hup⟩ := hmemU.mp hp
    obtain ⟨hp'N, hup'⟩ := hmemU.mp hp'
    have hsp : s p ∈ N := hsN p hpN
    have hp_eq : p = s p + u (s p) := by
      rw [hus p hpN, hup, hss p hpN, add_left_comm, h2, add_zero]
    have : B (u (s p)) p' = B (s p) p' := by
      conv_lhs => rw [← hup']
      exact hBu (s p) hsp p' hp'N
    rw [hp_eq, map_add, LinearMap.add_apply, this, hZ]
  have hdisj : ∀ p ∈ U, ∀ q ∈ U, p = s q → q = 0 := by
    intro p hp q hq p_eq
    obtain ⟨-, hup⟩ := hmemU.mp hp
    obtain ⟨hqN, huq⟩ := hmemU.mp hq
    have h1 : u (s q) = q + s q := by rw [hus q hqN, huq, hss q hqN]
    rw [p_eq, h1] at hup
    have : (0 : M) + s q = q + s q := by rw [zero_add, hup]
    exact (add_right_cancel this).symm
  have hdimU : finrank (ZMod 2) U ≤ 2 := by
    let sU : Submodule (ZMod 2) M := U.map s
    have hinf : U ⊓ sU = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxU, y, hyU, rfl⟩ := hx
      rw [hdisj (s y) hxU y hyU rfl, map_zero]
      exact Submodule.zero_mem _
    have hsup : U ⊔ sU ≤ N := by
      refine sup_le hUN ?_
      rintro x ⟨y, hyU, rfl⟩
      exact hsN y (hUN hyU)
    have hsU : finrank (ZMod 2) sU = finrank (ZMod 2) U :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective s hsinj U)).symm
    have hkey := Submodule.finrank_sup_add_finrank_inf_eq U sU
    rw [hinf, finrank_bot, add_zero, hsU] at hkey
    have hle := Submodule.finrank_mono hsup
    omega
  obtain ⟨a₀, ha₀N, ha₀⟩ := ht
  have hexU : ∃ a ∈ U, t a ≠ a := by
    obtain ⟨p, hp, q, hq, rfl⟩ := hdec a₀ ha₀N
    by_contra hcon
    push Not at hcon
    apply ha₀
    rw [map_add, hts q (hUN hq), hcon p hp, hcon q hq]
  obtain ⟨a, haU, hta⟩ := hexU
  obtain ⟨haN, hua⟩ := hmemU.mp haU
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hta (map_zero t)
  obtain ⟨b, hb_def⟩ : ∃ b, b = a + t a := ⟨_, rfl⟩
  have hbU : b ∈ U := by
    refine hmemU.mpr ⟨hb_def ▸ N.add_mem haN (htN a haN), ?_⟩
    rw [hb_def, map_add, hua, ← htu a haN, hua]
  have hbN : b ∈ N := hUN hbU
  have hb0 : b ≠ 0 := by
    intro hb
    exact hta (heq_of_add _ _ (by rw [add_comm, ← hb_def]; exact hb))
  have hab : a ≠ b := by
    intro hab
    have h0 : t a = 0 := by
      have : a + 0 = a + t a := by rw [add_zero, ← hb_def]; exact hab
      exact (add_left_cancel this).symm
    apply ha0
    rw [← htt a haN, h0, map_zero]
  have hsa : B (s a) a = 0 := by
    rw [hBsymm _ (hsN a haN) a haN]
    exact hq a haN hua
  have hsb : B (s b) b = 0 := by
    rw [hBsymm _ (hsN b hbN) b hbN]
    exact hq b hbN (hmemU.mp hbU).2
  have hkey : B (s a) (t a) ≠ 0 := by
    intro h0
    have hsab : B (s a) b = 0 := by
      rw [hb_def, map_add, hsa, h0, add_zero]
    have hli : LinearIndependent (ZMod 2) ![a, b] := by
      rw [LinearIndependent.pair_iff' ha0]
      intro c
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · rw [zero_smul]
        exact hb0.symm
      · rw [one_smul]
        exact hab
    have hspan_le : Submodule.span (ZMod 2) {a, b} ≤ U := by
      rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact haU
      · exact hbU
    have hspan_dim : finrank (ZMod 2) (Submodule.span (ZMod 2) ({a, b} : Set M)) = 2 := by
      have := finrank_span_eq_card hli
      rw [Matrix.range_cons_cons_empty] at this
      simpa using this
    have hspan : Submodule.span (ZMod 2) {a, b} = U :=
      Submodule.eq_of_le_of_finrank_le hspan_le (by rw [hspan_dim]; exact hdimU)
    have hsq : ∀ q ∈ U, B (s q) b = 0 := by
      intro q hq
      rw [← hspan, Submodule.mem_span_pair] at hq
      obtain ⟨c₁, c₂, rfl⟩ := hq
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hsab, hsb,
        smul_zero, add_zero]
    have hperp : ∀ v ∈ N, B b v = 0 := by
      intro v hv
      rw [hBsymm b hbN v hv]
      obtain ⟨p, hp, q, hq, rfl⟩ := hdec v hv
      rw [map_add, LinearMap.add_apply, hiso p hp b hbU, hsq q hq, add_zero]
    exact hb0 (hBnd b hbN hperp)
  refine ⟨s (s a), hsN _ (hsN a haN), ?_⟩
  have hu2 : u (s (s a)) = s a := by
    rw [hus (s a) (hsN a haN), hus a haN, hua, hsss (s a) (hsN a haN)]
  rw [hu2, hts a haN, hBs (s a) (hsN a haN) (t a) (htN a haN)]
  exact hkey

theorem exists_mem_polar_ne_zero_of_semilinear_involution {V : Type*} [Group V] [Finite V]
    (hVc : ∀ a b : V, a * b = b * a) (hV2 : ∀ a : V, a * a = 1)
    (N : Subgroup V) (hN : Nat.card N ≤ 16)
    (B : V → V → ZMod 2) (hBl : ∀ a b c, B (a * b) c = B a c + B b c)
    (hBr : ∀ a b c, B a (b * c) = B a b + B a c)
    (hBsymm : ∀ a ∈ N, ∀ b ∈ N, B a b = B b a)
    (hBnd : ∀ a ∈ N, (∀ b ∈ N, B a b = 0) → a = 1)
    (s t u : MulAut V)
    (hsN : ∀ a ∈ N, s a ∈ N) (htN : ∀ a ∈ N, t a ∈ N) (huN : ∀ a ∈ N, u a ∈ N)
    (hs3 : ∀ a ∈ N, a * s a * s (s a) = 1)
    (hBs : ∀ a ∈ N, ∀ b ∈ N, B (s a) (s b) = B a b)
    (hBu : ∀ a ∈ N, ∀ b ∈ N, B (u a) (u b) = B a b)
    (htt : ∀ a ∈ N, t (t a) = a) (huu : ∀ a ∈ N, u (u a) = a)
    (htu : ∀ a ∈ N, t (u a) = u (t a)) (hts : ∀ a ∈ N, t (s a) = s (t a))
    (hus : ∀ a ∈ N, u (s a) = s (s (u a)))
    (hq : ∀ a ∈ N, u a = a → B a (s a) = 0)
    (ht : ∃ a ∈ N, t a ≠ a) :
    ∃ a ∈ N, B a (t (u a)) ≠ 0 := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hVc }
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    exact hV2 (Additive.toMul x)
  let N' : Submodule (ZMod 2) (Additive V) := AddSubgroup.toZModSubmodule 2 N.toAddSubgroup
  have hmem : ∀ {a : Additive V}, a ∈ N' ↔ Additive.toMul a ∈ N := fun {a} => Iff.rfl
  have hN' : finrank (ZMod 2) N' ≤ 4 := by
    have hc : Nat.card N' = Nat.card N :=
      Nat.card_congr
        { toFun := fun a => ⟨Additive.toMul a.1, hmem.mp a.2⟩
          invFun := fun a => ⟨Additive.ofMul a.1, hmem.mpr a.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := N')
    rw [hc, Nat.card_zmod] at hpow
    by_contra hlt
    have h5 : 2 ^ 5 ≤ 2 ^ finrank (ZMod 2) N' := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hB0 : ∀ c, B 1 c = 0 := fun c => by
    have := hBl 1 1 c
    rw [one_mul] at this
    have h' : B 1 c + B 1 c = B 1 c + 0 := by rw [← this, add_zero]
    exact add_left_cancel h'
  have hB0' : ∀ c, B c 1 = 0 := fun c => by
    have := hBr c 1 1
    rw [one_mul] at this
    have h' : B c 1 + B c 1 = B c 1 + 0 := by rw [← this, add_zero]
    exact add_left_cancel h'
  have hsmul : ∀ (k : ZMod 2) (a : Additive V),
      Additive.toMul (k • a) = Additive.toMul a ^ k.val := fun k a => by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) k with rfl | rfl
    · rw [zero_smul, ZMod.val_zero, pow_zero]
      rfl
    · rw [one_smul, ZMod.val_one, pow_one]
  have hBk : ∀ (k : ZMod 2) (a c : V), B (a ^ k.val) c = k * B a c := fun k a c => by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) k with rfl | rfl
    · rw [ZMod.val_zero, pow_zero, hB0, zero_mul]
    · rw [ZMod.val_one, pow_one, one_mul]
  have hBk' : ∀ (k : ZMod 2) (a c : V), B a (c ^ k.val) = k * B a c := fun k a c => by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) k with rfl | rfl
    · rw [ZMod.val_zero, pow_zero, hB0', zero_mul]
    · rw [ZMod.val_one, pow_one, one_mul]
  let B' : LinearMap.BilinForm (ZMod 2) (Additive V) :=
    LinearMap.mk₂ (ZMod 2) (fun a b => B (Additive.toMul a) (Additive.toMul b))
      (fun a₁ a₂ b => hBl _ _ _) (fun k a b => by rw [hsmul, hBk]; rfl)
      (fun a b₁ b₂ => hBr _ _ _) (fun k a b => by rw [hsmul, hBk']; rfl)
  let lin : MulAut V → Additive V →ₗ[ZMod 2] Additive V := fun g =>
    AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive g.toMonoidHom)
  have hlin : ∀ (g : MulAut V) (a : Additive V),
      lin g a = Additive.ofMul (g (Additive.toMul a)) := fun _ _ => rfl
  have hsinj : Function.Injective (lin s) := fun a b hab => by
    rw [hlin, hlin] at hab
    exact Additive.toMul.injective (s.injective (Additive.ofMul.injective hab))
  obtain ⟨a, ha, hne⟩ := exists_mem_bilin_ne_zero_of_semilinear_involution N' hN' B'
    (fun a ha b hb => hBsymm _ ha _ hb)
    (fun a ha hperp => Additive.toMul.injective
      (hBnd _ ha fun b hb => hperp (Additive.ofMul b) hb))
    (lin s) (lin t) (lin u) hsinj
    (fun a ha => hsN _ ha) (fun a ha => htN _ ha) (fun a ha => huN _ ha)
    (fun a ha => Additive.toMul.injective (hs3 _ ha))
    (fun a ha b hb => hBs _ ha _ hb) (fun a ha b hb => hBu _ ha _ hb)
    (fun a ha => Additive.toMul.injective (htt _ ha))
    (fun a ha => Additive.toMul.injective (huu _ ha))
    (fun a ha => Additive.toMul.injective (htu _ ha))
    (fun a ha => Additive.toMul.injective (hts _ ha))
    (fun a ha => Additive.toMul.injective (hus _ ha))
    (fun a ha hua => hq _ ha (Additive.ofMul.injective hua))
    (by
      obtain ⟨a, ha, hta⟩ := ht
      exact ⟨Additive.ofMul a, ha, fun h' => hta (Additive.ofMul.injective h')⟩)
  exact ⟨Additive.toMul a, ha, hne⟩

end F2

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem conjV_apply_three {g : ↥(H z)} (h : Tim79a.ParrottHyp z) (hg : g ^ 3 = 1)
    (v : QuotientV.V z) : conjV h g (conjV h g (conjV h g v)) = v := by
  have hh := congrArg (fun φ : MulAut (QuotientV.V z) => φ v)
    (show conjV h g ^ 3 = 1 by rw [← map_pow, hg, map_one])
  simpa [pow_succ, MulAut.mul_apply] using hh

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

private theorem sigma1Commutator_eq_commutator :
    sigma1Commutator (z := z) D =
      ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := rfl

private theorem pow_three_sigma1Nine : sigma1Nine (z := z) D ^ 3 = 1 := by
  rw [← sigma1Nine_order (z := z) D]
  exact pow_orderOf_eq_one _

private theorem commute_sigma_tau {σ₂ : ↥(H z)} (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    Commute (sigma1Nine (z := z) D * σ₂⁻¹) (sigma1Nine (z := z) D * σ₂) := by
  have h1 : Commute (sigma1Nine (z := z) D) (sigma1Nine (z := z) D * σ₂) :=
    (Commute.refl _).mul_right hcomm
  have h2 : Commute σ₂⁻¹ (sigma1Nine (z := z) D * σ₂) :=
    (hcomm.symm.mul_right (Commute.refl σ₂)).inv_left
  exact h1.mul_left h2

private theorem pow_three_sigma {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    (sigma1Nine (z := z) D * σ₂⁻¹) ^ 3 = 1 := by
  have h3 : σ₂ ^ 3 = 1 := by
    rw [← hσ₂]
    exact pow_orderOf_eq_one σ₂
  rw [(hcomm.inv_right).mul_pow, pow_three_sigma1Nine D, inv_pow, h3, inv_one, one_mul]

private theorem conjV_tH_commute_sigma (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    Commute (conjV h (tH D)) (conjV h (sigma1Nine (z := z) D * σ₂⁻¹)) := by
  have h1 : Commute (conjV h (tH D)) (conjV h (sigma1Nine (z := z) D)) :=
    conjV_tH_commute_sigma1Nine D h
  have h2 : Commute (conjV h (tH D)) (conjV h σ₂) := conjV_tH_commute_sigma2 D h hq₂
  rw [map_mul, map_inv]
  exact h1.mul_right h2.inv_right

private theorem conjV_tH_commute_tau (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    Commute (conjV h (tH D)) (conjV h (sigma1Nine (z := z) D * σ₂)) := by
  have h1 : Commute (conjV h (tH D)) (conjV h (sigma1Nine (z := z) D)) :=
    conjV_tH_commute_sigma1Nine D h
  have h2 : Commute (conjV h (tH D)) (conjV h σ₂) := conjV_tH_commute_sigma2 D h hq₂
  rw [map_mul]
  exact h1.mul_right h2

private theorem conjV_uH_commute_tau (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    Commute (conjV h (uH D)) (conjV h (sigma1Nine (z := z) D * σ₂)) := by
  set A := conjV h (sigma1Nine (z := z) D)
  set C := conjV h σ₂
  set U := conjV h (uH D)
  have hUA : U * A * U⁻¹ = C := conjV_uH_conj_sigma1Nine D h hq₂
  have hUC : U * C * U⁻¹ = A := conjV_uH_conj_sigma2 D h hq₂
  have hAC : A * C = C * A := by
    rw [← map_mul, ← map_mul, hcomm.eq]
  show U * conjV h (sigma1Nine (z := z) D * σ₂) = conjV h (sigma1Nine (z := z) D * σ₂) * U
  rw [map_mul]
  calc U * (A * C) = (U * A * U⁻¹) * (U * C * U⁻¹) * U := by group
    _ = C * A * U := by rw [hUA, hUC]
    _ = A * C * U := by rw [hAC]

private theorem conjV_uH_mul_sigma (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    conjV h (uH D) * conjV h (sigma1Nine (z := z) D * σ₂⁻¹) =
      conjV h (sigma1Nine (z := z) D * σ₂⁻¹) * conjV h (sigma1Nine (z := z) D * σ₂⁻¹) *
        conjV h (uH D) := by
  set A := conjV h (sigma1Nine (z := z) D)
  set C := conjV h σ₂
  set U := conjV h (uH D)
  have hUA : U * A * U⁻¹ = C := conjV_uH_conj_sigma1Nine D h hq₂
  have hUC : U * C * U⁻¹ = A := conjV_uH_conj_sigma2 D h hq₂
  have hAC : A * C = C * A := by
    rw [← map_mul, ← map_mul, hcomm.eq]
  have hA3 : A * A * A = 1 := by
    rw [← map_mul, ← map_mul, ← pow_three', pow_three_sigma1Nine D, map_one]
  have hC3 : C * C * C = 1 := by
    have h3 : σ₂ ^ 3 = 1 := by
      rw [← hσ₂]
      exact pow_orderOf_eq_one σ₂
    rw [← map_mul, ← map_mul, ← pow_three', h3, map_one]
  have hAA : A * A = A⁻¹ := eq_inv_of_mul_eq_one_left hA3
  have hCC : C⁻¹ * C⁻¹ = C := by
    have hCC' : C * C = C⁻¹ := eq_inv_of_mul_eq_one_left hC3
    rw [← mul_inv_rev, hCC', inv_inv]
  have hACc : Commute A C := hAC
  have hCA : C⁻¹ * A = A * C⁻¹ := hACc.inv_right.eq.symm
  have hCA' : A⁻¹ * C = C * A⁻¹ := hACc.inv_left.eq
  rw [map_mul, map_inv]
  calc U * (A * C⁻¹) = (U * A * U⁻¹) * (U * C * U⁻¹)⁻¹ * U := by group
    _ = C * A⁻¹ * U := by rw [hUA, hUC]
    _ = A⁻¹ * C * U := by rw [hCA']
    _ = A * A * (C⁻¹ * C⁻¹) * U := by rw [hAA, hCC]
    _ = A * (C⁻¹ * A) * C⁻¹ * U := by rw [hCA]; group
    _ = A * C⁻¹ * (A * C⁻¹) * U := by group

theorem polarVZMod_conjV_tH_self_eq_zero (h : Tim79a.ParrottHyp z) {w : QuotientV.V z}
    (hw : w ∈ Wsub h (sigma1Nine (z := z) D)) :
    polarVZMod h w (conjV h (tH D) w) = 0 := by
  set T := conjV h (tH D)
  set S := conjV h (sigma1Nine (z := z) D)
  have hTT : ∀ v, T (T v) = v := fun v => by
    have := congrArg (fun φ : MulAut (QuotientV.V z) => φ v) (conjV_tH_mul_self D h)
    simpa [MulAut.mul_apply] using this
  have hadd : ∀ a b, polarVZMod h (a * b) (T (a * b)) =
      polarVZMod h a (T a) + polarVZMod h b (T b) := by
    intro a b
    have hcross : polarVZMod h b (T a) = polarVZMod h a (T b) := by
      rw [← polarVZMod_conj_eq h (tH D) b (T a), hTT, polarVZMod_comm]
    rw [map_mul, polarVZMod_add, polarVZMod_add_right, polarVZMod_add_right, hcross]
    have hZ : ∀ p q r : ZMod 2, p + q + (q + r) = p + r := by decide
    exact hZ _ _ _
  have hinv : ∀ a, polarVZMod h (S a) (T (S a)) = polarVZMod h a (T a) := by
    intro a
    have hTS : T (S a) = S (T a) := by
      have := congrArg (fun φ : MulAut (QuotientV.V z) => φ a) (conjV_tH_commute_sigma1Nine D h)
      simpa [MulAut.mul_apply] using this
    rw [hTS]
    exact polarVZMod_conj_eq h (sigma1Nine (z := z) D) a (T a)
  have h1 := mul_conjV_sigma1Nine_mul_eq_one D h hw
  have e : polarVZMod h (w * S w * S (S w)) (T (w * S w * S (S w))) =
      polarVZMod h 1 (T 1) := by rw [h1]
  rw [hadd, hadd, map_one, polarVZMod_self] at e
  simp only [hinv] at e
  have hZ : ∀ p : ZMod 2, p + p + p = 0 → p = 0 := by decide
  exact hZ _ e

theorem polarVZMod_conjV_uH_self_eq_zero (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {w : QuotientV.V z} (hw : w ∈ Wsub h (sigma1Nine (z := z) D)) :
    polarVZMod h w (conjV h (uH D) w) = 0 := by
  have hu : conjV h (uH D) =
      (conjV h (betaH D))⁻¹ * conjV h (tH D) * conjV h (betaH D) := by
    rw [← conjV_betaH_conj_uH D h]
    group
  have hβw : conjV h (betaH D) w ∈ Wsub h (sigma1Nine (z := z) D) :=
    conjV_mem_Wsub D h hσ₂ hq₂ hcomm hEq (betaH D) hw
  rw [hu, ← polarVZMod_conj_eq h (betaH D) w]
  simpa [MulAut.mul_apply] using polarVZMod_conjV_tH_self_eq_zero D h hβw

private theorem conjV_sigma_mem_RbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {a : QuotientV.V z} (ha : a ∈ RbarW D h σ₂) :
    conjV h (sigma1Nine (z := z) D * σ₂⁻¹) a ∈ RbarW D h σ₂ := by
  obtain ⟨haW, haτ⟩ := Subgroup.mem_inf.mp ha
  refine Subgroup.mem_inf.mpr ⟨conjV_mem_Wsub D h hσ₂ hq₂ hcomm hEq _ haW, ?_⟩
  rw [mem_autFixedSubgroup] at haτ ⊢
  have hc := congrArg (fun φ : MulAut (QuotientV.V z) => φ a)
    ((commute_sigma_tau D hcomm).map (conjV h)).eq
  simp only [MulAut.mul_apply] at hc
  rw [← hc, haτ]

private theorem conjV_tH_mem_RbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {a : QuotientV.V z} (ha : a ∈ RbarW D h σ₂) :
    conjV h (tH D) a ∈ RbarW D h σ₂ := by
  obtain ⟨haW, haτ⟩ := Subgroup.mem_inf.mp ha
  refine Subgroup.mem_inf.mpr ⟨conjV_mem_Wsub D h hσ₂ hq₂ hcomm hEq _ haW, ?_⟩
  rw [mem_autFixedSubgroup] at haτ ⊢
  have hc := congrArg (fun φ : MulAut (QuotientV.V z) => φ a) (conjV_tH_commute_tau D h hq₂).eq
  simp only [MulAut.mul_apply] at hc
  rw [← hc, haτ]

private theorem conjV_uH_mem_RbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {a : QuotientV.V z} (ha : a ∈ RbarW D h σ₂) :
    conjV h (uH D) a ∈ RbarW D h σ₂ := by
  obtain ⟨haW, haτ⟩ := Subgroup.mem_inf.mp ha
  refine Subgroup.mem_inf.mpr ⟨conjV_mem_Wsub D h hσ₂ hq₂ hcomm hEq _ haW, ?_⟩
  rw [mem_autFixedSubgroup] at haτ ⊢
  have hc := congrArg (fun φ : MulAut (QuotientV.V z) => φ a)
    (conjV_uH_commute_tau D h hq₂ hcomm).eq
  simp only [MulAut.mul_apply] at hc
  rw [← hc, haτ]

theorem polarVZMod_conjV_sigma_eq_zero_of_mem_RbarW (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {a : QuotientV.V z} (ha : a ∈ RbarW D h σ₂) (hua : conjV h (uH D) a = a) :
    polarVZMod h a (conjV h (sigma1Nine (z := z) D * σ₂⁻¹) a) = 0 := by
  set S := conjV h (sigma1Nine (z := z) D * σ₂⁻¹)
  have hS3 : ∀ v, S (S (S v)) = v := conjV_apply_three h (pow_three_sigma D hσ₂ hcomm)
  have h3 : a * S a * S (S a) = 1 := mul_conjV_sigma_mul_eq_one_of_mem_RbarW D h hσ₂ hcomm ha
  have hqa : qVZMod h a = polarVZMod h a (S a) := by
    have e := congrArg (qVZMod h) h3
    have hqS : ∀ v, qVZMod h (S v) = qVZMod h v := fun v => qVZMod_conj h _ v
    rw [qVZMod_mul_add, qVZMod_mul_add, polarVZMod_add, qVZMod_one] at e
    simp only [hqS] at e
    have e1 : polarVZMod h (S a) (S (S a)) = polarVZMod h a (S a) :=
      polarVZMod_conj_eq h _ a (S a)
    have e2 : polarVZMod h a (S (S a)) = polarVZMod h a (S a) := by
      rw [← polarVZMod_conj_eq h (sigma1Nine (z := z) D * σ₂⁻¹) a (S (S a)), hS3,
        polarVZMod_comm]
    rw [e1, e2] at e
    have hZ : ∀ p b : ZMod 2, p + p + b + p + (b + b) = 0 → p = b := by decide
    exact hZ _ _ e
  have hue : conjV h (uH D) (S a) = S (S a) := by
    have := congrArg (fun φ : MulAut (QuotientV.V z) => φ a)
      (conjV_uH_mul_sigma D h hσ₂ hq₂ hcomm)
    simp only [MulAut.mul_apply] at this
    rw [hua] at this
    exact this
  have hV2 : ∀ p : QuotientV.V z, p * p = 1 := fun p => by
    rw [← pow_two]
    exact QuotientV.pow_two_eq_one_V h p
  have ha_eq : a = S a * conjV h (uH D) (S a) := by
    rw [hue]
    calc a = a * (a * S a * S (S a)) := by rw [h3, mul_one]
      _ = (a * a) * (S a * S (S a)) := by group
      _ = S a * S (S a) := by rw [hV2, one_mul]
  have hSaW : S a ∈ Wsub h (sigma1Nine (z := z) D) :=
    (Subgroup.mem_inf.mp (conjV_sigma_mem_RbarW D h hσ₂ hq₂ hcomm hEq ha)).1
  have hq0 : qVZMod h a = 0 := by
    rw [ha_eq, qVZMod_mul_add, polarVZMod_conjV_uH_self_eq_zero D h hσ₂ hq₂ hcomm hEq hSaW,
      qVZMod_conj h (uH D)]
    have hZ : ∀ p : ZMod 2, p + p + 0 = 0 := by decide
    exact hZ _
  rw [← hqa, hq0]

theorem exists_mem_RbarW_conjV_tH_ne (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    ∃ a ∈ RbarW D h σ₂, conjV h (tH D) a ≠ a := by
  by_contra hcon
  push Not at hcon
  have hVc : ∀ p q : QuotientV.V z, p * q = q * p :=
    (QuotientV.isMulCommutative_V h).is_comm.comm
  have hTQ : ∀ v ∈ QbarW D h σ₂, conjV h (tH D) v ∈ QbarW D h σ₂ := by
    intro v hv
    obtain ⟨hvW, hvσ⟩ := Subgroup.mem_inf.mp hv
    refine Subgroup.mem_inf.mpr ⟨conjV_mem_Wsub D h hσ₂ hq₂ hcomm hEq _ hvW, ?_⟩
    rw [mem_autFixedSubgroup] at hvσ ⊢
    have hc := congrArg (fun φ : MulAut (QuotientV.V z) => φ v)
      (conjV_tH_commute_sigma D h hq₂).eq
    simp only [MulAut.mul_apply] at hc
    rw [← hc, hvσ]
  have hV : conjV h (tH D) = 1 := by
    ext v
    have hv : v ∈ Fsub (z := z) (sigma1Nine (z := z) D) ⊔ Wsub h (sigma1Nine (z := z) D) := by
      rw [sup_Fsub_Wsub_sigma1Nine D h]
      exact Subgroup.mem_top v
    obtain ⟨f, hf, w, hw, rfl⟩ := (CFSG.mem_sup_of_commute fun a _ b _ => hVc a b).mp hv
    obtain ⟨q, hq, r, hr, rfl⟩ := exists_mul_of_mem_Wsub D h hσ₂ hcomm hEq hw
    rw [map_mul, map_mul, conjV_eq_self_of_mem_Fsub D h hσ₂ hq₂ hEq (tH_mem_P_H D) hf,
      conjV_eq_self_of_mem_QbarW D h hσ₂ hq₂ hcomm hEq (conjV_tH_mul_self D h)
        (conjV_tH_commute_tau D h hq₂).eq hTQ hq, hcon r hr]
    rfl
  have hZ : conjZ z (tH D) = 1 := conjZ_eq_one_of_mem_Q D h (tH D) (qH_tH_mem_Q D)
  have htJ : ((tH D : ↥(H z)) : G) ∈ J z := mem_J_of_conjZ_eq_one_of_conjV_eq_one h hZ hV
  have h1 : qH D (tH D) = 1 := (J_mem_iff D (tH D)).mp (Subgroup.mem_subgroupOf.mpr htJ)
  rw [qH_tH] at h1
  exact t_ne_one (congrArg Subtype.val h1)

theorem exists_mem_RbarW_polarVZMod_ne_zero (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    ∃ a ∈ RbarW D h σ₂, polarVZMod h a (conjV h (tH D) (conjV h (uH D) a)) ≠ 0 := by
  have hVc : ∀ p q : QuotientV.V z, p * q = q * p :=
    (QuotientV.isMulCommutative_V h).is_comm.comm
  have hV2 : ∀ p : QuotientV.V z, p * p = 1 := fun p => by
    rw [← pow_two]
    exact QuotientV.pow_two_eq_one_V h p
  have happ : ∀ {φ ψ : MulAut (QuotientV.V z)}, φ = ψ → ∀ v, φ v = ψ v := fun e v => by
    rw [e]
  refine exists_mem_polar_ne_zero_of_semilinear_involution hVc hV2 (RbarW D h σ₂)
    (card_RbarW D h hσ₂ hq₂ hcomm hEq).le (polarVZMod h) (polarVZMod_add h)
    (polarVZMod_add_right h) (fun a _ b _ => polarVZMod_comm h a b) ?_
    (conjV h (sigma1Nine (z := z) D * σ₂⁻¹)) (conjV h (tH D)) (conjV h (uH D))
    (fun a ha => conjV_sigma_mem_RbarW D h hσ₂ hq₂ hcomm hEq ha)
    (fun a ha => conjV_tH_mem_RbarW D h hσ₂ hq₂ hcomm hEq ha)
    (fun a ha => conjV_uH_mem_RbarW D h hσ₂ hq₂ hcomm hEq ha)
    (fun a ha => mul_conjV_sigma_mul_eq_one_of_mem_RbarW D h hσ₂ hcomm ha)
    (fun a _ b _ => polarVZMod_conj_eq h _ a b) (fun a _ b _ => polarVZMod_conj_eq h _ a b)
    (fun a _ => by simpa [MulAut.mul_apply] using happ (conjV_tH_mul_self D h) a)
    (fun a _ => by simpa [MulAut.mul_apply] using happ (conjV_uH_mul_self D h) a)
    (fun a _ => by simpa [MulAut.mul_apply] using happ (conjV_tH_commute_uH D h) a)
    (fun a _ => by simpa [MulAut.mul_apply] using happ (conjV_tH_commute_sigma D h hq₂).eq a)
    (fun a _ => by
      simpa [MulAut.mul_apply] using happ (conjV_uH_mul_sigma D h hσ₂ hq₂ hcomm) a)
    (fun a ha hua => polarVZMod_conjV_sigma_eq_zero_of_mem_RbarW D h hσ₂ hq₂ hcomm hEq ha hua)
    (exists_mem_RbarW_conjV_tH_ne D h hσ₂ hq₂ hcomm hEq)
  intro a ha h0
  refine eq_one_of_mem_Wsub_of_forall_polarVZMod D h (Subgroup.mem_inf.mp ha).1 fun w hw => ?_
  obtain ⟨q, hq, r, hr, rfl⟩ := exists_mul_of_mem_Wsub D h hσ₂ hcomm hEq hw
  rw [polarVZMod_add_right, polarVZMod_comm h a q,
    polarVZMod_eq_zero_of_mem_QbarW_of_mem_RbarW D h hσ₂ hcomm hq ha, h0 r hr, add_zero]

theorem exists_mem_R_sq_eq_z_conj_eq_mul_z
    (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {x : G} (hx : cosetJ (z := z) (tH D * uH D) x) (hx2 : orderOf x = 2) :
    ∃ r ∈ sigma1Commutator (z := z) D,
      r ∈ Subgroup.centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G) ∧
      r * r = z ∧ x * r * x⁻¹ = r * z := by
  set τ : ↥(H z) := sigma1Nine (z := z) D * σ₂ with hτ_def
  have hxH : x ∈ H z := by
    obtain ⟨j, hj, rfl⟩ := hx
    exact (H z).mul_mem (tH D * uH D).2 (J_le_H hj)
  set X : ↥(H z) := ⟨x, hxH⟩ with hX_def
  have hxx : x * x = 1 := by
    rw [← pow_two, ← hx2]
    exact pow_orderOf_eq_one x
  have hX : conjV h X = conjV h (tH D) * conjV h (uH D) := conjV_eq_tH_mul_uH D h hxH hx
  have hzc : ∀ g ∈ H z, g * z = z * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hz2 : z * z = 1 := sq_eq_one_of_mem_zpowers h (Subgroup.mem_zpowers z)
  have hmemR : ∀ {c : J z}, c ∈ CJcomm (z := z) (D := D) τ →
      (c : G) ∈ sigma1Commutator (z := z) D ∧ (τ : G) * c = c * τ := by
    intro c hc
    obtain ⟨hcτ, hcW⟩ := Subgroup.mem_inf.mp hc
    exact ⟨Subgroup.mem_subgroupOf.mp hcW, (mem_centralizerJ_iff.mp hcτ).symm⟩
  obtain ⟨a, ha, hne⟩ := exists_mem_RbarW_polarVZMod_ne_zero D h hσ₂ hq₂ hcomm hEq
  obtain ⟨v, hv, rfl⟩ := (mem_RbarW_iff D h hσ₂ hcomm a).mp ha
  obtain ⟨hvW, hvτ⟩ := hmemR hv
  have hvJ : (v : G) ∈ J z := v.2
  have hvH : (v : G) ∈ H z := J_le_H hvJ
  set w : J z := conjJ' z X v with hw_def
  have hw : (w : G) = x * v * x⁻¹ := by rw [hw_def, conjJ'_apply_coe]
  have hxa : conjV h (tH D) (conjV h (uH D) (QuotientV.pi z v)) = QuotientV.pi z w := by
    rw [hw_def, ← conjV_mk h X v, hX, MulAut.mul_apply]
  rw [hxa] at hne
  have hncomm : ¬ Commute (v : G) (w : G) := fun hc =>
    hne ((polarVZMod_pi_eq_zero_iff h v w).mpr hc)
  have hvw : (v : G) * w * (v : G)⁻¹ * (w : G)⁻¹ = z := by
    have hmem := commutator_mem_zpowers_z h hvJ w.2
    rw [commutatorElement_def] at hmem
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two h.1).mp hmem with h1 | h1
    · exfalso
      apply hncomm
      calc (v : G) * w = ((v : G) * w * (v : G)⁻¹ * (w : G)⁻¹) * ((w : G) * v) := by group
        _ = (w : G) * v := by rw [h1, one_mul]
    · exact h1
  have hwH : (w : G) ∈ H z := J_le_H w.2
  have hwW : (w : G) ∈ sigma1Commutator (z := z) D := by
    rw [hw, sigma1Commutator_eq_commutator]
    rw [sigma1Commutator_eq_commutator] at hvW
    exact commutator_sigma1Nine_conj_mem (z := z) (D := D) h hEq hσ₂ hq₂ hcomm.eq.symm X v hvW
  have hwτ : (τ : G) * w = w * τ := by
    have hwR : QuotientV.pi z w ∈ RbarW D h σ₂ := by
      rw [← hxa]
      exact conjV_tH_mem_RbarW D h hσ₂ hq₂ hcomm hEq
        (conjV_uH_mem_RbarW D h hσ₂ hq₂ hcomm hEq ha)
    obtain ⟨r', hr', hr'π⟩ := (mem_RbarW_iff D h hσ₂ hcomm _).mp hwR
    obtain ⟨hr'W, hr'τ⟩ := hmemR hr'
    have hζZ : (w : G) * (r' : G)⁻¹ ∈ centerIn (J z) := by
      have hker : w * r'⁻¹ ∈ (QuotientV.pi z).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ← hr'π, mul_inv_cancel]
      rw [QuotientV.pi_ker] at hker
      simpa using Subgroup.mem_subgroupOf.mp hker
    have hζ : (w : G) * (r' : G)⁻¹ ∈ Subgroup.zpowers z := by
      rw [← sigma1Commutator_inf_centerIn D h]
      exact ⟨(sigma1Commutator (z := z) D).mul_mem hwW
        ((sigma1Commutator (z := z) D).inv_mem hr'W), hζZ⟩
    have hζτ : (τ : G) * ((w : G) * (r' : G)⁻¹) = ((w : G) * (r' : G)⁻¹) * τ :=
      Subgroup.mem_centralizer_iff.mp (zpowers_centralizes_H h hζ) (τ : G) τ.2
    calc (τ : G) * w = (τ : G) * ((w : G) * (r' : G)⁻¹) * r' := by group
      _ = ((w : G) * (r' : G)⁻¹) * τ * r' := by rw [hζτ]
      _ = ((w : G) * (r' : G)⁻¹) * (τ * r') := by group
      _ = ((w : G) * (r' : G)⁻¹) * (r' * τ) := by rw [hr'τ]
      _ = w * τ := by group
  have hv2 : (v : G) * v ∈ Subgroup.zpowers z := sq_mem_zpowers_z h hvJ
  have hw2 : (w : G) * w = (v : G) * v := by
    have hxc : x * ((v : G) * v) = ((v : G) * v) * x :=
      Subgroup.mem_centralizer_iff.mp (zpowers_centralizes_H h hv2) x hxH
    calc (w : G) * w = x * ((v : G) * v) * x⁻¹ := by rw [hw]; group
      _ = ((v : G) * v) * x * x⁻¹ := by rw [hxc]
      _ = (v : G) * v := by group
  have hwv : (w : G)⁻¹ * v = z * ((v : G) * (w : G)⁻¹) := by
    have e1 : (v : G) * w = z * ((w : G) * v) := by
      calc (v : G) * w = ((v : G) * w * (v : G)⁻¹ * (w : G)⁻¹) * ((w : G) * v) := by group
        _ = z * ((w : G) * v) := by rw [hvw]
    calc (w : G)⁻¹ * v = (w : G)⁻¹ * ((v : G) * w) * (w : G)⁻¹ := by group
      _ = (w : G)⁻¹ * (z * ((w : G) * v)) * (w : G)⁻¹ := by rw [e1]
      _ = ((w : G)⁻¹ * z) * ((w : G) * v) * (w : G)⁻¹ := by group
      _ = (z * (w : G)⁻¹) * ((w : G) * v) * (w : G)⁻¹ := by rw [hzc _ ((H z).inv_mem hwH)]
      _ = z * ((v : G) * (w : G)⁻¹) := by group
  have hsq : (v : G) * (w : G)⁻¹ * ((v : G) * (w : G)⁻¹) = z := by
    calc (v : G) * (w : G)⁻¹ * ((v : G) * (w : G)⁻¹) = v * ((w : G)⁻¹ * v) * (w : G)⁻¹ := by
          group
      _ = v * (z * ((v : G) * (w : G)⁻¹)) * (w : G)⁻¹ := by rw [hwv]
      _ = ((v : G) * z) * v * (w : G)⁻¹ * (w : G)⁻¹ := by group
      _ = (z * v) * v * (w : G)⁻¹ * (w : G)⁻¹ := by rw [hzc _ hvH]
      _ = z * ((v : G) * v) * ((w : G) * w)⁻¹ := by group
      _ = z := by rw [hw2]; group
  refine ⟨(v : G) * (w : G)⁻¹, (sigma1Commutator (z := z) D).mul_mem hvW
    ((sigma1Commutator (z := z) D).inv_mem hwW), ?_, hsq, ?_⟩
  ·
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    have hτw' : (τ : G) * (w : G)⁻¹ = (w : G)⁻¹ * τ := by
      calc (τ : G) * (w : G)⁻¹ = (w : G)⁻¹ * ((w : G) * τ) * (w : G)⁻¹ := by group
        _ = (w : G)⁻¹ * ((τ : G) * w) * (w : G)⁻¹ := by rw [hwτ]
        _ = (w : G)⁻¹ * τ := by group
    calc (τ : G) * ((v : G) * (w : G)⁻¹) = ((τ : G) * v) * (w : G)⁻¹ := by group
      _ = ((v : G) * τ) * (w : G)⁻¹ := by rw [hvτ]
      _ = (v : G) * ((τ : G) * (w : G)⁻¹) := by group
      _ = (v : G) * ((w : G)⁻¹ * τ) := by rw [hτw']
      _ = (v : G) * (w : G)⁻¹ * τ := by group
  ·
    have hconj : x * ((v : G) * (w : G)⁻¹) * x⁻¹ = (w : G) * (v : G)⁻¹ := by
      rw [hw]
      calc x * ((v : G) * (x * v * x⁻¹)⁻¹) * x⁻¹
          = x * v * x⁻¹ * ((x * x) * (v : G)⁻¹ * (x * x)⁻¹) := by group
        _ = x * v * x⁻¹ * (v : G)⁻¹ := by rw [hxx]; group
    rw [hconj]
    calc (w : G) * (v : G)⁻¹ = ((v : G) * (w : G)⁻¹)⁻¹ := by group
      _ = ((v : G) * (w : G)⁻¹)⁻¹ * (z * z) := by rw [hz2, mul_one]
      _ = ((v : G) * (w : G)⁻¹)⁻¹ * ((v : G) * (w : G)⁻¹ * ((v : G) * (w : G)⁻¹)) * z := by
          rw [hsq]; group
      _ = (v : G) * (w : G)⁻¹ * z := by group

end CFSG.RankThree.GF2n.Parrott
