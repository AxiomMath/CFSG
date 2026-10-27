module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LieType.Ree.SuzukiOvoidWeyl
import CFSG.Blueprint.LieModelAPI
import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers
import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree Subgroup
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szFieldAut_D)
open scoped LinearAlgebra.Projectivization

theorem uc22r899c3_suzuki_normalizer_torus {a : ℕ} {K : Type}
    [Field K] [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : suzukiGroup a K} (hg : ∀ t ∈ suzukiT a K, g * t * g⁻¹ ∈ suzukiT a K) :
    g ∈ suzukiT a K ∨ g * suzukiWElt a K ∈ suzukiT a K := by
  obtain ⟨l, hl⟩ : ∃ l : Kˣ, l ≠ 1 := by
    have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    haveI : Nontrivial Kˣ :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [Nat.card_units, hK]; omega)
    exact exists_ne 1
  obtain ⟨μ, hμ⟩ := mem_suzukiT_iff.1 (hg _ (suzukiDElt_mem_suzukiT a K l))
  have hμ1 : μ ≠ 1 := by
    rintro rfl
    rw [suzukiDElt_one] at hμ
    exact hl (suzukiDElt_injective hK ((conj_eq_one_iff.1 hμ.symm).trans suzukiDElt_one.symm))
  have hfix : ∀ x : ℙ K (Fin 4 → K), suzukiDElt a K l • x = x →
      suzukiDElt a K μ • (g • x) = g • x := by
    intro x hx
    rw [hμ, mul_smul, mul_smul, inv_smul_smul, hx]
  have hinf := hfix _ (suzuki_ovoid_torus_action a hK l 0 0).1
  have hzero := hfix _ (suzukiDElt_smul_suzukiLine_zero hK l)
  have hmem : ∀ x ∈ suzukiOmega a K, g • x ∈ suzukiOmega a K := fun x hx =>
    suzuki_smul_mem_suzukiOmega hK g hx
  have hne := suzukiLine_ne_suzukiInfty (a := a) (0 : K) 0
  obtain ⟨hW1, hW2, -⟩ := suzuki_ovoid_weyl_action a hK
  rcases fixed_mem_suzukiOmega hK hμ1 (hmem _ (suzukiInfty_mem_suzukiOmega a K)) hinf with
    h1 | h1 <;>
  rcases fixed_mem_suzukiOmega hK hμ1 (hmem _ (suzukiLine_mem_suzukiOmega a K 0 0)) hzero with
    h2 | h2
  · exact absurd (smul_left_cancel g (h2.trans h1.symm)) hne
  · exact Or.inl (mem_suzukiT_of_smul_eq hK h1 h2)
  · exact Or.inr (mem_suzukiT_of_smul_eq hK (by rw [mul_smul, hW1, h2])
      (by rw [mul_smul, hW2, h1]))
  · exact absurd (smul_left_cancel g (h2.trans h1.symm)) hne

theorem uc22r899c3_suzuki_fixes {a : ℕ} {K : Type} [Field K]
    [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {m p : ℕ}
    (hn : 2 * a + 1 = p * m) (hp : p.Prime) (hp2 : p ≠ 2) (α : MulAut (suzukiGroup a K))
    (hαT : ∀ x, x ∈ suzukiT a K ↔ α x ∈ suzukiT a K) (hαp : α ^ p = 1) {l : Kˣ}
    (hl : l ^ 2 ^ m = l) : α (suzukiDElt a K l) = suzukiDElt a K l := by
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  obtain ⟨-, ⟨e, he⟩, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  obtain ⟨⟨x, τ⟩, hxτ⟩ := e.surjective α
  rw [he] at hxτ
  obtain ⟨i, hi⟩ := uc22pwlie_ringEquiv_pow τ
  have hαD : ∀ s : Kˣ, α (suzukiDElt a K s) = x * suzukiDElt a K (s ^ 2 ^ i) * x⁻¹ := fun s => by
    rw [← hxτ, MulAut.mul_apply, szFieldAut_D, MulAut.conj_apply]
    exact congrArg (fun y => x * suzukiDElt a K y * x⁻¹) (Units.ext (by simp [hi]))
  have hxT : ∀ t ∈ suzukiT a K, x * t * x⁻¹ ∈ suzukiT a K := by
    intro t ht
    obtain ⟨s, rfl⟩ := mem_suzukiT_iff.1 ht
    have h1 := (hαT (suzukiDElt a K (Units.map (τ.symm : K →* K) s))).1
      (suzukiDElt_mem_suzukiT a K _)
    rwa [← hxτ, MulAut.mul_apply, szFieldAut_D, MulAut.conj_apply,
      show Units.map (τ : K →* K) (Units.map (τ.symm : K →* K) s) = s from
        Units.ext (by simp)] at h1
  obtain ⟨N, hN, hα1⟩ : ∃ N : ℤ, (N = ((2 ^ i : ℕ) : ℤ) ∨ N = -((2 ^ i : ℕ) : ℤ)) ∧
      ∀ s : Kˣ, α (suzukiDElt a K s) = suzukiDElt a K (s ^ N) := by
    rcases uc22r899c3_suzuki_normalizer_torus ha hK hxT with hx | hx
    · obtain ⟨μ, rfl⟩ := mem_suzukiT_iff.1 hx
      refine ⟨_, Or.inl rfl, fun s => ?_⟩
      rw [zpow_natCast, hαD, suzukiDElt_inv, suzukiDElt_mul, suzukiDElt_mul, mul_comm μ,
        mul_assoc, mul_inv_cancel, mul_one]
    · obtain ⟨μ, hμ⟩ := mem_suzukiT_iff.1 hx
      have hxe : x = suzukiDElt a K μ * suzukiWElt a K := by
        rw [hμ, mul_assoc, suzukiWElt_mul_self, mul_one]
      refine ⟨_, Or.inr rfl, fun s => ?_⟩
      rw [hαD, hxe, zpow_neg, zpow_natCast, mul_inv_rev, suzukiWElt_inv, suzukiDElt_inv]
      calc suzukiDElt a K μ * suzukiWElt a K * suzukiDElt a K (s ^ 2 ^ i) *
            (suzukiWElt a K * suzukiDElt a K μ⁻¹)
          = suzukiDElt a K μ * (suzukiWElt a K * suzukiDElt a K (s ^ 2 ^ i) * suzukiWElt a K) *
            suzukiDElt a K μ⁻¹ := by simp only [mul_assoc]
        _ = suzukiDElt a K (s ^ 2 ^ i)⁻¹ := by
            rw [suzukiWElt_D_W hK, suzukiDElt_mul, suzukiDElt_mul, mul_comm μ, mul_assoc,
              mul_inv_cancel, mul_one]
  have hpow : ∀ (j : ℕ) (s : Kˣ), (α ^ j) (suzukiDElt a K s) = suzukiDElt a K (s ^ (N ^ j)) := by
    intro j
    induction j with
    | zero => intro s; simp
    | succ j ih =>
      intro s
      rw [pow_succ α j, MulAut.mul_apply, hα1, ih, ← zpow_mul, pow_succ N j, mul_comm N]
  have hfix : ∀ s : Kˣ, s ^ (N ^ p) = s := fun s => by
    have h1 := hpow p s
    rw [hαp, MulAut.one_apply] at h1
    exact (suzukiDElt_injective hK h1).symm
  rcases hN with rfl | rfl
  ·
    have hdvd : 2 * a + 1 ∣ i * p := uc22r8100b_dvd_of_fix hK fun s => by
      simpa only [← Nat.cast_pow, zpow_natCast, ← pow_mul] using hfix s
    rw [hn, mul_comm i p] at hdvd
    obtain ⟨t, rfl⟩ := Nat.dvd_of_mul_dvd_mul_left hp.pos hdvd
    have hat : ∀ t : ℕ, l ^ 2 ^ (m * t) = l := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [Nat.mul_succ, pow_add, pow_mul', hl, ih]
    rw [hα1, zpow_natCast, hat]
  ·
    have hinv : ∀ s : Kˣ, s ^ 2 ^ (i * p) = s⁻¹ := fun s => by
      have h1 := hfix s
      rw [Odd.neg_pow (hp.odd_of_ne_two hp2), ← Nat.cast_pow, ← pow_mul, zpow_neg,
        zpow_natCast] at h1
      exact inv_eq_iff_eq_inv.1 h1
    have hfix2 : ∀ s : Kˣ, s ^ 2 ^ (2 * (i * p)) = s := fun s => by
      rw [two_mul, pow_add, pow_mul s (2 ^ (i * p)) (2 ^ (i * p)), hinv s, inv_pow, hinv s,
        inv_inv]
    have hdvd : 2 * a + 1 ∣ i * p := Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)))
      (uc22r8100b_dvd_of_fix hK hfix2)
    have hall : ∀ s : Kˣ, s = 1 := fun s => by
      obtain ⟨c, hc⟩ := Nat.pow_sub_one_dvd_pow_sub_one 2 hdvd
      have h0 : s ^ (2 ^ (i * p) - 1) = 1 := by
        rw [hc, pow_mul, ← hK, ← Nat.card_units, pow_card_eq_one', one_pow]
      have h1 : s ^ 2 ^ (i * p) = s := by
        rw [← Nat.sub_add_cancel (Nat.one_le_two_pow : 1 ≤ 2 ^ (i * p)), pow_succ, h0, one_mul]
      exact eq_one_of_sq_eq_one hK (by rw [sq, mul_eq_one_iff_eq_inv, ← hinv s, h1])
    rw [hall l, suzukiDElt_one, map_one]

theorem uc22r899c3_suzuki_torus_frame {X : Type} [Group X]
    [Finite X] {n : ℕ} (h : IsSz X n) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hq : q ∣ 2 ^ n - 1) (Q : Sylow q X) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : X ≃* suzukiGroup a K),
      1 ≤ a ∧ n = 2 * a + 1 ∧ Nat.card K = 2 ^ n ∧
      Subgroup.map e.toMonoidHom (Q : Subgroup X) ≤ suzukiT a K ∧
      ∀ g : suzukiGroup a K,
        (∀ s ∈ Subgroup.map e.toMonoidHom (Q : Subgroup X), g * s = s * g) →
        g ∈ suzukiT a K := by
  obtain ⟨-, -, a, ha, K, hKf, hKfin, rfl, hK, ⟨e₀⟩⟩ := LieModel.suzukiModel h
  have hqX : q ∣ Nat.card X := by
    have h1 : q ∣ Nat.card (suzukiT a K) := by
      rw [(suzuki_borel_structure hK).2.2.1]
      exact hq
    rw [Nat.card_congr e₀.toEquiv]
    exact h1.trans (Subgroup.card_subgroup_dvd_card _)
  have hQq : q ∣ Nat.card Q := Q.dvd_card_of_dvd_card hqX
  haveI : Nontrivial Q := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    exact lt_of_lt_of_le (Fact.out : q.Prime).one_lt (Nat.le_of_dvd Nat.card_pos hQq)
  have hQp : IsPGroup q Q := Q.isPGroup'
  haveI := hQp.center_nontrivial
  have hZq : q ∣ Nat.card (Subgroup.center Q) := by
    rcases (hQp.to_subgroup (Subgroup.center Q)).card_eq_or_dvd with h1 | h1
    · exact absurd h1 (Nat.ne_of_gt Finite.one_lt_card)
    · exact h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center Q)) q hZq
  have hz0o : orderOf (((z : Q)) : X) = q := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hz0c : ∀ s ∈ (Q : Subgroup X), s * ((z : Q) : X) = ((z : Q) : X) * s := fun s hs =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨s, hs⟩)
  obtain ⟨g, hg⟩ := exists_conj_mem_suzukiT hK (Fact.out : q.Prime) hq2 hq
    ((MulEquiv.orderOf_eq e₀ _).trans hz0o)
  obtain ⟨μ, hμ⟩ := mem_suzukiT_iff.1 hg
  let e : X ≃* suzukiGroup a K := e₀.trans (MulAut.conj g⁻¹)
  have hez : e ((z : Q) : X) = suzukiDElt a K μ := by
    rw [hμ]
    simp only [e, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hμ1 : μ ≠ 1 := by
    rintro rfl
    have h1 : e ((z : Q) : X) = 1 := by rw [hez, suzukiDElt_one]
    rw [← orderOf_eq_one_iff, MulEquiv.orderOf_eq, hz0o] at h1
    exact (Fact.out : q.Prime).one_lt.ne' h1
  have hC := centralizer_suzukiDElt hK hμ1
  have hS : ∀ s ∈ (Q : Subgroup X), e s ∈ suzukiT a K := by
    intro s hs
    rw [← hC, Subgroup.mem_centralizer_singleton_iff, ← hez, ← map_mul, ← map_mul, hz0c s hs]
  refine ⟨a, K, hKf, hKfin, e, ha, rfl, hK, ?_, fun g' hg' => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact hS s hs
  · rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    exact hg' _ ⟨_, ((z : Q)).2, hez⟩

theorem uc22r899c3_fixes_of_aut_Sz {X : Type} [Group X]
    [Finite X] {n m p q : ℕ} (h : IsSz X n) (hn : n = p * m) (hp : p.Prime) (hp2 : p ≠ 2)
    [Fact q.Prime] (hq2 : q ≠ 2) (hqm : q ∣ 2 ^ m - 1) (Q : Sylow q X) (ψ : MulAut X)
    (hψQ : ∀ x, x ∈ (Q : Subgroup X) ↔ ψ x ∈ (Q : Subgroup X)) (hψp : ψ ^ p = 1) {t : X}
    (ht : t ∈ (Q : Subgroup X)) (hto : orderOf t = q) : ψ t = t := by
  have hq : q ∣ 2 ^ n - 1 :=
    hqm.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨p, by rw [hn, mul_comm]⟩)
  obtain ⟨a, K, hKf, hKfin, e, ha, rfl, hK, hST, hC⟩ :=
    uc22r899c3_suzuki_torus_frame h hq2 hq Q
  set S' : Subgroup (suzukiGroup a K) := Subgroup.map e.toMonoidHom (Q : Subgroup X) with hS'
  have hmemS : ∀ g, g ∈ S' ↔ e.symm g ∈ (Q : Subgroup X) := fun g => Subgroup.mem_map_equiv
  let ψ' : MulAut (suzukiGroup a K) := MulAut.congr e ψ
  have hψ'a : ∀ g, ψ' g = e (ψ (e.symm g)) := fun g => rfl
  have hψ'S : ∀ g, g ∈ S' ↔ ψ' g ∈ S' := by
    intro g
    rw [hmemS, hmemS, hψ'a, e.symm_apply_apply]
    exact hψQ _
  have hTab := (suzuki_borel_structure hK).2.1
  have hpres : ∀ φ : MulAut (suzukiGroup a K), (∀ g, g ∈ S' ↔ φ g ∈ S') →
      ∀ x ∈ suzukiT a K, φ x ∈ suzukiT a K := by
    intro φ hφ x hx
    refine hC _ fun s hs => ?_
    obtain ⟨s₀, rfl⟩ : ∃ s₀, φ s₀ = s := ⟨φ.symm s, φ.apply_symm_apply s⟩
    have h1 : x * s₀ = s₀ * x := hTab x hx s₀ (hST ((hφ s₀).2 hs))
    rw [← map_mul, ← map_mul, h1]
  have hψ'T : ∀ x, x ∈ suzukiT a K ↔ ψ' x ∈ suzukiT a K := by
    refine fun x => ⟨hpres ψ' hψ'S x, fun hx => ?_⟩
    have hsymm : ∀ g, g ∈ S' ↔ ψ'.symm g ∈ S' := fun g => by
      rw [hψ'S (ψ'.symm g), ψ'.apply_symm_apply]
    simpa using hpres ψ'.symm hsymm _ hx
  have hψ'p : ψ' ^ p = 1 := by
    have : ψ' ^ p = MulAut.congr e (ψ ^ p) := (map_pow (MulAut.congr e) ψ p).symm
    rw [this, hψp, map_one]
  obtain ⟨τ, hτ⟩ : ∃ τ : Kˣ, suzukiDElt a K τ = e t := mem_suzukiT_iff.1 (hST ⟨t, ht, rfl⟩)
  have hDpow : ∀ (s : Kˣ) (k : ℕ), suzukiDElt a K (s ^ k) = suzukiDElt a K s ^ k := by
    intro s k
    induction k with
    | zero => rw [pow_zero, pow_zero, suzukiDElt_one]
    | succ k ih => rw [pow_succ, pow_succ, ← ih, suzukiDElt_mul]
  have ht1 : t ^ q = 1 := by simpa [hto] using pow_orderOf_eq_one t
  have hτq : τ ^ q = 1 := by
    apply suzukiDElt_injective hK
    rw [hDpow, hτ, ← map_pow e t q, ht1, map_one, suzukiDElt_one]
  have hτ2 : τ ^ 2 ^ m = τ := by
    obtain ⟨c, hc⟩ := hqm
    have h1 : τ ^ (2 ^ m - 1) = 1 := by rw [hc, pow_mul, hτq, one_pow]
    calc τ ^ 2 ^ m = τ ^ (2 ^ m - 1 + 1) := by rw [Nat.sub_add_cancel Nat.one_le_two_pow]
      _ = τ := by rw [pow_succ, h1, one_mul]
  have hfix := uc22r899c3_suzuki_fixes ha hK hn hp hp2 ψ' hψ'T hψ'p hτ2
  rw [hτ, hψ'a, e.symm_apply_apply] at hfix
  exact e.injective hfix

end CFSG.LocalAnalysis.UniquenessCase.UC22
