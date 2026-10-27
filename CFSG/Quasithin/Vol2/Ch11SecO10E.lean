module

public import CFSG.Quasithin.Vol2.KGNatSp4Flag
public import CFSG.Quasithin.Vol2.Ch11SecO1A

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open Ch11.SecA (EndStableW)

theorem card_eq_pow_of_endStableW {D : FFModel} {K M : Type} [Field K] [Finite K]
    [AddCommGroup M] [Module K M] [Module.Finite K M] {LM : LinModel D K M} {W : Type*}
    [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)} {π : D.Gam →* ↥H}
    {f : W → M} (hf : IsCoord LM H ⊥ π f)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    {U : Subgroup W} (hU : EndStableW H ⊥ U) : ∃ d : ℕ, Nat.card U = Nat.card K ^ d := by
  have : Finite M := Module.finite_of_finite K
  have hsc := (hf.endStableW_iff hW hcomm (bot_le : (⊥ : Subgroup W) ≤ U)).mp hU
  let S : Submodule K M :=
    { carrier := hf.img U
      add_mem' := (hf.img U).add_mem
      zero_mem' := (hf.img U).zero_mem
      smul_mem' := fun c x hx => hsc c x hx }
  refine ⟨Module.finrank K S, ?_⟩
  rw [← Subgroup.relIndex_bot_left, ← hf.card_img]
  exact Module.natCard_eq_pow_finrank (K := K) (V := S)

theorem exists_central_of_conj {Γ Y : Type*} [Group Γ] [Group Y] (ψ : Γ →* Y)
    (hψ : Function.Injective ψ) {U₀ Z' : Subgroup Γ} {P : Subgroup Y}
    (hP : ∀ x, x ∈ P ↔ ∃ u ∈ U₀, x = ψ u) (hZU : Z' ≤ U₀)
    (hZc : ∀ z ∈ Z', ∀ u ∈ U₀, z * u = u * z) :
    ∃ Z₀ : Subgroup Y, Z₀ ≤ P ∧ (∀ z ∈ Z₀, ∀ p ∈ P, z * p = p * z) ∧
      Nat.card Z₀ = Nat.card Z' ∧ Nat.card P = Nat.card U₀ := by
  have hPeq : P = U₀.map ψ := by
    ext x
    rw [hP, Subgroup.mem_map]
    exact ⟨fun ⟨u, hu, h⟩ => ⟨u, hu, h.symm⟩, fun ⟨u, hu, h⟩ => ⟨u, hu, h.symm⟩⟩
  refine ⟨Z'.map ψ, ?_, ?_, Subgroup.card_map_of_injective hψ, ?_⟩
  · rw [hPeq]
    exact Subgroup.map_mono hZU
  · rintro _ ⟨z, hz, rfl⟩ p hp
    rw [hPeq] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    rw [← map_mul, ← map_mul, hZc z hz u hu]
  · rw [hPeq]
    exact Subgroup.card_map_of_injective hψ

@[expose] def NatFactsW {W : Type*} [CommGroup W] [Finite W] (H P : Subgroup (MulAut W))
    (n : ℕ) : Prop :=
  (∀ U : Subgroup W, EndStableW H ⊥ U → ∃ d : ℕ, Nat.card U = (2 ^ n) ^ d) ∧
    Nat.card W ≤ (2 ^ n) ^ 4 ∧ Nontrivial W ∧
    (∃ Z₀ : Subgroup (MulAut W), Z₀ ≤ P ∧ (∀ z ∈ Z₀, ∀ p ∈ P, z * p = p * z) ∧
      2 ^ n ≤ Nat.card Z₀) ∧ 2 ^ n < Nat.card P

theorem natFacts_sl3 {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {π : ↥(StatedSL 3 K) →* ↥H}
    (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π) {P : Subgroup (MulAut W)}
    (hP : QuasithinUnique.IsSylowTwoOf P H) : NatFactsW H P n := by
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hcardW : Nat.card W = (2 ^ n) ^ 3 := by
    rw [Nat.card_eq_of_bijective f ⟨Ch11.SecO1.IsCoord.injective_of_bot hf, hf.surj⟩,
      Nat.card_fun, hK, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hq : 2 ≤ 2 ^ n := le_self_pow₀ (by norm_num) (by omega)
  refine ⟨fun U hU => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨d, hd⟩ := card_eq_pow_of_endStableW hW hf
      (fun T hT => commutant_statedSL (by norm_num) T hT) hU
    exact ⟨d, hK ▸ hd⟩
  · rw [hcardW]
    exact Nat.pow_le_pow_right (by positivity) (by norm_num)
  · rw [← Finite.one_lt_card_iff_nontrivial, hcardW]
    exact Nat.one_lt_pow (by norm_num) (by omega)
  all_goals obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  all_goals
    let ψ : Matrix.SpecialLinearGroup (Fin 3) K →* MulAut W :=
      (H.subtype.comp (rho3 π)).comp (MulAut.conj g).toMonoidHom
    have hψ : Function.Injective ψ := (Subtype.val_injective.comp (rho3_bijective hf).1).comp
      (MulAut.conj g).injective
    have hP' : ∀ x, x ∈ P ↔ ∃ u ∈ Usl K, x = ψ u := fun x => by
      rw [hg x]
      rfl
    let Z' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
      { carrier := {x | ∃ b : K, x = uSL 0 b 0}
        mul_mem' := by
          rintro _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
          exact ⟨b + b', by rw [uSL_mul]; simp⟩
        one_mem' := ⟨0, uSL_zero.symm⟩
        inv_mem' := by
          rintro _ ⟨b, rfl⟩
          exact ⟨-b, by rw [uSL_inv]; simp⟩ }
    have hZU : Z' ≤ Usl K := by
      rintro _ ⟨b, rfl⟩
      exact uSL_mem_Usl 0 b 0
    have hZc : ∀ z ∈ Z', ∀ u ∈ Usl K, z * u = u * z := by
      rintro _ ⟨b, rfl⟩ u hu
      obtain ⟨a', b', c', rfl⟩ := mem_Usl.mp hu
      rw [uSL_mul, uSL_mul]
      congr 1 <;> ring
    have hZcard : Nat.card Z' = Nat.card K := by
      have hinj : Function.Injective fun b : K => (⟨uSL 0 b 0, b, rfl⟩ : Z') := fun b b' h =>
        (uSL_injective (congrArg Subtype.val h)).2.1
      exact (Nat.card_eq_of_bijective _ ⟨hinj, fun ⟨_, b, hb⟩ => ⟨b, Subtype.ext hb.symm⟩⟩).symm
    obtain ⟨Z₀, hZ₀P, hZ₀c, hZ₀card, hPcard⟩ := exists_central_of_conj ψ hψ hP' hZU hZc
  · exact ⟨Z₀, hZ₀P, hZ₀c, by rw [hZ₀card, hZcard, hK]⟩
  · rw [hPcard, card_Usl, hK]
    calc 2 ^ n < (2 ^ n) ^ 2 := by nlinarith
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_right (by positivity) (by norm_num)

theorem natFacts_sp4 {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {π : ↥(StatedSp 2 K) →* ↥H}
    (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ ⊥ π) {P : Subgroup (MulAut W)}
    (hP : QuasithinUnique.IsSylowTwoOf P H) : NatFactsW H P n := by
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hcardW : Nat.card W = (2 ^ n) ^ 4 := by
    rw [Nat.card_eq_of_bijective f ⟨Ch11.SecO1.IsCoord.injective_of_bot hf, hf.surj⟩,
      Nat.card_fun, hK, Nat.card_eq_fintype_card]
    rfl
  refine ⟨fun U hU => ?_, hcardW.le, ?_, ?_, ?_⟩
  · obtain ⟨d, hd⟩ := card_eq_pow_of_endStableW hW hf
      (fun T hT => commutant_statedSp T hT) hU
    exact ⟨d, hK ▸ hd⟩
  · rw [← Finite.one_lt_card_iff_nontrivial, hcardW]
    exact Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
  all_goals obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  all_goals
    let ψ : ↥(StatedSp 2 K) →* MulAut W :=
      (H.subtype.comp π).comp (MulAut.conj g).toMonoidHom
    have hψ : Function.Injective ψ := (Subtype.val_injective.comp hf.injective_nat).comp
      (MulAut.conj g).injective
    have hP' : ∀ x, x ∈ P ↔ ∃ u ∈ Usp K, x = ψ u := fun x => by
      rw [hg x]
      rfl
    let Z' : Subgroup ↥(StatedSp 2 K) :=
      { carrier := {x | ∃ a : K, x = qSp a 0 0}
        mul_mem' := by
          rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
          exact ⟨a + b, by rw [qSp_mul]; simp⟩
        one_mem' := ⟨0, qSp_zero.symm⟩
        inv_mem' := by
          rintro _ ⟨a, rfl⟩
          exact ⟨-a, by rw [qSp_inv]; simp⟩ }
    have hZU : Z' ≤ Usp K := by
      rintro _ ⟨a, rfl⟩
      exact ⟨a, 0, 0, 0, by rw [nSp_zero, mul_one]⟩
    have hZc : ∀ z ∈ Z', ∀ u ∈ Usp K, z * u = u * z := by
      rintro _ ⟨a, rfl⟩ u ⟨x, y, z, r, rfl⟩
      have hn : nSp r * qSp a 0 0 = qSp a 0 0 * nSp r := by
        have h := nSp_conj_qSp r a 0 0
        simp only [mul_zero, add_zero] at h
        calc nSp r * qSp a 0 0 = (nSp r * qSp a 0 0 * (nSp r)⁻¹) * nSp r := by group
          _ = qSp a 0 0 * nSp r := by rw [h]
      rw [← mul_assoc, qSp_comm, mul_assoc, ← hn, mul_assoc]
    have hZcard : Nat.card Z' = Nat.card K := by
      have hinj : Function.Injective fun a : K => (⟨qSp a 0 0, a, rfl⟩ : Z') := fun a a' h =>
        (qSp_injective (congrArg Subtype.val h)).1
      exact (Nat.card_eq_of_bijective _ ⟨hinj, fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha.symm⟩⟩).symm
    obtain ⟨Z₀, hZ₀P, hZ₀c, hZ₀card, hPcard⟩ := exists_central_of_conj ψ hψ hP' hZU hZc
  · exact ⟨Z₀, hZ₀P, hZ₀c, by rw [hZ₀card, hZcard, hK]⟩
  · rw [hPcard, card_Usp, hK]
    have hq : 2 ≤ 2 ^ n := le_self_pow₀ (by norm_num) (by omega)
    calc 2 ^ n < (2 ^ n) ^ 2 := by nlinarith
      _ ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_right (by positivity) (by norm_num)

end CFSG.Quasithin.Vol2.Ch11.O10
