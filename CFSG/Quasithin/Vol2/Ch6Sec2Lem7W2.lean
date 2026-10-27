module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W1
public import CFSG.Quasithin.EmptyFaithful.R3c2Types

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {Q : Type} [CommGroup Q]

theorem mem_commV_zpowers627 (x : MulAut Q) (u : Q) :
    x u * u⁻¹ ∈ commV (Subgroup.zpowers x) :=
  Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, u, rfl⟩

theorem commV_mono627 {A B : Subgroup (MulAut Q)} (h : B ≤ A) : commV B ≤ commV A :=
  Subgroup.closure_mono fun _ ⟨x, hx, u, hu⟩ => ⟨x, h hx, u, hu⟩

theorem exists_mulVec_ne627 {d : ℕ} {K : Type} [Field K] {g : Matrix (Fin d) (Fin d) K}
    (hg : g ≠ 1) : ∃ v : Fin d → K, g.mulVec v ≠ v := by
  by_contra hcon
  push Not at hcon
  apply hg
  ext i j
  have := congrFun (hcon (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem natReal627 {d : ℕ} {K : Type} [Field K] {L : Subgroup (MulAut Q)} {U Z : Subgroup Q}
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin d) K)} {π : ↥Γ →* ↥L}
    (h : (FFModel.nat Γ).RealizesVia L U Z π) :
    Function.Surjective π ∧ (∀ y : ↥L, ∀ u ∈ U, (y : MulAut Q) u ∈ U) ∧
      ∃ β : ↥U →* Multiplicative (Fin d → K), Function.Surjective β ∧
        (∀ u, β u = 1 ↔ (u : Q) ∈ Z) ∧
        ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥L) : MulAut Q) (u : Q) ∈ U),
          Multiplicative.toAdd (β ⟨_, hu⟩) =
            ((γ : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec
              (Multiplicative.toAdd (β u)) := by
  obtain ⟨hs, -, -, hU, -, -, -, β, hβs, hβk, hβe⟩ := h
  let e : (↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec) ≃*
      Multiplicative (Fin d → K) :=
    ((QuotientGroup.quotientMulEquivOfEq (show (FFModel.nat Γ).ker.subgroupOf
        (FFModel.nat Γ).sec = ⊥ from Subgroup.bot_subgroupOf _)).trans
          QuotientGroup.quotientBot).trans Subgroup.topEquiv
  refine ⟨hs, hU, e.toMonoidHom.comp β, e.surjective.comp hβs, fun u => ?_, fun γ u hu => ?_⟩
  · show e (β u) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact hβk u
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have h1 := hβe γ u m hu (Subgroup.mem_top _) hm.symm
    refine (congrArg (fun y => Multiplicative.toAdd (e y)) h1).trans ?_
    show _ = ((γ : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec
      (Multiplicative.toAdd (e (β u)))
    rw [← hm]
    rfl

theorem card_le_commV_of_nat627 [Finite Q] {d : ℕ} {K : Type} [Field K] [Finite K]
    {L : Subgroup (MulAut Q)} {U Z : Subgroup Q}
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin d) K)} {π : ↥Γ →* ↥L}
    (h : (FFModel.nat Γ).RealizesVia L U Z π) {γ : ↥Γ} (hγ : γ ≠ 1) :
    Nat.card K ≤ Nat.card (commV (Subgroup.zpowers ((π γ : ↥L) : MulAut Q))) := by
  classical
  obtain ⟨-, hUinv, β, hβs, -, hβ⟩ := natReal627 h
  set x : MulAut Q := ((π γ : ↥L) : MulAut Q) with hx
  set g : Matrix (Fin d) (Fin d) K :=
    ((γ : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) with hg
  have hγm : g ≠ 1 := by
    intro h1
    apply hγ
    apply Subtype.ext
    apply Units.ext
    exact h1
  obtain ⟨v, hv⟩ := exists_mulVec_ne627 hγm
  set w : Fin d → K := g.mulVec v - v with hw
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hv
  choose u hu using fun c : K => hβs (Multiplicative.ofAdd (c • v))
  have hxu : ∀ c, x (u c : Q) ∈ U := fun c => hUinv (π γ) _ (u c).2
  set f : K → Q := fun c => x (u c : Q) * (u c : Q)⁻¹ with hf
  have hfU : ∀ c, f c ∈ U := fun c => U.mul_mem (hxu c) (U.inv_mem (u c).2)
  have hfmem : ∀ c, f c ∈ commV (Subgroup.zpowers x) := fun c => mem_commV_zpowers627 x _
  have hβf : ∀ c, Multiplicative.toAdd (β ⟨f c, hfU c⟩) = c • w := by
    intro c
    have e1 : (⟨f c, hfU c⟩ : ↥U) = ⟨x (u c : Q), hxu c⟩ * (u c)⁻¹ := rfl
    rw [e1, map_mul, map_inv, toAdd_mul, toAdd_inv, hβ γ (u c) (hxu c), hu c, toAdd_ofAdd,
      Matrix.mulVec_smul, hw, smul_sub]
    abel
  have hinj : Function.Injective fun c : K =>
      (⟨f c, hfmem c⟩ : ↥(commV (Subgroup.zpowers x))) := by
    intro c c' hcc
    have h1 : f c = f c' := congrArg Subtype.val hcc
    have h2 : c • w = c' • w := by
      rw [← hβf, ← hβf]
      congr 2
      exact Subtype.ext h1
    have h4 : (c - c') • w = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact sub_eq_zero.mp h5
    · exact absurd h5 hw0
  exact Nat.card_le_card_of_injective _ hinj

theorem pair_types627 [Finite Q] [Finite (MulAut Q)]
    (hK : KnownFacts15122Types)
    (hE : Vol2.Ch11.SecA.FactA318Excl) {L : Subgroup (MulAut Q)} {U Z : Subgroup Q}
    (hq : CFSG.IsQuasisimple ↥L) (hpair : B42ModulePair L U Z)
    (hexcl : A318Exclusion ↥L → False)
    (hhat : IsHat ↥L ↥(alternatingGroup (Fin 6)) → False) :
    (∃ n, BinaryNaturalSL L U Z 2 n) ∨ (∃ n, BinaryNaturalSL L U Z 3 n) ∨
      AlternatingNatural L U Z 5 := by
  classical
  rcases hpair with h2 | h3 | ⟨n, K, _, _, hKn, π, hπ⟩ | ⟨n, K, _, _, hKn, π, hπ⟩ |
    ⟨K, _, _, hK2, π, hπ⟩ | h5 | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨α, π, hπ⟩ |
    ⟨K, _, _, Γ₀, -, -, hhatΓ, -, π, hπ⟩ | h41 | h51 | ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exact Or.inl h2
  · exact Or.inr (Or.inl h3)
  ·
    exact (hexcl (R3c2.exclusion_sp4 hE hKn
      (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ).symm hq)).elim
  ·
    have := R3c.charP_two_of_natCard_eq_two_pow hKn
    exact (hexcl (R3c2.exclusion_g2 hE hKn
      (FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ).symm hq)).elim
  ·
    have hK2' : Nat.card K = 2 := by simpa using hK2
    have := R3c.charP_two_of_natCard_eq_two_pow hK2
    have hΓ : ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ ≤ CFSG.Open.quasithinG2 K := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact (CFSG.Open.quasithinG2 K).mul_mem
        ((CFSG.Open.quasithinG2 K).mul_mem ((CFSG.Open.quasithinG2 K).mul_mem ha hb)
          ((CFSG.Open.quasithinG2 K).inv_mem ha)) ((CFSG.Open.quasithinG2 K).inv_mem hb)
    exact (hexcl (R3c2.exclusion_g2Derived hK hK2'
      (FFC.equivOfRealizes (FFC.zornQ_faithful _ hΓ) hπ).symm)).elim
  · exact Or.inr (Or.inr h5)
  ·
    have : Finite (FFModel.altDn 6).Gam := (inferInstance : Finite ↥(alternatingGroup (Fin 6)))
    exact (hexcl (R3c2.exclusion_of_mulEquiv
      (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ) hK.alt6)).elim
  ·
    have : Finite (FFModel.altDn 7).Gam := (inferInstance : Finite ↥(alternatingGroup (Fin 7)))
    exact (hexcl (R3c2.exclusion_of_mulEquiv
      (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ) hK.alt7)).elim
  ·
    have : Finite (FFModel.a7Four α).Gam := (inferInstance : Finite ↥(alternatingGroup (Fin 7)))
    exact (hexcl (R3c2.exclusion_of_mulEquiv
      (FFC.equivOfRealizes (FFC.a7Four_faithful α) hπ) hK.alt7)).elim
  ·
    exact (hhat (IsHat.of_mulEquiv (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)
      hhatΓ)).elim
  ·
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h41
    exact (hexcl (hK.l42 _ (R3c2.isPSL_two_of_statedSL (by norm_num)
      (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ).symm))).elim
  ·
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h51
    exact (hexcl (hK.l52 _ (R3c2.isPSL_two_of_statedSL (by norm_num)
      (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ).symm))).elim
  ·
    exact (hexcl (hK.l42 _ (R3c2.isPSL_two_of_statedSL (by norm_num)
      (FFC.equivOfRealizes (FFC.extSq_faithful (by norm_num)) hπ).symm))).elim
  ·
    exact (hexcl (hK.l52 _ (R3c2.isPSL_two_of_statedSL (by norm_num)
      (FFC.equivOfRealizes (FFC.extSq_faithful (by norm_num)) hπ).symm))).elim

theorem pair_cases627 [Finite Q] [Finite (MulAut Q)]
    (hK : KnownFacts15122Types)
    (hE : Vol2.Ch11.SecA.FactA318Excl) {L A : Subgroup (MulAut Q)} {U Z : Subgroup Q}
    (hq : CFSG.IsQuasisimple ↥L) (hpair : B42ModulePair L U Z) (hAL : A ≤ L)
    (hA4 : Nat.card A = 4) (hfs : ∀ a ∈ A, Nat.card (commV (Subgroup.zpowers a)) ≤ 4)
    (hD5 : AlternatingNatural L U Z 5 → False) (hexcl : A318Exclusion ↥L → False)
    (hhat : IsHat ↥L ↥(alternatingGroup (Fin 6)) → False) :
    BinaryNaturalSL L U Z 2 2 ∨ BinaryNaturalSL L U Z 3 1 ∨ BinaryNaturalSL L U Z 3 2 := by
  classical
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : A = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hcon x hx)
    rw [this, Subgroup.card_bot] at hA4
    omega
  have hfield : ∀ {d : ℕ} {K : Type} [Field K] [Finite K] {π : ↥(StatedSL d K) →* ↥L},
      (FFModel.nat (StatedSL d K)).RealizesVia L U Z π → Nat.card K ≤ 4 := by
    intro d K _ _ π hπ
    obtain ⟨γ, hγ⟩ := hπ.1 ⟨a, hAL haA⟩
    have hγa : ((π γ : ↥L) : MulAut Q) = a := congrArg Subtype.val hγ
    have hγ1 : γ ≠ 1 := by
      intro h1
      apply ha1
      rw [← hγa, h1]
      exact congrArg Subtype.val (map_one π)
    have h1 := card_le_commV_of_nat627 hπ hγ1
    rw [hγa] at h1
    exact h1.trans (hfs a haA)
  have hpow : ∀ {n : ℕ}, 1 ≤ n → 2 ^ n ≤ 4 → n = 1 ∨ n = 2 := by
    intro n hn h4
    have : n ≤ 2 := by
      by_contra hcon
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  rcases pair_types627 hK hE hq hpair hexcl hhat with
    ⟨n, K, _, _, hKn, π, hπ⟩ | ⟨n, K, _, _, hKn, π, hπ⟩ | h5
  ·
    rcases hpow (one_le_of_card_eq_two_pow627 hKn) (hKn ▸ hfield hπ) with rfl | rfl
    · exfalso
      have e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
      refine SBc3.false_of_card_dvd_six hq ?_
      rw [← Nat.card_congr e.toEquiv]
      show Nat.card ↥(StatedSL 2 K) ∣ 6
      rw [R3c.card_statedSL_two_pow hKn]
      norm_num
    · exact Or.inl ⟨K, inferInstance, inferInstance, hKn, π, hπ⟩
  ·
    rcases hpow (one_le_of_card_eq_two_pow627 hKn) (hKn ▸ hfield hπ) with rfl | rfl
    · exact Or.inr (Or.inl ⟨K, inferInstance, inferInstance, hKn, π, hπ⟩)
    · exact Or.inr (Or.inr ⟨K, inferInstance, inferInstance, hKn, π, hπ⟩)
  · exact (hD5 h5).elim

end CFSG.Quasithin.H13
