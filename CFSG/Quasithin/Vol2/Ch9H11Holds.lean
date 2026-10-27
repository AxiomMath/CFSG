module

public import CFSG.Quasithin.Vol2.Ch9H11Main
public import CFSG.Quasithin.Vol2.Ch9Inputs

public section

noncomputable section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin (fixV mem_fixV rk rkIdx IsElemAbelian2)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂)
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)
open scoped Matrix

namespace H11P

variable {K : Type} [Field K]

abbrev slE (K : Type) [Field K] : ↥(StatedSL 2 K) ≃* SL₂ K :=
  (specialLinearGroupEquivStatedSL 2 K).symm

theorem coe_slE (g : ↥(StatedSL 2 K)) :
    ((slE K g : SL₂ K) : Mat K) = (((g : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Mat K) := by
  conv_rhs => rw [← (specialLinearGroupEquivStatedSL 2 K).apply_symm_apply g]
  rfl

theorem act_eq_rho (γ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) (m : VM K) :
    (tensorPairModel (StatedSL 2 K) (StatedSL 2 K)).act γ m = rho (slE K γ.1, slE K γ.2) m := by
  show Multiplicative.ofAdd ((((γ.1 : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Mat K) *
    Multiplicative.toAdd m * (((γ.2 : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Mat K)ᵀ) =
    Multiplicative.ofAdd (((slE K γ.1 : SL₂ K) : Mat K) * Multiplicative.toAdd m *
      ((slE K γ.2 : SL₂ K) : Mat K)ᵀ)
  rw [coe_slE, coe_slE]

theorem exists_model_equiv {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (h : (tensorPairModel (StatedSL 2 K) (StatedSL 2 K)).RealizesMod (V := V) L) :
    ∃ e : V ≃* VM K, L.map (MulAut.congr e).toMonoidHom = Lm K := by
  obtain ⟨π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let q : ↥(⊤ : Subgroup (VM K)) ⧸ (⊥ : Subgroup (VM K)).subgroupOf (⊤ : Subgroup (VM K)) ≃*
      VM K :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  let e : V ≃* VM K :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective β ⟨hβi, hβs⟩)).trans q
  have hqs : ∀ x, x = (QuotientGroup.mk ⟨q x, trivial⟩ : ↥(⊤ : Subgroup (VM K)) ⧸
      (⊥ : Subgroup (VM K)).subgroupOf (⊤ : Subgroup (VM K))) := fun x => by
    induction x using QuotientGroup.induction_on with
    | H m => rfl
  have he : ∀ (γ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) (v : V),
      e (((π γ : ↥L) : MulAut V) v) = rho (slE K γ.1, slE K γ.2) (e v) := by
    intro γ v
    have h1 : β ⟨v, trivial⟩ = QuotientGroup.mk ⟨e v, trivial⟩ := hqs _
    have h2 := hβe γ ⟨v, trivial⟩ ⟨e v, trivial⟩ trivial trivial h1
    have h3 := congrArg q h2
    rw [← act_eq_rho]
    exact h3
  refine ⟨e, ?_⟩
  have hpair : ∀ γ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K),
      (MulAut.congr e) ((π γ : ↥L) : MulAut V) = rho (slE K γ.1, slE K γ.2) := by
    intro γ
    refine MulEquiv.ext fun w => ?_
    rw [MulAut.congr_apply]
    show e (((π γ : ↥L) : MulAut V) (e.symm w)) = rho (slE K γ.1, slE K γ.2) w
    rw [he, MulEquiv.apply_symm_apply]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    have hx' : ((π γ : ↥L) : MulAut V) = x := by rw [hγ]
    exact ⟨(slE K γ.1, slE K γ.2), by rw [← hpair γ, hx']; rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨_, (π ((slE K).symm p.1, (slE K).symm p.2)).2, ?_⟩
    show (MulAut.congr e) ((π ((slE K).symm p.1, (slE K).symm p.2) : ↥L) : MulAut V) = rho p
    rw [hpair]
    simp

theorem fixV_map_congr {V W : Type} [CommGroup V] [CommGroup W] (e : V ≃* W)
    (A : Subgroup (MulAut V)) :
    fixV (A.map (MulAut.congr e).toMonoidHom) = (fixV A).map e.toMonoidHom :=
  fixV_map_congr_equiv e A

end H11P

open H11P in
theorem ch9InH11Plus_holds : Ch9InH11Plus := by
  intro V _ _ L M n hV2 hn hLM hMN hK' A hAM hA1 hA
  obtain ⟨K, hF, hfin, hK, hreal⟩ := hK'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨e, he⟩ := exists_model_equiv hreal
  set Φ := MulAut.congr e with hΦ
  set A' := A.map Φ.toMonoidHom with hA'
  have hA'N : A' ≤ NLm K := by
    have h1 : (Subgroup.normalizer (L : Set (MulAut V))).map Φ.toMonoidHom = NLm K := by
      rw [Subgroup.map_equiv_normalizer_eq, he]
    rw [← h1]
    exact Subgroup.map_mono (hAM.trans hMN)
  have hA'1 : A' ≠ ⊥ := fun h =>
    hA1 ((Subgroup.map_eq_bot_iff_of_injective _ Φ.injective).mp h)
  have hA'e : IsElemAbelian2 A' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hA.1 a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hA.2 a ha, map_one]
  obtain ⟨c1, c2, c3⟩ := h11_model hn hK hA'N hA'1 hA'e
  have hrk : rk A' = rk A := by
    unfold rk
    rw [Subgroup.card_map_of_injective Φ.injective]
  have hidx : ∀ B : Subgroup (MulAut V),
      rkIdx (fixV (B.map Φ.toMonoidHom)) = rkIdx (fixV B) := by
    intro B
    unfold rkIdx
    rw [fixV_map_congr, Subgroup.index_map_of_bijective e.bijective]
  rw [hrk, hidx] at c1 c2 c3
  refine ⟨c1, ?_, fun hAL => c3 ?_⟩
  · rcases c2 with c2 | ⟨hn2, t, ht, htc⟩
    · exact Or.inl c2
    · obtain ⟨a, ha, rfl⟩ := ht
      refine Or.inr ⟨hn2, a, ha, ?_⟩
      rw [← hidx (Subgroup.zpowers a), MonoidHom.map_zpowers]
      exact htc
  · rw [← he]
    exact Subgroup.map_mono hAL

end CFSG.Quasithin.H13

end
