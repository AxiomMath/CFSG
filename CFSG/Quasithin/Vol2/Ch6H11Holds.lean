module

public import CFSG.Quasithin.Vol2.Ch6H11Main
public import CFSG.Quasithin.Vol2.Ch9H11Holds
public import CFSG.Quasithin.Vol2.Ch6Inputs

public section

noncomputable section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin (fixV mem_fixV rk rkIdx IsElemAbelian2 frobPow hermSub)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂)
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix

namespace H11M

open CFSG.Quasithin.H13.H11P (Mat)

variable {F : Type} [Field F] [CharP F 2] {a : ℕ}

theorem act_eq_rhoH (hσ : SigInv a F) (γ : ↥(StatedSL 2 F)) (m : VH a F) :
    (FFModel.twistTensor a (StatedSL 2 F)).act γ (m : Multiplicative (Mat F)) =
      ((rhoH hσ (H11P.slE F γ) m : VH a F) : Multiplicative (Mat F)) := by
  show Multiplicative.ofAdd ((((γ : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Mat F) * hm m *
    (frobPow a (((γ : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Mat F))ᵀ) =
    Multiplicative.ofAdd (((H11P.slE F γ : SL₂ F) : Mat F) * hm m *
      (frobPow a ((H11P.slE F γ : SL₂ F) : Mat F))ᵀ)
  rw [H11P.coe_slE]

theorem exists_modelH_equiv {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (hσ : SigInv a F) (h : (FFModel.twistTensor a (StatedSL 2 F)).Realizes L ⊤ ⊥) :
    ∃ e : V ≃* VH a F, L.map (MulAut.congr e).toMonoidHom = LH hσ := by
  obtain ⟨π, hπs, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let q : ↥(hermSub a (Fin 2) F) ⧸ (⊥ : Subgroup (Multiplicative (Mat F))).subgroupOf
      (hermSub a (Fin 2) F) ≃* VH a F :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      QuotientGroup.quotientBot
  let e : V ≃* VH a F :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective β ⟨hβi, hβs⟩)).trans q
  have hqs : ∀ x, x = (QuotientGroup.mk (q x) : ↥(hermSub a (Fin 2) F) ⧸
      (⊥ : Subgroup (Multiplicative (Mat F))).subgroupOf (hermSub a (Fin 2) F)) := fun x => by
    induction x using QuotientGroup.induction_on with
    | H m => rfl
  have he : ∀ (γ : ↥(StatedSL 2 F)) (v : V),
      e (((π γ : ↥L) : MulAut V) v) = rhoH hσ (H11P.slE F γ) (e v) := by
    intro γ v
    have h1 : β ⟨v, trivial⟩ = QuotientGroup.mk (e v) := hqs _
    have h2 := hβe γ ⟨v, trivial⟩ (e v) trivial (hsec γ _ (e v).2) h1
    have h3 := congrArg q h2
    refine h3.trans (Subtype.ext ?_)
    exact act_eq_rhoH hσ γ (e v)
  refine ⟨e, ?_⟩
  have hpair : ∀ γ : ↥(StatedSL 2 F),
      (MulAut.congr e) ((π γ : ↥L) : MulAut V) = rhoH hσ (H11P.slE F γ) := by
    intro γ
    refine MulEquiv.ext fun w => ?_
    rw [MulAut.congr_apply]
    show e (((π γ : ↥L) : MulAut V) (e.symm w)) = rhoH hσ (H11P.slE F γ) w
    rw [he, MulEquiv.apply_symm_apply]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    have hx' : ((π γ : ↥L) : MulAut V) = x := by rw [hγ]
    exact ⟨H11P.slE F γ, by rw [← hpair γ, hx']; rfl⟩
  · rintro ⟨g, rfl⟩
    refine ⟨_, (π ((H11P.slE F).symm g)).2, ?_⟩
    show (MulAut.congr e) ((π ((H11P.slE F).symm g) : ↥L) : MulAut V) = rhoH hσ g
    rw [hpair]
    simp

end H11M

open H11M in
theorem ch6InH11_holds : Ch6InH11 := by
  intro V _ _ L M a _hV2 ha _hLM hMN hO A hAM hA1 hA
  obtain ⟨F, _, _, _, hF, hreal⟩ := hO
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ (2 * a) := by rw [← Nat.card_eq_fintype_card, hF]
  have hσ : SigInv a F := fun x => JonesParshall.sig_sig hFc x
  obtain ⟨e, he⟩ := exists_modelH_equiv hσ hreal
  set Φ := MulAut.congr e with hΦ
  set A' := A.map Φ.toMonoidHom with hA'
  have hA'N : A' ≤ NH hσ := by
    have h1 : (Subgroup.normalizer (L : Set (MulAut V))).map Φ.toMonoidHom = NH hσ := by
      rw [Subgroup.map_equiv_normalizer_eq, he]
    rw [← h1]
    exact Subgroup.map_mono (hAM.trans hMN)
  have hA'1 : A' ≠ ⊥ := fun h =>
    hA1 ((Subgroup.map_eq_bot_iff_of_injective _ Φ.injective).mp h)
  have hA'e : IsElemAbelian2 A' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hA.1 x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hA.2 x hx, map_one]
  obtain ⟨c1, c2, c3⟩ := h11_modelH hσ ha hFc hA'N hA'1 hA'e
  have hrk : rk A' = rk A := by
    unfold rk
    rw [Subgroup.card_map_of_injective Φ.injective]
  have hidx : ∀ B : Subgroup (MulAut V),
      rkIdx (fixV (B.map Φ.toMonoidHom)) = rkIdx (fixV B) := by
    intro B
    unfold rkIdx
    rw [H11P.fixV_map_congr, Subgroup.index_map_of_bijective e.bijective]
  rw [hrk, hidx] at c1 c2 c3
  refine ⟨c1, ?_, fun hAL => c3 ?_⟩
  · rcases c2 with c2 | ⟨ha2, t, ht, htc⟩
    · exact Or.inl c2
    · obtain ⟨x, hx, rfl⟩ := ht
      refine Or.inr ⟨ha2, x, hx, ?_⟩
      rw [← hidx (Subgroup.zpowers x), MonoidHom.map_zpowers]
      exact htc
  · rw [← he]
    exact Subgroup.map_mono hAL

end CFSG.Quasithin.H13

end
