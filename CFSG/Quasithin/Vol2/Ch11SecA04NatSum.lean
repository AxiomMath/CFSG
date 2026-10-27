module

public import CFSG.Quasithin.Vol2.Ch11SecANat2
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)
open scoped Matrix IsMulCommutative

section Model

variable {V : Type*} [CommGroup V] {d : ℕ} {K : Type} [Field K] {H : Subgroup (MulAut V)}
  {π : ↥(StatedSL d K) →* ↥H}

theorem exists_natEquiv (hR : (FFModel.nat (StatedSL d K)).RealizesVia H ⊤ ⊥ π) :
    ∃ θ : V ≃* Multiplicative (Fin d → K), ∀ (γ : ↥(StatedSL d K)) (v : V),
      θ (((π γ : ↥H) : MulAut V) v) = Multiplicative.ofAdd
        (((γ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ Multiplicative.toAdd (θ v)) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβc⟩ := hR
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have := (hβk u).mp hu
    rw [Subgroup.mem_bot] at this ⊢
    exact Subtype.ext this
  obtain ⟨q, hq⟩ : ∃ q : ↥(FFModel.nat (StatedSL d K)).sec ⧸
      (FFModel.nat (StatedSL d K)).ker.subgroupOf (FFModel.nat (StatedSL d K)).sec ≃*
        Multiplicative (Fin d → K), ∀ m, q (QuotientGroup.mk m) = m.1 :=
    ⟨((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      QuotientGroup.quotientBot).trans Subgroup.topEquiv, fun _ => rfl⟩
  refine ⟨((Subgroup.topEquiv (G := V)).symm.trans
    (MulEquiv.ofBijective β ⟨hβi, hβs⟩)).trans q, fun γ v => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨v, trivial⟩)
  have h1 : β ⟨((π γ : ↥H) : MulAut V) v, trivial⟩ =
      QuotientGroup.mk ⟨(FFModel.nat (StatedSL d K)).act γ m.1, trivial⟩ :=
    hβc γ ⟨v, trivial⟩ m trivial trivial hm.symm
  have e1 : (((Subgroup.topEquiv (G := V)).symm.trans (MulEquiv.ofBijective β ⟨hβi, hβs⟩)).trans
      q) (((π γ : ↥H) : MulAut V) v) = q (β ⟨((π γ : ↥H) : MulAut V) v, trivial⟩) := rfl
  have e2 : (((Subgroup.topEquiv (G := V)).symm.trans (MulEquiv.ofBijective β ⟨hβi, hβs⟩)).trans
      q) v = q (β ⟨v, trivial⟩) := rfl
  rw [e1, e2, h1, ← hm, hq, hq]
  rfl

theorem injective_of_realizesVia_nat (hR : (FFModel.nat (StatedSL d K)).RealizesVia H ⊤ ⊥ π) :
    Function.Injective π := by
  obtain ⟨θ, hθ⟩ := exists_natEquiv hR
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro γ hγ
  rw [Subgroup.mem_bot]
  have hfix : ∀ x : Fin d → K,
      ((γ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ x = x := by
    intro x
    obtain ⟨v, hv⟩ := θ.surjective (Multiplicative.ofAdd x)
    have h1 := hθ γ v
    rw [MonoidHom.mem_ker.mp hγ, Subgroup.coe_one, MulAut.one_apply, hv] at h1
    exact (Multiplicative.ofAdd.injective h1).symm
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h2 := congrFun (hfix (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at h2
  simpa [Matrix.col, Matrix.one_apply, Pi.single_apply, eq_comm] using h2

end Model

variable {G : Type} [Group G]

@[expose] def NatOn (L W : Subgroup G) (K : Type) [Field K]
    (φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)) : Prop :=
  ∃ θ : ↥W ≃* Multiplicative (Fin 3 → K), ∀ (l : ↥L) (w : ↥W)
    (hw : (l : G) * (w : G) * (l : G)⁻¹ ∈ W),
    θ ⟨_, hw⟩ = Multiplicative.ofAdd
      ((((φ (QuotientGroup.mk l) : ↥(StatedSL 3 K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (θ w))

variable [Finite G]

theorem natOn_of_realizesVia {L W : Subgroup G} [IsMulCommutative ↥W]
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) {K : Type} [Field K] [Finite K]
    {π : ↥(StatedSL 3 K) →* ↥(autOn L W)}
    (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia (V := ↥W) (autOn L W) ⊤ ⊥ π)
    (hO : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card ↥(StatedSL 3 K)) :
    ∃ φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K), NatOn L W K φ := by
  set πe := MulEquiv.ofBijective π ⟨injective_of_realizesVia_nat hπ, hπ.1⟩ with hπe
  set ρ : ↥L →* ↥(autOn L W) := (MulEquiv.subgroupCongr (range_conjHomL W L hLW)).toMonoidHom.comp
    (conjHomL W L hLW).rangeRestrict with hρ
  have hρs : Function.Surjective ρ :=
    (MulEquiv.subgroupCongr (range_conjHomL W L hLW)).surjective.comp
      (conjHomL W L hLW).rangeRestrict_surjective
  have hρc : ∀ l : ↥L, ((ρ l : ↥(autOn L W)) : MulAut ↥W) = conjV W l (hLW l.2) := fun _ => rfl
  have hle : CFSG.pCore 2 ↥L ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hρc]
    ext w
    rw [conjV_apply_coe]
    have hxC : (x : G) ∈ Subgroup.centralizer (W : Set G) := by
      apply hO
      refine ⟨x, ?_, rfl⟩
      exact hx
    rw [← Subgroup.mem_centralizer_iff.mp hxC w w.2, mul_inv_cancel_right]
    rfl
  set ν := QuotientGroup.lift (CFSG.pCore 2 ↥L) ρ hle with hν
  have hνs : Function.Surjective ν := by
    intro y
    obtain ⟨l, rfl⟩ := hρs y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hνb : Function.Bijective ν :=
    (Nat.bijective_iff_surjective_and_card ν).mpr ⟨hνs, hcard.trans (Nat.card_congr πe.toEquiv)⟩
  set φ := (MulEquiv.ofBijective ν hνb).trans πe.symm with hφ
  obtain ⟨θ, hθ⟩ := exists_natEquiv hπ
  refine ⟨φ, θ, fun l w hw => ?_⟩
  have h1 : π (φ (QuotientGroup.mk l)) = ρ l := by
    have : πe (φ (QuotientGroup.mk l)) = ν (QuotientGroup.mk l) := by
      rw [hφ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
    exact this
  have h2 := hθ (φ (QuotientGroup.mk l)) w
  rw [h1, hρc] at h2
  rw [← h2]
  exact congrArg θ (Subtype.ext (conjV_apply_coe W _ w).symm)

omit [Finite G] in
theorem natOn_of_equiv {L W₁ W₂ : Subgroup G} (hLW₁ : L ≤ Subgroup.normalizer (W₁ : Set G))
    {K : Type} [Field K] {φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)} (h : NatOn L W₁ K φ)
    (e : ↥W₁ ≃* ↥W₂)
    (he : ∀ (l : ↥L) (w : ↥W₁) (hw : (l : G) * (w : G) * (l : G)⁻¹ ∈ W₁),
      ((e ⟨_, hw⟩ : ↥W₂) : G) = (l : G) * (e w : G) * (l : G)⁻¹) :
    NatOn L W₂ K φ := by
  obtain ⟨θ, hθ⟩ := h
  refine ⟨e.symm.trans θ, fun l w hw => ?_⟩
  set w₁ := e.symm w with hw₁def
  have hw₁ : (l : G) * (w₁ : G) * (l : G)⁻¹ ∈ W₁ :=
    (Subgroup.mem_normalizer_iff.mp (hLW₁ l.2) _).mp w₁.2
  have key : e.symm ⟨_, hw⟩ = ⟨_, hw₁⟩ := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [he l w₁ hw₁, show e w₁ = w from e.apply_symm_apply w]
  rw [MulEquiv.trans_apply, key, hθ]
  rfl

omit [Finite G] in
theorem exists_equiv_of_isXSectionIso₂ {X A B : Subgroup G}
    (hXB : X ≤ Subgroup.normalizer (B : Set G)) (h : IsXSectionIso₂ X A ⊥ B ⊥) :
    ∃ e : ↥A ≃* ↥B, ∀ x ∈ X, ∀ (a : ↥A) (ha : x * (a : G) * x⁻¹ ∈ A),
      ((e ⟨_, ha⟩ : ↥B) : G) = x * (e a : G) * x⁻¹ := by
  obtain ⟨hnA, hnB, e, he⟩ := h
  obtain ⟨qA, hqA⟩ : ∃ q : ↥A ⧸ (⊥ : Subgroup G).subgroupOf A ≃* ↥A,
      ∀ a : ↥A, q (a : ↥A ⧸ (⊥ : Subgroup G).subgroupOf A) = a :=
    ⟨(QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf A)).trans
      QuotientGroup.quotientBot, fun _ => rfl⟩
  obtain ⟨qB, hqB⟩ : ∃ q : ↥B ⧸ (⊥ : Subgroup G).subgroupOf B ≃* ↥B,
      ∀ b : ↥B, q (b : ↥B ⧸ (⊥ : Subgroup G).subgroupOf B) = b :=
    ⟨(QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf B)).trans
      QuotientGroup.quotientBot, fun _ => rfl⟩
  have hqA' : ∀ a : ↥A, qA.symm a = (a : ↥A ⧸ (⊥ : Subgroup G).subgroupOf A) := fun a =>
    qA.symm_apply_eq.mpr (hqA a).symm
  have hqB' : ∀ y, (qB.symm (qB y)) = y := fun y => qB.symm_apply_apply y
  refine ⟨(qA.symm.trans e).trans qB, fun x hx a ha => ?_⟩
  set b := ((qA.symm.trans e).trans qB) a with hb
  have hbB : x * (b : G) * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hXB hx) _).mp b.2
  have h1 : e (a : ↥A ⧸ (⊥ : Subgroup G).subgroupOf A) =
      (b : ↥B ⧸ (⊥ : Subgroup G).subgroupOf B) := by
    rw [hb, MulEquiv.trans_apply, MulEquiv.trans_apply, hqA']
    apply qB.injective
    rw [hqB]
  have h2 := he x hx a b ha hbB h1
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hqA', h2, hqB]

end CFSG.Quasithin.Vol2.Ch11.SecA
