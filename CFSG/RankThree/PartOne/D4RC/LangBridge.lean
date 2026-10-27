module

public import CFSG.RankThree.PartOne.D4RC.Model
public import CFSG.RankThree.PartOne.D4RC.Class
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.KGD
  CFSG.SeitzReduction
open CFSG.RankThree.PartOne.Census3 (IsoLie)


section Frame

variable {X : Type} [Field X]

theorem rcg_pinnedX_highRoot [CharP X 2] (c : X) :
    pinnedX d4 X (highRoot d4) c = ((xd 22 c : adjointGroup d4 X) : ModGL d4 X) := by
  have hroot : IsRoot d4 (d4Root 22) := isRoot_d4 (by norm_num)
  have e : highRoot d4 = d4Root 22 := by decide +kernel
  have hs : (((rootOperatorFamily d4).pinnedFamilySign (d4Root 22) : ℤ) : X) = 1 := by
    rcases (rootOperatorFamily d4).pinnedFamilySign_eq (d4Root 22) with h | h <;> rw [h] <;>
      simp [CharTwo.neg_eq]
  rw [e, (rootOperatorFamily d4).pinnedX_eq_eltUnit X hroot c, hs, one_mul]
  show _ = ((xPar (rootOperatorFamily d4) (d4Root 22) c : adjointGroup d4 X) : ModGL d4 X)
  rw [xPar_of_isRoot hroot]
  exact ((rootOperatorFamily d4).coe_eltElement _ _).symm

theorem rcg_exists_of_pow_eq {L : Type} [Field L] [Finite X] [Algebra X L] (ρ : X →+* X) {q : ℕ}
    (hρ : ∀ c, ρ c = c ^ q) (hF : Nat.card (fixedField ρ) = q) {c : L} (hc : c ^ q = c) :
    ∃ c₀ : X, ρ c₀ = c₀ ∧ algebraMap X L c₀ = c := by
  classical
  have : Finite (fixedField ρ) := Subtype.finite
  have : Fintype (fixedField ρ) := Fintype.ofFinite _
  have hq2 : 1 < q := by
    rw [← hF]
    exact Finite.one_lt_card
  set S : Finset L := Finset.univ.image fun a : fixedField ρ => algebraMap X L (a : X) with hS
  have hinj : Function.Injective fun a : fixedField ρ => algebraMap X L (a : X) :=
    fun a b h => Subtype.ext ((algebraMap X L).injective h)
  have hSc : S.card = q := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card,
      hF]
  set P : Polynomial L := Polynomial.X ^ q - Polynomial.X with hP
  have hPdeg : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq L hq2
  have hP0 : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by rw [hPdeg]; omega)
  have hroot : ∀ y : L, y ^ q = y → y ∈ P.roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp only [hP, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hy, sub_self]
  have hsub : S ⊆ P.roots.toFinset := by
    intro y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
    refine hroot _ ?_
    have ha : ρ (a : X) = a := a.2
    rw [← map_pow, ← hρ, ha]
  have hle : P.roots.toFinset.card ≤ S.card :=
    calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = S.card := by rw [hPdeg, hSc]
  have hcmem : c ∈ S := by
    rw [Finset.eq_of_subset_of_card_le hsub hle]
    exact hroot c hc
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hcmem
  exact ⟨a, a.2, ha⟩

theorem rcg_triEmb_Xh_iff [CharP X 2] [Finite X] (σ : X ≃+* X) (hσ : ∀ c, σ (σ (σ c)) = c)
    {q : ℕ} (hσq : ∀ c, σ c = c ^ q) (hF : Nat.card (fixedField σ.toRingHom) = q)
    {G : Type} [Group G] (e₀ : G ≃* graphFixedRootGroup TwistTag.D4 X σ.toRingHom)
    (e : G ≃* twistedGroup σ.toRingHom)
    (hcompat : ∀ k, (((e k : twistedGroup σ.toRingHom) : adjointGroup d4 X) : ModGL d4 X) =
      ((e₀ k : graphFixedRootGroup TwistTag.D4 X σ.toRingHom) : ModGL d4 X))
    {L : Type} [Field L] [Algebra X L] (v : ModGL d4 L) :
    (∃ a : G, a ∈ (Xh σ.toRingHom).map e.symm.toMonoidHom ∧ triEmb X σ L (e₀ a) = v) ↔
      ∃ c : L, c ^ q = c ∧ v = pinnedX d4 L (highRoot d4) c := by
  have hσ' : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hσ
  have key : ∀ (c₀ : X) (hc₀ : σ.toRingHom c₀ = c₀) (a : G), e a = xHg hσ' c₀ hc₀ →
      triEmb X σ L (e₀ a) = pinnedX d4 L (highRoot d4) (algebraMap X L c₀) := by
    intro c₀ hc₀ a ha
    have h1 := hcompat a
    rw [ha] at h1
    have h2 : triEmb X σ L (e₀ a) =
        baseChangeGL (algebraMap X L) ((e₀ a : graphFixedRootGroup TwistTag.D4 X σ.toRingHom) :
          ModGL d4 X) := rfl
    rw [h2, ← h1]
    have h3 : (((xHg hσ' c₀ hc₀ : twistedGroup σ.toRingHom) : adjointGroup d4 X) : ModGL d4 X) =
        pinnedX d4 X (highRoot d4) c₀ := (rcg_pinnedX_highRoot c₀).symm
    rw [h3, baseChangeGL_pinnedX]
  constructor
  · rintro ⟨a, ⟨x, hx, rfl⟩, hv⟩
    obtain ⟨c₀, hc₀, hxc⟩ := (mem_Xh_iff hσ' x).1 hx
    have hx' : x = xHg hσ' c₀ hc₀ := Subtype.ext hxc
    subst hx'
    refine ⟨algebraMap X L c₀, ?_, ?_⟩
    · rw [← map_pow]
      have : c₀ ^ q = c₀ := by rw [← hσq]; exact hc₀
      rw [this]
    · exact hv.symm.trans (key c₀ hc₀ _ (e.apply_symm_apply _))
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨c₀, hc₀, rfl⟩ := rcg_exists_of_pow_eq σ.toRingHom hσq hF hc
    refine ⟨e.symm (xHg hσ' c₀ hc₀), ⟨_, xHg_mem hσ' c₀ hc₀, rfl⟩, ?_⟩
    exact key c₀ hc₀ _ (e.apply_symm_apply _)

end Frame

theorem rcg_exists_model_equiv {q : TauCeti.PrimePower} (hq : q.p = 2) {G : Type}
    [Group G] [Finite G] (hiso : IsoLie G (.trialityD4 q)) :
    ∃ (X : Type) (_ : Field X) (_ : Finite X) (σ : X ≃+* X) (_ : CharP X 2)
      (e₀ : G ≃* graphFixedRootGroup TwistTag.D4 X σ.toRingHom)
      (e : G ≃* twistedGroup σ.toRingHom),
      (∀ c, σ (σ (σ c)) = c) ∧ (∀ c, σ c = c ^ q.card) ∧ Nat.card X = q.card ^ 3 ∧
      Nat.card (fixedField σ.toRingHom) = q.card ∧
      (∀ k, (((e k : twistedGroup σ.toRingHom) : adjointGroup d4 X) : ModGL d4 X) =
        ((e₀ k : graphFixedRootGroup TwistTag.D4 X σ.toRingHom) : ModGL d4 X)) ∧
      Nat.card (twistedGroup σ.toRingHom) = d4Order q.exponent := by
  obtain ⟨X, hXf, hXfin, σ', hchar, e₀, e, hσ3, hσq, hcard, hF, -, hcompat, hord⟩ :=
    rcg_exists_model hq hiso
  exact ⟨X, hXf, hXfin,
    RingEquiv.ofBijective σ' ⟨σ'.injective, Finite.surjective_of_injective σ'.injective⟩,
    hchar, e₀, e, hσ3, hσq, hcard, hF, hcompat, hord⟩

end CFSG.RankThree.PartOne.D4RC
