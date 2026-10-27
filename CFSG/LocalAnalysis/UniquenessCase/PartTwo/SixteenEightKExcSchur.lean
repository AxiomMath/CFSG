module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open CFSG.QuasithinUnique.Setup.SL2Modules

private lemma s16k_two_nsmul {Q : Type} [CommGroup Q] (h2 : ∀ x : Q, x ^ 2 = 1) :
    ∀ x : Additive Q, (2 : ℕ) • x = 0 := fun x => by
  apply Additive.toMul.injective
  rw [two_nsmul, toMul_add, toMul_zero]
  simpa [pow_two] using h2 (Additive.toMul x)

private def s16kLinHom {Q : Type} [CommGroup Q] [Module (ZMod 2) (Additive Q)] :
    MulAut Q →* Module.End (ZMod 2) (Additive Q) where
  toFun c := (MonoidHom.toAdditive c.toMonoidHom).toZModLinearMap (n := 2)
  map_one' := by ext a; rfl
  map_mul' c d := by ext a; rfl

private def s16kRho {Q : Type} [CommGroup Q] [Module (ZMod 2) (Additive Q)]
    (L : Subgroup (MulAut Q)) : Representation (ZMod 2) L (Additive Q) :=
  s16kLinHom.comp L.subtype

private theorem s16k_isIrreducible {Q : Type} [CommGroup Q] [Finite Q] [Nontrivial Q]
    [Module (ZMod 2) (Additive Q)] {L : Subgroup (MulAut Q)}
    (hirr : ∀ B : Subgroup Q, (∀ l ∈ L, ∀ b ∈ B, l b ∈ B) → B = ⊥ ∨ B = ⊤) :
    (s16kRho L).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff]
  refine ⟨inferInstance, ?_⟩
  intro U hU
  let B : Subgroup Q :=
    { carrier := {b | Additive.ofMul b ∈ U}
      mul_mem' := fun {a b} ha hb => by
        show Additive.ofMul (a * b) ∈ U
        rw [ofMul_mul]
        exact U.add_mem ha hb
      one_mem' := by simpa using U.zero_mem
      inv_mem' := fun {a} ha => by
        show Additive.ofMul a⁻¹ ∈ U
        rw [ofMul_inv]
        exact U.neg_mem ha }
  have hB : ∀ l ∈ L, ∀ b ∈ B, l b ∈ B := by
    intro l hl b hb
    show Additive.ofMul (l b) ∈ U
    have := hU ⟨l, hl⟩ (Additive.ofMul b) hb
    simpa [s16kRho, s16kLinHom, MonoidHom.coe_toAdditive,
      AddMonoidHom.coe_toZModLinearMap] using this
  rcases hirr B hB with hB | hB
  · left
    rw [Submodule.eq_bot_iff]
    intro a ha
    have h1 : Additive.toMul a ∈ B := ha
    rw [hB, Subgroup.mem_bot] at h1
    exact Additive.toMul.injective h1
  · right
    rw [Submodule.eq_top_iff']
    intro a
    have h1 : Additive.toMul a ∈ B := by rw [hB]; trivial
    exact h1

private theorem s16kEnd_exists {Q : Type} [CommGroup Q] [Module (ZMod 2) (Additive Q)]
    {L : Subgroup (MulAut Q)}
    (c : ↥(Subgroup.centralizer (L : Set (MulAut Q)))) :
    ∃ ψ : EndRing (s16kRho L), (ψ : Additive Q → Additive Q) = s16kLinHom (c : MulAut Q) := by
  rw [mem_endRing_iff]
  intro g v
  have hcomm : (c : MulAut Q) * (g : MulAut Q) = (g : MulAut Q) * (c : MulAut Q) :=
    (Subgroup.mem_centralizer_iff.mp c.2 (g : MulAut Q) g.2).symm
  have h : s16kLinHom (c : MulAut Q) * s16kLinHom (g : MulAut Q) =
      s16kLinHom (g : MulAut Q) * s16kLinHom (c : MulAut Q) := by
    rw [← map_mul, ← map_mul, hcomm]
  exact congrArg (fun f : Module.End (ZMod 2) (Additive Q) => f v) h

private noncomputable def s16kEndOf {Q : Type} [CommGroup Q] [Module (ZMod 2) (Additive Q)]
    {L : Subgroup (MulAut Q)}
    (c : ↥(Subgroup.centralizer (L : Set (MulAut Q)))) : EndRing (s16kRho L) :=
  Classical.choose (s16kEnd_exists c)

private theorem s16kEndOf_spec {Q : Type} [CommGroup Q] [Module (ZMod 2) (Additive Q)]
    {L : Subgroup (MulAut Q)}
    (c : ↥(Subgroup.centralizer (L : Set (MulAut Q)))) :
    (s16kEndOf c : Additive Q → Additive Q) = s16kLinHom (c : MulAut Q) :=
  Classical.choose_spec (s16kEnd_exists c)

private noncomputable def s16kCentToEnd {Q : Type} [CommGroup Q] [Module (ZMod 2) (Additive Q)]
    (L : Subgroup (MulAut Q)) :
    ↥(Subgroup.centralizer (L : Set (MulAut Q))) →* EndRing (s16kRho L) where
  toFun c := s16kEndOf c
  map_one' := by
    apply LinearMap.ext
    intro v
    change (s16kEndOf 1) v = (1 : EndRing (s16kRho L)) v
    rw [s16kEndOf_spec]
    simp [s16kLinHom]
  map_mul' c d := by
    apply LinearMap.ext
    intro v
    change (s16kEndOf (c * d)) v = (s16kEndOf c * s16kEndOf d) v
    rw [s16kEndOf_spec]
    change (s16kLinHom ((c * d : ↥(Subgroup.centralizer (L : Set (MulAut Q)))) : MulAut Q)) v =
      (s16kEndOf c * s16kEndOf d) v
    simp only [Module.End.mul_apply]
    rw [s16kEndOf_spec, s16kEndOf_spec]
    rfl

private theorem s16kCentToEnd_injective {Q : Type} [CommGroup Q] [Module (ZMod 2) (Additive Q)]
    (L : Subgroup (MulAut Q)) : Function.Injective (s16kCentToEnd L) := by
  intro c d h
  have h1 : (s16kEndOf c : Additive Q → Additive Q) =
      (s16kEndOf d : Additive Q → Additive Q) :=
    congrArg (fun f : EndRing (s16kRho L) => (f : Additive Q → Additive Q)) h
  rw [s16kEndOf_spec, s16kEndOf_spec] at h1
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  have hx := congrArg (fun f : Additive Q → Additive Q => f (Additive.ofMul x)) h1
  have hy := congrArg Additive.toMul hx
  simpa [s16kLinHom, MonoidHom.coe_toAdditive,
    AddMonoidHom.coe_toZModLinearMap] using hy

theorem s16k_centralizer_isCyclic {Q : Type} [CommGroup Q] [Finite Q] (h2 : ∀ x : Q, x ^ 2 = 1)
    {L : Subgroup (MulAut Q)}
    (hirr : ∀ B : Subgroup Q, (∀ l ∈ L, ∀ b ∈ B, l b ∈ B) → B = ⊥ ∨ B = ⊤) :
    IsCyclic ↥(Subgroup.centralizer (L : Set (MulAut Q))) := by
  classical
  by_cases hQ1 : Subsingleton Q
  · haveI : Subsingleton Q := hQ1
    haveI : Subsingleton (MulAut Q) :=
      ⟨fun f g => MulEquiv.ext fun x => by simp [Subsingleton.elim x 1]⟩
    infer_instance
  · haveI : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hQ1
    letI : Module (ZMod 2) (Additive Q) :=
      AddCommGroup.zmodModule (s16k_two_nsmul h2)
    have hρ : (s16kRho L).IsIrreducible := s16k_isIrreducible hirr
    haveI : Fact (s16kRho L).IsIrreducible := ⟨hρ⟩
    exact isCyclic_of_injective_ringHom (R := EndRing (s16kRho L))
      (s16kCentToEnd L) (s16kCentToEnd_injective L)

theorem s16k_centralizer_card_dvd {Q : Type} [CommGroup Q] [Finite Q] (h2 : ∀ x : Q, x ^ 2 = 1)
    {L : Subgroup (MulAut Q)}
    (hirr : ∀ B : Subgroup Q, (∀ l ∈ L, ∀ b ∈ B, l b ∈ B) → B = ⊥ ∨ B = ⊤) {d : ℕ}
    (hQ : Nat.card Q = 2 ^ d) :
    ∃ e : ℕ, e ∣ d ∧ Nat.card ↥(Subgroup.centralizer (L : Set (MulAut Q))) ∣ 2 ^ e - 1 := by
  classical
  by_cases hQ1 : Subsingleton Q
  · haveI : Subsingleton Q := hQ1
    have h1 : Nat.card Q = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hQ1, inferInstance⟩
    have hd : d = 0 := by
      have h2d : 2 ^ d = 1 := by rw [← hQ, h1]
      rcases (pow_eq_one_iff).mp h2d with h | h
      · norm_num at h
      · exact h
    subst hd
    haveI : Subsingleton (MulAut Q) :=
      ⟨fun f g => MulEquiv.ext fun x => by simp [Subsingleton.elim x 1]⟩
    refine ⟨0, dvd_zero 0, ?_⟩
    haveI : Subsingleton ↥(Subgroup.centralizer (L : Set (MulAut Q))) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    simp
  · haveI : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hQ1
    letI : Module (ZMod 2) (Additive Q) :=
      AddCommGroup.zmodModule (s16k_two_nsmul h2)
    have hρ : (s16kRho L).IsIrreducible := s16k_isIrreducible hirr
    haveI : Fact (s16kRho L).IsIrreducible := ⟨hρ⟩
    let E := EndRing (s16kRho L)
    haveI : Field E := endRingField (s16kRho L)
    let e := Module.finrank (ZMod 2) E
    have hEcard : Nat.card E = 2 ^ e := by
      have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
      simpa [e, Nat.card_zmod] using this
    have hVcard : Nat.card (Additive Q) = Nat.card E ^ Module.finrank E (Additive Q) :=
      Module.natCard_eq_pow_finrank (K := E) (V := Additive Q)
    have hcardQ : Nat.card (Additive Q) = 2 ^ d := by
      rw [← hQ]
      exact Nat.card_congr (Additive.toMul : Additive Q ≃ Q)
    have hdvd : e ∣ d := by
      have h : 2 ^ d = 2 ^ (e * Module.finrank E (Additive Q)) := by
        rw [← hcardQ, hVcard, hEcard, ← pow_mul]
      exact Nat.pow_right_injective (le_refl 2) h ▸ dvd_mul_right e _
    refine ⟨e, hdvd, ?_⟩
    let f : ↥(Subgroup.centralizer (L : Set (MulAut Q))) →* E := s16kCentToEnd L
    have hf : Function.Injective f := s16kCentToEnd_injective L
    haveI : Finite E := finite_endRing (s16kRho L)
    let f' : ↥(Subgroup.centralizer (L : Set (MulAut Q))) →* Eˣ := f.toHomUnits
    have hf' : Function.Injective f' := by
      intro c d h
      apply hf
      change f c = f d
      simpa only [f', MonoidHom.coe_toHomUnits] using
        congrArg (fun u : Eˣ => (u : E)) h
    have hcard : Nat.card ↥(Subgroup.centralizer (L : Set (MulAut Q))) ∣ Nat.card Eˣ :=
      Subgroup.card_dvd_of_injective f' hf'
    have hEunits : Nat.card Eˣ = 2 ^ e - 1 := by
      rw [show Nat.card Eˣ = Nat.card E - 1 from
        @Nat.card_units E ((DivisionRing.toDivisionSemiring (K := E)).toGroupWithZero),
        hEcard]
    rw [hEunits] at hcard
    exact hcard

private theorem s16k_pRank_le_one_of_isCyclic {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hcyc : IsCyclic ↥H) (p : ℕ) (hp : p.Prime) : CFSG.Open.pRank p H ≤ 1 := by
  apply CFSG.GH74.Uniqueness.SU.SU1.pRank_le_of
  intro E hEH hEab k hk
  haveI : IsCyclic ↥E := Subgroup.isCyclic_of_le hEH
  have hexp : Monoid.exponent ↥E ∣ p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
      Subtype.ext (by simpa using hEab.2 x.val x.2)
  have hcardE : Nat.card ↥E ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact hexp
  have h1 : p ^ k ∣ p := by rw [← hk]; exact hcardE
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · rcases (pow_eq_one_iff (M := ℕ)).mp h with h' | h'
    · exact absurd h' (Nat.Prime.ne_one hp)
    · omega
  · rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · omega
    · have : p ^ k = p ^ 1 := by simpa using h
      exact (Nat.pow_right_injective (Nat.Prime.one_lt hp) this).le

theorem s16k_pRank_centralizer_le {Q : Type} [CommGroup Q] [Finite Q] (h2 : ∀ x : Q, x ^ 2 = 1)
    {L : Subgroup (MulAut Q)}
    (hirr : ∀ B : Subgroup Q, (∀ l ∈ L, ∀ b ∈ B, l b ∈ B) → B = ⊥ ∨ B = ⊤) {d : ℕ}
    (hQ : Nat.card Q = 2 ^ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (Subgroup.centralizer (L : Set (MulAut Q))) ≤
      if orderOf (2 : ZMod p) ∣ d then 1 else 0 := by
  classical
  let C := Subgroup.centralizer (L : Set (MulAut Q))
  have hcyc : IsCyclic ↥C := s16k_centralizer_isCyclic h2 hirr
  have hle : CFSG.Open.pRank p C ≤ 1 := s16k_pRank_le_one_of_isCyclic hcyc p hp
  by_cases hdiv : orderOf (2 : ZMod p) ∣ d
  · rw [if_pos hdiv]; exact hle
  · rw [if_neg hdiv]
    by_contra hne
    have hpos : 0 < CFSG.Open.pRank p C := Nat.lt_of_not_le hne
    have hp_dvd : p ∣ Nat.card C := by
      obtain ⟨E, hEC, hEab, hEcard⟩ :=
        CFSG.GH74.Uniqueness.SU.SU1.exists_pRank hp.one_lt C
      have h2 : p ∣ Nat.card E := by
        rw [hEcard]
        exact dvd_pow_self p hpos.ne'
      exact h2.trans (Subgroup.card_dvd_of_le hEC)
    obtain ⟨e, hed, hCdvd⟩ := s16k_centralizer_card_dvd h2 hirr hQ
    have hp_dvd_e : p ∣ 2 ^ e - 1 := hp_dvd.trans hCdvd
    have horder : orderOf (2 : ZMod p) ∣ e := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have h1 : ((2 : ZMod p) ^ e) = 1 := by
        have h2 : ((2 ^ e - 1 : ℕ) : ZMod p) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]
          exact hp_dvd_e
        have h3 : ((2 ^ e : ℕ) : ZMod p) = 1 := by
          have h4 : (1 : ℕ) ≤ 2 ^ e :=
            Nat.one_le_iff_ne_zero.mpr (pow_ne_zero e (by norm_num))
          rw [Nat.cast_sub h4, Nat.cast_one, sub_eq_zero] at h2
          exact h2
        simpa [Nat.cast_pow] using h3
      exact h1
    exact hdiv (horder.trans hed)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
