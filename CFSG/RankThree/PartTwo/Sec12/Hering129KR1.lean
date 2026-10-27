module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KLie
public import CFSG.RankThree.PartTwo.Sec12.Hering129KSLIso
public import CFSG.RankThree.PartTwo.Sec12.Hering129LRank
public import CFSG.RankThree.PartTwo.Sec12.Hering129HEnd

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Range

variable {G : Type} [Group G] [Finite G]

@[expose] def HasLieParamInRange (Y : Subgroup G) : Prop :=
  ∃ (r : TauCeti.PrimePower) (δ : ℕ), IsG2D4 (↥Y ⧸ CFSG.pCore 2 ↥Y) r δ ∧
    4 ≤ r.card ∧ r.p ≠ 3 ∧ (δ = 3 → r.p = 2)

theorem noLieParamInRange_iff {Y : Subgroup G} :
    NoLieParamInRange Y ↔ ¬ HasLieParamInRange Y := by
  constructor
  · rintro h ⟨r, δ, hG, hr⟩
    exact h r δ hG hr
  · intro h r δ hG hr
    exact h ⟨r, δ, hG, hr⟩

end Range

@[expose] def Gap129KFLieIn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → GTwoType129 L K →
    ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b →
      ∀ Y : Subgroup G, Core129 A c x Y → resCent K x ≤ Y → HasLieParamInRange Y →
        SymData129 A c x Y ∧
        ¬ (resCent Y c ⊔ inSubgroup (aschbacherSolvableCore 3) Y = Y) ∧
        (Typ129I K Y → Nonempty (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c) ≃*
          L ⧸ aschbacherSolvableCore 3 L)) ∧
        (∀ r : TauCeti.PrimePower, Sec4.IsoGTwo (Y ⧸ CFSG.pCore 2 Y) r →
          Sec4.IsSLThreePiAt (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c)) r.card) ∧
        (∀ (r : TauCeti.PrimePower) (hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid),
          Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group) →
          Sec4.IsSLThreePiAt (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c)) r.card)

theorem gap129KFLieIn_of (hP : Gap129KFLieP) : Gap129KFLieIn := by
  intro G _ _ A c L b a K S cfg hty x hxD hxb Y hY hXY hrange
  obtain ⟨r₀, δ₀, hG₀, hr4, hrp3, hrδ⟩ := hrange
  obtain ⟨hD, hlt, hsl₀⟩ :=
    hP G A c L b a K S cfg hty x hxD hxb Y hY hXY r₀ δ₀ hG₀ hr4 hrp3 hrδ
  have key : ∀ (r : TauCeti.PrimePower) (δ : ℕ), IsG2D4 (↥Y ⧸ CFSG.pCore 2 ↥Y) r δ →
      Sec4.IsSLThreePiAt (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c)) r.card :=
    fun r δ hG => by
      rw [(Hering129KOrders.isG2D4_unique hG hG₀).2]
      exact hsl₀
  refine ⟨hD, hlt, fun hI => ?_, fun r hr => key r 1 (Or.inl ⟨rfl, hr⟩),
    fun r hr hf => key r 3 (Or.inr ⟨rfl, hr, hf⟩)⟩
  obtain ⟨e⟩ := hI
  obtain ⟨q, hqL, hqK⟩ := hty
  have hIq : Sec4.IsSLThreePiAt
      (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c)) q.card := by
    rcases hqK with ⟨hq, ⟨f⟩⟩ | ⟨hq, ⟨f⟩⟩
    · exact key q 1 (Or.inl ⟨rfl, hq, ⟨e.trans f⟩⟩)
    · exact key q 3 (Or.inr ⟨rfl, hq, ⟨e.trans f⟩⟩)
  exact Hering129KSLIso.nonempty_mulEquiv_of_isSLThreePiAt hIq hqL

section Types

variable {G : Type} [Group G] [Finite G]

theorem prime_ne_three_of_isSLThreePiAt {X : Type} [Group X] {q : TauCeti.PrimePower}
    (h : Sec4.IsSLThreePiAt X q.card) : q.p ≠ 3 := by
  intro hp
  obtain ⟨K, _, _, h⟩ := h
  have hd : 3 ∣ q.card := by
    rw [TauCeti.PrimePower.card_def q, hp]
    exact dvd_pow_self 3 q.exponent_pos.ne'
  rcases h with ⟨-, hm, -⟩ | ⟨-, hm, -⟩ <;> omega

theorem d4_p_eq_two_of_cfg (h1 : Sec4.Item4_1LargePrime) {A L K S : Subgroup G} {c b a : G}
    (cfg : Cfg129 G A c L b a K S) {r : TauCeti.PrimePower}
    (hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid)
    (f : K ⧸ CFSG.pCore 2 K ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group) : r.p = 2 := by
  have hG : IsG2D4 (K ⧸ CFSG.pCore 2 K) r 3 := Or.inr ⟨rfl, hr, ⟨f⟩⟩
  have hθ : aschbacherSolvableCore 3 K = CFSG.pCore 2 K :=
    Hering129KOut.aschbacherSolvableCore_eq_pCore_two hG
  obtain ⟨-, -, -, hb1, -⟩ := cfg.point_facts
  have hS4 := Hering129L.sectionFourHyp_quot_of_mem_thetaComponentsAt h1
    cfg.std.toTheoremFourHyp hb1 cfg.hK
  exact Hering129L.p_eq_two_of_sectionFourHyp_d4
    (Sec4.Census.sectionFourHyp_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hθ) hS4) hG

theorem hasLieParamInRange_of_typ129I (h1 : Sec4.Item4_1LargePrime) {A L K S : Subgroup G}
    {c b a : G} (cfg : Cfg129 G A c L b a K S) {q : TauCeti.PrimePower}
    (hq : GTwoType129At L K q) {Y : Subgroup G} (hI : Typ129I K Y) : HasLieParamInRange Y := by
  have hq4 : 4 ≤ q.card :=
    four_le_of_isSLThreePiAt (isQuasisimple_thetaQuot_of_mem cfg.std.mem_thetaComponentsAt) hq.1
  have hq3 : q.p ≠ 3 := prime_ne_three_of_isSLThreePiAt hq.1
  obtain ⟨e⟩ := hI
  rcases hq.2 with ⟨hq', ⟨f⟩⟩ | ⟨hq', ⟨f⟩⟩
  · exact ⟨q, 1, Or.inl ⟨rfl, hq', ⟨e.trans f⟩⟩, hq4, hq3, fun h => absurd h (by norm_num)⟩
  · exact ⟨q, 3, Or.inr ⟨rfl, hq', ⟨e.trans f⟩⟩, hq4, hq3,
      fun _ => d4_p_eq_two_of_cfg h1 cfg hq' f⟩

theorem hasLieParamInRange_of_typ129II (h1 : Sec4.Item4_1LargePrime) {A L K S : Subgroup G}
    {c b a : G} (cfg : Cfg129 G A c L b a K S) {Y : Subgroup G} (hII : Typ129II K Y) :
    HasLieParamInRange Y := by
  obtain ⟨q', ⟨hq', ⟨e1⟩⟩, hG2⟩ := hII
  have hp2 : q'.p = 2 := d4_p_eq_two_of_cfg h1 cfg hq' e1
  set r₀ : TauCeti.PrimePower :=
    ⟨q'.p, 3 * q'.exponent, q'.prime_p, Nat.mul_pos (by norm_num) q'.exponent_pos⟩ with hr₀
  have hcard : r₀.card = q'.p ^ (3 * q'.exponent) := TauCeti.PrimePower.card_def r₀
  have h3e : 3 ≤ 3 * q'.exponent := by have := q'.exponent_pos; omega
  have h8 : 2 ^ 3 ≤ q'.p ^ (3 * q'.exponent) :=
    (Nat.pow_le_pow_left q'.prime_p.two_le 3).trans (Nat.pow_le_pow_right (by omega) h3e)
  refine ⟨r₀, 1, Or.inl ⟨rfl, hG2⟩, by omega, ?_, fun h => absurd h (by norm_num)⟩
  change q'.p ≠ 3
  omega

theorem hasLieParamInRange_of_typ129IV {q : TauCeti.PrimePower} {Y : Subgroup G}
    (hIV : Typ129IV q Y) : HasLieParamInRange Y := by
  obtain ⟨-, r, hr45, -, hG2⟩ := hIV
  refine ⟨r, 1, Or.inl ⟨rfl, hG2⟩, by omega, ?_, fun h => absurd h (by norm_num)⟩
  intro hp
  have hd : 3 ∣ r.card := by
    rw [TauCeti.PrimePower.card_def r, hp]
    exact dvd_pow_self 3 r.exponent_pos.ne'
  omega

end Types

end CFSG.RankThree.PartTwo.Sec12
