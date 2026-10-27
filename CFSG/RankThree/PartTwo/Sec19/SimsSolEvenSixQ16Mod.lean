module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16Rank
import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSIsoA
import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResEA
import CFSG.CGT.PushingUpLit.CGT6.SixFourAlt6
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11AltOrd
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen4
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

namespace Q16Mod

section Sq

variable {G : Type*} [Group G] {P : Subgroup G}

theorem mul_self_mem_sqSub {x : G} (hx : x ∈ P) : x * x ∈ Q16.sqSub P :=
  Subgroup.subset_closure ⟨x, hx, rfl⟩

theorem comm_mem_sqSub {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    x * y * x⁻¹ * y⁻¹ ∈ Q16.sqSub P := by
  have e : x * y * x⁻¹ * y⁻¹ =
      (x * y) * (x * y) * ((y⁻¹ * x⁻¹ * y) * (y⁻¹ * x⁻¹ * y)) * (y⁻¹ * y⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mul_self_mem_sqSub (P.mul_mem hx hy))
    (mul_self_mem_sqSub (P.mul_mem (P.mul_mem (P.inv_mem hy) (P.inv_mem hx)) hy)))
    (mul_self_mem_sqSub (P.inv_mem hy))

end Sq

section Perm

theorem card_le_of_dvd {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H) {n m : ℕ}
    (hn : Nat.card H ∣ n) (hm : ¬ 2 ^ (m + 1) ∣ n) : Nat.card H ≤ 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  rw [hk] at hn ⊢
  exact Nat.pow_le_pow_right (by norm_num) (not_lt.1 fun h => hm ((Nat.pow_dvd_pow 2 h).trans hn))

theorem card_le_sixteen {B : Subgroup (Perm (Fin 6))} (hB : IsPGroup 2 B) : Nat.card B ≤ 16 := by
  have h := Subgroup.card_subgroup_dvd_card B
  rw [Nat.card_perm, Nat.card_fin] at h
  exact card_le_of_dvd hB (m := 4) h (by decide)

theorem card_le_eight {B : Subgroup (Perm (Fin 6))} (hB : IsPGroup 2 B)
    (hBA : B ≤ alternatingGroup (Fin 6)) : Nat.card B ≤ 8 := by
  have h := Subgroup.card_dvd_of_le hBA
  rw [Nat.card_eq_fintype_card (α := alternatingGroup (Fin 6)), card_alternatingGroup,
    Fintype.card_fin] at h
  exact card_le_of_dvd hB (m := 3) h (by decide)

theorem mul_self_eq_one_of_inf_eq_bot {B : Subgroup (Perm (Fin 6))}
    (h : Q16.sqSub B ⊓ B = ⊥) {b : Perm (Fin 6)} (hb : b ∈ B) : b * b = 1 := by
  have hbb : b * b ∈ Q16.sqSub B ⊓ B :=
    Subgroup.mem_inf.2 ⟨mul_self_mem_sqSub hb, B.mul_mem hb hb⟩
  rwa [h, Subgroup.mem_bot] at hbb

theorem relIndex_sqSub_le_eight {B : Subgroup (Perm (Fin 6))} (hB : IsPGroup 2 B) :
    (Q16.sqSub B).relIndex B ≤ 8 := by
  have h := Subgroup.relIndex_mul_card (Q16.sqSub B) B
  by_cases h1 : Q16.sqSub B ⊓ B = ⊥
  · rw [h1, Subgroup.card_bot, mul_one] at h
    rw [h]
    exact CFSG.EvenSporadicStandard.M24Std.card_elemAb_perm_six_le B fun b hb =>
      mul_self_eq_one_of_inf_eq_bot h1 hb
  · have h2 := (Subgroup.one_lt_card_iff_ne_bot _).2 h1
    have h3 : (Q16.sqSub B).relIndex B * 2 ≤ 16 :=
      calc (Q16.sqSub B).relIndex B * 2
          ≤ (Q16.sqSub B).relIndex B * Nat.card ↥(Q16.sqSub B ⊓ B) := Nat.mul_le_mul_left _ h2
        _ ≤ 16 := (le_of_eq h).trans (card_le_sixteen hB)
    omega

theorem relIndex_sqSub_le_four {B : Subgroup (Perm (Fin 6))} (hB : IsPGroup 2 B)
    (hBA : B ≤ alternatingGroup (Fin 6)) : (Q16.sqSub B).relIndex B ≤ 4 := by
  have h := Subgroup.relIndex_mul_card (Q16.sqSub B) B
  by_cases h1 : Q16.sqSub B ⊓ B = ⊥
  · rw [h1, Subgroup.card_bot, mul_one] at h
    rw [h]
    exact CFSG.EvenSporadicStandard.M24Std.card_elemAb_alt_six_le B hBA fun b hb =>
      mul_self_eq_one_of_inf_eq_bot h1 hb
  · have h2 := (Subgroup.one_lt_card_iff_ne_bot _).2 h1
    have h3 : (Q16.sqSub B).relIndex B * 2 ≤ 8 :=
      calc (Q16.sqSub B).relIndex B * 2
          ≤ (Q16.sqSub B).relIndex B * Nat.card ↥(Q16.sqSub B ⊓ B) := Nat.mul_le_mul_left _ h2
        _ ≤ 8 := (le_of_eq h).trans (card_le_eight hB hBA)
    omega

theorem exists_even_involution {B : Subgroup (Perm (Fin 6))} (hB : IsPGroup 2 B)
    (hne : B ⊓ alternatingGroup (Fin 6) ≠ ⊥) :
    ∃ b ∈ B, b ≠ 1 ∧ b * b = 1 ∧ sign b = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card ↥(B ⊓ alternatingGroup (Fin 6)) :=
    (hB.to_le inf_le_left).card_eq_or_dvd.resolve_left fun h => hne (Subgroup.card_eq_one.1 h)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hb' : orderOf (b : Perm (Fin 6)) = 2 := by rw [Subgroup.orderOf_coe, hb]
  refine ⟨b, (Subgroup.mem_inf.1 b.2).1, fun h => ?_, ?_,
    mem_alternatingGroup.1 (Subgroup.mem_inf.1 b.2).2⟩
  · rw [h, orderOf_one] at hb'
    exact absurd hb' (by norm_num)
  · rw [← pow_two, ← hb']
    exact pow_orderOf_eq_one _

end Perm

section Fix

@[expose] def fixU (σ : Perm (Fin 6)) : Set (permBar 6) :=
  {v | v ∈ Set.range (heartToBar (n := 6)) ∧ barAct σ v = v}

theorem mem_fixU {σ : Perm (Fin 6)} {v : permBar 6} :
    v ∈ fixU σ ↔ v ∈ Set.range (heartToBar (n := 6)) ∧ barAct σ v = v := Iff.rfl

theorem card_fixU_conj_le (σ τ : Perm (Fin 6)) :
    Nat.card ↥(fixU (τ * σ * τ⁻¹)) ≤ Nat.card ↥(fixU σ) := by
  have hmap : ∀ v ∈ fixU (τ * σ * τ⁻¹), barAct τ⁻¹ v ∈ fixU σ := by
    intro v hv
    obtain ⟨⟨u, hu⟩, hv⟩ := mem_fixU.1 hv
    refine mem_fixU.2 ⟨⟨altAct τ⁻¹ u, by rw [heartToBar_altAct, hu]⟩, ?_⟩
    calc barAct σ (barAct τ⁻¹ v) = barAct τ⁻¹ (barAct (τ * σ * τ⁻¹) v) := by
          rw [← barAct_mul, ← barAct_mul, show τ⁻¹ * (τ * σ * τ⁻¹) = σ * τ⁻¹ by group]
      _ = barAct τ⁻¹ v := by rw [hv]
  refine Nat.card_le_card_of_injective (fun v => ⟨barAct τ⁻¹ v.1, hmap v.1 v.2⟩) fun v w h => ?_
  have h' := congrArg (fun x => barAct τ x) (congrArg Subtype.val h)
  simp only [← barAct_mul, mul_inv_cancel, barAct_one] at h'
  exact Subtype.ext h'

theorem std_fix_cases : ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 →
    (∃ c : ZMod 2, ∀ i, -x ((swap (0 : Fin 6) 1 * swap 2 3 : Perm (Fin 6))⁻¹ i) + x i = c) →
    ∃ bc : ZMod 2 × ZMod 2, -(![0, 0, bc.1, bc.1, bc.2, bc.2] : Fin 6 → ZMod 2) + x = 0 ∨
      -(![0, 0, bc.1, bc.1, bc.2, bc.2] : Fin 6 → ZMod 2) + x = allOnes 6 := by
  decide

theorem card_fixU_std_le : Nat.card ↥(fixU (swap (0 : Fin 6) 1 * swap 2 3)) ≤ 4 := by
  let g : ZMod 2 × ZMod 2 → permBar 6 := fun bc =>
    ((![0, 0, bc.1, bc.1, bc.2, bc.2] : Fin 6 → ZMod 2) : permBar 6)
  have hsub : fixU (swap (0 : Fin 6) 1 * swap 2 3) ⊆ Set.range g := by
    intro v hv
    obtain ⟨⟨u, rfl⟩, hv⟩ := mem_fixU.1 hv
    obtain ⟨e, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [heartToBar_mk, barAct_mk, QuotientAddGroup.eq] at hv
    rw [heartToBar_mk]
    have he : ∑ i, (e : Fin 6 → ZMod 2) i = 0 := by
      simpa [evenWeight, AddMonoidHom.mem_ker] using e.2
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_zmultiples hv
    obtain ⟨bc, hbc⟩ := std_fix_cases _ he ⟨c, hc⟩
    exact ⟨bc, QuotientAddGroup.eq.2 ((mem_zmultiples_allOnes_iff _).2 hbc)⟩
  calc Nat.card ↥(fixU (swap (0 : Fin 6) 1 * swap 2 3)) ≤ Nat.card ↥(Set.range g) :=
        Nat.card_mono (Set.finite_range g) hsub
    _ ≤ Nat.card (ZMod 2 × ZMod 2) :=
        Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = 4 := by rw [Nat.card_prod, Nat.card_zmod]

theorem card_fixU_le_four {σ : Perm (Fin 6)} (h1 : σ ≠ 1) (h2 : σ * σ = 1) (hs : sign σ = 1) :
    Nat.card ↥(fixU σ) ≤ 4 := by
  obtain ⟨τ, -, rfl⟩ := CFSG.CGT.PushingUpLit.CGT6.perm6_involution_conj h2 h1 hs
  exact (card_fixU_conj_le _ τ).trans card_fixU_std_le

end Fix

end Q16Mod

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (C : Cfg G M X n)

theorem relIndex_sqSub_le_mul (hR : Nat.card ↥(Rc X) ≤ 2) {P : Subgroup G} (hPM : P ≤ M)
    {p : G} (hp : p ∈ P) :
    (Q16.sqSub P).relIndex P ≤
      (Q16.sqSub ((P.subgroupOf M).map C.θ)).relIndex ((P.subgroupOf M).map C.θ) *
        Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer {p}) := by
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M
  set B : Subgroup (Perm (Fin n)) := (P.subgroupOf M).map C.θ
  set S : Subgroup G := Q16.sqSub P ⊓ P
  have hpM : p ∈ M := hPM hp
  have hpQ : ∀ {q : G}, q ∈ Q → p * q * p⁻¹ ∈ Q := fun hq => pCoreOf_normalized M hpM hq
  let f : ↥(P ⊓ Q) →* G := MonoidHom.mk' (fun a => p * a * p⁻¹ * (a : G)⁻¹) fun a b => by
    have ha : (a : G) ∈ Q := (Subgroup.mem_inf.1 a.2).2
    have hb : (b : G) ∈ Q := (Subgroup.mem_inf.1 b.2).2
    have hc := C.Q_comm hR _ (Q.inv_mem ha) _ (Q.mul_mem (hpQ hb) (Q.inv_mem hb))
    simp only [Subgroup.coe_mul]
    calc p * (a * b) * p⁻¹ * ((a : G) * b)⁻¹ =
          p * a * p⁻¹ * ((p * b * p⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = p * a * p⁻¹ * ((a : G)⁻¹ * (p * b * p⁻¹ * (b : G)⁻¹)) := by rw [hc]
      _ = p * a * p⁻¹ * (a : G)⁻¹ * (p * b * p⁻¹ * (b : G)⁻¹) := by group
  have hker : Nat.card f.ker ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer {p}) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : ↥(P ⊓ Q)) : G), Subgroup.mem_inf.2
      ⟨(Subgroup.mem_inf.1 (k : ↥(P ⊓ Q)).2).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩⟩)
      fun k k' h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h')
    have hk : p * ((k : ↥(P ⊓ Q)) : G) * p⁻¹ * ((k : ↥(P ⊓ Q)) : G)⁻¹ = 1 :=
      MonoidHom.mem_ker.1 k.2
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hk)).symm
  have hrange : f.range ≤ S ⊓ Q := by
    intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
    have ha := Subgroup.mem_inf.1 a.2
    show p * a * p⁻¹ * (a : G)⁻¹ ∈ S ⊓ Q
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Q16Mod.comm_mem_sqSub hp ha.1, ?_⟩, ?_⟩
    · exact P.mul_mem (P.mul_mem (P.mul_mem hp ha.1) (P.inv_mem hp)) (P.inv_mem ha.1)
    · exact Q.mul_mem (hpQ ha.2) (Q.inv_mem ha.2)
  have hsqB : Q16.sqSub B ≤ (S.subgroupOf M).map C.θ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hb
    have hmP : (m : G) ∈ P := Subgroup.mem_subgroupOf.1 hm
    exact ⟨m * m, Subgroup.mem_subgroupOf.2
      (Subgroup.mem_inf.2 ⟨Q16Mod.mul_self_mem_sqSub hmP, P.mul_mem hmP hmP⟩), map_mul _ _ _⟩
  have h1 : Nat.card P = Nat.card ↥(P ⊓ Q) * Nat.card B := C.card_eq_card_inf_mul hR hPM
  have h2 : Nat.card S = Nat.card ↥(S ⊓ Q) * Nat.card ↥((S.subgroupOf M).map C.θ) :=
    C.card_eq_card_inf_mul hR (inf_le_right.trans hPM)
  have h3 : (Q16.sqSub P).relIndex P * Nat.card S = Nat.card P :=
    Subgroup.relIndex_mul_card _ _
  have h4 : (Q16.sqSub B).relIndex B * Nat.card ↥(Q16.sqSub B ⊓ B) = Nat.card B :=
    Subgroup.relIndex_mul_card _ _
  have h5 : Nat.card f.ker * Nat.card f.range = Nat.card ↥(P ⊓ Q) :=
    Subgroup.card_ker_mul_card_range f
  have h6 : Nat.card f.range ≤ Nat.card ↥(S ⊓ Q) := Subgroup.card_le_of_le hrange
  have h7 : Nat.card ↥(Q16.sqSub B ⊓ B) ≤ Nat.card ↥((S.subgroupOf M).map C.θ) :=
    Subgroup.card_le_of_le (inf_le_left.trans hsqB)
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos : 0 < Nat.card S)
  calc (Q16.sqSub P).relIndex P * Nat.card S = Nat.card P := h3
    _ = Nat.card f.ker * Nat.card f.range *
          ((Q16.sqSub B).relIndex B * Nat.card ↥(Q16.sqSub B ⊓ B)) := by rw [h1, h5, h4]
    _ ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer {p}) * Nat.card ↥(S ⊓ Q) *
          ((Q16.sqSub B).relIndex B * Nat.card ↥((S.subgroupOf M).map C.θ)) := by gcongr
    _ = (Q16.sqSub B).relIndex B * Nat.card ↥(Q ⊓ Subgroup.centralizer {p}) * Nat.card S := by
          rw [h2]; ring

theorem isPGroup_map_theta {P : Subgroup G} (hPM : P ≤ M) (hP : IsPGroup 2 P) :
    IsPGroup 2 ↥((P.subgroupOf M).map C.θ) :=
  (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm).map C.θ

end Cfg

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

include D in
theorem q16_card_Rc (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) : Nat.card ↥(Rc X) = 1 := by
  have h2 : Nat.card ↥(Rc X) ≠ 2 := fun h => D.card_Q_ne_sixteen_of_card_Rc h hQ
  have hpos : 0 < Nat.card ↥(Rc X) := Nat.card_pos
  omega

theorem q16_piQ_injective (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) : Function.Injective D.piQ := by
  rw [injective_iff_map_eq_one]
  intro q hq
  have h := (D.piQ_eq_one_iff q).1 hq
  rw [Subgroup.card_eq_one.1 (D.q16_card_Rc hR hQ), Subgroup.mem_bot] at h
  exact Subtype.ext h

theorem q16_piQ_mem_range (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    Multiplicative.toAdd (D.piQ q) ∈ Set.range (heartToBar (n := 6)) := by
  have hcard := SixSIsoAAux.card_Q_eq_card_R_mul D
  rw [hQ, D.q16_card_Rc hR hQ, one_mul] at hcard
  have heq := Subgroup.eq_of_le_of_card_ge (SixSIsoAAux.range_heart_le_piQ D)
    (by rw [SixSIsoAAux.card_range_heart, ← hcard])
  have hq : D.piQ q ∈ ((CFSG.Open.pCoreOf 2 M).subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ :=
    ⟨q, Subgroup.mem_subgroupOf.2 q.2, rfl⟩
  rw [← heq] at hq
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hq
  exact ⟨Multiplicative.toAdd a, congrArg Multiplicative.toAdd ha⟩

include D in
theorem q16_card_centralizer_le_four (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) {p : G} (hpM : p ∈ M)
    (h1 : C.θ ⟨p, hpM⟩ ≠ 1) (h2 : C.θ ⟨p, hpM⟩ * C.θ ⟨p, hpM⟩ = 1)
    (hs : sign (C.θ ⟨p, hpM⟩) = 1) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer {p}) ≤ 4 := by
  have hfix : ∀ c : ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer {p}),
      Multiplicative.toAdd (D.piQ ⟨c, (Subgroup.mem_inf.1 c.2).1⟩) ∈
        Q16Mod.fixU (C.θ ⟨p, hpM⟩) := by
    intro c
    have hc := Subgroup.mem_inf.1 c.2
    have hcp : (c : G) * p = p * c := Subgroup.mem_centralizer_singleton_iff.1 hc.2
    refine Q16Mod.mem_fixU.2 ⟨D.q16_piQ_mem_range hR hQ _, ?_⟩
    exact (D.piQ_conj ⟨p, hpM⟩ ⟨c, hc.1⟩ ⟨c, hc.1⟩ (by
      show (c : G) = p * c * p⁻¹
      rw [← hcp, mul_inv_cancel_right])).symm
  refine le_trans (Nat.card_le_card_of_injective (fun c => ⟨_, hfix c⟩) fun c c' h => ?_)
    (Q16Mod.card_fixU_le_four h1 h2 hs)
  have h' := D.q16_piQ_injective hR hQ (Multiplicative.toAdd.injective (congrArg Subtype.val h))
  have h'' := congrArg Subtype.val h'
  exact Subtype.ext h''

include D in
theorem q16_relindex_sqSub_le (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) {P : Subgroup G} (hPM : P ≤ M)
    (hP : IsPGroup 2 P) : (Q16.sqSub P).relIndex P ≤ 32 := by
  have hBp := C.isPGroup_map_theta hPM hP
  by_cases hne : (P.subgroupOf M).map C.θ ⊓ alternatingGroup (Fin 6) = ⊥
  · calc (Q16.sqSub P).relIndex P ≤ _ := C.relIndex_sqSub_le_mul hR hPM P.one_mem
      _ ≤ 2 * 16 := Nat.mul_le_mul
          ((Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)).trans
            (CFSG.ComponentClassification.GSThmB.X11.Sym.card_le_two_of_inf_eq_bot hne))
          ((Subgroup.card_le_of_le inf_le_left).trans hQ.le)
  · obtain ⟨b, hbB, hb1, hb2, hbs⟩ := Q16Mod.exists_even_involution hBp hne
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hbB
    calc (Q16.sqSub P).relIndex P ≤ _ :=
          C.relIndex_sqSub_le_mul hR hPM (Subgroup.mem_subgroupOf.1 hm)
      _ ≤ 8 * 4 := Nat.mul_le_mul (Q16Mod.relIndex_sqSub_le_eight hBp)
          (D.q16_card_centralizer_le_four hR hQ m.2 hb1 hb2 hbs)

include D in
theorem q16_relindex_sqSub_le_alt (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) {P : Subgroup G} (hPM : P ≤ M)
    (hP : IsPGroup 2 P)
    (halt : ∀ (p : G) (hp : p ∈ P), C.θ ⟨p, hPM hp⟩ ∈ alternatingGroup (Fin 6)) :
    (Q16.sqSub P).relIndex P ≤ 16 := by
  have hBp := C.isPGroup_map_theta hPM hP
  have hBA : (P.subgroupOf M).map C.θ ≤ alternatingGroup (Fin 6) := by
    rintro _ ⟨m, hm, rfl⟩
    exact halt m (Subgroup.mem_subgroupOf.1 hm)
  by_cases hne : (P.subgroupOf M).map C.θ = ⊥
  · calc (Q16.sqSub P).relIndex P ≤ _ := C.relIndex_sqSub_le_mul hR hPM P.one_mem
      _ ≤ 1 * 16 := Nat.mul_le_mul (by rw [hne, Subgroup.relIndex_bot_right])
          ((Subgroup.card_le_of_le inf_le_left).trans hQ.le)
  · obtain ⟨b, hbB, hb1, hb2, hbs⟩ :=
      Q16Mod.exists_even_involution hBp (by rwa [inf_eq_left.2 hBA])
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hbB
    calc (Q16.sqSub P).relIndex P ≤ _ :=
          C.relIndex_sqSub_le_mul hR hPM (Subgroup.mem_subgroupOf.1 hm)
      _ ≤ 4 * 4 := Nat.mul_le_mul (Q16Mod.relIndex_sqSub_le_four hBp hBA)
          (D.q16_card_centralizer_le_four hR hQ m.2 hb1 hb2 hbs)

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
