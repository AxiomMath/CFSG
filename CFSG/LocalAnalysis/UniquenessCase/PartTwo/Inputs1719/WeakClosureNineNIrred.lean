module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNLift
public import CFSG.LocalAnalysis.WeakClosure81.NineLemmaD
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFW

open CFSG.Quasithin CFSG.Open Subgroup

theorem map_frattini_eq_nineFrattini_range {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) : (frattini A).map f = nineFrattini f.range := by
  set e : A ≃* f.range := MonoidHom.ofInjective hf
  have hfe : f = f.range.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [nineFrattini, ← map_frattini_mulEquiv e, Subgroup.map_map, ← hfe]

variable {G : Type} [Group G] {N : Subgroup G} {X : Type} [Group X] {π : ↥N →* X}

@[expose] def restr (π : ↥N →* X) {Y : Subgroup G} (hYN : Y ≤ N) : ↥Y →* X :=
  π.comp (Subgroup.inclusion hYN)

theorem barSub_eq_map_restr {Y Z : Subgroup G} (hYN : Y ≤ N) (hZY : Z ≤ Y) :
    barSub π Z = (Z.subgroupOf Y).map (restr π hYN) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hZY hx⟩, hx, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Subgroup.inclusion hYN z, hz, rfl⟩

variable (hker : ∀ x : ↥N, π x = 1 ↔ (x : G) ∈ pCoreOf 2 N)
include hker

theorem restr_injective {Y : Subgroup G} (hYN : Y ≤ N) (hYQ : Y ⊓ pCoreOf 2 N = ⊥) :
    Function.Injective (restr π hYN) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h1 : (y : G) ∈ pCoreOf 2 N := (hker _).1 hy
  have h2 : (y : G) ∈ Y ⊓ pCoreOf 2 N := ⟨y.2, h1⟩
  rw [hYQ, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

theorem barSub_nineFrattini {Y : Subgroup G} (hYN : Y ≤ N) (hYQ : Y ⊓ pCoreOf 2 N = ⊥) :
    barSub π (nineFrattini Y) = nineFrattini (barSub π Y) := by
  have hf := restr_injective hker hYN hYQ
  have h1 : barSub π (nineFrattini Y) = (frattini ↥Y).map (restr π hYN) := by
    rw [barSub_eq_map_restr hYN (show nineFrattini Y ≤ Y from Subgroup.map_subtype_le _)]
    congr 1
    show ((frattini ↥Y).map Y.subtype).comap Y.subtype = frattini ↥Y
    exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  have h2 : barSub π Y = (restr π hYN).range := by
    rw [barSub_eq_map_restr hYN le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  rw [h1, h2]
  exact map_frattini_eq_nineFrattini_range _ hf

theorem eq_of_barSub_eq {Y Z W : Subgroup G} (hYN : Y ≤ N) (hYQ : Y ⊓ pCoreOf 2 N = ⊥)
    (hZY : Z ≤ Y) (hWY : W ≤ Y) (h : barSub π Z = barSub π W) : Z = W := by
  rw [barSub_eq_map_restr hYN hZY, barSub_eq_map_restr hYN hWY] at h
  have h' := Subgroup.map_injective (restr_injective hker hYN hYQ) h
  rw [← Subgroup.map_subgroupOf_eq_of_le hZY, ← Subgroup.map_subgroupOf_eq_of_le hWY, h']

theorem exists_mem_normalizer_of_barSub [Finite G] {p : ℕ} [Fact p.Prime] {Yb Sb : Subgroup X}
    {Y : Subgroup G} (hY : IsSylowIn p Y (liftSub π Yb)) (hYb : barSub π Y = Yb)
    {sb : X} (hsb : sb ∈ Sb ⊓ normalizer (Yb : Set X)) (hπ : Function.Surjective π) :
    ∃ s ∈ liftSub π Sb ⊓ normalizer (Y : Set G), ∃ hsN : s ∈ N, π ⟨s, hsN⟩ = sb := by
  obtain ⟨s₀, rfl⟩ := hπ sb
  have hYN : Y ≤ N := hY.1.trans (liftSub_le _)
  set Y' : Subgroup G := Y.map (MulAut.conj (s₀ : G)).toMonoidHom with hY'
  have hY'le : Y' ≤ liftSub π Yb := by
    rintro _ ⟨y, hy, rfl⟩
    show (s₀ : G) * y * (s₀ : G)⁻¹ ∈ liftSub π Yb
    have hyN : y ∈ N := hYN hy
    have hmem : (s₀ : G) * y * (s₀ : G)⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem s₀.2 hyN) (N.inv_mem s₀.2)
    refine mem_liftSub.2 ⟨hmem, ?_⟩
    have e : (⟨(s₀ : G) * y * (s₀ : G)⁻¹, hmem⟩ : ↥N) = s₀ * ⟨y, hyN⟩ * s₀⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    have hyb : π ⟨y, hyN⟩ ∈ Yb := hYb ▸ mem_barSub_of_mem hyN hy
    exact (Subgroup.mem_normalizer_iff.1 hsb.2 _).1 hyb
  have hY'syl : IsSylowIn p Y' (liftSub π Yb) := by
    refine isSylowIn_of_card_eq hY'le ?_
    rw [hY', Subgroup.card_map_of_injective (MulAut.conj (s₀ : G)).injective]
    exact hY.card_eq
  obtain ⟨h, hh, hconj⟩ := Ch1Sec3.exists_conj_of_isSylowIn hY hY'syl
  obtain ⟨hhN, hhb⟩ := mem_liftSub.1 hh
  rw [← hYb] at hhb
  obtain ⟨y₀, hy₀Y, hy₀⟩ := hhb
  set q : ↥N := ⟨h, hhN⟩ * y₀⁻¹ with hq
  have hqQ : (q : G) ∈ pCoreOf 2 N := (hker q).1 (by rw [hq, map_mul, map_inv, hy₀, mul_inv_cancel])
  have hqval : (q : G) = h * (y₀ : G)⁻¹ := rfl
  set s : ↥N := q⁻¹ * s₀ with hs
  have hsval : (s : G) = (y₀ : G) * h⁻¹ * s₀ := by
    rw [hs, Subgroup.coe_mul, Subgroup.coe_inv, hqval]
    group
  refine ⟨s, Subgroup.mem_inf.2 ⟨?_, ?_⟩, s.2, ?_⟩
  ·
    refine mem_liftSub.2 ⟨s.2, ?_⟩
    have hq1 : π q = 1 := (hker q).2 hqQ
    rw [hs, map_mul, map_inv, hq1, inv_one, one_mul]
    exact hsb.1
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have key : (s : G) * y * (s : G)⁻¹ =
        (y₀ : G) * (h⁻¹ * ((s₀ : G) * y * (s₀ : G)⁻¹) * h) * (y₀ : G)⁻¹ := by
      rw [hsval]
      group
    have hmemY' : (s₀ : G) * y * (s₀ : G)⁻¹ ∈ Y' ↔ y ∈ Y := by
      rw [hY']
      constructor
      · rintro ⟨z, hz, hze⟩
        have hzy : z = y := by
          have := congrArg (fun w => (s₀ : G)⁻¹ * w * (s₀ : G)) hze
          simpa [MulAut.conj_apply, mul_assoc] using this
        exact hzy ▸ hz
      · intro hy
        exact ⟨y, hy, rfl⟩
    rw [key]
    constructor
    · intro hy
      have h1 := (hconj _).1 (hmemY'.2 hy)
      exact Y.mul_mem (Y.mul_mem hy₀Y h1) (Y.inv_mem hy₀Y)
    · intro hy
      have h1 : h⁻¹ * ((s₀ : G) * y * (s₀ : G)⁻¹) * h ∈ Y := by
        have := Y.mul_mem (Y.mul_mem (Y.inv_mem hy₀Y) hy) hy₀Y
        simpa [mul_assoc] using this
      exact hmemY'.1 ((hconj _).2 h1)
  · have hq1 : π q = 1 := (hker q).2 hqQ
    rw [hs, map_mul, map_inv, hq1, inv_one, one_mul]

theorem twoPTwoIrred_liftSub [Finite G] [Finite X] (hπ : Function.Surjective π)
    {K S Yb : Subgroup X} {p : ℕ} (h : TwoPTwoIrred K S Yb p) :
    ∃ Y : Subgroup G, TwoPTwoIrred (liftSub π K) (liftSub π S) Y p ∧ barSub π Y = Yb ∧
      Y ⊓ pCoreOf 2 N = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Y, hY⟩ := exists_isSylowIn p (liftSub π Yb)
  have hYN : Y ≤ N := hY.1.trans (liftSub_le _)
  have hYQ : Y ⊓ pCoreOf 2 N = ⊥ :=
    (IsPGroup.disjoint_of_ne p 2 h.odd Y (pCoreOf 2 N) hY.isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)).eq_bot
  have hYb : barSub π Y = Yb := by
    have hle : barSub π Y ≤ Yb := (barSub_le_iff hYN).2 hY.1
    have hidx : (barSub π Y).relIndex Yb = 1 := by
      have h1 : (barSub π Y).relIndex Yb =
          (liftSub π (barSub π Y)).relIndex (liftSub π Yb) := (relIndex_liftSub hπ _ _).symm
      have h2 : (liftSub π (barSub π Y)).relIndex (liftSub π Yb) ∣ Y.relIndex (liftSub π Yb) :=
        Subgroup.relIndex_dvd_of_le_left _ ((barSub_le_iff hYN).1 le_rfl)
      have h3 : (barSub π Y).relIndex Yb ∣ Nat.card Yb := Subgroup.relIndex_dvd_card _ _
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h.sylowP.isPGroup
      rw [hn] at h3
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow h.prime).1 h3
      rcases k with _ | k
      · simpa using hk
      · exfalso
        apply hY.2.2
        refine dvd_trans ?_ (h1 ▸ h2)
        rw [hk, pow_succ]
        exact dvd_mul_left _ _
    exact le_antisymm hle (Subgroup.relIndex_eq_one.1 hidx)
  have hKle : liftSub π Yb ≤ liftSub π K := liftSub_mono h.sylowP.le
  refine ⟨Y, ⟨⟨h.prime, h.odd, oTwoPTwo_liftSub hker K h.oTwoPTwo,
    isSylowIn_two_liftSub hker hπ h.sylowTwo, ?_⟩, ?_⟩, hYb, hYQ⟩
  ·
    refine ⟨hY.1.trans hKle, hY.isPGroup, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex Y (liftSub π Yb) (liftSub π K) hY.1 hKle,
      relIndex_liftSub hπ]
    intro hdvd
    rcases (Nat.Prime.dvd_mul h.prime).1 hdvd with h1 | h1
    · exact hY.2.2 h1
    · exact h.sylowP.2.2 h1
  ·
    have hΦ := barSub_nineFrattini hker hYN hYQ
    rw [hYb] at hΦ
    refine ⟨?_, ?_⟩
    · refine lt_of_le_of_ne (TwoPTwoIrred.nineFrattini_le Y) fun heq => ?_
      have := congrArg (barSub π) heq
      rw [hΦ, hYb] at this
      exact h.irred.1.ne this
    · intro Z hΦZ hZY hinv
      have hZb1 : nineFrattini Yb ≤ barSub π Z := hΦ ▸ barSub_mono hΦZ
      have hZb2 : barSub π Z ≤ Yb := hYb ▸ barSub_mono hZY
      have hZb3 : ∀ s ∈ S ⊓ normalizer (Yb : Set X), ∀ z ∈ barSub π Z,
          s * z * s⁻¹ ∈ barSub π Z := by
        rintro sb hsb _ ⟨z, hzZ, rfl⟩
        obtain ⟨s, hs, hsN, rfl⟩ := exists_mem_normalizer_of_barSub hker hY hYb hsb hπ
        have hmem := hinv s hs z hzZ
        have hmemN : (s : G) * z * s⁻¹ ∈ N := N.mul_mem (N.mul_mem hsN z.2) (N.inv_mem hsN)
        have e : π ⟨s, hsN⟩ * π z * (π ⟨s, hsN⟩)⁻¹ = π ⟨s * z * s⁻¹, hmemN⟩ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          rfl
        rw [e]
        exact mem_barSub_of_mem hmemN hmem
      rcases h.irred.2 _ hZb1 hZb2 hZb3 with h1 | h1
      · left
        exact eq_of_barSub_eq hker hYN hYQ hZY (TwoPTwoIrred.nineFrattini_le Y) (h1.trans hΦ.symm)
      · right
        exact eq_of_barSub_eq hker hYN hYQ hZY le_rfl (h1.trans hYb.symm)

end CFSG.LocalAnalysis.WeakClosure81.NFW
