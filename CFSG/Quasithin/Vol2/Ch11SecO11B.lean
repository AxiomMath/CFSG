module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.CharacterTheory.BrauerLinearThree.LocalRecognition
public import CFSG.LieType.HighestRoot.CentTrialitySL2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.O11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem isElemAbelian_nine {E : Subgroup Q} (hE : Nat.card ↥E = 9) (hE3 : ∀ e ∈ E, e ^ 3 = 1) :
    IsElemAbelian 3 E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hE]; norm_num), hE3⟩

theorem two_le_pRank_three {E : Subgroup Q} (hE : Nat.card ↥E = 9) (hE3 : ∀ e ∈ E, e ^ 3 = 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q) :=
  CFSG.SectionRank.le_pRank (by norm_num) le_top (isElemAbelian_nine hE hE3) (by rw [hE]; norm_num)

omit [Finite Q] in
theorem nine_dvd_card {E : Subgroup Q} (hE : Nat.card ↥E = 9) : 9 ∣ Nat.card Q :=
  hE ▸ Subgroup.card_subgroup_dvd_card E

omit [Finite Q] in
theorem card_map_eq_of_injective {G' : Type*} [Group G'] {E : Subgroup Q} (f : Q →* G')
    (hf : Function.Injective (f.comp E.subtype)) : Nat.card ↥(E.map f) = Nat.card ↥E := by
  have h : E.map f = (⊤ : Subgroup ↥E).map (f.comp E.subtype) := by
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h, Subgroup.card_map_of_injective hf, Subgroup.card_top]

theorem false_of_psl2 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hQ : IsPSL 2 p 1 Q) {E : Subgroup Q}
    (hE : Nat.card ↥E = 9) (hE3 : ∀ e ∈ E, e ^ 3 = 1) : False := by
  have h1 := CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_prime hp hp3 hQ Nat.prime_three
    (by norm_num)
  have h2 := two_le_pRank_three hE hE3
  omega

omit [Finite Q] in
theorem false_of_psl2_25 (hQ : IsPSL 2 5 2 Q) {E : Subgroup Q} (hE : Nat.card ↥E = 9) : False := by
  have hc := CFSG.Wreathed.ProjectiveTwoParameterUniqueness.card_stated_psl_two Q 5 2 hQ
  have h9 := nine_dvd_card hE
  rw [hc] at h9
  norm_num at h9

theorem card_statedSL3_five {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5) :
    Nat.card ↥(StatedSL 3 K) = 372000 := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv,
    CFSG.BrauerLinearThree.card_SL_three, hK]
  norm_num

omit [Finite Q] in
theorem false_of_sl3_5 (hQ : IsSL3 5 Q) {E : Subgroup Q} (hE : Nat.card ↥E = 9) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hQ
  have h9 := nine_dvd_card hE
  rw [Nat.card_congr e.toEquiv, card_statedSL3_five hK] at h9
  norm_num at h9

omit [Finite Q] in
theorem false_of_psl3_5 (hQ : IsPSL 3 5 1 Q) {E : Subgroup Q} (hE : Nat.card ↥E = 9) : False := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hQ
  have hd : Nat.card Q ∣ 372000 := by
    rw [Nat.card_congr e.toEquiv, ← card_statedSL3_five (by rw [hK]; norm_num)]
    exact Subgroup.index_dvd_card _
  have := (nine_dvd_card hE).trans hd
  norm_num at this

omit [Finite Q] in
theorem false_of_j1 (hQ : IsSporadic .J1 Q) {E : Subgroup Q}
    (hE : Nat.card ↥E = 9) : False := by
  obtain ⟨e⟩ := hQ
  have h9 := nine_dvd_card hE
  rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .J1) = 175560 from
    CFSG.Sporadic.J1.card_J1] at h9
  norm_num at h9

omit [Finite Q] in
theorem false_of_a36Case4 (hQ : A36Case4 Q) {E : Subgroup Q} (hE : Nat.card ↥E = 9) : False := by
  obtain ⟨-, -, ⟨e⟩, hp⟩ := hQ
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq : Nat.card (Q ⧸ CFSG.fittingSubgroup Q) = 120 := by
    have h := CFSG.LieType.HighestRoot.card_SL2 (F := ZMod 5)
    rw [Nat.card_zmod] at h
    rw [Nat.card_congr e.toEquiv]
    exact h
  have h3 : ¬ 3 ∣ Nat.card ↥(CFSG.fittingSubgroup Q) := fun h => by
    have := (hp 3 Nat.prime_three h).1
    omega
  have h9 := nine_dvd_card hE
  rw [(CFSG.fittingSubgroup Q).card_eq_card_quotient_mul_card_subgroup, hq] at h9
  have hcop : Nat.Coprime 9 (Nat.card ↥(CFSG.fittingSubgroup Q)) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  have := hcop.dvd_of_dvd_mul_right h9
  norm_num at this

theorem false_of_sl2 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {E : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))} (hE : Nat.card ↥E = 9)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
  have hinj : Function.Injective (π.comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxc : (x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
      have := (QuotientGroup.eq_one_iff _).mp hx
      exact this
    obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxc
    have h2 : (x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, ← map_pow]
      rw [Fintype.card_fin] at hr
      rw [hr, map_one]
      rfl
    have h3 := hE3 x x.2
    have h1 : (x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = 1 := by
      have := pow_gcd_eq_one.mpr ⟨h2, h3⟩
      rwa [show Nat.gcd 2 3 = 1 from rfl, pow_one] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  set E' := E.map π with hE'
  have hE'c : Nat.card ↥E' = 9 := by
    rw [hE', ← hE]
    exact card_map_eq_of_injective π hinj
  have hE'3 : ∀ x ∈ E', x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE3 a ha, map_one]
  have hp3 : IsPGroup 3 ↥E' := fun x => ⟨1, Subtype.ext (by simpa using hE'3 x x.2)⟩
  obtain ⟨R, hR⟩ := hp3.exists_le_sylow
  have hcop : Nat.Coprime 3 (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
  have hRc := CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card (ZMod p)
    (p := p) (f := 1) (by rw [Nat.card_zmod, pow_one]) (by rw [Nat.card_zmod]; exact hp7) 3
    (by norm_num) hcop R
  have hcyc : IsCyclic ↥E' := by
    have : IsCyclic ↥(E'.subgroupOf (R : Subgroup _)) := Subgroup.isCyclic _
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hR).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hR).surjective
  have hexp : Monoid.exponent ↥E' ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using hE'3 x x.2)
  have hle := Nat.le_of_dvd (by norm_num) hexp
  rw [IsCyclic.exponent_eq_card, hE'c] at hle
  omega

omit [Finite Q] in
theorem false_of_affine {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) {F : Subgroup Q} [F.Normal]
    (hF : IsElemAbelianOfRank p 2 ↥F) (hnat : NaturalSL2Action p Q F) {E : Subgroup Q}
    (hE : Nat.card ↥E = 9) (hE3 : ∀ e ∈ E, e ^ 3 = 1) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, ψ, -, hψk, -⟩ := hnat
  obtain ⟨eF⟩ := hF
  have hFp : ∀ f ∈ F, f ^ p = 1 := fun f hf => by
    have h1 : (eF ⟨f, hf⟩) ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      simp
    have h2 : (⟨f, hf⟩ : ↥F) ^ p = 1 := eF.injective (by rw [map_pow, h1, map_one])
    simpa using congrArg Subtype.val h2
  have hinj : Function.Injective (ψ.comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxF : (x : Q) ∈ F := by rw [← hψk]; exact hx
    have hcop : Nat.gcd 3 p = 1 :=
      (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
    have h1 : (x : Q) = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hE3 x x.2, hFp x hxF⟩
      rwa [hcop, pow_one] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  refine false_of_sl2 hp hp7 (E := E.map ψ) ?_ ?_
  · rw [← hE]
    exact card_map_eq_of_injective ψ hinj
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE3 a ha, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecS.O11
