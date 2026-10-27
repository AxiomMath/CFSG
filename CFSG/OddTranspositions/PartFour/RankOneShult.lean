module

public import CFSG.OddTranspositions.PartFour.SemiregularFourGroup
import CFSG.OddTranspositions.PartFour.LineShult
import CFSG.GroupTheory.ONanLinearSpace

public section

namespace CFSG.OddTranspositions.PartFour

open MulAction Subgroup

private theorem rankOneShult_isolated {X Ω : Type*} [Group X] [MulAction X Ω] {α : Ω} {z : X}
    (hzα : z ∈ stabilizer X α) (hzc : ∀ g ∈ stabilizer X α, Commute g z)
    (hzfix : ∀ β : Ω, z • β = β → β = α) :
    ∀ g : X, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) → g * z * g⁻¹ = z := by
  intro g hcomm
  let y : X := g * z * g⁻¹
  have hzα' : z • α = α := MulAction.mem_stabilizer_iff.mp hzα
  have hyfix : y • (g • α) = g • α := by
    dsimp [y]
    rw [mul_smul, mul_smul, inv_smul_smul, hzα']
  have hyonly : ∀ ω : Ω, y • ω = ω → ω = g • α := by
    intro ω hω
    have h1 : z • (g⁻¹ • ω) = g⁻¹ • ω := by
      have h := congrArg (fun t => g⁻¹ • t) hω
      simpa [y, mul_smul, mul_assoc] using h
    have h2 : g⁻¹ • ω = α := hzfix _ h1
    calc ω = g • (g⁻¹ • ω) := by
          rw [← mul_smul, mul_inv_cancel, one_smul]
      _ = g • α := by rw [h2]
  have hcommy : y * z = z * y := hcomm
  have hzfixg : z • (g • α) = g • α := by
    have h : y • (z • (g • α)) = z • (g • α) := by
      rw [← mul_smul, hcommy, mul_smul, hyfix]
    exact hyonly _ h
  have hgα : g • α = α := hzfix _ hzfixg
  have hg : g ∈ stabilizer X α := MulAction.mem_stabilizer_iff.mpr hgα
  have hcommg : g * z = z * g := (hzc g hg).eq
  change g * z * g⁻¹ = z
  rw [hcommg, mul_assoc, mul_inv_cancel, mul_one]

private theorem rankOneShult_fixed_le_stabilizer {X Ω : Type*} [Group X] [MulAction X Ω]
    {α : Ω} {F N : Subgroup X} [F.Normalizes N]
    (hFα : F ≤ stabilizer X α)
    (hFsemi : ∀ f ∈ F, ∀ β : Ω, f • β = β → β ≠ α → f = 1)
    (a : F) (ha1 : a ≠ 1) :
    fixedPointSubgroup (Subgroup.zpowers a) N ≤ (stabilizer X α).comap N.subtype := by
  intro y hy
  rw [Subgroup.mem_comap]
  rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
  have hsmul : (a : X) * (y : X) * (a : X)⁻¹ = (y : X) := by
    have hcoe := congrArg Subtype.val hy
    rwa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe F N a y] at hcoe
  have hay : (a : X) * (y : X) = (y : X) * (a : X) := by
    calc (a : X) * (y : X) = ((a : X) * (y : X) * (a : X)⁻¹) * (a : X) := by group
      _ = (y : X) * (a : X) := by rw [hsmul]
  rw [MulAction.mem_stabilizer_iff]
  by_contra hne
  have hfix : (a : X) • ((y : X) • α) = (y : X) • α := by
    calc (a : X) • ((y : X) • α) = ((a : X) * (y : X)) • α := (mul_smul ..).symm
      _ = ((y : X) * (a : X)) • α := by rw [hay]
      _ = (y : X) • ((a : X) • α) := mul_smul ..
      _ = (y : X) • α := by rw [MulAction.mem_stabilizer_iff.mp (hFα a.2)]
  have haX1 : (a : X) = 1 := hFsemi a a.2 ((y : X) • α) hfix hne
  exact ha1 (Subtype.ext haX1)

private theorem rankOneShult_normal_le_stabilizer {X Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω] {α : Ω} {F N : Subgroup X} (hN : N.Normal) (hNodd : Odd (Nat.card N))
    (hFα : F ≤ stabilizer X α) (hF2 : ∀ f ∈ F, f * f = 1) (hF4 : 4 ≤ Nat.card F)
    (hFsemi : ∀ f ∈ F, ∀ β : Ω, f • β = β → β ≠ α → f = 1) :
    N ≤ stabilizer X α := by
  classical
  haveI : N.Normal := hN
  have hFN : F ≤ Subgroup.normalizer (N : Set X) := by
    rw [Subgroup.normalizer_eq_top N]
    exact le_top
  haveI : F.Normalizes N := ⟨hFN⟩
  have hFcomm : ∀ a ∈ F, ∀ b ∈ F, Commute a b := by
    intro a ha b hb
    have hab : a * b ∈ F := F.mul_mem ha hb
    have hsq : (a * b) * (a * b) = 1 := hF2 (a * b) hab
    refine (commute_iff_eq a b).mpr ?_
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right hsq
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
          rw [inv_eq_of_mul_eq_one_right (hF2 a ha),
            inv_eq_of_mul_eq_one_right (hF2 b hb)]
  haveI : CFSG.IsElementaryAbelian 2 F :=
    CFSG.IsElementaryAbelian.two_of_forall_mul_self hFcomm hF2
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := F) (H := N)
    (by simpa using hF4) hNodd.not_two_dvd_nat
  have hle : (⊤ : Subgroup N) ≤ (stabilizer X α).comap N.subtype := by
    rw [← hgen]
    exact iSup_le fun a => iSup_le fun ha1 =>
      rankOneShult_fixed_le_stabilizer hFα hFsemi a ha1
  intro x hx
  have hx' : (⟨x, hx⟩ : N) ∈ (⊤ : Subgroup N) := Subgroup.mem_top _
  simpa using hle hx'

theorem false_of_central_involution_of_semiregular {X Ω : Type} [Group X] [Finite X]
    [MulAction X Ω] [IsPretransitive X Ω] {α : Ω} (hΩ : ∃ β : Ω, β ≠ α) {z : X}
    (hzα : z ∈ stabilizer X α) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hzc : ∀ g ∈ stabilizer X α, Commute g z) (hzfix : ∀ β : Ω, z • β = β → β = α)
    {F : Subgroup X} (hFα : F ≤ stabilizer X α) (hF2 : ∀ f ∈ F, f * f = 1)
    (hF4 : 4 ≤ Nat.card F) (hFsemi : ∀ f ∈ F, ∀ β : Ω, f • β = β → β ≠ α → f = 1) :
    False := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  have hiso := rankOneShult_isolated hzα hzc hzfix
  obtain ⟨N, hN, hNodd, hNmem⟩ := CFSG.ZStar.glauberman_zStar X z hz1 hz2 hiso
  have hNα : N ≤ stabilizer X α :=
    rankOneShult_normal_le_stabilizer hN hNodd hFα hF2 hF4 hFsemi
  obtain ⟨β, hβ⟩ := hΩ
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := X) α β
  have hzα' : z • α = α := MulAction.mem_stabilizer_iff.mp hzα
  have hzinv : z⁻¹ • α = α := by
    calc z⁻¹ • α = z⁻¹ • (z • α) := by rw [hzα']
      _ = α := inv_smul_smul z α
  have hall : ∀ x : X, x • α = α := by
    intro x
    have hmem : (x * z * x⁻¹) * z⁻¹ ∈ N := by simpa [mul_assoc] using hNmem x
    have hfix := MulAction.mem_stabilizer_iff.mp (hNα hmem)
    have hconj : (x * z * x⁻¹) • α = α := by
      rwa [mul_smul, hzinv] at hfix
    have h2 : z • (x⁻¹ • α) = x⁻¹ • α := by
      have h := congrArg (fun ω => x⁻¹ • ω) hconj
      simpa [mul_smul, mul_assoc] using h
    have hxinv : x⁻¹ • α = α := hzfix _ h2
    calc x • α = x • (x⁻¹ • α) := by rw [hxinv]
      _ = (x * x⁻¹) • α := (mul_smul x x⁻¹ α).symm
      _ = α := by rw [mul_inv_cancel, one_smul]
  exact hβ (by rw [← hg]; exact hall g)

private theorem rankOneShult_exists_ne_point {X Ω : Type*} [Group X] [MulAction X Ω]
    [FaithfulSMul X Ω] {α : Ω} {F : Subgroup X} (hF4 : 4 ≤ Nat.card F) :
    ∃ β : Ω, β ≠ α := by
  by_contra h
  have hsub : ∀ β : Ω, β = α := by
    intro β
    by_contra hne
    exact h ⟨β, hne⟩
  have hFbot : F = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro f hf
    rw [Subgroup.mem_bot]
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Ω) (m₁ := f) (m₂ := 1)
    intro ω
    calc f • ω = α := hsub _
      _ = (1 : X) • ω := by rw [one_smul, hsub ω]
  rw [hFbot, Subgroup.card_bot] at hF4
  omega

private theorem rankOneShult_card_F_add_one_le {X Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω] [Finite Ω] {α β : Ω} {F : Subgroup X} (hβne : β ≠ α)
    (hFα : F ≤ stabilizer X α) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFsemi : ∀ f ∈ F, ∀ ω : Ω, f • ω = ω → ω ≠ α → f = 1) :
    Nat.card F + 1 ≤ Nat.card Ω := by
  classical
  haveI : Nonempty Ω := ⟨α⟩
  have hinj : Function.Injective (fun f : F => f • β) := by
    intro f f' h
    let c : F := f'⁻¹ * f
    have h' : f • β = f' • β := h
    have hfix : c • β = β := by
      dsimp [c]
      rw [mul_smul, h']
      exact inv_smul_smul f' β
    have h1 : c = 1 := Subtype.ext (hFsemi (c : X) c.2 β hfix hβne)
    calc f = f' * c := by dsimp [c]; group
      _ = f' := by rw [h1, mul_one]
  have hnotmem : ∀ f : F, f • β ≠ α := by
    intro f hf
    apply hβne
    calc β = f⁻¹ • (f • β) := (inv_smul_smul f β).symm
      _ = f⁻¹ • α := by rw [hf]
      _ = α := MulAction.mem_stabilizer_iff.mp (hFα (f⁻¹).2)
  have himg : (Set.univ.image (fun f : F => f • β)).ncard = Nat.card F := by
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
  have hsub : Set.univ.image (fun f : F => f • β) ⊆ ({α}ᶜ : Set Ω) := by
    rintro ω ⟨f, -, rfl⟩
    exact hnotmem f
  have hle : Nat.card F ≤ ({α}ᶜ : Set Ω).ncard :=
    calc Nat.card F = (Set.univ.image (fun f : F => f • β)).ncard := himg.symm
      _ ≤ ({α}ᶜ : Set Ω).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_compl, Set.ncard_singleton] at hle
  have hpos : 0 < Nat.card Ω := Nat.card_pos
  omega

private theorem rankOneShult_ne_bot_of_orbit {X Ω : Type*} [Group X] [MulAction X Ω]
    {α β : Ω} {P : Subgroup X} {m : ℕ} (hm3 : 3 ≤ m) (hβne : β ≠ α)
    (horb : m ≤ (orbit P β).ncard) : P ≠ ⊥ := by
  intro hbot
  have hsing : orbit P β = {β} := by
    ext ω
    constructor
    · rintro ⟨p, hp⟩
      rw [Set.mem_singleton_iff]
      have hp1 : p = 1 := by
        apply Subtype.ext
        have hpbot : (p : X) ∈ (⊥ : Subgroup X) := by
          rw [← hbot]
          exact p.2
        simpa using hpbot
      have hpβ : p • β = β := by
        rw [hp1]
        exact one_smul P β
      rw [← hp]
      exact hpβ
    · intro hω
      rw [Set.mem_singleton_iff] at hω
      subst ω
      exact ⟨1, one_smul P β⟩
  rw [hsing, Set.ncard_singleton] at horb
  omega

private theorem rankOneShult_exists_central_involution {X : Type*} [Group X] [Finite X]
    {P : Subgroup X} (hPne : P ≠ ⊥) (hP2 : IsPGroup 2 P) :
    ∃ z : X, z ∈ P ∧ z ≠ 1 ∧ z * z = 1 ∧ ∀ y ∈ P, Commute z y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
  have hZ2 : IsPGroup 2 (Subgroup.center P) := hP2.to_subgroup (Subgroup.center P)
  have hZnt : Nontrivial (Subgroup.center P) := hP2.center_nontrivial
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ2
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have h1 : 1 < Nat.card (Subgroup.center P) :=
      Finite.one_lt_card_iff_nontrivial.mpr hZnt
    omega
  have hdvd : 2 ∣ Nat.card (Subgroup.center P) := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2 hdvd
  let z₀ : X := ((w : Subgroup.center P) : P)
  refine ⟨z₀, ?_, ?_, ?_, ?_⟩
  · exact (w : P).2
  · intro h
    have hP : (w : P) = 1 := Subtype.ext h
    have hC : (w : Subgroup.center P) = 1 := Subtype.ext hP
    rw [hC, orderOf_one] at hw
    omega
  · have h2 : (w : Subgroup.center P) ^ 2 = 1 := (orderOf_eq_prime_iff.mp hw).1
    have h2P : (w : P) ^ 2 = 1 := congrArg Subtype.val h2
    have h2X : z₀ ^ 2 = 1 := congrArg Subtype.val h2P
    simpa [pow_two] using h2X
  · intro y hy
    have hcomm : Commute (w : P) (⟨y, hy⟩ : P) :=
      (Subgroup.mem_center_iff.mp w.2 (⟨y, hy⟩ : P)).symm
    simpa [z₀] using (Submonoid.commute_coe_coe).mpr hcomm

private def rankOneShult_centralInvolutions {X : Type*} [Group X] (P : Subgroup X) :
    Subgroup X where
  carrier := {x | x ∈ P ∧ (∀ y ∈ P, Commute x y) ∧ x * x = 1}
  one_mem' := ⟨P.one_mem, fun y _ => Commute.one_left y, by simp⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨haP, haC, ha2⟩ := ha
    obtain ⟨hbP, hbC, hb2⟩ := hb
    refine ⟨P.mul_mem haP hbP, fun y hy => Commute.mul_left (haC y hy) (hbC y hy), ?_⟩
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [(haC b hbP).symm.eq]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  inv_mem' := by
    intro a ha
    obtain ⟨haP, haC, ha2⟩ := ha
    refine ⟨P.inv_mem haP, fun y hy => (haC y hy).inv_left, ?_⟩
    calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := (mul_inv_rev a a).symm
      _ = 1 := by rw [ha2, inv_one]

private theorem rankOneShult_mem_centralInvolutions {X : Type*} [Group X] {P : Subgroup X}
    {x : X} : x ∈ rankOneShult_centralInvolutions P ↔
      x ∈ P ∧ (∀ y ∈ P, Commute x y) ∧ x * x = 1 := Iff.rfl

private theorem rankOneShult_centralInvolutions_normalized {X Ω : Type*} [Group X]
    [MulAction X Ω] {α : Ω} {P : Subgroup X}
    (hPN : stabilizer X α ≤ normalizer (P : Set X)) :
    stabilizer X α ≤ normalizer (rankOneShult_centralInvolutions P : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [rankOneShult_mem_centralInvolutions] at hy ⊢
    refine ⟨?_, ?_, ?_⟩
    · exact (Subgroup.le_normalizer_iff.mp hPN) g hg y hy.1
    · intro p hp
      have hp' : g⁻¹ * p * g ∈ P := by
        simpa [inv_inv] using
          (Subgroup.le_normalizer_iff.mp hPN) g⁻¹ ((stabilizer X α).inv_mem hg) p hp
      have hcomm : Commute y (g⁻¹ * p * g) := hy.2.1 _ hp'
      have hconj := (Commute.conj_iff g).2 hcomm
      have heq : g * (g⁻¹ * p * g) * g⁻¹ = p := by group
      rwa [heq] at hconj
    · calc (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
        _ = 1 := by rw [hy.2.2]; simp
  · intro hy
    rw [rankOneShult_mem_centralInvolutions] at hy ⊢
    have hyy : y * y = 1 := by
      have h := congrArg (fun t => g⁻¹ * t * g) hy.2.2
      simpa [mul_assoc] using h
    refine ⟨?_, ?_, ?_⟩
    · have := (Subgroup.le_normalizer_iff.mp hPN) g⁻¹ ((stabilizer X α).inv_mem hg)
        (g * y * g⁻¹) hy.1
      simpa [inv_inv, mul_assoc] using this
    · intro p hp
      have hpq : g * p * g⁻¹ ∈ P :=
        (Subgroup.le_normalizer_iff.mp hPN) g hg p hp
      have hcomm : Commute (g * y * g⁻¹) (g * p * g⁻¹) := hy.2.1 _ hpq
      have hconj := (Commute.conj_iff g⁻¹).2 hcomm
      have hyeq : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      have hpeq : g⁻¹ * (g * p * g⁻¹) * g = p := by group
      simpa [hyeq, hpeq, inv_inv] using hconj
    · exact hyy

private theorem rankOneShult_false_of_small {X Ω : Type} [Group X] [Finite X]
    [MulAction X Ω] [IsPretransitive X Ω] {α : Ω} {z : X} (hΩ : ∃ β : Ω, β ≠ α)
    (hzα : z ∈ stabilizer X α) (hz1 : z ≠ 1) (hz2 : z * z = 1) {Y₀ : Subgroup X}
    (hzY : z ∈ Y₀) (hYα : Y₀ ≤ stabilizer X α)
    (hYN : stabilizer X α ≤ normalizer (Y₀ : Set X))
    (hYexp : ∀ y ∈ Y₀, y * y = 1)
    (hYsemi : ∀ y ∈ Y₀, ∀ β : Ω, y • β = β → β ≠ α → y = 1)
    (hsmall : ¬ 4 ≤ Nat.card Y₀) {F : Subgroup X} (hFα : F ≤ stabilizer X α)
    (hF2 : ∀ f ∈ F, f * f = 1) (hF4 : 4 ≤ Nat.card F)
    (hFsemi : ∀ f ∈ F, ∀ β : Ω, f • β = β → β ≠ α → f = 1) :
    False := by
  have hcz : ∀ g ∈ stabilizer X α, Commute g z := by
    intro g hg
    have hy : g * z * g⁻¹ ∈ Y₀ :=
      (Subgroup.le_normalizer_iff.mp hYN) g hg z hzY
    have hy1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have := congrArg (fun t => g⁻¹ * t * g) h
      simpa [mul_assoc] using this
    have heq : g * z * g⁻¹ = z := by
      by_contra hne
      apply hsmall
      apply four_le_natCard_of_mem (A := Y₀) hzY hy hz1 hy1
      · intro hzy
        apply hne
        have h := congrArg (fun t => z * t) hzy
        rw [← mul_assoc, hz2, one_mul, mul_one] at h
        exact h
      · exact hYexp _ hy
    rw [commute_iff_eq]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [heq]
  have hzfix : ∀ β : Ω, z • β = β → β = α := by
    intro β hβ
    by_contra hne
    exact hz1 (hYsemi z hzY β hβ hne)
  exact false_of_central_involution_of_semiregular (X := X) (Ω := Ω) (α := α) (z := z) (F := F)
    hΩ hzα hz1 hz2 hcz hzfix hFα hF2 hF4 hFsemi

private theorem rankOneShult_orbit_map_rangeRestrict {X Ω : Type*} [Group X] [MulAction X Ω]
    (P : Subgroup X) (β : Ω) :
    orbit (P.map (MulAction.toPermHom X Ω).rangeRestrict) β = orbit P β := by
  ext ω
  constructor
  · intro hω
    obtain ⟨p', hω'⟩ := hω
    obtain ⟨p, hp, hφ⟩ := Subgroup.mem_map.mp p'.2
    refine ⟨⟨p, hp⟩, ?_⟩
    change (⟨p, hp⟩ : P) • β = ω
    rw [Subgroup.smul_def, ← smul_rangeRestrict p β, hφ]
    exact hω'
  · intro hω
    obtain ⟨p, hω'⟩ := hω
    refine ⟨⟨(MulAction.toPermHom X Ω).rangeRestrict p,
      Subgroup.mem_map_of_mem _ p.2⟩, ?_⟩
    change (⟨(MulAction.toPermHom X Ω).rangeRestrict p,
      Subgroup.mem_map_of_mem _ p.2⟩ : P.map _) • β = ω
    rw [Subgroup.smul_def, smul_rangeRestrict]
    exact hω'

private theorem rankOneShult_four_le_card_map_rangeRestrict {X Ω : Type*} [Group X]
    [MulAction X Ω] [Finite Ω] {F : Subgroup X} (hF4 : ∃ β : Ω, 4 ≤ (orbit F β).ncard) :
    4 ≤ Nat.card (F.map (MulAction.toPermHom X Ω).rangeRestrict) := by
  obtain ⟨β, hβ⟩ := hF4
  have horb := rankOneShult_orbit_map_rangeRestrict F β
  rw [← horb] at hβ
  have hle : (orbit (F.map (MulAction.toPermHom X Ω).rangeRestrict) β).ncard ≤
      Nat.card (F.map (MulAction.toPermHom X Ω).rangeRestrict) := by
    have hset : (orbit (F.map (MulAction.toPermHom X Ω).rangeRestrict) β : Set Ω) =
        Set.range (fun f : F.map (MulAction.toPermHom X Ω).rangeRestrict => f • β) := by
      ext ω
      exact ⟨fun ⟨f, hf⟩ => ⟨f, hf⟩, fun ⟨f, hf⟩ => ⟨f, hf⟩⟩
    rw [hset, ← Nat.card_coe_set_eq]
    exact Finite.card_range_le _
  omega

section Certified


theorem exists_card_eq_two_pow_add_one_of_lt_sq {X Ω : Type} [Group X]
    [Finite X] [MulAction X Ω] [Finite Ω] [FaithfulSMul X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d) {α : Ω}
    {P : Subgroup X} (hPα : P ≤ stabilizer X α)
    (hPN : stabilizer X α ≤ normalizer (P : Set X)) (hP2 : IsPGroup 2 P) {m : ℕ}
    (horb : ∀ β : Ω, β ≠ α → m ≤ (orbit P β).ncard) (hlt : Nat.card Ω < m ^ 2 + 1)
    {F : Subgroup X} (hFα : F ≤ stabilizer X α) (hF2 : ∀ f ∈ F, f * f = 1)
    (hF4 : 4 ≤ Nat.card F) (hFsemi : ∀ f ∈ F, ∀ β : Ω, f • β = β → β ≠ α → f = 1) :
    ∃ e : ℕ, Nat.card Ω = 2 ^ e + 1 := by
  classical
  haveI : Nonempty Ω := ⟨α⟩
  obtain ⟨β, hβne⟩ := rankOneShult_exists_ne_point (Ω := Ω) (α := α) hF4
  have hFcard : Nat.card F + 1 ≤ Nat.card Ω :=
    rankOneShult_card_F_add_one_le hβne hFα hF2 hFsemi
  have hm3 : 3 ≤ m := by nlinarith [hF4, hFcard, hlt]
  have hPne : P ≠ ⊥ := rankOneShult_ne_bot_of_orbit (m := m) hm3 hβne (horb β hβne)
  obtain ⟨z, hzP, hz1, hz2, hzcP⟩ := rankOneShult_exists_central_involution hPne hP2
  let Y₀ : Subgroup X := rankOneShult_centralInvolutions P
  have hzY : z ∈ Y₀ := ⟨hzP, hzcP, hz2⟩
  have hYexp : ∀ y ∈ Y₀, y * y = 1 := fun y hy =>
    (rankOneShult_mem_centralInvolutions.mp hy).2.2
  have hYα : Y₀ ≤ stabilizer X α := fun y hy =>
    hPα (rankOneShult_mem_centralInvolutions.mp hy).1
  have hYN : stabilizer X α ≤ normalizer (Y₀ : Set X) :=
    rankOneShult_centralInvolutions_normalized hPN
  have hYsemi := CFSG.GroupTheory.ONan.semiregular_of_isPGroup_of_commute h2 hYα hYN
    (hP2.to_le fun y hy => (rankOneShult_mem_centralInvolutions.mp hy).1) hPα
    (fun x hx y hy => ((rankOneShult_mem_centralInvolutions.mp hy).2.1 x hx).symm) horb hlt
  haveI : MulAction.IsMultiplyPretransitive X Ω 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    exact h2 a b c d hab hcd
  haveI : IsPretransitive X Ω := MulAction.isPretransitive_of_is_two_pretransitive
  by_cases hY4 : 4 ≤ Nat.card Y₀
  · exact card_eq_two_pow_add_one_of_semiregular hYα hYN hYexp hY4 hYsemi
  · exact (rankOneShult_false_of_small (X := X) (Ω := Ω) (α := α) (z := z) (Y₀ := Y₀) (F := F)
      ⟨β, hβne⟩ (hPα hzP) hz1 hz2 hzY hYα hYN hYexp hYsemi hY4 hFα hF2 hF4 hFsemi).elim

theorem exists_card_eq_two_pow_add_one_of_lt_sq' {X : Type*} [Group X]
    {Ω : Type} [MulAction X Ω] [Finite Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d) {α : Ω}
    {P : Subgroup X} (hPα : P ≤ stabilizer X α)
    (hPN : stabilizer X α ≤ normalizer (P : Set X)) (hP2 : IsPGroup 2 P) {m : ℕ}
    (horb : ∀ β : Ω, β ≠ α → m ≤ (orbit P β).ncard) (hlt : Nat.card Ω < m ^ 2 + 1)
    {F : Subgroup X} (hFα : F ≤ stabilizer X α) (hF2 : ∀ f ∈ F, ∀ ω : Ω, (f * f) • ω = ω)
    (hF4 : ∃ β : Ω, 4 ≤ (orbit F β).ncard)
    (hFsemi : ∀ f ∈ F, ∀ β : Ω, f • β = β → β ≠ α → ∀ ω : Ω, f • ω = ω) :
    ∃ e : ℕ, Nat.card Ω = 2 ^ e + 1 := by
  classical
  let X' : Subgroup (Equiv.Perm Ω) := (MulAction.toPermHom X Ω).range
  let P' : Subgroup X' := P.map (MulAction.toPermHom X Ω).rangeRestrict
  let F' : Subgroup X' := F.map (MulAction.toPermHom X Ω).rangeRestrict
  haveI : Finite X' := inferInstance
  haveI : FaithfulSMul X' Ω := inferInstance
  have h2' : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X', g • a = c ∧ g • b = d := by
    intro a b c d hab hcd
    obtain ⟨g, hg1, hg2⟩ := h2 a b c d hab hcd
    exact ⟨(MulAction.toPermHom X Ω).rangeRestrict g, by
        rw [smul_rangeRestrict]; exact hg1, by
        rw [smul_rangeRestrict]; exact hg2⟩
  have horb' : ∀ β : Ω, β ≠ α → m ≤ (orbit P' β).ncard := by
    intro β hβ
    rw [show orbit P' β = orbit P β from
      rankOneShult_orbit_map_rangeRestrict P β]
    exact horb β hβ
  have hP2' : IsPGroup 2 P' := hP2.map (MulAction.toPermHom X Ω).rangeRestrict
  have hF2' : ∀ f ∈ F', f * f = 1 := by
    intro f' hf'
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hf'
    exact sq_rangeRestrict_eq_one hF2 hf
  obtain ⟨e, he⟩ := exists_card_eq_two_pow_add_one_of_lt_sq (X := X') (Ω := Ω) h2'
    (map_rangeRestrict_le_stabilizer hPα) (stabilizer_le_normalizer_map_rangeRestrict hPN)
    hP2' horb' hlt (map_rangeRestrict_le_stabilizer hFα)
    hF2' (rankOneShult_four_le_card_map_rangeRestrict hF4)
    (eq_one_of_map_rangeRestrict_semiregular hFsemi)
  exact ⟨e, he⟩

end Certified

end CFSG.OddTranspositions.PartFour
