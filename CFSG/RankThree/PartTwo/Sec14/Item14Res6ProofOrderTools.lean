module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Res6Order

open scoped Pointwise

theorem card_modEq_one_of_orbit_dvd {G α : Type*} [Group G] [MulAction G α] [Finite α] {m : ℕ}
    (a₀ : α) (ha₀ : ∀ g : G, g • a₀ = a₀)
    (h : ∀ a : α, a ≠ a₀ → m ∣ Nat.card (MulAction.orbit G a)) :
    Nat.card α ≡ 1 [MOD m] := by
  classical
  have : Finite (MulAction.orbitRel.Quotient G α) := Quotient.finite _
  have : Fintype (MulAction.orbitRel.Quotient G α) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits' G α), Nat.card_sigma]
  set ω₀ : MulAction.orbitRel.Quotient G α := Quotient.mk'' a₀ with hω₀
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ω₀)]
  have h0 : Nat.card ω₀.orbit = 1 := by
    have horb : ω₀.orbit = {a₀} := by
      rw [hω₀, MulAction.orbitRel.Quotient.orbit_mk]
      ext x
      simp only [MulAction.mem_orbit_iff, Set.mem_singleton_iff, ha₀]
      exact ⟨fun ⟨_, hg⟩ => hg.symm, fun hx => ⟨1, hx.symm⟩⟩
    rw [horb, Nat.card_unique]
  have h1 : m ∣ ∑ ω ∈ Finset.univ.erase ω₀, Nat.card ω.orbit := by
    refine Finset.dvd_sum fun ω hω => ?_
    have hωne : ω ≠ ω₀ := (Finset.mem_erase.mp hω).1
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
    refine h _ fun heq => hωne ?_
    rw [hω₀, ← heq]
    exact (Quotient.out_eq' ω).symm
  rw [h0]
  obtain ⟨t, ht⟩ := h1
  rw [ht]
  exact Nat.add_mul_mod_self_left 1 m t

theorem false_of_factorial_index_lt {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (K : Subgroup S) (hK : K ≠ ⊤) (hlt : (K.index).factorial < Nat.card S) : False := by
  classical
  set φ := MulAction.toPermHom S (S ⧸ K) with hφ
  rcases Subgroup.Normal.eq_bot_or_eq_top φ.ker with hbot | htop
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hbot
    have hle := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_perm, ← Subgroup.index_eq_card] at hle
    omega
  · apply hK
    rw [eq_top_iff]
    intro s _
    have hs : φ s = 1 := by
      rw [← MonoidHom.mem_ker, htop]
      exact Subgroup.mem_top s
    have h1 : (s : S ⧸ K) = ((1 : S) : S ⧸ K) := by
      have := congrArg (fun σ : Equiv.Perm (S ⧸ K) => σ ((1 : S) : S ⧸ K)) hs
      simpa [hφ, smul_eq_mul] using this
    rw [QuotientGroup.eq] at h1
    simpa using h1

theorem false_of_index_ten {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : Nat.card X = 604800) (H : Subgroup X) (hH : H.index = 10) : False := by
  classical
  have : Fintype (X ⧸ H) := Fintype.ofFinite _
  have hcard : Fintype.card (X ⧸ H) = 10 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hH]
  set φ := MulAction.toPermHom X (X ⧸ H) with hφ
  have hinj : Function.Injective φ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top φ.ker with hbot | htop
    · exact (MonoidHom.ker_eq_bot_iff φ).mp hbot
    · exfalso
      have hHtop : H = ⊤ := by
        rw [eq_top_iff]
        intro s _
        have hs : φ s = 1 := by
          rw [← MonoidHom.mem_ker, htop]
          exact Subgroup.mem_top s
        have h1 : (s : X ⧸ H) = ((1 : X) : X ⧸ H) := by
          have := congrArg (fun σ : Equiv.Perm (X ⧸ H) => σ ((1 : X) : X ⧸ H)) hs
          simpa [hφ, smul_eq_mul] using this
        rw [QuotientGroup.eq] at h1
        simpa using h1
      rw [hHtop, Subgroup.index_top] at hH
      omega
  set ψ := (Equiv.Perm.sign : Equiv.Perm (X ⧸ H) →* ℤˣ).comp φ with hψ
  have hsign : ∀ x : X, φ x ∈ alternatingGroup (X ⧸ H) := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ψ.ker with hbot | htop
    · exfalso
      have hinjψ : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hbot
      have hle := Nat.card_le_card_of_injective ψ hinjψ
      have h2 : Nat.card ℤˣ = 2 := by
        rw [Nat.card_eq_fintype_card]
        rfl
      rw [hX, h2] at hle
      omega
    · intro x
      rw [Equiv.Perm.mem_alternatingGroup]
      have : x ∈ ψ.ker := by rw [htop]; exact Subgroup.mem_top x
      exact this
  set θ : X →* alternatingGroup (X ⧸ H) := φ.codRestrict _ hsign with hθ
  have hθinj : Function.Injective θ := fun a b hab =>
    hinj (congrArg Subtype.val hab)
  have hnt : Nontrivial (X ⧸ H) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hcard]
    norm_num
  have hA : Nat.card (alternatingGroup (X ⧸ H)) = 1814400 := by
    have h2 := two_mul_card_alternatingGroup (α := X ⧸ H)
    rw [Fintype.card_perm, hcard] at h2
    rw [Nat.card_eq_fintype_card]
    have : (10 : ℕ).factorial = 3628800 := by decide
    omega
  have hsimple : IsSimpleGroup (alternatingGroup (X ⧸ H)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, hcard]; norm_num)
  set R := θ.range with hR
  have hRcard : Nat.card R = 604800 := by
    rw [hR, ← hX]
    exact (Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv).symm
  have hRidx : R.index = 3 := by
    have h := R.card_mul_index
    rw [hRcard, hA] at h
    omega
  refine false_of_factorial_index_lt R ?_ ?_
  · intro htop
    rw [htop, Subgroup.index_top] at hRidx
    omega
  · rw [hRidx, hA]
    decide

theorem exists_ne_one_commute_of_card_mod_three {K : Type*} [Group K] [Finite K]
    {Q F : Subgroup K} (hQ : IsPGroup 3 Q) (hF : Nat.card F % 3 = 2)
    (hQF : Q ≤ Subgroup.normalizer (F : Set K)) :
    ∃ f ∈ F, f ≠ 1 ∧ ∀ q ∈ Q, q * f = f * q := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : ∀ (q : Q) (f : F), (q : K) * f * (q : K)⁻¹ ∈ F := fun q f =>
    (Subgroup.mem_normalizer_iff.mp (hQF q.2) f).mp f.2
  let _ : MulAction Q F :=
    { smul := fun q f => ⟨(q : K) * f * (q : K)⁻¹, hmem q f⟩
      one_smul := fun f => Subtype.ext (by
        change ((1 : Q) : K) * f * ((1 : Q) : K)⁻¹ = f
        simp)
      mul_smul := fun q r f => Subtype.ext (by
        change ((q : K) * r) * f * ((q : K) * r)⁻¹ =
          (q : K) * ((r : K) * f * (r : K)⁻¹) * (q : K)⁻¹
        group) }
  have hmod := hQ.card_modEq_card_fixedPoints F
  have hfix : 2 ≤ Nat.card (MulAction.fixedPoints Q F) := by
    have h1 : 1 ∈ MulAction.fixedPoints Q F := fun q => Subtype.ext (by
      change (q : K) * 1 * (q : K)⁻¹ = 1
      group)
    have hpos : 0 < Nat.card (MulAction.fixedPoints Q F) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
    have : Nat.card (MulAction.fixedPoints Q F) % 3 = 2 := by
      rw [Nat.ModEq] at hmod
      omega
    omega
  obtain ⟨⟨f, hf⟩, hf1⟩ : ∃ f : MulAction.fixedPoints Q F, (f : F) ≠ 1 := by
    by_contra hall
    push Not at hall
    have hsub : Subsingleton (MulAction.fixedPoints Q F) :=
      ⟨fun a b => Subtype.ext ((hall a).trans (hall b).symm)⟩
    have := Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  refine ⟨f, f.2, fun h => hf1 (Subtype.ext h), fun q hq => ?_⟩
  have h2 : (⟨q, hq⟩ : Q) • f = f := hf ⟨q, hq⟩
  have h3 : q * f * q⁻¹ = f := congrArg Subtype.val h2
  calc q * f = q * f * q⁻¹ * q := by group
    _ = f * q := by rw [h3]

theorem le_centralizer_of_card_three {K : Type*} [Group K] [Finite K] {Q F : Subgroup K}
    (hQ : IsPGroup 3 Q) (hF : Nat.card F = 3) (hQF : Q ≤ Subgroup.normalizer (F : Set K)) :
    Q ≤ Subgroup.centralizer (F : Set K) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : ∀ (q : Q) (f : F), (q : K) * f * (q : K)⁻¹ ∈ F := fun q f =>
    (Subgroup.mem_normalizer_iff.mp (hQF q.2) f).mp f.2
  let _ : MulAction Q F :=
    { smul := fun q f => ⟨(q : K) * f * (q : K)⁻¹, hmem q f⟩
      one_smul := fun f => Subtype.ext (by
        change ((1 : Q) : K) * f * ((1 : Q) : K)⁻¹ = f
        simp)
      mul_smul := fun q r f => Subtype.ext (by
        change ((q : K) * r) * f * ((q : K) * r)⁻¹ =
          (q : K) * ((r : K) * f * (r : K)⁻¹) * (q : K)⁻¹
        group) }
  have hmod := hQ.card_modEq_card_fixedPoints F
  have h1 : (1 : F) ∈ MulAction.fixedPoints Q F := fun q => Subtype.ext (by
    change (q : K) * 1 * (q : K)⁻¹ = 1
    group)
  have hpos : 0 < Nat.card (MulAction.fixedPoints Q F) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
  have hle : Nat.card (MulAction.fixedPoints Q F) ≤ Nat.card F :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have hfix : Nat.card (MulAction.fixedPoints Q F) = Nat.card F := by
    rw [Nat.ModEq] at hmod
    omega
  have hall : MulAction.fixedPoints Q F = Set.univ := by
    have := Set.eq_of_subset_of_ncard_le (Set.subset_univ (MulAction.fixedPoints Q F))
      (by rw [Set.ncard_univ, ← Nat.card_coe_set_eq, hfix]) (Set.toFinite _)
    exact this
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hfix' : (⟨f, hf⟩ : F) ∈ MulAction.fixedPoints Q F := hall ▸ Set.mem_univ _
  have h2 : (q : K) * f * q⁻¹ = f := congrArg Subtype.val (hfix' ⟨q, hq⟩)
  calc f * q = q * f * q⁻¹ * q := by rw [h2]
    _ = q * f := by group

theorem exists_normal_isPGroup_of_isSolvable {H : Type*} [Group H] [Finite H] [Nontrivial H]
    (hs : Group.IsSolvable H) :
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card H ∧ ∃ U : Subgroup H, U.Normal ∧ U ≠ ⊥ ∧ IsPGroup p U := by
  classical
  have hex : ∃ n : ℕ, derivedSeries H n = ⊥ := hs.solvable
  set m := Nat.find hex with hm
  have hmbot : derivedSeries H m = ⊥ := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, derivedSeries_zero] at hmbot
    exact (top_ne_bot (α := Subgroup H)) hmbot
  obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  set A := derivedSeries H j with hA
  have hAne : A ≠ ⊥ := Nat.find_min hex (by omega)
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have hc := Subgroup.commutator_mem_commutator ha hb
    rw [← derivedSeries_succ, ← hj, hmbot] at hc
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := Subgroup.mem_bot.1 hc
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  have hA1 : Nat.card A ≠ 1 := by
    intro h
    exact hAne (Subgroup.eq_bot_of_card_eq A h)
  obtain ⟨p, hp, hpA⟩ := Nat.exists_prime_and_dvd hA1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨a, haA⟩, ha⟩ := exists_prime_orderOf_dvd_card' p hpA
  have ha' : orderOf a = p := by rw [← ha, Subgroup.orderOf_mk]
  let U : Subgroup H :=
    { carrier := {x | x ∈ A ∧ x ^ p = 1}
      one_mem' := ⟨A.one_mem, one_pow p⟩
      mul_mem' := by
        rintro x y ⟨hxA, hx⟩ ⟨hyA, hy⟩
        refine ⟨A.mul_mem hxA hyA, ?_⟩
        rw [(Commute.mul_pow (hAcomm x hxA y hyA) p), hx, hy, one_mul]
      inv_mem' := by
        rintro x ⟨hxA, hx⟩
        exact ⟨A.inv_mem hxA, by rw [inv_pow, hx, inv_one]⟩ }
  refine ⟨p, hp, hpA.trans (Subgroup.card_subgroup_dvd_card A), U, ⟨fun x hx g => ?_⟩, ?_, ?_⟩
  · obtain ⟨hxA, hx⟩ := hx
    refine ⟨(inferInstance : A.Normal).conj_mem x hxA g, ?_⟩
    rw [conj_pow, hx, mul_one, mul_inv_cancel]
  · intro hbot
    have haU : a ∈ U := ⟨haA, by rw [← ha', pow_orderOf_eq_one]⟩
    rw [hbot, Subgroup.mem_bot] at haU
    rw [haU, orderOf_one] at ha'
    exact hp.one_lt.ne ha'
  · intro x
    exact ⟨1, Subtype.ext (by simpa using x.2.2)⟩

variable {G : Type*} [Group G]

theorem conjugate_conjugate (H : Subgroup G) (a b : G) :
    conjugate (conjugate H a) b = conjugate H (a * b) := by
  ext x
  simp only [conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by group⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨a⁻¹ * y * a⁻¹⁻¹, ⟨y, hy, rfl⟩, by group⟩

theorem conjugate_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : conjugate H g = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hg)

theorem card_conjugate (H : Subgroup G) (g : G) : Nat.card (conjugate H g) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjugate_le_of_le_map {H K : Subgroup G} {g : G}
    (h : H ≤ K.map (MulAut.conj g).toMonoidHom) : conjugate H g ≤ K := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, hk, hkx⟩ := h hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hkx ⊢
  rw [← hkx]
  simpa [mul_assoc] using hk

theorem conjugate_eq_iff_mem_normalizer {H : Subgroup G} {g : G} :
    conjugate H g = H ↔ g ∈ Subgroup.normalizer (H : Set G) := by
  refine ⟨fun h => ?_, conjugate_eq_of_mem_normalizer⟩
  have h1 : g⁻¹ ∈ Subgroup.normalizer (H : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  simpa using inv_mem h1

theorem conjugate_injective {H K : Subgroup G} {g : G} (h : conjugate H g = conjugate K g) :
    H = K := by
  have h1 := congrArg (fun L => conjugate L g⁻¹) h
  simp only [conjugate_conjugate, mul_inv_cancel] at h1
  have e : ∀ L : Subgroup G, conjugate L 1 = L := fun L => by
    ext x
    simp [conjugate]
  rwa [e, e] at h1

end Res6Order

end CFSG.RankThree.PartTwo.Sec14
