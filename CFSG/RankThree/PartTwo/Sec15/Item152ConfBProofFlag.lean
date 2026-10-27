module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof152Flag

open CFSG.SectionRank.Ccomm
open scoped commutatorElement

section Power

variable {V : Type*} [Group V] [Finite V]

omit [Finite V] in
theorem exists_zpow_of_mapsTo (ℓ : Subgroup V) [IsCyclic ℓ] (σ : V →* V)
    (hσ : ∀ x ∈ ℓ, σ x ∈ ℓ) : ∃ m : ℤ, ∀ x ∈ ℓ, σ x = x ^ m := by
  let f : ℓ →* ℓ :=
    { toFun := fun x => ⟨σ (x : V), hσ x x.2⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : V) (y : V)) }
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic f
  refine ⟨m, fun x hx => ?_⟩
  have h := congrArg Subtype.val (hm ⟨x, hx⟩)
  simpa [f] using h

omit [Finite V] in
theorem exists_zpow_mod_of_mapsTo (ℓ : Subgroup V) [ℓ.Normal] [IsCyclic (V ⧸ ℓ)] (σ : V →* V)
    (hσ : ∀ x ∈ ℓ, σ x ∈ ℓ) : ∃ m : ℤ, ∀ w : V, (σ w)⁻¹ * w ^ m ∈ ℓ := by
  let f : V ⧸ ℓ →* V ⧸ ℓ := QuotientGroup.map ℓ ℓ σ (fun x hx => hσ x hx)
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic f
  refine ⟨m, fun w => ?_⟩
  have h : ((σ w : V) : V ⧸ ℓ) = (w : V ⧸ ℓ) ^ m := hm (w : V ⧸ ℓ)
  rw [← QuotientGroup.mk_zpow] at h
  exact QuotientGroup.eq.mp h

theorem inv_mapsTo_of_mapsTo (ℓ : Subgroup V) (σ : MulAut V) (hσ : ∀ x ∈ ℓ, σ x ∈ ℓ) :
    ∀ x ∈ ℓ, σ⁻¹ x ∈ ℓ := by
  let f : ℓ → ℓ := fun x => ⟨σ x, hσ x x.2⟩
  have hinj : Function.Injective f := fun x y hxy =>
    Subtype.ext (σ.injective (congrArg Subtype.val hxy))
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have h : σ y = x := congrArg Subtype.val hy
  have h' : σ⁻¹ x = y := by
    rw [← h]
    exact σ.symm_apply_apply y
  rw [h']
  exact y.2

end Power

section Flag

variable {V : Type*} [Group V]

@[expose] def flagFix (ℓ : Subgroup V) : Subgroup (MulAut V) where
  carrier := {α | (∀ x ∈ ℓ, α x = x) ∧ ∀ w, w⁻¹ * α w ∈ ℓ}
  mul_mem' := by
    rintro α β ⟨hα1, hα2⟩ ⟨hβ1, hβ2⟩
    refine ⟨fun x hx => ?_, fun w => ?_⟩
    · change α (β x) = x
      rw [hβ1 x hx, hα1 x hx]
    · change w⁻¹ * α (β w) ∈ ℓ
      have h := ℓ.mul_mem (hβ2 w) (hα2 (β w))
      simpa [mul_assoc] using h
  one_mem' := ⟨fun x _ => rfl, fun w => by simp⟩
  inv_mem' := by
    rintro α ⟨hα1, hα2⟩
    refine ⟨fun x hx => ?_, fun w => ?_⟩
    · have h := hα1 x hx
      calc α⁻¹ x = α⁻¹ (α x) := by rw [h]
        _ = x := α.symm_apply_apply x
    · set v := α⁻¹ w with hv
      have hw : α v = w := α.apply_symm_apply w
      have h := ℓ.inv_mem (hα2 v)
      rw [← hw]
      simpa [mul_assoc] using h

theorem pow_eq_one_of_mem_flagFix {ℓ : Subgroup V} {p : ℕ} (hexp : ∀ a : V, a ^ p = 1)
    {α : MulAut V} (hα : α ∈ flagFix ℓ) : α ^ p = 1 := by
  obtain ⟨hα1, hα2⟩ := hα
  have key : ∀ n : ℕ, ∀ w : V, (α ^ n) w = w * (w⁻¹ * α w) ^ n := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      have h1 : (α ^ (n + 1)) w = α ((α ^ n) w) := by rw [pow_succ']; rfl
      rw [h1, ih w, map_mul, map_pow, hα1 _ (hα2 w), pow_succ' (w⁻¹ * α w) n]
      simp only [mul_assoc, mul_inv_cancel_left]
  ext w
  rw [key p w, hexp, mul_one, MulAut.one_apply]

variable [Finite V]

theorem commutator_mem_flagFix {p : ℕ} [Fact p.Prime] (hcomm : ∀ a b : V, a * b = b * a)
    (hV : Nat.card V = p ^ 2) {ℓ : Subgroup V} (hℓ : Nat.card ℓ = p) {σ τ : MulAut V}
    (hσ : ∀ x ∈ ℓ, σ x ∈ ℓ) (hτ : ∀ x ∈ ℓ, τ x ∈ ℓ) : ⁅σ, τ⁆ ∈ flagFix ℓ := by
  have hp : p.Prime := Fact.out
  have hℓn : ℓ.Normal := ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
  have : IsCyclic ℓ := isCyclic_of_prime_card hℓ
  have hq : Nat.card (V ⧸ ℓ) = p := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ℓ
    rw [hV, hℓ, pow_two] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos h.symm
  have : IsCyclic (V ⧸ ℓ) := isCyclic_of_prime_card hq
  have hσ' := inv_mapsTo_of_mapsTo ℓ σ hσ
  have hτ' := inv_mapsTo_of_mapsTo ℓ τ hτ
  obtain ⟨a, ha0⟩ := exists_zpow_of_mapsTo ℓ σ.toMonoidHom hσ
  obtain ⟨b, hb0⟩ := exists_zpow_of_mapsTo ℓ τ.toMonoidHom hτ
  have ha : ∀ x ∈ ℓ, σ x = x ^ a := ha0
  have hb : ∀ x ∈ ℓ, τ x = x ^ b := hb0
  obtain ⟨a', ha'0⟩ := exists_zpow_mod_of_mapsTo ℓ σ.toMonoidHom hσ
  obtain ⟨b', hb'0⟩ := exists_zpow_mod_of_mapsTo ℓ τ.toMonoidHom hτ
  have ha' : ∀ w : V, (σ w)⁻¹ * w ^ a' ∈ ℓ := ha'0
  have hb' : ∀ w : V, (τ w)⁻¹ * w ^ b' ∈ ℓ := hb'0
  have hcom : ⁅σ, τ⁆ = σ * τ * σ⁻¹ * τ⁻¹ := commutatorElement_def σ τ
  refine ⟨fun x hx => ?_, fun w => ?_⟩
  ·
    set y := σ⁻¹ (τ⁻¹ x) with hy
    have hyℓ : y ∈ ℓ := hσ' _ (hτ' x hx)
    have h1 : σ (τ y) = τ (σ y) := by
      have hτy := hτ y hyℓ
      have hσy := hσ y hyℓ
      rw [ha _ hτy, hb _ hyℓ, hb _ hσy, ha _ hyℓ, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [hcom]
    change σ (τ y) = x
    rw [h1, hy]
    simp
  ·
    set y := σ⁻¹ (τ⁻¹ w) with hy
    have hwy : w = τ (σ y) := by rw [hy]; simp
    have hmk : ((σ (τ y) : V) : V ⧸ ℓ) = ((τ (σ y) : V) : V ⧸ ℓ) := by
      have hσq : ∀ v : V, ((σ v : V) : V ⧸ ℓ) = (v : V ⧸ ℓ) ^ a' := fun v => by
        rw [← QuotientGroup.mk_zpow]
        exact (QuotientGroup.eq.mpr (ha' v))
      have hτq : ∀ v : V, ((τ v : V) : V ⧸ ℓ) = (v : V ⧸ ℓ) ^ b' := fun v => by
        rw [← QuotientGroup.mk_zpow]
        exact (QuotientGroup.eq.mpr (hb' v))
      rw [hσq, hτq, hτq, hσq, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [hcom]
    change w⁻¹ * σ (τ y) ∈ ℓ
    rw [hwy]
    exact QuotientGroup.eq.mp hmk.symm

end Flag

section Line

variable {G : Type*} [Group G] [Finite G]

theorem false_of_invariant_line {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X P Z U : Subgroup G}
    (hP : IsPGroup p P) (hV : Nat.card (↥P ⧸ frattini ↥P) = p ^ 2) (N : Subgroup ↥X) [N.Normal]
    (hperf : Group.IsPerfect (↥X ⧸ N)) (h2 : 2 ∣ Nat.card (↥X ⧸ N)) (hZX : Z ≤ X)
    (hZP : Z ≤ Subgroup.normalizer (P : Set G))
    (hcov : (Z.subgroupOf X).map (QuotientGroup.mk' N) = ⊤)
    (hC : ∀ (x : G) (hx : x ∈ X), x ∈ Subgroup.centralizer (P : Set G) → (⟨x, hx⟩ : ↥X) ∈ N)
    (hZU : Z ≤ Subgroup.normalizer (U : Set G))
    (hℓ : Nat.card ((U.subgroupOf P).map (QuotientGroup.mk' (frattini ↥P))) = p) : False := by
  classical
  obtain ⟨hchar, hcomm, hexp⟩ := frattini_quotient_elementary hP
  set V := ↥P ⧸ frattini ↥P with hVdef
  set ℓ : Subgroup V := (U.subgroupOf P).map (QuotientGroup.mk' (frattini ↥P)) with hℓdef
  set NP := Subgroup.normalizer (P : Set G) with hNP
  let ρ : ↥NP →* MulAut ↥P := P.normalizerMonoidHom
  have hρ : ∀ (n : ↥NP) (u : ↥P), ((ρ n u : ↥P) : G) = n * u * (n : G)⁻¹ := fun _ _ => rfl
  let ψ : ↥NP →* MulAut V := (autQuotient (frattini ↥P)).comp ρ
  have hψ : ∀ (n : ↥NP) (u : ↥P), ψ n (u : V) = ((ρ n u : ↥P) : V) := fun _ _ => rfl
  have hpres : ∀ (z : G) (hz : z ∈ Z), ∀ x ∈ ℓ, ψ ⟨z, hZP hz⟩ x ∈ ℓ := by
    intro z hz x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hu' : u ∈ U.subgroupOf P := hu
    refine ⟨ρ ⟨z, hZP hz⟩ u, ?_, (hψ _ u).symm⟩
    show ρ ⟨z, hZP hz⟩ u ∈ U.subgroupOf P
    rw [Subgroup.mem_subgroupOf, hρ]
    exact (Subgroup.mem_normalizer_iff.mp (hZU hz) _).mp (Subgroup.mem_subgroupOf.mp hu')
  set D : Subgroup G := ((flagFix ℓ).comap ψ).map NP.subtype with hD
  have hZZ : ⁅Z, Z⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro z₁ hz₁ z₂ hz₂
    refine ⟨⁅(⟨z₁, hZP hz₁⟩ : ↥NP), ⟨z₂, hZP hz₂⟩⁆, ?_, ?_⟩
    · show _ ∈ (flagFix ℓ).comap ψ
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact commutator_mem_flagFix hcomm hV hℓ (hpres z₁ hz₁) (hpres z₂ hz₂)
    · simp [commutatorElement_def]
  have hDp : ∀ x ∈ D, ∃ k : ℕ, x ^ p ^ k ∈ Subgroup.centralizer (P : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    have h1 : ψ n ^ p = 1 := pow_eq_one_of_mem_flagFix hexp hn
    have h2 : ρ n ^ p ∈ (autQuotient (frattini ↥P)).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact h1
    obtain ⟨k, hk⟩ := isPGroup_ker_autQuotient_frattini hP ⟨_, h2⟩
    have hk' : (ρ n ^ p) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : ρ (n ^ p ^ (k + 1)) = 1 := by
      rw [map_pow, pow_succ', pow_mul]
      exact hk'
    refine ⟨k + 1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h4 := congrArg (fun α : MulAut ↥P => ((α ⟨u, hu⟩ : ↥P) : G)) h3
    simp only [MulAut.one_apply] at h4
    rw [hρ] at h4
    have h5 : ((n ^ p ^ (k + 1) : ↥NP) : G) = (n : G) ^ p ^ (k + 1) := by simp
    rw [h5] at h4
    calc u * (n : G) ^ p ^ (k + 1) = (n : G) ^ p ^ (k + 1) * u * ((n : G) ^ p ^ (k + 1))⁻¹ *
          (n : G) ^ p ^ (k + 1) := by rw [h4]
      _ = (n : G) ^ p ^ (k + 1) * u := by group
  have hXp : IsPGroup p (↥X ⧸ N) := by
    intro q
    have hq : q ∈ ⁅(Z.subgroupOf X).map (QuotientGroup.mk' N),
        (Z.subgroupOf X).map (QuotientGroup.mk' N)⁆ := by
      rw [hcov, ← commutator_def, hperf.commutator_eq_top]
      exact Subgroup.mem_top q
    rw [← Subgroup.map_commutator] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    have hxZ : (x : G) ∈ ⁅Z, Z⁆ := by
      have h := Subgroup.mem_map_of_mem X.subtype hx
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hZX] at h
      exact h
    obtain ⟨k, hk⟩ := hDp _ (hZZ hxZ)
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hxk : ((x ^ p ^ k : ↥X) : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.coe_pow]
      exact hk
    exact hC _ (x ^ p ^ k).2 hxk
  obtain ⟨m, hm⟩ := hXp.exists_card_eq
  rw [hm] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp
    (Nat.prime_two.dvd_of_dvd_pow h2)).symm

end Line

end CFSG.RankThree.PartTwo.Sec15.Proof152Flag
