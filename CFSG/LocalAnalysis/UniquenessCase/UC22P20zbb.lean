module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zb
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20z

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

section Aux

theorem uc22pwtb_mem_oPi {Y : Type} [Group Y] {E : Subgroup Y} (hE : IsMulCommutative E) {α : Set ℕ}
    {x : Y} (hx : x ∈ E) (hα : ∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∈ α) : x ∈ oPi α E := by
  haveI := hE
  have hz : zpowers x ≤ oPi α E := by
    refine le_iSup₂_of_le (zpowers x) ⟨?_, inferInstance, ?_⟩ le_rfl
    · rw [Subgroup.zpowers_le]
      exact hx
    · rintro p ⟨hp, hpd⟩
      rw [Nat.card_zpowers] at hpd
      exact hα p hp hpd
  exact hz (Subgroup.mem_zpowers x)

end Aux

section Elem

variable {X Γ : Type} [Group X] [Group Γ]

theorem uc22pwtb_exists_sylow [Finite X] {U A₁ : Subgroup X}
    (hUsyl : CFSG.ABGLocalTools.IsSylowOf 2 (U ⊓ A₁) A₁) :
    ∃ U' : Sylow 2 ↥A₁, (U' : Subgroup ↥A₁) = (U ⊓ A₁).subgroupOf A₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hUp, hUidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hUsyl
  exact ⟨(hUp.comap_subtype (K := A₁)).toSylow hUidx, rfl⟩

theorem uc22pwtb_map_normalizer {U A₁ : Subgroup X} :
    (normalizer (((U ⊓ A₁).subgroupOf A₁ : Subgroup ↥A₁) : Set ↥A₁)).map A₁.subtype =
      normalizer ((U ⊓ A₁ : Subgroup X) : Set X) ⊓ A₁ := by
  rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_right : U ⊓ A₁ ≤ A₁),
    Subgroup.subgroupOf_map_subtype]

@[expose] def uc22pwtRes2 (ρ : Γ →* MulAut X) (A₁ A₂ : Subgroup X) : ↥(uc22pwtStab2 ρ A₁ A₂) →* MulAut ↥A₁ :=
  (uc22pwtRes ρ A₁).comp (Subgroup.inclusion (inf_le_left : uc22pwtStab2 ρ A₁ A₂ ≤ uc22pwtStab ρ A₁))

theorem uc22pwt_elem_of_E [Finite X] {ρ : Γ →* MulAut X} {τ : Γ} {U A₁ A₂ : Subgroup X}
    (C : UC22pwtCtx ρ τ U A₁ A₂) (hq : CFSG.Open.IsQuasisimple ↥A₁) {n : ℕ} (hn : 2 < n)
    (hZ : ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → ¬ p ∣ Nat.card (Subgroup.center ↥A₁)) {m' : ℕ}
    {E : Subgroup ↥A₁} (hEU : E ≤ normalizer (((U ⊓ A₁).subgroupOf A₁ : Subgroup ↥A₁) : Set ↥A₁))
    (hEcyc : IsCyclic E) (hEsq : Squarefree (Nat.card E)) (hEodd : Odd (Nat.card E))
    (hEpi : piSet E = etaSet n)
    (hEinv : ∀ (g : ↥(uc22pwtStab2 ρ A₁ A₂)), ∀ x ∈ E,
      uc22pwtRes2 ρ A₁ A₂ g x ∈ E ⊔ (U ⊓ A₁).subgroupOf A₁)
    (hEα : ∀ (g : ↥(uc22pwtStab2 ρ A₁ A₂)), ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E,
      uc22pwtRes2 ρ A₁ A₂ g x * x⁻¹ ∈ (U ⊓ A₁).subgroupOf A₁)
    {w : ↥A₁} (hw2 : w ^ 2 = 1) (hwinv : ∀ x ∈ E, w * x * w⁻¹ = x⁻¹)
    (hwgen : normalizer (((U ⊓ A₁).subgroupOf A₁ : Subgroup ↥A₁) : Set ↥A₁) ⊔ Subgroup.zpowers w = ⊤) :
    ∃ (h w₁ : X) (m a b : ℕ), UC22pwtElem C h w₁ m a b {p : ℕ | p.Prime ∧ p ∣ 2 ^ m' - 1} ∧
      (∀ p : ℕ, p.Prime → (p ∣ m ↔ p ∣ 2 ^ n - 1)) ∧ ∃ h₀ : ↥A₁, h₀ ∈ E ∧ (h₀ : X) = h := by
  haveI := hEcyc
  obtain ⟨h₀, hh₀⟩ := IsCyclic.exists_generator (α := ↥E)
  have hord : orderOf h₀ = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hh₀
  have hE_eq : E = zpowers ((h₀ : ↥E) : ↥A₁) := by
    refine le_antisymm (fun x hx => ?_) ?_
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hh₀ ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]
      exact h₀.2
  set h : X := (((h₀ : ↥E) : ↥A₁) : X) with hh
  have hhA : h ∈ A₁ := ((h₀ : ↥E) : ↥A₁).2
  have hordh : orderOf h = Nat.card E := by
    rw [hh, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hord]
  have hEmap : E.map A₁.subtype = zpowers h := by
    rw [hE_eq, MonoidHom.map_zpowers]
    rfl
  have hU'map : ((U ⊓ A₁).subgroupOf A₁).map A₁.subtype = U ⊓ A₁ :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_right
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = Nat.card E := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = Nat.gcd m (2 ^ m' - 1) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = m / a := ⟨_, rfl⟩
  have hab : a * b = m := by
    rw [hb, ha]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hsqf : Squarefree m := by rw [hm]; exact hEsq
  have hm0 : 0 < m := by rw [hm]; exact Nat.card_pos
  have hbpos : 0 < b := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hab
    omega
  have hcop : Nat.Coprime a b := by
    have : Squarefree (a * b) := by rw [hab]; exact hsqf
    exact (Nat.squarefree_mul_iff.1 this).1
  have hprimes : ∀ p : ℕ, p.Prime → (p ∣ m ↔ p ∣ 2 ^ n - 1) := fun p hp => by
    rw [hm]
    exact ⟨fun hd => ((Set.ext_iff.1 hEpi p).1 ⟨hp, hd⟩).2,
      fun hd => ((Set.ext_iff.1 hEpi p).2 ⟨hp, hd⟩).2⟩
  have hbd : b ∣ orderOf h₀ := by
    rw [hord, ← hm]
    exact Dvd.intro_left a hab
  have hop : orderOf (h₀ ^ b) = a := by
    rw [orderOf_pow_of_dvd hbpos.ne' hbd, hord, ← hm]
    exact Nat.div_eq_of_eq_mul_left hbpos hab.symm
  have hxα : (((h₀ ^ b : ↥E) : ↥A₁)) ∈ oPi {p : ℕ | p.Prime ∧ p ∣ 2 ^ m' - 1} E := by
    refine uc22pwtb_mem_oPi (inferInstance : IsMulCommutative ↥E) (h₀ ^ b).2 fun p hp hpd => ?_
    rw [Subgroup.orderOf_coe, hop] at hpd
    exact ⟨hp, (Nat.dvd_gcd_iff.1 (ha ▸ hpd)).2⟩
  refine ⟨h, (w : X), m, a, b, ⟨hhA, by rw [hordh, hm], hsqf, by rw [hm]; exact hEodd, hab, hcop, ?_, ?_,
    ?_, ?_, ?_, ?_, w.2, ?_, ?_, ?_, fun K hKA hKn => uc22pwt_nc_of_quasisimple hq hKA hKn⟩,
    hprimes, (h₀ : ↥A₁), h₀.2, rfl⟩
  ·
    intro p hp hpm
    rw [ha]
    exact ⟨fun hpα => Nat.dvd_gcd hpm hpα.2, fun hpa => ⟨hp, (Nat.dvd_gcd_iff.1 hpa).2⟩⟩
  ·
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := 2 ^ n - 1) (by omega)
    exact ⟨p, hp, (hprimes p hp).2 hpd⟩
  ·
    exact fun p hp hpm => hZ p hp ((hprimes p hp).1 hpm)
  ·
    intro u hu
    have hhN : ((h₀ : ↥E) : ↥A₁) ∈ normalizer (((U ⊓ A₁).subgroupOf A₁ : Subgroup ↥A₁) : Set ↥A₁) :=
      hEU h₀.2
    have hu' : (⟨u, hu.2⟩ : ↥A₁) ∈ (U ⊓ A₁).subgroupOf A₁ := hu
    have h1 := (Subgroup.mem_normalizer_iff.1 hhN _).1 hu'
    have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hhN) _).1 hu'
    rw [inv_inv] at h2
    exact ⟨h1, h2⟩
  ·
    intro g hg
    have h1 := hEinv ⟨g, hg⟩ ((h₀ : ↥E) : ↥A₁) h₀.2
    have h2 : ((uc22pwtRes2 ρ A₁ A₂ ⟨g, hg⟩ ((h₀ : ↥E) : ↥A₁) : ↥A₁) : X) ∈
        (E ⊔ (U ⊓ A₁).subgroupOf A₁).map A₁.subtype := ⟨_, h1, rfl⟩
    rw [Subgroup.map_sup, hEmap, hU'map] at h2
    exact h2
  ·
    intro g hg
    have h1 := Subgroup.mem_subgroupOf.1 (hEα ⟨g, hg⟩ _ hxα)
    exact h1
  ·
    simpa using congrArg Subtype.val hw2
  ·
    simpa using congrArg Subtype.val (hwinv ((h₀ : ↥E) : ↥A₁) h₀.2)
  ·
    have h1 := congrArg (Subgroup.map A₁.subtype) hwgen
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_zpowers,
      uc22pwtb_map_normalizer] at h1
    exact h1

theorem uc22pwt_elem_of_input (hR1 : uc22pwCartanRankOne) [Finite X] (hΓ : IsPGroup 2 Γ)
    {ρ : Γ →* MulAut X} {τ : Γ} {U A₁ A₂ : Subgroup X} (C : UC22pwtCtx ρ τ U A₁ A₂)
    (hUsyl : CFSG.ABGLocalTools.IsSylowOf 2 (U ⊓ A₁) A₁) (hq : CFSG.Open.IsQuasisimple ↥A₁) {n : ℕ}
    (hn : 2 < n) (hsh : IsSz ↥A₁ n ∨ IsL2 ↥A₁ n ∨ IsSU3 ↥A₁ n)
    (hZ : ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → ¬ p ∣ Nat.card (Subgroup.center ↥A₁))
    {e m' : ℕ} (hm' : Odd m') (hnem : n = 2 ^ e * m') :
    ∃ (h w₁ : X) (m a b : ℕ), UC22pwtElem C h w₁ m a b {p : ℕ | p.Prime ∧ p ∣ 2 ^ m' - 1} ∧
      (∀ p : ℕ, p.Prime → (p ∣ m ↔ p ∣ 2 ^ n - 1)) := by
  obtain ⟨U', hU'⟩ := uc22pwtb_exists_sylow hUsyl
  let ψ : ↥(uc22pwtStab2 ρ A₁ A₂) →* MulAut ↥A₁ :=
    (uc22pwtRes ρ A₁).comp
      (Subgroup.inclusion (inf_le_left : uc22pwtStab2 ρ A₁ A₂ ≤ uc22pwtStab ρ A₁))
  have hUinv : ∀ (g : ↥(uc22pwtStab2 ρ A₁ A₂)) (x : ↥A₁),
      x ∈ (U' : Subgroup ↥A₁) ↔ ψ g x ∈ (U' : Subgroup ↥A₁) := by
    intro g x
    rw [hU', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact ⟨fun hx => ⟨(C.Uinv g x).1 hx.1, (ψ g x).2⟩, fun hx => ⟨(C.Uinv g x).2 hx.1, x.2⟩⟩
  obtain ⟨E, hEU, hEcyc, hEsq, hEodd, hEpi, hEinv, hEα, w, hw2, hwinv, hwgen⟩ :=
    hR1 ↥A₁ hq n hn hsh U' ↥(uc22pwtStab2 ρ A₁ A₂) (hΓ.to_subgroup _) ψ hUinv e m' hm' hnem
  rw [hU'] at hEU hEinv hEα hwgen
  obtain ⟨h, w₁, m, a, b, El, hpr, -⟩ :=
    uc22pwt_elem_of_E C hq hn hZ hEU hEcyc hEsq hEodd hEpi hEinv hEα hw2 hwinv hwgen
  exact ⟨h, w₁, m, a, b, El, hpr⟩

end Elem

end CFSG.LocalAnalysis.UniquenessCase.UC22
