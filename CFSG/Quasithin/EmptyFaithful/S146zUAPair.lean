module

public import CFSG.Quasithin.EmptyFaithful.S146zMRk

public section

namespace CFSG.Quasithin.S146zU.UA

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.SectionRank

section Group

theorem mem_zpowers_of_not_dvd_sq {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime)
    (hΓ : ¬ p ^ 2 ∣ Nat.card Γ) {c d : Γ} (hc : c ^ p = 1) (hd : d ^ p = 1)
    (hcd : c * d = d * c) (hc1 : c ≠ 1) : d ∈ Subgroup.zpowers c := by
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers d, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute c d from hcd) m n).eq
  have hA : IsElemAbelian p (Subgroup.zpowers c ⊔ Subgroup.zpowers d) :=
    zmElemAbelian_sup (zmElemAbelian_zpowers hc) (zmElemAbelian_zpowers hd) hcomm
  set A : Subgroup Γ := Subgroup.zpowers c ⊔ Subgroup.zpowers d with hAdef
  have hAp : IsPGroup p ↥A := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hA.2 g g.2⟩
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hdvd : Nat.card A ∣ Nat.card Γ := Subgroup.card_subgroup_dvd_card A
  have hn1 : n ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ n := by omega
    exact hΓ ((pow_dvd_pow p h2).trans (hn ▸ hdvd))
  have hcard : Nat.card (Subgroup.zpowers c) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hc hc1
  have hle : Subgroup.zpowers c ≤ A := le_sup_left
  have hAc : Nat.card A ≤ Nat.card (Subgroup.zpowers c) := by
    rw [hn, hcard]
    calc p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hn1
      _ = p := pow_one p
  have heq : Subgroup.zpowers c = A := Subgroup.eq_of_le_of_card_ge hle hAc
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)

end Group

section Lift

variable {p : ℕ} [hp : Fact p.Prime] {X : Type*} [Group X] [Finite X]

theorem exists_lift_of_elemAbelian (N : Subgroup X) [N.Normal] (hN : ¬ p ∣ Nat.card N)
    {A : Subgroup (X ⧸ N)} (hA : IsElemAbelian p A) :
    ∃ E : Subgroup X, IsElemAbelian p E ∧ ∀ a ∈ A, ∃ e ∈ E, (e : X ⧸ N) = a := by
  have hAp : IsPGroup p ↥A := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hA.2 g g.2⟩
  obtain ⟨k, hcard⟩ := hAp.exists_card_eq
  have hcop : ∀ {k : ℕ}, Nat.Coprime (p ^ k) (Nat.card N) := fun {k} =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN)
  set P : Subgroup X := A.comap (QuotientGroup.mk' N)
  have hPcard : Nat.card P = Nat.card N * p ^ k := by
    rw [← hcard]
    exact QuotientGroup.card_preimage_mk N (A : Set (X ⧸ N))
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p P))
  have hScard : Nat.card S = p ^ k := by
    rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero _ hp.out.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_pow hp.out,
      Finsupp.single_eq_same, zero_add]
  set ι : S →* X := P.subtype.comp (S : Subgroup P).subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  set φ : S →* A := ((QuotientGroup.mk' N).comp ι).codRestrict A fun s => s.1.2
  have hker : ∀ s : S, ι s ∈ N → s = 1 := by
    intro s hs
    have hdisj := Subgroup.disjoint_of_coprime_natCard (H := (S : Subgroup P).map P.subtype)
      (K := N) (by
        rw [Subgroup.card_map_of_injective Subtype.val_injective, hScard]
        exact hcop)
    have h1 : ι s ∈ (S : Subgroup P).map P.subtype ⊓ N := ⟨⟨s, s.2, rfl⟩, hs⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h2 : (QuotientGroup.mk' N) (ι s) = 1 := congrArg Subtype.val hs
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact (Subgroup.mem_bot).2 (hker s h2)
  have hφb : Function.Bijective φ :=
    hφ.bijective_of_nat_card_le (by rw [hcard, hScard])
  have hAc := hA.1
  obtain ⟨hcomm, hpow⟩ := comm_pow_of_injective (p := p) hφ (fun a b => mul_comm' _ _)
    (fun a => Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hA.2 _ (φ a).2))
  refine ⟨ι.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, fun a ha => ?_⟩
  · obtain ⟨s, hs⟩ := a.2
    obtain ⟨u, hu⟩ := b.2
    apply Subtype.ext
    show (a : X) * b = b * a
    rw [← hs, ← hu, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨s, rfl⟩ := hx
    rw [← map_pow, hpow, map_one]
  · obtain ⟨s, hs⟩ := hφb.2 ⟨a, ha⟩
    refine ⟨ι s, ⟨s, rfl⟩, ?_⟩
    have := congrArg Subtype.val hs
    exact this

end Lift

section Pair

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G}
  {t : G}

theorem exists_commuting_pair (hp : p.Prime) (hp2 : p ≠ 2) (h : IsDecP T M H p H₀ H₁ H₂ t)
    (φ₁ : ↥H₁ →* DihedralGroup p) (hs₁ : Function.Surjective φ₁)
    (hker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H)
    (φ₂ : ↥H₂ →* DihedralGroup p) (hs₂ : Function.Surjective φ₂)
    (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) :
    ∃ (x y : G) (hx : x ∈ H₁) (hy : y ∈ H₂), φ₁ ⟨x, hx⟩ = DihedralGroup.r 1 ∧
      φ₂ ⟨y, hy⟩ = DihedralGroup.r 1 ∧ x ^ p = 1 ∧ y ^ p = 1 ∧ x * y = y * x ∧
      y ∉ Subgroup.zpowers x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a₁, ha₁⟩ := hs₁ (DihedralGroup.r 1)
  obtain ⟨a₂, ha₂⟩ := hs₂ (DihedralGroup.r 1)
  have ha₁H : (a₁ : G) ∈ H := h.le (h.le₁ a₁.2)
  have ha₂H : (a₂ : G) ∈ H := h.le (h.le₂ a₂.2)
  have hrot : ∀ {Hi : Subgroup G} (φ : ↥Hi →* DihedralGroup p)
      (hker : ∀ y : ↥Hi, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) (a : ↥Hi),
      φ a = DihedralGroup.r 1 → (a : G) ∉ pCoreOf 2 H ∧ (a : G) ^ p ∈ pCoreOf 2 H := by
    intro Hi φ hker a ha
    refine ⟨fun hQ => ?_, ?_⟩
    · have := (hker a).mpr hQ
      rw [ha] at this
      have h1 : (DihedralGroup.r (1 : ZMod p)) = DihedralGroup.r 0 := this
      exact one_ne_zero (DihedralGroup.r.inj h1)
    · have h1 : φ (a ^ p) = 1 := by rw [map_pow, ha]; exact DihedralGroup.r_one_pow_n
      simpa using (hker _).mp h1
  obtain ⟨haQ₁, hap₁⟩ := hrot φ₁ hker₁ a₁ ha₁
  obtain ⟨haQ₂, hap₂⟩ := hrot φ₂ hker₂ a₂ ha₂
  set α₁ := piQ H ⟨(a₁ : G), ha₁H⟩ with hα₁
  set α₂ := piQ H ⟨(a₂ : G), ha₂H⟩ with hα₂
  have hα₂ne : α₂ ≠ 1 := fun e => haQ₂ ((piQ_eq_one_iff H _).mp e)
  have hα₁p : α₁ ^ p = 1 := by
    rw [hα₁, ← map_pow]
    exact (piQ_eq_one_iff H _).mpr (by simpa using hap₁)
  have hα₂p : α₂ ^ p = 1 := by
    rw [hα₂, ← map_pow]
    exact (piQ_eq_one_iff H _).mpr (by simpa using hap₂)
  have hα₁α₂ : α₁ * α₂ = α₂ * α₁ := by
    have h1 : (a₁ : G) * (a₂ : G) * (a₁ : G)⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H :=
      h.comm (Subgroup.commutator_mem_commutator a₁.2 a₂.2)
    exact mul_inv_eq_iff_eq_mul.mp ((cent_iff ha₁H ha₂H).mp h1)
  have hcomm : ∀ x ∈ Subgroup.zpowers α₁, ∀ y ∈ Subgroup.zpowers α₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute α₁ α₂ from hα₁α₂) m n).eq
  have hinf : Subgroup.zpowers α₁ ⊓ Subgroup.zpowers α₂ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers (x := α₁) (y := y)).mpr hy.1
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers (x := α₂) (y := y)).mpr hy.2
    have hm' : α₁ ^ m = y := hm
    have hn' : α₂ ^ n = y := hn
    have hmn : piQ H ⟨(a₁ : G) ^ m, H.pow_mem ha₁H m⟩ =
        piQ H ⟨(a₂ : G) ^ n, H.pow_mem ha₂H n⟩ := by
      have e1 : (⟨(a₁ : G) ^ m, H.pow_mem ha₁H m⟩ : ↥H) = ⟨(a₁ : G), ha₁H⟩ ^ m := rfl
      have e2 : (⟨(a₂ : G) ^ n, H.pow_mem ha₂H n⟩ : ↥H) = ⟨(a₂ : G), ha₂H⟩ ^ n := rfl
      rw [e1, e2, map_pow, map_pow, ← hα₁, ← hα₂, hm', hn']
    have hq : ((⟨(a₁ : G) ^ m, H.pow_mem ha₁H m⟩ : ↥H)⁻¹ *
        ⟨(a₂ : G) ^ n, H.pow_mem ha₂H n⟩ : ↥H) ∈ (pCoreOf 2 H).subgroupOf H :=
      QuotientGroup.eq.mp hmn
    have hqQ : ((a₁ : G) ^ m)⁻¹ * (a₂ : G) ^ n ∈ pCoreOf 2 H := hq
    have hv₂ : (a₂ : G) ^ n ∈ H₂ := H₂.pow_mem a₂.2 n
    have hv₁ : (a₂ : G) ^ n ∈ H₁ := by
      have e : (a₂ : G) ^ n = (a₁ : G) ^ m * (((a₁ : G) ^ m)⁻¹ * (a₂ : G) ^ n) := by group
      rw [e]
      exact H₁.mul_mem (H₁.pow_mem a₁.2 m) (h.Q₁ hqQ)
    have hvQ : (a₂ : G) ^ n ∈ pCoreOf 2 H := by
      have : (a₂ : G) ^ n ∈ H₁ ⊓ H₂ := ⟨hv₁, hv₂⟩
      rwa [h.inf] at this
    rw [← hn']
    have e3 : α₂ ^ n = piQ H ⟨(a₂ : G) ^ n, H.pow_mem ha₂H n⟩ := by
      have e2 : (⟨(a₂ : G) ^ n, H.pow_mem ha₂H n⟩ : ↥H) = ⟨(a₂ : G), ha₂H⟩ ^ n := rfl
      rw [e2, map_pow]
    rw [e3]
    exact (piQ_eq_one_iff H _).mpr hvQ
  have hAel : IsElemAbelian p (Subgroup.zpowers α₁ ⊔ Subgroup.zpowers α₂) :=
    zmElemAbelian_sup (zmElemAbelian_zpowers hα₁p) (zmElemAbelian_zpowers hα₂p) hcomm
  have hQcard : ¬ p ∣ Nat.card ((pCoreOf 2 H).subgroupOf H) := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).exists_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).toEquiv, hk]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨E₀, hE₀, hE₀l⟩ := exists_lift_of_elemAbelian ((pCoreOf 2 H).subgroupOf H) hQcard hAel
  obtain ⟨x₀, hx₀E, hx₀⟩ := hE₀l α₁ (Subgroup.mem_sup_left (Subgroup.mem_zpowers α₁))
  obtain ⟨y₀, hy₀E, hy₀⟩ := hE₀l α₂ (Subgroup.mem_sup_right (Subgroup.mem_zpowers α₂))
  have hxa : ((x₀ : ↥H) : G)⁻¹ * (a₁ : G) ∈ pCoreOf 2 H := by
    have := QuotientGroup.eq.mp (hx₀.trans (rfl : α₁ = QuotientGroup.mk ⟨(a₁ : G), ha₁H⟩))
    exact this
  have hya : ((y₀ : ↥H) : G)⁻¹ * (a₂ : G) ∈ pCoreOf 2 H := by
    have := QuotientGroup.eq.mp (hy₀.trans (rfl : α₂ = QuotientGroup.mk ⟨(a₂ : G), ha₂H⟩))
    exact this
  have hx₁ : ((x₀ : ↥H) : G) ∈ H₁ := by
    have e : ((x₀ : ↥H) : G) = (a₁ : G) * (((x₀ : ↥H) : G)⁻¹ * (a₁ : G))⁻¹ := by group
    rw [e]
    exact H₁.mul_mem a₁.2 (H₁.inv_mem (h.Q₁ hxa))
  have hy₁ : ((y₀ : ↥H) : G) ∈ H₂ := by
    have e : ((y₀ : ↥H) : G) = (a₂ : G) * (((y₀ : ↥H) : G)⁻¹ * (a₂ : G))⁻¹ := by group
    rw [e]
    exact H₂.mul_mem a₂.2 (H₂.inv_mem (h.Q₂ hya))
  have hφx : φ₁ ⟨((x₀ : ↥H) : G), hx₁⟩ = DihedralGroup.r 1 := by
    have e : (⟨((x₀ : ↥H) : G), hx₁⟩ : ↥H₁) =
        a₁ * ⟨(((x₀ : ↥H) : G)⁻¹ * (a₁ : G))⁻¹, H₁.inv_mem (h.Q₁ hxa)⟩ := by
      apply Subtype.ext
      show ((x₀ : ↥H) : G) = (a₁ : G) * (((x₀ : ↥H) : G)⁻¹ * (a₁ : G))⁻¹
      group
    rw [e, map_mul, ha₁, (hker₁ _).mpr ((pCoreOf 2 H).inv_mem hxa), mul_one]
  have hφy : φ₂ ⟨((y₀ : ↥H) : G), hy₁⟩ = DihedralGroup.r 1 := by
    have e : (⟨((y₀ : ↥H) : G), hy₁⟩ : ↥H₂) =
        a₂ * ⟨(((y₀ : ↥H) : G)⁻¹ * (a₂ : G))⁻¹, H₂.inv_mem (h.Q₂ hya)⟩ := by
      apply Subtype.ext
      show ((y₀ : ↥H) : G) = (a₂ : G) * (((y₀ : ↥H) : G)⁻¹ * (a₂ : G))⁻¹
      group
    rw [e, map_mul, ha₂, (hker₂ _).mpr ((pCoreOf 2 H).inv_mem hya), mul_one]
  refine ⟨((x₀ : ↥H) : G), ((y₀ : ↥H) : G), hx₁, hy₁, hφx, hφy, ?_, ?_, ?_, ?_⟩
  · have := hE₀.2 x₀ hx₀E
    exact congrArg Subtype.val this
  · have := hE₀.2 y₀ hy₀E
    exact congrArg Subtype.val this
  · exact congrArg Subtype.val (zmComm hE₀ hx₀E hy₀E)
  · intro hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hm' : y₀ = x₀ ^ m := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
    have h1 : α₂ ∈ Subgroup.zpowers α₁ ⊓ Subgroup.zpowers α₂ := by
      refine ⟨?_, Subgroup.mem_zpowers _⟩
      rw [← hy₀, hm']
      show (piQ H (x₀ ^ m)) ∈ _
      rw [map_zpow]
      have hx₀' : piQ H x₀ = α₁ := hx₀
      exact Subgroup.zpow_mem _ (by rw [hx₀']; exact Subgroup.mem_zpowers _) _
    rw [hinf, Subgroup.mem_bot] at h1
    exact hα₂ne h1

end Pair

end CFSG.Quasithin.S146zU.UA
