module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tb
public import CFSG.Quasithin.Vol2.Ch10SecK2Tc
public import CFSG.Quasithin.Vol2.Ch10SecK2Td
public import CFSG.Quasithin.Vol2.KGNatSL3LineFacts
public import CFSG.Quasithin.Vol2.Ch10SecQ9H63
public import CFSG.Quasithin.Vol2.Ch11SecCB51Ord
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch11.SecA

section Sub

variable {W : Type*} [Group W] {H : Subgroup (MulAut W)}

theorem map_perfectCore_subgroupOf [Finite W] (A : Subgroup (MulAut W)) :
    (perfectCore (A.subgroupOf H)).map H.subtype = perfectCore (H ⊓ A) := by
  rw [map_perfectCore, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem isSylowTwoOf_map_subtype {S₀ : Subgroup ↥H} (hS : IsSylowTwoOf S₀ ⊤) :
    IsSylowTwoOf (S₀.map H.subtype) H := by
  obtain ⟨-, hp, hi⟩ := hS
  refine ⟨Subgroup.map_subtype_le _, hp.map _, ?_⟩
  rw [show (S₀.map H.subtype).subgroupOf H = S₀ from
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective S₀]
  rwa [show (S₀.subgroupOf ⊤).index = S₀.index from Subgroup.relIndex_top_right S₀] at hi

theorem mem_normalizer_map_subtype {S₀ : Subgroup ↥H} {x : ↥H}
    (hx : x ∈ Subgroup.normalizer (S₀ : Set ↥H)) :
    (x : MulAut W) ∈ Subgroup.normalizer ((S₀.map H.subtype : Subgroup (MulAut W)) :
      Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · rintro ⟨s₀, hs₀, rfl⟩
    exact ⟨x * s₀ * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx s₀).mp hs₀, rfl⟩
  · rintro ⟨t, ht, hts⟩
    have hts' : (t : MulAut W) = (x : MulAut W) * s * (x : MulAut W)⁻¹ := hts
    have hsH : s ∈ H := by
      have : s = ((x⁻¹ * t * x : ↥H) : MulAut W) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hts', Subgroup.coe_inv]
        group
      rw [this]
      exact (x⁻¹ * t * x).2
    refine ⟨⟨s, hsH⟩, ?_, rfl⟩
    have h1 : x * ⟨s, hsH⟩ * x⁻¹ = t := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hts'])
    show (⟨s, hsH⟩ : ↥H) ∈ S₀
    exact (Subgroup.mem_normalizer_iff.mp hx _).mpr (h1 ▸ ht)

end Sub

section Orders

theorem card_eq_of_levi {X : Type*} [Group X] [Finite X] {K : Type} [Field K] [Finite K]
    (e : X ⧸ CFSG.pCore 2 X ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ k : ℕ, Nat.card X = Nat.card K * (Nat.card K ^ 2 - 1) * 2 ^ k := by
  have hc := (CFSG.pCore 2 X).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr e.toEquiv,
    Nat.card_congr (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toEquiv,
    card_statedSL_two1527d] at hc
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp (CFSG.pCore_isPGroup (p := 2) (G := X))
  exact ⟨k, by rw [hc, hk]⟩

theorem one_lt_card_of_levi {X : Type*} [Group X] [Finite X] {K : Type} [Field K] [Finite K]
    (e : X ⧸ CFSG.pCore 2 X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : 1 < Nat.card X := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨k, hk⟩ := card_eq_of_levi e
  have h2 : 4 ≤ Nat.card K ^ 2 := by nlinarith
  have h3 : 1 < Nat.card K * (Nat.card K ^ 2 - 1) := by
    have : 3 ≤ Nat.card K ^ 2 - 1 := by omega
    nlinarith
  have h4 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [hk]
  nlinarith

theorem card_ne_levi {m c k : ℕ} (hm : 1 ≤ m) (hc : 2 ≤ c) :
    2 ^ c * ((2 ^ c - 1) * (2 ^ (2 * m) - 1)) ≠ 2 ^ m * ((2 ^ m) ^ 2 - 1) * 2 ^ k := by
  intro h
  rw [← pow_mul, mul_comm m 2] at h
  have hA : 0 < 2 ^ (2 * m) - 1 := by
    have : 2 ^ 1 ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1 : (2 ^ (2 * m) - 1) * (2 ^ c * (2 ^ c - 1)) = (2 ^ (2 * m) - 1) * 2 ^ (m + k) := by
    rw [pow_add]
    linarith [h]
  have h2 := Nat.eq_of_mul_eq_mul_left hA h1
  have h4 : 4 ≤ 2 ^ c := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc
  have hodd : Odd (2 ^ c - 1) :=
    Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hcop : Nat.Coprime (2 ^ c - 1) (2 ^ (m + k)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have hdvd : 2 ^ c - 1 ∣ 2 ^ (m + k) := ⟨2 ^ c, by rw [← h2, mul_comm]⟩
  have := Nat.Coprime.eq_one_of_dvd hcop hdvd
  omega

end Orders

section Generic

open CFSG.QuasithinUnique.Setup.X6 (dInf ResidualOvergroupsAt)

variable {K : Type} [Field K] [Finite K] {m : ℕ} {W : Type} [CommGroup W] [Finite W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W}

theorem perfectCore_eq_flag_of (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (hHH : ⁅H, H⁆ = H)
    (hcard : ∀ k : ℕ, Nat.card ↥H ≠ 2 ^ m * ((2 ^ m) ^ 2 - 1) * 2 ^ k)
    (hres : ∀ S₀ : Subgroup ↥H, IsSylowTwoOf S₀ ⊤ → ∃ P, ResidualOvergroupsAt ↥H S₀ P)
    (hflag : ∀ S : Subgroup (MulAut W), IsSylowTwoOf S H → HasUniqueFlagW H S Z (2 ^ m))
    (hlevi : ∀ S : Subgroup (MulAut W), IsSylowTwoOf S H → ∀ (i : ℕ) (U : Subgroup W),
      (i = 1 ∨ i = 2) → IsFlagW H S Z (2 ^ m) i U →
      Nonempty (↥(perfectCore (H ⊓ stabW U)) ⧸ CFSG.pCore 2 ↥(perfectCore (H ⊓ stabW U)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K))
    (hpoint : ∀ S : Subgroup (MulAut W), IsSylowTwoOf S H → ∀ U : Subgroup W,
      IsFlagW H S Z (2 ^ m) 1 U → ∀ h ∈ perfectCore (H ⊓ stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ Z)
    (hline : ∀ S : Subgroup (MulAut W), IsSylowTwoOf S H → ∀ U : Subgroup W,
      IsFlagW H S Z (2 ^ m) 2 U → LineFacts H Z U)
    {Pst : Subgroup ↥H} (hPst : IsMaxParabolic2 ⊤ Pst) {S₀ : Subgroup ↥H}
    (hS₀ : IsSylowTwoOf S₀ ⊤) (hPS : Subgroup.normalizer (S₀ : Set ↥H) ≤ Pst) :
    ∃ (U : Subgroup W) (i : ℕ), (i = 1 ∨ i = 2) ∧ IsFlagW H (S₀.map H.subtype) Z (2 ^ m) i U ∧
      (perfectCore Pst).map H.subtype = perfectCore (H ⊓ stabW U) := by
  set S := S₀.map H.subtype with hSdef
  have hS : IsSylowTwoOf S H := isSylowTwoOf_map_subtype hS₀
  obtain ⟨U₁, U₂, -, hU₁, hU₂, -, h12, -, hu₁, hu₂, -⟩ := hflag S hS
  let Q : Fin 2 → Subgroup ↥H := ![(stabW U₁).subgroupOf H, (stabW U₂).subgroupOf H]
  have hQ0 : Q 0 = (stabW U₁).subgroupOf H := rfl
  have hQ1 : Q 1 = (stabW U₂).subgroupOf H := rfl
  have hmapQ : ∀ U : Subgroup W, ((perfectCore ((stabW U).subgroupOf H)).map H.subtype) =
      perfectCore (H ⊓ stabW U) := fun U => map_perfectCore_subgroupOf _
  have hQS : ∀ i, Subgroup.normalizer (S₀ : Set ↥H) ≤ Q i := by
    intro i x hx
    have hxN := mem_normalizer_map_subtype (W := W) hx
    fin_cases i
    · exact Subgroup.mem_subgroupOf.mpr (mem_stabW_of_unique hHZ hu₁ hU₁ x.2 hxN)
    · exact Subgroup.mem_subgroupOf.mpr (mem_stabW_of_unique hHZ hu₂ hU₂ x.2 hxN)
  have hsolv : ∀ (i : ℕ) (U : Subgroup W), (i = 1 ∨ i = 2) → IsFlagW H S Z (2 ^ m) i U →
      ¬ Group.IsSolvable ↥((stabW U).subgroupOf H) := by
    intro i U hi hU hs
    obtain ⟨e⟩ := hlevi S hS i U hi hU
    have h1 := one_lt_card_of_levi e
    rw [← hmapQ, (isSolvable_iff_perfectCore_eq_bot _).mp hs, Subgroup.map_bot,
      Subgroup.card_bot] at h1
    exact lt_irrefl _ h1
  have htop : ∀ (i : ℕ) (U : Subgroup W), (i = 1 ∨ i = 2) → IsFlagW H S Z (2 ^ m) i U →
      (stabW U).subgroupOf H ≠ ⊤ := by
    intro i U hi hU htop
    obtain ⟨e⟩ := hlevi S hS i U hi hU
    have hle : H ≤ stabW U := fun h hh => by
      have : (⟨h, hh⟩ : ↥H) ∈ (stabW U).subgroupOf H := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    have heq : perfectCore (H ⊓ stabW U) = H := by
      rw [inf_eq_left.mpr hle]
      exact perfectCore_eq_self_of_perfect hHH
    obtain ⟨k, hk⟩ := card_eq_of_levi e
    rw [heq, hK] at hk
    exact hcard k hk
  have hne : dInf (Q 0) ≠ dInf (Q 1) := by
    intro h
    rw [Vol2Native.A312L.dInf_eq_perfectCore, Vol2Native.A312L.dInf_eq_perfectCore] at h
    have h' : perfectCore (H ⊓ stabW U₁) = perfectCore (H ⊓ stabW U₂) := by
      rw [← hmapQ, ← hmapQ, ← hQ0, ← hQ1, h]
    have hfix := KGNat.fix_of_perfect (perfectCore_perfect (H ⊓ stabW U₁))
      (fun h hh z hz => hHZ h ((perfectCore_le _ hh).1) z hz) (hpoint S hS U₁ hU₁)
    obtain ⟨-, -, hc, -⟩ := hline S hS U₂ hU₂
    have hU₁Z : U₁ ≤ Z := fun u hu => (hc u (h12 hu)).mp fun s hs => hfix s (h' ▸ hs) u hu
    have h1 : Z.relIndex U₁ = 1 := Subgroup.relIndex_eq_one.mpr hU₁Z
    rw [hU₁.2.2.1, pow_one] at h1
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  obtain ⟨P, hres⟩ := hres S₀ hS₀
  have hQtop : ∀ i, Q i ≠ ⊤ := by
    intro i
    fin_cases i
    · exact htop 1 U₁ (Or.inl rfl) hU₁
    · exact htop 2 U₂ (Or.inr rfl) hU₂
  have hQsolv : ∀ i, ¬ Group.IsSolvable ↥(Q i) := by
    intro i
    fin_cases i
    · exact hsolv 1 U₁ (Or.inl rfl) hU₁
    · exact hsolv 2 U₂ (Or.inr rfl) hU₂
  obtain ⟨i, hi⟩ := dInf_eq_of_residual hS₀ hres hQS hQtop hQsolv hne hPS hPst
  rw [Vol2Native.A312L.dInf_eq_perfectCore, Vol2Native.A312L.dInf_eq_perfectCore] at hi
  fin_cases i
  · exact ⟨U₁, 1, Or.inl rfl, hU₁, by rw [hi]; exact hmapQ U₁⟩
  · exact ⟨U₂, 2, Or.inr rfl, hU₂, by rw [hi]; exact hmapQ U₂⟩

end Generic

section SL3


theorem perfectCore_eq_flag_SL3 {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {Z : Subgroup W}
    {π : ↥(Assembly.LowTwoRank.StatedSL 3 K) →* ↥H}
    (hR : (FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K)).RealizesVia H ⊤ Z π)
    (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {Pst : Subgroup ↥H} (hPst : IsMaxParabolic2 ⊤ Pst)
    {S₀ : Subgroup ↥H} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hPS : Subgroup.normalizer (S₀ : Set ↥H) ≤ Pst) :
    ∃ (U : Subgroup W) (i : ℕ), (i = 1 ∨ i = 2) ∧ IsFlagW H (S₀.map H.subtype) Z (2 ^ m) i U ∧
      (perfectCore Pst).map H.subtype = perfectCore (H ⊓ stabW U) := by
  have hπb : Function.Bijective π := ⟨injective_of_realizesVia_nat hR, hR.1⟩
  let e : ↥H ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    (MulEquiv.ofBijective π hπb).symm.trans
      (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  have hHp : Group.IsPerfect ↥H := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  have hcard : ∀ k : ℕ, Nat.card ↥H ≠ 2 ^ m * ((2 ^ m) ^ 2 - 1) * 2 ^ k := fun k => by
    rw [Nat.card_congr e.toEquiv, Ch11.SecC.B51.card_SL3_eq_pow hK]
    exact card_ne_levi (by omega) (by omega)
  have htype : IsSL3 (2 ^ m) ↥H := ⟨K, inferInstance, inferInstance, hK,
    ⟨(MulEquiv.ofBijective π hπb).symm⟩⟩
  exact perfectCore_eq_flag_of hm hK hHZ (Subgroup.isPerfect_iff.mp hHp) hcard
    (fun S₀ hS₀ => SecB.Rank2.exists_residualOvergroupsAt (by omega : 1 ≤ m)
      (Or.inr (Or.inl htype)) hS₀)
    (fun S hS => KGNat.factFlagSL3_holds K m hm hK W hW2 H Z π hR S hS)
    (fun S hS => KGNat.factLeviSL3_holds K m hm hK W hW2 H Z π hR S hS)
    (fun S hS => KGNat.factPointSL3_holds K m hm hK W hW2 H Z π hR S hS)
    (fun S hS => KGNat.factLineSL3_holds K m hm hK W hW2 H Z π hR hHZ S hS) hPst hS₀ hPS

end SL3

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
