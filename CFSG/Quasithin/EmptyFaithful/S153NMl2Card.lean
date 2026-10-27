module

public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.Open.MatrixFixedVectors

public section

namespace CFSG.Quasithin.S153N

open CFSG.Assembly.LowTwoRank

section NatSL2

private theorem card_eq_card_ker_mul_card_range {G Q : Type} [Group G] [Group Q] (f : G →* Q) :
    Nat.card G = Nat.card ↥f.ker * Nat.card ↥f.range := by
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker]

private theorem odd_two_pow_sub_one {k : ℕ} (hk : 0 < k) : Odd (2 ^ k - 1) := by
  have h : Even (2 ^ k) := (Nat.even_pow' hk.ne').mpr even_two
  exact Nat.Even.sub_odd Nat.one_le_two_pow h odd_one

private theorem card_natAct_fixed_le {K : Type} [Field K] [Finite K] (g : ↥(StatedSL 2 K))
    (hg : g ≠ 1) :
    Nat.card {x : Multiplicative (Fin 2 → K) // natAct (StatedSL 2 K) g x = x} ≤ Nat.card K :=
  (Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun _ => Iff.rfl)).le.trans
    (CFSG.Open.StatedAPI.card_mulVec_fixed_le fun h => hg (Subtype.ext (Units.ext h)))

private theorem card_elemAbelian_le_field {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    {π : ↥(StatedSL 2 K) →* ↥L} (hπ : Function.Surjective π) {A : Subgroup (MulAut V)}
    (hAL : A ≤ L) (hA2 : IsElemAbelian2 A) : Nat.card ↥A ≤ Nat.card K := by
  have hdvd : Nat.card ↥A ∣ Nat.card ↥(StatedSL 2 K) :=
    (Subgroup.card_dvd_of_le hAL).trans (Subgroup.card_dvd_of_surjective hπ)
  have hcard : Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num)]
    simp
  have hp : IsPGroup 2 ↥A := fun g => ⟨1, Subtype.ext (by simpa using hA2.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hm1 : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    have h1 := Finite.one_lt_card (α := K)
    rw [hm0, pow_zero] at hK
    omega
  have hodd : Odd (Nat.card K ^ 2 - 1) := by
    rw [hK, ← pow_mul]
    exact odd_two_pow_sub_one (by omega)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K ^ 2 - 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  rw [hk, hcard] at hdvd
  have h2 : 2 ^ k ∣ Nat.card K := hcop.dvd_of_dvd_mul_right hdvd
  rw [hk]
  exact Nat.le_of_dvd Nat.card_pos h2

theorem card_mul_le_of_natural_sl2 {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}
    {U Z : Subgroup V} {m : ℕ} (hnat : BinaryNaturalSL L U Z 2 m) {A : Subgroup (MulAut V)}
    (hAL : A ≤ L) (hA1 : A ≠ ⊥) (hA2 : IsElemAbelian2 A) :
    Nat.card ↥A * Nat.card ↥(fixV A ⊓ U) ≤ Nat.card ↥U := by
  obtain ⟨K, _, _, hK, π₀, hπ₀⟩ := hnat
  obtain ⟨π, hπ⟩ : ∃ π : ↥(StatedSL 2 K) →* ↥L,
      (FFModel.nat (StatedSL 2 K)).RealizesVia L U Z π := ⟨π₀, hπ₀⟩
  obtain ⟨hsurj, hUinv, -, β, hβs, hβk, hβe⟩ := SzN15.NatReal.of_realizesVia hπ
  have hZU : Z ≤ U := hπ.2.1
  have hCU : fixV A ⊓ U ≤ U := inf_le_right
  have hUcard : Nat.card ↥U = Nat.card ↥Z * Nat.card K ^ 2 := by
    have h1 := card_eq_card_ker_mul_card_range β
    have h2 : β.range = ⊤ := MonoidHom.range_eq_top.mpr hβs
    have h3 : Nat.card ↥β.range = Nat.card K ^ 2 := by
      rw [h2, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
      simp
    have h4 : Nat.card ↥β.ker = Nat.card ↥Z := by
      have hker : β.ker = Z.subgroupOf U := by
        ext u
        rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
    rw [h1, h3, h4]
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  obtain ⟨g, hg⟩ := hsurj ⟨(a : MulAut V), hAL a.2⟩
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply ha1
    have h1 : (⟨(a : MulAut V), hAL a.2⟩ : ↥L) = 1 := by rw [← hg, map_one]
    exact Subtype.ext (congrArg (fun x : ↥L => (x : MulAut V)) h1)
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(fixV A ⊓ U) →* Multiplicative (Fin 2 → K),
      ∀ c, φ c = β (Subgroup.inclusion hCU c) := ⟨β.comp (Subgroup.inclusion hCU), fun c => rfl⟩
  have hφker : Nat.card ↥φ.ker ≤ Nat.card ↥Z := by
    have hmemZ : ∀ c : ↥φ.ker, ((c : ↥(fixV A ⊓ U)) : V) ∈ Z := fun c =>
      (hβk (Subgroup.inclusion hCU c)).mp (by rw [← hφ]; exact c.2)
    refine Nat.card_le_card_of_injective (fun c => (⟨((c : ↥(fixV A ⊓ U)) : V), hmemZ c⟩ :
      ↥Z)) ?_
    intro c d h
    have h1 : ((c : ↥(fixV A ⊓ U)) : V) = ((d : ↥(fixV A ⊓ U)) : V) :=
      congrArg (fun z : ↥Z => (z : V)) h
    exact Subtype.ext (Subtype.ext h1)
  have hφrange : Nat.card ↥φ.range ≤ Nat.card K := by
    have hfix : ∀ c : ↥(fixV A ⊓ U), natAct (StatedSL 2 K) g (φ c) = φ c := by
      intro c
      have hcU : (c : V) ∈ U := hCU c.2
      have hfixc : ((π g : ↥L) : MulAut V) (c : V) = (c : V) := by
        rw [hg]
        exact mem_fixV.mp c.2.1 a a.2
      have hu : ((π g : ↥L) : MulAut V) (c : V) ∈ U := hUinv (π g) (c : V) hcU
      have h1 := hβe g ⟨(c : V), hcU⟩ hu
      have h2 : (⟨((π g : ↥L) : MulAut V) (c : V), hu⟩ : ↥U) = ⟨(c : V), hcU⟩ :=
        Subtype.ext hfixc
      have h3 : β ⟨((π g : ↥L) : MulAut V) (c : V), hu⟩ = β ⟨(c : V), hcU⟩ := congrArg β h2
      rw [hφ]
      exact (h1.symm.trans h3)
    have hmem : ∀ x : ↥φ.range, natAct (StatedSL 2 K) g x.1 = x.1 := by
      rintro ⟨x, c, rfl⟩
      exact hfix c
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : ↥φ.range => (⟨x.1, hmem x⟩ :
        {x : Multiplicative (Fin 2 → K) // natAct (StatedSL 2 K) g x = x})) ?_)
      (card_natAct_fixed_le g hg1)
    intro x y h
    have h1 : x.1 = y.1 := congrArg (fun z : {x : Multiplicative (Fin 2 → K) //
      natAct (StatedSL 2 K) g x = x} => z.1) h
    exact Subtype.ext h1
  have hCcard : Nat.card ↥(fixV A ⊓ U) ≤ Nat.card ↥Z * Nat.card K := by
    rw [card_eq_card_ker_mul_card_range φ]
    exact Nat.mul_le_mul hφker hφrange
  have hAcard : Nat.card ↥A ≤ Nat.card K := card_elemAbelian_le_field hK hsurj hAL hA2
  calc Nat.card ↥A * Nat.card ↥(fixV A ⊓ U)
      ≤ Nat.card K * (Nat.card ↥Z * Nat.card K) := Nat.mul_le_mul hAcard hCcard
    _ = Nat.card ↥Z * Nat.card K ^ 2 := by ring
    _ = Nat.card ↥U := hUcard.symm

theorem not_isStrongFFModule_of_natural_sl2 {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {Z : Subgroup V} {m : ℕ}
    (hnat : BinaryNaturalSL L ⊤ Z 2 m) : ¬ IsStrongFFModule L := by
  rintro ⟨A, hAL, hA1, hA2, hlt⟩
  have h := card_mul_le_of_natural_sl2 hnat hAL hA1 hA2
  rw [inf_top_eq, Subgroup.card_top] at h
  omega

end NatSL2

end CFSG.Quasithin.S153N
