module

public import CFSG.Quasithin.EmptyFaithful.S153MDef
public import CFSG.Quasithin.EmptyFaithful.S153LKsA
public import CFSG.Quasithin.EmptyFaithful.S1565M14
import CFSG.Open.MatrixFixedVectors
public import CFSG.Quasithin.EmptyFaithful.S1565M7

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace S153M

section Small

private theorem false_of_card_small {L : Type} [Group L] [Finite L]
    (hK : S153L.KsCover L) (h : Nat.card L = 6 ∨ Nat.card L = 168 ∨ Nat.card L = 720) : False := by
  obtain ⟨N, hN, hcard⟩ := hK.card_data_eq
  have hge := S153L.ksOrd_ge hN
  have h720 := (S153L.ksOrd_ne_fixed hN).2.1
  have hz : 0 < Nat.card ↥(Subgroup.center L) := Nat.card_pos
  generalize Nat.card ↥(Subgroup.center L) = c at hcard hz
  rcases h with h | h | h <;> rw [hcard] at h
  · nlinarith
  · nlinarith
  · have hc : c = 1 := by
      by_contra hne
      have : 2 ≤ c := by omega
      nlinarith
    subst hc
    omega

private theorem card_statedSL_two_of_two {K : Type} [Field K] [Finite K] (h : Nat.card K = 2) :
    Nat.card ↥(StatedSL 2 K) = 6 := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num), h]
  decide

private theorem card_statedSL_three_of_two {K : Type} [Field K] [Finite K] (h : Nat.card K = 2) :
    Nat.card ↥(StatedSL 3 K) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two h

private theorem card_statedSp_two_of_two {K : Type} [Field K] [Finite K] (h : Nat.card K = 2) :
    Nat.card ↥(StatedSp 2 K) = 720 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, h]
  decide

private theorem false_of_realizes {V : Type} [CommGroup V]
    [Finite V] {L : Subgroup (MulAut V)} (hK : S153L.KsCover ↥L) {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] {Γ : Subgroup (GL ι F)} {U Z : Subgroup V}
    {π : ↥Γ →* ↥L}
    (hR : (FFModel.nat Γ).RealizesVia L U Z π)
    (hΓ : Nat.card ↥Γ = 6 ∨ Nat.card ↥Γ = 168 ∨ Nat.card ↥Γ = 720) : False := by
  have hb : Function.Bijective π := ⟨natural_realizes_injective Γ hR, hR.1⟩
  have hc : Nat.card ↥L = Nat.card ↥Γ := (Nat.card_congr (Equiv.ofBijective π hb)).symm
  exact false_of_card_small hK (by rw [hc]; exact hΓ)

private theorem two_le_of_realizes {V : Type} [CommGroup V]
    [Finite V] {L : Subgroup (MulAut V)} (hK : S153L.KsCover ↥L) {ι : Type} [Fintype ι]
    [DecidableEq ι]
    {F : Type} [Field F] [Finite F] {m : ℕ} (hm : Nat.card F = 2 ^ m) {Γ : Subgroup (GL ι F)}
    {U Z : Subgroup V} {π : ↥Γ →* ↥L} (hR : (FFModel.nat Γ).RealizesVia L U Z π)
    (hΓ : Nat.card F = 2 →
      Nat.card ↥Γ = 6 ∨ Nat.card ↥Γ = 168 ∨ Nat.card ↥Γ = 720) : 2 ≤ m := by
  by_contra hlt
  have h1 := Finite.one_lt_card (α := F)
  have hm2 : m < 2 := by omega
  interval_cases m
  · rw [pow_zero] at hm
    omega
  · exact false_of_realizes hK hR (hΓ (hm.trans (pow_one 2)))

end Small

section Borel

private theorem regular_inf_comm {W : Type} [CommGroup W] {V C : Subgroup W} {b : MulAut W}
    (h : ∀ u ∈ V, b u * u⁻¹ ∈ V ⊓ C → u ∈ V ⊓ C) :
    ∀ u ∈ V, b u * u⁻¹ ∈ C ⊓ V → u ∈ C ⊓ V := by
  rw [inf_comm]
  exact h

private theorem regular_transfer {V : Type} [CommGroup V] {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (GL ι F)} {X : Subgroup (MulAut V)} {U₀ U₁ : Subgroup V}
    {π : ↥Γ →* ↥X} (h₀ : (FFModel.nat Γ).RealizesVia X U₀ ⊥ π)
    (h₁ : (FFModel.nat Γ).RealizesVia X U₁ ⊥ π) (b : ↥X)
    (hb : ∀ u ∈ U₀, ((b : MulAut V) u) * u⁻¹ ∈ (⊥ : Subgroup V) → u ∈ (⊥ : Subgroup V)) :
    ∀ u ∈ U₁, ((b : MulAut V) u) * u⁻¹ ∈ (⊥ : Subgroup V) → u ∈ (⊥ : Subgroup V) := by
  obtain ⟨g, rfl⟩ := h₀.1 b
  refine natural_regular_of_noFixedVec Γ h₁ g ?_
  intro x hx
  obtain ⟨-, hUinv, -, β, hβs, hβk, hβe⟩ := SzN15.NatReal.of_realizesVia h₀
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd x)
  have hu' : ((π g : ↥X) : MulAut V) u ∈ U₀ := hUinv (π g) u u.2
  have h1 := hβe g u hu'
  have h2 : natAct Γ g (β u) = β u := by
    rw [hu]
    exact congrArg Multiplicative.ofAdd hx
  have h3 : β (⟨((π g : ↥X) : MulAut V) u, hu'⟩ * u⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, h2, mul_inv_cancel]
  have h4 := hb u u.2 ((hβk _).mp h3)
  have h5 : β u = 1 := (hβk u).mpr h4
  rw [hu] at h5
  exact Multiplicative.ofAdd.injective h5

private theorem sum_regular {V : Type} [CommGroup V] {I₀ I₁ : Subgroup V} (hd : Disjoint I₀ I₁)
    (b : MulAut V) (h0 : ∀ u ∈ I₀, b u ∈ I₀) (h1 : ∀ u ∈ I₁, b u ∈ I₁)
    (hr0 : ∀ u ∈ I₀, b u * u⁻¹ = 1 → u = 1) (hr1 : ∀ u ∈ I₁, b u * u⁻¹ = 1 → u = 1) :
    ∀ u ∈ I₀ ⊔ I₁, b u = u → u = 1 := by
  intro u hu hbu
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
  rw [map_mul] at hbu
  have hyz : b y / y = z / b z := by
    rw [div_eq_div_iff_mul_eq_mul, hbu, mul_comm]
  have hmem0 : b y / y ∈ I₀ := I₀.div_mem (h0 y hy) hy
  have hmem1 : b y / y ∈ I₁ := by
    rw [hyz]
    exact I₁.div_mem hz (h1 z hz)
  have hone : b y / y = 1 := Subgroup.disjoint_def.mp hd hmem0 hmem1
  have hy1 : y = 1 := hr0 y hy (by rw [← div_eq_mul_inv]; exact hone)
  have hbyy : b y = y := div_eq_one.mp hone
  have hbzz : b z = z := by
    rw [hbyy] at hbu
    exact mul_left_cancel hbu
  have hz1 : z = 1 := hr1 z hz (by rw [hbzz, mul_inv_cancel])
  rw [hy1, hz1, mul_one]

end Borel

theorem ffNatShape_elt {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} (hsh : FFNatShape L) (hK : S153L.KsCover ↥L) (S : Sylow 2 ↥L) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), ∃ r : ℕ, Odd r ∧ b ^ r = 1 ∧
      ∀ u ∈ commV L, ((b : MulAut V) u) * u⁻¹ ∈ fixV L ⊓ commV L → u ∈ fixV L ⊓ commV L := by
  rcases hsh with ⟨K, _, _, m, hm, hR⟩ | ⟨K, _, _, m, hm, hR⟩ | ⟨K, _, _, m, hm, hR⟩ |
    ⟨K, _, _, m, I, π, hm, hind, hI, hreal⟩
  ·
    obtain ⟨π, hπ⟩ := hR
    have h2 : 2 ≤ m :=
      two_le_of_realizes hK hm hπ (fun h => Or.inl (card_statedSL_two_of_two h))
    have hbin : BinaryNaturalSL L (commV L) (commV L ⊓ fixV L) 2 m :=
      ⟨K, inferInstance, inferInstance, hm, π, by rw [inf_comm]; exact hπ⟩
    obtain ⟨b, hb, r, hr, hbr, hreg⟩ := natfree_sl2_of_two_le h2 hbin S
    exact ⟨b, hb, r, hr, hbr, regular_inf_comm hreg⟩
  ·
    obtain ⟨π, hπ⟩ := hR
    have h2 : 2 ≤ m :=
      two_le_of_realizes hK hm hπ (fun h => Or.inr (Or.inl (card_statedSL_three_of_two h)))
    have hbin : BinaryNaturalSL L (commV L) (commV L ⊓ fixV L) 3 m :=
      ⟨K, inferInstance, inferInstance, hm, π, by rw [inf_comm]; exact hπ⟩
    obtain ⟨b, hb, r, hr, hbr, hreg⟩ := natfree_sl3_of_two_le h2 hbin S
    exact ⟨b, hb, r, hr, hbr, regular_inf_comm hreg⟩
  ·
    obtain ⟨π, hπ⟩ := hR
    have h2 : 2 ≤ m :=
      two_le_of_realizes hK hm hπ (fun h => Or.inr (Or.inr (card_statedSp_two_of_two h)))
    have hbin : BinaryNaturalSp4 L (commV L) (commV L ⊓ fixV L) m :=
      ⟨K, inferInstance, inferInstance, hm, π, by rw [inf_comm]; exact hπ⟩
    obtain ⟨b, hb, r, hr, hbr, hreg⟩ := natfree_sp4_of_two_le h2 hbin S
    exact ⟨b, hb, r, hr, hbr, regular_inf_comm hreg⟩
  ·
    have : CharP K 2 := SzN15.charP_two_of_card hm
    have h2 : 2 ≤ m := two_le_of_realizes hK hm (hreal 0)
      (fun h => Or.inr (Or.inl (card_statedSL_three_of_two h)))
    obtain ⟨ω, hω1, hodd⟩ := exists_unit_odd_order_ne_one hm h2
    have hω2 : ω ^ 2 ≠ 1 := by
      intro h2'
      have h3 := orderOf_dvd_of_pow_eq_one h2'
      obtain ⟨c, hc⟩ := hodd
      have : orderOf ω ≤ 2 := Nat.le_of_dvd (by norm_num) h3
      have h4 : orderOf ω = 1 := by omega
      exact hω1 (orderOf_eq_one_iff.mp h4)
    obtain ⟨b, hb, hbr, hreg0⟩ :=
      natural_sl3_borel_element ω hω1 hω2 (orderOf ω) (pow_orderOf_eq_one ω) (hreal 0) S
    have hreg : ∀ i : Fin 2, ∀ u ∈ I i, ((b : MulAut V) u) * u⁻¹ ∈ (⊥ : Subgroup V) →
        u ∈ (⊥ : Subgroup V) :=
      Fin.forall_fin_two.2 ⟨hreg0, regular_transfer (hreal 0) (hreal 1) b hreg0⟩
    have hsup : commV L = I 0 ⊔ I 1 := by
      rw [← hI]
      exact le_antisymm (iSup_le (Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩))
        (sup_le (le_iSup I 0) (le_iSup I 1))
    have hdisj : Disjoint (I 0) (I 1) := hind.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1)
    have hinv : ∀ i : Fin 2, ∀ u ∈ I i, ((b : MulAut V) u) ∈ I i := fun i u hu =>
      (SzN15.NatReal.of_realizesVia (hreal i)).U_inv b u hu
    have hreg' : ∀ u ∈ commV L, (b : MulAut V) u = u → u = 1 := by
      rw [hsup]
      refine sum_regular hdisj (b : MulAut V) (hinv 0) (hinv 1) ?_ ?_
      · intro u hu h
        exact Subgroup.mem_bot.mp (hreg 0 u hu (by rw [h]; exact one_mem _))
      · intro u hu h
        exact Subgroup.mem_bot.mp (hreg 1 u hu (by rw [h]; exact one_mem _))
    refine ⟨b, hb, orderOf ω, hodd, hbr, fun u hu hmem => ?_⟩
    have hbL : (b : MulAut V) ∈ L := b.2
    have hZ : ∀ w ∈ fixV L ⊓ commV L, w = 1 := fun w hw =>
      hreg' w hw.2 (mem_fixV.mp hw.1 (b : MulAut V) hbL)
    have h1 : ((b : MulAut V) u) * u⁻¹ = 1 := hZ _ hmem
    have h2' : (b : MulAut V) u = u := mul_inv_eq_one.mp h1
    rw [hreg' u hu h2']
    exact one_mem _

section Strong

private theorem card_eq_card_ker_mul_card_range {G Q : Type} [Group G] [Group Q] (f : G →* Q) :
    Nat.card G = Nat.card ↥f.ker * Nat.card ↥f.range := by
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker]

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
    exact S153L.ks_odd_two_pow_sub_one (by omega)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K ^ 2 - 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  rw [hk, hcard] at hdvd
  have h2 : 2 ^ k ∣ Nat.card K := hcop.dvd_of_dvd_mul_right hdvd
  rw [hk]
  exact Nat.le_of_dvd Nat.card_pos h2

end Strong

theorem not_strong_of_natural_sl2 {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} {m : ℕ} (hnat : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 m)
    {A : Subgroup (MulAut V)} (hAL : A ≤ L) (hA1 : A ≠ ⊥) (hA2 : IsElemAbelian2 A) :
    Nat.card ↥A * Nat.card ↥(fixV A ⊓ commV L) ≤ Nat.card ↥(commV L) := by
  have _ := hV
  obtain ⟨K, _, _, hK, π₀, hπ₀⟩ := hnat
  obtain ⟨π, hπ⟩ : ∃ π : ↥(StatedSL 2 K) →* ↥L,
      (FFModel.nat (StatedSL 2 K)).RealizesVia L (commV L) (fixV L ⊓ commV L) π := ⟨π₀, hπ₀⟩
  obtain ⟨hsurj, hUinv, -, β, hβs, hβk, hβe⟩ := SzN15.NatReal.of_realizesVia hπ
  have hZU : fixV L ⊓ commV L ≤ commV L := inf_le_right
  have hCU : fixV A ⊓ commV L ≤ commV L := inf_le_right
  have hUcard : Nat.card ↥(commV L) = Nat.card ↥(fixV L ⊓ commV L) * Nat.card K ^ 2 := by
    have h1 := card_eq_card_ker_mul_card_range β
    have h2 : β.range = ⊤ := MonoidHom.range_eq_top.mpr hβs
    have h3 : Nat.card ↥β.range = Nat.card K ^ 2 := by
      rw [h2, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
      simp
    have h4 : Nat.card ↥β.ker = Nat.card ↥(fixV L ⊓ commV L) := by
      have hker : β.ker = (fixV L ⊓ commV L).subgroupOf (commV L) := by
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
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(fixV A ⊓ commV L) →* Multiplicative (Fin 2 → K),
      ∀ c, φ c = β (Subgroup.inclusion hCU c) := ⟨β.comp (Subgroup.inclusion hCU), fun c => rfl⟩
  have hφker : Nat.card ↥φ.ker ≤ Nat.card ↥(fixV L ⊓ commV L) := by
    have hmemZ : ∀ c : ↥φ.ker, ((c : ↥(fixV A ⊓ commV L)) : V) ∈ fixV L ⊓ commV L := fun c =>
      (hβk (Subgroup.inclusion hCU c)).mp (by rw [← hφ]; exact c.2)
    refine Nat.card_le_card_of_injective (fun c => (⟨((c : ↥(fixV A ⊓ commV L)) : V), hmemZ c⟩ :
      ↥(fixV L ⊓ commV L))) ?_
    intro c d h
    have h1 : ((c : ↥(fixV A ⊓ commV L)) : V) = ((d : ↥(fixV A ⊓ commV L)) : V) :=
      congrArg (fun z : ↥(fixV L ⊓ commV L) => (z : V)) h
    exact Subtype.ext (Subtype.ext h1)
  have hφrange : Nat.card ↥φ.range ≤ Nat.card K := by
    have hfix : ∀ c : ↥(fixV A ⊓ commV L), natAct (StatedSL 2 K) g (φ c) = φ c := by
      intro c
      have hcU : (c : V) ∈ commV L := hCU c.2
      have hfixc : ((π g : ↥L) : MulAut V) (c : V) = (c : V) := by
        rw [hg]
        exact mem_fixV.mp c.2.1 a a.2
      have hu : ((π g : ↥L) : MulAut V) (c : V) ∈ commV L := hUinv (π g) (c : V) hcU
      have h1 := hβe g ⟨(c : V), hcU⟩ hu
      have h2 : (⟨((π g : ↥L) : MulAut V) (c : V), hu⟩ : ↥(commV L)) = ⟨(c : V), hcU⟩ :=
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
  have hCcard : Nat.card ↥(fixV A ⊓ commV L) ≤ Nat.card ↥(fixV L ⊓ commV L) * Nat.card K := by
    rw [card_eq_card_ker_mul_card_range φ]
    exact Nat.mul_le_mul hφker hφrange
  have hAcard : Nat.card ↥A ≤ Nat.card K := card_elemAbelian_le_field hK hsurj hAL hA2
  calc Nat.card ↥A * Nat.card ↥(fixV A ⊓ commV L)
      ≤ Nat.card K * (Nat.card ↥(fixV L ⊓ commV L) * Nat.card K) := Nat.mul_le_mul hAcard hCcard
    _ = Nat.card ↥(fixV L ⊓ commV L) * Nat.card K ^ 2 := by ring
    _ = Nat.card ↥(commV L) := hUcard.symm

end S153M

end CFSG.Quasithin
