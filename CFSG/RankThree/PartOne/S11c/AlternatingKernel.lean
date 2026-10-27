module

public import CFSG.RankThree.PartOne.S11c.HNProps
import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingDegreeThirteen
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXAlternatingThreeCycles
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.RankThree.PartOne.HNRed

open Equiv Equiv.Perm Subgroup
open CFSG.Assembly.RankThreeEven (localRank)

theorem center_conj_eq {K : Type*} [Group K] {z : K} (hz : z ∈ Subgroup.center K) (u : K) :
    z * u * z⁻¹ = u := by
  rw [← Subgroup.mem_center_iff.mp hz u, mul_inv_cancel_right]

theorem mem_normalizer_of_mem_center {K : Type*} [Group K] {z : K} (hz : z ∈ Subgroup.center K)
    (S : Subgroup K) : z ∈ Subgroup.normalizer (S : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [center_conj_eq hz h]

theorem le_normalizer_of_le_center {K : Type*} [Group K] {U : Subgroup K}
    (hU : U ≤ Subgroup.center K) (V : Subgroup K) : V ≤ Subgroup.normalizer (U : Set K) := by
  intro v _
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have hcentral : ∀ w : K, w ∈ U → v * w * v⁻¹ = w := fun w hw => by
    rw [Subgroup.mem_center_iff.mp (hU hw) v, mul_inv_cancel_right]
  constructor
  · intro hu
    rw [hcentral u hu]
    exact hu
  · intro hu
    have h1 := hcentral _ hu
    have h2 : v⁻¹ * (v * u * v⁻¹) * v = u := by group
    rw [← h2, ← h1]
    have h3 : v⁻¹ * (v * (v * u * v⁻¹) * v⁻¹) * v = v * u * v⁻¹ := by group
    rw [h3]
    exact hu

theorem four_le_twoLocalOddRank_of_normalizing {G K : Type} [Group G] [Finite G] [Group K]
    (ι : K →* G) (hι : Function.Injective ι) {U V : Subgroup K} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hVc : IsMulCommutative V) (hVe : ∀ w ∈ V, w ^ 3 = 1) (hVcard : Nat.card V = 3 ^ 4)
    (hVN : V ≤ Subgroup.normalizer (U : Set K)) : 4 ≤ CFSG.twoLocalOddRank G := by
  have := hVc
  have hU' : U.map ι ≠ ⊥ := by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hι]
  have hU2' : IsPGroup 2 (U.map ι) := hU2.map ι
  have hV' : V.map ι ≤ Subgroup.normalizer ((U.map ι : Subgroup G) : Set G) :=
    (Subgroup.map_mono hVN).trans (Subgroup.le_normalizer_map ι)
  have hcard' : Nat.card (V.map ι) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective hι, hVcard]
  have hc' : IsMulCommutative (V.map ι) := by
    refine ⟨⟨?_⟩⟩
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    refine Subtype.ext ?_
    show ι a * ι b = ι b * ι a
    rw [← map_mul, ← map_mul]
    exact congrArg ι (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : V) ⟨b, hb⟩))
  have he' : ∀ w ∈ V.map ι, w ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hVe a ha, map_one]
  have h3 : 4 ≤ localRank 3 G :=
    CFSG.RankThree.Theta.le_localRank_of_le_normalizer (by norm_num) hU' hU2' hc' he' hcard' hV'
  have h3G : 3 ∣ Nat.card G :=
    (Dvd.intro_left _ (hcard'.symm.trans (by norm_num))).trans
      (Subgroup.card_subgroup_dvd_card (V.map ι))
  exact h3.trans (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank Nat.prime_three
    (by norm_num) h3G)

theorem exists_two_subgroup_normalized {K A : Type*} [Group K] [Finite K] [Group A]
    (π : K →* A) (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center K) {Q : Subgroup A}
    [IsMulCommutative Q] (hQ2 : 2 ∣ Nat.card Q) {V : Subgroup K}
    (hVQ : V.map π ≤ Subgroup.normalizer (Q : Set A)) :
    ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U ∧ V ≤ Subgroup.normalizer (U : Set K) := by
  set F := Q.comap π
  let f : F →* Q := (π.comp F.subtype).codRestrict Q fun w => w.2
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨w, rfl⟩ := hπ q
    exact ⟨⟨w, hq⟩, rfl⟩
  have hfker : f.ker ≤ Subgroup.center F := by
    intro w hw
    have hwK : (w : K) ∈ π.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hw)
    exact Subgroup.mem_center_iff.mpr fun w' =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hZ hwK) w')
  have hFnil : Group.IsNilpotent F := Subgroup.isNilpotent_of_ker_le_center f hfker
  have hF2 : 2 ∣ Nat.card F := hQ2.trans (Subgroup.card_dvd_of_surjective hf)
  have hU₀ : CFSG.pCore 2 F ≠ ⊥ :=
    CFSG.RankThree.GroupTheory.pCore_two_ne_bot_of_isNilpotent hFnil hF2
  have hVF : V ≤ Subgroup.normalizer (F : Set K) := by
    intro v hv
    apply Subgroup.le_normalizer_comap π
    rw [Subgroup.mem_comap]
    exact hVQ (Subgroup.mem_map_of_mem π hv)
  have hVU : V ≤ Subgroup.normalizer (((CFSG.pCore 2 F).map F.subtype : Subgroup K) : Set K) :=
    hVF.trans (CFSG.RankThree.GroupTheory.normalizer_le_normalizer_map_subtype (CFSG.pCore 2 F))
  refine ⟨(CFSG.pCore 2 F).map F.subtype, ?_, ?_, hVU⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective]
    exact hU₀
  · have h2 : IsPGroup 2 (CFSG.pCore 2 F) := CFSG.pCore_isPGroup
    exact h2.map F.subtype

theorem exists_lift_embedded {k n m : ℕ} (hk : k ≤ n) (hm : 3 ≤ m) (hmn : 3 * m ≤ n) {K : Type}
    [Group K] [Finite K] (π : K →* alternatingGroup (Fin n)) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center K) (c₀ : Fin m → alternatingGroup (Fin k))
    (h3 : ∀ i, (c₀ i : Perm (Fin k)).IsThreeCycle)
    (hd : Pairwise fun i j => (c₀ i : Perm (Fin k)).Disjoint (c₀ j)) :
    ∃ V : Subgroup K, CFSG.IsElementaryAbelian 3 V ∧ Nat.card V = 3 ^ m ∧ Set.InjOn π V ∧
      V.map π = Subgroup.closure (Set.range fun i => CFSG.SectionRank.altEmbed hk (c₀ i)) := by
  set c : Fin m → alternatingGroup (Fin n) := fun i => CFSG.SectionRank.altEmbed hk (c₀ i)
  have hc3 : ∀ i, (c i : Perm (Fin n)).IsThreeCycle := fun i => by
    change ((c₀ i : Perm (Fin k)).extendDomain (CFSG.SectionRank.firstPts hk)).cycleType = {3}
    rw [cycleType_extendDomain]
    exact h3 i
  have hcd : Pairwise fun i j => (c i : Perm (Fin n)).Disjoint (c j) := fun i j hij =>
    (hd hij).extendDomain (CFSG.SectionRank.firstPts hk)
  obtain ⟨-, ⟨V, hVel, hVcard, hVinj, hVmap⟩, -⟩ :=
    LocalAnalysis.GorensteinLyons.alternating_central_cover_injective_disjoint_three_cycles.{0}
      (k := m) hm hmn π hπ hZ c hc3 hcd
  exact ⟨V, hVel, hVcard, hVinj, hVmap⟩

def tenKleinX : Perm (Fin 10) := swap 0 1 * swap 2 3

def tenKleinY : Perm (Fin 10) := swap 0 2 * swap 1 3

def tenCycle : Fin 3 → Perm (Fin 10) :=
  ![swap 0 1 * swap 0 2, swap 4 5 * swap 4 6, swap 7 8 * swap 7 9]

theorem tenKleinX_sign : sign tenKleinX = 1 := by decide +kernel

theorem tenKleinY_sign : sign tenKleinY = 1 := by decide +kernel

theorem tenCycle_isThreeCycle (i : Fin 3) : (tenCycle i).IsThreeCycle := by
  fin_cases i <;> exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem tenCycle_disjoint : Pairwise fun i j : Fin 3 => (tenCycle i).Disjoint (tenCycle j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | (intro x; fin_cases x <;> decide)

theorem tenCycle_zero_conj_x : tenCycle 0 * tenKleinX * (tenCycle 0)⁻¹ = tenKleinY := by
  decide +kernel

theorem tenCycle_zero_conj_y :
    tenCycle 0 * tenKleinY * (tenCycle 0)⁻¹ = tenKleinX * tenKleinY := by decide +kernel

theorem tenCycle_commute_x : ∀ i : Fin 3, i ≠ 0 → tenCycle i * tenKleinX = tenKleinX * tenCycle i :=
  by decide +kernel

theorem tenCycle_commute_y : ∀ i : Fin 3, i ≠ 0 → tenCycle i * tenKleinY = tenKleinY * tenCycle i :=
  by decide +kernel

theorem tenKlein_commute : tenKleinX * tenKleinY = tenKleinY * tenKleinX := by decide +kernel

theorem tenKleinX_ne_one : tenKleinX ≠ 1 := by decide +kernel

theorem tenKleinX_mul_self : tenKleinX * tenKleinX = 1 := by decide +kernel

theorem four_le_twoLocalOddRank_of_three_dvd {G K : Type} [Group G] [Finite G] [Group K]
    (ι : K →* G) (hι : Function.Injective ι) {n : ℕ} (hn : 10 ≤ n)
    (π : K →* alternatingGroup (Fin n)) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center K) (h3 : 3 ∣ Nat.card π.ker) : 4 ≤ CFSG.twoLocalOddRank G := by
  have : Finite K := Finite.of_injective ι hι
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ε := CFSG.SectionRank.altEmbed hn
  set x : alternatingGroup (Fin 10) := ⟨tenKleinX, tenKleinX_sign⟩
  set y : alternatingGroup (Fin 10) := ⟨tenKleinY, tenKleinY_sign⟩
  set c₀ : Fin 3 → alternatingGroup (Fin 10) := fun i =>
    ⟨tenCycle i, (tenCycle_isThreeCycle i).mem_alternatingGroup⟩
  set Q₀ := Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 10)))
  have hxy : x * y = y * x := Subtype.ext tenKlein_commute
  have hnorm₀ : ∀ i, c₀ i ∈ Subgroup.normalizer (Q₀ : Set (alternatingGroup (Fin 10))) := by
    intro i
    apply CFSG.RankThree.GroupTheory.mem_normalizer_closure_of_conj_mem
    have hx : x ∈ Q₀ := Subgroup.subset_closure (by simp)
    have hy : y ∈ Q₀ := Subgroup.subset_closure (by simp)
    rintro s (rfl | rfl)
    · by_cases hi : i = 0
      · subst hi
        have h : c₀ 0 * x * (c₀ 0)⁻¹ = y := Subtype.ext tenCycle_zero_conj_x
        rw [h]
        exact hy
      · have h : c₀ i * x = x * c₀ i := Subtype.ext (tenCycle_commute_x i hi)
        rw [h, mul_inv_cancel_right]
        exact hx
    · by_cases hi : i = 0
      · subst hi
        have h : c₀ 0 * y * (c₀ 0)⁻¹ = x * y := Subtype.ext tenCycle_zero_conj_y
        rw [h]
        exact Q₀.mul_mem hx hy
      · have h : c₀ i * y = y * c₀ i := Subtype.ext (tenCycle_commute_y i hi)
        rw [h, mul_inv_cancel_right]
        exact hy
  set Q := Q₀.map ε
  have hcQ : Subgroup.closure (Set.range fun i => ε (c₀ i)) ≤
      Subgroup.normalizer (Q : Set (alternatingGroup (Fin n))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.le_normalizer_map ε (Subgroup.mem_map_of_mem ε (hnorm₀ i))
  obtain ⟨V, hVel, hVcard, hVinj, hVmap⟩ :=
    exists_lift_embedded hn (m := 3) le_rfl (by omega) π hπ hZ c₀
      (fun i => tenCycle_isThreeCycle i) (fun i j hij => tenCycle_disjoint hij)
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    have hQ₀ : IsMulCommutative Q₀ := Subgroup.isMulCommutative_closure (by
      rintro a (rfl | rfl) b (rfl | rfl) - <;> first | rfl | exact hxy | exact hxy.symm)
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ε (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Q₀) ⟨b, hb⟩))
  have hQc : IsMulCommutative Q := ⟨⟨fun a b => Subtype.ext (hQab a a.2 b b.2)⟩⟩
  have hQ2 : 2 ∣ Nat.card Q := by
    have hxQ : ε x ∈ Q := Subgroup.mem_map_of_mem ε (Subgroup.subset_closure (by simp))
    have hord : orderOf (⟨ε x, hxQ⟩ : Q) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      apply orderOf_eq_prime
      · apply Subtype.ext
        change ε x ^ 2 = 1
        rw [← map_pow, pow_two]
        have h : x * x = 1 := Subtype.ext tenKleinX_mul_self
        rw [h, map_one]
      · intro h
        have h1 : ε x = 1 := congrArg Subtype.val h
        have h2 : x = 1 := CFSG.SectionRank.altEmbed_injective hn (h1.trans (map_one ε).symm)
        exact tenKleinX_ne_one (congrArg Subtype.val h2)
    exact hord ▸ _root_.orderOf_dvd_natCard _
  have := hQc
  obtain ⟨U, hU, hU2, hVU⟩ := exists_two_subgroup_normalized π hπ hZ hQ2
    (V := V) (hVmap.le.trans hcQ)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) 3 h3
  set D : Subgroup K := Subgroup.zpowers (d : K)
  have hdK : (d : K) ∈ Subgroup.center K := hZ d.2
  have hDcent : D ≤ Subgroup.center K := (Subgroup.zpowers_le).mpr hdK
  have hDcard : Nat.card D = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hd]
  have hdo : orderOf (d : K) = 3 := by rw [Subgroup.orderOf_coe, hd]
  have hDe : ∀ w ∈ D, w ^ 3 = 1 := fun w hw =>
    orderOf_dvd_iff_pow_eq_one.mp (hdo ▸ orderOf_dvd_of_mem_zpowers hw)
  have hDV : ∀ w ∈ D, w ∈ V → w = 1 := by
    intro w hw hwV
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hπd : π ((d : K) ^ j) = π 1 := by
      rw [map_zpow, MonoidHom.mem_ker.mp d.2, one_zpow, map_one]
    exact hVinj hwV V.one_mem hπd
  have hcomm : ∀ (a : D) (b : V), Commute (D.subtype a) (V.subtype b) := fun a b =>
    ((Subgroup.mem_center_iff.mp (hDcent a.2) (b : K))).symm
  let μ : D × V →* K := MonoidHom.noncommCoprod D.subtype V.subtype hcomm
  have hμ : ∀ (a : D) (b : V), μ (a, b) = (a : K) * (b : K) := fun a b => rfl
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    rw [hμ] at hab
    have hb : (b : K) = ((a : K))⁻¹ := eq_inv_of_mul_eq_one_right hab
    have ha1 : (a : K) = 1 := by
      refine hDV a a.2 ?_
      have : ((a : K))⁻¹ ∈ V := hb ▸ b.2
      simpa using V.inv_mem this
    have hb1 : (b : K) = 1 := by rw [hb, ha1, inv_one]
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  set V' := μ.range
  have hV'card : Nat.card V' = 3 ^ 4 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv.symm, Nat.card_prod, hDcard, hVcard]
    norm_num
  have hV'c : IsMulCommutative V' := by
    have : IsMulCommutative D := inferInstance
    have : IsMulCommutative V := hVel.toIsMulCommutative
    refine ⟨⟨?_⟩⟩
    rintro ⟨_, p, rfl⟩ ⟨_, q, rfl⟩
    refine Subtype.ext ?_
    show μ p * μ q = μ q * μ p
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (mul_comm' p.1 q.1) (mul_comm' p.2 q.2)
  have hV'e : ∀ w ∈ V', w ^ 3 = 1 := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [← map_pow]
    have h1 : (a, b) ^ 3 = 1 := by
      refine Prod.ext (Subtype.ext (hDe a a.2)) (Subtype.ext ?_)
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := V) b b.2
    rw [h1, map_one]
  have hV'N : V' ≤ Subgroup.normalizer (U : Set K) := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [hμ]
    refine Subgroup.mul_mem _ ?_ (hVU b.2)
    exact mem_normalizer_of_mem_center (hDcent a.2) U
  exact four_le_twoLocalOddRank_of_normalizing ι hι hU hU2 hV'c hV'e hV'card hV'N

def twelveCycle : Fin 4 → Perm (Fin 12) :=
  ![swap 0 1 * swap 0 2, swap 3 4 * swap 3 5, swap 6 7 * swap 6 8, swap 9 10 * swap 9 11]

theorem twelveCycle_isThreeCycle (i : Fin 4) : (twelveCycle i).IsThreeCycle := by
  fin_cases i <;> exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem twelveCycle_disjoint : Pairwise fun i j : Fin 4 =>
    (twelveCycle i).Disjoint (twelveCycle j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | (intro x; fin_cases x <;> decide)

theorem four_le_twoLocalOddRank_of_two_dvd {G K : Type} [Group G] [Finite G] [Group K]
    (ι : K →* G) (hι : Function.Injective ι) {n : ℕ} (hn : 12 ≤ n)
    (π : K →* alternatingGroup (Fin n)) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center K) (h2 : 2 ∣ Nat.card π.ker) : 4 ≤ CFSG.twoLocalOddRank G := by
  have : Finite K := Finite.of_injective ι hι
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) 2 h2
  set U : Subgroup K := Subgroup.zpowers (t : K)
  have htK : (t : K) ∈ Subgroup.center K := hZ t.2
  have ht1 : (t : K) ≠ 1 := by
    intro h
    have : orderOf (t : K) = 1 := by rw [h, orderOf_one]
    rw [Subgroup.orderOf_coe, ht] at this
    omega
  have hU : U ≠ ⊥ := by
    intro h
    exact ht1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers (t : K)))
  have hU2 : IsPGroup 2 U := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one]
  obtain ⟨V, hVel, hVcard, -, -⟩ :=
    exists_lift_embedded hn (m := 4) (by norm_num) (by omega) π hπ hZ
      (fun i => ⟨twelveCycle i, (twelveCycle_isThreeCycle i).mem_alternatingGroup⟩)
      (fun i => twelveCycle_isThreeCycle i) (fun i j hij => twelveCycle_disjoint hij)
  exact four_le_twoLocalOddRank_of_normalizing ι hι hU hU2 hVel.toIsMulCommutative
    (fun w hw => CFSG.elemPow_eq_one_of_isElementaryAbelian (A := V) w hw) hVcard
    (le_normalizer_of_le_center ((Subgroup.zpowers_le).mpr htK) V)

theorem alternatingFullCentralKernel_holds : AlternatingFullCentralKernel := by
  intro G _ _ K _ ι hι n _ π hπ hZ hcase
  rcases hcase with ⟨hn, h3⟩ | ⟨hn, h2⟩
  · exact four_le_twoLocalOddRank_of_three_dvd ι hι hn π hπ hZ h3
  · exact four_le_twoLocalOddRank_of_two_dvd ι hι hn π hπ hZ h2

end CFSG.RankThree.PartOne.HNRed
