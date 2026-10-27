module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.GoodPath

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

private theorem mem_fixingSubgroup_of_orderOf_two_of_odd_relIndex {z : V} {K : Subgroup H}
    (hK : K ≤ MulAction.stabilizer H z)
    (hodd : Odd ((fixingSubgroup H (Γ.neighborSet z)).relIndex K))
    {u : H} (huK : u ∈ K) (hu2 : orderOf u = 2) :
    u ∈ fixingSubgroup H (Γ.neighborSet z) := by
  classical
  have hKA : K ≤ Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet z) : Set H) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) k z
    rw [MulAction.mem_stabilizer_iff.mp (hK hk)] at h
    exact h.symm
  haveI hN : ((fixingSubgroup H (Γ.neighborSet z)).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
    exact (le_inf hKA K.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  by_contra huA
  let uK : K := ⟨u, huK⟩
  have huK2 : orderOf uK = 2 := by
    rw [← Subgroup.orderOf_coe uK]
    exact hu2
  let φ : K →* K ⧸ (fixingSubgroup H (Γ.neighborSet z)).subgroupOf K :=
    QuotientGroup.mk' _
  have hclass_ne : φ uK ≠ 1 := by
    intro h1
    apply huA
    have hmem : uK ∈ (fixingSubgroup H (Γ.neighborSet z)).subgroupOf K :=
      (QuotientGroup.eq_one_iff (N := (fixingSubgroup H (Γ.neighborSet z)).subgroupOf K) uK).mp
        (by simpa [φ] using h1)
    exact hmem
  have hclass2 : orderOf (φ uK) = 2 := by
    have hdvd : orderOf (φ uK) ∣ orderOf uK := orderOf_map_dvd φ uK
    rw [huK2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hclass_ne
    · exact h
  have h2 : 2 ∣ Nat.card (K ⧸ (fixingSubgroup H (Γ.neighborSet z)).subgroupOf K) :=
    hclass2 ▸ orderOf_dvd_natCard (φ uK)
  have h2' : 2 ∣ ((fixingSubgroup H (Γ.neighborSet z)).subgroupOf K).index := by
    simpa only [Subgroup.index_eq_card] using h2
  exact hodd.not_two_dvd_nat h2'

theorem isGoodPath_snoc_unique [Finite H] {n : ℕ} (hn : 3 ≤ n) (hW : WeissFree H Γ n)
    (hL : ∀ z, LocalFacts H Γ z) {s : ℕ} (hs : n + 1 ≤ s) {p : GPath Γ s}
    {w w' : V} (hw : Γ.Adj (p s) w) (hw' : Γ.Adj (p s) w')
    (hg : IsGoodPath H (p.snoc w hw)) (hg' : IsGoodPath H (p.snoc w' hw')) : w = w' := by
  classical
  have hp : p.NoBack := by
    intro i hi
    have h := hg.1 i (by omega)
    rwa [GPath.snoc_of_le p w hw (by omega),
      GPath.snoc_of_le p w hw (by omega)] at h
  let q : GPath Γ (s + 1) := p.snoc w hw
  let q' : GPath Γ (s + 1) := p.snoc w' hw'
  have hqnb : q.NoBack := hg.1
  have hq'nb : q'.NoBack := hg'.1
  have hwne : w ≠ p (s - 1) := by
    intro h
    have hnb := hqnb (s - 1) (by omega)
    rw [show (s - 1) + 2 = s + 1 by omega] at hnb
    exact hnb (by rw [GPath.snoc_of_le p w hw (by omega), GPath.snoc_last p w hw, h])
  have hw'ne : w' ≠ p (s - 1) := by
    intro h
    have hnb := hq'nb (s - 1) (by omega)
    rw [show (s - 1) + 2 = s + 1 by omega] at hnb
    exact hnb (by rw [GPath.snoc_of_le p w' hw' (by omega), GPath.snoc_last p w' hw', h])
  have hzw : Γ.Adj (p s) (p (s - 1)) := by
    have h := p.adj (s - 1) (by omega)
    rw [show s - 1 + 1 = s by omega] at h
    exact h.symm
  let A : Subgroup H := GPath.stabPath (H := H) q ⊓ socleAt H Γ (p s)
  let A' : Subgroup H := GPath.stabPath (H := H) q' ⊓ socleAt H Γ (p s)
  let S : Set H := {x : H | (x ∈ A ∨ x ∈ A') ∧ Odd (orderOf x)}
  let K : Subgroup H := Subgroup.closure S
  have hAle : A ≤ socTorus H Γ (p s) (p (s - 1)) w := by
    intro a ha
    rw [socTorus]
    refine ⟨⟨ha.2, ?_⟩, ?_⟩
    · exact MulAction.mem_stabilizer_iff.mpr (by
        have h := GPath.mem_stabPath_iff.mp ha.1 (s - 1) (by omega)
        rwa [show q (s - 1) = p (s - 1) from
          GPath.snoc_of_le p w hw (by omega)] at h)
    · exact MulAction.mem_stabilizer_iff.mpr (by
        have h := GPath.mem_stabPath_iff.mp ha.1 (s + 1) (by omega)
        rwa [show q (s + 1) = w from GPath.snoc_last p w hw] at h)
  have hA'le : A' ≤ socTorus H Γ (p s) (p (s - 1)) w' := by
    intro a ha
    rw [socTorus]
    refine ⟨⟨ha.2, ?_⟩, ?_⟩
    · exact MulAction.mem_stabilizer_iff.mpr (by
        have h := GPath.mem_stabPath_iff.mp ha.1 (s - 1) (by omega)
        rwa [show q' (s - 1) = p (s - 1) from
          GPath.snoc_of_le p w' hw' (by omega)] at h)
    · exact MulAction.mem_stabilizer_iff.mpr (by
        have h := GPath.mem_stabPath_iff.mp ha.1 (s + 1) (by omega)
        rwa [show q' (s + 1) = w' from GPath.snoc_last p w' hw'] at h)
  have hAsup : socTorus H Γ (p s) (p (s - 1)) w ≤
      A ⊔ fixingSubgroup H (Γ.neighborSet (p s)) := by
    have h := hg.2 s (by omega) (by omega)
    rw [show q s = p s from GPath.snoc_of_le p w hw (by omega),
      show q (s - 1) = p (s - 1) from GPath.snoc_of_le p w hw (by omega),
      show q (s + 1) = w from GPath.snoc_last p w hw] at h
    exact h
  have hA'sup : socTorus H Γ (p s) (p (s - 1)) w' ≤
      A' ⊔ fixingSubgroup H (Γ.neighborSet (p s)) := by
    have h := hg'.2 s (by omega) (by omega)
    rw [show q' s = p s from GPath.snoc_of_le p w' hw' (by omega),
      show q' (s - 1) = p (s - 1) from GPath.snoc_of_le p w' hw' (by omega),
      show q' (s + 1) = w' from GPath.snoc_last p w' hw'] at h
    exact h
  obtain ⟨b, hbA, hbodd, hbgen⟩ :=
    (hL (p s)).torusGen (p (s - 1)) w hzw hw hwne.symm A hAle hAsup
  obtain ⟨b', hbA', hb'odd, hb'gen⟩ :=
    (hL (p s)).torusGen (p (s - 1)) w' hzw hw' hw'ne.symm A' hA'le hA'sup
  have hbK : b ∈ K := Subgroup.subset_closure ⟨Or.inl hbA, hbodd⟩
  have hb'K : b' ∈ K := Subgroup.subset_closure ⟨Or.inr hbA', hb'odd⟩
  have hb_le : Subgroup.closure ({b} : Set H) ≤ K := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hbK
  have hb'_le : Subgroup.closure ({b'} : Set H) ≤ K := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hb'K
  have htor_le_K : socTorus H Γ (p s) (p (s - 1)) w ≤
      K ⊔ fixingSubgroup H (Γ.neighborSet (p s)) :=
    hbgen.trans (sup_le_sup hb_le le_rfl)
  have htor'_le_K : socTorus H Γ (p s) (p (s - 1)) w' ≤
      K ⊔ fixingSubgroup H (Γ.neighborSet (p s)) :=
    hb'gen.trans (sup_le_sup hb'_le le_rfl)
  have hSodd : ∀ x ∈ S, Odd (orderOf x) := fun _ hx => hx.2
  have hSsub : ∀ i, 1 ≤ i → i ≤ s - 1 →
      S ⊆ ↑(MulAction.stabilizer H (p i) ⊓ MulAction.stabilizer H (p (i - 1)) ⊓
        MulAction.stabilizer H (p (i + 1))) := by
    intro i hi1 his x hx
    rcases hx.1 with hxA | hxA
    · have hfix := GPath.mem_stabPath_iff.mp hxA.1
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact MulAction.mem_stabilizer_iff.mpr (by
          have h := hfix i (by omega)
          rwa [show q i = p i from GPath.snoc_of_le p w hw (by omega)] at h)
      · exact MulAction.mem_stabilizer_iff.mpr (by
          have h := hfix (i - 1) (by omega)
          rwa [show q (i - 1) = p (i - 1) from
            GPath.snoc_of_le p w hw (by omega)] at h)
      · exact MulAction.mem_stabilizer_iff.mpr (by
          have h := hfix (i + 1) (by omega)
          rwa [show q (i + 1) = p (i + 1) from
            GPath.snoc_of_le p w hw (by omega)] at h)
    · have hfix := GPath.mem_stabPath_iff.mp hxA.1
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact MulAction.mem_stabilizer_iff.mpr (by
          have h := hfix i (by omega)
          rwa [show q' i = p i from GPath.snoc_of_le p w' hw' (by omega)] at h)
      · exact MulAction.mem_stabilizer_iff.mpr (by
          have h := hfix (i - 1) (by omega)
          rwa [show q' (i - 1) = p (i - 1) from
            GPath.snoc_of_le p w' hw' (by omega)] at h)
      · exact MulAction.mem_stabilizer_iff.mpr (by
          have h := hfix (i + 1) (by omega)
          rwa [show q' (i + 1) = p (i + 1) from
            GPath.snoc_of_le p w' hw' (by omega)] at h)
  have hKle : ∀ i, 1 ≤ i → i ≤ s - 1 → K ≤ MulAction.stabilizer H (p i) := by
    intro i hi1 his
    change Subgroup.closure S ≤ MulAction.stabilizer H (p i)
    rw [Subgroup.closure_le]
    exact (hSsub i hi1 his).trans fun _ hx => hx.1.1
  have hoddS : ∀ i, 1 ≤ i → i ≤ s - 1 →
      Odd ((fixingSubgroup H (Γ.neighborSet (p i))).relIndex K) := by
    intro i hi1 his
    have hne : p (i - 1) ≠ p (i + 1) := by
      have h := hp (i - 1) (by omega)
      rw [show i - 1 + 2 = i + 1 by omega] at h
      exact h
    have h1 : Γ.Adj (p i) (p (i - 1)) := by
      have h := p.adj (i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at h
      exact h.symm
    have h2 : Γ.Adj (p i) (p (i + 1)) := p.adj i (by omega)
    have hres := (hL (p i)).oddClosure (p (i - 1)) (p (i + 1)) h1 h2 hne S
      (hSsub i hi1 his) hSodd
    change Odd ((fixingSubgroup H (Γ.neighborSet (p i))).relIndex (Subgroup.closure S))
    exact hres
  have hKle_z : K ≤ MulAction.stabilizer H (p s) := by
    change Subgroup.closure S ≤ MulAction.stabilizer H (p s)
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx.1 with hxA | hxA
    · have h := GPath.mem_stabPath_iff.mp hxA.1 s (by omega)
      rw [show q s = p s from GPath.snoc_of_le p w hw (by omega)] at h
      exact h
    · have h := GPath.mem_stabPath_iff.mp hxA.1 s (by omega)
      rw [show q' s = p s from GPath.snoc_of_le p w' hw' (by omega)] at h
      exact h
  by_cases hoddz : Odd ((fixingSubgroup H (Γ.neighborSet (p s))).relIndex K)
  · obtain ⟨y, hyadj, hyne, hyfix⟩ :=
      (hL (p s)).oddFix (p (s - 1)) hzw K
        (le_inf hKle_z (hKle (s - 1) (by omega) le_rfl)) hoddz
    have hKnorm : K ≤
        Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet (p s)) : Set H) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) k (p s)
      rw [MulAction.mem_stabilizer_iff.mp (hKle_z hk)] at h
      exact h.symm
    have hfix_torus : ∀ t ∈ socTorus H Γ (p s) (p (s - 1)) w, t • y = y := by
      intro t ht
      have ht' : t ∈ (↑(K ⊔ fixingSubgroup H (Γ.neighborSet (p s))) : Set H) :=
        htor_le_K ht
      rw [Subgroup.coe_mul_of_left_le_normalizer_right K
        (fixingSubgroup H (Γ.neighborSet (p s))) hKnorm] at ht'
      rcases ht' with ⟨k, hk, g, hgmem, hkg⟩
      rw [← hkg, mul_smul, (mem_fixingSubgroup_iff H).mp hgmem y hyadj, hyfix k hk]
    have hyw : y = w := by
      rcases (hL (p s)).torusFix (p (s - 1)) w y hzw hw hwne.symm hyadj hfix_torus with h | h
      · exact absurd h hyne
      · exact h
    have hfix_torus' : ∀ t ∈ socTorus H Γ (p s) (p (s - 1)) w', t • y = y := by
      intro t ht
      have ht' : t ∈ (↑(K ⊔ fixingSubgroup H (Γ.neighborSet (p s))) : Set H) :=
        htor'_le_K ht
      rw [Subgroup.coe_mul_of_left_le_normalizer_right K
        (fixingSubgroup H (Γ.neighborSet (p s))) hKnorm] at ht'
      rcases ht' with ⟨k, hk, g, hgmem, hkg⟩
      rw [← hkg, mul_smul, (mem_fixingSubgroup_iff H).mp hgmem y hyadj, hyfix k hk]
    have hyw' : y = w' := by
      rcases (hL (p s)).torusFix (p (s - 1)) w' y hzw hw' hw'ne.symm hyadj
        hfix_torus' with h | h
      · exact absurd h hyne
      · exact h
    exact hyw.symm.trans hyw'
  · have heven : Even ((fixingSubgroup H (Γ.neighborSet (p s))).relIndex K) :=
      Nat.not_odd_iff_even.mp hoddz
    have h2K : 2 ∣ Nat.card K := by
      have hmul := Subgroup.relIndex_mul_card
        (H := fixingSubgroup H (Γ.neighborSet (p s))) (K := K)
      rw [← hmul]
      exact dvd_mul_of_dvd_left heven.two_dvd _
    obtain ⟨uK, huKord⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2K
    let u : H := uK
    have huK : u ∈ K := uK.2
    have hu2 : orderOf u = 2 := (Subgroup.orderOf_coe uK).trans huKord
    have huG1 : ∀ i, 1 ≤ i → i ≤ s - 1 →
        u ∈ fixingSubgroup H (Γ.neighborSet (p i)) := by
      intro i hi1 his
      exact mem_fixingSubgroup_of_orderOf_two_of_odd_relIndex (z := p i) (K := K)
        (hKle i hi1 his) (hoddS i hi1 his) huK hu2
    let r : GPath Γ n := (p.drop 1 (by omega)).take n (by omega)
    have hr_of_le : ∀ {i : ℕ}, i ≤ n → r i = p (1 + i) := by
      intro i hi
      change (p.drop 1 (by omega)).take n (by omega) i = p (1 + i)
      rw [GPath.take_apply_of_le _ _ _ hi, GPath.drop_apply _ _ _ (by omega)]
    have hrnb : r.NoBack := by
      change ((p.drop 1 (by omega)).take n (by omega)).NoBack
      exact (hp.drop 1 (by omega)).take n (by omega)
    have hfixr : ∀ i, i ≤ n → u • r i = r i := by
      intro i hi
      rw [hr_of_le hi]
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0
        have hu2p : u ∈ fixingSubgroup H (Γ.neighborSet (p 2)) :=
          huG1 2 (by omega) (by omega)
        have hadj : Γ.Adj (p 2) (p 1) := (p.adj 1 (by omega)).symm
        simpa using (mem_fixingSubgroup_iff H).mp hu2p (p 1) hadj
      · have huip : u ∈ fixingSubgroup H (Γ.neighborSet (p i)) :=
          huG1 i hi0 (by omega)
        have hadj : Γ.Adj (p i) (p (1 + i)) := by
          have h := p.adj i (by omega)
          rwa [show i + 1 = 1 + i by omega] at h
        simpa using (mem_fixingSubgroup_iff H).mp huip (p (1 + i)) hadj
    have hfixr0 : ∀ y, Γ.Adj (r 0) y → u • y = y := by
      intro y hy
      have hr0 : r 0 = p 1 := by simpa using hr_of_le (i := 0) (by omega)
      rw [hr0] at hy
      have hu1 : u ∈ fixingSubgroup H (Γ.neighborSet (p 1)) := huG1 1 (by omega) (by omega)
      exact (mem_fixingSubgroup_iff H).mp hu1 y hy
    have hfixr1 : ∀ y, Γ.Adj (r 1) y → u • y = y := by
      intro y hy
      have hr1 : r 1 = p 2 := by simpa using hr_of_le (i := 1) (by omega)
      rw [hr1] at hy
      have hu2p : u ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := huG1 2 (by omega) (by omega)
      exact (mem_fixingSubgroup_iff H).mp hu2p y hy
    have hone : u = 1 := hW r hrnb u hfixr hfixr0 hfixr1
    rw [hone, orderOf_one] at hu2
    omega

theorem stabPath_le_stabilizer_of_isGoodPath [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hW : WeissFree H Γ n) (hL : ∀ z, LocalFacts H Γ z) {s : ℕ} (hs : n + 1 ≤ s)
    {p : GPath Γ s} {w : V} (hw : Γ.Adj (p s) w)
    (hg : IsGoodPath H (p.snoc w hw)) : GPath.stabPath (H := H) p ≤ MulAction.stabilizer H w := by
  intro g hgstab
  rw [MulAction.mem_stabilizer_iff]
  have hgs : g • p s = p s := by
    have h := GPath.mem_stabPath_iff.mp hgstab s le_rfl
    simpa using h
  have hgw : Γ.Adj (p s) (g • w) := by
    have h := (GraphAction.adj_smul g (p s) w).mpr hw
    rwa [hgs] at h
  have hsmul : g • (p.snoc w hw) = p.snoc (g • w) hgw := by
    apply GPath.ext'
    intro i hi
    by_cases his : i ≤ s
    · have hpi : p.snoc w hw i = p i := GPath.snoc_of_le p w hw his
      have hgi : p.snoc (g • w) hgw i = p i := GPath.snoc_of_le p (g • w) hgw his
      rw [GPath.smul_apply, hpi, hgi]
      exact GPath.mem_stabPath_iff.mp hgstab i his
    · have his' : i = s + 1 := by omega
      subst his'
      rw [GPath.smul_apply, GPath.snoc_last p w hw, GPath.snoc_last p (g • w) hgw]
  have hg' : IsGoodPath H (p.snoc (g • w) hgw) := hsmul ▸ hg.smul g
  have hweq : w = g • w :=
    isGoodPath_snoc_unique hn hW hL hs hw hgw hg hg'
  exact hweq.symm

end CFSG.Quasithin.Stroth.WeissDelta

end
