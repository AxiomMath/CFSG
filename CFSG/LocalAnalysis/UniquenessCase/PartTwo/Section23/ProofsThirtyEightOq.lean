module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyEightPerf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SemiregularBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.BZeroCentralizerZ
public import CFSG.LocalAnalysis.UniquenessCase.UCKCommutingPrimes
public import CFSG.LocalAnalysis.UniquenessCase.UCKFixedPointFree
public import CFSG.GroupTheory.Commutator.ZPowersClosure
public import CFSG.GroupTheory.CyclicSubgroup.NormalizerCommutator

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem orderOf_bar_eq_of_prime {M : Subgroup G} {b : G} (hbM : b ∈ M) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩) = r :=
  CFSG.LocalAnalysis.UniquenessCase.UCK.orderOf_mk'_pCore_eq_of_prime
    (M := ↥M) (b := ⟨b, hbM⟩) hr hr2 (by rw [Subgroup.orderOf_mk]; exact hbr)

namespace Ctx23L

theorem bar_inf_centralizer_eq_bot_of_mem_B0 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty)
    {b : G} (hb : b ∈ c.B0) (hb1 : b ≠ 1) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar)
    (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥) :
    Dbar ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, c.hBM hb⟩} : Set (Bar2 D.M)) = ⊥ := by
  let c' : Ctx23L D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hbZ : b ∉ Subgroup.centralizer (D.Z : Set G) :=
    Ctx23L.not_mem_centralizer_Z_of_mem_B0 D Ch h4 h23 h1930 c hb hb1
  exact Ctx23L.centralizer_bar_inf_eq_bot c' h1930 h54 h6 h71 hsig hb hbZ hq hq2 hDn hDq hDnc
    hDexp hDcl

end Ctx23L

namespace Ctx23L

theorem le_M_of_le_pCoreOf {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {X : Subgroup G} (hX : X ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) : X ≤ D.M :=
  hX.trans ((uc22p20b_pCoreOf_le_T D le_sup_right).trans D.sylowM.le)

end Ctx23L

theorem barImage_le_centralizer_of_isCyclic {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1930 : H1930 D) (hn3 : H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ c.n)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hcyc : IsCyclic ↥Dbar)
    {X : Subgroup G} (hX : X ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))
    (hB0norm : c.B0 ≤ Subgroup.normalizer (X : Set G))
    (hperf : ∀ b ∈ c.B0, b ≠ 1 → Subgroup.closure {z : G | ∃ x ∈ X, z = ⁅x, b⁆} = X) :
    barImage D.M X ≤ Subgroup.centralizer (Dbar : Set (Bar2 D.M)) := by
  obtain ⟨b1, hb1B0, hb1ne, -⟩ := uc22s2338_exists_b1 D c h1930 hn3
  have hX_le_M : X ≤ D.M := c.le_M_of_le_pCoreOf hX
  have hcommG : ⁅Subgroup.zpowers b1, X⁆ = X :=
    CFSG.GroupTheory.commutator_zpowers_eq_of_closure (hB0norm hb1B0)
      (hperf b1 hb1B0 hb1ne)
  let bbar : Bar2 D.M := uc22p21cPi D.M ⟨b1, c.hBM hb1B0⟩
  have hcomm : ⁅Subgroup.zpowers bbar, barImage D.M X⁆ = barImage D.M X :=
    CFSG.GroupTheory.commutator_zpowers_map_subgroupOf_eq (uc22p21cPi D.M)
      (c.hBM hb1B0) hX_le_M hcommG
  haveI : Dbar.Normal := hDn
  haveI : IsCyclic ↥Dbar := hcyc
  have hnorm : ∀ Y : Subgroup (Bar2 D.M), Y ≤ Subgroup.normalizer (Dbar : Set (Bar2 D.M)) := by
    intro Y
    rw [Subgroup.normalizer_eq_top (H := Dbar)]
    exact le_top
  have hle := CFSG.GroupTheory.CyclicSubgroup.commutator_le_centralizer Dbar
    (Subgroup.zpowers bbar) (barImage D.M X) (hnorm _) (hnorm _)
  simpa only [hcomm] using hle

namespace Ctx23L

theorem exists_barImage_orderOf_eq {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hn : c.n ≠ 0) {r : ℕ}
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ c.n - 1) :
    ∃ a ∈ barImage D.M c.B0, orderOf a = r := by
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ c.n := dvd_pow_self 2 hn
    have h1 : 1 ≤ 2 ^ c.n := Nat.one_le_two_pow
    omega
  have hrmem : r ∈ etaSet c.n := ⟨hr, hrdvd⟩
  rw [← c.hpi] at hrmem
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨b, hbord⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) r hrmem.2
  have hbr : orderOf (b : G) = r := by rw [Subgroup.orderOf_coe, hbord]
  refine ⟨uc22p21cPi D.M ⟨(b : G), c.hBM b.2⟩, ?_, ?_⟩
  · exact uc22p21c_mem_barImage.2 ⟨⟨(b : G), c.hBM b.2⟩, b.2, rfl⟩
  · exact orderOf_bar_eq_of_prime (hbM := c.hBM b.2) hr hr2 hbr

theorem barImage_B0_b7g_data {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch)
    (hsig : D.sig.Nonempty) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar)
    (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥) {X : Subgroup G}
    (hX : X ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))
    (hB0norm : c.B0 ≤ Subgroup.normalizer (X : Set G))
    (hperf : ∀ b ∈ c.B0, b ≠ 1 → Subgroup.closure {z : G | ∃ x ∈ X, z = ⁅x, b⁆} = X) :
    (∀ a ∈ barImage D.M c.B0, ∀ b ∈ barImage D.M c.B0, Commute a b) ∧
      (∀ a ∈ barImage D.M c.B0, a ≠ 1 →
        Dbar ⊓ Subgroup.centralizer ({a} : Set (Bar2 D.M)) = ⊥) ∧
      (∀ a ∈ barImage D.M c.B0, a ≠ 1 →
        ⁅Subgroup.zpowers a, barImage D.M X⁆ = barImage D.M X) := by
  have hX_le_M : X ≤ D.M := c.le_M_of_le_pCoreOf hX
  refine ⟨?_, ?_, ?_⟩
  · haveI : IsMulCommutative c.B0 := c.hB0.2.1
    haveI : IsMulCommutative (c.B0.subgroupOf D.M) :=
      Subgroup.comap_injective_isMulCommutative c.B0 D.M.subtype_injective
    haveI : IsMulCommutative (barImage D.M c.B0) := Subgroup.map_isMulCommutative _ _
    exact fun a ha b hb => setLike_mul_comm ha hb
  · intro a ha ha1
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 ha
    have hm1 : (m : G) ≠ 1 := fun h => ha1 (by
      have hm_eq : m = 1 := Subtype.ext h
      rw [hm_eq, map_one])
    have hb := Ctx23L.bar_inf_centralizer_eq_bot_of_mem_B0 c h4 h23 h1930 h54 h6 h71 hsig
      hm hm1 hq hq2 hDn hDq hDnc hDexp hDcl
    simpa using hb
  · intro a ha ha1
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 ha
    have hm1 : (m : G) ≠ 1 := fun h => ha1 (by
      have hm_eq : m = 1 := Subtype.ext h
      rw [hm_eq, map_one])
    have hcommG : ⁅Subgroup.zpowers (m : G), X⁆ = X :=
      CFSG.GroupTheory.commutator_zpowers_eq_of_closure (hB0norm hm)
        (hperf (m : G) hm hm1)
    have hmap := CFSG.GroupTheory.commutator_zpowers_map_subgroupOf_eq (uc22p21cPi D.M)
      m.2 hX_le_M hcommG
    simpa [barImage] using hmap

end Ctx23L

theorem barImage_le_centralizer_of_not_isCyclic {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty)
    (hn3 : H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ c.n)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Dbar : Subgroup (Bar2 D.M)}
    (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar) (hD1 : Dbar ≠ ⊥)
    (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥)
    {X : Subgroup G} (hX : X ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))
    (hB0norm : c.B0 ≤ Subgroup.normalizer (X : Set G))
    (hperf : ∀ b ∈ c.B0, b ≠ 1 → Subgroup.closure {z : G | ∃ x ∈ X, z = ⁅x, b⁆} = X) :
    barImage D.M X ≤ Subgroup.centralizer (Dbar : Set (Bar2 D.M)) := by
  have hX2 : IsPGroup 2 X :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (c.L ⊔ D.T)).to_le hX
  have hXbar2 : IsPGroup 2 (barImage D.M X) :=
    (hX2.comap_subtype (K := D.M)).map (uc22p21cPi D.M)
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (IsPGroup q ↥Dbar) := ⟨hDq⟩
  haveI : IsElementaryAbelian q (↥Dbar ⧸ frattini ↥Dbar) :=
    CFSG.isElementaryAbelian_quotient_frattini
  obtain ⟨hAc, hAP, hTA⟩ :=
    Ctx23L.barImage_B0_b7g_data c h4 h23 h1930 h54 h6 h71 hsig hq hq2
      hDn hDq hDnc hDexp hDcl hX hB0norm hperf
  refine CFSG.LocalAnalysis.UniquenessCase.UCK.le_centralizer_of_semiregular
    (q := q) (P := Dbar) (T := barImage D.M X) (A := barImage D.M c.B0)
    hq2 hDq hD1 hXbar2 ?_ hAc hAP hTA (hn3 h1930 c) ?_
  · exact CFSG.GroupTheory.map_subgroupOf_le_normalizer (uc22p21cPi D.M) hB0norm
  · intro r hr hrdvd
    exact Ctx23L.exists_barImage_orderOf_eq c (by have := hn3 h1930 c; omega) hr hrdvd

theorem barImage_le_centralizer_of_normal_q {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty)
    (hn3 : H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ c.n)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Dbar : Subgroup (Bar2 D.M)}
    (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar) (hD1 : Dbar ≠ ⊥)
    (hDexp : ∀ y ∈ Dbar, y ^ q = 1) (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥)
    {X : Subgroup G} (hX : X ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))
    (hB0norm : c.B0 ≤ Subgroup.normalizer (X : Set G))
    (hperf : ∀ b ∈ c.B0, b ≠ 1 → Subgroup.closure {z : G | ∃ x ∈ X, z = ⁅x, b⁆} = X) :
    barImage D.M X ≤ Subgroup.centralizer (Dbar : Set (Bar2 D.M)) := by
  by_cases hcyc : IsCyclic ↥Dbar
  · exact barImage_le_centralizer_of_isCyclic c h1930 hn3 hDn hcyc hX hB0norm hperf
  · exact barImage_le_centralizer_of_not_isCyclic c h4 h23 h1930 h54 h6 h71 hsig hn3
      hq hq2 hDn hDq hD1 hcyc hDexp hDcl hX hB0norm hperf

theorem s23_38_perf_Oq_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch)
    (hsig : D.sig.Nonempty) (hn3 : H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ c.n) :
    S23_38_perf_Oq D Ch := by
  intro h1930 c q hq hq2 X hX hB0norm hperf
  let Q : Subgroup (Bar2 D.M) := CFSG.pCore q (Bar2 D.M)
  by_cases hQ1 : Q = ⊥
  · rw [show CFSG.pCore q (Bar2 D.M) = ⊥ from hQ1,
      Subgroup.centralizer_eq_top_iff_subset.mpr (SetLike.coe_subset_coe.mpr bot_le)]
    exact le_top
  · haveI : Fact q.Prime := ⟨hq⟩
    haveI : Q.Normal := CFSG.pCore_normal
    obtain ⟨D₀, hDn, hDq, hDne, hDexp, hDcl, hDfix⟩ :=
      CFSG.GroupTheory.exists_critical_map_subtype (q := q) (Q := Q) hq2
        CFSG.pCore_isPGroup hQ1
    let Dbar : Subgroup (Bar2 D.M) := D₀.map Q.subtype
    have hcent : barImage D.M X ≤ Subgroup.centralizer (Dbar : Set (Bar2 D.M)) :=
      barImage_le_centralizer_of_normal_q c h4 h23 h1930 h54 h6 h71 hsig hn3
        hq hq2 hDn hDq hDne hDexp hDcl hX hB0norm hperf
    have hX2 : IsPGroup 2 X :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (c.L ⊔ D.T)).to_le hX
    have hXbar2 : IsPGroup 2 (barImage D.M X) :=
      (hX2.comap_subtype (K := D.M)).map (uc22p21cPi D.M)
    intro t ht
    exact CFSG.GroupTheory.mem_centralizer_of_mem_centralizer_map_subtype (q := q) (Q := Q)
      (D := D₀) hq2 hDfix (hXbar2.to_le (Subgroup.zpowers_le.mpr ht)) (hcent ht)
