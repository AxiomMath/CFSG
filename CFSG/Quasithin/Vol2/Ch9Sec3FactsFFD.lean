module

public import CFSG.Quasithin.Vol2.Ch9Sec3FactsFF
public import CFSG.Quasithin.Vol2.Ch9Sec3FFDB51
public import CFSG.Quasithin.Vol2.Ch9Sec3FFDMod
public import CFSG.Walter.Bender1970.S3.CoreExchangeTools

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

theorem a7FFNoA5Fact_of (h51 : AsB51) (h56 : AsB56) : A7FFNoA5Fact := by
  intro G _ _ Y T K KY V hSQ hT hKKY hKYY hYKY hperf hA5 hTK hred hA7 hJ hKC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe : IsElemAbelian 2 V := hred.2.2.1
  have : IsMulCommutative ↥V := hVe.1
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hKYN : KY ≤ Subgroup.normalizer (V : Set G) := hKYY.trans hYV
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKKY.trans hKYN
  obtain ⟨hdir, hshape⟩ := FFD.b51_alt7 h51 h56 hSQ hT hKKY hKYY hYKY hred hA7 hJ
  have hJT : thompsonJ T ≤ Subgroup.normalizer (V : Set G) :=
    (iSup₂_le fun _ hA => hA.1).trans (hT.1.trans hYV)
  have hKV : ¬ K ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hJ (FFD.commutator_le_centralizer h hJT)
  have h60 := FFD.card_autOn_dvd hKN hperf hA5 hKV
  set U := ⁅V, KY⁆ with hU
  have hUV : U ≤ V := A7ZK.commutator_le_left_of_le_normalizer hKYN
  have hKYU : KY ≤ Subgroup.normalizer (U : Set G) :=
    A7ZK.le_normalizer_commutator hKYN Subgroup.le_normalizer
  have hUKU : ⁅U, K⁆ ≤ U := A7ZK.commutator_le_left_of_le_normalizer (hKKY.trans hKYU)
  have hUK : ⁅U, K⁆ ≠ ⊥ := by
    intro h
    apply hKV
    refine FFD.le_centralizer_of_le_centralizer_commutator hKYN hdir.1 hKKY ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact Subgroup.le_centralizer_iff.mp h
  have hTU : T ≤ Subgroup.normalizer (U : Set G) :=
    A7ZK.le_normalizer_commutator (hT.1.trans hYV) (hT.1.trans hYKY)
  have hTUK : T ≤ Subgroup.normalizer ((⁅U, K⁆ : Subgroup G) : Set G) :=
    A7ZK.le_normalizer_commutator hTU hTK
  have hUK2 : IsPGroup 2 ↥⁅U, K⁆ := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    have hx : (x : G) ∈ V := hUV (hUKU x.2)
    have h2 := hVe.2 (x : G) hx
    simpa [pow_two] using h2
  have hne := CFSG.Walter.inf_centralizer_ne_bot_of_isPGroup Nat.prime_two hT.2.1 hUK2 hTUK hUK
  obtain ⟨⟨u, huUK, huT⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huV : u ∈ V := hUV (hUKU huUK)
  have huK : u ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKC hk) u ⟨huV, huT⟩).symm
  rcases hshape with hnat | hfour
  · have hTKY : IsSylowTwoOf (T ⊓ KY) KY := A4.isSylowTwoOf_inf_normal hT hKYY hYKY
    have hbot := FFD.commutator_inf_centralizer_eq_bot_d7 hKKY hKYN hTKY
      (inf_le_left.trans hTK) (FFD.perfect_autOn hKN hperf) ((by norm_num : 15 ∣ 60).trans h60)
      (FFD.not_dvd_card_autOn hKN hA5 (Or.inl rfl)) (FFD.not_dvd_card_autOn hKN hA5 (Or.inr rfl))
      hA7 hnat
    have hmem : u ∈ ⁅U, K⁆ ⊓ Subgroup.centralizer (K : Set G) := ⟨huUK, huK⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hu1' hmem
  · have hbot := FFD.inf_centralizer_eq_bot_four hKKY hKYN ((by norm_num : 5 ∣ 60).trans h60)
      hdir.1 hfour
    have hmem : u ∈ U ⊓ Subgroup.centralizer (K : Set G) := ⟨hUKU huUK, huK⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hu1' hmem

end CFSG.Quasithin.H13.Ch9
