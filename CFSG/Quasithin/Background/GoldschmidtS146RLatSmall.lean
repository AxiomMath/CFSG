module

public import CFSG.Quasithin.Background.GoldschmidtS146RLatGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Six
public import CFSG.Quasithin.H13.U3U33Fixed
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.EmptyFaithful.S146F4

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section General

variable {X : Type} [Group X] [Finite X]

theorem card_eq_of_isSylowTwoOf_top {a m : ℕ} (hG : Nat.card X = 2 ^ a * m) (hm : ¬ 2 ∣ m)
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : Nat.card U = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  have h := Sylow.card_eq_multiplicity (sylowOfTop hU)
  have h2 : Nat.card ↥U = Nat.card ↥((sylowOfTop hU : Sylow 2 X) : Subgroup X) :=
    congrArg (fun H : Subgroup X => Nat.card ↥H) (coe_sylowOfTop hU).symm
  rw [h2, h, hG, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem eq_top_of_not_dvd_factorial_index [IsSimpleGroup X] (H : Subgroup X)
    (h : ¬ Nat.card X ∣ H.index.factorial) : H = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with hb | ht
  · exfalso
    apply h
    have := H.index_normalCore_dvd_factorial_index
    rwa [hb, Subgroup.index_bot] at this
  · exact eq_top_iff.2 (ht ▸ H.normalCore_le)

theorem latShape_of_card_168 [IsSimpleGroup X] (hcard : Nat.card X = 168) {U : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) : LatShape X U := by
  intro Y hUY hYtop
  have hUc : Nat.card U = 8 := card_eq_of_isSylowTwoOf_top (a := 3) (m := 21) (by omega)
    (by norm_num) hU
  have hdvd : Nat.card Y ∣ 168 := hcard ▸ Subgroup.card_subgroup_dvd_card Y
  have h8 : 8 ∣ Nat.card Y := hUc ▸ Subgroup.card_dvd_of_le hUY
  have hle : Nat.card Y ≤ 168 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : ∀ n < 169, n ∣ 168 → 8 ∣ n → n = 8 ∨ n = 24 ∨ n = 56 ∨ n = 168 := by
    decide +kernel
  have hmul := Subgroup.card_mul_index Y
  rw [hcard] at hmul
  rcases hcases _ (by omega) hdvd h8 with h | h | h | h
  · left
    have : U = Y := Subgroup.eq_of_le_of_card_ge hUY (by omega)
    rw [← this]
    exact Subgroup.le_normalizer
  · right
    left
    omega
  · exfalso
    have h3 : Y.index = 3 := by
      rw [h] at hmul
      omega
    apply hYtop
    refine eq_top_of_not_dvd_factorial_index Y ?_
    rw [h3, hcard]
    decide
  · exfalso
    exact hYtop ((Subgroup.card_eq_iff_eq_top Y).1 (by rw [h, hcard]))

end General

section Alt6

open CFSG.QuasithinUnique.Borel252.A6

theorem card_Sa : Nat.card Sa = 24 := by
  obtain ⟨-, hs, -, -, hsn, -, -, -, -, -⟩ := sizes_ok
  rw [card_of_list R6.enc_inj Sa saL hsn mem_Sa (fun r hr => (sound_Sa r hr).imp fun x hx => hx.2)]
  exact hs

theorem card_Sb : Nat.card Sb = 24 := by
  obtain ⟨-, -, hs, -, -, hsn, -, -, -, -⟩ := sizes_ok
  rw [card_of_list R6.enc_inj Sb sbL hsn mem_Sb (fun r hr => (sound_Sb r hr).imp fun x hx => hx.2)]
  exact hs

theorem isSylowTwoOf_D0 : IsSylowTwoOf (D0.subgroupOf A6s) ⊤ := by
  have hc : Nat.card (D0.subgroupOf A6s) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe D0_le_A6).toEquiv).trans card_D0
  have hmul := Subgroup.card_mul_index (D0.subgroupOf A6s)
  rw [hc] at hmul
  have hA : Nat.card ↥A6s = 360 := card_A6
  have hi : (D0.subgroupOf A6s).index = 45 := by omega
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [hc]; norm_num), ?_⟩
  rw [show ((D0.subgroupOf A6s).subgroupOf ⊤).index = (D0.subgroupOf A6s).index from
    Subgroup.relIndex_top_right _, hi]
  norm_num

theorem latShape_alternatingGroup_six : LatShape ↥A6s (D0.subgroupOf A6s) := by
  intro Y hDY hYtop
  have hinj : Function.Injective A6s.subtype := A6s.subtype_injective
  have hD : D0 ≤ Y.map A6s.subtype := fun d hd =>
    ⟨⟨d, D0_le_A6 hd⟩, hDY (by rwa [Subgroup.mem_subgroupOf]), rfl⟩
  have hA : Y.map A6s.subtype ≤ A6s := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hcardY : Nat.card ↥Y = Nat.card ↥(Y.map A6s.subtype) :=
    (Subgroup.card_map_of_injective hinj).symm
  have hcD : Nat.card (D0.subgroupOf A6s) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe D0_le_A6).toEquiv).trans card_D0
  rcases six_overgroups _ hD hA with h | h | h | h
  · left
    have hY : Y = D0.subgroupOf A6s := by
      ext y
      rw [Subgroup.mem_subgroupOf, ← h]
      constructor
      · intro hy
        exact ⟨y, hy, rfl⟩
      · rintro ⟨z, hz, hzy⟩
        rwa [← hinj hzy]
    rw [hY]
    exact Subgroup.le_normalizer
  · right
    left
    rw [hcardY, h, card_Sa, hcD]
  · right
    left
    rw [hcardY, h, card_Sb, hcD]
  · exfalso
    apply hYtop
    ext y
    simp only [Subgroup.mem_top, iff_true]
    have : (y : Equiv.Perm (Fin 6)) ∈ Y.map A6s.subtype := by
      rw [h]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := this
    rwa [← hinj hzy]

theorem latShape_of_isAlt_six {X : Type} [Group X] [Finite X] (hX : IsAlt 6 X) {U : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) : LatShape X U := by
  obtain ⟨e⟩ := hX
  have : Finite ↥A6s := Finite.of_equiv X e.toEquiv
  exact LatShape.of_equiv_sylow e.symm isSylowTwoOf_D0 latShape_alternatingGroup_six hU

end Alt6

section U33

open CFSG.Quasithin.H13.U3


theorem isSylowTwoOf_u33_T : IsSylowTwoOf u33Data.T ⊤ := by
  have h := u33_syl
  refine ⟨le_top, h.1, ?_⟩
  rw [show (u33Data.T.subgroupOf ⊤).index = u33Data.T.index from Subgroup.relIndex_top_right _]
  exact h.2

theorem latShape_u33 : LatShape U33G u33Data.T := by
  intro Y hTY hYtop
  rcases u33Data.lattice Y hTY with rfl | rfl | rfl | rfl
  · left
    exact Subgroup.le_normalizer
  · right
    left
    rw [card_u33_A, u33_card_T]
  · right
    left
    rw [card_u33_B, u33_card_T]
  · exact absurd rfl hYtop

theorem latShape_of_isPSU_three_three {X : Type} [Group X] [Finite X] (hX : IsPSU 3 3 1 X)
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : LatShape X U := by
  have hLie : CFSG.Blueprint.LieModel X .PSU 3 3 1 := Or.inl ⟨by decide, hX⟩
  let eU : X ≃* U33G := (CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hLie).some.trans
    u33Pres_mulEquiv_PSU3.some.symm
  exact LatShape.of_equiv_sylow eU.symm isSylowTwoOf_u33_T latShape_u33 hU

end U33

end CFSG.Quasithin.GoldS146R
