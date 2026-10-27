module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Cent
public import CFSG.RankThree.GF2n.Stroth80.Sec101Comp
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndPerfect
public import CFSG.RankThree.GF2n.Stroth80.Sec101SatRoots
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem mem_layer_of_endgOuterHom_eq_one {X : Type} [Group X] [Finite X]
    {L Λ H₀ : Subgroup X} [hLn : L.Normal] (hΛH : Λ ≤ H₀) (hLH : L ≤ H₀)
    (hn : ∀ k ∈ Λ, ∀ l ∈ L, k * l * k⁻¹ ∈ L)
    (hcent : ∀ x ∈ H₀, (∀ y ∈ L, x * y = y * x) → x = 1)
    {k : ↥Λ} (hk : endgOuterHom L Λ hn k = 1) : (k : X) ∈ L := by
  obtain ⟨l, hl, hconj⟩ := (endg_outerHom_eq_one_iff L Λ hn k).mp hk
  have hdH : (k : X) * l⁻¹ ∈ H₀ := H₀.mul_mem (hΛH k.2) (H₀.inv_mem (hLH hl))
  have hdcomm : ∀ y ∈ L, ((k : X) * l⁻¹) * y = y * ((k : X) * l⁻¹) := by
    intro y hy
    have hly : l⁻¹ * y * l ∈ L := by simpa using hLn.conj_mem y hy l⁻¹
    have hconj' : ((k : X) * l⁻¹) * y * ((k : X) * l⁻¹)⁻¹ = y := by
      calc ((k : X) * l⁻¹) * y * ((k : X) * l⁻¹)⁻¹
          = (k : X) * (l⁻¹ * y * l) * (k : X)⁻¹ := by group
        _ = l * (l⁻¹ * y * l) * l⁻¹ := hconj _ hly
        _ = y := by group
    calc ((k : X) * l⁻¹) * y
        = (((k : X) * l⁻¹) * y * ((k : X) * l⁻¹)⁻¹) * ((k : X) * l⁻¹) := by group
      _ = y * ((k : X) * l⁻¹) := by rw [hconj']
  have hd1 : (k : X) * l⁻¹ = 1 := hcent _ hdH hdcomm
  have hkl : (k : X) = l := by
    have := congrArg (fun z => z * l) hd1
    simpa [mul_assoc] using this
  rwa [hkl]

private theorem Sec10Hyp.sixty_four_le_card_bar_LB [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) :
    64 ≤ Nat.card ↥(bar M Q (LB M Q B)) := by
  rw [hc.card_bar_LB_of_34 h34 H.width H.n_gt H.noA2 H.gen]
  calc 64 = 4 ^ 3 := by norm_num
    _ ≤ Nat.card Z ^ 3 := Nat.pow_le_pow_left hc.hyp.q4 3
    _ ≤ Nat.card Z ^ (n - 1) :=
        Nat.pow_le_pow_right (n := Nat.card Z) Nat.card_pos
          (by simpa using Nat.sub_le_sub_right (Sec10Hyp.four_le h34 H) 1)

theorem Sec10Hyp.false_of_small_layer [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h44 : Stroth44Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) (hout : OutCyc ↥(layer (Mbar M Q)))
    (h8 : ∀ T : Sylow 2 ↥(layer (Mbar M Q)), Nat.card (T : Subgroup ↥(layer (Mbar M Q))) ≤ 8) :
    False := by
  let L := layer (Mbar M Q)
  let Λ := bar M Q (LB M Q B)
  haveI hchar : L.Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hnorm : L.Normal := Subgroup.normal_of_characteristic L
  have hn : ∀ k ∈ Λ, ∀ l ∈ L, k * l * k⁻¹ ∈ L := fun k _ l hl => hnorm.conj_mem l hl k
  let f : ↥Λ →* Outer ↥L := endgOuterHom L Λ hn
  have hΛH : Λ ≤ bar M Q (H0 M Z) := hc.bar_LB_le_bar_Lgen.trans hc.bar_Lgen_le_bar_H0
  have hLH : L ≤ bar M Q (H0 M Z) :=
    Ctx.layer_le_bar_H0 h34 hc H.width H.n_gt H.noA2 H.gen
  have hkerL : f.ker.map Λ.subtype ≤ L := by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_layer_of_endgOuterHom_eq_one hΛH hLH hn
      (fun x hx hxcomm => Ctx.eq_one_of_centralizes_layer h44 hc H.width H.n_gt H.noA2
        H.gen hx hxcomm) hk
  have hsq : ∀ x : ↥Λ, x * x = 1 := by
    intro x
    apply Subtype.ext
    show (x : Mbar M Q) * (x : Mbar M Q) = 1
    simpa [pow_two] using (hc.swapHyp H.width H.n_gt H.noA2).sq (x : Mbar M Q) x.2
  have hrange : Nat.card ↥f.range ≤ 2 := card_range_le_two_of_outCyc hout hsq f
  have hΛ2 : IsPGroup 2 ↥Λ := by
    rw [isPGroup_iff_pow_pow_eq_one]
    exact fun x => ⟨1, by simpa [pow_two] using hsq x⟩
  have hker2 : IsPGroup 2 ↥f.ker := hΛ2.to_subgroup f.ker
  have hK2 : IsPGroup 2 ↥(f.ker.map Λ.subtype) :=
    hker2.of_equiv (Subgroup.equivMapOfInjective f.ker Λ.subtype Λ.subtype_injective)
  have hK'2 : IsPGroup 2 ↥((f.ker.map Λ.subtype).subgroupOf L) :=
    hK2.of_equiv (Subgroup.subgroupOfEquivOfLe hkerL).symm
  obtain ⟨T, hKT⟩ := IsPGroup.exists_le_sylow hK'2
  have hcardK' : Nat.card ↥((f.ker.map Λ.subtype).subgroupOf L) ≤ 8 :=
    (Subgroup.card_le_of_le hKT).trans (h8 T)
  have hcardker : Nat.card ↥f.ker ≤ 8 := by
    have h1 : Nat.card ↥((f.ker.map Λ.subtype).subgroupOf L) = Nat.card ↥f.ker := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerL).toEquiv,
        Subgroup.card_map_of_injective Λ.subtype_injective]
    omega
  have hΛle : Nat.card ↥Λ ≤ 8 * 2 := by
    calc Nat.card ↥Λ = Nat.card ↥f.ker * Nat.card ↥f.range :=
          (Subgroup.card_ker_mul_card_range f).symm
      _ ≤ 8 * 2 := Nat.mul_le_mul hcardker hrange
  have hΛge : 64 ≤ Nat.card ↥Λ := Sec10Hyp.sixty_four_le_card_bar_LB h34 H
  omega

end CFSG.RankThree.GF2n.Stroth80
