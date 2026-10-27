module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixNaturalField
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusSmallCommCore

public section

noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
open Matrix

variable {G : Type} [Group G] [Finite G]
  {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_exists_elemAbelian_five_fix_v0_of_omegaMinus_six_four_natural
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 2)
    {w : G} (hw : w ∈ V₀) :
    ∃ E : Subgroup G, E ≤ D.M ⊓ centralizer ({w} : Set G) ∧
      IsElemAbelian 5 E ∧ Nat.card E = 25 := by
  classical
  have hrank : CFSG.Open.pRank 5 D.M = 3 :=
    (s168e3_sig_eq_five_of_omegaMinus_six_four_natural c hs hN).2
  obtain ⟨E₀, hE₀el, hE₀card⟩ :=
    exists_isElemAbelian_subgroupOf_of_le_pRank (M := D.M) (k := 2)
      Nat.prime_five (by rw [hrank]; norm_num)
  let E : Subgroup G := E₀.map D.M.subtype
  have hEM : E ≤ D.M := Subgroup.map_subtype_le E₀
  have hEel : IsElemAbelian 5 E := hE₀el.map D.M.subtype
  have hEcard : Nat.card E = 25 := by
    rw [Subgroup.card_map_of_injective D.M.subtype_injective, hE₀card]
    norm_num
  have hE5 : IsPGroup 5 E := hEel.isPGroup
  have hEnorm : E ≤ normalizer (V₀ : Set G) :=
    hEM.trans c.setting.hyp16.hyp125.pairFacts.le_normalizer₀
  have hcentV0 : E ≤ centralizer (V₀ : Set G) :=
    le_centralizer_of_mSub_le_two Nat.prime_five (by norm_num)
      c.setting.hyp16.hyp125.pairFacts.elemAbelian₀ c.setting.hyp16.small hE5 hEnorm
  have hcentw : E ≤ centralizer ({w} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have h1 := (Subgroup.mem_centralizer_iff.mp (hcentV0 he)) w hw
    exact h1
  exact ⟨E, le_inf hEM hcentw, hEel, hEcard⟩

theorem uniqueMax_of_isElemAbelian_five_card_eq_25
    (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) {w : G} {E : Subgroup G}
    (hE : E ≤ D.M ⊓ centralizer ({w} : Set G))
    (hEel : IsElemAbelian 5 E) (hEcard : Nat.card E = 25) (h5 : 5 ∈ D.sig) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : CFSG.IsElementaryAbelian 5 ↥E :=
    CFSG.Open.IsElemAbelian.isElementaryAbelian hEel
  have hnc : ¬ IsCyclic ↥E :=
    CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 5) (by
      rw [hEcard]; norm_num)
  have hEuniq : UniqueMax D.M E :=
    uc22p22u_uniqueMax_of_noncyclic D h61 h63 Nat.prime_five (by norm_num)
      (fun x hx => (hE hx).1) hEel.isPGroup hnc (Or.inr h5)
  exact ElevenFourteen.uniqueMax_of_le D.maxLocal hEuniq hE inf_le_left

theorem s168e3_uniqueMax_v0_of_omegaMinus_six_four_natural
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 2)
    {w : G} (hw : w ∈ V₀) (_hw1 : w ≠ 1) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨E, hE, hEel, hEcard⟩ :=
    s168e3_exists_elemAbelian_five_fix_v0_of_omegaMinus_six_four_natural c hs hN hw
  have hsig : D.sig = {5} := (s168e3_sig_eq_five_of_omegaMinus_six_four_natural c hs hN).1
  have h5 : 5 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 5
  exact uniqueMax_of_isElemAbelian_five_card_eq_25 D c.std.h61 c.std.h63 hE hEel hEcard h5

theorem s168e3_exists_noncyclic_five_fix_nonsingular_of_omegaMinus_six_four_natural
    (c : S168e3Ctx D V₀ V L hV)
    {F : Type} [Field F] [Finite F] {b d : F}
    (hF : Nat.card F = 4) (hirr : ∀ s : F, s ^ 2 + b * s + d ≠ 0)
    (ε : ↥(lBar V₀ V hV L) ≃* ↥(StatedOmega (StatedQuadMinus 3 F b d)))
    (ψ : ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hcoords : NatCoordsOmegaMinusOn (lBar V₀ V hV L) ⊤
      (fun _ _ s _ => Subgroup.mem_top s) F b d ε ψ)
    {w : G} (hw : w ∈ V)
    (hns : StatedQuadMinus 3 F b d
      (Multiplicative.toAdd (ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩),
        Subgroup.mem_top _⟩)) ≠ 0) :
    ∃ P : Subgroup G, P ≤ D.M ⊓ centralizer ({w} : Set G) ∧
      IsPGroup 5 P ∧ ¬ IsCyclic ↥P := by
  classical
  let : CharP F 2 := s16k_charP_two_of_card (a := 2) (by norm_num) (by
    rw [hF]; norm_num)
  have hcong : (2 : ℤ) ^ 2 ≡ -1 [ZMOD (5 : ℤ)] := by decide
  obtain ⟨EΩ, hEΩle, hEΩel, hEΩcard, hEΩfix⟩ :=
    exists_elemAbelian_fix_of_quadMinus_ne_zero (K := F) hirr
      (n := 2) (p := 5) (by norm_num) (by rw [hF]; norm_num)
      Nat.prime_five hcong hns
  let EΩ' : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b d)) :=
    EΩ.subgroupOf (StatedOmega (StatedQuadMinus 3 F b d))
  have hEΩ'el : IsElemAbelian 5 EΩ' := hEΩel.subgroupOf _
  have hEΩ'card : Nat.card EΩ' = 25 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΩle).toEquiv, hEΩcard]
    norm_num
  let Ebar : Subgroup (MulAut (Vtil V₀ V hV)) :=
    EΩ'.map ((lBar V₀ V hV L).subtype.comp ε.symm.toMonoidHom)
  have hEbarel : IsElemAbelian 5 Ebar := hEΩ'el.map _
  have hEbarinj : Function.Injective
      ((lBar V₀ V hV L).subtype.comp ε.symm.toMonoidHom) := by
    intro a b hab
    exact ε.symm.injective ((lBar V₀ V hV L).subtype_injective hab)
  have hEbarcard : Nat.card Ebar = 25 := by
    rw [Subgroup.card_map_of_injective hEbarinj, hEΩ'card]
  have hEbarp : IsPGroup 5 ↥Ebar := hEbarel.isPGroup
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : CFSG.IsElementaryAbelian 5 ↥Ebar :=
    CFSG.Open.IsElemAbelian.isElementaryAbelian hEbarel
  have hEbarnc : ¬ IsCyclic ↥Ebar :=
    CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 5) (by
      rw [hEbarcard]; norm_num)
  have hEbarM : Ebar ≤ Mbar D.M V₀ V hV := by
    rintro x ⟨y, -, rfl⟩
    exact barSub_mono V₀ V hV c.setting.hyp151.le (ε.symm y).2
  have hEbarfix : ∀ x ∈ Ebar,
      x (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)) =
        mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) := by
    rintro x ⟨y, hy, rfl⟩
    have hyΩ : (y : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) ∈ EΩ :=
      Subgroup.mem_subgroupOf.mp hy
    let l : ↥(lBar V₀ V hV L) := ε.symm y
    have hxl : (l : MulAut (Vtil V₀ V hV)) = (ε.symm y : ↥(lBar V₀ V hV L)).val := rfl
    have hx' := hcoords l ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩),
      Subgroup.mem_top _⟩
    have hεl : ε l = y := by
      change ε (ε.symm y) = y
      exact MulEquiv.apply_symm_apply ε y
    rw [hεl, hEΩfix y hyΩ] at hx'
    have h1 : ψ ⟨(l : MulAut (Vtil V₀ V hV))
        (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)), Subgroup.mem_top _⟩ =
        ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩ := by
      simpa only [ofAdd_toAdd] using hx'
    have h2 := congrArg Subtype.val (ψ.injective h1)
    simpa [hxl] using h2
  have hV0lt : Nat.card V₀ < 5 := by
    have h4 := Sixteen21.card_le_four_of_hyp16 c.setting.hyp16
    omega
  exact C163.exists_noncyclic_le_centralizer hV Nat.prime_five hV0lt hw hEbarM
    hEbarp hEbarnc hEbarfix

theorem s168e3_exists_elemAbelian_five_fix_nonsingular_of_omegaMinus_six_four_natural
    (c : S168e3Ctx D V₀ V L hV)
    {F : Type} [Field F] [Finite F] {b d : F}
    (hF : Nat.card F = 4) (hirr : ∀ s : F, s ^ 2 + b * s + d ≠ 0)
    (ε : ↥(lBar V₀ V hV L) ≃* ↥(StatedOmega (StatedQuadMinus 3 F b d)))
    (ψ : ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hcoords : NatCoordsOmegaMinusOn (lBar V₀ V hV L) ⊤
      (fun _ _ s _ => Subgroup.mem_top s) F b d ε ψ)
    {w : G} (hw : w ∈ V)
    (hns : StatedQuadMinus 3 F b d
      (Multiplicative.toAdd (ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩),
        Subgroup.mem_top _⟩)) ≠ 0) :
    ∃ E : Subgroup G, E ≤ D.M ⊓ centralizer ({w} : Set G) ∧
      IsElemAbelian 5 E ∧ Nat.card E = 25 := by
  obtain ⟨P, hP, hPp, hPnc⟩ :=
    s168e3_exists_noncyclic_five_fix_nonsingular_of_omegaMinus_six_four_natural
      c hF hirr ε ψ hcoords hw hns
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨E, hEP, hEel, hEcard⟩ :=
    GL83.I243.Inner.exists_isElemAbelian_card_sq_of_not_isCyclic (p := 5) (by norm_num) hPp hPnc
  exact ⟨E, hEP.trans hP, hEel, by rw [hEcard]; norm_num⟩

theorem s168e3_uniqueMax_nonsingular_of_omegaMinus_six_four_natural
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 2)
    {F : Type} [Field F] [Finite F] {b d : F}
    (hF : Nat.card F = 4) (hirr : ∀ s : F, s ^ 2 + b * s + d ≠ 0)
    (ε : ↥(lBar V₀ V hV L) ≃* ↥(StatedOmega (StatedQuadMinus 3 F b d)))
    (ψ : ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hcoords : NatCoordsOmegaMinusOn (lBar V₀ V hV L) ⊤
      (fun _ _ s _ => Subgroup.mem_top s) F b d ε ψ)
    {w : G} (hw : w ∈ V)
    (hns : StatedQuadMinus 3 F b d
      (Multiplicative.toAdd (ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩),
        Subgroup.mem_top _⟩)) ≠ 0) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨E, hE, hEel, hEcard⟩ :=
    s168e3_exists_elemAbelian_five_fix_nonsingular_of_omegaMinus_six_four_natural
      c hF hirr ε ψ hcoords hw hns
  have hsig : D.sig = {5} := (s168e3_sig_eq_five_of_omegaMinus_six_four_natural c hs hN).1
  have h5 : 5 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 5
  exact uniqueMax_of_isElemAbelian_five_card_eq_25 D c.std.h61 c.std.h63 hE hEel hEcard h5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
