module

public import CFSG.Quasithin.Background.SmithB51P5Basic
public import CFSG.Quasithin.Background.B4L3Key
public import CFSG.Quasithin.Background.B4L3Syl
public import CFSG.Quasithin.Background.FFC1NonsplitL3
public import CFSG.Quasithin.Background.FFC5Ext
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.VolII16SLNat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace B5

namespace P5

variable {V : Type} [CommGroup V]

section CommU

variable {U : Subgroup V} {a : MulAut V}

@[expose] def commU (U : Subgroup V) (a : MulAut V) : ↥U →* V where
  toFun u := a (u : V) * (u : V)⁻¹
  map_one' := by simp
  map_mul' u w := by
    simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
    rw [mul_comm (w : V)⁻¹ (u : V)⁻¹]
    simp only [mul_assoc, mul_left_comm]

theorem commU_apply (u : ↥U) : commU U a u = a (u : V) * (u : V)⁻¹ := rfl

theorem commU_range_le (haU : ∀ u ∈ U, a u ∈ U) : (commU U a).range ≤ U := by
  rintro _ ⟨u, rfl⟩
  exact U.mul_mem (haU _ u.2) (U.inv_mem u.2)

theorem commU_range_le_fixV (hV : ∀ v : V, v ^ 2 = 1) (haU : ∀ u ∈ U, a u ∈ U) (ha2 : a ^ 2 = 1) :
    (commU U a).range ≤ U ⊓ fixV (Subgroup.zpowers a) := by
  have hinv : ∀ y : V, y⁻¹ = y := fun y => by
    have := hV y
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  rintro _ ⟨u, rfl⟩
  refine ⟨commU_range_le haU ⟨u, rfl⟩, mem_fixV_zpowers_iff.2 ?_⟩
  have haa : a (a (u : V)) = u := by
    have h1 : (a ^ 2) (u : V) = u := by rw [ha2]; rfl
    rwa [pow_two] at h1
  rw [commU_apply, map_mul, map_inv, haa, hinv (a (u : V)), hinv (u : V), mul_comm]

theorem card_range_commU_mul [Finite V] :
    Nat.card (commU U a).range * Nat.card ↥(U ⊓ fixV (Subgroup.zpowers a)) = Nat.card U := by
  have hker : Nat.card (commU U a).ker = Nat.card ↥(U ⊓ fixV (Subgroup.zpowers a)) := by
    refine Nat.card_congr
      { toFun := fun u => ⟨((u : ↥U) : V), (u : ↥U).2, mem_fixV_zpowers_iff.2 ?_⟩
        invFun := fun x => ⟨⟨(x : V), x.2.1⟩, ?_⟩
        left_inv := fun u => rfl
        right_inv := fun x => rfl }
    · have h1 : commU U a (u : ↥U) = 1 := u.2
      rw [commU_apply, mul_inv_eq_one] at h1
      exact h1
    · show commU U a _ = 1
      rw [commU_apply, mul_inv_eq_one]
      exact mem_fixV_zpowers_iff.1 x.2.2
  rw [← hker, Subgroup.card_eq_card_quotient_mul_card_subgroup (commU U a).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (commU U a)).toEquiv]

end CommU

theorem card_inf_fixV_conj {U : Subgroup V} {g : MulAut V} (hg : ∀ u ∈ U, g u ∈ U)
    (hg' : ∀ u ∈ U, g⁻¹ u ∈ U) (a : MulAut V) :
    Nat.card ↥(U ⊓ fixV (Subgroup.zpowers (g * a * g⁻¹))) =
      Nat.card ↥(U ⊓ fixV (Subgroup.zpowers a)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨g⁻¹ (x : V), hg' _ x.2.1, mem_fixV_zpowers_iff.2 ?_⟩
      invFun := fun y => ⟨g (y : V), hg _ y.2.1, mem_fixV_zpowers_iff.2 ?_⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  · have h1 := mem_fixV_zpowers_iff.1 x.2.2
    have h2 : (g * a * g⁻¹) (x : V) = g (a (g⁻¹ (x : V))) := rfl
    rw [h2] at h1
    apply g.injective
    rw [h1]
    simp
  · have h1 := mem_fixV_zpowers_iff.1 y.2.2
    show g (a (g⁻¹ (g (y : V)))) = g (y : V)
    rw [show g⁻¹ (g (y : V)) = (y : V) by simp, h1]

section L3

variable [Finite V] {L : Subgroup (MulAut V)} {U Z : Subgroup V} (D : L3Data L U Z)

omit [Finite V] in
include D in
theorem exists_not_fixed {a : MulAut V} (ha : a ∈ L) (ha1 : a ≠ 1) :
    ∃ u ∈ U, a u ≠ u := by
  obtain ⟨γ, rfl⟩ := D.exists_rho ha
  have hγ : γ ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have hw : ∃ w, L3.act γ w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hγ (L3.act_injective γ hcon)
  obtain ⟨w, hw⟩ := hw
  obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd w)
  refine ⟨u, u.2, fun h => hw ?_⟩
  have hmem : D.rho γ (u : V) ∈ U := D.inv_U _ (D.rho_mem γ) _ u.2
  have h1 := D.β_rho γ (u : V) u.2 hmem
  have h2 : (⟨D.rho γ (u : V), hmem⟩ : ↥U) = u := Subtype.ext h
  have h3 : (⟨(u : V), u.2⟩ : ↥U) = u := rfl
  rw [h2, h3, hu] at h1
  have := congrArg Multiplicative.toAdd h1
  simpa using this.symm

include D in
theorem card_inf_fixV_invol (hV : ∀ v : V, v ^ 2 = 1) (hU16 : Nat.card U = 16)
    (hcomm : commSub U L = U) {a : MulAut V} (ha : a ∈ L) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) :
    Nat.card ↥(U ⊓ fixV (Subgroup.zpowers a)) = 4 := by
  have hLU : ∀ g ∈ L, ∀ u ∈ U, g u ∈ U := D.inv_U
  have hcases : ∀ b ∈ L, b ^ 2 = 1 → b ≠ 1 →
      Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) = 4 ∨
        Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) = 8 := by
    intro b hb hb2 hb1
    have h1 := card_range_commU_mul (U := U) (a := b)
    have h2 : Nat.card (commU U b).range ≤ Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) :=
      Subgroup.card_le_of_le (commU_range_le_fixV hV (hLU b hb) hb2)
    have h3 : Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) ∣ 16 := by
      rw [← hU16]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h4 : Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) ≠ 16 := by
      intro h16
      have heq : U ⊓ fixV (Subgroup.zpowers b) = U :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h16, hU16])
      obtain ⟨u, hu, hbu⟩ := exists_not_fixed D hb hb1
      have : u ∈ U ⊓ fixV (Subgroup.zpowers b) := by rw [heq]; exact hu
      exact hbu (mem_fixV_zpowers_iff.1 this.2)
    rw [hU16] at h1
    have h5 : 16 ≤ Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) *
        Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) := by
      calc 16 = _ := h1.symm
        _ ≤ _ := Nat.mul_le_mul_right _ h2
    have h6 : Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) ∈ Nat.divisors 16 :=
      Nat.mem_divisors.2 ⟨h3, by norm_num⟩
    have h7 : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
    rw [h7] at h6
    simp only [Finset.mem_insert, Finset.mem_singleton] at h6
    rcases h6 with h | h | h | h | h
    · rw [h] at h5; omega
    · rw [h] at h5; omega
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h h4
  rcases hcases a ha ha2 ha1 with h | h8
  · exact h
  exfalso
  have hall : ∀ γ : L3.Γ, L3.IsInvol γ → Nat.card (commU U (D.rho γ)).range = 2 := by
    intro γ hγ
    have hmem : D.rho γ ∈ L := D.rho_mem γ
    have hsq : D.rho γ ^ 2 = 1 := by rw [pow_two, ← map_mul, hγ.1, map_one]
    have hne : D.rho γ ≠ 1 := fun h1 => hγ.2 (D.rho_injective (by rw [h1, map_one]))
    obtain ⟨g, hg, hga⟩ := D.exists_conj ha ha2 ha1 hmem hsq hne
    have hfix : Nat.card ↥(U ⊓ fixV (Subgroup.zpowers (D.rho γ))) = 8 := by
      rw [← hga, card_inf_fixV_conj (hLU g hg) (hLU g⁻¹ (L.inv_mem hg)), h8]
    have h1 := card_range_commU_mul (U := U) (a := D.rho γ)
    rw [hfix, hU16] at h1
    omega
  set W := (commU U (D.rho L3.x12)).range ⊔ (commU U (D.rho L3.x23)).range ⊔
    (commU U (D.rho L3.x31)).range with hW
  have hsup2 : ∀ X Y : Subgroup V, Nat.card ↥(X ⊔ Y) ≤ Nat.card X * Nat.card Y := fun X Y => by
    have := card_sup_mul_card_inf X Y
    have hpos : 0 < Nat.card ↥(X ⊓ Y) := Nat.card_pos
    calc Nat.card ↥(X ⊔ Y) ≤ Nat.card ↥(X ⊔ Y) * Nat.card ↥(X ⊓ Y) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = _ := this
  have hW8 : Nat.card W ≤ 8 := by
    have h1 := hsup2 ((commU U (D.rho L3.x12)).range ⊔ (commU U (D.rho L3.x23)).range)
      (commU U (D.rho L3.x31)).range
    have h2 := hsup2 (commU U (D.rho L3.x12)).range (commU U (D.rho L3.x23)).range
    rw [hall _ L3.x12_invol, hall _ L3.x23_invol] at h2
    rw [hall _ L3.x31_invol] at h1
    calc Nat.card W ≤ _ := h1
      _ ≤ 4 * 2 := Nat.mul_le_mul_right _ h2
      _ = 8 := by norm_num
  have hWU : W ≤ U := sup_le (sup_le (commU_range_le (hLU _ (D.rho_mem _)))
    (commU_range_le (hLU _ (D.rho_mem _)))) (commU_range_le (hLU _ (D.rho_mem _)))
  have hstab : ∀ g ∈ L, g ∈ stabSub U := fun g hg => by
    intro u
    refine ⟨fun hu => ?_, hLU g hg u⟩
    have := hLU g⁻¹ (L.inv_mem hg) _ hu
    simpa using this
  have hgen : ∀ γ ∈ ({L3.x12, L3.x23, L3.x31} : Set L3.Γ), D.rho γ ∈ centSec U W := by
    intro γ hγ
    refine ⟨hstab _ (D.rho_mem γ), fun u hu => ?_⟩
    have hmem : D.rho γ u * u⁻¹ ∈ (commU U (D.rho γ)).range := ⟨⟨u, hu⟩, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hmem)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hmem)
    · exact Subgroup.mem_sup_right hmem
  have hLW : L ≤ centSec U W := D.le_of_gens (hgen _ (by simp)) (hgen _ (by simp))
    (hgen _ (by simp))
  have hcommW : commSub U L ≤ W := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    exact (hLW hx).2 w hw
  rw [hcomm] at hcommW
  have := Subgroup.card_le_of_le hcommW
  omega

include D in
theorem inf_fixV_eq_pre (hV : ∀ v : V, v ^ 2 = 1) (hU16 : Nat.card U = 16) (hZ2 : Nat.card Z = 2)
    (hcomm : commSub U L = U) {γ : L3.Γ} (hγ : L3.IsInvol γ) {c : L3.Vec} (hc : c ≠ 0)
    (hcim : L3.cim γ = {0, c}) :
    U ⊓ fixV (Subgroup.zpowers (D.rho γ)) = D.pre (Zc c) := by
  have hLU : ∀ g ∈ L, ∀ u ∈ U, g u ∈ U := D.inv_U
  have hmem : D.rho γ ∈ L := D.rho_mem γ
  have hsq : D.rho γ ^ 2 = 1 := by rw [pow_two, ← map_mul, hγ.1, map_one]
  have hne : D.rho γ ≠ 1 := fun h1 => hγ.2 (D.rho_injective (by rw [h1, map_one]))
  have hfix := card_inf_fixV_invol D hV hU16 hcomm hmem hsq hne
  have h1 := card_range_commU_mul (U := U) (a := D.rho γ)
  rw [hfix, hU16] at h1
  have hr4 : Nat.card (commU U (D.rho γ)).range = 4 := by omega
  have hpre4 : Nat.card (D.pre (Zc c)) = 4 := by rw [D.card_pre, card_Zc hc, hZ2]
  have hrpre : (commU U (D.rho γ)).range ≤ D.pre (Zc c) := by
    rintro _ ⟨u, rfl⟩
    have hmu : D.rho γ (u : V) ∈ U := hLU _ hmem _ u.2
    have hx : D.rho γ (u : V) * (u : V)⁻¹ ∈ U := U.mul_mem hmu (U.inv_mem u.2)
    rw [commU_apply, D.mem_pre]
    refine ⟨hx, ?_⟩
    rw [D.β_comm γ u hmu hx]
    show L3.act γ (Multiplicative.toAdd (D.β u)) - Multiplicative.toAdd (D.β u) ∈
      ({0, c} : Finset L3.Vec)
    rw [← hcim]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hr1 : (commU U (D.rho γ)).range = D.pre (Zc c) :=
    Subgroup.eq_of_le_of_card_ge hrpre (by rw [hr4, hpre4])
  have hr2 : (commU U (D.rho γ)).range = U ⊓ fixV (Subgroup.zpowers (D.rho γ)) :=
    Subgroup.eq_of_le_of_card_ge (commU_range_le_fixV hV (hLU _ hmem) hsq) (by rw [hr4, hfix])
  rw [← hr2, hr1]

end L3

section Main

variable [Finite V] {G L : Subgroup (MulAut V)}

theorem exists_isSylowTwoOf_ge {X P : Subgroup (MulAut V)} (hPX : P ≤ X) (hP2 : IsPGroup 2 ↥P) :
    ∃ T : Subgroup (MulAut V), IsSylowTwoOf T X ∧ P ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(P.subgroupOf X) :=
    hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  refine ⟨(Q : Subgroup ↥X).map X.subtype, ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩, ?_⟩
  · have : ((Q : Subgroup ↥X).map X.subtype).subgroupOf X = (Q : Subgroup ↥X) :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [this]
    exact Q.not_dvd_index
  · intro a ha
    have : (⟨a, hPX ha⟩ : ↥X) ∈ P.subgroupOf X := ha
    exact ⟨⟨a, hPX ha⟩, hQ this, rfl⟩

theorem fixV_inf_commV_eq_bot_of_l3 (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤)
    (hnat : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 1)
    (hnd : commV L ⊔ fixV G ≠ ⊤) : fixV L ⊓ commV L = ⊥ := by
  obtain ⟨T0, hT0⟩ := exists_isSylowTwoOf G
  have hT0L : T0 ≤ L := FFC.sylow_le_of_binaryNaturalSL_three hV h hU hT0 hnat
  have hGL : G = L := eq_of_offenders_le h hT0 (fun A _ hAT => hAT.trans hT0L)
  obtain ⟨D⟩ := hnat.toL3Coord
  by_contra hZ
  have hZ2 : Nat.card ↥(fixV L ⊓ commV L) = 2 := by
    have h1 := H13.VolI.binaryNaturalSL_three_card_le hV hU hnat
    have h2 : 1 < Nat.card ↥(fixV L ⊓ commV L) := by
      by_contra hle
      push Not at hle
      exact hZ (Subgroup.eq_bot_of_card_le _ hle)
    omega
  have hU16 : Nat.card ↥(commV L) = 16 := by rw [D.card_U, hZ2]
  obtain ⟨-, hcomm, -, -⟩ := irr_data hU
  have hLU : ∀ g ∈ L, ∀ u ∈ commV L, g u ∈ commV L := D.inv_U
  obtain ⟨A, hA⟩ := exists_offender h
  have hAL : A ≤ L := hGL ▸ hA.1
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hA4 : Nat.card A ≤ 4 := D.elemAbelian_card_le_four hAL hAel
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.2.1
  have ha1' : a ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
  have ha2 : a ^ 2 = 1 := hAel.2 a haA
  have hCa := card_inf_fixV_invol D hV hU16 hcomm (hAL haA) ha2 ha1'
  have hCA : Nat.card ↥(commV L ⊓ fixV A) ≤ 4 := by
    rw [← hCa]
    exact Subgroup.card_le_of_le (inf_le_inf_left _ (B1.fixV_le_fixV (Subgroup.zpowers_le.2 haA)))
  obtain ⟨hsupA, hcardA⟩ := sup_fixV_eq_top_of_card_le hA (U := commV L) (by
    rw [hU16]
    calc Nat.card A * Nat.card ↥(commV L ⊓ fixV A) ≤ 4 * 4 := Nat.mul_le_mul hA4 hCA
      _ = 16 := by norm_num)
  rw [hU16] at hcardA
  have hA4' : Nat.card A = 4 := by
    refine le_antisymm hA4 ?_
    by_contra hlt
    push Not at hlt
    have : Nat.card A * Nat.card ↥(commV L ⊓ fixV A) ≤ 3 * 4 := Nat.mul_le_mul (by omega) hCA
    omega
  have hCA4 : Nat.card ↥(commV L ⊓ fixV A) = 4 := by
    rw [hA4'] at hcardA
    omega
  obtain ⟨T, hT, hAT⟩ := exists_isSylowTwoOf_ge hAL hAel.isPGroup
  have hT8 : Nat.card T = 8 := D.card_sylow hT
  have hidx : (A.subgroupOf T).index = 2 := by
    have := Subgroup.index_mul_card (A.subgroupOf T)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv, hA4', hT8] at this
    omega
  obtain ⟨t, htT, htA⟩ : ∃ t ∈ T, t ∉ A := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show T ≤ A from hcon)
    omega
  have hnorm := Subgroup.normal_of_index_eq_two hidx
  have htA' : ∀ x ∈ A, t⁻¹ * x * t ∈ A := by
    intro x hx
    have h1 := hnorm.conj_mem ⟨x, hAT hx⟩ hx (⟨t, htT⟩ : ↥T)⁻¹
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have ht2 : t ^ 2 ∈ A := by
    have h1 := Subgroup.sq_mem_of_index_two hidx (⟨t, htT⟩ : ↥T)
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hTeq : A ⊔ Subgroup.zpowers t = T := by
    have hle : A ⊔ Subgroup.zpowers t ≤ T := sup_le hAT (Subgroup.zpowers_le.2 htT)
    have hd1 : Nat.card A ∣ Nat.card ↥(A ⊔ Subgroup.zpowers t) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hd2 : Nat.card ↥(A ⊔ Subgroup.zpowers t) ∣ Nat.card T := Subgroup.card_dvd_of_le hle
    have hne : Nat.card ↥(A ⊔ Subgroup.zpowers t) ≠ 4 := by
      intro h4
      have heq : A = A ⊔ Subgroup.zpowers t :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h4, hA4'])
      apply htA
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    rw [hA4'] at hd1
    rw [hT8] at hd2
    have h8 : Nat.card ↥(A ⊔ Subgroup.zpowers t) = 8 := by
      obtain ⟨k, hk⟩ := hd1
      have hle8 := Nat.le_of_dvd (by norm_num) hd2
      rw [hk] at hle8 hne hd2 ⊢
      have hk2 : k ≤ 2 := by omega
      interval_cases k <;> simp_all
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h8, hT8])
  have hCT : Nat.card ↥(commV L ⊓ fixV T) = 2 := by
    obtain ⟨γ, δ, hγ, hδ, hγT, hδT, hne⟩ := D.exists_two_centers_in_sylow hT
    obtain ⟨c, hc0, hcγ⟩ := L3.invol_center γ hγ
    obtain ⟨c', hc0', hcδ⟩ := L3.invol_center δ hδ
    have hcc : c ≠ c' := fun h1 => hne (by rw [hcγ, hcδ, h1])
    have h1 := inf_fixV_eq_pre D hV hU16 hZ2 hcomm hγ hc0 hcγ
    have h2 := inf_fixV_eq_pre D hV hU16 hZ2 hcomm hδ hc0' hcδ
    have hle : commV L ⊓ fixV T ≤ fixV L ⊓ commV L := by
      intro x hx
      have hx1 : x ∈ commV L ⊓ fixV (Subgroup.zpowers (D.rho γ)) :=
        ⟨hx.1, B1.fixV_le_fixV (Subgroup.zpowers_le.2 hγT) hx.2⟩
      have hx2 : x ∈ commV L ⊓ fixV (Subgroup.zpowers (D.rho δ)) :=
        ⟨hx.1, B1.fixV_le_fixV (Subgroup.zpowers_le.2 hδT) hx.2⟩
      rw [h1, D.mem_pre] at hx1
      rw [h2, D.mem_pre] at hx2
      obtain ⟨hxU, hb1⟩ := hx1
      obtain ⟨hxU', hb2⟩ := hx2
      have hb1' : Multiplicative.toAdd (D.β ⟨x, hxU⟩) ∈ ({0, c} : Finset L3.Vec) := hb1
      have hb2' : Multiplicative.toAdd (D.β ⟨x, hxU⟩) ∈ ({0, c'} : Finset L3.Vec) := hb2
      have hb : D.β ⟨x, hxU⟩ = 1 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb1' hb2'
        rcases hb1' with hb1' | hb1'
        · exact Multiplicative.toAdd.injective hb1'
        · rcases hb2' with hb2' | hb2'
          · exact Multiplicative.toAdd.injective hb2'
          · exact absurd (hb1'.symm.trans hb2') hcc
      exact (D.ker_β ⟨x, hxU⟩).1 hb
    have hZle : fixV L ⊓ commV L ≤ commV L ⊓ fixV T :=
      fun z hz => ⟨hz.2, fun g hg => hz.1 g (hT.1 hg)⟩
    have h3 := Subgroup.card_le_of_le hle
    have h4 := Subgroup.card_le_of_le hZle
    omega
  have htL : t ∈ L := hT.1 htT
  have hlift := lift_of_card hV htA' ht2 (hLU t htL) (by rw [hTeq, hCA4, hCT]; norm_num)
  have hle := fixV_le_sup_fixV_of_lift (U := commV L) hV htA' ht2
    (fun v => Subgroup.subset_closure ⟨t, htL, v, rfl⟩) hlift
  rw [hTeq] at hle
  have hsupT : commV L ⊔ fixV T = ⊤ := by
    rw [eq_top_iff, ← hsupA]
    exact sup_le le_sup_left hle
  have hodd : Odd (T.subgroupOf L).index := by
    have := Subgroup.index_mul_card (T.subgroupOf L)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv, hT8, D.card_G] at this
    have h21 : (T.subgroupOf L).index = 21 := by omega
    rw [h21]
    decide
  have hsupL := FFC.sup_fixV_eq_top_of_odd hLU
    (fun g hg v => Subgroup.subset_closure ⟨g, hg, v, rfl⟩) hV hodd hsupT
  apply hnd
  rw [hGL]
  exact hsupL

end Main

end P5

end B5

end CFSG.Quasithin
