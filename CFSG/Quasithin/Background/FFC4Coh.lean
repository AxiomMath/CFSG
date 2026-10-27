module

public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.FFC4Small1
public import CFSG.Quasithin.Background.JonesParshallSLn
public import CFSG.Quasithin.Background.FFC4Case2

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin.JonesParshall

section Coh

variable {W : Type} [CommGroup W]

abbrev SL3F2 : Type := SpecialLinearGroup (Fin 3) (ZMod 2)

structure CohData (H : Subgroup (MulAut W)) (U : Subgroup W) where
  ρ : SL3F2 →* ↥H
  surj : Function.Surjective ρ
  θ : ↥U →* Multiplicative (Fin 3 → ZMod 2)
  bij : Function.Bijective θ
  inv : ∀ (g : SL3F2) (u : W), u ∈ U → ((ρ g : ↥H) : MulAut W) u ∈ U
  mem : ∀ (g : SL3F2) (w : W), ((ρ g : ↥H) : MulAut W) w * w⁻¹ ∈ U
  equiv : ∀ (g : SL3F2) (u : ↥U),
    θ ⟨((ρ g : ↥H) : MulAut W) (u : W), inv g u u.2⟩ =
      Multiplicative.ofAdd (g • Multiplicative.toAdd (θ u))

variable {H : Subgroup (MulAut W)} {U : Subgroup W} (D : CohData H U)

@[expose] def CohData.cocy (w : W) : SL3F2 → (Fin 3 → ZMod 2) := fun g =>
  Multiplicative.toAdd (D.θ ⟨((D.ρ g : ↥H) : MulAut W) w * w⁻¹, D.mem g w⟩)

theorem CohData.cocy_one : D.cocy 1 = 0 := by
  funext g
  have h1 : (⟨((D.ρ g : ↥H) : MulAut W) 1 * (1 : W)⁻¹, D.mem g 1⟩ : ↥U) = 1 := by
    apply Subtype.ext
    simp
  show Multiplicative.toAdd (D.θ ⟨_, D.mem g 1⟩) = 0
  rw [h1, map_one]
  rfl

theorem CohData.cocy_mul (w w' : W) : D.cocy (w * w') = D.cocy w + D.cocy w' := by
  funext g
  have : (⟨((D.ρ g : ↥H) : MulAut W) (w * w') * (w * w')⁻¹, D.mem g (w * w')⟩ : ↥U) =
      ⟨((D.ρ g : ↥H) : MulAut W) w * w⁻¹, D.mem g w⟩ *
        ⟨((D.ρ g : ↥H) : MulAut W) w' * w'⁻¹, D.mem g w'⟩ := by
    apply Subtype.ext
    show ((D.ρ g : ↥H) : MulAut W) (w * w') * (w * w')⁻¹ =
      (((D.ρ g : ↥H) : MulAut W) w * w⁻¹) * (((D.ρ g : ↥H) : MulAut W) w' * w'⁻¹)
    rw [map_mul, mul_inv, mul_mul_mul_comm]
  show Multiplicative.toAdd (D.θ ⟨_, D.mem g (w * w')⟩) =
    Multiplicative.toAdd (D.θ ⟨_, D.mem g w⟩) + Multiplicative.toAdd (D.θ ⟨_, D.mem g w'⟩)
  rw [this, map_mul, toAdd_mul]

theorem CohData.cocy_cocycle (w : W) : D.cocy w ∈ Z1A (muF2 3) := by
  intro g h
  have hu : ((D.ρ h : ↥H) : MulAut W) w * w⁻¹ ∈ U := D.mem h w
  have h1 : (⟨((D.ρ (g * h) : ↥H) : MulAut W) w * w⁻¹, D.mem (g * h) w⟩ : ↥U) =
      ⟨((D.ρ g : ↥H) : MulAut W) (((D.ρ h : ↥H) : MulAut W) w * w⁻¹), D.inv g _ hu⟩ *
        ⟨((D.ρ g : ↥H) : MulAut W) w * w⁻¹, D.mem g w⟩ := by
    apply Subtype.ext
    show ((D.ρ (g * h) : ↥H) : MulAut W) w * w⁻¹ =
      (((D.ρ g : ↥H) : MulAut W) (((D.ρ h : ↥H) : MulAut W) w * w⁻¹)) *
        (((D.ρ g : ↥H) : MulAut W) w * w⁻¹)
    rw [map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, MulAut.mul_apply]
    rw [mul_assoc, inv_mul_cancel_left]
  have h2 := D.equiv g ⟨((D.ρ h : ↥H) : MulAut W) w * w⁻¹, hu⟩
  show Multiplicative.toAdd (D.θ ⟨((D.ρ (g * h) : ↥H) : MulAut W) w * w⁻¹, D.mem (g * h) w⟩) =
    Multiplicative.toAdd (D.θ ⟨((D.ρ g : ↥H) : MulAut W) w * w⁻¹, D.mem g w⟩) +
      (muF2 3 g) (Multiplicative.toAdd (D.θ ⟨((D.ρ h : ↥H) : MulAut W) w * w⁻¹, D.mem h w⟩))
  rw [h1, map_mul, toAdd_mul, h2, toAdd_ofAdd]
  exact add_comm _ _

theorem CohData.cocy_eq_zero_iff (w : W) : D.cocy w = 0 ↔ w ∈ fixV H := by
  constructor
  · intro h x hx
    obtain ⟨g, hg⟩ := D.surj ⟨x, hx⟩
    have hgx : ((D.ρ g : ↥H) : MulAut W) = x := congrArg Subtype.val hg
    have h1 := congrFun h g
    have h2 : D.θ ⟨((D.ρ g : ↥H) : MulAut W) w * w⁻¹, D.mem g w⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      exact h1
    have h3 : (⟨((D.ρ g : ↥H) : MulAut W) w * w⁻¹, D.mem g w⟩ : ↥U) = 1 :=
      D.bij.1 (h2.trans (map_one D.θ).symm)
    have h4 : ((D.ρ g : ↥H) : MulAut W) w * w⁻¹ = 1 := congrArg Subtype.val h3
    rw [← hgx]
    exact mul_inv_eq_one.1 h4
  · intro hw
    funext g
    have h1 : (⟨((D.ρ g : ↥H) : MulAut W) w * w⁻¹, D.mem g w⟩ : ↥U) = 1 := by
      apply Subtype.ext
      show ((D.ρ g : ↥H) : MulAut W) w * w⁻¹ = 1
      rw [hw _ (D.ρ g).2, mul_inv_cancel]
    show Multiplicative.toAdd (D.θ _) = 0
    rw [h1, map_one]
    rfl

theorem CohData.cocy_of_mem (u : ↥U) (g : SL3F2) :
    D.cocy (u : W) g = coboundaryA (muF2 3) (Multiplicative.toAdd (D.θ u)) g := by
  have h1 : (⟨((D.ρ g : ↥H) : MulAut W) (u : W) * (u : W)⁻¹, D.mem g u⟩ : ↥U) =
      ⟨((D.ρ g : ↥H) : MulAut W) (u : W), D.inv g u u.2⟩ * u⁻¹ := rfl
  show Multiplicative.toAdd (D.θ ⟨_, D.mem g u⟩) =
    (muF2 3 g) (Multiplicative.toAdd (D.θ u)) - Multiplicative.toAdd (D.θ u)
  rw [h1, map_mul, map_inv, toAdd_mul, toAdd_inv, D.equiv, toAdd_ofAdd]
  exact (sub_eq_add_neg _ _).symm

@[expose] def CohData.psi : Additive W →+ (SL3F2 → Fin 3 → ZMod 2) where
  toFun w := D.cocy (Additive.toMul w)
  map_zero' := D.cocy_one
  map_add' _ _ := D.cocy_mul _ _

theorem CohData.card_ker_psi : Nat.card D.psi.ker = Nat.card ↥(fixV H) :=
  Nat.card_congr
    { toFun := fun x => ⟨Additive.toMul x.1, (D.cocy_eq_zero_iff _).1 (AddMonoidHom.mem_ker.1 x.2)⟩
      invFun := fun y => ⟨Additive.ofMul y.1, AddMonoidHom.mem_ker.2 ((D.cocy_eq_zero_iff _).2 y.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Coh

section Three

theorem coboundaryA_injective_three : Function.Injective (coboundaryA (muF2 3)) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  have hfix : ∀ γ : ↥(StatedSL 3 (ZMod 2)),
      natAct (StatedSL 3 (ZMod 2)) γ (Multiplicative.ofAdd m) = Multiplicative.ofAdd m := by
    intro γ
    obtain ⟨g, rfl⟩ := (specialLinearGroupEquivStatedSL 3 (ZMod 2)).surjective γ
    have h1 := congrFun hm g
    have h2 : (muF2 3 g) m - m = 0 := h1
    have h3 : (muF2 3 g) m = m := sub_eq_zero.1 h2
    show Multiplicative.ofAdd (((g : Matrix (Fin 3) (Fin 3) (ZMod 2))).mulVec m) = Multiplicative.ofAdd m
    exact congrArg Multiplicative.ofAdd h3
  have := eq_one_of_fixed_nat (by norm_num) _ hfix
  exact this

theorem card_B1A_three : Nat.card (B1A (muF2 3)) = 8 := by
  have hinj := coboundaryA_injective_three
  have h1 : Nat.card (B1A (muF2 3)) = Nat.card (Fin 3 → ZMod 2) :=
    (Nat.card_congr (AddMonoidHom.ofInjective hinj).toEquiv).symm
  rw [h1, Nat.card_eq_fintype_card]
  simp [ZMod.card]

end Three

section Coh2

variable {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {U : Subgroup W} (D : CohData H U)

theorem CohData.card_range_psi
    (hne : ¬ (U ⊔ fixV H = ⊤)) : Nat.card D.psi.range = 16 := by
  have hBR : B1A (muF2 3) ≤ D.psi.range := by
    rintro _ ⟨m, rfl⟩
    obtain ⟨u, hu⟩ := D.bij.2 (Multiplicative.ofAdd m)
    refine ⟨Additive.ofMul (u : W), ?_⟩
    funext g
    show D.cocy (u : W) g = coboundaryA (muF2 3) m g
    rw [D.cocy_of_mem u g, hu, toAdd_ofAdd]
  have hRZ : D.psi.range ≤ Z1A (muF2 3) := by
    rintro _ ⟨w, rfl⟩
    exact D.cocy_cocycle _
  have hne' : B1A (muF2 3) ≠ D.psi.range := by
    intro heq
    apply hne
    rw [eq_top_iff]
    intro w _
    have hmem : D.psi (Additive.ofMul w) ∈ B1A (muF2 3) := by
      rw [heq]; exact ⟨_, rfl⟩
    obtain ⟨m, hm⟩ := hmem
    obtain ⟨u, hu⟩ := D.bij.2 (Multiplicative.ofAdd m)
    have hum : D.psi (Additive.ofMul (u : W)) = coboundaryA (muF2 3) m := by
      funext g
      show D.cocy (u : W) g = coboundaryA (muF2 3) m g
      rw [D.cocy_of_mem u g, hu, toAdd_ofAdd]
    have hker : D.psi (Additive.ofMul w - Additive.ofMul (u : W)) = 0 := by
      rw [map_sub, hum, ← hm]
      exact sub_self _
    have hdiv : Additive.ofMul w - Additive.ofMul (u : W) = Additive.ofMul (w * (u : W)⁻¹) := by
      rw [← ofMul_div, div_eq_mul_inv]
    rw [hdiv] at hker
    have h0 : D.cocy (w * (u : W)⁻¹) = 0 := hker
    have h1 : w * (u : W)⁻¹ ∈ fixV H := (D.cocy_eq_zero_iff _).1 h0
    have h3 : (w * (u : W)⁻¹) * (u : W) ∈ fixV H ⊔ U := Subgroup.mul_mem_sup h1 u.2
    rw [inv_mul_cancel_right, sup_comm] at h3
    exact h3
  have hB8 := card_B1A_three
  have hd1 : 8 ∣ Nat.card D.psi.range := by
    have := AddSubgroup.card_dvd_of_le hBR
    rwa [hB8] at this
  have hd2 : Nat.card D.psi.range ∣ 16 := by
    have h2 : Nat.card D.psi.range ∣ Nat.card (Z1A (muF2 3)) := AddSubgroup.card_dvd_of_le hRZ
    have hz : Nat.card (Z1A (muF2 3)) = 2 * Nat.card (B1A (muF2 3)) := card_Z1A_three
    rw [hz, hB8] at h2
    exact h2
  have hpos : 0 < Nat.card D.psi.range := Nat.pos_of_dvd_of_pos hd2 (by norm_num)
  have hle : Nat.card D.psi.range ≤ 16 := Nat.le_of_dvd (by norm_num) hd2
  have hne8 : Nat.card D.psi.range ≠ 8 := by
    intro h8
    have h9 : Nat.card D.psi.range ≤ Nat.card (B1A (muF2 3)) := by
      rw [h8, hB8]
    exact hne' (AddSubgroup.eq_of_le_of_card_ge hBR h9)
  obtain ⟨k, hk⟩ := hd1
  omega

include D in
theorem CohData.card_eq [Finite W] (hne : ¬ (U ⊔ fixV H = ⊤)) :
    Nat.card W = 2 ^ 4 * Nat.card ↥(fixV H) := by
  have h := AddSubgroup.card_ker_mul_card_range D.psi
  rw [D.card_ker_psi, D.card_range_psi hne, Nat.card_congr (Additive.toMul : Additive W ≃ W)] at h
  rw [← h]
  ring

theorem exists_cohData {H : Subgroup (MulAut W)} {U : Subgroup W} (hcomm : commV H ≤ U)
    (h : BinaryNaturalSL H U ⊥ 3 1) : Nonempty (CohData H U) := by
  obtain ⟨π, hπ⟩ := BinaryNaturalSL.exists_zmod h
  obtain ⟨f, hfs, hfk, hfe⟩ := exists_natMap hπ
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hfk u).1 hu
    exact Subtype.ext (Subgroup.mem_bot.1 this)
  refine ⟨{ ρ := π.comp (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toMonoidHom
            surj := hπ.1.comp (specialLinearGroupEquivStatedSL 3 (ZMod 2)).surjective
            θ := f
            bij := ⟨hinj, hfs⟩
            inv := fun g u hu => hπ.2.2.2.1 _ u hu
            mem := fun g w => hcomm (Subgroup.subset_closure ⟨_, (π _).2, w, rfl⟩)
            equiv := fun g u => hfe _ u _ }⟩

end Coh2

section Beta

variable {W : Type} [CommGroup W]

theorem good_of_beta
    [Finite W] {H : Subgroup (MulAut W)} (hne : ¬ (commV H ⊔ fixV H = ⊤))
    (hirr : commV H ∈ IrrPlus H ⊤) (hnat : BinaryNaturalSL H (commV H) (fixV H ⊓ commV H) 3 1)
    (hbot : fixV H ⊓ commV H = ⊥) : GoodFactor H := by
  have hbot' : commV H ⊓ fixV H = ⊥ := by rw [inf_comm]; exact hbot
  rw [hbot] at hnat
  obtain ⟨D⟩ := exists_cohData le_rfl hnat
  obtain ⟨π', hπ'⟩ := BinaryNaturalSL.exists_zmod hnat
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := hnat
  have hinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have hinj' : Function.Injective π' := injective_of_faithful_sec (FFModel.nat_faithful _) hπ'
  have hCinv : ∀ g : ↥H, ∀ c ∈ fixV H, (g : MulAut W) c ∈ fixV H := fun g c hc => by
    rw [hc g g.2]; exact hc
  refine ⟨Or.inr (Or.inr ⟨1, K, hK, hf, le_rfl, odd_one, hc,
    ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩⟩), Or.inr (Or.inr ⟨?_, le_top, ?_, ?_, ?_⟩)⟩
  · exact ⟨(MulEquiv.ofBijective π' ⟨hinj', hπ'.1⟩).symm⟩
  · rw [Subgroup.card_top]
    exact D.card_eq hne
  · rintro ⟨A, B, hCA, hCB, hAi, hBi, -, hAB⟩
    have key : ∀ X : Subgroup W, fixV H < X → XMod.IsInv ↥H X → X ⊓ commV H ≠ ⊥ := by
      intro X hCX hXi hX
      obtain ⟨a, haX, haC⟩ := IsConcreteLE.exists_of_lt hCX
      have hmove : ∃ h ∈ H, h a ≠ a := by
        by_contra hcon
        push Not at hcon
        exact haC (fun h hh => hcon h hh)
      obtain ⟨h, hh, hha⟩ := hmove
      have h1 : h a * a⁻¹ ∈ X ⊓ commV H :=
        ⟨X.mul_mem (hXi ⟨h, hh⟩ a haX) (X.inv_mem haX), Subgroup.subset_closure ⟨h, hh, a, rfl⟩⟩
      rw [hX] at h1
      exact hha (mul_inv_eq_one.1 (Subgroup.mem_bot.1 h1))
    have hfixed : XMod.fixed ↥H (commV H) = ⊥ := by
      rw [eq_bot_iff, ← hbot]
      intro l hl
      exact ⟨fun g hg => hl.2 ⟨g, hg⟩, hl.1⟩
    have hirr' := hirr.2.2.2
    rw [hfixed] at hirr'
    have hinvU : ∀ X : Subgroup W, XMod.IsInv ↥H X → XMod.IsInv ↥H (X ⊓ commV H) := by
      intro X hX a l hl
      exact ⟨hX a l hl.1, commV_invariant_self H a a.2 l hl.2⟩
    have hsub : ∀ X : Subgroup W, fixV H < X → XMod.IsInv ↥H X → X ⊓ commV H = commV H := by
      intro X hCX hXi
      rcases hirr'.2 (X ⊓ commV H) (hinvU X hXi) bot_le inf_le_right with h | h
      · exact absurd h (key X hCX hXi)
      · exact h
    have hAU := hsub A hCA hAi
    have hBU := hsub B hCB hBi
    have hUC : commV H ≤ fixV H := by
      rw [← hAB]
      exact le_inf (hAU ▸ inf_le_left) (hBU ▸ inf_le_left)
    have hU0 : commV H = ⊥ := by
      rw [eq_bot_iff, ← hbot]
      exact le_inf hUC le_rfl
    exact key A hCA hAi (by rw [hAU, hU0])
  · rw [modComm_eq_commSub, ← commV_eq_commSub]
    exact ⟨K, hK, hf, hc, π, RealizesVia.extend hπ hCinv hbot'⟩

end Beta

end FFC

end CFSG.Quasithin
