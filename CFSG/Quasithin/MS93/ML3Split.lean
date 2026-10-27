module

public import CFSG.Quasithin.MS93.ML3ExtFF
import all CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Quasithin.MS93.ML3Gen

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Timmesfeld
open CFSG.Timmesfeld.Orders Matrix

theorem ordA_two_ne_360 {m : ℕ} (hm : 1 ≤ m) : ordA 2 (2 ^ m) ≠ 360 := by
  intro h
  obtain ⟨r, hr, hm'⟩ := (profile_ordA (n := 2) (f := m) (by norm_num) hm).two
  rw [h] at hm'
  have h3 : m * (2 * (2 + 1) / 2) = 3 :=
    eq_of_two_pow_mul_odd hr (by decide : Odd 45) (hm'.symm.trans (by norm_num))
  have hm1 : m = 1 := by norm_num at h3; omega
  subst hm1
  revert h
  decide

theorem ordA_two_ne_ordG2 {m g : ℕ} (hm : 1 ≤ m) (hg : 2 ≤ g) : ordA 2 (2 ^ m) ≠ ordG2 (2 ^ g) := by
  intro h
  have P1 := profile_ordA (n := 2) (f := m) (by norm_num) hm
  rw [h] at P1
  obtain ⟨hN, hZ⟩ := Profile.transfer P1 (profile_ordG2 (by omega : 1 ≤ g))
  have hm2 : m = 2 * g := by norm_num at hN; omega
  have hz : zA 2 m (4 * g) := ⟨2, by simp, ⟨1, by rw [hm2]; ring⟩⟩
  obtain ⟨a, ha, hdvd⟩ := (hZ (4 * g) (by omega) (by omega)).1 hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · obtain ⟨c, hc⟩ := hdvd
    have : g * 6 = 4 * g * c := hc
    have hc' : 6 = 4 * c := by
      have hg0 : 0 < g := by omega
      nlinarith
    omega
  · have := Nat.le_of_dvd (by omega) hdvd
    omega

section Card

variable {V : Type} [CommGroup V]

theorem card_of_realizesVia_nat {ι : Type} [Fintype ι] [DecidableEq ι] {F' : Type} [Field F']
    [Finite F'] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F')} {H : Subgroup (MulAut V)}
    {U : Subgroup V} {π : (FFModel.nat Γ).Gam →* ↥H} (h : (FFModel.nat Γ).RealizesVia H U ⊥ π) :
    Nat.card U = Nat.card F' ^ Fintype.card ι := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβ1, -⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβ1 u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩)]
  change Nat.card (↥(⊤ : Subgroup (Multiplicative (ι → F'))) ⧸
    (⊥ : Subgroup (Multiplicative (ι → F'))).subgroupOf ⊤) = _
  rw [Subgroup.bot_subgroupOf]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (⊥ : Subgroup ↥(⊤ : Subgroup (Multiplicative (ι → F'))))
  rw [Subgroup.card_bot, mul_one] at h1
  rw [← h1, Subgroup.card_top]
  rw [show Nat.card (Multiplicative (ι → F')) = Nat.card (ι → F') from rfl, Nat.card_fun,
    Nat.card_eq_fintype_card (α := ι)]

theorem card_mul_le_of_inf_eq_bot [Finite V] {A B : Subgroup V} (h : A ⊓ B = ⊥) :
    Nat.card A * Nat.card B ≤ Nat.card V ∧
      (Nat.card A * Nat.card B = Nat.card V → ∀ v : V, ∃ a ∈ A, ∃ b ∈ B, a * b = v) := by
  let f : A × B → V := fun p => (p.1 : V) * p.2
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hab' : (a : V) * b = a' * b' := hab
    have hx : (a' : V)⁻¹ * a = b' * (b : V)⁻¹ := by
      calc (a' : V)⁻¹ * a = (a' : V)⁻¹ * ((a : V) * b) * (b : V)⁻¹ := by group
        _ = (a' : V)⁻¹ * ((a' : V) * b') * (b : V)⁻¹ := by rw [hab']
        _ = b' * (b : V)⁻¹ := by group
    have hmem : (a' : V)⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, hx ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [h, Subgroup.mem_bot] at hmem
    have ha : (a' : V) = a := inv_mul_eq_one.mp hmem
    have hb : (b' : V) = b := by
      rw [hmem] at hx
      exact (mul_inv_eq_one.mp hx.symm)
    exact Prod.ext (Subtype.ext ha.symm) (Subtype.ext hb.symm)
  have hc : Nat.card A * Nat.card B ≤ Nat.card V := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective f hf
  refine ⟨hc, fun heq v => ?_⟩
  have hbij := hf.bijective_of_nat_card_le (by rw [Nat.card_prod, heq])
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 v
  exact ⟨a, a.2, b, b.2, hab⟩

end Card

variable {F : Type} [Field F] [CharP F 2] [Finite F]
variable {V : Type} [CommGroup V] {ρ : SL3 F →* MulAut V}

namespace NatNatExt

variable (E : NatNatExt ρ)
include E

omit [CharP F 2] [Finite F] in
theorem inf_range_eq_bot_or {W : Subgroup V}
    (hW : ∀ (g : SL3 F), ∀ w ∈ W, ρ g w ∈ W) : W ⊓ E.ι.range = ⊥ ∨ E.ι.range ≤ W := by
  by_cases h : W ⊓ E.ι.range = ⊥
  · exact Or.inl h
  · right
    obtain ⟨⟨v, hvW, hvι⟩, hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
    have hv1 : v ≠ 1 := fun hv => hv1' (Subtype.ext hv)
    obtain ⟨m, rfl⟩ := hvι
    let S : AddSubgroup (Fin 3 → F) :=
      { carrier := {y | E.ι (Multiplicative.ofAdd y) ∈ W}
        zero_mem' := by
          show E.ι (Multiplicative.ofAdd 0) ∈ W
          rw [ofAdd_zero, map_one]
          exact W.one_mem
        add_mem' := fun {y y'} hy hy' => by
          show E.ι (Multiplicative.ofAdd (y + y')) ∈ W
          rw [ofAdd_add, map_mul]
          exact W.mul_mem hy hy'
        neg_mem' := fun {y} hy => by
          show E.ι (Multiplicative.ofAdd (-y)) ∈ W
          rw [ofAdd_neg, map_inv]
          exact W.inv_mem hy }
    have hS : ∀ (g : SL3 F) (y : Fin 3 → F), y ∈ S →
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ S := fun g y hy => by
      show E.ι (Multiplicative.ofAdd _) ∈ W
      rw [← E.ι_equiv]
      exact hW g _ hy
    have hm : Multiplicative.toAdd m ∈ S := by
      show E.ι (Multiplicative.ofAdd (Multiplicative.toAdd m)) ∈ W
      exact hvW
    have hm0 : Multiplicative.toAdd m ≠ 0 := by
      intro h0
      apply hv1
      rw [show m = Multiplicative.ofAdd (Multiplicative.toAdd m) from rfl, h0, ofAdd_zero,
        map_one]
    rintro _ ⟨y, rfl⟩
    exact mem_of_invariant S hS hm hm0 (Multiplicative.toAdd y)

omit [CharP F 2] in
theorem card_range_ι : Nat.card E.ι.range = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective E.ι_injective).toEquiv, card_natMod]

omit [CharP F 2] [Finite F] in
theorem exists_equiv_of_compl [Finite V] {W : Subgroup V}
    (hW : ∀ (g : SL3 F), ∀ w ∈ W, ρ g w ∈ W) (hW0 : W ⊓ E.ι.range = ⊥)
    (hWc : Nat.card W * Nat.card E.ι.range = Nat.card V) :
    ∃ γ : V →* Multiplicative (Fin 2 → Fin 3 → F), Function.Bijective γ ∧
      ∀ (g : SL3 F) (v : V) (i : Fin 2), Multiplicative.toAdd (γ (ρ g v)) i =
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (γ v) i := by
  have hsurj := (card_mul_le_of_inf_eq_bot hW0).2 hWc
  let βW : W →* Multiplicative (Fin 3 → F) := E.β.comp W.subtype
  have hβWi : Function.Injective βW := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hmem : (w : V) ∈ W ⊓ E.ι.range := ⟨w.2, (E.mem_range_ι_iff _).mpr hw⟩
    rw [hW0, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hβWs : Function.Surjective βW := by
    intro x
    obtain ⟨v, rfl⟩ := E.β_surjective x
    obtain ⟨a, ha, b, hb, rfl⟩ := hsurj v
    refine ⟨⟨a, ha⟩, ?_⟩
    show E.β a = E.β (a * b)
    rw [map_mul, (E.mem_range_ι_iff b).mp hb, mul_one]
  let eW : W ≃* Multiplicative (Fin 3 → F) := MulEquiv.ofBijective βW ⟨hβWi, hβWs⟩
  have hs_equiv : ∀ (g : SL3 F) (x : Fin 3 → F),
      ρ g (eW.symm (Multiplicative.ofAdd x) : V) =
        (eW.symm (Multiplicative.ofAdd (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)) : V) := by
    intro g x
    set w := eW.symm (Multiplicative.ofAdd x) with hw
    have hgw : ρ g (w : V) ∈ W := hW g _ w.2
    have h1 : eW ⟨ρ g w, hgw⟩ =
        Multiplicative.ofAdd (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
      show E.β (ρ g w) = _
      apply Multiplicative.toAdd.injective
      rw [E.β_equiv]
      have : E.β (w : V) = Multiplicative.ofAdd x := by
        have := eW.apply_symm_apply (Multiplicative.ofAdd x)
        exact this
      rw [this]
      rfl
    rw [← h1, MulEquiv.symm_apply_apply]
  let θ : Multiplicative (Fin 2 → Fin 3 → F) →* V :=
    { toFun := fun z => (eW.symm (Multiplicative.ofAdd (Multiplicative.toAdd z 0)) : V) *
        E.ι (Multiplicative.ofAdd (Multiplicative.toAdd z 1))
      map_one' := by simp
      map_mul' := fun z z' => by
        simp only [toAdd_mul, Pi.add_apply, ofAdd_add, map_mul, Subgroup.coe_mul]
        ac_rfl }
  have hθ : Function.Bijective θ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro z hz
      have hz' : (eW.symm (Multiplicative.ofAdd (Multiplicative.toAdd z 0)) : V) *
          E.ι (Multiplicative.ofAdd (Multiplicative.toAdd z 1)) = 1 := hz
      have hβ := congrArg E.β hz'
      rw [map_mul, (E.mem_range_ι_iff _).mp ⟨_, rfl⟩, mul_one, map_one] at hβ
      have h0 : Multiplicative.toAdd z 0 = 0 := by
        have : eW (eW.symm (Multiplicative.ofAdd (Multiplicative.toAdd z 0))) = 1 := hβ
        rw [MulEquiv.apply_symm_apply] at this
        exact this
      rw [h0, ofAdd_zero, map_one, Subgroup.coe_one, one_mul] at hz'
      have h1 := E.ι_ofAdd_eq_one hz'
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · exact h0
      · exact h1
    · intro v
      set x := Multiplicative.toAdd (E.β v)
      set w := eW.symm (Multiplicative.ofAdd x)
      have hβw : E.β (v * (w : V)⁻¹) = 1 := by
        rw [map_mul, map_inv]
        have : E.β (w : V) = Multiplicative.ofAdd x := eW.apply_symm_apply _
        rw [this]
        exact mul_inv_cancel _
      obtain ⟨y, hy⟩ := E.exists_ι_eq hβw
      refine ⟨Multiplicative.ofAdd ![x, y], ?_⟩
      change (w : V) * E.ι (Multiplicative.ofAdd y) = v
      rw [hy, mul_comm v, mul_inv_cancel_left]
  let eθ := MulEquiv.ofBijective θ hθ
  refine ⟨eθ.symm.toMonoidHom, eθ.symm.bijective, ?_⟩
  intro g v i
  obtain ⟨z, rfl⟩ := hθ.2 v
  have hθg : ρ g (θ z) = θ (Multiplicative.ofAdd fun j =>
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd z j) := by
    show ρ g ((eW.symm (Multiplicative.ofAdd (Multiplicative.toAdd z 0)) : V) *
      E.ι (Multiplicative.ofAdd (Multiplicative.toAdd z 1))) = _
    rw [map_mul, hs_equiv, E.ι_equiv]
    rfl
  rw [hθg]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [show eθ.symm (θ (Multiplicative.ofAdd fun j => ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Multiplicative.toAdd z j)) = Multiplicative.ofAdd fun j =>
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd z j from
      eθ.symm_apply_apply _, show eθ.symm (θ z) = z from eθ.symm_apply_apply _]
  rfl

omit [CharP F 2] in
theorem exists_dsum_of_ffConclusion
    [Finite V] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hc : FFConclusion ρ.range ρ.range) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F'),
      DirectSumOfCopies ρ.range ⊤ ⊥ (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F')) 2 := by
  obtain ⟨-, -, hcases, -⟩ := hc
  have hn : 1 ≤ n := R3c2.one_le_of_natCard_eq_two_pow hF
  have hKZ : Nat.card (↥ρ.range ⧸ Subgroup.center ↥ρ.range) = ordA 2 (2 ^ n) :=
    (isPSL_quot_of_equiv_statedSL_three hF
      ((specialLinearGroupEquivStatedSL 3 F).symm.trans E.rangeEquiv)).2.2
  rcases hcases with ⟨n', F', iF', fF', hn', hF', ⟨e⟩, -, hnat | hdsum⟩ | ⟨-, hHat, -, -⟩ |
    (⟨n', hn', F'', iF'', fF'', hF'', π, hπ⟩ | ⟨π, hπ⟩) |
    (⟨n', hn', F'', iF'', fF'', hF'', π, hπ⟩ | ⟨-, hne, -⟩)
  · exfalso
    obtain ⟨π, hπ⟩ := hnat
    have h1 := card_of_realizesVia_nat hπ
    rw [Subgroup.card_top, E.card_eq, Fintype.card_fin, hF', hF] at h1
    have h2 := (isPSL_quot_of_equiv_statedSL_three hF' e.symm).2.2
    rw [hKZ] at h2
    have P1 := profile_ordA (n := 2) (f := n) (by norm_num) hn
    rw [h2] at P1
    obtain ⟨hN, -⟩ := Profile.transfer P1 (profile_ordA (n := 2) (f := n') (by norm_num) hn')
    have hnn : n = n' := by norm_num at hN; omega
    rw [← pow_mul, ← pow_mul] at h1
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  · exact ⟨F', iF', fF', hdsum⟩
  · exact absurd (hKZ.symm.trans (card_quot_of_isHat hHat)) (ordA_two_ne_360 hn)
  · exfalso
    let e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    have h1 := card_quot_of_equiv_statedSp hF'' hn' e
    rw [hKZ] at h1
    exact ordA_ne_ordBC_two (n := 2) (by norm_num) hn (by omega) h1
  · exfalso
    let e := FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ
    exact ordA_two_ne_360 hn (hKZ.symm.trans (card_quot_of_equiv_alt6 e))
  · exfalso
    have : CharP F'' 2 := FFC.charP_two_of_card_pow hF''
    let e := FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ
    have h1 := card_quot_of_equiv_quasithinG2 hF'' hn' e
    rw [hKZ] at h1
    exact ordA_two_ne_ordG2 hn hn' h1
  · exact absurd rfl hne

omit [CharP F 2] in
theorem exists_equiv_of_dsum [Finite V] {F' : Type} [Field F'] [Finite F']
    (hd : DirectSumOfCopies ρ.range ⊤ ⊥ (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F')) 2) :
    ∃ γ : V →* Multiplicative (Fin 2 → Fin 3 → F), Function.Bijective γ ∧
      ∀ (g : SL3 F) (v : V) (i : Fin 2), Multiplicative.toAdd (γ (ρ g v)) i =
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (γ v) i := by
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := hd
  have h01 : I 0 ⊓ I 1 = ⊥ := by
    apply le_bot_iff.mp
    rw [← hind 0]
    refine inf_le_inf_left _ (le_sup_of_le_right ?_)
    exact le_iSup₂_of_le (f := fun (j : Fin 2) (_ : j ≠ 0) => I j) 1 (by decide) le_rfl
  have hinv : ∀ i (g : SL3 F), ∀ w ∈ I i, ρ g w ∈ I i := fun i g w hw =>
    (hreal i).2.2.2.1 ⟨ρ g, g, rfl⟩ w hw
  have hcard : ∀ i, Nat.card (I i) = Nat.card F' ^ 3 := fun i => by
    rw [card_of_realizesVia_nat (hreal i), Fintype.card_fin]
  have htop : I 0 ⊔ I 1 = ⊤ := by
    rw [eq_top_iff, ← hsup, bot_sup_eq]
    refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hV : Nat.card (I 0) * Nat.card (I 1) = Nat.card V := by
    refine le_antisymm (card_mul_le_of_inf_eq_bot h01).1 ?_
    rw [← Subgroup.card_top (G := V), ← htop]
    exact card_sup_le_mul _ _
  have hI0 : Nat.card (I 0) = Nat.card F ^ 3 := by
    rw [hcard 1, ← hcard 0, E.card_eq, ← sq, show 6 = 3 * 2 by rfl, pow_mul] at hV
    exact Nat.pow_left_injective (by norm_num) hV
  have hI1 : Nat.card (I 1) = Nat.card F ^ 3 := by rw [hcard 1, ← hcard 0, hI0]
  have hcV : Nat.card F ^ 3 * Nat.card F ^ 3 = Nat.card V := by rw [E.card_eq]; ring
  rcases E.inf_range_eq_bot_or (hinv 0) with h0 | h0
  · exact E.exists_equiv_of_compl (hinv 0) h0 (by rw [hI0, E.card_range_ι, hcV])
  · have h1 : I 1 ⊓ E.ι.range = ⊥ := by
      apply le_bot_iff.mp
      calc I 1 ⊓ E.ι.range ≤ I 1 ⊓ I 0 := inf_le_inf_left _ h0
        _ = ⊥ := by rw [inf_comm, h01]
    exact E.exists_equiv_of_compl (hinv 1) h1 (by rw [hI1, E.card_range_ι, hcV])

variable (hV : ∀ v : V, v ^ 2 = 1)
include hV

theorem exists_equiv_two
    [Finite V] (h14 : MS14AS) {n : ℕ} (hF : Nat.card F = 2 ^ n) (hsq : SQTKGroup ↥ρ.range) :
    ∃ γ : V →* Multiplicative (Fin 2 → Fin 3 → F), Function.Bijective γ ∧
      ∀ (g : SL3 F) (v : V) (i : Fin 2), Multiplicative.toAdd (γ (ρ g v)) i =
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (γ v) i := by
  obtain ⟨F', iF', fF', hd⟩ := E.exists_dsum_of_ffConclusion hF (E.ffConclusion hV h14 hF hsq)
  exact E.exists_equiv_of_dsum hd

end NatNatExt

end CFSG.Quasithin.MS93
