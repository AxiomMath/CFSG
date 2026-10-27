module

public import CFSG.Quasithin.Background.RonanE43M24
public import CFSG.Quasithin.Background.RonanE43Cyc23
public import CFSG.Quasithin.Background.HMathieuCode

public section

open scoped commutatorElement

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.E3
  CFSG.Monster.Code

section Simple

variable {X : Type} [Group X] [Finite X]

theorem generalizedFitting_eq_top_of_simple (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) : CFSG.generalizedFitting X = ⊤ := by
  haveI := hs
  haveI hn : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.generalizedFitting X) with h | h
  · exfalso
    have hle := CFSG.centralizer_generalizedFitting_le X
    rw [h] at hle
    obtain ⟨a, b, hab⟩ := hnab
    have hall : ∀ y : X, y = 1 := fun y => by
      have hy : y ∈ Subgroup.centralizer ((⊥ : Subgroup X) : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
        rw [hg]
        simp
      exact Subgroup.mem_bot.mp (hle hy)
    exact hab (by rw [hall a, hall b])
  · exact h

theorem center_eq_bot_of_simple (hs : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) :
    Subgroup.center X = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem isQuasisimple_of_simple (hs : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) :
    CFSG.IsQuasisimple X := by
  haveI := hs
  have hcenter : Subgroup.center X = ⊥ := center_eq_bot_of_simple hs hnab
  have hcomm : commutator X = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have : ⁅a, b⁆ ∈ commutator X :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact hab this
    · exact h
  obtain ⟨a, b, hab⟩ := hnab
  let f : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  refine ⟨⟨hcomm⟩, f.isSimpleGroup, f.symm a, f.symm b, fun h => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg f h

end Simple

theorem eq_mul_inv_self_aux {M : Type*} [CommGroup M] (u x : M) : x = u * (u * x⁻¹)⁻¹ := by
  simp [mul_comm]

section Fixed

theorem rho_eq_one_of_fixed {numer denom : Subgroup (G6.PermMod 24)} {W : Type*} [CommGroup W]
    (c : SecCoords numer denom W) (hnum : numer ≤ G6.coreMod 24) (hΩ : G6.allOnes 24 ∈ denom)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)
    (σ : ↥Γ) (hσ : orderOf (σ : Equiv.Perm (Fin 24)) = 23) {w : W}
    (hw : c.rho Γ hΓ σ w = w) : w = 1 := by
  set a : MulAut (G6.PermMod 24) := G6.permAct 24 (σ : Equiv.Perm (Fin 24)) with ha
  have hσ23 : (σ : Equiv.Perm (Fin 24)) ^ 23 = 1 := by
    have := pow_orderOf_eq_one (σ : Equiv.Perm (Fin 24))
    rwa [hσ] at this
  have ha23 : a ^ 23 = 1 := by rw [ha, ← map_pow, hσ23, map_one]
  have hxnum : c.lift w ∈ numer := c.lift_mem w
  have hxx : c.lift w * c.lift w = 1 := permMod_mul_self 24 _
  have hκ : c.κ (a (c.lift w)) = c.κ (c.lift w) := by
    have := c.κ_permAct_rho Γ hΓ σ hxnum
    rw [c.κ_lift] at this
    rw [c.κ_lift]
    exact this.trans hw
  have hmem : a (c.lift w) * (c.lift w)⁻¹ ∈ numer :=
    numer.mul_mem ((hΓ σ σ.2).1 _ hxnum) (numer.inv_mem hxnum)
  have h1 : c.κ (a (c.lift w) * (c.lift w)⁻¹) = 1 := by
    have e1 : c.κ (a (c.lift w) * (c.lift w)⁻¹) = c.κ (a (c.lift w)) * c.κ ((c.lift w)⁻¹) :=
      c.κ.map_mul _ _
    have e2 : c.κ ((c.lift w)⁻¹) = (c.κ (c.lift w))⁻¹ := c.κ.map_inv _
    rw [e1, e2, hκ, mul_inv_cancel]
  have hxD : a (c.lift w) * (c.lift w)⁻¹ ∈ denom := (c.ker_iff _ hmem).1 h1
  obtain ⟨u, huE, hau, huD⟩ := exists_fixed_mem_of_pow a ha23 denom numer
    (fun d hd => (hΓ σ σ.2).2 d hd) (fun e he => (hΓ σ σ.2).1 e he) hxx hxnum hxD
  have hu01 := eq_one_or_allOnes_of_perm23 hσ (hnum huE) hau
  have huden : u ∈ denom := by
    rcases hu01 with h | h
    · rw [h]; exact denom.one_mem
    · rw [h]; exact hΩ
  have hxden : c.lift w ∈ denom := by
    have : c.lift w = u * (u * (c.lift w)⁻¹)⁻¹ := (eq_mul_inv_self_aux u (c.lift w))
    rw [this]
    exact denom.mul_mem huden (denom.inv_mem huD)
  calc w = c.κ (c.lift w) := (c.κ_lift w).symm
    _ = 1 := (c.ker_iff _ hxnum).2 hxden

theorem fixV_rho_eq_bot {numer denom : Subgroup (G6.PermMod 24)} {W : Type*} [CommGroup W]
    (c : SecCoords numer denom W) (hnum : numer ≤ G6.coreMod 24) (hΩ : G6.allOnes 24 ∈ denom)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)
    (σ : ↥Γ) (hσ : orderOf (σ : Equiv.Perm (Fin 24)) = 23) :
    fixV (c.rho Γ hΓ).range = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  have h : ∀ x ∈ (c.rho Γ hΓ).range, x v = v := mem_fixV.mp hv
  exact rho_eq_one_of_fixed c hnum hΩ hΓ σ hσ (h _ ⟨σ, rfl⟩)

theorem golayC_le_coreMod : golayC ≤ G6.coreMod 24 := by
  intro x hx
  rw [G6.mem_coreMod]
  have h := dotProduct_eq_zero (show Multiplicative.toAdd x ∈ C from hx) Ω_mem_C
  simpa [dotProduct, Ω] using h

theorem allOnes_mem_golayC : G6.allOnes 24 ∈ golayC := Ω_mem_C

end Fixed

section Main


theorem exists_orderOf_23 : ∃ σ : ↥AutPerm, orderOf (σ : Equiv.Perm (Fin 24)) = 23 := by
  haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have h : 23 ∣ Nat.card ↥AutPerm := by rw [card_AutPerm]; norm_num
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' 23 h
  exact ⟨σ, by rw [Subgroup.orderOf_coe]; exact hσ⟩

theorem fixV_rhoC11_eq_bot : fixV (rhoC11 AutPerm le_rfl).range = ⊥ := by
  obtain ⟨σ, hσ⟩ := exists_orderOf_23
  exact fixV_rho_eq_bot codeCoords golayC_le_coreMod (Subgroup.mem_zpowers _)
    (fun _ hσ => preserves_code hσ) σ hσ

theorem fixV_rho11_eq_bot : fixV (rho11 AutPerm le_rfl).range = ⊥ := by
  obtain ⟨σ, hσ⟩ := exists_orderOf_23
  exact fixV_rho_eq_bot cocodeCoords le_rfl allOnes_mem_golayC
    (fun _ hσ => preserves_cocode hσ) σ hσ

theorem exists_ne_one_fixed {W : Type} [CommGroup W] [Finite W] (hW : Even (Nat.card W))
    (T : Subgroup (MulAut W)) (hT : IsPGroup 2 T) : ∃ v : W, v ≠ 1 ∧ ∀ x ∈ T, x v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hT.card_modEq_card_fixedPoints W
  have hF1 : (1 : W) ∈ MulAction.fixedPoints ↥T W := fun t => by
    show (t : MulAut W) 1 = 1
    exact map_one _
  haveI : Nonempty (MulAction.fixedPoints ↥T W) := ⟨⟨1, hF1⟩⟩
  have h' : Nat.card W % 2 = Nat.card (MulAction.fixedPoints ↥T W) % 2 := h
  have hFeven : Nat.card (MulAction.fixedPoints ↥T W) % 2 = 0 := by
    rw [← h']
    exact Nat.even_iff.mp hW
  have hgt : 1 < Nat.card (MulAction.fixedPoints ↥T W) := by
    by_contra hle
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥T W) := Nat.card_pos
    have : Nat.card (MulAction.fixedPoints ↥T W) = 1 := by omega
    omega
  haveI : Nontrivial (MulAction.fixedPoints ↥T W) := Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨c, hc⟩ := exists_ne (⟨1, hF1⟩ : MulAction.fixedPoints ↥T W)
  refine ⟨c, fun h1 => hc (Subtype.ext h1), fun x hx => ?_⟩
  have := c.2 ⟨x, hx⟩
  exact this

end Main

section Final


noncomputable def autPermEquivM24 : ↥AutPerm ≃* ↥CFSG.Blueprint.NativeSporadic.M24 :=
  (MulEquiv.subgroupCongr (AutPerm_eq_closure.trans bridge_closure_eq_map)).trans
    (CFSG.Blueprint.NativeSporadic.M24.equivMapOfInjective _
      (MulAut.conj bridgeQ⁻¹).injective).symm

theorem aParam_le_three_of_fixfree {W : Type} [CommGroup W] [Finite W] (hW : Even (Nat.card W))
    (ϱ : ↥AutPerm →* MulAut W) (hfix : fixV ϱ.range = ⊥) : aParam ϱ.range ≤ 3 := by
  classical
  haveI hsimple : IsSimpleGroup ↥AutPerm := AutPerm_isSimpleGroup
  have hnab : ∃ a b : ↥AutPerm, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative ↥AutPerm := ⟨⟨hcon⟩⟩
    have hp : (Nat.card ↥AutPerm).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    rw [card_AutPerm] at hp
    exact absurd hp (by norm_num)
  have hW1 : 1 < Nat.card W := by
    have hpos : 0 < Nat.card W := Nat.card_pos
    obtain ⟨k, hk⟩ := hW
    omega
  haveI : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp hW1
  obtain ⟨w, hw⟩ := exists_ne (1 : W)
  have hρ : Function.Injective ϱ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ϱ.ker with h | h
    · exact h
    · exfalso
      have hmem : w ∈ fixV ϱ.range := by
        rw [mem_fixV]
        rintro _ ⟨g, rfl⟩
        have : g ∈ ϱ.ker := by rw [h]; exact Subgroup.mem_top g
        rw [MonoidHom.mem_ker.mp this]
        rfl
      rw [hfix] at hmem
      exact hw (Subgroup.mem_bot.mp hmem)
  have hO2 : pCoreOf 2 (⊤ : Subgroup ↥AutPerm) = ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI hn : (pCoreOf 2 (⊤ : Subgroup ↥AutPerm)).Normal :=
      Subgroup.normalizer_eq_top_iff.mp
        (eq_top_iff.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCoreOf 2 (⊤ : Subgroup ↥AutPerm)) with h | h
    · exact h
    · exfalso
      have hp : IsPGroup 2 (⊤ : Subgroup ↥AutPerm) := by
        have := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup ↥AutPerm)
        rwa [h] at this
      have hp' : IsPGroup 2 ↥AutPerm := hp.of_equiv Subgroup.topEquiv
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp'
      rw [card_AutPerm] at hn
      have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥AutPerm) := inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowIn 2 (P : Subgroup ↥AutPerm) ⊤ :=
    ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩
  have hlt : fixV ϱ.range < fixV ((P : Subgroup ↥AutPerm).map ϱ) := by
    obtain ⟨v, hv1, hvT⟩ := exists_ne_one_fixed hW ((P : Subgroup ↥AutPerm).map ϱ)
      (hT.isPGroup.map ϱ)
    rw [hfix]
    refine bot_lt_iff_ne_bot.mpr fun h => hv1 ?_
    have : v ∈ fixV ((P : Subgroup ↥AutPerm).map ϱ) := mem_fixV.mpr hvT
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  have hLF : (⊤ : Subgroup ↥AutPerm) = CFSG.generalizedFitting ↥AutPerm :=
    (generalizedFitting_eq_top_of_simple hsimple hnab).symm
  have hLq : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥AutPerm) :=
    CFSG.IsQuasisimple.of_mulEquiv Subgroup.topEquiv (isQuasisimple_of_simple hsimple hnab)
  have hM24 : IsSporadic .M24
      (↥(⊤ : Subgroup ↥AutPerm) ⧸ Subgroup.center ↥(⊤ : Subgroup ↥AutPerm)) := by
    haveI : IsSimpleGroup ↥(⊤ : Subgroup ↥AutPerm) :=
      (Subgroup.topEquiv (G := ↥AutPerm)).isSimpleGroup
    have hnab' : ∃ a b : ↥(⊤ : Subgroup ↥AutPerm), a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩
    have hcenter := center_eq_bot_of_simple this hnab'
    exact ⟨((((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).trans
      Subgroup.topEquiv).trans autPermEquivM24)⟩
  exact e43_M24 ↥AutPerm W ϱ hρ hO2 (P : Subgroup ↥AutPerm) ⊤ hT hlt hLF hLq hM24

theorem even_card_W11 : Even (Nat.card W11) := by
  have : Nat.card W11 = 2 ^ 11 := by
    rw [Nat.card_congr (Multiplicative.toAdd : W11 ≃ (Fin 11 → ZMod 2))]
    simp [Nat.card_eq_fintype_card]
  rw [this]
  exact ⟨2 ^ 10, by norm_num⟩

theorem aParam_le_three_of_mathieu23 {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} (h : MathieuCode23 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥) :
    aParam L ≤ 3 := by
  rcases h with h | h
  · obtain ⟨e, he⟩ := code23_std h
    have hle : L.map (congrHom e) ≤ (rhoC11 AutPerm le_rfl).range := by
      rw [he]
      rintro _ ⟨σ, rfl⟩
      exact ⟨⟨σ.1, σ.2.1⟩, rfl⟩
    rw [← aParam_map_congrHom e L]
    exact (aParam_mono hle).trans
      (aParam_le_three_of_fixfree even_card_W11 (rhoC11 AutPerm le_rfl) fixV_rhoC11_eq_bot)
  · obtain ⟨e, he⟩ := cocode23_std h
    have hle : L.map (congrHom e) ≤ (rho11 AutPerm le_rfl).range := by
      rw [he]
      rintro _ ⟨σ, rfl⟩
      exact ⟨⟨σ.1, σ.2.1⟩, rfl⟩
    rw [← aParam_map_congrHom e L]
    exact (aParam_mono hle).trans
      (aParam_le_three_of_fixfree even_card_W11 (rho11 AutPerm le_rfl) fixV_rho11_eq_bot)

end Final

end CFSG.Quasithin.RonanE43
