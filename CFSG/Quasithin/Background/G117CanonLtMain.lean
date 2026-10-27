module

public import CFSG.Quasithin.Background.G117CanonA6Perm
public import CFSG.Quasithin.Background.G117CanonA6Z3
public import CFSG.Quasithin.Background.G117CanonGroup
public import CFSG.Quasithin.Background.G117CanonLt
public import CFSG.Quasithin.Background.G117CanonMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace Canon

open CFSG.Quasithin.G11.G117 CFSG.Assembly.LowTwoRank

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem stepLt {Q : ConclPred} (hE11 : E11Stmt) (hN6 : A6NormalizerBound) (hA6 : A6Facts)
    (hQ : QContains Q) : StepLt Q := by
  intro V _ _ _ B Γ v₁ W X X₀ L I m c hH hne hV8 hm3 hI4 hperm hend
  have hf : LtFacts Γ L X I := ltFacts hE11 hN6 hA6 c hH hne hV8 hm3 hI4 hperm hend
  have h108 := c.h108
  have hHΓ : normalClosure Γ L ≤ Γ := h108.H_le
  have hNorm := normalClosure_normal Γ L
  have hfaithH : FaithfulOn (normalClosure Γ L) I := props_faithful c.props
  haveI : IsSimpleGroup ↥(normalClosure Γ L) := hf.simple_H
  obtain ⟨φ', β, hsurj, hker, hequ⟩ := hperm
  have hxI : ∀ x : ↥X, conjSub (x : GLV V) I = I := fun x => c.invariantX.conjSub_eq x.2
  let rx : ↥X → GLV ↥I := fun x => restrictEquiv (x : GLV V) I (hxI x)
  have hrnorm : ∀ x : ↥X, ∀ h' ∈ restrictRange (normalClosure Γ L) I hH,
      rx x * h' * (rx x)⁻¹ ∈ restrictRange (normalClosure Γ L) I hH := by
    intro x h' hh'
    obtain ⟨k, hk, rfl⟩ := (mem_restrictRange_iff' hH).1 hh'
    have hxk : (x : GLV V) * k * (x : GLV V)⁻¹ ∈ normalClosure Γ L :=
      hNorm x (h108.X_le x.2) k hk
    have e1 : rx x * restrictEquiv k I (hH.conjSub_eq hk) * (rx x)⁻¹ =
        restrictEquiv ((x : GLV V) * k * (x : GLV V)⁻¹) I (hH.conjSub_eq hxk) := by
      ext i
      rfl
    rw [e1]
    exact restrictEquiv_mem_restrictRange hH hxk
  have hex : ∀ x : ↥X, ∃ σ : Equiv.Perm (Fin 6), ActsAs β (rx x) σ := fun x =>
    exists_actsAs_of_normalizes φ' hsurj hker hequ (rx x) (hrnorm x)
  choose σ hσ using hex
  have hrmul : ∀ x y : ↥X, rx (x * y) = rx x * rx y := fun x y => by
    ext i
    rfl
  have hrone : rx 1 = 1 := by
    ext i
    rfl
  have hσmul : ∀ x y : ↥X, σ (x * y) = σ x * σ y := fun x y =>
    (hσ (x * y)).unique hker (by rw [hrmul x y]; exact (hσ x).mul (hσ y))
  have hσone : σ 1 = 1 :=
    (hσ 1).unique hker (by rw [hrone]; exact ActsAs.one β)
  let Θ : ↥X →* Equiv.Perm (Fin 6) :=
    { toFun := σ, map_one' := hσone, map_mul' := hσmul }
  have hΘinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hact : ActsAs β (rx x) 1 := by
      have := hσ x
      rwa [show σ x = 1 from hx] at this
    have hrx1 : rx x = 1 := actsAs_perm_unique hsurj hact (ActsAs.one β)
    apply Subtype.ext
    refine faithfulOn_iff.1 c.faithful (x : GLV V) x.2 (fun u hu => ?_)
    have h1 : ((rx x ⟨u, hu⟩ : ↥I) : V) = u := by
      have := congrArg (fun r : GLV ↥I => ((r ⟨u, hu⟩ : ↥I) : V)) hrx1
      simpa using this
    exact h1
  have hK8 : Nat.card ↥Θ.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΘinj).toEquiv, c.card, hm3]
    norm_num
  have hexp : ∀ k ∈ Θ.range, k * k = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (h108.X_sq x x.2)
    rw [this, map_one]
  have hcomm : ∀ a ∈ Θ.range, ∀ b ∈ Θ.range, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    have : x * y = y * x := Subtype.ext (h108.X_comm x x.2 y y.2)
    rw [this]
  obtain ⟨k, ⟨x₁, hx₁⟩, hswap⟩ := exists_swap_of_elemAbelian_order_eight Θ.range hK8 hexp hcomm
  have hτ : (σ x₁).IsSwap := by
    have : σ x₁ = k := hx₁
    rwa [this]
  have hx₁H : (x₁ : GLV V) ∉ normalClosure Γ L := by
    intro hmem
    have hrmem : rx x₁ ∈ restrictRange (normalClosure Γ L) I hH :=
      restrictEquiv_mem_restrictRange hH hmem
    obtain ⟨σ', hσ'A, hσ'⟩ := actsAs_even_of_mem φ' hequ hrmem
    have heq : σ' = σ x₁ := hσ'.unique hker (hσ x₁)
    rw [heq] at hσ'A
    obtain ⟨a, b, hab, hs⟩ := hτ
    have h1 : Equiv.Perm.sign (σ x₁) = 1 := Equiv.Perm.mem_alternatingGroup.1 hσ'A
    rw [hs, Equiv.Perm.sign_swap hab] at h1
    exact absurd h1 (by decide)
  obtain ⟨E, hE⟩ : ∃ E : Subgroup (GLV V), E = (genFittingLayer ↥Γ).map Γ.subtype := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Subgroup (GLV V), P = (CFSG.pCore 3 ↥Γ).map Γ.subtype := ⟨_, rfl⟩
  have hEH : E = normalClosure Γ L := hE.trans hf.layer
  have hPC : P = Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)) := hP.trans hf.pCore
  have hPcard : Nat.card ↥P = 3 := by
    rw [hPC]
    exact hf.card_C
  have hEcard : Nat.card ↥E = 360 := by
    rw [hEH]
    exact hf.card_H
  have hcommEP : ∀ e ∈ E, ∀ p ∈ P, e * p = p * e := by
    intro e he p hp
    rw [hEH] at he
    rw [hPC] at hp
    exact Subgroup.mem_centralizer_iff.1 hp.2 e he
  have hEP : E ⊓ P = ⊥ := by
    rw [hEH, hPC]
    exact inf_eq_bot_of_centralizing hf.simple_H hf.card_H fun p hp h hh =>
      (Subgroup.mem_centralizer_iff.1 hp.2 h hh).symm
  have hFit : genFittingFitting ↥Γ =
      (Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))).subgroupOf Γ := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine fitting_eq_centralizer hHΓ hNorm hf.simple_H
      (not_isNilpotent_of_simple_card_360 _ hf.card_H) ?_
    exact (IsPGroup.of_card (p := 3) (n := 1) (by rw [hf.card_C]; norm_num)).isNilpotent
  have hF : (genFittingFStar ↥Γ).map Γ.subtype = E ⊔ P := by
    rw [genFittingFStar.eq_sup, Subgroup.map_sup, hFit,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left, ← hE, ← hPC, sup_comm]
  have hinvP : ∀ p ∈ P, (x₁ : GLV V) * p * (x₁ : GLV V)⁻¹ = p⁻¹ := by
    intro p hp
    rw [hPC] at hp
    exact hf.inverts (x₁ : GLV V) x₁.2 hx₁H p hp
  have hMΓ : E ⊔ P ≤ Γ := sup_le (hEH ▸ hHΓ) (hPC ▸ inf_le_left)
  haveI : Finite ↥(E ⊔ P) :=
    Finite.of_injective (Subgroup.inclusion hMΓ) (Subgroup.inclusion_injective hMΓ)
  have hM1080 : 1080 ≤ Nat.card ↥(E ⊔ P) := by
    have := card_mul_le_card_sup E P hEP
    rw [hEcard, hPcard] at this
    omega
  have hxM : (x₁ : GLV V) ∉ E ⊔ P := by
    intro hmem
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hPcyc : IsCyclic ↥P := isCyclic_of_prime_card hPcard
    have hPcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p := fun p hp q hq => by
      letI := hPcyc.commGroup
      exact congrArg Subtype.val (mul_comm (⟨p, hp⟩ : ↥P) ⟨q, hq⟩)
    have hle : E ⊔ P ≤ Subgroup.centralizer (P : Set (GLV V)) := by
      refine sup_le (fun e he => ?_) (fun p hp => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro p hp
        exact (hcommEP e he p hp).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro q hq
        exact hPcomm q hq p hp
    have hcen := Subgroup.mem_centralizer_iff.1 (hle hmem)
    have hp1 : ∀ p ∈ P, p = 1 := by
      intro p hp
      have h1 : p * (x₁ : GLV V) = (x₁ : GLV V) * p := hcen p hp
      have h2 := hinvP p hp
      have h3 : (x₁ : GLV V) * p = p⁻¹ * (x₁ : GLV V) := by
        rw [mul_inv_eq_iff_eq_mul] at h2
        exact h2
      have h4 : p = p⁻¹ := by
        have := h1.trans h3
        exact mul_right_cancel this
      have h5 : p ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥P) (x := ⟨p, hp⟩)
        rw [hPcard] at this
        exact congrArg Subtype.val this
      have h6 : p * p = 1 := by
        have := mul_inv_cancel p
        rwa [← h4] at this
      calc p = p ^ 3 * (p * p)⁻¹ := by group
        _ = 1 := by rw [h5, h6]; simp
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 hp1
    rw [this, Subgroup.card_bot] at hPcard
    omega
  have hMlt : Nat.card ↥(E ⊔ P) < Nat.card ↥Γ := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne hMΓ fun h => hxM ?_)
    rw [h]
    exact h108.X_le x₁.2
  have hΓcard : Nat.card ↥Γ = 2 * Nat.card ↥(E ⊔ P) := by
    obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hMΓ
    rw [hf.card_Γ] at hj hMlt ⊢
    have hj3 : j < 3 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    interval_cases j <;> omega
  have hΓeq : Γ = (E ⊔ P) ⊔ Subgroup.zpowers (x₁ : GLV V) :=
    eq_sup_zpowers_of_card hMΓ (h108.X_le x₁.2) hxM hΓcard
  let hI : ↥(normalClosure Γ L) ≃* ↥(restrictRange (normalClosure Γ L) I hH) :=
    restrictRangeEquiv hH hfaithH
  let φ : ↥E ≃* ↥(alternatingGroup (Fin 6)) :=
    ((MulEquiv.subgroupCongr hEH).trans hI).trans φ'
  have hconj : ∀ e e' : ↥E, (x₁ : GLV V) * (e : GLV V) * (x₁ : GLV V)⁻¹ = (e' : GLV V) →
      ((φ e' : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) =
        σ x₁ * ((φ e : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) * (σ x₁)⁻¹ := by
    intro e₁ e₂ hx
    let g : ↥(restrictRange (normalClosure Γ L) I hH) :=
      hI (MulEquiv.subgroupCongr hEH e₁)
    have hg : rx x₁ * (g : GLV ↥I) * (rx x₁)⁻¹ ∈ restrictRange (normalClosure Γ L) I hH :=
      hrnorm x₁ g g.2
    have key := phi_conj_of_actsAs φ' hker hequ (hσ x₁) (hrnorm x₁) g hg
    have hgeq : (⟨rx x₁ * (g : GLV ↥I) * (rx x₁)⁻¹, hg⟩ :
        ↥(restrictRange (normalClosure Γ L) I hH)) = hI (MulEquiv.subgroupCongr hEH e₂) := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro i
      apply Subtype.ext
      exact congrArg (fun z : GLV V => z (i : V)) hx
    rw [hgeq] at key
    exact key
  have hIirr : IsIrr E I := by
    rw [hEH]
    exact (props_irrPlus c.props).isIrr h108.fixedSpace_H
  let βV : ↥(permCore 6) →ₗ[ZMod 2] V := I.subtype ∘ₗ β
  have hrange : LinearMap.range βV = I := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.2 hsurj, Submodule.map_top,
      Submodule.range_subtype]
  have hkerV : ∀ u : ↥(permCore 6), βV u = 0 ↔ (u = 0 ∨ u = onesCore6) := by
    intro u
    have h0 : βV u = 0 ↔ β u = 0 := by
      show ((β u : ↥I) : V) = 0 ↔ β u = 0
      exact Submodule.coe_eq_zero
    have hones : (Even 6 ∧ ∀ i, (u : Fin 6 → ZMod 2) i = 1) ↔ u = onesCore6 := by
      constructor
      · rintro ⟨-, h⟩
        exact Subtype.ext (funext h)
      · intro h
        refine ⟨by decide, fun i => ?_⟩
        rw [h]
        rfl
    rw [h0, hker u, hones]
  have hequV : ∀ (e : ↥E) (u u' : ↥(permCore 6)),
      (u' : Fin 6 → ZMod 2) = permAct ((φ e : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))
        (u : Fin 6 → ZMod 2) → βV u' = (e : GLV V) (βV u) := by
    intro e₁ u u' hu'
    have := congrArg Subtype.val (hequ (hI (MulEquiv.subgroupCongr hEH e₁)) u u' hu')
    exact this
  have hfix : ∀ p ∈ P, p ≠ 1 → ∀ v : V, p v = v → v = 0 := by
    intro p hp hp1 v hv
    by_contra hv0
    have hpC : p ∈ Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)) := hPC ▸ hp
    let U : Submodule (ZMod 2) V :=
      { carrier := {w | p w = w}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at *
          rw [map_add, ha, hb]
        zero_mem' := map_zero p
        smul_mem' := fun a w hw => by
          simp only [Set.mem_setOf_eq] at *
          rw [map_smul, hw] }
    have hUinv : Invariant (normalClosure Γ L) U := by
      intro h hh u hu
      have hc : h * p = p * h := Subgroup.mem_centralizer_iff.1 hpC.2 h hh
      have hu' : p u = u := hu
      show p (h u) = h u
      calc p (h u) = (p * h) u := rfl
        _ = (h * p) u := by rw [hc]
        _ = h u := by
          show h (p u) = h u
          rw [hu']
    have hUne : U ≠ ⊥ := fun hbot => hv0 (by
      have : v ∈ U := hv
      rw [hbot] at this
      exact (Submodule.mem_bot _).1 this)
    obtain ⟨J, hJU, hJirr⟩ := exists_isIrr_le hUinv hUne
    have hJplus : IrrPlus (normalClosure Γ L) J := hJirr.irrPlus h108.fixedSpace_H
    have hpJ : conjSub p J = J := by
      refine Submodule.ext fun w => ⟨fun ⟨u, hu, hw⟩ => ?_, fun hw => ⟨w, hw, ?_⟩⟩
      · have hpu : p u = u := hJU hu
        rw [← hw]
        change p u ∈ J
        rw [hpu]
        exact hu
      · exact hJU hw
    exact hf.moves p hpC hp1 ⟨J, hJplus⟩ hpJ
  have hmove : ∀ p ∈ P, p ≠ 1 → conjSub p I ≠ I := by
    intro p hp hp1 h
    have hpC : p ∈ Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)) := hPC ▸ hp
    exact hp1 (hf.inter_stab p hpC h)
  have hmark : TensorA6Z3WithMarking E P φ :=
    tensorA6Z3WithMarking_of_homogeneous E P φ I βV hV8 hrange hkerV hequV hIirr hPcard hcommEP
      hfix hmove
  exact c.setup.notConcl (hQ.c10 B Γ X ⟨hV8, E, P, (x₁ : GLV V), hE, hP, hPcard, hEP, hcommEP,
    hF, x₁.2, h108.X_le x₁.2, hΓeq, hinvP, φ, σ x₁, hτ, hmark, hconj⟩)

end Canon

end G11

end CFSG.Quasithin
