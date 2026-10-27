module

public import CFSG.Quasithin.EmptyFaithful.S1421QA26Fin
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.QA26

open Equiv Equiv.Perm

section Unpack

variable {V : Type} [CommGroup V]

theorem altDn7_ker_eq : (FFModel.altDn 7).ker = ⊥ := by
  show Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7 = ⊥
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz1
  have hsq : G6.allOnes 7 * G6.allOnes 7 = 1 := by decide +kernel
  have hnot : G6.allOnes 7 ∉ G6.coreMod 7 := by
    rw [G6.mem_coreMod]
    decide +kernel
  have hord : orderOf (G6.allOnes 7) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) (by decide +kernel)
  have hmod := zpow_mod_orderOf (G6.allOnes 7) k
  rw [hord] at hmod
  simp only [Nat.cast_ofNat] at hmod
  rw [← hmod]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero]
  · exfalso
    apply hnot
    rw [← hmod, h, zpow_one] at hz2
    exact hz2

@[expose] def D7Data (K : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∃ (π : ↥(alternatingGroup (Fin 7)) →* ↥K) (β : ↥U ≃* ↥(G6.coreMod 7)),
    Function.Surjective π ∧
    ∀ (σ : ↥(alternatingGroup (Fin 7))) (u : ↥U) (hu : ((π σ : ↥K) : MulAut V) (u : V) ∈ U),
      ((β ⟨((π σ : ↥K) : MulAut V) (u : V), hu⟩ : ↥(G6.coreMod 7)) : G6.PermMod 7) =
        G6.permAct 7 (σ : Perm (Fin 7)) (β u)

theorem D7Data.of_alternatingNatural {K : Subgroup (MulAut V)} {U : Subgroup V}
    (h : AlternatingNatural K U ⊥ 7) : D7Data K U := by
  obtain ⟨π, hπs, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  have hker : (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec = ⊥ := by
    rw [altDn7_ker_eq, Subgroup.bot_subgroupOf]
  let φ : (↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec) ≃*
      ↥(FFModel.altDn 7).sec :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans QuotientGroup.quotientBot
  have hφ : ∀ q, (QuotientGroup.mk (φ q) :
      ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec) = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => rfl
  have hinj : Function.Injective (φ.toMonoidHom.comp β) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : β u = 1 := φ.injective (by simpa using hu)
    have h2 := (hβk u).1 h1
    exact Subtype.ext (Subgroup.mem_bot.1 h2)
  have hsurj : Function.Surjective (φ.toMonoidHom.comp β) :=
    φ.surjective.comp hβs
  let e : ↥U ≃* ↥(FFModel.altDn 7).sec := MulEquiv.ofBijective (φ.toMonoidHom.comp β) ⟨hinj, hsurj⟩
  refine ⟨π, e, hπs, fun σ u hu => ?_⟩
  have hm : (FFModel.altDn 7).act σ ((e u : ↥(FFModel.altDn 7).sec) : (FFModel.altDn 7).Amb) ∈
      (FFModel.altDn 7).sec := hsec σ _ (e u).2
  have hum : β u = QuotientGroup.mk (e u) := (hφ (β u)).symm
  have := hβe σ u (e u) hu hm hum
  have h2 : e ⟨((π σ : ↥K) : MulAut V) (u : V), hu⟩ =
      ⟨(FFModel.altDn 7).act σ ((e u : ↥(FFModel.altDn 7).sec) : (FFModel.altDn 7).Amb), hm⟩ := by
    show φ (β _) = _
    rw [this]
    rfl
  exact congrArg Subtype.val h2

theorem card_of_a7Four {K : Subgroup (MulAut V)} {U : Subgroup V} (h : A7Four K U ⊥) :
    Nat.card U = 16 := by
  obtain ⟨α, π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)]
  have hker : (FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec = ⊥ := by
    have hk : (FFModel.a7Four α).ker = ⊥ := rfl
    rw [hk, Subgroup.bot_subgroupOf]
  have e1 : (↥(FFModel.a7Four α).sec ⧸ (FFModel.a7Four α).ker.subgroupOf
      (FFModel.a7Four α).sec) ≃* ↥(FFModel.a7Four α).sec :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans QuotientGroup.quotientBot
  rw [Nat.card_congr e1.toEquiv]
  show Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) = 16
  rw [Subgroup.card_top, Nat.card_eq_fintype_card]
  simp

end Unpack

section Four

variable {V : Type} [CommGroup V]

@[expose] def actHom (H : Subgroup (MulAut V)) (U : Subgroup V)
    (hH : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) : ↥H →* Equiv.Perm ↥U where
  toFun h :=
    { toFun := fun u => ⟨(h : MulAut V) u, hH h h.2 u u.2⟩
      invFun := fun u => ⟨((h⁻¹ : ↥H) : MulAut V) u, hH _ (h⁻¹).2 u u.2⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp) }
  map_one' := by ext u; rfl
  map_mul' := fun a b => by ext u; rfl

theorem card_modEq_fixed [Finite V] {p : ℕ} [Fact p.Prime] (H : Subgroup (MulAut V))
    (U : Subgroup V) (hH : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) (hp : IsPGroup p H) :
    Nat.card U ≡ Nat.card {u : ↥U // ∀ h ∈ H, (h : MulAut V) (u : V) = u} [MOD p] := by
  let _ : MulAction ↥H ↥U := MulAction.compHom ↥U (actHom H U hH)
  have h1 := hp.card_modEq_card_fixedPoints (α := ↥U)
  have h2 : Nat.card (MulAction.fixedPoints ↥H ↥U) =
      Nat.card {u : ↥U // ∀ h ∈ H, (h : MulAut V) (u : V) = u} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun u => ?_
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hu h hh
      exact congrArg Subtype.val (hu ⟨h, hh⟩)
    · intro hu g
      exact Subtype.ext (hu g g.2)
  rwa [h2] at h1

theorem false_of_four [Finite V] {K Ŝ : Subgroup (MulAut V)} {U : Subgroup V}
    (hcard : Nat.card U = 16) (hŜ2 : IsPGroup 2 Ŝ) (hŜU : ∀ s ∈ Ŝ, ∀ u ∈ U, s u ∈ U)
    (hKU : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U)
    (hsplit : ∀ v : V, ∃ u ∈ U, ∃ c ∈ fixV K, u * c = v)
    {x : MulAut V} (hxK : x ∈ K) (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1)
    (hfix : ∀ u ∈ U, (∀ s ∈ Ŝ, s u = u) → x u = u) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hnt : ∃ u ∈ U, x u ≠ u := by
    by_contra hall
    push Not at hall
    apply hx1
    ext v
    obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    rw [map_mul, hall u hu, (mem_fixV.1 hc) x hxK]
    rfl
  have hS := card_modEq_fixed Ŝ U hŜU hŜ2
  rw [hcard] at hS
  have hFpos : 0 < Nat.card {u : ↥U // ∀ h ∈ Ŝ, (h : MulAut V) (u : V) = u} :=
    Nat.card_pos_iff.2 ⟨⟨⟨1, fun h _ => by simp⟩⟩, inferInstance⟩
  have hF2 : 1 < Nat.card {u : ↥U // ∀ h ∈ Ŝ, (h : MulAut V) (u : V) = u} := by
    have : 16 % 2 = (Nat.card {u : ↥U // ∀ h ∈ Ŝ, (h : MulAut V) (u : V) = u}) % 2 := hS
    omega
  obtain ⟨⟨u, hu⟩, hne⟩ : ∃ f : {u : ↥U // ∀ h ∈ Ŝ, (h : MulAut V) (u : V) = u},
      f ≠ ⟨1, fun h _ => by simp⟩ := by
    have := Finite.one_lt_card_iff_nontrivial.1 hF2
    exact exists_ne _
  have hux : (x : MulAut V) (u : V) = u :=
    hfix u u.2 hu
  have hzp : ∀ h ∈ Subgroup.zpowers x, ∀ u ∈ U, h u ∈ U := fun h hh u hu =>
    hKU h ((Subgroup.zpowers_le.2 hxK) hh) u hu
  have hp5 : IsPGroup 5 ↥(Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hx5 hx1]
    norm_num
  have hX := card_modEq_fixed (Subgroup.zpowers x) U hzp hp5
  rw [hcard] at hX
  let C : Subgroup ↥U :=
    { carrier := {u | (x : MulAut V) (u : V) = (u : V)}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        have ha' : (x : MulAut V) (a : V) = (a : V) := ha
        have hb' : (x : MulAut V) (b : V) = (b : V) := hb
        show (x : MulAut V) (((a * b : ↥U)) : V) = (((a * b : ↥U)) : V)
        simp only [Subgroup.coe_mul, map_mul, ha', hb']
      inv_mem' := fun {a} ha => by
        have ha' : (x : MulAut V) (a : V) = (a : V) := ha
        show (x : MulAut V) (((a⁻¹ : ↥U)) : V) = (((a⁻¹ : ↥U)) : V)
        simp only [Subgroup.coe_inv, map_inv, ha'] }
  have hCard : Nat.card {u : ↥U // ∀ h ∈ Subgroup.zpowers x, (h : MulAut V) (u : V) = u} =
      Nat.card C := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun u => ?_
    constructor
    · intro hu
      exact hu x (Subgroup.mem_zpowers x)
    · intro hu h hh
      have hxs : x ∈ MulAction.stabilizer (MulAut V) (u : V) := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hu
      have := (Subgroup.zpowers_le.2 hxs) hh
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
  rw [hCard] at hX
  have hdvd : Nat.card C ∣ 16 := hcard ▸ Subgroup.card_subgroup_dvd_card C
  have hu1 : u ≠ 1 := fun h => hne (Subtype.ext h)
  have huC : u ∈ C := hux
  have hCle : Nat.card C ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
  have hC1 : Nat.card C = 1 ∨ Nat.card C = 16 := by
    have hmod : 16 % 5 = Nat.card C % 5 := hX
    generalize Nat.card C = c at hdvd hCle hmod ⊢
    interval_cases c <;> omega
  rcases hC1 with h1 | h16
  · rw [Subgroup.card_eq_one] at h1
    exact hu1 (by simpa [h1] using huC)
  · obtain ⟨v, hv, hxv⟩ := hnt
    have hCtop : C = ⊤ := Subgroup.card_eq_iff_eq_top C |>.1 (by rw [h16, hcard])
    have : (⟨v, hv⟩ : ↥U) ∈ C := by rw [hCtop]; exact Subgroup.mem_top _
    exact hxv this

end Four

section D7

variable {V : Type} [CommGroup V]

theorem alt7_isSimple : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)

theorem false_of_d7 {K Ū Ŝ : Subgroup (MulAut V)} {U : Subgroup V}
    (hKU : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U) (hD : D7Data K U) (hŪK : Ū ≤ K)
    (hŪ8 : Nat.card Ū = 8)
    (hŜK : ∀ s ∈ Ŝ, ∀ k ∈ K, s * k * s⁻¹ ∈ K)
    (hŜŪ : ∀ s ∈ Ŝ, ∀ k ∈ Ū, s * k * s⁻¹ ∈ Ū)
    (hŜU : ∀ s ∈ Ŝ, ∀ u ∈ U, s u ∈ U)
    {x : MulAut V} (hxK : x ∈ K) (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1)
    (hfix : ∀ u ∈ U, (∀ s ∈ Ŝ, s u = u) → x u = u) : False := by
  obtain ⟨π, β, hπs, hβe⟩ := hD
  have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alt7_isSimple
  have hπinj : Function.Injective π := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff π).1 h
    · exfalso
      obtain ⟨σ, hσ⟩ := hπs ⟨x, hxK⟩
      have h1 : σ ∈ π.ker := h ▸ Subgroup.mem_top σ
      rw [MonoidHom.mem_ker] at h1
      apply hx1
      have := congrArg (fun k : ↥K => (k : MulAut V)) (hσ.symm.trans h1)
      simpa using this
  let e : ↥(alternatingGroup (Fin 7)) ≃* ↥K := MulEquiv.ofBijective π ⟨hπinj, hπs⟩
  let P' : Subgroup ↥(alternatingGroup (Fin 7)) := (Ū.subgroupOf K).comap π
  let P : Subgroup (Perm (Fin 7)) := P'.map (alternatingGroup (Fin 7)).subtype
  have hPA : P ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hP8 : Nat.card P = 8 := by
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective]
    have h1 : Nat.card P' = Nat.card (Ū.subgroupOf K) :=
      Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun a => Iff.rfl))
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hŪK).toEquiv, hŪ8]
  obtain ⟨w, hwe, hw1, hwP, hw5, hw'⟩ := exists_fixed_four hPA hP8
  have hβ' : ∀ (σ : ↥(alternatingGroup (Fin 7))) (u : ↥U),
      ((β ⟨((π σ : ↥K) : MulAut V) (u : V), hKU _ (π σ).2 u u.2⟩ : ↥(G6.coreMod 7)) :
        G6.PermMod 7) = G6.permAct 7 (σ : Perm (Fin 7)) (β u) := fun σ u => hβe σ u _
  have hmemP : ∀ σ : ↥(alternatingGroup (Fin 7)), ((π σ : ↥K) : MulAut V) ∈ Ū →
      (σ : Perm (Fin 7)) ∈ P := fun σ hσ =>
    ⟨σ, Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 hσ), rfl⟩
  have hPmem : ∀ τ ∈ P, ∃ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) = τ ∧
      ((π σ : ↥K) : MulAut V) ∈ Ū := by
    rintro τ ⟨σ, hσ, rfl⟩
    exact ⟨σ, rfl, Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hσ)⟩
  let u₁ : ↥U := β.symm ⟨w, hwe⟩
  have hβu₁ : ((β u₁ : ↥(G6.coreMod 7)) : G6.PermMod 7) = w := by
    simp [u₁]
  have hcoe5 : ∀ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) ^ 5 = 1 ↔ σ ^ 5 = 1 := by
    intro σ
    constructor
    · intro h
      exact Subtype.ext (by simpa using h)
    · intro h
      simpa using congrArg Subtype.val h
  have hcoe1 : ∀ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) = 1 ↔ σ = 1 := by
    intro σ
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      rw [h]
      rfl
  have hSfix : ∀ s ∈ Ŝ, (s : MulAut V) (u₁ : V) = u₁ := by
    intro s hs
    have hs' : s⁻¹ ∈ Ŝ := Ŝ.inv_mem hs
    have hKt : ∀ σ : ↥(alternatingGroup (Fin 7)),
        s⁻¹ * ((π σ : ↥K) : MulAut V) * s ∈ K := by
      intro σ
      have := hŜK s⁻¹ hs' _ (π σ).2
      rwa [inv_inv] at this
    let tw : ↥(alternatingGroup (Fin 7)) → ↥(alternatingGroup (Fin 7)) :=
      fun σ => e.symm ⟨s⁻¹ * ((π σ : ↥K) : MulAut V) * s, hKt σ⟩
    have hπtw : ∀ σ, ((π (tw σ) : ↥K) : MulAut V) = s⁻¹ * ((π σ : ↥K) : MulAut V) * s := by
      intro σ
      have := e.apply_symm_apply ⟨s⁻¹ * ((π σ : ↥K) : MulAut V) * s, hKt σ⟩
      exact congrArg Subtype.val this
    have hconj : ∀ (σ : ↥(alternatingGroup (Fin 7))) (v : V),
        s (((π (tw σ) : ↥K) : MulAut V) v) = ((π σ : ↥K) : MulAut V) (s v) := by
      intro σ v
      rw [hπtw]
      simp [MulAut.mul_apply]
    have htwP : ∀ σ, ((π σ : ↥K) : MulAut V) ∈ Ū → ((π (tw σ) : ↥K) : MulAut V) ∈ Ū := by
      intro σ hσ
      rw [hπtw]
      have := hŜŪ s⁻¹ hs' _ hσ
      rwa [inv_inv] at this
    have htw5 : ∀ σ : ↥(alternatingGroup (Fin 7)), σ ^ 5 = 1 → tw σ ^ 5 = 1 := by
      intro σ h5
      apply hπinj
      apply Subtype.ext
      have h1 : ((π σ : ↥K) : MulAut V) ^ 5 = 1 := by
        have := congrArg (fun k : ↥K => (k : MulAut V)) (congrArg π h5)
        simpa using this
      have h2 := conj_pow (a := s⁻¹) (b := ((π σ : ↥K) : MulAut V)) (i := 5)
      rw [inv_inv, h1] at h2
      simp only [map_pow, Subgroup.coe_pow, hπtw, map_one, OneMemClass.coe_one]
      rw [h2]
      group
    have htw1 : ∀ σ : ↥(alternatingGroup (Fin 7)), σ ≠ 1 → tw σ ≠ 1 := by
      intro σ hσ h
      apply hσ
      apply hπinj
      apply Subtype.ext
      have h1 : s⁻¹ * ((π σ : ↥K) : MulAut V) * s = 1 := by
        rw [← hπtw, h]
        simp
      have h2 : ((π σ : ↥K) : MulAut V) = 1 := by
        have : ((π σ : ↥K) : MulAut V) = s * (s⁻¹ * ((π σ : ↥K) : MulAut V) * s) * s⁻¹ := by
          group
        rw [this, h1]
        group
      simp [h2]
    let a : ↥U := ⟨s (u₁ : V), hŜU s hs _ u₁.2⟩
    have hΦ : ∀ σ : ↥(alternatingGroup (Fin 7)),
        ((β ⟨((π σ : ↥K) : MulAut V) (a : V), hKU _ (π σ).2 a a.2⟩ : ↥(G6.coreMod 7)) :
          G6.PermMod 7) = G6.permAct 7 (σ : Perm (Fin 7)) (β a) := fun σ => hβ' σ a
    have hkey : ∀ σ : ↥(alternatingGroup (Fin 7)), ((π σ : ↥K) : MulAut V) (a : V) =
        s (((π (tw σ) : ↥K) : MulAut V) (u₁ : V)) := fun σ => (hconj σ u₁).symm
    have hfixu : ∀ σ : ↥(alternatingGroup (Fin 7)), G6.permAct 7 (σ : Perm (Fin 7)) w = w →
        ((π σ : ↥K) : MulAut V) (u₁ : V) = u₁ := by
      intro σ hσ
      have h1 := hβ' σ u₁
      rw [hβu₁, hσ] at h1
      have h2 : β ⟨((π σ : ↥K) : MulAut V) (u₁ : V), hKU _ (π σ).2 u₁ u₁.2⟩ = β u₁ :=
        Subtype.ext (h1.trans hβu₁.symm)
      exact congrArg Subtype.val (β.injective h2)
    have hŵ1 : (β a : G6.PermMod 7) ≠ 1 := by
      intro h
      have h1 : β a = 1 := Subtype.ext h
      have h2 : a = 1 := (map_eq_one_iff β β.injective).1 h1
      have h3 : s (u₁ : V) = 1 := congrArg Subtype.val h2
      have h4 : (u₁ : V) = 1 := by simpa using h3
      have h5 : u₁ = 1 := Subtype.ext h4
      apply hw1
      rw [← hβu₁, h5, map_one]
      rfl
    have hŵP : ∀ τ ∈ P, G6.permAct 7 τ (β a : G6.PermMod 7) = β a := by
      intro τ hτ
      obtain ⟨σ, rfl, hσ⟩ := hPmem τ hτ
      have h1 := hΦ σ
      have h2 : ((π σ : ↥K) : MulAut V) (a : V) = (a : V) := by
        rw [hkey σ, hfixu (tw σ) (hwP _ (hmemP (tw σ) (htwP σ hσ)))]
      have h3 : (⟨((π σ : ↥K) : MulAut V) (a : V), hKU _ (π σ).2 a a.2⟩ : ↥U) = a :=
        Subtype.ext h2
      rw [← h1, h3]
    have hŵ5 : ∀ σ : ↥(alternatingGroup (Fin 7)), σ ^ 5 = 1 → σ ≠ 1 →
        G6.permAct 7 (σ : Perm (Fin 7)) (β a : G6.PermMod 7) ≠ β a := by
      intro σ h5 h1 h
      have h1' := hΦ σ
      rw [h] at h1'
      have h2 : (⟨((π σ : ↥K) : MulAut V) (a : V), hKU _ (π σ).2 a a.2⟩ : ↥U) = a :=
        β.injective (Subtype.ext h1')
      have h3 : ((π σ : ↥K) : MulAut V) (a : V) = (a : V) := congrArg Subtype.val h2
      rw [hkey σ] at h3
      have h4 : ((π (tw σ) : ↥K) : MulAut V) (u₁ : V) = (u₁ : V) := (MulEquiv.injective s) h3
      have h6 := hβ' (tw σ) u₁
      have h7 : (⟨((π (tw σ) : ↥K) : MulAut V) (u₁ : V), hKU _ (π (tw σ)).2 u₁ u₁.2⟩ : ↥U) = u₁ :=
        Subtype.ext h4
      rw [h7, hβu₁] at h6
      exact hw5 (tw σ : Perm (Fin 7)) ((hcoe5 _).2 (htw5 σ h5))
        (fun h8 => htw1 σ h1 ((hcoe1 _).1 h8)) h6.symm
    by_cases hŵw : (β a : G6.PermMod 7) = w
    · have : a = u₁ := β.injective (Subtype.ext (hŵw.trans hβu₁.symm))
      exact congrArg Subtype.val this
    · exfalso
      obtain ⟨τ, hτA, hτ5, hτ1, hτf⟩ := hw' (β a) (β a).2 hŵ1 hŵw hŵP
      exact hŵ5 ⟨τ, hτA⟩ ((hcoe5 ⟨τ, hτA⟩).1 hτ5) (fun h => hτ1 ((hcoe1 ⟨τ, hτA⟩).2 h)) hτf
  have hxu : (x : MulAut V) (u₁ : V) = u₁ := hfix (u₁ : V) u₁.2 hSfix
  obtain ⟨σx, hσx⟩ := hπs ⟨x, hxK⟩
  have hσx' : ((π σx : ↥K) : MulAut V) = x := congrArg Subtype.val hσx
  have hσx5 : σx ^ 5 = 1 := by
    apply hπinj
    apply Subtype.ext
    simp [hσx', hx5]
  have hσx1 : σx ≠ 1 := by
    intro h
    apply hx1
    rw [← hσx', h]
    simp
  have h1 := hβ' σx u₁
  have h2' : ((π σx : ↥K) : MulAut V) (u₁ : V) = u₁ := by rw [hσx']; exact hxu
  have h2 : (⟨((π σx : ↥K) : MulAut V) (u₁ : V), hKU _ (π σx).2 u₁ u₁.2⟩ : ↥U) = u₁ :=
    Subtype.ext h2'
  rw [h2, hβu₁] at h1
  exact hw5 (σx : Perm (Fin 7)) ((hcoe5 _).2 hσx5) (fun h => hσx1 ((hcoe1 _).1 h)) h1.symm

end D7

section Config

variable {V : Type} [CommGroup V]

theorem false_of_a7Config [Finite V] {K Ū Ŝ : Subgroup (MulAut V)} {U : Subgroup V}
    (hKU : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U) (hsplit : IsIntDirect U (fixV K) ⊤)
    (hmod : AlternatingNatural K U ⊥ 7 ∨ A7Four K U ⊥)
    (hŪK : Ū ≤ K) (hŪ8 : Nat.card Ū = 8) (hŜ2 : IsPGroup 2 Ŝ)
    (hŜK : ∀ s ∈ Ŝ, ∀ k ∈ K, s * k * s⁻¹ ∈ K)
    (hŜŪ : ∀ s ∈ Ŝ, ∀ k ∈ Ū, s * k * s⁻¹ ∈ Ū)
    (hŜU : ∀ s ∈ Ŝ, ∀ u ∈ U, s u ∈ U)
    {x : MulAut V} (hxK : x ∈ K) (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1)
    (hfix : ∀ u ∈ U, (∀ s ∈ Ŝ, s u = u) → x u = u) : False := by
  rcases hmod with h | h
  · exact false_of_d7 hKU (D7Data.of_alternatingNatural h) hŪK hŪ8 hŜK hŜŪ hŜU hxK hx5 hx1 hfix
  · have hsp : ∀ v : V, ∃ u ∈ U, ∃ c ∈ fixV K, u * c = v := by
      intro v
      have hv : v ∈ U ⊔ fixV K := by
        rw [hsplit.1]
        exact Subgroup.mem_top v
      obtain ⟨u, hu, c, hc, huc⟩ := Subgroup.mem_sup.1 hv
      exact ⟨u, hu, c, hc, huc⟩
    exact false_of_four (card_of_a7Four h) hŜ2 hŜU hKU hsp hxK hx5 hx1 hfix

end Config

section Equiv

variable {V : Type} [CommGroup V]

theorem equiv_alt7_of_modData {K : Subgroup (MulAut V)} {U : Subgroup V} (hK : K ≠ ⊥)
    (h : AlternatingNatural K U ⊥ 7 ∨ A7Four K U ⊥) :
    Nonempty (↥K ≃* alternatingGroup (Fin 7)) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alt7_isSimple
  have hπ : ∃ π : ↥(alternatingGroup (Fin 7)) →* ↥K, Function.Surjective π := by
    rcases h with ⟨π, hπ⟩ | ⟨α, π, hπ⟩
    · exact ⟨π, hπ.1⟩
    · exact ⟨π, hπ.1⟩
  obtain ⟨π, hπs⟩ := hπ
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hK
  have hinj : Function.Injective π := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff π).1 h
    · exfalso
      obtain ⟨k, hk⟩ := exists_ne (1 : ↥K)
      obtain ⟨σ, rfl⟩ := hπs k
      have h1 : σ ∈ π.ker := h ▸ Subgroup.mem_top σ
      exact hk (MonoidHom.mem_ker.1 h1)
  exact ⟨(MulEquiv.ofBijective π ⟨hinj, hπs⟩).symm⟩

end Equiv

end CFSG.Quasithin.QA26
