module

public import CFSG.Quasithin.H13.A7FiveFixed
public import CFSG.Quasithin.Background.B4ModelsWitness
public import CFSG.Quasithin.Background.G64SymSec
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin Equiv

@[expose] def d5Fix (s : Finset (Perm (Fin 5))) : Finset (Fin 5 → ZMod 2) :=
  Finset.univ.filter fun m => ∑ i, m i = 0 ∧ ∀ γ ∈ s, ∀ i, m (γ⁻¹ i) = m i

theorem card_d5Fix_one : ∀ γ : Perm (Fin 5), γ * γ = 1 → γ ≠ 1 → Perm.sign γ = 1 →
    (d5Fix {γ}).card ≤ 4 := by
  decide +kernel

theorem card_d5Fix_two : ∀ γ δ : Perm (Fin 5), γ * γ = 1 → δ * δ = 1 → γ ≠ 1 → δ ≠ 1 →
    γ ≠ δ → γ * δ = δ * γ → Perm.sign γ = 1 → Perm.sign δ = 1 → (d5Fix {γ, δ}).card ≤ 2 := by
  decide +kernel

section Transfer

variable {V : Type} [CommGroup V]

@[expose] noncomputable def d5Rep :
    ↥(FFModel.altDn 5).sec ⧸ (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec ≃
      ↥(FFModel.altDn 5).sec :=
  (Equiv.ofBijective _ ⟨A7.altDn_five_mk_injective, QuotientGroup.mk_surjective⟩).symm

theorem mk_d5Rep (q : ↥(FFModel.altDn 5).sec ⧸
    (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) :
    (QuotientGroup.mk (d5Rep q) : ↥(FFModel.altDn 5).sec ⧸
      (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) = q :=
  (Equiv.ofBijective _ ⟨A7.altDn_five_mk_injective, QuotientGroup.mk_surjective⟩).apply_symm_apply q

@[expose] def d5Vec (m : ↥(FFModel.altDn 5).sec) : Fin 5 → ZMod 2 :=
  Multiplicative.toAdd (show G6.PermMod 5 from m.1)

theorem d5Vec_injective : Function.Injective d5Vec := fun _ _ h =>
  Subtype.ext (Multiplicative.toAdd.injective h)

theorem card_le_d5Fix {K : Subgroup (MulAut V)} {U W : Subgroup V}
    {π : ↥(alternatingGroup (Fin 5)) →* ↥K} (h : (FFModel.altDn 5).RealizesVia K U ⊥ π)
    (hWU : W ≤ U) (s : Finset (Perm (Fin 5))) (hs : ∀ γ ∈ s, γ ∈ alternatingGroup (Fin 5))
    (hW : ∀ γ : ↥(alternatingGroup (Fin 5)), (γ : Perm (Fin 5)) ∈ s →
      ∀ w ∈ W, ((π γ : ↥K) : MulAut V) w = w) :
    Nat.card W ≤ (d5Fix s).card := by
  obtain ⟨-, -, -, hU, -, -, -, β, -, hβk, hβe⟩ := h
  have hmem : ∀ w : ↥W, d5Vec (d5Rep (β ⟨w, hWU w.2⟩)) ∈ d5Fix s := by
    intro w
    rw [d5Fix, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (d5Rep (β ⟨w, hWU w.2⟩)).2, fun γ hγ i => ?_⟩
    set u : ↥U := ⟨w, hWU w.2⟩ with hu
    set γ' : ↥(alternatingGroup (Fin 5)) := ⟨γ, hs γ hγ⟩
    have hfix : ((π γ' : ↥K) : MulAut V) (u : V) = u := hW γ' hγ w w.2
    have hu' : ((π γ' : ↥K) : MulAut V) (u : V) ∈ U := hU (π γ') u u.2
    set m := d5Rep (β u) with hm
    have hm' : (FFModel.altDn 5).act γ' (m : (FFModel.altDn 5).Amb) ∈
        (FFModel.altDn 5).sec := G6.permAct_mem_coreMod γ m.2
    have h1 := hβe γ' u m hu' hm' (mk_d5Rep (β u)).symm
    have h2 : (⟨((π γ' : ↥K) : MulAut V) (u : V), hu'⟩ : ↥U) = u := Subtype.ext hfix
    have h1' : (QuotientGroup.mk m : ↥(FFModel.altDn 5).sec ⧸
        (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) =
        QuotientGroup.mk ⟨(FFModel.altDn 5).act γ' (m : (FFModel.altDn 5).Amb), hm'⟩ :=
      (mk_d5Rep (β u)).trans ((congrArg β h2).symm.trans h1)
    have h3 := congrArg (fun x : ↥(FFModel.altDn 5).sec => d5Vec x i)
      (A7.altDn_five_mk_injective h1')
    exact h3.symm
  let f : ↥W → ↥(d5Fix s) := fun w => ⟨d5Vec (d5Rep (β ⟨w, hWU w.2⟩)), hmem w⟩
  have hf : Function.Injective f := by
    intro w₁ w₂ h12
    have h0 : d5Vec (d5Rep (β ⟨w₁, hWU w₁.2⟩)) = d5Vec (d5Rep (β ⟨w₂, hWU w₂.2⟩)) := by
      have := congrArg Subtype.val h12
      exact this
    have h2 : β ⟨w₁, hWU w₁.2⟩ = β ⟨w₂, hWU w₂.2⟩ := d5Rep.injective (d5Vec_injective h0)
    have h3 : β (⟨w₁, hWU w₁.2⟩ * (⟨w₂, hWU w₂.2⟩ : ↥U)⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    have h4 := (hβk _).mp h3
    rw [Subgroup.mem_bot] at h4
    apply Subtype.ext
    have h5 : (w₁ : V) * (w₂ : V)⁻¹ = 1 := h4
    exact mul_inv_eq_one.mp h5
  calc Nat.card W ≤ Nat.card ↥(d5Fix s) := Nat.card_le_card_of_injective f hf
    _ = (d5Fix s).card := Nat.card_eq_finsetCard _

theorem sixteen_le_card_of_altDn_five [Finite V] {K : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(alternatingGroup (Fin 5)) →* ↥K} (h : (FFModel.altDn 5).RealizesVia K U Z π) :
    16 ≤ Nat.card U := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, -, -⟩ := h
  have h1 : Nat.card (↥(FFModel.altDn 5).sec ⧸
      (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) = 16 := by
    rw [Nat.card_congr d5Rep]
    exact Explicit.card_coreMod (n := 5) (by norm_num)
  rw [← h1]
  exact Nat.card_le_card_of_surjective β hβs

end Transfer

theorem card_mul_card_fixV_lt_of_altDn_five {V : Type} [CommGroup V] [Finite V]
    {K : Subgroup (MulAut V)} (hD : IsIntDirect (commV K) (fixV K) ⊤)
    (hR : AlternatingNatural K (commV K) ⊥ 5) {A : Subgroup (MulAut V)} (hAK : A ≤ K)
    (hA : A ≠ ⊥) (hA2 : IsElemAbelian2 A) : Nat.card A * Nat.card (fixV A) < Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπ⟩ : ∃ π : ↥(alternatingGroup (Fin 5)) →* ↥K,
      (FFModel.altDn 5).RealizesVia K (commV K) ⊥ π := hR
  have hπi : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (G64.altDn_faithful (by norm_num)) hπ
  have hπs : Function.Surjective π := hπ.1
  set U := commV K with hUdef
  set W := fixV A with hWdef
  have hK60 : Nat.card K = 60 := by
    rw [← Nat.card_congr (Equiv.ofBijective π ⟨hπi, hπs⟩)]
    exact SteinbergCB.nat_card_alternating_five
  have hA4 : Nat.card A ≤ 4 := by
    have hp : IsPGroup 2 ↥A := fun a =>
      ⟨1, Subtype.ext (by simpa using hA2.2 (a : MulAut V) a.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have hdvd : Nat.card A ∣ 60 := hK60 ▸ Subgroup.card_dvd_of_le hAK
    rw [hk] at hdvd ⊢
    have hk2 : k ≤ 2 := by
      by_contra hk3
      have h8 : 2 ^ 3 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
      have := h8.trans hdvd
      norm_num at this
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  have hCW : fixV K ≤ W := B1.fixV_le_fixV hAK
  have hUW : U ⊔ W = ⊤ := eq_top_iff.mpr (hD.1 ▸ sup_le_sup_left hCW U)
  have hidx : W.index = W.relIndex U := by
    rw [← Subgroup.relIndex_top_right, ← hUW, Subgroup.relIndex_sup_right]
  have hV : W.relIndex U * Nat.card W = Nat.card V := by
    rw [← hidx]
    exact Subgroup.index_mul_card W
  have hU : W.relIndex U * Nat.card ↥(W ⊓ U) = Nat.card U := Subgroup.relIndex_mul_card W U
  have h16 : 16 ≤ Nat.card U := sixteen_le_card_of_altDn_five hπ
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hfixW : ∀ a ∈ A, ∀ w ∈ W ⊓ U, a w = w := fun a ha w hw => hw.1 a ha
  have hsign : ∀ γ : ↥(alternatingGroup (Fin 5)), Perm.sign (γ : Perm (Fin 5)) = 1 :=
    fun γ => Equiv.Perm.mem_alternatingGroup.mp γ.2
  have hpre : ∀ σ ∈ A, ∃ γ : ↥(alternatingGroup (Fin 5)), ((π γ : ↥K) : MulAut V) = σ := by
    intro σ hσ
    obtain ⟨γ, hγ⟩ := hπs ⟨σ, hAK hσ⟩
    exact ⟨γ, congrArg Subtype.val hγ⟩
  have hinv : ∀ γ : ↥(alternatingGroup (Fin 5)), ((π γ : ↥K) : MulAut V) ∈ A →
      (γ : Perm (Fin 5)) * γ = 1 := by
    intro γ hγ
    have h1 : π (γ * γ) = 1 := by
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, ← pow_two]
      exact hA2.2 _ hγ
    rw [← map_one π] at h1
    exact congrArg Subtype.val (hπi h1)
  have hne1 : ∀ γ : ↥(alternatingGroup (Fin 5)), ((π γ : ↥K) : MulAut V) ≠ 1 →
      (γ : Perm (Fin 5)) ≠ 1 := by
    intro γ hγ h1
    apply hγ
    have : γ = 1 := Subtype.ext h1
    rw [this, map_one]
    rfl
  obtain ⟨⟨σ, hσA⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have hσ1' : σ ≠ 1 := fun h => hσ1 (Subtype.ext h)
  obtain ⟨γ, hγ⟩ := hpre σ hσA
  have hγA : ((π γ : ↥K) : MulAut V) ∈ A := hγ ▸ hσA
  have hc4 : Nat.card ↥(W ⊓ U) ≤ 4 := by
    refine (card_le_d5Fix hπ inf_le_right {(γ : Perm (Fin 5))} ?_ ?_).trans
      (card_d5Fix_one _ (hinv γ hγA) (hne1 γ (hγ ▸ hσ1')) (hsign γ))
    · intro δ hδ
      rw [Finset.mem_singleton] at hδ
      rw [hδ]
      exact γ.2
    · intro δ hδ w hw
      rw [Finset.mem_singleton] at hδ
      have : δ = γ := Subtype.ext hδ
      rw [this]
      exact hfixW _ hγA w hw
  by_cases hA2' : Nat.card A ≤ 2
  · have hr : 4 ≤ W.relIndex U := by nlinarith
    calc Nat.card A * Nat.card W ≤ 2 * Nat.card W := Nat.mul_le_mul_right _ hA2'
      _ < W.relIndex U * Nat.card W := by nlinarith
      _ = Nat.card V := hV
  ·
    have : Fintype ↥A := Fintype.ofFinite _
    have h3 : 2 < Fintype.card ↥A := by rw [← Nat.card_eq_fintype_card]; omega
    obtain ⟨τ, hτA, hτ1, hτσ⟩ : ∃ τ ∈ A, τ ≠ 1 ∧ τ ≠ σ := by
      obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h3
      by_contra hno
      push Not at hno
      have hall : ∀ x : ↥A, (x : MulAut V) = 1 ∨ (x : MulAut V) = σ := by
        intro x
        by_cases hx : (x : MulAut V) = 1
        · exact Or.inl hx
        · exact Or.inr (hno x x.2 hx)
      rcases hall a with ha | ha <;> rcases hall b with hb | hb <;> rcases hall c with hc | hc
      all_goals first
        | exact hab (Subtype.ext (ha.trans hb.symm))
        | exact hac (Subtype.ext (ha.trans hc.symm))
        | exact hbc (Subtype.ext (hb.trans hc.symm))
    obtain ⟨δ, hδ⟩ := hpre τ hτA
    have hδA : ((π δ : ↥K) : MulAut V) ∈ A := hδ ▸ hτA
    have hγδ : (γ : Perm (Fin 5)) ≠ δ := by
      intro h
      apply hτσ
      rw [← hδ, ← hγ, show δ = γ from (Subtype.ext h).symm]
    have hcomm : (γ : Perm (Fin 5)) * δ = δ * γ := by
      have h1 : π (γ * δ) = π (δ * γ) := by
        apply Subtype.ext
        rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
        exact hA2.1 _ hγA _ hδA
      exact congrArg Subtype.val (hπi h1)
    have hc2 : Nat.card ↥(W ⊓ U) ≤ 2 := by
      refine (card_le_d5Fix hπ inf_le_right {(γ : Perm (Fin 5)), (δ : Perm (Fin 5))} ?_ ?_).trans
        (card_d5Fix_two _ _ (hinv γ hγA) (hinv δ hδA) (hne1 γ (hγ ▸ hσ1'))
          (hne1 δ (hδ ▸ hτ1)) hγδ hcomm (hsign γ) (hsign δ))
      · intro ε hε
        rw [Finset.mem_insert, Finset.mem_singleton] at hε
        rcases hε with rfl | rfl
        · exact γ.2
        · exact δ.2
      · intro ε hε w hw
        rw [Finset.mem_insert, Finset.mem_singleton] at hε
        rcases hε with h | h
        · rw [show ε = γ from Subtype.ext h]
          exact hfixW _ hγA w hw
        · rw [show ε = δ from Subtype.ext h]
          exact hfixW _ hδA w hw
    have hr : 8 ≤ W.relIndex U := by nlinarith
    calc Nat.card A * Nat.card W ≤ 4 * Nat.card W := Nat.mul_le_mul_right _ hA4
      _ < W.relIndex U * Nat.card W := by nlinarith
      _ = Nat.card V := hV

end CFSG.Quasithin.H13
