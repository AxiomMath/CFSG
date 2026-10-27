module

public import CFSG.RankThree.GF2n.Smith81.Lin31Two

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

private theorem p31_modules (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) :
    ∀ v ∈ Q, v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂) := by
  obtain ⟨V₁', V₂', hS', -, h31'⟩ := lin31Statement_holds G M Q Z B n V₁ V₂ hb hc hS (by omega)
  intro v hv hv1
  rw [h31' v hv hv1]
  rcases linPair_unique hc hS hS' hn with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
  · rw [e1, e2]
    exact or_comm

private theorem inf_QB_eq_V₁ (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) {Y : Subgroup G} (hY : Ctx M Q Z Y)
    (hYV : Y ≤ V₁) : Q ⊓ QB Y = V₁ := by
  obtain ⟨-, hV₁Q, -, -, -, -, -, -, hcard₁, -⟩ := hS.basic
  have hmod := linModuleStatement_holds G M Q Z B n V₁ V₂ hb hc hS hn Y hY.conj hY.ne
  have hle : V₁ ≤ Q ⊓ QB Y := le_inf hV₁Q (hmod.1 hYV)
  have hcard := hY.card_inf_QB_le (LinSetup.width hc.hyp hS)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard₁]; exact hcard)).symm

private theorem uniq_over_xbar_core (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) {g : G} (hY : Ctx M Q Z (conjSubgroup g⁻¹ Z))
    (hYV : conjSubgroup g⁻¹ Z ≤ V₁) {x x'' : G} (hxcl : InZClass Z x)
    (hx''cl : InZClass Z x'') (hxQ : x ∉ Q) (hx''Q : x'' ∉ Q) (hxA : x ∈ conjSubgroup g Q)
    (hx''A : x'' ∈ conjSubgroup g Q) (hxx'' : x⁻¹ * x'' ∈ Q) :
    x⁻¹ * x'' ∈ conjSubgroup g Z := by
  have H := hc.hyp
  obtain ⟨-, -, -, -, hint, -, -, -, -, -⟩ := hS.basic
  have h31 := p31_modules hb hc hS hn
  have hQY := inf_QB_eq_V₁ hb hc hS hn hY hYV
  rw [QB_conj_eq H g⁻¹] at hQY
  have hxQ' : g⁻¹ * x * g ∈ Q := mem_conjSubgroup.mp hxA
  have hx''Q' : g⁻¹ * x'' * g ∈ Q := mem_conjSubgroup.mp hx''A
  have hx1 : x ≠ 1 := fun h => hxQ (h ▸ Q.one_mem)
  have hx''1 : x'' ≠ 1 := fun h => hx''Q (h ▸ Q.one_mem)
  have hx'1 : g⁻¹ * x * g ≠ 1 := fun h => hx1 (by
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hx''1' : g⁻¹ * x'' * g ≠ 1 := fun h => hx''1 (by
    have : x'' = g * (g⁻¹ * x'' * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hx'cl : InZClass Z (g⁻¹ * x * g) := by
    have := (inZClass_conj_iff (Z := Z) (v := x) g⁻¹).mpr hxcl
    simpa using this
  have hx''cl' : InZClass Z (g⁻¹ * x'' * g) := by
    have := (inZClass_conj_iff (Z := Z) (v := x'') g⁻¹).mpr hx''cl
    simpa using this
  have hnot : ∀ y : G, y ∉ Q → g⁻¹ * y * g ∉ V₁ := by
    intro y hy hyV
    apply hy
    rw [← hQY] at hyV
    have h2 := mem_conjSubgroup.mp hyV.2
    have e : (g⁻¹)⁻¹ * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at h2
  have hx'V₂ : g⁻¹ * x * g ∈ V₂ := by
    rcases (h31 _ hxQ' hx'1).mp hx'cl with h | h
    · exact absurd h (hnot x hxQ)
    · exact h
  have hx''V₂ : g⁻¹ * x'' * g ∈ V₂ := by
    rcases (h31 _ hx''Q' hx''1').mp hx''cl' with h | h
    · exact absurd h (hnot x'' hx''Q)
    · exact h
  have e : g⁻¹ * (x⁻¹ * x'') * g = (g⁻¹ * x * g)⁻¹ * (g⁻¹ * x'' * g) := by group
  have hvV₂ : g⁻¹ * (x⁻¹ * x'') * g ∈ V₂ := by
    rw [e]
    exact V₂.mul_mem (V₂.inv_mem hx'V₂) hx''V₂
  have hvV₁ : g⁻¹ * (x⁻¹ * x'') * g ∈ V₁ := by
    rw [← hQY]
    refine Subgroup.mem_inf.mpr ⟨?_, mem_conjSubgroup.mpr ?_⟩
    · rw [e]
      exact Q.mul_mem (Q.inv_mem hxQ') hx''Q'
    · have e' : (g⁻¹)⁻¹ * (g⁻¹ * (x⁻¹ * x'') * g) * g⁻¹ = x⁻¹ * x'' := by group
      rw [e']
      exact hxx''
  have hvZ : g⁻¹ * (x⁻¹ * x'') * g ∈ Z := by
    rw [← hint]
    exact ⟨hvV₁, hvV₂⟩
  exact mem_conjSubgroup.mpr hvZ

theorem uniq_over_xbar (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) {A : Subgroup G} (hA : Ctx M Q Z A)
    {x x'' : G} (hxcl : InZClass Z x) (hx''cl : InZClass Z x'')
    (hxQ : x ∉ Q) (hx''Q : x'' ∉ Q) (hxA : x ∈ QB A) (hx''A : x'' ∈ QB A)
    (hxx'' : x⁻¹ * x'' ∈ Q) : x⁻¹ * x'' ∈ A := by
  have H := hc.hyp
  obtain ⟨g, rfl⟩ := hA.conj
  rw [QB_conj_eq H g] at hxA hx''A
  have hZA : Z ≤ conjSubgroup g Q := by
    have := (Ctx.Z_le_QB hA).1
    rwa [QB_conj_eq H g] at this
  have hYQ : conjSubgroup g⁻¹ Z ≤ Q := by
    intro y hy
    rw [mem_conjSubgroup] at hy
    have h1 := mem_conjSubgroup.mp (hZA hy)
    have e : g⁻¹ * ((g⁻¹)⁻¹ * y * g⁻¹) * g = y := by group
    rwa [e] at h1
  have hYZ : conjSubgroup g⁻¹ Z ≠ Z := by
    intro h
    apply hA.ne
    calc conjSubgroup g Z = conjSubgroup g (conjSubgroup g⁻¹ Z) := by rw [h]
      _ = Z := conjSubgroup_conj_inv g Z
  have hY : Ctx M Q Z (conjSubgroup g⁻¹ Z) := ⟨H, ⟨g⁻¹, rfl⟩, hYQ, hYZ⟩
  rcases hS.conj_le_V hc hn hY with hYV | hYV
  · exact uniq_over_xbar_core hb hc hS hn hY hYV hxcl hx''cl hxQ hx''Q hxA hx''A hxx''
  · exact uniq_over_xbar_core hb hc hS.symm hn hY hYV hxcl hx''cl hxQ hx''Q hxA hx''A hxx''

private theorem commutator_mul_left_of_comm {p p' x : G} (h1 : p * ⁅p', x⁆ = ⁅p', x⁆ * p)
    (h2 : ⁅p, x⁆ * ⁅p', x⁆ = ⁅p', x⁆ * ⁅p, x⁆) : ⁅p * p', x⁆ = ⁅p, x⁆ * ⁅p', x⁆ := by
  have e : ⁅p * p', x⁆ = (p * ⁅p', x⁆ * p⁻¹) * ⁅p, x⁆ := by
    simp only [commutatorElement_def]; group
  have h3 : p * ⁅p', x⁆ * p⁻¹ = ⁅p', x⁆ := by rw [h1]; group
  rw [e, h3]
  exact h2.symm

theorem exists_conj_mul_eq (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) {A : Subgroup G} (hA : Ctx M Q Z A)
    (hAV : A ≤ V₁) {x : G} (hxM : x ∈ M) (hxQ : x ∉ Q) (hxA : x ∈ QB A) :
    ∀ a ∈ A, ∃ p ∈ V₁, p * x * p⁻¹ = x * a := by
  have H := hc.hyp
  have hAc : IsZConjugate Z A := hA.conj
  have hVA : V₁ ≤ QB A :=
    (linModuleStatement_holds G M Q Z B n V₁ V₂ hb hc hS hn A hAc hA.ne).1 hAV
  have hcommA : ∀ p ∈ V₁, ⁅p, x⁆ ∈ A := fun p hp => hA.comm_QB_le_B (hVA hp) hxA
  have hxcomm : ∀ a ∈ A, a * x = x * a := fun a ha => IsZConjugate.central_QB H hAc ha hxA
  let f : ↥V₁ →* G := MonoidHom.mk' (fun p => ⁅(p : G), x⁆) fun p p' => by
    have hcp : ⁅(p : G), x⁆ ∈ V₁ := hAV (hcommA p p.2)
    have hcp' : ⁅(p' : G), x⁆ ∈ V₁ := hAV (hcommA p' p'.2)
    exact commutator_mul_left_of_comm (LinSetup.comm_eq_one_V₁ hc hS hn p.2 hcp')
      (LinSetup.comm_eq_one_V₁ hc hS hn hcp hcp')
  have hf : ∀ p : ↥V₁, f p = ⁅(p : G), x⁆ := fun p => rfl
  have hfA : f.range ≤ A := by
    rintro _ ⟨p, rfl⟩
    rw [hf]
    exact hcommA p p.2
  have hpow : ∀ v ∈ V₁, ∀ k : ℤ, ⁅v, x ^ k⁆ = ⁅v, x⁆ ^ k := by
    intro v hv k
    have hcx : Commute ⁅v, x⁆ x := hxcomm _ (hcommA v hv)
    have h1 : v * x * v⁻¹ = ⁅v, x⁆ * x := by simp only [commutatorElement_def]; group
    calc ⁅v, x ^ k⁆ = (v * x * v⁻¹) ^ k * (x ^ k)⁻¹ := by
          rw [commutatorElement_def, conj_zpow]
      _ = (⁅v, x⁆ * x) ^ k * (x ^ k)⁻¹ := by rw [h1]
      _ = ⁅v, x⁆ ^ k := by rw [hcx.mul_zpow k, mul_inv_cancel_right]
  have hle₀ : ⁅V₁, Subgroup.zpowers x⁆ ≤ f.range := by
    rw [Subgroup.commutator_le]
    intro v hv s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    rw [hpow v hv k]
    exact f.range.zpow_mem (MonoidHom.mem_range.mpr ⟨⟨v, hv⟩, rfl⟩) k
  have hxL : x ∈ LB M Q A := Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hxA, hxM⟩)
  have hAZ := (LinSetup.transv_of_conj_le_V₁ hc hS hn hA hAV hxL hxQ).1
  have hsup : A ⊔ Z ≤ f.range ⊔ Z := by
    rw [← hAZ]
    exact sup_le_sup_right hle₀ Z
  have hZA : Z ⊓ A = ⊥ := hA.inf_eq_bot
  have hZcomm : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a := fun a ha z hz =>
    (Z_central H hz (hA.le ha)).symm
  have hbotA : A ⊓ Z = ⊥ := by rw [inf_comm]; exact hZA
  have hbot₀ : f.range ⊓ Z = ⊥ :=
    le_antisymm ((inf_le_inf_right Z hfA).trans hbotA.le) bot_le
  have hcardA : Nat.card ↥(A ⊔ Z) = Nat.card A * Nat.card Z :=
    card_sup_of_comm_inf_bot hZcomm hbotA
  have hcard₀ : Nat.card ↥(f.range ⊔ Z) = Nat.card f.range * Nat.card Z :=
    card_sup_of_comm_inf_bot (fun a ha z hz => hZcomm a (hfA ha) z hz) hbot₀
  have hcardle : Nat.card A ≤ Nat.card f.range := by
    have h1 : Nat.card ↥(A ⊔ Z) ≤ Nat.card ↥(f.range ⊔ Z) := Subgroup.card_le_of_le hsup
    rw [hcardA, hcard₀] at h1
    exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  have hrange : f.range = A := Subgroup.eq_of_le_of_card_ge hfA hcardle
  intro a ha
  obtain ⟨⟨p, hp⟩, hpa⟩ := MonoidHom.mem_range.mp (hrange.symm ▸ ha)
  refine ⟨p, hp, ?_⟩
  have h1 : ⁅p, x⁆ = a := hpa
  calc p * x * p⁻¹ = ⁅p, x⁆ * x := by simp only [commutatorElement_def]; group
    _ = a * x := by rw [h1]
    _ = x * a := hxcomm a ha

end CFSG.RankThree.GF2n.Smith81
