module

public import CFSG.LocalAnalysis.StandardType.GGForkCellsDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflCartan
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section ForkData

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type*}
  [AddCommGroup V] [Module (ZMod p) V]
variable {Λ : Type*} [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ} {h : Λ → V}
  {α : Λ → Module.Dual (ZMod p) V} {ha : V} {αa : Module.Dual (ZMod p) V}
  {φ : Λ → MulAut ↥Bs} {φa : MulAut ↥Bs}

private theorem ggFork_inv_eq (ι : Additive ↥Bs ≃+ V) {x : V} {f : Module.Dual (ZMod p) V}
    (hfx : f x = 2) {ψ : MulAut ↥Bs} (hψ : ∀ w, ggLin (p := p) ι ψ w = w - f w • x) :
    ψ⁻¹ = ψ := by
  apply ggLin_injective (p := p) ι
  rw [map_inv, ggLin_eq_reflection ι hfx hψ, reflection_inv]

private theorem ggFork_indep_three (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hbc : b ≠ c) : LinearIndependent (ZMod p) ![ha, h b, h c] := by
  have hinj : Function.Injective (fun i : Fin 3 => ![none, some (b : Λ), some c] i) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hli := hind.comp (fun i : Fin 3 => ![none, some (b : Λ), some c] i) hinj
  have hfun : (ggOptFam ha h ∘ fun i : Fin 3 => ![none, some (b : Λ), some c] i) =
      ![ha, h b, h c] := by
    funext i
    fin_cases i <;> rfl
  rwa [hfun] at hli

private theorem ggFork_indep_four (hind : LinearIndependent (ZMod p) (ggOptFam ha h)) {d : Λ}
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    LinearIndependent (ZMod p) ![ha, h b, h c, h d] := by
  have hinj : Function.Injective (fun i : Fin 4 => ![none, some (b : Λ), some c, some d] i) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hli := hind.comp (fun i : Fin 4 => ![none, some (b : Λ), some c, some d] i) hinj
  have hfun : (ggOptFam ha h ∘ fun i : Fin 4 => ![none, some (b : Λ), some c, some d] i) =
      ![ha, h b, h c, h d] := by
    funext i
    fin_cases i <;> rfl
  rwa [hfun] at hli

private theorem ggFork_three_coeffs (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hbc : b ≠ c) {c₀ c₁ c₂ : ZMod p} (hrel : c₀ • ha + c₁ • h b + c₂ • h c = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  have h3 := ggFork_indep_three (p := p) hind hbc
  have hg : (∑ i : Fin 3, ![c₀, c₁, c₂] i • ![ha, h b, h c] i) = 0 := by
    rw [Fin.sum_univ_three]
    simpa using hrel
  have h := (Fintype.linearIndependent_iff.mp h3) ![c₀, c₁, c₂] hg
  exact ⟨h 0, h 1, h 2⟩

private theorem ggFork_four_coeffs (hind : LinearIndependent (ZMod p) (ggOptFam ha h)) {d : Λ}
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {c₀ c₁ c₂ c₃ : ZMod p}
    (hrel : c₀ • ha + c₁ • h b + c₂ • h c + c₃ • h d = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  have h4 := ggFork_indep_four (p := p) hind hbc hbd hcd
  have hg : (∑ i : Fin 4, ![c₀, c₁, c₂, c₃] i • ![ha, h b, h c, h d] i) = 0 := by
    rw [Fin.sum_univ_four]
    simpa using hrel
  have h := (Fintype.linearIndependent_iff.mp h4) ![c₀, c₁, c₂, c₃] hg
  exact ⟨h 0, h 1, h 2, h 3⟩

private theorem ggFork_indep_ht_hc (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hbc : b ≠ c) :
    LinearIndependent (ZMod p) ![ha + h c + (1 - α b ha) • h b, h c] := by
  rw [LinearIndependent.pair_iff]
  intro r s hrs
  have hrel : r • ha + (r * (1 - α b ha)) • h b + (r + s) • h c = 0 := by
    have h := hrs
    simp only [smul_add, smul_smul] at h
    rw [add_smul, ← h]
    module
  obtain ⟨h0, -, h2⟩ := ggFork_three_coeffs (p := p) hind hbc hrel
  refine ⟨h0, ?_⟩
  rw [h0, zero_add] at h2
  exact h2

private theorem ggFork_four_coeffs_sub (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    {d : Λ} (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {s t : ZMod p}
    (hrel : (ha + h c + (1 - α b ha) • h b) - t • h d = s • h c) : False := by
  have hrel0 : (1 : ZMod p) • ha + (1 - α b ha) • h b + (1 - s) • h c + (-t) • h d = 0 := by
    have h' : ha + h c + (1 - α b ha) • h b - t • h d - s • h c = 0 := sub_eq_zero.mpr hrel
    rw [sub_smul, one_smul, neg_smul, ← h']
    module
  exact one_ne_zero (ggFork_four_coeffs (p := p) hind hbc hbd hcd hrel0).1

private theorem ggFork_coroot_prop (hp2 : p ≠ 2) (ι : Additive ↥Bs ≃+ V) {x y : V}
    {f g : Module.Dual (ZMod p) V} (hfx : f x = 2) (hgy : g y = 2) {ψ χ : MulAut ↥Bs}
    (hψ : ∀ w, ggLin (p := p) ι ψ w = w - f w • x) (hχ : ∀ w, ggLin (p := p) ι χ w = w - g w • y)
    (heq : ψ = χ) : ∃ s : ZMod p, y = s • x := by
  have h : y - f y • x = y - g y • y := by
    rw [← hψ y, heq, hχ y]
  rw [hgy] at h
  have h2 : f y • x = (2 : ZMod p) • y := sub_right_inj.mp h
  refine ⟨(2 : ZMod p)⁻¹ * f y, ?_⟩
  calc y = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • y) := by
        rw [smul_smul, inv_mul_cancel₀ (zmod_two_ne_zero hp2), one_smul]
    _ = (2 : ZMod p)⁻¹ • (f y • x) := by rw [← h2]
    _ = ((2 : ZMod p)⁻¹ * f y) • x := by rw [smul_smul]

private theorem ggFork_symm (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) :
    (ggLin (p := p) ι (φ b * φ c)).symm = ggLin (p := p) ι (φ c * φ b) := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.symm_apply_eq]
  have hb_inv : (φ b)⁻¹ = φ b := ggFork_inv_eq ι (hF.self b) (hlin b)
  have hc_inv : (φ c)⁻¹ = φ c := ggFork_inv_eq ι (hF.self c) (hlin c)
  have hmul : (φ b * φ c) * (φ c * φ b) = 1 := by
    have h : φ c * φ b = (φ b * φ c)⁻¹ := by rw [mul_inv_rev, hb_inv, hc_inv]
    rw [h, mul_inv_cancel]
  rw [← LinearEquiv.mul_apply, ← map_mul, hmul, map_one]
  rfl

theorem exists_fork_second_neighbour {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} {b c : Λ} (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M C) (hbc : b ≠ c) (hbL : ∀ i, i ≠ b → C b i = if i = c then -1 else 0)
    (h3 : 3 ≤ Fintype.card Λ) :
    ∃ v₂ : Λ, v₂ ≠ b ∧ v₂ ≠ c ∧
      (C c v₂ * C v₂ c = 1 ∨ C c v₂ * C v₂ c = 2 ∨ C c v₂ * C v₂ c = 3) := by
  by_contra h
  have hall : ∀ v, v ≠ b → v ≠ c →
      ¬(C c v * C v c = 1 ∨ C c v * C v c = 2 ∨ C c v * C v c = 3) := by
    intro v hvb hvc hcon
    exact h ⟨v, hvb, hvc, hcon⟩
  have hclosed : ∀ u ∈ ({b, c} : Set Λ), ∀ v, (TauCeti.diagramGraph C).Adj u v →
      v ∈ ({b, c} : Set Λ) := by
    intro u hu v huv
    rw [TauCeti.diagramGraph_adj] at huv
    obtain ⟨huv_ne, huv_uv, -⟩ := huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    rcases hu with hb | hc
    · by_contra hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hv
      obtain ⟨hvb, hvc⟩ := hv
      have h0 : C b v = 0 := by rw [hbL v hvb, if_neg hvc]
      rw [← hb] at h0
      exact huv_uv h0
    · by_contra hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hv
      obtain ⟨hvb, hvc⟩ := hv
      rcases hC.entries huv_ne with ⟨-, h0, -⟩ | ⟨-, h1, h2⟩ | h | h
      · exact huv_uv h0
      · rw [hc] at h1 h2
        exact hall v hvb hvc (Or.inl (by rw [h1, h2]; norm_num))
      · rcases h with ⟨-, h'⟩
        rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hc] at h1 h2
          exact hall v hvb hvc (Or.inr (Or.inl (by rw [h1, h2]; norm_num)))
        · rw [hc] at h1 h2
          exact hall v hvb hvc (Or.inr (Or.inl (by rw [h1, h2]; norm_num)))
      · rcases h with ⟨-, h'⟩
        rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hc] at h1 h2
          exact hall v hvb hvc (Or.inr (Or.inr (by rw [h1, h2]; norm_num)))
        · rw [hc] at h1 h2
          exact hall v hvb hvc (Or.inr (Or.inr (by rw [h1, h2]; norm_num)))
  have hconn : (TauCeti.diagramGraph C).Connected :=
    connected_diagramGraph_of_ggIsWeylMatrix (hM : GGIsWeylMatrixFixed M) hC
  have hmem : ∀ v : Λ, v ∈ ({b, c} : Set Λ) := fun v =>
    mem_of_reachable_of_closed hclosed (hconn.preconnected b v) (by simp)
  have hcard : Fintype.card Λ ≤ 2 := by
    have hsub : (Finset.univ : Finset Λ) ⊆ ({b, c} : Finset Λ) := by
      intro x _
      have hx := hmem x
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert,
        Finset.mem_singleton] using hx
    calc Fintype.card Λ = (Finset.univ : Finset Λ).card := rfl
      _ ≤ ({b, c} : Finset Λ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  omega

theorem three_le_card_of_ggForkF1Fails {Λ : Type} [Fintype Λ] {M : CoxeterMatrix Λ}
    (h : GGForkF1Fails M) : 3 ≤ Fintype.card Λ := by
  rcases h with ⟨h3, -⟩ | ⟨e, -⟩
  · omega
  · have hc := Fintype.card_congr e.symm
    simp only [Fintype.card_fin] at hc
    omega

theorem ggFork_braid (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha) :
    φa = (φ c * φa) * φ c * (φ c * φa)⁻¹ := by
  have h1 : ∀ z, ggLin (p := p) ι (φ c * φa * (φ c)⁻¹) z =
      z - (αa + α c) z • (ha + h c) := by
    intro z
    rw [ggLin_conj_reflection ι (hF.self c) hlina (hlin c), hF.a_c, hF.c_a,
      LinearMap.add_apply]
    module
  have h2 : ∀ z, ggLin (p := p) ι (φa * φ c * (φa)⁻¹) z =
      z - (αa + α c) z • (ha + h c) := by
    intro z
    rw [ggLin_conj_reflection ι hF.aa (hlin c) hlina, hF.a_c, hF.c_a, LinearMap.add_apply]
    module
  have hconj : φ c * φa * (φ c)⁻¹ = φa * φ c * (φa)⁻¹ := by
    apply ggLin_injective (p := p) ι
    refine LinearEquiv.ext fun z => ?_
    rw [h1 z, h2 z]
  have hc_inv : (φ c)⁻¹ = φ c := ggFork_inv_eq ι (hF.self c) (hlin c)
  have ha_inv : (φa)⁻¹ = φa := ggFork_inv_eq ι hF.aa hlina
  rw [hc_inv, ha_inv] at hconj
  rw [hconj]
  group

theorem ggFork_t_apply (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha) (w : V) :
    ggLin (p := p) ι ((φ b * φ c) * φa * (φ b * φ c)⁻¹) w =
      w - αa (ggLin (p := p) ι (φ c * φ b) w) • (ha + h c + (1 - α b ha) • h b) := by
  have hsymm := ggFork_symm ι hF hlin
  have hha : ggLin (p := p) ι (φ b * φ c) ha = ha + h c + (1 - α b ha) • h b := by
    rw [map_mul, LinearEquiv.mul_apply, hlin c, hlin b, hF.c_a, map_sub, map_smul,
      hF.b_c]
    module
  rw [ggLin_conj_apply ι (φ b * φ c) φa hlina w, hsymm, hha]

theorem ggFork_t_pairing (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) {v₂ : Λ} (hvb : v₂ ≠ b)
    (hvc : v₂ ≠ c) :
    αa (ggLin (p := p) ι (φ c * φ b) (h c)) = αa (h b) ∧
      αa (ggLin (p := p) ι (φ c * φ b) (h v₂)) = (C c v₂ : ZMod p) ∧
      α v₂ (ha + h c + (1 - α b ha) • h b) = (C v₂ c : ZMod p) := by
  have hbv : α b (h v₂) = 0 := by rw [hF.pair, hF.bL v₂ hvb, if_neg hvc]; simp
  have hav : αa (h v₂) = 0 := by rw [hF.aL v₂ hvb, if_neg hvc]
  have hvb' : α v₂ (h b) = 0 := by rw [hF.pair, hF.bR v₂ hvb, if_neg hvc]; simp
  have hva : α v₂ ha = 0 := by rw [hF.aR v₂ hvb, if_neg hvc]
  refine ⟨?_, ?_, ?_⟩
  · have hc1 : ggLin (p := p) ι (φ c * φ b) (h c) = h b := by
      rw [map_mul, LinearEquiv.mul_apply, hlin b, hF.b_c, hlin c, map_sub, map_smul,
        hF.self c, hF.c_b]
      module
    rw [hc1]
  · have hv2 : ggLin (p := p) ι (φ c * φ b) (h v₂) = h v₂ - (C c v₂ : ZMod p) • h c := by
      rw [map_mul, LinearEquiv.mul_apply, hlin b, hbv, zero_smul, sub_zero, hlin c,
        hF.pair]
    rw [hv2, map_sub, map_smul, hav, hF.a_c, smul_eq_mul]
    ring
  · rw [map_add, map_add, map_smul, hva, hvb', hF.pair]
    simp

theorem ggFork_cross_zero_of_commute (hp2 : p ≠ 2) (ι : Additive ↥Bs ≃+ V)
    (hF : GGForkPairing C b c h α ha αa)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hcomm : (φ b * φ c) * φa * (φ b * φ c)⁻¹ * φ c = φ c * ((φ b * φ c) * φa * (φ b * φ c)⁻¹)) :
    αa (h b) = 0 := by
  set ht : V := ha + h c + (1 - α b ha) • h b with hht
  set f : Module.Dual (ZMod p) V :=
    αa.comp ((ggLin (p := p) ι (φ b * φ c)).symm).toLinearMap with hf
  have hsymm := ggFork_symm ι hF hlin
  have hha : ggLin (p := p) ι (φ b * φ c) ha = ht := by
    dsimp only [ht]
    rw [map_mul, LinearEquiv.mul_apply, hlin c, hlin b, hF.c_a, map_sub, map_smul,
      hF.b_c]
    module
  have hft : f ht = 2 := by
    rw [← hha, hf, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, hF.aa]
  have hlin_t : ∀ w, ggLin (p := p) ι ((φ b * φ c) * φa * (φ b * φ c)⁻¹) w =
      w - f w • ht := by
    intro w
    rw [ggLin_conj_apply ι (φ b * φ c) φa hlina w, hha, hf, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap]
  have hyz : LinearIndependent (ZMod p) ![ht, h c] := ggFork_indep_ht_hc (p := p) hind hF.ne
  have hLt : ggLin (p := p) ι ((φ b * φ c) * φa * (φ b * φ c)⁻¹) = reflection hft :=
    ggLin_eq_reflection ι hft hlin_t
  have hLc : ggLin (p := p) ι (φ c) = reflection (hF.self c) :=
    ggLin_eq_reflection ι (hF.self c) (hlin c)
  have hcomm' : reflection hft * reflection (hF.self c) =
      reflection (hF.self c) * reflection hft := by
    have h2 : ggLin (p := p) ι ((φ b * φ c) * φa * (φ b * φ c)⁻¹ * φ c) =
        ggLin (p := p) ι ((φ b * φ c) * φa * (φ b * φ c)⁻¹) * ggLin (p := p) ι (φ c) :=
      map_mul (ggLin (p := p) ι) _ _
    have h3 : ggLin (p := p) ι (φ c * ((φ b * φ c) * φa * (φ b * φ c)⁻¹)) =
        ggLin (p := p) ι (φ c) * ggLin (p := p) ι ((φ b * φ c) * φa * (φ b * φ c)⁻¹) :=
      map_mul (ggLin (p := p) ι) _ _
    have h := congrArg (ggLin (p := p) ι) hcomm
    rw [h2, h3, hLt, hLc] at h
    exact h
  have hfz : f (h c) = 0 :=
    ggReflection_comm_cross_eq_zero hp2 hft (hF.self c) hyz hcomm'
  have hc1 : ggLin (p := p) ι (φ c * φ b) (h c) = h b := by
    rw [map_mul, LinearEquiv.mul_apply, hlin b, hF.b_c, hlin c, map_sub, map_smul,
      hF.self c, hF.c_b]
    module
  have hfc : f (h c) = αa (h b) := by
    rw [hf, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hsymm, hc1]
  rwa [hfc] at hfz

theorem ggFork_ne_t (hp2 : p ≠ 2) (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h)) {v₂ : Λ} (hvb : v₂ ≠ b) (hvc : v₂ ≠ c) :
    φ c ≠ (φ b * φ c) * φa * (φ b * φ c)⁻¹ ∧
      φ c ≠ φ v₂ * ((φ b * φ c) * φa * (φ b * φ c)⁻¹) * φ v₂ := by
  set t : MulAut ↥Bs := (φ b * φ c) * φa * (φ b * φ c)⁻¹ with htl
  set ht : V := ha + h c + (1 - α b ha) • h b with hht
  set f : Module.Dual (ZMod p) V :=
    αa.comp ((ggLin (p := p) ι (φ b * φ c)).symm).toLinearMap with hf
  have hsymm := ggFork_symm ι hF hlin
  have hha : ggLin (p := p) ι (φ b * φ c) ha = ht := by
    dsimp only [ht]
    rw [map_mul, LinearEquiv.mul_apply, hlin c, hlin b, hF.c_a, map_sub, map_smul,
      hF.b_c]
    module
  have hft : f ht = 2 := by
    rw [← hha, hf, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, hF.aa]
  have hlin_t : ∀ w, ggLin (p := p) ι t w = w - f w • ht := by
    intro w
    rw [htl, ggLin_conj_apply ι (φ b * φ c) φa hlina w, hha, hf, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap]
  have hyz : LinearIndependent (ZMod p) ![ht, h c] := ggFork_indep_ht_hc (p := p) hind hF.ne
  constructor
  · intro hct
    obtain ⟨s, hs⟩ := ggFork_coroot_prop hp2 ι (hF.self c) hft (hlin c) hlin_t hct
    have hrel : (1 : ZMod p) • ht + (-s) • h c = 0 := by
      rw [hs, one_smul, neg_smul, add_neg_cancel]
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hyz) 1 (-s) hrel).1
  · intro hct2
    have hv_inv : (φ v₂)⁻¹ = φ v₂ := ggFork_inv_eq ι (hF.self v₂) (hlin v₂)
    have hlin_v2 : ∀ w, ggLin (p := p) ι (φ v₂ * t * φ v₂) w =
        w - (f.comp ((ggLin (p := p) ι (φ v₂)).symm).toLinearMap) w •
          (ht - α v₂ ht • h v₂) := by
      intro w
      rw [show φ v₂ * t * φ v₂ = φ v₂ * t * (φ v₂)⁻¹ from by rw [hv_inv]]
      rw [ggLin_conj_apply ι (φ v₂) t hlin_t w, hlin v₂]
      conv_rhs => rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    have hgy : (f.comp ((ggLin (p := p) ι (φ v₂)).symm).toLinearMap)
        (ht - α v₂ ht • h v₂) = 2 := by
      have hvy : ht - α v₂ ht • h v₂ = ggLin (p := p) ι (φ v₂) ht := by rw [hlin v₂]
      rw [hvy]
      conv_lhs => rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.symm_apply_apply]
      exact hft
    obtain ⟨s, hs⟩ := ggFork_coroot_prop hp2 ι (hF.self c) hgy (hlin c) hlin_v2 hct2
    exact ggFork_four_coeffs_sub (p := p) hind hF.ne hvb.symm hvc.symm hs

end ForkData

end CFSG.StandardType
