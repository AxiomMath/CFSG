module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Lie
public import CFSG.Milestones.ASVolI.F48.Rest.G23Model
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12G2Aut
public import CFSG.Milestones.ASVolI.F48.Small.Small
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F48.Rest.EngQE

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.ONSchreier

attribute [local irreducible] burnsideF48t_g23LArr burnsideF48t_g23Tau burnsideF48t_g23GensArr
  burnsideF48t_g23PtsStr

section Apply

variable {N : ℕ}

theorem burnsideF48t_perm_mul_apply (f g : Equiv.Perm (Fin N)) (x : Fin N) :
    (f * g) x = f (g x) :=
  rfl

theorem burnsideF48t_perm_inv_apply (f : Equiv.Perm (Fin N)) (x : Fin N) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

theorem burnsideF48t_perm_apply_inv (f : Equiv.Perm (Fin N)) (x : Fin N) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

end Apply

section Tau


@[expose] noncomputable def burnsideF48t_g23τHom : ↥burnsideF48t_g23X →* ↥burnsideF48t_g23X where
  toFun z := ⟨burnsideF48t_g23τ * z * burnsideF48t_g23τ⁻¹, burnsideF48t_g23_τ_conj_mem z.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem burnsideF48t_g23_τHom_injective : Function.Injective burnsideF48t_g23τHom := by
  intro a b h
  have := congrArg Subtype.val h
  simp only [burnsideF48t_g23τHom, MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj,
    mul_right_inj] at this
  exact Subtype.ext this

@[expose] noncomputable def burnsideF48t_g23τHat : MulAut ↥burnsideF48t_g23X :=
  MulEquiv.ofBijective burnsideF48t_g23τHom
    (Finite.injective_iff_bijective.1 burnsideF48t_g23_τHom_injective)

theorem burnsideF48t_g23_τHat_apply (z : ↥burnsideF48t_g23X) :
    ((burnsideF48t_g23τHat z : ↥burnsideF48t_g23X) : Equiv.Perm (Fin 728)) =
      burnsideF48t_g23τ * z * burnsideF48t_g23τ⁻¹ :=
  rfl

theorem burnsideF48t_g23_τHat_not_inner (x : ↥burnsideF48t_g23X) :
    burnsideF48t_g23τHat ≠ MulAut.conj x := by
  intro hx
  have hxy : ∀ y : ↥burnsideF48t_g23X, burnsideF48t_g23τ * y * burnsideF48t_g23τ⁻¹ =
      (x : Equiv.Perm (Fin 728)) * y * (x : Equiv.Perm (Fin 728))⁻¹ := by
    intro y
    have := congrArg (fun φ : MulAut ↥burnsideF48t_g23X => ((φ y : ↥burnsideF48t_g23X) :
      Equiv.Perm (Fin 728))) hx
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      burnsideF48t_g23_τHat_apply] at this
    exact this
  have hq : 364 ≤ (((x : Equiv.Perm (Fin 728))⁻¹ (burnsideF48t_g23τ burnsideF48t_g23pA) :
      Fin 728) : ℕ) :=
    burnsideF48t_g23_X_ge (burnsideF48t_g23X.inv_mem x.2) burnsideF48t_g23_τ_pA
  obtain ⟨g, hg, hgq⟩ := burnsideF48t_g23_P1'_nofix _ hq
  have hgX : g ∈ burnsideF48t_g23X := burnsideF48t_g23_P1'_le_X hg
  have hg0 : g burnsideF48t_g23pA = burnsideF48t_g23pA :=
    MulAction.mem_stabilizer_iff.1 (burnsideF48t_g23_P1'_le_stab hg)
  apply hgq
  have h2 : g = (x : Equiv.Perm (Fin 728))⁻¹ *
      (burnsideF48t_g23τ * g * burnsideF48t_g23τ⁻¹) * x := by
    rw [hxy ⟨g, hgX⟩]
    group
  rw [h2, burnsideF48t_perm_mul_apply ((x : Equiv.Perm (Fin 728))⁻¹ *
      (burnsideF48t_g23τ * g * burnsideF48t_g23τ⁻¹)) x,
    burnsideF48t_perm_apply_inv, burnsideF48t_perm_mul_apply (x : Equiv.Perm (Fin 728))⁻¹
      (burnsideF48t_g23τ * g * burnsideF48t_g23τ⁻¹),
    burnsideF48t_perm_mul_apply (burnsideF48t_g23τ * g) burnsideF48t_g23τ⁻¹,
    burnsideF48t_perm_inv_apply, burnsideF48t_perm_mul_apply burnsideF48t_g23τ g, hg0]

end Tau

theorem burnsideF48t_g23_lieModel {H : Type} [Group H] (h : ChF.IsGenLie H .G2 3 1) :
    CFSG.Blueprint.LieModel H .G2 0 3 1 :=
  Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩, h.2.2⟩)

section Top


theorem burnsideF48t_g23_eq_top {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .G2 3 1 Gp M₁ M₂) (ε : ↥burnsideF48t_g23X ≃* ↥Gp)
    (hε : burnsideF48_img ε burnsideF48t_g23P1 = Gp ⊓ M₁ ∨
      burnsideF48_img ε burnsideF48t_g23P1 = Gp ⊓ M₂) : Gp = ⊤ := by
  classical
  haveI hN : Gp.Normal := hyp.normal
  by_contra hne
  obtain ⟨e, he⟩ : ∃ e : E, e ∉ Gp := by
    by_contra h
    exact hne (eq_top_iff.2 fun e _ => not_not.1 (fun h' => h ⟨e, h'⟩))
  obtain ⟨n, hn, h, hh, rfl⟩ := hyp.split e
  have hhGp : h ∉ Gp := fun hG => he (Gp.mul_mem hn hG)
  have hconjGp : ∀ g : E, g ∈ Gp ↔ h * g * h⁻¹ ∈ Gp := fun g =>
    ⟨fun hg => hN.conj_mem g hg h, fun hg => by
      have := hN.conj_mem _ hg h⁻¹
      simpa [mul_assoc] using this⟩
  have hconjM : ∀ {M : Subgroup E}, h ∈ M → ∀ g : E, g ∈ M ↔ h * g * h⁻¹ ∈ M := fun {M} hM g =>
    ⟨fun hg => M.mul_mem (M.mul_mem hM hg) (M.inv_mem hM), fun hg => by
      have := M.mul_mem (M.mul_mem (M.inv_mem hM) hg) hM
      simpa [mul_assoc] using this⟩
  have hnB : h ∈ Subgroup.normalizer ((Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) : Set E) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    simp only [Subgroup.mem_inf]
    rw [hconjGp g, hconjM hh.1 g, hconjM hh.2 g]
  have hn1 : h ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E) := hyp.dynkin h hnB
  have hn2 : h ∈ Subgroup.normalizer ((Gp ⊓ M₂ : Subgroup E) : Set E) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    simp only [Subgroup.mem_inf]
    rw [hconjGp g, hconjM hh.2 g]
  have hnP : h ∈ Subgroup.normalizer
      ((burnsideF48_img ε burnsideF48t_g23P1 : Subgroup E) : Set E) := by
    rcases hε with h1 | h1 <;> rw [h1]
    exacts [hn1, hn2]
  let α : MulAut ↥Gp := MulAut.conjNormal h
  let α' : MulAut ↥burnsideF48t_g23X := (ε.trans α).trans ε.symm
  have hεα' : ∀ z, ((ε (α' z) : ↥Gp) : E) = h * (ε z : E) * h⁻¹ := by
    intro z
    simp [α', α, MulAut.conjNormal_apply]
  have hα'P1 : ∀ z, z ∈ burnsideF48t_g23P1 ↔ α' z ∈ burnsideF48t_g23P1 := by
    intro z
    rw [← burnsideF48_mem_img ε, ← burnsideF48_mem_img ε (burnsideF48t_g23P1) (α' z), hεα']
    exact Subgroup.mem_normalizer_iff.1 hnP _
  have hcent : ∀ x : ↥burnsideF48t_g23X, (∀ y, α' y = x * y * x⁻¹) → False := by
    intro x hx
    apply hhGp
    have hc : (ε x : E)⁻¹ * h ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 := hεα' (ε.symm ⟨g, hg⟩)
      rw [hx, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc g * ((ε x : E)⁻¹ * h) = (ε x : E)⁻¹ * ((ε x : E) * g * (ε x : E)⁻¹) * h := by group
        _ = (ε x : E)⁻¹ * (h * g * h⁻¹) * h := by rw [h1]
        _ = (ε x : E)⁻¹ * h * g := by group
    rw [hyp.centralizer_trivial, Subgroup.mem_bot] at hc
    have : h = (ε x : E) := by
      calc h = (ε x : E) * ((ε x : E)⁻¹ * h) := by group
        _ = (ε x : E) := by rw [hc, mul_one]
    rw [this]
    exact (ε x).2
  have hconj_inj : Function.Injective
      (MulAut.conj : ↥burnsideF48t_g23X →* MulAut ↥burnsideF48t_g23X) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hc : (ε x : E) ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 := congrArg (fun φ : MulAut ↥burnsideF48t_g23X => φ (ε.symm ⟨g, hg⟩)) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      have h2 := congrArg (fun y => ((ε y : ↥Gp) : E)) h1
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h2
      calc g * (ε x : E) = ((ε x : E) * g * (ε x : E)⁻¹) * (ε x : E) := by rw [h2]
        _ = (ε x : E) * g := by group
    rw [hyp.centralizer_trivial, Subgroup.mem_bot] at hc
    exact ε.injective ((Subtype.ext hc).trans (map_one ε).symm)
  haveI : Finite (MulAut ↥burnsideF48t_g23X) :=
    Finite.of_injective (fun φ : MulAut ↥burnsideF48t_g23X => (φ : ↥burnsideF48t_g23X →
      ↥burnsideF48t_g23X)) DFunLike.coe_injective
  have hM := burnsideF48t_g23_lieModel hyp.model
  have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.card_mulAut_G2_dvd Nat.prime_three
    (by norm_num) hM
  have hord : CFSG.Open.ordG2 3 = 4245696 := by norm_num [CFSG.Open.ordG2]
  rw [hord, ← Nat.card_congr (MulAut.congr ε).toEquiv] at hdvd
  have hle : Nat.card (MulAut ↥burnsideF48t_g23X) ≤ 2 * 4245696 :=
    Nat.le_of_dvd (by norm_num) hdvd
  set H := (MulAut.conj : ↥burnsideF48t_g23X →* MulAut ↥burnsideF48t_g23X).range with hH
  have hHcard : Nat.card ↥H = 4245696 := by
    rw [hH, ← Nat.card_congr (MonoidHom.ofInjective hconj_inj).toEquiv, burnsideF48t_g23_card_X]
  have hτH : burnsideF48t_g23τHat ∉ H := by
    rintro ⟨x, hx⟩
    exact burnsideF48t_g23_τHat_not_inner x hx.symm
  have hidx : H.index = 2 := by
    have h1 := Subgroup.card_mul_index H
    rw [hHcard] at h1
    have h2 : H.index ≠ 1 := fun h1' =>
      hτH (by rw [Subgroup.index_eq_one.1 h1']; exact Subgroup.mem_top _)
    have h3 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h4 : H.index ≤ 2 := by
      by_contra h5
      have : 4245696 * 3 ≤ 4245696 * H.index := Nat.mul_le_mul_left _ (by omega)
      omega
    omega
  have hα'out : α' ∉ H := by
    rintro ⟨x, hx⟩
    exact hcent x fun y => by rw [← hx]; rfl
  have hmem : burnsideF48t_g23τHat⁻¹ * α' ∈ H := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact ⟨fun h1 => absurd (by simpa using H.inv_mem h1) hτH, fun h1 => absurd h1 hα'out⟩
  obtain ⟨x, hx⟩ := hmem
  have hα'eq : ∀ y, α' y = burnsideF48t_g23τHat (x * y * x⁻¹) := by
    intro y
    have h1 := congrArg (fun φ : MulAut ↥burnsideF48t_g23X => (burnsideF48t_g23τHat * φ) y) hx
    simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
    rw [h1, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hq : 364 ≤ ((burnsideF48t_g23τ ((x : Equiv.Perm (Fin 728)) burnsideF48t_g23pA) :
      Fin 728) : ℕ) := by
    have e : burnsideF48t_g23τ ((x : Equiv.Perm (Fin 728)) burnsideF48t_g23pA) =
        (burnsideF48t_g23τ * (x : Equiv.Perm (Fin 728)) * burnsideF48t_g23τ⁻¹)
          (burnsideF48t_g23τ burnsideF48t_g23pA) := by
      rw [burnsideF48t_perm_mul_apply (burnsideF48t_g23τ * (x : Equiv.Perm (Fin 728)))
          burnsideF48t_g23τ⁻¹, burnsideF48t_perm_inv_apply,
        burnsideF48t_perm_mul_apply burnsideF48t_g23τ (x : Equiv.Perm (Fin 728))]
    rw [e]
    exact burnsideF48t_g23_X_ge (burnsideF48t_g23_τ_conj_mem x.2) burnsideF48t_g23_τ_pA
  obtain ⟨g, hg, hgq⟩ := burnsideF48t_g23_P1'_nofix _ hq
  have hgX : g ∈ burnsideF48t_g23X := burnsideF48t_g23_P1'_le_X hg
  have hgP : (⟨g, hgX⟩ : ↥burnsideF48t_g23X) ∈ burnsideF48t_g23P1 :=
    (burnsideF48t_g23_mem_P1 _).2 hg
  have hz : α' (α'.symm ⟨g, hgX⟩) = ⟨g, hgX⟩ := α'.apply_symm_apply _
  have hzP : α'.symm ⟨g, hgX⟩ ∈ burnsideF48t_g23P1 := (hα'P1 _).2 (by rw [hz]; exact hgP)
  have hz0 : ((α'.symm ⟨g, hgX⟩ : ↥burnsideF48t_g23X) : Equiv.Perm (Fin 728))
      burnsideF48t_g23pA = burnsideF48t_g23pA := (burnsideF48t_g23_mem_P1_iff _).1 hzP
  apply hgq
  have hgv : g = burnsideF48t_g23τ * ((x : Equiv.Perm (Fin 728)) *
      ((α'.symm ⟨g, hgX⟩ : ↥burnsideF48t_g23X) : Equiv.Perm (Fin 728)) *
        (x : Equiv.Perm (Fin 728))⁻¹) * burnsideF48t_g23τ⁻¹ := by
    have h1 := congrArg Subtype.val hz
    rw [hα'eq, burnsideF48t_g23_τHat_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact h1.symm
  set z : ↥burnsideF48t_g23X := α'.symm ⟨g, hgX⟩ with hzdef
  rw [hgv, burnsideF48t_perm_mul_apply (burnsideF48t_g23τ * ((x : Equiv.Perm (Fin 728)) *
      (z : Equiv.Perm (Fin 728)) * (x : Equiv.Perm (Fin 728))⁻¹)) burnsideF48t_g23τ⁻¹,
    burnsideF48t_perm_inv_apply, burnsideF48t_perm_mul_apply burnsideF48t_g23τ
      ((x : Equiv.Perm (Fin 728)) * (z : Equiv.Perm (Fin 728)) * (x : Equiv.Perm (Fin 728))⁻¹),
    burnsideF48t_perm_mul_apply ((x : Equiv.Perm (Fin 728)) * (z : Equiv.Perm (Fin 728)))
      (x : Equiv.Perm (Fin 728))⁻¹, burnsideF48t_perm_inv_apply,
    burnsideF48t_perm_mul_apply (x : Equiv.Perm (Fin 728)) (z : Equiv.Perm (Fin 728)), hz0]

end Top

theorem burnsideF48t_g23_chart {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .G2 3 1 Gp M₁ M₂) :
    Gp = ⊤ ∧ ∃ θ : ↥burnsideF48t_g23X ≃* E,
      M₁ ⊓ M₂ = (burnsideF48t_g23P1 ⊓ burnsideF48t_g23P2).map θ.toMonoidHom ∧
      ((M₁ = burnsideF48t_g23P1.map θ.toMonoidHom ∧ M₂ = burnsideF48t_g23P2.map θ.toMonoidHom) ∨
        (M₁ = burnsideF48t_g23P2.map θ.toMonoidHom ∧
          M₂ = burnsideF48t_g23P1.map θ.toMonoidHom)) := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨ε₀⟩ := burnsideF48t_g23_equiv_X hyp.model
  obtain ⟨ε, hεB, hε⟩ := burnsideF48t_identify ε₀ burnsideF48t_g23_sylow burnsideF48t_g23_B_eq
    burnsideF48t_g23_P1_ne_P2 burnsideF48t_g23_P1_max burnsideF48t_g23_P2_max hP
  have hGp : Gp = ⊤ := burnsideF48t_g23_eq_top hyp ε (by
    rcases hε with ⟨h1, -⟩ | ⟨h1, -⟩
    exacts [Or.inl h1, Or.inr h1])
  subst hGp
  let θ : ↥burnsideF48t_g23X ≃* E := ε.trans Subgroup.topEquiv
  have himg : ∀ Q : Subgroup ↥burnsideF48t_g23X, burnsideF48_img ε Q = Q.map θ.toMonoidHom := by
    intro Q
    unfold burnsideF48_img
    rw [Subgroup.map_map]
    rfl
  refine ⟨rfl, θ, ?_, ?_⟩
  · rw [← himg, hεB, top_inf_eq]
  · rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [← himg, h1, top_inf_eq], by rw [← himg, h2, top_inf_eq]⟩
    · exact Or.inr ⟨by rw [← himg, h2, top_inf_eq], by rw [← himg, h1, top_inf_eq]⟩

theorem burnsideF48t_small_G2_three (h45 : F_4_5) (h46 : F_4_6) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .G2 3 1 Gp M₁ M₂) : F48Concl .G2 3 1 Gp M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨hGp, θ, hBθ, hor⟩ := burnsideF48t_g23_chart hyp
  subst hGp
  have hcardE : Nat.card E = 4245696 := by
    rw [← Nat.card_congr θ.toEquiv, burnsideF48t_g23_card_X]
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45 .G2 3 1 E ⊤ M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Y _ β hβ hs
  obtain ⟨a, b, K', haM, hbM, hK', hnaK, hnbK, ha2, hb2, hrel⟩ :=
    burnsideF48s_rel h45 h46 hyp ⟨by decide, by decide⟩ β hβ hs
  obtain ⟨S, hS, hKS⟩ := burnsideF48s_e_card_compl hP hK'
  have hcS : Nat.card ↥S = 729 :=
    burnsideF48s_e_card_sylow hS (k := 6) (a := 5824)
      (by rw [Subgroup.card_top, hcardE]; norm_num) (by norm_num)
  have hcB : Nat.card ↥(M₁ ⊓ M₂) = 2916 := by
    rw [hBθ, Subgroup.card_map_of_injective θ.injective, burnsideF48t_g23_card_B]
  have hK'card : Nat.card ↥K' = Nat.card ↥burnsideF48t_g23K := by
    rw [burnsideF48t_g23_card_K]
    rw [hcS, hcB] at hKS
    omega
  have hcard : Nat.card ↥burnsideF48t_g23X ≤ Nat.card Y := by
    have h13 := (burnside_as_F_4_13_of h45 h46 .G2 3 1 E ⊤ M₁ M₂ hyp Y β hβ hs).2
    rw [card_G0] at h13
    rw [h13, hcardE, burnsideF48t_g23_card_X]
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF48t_qe burnsideF48t_g23_facts burnsideF48t_g23_hconj θ (Or.inl ⟨rfl, rfl⟩) h1 h2
      hyp.gen β hβ hcard haM hbM hK'.2.1 hK'card hnaK hnbK ha2 hb2 hrel
  · exact burnsideF48t_qe burnsideF48t_g23_facts burnsideF48t_g23_hconj θ (Or.inr ⟨rfl, rfl⟩) h1 h2
      hyp.gen β hβ hcard haM hbM hK'.2.1 hK'card hnaK hnbK ha2 hb2 hrel

@[expose] def burnsideF48t_SmallOpen : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → (κ = .D4tw ∧ p = 3 ∧ f = 1) ∨ (κ = .U5 ∧ p = 2 ∧ f = 1) →
    F48Concl κ p f Gp M₁ M₂

theorem burnsideF48t_smallRest_of_open (h45 : F_4_5) (h46 : F_4_6)
    (hopen : burnsideF48t_SmallOpen) : burnsideF48s_SmallRest := by
  intro κ p f E _ Gp M₁ M₂ hyp hcase
  rcases hcase with ⟨hκ | hκ, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · subst hκ
    exact burnsideF48t_small_G2_three h45 h46 hyp
  · subst hκ
    exact hopen _ _ _ E Gp M₁ M₂ hyp (Or.inl ⟨rfl, rfl, rfl⟩)
  · exact hopen _ _ _ E Gp M₁ M₂ hyp (Or.inr ⟨rfl, rfl, rfl⟩)

end CFSG.ASVolI
