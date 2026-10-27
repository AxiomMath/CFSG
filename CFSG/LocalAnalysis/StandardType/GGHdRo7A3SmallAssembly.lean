module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallBasic
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Normalizer
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3ReflFix
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallExcl

public section

namespace CFSG.StandardType.HdRo7A3.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7A3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  {θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V} {z : V} {H A : Subgroup (V ≃ₗ[ZMod 3] V)}

private instance hdRo7A9AsmAux_decidableEqA9Class : DecidableEq A9Class := fun a b => by
  cases a <;> cases b <;> first
    | exact isTrue rfl
    | exact isFalse (by intro h; cases h)

private lemma hdRo7A9AsmAux_const_sub_symm {u v : Fin 9 → ZMod 3} (h : a9Const (u - v)) :
    a9Const (v - u) := by
  intro i
  have hi := h i
  have h0 := h 0
  simp only [Pi.sub_apply] at hi h0 ⊢
  rw [show v i - u i = -(u i - v i) by abel,
    show v 0 - u 0 = -(u 0 - v 0) by abel, hi]

private theorem hdRo7A9AsmAux_fixes_of_gen {S : Set (V ≃ₗ[ZMod 3] V)}
    (hHgen : H = Subgroup.closure S) (hS : ∀ s ∈ S, s z = z) : ∀ a ∈ H, a z = z := by
  intro a ha
  rw [hHgen] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => rfl
  | mul x y _ _ hx hy => rw [LinearEquiv.mul_apply, hy, hx]
  | inv x _ hx =>
      conv_lhs => rw [← hx]
      simp

private theorem hdRo7A9AsmAux_classify (hR : A9RealLeaf) (hN : A9NormLeaf)
    (hW : ∀ g ∈ A, ∀ ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3,
      A9Lift θ z g ρ → ∀ a b : Fin 9, ¬ A9Wit ρ a b)
    (hD : A3LinData 3 9 V θ z H A) (hM : θ (fun _ => 1) = 0)
    {s : V ≃ₗ[ZMod 3] V} (hsH : s ∈ H) (hsr : GGLinRefl s) (hsz : s z ≠ z) :
    ∃ (a : V ≃ₗ[ZMod 3] V) (X : A9Class), A3P 3 9 θ z a ∧
      (X = .cz ∨ X = .ep ∨ X = .em) ∧
      A9Real θ z (a9H X) (a9F X) (a9D X) (a * s * a⁻¹) := by
  obtain ⟨hh, f, d, hhU, hfsum, hfhd, hlevels, hreal⟩ :=
    hR V θ z H A hD hM s hsH hsr hsz
  have hd : d ≠ 0 := by
    intro hd0
    apply hsz
    have h := hreal 0 (zero_mem (a3Aug 3 9)) 1
    simpa [a9Act, hd0] using h
  obtain ⟨σ, X, hhh, hff, hdX⟩ := hN hh f d hhU hfsum hfhd hd hlevels
  obtain ⟨a, ha, haz⟩ := a3_exists_perm hD.hfr hD.h3 σ
  have haP : A3P 3 9 θ z a := ⟨σ, ha, haz⟩
  have haH : a ∈ H := hD.hPH a haP
  have hconj : A9Real θ z (fun i => hh (σ.symm i)) (fun i => f (σ.symm i)) d
      (a * s * a⁻¹) := a9Real_conj ha haz hhU hreal
  have hrealX : A9Real θ z (a9H X) (a9F X) (a9D X) (a * s * a⁻¹) := by
    rw [← hdX]
    exact a9Real_congr hM hconj (hdRo7A9AsmAux_const_sub_symm hhh)
      (hdRo7A9AsmAux_const_sub_symm hff)
  have hmemH : a * s * a⁻¹ ∈ H := H.mul_mem (H.mul_mem haH hsH) (H.inv_mem haH)
  refine ⟨a, X, haP, ?_, hrealX⟩
  rcases X with _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact (a9_excl hD hW .bpm ⟨by decide, by decide, by decide⟩ hmemH hrealX).elim
  · exact (a9_excl hD hW .bmp ⟨by decide, by decide, by decide⟩ hmemH hrealX).elim
  · exact (a9_excl hD hW .cp ⟨by decide, by decide, by decide⟩ hmemH hrealX).elim
  · exact (a9_excl hD hW .cm ⟨by decide, by decide, by decide⟩ hmemH hrealX).elim
  · exact (a9_excl hD hW .d ⟨by decide, by decide, by decide⟩ hmemH hrealX).elim
  · exact (a9_excl hD hW .e ⟨by decide, by decide, by decide⟩ hmemH hrealX).elim
  · exact (a9_excl hD hW .f ⟨by decide, by decide, by decide⟩ hmemH hrealX).elim

private theorem hdRo7A9AsmAux_gen_eq (hR : A9RealLeaf) (hN : A9NormLeaf)
    (hW : ∀ g ∈ A, ∀ ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3,
      A9Lift θ z g ρ → ∀ a b : Fin 9, ¬ A9Wit ρ a b)
    (hD : A3LinData 3 9 V θ z H A) (hM : θ (fun _ => 1) = 0)
    {r : V ≃ₗ[ZMod 3] V} (hrH : r ∈ H) (hr : A9Real θ z a9T a9T 2 r) :
    H = Subgroup.closure ({a : V ≃ₗ[ZMod 3] V | A3P 3 9 θ z a} ∪ {r}) := by
  obtain ⟨S, hS, hHgen, -⟩ := hD.hgen
  apply le_antisymm
  · rw [hHgen, Subgroup.closure_le]
    intro s hs
    have hsH : s ∈ H := (hS s hs).1
    have hsr : GGLinRefl s := (hS s hs).2
    by_cases hsz : s z = z
    · have hPs : A3P 3 9 θ z s :=
        a3_reflFix_holds a3_normalizer_holds 3 9 V θ z H A hD s (hD.hHA hsH) hsr hsz
      exact Subgroup.subset_closure (Set.mem_union_left _ hPs)
    · obtain ⟨a, X, haP, hX, hreal⟩ :=
        hdRo7A9AsmAux_classify hR hN hW hD hM hsH hsr hsz
      have haH : a ∈ H := hD.hPH a haP
      have hconjH : a * s * a⁻¹ ∈ H := H.mul_mem (H.mul_mem haH hsH) (H.inv_mem haH)
      rcases hX with rfl | rfl | rfl
      · exact (a9_excl_cz hD hW hrH hr hconjH hreal).elim
      · have heq : a * s * a⁻¹ = r := a9Real_unique hD.hfr hreal hr
        have hs_eq : s = a⁻¹ * r * a := by
          rw [← heq]
          group
        rw [hs_eq]
        let K : Subgroup (V ≃ₗ[ZMod 3] V) :=
          Subgroup.closure ({a : V ≃ₗ[ZMod 3] V | A3P 3 9 θ z a} ∪ {r})
        exact K.mul_mem
          (K.mul_mem (K.inv_mem (Subgroup.subset_closure
            (Set.mem_union_left _ haP)))
            (Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton r))))
          (Subgroup.subset_closure (Set.mem_union_left _ haP))
      · exact (a9_excl_mix hD hW hrH hr hconjH hreal).elim
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hxP | hxr
    · exact hD.hPH x hxP
    · rw [Set.mem_singleton_iff] at hxr
      subst hxr
      exact hrH

private theorem hdRo7A9AsmAux_linWeyl_of_ep (hR : A9RealLeaf) (hN : A9NormLeaf)
    (hW : A9WitLeaf) (hD : A3LinData 3 9 V θ z H A) (hM : θ (fun _ => 1) = 0)
    (hE : A9E8Leaf) {r : V ≃ₗ[ZMod 3] V} (hrH : r ∈ H)
    (hr : A9Real θ z a9T a9T 2 r) : ZS.LinWeyl 3 H := by
  have hWA : ∀ g ∈ A, ∀ ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3,
      A9Lift θ z g ρ → ∀ a b : Fin 9, ¬ A9Wit ρ a b :=
    hW a3_normalizer_holds V θ z H A hD hM
  have heq := hdRo7A9AsmAux_gen_eq hR hN hWA hD hM hrH hr
  have hweyl : ZS.LinWeyl 3
      (Subgroup.closure ({a : V ≃ₗ[ZMod 3] V | A3P 3 9 θ z a} ∪ {r})) :=
    hE V θ z hD.hfr hM r hr
  rw [heq]
  exact hweyl

private theorem hdRo7A9AsmAux_linWeyl_of_em (hR : A9RealLeaf) (hN : A9NormLeaf)
    (hW : A9WitLeaf) (hD : A3LinData 3 9 V θ z H A) (hM : θ (fun _ => 1) = 0)
    (hE : A9E8Leaf) {r : V ≃ₗ[ZMod 3] V} (hrH : r ∈ H)
    (hr : A9Real θ z a9Tn a9Tn 2 r) : ZS.LinWeyl 3 H := by
  have hD' : A3LinData 3 9 V (-θ) z H A := a3LinData_neg hD hM
  have hfr' : A3Frame 3 9 (-θ) z := a3Frame_neg hD.hfr hM
  have hM' : (-θ) (fun _ => 1) = 0 := by
    rw [LinearMap.neg_apply, hM, neg_zero]
  have hWA' : ∀ g ∈ A, ∀ ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3,
      A9Lift (-θ) z g ρ → ∀ a b : Fin 9, ¬ A9Wit ρ a b :=
    hW a3_normalizer_holds V (-θ) z H A hD' hM'
  have hr' : A9Real (-θ) z a9T a9T 2 r := by
    have h := a9Real_neg (θ := θ) hr
    have hneg : (-a9Tn : Fin 9 → ZMod 3) = a9T := by decide
    simpa [hneg] using h
  have heq := hdRo7A9AsmAux_gen_eq (θ := -θ) hR hN hWA' hD' hM' hrH hr'
  have hPset : {a : V ≃ₗ[ZMod 3] V | A3P 3 9 (-θ) z a} = {a | A3P 3 9 θ z a} := by
    ext a
    exact a3P_neg_iff
  rw [hPset] at heq
  have hweyl : ZS.LinWeyl 3
      (Subgroup.closure ({a : V ≃ₗ[ZMod 3] V | A3P 3 9 θ z a} ∪ {r})) := by
    have h := hE V (-θ) z hfr' hM' r hr'
    rwa [hPset] at h
  rw [heq]
  exact hweyl

private theorem hdRo7A9AsmAux_moving_eq_c {S : Set (V ≃ₗ[ZMod 3] V)}
    (hD : A3LinData 3 9 V θ z H A) {c : V ≃ₗ[ZMod 3] V}
    (hrealc : A9Real θ z 0 0 2 c)
    (hmoving : ∀ s ∈ S, s z ≠ z →
      ∃ a : V ≃ₗ[ZMod 3] V, A3P 3 9 θ z a ∧ A9Real θ z 0 0 2 (a * s * a⁻¹)) :
    ∀ s ∈ S, s z ≠ z → s = c := by
  intro s hs hsz
  obtain ⟨a, haP, hreal⟩ := hmoving s hs hsz
  have heq : a * s * a⁻¹ = c := a9Real_unique hD.hfr hreal hrealc
  have hac : c * a = a * c := a9_cz_comm hD.hfr hrealc haP
  calc s = a⁻¹ * (a * s * a⁻¹) * a := by group
    _ = a⁻¹ * c * a := by rw [heq]
    _ = c := by
      calc a⁻¹ * c * a = a⁻¹ * (c * a) := by group
        _ = a⁻¹ * (a * c) := by rw [hac]
        _ = c := by group

private theorem hdRo7A9AsmAux_cz_false (hD : A3LinData 3 9 V θ z H A)
    {S : Set (V ≃ₗ[ZMod 3] V)} (hHgen : H = Subgroup.closure S)
    (hconn : ∀ s ∈ S, ∀ t ∈ S, Relation.ReflTransGen
      (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v) s t)
    {s₀ : V ≃ₗ[ZMod 3] V} (hs₀S : s₀ ∈ S) (hs₀z : s₀ z ≠ z)
    {c : V ≃ₗ[ZMod 3] V} (hrealc : A9Real θ z 0 0 2 c)
    (hmove_eq_c : ∀ s ∈ S, s z ≠ z → s = c)
    (hcomm : ∀ s ∈ S, Commute c s) (hcc : c * c = 1) : False := by
  have hmem : ∀ x ∈ Subgroup.closure ({c} : Set (V ≃ₗ[ZMod 3] V)), x = 1 ∨ x = c := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Or.inr rfl
    | one => exact Or.inl rfl
    | mul y w _ _ ihy ihw =>
        rcases ihy with h1 | h1 <;> rcases ihw with h2 | h2
        · rw [h1, h2, one_mul]; exact Or.inl rfl
        · rw [h1, h2, one_mul]; exact Or.inr rfl
        · rw [h1, h2, mul_one]; exact Or.inr rfl
        · rw [h1, h2]; exact Or.inl hcc
    | inv y _ ihy =>
        rcases ihy with h1 | h1
        · rw [h1, inv_one]; exact Or.inl rfl
        · rw [h1, inv_eq_of_mul_eq_one_right hcc]; exact Or.inr rfl
  have hS_eq : S = {c} := by
    ext t
    constructor
    · intro ht
      have hpath : Relation.ReflTransGen
          (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v) c t := by
        rw [← hmove_eq_c s₀ hs₀S hs₀z]
        exact hconn s₀ hs₀S t ht
      have hall : ∀ u, Relation.ReflTransGen
          (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v) c u → u = c := by
        intro u hu
        induction hu with
        | refl => rfl
        | tail _ hstep ih =>
            exfalso
            rw [ih] at hstep
            exact hstep.2.2 (hcomm _ hstep.2.1)
      rw [hall t hpath]
      exact Set.mem_singleton c
    · intro ht
      rw [Set.mem_singleton_iff] at ht
      rw [ht, ← hmove_eq_c s₀ hs₀S hs₀z]
      exact hs₀S
  have hHc : H = Subgroup.closure ({c} : Set (V ≃ₗ[ZMod 3] V)) := by
    rw [hHgen, hS_eq]
  obtain ⟨t, ψ, ht, htz, hψu, -, hformula, -⟩ :=
    a3_transp (p := 3) (m := 9) rfl hD.hfr hD.h3 (by norm_num)
      (i := (0 : Fin 9)) (j := (1 : Fin 9)) (by decide)
  have htP : A3P 3 9 θ z t := ⟨Equiv.swap 0 1, ht, htz⟩
  have htmem : t ∈ Subgroup.closure ({c} : Set (V ≃ₗ[ZMod 3] V)) := by
    rw [← hHc]
    exact hD.hPH t htP
  let root : V := θ (Pi.single (0 : Fin 9) (1 : ZMod 3) - Pi.single (1 : Fin 9) (1 : ZMod 3))
  have hroot_ne : root ≠ 0 :=
    a3_theta_single_sub_ne_zero (p := 3) (m := 9) hD.hfr (by norm_num)
      (i := (0 : Fin 9)) (j := (1 : Fin 9)) (by decide)
  have hψroot : ψ root = 2 := by
    change ψ (θ (Pi.single (0 : Fin 9) (1 : ZMod 3) -
      Pi.single (1 : Fin 9) (1 : ZMod 3))) = 2
    rw [hψu _ (a3_single_sub_mem (0 : Fin 9) (1 : Fin 9))]
    decide
  have ht_ne_one : t ≠ 1 := by
    intro ht1
    apply hroot_ne
    have h1 := hformula root
    rw [ht1, hψroot] at h1
    have h2 : (2 : ZMod 3) • root = 0 := by
      have h' : root + (2 : ZMod 3) • root = root := (eq_sub_iff_add_eq).mp h1
      have h'' : root + (2 : ZMod 3) • root = root + 0 := by rw [add_zero]; exact h'
      exact add_left_cancel h''
    exact (smul_eq_zero.mp h2).resolve_left (by decide)
  have hcz : c z = (2 : ZMod 3) • z := by
    have h := hrealc 0 (zero_mem (a3Aug 3 9)) 1
    have h2 : (1 : ZMod 3) - 2 = 2 := by decide
    simpa [a9Act, h2] using h
  have hz0 : z ≠ 0 := by
    rcases hD.hfr.2.2 with ⟨hU, hzne⟩ | ⟨-, hzM⟩
    · exact hzne
    · intro hz
      exact hzM 0 (zero_mem _) (by rw [map_zero]; exact hz.symm)
  have ht_ne_c : t ≠ c := by
    intro htc
    have h1 : (2 : ZMod 3) • z = z := by
      rw [← hcz, ← htc]
      exact htz
    have h2 : ((2 : ZMod 3) - 1) • z = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    have h2' : (1 : ZMod 3) • z = 0 := by
      have h21 : (2 : ZMod 3) - 1 = 1 := by decide
      rwa [h21] at h2
    exact hz0 (by simpa using h2')
  rcases hmem t htmem with ht1 | htc
  · exact ht_ne_one ht1
  · exact ht_ne_c htc

theorem a3_linSmall_of_leaves (hR : A9RealLeaf) (hN : A9NormLeaf) (hW : A9WitLeaf)
    (hE : A9E8Leaf) : A3LinSmallLeaf := by
  intro p hpFact m V instV instM θ z H A hD hM hm9 hr hmove
  obtain hp := hD.hp
  subst hp
  subst hm9
  have hWA : ∀ g ∈ A, ∀ ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3,
      A9Lift θ z g ρ → ∀ a b : Fin 9, ¬ A9Wit ρ a b :=
    hW a3_normalizer_holds V θ z H A hD hM
  obtain ⟨S, hS, hHgen, hconn⟩ := hD.hgen
  have hmover : ∃ s ∈ S, s z ≠ z := by
    by_contra h
    push Not at h
    obtain ⟨a, ha, haz⟩ := hmove
    exact haz (hdRo7A9AsmAux_fixes_of_gen hHgen h a ha)
  obtain ⟨s₀, hs₀S, hs₀z⟩ := hmover
  by_cases hex : ∃ (s : V ≃ₗ[ZMod 3] V) (a : V ≃ₗ[ZMod 3] V) (X : A9Class),
      s ∈ S ∧ A3P 3 9 θ z a ∧ (X = .ep ∨ X = .em) ∧
        A9Real θ z (a9H X) (a9F X) (a9D X) (a * s * a⁻¹)
  · obtain ⟨s, a, X, hsS, haP, hX, hreal⟩ := hex
    have hsH : s ∈ H := (hS s hsS).1
    have haH : a ∈ H := hD.hPH a haP
    have hconjH : a * s * a⁻¹ ∈ H := H.mul_mem (H.mul_mem haH hsH) (H.inv_mem haH)
    rcases hX with rfl | rfl
    · exact hdRo7A9AsmAux_linWeyl_of_ep hR hN hW hD hM hE hconjH hreal
    · exact hdRo7A9AsmAux_linWeyl_of_em hR hN hW hD hM hE hconjH hreal
  · have hmoving_cz : ∀ s ∈ S, s z ≠ z →
        ∃ a : V ≃ₗ[ZMod 3] V, A3P 3 9 θ z a ∧ A9Real θ z 0 0 2 (a * s * a⁻¹) := by
      intro s hs hsz
      obtain ⟨a, X, haP, hX, hreal⟩ :=
        hdRo7A9AsmAux_classify hR hN hWA hD hM (hS s hs).1 (hS s hs).2 hsz
      have hXcz : X = .cz := by
        rcases hX with h | h | h
        · exact h
        · exact absurd ⟨s, a, .ep, hs, haP, Or.inl rfl, h ▸ hreal⟩ hex
        · exact absurd ⟨s, a, .em, hs, haP, Or.inr rfl, h ▸ hreal⟩ hex
      have hrealcz : A9Real θ z 0 0 2 (a * s * a⁻¹) := by
        rw [hXcz] at hreal
        exact hreal
      exact ⟨a, haP, hrealcz⟩
    obtain ⟨a₀, ha₀P, hreal₀cz⟩ := hmoving_cz s₀ hs₀S hs₀z
    let c : V ≃ₗ[ZMod 3] V := a₀ * s₀ * a₀⁻¹
    have hrealc : A9Real θ z 0 0 2 c := hreal₀cz
    have hcc : c * c = 1 := by
      have hs₀sq : s₀ * s₀ = 1 := (hS s₀ hs₀S).2.1
      change (a₀ * s₀ * a₀⁻¹) * (a₀ * s₀ * a₀⁻¹) = 1
      calc (a₀ * s₀ * a₀⁻¹) * (a₀ * s₀ * a₀⁻¹) = a₀ * (s₀ * s₀) * a₀⁻¹ := by group
        _ = 1 := by rw [hs₀sq]; group
    have hmove_eq_c : ∀ s ∈ S, s z ≠ z → s = c :=
      hdRo7A9AsmAux_moving_eq_c hD hrealc hmoving_cz
    have hcomm : ∀ s ∈ S, Commute c s := by
      intro s hs
      by_cases hsz : s z = z
      · have hPs : A3P 3 9 θ z s :=
          a3_reflFix_holds a3_normalizer_holds 3 9 V θ z H A hD s (hD.hHA (hS s hs).1)
            (hS s hs).2 hsz
        exact a9_cz_comm hD.hfr hrealc hPs
      · simp [hmove_eq_c s hs hsz]
    exact (hdRo7A9AsmAux_cz_false hD hHgen hconn hs₀S hs₀z hrealc hmove_eq_c hcomm hcc).elim

end CFSG.StandardType.HdRo7A3.Small
