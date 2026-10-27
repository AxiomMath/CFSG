module

public import CFSG.Quasithin.Background.G2SixCore
public import CFSG.Quasithin.Background.G2SL3Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
  CFSG.Quasithin.G1
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G]

@[expose] def IsSumOfNaturalSL2ModulesOver (F : Type*) [Field F] (s : ℕ) (M Si S S₂ : Subgroup G) :
    Prop :=
  ∃ (β : ↥M →* SL(2, F)) (φ : ↥Si →* Multiplicative (Fin s → Fin 2 → F)),
    Function.Surjective β ∧ (∀ x : ↥M, β x = 1 ↔ (x : G) ∈ S) ∧
    Function.Surjective φ ∧ (∀ x : ↥Si, φ x = 1 ↔ (x : G) ∈ S₂) ∧
    ∀ (m : ↥M) (x y : ↥Si), (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
      φ y = Multiplicative.ofAdd (fun j => β m • Multiplicative.toAdd (φ x) j)

theorem comm_mem_of_forall_gen {N X Y : Subgroup G}
    (hN : ∀ s ∈ X ⊔ Y, ∀ z ∈ N, s * z * s⁻¹ ∈ N)
    (hXX : ∀ a ∈ X, ∀ b ∈ X, ⁅a, b⁆ ∈ N) (hXY : ∀ a ∈ X, ∀ b ∈ Y, ⁅a, b⁆ ∈ N)
    (hYY : ∀ a ∈ Y, ∀ b ∈ Y, ⁅a, b⁆ ∈ N) :
    ∀ a ∈ X ⊔ Y, ∀ b ∈ X ⊔ Y, ⁅a, b⁆ ∈ N := by
  have hYX : ∀ a ∈ Y, ∀ b ∈ X, ⁅a, b⁆ ∈ N := by
    intro a ha b hb
    have h1 := N.inv_mem (hXY b hb a ha)
    rwa [commutatorElement_inv] at h1
  have key : ∀ b : G, (∀ a ∈ X, ⁅a, b⁆ ∈ N) → (∀ a ∈ Y, ⁅a, b⁆ ∈ N) →
      ∀ a ∈ X ⊔ Y, ⁅a, b⁆ ∈ N := by
    intro b hbX hbY a ha
    rw [Subgroup.sup_eq_closure] at ha
    induction ha using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact hbX y hy
      · exact hbY y hy
    | one => simp [N.one_mem]
    | mul y z hy hz ihy ihz =>
      have hyJ : y ∈ X ⊔ Y := by rw [Subgroup.sup_eq_closure]; exact hy
      have e : ⁅y * z, b⁆ = (y * ⁅z, b⁆ * y⁻¹) * ⁅y, b⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact N.mul_mem (hN y hyJ _ ihz) ihy
    | inv y hy ih =>
      have hyJ : y ∈ X ⊔ Y := by rw [Subgroup.sup_eq_closure]; exact hy
      have e : ⁅y⁻¹, b⁆ = y⁻¹ * ⁅y, b⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hN y⁻¹ (inv_mem hyJ) _ (N.inv_mem ih)
  have h1 : ∀ b ∈ X, ∀ a ∈ X ⊔ Y, ⁅a, b⁆ ∈ N := fun b hb =>
    key b (fun a ha => hXX a ha b hb) (fun a ha => hYX a ha b hb)
  have h2 : ∀ b ∈ Y, ∀ a ∈ X ⊔ Y, ⁅a, b⁆ ∈ N := fun b hb =>
    key b (fun a ha => hXY a ha b hb) (fun a ha => hYY a ha b hb)
  intro a ha b hb
  rw [Subgroup.sup_eq_closure] at hb
  induction hb using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact h1 y hy a ha
    · exact h2 y hy a ha
  | one => simp [N.one_mem]
  | mul y z hy hz ihy ihz =>
    have hyJ : y ∈ X ⊔ Y := by rw [Subgroup.sup_eq_closure]; exact hy
    have e : ⁅a, y * z⁆ = ⁅a, y⁆ * (y * ⁅a, z⁆ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem ihy (hN y hyJ _ ihz)
  | inv y hy ih =>
    have hyJ : y ∈ X ⊔ Y := by rw [Subgroup.sup_eq_closure]; exact hy
    have e : ⁅a, y⁻¹⁆ = y⁻¹ * ⁅a, y⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hN y⁻¹ (inv_mem hyJ) _ (N.inv_mem ih)

theorem mul_self_mem_of_forall_gen {N X Y : Subgroup G}
    (hN : ∀ s ∈ X ⊔ Y, ∀ z ∈ N, s * z * s⁻¹ ∈ N)
    (habel : ∀ a ∈ X ⊔ Y, ∀ b ∈ X ⊔ Y, ⁅a, b⁆ ∈ N)
    (hX : ∀ a ∈ X, a * a ∈ N) (hY : ∀ a ∈ Y, a * a ∈ N) : ∀ a ∈ X ⊔ Y, a * a ∈ N := by
  intro a ha
  rw [Subgroup.sup_eq_closure] at ha
  induction ha using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact hX y hy
    · exact hY y hy
  | one => simp
  | mul y z hy hz ihy ihz =>
    have hyJ : y ∈ X ⊔ Y := by rw [Subgroup.sup_eq_closure]; exact hy
    have hzJ : z ∈ X ⊔ Y := by rw [Subgroup.sup_eq_closure]; exact hz
    have e : (y * z) * (y * z) = (y * ⁅z, y⁆ * y⁻¹) * (y * y) * (z * z) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem (N.mul_mem (hN y hyJ _ (habel z hzJ y hyJ)) ihy) ihz
  | inv y hy ih =>
    have : y⁻¹ * y⁻¹ = (y * y)⁻¹ := (mul_inv_rev y y).symm
    rw [this]
    exact N.inv_mem ih

theorem e12_mul_lower_left {F : Type*} [Field F] (b : F) (A : SL(2, F)) :
    (e12 b * A).1 1 0 = A.1 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

theorem mem_normalizer_U_of_stab (i : ↥(L ⊔ conjClosure V H)) (hi : (S.Phi i).1 1 0 = 0) :
    (i : G) ∈ Subgroup.normalizer ((conjClosure V H : Subgroup G) : Set G) := by
  have hnorm : conjClosure V H ≤ Subgroup.normalizer (L : Set G) := fun u hu => S.U_le_normL hu
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (conjClosure V H) L hnorm
  have hi' : (i : G) ∈ (↑(conjClosure V H ⊔ L) : Set G) := by
    rw [sup_comm]
    exact i.2
  rw [hmul] at hi'
  obtain ⟨u, hu, l, hl, hil⟩ := Set.mem_mul.1 hi'
  have hu' : u ∈ L ⊔ conjClosure V H := (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu
  have hl' : l ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) hl
  have hiul : i = ⟨u, hu'⟩ * ⟨l, hl'⟩ := Subtype.ext hil.symm
  obtain ⟨b, hb⟩ := S.Phi_of_U hu
  have hlθ : S.Phi ⟨l, hl'⟩ = S.D.θ ⟨l, hl⟩ := S.Phi_of_L ⟨l, hl⟩
  rw [hiul, map_mul, hb, e12_mul_lower_left, hlθ] at hi
  have hlN := S.mem_normalizer_V₁_of_stab ⟨l, hl⟩ hi
  have hlH : l ∈ H := S.hyp.base.toBase.N_le_H ⟨hl, hlN⟩
  rw [← hil]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer hu) (le_normalizer_conjClosure V H hlH)

theorem sum_natural {U I Sx W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : Sx = pCoreOf 2 I) (hW : W = U ⊓ Sx)
    (hG13 : Theorem_G_1_3 (GaloisField 2 n) 2 (le_refl 2)) :
    ∃ (s : ℕ) (β : ↥I →* SL(2, GaloisField 2 n))
      (φ : ↥Sx →* Multiplicative (Fin s → Fin 2 → GaloisField 2 n)),
      Function.Surjective β ∧ (∀ x : ↥I, β x = 1 ↔ (x : G) ∈ Sx) ∧
      Function.Surjective φ ∧ (∀ x : ↥Sx, φ x = 1 ↔ (x : G) ∈ U ⊓ rconj U g) ∧
      (∀ (m : ↥I) (x y : ↥Sx), (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
        φ y = Multiplicative.ofAdd (fun j => β m • Multiplicative.toAdd (φ x) j)) ∧
      Nat.card ↥W = Nat.card ↥(U ⊓ rconj U g) * Nat.card (GaloisField 2 n) ^ s ∧
      (∀ x ∈ Sx, x ∈ W ↔ ∀ u ∈ U, ⁅u, x⁆ ∈ U ⊓ rconj U g) ∧
      W ⊓ rconj W g = U ⊓ rconj U g ∧ Sx = W ⊔ rconj W g := by
  obtain ⟨hI', hLI, hUI, hIle, hSxO, hINorm, hSxU⟩ := S.sx_facts hU hg hgN hI
  rw [← hS] at hSxO hINorm hSxU
  have hgI : g ∈ I := hLI hg
  have four := S.G23_four hg hgN
  rw [← hU, ← hI, ← hS] at four
  obtain ⟨hVS₂, hS₂Sx, -, -, hI_norm_S₂, -⟩ := four
  have hSxI : Sx ≤ I := by
    rw [hS]
    exact pCoreOf_le 2 I
  have hS₂N : ∀ x ∈ I, ∀ y ∈ U ⊓ rconj U g, x * y * x⁻¹ ∈ U ⊓ rconj U g := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1 (hI_norm_S₂ hx) y).1 hy
  have hWU : W ≤ U := by
    rw [hW]
    exact inf_le_left
  have hWSx : W ≤ Sx := by
    rw [hW]
    exact inf_le_right
  have hS₂W : U ⊓ rconj U g ≤ W := by
    rw [hW]
    exact le_inf inf_le_left hS₂Sx
  have hsup : W ⊔ rconj W g = Sx := (S.hyp.G23_three hU hg hgN hI hS hW).1.symm
  have hWg_le : rconj W g ≤ Sx := by
    have := rconj_inf_le_Sx (U := U) hgI hINorm
    rwa [← hW] at this
  have hWg_U : rconj W g ≤ rconj U g := fun y hy => by
    rw [mem_rconj] at hy ⊢
    exact hWU hy
  have hUSx : ∀ x ∈ U, ∀ y ∈ Sx, x * y * x⁻¹ ∈ Sx := fun x hx y hy => hINorm x (hUI hx) y hy
  have hV₁S₂ : V₁ ≤ U ⊓ rconj U g := fun x hx => hVS₂ (S.hyp.base.le_V hx)
  have hV₁gS₂ : rconj V₁ g ≤ U ⊓ rconj U g := fun x hx => hVS₂ (S.V₁_le_rconj_V hg hx)
  have hXX : ∀ a ∈ W, ∀ b ∈ W, ⁅a, b⁆ ∈ U ⊓ rconj U g := fun a ha b hb =>
    hV₁S₂ (S.hyp.base.G22_commutator_mem (hU ▸ hWU ha) (hU ▸ hWU hb))
  have hXY : ∀ a ∈ W, ∀ b ∈ rconj W g, ⁅a, b⁆ ∈ U ⊓ rconj U g := by
    intro a ha b hb
    have haU : a ∈ U := hWU ha
    have haS : a ∈ Sx := hWSx ha
    have hbS : b ∈ Sx := hWg_le hb
    have hbU : b ∈ rconj U g := hWg_U hb
    have h1 := comm_mem_inf_of_normalizes (U := U) (Sx := Sx) haU hbS hUSx hSxU
    have h2 := comm_mem_rconj_inf (U := U) (Sx := Sx) (I := I) hgI hINorm hUI hSxU hbU haS
    refine Subgroup.mem_inf.2 ⟨h1.1, ?_⟩
    have h3 := (mem_rconj.1 h2).1
    rw [mem_rconj]
    have e : g * ⁅a, b⁆ * g⁻¹ = (g * ⁅b, a⁆ * g⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact U.inv_mem h3
  have hYY : ∀ a ∈ rconj W g, ∀ b ∈ rconj W g, ⁅a, b⁆ ∈ U ⊓ rconj U g := fun a ha b hb =>
    hV₁gS₂ (S.rconj_commutator_mem (hU ▸ hWg_U ha) (hU ▸ hWg_U hb))
  have hN : ∀ s ∈ W ⊔ rconj W g, ∀ z ∈ U ⊓ rconj U g, s * z * s⁻¹ ∈ U ⊓ rconj U g :=
    fun s hs z hz => hS₂N s (hSxI (hsup ▸ hs)) z hz
  have habel0 := comm_mem_of_forall_gen hN hXX hXY hYY
  have habel : ∀ a ∈ Sx, ∀ b ∈ Sx, ⁅a, b⁆ ∈ U ⊓ rconj U g := by
    rw [← hsup]
    exact habel0
  have hsq : ∀ a ∈ Sx, a * a ∈ U ⊓ rconj U g := by
    have hX : ∀ a ∈ W, a * a ∈ U ⊓ rconj U g := fun a ha => by
      have := S.hyp.base.G22_sq_mem (hU ▸ hWU ha)
      rw [pow_two] at this
      exact hV₁S₂ this
    have hY : ∀ a ∈ rconj W g, a * a ∈ U ⊓ rconj U g := fun a ha => by
      have := S.rconj_sq_mem (hU ▸ hWg_U ha)
      rw [pow_two] at this
      exact hV₁gS₂ this
    have := mul_self_mem_of_forall_gen hN habel0 hX hY
    rwa [hsup] at this
  have Q : QuotSetting I Sx (U ⊓ rconj U g) :=
    ⟨hS₂Sx, hSxI, hINorm, hS₂N, habel, hsq⟩
  have hI'' : I = L ⊔ conjClosure V H := by rw [hI', hU]
  let β : ↥I →* SL(2, GaloisField 2 n) := S.Phi.comp (Subgroup.inclusion hI''.le)
  have hβ_apply : ∀ x : ↥I, β x = S.Phi ⟨x, hI''.le x.2⟩ := fun x => rfl
  have hβs : Function.Surjective β := by
    intro A
    obtain ⟨x, hx⟩ := S.Phi_surjective A
    refine ⟨⟨x, by rw [hI'']; exact x.2⟩, ?_⟩
    exact hx
  have hβk : ∀ x : ↥I, β x = 1 ↔ (x : G) ∈ Sx := by
    intro x
    rw [hβ_apply, S.Phi_eq_one_iff]
    constructor
    · intro hxO
      rw [hS]
      exact mem_pCoreOf_of_mem_pCoreOf_of_le hIle x.2 hxO
    · intro hx
      exact hSxO hx
  have hβh : β ⟨g⁻¹, inv_mem hgI⟩ = (S.D.θ ⟨g, hg⟩)⁻¹ := by
    have h1 : (⟨g⁻¹, hI''.le (inv_mem hgI)⟩ : ↥(L ⊔ conjClosure V H)) =
        (⟨g, (le_sup_left : L ≤ L ⊔ conjClosure V H) hg⟩ : ↥(L ⊔ conjClosure V H))⁻¹ :=
      Subtype.ext rfl
    rw [hβ_apply, h1, map_inv, S.Phi_of_L ⟨g, hg⟩]
  have hhne : (β ⟨g⁻¹, inv_mem hgI⟩).1 1 0 ≠ 0 := by
    rw [hβh, inv_lower_left]
    exact neg_ne_zero.2 (S.lower_left_ne_zero hg hgN)
  have hW' : ∀ y : G, y ∈ rconj W g ↔
      ((⟨g⁻¹, inv_mem hgI⟩ : ↥I) : G)⁻¹ * y * ((⟨g⁻¹, inv_mem hgI⟩ : ↥I) : G) ∈ W := fun y => by
    rw [mem_rconj]
    show g * y * g⁻¹ ∈ W ↔ (g⁻¹)⁻¹ * y * g⁻¹ ∈ W
    rw [inv_inv]
  have hinv : ∀ i : ↥I, (β i).1 1 0 = 0 → ∀ w ∈ W, (i : G) * w * (i : G)⁻¹ ∈ W := by
    intro i hi w hw
    have hiN : (i : G) ∈ Subgroup.normalizer ((conjClosure V H : Subgroup G) : Set G) :=
      S.mem_normalizer_U_of_stab ⟨i, hI''.le i.2⟩ hi
    rw [← hU] at hiN
    rw [hW] at hw ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.1 hiN w).1 hw.1, hINorm i i.2 w hw.2⟩
  have hRU : ∀ r ∈ Rg (GaloisField 2 n), ∃ u : ↥I, (u : G) ∈ U ∧ β u = r := by
    intro r hr
    rw [← S.Ubar_eq_Rg] at hr
    obtain ⟨u, rfl⟩ := hr
    have hu : (u : G) ∈ U := by rw [hU]; exact u.2
    exact ⟨⟨u, hUI hu⟩, hu, rfl⟩
  have hcomm : ∀ u ∈ U, ∀ s ∈ Sx, ⁅u, s⁆ ∈ W := by
    intro u hu s hs
    have := comm_mem_inf_of_normalizes (U := U) (Sx := Sx) hu hs hUSx hSxU
    rw [hW]
    exact this
  have hfix : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ U ⊓ rconj U g := fun u hu w hw =>
    hV₁S₂ (S.hyp.base.G22_commutator_mem (hU ▸ hu) (hU ▸ hWU hw))
  have hdisj : W ⊓ rconj W g = U ⊓ rconj U g := by
    apply le_antisymm
    · rintro y ⟨hyW, hyg⟩
      refine Subgroup.mem_inf.2 ⟨hWU hyW, hWg_U hyg⟩
    · intro y hy
      refine Subgroup.mem_inf.2 ⟨hS₂W hy, ?_⟩
      rw [mem_rconj, hW]
      refine Subgroup.mem_inf.2 ⟨mem_rconj.1 (Subgroup.mem_inf.1 hy).2, ?_⟩
      exact hINorm g hgI y (hS₂Sx hy)
  obtain ⟨s, φ, hφs, hφk, hφe, hcard, hC⟩ := exists_sum_natural_of_halves hG13 Q β hβs
    (fun x hx => (hβk x).1 hx) hS₂W hWSx ⟨g⁻¹, inv_mem hgI⟩ hhne hW' hinv hRU hcomm hfix hdisj hsup
  exact ⟨s, β, φ, hβs, hβk, hφs, hφk, hφe, hcard, fun x hx => (hC x hx).symm, hdisj, hsup.symm⟩

end L2Setting

namespace AlmostSpecialL2Hyp

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialL2Hyp n V V₁ L T H)

include hyp

theorem G23_six {U I S W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S)
    (hG13 : Theorem_G_1_3 (GaloisField 2 n) 2 (le_refl 2)) :
    (∃ s : ℕ, IsSumOfNaturalSL2ModulesOver (GaloisField 2 n) s I S S (U ⊓ rconj U g)) ∧
      W ⊓ rconj W g = U ⊓ rconj U g ∧ S = W ⊔ rconj W g ∧
      ∀ x ∈ S, x ∈ W ↔ ∀ u ∈ U, ⁅u, x⁆ ∈ U ⊓ rconj U g := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L2Setting n V V₁ L T H := ⟨hyp, D⟩
  obtain ⟨s, β, φ, hβs, hβk, hφs, hφk, hφe, -, hC, hdisj, hsup⟩ :=
    St.sum_natural hU hg hgN hI hS hW hG13
  exact ⟨⟨s, β, φ, hβs, hβk, hφs, hφk, hφe⟩, hdisj, hsup, hC⟩

end AlmostSpecialL2Hyp

end CFSG.Quasithin
