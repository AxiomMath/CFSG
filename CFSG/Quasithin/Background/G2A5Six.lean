module

public import CFSG.Quasithin.Background.G2A5Four
public import CFSG.Quasithin.Background.G2A5Iso
public import CFSG.Quasithin.Background.G2L2Six
public import CFSG.Quasithin.Background.G2A5Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.A5Model
  CFSG.Quasithin.SL2Model CFSG.Quasithin.G1
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G]

theorem comm_mem_of_forall_gen_right {N X Y : Subgroup G} {u : G}
    (hN : ∀ s ∈ X ⊔ Y, ∀ z ∈ N, s * z * s⁻¹ ∈ N)
    (hX : ∀ x ∈ X, ⁅u, x⁆ ∈ N) (hY : ∀ y ∈ Y, ⁅u, y⁆ ∈ N) : ∀ w ∈ X ⊔ Y, ⁅u, w⁆ ∈ N := by
  intro w hw
  rw [Subgroup.sup_eq_closure] at hw
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact hX y hy
    · exact hY y hy
  | one => simp [N.one_mem]
  | mul y z hy hz ihy ihz =>
    have hyJ : y ∈ X ⊔ Y := by rw [Subgroup.sup_eq_closure]; exact hy
    have e : ⁅u, y * z⁆ = ⁅u, y⁆ * (y * ⁅u, z⁆ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem ihy (hN y hyJ _ ihz)
  | inv y hy ih =>
    have hyJ : y ∈ X ⊔ Y := by rw [Subgroup.sup_eq_closure]; exact hy
    have e : ⁅u, y⁻¹⁆ = y⁻¹ * ⁅u, y⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hN y⁻¹ (inv_mem hyJ) _ (N.inv_mem ih)

theorem Ev_decomp : ∀ j : Fin 5, j ≠ 4 → ∀ x : ↥Ev, ∃ y z : ↥Ev, x = y + z ∧
    (y : Fin 5 → ZMod 2) 4 = 0 ∧ (z : Fin 5 → ZMod 2) j = 0 := by
  set_option maxRecDepth 100000 in decide

theorem coord_four_eq_zero_of_comm_K4 : ∀ x : ↥Ev,
    (∀ k : A5, k ∈ K4 → pw (k : Equiv.Perm (Fin 5)) x - x = 0 ∨
      pw (k : Equiv.Perm (Fin 5)) x - x = wA 4) → (x : Fin 5 → ZMod 2) 4 = 0 := by
  set_option maxRecDepth 100000 in decide

theorem card_eq_card_inf_mul_card_secImg {Sx S₂ X : Subgroup G} [(S₂.subgroupOf Sx).Normal]
    (hX : X ≤ Sx) : Nat.card ↥X = Nat.card ↥(S₂ ⊓ X) * Nat.card ↥(secImg Sx S₂ X) := by
  let f : ↥X →* SecQuot Sx S₂ := (secMk Sx S₂).comp (Subgroup.inclusion hX)
  have hker : f.ker = (S₂ ⊓ X).subgroupOf X := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : secMk Sx S₂ (Subgroup.inclusion hX w) = 1 := h
      exact ⟨(secMk_eq_one_iff (A := Sx) (B := S₂)).1 h', w.2⟩
    · rintro ⟨h, -⟩
      exact (secMk_eq_one_iff (A := Sx) (B := S₂)).2 h
  have hrange : f.range = secImg Sx S₂ X := by
    ext z
    rw [MonoidHom.mem_range, mem_secImg]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Subgroup.inclusion hX w, w.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have h := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : S₂ ⊓ X ≤ X)).toEquiv] at h
  exact h.symm

namespace RawData5

variable {L K V V₁ : Subgroup G} (D : RawData5 L K (conjClosure V₁ L))

include D

theorem V_le_VL (hV : V = ⁅conjClosure V₁ L, lOne L V₁⁆) : V ≤ conjClosure V₁ L := by
  rw [hV, Subgroup.commutator_le]
  intro v hv l hl
  have hlL : l ∈ L := (oTwoUpper_le _ hl).1
  have h1 : (l : G) * v⁻¹ * l⁻¹ ∈ conjClosure V₁ L :=
    (Subgroup.mem_normalizer_iff.1 (D.hnorm hlL) v⁻¹).1 (Subgroup.inv_mem _ hv)
  have := Subgroup.mul_mem _ hv h1
  simpa [commutatorElement_def, mul_assoc] using this

end RawData5

namespace NatData5

variable {L K V V₁ : Subgroup G} (D : NatData5 L K (conjClosure V₁ L) V V₁)

include D

theorem exists_mul_of_mem_VL {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G))
    {v : G} (hv : v ∈ conjClosure V₁ L) :
    ∃ v₁ ∈ V, ∃ v₂ ∈ rconj V g, v = v₁ * v₂ := by
  set σ : Equiv.Perm (Fin 5) := ((D.θ ⟨g, hg⟩ : A5) : Equiv.Perm (Fin 5)) with hσ
  have hσ4 : σ 4 ≠ 4 := fun h => D.theta_not_mem_A4s (le_conjClosure V₁ L) hg hgN h
  have hj : σ⁻¹ 4 ≠ 4 := by
    intro h
    apply hσ4
    rw [Equiv.Perm.inv_eq_iff_eq] at h
    exact h.symm
  obtain ⟨y, z, hxyz, hy4, hzj⟩ := Ev_decomp (σ⁻¹ 4) hj (Multiplicative.toAdd (D.ψ ⟨v, hv⟩))
  obtain ⟨v₁, hv₁⟩ := D.ψ.surjective (Multiplicative.ofAdd y)
  obtain ⟨v₂, hv₂⟩ := D.ψ.surjective (Multiplicative.ofAdd z)
  refine ⟨(v₁ : G), ?_, (v₂ : G), ?_, ?_⟩
  · refine (D.hV v₁).2 ?_
    rw [hv₁]
    exact hy4
  · rw [mem_rconj]
    have hn : (g * (v₂ : G) * g⁻¹) ∈ conjClosure V₁ L :=
      (Subgroup.mem_normalizer_iff.1 (D.hnorm hg) (v₂ : G)).1 v₂.2
    refine (D.hV ⟨_, hn⟩).2 ?_
    have h1 : conjAct (conjClosure V₁ L) ⟨g, D.hnorm hg⟩ v₂ = ⟨g * (v₂ : G) * g⁻¹, hn⟩ :=
      Subtype.ext (by rw [conjAct_coe_apply])
    have h2 : D.ψ ⟨g * (v₂ : G) * g⁻¹, hn⟩ = pact σ (Multiplicative.ofAdd z) := by
      rw [← h1, ← hv₂]
      exact D.equiv ⟨g, hg⟩ v₂
    rw [h2, toAdd_pact, toAdd_ofAdd, pw_coe]
    exact hzj
  · have hvv : (⟨v, hv⟩ : conjClosure V₁ L) = v₁ * v₂ := by
      apply D.ψ.injective
      rw [map_mul, hv₁, hv₂, ← ofAdd_add, ← hxyz]
      try rfl
    exact congrArg Subtype.val hvv

end NatData5

namespace A5SettingCore

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5SettingCore V V₁ L T H)

include S

omit [Finite G] in
theorem V_le_VL : V ≤ conjClosure V₁ L := S.D.V_le_VL S.hyp.V_eq

omit [Finite G] in
theorem exists_mul_of_mem_VL {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G))
    {v : G} (hv : v ∈ conjClosure V₁ L) :
    ∃ v₁ ∈ V, ∃ v₂ ∈ rconj V g, v = v₁ * v₂ := S.D.exists_mul_of_mem_VL hg hgN hv

theorem inf_le_V {x : G} (hxVL : x ∈ conjClosure V₁ L) (hxU : x ∈ conjClosure V H) : x ∈ V := by
  refine (S.D.hV ⟨x, hxVL⟩).2 ?_
  refine coord_four_eq_zero_of_comm_K4 (Multiplicative.toAdd (S.D.ψ ⟨x, hxVL⟩)) ?_
  intro k hk
  rw [← S.Ubar_eq_K4] at hk
  obtain ⟨u, rfl⟩ := hk
  have huLU : (u : G) ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2
  have hα : S.D.alpha ⟨u, S.LU_le_normVL huLU⟩ =
      pact ((S.betaU u : A5) : Equiv.Perm (Fin 5)) := (S.pactA_Phi ⟨u, huLU⟩).symm
  have hc : ((conjAct (conjClosure V₁ L) ⟨u, S.LU_le_normVL huLU⟩ ⟨x, hxVL⟩ *
      ⟨x, hxVL⟩⁻¹ : conjClosure V₁ L) : G) ∈ V₁ := by
    rw [Subgroup.coe_mul, conjAct_coe_apply, Subgroup.coe_inv]
    have := S.hyp.G22_commutator_mem u.2 hxU
    simpa using this
  have h := (S.D.line _).1 hc
  rw [map_mul, map_inv, ← S.D.alpha_psi, hα] at h
  rcases h with h | h
  · left
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_mul, toAdd_inv, toAdd_pact] at h'
    simpa [sub_eq_add_neg] using h'
  · right
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_mul, toAdd_inv, toAdd_pact] at h'
    simpa [W4, sub_eq_add_neg] using h'

theorem mem_normalizer_U_of_Phi_mem_A4s (i : ↥(L ⊔ conjClosure V H)) (hi : S.Phi i ∈ A4s) :
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
  have hu4 : S.Phi ⟨u, hu'⟩ ∈ A4s := K4_le_A4s (S.betaU_mem_K4 ⟨u, hu⟩)
  have hlA : S.D.θ ⟨l, hl⟩ ∈ A4s := by
    have h1 : S.D.θ ⟨l, hl⟩ = (S.Phi ⟨u, hu'⟩)⁻¹ * S.Phi i := by
      rw [← S.Phi_of_L ⟨l, hl⟩]
      show S.Phi ⟨l, hl'⟩ = _
      rw [hiul, map_mul, inv_mul_cancel_left]
    rw [h1]
    exact A4s.mul_mem (A4s.inv_mem hu4) hi
  have hmem : S.D.θ ⟨l, hl⟩ ∈ ((lOne L V₁).subgroupOf L).map S.D.θ := by
    rw [S.map_theta_lOne]
    exact hlA
  obtain ⟨a, ha, haθ⟩ := hmem
  have hker : (⟨l, hl⟩ : ↥L) * a⁻¹ ∈ S.D.θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, haθ, mul_inv_cancel]
  rw [S.D.ker_eq] at hker
  have hlaO : (l : G) * (a : G)⁻¹ ∈ pCoreOf 2 (L ⊔ T) := hker
  have hlaT : (l : G) * (a : G)⁻¹ ∈ T := S.O_le_T hlaO
  have haH : (a : G) ∈ H := S.hyp.base.lOne_sup_le
    ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T) (Subgroup.mem_subgroupOf.1 ha))
  have hlH : l ∈ H := by
    have e : l = (l * (a : G)⁻¹) * a := by group
    rw [e]
    exact H.mul_mem (S.hyp.base.T_le_H hlaT) haH
  rw [← hil]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer hu) (le_normalizer_conjClosure V H hlH)

theorem sum_natural {U I Sx W VL S₂ : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : Sx = pCoreOf 2 I) (hW : W = U ⊓ Sx) (hVL : VL = conjClosure V₁ L)
    (hS₂ : S₂ = VL ⊔ (U ⊓ rconj U g))
    (hG13 : Theorem_G_1_3 (GaloisField 2 2) 2 (le_refl 2)) :
    ∃ (s : ℕ) (β : ↥I →* SL(2, GaloisField 2 2))
      (φ : ↥Sx →* Multiplicative (Fin s → Fin 2 → GaloisField 2 2)),
      Function.Surjective β ∧ (∀ x : ↥I, β x = 1 ↔ (x : G) ∈ Sx) ∧
      Function.Surjective φ ∧ (∀ x : ↥Sx, φ x = 1 ↔ (x : G) ∈ S₂) ∧
      (∀ (m : ↥I) (x y : ↥Sx), (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
        φ y = Multiplicative.ofAdd (fun j => β m • Multiplicative.toAdd (φ x) j)) ∧
      Nat.card ↥(W ⊔ S₂) = Nat.card ↥S₂ * Nat.card (GaloisField 2 2) ^ s ∧
      Nat.card ↥W = Nat.card ↥(U ⊓ S₂) * Nat.card (GaloisField 2 2) ^ s ∧
      (∀ x ∈ Sx, x ∈ W ⊔ S₂ ↔ ∀ u ∈ U, ⁅u, x⁆ ∈ S₂) ∧
      (W ⊔ S₂) ⊓ (rconj W g ⊔ S₂) = S₂ ∧ Sx = (W ⊔ S₂) ⊔ (rconj W g ⊔ S₂) := by
  have hI'' : I = L ⊔ conjClosure V H := by
    rw [hI, hU]
    exact S.G24_two_aux hg hgN
  have hI' : I = L ⊔ U := by rw [hI'', hU]
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := sx_facts_gen hI'' S.U_le_T
    S.hyp.G22_three.2 S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  rw [← hS] at hSxO hSxT hINorm hSxU
  rw [← hU] at hSxU
  have hLI : L ≤ I := by rw [hI']; exact le_sup_left
  have hUI : U ≤ I := by rw [hI]; exact le_sup_left
  have hgI : g ∈ I := hLI hg
  have four := S.series_facts hg hgN
  rw [← hU, ← hVL, ← hS₂, ← hI, ← hS] at four
  obtain ⟨hVLS₂, hS₂Sx, hVLcent, hIVL, hIS₂, -, -⟩ := four
  have hSxI : Sx ≤ I := by rw [hS]; exact pCoreOf_le 2 I
  have hS₂N : ∀ x ∈ I, ∀ y ∈ S₂, x * y * x⁻¹ ∈ S₂ := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1 (hIS₂ hx) y).1 hy
  have hWU : W ≤ U := by rw [hW]; exact inf_le_left
  have hWSx : W ≤ Sx := by rw [hW]; exact inf_le_right
  have hAS₂ : U ⊓ rconj U g ≤ S₂ := by rw [hS₂]; exact le_sup_right
  have hVLS₂' : VL ≤ S₂ := hVLS₂
  have hV₁VL : V₁ ≤ VL := by rw [hVL]; exact le_conjClosure V₁ L
  have hV₁S₂ : V₁ ≤ S₂ := hV₁VL.trans hVLS₂'
  have hV₁gS₂ : rconj V₁ g ≤ S₂ := fun x hx =>
    hVLS₂' (by rw [hVL]; exact S.rconj_V₁_le_VL hg hx)
  have hWg_le : rconj W g ≤ Sx := by
    have := rconj_inf_le_Sx (U := U) hgI hINorm
    rwa [← hW] at this
  have hWg_U : rconj W g ≤ rconj U g := fun y hy => by
    rw [mem_rconj] at hy ⊢
    exact hWU hy
  have hUSx : ∀ x ∈ U, ∀ y ∈ Sx, x * y * x⁻¹ ∈ Sx := fun x hx y hy => hINorm x (hUI hx) y hy
  have hsup0 : W ⊔ rconj W g = Sx := by
    have := (S.pCoreOf_I_eq hU hg hgN hI).1
    rw [← hS, ← hW] at this
    exact this.symm
  have hrc : ∀ {x y : G}, x ∈ rconj U g → y ∈ rconj U g → x * y * x⁻¹ * y⁻¹ ∈ rconj V₁ g := by
    intro x y hx hy
    rw [mem_rconj] at hx hy ⊢
    have h := S.hyp.G22_commutator_mem (hU ▸ hx) (hU ▸ hy)
    have e : g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
    rwa [e]
  have hrs : ∀ {x : G}, x ∈ rconj U g → x ^ 2 ∈ rconj V₁ g := by
    intro x hx
    rw [mem_rconj] at hx ⊢
    have h := S.hyp.G22_sq_mem (hU ▸ hx)
    have e : g * x ^ 2 * g⁻¹ = (g * x * g⁻¹) ^ 2 := conj_pow.symm
    rwa [e]
  have hXX : ∀ a ∈ W, ∀ b ∈ W, ⁅a, b⁆ ∈ S₂ := fun a ha b hb =>
    hV₁S₂ (S.hyp.G22_commutator_mem (hU ▸ hWU ha) (hU ▸ hWU hb))
  have hXY : ∀ a ∈ W, ∀ b ∈ rconj W g, ⁅a, b⁆ ∈ S₂ := by
    intro a ha b hb
    have haU : a ∈ U := hWU ha
    have haS : a ∈ Sx := hWSx ha
    have hbS : b ∈ Sx := hWg_le hb
    have hbU : b ∈ rconj U g := hWg_U hb
    have h1 := comm_mem_inf_of_normalizes (U := U) (Sx := Sx) haU hbS hUSx hSxU
    have h2 := comm_mem_rconj_inf (U := U) (Sx := Sx) (I := I) hgI hINorm hUI hSxU hbU haS
    apply hAS₂
    refine Subgroup.mem_inf.2 ⟨h1.1, ?_⟩
    have h3 := (mem_rconj.1 h2).1
    rw [mem_rconj]
    have e : g * ⁅a, b⁆ * g⁻¹ = (g * ⁅b, a⁆ * g⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact U.inv_mem h3
  have hYY : ∀ a ∈ rconj W g, ∀ b ∈ rconj W g, ⁅a, b⁆ ∈ S₂ := fun a ha b hb =>
    hV₁gS₂ (hrc (hWg_U ha) (hWg_U hb))
  have hN : ∀ s ∈ W ⊔ rconj W g, ∀ z ∈ S₂, s * z * s⁻¹ ∈ S₂ :=
    fun s hs z hz => hS₂N s (hSxI (hsup0 ▸ hs)) z hz
  have habel0 := comm_mem_of_forall_gen hN hXX hXY hYY
  have habel : ∀ a ∈ Sx, ∀ b ∈ Sx, ⁅a, b⁆ ∈ S₂ := by
    rw [← hsup0]
    exact habel0
  have hsq : ∀ a ∈ Sx, a * a ∈ S₂ := by
    have hX : ∀ a ∈ W, a * a ∈ S₂ := fun a ha => by
      have := S.hyp.G22_sq_mem (hU ▸ hWU ha)
      rw [pow_two] at this
      exact hV₁S₂ this
    have hY : ∀ a ∈ rconj W g, a * a ∈ S₂ := fun a ha => by
      have := hrs (hWg_U ha)
      rw [pow_two] at this
      exact hV₁gS₂ this
    have := mul_self_mem_of_forall_gen hN habel0 hX hY
    rwa [hsup0] at this
  have Q : QuotSetting I Sx S₂ := ⟨hS₂Sx, hSxI, hINorm, hS₂N, habel, hsq⟩
  obtain ⟨e, he⟩ := exists_mulEquiv_A5_SL2_four
  let β : ↥I →* SL(2, GaloisField 2 2) :=
    e.toMonoidHom.comp (S.Phi.comp (Subgroup.inclusion hI''.le))
  have hβ_apply : ∀ x : ↥I, β x = e (S.Phi ⟨x, hI''.le x.2⟩) := fun x => rfl
  have hβs : Function.Surjective β := by
    intro A
    obtain ⟨x, hx⟩ := S.Phi_surjective (e.symm A)
    refine ⟨⟨x, by rw [hI'']; exact x.2⟩, ?_⟩
    rw [hβ_apply]
    show e (S.Phi x) = A
    rw [hx, MulEquiv.apply_symm_apply]
  have hβk : ∀ x : ↥I, β x = 1 ↔ (x : G) ∈ Sx := by
    intro x
    rw [hβ_apply, map_eq_one_iff e e.injective, S.Phi_eq_one_iff]
    constructor
    · intro hxO
      rw [hS]
      exact mem_pCoreOf_of_mem_pCoreOf_of_le hIle x.2 hxO
    · intro hx
      exact hSxO hx
  have hβh : β ⟨g⁻¹, inv_mem hgI⟩ = (e (S.D.θ ⟨g, hg⟩))⁻¹ := by
    have h1 : (⟨g⁻¹, hI''.le (inv_mem hgI)⟩ : ↥(L ⊔ conjClosure V H)) =
        (⟨g, (le_sup_left : L ≤ L ⊔ conjClosure V H) hg⟩ : ↥(L ⊔ conjClosure V H))⁻¹ :=
      Subtype.ext rfl
    rw [hβ_apply, h1, map_inv, S.Phi_of_L ⟨g, hg⟩, map_inv]
  have hhne : (β ⟨g⁻¹, inv_mem hgI⟩).1 1 0 ≠ 0 := by
    rw [hβh, inv_lower_left]
    refine neg_ne_zero.2 fun h0 => ?_
    exact S.theta_not_mem_A4s hg hgN (mem_A4s_of_stab he h0)
  have hW' : ∀ y : G, y ∈ rconj (W ⊔ S₂) g ↔
      ((⟨g⁻¹, inv_mem hgI⟩ : ↥I) : G)⁻¹ * y * ((⟨g⁻¹, inv_mem hgI⟩ : ↥I) : G) ∈ W ⊔ S₂ :=
    fun y => by
    rw [mem_rconj]
    show g * y * g⁻¹ ∈ W ⊔ S₂ ↔ (g⁻¹)⁻¹ * y * g⁻¹ ∈ W ⊔ S₂
    rw [inv_inv]
  have hinvW : ∀ i : ↥I, (β i).1 1 0 = 0 → ∀ w ∈ W, (i : G) * w * (i : G)⁻¹ ∈ W := by
    intro i hi w hw
    have hiN : (i : G) ∈ Subgroup.normalizer ((conjClosure V H : Subgroup G) : Set G) :=
      S.mem_normalizer_U_of_Phi_mem_A4s ⟨i, hI''.le i.2⟩ (mem_A4s_of_stab he hi)
    rw [← hU] at hiN
    rw [hW] at hw ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.1 hiN w).1 hw.1, hINorm i i.2 w hw.2⟩
  have hinv : ∀ i : ↥I, (β i).1 1 0 = 0 → ∀ w ∈ W ⊔ S₂, (i : G) * w * (i : G)⁻¹ ∈ W ⊔ S₂ := by
    intro i hi w hw
    rw [Subgroup.sup_eq_closure] at hw
    induction hw using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact Subgroup.mem_sup_left (hinvW i hi y hy)
      · exact Subgroup.mem_sup_right (hS₂N i i.2 y hy)
    | one => simp
    | mul y z hy hz ihy ihz =>
      have e : (i : G) * (y * z) * (i : G)⁻¹ = ((i : G) * y * (i : G)⁻¹) * ((i : G) * z * (i : G)⁻¹) := by
        group
      rw [e]
      exact Subgroup.mul_mem _ ihy ihz
    | inv y hy ih =>
      have e : (i : G) * y⁻¹ * (i : G)⁻¹ = ((i : G) * y * (i : G)⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ih
  have hRU : ∀ r ∈ Rg (GaloisField 2 2), ∃ u : ↥I, (u : G) ∈ U ∧ β u = r := by
    intro r hr
    rw [← he] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    rw [← S.Ubar_eq_K4] at hk
    obtain ⟨u, rfl⟩ := hk
    have hu : (u : G) ∈ U := by rw [hU]; exact u.2
    exact ⟨⟨u, hUI hu⟩, hu, rfl⟩
  have hcomm : ∀ u ∈ U, ∀ s ∈ Sx, ⁅u, s⁆ ∈ W ⊔ S₂ := by
    intro u hu s hs
    have := comm_mem_inf_of_normalizes (U := U) (Sx := Sx) hu hs hUSx hSxU
    apply Subgroup.mem_sup_left
    rw [hW]
    exact this
  have hfix : ∀ u ∈ U, ∀ w ∈ W ⊔ S₂, ⁅u, w⁆ ∈ S₂ := by
    intro u hu
    have hN' : ∀ s ∈ W ⊔ S₂, ∀ z ∈ S₂, s * z * s⁻¹ ∈ S₂ := fun s hs z hz =>
      hS₂N s (hSxI ((sup_le hWSx hS₂Sx) hs)) z hz
    refine comm_mem_of_forall_gen_right hN' (fun x hx => ?_) (fun y hy => ?_)
    · exact hV₁S₂ (S.hyp.G22_commutator_mem (hU ▸ hu) (hU ▸ hWU hx))
    · have := hS₂N u (hUI hu) y hy
      have e : ⁅u, y⁆ = (u * y * u⁻¹) * y⁻¹ := rfl
      rw [e]
      exact S₂.mul_mem this (S₂.inv_mem hy)
  have hWS₂ : W ⊔ S₂ ≤ Sx := sup_le hWSx hS₂Sx
  have hrcS₂ : rconj S₂ g = S₂ := by
    apply le_antisymm
    · intro y hy
      rw [mem_rconj] at hy
      have := hS₂N g⁻¹ (inv_mem hgI) _ hy
      simpa [mul_assoc] using this
    · intro y hy
      rw [mem_rconj]
      exact hS₂N g hgI y hy
  have hrcsup : rconj (W ⊔ S₂) g = rconj W g ⊔ S₂ := by
    unfold rconj
    rw [Subgroup.map_sup]
    congr 1
  have hdisj : (W ⊔ S₂) ⊓ rconj (W ⊔ S₂) g = S₂ := by
    apply le_antisymm
    · rintro x ⟨hx1, hx2⟩
      have hWnorm : W ≤ Subgroup.normalizer (S₂ : Set G) := (hWSx.trans hSxI).trans hIS₂
      have hmul1 := Subgroup.coe_mul_of_left_le_normalizer_right W S₂ hWnorm
      have hx1' : x ∈ (↑(W ⊔ S₂) : Set G) := hx1
      rw [hmul1] at hx1'
      obtain ⟨w, hw, z, hz, hwz⟩ := Set.mem_mul.1 hx1'
      rw [hrcsup] at hx2
      have hWgnorm : rconj W g ≤ Subgroup.normalizer (S₂ : Set G) := fun y hy =>
        hIS₂ (hSxI (hWg_le hy))
      have hmul2 := Subgroup.coe_mul_of_left_le_normalizer_right (rconj W g) S₂ hWgnorm
      have hx2' : x ∈ (↑(rconj W g ⊔ S₂) : Set G) := hx2
      rw [hmul2] at hx2'
      obtain ⟨w₂, hw₂, z₂, hz₂, hwz₂⟩ := Set.mem_mul.1 hx2'
      have hwS₂ : w ∈ S₂ := by
        have hws : w = w₂ * (z₂ * z⁻¹) := by
          calc w = (w * z) * z⁻¹ := by group
            _ = (w₂ * z₂) * z⁻¹ := by rw [hwz, hwz₂]
            _ = w₂ * (z₂ * z⁻¹) := by group
        have hs'S₂ : z₂ * z⁻¹ ∈ S₂ := S₂.mul_mem hz₂ (S₂.inv_mem hz)
        have hAnorm : U ⊓ rconj U g ≤ Subgroup.normalizer (VL : Set G) := fun a ha =>
          hIVL (hUI (Subgroup.mem_inf.1 ha).1)
        have hmulA := Subgroup.coe_mul_of_left_le_normalizer_right (U ⊓ rconj U g) VL hAnorm
        have hs'A : z₂ * z⁻¹ ∈ (↑(U ⊓ rconj U g ⊔ VL) : Set G) := by
          rw [sup_comm, ← hS₂]
          exact hs'S₂
        rw [hmulA] at hs'A
        obtain ⟨c, hc, v, hv, hcv⟩ := Set.mem_mul.1 hs'A
        obtain ⟨v₁, hv₁V, v₂, hv₂V, hvv⟩ := S.exists_mul_of_mem_VL hg hgN (hVL ▸ hv)
        have hv₁VL : v₁ ∈ VL := by rw [hVL]; exact S.V_le_VL hv₁V
        have hv₁U : v₁ ∈ U := by rw [hU]; exact le_conjClosure V H hv₁V
        have hv₂U : v₂ ∈ rconj U g := by
          rw [mem_rconj] at hv₂V ⊢
          rw [hU]
          exact le_conjClosure V H hv₂V
        have hw₂S : w₂ ∈ Sx := hWg_le hw₂
        have hcS : c ∈ Sx := hS₂Sx (hAS₂ hc)
        have hwcS : w₂ * c ∈ Sx := Sx.mul_mem hw₂S hcS
        have hv₁c : (w₂ * c) * v₁ = v₁ * (w₂ * c) :=
          Subgroup.mem_centralizer_iff.1 (hVLcent hv₁VL).2 (w₂ * c) hwcS
        have hw_eq : w = v₁ * (w₂ * c * v₂) := by
          calc w = w₂ * (c * v) := by rw [hws, ← hcv]
            _ = (w₂ * c) * (v₁ * v₂) := by rw [hvv]; group
            _ = ((w₂ * c) * v₁) * v₂ := by group
            _ = (v₁ * (w₂ * c)) * v₂ := by rw [hv₁c]
            _ = v₁ * (w₂ * c * v₂) := by group
        have hmemU : v₁⁻¹ * w ∈ U := U.mul_mem (U.inv_mem hv₁U) (hWU hw)
        have hmemg : v₁⁻¹ * w ∈ rconj U g := by
          have h1 : v₁⁻¹ * w = w₂ * c * v₂ := by rw [hw_eq]; group
          rw [h1]
          exact (rconj U g).mul_mem ((rconj U g).mul_mem (hWg_U hw₂)
            (Subgroup.mem_inf.1 hc).2) hv₂U
        have hmemS₂ : v₁⁻¹ * w ∈ S₂ := hAS₂ (Subgroup.mem_inf.2 ⟨hmemU, hmemg⟩)
        have e : w = v₁ * (v₁⁻¹ * w) := by group
        rw [e]
        exact S₂.mul_mem (hVLS₂' hv₁VL) hmemS₂
      have : x = w * z := hwz.symm
      rw [this]
      exact S₂.mul_mem hwS₂ hz
    · intro y hy
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_right hy, ?_⟩
      rw [mem_rconj]
      exact Subgroup.mem_sup_right (hS₂N g hgI y hy)
  have hsup : (W ⊔ S₂) ⊔ rconj (W ⊔ S₂) g = Sx := by
    apply le_antisymm
    · refine sup_le hWS₂ ?_
      intro y hy
      rw [mem_rconj] at hy
      have := hINorm g⁻¹ (inv_mem hgI) _ (hWS₂ hy)
      simpa [mul_assoc] using this
    · rw [← hsup0]
      refine sup_le (le_sup_of_le_left le_sup_left) ?_
      exact le_sup_of_le_right (Subgroup.map_mono le_sup_left)
  obtain ⟨s, φ, hφs, hφk, hφe, hcard, hC⟩ := exists_sum_natural_of_halves hG13 Q β hβs
    (fun x hx => (hβk x).1 hx) (le_sup_right : S₂ ≤ W ⊔ S₂) hWS₂ ⟨g⁻¹, inv_mem hgI⟩ hhne hW'
    hinv hRU hcomm hfix hdisj hsup
  have hN := Q.normal
  have hsec : secImg Sx S₂ (W ⊔ S₂) = secImg Sx S₂ W := by
    ext z
    rw [mem_secImg, mem_secImg]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hWnorm : W ≤ Subgroup.normalizer (S₂ : Set G) := (hWSx.trans hSxI).trans hIS₂
      have hmul := Subgroup.coe_mul_of_left_le_normalizer_right W S₂ hWnorm
      have hx' : (x : G) ∈ (↑(W ⊔ S₂) : Set G) := hx
      rw [hmul] at hx'
      obtain ⟨w, hw, z', hz', hwz⟩ := Set.mem_mul.1 hx'
      refine ⟨⟨w, hWSx hw⟩, hw, ?_⟩
      rw [secMk_eq_secMk_iff]
      show (w : G)⁻¹ * (x : G) ∈ S₂
      rw [← hwz]
      have e : (w : G)⁻¹ * (w * z') = z' := by group
      rw [e]
      exact hz'
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_sup_left hx, rfl⟩
  have hc1 := card_eq_card_inf_mul_card_secImg (Sx := Sx) (S₂ := S₂) (X := W ⊔ S₂) hWS₂
  rw [inf_eq_left.2 (le_sup_right : S₂ ≤ W ⊔ S₂), hcard] at hc1
  have hq : Nat.card ↥(secImg Sx S₂ (W ⊔ S₂)) = Nat.card (GaloisField 2 2) ^ s :=
    (Nat.eq_of_mul_eq_mul_left Nat.card_pos hc1).symm
  have hc2 := card_eq_card_inf_mul_card_secImg (Sx := Sx) (S₂ := S₂) (X := W) hWSx
  rw [← hsec, hq] at hc2
  have hSW : S₂ ⊓ W = U ⊓ S₂ := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hW, Subgroup.mem_inf]
    constructor
    · rintro ⟨h₁, h₂, -⟩
      exact ⟨h₂, h₁⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₂, h₁, hS₂Sx h₂⟩
  rw [hSW] at hc2
  refine ⟨s, β, φ, hβs, hβk, hφs, hφk, hφe, hcard, hc2, fun x hx => (hC x hx).symm, ?_, ?_⟩
  · rw [← hrcsup]
    exact hdisj
  · rw [← hrcsup]
    exact hsup.symm

end A5SettingCore

namespace AlmostSpecialA5Core

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Core V V₁ L T H)

include hyp

theorem G24_six {U I S W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S)
    (hG13 : Theorem_G_1_3 (GaloisField 2 2) 2 (le_refl 2)) :
    (∃ s : ℕ, IsSumOfNaturalSL2ModulesOver (GaloisField 2 2) s I S S
        (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ∧
      (W ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ⊓
          (rconj W g ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) =
        conjClosure V₁ L ⊔ (U ⊓ rconj U g) ∧
      S = (W ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ⊔
          (rconj W g ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ∧
      ∀ x ∈ S, x ∈ W ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g)) ↔
        ∀ u ∈ U, ⁅u, x⁆ ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_natData5 hyp.base.le_V (le_conjClosure V₁ L) hyp.card_V₁
    hyp.V_eq
  let St : A5SettingCore V V₁ L T H := ⟨hyp, D⟩
  obtain ⟨s, β, φ, hβs, hβk, hφs, hφk, hφe, -, -, hC, hdisj, hsup⟩ :=
    St.sum_natural hU hg hgN hI hS hW rfl rfl hG13
  exact ⟨⟨s, β, φ, hβs, hβk, hφs, hφk, hφe⟩, hdisj, hsup, hC⟩

end AlmostSpecialA5Core

namespace AlmostSpecialA5Hyp

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Hyp V V₁ L T H)

include hyp

theorem G24_six {U I S W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S)
    (hG13 : Theorem_G_1_3 (GaloisField 2 2) 2 (le_refl 2)) :
    (∃ s : ℕ, IsSumOfNaturalSL2ModulesOver (GaloisField 2 2) s I S S
        (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ∧
      (W ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ⊓
          (rconj W g ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) =
        conjClosure V₁ L ⊔ (U ⊓ rconj U g) ∧
      S = (W ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ⊔
          (rconj W g ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ∧
      ∀ x ∈ S, x ∈ W ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g)) ↔
        ∀ u ∈ U, ⁅u, x⁆ ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) :=
  hyp.toCore.G24_six hU hg hgN hI hS hW hG13

end AlmostSpecialA5Hyp

end CFSG.Quasithin
