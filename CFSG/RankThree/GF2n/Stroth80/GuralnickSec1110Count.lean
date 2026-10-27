module

import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Form
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Group
import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualInv
import CFSG.RankThree.GF2n.Stroth80.CarterSec11PiPre
import CFSG.LinearAlgebra.FlagAbelianBound
import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Basic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalStabilizerRigidityGeometry
public import CFSG.RankThree.GF2n.Stroth80.CarterSec11CMIsometry
public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCentralizer
public import CFSG.RankThree.GF2n.Stroth80.Sec11A2Line

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open Matrix
open scoped commutatorElement Matrix MatrixGroups

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

private theorem map_eq_self_of_maps_into {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : Submodule K V} {t : V ≃ₗ[K] V} (h : ∀ w ∈ W, t w ∈ W) :
    Submodule.map (t : V →ₗ[K] V) W = W := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq t W)
  rw [Submodule.map_le_iff_le_comap]
  intro w hw
  exact h w hw

private theorem maps_into_inv_of_maps_into {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : Submodule K V} {t : V ≃ₗ[K] V} (h : ∀ w ∈ W, t w ∈ W) :
    ∀ w ∈ W, t⁻¹ w ∈ W := by
  intro w hw
  have hmap := map_eq_self_of_maps_into h
  have hw' : w ∈ Submodule.map (t : V →ₗ[K] V) W := by rw [hmap]; exact hw
  obtain ⟨v, hv, hvw⟩ := Submodule.mem_map.mp hw'
  have hveq : t⁻¹ w = v := by
    rw [← hvw]
    exact LinearEquiv.symm_apply_apply t v
  rw [hveq]
  exact hv

private theorem card_le_two_mul_card_stabilizer {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Finite V] (A : Subgroup (V ≃ₗ[K] V))
    {W W' : Submodule K V}
    (hdich : ∀ t ∈ A, ((∀ w ∈ W, t w ∈ W) ∧ (∀ w ∈ W', t w ∈ W')) ∨
      ((∀ w ∈ W, t w ∈ W') ∧ (∀ w ∈ W', t w ∈ W))) :
    ∃ A0 : Subgroup (V ≃ₗ[K] V), (∀ t, t ∈ A0 ↔ t ∈ A ∧ ∀ w ∈ W, t w ∈ W) ∧
      Nat.card A ≤ 2 * Nat.card A0 := by
  classical
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V))
      (fun f g h => LinearEquiv.ext (congrFun h))
  let A0 : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {t | t ∈ A ∧ ∀ w ∈ W, t w ∈ W}
      one_mem' := ⟨A.one_mem, fun w hw => by simpa using hw⟩
      mul_mem' := by
        rintro s t ⟨hsA, hsW⟩ ⟨htA, htW⟩
        refine ⟨A.mul_mem hsA htA, fun w hw => ?_⟩
        simpa using hsW _ (htW w hw)
      inv_mem' := by
        rintro t ⟨htA, htW⟩
        exact ⟨A.inv_mem htA, maps_into_inv_of_maps_into htW⟩ }
  refine ⟨A0, fun t => Iff.rfl, ?_⟩
  by_cases hA0 : A0 = A
  · rw [hA0]
    omega
  · have hle : A0 ≤ A := fun t ht => ht.1
    have hlt : A0 < A := lt_of_le_of_ne hle hA0
    obtain ⟨s₀, hs₀A, hs₀A0⟩ := SetLike.exists_of_lt hlt
    have hs₀not : ¬ ∀ w ∈ W, s₀ w ∈ W := fun h => hs₀A0 ⟨hs₀A, h⟩
    have hs₀swap : (∀ w ∈ W, s₀ w ∈ W') ∧ (∀ w ∈ W', s₀ w ∈ W) := by
      rcases hdich s₀ hs₀A with h | h
      · exact absurd h.1 hs₀not
      · exact h
    let f : A → A0 ⊕ A0 := fun t =>
      if ht : (t : V ≃ₗ[K] V) ∈ A0 then Sum.inl ⟨t, ht⟩
      else Sum.inr ⟨s₀ * t, by
        refine ⟨A.mul_mem hs₀A t.2, fun w hw => ?_⟩
        have htnot : ¬ ∀ w ∈ W, (t : V ≃ₗ[K] V) w ∈ W := fun h => ht ⟨t.2, h⟩
        have htswap : (∀ w ∈ W, (t : V ≃ₗ[K] V) w ∈ W') ∧
            (∀ w ∈ W', (t : V ≃ₗ[K] V) w ∈ W) := by
          rcases hdich t t.2 with h | h
          · exact absurd h.1 htnot
          · exact h
        exact hs₀swap.2 _ (htswap.1 w hw)⟩
    have hf : Function.Injective f := by
      intro t t' h
      by_cases ht : (t : V ≃ₗ[K] V) ∈ A0
      · by_cases ht' : (t' : V ≃ₗ[K] V) ∈ A0
        · simp only [f, dif_pos ht, dif_pos ht'] at h
          have h1 : (⟨t, ht⟩ : A0) = ⟨t', ht'⟩ := Sum.inl_injective h
          exact Subtype.ext (congrArg (fun x : A0 => (x : V ≃ₗ[K] V)) h1)
        · simp only [f, dif_pos ht, dif_neg ht'] at h
          exact absurd h (by simp)
      · by_cases ht' : (t' : V ≃ₗ[K] V) ∈ A0
        · simp only [f, dif_neg ht, dif_pos ht'] at h
          exact absurd h (by simp)
        · simp only [f, dif_neg ht, dif_neg ht'] at h
          have h1 : (⟨s₀ * t, _⟩ : A0) = ⟨s₀ * t', _⟩ := Sum.inr_injective h
          have h2 : s₀ * (t : V ≃ₗ[K] V) = s₀ * (t' : V ≃ₗ[K] V) :=
            congrArg (fun x : A0 => (x : V ≃ₗ[K] V)) h1
          exact Subtype.ext (mul_left_cancel h2)
    calc Nat.card A ≤ Nat.card (A0 ⊕ A0) := Nat.card_le_card_of_injective f hf
      _ = Nat.card A0 + Nat.card A0 := Nat.card_sum
      _ = 2 * Nat.card A0 := by omega

private theorem card_le_of_flag_restriction {K V W : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Finite W]
    (A0 : Subgroup (V ≃ₗ[K] V)) (res : A0 →* (W ≃ₗ[K] W))
    (hfaith : Function.Injective res)
    (hcomm : ∀ s t : A0, s.1 * t.1 = t.1 * s.1)
    {H ℓ : Submodule K W} (hH : Module.finrank K H + 1 = Module.finrank K W)
    (hℓ : Module.finrank K ℓ ≤ 1) (hℓH : ℓ ≤ H)
    (h1 : ∀ t : A0, ∀ w : W, res t w - w ∈ H)
    (h2 : ∀ t : A0, ∀ h ∈ H, res t h - h ∈ ℓ)
    (h3 : ∀ t : A0, ∀ l ∈ ℓ, res t l = l) :
    Nat.card A0 ≤ Nat.card K ^ (Module.finrank K W - 1) := by
  let Ahat : Subgroup (W ≃ₗ[K] W) := res.range
  have hcard : Nat.card A0 = Nat.card Ahat :=
    Nat.card_congr (MonoidHom.ofInjective hfaith).toEquiv
  have hcommA : ∀ s ∈ Ahat, ∀ t ∈ Ahat, s * t = t * s := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    show res a * res b = res b * res a
    rw [← map_mul, ← map_mul]
    exact congrArg res (Subtype.ext (hcomm a b))
  have h1' : ∀ s ∈ Ahat, ∀ w : W, s w - w ∈ H := by
    rintro _ ⟨t, rfl⟩ w
    exact h1 t w
  have h2' : ∀ s ∈ Ahat, ∀ h ∈ H, s h - h ∈ ℓ := by
    rintro _ ⟨t, rfl⟩ h hh
    exact h2 t h hh
  have h3' : ∀ s ∈ Ahat, ∀ l ∈ ℓ, s l = l := by
    rintro _ ⟨t, rfl⟩ l hl
    exact h3 t l hl
  calc Nat.card A0 = Nat.card Ahat := hcard
    _ ≤ Nat.card K ^ (Module.finrank K W - 1) :=
      CFSG.LinearAlgebra.card_le_of_commute_of_flag Ahat hcommA hH hℓ hℓH h1' h2' h3'

open CFSG.ComponentClassification.CatalogueBOrthogonalStabilizerRigidity in
private theorem eq_orthogonal_of_totallySingular {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Qf : QuadraticForm K V)
    (hnd : ∀ x : V, (∀ y, QuadraticMap.polar Qf x y = 0) → x = 0)
    {W : Submodule K V} (hs : ∀ w ∈ W, Qf w = 0)
    (hfin : 2 * Module.finrank K W = Module.finrank K V) :
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Qf) W = W :=
  (totally_singular_eq_orthogonal (Q := Qf) (nondegenerate_polarBilin hnd) hs (by
    have hfin' := hfin
    omega)).symm

private theorem exists_natDualCoord_addEquiv (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) {m : ℕ}
    {W₁ W₂ : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)} (hW : IsCompl W₁ W₂)
    {F : (Fin m → K) →+ ↥(cmComm M Q Z B K γ M₀ φ)}
    (hFinj : Function.Injective F)
    (hFW : ∀ x, F x ∈ W₁) (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w)
    {F' : (Fin m → K) →+ ↥(cmComm M Q Z B K γ M₀ φ)}
    (hF'inj : Function.Injective F')
    (hF'W : ∀ x, F' x ∈ W₂) (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w) :
    ∃ Ψ : ↥(cmComm M Q Z B K γ M₀ φ) ≃+ ((Fin m → K) × (Fin m → K)),
      (∀ x y, Ψ (F x + F' y) = (x, y)) ∧
      (∀ x, Ψ (F x) = (x, 0)) ∧ (∀ y, Ψ (F' y) = (0, y)) ∧
      (∀ e, F (Ψ e).1 + F' (Ψ e).2 = e) := by
  classical
  let Φ : ((Fin m → K) × (Fin m → K)) →+ ↥(cmComm M Q Z B K γ M₀ φ) :=
    F.comp (AddMonoidHom.fst (Fin m → K) (Fin m → K)) +
      F'.comp (AddMonoidHom.snd (Fin m → K) (Fin m → K))
  have hΦ : ∀ x y, Φ (x, y) = F x + F' y := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    rw [hΦ, hΦ] at h
    have h1 : F x - F x' = F' y' - F' y := by
      calc F x - F x' = (F x + F' y) - (F x' + F' y) := by abel
        _ = (F x' + F' y') - (F x' + F' y) := by rw [h]
        _ = F' y' - F' y := by abel
    have hleft : F x - F x' ∈ W₁ := W₁.sub_mem (hFW x) (hFW x')
    have hright : F' y' - F' y ∈ W₂ := W₂.sub_mem (hF'W y') (hF'W y)
    have h0 : F x - F x' = 0 :=
      Submodule.disjoint_def.mp hW.disjoint _ hleft (h1.symm ▸ hright)
    have h0' : F' y' - F' y = 0 := h1 ▸ h0
    have hxx : x = x' := hFinj (sub_eq_zero.mp h0)
    have hyy : y = y' := (hF'inj (sub_eq_zero.mp h0')).symm
    rw [hxx, hyy]
  have hsurj : Function.Surjective Φ := by
    intro v
    have hv : v ∈ W₁ ⊔ W₂ := by rw [hW.sup_eq_top]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hv
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hv
    obtain ⟨x, hx⟩ := hFsurj w₁ hw₁
    obtain ⟨y, hy⟩ := hF'surj w₂ hw₂
    exact ⟨(x, y), by rw [hΦ, hx, hy]⟩
  let Ψ : ↥(cmComm M Q Z B K γ M₀ φ) ≃+ ((Fin m → K) × (Fin m → K)) :=
    (AddEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm
  have hΨΦ : ∀ p, Ψ (Φ p) = p := fun p => (AddEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm_apply_apply p
  have hΦΨ : ∀ e, Φ (Ψ e) = e :=
    fun e => (AddEquiv.ofBijective Φ ⟨hinj, hsurj⟩).apply_symm_apply e
  refine ⟨Ψ, ?_, ?_, ?_, ?_⟩
  · intro x y
    rw [← hΦ x y]
    exact hΨΦ (x, y)
  · intro x
    have h : F x + F' (0 : Fin m → K) = F x := by rw [map_zero, add_zero]
    rw [← h, ← hΦ x (0 : Fin m → K)]
    exact hΨΦ (x, 0)
  · intro y
    have h : F (0 : Fin m → K) + F' y = F' y := by rw [map_zero, zero_add]
    rw [← h, ← hΦ (0 : Fin m → K) y]
    exact hΨΦ (0, y)
  · intro e
    exact hΦΨ e

private theorem exists_natDualCoord (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) {m : ℕ}
    {ρ : SL(m, K) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    {W₁ W₂ : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)} (hW : IsCompl W₁ W₂)
    {σ : K ≃+* K} {F : (Fin m → K) →+ ↥(cmComm M Q Z B K γ M₀ φ)}
    (hFσ : ∀ (c : K) x, F (c • x) = σ c • F x) (hFinj : Function.Injective F)
    (hFW : ∀ x, F x ∈ W₁) (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w)
    {σ' : K ≃+* K} {F' : (Fin m → K) →+ ↥(cmComm M Q Z B K γ M₀ φ)}
    (hF'σ : ∀ (c : K) x, F' (c • x) = σ' c • F' x) (hF'inj : Function.Injective F')
    (hF'W : ∀ x, F' x ∈ W₂) (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w)
    (hFeq : ∀ (g : SL(m, K)) x,
      F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = ρ g (F x))
    (hF'eq : ∀ (g : SL(m, K)) x,
      F' (((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)ᵀ *ᵥ x) = ρ g (F' x)) :
    ∃ C : NatDualCoord ρ (Matrix.SpecialLinearGroup.toGL : SL(m, K) →* GL (Fin m) K),
      (∀ x, C.inl x = F x) ∧ ∀ y, C.inr y = F' y := by
  classical
  obtain ⟨Ψ, hΨadd, hΨF, hΨF', hcomp⟩ :=
    exists_natDualCoord_addEquiv φ hW hFinj hFW hFsurj hF'inj hF'W hF'surj
  refine ⟨{ Ψ := Ψ, θ₁ := σ.symm, θ₂ := σ'.symm, smul := ?_, act := ?_ }, ?_, ?_⟩
  · intro c e
    have h1 : c • F' (Ψ e).2 = F' (σ'.symm c • (Ψ e).2) := by
      rw [hF'σ, RingEquiv.apply_symm_apply]
    have h2 : c • F (Ψ e).1 = F (σ.symm c • (Ψ e).1) := by
      rw [hFσ, RingEquiv.apply_symm_apply]
    have h3 : F (σ.symm c • (Ψ e).1) + F' (σ'.symm c • (Ψ e).2) = c • e := by
      rw [← h2, ← h1, ← smul_add, hcomp e]
    rw [← h3, hΨadd]
  · intro g e
    have h1 : (((Matrix.SpecialLinearGroup.toGL : SL(m, K) →* GL (Fin m) K) g :
        GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = (g : Matrix (Fin m) (Fin m) K) := rfl
    have h2 : ((((Matrix.SpecialLinearGroup.toGL : SL(m, K) →* GL (Fin m) K) g)⁻¹ :
        GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        (((Matrix.SpecialLinearGroup.toGL : SL(m, K) →* GL (Fin m) K) (g⁻¹) :
          GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by rw [map_inv]
    have h3 : F ((g : Matrix (Fin m) (Fin m) K) *ᵥ (Ψ e).1) +
        F' ((((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K))ᵀ *ᵥ (Ψ e).2) = ρ g e := by
      rw [hFeq, hF'eq, ← map_add, hcomp e]
    rw [← h3, hΨadd]
    refine Prod.ext ?_ ?_
    · rw [h1]
    · rw [coe_tinvGL, h2]
      rfl
  · intro x
    show Ψ.symm (x, 0) = F x
    rw [← hΨF x, AddEquiv.symm_apply_apply]
  · intro y
    show Ψ.symm (0, y) = F' y
    rw [← hΨF' y, AddEquiv.symm_apply_apply]

private theorem exists_conj_action_of_mem_LB (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    {m : ℕ} {σ₀ : SL(m, K) →* ↥(Xbar M Q Z B)} (hσ₀ : Function.Surjective σ₀)
    {ρ : SL(m, K) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)),
      xbarHToXbar M Q Z B s = σ₀ g → ρ g = cmCommAct hc φ s)
    {l : G} (hl : l ∈ LB M Q B)
    {τ : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)}
    (hτ : ∀ v, (τ v : M₀.E) = φ ⟨l, hc.LB_le_H0 hl⟩ (v : M₀.E)) :
    ∀ g : SL(m, K), ∃ g' : SL(m, K), ∀ v, ρ g (τ v) = τ (ρ g' v) := by
  classical
  have hlM : l ∈ M := hc.LB_le_M hl
  have hlH : l ∈ H0 M Z := hc.LB_le_H0 hl
  have hsq : φ ⟨l, hlH⟩ * φ ⟨l, hlH⟩ = 1 := by
    rw [← map_mul]
    refine (hφk _).mpr ?_
    rw [← pow_two]
    exact hc.sq_mem_Q_of_mem_LB hl
  have hinv : (φ ⟨l, hlH⟩)⁻¹ = φ ⟨l, hlH⟩ := inv_eq_of_mul_eq_one_right hsq
  intro g
  obtain ⟨s, hs⟩ := xbarHToXbar_surjective hc (σ₀ g)
  have hsX : ((s : ↥(H0 M Z)) : G) ∈ XbarPre M Q Z B := (mem_XbarH_iff hc _).mp s.2
  have hconjX : l * ((s : ↥(H0 M Z)) : G) * l⁻¹ ∈ XbarPre M Q Z B := by
    have hmem : l * ((s : ↥(H0 M Z)) : G) * l⁻¹ ∈ conjSubgroup l (XbarPre M Q Z B) :=
      ⟨_, hsX, by show (MulAut.conj l) _ = _; rw [MulAut.conj_apply]⟩
    rwa [XbarPre_normal hc hlM] at hmem
  have hconjH : l * ((s : ↥(H0 M Z)) : G) * l⁻¹ ∈ H0 M Z :=
    (H0 M Z).mul_mem ((H0 M Z).mul_mem hlH s.1.2) ((H0 M Z).inv_mem hlH)
  let s' : ↥(XbarH M Q Z B) :=
    ⟨⟨l * ((s : ↥(H0 M Z)) : G) * l⁻¹, hconjH⟩, (mem_XbarH_iff hc _).mpr hconjX⟩
  obtain ⟨g', hg'⟩ := hσ₀ (xbarHToXbar M Q Z B s')
  refine ⟨g', fun v => ?_⟩
  have h1 : ρ g (τ v) = cmCommAct hc φ s (τ v) := by rw [hρ g s hs]
  have h2 : ρ g' v = cmCommAct hc φ s' v := by rw [hρ g' s' hg'.symm]
  apply Subtype.ext
  rw [h1, h2, coe_cmCommAct, hτ v, hτ (cmCommAct hc φ s' v), coe_cmCommAct]
  have hcoe : (s' : ↥(H0 M Z)) =
      ⟨l * ((s : ↥(H0 M Z)) : G) * l⁻¹, hconjH⟩ := rfl
  have hφs' : φ (s' : ↥(H0 M Z)) =
      φ ⟨l, hlH⟩ * φ (s : ↥(H0 M Z)) * (φ ⟨l, hlH⟩)⁻¹ := by
    rw [hcoe,
      show (⟨l * ((s : ↥(H0 M Z)) : G) * l⁻¹, hconjH⟩ : ↥(H0 M Z)) =
        ⟨l, hlH⟩ * (s : ↥(H0 M Z)) * ⟨l, hlH⟩⁻¹ from Subtype.ext rfl,
      map_mul, map_mul, map_inv]
  have hkey : φ ⟨l, hlH⟩ * φ (s' : ↥(H0 M Z)) = φ s * φ ⟨l, hlH⟩ := by
    rw [hφs', hinv]
    calc φ ⟨l, hlH⟩ * (φ ⟨l, hlH⟩ * φ (s : ↥(H0 M Z)) * φ ⟨l, hlH⟩) =
        (φ ⟨l, hlH⟩ * φ ⟨l, hlH⟩) * (φ (s : ↥(H0 M Z)) * φ ⟨l, hlH⟩) := by group
      _ = φ (s : ↥(H0 M Z)) * φ ⟨l, hlH⟩ := by rw [hsq, one_mul]
  calc φ (s : ↥(H0 M Z)) (φ ⟨l, hlH⟩ v) = (φ s * φ ⟨l, hlH⟩) v := rfl
    _ = (φ ⟨l, hlH⟩ * φ (s' : ↥(H0 M Z))) v := by rw [hkey]
    _ = φ ⟨l, hlH⟩ (φ (s' : ↥(H0 M Z)) v) := rfl

private theorem preserves_or_swaps_summands (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    {m : ℕ} (hm : 3 ≤ m) {σ₀ : SL(m, K) →* ↥(Xbar M Q Z B)}
    (hσ₀ : Function.Surjective σ₀)
    {ρ : SL(m, K) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)),
      xbarHToXbar M Q Z B s = σ₀ g → ρ g = cmCommAct hc φ s)
    {W₁ W₂ : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)}
    {C : NatDualCoord ρ (Matrix.SpecialLinearGroup.toGL : SL(m, K) →* GL (Fin m) K)}
    (hW₁mem : ∀ x, C.inl x ∈ W₁) (hW₁surj : ∀ w ∈ W₁, ∃ x, C.inl x = w)
    (hW₂mem : ∀ y, C.inr y ∈ W₂) (hW₂surj : ∀ w ∈ W₂, ∃ y, C.inr y = w)
    {l : G} (hl : l ∈ LB M Q B)
    {τ : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)}
    (hτ : ∀ v, (τ v : M₀.E) = φ ⟨l, hc.LB_le_H0 hl⟩ (v : M₀.E)) :
    ((∀ w ∈ W₁, τ w ∈ W₁) ∧ (∀ w ∈ W₂, τ w ∈ W₂)) ∨
      ((∀ w ∈ W₁, τ w ∈ W₂) ∧ (∀ w ∈ W₂, τ w ∈ W₁)) := by
  have hrange : (Matrix.SpecialLinearGroup.toGL : SL(m, K) →* GL (Fin m) K).range =
      StatedSL m K := (CFSG.Open.StatedAPI.statedSL_eq_range_toGL m K).symm
  have hT : ∀ g : SL(m, K), ∃ g' : SL(m, K), ∀ e, ρ g (τ e) = τ (ρ g' e) :=
    exists_conj_action_of_mem_LB hc φ hφk hσ₀ hρ hl hτ
  have hCW₁ : (C.W₁ : Set ↥(cmComm M Q Z B K γ M₀ φ)) = (W₁ : Set _) := by
    ext v
    constructor
    · intro hv
      have hv' : v = C.inl (C.Ψ v).1 := C.eq_inl_of_mem_W₁ hv
      rw [hv']
      exact hW₁mem _
    · intro hv
      obtain ⟨x, rfl⟩ := hW₁surj v hv
      exact C.inl_mem_W₁ x
  have hCW₂ : (C.W₂ : Set ↥(cmComm M Q Z B K γ M₀ φ)) = (W₂ : Set _) := by
    ext v
    constructor
    · intro hv
      have hv' : v = C.inr (C.Ψ v).2 := C.eq_inr_of_mem_W₂ hv
      rw [hv']
      exact hW₂mem _
    · intro hv
      obtain ⟨y, rfl⟩ := hW₂surj v hv
      exact C.inr_mem_W₂ y
  rcases C.preserves_or_swaps hm hrange τ hT with h | h
  · refine Or.inl ⟨fun w hw => ?_, fun w hw => ?_⟩
    · obtain ⟨x, rfl⟩ := hW₁surj w hw
      change τ (C.inl x) ∈ (W₁ : Set _)
      rw [← hCW₁]
      exact h.1 x
    · obtain ⟨y, rfl⟩ := hW₂surj w hw
      change τ (C.inr y) ∈ (W₂ : Set _)
      rw [← hCW₂]
      exact h.2 y
  · refine Or.inr ⟨fun w hw => ?_, fun w hw => ?_⟩
    · obtain ⟨x, rfl⟩ := hW₁surj w hw
      change τ (C.inl x) ∈ (W₂ : Set _)
      rw [← hCW₂]
      exact h.1 x
    · obtain ⟨y, rfl⟩ := hW₂surj w hw
      change τ (C.inr y) ∈ (W₁ : Set _)
      rw [← hCW₁]
      exact h.2 y

private theorem polarBilin_orthogonal_eq_self (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {W : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)}
    (hs : ∀ w ∈ W, cmCommQf B φ w = 0)
    (hfin : 2 * Module.finrank K W = Module.finrank K ↥(cmComm M Q Z B K γ M₀ φ)) :
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (cmCommQf B φ)) W = W :=
  eq_orthogonal_of_totallySingular (cmCommQf B φ)
    (fun x hx => hc.cmCommQf_nondegenerate hD φ hφπ x hx) hs hfin

private theorem finrank_eq_of_isCompl
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    {W₁ W₂ : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)}
    (hW : IsCompl W₁ W₂) {m : ℕ} (h₁ : Module.finrank K W₁ = m)
    (h : Module.finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 2 * m) :
    Module.finrank K W₂ = m := by
  have h₁' := h₁
  have h' := h
  have hadd := Submodule.finrank_add_eq_of_isCompl hW
  omega

private theorem exists_mem_B_ne_zero_of_not_mem (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {W : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)}
    (hs : ∀ w ∈ W, cmCommQf B φ w = 0)
    (hfin : 2 * Module.finrank K W = Module.finrank K ↥(cmComm M Q Z B K γ M₀ φ))
    {b : M₀.E} (hbV : b ∈ cmComm M Q Z B K γ M₀ φ)
    (hbW : (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∉ W) :
    ∃ w ∈ W, M₀.B (w : M₀.E) b ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hb : (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∈
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (cmCommQf B φ)) W := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [QuadraticMap.polarBilin_apply_apply, polar_cmCommQf]
    exact hcon w hw
  rw [polarBilin_orthogonal_eq_self hc hD φ hφπ hs hfin] at hb
  exact hbW hb

private theorem exists_flag_line {K W : Type} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (A : Subgroup (W ≃ₗ[K] W))
    {H : Submodule K W} {D : AddSubgroup W}
    (hDcard : Nat.card D ≤ Nat.card K)
    (h1 : ∀ t ∈ A, ∀ w : W, t w - w ∈ H)
    (h2 : ∀ t ∈ A, ∀ h ∈ H, t h - h ∈ D)
    (h3 : ∀ t ∈ A, ∀ d ∈ D, t d = d) :
    ∃ ℓ : Submodule K W, Module.finrank K ℓ ≤ 1 ∧ ℓ ≤ H ∧
      (∀ t ∈ A, ∀ h ∈ H, t h - h ∈ ℓ) ∧ (∀ t ∈ A, ∀ l ∈ ℓ, t l = l) := by
  classical
  by_cases hzero : ∀ t ∈ A, ∀ h ∈ H, t h = h
  · refine ⟨⊥, by simp, bot_le, ?_, ?_⟩
    · intro t ht h hh
      rw [hzero t ht h hh, sub_self]
      exact Submodule.zero_mem ⊥
    · intro t ht l hl
      have hl0 : l = 0 := by simpa using hl
      rw [hl0, map_zero]
  · push Not at hzero
    obtain ⟨t₀, ht₀, h₀, hh₀, hne⟩ := hzero
    let ℓ : Submodule K W := Submodule.map ((t₀ : W ≃ₗ[K] W) - 1 : W →ₗ[K] W) H
    have hℓmem : ∀ x ∈ ℓ, x ∈ D := by
      rintro _ ⟨h, hh, rfl⟩
      exact h2 t₀ ht₀ h hh
    have hℓle : ℓ.toAddSubgroup ≤ D := hℓmem
    have hne0 : t₀ h₀ - h₀ ≠ 0 := sub_ne_zero.mpr hne
    have hmem : t₀ h₀ - h₀ ∈ ℓ := Submodule.mem_map.mpr ⟨h₀, hh₀, rfl⟩
    have hℓne : ℓ ≠ ⊥ := fun hbot => by
      rw [hbot] at hmem
      exact hne0 (by simpa using hmem)
    letI : Fintype K := Fintype.ofFinite K
    haveI : Finite W := Module.finite_of_finite K
    have hq1 : 1 < Nat.card K := Finite.one_lt_card (α := K)
    have hcardle : Nat.card ℓ ≤ Nat.card K :=
      (AddSubgroup.card_le_of_le hℓle).trans hDcard
    haveI : Nontrivial ℓ := Submodule.nontrivial_iff_ne_bot.mpr hℓne
    have hcardℓ : Nat.card ℓ = Nat.card K ^ Module.finrank K ℓ :=
      Module.natCard_eq_pow_finrank
    have hle1 : Nat.card K ^ Module.finrank K ℓ ≤ Nat.card K ^ 1 := by
      rw [← hcardℓ, pow_one]
      exact hcardle
    have hfr : Module.finrank K ℓ ≤ 1 := (pow_le_pow_iff_right₀ hq1).mp hle1
    have hfr1 : Module.finrank K ℓ = 1 := by
      have := Module.finrank_pos (R := K) (M := ℓ)
      omega
    have hcardℓq : Nat.card ℓ = Nat.card K := by
      rw [hcardℓ, hfr1, pow_one]
    have hDle : Nat.card D ≤ Nat.card ℓ.toAddSubgroup := by
      have hc : Nat.card ℓ.toAddSubgroup = Nat.card ℓ := rfl
      rw [hc, hcardℓq]
      exact hDcard
    have hEq : ℓ.toAddSubgroup = D := AddSubgroup.eq_of_le_of_card_ge hℓle hDle
    have hDsub : ∀ x ∈ D, x ∈ ℓ := fun x hx => by rw [← hEq] at hx; exact hx
    refine ⟨ℓ, by omega, ?_, ?_, ?_⟩
    · rintro x ⟨h, hh, rfl⟩
      exact h1 t₀ ht₀ h
    · intro t ht h hh
      exact hDsub _ (h2 t ht h hh)
    · intro t ht l hl
      exact h3 t ht l (hℓmem l hl)

private theorem eq_one_of_restrict_eq_one (hc : Ctx M Q Z B)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {l : G} (hl : l ∈ LB M Q B) {τ : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ)}
    (hτ : ∀ v, (τ v : M₀.E) = φ ⟨l, hc.LB_le_H0 hl⟩ (v : M₀.E))
    (hτ1 : τ = 1) : φ ⟨l, hc.LB_le_H0 hl⟩ = 1 := by
  have hfixV : ∀ v : ↥(cmComm M Q Z B K γ M₀ φ),
      φ ⟨l, hc.LB_le_H0 hl⟩ (v : M₀.E) = (v : M₀.E) := by
    intro v
    rw [← hτ v, hτ1]
    rfl
  have hfixO : ∀ y ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ),
      φ ⟨l, hc.LB_le_H0 hl⟩ y = y := fun y hy =>
    hc.action_fixes_orthogonal hD φ hφπ ha2 hl (hc.LB_le_H0 hl) hy
  ext e
  have he : e ∈ cmComm M Q Z B K γ M₀ φ ⊔
      M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ) := by
    rw [(hc.isCompl_cmComm_orthogonal hD φ hφπ).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨v, hv, y, hy, rfl⟩ := Submodule.mem_sup.mp he
  rw [map_add, hfixV ⟨v, hv⟩, hfixO y hy]
  rfl

private theorem card_range_eq_card_bar_of_ker (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ)))
    (hker : f.ker = Q.subgroupOf (LB M Q B)) :
    Nat.card f.range = Nat.card (bar M Q (LB M Q B)) := by
  have hcardker : Nat.card (Q.subgroupOf (LB M Q B)) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe sec39_Q_le_LB).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [hker, hcardker] at h1
  have h2 := bar_card_mul_card_of_le (M := M) (S := LB M Q B) sec39_Q_le_LB hc.LB_le_M
  have h3 : Nat.card Q * Nat.card f.range =
      Nat.card Q * Nat.card (bar M Q (LB M Q B)) := by
    calc Nat.card Q * Nat.card f.range = Nat.card (LB M Q B) := h1
      _ = Nat.card Q * Nat.card (bar M Q (LB M Q B)) := ((mul_comm _ _).trans h2).symm
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h3

private theorem summand_dichotomy (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    {m : ℕ} (hm : 3 ≤ m) {σ₀ : SL(m, K) →* ↥(Xbar M Q Z B)}
    (hσ₀ : Function.Surjective σ₀)
    {ρ : SL(m, K) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)),
      xbarHToXbar M Q Z B s = σ₀ g → ρ g = cmCommAct hc φ s)
    (f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ)))
    (hf : ∀ (l : ↥(LB M Q B)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
      (f l v : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (v : M₀.E))
    {W₁ W₂ : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)} (hW : IsCompl W₁ W₂)
    {σ : K ≃+* K} {F : (Fin m → K) →+ ↥(cmComm M Q Z B K γ M₀ φ)}
    (hFσ : ∀ (c : K) x, F (c • x) = σ c • F x) (hFinj : Function.Injective F)
    (hFW : ∀ x, F x ∈ W₁) (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w)
    (hFeq : ∀ (g : SL(m, K)) x,
      F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = ρ g (F x))
    {σ' : K ≃+* K} {F' : (Fin m → K) →+ ↥(cmComm M Q Z B K γ M₀ φ)}
    (hF'σ : ∀ (c : K) x, F' (c • x) = σ' c • F' x) (hF'inj : Function.Injective F')
    (hF'W : ∀ x, F' x ∈ W₂) (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w)
    (hF'eq : ∀ (g : SL(m, K)) x,
      F' (((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)ᵀ *ᵥ x) = ρ g (F' x)) :
    ∀ l : ↥(LB M Q B),
      ((∀ w ∈ W₁, f l w ∈ W₁) ∧ (∀ w ∈ W₂, f l w ∈ W₂)) ∨
        ((∀ w ∈ W₁, f l w ∈ W₂) ∧ (∀ w ∈ W₂, f l w ∈ W₁)) := by
  obtain ⟨C, hCinl, hCinr⟩ := exists_natDualCoord φ hW hFσ hFinj hFW hFsurj
    hF'σ hF'inj hF'W hF'surj hFeq hF'eq
  have hW₁mem : ∀ x, C.inl x ∈ W₁ := fun x => by rw [hCinl x]; exact hFW x
  have hW₁surj : ∀ w ∈ W₁, ∃ x, C.inl x = w := by
    intro w hw
    obtain ⟨x, hx⟩ := hFsurj w hw
    exact ⟨x, (hCinl x).trans hx⟩
  have hW₂mem : ∀ y, C.inr y ∈ W₂ := fun y => by rw [hCinr y]; exact hF'W y
  have hW₂surj : ∀ w ∈ W₂, ∃ y, C.inr y = w := by
    intro w hw
    obtain ⟨y, hy⟩ := hF'surj w hw
    exact ⟨y, (hCinr y).trans hy⟩
  intro l
  exact preserves_or_swaps_summands hc φ hφk hm hσ₀ hρ hW₁mem hW₁surj hW₂mem hW₂surj
    l.2 (hf l)

private theorem exists_restrict_hom (hc : Ctx M Q Z B)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) :
    ∃ f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
        ↥(cmComm M Q Z B K γ M₀ φ)),
      f.ker = Q.subgroupOf (LB M Q B) ∧
      ∀ (l : ↥(LB M Q B)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
        (f l v : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (v : M₀.E) := by
  classical
  let rhoV : ↥((LB M Q B).subgroupOf (H0 M Z)) →*
      (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)) :=
    { toFun := fun l => LinearEquiv.ofSubmodules (φ l.1)
        (cmComm M Q Z B K γ M₀ φ) (cmComm M Q Z B K γ M₀ φ)
        (map_eq_self_of_maps_into (fun v hv => hc.mem_cmComm_of_act hD φ hφπ l.1.2 hv))
      map_one' := by
        refine LinearEquiv.ext fun v => Subtype.ext ?_
        simp [LinearEquiv.ofSubmodules_apply]
      map_mul' := by
        intro s t
        refine LinearEquiv.ext fun v => Subtype.ext ?_
        simp [LinearEquiv.ofSubmodules_apply] }
  let m : ↥(LB M Q B) →* ↥((LB M Q B).subgroupOf (H0 M Z)) :=
    { toFun := fun l => ⟨⟨l, hc.LB_le_H0 l.2⟩, l.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun s t => Subtype.ext rfl }
  let f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ)) := rhoV.comp m
  have hf : ∀ (l : ↥(LB M Q B)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
      (f l v : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (v : M₀.E) := fun l v => rfl
  refine ⟨f, ?_, hf⟩
  ext l
  constructor
  · intro hl
    have h1 : rhoV (m l) = 1 := hl
    have h2 : φ ⟨l, hc.LB_le_H0 l.2⟩ = 1 :=
      eq_one_of_restrict_eq_one hc ha2 hD φ hφπ l.2 (τ := rhoV (m l))
        (fun v => rfl) h1
    exact Subgroup.mem_subgroupOf.mpr ((hφk _).mp h2)
  · intro hl
    have h2 : φ ⟨l, hc.LB_le_H0 l.2⟩ = 1 := (hφk _).mpr (Subgroup.mem_subgroupOf.mp hl)
    have h2' : φ (m l).1 = 1 := h2
    show f l = 1
    change LinearEquiv.ofSubmodules (φ (m l).1)
      (cmComm M Q Z B K γ M₀ φ) (cmComm M Q Z B K γ M₀ φ) _ = 1
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    change φ (m l).1 (v : M₀.E) = (v : M₀.E)
    rw [h2']
    rfl

private theorem mul_comm_range (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ)))
    (hfker : f.ker = Q.subgroupOf (LB M Q B)) :
    ∀ s ∈ f.range, ∀ t ∈ f.range, s * t = t * s := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  have hcommQ : ⁅a, b⁆ ∈ f.ker := by
    rw [hfker]
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.commutator_le.mp hc.commutator_LB_le_Q _ a.2 _ b.2)
  have h1 : f ⁅a, b⁆ = 1 := hcommQ
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

private theorem exists_stabilizer_res
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ)))
    {W W' : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)}
    (hdich : ∀ t ∈ f.range, ((∀ w ∈ W, t w ∈ W) ∧ (∀ w ∈ W', t w ∈ W')) ∨
      ((∀ w ∈ W, t w ∈ W') ∧ (∀ w ∈ W', t w ∈ W))) :
    ∃ (A0 : Subgroup (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
        ↥(cmComm M Q Z B K γ M₀ φ))),
      (∀ t, t ∈ A0 ↔ t ∈ f.range ∧ ∀ w ∈ W, t w ∈ W) ∧
      Nat.card f.range ≤ 2 * Nat.card A0 ∧
      ∃ res : A0 →* (W ≃ₗ[K] W),
        ∀ (t : A0) (w : W), ((res t w : W) : ↥(cmComm M Q Z B K γ M₀ φ)) = t.1 w := by
  classical
  haveI : Finite ↥(cmComm M Q Z B K γ M₀ φ) := Module.finite_of_finite K
  obtain ⟨A0, hA0mem, hcard2⟩ :=
    card_le_two_mul_card_stabilizer f.range hdich
  have hA0W : ∀ t, t ∈ A0 → ∀ w ∈ W, t w ∈ W := fun t ht => (hA0mem t).mp ht |>.2
  let res : A0 →* (W ≃ₗ[K] W) :=
    { toFun := fun t => LinearEquiv.ofSubmodules t.1 W W
        (map_eq_self_of_maps_into (hA0W t.1 t.2))
      map_one' := by
        refine LinearEquiv.ext fun w => Subtype.ext ?_
        simp [LinearEquiv.ofSubmodules_apply]
      map_mul' := by
        intro s t
        refine LinearEquiv.ext fun w => Subtype.ext ?_
        simp [LinearEquiv.ofSubmodules_apply] }
  exact ⟨A0, hA0mem, hcard2, res, fun t w => rfl⟩

private theorem line_action (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {b : M₀.E} (hbB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) :
    ∀ (l : ↥(LB M Q B)) (e : M₀.E), e ∈ M₀.img (Q ⊓ QB B) →
      ∃ c : K, φ ⟨(l : G), hc.LB_le_H0 l.2⟩ e - e = c • b := fun l => by
  simpa using (hc.LB_act_fix_line hD hbB l.2
    (T := (φ ⟨(l : G), hc.LB_le_H0 l.2⟩ : M₀.E →ₗ[K] M₀.E))
    (hφπ ⟨(l : G), hc.LB_le_H0 l.2⟩)).2

private theorem fix_of_mem_D (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hf : ∀ (l : ↥(LB M Q B)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
      (f l v : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (v : M₀.E))
    {W : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)} (D : AddSubgroup W)
    (hDmem : ∀ d : W, d ∈ D ↔ (d : M₀.E) ∈ M₀.img (Q ⊓ QB B))
    {A0 : Subgroup (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hA0mem : ∀ t, t ∈ A0 ↔ t ∈ f.range ∧ ∀ w ∈ W, t w ∈ W)
    {l : ↥(LB M Q B)} (hfl : f l ∈ A0) {d : W} (hd : d ∈ D)
    {b : M₀.E} {hbV : b ∈ cmComm M Q Z B K γ M₀ φ}
    {hbW : (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∉ W}
    (hbB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) :
    φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (d : M₀.E) = (d : M₀.E) := by
  obtain ⟨c, hc'⟩ := line_action hc hD φ hφπ hbB l (d : M₀.E) ((hDmem d).mp hd)
  have hA0W : ∀ w ∈ W, f l w ∈ W := (hA0mem (f l)).mp hfl |>.2
  have hflW : f l (d : ↥(cmComm M Q Z B K γ M₀ φ)) ∈ W := hA0W d d.2
  have hdiffW : (f l (d : ↥(cmComm M Q Z B K γ M₀ φ)) - d :
      ↥(cmComm M Q Z B K γ M₀ φ)) ∈ W := W.sub_mem hflW d.2
  have hcoe : ((f l (d : ↥(cmComm M Q Z B K γ M₀ φ)) - d :
      ↥(cmComm M Q Z B K γ M₀ φ)) : M₀.E) = c • b := by
    rw [Submodule.coe_sub, hf l (d : ↥(cmComm M Q Z B K γ M₀ φ)), hc']
  have hcW : c • (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∈ W := by
    have hEq : (f l (d : ↥(cmComm M Q Z B K γ M₀ φ)) - d :
        ↥(cmComm M Q Z B K γ M₀ φ)) =
        c • (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) := Subtype.ext hcoe
    rw [← hEq]
    exact hdiffW
  have hc0 : c = 0 := by
    by_contra hcne
    apply hbW
    have hEq : (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) =
        c⁻¹ • (c • (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ))) := by
      rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
    rw [hEq]
    exact W.smul_mem c⁻¹ hcW
  rw [hc0, zero_smul, sub_eq_zero] at hc'
  exact hc'

private theorem card_D_le_of_stabilizer (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hf : ∀ (l : ↥(LB M Q B)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
      (f l v : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (v : M₀.E))
    {W : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)} (D : AddSubgroup W)
    (hDmem : ∀ d : W, d ∈ D ↔ (d : M₀.E) ∈ M₀.img (Q ⊓ QB B))
    {A0 : Subgroup (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hA0mem : ∀ t, t ∈ A0 ↔ t ∈ f.range ∧ ∀ w ∈ W, t w ∈ W)
    (hA0eq : A0 = f.range) {b : M₀.E}
    {hbV : b ∈ cmComm M Q Z B K γ M₀ φ}
    {hbW : (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∉ W}
    (hbB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) :
    Nat.card D ≤ Nat.card K := by
  have hdeq : ∀ d : W, d ∈ D → d = 0 := by
    intro d hd
    have hfix : ∀ (l : G) (hl : l ∈ LB M Q B) (hlH : l ∈ H0 M Z),
        φ ⟨l, hlH⟩ (d : M₀.E) = (d : M₀.E) := by
      intro l hl hlH
      have hfl : f ⟨l, hl⟩ ∈ A0 := by rw [hA0eq]; exact ⟨⟨l, hl⟩, rfl⟩
      exact fix_of_mem_D hc hD φ hφπ hf D hDmem hA0mem hfl hd (hbV := hbV) (hbW := hbW) hbB
    obtain ⟨s, hs⟩ := hc.eq_smul_of_fixed_mem_img_inf_QB φ hφπ hbB ((hDmem d).mp hd) hfix
    by_contra hdne
    have hEq : (d : ↥(cmComm M Q Z B K γ M₀ φ)) = s • (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) :=
      Subtype.ext (by rw [hs]; rfl)
    have hsW : s • (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∈ W := by rw [← hEq]; exact d.2
    have hs0 : s = 0 := by
      by_contra hsne
      apply hbW
      have h2 : (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) =
          s⁻¹ • (s • (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ))) := by
        rw [smul_smul, inv_mul_cancel₀ hsne, one_smul]
      rw [h2]
      exact W.smul_mem s⁻¹ hsW
    exact hdne (Subtype.ext (by rw [hEq, hs0, zero_smul]; rfl))
  have hbot : D = ⊥ := by
    ext d
    constructor
    · intro hd
      exact AddSubgroup.mem_bot.mpr (hdeq d hd)
    · intro hd
      rw [AddSubgroup.mem_bot] at hd
      rw [hd]
      exact D.zero_mem
  rw [hbot]
  have h1 : Nat.card (⊥ : AddSubgroup W) = 1 := by simp
  rw [h1]
  exact Nat.card_pos (α := K)

private theorem card_D_le_of_swap (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hf : ∀ (l : ↥(LB M Q B)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
      (f l v : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (v : M₀.E))
    {W W' : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)} (hW : IsCompl W W')
    (D : AddSubgroup W)
    (hDmem : ∀ d : W, d ∈ D ↔ (d : M₀.E) ∈ M₀.img (Q ⊓ QB B))
    {s₀ : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)}
    (hs₀A : s₀ ∈ f.range)
    (hs₀swap : (∀ w ∈ W, s₀ w ∈ W') ∧ (∀ w ∈ W', s₀ w ∈ W))
    {b : M₀.E} (hbB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) :
    Nat.card D ≤ Nat.card K := by
  obtain ⟨l₀, hl₀⟩ := MonoidHom.mem_range.mp hs₀A
  have hg : ∀ d : D, ∃ c : K,
      φ ⟨(l₀ : G), hc.LB_le_H0 l₀.2⟩ (d.1 : M₀.E) - (d.1 : M₀.E) = c • b :=
    fun d => line_action hc hD φ hφπ hbB l₀ (d.1 : M₀.E) ((hDmem d.1).mp d.2)
  let g : D → K := fun d => Classical.choose (hg d)
  have hgspec : ∀ d : D,
      φ ⟨(l₀ : G), hc.LB_le_H0 l₀.2⟩ (d.1 : M₀.E) - (d.1 : M₀.E) = g d • b :=
    fun d => Classical.choose_spec (hg d)
  have hginj : Function.Injective g := by
    intro d d' hdd
    have h1 : φ ⟨(l₀ : G), hc.LB_le_H0 l₀.2⟩ (d.1 : M₀.E) - (d.1 : M₀.E) =
        φ ⟨(l₀ : G), hc.LB_le_H0 l₀.2⟩ (d'.1 : M₀.E) - (d'.1 : M₀.E) := by
      rw [hgspec d, hgspec d', hdd]
    have h2 : f l₀ ((d.1 : ↥(cmComm M Q Z B K γ M₀ φ)) - (d'.1 : ↥(cmComm M Q Z B K γ M₀ φ))) =
        (d.1 : ↥(cmComm M Q Z B K γ M₀ φ)) - (d'.1 : ↥(cmComm M Q Z B K γ M₀ φ)) := by
      apply Subtype.ext
      rw [hf l₀, Submodule.coe_sub, map_sub]
      rw [sub_eq_sub_iff_add_eq_add] at h1
      rw [sub_eq_sub_iff_add_eq_add, add_comm (d : M₀.E)
        ((φ ⟨(l₀ : G), hc.LB_le_H0 l₀.2⟩) (d' : M₀.E))]
      exact h1
    have hmemW : (d.1 : ↥(cmComm M Q Z B K γ M₀ φ)) -
        (d'.1 : ↥(cmComm M Q Z B K γ M₀ φ)) ∈ W := W.sub_mem d.1.2 d'.1.2
    have hmemW' : (d.1 : ↥(cmComm M Q Z B K γ M₀ φ)) -
        (d'.1 : ↥(cmComm M Q Z B K γ M₀ φ)) ∈ W' := by
      rw [← h2, hl₀]
      exact hs₀swap.1 _ hmemW
    have hzero : (d.1 : ↥(cmComm M Q Z B K γ M₀ φ)) -
        (d'.1 : ↥(cmComm M Q Z B K γ M₀ φ)) = 0 :=
      Submodule.disjoint_def.mp hW.disjoint _ hmemW hmemW'
    exact Subtype.ext (Subtype.ext (sub_eq_zero.mp hzero))
  exact (Nat.card_le_card_of_injective g hginj).trans (le_of_eq (Nat.card_congr
    (Equiv.refl K)))

private theorem card_D_le (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hf : ∀ (l : ↥(LB M Q B)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
      (f l v : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (v : M₀.E))
    {W W' : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)} (hW : IsCompl W W')
    (D : AddSubgroup W)
    (hDmem : ∀ d : W, d ∈ D ↔ (d : M₀.E) ∈ M₀.img (Q ⊓ QB B))
    {A0 : Subgroup (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hA0mem : ∀ t, t ∈ A0 ↔ t ∈ f.range ∧ ∀ w ∈ W, t w ∈ W)
    (hdich : ∀ t ∈ f.range, ((∀ w ∈ W, t w ∈ W) ∧ (∀ w ∈ W', t w ∈ W')) ∨
      ((∀ w ∈ W, t w ∈ W') ∧ (∀ w ∈ W', t w ∈ W)))
    {b : M₀.E} {hbV : b ∈ cmComm M Q Z B K γ M₀ φ}
    {hbW : (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∉ W}
    (hbB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) :
    Nat.card D ≤ Nat.card K := by
  by_cases hA0eq : A0 = f.range
  · exact card_D_le_of_stabilizer hc hD φ hφπ hf D hDmem hA0mem hA0eq (hbV := hbV) (hbW := hbW) hbB
  · have hle : A0 ≤ f.range := fun t ht => (hA0mem t).mp ht |>.1
    have hlt : A0 < f.range := lt_of_le_of_ne hle hA0eq
    obtain ⟨s₀, hs₀A, hs₀A0⟩ := SetLike.exists_of_lt hlt
    have hs₀not : ¬ ∀ w ∈ W, s₀ w ∈ W := fun h => hs₀A0 ((hA0mem s₀).mpr ⟨hs₀A, h⟩)
    have hs₀swap : (∀ w ∈ W, s₀ w ∈ W') ∧ (∀ w ∈ W', s₀ w ∈ W) := by
      rcases hdich s₀ hs₀A with h | h
      · exact absurd h.1 hs₀not
      · exact h
    exact card_D_le_of_swap hc hD φ hφπ hf hW D hDmem hs₀A hs₀swap hbB

private theorem exists_hyperplane (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {m : ℕ} {W : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)}
    (hWs : ∀ w ∈ W, cmCommQf B φ w = 0)
    (hdimV : Module.finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 2 * m)
    (hWfin : Module.finrank K W = m) {b : M₀.E}
    {hbV : b ∈ cmComm M Q Z B K γ M₀ φ}
    (hbW : (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∉ W) :
    ∃ H : Submodule K W, (∀ w : W, w ∈ H ↔ M₀.B (w : M₀.E) b = 0) ∧
      Module.finrank K H + 1 = Module.finrank K W := by
  let lin : W →ₗ[K] K :=
    (M₀.B.flip b).comp (((cmComm M Q Z B K γ M₀ φ).subtype).comp W.subtype)
  let H : Submodule K W := LinearMap.ker lin
  have hHmem : ∀ w : W, w ∈ H ↔ M₀.B (w : M₀.E) b = 0 := fun w => Iff.rfl
  have hexW : ∃ w ∈ W, M₀.B (w : M₀.E) b ≠ 0 :=
    exists_mem_B_ne_zero_of_not_mem hc hD φ hφπ hWs (by rw [hWfin, hdimV]) hbV hbW
  have hlinne : lin ≠ 0 := by
    obtain ⟨w, hw, hne⟩ := hexW
    intro h0
    exact hne (by
      have := congrArg (fun g : W →ₗ[K] K => g ⟨w, hw⟩) h0
      simpa [lin] using this)
  have hH : Module.finrank K H + 1 = Module.finrank K W := by
    change Module.finrank K (LinearMap.ker lin) + 1 = Module.finrank K W
    have hrange : LinearMap.range lin = ⊤ := by
      obtain ⟨w, hne⟩ : ∃ w : W, lin w ≠ 0 := by
        by_contra h
        apply hlinne
        ext w
        by_contra hw
        exact h ⟨w, hw⟩
      have hmem : lin w ∈ LinearMap.range lin := ⟨w, rfl⟩
      have h1 : (1 : K) ∈ LinearMap.range lin := by
        have h2 := (LinearMap.range lin).smul_mem (lin w)⁻¹ hmem
        simpa [inv_mul_cancel₀ hne] using h2
      rw [Submodule.eq_top_iff']
      intro x
      have h3 := (LinearMap.range lin).smul_mem x h1
      simpa using h3
    have h1 := LinearMap.finrank_range_add_finrank_ker lin
    rw [hrange, finrank_top, Module.finrank_self] at h1
    omega
  exact ⟨H, hHmem, hH⟩

private theorem flag_data (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hf : ∀ (l : ↥(LB M Q B)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
      (f l v : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (v : M₀.E))
    {W : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)}
    (A0 : Subgroup (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))) (res : A0 →* (W ≃ₗ[K] W))
    (H : Submodule K W) (D : AddSubgroup W)
    (hA0mem : ∀ t, t ∈ A0 ↔ t ∈ f.range ∧ ∀ w ∈ W, t w ∈ W)
    (hrescoe : ∀ (t : A0) (w : W), ((res t w : W) : ↥(cmComm M Q Z B K γ M₀ φ)) = t.1 w)
    (hDmem : ∀ d : W, d ∈ D ↔ (d : M₀.E) ∈ M₀.img (Q ⊓ QB B))
    {b : M₀.E} {hbV : b ∈ cmComm M Q Z B K γ M₀ φ}
    {hbW : (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∉ W}
    (hHmem : ∀ w : W, w ∈ H ↔ M₀.B (w : M₀.E) b = 0)
    (hbB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hbperp : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0) :
    (∀ t : A0, ∀ w : W, res t w - w ∈ H) ∧
      (∀ t : A0, ∀ h ∈ H, res t h - h ∈ D) ∧
      (∀ t : A0, ∀ d ∈ D, res t d = d) := by
  have hiso : ∀ (l : ↥(LB M Q B)) (x y : M₀.E),
      M₀.B (φ ⟨(l : G), hc.LB_le_H0 l.2⟩ x) (φ ⟨(l : G), hc.LB_le_H0 l.2⟩ y) = M₀.B x y :=
    fun l => (isometry_of_π hD ⟨(l : G), hc.LB_le_H0 l.2⟩ (hφπ _)).2
  have hb_fix : ∀ l : ↥(LB M Q B), φ ⟨(l : G), hc.LB_le_H0 l.2⟩ b = b := fun l => by
    simpa using (hc.LB_act_fix_line hD hbB l.2
      (T := (φ ⟨(l : G), hc.LB_le_H0 l.2⟩ : M₀.E →ₗ[K] M₀.E))
      (hφπ ⟨(l : G), hc.LB_le_H0 l.2⟩)).1
  have h1A0 : ∀ t : A0, ∀ w : W, res t w - w ∈ H := by
    intro t w
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp ((hA0mem t.1).mp t.2 |>.1)
    rw [hHmem]
    have hcoe : ((res t w - w : W) : M₀.E) =
        φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (w : M₀.E) - (w : M₀.E) := by
      rw [Submodule.coe_sub, Submodule.coe_sub, hrescoe t w, ← hl,
        hf l (w : ↥(cmComm M Q Z B K γ M₀ φ))]
    rw [hcoe]
    calc M₀.B (φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (w : M₀.E) - (w : M₀.E)) b =
        M₀.B (φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (w : M₀.E)) b - M₀.B (w : M₀.E) b := by
          rw [map_sub, LinearMap.sub_apply]
      _ = 0 := by
          have his := hiso l (w : M₀.E) b
          have his' : M₀.B (φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (w : M₀.E)) b =
              M₀.B (w : M₀.E) b := by
            simpa [hb_fix l] using his
          rw [his', sub_self]
  have h2A0 : ∀ t : A0, ∀ h : W, h ∈ H → res t h - h ∈ D := by
    intro t h hh
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp ((hA0mem t.1).mp t.2 |>.1)
    rw [hDmem]
    have hcoe : ((res t h - h : W) : M₀.E) =
        φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (h : M₀.E) - (h : M₀.E) := by
      rw [Submodule.coe_sub, Submodule.coe_sub, hrescoe t h, ← hl,
        hf l (h : ↥(cmComm M Q Z B K γ M₀ φ))]
    rw [hcoe]
    exact hc.map_sub_one_mem_img_inf_QB φ hφπ hbperp l.2 (hc.LB_le_H0 l.2) ((hHmem h).mp hh)
  have h3A0 : ∀ t : A0, ∀ d : W, d ∈ D → res t d = d := by
    intro t d hd
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp ((hA0mem t.1).mp t.2 |>.1)
    have hfix := fix_of_mem_D hc hD φ hφπ hf D hDmem hA0mem (l := l)
      (by rw [hl]; exact t.2) hd (hbV := hbV) (hbW := hbW) hbB
    apply Subtype.ext
    rw [hrescoe, ← hl]
    exact Subtype.ext ((hf l (d : ↥(cmComm M Q Z B K γ M₀ φ))).trans hfix)
  exact ⟨h1A0, h2A0, h3A0⟩

private theorem eq_one_of_fixes_of_preserves (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hf : ∀ (l : ↥(LB M Q B)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
      (f l v : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (v : M₀.E))
    {W W' : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)}
    (hW : IsCompl W W') (hWs : ∀ w ∈ W, cmCommQf B φ w = 0)
    {m : ℕ} (hdimV : Module.finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 2 * m)
    (hWfin : Module.finrank K W = m)
    {t : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)}
    (ht : t ∈ f.range) (hfix : ∀ w ∈ W, t w = w) (hpres : ∀ w ∈ W', t w ∈ W') :
    t = 1 := by
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp ht
  have hiso := (isometry_of_π hD ⟨(l : G), hc.LB_le_H0 l.2⟩ (hφπ _)).2
  have hfix' : ∀ w ∈ W', t w = w := by
    intro w' hw'
    have horth : t w' - w' ∈ W := by
      rw [← polarBilin_orthogonal_eq_self hc hD φ hφπ hWs (by rw [hWfin, hdimV])]
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro z hz
      rw [QuadraticMap.polarBilin_apply_apply, polar_cmCommQf]
      have hB1 : M₀.B (t w') (t z) = M₀.B (w' : M₀.E) (z : M₀.E) := by
        rw [← hl, hf l (w' : ↥(cmComm M Q Z B K γ M₀ φ)),
          hf l (z : ↥(cmComm M Q Z B K γ M₀ φ))]
        exact hiso (w' : M₀.E) (z : M₀.E)
      have hzfix : t z = z := hfix z hz
      rw [hzfix] at hB1
      have hB2 : M₀.B (z : M₀.E) (t w') = M₀.B (z : M₀.E) w' := by
        calc M₀.B (z : M₀.E) (t w') = -M₀.B (t w') (z : M₀.E) :=
              Tim79.QuadModel.B_comm (M₀ := M₀) z _
          _ = -M₀.B (w' : M₀.E) (z : M₀.E) := by rw [hB1]
          _ = M₀.B (z : M₀.E) w' := by
              rw [Tim79.QuadModel.B_comm (M₀ := M₀) w' z, neg_neg]
      rw [Submodule.coe_sub, map_sub, hB2]
      exact sub_self _
    have hmemW' : t w' - w' ∈ W' := W'.sub_mem (hpres w' hw') hw'
    have hzero : t w' - w' = 0 := Submodule.disjoint_def.mp hW.disjoint _ horth hmemW'
    exact sub_eq_zero.mp hzero
  ext v
  have hv : v ∈ W ⊔ W' := by rw [hW.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hfix w hw, hfix' w' hw']
  rfl

private theorem res_injective (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hf : ∀ (l : ↥(LB M Q B)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
      (f l v : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (v : M₀.E))
    {W W' : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)} (hW : IsCompl W W')
    (hWs : ∀ w ∈ W, cmCommQf B φ w = 0)
    {m : ℕ} (hm : 3 ≤ m)
    (hdimV : Module.finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 2 * m)
    (hWfin : Module.finrank K W = m)
    {A0 : Subgroup (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))} (res : A0 →* (W ≃ₗ[K] W))
    (hA0mem : ∀ t, t ∈ A0 ↔ t ∈ f.range ∧ ∀ w ∈ W, t w ∈ W)
    (hrescoe : ∀ (t : A0) (w : W), ((res t w : W) : ↥(cmComm M Q Z B K γ M₀ φ)) = t.1 w)
    (hdich : ∀ t ∈ f.range, ((∀ w ∈ W, t w ∈ W) ∧ (∀ w ∈ W', t w ∈ W')) ∨
      ((∀ w ∈ W, t w ∈ W') ∧ (∀ w ∈ W', t w ∈ W))) :
    Function.Injective res := by
  intro s t hst
  have h1 : res (s * t⁻¹) = 1 := by
    rw [map_mul, hst, map_inv]
    exact mul_inv_cancel (res t)
  have hfixW : ∀ w ∈ W, (s * t⁻¹).1 w = w := by
    intro w hw
    have hw' : res (s * t⁻¹) ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [h1]; rfl
    have h2 := congrArg (fun x : W => (x : ↥(cmComm M Q Z B K γ M₀ φ))) hw'
    rwa [hrescoe] at h2
  have hu : (s * t⁻¹).1 ∈ f.range := (hA0mem _).mp (s * t⁻¹).2 |>.1
  have huW' : ∀ w ∈ W', (s * t⁻¹).1 w ∈ W' := by
    have hd : ((∀ w ∈ W, (s * t⁻¹).1 w ∈ W) ∧
        (∀ w ∈ W', (s * t⁻¹).1 w ∈ W')) ∨
        ((∀ w ∈ W, (s * t⁻¹).1 w ∈ W') ∧
          (∀ w ∈ W', (s * t⁻¹).1 w ∈ W)) := hdich (s * t⁻¹).1 hu
    rcases hd with h | h
    · exact h.2
    · exfalso
      have hm3 : 3 ≤ m := hm
      have hpos : 0 < Module.finrank K W := by omega
      obtain ⟨w, hw0⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := W)).mp hpos
      have hmemW' : (w : ↥(cmComm M Q Z B K γ M₀ φ)) ∈ W' := by
        rw [← hfixW (w : ↥(cmComm M Q Z B K γ M₀ φ)) w.2]
        exact h.1 (w : ↥(cmComm M Q Z B K γ M₀ φ)) w.2
      have hzero : (w : ↥(cmComm M Q Z B K γ M₀ φ)) = 0 :=
        Submodule.disjoint_def.mp hW.disjoint _ w.2 hmemW'
      exact hw0 (Subtype.ext hzero)
  have hu1 : (s * t⁻¹).1 = 1 :=
    eq_one_of_fixes_of_preserves hc hD φ hφπ hf hW hWs hdimV hWfin hu hfixW huW'
  have : s * t⁻¹ = 1 := Subtype.ext hu1
  calc s = s * t⁻¹ * t := by group
    _ = t := by rw [this, one_mul]

private theorem count_of_summand (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {m : ℕ} (hm : 3 ≤ m)
    (f : ↥(LB M Q B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ)))
    (hfker : f.ker = Q.subgroupOf (LB M Q B))
    (hf : ∀ (l : ↥(LB M Q B)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
      (f l v : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 l.2⟩ (v : M₀.E))
    {W W' : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)} (hW : IsCompl W W')
    (hWs : ∀ w ∈ W, cmCommQf B φ w = 0)
    (hdimV : Module.finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 2 * m)
    (hWfin : Module.finrank K W = m)
    {b : M₀.E} (hbV : b ∈ cmComm M Q Z B K γ M₀ φ)
    (hbW : (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∉ W)
    (hbB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hbperp : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    (hdich : ∀ t ∈ f.range, ((∀ w ∈ W, t w ∈ W) ∧ (∀ w ∈ W', t w ∈ W')) ∨
      ((∀ w ∈ W, t w ∈ W') ∧ (∀ w ∈ W', t w ∈ W))) :
    Nat.card (bar M Q (LB M Q B)) ≤ 2 * Nat.card K ^ (m - 1) := by
  classical
  have hcardA : Nat.card f.range = Nat.card (bar M Q (LB M Q B)) :=
    card_range_eq_card_bar_of_ker hc φ f hfker
  obtain ⟨A0, hA0mem, hcard2, res, hrescoe⟩ := exists_stabilizer_res φ f hdich
  let D : AddSubgroup W := (M₀.img (Q ⊓ QB B)).comap
    (((cmComm M Q Z B K γ M₀ φ).subtype).comp W.subtype).toAddMonoidHom
  have hDmem : ∀ d : W, d ∈ D ↔ (d : M₀.E) ∈ M₀.img (Q ⊓ QB B) := fun d => by
    simp [D]
  have hDcard : Nat.card D ≤ Nat.card K :=
    card_D_le hc hD φ hφπ hf hW D hDmem hA0mem hdich (hbV := hbV) (hbW := hbW) hbB
  obtain ⟨H, hHmem, hH⟩ := exists_hyperplane hc hD φ hφπ hWs hdimV hWfin hbW
  obtain ⟨h1A0, h2A0, h3A0⟩ :=
    flag_data hc hD φ hφπ hf A0 res H D hA0mem hrescoe hDmem
      (hbV := hbV) (hbW := hbW) hHmem hbB hbperp
  let Ahat : Subgroup (W ≃ₗ[K] W) := res.range
  have h1D : ∀ t ∈ Ahat, ∀ w : W, t w - w ∈ H := by
    rintro _ ⟨t, rfl⟩ w
    exact h1A0 t w
  have h2D : ∀ t ∈ Ahat, ∀ h ∈ H, t h - h ∈ D := by
    rintro _ ⟨t, rfl⟩ h hh
    exact h2A0 t h hh
  have h3D : ∀ t ∈ Ahat, ∀ d ∈ D, t d = d := by
    rintro _ ⟨t, rfl⟩ d hd
    exact h3A0 t d hd
  obtain ⟨ℓ, hℓ, hℓH, h2ℓ, h3ℓ⟩ := exists_flag_line Ahat hDcard h1D h2D h3D
  have h2A0' : ∀ t : A0, ∀ h ∈ H, res t h - h ∈ ℓ := fun t h hh =>
    h2ℓ (res t) ⟨t, rfl⟩ h hh
  have h3A0' : ∀ t : A0, ∀ l ∈ ℓ, res t l = l := fun t l hl =>
    h3ℓ (res t) ⟨t, rfl⟩ l hl
  have hfaith : Function.Injective res :=
    res_injective hc hD φ hφπ hf hW hWs hm hdimV hWfin res hA0mem hrescoe hdich
  have hcomm : ∀ s t : A0, s.1 * t.1 = t.1 * s.1 := fun s t =>
    mul_comm_range hc φ f hfker s.1 ((hA0mem s.1).mp s.2 |>.1) t.1 ((hA0mem t.1).mp t.2 |>.1)
  haveI : Finite ↥W := Module.finite_of_finite K
  have hcardA0 : Nat.card A0 ≤ Nat.card K ^ (Module.finrank K W - 1) :=
    card_le_of_flag_restriction A0 res hfaith hcomm hH hℓ hℓH h1A0 h2A0' h3A0'
  rw [hWfin] at hcardA0
  calc Nat.card (bar M Q (LB M Q B)) = Nat.card f.range := hcardA.symm
    _ ≤ 2 * Nat.card A0 := hcard2
    _ ≤ 2 * Nat.card K ^ (m - 1) := Nat.mul_le_mul_left 2 hcardA0

theorem Ctx.exists_b_mem_cmComm (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) :
    ∃ b : M₀.E, b ≠ 0 ∧ b ∈ cmComm M Q Z B K γ M₀ φ ∧
      (∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) ∧
      (∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0) := by
  obtain ⟨b, hb0, -, hB, hperp, -⟩ := hc.dictB hD
  obtain ⟨a, haL, hA⟩ := ha2
  have haM : a ∈ M := hc.LB_le_M haL
  have haX : a ∈ XbarPre M Q Z B :=
    (mem_XbarPre_iff hc haM).mpr (mk_mem_Xbar_of_LB M Q Z B ⟨a, haM⟩ haL hA)
  have hBle : B ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z := hc.B_le_commutator_of_a2 haL hA
  have hzle : ⁅Q, Subgroup.zpowers a⁆ ≤ ⁅Q, XbarPre M Q Z B⁆ :=
    Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr haX)
  have hBle' : B ≤ Z ⊔ ⁅Q, XbarPre M Q Z B⁆ := by
    refine (hBle.trans (sup_le (hzle.trans le_sup_right) le_sup_left))
  have hbimg : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul K b).symm⟩
  obtain ⟨c, hcB, -, hcπ⟩ := M₀.mem_img.mp hbimg
  have hcQ : c ∈ Q := hc.le hcB
  refine ⟨b, hb0, ?_, hB, hperp⟩
  have hpi : c ∈ piPre M₀ (cmComm M Q Z B K γ M₀ φ) := by
    rw [piPre_cmComm_eq_sup_comm hc hD φ hφπ]
    exact hBle' hcB
  rw [← hcπ]
  exact hpi.2

theorem Ctx.cmComm_eq_top_of_rt1 (hc : Ctx M Q Z B) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {n m : ℕ} (hw : Width Q Z n)
    (hn : 1 ≤ n) (hm : 3 ≤ m) {σ₀ : SL(m, K) →* ↥(Xbar M Q Z B)}
    (hσ₀ : Function.Surjective σ₀)
    {ρ : SL(m, K) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ))}
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    {W₁ W₂ : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)} (hW : IsCompl W₁ W₂)
    (hW₁s : ∀ w ∈ W₁, cmCommQf B φ w = 0) (hW₂s : ∀ w ∈ W₂, cmCommQf B φ w = 0)
    (hdim₁ : Module.finrank K W₁ = m)
    (hdim : Module.finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 2 * m)
    {σ : K ≃+* K} {F : (Fin m → K) →+ ↥(cmComm M Q Z B K γ M₀ φ)}
    (hFσ : ∀ (c : K) x, F (c • x) = σ c • F x) (hFinj : Function.Injective F)
    (hFW : ∀ x, F x ∈ W₁) (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w)
    (hFeq : ∀ (g : SL(m, K)) x, F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = ρ g (F x))
    {σ' : K ≃+* K} {F' : (Fin m → K) →+ ↥(cmComm M Q Z B K γ M₀ φ)}
    (hF'σ : ∀ (c : K) x, F' (c • x) = σ' c • F' x) (hF'inj : Function.Injective F')
    (hF'W : ∀ x, F' x ∈ W₂) (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w)
    (hF'eq : ∀ (g : SL(m, K)) x,
      F' (((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)ᵀ *ᵥ x) = ρ g (F' x)) :
    m = n ∧ cmComm M Q Z B K γ M₀ φ = ⊤ := by
  classical
  obtain ⟨f, hfker, hf⟩ := exists_restrict_hom hc ha2 hD φ hφπ hφk
  obtain ⟨b, hb0, hbV, hbB, hbperp⟩ := hc.exists_b_mem_cmComm hD φ hφπ ha2
  have dich := summand_dichotomy hc φ hφk hm hσ₀ hρ f hf hW hFσ hFinj hFW hFsurj hFeq
    hF'σ hF'inj hF'W hF'surj hF'eq
  have hbound : Nat.card (bar M Q (LB M Q B)) ≤ 2 * Nat.card K ^ (m - 1) := by
    by_cases hb1 : (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∈ W₁
    · have hb2 : (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∉ W₂ := by
        intro h2
        have hzero := Submodule.disjoint_def.mp hW.disjoint _
          (show (⟨b, hbV⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∈ W₁ from hb1) h2
        exact hb0 (by simpa using congrArg Subtype.val hzero)
      have hfin₂ : Module.finrank K W₂ = m := finrank_eq_of_isCompl φ hW hdim₁ hdim
      refine count_of_summand hc hD φ hφπ hm f hfker hf hW.symm hW₂s hdim hfin₂
        hbV hb2 hbB hbperp ?_
      rintro _ ⟨l, rfl⟩
      rcases dich l with h | h
      · exact Or.inl ⟨h.2, h.1⟩
      · exact Or.inr ⟨h.2, h.1⟩
    · refine count_of_summand hc hD φ hφπ hm f hfker hf hW hW₁s hdim hdim₁
        hbV hb1 hbB hbperp ?_
      rintro _ ⟨l, rfl⟩
      exact dich l
  have hge : Nat.card K ^ (n - 1) ≤ Nat.card (bar M Q (LB M Q B)) := by
    rw [hD.card]
    exact hc.card_bar_LB_ge hw hn
  have hq4 : 4 ≤ Nat.card K := by rw [hD.card]; exact hc.hyp.q4
  have hlt : 2 * Nat.card K ^ (m - 1) < Nat.card K ^ m := by
    have hpos : 0 < Nat.card K ^ (m - 1) := pow_pos (by omega : 0 < Nat.card K) _
    have h2 : 2 < Nat.card K := by omega
    calc 2 * Nat.card K ^ (m - 1) < Nat.card K * Nat.card K ^ (m - 1) :=
          Nat.mul_lt_mul_of_pos_right h2 hpos
      _ = Nat.card K ^ m := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hnm : n ≤ m := by
    by_contra h
    have h1 : Nat.card K ^ m ≤ Nat.card K ^ (n - 1) := by
      refine Nat.pow_le_pow_right (by omega) (Nat.le_sub_one_of_lt (Nat.lt_of_not_le h))
    have h3 : Nat.card K ^ m ≤ 2 * Nat.card K ^ (m - 1) :=
      le_trans h1 (le_trans hge hbound)
    exact (not_lt_of_ge h3) hlt
  have hdimE : Module.finrank K M₀.E = 2 * n :=
    GlobalModelData.finrank_E hD hw (by omega)
  have hmn : m ≤ n := by
    have hle : 2 * m ≤ 2 * n := by
      calc 2 * m = Module.finrank K ↥(cmComm M Q Z B K γ M₀ φ) := hdim.symm
        _ ≤ Module.finrank K M₀.E := Submodule.finrank_le _
        _ = 2 * n := hdimE
    omega
  have hmn' : m = n := le_antisymm hmn hnm
  refine ⟨hmn', ?_⟩
  have hfin : Module.finrank K ↥(cmComm M Q Z B K γ M₀ φ) = Module.finrank K M₀.E := by
    rw [hdim, hmn', hdimE]
  exact Submodule.eq_top_of_finrank_eq hfin

end CFSG.RankThree.GF2n.Stroth80

end
