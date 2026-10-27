module

public import CFSG.Quasithin.Recognition.St84.Gen.D4qVertexOneDefs
import CFSG.Quasithin.Recognition.St84.Gen.D4qVertexOneModule
import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSpecial
import CFSG.Quasithin.Recognition.St84.Gen.SecRepForms
import CFSG.Quasithin.Recognition.St84.Gen.TorusEndTransfer
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6KProd

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Quasithin.H13.NFa2 CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.KProd
open scoped MatrixGroups commutatorElement

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
  {Q Z K H : Subgroup G} {Q' Z' K' H' : Subgroup G'} {f : ℕ}

private theorem secHyp_bot_of_data (hd : D4qVertexOneData Q Z K H f) :
    SecHyp (K ⊔ H) ⊥ Z where
  le := bot_le
  norm₀ := fun r _ => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top r
  norm₁ := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hd.conj_mem_center r hr z hz
    · intro hz
      have h := hd.conj_mem_center r⁻¹ ((K ⊔ H).inv_mem hr) (r * z * r⁻¹) hz
      have hEq : z = r⁻¹ * (r * z * r⁻¹) * r := by group
      rw [hEq]
      simpa using h
  normal := by
    intro z _
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top z
  comm := by
    intro a ha b hb
    rw [Subgroup.mem_bot]
    rw [hd.commute_of_mem a ha b (hd.le hb)]
    group
  sq := by
    intro a ha
    rw [Subgroup.mem_bot, ← pow_two]
    exact hd.sq_eq_one a ha

private theorem leviRep_bot_eq_one (hd : D4qVertexOneData Q Z K H f) {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] (s₀ : SecRep (K ⊔ H) ⊥ Z W) (k : ↥K) :
    s₀.ρ (Subgroup.inclusion le_sup_left k) = 1 := by
  ext x
  obtain ⟨z, rfl⟩ := s₀.exists_cl x
  let z' : ↥Z := ⟨(k : G) * z * (k : G)⁻¹, hd.conj_mem_center k (Subgroup.mem_sup_left k.2) z z.2⟩
  have hact : s₀.ρ (Subgroup.inclusion le_sup_left k) (s₀.cl z) = s₀.cl z' :=
    s₀.act (Subgroup.inclusion le_sup_left k) z z' rfl
  rw [hact]
  have hz' : z' = z := Subtype.ext (hd.levi_centralizes k k.2 z z.2)
  rw [hz']
  rfl

section Split

variable {W W₀ W' W₀' : Type}
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [Finite W₀]
  [AddCommGroup W'] [Module (ZMod 2) W'] [Finite W']
  [AddCommGroup W₀'] [Module (ZMod 2) W₀'] [Finite W₀']


private lemma f₀_K_equivariant (hd : D4qVertexOneData Q Z K H f)
    (hd' : D4qVertexOneData Q' Z' K' H' f) (s : SecRep (K ⊔ H) Z Q W)
    (s' : SecRep (K' ⊔ H') Z' Q' W') (e_K : ↥K ≃* ↥K')
    (he_K : e_K = hd.levi_mulEquiv.some.trans hd'.levi_mulEquiv.some.symm)
    (f₀ : W ≃ₗ[ZMod 2] W')
    (hf₀ : ∀ (g : SL(2, GaloisField 2 (3 * f))) (w : W),
      f₀ (D4qVertexOneData.leviRepSL hd s g w) =
        D4qVertexOneData.leviRepSL hd' s' g (f₀ w)) :
    ∀ (k : ↥K) (w : W), f₀ (s.ρ (Subgroup.inclusion le_sup_left k) w) =
      s'.ρ (Subgroup.inclusion le_sup_left (e_K k)) (f₀ w) := by
  intro k w
  have h1 : f₀ (s.ρ (Subgroup.inclusion le_sup_left k) w) =
      f₀ (D4qVertexOneData.leviRepSL hd s (hd.levi_mulEquiv.some k) w) := by
    rw [D4qVertexOneData.leviRepSL_apply]
    rfl
  have h2 : (D4qVertexOneData.leviRepSL hd' s' (hd.levi_mulEquiv.some k) :
        W' →ₗ[ZMod 2] W') =
      (s'.ρ (Subgroup.inclusion le_sup_left (e_K k)) : W' →ₗ[ZMod 2] W') := by
    have hk : hd'.levi_mulEquiv.some (e_K k) = hd.levi_mulEquiv.some k := by
      rw [he_K]
      simp
    rw [← hk, D4qVertexOneData.leviRepSL_apply]
    rfl
  calc f₀ (s.ρ (Subgroup.inclusion le_sup_left k) w)
      = f₀ (D4qVertexOneData.leviRepSL hd s (hd.levi_mulEquiv.some k) w) := h1
    _ = D4qVertexOneData.leviRepSL hd' s' (hd.levi_mulEquiv.some k) (f₀ w) :=
        hf₀ (hd.levi_mulEquiv.some k) w
    _ = s'.ρ (Subgroup.inclusion le_sup_left (e_K k)) (f₀ w) :=
        LinearMap.congr_fun h2 (f₀ w)

private lemma torus_injective (hd : D4qVertexOneData Q Z K H f)
    (s : SecRep (K ⊔ H) Z Q W) :
    Function.Injective (s.ρ.comp (Subgroup.inclusion le_sup_right) :
      ↥H →* (W ≃ₗ[ZMod 2] W)) := by
  intro h1 h2 hEq
  have hfix : (s.ρ.comp (Subgroup.inclusion le_sup_right)) (h1 * h2⁻¹) = 1 := by
    rw [map_mul, map_inv, hEq, mul_inv_cancel]
  have hcomm : ∀ x ∈ Q, (h1 * h2⁻¹) * x * (h1 * h2⁻¹)⁻¹ * x⁻¹ ∈ Z := by
    intro x hx
    have hxcl : s.ρ (Subgroup.inclusion le_sup_right (h1 * h2⁻¹)) (s.cl ⟨x, hx⟩) =
        s.cl ⟨x, hx⟩ := by
      have := congrArg (fun e : W ≃ₗ[ZMod 2] W => e (s.cl ⟨x, hx⟩)) hfix
      simpa using this
    exact (SecRep.fix_iff hd.secHyp s (Subgroup.inclusion le_sup_right (h1 * h2⁻¹))
      ⟨x, hx⟩).mp hxcl
  have h1eqG : ((h1 * h2⁻¹ : ↥H) : G) = 1 := hd.torus_faithful (h1 * h2⁻¹)
    (H.mul_mem h1.2 (H.inv_mem h2.2)) hcomm
  have h1eq : h1 * h2⁻¹ = 1 := Subtype.ext h1eqG
  exact mul_inv_eq_one.mp h1eq

private lemma torus_commutes (hd : D4qVertexOneData Q Z K H f)
    (s : SecRep (K ⊔ H) Z Q W) (h : ↥H) (k : ↥K) (w : W) :
    s.ρ (Subgroup.inclusion le_sup_right h)
        (s.ρ (Subgroup.inclusion le_sup_left k) w) =
      s.ρ (Subgroup.inclusion le_sup_left k)
        (s.ρ (Subgroup.inclusion le_sup_right h) w) := by
  have hcomm : Subgroup.inclusion le_sup_right h * Subgroup.inclusion le_sup_left k =
      Subgroup.inclusion le_sup_left k * Subgroup.inclusion le_sup_right h := by
    apply Subtype.ext
    exact (hd.levi_commute_torus k k.2 h h.2).symm
  have h1 := congrArg (fun e : W ≃ₗ[ZMod 2] W => e w) (congrArg s.ρ hcomm)
  change s.ρ (Subgroup.inclusion le_sup_right h)
      (s.ρ (Subgroup.inclusion le_sup_left k) w) =
    s.ρ (Subgroup.inclusion le_sup_left k)
      (s.ρ (Subgroup.inclusion le_sup_right h) w)
  simpa [map_mul, LinearEquiv.mul_apply] using h1

private lemma exists_e_H (hf : 2 ≤ f) (hd : D4qVertexOneData Q Z K H f)
    (hd' : D4qVertexOneData Q' Z' K' H' f) (s : SecRep (K ⊔ H) Z Q W)
    (s' : SecRep (K' ⊔ H') Z' Q' W') (e_K : ↥K ≃* ↥K')
    (he_K : e_K = hd.levi_mulEquiv.some.trans hd'.levi_mulEquiv.some.symm)
    (f₀ : W ≃ₗ[ZMod 2] W')
    (hf₀K : ∀ (k : ↥K) (w : W), f₀ (s.ρ (Subgroup.inclusion le_sup_left k) w) =
      s'.ρ (Subgroup.inclusion le_sup_left (e_K k)) (f₀ w)) :
    ∃ e_H : ↥H ≃* ↥H', ∀ (h : ↥H) (w : W),
      f₀ (s.ρ (Subgroup.inclusion le_sup_right h) w) =
        s'.ρ (Subgroup.inclusion le_sup_right (e_H h)) (f₀ w) := by
  let τ : ↥H →* (W ≃ₗ[ZMod 2] W) := s.ρ.comp (Subgroup.inclusion le_sup_right)
  let τ' : ↥H' →* (W' ≃ₗ[ZMod 2] W') := s'.ρ.comp (Subgroup.inclusion le_sup_right)
  have hτ : Function.Injective τ := by simpa [τ] using torus_injective hd s
  have hτ' : Function.Injective τ' := by simpa [τ'] using torus_injective hd' s'
  have hτρ : ∀ h k w, τ h (leviRep le_sup_left s k w) =
      leviRep le_sup_left s k (τ h w) := fun h k w => torus_commutes hd s h k w
  have hτρ' : ∀ h k w, τ' h (leviRep le_sup_left s' k w) =
      leviRep le_sup_left s' k (τ' h w) := fun h k w => torus_commutes hd' s' h k w
  have hcard_end : Nat.card (EndRing (leviRep le_sup_left s)) = 2 ^ f :=
    hd.card_endRing_leviRep hf s
  have hcard_end' : Nat.card (EndRing (leviRep le_sup_left s')) = 2 ^ f :=
    hd'.card_endRing_leviRep hf s'
  have hcard : Nat.card (EndRing (leviRep le_sup_left s)) = Nat.card H + 1 := by
    rw [hcard_end, hd.card_torus]
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  have hcard' : Nat.card (EndRing (leviRep le_sup_left s')) = Nat.card H' + 1 := by
    rw [hcard_end', hd'.card_torus]
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  haveI : Fact (leviRep le_sup_left s).IsIrreducible := ⟨hd.isIrreducible_leviRep hf s⟩
  haveI : Fact (leviRep le_sup_left s').IsIrreducible := ⟨hd'.isIrreducible_leviRep hf s'⟩
  obtain ⟨e_H, he_H⟩ := exists_mulEquiv_of_commute_of_card
    (leviRep le_sup_left s) (leviRep le_sup_left s') e_K f₀ hf₀K
    τ τ' hτ hτ' hτρ hτρ' hcard hcard'
  exact ⟨e_H, he_H⟩

private lemma exists_e (hd : D4qVertexOneData Q Z K H f)
    (hd' : D4qVertexOneData Q' Z' K' H' f) (e_K : ↥K ≃* ↥K') (e_H : ↥H ≃* ↥H') :
    ∃ e : ↥(K ⊔ H) ≃* ↥(K' ⊔ H'),
      (∀ (k : ↥K) (h : ↥H),
        e (prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus (k, h)) =
          prodEquivSup K' H' hd'.levi_commute_torus hd'.levi_inf_torus (e_K k, e_H h)) ∧
      (∀ k : ↥K, e (Subgroup.inclusion le_sup_left k) =
        Subgroup.inclusion le_sup_left (e_K k)) ∧
      (∀ h : ↥H, e (Subgroup.inclusion le_sup_right h) =
        Subgroup.inclusion le_sup_right (e_H h)) := by
  let e : ↥(K ⊔ H) ≃* ↥(K' ⊔ H') :=
    (prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus).symm.trans
      ((e_K.prodCongr e_H).trans
        (prodEquivSup K' H' hd'.levi_commute_torus hd'.levi_inf_torus))
  have he_apply : ∀ (k : ↥K) (h : ↥H),
      e (prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus (k, h)) =
        prodEquivSup K' H' hd'.levi_commute_torus hd'.levi_inf_torus (e_K k, e_H h) := by
    intro k h
    simp only [e, MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_apply]
    rfl
  have he_left : ∀ (k : ↥K),
      e (Subgroup.inclusion le_sup_left k) =
        Subgroup.inclusion le_sup_left (e_K k) := by
    intro k
    have h1 : (Subgroup.inclusion le_sup_left k : ↥(K ⊔ H)) =
        prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus (k, 1) := by
      apply Subtype.ext
      rw [prodEquivSup_apply]
      simp
    rw [h1, he_apply]
    apply Subtype.ext
    rw [prodEquivSup_apply]
    simp
  have he_right : ∀ (h : ↥H),
      e (Subgroup.inclusion le_sup_right h) =
        Subgroup.inclusion le_sup_right (e_H h) := by
    intro h
    have h1 : (Subgroup.inclusion le_sup_right h : ↥(K ⊔ H)) =
        prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus (1, h) := by
      apply Subtype.ext
      rw [prodEquivSup_apply]
      simp
    rw [h1, he_apply]
    apply Subtype.ext
    rw [prodEquivSup_apply]
    simp
  exact ⟨e, he_apply, he_left, he_right⟩

private lemma f₀_R_equivariant (hd : D4qVertexOneData Q Z K H f)
    (hd' : D4qVertexOneData Q' Z' K' H' f) (s : SecRep (K ⊔ H) Z Q W)
    (s' : SecRep (K' ⊔ H') Z' Q' W') (e_K : ↥K ≃* ↥K') (e_H : ↥H ≃* ↥H')
    (e : ↥(K ⊔ H) ≃* ↥(K' ⊔ H')) (f₀ : W ≃ₗ[ZMod 2] W')
    (hf₀K : ∀ (k : ↥K) (w : W), f₀ (s.ρ (Subgroup.inclusion le_sup_left k) w) =
      s'.ρ (Subgroup.inclusion le_sup_left (e_K k)) (f₀ w))
    (he_H : ∀ (h : ↥H) (w : W), f₀ (s.ρ (Subgroup.inclusion le_sup_right h) w) =
      s'.ρ (Subgroup.inclusion le_sup_right (e_H h)) (f₀ w))
    (he_apply : ∀ (k : ↥K) (h : ↥H),
      e (prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus (k, h)) =
        prodEquivSup K' H' hd'.levi_commute_torus hd'.levi_inf_torus (e_K k, e_H h)) :
    ∀ (r : ↥(K ⊔ H)) (w : W), f₀ (s.ρ r w) = s'.ρ (e r) (f₀ w) := by
  intro r w
  obtain ⟨⟨k, h⟩, rfl⟩ :=
    (prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus).surjective r
  have hr : (prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus (k, h) :
      ↥(K ⊔ H)) =
      Subgroup.inclusion le_sup_left k * Subgroup.inclusion le_sup_right h := by
    apply Subtype.ext
    rw [prodEquivSup_apply]
    rfl
  rw [hr, map_mul]
  change f₀ (s.ρ (Subgroup.inclusion le_sup_left k)
      (s.ρ (Subgroup.inclusion le_sup_right h) w)) =
    s'.ρ (e (prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus (k, h))) (f₀ w)
  rw [hf₀K k (s.ρ (Subgroup.inclusion le_sup_right h) w), he_H h w, he_apply k h]
  have hr' : (prodEquivSup K' H' hd'.levi_commute_torus hd'.levi_inf_torus (e_K k, e_H h) :
      ↥(K' ⊔ H')) =
      Subgroup.inclusion le_sup_left (e_K k) * Subgroup.inclusion le_sup_right (e_H h) := by
    apply Subtype.ext
    rw [prodEquivSup_apply]
    rfl
  rw [hr', map_mul]
  rfl

private lemma commForm_levi_inv (hd : D4qVertexOneData Q Z K H f)
    (s : SecRep (K ⊔ H) Z Q W) (s₀ : SecRep (K ⊔ H) (⊥ : Subgroup G) Z W₀)
    (hKZ : ∀ k : ↥K, s₀.ρ (Subgroup.inclusion le_sup_left k) = 1) :
    ∀ (k : ↥K) (x y : W),
      SecRep.commForm s s₀ hd.commute_of_mem hd.commutator_mem
        (s.ρ (Subgroup.inclusion le_sup_left k) x)
        (s.ρ (Subgroup.inclusion le_sup_left k) y) =
      SecRep.commForm s s₀ hd.commute_of_mem hd.commutator_mem x y := by
  intro k x y
  have h := SecRep.commForm_ρ hd.secHyp s s₀ hd.commute_of_mem hd.commutator_mem
    (Subgroup.inclusion le_sup_left k) x y
  rw [h, hKZ k]
  rfl

private lemma commForm_comp_inv (hd' : D4qVertexOneData Q' Z' K' H' f)
    (s : SecRep (K ⊔ H) Z Q W)
    (s' : SecRep (K' ⊔ H') Z' Q' W')
    (s₀' : SecRep (K' ⊔ H') (⊥ : Subgroup G') Z' W₀') (e_K : ↥K ≃* ↥K')
    (f₀ : W ≃ₗ[ZMod 2] W')
    (hf₀K : ∀ (k : ↥K) (w : W), f₀ (s.ρ (Subgroup.inclusion le_sup_left k) w) =
      s'.ρ (Subgroup.inclusion le_sup_left (e_K k)) (f₀ w)) :
    ∀ (k : ↥K) (x y : W),
      LinearMap.compl₁₂ (SecRep.commForm s' s₀' hd'.commute_of_mem hd'.commutator_mem) f₀ f₀
        (s.ρ (Subgroup.inclusion le_sup_left k) x)
        (s.ρ (Subgroup.inclusion le_sup_left k) y) =
      LinearMap.compl₁₂ (SecRep.commForm s' s₀' hd'.commute_of_mem hd'.commutator_mem) f₀ f₀
        x y := by
  intro k x y
  change SecRep.commForm s' s₀' hd'.commute_of_mem hd'.commutator_mem
      (f₀ (s.ρ (Subgroup.inclusion le_sup_left k) x))
      (f₀ (s.ρ (Subgroup.inclusion le_sup_left k) y)) =
    SecRep.commForm s' s₀' hd'.commute_of_mem hd'.commutator_mem (f₀ x) (f₀ y)
  rw [hf₀K k x, hf₀K k y]
  have h := SecRep.commForm_ρ hd'.secHyp s' s₀' hd'.commute_of_mem hd'.commutator_mem
    (Subgroup.inclusion le_sup_left (e_K k)) (f₀ x) (f₀ y)
  rw [h, leviRep_bot_eq_one hd' s₀' (e_K k)]
  rfl

private lemma exists_g₀ (hf : 2 ≤ f) (hd : D4qVertexOneData Q Z K H f)
    (hd' : D4qVertexOneData Q' Z' K' H' f) (s : SecRep (K ⊔ H) Z Q W)
    (s₀ : SecRep (K ⊔ H) (⊥ : Subgroup G) Z W₀)
    (s' : SecRep (K' ⊔ H') Z' Q' W')
    (s₀' : SecRep (K' ⊔ H') (⊥ : Subgroup G') Z' W₀')
    (e_K : ↥K ≃* ↥K') (f₀ : W ≃ₗ[ZMod 2] W')
    (hf₀K : ∀ (k : ↥K) (w : W), f₀ (s.ρ (Subgroup.inclusion le_sup_left k) w) =
      s'.ρ (Subgroup.inclusion le_sup_left (e_K k)) (f₀ w)) :
    ∃ g₀ : W₀ ≃ₗ[ZMod 2] W₀', ∀ x y,
      g₀ (SecRep.commForm s s₀ hd.commute_of_mem hd.commutator_mem x y) =
        SecRep.commForm s' s₀' hd'.commute_of_mem hd'.commutator_mem (f₀ x) (f₀ y) := by
  let c : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W₀ :=
    SecRep.commForm s s₀ hd.commute_of_mem hd.commutator_mem
  let c' : W' →ₗ[ZMod 2] W' →ₗ[ZMod 2] W₀' :=
    SecRep.commForm s' s₀' hd'.commute_of_mem hd'.commutator_mem
  let c'F : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W₀' := LinearMap.compl₁₂ c' f₀ f₀
  have hc_inv : ∀ (k : ↥K) (x y : W), c (s.ρ (Subgroup.inclusion le_sup_left k) x)
      (s.ρ (Subgroup.inclusion le_sup_left k) y) = c x y := by
    intro k x y
    simpa [c] using commForm_levi_inv hd s s₀ (fun k => leviRep_bot_eq_one hd s₀ k) k x y
  have hc'F_inv : ∀ (k : ↥K) (x y : W), c'F (s.ρ (Subgroup.inclusion le_sup_left k) x)
      (s.ρ (Subgroup.inclusion le_sup_left k) y) = c'F x y := by
    intro k x y
    simpa [c'F, c'] using commForm_comp_inv hd' s s' s₀' e_K f₀ hf₀K k x y
  have hgen : ⁅Q, Q⁆ = Z := by
    have h2f : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hd.centerOf_eq]
    exact (CFSG.Quasithin.H13.commutator_eq_centerOf_of_isSpecialPow
      (p := 2) (q := 2 ^ f) (w := 4) (by norm_num) h2f hd.special).1
  have hgen' : ⁅Q', Q'⁆ = Z' := by
    have h2f : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hd'.centerOf_eq]
    exact (CFSG.Quasithin.H13.commutator_eq_centerOf_of_isSpecialPow
      (p := 2) (q := 2 ^ f) (w := 4) (by norm_num) h2f hd'.special).1
  have hspan : Submodule.span (ZMod 2) (Set.range fun p : W × W => c p.1 p.2) = ⊤ :=
    SecRep.span_range_commForm s s₀ hd.commute_of_mem hd.commutator_mem hgen
  have hspan' : Submodule.span (ZMod 2) (Set.range fun p : W' × W' => c' p.1 p.2) = ⊤ :=
    SecRep.span_range_commForm s' s₀' hd'.commute_of_mem hd'.commutator_mem hgen'
  have hspan'F : Submodule.span (ZMod 2) (Set.range fun p : W × W => c'F p.1 p.2) = ⊤ := by
    have hrange : Set.range (fun p : W × W => c'F p.1 p.2) =
        Set.range (fun p : W' × W' => c' p.1 p.2) := by
      ext z
      constructor
      · rintro ⟨⟨x, y⟩, rfl⟩
        exact ⟨(f₀ x, f₀ y), rfl⟩
      · rintro ⟨⟨x, y⟩, rfl⟩
        obtain ⟨x', rfl⟩ := f₀.surjective x
        obtain ⟨y', rfl⟩ := f₀.surjective y
        exact ⟨(x', y'), rfl⟩
    rw [hrange, hspan']
  have hcardW₀ : Nat.card W₀ = 2 ^ f := by
    calc Nat.card W₀ = Nat.card (Multiplicative W₀) :=
          (Nat.card_congr Multiplicative.toAdd).symm
      _ = Nat.card Z := (Nat.card_congr (SecRep.equivOfBot s₀).toEquiv).symm
      _ = 2 ^ f := hd.card_center
  have hcardW₀' : Nat.card W₀' = 2 ^ f := by
    calc Nat.card W₀' = Nat.card (Multiplicative W₀') :=
          (Nat.card_congr Multiplicative.toAdd).symm
      _ = Nat.card Z' := (Nat.card_congr (SecRep.equivOfBot s₀').toEquiv).symm
      _ = 2 ^ f := hd'.card_center
  have hZZ' : Nat.card W₀ = Nat.card W₀' := by rw [hcardW₀, hcardW₀']
  have hcard_end : Nat.card (EndRing (leviRep le_sup_left s)) = 2 ^ f :=
    hd.card_endRing_leviRep hf s
  have hE : Nat.card (EndRing (leviRep le_sup_left s)) ≤ Nat.card W₀ := by
    rw [hcard_end, hcardW₀]
  haveI : Fact (leviRep le_sup_left s).IsIrreducible := ⟨hd.isIrreducible_leviRep hf s⟩
  obtain ⟨g₀, hg₀_add⟩ := exists_linearEquiv_comp_eq_of_invariant
    (leviRep le_sup_left s) hE hZZ' c c'F hc_inv hc'F_inv hspan hspan'F
  exact ⟨g₀, fun x y => by simpa [c, c', c'F] using hg₀_add x y⟩

private lemma g₀_H_equivariant (hf : 2 ≤ f) (hd : D4qVertexOneData Q Z K H f)
    (hd' : D4qVertexOneData Q' Z' K' H' f) (s : SecRep (K ⊔ H) Z Q W)
    (s₀ : SecRep (K ⊔ H) (⊥ : Subgroup G) Z W₀)
    (s' : SecRep (K' ⊔ H') Z' Q' W')
    (s₀' : SecRep (K' ⊔ H') (⊥ : Subgroup G') Z' W₀')
    (e_H : ↥H ≃* ↥H') (f₀ : W ≃ₗ[ZMod 2] W') (g₀ : W₀ ≃ₗ[ZMod 2] W₀')
    (hg₀_add' : ∀ x y,
      g₀ (SecRep.commForm s s₀ hd.commute_of_mem hd.commutator_mem x y) =
        SecRep.commForm s' s₀' hd'.commute_of_mem hd'.commutator_mem (f₀ x) (f₀ y))
    (he_H : ∀ (h : ↥H) (w : W), f₀ (s.ρ (Subgroup.inclusion le_sup_right h) w) =
      s'.ρ (Subgroup.inclusion le_sup_right (e_H h)) (f₀ w)) :
    ∀ (h : ↥H) (x : W₀),
      g₀ (s₀.ρ (Subgroup.inclusion le_sup_right h) x) =
        s₀'.ρ (Subgroup.inclusion le_sup_right (e_H h)) (g₀ x) := by
  let c : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W₀ :=
    SecRep.commForm s s₀ hd.commute_of_mem hd.commutator_mem
  let c' : W' →ₗ[ZMod 2] W' →ₗ[ZMod 2] W₀' :=
    SecRep.commForm s' s₀' hd'.commute_of_mem hd'.commutator_mem
  have hgen : ⁅Q, Q⁆ = Z := by
    have h2f : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ f)
    rw [← hd.centerOf_eq]
    exact (CFSG.Quasithin.H13.commutator_eq_centerOf_of_isSpecialPow
      (p := 2) (q := 2 ^ f) (w := 4) (by norm_num) h2f hd.special).1
  have hspan : Submodule.span (ZMod 2) (Set.range fun p : W × W => c p.1 p.2) = ⊤ :=
    SecRep.span_range_commForm s s₀ hd.commute_of_mem hd.commutator_mem hgen
  intro h x
  have hL : (g₀.toLinearMap.comp
        (s₀.ρ (Subgroup.inclusion le_sup_right h)).toLinearMap) =
      ((s₀'.ρ (Subgroup.inclusion le_sup_right (e_H h))).toLinearMap.comp g₀.toLinearMap) := by
    refine LinearMap.ext_on_range hspan ?_
    rintro ⟨y, z⟩
    change g₀ (s₀.ρ (Subgroup.inclusion le_sup_right h) (c y z)) =
      s₀'.ρ (Subgroup.inclusion le_sup_right (e_H h)) (g₀ (c y z))
    rw [← SecRep.commForm_ρ hd.secHyp s s₀ hd.commute_of_mem hd.commutator_mem
      (Subgroup.inclusion le_sup_right h) y z]
    rw [show g₀ (c (s.ρ (Subgroup.inclusion le_sup_right h) y)
        (s.ρ (Subgroup.inclusion le_sup_right h) z)) =
        c' (f₀ (s.ρ (Subgroup.inclusion le_sup_right h) y))
          (f₀ (s.ρ (Subgroup.inclusion le_sup_right h) z)) from hg₀_add' _ _]
    rw [he_H h y, he_H h z]
    change c' (s'.ρ (Subgroup.inclusion le_sup_right (e_H h)) (f₀ y))
        (s'.ρ (Subgroup.inclusion le_sup_right (e_H h)) (f₀ z)) =
      s₀'.ρ (Subgroup.inclusion le_sup_right (e_H h)) (g₀ (c y z))
    rw [SecRep.commForm_ρ hd'.secHyp s' s₀' hd'.commute_of_mem hd'.commutator_mem
      (Subgroup.inclusion le_sup_right (e_H h)) (f₀ y) (f₀ z)]
    rw [hg₀_add' y z]
  exact LinearMap.congr_fun hL x

private lemma g₀_R_equivariant (hd : D4qVertexOneData Q Z K H f)
    (hd' : D4qVertexOneData Q' Z' K' H' f) (s₀ : SecRep (K ⊔ H) (⊥ : Subgroup G) Z W₀)
    (s₀' : SecRep (K' ⊔ H') (⊥ : Subgroup G') Z' W₀')
    (e_K : ↥K ≃* ↥K') (e_H : ↥H ≃* ↥H') (e : ↥(K ⊔ H) ≃* ↥(K' ⊔ H'))
    (g₀ : W₀ ≃ₗ[ZMod 2] W₀')
    (hg₀H : ∀ (h : ↥H) (x : W₀), g₀ (s₀.ρ (Subgroup.inclusion le_sup_right h) x) =
      s₀'.ρ (Subgroup.inclusion le_sup_right (e_H h)) (g₀ x))
    (he_apply : ∀ (k : ↥K) (h : ↥H),
      e (prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus (k, h)) =
        prodEquivSup K' H' hd'.levi_commute_torus hd'.levi_inf_torus (e_K k, e_H h))
    (hKZ : ∀ k : ↥K, s₀.ρ (Subgroup.inclusion le_sup_left k) = 1)
    (hK'Z' : ∀ k : ↥K', s₀'.ρ (Subgroup.inclusion le_sup_left k) = 1) :
    ∀ (r : ↥(K ⊔ H)) (x : W₀), g₀ (s₀.ρ r x) = s₀'.ρ (e r) (g₀ x) := by
  intro r x
  obtain ⟨⟨k, h⟩, rfl⟩ :=
    (prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus).surjective r
  have hr : (prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus (k, h) :
      ↥(K ⊔ H)) =
      Subgroup.inclusion le_sup_left k * Subgroup.inclusion le_sup_right h := by
    apply Subtype.ext
    rw [prodEquivSup_apply]
    rfl
  rw [hr, map_mul]
  change g₀ (s₀.ρ (Subgroup.inclusion le_sup_left k)
      (s₀.ρ (Subgroup.inclusion le_sup_right h) x)) =
    s₀'.ρ (e (prodEquivSup K H hd.levi_commute_torus hd.levi_inf_torus (k, h))) (g₀ x)
  rw [he_apply k h]
  have hr' : (prodEquivSup K' H' hd'.levi_commute_torus hd'.levi_inf_torus (e_K k, e_H h) :
      ↥(K' ⊔ H')) =
      Subgroup.inclusion le_sup_left (e_K k) * Subgroup.inclusion le_sup_right (e_H h) := by
    apply Subtype.ext
    rw [prodEquivSup_apply]
    rfl
  rw [hr', map_mul]
  change g₀ (s₀.ρ (Subgroup.inclusion le_sup_left k)
      (s₀.ρ (Subgroup.inclusion le_sup_right h) x)) =
    s₀'.ρ (Subgroup.inclusion le_sup_left (e_K k))
      (s₀'.ρ (Subgroup.inclusion le_sup_right (e_H h)) (g₀ x))
  rw [hKZ k, hK'Z' (e_K k)]
  exact hg₀H h x

private lemma exists_g (s₀ : SecRep (K ⊔ H) (⊥ : Subgroup G) Z W₀)
    (s₀' : SecRep (K' ⊔ H') (⊥ : Subgroup G') Z' W₀') (g₀ : W₀ ≃ₗ[ZMod 2] W₀') :
    ∃ g : ↥Z ≃* ↥Z',
      (∀ z : ↥Z, SecRep.equivOfBot s₀' (g z) =
        Multiplicative.ofAdd (g₀ (s₀.cl z))) ∧
      (∀ (z : ↥Z) (z' : ↥Z'), g z = z' ↔ g₀ (s₀.cl z) = s₀'.cl z') := by
  let g₀Mul : Multiplicative W₀ ≃* Multiplicative W₀' :=
    { toFun := fun x => Multiplicative.ofAdd (g₀ (Multiplicative.toAdd x))
      invFun := fun y => Multiplicative.ofAdd (g₀.symm (Multiplicative.toAdd y))
      left_inv := fun x => by simp
      right_inv := fun y => by simp
      map_mul' := fun x y => by simp [map_add] }
  let g : ↥Z ≃* ↥Z' := (SecRep.equivOfBot s₀).trans (g₀Mul.trans (SecRep.equivOfBot s₀').symm)
  have hg_apply : ∀ z : ↥Z, SecRep.equivOfBot s₀' (g z) =
      Multiplicative.ofAdd (g₀ (s₀.cl z)) := by
    intro z
    simp [g, g₀Mul, MulEquiv.trans_apply, SecRep.equivOfBot_apply]
  have hg_iff : ∀ (z : ↥Z) (z' : ↥Z'), g z = z' ↔ g₀ (s₀.cl z) = s₀'.cl z' := by
    intro z z'
    have h2 : (SecRep.equivOfBot s₀' z' : Multiplicative W₀') =
        Multiplicative.ofAdd (s₀'.cl z') := by
      rw [SecRep.equivOfBot_apply]
      rfl
    constructor
    · intro h
      have h1 := congrArg (SecRep.equivOfBot s₀') h
      rw [hg_apply, h2] at h1
      exact Multiplicative.ofAdd.injective h1
    · intro h
      apply (SecRep.equivOfBot s₀').injective
      rw [hg_apply, h, ← h2]
  exact ⟨g, hg_apply, hg_iff⟩

private lemma g_cond (hd' : D4qVertexOneData Q' Z' K' H' f)
    (s₀ : SecRep (K ⊔ H) (⊥ : Subgroup G) Z W₀)
    (s₀' : SecRep (K' ⊔ H') (⊥ : Subgroup G') Z' W₀')
    (e : ↥(K ⊔ H) ≃* ↥(K' ⊔ H')) (g : ↥Z ≃* ↥Z') (g₀ : W₀ ≃ₗ[ZMod 2] W₀')
    (hg_apply : ∀ z : ↥Z, SecRep.equivOfBot s₀' (g z) =
      Multiplicative.ofAdd (g₀ (s₀.cl z)))
    (hg₀R : ∀ (r : ↥(K ⊔ H)) (x : W₀), g₀ (s₀.ρ r x) = s₀'.ρ (e r) (g₀ x)) :
    ∀ (r : ↥(K ⊔ H)) (z w : ↥Z), (w : G) = (r : G) * z * (r : G)⁻¹ →
      (g w : G') = (e r : G') * (g z : G') * (e r : G')⁻¹ := by
  intro r z w hw
  have hcl : s₀.cl w = s₀.ρ r (s₀.cl z) := (s₀.act r z w hw).symm
  have hgz : s₀'.cl (g z) = g₀ (s₀.cl z) := by
    have h := hg_apply z
    rw [SecRep.equivOfBot_apply] at h
    exact Multiplicative.ofAdd.injective (by simpa [SecRep.cl] using h)
  have hkey : SecRep.equivOfBot s₀' (g w) =
      Multiplicative.ofAdd (s₀'.ρ (e r) (s₀'.cl (g z))) := by
    calc SecRep.equivOfBot s₀' (g w) = Multiplicative.ofAdd (g₀ (s₀.cl w)) := hg_apply w
      _ = Multiplicative.ofAdd (g₀ (s₀.ρ r (s₀.cl z))) := by rw [hcl]
      _ = Multiplicative.ofAdd (s₀'.ρ (e r) (g₀ (s₀.cl z))) := by rw [hg₀R r]
      _ = Multiplicative.ofAdd (s₀'.ρ (e r) (s₀'.cl (g z))) := by rw [hgz]
  have hmem : (e r : G') * (g z : G') * (e r : G')⁻¹ ∈ Z' :=
    hd'.conj_mem_center (e r) (e r).2 (g z) (g z).2
  have hEq : g w = ⟨(e r : G') * (g z : G') * (e r : G')⁻¹, hmem⟩ := by
    apply (SecRep.equivOfBot s₀').injective
    rw [hkey, SecRep.equivOfBot_apply]
    change Multiplicative.ofAdd (s₀'.ρ (e r) (s₀'.cl (g z))) =
      Multiplicative.ofAdd (s₀'.cl ⟨_, hmem⟩)
    exact congrArg Multiplicative.ofAdd (s₀'.act (e r) (g z) ⟨_, hmem⟩ rfl)
  exact congrArg (fun y : ↥Z' => (y : G')) hEq

private lemma exists_fmap (s : SecRep (K ⊔ H) Z Q W)
    (s' : SecRep (K' ⊔ H') Z' Q' W') (f₀ : W ≃ₗ[ZMod 2] W')
    [hWn : (Z.subgroupOf Q).Normal] [hW'n : (Z'.subgroupOf Q').Normal] :
    ∃ fmap : ↥Q ⧸ Z.subgroupOf Q ≃* ↥Q' ⧸ Z'.subgroupOf Q',
      (∀ v : ↥Q, fmap (QuotientGroup.mk v) =
        (SecRep.quotEquiv s').symm (Multiplicative.ofAdd (f₀ (s.cl v)))) ∧
      (∀ (v : ↥Q) (v' : ↥Q'),
        fmap (QuotientGroup.mk v) = QuotientGroup.mk v' ↔ f₀ (s.cl v) = s'.cl v') := by
  let f₀Mul : Multiplicative W ≃* Multiplicative W' :=
    { toFun := fun x => Multiplicative.ofAdd (f₀ (Multiplicative.toAdd x))
      invFun := fun y => Multiplicative.ofAdd (f₀.symm (Multiplicative.toAdd y))
      left_inv := fun x => by simp
      right_inv := fun y => by simp
      map_mul' := fun x y => by simp [map_add] }
  let fmap : ↥Q ⧸ Z.subgroupOf Q ≃* ↥Q' ⧸ Z'.subgroupOf Q' :=
    (SecRep.quotEquiv s).trans (f₀Mul.trans (SecRep.quotEquiv s').symm)
  have hf_apply : ∀ v : ↥Q, fmap (QuotientGroup.mk v) =
      (SecRep.quotEquiv s').symm (Multiplicative.ofAdd (f₀ (s.cl v))) := by
    intro v
    simp [fmap, MulEquiv.trans_apply, f₀Mul, SecRep.quotEquiv_mk]
  have hf_iff : ∀ (v : ↥Q) (v' : ↥Q'),
      fmap (QuotientGroup.mk v) = QuotientGroup.mk v' ↔ f₀ (s.cl v) = s'.cl v' := by
    intro v v'
    rw [hf_apply]
    have h2 : (QuotientGroup.mk v' : ↥Q' ⧸ Z'.subgroupOf Q') =
        (SecRep.quotEquiv s').symm (Multiplicative.ofAdd (s'.cl v')) := by
      have hcls : Multiplicative.ofAdd (s'.cl v') = s'.cls v' := rfl
      rw [hcls, ← SecRep.quotEquiv_mk (s := s') v']
      rw [MulEquiv.symm_apply_apply]
    rw [h2]
    constructor
    · intro h
      have h1 := congrArg (SecRep.quotEquiv s') h
      simp only [MulEquiv.apply_symm_apply] at h1
      change Multiplicative.ofAdd (f₀ (s.cl v)) = Multiplicative.ofAdd (s'.cl v') at h1
      exact Multiplicative.ofAdd.injective h1
    · intro h
      rw [h]
  exact ⟨fmap, hf_apply, hf_iff⟩

private lemma f_cond (s : SecRep (K ⊔ H) Z Q W) (s' : SecRep (K' ⊔ H') Z' Q' W')
    [hWn : (Z.subgroupOf Q).Normal] [hW'n : (Z'.subgroupOf Q').Normal]
    (e : ↥(K ⊔ H) ≃* ↥(K' ⊔ H')) (f₀ : W ≃ₗ[ZMod 2] W')
    (fmap : ↥Q ⧸ Z.subgroupOf Q ≃* ↥Q' ⧸ Z'.subgroupOf Q')
    (hf₀R : ∀ (r : ↥(K ⊔ H)) (w : W), f₀ (s.ρ r w) = s'.ρ (e r) (f₀ w))
    (hf_iff : ∀ (v : ↥Q) (v' : ↥Q'),
      fmap (QuotientGroup.mk v) = QuotientGroup.mk v' ↔ f₀ (s.cl v) = s'.cl v') :
    ∀ (r : ↥(K ⊔ H)) (v w : ↥Q) (v' w' : ↥Q'),
      (w : G) = (r : G) * v * (r : G)⁻¹ →
      (w' : G') = (e r : G') * v' * (e r : G')⁻¹ →
      fmap (QuotientGroup.mk v) = QuotientGroup.mk v' →
      fmap (QuotientGroup.mk w) = QuotientGroup.mk w' := by
  intro r v w v' w' hw hw' hvv
  rw [hf_iff] at hvv ⊢
  have hclw : s.cl w = s.ρ r (s.cl v) := (s.act r v w hw).symm
  have hclw' : s'.cl w' = s'.ρ (e r) (s'.cl v') := (s'.act (e r) v' w' hw').symm
  calc f₀ (s.cl w) = f₀ (s.ρ r (s.cl v)) := by rw [hclw]
    _ = s'.ρ (e r) (f₀ (s.cl v)) := hf₀R r (s.cl v)
    _ = s'.ρ (e r) (s'.cl v') := by rw [hvv]
    _ = s'.cl w' := by rw [hclw']

private lemma sqMap_g₀_eq (hf : 2 ≤ f) (hd : D4qVertexOneData Q Z K H f)
    (hd' : D4qVertexOneData Q' Z' K' H' f) (s : SecRep (K ⊔ H) Z Q W)
    (s₀ : SecRep (K ⊔ H) (⊥ : Subgroup G) Z W₀)
    (s' : SecRep (K' ⊔ H') Z' Q' W')
    (s₀' : SecRep (K' ⊔ H') (⊥ : Subgroup G') Z' W₀')
    (e_K : ↥K ≃* ↥K') (f₀ : W ≃ₗ[ZMod 2] W') (g₀ : W₀ ≃ₗ[ZMod 2] W₀')
    (hf₀K : ∀ (k : ↥K) (w : W), f₀ (s.ρ (Subgroup.inclusion le_sup_left k) w) =
      s'.ρ (Subgroup.inclusion le_sup_left (e_K k)) (f₀ w))
    (hg₀_add' : ∀ x y,
      g₀ (SecRep.commForm s s₀ hd.commute_of_mem hd.commutator_mem x y) =
        SecRep.commForm s' s₀' hd'.commute_of_mem hd'.commutator_mem (f₀ x) (f₀ y))
    (hKZ : ∀ k : ↥K, s₀.ρ (Subgroup.inclusion le_sup_left k) = 1)
    (hK'Z' : ∀ k : ↥K', s₀'.ρ (Subgroup.inclusion le_sup_left k) = 1) :
    ∀ v : W,
      g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one v) =
        SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (f₀ v) := by
  let sq : W → W₀ := SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one
  let sq' : W' → W₀' := SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one
  let δfun : W → W₀' := fun x => g₀ (sq x) - sq' (f₀ x)
  have hsq0 : sq 0 = 0 := by
    have h := SecRep.sqMap_cl s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one (1 : ↥Q)
    have h1 : s.cl (1 : ↥Q) = 0 := by simp [SecRep.cl]
    have h2 : (⟨((1 : ↥Q) : G) ^ 2, hd.sq_mem 1 (1 : ↥Q).2⟩ : ↥Z) = 1 := by
      apply Subtype.ext
      simp
    rw [h1, h2] at h
    simpa [sq, SecRep.cl] using h
  have hsq0' : sq' 0 = 0 := by
    have h := SecRep.sqMap_cl s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (1 : ↥Q')
    have h1 : s'.cl (1 : ↥Q') = 0 := by simp [SecRep.cl]
    have h2 : (⟨((1 : ↥Q') : G') ^ 2, hd'.sq_mem 1 (1 : ↥Q').2⟩ : ↥Z') = 1 := by
      apply Subtype.ext
      simp
    rw [h1, h2] at h
    simpa [sq', SecRep.cl] using h
  have hδadd : ∀ x y, δfun (x + y) = δfun x + δfun y := by
    intro x y
    have h1 := SecRep.sqMap_add s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one
      hd.commutator_mem x y
    have h2 := SecRep.sqMap_add s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one
      hd'.commutator_mem (f₀ x) (f₀ y)
    have h3 : f₀ (x + y) = f₀ x + f₀ y := map_add f₀ x y
    change g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one (x + y)) -
        SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (f₀ (x + y)) =
      (g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one x) -
        SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (f₀ x)) +
      (g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one y) -
        SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (f₀ y))
    rw [h1, h3, h2]
    have h4 : g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one x +
        SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one y +
        (SecRep.commForm s s₀ hd.commute_of_mem hd.commutator_mem) x y) =
        g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one x) +
        g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one y) +
        g₀ ((SecRep.commForm s s₀ hd.commute_of_mem hd.commutator_mem) x y) := by
      rw [map_add, map_add]
    rw [h4, hg₀_add' x y]
    abel
  let δadd : W →+ W₀' :=
    { toFun := δfun, map_zero' := by simp [δfun, hsq0, hsq0'], map_add' := hδadd }
  let δ : W →ₗ[ZMod 2] W₀' := δadd.toZModLinearMap 2
  have hδinv : ∀ k x, δ (s.ρ (Subgroup.inclusion le_sup_left k) x) = δ x := by
    intro k x
    show δfun (s.ρ (Subgroup.inclusion le_sup_left k) x) = δfun x
    change g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one
        (s.ρ (Subgroup.inclusion le_sup_left k) x)) -
        SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one
          (f₀ (s.ρ (Subgroup.inclusion le_sup_left k) x)) =
      g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one x) -
        SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (f₀ x)
    have hsqρ : SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one
        (s.ρ (Subgroup.inclusion le_sup_left k) x) =
        s₀.ρ (Subgroup.inclusion le_sup_left k)
          (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one x) := by
      have h := SecRep.sqMap_ρ hd.secHyp s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one
        (Subgroup.inclusion le_sup_left k) x
      simpa [leviRep] using h
    have hsqρ' : SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one
        (f₀ (s.ρ (Subgroup.inclusion le_sup_left k) x)) =
        SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one
          (s'.ρ (Subgroup.inclusion le_sup_left (e_K k)) (f₀ x)) := by
      rw [hf₀K k x]
    have hsqρ'' : SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one
        (s'.ρ (Subgroup.inclusion le_sup_left (e_K k)) (f₀ x)) =
        s₀'.ρ (Subgroup.inclusion le_sup_left (e_K k))
          (SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (f₀ x)) := by
      have h := SecRep.sqMap_ρ hd'.secHyp s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one
        (Subgroup.inclusion le_sup_left (e_K k)) (f₀ x)
      simpa [leviRep] using h
    rw [hsqρ, hsqρ', hsqρ'', hKZ k, hK'Z' (e_K k)]
    rfl
  have hntρ : ∃ k : ↥K, leviRep le_sup_left s k ≠ 1 := hd.exists_leviRep_ne_one hf s
  haveI : Fact (leviRep le_sup_left s).IsIrreducible := ⟨hd.isIrreducible_leviRep hf s⟩
  have hδzero : δ = 0 := eq_zero_of_invariant_linearMap (leviRep le_sup_left s) hntρ δ hδinv
  intro v
  have h := congrArg (fun L : W →ₗ[ZMod 2] W₀' => L v) hδzero
  have h0 : g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one v) -
      SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (f₀ v) = 0 := by
    simpa [δ, δadd, δfun, sq, sq'] using h
  exact sub_eq_zero.mp h0

private lemma hsq_cond (hd : D4qVertexOneData Q Z K H f)
    (hd' : D4qVertexOneData Q' Z' K' H' f)
    (s : SecRep (K ⊔ H) Z Q W) (s₀ : SecRep (K ⊔ H) (⊥ : Subgroup G) Z W₀)
    (s' : SecRep (K' ⊔ H') Z' Q' W')
    (s₀' : SecRep (K' ⊔ H') (⊥ : Subgroup G') Z' W₀')
    [hWn : (Z.subgroupOf Q).Normal] [hW'n : (Z'.subgroupOf Q').Normal]
    (e_H : ↥H ≃* ↥H') (f₀ : W ≃ₗ[ZMod 2] W')
    (fmap : ↥Q ⧸ Z.subgroupOf Q ≃* ↥Q' ⧸ Z'.subgroupOf Q')
    (g : ↥Z ≃* ↥Z') (g₀ : W₀ ≃ₗ[ZMod 2] W₀')
    (hg_apply : ∀ z : ↥Z, SecRep.equivOfBot s₀' (g z) =
      Multiplicative.ofAdd (g₀ (s₀.cl z)))
    (hsq_eq : ∀ v : W,
      g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one v) =
        SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (f₀ v))
    (hf_iff : ∀ (v : ↥Q) (v' : ↥Q'),
      fmap (QuotientGroup.mk v) = QuotientGroup.mk v' ↔ f₀ (s.cl v) = s'.cl v') :
    ∀ (v : ↥Q) (v' : ↥Q'), fmap (QuotientGroup.mk v) = QuotientGroup.mk v' →
      ∀ hz : (v : G) ^ 2 ∈ Z, (g ⟨(v : G) ^ 2, hz⟩ : G') = (v' : G') ^ 2 := by
  intro v v' hvv hz
  have hfv : f₀ (s.cl v) = s'.cl v' := (hf_iff v v').mp hvv
  have hδv : g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one (s.cl v)) =
      SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (f₀ (s.cl v)) :=
    hsq_eq (s.cl v)
  have hsqv : SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one (s.cl v) =
      s₀.cl ⟨(v : G) ^ 2, hd.sq_mem v v.2⟩ :=
    SecRep.sqMap_cl s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one v
  have hsqv' : SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (s'.cl v') =
      s₀'.cl ⟨(v' : G') ^ 2, hd'.sq_mem v' v'.2⟩ :=
    SecRep.sqMap_cl s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one v'
  have hEq : g ⟨(v : G) ^ 2, hz⟩ = ⟨(v' : G') ^ 2, hd'.sq_mem v' v'.2⟩ := by
    apply (SecRep.equivOfBot s₀').injective
    calc SecRep.equivOfBot s₀' (g ⟨(v : G) ^ 2, hz⟩)
        = Multiplicative.ofAdd (g₀ (s₀.cl ⟨(v : G) ^ 2, hz⟩)) := hg_apply _
      _ = Multiplicative.ofAdd
            (g₀ (SecRep.sqMap s s₀ hd.commute_of_mem hd.sq_mem hd.sq_eq_one (s.cl v))) := by
          congr 2
          have hzeq : (⟨(v : G) ^ 2, hz⟩ : ↥Z) =
              ⟨(v : G) ^ 2, hd.sq_mem v v.2⟩ := Subtype.ext rfl
          rw [hzeq, ← hsqv]
      _ = Multiplicative.ofAdd
            (SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (f₀ (s.cl v))) := by
          rw [hδv]
      _ = Multiplicative.ofAdd
            (SecRep.sqMap s' s₀' hd'.commute_of_mem hd'.sq_mem hd'.sq_eq_one (s'.cl v')) := by
          rw [hfv]
      _ = Multiplicative.ofAdd (s₀'.cl ⟨(v' : G') ^ 2, hd'.sq_mem v' v'.2⟩) := by rw [hsqv']
      _ = SecRep.equivOfBot s₀' ⟨(v' : G') ^ 2, hd'.sq_mem v' v'.2⟩ := by
          rw [SecRep.equivOfBot_apply]
          rfl
  exact congrArg (fun y : ↥Z' => (y : G')) hEq

private lemma crossedHomPrincipal_data (hf : 2 ≤ f) (hd : D4qVertexOneData Q Z K H f)
    (hd' : D4qVertexOneData Q' Z' K' H' f) (e_K : ↥K ≃* ↥K')
    (e : ↥(K ⊔ H) ≃* ↥(K' ⊔ H'))
    (he_left : ∀ k : ↥K, e (Subgroup.inclusion le_sup_left k) =
      Subgroup.inclusion le_sup_left (e_K k)) :
    CrossedHomPrincipal Q Z (K ⊔ H) Z' (K' ⊔ H') e := by
  refine hd.crossedHomPrincipal hf e hd'.conj_mem_center (fun a ha b hb =>
    hd'.commute_of_mem a ha b (hd'.le hb)) hd'.sq_eq_one ?_
  intro k hk z hz
  have hk' : (e k : G') = (e_K ⟨(k : G), hk⟩ : G') := by
    have h1 : (k : ↥(K ⊔ H)) = Subgroup.inclusion le_sup_left ⟨(k : G), hk⟩ := rfl
    have h2 := congrArg Subtype.val (he_left ⟨(k : G), hk⟩)
    rw [← h1] at h2
    exact h2
  rw [hk']
  exact hd'.levi_centralizes (e_K ⟨(k : G), hk⟩) (e_K ⟨(k : G), hk⟩).2 z hz

private lemma mem_iff_of_restrict {G G' : Type*} [Group G] [Group G']
    {P A : Subgroup G} {P' A' : Subgroup G'} (hA : A ≤ P) (ψ : ↥P ≃* ↥P')
    (θ : ↥A ≃* ↥A') (hψ : ∀ a : ↥A, (ψ ⟨a, hA a.2⟩ : G') = θ a) (x : ↥P) :
    (x : G) ∈ A ↔ (ψ x : G') ∈ A' := by
  constructor
  · intro hx
    rw [show (ψ x : G') = θ ⟨x, hx⟩ from hψ ⟨x, hx⟩]
    exact (θ ⟨x, hx⟩).2
  · intro hx
    let a : ↥A := θ.symm ⟨(ψ x : G'), hx⟩
    have ha : (ψ ⟨a, hA a.2⟩ : G') = (ψ x : G') := by
      rw [hψ a]
      exact congrArg Subtype.val (θ.apply_symm_apply _)
    have hxeq : (⟨a, hA a.2⟩ : ↥P) = x := ψ.injective (Subtype.ext ha)
    have hxa : (x : G) = (a : G) := by rw [← hxeq]
    rw [hxa]
    exact a.2

private lemma assemble (hd : D4qVertexOneData Q Z K H f)
    (hd' : D4qVertexOneData Q' Z' K' H' f) (e : ↥(K ⊔ H) ≃* ↥(K' ⊔ H'))
    [hWn : (Z.subgroupOf Q).Normal] [hW'n : (Z'.subgroupOf Q').Normal]
    (fmap : ↥Q ⧸ Z.subgroupOf Q ≃* ↥Q' ⧸ Z'.subgroupOf Q')
    (g : ↥Z ≃* ↥Z')
    (hf_cond : ∀ (r : ↥(K ⊔ H)) (v w : ↥Q) (v' w' : ↥Q'),
      (w : G) = (r : G) * v * (r : G)⁻¹ →
      (w' : G') = (e r : G') * v' * (e r : G')⁻¹ →
      fmap (QuotientGroup.mk v) = QuotientGroup.mk v' →
      fmap (QuotientGroup.mk w) = QuotientGroup.mk w')
    (hg_cond : ∀ (r : ↥(K ⊔ H)) (z w : ↥Z), (w : G) = (r : G) * z * (r : G)⁻¹ →
      (g w : G') = (e r : G') * (g z : G') * (e r : G')⁻¹)
    (hsq_cond : ∀ (v : ↥Q) (v' : ↥Q'),
      fmap (QuotientGroup.mk v) = QuotientGroup.mk v' →
      ∀ hz : (v : G) ^ 2 ∈ Z, (g ⟨(v : G) ^ 2, hz⟩ : G') = (v' : G') ^ 2)
    (hH1 : CrossedHomPrincipal Q Z (K ⊔ H) Z' (K' ⊔ H') e)
    (e_K : ↥K ≃* ↥K') (e_H : ↥H ≃* ↥H')
    (he_left : ∀ k : ↥K, e (Subgroup.inclusion le_sup_left k) =
      Subgroup.inclusion le_sup_left (e_K k))
    (he_right : ∀ h : ↥H, e (Subgroup.inclusion le_sup_right h) =
      Subgroup.inclusion le_sup_right (e_H h)) :
    ∃ ψ : ↥(Q ⊔ (K ⊔ H)) ≃* ↥(Q' ⊔ (K' ⊔ H')),
      (∀ x : ↥(Q ⊔ (K ⊔ H)), (x : G) ∈ Q ↔ (ψ x : G') ∈ Q') ∧
      (∀ x : ↥(Q ⊔ (K ⊔ H)), (x : G) ∈ K ↔ (ψ x : G') ∈ K') ∧
      (∀ x : ↥(Q ⊔ (K ⊔ H)), (x : G) ∈ H ↔ (ψ x : G') ∈ H') := by
  obtain ⟨θ, ψ, hψQ, hψR, -⟩ := exists_vertexIso_special hd.le_normalizer hd.disjoint
    hd'.le_normalizer hd'.disjoint hd.le hd.commute_of_mem hd.sq_eq_one hd.sq_mem
    hd.conj_mem_center hd'.le hd'.commute_of_mem hd'.sq_eq_one hd'.sq_mem hd'.conj_mem_center
    e fmap g hf_cond hg_cond hsq_cond hH1
  have hKP : K ≤ Q ⊔ (K ⊔ H) := le_sup_left.trans le_sup_right
  have hHP : H ≤ Q ⊔ (K ⊔ H) := le_sup_right.trans le_sup_right
  have hψK : ∀ k : ↥K, (ψ ⟨k, hKP k.2⟩ : G') = e_K k := fun k => by
    have h := hψR (Subgroup.inclusion le_sup_left k)
    rw [he_left] at h
    exact h
  have hψH : ∀ h : ↥H, (ψ ⟨h, hHP h.2⟩ : G') = e_H h := fun h => by
    have h' := hψR (Subgroup.inclusion le_sup_right h)
    rw [he_right] at h'
    exact h'
  exact ⟨ψ, mem_iff_of_restrict le_sup_left ψ θ hψQ, mem_iff_of_restrict hKP ψ e_K hψK,
    mem_iff_of_restrict hHP ψ e_H hψH⟩

end Split

theorem D4qVertexOneData.exists_mulEquiv (hf : 2 ≤ f) (hd : D4qVertexOneData Q Z K H f)
    (hd' : D4qVertexOneData Q' Z' K' H' f) :
    ∃ ψ : ↥(Q ⊔ (K ⊔ H)) ≃* ↥(Q' ⊔ (K' ⊔ H')),
      (∀ x : ↥(Q ⊔ (K ⊔ H)), (x : G) ∈ Q ↔ (ψ x : G') ∈ Q') ∧
      (∀ x : ↥(Q ⊔ (K ⊔ H)), (x : G) ∈ K ↔ (ψ x : G') ∈ K') ∧
      (∀ x : ↥(Q ⊔ (K ⊔ H)), (x : G) ∈ H ↔ (ψ x : G') ∈ H') := by
  classical
  obtain ⟨W, hWadd, hWmod, hWfin, ⟨s⟩⟩ := exists_secRep hd.secHyp
  letI : AddCommGroup W := hWadd
  letI : Module (ZMod 2) W := hWmod
  letI : Finite W := hWfin
  obtain ⟨W₀, hW₀add, hW₀mod, hW₀fin, ⟨s₀⟩⟩ :=
    exists_secRep (secHyp_bot_of_data hd)
  letI : AddCommGroup W₀ := hW₀add
  letI : Module (ZMod 2) W₀ := hW₀mod
  letI : Finite W₀ := hW₀fin
  obtain ⟨W', hW'add, hW'mod, hW'fin, ⟨s'⟩⟩ := exists_secRep hd'.secHyp
  letI : AddCommGroup W' := hW'add
  letI : Module (ZMod 2) W' := hW'mod
  letI : Finite W' := hW'fin
  obtain ⟨W₀', hW₀'add, hW₀'mod, hW₀'fin, ⟨s₀'⟩⟩ :=
    exists_secRep (secHyp_bot_of_data hd')
  letI : AddCommGroup W₀' := hW₀'add
  letI : Module (ZMod 2) W₀' := hW₀'mod
  letI : Finite W₀' := hW₀'fin
  letI hWn : (Z.subgroupOf Q).Normal := SecRep.normal_subgroupOf s
  letI hW'n : (Z'.subgroupOf Q').Normal := SecRep.normal_subgroupOf s'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (GaloisField 2 (3 * f)) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 (3 * f)) = 2 ^ (3 * f) := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 (3 * f) (by omega)
  haveI : Fact (hd.leviRepSL s).IsIrreducible := ⟨hd.isIrreducible_leviRepSL hf s⟩
  haveI : Fact (hd'.leviRepSL s').IsIrreducible := ⟨hd'.isIrreducible_leviRepSL hf s'⟩
  obtain ⟨f₀, hf₀⟩ := exists_equiv_of_card_eq_two_pow_eight_mul hf hF (hd.leviRepSL s)
    (hd'.leviRepSL s') (hd.exists_leviRepSL_ne_one hf s) (hd'.exists_leviRepSL_ne_one hf s')
    (hd.card_secRep s) (hd'.card_secRep s')
  let e_K : ↥K ≃* ↥K' := hd.levi_mulEquiv.some.trans hd'.levi_mulEquiv.some.symm
  have hf₀K : ∀ (k : ↥K) (w : W), f₀ (s.ρ (Subgroup.inclusion le_sup_left k) w) =
      s'.ρ (Subgroup.inclusion le_sup_left (e_K k)) (f₀ w) :=
    f₀_K_equivariant hd hd' s s' e_K rfl f₀ hf₀
  obtain ⟨e_H, he_H⟩ := exists_e_H hf hd hd' s s' e_K rfl f₀ hf₀K
  obtain ⟨e, he_apply, he_left, he_right⟩ := exists_e hd hd' e_K e_H
  have hf₀R := f₀_R_equivariant hd hd' s s' e_K e_H e f₀ hf₀K he_H he_apply
  have hKZ : ∀ k : ↥K, s₀.ρ (Subgroup.inclusion le_sup_left k) = 1 :=
    fun k => leviRep_bot_eq_one hd s₀ k
  have hK'Z' : ∀ k : ↥K', s₀'.ρ (Subgroup.inclusion le_sup_left k) = 1 :=
    fun k => leviRep_bot_eq_one hd' s₀' k
  obtain ⟨g₀, hg₀_add'⟩ := exists_g₀ hf hd hd' s s₀ s' s₀' e_K f₀ hf₀K
  have hg₀H := g₀_H_equivariant hf hd hd' s s₀ s' s₀' e_H f₀ g₀ hg₀_add' he_H
  have hg₀R := g₀_R_equivariant hd hd' s₀ s₀' e_K e_H e g₀ hg₀H he_apply hKZ hK'Z'
  obtain ⟨g, hg_apply, hg_iff⟩ := exists_g s₀ s₀' g₀
  have hg_cond := g_cond hd' s₀ s₀' e g g₀ hg_apply hg₀R
  obtain ⟨fmap, hf_apply, hf_iff⟩ := exists_fmap s s' f₀
  have hf_cond := f_cond s s' e f₀ fmap hf₀R hf_iff
  have hsq_eq := sqMap_g₀_eq hf hd hd' s s₀ s' s₀' e_K f₀ g₀ hf₀K hg₀_add' hKZ hK'Z'
  have hsq_cond := hsq_cond hd hd' s s₀ s' s₀' e_H f₀ fmap g g₀ hg_apply hsq_eq hf_iff
  have hH1 := crossedHomPrincipal_data hf hd hd' e_K e he_left
  exact assemble hd hd' e fmap g hf_cond hg_cond hsq_cond hH1 e_K e_H he_left he_right

end CFSG.Quasithin.F112R.St84

end
