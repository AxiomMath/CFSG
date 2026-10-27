module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapTensorA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16f_mul_mul_comm {A B : Subgroup (MulAut W)}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {a₁ a₂ b₁ b₂ : MulAut W}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) :
    (a₁ * a₂) * (b₁ * b₂) = (a₁ * b₁) * (a₂ * b₂) := by
  rw [mul_assoc a₁ a₂ (b₁ * b₂), ← mul_assoc a₂ b₁ b₂, hc a₂ ha₂ b₁ hb₁,
    mul_assoc b₁ a₂ b₂, ← mul_assoc a₁ b₁ (a₂ * b₂)]

theorem w16f_isMatTensor2_realizes {K K' : Subgroup (MulAut W)} {U₀ U R : Subgroup W}
    (hKs : K ≤ secStabAll U U₀) (hK's : K' ≤ secStabAll U U₀) (hcomm : ⁅K, K'⁆ = ⊥) (hRU : R ≤ U)
    (hRst : StableUnder (K ⊔ K') R) (hinf : R ⊓ U₀ = ⊥) (hsup : R ⊔ U₀ = U)
    (hKf : K ⊓ centSub R = ⊥) (hK'f : K' ⊓ centSub R = ⊥) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (h : IsMatTensor2 (secImg K U U₀) (secImg K' U U₀) F) :
    (FFModel.tensorNat 2 F).Realizes (K ⊔ K') R ⊥ := by
  classical
  have hRstK : StableUnder K R := fun a ha r hr => hRst a (Subgroup.mem_sup_left ha) r hr
  have hRstK' : StableUnder K' R := fun a ha r hr => hRst a (Subgroup.mem_sup_right ha) r hr
  obtain ⟨φ₁, φ₂, ψ, h₁, h₂⟩ := h
  let eSL : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(StatedSL 2 F) :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
  let ρ : ↥K ≃* ↥(secImg K U U₀) :=
    w16f_secImgEquiv K U U₀ R hKs hRstK hRU hinf hKf
  let ρ' : ↥K' ≃* ↥(secImg K' U U₀) :=
    w16f_secImgEquiv K' U U₀ R hK's hRstK' hRU hinf hK'f
  let χ₁ : ↥K ≃* ↥(StatedSL 2 F) := ρ.trans (φ₁.trans eSL)
  let χ₂ : ↥K' ≃* ↥(StatedSL 2 F) := ρ'.trans (φ₂.trans eSL)
  let θ : ↥R ≃* SecT U U₀ := w16f_secTEquiv R U U₀ hRU hinf hsup
  have hc : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) ha) b hb).symm
  have hK'cent : K' ≤ Subgroup.centralizer (K : Set (MulAut W)) :=
    fun b hb => Subgroup.mem_centralizer_iff.mpr (fun a ha => hc a ha b hb)
  have hnorm : K' ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    fun b hb => Subgroup.centralizer_le_normalizer (K : Set (MulAut W)) (hK'cent hb)
  have hdecomp : ∀ x ∈ K ⊔ K', ∃ a ∈ K, ∃ b ∈ K', a * b = x := by
    intro x hx
    have hset : (↑(K ⊔ K') : Set (MulAut W)) =
        (K : Set (MulAut W)) * (K' : Set (MulAut W)) :=
      Subgroup.coe_mul_of_right_le_normalizer_left K K' hnorm
    have hx' : x ∈ (K : Set (MulAut W)) * (K' : Set (MulAut W)) := by
      rw [← hset]; exact hx
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx'
    exact ⟨a, ha, b, hb, hab⟩
  let π : ↥(StatedSL 2 F) × ↥(StatedSL 2 F) →* ↥(K ⊔ K') :=
    { toFun := fun γ => ⟨(χ₁.symm γ.1 : ↥K).1 * (χ₂.symm γ.2 : ↥K').1,
        Subgroup.mul_mem_sup (χ₁.symm γ.1).2 (χ₂.symm γ.2).2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun γ δ => Subtype.ext (by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        exact w16f_mul_mul_comm hc (χ₁.symm γ.1).2 (χ₁.symm δ.1).2
          (χ₂.symm γ.2).2 (χ₂.symm δ.2).2) }
  have hπ_surj : Function.Surjective π := by
    intro x
    obtain ⟨a, ha, b, hb, hab⟩ := hdecomp x.1 x.2
    refine ⟨(χ₁ ⟨a, ha⟩, χ₂ ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    show ((χ₁.symm (χ₁ ⟨a, ha⟩) : ↥K) : MulAut W) *
        ((χ₂.symm (χ₂ ⟨b, hb⟩) : ↥K') : MulAut W) = x.1
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact hab
  let β₀ : ↥R →* ↥(⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))) :=
    (ψ.toMonoidHom.comp θ.toMonoidHom).codRestrict ⊤ (fun _ => Subgroup.mem_top _)
  let β : ↥R →* ↥(⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))) ⧸
      (⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))).subgroupOf ⊤ :=
    (QuotientGroup.mk' _).comp β₀
  have hβ₀_apply : ∀ u : ↥R, β₀ u =
      (⟨ψ (θ u), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)))) :=
    fun u => rfl
  have hβ_surj : Function.Surjective β := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨w, hw⟩ := ψ.surjective (m : Multiplicative (Matrix (Fin 2) (Fin 2) F))
    obtain ⟨u, hu⟩ := θ.surjective w
    refine ⟨u, ?_⟩
    show QuotientGroup.mk' _ (β₀ u) = QuotientGroup.mk' _ m
    rw [show β₀ u = m from Subtype.ext (by
      rw [hβ₀_apply]
      show ψ (θ u) = (m : Multiplicative (Matrix (Fin 2) (Fin 2) F))
      rw [hu, hw])]
  have hβ_ker : ∀ u : ↥R, β u = 1 ↔ (u : W) ∈ (⊥ : Subgroup W) := by
    intro u
    constructor
    · intro h
      have h1 : β₀ u ∈ (⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))).subgroupOf ⊤ :=
        (QuotientGroup.eq_one_iff _).mp h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h1
      have h2 : ψ (θ u) = 1 := h1
      have h3 : θ u = 1 := ψ.injective (by rw [h2, map_one])
      have h4 : u = 1 := θ.injective (by rw [h3, map_one])
      rw [h4]
      exact Subgroup.mem_bot.mpr rfl
    · intro h
      rw [Subgroup.mem_bot] at h
      rw [show u = 1 from Subtype.ext h, map_one]
  refine ⟨π, ?_⟩
  dsimp only [FFModel.RealizesVia, FFModel.tensorNat]
  refine ⟨hπ_surj, bot_le, bot_le, ?_, ?_, ?_, ?_, β, hβ_surj, hβ_ker, ?_⟩
  · intro h u hu
    exact hRst h.1 h.2 u hu
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ m hm
    exact Subgroup.mem_top _
  · intro γ m hm
    rw [Subgroup.mem_bot] at hm ⊢
    rw [hm]
    simp [tensorAct]
  · intro γ u m hu hm hβu
    have hm_eq : m = (⟨ψ (θ u), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)))) := by
      have h2 : (β₀ u / m : ↥(⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)))) ∈
          (⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))).subgroupOf ⊤ :=
        (QuotientGroup.eq_iff_div_mem).mp hβu
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h2
      have h3 : β₀ u = m := by
        apply div_eq_one.mp
        apply Subtype.ext
        change (β₀ u : Multiplicative (Matrix (Fin 2) (Fin 2) F)) / m = 1
        exact h2
      rw [← h3, hβ₀_apply]
    let aK : ↥K := χ₁.symm γ.1
    let aK' : ↥K' := χ₂.symm γ.2
    let xK : ↥(secImg K U U₀) := ρ aK
    let yK' : ↥(secImg K' U U₀) := ρ' aK'
    have hxK : (xK : MulAut (SecT U U₀)) = secAut U U₀ ⟨aK.1, hKs aK.2⟩ := rfl
    have hyK' : (yK' : MulAut (SecT U U₀)) = secAut U U₀ ⟨aK'.1, hK's aK'.2⟩ := rfl
    have hθa : θ ⟨aK.1 (u : W), hRstK aK.1 aK.2 (u : W) u.2⟩ = (xK : MulAut (SecT U U₀)) (θ u) := by
      rw [hxK]
      exact w16f_secTEquiv_secAut R U U₀ hRU hinf hsup (hKs aK.2)
        (fun r hr => hRstK aK.1 aK.2 r hr) u
    have hθa' : θ ⟨aK'.1 (u : W), hRstK' aK'.1 aK'.2 (u : W) u.2⟩ =
        (yK' : MulAut (SecT U U₀)) (θ u) := by
      rw [hyK']
      exact w16f_secTEquiv_secAut R U U₀ hRU hinf hsup (hK's aK'.2)
        (fun r hr => hRstK' aK'.1 aK'.2 r hr) u
    have hθcomp : θ ⟨aK.1 (aK'.1 (u : W)),
        hRstK aK.1 aK.2 (aK'.1 (u : W)) (hRstK' aK'.1 aK'.2 (u : W) u.2)⟩ =
        (xK : MulAut (SecT U U₀)) (θ ⟨aK'.1 (u : W), hRstK' aK'.1 aK'.2 (u : W) u.2⟩) := by
      rw [hxK]
      exact w16f_secTEquiv_secAut R U U₀ hRU hinf hsup (hKs aK.2)
        (fun r hr => hRstK aK.1 aK.2 r hr)
        ⟨aK'.1 (u : W), hRstK' aK'.1 aK'.2 (u : W) u.2⟩
    have hmat1 : (φ₁ xK : Matrix (Fin 2) (Fin 2) F) =
        (((γ.1 : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) := by
      have h1 : eSL (φ₁ xK) = (γ.1 : ↥(StatedSL 2 F)) := by
        change χ₁ aK = γ.1
        exact MulEquiv.apply_symm_apply χ₁ γ.1
      calc (φ₁ xK : Matrix (Fin 2) (Fin 2) F) =
            (((eSL (φ₁ xK) : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) :=
            (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 2 F (φ₁ xK)).symm
        _ = (((γ.1 : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) := by rw [h1]
    have hmat2 : (φ₂ yK' : Matrix (Fin 2) (Fin 2) F) =
        (((γ.2 : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) := by
      have h1 : eSL (φ₂ yK') = (γ.2 : ↥(StatedSL 2 F)) := by
        change χ₂ aK' = γ.2
        exact MulEquiv.apply_symm_apply χ₂ γ.2
      calc (φ₂ yK' : Matrix (Fin 2) (Fin 2) F) =
            (((eSL (φ₂ yK') : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) :=
            (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 2 F (φ₂ yK')).symm
        _ = (((γ.2 : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) := by rw [h1]
    have hkey : ψ (θ ⟨((π γ : ↥(K ⊔ K')) : MulAut W) (u : W), hu⟩) =
        tensorAct 2 F γ (ψ (θ u)) := by
      have hsub : (⟨((π γ : ↥(K ⊔ K')) : MulAut W) (u : W), hu⟩ : ↥R) =
          ⟨aK.1 (aK'.1 (u : W)), hRstK aK.1 aK.2 (aK'.1 (u : W))
            (hRstK' aK'.1 aK'.2 (u : W) u.2)⟩ := Subtype.ext rfl
      rw [hsub, hθcomp, hθa']
      apply Multiplicative.toAdd.injective
      rw [tensorAct, toAdd_ofAdd]
      have h1 := h₁ xK ((yK' : MulAut (SecT U U₀)) (θ u))
      have h2 := h₂ yK' (θ u)
      rw [h1, h2, hmat1, hmat2, mul_assoc]
    rw [hm_eq]
    change QuotientGroup.mk' _ (β₀ ⟨((π γ : ↥(K ⊔ K')) : MulAut W) (u : W), hu⟩) =
      QuotientGroup.mk' _ ⟨tensorAct 2 F γ (ψ (θ u)), hm⟩
    congr 1
    apply Subtype.ext
    exact hkey

end CFSG.LocalAnalysis.WeakClosure81
