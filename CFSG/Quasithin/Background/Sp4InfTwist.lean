module

public import CFSG.Quasithin.Background.Sp4InfPair
public import CFSG.Quasithin.Background.Sp4InfGeo
public import CFSG.Quasithin.Background.B69Dual
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.B69Cnt

public section

namespace CFSG.Quasithin

namespace B69

open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H CFSG.Quasithin.H.PairG
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.QuasithinUnique.Lin2.Five (tauSp projEquiv)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (conjAut_proj fieldAut_proj coe_conjSp coe_fieldSp
  proj_surjective)
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem exists_tau_coord_of_mat {L : Type*} [Group L] {M : Type*} [CommGroup M] (ρ : L →* MulAut M)
    (r₁ r₂ : L →* StatedSp 2 K) (A : GL (Fin 2 ⊕ Fin 2) K) (σ : K ≃+* K)
    (hmat : ∀ l, (((r₂ l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((tauSp (r₁ l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ *
        (((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (e₂ : M ≃* StdMod (Fin 2 ⊕ Fin 2) K)
    (he₂ : ∀ (l : L) (s : M), e₂ (ρ l s) =
      matAut ((r₂ l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (e₂ s)) :
    ∃ e₂' : M ≃* StdMod (Fin 2 ⊕ Fin 2) K, ∀ (l : L) (s : M),
      e₂' (ρ l s) = matAut ((tauSp (r₁ l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (e₂' s) := by
  refine ⟨e₂.trans (twistAut A σ), fun l s => ?_⟩
  show twistAut A σ (e₂ (ρ l s)) = matAut _ (twistAut A σ (e₂ s))
  rw [he₂ l s]
  have := congrArg (fun f : MulAut (StdMod (Fin 2 ⊕ Fin 2) K) => f (e₂ s))
    (twistAut_mul A σ ((tauSp (r₁ l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)
      ((r₂ l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (hmat l))
  simpa using this

theorem exists_tau_mat (thb : MulAut (StatedProj (StatedSp 2 K))) (hnot : ¬ TypePresSp thb) :
    ∃ (A : GL (Fin 2 ⊕ Fin 2) K) (σ : K ≃+* K), ∀ g : StatedSp 2 K,
      ((((projEquiv K).symm (thb (projEquiv K g)) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((tauSp g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ *
        (((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  set θ' : MulAut (StatedSp 2 K) := (projEquiv K).trans (thb.trans (projEquiv K).symm) with hθ'
  have hθ'proj : ∀ g, projEquiv K (θ' g) = thb (projEquiv K g) := fun g => by
    rw [hθ']
    exact (projEquiv K).apply_symm_apply _
  have hproj : ∀ g : StatedSp 2 K, proj 2 K g = projEquiv K g := fun g => rfl
  obtain ⟨A, σ, h | h⟩ := Sp4.exists_aut_eq θ'
  · exfalso
    apply hnot
    have hthb' : thb = SymplecticHigher.conjAut 2 K A * SymplecticHigher.fieldAut 2 K σ := by
      ext x
      obtain ⟨g, rfl⟩ := proj_surjective x
      rw [hproj g, ← hθ'proj, h g, ← hproj, ← hproj g, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
    rw [hthb']
    exact typePresSp_conjAut_mul_fieldAut A σ
  · refine ⟨(A : GL (Fin 2 ⊕ Fin 2) K), σ, fun g => ?_⟩
    have : (projEquiv K).symm (thb (projEquiv K g)) = θ' g := rfl
    rw [this, h g, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]

theorem not_exists_tau_iso (Φ : StdMod (Fin 2 ⊕ Fin 2) K ≃* StdMod (Fin 2 ⊕ Fin 2) K)
    (hΦ : ∀ (γ : StatedSp 2 K) (x : StdMod (Fin 2 ⊕ Fin 2) K),
      Φ (matAut (γ : GL (Fin 2 ⊕ Fin 2) K) x) =
        matAut ((tauSp γ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (Φ x)) : False := by
  refine Sp4.not_isoMod (K := K) ?_
  let e : V₁ (Fin 2 ⊕ Fin 2) K ≃* V₂ (Fin 2 ⊕ Fin 2) K :=
    { toFun := fun w => ⟨((1 : StdMod (Fin 2 ⊕ Fin 2) K), Φ (w : PairMod (Fin 2 ⊕ Fin 2) K).1),
        mem_V₂.mpr rfl⟩
      invFun := fun w => ⟨(Φ.symm (w : PairMod (Fin 2 ⊕ Fin 2) K).2,
        (1 : StdMod (Fin 2 ⊕ Fin 2) K)), mem_V₁.mpr rfl⟩
      left_inv := fun w => by
        apply Subtype.ext
        have h2 : (w : PairMod (Fin 2 ⊕ Fin 2) K).2 = 1 := mem_V₁.mp w.2
        exact Prod.ext (by simp) h2.symm
      right_inv := fun w => by
        apply Subtype.ext
        have h1 : (w : PairMod (Fin 2 ⊕ Fin 2) K).1 = 1 := mem_V₂.mp w.2
        exact Prod.ext h1.symm (by simp)
      map_mul' := fun w w' => by
        apply Subtype.ext
        exact Prod.ext (by simp) (by simp [map_mul]) }
  refine ⟨e, ?_⟩
  rintro _ ⟨γ, rfl⟩ w h
  refine Prod.ext ?_ ?_
  · simp [e, pairHom_apply]
  · simp [e, pairHom_apply]
    exact hΦ γ _

omit [Finite K] in
theorem ne_of_tau' {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (r : ↥L →* StatedSp 2 K) {W₁ W₂ U : Subgroup V}
    (hLW₁ : L ≤ stabSub W₁) (hLW₂ : L ≤ stabSub W₂) (hLU : L ≤ stabSub U)
    (e₁ : Sec W₁ U ≃* StdMod (Fin 2 ⊕ Fin 2) K) (e₂ : Sec W₂ U ≃* StdMod (Fin 2 ⊕ Fin 2) K)
    (he₁ : ∀ (l : ↥L) (s : Sec W₁ U), e₁ (B5.secHom L hLW₁ hLU l s) =
      matAut ((r l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (e₁ s))
    (he₂ : ∀ (l : ↥L) (s : Sec W₂ U), e₂ (B5.secHom L hLW₂ hLU l s) =
      matAut ((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (e₂ s))
    (hniso : ∀ Φ : StdMod (Fin 2 ⊕ Fin 2) K ≃* StdMod (Fin 2 ⊕ Fin 2) K,
      (∀ (l : ↥L) (x : StdMod (Fin 2 ⊕ Fin 2) K),
        Φ (matAut ((r l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) x) =
          matAut ((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (Φ x)) → False) :
    W₁ ≠ W₂ := by
  rintro rfl
  refine hniso (e₁.symm.trans e₂) fun l x => ?_
  have h1 : e₁.symm (matAut ((r l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) x) =
      B5.secHom L hLW₁ hLU l (e₁.symm x) := by
    rw [MulEquiv.symm_apply_eq, he₁, MulEquiv.apply_symm_apply]
  show e₂ (e₁.symm (matAut ((r l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) x)) =
    matAut ((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (e₂ (e₁.symm x))
  rw [h1, he₂]

omit [Finite K] [CharP K 2] in
theorem mem_pairNorm_of_conj {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Subgroup (GL ι K)}
    {θ : ↥Γ →* ↥Γ} {x : MulAut (PairMod ι K)}
    (h₁ : ∀ γ : ↥Γ, ∃ δ : ↥Γ, x * pairHom Γ θ γ * x⁻¹ = pairHom Γ θ δ)
    (h₂ : ∀ γ : ↥Γ, ∃ δ : ↥Γ, x⁻¹ * pairHom Γ θ γ * x = pairHom Γ θ δ) :
    x ∈ pairNorm Γ θ := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨δ, h⟩ := h₁ γ
    exact ⟨δ, h.symm⟩
  · rintro ⟨δ, hδy⟩
    obtain ⟨γ, h⟩ := h₂ δ
    refine ⟨γ, ?_⟩
    change pairHom Γ θ γ = y
    rw [← h, hδy]
    group

variable {V : Type} [CommGroup V]

theorem card_le_of_tau {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {A L : Subgroup (MulAut V)}
    (hA : IsElemAbelian2 A) (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) {W₁ W₂ U : Subgroup V}
    (hAW₁ : A ≤ stabSub W₁) (hAW₂ : A ≤ stabSub W₂) (hAU : A ≤ stabSub U)
    (hLW₁ : L ≤ stabSub W₁) (hLW₂ : L ≤ stabSub W₂) (hLU : L ≤ stabSub U)
    (r : ↥L →* StatedSp 2 K)
    (hnorm : ∀ x : MulAut (PairMod (Fin 2 ⊕ Fin 2) K), x ∈ pairSub (Fin 2 ⊕ Fin 2) K →
      (∀ γ ∈ r.range, ∃ δ ∈ r.range,
        x * pairHom (StatedSp 2 K) tauSp γ * x⁻¹ = pairHom (StatedSp 2 K) tauSp δ) →
      (∀ γ ∈ r.range, ∃ δ ∈ r.range,
        x⁻¹ * pairHom (StatedSp 2 K) tauSp γ * x = pairHom (StatedSp 2 K) tauSp δ) →
      x ∈ Sp4.pairNormSp K)
    (e₁ : Sec W₁ U ≃* StdMod (Fin 2 ⊕ Fin 2) K) (e₂ : Sec W₂ U ≃* StdMod (Fin 2 ⊕ Fin 2) K)
    (he₁ : ∀ (l : ↥L) (s : Sec W₁ U), e₁ (B5.secHom L hLW₁ hLU l s) =
      matAut ((r l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (e₁ s))
    (he₂ : ∀ (l : ↥L) (s : Sec W₂ U), e₂ (B5.secHom L hLW₂ hLU l s) =
      matAut ((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (e₂ s))
    (hB : ¬ A ≤ centSec W₁ U) :
    Nat.card ↥A * Nat.card ↥(fixV (autSec A W₁ U)) * Nat.card ↥(fixV (autSec A W₂ U)) ≤
      Nat.card (Sec W₁ U) * Nat.card (Sec W₂ U) *
        Nat.card ↥(A ⊓ centSec W₁ U ⊓ centSec W₂ U) := by
  classical
  let σ₁ := B5.secHom A hAW₁ hAU
  let σ₂ := B5.secHom A hAW₂ hAU
  let ε₁ : ↥A →* MulAut (StdMod (Fin 2 ⊕ Fin 2) K) := (congrHom e₁).comp σ₁
  let ε₂ : ↥A →* MulAut (StdMod (Fin 2 ⊕ Fin 2) K) := (congrHom e₂).comp σ₂
  let ξ : ↥A →* MulAut (PairMod (Fin 2 ⊕ Fin 2) K) :=
    (pairHom₂ (Fin 2 ⊕ Fin 2) K).comp (ε₁.prod ε₂)
  have hξ : ∀ a : ↥A, ξ a = pairAut (ε₁ a) (ε₂ a) := fun a => rfl
  have hm₁ : ∀ l : ↥L, congrHom e₁ (B5.secHom L hLW₁ hLU l) =
      matAut ((r l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
    intro l
    refine MulEquiv.ext fun x => ?_
    rw [congrHom_apply]
    have := he₁ l (e₁.symm x)
    rwa [MulEquiv.apply_symm_apply] at this
  have hm₂ : ∀ l : ↥L, congrHom e₂ (B5.secHom L hLW₂ hLU l) =
      matAut ((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
    intro l
    refine MulEquiv.ext fun x => ?_
    rw [congrHom_apply]
    have := he₂ l (e₂.symm x)
    rwa [MulEquiv.apply_symm_apply] at this
  have hc₁ : ∀ (a : ↥A) (l : ↥L), ε₁ a * matAut ((r l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) *
      (ε₁ a)⁻¹ = matAut ((r ⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, hAn a a.2 l l.2⟩ :
        StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
    intro a l
    rw [← hm₁ l, ← hm₁ ⟨_, hAn a a.2 l l.2⟩, ← secHom_conj hAW₁ hAU hLW₁ hLU hAn a l]
    simp only [ε₁, σ₁, MonoidHom.comp_apply, map_mul, map_inv]
  have hc₂ : ∀ (a : ↥A) (l : ↥L), ε₂ a *
      matAut ((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) * (ε₂ a)⁻¹ =
      matAut ((tauSp (r ⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, hAn a a.2 l l.2⟩) :
        StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
    intro a l
    rw [← hm₂ l, ← hm₂ ⟨_, hAn a a.2 l l.2⟩, ← secHom_conj hAW₂ hAU hLW₂ hLU hAn a l]
    simp only [ε₂, σ₂, MonoidHom.comp_apply, map_mul, map_inv]
  have hconjN : ∀ a : ↥A, ∀ γ ∈ r.range, ∃ δ ∈ r.range,
      ξ a * pairHom (StatedSp 2 K) tauSp γ * (ξ a)⁻¹ = pairHom (StatedSp 2 K) tauSp δ := by
    intro a γ hγ
    obtain ⟨l, rfl⟩ := hγ
    refine ⟨r ⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, hAn a a.2 l l.2⟩, ⟨_, rfl⟩, ?_⟩
    rw [hξ, pairHom_apply, pairHom_apply, pairAut_inv, pairAut_mul, pairAut_mul]
    exact congrArg₂ pairAut (hc₁ a l) (hc₂ a l)
  have hN : ∀ a : ↥A, ξ a ∈ Sp4.pairNormSp K := fun a =>
    hnorm (ξ a) (by rw [hξ]; exact pairAut_mem_pairSub _ _) (hconjN a) (fun γ hγ => by
      obtain ⟨δ, hδ, h⟩ := hconjN a⁻¹ γ hγ
      refine ⟨δ, hδ, ?_⟩
      simpa [map_inv] using h)
  set B : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) := ξ.range with hBdef
  have hBN : B ≤ Sp4.pairNormSp K := by
    rintro _ ⟨a, rfl⟩
    exact hN a
  have hBs : B ≤ pairSub (Fin 2 ⊕ Fin 2) K := by
    rintro _ ⟨a, rfl⟩
    rw [hξ]
    exact pairAut_mem_pairSub _ _
  have hB2 : IsElemAbelian2 B := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hA.1 a a.2 b b.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.2 a a.2)
      rw [this, map_one]
  have hB1 : B ≠ ⊥ := by
    obtain ⟨a, haA, haC⟩ := IsConcreteLE.not_le_iff_exists.1 hB
    intro hbot
    have hmem : ξ ⟨a, haA⟩ ∈ B := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot, hξ] at hmem
    have h1 : ε₁ ⟨a, haA⟩ = 1 := (pairAut_injective (hmem.trans pairAut_one.symm)).1
    have h2 : σ₁ ⟨a, haA⟩ = 1 :=
      congrHom_injective e₁ (by rw [map_one]; exact h1)
    exact haC ((B5.mem_ker_secHom A hAW₁ hAU ⟨a, haA⟩).1 (MonoidHom.mem_ker.2 h2))
  have h2 := Sp4Inf.card_mul_fixV_le_pair hn hK hBN hBs hB2 hB1
  have hcardV : Nat.card (PairMod (Fin 2 ⊕ Fin 2) K) = Nat.card (Sec W₁ U) * Nat.card (Sec W₂ U) := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (Equiv.prodCongr e₁.toEquiv e₂.toEquiv)).symm
  have hfixB : fixV B = (fixV ε₁.range).prod (fixV ε₂.range) := by
    ext x
    simp only [mem_fixV, Subgroup.mem_prod]
    constructor
    · intro h
      refine ⟨fun g hg => ?_, fun g hg => ?_⟩
      · obtain ⟨a, rfl⟩ := hg
        have := h (ξ a) ⟨a, rfl⟩
        rw [hξ] at this
        exact congrArg Prod.fst this
      · obtain ⟨a, rfl⟩ := hg
        have := h (ξ a) ⟨a, rfl⟩
        rw [hξ] at this
        exact congrArg Prod.snd this
    · rintro ⟨h1, h2⟩ b ⟨a, rfl⟩
      rw [hξ]
      exact Prod.ext (h1 _ ⟨a, rfl⟩) (h2 _ ⟨a, rfl⟩)
  have hrange₁ : ε₁.range = (autSec A W₁ U).map (congrHom e₁) := by
    rw [MonoidHom.range_comp, ← B5.range_secHom A hAW₁ hAU]
  have hrange₂ : ε₂.range = (autSec A W₂ U).map (congrHom e₂) := by
    rw [MonoidHom.range_comp, ← B5.range_secHom A hAW₂ hAU]
  have hF₁ : Nat.card ↥(fixV ε₁.range) = Nat.card ↥(fixV (autSec A W₁ U)) := by
    rw [hrange₁, fixV_map_congrHom e₁ (autSec A W₁ U)]
    exact Subgroup.card_map_of_injective e₁.injective
  have hF₂ : Nat.card ↥(fixV ε₂.range) = Nat.card ↥(fixV (autSec A W₂ U)) := by
    rw [hrange₂, fixV_map_congrHom e₂ (autSec A W₂ U)]
    exact Subgroup.card_map_of_injective e₂.injective
  have hfixcard : Nat.card ↥(fixV B) =
      Nat.card ↥(fixV (autSec A W₁ U)) * Nat.card ↥(fixV (autSec A W₂ U)) := by
    rw [hfixB, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hF₁, hF₂]
  have hker : ξ.ker = (A ⊓ centSec W₁ U ⊓ centSec W₂ U).subgroupOf A := by
    ext a
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      rw [hξ] at h
      obtain ⟨h1, h2⟩ := pairAut_injective (h.trans pairAut_one.symm)
      refine ⟨⟨a.2, ?_⟩, ?_⟩
      · exact (B5.mem_ker_secHom A hAW₁ hAU a).1
          (MonoidHom.mem_ker.2 (congrHom_injective e₁ (by rw [map_one]; exact h1)))
      · exact (B5.mem_ker_secHom A hAW₂ hAU a).1
          (MonoidHom.mem_ker.2 (congrHom_injective e₂ (by rw [map_one]; exact h2)))
    · rintro ⟨⟨-, h1⟩, h2⟩
      rw [hξ]
      have e1 : σ₁ a = 1 := MonoidHom.mem_ker.1 ((B5.mem_ker_secHom A hAW₁ hAU a).2 h1)
      have e2 : σ₂ a = 1 := MonoidHom.mem_ker.1 ((B5.mem_ker_secHom A hAW₂ hAU a).2 h2)
      have f1 : ε₁ a = 1 := by simp only [ε₁, MonoidHom.comp_apply, e1, map_one]
      have f2 : ε₂ a = 1 := by simp only [ε₂, MonoidHom.comp_apply, e2, map_one]
      rw [f1, f2]
      exact pairAut_one
  have hK0A : A ⊓ centSec W₁ U ⊓ centSec W₂ U ≤ A := inf_le_left.trans inf_le_left
  have hcardK : Nat.card ↥ξ.ker = Nat.card ↥(A ⊓ centSec W₁ U ⊓ centSec W₂ U) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0A).toEquiv
  have hcardA : Nat.card ↥B * Nat.card ↥ξ.ker = Nat.card ↥A := by
    have := B1More.card_map_mul_card_inf_ker (⊤ : Subgroup ↥A) ξ
    rwa [← MonoidHom.range_eq_map, top_inf_eq, Subgroup.card_top] at this
  rw [hfixcard, hcardV] at h2
  rw [← hcardA, ← hcardK]
  calc Nat.card ↥B * Nat.card ↥ξ.ker * Nat.card ↥(fixV (autSec A W₁ U)) *
        Nat.card ↥(fixV (autSec A W₂ U))
      = (Nat.card ↥B * (Nat.card ↥(fixV (autSec A W₁ U)) *
          Nat.card ↥(fixV (autSec A W₂ U)))) * Nat.card ↥ξ.ker := by ring
    _ ≤ (Nat.card (Sec W₁ U) * Nat.card (Sec W₂ U)) * Nat.card ↥ξ.ker :=
        Nat.mul_le_mul_right _ h2

omit [Finite K] in
theorem hnorm_of_surjective {L : Type*} [Group L] (r : L →* StatedSp 2 K) (hr : Function.Surjective r) :
    ∀ x : MulAut (PairMod (Fin 2 ⊕ Fin 2) K), x ∈ pairSub (Fin 2 ⊕ Fin 2) K →
      (∀ γ ∈ r.range, ∃ δ ∈ r.range,
        x * pairHom (StatedSp 2 K) tauSp γ * x⁻¹ = pairHom (StatedSp 2 K) tauSp δ) →
      (∀ γ ∈ r.range, ∃ δ ∈ r.range,
        x⁻¹ * pairHom (StatedSp 2 K) tauSp γ * x = pairHom (StatedSp 2 K) tauSp δ) →
      x ∈ Sp4.pairNormSp K := by
  intro x _ h₁ h₂
  refine mem_pairNorm_of_conj (fun γ => ?_) (fun γ => ?_)
  · obtain ⟨δ, -, h⟩ := h₁ γ (by obtain ⟨l, rfl⟩ := hr γ; exact ⟨l, rfl⟩)
    exact ⟨δ, h⟩
  · obtain ⟨δ, -, h⟩ := h₂ γ (by obtain ⟨l, rfl⟩ := hr γ; exact ⟨l, rfl⟩)
    exact ⟨δ, h⟩

theorem arith_ul₁ {a k k' aY cY c₁ c₂ s₁ s₂ d y : ℕ} (hk : 0 < k) (H1 : y < aY * cY) (H2 : k ≤ k') (H3 : aY * k' = a)
    (H4 : cY ≤ c₁ * c₂ * d) (H5 : y = s₁ * s₂ * d) (H6 : a * c₁ * c₂ ≤ s₁ * s₂ * k) :
    False := by
  have h1 : y * k < a * (c₁ * c₂ * d) := by
    calc y * k < aY * cY * k := Nat.mul_lt_mul_of_pos_right H1 hk
      _ ≤ aY * cY * k' := Nat.mul_le_mul_left _ H2
      _ = a * cY := by rw [← H3]; ring
      _ ≤ a * (c₁ * c₂ * d) := Nat.mul_le_mul_left _ H4
  have h2 : a * (c₁ * c₂ * d) ≤ y * k := by
    calc a * (c₁ * c₂ * d) = (a * c₁ * c₂) * d := by ring
      _ ≤ (s₁ * s₂ * k) * d := Nat.mul_le_mul_right _ H6
      _ = y * k := by rw [H5]; ring
  exact absurd h1 (not_lt.2 h2)

variable [Finite V]

theorem false_of_two_sections₁ (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hs : rAV A < 1) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L)
    {W₁ W₂ : Subgroup V} (h₁ : W₁ ∈ IrrPlus L (⊤ : Subgroup V))
    (h₂ : W₂ ∈ IrrPlus L (⊤ : Subgroup V)) (hne : W₁ ≠ W₂)
    (hGT : Nat.card A * Nat.card ↥(fixV (autSec A W₁ (fixV L))) *
        Nat.card ↥(fixV (autSec A W₂ (fixV L))) ≤
      Nat.card (Sec W₁ (fixV L)) * Nat.card (Sec W₂ (fixV L)) *
        Nat.card ↥(A ⊓ centSec W₁ (fixV L) ⊓ centSec W₂ (fixV L))) : False := by
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hA₁ := a_stab_irr hV hA hL hLA h₁
  have hA₂ := a_stab_irr hV hA hL hLA h₂
  have hind := inf_le_fixV_of_ne h₁ h₂ hne
  have hAY : ∀ a ∈ A, ∀ y ∈ W₁ ⊔ W₂, a y ∈ W₁ ⊔ W₂ := isInv_sup hA₁ hA₂
  have hAst : A ≤ stabSub (W₁ ⊔ W₂) := B1.le_stabSub_of_invariant hAY
  have hnt : commSub (W₁ ⊔ W₂) A ≠ ⊥ := fun h =>
    commSub_ne_bot_of_irr hLA h₁ (eq_bot_iff.2 (h ▸ commSub_mono le_sup_left le_rfl))
  obtain ⟨hmin, -⟩ := B1_5_2 hV hA hAY hnt
  have hr : rAV (autSub A (W₁ ⊔ W₂)) < 1 := rAV_autSub_lt_one hV hA hAY hnt hs
  have hY1 : Nat.card ↥(W₁ ⊔ W₂) <
      Nat.card ↥(autSub A (W₁ ⊔ W₂)) * Nat.card ↥(fixV (autSub A (W₁ ⊔ W₂))) :=
    (rAV_lt_one_iff (B1.sq_eq_one_sub hV (W₁ ⊔ W₂)) hmin.1.isA2).1 hr
  have hK0 : A ⊓ centSec W₁ (fixV L) ⊓ centSec W₂ (fixV L) ≤ A ⊓ centSub (W₁ ⊔ W₂) := by
    intro a ha
    obtain ⟨⟨haA, ha1⟩, ha2⟩ := ha
    refine ⟨haA, ?_⟩
    have e1 := sec_triv_imp_triv hL hAn h₁ hA₁ haA ha1.2
    have e2 := sec_triv_imp_triv hL hAn h₂ hA₂ haA ha2.2
    intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := Subgroup.mem_sup.1 hy
    rw [map_mul, e1 x hx, e2 z hz]
  have hk' := Subgroup.card_le_of_le hK0
  have hA3 := card_autSub_mul hAst
  exact arith_ul₁ Nat.card_pos hY1 hk' hA3
    (card_fixY_le (fixV L) hind hA₁ hA₂) (card_Y_eq (fixV L) hind) hGT

end B69

end CFSG.Quasithin
