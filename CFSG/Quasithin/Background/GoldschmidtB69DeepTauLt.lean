module

public import CFSG.Quasithin.Background.GoldschmidtB69DeepPair
public import CFSG.Quasithin.Background.B69Dual

public section

namespace CFSG.Quasithin

namespace B69

open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H CFSG.Quasithin.H.PairG
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.QuasithinUnique.Lin2.Five (tauSp projEquiv)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {V : Type} [CommGroup V] [Finite V]

theorem card_lt_of_tau {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {A L : Subgroup (MulAut V)}
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
    Nat.card ↥A * Nat.card ↥(fixV (autSec A W₁ U)) * Nat.card ↥(fixV (autSec A W₂ U)) <
      Nat.card (Sec W₁ U) * Nat.card (Sec W₂ U) *
        Nat.card ↥(A ⊓ centSec W₁ U ⊓ centSec W₂ U) := by
  classical
  have : Finite (MulAut V) := MulEquiv.finite_left
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
  have h2 := Sp4Inf.card_mul_fixV_lt_pair hn hK hBN hBs hB2 hB1
  have hcardV : Nat.card (PairMod (Fin 2 ⊕ Fin 2) K) =
      Nat.card (Sec W₁ U) * Nat.card (Sec W₂ U) := by
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
    _ < (Nat.card (Sec W₁ U) * Nat.card (Sec W₂ U)) * Nat.card ↥ξ.ker :=
        Nat.mul_lt_mul_of_pos_right h2 Nat.card_pos

end B69

end CFSG.Quasithin
