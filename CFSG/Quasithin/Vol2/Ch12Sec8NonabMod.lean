module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {Γ : Type*} [Group Γ]

theorem s3_module_core (S W X : Subgroup Γ) (g u : Γ)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hsq : ∀ a ∈ S, a * a = 1)
    (hWS : W ≤ S) (hXS : X ≤ S)
    (hSWX : ∀ s ∈ S, ∃ w ∈ W, ∃ x ∈ X, s = w * x)
    (hXg : ∀ x : Γ, x ∈ X ↔ g * x * g⁻¹ ∈ W)
    (hWX : ∀ a ∈ W, a ∈ X → a = 1)
    (hgS : ∀ s ∈ S, g * s * g⁻¹ ∈ S) (hg3 : g * g * g ∈ S)
    (hu2 : u * u = 1)
    (huW : ∀ w ∈ W, u * w * u⁻¹ = w)
    (huSW : ∀ s ∈ S, u * s * u⁻¹ * s⁻¹ ∈ W)
    (hker : ∀ y ∈ X, u * y * u⁻¹ * y⁻¹ = 1 → y = 1)
    (hK2 : u * g * u⁻¹ * g ∈ S) :
    (∀ w ∈ W, w * (g * w * g⁻¹) * (g * g * w * (g * g)⁻¹) = 1) ∧
    (∀ w ∈ W, (g⁻¹ * w * g) * u * (g⁻¹ * w * g)⁻¹ * u⁻¹ = w) ∧
    (∀ x ∈ X, ∀ z ∈ W, u * x * u⁻¹ * x⁻¹ = z → x = g⁻¹ * z * g) ∧
    (∀ c ∈ S, g * c * g⁻¹ = c → c = 1) := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  set s₀ := u * g * u⁻¹ * g with hs₀
  have hug : u * g * u⁻¹ = s₀ * g⁻¹ := by rw [hs₀]; group
  have hugi : u * g⁻¹ * u⁻¹ = g * s₀⁻¹ := by
    calc u * g⁻¹ * u⁻¹ = (u * g * u⁻¹)⁻¹ := by group
      _ = (s₀ * g⁻¹)⁻¹ := by rw [hug]
      _ = g * s₀⁻¹ := by group
  have hg3c : ∀ w ∈ S, (g * g * g)⁻¹ * w * (g * g * g) = w := fun w hw => by
    have := hcomm (g * g * g) hg3 w hw
    calc (g * g * g)⁻¹ * w * (g * g * g) = (g * g * g)⁻¹ * (w * (g * g * g)) := by group
      _ = (g * g * g)⁻¹ * ((g * g * g) * w) := by rw [this]
      _ = w := by group
  have hfix : ∀ c ∈ S, g * c * g⁻¹ = c → c = 1 := by
    intro c hc hgc
    have hgic : g⁻¹ * c * g = c := by
      calc g⁻¹ * c * g = g⁻¹ * (g * c * g⁻¹) * g := by rw [hgc]
        _ = c := by group
    have hs₀S : s₀ ∈ S := hK2
    have hscomm : s₀ * c * s₀⁻¹ = c := by
      have := hcomm s₀ hs₀S c hc
      calc s₀ * c * s₀⁻¹ = (c * s₀) * s₀⁻¹ := by rw [this]
        _ = c := by group
    have he1 : u⁻¹ * g * u = s₀ * g⁻¹ := by
      rw [hui]
      rw [hui] at hug
      exact hug
    have hgd : g * (u * c * u⁻¹) * g⁻¹ = u * c * u⁻¹ := by
      have e : g * (u * c * u⁻¹) * g⁻¹ =
          u * ((u⁻¹ * g * u) * c * (u⁻¹ * g * u)⁻¹) * u⁻¹ := by group
      rw [e, he1]
      have e2 : (s₀ * g⁻¹) * c * (s₀ * g⁻¹)⁻¹ = s₀ * (g⁻¹ * c * g) * s₀⁻¹ := by group
      rw [e2, hgic, hscomm]
    have hdW : u * c * u⁻¹ * c⁻¹ ∈ W := huSW c hc
    have hgdfix : g * (u * c * u⁻¹ * c⁻¹) * g⁻¹ = u * c * u⁻¹ * c⁻¹ := by
      have e : g * (u * c * u⁻¹ * c⁻¹) * g⁻¹ =
          (g * (u * c * u⁻¹) * g⁻¹) * (g * c * g⁻¹)⁻¹ := by group
      rw [e, hgd, hgc]
    have hd1 : u * c * u⁻¹ * c⁻¹ = 1 :=
      hWX _ hdW ((hXg _).mpr (by rw [hgdfix]; exact hdW))
    have huc : u * c * u⁻¹ = c := by
      have : u * c * u⁻¹ = (u * c * u⁻¹ * c⁻¹) * c := by group
      rw [this, hd1, one_mul]
    obtain ⟨w₁, hw₁, x₁, hx₁, rfl⟩ := hSWX c hc
    have hux : u * x₁ * u⁻¹ = x₁ := by
      have e : u * (w₁ * x₁) * u⁻¹ = (u * w₁ * u⁻¹) * (u * x₁ * u⁻¹) := by group
      rw [e, huW w₁ hw₁] at huc
      exact mul_left_cancel huc
    have hx1 : x₁ = 1 := hker x₁ hx₁ (by rw [hux]; group)
    subst hx1
    rw [mul_one] at hgc ⊢
    exact hWX _ hw₁ ((hXg _).mpr (by rw [hgc]; exact hw₁))
  have hnorm : ∀ w ∈ W, w * (g * w * g⁻¹) * (g * g * w * (g * g)⁻¹) = 1 := by
    intro w hw
    have hwS : w ∈ S := hWS hw
    have ha : g * w * g⁻¹ ∈ S := hgS w hwS
    have hb : g * g * w * (g * g)⁻¹ ∈ S := by
      have := hgS _ ha
      have e : g * (g * w * g⁻¹) * g⁻¹ = g * g * w * (g * g)⁻¹ := by group
      rwa [e] at this
    have hnS : w * (g * w * g⁻¹) * (g * g * w * (g * g)⁻¹) ∈ S :=
      S.mul_mem (S.mul_mem hwS ha) hb
    apply hfix _ hnS
    have h3 : (g * g * g) * w * (g * g * g)⁻¹ = w := by
      have := hcomm (g * g * g) hg3 w hwS
      calc (g * g * g) * w * (g * g * g)⁻¹ = (w * (g * g * g)) * (g * g * g)⁻¹ := by rw [this]
        _ = w := by group
    have e : g * (w * (g * w * g⁻¹) * (g * g * w * (g * g)⁻¹)) * g⁻¹ =
        (g * w * g⁻¹) * (g * g * w * (g * g)⁻¹) * ((g * g * g) * w * (g * g * g)⁻¹) := by group
    rw [e, h3]
    have := hcomm w hwS ((g * w * g⁻¹) * (g * g * w * (g * g)⁻¹)) (S.mul_mem ha hb)
    calc (g * w * g⁻¹) * (g * g * w * (g * g)⁻¹) * w
        = ((g * w * g⁻¹) * (g * g * w * (g * g)⁻¹)) * w := rfl
      _ = w * ((g * w * g⁻¹) * (g * g * w * (g * g)⁻¹)) := this.symm
      _ = w * (g * w * g⁻¹) * (g * g * w * (g * g)⁻¹) := by group
  have hKI : ∀ w ∈ W, (g⁻¹ * w * g) * u * (g⁻¹ * w * g)⁻¹ * u⁻¹ = w := by
    intro w hw
    have hwS : w ∈ S := hWS hw
    have ha : g * w * g⁻¹ ∈ S := hgS w hwS
    have hs₀S : s₀ ∈ S := hK2
    have hwi : u * w⁻¹ * u⁻¹ = w⁻¹ := huW w⁻¹ (W.inv_mem hw)
    have hux : u * (g⁻¹ * w * g)⁻¹ * u⁻¹ = g * w⁻¹ * g⁻¹ := by
      have e : u * (g⁻¹ * w * g)⁻¹ * u⁻¹ =
          (u * g⁻¹ * u⁻¹) * (u * w⁻¹ * u⁻¹) * (u * g * u⁻¹) := by group
      rw [e, hugi, hwi, hug]
      have hcs : s₀⁻¹ * w⁻¹ * s₀ = w⁻¹ := by
        have := hcomm s₀⁻¹ (S.inv_mem hs₀S) w⁻¹ (S.inv_mem hwS)
        calc s₀⁻¹ * w⁻¹ * s₀ = (w⁻¹ * s₀⁻¹) * s₀ := by rw [this]
          _ = w⁻¹ := by group
      calc g * s₀⁻¹ * w⁻¹ * (s₀ * g⁻¹) = g * (s₀⁻¹ * w⁻¹ * s₀) * g⁻¹ := by group
        _ = g * w⁻¹ * g⁻¹ := by rw [hcs]
    have hxb : g⁻¹ * w * g = g * g * w * (g * g)⁻¹ := by
      have := hg3c w hwS
      calc g⁻¹ * w * g = (g * g) * ((g * g * g)⁻¹ * w * (g * g * g)) * (g * g)⁻¹ := by group
        _ = g * g * w * (g * g)⁻¹ := by rw [this]
    have hb : g * g * w * (g * g)⁻¹ = w * (g * w * g⁻¹) := by
      have hn := hnorm w hw
      have hwa : w * (g * w * g⁻¹) ∈ S := S.mul_mem hwS ha
      have h1 : (w * (g * w * g⁻¹)) * (g * g * w * (g * g)⁻¹) = 1 := hn
      have h2 := hsq _ hwa
      exact (mul_left_cancel (h1.trans h2.symm))
    calc (g⁻¹ * w * g) * u * (g⁻¹ * w * g)⁻¹ * u⁻¹
        = (g⁻¹ * w * g) * (u * (g⁻¹ * w * g)⁻¹ * u⁻¹) := by group
      _ = (g * g * w * (g * g)⁻¹) * (g * w⁻¹ * g⁻¹) := by rw [hux, hxb]
      _ = (w * (g * w * g⁻¹)) * (g * w⁻¹ * g⁻¹) := by rw [hb]
      _ = w := by group
  have hphi_mul : ∀ x ∈ X, ∀ y ∈ X, u * (x * y) * u⁻¹ * (x * y)⁻¹ =
      (u * x * u⁻¹ * x⁻¹) * (u * y * u⁻¹ * y⁻¹) := by
    intro x hx y hy
    have hxS : x ∈ S := hXS hx
    have hyS : y ∈ S := hXS hy
    have h1 : u * y * u⁻¹ * y⁻¹ ∈ S := hWS (huSW y hyS)
    have hc := hcomm x hxS _ h1
    calc u * (x * y) * u⁻¹ * (x * y)⁻¹
        = (u * x * u⁻¹ * x⁻¹) * (x * (u * y * u⁻¹ * y⁻¹) * x⁻¹) := by group
      _ = (u * x * u⁻¹ * x⁻¹) * ((u * y * u⁻¹ * y⁻¹) * x * x⁻¹) := by rw [← hc]
      _ = (u * x * u⁻¹ * x⁻¹) * (u * y * u⁻¹ * y⁻¹) := by group
  have huniq : ∀ x ∈ X, ∀ z ∈ W, u * x * u⁻¹ * x⁻¹ = z → x = g⁻¹ * z * g := by
    intro x hx z hz hxz
    set x' := g⁻¹ * z * g with hx'
    have hx'X : x' ∈ X := (hXg x').mpr (by
      have : g * x' * g⁻¹ = z := by rw [hx']; group
      rw [this]; exact hz)
    have hkx' := hKI z hz
    have hphi' : u * x' * u⁻¹ * x'⁻¹ = z⁻¹ := by
      have : u * x' * u⁻¹ * x'⁻¹ = (x' * u * x'⁻¹ * u⁻¹)⁻¹ := by group
      rw [this, show x' * u * x'⁻¹ * u⁻¹ = z from hkx']
    have hzz : z⁻¹ = z := inv_eq_of_mul_eq_one_right (hsq z (hWS hz))
    have hx'inv : x'⁻¹ ∈ X := by
      refine (hXg _).mpr ?_
      have : g * x'⁻¹ * g⁻¹ = z⁻¹ := by rw [hx']; group
      rw [this]; exact W.inv_mem hz
    have hy : x * x'⁻¹ ∈ X := by
      refine (hXg _).mpr ?_
      have e : g * (x * x'⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * x'⁻¹ * g⁻¹) := by group
      rw [e]
      exact W.mul_mem ((hXg x).mp hx) ((hXg _).mp hx'inv)
    have hphiinv : u * x'⁻¹ * u⁻¹ * (x'⁻¹)⁻¹ = (u * x' * u⁻¹ * x'⁻¹)⁻¹ := by
      have h1 := hphi_mul x' hx'X x'⁻¹ hx'inv
      rw [mul_inv_cancel] at h1
      have h2 : u * (1 : Γ) * u⁻¹ * (1 : Γ)⁻¹ = 1 := by group
      rw [h2] at h1
      exact eq_inv_of_mul_eq_one_right h1.symm
    have h0 : u * (x * x'⁻¹) * u⁻¹ * (x * x'⁻¹)⁻¹ = 1 := by
      rw [hphi_mul x hx x'⁻¹ hx'inv, hphiinv, hxz, hphi', hzz]
      exact mul_inv_cancel z
    have := hker _ hy h0
    calc x = (x * x'⁻¹) * x' := by group
      _ = x' := by rw [this, one_mul]
  exact ⟨hnorm, hKI, huniq, hfix⟩


theorem perm3_conj_inv : ∀ a b : Equiv.Perm (Fin 3), a ^ 2 = 1 → a ≠ 1 → b ^ 3 = 1 → b ≠ 1 →
    a * b * a⁻¹ * b = 1 := by decide

theorem perm3_sign_pow : ∀ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 → σ ^ 3 = 1 := by decide

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

namespace Hyp1281Two

noncomputable def phiS3 (h : Hyp1281Two G T M L) : ↥(L ⊔ T) →* Equiv.Perm (Fin 3) :=
  (Classical.choice h.sThree).toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(L ⊔ T)))

theorem phiS3_eq_one_iff (h : Hyp1281Two G T M L) (x : ↥(L ⊔ T)) :
    h.phiS3 x = 1 ↔ (x : G) ∈ pCoreOf 2 (L ⊔ T) := by
  have e1 : h.phiS3 x = 1 ↔ (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(L ⊔ T)) x) = 1 := by
    constructor
    · intro h1
      refine (Classical.choice h.sThree).injective ?_
      rw [map_one]
      exact h1
    · intro h1
      show (Classical.choice h.sThree) (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(L ⊔ T)) x) = 1
      rw [h1, map_one]
  rw [e1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (Subgroup.mem_map_iff_mem (L ⊔ T).subtype_injective).symm

theorem pow_three_mem_pCoreOf_LT (h : Hyp1281Two G T M L) {x : G} (hx : x ∈ L) :
    x ^ 3 ∈ pCoreOf 2 (L ⊔ T) := by
  let ι : ↥L →* ↥(L ⊔ T) := Subgroup.inclusion le_sup_left
  let N : Subgroup ↥L := MonoidHom.ker (Equiv.Perm.sign.comp (h.phiS3.comp ι))
  have htop : N = ⊤ := by
    refine eq_top_of_oTwoUpper_eq h.residual.symm N fun y => ⟨1, ?_⟩
    rw [MonoidHom.mem_ker, pow_one]
    simp only [MonoidHom.comp_apply, map_pow]
    exact Int.units_pow_two _
  have hxN : (⟨x, hx⟩ : ↥L) ∈ N := by rw [htop]; exact Subgroup.mem_top _
  have h1 : Equiv.Perm.sign (h.phiS3 (ι ⟨x, hx⟩)) = 1 := hxN
  have h2 : (h.phiS3 (ι ⟨x, hx⟩)) ^ 3 = 1 := perm3_sign_pow _ h1
  rw [← map_pow, ← map_pow] at h2
  exact (h.phiS3_eq_one_iff _).mp h2

theorem mul_mul_inv_mul_mem_pCoreOf_LT (h : Hyp1281Two G T M L) {a b : G} (ha : a ∈ L ⊔ T)
    (hb : b ∈ L ⊔ T) (ha2 : a ^ 2 ∈ pCoreOf 2 (L ⊔ T)) (ha1 : a ∉ pCoreOf 2 (L ⊔ T))
    (hb3 : b ^ 3 ∈ pCoreOf 2 (L ⊔ T)) (hb1 : b ∉ pCoreOf 2 (L ⊔ T)) :
    a * b * a⁻¹ * b ∈ pCoreOf 2 (L ⊔ T) := by
  have h2 : h.phiS3 (⟨a, ha⟩ ^ 2) = 1 := (h.phiS3_eq_one_iff _).mpr ha2
  have h3 : h.phiS3 (⟨b, hb⟩ ^ 3) = 1 := (h.phiS3_eq_one_iff _).mpr hb3
  have h1a : h.phiS3 ⟨a, ha⟩ ≠ 1 := fun he => ha1 ((h.phiS3_eq_one_iff _).mp he)
  have h1b : h.phiS3 ⟨b, hb⟩ ≠ 1 := fun he => hb1 ((h.phiS3_eq_one_iff _).mp he)
  rw [map_pow] at h2 h3
  have := perm3_conj_inv _ _ h2 h1a h3 h1b
  have h4 : h.phiS3 (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv]
    exact this
  exact (h.phiS3_eq_one_iff _).mp h4

section Mod

variable (h : Hyp1281Two G T M L)

include h

theorem VZ_le_pCoreOf_LT : VZ T M ≤ pCoreOf 2 (L ⊔ T) := by
  rw [← h.centralizer]
  refine le_inf (h.isTwoReducedIn.2.trans le_sup_right) fun x hx => ?_
  exact Subgroup.mem_centralizer_iff.mpr fun y hy => h.almostSpecialHyp_g1.commV hy hx

theorem sq_mem_pCoreOf_LT {u : G} (hu : u ∈ uOfL22 T M) : u ^ 2 ∈ pCoreOf 2 (L ⊔ T) :=
  h.VZ_le_pCoreOf_LT (omegaOneCenter_le_VZ T M (h.sq_mem_omegaOneCenter hu))

theorem pCoreOf_LT_le_centralizer : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (VZ T M : Set G) := by
  rw [← h.centralizer]
  exact inf_le_right

theorem not_mem_pCoreOf_LT_of_not_mem_W {u : G} (hu : u ∈ uOfL22 T M) (huW : u ∉ wOfU T M) :
    u ∉ pCoreOf 2 (L ⊔ T) := fun hmem => huW ⟨hu, h.pCoreOf_LT_le_centralizer hmem⟩

theorem not_mem_pCoreOf_LT_of_goodElt {g : G} (hg : GoodElt128 T L g) :
    g ∉ pCoreOf 2 (L ⊔ T) := by
  intro hmem
  apply hg.not_mem
  have hc : g ∈ Subgroup.centralizer (VZ T M : Set G) := h.pCoreOf_LT_le_centralizer hmem
  rw [h.normalizer_Z_eq_centralizer]
  exact Subgroup.centralizer_le (omegaOneCenter_le_VZ T M) hc

variable (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g)

include hU hg

theorem mul_mul_mem_pCoreOf_sup : g * g * g ∈ pCoreOf 2 (L ⊔ uOfL22 T M) := by
  rw [h.pCoreOf_sup_uOfL22_eq hU hg]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (hg.mem_sup _) (hg.mem_sup _)) (hg.mem_sup _), ?_⟩
  have := h.pCoreOf_LT_le_centralizer (h.pow_three_mem_pCoreOf_LT hg.mem)
  have e : g ^ 3 = g * g * g := by rw [pow_succ, pow_two]
  rwa [e] at this

theorem mul_mul_inv_mul_mem_pCoreOf_sup {u : G} (hu : u ∈ uOfL22 T M) (huW : u ∉ wOfU T M) :
    u * g * u⁻¹ * g ∈ pCoreOf 2 (L ⊔ uOfL22 T M) := by
  have huLT : u ∈ L ⊔ T := Subgroup.mem_sup_right (h.uOfL22_le_T hu)
  have hgLT : g ∈ L ⊔ T := Subgroup.mem_sup_left hg.mem
  have h1 := h.mul_mul_inv_mul_mem_pCoreOf_LT huLT hgLT (h.sq_mem_pCoreOf_LT hu)
    (h.not_mem_pCoreOf_LT_of_not_mem_W hu huW) (h.pow_three_mem_pCoreOf_LT hg.mem)
    (h.not_mem_pCoreOf_LT_of_goodElt hg)
  rw [h.pCoreOf_sup_uOfL22_eq hU hg]
  refine ⟨?_, h.pCoreOf_LT_le_centralizer h1⟩
  have huI : u ∈ L ⊔ uOfL22 T M := Subgroup.mem_sup_right hu
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ huI (hg.mem_sup _))
    (Subgroup.inv_mem _ huI)) (hg.mem_sup _)

theorem module_relations {u : G} (hu : u ∈ uOfL22 T M) (huW : u ∉ wOfU T M) :
    (∀ w ∈ wOfU T M, w * (g * w * g⁻¹) * (g * g * w * (g * g)⁻¹) ∈
        wOfU T M ⊓ rconj (wOfU T M) g) ∧
      (∀ w ∈ wOfU T M, (g⁻¹ * w * g) * u * (g⁻¹ * w * g)⁻¹ * u⁻¹ * w⁻¹ ∈
        wOfU T M ⊓ rconj (wOfU T M) g) ∧
      (∀ x ∈ rconj (wOfU T M) g, ∀ ζ ∈ wOfU T M,
        (u * x * u⁻¹ * x⁻¹)⁻¹ * ζ ∈ wOfU T M ⊓ rconj (wOfU T M) g →
          x⁻¹ * (g⁻¹ * ζ * g) ∈ wOfU T M ⊓ rconj (wOfU T M) g) ∧
      (∀ c ∈ pCoreOf 2 (L ⊔ uOfL22 T M), (g * c * g⁻¹)⁻¹ * c ∈ wOfU T M ⊓ rconj (wOfU T M) g →
        c ∈ wOfU T M ⊓ rconj (wOfU T M) g) := by
  set U := uOfL22 T M with hUdef
  set W := wOfU T M with hWdef
  set X := rconj W g with hXdef
  set E := W ⊓ X with hEdef
  set I := L ⊔ U with hIdef
  set Sg := pCoreOf 2 I with hSdef
  have hEU : E = U ⊓ rconj U g := h.wOfU_inf_rconj_eq hU hg
  have hEN : I ≤ Subgroup.normalizer (E : Set G) := by
    rw [hEU]
    exact h.sup_le_normalizer_inf_rconj hU hg
  have hEnorm : (E.subgroupOf I).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hEN
  let π : ↥I →* ↥I ⧸ E.subgroupOf I := QuotientGroup.mk' _
  have hEq : ∀ a b : ↥I, π a = π b ↔ (a : G)⁻¹ * b ∈ E := fun a b => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rfl
  have hπ1 : ∀ a : ↥I, π a = 1 ↔ (a : G) ∈ E := fun a => by
    have := hEq a 1
    rw [map_one] at this
    rw [this]
    simp
  have hKq : ∀ K : Subgroup G, E ≤ K → ∀ a : ↥I, π a ∈ (K.subgroupOf I).map π ↔ (a : G) ∈ K := by
    intro K hEK a
    constructor
    · rintro ⟨k, hk, hka⟩
      have hk' : (k : G) ∈ K := hk
      have h2 : (k : G)⁻¹ * a ∈ E := (hEq k a).mp hka
      have e : (a : G) = k * ((k : G)⁻¹ * a) := by group
      rw [e]
      exact K.mul_mem hk' (hEK h2)
    · intro ha
      exact ⟨a, ha, rfl⟩
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hEW : E ≤ W := inf_le_left
  have hEX : E ≤ X := inf_le_right
  have hES : E ≤ Sg := (inf_le_left.trans (h.wOfU_le_pCoreOf hU hg))
  have hWI : W ≤ I := (wOfU_le_uOfL22 T M).trans le_sup_right
  have hSI : Sg ≤ I := pCoreOf_le 2 I
  have hSW : W ≤ Sg := h.wOfU_le_pCoreOf hU hg
  have hSX : X ≤ Sg := h.rconj_wOfU_le_pCoreOf hU hg
  have hXI : X ≤ I := hSX.trans hSI
  have hSset : ((Sg : Subgroup G) : Set G) = (W : Set G) * (X : Set G) :=
    (h.pCoreOf_sup_uOfL22_eq_wOfU_sup hU hg).2
  have huI : u ∈ I := Subgroup.mem_sup_right hu
  have hgI : g ∈ I := hg.mem_sup U
  have hmem : ∀ (K : Subgroup G) (a : ↥I ⧸ E.subgroupOf I),
      a ∈ (K.subgroupOf I).map π ↔ ∃ y : ↥I, (y : G) ∈ K ∧ π y = a := fun K a => by
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have hZE : quasithinOmegaOneCenter T ≤ E := h.omegaOneCenter_le_inf_rconj hU hg
  have hVE : VZ T M ≤ E := by
    rw [hEU]
    exact h.VZ_le_inf_rconj hU hg
  have hπcomm : ∀ x y : ↥I, ((x : G) ∈ W ∨ (x : G) ∈ X) → ((y : G) ∈ W ∨ (y : G) ∈ X) →
      π x * π y = π y * π x := by
    intro x y hx hy
    rw [← map_mul, ← map_mul, hEq]
    have e : ((x * y : ↥I) : G)⁻¹ * ((y * x : ↥I) : G) = (y : G)⁻¹ * (x : G)⁻¹ * y * x := by
      simp [mul_assoc]
    rw [e]
    have hWX' : ∀ a ∈ W, ∀ b ∈ X, (b : G)⁻¹ * a⁻¹ * b * a ∈ E := by
      intro a ha b hb
      have h1 : ⁅b⁻¹, a⁻¹⁆ ∈ ⁅X, W⁆ :=
        Subgroup.commutator_mem_commutator (X.inv_mem hb) (W.inv_mem ha)
      rw [Subgroup.commutator_comm] at h1
      have h2 := h.commutator_wOfU_rconj_le hU hg h1
      have e2 : ⁅b⁻¹, a⁻¹⁆ = b⁻¹ * a⁻¹ * b * a := by simp [commutatorElement_def]
      rw [e2] at h2
      exact h2
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · have := h.commutator_mem_omegaOneCenter (x := (y : G)⁻¹) (y := (x : G)⁻¹)
        (U.inv_mem (wOfU_le_uOfL22 T M hy)) (U.inv_mem (wOfU_le_uOfL22 T M hx))
      simp only [inv_inv] at this
      exact hZE this
    · exact hWX' _ hx _ hy
    · have := hWX' _ hy _ hx
      have e3 : ∀ a b : G, b⁻¹ * a⁻¹ * b * a = (a⁻¹ * b⁻¹ * a * b)⁻¹ := fun a b => by group
      rw [e3]
      exact E.inv_mem this
    · have := h.commutator_rconj_uOfL22_mem_VZ hU hg (a := (y : G)⁻¹) (b := (x : G)⁻¹)
        (by
          have : (y : G) ∈ rconj U g := by
            rw [mem_rconj] at hy ⊢
            exact wOfU_le_uOfL22 T M hy
          exact (rconj U g).inv_mem this)
        (by
          have : (x : G) ∈ rconj U g := by
            rw [mem_rconj] at hx ⊢
            exact wOfU_le_uOfL22 T M hx
          exact (rconj U g).inv_mem this)
      simp only [inv_inv] at this
      exact hVE this
  have hXUg : X ≤ rconj U g := by
    intro y hy
    have hy' : y ∈ rconj W g := hy
    rw [mem_rconj] at hy'
    rw [mem_rconj]
    exact wOfU_le_uOfL22 T M hy'
  have hSdec : ∀ a : ↥I, (a : G) ∈ Sg → ∃ w ∈ W, ∃ x ∈ X, (a : G) = w * x := by
    intro a ha
    have : (a : G) ∈ (W : Set G) * (X : Set G) := by rw [← hSset]; exact ha
    obtain ⟨w, hw, x, hx, hwx⟩ := this
    exact ⟨w, hw, x, hx, hwx.symm⟩
  have hSq : ∀ s' ∈ (Sg.subgroupOf I).map π, ∃ w x : ↥I, (w : G) ∈ W ∧ (x : G) ∈ X ∧
      s' = π w * π x := by
    intro s' hs'
    obtain ⟨a, ha, rfl⟩ := (hmem Sg s').mp hs'
    obtain ⟨w, hw, x, hx, hax⟩ := hSdec a ha
    refine ⟨⟨w, hWI hw⟩, ⟨x, hXI hx⟩, hw, hx, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hax
  have hcomm : ∀ a ∈ (Sg.subgroupOf I).map π, ∀ b ∈ (Sg.subgroupOf I).map π, a * b = b * a := by
    intro a ha b hb
    obtain ⟨w₁, x₁, hw₁, hx₁, rfl⟩ := hSq a ha
    obtain ⟨w₂, x₂, hw₂, hx₂, rfl⟩ := hSq b hb
    have c11 : Commute (π w₁) (π w₂) := hπcomm w₁ w₂ (Or.inl hw₁) (Or.inl hw₂)
    have c12 : Commute (π w₁) (π x₂) := hπcomm w₁ x₂ (Or.inl hw₁) (Or.inr hx₂)
    have c21 : Commute (π x₁) (π w₂) := hπcomm x₁ w₂ (Or.inr hx₁) (Or.inl hw₂)
    have c22 : Commute (π x₁) (π x₂) := hπcomm x₁ x₂ (Or.inr hx₁) (Or.inr hx₂)
    exact (Commute.mul_left (Commute.mul_right c11 c12) (Commute.mul_right c21 c22))
  have hsq : ∀ a ∈ (Sg.subgroupOf I).map π, a * a = 1 := by
    intro a ha
    obtain ⟨w, x, hw, hx, rfl⟩ := hSq a ha
    have c : π w * π x = π x * π w := hπcomm w x (Or.inl hw) (Or.inr hx)
    have hw2 : π w * π w = 1 := by
      rw [← map_mul, hπ1]
      have := h.sq_mem_omegaOneCenter (wOfU_le_uOfL22 T M hw)
      rw [pow_two] at this
      exact hZE this
    have hx2 : π x * π x = 1 := by
      rw [← map_mul, hπ1]
      have h1 := (h.l2Setting128 hU).rconj_sq_mem (hXUg hx)
      have h2 := (h.l2Setting128 hU).V₁_le_rconj_V hg.mem h1
      rw [pow_two] at h2
      exact hVE h2
    calc π w * π x * (π w * π x) = π w * (π x * π w) * π x := by group
      _ = π w * (π w * π x) * π x := by rw [← c]
      _ = (π w * π w) * (π x * π x) := by group
      _ = 1 := by rw [hw2, hx2, one_mul]
  have hWS' : (W.subgroupOf I).map π ≤ (Sg.subgroupOf I).map π := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := (hmem W a).mp ha
    exact (hmem Sg _).mpr ⟨y, hSW hy, rfl⟩
  have hXS' : (X.subgroupOf I).map π ≤ (Sg.subgroupOf I).map π := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := (hmem X a).mp ha
    exact (hmem Sg _).mpr ⟨y, hSX hy, rfl⟩
  have hSWX : ∀ s ∈ (Sg.subgroupOf I).map π, ∃ w ∈ (W.subgroupOf I).map π,
      ∃ x ∈ (X.subgroupOf I).map π, s = w * x := by
    intro s hs
    obtain ⟨w, x, hw, hx, rfl⟩ := hSq s hs
    exact ⟨π w, (hmem W _).mpr ⟨w, hw, rfl⟩, π x, (hmem X _).mpr ⟨x, hx, rfl⟩, rfl⟩
  have hXg : ∀ x : ↥I ⧸ E.subgroupOf I, x ∈ (X.subgroupOf I).map π ↔
      π ⟨g, hgI⟩ * x * (π ⟨g, hgI⟩)⁻¹ ∈ (W.subgroupOf I).map π := by
    intro x
    obtain ⟨y, rfl⟩ := hπsurj x
    have e : π ⟨g, hgI⟩ * π y * (π ⟨g, hgI⟩)⁻¹ = π (⟨g, hgI⟩ * y * ⟨g, hgI⟩⁻¹) := by
      simp [map_mul, map_inv]
    rw [e, hKq X hEX, hKq W hEW]
    exact mem_rconj
  have hWX : ∀ a ∈ (W.subgroupOf I).map π, a ∈ (X.subgroupOf I).map π → a = 1 := by
    intro a haW haX
    obtain ⟨y, hyW, rfl⟩ := (hmem W a).mp haW
    have hyX := (hKq X hEX y).mp haX
    exact (hπ1 y).mpr ⟨hyW, hyX⟩
  have hgS : ∀ s ∈ (Sg.subgroupOf I).map π,
      π ⟨g, hgI⟩ * s * (π ⟨g, hgI⟩)⁻¹ ∈ (Sg.subgroupOf I).map π := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := (hmem Sg s).mp hs
    have e : π ⟨g, hgI⟩ * π a * (π ⟨g, hgI⟩)⁻¹ = π (⟨g, hgI⟩ * a * ⟨g, hgI⟩⁻¹) := by
      simp [map_mul, map_inv]
    rw [e]
    exact (hmem Sg _).mpr ⟨_, (Subgroup.mem_normalizer_iff.mp (mem_normalizer_pCoreOf_sup g hg U)
      a).mp ha, rfl⟩
  have hg3 : π ⟨g, hgI⟩ * π ⟨g, hgI⟩ * π ⟨g, hgI⟩ ∈ (Sg.subgroupOf I).map π := by
    rw [← map_mul, ← map_mul]
    exact (hmem Sg _).mpr ⟨_, h.mul_mul_mem_pCoreOf_sup hU hg, rfl⟩
  have hu2 : π ⟨u, huI⟩ * π ⟨u, huI⟩ = 1 := by
    rw [← map_mul, hπ1]
    have := h.sq_mem_omegaOneCenter hu
    rw [pow_two] at this
    exact hZE this
  have huW' : ∀ w' ∈ (W.subgroupOf I).map π, π ⟨u, huI⟩ * w' * (π ⟨u, huI⟩)⁻¹ = w' := by
    intro w' hw'
    obtain ⟨y, hy, rfl⟩ := (hmem W w').mp hw'
    have e : π ⟨u, huI⟩ * π y * (π ⟨u, huI⟩)⁻¹ = π (⟨u, huI⟩ * y * ⟨u, huI⟩⁻¹) := by
      simp [map_mul, map_inv]
    rw [e, hEq]
    have := h.commutator_mem_omegaOneCenter (x := u) (y := (y : G)⁻¹) hu
      (U.inv_mem (wOfU_le_uOfL22 T M hy))
    have e2 : ((⟨u, huI⟩ * y * ⟨u, huI⟩⁻¹ : ↥I) : G)⁻¹ * (y : G) = u * (y : G)⁻¹ * u⁻¹ * (y : G) := by
      simp [mul_assoc]
    rw [e2]
    simpa using hZE this
  have huSW : ∀ s' ∈ (Sg.subgroupOf I).map π,
      π ⟨u, huI⟩ * s' * (π ⟨u, huI⟩)⁻¹ * s'⁻¹ ∈ (W.subgroupOf I).map π := by
    intro s' hs'
    obtain ⟨a, ha, rfl⟩ := (hmem Sg s').mp hs'
    have e : π ⟨u, huI⟩ * π a * (π ⟨u, huI⟩)⁻¹ * (π a)⁻¹ =
        π (⟨u, huI⟩ * a * ⟨u, huI⟩⁻¹ * a⁻¹) := by
      simp [map_mul, map_inv]
    rw [e, hKq W hEW]
    show u * (a : G) * u⁻¹ * (a : G)⁻¹ ∈ W
    rw [hWdef, h.wOfU_eq_inf_pCoreOf hU hg]
    refine ⟨?_, ?_⟩
    · have hau : (a : G) * u⁻¹ * (a : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp
          (h.pCoreOf_sup_uOfL22_le_normalizer_U hU hg ha) _).mp (U.inv_mem hu)
      have e3 : u * (a : G) * u⁻¹ * (a : G)⁻¹ = u * ((a : G) * u⁻¹ * (a : G)⁻¹) := by group
      rw [e3]
      exact U.mul_mem hu hau
    · have hua : u * (a : G) * u⁻¹ ∈ Sg :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 I huI) _).mp ha
      exact Sg.mul_mem hua (Sg.inv_mem ha)
  have hker : ∀ y' ∈ (X.subgroupOf I).map π,
      π ⟨u, huI⟩ * y' * (π ⟨u, huI⟩)⁻¹ * y'⁻¹ = 1 → y' = 1 := by
    intro y' hy' h1
    obtain ⟨y, hyX, rfl⟩ := (hmem X y').mp hy'
    have e : π ⟨u, huI⟩ * π y * (π ⟨u, huI⟩)⁻¹ * (π y)⁻¹ =
        π (⟨u, huI⟩ * y * ⟨u, huI⟩⁻¹ * y⁻¹) := by
      simp [map_mul, map_inv]
    rw [e, hπ1] at h1
    have h2 : (y : G) * u * (y : G)⁻¹ * u⁻¹ ∈ E := by
      have e2 : (y : G) * u * (y : G)⁻¹ * u⁻¹ = (u * (y : G) * u⁻¹ * (y : G)⁻¹)⁻¹ := by group
      rw [e2]
      exact E.inv_mem h1
    exact (hπ1 y).mpr (h.mem_inf_of_commutator_mem hU hg hu huW hyX h2)
  have hK2 : π ⟨u, huI⟩ * π ⟨g, hgI⟩ * (π ⟨u, huI⟩)⁻¹ * π ⟨g, hgI⟩ ∈
      (Sg.subgroupOf I).map π := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact (hmem Sg _).mpr ⟨_, h.mul_mul_inv_mul_mem_pCoreOf_sup hU hg hu huW, rfl⟩
  obtain ⟨hN, hKI, huniq, hfix⟩ := s3_module_core ((Sg.subgroupOf I).map π) ((W.subgroupOf I).map π)
    ((X.subgroupOf I).map π) (π ⟨g, hgI⟩) (π ⟨u, huI⟩) hcomm hsq hWS' hXS' hSWX hXg hWX hgS hg3 hu2
    huW' huSW hker hK2
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun x hx ζ hζ hxζ => ?_, fun c hc hcE => ?_⟩
  · have hn := hN (π ⟨w, hWI hw⟩) ((hmem W _).mpr ⟨_, hw, rfl⟩)
    have : π (⟨w, hWI hw⟩ * (⟨g, hgI⟩ * ⟨w, hWI hw⟩ * ⟨g, hgI⟩⁻¹) *
        (⟨g, hgI⟩ * ⟨g, hgI⟩ * ⟨w, hWI hw⟩ * (⟨g, hgI⟩ * ⟨g, hgI⟩)⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      exact hn
    exact (hπ1 _).mp this
  · have hn := hKI (π ⟨w, hWI hw⟩) ((hmem W _).mpr ⟨_, hw, rfl⟩)
    have h1 : π (⟨g, hgI⟩⁻¹ * ⟨w, hWI hw⟩ * ⟨g, hgI⟩ * ⟨u, huI⟩ *
        (⟨g, hgI⟩⁻¹ * ⟨w, hWI hw⟩ * ⟨g, hgI⟩)⁻¹ * ⟨u, huI⟩⁻¹ * ⟨w, hWI hw⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv] at hn ⊢
      rw [hn]
      group
    exact (hπ1 _).mp h1
  · have hxI : x ∈ I := hXI hx
    have hζI : ζ ∈ I := hWI hζ
    have h1 : π (⟨u, huI⟩ * ⟨x, hxI⟩ * ⟨u, huI⟩⁻¹ * ⟨x, hxI⟩⁻¹) = π ⟨ζ, hζI⟩ := by
      rw [hEq]
      exact hxζ
    have h2 := huniq (π ⟨x, hxI⟩) ((hmem X _).mpr ⟨_, hx, rfl⟩) (π ⟨ζ, hζI⟩)
      ((hmem W _).mpr ⟨_, hζ, rfl⟩) (by simpa only [map_mul, map_inv] using h1)
    have h3 : π ⟨x, hxI⟩ = π (⟨g, hgI⟩⁻¹ * ⟨ζ, hζI⟩ * ⟨g, hgI⟩) := by
      simpa only [map_mul, map_inv] using h2
    rw [hEq] at h3
    exact h3
  · have hcI : c ∈ I := hSI hc
    have h1 : π ⟨g, hgI⟩ * π ⟨c, hcI⟩ * (π ⟨g, hgI⟩)⁻¹ = π ⟨c, hcI⟩ := by
      have e : π ⟨g, hgI⟩ * π ⟨c, hcI⟩ * (π ⟨g, hgI⟩)⁻¹ =
          π (⟨g, hgI⟩ * ⟨c, hcI⟩ * ⟨g, hgI⟩⁻¹) := by
        simp only [map_mul, map_inv]
      rw [e, hEq]
      exact hcE
    exact (hπ1 _).mp (hfix _ ((hmem Sg _).mpr ⟨_, hc, rfl⟩) h1)

end Mod

end Hyp1281Two

end CFSG.Quasithin
