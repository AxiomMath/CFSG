module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHatVec
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHatSwap
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatVec
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsEleven

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

theorem not_rconj_wA_le_wA (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g)
    (hU4 : 4 < (centerOf (uA V V₁)).relIndex (uA V V₁)) : ¬ rconj (wA V V₁) g ≤ wA V V₁ := by
  intro hXW
  have hE : wA V V₁ ⊓ rconj (wA V V₁) g = rconj (wA V V₁) g := inf_eq_right.mpr hXW
  have hXeqW : rconj (wA V V₁) g = wA V V₁ :=
    Subgroup.eq_of_le_of_card_ge hXW (by rw [card_rconj_eq])
  have hEW : wA V V₁ ⊓ rconj (wA V V₁) g = wA V V₁ := by rw [hE, hXeqW]
  have hEabel := (S.eleven_two hg).1
  have hC : centralizerMod (centerOf (uA V V₁)) (wA V V₁ ⊓ rconj (wA V V₁) g)
      (rconj (wA V V₁) g) = wA V V₁ ⊓ rconj (wA V V₁) g := by
    refine le_antisymm (centralizerMod_le_left _ _ _) fun e he => ⟨he,
      normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer (wA_le_uA V V₁ he.1)),
      fun x hx => ?_⟩
    have hxE : x ∈ wA V V₁ ⊓ rconj (wA V V₁) g := by rw [hE]; exact hx
    have hcomm : e * x = x * e :=
      congrArg Subtype.val (hEabel.1.is_comm.comm ⟨e, he⟩ ⟨x, hxE⟩)
    have h1 : e * x * e⁻¹ * x⁻¹ = 1 := by rw [hcomm]; group
    rw [h1]
    exact Subgroup.one_mem _
  have h4 := S.eleven_four hg
  rw [hC, hEW, sup_eq_left.mpr (centerOf_uA_le_wA V V₁)] at h4
  have hZuU : centerOf (uA V V₁) ≤ uA V V₁ := inf_le_left
  have hVU : V ≤ uA V V₁ := le_uA V V₁
  have hNorm : uA V V₁ ≤ Subgroup.normalizer (centerOf (uA V V₁) : Set G) :=
    fun u hu => normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer hu)
  have hsecond : (centerOf (uA V V₁)).relIndex (centerOf (uA V V₁) ⊔ V) =
      (V ⊓ centerOf (uA V V₁)).relIndex V := by
    have : ((centerOf (uA V V₁)).subgroupOf (uA V V₁)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hNorm
    have h1 := Subgroup.relIndex_sup_left (K := (centerOf (uA V V₁)).subgroupOf (uA V V₁))
      (H := V.subgroupOf (uA V V₁))
    rw [← Subgroup.subgroupOf_sup hZuU hVU, Subgroup.relIndex_subgroupOf (sup_le hZuU hVU),
      Subgroup.relIndex_subgroupOf hVU] at h1
    rw [h1, ← Subgroup.inf_relIndex_right, inf_comm]
  have hVV₁ : V₁.relIndex V = 2 := by
    have h1 := Subgroup.relIndex_mul_card V₁ V
    rw [inf_eq_left.2 S.V₁_le, S.card_V₁, S.card_V] at h1
    omega
  have hchain := Subgroup.relIndex_mul_relIndex (centerOf (uA V V₁)) (wA V V₁) (uA V V₁)
    (centerOf_uA_le_wA V V₁) (wA_le_uA V V₁)
  rw [S.relIndex_wA_eq_two, h4, sup_comm, hsecond, S.inf_centerOf, hVV₁] at hchain
  omega

theorem eleven_six (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) (D : HatModelU (uA V V₁))
    (hU4 : 4 < (centerOf (uA V V₁)).relIndex (uA V V₁))
    (hF : D.hat V < HatU.fixSpace D (rconj (wA V V₁) g)) :
    ∃ γ ∈ D.img (rconj (wA V V₁) g), γ ≠ 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (γ.toLinearMap - LinearMap.id)) ≤ 2 ∧
        D.hat V ≤ LinearMap.range (γ.toLinearMap - LinearMap.id) := by
  classical
  obtain ⟨a, haV, haZ⟩ := S.exists_mem_not_mem
  obtain ⟨hπa, -, hhatV⟩ := S.hat_V_cases D haV haZ
  have hXT : rconj (wA V V₁) g ≤ T := S.rconj_wA_le_T hg
  have hXN : rconj (wA V V₁) g ≤ Subgroup.normalizer (uA V V₁ : Set G) :=
    hXT.trans S.T_le_normalizer_uA
  have hrho_ne : ∀ (x : G) (hxX : x ∈ rconj (wA V V₁) g),
      x ∉ wA V V₁ ⊓ rconj (wA V V₁) g → D.ρ ⟨x, hXN hxX⟩ ≠ 1 := by
    intro x hxX hxE h1
    apply hxE
    rw [← (S.nine_five hg).1]
    exact ⟨hxX, normalizer_le_normalizer_centerOf _ (hXN hxX),
      (HatU.rho_eq_one_iff D ⟨x, hXN hxX⟩).mp h1⟩
  have hπ_mem : ∀ {x u : G} (hxN : x ∈ Subgroup.normalizer (uA V V₁ : Set G))
      (hu : u ∈ uA V V₁), D.ρ ⟨x, hxN⟩ (D.π u) = D.π u →
        x * u * x⁻¹ * u⁻¹ ∈ centerOf (uA V V₁) := by
    intro x u hxN hu hfix
    have h1 := HatU.rho_sub_π D hxN hu
    rw [hfix, sub_self] at h1
    have hmem : x * u * x⁻¹ * u⁻¹ ∈ uA V V₁ :=
      (uA V V₁).mul_mem (HatU.conj_mem hxN hu) ((uA V V₁).inv_mem hu)
    exact (HatU.π_eq_zero_iff D hmem).mp h1.symm
  have key : ∀ (x : G) (hxX : x ∈ rconj (wA V V₁) g), D.ρ ⟨x, hXN hxX⟩ ≠ 1 →
      (∀ w ∈ wA V V₁, x * w * x⁻¹ * w⁻¹ ∈ centerOf (uA V V₁) ⊔ V) →
        ∃ γ ∈ D.img (rconj (wA V V₁) g), γ ≠ 1 ∧
          Module.finrank (ZMod 2) (LinearMap.range (γ.toLinearMap - LinearMap.id)) ≤ 2 ∧
            D.hat V ≤ LinearMap.range (γ.toLinearMap - LinearMap.id) := by
    intro x hxX hne hxw
    have hxN := hXN hxX
    have hW : ∀ v, D.B (D.π a) v = 0 →
        D.ρ ⟨x, hxN⟩ v - v ∈ Submodule.span (ZMod 2) {D.π a} := by
      intro v hv
      obtain ⟨w, hwW, hwU, hwv⟩ := (HatU.mem_hat D).mp ((S.mem_hat_wA_iff D haV haZ).mpr hv)
      rw [← hwv, HatU.rho_sub_π D hxN hwU]
      exact S.π_mem_span_of_mem_sup D haV haZ (hxw w hwW)
    have hLA := isometry_range_of_fixing_point D.B (fun v hv => HatU.B_nondegenerate D v hv)
      (D.ρ ⟨x, hxN⟩) (HatU.B_rho D ⟨x, hxN⟩) hπa hW hne
    refine ⟨D.ρ ⟨x, hxN⟩, HatU.rho_mem_img D hxX hxN, hne, hLA.1, ?_⟩
    intro v hv
    rcases hhatV v hv with h0 | h0
    · rw [h0]
      exact Submodule.zero_mem _
    · rw [h0]
      exact hLA.2
  by_cases hZE : rconj (centerOf (uA V V₁)) g ≤ wA V V₁ ⊓ rconj (wA V V₁) g
  swap
  ·
    obtain ⟨x, hxZ, hxE⟩ := IsConcreteLE.not_le_iff_exists.mp hZE
    have hxX : x ∈ rconj (wA V V₁) g := rconj_centerOf_le_rconj_wA V V₁ g hxZ
    refine key x hxX (hrho_ne x hxX hxE) (fun w hw => ?_)
    have hcomm : ⁅w, x⁆ ∈ centerOf (uA V V₁) ⊔ V :=
      S.ten_four hg (Subgroup.commutator_mem_commutator hw hxZ)
    have hinv : x * w * x⁻¹ * w⁻¹ = ⁅w, x⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hinv]
    exact (centerOf (uA V V₁) ⊔ V).inv_mem hcomm
  ·
    obtain ⟨v₀, hv₀F, hv₀V⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp hF).2
    obtain ⟨f, hfU, hπf⟩ := D.π_surj v₀
    have hXnW := S.not_rconj_wA_le_wA hg hU4
    have hfix : ∀ (x : G) (hxX : x ∈ rconj (wA V V₁) g),
        D.ρ ⟨x, hXN hxX⟩ (D.π f) = D.π f := by
      intro x hxX
      rw [hπf]
      exact (HatU.mem_fixSpace D).mp hv₀F _ (HatU.rho_mem_img D hxX (hXN hxX))
    have hfW : f ∈ wA V V₁ := by
      by_contra hfW
      apply hXnW
      intro x hxX
      have hcomm := hπ_mem (hXN hxX) hfU (hfix x hxX)
      have h9 := S.nine_six hg hfU hfW hxX hcomm
      rw [sup_eq_right.mpr hZE] at h9
      exact h9.1
    have hπfE : D.π f ∉ D.hat (wA V V₁ ⊓ rconj (wA V V₁) g) := by
      intro hmem
      obtain ⟨e, heE, heU, hπe⟩ := (HatU.mem_hat D).mp hmem
      have heC : e ∈ centralizerMod (centerOf (uA V V₁)) (wA V V₁ ⊓ rconj (wA V V₁) g)
          (rconj (wA V V₁) g) := by
        refine ⟨heE, normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer heU),
          fun x hx => ?_⟩
        have hfixe : D.ρ ⟨x, hXN hx⟩ (D.π e) = D.π e := by
          rw [hπe]
          exact hfix x hx
        have hc := hπ_mem (hXN hx) heU hfixe
        have e1 : e * x * e⁻¹ * x⁻¹ = (x * e * x⁻¹ * e⁻¹)⁻¹ := by group
        rw [e1]
        exact (centerOf (uA V V₁)).inv_mem hc
      have heVZ : e ∈ V ⊔ centerOf (uA V V₁) := by
        rw [← S.eleven_four hg]
        exact Subgroup.mem_sup_left heC
      apply hv₀V
      rw [← hπf, ← hπe]
      obtain ⟨v, hv, z, hz, rfl⟩ := exists_eq_mul_of_mem_sup_of_forall_commute
        (A := V) (B := centerOf (uA V V₁))
        (fun v hv z hz => Subgroup.mem_centralizer_iff.mp hz.2 v (le_uA V V₁ hv)) heVZ
      rw [D.π_mul v (le_uA V V₁ hv) z hz.1, (HatU.π_eq_zero_iff D hz.1).mpr hz, add_zero]
      exact HatU.π_mem_hat D hv (le_uA V V₁ hv)
    have hP3 : ∀ y ∈ rconj (wA V V₁) g,
        y * f * y⁻¹ * f⁻¹ ∈ centerOf (L ⊔ uA V V₁) ⊔ V₁ := by
      intro y hyX
      have hZ := hπ_mem (hXN hyX) hfU (hfix y hyX)
      have hfN : f ∈ Subgroup.normalizer (rconj (wA V V₁) g : Set G) :=
        S.pCoreOf_sup_le_normalizer_X hg (S.wA_le_pCoreOf hg hfW)
      have hcX : y * f * y⁻¹ * f⁻¹ ∈ rconj (wA V V₁) g := by
        have e : y * f * y⁻¹ * f⁻¹ = y * (f * y⁻¹ * f⁻¹) := by group
        rw [e]
        exact (rconj (wA V V₁) g).mul_mem hyX
          ((Subgroup.mem_normalizer_iff.mp hfN _).mp ((rconj (wA V V₁) g).inv_mem hyX))
      have hcUg : y * f * y⁻¹ * f⁻¹ ∈ rconj (uA V V₁) g :=
        rconj_le_rconj (wA_le_uA V V₁) g hcX
      have hmem : y * f * y⁻¹ * f⁻¹ ∈ centerOf (uA V V₁) ⊓ rconj (uA V V₁) g :=
        ⟨hZ, hcUg⟩
      rw [S.ten_one hg, S.ten_two hg] at hmem
      exact hmem
    obtain ⟨t, htN, htI, htZ, htW, htX⟩ := S.exists_swap hg
    have hXWt : rconj (wA V V₁) t = rconj (wA V V₁) g := by
      have h1 := congrArg (fun K => rconj K t) htX
      simp only [rconj_rconj_eq, inv_mul_cancel_right] at h1
      exact h1.symm
    have hx₀X : t * f * t⁻¹ ∈ rconj (wA V V₁) g := by
      have h1 := inv_mul_mul_mem_rconj (X := wA V V₁) (g := t⁻¹) hfW
      rw [htW, inv_inv] at h1
      exact h1
    have hx₀E : t * f * t⁻¹ ∉ wA V V₁ ⊓ rconj (wA V V₁) g := by
      intro hx₀E
      have hfX : f ∈ rconj (wA V V₁) g := by
        rw [← hXWt, mem_rconj]
        exact hx₀E.1
      exact hπfE (HatU.π_mem_hat D (A := wA V V₁ ⊓ rconj (wA V V₁) g) ⟨hfW, hfX⟩ hfU)
    refine key (t * f * t⁻¹) hx₀X (hrho_ne _ hx₀X hx₀E) (fun w hw => ?_)
    have hyX : t⁻¹ * w * t ∈ rconj (wA V V₁) g := by
      have h1 : w ∈ rconj (rconj (wA V V₁) g) t⁻¹ := by
        rw [htX]
        exact hw
      have h2 := mem_rconj.mp h1
      simpa using h2
    have hy1 := hP3 _ hyX
    have hy2 : f * (t⁻¹ * w * t) * f⁻¹ * (t⁻¹ * w * t)⁻¹ ∈ centerOf (L ⊔ uA V V₁) ⊔ V₁ := by
      have e : f * (t⁻¹ * w * t) * f⁻¹ * (t⁻¹ * w * t)⁻¹ =
          ((t⁻¹ * w * t) * f * (t⁻¹ * w * t)⁻¹ * f⁻¹)⁻¹ := by group
      rw [e]
      exact (centerOf (L ⊔ uA V V₁) ⊔ V₁).inv_mem hy1
    have hy3 := inv_mul_mul_mem_rconj (X := centerOf (L ⊔ uA V V₁) ⊔ V₁) (g := t⁻¹) hy2
    have htZI : rconj (centerOf (L ⊔ uA V V₁)) t⁻¹ = centerOf (L ⊔ uA V V₁) :=
      rconj_eq_of_mem_normalizer (normalizer_le_normalizer_centerOf _
        (Subgroup.le_normalizer (Subgroup.inv_mem _ htI)))
    rw [rconj_sup_eq, htZI, htZ, inv_inv] at hy3
    have hy4 : centerOf (L ⊔ uA V V₁) ⊔ rconj V₁ g ≤ centerOf (uA V V₁) ⊔ V := by
      refine sup_le ?_ ((S.l2Setting.V₁_le_rconj_V hg.mem).trans le_sup_right)
      rw [← S.ten_two hg]
      exact inf_le_left.trans le_sup_left
    have e2 : (t * f * t⁻¹) * w * (t * f * t⁻¹)⁻¹ * w⁻¹ =
        t * (f * (t⁻¹ * w * t) * f⁻¹ * (t⁻¹ * w * t)⁻¹) * t⁻¹ := by group
    rw [e2]
    exact hy4 hy3

end Setting

end L128A

end CFSG.Quasithin.H13
