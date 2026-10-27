module

public import CFSG.Quasithin.Background.OperatorJordanHolderJH1
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FS

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G} {α : ↥L →* SL4}

theorem fix_unitri_nat : ∀ x : FLc.Vt 4,
    (1 + single 0 1 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 2 3 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x → x = 0 ∨ x = Pi.single 0 1 := by
  decide +kernel

theorem fix_unitri_dual : ∀ x : FLc.Vt 4,
    (1 + single 1 0 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 2 1 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 3 2 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x → x = 0 ∨ x = Pi.single 3 1 := by
  decide +kernel

theorem transvection_mem_unitri {i j : Fin 4} (hij : i < j) (h : i ≠ j) :
    SpecialLinearGroup.transvection h (1 : ZMod 2) ∈ FLc.Ut 4 :=
  transvection_mem_unitriangular hij 1

omit [Finite G] in
theorem eq_one_or_eq_of_card_le_two {S : Subgroup G} [Finite S] (hS : Nat.card S ≤ 2) {a x : G}
    (ha : a ∈ S) (hx : x ∈ S) (ha1 : a ≠ 1) : x = 1 ∨ x = a := by
  by_contra hne
  push Not at hne
  have hinj : Function.Injective
      (![(⟨1, S.one_mem⟩ : S), ⟨a, ha⟩, ⟨x, hx⟩] : Fin 3 → S) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff, eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

omit [Finite G] in
theorem conj_mem_centralizer {Y : Subgroup G} {d x : G}
    (hd : d ∈ Subgroup.normalizer (Y : Set G)) (hx : x ∈ Subgroup.centralizer (Y : Set G)) :
    d * x * d⁻¹ ∈ Subgroup.centralizer (Y : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : d⁻¹ * y * d ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hd) y).mp hy
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hx _ hy'
  calc y * (d * x * d⁻¹) = d * ((d⁻¹ * y * d) * x) * d⁻¹ := by group
    _ = d * (x * (d⁻¹ * y * d)) * d⁻¹ := by rw [hc]
    _ = d * x * d⁻¹ * y := by group

variable {ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)} [IsMulCommutative ↥(vPlus L T)]

theorem exists_Z_coords (h : Hyp331 G T M L D) (hD : FData G T M L D α)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {U₁ U₂ : Subgroup ↥(vPlus L T)} (hsup : U₁ ⊔ U₂ = ⊤) (hdisj : U₁ ⊓ U₂ = ⊥)
    (D₁ : FLc.VModel 4 ρ U₁ ⊥ (Multiplicative (FLc.Vt 4)) (fun g a => FLc.actM g a))
    (D₂ : FLc.VModel 4 ρ U₂ ⊥ (Multiplicative (FLc.Vt 4)) FLc.actDl) :
    ∃ a b : G, a ∈ quasithinOmegaOneCenter T ∧ b ∈ quasithinOmegaOneCenter T ∧ a ≠ 1 ∧ b ≠ 1 ∧
      a ≠ b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧
      a ∈ Subgroup.centralizer (liftCore α (FLc.QI 4 {1}) : Set G) ∧
      b ∈ Subgroup.centralizer (liftCore α (FLc.QI 4 {3}) : Set G) ∧
      (∀ z ∈ quasithinOmegaOneCenter T, z = 1 ∨ z = a ∨ z = b ∨ z = a * b) ∧
      (∀ x ∈ quasithinOmegaOneCenter T,
        x ∈ Subgroup.centralizer (liftCore α (FLc.QI 4 {1}) : Set G) → x = 1 ∨ x = a) ∧
      (∀ x ∈ quasithinOmegaOneCenter T,
        x ∈ Subgroup.centralizer (liftCore α (FLc.QI 4 {3}) : Set G) → x = 1 ∨ x = b) := by
  classical
  have hVr := Hyp331.vPlus_reduced h.toSetup331
  have hVT : vPlus L T ≤ T := (hVr.1.trans inf_le_left).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf)
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hVr.2.2.2.1
  have hV2 : ∀ x ∈ vPlus L T, x ^ 2 = 1 := hVr.2.1.2
  have hZV : quasithinOmegaOneCenter T ≤ vPlus L T := le_conjClosure _ _
  obtain ⟨u₀, hu₀⟩ := D₁.surj (Multiplicative.ofAdd (Pi.single 0 1))
  obtain ⟨u₃, hu₃⟩ := D₂.surj (Multiplicative.ofAdd (Pi.single 3 1))
  have haV : ((u₀ : ↥(vPlus L T)) : G) ∈ vPlus L T := (u₀ : ↥(vPlus L T)).2
  have hbV : ((u₃ : ↥(vPlus L T)) : G) ∈ vPlus L T := (u₃ : ↥(vPlus L T)).2
  have ha1 : ((u₀ : ↥(vPlus L T)) : G) ≠ 1 := by
    intro h1
    have h0 : u₀ = 1 := Subtype.ext (Subtype.ext h1)
    rw [h0, map_one] at hu₀
    have h2 := congrFun (congrArg Multiplicative.toAdd hu₀) 0
    simp at h2
  have hb1 : ((u₃ : ↥(vPlus L T)) : G) ≠ 1 := by
    intro h1
    have h0 : u₃ = 1 := Subtype.ext (Subtype.ext h1)
    rw [h0, map_one] at hu₃
    have h2 := congrFun (congrArg Multiplicative.toAdd hu₃) 3
    simp at h2
  have hab : ((u₀ : ↥(vPlus L T)) : G) ≠ ((u₃ : ↥(vPlus L T)) : G) := by
    intro e
    have e' : (u₀ : ↥(vPlus L T)) = (u₃ : ↥(vPlus L T)) := Subtype.ext e
    have hm : (u₀ : ↥(vPlus L T)) ∈ U₁ ⊓ U₂ := ⟨u₀.2, e' ▸ u₃.2⟩
    rw [hdisj, Subgroup.mem_bot] at hm
    exact ha1 (by rw [hm]; rfl)
  have haY : ((u₀ : ↥(vPlus L T)) : G) ∈
      Subgroup.centralizer (liftCore α (FLc.QI 4 {1}) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    have hg' := L3318.mem_perfectCore_of_mem_liftCore hD.surj hy'
    have hmem' := D₁.inv (α ⟨y', liftCore_le α _ hy'⟩) (u₀ : ↥(vPlus L T)) u₀.2
    have hfix : (⟨ρ (α ⟨y', liftCore_le α _ hy'⟩) u₀, hmem'⟩ : ↥U₁) = u₀ := by
      apply FLc.VModel.β_injective D₁
      rw [D₁.equiv _ u₀ hmem', hu₀]
      exact actM_e0 (perfectCore_le _ hg')
    have h1 := congrArg (fun x : ↥U₁ => ((x : ↥(vPlus L T)) : G)) hfix
    simp only at h1
    rw [hαv, FLc.conjAct_coe] at h1
    calc y' * ((u₀ : ↥(vPlus L T)) : G) = (y' * u₀ * y'⁻¹) * y' := by group
      _ = u₀ * y' := by rw [h1]
  have hbY : ((u₃ : ↥(vPlus L T)) : G) ∈
      Subgroup.centralizer (liftCore α (FLc.QI 4 {3}) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    have hg' := L3318.mem_perfectCore_of_mem_liftCore hD.surj hy'
    have hmem' := D₂.inv (α ⟨y', liftCore_le α _ hy'⟩) (u₃ : ↥(vPlus L T)) u₃.2
    have hfix : (⟨ρ (α ⟨y', liftCore_le α _ hy'⟩) u₃, hmem'⟩ : ↥U₂) = u₃ := by
      apply FLc.VModel.β_injective D₂
      rw [D₂.equiv _ u₃ hmem', hu₃]
      exact actDl_e3 hg'
    have h1 := congrArg (fun x : ↥U₂ => ((x : ↥(vPlus L T)) : G)) hfix
    simp only at h1
    rw [hαv, FLc.conjAct_coe] at h1
    calc y' * ((u₃ : ↥(vPlus L T)) : G) = (y' * u₃ * y'⁻¹) * y' := by group
      _ = u₃ * y' := by rw [h1]
  have hc1 := card_centralizer_le_one h hD.surj hαv hsup hdisj D₁ D₂
  have hc3 := card_centralizer_le_three h hD.surj hαv hsup hdisj D₁ D₂
  have hVY1 : ∀ x ∈ vPlus L T, x ∈ Subgroup.centralizer (liftCore α (FLc.QI 4 {1}) : Set G) →
      x = 1 ∨ x = ((u₀ : ↥(vPlus L T)) : G) := fun x hx hxY =>
    eq_one_or_eq_of_card_le_two hc1 ⟨haV, haY⟩ ⟨hx, hxY⟩ ha1
  have hVY3 : ∀ x ∈ vPlus L T, x ∈ Subgroup.centralizer (liftCore α (FLc.QI 4 {3}) : Set G) →
      x = 1 ∨ x = ((u₃ : ↥(vPlus L T)) : G) := fun x hx hxY =>
    eq_one_or_eq_of_card_le_two hc3 ⟨hbV, hbY⟩ ⟨hx, hxY⟩ hb1
  have hfixT : ∀ {I : Set ℕ} {v : G}, v ∈ vPlus L T →
      v ∈ Subgroup.centralizer (liftCore α (FLc.QI 4 I) : Set G) → v ≠ 1 →
      (∀ x ∈ vPlus L T, x ∈ Subgroup.centralizer (liftCore α (FLc.QI 4 I) : Set G) →
        x = 1 ∨ x = v) → v ∈ quasithinOmegaOneCenter T := by
    intro I v hv hvY hv1 hVY
    have hTv : ∀ t ∈ T, t * v * t⁻¹ = v := by
      intro t ht
      have hmemV : t * v * t⁻¹ ∈ vPlus L T := (Subgroup.mem_normalizer_iff.mp (hTV ht) v).mp hv
      rcases hVY _ hmemV (conj_mem_centralizer (hD.le_normalizer_Y I ht) hvY) with h1 | h1
      · exact absurd ((conj_eq_one_iff).mp h1) hv1
      · exact h1
    refine Subgroup.subset_closure ⟨⟨hVT hv, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩,
      hV2 v hv⟩
    calc t * v = (t * v * t⁻¹) * t := by group
      _ = v * t := by rw [hTv t ht]
  have haZ := hfixT haV haY ha1 hVY1
  have hbZ := hfixT hbV hbY hb1 hVY3
  have hZ : ∀ z ∈ quasithinOmegaOneCenter T, z = 1 ∨ z = ((u₀ : ↥(vPlus L T)) : G) ∨
      z = ((u₃ : ↥(vPlus L T)) : G) ∨
        z = ((u₀ : ↥(vPlus L T)) : G) * ((u₃ : ↥(vPlus L T)) : G) := by
    intro z hz
    have hzT : z ∈ Subgroup.centralizer (T : Set G) :=
      ((B2F.omegaOneCenter_le_inf_centralizer T) hz).2
    have hvU : (⟨z, hZV hz⟩ : ↥(vPlus L T)) ∈ U₁ ⊔ U₂ := by
      rw [hsup]
      exact Subgroup.mem_top _
    obtain ⟨v₁, hv₁, v₂, hv₂, hv12⟩ := Subgroup.mem_sup.1 hvU
    have hz12 : z = ((v₁ : ↥(vPlus L T)) : G) * ((v₂ : ↥(vPlus L T)) : G) :=
      (congrArg Subtype.val hv12).symm
    have hfixz : ∀ g ∈ (FLc.Ut 4 : Set SL4), ρ g ⟨z, hZV hz⟩ = ⟨z, hZV hz⟩ := by
      intro g hg
      have hg' : g ∈ ((T ⊓ L).subgroupOf L).map α := by rw [hD.mapU]; exact hg
      obtain ⟨l, hl, rfl⟩ := hg'
      have hl' := Subgroup.mem_subgroupOf.1 hl
      rw [hαv]
      apply Subtype.ext
      rw [FLc.conjAct_coe]
      show (l : G) * z * (l : G)⁻¹ = z
      rw [Subgroup.mem_centralizer_iff.1 hzT l hl'.1, mul_inv_cancel_right]
    have hfix12 : ∀ g ∈ (FLc.Ut 4 : Set SL4), ρ g v₁ = v₁ ∧ ρ g v₂ = v₂ :=
      fun g hg => FLc.fixed_of_two hdisj (ρ g) (fun u hu => D₁.inv g u hu)
        (fun u hu => D₂.inv g u hu) hv₁ hv₂ (by rw [hv12]; exact hfixz g hg)
    have hb1' := beta_fix D₁ hv₁ (fun g hg => (hfix12 g hg).1)
    have hb2' := beta_fix D₂ hv₂ (fun g hg => (hfix12 g hg).2)
    have hβ1 : D₁.β ⟨v₁, hv₁⟩ = 1 ∨ D₁.β ⟨v₁, hv₁⟩ = Multiplicative.ofAdd (Pi.single 0 1) := by
      have e1 := congrArg Multiplicative.toAdd (hb1' _ (transvection_mem_unitri (i := 0) (j := 1)
        (by decide) (by decide)))
      have e2 := congrArg Multiplicative.toAdd (hb1' _ (transvection_mem_unitri (i := 1) (j := 2)
        (by decide) (by decide)))
      have e3 := congrArg Multiplicative.toAdd (hb1' _ (transvection_mem_unitri (i := 2) (j := 3)
        (by decide) (by decide)))
      rw [toAdd_actM_tr] at e1 e2 e3
      rcases fix_unitri_nat _ e1 e2 e3 with h0 | h0
      · exact Or.inl (Multiplicative.toAdd.injective (by rw [h0, toAdd_one]))
      · exact Or.inr (Multiplicative.toAdd.injective (by rw [h0, toAdd_ofAdd]))
    have hβ2 : D₂.β ⟨v₂, hv₂⟩ = 1 ∨ D₂.β ⟨v₂, hv₂⟩ = Multiplicative.ofAdd (Pi.single 3 1) := by
      have e1 := congrArg Multiplicative.toAdd (hb2' _ (transvection_mem_unitri (i := 0) (j := 1)
        (by decide) (by decide)))
      have e2 := congrArg Multiplicative.toAdd (hb2' _ (transvection_mem_unitri (i := 1) (j := 2)
        (by decide) (by decide)))
      have e3 := congrArg Multiplicative.toAdd (hb2' _ (transvection_mem_unitri (i := 2) (j := 3)
        (by decide) (by decide)))
      rw [toAdd_actDl_tr] at e1 e2 e3
      rcases fix_unitri_dual _ e1 e2 e3 with h0 | h0
      · exact Or.inl (Multiplicative.toAdd.injective (by rw [h0, toAdd_one]))
      · exact Or.inr (Multiplicative.toAdd.injective (by rw [h0, toAdd_ofAdd]))
    have hv₁' : ((v₁ : ↥(vPlus L T)) : G) = 1 ∨
        ((v₁ : ↥(vPlus L T)) : G) = ((u₀ : ↥(vPlus L T)) : G) := by
      rcases hβ1 with h1 | h1
      · left
        have : (⟨v₁, hv₁⟩ : ↥U₁) = 1 := FLc.VModel.β_injective D₁ (by rw [h1, map_one])
        rw [show v₁ = 1 from congrArg Subtype.val this]
        rfl
      · right
        have : (⟨v₁, hv₁⟩ : ↥U₁) = u₀ := FLc.VModel.β_injective D₁ (by rw [h1, hu₀])
        rw [show v₁ = (u₀ : ↥(vPlus L T)) from congrArg Subtype.val this]
    have hv₂' : ((v₂ : ↥(vPlus L T)) : G) = 1 ∨
        ((v₂ : ↥(vPlus L T)) : G) = ((u₃ : ↥(vPlus L T)) : G) := by
      rcases hβ2 with h1 | h1
      · left
        have : (⟨v₂, hv₂⟩ : ↥U₂) = 1 := FLc.VModel.β_injective D₂ (by rw [h1, map_one])
        rw [show v₂ = 1 from congrArg Subtype.val this]
        rfl
      · right
        have : (⟨v₂, hv₂⟩ : ↥U₂) = u₃ := FLc.VModel.β_injective D₂ (by rw [h1, hu₃])
        rw [show v₂ = (u₃ : ↥(vPlus L T)) from congrArg Subtype.val this]
    rcases hv₁' with h1 | h1 <;> rcases hv₂' with h2 | h2 <;> rw [hz12, h1, h2] <;> simp
  exact ⟨_, _, haZ, hbZ, ha1, hb1, hab, hV2 _ haV, hV2 _ hbV, haY, hbY, hZ,
    fun x hx hxY => hVY1 x (hZV hx) hxY, fun x hx hxY => hVY3 x (hZV hx) hxY⟩

omit [IsMulCommutative ↥(vPlus L T)] in
theorem pCoreOf_ne_bot_of_le_normalizer (h : Hyp331 G T M L D) {Y Y' : Subgroup G} {a b : G}
    (haZ : a ∈ quasithinOmegaOneCenter T) (hbZ : b ∈ quasithinOmegaOneCenter T) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (haY : a ∈ Subgroup.centralizer (Y : Set G)) (hbY : b ∈ Subgroup.centralizer (Y' : Set G))
    (hZ : ∀ z ∈ quasithinOmegaOneCenter T, z = 1 ∨ z = a ∨ z = b ∨ z = a * b)
    (hZY : ∀ x ∈ quasithinOmegaOneCenter T, x ∈ Subgroup.centralizer (Y' : Set G) →
      x = 1 ∨ x = b)
    (hDY : D ≤ Subgroup.normalizer (Y' : Set G)) : pCoreOf 2 (Y ⊔ T ⊔ D) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZT := B2F.omegaOneCenter_le_inf_centralizer T
  have hDZ : ∀ d ∈ D, ∀ z ∈ quasithinOmegaOneCenter T,
      d * z * d⁻¹ ∈ quasithinOmegaOneCenter T := fun d hd z hz =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.Quasithin.normalizer_le_normalizer_quasithinOmegaOneCenter T (h.DN hd)) z).mp hz
  have hDb : ∀ d ∈ D, d * b * d⁻¹ = b := by
    intro d hd
    rcases hZY _ (hDZ d hd b hbZ) (conj_mem_centralizer (hDY hd) hbY) with h1 | h1
    · exact absurd ((conj_eq_one_iff).mp h1) hb1
    · exact h1
  have hconj : ∀ (x : G) (n : ℕ), x * a * x⁻¹ = a → x ^ n * a * (x ^ n)⁻¹ = a := by
    intro x n hx
    induction n with
    | zero => simp
    | succ n ih =>
      calc x ^ (n + 1) * a * (x ^ (n + 1))⁻¹ = x ^ n * (x * a * x⁻¹) * (x ^ n)⁻¹ := by
            rw [pow_succ]
            group
        _ = a := by rw [hx, ih]
  have hDa : ∀ d ∈ D, d * a * d⁻¹ = a := by
    intro d hd
    rcases hZ _ (hDZ d hd a haZ) with h1 | h1 | h1 | h1
    · exact absurd ((conj_eq_one_iff).mp h1) ha1
    · exact h1
    · exfalso
      apply hab
      have e : d * a * d⁻¹ = d * b * d⁻¹ := h1.trans (hDb d hd).symm
      exact mul_left_cancel (mul_right_cancel e)
    · exfalso
      have h2 : (d * d) * a * (d * d)⁻¹ = a := by
        calc (d * d) * a * (d * d)⁻¹ = d * (d * a * d⁻¹) * d⁻¹ := by group
          _ = d * (a * b) * d⁻¹ := by rw [h1]
          _ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
          _ = (a * b) * b := by rw [h1, hDb d hd]
          _ = a := by rw [mul_assoc, ← sq, hb2, mul_one]
      have hodd : Odd (orderOf d) :=
        Odd.of_dvd_nat h.Dodd (Subgroup.orderOf_dvd_natCard D hd)
      obtain ⟨m, hm⟩ := hodd
      have hd' : d = (d * d) ^ (m + 1) := by
        rw [← sq, ← pow_mul]
        calc d = d ^ (orderOf d + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
          _ = d ^ (2 * (m + 1)) := by rw [hm]; ring_nf
      have h3 : d * a * d⁻¹ = a := by
        rw [hd']
        exact hconj _ _ h2
      apply hb1
      have e : a = a * b := h3.symm.trans h1
      calc b = a⁻¹ * (a * b) := by group
        _ = a⁻¹ * a := by rw [← e]
        _ = 1 := inv_mul_cancel a
  have hX : Y ⊔ T ⊔ D ≤ Subgroup.centralizer ({a} : Set G) := by
    refine sup_le (sup_le (fun y hy => ?_) (fun t ht => ?_)) (fun d hd => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp haY y hy
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hZT haZ).2 t ht
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc d * a = (d * a * d⁻¹) * d := by group
        _ = a * d := by rw [hDa d hd]
  intro hbot
  have hP : Subgroup.zpowers a ≤ pCoreOf 2 (Y ⊔ T ⊔ D) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ (fun x hx => ?_) ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (hZT haZ).1)
    · have hxa : x * a * x⁻¹ = a := by
        have := Subgroup.mem_centralizer_singleton_iff.mp (hX hx)
        rw [this, mul_inv_cancel_right]
      refine OperatorJH.mem_normalizer_of_conj_mem_of fun y hy => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← conj_zpow, hxa]
      exact Subgroup.zpow_mem_zpowers a n
    · have hcard : Nat.card ↥(Subgroup.zpowers a) = 2 ^ 1 := by
        rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1, pow_one]
      exact IsPGroup.of_card hcard
  rw [hbot] at hP
  exact ha1 (Subgroup.mem_bot.mp (hP (Subgroup.mem_zpowers a)))

end CFSG.Quasithin.H13.L3321
