module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GExt
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FA

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem card_le_comm [Finite G] {V Y : Subgroup G} [IsMulCommutative ↥V] {n : ℕ}
    {ρ : FLc.SLt n →* MulAut ↥V}
    {U' Z' : Subgroup ↥V} {A : Type} [CommGroup A] [Finite A] {act : FLc.SLt n → A → A}
    (D : FLc.VModel n ρ U' Z' A act) {P : Set (FLc.SLt n)}
    (hP : ∀ g ∈ P, ∃ y ∈ Y, ∀ v : ↥V, ((ρ g v : ↥V) : G) = y * v * y⁻¹)
    (hgen : Subgroup.closure {x | ∃ g ∈ P, ∃ b : A, x = act g b * b⁻¹} = ⊤) :
    Nat.card A ≤ Nat.card ↥⁅V, Y⁆ := by
  set W : Subgroup ↥U' := ((⁅V, Y⁆).subgroupOf V).subgroupOf U' with hW
  have hK : W.map D.β = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x ⟨g, hg, b, rfl⟩
    obtain ⟨u, hu⟩ := D.surj b
    obtain ⟨y, hyY, hy⟩ := hP g hg
    have hmem : (ρ g) (u : ↥V) ∈ U' := D.inv g u u.2
    refine ⟨⟨(ρ g) u, hmem⟩ * u⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have e1 : ((((⟨(ρ g) u, hmem⟩ * u⁻¹ : ↥U') : ↥V) : G)) = ⁅y, ((u : ↥V) : G)⁆ := by
        rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inv, hy]
      rw [e1, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hyY (u : ↥V).2
    · rw [map_mul, map_inv, D.equiv g u hmem, hu]
  have h1 : Nat.card A = Nat.card ↥(W.map D.β) := by
    rw [hK]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
  have h2 : Nat.card ↥(W.map D.β) ≤ Nat.card ↥W :=
    Nat.card_le_card_of_surjective (fun w : ↥W => (⟨D.β w, ⟨w, w.2, rfl⟩⟩ : ↥(W.map D.β)))
      fun ⟨_, ⟨w, hw, rfl⟩⟩ => ⟨⟨w, hw⟩, rfl⟩
  have h3 : Nat.card ↥W ≤ Nat.card ↥⁅V, Y⁆ := by
    refine Nat.card_le_card_of_injective
      (fun w : ↥W => (⟨(((w : ↥U') : ↥V) : G), w.2⟩ : ↥⁅V, Y⁆)) fun w w' hww => ?_
    have := congrArg Subtype.val hww
    exact Subtype.ext (Subtype.ext (Subtype.ext this))
  omega

theorem mem_of_fix {V : Subgroup G} [IsMulCommutative ↥V] {n : ℕ} {ρ : FLc.SLt n →* MulAut ↥V}
    {U' Z' : Subgroup ↥V}
    {A : Type} [CommGroup A] {act : FLc.SLt n → A → A} (D : FLc.VModel n ρ U' Z' A act)
    {P : Set (FLc.SLt n)} (hfix : ∀ b : A, (∀ g ∈ P, act g b = b) → b = 1) {u : ↥V}
    (hu : u ∈ U') (hfu : ∀ g ∈ P, ρ g u = u) : u ∈ Z' := by
  refine D.ker ⟨u, hu⟩ (hfix _ fun g hg => ?_)
  have hmem : (ρ g) u ∈ U' := D.inv g u hu
  rw [← D.equiv g ⟨u, hu⟩ hmem]
  congr 1
  exact Subtype.ext (hfu g hg)

theorem beta_fix {V : Subgroup G} [IsMulCommutative ↥V] {n : ℕ} {ρ : FLc.SLt n →* MulAut ↥V}
    {U' Z' : Subgroup ↥V}
    {A : Type} [CommGroup A] {act : FLc.SLt n → A → A} (D : FLc.VModel n ρ U' Z' A act)
    {P : Set (FLc.SLt n)} {u : ↥V} (hu : u ∈ U') (hfu : ∀ g ∈ P, ρ g u = u) :
    ∀ g ∈ P, act g (D.β ⟨u, hu⟩) = D.β ⟨u, hu⟩ := by
  intro g hg
  have hmem : (ρ g) u ∈ U' := D.inv g u hu
  rw [← D.equiv g ⟨u, hu⟩ hmem]
  congr 1
  exact Subtype.ext (hfu g hg)

variable [Finite G] {T M L D : Subgroup G}

theorem vPlus_eq_comm (h7 : Stmt3_3_7) (h14 : Stmt3_3_14) (he : Step3_3_21e)
    (h : Hyp331 G T M L D)
    (e : Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hmod : Mod3321 T L) : ⁅vPlus L T, L⁆ = vPlus L T := by
  obtain ⟨hML, -⟩ := h14 G T M L D h
  obtain ⟨-, -, -, -, hV⟩ := h7 G T M L D h
  rw [hML, he G T M L D h e hmod, sup_bot_eq] at hV
  exact hV.symm

theorem commV_eq_top (h7 : Stmt3_3_7) (h14 : Stmt3_3_14) (he : Step3_3_21e)
    (h : Hyp331 G T M L D)
    (e : Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321 T L) :
    commV (autOn L (vPlus L T)) = ⊤ := by
  rw [Ln2.commV_autOn_eq h]
  show (⁅vPlus L T, L⁆).subgroupOf (vPlus L T) = ⊤
  rw [vPlus_eq_comm h7 h14 he h e hmod]
  exact Subgroup.subgroupOf_self _

theorem exists_ne_one {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    (e : ↥H ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) {ρ₀ : FLc.SLt 4 →* MulAut V}
    (hrange : ∀ k ∈ H, ∃ g, ρ₀ g = k) : ∃ g, ρ₀ g ≠ 1 := by
  have : Finite ↥H := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card ↥H = 20160 := by
    rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 4 (Or.inl rfl)]
    rfl
  have : Nontrivial ↥H := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
  obtain ⟨k, hk⟩ := exists_ne (1 : ↥H)
  obtain ⟨g₀, hg₀⟩ := hrange k k.2
  exact ⟨g₀, by rw [hg₀]; exact fun h1 => hk (Subtype.ext h1)⟩

theorem kerV_of_rho (h : Hyp331 G T M L D) {α : ↥L →* SL4}
    {ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)} (hinj : Function.Injective ρ)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    (l : ↥L) : α l = 1 ↔ (l : G) ∈ Subgroup.centralizer (vPlus L T : Set G) := by
  constructor
  · intro hl
    have h1 := hαv l
    rw [hl, map_one] at h1
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    have h2 := congrArg (fun φ : MulAut ↥(vPlus L T) => ((φ ⟨v, hv⟩ : ↥(vPlus L T)) : G)) h1
    simp only [MulAut.one_apply, FLc.conjAct_coe] at h2
    calc v * l = (l * v * (l : G)⁻¹) * l := by rw [← h2]
      _ = l * v := by group
  · intro hl
    apply hinj
    rw [map_one, hαv l]
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [FLc.conjAct_coe, MulAut.one_apply,
      ← Subgroup.mem_centralizer_iff.1 hl v v.2, mul_inv_cancel_right]

theorem exists_fdata_sum (h14 : Stmt3_3_14) (hGA : GriessAllModelsStatement)
    (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Sum T L) (hin : InducesInnerOn T L) :
    ∃ (α : ↥L →* SL4) (ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)) (U₁ U₂ : Subgroup ↥(vPlus L T)),
      FData G T M L D α ∧
      (∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩) ∧
      IsIntDirect U₁ U₂ (commV (autOn L (vPlus L T))) ∧
      Nonempty (FLc.VModel 4 ρ U₁ ⊥ (Multiplicative (FLc.Vt 4)) (fun g a => FLc.actM g a)) ∧
      Nonempty (FLc.VModel 4 ρ U₂ ⊥ (Multiplicative (FLc.Vt 4)) FLc.actDl) := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨hVe, hLV, -, -, -, -, -⟩ := setting_facts h hTL
  obtain ⟨-, π, U₁, U₂, hdirect, hreal1, hreal2⟩ := hmod
  obtain ⟨D₁⟩ := FLc.vmodelNat hreal1
    (fun g _ z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  obtain ⟨D₂⟩ := FLc.vmodelDual hreal2
    (fun g _ z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  obtain ⟨h', hinj, hr1, hr2, hU⟩ := exists_normalized_eq hVe hLV (L3317.isSylowTwoOf_inf h hTL)
    (by norm_num) (FLc.rhoOf π) (FLc.rhoOf_surj hreal1.1) (FLc.rhoOf_mem π)
    (exists_ne_one e (FLc.rhoOf_surj hreal1.1))
  obtain ⟨α, hαs, hαk, hαU, hαv⟩ := exists_alpha_of_rho h hGA hTL e hinj hr1 hr2 hU
  exact ⟨α, _, U₁, U₂, ⟨h, hTL, hαs, hαk, kerV_of_rho h hinj hαv, hαU, hin⟩, hαv, hdirect,
    ⟨D₁.rtwist h'⟩, ⟨D₂.rtwist h'⟩⟩

theorem exists_fdata_ext (h14 : Stmt3_3_14) (hGA : GriessAllModelsStatement)
    (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Ext T L) (hin : InducesInnerOn T L) :
    ∃ (α : ↥L →* SL4) (ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)) (Z₀ : Subgroup ↥(vPlus L T)),
      FData G T M L D α ∧
      (∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩) ∧
      Z₀ ≤ fixV (autOn L (vPlus L T)) ⊓ commV (autOn L (vPlus L T)) ∧ Nat.card ↥Z₀ ≤ 2 ∧
      Nonempty (FLc.VModel 4 ρ (commV (autOn L (vPlus L T))) Z₀
        (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW) := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨hVe, hLV, -, -, -, -, -⟩ := setting_facts h hTL
  obtain ⟨Z₀, hZ₀, hZ₀2, π, hπ⟩ := hmod
  obtain ⟨D₀⟩ := FLc.vmodelExtSq hπ (fun g hg z hz => (hZ₀.trans inf_le_left) hz g hg)
  obtain ⟨h', hinj, hr1, hr2, hU⟩ := exists_normalized_eq hVe hLV (L3317.isSylowTwoOf_inf h hTL)
    (by norm_num) (FLc.rhoOf π) (FLc.rhoOf_surj hπ.1) (FLc.rhoOf_mem π)
    (exists_ne_one e (FLc.rhoOf_surj hπ.1))
  obtain ⟨α, hαs, hαk, hαU, hαv⟩ := exists_alpha_of_rho h hGA hTL e hinj hr1 hr2 hU
  exact ⟨α, _, Z₀, ⟨h, hTL, hαs, hαk, kerV_of_rho h hinj hαv, hαU, hin⟩, hαv, hZ₀, hZ₀2,
    ⟨D₀.rtwist h'⟩⟩

theorem exists_mem_Y (h : Hyp331 G T M L D) {α : ↥L →* SL4}
    {ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)} (hαs : Function.Surjective α)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {I : Set ℕ} {g : SL4} (hg : g ∈ perfectCore (FLc.QI 4 I)) :
    ∃ y ∈ L3316.liftCore α (FLc.QI 4 I), ∀ v : ↥(vPlus L T),
      ((ρ g v : ↥(vPlus L T)) : G) = y * v * y⁻¹ := by
  obtain ⟨y, hy, hye⟩ := L3318.exists_mem_liftCore hαs hg
  refine ⟨y, hy, fun v => ?_⟩
  rw [← hye, hαv, FLc.conjAct_coe]

end CFSG.Quasithin.H13.L3321
