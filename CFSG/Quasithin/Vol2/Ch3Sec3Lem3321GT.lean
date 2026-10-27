module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FC

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open scoped commutatorElement IsMulCommutative

namespace L3321

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem exists_coords_sum (h14 : Stmt3_3_14) (hGA : GriessAllModelsStatement)
    (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Sum T L) :
    ∃ (α : ↥L →* SL4) (ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)) (U₁ U₂ : Subgroup ↥(vPlus L T)),
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
      (∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Subgroup.centralizer (vPlus L T : Set G)) ∧
      ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4 ∧
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
  exact ⟨α, _, U₁, U₂, hαs, hαk, kerV_of_rho h hinj hαv, hαU, hαv, hdirect,
    ⟨D₁.rtwist h'⟩, ⟨D₂.rtwist h'⟩⟩

theorem gam_mem_QI3 {g : SL4} (hg : g ∈ FLc.QI 4 {1}) : gam g ∈ FLc.QI 4 {3} := by
  have hg' : g⁻¹ ∈ FLc.QI 4 {1} := Subgroup.inv_mem _ hg
  refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
  rw [Set.mem_singleton_iff] at hc
  subst hc
  rw [gam_apply_coe]
  refine stabilizer_entries (mem_flagStabilizer.1 hg' 1 (by simp)) ?_ ?_
  · rw [Fin.val_rev]
    have := k.isLt
    omega
  · rw [Fin.val_rev]
    omega

theorem gam_mem_QI1 {g : SL4} (hg : g ∈ FLc.QI 4 {3}) : gam g ∈ FLc.QI 4 {1} := by
  have hg' : g⁻¹ ∈ FLc.QI 4 {3} := Subgroup.inv_mem _ hg
  refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
  rw [Set.mem_singleton_iff] at hc
  subst hc
  rw [gam_apply_coe]
  refine stabilizer_entries (mem_flagStabilizer.1 hg' 3 (by simp)) ?_ ?_
  · rw [Fin.val_rev]
    omega
  · rw [Fin.val_rev]
    have := l.isLt
    omega

section Conj

variable {α : ↥L →* SL4} {t₀ : G} {u₀ : SL4}

omit [Finite G] in
theorem conj_liftPre_one (ht₀ : t₀ ∈ Subgroup.normalizer (L : Set G)) (hu₀ : u₀ ∈ FLc.Ut 4)
    (hact : ∀ (x : ↥L) (hx : t₀ * (x : G) * t₀⁻¹ ∈ L),
      α ⟨t₀ * x * t₀⁻¹, hx⟩ = u₀ * gam (α x) * u₀⁻¹) :
    (liftPre α (FLc.QI 4 {1})).map (MulAut.conj t₀).toMonoidHom ≤ liftPre α (FLc.QI 4 {3}) := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hxL : t₀ * (x : G) * t₀⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ht₀ x).mp x.2
  refine ⟨⟨t₀ * x * t₀⁻¹, hxL⟩, ?_, rfl⟩
  show α ⟨t₀ * x * t₀⁻¹, hxL⟩ ∈ FLc.QI 4 {3}
  have hu₀' : u₀ ∈ FLc.QI 4 {3} := FLc.Ut_le_QI 4 {3} hu₀
  rw [hact x hxL]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu₀' (gam_mem_QI3 hx)) (Subgroup.inv_mem _ hu₀')

omit [Finite G] in
theorem conj_liftPre_three (ht₀ : t₀ ∈ Subgroup.normalizer (L : Set G)) (hu₀ : u₀ ∈ FLc.Ut 4)
    (hact : ∀ (x : ↥L) (hx : t₀ * (x : G) * t₀⁻¹ ∈ L),
      α ⟨t₀ * x * t₀⁻¹, hx⟩ = u₀ * gam (α x) * u₀⁻¹) :
    (liftPre α (FLc.QI 4 {3})).map (MulAut.conj t₀⁻¹).toMonoidHom ≤ liftPre α (FLc.QI 4 {1}) := by
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  have hxL : t₀⁻¹ * (l : G) * t₀⁻¹⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht₀) l).mp l.2
  let x : ↥L := ⟨t₀⁻¹ * l * t₀⁻¹⁻¹, hxL⟩
  have hlx : t₀ * (x : G) * t₀⁻¹ ∈ L := by
    show t₀ * (t₀⁻¹ * (l : G) * t₀⁻¹⁻¹) * t₀⁻¹ ∈ L
    have e : t₀ * (t₀⁻¹ * (l : G) * t₀⁻¹⁻¹) * t₀⁻¹ = l := by group
    rw [e]
    exact l.2
  have h1 : α l = u₀ * gam (α x) * u₀⁻¹ := by
    rw [← hact x hlx]
    congr 1
    apply Subtype.ext
    show (l : G) = t₀ * (t₀⁻¹ * (l : G) * t₀⁻¹⁻¹) * t₀⁻¹
    group
  refine ⟨x, ?_, rfl⟩
  show α x ∈ FLc.QI 4 {1}
  have hu₀' : u₀ ∈ FLc.QI 4 {3} := FLc.Ut_le_QI 4 {3} hu₀
  have h2 : gam (α x) ∈ FLc.QI 4 {3} := by
    have : gam (α x) = u₀⁻¹ * α l * u₀ := by rw [h1]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu₀') hl) hu₀'
  have h3 := gam_mem_QI1 h2
  rwa [gam_gam] at h3

theorem conj_Y_one (ht₀ : t₀ ∈ Subgroup.normalizer (L : Set G)) (hu₀ : u₀ ∈ FLc.Ut 4)
    (hact : ∀ (x : ↥L) (hx : t₀ * (x : G) * t₀⁻¹ ∈ L),
      α ⟨t₀ * x * t₀⁻¹, hx⟩ = u₀ * gam (α x) * u₀⁻¹)
    {y : G} (hy : y ∈ liftCore α (FLc.QI 4 {1})) : t₀ * y * t₀⁻¹ ∈ liftCore α (FLc.QI 4 {3}) := by
  have h1 : (MulAut.conj t₀).toMonoidHom y ∈
      (liftCore α (FLc.QI 4 {1})).map (MulAut.conj t₀).toMonoidHom := ⟨y, hy, rfl⟩
  rw [L3316.liftCore, map_perfectCore] at h1
  exact perfectCore_mono (conj_liftPre_one ht₀ hu₀ hact) h1

theorem conj_Y_three (ht₀ : t₀ ∈ Subgroup.normalizer (L : Set G)) (hu₀ : u₀ ∈ FLc.Ut 4)
    (hact : ∀ (x : ↥L) (hx : t₀ * (x : G) * t₀⁻¹ ∈ L),
      α ⟨t₀ * x * t₀⁻¹, hx⟩ = u₀ * gam (α x) * u₀⁻¹)
    {y : G} (hy : y ∈ liftCore α (FLc.QI 4 {3})) : t₀⁻¹ * y * t₀ ∈ liftCore α (FLc.QI 4 {1}) := by
  have h1 : (MulAut.conj t₀⁻¹).toMonoidHom y ∈
      (liftCore α (FLc.QI 4 {3})).map (MulAut.conj t₀⁻¹).toMonoidHom := ⟨y, hy, rfl⟩
  rw [L3316.liftCore, map_perfectCore] at h1
  have h2 := perfectCore_mono (conj_liftPre_three ht₀ hu₀ hact) h1
  have h3 : t₀⁻¹ * y * t₀ ∈ perfectCore (liftPre α (FLc.QI 4 {1})) := by simpa using h2
  exact h3

end Conj

omit [Finite G] in
theorem normalizer_le_of_char {S C : Subgroup G} (hCS : C ≤ S)
    (hchar : (C.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) :=
  Hyp331.normalizer_le_normalizer_of_characteristic hCS hchar

theorem false_of_char (h5 : Stmt3_3_5) (h14 : Stmt3_3_14) (h : Hyp331 G T M L D)
    {S Y₁ Y₃ : Subgroup G} (hST : S ≤ T) (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hDS : D ≤ Subgroup.normalizer (S : Set G)) (hL : L ≤ Y₁ ⊔ Y₃ ⊔ T) {t₀ : G} (ht₀ : t₀ ∈ T)
    (h31 : ∀ y ∈ Y₃, t₀⁻¹ * y * t₀ ∈ Y₁) {C : Subgroup G} (hCS : C ≤ S) (hC1 : C ≠ ⊥)
    (hchar : (C.subgroupOf S).Characteristic) (hCN : Y₁ ⊔ S ≤ Subgroup.normalizer (C : Set G)) :
    False := by
  have hNS := normalizer_le_of_char hCS hchar
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := hTS.trans hNS
  have hY₁ : Y₁ ≤ Subgroup.normalizer (C : Set G) := le_sup_left.trans hCN
  have hY₃ : Y₃ ≤ Subgroup.normalizer (C : Set G) := by
    intro y hy
    have h1 := hY₁ (h31 y hy)
    have h2 := hTC ht₀
    have e : y = t₀ * (t₀⁻¹ * y * t₀) * t₀⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 h1) (Subgroup.inv_mem _ h2)
  have hN : L ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
    sup_le (hL.trans (sup_le (sup_le hY₁ hY₃) hTC)) hTC
  obtain ⟨hML, -⟩ := h14 G T M L D h
  have hU := (h5 G T M L h.toSetup331).2.1
  rw [hML] at hU
  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
    ⟨C, hC1, h.sylow.1.to_le (hCS.trans hST), rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq := hU.2 M' ⟨hM', hN.trans hle⟩
  exact Hyp331.not_D_le h ((hDS.trans hNS).trans (hM'eq ▸ hle))

end L3321

end CFSG.Quasithin.H13
