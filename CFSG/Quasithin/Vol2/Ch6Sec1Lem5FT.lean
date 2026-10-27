module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FR
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FS
public import CFSG.Quasithin.EmptyFaithful.LRed5Models
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Conj

variable {Γ : Type*} [Group Γ] {F : Subgroup Γ} {k : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_conj_unitriangular_ch615 (hk : 1 ≤ k) {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (ψ : SpecialLinearGroup (Fin k) K ≃* ↥F) {S : Subgroup Γ} (hS : IsSylowTwoOf S F) :
    ∃ g : SpecialLinearGroup (Fin k) K,
      ∀ u ∈ unitriangular k K, ((ψ (g * u * g⁻¹) : ↥F) : Γ) ∈ S := by
  have hS' := isSylowTwoOf_map_ch615 ψ.symm hS
  obtain ⟨g, -, hg⟩ := (isSylowTwoOf_unitriangular_ch615 hK hk).exists_conj hS'
  refine ⟨g, fun u hu => ?_⟩
  have h1 : g * u * g⁻¹ ∈ (S.subgroupOf F).map ψ.symm.toMonoidHom := by
    rw [hg]
    exact ⟨u, hu, rfl⟩
  obtain ⟨s, hs, hse⟩ := h1
  have : ψ (g * u * g⁻¹) = s := by
    rw [← hse]
    simp
  rw [this]
  exact Subgroup.mem_subgroupOf.mp hs

end Conj

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem flag_cuts_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hFX : F ≤ autI hU (borelL T L ⊔ H))
    (hXF : autI hU (borelL T L ⊔ H) ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hdl : DLemmaFacts_ch615 F) (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1)
    (hKF : autI hU (oTwoUpper H) ≤ F) {k : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (ψ : SpecialLinearGroup (Fin k) K ≃* ↥F)
    (g : SpecialLinearGroup (Fin k) K)
    (hg : ∀ u ∈ unitriangular k K,
      ((ψ (g * u * g⁻¹) : ↥F) : MulAut (IntMod (UX615 T L H) hU)) ∈ autI hU T ⊓ F) :
    ∃ IK ID : Set ℕ, (∀ i, 1 ≤ i → i + 1 < k → i ∈ IK ∨ i + 1 ∈ IK) ∧
      (∀ i, 1 ≤ i → i + 1 < k → i ∈ ID ∨ i + 1 ∈ ID) ∧
      (∀ e, 1 ≤ e → e < k → ¬ (e ∈ IK ∧ e ∈ ID)) ∧
      (∀ x ∈ autI hU (oTwoUpper H), ∃ y ∈ flagStabilizer k K IK,
        ((ψ (g * y * g⁻¹) : ↥F) : MulAut (IntMod (UX615 T L H) hU)) = x) ∧
      (∀ y ∈ flagStabilizer k K ID,
        ((ψ (g * y * g⁻¹) : ↥F) : MulAut (IntMod (UX615 T L H) hU)) ∈
          autI hU (borelL T L ⊔ T)) ∧
      ∃ D : Subgroup G, Lin2.IsHallTwoPrimeOf D (borelL T L) ∧ ∃ d ∈ autI hU D, d ≠ 1 ∧
        ∃ y ∈ flagStabilizer k K ID,
          ((ψ (g * y * g⁻¹) : ↥F) : MulAut (IntMod (UX615 T L H) hU)) = d := by
  classical
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  obtain ⟨d, hdD, hd1, hdPD, hSD, hDS, hDs, hKF', hKS, hKs, -⟩ :=
    c.exists_overgroups_ch615 hU hN hD hFX hXF hdl hZ hKF
  have hgen := c.le_sup_overgroups_ch615 hU hFX hXF hdl hZ hKF
  set PK := autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F) with hPK
  set PD := autI hU (borelL T L ⊔ T) ⊓ F with hPD
  set φ : SpecialLinearGroup (Fin k) K ≃* ↥F := (MulAut.conj g).trans ψ with hφ
  have hφa : ∀ y, φ y = ψ (g * y * g⁻¹) := fun y => by
    simp [hφ, MulAut.conj_apply]
  have hU2 : upperTriangular k K ≤ unitriangular k K :=
    CFSG.QuasithinUnique.Vol2Native.A312L.upperTriangular_le_unitriangular hK
  have key : ∀ R : Subgroup (MulAut (IntMod (UX615 T L H) hU)), autI hU T ⊓ F ≤ R → R ≤ F →
      Group.IsSolvable ↥R →
      (R.subgroupOf F).map φ.symm.toMonoidHom =
        flagStabilizer k K (borelOvergroupCuts ((R.subgroupOf F).map φ.symm.toMonoidHom)) ∧
      Group.IsSolvable ↥((R.subgroupOf F).map φ.symm.toMonoidHom) := by
    intro R hSR hRF hRs
    have hUR : upperTriangular k K ≤ (R.subgroupOf F).map φ.symm.toMonoidHom := fun u hu => by
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf, hφa]
      exact hSR (hg u (hU2 hu))
    exact ⟨(borel_overgroups _ hUR).1, isSolvable_map_ch615 φ.symm hRF hRs⟩
  obtain ⟨hKe, hKsol⟩ := key PK le_sup_right hKF' hKs
  obtain ⟨hDe, hDsol⟩ := key PD hSD inf_le_right hDs
  set IK := borelOvergroupCuts ((PK.subgroupOf F).map φ.symm.toMonoidHom) with hIK
  set ID := borelOvergroupCuts ((PD.subgroupOf F).map φ.symm.toMonoidHom) with hID
  have htop : (PK.subgroupOf F).map φ.symm.toMonoidHom ⊔ (PD.subgroupOf F).map φ.symm.toMonoidHom =
      ⊤ := by
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hKF' inf_le_right,
      (Subgroup.subgroupOf_eq_top (H := PK ⊔ PD) (K := F)).mpr hgen,
      Subgroup.map_top_of_surjective _ φ.symm.surjective]
  have hsurj : ∀ R : Subgroup (MulAut (IntMod (UX615 T L H) hU)), R ≤ F → ∀ x ∈ R,
      ∃ y ∈ (R.subgroupOf F).map φ.symm.toMonoidHom, ((φ y : ↥F) : MulAut _) = x := by
    intro R hRF x hx
    refine ⟨φ.symm ⟨x, hRF hx⟩, ⟨⟨x, hRF hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, by simp⟩
  refine ⟨IK, ID, fun i hi hik => cut_or_cut_of_isSolvable_ch615 hK (hKe ▸ hKsol) hi hik,
    fun i hi hik => cut_or_cut_of_isSolvable_ch615 hK (hDe ▸ hDsol) hi hik,
    fun e he hek => not_cut_and_cut_of_sup_eq_top_ch615 (by rw [← hKe, ← hDe]; exact htop) he hek,
    fun x hx => ?_, fun y hy => ?_, D, hD, d, hdD, hd1, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hsurj PK hKF' x (Subgroup.mem_sup_left hx)
    exact ⟨y, hKe ▸ hy, by rw [hφa]⟩
  · rw [← hDe] at hy
    obtain ⟨⟨x, hxF⟩, hx, hxe⟩ := hy
    have hφx : φ y = ⟨x, hxF⟩ := by rw [← hxe]; simp
    rw [← hφa, hφx]
    exact (Subgroup.mem_subgroupOf.mp hx).1
  · obtain ⟨y, hy, hye⟩ := hsurj PD inf_le_right d hdPD
    exact ⟨y, hDe ▸ hy, by rw [← hφa]; exact hye⟩

theorem false_of_flag_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hFX : F ≤ autI hU (borelL T L ⊔ H))
    (hXF : autI hU (borelL T L ⊔ H) ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hdl : DLemmaFacts_ch615 F) (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1)
    (hKF : autI hU (oTwoUpper H) ≤ F) {k : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (ψ : SpecialLinearGroup (Fin k) K ≃* ↥F)
    (g : SpecialLinearGroup (Fin k) K)
    (hg : ∀ u ∈ unitriangular k K,
      ((ψ (g * u * g⁻¹) : ↥F) : MulAut (IntMod (UX615 T L H) hU)) ∈ autI hU T ⊓ F)
    (Fx : Subgroup (SpecialLinearGroup (Fin k) K) → Prop)
    (hFx : ∀ R : Subgroup (SpecialLinearGroup (Fin k) K), Fx R →
      ∀ w : IntMod (UX615 T L H) hU, (∀ s ∈ autI hU T ⊓ F, s w = w) →
        ∀ y ∈ R, ((ψ (g * y * g⁻¹) : ↥F) : MulAut (IntMod (UX615 T L H) hU)) w = w)
    (hcomb : ∀ I J : Set ℕ, (∀ i, 1 ≤ i → i + 1 < k → i ∈ I ∨ i + 1 ∈ I) →
      (∀ i, 1 ≤ i → i + 1 < k → i ∈ J ∨ i + 1 ∈ J) →
      (∀ d, 1 ≤ d → d < k → ¬ (d ∈ I ∧ d ∈ J)) →
        Fx (flagStabilizer k K I) ∨ Fx (flagStabilizer k K J)) : False := by
  obtain ⟨IK, ID, hcK, hcD, hdisj, hKy, -, D, hD, d, hdD, hd1, yd, hyd, hyde⟩ :=
    c.flag_cuts_ch615 hU hN hFX hXF hdl hZ hKF hK ψ g hg
  rcases hcomb IK ID hcK hcD hdisj with h | h
  · apply c.not_fix_oTwoUpper_ch615 hU
    intro w hw x hx
    obtain ⟨y, hy, rfl⟩ := hKy x hx
    exact hFx _ h w (fun s hs => hw s hs.1) y hy
  · apply c.not_fix_hall_ch615 hU hD hdD hd1
    intro w hw
    rw [← hyde]
    exact hFx _ h w (fun s hs => hw s hs.1) yd hyd

theorem false_of_flag_five_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hFX : F ≤ autI hU (borelL T L ⊔ H))
    (hXF : autI hU (borelL T L ⊔ H) ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hdl : DLemmaFacts_ch615 F) (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1)
    (hKF : autI hU (oTwoUpper H) ≤ F) (ψ : SpecialLinearGroup (Fin 5) (ZMod 2) ≃* ↥F)
    (g : SpecialLinearGroup (Fin 5) (ZMod 2))
    (hg : ∀ u ∈ unitriangular 5 (ZMod 2),
      ((ψ (g * u * g⁻¹) : ↥F) : MulAut (IntMod (UX615 T L H) hU)) ∈ autI hU T ⊓ F) :
    False := by
  obtain ⟨IK, ID, hcK, hcD, hdisj, -, hDy, -⟩ :=
    c.flag_cuts_ch615 hU hN hFX hXF hdl hZ hKF (Nat.card_zmod 2) ψ g hg
  have h9 : (1 ∉ ID ∧ 3 ∉ ID) ∨ (2 ∉ ID ∧ 4 ∉ ID) := by
    have c1 := hcK 1 le_rfl (by norm_num)
    have c2 := hcK 2 (by norm_num) (by norm_num)
    have c3 := hcK 3 (by norm_num) (by norm_num)
    have d1 := hcD 1 le_rfl (by norm_num)
    have d2 := hcD 2 (by norm_num) (by norm_num)
    have d3 := hcD 3 (by norm_num) (by norm_num)
    have e1 := hdisj 1 le_rfl (by norm_num)
    have e2 := hdisj 2 (by norm_num) (by norm_num)
    have e3 := hdisj 3 (by norm_num) (by norm_num)
    have e4 := hdisj 4 (by norm_num) (by norm_num)
    norm_num at c1 c2 c3 d1 d2 d3
    tauto
  obtain ⟨x, hx, y, hy, hx3, hy3, hxy, hx1, hyx⟩ := exists_e9_ch615 h9
  set θ : SpecialLinearGroup (Fin 5) (ZMod 2) →* MulAut (IntMod (UX615 T L H) hU) :=
    F.subtype.comp (ψ.toMonoidHom.comp (MulAut.conj g).toMonoidHom) with hθ
  have hθa : ∀ z, θ z = ((ψ (g * z * g⁻¹) : ↥F) : MulAut (IntMod (UX615 T L H) hU)) :=
    fun z => by simp [hθ, MulAut.conj_apply]
  have hθinj : Function.Injective θ :=
    Subtype.val_injective.comp (ψ.injective.comp (MulAut.conj g).injective)
  have hxB := c.mem_autI_borelL_of_odd_ch615 hU (hθa x ▸ hDy x hx) (by
    rw [orderOf_injective θ hθinj, orderOf_eq_prime hx3 hx1]
    decide)
  have hyB := c.mem_autI_borelL_of_odd_ch615 hU (hθa y ▸ hDy y hy) (by
    rw [orderOf_injective θ hθinj]
    by_cases hy1 : y = 1
    · rw [hy1, orderOf_one]; decide
    · rw [orderOf_eq_prime hy3 hy1]; decide)
  have hmem := c.mem_zpowers_of_autI_borelL_ch615 hU hxB hyB
    (by rw [← map_pow, hx3, map_one]) (by rw [← map_pow, hy3, map_one])
    (by rw [← map_mul, ← map_mul, hxy])
    (fun h1 => hx1 (hθinj (h1.trans (map_one θ).symm)))
  apply hyx
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨j, hθinj (by rw [map_zpow, hj])⟩

end Cx615C

section NatModule

variable {V : Type*} [CommGroup V] {k : ℕ} {K : Type} [Field K]

theorem conj_mulVec_ch615 (g z : SpecialLinearGroup (Fin k) K) (v : Fin k → K) :
    ((g * z * g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ v =
      (g : Matrix (Fin k) (Fin k) K) *ᵥ ((z : Matrix (Fin k) (Fin k) K) *ᵥ
        (((g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ v)) := by
  change ((g : Matrix (Fin k) (Fin k) K) * (z : Matrix (Fin k) (Fin k) K) *
    ((g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K)) *ᵥ v = _
  rw [← mulVec_mulVec, ← mulVec_mulVec]

theorem mulVec_inv_mulVec_ch615 (g : SpecialLinearGroup (Fin k) K) (v : Fin k → K) :
    (g : Matrix (Fin k) (Fin k) K) *ᵥ
        (((g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ v) = v ∧
      ((g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ
        ((g : Matrix (Fin k) (Fin k) K) *ᵥ v) = v := by
  have h1 : (g : Matrix (Fin k) (Fin k) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) = 1 :=
    congrArg Subtype.val (mul_inv_cancel g)
  have h2 : ((g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) *
      (g : Matrix (Fin k) (Fin k) K) = 1 :=
    congrArg Subtype.val (inv_mul_cancel g)
  exact ⟨by rw [mulVec_mulVec, h1, one_mulVec], by rw [mulVec_mulVec, h2, one_mulVec]⟩

theorem fix_of_natFix_ch615 {H : Subgroup (MulAut V)} {W : Subgroup V}
    {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL k K) →* ↥H}
    (h : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL k K)).RealizesVia H W ⊥ π)
    (g : SpecialLinearGroup (Fin k) K) {S : Subgroup (MulAut V)}
    (hS : ∀ u ∈ unitriangular k K,
      ((π (specialLinearGroupEquivStatedSL k K (g * u * g⁻¹)) : ↥H) : MulAut V) ∈ S)
    {R : Subgroup (SpecialLinearGroup (Fin k) K)}
    (hR : ∀ v : Fin k → K, (∀ u ∈ unitriangular k K, (u : Matrix (Fin k) (Fin k) K) *ᵥ v = v) →
      ∀ y ∈ R, (y : Matrix (Fin k) (Fin k) K) *ᵥ v = v)
    {w : V} (hwW : w ∈ W) (hw : ∀ s ∈ S, s w = w) :
    ∀ y ∈ R, ((π (specialLinearGroupEquivStatedSL k K (g * y * g⁻¹)) : ↥H) : MulAut V) w = w := by
  set ε := specialLinearGroupEquivStatedSL k K with hε
  set f : SpecialLinearGroup (Fin k) K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL k K) :=
    ε.toMonoidHom.comp (MulAut.conj g).toMonoidHom with hf
  have hfa : ∀ z, f z = ε (g * z * g⁻¹) := fun z => by simp [hf, MulAut.conj_apply]
  have key := fix_of_realizesVia_ch615 h (S' := (unitriangular k K).map f)
    (R' := R.map f) ?_ hwW ?_
  · intro y hy
    exact (congrArg (fun γ => ((π γ : ↥H) : MulAut V) w) (hfa y)).symm.trans
      (key _ ⟨y, hy, rfl⟩)
  · intro m _ hm γ hγ
    obtain ⟨y, hy, rfl⟩ := hγ
    obtain ⟨v, rfl⟩ : ∃ v : Fin k → K,
        (Multiplicative.ofAdd v : Multiplicative (Fin k → K)) = m := ⟨Multiplicative.toAdd m, rfl⟩
    have hact : ∀ z : SpecialLinearGroup (Fin k) K,
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL k K)).act (f z)
            (Multiplicative.ofAdd v) =
          Multiplicative.ofAdd (((g * z * g⁻¹ : SpecialLinearGroup (Fin k) K) :
            Matrix (Fin k) (Fin k) K) *ᵥ v) := fun z => by
      rw [hfa]
      rfl
    have hU : ∀ u ∈ unitriangular k K, (u : Matrix (Fin k) (Fin k) K) *ᵥ
        (((g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ v) =
          ((g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ v := by
      intro u hu
      have h1 := mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hm _ ⟨u, hu, rfl⟩))
      have h2 := Multiplicative.ofAdd.injective ((hact u).symm.trans h1)
      rw [conj_mulVec_ch615] at h2
      have h5 := congrArg (fun x => ((g⁻¹ : SpecialLinearGroup (Fin k) K) :
        Matrix (Fin k) (Fin k) K) *ᵥ x) h2
      simpa only [(mulVec_inv_mulVec_ch615 g _).2] using h5
    have h4 := hR _ hU y hy
    refine Subgroup.mem_bot.mpr (mul_inv_eq_one.mpr ((hact y).trans ?_))
    rw [conj_mulVec_ch615, h4, (mulVec_inv_mulVec_ch615 g _).1]
  · rintro _ ⟨u, hu, rfl⟩
    exact (congrArg (fun γ => ((π γ : ↥H) : MulAut V) w) (hfa u)).trans (hw _ (hS u hu))

end NatModule

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_case1_l52_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))))
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) : False := by
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    have := CFSG.Quasithin.B69.isSimpleGroup_statedSL_two h2 (by norm_num : 3 ≤ 5)
    exact e.isSimpleGroup
  have hdl := dLemmaFacts_of_smallAlt_ch615 hs
    (CFSG.Quasithin.InternalSec.exists_noncomm_of_isQuasisimple hq)
    (Or.inr ⟨5, ZMod 2, inferInstance, inferInstance, by norm_num, h2,
      ⟨e.trans ((CFSG.Quasithin.B69.statedSLEquivStatedProj h2 5).trans
        (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 5 (ZMod 2)))⟩⟩)
  have hZ := center_of_isSimpleGroup_ch615 hs hdl.1
  have hFX : quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) ≤ autI hU (borelL T L ⊔ H) :=
    (quasithinGenFitting_le _).trans (B6.ffJ_le _)
  have hKF := c.autI_oTwoUpper_le_genFitting_ch615 hU hdl.2.1
  set ψ := (specialLinearGroupEquivStatedSL 5 (ZMod 2)).trans e.symm with hψ
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_ch615 (by norm_num) (m := 1) (by rw [h2]; norm_num)
    ψ (c.isSylowTwoOf_genFitting_ch615 hU)
  exact c.false_of_flag_five_ch615 hU hN hFX (le_normalizer_genFitting_ch615 hU) hdl hZ hKF ψ g hg


theorem false_of_case1_l32_nofix_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H)))) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥) : False := by
  classical
  obtain ⟨e'⟩ := nonempty_l32_ch615 hK e
  have hdl := dLemmaFacts_l32_ch615 e'
  have hZ : ∀ g ∈ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))),
      (∀ x ∈ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))), g * x = x * g) → g = 1 :=
    fun _ hg h => eq_one_of_commute_l32_ch615 e' hg h
  have hFX : quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) ≤ autI hU (borelL T L ⊔ H) :=
    (quasithinGenFitting_le _).trans (B6.ffJ_le _)
  have hXF := le_normalizer_genFitting_ch615 hU
  have hKF := c.autI_oTwoUpper_le_genFitting_ch615 hU hdl.2.1
  have hS := c.isSylowTwoOf_genFitting_ch615 hU
  have h168 := card_l32_ch615 e'
  have htr : ∀ w : IntMod (UX615 T L H) hU,
      (∀ s ∈ autI hU T ⊓ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))), s w = w) →
      w ∈ commV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := fun w hw => by
    have := mem_commV_sup_fixV_ch615 IntMod.sq_eq_one hS.2.2 hw
    rwa [hfix, sup_bot_eq] at this
  have h2 : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  have hcomb : ∀ I J : Set ℕ, (∀ i, 1 ≤ i → i + 1 < 3 → i ∈ I ∨ i + 1 ∈ I) →
      (∀ i, 1 ≤ i → i + 1 < 3 → i ∈ J ∨ i + 1 ∈ J) →
      (∀ d, 1 ≤ d → d < 3 → ¬ (d ∈ I ∧ d ∈ J)) → 1 ∈ I ∨ 1 ∈ J := by
    intro I J hI hJ hd
    have a := hI 1 le_rfl (by norm_num)
    have b := hJ 1 le_rfl (by norm_num)
    have e2 := hd 2 (by norm_num) (by norm_num)
    tauto
  have hNat : ∀ I : Set ℕ, 1 ∈ I → ∀ v : Fin 3 → ZMod 2,
      (∀ u ∈ unitriangular 3 (ZMod 2), (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v) →
      ∀ y ∈ flagStabilizer 3 (ZMod 2) I, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v :=
    fun I h v hv y hy => natFix_ch615 (Nat.card_zmod 2) h hv hy
  rcases LRed5.b51_cases (Or.inl h168) h1.2.1.1 with ⟨-, ⟨π, hπ⟩ | hsum⟩ | ⟨h360, -⟩
  ·
    rw [hfix, bot_inf_eq] at hπ
    have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
    set ψ := (specialLinearGroupEquivStatedSL 3 (ZMod 2)).trans
      (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩) with hψ
    obtain ⟨g, hg⟩ := exists_conj_unitriangular_ch615 (by norm_num) h2 ψ hS
    refine c.false_of_flag_ch615 hU hN hFX hXF hdl hZ hKF (Nat.card_zmod 2) ψ g hg
      (fun R => ∀ v : Fin 3 → ZMod 2,
        (∀ u ∈ unitriangular 3 (ZMod 2), (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v) →
          ∀ y ∈ R, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v)
      (fun R hR w hw y hy => fix_of_natFix_ch615 hπ g (fun u hu => hg u hu) hR (htr w hw) hw y hy)
      fun I J hI hJ hd => ?_
    rcases hcomb I J hI hJ hd with h | h
    · exact Or.inl (hNat I h)
    · exact Or.inr (hNat J h)
  ·
    obtain ⟨I, π, -, hind, hsup, hreal⟩ := hsum
    have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal 0)
    set ψ := (specialLinearGroupEquivStatedSL 3 (ZMod 2)).trans
      (MulEquiv.ofBijective π ⟨hinj, (hreal 0).1⟩) with hψ
    obtain ⟨g, hg⟩ := exists_conj_unitriangular_ch615 (by norm_num) h2 ψ hS
    refine c.false_of_flag_ch615 hU hN hFX hXF hdl hZ hKF (Nat.card_zmod 2) ψ g hg
      (fun R => ∀ v : Fin 3 → ZMod 2,
        (∀ u ∈ unitriangular 3 (ZMod 2), (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v) →
          ∀ y ∈ R, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v)
      (fun R hR w hw y hy => ?_) fun I J hI hJ hd => ?_
    · have hw' : w ∈ ⨆ i, I i := by
        have := htr w hw
        rwa [← hsup, bot_sup_eq] at this
      set Rimg : Subgroup (MulAut (IntMod (UX615 T L H) hU)) :=
        (R.map ((MulAut.conj g).trans ψ).toMonoidHom).map
          (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))).subtype with hRimg
      have hyR : ((ψ (g * y * g⁻¹) : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))) :
          MulAut (IntMod (UX615 T L H) hU)) ∈ Rimg :=
        ⟨_, ⟨y, hy, rfl⟩, by simp [MulAut.conj_apply]⟩
      refine fix_of_iSup_ch615 (I := I) (fun i => by simpa using hind i) (S := autI hU T ⊓ _)
        (R := Rimg) (fun s hs i v hv => (hreal i).2.2.2.1 ⟨s, hs.2⟩ v hv)
        (fun i v hv hvS x hx => ?_) hw' hw _ hyR
      obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hx
      exact fix_of_natFix_ch615 (hreal i) g (fun u hu => hg u hu) hR hv hvS z hz
    · rcases hcomb I J hI hJ hd with h | h
      · exact Or.inl (hNat I h)
      · exact Or.inr (hNat J h)
  · omega

end Cx615C

end CFSG.Quasithin.H13
