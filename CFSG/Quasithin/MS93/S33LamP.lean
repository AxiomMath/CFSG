module

public import CFSG.Quasithin.MS93.S33LamM
public import CFSG.Quasithin.MS93.S33Main

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem relIndex_centralizer_Z0q_le (h : PUHyp M T L) {t : G} (ht : t ∈ T) :
    (Subgroup.centralizer ({t} : Set G)).relIndex (Z0q M T) ≤
      (Subgroup.centralizer ({t} : Set G)).relIndex (Uq M T L) := by
  refine relIndex_le_of_mul (Uq_le_Z0q h.L_le) fun z hz => ?_
  have hcomm := isMulCommutative_subgroup_iff.mp h.isElemAbelian_Z0q.1
  rw [h.Z0q_eq_sup, sup_comm] at hz
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_mul_of_mem_sup (U := Uq M T L) (W := omegaOneCenterOf T)
    (fun u hu w hw => hcomm u (Uq_le_Z0q h.L_le hu) w (omegaOneCenterOf_le_Z0q M T h.le hw)) hz
  refine ⟨u, hu, w, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp ((PU.omegaOneCenterOf_le_centerOf T hw).2) t ht).symm

variable {F : Type} [Field F] [Fintype F] {A : Subgroup G} {α : ↥A →* ↥(StatedSp 2 F)}
  {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → MSP.V4 F)}
  (h : PUHyp M T L) (hAM : A ≤ M) (hβ : Function.Surjective β)
  (hβker : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L))
  (hAβ : ∀ a : ↥A, IsCoordAct β a (MSP.mat (α a)).mulVec)
  (hlift : ∀ m ∈ M, ∀ u ∈ Uq M T L,
    m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) → m * u * m⁻¹ = u)
include h hAM hβ hβker hAβ hlift

omit [Fintype F] in
theorem relIndex_centralizer_Uq_le_two (hq : Nat.card F = 2) {t : ↥A} {x : MSP.V4 F}
    (hx : x ≠ 0) (htx : α t = MSP.transv x 1) :
    (Subgroup.centralizer ({(t : G)} : Set G)).relIndex (Uq M T L) ≤ 2 := by
  set c := natCoordOf β hβ hβker hAβ with hc
  let f : ↥(Uq M T L) →* Multiplicative F :=
    { toFun := fun u => Multiplicative.ofAdd (MSP.form F x (c.vec u))
      map_one' := by
        show Multiplicative.ofAdd (MSP.form F x (c.vec 1)) = 1
        rw [show c.vec 1 = 0 by simp [MSP.NatCoord.vec], map_zero, ofAdd_zero]
      map_mul' := fun u v => by
        show Multiplicative.ofAdd (MSP.form F x (c.vec (u * v))) = _
        rw [c.vec_mul, map_add, ofAdd_add] }
  have hker : f.ker ≤ (Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf (Uq M T L) := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have h0 : MSP.form F x (c.vec u) = 0 := by
      have := congrArg Multiplicative.toAdd hu
      simpa [f] using this
    have htV : (t : G) * u * (t : G)⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_Uq h.le_normalizer (hAM t.2)) u).1 u.2
    have hv : c.vec ⟨(t : G) * u * (t : G)⁻¹ * (u : G)⁻¹, mul_mem htV (inv_mem u.2)⟩ = 0 := by
      rw [c.vec_commutator t u htV, htx, MSP.transv_mulVec, h0, mul_zero, zero_smul, add_zero,
        sub_self]
    have hC := (c.vec_eq_zero_iff _).1 hv
    rw [h.Uq_inf_Zq] at hC
    have hfix := hlift t (hAM t.2) u u.2 hC.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    calc (u : G) * t = (t : G) * u * (t : G)⁻¹ * t := by rw [hfix]
      _ = t * u := by group
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨w, hw⟩ := MSP.exists_form_eq_one hx
    obtain ⟨u, hu⟩ := c.exists_vec_eq ((Multiplicative.toAdd y) • w)
    refine ⟨u, ?_⟩
    show Multiplicative.ofAdd (MSP.form F x (c.vec u)) = y
    rw [hu, map_smul, hw, smul_eq_mul, mul_one, ofAdd_toAdd]
  have hidx : f.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
    exact hq
  calc (Subgroup.centralizer ({(t : G)} : Set G)).relIndex (Uq M T L)
      = ((Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf (Uq M T L)).index := rfl
    _ ≤ f.ker.index := Nat.le_of_dvd (by rw [hidx]; norm_num) (Subgroup.index_dvd_of_le hker)
    _ = 2 := hidx

omit [Fintype F] in
theorem relIndex_centralizer_Z0q_eq_two (hq : Nat.card F = 2) {t : ↥A} (htT : (t : G) ∈ T)
    {x : MSP.V4 F} (hx : x ≠ 0) (htx : α t = MSP.transv x 1) :
    (Subgroup.centralizer ({(t : G)} : Set G)).relIndex (Z0q M T) = 2 := by
  have h1 := (relIndex_centralizer_Z0q_le h htT).trans
    (relIndex_centralizer_Uq_le_two h hAM hβ hβker hAβ hlift hq hx htx)
  have h2 : (Subgroup.centralizer ({(t : G)} : Set G)).relIndex (Z0q M T) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    have hU : (t : G) ∈ actTriv h := by
      refine (mem_actTriv h).2 ⟨hAM t.2, fun u hu => ?_⟩
      have hut := Subgroup.mem_centralizer_singleton_iff.1 (hle (Uq_le_Z0q h.L_le hu))
      rw [commutatorElement_def, hut, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    have h1' := (image_eq_one_iff h hAM (natCoordOf β hβ hβker hAβ) t).2 hU
    rw [htx] at h1'
    exact one_ne_zero (MSP.transv_injective hx (h1'.trans (MSP.transv_zero x).symm))
  have h3 : (Subgroup.centralizer ({(t : G)} : Set G)).relIndex (Z0q M T) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  omega

theorem lam_pair (hq : Nat.card F = 2) {E : Subgroup G} (hEA : E ≤ A) (hET : E ≤ T)
    {p p' : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p) (hp' : MSP.IsPoint p')
    (hpp : p' ≤ MSP.perp p) (hΓ : (E.subgroupOf A).map α = MSP.xPoint p ⊔ MSP.xPoint p')
    (h4 : 4 ≤ Nat.card ((E.subgroupOf A).map α)) :
    ∃ t₁ ∈ E, ∃ t₂ ∈ E, (Subgroup.centralizer ({t₁} : Set G)).relIndex (Z0q M T) = 2 ∧
      (Subgroup.centralizer ({t₂} : Set G)).relIndex (Z0q M T) = 2 ∧ t₁ * t₂⁻¹ ∉ pCoreOf 2 M ∧
      E ⊔ pCoreOf 2 M = Subgroup.closure ({t₁, t₂} : Set G) ⊔ pCoreOf 2 M := by
  have : CharP F 2 := by
    have hc : Fintype.card F = 2 ^ 1 := by rw [← Nat.card_eq_fintype_card, hq, pow_one]
    exact charP_of_card_eq_prime_pow hc
  obtain ⟨v, hv0, rfl⟩ := MSP.exists_eq_span_of_isPoint hp
  obtain ⟨v', hv'0, rfl⟩ := MSP.exists_eq_span_of_isPoint hp'
  have hvv : MSP.form F v v' = 0 := MSP.mem_perp_span.1 (hpp (Submodule.mem_span_singleton_self v'))
  have hind : v' ∉ F ∙ v := by
    intro hv'
    have hle : F ∙ v' ≤ F ∙ v := (Submodule.span_singleton_le_iff_mem _ _).2 hv'
    have heq : F ∙ v' = F ∙ v := Submodule.eq_of_le_of_finrank_eq hle (by rw [hp', hp])
    rw [hΓ, heq, sup_idem, MSP.card_xPoint hp, hq] at h4
    omega
  set c := natCoordOf β hβ hβker hAβ with hc
  have hkerT : ∀ a : ↥A, (a : G) ∈ T → α a = 1 → (a : G) ∈ pCoreOf 2 M := fun a haT ha =>
    mem_pCoreOf_of_actTriv h haT ((image_eq_one_iff h hAM c a).1 ha)
  have hQker : ∀ a : ↥A, (a : G) ∈ pCoreOf 2 M → α a = 1 := by
    intro a ha
    refine (image_eq_one_iff h hAM c a).2 ((mem_actTriv h).2 ⟨hAM a.2, fun u hu => ?_⟩)
    have hcu := Subgroup.mem_centralizer_iff.mp (h.pCoreOf_le_centralizer_Z0q ha) u
      (Uq_le_Z0q h.L_le hu)
    rw [commutatorElement_def, hcu, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hτ : ∀ w : MSP.V4 F, MSP.transv w 1 ∈ MSP.xPoint (F ∙ w) := fun w =>
    MSP.transv_mem_xPoint w 1
  obtain ⟨e₁, he₁, he₁v⟩ : MSP.transv v 1 ∈ (E.subgroupOf A).map α := by
    rw [hΓ]
    exact (le_sup_left : MSP.xPoint (F ∙ v) ≤ _) (hτ v)
  obtain ⟨e₂, he₂, he₂v⟩ : MSP.transv v' 1 ∈ (E.subgroupOf A).map α := by
    rw [hΓ]
    exact (le_sup_right : MSP.xPoint (F ∙ v') ≤ _) (hτ v')
  have he₁E : (e₁ : G) ∈ E := Subgroup.mem_subgroupOf.1 he₁
  have he₂E : (e₂ : G) ∈ E := Subgroup.mem_subgroupOf.1 he₂
  refine ⟨e₁, he₁E, e₂, he₂E,
    relIndex_centralizer_Z0q_eq_two h hAM hβ hβker hAβ hlift hq (hET he₁E) hv0 he₁v,
    relIndex_centralizer_Z0q_eq_two h hAM hβ hβker hAβ hlift hq (hET he₂E) hv'0 he₂v, ?_, ?_⟩
  · intro hmem
    have h1 := hQker (e₁ * e₂⁻¹) hmem
    rw [map_mul, map_inv, he₁v, he₂v, mul_inv_eq_one] at h1
    have hvv' : v' = v := (MSP.transv_eq_transv_iff hv0).1 h1.symm
    exact hind (by rw [hvv']; exact Submodule.mem_span_singleton_self v)
  · apply le_antisymm
    · refine sup_le (fun e he => ?_) le_sup_right
      have hmem : α ⟨e, hEA he⟩ ∈ MSP.xPoint (F ∙ v) ⊔ MSP.xPoint (F ∙ v') := by
        rw [← hΓ]
        exact ⟨⟨e, hEA he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
      obtain ⟨a, b, hab⟩ := exists_eq_of_mem_sup hv0 hv'0 hvv hmem
      have hpow : ∀ (w : MSP.V4 F) (z : F), ∃ n : ℕ, MSP.transv w z = MSP.transv w 1 ^ n := by
        intro w z
        rcases MSP.eq_zero_or_eq_one_of_card_two hq z with rfl | rfl
        · exact ⟨0, by rw [MSP.transv_zero, pow_zero]⟩
        · exact ⟨1, (pow_one _).symm⟩
      obtain ⟨n, hn⟩ := hpow v a
      obtain ⟨m, hm⟩ := hpow v' b
      have hwα : α (e₁ ^ n * e₂ ^ m) = α ⟨e, hEA he⟩ := by
        rw [map_mul, map_pow, map_pow, he₁v, he₂v, hab, hn, hm]
      have hwG : ((e₁ ^ n * e₂ ^ m : ↥A) : G) = (e₁ : G) ^ n * (e₂ : G) ^ m := by
        simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      have hwcl : (e₁ : G) ^ n * (e₂ : G) ^ m ∈
          Subgroup.closure ({(e₁ : G), (e₂ : G)} : Set G) :=
        mul_mem (pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) n)
          (pow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) m)
      have hwE : (e₁ : G) ^ n * (e₂ : G) ^ m ∈ E := mul_mem (pow_mem he₁E n) (pow_mem he₂E m)
      have hkα : α (⟨e, hEA he⟩ * (e₁ ^ n * e₂ ^ m)⁻¹) = 1 := by
        rw [map_mul, map_inv, hwα, mul_inv_cancel]
      have hkG : ((⟨e, hEA he⟩ * (e₁ ^ n * e₂ ^ m)⁻¹ : ↥A) : G) =
          e * ((e₁ : G) ^ n * (e₂ : G) ^ m)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hwG]
      have hkQ : e * ((e₁ : G) ^ n * (e₂ : G) ^ m)⁻¹ ∈ pCoreOf 2 M := by
        have hT' : ((⟨e, hEA he⟩ * (e₁ ^ n * e₂ ^ m)⁻¹ : ↥A) : G) ∈ T := by
          rw [hkG]
          exact hET (mul_mem he (inv_mem hwE))
        have := hkerT _ hT' hkα
        rwa [hkG] at this
      have e' : e = (e * ((e₁ : G) ^ n * (e₂ : G) ^ m)⁻¹) * ((e₁ : G) ^ n * (e₂ : G) ^ m) := by
        group
      rw [e']
      exact mul_mem (Subgroup.mem_sup_right hkQ) (Subgroup.mem_sup_left hwcl)
    · refine sup_le ((Subgroup.closure_le _).2 ?_) le_sup_right
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_sup_left he₁E
      · exact Subgroup.mem_sup_left he₂E

end CFSG.Quasithin.MS93.S33
