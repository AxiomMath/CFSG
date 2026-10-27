module

public import CFSG.Milestones.ASVolI.F437.Gen
public import CFSG.Milestones.ASVolI.F48.Core

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

section Quot

variable {E : Type} [Group E]

@[expose] def burnsideF437_c (fb : E) : ↥(f437Ebar fb) :=
  ⟨fb, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem burnsideF437_c_central (fb : E) :
    Subgroup.zpowers (burnsideF437_c fb) ≤ Subgroup.center ↥(f437Ebar fb) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_singleton_iff.mp x.2)

theorem burnsideF437_c_normal (fb : E) : (Subgroup.zpowers (burnsideF437_c fb)).Normal :=
  ⟨fun n hn g => by
    have := burnsideF437_c_central fb hn
    rw [Subgroup.mem_center_iff] at this
    rw [this g, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩

theorem burnsideF437_zpow_eq {fb : E} (hsq : fb * fb = 1) (k : ℤ) : fb ^ k = 1 ∨ fb ^ k = fb := by
  have h2 : fb ^ (2 : ℤ) = 1 := by rw [zpow_two, hsq]
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [hk, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem burnsideF437_mem_zpowers_c {fb : E} (hsq : fb * fb = 1) {x : ↥(f437Ebar fb)}
    (hx : x ∈ Subgroup.zpowers (burnsideF437_c fb)) : (x : E) = 1 ∨ (x : E) = fb := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have : ((burnsideF437_c fb ^ k : ↥(f437Ebar fb)) : E) = fb ^ k := by
    rw [Subgroup.coe_zpow]; rfl
  rw [this]
  exact burnsideF437_zpow_eq hsq k

theorem burnsideF437_eq_one_of_mem {Gp : Subgroup E} {fb : E} (hsq : fb * fb = 1) (hfG : fb ∉ Gp)
    {x : ↥(f437Ebar fb)} (hx : x ∈ Subgroup.zpowers (burnsideF437_c fb)) (hxG : (x : E) ∈ Gp) :
    x = 1 := by
  rcases burnsideF437_mem_zpowers_c hsq hx with h | h
  · exact Subtype.ext h
  · exact absurd (h ▸ hxG) hfG

end Quot

section QuotMaps

variable {E : Type} [Group E] {fb : E}

attribute [local instance] burnsideF437_c_normal

@[expose] noncomputable def burnsideF437_q (fb : E) :
    ↥(f437Ebar fb) →* ↥(f437Ebar fb) ⧸ Subgroup.zpowers (burnsideF437_c fb) :=
  QuotientGroup.mk' (Subgroup.zpowers (burnsideF437_c fb))

theorem burnsideF437_q_surjective (fb : E) : Function.Surjective (burnsideF437_q fb) :=
  QuotientGroup.mk'_surjective _

theorem burnsideF437_q_ker (fb : E) :
    (burnsideF437_q fb).ker = Subgroup.zpowers (burnsideF437_c fb) :=
  QuotientGroup.ker_mk' _

theorem burnsideF437_inf_subgroupOf (A B : Subgroup E) :
    (A ⊓ B).subgroupOf (f437Ebar fb) = A.subgroupOf (f437Ebar fb) ⊓ B.subgroupOf (f437Ebar fb) := by
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem burnsideF437_map_inf {A B : Subgroup E} (hB : fb ∈ B) :
    ((A ⊓ B).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) =
      (A.subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) ⊓
        (B.subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) := by
  rw [burnsideF437_inf_subgroupOf, inf_comm (A.subgroupOf _), inf_comm ((A.subgroupOf _).map _)]
  refine burnsideF4h_cl_map_inf_of_ker_le _ ?_
  rw [burnsideF437_q_ker, Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
  exact hB

@[expose] noncomputable def burnsideF437_psi (Gp : Subgroup E) (fb : E) :
    ↥(f437Dbar Gp fb) →* ↥(f437Ebar fb) ⧸ Subgroup.zpowers (burnsideF437_c fb) :=
  (burnsideF437_q fb).comp (Subgroup.inclusion (inf_le_right : Gp ⊓ f437Ebar fb ≤ f437Ebar fb))

theorem burnsideF437_psi_injective {Gp : Subgroup E} (hsq : fb * fb = 1) (hfG : fb ∉ Gp) :
    Function.Injective (burnsideF437_psi Gp fb) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  have hk : Subgroup.inclusion (inf_le_right : Gp ⊓ f437Ebar fb ≤ f437Ebar fb) d ∈
      (burnsideF437_q fb).ker := hd
  rw [burnsideF437_q_ker] at hk
  have := burnsideF437_eq_one_of_mem hsq hfG hk d.2.1
  have h' : ((Subgroup.inclusion (inf_le_right : Gp ⊓ f437Ebar fb ≤ f437Ebar fb) d :
      ↥(f437Ebar fb)) : E) = 1 := congrArg Subtype.val this
  exact Subtype.ext h'

theorem burnsideF437_psi_range (Gp : Subgroup E) (fb : E) :
    (burnsideF437_psi Gp fb).range =
      ((f437Dbar Gp fb).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) := by
  ext y
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨_, d.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨(x : E), hx⟩, rfl⟩

theorem burnsideF437_psi_map {Gp X : Subgroup E} (hX : X ≤ f437Dbar Gp fb) :
    (X.subgroupOf (f437Dbar Gp fb)).map (burnsideF437_psi Gp fb) =
      (X.subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) := by
  rw [burnsideF437_psi, ← Subgroup.map_map]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨⟨(y : E), hX hy⟩, hy, rfl⟩

theorem burnsideF437_mem_normalizer_of_map {Gp : Subgroup E} [Gp.Normal] (hsq : fb * fb = 1)
    (hfG : fb ∉ Gp) {X : Subgroup E} (hXG : X ≤ Gp) (hXE : X ≤ f437Ebar fb) (e : ↥(f437Ebar fb))
    (he : burnsideF437_q fb e ∈ Subgroup.normalizer
      (((X.subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) : Subgroup _) : Set _)) :
    (e : E) ∈ Subgroup.normalizer (X : Set E) := by
  have key : ∀ g : ↥(f437Ebar fb), burnsideF437_q fb g ∈ Subgroup.normalizer
      (((X.subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) : Subgroup _) : Set _) →
      ∀ y ∈ X, (g : E) * y * (g : E)⁻¹ ∈ X := by
    intro g hg y hy
    have hyE : y ∈ f437Ebar fb := hXE hy
    have h1 := (Subgroup.mem_normalizer_iff.mp hg (burnsideF437_q fb ⟨y, hyE⟩)).mp
      ⟨⟨y, hyE⟩, hy, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    obtain ⟨x', hx', hxe⟩ := h1
    have hk : x'⁻¹ * (g * ⟨y, hyE⟩ * g⁻¹) ∈ Subgroup.zpowers (burnsideF437_c fb) := by
      rw [← burnsideF437_q_ker, MonoidHom.mem_ker, map_mul, map_inv, hxe, inv_mul_cancel]
    have hkG : ((x'⁻¹ * (g * ⟨y, hyE⟩ * g⁻¹) : ↥(f437Ebar fb)) : E) ∈ Gp := by
      have h2 : ((g : E) * y * (g : E)⁻¹) ∈ Gp :=
        Subgroup.Normal.conj_mem inferInstance y (hXG hy) g
      have h3 : ((x' : E))⁻¹ ∈ Gp := Gp.inv_mem (hXG hx')
      simpa [mul_assoc] using Gp.mul_mem h3 h2
    have h4 := burnsideF437_eq_one_of_mem hsq hfG hk hkG
    have h5 : g * ⟨y, hyE⟩ * g⁻¹ = x' := by
      have := congrArg (x' * ·) h4
      simpa [mul_assoc] using this
    have h6 := congrArg Subtype.val h5
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h6
    rw [h6]
    exact hx'
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key e he y
  · intro hy
    have hinv : burnsideF437_q fb e⁻¹ ∈ Subgroup.normalizer
        (((X.subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) : Subgroup _) : Set _) := by
      rw [map_inv]; exact Subgroup.inv_mem _ he
    have := key e⁻¹ hinv _ hy
    simpa [mul_assoc] using this

theorem burnsideF437_map_mem_normalizer {X : Subgroup E} (e : ↥(f437Ebar fb))
    (he : (e : E) ∈ Subgroup.normalizer (X : Set E)) :
    burnsideF437_q fb e ∈ Subgroup.normalizer
      (((X.subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) : Subgroup _) : Set _) := by
  refine Subgroup.le_normalizer_map (burnsideF437_q fb) ⟨e, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  rw [Subgroup.mem_normalizer_iff] at he
  intro y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using he (y : E)

end QuotMaps

section Assembly

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {fb : E}

attribute [local instance] burnsideF437_c_normal

theorem burnsideF437_Dbar_inf_one :
    f437Dbar Gp fb ⊓ f437EbarOne M₁ fb = f437DbarOne Gp M₁ fb := by
  ext x
  simp only [f437Dbar, f437EbarOne, f437DbarOne, cenIn, Subgroup.mem_inf]
  tauto

theorem burnsideF437_Dbar_inf_two :
    f437Dbar Gp fb ⊓ f437EbarTwo M₂ fb = f437DbarTwo Gp M₂ fb := by
  ext x
  simp only [f437Dbar, f437EbarTwo, f437DbarTwo, cenIn, Subgroup.mem_inf]
  tauto

theorem burnsideF437_Dbar_inf_edge :
    f437Dbar Gp fb ⊓ cenIn (M₁ ⊓ M₂) fb = cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb := by
  ext x
  simp only [f437Dbar, cenIn, Subgroup.mem_inf]
  tauto

theorem burnsideF437_Ebar_inf :
    f437EbarOne M₁ fb ⊓ f437EbarTwo M₂ fb = cenIn (M₁ ⊓ M₂) fb := by
  ext x
  simp only [f437EbarOne, f437EbarTwo, cenIn, Subgroup.mem_inf]
  tauto

theorem burnsideF437_mem_cenIn {X : Subgroup E} (h : fb ∈ X) : fb ∈ cenIn X fb :=
  ⟨h, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem burnsideF437_isLieParabolics_image (hsq : fb * fb = 1) (hfG : fb ∉ Gp)
    (hP : IsLieParabolics 2 (f437Dbar Gp fb) (cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb)
      (f437DbarOne Gp M₁ fb) (f437DbarTwo Gp M₂ fb)) :
    IsLieParabolics 2 (((f437Dbar Gp fb).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb))
      (((cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb))
      (((f437DbarOne Gp M₁ fb).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb))
      (((f437DbarTwo Gp M₂ fb).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb)) := by
  have h12 : cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb ≤ f437Dbar Gp fb := inf_le_inf_right _ inf_le_left
  have h1 : f437DbarOne Gp M₁ fb ≤ f437Dbar Gp fb := inf_le_inf_right _ inf_le_left
  have h2 : f437DbarTwo Gp M₂ fb ≤ f437Dbar Gp fb := inf_le_inf_right _ inf_le_left
  have hD : IsLieParabolics 2 (⊤ : Subgroup ↥(f437Dbar Gp fb))
      ((cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb).subgroupOf (f437Dbar Gp fb))
      ((f437DbarOne Gp M₁ fb).subgroupOf (f437Dbar Gp fb))
      ((f437DbarTwo Gp M₂ fb).subgroupOf (f437Dbar Gp fb)) := by
    refine burnsideF48_isLieParabolics_of_map (f437Dbar Gp fb).subtype
      (f437Dbar Gp fb).subtype_injective ?_
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.map_subgroupOf_eq_of_le h12,
      Subgroup.map_subgroupOf_eq_of_le h1, Subgroup.map_subgroupOf_eq_of_le h2]
    exact hP
  have hmap := burnsideF48_isLieParabolics_map (burnsideF437_psi Gp fb)
    (burnsideF437_psi_injective hsq hfG) hD
  rw [← MonoidHom.range_eq_map, burnsideF437_psi_range, burnsideF437_psi_map h12,
    burnsideF437_psi_map h1, burnsideF437_psi_map h2] at hmap
  exact hmap

theorem burnsideF437_quotientAssembly [Gp.Normal] (hfbM : fb ∈ M₁ ⊓ M₂) (hfG : fb ∉ Gp)
    (hf1 : fb ≠ 1) (hsq : fb * fb = 1) {kind : GLKind} {degree : ℕ}
    (hlie : IsGenLie (f437Dbar Gp fb) kind 2 degree)
    (hP : IsLieParabolics 2 (f437Dbar Gp fb) (cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb)
      (f437DbarOne Gp M₁ fb) (f437DbarTwo Gp M₂ fb))
    (hrig : Subgroup.centralizer ((cenIn Gp fb : Subgroup E) : Set E) ⊓
      Subgroup.centralizer ({fb} : Set E) ≤ Subgroup.zpowers fb)
    (hfrat : ∀ e ∈ Subgroup.centralizer ({fb} : Set E), ∃ d ∈ cenIn Gp fb,
      ∃ h ∈ Subgroup.centralizer ({fb} : Set E) ⊓ (M₁ ⊓ M₂), e = d * h)
    (hdyn : ∀ e ∈ Subgroup.centralizer ({fb} : Set E),
      e ∈ Subgroup.normalizer ((cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb : Subgroup E) : Set E) →
      e ∈ Subgroup.normalizer ((f437DbarOne Gp M₁ fb : Subgroup E) : Set E)) :
    F437QuotientAssembly Gp M₁ M₂ fb kind degree := by
  set L1 := ((f437EbarOne M₁ fb).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) with hL1
  set L2 := ((f437EbarTwo M₂ fb).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) with hL2
  set L12 := ((cenIn (M₁ ⊓ M₂) fb).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) with hL12
  set N0 := ((f437Dbar Gp fb).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) with hN0
  have hfE1 : fb ∈ f437EbarOne M₁ fb := burnsideF437_mem_cenIn hfbM.1
  have hfE2 : fb ∈ f437EbarTwo M₂ fb := burnsideF437_mem_cenIn hfbM.2
  have hfE12 : fb ∈ cenIn (M₁ ⊓ M₂) fb := burnsideF437_mem_cenIn hfbM
  have hD1 : N0 ⊓ L1 = ((f437DbarOne Gp M₁ fb).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) := by
    rw [← burnsideF437_Dbar_inf_one, burnsideF437_map_inf hfE1]
  have hD2 : N0 ⊓ L2 = ((f437DbarTwo Gp M₂ fb).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) := by
    rw [← burnsideF437_Dbar_inf_two, burnsideF437_map_inf hfE2]
  have hD12 : N0 ⊓ L12 = ((cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb).subgroupOf (f437Ebar fb)).map (burnsideF437_q fb) := by
    rw [← burnsideF437_Dbar_inf_edge, burnsideF437_map_inf hfE12]
  have hL : L1 ⊓ L2 = L12 := by
    rw [hL12, ← burnsideF437_Ebar_inf, burnsideF437_map_inf hfE2]
  have hEsup : f437Ebar fb ≤ f437EbarOne M₁ fb ⊔ f437EbarTwo M₂ fb := by
    intro e he
    obtain ⟨d, hd, h, hh, rfl⟩ := hfrat e he
    have hdD : d ∈ f437DbarOne Gp M₁ fb ⊔ f437DbarTwo Gp M₂ fb := by
      rw [burnsideF437_sup_eq hP]; exact hd
    have hle : f437DbarOne Gp M₁ fb ⊔ f437DbarTwo Gp M₂ fb ≤
        f437EbarOne M₁ fb ⊔ f437EbarTwo M₂ fb :=
      sup_le_sup (inf_le_inf_right _ inf_le_right) (inf_le_inf_right _ inf_le_right)
    refine Subgroup.mul_mem _ (hle hdD) (Subgroup.mem_sup_left ?_)
    exact ⟨hh.2.1, hh.1⟩
  have hle1 : f437EbarOne M₁ fb ≤ f437Ebar fb := inf_le_right
  have hle2 : f437EbarTwo M₂ fb ≤ f437Ebar fb := inf_le_right
  have hgen : L1 ⊔ L2 = ⊤ := by
    rw [hL1, hL2, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hle1 hle2,
      Subgroup.subgroupOf_eq_top.mpr hEsup]
    exact Subgroup.map_top_of_surjective _ (burnsideF437_q_surjective fb)
  have hfact : ∀ x : ↥(f437Ebar fb) ⧸ Subgroup.zpowers (burnsideF437_c fb),
      ∃ inner ∈ N0, ∃ edge ∈ L12, x = inner * edge := by
    intro x
    obtain ⟨e, rfl⟩ := burnsideF437_q_surjective fb x
    obtain ⟨d, hd, h, hh, he⟩ := hfrat e e.2
    refine ⟨(burnsideF437_q fb) ⟨d, hd.2⟩, ⟨⟨d, hd.2⟩, hd, rfl⟩, (burnsideF437_q fb) ⟨h, hh.1⟩, ⟨⟨h, hh.1⟩, ⟨hh.2, hh.1⟩, rfl⟩, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext he
  have hinj := burnsideF437_psi_injective (Gp := Gp) hsq hfG
  let marking : ↥(f437Dbar Gp fb) ≃* N0 :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (burnsideF437_psi_range Gp fb))
  have hmarking : ∀ element, (marking element : ↥(f437Ebar fb) ⧸ Subgroup.zpowers
      (burnsideF437_c fb)) = (burnsideF437_q fb) (Subgroup.inclusion
        (inf_le_right : Gp ⊓ f437Ebar fb ≤ f437Ebar fb) element) := fun _ => rfl
  have hpar : IsLieParabolics 2 N0 (N0 ⊓ L12) (N0 ⊓ L1) (N0 ⊓ L2) := by
    rw [hD12, hD1, hD2]
    exact burnsideF437_isLieParabolics_image hsq hfG hP
  have hdynE : ∀ x : ↥(f437Ebar fb) ⧸ Subgroup.zpowers (burnsideF437_c fb),
      x ∈ Subgroup.normalizer ((N0 ⊓ L12 : Subgroup _) : Set _) →
      x ∈ Subgroup.normalizer ((N0 ⊓ L1 : Subgroup _) : Set _) := by
    intro x hx
    rw [hD12] at hx
    rw [hD1]
    obtain ⟨e, rfl⟩ := burnsideF437_q_surjective fb x
    have h1 := burnsideF437_mem_normalizer_of_map hsq hfG
      ((inf_le_left : cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb ≤ Gp ⊓ (M₁ ⊓ M₂)).trans inf_le_left)
      inf_le_right e hx
    exact burnsideF437_map_mem_normalizer e (hdyn e e.2 h1)
  have hnormal : N0.Normal := by
    refine Subgroup.Normal.map ?_ (burnsideF437_q fb) (burnsideF437_q_surjective fb)
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := burnsideF437_conj_mem (Gp := Gp) (g : E) g.2 _ hn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact this
  have hcent : Subgroup.centralizer
      (N0 : Set (↥(f437Ebar fb) ⧸ Subgroup.zpowers (burnsideF437_c fb))) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨e, rfl⟩ := burnsideF437_q_surjective fb x
    have hcomm : ∀ d ∈ cenIn Gp fb, (e : E) * d = d * (e : E) := by
      intro d hd
      have h1 := (Subgroup.mem_centralizer_iff.mp hx) ((burnsideF437_q fb) ⟨d, hd.2⟩) ⟨⟨d, hd.2⟩, hd, rfl⟩
      have hk : (⟨d, hd.2⟩ * e * (⟨d, hd.2⟩ : ↥(f437Ebar fb))⁻¹ * e⁻¹) ∈
          Subgroup.zpowers (burnsideF437_c fb) := by
        rw [← burnsideF437_q_ker, MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [h1]
        group
      have hkG : (((⟨d, hd.2⟩ * e * (⟨d, hd.2⟩ : ↥(f437Ebar fb))⁻¹ * e⁻¹ :
          ↥(f437Ebar fb))) : E) ∈ Gp := by
        have h2 : (e : E) * d⁻¹ * (e : E)⁻¹ ∈ Gp :=
          Subgroup.Normal.conj_mem inferInstance _ (Gp.inv_mem hd.1) e
        have := Gp.mul_mem hd.1 h2
        simpa [mul_assoc] using this
      have h3 := congrArg Subtype.val (burnsideF437_eq_one_of_mem hsq hfG hk hkG)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h3
      have h4 : d * (e : E) * d⁻¹ = (e : E) := by
        have := congrArg (· * (e : E)) h3
        simpa [mul_assoc] using this
      calc (e : E) * d = d * (e : E) * d⁻¹ * d := by rw [h4]
        _ = d * (e : E) := by group
    have hmem : (e : E) ∈ Subgroup.centralizer ((cenIn Gp fb : Subgroup E) : Set E) ⊓
        Subgroup.centralizer ({fb} : Set E) := by
      refine Subgroup.mem_inf.mpr ⟨?_, e.2⟩
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (hcomm d hd).symm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hrig hmem)
    have he : e = burnsideF437_c fb ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk.symm
    rw [Subgroup.mem_bot, he, ← MonoidHom.mem_ker, burnsideF437_q_ker]
    exact Subgroup.zpow_mem_zpowers _ k
  have hext : IsLieExtBy (↥(f437Ebar fb) ⧸ Subgroup.zpowers (burnsideF437_c fb)) N0 kind 2 degree :=
    ⟨burnsideF4j_isGenLie_congr marking hlie, hnormal, hcent, N0 ⊓ L12, N0 ⊓ L1, N0 ⊓ L2,
      hpar, hdynE⟩
  let cpl : (RankTwoAmalgam.ofSubgroups L1 L2).Completion
      (↥(f437Ebar fb) ⧸ Subgroup.zpowers (burnsideF437_c fb)) :=
    { φ1 := L1.subtype
      φ12 := (L1 ⊓ L2).subtype
      φ2 := L2.subtype
      comm1 := fun _ => rfl
      comm2 := fun _ => rfl
      inter := by
        show L1.subtype.range ⊓ L2.subtype.range = (L1 ⊓ L2).subtype.range
        rw [Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.range_subtype]
      gen := by
        show L1.subtype.range ⊔ L2.subtype.range = ⊤
        rw [Subgroup.range_subtype, Subgroup.range_subtype, hgen] }
  have hcpl : cpl.IsFaithful :=
    ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, Subgroup.subtype_injective _⟩
  refine ⟨burnsideF437_c fb, rfl, fun h => hf1 (congrArg Subtype.val h), Subtype.ext hsq,
    burnsideF437_c_central fb, burnsideF437_c_normal fb, ?_⟩
  exact ⟨hlie, ⟨marking, hmarking⟩, hinj, hext, hgen, hfact, hL, hD1, hD2, hD12, hpar, hdynE,
    cpl, hcpl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

end Assembly

end CFSG.ASVolI
