module

public import CFSG.Quasithin.Background.F918Z8Sz6Ba
public import CFSG.Quasithin.Background.D2Decomp
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.B5Sec
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Sec

variable {V : Type} [CommGroup V] [Finite V] {X A : Subgroup (MulAut V)} {W U : Subgroup V}

omit [Finite V] in
theorem suzb4_layer_eq_top {M : Type*} [Group M] (hM : CFSG.IsQuasisimple M) :
    CFSG.layer M = ⊤ :=
  CFSG.WholeGroup.layer_eq_top_of_isQuasisimple hM

omit [Finite V] in
theorem suzb4_isQuasisimple_autSec (hXW : X ≤ stabSub W) (hXU : X ≤ stabSub U)
    (hXq : CFSG.IsQuasisimple ↥X) (hnt : ∃ x ∈ X, ∃ w ∈ W, x w * w⁻¹ ∉ U) :
    CFSG.IsQuasisimple ↥(autSec X W U) := by
  have hq := B1Red.isQuasisimple_to_open hXq
  rw [← B5.range_secHom X hXW hXU]
  refine B1Red.isQuasisimple_of_open
    (CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hq _ ?_)
  intro htop
  obtain ⟨x, hx, w, hw, hxw⟩ := hnt
  have hmem : (⟨x, hx⟩ : ↥X) ∈ (B5.secHom X hXW hXU).ker := by rw [htop]; trivial
  exact hxw (((B5.mem_ker_secHom X hXW hXU _).1 hmem).2 w hw)

omit [Finite V] in
theorem suzb4_sup_conj (hAn : A ≤ Subgroup.normalizer (X : Set (MulAut V))) :
    ∀ x ∈ X ⊔ A, ∀ l ∈ X, x * l * x⁻¹ ∈ X := by
  intro x hx l hl
  obtain ⟨l', hl', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAn).1 hx
  have e : l' * a * l * (l' * a)⁻¹ = l' * (a * l * a⁻¹) * l'⁻¹ := by group
  rw [e]
  exact X.mul_mem (X.mul_mem hl' (B19Aux.conj_mem_of_le_normalizer hAn ha hl)) (X.inv_mem hl')

omit [Finite V] in
theorem suzb4_conj_mem (hAn : A ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hMW : X ⊔ A ≤ stabSub W) (hMU : X ⊔ A ≤ stabSub U) {y l : MulAut (Sec W U)}
    (hy : y ∈ autSec (X ⊔ A) W U) (hl : l ∈ autSec X W U) : y * l * y⁻¹ ∈ autSec X W U := by
  have hmapL := B5.map_secHom_eq_autSec (X ⊔ A) hMW hMU (le_sup_left : X ≤ X ⊔ A)
  rw [← B5.range_secHom (X ⊔ A) hMW hMU] at hy
  obtain ⟨m, rfl⟩ := hy
  rw [← hmapL] at hl ⊢
  obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.1 hl
  refine Subgroup.mem_map.2 ⟨m * l₀ * m⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  rw [Subgroup.mem_subgroupOf] at hl₀ ⊢
  exact suzb4_sup_conj hAn _ m.2 _ hl₀

omit [Finite V] in
theorem suzb4_sq_mem (hAn : A ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hMW : X ⊔ A ≤ stabSub W) (hMU : X ⊔ A ≤ stabSub U)
    {y : MulAut (Sec W U)} (hy : y ∈ autSec (X ⊔ A) W U) : y ^ 2 ∈ autSec X W U := by
  have hmapL := B5.map_secHom_eq_autSec (X ⊔ A) hMW hMU (le_sup_left : X ≤ X ⊔ A)
  rw [← B5.range_secHom (X ⊔ A) hMW hMU] at hy
  obtain ⟨m, rfl⟩ := hy
  rw [← hmapL]
  refine Subgroup.mem_map.2 ⟨m ^ 2, ?_, by simp only [map_pow]⟩
  rw [Subgroup.mem_subgroupOf]
  exact B1Red.sq_mem_of_mem_sup hAn hA2 (m : MulAut V) m.2

theorem suzb4_sqtk (hA21 : AsA21SQTKSection) {S' : Type} [Group S'] [Finite S']
    (hS : SQTKGroup S') {Γ : Subgroup (MulAut V)} (φ : S' →* ↥Γ) (hφ : Function.Surjective φ)
    (hXΓ : X ≤ Γ) (hAΓ : A ≤ Γ) (hq : CFSG.IsQuasisimple ↥(autSec X W U))
    (hAn : A ≤ Subgroup.normalizer (X : Set (MulAut V))) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hMW : X ⊔ A ≤ stabSub W) (hMU : X ⊔ A ≤ stabSub U) :
    SQTKGroup ↥(autSec (X ⊔ A) W U) := by
  have hMΓ : X ⊔ A ≤ Γ := sup_le hXΓ hAΓ
  set G := autSec (X ⊔ A) W U with hGdef
  have hmem : ∀ g : ↥(X ⊔ A), B5.secHom (X ⊔ A) hMW hMU g ∈ G := fun g => by
    rw [hGdef, ← B5.range_secHom (X ⊔ A) hMW hMU]; exact ⟨g, rfl⟩
  let ψ : ↥(X ⊔ A) →* ↥G := (B5.secHom (X ⊔ A) hMW hMU).codRestrict G hmem
  have hψ : Function.Surjective ψ := by
    intro y
    have hy : (y : MulAut (Sec W U)) ∈ (B5.secHom (X ⊔ A) hMW hMU).range := by
      rw [B5.range_secHom]; exact y.2
    obtain ⟨g, hg⟩ := hy
    exact ⟨g, Subtype.ext hg⟩
  let H : Subgroup S' := ((X ⊔ A).subgroupOf Γ).comap φ
  let τ : ↥H →* ↥(X ⊔ A) :=
    (Subgroup.subgroupOfEquivOfLe hMΓ).toMonoidHom.comp (φ.subgroupComap ((X ⊔ A).subgroupOf Γ))
  have hτ : Function.Surjective τ := by
    intro m
    obtain ⟨h, hh⟩ := hφ ⟨(m : MulAut V), hMΓ m.2⟩
    have hmemH : h ∈ H := by
      rw [Subgroup.mem_comap, hh]
      exact m.2
    refine ⟨⟨h, hmemH⟩, Subtype.ext ?_⟩
    show ((φ h : ↥Γ) : MulAut V) = m
    rw [hh]
  let π : ↥H →* ↥G := ψ.comp τ
  have hπ : Function.Surjective π := hψ.comp hτ
  have hLG : autSec X W U ≤ G := autSec_mono le_sup_left W U
  let Lb : Subgroup ↥G := (autSec X W U).subgroupOf G
  have hLbn : Lb.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using suzb4_conj_mem hAn hMW hMU g.2 hx⟩
  have hLq : CFSG.IsQuasisimple ↥Lb :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLG).symm hq
  have hlayer : CFSG.layer ↥Lb = ⊤ := suzb4_layer_eq_top hLq
  have h2 : IsPGroup 2 (↥G ⧸ Lb) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    show (QuotientGroup.mk y : ↥G ⧸ Lb) ^ (2 ^ 1) = 1
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact suzb4_sq_mem hAn hA2 hMW hMU y.2
  exact hA21 S' hS H ↥G π hπ Lb hlayer h2

end Sec

section Main

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ : Subgroup (MulAut Y)}

theorem suz_b4hyp_proved (hA21 : AsA21SQTKSection) (hΓ : IsQuotientOfSQTKTC ↥Γ)
    (hexp : ∀ y : Y, y ^ 2 = 1) {X A : Subgroup (MulAut Y)}
    (hXΓ : X ≤ Γ) (hAΓ : A ≤ Γ) (hXq : CFSG.IsQuasisimple ↥X) (hAel : IsElemAbelian2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut Y))) {I J : Subgroup Y} (hJI : J ≤ I)
    (hXI : X ≤ stabSub I) (hXJ : X ≤ stabSub J) (hAI : A ≤ stabSub I) (hAJ : A ≤ stabSub J)
    (hirr : ∀ T : Subgroup Y, J ≤ T → T ≤ I → (∀ x ∈ X, ∀ t ∈ T, x t ∈ T) → T = J ∨ T = I)
    (hnt : ∃ x ∈ X, ∃ w ∈ I, x w * w⁻¹ ∉ J) :
    B4Hyp (autSec (X ⊔ A) I J) (autSec X I J) := by
  have hMI : X ⊔ A ≤ stabSub I := sup_le hXI hAI
  have hMJ : X ⊔ A ≤ stabSub J := sup_le hXJ hAJ
  have hJI' : J < I := by
    obtain ⟨x, hx, w, hw, hxw⟩ := hnt
    refine lt_of_le_of_ne hJI ?_
    rintro rfl
    exact hxw (J.mul_mem ((hXI hx w).2 hw) (J.inv_mem hw))
  have hirr' : XMod.IsIrrSec ↥(autSec X I J) (⊥ : Subgroup (Sec I J)) ⊤ :=
    B5.isIrrSec_autSec hJI' (fun T hTinv hJT hTI => hirr T hJT hTI hTinv) hXI hXJ
  have hq : CFSG.IsQuasisimple ↥(autSec X I J) :=
    suzb4_isQuasisimple_autSec hXI hXJ hXq hnt
  have hLG : autSec X I J ≤ autSec (X ⊔ A) I J := autSec_mono le_sup_left I J
  have hn : ∀ y ∈ autSec (X ⊔ A) I J, ∀ l ∈ autSec X I J, y * l * y⁻¹ ∈ autSec X I J :=
    fun y hy l hl => suzb4_conj_mem hAX hMI hMJ hy hl
  have h2 : ∀ y ∈ autSec (X ⊔ A) I J, y ^ 2 ∈ autSec X I J :=
    fun y hy => suzb4_sq_mem hAX hAel.2 hMI hMJ hy
  have hRexp : ∀ r : Sec I J, r ^ 2 = 1 := by
    intro r
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective r
    rw [← QuotientGroup.mk_pow]
    have : w ^ 2 = 1 := Subtype.ext (by simpa using hexp (w : Y))
    rw [this]
    exact QuotientGroup.mk_one _
  have hqo := B1Red.isQuasisimple_to_open hq
  have hO2 : pCoreOf 2 (autSec (X ⊔ A) I J) = ⊥ :=
    suzb4_pCoreOf_eq_bot hLG hqo hn
      (fun x _ hx2 hxc => suzb4_invol_eq_one hRexp hirr' hx2 hxc)
  have hF : quasithinGenFitting (autSec (X ⊔ A) I J) = autSec X I J :=
    B1Red.quasithinGenFitting_eq_of_two_quot hLG hn hqo h2 hO2
  obtain ⟨S', _, _, hSQT, hK, φ, hφ⟩ := hΓ
  have hS : SQTKGroup S' := ⟨fun p hp hp2 => hSQT p hp hp2, hK⟩
  exact ⟨suzb4_sqtk hA21 hS φ hφ hXΓ hAΓ hq hAX hAel.2 hMI hMJ, hF.symm, hq, hirr'⟩

end Main

end CFSG.Quasithin
