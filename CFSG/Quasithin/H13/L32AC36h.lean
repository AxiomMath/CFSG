module

public import CFSG.Quasithin.H13.L32AC36g
public import CFSG.Quasithin.Background.F918C8
public import CFSG.Quasithin.EmptyFaithful.F918C5
public import CFSG.Quasithin.EmptyFaithful.SzN15Vocab

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.SzN15

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G}

section Lower

variable {I : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))]

theorem four_mul_card_le_fixMod (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hIU : I ≤ conjClosure V H) (hV₁I : fsuV1 T V ≤ I) (hHI : H ≤ Subgroup.normalizer (I : Set G))
    (hVI : V ≤ I) (hK₀ : conjClosure K T = K) {R : Subgroup G}
    (hR : ∀ r ∈ R, ∀ v ∈ V, r * v * r⁻¹ * v⁻¹ ∈ fsuV1 T V)
    (hRV : R ≤ Subgroup.normalizer (V : Set G)) {x : G} (hxK : x ∈ K)
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V)
    (hV4 : (fsuV1 T V).relIndex V = 4)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) :
    4 * Nat.card ↥((subM (fsuV1 T V) (conjClosure I H) I ⊓
        fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
          (subM (fsuV1 T V) (conjClosure I H) I)) ≤
      Nat.card ↥(fixMod ((R.subgroupOf H).map (psiI hF hIU hV₁I hHI)) ⊤
        ((subM (fsuV1 T V) (conjClosure I H) I ⊓
          fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
            (subM (fsuV1 T V) (conjClosure I H) I))) := by
  set V₁ := fsuV1 T V with hV₁
  set IH := conjClosure I H with hIH'
  set V' := subM V₁ IH I with hV'
  set Mp := autIH V₁ I H (conjClosure K T) with hMp
  set C := (V' ⊓ fixV Mp).subgroupOf V' with hC
  set Ψ := psiI hF hIU hV₁I hHI with hΨ
  set Rc := (R.subgroupOf H).map Ψ with hRc
  have hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G) := hF.conjClosure_le_normalizer_V₁ hIU
  have hIH : H ≤ Subgroup.normalizer (IH : Set G) := le_normalizer_conjClosure I H
  have hVIH : V ≤ IH := hVI.trans (le_conjClosure I H)
  have hV₁V : V₁ ≤ V := inf_le_left
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hsub : subM V₁ IH V ≤ V' := fun w hw => secImg_mono hVI hw
  set Vt := (subM V₁ IH V).subgroupOf V' with hVt
  have hVt4 : Nat.card Vt = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsub).toEquiv,
      card_subM hIHN hV₁V hVIH, hV4]
  have hrep : ∀ w ∈ Vt, ∃ v : G, ∃ hv : v ∈ V,
      (w : ↥(tildeOf V₁ IH)) = modMk hIHN v (hVIH hv) := by
    intro w hw
    obtain ⟨a, haV, ha⟩ := mem_secImg.mp (show ((w : ↥(tildeOf V₁ IH)) :
      SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ tildeOf V₁ V from hw)
    exact ⟨a, haV, Subtype.ext ha.symm⟩
  have hMpK : Mp = autIH V₁ I H K := by rw [hMp, hK₀]
  have hVtC : C ⊓ Vt = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwC, hwVt⟩
    obtain ⟨v, hv, hwv⟩ := hrep w hwVt
    have hxK₀ : x ∈ conjClosure K T := le_conjClosure K T hxK
    have hxMp := actH_mem_autIH_of_mem (I := I) hF hF.K₀_le_H hxK₀
    have hwC' : (w : ↥(tildeOf V₁ IH)) ∈ V' ⊓ fixV Mp := Subgroup.mem_subgroupOf.mp hwC
    have hfix := hwC'.2 _ hxMp
    rw [hwv] at hfix
    have hc := hF.commutator_mem_of_actH_fix hIU (hVIH hv) hfix
    have hv1 := hfpf v hv hc
    rw [Subgroup.mem_bot]
    refine Subtype.ext (Subtype.ext ?_)
    rw [hwv]
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (x := ⟨v, hIHN (hVIH hv)⟩)).mpr hv1
  have hVtF : Vt ≤ fixMod Rc ⊤ C := by
    intro w hw
    refine ⟨Subgroup.mem_top w, fun r hr => ?_⟩
    obtain ⟨y, hyR, rfl⟩ := hr
    have hyR' : (y : G) ∈ R := Subgroup.mem_subgroupOf.mp hyR
    obtain ⟨v, hv, hwv⟩ := hrep w hw
    have h1 : Ψ y w = w := by
      apply Subtype.ext
      rw [psiI_apply, hwv, actH_modMk hF.H_le_normalizer_V₁ hIHN hIH y (hVIH hv)]
      apply Subtype.ext
      show secMk _ _ ⟨(y : G) * v * (y : G)⁻¹, _⟩ = secMk _ _ ⟨v, _⟩
      rw [secMk_eq_secMk_iff]
      have hc := hR y hyR' v hv
      have hyv : (y : G) * v * (y : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hRV hyR') v).mp hv
      show ((y : G) * v * (y : G)⁻¹)⁻¹ * v ∈ V₁
      set b := (y : G) * v * (y : G)⁻¹ with hb
      have e : b⁻¹ * v = (b * v⁻¹)⁻¹ := by
        rw [show (b * v⁻¹)⁻¹ = v * b⁻¹ by group]
        exact hVc _ (inv_mem hyv) v hv
      rw [e]
      exact inv_mem hc
    rw [h1, mul_inv_cancel]
    exact C.one_mem
  have hCF : C ≤ fixMod Rc ⊤ C := by
    intro c hc
    refine ⟨Subgroup.mem_top c, fun r hr => ?_⟩
    obtain ⟨y, -, rfl⟩ := hr
    refine C.mul_mem ?_ (C.inv_mem hc)
    have hc' : (c : ↥(tildeOf V₁ IH)) ∈ V' ⊓ fixV Mp := Subgroup.mem_subgroupOf.mp hc
    refine Subgroup.mem_subgroupOf.mpr ⟨(Ψ y c).2, fun m hm => ?_⟩
    rw [psiI_apply]
    have hyK : (y : G) ∈ Subgroup.normalizer (K : Set G) := hK₀ ▸ hF.K₀_normal y.2
    have hyN := actH_mem_normalizer_autIH (I := I) hF y.2 hyK
    rw [← hMpK] at hyN
    set a := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) y with ha
    have hm' : a⁻¹ * m * a⁻¹⁻¹ ∈ Mp := (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) m).mp hm
    rw [inv_inv] at hm'
    have h2 := hc'.2 _ hm'
    have h3 : m (a (c : ↥(tildeOf V₁ IH))) = a ((a⁻¹ * m * a) (c : ↥(tildeOf V₁ IH))) := by
      simp [MulAut.mul_apply]
    rw [h3, h2]
  have hsupF : Vt ⊔ C ≤ fixMod Rc ⊤ C := sup_le hVtF hCF
  have hcomm : Vt ≤ Subgroup.normalizer (C : Set ↥V') := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro c
    rw [mul_comm g c, mul_inv_cancel_right]
  have hcard := card_sup_eq hcomm
  have h1 := Subgroup.relIndex_mul_card C Vt
  rw [hVtC, Subgroup.card_bot, mul_one, hVt4] at h1
  rw [h1] at hcard
  rw [← hcard]
  exact Subgroup.card_le_of_le hsupF

end Lower

end CFSG.Quasithin.H13.L32A.C
