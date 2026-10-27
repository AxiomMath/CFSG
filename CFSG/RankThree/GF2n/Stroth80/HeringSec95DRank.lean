module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DPair
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DLin
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DWV

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open Module
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem close95_core2 (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r)
    {z y c : G} (hzM : z ∈ M) (hzL : conjSubgroup z (LB M Q B) = LB M Q B)
    (hy : y ∈ N1 hc t) (hxN : z * y * z⁻¹ ∉ hc.CN t)
    (hcR : c ∈ Rt M (LB M Q B) t)
    (hCVle : conjSubgroup c B ≤ Vt M (LB M Q B) B Z t ⊓
      conjSubgroup z (Vt M (LB M Q B) B Z t))
    (hxC : z * y * z⁻¹ ∈ LB M Q (conjSubgroup c B))
    (hcN : c ∉ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G))
    (h5 : Five95 hc t z) :
    ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅z * y * z⁻¹, w⁆ ∈ Vt M (LB M Q B) B Z t := by
  classical
  obtain ⟨h51, h52, h53, h54, h55⟩ := h5
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hyL : y ∈ LB M Q B := (Subgroup.mem_inf.mp hy).1
  have hyN : y ∈ hc.CN t := (Subgroup.mem_inf.mp hy).2
  set x : G := z * y * z⁻¹ with hxdef
  have hxL : x ∈ LB M Q B := by
    have : x ∈ conjSubgroup z (LB M Q B) := conj_mem95 z hyL
    rwa [hzL] at this
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  have hxM : x ∈ M := hc.LB_le_M hxL
  have hzBZ := mem_normalizer_BZ95 h34 hs hzM hzL
  have hcM : c ∈ M := hc.Rt_le_M t hcR
  obtain ⟨K', fK', finK', chK', γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ₀, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  haveI : Finite M₀.E := Module.finite_of_finite K'
  have hKZ : Nat.card K' = Nat.card Z := h.card
  have hK2' : 1 < Nat.card K' := by rw [hKZ]; have := hc.hyp.q4; omega
  obtain ⟨U, hUmem, hUdim, hE, hUsing, hUperp⟩ := exists_lagrangian95 h34 hs h
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  have hQ : IsQuadSpace M₀.B M₀.Qf := ⟨M₀.alt, M₀.nondeg, M₀.Qf_add⟩
  have hbU : b ∈ U := (hUmem b).mpr (M₀.img_mono (le_inf hc.le hc.B_le_QB)
    ((hB b).mpr ⟨1, (one_smul K' b).symm⟩))
  let α : ↥(LB M Q B) →* (M₀.E ≃ₗ[K'] M₀.E) := φ₀.comp (Subgroup.inclusion hc.LB_le_H0)
  have hαπ : ∀ (l : ↥(LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((l : G) * x * (l : G)⁻¹) = α l (M₀.π x) := fun l x hx =>
    hφπ ⟨(l : G), hc.LB_le_H0 l.2⟩ x hx
  have hα1 : ∀ l : ↥(LB M Q B), α l = 1 ↔ (l : G) ∈ Q := fun l =>
    hφQ ⟨(l : G), hc.LB_le_H0 l.2⟩
  have hαiso : ∀ (l : ↥(LB M Q B)) e, M₀.Qf (α l e) = M₀.Qf e := fun l e =>
    hφiso ⟨(l : G), hc.LB_le_H0 l.2⟩ e
  have hS : Siegel M₀.B M₀.Qf α U b := by
    refine ⟨hαiso, fun l e => ?_, hUsing, hUperp, hbU, hb0, fun l => ?_, fun l u hu => ?_⟩
    · have h1 : α l * α l = 1 := by
        rw [← map_mul, hα1]
        show (l : G) * (l : G) ∈ Q
        rw [← pow_two]
        exact hc.sq_mem_Q_of_mem_LB l.2
      have := congrArg (fun f : M₀.E ≃ₗ[K'] M₀.E => f e) h1
      simpa using this
    · exact (hc.LB_act_fix_line h hB l.2 (T := (α l : M₀.E →ₗ[K'] M₀.E)) (hαπ l)).1
    · obtain ⟨c, hc'⟩ := (hc.LB_act_fix_line h hB l.2 (T := (α l : M₀.E →ₗ[K'] M₀.E))
        (hαπ l)).2 u ((hUmem u).mp hu)
      refine ⟨c, ?_⟩
      have : α l u - u = c • b := hc'
      rw [← this]; abel
  set V := Vt M (LB M Q B) B Z t with hV
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  obtain ⟨-, -, hVA₂, hA₂W, -⟩ := isOppDecomp95 h34 h91b hs hr
  have hVW : V ≤ Wt Q V := hVA₂.trans hA₂W
  let Vsub : Submodule K' M₀.E := imgSub M₀ V (fun c e he => hc.smul_mem_img_Vt h t c he)
  have hVsub_mem : ∀ e, e ∈ Vsub ↔ e ∈ M₀.img V := fun e => mem_imgSub
  have hVsubdim : finrank K' Vsub = 4 := by
    have h1 : Nat.card ↥Vsub = Nat.card (M₀.img V) :=
      Nat.card_congr (Equiv.subtypeEquivRight hVsub_mem)
    have h2 := M₀.card_eq hVQ hZV
    rw [hs.card_V] at h2
    have h3 : Nat.card (M₀.img V) = Nat.card Z ^ 4 := by
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← h2]
      ring
    have h4 : Nat.card K' ^ finrank K' Vsub = Nat.card K' ^ 4 := by
      rw [← Module.natCard_eq_pow_finrank, h1, h3, hKZ]
    exact Nat.pow_right_injective hK2' h4
  have hWimg : ∀ e, (∀ v ∈ Vsub, M₀.B v e = 0) ↔ e ∈ M₀.img (Wt Q V) := by
    intro e
    rw [mem_img_Wt_iff M₀ h.reg hVQ]
    constructor
    · intro H v hv
      rw [hQ.B_neg v e, H v ((hVsub_mem v).mpr hv), neg_zero]
    · intro H v hv
      rw [hQ.B_neg e v, H v ((hVsub_mem v).mp hv), neg_zero]
  have hVV : ∀ v ∈ Vsub, ∀ v' ∈ Vsub, M₀.B v v' = 0 := by
    intro v hv v' hv'
    obtain ⟨a', ha'V, ha'Q, rfl⟩ := (hVsub_mem v').mp hv'
    have h1 : M₀.π a' ∈ M₀.img (Wt Q V) := M₀.pi_mem_img (hVW ha'V) ha'Q
    have h2 := (mem_img_Wt_iff M₀ h.reg hVQ).mp h1 v ((hVsub_mem v).mp hv)
    rw [hQ.B_neg (M₀.π a') v, h2, neg_zero]
  have hcommπ : ∀ (l : ↥(LB M Q B)) (a : G), a ∈ Q →
      ⁅(l : G), a⁆ ∈ Q ∧ M₀.π ⁅(l : G), a⁆ = α l (M₀.π a) - M₀.π a := by
    intro l a ha
    have hlM : (l : G) ∈ M := hc.LB_le_M l.2
    have hnorm : (l : G) * a * (l : G)⁻¹ ∈ Q := n12l3_normalizes_Q hc hlM ha
    have hcQ : ⁅(l : G), a⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem hnorm (Q.inv_mem ha)
    refine ⟨hcQ, ?_⟩
    have e : ⁅(l : G), a⁆ = ((l : G) * a * (l : G)⁻¹) * a⁻¹ := by rw [commutatorElement_def]
    rw [e, M₀.π_mul _ hnorm _ (Q.inv_mem ha), M₀.pi_inv ha, hαπ l a ha, sub_eq_add_neg]
  let xa : ↥(LB M Q B) := ⟨x, hxL⟩
  let T : M₀.E ≃ₗ[K'] M₀.E := α xa
  have hT : ∀ e, M₀.Qf (T e) = M₀.Qf e := fun e => hαiso xa e
  have hT2 : ∀ e, T (T e) = e := fun e => hS.invol xa e
  have hTV : ∀ v ∈ Vsub, T v ∈ Vsub := by
    intro v hv
    obtain ⟨a, haV, haQ, rfl⟩ := (hVsub_mem v).mp hv
    have h1 : x * a * x⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hxR) a).mp haV
    show α xa (M₀.π a) ∈ Vsub
    rw [← hαπ xa a haQ]
    exact (hVsub_mem _).mpr (M₀.pi_mem_img h1 (n12l3_normalizes_Q hc hxM haQ))
  let Φ : M₀.E →ₗ[K'] M₀.E := (T : M₀.E →ₗ[K'] M₀.E) - 1
  have hΦe : ∀ e, Φ e = T e - e := fun e => by simp [Φ]
  have hΦπ : ∀ a ∈ Q, Φ (M₀.π a) = M₀.π ⁅x, a⁆ := fun a ha => by
    rw [hΦe]
    exact ((hcommπ xa a ha).2).symm
  set Vz : Subgroup G := conjSubgroup z V with hVz
  have hVzQ : Vz ≤ Q := by
    intro a ha
    have h1 : z⁻¹ * a * z ∈ V := mem_conjSubgroup.mp ha
    have h2 := (hc.conj_mem_Q_of_mem_M hzM).1 _ (hVQ h1)
    have e : z * (z⁻¹ * a * z) * z⁻¹ = a := by group
    rwa [e] at h2
  have hVzZ : Z ≤ V ⊓ Vz := le_inf hZV (Z_le_conj_Vt hc hzM)
  have hDQ : V ⊓ Vz ≤ Q := inf_le_left.trans hVQ
  have hDcard : Nat.card (M₀.img (V ⊓ Vz)) = Nat.card Z ^ 2 := by
    have h2 := M₀.card_eq hDQ hVzZ
    rw [h51] at h2
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
    rw [← h2]
    ring
  have hS5 : ⁅V, Subgroup.zpowers x⁆ ⊔ Z = V ⊓ Vz := h55 x (conj_mem95 z hy) hxN
  have hΦD : ∀ e ∈ Vsub.map Φ, e ∈ M₀.img (V ⊓ Vz) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨a, haV, haQ, rfl⟩ := (hVsub_mem v).mp hv
    rw [hΦπ a haQ]
    have hxa : ⁅x, a⁆ ∈ V ⊓ Vz := by
      rw [← hS5]
      refine Subgroup.mem_sup_left ?_
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator haV (Subgroup.mem_zpowers x))
    exact M₀.pi_mem_img hxa ((hcommπ xa a haQ).1)
  obtain ⟨K, fK, finK, hch, hnrm, ⟨C⟩⟩ := exists_coord95 h34 hs hr
  obtain ⟨w₀, -, -, -, -, -, hCentV⟩ := C.plane_facts hs hxL hxN
  have hf1 : finrank K' ↥(LinearMap.ker Φ ⊓ Vsub) ≤ 2 := by
    have hZC : Z ≤ CentMod Z V (Vt_le_normalizer hc t) x := fun ζ hζ => ⟨hZV hζ, by
      have e : ⁅x, ζ⁆ = (x * ζ * x⁻¹) * ζ⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hxM) ζ).mp hζ)
        (Z.inv_mem hζ)⟩
    have hCle : CentMod Z V (Vt_le_normalizer hc t) x ≤ Q := fun a ha =>
      hVQ (mem_CentMod.mp ha).1
    have hcardC := M₀.card_eq hCle hZC
    rw [hCentV] at hcardC
    have himg : Nat.card (M₀.img (CentMod Z V (Vt_le_normalizer hc t) x)) =
        Nat.card Z ^ 2 := by
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← hcardC]
      ring
    have hsub : ((LinearMap.ker Φ ⊓ Vsub : Submodule K' M₀.E) : Set M₀.E) ⊆
        ↑(M₀.img (CentMod Z V (Vt_le_normalizer hc t) x)) := by
      intro e he
      obtain ⟨hFe, hVe⟩ := he
      obtain ⟨a, haV, haQ, rfl⟩ := (hVsub_mem e).mp hVe
      have hTe : T (M₀.π a) = M₀.π a := by
        have := LinearMap.mem_ker.mp hFe
        rw [hΦe] at this
        exact sub_eq_zero.mp this
      have hxaQ : x * a * x⁻¹ ∈ Q := n12l3_normalizes_Q hc hxM haQ
      have hπ : M₀.π (x * a * x⁻¹) = M₀.π a := by
        rw [hαπ xa a haQ]
        exact hTe
      have hcomm : ⁅x, a⁆ ∈ Z := (M₀.comm_mem_iff haQ hxaQ).mpr hπ
      exact M₀.pi_mem_img (show a ∈ CentMod Z V (Vt_le_normalizer hc t) x from ⟨haV, hcomm⟩) haQ
    have hle : Nat.card ↥(LinearMap.ker Φ ⊓ Vsub) ≤
        Nat.card ↥(M₀.img (CentMod Z V (Vt_le_normalizer hc t) x)) :=
      Nat.card_mono (Set.toFinite _) hsub
    rw [himg] at hle
    have h5 : Nat.card K' ^ finrank K' ↥(LinearMap.ker Φ ⊓ Vsub) ≤ Nat.card K' ^ 2 := by
      rw [← Module.natCard_eq_pow_finrank, hKZ]
      exact hle
    exact (Nat.pow_le_pow_iff_right hK2').mp h5
  have hfrk := finrank_map_add_finrank_inf_ker Φ Vsub
  have hΦsub : ((Vsub.map Φ : Submodule K' M₀.E) : Set M₀.E) ⊆ ↑(M₀.img (V ⊓ Vz)) := hΦD
  have hΦle : finrank K' ↥(Vsub.map Φ) ≤ 2 := by
    have hle : Nat.card ↥(Vsub.map Φ) ≤ Nat.card ↥(M₀.img (V ⊓ Vz)) :=
      Nat.card_mono (Set.toFinite _) hΦsub
    rw [hDcard] at hle
    have h5 : Nat.card K' ^ finrank K' ↥(Vsub.map Φ) ≤ Nat.card K' ^ 2 := by
      rw [← Module.natCard_eq_pow_finrank, hKZ]
      exact hle
    exact (Nat.pow_le_pow_iff_right hK2').mp h5
  have hPdim : finrank K' ↥(Vsub.map Φ) = 2 := by omega
  have hDeq : ∀ e ∈ M₀.img (V ⊓ Vz), e ∈ Vsub.map Φ := by
    have hnc : (↑(M₀.img (V ⊓ Vz)) : Set M₀.E).ncard ≤
        ((Vsub.map Φ : Submodule K' M₀.E) : Set M₀.E).ncard := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      have h2 : Nat.card ↥(Vsub.map Φ) = Nat.card Z ^ 2 := by
        rw [← hKZ, Module.natCard_eq_pow_finrank (K := K'), hPdim]
      exact le_of_eq (hDcard.trans h2.symm)
    have heq := Set.eq_of_subset_of_ncard_le hΦsub hnc
    intro e he
    have he' : e ∈ ((Vsub.map Φ : Submodule K' M₀.E) : Set M₀.E) := by
      rw [heq]
      exact he
    exact he'
  have hcH0 : c ∈ H0 M Z := hc.Rt_le_H0 t hcR
  let P : M₀.E ≃ₗ[K'] M₀.E := φ₀ ⟨c, hcH0⟩
  have hPiso : ∀ e, M₀.Qf (P e) = M₀.Qf e := fun e => hφiso ⟨c, hcH0⟩ e
  have hPπ : ∀ a ∈ Q, M₀.π (c * a * c⁻¹) = P (M₀.π a) := fun a ha => hφπ ⟨c, hcH0⟩ a ha
  have hcQ' : ∀ a ∈ Q, c * a * c⁻¹ ∈ Q := fun a ha => (hc.conj_mem_Q_of_mem_M hcM).1 a ha
  have hl : c⁻¹ * x * c ∈ LB M Q B := by
    have h1 : x ∈ conjSubgroup c (LB M Q B) := by
      rw [← hc.LB_conj hcM]
      exact hxC
    simpa using mem_conjSubgroup.mp h1
  let la : ↥(LB M Q B) := ⟨c⁻¹ * x * c, hl⟩
  let Tl : M₀.E ≃ₗ[K'] M₀.E := α la
  have hTT : ∀ e, T e = P (Tl (P.symm e)) := by
    have hxH0 : x ∈ H0 M Z := hc.LB_le_H0 hxL
    have h1 : T = P * Tl * P⁻¹ := by
      show φ₀ ⟨x, hxH0⟩ = φ₀ ⟨c, hcH0⟩ * φ₀ ⟨c⁻¹ * x * c, hc.LB_le_H0 hl⟩ * (φ₀ ⟨c, hcH0⟩)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    intro e
    have := congrArg (fun f : M₀.E ≃ₗ[K'] M₀.E => f e) h1
    simpa [LinearEquiv.mul_apply] using this
  have hPV : ∀ v ∈ Vsub, P v ∈ Vsub := by
    intro v hv
    obtain ⟨a, haV, haQ, rfl⟩ := (hVsub_mem v).mp hv
    rw [← hPπ a haQ]
    have h1 : c * a * c⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hcR) a).mp haV
    exact (hVsub_mem _).mpr (M₀.pi_mem_img h1 (hcQ' a haQ))
  have hCV : ∀ a ∈ conjSubgroup c B, a ∈ V ⊓ Vz := fun a ha => hCVle ha
  let U₂ : Submodule K' M₀.E := U.map (P : M₀.E →ₗ[K'] M₀.E)
  have hPB : ∀ e f, M₀.B (P e) (P f) = M₀.B e f := fun e f => hQ.B_iso P hPiso e f
  have hUorth : ∀ e ∈ U, ∀ f ∈ U, M₀.B e f = 0 := by
    intro e he f hf
    have h1 := M₀.Qf_add e f
    rw [hUsing _ (U.add_mem he hf), hUsing e he, hUsing f hf] at h1
    linear_combination -h1
  have hU₁ : M₀.B.orthogonal U = U := by
    refine le_antisymm (fun e he => hUperp e (LinearMap.BilinForm.mem_orthogonal_iff.mp he)) ?_
    intro e he
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun f hf => ?_
    exact hUorth f hf e he
  have hU₂ : M₀.B.orthogonal U₂ = U₂ := by
    apply le_antisymm
    · intro e he
      have he' : ∀ v ∈ U₂, M₀.B v e = 0 := LinearMap.BilinForm.mem_orthogonal_iff.mp he
      have h1 : P.symm e ∈ U := by
        rw [← hU₁]
        refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => ?_
        have h2 := he' (P u) ⟨u, hu, rfl⟩
        rw [← hPB u (P.symm e), LinearEquiv.apply_symm_apply]
        exact h2
      exact ⟨P.symm e, h1, by simp⟩
    · intro e he
      obtain ⟨u, hu, rfl⟩ := he
      refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun v hv => ?_
      obtain ⟨u', hu', rfl⟩ := hv
      show M₀.B (P u') (P u) = 0
      rw [hPB]
      exact hUorth u' hu' u hu
  have hb : ∀ e, M₀.B b e = 0 → T e - e ∈ U := fun e he => hS.sub_mem_U hQ xa he
  have hb' : ∀ u ∈ U, T u - u ∈ Submodule.span K' {b} := by
    intro u hu
    obtain ⟨s, hs'⟩ := hS.act xa u hu
    have : T u - u = s • b := by
      show α xa u - u = s • b
      rw [hs']
      abel
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)
  have hbl : ∀ e, M₀.B b e = 0 → Tl e - e ∈ U := fun e he => hS.sub_mem_U hQ la he
  have hbl' : ∀ u ∈ U, Tl u - u ∈ Submodule.span K' {b} := by
    intro u hu
    obtain ⟨s, hs'⟩ := hS.act la u hu
    have : Tl u - u = s • b := by
      show α la u - u = s • b
      rw [hs']
      abel
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)
  have hc1 : ∀ e, M₀.B (P b) e = 0 → T e - e ∈ U₂ := by
    intro e he
    have h1 : M₀.B b (P.symm e) = 0 := by
      have := hPB b (P.symm e)
      rw [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      exact he
    refine ⟨Tl (P.symm e) - P.symm e, hbl _ h1, ?_⟩
    show P (Tl (P.symm e) - P.symm e) = T e - e
    rw [map_sub, ← hTT e, LinearEquiv.apply_symm_apply]
  have hc2 : ∀ u ∈ U₂, T u - u ∈ Submodule.span K' {P b} := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨s, hs'⟩ := Submodule.mem_span_singleton.mp (hbl' u hu)
    have : T (P u) - P u = s • P b := by
      rw [hTT, LinearEquiv.symm_apply_apply, ← map_sub, ← hs']
      simp
    show T (P u) - P u ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  let V' : Submodule K' M₀.E := imgSub M₀ Vz (fun c' e he =>
    smul_mem_img_conj95 hc h hzM hVQ (fun c e he => hc.smul_mem_img_Vt h t c he) c' he)
  have hV'mem : ∀ e, e ∈ V' ↔ e ∈ M₀.img Vz := fun e => mem_imgSub
  have hpol := C.polar_conj_eq_zero95 hs hcR h52 hCV h53
  obtain ⟨hL1, hL2⟩ := C.mem_QB_of_pair95 hs hcR hpol
  obtain ⟨b₀, hb₀B, hb₀Q, hb₀π⟩ := M₀.mem_img.mp ((hB b).mpr ⟨1, (one_smul K' b).symm⟩)
  have hcb₀Q : c * b₀ * c⁻¹ ∈ Q := hcQ' b₀ hb₀Q
  have hbV' : b ∈ V' := by
    rw [hV'mem, ← hb₀π]
    exact M₀.pi_mem_img (h52 hb₀B).2 hb₀Q
  have hbU₂ : b ∈ U₂ := by
    have hQ1 : c⁻¹ * b₀ * c ∈ Q := by
      have := (hc.conj_mem_Q_of_mem_M (M.inv_mem hcM)).1 b₀ hb₀Q
      simpa using this
    refine ⟨M₀.π (c⁻¹ * b₀ * c), (hUmem _).mpr ?_, ?_⟩
    · refine M₀.pi_mem_img ⟨hQ1, ?_⟩ hQ1
      have h1 := hL1 b₀ hb₀B
      rw [QB_conj, mem_conjSubgroup] at h1
      exact h1
    · show P (M₀.π (c⁻¹ * b₀ * c)) = b
      rw [← hPπ _ hQ1]
      have e : c * (c⁻¹ * b₀ * c) * c⁻¹ = b₀ := by group
      rw [e, hb₀π]
  have hc'V' : P b ∈ V' := by
    rw [hV'mem, ← hb₀π, ← hPπ _ hb₀Q]
    exact M₀.pi_mem_img (hCV _ (conj_mem95 c hb₀B)).2 hcb₀Q
  have hc'U : P b ∈ U := by
    rw [hUmem, ← hb₀π, ← hPπ _ hb₀Q]
    exact M₀.pi_mem_img ⟨hcb₀Q, hL2 b₀ hb₀B⟩ hcb₀Q
  have hc'U₂ : P b ∈ U₂ := ⟨b, hbU, rfl⟩
  have hCtxc : Ctx M Q Z (conjSubgroup c B) := hc.conj_of_mem hcM
  have hdim : finrank K' ↥(V' ⊓ U ⊓ U₂) ≤ 2 := by
    have hcardS := C.card_conj_inf95 hs h hzM hzBZ hcR hcN hCV h54
    have hSQ : Vz ⊓ QB B ⊓ QB (conjSubgroup c B) ≤ Q :=
      inf_le_left.trans (inf_le_left.trans hVzQ)
    have hZS : Z ≤ Vz ⊓ QB B ⊓ QB (conjSubgroup c B) :=
      le_inf (le_inf (Z_le_conj_Vt hc hzM) hc.Z_le_QB.1) hCtxc.Z_le_QB.1
    have hcardimg := M₀.card_eq hSQ hZS
    rw [hcardS] at hcardimg
    have himg : Nat.card (M₀.img (Vz ⊓ QB B ⊓ QB (conjSubgroup c B))) = Nat.card Z ^ 2 := by
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← hcardimg]
      ring
    have hsub : ((V' ⊓ U ⊓ U₂ : Submodule K' M₀.E) : Set M₀.E) ⊆
        ↑(M₀.img (Vz ⊓ QB B ⊓ QB (conjSubgroup c B))) := by
      intro e he
      obtain ⟨⟨heV', heU⟩, heU₂⟩ := he
      obtain ⟨a, haVz, haQ, rfl⟩ := (hV'mem e).mp heV'
      have h1 : M₀.π a ∈ M₀.img (Q ⊓ QB B) := (hUmem _).mp heU
      have h1' : a ∈ Q ⊓ QB B :=
        (M₀.mem_img_iff (le_inf hZQ hc.Z_le_QB.1) haQ).mp h1
      obtain ⟨u, hu, hue⟩ := heU₂
      obtain ⟨a₀, ha₀S, ha₀Q, rfl⟩ := (hUmem u).mp hu
      have h2 : M₀.π a ∈ M₀.img (Q ⊓ QB (conjSubgroup c B)) := by
        have h3 : M₀.π a = P (M₀.π a₀) := hue.symm
        rw [h3, ← hPπ a₀ ha₀Q]
        refine M₀.pi_mem_img ⟨hcQ' a₀ ha₀Q, ?_⟩ (hcQ' a₀ ha₀Q)
        rw [QB_conj]
        exact conj_mem95 c (Subgroup.mem_inf.mp ha₀S).2
      have h2' : a ∈ Q ⊓ QB (conjSubgroup c B) :=
        (M₀.mem_img_iff (le_inf hZQ hCtxc.Z_le_QB.1) haQ).mp h2
      exact M₀.pi_mem_img ⟨⟨haVz, h1'.2⟩, h2'.2⟩ haQ
    have hle : Nat.card ↥(V' ⊓ U ⊓ U₂) ≤
        Nat.card ↥(M₀.img (Vz ⊓ QB B ⊓ QB (conjSubgroup c B))) :=
      Nat.card_mono (Set.toFinite _) hsub
    rw [himg] at hle
    have h5 : Nat.card K' ^ finrank K' ↥(V' ⊓ U ⊓ U₂) ≤ Nat.card K' ^ 2 := by
      rw [← Module.natCard_eq_pow_finrank, hKZ]
      exact hle
    exact (Nat.pow_le_pow_iff_right hK2').mp h5
  have hWz : ∀ e, (∀ v ∈ V', M₀.B v e = 0) ↔ e ∈ M₀.img (Wt Q Vz) := by
    intro e
    rw [mem_img_Wt_iff M₀ h.reg hVzQ]
    constructor
    · intro H v hv
      rw [hQ.B_neg v e, H v ((hV'mem v).mpr hv), neg_zero]
    · intro H v hv
      rw [hQ.B_neg e v, H v ((hV'mem v).mp hv), neg_zero]
  have hW' : ∀ e, (∀ v ∈ V', M₀.B v e = 0) → T e - e ∈ V' := by
    intro e he
    obtain ⟨a, haW, haQ, rfl⟩ := (hWz e).mp he
    have haW' : z⁻¹ * a * z ∈ Wt Q V := by
      refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      · have := (hc.conj_mem_Q_of_mem_M (M.inv_mem hzM)).1 a haQ
        simpa using this
      · have hzv : z * v * z⁻¹ ∈ Vz := conj_mem95 z hv
        have h1 := Subgroup.mem_centralizer_iff.mp haW.2 _ hzv
        have e1 : v * (z⁻¹ * a * z) = z⁻¹ * ((z * v * z⁻¹) * a) * z := by group
        have e2 : z⁻¹ * a * z * v = z⁻¹ * (a * (z * v * z⁻¹)) * z := by group
        rw [e1, e2, h1]
    have hcomm : ⁅y, z⁻¹ * a * z⁆ ∈ V := comm_CN_Wt_mem_Vt h91b hs hr hyN haW'
    have hxa : ⁅x, a⁆ ∈ Vz := by
      have e : ⁅x, a⁆ = z * ⁅y, z⁻¹ * a * z⁆ * z⁻¹ := by
        simp only [hxdef, commutatorElement_def]
        group
      rw [e]
      exact conj_mem95 z hcomm
    have hxaQ : ⁅x, a⁆ ∈ Q := (hcommπ xa a haQ).1
    have : T (M₀.π a) - M₀.π a = M₀.π ⁅x, a⁆ := ((hcommπ xa a haQ).2).symm
    rw [this, hV'mem]
    exact M₀.pi_mem_img hxa hxaQ
  have key := map_orth_le_of_two_points95 hQ T hT hT2 (V := Vsub) (V' := V') (U₁ := U) (U₂ := U₂)
    (b := b) (c := P b) hVV hTV hPdim hU₁ hU₂ ⟨⟨hbV', hbU⟩, hbU₂⟩ ⟨⟨hc'V', hc'U⟩, hc'U₂⟩ hW' hb hb'
    hc1 hc2 hdim
  intro w hw
  have hwQ : w ∈ Q := hw.1
  have h2 : ∀ v ∈ Vsub, M₀.B v (M₀.π w) = 0 := (hWimg _).mpr (M₀.pi_mem_img hw hwQ)
  have h3 := key _ h2
  have h4 : M₀.π ⁅x, w⁆ ∈ M₀.img V := by
    rw [(hcommπ xa w hwQ).2]
    exact (hVsub_mem _).mp h3
  exact (M₀.mem_img_iff hZV (hcommπ xa w hwQ).1).mp h4

theorem exists_conj_R_of_point95 {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {z : G} (h5 : Five95 hc t z) {ρ : G} (hρM : ρ ∈ M)
    (hCV : conjSubgroup ρ B ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t))
    (hCB : ¬ conjSubgroup ρ B ≤ B ⊔ Z) :
    ∃ c ∈ Rt M (LB M Q B) t, conjSubgroup ρ B ⊔ Z = conjSubgroup c B ⊔ Z := by
  classical
  obtain ⟨u, huC, huZ⟩ : ∃ u ∈ conjSubgroup ρ B, u ∉ Z := by
    by_contra hall
    push Not at hall
    exact hCB fun u hu => Subgroup.mem_sup_right (hall u hu)
  obtain ⟨c, hcR, b₁, hb₁B, hu1⟩ := h5.2.2.1 u (hCV huC)
  have hcM : c ∈ M := hc.Rt_le_M t hcR
  obtain ⟨K', fK', finK', chK', γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  have hCctx : Ctx M Q Z (conjSubgroup ρ B) := hc.conj_of_mem hρM
  have hCctx' : Ctx M Q Z (conjSubgroup c B) := hc.conj_of_mem hcM
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have huQ : u ∈ Q := hCctx.le huC
  have ha'C : c * b₁ * c⁻¹ ∈ conjSubgroup c B := conj_mem95 c hb₁B
  have ha'Q : c * b₁ * c⁻¹ ∈ Q := hCctx'.le ha'C
  have hpi : M₀.π u = M₀.π (c * b₁ * c⁻¹) := by
    have h1 : u * (c * b₁ * c⁻¹)⁻¹ ∈ Z := hu1
    have h2 : M₀.π (u * (c * b₁ * c⁻¹)⁻¹) = 0 :=
      (M₀.π_ker _ (Q.mul_mem huQ (Q.inv_mem ha'Q))).mpr h1
    have h3 := M₀.π_mul _ (Q.mul_mem huQ (Q.inv_mem ha'Q)) _ ha'Q
    rw [h2, inv_mul_cancel_right, zero_add] at h3
    exact h3
  have hne : M₀.π u ≠ 0 := fun h0 => huZ ((M₀.π_ker _ huQ).mp h0)
  refine ⟨c, hcR, le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)⟩
  · have := le_sup_of_common_pi95 h hCctx' hCctx ha'C huC hpi.symm (hpi ▸ hne)
    rw [sup_comm] at this
    exact this
  · have := le_sup_of_common_pi95 h hCctx hCctx' huC ha'C hpi hne
    rw [sup_comm] at this
    exact this

end HS9

@[expose] def Step95LCStatementFrom (n0 : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
    (Z0 : Subgroup G), HS9.Cfg95 hc n t Z0 → n0 ≤ n → HS9.One95 hc t Z0 →
      ∀ z : G, HS9.ZPair95 hc t Z0 z → HS9.Three95 hc t z → HS9.Five95 hc t z →
        ∃ ρ ∈ conjSubgroup z (Rt M (LB M Q B) t),
          conjSubgroup ρ B ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) ∧
          ¬ conjSubgroup ρ B ≤ B ⊔ Z ∧
          ∃ x ∈ conjSubgroup z (HS9.N1 hc t) ⊓ LB M Q (conjSubgroup ρ B), x ∉ hc.CN t

@[expose] def Step95RankLCStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
    (Z0 : Subgroup G), HS9.Cfg95 hc n t Z0 →
      ∀ z : G, HS9.ZPair95 hc t Z0 z → HS9.Three95 hc t z → HS9.Five95 hc t z →
        ∀ ρ ∈ conjSubgroup z (Rt M (LB M Q B) t),
          conjSubgroup ρ B ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) →
          ¬ conjSubgroup ρ B ≤ B ⊔ Z →
          ∀ x ∈ conjSubgroup z (HS9.N1 hc t) ⊓ LB M Q (conjSubgroup ρ B), x ∉ hc.CN t →
            ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t

theorem rankLC95_of (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    (hA : Sec9AExistsStatement) : Step95RankLCStatement := by
  intro G _ _ M Q Z B hc n t Z0 cfg z hz h3 h5 ρ hρ hCV hCB x hx hxN w hw
  have hs := cfg.hs
  obtain ⟨hxz, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hρM : ρ ∈ M := by
    have h1 : z⁻¹ * ρ * z ∈ Rt M (LB M Q B) t := mem_conjSubgroup.mp hρ
    have h2 := hc.Rt_le_M t h1
    have e : ρ = z * (z⁻¹ * ρ * z) * z⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hz.mem h2) (M.inv_mem hz.mem)
  obtain ⟨c, hcR, hcC⟩ := HS9.exists_conj_R_of_point95 hs h5 hρM hCV hCB
  have hcM : c ∈ M := hc.Rt_le_M t hcR
  have hZle : Z ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) :=
    le_inf sec39_Z_le_Vt (HS9.Z_le_conj_Vt hc hz.mem)
  have hCV' : conjSubgroup c B ≤ Vt M (LB M Q B) B Z t ⊓
      conjSubgroup z (Vt M (LB M Q B) B Z t) :=
    le_sup_left.trans (hcC ▸ sup_le hCV hZle)
  have hcN : c ∉ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
    intro hcN
    have h1 : conjSubgroup c B ≤ B ⊔ Z :=
      (conjSubgroup_eq_self_iff.mpr hcN : conjSubgroup c (B ⊔ Z) = B ⊔ Z) ▸
        (Subgroup.map_mono le_sup_left)
    apply hCB
    exact le_sup_left.trans (hcC ▸ sup_le h1 le_sup_right)
  have hxC' : x ∈ LB M Q (conjSubgroup c B) := by
    rw [hc.LB_conj hρM, hc.conj_LB_eq_of_conj_BZ hρM hcM hcC, ← hc.LB_conj hcM] at hxC
    exact hxC
  obtain ⟨y, hy, rfl⟩ : ∃ y ∈ HS9.N1 hc t, z * y * z⁻¹ = x :=
    ⟨z⁻¹ * x * z, mem_conjSubgroup.mp hxz, by group⟩
  exact HS9.close95_core2 h34 h91b hs hr hz.mem hz.normL hy hxN hcR hCV' hxC' hcN h5 w hw

theorem wvMin_of_LC (n0 : ℕ) (hF : Step95LCStatementFrom n0) (hR : Step95RankLCStatement) :
    Step95WVMinStatementFrom n0 := by
  intro G _ _ M Q Z B hc n t Z0 hcfg hn h1 z hz h3 h5
  obtain ⟨ρ, hρ, hCV, hCB, x, hx, hxN⟩ := hF G M Q Z B hc n t Z0 hcfg hn h1 z hz h3 h5
  exact ⟨x, (Subgroup.mem_inf.mp hx).1, hxN,
    hR G M Q Z B hc n t Z0 hcfg z hz h3 h5 ρ hρ hCV hCB x hx hxN⟩

theorem wvMin_of_lc95 (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    (hA : Sec9AExistsStatement) {n0 : ℕ} (hF : Step95LCStatementFrom n0) :
    Step95WVMinStatementFrom n0 :=
  wvMin_of_LC n0 hF (rankLC95_of h34 h91b hA)

end CFSG.RankThree.GF2n.Stroth80
