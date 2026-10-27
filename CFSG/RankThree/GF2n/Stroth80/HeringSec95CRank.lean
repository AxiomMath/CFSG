module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CGeo
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CHP
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CLin
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95COne
public import CFSG.RankThree.GF2n.Stroth80.Sec91b

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open Module
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conjSubgroup_sup95 (g : G) (A B' : Subgroup G) :
    conjSubgroup g (A ⊔ B') = conjSubgroup g A ⊔ conjSubgroup g B' :=
  Subgroup.map_sup _ _ _

theorem card_A2_95 (h34 : Stroth34Statement) (h91b : Stroth91bStatement) {hc : Ctx M Q Z B}
    {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r) :
    Nat.card ↥((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) =
      Nat.card Z ^ (n + 1) := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  obtain ⟨hVA₁, hA₁W, hVA₂, hA₂W, hsup, hinf, hcomm, -⟩ := isOppDecomp95 h34 h91b hs hr
  have hA₁eq : ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
      Vt M (LB M Q B) B Z t) = conjSubgroup r ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
      Vt M (LB M Q B) B Z t) := by
    rw [conjSubgroup_sup95, conjSubgroup_inf, QB_conj, sec9_conj_Wt_eq hc ht hrR,
      sec9_conj_Vt_eq hc ht hrR]
  have hcard12 : Nat.card ↥((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
      Vt M (LB M Q B) B Z t) = Nat.card ↥((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
      Vt M (LB M Q B) B Z t) := by
    rw [hA₁eq, card_conjSubgroup]
  have hnorm : ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
      Vt M (LB M Q B) B Z t) ≤ Subgroup.normalizer
      (((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t : Subgroup G) :
        Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun a ha b hb => ?_
    have hcb : ⁅a, b⁆ ∈ Vt M (LB M Q B) B Z t := hcomm a (hA₁W ha) b (hA₂W hb)
    have key : a * b * a⁻¹ = ⁅a, b⁆ * b := by
      rw [commutatorElement_def]
      group
    rw [key]
    exact Subgroup.mul_mem _ (hVA₂ hcb) hb
  have hprod := card_sup_mul_card_inf_of_le_normalizer hnorm
  have hsup' : ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) ⊔
      ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) =
      Wt Q (Vt M (LB M Q B) B Z t) := by rw [sup_comm]; exact hsup
  have hinf' : ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) ⊓
      ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) =
      Vt M (LB M Q B) B Z t := by rw [inf_comm]; exact hinf
  rw [hsup', hinf', hcard12, hs.card_W h34, hs.card_V] at hprod
  have hn3 := hs5.n_gt
  have e : Nat.card Z ^ (2 * n - 3) * Nat.card Z ^ 5 =
      Nat.card Z ^ (n + 1) * Nat.card Z ^ (n + 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [e] at hprod
  exact (Nat.mul_self_inj.mp hprod).symm

theorem rank95_le_six (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r)
    {z y : G} (hzM : z ∈ M) (hy : y ∈ N1 hc t) (hxL : z * y * z⁻¹ ∈ LB M Q B)
    (hxN : z * y * z⁻¹ ∉ hc.CN t) (hnA : ¬ IsTypeA2 M Q Z B t (z * y * z⁻¹)) : n ≤ 6 := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hyL : y ∈ LB M Q B := (Subgroup.mem_inf.mp hy).1
  have hq4 := hc.hyp.q4
  have hHP : ∀ w : G, w ∈ Wt Q (Vt M (LB M Q B) B Z t) →
      ⁅z * y * z⁻¹, w⁆ ∈ Vt M (LB M Q B) B Z t →
      w ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t :=
    fun w hw hxw => hp95 h34 h91b hs hr hxL hxN hnA hw hxw
  have hA2card := card_A2_95 h34 h91b hs hr
  obtain ⟨hVA₁, hA₁W, hVA₂, hA₂W, -⟩ := isOppDecomp95 h34 h91b hs hr
  obtain ⟨K, fK, finK, hK2, hnrm, ⟨C⟩⟩ := exists_coord95 h34 hs hr
  obtain ⟨w₀, -, -, -, -, -, hCentV⟩ := C.plane_facts hs hxL hxN
  obtain ⟨K', fK', finK', chK', γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ₀, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨φ, hφπ', hφker, hφadd, hφsemi⟩ := exists_actionHom_M hc.hyp h
  haveI : Finite M₀.E := Module.finite_of_finite K'
  have hKZ : Nat.card K' = Nat.card Z := h.card
  have hK2' : 1 < Nat.card K' := by rw [hKZ]; omega
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
  have hφα : ∀ (l : ↥(LB M Q B)) e, φ ⟨(l : G), hc.LB_le_M l.2⟩ e = α l e := by
    intro l e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    rw [← hφπ' ⟨(l : G), hc.LB_le_M l.2⟩ x hxQ, hαπ l x hxQ]
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
  have hyN : y ∈ hc.CN t := (Subgroup.mem_inf.mp hy).2
  set V := Vt M (LB M Q B) B Z t with hV
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hZW : Z ≤ Wt Q V := n12l3_Z_le_W hc t
  have hWQ : Wt Q V ≤ Q := inf_le_left
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
  have hVU : ¬ Vsub ≤ U := by
    intro hle
    apply sec9_notQB h34 hs
    intro v hv
    have h1 : M₀.π v ∈ U := hle ((hVsub_mem _).mpr (M₀.pi_mem_img hv (hVQ hv)))
    have h2 : M₀.π v ∈ M₀.img (Q ⊓ QB B) := (hUmem _).mp h1
    exact ((M₀.mem_img_iff (le_inf hZQ hc.Z_le_QB.1) (hVQ hv)).mp h2).2
  have hbV : b ∈ Vsub := (hVsub_mem b).mpr (M₀.img_mono (hc.B_le_Vt ht)
    ((hB b).mpr ⟨1, (one_smul K' b).symm⟩))
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
  have hg : ∀ e, (∀ v ∈ Vsub, M₀.B v e = 0) → α ⟨y, hyL⟩ e - e ∈ Vsub := by
    intro e he
    obtain ⟨a, haW, haQ, rfl⟩ := (hWimg e).mp he
    obtain ⟨hcQ, hπ⟩ := hcommπ ⟨y, hyL⟩ a haQ
    have hcV : ⁅y, a⁆ ∈ V := comm_CN_Wt_mem_Vt h91b hs hr hyN haW
    rw [← hπ]
    exact (hVsub_mem _).mpr (M₀.pi_mem_img hcV hcQ)
  have hlow := Siegel.finrank_fix_ge hQ hS hbV hVsubdim hVU hE ⟨y, hyL⟩ hg
  set x : G := z * y * z⁻¹ with hxdef
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  have hxM : x ∈ M := hc.LB_le_M hxL
  let Tx : M₀.E ≃ₗ[K'] M₀.E := α ⟨x, hxL⟩
  let Ty : M₀.E ≃ₗ[K'] M₀.E := α ⟨y, hyL⟩
  have hTV : ∀ v ∈ Vsub, Tx v ∈ Vsub := by
    intro v hv
    obtain ⟨a, haV, haQ, rfl⟩ := (hVsub_mem v).mp hv
    have h1 : x * a * x⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hxR) a).mp haV
    show α ⟨x, hxL⟩ (M₀.π a) ∈ Vsub
    rw [← hαπ ⟨x, hxL⟩ a haQ]
    exact (hVsub_mem _).mpr (M₀.pi_mem_img h1 (n12l3_normalizes_Q hc hxM haQ))
  let Ws : Submodule K' M₀.E := M₀.B.orthogonal Vsub
  let A : Submodule K' M₀.E := (U ⊓ Ws) ⊔ Vsub
  have hWsmem : ∀ e, e ∈ Ws ↔ ∀ v ∈ Vsub, M₀.B v e = 0 := fun e =>
    LinearMap.BilinForm.mem_orthogonal_iff
  have hn' : QB B ⊓ Wt Q V ≤ Subgroup.normalizer (V : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).2).2
  have hA : ∀ e, Tx e = e → (∀ v ∈ Vsub, M₀.B v e = 0) → e ∈ A := by
    intro e hTe hWe
    obtain ⟨a, haW, haQ, rfl⟩ := (hWimg e).mp hWe
    have hxaQ : x * a * x⁻¹ ∈ Q := n12l3_normalizes_Q hc hxM haQ
    have hπ : M₀.π (x * a * x⁻¹) = M₀.π a := by
      rw [hαπ ⟨x, hxL⟩ a haQ]
      exact hTe
    have hcomm : ⁅x, a⁆ ∈ Z := (M₀.comm_mem_iff haQ hxaQ).mpr hπ
    have haA2 := hHP a haW (hZV hcomm)
    obtain ⟨c, hcmem, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hn' haA2
    have hcW : c ∈ Wt Q V := (Subgroup.mem_inf.mp hcmem).2
    have hcQ : c ∈ Q := hWQ hcW
    have hvQ : v ∈ Q := hVQ hv
    rw [M₀.π_mul c hcQ v hvQ]
    refine Submodule.mem_sup.mpr ⟨M₀.π c, ⟨?_, ?_⟩, M₀.π v,
      (hVsub_mem _).mpr (M₀.pi_mem_img hv hvQ), rfl⟩
    · exact (hUmem _).mpr (M₀.pi_mem_img ⟨hcQ, (Subgroup.mem_inf.mp hcmem).1⟩ hcQ)
    · exact (hWsmem _).mpr ((hWimg _).mpr (M₀.pi_mem_img hcW hcQ))
  have hf1 : finrank K' ↥(LinearMap.ker ((Tx : M₀.E →ₗ[K'] M₀.E) - 1) ⊓ Vsub) ≤ 2 := by
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
    have hsub : ((LinearMap.ker ((Tx : M₀.E →ₗ[K'] M₀.E) - 1) ⊓ Vsub : Submodule K' M₀.E) :
        Set M₀.E) ⊆ ↑(M₀.img (CentMod Z V (Vt_le_normalizer hc t) x)) := by
      intro e he
      obtain ⟨hFe, hVe⟩ := he
      obtain ⟨a, haV, haQ, rfl⟩ := (hVsub_mem e).mp hVe
      have hTe : Tx (M₀.π a) = M₀.π a := by
        have := LinearMap.mem_ker.mp hFe
        simpa [sub_eq_zero] using this
      have hxaQ : x * a * x⁻¹ ∈ Q := n12l3_normalizes_Q hc hxM haQ
      have hπ : M₀.π (x * a * x⁻¹) = M₀.π a := by
        rw [hαπ ⟨x, hxL⟩ a haQ]
        exact hTe
      have hcomm : ⁅x, a⁆ ∈ Z := (M₀.comm_mem_iff haQ hxaQ).mpr hπ
      exact M₀.pi_mem_img (show a ∈ CentMod Z V (Vt_le_normalizer hc t) x from ⟨haV, hcomm⟩) haQ
    have hle : Nat.card ↥(LinearMap.ker ((Tx : M₀.E →ₗ[K'] M₀.E) - 1) ⊓ Vsub) ≤
        Nat.card ↥(M₀.img (CentMod Z V (Vt_le_normalizer hc t) x)) :=
      Nat.card_mono (Set.toFinite _) hsub
    rw [himg] at hle
    have h5 : Nat.card K' ^ finrank K' ↥(LinearMap.ker ((Tx : M₀.E →ₗ[K'] M₀.E) - 1) ⊓ Vsub) ≤
        Nat.card K' ^ 2 := by
      rw [← Module.natCard_eq_pow_finrank, hKZ]
      exact hle
    exact (Nat.pow_le_pow_iff_right hK2').mp h5
  have hAn : finrank K' A ≤ n := by
    have hA2le : Z ≤ (QB B ⊓ Wt Q V) ⊔ V := hZV.trans le_sup_right
    have hA2Q : (QB B ⊓ Wt Q V) ⊔ V ≤ Q := sup_le (inf_le_right.trans hWQ) hVQ
    have hcardA2 := M₀.card_eq hA2Q hA2le
    rw [hA2card] at hcardA2
    have himgA : Nat.card (M₀.img ((QB B ⊓ Wt Q V) ⊔ V)) = Nat.card Z ^ n := by
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← hcardA2]
      ring
    have hsub : (A : Set M₀.E) ⊆ ↑(M₀.img ((QB B ⊓ Wt Q V) ⊔ V)) := by
      intro e he
      obtain ⟨u', ⟨hu'U, hu'W⟩, v', hv', rfl⟩ := Submodule.mem_sup.mp he
      obtain ⟨c, hcQQB, hcQ, hcπ⟩ := (hUmem u').mp hu'U
      obtain ⟨v, hvV, hvQ, hvπ⟩ := (hVsub_mem v').mp hv'
      have hcW : c ∈ Wt Q V := by
        have h1 : M₀.π c ∈ M₀.img (Wt Q V) := by
          rw [hcπ]
          exact (hWimg u').mp ((hWsmem u').mp hu'W)
        exact (M₀.mem_img_iff hZW hcQ).mp h1
      have hcA : c * v ∈ (QB B ⊓ Wt Q V) ⊔ V :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨(Subgroup.mem_inf.mp hcQQB).2, hcW⟩)
          (Subgroup.mem_sup_right hvV)
      have e1 : u' + v' = M₀.π (c * v) := by rw [M₀.π_mul c hcQ v hvQ, hcπ, hvπ]
      rw [show (u' + v' : M₀.E) = M₀.π (c * v) from e1]
      exact M₀.pi_mem_img hcA (Q.mul_mem hcQ hvQ)
    have hle : Nat.card ↥A ≤ Nat.card ↥(M₀.img ((QB B ⊓ Wt Q V) ⊔ V)) :=
      Nat.card_mono (Set.toFinite _) hsub
    rw [himgA] at hle
    have h5 : Nat.card K' ^ finrank K' A ≤ Nat.card K' ^ n := by
      rw [← Module.natCard_eq_pow_finrank, hKZ]
      exact hle
    exact (Nat.pow_le_pow_iff_right hK2').mp h5
  have hup := finrank_fix_le_of_flag hQ hE hVsubdim hVV Tx (fun e => hαiso ⟨x, hxL⟩ e) hTV
    (A := A) le_sup_right hA hf1
  have hgz : z⁻¹ ∈ M := M.inv_mem hzM
  have hφinv' : ∀ e, φ ⟨z⁻¹, hgz⟩ (φ ⟨z, hzM⟩ e) = e := fun e => by
    have h1 : φ ⟨z⁻¹, hgz⟩ * φ ⟨z, hzM⟩ = 1 := by
      rw [← map_mul]
      have : (⟨z⁻¹, hgz⟩ * ⟨z, hzM⟩ : ↥M) = 1 := Subtype.ext (inv_mul_cancel z)
      rw [this, map_one]
    have := congrArg (fun f : Equiv.Perm M₀.E => f e) h1
    simpa using this
  have hφconj : ∀ e, Tx (φ ⟨z, hzM⟩ e) = φ ⟨z, hzM⟩ (Ty e) := by
    intro e
    have h1 : (⟨z * y * z⁻¹, hc.LB_le_M hxL⟩ : ↥M) =
        ⟨z, hzM⟩ * ⟨y, hc.LB_le_M hyL⟩ * ⟨z⁻¹, hgz⟩ := Subtype.ext rfl
    show α ⟨x, hxL⟩ (φ ⟨z, hzM⟩ e) = φ ⟨z, hzM⟩ (α ⟨y, hyL⟩ e)
    rw [← hφα ⟨x, hxL⟩, ← hφα ⟨y, hyL⟩]
    show φ ⟨z * y * z⁻¹, hc.LB_le_M hxL⟩ (φ ⟨z, hzM⟩ e) =
      φ ⟨z, hzM⟩ (φ ⟨y, hc.LB_le_M hyL⟩ e)
    rw [h1, map_mul, map_mul]
    show φ ⟨z, hzM⟩ (φ ⟨y, hc.LB_le_M hyL⟩ (φ ⟨z⁻¹, hgz⟩ (φ ⟨z, hzM⟩ e))) = _
    rw [hφinv']
  have hFy : ∀ e, e ∈ LinearMap.ker ((Ty : M₀.E →ₗ[K'] M₀.E) - 1) ↔ Ty e = e := fun e => by
    rw [LinearMap.mem_ker]
    simp [sub_eq_zero]
  have hFx : ∀ e, e ∈ LinearMap.ker ((Tx : M₀.E →ₗ[K'] M₀.E) - 1) ↔ Tx e = e := fun e => by
    rw [LinearMap.mem_ker]
    simp [sub_eq_zero]
  have hFcard : Nat.card ↥(LinearMap.ker ((Ty : M₀.E →ₗ[K'] M₀.E) - 1)) ≤
      Nat.card ↥(LinearMap.ker ((Tx : M₀.E →ₗ[K'] M₀.E) - 1)) := by
    refine Nat.card_le_card_of_injective
      (fun e => ⟨φ ⟨z, hzM⟩ e.1, by rw [hFx, hφconj, (hFy e.1).mp e.2]⟩) ?_
    intro e e' hee'
    have h1 : φ ⟨z, hzM⟩ e.1 = φ ⟨z, hzM⟩ e'.1 :=
      congrArg (fun p : ↥(LinearMap.ker ((Tx : M₀.E →ₗ[K'] M₀.E) - 1)) => p.1) hee'
    have h2 := congrArg (φ ⟨z⁻¹, hgz⟩) h1
    rw [hφinv', hφinv'] at h2
    exact Subtype.ext h2
  have hFcard' : finrank K' ↥(LinearMap.ker ((Ty : M₀.E →ₗ[K'] M₀.E) - 1)) ≤
      finrank K' ↥(LinearMap.ker ((Tx : M₀.E →ₗ[K'] M₀.E) - 1)) := by
    have h5 : Nat.card K' ^ finrank K' ↥(LinearMap.ker ((Ty : M₀.E →ₗ[K'] M₀.E) - 1)) ≤
        Nat.card K' ^ finrank K' ↥(LinearMap.ker ((Tx : M₀.E →ₗ[K'] M₀.E) - 1)) := by
      rw [← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank]
      exact hFcard
    exact (Nat.pow_le_pow_iff_right hK2').mp h5
  have e1 : finrank K' ↥(LinearMap.ker ((Ty : M₀.E →ₗ[K'] M₀.E) - 1)) =
      finrank K' ↥(LinearMap.ker ((α ⟨y, hyL⟩ : M₀.E →ₗ[K'] M₀.E) - 1)) := rfl
  omega

end HS9

end CFSG.RankThree.GF2n.Stroth80
