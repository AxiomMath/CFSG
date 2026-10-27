module

public import CFSG.RankThree.GF2n.Stroth80.Core4Coset
public import CFSG.RankThree.GF2n.Stroth80.Sec101FlagLB
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix Pointwise

section LinAlg

theorem psi_surj_of_card {K W S : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    [Module.Finite K W] [Group S] [Finite S] (ψ : S → (W →ₗ[K] K))
    (hmul : ∀ a b, ψ (a * b) = ψ a + ψ b) (hinj : ∀ a, ψ a = 0 → a = 1)
    (Sg : Submodule K W) (hvan : ∀ a, ∀ v ∈ Sg, ψ a v = 0) {n k : ℕ}
    (hn : Module.finrank K W = n) (hk : k ≤ Module.finrank K Sg)
    (hcard : Nat.card K ^ (n - k) ≤ Nat.card S) (f : W →ₗ[K] K) (hf : ∀ v ∈ Sg, f v = 0) :
    ∃ a : S, ψ a = f := by
  classical
  have hψ1 : ψ 1 = 0 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hψinv : ∀ a, ψ a⁻¹ = - ψ a := fun a => by
    have := hmul a a⁻¹
    rw [mul_inv_cancel, hψ1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have : ψ (a * b⁻¹) = 0 := by rw [hmul, hψinv, hab, add_neg_cancel]
    have h1 := hinj _ this
    exact mul_inv_eq_one.mp h1
  let Ann : Submodule K (Module.Dual K W) := Sg.dualAnnihilator
  have hAnn : ∀ f, f ∈ Ann ↔ ∀ v ∈ Sg, f v = 0 := fun f => by
    simp only [Ann, Submodule.mem_dualAnnihilator]
  have hdim : Module.finrank K Sg + Module.finrank K Ann = n := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq Sg
    rw [hn] at this
    exact this
  have hAnncard : Nat.card Ann = Nat.card K ^ (n - Module.finrank K Sg) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := Ann)]
    congr 1
    omega
  have hq : 0 < Nat.card K := Nat.card_pos
  have hq1 : 1 ≤ Nat.card K := hq
  have hAnnle : Nat.card Ann ≤ Nat.card K ^ (n - k) := by
    rw [hAnncard]
    exact Nat.pow_le_pow_right hq (by omega)
  let Ψ : S → Ann := fun a => ⟨ψ a, (hAnn _).mpr (hvan a)⟩
  have hΨinj : Function.Injective Ψ := fun a b hab => hψinj (congrArg Subtype.val hab)
  have hfinAnn : Finite Ann := by
    haveI : Module.Finite K Ann := inferInstance
    exact Module.finite_of_finite K
  have hle : Nat.card Ann ≤ Nat.card S := hAnnle.trans hcard
  have hbij : Function.Bijective Ψ := hΨinj.bijective_of_nat_card_le hle
  obtain ⟨a', ha'⟩ := hbij.2 ⟨f, (hAnn _).mpr hf⟩
  exact ⟨a', congrArg Subtype.val ha'⟩

end LinAlg

section FlagLemmas

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel QF V K γ} {b : M₀.E} {W : Submodule K M₀.E}
  {Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E)} {f₀ : M₀.E}

theorem FlagData.psi_mul (hΛ : FlagData M₀ b W Λ) (hf₀ : M₀.B f₀ b = 1)
    {T S : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) (hS : S ∈ Λ) {d : M₀.E} (hd : d ∈ W) :
    flagPsi M₀ f₀ (T * S) d = flagPsi M₀ f₀ T d + flagPsi M₀ f₀ S d := by
  have e1 : S d - d = flagPsi M₀ f₀ S d • b := hΛ.sub_eq hf₀ hS hd
  have e2 : (T * S) d - d = T (S d - d) + (T d - d) := by
    show T (S d) - d = T (S d - d) + (T d - d)
    rw [map_sub]
    abel
  have e3 : T (S d - d) = flagPsi M₀ f₀ S d • b := by
    rw [e1, map_smul, hΛ.fix T hT]
  have h3 : flagPsi M₀ f₀ (T * S) d = M₀.B f₀ ((T * S) d - d) := rfl
  rw [h3, e2, e3, map_add, map_smul, hf₀, smul_eq_mul, mul_one, add_comm]
  rfl

theorem FlagData.psi_conj (hΛ : FlagData M₀ b W Λ) (hf₀ : M₀.B f₀ b = 1)
    {g T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) (hgb : g b = b) (hgW : ∀ x ∈ W, g⁻¹ x ∈ W)
    {d : M₀.E} (hd : d ∈ W) :
    flagPsi M₀ f₀ (g * T * g⁻¹) d = flagPsi M₀ f₀ T (g⁻¹ d) := by
  have e1 : T (g⁻¹ d) - g⁻¹ d = flagPsi M₀ f₀ T (g⁻¹ d) • b := hΛ.sub_eq hf₀ hT (hgW d hd)
  have e2 : (g * T * g⁻¹) d - d = g (T (g⁻¹ d) - g⁻¹ d) := by
    have hgd : g (g⁻¹ d) = d := g.apply_symm_apply d
    show g (T (g⁻¹ d)) - d = g (T (g⁻¹ d) - g⁻¹ d)
    rw [map_sub, hgd]
  have h3 : flagPsi M₀ f₀ (g * T * g⁻¹) d = M₀.B f₀ ((g * T * g⁻¹) d - d) := rfl
  rw [h3, e2, e1, map_smul, hgb, map_smul, hf₀, smul_eq_mul, mul_one]

end FlagLemmas

section Act

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

@[expose] noncomputable def GlobalModelAction.act (Pk : GlobalModelAction M Q Z K γ M₀) (g : G) :
    M₀.E ≃ₗ[K] M₀.E := by
  classical
  exact if h : g ∈ H0 M Z then Pk.φ ⟨g, h⟩ else 1

theorem GlobalModelAction.act_of_mem (Pk : GlobalModelAction M Q Z K γ M₀) {g : G}
    (hg : g ∈ H0 M Z) : Pk.act g = Pk.φ ⟨g, hg⟩ := by
  simp [GlobalModelAction.act, hg]

theorem GlobalModelAction.act_mul (Pk : GlobalModelAction M Q Z K γ M₀) {g h : G}
    (hg : g ∈ H0 M Z) (hh : h ∈ H0 M Z) : Pk.act (g * h) = Pk.act g * Pk.act h := by
  rw [Pk.act_of_mem hg, Pk.act_of_mem hh, Pk.act_of_mem ((H0 M Z).mul_mem hg hh)]
  exact map_mul Pk.φ ⟨g, hg⟩ ⟨h, hh⟩

theorem GlobalModelAction.act_inv (Pk : GlobalModelAction M Q Z K γ M₀) {g : G}
    (hg : g ∈ H0 M Z) : Pk.act g⁻¹ = (Pk.act g)⁻¹ := by
  rw [Pk.act_of_mem hg, Pk.act_of_mem ((H0 M Z).inv_mem hg)]
  exact map_inv Pk.φ ⟨g, hg⟩

theorem GlobalModelAction.act_pi (Pk : GlobalModelAction M Q Z K γ M₀) {g x : G}
    (hg : g ∈ H0 M Z) (hx : x ∈ Q) : M₀.π (g * x * g⁻¹) = Pk.act g (M₀.π x) := by
  rw [Pk.act_of_mem hg]
  exact Pk.hφπ ⟨g, hg⟩ x hx

theorem GlobalModelAction.act_eq_one_iff (Pk : GlobalModelAction M Q Z K γ M₀) {g : G}
    (hg : g ∈ H0 M Z) : Pk.act g = 1 ↔ g ∈ Q := by
  rw [Pk.act_of_mem hg]
  exact Pk.hφker ⟨g, hg⟩

theorem GlobalModelAction.act_fix (Pk : GlobalModelAction M Q Z K γ M₀) {g u : G}
    (hg : g ∈ H0 M Z) (hQn : M ≤ Subgroup.normalizer (Q : Set G)) (hu : u ∈ Q)
    (hgu : ⁅g, u⁆ ∈ Z) : Pk.act g (M₀.π u) = M₀.π u := by
  rw [← Pk.act_pi hg hu]
  have hgu' : g * u * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQn hg.1) u).mp hu
  exact (M₀.comm_mem_iff hu hgu').mp hgu

end Act

section Core

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem conj_le_sup_of_mem_CN (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {r : G} (hrR : r ∈ Rt M (LB M Q B) t) {x : G} (hx : x ∈ hc.CN t) :
    conjSubgroup x (conjSubgroup r B) ≤ Z ⊔ conjSubgroup r B := by
  intro y hy
  have hα : x⁻¹ * y * x ∈ conjSubgroup r B := mem_conjSubgroup.mp hy
  have hAV : x⁻¹ * y * x ∈ Vt M (LB M Q B) B Z t :=
    (hc.conj_Rt_le_Vt hs.toSec5.mem hrR) (Subgroup.mem_sup_left hα)
  have hxcomm : ⁅x, x⁻¹ * y * x⁆ ∈ Z := (Ctx.mem_CN.mp hx).2 _ hAV
  have e : y = ⁅x, x⁻¹ * y * x⁆ * (x⁻¹ * y * x) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxcomm) (Subgroup.mem_sup_right hα)

theorem conj_LA_eq_of_mem_CN (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {r : G} (hrR : r ∈ Rt M (LB M Q B) t) {x : G} (hx : x ∈ hc.CN t) :
    conjSubgroup x (LB M Q (conjSubgroup r B)) = LB M Q (conjSubgroup r B) := by
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hxM : x ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hx).1
  refine (hc.conj_of_mem hrM).conj_LB_eq_of_le_sup_Z hxM ?_
  rw [sup_comm]
  exact conj_le_sup_of_mem_CN hc hs hrR hx

theorem act_fix_line (Pk : GlobalModelAction M Q Z K γ M₀) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {r : G} (hrR : r ∈ Rt M (LB M Q B) t) {x : G}
    (hxL : x ∈ LB M Q B) (hx : x ∈ hc.CN t) {a : M₀.E} (haA : a ∈ M₀.img (conjSubgroup r B)) :
    Pk.act x a = a := by
  obtain ⟨u, huA, huQ, rfl⟩ := haA
  have hAV : u ∈ Vt M (LB M Q B) B Z t :=
    (hc.conj_Rt_le_Vt hs.toSec5.mem hrR) (Subgroup.mem_sup_left huA)
  exact Pk.act_fix (hc.LB_le_H0_cb hxL) hc.hyp.Q_normal.2 huQ ((Ctx.mem_CN.mp hx).2 u hAV)

theorem act_mem_img_QInfQB (Pk : GlobalModelAction M Q Z K γ M₀) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec9Hyp hc n t) {r : G} (hrR : r ∈ Rt M (LB M Q B) t) {x : G}
    (hxL : x ∈ LB M Q B) (hx : x ∈ hc.CN t) {e : M₀.E}
    (he : e ∈ M₀.img (Q ⊓ QB (conjSubgroup r B))) :
    Pk.act x e ∈ M₀.img (Q ⊓ QB (conjSubgroup r B)) := by
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hcA : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hxM : x ∈ M := hc.LB_le_M hxL
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  obtain ⟨w, hwS, hwQ, rfl⟩ := he
  obtain ⟨p, hpQ, hp⟩ := hcA.exists_conj_of_le_ZB (hcA.conj_of_mem hxM)
    (conj_le_sup_of_mem_CN hc hs hrR hx)
  have hQB : conjSubgroup x (QB (conjSubgroup r B)) = conjSubgroup p (QB (conjSubgroup r B)) := by
    rw [← QB_conj, ← QB_conj, hp]
  rw [← Pk.act_pi (hc.LB_le_H0_cb hxL) hwQ]
  have hxw : x * w * x⁻¹ ∈ conjSubgroup p (QB (conjSubgroup r B)) := by
    rw [← hQB]
    exact ⟨w, hwS.2, by simp [MulAut.conj_apply]⟩
  have hxwQ : x * w * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQn hxM) w).mp hwQ
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hpQ
  have hw'B : p⁻¹ * (x * w * x⁻¹) * p ∈ QB (conjSubgroup r B) := mem_conjSubgroup.mp hxw
  have hw'Q : p⁻¹ * (x * w * x⁻¹) * p ∈ Q :=
    Q.mul_mem (Q.mul_mem (Q.inv_mem hpQ) hxwQ) hpQ
  have hπ : M₀.π (x * w * x⁻¹) = M₀.π (p⁻¹ * (x * w * x⁻¹) * p) := by
    have h1 := M₀.pi_conj_self hpQ hw'Q
    rw [show p * (p⁻¹ * (x * w * x⁻¹) * p) * p⁻¹ = x * w * x⁻¹ by group] at h1
    exact h1
  rw [hπ]
  exact M₀.pi_mem_img ⟨hw'Q, hw'B⟩ hw'Q

theorem conj_CN_eq_of_mem_Rt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) : conjSubgroup r (hc.CN t) = hc.CN t :=
  HS9.conj_eq_of_le (HS9.conj_le_of_forall fun x hx => hc.CN_conj_mem ht hr hx)

theorem LA_inf_CN_eq (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) :
    LB M Q (conjSubgroup r B) ⊓ hc.CN t = conjSubgroup r (LB M Q B ⊓ hc.CN t) := by
  rw [conjSubgroup_inf, hc.LB_conj (hc.Rt_le_M t hr), conj_CN_eq_of_mem_Rt hc ht hr]

theorem relIndex_Q_LA_inf_CN (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {r : G} (hr : r ∈ Rt M (LB M Q B) t) :
    Q.relIndex (LB M Q (conjSubgroup r B) ⊓ hc.CN t) = Nat.card Z ^ (n - 3) := by
  rw [LA_inf_CN_eq hc hs.toSec5.mem hr, ← HS9.relIndex_Q_LB_inf_CN h34 hc hs]
  have h3 := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj r).toMonoidHom)
    Q (LB M Q B ⊓ hc.CN t) (MulAut.conj r).injective
  have e1 : Q.map (MulAut.conj r).toMonoidHom = Q := hc.conj_Q_eq (hc.Rt_le_M t hr)
  rw [e1] at h3
  exact h3

theorem card_img_Vt_inf_QB_conj (Pk : GlobalModelAction M Q Z K γ M₀) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec9Hyp hc n t) (h91 : Step91OrderVQBStatement) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) :
    Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B))) = Nat.card K ^ 3 := by
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcA : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hV4 := h91 G M Q Z B hc n t hs _ rfl
  have hVr : conjSubgroup r (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.toSec5.mem hr)
  have hset : Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B) =
      conjSubgroup r (Vt M (LB M Q B) B Z t ⊓ QB B) := by
    rw [conjSubgroup_inf, hVr, QB_conj]
  have hcard4 : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B)) = Nat.card Z ^ 4 := by
    rw [hset, card_conjSubgroup, hV4]
  have hZS : Z ≤ Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B) :=
    le_inf sec39_Z_le_Vt hcA.Z_le_QB.1
  have hSQ : Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B) ≤ Q :=
    inf_le_left.trans (hc.Vt_le_Q t)
  have h := M₀.card_eq hSQ hZS
  rw [hcard4] at h
  have hZK : Nat.card Z = Nat.card K := Pk.h.card.symm
  rw [hZK] at h
  have hpos : 0 < Nat.card K := Nat.card_pos
  have h4 : Nat.card K ^ 4 = Nat.card K * Nat.card K ^ 3 := by ring
  rw [h4] at h
  exact (Nat.eq_of_mul_eq_mul_left hpos h).symm

theorem act_fix_img_Vt (Pk : GlobalModelAction M Q Z K γ M₀) (hc : Ctx M Q Z B) {t g : G}
    (hgH : g ∈ H0 M Z) (hg : g ∈ hc.CN t) {e : M₀.E}
    (he : e ∈ M₀.img (Vt M (LB M Q B) B Z t)) : Pk.act g e = e := by
  obtain ⟨w, hwV, hwQ, rfl⟩ := he
  exact Pk.act_fix hgH hc.hyp.Q_normal.2 hwQ ((Ctx.mem_CN.mp hg).2 w hwV)

theorem card_phi_image (Pk : GlobalModelAction M Q Z K γ M₀) {H : Subgroup G} (hQH : Q ≤ H)
    (hHH0 : H ≤ H0 M Z) :
    Nat.card ↥((H.subgroupOf (H0 M Z)).map Pk.φ) = Q.relIndex H := by
  let ΦT : ↥H →* (M₀.E ≃ₗ[K] M₀.E) := Pk.φ.comp (Subgroup.inclusion hHH0)
  have hrange : ΦT.range = (H.subgroupOf (H0 M Z)).map Pk.φ := by
    ext T
    simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g, hHH0 g.2⟩, g.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  have hker : ΦT.ker = Q.subgroupOf H := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact Pk.hφker (Subgroup.inclusion hHH0 g)
  have h1 : Nat.card ΦT.ker = Nat.card Q := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hcardT : Nat.card H = Nat.card Q * Nat.card ΦT.range := by
    rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have h2 := Subgroup.relIndex_mul_card (H := Q) (K := H)
  rw [inf_of_le_left hQH, hcardT] at h2
  rw [← hrange]
  exact Nat.eq_of_mul_eq_mul_left hQpos (by rw [mul_comm] at h2; exact h2.symm)

theorem exists_act_psi_eq (Pk : GlobalModelAction M Q Z K γ M₀) (h34 : Stroth34Statement)
    (h91 : Step91OrderVQBStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {r : G} (hrR : r ∈ Rt M (LB M Q B) t) {a f₀ : M₀.E}
    (hFD : FlagData M₀ a (imgQInfQB M₀ (conjSubgroup r B)) (Pk.lam (conjSubgroup r B)))
    (hfaith : ∀ T ∈ Pk.lam (conjSubgroup r B), (∀ e ∈ imgQInfQB M₀ (conjSubgroup r B), T e = e) →
      T = 1)
    (hf₀ : M₀.B f₀ a = 1) :
    ∀ f : ↥(imgQInfQB M₀ (conjSubgroup r B)) →ₗ[K] K,
      (∀ e : ↥(imgQInfQB M₀ (conjSubgroup r B)),
        (e : M₀.E) ∈ M₀.img (Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B)) → f e = 0) →
      ∃ g ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t,
        flagPsiLin M₀ (imgQInfQB M₀ (conjSubgroup r B)) f₀ (Pk.act g) = f := by
  classical
  have hs5 := hs.toSec5
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  set A := conjSubgroup r B with hAdef
  have hcA : Ctx M Q Z A := hc.conj_of_mem hrM
  have hnoA : NoA2 Q Z (LB M Q A) := hc.noA2_conj hs5.noA2 hrM
  set W := imgQInfQB M₀ A with hWdef
  set TA : Subgroup G := LB M Q A ⊓ hc.CN t with hTAdef
  have hLAH0 : LB M Q A ≤ H0 M Z := hcA.LB_le_H0_cb
  have hTAH0 : TA ≤ H0 M Z := inf_le_left.trans hLAH0
  have hQLA : Q ≤ LB M Q A := le_sup_left
  have hQTA : Q ≤ TA := le_inf hQLA (sec9_Q_le_CN hc hs5.mem)
  obtain ⟨hWn, hWp, hWs⟩ := hcA.imgQInfQB_lagr hs5.width hs5.n_gt hnoA Pk.h
  have hWmem := hcA.mem_imgQInfQB_iff hs5.width hs5.n_gt hnoA Pk.h
  haveI : Finite (Pk.lam A) := Pk.finite_lam A
  let Ssub : Subgroup (M₀.E ≃ₗ[K] M₀.E) := (TA.subgroupOf (H0 M Z)).map Pk.φ
  have hSmem : ∀ T, T ∈ Ssub ↔ ∃ g ∈ TA, Pk.act g = T := by
    intro T
    simp only [Ssub, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, Pk.act_of_mem m.2⟩
    · rintro ⟨g, hgT, rfl⟩
      exact ⟨⟨g, hTAH0 hgT⟩, hgT, (Pk.act_of_mem (hTAH0 hgT)).symm⟩
  have hSΛ : Ssub ≤ Pk.lam A := by
    intro T hT
    obtain ⟨g, hgT, rfl⟩ := (hSmem T).mp hT
    rw [Pk.act_of_mem (hTAH0 hgT)]
    exact (Pk.phi_mem_lam_iff ⟨g, hTAH0 hgT⟩).mpr hgT.1
  haveI : Finite Ssub := Finite.of_injective (Subgroup.inclusion hSΛ)
    (Subgroup.inclusion_injective hSΛ)
  have hq : 1 < Nat.card K := by
    rw [Pk.h.card]
    have := hc.hyp.q4
    omega
  have hScard : Nat.card Ssub = Nat.card K ^ (n - 3) := by
    have hrel : Q.relIndex TA = Nat.card Z ^ (n - 3) := relIndex_Q_LA_inf_CN h34 hc hs hrR
    rw [card_phi_image Pk hQTA hTAH0, hrel, ← Pk.h.card]
  let S₀ : Set M₀.E := ((M₀.img (Vt M (LB M Q B) B Z t ⊓ QB A) : AddSubgroup M₀.E) : Set M₀.E)
  let Sg : Submodule K W := Submodule.span K {v : W | (v : M₀.E) ∈ S₀}
  have hS₀W : ∀ e ∈ S₀, e ∈ W := by
    intro e he
    refine (hWmem e).mpr (M₀.img_mono ?_ he)
    exact inf_le_inf_right _ ((hc.Vt_le_Q t))
  have hψ_ker : ∀ T : Ssub, ∀ v ∈ Sg, flagPsiLin M₀ W f₀ T.1 v = 0 := by
    intro T v hv
    obtain ⟨g, hgT, hgeq⟩ := (hSmem T.1).mp T.2
    have hS₀ker : {v : W | (v : M₀.E) ∈ S₀} ⊆ LinearMap.ker (flagPsiLin M₀ W f₀ T.1) := by
      intro v hv0
      have hfix : T.1 (v : M₀.E) = v := by
        rw [← hgeq]
        exact act_fix_img_Vt Pk hc (hTAH0 hgT) hgT.2 (M₀.img_mono inf_le_left hv0)
      rw [SetLike.mem_coe, LinearMap.mem_ker, flagPsiLin_apply]
      simp [flagPsi, hfix]
    exact LinearMap.mem_ker.mp (Submodule.span_le.mpr hS₀ker hv)
  have hψ_mul : ∀ T T' : Ssub, flagPsiLin M₀ W f₀ (T * T').1 =
      flagPsiLin M₀ W f₀ T.1 + flagPsiLin M₀ W f₀ T'.1 := by
    intro T T'
    refine LinearMap.ext fun d => ?_
    simp only [flagPsiLin_apply, LinearMap.add_apply]
    exact hFD.psi_mul hf₀ (hSΛ T.2) (hSΛ T'.2) d.2
  have hψ_inj : ∀ T : Ssub, flagPsiLin M₀ W f₀ T.1 = 0 → T = 1 := by
    intro T hT
    refine Subtype.ext (hfaith T.1 (hSΛ T.2) fun e he => ?_)
    have h1 := hFD.sub_eq hf₀ (hSΛ T.2) he
    have h2 : flagPsi M₀ f₀ T.1 e = 0 := by
      have := congrArg (fun F => F ⟨e, he⟩) hT
      simpa [flagPsiLin_apply] using this
    rw [h2, zero_smul] at h1
    exact sub_eq_zero.mp h1
  have hSgk : 3 ≤ Module.finrank K Sg := by
    have hcard3 := card_img_Vt_inf_QB_conj Pk hc hs h91 hrR
    let ι : ↥(M₀.img (Vt M (LB M Q B) B Z t ⊓ QB A)) → Sg := fun e =>
      ⟨⟨e.1, hS₀W e.1 e.2⟩, Submodule.subset_span e.2⟩
    have hι : Function.Injective ι := fun e e' h => by
      apply Subtype.ext
      have := congrArg (fun z : Sg => z.1.1) h
      exact this
    haveI : Finite Sg := Module.finite_of_finite K
    have h1 := Nat.card_le_card_of_injective ι hι
    rw [hcard3, Module.natCard_eq_pow_finrank (K := K) (V := Sg)] at h1
    exact (Nat.pow_le_pow_iff_right hq).mp h1
  intro f hf
  have hfSg : ∀ v ∈ Sg, f v = 0 := by
    have hS₀f : {v : W | (v : M₀.E) ∈ S₀} ⊆ LinearMap.ker f := fun v hv0 =>
      LinearMap.mem_ker.mpr (hf v hv0)
    exact fun v hv => LinearMap.mem_ker.mp (Submodule.span_le.mpr hS₀f hv)
  obtain ⟨a', ha'⟩ := psi_surj_of_card (K := K) (W := W)
    (fun T : Ssub => flagPsiLin M₀ W f₀ T.1) hψ_mul hψ_inj Sg hψ_ker hWn hSgk
    (by rw [hScard]) f hfSg
  obtain ⟨g', hg'T, hg'eq⟩ := (hSmem a'.1).mp a'.2
  refine ⟨g', hg'T, ?_⟩
  rw [hg'eq]
  exact ha'

theorem exists_smul_psi (Pk : GlobalModelAction M Q Z K γ M₀) (h34 : Stroth34Statement)
    (h91 : Step91OrderVQBStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {r : G} (hrR : r ∈ Rt M (LB M Q B) t) {a f₀ : M₀.E}
    (hFD : FlagData M₀ a (imgQInfQB M₀ (conjSubgroup r B)) (Pk.lam (conjSubgroup r B)))
    (hfaith : ∀ T ∈ Pk.lam (conjSubgroup r B), (∀ e ∈ imgQInfQB M₀ (conjSubgroup r B), T e = e) →
      T = 1)
    (hf₀ : M₀.B f₀ a = 1) :
    ∀ g ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, ∀ c : K,
      ∃ g' ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t,
        flagPsiLin M₀ (imgQInfQB M₀ (conjSubgroup r B)) f₀ (Pk.act g') =
          c • flagPsiLin M₀ (imgQInfQB M₀ (conjSubgroup r B)) f₀ (Pk.act g) := by
  intro g hg c
  refine exists_act_psi_eq Pk h34 h91 hc hs hrR hFD hfaith hf₀ _ (fun e he => ?_)
  have hgH0 : g ∈ H0 M Z := (hc.conj_of_mem (hc.Rt_le_M t hrR)).LB_le_H0_cb hg.1
  have hfix : Pk.act g (e : M₀.E) = e :=
    act_fix_img_Vt Pk hc hgH0 hg.2 (M₀.img_mono inf_le_left he)
  simp [flagPsiLin_apply, flagPsi, hfix]

theorem flagPsi_comm_apply (Pk : GlobalModelAction M Q Z K γ M₀) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec9Hyp hc n t) {r : G} (hrR : r ∈ Rt M (LB M Q B) t) {a f₀ : M₀.E}
    (hFD : FlagData M₀ a (imgQInfQB M₀ (conjSubgroup r B)) (Pk.lam (conjSubgroup r B)))
    (hf₀ : M₀.B f₀ a = 1) (haA : a ∈ M₀.img (conjSubgroup r B)) {x y : G}
    (hx : x ∈ LB M Q B ⊓ hc.CN t) (hy : y ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t) {d : M₀.E}
    (hd : d ∈ imgQInfQB M₀ (conjSubgroup r B)) :
    flagPsi M₀ f₀ (Pk.act ⁅x, y⁆) d = flagPsi M₀ f₀ (Pk.act y) ((Pk.act x)⁻¹ d - d) := by
  classical
  have hs5 := hs.toSec5
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  set A := conjSubgroup r B with hAdef
  have hcA : Ctx M Q Z A := hc.conj_of_mem hrM
  have hnoA : NoA2 Q Z (LB M Q A) := hc.noA2_conj hs5.noA2 hrM
  have hLBH0 : LB M Q B ≤ H0 M Z := hc.LB_le_H0_cb
  have hLAH0 : LB M Q A ≤ H0 M Z := hcA.LB_le_H0_cb
  have hWmem := hcA.mem_imgQInfQB_iff hs5.width hs5.n_gt hnoA Pk.h
  have hxL : x ∈ LB M Q B := hx.1
  have hxN : x ∈ hc.CN t := hx.2
  have hxH0 : x ∈ H0 M Z := hLBH0 hxL
  have hxinv : x⁻¹ ∈ LB M Q B ⊓ hc.CN t := (LB M Q B ⊓ hc.CN t).inv_mem hx
  have hξa : Pk.act x a = a := act_fix_line Pk hc hs hrR hxL hxN haA
  have hξinv : Pk.act x⁻¹ = (Pk.act x)⁻¹ := Pk.act_inv hxH0
  have hξinvW : ∀ e ∈ imgQInfQB M₀ A, (Pk.act x)⁻¹ e ∈ imgQInfQB M₀ A := fun e he => by
    rw [← hξinv]
    exact (hWmem _).mpr (act_mem_img_QInfQB Pk hc hs hrR hxinv.1 hxinv.2 ((hWmem e).mp he))
  have hxy : x * y * x⁻¹ ∈ LB M Q A := by
    have h1 : x * y * x⁻¹ ∈ conjSubgroup x (LB M Q A) := ⟨y, hy.1, by simp [MulAut.conj_apply]⟩
    rwa [conj_LA_eq_of_mem_CN hc hs hrR hxN] at h1
  have hlam : ∀ g ∈ LB M Q A, Pk.act g ∈ Pk.lam A := fun g hg => by
    rw [Pk.act_of_mem (hLAH0 hg)]
    exact (Pk.phi_mem_lam_iff ⟨g, hLAH0 hg⟩).mpr hg
  have hyH0 : y ∈ H0 M Z := hLAH0 hy.1
  have hxyH0 : x * y * x⁻¹ ∈ H0 M Z :=
    (H0 M Z).mul_mem ((H0 M Z).mul_mem hxH0 hyH0) ((H0 M Z).inv_mem hxH0)
  have hcx : Pk.act ⁅x, y⁆ = (Pk.act x * Pk.act y * (Pk.act x)⁻¹) * (Pk.act y)⁻¹ := by
    have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by rw [commutatorElement_def]
    rw [e, Pk.act_mul hxyH0 ((H0 M Z).inv_mem hyH0), Pk.act_mul ((H0 M Z).mul_mem hxH0 hyH0)
      ((H0 M Z).inv_mem hxH0), Pk.act_mul hxH0 hyH0, Pk.act_inv hxH0, Pk.act_inv hyH0]
  have hT : Pk.act y ∈ Pk.lam A := hlam y hy.1
  have hT₁ : Pk.act x * Pk.act y * (Pk.act x)⁻¹ ∈ Pk.lam A := by
    have := hlam _ hxy
    rwa [Pk.act_mul ((H0 M Z).mul_mem hxH0 hyH0) ((H0 M Z).inv_mem hxH0),
      Pk.act_mul hxH0 hyH0, Pk.act_inv hxH0] at this
  have hpsi1 : ∀ d : M₀.E, flagPsi M₀ f₀ (1 : M₀.E ≃ₗ[K] M₀.E) d = 0 := fun d => by
    simp [flagPsi]
  rw [hcx, hFD.psi_mul hf₀ hT₁ ((Pk.lam A).inv_mem hT) hd,
    hFD.psi_conj hf₀ hT hξa hξinvW hd]
  have hinv : flagPsi M₀ f₀ (Pk.act y)⁻¹ d = - flagPsi M₀ f₀ (Pk.act y) d := by
    have h := hFD.psi_mul hf₀ hT ((Pk.lam A).inv_mem hT) hd
    rw [mul_inv_cancel, hpsi1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  rw [hinv]
  simp only [flagPsi, map_sub]
  ring

theorem coset_core (Pk : GlobalModelAction M Q Z K γ M₀) (h34 : Stroth34Statement)
    (h91 : Step91OrderVQBStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {r : G} (hrR : r ∈ Rt M (LB M Q B) t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hcen : HS9.Centre95 hc t Z0)
    (hNN : ⁅hc.CN t, hc.CN t⁆ ≤ Z0) (hZ0A : Z0 ≤ LB M Q (conjSubgroup r B)) {x : G}
    (hx : x ∈ LB M Q B ⊓ hc.CN t) {b : G} (hb : b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t)
    (hxb : ⁅x, b⁆ ∉ Q) (c : G) (hc0 : c ∈ Z0) :
    ∃ y ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, ⁅x, y⁆ * c⁻¹ ∈ Q := by
  classical
  have hs5 := hs.toSec5
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  set A := conjSubgroup r B with hAdef
  have hcA : Ctx M Q Z A := hc.conj_of_mem hrM
  have hnoA : NoA2 Q Z (LB M Q A) := hc.noA2_conj hs5.noA2 hrM
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hLBH0 : LB M Q B ≤ H0 M Z := hc.LB_le_H0_cb
  have hLAH0 : LB M Q A ≤ H0 M Z := hcA.LB_le_H0_cb
  obtain ⟨a, ha0, -, haL, -, -⟩ := hcA.dictB Pk.h
  obtain ⟨hFD, hfaith, -⟩ := hcA.flagData_lam hs5.width hs5.n_gt hnoA Pk ha0 haL
  set W := imgQInfQB M₀ A with hWdef
  have hWmem := hcA.mem_imgQInfQB_iff hs5.width hs5.n_gt hnoA Pk.h
  obtain ⟨f₁, hf₁⟩ := Tim79.QuadModel.exists_B_ne_zero ha0
  have hf₀ : M₀.B ((M₀.B f₁ a)⁻¹ • f₁) a = 1 := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₁]
  set f₀ := (M₀.B f₁ a)⁻¹ • f₁ with hf₀def
  have haA : a ∈ M₀.img A := (haL a).mpr ⟨1, (one_smul K a).symm⟩
  have hxL : x ∈ LB M Q B := hx.1
  have hxN : x ∈ hc.CN t := hx.2
  have hxM : x ∈ M := hc.LB_le_M hxL
  have hxH0 : x ∈ H0 M Z := hLBH0 hxL
  have hxinv : x⁻¹ ∈ LB M Q B ⊓ hc.CN t := (LB M Q B ⊓ hc.CN t).inv_mem hx
  have hξinv : Pk.act x⁻¹ = (Pk.act x)⁻¹ := Pk.act_inv hxH0
  have hξinvW : ∀ e ∈ W, (Pk.act x)⁻¹ e ∈ W := fun e he => by
    rw [← hξinv]
    exact (hWmem _).mpr (act_mem_img_QInfQB Pk hc hs hrR hxinv.1 hxinv.2 ((hWmem e).mp he))
  let ξi : M₀.E →ₗ[K] M₀.E := ((Pk.act x)⁻¹ : M₀.E ≃ₗ[K] M₀.E)
  let Dmap : M₀.E →ₗ[K] M₀.E := ξi - LinearMap.id
  have hD : ∀ d ∈ W, Dmap d ∈ W := fun d hd => by
    simpa [Dmap, ξi] using W.sub_mem (hξinvW d hd) hd
  let Dlin : W →ₗ[K] W := Dmap.restrict hD
  have hDlin : ∀ d : W, ((Dlin d : W) : M₀.E) = (Pk.act x)⁻¹ d - d := fun d => rfl
  have hxy : ∀ y ∈ LB M Q A ⊓ hc.CN t, x * y * x⁻¹ ∈ LB M Q A := by
    intro y hy
    have h1 : x * y * x⁻¹ ∈ conjSubgroup x (LB M Q A) := ⟨y, hy.1, by simp [MulAut.conj_apply]⟩
    rwa [conj_LA_eq_of_mem_CN hc hs hrR hxN] at h1
  have hlam : ∀ g ∈ LB M Q A, Pk.act g ∈ Pk.lam A := fun g hg => by
    rw [Pk.act_of_mem (hLAH0 hg)]
    exact (Pk.phi_mem_lam_iff ⟨g, hLAH0 hg⟩).mpr hg
  have hcomm : ∀ y ∈ LB M Q A ⊓ hc.CN t, flagPsiLin M₀ W f₀ (Pk.act ⁅x, y⁆) =
      (flagPsiLin M₀ W f₀ (Pk.act y)).comp Dlin := by
    intro y hy
    refine LinearMap.ext fun d => ?_
    rw [flagPsiLin_apply, LinearMap.comp_apply, flagPsiLin_apply, hDlin]
    exact flagPsi_comm_apply Pk hc hs hrR hFD hf₀ haA hx hy d.2
  have hψ0 : ∀ T ∈ Pk.lam A, flagPsiLin M₀ W f₀ T = 0 → T = 1 := by
    intro T hT h0
    refine hfaith T hT fun e he => ?_
    have h1 := hFD.sub_eq hf₀ hT he
    have h2 : flagPsi M₀ f₀ T e = 0 := by
      have := congrArg (fun F => F ⟨e, he⟩) h0
      simpa [flagPsiLin_apply] using this
    rw [h2, zero_smul] at h1
    exact sub_eq_zero.mp h1
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre hs5.mem hZ0
  have hZ0H0 : Z0 ≤ H0 M Z := (hcen.1.trans inf_le_left).trans hLBH0
  let Zset : Set (W →ₗ[K] K) := {f | ∃ z ∈ Z0, flagPsiLin M₀ W f₀ (Pk.act z) = f}
  haveI : Finite (W →ₗ[K] K) := Module.finite_of_finite K
  have hZsetcard : Nat.card Zset ≤ Nat.card K := by
    let ev : ↥Z0 → Zset := fun z => ⟨flagPsiLin M₀ W f₀ (Pk.act z), z, z.2, rfl⟩
    have hev : ∀ z z' : ↥Z0, (QuotientGroup.leftRel (Q.subgroupOf Z0)) z z' → ev z = ev z' := by
      intro z z' h
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h
      have h1 : Pk.act ((z⁻¹ * z' : ↥Z0) : G) = 1 :=
        (Pk.act_eq_one_iff (hZ0H0 (z⁻¹ * z').2)).mpr h
      have h2 : Pk.act (z' : G) = Pk.act (z : G) := by
        have e : (z' : G) = (z : G) * ((z⁻¹ * z' : ↥Z0) : G) := by simp
        rw [e, Pk.act_mul (hZ0H0 z.2) (hZ0H0 (z⁻¹ * z').2), h1, mul_one]
      apply Subtype.ext
      show flagPsiLin M₀ W f₀ (Pk.act z) = flagPsiLin M₀ W f₀ (Pk.act z')
      rw [h2]
    let ev' : (↥Z0 ⧸ Q.subgroupOf Z0) → Zset := Quotient.lift ev hev
    have hsurj : Function.Surjective ev' := by
      rintro ⟨f, z, hz, rfl⟩
      exact ⟨QuotientGroup.mk ⟨z, hz⟩, rfl⟩
    have h3 := Nat.card_le_card_of_surjective ev' hsurj
    have h4 : Nat.card (↥Z0 ⧸ Q.subgroupOf Z0) = Q.relIndex Z0 := rfl
    rw [h4, hcen.2.1, ← Pk.h.card] at h3
    exact h3
  have hxyLA : ∀ y ∈ LB M Q A ⊓ hc.CN t, ⁅x, y⁆ ∈ LB M Q A := by
    intro y hy
    have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact (LB M Q A).mul_mem (hxy y hy) ((LB M Q A).inv_mem hy.1)
  have hf1'ne : flagPsiLin M₀ W f₀ (Pk.act ⁅x, b⁆) ≠ 0 := by
    intro h0
    apply hxb
    exact (Pk.act_eq_one_iff (hLAH0 (hxyLA b hb))).mp (hψ0 _ (hlam _ (hxyLA b hb)) h0)
  have hf1'def : flagPsiLin M₀ W f₀ (Pk.act ⁅x, b⁆) =
      (flagPsiLin M₀ W f₀ (Pk.act b)).comp Dlin := hcomm b hb
  have hF1sub : ∀ lam : K, lam • flagPsiLin M₀ W f₀ (Pk.act ⁅x, b⁆) ∈ Zset := by
    intro lam
    obtain ⟨y, hyT, hy⟩ := exists_smul_psi Pk h34 h91 hc hs hrR hFD hfaith hf₀ b hb lam
    refine ⟨⁅x, y⁆, hNN (Subgroup.commutator_mem_commutator hxN hyT.2), ?_⟩
    rw [hcomm y hyT, hy, LinearMap.smul_comp, hf1'def]
  have hZeq : ∀ f ∈ Zset, ∃ lam : K, f = lam • flagPsiLin M₀ W f₀ (Pk.act ⁅x, b⁆) := by
    let F1 : Set (W →ₗ[K] K) :=
      Set.range (fun lam : K => lam • flagPsiLin M₀ W f₀ (Pk.act ⁅x, b⁆))
    have hF1Z : F1 ⊆ Zset := by
      rintro _ ⟨lam, rfl⟩
      exact hF1sub lam
    have hinjF : Function.Injective
        (fun lam : K => lam • flagPsiLin M₀ W f₀ (Pk.act ⁅x, b⁆)) :=
      smul_left_injective K hf1'ne
    have hF1card : Nat.card F1 = Nat.card K := Nat.card_range_of_injective hinjF
    have hZfin : Zset.Finite := Set.toFinite _
    have heq : F1 = Zset := Set.eq_of_subset_of_ncard_le hF1Z (by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hZsetcard.trans hF1card.ge) hZfin
    intro f hf
    have hfF : f ∈ F1 := heq ▸ hf
    obtain ⟨lam, rfl⟩ := hfF
    exact ⟨lam, rfl⟩
  obtain ⟨lam, hlam'⟩ := hZeq _ ⟨c, hc0, rfl⟩
  obtain ⟨y, hyT, hy⟩ := exists_smul_psi Pk h34 h91 hc hs hrR hFD hfaith hf₀ b hb lam
  refine ⟨y, hyT, ?_⟩
  have hcH0 : c ∈ H0 M Z := hZ0H0 hc0
  have hxyH0 : ⁅x, y⁆ ∈ H0 M Z := hLAH0 (hxyLA y hyT)
  have hfun : flagPsiLin M₀ W f₀ (Pk.act ⁅x, y⁆) = flagPsiLin M₀ W f₀ (Pk.act c) := by
    rw [hcomm y hyT, hy, LinearMap.smul_comp, ← hf1'def, ← hlam']
  have hEq : Pk.act ⁅x, y⁆ = Pk.act c := by
    refine hFD.eq_of_psi_eq hfaith hf₀ (hlam _ (hxyLA y hyT)) (hlam _ (hZ0A hc0))
      (fun d hd => ?_)
    have h1 := congrArg (fun F => F ⟨d, hd⟩) hfun
    simpa [flagPsiLin_apply] using h1
  refine (Pk.act_eq_one_iff ((H0 M Z).mul_mem hxyH0 ((H0 M Z).inv_mem hcH0))).mp ?_
  rw [Pk.act_mul hxyH0 ((H0 M Z).inv_mem hcH0), Pk.act_inv hcH0, hEq, mul_inv_cancel]

end Core


@[expose] def Sec97NoncommStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ r : G, Sec7A hc t r → ∀ Z0 : Subgroup G,
      IsCentrePre Z0 (Rt M (LB M Q B) t) Q → ∀ x ∈ LB M Q B ⊓ hc.CN t, x ∉ Z0 →
        ∃ y ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, ⁅x, y⁆ ∉ Q

theorem sec97Coset_of_noncomm (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (hA : Sec9AExistsStatement)
    (hCentre : Step95CentreStatement) (h91 : Step91OrderVQBStatement)
    (hP : Sec97NoncommStatement) : Sec97CosetStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit Z0 hZ0 x hx hxZ hxconj c hc0
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hcen := hCentre G M Q Z B hc n t hs Z0 hZ0
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  have hNN := HS9.comm_CN_le_centre95 h34 h311bComm hs hZ0
  obtain ⟨hprod, hcomm, -⟩ := HS9.CN_eq_mul95 h34 h311a hNC hs hr
  have hZ0eq := HS9.isCentrePre_eq_inf91 hs hr hprod hcomm hZ0
  have hZ0A : Z0 ≤ LB M Q (conjSubgroup r B) := by
    rw [hZ0eq]
    exact inf_le_right
  obtain ⟨b, hbT, hxb⟩ := hP G M Q Z B hc n t hs r hr Z0 hZ0 x hx hxZ
  obtain ⟨K, _, _, _, γ, M₀, ⟨Pk⟩⟩ := exists_globalModelAction hc.hyp
  obtain ⟨y', hy'T, hy'⟩ := coset_core Pk h34 h91 hc hs hrR hZ0 hcen hNN hZ0A hx hbT hxb c hc0
  exact ⟨y', hy'T.2, hy'⟩

theorem core4_of_noncomm (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    (hA : Sec9AExistsStatement) (hn5 : Sec9NGeFiveStatement) (hS4 : Sec4Statement)
    (hCentre : Step95CentreStatement) (h91 : Step91OrderVQBStatement)
    (hP : Sec97NoncommStatement) : Sec97FourCore94Statement :=
  core4_of_coset h34 h311a h311bComm h312b hA hn5 hS4 hCentre
    (sec97Coset_of_noncomm h34 h311a h311bComm hA hCentre h91 hP)

end CFSG.RankThree.GF2n.Stroth80
