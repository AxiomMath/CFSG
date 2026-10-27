module

public import CFSG.RankThree.GF2n.Stroth80.Sec7WVSecCard
public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77OneCases

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

@[expose] def sec7Pre {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (Y : AddSubgroup M₀.E) : Subgroup G where
  carrier := {x | x ∈ Q ∧ M₀.π x ∈ Y}
  mul_mem' := fun {x y} hx hy =>
    ⟨Q.mul_mem hx.1 hy.1, by rw [M₀.π_mul x hx.1 y hy.1]; exact Y.add_mem hx.2 hy.2⟩
  one_mem' := ⟨Q.one_mem, by rw [Tim79.QuadModel.pi_one M₀]; exact Y.zero_mem⟩
  inv_mem' := fun {x} hx => ⟨Q.inv_mem hx.1, by rw [M₀.pi_inv hx.1]; exact Y.neg_mem hx.2⟩

theorem sec7_img_pre {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (Y : AddSubgroup M₀.E) (e : M₀.E) :
    e ∈ M₀.img (sec7Pre M₀ Y) ↔ e ∈ Y := by
  constructor
  · rintro ⟨x, hx, -, rfl⟩
    exact hx.2
  · intro he
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    exact M₀.pi_mem_img ⟨hxQ, he⟩ hxQ

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_act_sub_comm [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) {n : ℕ} [Finite K]
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) (hS : IsTensorSetup hc n M₀ ρ b)
    {x : G} (hxM : x ∈ M) {y : G} (hyQ : y ∈ Q) :
    (ρ (QuotientGroup.mk (⟨x, hxM⟩ : ↥M))).toAdd (M₀.π y) - M₀.π y = M₀.π ⁅x, y⁆ := by
  have hxyQ : x * y * x⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hxM).1 y hyQ
  have e1 : M₀.π (x * y * x⁻¹) = (ρ (QuotientGroup.mk (⟨x, hxM⟩ : ↥M))).toAdd (M₀.π y) :=
    hS.conj ⟨x, hxM⟩ y hyQ
  have e2 : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := rfl
  rw [e2, M₀.π_mul _ hxyQ _ (Q.inv_mem hyQ), M₀.pi_inv hyQ, ← e1, sub_eq_add_neg]

theorem sec7_psi_apply_comm [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) {n : ℕ} [Finite K]
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) (hS : IsTensorSetup hc n M₀ ρ b)
    {s : G} (hsM : s ∈ M) (ψs : M₀.E →ₗ[K] M₀.E)
    (hψs : ∀ e, ψs e = (ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd e - e) {x : G} (hxQ : x ∈ Q) :
    ψs (M₀.π x) = M₀.π ⁅s, x⁆ := by
  have hsxQ : s * x * s⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hsM).1 x hxQ
  have e1 : M₀.π (s * x * s⁻¹) = (ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd (M₀.π x) :=
    hS.conj ⟨s, hsM⟩ x hxQ
  have e2 : ⁅s, x⁆ = (s * x * s⁻¹) * x⁻¹ := rfl
  rw [hψs, e2, M₀.π_mul _ hsxQ _ (Q.inv_mem hxQ), M₀.pi_inv hxQ, ← e1, sub_eq_add_neg]

theorem sec7_comm_mem_Q (hc : Ctx M Q Z B) {s x : G} (hsM : s ∈ M) (hxQ : x ∈ Q) :
    ⁅s, x⁆ ∈ Q := by
  have e2 : ⁅s, x⁆ = (s * x * s⁻¹) * x⁻¹ := rfl
  rw [e2]
  exact Q.mul_mem ((hc.conj_mem_Q_of_mem_M hsM).1 x hxQ) (Q.inv_mem hxQ)

theorem sec7_pair_section [(Q.subgroupOf M).Normal] (h71 : Stroth71Statement)
    (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hno : ¬ Conc71abcd hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {K : Type} [Field K]
    [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) (hS : IsTensorSetup hc n M₀ ρ b)
    (ψ : M₀.E →ₗ[K] M₀.E)
    (hψ : ∀ e, ψ e = (ρ (QuotientGroup.mk (⟨t, hc.LB_le_M hs.toSec5.mem⟩ : ↥M))).toAdd e - e)
    (hW : ∀ x ∈ Q, x ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔ ψ (M₀.π x) = 0)
    {g s : G} (hgM : g ∈ M) (hsM : s ∈ M) (hs1 : s * (g * t * g⁻¹)⁻¹ ∈ Q) (hs2 : ⁅s, t⁆ ∈ Q)
    (ψs : M₀.E →ₗ[K] M₀.E)
    (hψs : ∀ e, ψs e = (ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd e - e) :
    hc.VtSub hS.model t ≤ M₀.B.orthogonal (hc.VtSub hS.model t) ∧
      LinearMap.range ψs ≤ M₀.B.orthogonal (hc.VtSub hS.model t) ∧
      ∀ (r : G) (hr : r ∈ Rt M (LB M Q B) t),
        ∀ y ∈ (M₀.B.orthogonal (hc.VtSub hS.model t)).map ψs ⊔ hc.VtSub hS.model t,
          (ρ (QuotientGroup.mk (⟨r, hc.Rt_le_M t hr⟩ : ↥M))).toAdd y ∈
            (M₀.B.orthogonal (hc.VtSub hS.model t)).map ψs ⊔ hc.VtSub hS.model t := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hk1 := sec7_ker_psi_eq_orth hc M₀ ρ b hS ψ hW
  have hvan := sec7_pair_vanish h71 hc hs hno hgM hs1 hs2
  have hsH : s ∈ H0 M Z :=
    sec7_mem_H0_of_mul_Q hc (sec7_conj_mem_H0 hc hgM (hc.LB_le_H0 ht)) hs1
  have hsbar : (QuotientGroup.mk (⟨s, hsM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨s, hsM⟩, Subgroup.mem_subgroupOf.mpr hsH, rfl⟩
  have hψsU : ∀ u ∈ hc.VtSub hS.model t, ψs u = 0 := by
    intro u hu
    obtain ⟨v, hvV, hvQ, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hu)
    rw [sec7_psi_apply_comm hc M₀ ρ b hS hsM ψs hψs hvQ]
    exact (M₀.π_ker _ (sec7_comm_mem_Q hc hsM hvQ)).mpr (hvan v hvV)
  have hUperp : hc.VtSub hS.model t ≤ M₀.B.orthogonal (hc.VtSub hS.model t) := by
    intro u hu
    rw [← hk1]
    obtain ⟨v, hvV, hvQ, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hu)
    exact LinearMap.mem_ker.mpr ((hW v hvQ).mp (sec7_V_le_W h310chi hc hs hvV))
  have hRW : LinearMap.range ψs ≤ M₀.B.orthogonal (hc.VtSub hS.model t) := by
    rintro _ ⟨e', rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hfix : (ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd u = u :=
      sub_eq_zero.mp ((hψs u).symm.trans (hψsU u hu))
    have h1 := hS.iso _ hsbar u e'
    rw [hfix] at h1
    exact LinearMap.BilinForm.isOrtho_def.mpr (by rw [hψs, map_sub, h1, sub_self])
  have hbarR : ∀ (r : G) (hr : r ∈ Rt M (LB M Q B) t),
      (QuotientGroup.mk (⟨r, hRM hr⟩ : ↥M) : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t) := by
    intro r hr
    exact Subgroup.mem_map.mpr ⟨⟨r, hRM hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hcomm_act : ∀ a b : Mbar M Q, a * b = b * a → ∀ e,
      (ρ a).toAdd ((ρ b).toAdd e) = (ρ b).toAdd ((ρ a).toAdd e) := by
    intro a b hab e
    rw [← act_mul_apply ρ a b e, ← act_mul_apply ρ b a e, hab]
  have hψS : ∀ (r : G) (hr : r ∈ Rt M (LB M Q B) t) (e : M₀.E),
      ψ ((ρ (QuotientGroup.mk (⟨r, hRM hr⟩ : ↥M))).toAdd e) =
        (ρ (QuotientGroup.mk (⟨r, hRM hr⟩ : ↥M))).toAdd (ψ e) := by
    intro r hr e
    rw [hψ, hψ, map_sub,
      hcomm_act _ _ (endg_comm_centre hZ0 hRM (z := ⟨t, htM⟩) htZ0 (hbarR r hr)) e]
  have hactU : ∀ (r : G) (hr : r ∈ Rt M (LB M Q B) t), ∀ u ∈ hc.VtSub hS.model t,
      (ρ (QuotientGroup.mk (⟨r, hRM hr⟩ : ↥M))).toAdd u ∈ hc.VtSub hS.model t :=
    fun r hr u hu => hc.act_mem_VtSub hS ht _ (hbarR r hr) u hu
  have hNact : ∀ n' ∈ hc.CN t, ∀ e : M₀.E, ψ e = 0 → ∀ hn'M : n' ∈ M,
      (ρ (QuotientGroup.mk (⟨n', hn'M⟩ : ↥M))).toAdd e - e ∈ hc.VtSub hS.model t := by
    intro n' hn' e he0 hn'M
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    have hxW : x ∈ Wt Q (Vt M (LB M Q B) B Z t) := (hW x hxQ).mpr he0
    have hcomm := sec7_N_comm_W_le_V h52a hA hc hs n' hn' x hxW
    rw [sec7_act_sub_comm hc M₀ ρ b hS hn'M hxQ]
    exact (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hcomm (sec7_comm_mem_Q hc hn'M hxQ))
  let A : Submodule K M₀.E := (M₀.B.orthogonal (hc.VtSub hS.model t)).map ψs
  let Y : Submodule K M₀.E := A ⊔ hc.VtSub hS.model t
  have hAle : A ≤ M₀.B.orthogonal (hc.VtSub hS.model t) :=
    LinearMap.map_le_range.trans hRW
  have hYle : Y ≤ M₀.B.orthogonal (hc.VtSub hS.model t) := sup_le hAle hUperp
  have hψψs : ∀ e, ψ (ψs e) = 0 := by
    intro e
    have := hRW (LinearMap.mem_range_self ψs e)
    rw [← hk1] at this
    exact LinearMap.mem_ker.mp this
  have hYinv : ∀ (r : G) (hr : r ∈ Rt M (LB M Q B) t), ∀ y ∈ Y,
      (ρ (QuotientGroup.mk (⟨r, hRM hr⟩ : ↥M))).toAdd y ∈ Y := by
    intro r hr y hy
    obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add]
    refine Y.add_mem ?_ (Submodule.mem_sup_right (hactU r hr u hu))
    obtain ⟨e, he, rfl⟩ := ha
    have hn : ⁅r, s⁆ ∈ hc.CN t := comm_mem_CN_of_vanish hc hs hsM hs2 hvan hr
    have hnM : ⁅r, s⁆ ∈ M := hRM (Ctx.mem_CN.mp hn).1
    have he0 : ψ e = 0 := by
      have := he
      rw [← hk1] at this
      exact LinearMap.mem_ker.mp this
    set e' := (ρ (QuotientGroup.mk (⟨r, hRM hr⟩ : ↥M))).toAdd e with he'
    have he'0 : ψ e' = 0 := by rw [he', hψS r hr, he0, map_zero]
    have he'U : e' ∈ M₀.B.orthogonal (hc.VtSub hS.model t) := by
      rw [← hk1]
      exact LinearMap.mem_ker.mpr he'0
    have hmk : (QuotientGroup.mk (⟨r, hRM hr⟩ : ↥M) : Mbar M Q) *
        QuotientGroup.mk (⟨s, hsM⟩ : ↥M) =
        QuotientGroup.mk (⟨⁅r, s⁆, hnM⟩ : ↥M) * QuotientGroup.mk (⟨s, hsM⟩ : ↥M) *
          QuotientGroup.mk (⟨r, hRM hr⟩ : ↥M) := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group
    have hkey : (ρ (QuotientGroup.mk (⟨r, hRM hr⟩ : ↥M))).toAdd
        ((ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd e) =
        (ρ (QuotientGroup.mk (⟨⁅r, s⁆, hnM⟩ : ↥M))).toAdd
          ((ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd e') := by
      rw [← act_mul_apply ρ, hmk, act_mul_apply ρ, act_mul_apply ρ]
    have hsplit : (ρ (QuotientGroup.mk (⟨r, hRM hr⟩ : ↥M))).toAdd (ψs e) =
        ((ρ (QuotientGroup.mk (⟨⁅r, s⁆, hnM⟩ : ↥M))).toAdd e' - e') +
          ((ρ (QuotientGroup.mk (⟨⁅r, s⁆, hnM⟩ : ↥M))).toAdd (ψs e') - ψs e') + ψs e' := by
      have h1 : (ρ (QuotientGroup.mk (⟨r, hRM hr⟩ : ↥M))).toAdd (ψs e) =
          (ρ (QuotientGroup.mk (⟨⁅r, s⁆, hnM⟩ : ↥M))).toAdd
            ((ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd e') - e' := by
        rw [hψs, map_sub, hkey]
      have h2 : (ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd e' = e' + ψs e' := by
        rw [hψs]
        abel
      rw [h1, h2, map_add]
      abel
    rw [hsplit]
    exact Y.add_mem (Y.add_mem (Submodule.mem_sup_right (hNact _ hn e' he'0 hnM))
      (Submodule.mem_sup_right (hNact _ hn (ψs e') (hψψs e') hnM)))
      (Submodule.mem_sup_left (Submodule.mem_map_of_mem he'U))
  exact ⟨hUperp, hRW, hYinv⟩

theorem sec7_section_pre [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
    (hS : IsTensorSetup hc n M₀ ρ b) (ψ : M₀.E →ₗ[K] M₀.E)
    (hW : ∀ x ∈ Q, x ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔ ψ (M₀.π x) = 0)
    (Y : Submodule K M₀.E) (hUY : hc.VtSub hS.model t ≤ Y)
    (hYle : Y ≤ M₀.B.orthogonal (hc.VtSub hS.model t))
    (hYinv : ∀ (r : G) (hr : r ∈ Rt M (LB M Q B) t), ∀ y ∈ Y,
      (ρ (QuotientGroup.mk (⟨r, hc.Rt_le_M t hr⟩ : ↥M))).toAdd y ∈ Y) :
    Vt M (LB M Q B) B Z t ≤ sec7Pre M₀ Y.toAddSubgroup ∧
      sec7Pre M₀ Y.toAddSubgroup ≤ Wt Q (Vt M (LB M Q B) B Z t) ∧
      ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r (sec7Pre M₀ Y.toAddSubgroup) =
        sec7Pre M₀ Y.toAddSubgroup := by
  classical
  have hk1 := sec7_ker_psi_eq_orth hc M₀ ρ b hS ψ hW
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  refine ⟨fun x hx => ⟨hVQ hx, hUY ((hc.mem_VtSub hS.model t).mpr
    (M₀.pi_mem_img hx (hVQ hx)))⟩, ?_, ?_⟩
  · intro x hx
    refine (hW x hx.1).mpr ?_
    have h1 := hYle hx.2
    rw [← hk1] at h1
    exact LinearMap.mem_ker.mp h1
  · intro r hr
    apply conjSubgroup_eq_self_iff.mpr
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    refine ⟨(hc.conj_mem_Q_of_mem_M (hc.Rt_le_M t hr)).1 x hx.1, ?_⟩
    rw [hS.conj ⟨r, hc.Rt_le_M t hr⟩ x hx.1]
    exact hYinv r hr _ hx.2

theorem step77OneWildCase_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hSec : Sec7WVSecCardStatement) :
    Step77OneWildCaseStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 hVne ⟨w₀, hw₀W, hw₀⟩
  classical
  haveI := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hguM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  have hsM : s ∈ M := by
    have h1 : s = (s * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
    rw [h1]
    exact M.mul_mem (hc.hyp.Q_normal.1 hs1) hguM
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, ψ, hψ, hrange, hW, hinj, hA5, hA6⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  obtain ⟨ψs, hψs, hrs, hker⟩ := sec7_pair_psi hc M₀ ρ b hS ht ψ hψ hrange hgM hsM hs1
  obtain ⟨-, hUcard⟩ := sec7_Hset_card h34 hRoot hc hs hom M₀ ρ b hS
  obtain ⟨hc1, hd4, hd⟩ := sec7_pair_card_meet hc M₀ ρ b hS hgM ψs hrs hUcard
  obtain ⟨hf, hr⟩ := sec7_model_form M₀
  have hk1 := sec7_ker_psi_eq_orth hc M₀ ρ b hS ψ hW
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨hUperp, hRW, hYinv⟩ := sec7_pair_section h71 h310chi h52a hA hc hs hno hZ0 M₀ ρ b hS ψ
    hψ hW hgM hsM hs1 hs2 ψs hψs
  let A : Submodule K M₀.E := (M₀.B.orthogonal (hc.VtSub hS.model t)).map ψs
  let Y : Submodule K M₀.E := A ⊔ hc.VtSub hS.model t
  have hAle : A ≤ M₀.B.orthogonal (hc.VtSub hS.model t) :=
    LinearMap.map_le_range.trans hRW
  have hYle : Y ≤ M₀.B.orthogonal (hc.VtSub hS.model t) := sup_le hAle hUperp
  obtain ⟨hVP, hPW, hPR⟩ := sec7_section_pre hc hs M₀ ρ b hS ψ hW Y le_sup_right hYle hYinv
  let Pg : Subgroup G := sec7Pre M₀ Y.toAddSubgroup
  obtain ⟨k, hk⟩ := (hSec G M Q Z B hc n t hs Pg hVP hPW hPR 2 le_rfl).1 hom
  have hZPg : Z ≤ Pg := fun z hz => ⟨hc.Z_le_Q hz, by
    rw [(M₀.π_ker z (hc.Z_le_Q hz)).mpr hz]
    exact Y.zero_mem⟩
  have hPQ : Pg ≤ Q := fun x hx => hx.1
  have hcP := Tim79.QuadModel.card_eq M₀ hPQ hZPg
  have hcimgP : Nat.card (M₀.img Pg) = Nat.card Y :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun e => sec7_img_pre M₀ Y.toAddSubgroup e))
  have hcV := Tim79.QuadModel.card_eq M₀ hVQ hZV'
  have hcimgV : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) = Nat.card (hc.VtSub hS.model t) :=
    rfl
  have hZK : Nat.card Z = Nat.card K := hS.card.symm
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hYcard : Nat.card Y = Nat.card K ^ (4 + 4 * k) := by
    rw [hcP, hcimgP, hcV, hcimgV, hUcard] at hk
    have h2 : Nat.card Z * Nat.card Y =
        Nat.card Z * (Nat.card K ^ 4 * Nat.card K ^ (4 * k)) := by
      rw [hk, mul_assoc, hZK]
      norm_num
    rw [Nat.eq_of_mul_eq_mul_left hZpos h2, ← pow_add]
  have hfinY : Module.finrank K Y = 4 + 4 * k := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := Y)
    rw [hYcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  have hfU : Module.finrank K (hc.VtSub hS.model t) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := hc.VtSub hS.model t)
    rw [hUcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  have hfR : Module.finrank K (LinearMap.range ψs) = 4 := by
    have hcard : Nat.card (LinearMap.range ψs) = Nat.card K ^ 4 := by
      have h1 : Nat.card (LinearMap.range ψs) = Nat.card (M₀.img (conjSubgroup g
          (Vt M (LB M Q B) B Z t))) :=
        Nat.card_congr (Equiv.subtypeEquivRight hrs)
      rw [h1, sec7_card_img_conj hc M₀ ρ b hS hgM hZV']
      have h2 : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) =
          Nat.card (hc.VtSub hS.model t) := rfl
      rw [h2, hUcard]
    have h := Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.range ψs)
    rw [hcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  have hmap := sec7_finrank_map_orthogonal M₀.B hf hr ψs hker (hc.VtSub hS.model t)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A (hc.VtSub hS.model t)
  have hw₀Q : w₀ ∈ Q := hw₀W.1
  have hw₀ker : M₀.π w₀ ∈ M₀.B.orthogonal (hc.VtSub hS.model t) := by
    rw [← hk1]
    exact LinearMap.mem_ker.mpr ((hW w₀ hw₀Q).mp hw₀W)
  have hnotU : ψs (M₀.π w₀) ∉ hc.VtSub hS.model t := by
    intro h
    rw [sec7_psi_apply_comm hc M₀ ρ b hS hsM ψs hψs hw₀Q] at h
    exact hw₀ ((Tim79.QuadModel.mem_img_iff M₀ hZV' (sec7_comm_mem_Q hc hsM hw₀Q)).mp
      ((hc.mem_VtSub hS.model t).mp h))
  have hlt : hc.VtSub hS.model t < Y := by
    refine lt_of_le_of_ne le_sup_right fun h => hnotU ?_
    rw [h]
    exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hw₀ker)
  have hk1' := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hfinY, hfU] at hk1'
  rw [hfinY, hmap, hfR, hfU] at hsum
  have hd0 : Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs) = 0 := by
    omega
  rw [hd0, add_zero, pow_one, ← hZK] at hc1
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hZV' (hc.Z_le_conjSubgroup hZV' hgM))
    (le_of_eq hc1)).symm

end CFSG.RankThree.GF2n.Stroth80
