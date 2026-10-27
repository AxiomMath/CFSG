module

public import CFSG.RankThree.GF2n.Stroth80.Sec713O2XActsPlus6
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveRep

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.opm_mem_of_two_fix_T (h34 : Stroth34Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hc : Ctx M Q Z B) {t : G} (hs : Sec7Hyp hc 10 t) (hp3 : OmegaPlusNat hc t 3)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (hM : GlobalModelData M Q Z γ M₀) (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T)
    (hRT : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ w ∈ T, φ r w ∈ T)
    (hRfix : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      (∀ w ∈ T, φ r w = w) → r ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) :
    ∀ c ∈ (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)),
      IsPGroup 2 ↥(Subgroup.zpowers c) → (∀ w ∈ T, φ c w = w) →
        ∀ w ∈ M₀.B.orthogonal T, opm (φ c) w ∈ T := by
  classical
  intro c hcK hc2 hcT
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hQK : Q ≤ NormH0 M Z Z0 := fun q hq =>
    Subgroup.mem_inf.mpr ⟨hQH hq, Subgroup.le_normalizer (hQZ0 hq)⟩
  have hQM : ∀ y ∈ M, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hy) x).mp hx
  have hVH : bar M Q Z0 ≤ bar M Q (H0 M Z) := bar_mono' (hZ0.le.trans hRH)
  obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  have hsM : s ∈ M := hZ0M hsZ0
  have hsbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q Z0 :=
    (mk_mem_bar_iff_sec4 hQZ0 _).mpr hsZ0
  have hsH : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q (H0 M Z) := hVH hsbar
  have ha₀V : (⟨_, hsH⟩ : ↥(bar M Q (H0 M Z))) ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) :=
    Subgroup.mem_subgroupOf.mpr hsbar
  have ha₀1 : (⟨_, hsH⟩ : ↥(bar M Q (H0 M Z))) ≠ 1 := fun h => hsQ (Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)))
  have hs2 : s ^ 2 ∈ Q := by
    have h := sq_eq_one_bar hc hs hZc hZ0 (QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩) hsbar
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hTset : (T : Set M₀.E) = M₀.π '' (Vt M (LB M Q B) B Z t : Set G) := by
    rw [← hT _ ha₀V ha₀1, range_opm_eq_image M₀ s (φ ⟨_, hsH⟩) hZQ (fun x hx => hQM s hsM x hx)
      (fun x hx => hφπ ⟨s, hsM⟩ hsH x hx) hs2, hZV G M Q Z B hc 10 t hs Z0 hZ0 s hsZ0 hsQ]
  have hπT : ∀ v ∈ Vt M (LB M Q B) B Z t, M₀.π v ∈ T := fun v hv => by
    have : M₀.π v ∈ (T : Set M₀.E) := by rw [hTset]; exact ⟨v, hv, rfl⟩
    exact this
  obtain ⟨y, hyK, hyc⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hcK)
  have hyN : (y : G) ∈ NormH0 M Z Z0 := Subgroup.mem_subgroupOf.mp hyK
  have hpowH : ∀ k : ℕ, QuotientGroup.mk' (Q.subgroupOf M) (y ^ k) ∈ bar M Q (H0 M Z) :=
    fun k => by
      rw [map_pow, hyc]
      exact pow_mem c.2 k
  have hpowc : ∀ k : ℕ, (⟨_, hpowH k⟩ : ↥(bar M Q (H0 M Z))) = c ^ k := fun k => by
    apply Subtype.ext
    show QuotientGroup.mk' (Q.subgroupOf M) (y ^ k) = ((c ^ k : ↥(bar M Q (H0 M Z))) : Mbar M Q)
    rw [map_pow, hyc, Subgroup.coe_pow]
  have hcpowT : ∀ k : ℕ, ∀ w ∈ T, φ (c ^ k) w = w := by
    intro k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      rw [pow_succ, map_mul, LinearEquiv.mul_apply, hcT w hw, ih w hw]
  have hRcomm : ∀ (k : ℕ), ∀ r ∈ Rt M (LB M Q B) t, ⁅r, ((y ^ k : ↥M) : G)⁆ ∈ hc.CN t := by
    intro k r hr
    have hykN : ((y ^ k : ↥M) : G) ∈ NormH0 M Z Z0 := by
      rw [Subgroup.coe_pow]
      exact pow_mem hyN k
    have hcR : conjSubgroup ((y ^ k : ↥M) : G) (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
      (sec7_normalizes_of_zt hZt hZcard hc hs hZ0 hykN).1
    have hyRn := conjSubgroup_eq_self_iff.mp hcR
    have hcommR : ⁅r, ((y ^ k : ↥M) : G)⁆ ∈ Rt M (LB M Q B) t := by
      rw [commutatorElement_def]
      have h1 : ((y ^ k : ↥M) : G) * r⁻¹ * ((y ^ k : ↥M) : G)⁻¹ ∈ Rt M (LB M Q B) t :=
        (Subgroup.mem_normalizer_iff.mp hyRn _).mp (Subgroup.inv_mem _ hr)
      have e : r * ((y ^ k : ↥M) : G) * r⁻¹ * ((y ^ k : ↥M) : G)⁻¹ =
          r * (((y ^ k : ↥M) : G) * r⁻¹ * ((y ^ k : ↥M) : G)⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hr h1
    have hrM : r ∈ M := hRM hr
    set rb : ↥(bar M Q (H0 M Z)) := ⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨r, hrM⟩,
      bar_mono' hRH (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr))⟩ with hrb
    have hrbR : rb ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr))
    have hcommM : ⁅r, ((y ^ k : ↥M) : G)⁆ ∈ M := hRM hcommR
    have hbarc : QuotientGroup.mk' (Q.subgroupOf M) ⟨_, hcommM⟩ ∈ bar M Q (H0 M Z) :=
      bar_mono' hRH (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hcommR))
    have hbare : (⟨_, hbarc⟩ : ↥(bar M Q (H0 M Z))) = rb * c ^ k * rb⁻¹ * (c ^ k)⁻¹ := by
      rw [← hpowc k]
      apply Subtype.ext
      show QuotientGroup.mk' (Q.subgroupOf M) ⟨_, hcommM⟩ = _
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hrb]
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      congr 1
    have hfix : ∀ w ∈ T, φ ⟨_, hbarc⟩ w = w := by
      intro w hw
      rw [hbare, map_mul, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply]
      have h1 : φ (c ^ k)⁻¹ w = w := by
        conv_lhs => rw [← hcpowT k w hw]
        exact phi_inv_apply_phi φ _ w
      have h2 : φ rb⁻¹ w ∈ T := hRT _ (Subgroup.inv_mem _ hrbR) w hw
      rw [h1, hcpowT k _ h2, phi_apply_inv_apply]
    have hmemR : (⟨_, hbarc⟩ : ↥(bar M Q (H0 M Z))) ∈
        (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hcommR))
    have hN := Subgroup.mem_subgroupOf.mp (hRfix _ hmemR hfix)
    exact (mk_mem_bar_iff_sec4 hQN _).mp hN
  obtain ⟨a, ha⟩ := hc2 ⟨c, Subgroup.mem_zpowers c⟩
  have hca : c ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hyaQ : ((y ^ 2 ^ a : ↥M) : G) ∈ Q := by
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (y ^ 2 ^ a) = 1 := by
      have := congrArg Subtype.val (hpowc (2 ^ a))
      rw [hca] at this
      exact this
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hWV : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅(y : G), w⁆ ∈ Vt M (LB M Q B) B Z t := by
    by_contra hex
    push Not at hex
    have hPa : ∃ j : ℕ, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
        ⁅((y ^ 2 ^ j : ↥M) : G), w⁆ ∈ Vt M (LB M Q B) B Z t :=
      ⟨a, fun w hw => hZV' (hc.hyp.toHyp79.comm_mem_V hyaQ hw.1)⟩
    have hj := Nat.find_spec hPa
    have hj0 : Nat.find hPa ≠ 0 := by
      intro h0
      obtain ⟨w, hw, hwV⟩ := hex
      have h1 := hj w hw
      rw [h0, pow_zero, pow_one] at h1
      exact hwV h1
    have hj1 := Nat.find_min hPa (show Nat.find hPa - 1 < Nat.find hPa by omega)
    push Not at hj1
    obtain ⟨w, hw, hwV⟩ := hj1
    set y' : ↥M := y ^ 2 ^ (Nat.find hPa - 1) with hy'
    have hy2 : y' ^ 2 = y ^ 2 ^ Nat.find hPa := by
      rw [hy', ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
    have hy'N : (y' : G) ∈ NormH0 M Z Z0 := by
      rw [hy', Subgroup.coe_pow]
      exact pow_mem hyN _
    have hy'Z : ∀ z ∈ Z, (y' : G) * z * (y' : G)⁻¹ = z := by
      intro z hz
      have h1 := Subgroup.mem_centralizer_iff.mp hy'N.1.2 z hz
      rw [← h1, mul_inv_cancel_right]
    have hy'V : (y' : G) ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
      conjSubgroup_eq_self_iff.mp (sec7_normalizes_of_zt hZt hZcard hc hs hZ0 hy'N).2
    have hy'2W : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
        ⁅(y' : G) ^ 2, w⁆ ∈ Vt M (LB M Q B) B Z t := by
      intro w hw
      have := hj w hw
      rwa [← hy2, Subgroup.coe_pow] at this
    exact hwV (no_wild_plus6_ten_of h34 hA hPts h52a h52b (stroth310Chi_of_34 h34) hc hs hp3
      y'.2 hy'V (hRcomm _) hy'Z hy'2W w hw)
  intro w hw
  have hwW : w ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) := by
    rw [mem_img_Wt_iff M₀ hM.reg hVQ]
    intro v hv
    obtain ⟨x, hxV, -, rfl⟩ := hv
    exact (quadModel_form_facts M₀).2.1 _ _
      ((LinearMap.BilinForm.mem_orthogonal_iff.mp hw) _ (hπT x hxV))
  obtain ⟨x, hxW, hxQ, rfl⟩ := hwW
  have hyH : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z) := by rw [hyc]; exact c.2
  have hcy : c = ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hyH⟩ := Subtype.ext hyc.symm
  have hyxQ : (y : G) * x * (y : G)⁻¹ ∈ Q := hQM y y.2 x hxQ
  rw [opm_apply, hcy, ← hφπ y hyH x hxQ]
  have hcomm := hWV x hxW
  have e : (y : G) * x * (y : G)⁻¹ = ⁅(y : G), x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [e, M₀.π_mul _ (hVQ hcomm) _ hxQ, add_sub_cancel_right]
  exact hπT _ hcomm

end CFSG.RankThree.GF2n.Stroth80
