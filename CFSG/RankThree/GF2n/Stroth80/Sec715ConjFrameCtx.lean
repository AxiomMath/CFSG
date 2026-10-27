module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveRep

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.LB_le_conj_Rt (hZt : Sec7ZtStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g s : G} (hg : g ∈ M) (hsZ : s ∈ Z0) (hsQ : s ∉ Q) (hgs : g * s * g⁻¹ ∈ LB M Q B) :
    LB M Q B ≤ conjSubgroup g (Rt M (LB M Q B) t) := by
  obtain ⟨hRs, -⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 s hsZ hsQ
  rw [← hRs, conjSubgroup_Rt_eq hg s]
  exact le_Rt (M := M) (LB M Q B) hgs

theorem Ctx.sec715_Tt_facts (hZV : Sec7ZVStatement) (hZc : Sec7CentreMpStatement)
    (hZcard : Sec7ZCardStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x)) :
    ∃ Tt : ↥(bar M Q (H0 M Z)) → Submodule K M₀.E,
      (∀ g a : ↥(bar M Q (H0 M Z)), a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) → a ≠ 1 →
        LinearMap.range (opm (φ (g * a * g⁻¹))) = Tt g) ∧
      (∀ n ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), ∀ w ∈ Tt 1, φ n w = w) ∧
      (∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
        (∀ w ∈ Tt 1, φ r w = w) →
          r ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hVtQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVH : bar M Q Z0 ≤ bar M Q (H0 M Z) := bar_mono' (hZ0.le.trans hRH)
  have hlift : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      ∃ (z : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) z ∈ bar M Q (H0 M Z)), (z : G) ∈ Z0 ∧
        a = ⟨QuotientGroup.mk' (Q.subgroupOf M) z, hy⟩ := by
    intro a ha ha1
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (a : Mbar M Q)
    have hzZ : (z : G) ∈ Z0 := (mk_mem_bar_iff_sec4 hQZ0 z).mp (hz ▸ Subgroup.mem_subgroupOf.mp ha)
    exact ⟨z, hz ▸ a.2, hzZ, Subtype.ext hz.symm⟩
  have hrange : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      (LinearMap.range (opm (φ a)) : Set M₀.E) = M₀.π '' (Vt M (LB M Q B) B Z t : Set G) := by
    intro a ha ha1
    obtain ⟨z, hy, hzZ, rfl⟩ := hlift a ha ha1
    have hzQ : ∀ x ∈ Q, (z : G) * x * (z : G)⁻¹ ∈ Q := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 z.2) x).mp hx
    have hz2 : (z : G) ^ 2 ∈ Q := by
      have h := sq_eq_one_bar hc hs hZc hZ0 (QuotientGroup.mk' (Q.subgroupOf M) z)
        ((mk_mem_bar_iff_sec4 hQZ0 z).mpr hzZ)
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact Subgroup.mem_subgroupOf.mp h
    have hzNQ : (z : G) ∉ Q := fun h => ha1 (Subtype.ext
      ((QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_subgroupOf.mpr h)))
    have hZVz : Ut Q Z (z : G) = Vt M (LB M Q B) B Z t :=
      hZV G M Q Z B hc n t hs Z0 hZ0 (z : G) hzZ hzNQ
    have h1 := range_opm_eq_image M₀ (z : G) (φ ⟨QuotientGroup.mk' (Q.subgroupOf M) z, hy⟩) hZQ
      hzQ (fun x hx => hφπ z hy x hx) hz2
    rw [h1, hZVz]
  obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  have hsM : s ∈ M := hZ0M hsZ0
  have hsbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q Z0 :=
    (mk_mem_bar_iff_sec4 hQZ0 _).mpr hsZ0
  have hsH : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q (H0 M Z) := hVH hsbar
  have ha₀V : (⟨_, hsH⟩ : ↥(bar M Q (H0 M Z))) ∈
      (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := Subgroup.mem_subgroupOf.mpr hsbar
  have ha₀1 : (⟨_, hsH⟩ : ↥(bar M Q (H0 M Z))) ≠ 1 := fun h => hsQ (Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)))
  set a₀ : ↥(bar M Q (H0 M Z)) := ⟨_, hsH⟩ with ha₀
  let Tt : ↥(bar M Q (H0 M Z)) → Submodule K M₀.E := fun g =>
    (LinearMap.range (opm (φ a₀))).map ((φ g : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
  have hTt1 : Tt 1 = LinearMap.range (opm (φ a₀)) := by
    simp [Tt]
  have hTt1set : (Tt 1 : Set M₀.E) = M₀.π '' (Vt M (LB M Q B) B Z t : Set G) := by
    rw [hTt1]
    exact hrange a₀ ha₀V ha₀1
  refine ⟨Tt, ?_, ?_, ?_⟩
  · intro g a ha ha1
    have hsame : LinearMap.range (opm (φ a)) = LinearMap.range (opm (φ a₀)) :=
      SetLike.coe_injective ((hrange a ha ha1).trans (hrange a₀ ha₀V ha₀1).symm)
    rw [map_mul, map_mul, map_inv, range_opm_conj, hsame]
  · intro nn hnn w hw
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (nn : Mbar M Q)
    have hyCN : (y : G) ∈ hc.CN t :=
      (mk_mem_bar_iff_sec4 hQN y).mp (hy ▸ Subgroup.mem_subgroupOf.mp hnn)
    have hw' : w ∈ (Tt 1 : Set M₀.E) := hw
    rw [hTt1set] at hw'
    obtain ⟨v, hv, rfl⟩ := hw'
    have hyH : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z) := hy ▸ nn.2
    have hnn' : nn = ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hyH⟩ := Subtype.ext hy.symm
    rw [hnn', ← hφπ y hyH v (hVtQ hv)]
    have hcZ : ⁅(y : G), v⁆ ∈ Z := (Ctx.mem_CN.mp hyCN).2 v hv
    have hcQ : ⁅(y : G), v⁆ ∈ Q := hZQ hcZ
    have hyv : (y : G) * v * (y : G)⁻¹ = ⁅(y : G), v⁆ * v := by
      rw [commutatorElement_def]
      group
    rw [hyv, M₀.π_mul _ hcQ v (hVtQ hv), (M₀.π_ker _ hcQ).mpr hcZ, zero_add]
  · intro r hr hfix
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (r : Mbar M Q)
    have hyR : (y : G) ∈ Rt M (LB M Q B) t :=
      (mk_mem_bar_iff_sec4 hQR y).mp (hy ▸ Subgroup.mem_subgroupOf.mp hr)
    have hyH : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z) := hy ▸ r.2
    have hrr : r = ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hyH⟩ := Subtype.ext hy.symm
    refine Subgroup.mem_subgroupOf.mpr ((mk_mem_bar_iff_sec4 hQN y).mpr ?_ |> fun h => hy ▸ h)
    refine Ctx.mem_CN.mpr ⟨hyR, fun v hv => ?_⟩
    have hvQ : v ∈ Q := hVtQ hv
    have hπv : M₀.π v ∈ Tt 1 := by
      have : M₀.π v ∈ (Tt 1 : Set M₀.E) := by
        rw [hTt1set]
        exact ⟨v, hv, rfl⟩
      exact this
    have hf := hfix _ hπv
    rw [hrr, ← hφπ y hyH v hvQ] at hf
    have hyvQ : (y : G) * v * (y : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 y.2) v).mp hvQ
    have hcQ : ⁅(y : G), v⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem hyvQ (Q.inv_mem hvQ)
    have hyv : (y : G) * v * (y : G)⁻¹ = ⁅(y : G), v⁆ * v := by
      rw [commutatorElement_def]
      group
    rw [hyv, M₀.π_mul _ hcQ v hvQ] at hf
    have h0 : M₀.π ⁅(y : G), v⁆ = 0 := by
      have := add_eq_right.mp hf
      exact this
    exact (M₀.π_ker _ hcQ).mp h0

theorem Ctx.sec715Frame (h34 : Stroth34Statement) (hZt : Sec7ZtStatement)
    (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x)) :
    ∃ Tt : ↥(bar M Q (H0 M Z)) → Submodule K M₀.E,
      Sec715Frame φ ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
        ((bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)))
        ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
        ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) Tt := by
  classical
  obtain ⟨Tt, hTtR, hTtN, hTtR'⟩ := Ctx.sec715_Tt_facts hZV hZc hZcard hc hs hZ0 M₀ φ hφπ
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hZ0L : Z0 ≤ LB M Q B := fun x hx => (hZc G M Q Z B hc n t hs Z0 hZ0 x hx).1
  have hZ0N : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hRK : Rt M (LB M Q B) t ≤ NormH0 M Z Z0 := fun ρ hρ =>
    Subgroup.mem_inf.mpr ⟨hRH hρ, IsCentrePre.mem_normalizer hZ0 hnormR hρ⟩
  have hmem : ∀ {S : Subgroup G}, Q ≤ S → ∀ (x : ↥(bar M Q (H0 M Z))) (y : ↥M),
      QuotientGroup.mk' (Q.subgroupOf M) y = (x : Mbar M Q) →
        (x ∈ (bar M Q S).subgroupOf (bar M Q (H0 M Z)) ↔ (y : G) ∈ S) := by
    intro S hQS x y hy
    rw [Subgroup.mem_subgroupOf, ← hy]
    exact mk_mem_bar_iff_sec4 hQS y
  have hsub : ∀ {S T : Subgroup G}, S ≤ T → (bar M Q S).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q T).subgroupOf (bar M Q (H0 M Z)) :=
    fun hST x hx => Subgroup.mem_subgroupOf.mpr (bar_mono' hST (Subgroup.mem_subgroupOf.mp hx))
  have hrep : ∀ x : ↥(bar M Q (H0 M Z)), ∃ y : ↥M,
      QuotientGroup.mk' (Q.subgroupOf M) y = (x : Mbar M Q) :=
    fun x => QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
  refine ⟨Tt, ?_⟩
  exact
    { V_le_L := hsub hZ0L
      V_le_Nb := hsub hZ0N
      L_le_Rb := hsub hLR
      Nb_le_Rb := hsub hNR
      Nb_normal := fun r hr nn hnn => by
        obtain ⟨y, hy⟩ := hrep r
        obtain ⟨z, hz⟩ := hrep nn
        have hyR : (y : G) ∈ Rt M (LB M Q B) t := (hmem hQR r y hy).mp hr
        have hzN : (z : G) ∈ hc.CN t := (hmem hQN nn z hz).mp hnn
        have hconj := sec7_conj_CN_eq hZt hZcard hc hs hZ0 (hRK hyR)
        have h1 : (y : G) * z * (y : G)⁻¹ ∈ hc.CN t := by
          rw [← hconj, mem_conjSubgroup]
          simpa [mul_assoc] using hzN
        refine (hmem hQN (r * nn * r⁻¹) (y * z * y⁻¹) ?_).mpr (by simpa using h1)
        simp only [map_mul, map_inv, hy, hz, Subgroup.coe_mul, Subgroup.coe_inv]
      L_comm := fun a ha b hb => by
        apply Subtype.ext
        have hab := (hc.isElemAbelian_bar_LB).1.is_comm.comm
          ⟨(a : Mbar M Q), Subgroup.mem_subgroupOf.mp ha⟩
          ⟨(b : Mbar M Q), Subgroup.mem_subgroupOf.mp hb⟩
        show (a : Mbar M Q) * b = b * a
        exact congrArg Subtype.val hab
      Nb_norm_L := fun nn hnn l hl => by
        have hN := hc.bar_CN_le_normalizer h34 hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2
          hs.toSec5.gen ht (Subgroup.mem_subgroupOf.mp hnn)
        exact Subgroup.mem_subgroupOf.mpr
          ((Subgroup.mem_normalizer_iff.mp hN (l : Mbar M Q)).mp (Subgroup.mem_subgroupOf.mp hl))
      L_le_conj_Rb := fun g hg l hl => by
        obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
        have hsM : s ∈ M := hc.centre_le_M t hZ0 hsZ0
        have hsbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q (H0 M Z) :=
          bar_mono' (hZ0.le.trans hRH) ((mk_mem_bar_iff_sec4 hQZ0 _).mpr hsZ0)
        set a : ↥(bar M Q (H0 M Z)) := ⟨_, hsbar⟩ with ha
        have haV : a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) :=
          (hmem hQZ0 a ⟨s, hsM⟩ rfl).mpr hsZ0
        obtain ⟨y, hy⟩ := hrep g
        obtain ⟨w, hw⟩ := hrep l
        have hgs : (y : G) * s * (y : G)⁻¹ ∈ LB M Q B := by
          have h1 := hg a haV
          refine (hmem hQL (g * a * g⁻¹) (y * ⟨s, hsM⟩ * y⁻¹) ?_).mp h1
          simp only [map_mul, map_inv, hy, Subgroup.coe_mul, Subgroup.coe_inv, ha]
        have hwL : (w : G) ∈ LB M Q B := (hmem hQL l w hw).mp hl
        have hle := hc.LB_le_conj_Rt hZt hs hZ0 y.2 hsZ0 hsQ hgs
        have h2 : (y : G)⁻¹ * w * y ∈ Rt M (LB M Q B) t := mem_conjSubgroup.mp (hle hwL)
        refine (hmem hQR (g⁻¹ * l * g) (y⁻¹ * w * y) ?_).mpr (by simpa using h2)
        simp only [map_mul, map_inv, hy, hw, Subgroup.coe_mul, Subgroup.coe_inv]
      Tt_range := hTtR
      Nb_fixes := hTtN
      Rb_fix_Nb := hTtR' }

end CFSG.RankThree.GF2n.Stroth80
