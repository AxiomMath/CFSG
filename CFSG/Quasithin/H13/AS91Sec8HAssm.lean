module

public import CFSG.Quasithin.H13.AS91Sec8HIsom
public import CFSG.Quasithin.H13.AS91Sec8HExt
public import CFSG.Quasithin.H13.AS91Sec8HGeom
public import CFSG.LargeExtraspecial.SettingLiftIsometry
public import CFSG.Quasithin.H13.AS91ResHolds

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin.HatM22
open CFSG.RankThree.Literature.FSmith
open CFSG.CharacterTheory.SteinbergBY (FieldFour)
open CFSG.CharacterTheory.SteinbergBY.FieldFour (ω ω₂ ω_ne_zero ω_ne_one ω₂_ne_zero
  ω₂_ne_one ω_sq)

namespace Loc41

variable {G : Type} [Group G] [Finite G] {z : G}

theorem X_le_M (c : Loc41 G z) : c.X ≤ c.S.M := c.SM_eq.symm ▸ c.X_le

theorem NX_le_M (c : Loc41 G z) : c.NX ≤ c.S.M := c.SM_eq.symm ▸ inf_le_left

theorem subgroupOf_QG_eq (c : Loc41 G z) : c.S.QG.subgroupOf c.S.M = c.S.Q := by
  apply Subgroup.ext
  intro x
  rw [Subgroup.mem_subgroupOf, c.S.mem_QG_iff]
  constructor
  · rintro ⟨_, hxQ⟩
    simpa using hxQ
  · intro hx
    exact ⟨x.2, by simpa using hx⟩

@[expose] noncomputable def equivQG (c : Loc41 G z) : ↥(Q z) ≃* ↥c.S.Q :=
  (MulEquiv.subgroupCongr c.S_QG).symm.trans
    ((Subgroup.subgroupOfEquivOfLe c.S.QG_le_M).symm.trans
      (MulEquiv.subgroupCongr c.subgroupOf_QG_eq))

@[expose] noncomputable def equivQ (c : Loc41 G z) : ↥c.S.Q ≃* ↥(Q z) :=
  (MulEquiv.subgroupCongr (c.subgroupOf_QG_eq).symm).trans
    ((Subgroup.subgroupOfEquivOfLe c.S.QG_le_M).trans (MulEquiv.subgroupCongr c.S_QG))

@[simp] theorem coe_equivQG (c : Loc41 G z) (q : ↥(Q z)) :
    ((c.equivQG q : ↥c.S.Q) : G) = (q : G) := rfl

@[simp] theorem coe_equivQ (c : Loc41 G z) (q : ↥c.S.Q) :
    ((c.equivQ q : ↥(Q z)) : G) = (q : G) := rfl

theorem equivQ_zQ (c : Loc41 G z) : c.equivQ c.S.zQ = ⟨z, c.z_mem_Q⟩ := by
  apply Subtype.ext
  rw [c.coe_equivQ]
  exact c.S.coe_zM.trans c.S_z

theorem equivQG_zQ (c : Loc41 G z) : c.equivQG ⟨z, c.z_mem_Q⟩ = c.S.zQ := by
  apply Subtype.ext
  apply Subtype.ext
  rw [c.coe_equivQG]
  exact (c.S.coe_zM.trans c.S_z).symm

abbrev NXm (c : Loc41 G z) : Subgroup ↥c.S.M := c.NX.subgroupOf c.S.M

@[simp] theorem mem_NXm_iff (c : Loc41 G z) {n : ↥c.S.M} : n ∈ c.NXm ↔ (n : G) ∈ c.NX :=
  Subgroup.mem_subgroupOf

theorem zpowers_toSM (c : Loc41 G z) {x : G} (hx : x ∈ c.X) (hx1 : x ≠ 1) :
    Subgroup.zpowers (c.toSM ⟨x, c.X_le_CX hx⟩) = c.X.subgroupOf c.S.M := by
  have hxord : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard c.X hx
      rwa [c.card_X] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ?_) ?_
  · rw [Subgroup.mem_subgroupOf]; exact hx
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, c.coe_toSM, hxord,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.X_le_M).toEquiv, c.card_X]

theorem eq_zero_of_rho_fixed_of_piC_mem (c : Loc41 G z) (h : ↥c.CX)
    (hpi : c.piC h = hatM22Z ∨ c.piC h = hatM22Z ^ 2) {v : c.S.Qt}
    (hv : (c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v = v) : v = 0 := by
  have key : ∀ e : FieldFour, e ≠ 1 → c.ψ v = e • c.ψ v → c.ψ v = 0 := by
    intro e he hψ
    by_contra hw
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
    have hωj : e * (c.ψ v) j = 1 * (c.ψ v) j := by
      rw [one_mul]
      exact (congrArg (fun f => f j) hψ).symm
    exact he (mul_right_cancel₀ hj hωj)
  have h0 : c.ψ v = 0 := by
    rcases hpi with hpi | hpi
    · refine key ω ω_ne_one ?_
      have hspec := c.piC_spec h v
      rw [hpi, hatM22Z_val, Matrix.smul_mulVec, Matrix.one_mulVec, hv] at hspec
      exact hspec
    · refine key ω₂ ω₂_ne_one ?_
      have hspec := c.piC_spec h v
      rw [hpi, hatM22Z_sq_val, Matrix.smul_mulVec, Matrix.one_mulVec, hv] at hspec
      exact hspec
  exact c.ψ.injective (by rw [h0, map_zero])

end Loc41

namespace Loc41

variable {G : Type} [Group G] [Finite G] {z : G}
variable {G' : Type} [Group G'] [Finite G'] {z' : G'}

@[expose] noncomputable def thetaNXm (c : Loc41 G z) (c' : Loc41 G' z')
    (θN : ↥c.NX ≃* ↥c'.NX) : ↥c.NXm ≃* ↥c'.NXm :=
  (Subgroup.subgroupOfEquivOfLe c.NX_le_M).trans
    (θN.trans (Subgroup.subgroupOfEquivOfLe c'.NX_le_M).symm)

theorem coe_thetaNXm (c : Loc41 G z) (c' : Loc41 G' z') (θN : ↥c.NX ≃* ↥c'.NX)
    (n : ↥c.NXm) :
    ((c.thetaNXm c' θN n : ↥c'.NXm) : G') =
      (θN ⟨(n : G), c.mem_NXm_iff.mp n.2⟩ : ↥c'.NX) := rfl

theorem eq_zero_of_rho_thetaNXm
    (c : Loc41 G z) (c' : Loc41 G' z')
    (θ : ↥c.CX ≃* ↥c'.CX) (hθ : ∀ h, c'.piC (θ h) = c.piC h)
    (θN : ↥c.NX ≃* ↥c'.NX)
    (hext : ∀ h : ↥c.CX, ((θN ⟨h, c.CX_le_NX h.2⟩ : ↥c'.NX) : G') = (θ h : G'))
    {y : ↥c.NXm} (hyX : (y : G) ∈ c.X) (hy1 : (y : G) ≠ 1) {v : c'.S.Qt}
    (hv : (c'.S.ρ (c.thetaNXm c' θN y) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) v = v) : v = 0 := by
  let h : ↥c.CX := ⟨(y : G), c.X_le_CX hyX⟩
  have hyN : (⟨h, c.CX_le_NX h.2⟩ : ↥c.NX) = ⟨(y : G), c.mem_NXm_iff.mp y.2⟩ := Subtype.ext rfl
  have hval : ((c.thetaNXm c' θN y : ↥c'.NXm) : G') = (θ h : G') := by
    rw [c.coe_thetaNXm, ← hyN]
    exact hext h
  have hSM : ((c.thetaNXm c' θN y : ↥c'.NXm) : c'.S.M) = c'.toSM (θ h) := Subtype.ext hval
  have hρ : (c'.S.ρ (c.thetaNXm c' θN y) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) =
      (c'.S.ρ (c'.toSM (θ h)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) := by rw [hSM]
  rw [hρ] at hv
  refine c'.eq_zero_of_rho_fixed_of_piC_mem (θ h) ?_ hv
  rw [hθ h]
  exact c.piC_of_mem_X hyX hy1

theorem coe_equivQ_conj (c : Loc41 G z) (n : ↥c.NXm) (q : ↥c.S.Q) :
    ((c.equivQ (CFSG.RankThree.Literature.FSmith.conjAut c.S.normal (n : ↥c.S.M) q) : ↥(Q z)) : G) =
      (n : G) * ((c.equivQ q : ↥(Q z)) : G) * (n : G)⁻¹ := by
  rw [c.coe_equivQ, CFSG.RankThree.Literature.FSmith.conjAut_apply, c.coe_equivQ]
  simp

theorem exists_mulEquiv_SQ_of_isometry
    (c : Loc49 G z) (c' : Loc49 G' z')
    (θ : ↥c.CX ≃* ↥c'.CX) (hθ : ∀ h, c'.piC (θ h) = c.piC h)
    (θN : ↥c.NX ≃* ↥c'.NX)
    (hext : ∀ h : ↥c.CX, ((θN ⟨h, c.CX_le_NX h.2⟩ : ↥c'.NX) : G') = (θ h : G'))
    (a : c.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (ha : ∀ v, c'.S.q (a v) = c.S.q v)
    (hequiv : ∀ (n : ↥c.NX) (v : c.S.Qt),
      a ((c.S.ρ (c.toSMN n) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v) =
        (c'.S.ρ (c'.toSMN (θN n)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (a v)) :
    ∃ θQ : ↥c.S.Q ≃* ↥c'.S.Q,
      (∀ q, a (c.S.toQt q) = c'.S.toQt (θQ q)) ∧
      ∀ (n : ↥c.NXm) (q : ↥c.S.Q),
        θQ (CFSG.RankThree.Literature.FSmith.conjAut c.S.normal (n : ↥c.S.M) q) =
          CFSG.RankThree.Literature.FSmith.conjAut c'.S.normal
            ((c.thetaNXm c'.toLoc41 θN n : ↥c'.NXm) : ↥c'.S.M) (θQ q) := by
  classical
  obtain ⟨x0, hx0ne, -⟩ := c.exists_x0_piC_hatM22Z
  let x : ↥c.S.M := c.toSM ⟨(x0 : G), c.X_le_CX x0.2⟩
  have hxN : x ∈ c.NXm := by
    rw [c.mem_NXm_iff]
    exact c.X_le_NX x0.2
  have hx1 : x ≠ 1 := by
    intro h
    refine hx0ne ?_
    have hcoe := congrArg (fun t : ↥c.S.M => (t : G)) h
    simpa [x, c.coe_toSM] using hcoe
  have hzp : Subgroup.zpowers x = c.X.subgroupOf c.S.M := c.zpowers_toSM x0.2 hx0ne
  have hXN : ∀ n ∈ c.NXm, n * x * n⁻¹ ∈ Subgroup.zpowers x := by
    intro n hn
    rw [hzp, Subgroup.mem_subgroupOf]
    have hcoe : ((n * x * n⁻¹ : ↥c.S.M) : G) = (n : G) * (x0 : G) * (n : G)⁻¹ := by
      simp [x, c.coe_toSM]
    rw [hcoe]
    exact (Subgroup.normal_subgroupOf_iff c.X_le_NX).mp c.X_normal_NX (x0 : G) (n : G)
      x0.2 (c.mem_NXm_iff.mp hn)
  have hfpf : ∀ y : ↥c.NXm, (y : c.S.M) ∈ Subgroup.zpowers x → y ≠ 1 →
      ∀ v : c'.S.Qt,
        (c'.S.ρ (c.thetaNXm c'.toLoc41 θN y) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) v = v → v = 0 := by
    intro y hyz hy1 v hv
    rw [hzp] at hyz
    have hyX : ((y : c.S.M) : G) ∈ c.X := Subgroup.mem_subgroupOf.mp hyz
    exact c.eq_zero_of_rho_thetaNXm c'.toLoc41 θ hθ θN hext hyX
      (fun h => hy1 (Subtype.ext (Subtype.ext h))) hv
  have hequiv' : ∀ (n : ↥c.NXm) (v : c.S.Qt),
      a ((c.S.ρ (n : c.S.M) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v) =
        (c'.S.ρ ((c.thetaNXm c'.toLoc41 θN n : ↥c'.NXm) : c'.S.M) :
          c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (a v) := by
    intro n v
    have h1 : (n : c.S.M) = c.toSMN ⟨(n : G), c.mem_NXm_iff.mp n.2⟩ := Subtype.ext rfl
    have h2 : ((c.thetaNXm c'.toLoc41 θN n : ↥c'.NXm) : c'.S.M) =
        c'.toSMN (θN ⟨(n : G), c.mem_NXm_iff.mp n.2⟩) := Subtype.ext rfl
    rw [h1, h2]
    exact hequiv _ v
  obtain ⟨θQ, hφa, hφc⟩ :=
    Setting.exists_mulEquiv_Q_of_isometry c.S c'.S (c.thetaNXm c'.toLoc41 θN) a ha hequiv'
      hxN hx1 hXN hfpf
  exact ⟨θQ, hφa, hφc⟩

end Loc41

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G}
variable {G' : Type} [Group G'] [Finite G'] {z' : G'}

theorem exists_mulEquiv_Q
    (c : Loc49 G z) (c' : Loc49 G' z')
    (θ : ↥c.CX ≃* ↥c'.CX) (hθ : ∀ h, c'.piC (θ h) = c.piC h)
    (θN : ↥c.NX ≃* ↥c'.NX)
    (hext : ∀ h : ↥c.CX, ((θN ⟨h, c.CX_le_NX h.2⟩ : ↥c'.NX) : G') = (θ h : G'))
    (a : c.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (ha : ∀ v, c'.S.q (a v) = c.S.q v)
    (hequiv : ∀ (n : ↥c.NX) (v : c.S.Qt),
      a ((c.S.ρ (c.toSMN n) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v) =
        (c'.S.ρ (c'.toSMN (θN n)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (a v)) :
    ∃ θQ : ↥(Q z) ≃* ↥(Q z'),
      ((θQ ⟨z, c.z_mem_Q⟩ : ↥(Q z')) : G') = z' ∧
      ∀ (n : ↥c.NX) (q : ↥(Q z)) (hq : (n : G) * (q : G) * (n : G)⁻¹ ∈ Q z),
        ((θQ ⟨(n : G) * (q : G) * (n : G)⁻¹, hq⟩ : ↥(Q z')) : G') =
          (θN n : G') * (θQ q : G') * (θN n : G')⁻¹ := by
  obtain ⟨θS, hφa, hφc⟩ :=
    Loc41.exists_mulEquiv_SQ_of_isometry c c' θ hθ θN hext a ha hequiv
  have hz : θS c.S.zQ = c'.S.zQ := by
    have h0 : c'.S.toQt (θS c.S.zQ) = 0 := by
      rw [← hφa c.S.zQ, (c.S.toQt_eq_zero_iff' c.S.zQ).mpr (Or.inr rfl), map_zero]
    rcases (c'.S.toQt_eq_zero_iff' (θS c.S.zQ)).mp h0 with h1 | h1
    · exact absurd h1 fun h1' => c.S.zQ_ne_one (θS.injective (by rw [h1', map_one]))
    · exact h1
  refine ⟨c.equivQG.trans (θS.trans c'.equivQ), ?_, ?_⟩
  · have h1 : (c.equivQG.trans (θS.trans c'.equivQ)) ⟨z, c.z_mem_Q⟩ =
        c'.equivQ c'.S.zQ := by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, c.equivQG_zQ, hz]
    rw [h1, c'.equivQ_zQ]
  · intro n q hq
    let nM : ↥c.NXm := (Subgroup.subgroupOfEquivOfLe c.NX_le_M).symm n
    let qS : ↥c.S.Q := c.equivQG q
    have hqS : c.equivQG ⟨(n : G) * (q : G) * (n : G)⁻¹, hq⟩ =
        CFSG.RankThree.Literature.FSmith.conjAut c.S.normal (nM : ↥c.S.M) qS := by
      apply Subtype.ext
      apply Subtype.ext
      rw [c.coe_equivQG, CFSG.RankThree.Literature.FSmith.conjAut_apply]
      simp [nM, qS]
    have hθN : (((c.thetaNXm c'.toLoc41 θN nM : ↥c'.NXm) : ↥c'.S.M) : G') = (θN n : G') :=
      congrArg (fun m : ↥c.NX => (θN m : G')) (Subtype.ext rfl)
    have hL : (((c.equivQG.trans (θS.trans c'.equivQ))
          ⟨(n : G) * (q : G) * (n : G)⁻¹, hq⟩ : ↥(Q z')) : G') =
        (θN n : G') * ((c'.equivQ (θS qS) : ↥(Q z')) : G') * (θN n : G')⁻¹ := by
      have h1 : (c.equivQG.trans (θS.trans c'.equivQ))
            ⟨(n : G) * (q : G) * (n : G)⁻¹, hq⟩ =
          c'.equivQ (θS (CFSG.RankThree.Literature.FSmith.conjAut c.S.normal
            (nM : ↥c.S.M) qS)) := by
        rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hqS]
      rw [h1, hφc nM qS, c'.coe_equivQ_conj, hθN]
    have hR : (((c.equivQG.trans (θS.trans c'.equivQ)) q : ↥(Q z')) : G') =
        ((c'.equivQ (θS qS) : ↥(Q z')) : G') := by
      have h1 : (c.equivQG.trans (θS.trans c'.equivQ)) q = c'.equivQ (θS qS) := by
        rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
      rw [h1]
    rw [hL, hR]

theorem exists_mulEquiv_G3_of_NX
    (c : Loc49 G z) (c' : Loc49 G' z')
    (θ : ↥c.CX ≃* ↥c'.CX) (hθ : ∀ h, c'.piC (θ h) = c.piC h) (θN : ↥c.NX ≃* ↥c'.NX)
    (hext : ∀ h : ↥c.CX, ((θN ⟨h, c.CX_le_NX h.2⟩ : ↥c'.NX) : G') = (θ h : G')) :
    Nonempty (↥c.G3 ≃* ↥c'.G3) := by
  obtain ⟨a, ha, hequiv⟩ := c.exists_isometry_NX c' θ hθ θN hext
  obtain ⟨θQ, hQz, hQconj⟩ := c.exists_mulEquiv_Q c' θ hθ θN hext a ha hequiv
  have hN : c.NX ≤ Subgroup.normalizer (Q z : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact c.Q_normal_H n hn.1 q hq
    · intro hq
      have h := c.Q_normal_H n⁻¹ ((H z).inv_mem hn.1) (n * q * n⁻¹) hq
      have he : n⁻¹ * (n * q * n⁻¹) * n⁻¹⁻¹ = q := by group
      rwa [he] at h
  have hN' : c'.NX ≤ Subgroup.normalizer (Q z' : Set G') := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact c'.Q_normal_H n hn.1 q hq
    · intro hq
      have h := c'.Q_normal_H n⁻¹ ((H z').inv_mem hn.1) (n * q * n⁻¹) hq
      have he : n⁻¹ * (n * q * n⁻¹) * n⁻¹⁻¹ = q := by group
      rwa [he] at h
  have hagree : ∀ (x : G) (hxQ : x ∈ Q z) (hxN : x ∈ c.NX),
      ((θQ ⟨x, hxQ⟩ : ↥(Q z')) : G') = θN ⟨x, hxN⟩ := by
    intro x hxQ hxN
    have hxz : x ∈ Subgroup.zpowers z := by
      rw [← c.inf_Q_NX]
      exact ⟨hxQ, hxN⟩
    rcases eq_one_or_of_mem_zpowers_of_orderOf_eq_two c.z_orderOf hxz with h1 | hz
    · have hQ1 : (⟨x, hxQ⟩ : ↥(Q z)) = 1 := Subtype.ext h1
      have hN1 : (⟨x, hxN⟩ : ↥c.NX) = 1 := Subtype.ext h1
      simp [hQ1, hN1]
    · have hQz' : (⟨x, hxQ⟩ : ↥(Q z)) = ⟨z, c.z_mem_Q⟩ := Subtype.ext hz
      have hNz' : (⟨x, hxN⟩ : ↥c.NX) =
          ⟨z, c.CX_le_NX c.z_mem_CX⟩ := Subtype.ext hz
      rw [hQz', hQz, hNz', hext ⟨z, c.z_mem_CX⟩, mulEquiv_CX_maps_z c c' θ hθ]
  have hback : ∀ n : ↥c.NX, (θN n : G') ∈ Q z' → (n : G) ∈ Q z := by
    intro n hnQ
    have hmem : (θN n : G') ∈ Subgroup.zpowers z' := by
      rw [← c'.inf_Q_NX]
      exact ⟨hnQ, (θN n).2⟩
    rcases eq_one_or_of_mem_zpowers_of_orderOf_eq_two c'.z_orderOf hmem with h1 | hz
    · have hn1 : n = 1 := θN.injective (by
        rw [show θN n = 1 from Subtype.ext h1, map_one])
      rw [hn1]
      exact (Q z).one_mem
    · have hzn : n = (⟨z, c.CX_le_NX c.z_mem_CX⟩ : ↥c.NX) := by
        apply θN.injective
        apply Subtype.ext
        rw [hext ⟨z, c.z_mem_CX⟩, mulEquiv_CX_maps_z c c' θ hθ]
        exact hz
      rw [hzn]
      exact c.z_mem_Q
  obtain ⟨ζ, -, -⟩ :=
    CFSG.GroupTheory.exists_mulEquiv_sup_glue hN hN' θQ θN hagree hback hQconj
  exact ⟨(MulEquiv.subgroupCongr c.H_eq_sup_NX).trans
    (ζ.trans (MulEquiv.subgroupCongr c'.H_eq_sup_NX.symm))⟩

theorem exists_mulEquiv_G3
    {W : Type} [Group W] [Finite W] {M : Subgroup W} {T : W}
    (hmod : CFSG.Quasithin.TwoM22.IsTwoM22TwoModel M T)
    {G : Type} [Group G] [Finite G] {z : G} {G' : Type} [Group G'] [Finite G'] {z' : G'}
    (c : Loc49 G z) (c' : Loc49 G' z') : Nonempty (↥c.G3 ≃* ↥c'.G3) := by
  obtain ⟨θ, hθ⟩ := c.exists_mulEquiv_CX c'
  obtain ⟨θN, hext⟩ := c.exists_mulEquiv_NX c' (c'.mul_self_eq_one_of_mem_NX hmod) θ
  exact c.exists_mulEquiv_G3_of_NX c' θ hθ θN hext

end Loc49

theorem stmt8_3_of_model
    {W : Type} [Group W] [Finite W] {M : Subgroup W} {T : W}
    (hmod : CFSG.Quasithin.TwoM22.IsTwoM22TwoModel M T) : Stmt8_3 := by
  intro G _ _ z hJ c G' _ _ z' hJ' c' y y' hy hyx hy' hyx'
  obtain ⟨ζ₀⟩ := c.exists_mulEquiv_G3 hmod c'
  obtain ⟨ζ, h1, h2⟩ :=
    Loc49.exists_stmt8_3_of_mulEquiv
      (stmt5_lineU_of_2c stmt5_2c_holds) (stmt5_gamma2_of_2c stmt5_2c_holds)
      hJ c (resM24_holds G z hJ c).some hJ' c' (resM24_holds G' z' hJ' c').some ζ₀
      hy hyx hy' hyx'
  exact ⟨ζ, h1, h2⟩

end CFSG.Quasithin.H13.AS91
