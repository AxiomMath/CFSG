module

public import CFSG.RankThree.GF2n.Stroth80.Sec96WCaseA
import CFSG.GroupTheory.CommutatorLeSubgroupOf
import CFSG.RankThree.GF2n.Stroth80.Sec97FiveLineX
import CFSG.RankThree.GF2n.Stroth80.Sec97FivePoint

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Quasithin.G11.P3Ortho.Om4
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem uline_le_sup_inf_QB_of_eq_X_or_Y (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y S : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (hS : S = X ∨ S = Y) :
    Uline Z B S ≤ (Vt M (LB M Q B) B Z t ⊓ QB B) ⊔ Z := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hSR : S ≤ Rt M (LB M Q B) t := by
    rcases hS with rfl | rfl
    · exact hsplit.1.2.1
    · exact hsplit.1.2.2.2.1
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, hK, hrange, hker, hnorm, hψ, hBiff, hflag, hdet, hu0⟩ :=
    sec9_coord h34 hc hs
  haveI := hn
  haveI : CharP K 2 := chK
  have hfac := sec97_factor_pair h34 h311a hc hs hsplit hK φ hrange hker
  set H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
    (S.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) with hHdef
  have hHS : H = leftF K ∨ H = rightF K := by
    rcases hfac with ⟨hY, hX⟩ | ⟨hY, hX⟩
    · rcases hS with rfl | rfl
      · exact Or.inr (by rw [hHdef, hX])
      · exact Or.inl (by rw [hHdef, hY])
    · rcases hS with rfl | rfl
      · exact Or.inl (by rw [hHdef, hX])
      · exact Or.inr (by rw [hHdef, hY])
  have hHmem : ∀ h, h ∈ H ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ S ∧ Ψ K (φ s) = h := by
    intro h
    simp only [hHdef, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  obtain ⟨Φ, w₀, hA, hw₀, hu⟩ := natural_module_data (H := H) hHS hdet hu0
  have hdetH : ∀ h ∈ H, ∀ X : Matrix (Fin 2) (Fin 2) K, (h X).det = X.det := by
    intro h hh X
    rcases hHS with hf | hf <;> rw [hf] at hh
    · obtain ⟨A, rfl⟩ := hh
      show (rho' K (A, 1) X).det = X.det
      rw [rho'_inl_apply, Matrix.det_mul, A.det_coe, one_mul]
    · obtain ⟨B', rfl⟩ := hh
      show (rho' K (1, B') X).det = X.det
      rw [rho'_inr_apply, Matrix.det_mul, (B'⁻¹).det_coe, mul_one]
  have hdetΦ : ∀ w, (Φ w).det = 0 := by
    intro w
    by_cases hw : w = 0
    · rw [hw, map_zero]
      simp
    · obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq hw₀ hw
      obtain ⟨h, hh, hact⟩ := hA.lift g
      have hΦw : Φ w = h (Φ w₀) := by rw [hact, hg]
      rw [hΦw, hdetH h ((hHmem h).mpr hh) (Φ w₀), ← hu]
      exact hdet
  have hQdet : ∀ v, quadPlus 2 K v = (toMat K v).det := fun v =>
    (congrFun (coe_quadPlus 2 K) v).trans (det_toMat K v).symm
  intro x hx
  obtain ⟨hxV, w', hw'⟩ :=
    (uline_mem_iff ψ φ hψ hnorm hSR hZV hBV u hBiff hHmem hA hw₀ hu x).mp hx
  have hx' : toMat K (secVec ψ ⟨x, hxV⟩) = Φ w' := hw'.symm
  have hpolar : polar (quadPlus 2 K) u (secVec ψ ⟨x, hxV⟩) = 0 := by
    show quadPlus 2 K (u + secVec ψ ⟨x, hxV⟩) - quadPlus 2 K u -
      quadPlus 2 K (secVec ψ ⟨x, hxV⟩) = 0
    rw [hQdet, hQdet, hQdet, map_add, hu, hx', ← map_add, hdetΦ, hdetΦ, hdetΦ]
    simp
  obtain ⟨w, hwmem, hwsv⟩ := (hflag _).mpr hpolar
  have hz : x * (w : G)⁻¹ ∈ Z := (secVec_eq_iff ψ ⟨x, hxV⟩ w).mp hwsv.symm
  have hxe : x = (x * (w : G)⁻¹) * (w : G) := by group
  rw [hxe, sup_comm]
  exact Subgroup.mul_mem_sup hz hwmem

private theorem sq_eq_one_of_isConjB (hc : Ctx M Q Z B) {t g b : G} (hb : b ∈ B)
    (hgt : g * t * g⁻¹ = b) : t ^ 2 = 1 := by
  have hb2 : b ^ 2 = 1 := hc.isElemAbelian_B.2 b hb
  have h1 : g * t ^ 2 * g⁻¹ = 1 := by
    rw [show g * t ^ 2 * g⁻¹ = (g * t * g⁻¹) ^ 2 by
      rw [pow_two, pow_two]
      group, hgt, hb2]
  have h2 := congrArg (fun x => g⁻¹ * x * g) h1
  simpa [mul_assoc] using h2

private theorem zpow_comm_mem_Z_of_sq_eq_one {t δ : G} (ht2 : t ^ 2 = 1) (Z : Subgroup G)
    (htd : ⁅t, δ⁆ ∈ Z) : ∀ k : ℤ, ⁅t ^ k, δ⁆ ∈ Z := by
  intro k
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact ht2
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · rw [hk, zpow_zero]
    simp
  · rw [hk, zpow_one]
    exact htd

private theorem comm_mem_Wt_of_mem_X (h34 : Stroth34Statement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X : Subgroup G} (hXR : X ≤ Rt M (LB M Q B) t)
    (ht2 : t ^ 2 = 1) {x : G} (hx : x ∈ X) :
    ⁅x, t⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hWQ1 := (hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 ht hs5.notQ
    (sec9_notQB h34 hs)).2
  have hxR : x ∈ Rt M (LB M Q B) t := hXR hx
  have hdQ : ⁅x, t⁆ ∈ Q := hc.Rt_comm_mem_Q hxR
  have hxt : x * t * x⁻¹ = ⁅x, t⁆ * t := by
    rw [commutatorElement_def]
    group
  have hsq : (⁅x, t⁆ * t) * (⁅x, t⁆ * t) = 1 := by
    rw [← hxt]
    have e : (x * t * x⁻¹) * (x * t * x⁻¹) = x * t ^ 2 * x⁻¹ := by
      rw [pow_two]
      group
    rw [e, ht2]
    group
  have hconj : t * ⁅x, t⁆ * t = ⁅x, t⁆⁻¹ := by
    have h5 : ⁅x, t⁆⁻¹ * (⁅x, t⁆ * t * (⁅x, t⁆ * t)) = ⁅x, t⁆⁻¹ := by
      rw [hsq, mul_one]
    rwa [show ⁅x, t⁆⁻¹ * (⁅x, t⁆ * t * (⁅x, t⁆ * t)) = t * ⁅x, t⁆ * t by group] at h5
  have hconj' : t * ⁅x, t⁆ * t⁻¹ = ⁅x, t⁆⁻¹ := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht2)
    rw [htinv]
    exact hconj
  have htdZ : ⁅t, ⁅x, t⁆⁆ ∈ Z := by
    rw [commutatorElement_def, hconj', ← mul_inv_rev, ← pow_two]
    exact Z.inv_mem (CFSG.RankThree.GF2n.Smith81.sq_mem_Z hc.hyp hdQ)
  have hcomm : ∀ s ∈ Subgroup.zpowers t, ⁅s, ⁅x, t⁆⁆ ∈ Z := by
    intro s hs
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact zpow_comm_mem_Z_of_sq_eq_one ht2 Z htdZ j
  have hmem : ⁅x, t⁆ ∈ Q1 hc t := by
    show ⁅x, t⁆ ∈ CQtGrp hc (Subgroup.zpowers t)
    rw [mem_CQtGrp]
    exact ⟨hdQ, hcomm⟩
  rw [hWQ1]
  exact hmem

private theorem conjSubgroup_sup_Z_eq_of_comm_mem_Z {Z H : Subgroup G} {g : G}
    (hcomm : ∀ h ∈ H, ⁅g, h⁆ ∈ Z) : conjSubgroup g H ⊔ Z = H ⊔ Z := by
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
  · intro x hx
    rw [mem_conjSubgroup] at hx
    have e : x = ⁅g, g⁻¹ * x * g⁆ * (g⁻¹ * x * g) := by
      rw [commutatorElement_def]
      group
    have hmem : ⁅g, g⁻¹ * x * g⁆ * (g⁻¹ * x * g) ∈ Z ⊔ H :=
      Subgroup.mul_mem_sup (hcomm _ hx) hx
    rw [sup_comm] at hmem
    rwa [← e] at hmem
  · intro x hx
    have hx' : g * x * g⁻¹ ∈ conjSubgroup g H := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hx
    have e : x = ⁅g, x⁆⁻¹ * (g * x * g⁻¹) := by
      rw [commutatorElement_def]
      group
    have hmem : ⁅g, x⁆⁻¹ * (g * x * g⁻¹) ∈ Z ⊔ conjSubgroup g H :=
      Subgroup.mul_mem_sup (Z.inv_mem (hcomm x hx)) hx'
    rw [sup_comm] at hmem
    rwa [← e] at hmem

private theorem comm_mul_mem_of_comm_mem {V W X : Subgroup G} {t : G}
    (hδW : ∀ x ∈ X, ⁅x, t⁆ ∈ W) (hXV : ∀ x ∈ X, ∀ w ∈ W, ⁅x, w⁆ ∈ V)
    (hWW : ⁅W, W⁆ ≤ V) {a b : G} (ha : a ∈ X) (hb : b ∈ X) :
    ⁅a * b, t⁆ * (⁅a, t⁆ * ⁅b, t⁆)⁻¹ ∈ V := by
  have e : ⁅a * b, t⁆ = ⁅a, ⁅b, t⁆⁆ * ⁅b, t⁆ * ⁅a, t⁆ := by
    rw [commutatorElement_def]
    group
  rw [e]
  have h1 : ⁅a, ⁅b, t⁆⁆ ∈ V := hXV a ha _ (hδW b hb)
  have h2 : ⁅⁅b, t⁆, ⁅a, t⁆⁆ ∈ V :=
    hWW (Subgroup.commutator_mem_commutator (hδW b hb) (hδW a ha))
  have e2 : (⁅a, ⁅b, t⁆⁆ * ⁅b, t⁆ * ⁅a, t⁆) * (⁅a, t⁆ * ⁅b, t⁆)⁻¹ =
      ⁅a, ⁅b, t⁆⁆ * ⁅⁅b, t⁆, ⁅a, t⁆⁆ := by
    rw [commutatorElement_def]
    group
  rw [e2]
  exact V.mul_mem h1 h2

private theorem comm_mem_Vt_of_mem_commutator (h34 : Stroth34Statement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (ht2 : t ^ 2 = 1) {k : G}
    (hk : k ∈ ⁅X, X⁆) : ⁅k, t⁆ ∈ Vt M (LB M Q B) B Z t := by
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, -, hXV⟩ := hsplit
  set V := Vt M (LB M Q B) B Z t with hV
  set W := Wt Q V with hW
  have hδW : ∀ x ∈ X, ⁅x, t⁆ ∈ W := fun x hx =>
    comm_mem_Wt_of_mem_X h34 hc hs hXR ht2 hx
  have hVW : V ≤ W := HS6.Vt_le_Wt h34 hc hs.toSec5
  have hWQ : W ≤ Q := by rw [hW]; exact inf_le_left
  have hWW : ⁅W, W⁆ ≤ V :=
    (Subgroup.commutator_mono hWQ hWQ).trans
      ((Subgroup.commutator_le.mpr fun a ha b hb => hc.hyp.toHyp79.comm_mem_V ha hb).trans
        (by rw [hV]; exact sec39_Z_le_Vt))
  have hnorm : (V.subgroupOf W).Normal :=
    CFSG.GroupTheory.normal_subgroupOf_of_commutator_le hWW
  haveI : (V.subgroupOf W).Normal := hnorm
  have hVnorm : ∀ v ∈ V, ∀ w ∈ W, w * v * w⁻¹ ∈ V := by
    intro v hv w hw
    exact Subgroup.mem_subgroupOf.mp
      (hnorm.conj_mem ⟨v, hVW hv⟩ (Subgroup.mem_subgroupOf.mpr hv) ⟨w, hw⟩)
  haveI : IsMulCommutative (↥W ⧸ V.subgroupOf W) :=
    CFSG.GroupTheory.isMulCommutative_quotient_subgroupOf_of_commutator_le hWW
  have hδadd : ∀ a ∈ X, ∀ b ∈ X, ⁅a * b, t⁆ * (⁅a, t⁆ * ⁅b, t⁆)⁻¹ ∈ V :=
    fun a ha b hb => comm_mul_mem_of_comm_mem hδW hXV hWW ha hb
  let F : ↥X →* ↥W ⧸ V.subgroupOf W :=
    { toFun := fun x => QuotientGroup.mk' (V.subgroupOf W) ⟨⁅(x : G), t⁆, hδW x.1 x.2⟩
      map_one' := by
        have h1 : (⟨⁅((1 : ↥X) : G), t⁆, hδW 1 X.one_mem⟩ : ↥W) = 1 := by
          ext
          simp
        rw [h1, map_one]
      map_mul' := fun a b => by
        show QuotientGroup.mk' (V.subgroupOf W) ⟨⁅((a * b : ↥X) : G), t⁆,
            hδW (a * b).1 (a * b).2⟩ =
          QuotientGroup.mk' (V.subgroupOf W) ⟨⁅(a : G), t⁆, hδW a.1 a.2⟩ *
            QuotientGroup.mk' (V.subgroupOf W) ⟨⁅(b : G), t⁆, hδW b.1 b.2⟩
        rw [← map_mul]
        refine (QuotientGroup.eq (s := V.subgroupOf W)).mpr ?_
        have hq := hδadd a.1 a.2 b.1 b.2
        have hqG : (⁅(a : G), t⁆ * ⁅(b : G), t⁆)⁻¹ *
            (⁅((a * b : ↥X) : G), t⁆ * (⁅(a : G), t⁆ * ⁅(b : G), t⁆)⁻¹)⁻¹ *
              (⁅(a : G), t⁆ * ⁅(b : G), t⁆)⁻¹⁻¹ ∈ V :=
          hVnorm _ (V.inv_mem hq) _ (W.inv_mem (W.mul_mem (hδW a.1 a.2) (hδW b.1 b.2)))
        rw [inv_inv] at hqG
        have hq' : (⁅((a * b : ↥X) : G), t⁆)⁻¹ *
            (⁅(a : G), t⁆ * ⁅(b : G), t⁆) ∈ V := by
          rwa [show (⁅(a : G), t⁆ * ⁅(b : G), t⁆)⁻¹ *
              (⁅((a * b : ↥X) : G), t⁆ * (⁅(a : G), t⁆ * ⁅(b : G), t⁆)⁻¹)⁻¹ *
                (⁅(a : G), t⁆ * ⁅(b : G), t⁆) =
              (⁅((a * b : ↥X) : G), t⁆)⁻¹ *
                (⁅(a : G), t⁆ * ⁅(b : G), t⁆) by group] at hqG
        rw [Subgroup.mem_subgroupOf]
        exact hq' }
  have hker_le : ⁅X, X⁆ ≤ (F.ker).map X.subtype := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    refine Subgroup.mem_map.mpr ⟨⟨⁅a, b⁆,
      Subgroup.commutator_le_self X (Subgroup.commutator_mem_commutator ha hb)⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    have e : F ⟨⁅a, b⁆,
        Subgroup.commutator_le_self X (Subgroup.commutator_mem_commutator ha hb)⟩ =
        ⁅F ⟨a, ha⟩, F ⟨b, hb⟩⁆ := by
      rw [show (⟨⁅a, b⁆,
          Subgroup.commutator_le_self X (Subgroup.commutator_mem_commutator ha hb)⟩ : ↥X) =
          ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ by exact Subtype.ext rfl]
      simp only [map_mul, map_inv]
      rfl
    rw [e, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' _ _
  obtain ⟨y, hyker, hyk⟩ := Subgroup.mem_map.mp (hker_le hk)
  have hy1 : QuotientGroup.mk' (V.subgroupOf W) ⟨⁅(y : G), t⁆, hδW y.1 y.2⟩ = 1 :=
    MonoidHom.mem_ker.mp hyker
  have hyV : ⁅(y : G), t⁆ ∈ V := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hy1)
  exact hyk ▸ hyV

private theorem exists_mem_commutator_mul_mem_CN (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) {x : G} (hx : x ∈ X) :
    ∃ k ∈ ⁅X, X⁆, k⁻¹ * x ∈ hc.CN t := by
  classical
  have hXR : X ≤ Rt M (LB M Q B) t := hsplit.1.2.1
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, hK, hrange, hker, hnorm, hψ, hBiff, hflag, hdet, hu0⟩ :=
    sec9_coord h34 hc hs
  haveI := hn
  haveI : CharP K 2 := chK
  let φ'' : ↥(Rt M (LB M Q B) t) →*
      (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) := (Ψ K).toMonoidHom.comp φ
  have hφ''1 : ∀ s : ↥(Rt M (LB M Q B) t), φ'' s = 1 ↔ (s : G) ∈ hc.CN t := by
    intro s
    show Ψ K (φ s) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hfac := sec97_factor_pair h34 h311a hc hs hsplit hK φ hrange hker
  let f : ↥X →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
    φ''.comp (Subgroup.inclusion hXR)
  have hfr : f.range = (X.subgroupOf (Rt M (LB M Q B) t)).map φ'' := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨z, hXR z.2⟩, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have hfr' : f.range = leftF K ∨ f.range = rightF K := by
    rw [hfr]
    rcases hfac with ⟨-, hX⟩ | ⟨-, hX⟩
    · exact Or.inr hX
    · exact Or.inl hX
  haveI : Group.IsPerfect f.range := by
    have hq4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
    have hSL := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hq4
    haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K ×
        Matrix.SpecialLinearGroup (Fin 2) K) := isPerfect_prod hSL hSL
    rcases hfr' with h | h
    · rw [h]
      exact Group.IsPerfect.range ((rho' K).comp (MonoidHom.inl _ _))
    · rw [h]
      exact Group.IsPerfect.range ((rho' K).comp (MonoidHom.inr _ _))
  have hmap : f.range = (commutator ↥X).map f := by
    rw [map_commutator_eq, Subgroup.commutator_eq_self]
  have hxmem : f ⟨x, hx⟩ ∈ (commutator ↥X).map f := by
    rw [← hmap]
    exact MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨y, hy, hyf⟩ := Subgroup.mem_map.mp hxmem
  refine ⟨(y : G), ?_, ?_⟩
  · have hkmap : (y : G) ∈ (commutator ↥X).map X.subtype :=
      Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    rwa [Subgroup.map_subtype_commutator] at hkmap
  · have h1 : φ'' ⟨(y : G), hXR y.2⟩ = φ'' ⟨x, hXR hx⟩ := hyf
    have h2 : φ'' (⟨(y : G), hXR y.2⟩⁻¹ * ⟨x, hXR hx⟩) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := (hφ''1 _).mp h2
    simpa using h3

private theorem exists_conj_not_le_sup_Z (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) :
    ∃ x ∈ X, ¬ conjSubgroup x B ≤ (B ⊔ Z : Subgroup G) := by
  by_contra hno
  push Not at hno
  have hle : Uline Z B X ≤ (B ⊔ Z : Subgroup G) := sup_le le_sup_right (iSup₂_le hno)
  have hcard := Subgroup.card_le_of_le hle
  rw [(ulineX_data h34 h311a hc hs hsplit).1] at hcard
  have hBZ : Nat.card ↥(B ⊔ Z : Subgroup G) = Nat.card Z ^ 2 := by
    have h := card_conj_sup_Z hc (m := 1) M.one_mem
    rwa [conjSubgroup_one] at h
  rw [hBZ] at hcard
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have h3 : Nat.card Z * Nat.card Z * Nat.card Z ≤ Nat.card Z * Nat.card Z * 1 := by
    calc Nat.card Z * Nat.card Z * Nat.card Z = Nat.card Z ^ 3 := by ring
      _ ≤ Nat.card Z ^ 2 := hcard
      _ = Nat.card Z * Nat.card Z * 1 := by ring
  have h1 := Nat.le_of_mul_le_mul_left h3 (by positivity)
  omega

private theorem exists_conj_eq_of_comm_mem_Vt (h34 : Stroth34Statement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    (hB : ¬ CaseA Q Z t) {k : G} (hkV : ⁅k, t⁆ ∈ Vt M (LB M Q B) B Z t) :
    ∃ c ∈ Q, k * t * k⁻¹ = c * t * c⁻¹ := by
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hchi := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 ht hs5.notQ (sec9_notQB h34 hs)
  have hD := hc.natCommData ht hchi.1 hchi.2
  obtain ⟨y, hyQ, hyz⟩ := hD.lift ⁅k, t⁆ hkV
  set δ := ⁅k, t⁆ with hδ
  set z := ⁅y, t⁆ * δ⁻¹ with hz
  have hzZ : z ∈ Z := hyz
  have hδeq : δ = z⁻¹ * ⁅y, t⁆ := by
    rw [hz]
    group
  have hyt : ⁅y, t⁆ * t = y * t * y⁻¹ := by
    rw [commutatorElement_def]
    group
  have hkt : k * t * k⁻¹ = δ * t := by
    rw [hδ, commutatorElement_def]
    group
  have hzt : t * z⁻¹ = z⁻¹ * t := by
    have h := hc.LB_centralizes_Z ht z⁻¹ (Z.inv_mem hzZ)
    calc t * z⁻¹ = (t * z⁻¹ * t⁻¹) * t := by group
      _ = z⁻¹ * t := by rw [h]
  have hzy : y * z⁻¹ = z⁻¹ * y := hc.Z_central (Z.inv_mem hzZ) hyQ
  have hkey0 : k * t * k⁻¹ = z⁻¹ * (y * t * y⁻¹) := by
    rw [hkt, hδeq, mul_assoc, hyt]
  have hkey : k * t * k⁻¹ = y * (t * z⁻¹) * y⁻¹ := by
    rw [hkey0]
    calc z⁻¹ * (y * t * y⁻¹) = (z⁻¹ * y) * t * y⁻¹ := by group
      _ = (y * z⁻¹) * t * y⁻¹ := by rw [← hzy]
      _ = y * (z⁻¹ * t) * y⁻¹ := by group
      _ = y * (t * z⁻¹) * y⁻¹ := by rw [← hzt]
  have hnotA : ∀ w ∈ Z, ∃ y' ∈ Q, y' * t * y'⁻¹ = t * w := by
    intro w hw
    by_contra hcon
    push Not at hcon
    exact hB ⟨w, hw, hcon⟩
  obtain ⟨y', hy'Q, hy't⟩ := hnotA z⁻¹ (Z.inv_mem hzZ)
  refine ⟨y * y', Q.mul_mem hyQ hy'Q, ?_⟩
  rw [show (y * y') * t * (y * y')⁻¹ = y * (y' * t * y'⁻¹) * y⁻¹ by group, hy't]
  exact hkey

theorem wPointConcl_of_not_caseA (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (hB : ¬ CaseA Q Z t) :
    WPointConcl M Q Z B t := by
  classical
  intro htconj hBt
  obtain ⟨g, b, hb, hgt⟩ := htconj
  have hXR : X ≤ Rt M (LB M Q B) t := hsplit.1.2.1
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have ht2 : t ^ 2 = 1 := sq_eq_one_of_isConjB hc hb hgt
  obtain ⟨x, hxX, hxnot⟩ := exists_conj_not_le_sup_Z h34 h311a hc hs hsplit
  obtain ⟨k, hkcomm, hkxN⟩ :=
    exists_mem_commutator_mul_mem_CN h34 h311a hc hs hsplit hxX
  have hkX : k ∈ X := Subgroup.commutator_le_self X hkcomm
  have hkR : k ∈ Rt M (LB M Q B) t := hXR hkX
  have hkV : ⁅k, t⁆ ∈ Vt M (LB M Q B) B Z t :=
    comm_mem_Vt_of_mem_commutator h34 hc hs hsplit ht2 hkcomm
  obtain ⟨c, hcQ, hck⟩ := exists_conj_eq_of_comm_mem_Vt h34 hc hs hB hkV
  set h := c⁻¹ * k with hh
  have hhQ : c⁻¹ ∈ Q := Q.inv_mem hcQ
  have hhM : h ∈ M := M.mul_mem (hc.hyp.Q_normal.1 hhQ) (hc.Rt_le_M t hkR)
  have hht : h * t = t * h := by
    have h1 : h * t * h⁻¹ = t := by
      rw [hh]
      calc c⁻¹ * k * t * (c⁻¹ * k)⁻¹ = c⁻¹ * (k * t * k⁻¹) * c := by group
        _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [hck]
        _ = t := by group
    calc h * t = (h * t * h⁻¹) * h := by group
      _ = t * h := by rw [h1]
  set nn := k⁻¹ * x with hnn
  have hxkn : x = k * nn := by rw [hnn]; group
  have hniZ : ∀ b ∈ B, ⁅nn, b⁆ ∈ Z := fun b hb =>
    (Ctx.mem_CN.mp hkxN).2 b (hc.B_le_Vt ht hb)
  have hnn_sup : conjSubgroup nn B ⊔ Z = B ⊔ Z :=
    conjSubgroup_sup_Z_eq_of_comm_mem_Z hniZ
  have hkBQ : conjSubgroup k B ≤ Q := by
    calc conjSubgroup k B ≤ conjSubgroup k Q := Subgroup.map_mono hc.le
      _ = Q := hc.conj_Q_eq (hc.Rt_le_M t hkR)
  have hcZ : ∀ b ∈ conjSubgroup k B, ⁅c⁻¹, b⁆ ∈ Z := fun b hb =>
    hc.hyp.toHyp79.comm_mem_V hhQ (hkBQ hb)
  have hc_sup : conjSubgroup c⁻¹ (conjSubgroup k B) ⊔ Z = conjSubgroup k B ⊔ Z :=
    conjSubgroup_sup_Z_eq_of_comm_mem_Z hcZ
  have hkZ : conjSubgroup k Z = Z := hc.conj_Z_eq (hc.Rt_le_M t hkR)
  have hk_sup : conjSubgroup k (conjSubgroup nn B) ⊔ Z = conjSubgroup k B ⊔ Z := by
    have h1 : conjSubgroup k (conjSubgroup nn B) ⊔ conjSubgroup k Z =
        conjSubgroup k B ⊔ conjSubgroup k Z := by
      simp only [conjSubgroup]
      rw [← Subgroup.map_sup, ← Subgroup.map_sup]
      exact congrArg (Subgroup.map (MulAut.conj k).toMonoidHom) hnn_sup
    rwa [hkZ] at h1
  have hCZ : conjSubgroup h B ⊔ Z = conjSubgroup x B ⊔ Z := by
    rw [hh, conjSubgroup_mul, hxkn, conjSubgroup_mul, hc_sup, hk_sup]
  have hCQ : conjSubgroup h B ≤ Q ⊓ QB (Subgroup.zpowers t) := by
    intro y hy
    rw [mem_conjSubgroup] at hy
    have hb' : h⁻¹ * y * h ∈ Q ⊓ QB (Subgroup.zpowers t) := ⟨hc.le hy, hBt hy⟩
    have hres := caseA_conj_P hc hhM hht hb'
    rwa [show h * (h⁻¹ * y * h) * h⁻¹ = y by group] at hres
  have hCUline : conjSubgroup h B ⊔ Z ≤ Uline Z B X := by
    rw [hCZ]
    refine sup_le ?_ (le_sup_left : Z ≤ Uline Z B X)
    intro y hy
    exact conjSubgroup_le_Uline (Z := Z) hxX hy
  have hflag := uline_le_sup_inf_QB_of_eq_X_or_Y h34 h311a hc hs hsplit (Or.inl rfl)
  have hCQB : conjSubgroup h B ≤ QB B := by
    refine le_trans (le_sup_left : conjSubgroup h B ≤ conjSubgroup h B ⊔ Z) ?_
    exact hCUline.trans (hflag.trans (sup_le inf_le_right hc.Z_le_QB.1))
  have hCne : conjSubgroup h B ≠ B := by
    intro heq
    apply hxnot
    have h1 : conjSubgroup x B ⊔ Z = B ⊔ Z := by rw [← hCZ, heq]
    exact le_trans le_sup_left (le_of_eq h1)
  exact ⟨conjSubgroup h B, ⟨h, hhM, rfl⟩, hCne, le_inf hCQ hCQB⟩

end HS9

theorem sec96WCaseB_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement) :
    Sec96WCaseBStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit _ _ hB
  exact HS9.wPointConcl_of_not_caseA h34 h311a hc hs hsplit hB

theorem sec96W_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement) : Sec96WStatement :=
  sec96W_of_caseB h34 h311a (sec96WCaseB_of h34 h311a)

end CFSG.RankThree.GF2n.Stroth80
