module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjKappa

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Stmt


@[expose] def Sec715AdjStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 4 → n = 16 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ g ∈ M, conjSubgroup g Z0 ≤ LB M Q B → ¬ conjSubgroup g Z0 ≤ hc.CN t →
      ∃ x ∈ hc.CN t, ∃ s ∈ Z0, s ∉ Q ∧ ⁅x, g * s * g⁻¹⁆ ∉ Q ∧
        ⁅x, g * s * g⁻¹⁆ ∈ LB M Q B ∧ ⁅x, g * s * g⁻¹⁆ ∈ conjSubgroup g (hc.CN t)

end Stmt

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conj_CN_eq_of_normalizer (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {k : G} (hkM : k ∈ M)
    (hkN : k ∈ Subgroup.normalizer (Z0 : Set G)) : conjSubgroup k (hc.CN t) = hc.CN t := by
  obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  have hs' : k * s * k⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hkN s).mp hsZ0
  have hs'Q : k * s * k⁻¹ ∉ Q := by
    intro h
    apply hsQ
    have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hkM)) _).mp h
    simpa [mul_assoc] using h2
  obtain ⟨hR1, hV1⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 s hsZ0 hsQ
  obtain ⟨hR2, hV2⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 (k * s * k⁻¹) hs' hs'Q
  have hR : conjSubgroup k (Rt M (LB M Q B) t) = Rt M (LB M Q B) t := by
    calc conjSubgroup k (Rt M (LB M Q B) t) = conjSubgroup k (Rt M (LB M Q B) s) := by rw [hR1]
      _ = Rt M (LB M Q B) (k * s * k⁻¹) := conjSubgroup_Rt_eq hkM s
      _ = Rt M (LB M Q B) t := hR2
  have hV : conjSubgroup k (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
    calc conjSubgroup k (Vt M (LB M Q B) B Z t) = conjSubgroup k (Vt M (LB M Q B) B Z s) := by
          rw [hV1]
      _ = Vt M (LB M Q B) B Z (k * s * k⁻¹) :=
          conjSubgroup_Vt_eq hkM (hc.conj_Z_eq hkM) s
      _ = Vt M (LB M Q B) B Z t := hV2
  exact conjSubgroup_CN_eq hc hkM hR hV

variable [(Q.subgroupOf M).Normal]

theorem Ctx.sec715Adj_of_kappa (h34 : Stroth34Statement) (hZt : Sec7ZtStatement)
    (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hCN : Sec7CommNStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G))
    (hN2 : IsPGroup 2 ↥(bar M Q (hc.CN t))) (hC : CentTwoInV hc t Z0)
    (hsq : ∀ x ∈ hc.CN t, x * x ∈ Z0)
    (hκ : ∀ h : ↥(bar M Q (H0 M Z)),
      (∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        h * a * h⁻¹ ∈ (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z))) →
      (¬ ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        h * a * h⁻¹ ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) →
      ∀ b ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), b ≠ 1 →
        (∀ x ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
          ∃ z ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
            ⁅h * b * h⁻¹, x⁆ * z⁻¹ ∈
              conjSubgroup h ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))) ∧
        Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ^ 2 *
            Nat.card ↥(Subgroup.centralizer ({h * b * h⁻¹} : Set ↥(bar M Q (H0 M Z))) ⊓
              (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) <
          Nat.card ↥((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))))
    {g : G} (hgM : g ∈ M) (hgL : conjSubgroup g Z0 ≤ LB M Q B)
    (hgN : ¬ conjSubgroup g Z0 ≤ hc.CN t) :
    ∃ x ∈ hc.CN t, ∃ s ∈ Z0, s ∉ Q ∧ ⁅x, g * s * g⁻¹⁆ ∉ Q ∧ ⁅x, g * s * g⁻¹⁆ ∈ LB M Q B ∧
      ⁅x, g * s * g⁻¹⁆ ∈ conjSubgroup g (hc.CN t) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hHM : H0 M Z ≤ M := fun x hx => hx.1
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  obtain ⟨m, γ, M₀, -, hM⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ₀, hφπ, hφker, -⟩ := exists_actionHom_H0 hc.hyp hM
  obtain ⟨φ, -, hφmk⟩ := exists_barAct hQH hHM φ₀ hφker
  have hφπ' : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z))
      (x : G), x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x) := by
    intro y hy x hx
    have hyH : (y : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH y).mp hy
    rw [hφmk y hy hyH]
    exact hφπ ⟨(y : G), hyH⟩ x hx
  obtain ⟨Tt, F⟩ := Ctx.sec715Frame h34 hZt hZcard hZc hZV hc hs hZ0 M₀ φ hφπ'
  obtain ⟨h₀, hh₀H, hh₀⟩ := hc.exists_H0_conj hs hZ0 hZt hZcard hN2 hTI hC hgM
  have hgL₀ : conjSubgroup h₀ Z0 ≤ LB M Q B := hh₀ ▸ hgL
  have hgN₀ : ¬ conjSubgroup h₀ Z0 ≤ hc.CN t := hh₀ ▸ hgN
  have hmem : ∀ {S : Subgroup G}, Q ≤ S → ∀ (x : ↥(bar M Q (H0 M Z))) (y : ↥M),
      QuotientGroup.mk' (Q.subgroupOf M) y = (x : Mbar M Q) →
        (x ∈ (bar M Q S).subgroupOf (bar M Q (H0 M Z)) ↔ (y : G) ∈ S) := by
    intro S hQS x y hy
    rw [Subgroup.mem_subgroupOf, ← hy]
    exact mk_mem_bar_iff_sec4 hQS y
  have hrep : ∀ x : ↥(bar M Q (H0 M Z)), ∃ y : ↥M,
      QuotientGroup.mk' (Q.subgroupOf M) y = (x : Mbar M Q) :=
    fun x => QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
  have hh₀M : h₀ ∈ M := hHM hh₀H
  have hh₀bar : QuotientGroup.mk' (Q.subgroupOf M) ⟨h₀, hh₀M⟩ ∈ bar M Q (H0 M Z) :=
    (mk_mem_bar_iff_sec4 hQH _).mpr hh₀H
  set h : ↥(bar M Q (H0 M Z)) := ⟨_, hh₀bar⟩ with hh
  have hconjmk : ∀ (a : ↥(bar M Q (H0 M Z))) (z : ↥M),
      QuotientGroup.mk' (Q.subgroupOf M) z = (a : Mbar M Q) →
      QuotientGroup.mk' (Q.subgroupOf M) (⟨h₀, hh₀M⟩ * z * ⟨h₀, hh₀M⟩⁻¹) =
        ((h * a * h⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q) := by
    intro a z hz
    simp only [map_mul, map_inv, hz, Subgroup.coe_mul, Subgroup.coe_inv, hh]
  have hL : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      h * a * h⁻¹ ∈ (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)) := by
    intro a ha
    obtain ⟨z, hz⟩ := hrep a
    have hzZ : (z : G) ∈ Z0 := (hmem hQZ0 a z hz).mp ha
    refine (hmem hQL _ _ (hconjmk a z hz)).mpr ?_
    apply hgL₀
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hzZ
  have hout : ¬ ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      h * a * h⁻¹ ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
    intro hall
    apply hgN₀
    intro x hx
    obtain ⟨z, hzZ, rfl⟩ : ∃ z ∈ Z0, h₀ * z * h₀⁻¹ = x :=
      ⟨h₀⁻¹ * x * h₀, mem_conjSubgroup.mp hx, by group⟩
    have hzM : z ∈ M := hZ0M hzZ
    have hzbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hzM⟩ ∈ bar M Q (H0 M Z) :=
      (mk_mem_bar_iff_sec4 hQH _).mpr (hZ0.le.trans hRH hzZ)
    have haV : (⟨_, hzbar⟩ : ↥(bar M Q (H0 M Z))) ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) :=
      (hmem hQZ0 _ ⟨z, hzM⟩ rfl).mpr hzZ
    exact (hmem hQN _ _ (hconjmk _ ⟨z, hzM⟩ rfl)).mp (hall _ haV)
  obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  have hsM : s ∈ M := hZ0M hsZ0
  have hsbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q (H0 M Z) :=
    (mk_mem_bar_iff_sec4 hQH _).mpr (hZ0.le.trans hRH hsZ0)
  set b₀ : ↥(bar M Q (H0 M Z)) := ⟨_, hsbar⟩ with hb₀
  have hb₀V : b₀ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := (hmem hQZ0 _ _ rfl).mpr hsZ0
  have hb₀1 : b₀ ≠ 1 := fun h1 => hsQ (Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)))
  obtain ⟨hκ1, hκ2⟩ := hκ h hL hout b₀ hb₀V hb₀1
  set y := h * b₀ * h⁻¹ with hy
  set Vh := (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) with hVh
  set Lh := (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)) with hLh
  set Nh := (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) with hNh
  set Rh := (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) with hRh
  have hyL : y ∈ Lh := hL b₀ hb₀V
  have hVc : ∀ z ∈ Vh, ∀ x ∈ Nh, z * x = x * z := by
    intro z hz x hx
    obtain ⟨z₀, hz₀⟩ := hrep z
    have hz₀Z : (z₀ : G) ∈ Z0 := (hmem hQZ0 z z₀ hz₀).mp hz
    apply Subtype.ext
    show (z : Mbar M Q) * x = x * z
    rw [← hz₀]
    exact endg_comm_centre hZ0 (hc.Rt_le_M t) hz₀Z
      (bar_mono' hNR (Subgroup.mem_subgroupOf.mp hx))
  have hVsq : ∀ z ∈ Vh, z * z = 1 := by
    intro z hz
    apply Subtype.ext
    have := sq_eq_one_bar hc hs hZc hZ0 (z : Mbar M Q) (Subgroup.mem_subgroupOf.mp hz)
    simpa [pow_two] using this
  have hNc : ∀ a ∈ Nh, ∀ b ∈ Nh, ⁅a, b⁆ ∈ Vh := by
    intro a ha b hb
    obtain ⟨x, hx⟩ := hrep a
    obtain ⟨w, hw⟩ := hrep b
    have hxN : (x : G) ∈ hc.CN t := (hmem hQN a x hx).mp ha
    have hwN : (w : G) ∈ hc.CN t := (hmem hQN b w hw).mp hb
    have hcomm : ⁅(x : G), (w : G)⁆ ∈ Z0 :=
      hCN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator hxN hwN)
    rw [Subgroup.mem_subgroupOf]
    show ⁅(a : Mbar M Q), (b : Mbar M Q)⁆ ∈ bar M Q Z0
    rw [← hx, ← hw, ← map_commutatorElement]
    have hxw : ((⁅x, w⁆ : ↥M) : G) = ⁅(x : G), (w : G)⁆ := by
      simp [commutatorElement_def]
    exact (mk_mem_bar_iff_sec4 hQZ0 ⁅x, w⁆).mpr (hxw ▸ hcomm)
  have hNsq : ∀ a ∈ Nh, a * a ∈ Vh := by
    intro a ha
    obtain ⟨x, hx⟩ := hrep a
    have hxN : (x : G) ∈ hc.CN t := (hmem hQN a x hx).mp ha
    refine (hmem hQZ0 (a * a) (x * x) ?_).mpr (by simpa using hsq _ hxN)
    simp only [map_mul, hx, Subgroup.coe_mul]
  have hyLc : ∀ x ∈ Nh, ⁅y, x⁆ ∈ Lh := by
    intro x hx
    rw [commutatorElement_def]
    have h1 : x * y⁻¹ * x⁻¹ ∈ Lh := F.Nb_norm_L x hx _ (Lh.inv_mem hyL)
    have e : y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) := by group
    rw [e]
    exact Lh.mul_mem hyL h1
  have hyN : ∀ x ∈ Nh, ⁅y, x⁆ ∈ Nh := by
    intro x hx
    rw [commutatorElement_def]
    exact Nh.mul_mem (F.Nb_normal y (F.L_le_Rb hyL) x hx) (Nh.inv_mem hx)
  have hyV : ∀ z ∈ Vh, y * z = z * y := fun z hz => F.L_comm y hyL z (F.V_le_L hz)
  set Ker := Lh ⊓ conjSubgroup h Nh with hKer
  have hKerV : ∀ z ∈ Vh, z ∈ Ker → z = 1 := by
    intro z hz hzK
    exact F.eq_one_of_mem_conj_Nb hL hout hz (mem_conjSubgroup.mp hzK.2)
  have hK₂ : ∀ x ∈ Nh, ∃ z ∈ Vh, ⁅y, x⁆ * z⁻¹ ∈ Ker := by
    intro x hx
    obtain ⟨z, hz, hzK⟩ := hκ1 x hx
    exact ⟨z, hz, Lh.mul_mem (hyLc x hx) (Lh.inv_mem (F.V_le_L hz)), hzK⟩
  obtain ⟨x, hx, hxy, hxK⟩ := exists_comm_mem_of_card_lt (N := Nh) (V := Vh) (L := Lh)
    (K₂ := Nh) (Ker := Ker) (y := y) F.V_le_Nb F.V_le_L hVc hVsq hNc hNsq F.L_comm hyLc hyN hyV
    hKerV le_rfl (fun c hc _ => hc) hK₂ hκ2
  obtain ⟨x₀, hx₀⟩ := hrep x
  have hx₀N : (x₀ : G) ∈ hc.CN t := (hmem hQN x x₀ hx₀).mp hx
  have hyrep := hconjmk b₀ ⟨s, hsM⟩ rfl
  set y₀ : ↥M := ⟨h₀, hh₀M⟩ * ⟨s, hsM⟩ * ⟨h₀, hh₀M⟩⁻¹ with hy₀
  have hcrep : QuotientGroup.mk' (Q.subgroupOf M) ⁅x₀, y₀⁆ = ((⁅x, y⁆ : ↥(bar M Q (H0 M Z))) :
      Mbar M Q) := by
    rw [map_commutatorElement, hx₀, hyrep]
    rfl
  have hcG : ((⁅x₀, y₀⁆ : ↥M) : G) = ⁅(x₀ : G), h₀ * s * h₀⁻¹⁆ := by
    simp [hy₀, commutatorElement_def]
  have hcQ : ⁅(x₀ : G), h₀ * s * h₀⁻¹⁆ ∉ Q := by
    intro hQ
    apply hxy
    have h1 : (⁅x, y⁆ : ↥(bar M Q (H0 M Z))) = 1 := by
      apply Subtype.ext
      rw [← hcrep, Subgroup.coe_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (hcG ▸ hQ)
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hxyK : ⁅x, y⁆ ∈ Ker := by
    rw [← commutatorElement_inv]
    exact Ker.inv_mem hxK
  have hcL : ⁅(x₀ : G), h₀ * s * h₀⁻¹⁆ ∈ LB M Q B := hcG ▸ (hmem hQL _ _ hcrep).mp hxyK.1
  have hcN₀ : h₀⁻¹ * ⁅(x₀ : G), h₀ * s * h₀⁻¹⁆ * h₀ ∈ hc.CN t := by
    have h1 : h⁻¹ * ⁅x, y⁆ * h ∈ Nh := mem_conjSubgroup.mp hxyK.2
    have h2 : QuotientGroup.mk' (Q.subgroupOf M) (⟨h₀, hh₀M⟩⁻¹ * ⁅x₀, y₀⁆ * ⟨h₀, hh₀M⟩) =
        ((h⁻¹ * ⁅x, y⁆ * h : ↥(bar M Q (H0 M Z))) : Mbar M Q) := by
      simp only [map_mul, map_inv, hcrep, Subgroup.coe_mul, Subgroup.coe_inv, hh]
    have h3 := (hmem hQN _ _ h2).mp h1
    simpa [hcG, mul_assoc] using h3
  have hk : g⁻¹ * h₀ ∈ M := M.mul_mem (M.inv_mem hgM) hh₀M
  have hs'Z0 : g⁻¹ * (h₀ * s * h₀⁻¹) * g ∈ Z0 := by
    have h1 : h₀ * s * h₀⁻¹ ∈ conjSubgroup g Z0 := by
      rw [hh₀, mem_conjSubgroup]
      simpa [mul_assoc] using hsZ0
    exact mem_conjSubgroup.mp h1
  have hkN : g⁻¹ * h₀ ∈ Subgroup.normalizer (Z0 : Set G) := by
    refine hTI _ hk s hsZ0 hsQ ?_
    have e : g⁻¹ * h₀ * s * (g⁻¹ * h₀)⁻¹ = g⁻¹ * (h₀ * s * h₀⁻¹) * g := by group
    rw [e]
    exact hs'Z0
  have hkCN := conj_CN_eq_of_normalizer hZt hZcard hc hs hZ0 hk hkN
  refine ⟨x₀, hx₀N, g⁻¹ * (h₀ * s * h₀⁻¹) * g, hs'Z0, ?_, ?_, ?_, ?_⟩
  · intro hQ'
    apply hsQ
    have h1 : g * (g⁻¹ * (h₀ * s * h₀⁻¹) * g) * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) _).mp hQ'
    have h2 : h₀⁻¹ * (g * (g⁻¹ * (h₀ * s * h₀⁻¹) * g) * g⁻¹) * h₀ ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hh₀M)) _).mp h1
      simpa [mul_assoc] using this
    have e : h₀⁻¹ * (g * (g⁻¹ * (h₀ * s * h₀⁻¹) * g) * g⁻¹) * h₀ = s := by group
    rwa [e] at h2
  · have e : g * (g⁻¹ * (h₀ * s * h₀⁻¹) * g) * g⁻¹ = h₀ * s * h₀⁻¹ := by group
    rw [e]
    exact hcQ
  · have e : g * (g⁻¹ * (h₀ * s * h₀⁻¹) * g) * g⁻¹ = h₀ * s * h₀⁻¹ := by group
    rw [e]
    exact hcL
  · have e : g * (g⁻¹ * (h₀ * s * h₀⁻¹) * g) * g⁻¹ = h₀ * s * h₀⁻¹ := by group
    rw [e, mem_conjSubgroup]
    have h1 : g⁻¹ * h₀ * (h₀⁻¹ * ⁅(x₀ : G), h₀ * s * h₀⁻¹⁆ * h₀) * (g⁻¹ * h₀)⁻¹ ∈
        conjSubgroup (g⁻¹ * h₀) (hc.CN t) := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hcN₀
    rw [hkCN] at h1
    have e2 : g⁻¹ * h₀ * (h₀⁻¹ * ⁅(x₀ : G), h₀ * s * h₀⁻¹⁆ * h₀) * (g⁻¹ * h₀)⁻¹ =
        g⁻¹ * ⁅(x₀ : G), h₀ * s * h₀⁻¹⁆ * g := by group
    rwa [e2] at h1

section Certs

theorem sec715Adj_of (hLS : S715L.Sec715LayerSplitStatement) (hCent : Sec715CentStatement) :
    Sec715AdjStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp hn Z0 hZ0 hZ0N hTI g hgM hgL hgN
  subst hn
  have h34 := stroth34Statement_unconditional
  have h311a := stroth311aStatement_unconditional
  have h51 := stroth51Statement_unconditional
  have hA := sec7AExistsStatement_unconditional
  obtain ⟨r, hr⟩ := hA G M Q Z B hc 16 t hs
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0
    (sec7ctr_Z0_le_CN hc hs hZ0)
  have hsq : ∀ x ∈ hc.CN t, x * x ∈ Z0 := fun x hx => by
    rw [← pow_two]
    exact hopp.2.2.2.2.2.2.2.1 x hx
  have hC : CentTwoInV hc t Z0 := fun k _ hk2 hkc =>
    hCent G M Q Z B hc 16 t hs (Or.inr hp) Z0 hZ0 hZ0N k hk2 hkc
  exact hc.sec715Adj_of_kappa h34 sec7ZtStatement_holds sec7ZCardStatement_holds
    sec7CentreMpStatement_holds sec7ZVStatement_holds
    (sec7CommN_of_34 h34 stroth310Statement_unconditional h311a) hs hZ0 hTI
    (sec7_CN_pgroup_bar h34 h311a hc hs) hC hsq
    (hc.sec715_kappa hLS h34 stroth310RootStatement_unconditional (stroth310Chi_of_34 h34) h51
      stroth52aStatement_holds stroth52bStatement_holds sec7NOrderStatement_holds
      sec7CentreMpStatement_holds sec7CRWStatement_holds sec7ZVStatement_holds
      sec7ZCardStatement_holds sec7ZtStatement_holds hA hs hp hZ0 hZ0N) hgM hgL hgN

end Certs

end CFSG.RankThree.GF2n.Stroth80
