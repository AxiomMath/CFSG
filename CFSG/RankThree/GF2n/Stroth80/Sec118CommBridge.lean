module

public import CFSG.RankThree.GF2n.Stroth80.Sec118Nondeg
public import CFSG.ClassicalGroups.Symplectic.CoordinateRank
public import CFSG.ClassicalGroups.Symplectic.NaturalDuality
import CFSG.RankThree.GF2n.Stroth80.Sec118LBCent
import CFSG.RankThree.GF2n.Stroth80.CarterSec11CMIsometry

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix
open CFSG.ClassicalGroups.Symplectic

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.eq_zero_of_mem_cmComm_of_orthogonal (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {y : M₀.E} (hy : y ∈ cmComm M Q Z B K γ M₀ φ)
    (horth : ∀ z ∈ cmComm M Q Z B K γ M₀ φ, M₀.B y z = 0) : y = 0 := by
  obtain ⟨x, hx, rfl⟩ := (mem_cmComm_iff hc h φ hφπ y).mp hy
  have hxQ : x ∈ Q := commutator_le_Q hc hx
  have hcent : x ∈ Subgroup.centralizer ((⁅Q, XbarPre M Q Z B⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hcC
    have hcQ : c ∈ Q := commutator_le_Q hc hcC
    have hB := horth (M₀.π c) ((mem_cmComm_iff hc h φ hφπ _).mpr ⟨c, hcC, rfl⟩)
    exact ((Tim79.QuadModel.comm_iff_B M₀ h.reg hxQ hcQ).mpr hB).symm
  have hZ : x ∈ Z := by
    rw [← hc.commXbarPre_sup_inf_centralizer_eq]
    exact ⟨Subgroup.mem_sup_left hx, hcent⟩
  exact (M₀.π_ker x hxQ).mpr hZ

theorem Ctx.mem_img_sup_iff_mem_cmComm (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) (e : M₀.E) :
    e ∈ M₀.img (Z ⊔ ⁅Q, XbarPre M Q Z B⁆) ↔ e ∈ cmComm M Q Z B K γ M₀ φ := by
  constructor
  · rintro ⟨x, hxY, hxQ, rfl⟩
    let S : Subgroup G :=
      { carrier := {x | x ∈ Q ∧ ∃ c ∈ (⁅Q, XbarPre M Q Z B⁆ : Subgroup G), M₀.π x = M₀.π c}
        one_mem' := ⟨Q.one_mem, 1, Subgroup.one_mem _, rfl⟩
        mul_mem' := by
          rintro x y ⟨hxQ, c, hcC, hxc⟩ ⟨hyQ, d, hdC, hyd⟩
          refine ⟨Q.mul_mem hxQ hyQ, c * d, Subgroup.mul_mem _ hcC hdC, ?_⟩
          rw [M₀.π_mul x hxQ y hyQ, M₀.π_mul c (commutator_le_Q hc hcC) d
            (commutator_le_Q hc hdC), hxc, hyd]
        inv_mem' := by
          rintro x ⟨hxQ, c, hcC, hxc⟩
          refine ⟨Q.inv_mem hxQ, c⁻¹, Subgroup.inv_mem _ hcC, ?_⟩
          rw [pi_inv hxQ, pi_inv (commutator_le_Q hc hcC), hxc] }
    have hZS : Z ≤ S := fun z hz =>
      ⟨h.reg.V_le hz, 1, Subgroup.one_mem _, by
        rw [pi_one, (M₀.π_ker z (h.reg.V_le hz)).mpr hz]⟩
    have hCS : (⁅Q, XbarPre M Q Z B⁆ : Subgroup G) ≤ S := fun c hcC =>
      ⟨commutator_le_Q hc hcC, c, hcC, rfl⟩
    obtain ⟨-, c, hcC, hxc⟩ := (sup_le hZS hCS) hxY
    rw [hxc]
    exact (mem_cmComm_iff hc h φ hφπ _).mpr ⟨c, hcC, rfl⟩
  · intro he
    obtain ⟨x, hx, rfl⟩ := (mem_cmComm_iff hc h φ hφπ e).mp he
    exact ⟨x, Subgroup.mem_sup_right hx, commutator_le_Q hc hx, rfl⟩

theorem Ctx.card_sup_commXbarPre_eq (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) :
    Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) =
      Nat.card Z * Nat.card ↥(cmComm M Q Z B K γ M₀ φ) := by
  have hle : (Z ⊔ ⁅Q, XbarPre M Q Z B⁆ : Subgroup G) ≤ Q :=
    sup_le hc.Z_le_Q (commutator_le_Q hc)
  rw [M₀.card_eq hle le_sup_left]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun e =>
    Ctx.mem_img_sup_iff_mem_cmComm hc h φ hφπ e)

theorem Ctx.action_sq_eq_one (hc : Ctx M Q Z B) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) {a : G} (haH : a ∈ H0 M Z)
    (ha2 : a ^ 2 ∈ Q) (e : M₀.E) :
    φ ⟨a, haH⟩ (φ ⟨a, haH⟩ e) = e := by
  have hQn : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 haH.1) x).mp hx
  obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
  rw [← hφπ ⟨a, haH⟩ y hyQ, ← hφπ ⟨a, haH⟩ _ (hQn y hyQ)]
  have h1 : a * (a * y * a⁻¹) * a⁻¹ = a ^ 2 * y * (a ^ 2)⁻¹ := by
    rw [pow_two]; group
  show M₀.π (a * (a * y * a⁻¹) * a⁻¹) = M₀.π y
  rw [h1]
  exact Tim79.QuadModel.pi_conj_self (M₀ := M₀) ha2 hyQ

theorem Ctx.mem_img_zpowers_sup_iff (hc : Ctx M Q Z B) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) {a : G} (haH : a ∈ H0 M Z)
    (ha2 : a ^ 2 ∈ Q) (e : M₀.E) :
    e ∈ M₀.img (⁅Q, Subgroup.zpowers a⁆ ⊔ Z) ↔
      e ∈ LinearMap.range (((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) := by
  set T : M₀.E ≃ₗ[K] M₀.E := φ ⟨a, haH⟩ with hT
  have hT2 := hc.action_sq_eq_one φ hφπ haH ha2
  have hQn : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 haH.1) x).mp hx
  have hcomm : ∀ q ∈ Q, M₀.π ⁅q, a⁆ = M₀.π q - T (M₀.π q) := fun q hq =>
    pi_commutatorElement hc φ hφπ hq ⟨a, haH⟩
  constructor
  · rintro ⟨x, hxD, hxQ, rfl⟩
    let S : Subgroup G :=
      { carrier := {x | x ∈ Q ∧ M₀.π x ∈
          LinearMap.range (((T : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)}
        one_mem' := ⟨Q.one_mem, by rw [pi_one]; exact Submodule.zero_mem _⟩
        mul_mem' := by
          rintro x y ⟨hxQ, hx⟩ ⟨hyQ, hy⟩
          exact ⟨Q.mul_mem hxQ hyQ, by rw [M₀.π_mul x hxQ y hyQ]; exact Submodule.add_mem _ hx hy⟩
        inv_mem' := by
          rintro x ⟨hxQ, hx⟩
          exact ⟨Q.inv_mem hxQ, by rw [pi_inv hxQ]; exact Submodule.neg_mem _ hx⟩ }
    have hZS : Z ≤ S := fun z hz =>
      ⟨hc.Z_le_Q hz, by
        rw [(M₀.π_ker z (hc.Z_le_Q hz)).mpr hz]; exact Submodule.zero_mem _⟩
    have hCS : (⁅Q, Subgroup.zpowers a⁆ : Subgroup G) ≤ S := by
      rw [Subgroup.commutator_le]
      intro q hq g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hgH : a ^ k ∈ H0 M Z := (H0 M Z).zpow_mem haH k
      have hgQ : (a ^ k) * q⁻¹ * (a ^ k)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgH.1) _).mp (Q.inv_mem hq)
      have hcQ : ⁅q, a ^ k⁆ ∈ Q := by
        have e : ⁅q, a ^ k⁆ = q * ((a ^ k) * q⁻¹ * (a ^ k)⁻¹) := by
          rw [commutatorElement_def]; group
        rw [e]; exact Q.mul_mem hq hgQ
      refine ⟨hcQ, ?_⟩
      have h1 := pi_commutatorElement hc φ hφπ hq (⟨a ^ k, hgH⟩ : ↥(H0 M Z))
      have hφk : φ (⟨a ^ k, hgH⟩ : ↥(H0 M Z)) = T ^ k := by
        rw [hT, ← map_zpow]; rfl
      have hTT : T * T = 1 := LinearEquiv.ext fun f => hT2 f
      have hTT2 : T ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hTT
      have h2 : ∀ f : M₀.E, (T ^ k) f = f ∨ (T ^ k) f = T f := by
        intro f
        rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
        · left
          have : T ^ (2 * n) = 1 := by rw [zpow_mul, hTT2, one_zpow]
          rw [this]; rfl
        · right
          have : T ^ (2 * n + 1) = T := by rw [zpow_add_one, zpow_mul, hTT2, one_zpow, one_mul]
          rw [this]
      change M₀.π ⁅q, (⟨a ^ k, hgH⟩ : ↥(H0 M Z)).1⁆ ∈ _
      rw [h1, hφk]
      rcases h2 (M₀.π q) with h3 | h3
      · rw [h3, sub_self]; exact Submodule.zero_mem _
      · rw [h3]
        have : M₀.π q - T (M₀.π q) = -((T : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π q) := by
          simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe]; abel
        rw [this]
        exact Submodule.neg_mem _ ⟨M₀.π q, rfl⟩
    exact ((sup_le hCS hZS) hxD).2
  · rintro ⟨f, rfl⟩
    obtain ⟨q, hq, rfl⟩ := M₀.π_surj f
    have hcQ : ⁅q, a⁆ ∈ Q := by
      have e : ⁅q, a⁆ = q * (a * q⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
      rw [e]; exact Q.mul_mem hq (hQn _ (Q.inv_mem hq))
    have hD : ⁅q, a⁆⁻¹ ∈ (⁅Q, Subgroup.zpowers a⁆ ⊔ Z : Subgroup G) :=
      Subgroup.inv_mem _ (Subgroup.mem_sup_left
        (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers a)))
    refine ⟨⁅q, a⁆⁻¹, hD, Q.inv_mem hcQ, ?_⟩
    rw [pi_inv hcQ, hcomm q hq]
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe]
    abel

theorem Ctx.finrank_range_sub_one_of_card (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) {a : G} (haH : a ∈ H0 M Z)
    (ha2 : a ^ 2 ∈ Q) (hcard : Nat.card ↥(⁅Q, Subgroup.zpowers a⁆ ⊔ Z) = Nat.card Z ^ 3) :
    Module.finrank K
      (LinearMap.range (((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)) = 2 := by
  have hle : (⁅Q, Subgroup.zpowers a⁆ ⊔ Z : Subgroup G) ≤ Q := by
    refine sup_le ?_ hc.Z_le_Q
    rw [Subgroup.commutator_le]
    intro q hq g hg
    have hgM : g ∈ M := (Subgroup.zpowers_le.mpr haH.1) hg
    have hgQ : g * q⁻¹ * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) _).mp (Q.inv_mem hq)
    have e : ⁅q, g⁆ = q * (g * q⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [e]; exact Q.mul_mem hq hgQ
  have h1 := M₀.card_eq hle le_sup_right
  have h2 : Nat.card ↥(M₀.img (⁅Q, Subgroup.zpowers a⁆ ⊔ Z)) =
      Nat.card ↥(LinearMap.range (((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun e =>
      hc.mem_img_zpowers_sup_iff φ hφπ haH ha2 e)
  have h3 := Module.natCard_eq_pow_finrank (K := K)
    (V := ↥(LinearMap.range (((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)))
  rw [hcard, h2, h3, h.card] at h1
  have hZ2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have h4 : Nat.card Z ^ 2 = Nat.card Z ^
      Module.finrank K
        (LinearMap.range (((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)) := by
    have hpos : 0 < Nat.card Z := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [← pow_succ', ← h1]
  exact ((Nat.pow_right_injective hZ2) h4).symm

theorem Ctx.isCompl_cmComm_orthogonal (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) :
    IsCompl (cmComm M Q Z B K γ M₀ φ) (M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ)) := by
  have hrefl : M₀.B.IsRefl := fun x y hxy => by
    rw [Tim79.QuadModel.B_comm, hxy, neg_zero]
  refine LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl ?_
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · refine Subtype.ext (hc.eq_zero_of_mem_cmComm_of_orthogonal h φ hφπ x.2 fun z hz => ?_)
    have := hx ⟨z, hz⟩
    simpa using this
  · refine Subtype.ext (hc.eq_zero_of_mem_cmComm_of_orthogonal h φ hφπ x.2 fun z hz => ?_)
    have := hx ⟨z, hz⟩
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      Submodule.coe_subtype] at this
    rw [Tim79.QuadModel.B_comm, this, neg_zero]

theorem Ctx.action_fixes_orthogonal (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {l : G} (hl : l ∈ LB M Q B) (hlH : l ∈ H0 M Z)
    {y : M₀.E} (hy : y ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ)) :
    φ ⟨l, hlH⟩ y = y := by
  obtain ⟨v, hvQ, rfl⟩ := M₀.π_surj y
  have hvY : v ∈ Subgroup.centralizer
      ((⁅Q, XbarPre M Q Z B⁆ ⊔ Z : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgY : g ∈ Q := sup_le (commutator_le_Q hc) hc.Z_le_Q hg
    have hg' : g ∈ (Z ⊔ ⁅Q, XbarPre M Q Z B⁆ : Subgroup G) := by rwa [sup_comm]
    have hπg : M₀.π g ∈ cmComm M Q Z B K γ M₀ φ :=
      (hc.mem_img_sup_iff_mem_cmComm h φ hφπ _).mp ⟨g, hg', hgY, rfl⟩
    exact (Tim79.QuadModel.comm_iff_B M₀ h.reg hgY hvQ).mpr (hy (M₀.π g) hπg)
  have hcomm := hc.comm_mem_Z_of_centralizes_commXbarPre ha2 hl hvQ hvY
  have hlM : l ∈ M := hlH.1
  have hlvQ : l * v * l⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) v).mp hvQ
  rw [← hφπ ⟨l, hlH⟩ v hvQ]
  exact (M₀.comm_mem_iff hvQ hlvQ).mp hcomm

theorem Ctx.range_sub_one_eq_map_cmComm (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {l : G} (hl : l ∈ LB M Q B) (hlH : l ∈ H0 M Z) :
    LinearMap.range (((φ ⟨l, hlH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) =
      Submodule.map (((φ ⟨l, hlH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)
        (cmComm M Q Z B K γ M₀ φ) := by
  apply le_antisymm
  · rintro _ ⟨e, rfl⟩
    have he : e ∈ cmComm M Q Z B K γ M₀ φ ⊔ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ) := by
      rw [(hc.isCompl_cmComm_orthogonal h φ hφπ).sup_eq_top]; trivial
    obtain ⟨y, hy, y', hy', rfl⟩ := Submodule.mem_sup.mp he
    refine ⟨y, hy, ?_⟩
    have h1 := hc.action_fixes_orthogonal h φ hφπ ha2 hl hlH hy'
    simp only [map_add, LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, h1]
    abel
  · rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩

theorem Ctx.rank_sub_one_eq_one (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {m : ℕ} {W₁ W₂ : Submodule K M₀.E}
    (hdisj : Disjoint W₁ W₂) (hsup : W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ)
    (hW₁ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁)
    (hW₂ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂)
    (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K)
    (e₁ : W₁ ≃ₗ[K] (Fin m ⊕ Fin m → K)) (e₂ : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (he₁ : ∀ (s : ↥(XbarH M Q Z B)) (w : W₁),
      e₁ ⟨φ s w, hW₁ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₁ w)
    (he₂ : ∀ (s : ↥(XbarH M Q Z B)) (w : W₂),
      e₂ ⟨φ s w, hW₂ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₂ w)
    {a : G} (haL : a ∈ LB M Q B) (hA : IsA2 Q Z a) (haX : a ∈ XbarPre M Q Z B) :
    (((ρ ⟨⟨a, XbarPre_le_H0 hc haX⟩, (mem_XbarH_iff hc _).mpr haX⟩ : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1).rank = 1 := by
  obtain ⟨-, -, ha2', hcardA, -⟩ := hA
  have haH : a ∈ H0 M Z := XbarPre_le_H0 hc haX
  have h1 := hc.finrank_range_sub_one_of_card h φ hφπ haH ha2' hcardA
  have h2 := hc.range_sub_one_eq_map_cmComm h φ hφπ ha2 haL haH
  rw [h2, ← hsup] at h1
  have h3 := finrank_map_sub_one_sup_of_coords hdisj e₁ e₂
    ((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
    (hW₁ ⟨⟨a, haH⟩, (mem_XbarH_iff hc _).mpr haX⟩)
    (hW₂ ⟨⟨a, haH⟩, (mem_XbarH_iff hc _).mpr haX⟩) _
    (he₁ ⟨⟨a, haH⟩, (mem_XbarH_iff hc _).mpr haX⟩)
    (he₂ ⟨⟨a, haH⟩, (mem_XbarH_iff hc _).mpr haX⟩)
  rw [h3] at h1
  omega

theorem Ctx.smul_range_of_stab (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {m : ℕ} {W₁ W₂ : Submodule K M₀.E}
    (hsup : W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ)
    (hW₁ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁)
    (hW₂ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂)
    (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K)
    (e₁ : W₁ ≃ₗ[K] (Fin m ⊕ Fin m → K)) (e₂ : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (he₁ : ∀ (s : ↥(XbarH M Q Z B)) (w : W₁),
      e₁ ⟨φ s w, hW₁ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₁ w)
    (he₂ : ∀ (s : ↥(XbarH M Q Z B)) (w : W₂),
      e₂ ⟨φ s w, hW₂ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₂ w)
    {a : G} (haL : a ∈ LB M Q B) (haX : a ∈ XbarPre M Q Z B) (c : K) {s : ↥(XbarH M Q Z B)}
    (hstab : ∀ v ∈ LinearMap.range (Matrix.mulVecLin
      (((ρ ⟨⟨a, XbarPre_le_H0 hc haX⟩, (mem_XbarH_iff hc _).mpr haX⟩ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1)),
      (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = c • v) :
    ∀ x ∈ LinearMap.range
      (((φ ⟨a, XbarPre_le_H0 hc haX⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1),
      φ s x = c • x := by
  have haH : a ∈ H0 M Z := XbarPre_le_H0 hc haX
  set sa : ↥(XbarH M Q Z B) := ⟨⟨a, haH⟩, (mem_XbarH_iff hc _).mpr haX⟩ with hsa
  intro x hx
  rw [hc.range_sub_one_eq_map_cmComm h φ hφπ ha2 haL haH, ← hsup, Submodule.map_sup] at hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
  have h1 := smul_of_map_sub_one e₁ ((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
    (hW₁ sa) _ (he₁ sa) ((φ s : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) (hW₁ s) _ (he₁ s) c hstab
  have h2 := smul_of_map_sub_one e₂ ((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
    (hW₂ sa) _ (he₂ sa) ((φ s : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) (hW₂ s) _ (he₂ s) c hstab
  have h3 := h1 x₁ hx₁
  have h4 := h2 x₂ hx₂
  simp only [LinearEquiv.coe_coe] at h3 h4
  rw [map_add, h3, h4, smul_add]

theorem Ctx.exists_coords_of_global [CharP K 2] (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {m : ℕ} {W₁ W₂ : Submodule K M₀.E} (hsup : W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ)
    (hW₁ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁)
    (hW₂ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂)
    (hs₁ : ∀ w ∈ W₁, M₀.Qf w = 0) (hs₂ : ∀ w ∈ W₂, M₀.Qf w = 0)
    (b : Module.Basis (Fin m ⊕ Fin m) K ↥W₁) (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K)
    (hρr : ρ.range = StatedSp m K)
    (hρe : ∀ (s : ↥(XbarH M Q Z B)) (w : ↥W₁),
      b.equivFun ⟨φ s (w : M₀.E), hW₁ s (w : M₀.E) w.2⟩ =
        (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ b.equivFun w) :
    ∃ (e₁ : W₁ ≃ₗ[K] (Fin m ⊕ Fin m → K)) (e₂ : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K)),
      (∀ (s : ↥(XbarH M Q Z B)) (w : W₁),
        e₁ ⟨φ s w, hW₁ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₁ w) ∧
      ∀ (s : ↥(XbarH M Q Z B)) (w : W₂),
        e₂ ⟨φ s w, hW₂ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₂ w := by
  have hΦB : ∀ (t : ↥(XbarH M Q Z B)) (u v : M₀.E), M₀.B (φ t u) (φ t v) = M₀.B u v :=
    fun t u v => (isometry_of_π h (t : ↥(H0 M Z)) (hφπ t)).2 u v
  have hsymm : ∀ x y : M₀.E, M₀.B x y = M₀.B y x := fun x y => by
    rw [Tim79.QuadModel.B_comm, CharTwo.neg_eq]
  have hiso : ∀ {W : Submodule K M₀.E}, (∀ w ∈ W, M₀.Qf w = 0) →
      ∀ x ∈ W, ∀ y ∈ W, M₀.B x y = 0 := by
    intro W hW x hx y hy
    have h1 := M₀.Qf_add x y
    rw [hW _ (W.add_mem hx hy), hW x hx, hW y hy] at h1
    simpa using h1.symm
  have hnd : ∀ y ∈ W₁ ⊔ W₂, (∀ z ∈ W₁ ⊔ W₂, M₀.B y z = 0) → y = 0 := by
    intro y hy hz
    rw [hsup] at hy hz
    exact hc.eq_zero_of_mem_cmComm_of_orthogonal h φ hφπ hy hz
  have hρsp : ∀ t, ρ t ∈ StatedSp m K := fun t => hρr ▸ ⟨t, rfl⟩
  have hρb : ∀ (s : ↥(XbarH M Q Z B)) (i : Fin m ⊕ Fin m),
      φ s ((b i : ↥W₁) : M₀.E) =
        ∑ j, (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) j i • ((b j : ↥W₁) : M₀.E) :=
    fun s i => map_basis_eq_sum_of_equivFun b ((φ s : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
      (hW₁ s) (ρ s) (hρe s) i
  obtain ⟨e₂, he₂⟩ := exists_equiv_of_isotropic_nondegenerate M₀.B hsymm (hiso hs₁) (hiso hs₂)
    hnd b (φ.comp (XbarH M Q Z B).subtype) hΦB hW₂ ρ hρsp hρb
  exact ⟨b.equivFun, e₂, hρe, he₂⟩

end CFSG.RankThree.GF2n.Stroth80
