module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Module
public import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110LineCent
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110EbarSiegel
import CFSG.RankThree.GF2n.Stroth80.Sec118CommBridge
import CFSG.RankThree.GF2n.Stroth80.Sec11TorusLine
import CFSG.RankThree.GF2n.Stroth80.Sec123Order
import CFSG.RankThree.OrthogonalInvolutions.A2Pencil
public import CFSG.RankThree.GF2n.Stroth80.Sec5Comm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

theorem Ctx.exists_lbLine_subset_Ebar (hc : Ctx M Q Z B) {y : G} (hy : IsLBTorus M Q Z B y)
    {a : ↥M} (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)) :
    ∃ U : Subgroup (Mbar M Q), U ≤ bar M Q (LB M Q B) ∧ Nat.card U = Nat.card Z ∧
      (QuotientGroup.mk a : Mbar M Q) ∈ U ∧
      (∀ u ∈ U, u ≠ 1 → ∃ i : ℕ, ∃ m : ↥M, (m : G) = y ^ i * (a : G) * (y ^ i)⁻¹ ∧
        u = QuotientGroup.mk m) ∧
      ∀ u ∈ U, u ≠ 1 → u ∈ Ebar M Q Z B := by
  obtain ⟨U, hUle, hUcard, hUl, hUelts⟩ := hy.exists_lbLine hc h.1 h.2.2.1
  refine ⟨U, hUle, hUcard, hUl a rfl, fun u hu hu1 => ?_, fun u hu hu1 => ?_⟩
  · obtain ⟨i, -, m, hm, hum⟩ := hUelts u hu hu1
    exact ⟨i, m, hm, hum⟩
  · obtain ⟨i, -, m, hm, rfl⟩ := hUelts u hu hu1
    have hm' : m = (⟨y, hy.mem_M⟩ : ↥M) ^ i * a * ((⟨y, hy.mem_M⟩ : ↥M) ^ i)⁻¹ := by
      apply Subtype.ext
      rw [hm]
      simp
    have h1 := hc.Ebar_conj (hc.mk_mem_Ebar h.1 h.2)
      ((QuotientGroup.mk (⟨y, hy.mem_M⟩ : ↥M) : Mbar M Q) ^ i)
    have h2 : QuotientGroup.mk' (Q.subgroupOf M) m =
        (QuotientGroup.mk (⟨y, hy.mem_M⟩ : ↥M) : Mbar M Q) ^ i * QuotientGroup.mk a *
          ((QuotientGroup.mk (⟨y, hy.mem_M⟩ : ↥M) : Mbar M Q) ^ i)⁻¹ := by
      rw [hm', map_mul, map_mul, map_pow, map_inv, map_pow]
      rfl
    rw [h2]
    exact h1

omit [Finite G] in
theorem mk_mul_comm_iff_commutator_mem_Q {x z : ↥M} :
    (QuotientGroup.mk x : Mbar M Q) * QuotientGroup.mk z =
      QuotientGroup.mk z * QuotientGroup.mk x ↔ ⁅(x : G), (z : G)⁆ ∈ Q := by
  have hcoe : ((⁅x, z⁆ : ↥M) : G) = ⁅(x : G), (z : G)⁆ := by simp [commutatorElement_def]
  have h2 : ⁅(QuotientGroup.mk' (Q.subgroupOf M) x : Mbar M Q),
      QuotientGroup.mk' (Q.subgroupOf M) z⁆ = 1 ↔ (⁅x, z⁆ : ↥M) ∈ Q.subgroupOf M := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _)
  rw [← hcoe, ← Subgroup.mem_subgroupOf, ← h2, commutatorElement_eq_one_iff_mul_comm]
  rfl

theorem Ctx.mk_comm_of_mem_D (hc : Ctx M Q Z B) {y : G} (hy : IsLBTorus M Q Z B y) {a : ↥M}
    (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)) {e : Mbar M Q} (he : e ∈ Ebar M Q Z B)
    (hea : e * QuotientGroup.mk a = QuotientGroup.mk a * e)
    (heaE : e * QuotientGroup.mk a ∈ Ebar M Q Z B) (i : ℕ) (m : ↥M)
    (hm : (m : G) = y ^ i * (a : G) * (y ^ i)⁻¹) :
    e * QuotientGroup.mk m = QuotientGroup.mk m * e := by
  obtain ⟨k, hke, -, hkH⟩ := hc.exists_H0_rep_of_mem_Ebar he
  have haH : (a : G) ∈ H0 M Z := hc.LB_le_H0 h.1
  obtain ⟨n, γ, M₀, hZn, hD⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, -⟩ := exists_actionHom_H0 hc.hyp hD
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hZn
    have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
    omega
  have hKZ : Nat.card (GaloisField 2 n) = Nat.card Z := by
    rw [GaloisField.card 2 n hn, ← hZn]
  have hτk : (QuotientGroup.mk (⟨(k : G), hkH.1⟩ : ↥M) : Mbar M Q) ∈ Ebar M Q Z B := by
    rw [show (⟨(k : G), hkH.1⟩ : ↥M) = k from Subtype.ext rfl, hke]
    exact he
  have hTk := hc.isOrthA2_of_mem_Ebar hD hKZ hkH hτk
    (fun x hx => hφπ ⟨(k : G), hkH⟩ x hx)
  have hτa : (QuotientGroup.mk (⟨(a : G), haH.1⟩ : ↥M) : Mbar M Q) ∈ Ebar M Q Z B := by
    rw [show (⟨(a : G), haH.1⟩ : ↥M) = a from Subtype.ext rfl]
    exact hc.mk_mem_Ebar h.1 h.2
  have hTl := hc.isOrthA2_of_mem_Ebar hD hKZ haH hτa
    (fun x hx => hφπ ⟨(a : G), haH⟩ x hx)
  have hkaH : (k : G) * (a : G) ∈ H0 M Z := (H0 M Z).mul_mem hkH haH
  have hτka : (QuotientGroup.mk (⟨(k : G) * (a : G), hkaH.1⟩ : ↥M) : Mbar M Q) ∈
      Ebar M Q Z B := by
    rw [show (⟨(k : G) * (a : G), hkaH.1⟩ : ↥M) = k * a from Subtype.ext rfl,
      QuotientGroup.mk_mul, hke]
    exact heaE
  have hTka := hc.isOrthA2_of_mem_Ebar hD hKZ hkaH hτka
    (T := φ ⟨(k : G), hkH⟩ * φ ⟨(a : G), haH⟩) (fun x hx => by
      have := hφπ (⟨(k : G), hkH⟩ * ⟨(a : G), haH⟩) x hx
      rw [map_mul] at this
      simpa using this)
  have hkl : ⁅(k : G), (a : G)⁆ ∈ Q := by
    apply mk_mul_comm_iff_commutator_mem_Q.mp
    rw [hke]
    exact hea
  have hcommT : Commute (φ ⟨(k : G), hkH⟩) (φ ⟨(a : G), haH⟩) := by
    have h1 : φ ((⟨(k : G), hkH⟩ * ⟨(a : G), haH⟩) *
        (⟨(a : G), haH⟩ * ⟨(k : G), hkH⟩)⁻¹) = 1 := by
      have hcoe : (((⟨(k : G), hkH⟩ * ⟨(a : G), haH⟩) *
          (⟨(a : G), haH⟩ * ⟨(k : G), hkH⟩)⁻¹ : ↥(H0 M Z)) : G) = ⁅(k : G), (a : G)⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [hφker, hcoe]
      exact hkl
    rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul] at h1
    exact h1
  have hpen := commSpace_eq_or_pencil_of_mul (polarBilin_toQuadraticForm_nondegenerate M₀) hTk
    hTl hcommT hTka
  have htriv : ∀ w ∈ commSpace (φ ⟨(a : G), haH⟩), φ ⟨(k : G), hkH⟩ w = w := by
    intro w hw
    rcases hpen with h1 | ⟨-, h2⟩
    · rw [← h1] at hw
      exact mem_fixSpace.mp (commSpace_le_fixSpace hTk.mul_self hw)
    · have hw' : w ∈ fixSpace (φ ⟨(k : G), hkH⟩) := by
        rw [fixSpace_eq_orthogonal_commSpace (polarBilin_toQuadraticForm_nondegenerate M₀)
          hTk.mem hTk.mul_self, LinearMap.BilinForm.mem_orthogonal_iff]
        intro p hp
        have h3 := h2 (p + w) (Submodule.add_mem_sup hp hw)
        have h4 := h2 p (Submodule.mem_sup_left hp)
        have h5 := h2 w (Submodule.mem_sup_right hw)
        have h6 := map_add_eq M₀.toQuadraticForm p w
        rw [h3, h4, h5, zero_add, zero_add] at h6
        rw [QuadraticMap.polarBilin_apply_apply]
        exact h6.symm
      exact mem_fixSpace.mp hw'
  have hQcomm : (⁅Q, Subgroup.zpowers (a : G)⁆ : Subgroup G) ≤ Q := by
    rw [Subgroup.commutator_le]
    intro q hq g hg
    have hgM : g ∈ M := (Subgroup.zpowers_le.mpr haH.1) hg
    have hgQ : g * q⁻¹ * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) _).mp (Q.inv_mem hq)
    have e : ⁅q, g⁆ = q * (g * q⁻¹ * g⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem hq hgQ
  have hfix : ∀ x ∈ ⁅Q, Subgroup.zpowers (a : G)⁆, ⁅(k : G), x⁆ ∈ Z := by
    intro x hx
    have hxQ : x ∈ Q := hQcomm hx
    have hximg : M₀.π x ∈ M₀.img (⁅Q, Subgroup.zpowers (a : G)⁆ ⊔ Z) :=
      M₀.pi_mem_img (Subgroup.mem_sup_left hx) hxQ
    have hxr := (hc.mem_img_zpowers_sup_iff φ hφπ haH h.2.2.2.1 (M₀.π x)).mp hximg
    have hT := htriv _ hxr
    have hcommQ : ⁅x, (k : G)⁆ ∈ Q := hc.comm_mem_Q hkH.1 hxQ
    have hpi := pi_commutatorElement hc φ hφπ hxQ (⟨(k : G), hkH⟩ : ↥(H0 M Z))
    have hz : ⁅x, (k : G)⁆ ∈ Z := by
      rw [← M₀.π_ker _ hcommQ]
      show M₀.π ⁅x, (k : G)⁆ = 0
      rw [hpi, hT, sub_self]
    rw [← commutatorElement_inv x (k : G)]
    exact Z.inv_mem hz
  have hcomm := hy.comm_conj_mem_Q_of_fix hc h.1 h.2 hkH hkl hfix i
  rw [← hm] at hcomm
  rw [← hke]
  exact mk_mul_comm_iff_commutator_mem_Q.mpr hcomm

end CFSG.RankThree.GF2n.Stroth80
