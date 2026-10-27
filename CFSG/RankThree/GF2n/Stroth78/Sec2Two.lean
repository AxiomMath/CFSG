module

public import CFSG.RankThree.GF2n.Stroth78.ConjAction

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

private theorem conjQbar_qS (S : Setting z E F) (h : ↥(H z))
    (x : Additive (QbarOf S)) :
    qS S (conjQbar S h x) = qS S x :=
  (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (conjQbar_mem_orthogonal S h)) x

private theorem conjQbar_polar (S : Setting z E F) (h : ↥(H z))
    (x y : Additive (QbarOf S)) :
    (qS S).polarBilin (conjQbar S h x) (conjQbar S h y) =
      (qS S).polarBilin x y := by
  have hx := conjQbar_qS S h x
  have hy := conjQbar_qS S h y
  have hxy := conjQbar_qS S h (x + y)
  rw [map_add (conjQbar S h) x y] at hxy
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [hxy, hx, hy]

theorem stroth78_2_2 (S : Setting z E F) {a r : G}
    (haQ : a ∈ Q z) (haZ : a ∉ ZQ z) (ha2 : a ^ 2 = 1) (hrH : r ∈ H z)
    (hcomm : ∀ u ∈ Q z, ⁅u, a⁆ = 1 → ⁅u, r⁆ = 1) : r ∈ Q z := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  let V := Additive (QbarOf S)
  let aV : V := Additive.ofMul (QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z)))
  let B : LinearMap.BilinForm (ZMod 2) V := (q S).polarBilin
  let φ : V ≃ₗ[ZMod 2] V := conjQbar S (⟨r, hrH⟩ : ↥(H z))
  haveI : Finite V := inferInstance
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hqa : q S aV = 0 := by
    change q S (QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z))) = 0
    exact (q_eq_zero_iff S (⟨a, haQ⟩ : ↥(Q z))).mpr (by simpa using ha2)
  have haV_ne : aV ≠ 0 := by
    intro h
    apply haZ
    have h' : Additive.ofMul ((QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z))) : QbarOf S) = 0 := by
      change aV = 0
      exact h
    have h1 : (QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z)) : QbarOf S) = 1 := by
      have h2 := congrArg Additive.toMul h'
      simpa using h2
    have h2 : (⟨a, haQ⟩ : ↥(Q z)) ∈ (ZQ z).subgroupOf (Q z) :=
      (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  have hB : B.Nondegenerate := q_nondegenerate S
  have hBsymm : B.IsSymm := by
    refine ⟨fun x y => ?_⟩
    simp only [B, QuadraticMap.polarBilin_apply_apply]
    exact QuadraticMap.polar_comm (q S) x y
  have hBrefl : B.IsRefl := hBsymm.isRefl
  have hb_exists : ∃ b : V, B aV b ≠ 0 := by
    by_contra h
    push Not at h
    exact haV_ne (hB.1 aV h)
  obtain ⟨b, hb⟩ := hb_exists
  have hb1 : B aV b = 1 := by
    rcases zmod2_cases (B aV b) with h | h
    · exact absurd h hb
    · exact h
  have hfix : ∀ u : V, u ∈ B.orthogonal (Submodule.span (ZMod 2) ({aV} : Set V)) →
      φ u = u := by
    intro u hu
    have hu0 : B aV u = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hu) aV (Submodule.mem_span_singleton_self aV)
    obtain ⟨x, rfl⟩ := Additive.ofMul.surjective u
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    change conjQbar S (⟨r, hrH⟩ : ↥(H z)) (Additive.ofMul (QuotientGroup.mk y)) =
      Additive.ofMul (QuotientGroup.mk y)
    rw [conjQbar_apply_mk]
    have hu0' : QuadraticMap.polar (q S) (QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z)))
        (QuotientGroup.mk y) = 0 := by
      have h := hu0
      change QuadraticMap.polar (q S) (QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z)))
        (QuotientGroup.mk y) = 0 at h
      exact h
    have hay : (a : G) * (y : G) = (y : G) * a :=
      (polar_q_eq_zero_iff S (⟨a, haQ⟩ : ↥(Q z)) y).mp hu0'
    have hya : ⁅(y : G), a⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr hay.symm
    have hyr : ⁅(y : G), r⁆ = 1 := hcomm (y : G) y.2 hya
    have hconj : conjAutQ S (⟨r, hrH⟩ : ↥(H z)) y = y := by
      apply Subtype.ext
      rw [conjAutQ_apply]
      have hry : (r : G) * (y : G) = (y : G) * (r : G) :=
        (commutatorElement_eq_one_iff_mul_comm.mp hyr).symm
      rw [hry]
      group
    rw [hconj]
  have hiso : ∀ x y : V, B (φ x) (φ y) = B x y := by
    intro x y
    change (qS S).polarBilin (conjQbar S (⟨r, hrH⟩ : ↥(H z)) x)
        (conjQbar S (⟨r, hrH⟩ : ↥(H z)) y) = (qS S).polarBilin x y
    exact conjQbar_polar S (⟨r, hrH⟩ : ↥(H z)) x y
  have hmem : φ b - b ∈
      B.orthogonal (B.orthogonal (Submodule.span (ZMod 2) ({aV} : Set V))) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hfixu : φ u = u := hfix u hu
    have hfixu_inv : φ.symm u = u := by
      calc
        φ.symm u = φ.symm (φ u) := by rw [hfixu]
        _ = u := φ.symm_apply_apply u
    calc
      B u (φ b - b) = B u (φ b) - B u b := by rw [map_sub]
      _ = B (φ (φ.symm u)) (φ b) - B u b := by rw [LinearEquiv.apply_symm_apply]
      _ = B (φ.symm u) b - B u b := by rw [hiso]
      _ = B u b - B u b := by rw [hfixu_inv]
      _ = 0 := sub_self _
  have horth : B.orthogonal (B.orthogonal (Submodule.span (ZMod 2) ({aV} : Set V))) =
      Submodule.span (ZMod 2) ({aV} : Set V) :=
    LinearMap.BilinForm.orthogonal_orthogonal hB hBrefl _
  have hspan : φ b - b ∈ Submodule.span (ZMod 2) ({aV} : Set V) := by
    rw [← horth]
    exact hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  have hφb : φ b = b + c • aV := by
    calc
      φ b = (φ b - b) + b := (sub_add_cancel (φ b) b).symm
      _ = c • aV + b := by rw [hc.symm]
      _ = b + c • aV := add_comm _ _
  have hφq : q S (φ b) = q S b := by
    change qS S (conjQbar S (⟨r, hrH⟩ : ↥(H z)) b) = qS S b
    exact conjQbar_qS S (⟨r, hrH⟩ : ↥(H z)) b
  have hq1 : q S (b + c • aV) = q S b + c := by
    rw [QuadraticMap.map_add (q S)]
    rw [QuadraticMap.map_smul (q S), hqa, smul_zero, add_zero]
    rw [QuadraticMap.polar_smul_right (q S)]
    have hp : QuadraticMap.polar (q S) b aV = 1 := by
      rw [QuadraticMap.polar_comm (q S)]
      simpa [B, QuadraticMap.polarBilin_apply_apply] using hb1
    rw [hp, smul_eq_mul, mul_one]
  have hczero : c = 0 := by
    have hmain : q S b + c = q S b := by
      rw [← hq1, ← hφb]
      exact hφq
    have h : q S b + c = q S b + 0 := by simpa using hmain
    exact add_left_cancel h
  have hφb_fix : φ b = b := by
    rw [hφb, hczero, zero_smul, add_zero]
  have hφ_eq_one : φ = 1 := by
    refine LinearEquiv.ext fun v => ?_
    have hv_mem : v - B aV v • b ∈
        B.orthogonal (Submodule.span (ZMod 2) ({aV} : Set V)) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hn
      calc
        B (μ • aV) (v - B aV v • b)
            = μ • B aV (v - B aV v • b) := by
              rw [LinearMap.map_smul, LinearMap.smul_apply]
        _ = μ • (B aV v - B aV ((B aV v) • b)) := by rw [LinearMap.map_sub]
        _ = μ • (B aV v - (B aV v) • B aV b) := by rw [LinearMap.map_smul]
        _ = μ • (B aV v - (B aV v) • (1 : ZMod 2)) := by rw [hb1]
        _ = 0 := by simp [smul_eq_mul]
    have hv : φ v = v := by
      calc
        φ v = φ ((v - B aV v • b) + B aV v • b) := by rw [sub_add_cancel]
        _ = φ (v - B aV v • b) + φ (B aV v • b) := by rw [map_add]
        _ = (v - B aV v • b) + B aV v • φ b := by rw [hfix _ hv_mem, map_smul]
        _ = (v - B aV v • b) + B aV v • b := by rw [hφb_fix]
        _ = v := sub_add_cancel _ _
    simpa using hv
  refine (S.hyp.centralizer_quotient r).mp ⟨hrH, ?_⟩
  intro x hx
  have hfixx : conjQbar S (⟨r, hrH⟩ : ↥(H z))
      (Additive.ofMul (QuotientGroup.mk (⟨x, hx⟩ : ↥(Q z)))) =
      Additive.ofMul (QuotientGroup.mk (⟨x, hx⟩ : ↥(Q z))) := by
    change φ _ = _
    rw [hφ_eq_one]
    rfl
  rw [conjQbar_apply_mk] at hfixx
  have hq : (QuotientGroup.mk (conjAutQ S (⟨r, hrH⟩ : ↥(H z))
        (⟨x, hx⟩ : ↥(Q z))) : QbarOf S) =
      QuotientGroup.mk (⟨x, hx⟩ : ↥(Q z)) :=
    Additive.ofMul.injective hfixx
  have hmem := (QuotientGroup.eq_iff_div_mem).mp hq
  have hmem' : conjAutQ S (⟨r, hrH⟩ : ↥(H z)) (⟨x, hx⟩ : ↥(Q z)) *
      (⟨x, hx⟩ : ↥(Q z))⁻¹ ∈ (ZQ z).subgroupOf (Q z) := by
    simpa [div_eq_mul_inv] using hmem
  have hmemG : ((conjAutQ S (⟨r, hrH⟩ : ↥(H z)) (⟨x, hx⟩ : ↥(Q z)) *
      (⟨x, hx⟩ : ↥(Q z))⁻¹ : ↥(Q z)) : G) ∈ ZQ z :=
    Subgroup.mem_subgroupOf.mp hmem'
  simpa [conjAutQ_apply, div_eq_mul_inv] using hmemG

end CFSG.RankThree.GF2n.Stroth78
