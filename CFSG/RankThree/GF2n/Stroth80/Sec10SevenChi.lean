module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Five

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Good103.comm_mem_Vt_iff (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {x : G} (hx : x ∈ Q) :
    ⁅x, t⁆ ∈ Vt M (LB M Q B) B Z t ↔ x ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  have hVT : Vt M (LB M Q B) B Z t = Tt Q Z (Vt M (LB M Q B) B Z t) t :=
    (stroth_10_5 h34 h311a hspread) G M Q Z B hc n t H ht
  have hTU : Tt Q Z (Vt M (LB M Q B) B Z t) t ≤ Ut Q Z t :=
    sup_le_sup_right (Subgroup.commutator_mono inf_le_left le_rfl) Z
  have h := hc.comm_mem_Tt_iff ht.1.mem_LB (hVT.le.trans hTU) hx
  rwa [← hVT] at h

theorem mem_centralizer_of_comm_mem_Z {t : G} (htZ : ∀ z ∈ Z, t * z = z * t)
    (hnf : ∀ w ∈ Q, ∀ z ∈ Z, w * t * w⁻¹ = t * z → z = 1) {x : G} (hx : x ∈ Q)
    (hxt : ⁅x, t⁆ ∈ Z) : x ∈ Subgroup.centralizer ({t} : Set G) := by
  have hcomm : x * t * x⁻¹ = t * ⁅x, t⁆ := by
    calc x * t * x⁻¹ = ⁅x, t⁆ * t := by
          rw [commutatorElement_def]
          group
      _ = t * ⁅x, t⁆ := (htZ ⁅x, t⁆ hxt).symm
  have h1 : ⁅x, t⁆ = 1 := hnf x hx ⁅x, t⁆ hxt hcomm
  have h2 : x * t * x⁻¹ = t := by
    calc x * t * x⁻¹ = t * ⁅x, t⁆ := hcomm
      _ = t * 1 := by rw [h1]
      _ = t := mul_one t
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc x * t = (x * t * x⁻¹) * x := by group
    _ = t * x := by rw [h2]

theorem Ctx.card_centralizer_mul_card_Ut (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (hnf : ∀ w ∈ Q, ∀ z ∈ Z, w * t * w⁻¹ = t * z → z = 1) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card ↥(Ut Q Z t) =
      Nat.card Q * Nat.card Z := by
  obtain ⟨K, hK, hfin, hch, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI := hfin
  obtain ⟨φ, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp hD
  let τ := φ ⟨t, hc.LB_le_H0 ht⟩
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  have hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x) :=
    fun x hx => hφπ ⟨t, hc.LB_le_H0 ht⟩ x hx
  have hcardQ := hc.card_Q_eq_card_Q1_mul_img_Ut htM hD.reg τ htQ htQ' hTπ
  have hcardU : Nat.card ↥(Ut Q Z t) = Nat.card Z * Nat.card (M₀.img (Ut Q Z t)) :=
    M₀.card_eq (hc.Ut_le_Q htM) le_sup_right
  have htZ : ∀ z ∈ Z, t * z = z * t := by
    intro z hz
    have h := hc.LB_centralizes_Z ht z hz
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [h]
  have hQ1 : Q1 hc t = Q ⊓ Subgroup.centralizer ({t} : Set G) := by
    ext x
    rw [hc.mem_Q1_iff htM]
    constructor
    · rintro ⟨hxQ, hxt⟩
      have hxtZ : ⁅x, t⁆ ∈ Z := by
        rw [← commutatorElement_inv t x]
        exact Z.inv_mem hxt
      exact Subgroup.mem_inf.mpr ⟨hxQ,
        mem_centralizer_of_comm_mem_Z htZ hnf hxQ hxtZ⟩
    · intro hx
      refine ⟨(Subgroup.mem_inf.mp hx).1, ?_⟩
      have hxt : t * x = x * t :=
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2).symm
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hxt]
      exact Z.one_mem
  rw [← hQ1, hcardU, hcardQ]
  ring

theorem Ctx.exists_comm_mul_of_mem_Ut (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {u : G}
    (hu : u ∈ Ut Q Z t) : ∃ x ∈ Q, ∃ z ∈ Z, u = ⁅x, t⁆ * z := by
  obtain ⟨x, hxQ, hw⟩ := hc.exists_comm_mul_inv_mem_Z ht hu
  have haQ : ⁅x, t⁆ ∈ Q := hc.comm_mem_Q (hc.LB_le_M ht) hxQ
  set z : G := (⁅x, t⁆ * u⁻¹)⁻¹ with hz
  have hzZ : z ∈ Z := by
    rw [hz]
    exact Z.inv_mem hw
  have hcomm : z * ⁅x, t⁆ = ⁅x, t⁆ * z := by
    rw [hz]
    exact Z_central hc.hyp (Z.inv_mem hw) haQ
  have hwa : z * ⁅x, t⁆ = u := by
    rw [hz]
    group
  refine ⟨x, hxQ, z, hzZ, ?_⟩
  rw [← hwa, hcomm]

theorem Ctx.Wt_centralizer_eq_Ut (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (hnf : ∀ w ∈ Q, ∀ z ∈ Z, w * t * w⁻¹ = t * z → z = 1) :
    Wt Q (Q ⊓ Subgroup.centralizer ({t} : Set G)) = Ut Q Z t := by
  set C : Subgroup G := Q ⊓ Subgroup.centralizer ({t} : Set G)
  have hUW : Ut Q Z t ≤ Wt Q C := Ut_le_Wt_centralizer hc ht
  have hC : Z ≤ C := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hz, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 := hc.LB_centralizes_Z ht z hz
    calc z * t = (t * z * t⁻¹) * t := by rw [h1]
      _ = t * z := by group
  have hbound : Nat.card ↥(Wt Q C) * Nat.card ↥C ≤ Nat.card Q * Nat.card Z :=
    StrothHyp.card_Wt_mul_card_le hc.hyp (X := C) inf_le_left hC
  have hcount := Ctx.card_centralizer_mul_card_Ut hc ht hnf
  have h3 : Nat.card ↥(Wt Q C) * Nat.card ↥C ≤ Nat.card ↥C * Nat.card ↥(Ut Q Z t) := by
    have h := hbound
    rw [← hcount] at h
    exact h
  have h4 : Nat.card ↥(Wt Q C) * Nat.card ↥C ≤ Nat.card ↥(Ut Q Z t) * Nat.card ↥C := by
    calc Nat.card ↥(Wt Q C) * Nat.card ↥C ≤ Nat.card ↥C * Nat.card ↥(Ut Q Z t) := h3
      _ = Nat.card ↥(Ut Q Z t) * Nat.card ↥C := Nat.mul_comm _ _
  have hWU : Nat.card ↥(Wt Q C) ≤ Nat.card ↥(Ut Q Z t) :=
    Nat.le_of_mul_le_mul_right h4 Nat.card_pos
  exact (Subgroup.eq_of_le_of_card_ge hUW hWU).symm

end CFSG.RankThree.GF2n.Stroth80
