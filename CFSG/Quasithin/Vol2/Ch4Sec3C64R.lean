module

public import CFSG.Quasithin.Vol2.Ch4Sec3C64Y
public import CFSG.Quasithin.Vol2.Ch4Sec3C64Cob
public import CFSG.Quasithin.Vol2.Ch4Sec3C64TH

public section

namespace CFSG.Quasithin.H13.Ch4.C64

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv

variable {G : Type} [Group G] [Finite G]

@[expose] def sqComm (E : Subgroup G) : Subgroup G :=
  Subgroup.closure ({x | ∃ e ∈ E, x = e ^ 2} ∪ {x | ∃ e ∈ E, ∃ e' ∈ E, x = e * e' * e⁻¹ * e'⁻¹})

omit [Finite G] in
theorem sqComm_le {E K : Subgroup G} (h1 : ∀ e ∈ E, e ^ 2 ∈ K)
    (h2 : ∀ e ∈ E, ∀ e' ∈ E, e * e' * e⁻¹ * e'⁻¹ ∈ K) : sqComm E ≤ K := by
  rw [sqComm, Subgroup.closure_le]
  rintro x (⟨e, he, rfl⟩ | ⟨e, he, e', he', rfl⟩)
  · exact h1 e he
  · exact h2 e he e' he'

theorem mem_normalizer_sqComm {E : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) :
    g ∈ Subgroup.normalizer ((sqComm E : Subgroup G) : Set G) := by
  have hE : ∀ e ∈ E, g * e * g⁻¹ ∈ E := fun e he => (Subgroup.mem_normalizer_iff.1 hg e).1 he
  apply mem_normalizer_of_conj_mem
  have hle : sqComm E ≤ (sqComm E).comap (MulAut.conj g).toMonoidHom := by
    refine sqComm_le (fun e he => ?_) (fun e he e' he' => ?_)
    · show g * e ^ 2 * g⁻¹ ∈ sqComm E
      have e1 : g * e ^ 2 * g⁻¹ = (g * e * g⁻¹) ^ 2 := by
        rw [pow_two, pow_two]
        group
      rw [e1]
      exact Subgroup.subset_closure (Or.inl ⟨_, hE e he, rfl⟩)
    · show g * (e * e' * e⁻¹ * e'⁻¹) * g⁻¹ ∈ sqComm E
      have e1 : g * (e * e' * e⁻¹ * e'⁻¹) * g⁻¹ = (g * e * g⁻¹) * (g * e' * g⁻¹) *
          (g * e * g⁻¹)⁻¹ * (g * e' * g⁻¹)⁻¹ := by group
      rw [e1]
      exact Subgroup.subset_closure (Or.inr ⟨_, hE e he, _, hE e' he', rfl⟩)
  intro x hx
  exact hle hx

omit [Finite G] in
theorem comm_mul_mul {x y a b : G} (hxa : Commute x a) (hxb : Commute x b) (hya : Commute y a)
    (hyb : Commute y b) (hxy : Commute x y) :
    (x * a) * (y * b) * (x * a)⁻¹ * (y * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hc : Commute x (a * b * a⁻¹ * b⁻¹) :=
    ((hxa.mul_right hxb).mul_right hxa.inv_right).mul_right hxb.inv_right
  have hc' : Commute y (a * b * a⁻¹ * b⁻¹) :=
    ((hya.mul_right hyb).mul_right hya.inv_right).mul_right hyb.inv_right
  have e1 : (x * a) * (y * b) = x * y * (a * b) := by
    rw [mul_assoc x a, ← mul_assoc a y b, ← hya.eq, mul_assoc y a b, ← mul_assoc x y]
  have e2 : (x * a)⁻¹ * (y * b)⁻¹ = (b * a)⁻¹ * (x * y)⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev]
    congr 1
    rw [mul_assoc y b, ← mul_assoc b x a, ← hxb.eq, mul_assoc x b a, ← mul_assoc y x, hxy.eq]
  calc (x * a) * (y * b) * (x * a)⁻¹ * (y * b)⁻¹
      = (x * a) * (y * b) * ((x * a)⁻¹ * (y * b)⁻¹) := by group
    _ = x * y * (a * b) * ((b * a)⁻¹ * (x * y)⁻¹) := by rw [e1, e2]
    _ = x * y * (a * b * a⁻¹ * b⁻¹) * (x * y)⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * (x * y) * (x * y)⁻¹ := by
        rw [mul_assoc x y, hc'.eq, ← mul_assoc, hc.eq]
        group
    _ = a * b * a⁻¹ * b⁻¹ := by group

namespace Hyp64

variable {L R TH Sig : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
  {β : ↥(blockU L) →* Multiplicative (AltHeart 7)} {a b : Fin 7}
  (h : Hyp64 L R TH Sig α β a b)
include h

theorem Q_le_centralizer : pCoreOf 2 (L ⊔ TH) ≤ Subgroup.centralizer (blockU L : Set G) :=
  pCoreOf_le_centralizer_blockU h.blk.short h.TH2 h.THL

omit [Finite G] in
theorem R_le_H : R ≤ L ⊔ TH := h.RTH.trans le_sup_right

omit [Finite G] in
theorem R_le_N_Q : R ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ TH) : Set G) :=
  h.R_le_H.trans
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ TH))

omit [Finite G] in
theorem mem_Q_of_induces_one {r : G} (hr : r ∈ R)
    (h1 : ∀ k : ↥L, α ((conjAct L (⟨r, h.RN hr⟩ : ↥(Subgroup.normalizer (L : Set G)))) k) =
      α k) : r ∈ pCoreOf 2 (L ⊔ TH) := by
  apply h.R4 r hr
  intro l hl
  have hk : (conjAct L (⟨r, h.RN hr⟩ : ↥(Subgroup.normalizer (L : Set G)))) ⟨l⁻¹, L.inv_mem hl⟩ =
      ⟨r * l⁻¹ * r⁻¹, (Subgroup.mem_normalizer_iff.1 (h.RN hr) _).1 (L.inv_mem hl)⟩ :=
    Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe L
      (Subgroup.inclusion le_rfl ⟨r, h.RN hr⟩) _)
  have h2 : α (⟨l, hl⟩ * ⟨r * l⁻¹ * r⁻¹,
      (Subgroup.mem_normalizer_iff.1 (h.RN hr) _).1 (L.inv_mem hl)⟩) = 1 := by
    rw [map_mul, ← hk, h1, ← map_mul]
    rw [show (⟨l, hl⟩ : ↥L) * ⟨l⁻¹, L.inv_mem hl⟩ = 1 from Subtype.ext (mul_inv_cancel l),
      map_one]
  rw [← MonoidHom.mem_ker, h.blk.ker] at h2
  have h3 := (L246.mem_blockQ_iff _).2 h2
  have e : ((⟨l, hl⟩ * ⟨r * l⁻¹ * r⁻¹,
      (Subgroup.mem_normalizer_iff.1 (h.RN hr) _).1 (L.inv_mem hl)⟩ : ↥L) : G) =
      l * r * l⁻¹ * r⁻¹ := by
    show l * (r * l⁻¹ * r⁻¹) = l * r * l⁻¹ * r⁻¹
    group
  rw [e] at h3
  exact h3

theorem mem_Q_iff {r : G} (hr : r ∈ R) :
    r ∈ pCoreOf 2 (L ⊔ TH) ↔ r ∈ Subgroup.centralizer (blockU L : Set G) := by
  refine ⟨fun hq => h.Q_le_centralizer hq, fun hrU => ?_⟩
  rcases h.R1 ⟨r, h.RN hr⟩ hr with h1 | h1
  · exact h.mem_Q_of_induces_one hr h1
  · exfalso
    have hσ := h.blk.isCoordAct_of_conjAct ⟨r, h.RN hr⟩ h1
    have h1' : H13.A7.IsCoordAct h.blk.psi r 1 := by
      intro x z hxz
      have : z = x := Subtype.ext (by
        rw [hxz, (Subgroup.mem_centralizer_iff.1 hrU x x.2).symm]
        group)
      rw [this, SteinbergCB.permAct7_one]
    have h2 := H13.A7.IsCoordAct.unique h.blk.psi (C1.mem_normalizer_blockU (h.RN hr)) hσ h1'
    have h3 := congrArg (fun σ : Perm (Fin 7) => σ a) h2
    simp only [swap_apply_left, Perm.one_apply] at h3
    exact h.hab h3.symm

theorem isCoordAct_swap {r : G} (hr : r ∈ R) (hrQ : r ∉ pCoreOf 2 (L ⊔ TH)) :
    H13.A7.IsCoordAct h.blk.psi r (swap a b) := by
  rcases h.blk.isCoordAct_one_or_swap h.RN h.R1 hr with h1 | h1
  · exfalso
    apply hrQ
    rw [h.mem_Q_iff hr, Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 := h1 ⟨x, hx⟩ ⟨r * x * r⁻¹, (Subgroup.mem_normalizer_iff.1
      (C1.mem_normalizer_blockU (h.RN hr)) x).1 hx⟩ rfl
    rw [SteinbergCB.permAct7_one] at h2
    have h3 : r * x * r⁻¹ = x := congrArg Subtype.val (H13.A7.vec_injective h.blk.psi h2)
    calc x * r = (r * x * r⁻¹) * r := by rw [h3]
      _ = r * x := by group
  · exact h1

theorem inv_mul_mem_Q {r r' : G} (hr : r ∈ R) (hr' : r' ∈ R) (hrQ : r ∉ pCoreOf 2 (L ⊔ TH))
    (hr'Q : r' ∉ pCoreOf 2 (L ⊔ TH)) : r⁻¹ * r' ∈ pCoreOf 2 (L ⊔ TH) := by
  have h1 := h.isCoordAct_swap hr hrQ
  have h2 := h.isCoordAct_swap hr' hr'Q
  have hrU : r ∈ Subgroup.normalizer (blockU L : Set G) := C1.mem_normalizer_blockU (h.RN hr)
  have hr'U : r' ∈ Subgroup.normalizer (blockU L : Set G) := C1.mem_normalizer_blockU (h.RN hr')
  rw [h.mem_Q_iff (R.mul_mem (R.inv_mem hr) hr'), Subgroup.mem_centralizer_iff]
  intro x hx
  set z : ↥(blockU L) := ⟨r' * x * r'⁻¹, (Subgroup.mem_normalizer_iff.1 hr'U x).1 hx⟩ with hz
  set w : ↥(blockU L) := ⟨r⁻¹ * z * r, by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hrU) z).1 z.2
    simpa using this⟩ with hw
  have e1 := h2 ⟨x, hx⟩ z rfl
  have e2 := h1 w z (by
    show (r' * x * r'⁻¹ : G) = r * (r⁻¹ * (r' * x * r'⁻¹) * r) * r⁻¹
    group)
  have e3 : H13.A7.vec h.blk.psi w = H13.A7.vec h.blk.psi ⟨x, hx⟩ := by
    have := congrArg (SteinbergCB.permAct7 (swap a b)) e2
    rw [← SteinbergCB.permAct7_mul, swap_mul_self, SteinbergCB.permAct7_one, e1,
      ← SteinbergCB.permAct7_mul, swap_mul_self, SteinbergCB.permAct7_one] at this
    exact this.symm
  have e4 := congrArg Subtype.val (H13.A7.vec_injective h.blk.psi e3)
  have e5 : r⁻¹ * (r' * x * r'⁻¹) * r = x := e4
  calc x * (r⁻¹ * r') = (r⁻¹ * (r' * x * r'⁻¹) * r) * (r⁻¹ * r') := by rw [e5]
    _ = r⁻¹ * r' * x := by group

theorem exists_data {u : ↥(blockU L)}
    (hu : Multiplicative.toAdd (β u) = (QuotientAddGroup.mk (A7.pairVec a b) : AltHeart 7)) :
    ∃ (E : Subgroup G) (s t : G), (∀ x ∈ E, x ^ 2 = 1) ∧ (∀ x ∈ E, ∀ x' ∈ E, x * x' = x' * x) ∧
      s * s = 1 ∧ t * t = 1 ∧ (∀ x ∈ E, s * x = x * s) ∧ (∀ x ∈ E, t * x = x * t) ∧
      (s * t) ^ 2 = (u : G) ∧ (u : G) ∈ E ∧ (u : G) ≠ 1 ∧ s ∉ E ∧ t ∉ pCoreOf 2 (L ⊔ TH) ∧
      pCoreOf 2 (L ⊔ TH) = E ⊔ Subgroup.zpowers s ∧ R = E ⊔ Subgroup.closure {s, t} := by
  classical
  obtain ⟨y, hyX, hyR, hy2, hyc, u₀, hu₀, hu₀Q⟩ := h.exists_y
  have hL := h.blk.short
  set Q := pCoreOf 2 (L ⊔ TH) with hQ
  have hyN : y ∈ Subgroup.normalizer (R : Set G) := hyX.2
  have hyRR : ∀ r ∈ R, y * r * y⁻¹ ∈ R := fun r hr => (Subgroup.mem_normalizer_iff.1 hyN r).1 hr
  have hyRR' : ∀ r ∈ R, y⁻¹ * r * y ∈ R := fun r hr => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hyN) r).1 hr
    simpa using this
  have hUQ : blockU L ≤ Q := h.U_le_Q
  have hUR : blockU L ≤ R := hUQ.trans h.QR
  have hQU : ∀ q ∈ Q, ∀ v ∈ blockU L, q * v = v * q := fun q hq v hv =>
    (Subgroup.mem_centralizer_iff.1 (h.Q_le_centralizer hq) v hv).symm
  have hU2 : ∀ v ∈ blockU L, v * v = 1 := fun v hv => by
    have := C1.blockU_sq hL v hv
    rwa [pow_two] at this
  have hHQ : L ⊔ TH ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ TH)
  have hy2Q : y ^ 2 ∈ Subgroup.normalizer (Q : Set G) := h.R_le_N_Q hy2
  set Qy : Subgroup G := Q.map (MulAut.conj y).toMonoidHom with hQy
  have mem_Qy : ∀ x, x ∈ Qy ↔ y⁻¹ * x * y ∈ Q := by
    intro x
    constructor
    · rintro ⟨q, hq, rfl⟩
      have e : y⁻¹ * (y * q * y⁻¹) * y = q := by group
      simpa [MulAut.conj_apply, e] using hq
    · intro hx
      refine ⟨y⁻¹ * x * y, hx, ?_⟩
      show y * (y⁻¹ * x * y) * y⁻¹ = x
      group
  have inv_mul_mem_Qy : ∀ r ∈ R, ∀ r' ∈ R, r ∉ Qy → r' ∉ Qy → r⁻¹ * r' ∈ Qy := by
    intro r hr r' hr' hrQ hr'Q
    rw [mem_Qy] at hrQ hr'Q ⊢
    have h1 := h.inv_mul_mem_Q (hyRR' r hr) (hyRR' r' hr') hrQ hr'Q
    have e : y⁻¹ * (r⁻¹ * r') * y = (y⁻¹ * r * y)⁻¹ * (y⁻¹ * r' * y) := by group
    rw [e]
    exact h1
  set t : G := y * u₀ * y⁻¹ with ht
  have htR : t ∈ R := hyRR u₀ (hUR hu₀)
  have htQy : t ∈ Qy := by
    rw [mem_Qy, ht, show y⁻¹ * (y * u₀ * y⁻¹) * y = u₀ by group]
    exact hUQ hu₀
  have ht2 : t * t = 1 := by
    rw [ht, show y * u₀ * y⁻¹ * (y * u₀ * y⁻¹) = y * (u₀ * u₀) * y⁻¹ by group, hU2 u₀ hu₀]
    group
  have htact := h.isCoordAct_swap htR hu₀Q
  obtain ⟨c, hca, hcb⟩ : ∃ c : Fin 7, c ≠ a ∧ c ≠ b := by
    by_contra hne
    push Not at hne
    have h2 : (Finset.univ : Finset (Fin 7)) ⊆ {a, b} := fun c _ => by
      by_cases hc : c = a
      · simp [hc]
      · simp [hne c hc]
    have h3 := Finset.card_le_card h2
    rw [Finset.card_univ, Fintype.card_fin] at h3
    have h4 := Finset.card_le_two (a := a) (b := b)
    omega
  obtain ⟨s', hs'⟩ := exists_crd_eq h.blk (SteinbergCB.pair_mem_evenWeight a c)
  have hsU : (s' : G) ∈ blockU L := s'.2
  have hs2 : (s' : G) * s' = 1 := hU2 _ hsU
  have htU : t ∈ Subgroup.normalizer (blockU L : Set G) := C1.mem_normalizer_blockU (h.RN htR)
  set w₀ : ↥(blockU L) := ⟨t * s' * t⁻¹, (Subgroup.mem_normalizer_iff.1 htU s').1 hsU⟩ with hw₀
  have hcu := crd_eq_pair hu
  have hsw : s'⁻¹ * w₀ = u := by
    have h1 := htact s' w₀ rfl
    rw [h.blk.vec_psi, h.blk.vec_psi] at h1
    apply h.blk.crd_injective
    rw [crd_mul, crd_inv, h1, add_permAct7_swap _ h.hab, hs', hcu]
    simp only [Pi.add_apply, Pi.single_apply, Ne.symm hca, Ne.symm hcb, Ne.symm h.hab,
      ite_true, ite_false, add_zero, one_smul]
  have hst : ((s' : G) * t) ^ 2 = (u : G) := by
    have h1 : ((s'⁻¹ * w₀ : ↥(blockU L)) : G) = (s' : G)⁻¹ * (t * s' * t⁻¹) := rfl
    have hsinv : (s' : G)⁻¹ = s' := inv_eq_of_mul_eq_one_right hs2
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    rw [← hsw, h1, hsinv, htinv, pow_two]
    group
  have hu1 : (u : G) ≠ 1 := by
    intro h1
    have h2 := congrFun hcu a
    rw [show u = 1 from Subtype.ext h1, crd_one] at h2
    simp [h.hab] at h2
  have hsQy : (s' : G) ∉ Qy := by
    intro h1
    rw [mem_Qy] at h1
    have h2 := hQU _ h1 u₀ hu₀
    have h3 : (s' : G) * t = t * s' := by
      rw [ht]
      calc (s' : G) * (y * u₀ * y⁻¹) = y * ((y⁻¹ * s' * y) * u₀) * y⁻¹ := by group
        _ = y * (u₀ * (y⁻¹ * s' * y)) * y⁻¹ := by rw [h2]
        _ = y * u₀ * y⁻¹ * s' := by group
    apply hu1
    rw [← hst, pow_two, mul_assoc, ← mul_assoc t, ← h3, mul_assoc, ht2, mul_one, hs2]
  set E : Subgroup G := Q ⊓ Qy with hE
  have hEs : ∀ x ∈ E, (s' : G) * x = x * s' := fun x hx => (hQU x hx.1 s' hsU).symm
  have hEt : ∀ x ∈ E, t * x = x * t := by
    intro x hx
    have h1 := hQU _ ((mem_Qy x).1 hx.2) u₀ hu₀
    rw [ht]
    calc y * u₀ * y⁻¹ * x = y * (u₀ * (y⁻¹ * x * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * x * y) * u₀) * y⁻¹ := by rw [h1]
      _ = x * (y * u₀ * y⁻¹) := by group
  have hsE : (s' : G) ∉ E := fun h1 => hsQy h1.2
  have hQE : Q = E ⊔ Subgroup.zpowers (s' : G) := by
    refine le_antisymm (fun q hq => ?_)
      (sup_le inf_le_left (Subgroup.zpowers_le.2 (hUQ hsU)))
    by_cases hqQy : q ∈ Qy
    · exact Subgroup.mem_sup_left ⟨hq, hqQy⟩
    · have h1 := inv_mul_mem_Qy _ (hUR hsU) q (h.QR hq) hsQy hqQy
      have h2 : (s' : G)⁻¹ * q ∈ Q := Q.mul_mem (Q.inv_mem (hUQ hsU)) hq
      have e : q = (s' : G) * ((s' : G)⁻¹ * q) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_left ⟨h2, h1⟩)
  have hRE : R = E ⊔ Subgroup.closure {(s' : G), t} := by
    refine le_antisymm (fun r hr => ?_) (sup_le (inf_le_left.trans h.QR)
      ((Subgroup.closure_le _).2 (by
        rintro x (rfl | rfl)
        · exact hUR hsU
        · exact htR)))
    have hQle : Q ≤ E ⊔ Subgroup.closure {(s' : G), t} := by
      rw [hQE]
      exact sup_le_sup_left (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))) _
    by_cases hrQ : r ∈ Q
    · exact hQle hrQ
    · have h1 := h.inv_mul_mem_Q htR hr hu₀Q hrQ
      have e : r = t * (t⁻¹ * r) := by group
      rw [e]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))) (hQle h1)
  set S := sqComm E with hS
  have hlE : ∀ l ∈ L, ∀ e ∈ Q, ∃ κ ∈ blockU L, l * e * l⁻¹ = κ * e := by
    intro l hl e he
    refine ⟨(e * l * e⁻¹ * l⁻¹)⁻¹,
      (blockU L).inv_mem (VolI.commutator_mem_blockU hL h.THL he hl), by group⟩
  have hSC : S ≤ Subgroup.centralizer (L : Set G) := by
    refine sqComm_le (fun e he => ?_) (fun e he e' he' => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      obtain ⟨κ, hκ, hle⟩ := hlE l hl e he.1
      have hκe : κ * e = e * κ := (hQU e he.1 κ hκ).symm
      have h1 : l * e ^ 2 * l⁻¹ = e ^ 2 := by
        calc l * e ^ 2 * l⁻¹ = (l * e * l⁻¹) * (l * e * l⁻¹) := by rw [pow_two]; group
          _ = (κ * e) * (κ * e) := by rw [hle]
          _ = (κ * κ) * (e * e) := by rw [mul_assoc κ e, ← mul_assoc e κ, ← hκe]; group
          _ = e ^ 2 := by rw [hU2 κ hκ, one_mul, pow_two]
      calc l * e ^ 2 = (l * e ^ 2 * l⁻¹) * l := by group
        _ = e ^ 2 * l := by rw [h1]
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      obtain ⟨κ, hκ, hle⟩ := hlE l hl e he.1
      obtain ⟨κ', hκ', hle'⟩ := hlE l hl e' he'.1
      have h1 : l * (e * e' * e⁻¹ * e'⁻¹) * l⁻¹ = e * e' * e⁻¹ * e'⁻¹ := by
        calc l * (e * e' * e⁻¹ * e'⁻¹) * l⁻¹ = (l * e * l⁻¹) * (l * e' * l⁻¹) *
              (l * e * l⁻¹)⁻¹ * (l * e' * l⁻¹)⁻¹ := by group
          _ = (κ * e) * (κ' * e') * (κ * e)⁻¹ * (κ' * e')⁻¹ := by rw [hle, hle']
          _ = e * e' * e⁻¹ * e'⁻¹ := comm_mul_mul (hQU e he.1 κ hκ).symm
              (hQU e' he'.1 κ hκ).symm (hQU e he.1 κ' hκ').symm (hQU e' he'.1 κ' hκ').symm
              (AppC.blockU_comm_blockU hL hκ hκ')
      calc l * (e * e' * e⁻¹ * e'⁻¹) = (l * (e * e' * e⁻¹ * e'⁻¹) * l⁻¹) * l := by group
        _ = e * e' * e⁻¹ * e'⁻¹ * l := by rw [h1]
  have hSE : S ≤ E := sqComm_le (fun e he => E.pow_mem he 2)
    (fun e he e' he' => E.mul_mem (E.mul_mem (E.mul_mem he he') (E.inv_mem he)) (E.inv_mem he'))
  have hTQy : TH ≤ Subgroup.normalizer (Qy : Set G) := by
    intro t' ht'
    apply mem_normalizer_of_conj_mem
    intro x hx
    rw [mem_Qy] at hx ⊢
    have hr := hyc t' ht'
    have hc : y⁻¹ * t' * y ∈ TH := by
      have e : y⁻¹ * t' * y = (y⁻¹ * (t' * y * t'⁻¹ * y⁻¹) * y) * t' := by group
      rw [e]
      exact TH.mul_mem (h.RTH (hyRR' _ hr)) ht'
    have h1 := (Subgroup.mem_normalizer_iff.1 (hHQ (Subgroup.mem_sup_right hc)) _).1 hx
    have e : y⁻¹ * (t' * x * t'⁻¹) * y =
        (y⁻¹ * t' * y) * (y⁻¹ * x * y) * (y⁻¹ * t' * y)⁻¹ := by group
    rw [e]
    exact h1
  have hTE : TH ≤ Subgroup.normalizer (E : Set G) := fun t' ht' =>
    mem_normalizer_inf (hHQ (Subgroup.mem_sup_right ht')) (hTQy ht')
  have hyE : y ∈ Subgroup.normalizer (E : Set G) := by
    apply mem_normalizer_of_conj_mem
    rintro x ⟨hxQ, hxQy⟩
    refine Subgroup.mem_inf.2 ⟨?_, (mem_Qy _).2 ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.1 hy2Q _).1 ((mem_Qy x).1 hxQy)
      have e : y * x * y⁻¹ = y ^ 2 * (y⁻¹ * x * y) * (y ^ 2)⁻¹ := by
        rw [pow_two]
        group
      rw [e]
      exact h1
    · rw [show y⁻¹ * (y * x * y⁻¹) * y = x by group]
      exact hxQ
  have hSbot : S = ⊥ := by
    by_contra hne
    have hLS : L ≤ Subgroup.normalizer (S : Set G) := by
      intro l hl
      apply mem_normalizer_of_conj_mem
      intro x hx
      have h1 := Subgroup.mem_centralizer_iff.1 (hSC hx) l hl
      rw [h1]
      group
      exact hx
    have hII := h.II S hne (hSE.trans (inf_le_left.trans h.QR))
      (sup_le hLS fun t' ht' => mem_normalizer_sqComm (hTE ht'))
    have hyS : y ∈ Sig ⊓ Subgroup.normalizer (S : Set G) := ⟨hyX.1, mem_normalizer_sqComm hyE⟩
    rw [hII] at hyS
    exact hyR hyS
  have huE : (u : G) ∈ E := by
    have hTu := h.blk.le_centralizer_of_normalizes h.hab h.RN h.R1 h.R2 h.THL h.THR hu
    refine ⟨hUQ u.2, (mem_Qy _).2 ?_⟩
    rw [h.mem_Q_iff (hyRR' _ (hUR u.2)), Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : y * v * y⁻¹ ∈ R := hyRR v (hUR hv)
    have h2 := Subgroup.mem_centralizer_singleton_iff.1 (hTu (h.RTH h1))
    calc v * (y⁻¹ * u * y) = y⁻¹ * ((y * v * y⁻¹) * u) * y := by group
      _ = y⁻¹ * (u * (y * v * y⁻¹)) * y := by rw [h2]
      _ = y⁻¹ * u * y * v := by group
  refine ⟨E, s', t, fun x hx => ?_, fun x hx x' hx' => ?_, hs2, ht2, hEs, hEt, hst, huE, hu1,
    hsE, hu₀Q, hQE, hRE⟩
  · have h1 : x ^ 2 ∈ S := Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩)
    rw [hSbot, Subgroup.mem_bot] at h1
    exact h1
  · have h1 : x * x' * x⁻¹ * x'⁻¹ ∈ S := Subgroup.subset_closure (Or.inr ⟨x, hx, x', hx', rfl⟩)
    rw [hSbot, Subgroup.mem_bot] at h1
    calc x * x' = (x * x' * x⁻¹ * x'⁻¹) * (x' * x) := by group
      _ = x' * x := by rw [h1, one_mul]

end Hyp64

end CFSG.Quasithin.H13.Ch4.C64
