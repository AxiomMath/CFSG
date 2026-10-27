module

public import CFSG.RankThree.GF2n.Smith81.S81NLift1

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LCond

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] {M Q Z X : Subgroup G} {x : G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}


@[expose] def ZetaRel (Q Z : Subgroup G) (x m z : G) : Prop :=
  z ∈ Z ∧ ∃ q ∈ Q, m * x * m⁻¹ = q * x * q⁻¹ * z

section Lift2
variable [Finite G] [CharP K 2]

private theorem zetaRel_iff {m z : G} :
    ZetaRel Q Z x m z ↔ z ∈ Z ∧ ∃ q ∈ Q, m * x * m⁻¹ = q * x * q⁻¹ * z := Iff.rfl

private theorem H0_conj_Z {a : G} (ha : a ∈ H0 M Z) {z : G} (hz : z ∈ Z) :
    a * z * a⁻¹ = z := by
  have hc : z * a = a * z := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2 z hz
  rw [← hc]
  group

private theorem x_mul_Z_comm (hs : Sit M Q Z X x) {z : G} (hz : z ∈ Z) : x * z = z * x :=
  mul_inv_eq_iff_eq_mul.mp (hs.x_cent (smith_1_12 hs) z hz)

theorem zetaRel_of_piComm (hs : Sit M Q Z X x) (Tx : XAct M₀ x) {u : G} (hu0 : u ∈ H0 M Z)
    (hux : ⁅u, x⁆ ∈ Q) (hπ : M₀.π ⁅u, x⁆ ∈ Rs Tx) : ∃ z, ZetaRel Q Z x u z := by
  obtain ⟨d, hdQ, z, hzZ, hz⟩ := exists_comm_of_mem_Rs hs Tx hux hπ
  refine ⟨z, zetaRel_iff.mpr ⟨hzZ, d, hdQ, ?_⟩⟩
  have hxz : x * z = z * x := x_mul_Z_comm hs hzZ
  have e2 : ⁅d, x⁆ * x = d * x * d⁻¹ := by
    rw [commutatorElement_def]
    group
  calc u * x * u⁻¹ = ⁅u, x⁆ * x := by
        rw [commutatorElement_def]
        group
    _ = (⁅d, x⁆ * z) * x := by rw [hz]
    _ = ⁅d, x⁆ * (z * x) := by group
    _ = ⁅d, x⁆ * (x * z) := by rw [← hxz]
    _ = (⁅d, x⁆ * x) * z := by group
    _ = d * x * d⁻¹ * z := by rw [e2]

theorem zetaRel_mul (hs : Sit M Q Z X x) {a b za zb : G} (ha0 : a ∈ H0 M Z) (hb0 : b ∈ H0 M Z)
    (hza : ZetaRel Q Z x a za) (hzb : ZetaRel Q Z x b zb) : ZetaRel Q Z x (a * b) (za * zb) := by
  obtain ⟨hzaZ, q, hq, hA⟩ := zetaRel_iff.mp hza
  obtain ⟨hzbZ, q', hq', hB⟩ := zetaRel_iff.mp hzb
  have haM : a ∈ M := (Subgroup.mem_inf.mp ha0).1
  have hr : a * q' * a⁻¹ ∈ Q := conj_mem_Q hs.hyp haM hq'
  have hcom : za * (a * q' * a⁻¹)⁻¹ = (a * q' * a⁻¹)⁻¹ * za :=
    Z_central hs.hyp hzaZ (Q.inv_mem hr)
  have hzbc : a * zb * a⁻¹ = zb := H0_conj_Z ha0 hzbZ
  refine zetaRel_iff.mpr ⟨Z.mul_mem hzaZ hzbZ, a * q' * a⁻¹ * q, Q.mul_mem hr hq, ?_⟩
  calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    _ = a * (q' * x * q'⁻¹ * zb) * a⁻¹ := by rw [hB]
    _ = (a * q' * a⁻¹) * (a * x * a⁻¹) * (a * q'⁻¹ * a⁻¹) * (a * zb * a⁻¹) := by group
    _ = (a * q' * a⁻¹) * (q * x * q⁻¹ * za) * (a * q' * a⁻¹)⁻¹ * zb := by
        rw [hA, hzbc]
        group
    _ = (a * q' * a⁻¹) * q * x * q⁻¹ * (za * (a * q' * a⁻¹)⁻¹) * zb := by group
    _ = (a * q' * a⁻¹) * q * x * q⁻¹ * ((a * q' * a⁻¹)⁻¹ * za) * zb := by rw [hcom]
    _ = (a * q' * a⁻¹ * q) * x * (a * q' * a⁻¹ * q)⁻¹ * (za * zb) := by group

theorem zetaRel_inv (hs : Sit M Q Z X x) {a za : G} (ha0 : a ∈ H0 M Z)
    (h : ZetaRel Q Z x a za) : ZetaRel Q Z x a⁻¹ za⁻¹ := by
  obtain ⟨hzaZ, q, hq, hA⟩ := zetaRel_iff.mp h
  have haM : a ∈ M := (Subgroup.mem_inf.mp ha0).1
  have hq₂ : a⁻¹ * q⁻¹ * a ∈ Q := by
    have h1 := conj_mem_Q hs.hyp (M.inv_mem haM) (Q.inv_mem hq)
    rwa [inv_inv] at h1
  have hzq : za * q = q * za := Z_central hs.hyp hzaZ hq
  have hqz : q⁻¹ * za * q = za := by
    rw [mul_assoc, hzq]
    group
  have hza_a : za * a = a * za := by
    calc za * a = (a * za * a⁻¹) * a := by rw [H0_conj_Z ha0 hzaZ]
      _ = a * za := by group
  have hkey : a⁻¹ * q⁻¹ * a * x * (a⁻¹ * q⁻¹ * a)⁻¹ = a⁻¹ * x * a * za := by
    calc a⁻¹ * q⁻¹ * a * x * (a⁻¹ * q⁻¹ * a)⁻¹ = a⁻¹ * q⁻¹ * (a * x * a⁻¹) * q * a := by
          group
      _ = a⁻¹ * q⁻¹ * (q * x * q⁻¹ * za) * q * a := by rw [hA]
      _ = a⁻¹ * (x * (q⁻¹ * za * q)) * a := by group
      _ = a⁻¹ * (x * za) * a := by rw [hqz]
      _ = a⁻¹ * x * (za * a) := by group
      _ = a⁻¹ * x * (a * za) := by rw [hza_a]
      _ = a⁻¹ * x * a * za := by group
  refine zetaRel_iff.mpr ⟨Z.inv_mem hzaZ, a⁻¹ * q⁻¹ * a, hq₂, ?_⟩
  rw [inv_inv, hkey]
  group

theorem zetaRel_comm (hs : Sit M Q Z X x) {a b za zb : G} (ha0 : a ∈ H0 M Z) (hb0 : b ∈ H0 M Z)
    (ha : ZetaRel Q Z x a za) (hb : ZetaRel Q Z x b zb) : ZetaRel Q Z x ⁅a, b⁆ 1 := by
  obtain ⟨haZ, -⟩ := zetaRel_iff.mp ha
  obtain ⟨hbZ, -⟩ := zetaRel_iff.mp hb
  have hab : a * b ∈ H0 M Z := mul_mem ha0 hb0
  have h1 := zetaRel_mul hs ha0 hb0 ha hb
  have h2 := zetaRel_mul hs hab (inv_mem ha0) h1 (zetaRel_inv hs ha0 ha)
  have h3 := zetaRel_mul hs (mul_mem hab (inv_mem ha0)) (inv_mem hb0) h2 (zetaRel_inv hs hb0 hb)
  have hc : za * zb = zb * za := Z_central hs.hyp haZ (hs.hyp.Z_normal.1 hbZ)
  have e : za * zb * za⁻¹ * zb⁻¹ = 1 := by
    calc za * zb * za⁻¹ * zb⁻¹ = zb * za * za⁻¹ * zb⁻¹ := by rw [hc]
      _ = 1 := by group
  rw [e] at h3
  rw [commutatorElement_def]
  exact h3

theorem piD_conj_mem (hs : Sit M Q Z X x) {m : G} (hm0 : m ∈ H0 M Z) {q : G} (hq : q ∈ Q)
    (h : m * x * m⁻¹ = q * x * q⁻¹) {d : G} (hd : d ∈ Q ⊓ QB X) :
    ∃ d' ∈ Q ⊓ QB X, M₀.π d' = M₀.π (m * d * m⁻¹) := by
  obtain ⟨hdQ, hdB⟩ := Subgroup.mem_inf.mp hd
  have hmM : m ∈ M := (Subgroup.mem_inf.mp hm0).1
  have hmx : m * x = q * x * q⁻¹ * m := by
    rw [← h]
    group
  have hyx : q⁻¹ * m * x = x * (q⁻¹ * m) := by
    calc q⁻¹ * m * x = q⁻¹ * (m * x) := by group
      _ = q⁻¹ * (q * x * q⁻¹ * m) := by rw [hmx]
      _ = x * (q⁻¹ * m) := by group
  have hX : IsZConjugate Z X := hs.conj
  have hnorm : q⁻¹ * m ∈ Subgroup.normalizer (X : Set G) :=
    IsZConjugate.mem_normalizer_of_commute hs.hyp hX hs.ne_one hs.mem
      (show Commute (q⁻¹ * m) x from hyx)
  obtain ⟨d', hd'def⟩ : ∃ d', d' = q⁻¹ * m * d * (q⁻¹ * m)⁻¹ := ⟨_, rfl⟩
  have hd'B : d' ∈ QB X := by
    rw [hd'def]
    exact IsZConjugate.conj_mem_QB hs.hyp hX hnorm hdB
  have hmd : m * d * m⁻¹ = q * d' * q⁻¹ := by
    rw [hd'def]
    group
  have hd'Q : d' ∈ Q := by
    have h1 : m * d * m⁻¹ ∈ Q := conj_mem_Q hs.hyp hmM hdQ
    have h2 : d' = q⁻¹ * (m * d * m⁻¹) * q := by
      rw [hd'def]
      group
    rw [h2]
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem hq) h1) hq
  refine ⟨d', Subgroup.mem_inf.mpr ⟨hd'Q, hd'B⟩, ?_⟩
  rw [hmd, Tim79.QuadModel.pi_conj_self (M₀ := M₀) hq hd'Q]

theorem caseII_piD_le_R (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) (Tx : XAct M₀ x)
    (hII : CaseII Q Z x) {d : G} (hd : d ∈ Q ⊓ QB X) : M₀.π d ∈ Rs Tx := by
  apply perp_Cs hs Tx
  intro c hc
  obtain ⟨q, hq, rfl⟩ := M₀.π_surj c
  have hZ : ⁅q, x⁆ ∈ Z := (comm_mem_Z_iff hs Tx hq).mpr hc
  have hcomm : ⁅q, x⁆ = 1 := hII q hq hZ
  have hqc : q ∈ Q ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hq, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
  have hdq : d * q = q * d := (smith_1_13 hs).2.2.2.2 d hd q hqc
  have hdQ : d ∈ Q := (Subgroup.mem_inf.mp hd).1
  have hdq1 : ⁅d, q⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hdq
  have h := M₀.comm_eq d hdQ q hq
  rw [hdq1, hD.reg.one] at h
  exact h.symm

theorem commInv_piD (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) (Tx : XAct M₀ x)
    (hII : CaseII Q Z x) {a b : G} (ha0 : a ∈ H0 M Z) (hax : ⁅a, x⁆ ∈ Q) (hb0 : b ∈ H0 M Z)
    (hbx : ⁅b, x⁆ ∈ Q) {d : G} (hd : d ∈ Q ⊓ QB X) :
    ∃ d' ∈ Q ⊓ QB X, M₀.π d' = M₀.π (⁅a, b⁆ * d * ⁅a, b⁆⁻¹) := by
  obtain ⟨za, hza⟩ :=
    zetaRel_of_piComm hs Tx ha0 hax (caseII_piComm_mem_Rs hD hs Tx hII ha0 hax)
  obtain ⟨zb, hzb⟩ :=
    zetaRel_of_piComm hs Tx hb0 hbx (caseII_piComm_mem_Rs hD hs Tx hII hb0 hbx)
  have hcH : ⁅a, b⁆ ∈ H0 M Z := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha0 hb0) (inv_mem ha0)) (inv_mem hb0)
  obtain ⟨-, q, hq, h⟩ := zetaRel_iff.mp (zetaRel_comm hs ha0 hb0 hza hzb)
  rw [mul_one] at h
  exact piD_conj_mem hs hcH hq h hd

theorem piD_mem_Jx (hs : Sit M Q Z X x) (Tx : XAct M₀ x) (hI : CaseI Q Z x) {d : G}
    (hd : d ∈ Q ⊓ QB X) (hdR : M₀.π d ∈ Rs Tx) : d ∈ Jx Q X x := by
  have hdQ : d ∈ Q := (Subgroup.mem_inf.mp hd).1
  have hdB : d ∈ QB X := (Subgroup.mem_inf.mp hd).2
  obtain ⟨e, heQ, z, hzZ, hde⟩ := exists_comm_of_mem_Rs hs Tx hdQ hdR
  obtain ⟨q₂, hq₂Q, hq₂z⟩ := hI z hzZ
  unfold Jx
  refine Subgroup.mem_inf.mpr ⟨?_, hdB⟩
  rw [hde, ← hq₂z]
  exact mul_mem (Subgroup.commutator_mem_commutator heQ (Subgroup.mem_zpowers x))
    (Subgroup.commutator_mem_commutator hq₂Q (Subgroup.mem_zpowers x))

theorem caseI_D_bot (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) (Tx : XAct M₀ x)
    (hI : CaseI Q Z x) (hJ : Jx Q X x = ⊥) (hQf : ∀ r ∈ Rs Tx, M₀.Qf r = 0)
    (Ufam : Set G) (hU0 : ∀ u ∈ Ufam, u ∈ H0 M Z) (hUx : ∀ u ∈ Ufam, ⁅u, x⁆ ∈ Q)
    (hUC : ∀ u ∈ Ufam, ∀ w ∈ Q, M₀.π w ∈ Cs Tx → M₀.π (u * w * u⁻¹) - M₀.π w ∈ Rs Tx)
    (hUfix : ∀ e ∈ Cs Tx, (∀ u ∈ Ufam, ∀ w ∈ Q, M₀.π w = e → M₀.π (u * w * u⁻¹) = e) →
      e ∈ Rs Tx) :
    Q ⊓ QB X = ⊥ := by
  have hA : ∀ d' ∈ Q ⊓ QB X, M₀.π d' ∈ Rs Tx → d' = 1 := by
    intro d' hd' hR
    have h1 : d' ∈ Jx Q X x := piD_mem_Jx hs Tx hI hd' hR
    rw [hJ, Subgroup.mem_bot] at h1
    exact h1
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  have hdQ : d ∈ Q := (Subgroup.mem_inf.mp hd).1
  have hfix : ∀ u ∈ Ufam, M₀.π (u * d * u⁻¹) = M₀.π d := by
    intro u hu
    have hπu : M₀.π ⁅u, x⁆ ∈ Rs Tx :=
      caseI_piComm_mem_Rs hD hs Tx hQf (hU0 u hu) (hUx u hu) (hUC u hu)
    obtain ⟨z, hzeta⟩ := zetaRel_of_piComm hs Tx (hU0 u hu) (hUx u hu) hπu
    obtain ⟨hzZ, q, hq, hz⟩ := zetaRel_iff.mp hzeta
    obtain ⟨q₂, hq₂, hq₂z⟩ := hI z hzZ
    have hxz : x * z = z * x := x_mul_Z_comm hs hzZ
    have hqz : q * z * q⁻¹ = z := by
      rw [← Z_central hs.hyp hzZ hq]
      group
    have h1 : q₂ * x * q₂⁻¹ = x * z := by
      have e : q₂ * x * q₂⁻¹ = z * x := by
        rw [← hq₂z, commutatorElement_def]
        group
      rw [e, hxz]
    have hconj : u * x * u⁻¹ = (q * q₂) * x * (q * q₂)⁻¹ := by
      calc u * x * u⁻¹ = q * x * q⁻¹ * z := hz
        _ = q * x * q⁻¹ * (q * z * q⁻¹) := by rw [hqz]
        _ = q * (x * z) * q⁻¹ := by group
        _ = q * (q₂ * x * q₂⁻¹) * q⁻¹ := by rw [h1]
        _ = (q * q₂) * x * (q * q₂)⁻¹ := by group
    obtain ⟨d', hd'D, hd'π⟩ :=
      piD_conj_mem (M₀ := M₀) hs (hU0 u hu) (Q.mul_mem hq hq₂) hconj hd
    have hR1 : M₀.π (u * d * u⁻¹) - M₀.π d ∈ Rs Tx :=
      hUC u hu d hdQ (D_pi_mem_Cs hs Tx hd)
    have hd'R : M₀.π d' - M₀.π d ∈ Rs Tx := by
      rw [hd'π]
      exact hR1
    have hd'Q : d' ∈ Q := (Subgroup.mem_inf.mp hd'D).1
    have hsub : M₀.π (d' * d⁻¹) ∈ Rs Tx := by
      rw [M₀.π_mul d' hd'Q d⁻¹ (Q.inv_mem hdQ), Tim79.QuadModel.pi_inv M₀ hdQ,
        ← sub_eq_add_neg]
      exact hd'R
    have hdd : d' * d⁻¹ ∈ Q ⊓ QB X := mul_mem hd'D (inv_mem hd)
    have hdeq : d' = d := mul_inv_eq_one.mp (hA _ hdd hsub)
    rw [← hd'π, hdeq]
  have hRd : M₀.π d ∈ Rs Tx := by
    refine hUfix (M₀.π d) (D_pi_mem_Cs hs Tx hd) ?_
    intro u hu w hw hwd
    have hzQ : d⁻¹ * w ∈ Q := Q.mul_mem (Q.inv_mem hdQ) hw
    have hzZ : d⁻¹ * w ∈ Z := by
      rw [← M₀.π_ker _ hzQ, M₀.π_mul _ (Q.inv_mem hdQ) w hw, Tim79.QuadModel.pi_inv M₀ hdQ,
        hwd, neg_add_cancel]
    have hcen : u * (d⁻¹ * w) * u⁻¹ = d⁻¹ * w := H0_conj_Z (hU0 u hu) hzZ
    have hudQ : u * d * u⁻¹ ∈ Q :=
      conj_mem_Q hs.hyp (Subgroup.mem_inf.mp (hU0 u hu)).1 hdQ
    have e : u * w * u⁻¹ = (u * d * u⁻¹) * (d⁻¹ * w) := by
      calc u * w * u⁻¹ = (u * d * u⁻¹) * (u * (d⁻¹ * w) * u⁻¹) := by group
        _ = (u * d * u⁻¹) * (d⁻¹ * w) := by rw [hcen]
    rw [e, M₀.π_mul _ hudQ _ hzQ, (M₀.π_ker _ hzQ).mpr hzZ, add_zero]
    exact hfix u hu
  exact hA d hd hRd

end Lift2

end CFSG.RankThree.GF2n.Smith81.E3LCond
