module

public import CFSG.Quasithin.Vol2.Ch10SecBXi
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

section Generic

variable {T X P Q : Subgroup G}

theorem exists_mul_mem_normalizer (hP : IsSylowIn 3 P X) (hQP : P ≤ Subgroup.normalizer (Q : Set G))
    (hX : Q ⊔ P = X) (hTX : T ≤ Subgroup.normalizer (X : Set G)) {s : G} (hs : s ∈ T) :
    ∃ q ∈ Q, q * s ∈ Subgroup.normalizer (P : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP' := Ch1Sec3.isSylowIn_map_conj hP (hTX hs)
  obtain ⟨h, hhX, hh⟩ := Ch1Sec3.exists_conj_of_isSylowIn hP hP'
  have hh' : h ∈ ((Q ⊔ P : Subgroup G) : Set G) := by rw [hX]; exact hhX
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q P hQP] at hh'
  obtain ⟨q, hq, p, hp, rfl⟩ := Set.mem_mul.mp hh'
  have key : ∀ x : G, s⁻¹ * x * s ∈ P ↔ q⁻¹ * x * q ∈ P := by
    intro x
    have h1 : x ∈ P.map (MulAut.conj s).toMonoidHom ↔ s⁻¹ * x * s ∈ P := by
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [mul_assoc] using hz
      · intro hx
        exact ⟨s⁻¹ * x * s, hx, by simp [mul_assoc]⟩
    rw [← h1, hh x]
    constructor
    · intro hx
      have := P.mul_mem (P.mul_mem hp hx) (P.inv_mem hp)
      simpa [mul_assoc] using this
    · intro hx
      have := P.mul_mem (P.mul_mem (P.inv_mem hp) hx) hp
      simpa [mul_assoc] using this
  refine ⟨q⁻¹, Q.inv_mem hq, Subgroup.mem_normalizer_iff.mpr fun z => ?_⟩
  constructor
  · intro hz
    have := (key (s * z * s⁻¹)).mp (by simpa [mul_assoc] using hz)
    simpa [mul_assoc] using this
  · intro hz
    have := (key (s * z * s⁻¹)).mpr (by simpa [mul_assoc] using hz)
    simpa [mul_assoc] using this

omit [Finite G] in
theorem conj_mul_inv_mem {X Q : Subgroup G} (hQX : Q ≤ X) (hXQ : ⁅X, X⁆ ≤ Q) {r z : G}
    (hr : r ∈ Q) (hz : z ∈ X) : r * z * r⁻¹ * z⁻¹ ∈ Q :=
  hXQ (Subgroup.commutator_mem_commutator (hQX hr) hz)

theorem comm_of_autCyclic (hP : IsSylowIn 3 P X) (hQX : Q ≤ X)
    (hQn : X ≤ Subgroup.normalizer (Q : Set G)) (hXQ : ⁅X, X⁆ ≤ Q) (hQT : Q ≤ T)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hX : Q ⊔ P = X) (hcyc : EmptyFaithfulMultiple.AutCyclic T P) {a b y : G} (ha : a ∈ T)
    (hb : b ∈ T) (hy : y ∈ X) :
    a * b * y * (a * b)⁻¹ * (b * a * y * (b * a)⁻¹)⁻¹ ∈ Q := by
  have hQP : P ≤ Subgroup.normalizer (Q : Set G) := hP.le.trans hQn
  obtain ⟨q1, hq1, hn1⟩ := exists_mul_mem_normalizer hP hQP hX hTX ha
  obtain ⟨q2, hq2, hn2⟩ := exists_mul_mem_normalizer hP hQP hX hTX hb
  obtain ⟨c, -, hc⟩ := hcyc
  obtain ⟨k1, hk1⟩ := hc _ ⟨T.mul_mem (hQT hq1) ha, hn1⟩
  obtain ⟨k2, hk2⟩ := hc _ ⟨T.mul_mem (hQT hq2) hb, hn2⟩
  have hcomm : ∀ x ∈ P, q1 * a * (q2 * b) * x * (q1 * a * (q2 * b))⁻¹ =
      q2 * b * (q1 * a) * x * (q2 * b * (q1 * a))⁻¹ := by
    intro x hx
    have hx2 : q2 * b * x * (q2 * b)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hn2 x).mp hx
    have hx1 : q1 * a * x * (q1 * a)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hn1 x).mp hx
    calc q1 * a * (q2 * b) * x * (q1 * a * (q2 * b))⁻¹
        = q1 * a * (q2 * b * x * (q2 * b)⁻¹) * (q1 * a)⁻¹ := by group
      _ = c ^ k1 * (c ^ k2 * x * (c ^ k2)⁻¹) * (c ^ k1)⁻¹ := by rw [hk1 _ hx2, hk2 x hx]
      _ = c ^ k2 * (c ^ k1 * x * (c ^ k1)⁻¹) * (c ^ k2)⁻¹ := by group
      _ = q2 * b * (q1 * a * x * (q1 * a)⁻¹) * (q2 * b)⁻¹ := by rw [hk2 _ hx1, hk1 x hx]
      _ = q2 * b * (q1 * a) * x * (q2 * b * (q1 * a))⁻¹ := by group
  have hyQP : y ∈ ((Q ⊔ P : Subgroup G) : Set G) := by rw [hX]; exact hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q P hQP] at hyQP
  obtain ⟨q0, hq0, p0, hp0, rfl⟩ := Set.mem_mul.mp hyQP
  have hconjQ : ∀ g ∈ T, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hTQ hg) q).mp hq
  have hN1 : q1 * a * (q2 * b) ∈ T := T.mul_mem (T.mul_mem (hQT hq1) ha) (T.mul_mem (hQT hq2) hb)
  have hN2 : q2 * b * (q1 * a) ∈ T := T.mul_mem (T.mul_mem (hQT hq2) hb) (T.mul_mem (hQT hq1) ha)
  set N1 := q1 * a * (q2 * b) with hN1def
  set N2 := q2 * b * (q1 * a) with hN2def
  set m1 := N1 * (q0 * p0) * N1⁻¹ with hm1def
  set m2 := N2 * (q0 * p0) * N2⁻¹ with hm2def
  have hm12 : m1 * m2⁻¹ ∈ Q := by
    have e : m1 * m2⁻¹ = (N1 * q0 * N1⁻¹) * (N1 * p0 * N1⁻¹) * (N2 * p0 * N2⁻¹)⁻¹ *
        (N2 * q0 * N2⁻¹)⁻¹ := by rw [hm1def, hm2def]; group
    rw [e, hcomm p0 hp0, mul_assoc (N1 * q0 * N1⁻¹), mul_inv_cancel, mul_one]
    exact Q.mul_mem (hconjQ _ hN1 _ hq0) (Q.inv_mem (hconjQ _ hN2 _ hq0))
  have hm1X : m1 ∈ X := (Subgroup.mem_normalizer_iff.mp (hTX hN1) _).mp hy
  have hm2X : m2 ∈ X := (Subgroup.mem_normalizer_iff.mp (hTX hN2) _).mp hy
  set r1 := q1 * (a * q2 * a⁻¹) with hr1def
  set r2 := q2 * (b * q1 * b⁻¹) with hr2def
  have hr1 : r1 ∈ Q := Q.mul_mem hq1 (hconjQ _ ha _ hq2)
  have hr2 : r2 ∈ Q := Q.mul_mem hq2 (hconjQ _ hb _ hq1)
  have e : a * b * (q0 * p0) * (a * b)⁻¹ * (b * a * (q0 * p0) * (b * a)⁻¹)⁻¹ =
      (r1⁻¹ * m1 * r1⁻¹⁻¹ * m1⁻¹) * (m1 * m2⁻¹) * (m2 * r2⁻¹ * m2⁻¹ * r2⁻¹⁻¹) := by
    rw [hr1def, hr2def, hm1def, hm2def, hN1def, hN2def]; group
  rw [e]
  refine Q.mul_mem (Q.mul_mem (conj_mul_inv_mem hQX hXQ (Q.inv_mem hr1) hm1X) hm12) ?_
  have h1 : m2 * r2⁻¹ * m2⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQn hm2X) _).mp
    (Q.inv_mem hr2)
  exact Q.mul_mem h1 (Q.inv_mem (Q.inv_mem hr2))

end Generic

variable {T L I : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ}
  {A K E : Subgroup L32.Γ}

theorem mul_self_mem_T1 (h : MaxCtx T L I t Ψ c) {s : G} (hs : s ∈ T) : s * s ∈ T1 T L := by
  refine ⟨T.mul_mem hs hs, ?_⟩
  by_cases hsN : s ∈ Subgroup.normalizer (L : Set G)
  · exact Subgroup.mul_mem _ hsN hsN
  · exact SecA.mul_self_mem_normalizer h.h37 h.h38 h.hyp hs hsN

theorem pow_four_mem (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {s x : G} (hs : s ∈ T)
    (hx : x ∈ XOf T L Ψ A) :
    s ^ 4 * x * (s ^ 4)⁻¹ * x⁻¹ ∈ pCoreOf 2 (XOf T L Ψ A) := by
  have hXL0 := XOf_le_fsuL0 h hD
  have hTX : T ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) :=
    le_sup_right.trans (le_normalizer_oTwoUpper _)
  have hs2 := mul_self_mem_T1 h hs
  obtain ⟨u, v, hu, hv, huv⟩ := h.hC.T1act _ hs2
  have hw : s * s * x * (s * s)⁻¹ ∈ XOf T L Ψ A :=
    (Subgroup.mem_normalizer_iff.mp (hTX hs2.1) x).mp hx
  have hw' : s * s * (s * s * x * (s * s)⁻¹) * (s * s)⁻¹ ∈ XOf T L Ψ A :=
    (Subgroup.mem_normalizer_iff.mp (hTX hs2.1) _).mp hw
  have e4 : s ^ 4 * x * (s ^ 4)⁻¹ = s * s * (s * s * x * (s * s)⁻¹) * (s * s)⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul]; group
  rw [e4, pCoreOf_XOf h hD]
  have hm := (XOf T L Ψ A).mul_mem hw' ((XOf T L Ψ A).inv_mem hx)
  refine ⟨hm, mem_preIn.mpr ⟨hXL0 hm, ?_⟩⟩
  have hxK := mem_prod_of_mem_XOf h hD hx
  have e1 : Ψ ⟨s * s * (s * s * x * (s * s)⁻¹) * (s * s)⁻¹, hXL0 hw'⟩ =
      (u * (Ψ ⟨s * s * x * (s * s)⁻¹, hXL0 hw⟩).1 * u⁻¹,
        v * (Ψ ⟨s * s * x * (s * s)⁻¹, hXL0 hw⟩).2 * v⁻¹) := huv ⟨_, hXL0 hw⟩ (hXL0 hw')
  have e2 : Ψ ⟨s * s * x * (s * s)⁻¹, hXL0 hw⟩ =
      (u * (Ψ ⟨x, hXL0 hx⟩).1 * u⁻¹, v * (Ψ ⟨x, hXL0 hx⟩).2 * v⁻¹) :=
    huv ⟨x, hXL0 hx⟩ (hXL0 hw)
  rw [show (⟨s * s * (s * s * x * (s * s)⁻¹) * (s * s)⁻¹ * x⁻¹, hXL0 hm⟩ : ↥(fsuL0 T L)) =
    ⟨_, hXL0 hw'⟩ * ⟨x, hXL0 hx⟩⁻¹ from rfl, map_mul, map_inv, e1, e2, Subgroup.mem_prod]
  refine ⟨?_, ?_⟩
  · have := hD.sq u hu _ hxK.1
    simp only [Prod.fst_mul, Prod.fst_inv]
    convert this using 1
    group
  · have := hD.sq v hv _ hxK.2
    simp only [Prod.snd_mul, Prod.snd_inv]
    convert this using 1
    group

theorem exists_noncomm (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    ∃ a ∈ T, ∃ b ∈ T, ∃ y ∈ XOf T L Ψ A,
      a * b * y * (a * b)⁻¹ * (b * a * y * (b * a)⁻¹)⁻¹ ∉ pCoreOf 2 (XOf T L Ψ A) := by
  have hXL0 := XOf_le_fsuL0 h hD
  have hC := h.hC
  obtain ⟨d, hdU, k, hkK, hdk⟩ := hD.noncomm
  have hd1 : ((d, 1) : L32.Γ × L32.Γ) ∈ L32.U3.prod L32.U3 := ⟨hdU, L32.U3.one_mem⟩
  rw [← hC.T0] at hd1
  obtain ⟨⟨t0, ht0L0⟩, ht0, hΨt0⟩ := hd1
  have ht0T : t0 ∈ T := (Subgroup.mem_subgroupOf.mp ht0).1
  have hk1 : ((k, 1) : L32.Γ × L32.Γ) ∈ imgIn Ψ (XOf T L Ψ A) := by
    rw [imgIn_XOf h hD]; exact ⟨hkK, K.one_mem⟩
  obtain ⟨y, hyL0, hyX, hΨy⟩ := mem_imgIn.mp hk1
  refine ⟨t⁻¹, T.inv_mem h.ht, t0, ht0T, y, hyX, fun hmem => ?_⟩
  rw [pCoreOf_XOf h hD] at hmem
  obtain ⟨-, hmem⟩ := hmem
  obtain ⟨hzL0, hz⟩ := mem_preIn.mp hmem
  have hw1 : t0 * y * t0⁻¹ ∈ fsuL0 T L :=
    (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem ht0L0 hyL0) ((fsuL0 T L).inv_mem ht0L0)
  have hu1 : t⁻¹ * (t0 * y * t0⁻¹) * t ∈ fsuL0 T L := by
    have := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (SecA.le_fsuM T L h.ht)) _).mp hw1
    simpa using this
  have hw2 : t⁻¹ * y * t ∈ fsuL0 T L := by
    have := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (SecA.le_fsuM T L h.ht)) _).mp hyL0
    simpa using this
  have hu2 : t0 * (t⁻¹ * y * t) * t0⁻¹ ∈ fsuL0 T L :=
    (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem ht0L0 hw2) ((fsuL0 T L).inv_mem ht0L0)
  have eu1 : Ψ ⟨_, hu1⟩ = (c * (Ψ ⟨_, hw1⟩).2 * c⁻¹, (Ψ ⟨_, hw1⟩).1) := hC.swap ⟨_, hw1⟩ hu1
  have ew1 : Ψ ⟨_, hw1⟩ = (d, 1) * (k, 1) * (d, 1)⁻¹ := by
    rw [show (⟨t0 * y * t0⁻¹, hw1⟩ : ↥(fsuL0 T L)) = ⟨t0, ht0L0⟩ * ⟨y, hyL0⟩ * ⟨t0, ht0L0⟩⁻¹
      from rfl, map_mul, map_mul, map_inv, hΨt0, hΨy]
  have ew2 : Ψ ⟨_, hw2⟩ = (c * (Ψ ⟨y, hyL0⟩).2 * c⁻¹, (Ψ ⟨y, hyL0⟩).1) := hC.swap ⟨y, hyL0⟩ hw2
  have eu2 : Ψ ⟨_, hu2⟩ = (d, 1) * Ψ ⟨_, hw2⟩ * (d, 1)⁻¹ := by
    rw [show (⟨t0 * (t⁻¹ * y * t) * t0⁻¹, hu2⟩ : ↥(fsuL0 T L)) =
      ⟨t0, ht0L0⟩ * ⟨_, hw2⟩ * ⟨t0, ht0L0⟩⁻¹ from rfl, map_mul, map_mul, map_inv, hΨt0]
  have ez : (⟨_, hzL0⟩ : ↥(fsuL0 T L)) = ⟨_, hu1⟩ * ⟨_, hu2⟩⁻¹ := Subtype.ext (by
    show t⁻¹ * t0 * y * (t⁻¹ * t0)⁻¹ * (t0 * t⁻¹ * y * (t0 * t⁻¹)⁻¹)⁻¹ =
      t⁻¹ * (t0 * y * t0⁻¹) * t * (t0 * (t⁻¹ * y * t) * t0⁻¹)⁻¹
    group)
  rw [ez, map_mul, map_inv, eu1, eu2, ew1, ew2, hΨy] at hz
  apply hdk
  have := hz.2
  simpa [mul_assoc] using this

theorem not_autCyclic (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {P : Subgroup G}
    (hP : IsSylowIn 3 P (XOf T L Ψ A)) : ¬ EmptyFaithfulMultiple.AutCyclic T P := by
  intro hcyc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXi := isXi_XOf h hD
  have h3 : 3 ∣ Nat.card (XOf T L Ψ A) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, relIndex_XOf h hD]
    exact Dvd.dvd.mul_left (by norm_num) _
  have hTX : T ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) := hXi.2.1
  have hTQ : T ≤ Subgroup.normalizer (pCoreOf 2 (XOf T L Ψ A) : Set G) :=
    hTX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hQT : pCoreOf 2 (XOf T L Ψ A) ≤ T := by
    refine (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left) (sup_le
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) hTQ)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans ?_
    exact SecA.pCoreOf_le_of_sylow h.hyp.fsu.sylow le_sup_right
  obtain ⟨a, ha, b, hb, y, hy, hne⟩ := exists_noncomm h hD
  exact hne (comm_of_autCyclic hP (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) (commutator_le_pCoreOf h hD) hQT hTX hTQ
    (hXi.pCoreOf_sup_eq (by norm_num) h3 hP) hcyc ha hb hy)

end CFSG.Quasithin.Vol2.Ch10.SecB
