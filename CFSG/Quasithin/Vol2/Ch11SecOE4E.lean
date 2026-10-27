module

public import CFSG.Quasithin.Vol2.Ch11SecOE4D
public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Setup

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE4

open Subgroup CFSG.Quasithin
open CFSG.Open (pCoreOf quasithinIsSylowTwo IsSubnormal)
open CFSG.Quasithin.H13 (reducedAggregate)
open CFSG.LieType.BorelTits (le_pCoreOf_of_le_normalizer le_normalizer_pCoreOf pCoreOf_isPGroup
  normalizer_le_normalizer_pCoreOf pCoreOf_le)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev vIP (T D : Subgroup G) (p : ℕ) : Subgroup G := EmptyFaithfulMultiple.L3213.vOf T (iP D p)

section Basic

variable {T D : Subgroup G} {p : ℕ}

theorem sup_le_normalizer_iP (hTD : T ≤ normalizer (D : Set G)) :
    iP D p ⊔ T ≤ normalizer (iP D p : Set G) :=
  sup_le le_normalizer (hTD.trans (normalizer_le_normalizer_iP D p))

theorem vOf_iP_le (hTD : T ≤ normalizer (D : Set G)) : vIP T D p ≤ iP D p := by
  show ⁅omegaOneCenterOf (pCoreOf 2 (iP D p ⊔ T)), iP D p⁆ ≤ iP D p
  rw [commutator_comm]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((omegaOneCenterOf_le _).trans
    ((pCoreOf_le 2 _).trans (sup_le_normalizer_iP hTD)))

theorem sup_le_normalizer_vOf_iP (hTD : T ≤ normalizer (D : Set G)) :
    iP D p ⊔ T ≤ normalizer (vIP T D p : Set G) := fun _ hg =>
  show _ ∈ normalizer
    ((⁅omegaOneCenterOf (pCoreOf 2 (iP D p ⊔ T)), iP D p⁆ : Subgroup G) : Set G) from
  A4.mem_normalizer_commutator
    (EmptyFaithfulMultiple.L3213.sup_le_normalizer_omegaOneCenterOf T (iP D p) hg)
    (sup_le_normalizer_iP hTD hg)

theorem pCoreOf_iP_le_pCoreOf_sup (hTD : T ≤ normalizer (D : Set G)) :
    pCoreOf 2 (iP D p) ≤ pCoreOf 2 (iP D p ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
    ((sup_le_normalizer_iP hTD).trans (normalizer_le_normalizer_pCoreOf 2 _))
    (pCoreOf_isPGroup 2 _)

theorem pCoreOf_iP_le_centralizer_vOf (hTD : T ≤ normalizer (D : Set G)) :
    pCoreOf 2 (iP D p) ≤ centralizer (vIP T D p : Set G) :=
  (pCoreOf_iP_le_pCoreOf_sup hTD).trans
    (EmptyFaithfulMultiple.L3213.pCoreOf_sup_le_centralizer_vOf T (iP D p))

theorem inf_sectionCentralizer_le (hT : quasithinIsSylowTwo T) {X : Subgroup G}
    (hTX : T ≤ normalizer (X : Set G)) :
    T ⊓ sectionCentralizer X (pCoreOf 2 X) ≤ pCoreOf 2 (X ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₀ := T ⊓ sectionCentralizer X (pCoreOf 2 X) with hT₀
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_le_of_quasithinIsSylowTwo hT hTX
  have hQT₀ : pCoreOf 2 X ≤ T₀ :=
    le_inf hQT (EmptyFaithfulMultiple.L3213.pCoreOf_le_sectionCentralizer X)
  have hXN : X ≤ normalizer (T₀ : Set G) := by
    intro x hx
    refine mem_normalizer_fintype fun s hs => ?_
    have hsc := hs.2.2.2
    have h1 : s * x⁻¹ * s⁻¹ * x⁻¹⁻¹ ∈ pCoreOf 2 X := hsc x⁻¹ (X.inv_mem hx)
    have h2 : x * (s * x⁻¹ * s⁻¹ * x⁻¹⁻¹) * x⁻¹ ∈ pCoreOf 2 X :=
      (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 X hx) _).mp h1
    have e : x * s * x⁻¹ = (x * (s * x⁻¹ * s⁻¹ * x⁻¹⁻¹) * x⁻¹) * s := by group
    rw [e]
    exact T₀.mul_mem (hQT₀ h2) hs
  have hTN : T ≤ normalizer (T₀ : Set G) := by
    intro t ht
    refine mem_normalizer_fintype fun s hs => ?_
    exact ⟨T.mul_mem (T.mul_mem ht hs.1) (T.inv_mem ht),
      EmptyFaithfulMultiple.L3213.conj_mem_sectionCentralizer (hTX ht)
        (normalizer_le_normalizer_pCoreOf 2 X (hTX ht)) hs.2⟩
  exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) (sup_le hXN hTN)
    (hT.1.to_le inf_le_left)

end Basic

structure HomData (T D : Subgroup G) (p e : ℕ) : Prop where
  sylow : quasithinIsSylowTwo T
  le_normalizer : T ≤ normalizer (D : Set G)
  perfect : ⁅D, D⁆ = D
  prime : p.Prime
  five_le : 5 ≤ p
  one_le : 1 ≤ e
  iso : Nonempty (↥(CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)) ≃*
    (Multiplicative (ZMod (p ^ e)) × Multiplicative (ZMod (p ^ e))))
  canonical : H13.NQCore.SNCanonical T D (H13.nqPrimeResidualX D p) p
  mapsTo : ∀ x ∈ iP D p, ∀ hxD : x ∈ D,
    QuotientGroup.mk' (CFSG.pCore 2 ↥D) ⟨x, hxD⟩ ∈ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)
  charTwo : QuasithinUnique.CharTwo (D ⊔ T)

section Module

variable {T D : Subgroup G} {p e : ℕ}

omit [Finite G] in
theorem HomData.prime_ne_two (h : HomData T D p e) : p ≠ 2 := by
  have := h.five_le
  omega

theorem HomData.pow_mem_pCoreOf (h : HomData T D p e) {x : G} (hx : x ∈ iP D p) :
    x ^ p ^ e ∈ pCoreOf 2 (iP D p) := by
  obtain ⟨φ⟩ := h.iso
  have hxD := iP_le D p hx
  have h1 : (⟨_, h.mapsTo x hx hxD⟩ : ↥(CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D))) ^ p ^ e = 1 := by
    apply φ.injective
    rw [map_pow, map_one]
    exact H13.NQBlock.homocyclic_pow_prime_pow_eq_one (MulEquiv.refl _) _
  refine (mk_eq_one_iff (pow_mem hx _) (pow_mem hxD _)).mp ?_
  have h2 := congrArg Subtype.val h1
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
  rw [← h2, ← map_pow]
  rfl

theorem vIP_ne_bot (h : HomData T D p e)
    (hI : ¬ iP D p ≤ centralizer (reducedAggregate (D ⊔ T) : Set G)) : vIP T D p ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIne : iP D p ≠ ⊥ := fun h0 => hI (by rw [h0]; exact bot_le)
  have hID : iP D p ≤ D ⊔ T := (iP_le D p).trans le_sup_left
  have hDTI : D ⊔ T ≤ normalizer (iP D p : Set G) :=
    sup_le (le_normalizer.trans (normalizer_le_normalizer_iP D p))
      (h.le_normalizer.trans (normalizer_le_normalizer_iP D p))
  have hsubDT : IsSubnormal (iP D p) (D ⊔ T) :=
    A3.subnormal_of_normal hID ((normal_subgroupOf_iff_le_normalizer hID).mpr hDTI)
  have hsubIT : IsSubnormal (iP D p) (iP D p ⊔ T) :=
    A3.subnormal_of_normal le_sup_left ((normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le_normalizer_iP h.le_normalizer))
  have hXc : IsXClass (iP D p) :=
    ⟨hIne, iP_eq_oTwoUpper D h.prime h.prime_ne_two, A4.charTwo_of_subnormal hsubDT h.charTwo⟩
  have h1 : ⁅omegaOneCenterOf (pCoreOf 2 (D ⊔ T)), iP D p⁆ ≠ ⊥ := by
    intro h0
    apply hI
    rw [commutator_eq_bot_iff_le_centralizer] at h0
    exact (le_centralizer_iff.mp h0).trans
      (centralizer_le (H13.NQBlock.reducedAggregate_le_omegaOneCenterOf (D ⊔ T)))
  exact (a4_9 hXc hsubIT).mpr ((a4_9 hXc hsubDT).mp h1)

theorem inf_centralizer_vIP_pow (h : HomData T D p e)
    (hI : ¬ iP D p ≤ centralizer (reducedAggregate (D ⊔ T) : Set G)) :
    ∀ c ∈ iP D p ⊓ centralizer (vIP T D p : Set G), ∀ hcD : c ∈ D,
      ∃ w ∈ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D),
        QuotientGroup.mk' (CFSG.pCore 2 ↥D) ⟨c, hcD⟩ = w ^ p := by
  obtain ⟨φ⟩ := h.iso
  set V := vIP T D p with hV
  have hTV : T ≤ normalizer (V : Set G) :=
    le_sup_right.trans (sup_le_normalizer_vOf_iP h.le_normalizer)
  have hTI : T ≤ normalizer (iP D p : Set G) :=
    h.le_normalizer.trans (normalizer_le_normalizer_iP D p)
  have hTC : T ≤ normalizer ((iP D p ⊓ centralizer (V : Set G) : Subgroup G) : Set G) :=
    OE1.le_normalizer_inf hTI (hTV.trans (OE1.normalizer_le_normalizer_centralizer V))
  have hOC : pCoreOf 2 (iP D p) ≤ iP D p ⊓ centralizer (V : Set G) :=
    le_inf (pCoreOf_le 2 _) (pCoreOf_iP_le_centralizer_vOf h.le_normalizer)
  rcases le_pow_or_le_of_invariant h.sylow h.le_normalizer h.perfect h.prime h.five_le h.one_le φ
    h.canonical h.mapsTo inf_le_left hTC hOC with h1 | h1
  · exact h1
  exfalso
  apply vIP_ne_bot h hI
  rw [eq_bot_iff]
  show ⁅omegaOneCenterOf (pCoreOf 2 (iP D p ⊔ T)), iP D p⁆ ≤ ⊥
  rw [commutator_le]
  intro u hu x hx
  rw [mem_bot]
  set c := x * u * x⁻¹ * u⁻¹ with hc
  have hcV : c ∈ V := by
    have := commutator_mem_commutator hx hu
    rwa [commutator_comm, commutatorElement_def] at this
  have hxc : x * c * x⁻¹ = c := by
    rw [← mem_centralizer_iff.mp (h1 hx).2 c hcV, mul_inv_cancel_right]
  have hxu : x * u * x⁻¹ = c * u := by rw [hc]; group
  have hxpu : x ^ p ^ e * u * (x ^ p ^ e)⁻¹ = u := by
    rw [mem_centralizer_of_mem_omegaOneCenterOf hu
      (pCoreOf_iP_le_pCoreOf_sup h.le_normalizer (h.pow_mem_pCoreOf hx)), mul_inv_cancel_right]
  have hc2 : c ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenterOf
    (EmptyFaithfulMultiple.L3213.vOf_le_omegaOneCenterOf T (iP D p) hcV)
  have hcop : Nat.Coprime (p ^ e) 2 := Nat.Coprime.pow_left e
    ((Nat.coprime_primes h.prime Nat.prime_two).mpr h.prime_ne_two)
  have hc1 : c = 1 := EmptyFaithfulMultiple.L3213.eq_one_of_conj_coprime hcop hxpu hxu hxc hc2
  rw [commutatorElement_def]
  have : x * u * x⁻¹ = u := by rw [hxu, hc1, one_mul]
  calc u * x * u⁻¹ * x⁻¹ = u * (x * u * x⁻¹)⁻¹ := by group
    _ = 1 := by rw [this, mul_inv_cancel]

theorem mem_pCoreOf_sup_of_commutator_mem (h : HomData T D p e)
    (hI : ¬ iP D p ≤ centralizer (reducedAggregate (D ⊔ T) : Set G)) {t : G} (ht : t ∈ T)
    (hc : ∀ x ∈ iP D p, t * x * t⁻¹ * x⁻¹ ∈ centralizer (vIP T D p : Set G)) :
    t ∈ pCoreOf 2 (iP D p ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := h.iso
  have hTI : T ≤ normalizer (iP D p : Set G) :=
    h.le_normalizer.trans (normalizer_le_normalizer_iP D p)
  have hb := commutator_mem_pCoreOf_of_pow h.sylow h.le_normalizer h.prime h.prime_ne_two φ
    h.mapsTo ht fun x hx hcD => inf_centralizer_vIP_pow h hI _
      ⟨(iP D p).mul_mem ((mem_normalizer_iff.mp (hTI ht) x).mp hx) ((iP D p).inv_mem hx),
        hc x hx⟩ hcD
  exact inf_sectionCentralizer_le h.sylow hTI
    ⟨ht, hTI ht, normalizer_le_normalizer_pCoreOf 2 _ (hTI ht), hb⟩

theorem pCoreOf_autOn_vIP_eq_bot (h : HomData T D p e)
    (hI : ¬ iP D p ≤ centralizer (reducedAggregate (D ⊔ T) : Set G)) :
    pCoreOf 2 (autOn (iP D p ⊔ T) (vIP T D p)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨h.prime⟩
  have hp2 := h.prime_ne_two
  set X := iP D p with hXdef
  set V := vIP T D p with hVdef
  set N := normalizer (V : Set G) with hN
  have hTX : T ≤ normalizer (X : Set G) := h.le_normalizer.trans (normalizer_le_normalizer_iP D p)
  have hXTV : X ⊔ T ≤ N := sup_le_normalizer_vOf_iP h.le_normalizer
  have hXVN : X ≤ N := le_sup_left.trans hXTV
  have hTVN : T ≤ N := le_sup_right.trans hXTV
  set Xb := autOn (X ⊔ T) V with hXb
  set Xs := autOn X V with hXs
  set Ts := autOn T V with hTs
  set Q := pCoreOf 2 Xb with hQ
  have hQXb : Q ≤ Xb := pCoreOf_le 2 Xb
  have hXbQ : Xb ≤ normalizer (Q : Set (MulAut V)) := le_normalizer_pCoreOf 2 Xb
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 Xb
  have hconj : ∀ g k : N, conjAct V g * conjAct V k * (conjAct V g)⁻¹ =
      conjAct V (g * k * g⁻¹) := fun g k => by simp
  have hXsp : ∀ y ∈ Xs, y ^ p ^ e = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    refine A4.conjAct_eq_one_iff.mpr ?_
    have hxp := pCoreOf_iP_le_centralizer_vOf h.le_normalizer
      (h.pow_mem_pCoreOf (mem_subgroupOf.mp hx))
    simpa using hxp
  have hXsP : IsPGroup p Xs := fun y => ⟨e, Subtype.ext (by simpa using hXsp y y.2)⟩
  have hXbN : Xb ≤ normalizer (Xs : Set (MulAut V)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine mem_normalizer_fintype fun a ha => ?_
    obtain ⟨x, hx, rfl⟩ := ha
    rw [hconj]
    refine ⟨g * x * g⁻¹, mem_subgroupOf.mpr ?_, rfl⟩
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (sup_le_normalizer_iP h.le_normalizer
      (mem_subgroupOf.mp hg)) x).mp (mem_subgroupOf.mp hx)
  have hTs2 : IsPGroup 2 Ts := by
    rintro ⟨_, t, ht, rfl⟩
    obtain ⟨k, hk⟩ := h.sylow.1 ⟨(t : G), mem_subgroupOf.mp ht⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : t ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    simp [← map_pow, hk']
  have hTsXb : Ts ≤ Xb := A4.autOn_mono le_sup_right
  have hXsXb : Xs ≤ Xb := A4.autOn_mono le_sup_left
  have hQTs : IsPGroup 2 (Q ⊔ Ts : Subgroup (MulAut V)) :=
    IsPGroup.to_sup_of_normal_left' hQ2 hTs2 (hTsXb.trans hXbQ)
  have hQXs : Q ⊓ Xs = ⊥ := (IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) Q Xs hQ2 hXsP).eq_bot
  rw [eq_bot_iff]
  intro q hq
  rw [mem_bot]
  obtain ⟨g, hg, rfl⟩ := hQXb hq
  have hg' : (g : G) ∈ ((X ⊔ T : Subgroup G) : Set G) := mem_subgroupOf.mp hg
  rw [coe_mul_of_right_le_normalizer_left X T hTX] at hg'
  obtain ⟨x, hx, t, ht, hgxt⟩ := hg'
  have hgxt' : g = ⟨x, hXVN hx⟩ * ⟨t, hTVN ht⟩ := Subtype.ext hgxt.symm
  set xh := conjAct V ⟨x, hXVN hx⟩ with hxh
  set th := conjAct V ⟨t, hTVN ht⟩ with hth
  have hqe : conjAct V g = xh * th := by rw [hgxt', map_mul]
  have hxhXs : xh ∈ Xs := ⟨⟨x, hXVN hx⟩, mem_subgroupOf.mpr hx, rfl⟩
  have hxhQ : xh ∈ Q ⊔ Ts := by
    have e' : xh = conjAct V g * th⁻¹ := by rw [hqe]; group
    rw [e']
    exact mul_mem (mem_sup_left hq) (mem_sup_right
      (inv_mem ⟨⟨t, hTVN ht⟩, mem_subgroupOf.mpr ht, rfl⟩))
  obtain ⟨k, hk⟩ := hQTs ⟨xh, hxhQ⟩
  have hk' : xh ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) (p ^ e) :=
    Nat.Coprime.pow k e ((Nat.coprime_primes Nat.prime_two h.prime).mpr (Ne.symm hp2))
  have hxh1 : xh = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one (hXsp xh hxhXs)))
  have hqt : conjAct V g = th := by rw [hqe, hxh1, one_mul]
  have hcent : ∀ y ∈ Xs, th * y * th⁻¹ * y⁻¹ = 1 := by
    intro y hy
    have h1 : th * y * th⁻¹ * y⁻¹ ∈ Q := by
      have hthQ : th ∈ Q := hqt ▸ hq
      have hyQ : y * th⁻¹ * y⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp (hXbQ (hXsXb hy)) th⁻¹).mp (Q.inv_mem hthQ)
      have e' : th * y * th⁻¹ * y⁻¹ = th * (y * th⁻¹ * y⁻¹) := by group
      rw [e']
      exact Q.mul_mem hthQ hyQ
    have h2 : th * y * th⁻¹ * y⁻¹ ∈ Xs := by
      have hthy : th * y * th⁻¹ ∈ Xs :=
        (mem_normalizer_iff.mp (hXbN (hqt ▸ hQXb hq)) y).mp hy
      exact Xs.mul_mem hthy (Xs.inv_mem hy)
    have h3 : th * y * th⁻¹ * y⁻¹ ∈ Q ⊓ Xs := ⟨h1, h2⟩
    rwa [hQXs, mem_bot] at h3
  have htR : t ∈ pCoreOf 2 (X ⊔ T) := by
    refine mem_pCoreOf_sup_of_commutator_mem h hI ht fun x' hx' => ?_
    have h1 := hcent (conjAct V ⟨x', hXVN hx'⟩) ⟨⟨x', hXVN hx'⟩, mem_subgroupOf.mpr hx', rfl⟩
    rw [hth, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul] at h1
    have h2 := A4.conjAct_eq_one_iff.mp h1
    simpa using h2
  rw [hqt, hth]
  exact A4.conjAct_eq_one_iff.mpr
    (EmptyFaithfulMultiple.L3213.pCoreOf_sup_le_centralizer_vOf T X htR)

theorem isTwoReducedIn_vIP (h : HomData T D p e)
    (hI : ¬ iP D p ≤ centralizer (reducedAggregate (D ⊔ T) : Set G)) :
    IsTwoReducedIn (iP D p ⊔ T) (vIP T D p) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨(vOf_iP_le h.le_normalizer).trans le_sup_left, sup_le_normalizer_vOf_iP h.le_normalizer,
    EmptyFaithfulMultiple.L3213.isElemAbelian_vOf T (iP D p), ?_⟩
  intro E hE hEn hE2
  set V := vIP T D p with hVdef
  have hXTV : iP D p ⊔ T ≤ normalizer (V : Set G) := sup_le_normalizer_vOf_iP h.le_normalizer
  have hO := pCoreOf_autOn_vIP_eq_bot h hI
  set Xb := autOn (iP D p ⊔ T) V with hXb
  set Eb := autOn E V with hEb
  have hconj : ∀ g k : normalizer (V : Set G), conjAct V g * conjAct V k *
      (conjAct V g)⁻¹ = conjAct V (g * k * g⁻¹) := fun g k => by simp
  have hEbXb : Eb ≤ Xb := A4.autOn_mono hE
  have hXbEb : Xb ≤ normalizer (Eb : Set (MulAut V)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine mem_normalizer_fintype fun a ha => ?_
    obtain ⟨d, hd, rfl⟩ := ha
    rw [hconj]
    refine ⟨g * d * g⁻¹, mem_subgroupOf.mpr ?_, rfl⟩
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (hEn (mem_subgroupOf.mp hg)) d).mp (mem_subgroupOf.mp hd)
  have hEb2 : IsPGroup 2 Eb := by
    rintro ⟨_, d, hd, rfl⟩
    obtain ⟨k, hk⟩ := hE2 d (mem_subgroupOf.mp hd)
    refine ⟨k, Subtype.ext ?_⟩
    simp only [coe_pow, coe_one, ← map_pow]
    exact A4.conjAct_eq_one_iff.mpr (by simpa using hk)
  have hle : Eb ≤ pCoreOf 2 Xb := le_pCoreOf_of_le_normalizer 2 hEbXb hXbEb hEb2
  rw [hO] at hle
  intro d hd
  have hdN : d ∈ normalizer (V : Set G) := hXTV (hE hd)
  have h1 := hle ⟨⟨d, hdN⟩, mem_subgroupOf.mpr hd, rfl⟩
  rw [mem_bot] at h1
  exact A4.conjAct_eq_one_iff.mp h1

theorem pCoreOf_sup_eq_inf_centralizer (h : HomData T D p e)
    (hI : ¬ iP D p ≤ centralizer (reducedAggregate (D ⊔ T) : Set G)) :
    pCoreOf 2 (iP D p ⊔ T) = T ⊓ centralizer (vIP T D p : Set G) := by
  set V := vIP T D p with hVdef
  have hXTV : iP D p ⊔ T ≤ normalizer (V : Set G) := sup_le_normalizer_vOf_iP h.le_normalizer
  refine le_antisymm (le_inf ?_ (EmptyFaithfulMultiple.L3213.pCoreOf_sup_le_centralizer_vOf T _))
    ?_
  · exact pCoreOf_le_of_quasithinIsSylowTwo h.sylow (le_sup_right.trans le_normalizer)
  · rintro t ⟨ht, htV⟩
    refine mem_pCoreOf_sup_of_commutator_mem h hI ht fun x hx => ?_
    have h1 : x * t⁻¹ * x⁻¹ ∈ centralizer (V : Set G) :=
      (mem_normalizer_iff.mp (A4.mem_normalizer_centralizer
        (hXTV (le_sup_left (b := T) hx))) t⁻¹).mp (inv_mem htV)
    have e' : t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) := by group
    rw [e']
    exact mul_mem htV h1

end Module

end CFSG.Quasithin.Vol2.Ch11.OE4
