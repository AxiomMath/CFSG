module

public import CFSG.Quasithin.H13.A7Nat1238NQ21
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Background.A4Local
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.H13.A7Coordinates

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G]

theorem mem_of_odd_two_pow {H : Subgroup G} {y : G} (hy : orderOf y ≠ 0)
    (hodd : ∀ m : ℕ, Odd (orderOf (y ^ m)) → y ^ m ∈ H)
    (htwo : ∀ m k : ℕ, (y ^ m) ^ 2 ^ k = 1 → y ^ m ∈ H) : y ∈ H := by
  obtain ⟨e, o, ho, hord⟩ := Nat.exists_eq_two_pow_mul_odd hy
  have h1 : y ^ 2 ^ e ∈ H := by
    apply hodd
    have hd : orderOf (y ^ 2 ^ e) ∣ o :=
      orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, ← hord, pow_orderOf_eq_one])
    exact ho.of_dvd_nat hd
  have h2 : y ^ o ∈ H := htwo o e (by rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one])
  have hab : Nat.Coprime (2 ^ e) o := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr ho)
  have h := Nat.gcd_eq_gcd_ab (2 ^ e) o
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have hy' : y = (y ^ 2 ^ e) ^ (Nat.gcdA (2 ^ e) o) * (y ^ o) ^ (Nat.gcdB (2 ^ e) o) := by
    rw [← zpow_natCast y (2 ^ e), ← zpow_natCast y o, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h,
      zpow_one]
  rw [hy']
  exact H.mul_mem (H.zpow_mem h1 _) (H.zpow_mem h2 _)

@[expose] noncomputable def oddBar (K T : Subgroup G) :
    Subgroup (↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T)) :=
  (CFSG.oddCore ↥(modO2Image (K ⊔ T) K)).map (modO2Image (K ⊔ T) K).subtype

@[expose] noncomputable def oddPre (K T : Subgroup G) : Subgroup G :=
  ((oddBar K T).comap ((QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊔ T))).comp
    (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ T)))).map K.subtype

theorem mem_oddPre {K T : Subgroup G} {x : G} :
    x ∈ oddPre K T ↔ ∃ hx : x ∈ K,
      QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊔ T)) ⟨x, (le_sup_left : K ≤ K ⊔ T) hx⟩ ∈
        oddBar K T := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem oddPre_le (K T : Subgroup G) : oddPre K T ≤ K := Subgroup.map_subtype_le _

theorem le_normalizer_oddPre (K T : Subgroup G) :
    K ≤ normalizer (oddPre K T : Set G) := by
  have key : ∀ k ∈ K, ∀ x ∈ oddPre K T, k * x * k⁻¹ ∈ oddPre K T := by
    intro k hk x hx
    obtain ⟨hxK, hxo⟩ := mem_oddPre.1 hx
    have hy : k * x * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)
    refine mem_oddPre.2 ⟨hy, ?_⟩
    obtain ⟨o, ho, hox⟩ := hxo
    set l : ↥(modO2Image (K ⊔ T) K) :=
      ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊔ T)) ⟨k, (le_sup_left : K ≤ K ⊔ T) hk⟩,
        ⟨⟨k, (le_sup_left : K ≤ K ⊔ T) hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩⟩ with hl
    refine ⟨l * o * l⁻¹, (CFSG.oddCore_normal (G := ↥(modO2Image (K ⊔ T) K))).conj_mem o ho _,
      ?_⟩
    have e : (⟨k * x * k⁻¹, (le_sup_left : K ≤ K ⊔ T) hy⟩ : ↥(K ⊔ T)) =
        ⟨k, (le_sup_left : K ≤ K ⊔ T) hk⟩ * ⟨x, (le_sup_left : K ≤ K ⊔ T) hxK⟩ *
          ⟨k, (le_sup_left : K ≤ K ⊔ T) hk⟩⁻¹ := rfl
    have hox' : ((o : ↥(modO2Image (K ⊔ T) K)) : ↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T)) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊔ T)) ⟨x, (le_sup_left : K ≤ K ⊔ T) hxK⟩ := hox
    show ((l * o * l⁻¹ : ↥(modO2Image (K ⊔ T) K)) : ↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T)) = _
    rw [e, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hox']
  intro k hk
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hx
  simpa [mul_assoc] using this

variable [Finite G]

theorem oddPre_le_solvableRadical (K T : Subgroup G) :
    oddPre K T ≤ (CFSG.solvableRadical ↥K).map K.subtype := by
  intro x hx
  obtain ⟨hxK, hxo⟩ := mem_oddPre.1 hx
  exact mem_solvableRadical_of_mk_mem_oddCore le_sup_left hxK hxo

theorem mem_pCoreOf_of_mem_oddPre {K T : Subgroup G} {x : G} (hx : x ∈ oddPre K T) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ∈ pCoreOf 2 (K ⊔ T) := by
  obtain ⟨hxK, o, ho, hox⟩ := mem_oddPre.1 hx
  have hodd : Odd (Nat.card ↥(CFSG.oddCore ↥(modO2Image (K ⊔ T) K))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hox' : ((o : ↥(modO2Image (K ⊔ T) K)) : ↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T)) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊔ T)) ⟨x, (le_sup_left : K ≤ K ⊔ T) hxK⟩ := hox
  set o' : ↥(CFSG.oddCore ↥(modO2Image (K ⊔ T) K)) := ⟨o, ho⟩ with ho'
  have h1 : o' ^ 2 ^ k = 1 := by
    apply (CFSG.oddCore ↥(modO2Image (K ⊔ T) K)).subtype_injective
    apply (modO2Image (K ⊔ T) K).subtype_injective
    simp only [map_pow, map_one, Subgroup.coe_subtype]
    show ((o : ↥(modO2Image (K ⊔ T) K)) : ↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T)) ^ 2 ^ k = 1
    rw [hox', ← map_pow]
    have : (⟨x, (le_sup_left : K ≤ K ⊔ T) hxK⟩ : ↥(K ⊔ T)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hord : orderOf o' = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))) (orderOf_dvd_natCard _)
  have ho1 : o = 1 := by
    have := orderOf_eq_one_iff.1 hord
    exact congrArg Subtype.val this
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊔ T))
      (⟨x, (le_sup_left : K ≤ K ⊔ T) hxK⟩ : ↥(K ⊔ T)) = 1 := by
    rw [← hox', ho1]
    rfl
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  rw [pCoreOf_eq_map_cfsgPCore]
  exact ⟨⟨x, (le_sup_left : K ≤ K ⊔ T) hxK⟩, h2, rfl⟩

theorem noncentral_oTwoUpper_oddPre (K T : Subgroup G) :
    NoncentralTwoChiefFactorsInO2 (oTwoUpper (oddPre K T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := oTwoUpper (oddPre K T) with hX
  intro A B hAB
  exfalso
  obtain ⟨hOB, hBA, hAX, -, -, -, h2⟩ := hAB
  have hXH : X ≤ K ⊔ T := ((oTwoUpper_le _).trans (oddPre_le K T)).trans le_sup_left
  have hPX : pCoreOf 2 (K ⊔ T) ⊓ X ≤ pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun x hx => ?_)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    have h1 := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T) (hXH hx)
    have h2 := Subgroup.le_normalizer hx
    rw [mem_normalizer_iff] at h1 h2 ⊢
    intro y
    exact ⟨fun hy => ⟨(h1 y).1 hy.1, (h2 y).1 hy.2⟩, fun hy => ⟨(h1 y).2 hy.1, (h2 y).2 hy.2⟩⟩
  have htwoB : ∀ x ∈ X, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ B := fun x hx k hk =>
    hOB (hPX ⟨mem_pCoreOf_of_mem_oddPre (oTwoUpper_le _ hx) hk, hx⟩)
  apply (lt_iff_le_not_ge.mp hBA).2
  intro a ha
  have haX := hAX ha
  obtain ⟨k, hk⟩ := h2 a ha
  apply mem_of_odd_two_pow (orderOf_pos a).ne'
  · intro m hm
    have hmem : (a ^ m) ^ 2 ^ k ∈ B := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact B.pow_mem hk m
    have hcop : Nat.Coprime (2 ^ k) (orderOf (a ^ m)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
    exact (Subgroup.zpowers_le.mpr hmem) (A4.mem_zpowers_pow_of_coprime hcop)
  · intro m j hj
    exact htwoB _ (X.pow_mem haX m) j hj

theorem oddPre_le_centralizer (h3214 : Stmt3_2_14) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : QuasithinUnique.quasithinIsQTKECat G)
    {T K : Subgroup G} (hT : quasithinIsSylowTwo T) (hloc : quasithinIsLocal T K)
    (hTK : T ≤ normalizer (K : Set G)) (hnq : ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    oddPre K T ≤ centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ T)) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := oddPre K T with hPdef
  set X := oTwoUpper P with hX
  have hO : pCoreOf 2 (K ⊔ T) ≠ ⊥ := hloc.2.2.2
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hchar : QuasithinUnique.CharTwo (K ⊔ T) :=
    charTwo_of_inH hQ.2.1 S ⟨hS ▸ le_sup_right, hO⟩
  have hR := h3214 G T K hs hnab hQ hT hloc hnq
  have hPK : P ≤ K := oddPre_le K T
  have hKP : K ≤ normalizer (P : Set G) := le_normalizer_oddPre K T
  have hXP : X ≤ P := oTwoUpper_le P
  have hKM : K ≤ K ⊔ T := le_sup_left
  have hMK : K ⊔ T ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hXsub : IsSubnormal X (K ⊔ T) :=
    IsSubnormal.step hXP ((Subgroup.normal_subgroupOf_iff_le_normalizer hXP).mpr
      (le_normalizer_oTwoUpper P)) (IsSubnormal.step hPK
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mpr hKP)
        (A3.subnormal_of_normal hKM
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK)))
  have hXR : ⁅twoReducedJoin (K ⊔ T), X⁆ = ⊥ := by
    rw [← primeReducedAggregate_map_subtype_eq_twoReducedJoin,
      Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact (hXP.trans (oddPre_le_solvableRadical K T)).trans hR
  have htfae := a4_11 hchar (A4.oTwoUpper_oTwoUpper P).symm hXsub
    (noncentral_oTwoUpper_oddPre K T)
  have h13 : IsXf X ↔ ⁅twoReducedJoin (K ⊔ T), X⁆ ≠ ⊥ := htfae.out 1 3
  have hnXf : ¬ IsXf X := fun hXf => h13.mp hXf hXR
  have hXC : X ≤ centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ T)) : Set G) := by
    by_cases hX1 : X = ⊥
    · rw [hX1]
      exact bot_le
    have hXc : IsXClass X :=
      ⟨hX1, (A4.oTwoUpper_oTwoUpper P).symm, A4.charTwo_of_subnormal hXsub hchar⟩
    have hVY : VY X = ⊥ := by
      by_contra hne
      exact hnXf ⟨hXc, hne⟩
    have hb : ¬ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ T)), X⁆ ≠ ⊥ := fun hne =>
      ((a4_9 hXc hXsub).mp hne) hVY
    rw [not_not, Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
    exact Subgroup.le_centralizer_iff.mp hb
  intro y hy
  apply mem_of_odd_two_pow (orderOf_pos y).ne'
  · intro m hm
    exact hXC (mem_oTwoUpper_of_odd (P.pow_mem hy m) hm)
  · intro m k hk
    have hmem := mem_pCoreOf_of_mem_oddPre (P.pow_mem hy m) hk
    rw [mem_centralizer_iff]
    intro w hw
    exact (mem_centralizer_iff.1 (A4.centerOf_le_centralizer _
      (A4.omegaOneCenterOf_le_centerOf _ hw)) _ hmem).symm

omit [Finite G] in
theorem le_sup_of_le_sup_oddPre {T K Ke C : Subgroup G} (hKeK : Ke ≤ K)
    (hC : oddPre K T ≤ C)
    (hL : modO2Image (K ⊔ T) K ≤ modO2Image (K ⊔ T) Ke ⊔ oddBar K T) :
    K ≤ (K ⊓ C) ⊔ Ke := by
  set P := CFSG.pCore 2 ↥(K ⊔ T) with hP
  set L := modO2Image (K ⊔ T) K with hLdef
  set B := modO2Image (K ⊔ T) Ke with hB
  set OL := oddBar K T with hOL
  have hKH : K ≤ K ⊔ T := le_sup_left
  have hBL : B ≤ L := Subgroup.map_mono fun x hx => hKeK hx
  have hLN : L ≤ normalizer (OL : Set (↥(K ⊔ T) ⧸ P)) := by
    intro l hl
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨⟨l, hl⟩ * o * ⟨l, hl⟩⁻¹, (CFSG.oddCore_normal (G := ↥L)).conj_mem o ho _, rfl⟩
    · intro hx
      obtain ⟨o, ho, hox⟩ := hx
      refine ⟨⟨l, hl⟩⁻¹ * o * ⟨l, hl⟩, ?_, ?_⟩
      · have := (CFSG.oddCore_normal (G := ↥L)).conj_mem o ho (⟨l, hl⟩⁻¹)
        simpa using this
      · have h1 : (o : ↥(K ⊔ T) ⧸ P) = l * x * l⁻¹ := hox
        show ((⟨l, hl⟩⁻¹ * o * ⟨l, hl⟩ : ↥L) : ↥(K ⊔ T) ⧸ P) = x
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h1]
        group
  intro k hk
  have hkL : QuotientGroup.mk' P ⟨k, hKH hk⟩ ∈ L :=
    ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
  have hkBO : QuotientGroup.mk' P ⟨k, hKH hk⟩ ∈ OL ⊔ B := by
    have h := hL hkL
    rw [sup_comm B OL] at h
    exact h
  obtain ⟨o, ho, b, hb, hob⟩ :=
    Setup.Family.mem_sup_of_le_normalizer (hBL.trans hLN) hkBO
  obtain ⟨x, hx, rfl⟩ := hb
  have hxKe : (x : G) ∈ Ke := Subgroup.mem_subgroupOf.1 hx
  have hxK : (x : G) ∈ K := hKeK hxKe
  have hy : k * (x : G)⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hxK)
  have hyo : QuotientGroup.mk' P ⟨k * (x : G)⁻¹, hKH hy⟩ ∈ OL := by
    have h1 : (⟨k * (x : G)⁻¹, hKH hy⟩ : ↥(K ⊔ T)) = ⟨k, hKH hk⟩ * x⁻¹ := rfl
    rw [h1, map_mul, map_inv, hob, mul_inv_cancel_right]
    exact ho
  have hyC : k * (x : G)⁻¹ ∈ C := hC (mem_oddPre.2 ⟨hy, hyo⟩)
  have hkeq : k = (k * (x : G)⁻¹) * x := by group
  rw [hkeq]
  exact Subgroup.mul_mem_sup ⟨hy, hyC⟩ hxKe

end CFSG.Quasithin.H13.A7
