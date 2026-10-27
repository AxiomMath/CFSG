module

public import CFSG.Quasithin.Vol2.Ch7Sec77Min
public import CFSG.Quasithin.Vol2.Ch7Faith
public import CFSG.Quasithin.Background.HB56Three
public import CFSG.Quasithin.Background.HSL2InvFix
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.EmptyFaithful.SzN17Ctx

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem isSolvable_sup_of_le_normalizer {A B : Subgroup G} (hA : Group.IsSolvable ↥A)
    (hB : Group.IsSolvable ↥B) (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    Group.IsSolvable ↥(A ⊔ B) := by
  have hAK : A ≤ A ⊔ B := le_sup_left
  have hn : (A.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).2 (sup_le Subgroup.le_normalizer hBA)
  set f : ↥B →* ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_right) with hf
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := (SzN17.mem_sup_iff_of_right_le_normalizer hBA).1 hk
    refine ⟨⟨b, hb⟩, ?_⟩
    change (QuotientGroup.mk' _ (Subgroup.inclusion le_sup_right ⟨b, hb⟩) :
      ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) = QuotientGroup.mk ⟨a * b, hk⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (((Subgroup.inclusion le_sup_right ⟨b, hb⟩)⁻¹ * ⟨a * b, hk⟩ : ↥(A ⊔ B)) : G) ∈ A
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    have hb' : b⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ (hBA hb)
    have := (Subgroup.mem_normalizer_iff.mp hb' a).mp ha
    simpa [mul_assoc] using this
  have : Group.IsSolvable (↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_surjective hfs
  have : Group.IsSolvable ↥(A.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hAK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAK).injective
  exact Group.isSolvable_of_ker_le_range (A.subgroupOf (A ⊔ B)).subtype
    (QuotientGroup.mk' (A.subgroupOf (A ⊔ B)))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

omit [Finite G] in
theorem conj_mem_oTwoUpper_of_normalizer {X : Subgroup G} {g y : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hy : y ∈ oTwoUpper X) :
    g * y * g⁻¹ ∈ oTwoUpper X := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hx.1, ?_⟩
    have h1 := (MulAut.conj g).orderOf_eq x
    rw [MulAut.conj_apply] at h1
    rw [h1]
    exact hx.2
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

omit [Finite G] in
theorem le_normalizer_oTwoUpper {X Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (X : Set G)) :
    Y ≤ Subgroup.normalizer (oTwoUpper X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨conj_mem_oTwoUpper_of_normalizer (hY hg), fun h => ?_⟩
  have := conj_mem_oTwoUpper_of_normalizer (Subgroup.inv_mem _ (hY hg)) h
  simpa [mul_assoc] using this

theorem isSolvable_of_isPGroup {X : Subgroup G} (hX : IsPGroup 2 ↥X) : Group.IsSolvable ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hX.isNilpotent
  infer_instance

section Odd

variable {Ω : Type*} [Group Ω]

omit [Finite G] in
theorem eq_pow_two_pow_of_odd {g : Ω} {n : ℕ} (hn : Odd n) (hgn : g ^ n = 1) :
    g = (g ^ 2) ^ ((n + 1) / 2) := by
  obtain ⟨k, rfl⟩ := hn
  have e : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [e, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hgn, one_mul]

omit [Finite G] in
theorem conj_eq_of_odd {g : Ω} {n : ℕ} (hn : Odd n) (hgn : g ^ n = 1) {Q : Subgroup Ω}
    (hQ : Nat.card Q = 3) (hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) {z : Ω} (hz : z ∈ Q) :
    g * z * g⁻¹ = z := by
  have h2 : ∀ q ∈ Q, g ^ 2 * q * (g ^ 2)⁻¹ = q := by
    intro q hq
    by_cases hq1 : q = 1
    · subst hq1; group
    obtain ⟨hq3, hcases⟩ := SzN17.card_three_cases hQ hq hq1
    have hw : g * q * g⁻¹ ∈ Q := hgQ q hq
    have hw1 : g * q * g⁻¹ ≠ 1 := by
      intro h
      apply hq1
      have : q = g⁻¹ * (g * q * g⁻¹) * g := by group
      rw [this, h]
      group
    have e : g ^ 2 * q * (g ^ 2)⁻¹ = g * (g * q * g⁻¹) * g⁻¹ := by rw [pow_two]; group
    rcases hcases _ hw with h | h | h
    · exact absurd h hw1
    · rw [e, h, h]
    · rw [e, h]
      have : g * q⁻¹ * g⁻¹ = (g * q * g⁻¹)⁻¹ := by group
      rw [this, h, inv_inv]
  have hk : ∀ k : ℕ, (g ^ 2) ^ k * z * ((g ^ 2) ^ k)⁻¹ = z := by
    intro k
    induction k with
    | zero => group
    | succ k ih =>
      calc (g ^ 2) ^ (k + 1) * z * ((g ^ 2) ^ (k + 1))⁻¹ =
          (g ^ 2) ^ k * (g ^ 2 * z * (g ^ 2)⁻¹) * ((g ^ 2) ^ k)⁻¹ := by group
        _ = z := by rw [h2 z hz, ih]
  rw [eq_pow_two_pow_of_odd hn hgn]
  exact hk _

omit [Finite G] in
theorem map_conj_eq_of_odd {H Z₁ Z₂ : Subgroup Ω}
    (hΞ : ∀ Q : Subgroup Ω, SzN17.IsNormalThree H Q → Q = Z₁ ∨ Q = Z₂) {g : Ω} {n : ℕ}
    (hn : Odd n) (hgn : g ^ n = 1) (hgH : ∀ x, x ∈ H ↔ g * x * g⁻¹ ∈ H) {Q : Subgroup Ω}
    (hQ : SzN17.IsNormalThree H Q) : Q.map (MulAut.conj g).toMonoidHom = Q := by
  set c : Subgroup Ω → Subgroup Ω := fun R => R.map (MulAut.conj g).toMonoidHom with hc
  have hinj : Function.Injective c := Subgroup.map_injective (MulAut.conj g).injective
  have h1 : SzN17.IsNormalThree H (c Q) := SzN17.isNormalThree_map_conj hgH hQ
  have h2 : SzN17.IsNormalThree H (c (c Q)) := SzN17.isNormalThree_map_conj hgH h1
  by_contra hne
  have hccQ : c (c Q) = Q := by
    rcases hΞ Q hQ with e1 | e1 <;> rcases hΞ (c Q) h1 with e2 | e2 <;>
      rcases hΞ (c (c Q)) h2 with e3 | e3 <;>
      first
        | exact e3.trans e1.symm
        | exact absurd (e2.trans e1.symm) hne
        | exact absurd (hinj (e3.trans e2.symm)) hne
  have hpow : ∀ k : ℕ, Q.map (MulAut.conj ((g ^ 2) ^ k)).toMonoidHom = Q := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, map_one]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    | succ k ih =>
      have e : (MulAut.conj ((g ^ 2) ^ (k + 1))).toMonoidHom =
          (MulAut.conj ((g ^ 2) ^ k)).toMonoidHom.comp
            ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom) := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e, ← Subgroup.map_map, ← Subgroup.map_map]
      change (c (c Q)).map _ = Q
      rw [hccQ, ih]
  apply hne
  have h3 := hpow ((n + 1) / 2)
  rw [← eq_pow_two_pow_of_odd hn hgn] at h3
  exact h3

omit [Finite G] in
theorem fix_of_card_four {W : Type*} [CommGroup W] {A : Subgroup W} (hA : Nat.card A = 4)
    (hA2 : ∀ a ∈ A, a * a = 1) {w : W} (hwA : w ∈ A) (hw1 : w ≠ 1) {l : MulAut W}
    (hlA : ∀ a ∈ A, l a ∈ A) (hlw : l w = w) {n : ℕ} (hn : Odd n) (hln : l ^ n = 1) :
    ∀ a ∈ A, l a = a := by
  set D : Subgroup W := Subgroup.zpowers w with hD
  have hDA : D ≤ A := Subgroup.zpowers_le.2 hwA
  have hw2 : w * w = 1 := hA2 w hwA
  have hDcard : Nat.card D = 2 := by
    rw [hD, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
  have hidx : (D.subgroupOf A).index = 2 := by
    have h1 := Subgroup.card_mul_index (D.subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv, hDcard, hA] at h1
    omega
  have hlD : ∀ d ∈ D, l d = d := by
    intro d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    rw [map_zpow, hlw]
  have hkey : ∀ a ∈ A, l a * a⁻¹ ∈ D := by
    intro a ha
    by_cases haD : a ∈ D
    · rw [hlD a haD, mul_inv_cancel]
      exact D.one_mem
    · have hlaD : l a ∉ D := by
        intro h
        apply haD
        have := hlD _ h
        exact (l.injective this) ▸ h
      have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨l a, hlA a ha⟩ : ↥A))
        (b := (⟨a, ha⟩ : ↥A)⁻¹))
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      exact h1.2 (iff_of_false hlaD (fun h => haD (by simpa using D.inv_mem h)))
  have hD12 : ∀ d ∈ D, d = 1 ∨ d = w := by
    intro d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    have h2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
    have e : w ^ k = w ^ (k % 2) := by
      rw [← zpow_mod_orderOf w k, h2, Nat.cast_ofNat]
    rw [e]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  have hsq : ∀ a ∈ A, (l ^ 2) a = a := by
    intro a ha
    rcases hD12 _ (hkey a ha) with h | h
    · have hla : l a = a := mul_inv_eq_one.mp h
      rw [pow_two, MulAut.mul_apply, hla, hla]
    · have hla : l a = w * a := by
        rw [← h]
        group
      rw [pow_two, MulAut.mul_apply, hla, map_mul, hlw, hla, ← mul_assoc, hw2, one_mul]
  intro a ha
  have hk : ∀ k : ℕ, ((l ^ 2) ^ k) a = a := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hsq a ha, ih]
  have := hk ((n + 1) / 2)
  rwa [← eq_pow_two_pow_of_odd hn hln] at this

omit [Finite G] in
theorem card_two_of_isSylowTwoOf {P L : Subgroup Ω} (hP : IsSylowTwoOf P L)
    (hL : Nat.card L = 6) : Nat.card P = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  have hfinP : Finite ↥P := Finite.of_injective (Subgroup.inclusion hP.1)
    (Subgroup.inclusion_injective _)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥P)).mp hP.2.1
  have hmul := Subgroup.card_mul_index (P.subgroupOf L)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv, hk, hL] at hmul
  have hodd := hP.2.2
  have hk1 : k ≤ 1 := by
    by_contra h
    have : 2 ^ 2 ∣ 6 := by
      rw [← hmul]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    norm_num at this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with rfl | rfl
  · exfalso
    apply hodd
    rw [pow_zero, one_mul] at hmul
    rw [hmul]
    norm_num
  · rw [hk]
    norm_num

omit [Finite G] in
theorem exists_three_of_card_six {L : Subgroup Ω} (hL : Nat.card L = 6) :
    ∃ N : Subgroup Ω, N ≤ L ∧ Nat.card N = 3 ∧ (N.subgroupOf L).index = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 (by rw [hL]; norm_num)
  refine ⟨Subgroup.zpowers (x : Ω), Subgroup.zpowers_le.2 x.2, ?_, ?_⟩
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  · have h1 := Subgroup.card_mul_index ((Subgroup.zpowers (x : Ω)).subgroupOf L)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 x.2)).toEquiv,
      Nat.card_zpowers, Subgroup.orderOf_coe, hx, hL] at h1
    omega

end Odd

omit [Finite G] in
theorem autOn_sup {U A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (U : Set G))
    (hB : B ≤ Subgroup.normalizer (U : Set G)) : autOn (A ⊔ B) U = autOn A U ⊔ autOn B U :=
  CFSG.Quasithin.AutOn.autOn_sup_eq hA hB

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

theorem isSolvable_L_inf_centralizer (hc : S.Coord θ e) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := L ⊓ Subgroup.centralizer (fsuV T I : Set G) with hK
  have hcomm := H13.commutatorElement_mem_pCoreOf S.hyp.fsu.quasisimple S.L_le_normalizer_V
    S.pCoreOf_L_le (fun h => th_not_mem hc (h hc.mem))
  have hKK : ⁅K, K⁆ ≤ pCoreOf 2 L :=
    Subgroup.commutator_le.mpr fun x hx y hy => hcomm x hx y hy.1
  have h2 : IsPGroup 2 ↥(commutator ↥K) := by
    have h1 : IsPGroup 2 ↥(pCoreOf 2 L) := pCoreOf_isPGroup 2 L
    intro x
    have hx : ((x : ↥K) : G) ∈ ⁅K, K⁆ := by
      have hmap : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      rw [← hmap]
      exact ⟨x, x.2, rfl⟩
    obtain ⟨n, hn⟩ := h1 ⟨_, hKK hx⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have : Group.IsSolvable ↥(commutator ↥K) := by
    have := h2.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (commutator ↥K).subtype Abelianization.of
    (by rw [Abelianization.ker_of, Subgroup.range_subtype])

theorem isSolvable_L_inf_centralizer_V0 (hc : S.Coord θ e) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ((fsuV T I ⊓
      Subgroup.centralizer ({θ} : Set G) : Subgroup G) : Set G)) := by
  set X := L ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
    Subgroup G) : Set G) with hX
  have hXM : X ≤ fsuM T L := inf_le_left.trans S.L_le_fsuM
  have hX1 : X ≤ Subgroup.centralizer ({S.vec e a1} : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (vec_a1_mem_V0 hc)))
  obtain ⟨φ, hφ⟩ := exists_stabHom hc hXM hX1
  set χ : ↥X →* GL (Fin 2) (ZMod 2) := blkHom.comp φ with hχ
  have hle : L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ X :=
    inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))
  have := isSolvable_L_inf_centralizer hc
  have : Group.IsSolvable (GL (Fin 2) (ZMod 2)) := S153L.comp_solvable_of_card_six card_GL2
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) χ ?_
  intro x hx
  obtain ⟨g, hg1, hgd, hg⟩ := exists_stab0 hc (hXM x.2) x.2.2
  have hgφ : (φ x : SL32) = g := by
    apply SL3One.rho_injective
    rw [hφ x]
    exact hg
  have hb : blk g = 1 := by
    have h1 : (χ x : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
      rw [MonoidHom.mem_ker.mp hx]
      rfl
    rw [hχ, MonoidHom.comp_apply, coe_blkHom, hgφ] at h1
    exact h1
  have hg' : g = 1 := blk_fix_H0 hg1 hgd hb
  have hxV : (x : G) ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    rw [hg', map_one] at hg
    exact (convI_eq_one_iff S.hV _).mp ((congrHom_injective e) (hg.trans (map_one _).symm))
  exact ⟨⟨x, ⟨x.2.1, hxV⟩⟩, rfl⟩

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem isSolvable_LT : Group.IsSolvable ↥(oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔
    (T ⊓ Subgroup.centralizer (Vp : Set G))) := by
  have hX := isSolvable_L_inf_centralizer_V0 C.conf.hc
  rw [← C.hVp] at hX
  have hL₀ : Group.IsSolvable ↥(oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G))) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (oTwoUpper_le _))
  have hT₀ : Group.IsSolvable ↥(T ⊓ Subgroup.centralizer (Vp : Set G)) :=
    isSolvable_of_isPGroup C.conf.sylG.2.1
  refine isSolvable_sup_of_le_normalizer hL₀ hT₀ (le_normalizer_oTwoUpper ?_)
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have htL : t ∈ Subgroup.normalizer (L : Set G) := S.T_le_normalizer_L ht.1
  constructor
  · rintro ⟨hyL, hyC⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp htL y).mp hyL,
      (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).mul_mem ht.2 hyC)
        ((Subgroup.centralizer _).inv_mem ht.2)⟩
  · rintro ⟨hyL, hyC⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp htL y).mpr hyL, ?_⟩
    have := (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).mul_mem
      ((Subgroup.centralizer _).inv_mem ht.2) hyC) ht.2
    simpa [mul_assoc] using this

theorem exists_cComp_not_le (h3108 : Stmt3_2_10_eight) (h56 : AsB56) (h39 : A39ForSQTK)
    (hF : CharTwo H) : ∃ K ∈ cComp (thompsonJ H), ¬ K ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C.conf.hc
  set Tp := T ⊓ Subgroup.centralizer (Vp : Set G) with hTpdef
  set U := conjClosure (quasithinOmegaOneCenter Tp) H with hUdef
  obtain ⟨hUe, hred⟩ := C.isTwoReduced_U hF
  have : IsMulCommutative ↥U := hUe.1
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hyp.fsu.simple
    S.hyp.fsu.nonabelian C.conf.pCoreOf_ne_bot
  have hO2 : pCoreOf 2 (autOn H U) = ⊥ := CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred
  have hJH : thompsonJ H ≤ H := thompsonJ_le_self H
  have hHJ : H ≤ Subgroup.normalizer ((thompsonJ H : Subgroup G) : Set G) := fun g hg =>
    GammaExtra.normalizer_le_normalizer_thompsonJ H (Subgroup.le_normalizer hg)
  have hJn : ((thompsonJ H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).2 hHJ
  have hJsH : autOn (thompsonJ H) U ≤ autOn H U := InternalSec.autOn_le_autOn_of_le hJH
  have hJsn : ∀ h ∈ autOn H U, ∀ j ∈ autOn (thompsonJ H) U,
      h * j * h⁻¹ ∈ autOn (thompsonJ H) U := InternalSec.autOn_normal_of hHJ
  have hJsnorm : ((autOn (thompsonJ H) U).subgroupOf (autOn H U)).Normal :=
    (Subgroup.normal_subgroupOf_iff hJsH).2 fun h k hh hk => hJsn k hk h hh
  have hffJ : autOn (thompsonJ H) U = ffJ (autOn (thompsonJ H) U) :=
    le_antisymm (SzN17.autOn_thompsonJ_le_ffJ_self hUe hred.1 hHU) (B6.ffJ_le _)
  have hB53 : B53Hyp (autOn (thompsonJ H) U) :=
    SzN17.b53Hyp_of_normal hHU hSQ hO2 hJsH hJsnorm hffJ
  have hCU : H ⊓ Subgroup.centralizer (U : Set G) ≤ fsuM T L ⊓ H :=
    le_inf C.inf_centralizer_U_le inf_le_left
  have hle_of : ∀ X : Subgroup G, X ≤ H → autOn X U ≤ autOn (fsuM T L ⊓ H) U →
      X ≤ fsuM T L := fun X hXH h =>
    (S153D.le_of_autOn_le hHU hXH inf_le_right hCU h).trans inf_le_left
  have hJsM : ¬ autOn (thompsonJ H) U ≤ autOn (fsuM T L ⊓ H) U :=
    fun h => C.not_thompsonJ_le h3108 (hle_of _ hJH h)
  have hJne : autOn (thompsonJ H) U ≠ ⊥ := fun h => hJsM (h ▸ bot_le)
  have hV2 : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hUe.2 v v.2)
  have hcases := h56 ↥U hV2 _ hJne hB53
  set R := Tp ⊓ thompsonJ H with hRdef
  have hR : IsSylowTwoOf R (thompsonJ H) :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal C.conf.sylH hJH hJn.isSubnormal
  have hP : IsSylowTwoOf (autOn R U) (autOn (thompsonJ H) U) :=
    CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn hR (hJH.trans hHU)
  have hPM : autOn R U ≤ autOn (fsuM T L ⊓ H) U := InternalSec.autOn_le_autOn_of_le
    (le_inf (inf_le_left.trans (inf_le_left.trans S.T_le_fsuM)) (inf_le_right.trans hJH))
  by_contra hall
  push Not at hall
  have hSQJ : SQTKGroup ↥(thompsonJ H) := B5.sqtk_of_le hSQ hJH
  have hspan : cCompSpan (thompsonJ H) = perfectCore (thompsonJ H) :=
    cCompSpan_eq_perfectCore_of_subgroup _ (h39 _ (SQTKHyp.of_sqtkGroup ↥(thompsonJ H) hSQJ)).1
  have hcoreM : perfectCore (thompsonJ H) ≤ fsuM T L ⊓ H := by
    rw [← hspan]
    exact sSup_le fun K hK => le_inf (hall K hK) ((le_of_mem_cComp hK).trans hJH)
  have hcoreJs : perfectCore (autOn (thompsonJ H) U) ≤ autOn (fsuM T L ⊓ H) U := by
    intro φ hφ
    have hmap : perfectCore (autOn (thompsonJ H) U) =
        (perfectCore ((thompsonJ H).subgroupOf (Subgroup.normalizer (U : Set G)))).map
          (conjAct U) := by
      unfold autOn
      exact (map_perfectCore (conjAct U) _).symm
    rw [hmap] at hφ
    obtain ⟨x, hx, rfl⟩ := hφ
    have hxJ : (x : G) ∈ perfectCore (thompsonJ H) := by
      have h1 := map_perfectCore (Subgroup.normalizer (U : Set G)).subtype
        ((thompsonJ H).subgroupOf (Subgroup.normalizer (U : Set G)))
      rw [Subgroup.map_subgroupOf_eq_of_le (hJH.trans hHU)] at h1
      rw [← h1]
      exact ⟨x, hx, rfl⟩
    exact CFSG.QuasithinUnique.Setup.mem_autOn_iff.2 ⟨x, hcoreM hxJ, rfl⟩
  rcases B56N3.digest3_of_b56 hP hffJ hcases with hdec | ⟨Z₁, Z₂, hD⟩
  · exact hJsM (hdec.trans (sup_le hcoreJs hPM))
  set Js := autOn (thompsonJ H) U with hJsdef
  set Hs := autOn H U with hHsdef
  set Z := Z₁ ⊔ Z₂ with hZdef
  have hZM : ¬ Z ≤ autOn (fsuM T L ⊓ H) U :=
    fun h => hJsM (hD.decomp.trans (sup_le (sup_le hcoreJs h) hPM))
  have hZi : ∀ Q : Subgroup (MulAut ↥U), (Q = ⊥ ∨ SzN17.IsNormalThree Js Q) → Q ≤ Js := by
    rintro Q (rfl | hQ)
    · exact bot_le
    · exact hQ.1
  have hZJ : Z ≤ Js := sup_le (hZi _ hD.normal₁) (hZi _ hD.normal₂)
  have hHsJ : ∀ g ∈ Hs, ∀ x, x ∈ Js ↔ g * x * g⁻¹ ∈ Js := fun g hg x =>
    ⟨fun hx => hJsn g hg x hx, fun hx => by
      have := hJsn g⁻¹ (Hs.inv_mem hg) _ hx
      simpa [mul_assoc] using this⟩
  have hZn : ∀ g ∈ Hs, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
    intro g hg z hz
    have key : ∀ Q : Subgroup (MulAut ↥U), (Q = ⊥ ∨ SzN17.IsNormalThree Js Q) →
        Q.map (MulAut.conj g).toMonoidHom ≤ Z := by
      rintro Q (rfl | hQ)
      · rw [Subgroup.map_bot]
        exact bot_le
      · rcases hD.unique _ (SzN17.isNormalThree_map_conj (hHsJ g hg) hQ) with h | h
        · rw [h]
          exact le_sup_left
        · rw [h]
          exact le_sup_right
    have hmap : Z.map (MulAut.conj g).toMonoidHom ≤ Z := by
      rw [hZdef, Subgroup.map_sup]
      exact sup_le (key _ hD.normal₁) (key _ hD.normal₂)
    exact hmap ⟨z, hz, rfl⟩
  have hcyc : ∀ Q : Subgroup (MulAut ↥U), (Q = ⊥ ∨ SzN17.IsNormalThree Js Q) →
      ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    rintro Q (rfl | hQ) a ha b hb
    · rw [Subgroup.mem_bot] at ha
      rw [ha, one_mul, mul_one]
    · by_cases ha1 : a = 1
      · rw [ha1, one_mul, mul_one]
      obtain ⟨-, heq⟩ := SzN17.eq_zpowers_of_card_three hQ.2.2 ha ha1
      rw [heq] at hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.self_zpow a k).eq
  have hc12 : ∀ a ∈ Z₁, ∀ b ∈ Z₂, a * b = b * a := by
    rcases hD.normal₁ with h1 | h1
    · intro a ha b _
      rw [h1, Subgroup.mem_bot] at ha
      rw [ha, one_mul, mul_one]
    rcases hD.normal₂ with h2 | h2
    · intro a _ b hb
      rw [h2, Subgroup.mem_bot] at hb
      rw [hb, one_mul, mul_one]
    by_cases h12 : Z₁ = Z₂
    · intro a ha b hb
      rw [← h12] at hb
      exact hcyc Z₁ (Or.inr h1) a ha b hb
    · have hinf : Z₁ ⊓ Z₂ = ⊥ := by
        have hdvd : Nat.card ↥(Z₁ ⊓ Z₂) ∣ 3 := h1.2.2 ▸ Subgroup.card_dvd_of_le inf_le_left
        rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
        · exact Subgroup.card_eq_one.mp h
        · exfalso
          apply h12
          have e1 : Z₁ ⊓ Z₂ = Z₁ := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, h1.2.2])
          have e2 : Z₁ ⊓ Z₂ = Z₂ := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, h2.2.2])
          exact e1.symm.trans e2
      intro a ha b hb
      have hcomm : a * b * a⁻¹ * b⁻¹ ∈ Z₁ ⊓ Z₂ := by
        refine ⟨?_, ?_⟩
        · have := h1.2.1 b (h2.1 hb) a⁻¹ (Z₁.inv_mem ha)
          have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
          rw [e]
          exact Z₁.mul_mem ha this
        · have := h2.2.1 a (h1.1 ha) b hb
          exact Z₂.mul_mem this (Z₂.inv_mem hb)
      rw [hinf, Subgroup.mem_bot] at hcomm
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [hcomm, one_mul]
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := S153L.comp_exists_mul hc12 ha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := S153L.comp_exists_mul hc12 hb
    have e1 := hcyc Z₁ hD.normal₁ a₁ ha₁ b₁ hb₁
    have e2 := hcyc Z₂ hD.normal₂ a₂ ha₂ b₂ hb₂
    have e3 := hc12 a₁ ha₁ b₂ hb₂
    have e4 := hc12 b₁ hb₁ a₂ ha₂
    calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [e4]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
      _ = (b₁ * a₁) * (b₂ * a₂) := by rw [e1, e2]
      _ = b₁ * (a₁ * b₂) * a₂ := by group
      _ = b₁ * (b₂ * a₁) * a₂ := by rw [e3]
      _ = b₁ * b₂ * (a₁ * a₂) := by group
  set X : Subgroup G := H ⊓ (Z.comap (conjAct U)).map (Subgroup.normalizer (U : Set G)).subtype
    with hXdef
  have hXH : X ≤ H := inf_le_left
  have mem_X : ∀ x (hx : x ∈ H), x ∈ X ↔ conjAct U ⟨x, hHU hx⟩ ∈ Z := by
    intro x hx
    constructor
    · rintro ⟨-, ⟨y, hy, hyx⟩⟩
      have e : y = ⟨x, hHU hx⟩ := Subtype.ext hyx
      rw [← e]
      exact hy
    · intro h
      exact ⟨hx, ⟨⟨x, hHU hx⟩, h, rfl⟩⟩
  have hXn : H ≤ Subgroup.normalizer (X : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ H, ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
      intro g hg x hx
      have hgx : g * x * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg (hXH hx)) (H.inv_mem hg)
      refine (mem_X _ hgx).2 ?_
      have h1 := (mem_X x (hXH hx)).1 hx
      have h2 := hZn (conjAct U ⟨g, hHU hg⟩)
        (CFSG.QuasithinUnique.Setup.mem_autOn_iff.2 ⟨_, hg, rfl⟩) _ h1
      have e : conjAct U ⟨g * x * g⁻¹, hHU hgx⟩ =
          conjAct U ⟨g, hHU hg⟩ * conjAct U ⟨x, hHU (hXH hx)⟩ * (conjAct U ⟨g, hHU hg⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact h2
    intro y
    refine ⟨key h hh y, fun hy => ?_⟩
    have := key h⁻¹ (H.inv_mem hh) _ hy
    simpa [mul_assoc] using this
  have hZX : Z ≤ autOn X U := by
    intro z hz
    obtain ⟨⟨g, hgN⟩, hgH, hgz⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.1 (hJsH (hZJ hz))
    refine CFSG.QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨g, hgN⟩, (mem_X g hgH).2 ?_, hgz⟩
    rw [← hgz] at hz
    exact hz
  have hXZ : autOn X U ≤ Z := by
    intro φ hφ
    obtain ⟨⟨g, hgN⟩, hgX, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.1 hφ
    exact (mem_X g (hXH hgX)).1 hgX
  have hXM : ¬ X ≤ fsuM T L := fun h =>
    hZM (hZX.trans (InternalSec.autOn_le_autOn_of_le (le_inf h hXH)))
  have hHX : X ⊔ (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔ Tp) = H :=
    C.min _ le_sup_right (sup_le hXH C.conf.hLH) fun h => hXM (le_sup_left.trans h)
  have hsolv : Group.IsSolvable ↥Hs := by
    have := C.isSolvable_LT
    have h1 : Hs = autOn X U ⊔ autOn (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔ Tp) U :=
      by
        have e := autOn_sup (U := U) (hXH.trans hHU) (C.conf.hLH.trans hHU)
        rw [hHX] at e
        exact e
    have hXs : Group.IsSolvable ↥(autOn X U) :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (hZab _ (hXZ a.2) _ (hXZ b.2))
    have hLTs : Group.IsSolvable
        ↥(autOn (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔ Tp) U) :=
      Group.isSolvable_of_surjective (InternalSec.autOnHom_surjective (C.conf.hLH.trans hHU))
    have hnorm : autOn (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔ Tp) U ≤
        Subgroup.normalizer (autOn X U : Set (MulAut ↥U)) := by
      have hLTX : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔ Tp ≤
          Subgroup.normalizer (X : Set G) := C.conf.hLH.trans hXn
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => InternalSec.autOn_normal_of hLTX g hg y hy, fun hy => ?_⟩
      have := InternalSec.autOn_normal_of hLTX g⁻¹
        ((autOn (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔ Tp) U).inv_mem hg) _ hy
      simpa [mul_assoc] using this
    rw [h1]
    exact isSolvable_sup_of_le_normalizer hXs hLTs hnorm
  obtain ⟨hU', -, hcase, -⟩ := B2_16_of_quot hF hsolv C.conf.sylH rfl
  rcases hcase with ⟨hJT, -⟩ |
    ⟨hJT, Ifac, hsylJ, hJsup, hIcomm, hIind, hInat, hfixsup, -, -, hIperm⟩
  · apply C.not_thompsonJ_le h3108
    have h1 := B6.thompsonJ_le_of_sylow_of_le C.conf.sylH hJT (B6.le_normalizer_centralizer hHU)
    exact fun x hx => C.inf_centralizer_U_le ⟨hJH hx, h1 hx⟩
  have hθH : θ ∈ H := C.conf.th_mem_H
  set tθ : MulAut ↥U := conjAct U ⟨θ, hHU hθH⟩ with htθ
  have htθHs : tθ ∈ Hs := CFSG.QuasithinUnique.Setup.mem_autOn_iff.2 ⟨_, hθH, rfl⟩
  have hn : Odd (orderOf θ) := hc.odd
  have htθn : tθ ^ orderOf θ = 1 := by
    rw [htθ, ← map_pow]
    have e : (⟨θ, hHU hθH⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ orderOf θ = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [e, map_one]
  have hfixZi : ∀ Q : Subgroup (MulAut ↥U), (Q = ⊥ ∨ SzN17.IsNormalThree Js Q) →
      ∀ z ∈ Q, tθ * z * tθ⁻¹ = z := by
    rintro Q (rfl | hQ) z hz
    · rw [Subgroup.mem_bot] at hz
      rw [hz, mul_one, mul_inv_cancel]
    · have hmap := map_conj_eq_of_odd hD.unique hn htθn (hHsJ tθ htθHs) hQ
      refine conj_eq_of_odd hn htθn hQ.2.2 (fun q hq => ?_) hz
      rw [← hmap]
      exact ⟨q, hq, rfl⟩
  have hfixZ : ∀ z ∈ Z, tθ * z * tθ⁻¹ = z := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := S153L.comp_exists_mul hc12 hz
    have e1 := hfixZi Z₁ hD.normal₁ a ha
    have e2 := hfixZi Z₂ hD.normal₂ b hb
    calc tθ * (a * b) * tθ⁻¹ = (tθ * a * tθ⁻¹) * (tθ * b * tθ⁻¹) := by group
      _ = a * b := by rw [e1, e2]
  set JsI : Subgroup (MulAut (IntMod U hU')) := autI hU' (thompsonJ H) with hJsI
  set HsI : Subgroup (MulAut (IntMod U hU')) := autI hU' H with hHsI
  set tI : MulAut (IntMod U hU') := convI hU' ⟨θ, hHU hθH⟩ with htI
  have hJsHI : JsI ≤ HsI := autI_mono hU' hJH
  have htIHs : tI ∈ HsI := convI_mem_autI hU' hθH (hHU hθH)
  have htIn : tI ^ orderOf θ = 1 := htθn
  have hHsJI : ∀ g ∈ HsI, ∀ x, x ∈ JsI ↔ g * x * g⁻¹ ∈ JsI := fun g hg x => hHsJ g hg x
  have hDu : ∀ Q : Subgroup (MulAut (IntMod U hU')), SzN17.IsNormalThree JsI Q →
      Q = Z₁ ∨ Q = Z₂ := fun Q hQ => hD.unique Q hQ
  have hLJ : ∀ Lf ∈ Ifac, Lf ≤ JsI := fun Lf hL => by
    have h1 : Lf ≤ ⨆ L' ∈ Ifac, L' := le_iSup₂_of_le Lf hL le_rfl
    rw [← hJsup] at h1
    exact h1
  have hJsNL : ∀ Lf ∈ Ifac, ∀ g ∈ JsI, ∀ x ∈ Lf, g * x * g⁻¹ ∈ Lf := by
    intro Lf hL g hg x hx
    have hle : (⨆ L' ∈ Ifac, L') ≤ Subgroup.normalizer (Lf : Set (MulAut (IntMod U hU'))) := by
      refine iSup₂_le fun L' hL' => ?_
      by_cases h : L' = Lf
      · rw [h]
        exact Subgroup.le_normalizer
      · intro y hy
        exact Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.2 fun z hz => (hIcomm L' hL' Lf hL h y hy z hz).symm)
    have hg' : g ∈ ⨆ L' ∈ Ifac, L' := by
      rw [← hJsup]
      exact hg
    exact (Subgroup.mem_normalizer_iff.mp (hle hg') x).mp hx
  have hNL : ∀ Lf ∈ Ifac, ∃ N : Subgroup (MulAut (IntMod U hU')), N ≤ Lf ∧
      SzN17.IsNormalThree JsI N ∧ (N.subgroupOf Lf).index = 2 := by
    intro Lf hL
    obtain ⟨N, hNL, hN3, hNidx⟩ :=
      exists_three_of_card_six (SL2Nat.card_of_actsAsNaturalL2 (hInat Lf hL)).1
    refine ⟨N, hNL, ⟨hNL.trans (hLJ Lf hL), fun g hg q hq => ?_, hN3⟩, hNidx⟩
    have hgq : g * q * g⁻¹ ∈ Lf := hJsNL Lf hL g hg q (hNL hq)
    refine SzN17.mem_of_cube_of_index_two hNidx hgq ?_
    have hq3 : q ^ 3 = 1 := by
      have h1 : (⟨q, hq⟩ : ↥N) ^ Nat.card ↥N = 1 := pow_card_eq_one'
      rw [hN3] at h1
      have := congrArg Subtype.val h1
      simpa using this
    have e : g * q * g⁻¹ = MulAut.conj g q := rfl
    rw [e, ← map_pow, hq3, map_one]
  have hθLeq : ∀ Lf ∈ Ifac, B1.conjAut tI Lf = Lf := by
    intro Lf hL
    obtain ⟨N, hNL', hNn, -⟩ := hNL Lf hL
    have hNmap := map_conj_eq_of_odd hDu hn htIn (hHsJI tI htIHs) hNn
    obtain ⟨hmem, -⟩ := hIperm tI htIHs Lf hL
    by_contra hc'
    have hN1 : N ≤ B1.conjAut tI Lf := by
      intro q hq
      rw [B1.mem_conjAut]
      have hq' : tI⁻¹ * q * tI ∈ N := by
        have h1 : q ∈ N.map (MulAut.conj tI).toMonoidHom := by rw [hNmap]; exact hq
        obtain ⟨r, hr, hrq⟩ := h1
        rw [← hrq]
        simpa [mul_assoc] using hr
      exact hNL' hq'
    have hNbot : N ≤ Lf ⊓ ⨆ L' ∈ Ifac, ⨆ (_ : L' ≠ Lf), L' :=
      le_inf hNL' (hN1.trans (le_iSup₂_of_le (B1.conjAut tI Lf) hmem (le_iSup_of_le hc' le_rfl)))
    rw [hIind Lf hL] at hNbot
    have h1 := Subgroup.card_le_of_le hNbot
    rw [Subgroup.card_bot, hNn.2.2] at h1
    omega
  have hθL : ∀ Lf ∈ Ifac, ∀ x ∈ Lf, tI * x * tI⁻¹ ∈ Lf := by
    intro Lf hL x hx
    have h1 : tI * x * tI⁻¹ ∈ B1.conjAut tI Lf := by
      rw [B1.mem_conjAut]
      simpa [mul_assoc] using hx
    rwa [hθLeq Lf hL] at h1
  have hJTeq : thompsonJ Tp = thompsonJ T := by
    have hVp' : IsVplus T L I (fsuV T I) := Or.inr ⟨fun h => h.1 S.hL, rfl⟩
    have hJTp : thompsonJ T ≤ Tp := le_inf (thompsonJ_le_self T)
      (S.hJ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr C.conf.vp_le_V)))
    exact (h3108 G T L I (fsuV T I) S.hyp.fsu hVp' S.hJ Tp C.conf.sylG.2.1 hJTp).1.symm
  have hθJ : θ ∈ Subgroup.normalizer ((thompsonJ Tp : Subgroup G) : Set G) := by
    have hQ : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
      have h := S.hQ
      rwa [S.fsuL0_eq] at h
    have hJQ : thompsonJ (pCoreOf 2 (L ⊔ T)) = thompsonJ T :=
      B6.thompsonJ_eq_of_le (by rw [hQ]; exact le_inf (thompsonJ_le_self T) S.hJ)
        (by rw [hQ]; exact inf_le_left)
    have h1 : θ ∈ Subgroup.normalizer ((pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) :=
      le_normalizer_pCoreOf 2 (L ⊔ T) (le_sup_left (a := L) hc.mem)
    have h2 := GammaExtra.normalizer_le_normalizer_thompsonJ (pCoreOf 2 (L ⊔ T)) h1
    rw [hJQ] at h2
    rw [hJTeq]
    exact h2
  have htIJ : ∀ k ∈ autI hU' (thompsonJ Tp), tI * k * tI⁻¹ ∈ autI hU' (thompsonJ Tp) :=
    InternalSec.autOn_normal_of (Y := Subgroup.zpowers θ) (Subgroup.zpowers_le.2 hθJ) tI
      (convI_mem_autI hU' (Subgroup.mem_zpowers θ) (hHU hθH))
  have hfixL : ∀ Lf ∈ Ifac, ∀ v ∈ commV Lf, tI v = v := by
    intro Lf hL
    obtain ⟨hL6, hL4⟩ := SL2Nat.card_of_actsAsNaturalL2 (hInat Lf hL)
    have hLinv : ∀ x ∈ Lf, ∀ u ∈ commV Lf, x u ∈ commV Lf := by
      intro x hx u hu
      have hxHs : x ∈ HsI := hJsHI (hLJ Lf hL hx)
      have hcx : B1.conjAut x Lf = Lf := by
        apply le_antisymm
        · intro y hy
          rw [B1.mem_conjAut] at hy
          have := Lf.mul_mem (Lf.mul_mem hx hy) (Lf.inv_mem hx)
          simpa [mul_assoc] using this
        · intro y hy
          rw [B1.mem_conjAut]
          exact Lf.mul_mem (Lf.mul_mem (Lf.inv_mem hx) hy) hx
      have h1 := (hIperm x hxHs Lf hL).2
      rw [hcx] at h1
      have h2 : x u ∈ (commV Lf).map x.toMonoidHom := ⟨u, hu, rfl⟩
      rwa [h1] at h2
    have hS2 : IsSylowTwoOf (autI hU' (thompsonJ Tp) ⊓ Lf) Lf := by
      have hn' : (Lf.subgroupOf JsI).Normal :=
        (Subgroup.normal_subgroupOf_iff (hLJ Lf hL)).2 fun y g hy hg => hJsNL Lf hL g hg y hy
      exact RankOneRecog.isSylowTwoOf_inf_of_subnormal hsylJ (hLJ Lf hL) hn'.isSubnormal
    have hS2c : Nat.card ↥(autI hU' (thompsonJ Tp) ⊓ Lf) = 2 :=
      card_two_of_isSylowTwoOf hS2 hL6
    obtain ⟨⟨s, hs⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one
      (H := autI hU' (thompsonJ Tp) ⊓ Lf)).mp (fun h => by
        rw [h, Subgroup.card_bot] at hS2c
        omega)
    have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext (by simpa using h))
    have hss : s * s = 1 := by
      have h1 : (⟨s, hs⟩ : ↥(autI hU' (thompsonJ Tp) ⊓ Lf)) ^
          Nat.card ↥(autI hU' (thompsonJ Tp) ⊓ Lf) = 1 := pow_card_eq_one'
      rw [hS2c, pow_two] at h1
      have := congrArg Subtype.val h1
      simpa using this
    have hS2s : autI hU' (thompsonJ Tp) ⊓ Lf = Subgroup.zpowers s := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hs) ?_).symm
      rw [hS2c, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hss) hs1']
    have htIs : tI * s * tI⁻¹ = s := by
      have h1 : tI * s * tI⁻¹ ∈ autI hU' (thompsonJ Tp) ⊓ Lf := ⟨htIJ s hs.1, hθL Lf hL s hs.2⟩
      rw [hS2s] at h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      have h2 : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hss) hs1'
      have e : s ^ k = s ^ (k % 2) := by rw [← zpow_mod_orderOf s k, h2, Nat.cast_ofNat]
      rw [e] at hk
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · exfalso
        rw [h, zpow_zero] at hk
        apply hs1'
        have : s = tI⁻¹ * (tI * s * tI⁻¹) * tI := by group
        rw [this, ← hk]
        group
      · rw [h, zpow_one] at hk
        exact hk.symm
    obtain ⟨w, hwL, hw1, hsw, hwu⟩ :=
      SL2Nat.exists_fix_of_actsAsNaturalL2 (hInat Lf hL) hLinv hs.2 hs1' hss
    have hθV : ∀ u ∈ commV Lf, tI u ∈ commV Lf := by
      intro u hu
      have h1 := (hIperm tI htIHs Lf hL).2
      rw [hθLeq Lf hL] at h1
      have h2 : tI u ∈ (commV Lf).map tI.toMonoidHom := ⟨u, hu, rfl⟩
      rwa [h1] at h2
    have htIw : tI w = w := by
      have h1 : s (tI w) = tI w := by
        have e : s * tI = tI * s := by
          calc s * tI = (tI * s * tI⁻¹) * tI := by rw [htIs]
            _ = tI * s := by group
        calc s (tI w) = (s * tI) w := rfl
          _ = (tI * s) w := by rw [e]
          _ = tI (s w) := rfl
          _ = tI w := by rw [hsw]
      rcases hwu _ (hθV w hwL) h1 with h | h
      · exfalso
        apply hw1
        exact (MulEquiv.map_eq_one_iff tI).mp h
      · exact h
    exact fix_of_card_four hL4 (fun a _ => by rw [← pow_two]; exact IntMod.sq_eq_one a) hwL hw1
      hθV htIw hn htIn
  set W : Subgroup (IntMod U hU') := ⨆ Lf ∈ Ifac, commV Lf with hWdef
  have hfixW : ∀ v ∈ W, tI v = v := by
    let Fθ : Subgroup (IntMod U hU') :=
      { carrier := {v | tI v = v}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [map_mul, ha, hb]
        one_mem' := map_one tI
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_ofPred_eq] at ha ⊢
          rw [map_inv, ha] }
    have hle : W ≤ Fθ := iSup₂_le fun Lf hL v hv => hfixL Lf hL v hv
    exact fun v hv => hle hv
  have hWinv : ∀ g ∈ HsI, ∀ v ∈ W, g v ∈ W := by
    intro g hg v hv
    have hle : W.map (g : MulAut (IntMod U hU')).toMonoidHom ≤ W := by
      rw [hWdef, Subgroup.map_iSup]
      refine iSup_le fun Lf => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hL => ?_
      rw [(hIperm g hg Lf hL).2]
      exact le_iSup₂_of_le (B1.conjAut g Lf) (hIperm g hg Lf hL).1 le_rfl
    exact hle ⟨v, hv, rfl⟩
  have hZW : ∀ z : MulAut (IntMod U hU'), z ∈ JsI → ∀ u : IntMod U hU', z u * u⁻¹ ∈ W := by
    intro z hzJ u
    have hu : u ∈ fixV (autI hU' (thompsonJ H)) ⊔ W := by
      rw [hfixsup]
      exact Subgroup.mem_top u
    obtain ⟨f, hf, w', hw', rfl⟩ := Subgroup.mem_sup.mp hu
    have hzf : z f = f := (mem_fixV.mp hf) z hzJ
    have hzw : z w' ∈ W := hWinv z (hJsHI hzJ) w' hw'
    rw [map_mul, hzf, ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv]
    exact W.mul_mem hzw (W.inv_mem hw')
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hXθ : ∀ x ∈ X, ∀ k : ℕ, ∀ u ∈ U,
      x * (θ ^ k * u * (θ ^ k)⁻¹ * u⁻¹) * x⁻¹ = θ ^ k * u * (θ ^ k)⁻¹ * u⁻¹ := by
    intro x hx k u hu
    have hxH := hXH hx
    have hxN := hHU hxH
    have hθkN : θ ^ k ∈ Subgroup.normalizer (U : Set G) := Subgroup.pow_mem _ (hHU hθH) k
    have hzZ : conjAct U ⟨x, hxN⟩ ∈ Z := (mem_X x hxH).1 hx
    have hcN : x * θ ^ k * x⁻¹ * (θ ^ k)⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hθkN)
        (Subgroup.inv_mem _ hxN)) (Subgroup.inv_mem _ hθkN)
    have hθk : conjAct U ⟨θ ^ k, hθkN⟩ = tθ ^ k := by
      rw [htθ, ← map_pow]
      rfl
    have hcomm : tθ ^ k * conjAct U ⟨x, hxN⟩ = conjAct U ⟨x, hxN⟩ * tθ ^ k := by
      have h1 : tθ * conjAct U ⟨x, hxN⟩ = conjAct U ⟨x, hxN⟩ * tθ := by
        have := hfixZ _ hzZ
        calc tθ * conjAct U ⟨x, hxN⟩ = (tθ * conjAct U ⟨x, hxN⟩ * tθ⁻¹) * tθ := by group
          _ = conjAct U ⟨x, hxN⟩ * tθ := by rw [this]
      exact (Commute.pow_left h1 k).eq
    have hc' : x * θ ^ k * x⁻¹ * (θ ^ k)⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
      have h1 : conjAct U ⟨x * θ ^ k * x⁻¹ * (θ ^ k)⁻¹, hcN⟩ = 1 := by
        have e : conjAct U ⟨x * θ ^ k * x⁻¹ * (θ ^ k)⁻¹, hcN⟩ =
            conjAct U ⟨x, hxN⟩ * conjAct U ⟨θ ^ k, hθkN⟩ * (conjAct U ⟨x, hxN⟩)⁻¹ *
              (conjAct U ⟨θ ^ k, hθkN⟩)⁻¹ := by
          rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
          rfl
        rw [e, hθk, ← hcomm]
        group
      exact (convI_eq_one_iff hUe ⟨_, hcN⟩).mp h1
    have hxu : x * u * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hxN u).mp hu
    have hwU : x * u * x⁻¹ * u⁻¹ ∈ U := U.mul_mem hxu (U.inv_mem hu)
    have hw : θ ^ k * (x * u * x⁻¹ * u⁻¹) * (θ ^ k)⁻¹ = x * u * x⁻¹ * u⁻¹ := by
      set u' : IntMod U hU' := IntMod.mk hU' ⟨u, hu⟩ with hu'
      have hzJ : convI hU' ⟨x, hxN⟩ ∈ JsI := hZJ hzZ
      have h1 := hZW _ hzJ u'
      have h2 : ((convI hU' ⟨x, hxN⟩ u' * u'⁻¹ : IntMod U hU')).val = x * u * x⁻¹ * u⁻¹ := by
        rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val]
        rfl
      have h3 := pow_apply_eq_self (hfixW _ h1) k
      have h4 : ((tI ^ k) (convI hU' ⟨x, hxN⟩ u' * u'⁻¹)).val =
          θ ^ k * (convI hU' ⟨x, hxN⟩ u' * u'⁻¹).val * (θ ^ k)⁻¹ := by
        have e : tI ^ k = convI hU' ⟨θ ^ k, hθkN⟩ := by
          rw [htI, ← map_pow]
          rfl
        rw [e, convI_apply_val]
      rw [← h2, ← h4, h3]
    have hθu : θ ^ k * u * (θ ^ k)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hθkN u).mp hu
    have hy : θ ^ k * (x * u * x⁻¹ * u⁻¹ * u) * (θ ^ k)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hθkN _).mp (U.mul_mem hwU hu)
    have hcy : (x * θ ^ k * x⁻¹ * (θ ^ k)⁻¹) * (θ ^ k * (x * u * x⁻¹ * u⁻¹ * u) * (θ ^ k)⁻¹) *
        (x * θ ^ k * x⁻¹ * (θ ^ k)⁻¹)⁻¹ = θ ^ k * (x * u * x⁻¹ * u⁻¹ * u) * (θ ^ k)⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.mp hc' _ hy]
      group
    have e1 := hUcomm _ hwU _ hθu
    have e2 := hUcomm _ hwU _ (U.inv_mem hu)
    calc x * (θ ^ k * u * (θ ^ k)⁻¹ * u⁻¹) * x⁻¹
        = (x * θ ^ k * x⁻¹ * (θ ^ k)⁻¹) * (θ ^ k * (x * u * x⁻¹ * u⁻¹ * u) * (θ ^ k)⁻¹) *
            (x * θ ^ k * x⁻¹ * (θ ^ k)⁻¹)⁻¹ * (x * u * x⁻¹ * u⁻¹ * u)⁻¹ := by group
      _ = θ ^ k * (x * u * x⁻¹ * u⁻¹ * u) * (θ ^ k)⁻¹ * (x * u * x⁻¹ * u⁻¹ * u)⁻¹ := by rw [hcy]
      _ = (θ ^ k * (x * u * x⁻¹ * u⁻¹) * (θ ^ k)⁻¹) * (θ ^ k * u * (θ ^ k)⁻¹) * u⁻¹ *
            (x * u * x⁻¹ * u⁻¹)⁻¹ := by group
      _ = (x * u * x⁻¹ * u⁻¹) * (θ ^ k * u * (θ ^ k)⁻¹) * u⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ := by
          rw [hw]
      _ = (θ ^ k * u * (θ ^ k)⁻¹) * ((x * u * x⁻¹ * u⁻¹) * u⁻¹) * (x * u * x⁻¹ * u⁻¹)⁻¹ := by
          rw [e1]; group
      _ = θ ^ k * u * (θ ^ k)⁻¹ * u⁻¹ := by rw [e2]; group
  have hXV : X ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    intro x hx
    have hxVm : x ∈ Subgroup.centralizer (S.vm e : Set G) := by
      have hle : S.vm e ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [← commutator_vm hc, Subgroup.commutator_def, Subgroup.closure_le]
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have haU : a ∈ U := C.V_le_U (vm_le ha)
        obtain ⟨n, rfl⟩ : ∃ n : ℕ, θ ^ n = b := by
          have hfin : IsOfFinOrder θ := isOfFinOrder_of_finite θ
          exact (mem_powers_iff_mem_zpowers.mpr hb)
        have e : ⁅a, θ ^ n⁆ = θ ^ n * a⁻¹ * (θ ^ n)⁻¹ * a⁻¹⁻¹ := by
          rw [commutatorElement_def]
          have hθa : θ ^ n * a⁻¹ * (θ ^ n)⁻¹ ∈ U :=
            (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hHU hθH) n) _).mp (U.inv_mem haU)
          have := hUcomm _ haU _ hθa
          calc a * θ ^ n * a⁻¹ * (θ ^ n)⁻¹ = a * (θ ^ n * a⁻¹ * (θ ^ n)⁻¹) := by group
            _ = (θ ^ n * a⁻¹ * (θ ^ n)⁻¹) * a := this
            _ = θ ^ n * a⁻¹ * (θ ^ n)⁻¹ * a⁻¹⁻¹ := by rw [inv_inv]
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, e]
        have h1 := hXθ x hx n a⁻¹ (U.inv_mem haU)
        calc θ ^ n * a⁻¹ * (θ ^ n)⁻¹ * a⁻¹⁻¹ * x =
            x * (x⁻¹ * (θ ^ n * a⁻¹ * (θ ^ n)⁻¹ * a⁻¹⁻¹) * x) := by group
          _ = x * (θ ^ n * a⁻¹ * (θ ^ n)⁻¹ * a⁻¹⁻¹) := by
            congr 1
            calc x⁻¹ * (θ ^ n * a⁻¹ * (θ ^ n)⁻¹ * a⁻¹⁻¹) * x =
                x⁻¹ * (x * (θ ^ n * a⁻¹ * (θ ^ n)⁻¹ * a⁻¹⁻¹) * x⁻¹) * x := by rw [h1]
              _ = θ ^ n * a⁻¹ * (θ ^ n)⁻¹ * a⁻¹⁻¹ := by group
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv))
    exact C.conf.mem_centralizer_V (C.conf.hHG (hXH hx)) hxVm
  exact hXM fun x hx => S.centralizer_le_fsuM (hXV hx)

theorem exists_cComp_quasisimple (h3108 : Stmt3_2_10_eight) (h56 : AsB56) (h39 : A39ForSQTK)
    (hF : CharTwo H) : ∃ K ∈ cComp (thompsonJ H), ¬ K ≤ fsuM T L ∧
      CFSG.IsQuasisimple ↥(autOn K (conjClosure (quasithinOmegaOneCenter
        (T ⊓ Subgroup.centralizer (Vp : Set G))) H)) ∧
      B56QuasisimpleList ↥(autOn K (conjClosure (quasithinOmegaOneCenter
        (T ⊓ Subgroup.centralizer (Vp : Set G))) H)) := by
  obtain ⟨K, hK, hKM⟩ := C.exists_cComp_not_le h3108 h56 h39 hF
  set U := conjClosure (quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer (Vp : Set G))) H
    with hUdef
  obtain ⟨hUe, hred⟩ := C.isTwoReduced_U hF
  have : IsMulCommutative ↥U := hUe.1
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hyp.fsu.simple
    S.hyp.fsu.nonabelian C.conf.pCoreOf_ne_bot
  have hO2 : pCoreOf 2 (autOn H U) = ⊥ := CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred
  have hJH : thompsonJ H ≤ H := thompsonJ_le_self H
  have hHJ : H ≤ Subgroup.normalizer ((thompsonJ H : Subgroup G) : Set G) := fun g hg =>
    GammaExtra.normalizer_le_normalizer_thompsonJ H (Subgroup.le_normalizer hg)
  have hJsH : autOn (thompsonJ H) U ≤ autOn H U := InternalSec.autOn_le_autOn_of_le hJH
  have hJsn : ∀ h ∈ autOn H U, ∀ j ∈ autOn (thompsonJ H) U,
      h * j * h⁻¹ ∈ autOn (thompsonJ H) U := InternalSec.autOn_normal_of hHJ
  have hJsnorm : ((autOn (thompsonJ H) U).subgroupOf (autOn H U)).Normal :=
    (Subgroup.normal_subgroupOf_iff hJsH).2 fun h k hh hk => hJsn k hk h hh
  have hffJ : autOn (thompsonJ H) U = ffJ (autOn (thompsonJ H) U) :=
    le_antisymm (SzN17.autOn_thompsonJ_le_ffJ_self hUe hred.1 hHU) (B6.ffJ_le _)
  have hB53 : B53Hyp (autOn (thompsonJ H) U) :=
    SzN17.b53Hyp_of_normal hHU hSQ hO2 hJsH hJsnorm hffJ
  have hCU : H ⊓ Subgroup.centralizer (U : Set G) ≤ fsuM T L ⊓ H :=
    le_inf C.inf_centralizer_U_le inf_le_left
  have hle_of : ∀ X : Subgroup G, X ≤ H → autOn X U ≤ autOn (fsuM T L ⊓ H) U →
      X ≤ fsuM T L := fun X hXH h =>
    (S153D.le_of_autOn_le hHU hXH inf_le_right hCU h).trans inf_le_left
  have hJne : autOn (thompsonJ H) U ≠ ⊥ := fun h =>
    C.not_thompsonJ_le h3108 (hle_of _ hJH (by rw [h]; exact bot_le))
  have hV2 : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hUe.2 v v.2)
  have hKH : K ≤ H := (le_of_mem_cComp hK).trans hJH
  have hne : autOn K U ≠ ⊥ := fun h => hKM (hle_of K hKH (by rw [h]; exact bot_le))
  have hKc : autOn K U ∈ cComp (autOn (thompsonJ H) U) :=
    SzN17.autOn_mem_cComp (hJH.trans hHU) hK hne
  obtain ⟨hq, hlist⟩ := SzN17.quasisimple_of_mem_cComp h56 hV2 hJne hB53 hKc
  exact ⟨K, hK, hKM, hq, hlist⟩

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
