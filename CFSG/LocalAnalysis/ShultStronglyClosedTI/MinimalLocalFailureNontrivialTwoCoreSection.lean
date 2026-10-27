module

public import CFSG.GroupTheory.HyperplaneGeneration

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore

open CFSG CFSG.SolvableHall

variable {G : Type*} [Group G]

@[reducible] private def conjAction (T A : Subgroup G)
    (hTA : T ≤ Subgroup.normalizer (A : Set G)) : MulDistribMulAction T A where
  smul t a := ⟨t * a * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTA t.2) a).mp a.2⟩
  one_smul a := Subtype.ext (by change (1 : G) * a * 1⁻¹ = a; group)
  mul_smul s t a := Subtype.ext (by
    change (s * t : G) * a * (s * t : G)⁻¹ = s * (t * a * (t : G)⁻¹) * (s : G)⁻¹
    group)
  smul_mul t a b := Subtype.ext (by
    change (t : G) * (a * b) * (t : G)⁻¹ = (t * a * (t : G)⁻¹) * (t * b * (t : G)⁻¹)
    group)
  smul_one t := Subtype.ext (by change (t : G) * 1 * (t : G)⁻¹ = 1; group)

theorem le_normalizer_of_forall_conj_mem {E S : Subgroup G}
    (h : ∀ e ∈ E, ∀ s ∈ S, e * s * e⁻¹ ∈ S) : E ≤ Subgroup.normalizer (S : Set G) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨h e he s, fun hs => ?_⟩
  have h1 := h e⁻¹ (E.inv_mem he) _ hs
  have h2 : e⁻¹ * (e * s * e⁻¹) * e⁻¹⁻¹ = s := by group
  rwa [h2] at h1

theorem normal_subgroupOf_of_le_centralizer {Q M : Subgroup G}
    (hQ : Q ≤ Subgroup.centralizer (M : Set G)) : (Q.subgroupOf M).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hc := Subgroup.mem_centralizer_iff.mp (hQ hn) g g.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hc, mul_inv_cancel_right]
  exact hn

def centralPreimage (M Q : Subgroup G) (hQ : Q ≤ Subgroup.centralizer (M : Set G)) :
    Subgroup G where
  carrier := {a | a ∈ M ∧ ∀ m ∈ M, a * m * a⁻¹ * m⁻¹ ∈ Q}
  one_mem' := ⟨M.one_mem, fun m _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact Q.one_mem⟩
  mul_mem' := by
    rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
    refine ⟨M.mul_mem haM hbM, fun m hm => ?_⟩
    have hq := hb m hm
    have hqa : a * (b * m * b⁻¹ * m⁻¹) = (b * m * b⁻¹ * m⁻¹) * a :=
      Subgroup.mem_centralizer_iff.mp (hQ hq) a haM
    have heq : a * b * m * (a * b)⁻¹ * m⁻¹ = (b * m * b⁻¹ * m⁻¹) * (a * m * a⁻¹ * m⁻¹) := by
      calc a * b * m * (a * b)⁻¹ * m⁻¹ = (a * (b * m * b⁻¹ * m⁻¹)) * (m * a⁻¹ * m⁻¹) := by
            group
        _ = ((b * m * b⁻¹ * m⁻¹) * a) * (m * a⁻¹ * m⁻¹) := by rw [hqa]
        _ = _ := by group
    rw [heq]
    exact Q.mul_mem hq (ha m hm)
  inv_mem' := by
    rintro a ⟨haM, ha⟩
    refine ⟨M.inv_mem haM, fun m hm => ?_⟩
    have hq := ha m hm
    have hc : a⁻¹ * (a * m * a⁻¹ * m⁻¹)⁻¹ = (a * m * a⁻¹ * m⁻¹)⁻¹ * a⁻¹ :=
      Subgroup.mem_centralizer_iff.mp (hQ (Q.inv_mem hq)) a⁻¹ (M.inv_mem haM)
    have heq : a⁻¹ * m * a⁻¹⁻¹ * m⁻¹ = (a * m * a⁻¹ * m⁻¹)⁻¹ := by
      calc a⁻¹ * m * a⁻¹⁻¹ * m⁻¹ = a⁻¹ * (a * m * a⁻¹ * m⁻¹)⁻¹ * a := by group
        _ = (a * m * a⁻¹ * m⁻¹)⁻¹ * a⁻¹ * a := by rw [hc]
        _ = _ := by group
    rw [heq]
    exact Q.inv_mem hq

theorem mem_centralPreimage_iff {M Q : Subgroup G} {hQ : Q ≤ Subgroup.centralizer (M : Set G)}
    {a : G} : a ∈ centralPreimage M Q hQ ↔ a ∈ M ∧ ∀ m ∈ M, a * m * a⁻¹ * m⁻¹ ∈ Q :=
  Iff.rfl

def fixedCosetPreimage (A Q : Subgroup G) (hQ : Q ≤ Subgroup.centralizer (A : Set G)) (y : G) :
    Subgroup G where
  carrier := {b | b ∈ A ∧ b⁻¹ * (y * b * y⁻¹) ∈ Q}
  one_mem' := ⟨A.one_mem, by
    rw [inv_one, one_mul, mul_one, mul_inv_cancel]
    exact Q.one_mem⟩
  mul_mem' := by
    rintro b c ⟨hbA, hb⟩ ⟨hcA, hc⟩
    refine ⟨A.mul_mem hbA hcA, ?_⟩
    have hqc : c⁻¹ * (b⁻¹ * (y * b * y⁻¹)) = (b⁻¹ * (y * b * y⁻¹)) * c⁻¹ :=
      Subgroup.mem_centralizer_iff.mp (hQ hb) c⁻¹ (A.inv_mem hcA)
    have heq : (b * c)⁻¹ * (y * (b * c) * y⁻¹) =
        (b⁻¹ * (y * b * y⁻¹)) * (c⁻¹ * (y * c * y⁻¹)) := by
      calc (b * c)⁻¹ * (y * (b * c) * y⁻¹) = c⁻¹ * (b⁻¹ * (y * b * y⁻¹)) * (y * c * y⁻¹) := by
            group
        _ = (b⁻¹ * (y * b * y⁻¹)) * c⁻¹ * (y * c * y⁻¹) := by rw [hqc]
        _ = _ := by group
    rw [heq]
    exact Q.mul_mem hb hc
  inv_mem' := by
    rintro b ⟨hbA, hb⟩
    refine ⟨A.inv_mem hbA, ?_⟩
    have hqb : b * (b⁻¹ * (y * b * y⁻¹))⁻¹ = (b⁻¹ * (y * b * y⁻¹))⁻¹ * b :=
      Subgroup.mem_centralizer_iff.mp (hQ (Q.inv_mem hb)) b hbA
    have heq : b⁻¹⁻¹ * (y * b⁻¹ * y⁻¹) = (b⁻¹ * (y * b * y⁻¹))⁻¹ := by
      calc b⁻¹⁻¹ * (y * b⁻¹ * y⁻¹) = b * (b⁻¹ * (y * b * y⁻¹))⁻¹ * b⁻¹ := by group
        _ = (b⁻¹ * (y * b * y⁻¹))⁻¹ * b * b⁻¹ := by rw [hqb]
        _ = _ := by group
    rw [heq]
    exact Q.inv_mem hb

theorem mem_fixedCosetPreimage_iff {A Q : Subgroup G}
    {hQ : Q ≤ Subgroup.centralizer (A : Set G)} {y b : G} :
    b ∈ fixedCosetPreimage A Q hQ y ↔ b ∈ A ∧ b⁻¹ * (y * b * y⁻¹) ∈ Q :=
  Iff.rfl

variable [Finite G]

theorem exists_ne_one_fixing_coset {p : ℕ} [Fact p.Prime] {A Q E : Subgroup G}
    (hQn : (Q.subgroupOf A).Normal)
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEexp : ∀ a ∈ E, a ^ p = 1)
    (hEcard : p ^ 2 ≤ Nat.card E)
    (hEA : E ≤ Subgroup.normalizer (A : Set G)) (hEQ : E ≤ Subgroup.normalizer (Q : Set G))
    (hp : ¬ p ∣ Q.relIndex A) (hlt : Q < A) :
    ∃ y ∈ E, y ≠ 1 ∧ ∃ a ∈ A, a ∉ Q ∧ a⁻¹ * (y * a * y⁻¹) ∈ Q := by
  classical
  let : MulDistribMulAction E A := conjAction E A hEA
  have hsmul : ∀ (e : E) (a : A), ((e • a : A) : G) = e * a * (e : G)⁻¹ := fun _ _ => rfl
  have hinv : CFSG.IsInvariant E A (Q.subgroupOf A) := ⟨fun e a => by
    simp only [Subgroup.mem_subgroupOf, hsmul]
    exact Subgroup.mem_normalizer_iff.mp (hEQ e.2) a⟩
  let : MulDistribMulAction E (A ⧸ Q.subgroupOf A) :=
    quotientMulDistribMulAction (Q.subgroupOf A) hinv
  have hEpow : ∀ g : E, g ^ p = 1 := fun g => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hEexp g g.2)
  have : IsElementaryAbelian p E :=
    { toIsMulCommutative := isMulCommutative_iff.mpr fun a b => Subtype.ext (hEcomm a a.2 b b.2)
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hEpow }
  have hpV : ¬ p ∣ Nat.card (A ⧸ Q.subgroupOf A) := by
    rwa [← Subgroup.index_eq_card]
  have hgen := coprime_centralizer_generation (A := E) (H := A ⧸ Q.subgroupOf A) hEcard hpV
  by_contra hcon
  push Not at hcon
  have hbot : ∀ e : E, e ≠ 1 →
      fixedPointSubgroup (Subgroup.zpowers e) (A ⧸ Q.subgroupOf A) = ⊥ := by
    intro e he
    rw [eq_bot_iff]
    intro v hv
    rw [mem_fixedPointSubgroup_zpowers_iff] at hv
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective v
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    by_contra hbQ
    apply hcon e e.2 (fun h => he (Subtype.ext h)) b b.2 hbQ
    have h1 : ((e • b : A) : A ⧸ Q.subgroupOf A) = (b : A ⧸ Q.subgroupOf A) := hv
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have h2 := Q.inv_mem h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hsmul, mul_inv_rev, inv_inv] using h2
  have htop : (⊤ : Subgroup (A ⧸ Q.subgroupOf A)) = ⊥ := by
    rw [← hgen]
    exact iSup₂_eq_bot.mpr hbot
  obtain ⟨a, haA, haQ⟩ := IsConcreteLE.exists_of_lt hlt
  have h1 := Subgroup.mem_top (QuotientGroup.mk (⟨a, haA⟩ : A) : A ⧸ Q.subgroupOf A)
  rw [htop, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact haQ h1

theorem exists_fixed_mul_of_fixes_cosets {A Q : Subgroup G} {y : G}
    (hQn : (Q.subgroupOf A).Normal) (hQsolv : Group.IsSolvable Q)
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hcop : Nat.Coprime (orderOf y) (Nat.card Q)) (hQA : Q ≤ A)
    (hfix : ∀ a ∈ A, a⁻¹ * (y * a * y⁻¹) ∈ Q) {a : G} (ha : a ∈ A) :
    ∃ c ∈ A, y * c * y⁻¹ = c ∧ c⁻¹ * a ∈ Q := by
  classical
  set T := Subgroup.zpowers y with hTdef
  have hTA : T ≤ Subgroup.normalizer (A : Set G) := Subgroup.zpowers_le.mpr hyA
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hyQ
  let : MulDistribMulAction T A := conjAction T A hTA
  have hsmul : ∀ (s : T) (b : A), ((s • b : A) : G) = s * b * (s : G)⁻¹ := fun _ _ => rfl
  have hinv : CFSG.IsInvariant T A (Q.subgroupOf A) := ⟨fun s b => by
    simp only [Subgroup.mem_subgroupOf, hsmul]
    exact Subgroup.mem_normalizer_iff.mp (hTQ s.2) b⟩
  have hsolv : Group.IsSolvable (Q.subgroupOf A) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hQA).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hcop' : Nat.Coprime (Nat.card T) (Nat.card (Q.subgroupOf A)) := by
    rwa [hTdef, Nat.card_zpowers, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQA).toEquiv]
  let : MulDistribMulAction T (A ⧸ Q.subgroupOf A) :=
    quotientMulDistribMulAction (Q.subgroupOf A) hinv
  have hlift : fixedPointSubgroup T (A ⧸ Q.subgroupOf A) =
      (fixedPointSubgroup T A).map (QuotientGroup.mk' (Q.subgroupOf A)) :=
    coprime_solvable_kernel_fixed_point_lifting (Q.subgroupOf A) hinv hsolv hcop'
  set v : A ⧸ Q.subgroupOf A := QuotientGroup.mk (⟨a, ha⟩ : A) with hvdef
  have hy : (⟨y, Subgroup.mem_zpowers y⟩ : T) • v = v := by
    change (((⟨y, Subgroup.mem_zpowers y⟩ : T) • (⟨a, ha⟩ : A) : A) : A ⧸ Q.subgroupOf A) =
      (⟨a, ha⟩ : A)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := Q.inv_mem (hfix a ha)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hsmul, mul_inv_rev, inv_inv] using h1
  have hmem : v ∈ fixedPointSubgroup T (A ⧸ Q.subgroupOf A) := by
    intro s
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp s.2
    have hs : s = (⟨y, Subgroup.mem_zpowers y⟩ : T) ^ k := by
      apply Subtype.ext
      rw [SubgroupClass.coe_zpow]
      exact hk.symm
    rw [hs]
    exact MulAction.mem_fixedBy_zpow (α := A ⧸ Q.subgroupOf A) hy k
  rw [hlift] at hmem
  obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.mp hmem
  refine ⟨c, c.2, ?_, ?_⟩
  · exact congrArg Subtype.val (hc ⟨y, Subgroup.mem_zpowers y⟩)
  · have h2 := (QuotientGroup.eq (s := Q.subgroupOf A)).mp hca
    rwa [Subgroup.mem_subgroupOf] at h2

theorem exists_involution_central_mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {M Q E : Subgroup G} (hQM : Q ≤ M) (hQlt : Q < M) (hM2 : IsPGroup 2 M)
    (hQcent : Q ≤ Subgroup.centralizer (M : Set G))
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEexp : ∀ a ∈ E, a ^ p = 1)
    (hEcard : p ^ 2 ≤ Nat.card E)
    (hEM : E ≤ Subgroup.normalizer (M : Set G)) (hEQ : E ≤ Subgroup.normalizer (Q : Set G))
    (hdich : ∀ y ∈ E, y ≠ 1 →
      M ⊓ Subgroup.centralizer ({y} : Set G) ≤ Q ∨ Q ⊓ Subgroup.centralizer ({y} : Set G) = ⊥) :
    ∃ v ∈ M, v ∉ Q ∧ orderOf v = 2 ∧ ∀ m ∈ M, v * m * v⁻¹ * m⁻¹ ∈ Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := (Fact.out : p.Prime)
  set Z := centralPreimage M Q hQcent with hZdef
  have hZM : Z ≤ M := fun a ha => ha.1
  have hQZ : Q ≤ Z := fun q hq => ⟨hQM hq, fun m hm => by
    have hc : m * q = q * m := Subgroup.mem_centralizer_iff.mp (hQcent hq) m hm
    have heq : q * m * q⁻¹ * m⁻¹ = 1 := by
      rw [← hc, mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
    rw [heq]
    exact Q.one_mem⟩
  have hQZlt : Q < Z := by
    refine lt_of_le_of_ne hQZ fun hQZeq => ?_
    have hQMn := normal_subgroupOf_of_le_centralizer hQcent
    have hV2 : IsPGroup 2 (M ⧸ Q.subgroupOf M) := hM2.to_quotient _
    obtain ⟨a, haM, haQ⟩ := IsConcreteLE.exists_of_lt hQlt
    have : Nontrivial (M ⧸ Q.subgroupOf M) := ⟨⟨QuotientGroup.mk (⟨a, haM⟩ : M), 1, by
      rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact haQ⟩⟩
    have := hV2.center_nontrivial
    obtain ⟨⟨w, hw⟩, hw1⟩ := exists_ne (1 : Subgroup.center (M ⧸ Q.subgroupOf M))
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective w
    have hbQ : (b : G) ∉ Q := by
      intro hbQ
      apply hw1
      apply Subtype.ext
      change (QuotientGroup.mk b : M ⧸ Q.subgroupOf M) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hbQ
    apply hbQ
    rw [hQZeq]
    refine ⟨b.2, fun m hm => ?_⟩
    have hcomm := Subgroup.mem_center_iff.mp hw (QuotientGroup.mk (⟨m, hm⟩ : M))
    have h1 : (QuotientGroup.mk (b * ⟨m, hm⟩ * b⁻¹ * (⟨m, hm⟩ : M)⁻¹) : M ⧸ Q.subgroupOf M) =
        1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← hcomm]
      group
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) := by
    apply le_normalizer_of_forall_conj_mem
    rintro e he a ⟨haM, ha⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hEM he) a).mp haM, fun m hm => ?_⟩
    have hm' : e⁻¹ * m * e⁻¹⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hEM (E.inv_mem he)) m).mp hm
    have h1 := (Subgroup.mem_normalizer_iff.mp (hEQ he) _).mp (ha _ hm')
    have heq : e * (a * (e⁻¹ * m * e⁻¹⁻¹) * a⁻¹ * (e⁻¹ * m * e⁻¹⁻¹)⁻¹) * e⁻¹ =
        e * a * e⁻¹ * m * (e * a * e⁻¹)⁻¹ * m⁻¹ := by group
    rwa [heq] at h1
  let P : Subgroup G → Prop := fun A => Q < A ∧ A ≤ Z ∧ E ≤ Subgroup.normalizer (A : Set G)
  have hex : ∃ n, ∃ A, P A ∧ Nat.card A = n := ⟨_, Z, ⟨hQZlt, le_rfl, hEZ⟩, rfl⟩
  obtain ⟨A, ⟨hQA, hAZ, hEA⟩, hAn⟩ := Nat.find_spec hex
  have hmin : ∀ A', P A' → Nat.card A ≤ Nat.card A' := fun A' hA' =>
    hAn ▸ Nat.find_min' hex ⟨A', hA', rfl⟩
  have hAM : A ≤ M := hAZ.trans hZM
  have hQcentA : Q ≤ Subgroup.centralizer (A : Set G) :=
    hQcent.trans (Subgroup.centralizer_le hAM)
  have hQAn := normal_subgroupOf_of_le_centralizer hQcentA
  have hA2 : IsPGroup 2 A := hM2.to_le hAM
  have hpidx : ¬ p ∣ Q.relIndex A := by
    intro h
    obtain ⟨n, hn⟩ := hA2.exists_card_eq
    have hdvd : Q.relIndex A ∣ Nat.card A := Dvd.intro _ (Subgroup.relIndex_mul_card Q A)
    rw [hn] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (h.trans hdvd)))
  obtain ⟨y, hyE, hy1, a, haA, haQ, hay⟩ :=
    exists_ne_one_fixing_coset hQAn hEcomm hEexp hEcard hEA hEQ hpidx hQA
  set Ay := fixedCosetPreimage A Q hQcentA y with hAydef
  have hQAy : Q ≤ Ay := fun q hq => ⟨hQA.le hq, by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hEQ hyE) q).mp hq
    exact Q.mul_mem (Q.inv_mem hq) h1⟩
  have hEAy : E ≤ Subgroup.normalizer (Ay : Set G) := by
    apply le_normalizer_of_forall_conj_mem
    rintro e he b ⟨hbA, hb⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hEA he) b).mp hbA, ?_⟩
    have hye : y = e * y * e⁻¹ := by rw [hEcomm e he y hyE, mul_inv_cancel_right]
    have key : (e * b * e⁻¹)⁻¹ * (y * (e * b * e⁻¹) * y⁻¹) =
        e * (b⁻¹ * (y * b * y⁻¹)) * e⁻¹ := by
      conv_lhs => rw [hye]
      group
    rw [key]
    exact (Subgroup.mem_normalizer_iff.mp (hEQ he) _).mp hb
  have hAyA : Ay ≤ A := fun b hb => hb.1
  have hAyP : P Ay := ⟨lt_of_le_of_ne hQAy fun h => haQ (h ▸ ⟨haA, hay⟩), hAyA.trans hAZ, hEAy⟩
  have hAyeq : Ay = A := Subgroup.eq_of_le_of_card_ge hAyA (hmin Ay hAyP)
  have hfix : ∀ b ∈ A, b⁻¹ * (y * b * y⁻¹) ∈ Q := by
    intro b hb
    rw [← hAyeq] at hb
    exact hb.2
  have hyord : orderOf y = p := orderOf_eq_prime (hEexp y hyE) hy1
  have hQ2 : IsPGroup 2 Q := hM2.to_le hQM
  have hQsolv : Group.IsSolvable Q := by
    have : Group.IsNilpotent Q := hQ2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (orderOf y) (Nat.card Q) := by
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    rw [hyord, hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  obtain ⟨c, hcA, hcy, hca⟩ := exists_fixed_mul_of_fixes_cosets hQAn hQsolv (hEA hyE) (hEQ hyE)
    hcop hQA.le hfix haA
  have hcQ : c ∉ Q := fun h => haQ (by simpa only [mul_inv_cancel_left] using Q.mul_mem h hca)
  have hcC : c ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * y = y * c * y⁻¹ * y := by rw [hcy]
      _ = y * c := by group
  have hQy : Q ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ :=
    (hdich y hyE hy1).resolve_left fun h => hcQ (h ⟨hAM hcA, hcC⟩)
  set D := A ⊓ Subgroup.centralizer ({y} : Set G) with hDdef
  have hD2 : IsPGroup 2 D := hA2.to_le inf_le_left
  have hcD : c ∈ D := ⟨hcA, hcC⟩
  have h2D : 2 ∣ Nat.card D := by
    obtain ⟨n, hn⟩ := hD2.exists_card_eq
    rcases n with _ | n
    · exfalso
      rw [pow_zero] at hn
      have hc1 : (⟨c, hcD⟩ : D) = 1 := (Nat.card_eq_one_iff_unique.mp hn).1.elim _ _
      exact hcQ (by rw [show c = 1 from congrArg Subtype.val hc1]; exact Q.one_mem)
    · rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2D
  have hv2 : orderOf (v : G) = 2 := by rw [Subgroup.orderOf_coe, hv]
  have hvQ : (v : G) ∉ Q := by
    intro h
    have hv1 : (v : G) ∈ Q ⊓ Subgroup.centralizer ({y} : Set G) := ⟨h, v.2.2⟩
    rw [hQy, Subgroup.mem_bot] at hv1
    rw [hv1, orderOf_one] at hv2
    exact absurd hv2 (by norm_num)
  exact ⟨v, hAM v.2.1, hvQ, hv2, (hAZ v.2.1).2⟩

end CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore
