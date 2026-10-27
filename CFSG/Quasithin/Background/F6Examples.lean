module

public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace F6

theorem perm_three_sq_key : ∀ g : Equiv.Perm (Fin 3), g ^ 2 = 1 →
    (∀ c : Equiv.Perm (Fin 3), (g * (c * g * c⁻¹)) ^ 2 = 1) → g = 1 := by
  decide +kernel

theorem perm_three_pow_six : ∀ g : Equiv.Perm (Fin 3), g ^ 6 = 1 := by
  decide +kernel

theorem sq_eq_one_of_mem_pCore_perm_three {g : Equiv.Perm (Fin 3)}
    (hg : g ∈ Open.pCore 2 (Equiv.Perm (Fin 3))) : g ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := Equiv.Perm (Fin 3)) 2) ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have h6 : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one (perm_three_pow_six g)
  have hj1 : j ≤ 1 := by
    by_contra hj1
    have : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega)).trans (hj ▸ h6)
    omega
  have : orderOf g ∣ 2 := by
    rw [hj]
    exact (pow_dvd_pow 2 hj1).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem pCore_perm_three_eq_bot : Open.pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hn : (Open.pCore 2 (Equiv.Perm (Fin 3))).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  exact perm_three_sq_key g (sq_eq_one_of_mem_pCore_perm_three hg) fun c =>
    sq_eq_one_of_mem_pCore_perm_three ((Open.pCore 2 _).mul_mem hg (hn.conj_mem g hg c))

theorem nonempty_quotient_pCore_of_mulEquiv {H : Type*} [Group H] [Finite H]
    (e : H ≃* Equiv.Perm (Fin 3)) : Nonempty (H ⧸ Open.pCore 2 H ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 e.symm.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.symm.injective]
    exact IsPGroup.of_bot
  exact gold_isoS3_of_surjective_kernel e.symm.toMonoidHom e.symm.surjective hker
    ((QuotientGroup.quotientMulEquivOfEq pCore_perm_three_eq_bot).trans
      QuotientGroup.quotientBot)

abbrev SymThreeSq := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)

theorem signMatched_mul_mem : ∀ a b : SymThreeSq, (a.1 ^ 3 = 1 ↔ a.2 ^ 3 = 1) →
    (b.1 ^ 3 = 1 ↔ b.2 ^ 3 = 1) → ((a * b).1 ^ 3 = 1 ↔ (a * b).2 ^ 3 = 1) := by
  decide +kernel

theorem signMatched_inv_mem : ∀ a : SymThreeSq, (a.1 ^ 3 = 1 ↔ a.2 ^ 3 = 1) →
    (a⁻¹.1 ^ 3 = 1 ↔ a⁻¹.2 ^ 3 = 1) := by
  decide +kernel

@[expose] def signMatched : Subgroup SymThreeSq where
  carrier := {x | x.1 ^ 3 = 1 ↔ x.2 ^ 3 = 1}
  mul_mem' := fun {a b} ha hb => signMatched_mul_mem a b ha hb
  one_mem' := Iff.rfl
  inv_mem' := fun {a} ha => signMatched_inv_mem a ha

instance : DecidablePred (· ∈ signMatched) := fun x =>
  inferInstanceAs (Decidable (x.1 ^ 3 = 1 ↔ x.2 ^ 3 = 1))

theorem mem_signMatched {x : SymThreeSq} : x ∈ signMatched ↔ (x.1 ^ 3 = 1 ↔ x.2 ^ 3 = 1) :=
  Iff.rfl

theorem swap_pair_mul : ∀ u v : Equiv.Perm (Fin 3), (u = 1 ∨ u = Equiv.swap 1 2) →
    (v = 1 ∨ v = Equiv.swap 1 2) → (u * v = 1 ∨ u * v = Equiv.swap 1 2) := by
  decide +kernel

theorem swap_pair_inv : ∀ u : Equiv.Perm (Fin 3), (u = 1 ∨ u = Equiv.swap 1 2) →
    (u⁻¹ = 1 ∨ u⁻¹ = Equiv.swap 1 2) := by
  decide +kernel

@[expose] def signMatchedLeft : Subgroup ↥signMatched where
  carrier := {x | x.1.2 = 1 ∨ x.1.2 = Equiv.swap 1 2}
  mul_mem' := fun {a b} ha hb => swap_pair_mul a.1.2 b.1.2 ha hb
  one_mem' := Or.inl rfl
  inv_mem' := fun {a} ha => swap_pair_inv a.1.2 ha

@[expose] def signMatchedRight : Subgroup ↥signMatched where
  carrier := {x | x.1.1 = 1 ∨ x.1.1 = Equiv.swap 1 2}
  mul_mem' := fun {a b} ha hb => swap_pair_mul a.1.1 b.1.1 ha hb
  one_mem' := Or.inl rfl
  inv_mem' := fun {a} ha => swap_pair_inv a.1.1 ha

instance : DecidablePred (· ∈ signMatchedLeft) := fun x =>
  inferInstanceAs (Decidable (x.1.2 = 1 ∨ x.1.2 = Equiv.swap 1 2))

instance : DecidablePred (· ∈ signMatchedRight) := fun x =>
  inferInstanceAs (Decidable (x.1.1 = 1 ∨ x.1.1 = Equiv.swap 1 2))

instance : DecidablePred (· ∈ signMatchedLeft ⊓ signMatchedRight) := fun x =>
  decidable_of_iff (x ∈ signMatchedLeft ∧ x ∈ signMatchedRight) Subgroup.mem_inf.symm

theorem card_signMatched : Nat.card ↥signMatched = 18 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_signMatched_inf : Nat.card ↥(signMatchedLeft ⊓ signMatchedRight) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem signMatched_left_inj : ∀ x y : SymThreeSq, ((x.1 ^ 3 = 1 ↔ x.2 ^ 3 = 1) ∧
    (y.1 ^ 3 = 1 ↔ y.2 ^ 3 = 1) ∧ (x.2 = 1 ∨ x.2 = Equiv.swap 1 2) ∧
    (y.2 = 1 ∨ y.2 = Equiv.swap 1 2) ∧ x.1 = y.1) → x = y := by
  decide +kernel

theorem signMatched_right_inj : ∀ x y : SymThreeSq, ((x.1 ^ 3 = 1 ↔ x.2 ^ 3 = 1) ∧
    (y.1 ^ 3 = 1 ↔ y.2 ^ 3 = 1) ∧ (x.1 = 1 ∨ x.1 = Equiv.swap 1 2) ∧
    (y.1 = 1 ∨ y.1 = Equiv.swap 1 2) ∧ x.2 = y.2) → x = y := by
  decide +kernel

@[expose] def signPartner (u : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 3) :=
  if u ^ 3 = 1 then 1 else Equiv.swap 1 2

theorem signPartner_spec : ∀ u : Equiv.Perm (Fin 3), (u ^ 3 = 1 ↔ signPartner u ^ 3 = 1) ∧
    (signPartner u = 1 ∨ signPartner u = Equiv.swap 1 2) := by
  unfold signPartner
  decide +kernel

@[expose] def signMatchedLeftHom : ↥signMatchedLeft →* Equiv.Perm (Fin 3) :=
  (MonoidHom.fst _ _).comp (signMatched.subtype.comp signMatchedLeft.subtype)

@[expose] def signMatchedRightHom : ↥signMatchedRight →* Equiv.Perm (Fin 3) :=
  (MonoidHom.snd _ _).comp (signMatched.subtype.comp signMatchedRight.subtype)

theorem signMatchedLeftHom_bijective : Function.Bijective signMatchedLeftHom := by
  refine ⟨fun a b hab => ?_, fun u => ?_⟩
  · exact Subtype.ext (Subtype.ext (signMatched_left_inj _ _ ⟨a.1.2, b.1.2, a.2, b.2, hab⟩))
  · obtain ⟨h1, h2⟩ := signPartner_spec u
    exact ⟨⟨⟨(u, signPartner u), h1⟩, h2⟩, rfl⟩

theorem signMatchedRightHom_bijective : Function.Bijective signMatchedRightHom := by
  refine ⟨fun a b hab => ?_, fun u => ?_⟩
  · exact Subtype.ext (Subtype.ext (signMatched_right_inj _ _ ⟨a.1.2, b.1.2, a.2, b.2, hab⟩))
  · obtain ⟨h1, h2⟩ := signPartner_spec u
    exact ⟨⟨⟨(signPartner u, u), h1.symm⟩, h2⟩, rfl⟩

@[expose] noncomputable def signMatchedLeftEquiv : ↥signMatchedLeft ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective _ signMatchedLeftHom_bijective

@[expose] noncomputable def signMatchedRightEquiv : ↥signMatchedRight ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective _ signMatchedRightHom_bijective

theorem signMatched_factor : ∀ x : SymThreeSq, (x.1 ^ 3 = 1 ↔ x.2 ^ 3 = 1) →
    ((x * (signPartner x.2, x.2)⁻¹).1 ^ 3 = 1 ↔ (x * (signPartner x.2, x.2)⁻¹).2 ^ 3 = 1) ∧
      ((x * (signPartner x.2, x.2)⁻¹).2 = 1 ∨
        (x * (signPartner x.2, x.2)⁻¹).2 = Equiv.swap 1 2) := by
  unfold signPartner
  decide +kernel

theorem signMatched_core_key : ∀ x : SymThreeSq, ((x.1 = 1 ∨ x.1 = Equiv.swap 1 2) ∧
    (x.2 = 1 ∨ x.2 = Equiv.swap 1 2) ∧
    (∀ g : SymThreeSq, (g.1 ^ 3 = 1 ↔ g.2 ^ 3 = 1) →
      (((g * x * g⁻¹).1 = 1 ∨ (g * x * g⁻¹).1 = Equiv.swap 1 2) ∧
        ((g * x * g⁻¹).2 = 1 ∨ (g * x * g⁻¹).2 = Equiv.swap 1 2)))) → x = 1 := by
  decide +kernel

theorem isGoldschmidtAmalgam_signMatched :
    IsGoldschmidtAmalgam signMatchedLeft signMatchedRight := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsGoldschmidtTriple signMatchedLeft signMatchedRight := by
    refine ⟨?_, nonempty_quotient_pCore_of_mulEquiv signMatchedLeftEquiv,
      nonempty_quotient_pCore_of_mulEquiv signMatchedRightEquiv, ?_⟩
    · refine top_le_iff.mp fun x _ => ?_
      obtain ⟨h1, h2⟩ := signMatched_factor x.1 x.2
      obtain ⟨h3, h4⟩ := signPartner_spec x.1.2
      let a : ↥signMatched := ⟨x.1 * (signPartner x.1.2, x.1.2)⁻¹, h1⟩
      let b : ↥signMatched := ⟨(signPartner x.1.2, x.1.2), h3.symm⟩
      have hab : x = a * b := Subtype.ext (mul_inv_cancel_right (x : SymThreeSq) _).symm
      rw [hab]
      exact Subgroup.mul_mem_sup (show a ∈ signMatchedLeft from h2)
        (show b ∈ signMatchedRight from h4)
    · have hP : IsPGroup 2 ↥(signMatchedLeft ⊓ signMatchedRight) :=
        IsPGroup.of_card (n := 1) (by rw [card_signMatched_inf, pow_one])
      have hidx : (signMatchedLeft ⊓ signMatchedRight).index = 9 := by
        have := Subgroup.index_mul_card (signMatchedLeft ⊓ signMatchedRight)
        rw [card_signMatched_inf, card_signMatched] at this
        omega
      exact ⟨hP.toSylow (by rw [hidx]; decide), hP.toSylow_coe _⟩
  refine ⟨hT, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hn : (Open.pCore 2 ↥signMatched).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hle := hT.pCore_le_inf
  have hx1 := hle hx
  refine Subtype.ext (signMatched_core_key x.1 ⟨(Subgroup.mem_inf.mp hx1).2,
    (Subgroup.mem_inf.mp hx1).1, fun g hg => ?_⟩)
  have hc := hle (hn.conj_mem x hx ⟨g, hg⟩)
  exact ⟨(Subgroup.mem_inf.mp hc).2, (Subgroup.mem_inf.mp hc).1⟩

@[expose] noncomputable def signMatchedInfEquiv :
    ↥(signMatchedLeft ⊓ signMatchedRight) ≃* Multiplicative (ZMod 2) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  mulEquivOfPrimeCardEq card_signMatched_inf (by simp)

theorem isGoldCaseI_signMatched : IsGoldCaseI signMatchedLeft signMatchedRight :=
  ⟨⟨signMatchedLeftEquiv⟩, ⟨signMatchedInfEquiv⟩, ⟨signMatchedRightEquiv⟩⟩

theorem isGoldCase_signMatched : IsGoldCase signMatchedLeft signMatchedRight :=
  Or.inl (Or.inl isGoldCaseI_signMatched)

theorem perm_three_cube_mul : ∀ u v : Equiv.Perm (Fin 3), u ^ 3 = 1 → v ^ 3 = 1 →
    (u * v) ^ 3 = 1 := by
  decide +kernel

theorem perm_three_cube_conj : ∀ u c : Equiv.Perm (Fin 3), u ^ 3 = 1 →
    (c * u * c⁻¹) ^ 3 = 1 := by
  decide +kernel

@[expose] def signMatchedThree : Subgroup ↥signMatched where
  carrier := {x | x.1.1 ^ 3 = 1 ∧ x.1.2 ^ 3 = 1}
  mul_mem' := fun {a b} ha hb =>
    ⟨perm_three_cube_mul _ _ ha.1 hb.1, perm_three_cube_mul _ _ ha.2 hb.2⟩
  one_mem' := ⟨one_pow 3, one_pow 3⟩
  inv_mem' := fun {a} ha => ⟨by simp [inv_pow, ha.1], by simp [inv_pow, ha.2]⟩

instance : DecidablePred (· ∈ signMatchedThree) := fun x =>
  inferInstanceAs (Decidable (x.1.1 ^ 3 = 1 ∧ x.1.2 ^ 3 = 1))

theorem card_signMatchedThree : Nat.card ↥signMatchedThree = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem signMatchedThree_normal : signMatchedThree.Normal where
  conj_mem := fun _ hx _ =>
    ⟨perm_three_cube_conj _ _ hx.1, perm_three_cube_conj _ _ hx.2⟩

theorem signMatchedThree_le_pCore : signMatchedThree ≤ Open.pCore 3 ↥signMatched := by
  refine CFSG.LieType.BorelTits.le_pCore 3 signMatchedThree_normal fun x => ⟨1, ?_⟩
  refine Subtype.ext (Subtype.ext ?_)
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  exact Prod.ext x.2.1 x.2.2

theorem not_isCyclic_pCore_three_signMatched : ¬ IsCyclic ↥(Open.pCore 3 ↥signMatched) := by
  intro hcyc
  have : IsCyclic ↥signMatchedThree := Subgroup.isCyclic_of_le signMatchedThree_le_pCore
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥signMatchedThree)
  rw [card_signMatchedThree] at hg
  have h3 : g ^ 3 = 1 := by
    refine Subtype.ext (Subtype.ext ?_)
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    exact Prod.ext g.2.1 g.2.2
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hg] at this
  omega

theorem signMatched_pow_six : ∀ x : SymThreeSq, x ^ 6 = 1 := by
  decide +kernel

@[expose] def signMatchedRot : SymThreeSq := (finRotate 3, finRotate 3)

theorem signMatchedRot_mem : signMatchedRot.1 ^ 3 = 1 ↔ signMatchedRot.2 ^ 3 = 1 := by
  unfold signMatchedRot
  decide +kernel

theorem signMatched_involution_key : ∀ x : SymThreeSq,
    ((x.1 ^ 3 = 1 ↔ x.2 ^ 3 = 1) ∧ x ^ 2 = 1 ∧ x ≠ 1) →
      ((x * (signMatchedRot * x * signMatchedRot⁻¹)) ^ 3 = 1 ∧
        x * (signMatchedRot * x * signMatchedRot⁻¹) ≠ 1) := by
  unfold signMatchedRot
  decide +kernel

theorem pPrimeCore_signMatched_eq_bot : CFSG.pPrimeCore 3 ↥signMatched = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hK hcop
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hne
  have hsq : x ^ 2 = 1 := by
    have h1 : orderOf x ∣ Nat.card ↥K := Subgroup.orderOf_dvd_natCard K hx
    have h6 : orderOf x ∣ 2 * 3 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (signMatched_pow_six x.1))
    have hc : Nat.Coprime (orderOf x) 3 :=
      Nat.Coprime.coprime_dvd_left h1 (Nat.coprime_comm.mp hcop)
    exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_right h6)
  obtain ⟨h3, h1⟩ := signMatched_involution_key x.1 ⟨x.2,
    congrArg Subtype.val hsq, fun h => hne (Subtype.ext h)⟩
  let g : ↥signMatched := ⟨signMatchedRot, signMatchedRot_mem⟩
  let y : ↥signMatched := x * (g * x * g⁻¹)
  have hy : y ∈ K := K.mul_mem hx (hK.conj_mem x hx _)
  have hy3 : orderOf y = 3 := by
    refine orderOf_eq_prime (Subtype.ext h3) fun h => h1 ?_
    exact congrArg Subtype.val h
  have hdvd : 3 ∣ Nat.card ↥K := by
    have := Subgroup.orderOf_dvd_natCard K hy
    rwa [hy3] at this
  have := Nat.Coprime.eq_one_of_dvd hcop hdvd
  omega

theorem isSolvable_signMatched : Group.IsSolvable ↥signMatched := by
  have : signMatchedThree.Normal := signMatchedThree_normal
  have hcomm : ∀ a b : ↥signMatchedThree, a * b = b * a := by
    have key : ∀ u v : SymThreeSq, (u.1 ^ 3 = 1 ∧ u.2 ^ 3 = 1 ∧ v.1 ^ 3 = 1 ∧ v.2 ^ 3 = 1) →
        u * v = v * u := by
      decide +kernel
    intro a b
    exact Subtype.ext (Subtype.ext (key _ _ ⟨a.2.1, a.2.2, b.2.1, b.2.2⟩))
  have : Group.IsSolvable ↥signMatchedThree := Group.isSolvable_of_comm hcomm
  have hq : Nat.card (↥signMatched ⧸ signMatchedThree) = 2 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup signMatchedThree
    rw [card_signMatched, card_signMatchedThree] at this
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (↥signMatched ⧸ signMatchedThree) := isCyclic_of_prime_card hq
  have : Group.IsSolvable (↥signMatched ⧸ signMatchedThree) :=
    Group.isSolvable_of_comm fun a b => IsCyclic.isMulCommutative.is_comm.comm a b
  exact Group.isSolvable_of_subgroup_quotient signMatchedThree

theorem stronglyQuasithin_signMatched : SQTKTauCeti.StronglyQuasithin ↥signMatched := by
  intro p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
  have hEp : IsPGroup p ↥E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  have hdvd : p ^ n ∣ 18 := by
    rw [← hn, ← card_signMatched]
    exact Subgroup.card_subgroup_dvd_card E
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rw [hn]
  refine Nat.pow_le_pow_right hp.pos ?_
  by_contra hn2
  have h27 : 3 ^ 3 ≤ p ^ n :=
    (Nat.pow_le_pow_left hp3 3).trans (Nat.pow_le_pow_right hp.pos (by omega))
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem kGroup_signMatched : CFSG.SectionRank.IsKGroupCat ↥signMatched := by
  intro H N _ hsimple
  have : Group.IsSolvable ↥signMatched := isSolvable_signMatched
  have : IsSimpleGroup (↥H ⧸ N) := hsimple
  exact CFSG.QuasithinUnique.catalog_of_commutative _
    fun a b => (IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance a b

theorem theoremF618_hypothesis_signMatched :
    ∃ (X : Type) (_ : Group X) (_ : Finite X), SQTKTauCeti.StronglyQuasithin X ∧
      CFSG.SectionRank.IsKGroupCat X ∧ Nonempty (↥signMatched ≃* X ⧸ CFSG.pPrimeCore 3 X) :=
  ⟨↥signMatched, inferInstance, inferInstance, stronglyQuasithin_signMatched,
    kGroup_signMatched, ⟨QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq pPrimeCore_signMatched_eq_bot.symm)⟩⟩

theorem pCoreOf_signMatchedLeft : pCoreOf 2 signMatchedLeft = ⊥ := by
  have h := map_pCore_mulEquiv 2 signMatchedLeftEquiv
  rw [pCore_perm_three_eq_bot] at h
  rw [pCoreOf, (Subgroup.map_eq_bot_iff_of_injective _ signMatchedLeftEquiv.injective).mp h,
    Subgroup.map_bot]

theorem pCoreOf_signMatchedRight : pCoreOf 2 signMatchedRight = ⊥ := by
  have h := map_pCore_mulEquiv 2 signMatchedRightEquiv
  rw [pCore_perm_three_eq_bot] at h
  rw [pCoreOf, (Subgroup.map_eq_bot_iff_of_injective _ signMatchedRightEquiv.injective).mp h,
    Subgroup.map_bot]

theorem isF618CaseOne_signMatched : IsF618CaseOne signMatchedLeft signMatchedRight :=
  ⟨⟨signMatchedInfEquiv⟩, pCoreOf_signMatchedLeft, pCoreOf_signMatchedRight,
    not_isCyclic_pCore_three_signMatched⟩

theorem f618Conclusion_signMatched : F618Conclusion signMatchedLeft signMatchedRight :=
  Or.inl (Or.inl isF618CaseOne_signMatched)

end F6

end CFSG.Quasithin
