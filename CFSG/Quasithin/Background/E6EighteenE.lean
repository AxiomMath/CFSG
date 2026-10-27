module

public import CFSG.Quasithin.Background.E6NineteenB
public import CFSG.Quasithin.Background.E6EighteenB

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

@[expose] def IsHeQuot {Y : Type} [Group Y] (K : Subgroup Y) : Prop :=
  Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* Blueprint.NativeSporadic.Carrier .He)

@[expose] def NoA7FixL115NotHe : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (z : Y), CFSG.IsQuasisimple ↥K →
    Lemma115Cases K z → ¬ IsHeQuot K → NoA7Fix (Bar.Qbar K)

section Tools

theorem not_hasA7Component_of_not_dvd {Q : Type*} [Group Q] [Finite Q]
    (h : ¬ 2520 ∣ Nat.card Q) : ¬ HasA7Component Q := by
  rintro ⟨B, -, hB⟩
  exact h (hB.dvd_card.trans (Subgroup.card_subgroup_dvd_card B))

theorem not_hasA7Component_of_isSimpleGroup {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (h : Nat.card Q ≠ 2520) : ¬ HasA7Component Q := by
  rintro ⟨B, hB, h7⟩
  have hBtop := Id2519.isComponent_eq_top_of_isSimpleGroup hB
  subst hBtop
  have hZ : Subgroup.center ↥(⊤ : Subgroup Q) = ⊥ :=
    Inn.center_eq_bot_of_isQuasisimple_of_simple hB.1
      (Subgroup.topEquiv (G := Q)).isSimpleGroup
  have hc := h7.card_eq
  rw [hZ, Subgroup.card_bot, one_mul, Subgroup.card_top] at hc
  exact h hc

theorem not_hasA7Component_of_commutator_simple {Q : Type*} [Group Q] [Finite Q]
    [IsSimpleGroup ↥(commutator Q)] (h : Nat.card ↥(commutator Q) ≠ 2520) :
    ¬ HasA7Component Q := by
  rintro ⟨B, hB, h7⟩
  have hBle : B ≤ commutator Q := Id2519.le_commutator_of_isQuasisimple hB.1
  have htop := Id2519.isComponent_eq_top_of_isSimpleGroup
    (CFSG.LocalCores.component_overgroup hB hBle)
  have hBeq : B = commutator Q := le_antisymm hBle (Subgroup.subgroupOf_eq_top.mp htop)
  have hs : IsSimpleGroup ↥B := by
    rw [hBeq]
    infer_instance
  have hZ : Subgroup.center ↥B = ⊥ :=
    Inn.center_eq_bot_of_isQuasisimple_of_simple hB.1 hs
  have hc := h7.card_eq
  rw [hZ, Subgroup.card_bot, one_mul, hBeq] at hc
  exact h hc

theorem two_pow_mul_ne_2520 {n M : ℕ} (hn : 4 ≤ n) : 2 ^ n * M ≠ 2520 := by
  intro h
  have h1 : 2 ^ 4 ∣ 2 ^ n * M := (pow_dvd_pow 2 hn).trans (Dvd.intro M rfl)
  rw [h] at h1
  norm_num at h1

theorem simple_nonab_of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (hs : IsSimpleGroup S) (hab : ∃ a b : S, a * b ≠ b * a) :
    IsSimpleGroup T ∧ ∃ a b : T, a * b ≠ b * a := by
  obtain ⟨a, b, h⟩ := hab
  refine ⟨e.isSimpleGroup_congr.mp hs, e a, e b, fun h' => h (e.injective ?_)⟩
  rw [map_mul, map_mul, h']

theorem center_eq_bot_of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : Subgroup.center S = ⊥) : Subgroup.center T = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hz (e g)
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot, ← e.apply_symm_apply z, hz', map_one]

theorem fixSubgroup_ne_top {S : Type*} [Group S] {α : MulAut S} (hne : α ≠ 1) :
    Id2519.fixSubgroup α ≠ ⊤ := by
  intro h
  apply hne
  ext x
  have hx : x ∈ Id2519.fixSubgroup α := by rw [h]; exact Subgroup.mem_top x
  exact hx

theorem hasA7Component_fixSubgroup_of_intertwine {H H' : Type*} [Group H] [Group H']
    (e : H ≃* H') (a : MulAut H) (a' : MulAut H') (h : ∀ y, a' (e y) = e (a y))
    (hK : HasA7Component ↥(Id2519.fixSubgroup a)) : HasA7Component ↥(Id2519.fixSubgroup a') :=
  hK.of_mulEquiv (((Id2519.fixSubgroup a).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (Id2519.fixSubgroup_eq_map e a a' h).symm))

theorem not_hasA7Component_fix_of_inner {Γ : Type*} [Group Γ] (hZ : Subgroup.center Γ = ⊥)
    (hfree : ∀ y : Γ, orderOf y = 2 →
      ∀ B : Subgroup ↥(Subgroup.centralizer ({y} : Set Γ)), ¬ CFSG.IsComponent B)
    {a : MulAut Γ} (haa : a * a = 1) (ha1 : a ≠ 1)
    (hin : a ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Γ) :
    ¬ HasA7Component ↥(Id2519.fixSubgroup a) := by
  obtain ⟨x, rfl⟩ := hin
  have hxx : x * x = 1 := by
    apply Id2519.conj_injective_of_center_bot hZ
    rw [map_mul, haa, map_one]
  have hx1 : x ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two, hxx]) hx1
  intro h
  obtain ⟨B, hB, -⟩ := h.of_mulEquiv (MulEquiv.subgroupCongr (Id2519.fixSubgroup_conj x))
  exact hfree x hord B hB

theorem noA7Fix_of_not_dvd {S : Type*} [Group S] [Finite S] (h : ¬ 2520 ∣ Nat.card S) :
    NoA7Fix S := fun _ _ _ =>
  not_hasA7Component_of_not_dvd fun h' => h (h'.trans (Subgroup.card_subgroup_dvd_card _))

theorem noA7Fix_of_card_le {S : Type*} [Group S] [Finite S] (h : Nat.card S ≤ 2520) :
    NoA7Fix S := by
  intro α _ hne hA
  obtain ⟨B, -, hB⟩ := hA
  have hlt : Nat.card ↥(Id2519.fixSubgroup α) < Nat.card S := by
    have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 (fixSubgroup_ne_top hne))
    rwa [Subgroup.card_top] at this
  have hle : Nat.card ↥B ≤ Nat.card ↥(Id2519.fixSubgroup α) := Subgroup.card_le_card_group B
  have hpos : 0 < Nat.card ↥B := Nat.card_pos
  have h2520 := Nat.le_of_dvd hpos hB.dvd_card
  omega

theorem noA7Fix_of_fixed_card {S : Type*} [Group S] [Finite S]
    (h : ∀ α : MulAut S, α * α = 1 → α ≠ 1 → ¬ 2520 ∣ Nat.card {x : S // α x = x}) :
    NoA7Fix S := by
  intro α hα hne
  refine not_hasA7Component_of_not_dvd ?_
  have hc : Nat.card ↥(Id2519.fixSubgroup α) = Nat.card {x : S // α x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  rw [hc]
  exact h α hα hne

end Tools

theorem noA7Fix_alt6 : NoA7Fix (alternatingGroup (Fin 6)) := by
  refine noA7Fix_of_card_le ?_
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at h
  have h6 : Nat.factorial 6 = 720 := by decide
  omega

theorem noA7Fix_alt7 : NoA7Fix (alternatingGroup (Fin 7)) :=
  noA7Fix_of_card_le card_alternatingGroup_seven.le

theorem noA7FixL115NotHe_of
    (hLie : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      SQTKCharTwoLie X → NoA7Fix X)
    (hU33 : ∀ (X : Type) [Group X] [Finite X],
      Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1 → NoA7Fix X)
    (hL33 : ∀ (X : Type) [Group X] [Finite X],
      Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 3 1 → NoA7Fix X)
    (hL2p : ∀ (X : Type) [Group X] [Finite X] (p : ℕ), IsFermatOrMersennePrime p →
      Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p 1 → NoA7Fix X)
    (hspor : ∀ s : TauCeti.SporadicName, IsLemma115SporadicName s → s ≠ .He →
      IsSimpleGroup (Blueprint.NativeSporadic.Carrier s) ∧
        NoA7Fix (Blueprint.NativeSporadic.Carrier s)) :
    NoA7FixL115NotHe := by
  intro Y _ _ K z hKq hcases hnHe
  rcases hcases with hA | hB | hC' | hD' | hE' | hF
  ·
    obtain ⟨hs, hlie, -⟩ := hA
    have hc : Subgroup.center ↥K = ⊥ := Inn.center_eq_bot_of_isQuasisimple_of_simple hKq hs
    let e : Bar.Qbar K ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    obtain ⟨hs', hab'⟩ := simple_nonab_of_mulEquiv e hKq.2.1 hKq.2.2
    refine NoA7Fix.of_mulEquiv e.symm ?_
    rcases hlie with hsq | h6 | hu33
    · exact hLie _ hs' hab' hsq
    · obtain ⟨e6⟩ := h6
      exact NoA7Fix.of_mulEquiv e6.symm noA7Fix_alt6
    · exact hU33 _ hu33
  ·
    obtain ⟨-, hZO, hL, -⟩ := hB
    let e : Bar.Qbar K ≃* (↥K ⧸ CFSG.pCore 2 ↥K) := QuotientGroup.quotientMulEquivOfEq hZO
    obtain ⟨hs', hab'⟩ := simple_nonab_of_mulEquiv e hKq.2.1 hKq.2.2
    refine NoA7Fix.of_mulEquiv e.symm (hLie _ hs' hab' ?_)
    rcases hL with h | h
    · exact Or.inl (Or.inl ⟨2, Or.inr (Or.inl ⟨by norm_num, h⟩)⟩)
    · exact Or.inl (Or.inl ⟨2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl, h⟩))))⟩)
  ·
    obtain ⟨φ, -, -, -, -⟩ := hC'
    exact NoA7Fix.of_mulEquiv φ.symm noA7Fix_alt6
  ·
    obtain ⟨φ, -, -, -, -⟩ := hD'
    exact NoA7Fix.of_mulEquiv φ.symm noA7Fix_alt7
  ·
    obtain ⟨hmodel, -⟩ := hE'
    have hs : IsSimpleGroup ↥K := by
      rcases hmodel with h33 | ⟨p, -, hp⟩
      · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 3 1 h33).2
      · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hp).2
    have hc : Subgroup.center ↥K = ⊥ := Inn.center_eq_bot_of_isQuasisimple_of_simple hKq hs
    let e : Bar.Qbar K ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    refine NoA7Fix.of_mulEquiv e.symm ?_
    rcases hmodel with h33 | ⟨p, hFM, hp⟩
    · exact hL33 _ h33
    · exact hL2p _ p hFM hp
  ·
    obtain ⟨⟨s, hs, ⟨ψ⟩⟩, -⟩ := hF
    have hsHe : s ≠ .He := by
      rintro rfl
      exact hnHe ⟨ψ⟩
    have hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
      ψ.isSimpleGroup_congr.mpr (hspor s hs hsHe).1
    have hO2 : CFSG.pCore 2 ↥K ≤ Subgroup.center ↥K := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq
          (N := CFSG.pCore 2 ↥K) CFSG.pCore_normal with hN | hN
      · exfalso
        have : Group.IsPerfect ↥K := hKq.1
        have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
        have hp : IsPGroup 2 ↥K := by
          have h1 : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup
          rw [hN] at h1
          exact h1.of_equiv Subgroup.topEquiv
        exact Group.IsPerfect.not_isNilpotent ↥K hp.isNilpotent
      · exact hN
    have hZO : Subgroup.center ↥K = CFSG.pCore 2 ↥K :=
      center_eq_of_quot_simple hKq hO2 hsimple
    exact NoA7Fix.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZO).trans ψ).symm
      (hspor s hs hsHe).2

end E6

end CFSG.Quasithin
