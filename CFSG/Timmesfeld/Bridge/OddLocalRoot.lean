module

public import CFSG.Timmesfeld.Bridge.OddLocalRootCore

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72

namespace OddLocal

section Reduction

variable {G : Type*} [Group G] {D : Set G}

theorem mem_rootGen_left (d x : G) : x ∈ rootGen D d x :=
  Subgroup.subset_closure (Set.mem_insert x _)

theorem mem_rootGen_of_mem {d x e : G} (he : e ∈ rootSet D d) : e ∈ rootGen D d x :=
  Subgroup.subset_closure (Set.mem_insert_of_mem x he)

@[expose] def classX (D : Set G) (d x : G) : Set (rootGen D d x) :=
  {y | IsConj (⟨x, mem_rootGen_left d x⟩ : rootGen D d x) y}

theorem classX_subset (hN : IsNormalSet D) {x : G} (hx : x ∈ D) {d : G} {y : rootGen D d x}
    (hy : y ∈ classX D d x) : (y : G) ∈ D := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hy
  exact hN c x hx

theorem eq_top_of_le_map {X : Subgroup G} {H : Subgroup X} (h : X ≤ H.map X.subtype) : H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨h', hh', he⟩ := h g.2
  have : h' = g := Subtype.ext he
  rw [← this]
  exact hh'

theorem mem_classX (hD : IsOddTransp D) {d x : G} (hx : x ∈ D) (hdx : ¬ Commute d x) {e : G}
    (he : e ∈ rootSet D d) :
    (⟨e, mem_rootGen_of_mem he⟩ : rootGen D d x) ∈ classX D d x := by
  have hex : ¬ Commute x e := fun h => hdx ((he.2 x hx).mp h.symm)
  obtain ⟨g, hg, hge⟩ := hD.exists_conj hx he.1 hex
  have hgX : g ∈ rootGen D d x := by
    have hle : Subgroup.closure ({x, e} : Set G) ≤ rootGen D d x := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact mem_rootGen_left d y
      · exact mem_rootGen_of_mem he
    exact hle hg
  refine isConj_iff.mpr ⟨⟨g, hgX⟩, Subtype.ext ?_⟩
  simpa using hge

theorem setup_classX (hD : IsOddTransp D) (hN : IsNormalSet D) {d x : G} (hx : x ∈ D)
    (hdx : ¬ Commute d x) : Setup (rootGen D d x) (classX D d x) := by
  refine ⟨⟨_, rfl⟩, ?_, ?_⟩
  · refine ⟨fun y hy => ?_, fun y hy z hz => ?_⟩
    · rw [← Subgroup.orderOf_coe]
      exact hD.1 _ (classX_subset hN hx hy)
    · rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
      exact hD.2 _ (classX_subset hN hx hy) _ (classX_subset hN hx hz)
  · apply eq_top_of_le_map
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (rfl | hy)
    · exact Subgroup.subset_closure ⟨⟨y, mem_rootGen_left d y⟩, IsConj.refl _, rfl⟩
    · exact Subgroup.subset_closure ⟨_, mem_classX hD hx hdx hy, rfl⟩

theorem mem_rootSet_classX (hD : IsOddTransp D) (hN : IsNormalSet D) {d x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x) {e : G} (he : e ∈ rootSet D d) :
    (⟨e, mem_rootGen_of_mem he⟩ : rootGen D d x) ∈
      rootSet (classX D d x) ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩ := by
  refine ⟨mem_classX hD hx hdx he, fun f hf => ?_⟩
  have h := he.2 (f : G) (classX_subset hN hx hf)
  constructor
  · intro hef
    exact Subtype.ext ((h.mp (hef.map (rootGen D d x).subtype)).eq)
  · intro hdf
    exact Subtype.ext ((h.mpr (hdf.map (rootGen D d x).subtype)).eq)

theorem rootGen_classX_eq_top (hD : IsOddTransp D) (hN : IsNormalSet D) {d x : G}
    (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x) :
    rootGen (classX D d x) ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩
      ⟨x, mem_rootGen_left d x⟩ = ⊤ := by
  apply eq_top_of_le_map
  have e : rootGen (classX D d x) ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩
      ⟨x, mem_rootGen_left d x⟩ = Subgroup.closure (insert ⟨x, mem_rootGen_left d x⟩
        (rootSet (classX D d x) ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩)) := rfl
  rw [e, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro y (rfl | hy)
  · exact Subgroup.subset_closure ⟨_, Set.mem_insert _ _, rfl⟩
  · exact Subgroup.subset_closure
      ⟨_, Set.mem_insert_of_mem _ (mem_rootSet_classX hD hN hd hx hdx hy), rfl⟩

end Reduction

section Quotient

variable {X : Type*} [Group X] [Finite X] {C : Set X}

omit [Finite X] in
theorem commute_iff_of_mem_pCore (hC : IsOddTransp C) {P : Subgroup X} [P.Normal]
    (hP : IsPGroup 2 P) {a b : X} (ha : a ∈ C) (hb : b ∈ C) :
    Commute (QuotientGroup.mk' P a) (QuotientGroup.mk' P b) ↔ Commute a b := by
  constructor
  · intro h
    by_contra hnc
    have hodd := hC.odd_of_not_commute ha hb hnc
    have hsq : (a * b) * (a * b) ∈ P := by
      have h1 : QuotientGroup.mk' P (a * b * (a * b)) = 1 := by
        simp only [map_mul]
        have ha2 : QuotientGroup.mk' P a * QuotientGroup.mk' P a = 1 := by
          rw [← map_mul, hC.mul_self_eq_one ha, map_one]
        have hb2 : QuotientGroup.mk' P b * QuotientGroup.mk' P b = 1 := by
          rw [← map_mul, hC.mul_self_eq_one hb, map_one]
        calc QuotientGroup.mk' P a * QuotientGroup.mk' P b *
              (QuotientGroup.mk' P a * QuotientGroup.mk' P b)
            = QuotientGroup.mk' P a * (QuotientGroup.mk' P b * QuotientGroup.mk' P a) *
                QuotientGroup.mk' P b := by group
          _ = QuotientGroup.mk' P a * (QuotientGroup.mk' P a * QuotientGroup.mk' P b) *
                QuotientGroup.mk' P b := by rw [h.eq]
          _ = 1 := by
              rw [← mul_assoc, ha2, one_mul, hb2]
      rwa [← QuotientGroup.ker_mk' P, MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := hP ⟨_, hsq⟩
    have hk' : ((a * b) * (a * b)) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hodd2 : Odd (orderOf ((a * b) * (a * b))) := by
      rw [← pow_two, orderOf_pow' _ (by norm_num)]
      exact Odd.of_dvd_nat hodd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
    have hdvd := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hi0 : i = 0 := by
      rcases i with _ | i
      · rfl
      · rw [hi, pow_succ] at hodd2
        exact absurd hodd2 (by simp [Nat.not_odd_iff_even])
    rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
    have h2 : orderOf (a * b) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hi)
    have h1 : orderOf (a * b) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h' | h'
      · exact h'
      · rw [h'] at hodd
        exact absurd hodd (by decide)
    rw [orderOf_eq_one_iff] at h1
    exact hnc (hC.eq_of_mul_eq_one ha h1 ▸ Commute.refl a)
  · intro h
    exact h.map _

omit [Finite X] in
theorem quotient_pCore_twoCore (N : Subgroup (X ⧸ CFSG.pCore 2 X)) (hN : N.Normal)
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  set P := CFSG.pCore 2 X
  have hPn : P.Normal := CFSG.BaerSuzuki.Helpers.pCore_normal 2
  have hP2 : IsPGroup 2 P := CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2
  have hker : (QuotientGroup.mk' P).ker = P := QuotientGroup.ker_mk' P
  have hM2 : IsPGroup 2 (N.comap (QuotientGroup.mk' P)) :=
    hN2.comap_of_ker_isPGroup _ (by rw [hker]; exact hP2)
  have hMn : (N.comap (QuotientGroup.mk' P)).Normal := hN.comap _
  have hle : N.comap (QuotientGroup.mk' P) ≤ P :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hMn hM2
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective P g
  have : g ∈ P := hle hg
  rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, hker]
  exact this

end Quotient

end OddLocal

open OddLocal in
theorem rootGen_quotient (h16 : OddTranspZStar) (h18 : CommonNeighbourStmt) {G : Type} [Group G]
    [Finite G] {D : Set G} (hD : IsOddTransp D) (hN : IsNormalSet D) {d x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x) :
    (∃ n, 2 ≤ n ∧
      Nonempty (rootGen D d x ⧸ CFSG.pCore 2 (rootGen D d x) ≃* CFSG.Theory.Comparator.PSL2Model n)) ∨
    (∃ n, 1 ≤ n ∧
      Nonempty (rootGen D d x ⧸ CFSG.pCore 2 (rootGen D d x) ≃* CFSG.Theory.Comparator.SzModel n)) ∨
    (let π := QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x))
     let dbar := π ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩
     let xbar := π ⟨x, mem_rootGen_left d x⟩
     Subgroup.closure {dbar, xbar} = ⊤ ∧ orderOf dbar = 2 ∧ orderOf xbar = 2 ∧
       Odd (orderOf (dbar * xbar)) ∧ 1 < orderOf (dbar * xbar) ∧
       ∀ e ∈ rootSet D d,
         e⁻¹ * d ∈ (CFSG.pCore 2 (rootGen D d x)).map (rootGen D d x).subtype) := by
  set X := rootGen D d x
  set P := CFSG.pCore 2 X
  set π := QuotientGroup.mk' P
  set C := classX D d x
  set d' : X := ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩
  set x' : X := ⟨x, mem_rootGen_left d x⟩
  have hS0 : Setup X C := setup_classX hD hN hx hdx
  have hP2 : IsPGroup 2 P := CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2
  have hcomm : ∀ a ∈ C, ∀ b ∈ C, Commute (π a) (π b) ↔ Commute a b := fun a ha b hb =>
    commute_iff_of_mem_pCore hS0.oddT hP2 ha hb
  have hd' : d' ∈ C := mem_classX hD hx hdx (mem_rootSet_self hd)
  have hx' : x' ∈ C := IsConj.refl _
  have hdx' : ¬ Commute (π d') (π x') := by
    rw [hcomm d' hd' x' hx']
    exact fun h => hdx (h.map X.subtype)
  have hne1 : ∀ k ∈ C, π k ≠ 1 := by
    intro k hk h1
    obtain ⟨c, rfl⟩ := isConj_iff.mp hk
    have hx1 : π x' = 1 := by
      calc π x' = (π c)⁻¹ * π (c * x' * c⁻¹) * π c := by
            rw [map_mul, map_mul, map_inv]
            group
        _ = 1 := by rw [h1, mul_one, inv_mul_cancel]
    apply hdx'
    rw [hx1]
    exact Commute.one_right _
  have hS1 : Setup (X ⧸ P) (π '' C) := hS0.map π (QuotientGroup.mk'_surjective P) hne1
  have hEC : ∀ y ∈ rootSet C d', π y ∈ rootSet (π '' C) (π d') := by
    intro y hy
    refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    rw [hcomm y hy.1 f hf, hcomm d' hd' f hf]
    exact hy.2 f hf
  have hgen : rootGen (π '' C) (π d') (π x') = ⊤ := by
    rw [eq_top_iff]
    rintro g -
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective P g
    have hg : g ∈ rootGen C d' x' :=
      (rootGen_classX_eq_top hD hN hd hx hdx) ▸ Subgroup.mem_top g
    have hle : rootGen C d' x' ≤ (rootGen (π '' C) (π d') (π x')).comap π := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y (rfl | hy)
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (hEC y hy))
    exact hle hg
  rcases rootGen_core h16 h18 hS1 quotient_pCore_twoCore ⟨d', hd', rfl⟩ ⟨x', hx', rfl⟩ hdx'
    hgen with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right
    right
    have hodd : Odd (orderOf (π d' * π x')) := by
      rw [← map_mul]
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd π (d' * x'))
      rw [← Subgroup.orderOf_coe]
      exact hD.odd_of_not_commute hd hx hdx
    refine ⟨?_, hS1.oddT.orderOf_eq_two ⟨d', hd', rfl⟩, hS1.oddT.orderOf_eq_two ⟨x', hx', rfl⟩,
      hodd, ?_, ?_⟩
    · rw [← hgen]
      show _ = Subgroup.closure (insert (π x') (rootSet (π '' C) (π d')))
      rw [h, Set.pair_comm]
    · rcases Nat.lt_or_ge 1 (orderOf (π d' * π x')) with h1 | h1
      · exact h1
      · exfalso
        have h0 : orderOf (π d' * π x') ≠ 0 := (orderOf_pos _).ne'
        have h1' : orderOf (π d' * π x') = 1 := by omega
        rw [orderOf_eq_one_iff] at h1'
        have := hS1.oddT.eq_of_mul_eq_one ⟨d', hd', rfl⟩ h1'
        exact hdx' (this ▸ Commute.refl _)
    · intro e he
      have hmem := hEC _ (mem_rootSet_classX hD hN hd hx hdx he)
      rw [h, Set.mem_singleton_iff, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at hmem
      exact ⟨_, hmem, by simp [d']⟩

end CFSG.Timmesfeld.Bridge
