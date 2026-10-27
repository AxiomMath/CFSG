module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank

public section

namespace CFSG.Walter.Huppert

open scoped Pointwise commutatorElement

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem isMetacyclic_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : CFSG.IsMetacyclic G) : CFSG.IsMetacyclic H := by
  obtain ⟨N, hN, hNc, hQc⟩ := h
  refine ⟨N.map e.toMonoidHom, hN.map _ e.surjective, ?_, ?_⟩
  · exact (N.equivMapOfInjective e.toMonoidHom e.injective).isCyclic.mp hNc
  · have : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
    exact (QuotientGroup.congr N (N.map e.toMonoidHom) e rfl).isCyclic.mp hQc

omit hp in
theorem isMetacyclic_subgroup {G : Type*} [Group G] (h : CFSG.IsMetacyclic G) (H : Subgroup G) :
    CFSG.IsMetacyclic H := by
  obtain ⟨N, hN, hNc, hQc⟩ := h
  refine ⟨N.subgroupOf H, hN.subgroupOf H, ?_, ?_⟩
  · let f : N.subgroupOf H →* N :=
      { toFun := fun x => ⟨(x : H), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective f := by
      intro x y hxy
      have h := congrArg (fun z : N => (z : G)) hxy
      exact Subtype.ext (Subtype.ext h)
    exact isCyclic_of_injective f hinj
  ·
    let φ : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
    have hker : φ.ker = N.subgroupOf H := by
      ext x
      simp [φ, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
    have hinj : Function.Injective (QuotientGroup.kerLift φ) := QuotientGroup.kerLift_injective φ
    let e : H ⧸ φ.ker ≃* H ⧸ N.subgroupOf H := QuotientGroup.quotientMulEquivOfEq hker
    have : IsCyclic (H ⧸ φ.ker) := isCyclic_of_injective _ hinj
    exact e.isCyclic.mp this

omit hp in
theorem isMetacyclic_of_le {X : Type*} [Group X] {Q P : Subgroup X} (hQP : Q ≤ P)
    (h : CFSG.IsMetacyclic P) : CFSG.IsMetacyclic Q :=
  isMetacyclic_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQP) (isMetacyclic_subgroup h _)

omit hp in
theorem isCyclic_commutator {G : Type*} [Group G] (h : CFSG.IsMetacyclic G) :
    IsCyclic (commutator G) := by
  obtain ⟨N, hN, hNc, hQc⟩ := h
  have hcomm : IsMulCommutative (G ⧸ N) := hQc.isMulCommutative
  have hle : commutator G ≤ N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).1 hcomm
  exact Subgroup.isCyclic_of_le hle

theorem frattini_quotient_facts {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G) :
    (∀ a b : G ⧸ frattini G, a * b = b * a) ∧ ∀ v : G ⧸ frattini G, v ^ p = 1 := by
  have : Fact (IsPGroup p G) := ⟨hG⟩
  have h := CFSG.isElementaryAbelian_quotient_frattini (R := G) (p := p)
  refine ⟨fun a b => h.toIsMulCommutative.is_comm.comm a b, fun v => ?_⟩
  exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.exponent_dvd_p) v

theorem mem_frattini_of_isPGroup {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G) (x : G) :
    x ^ p ∈ frattini G := by
  have : Fact (IsPGroup p G) := ⟨hG⟩
  exact CFSG.pth_power_mem_frattini_of_isPGroup (R := G) (p := p) x

theorem commutator_le_frattini {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G) :
    commutator G ≤ frattini G := by
  have : Fact (IsPGroup p G) := ⟨hG⟩
  exact CFSG.commutator_le_frattini_of_isPGroup (R := G) (p := p)

theorem card_frattini_quotient_le_sq {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    {a b : G} (hab : ∀ g : G, ∃ i j : ℕ, (g : G ⧸ frattini G) = (a : G ⧸ frattini G) ^ i *
      (b : G ⧸ frattini G) ^ j) :
    Nat.card (G ⧸ frattini G) ≤ p ^ 2 := by
  obtain ⟨-, hpow⟩ := frattini_quotient_facts hG
  let φ : Fin p × Fin p → G ⧸ frattini G := fun x =>
    (a : G ⧸ frattini G) ^ (x.1 : ℕ) * (b : G ⧸ frattini G) ^ (x.2 : ℕ)
  have hsurj : Function.Surjective φ := by
    intro v
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨i, j, hij⟩ := hab g
    have hp0 : 0 < p := hp.out.pos
    refine ⟨(⟨i % p, Nat.mod_lt _ hp0⟩, ⟨j % p, Nat.mod_lt _ hp0⟩), ?_⟩
    simp only [φ]
    rw [hij, ← pow_eq_pow_mod i (hpow _), ← pow_eq_pow_mod j (hpow _)]
  have := Nat.card_le_card_of_surjective φ hsurj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at this
  rwa [sq]

theorem card_frattini_quotient_dvd_sq {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    (h : CFSG.IsMetacyclic G) : Nat.card (G ⧸ frattini G) ∣ p ^ 2 := by
  obtain ⟨N, hN, hNc, hQc⟩ := h
  obtain ⟨⟨a, haN⟩, ha⟩ := hNc.exists_generator
  obtain ⟨bq, hb⟩ := hQc.exists_generator
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective bq
  have hle : Nat.card (G ⧸ frattini G) ≤ p ^ 2 := by
    refine card_frattini_quotient_le_sq hG (a := a) (b := b) fun g => ?_
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr (hb (g : G ⧸ N)))
    have hc : (b ^ j)⁻¹ * g ∈ N := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_pow]
      exact hj
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr (ha ⟨_, hc⟩))
    have hi' : a ^ i = (b ^ j)⁻¹ * g := by
      have := congrArg Subtype.val hi
      simpa using this
    refine ⟨i, j, ?_⟩
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, hi']
    rw [QuotientGroup.eq]
    have hcomm := commutator_le_frattini hG
    have : g⁻¹ * ((b ^ j)⁻¹ * g * b ^ j) = ⁅g⁻¹, (b ^ j)⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [this]
    exact hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  obtain ⟨-, hpow⟩ := frattini_quotient_facts hG
  have hpg : IsPGroup p (G ⧸ frattini G) := hG.to_quotient _
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hpg
  rw [hd] at hle ⊢
  exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.out.one_lt).mp hle)

theorem card_frattini_quotient_dvd_of_isCyclic {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) [hc : IsCyclic G] : Nat.card (G ⧸ frattini G) ∣ p := by
  obtain ⟨-, hpow⟩ := frattini_quotient_facts hG
  obtain ⟨a, ha⟩ := hc.exists_generator
  have hle : Nat.card (G ⧸ frattini G) ≤ p := by
    let φ : Fin p → G ⧸ frattini G := fun i => (a : G ⧸ frattini G) ^ (i : ℕ)
    have hsurj : Function.Surjective φ := by
      intro v
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective v
      obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (ha g))
      refine ⟨⟨i % p, Nat.mod_lt _ hp.out.pos⟩, ?_⟩
      simp only [φ]
      rw [← pow_eq_pow_mod i (hpow _), QuotientGroup.mk_pow]
    have := Nat.card_le_card_of_surjective φ hsurj
    rwa [Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at this
  have hpg : IsPGroup p (G ⧸ frattini G) := hG.to_quotient _
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hpg
  rw [hd] at hle ⊢
  have : d ≤ 1 := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp (by rwa [pow_one])
  exact (pow_dvd_pow p this).trans (by rw [pow_one])

@[expose] noncomputable def frattiniAut (G : Type*) [Group G] : MulAut G →* MulAut (G ⧸ frattini G)
    where
  toFun σ := QuotientGroup.congr (frattini G) (frattini G) σ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance σ)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' σ τ := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

omit hp in
@[simp]
theorem frattiniAut_mk {G : Type*} [Group G] (σ : MulAut G) (x : G) :
    frattiniAut G σ (x : G ⧸ frattini G) = (σ x : G ⧸ frattini G) :=
  QuotientGroup.congr_mk _ _ _ (Subgroup.characteristic_iff_map_eq.mp inferInstance σ) x

theorem actsTrivially_of_frattini {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hG : IsPGroup p G) (hcop : Nat.Coprime (Nat.card A) (Nat.card G))
    (h : ∀ (a : A) (x : G), x⁻¹ * (a • x) ∈ frattini G) : ∀ (a : A) (x : G), a • x = x := by
  have hsolv : Group.IsSolvable G := by
    have := hG.isNilpotent
    infer_instance
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := G) (A := A) hsolv hcop
  have hle : CFSG.commutatorAction A G ≤ frattini G := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨a, x, -, rfl⟩
    exact h a x
  have htop : CFSG.fixedPointSubgroup A G ⊔ frattini G = ⊤ :=
    eq_top_iff.mpr (hsup.symm.le.trans (sup_le_sup_left hle _))
  have hfix := frattini_nongenerating htop
  intro a x
  have hx : x ∈ CFSG.fixedPointSubgroup A G := by rw [hfix]; exact Subgroup.mem_top x
  exact (FixedPoints.mem_subgroup A G x).mp hx a

theorem eq_one_of_frattiniAut_eq_one {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    {τ : MulAut G} (hcop : Nat.Coprime p (orderOf τ)) (h : frattiniAut G τ = 1) : τ = 1 := by
  have hcard : Nat.Coprime (Nat.card (Subgroup.zpowers τ)) (Nat.card G) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
    rw [Nat.card_zpowers, hn]
    exact (Nat.Coprime.pow_left n hcop).symm
  have htriv := actsTrivially_of_frattini (A := Subgroup.zpowers τ) hG hcard (by
    rintro ⟨_, z, rfl⟩ x
    have hz : frattiniAut G (τ ^ z) = 1 := by rw [map_zpow, h, one_zpow]
    rw [← QuotientGroup.eq]
    have := congrArg (fun σ : MulAut (G ⧸ frattini G) => σ (x : G ⧸ frattini G)) hz
    simp only [frattiniAut_mk, MulAut.one_apply] at this
    exact this.symm)
  ext x
  exact htriv ⟨τ, Subgroup.mem_zpowers τ⟩ x

theorem coprime_orderOf_pow_card {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.Coprime p (orderOf (g ^ p ^ Nat.card G)) := by
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.one_lt.ne'
  have hle : p ^ e ≤ Nat.card G := by
    have h1 : p ^ e ∣ Nat.card G := (Dvd.intro m he.symm).trans (orderOf_dvd_natCard g)
    exact Nat.le_of_dvd Nat.card_pos h1
  have hlt : e < Nat.card G := lt_of_lt_of_le (Nat.lt_pow_self hp.out.one_lt) hle
  rw [orderOf_pow' g (pow_ne_zero _ hp.out.ne_zero), he]
  have hgcd : (p ^ e * m).gcd (p ^ Nat.card G) = p ^ e := by
    have hcop : Nat.Coprime m (p ^ Nat.card G) :=
      (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)).symm
    rw [Nat.Coprime.gcd_mul_right_cancel (p ^ e) hcop, Nat.gcd_eq_left (pow_dvd_pow p hlt.le)]
  rw [hgcd, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos e)]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm

theorem pow_card_eq_one_of_isPGroup_elem {G : Type*} [Group G] [Finite G] {g : G} {k : ℕ}
    (hg : g ^ p ^ k = 1) : g ^ p ^ Nat.card G = 1 := by
  have hdvd : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hg
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  have hle : p ^ c ≤ Nat.card G := hc ▸ Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard g)
  have hlt : c < Nat.card G :=
    lt_of_lt_of_le (Nat.lt_pow_self hp.out.one_lt) hle
  exact orderOf_dvd_iff_pow_eq_one.mp (hc ▸ pow_dvd_pow p hlt.le)

theorem exists_pow_eq_one_of_frattiniAut_eq_one {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) {τ : MulAut G} (h : frattiniAut G τ = 1) :
    τ ^ p ^ Nat.card (MulAut G) = 1 :=
  eq_one_of_frattiniAut_eq_one hG (coprime_orderOf_pow_card τ) (by rw [map_pow, h, one_pow])

end CFSG.Walter.Huppert
