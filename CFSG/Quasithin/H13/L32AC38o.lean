module

public import CFSG.Quasithin.EmptyFaithful.S153EB6B
public import CFSG.Quasithin.H13.L32AC38d
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

theorem exists_fix3_of_realizes {W : Type} [CommGroup W] {D : FFModel} (hD : D.Faithful)
    {K : Subgroup (MulAut W)} {U : Subgroup W} {π : D.Gam →* ↥K}
    (h : D.RealizesVia K U ⊥ π)
    (hfix : ∀ m ∈ D.sec, ∃ γ : D.Gam, γ ^ 3 = 1 ∧ γ ≠ 1 ∧ D.act γ m * m⁻¹ ∈ D.ker) :
    ∀ u ∈ U, ∃ e ∈ K, e ^ 3 = 1 ∧ e ≠ 1 ∧ e u = u := by
  have hπi := FFC.injective_of_faithful_sec hD h
  obtain ⟨-, -, -, hKU, -, hsec, -, β, -, hβk, hβe⟩ := h
  intro u hu
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, hu⟩)
  obtain ⟨γ, hγ3, hγ1, hγm⟩ := hfix m m.2
  refine ⟨((π γ : ↥K) : MulAut W), (π γ).2, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, hγ3, map_one, Subgroup.coe_one]
  · intro h1
    apply hγ1
    apply hπi
    rw [map_one]
    exact Subtype.ext h1
  · have hu' : ((π γ : ↥K) : MulAut W) u ∈ U := hKU (π γ) u hu
    have hact : D.act γ (m : D.Amb) ∈ D.sec := hsec γ m m.2
    have h1 := hβe γ ⟨u, hu⟩ m hu' hact hm.symm
    have h2 : (QuotientGroup.mk ⟨D.act γ (m : D.Amb), hact⟩ :
        ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk m := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h := D.ker.inv_mem hγm
      rw [mul_inv_rev, inv_inv, mul_comm] at h
      exact h
    rw [h2, hm] at h1
    have h3 : β (⟨_, hu'⟩ * (⟨u, hu⟩ : ↥U)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h4 := (hβk _).mp h3
    rw [Subgroup.mem_bot] at h4
    have h5 : ((π γ : ↥K) : MulAut W) u * u⁻¹ = 1 := h4
    exact mul_inv_eq_one.mp h5

theorem isSolvable_of_binaryNaturalSL_two {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    {U : Subgroup W} (h : BinaryNaturalSL K U ⊥ 2 1) : Group.IsSolvable ↥K := by
  obtain ⟨K₂, _, _, hK2, π₀, hπ⟩ := h
  have hsl : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 1) (b := 1)
      Nat.prime_two Nat.prime_three (by norm_num) (by decide)
  have : Group.IsSolvable ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K₂) :=
    Group.isSolvable_of_isSolvable_injective (f := (statedSLEquivZModTwo (n := 2) hK2).toMonoidHom)
      (statedSLEquivZModTwo hK2).injective
  have : Group.IsSolvable (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 K₂)).Gam := this
  exact Group.isSolvable_of_surjective hπ.1

theorem isSolvable_sup_zpowers {X : Type*} [Group X] {G' K₀ K₁ : Subgroup X} {t : X}
    (h0 : Group.IsSolvable ↥K₀) (h1 : Group.IsSolvable ↥K₁)
    (hc : ∀ x ∈ K₀, ∀ y ∈ K₁, x * y = y * x) (htG : t ∈ G') (hKG : K₀ ⊔ K₁ ≤ G')
    (hG : G' = (K₀ ⊔ K₁) ⊔ Subgroup.zpowers t)
    (hn : G' ≤ Subgroup.normalizer ((K₀ ⊔ K₁ : Subgroup X) : Set X)) :
    Group.IsSolvable ↥G' := by
  have hcomm : ∀ (a : ↥K₀) (b : ↥K₁), Commute (K₀.subtype a) (K₁.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hfr : (MonoidHom.noncommCoprod K₀.subtype K₁.subtype hcomm).range = K₀ ⊔ K₁ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hK : Group.IsSolvable ↥(K₀ ⊔ K₁) := by
    have : Group.IsSolvable ↥(MonoidHom.noncommCoprod K₀.subtype K₁.subtype hcomm).range :=
      Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective _)
    rw [hfr] at this
    exact this
  have hnorm : ((K₀ ⊔ K₁).subgroupOf G').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mpr hn
  have hcyc : IsCyclic (↥G' ⧸ (K₀ ⊔ K₁).subgroupOf G') := by
    refine ⟨⟨QuotientGroup.mk ⟨t, htG⟩, fun q => ?_⟩⟩
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hg' : g ∈ (K₀ ⊔ K₁) ⊔ Subgroup.zpowers t := hG ▸ hg
    have hZ : Subgroup.zpowers t ≤ Subgroup.normalizer ((K₀ ⊔ K₁ : Subgroup X) : Set X) :=
      Subgroup.zpowers_le.mpr (hn htG)
    obtain ⟨k, hk, z, hz, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZ).mp hg'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨m, ?_⟩
    show (QuotientGroup.mk ⟨t, htG⟩ : ↥G' ⧸ (K₀ ⊔ K₁).subgroupOf G') ^ m = QuotientGroup.mk ⟨_, hg⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (((⟨t, htG⟩ : ↥G') ^ m)⁻¹ * ⟨k * t ^ m, hg⟩ : ↥G') = (t ^ m)⁻¹ * k * t ^ m := by
      simp [mul_assoc]
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp (hZ (inv_mem (Subgroup.zpow_mem_zpowers t m))) k).mp
      hk
    simpa [mul_assoc] using this
  have hQ : Group.IsSolvable (↥G' ⧸ (K₀ ⊔ K₁).subgroupOf G') :=
    Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b
  exact Group.isSolvable_of_ker_le_range (Subgroup.inclusion hKG)
    (QuotientGroup.mk' ((K₀ ⊔ K₁).subgroupOf G')) (by
      intro g hg
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at hg
      exact ⟨⟨g, hg⟩, rfl⟩)

theorem exists_fix3_nat {W : Type} [CommGroup W] {K : Subgroup (MulAut W)} {U : Subgroup W}
    {n : ℕ} (hn : 3 ≤ n) (h : BinaryNaturalSL K U ⊥ n 1) :
    ∀ u ∈ U, ∃ e ∈ K, e ^ 3 = 1 ∧ e ≠ 1 ∧ e u = u := by
  obtain ⟨K₂, _, _, hK2, π₀, hπ⟩ := h
  refine exists_fix3_of_realizes (FFModel.nat_faithful _) hπ ?_
  intro (m : Multiplicative (Fin n → K₂)) _
  obtain ⟨γ, hγ3, hγm, m', hm'⟩ := S153EB6.natSL_fix (by simpa using hK2) n hn m
  have hγ1 : γ ≠ 1 := fun h1 => hm' (by rw [h1]; simp [natAct])
  refine ⟨γ, hγ3, hγ1, ?_⟩
  show natAct _ γ m * m⁻¹ ∈ (⊥ : Subgroup (Multiplicative (Fin n → K₂)))
  rw [hγm, mul_inv_cancel]
  exact one_mem _

theorem exists_fix3_perm {W : Type} [CommGroup W] {K : Subgroup (MulAut W)} {U : Subgroup W}
    {n : ℕ} (hn : 5 ≤ n) {Z : Subgroup (G6.PermMod n)} (hD : (G64.permModel n Z).Faithful)
    {π₀ : Equiv.Perm (Fin n) →* ↥K} (hπ : (G64.permModel n Z).RealizesVia K U ⊥ π₀) :
    ∀ u ∈ U, ∃ e ∈ K, e ^ 3 = 1 ∧ e ≠ 1 ∧ e u = u := by
  refine exists_fix3_of_realizes hD hπ ?_
  intro (m : G6.PermMod n) _
  obtain ⟨γ, hγ3, hγm, m', -, hm'⟩ := S153EB6.perm_cyc n hn m
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    apply hm'
    refine Subgroup.mem_zpowers_iff.mpr ⟨0, ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    simp only [zpow_zero, toAdd_one, Pi.zero_apply, toAdd_mul, toAdd_inv, Pi.add_apply,
      Pi.neg_apply, G6.permAct_apply, inv_one, Equiv.Perm.coe_one, id_eq]
    exact (add_neg_cancel _).symm
  refine ⟨γ, hγ3, hγ1, ?_⟩
  show G6.permAct n γ m * m⁻¹ ∈ Z
  rw [hγm, mul_inv_cancel]
  exact one_mem _

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Ctx38

variable {b c : G} (C : Ctx38 T L V H b c)
include C

theorem false_of_isSolvable_range (h29 : Thm14_7_29)
    (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H)) (hs : Group.IsSolvable ↥C.ψ.range) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker2 : IsPGroup 2 ↥C.ψ.ker := by
    rintro ⟨k, hk⟩
    have hkQ : (k : G) ∈ pCoreOf 2 H := C.mem_pCoreOf_of_ψ hW k.2 hk
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hkQ⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hm
    simpa using this
  have : Group.IsNilpotent ↥C.ψ.ker := hker2.isNilpotent
  have : Group.IsSolvable ↥C.ψ.ker := inferInstance
  have hsolv : Group.IsSolvable ↥H :=
    Group.isSolvable_of_ker_le_range C.ψ.ker.subtype C.ψ.rangeRestrict (by
      rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  exact C.S.hz.2.2 (h29 G T L V C.S.hyp H C.S.hz.1.1 C.S.hz.2.1 hsolv)

theorem fix3_or_solvable {K₀ : Subgroup (MulAut (IntMod C.Wt C.hUe))}
    (h : G64.ModuleType K₀ (commV K₀)) :
    Group.IsSolvable ↥K₀ ∨
      ∀ u ∈ commV K₀, ∃ e ∈ K₀, e ^ 3 = 1 ∧ e ≠ 1 ∧ e u = u := by
  rcases h with ⟨n, hn2, -, hnat⟩ | ⟨n, hn5, -, hsym⟩ | ⟨n, hn, hcore⟩
  · rcases Nat.lt_or_ge n 3 with hlt | hge
    · left
      have : n = 2 := by omega
      subst this
      exact isSolvable_of_binaryNaturalSL_two hnat
    · exact Or.inr (exists_fix3_nat hge hnat)
  · obtain ⟨π₀, hπ⟩ := hsym
    exact Or.inr (exists_fix3_perm hn5 (G64.symDn_faithful hn5) hπ)
  · obtain ⟨π₀, hπ⟩ := hcore
    have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
    exact Or.inr (exists_fix3_perm hn5 (G64.symCore_faithful (by omega)) hπ)

end Ctx38

end CFSG.Quasithin.H13.L32A.C
