module

public import CFSG.Quasithin.MS93.S5BExcl
public import CFSG.Quasithin.MS93.S5BTv

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix Pointwise

namespace S5B

theorem inf_eq_bot_of_ne {F : Type} [Field F] {p₁ p₂ : Submodule F (MSP.V4 F)}
    (hp₁ : MSP.IsPoint p₁) (hp₂ : MSP.IsPoint p₂) (hne : p₁ ≠ p₂) : p₁ ⊓ p₂ = ⊥ := by
  have h1 : Module.finrank F p₁ = 1 := hp₁
  have h2 : Module.finrank F p₂ = 1 := hp₂
  refine Submodule.finrank_eq_zero.1 ?_
  by_contra h0
  have hle₁ := Submodule.finrank_mono (inf_le_left : p₁ ⊓ p₂ ≤ p₁)
  have hle₂ := Submodule.finrank_mono (inf_le_right : p₁ ⊓ p₂ ≤ p₂)
  have heq₁ : p₁ ⊓ p₂ = p₁ := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  have heq₂ : p₁ ⊓ p₂ = p₂ := Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
  exact hne (heq₁.symm.trans heq₂)

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Hyp

theorem relIndex_centralizer_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M) (hE2 : IsPGroup 2 E) (hEO : ¬ E ≤ pCoreOf 2 M) :
    2 ^ k ≤ (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) ∧
      ((Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) ≤ 2 ^ k →
        ∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧
          MSP.fixSp ((E.subgroupOf M).map a) = MSP.perp p) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  set Ē := (E.subgroupOf M).map a with hĒdef
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hĒ : Ē ≠ ⊥ := by
    intro hbot
    apply hEO
    intro e he
    have h1 : a ⟨e, hEM he⟩ = 1 := by
      have : a ⟨e, hEM he⟩ ∈ Ē := ⟨⟨e, hEM he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
      rw [hbot] at this
      exact this
    obtain ⟨n, hn⟩ := hE2 ⟨e, he⟩
    exact mem_pCoreOf_of_ker h hd h1 ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hne : MSP.fixSp Ē ≠ ⊤ := fun htop => hĒ (MSP.fixSp_eq_top_iff.1 htop)
  have hrel := relIndex_centralizer_mul_card h hlift c hEM
  rw [MSP.card_V4, hFq, Module.natCard_eq_pow_finrank (K := F), hFq] at hrel
  set r := (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) with hr
  set d := Module.finrank F ↥(MSP.fixSp Ē) with hdd
  have h4 : Module.finrank F (MSP.V4 F) = 4 := by simp
  have hd3 : d ≤ 3 := by
    by_contra h3
    have hle := Submodule.finrank_le (MSP.fixSp Ē)
    rw [h4] at hle
    exact hne (Submodule.eq_top_of_finrank_eq (by rw [h4]; omega))
  have hk1 : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
  have hpos : 0 < 2 ^ k := by positivity
  constructor
  ·
    have hqd : (2 ^ k) ^ d ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_right hpos hd3
    have h1 : 2 ^ k * (2 ^ k) ^ 3 ≤ r * (2 ^ k) ^ 3 := by
      calc 2 ^ k * (2 ^ k) ^ 3 = (2 ^ k) ^ 4 := by ring
        _ = r * (2 ^ k) ^ d := hrel.symm
        _ ≤ r * (2 ^ k) ^ 3 := Nat.mul_le_mul_left r hqd
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  · intro hle
    have h1 : (2 ^ k) ^ 4 ≤ (2 ^ k) ^ (d + 1) := by
      calc (2 ^ k) ^ 4 = r * (2 ^ k) ^ d := hrel.symm
        _ ≤ 2 ^ k * (2 ^ k) ^ d := Nat.mul_le_mul_right _ hle
        _ = (2 ^ k) ^ (d + 1) := by ring
    have h2 : 4 ≤ d + 1 := (Nat.pow_le_pow_iff_right hk1).1 h1
    refine ⟨MSP.perp (MSP.fixSp Ē), ?_, (MSP.perp_perp _).symm⟩
    have := MSP.finrank_perp (MSP.fixSp Ē)
    change Module.finrank F _ = 1
    omega

theorem commutator_eq_one_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E₁ E₂ : Subgroup G} (hE₁M : E₁ ≤ M) (hE₂M : E₂ ≤ M) (hE₁2 : IsPGroup 2 E₁)
    (hE₂2 : IsPGroup 2 E₂) (hE₁O : ¬ E₁ ≤ pCoreOf 2 M) (hE₂O : ¬ E₂ ≤ pCoreOf 2 M)
    (hrel₁ : (Subgroup.centralizer (E₁ : Set G)).relIndex (Uq M T L) ≤ 2 ^ k)
    (hrel₂ : (Subgroup.centralizer (E₂ : Set G)).relIndex (Uq M T L) ≤ 2 ^ k)
    {u e : G} (hu : u ∈ Uq M T L ⊓ Subgroup.centralizer (E₁ : Set G)) (he : e ∈ E₂)
    (hc : e * u * e⁻¹ * u⁻¹ ∈ ⁅E₁, Uq M T L⁆ ⊔ (M ⊓ Subgroup.centralizer (M : Set G))) :
    e * u * e⁻¹ = u := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  obtain ⟨p₁, hp₁, hfix₁⟩ := (relIndex_centralizer_M h hd hE₁M hE₁2 hE₁O).2 hrel₁
  obtain ⟨p₂, hp₂, hfix₂⟩ := (relIndex_centralizer_M h hd hE₂M hE₂2 hE₂O).2 hrel₂
  have hcomm : ∀ {E : Subgroup G} {p : Submodule F (MSP.V4 F)},
      MSP.fixSp ((E.subgroupOf M).map a) = MSP.perp p →
        MSP.commSp ((E.subgroupOf M).map a) ≤ p := by
    intro E p hfix
    refine (MSP.commSp_mono ?_).trans (MSP.commSp_fixer_perp_le p)
    rw [← hfix]
    exact MSP.le_fixer_iff.2 le_rfl
  have heu : e * u * e⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn (hE₂M he)) u).1 hu.1
  set w : ↥(Uq M T L) := ⟨e * u * e⁻¹ * u⁻¹, mul_mem heu (inv_mem hu.1)⟩ with hw
  have hemem : a ⟨e, hE₂M he⟩ ∈ (E₂.subgroupOf M).map a :=
    ⟨⟨e, hE₂M he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
  have hv₂ : c.vec w ∈ p₂ := by
    rw [hw, c.vec_commutator ⟨e, hE₂M he⟩ ⟨u, hu.1⟩ heu]
    exact hcomm hfix₂ (MSP.sub_mem_commSp hemem _)
  have hv₁ : c.vec w ∈ p₁ := by
    have hZn : M ⊓ Subgroup.centralizer (M : Set G) ≤
        Subgroup.normalizer ((⁅E₁, Uq M T L⁆ : Subgroup G) : Set G) := by
      refine le_normalizer_of_map_conj_le fun z hz => ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxM : x ∈ M := commutator_le_of_le hE₁M (Uq_le h.L_le) hx
      have hzx : x * z = z * x := Subgroup.mem_centralizer_iff.1 hz.2 x hxM
      change z * x * z⁻¹ ∈ _
      rw [← hzx, mul_inv_cancel_right]
      exact hx
    rw [sup_comm] at hc
    have hc' : e * u * e⁻¹ * u⁻¹ ∈ ((M ⊓ Subgroup.centralizer (M : Set G) : Subgroup G) : Set G) *
        ((⁅E₁, Uq M T L⁆ : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZn]
      exact hc
    obtain ⟨z, hz, r, hr, hzr⟩ := hc'
    have hrU : r ∈ Uq M T L := commutator_le_left_of_le_normalizer (hE₁M.trans hUn)
      (by rw [Subgroup.commutator_comm]; exact hr)
    have hzU : z ∈ Uq M T L := by
      have : z = (e * u * e⁻¹ * u⁻¹) * r⁻¹ := by rw [← hzr]; group
      rw [this]
      exact mul_mem (mul_mem heu (inv_mem hu.1)) (inv_mem hrU)
    have hw' : w = ⟨z, hzU⟩ * ⟨r, hrU⟩ := Subtype.ext hzr.symm
    rw [hw', c.vec_mul, (c.vec_eq_zero_iff ⟨z, hzU⟩).2
      ⟨hzU, Subgroup.centralizer_le h.L_le hz.2⟩, zero_add]
    refine hcomm hfix₁ (vec_mem_commSp h c hE₁M ⟨r, hrU⟩ ?_)
    rw [Subgroup.commutator_comm]
    exact hr
  have hvu : c.vec ⟨u, hu.1⟩ ∈ MSP.perp p₁ :=
    hfix₁ ▸ (mem_centralizer_iff_vec h hlift c hE₁M ⟨u, hu.1⟩).1 hu.2
  have h0 : c.vec w = 0 := by
    by_cases hpp : p₁ = p₂
    · rw [hw, c.vec_commutator ⟨e, hE₂M he⟩ ⟨u, hu.1⟩ heu, sub_eq_zero]
      have hfix : c.vec ⟨u, hu.1⟩ ∈ MSP.fixSp ((E₂.subgroupOf M).map a) := by
        rw [hfix₂, ← hpp]
        exact hvu
      exact MSP.mem_fixSp.1 hfix _ hemem
    · have hmem : c.vec w ∈ p₁ ⊓ p₂ := ⟨hv₁, hv₂⟩
      rw [inf_eq_bot_of_ne hp₁ hp₂ hpp] at hmem
      exact (Submodule.mem_bot F).1 hmem
  exact hlift e (hE₂M he) u hu.1 ((c.vec_eq_zero_iff w).1 h0).2

end Hyp

section Vertex

theorem uSub_inf_centralizer_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    {E₀ : Subgroup G} (hE₀M : E₀ ≤ M) :
    S5.uSub h.le L (g • baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (((imM h.le E₀).map (MulAut.conj g).toMonoidHom : Subgroup _) : Set _) =
      (imM h.le (Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G))).map
        (MulAut.conj g).toMonoidHom := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  rw [uSub_smul h.le hLn, uSub_baseA h, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← imM_inf_centralizer h.le _ hE₀M]

theorem relIndex_centralizer_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    {E₀ : Subgroup G} (hE₀M : E₀ ≤ M) :
    (Subgroup.centralizer (((imM h.le E₀).map (MulAut.conj g).toMonoidHom : Subgroup _) :
        Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L (g • baseA (puAmalgam h.le))) =
      (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  rw [uSub_smul h.le hLn, uSub_baseA h, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₀M]

theorem isPGroup_not_le_of_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    {E₀ : Subgroup G} (hE₀M : E₀ ≤ M)
    (hE2 : IsPGroup 2 ((imM h.le E₀).map (MulAut.conj g).toMonoidHom))
    (hEQ : ¬ (imM h.le E₀).map (MulAut.conj g).toMonoidHom ≤ Qv _ (g • baseA (puAmalgam h.le))) :
    IsPGroup 2 E₀ ∧ ¬ E₀ ≤ pCoreOf 2 M := by
  refine ⟨?_, fun hle => hEQ ?_⟩
  · have e1 : ↥E₀ ≃* ↥(imM h.le E₀) := by
      refine (Subgroup.subgroupOfEquivOfLe hE₀M).symm.trans ?_
      exact Subgroup.equivMapOfInjective _ _ (puAmalgam h.le).ofA_injective
    have e2 : ↥(imM h.le E₀) ≃* ↥((imM h.le E₀).map (MulAut.conj g).toMonoidHom) :=
      Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective
    exact hE2.of_equiv (e1.trans e2).symm
  · rw [qv_smul, map_conj_le_map_conj_iff, qv_baseA_eq h]
    exact imM_mono h.le hle

theorem le_relIndex_centralizer (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ) (hE2 : IsPGroup 2 E) (hEQ : ¬ E ≤ Qv _ δ) :
    2 ^ k ≤ (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := exists_eq_map_imM h.le g hE
  obtain ⟨hE₀2, hE₀O⟩ := isPGroup_not_le_of_smul h g hE₀M hE2 hEQ
  rw [relIndex_centralizer_smul h g hE₀M]
  exact (relIndex_centralizer_M h hd hE₀M hE₀2 hE₀O).1

theorem stabCenter_le_inf {A B : Type} {C : Type} [Group A] [Group C] [Group B]
    {X : GoldAmalgam A C B} (δ : Vtx X) :
    stabCenter X δ ≤ stab X δ ⊓ Subgroup.centralizer (stab X δ : Set X.Universal) := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y.2, Subgroup.mem_centralizer_iff.2 fun x hx =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨x, hx⟩)⟩

theorem commutator_eq_one (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) {E₁ E₂ : Subgroup (puAmalgam h.le).Universal}
    (hE₁ : E₁ ≤ stab _ ρ) (hE₂ : E₂ ≤ stab _ ρ) (hE₁2 : IsPGroup 2 E₁) (hE₂2 : IsPGroup 2 E₂)
    (hE₁Q : ¬ E₁ ≤ Qv _ ρ) (hE₂Q : ¬ E₂ ≤ Qv _ ρ)
    (hrel₁ : (Subgroup.centralizer (E₁ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L ρ) ≤ 2 ^ k)
    (hrel₂ : (Subgroup.centralizer (E₂ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L ρ) ≤ 2 ^ k)
    {u e : (puAmalgam h.le).Universal}
    (hu : u ∈ S5.uSub h.le L ρ ⊓ Subgroup.centralizer (E₁ : Set (puAmalgam h.le).Universal))
    (he : e ∈ E₂) (hc : ⁅e, u⁆ ∈ ⁅E₁, S5.uSub h.le L ρ⁆ ⊔
      (stab _ ρ ⊓ Subgroup.centralizer (stab _ ρ : Set (puAmalgam h.le).Universal))) :
    ⁅e, u⁆ = 1 := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hρ
  obtain ⟨E₁₀, hE₁₀M, rfl⟩ := exists_eq_map_imM h.le g hE₁
  obtain ⟨E₂₀, hE₂₀M, rfl⟩ := exists_eq_map_imM h.le g hE₂
  obtain ⟨hE₁₀2, hE₁₀O⟩ := isPGroup_not_le_of_smul h g hE₁₀M hE₁2 hE₁Q
  obtain ⟨hE₂₀2, hE₂₀O⟩ := isPGroup_not_le_of_smul h g hE₂₀M hE₂2 hE₂Q
  rw [relIndex_centralizer_smul h g hE₁₀M] at hrel₁
  rw [relIndex_centralizer_smul h g hE₂₀M] at hrel₂
  rw [uSub_inf_centralizer_smul h g hE₁₀M] at hu
  have hK : ⁅(imM h.le E₁₀).map (MulAut.conj g).toMonoidHom,
      S5.uSub h.le L (g • baseA (puAmalgam h.le))⁆ ⊔
      (stab _ (g • baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (stab _ (g • baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal)) =
      (imM h.le (⁅E₁₀, Uq M T L⁆ ⊔ (M ⊓ Subgroup.centralizer (M : Set G)))).map
        (MulAut.conj g).toMonoidHom := by
    rw [uSub_smul h.le hLn, uSub_baseA h, ← Subgroup.map_commutator,
      ← imM_commutator h.le hE₁₀M (Uq_le h.L_le), stab_smul, PU.centralizer_map_mulEquiv,
      ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, puAmalgam.stab_baseA,
      ← imM_inf_centralizer h.le M le_rfl, ← Subgroup.map_sup,
      imM_sup_of_le h.le (commutator_le_of_le hE₁₀M (Uq_le h.L_le)) inf_le_left]
  rw [hK] at hc
  obtain ⟨_, ⟨u₀, hu₀, rfl⟩, rfl⟩ := hu
  obtain ⟨_, ⟨e₀, he₀, rfl⟩, rfl⟩ := he
  rw [← map_commutatorElement, ← map_commutatorElement] at hc ⊢
  obtain ⟨_, ⟨y, hy, rfl⟩, hyeq⟩ := hc
  have hy' : y = ⁅e₀, u₀⁆ :=
    (puAmalgam h.le).ofA_injective ((MulAut.conj g).injective hyeq)
  rw [hy'] at hy
  have key := commutator_eq_one_M h hd hE₁₀M hE₂₀M hE₁₀2 hE₂₀2 hE₁₀O hE₂₀O hrel₁ hrel₂
    (Subgroup.mem_subgroupOf.1 hu₀) (Subgroup.mem_subgroupOf.1 he₀)
    (by simpa [commutatorElement_def] using Subgroup.mem_subgroupOf.1 hy)
  have h1 : ⁅e₀, u₀⁆ = 1 := by
    apply Subtype.ext
    rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_inv, key, mul_inv_cancel, Subgroup.coe_one]
  rw [h1, map_one, map_one]

end Vertex

end S5B

end CFSG.Quasithin.MS93
