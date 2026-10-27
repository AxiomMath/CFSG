module

public import CFSG.Quasithin.MS93.S5BNat
public import CFSG.Quasithin.MS93.S5BEqv
public import CFSG.Quasithin.MS93.M15Lift

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S5B

section NatM

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Fintype F] in
theorem vec_mem_commSp (h : PUHyp M T L)
    (c : MSP.NatCoord M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) a)
    {E : Subgroup G} (hEM : E ≤ M) (u : ↥(Uq M T L)) (hu : (u : G) ∈ ⁅Uq M T L, E⁆) :
    c.vec u ∈ MSP.commSp ((E.subgroupOf M).map a) := by
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  let P : Subgroup ↥(Uq M T L) :=
    (AddSubgroup.toSubgroup (MSP.commSp ((E.subgroupOf M).map a)).toAddSubgroup).comap c.toVec
  have hP : ∀ v : ↥(Uq M T L), v ∈ P ↔ c.vec v ∈ MSP.commSp ((E.subgroupOf M).map a) :=
    fun _ => Iff.rfl
  have hle : ⁅Uq M T L, E⁆ ≤ P.map (Uq M T L).subtype := by
    rw [Subgroup.commutator_le]
    intro v hv e he
    have hev : e * v * e⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn (hEM he)) v).1 hv
    refine ⟨⟨v, hv⟩ * (⟨e * v * e⁻¹, hev⟩ : ↥(Uq M T L))⁻¹, ?_, ?_⟩
    · show _ ∈ P
      rw [hP, c.vec_mul, c.vec_inv]
      have h1 := c.vec_conj ⟨e, hEM he⟩ ⟨v, hv⟩ hev
      rw [h1, ← sub_eq_add_neg]
      have h2 := MSP.sub_mem_commSp (A := (E.subgroupOf M).map a)
        (Subgroup.mem_map_of_mem a (show (⟨e, hEM he⟩ : ↥M) ∈ E.subgroupOf M from he))
        (c.vec ⟨v, hv⟩)
      have h3 := neg_mem h2
      rwa [neg_sub] at h3
    · simp [commutatorElement_def, mul_assoc]
  obtain ⟨v, hv, hvu⟩ := hle hu
  have : v = u := Subtype.ext hvu
  rw [← this]
  exact hv

omit [Fintype F] in
theorem exists_mem_commutator_vec_eq (h : PUHyp M T L)
    (c : MSP.NatCoord M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) a)
    {E : Subgroup G} {w : MSP.V4 F} (hw : w ∈ MSP.commSp ((E.subgroupOf M).map a)) :
    ∃ u : ↥(Uq M T L), (u : G) ∈ ⁅Uq M T L, E⁆ ∧ c.vec u = w := by
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  obtain ⟨u, hu, rfl⟩ := (c.mem_commSp_iff hUn _ w).1 hw
  refine ⟨u, ?_, rfl⟩
  clear hw
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, hxv⟩ := hx
    rw [hxv, ← commutatorElement_def, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hb) v.2
  | one => exact one_mem _
  | mul x y _ _ hx hy => exact mul_mem hx hy
  | inv x _ hx => exact inv_mem hx

omit [Fintype F] in
theorem commSp_eq_of_commutator_eq (h : PUHyp M T L)
    (c : MSP.NatCoord M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) a)
    {E E' : Subgroup G} (hEM : E ≤ M) (hE'M : E' ≤ M) (heq : ⁅Uq M T L, E⁆ = ⁅Uq M T L, E'⁆) :
    MSP.commSp ((E.subgroupOf M).map a) = MSP.commSp ((E'.subgroupOf M).map a) := by
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := exists_mem_commutator_vec_eq h c hw
    exact vec_mem_commSp h c hE'M u (heq ▸ hu)
  · intro hw
    obtain ⟨u, hu, rfl⟩ := exists_mem_commutator_vec_eq h c hw
    exact vec_mem_commSp h c hEM u (heq ▸ hu)

theorem uq_inf_centralizer_eq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E E' : Subgroup G} (hEM : E ≤ M) (hE'M : E' ≤ M) (heq : ⁅Uq M T L, E⁆ = ⁅Uq M T L, E'⁆) :
    Uq M T L ⊓ Subgroup.centralizer (E : Set G) = Uq M T L ⊓ Subgroup.centralizer (E' : Set G) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hfix : MSP.fixSp ((E.subgroupOf M).map a) = MSP.fixSp ((E'.subgroupOf M).map a) := by
    rw [fixSp_eq_perp_commSp, fixSp_eq_perp_commSp, commSp_eq_of_commutator_eq h c hEM hE'M heq]
  ext u
  constructor
  · rintro ⟨hu, huE⟩
    refine ⟨hu, ?_⟩
    have := (mem_centralizer_iff_vec h hlift c hEM ⟨u, hu⟩).1 huE
    rw [hfix] at this
    exact (mem_centralizer_iff_vec h hlift c hE'M ⟨u, hu⟩).2 this
  · rintro ⟨hu, huE⟩
    refine ⟨hu, ?_⟩
    have := (mem_centralizer_iff_vec h hlift c hE'M ⟨u, hu⟩).1 huE
    rw [← hfix] at this
    exact (mem_centralizer_iff_vec h hlift c hEM ⟨u, hu⟩).2 this

theorem tv_card_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M) (hE2 : IsPGroup 2 E) (hEO : ¬ E ≤ pCoreOf 2 M)
    (hcard : Nat.card ↥⁅Uq M T L, E⁆ ≤ 2 ^ k) :
    2 ^ k ≤ Nat.card ↥⁅Uq M T L, E⁆ ∧
      (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  obtain ⟨p, hp, hcomm, -, -, hrel⟩ := exists_point_of_card_commutator_le h hd hlift hEM hE2 hEO hcard
  refine ⟨?_, hrel⟩
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hpc : Nat.card p = 2 ^ k := by
    rw [Module.natCard_eq_pow_finrank (K := F), show Module.finrank F p = 1 from hp, pow_one, hFq]
  have hsub : ((p : Submodule F (MSP.V4 F)) : Set (MSP.V4 F)) ⊆
      Set.range (fun x : ↥⁅Uq M T L, E⁆ =>
        c.vec ⟨x, commutator_le_left_of_le_normalizer
          (hEM.trans (le_normalizer_Uq h.le_normalizer)) x.2⟩) := by
    intro w hw
    rw [← hcomm] at hw
    obtain ⟨u, hu, rfl⟩ := exists_mem_commutator_vec_eq h c hw
    exact ⟨⟨u, hu⟩, rfl⟩
  calc 2 ^ k = Nat.card p := hpc.symm
    _ ≤ Nat.card (Set.range (fun x : ↥⁅Uq M T L, E⁆ =>
        c.vec ⟨x, commutator_le_left_of_le_normalizer
          (hEM.trans (le_normalizer_Uq h.le_normalizer)) x.2⟩)) :=
        Nat.card_mono (Set.finite_range _) hsub
    _ ≤ Nat.card ↥⁅Uq M T L, E⁆ := Finite.card_range_le _

end NatM

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] in
theorem exists_eq_map_imM (hTM : T ≤ M) (g : (puAmalgam hTM).Universal)
    {E : Subgroup (puAmalgam hTM).Universal} (hE : E ≤ stab _ (g • baseA (puAmalgam hTM))) :
    ∃ E₀ : Subgroup G, E₀ ≤ M ∧ E = (imM hTM E₀).map (MulAut.conj g).toMonoidHom := by
  have hE' : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ imM hTM M := by
    rw [← puAmalgam.stab_baseA, map_conj_le_iff, inv_inv, ← stab_smul]
    exact hE
  obtain ⟨E₀, -, hE₀M, he⟩ := exists_eq_imM hTM hE'
  refine ⟨E₀, hE₀M, ?_⟩
  rw [← he, map_conj_map_conj_inv]

theorem tv_card (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {δ : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ stab _ δ)
    (hE2 : IsPGroup 2 E) (hEQ : ¬ E ≤ Qv _ δ)
    (hcard : Nat.card ↥⁅S5.uSub h.le L δ, E⁆ ≤ 2 ^ k) :
    2 ^ k ≤ Nat.card ↥⁅S5.uSub h.le L δ, E⁆ ∧
      (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L δ) = 2 ^ k := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := exists_eq_map_imM h.le g hE
  have hU : S5.uSub h.le L (g • baseA (puAmalgam h.le)) =
      (imM h.le (Uq M T L)).map (MulAut.conj g).toMonoidHom := by
    rw [uSub_smul h.le hLn, uSub_baseA h]
  have hcomm : ⁅S5.uSub h.le L (g • baseA (puAmalgam h.le)),
      (imM h.le E₀).map (MulAut.conj g).toMonoidHom⁆ =
      (imM h.le ⁅Uq M T L, E₀⁆).map (MulAut.conj g).toMonoidHom := by
    rw [hU, ← Subgroup.map_commutator, imM_commutator h.le (Uq_le h.L_le) hE₀M]
  have hcardeq : Nat.card ↥⁅S5.uSub h.le L (g • baseA (puAmalgam h.le)),
      (imM h.le E₀).map (MulAut.conj g).toMonoidHom⁆ = Nat.card ↥⁅Uq M T L, E₀⁆ := by
    rw [hcomm, card_map_conj, card_imM h.le (commutator_le_of_le (Uq_le h.L_le) hE₀M)]
  have hrel : (Subgroup.centralizer (((imM h.le E₀).map (MulAut.conj g).toMonoidHom :
      Subgroup _) : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L (g • baseA (puAmalgam h.le))) =
      (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) := by
    rw [hU, PU.centralizer_map_mulEquiv,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
      relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₀M]
  have hE₀2 : IsPGroup 2 E₀ := by
    have e1 : ↥E₀ ≃* ↥(imM h.le E₀) := by
      refine (Subgroup.subgroupOfEquivOfLe hE₀M).symm.trans ?_
      exact Subgroup.equivMapOfInjective _ _ (puAmalgam h.le).ofA_injective
    have e2 : ↥(imM h.le E₀) ≃* ↥((imM h.le E₀).map (MulAut.conj g).toMonoidHom) :=
      Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective
    exact hE2.of_equiv (e1.trans e2).symm
  have hE₀O : ¬ E₀ ≤ pCoreOf 2 M := by
    intro hle
    apply hEQ
    rw [qv_smul, map_conj_le_map_conj_iff, qv_baseA_eq h]
    exact imM_mono h.le hle
  rw [hcardeq] at hcard ⊢
  rw [hrel]
  exact tv_card_M h hd hE₀M hE₀2 hE₀O hcard

theorem uSub_inf_centralizer_eq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E E' : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ) (hE' : E' ≤ stab _ δ)
    (heq : ⁅S5.uSub h.le L δ, E⁆ = ⁅S5.uSub h.le L δ, E'⁆) :
    S5.uSub h.le L δ ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) =
      S5.uSub h.le L δ ⊓ Subgroup.centralizer (E' : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := exists_eq_map_imM h.le g hE
  obtain ⟨E₁, hE₁M, rfl⟩ := exists_eq_map_imM h.le g hE'
  have hU : S5.uSub h.le L (g • baseA (puAmalgam h.le)) =
      (imM h.le (Uq M T L)).map (MulAut.conj g).toMonoidHom := by
    rw [uSub_smul h.le hLn, uSub_baseA h]
  rw [hU, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
    ← imM_commutator h.le (Uq_le h.L_le) hE₀M, ← imM_commutator h.le (Uq_le h.L_le) hE₁M] at heq
  have heq' : ⁅Uq M T L, E₀⁆ = ⁅Uq M T L, E₁⁆ := by
    have h1 := Subgroup.map_injective (MulAut.conj g).injective heq
    exact le_antisymm
      ((imM_le_imM_iff h.le (commutator_le_of_le (Uq_le h.L_le) hE₀M)).1 h1.le)
      ((imM_le_imM_iff h.le (commutator_le_of_le (Uq_le h.L_le) hE₁M)).1 h1.ge)
  have key := uq_inf_centralizer_eq h hd hE₀M hE₁M heq'
  rw [hU, PU.centralizer_map_mulEquiv, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← imM_inf_centralizer h.le _ hE₀M, ← imM_inf_centralizer h.le _ hE₁M, key]

end Vertex

end S5B

end CFSG.Quasithin.MS93
