module

public import CFSG.Quasithin.MS93.M15Lift
public import CFSG.Quasithin.MS93.S5BEqv
public import CFSG.Quasithin.MS93.S5BNat

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S5B

section Sp4

variable {F : Type} [Field F]

@[expose] def fixVec (g : MSP.Sp4 F) : Submodule F (MSP.V4 F) :=
  LinearMap.ker (Matrix.mulVecLin (MSP.mat g) - LinearMap.id)

theorem mem_fixVec {g : MSP.Sp4 F} {v : MSP.V4 F} : v ∈ fixVec g ↔ MSP.mat g *ᵥ v = v := by
  rw [fixVec, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem eq_one_of_fixVec_eq_top {g : MSP.Sp4 F} (hg : fixVec g = ⊤) : g = 1 :=
  MSP.ext_mulVec fun v => by
    rw [MSP.mat_one, Matrix.one_mulVec]
    exact mem_fixVec.1 (hg ▸ Submodule.mem_top)

theorem eq_top_of_perp_lt {p W : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    (hW : MSP.perp p < W) : W = ⊤ := by
  have h4 : Module.finrank F (MSP.V4 F) = 4 := by simp
  have h3 := MSP.finrank_perp p
  have hp1 : Module.finrank F p = 1 := hp
  have hlt := Submodule.finrank_lt_finrank_of_lt hW
  have hle := Submodule.finrank_le W
  exact Submodule.eq_top_of_finrank_eq (by omega)

theorem le_of_mem_xPoint_stab {p l : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    (hl : MSP.IsLine l) {g : MSP.Sp4 F} (hgx : g ∈ MSP.xPoint p) (hgl : g ∈ MSP.stab l)
    (hg1 : g ≠ 1) : p ≤ l := by
  by_contra hpl
  have hl' : ¬ l ≤ MSP.perp p := by
    intro hle
    apply hpl
    have := MSP.perp_antitone hle
    rwa [MSP.perp_perp, hl.perp_eq] at this
  obtain ⟨v, hvl, hvp⟩ := Set.not_subset.1 hl'
  have h1 : MSP.mat g *ᵥ v - v ∈ p := MSP.sub_mem_of_mem_fixer_perp hgx v
  have h2 : MSP.mat g *ᵥ v - v ∈ l := sub_mem (MSP.mulVec_mem_of_mem_stab hgl hvl) hvl
  by_cases h0 : MSP.mat g *ᵥ v - v = 0
  ·
    apply hg1
    refine eq_one_of_fixVec_eq_top (eq_top_of_perp_lt hp ?_)
    refine lt_of_le_of_ne (fun w hw => mem_fixVec.2 (hgx w hw)) fun he => hvp ?_
    rw [he]
    exact mem_fixVec.2 (sub_eq_zero.1 h0)
  ·
    apply hpl
    have hspan : (F ∙ (MSP.mat g *ᵥ v - v)) ≤ p := (Submodule.span_singleton_le_iff_mem _ _).2 h1
    have heq : (F ∙ (MSP.mat g *ᵥ v - v)) = p := by
      refine Submodule.eq_of_le_of_finrank_eq hspan ?_
      rw [finrank_span_singleton h0]
      exact hp.symm
    rw [← heq]
    exact (Submodule.span_singleton_le_iff_mem _ _).2 h2

theorem eq_of_mem_xPoint_qPoint {p p₀ : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    (hp₀ : MSP.IsPoint p₀) {g : MSP.Sp4 F} (hgx : g ∈ MSP.xPoint p) (hgq : g ∈ MSP.qPoint p₀)
    (hg1 : g ≠ 1) : p = p₀ := by
  by_contra hne
  have hinf : p ⊓ p₀ = ⊥ := by
    have hlt : p ⊓ p₀ < p := by
      refine lt_of_le_of_ne inf_le_left fun he => hne ?_
      have hle : p ≤ p₀ := he ▸ inf_le_right
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      rw [show Module.finrank F p = 1 from hp, show Module.finrank F p₀ = 1 from hp₀]
    have := Submodule.finrank_lt_finrank_of_lt hlt
    rw [show Module.finrank F p = 1 from hp] at this
    exact Submodule.finrank_eq_zero.1 (by omega)
  have hfix₀ : MSP.perp p₀ ≤ fixVec g := by
    intro v hv
    have h1 : MSP.mat g *ᵥ v - v ∈ p₀ := hgq.2 v hv
    have h2 : MSP.mat g *ᵥ v - v ∈ p := MSP.sub_mem_of_mem_fixer_perp hgx v
    have : MSP.mat g *ᵥ v - v ∈ p ⊓ p₀ := ⟨h2, h1⟩
    rw [hinf] at this
    exact mem_fixVec.2 (sub_eq_zero.1 this)
  have hfix : MSP.perp p ≤ fixVec g := fun w hw => mem_fixVec.2 (hgx w hw)
  apply hg1
  refine eq_one_of_fixVec_eq_top (eq_top_of_perp_lt hp (lt_of_le_of_ne hfix fun he => hne ?_))
  have hle : MSP.perp p₀ ≤ MSP.perp p := he ▸ hfix₀
  have := MSP.perp_antitone hle
  rw [MSP.perp_perp, MSP.perp_perp] at this
  refine Submodule.eq_of_le_of_finrank_eq this ?_
  rw [show Module.finrank F p = 1 from hp, show Module.finrank F p₀ = 1 from hp₀]

theorem fixer_le_stab_perp (p : Submodule F (MSP.V4 F)) :
    MSP.fixer p ≤ MSP.stab (MSP.perp p) :=
  (MSP.fixer_le_stab p).trans (MSP.stab_le_stab_perp p)

end Sp4

section JFix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] in
theorem imM_le_normalizer (hTM : T ≤ M) {K X : Subgroup G}
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) :
    imM hTM K ≤ Subgroup.normalizer (imM hTM X : Set (puAmalgam hTM).Universal) := by
  refine le_normalizer_of_map_conj_le ?_
  rintro _ ⟨m, hm, rfl⟩ _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hmx : (m : G) * x * (m : G)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.1 (hKX (Subgroup.mem_subgroupOf.1 hm)) x).1
      (Subgroup.mem_subgroupOf.1 hx)
  refine ⟨m * x * m⁻¹, Subgroup.mem_subgroupOf.2 (by simpa using hmx), ?_⟩
  simp [map_mul, map_inv]

theorem le_normalizer_uq_inf_centralizer (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E J₀ : Subgroup G} (hEM : E ≤ M) (hJM : J₀ ≤ M)
    (hJ : (J₀.subgroupOf M).map a ≤ MSP.stab (MSP.fixSp ((E.subgroupOf M).map a))) :
    J₀ ≤ Subgroup.normalizer
      ((Uq M T L ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  refine le_normalizer_of_map_conj_le fun j hj => ?_
  rintro _ ⟨u, ⟨hu, huE⟩, rfl⟩
  have hju : j * u * j⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn (hJM hj)) u).1 hu
  refine ⟨hju, ?_⟩
  have h1 := (mem_centralizer_iff_vec h hlift c hEM ⟨u, hu⟩).1 huE
  have h2 : a ⟨j, hJM hj⟩ ∈ MSP.stab (MSP.fixSp ((E.subgroupOf M).map a)) :=
    hJ ⟨⟨j, hJM hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
  have h3 := c.vec_conj ⟨j, hJM hj⟩ ⟨u, hu⟩ hju
  have h4 : c.vec ⟨_, hju⟩ ∈ MSP.fixSp ((E.subgroupOf M).map a) := by
    rw [h3]
    exact MSP.mulVec_mem_of_mem_stab h2 h1
  exact (mem_centralizer_iff_vec h hlift c hEM ⟨_, hju⟩).2 h4

theorem jOff_le_normalizer_baseA (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) (h54 : S54)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ (baseB (puAmalgam h.le)))
    (hEQ : ¬ E ≤ Qv _ (baseA (puAmalgam h.le)))
    (hcard : Nat.card ↥⁅S5.uSub h.le L (baseA (puAmalgam h.le)), E⁆ ≤ 2 ^ k) :
    S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ Subgroup.normalizer
      ((S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) : Subgroup _) : Set _) := by
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  rw [puAmalgam.qv_baseB] at hE
  obtain ⟨E₀, hE₀T, hE₀M, rfl⟩ := exists_eq_imM h.le hE
  have hE₀2 : IsPGroup 2 E₀ := h.isPGroup.to_le hE₀T
  have hE₀O : ¬ E₀ ≤ pCoreOf 2 M := by
    intro hle
    apply hEQ
    rw [qv_baseA_eq h]
    exact imM_mono h.le hle
  have hcard₀ : Nat.card ↥⁅Uq M T L, E₀⁆ ≤ 2 ^ k := by
    rw [uSub_baseA h, ← imM_commutator h.le (Uq_le h.L_le) hE₀M,
      card_imM h.le (commutator_le_of_le (Uq_le h.L_le) hE₀M)] at hcard
    exact hcard
  obtain ⟨p, hp, -, hfix, hxP, -⟩ :=
    exists_point_of_card_commutator_le h hd hlift hE₀M hE₀2 hE₀O hcard₀
  obtain ⟨g, hgE, hg1⟩ : ∃ g ∈ (E₀.subgroupOf M).map a, g ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : (E₀.subgroupOf M).map a = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hne
    have htop : MSP.fixSp ((E₀.subgroupOf M).map a) = ⊤ := by
      rw [hbot]
      ext v
      simp [MSP.mem_fixSp, MSP.mat_one]
    rw [htop] at hfix
    have h4 : Module.finrank F (MSP.V4 F) = 4 := by simp
    have h3 := MSP.finrank_perp p
    rw [← hfix, finrank_top, h4] at h3
    have hp1 : Module.finrank F p = 1 := hp
    omega
  have hTE : ∀ x ∈ (E₀.subgroupOf M).map a, x ∈ (T.subgroupOf M).map a := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.2 (hE₀T (Subgroup.mem_subgroupOf.1 hm)), rfl⟩
  rw [uSub_baseA h, ← imM_inf_centralizer h.le _ hE₀M]
  suffices hJ : ∃ J₀ : Subgroup G, J₀ ≤ M ∧
      S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤ imM h.le J₀ ∧
      (J₀.subgroupOf M).map a ≤ MSP.fixer p by
    obtain ⟨J₀, hJ₀M, hJJ, hJp⟩ := hJ
    refine hJJ.trans (imM_le_normalizer h.le ?_)
    refine le_normalizer_uq_inf_centralizer h hd hE₀M hJ₀M ?_
    rw [hfix]
    exact hJp.trans (fixer_le_stab_perp p)
  rcases h54 G M T L h hmin hb k F _ _ a hd with
    ⟨-, ⟨l, hl, hTl, hJl⟩, -⟩ | ⟨-, hJT, p₀, hp₀, hTq⟩
  ·
    have hgl : g ∈ MSP.stab l := by
      obtain ⟨m, hm, rfl⟩ := hTE g hgE
      have hmT : (puAmalgam h.le).ofA m ∈ Qv _ (baseB (puAmalgam h.le)) := by
        rw [puAmalgam.qv_baseB]
        exact ⟨m, hm, rfl⟩
      obtain ⟨m', hm', he⟩ := hTl hmT
      rw [(puAmalgam h.le).ofA_injective he] at hm'
      exact hm'
    have hpl := le_of_mem_xPoint_stab hp hl (hxP hgE) hgl hg1
    refine ⟨((MSP.qLine l).comap a).map M.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
    · refine hJl.trans ?_
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, Subgroup.mem_subgroupOf.2 ⟨m, hm, rfl⟩, rfl⟩
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨m', hm', he⟩ := Subgroup.mem_subgroupOf.1 hm
      rw [Subtype.ext he] at hm'
      exact MSP.fixer_antitone hpl hm'
  ·
    have hTq' : (T.subgroupOf M).map a = MSP.qPoint p₀ := by
      rw [← hTq, S5.vIm, puAmalgam.qv_baseB]
      ext x
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m, ⟨m, hm, rfl⟩, rfl⟩
      · rintro ⟨m, ⟨m', hm', he⟩, rfl⟩
        rw [(puAmalgam h.le).ofA_injective he] at hm'
        exact ⟨m, hm', rfl⟩
    have hpp : p = p₀ :=
      eq_of_mem_xPoint_qPoint hp hp₀ (hxP hgE) (hTq' ▸ hTE g hgE) hg1
    refine ⟨T, h.le, ?_, ?_⟩
    · rw [hJT, puAmalgam.qv_baseB]
    · rw [hTq', ← hpp]
      exact MSP.qPoint_le_fixer p

theorem jOff_le_normalizer (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) (h54 : S54)
    {γ ε : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) (hγε : (puAmalgam h.le).treeGraph.Adj γ ε)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ ε) (hEQ : ¬ E ≤ Qv _ γ)
    (hcard : Nat.card ↥⁅S5.uSub h.le L γ, E⁆ ≤ 2 ^ k) :
    S5.jOff h.le L (2 ^ k) γ ε ≤ Subgroup.normalizer
      ((S5.uSub h.le L γ ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) :
        Subgroup _) : Set _) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hγ hγε
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hEE : E = E'.map (MulAut.conj g).toMonoidHom := (map_conj_map_conj_inv E g).symm
  rw [hEE] at hE hEQ hcard ⊢
  rw [qv_smul, map_conj_le_map_conj_iff] at hE hEQ
  rw [uSub_smul h.le hLn, ← Subgroup.map_commutator, card_map_conj] at hcard
  rw [jOff_smul h.le hLn, uSub_smul h.le hLn, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, normalizer_map_conj,
    map_conj_le_map_conj_iff]
  exact jOff_le_normalizer_baseA h hmin hb hd h54 hE hEQ hcard

end JFix

end S5B

end CFSG.Quasithin.MS93
