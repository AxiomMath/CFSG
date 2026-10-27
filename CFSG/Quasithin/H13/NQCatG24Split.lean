module

public import CFSG.Quasithin.Vol2.Ch6Sec1Res619
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame

public section

namespace CFSG.Quasithin.H13.NQCat.G24Split

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.L239.Lie
  CFSG.LieType.BorelTits

section Elem

variable {G G' : Type*} [Group G] [Group G']

theorem isElemAbelian_map {X : Subgroup G} (h : CFSG.Open.IsElemAbelian 2 X) (f : G →* G') :
    CFSG.Open.IsElemAbelian 2 (X.map f) := CFSG.SectionRank.isElemAbelian_map h _

theorem isElemAbelian_of_map {X : Subgroup G} (f : G →* G') (hf : Function.Injective f)
    (h : CFSG.Open.IsElemAbelian 2 (X.map f)) : CFSG.Open.IsElemAbelian 2 X := by
  have := h.1
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · have h1 := congrArg Subtype.val
      (mul_comm' (⟨f a, a, a.2, rfl⟩ : X.map f) ⟨f b, b, b.2, rfl⟩)
    simpa using h1
  · rw [map_pow, map_one]
    exact h.2 (f x) ⟨x, hx, rfl⟩

end Elem

section Abstract

variable {G : Type*} [Group G] [Finite G]

structure RootSplit (P Q X : Subgroup G) (q : ℕ) : Prop where
  facts : ParabolicFacts P Q
  le_core : X ≤ perfectCore P
  inf_eq : X ⊓ Q = ⊥
  elem : CFSG.Open.IsElemAbelian 2 X
  card : Nat.card X = q

theorem RootSplit.map {G' : Type*} [Group G'] [Finite G'] {P Q X : Subgroup G} {q : ℕ}
    (h : RootSplit P Q X q) (f : G →* G') (hf : Function.Injective f) :
    RootSplit (P.map f) (Q.map f) (X.map f) q where
  facts := h.facts.map f hf
  le_core := by
    rw [← map_perfectCore f P]
    exact Subgroup.map_mono h.le_core
  inf_eq := by rw [← Subgroup.map_inf_eq _ _ f hf, h.inf_eq, Subgroup.map_bot]
  elem := isElemAbelian_map h.elem f
  card := by rw [Subgroup.card_map_of_injective hf, h.card]

theorem RootSplit.of_map {G' : Type*} [Group G'] [Finite G'] {P Q X : Subgroup G} {q : ℕ}
    (f : G →* G') (hf : Function.Injective f) (h : RootSplit (P.map f) (Q.map f) (X.map f) q) :
    RootSplit P Q X q where
  facts := ParabolicFacts.of_map f hf h.facts
  le_core := by
    have h1 := h.le_core
    rw [← map_perfectCore f P] at h1
    exact (Subgroup.map_le_map_iff_of_injective hf).1 h1
  inf_eq := by
    have h1 := h.inf_eq
    rw [← Subgroup.map_inf_eq _ _ f hf] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ hf).1 h1
  elem := isElemAbelian_of_map f hf h.elem
  card := by rw [← h.card, Subgroup.card_map_of_injective hf]

theorem RootSplit.subgroupOf {P Q X C : Subgroup G} {q : ℕ} (h : RootSplit P Q X q)
    (hPC : P ≤ C) : RootSplit (P.subgroupOf C) (Q.subgroupOf C) (X.subgroupOf C) q := by
  have hQC : Q ≤ C := h.facts.le.trans hPC
  have hXC : X ≤ C := h.le_core.trans ((perfectCore_le P).trans hPC)
  refine RootSplit.of_map C.subtype C.subtype_injective ?_
  rw [Subgroup.map_subgroupOf_eq_of_le hPC, Subgroup.map_subgroupOf_eq_of_le hQC,
    Subgroup.map_subgroupOf_eq_of_le hXC]
  exact h

theorem eq_bot_of_perfect_of_isPGroup {D : Subgroup G} (hD : ⁅D, D⁆ = D) (hp : IsPGroup 2 D) :
    D = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent D := hp.isNilpotent
  rw [← perfectCore_eq_self_of_perfect hD]
  exact (isSolvable_iff_perfectCore_eq_bot D).1 inferInstance

theorem RootSplit.le_and_inf_pCoreOf {P Q X N : Subgroup G} {q : ℕ} (h : RootSplit P Q X q)
    (hNP : N ≤ P) (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hN : ¬ Group.IsSolvable N) :
    X ≤ N ∧ X ⊓ pCoreOf 2 N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := perfectCore P with hC
  set D := perfectCore N with hD
  have hCP : C ≤ P := perfectCore_le P
  have hDC : D ≤ C := perfectCore_mono hNP
  have hPD : P ≤ Subgroup.normalizer (D : Set G) :=
    hPN.trans (normalizer_le_normalizer_perfectCore N)
  have hDQ : ¬ D ≤ Q := fun hle => hN ((isSolvable_iff_perfectCore_eq_bot N).2
    (eq_bot_of_perfect_of_isPGroup (perfectCore_perfect N) (h.facts.pGroup.to_le hle)))
  rcases h.facts.levi with hCQ | ⟨hQ, T, _, g, hT, hg, hker⟩
  · exact absurd (hDC.trans hCQ) hDQ
  have hQC : Q ≤ C := by
    refine hQ.trans (Subgroup.commutator_le.2 fun x hx c hc => ?_)
    have hxN : x ∈ Subgroup.normalizer (C : Set G) :=
      normalizer_le_normalizer_perfectCore P (Subgroup.le_normalizer (h.facts.le hx))
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 hxN c).1 hc) (inv_mem hc)
  have himg : ∀ A : Subgroup G, A ≤ C → C ≤ Subgroup.normalizer (A : Set G) →
      (A.subgroupOf C).map g = ⊥ ∨ (A.subgroupOf C).map g = ⊤ := fun A hAC hCA => by
    have hn : (A.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAC).2 hCA
    have := hn.map g hg
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal _
  have hbot : ∀ A : Subgroup G, (hAC : A ≤ C) → (A.subgroupOf C).map g = ⊥ → A ≤ Q :=
    fun A hAC h0 x hx => by
      have h1 := Subgroup.mem_map_of_mem g
        (show (⟨x, hAC hx⟩ : ↥C) ∈ A.subgroupOf C from hx)
      rw [h0, Subgroup.mem_bot] at h1
      exact hker _ h1
  have hCD : C ≤ D := by
    rcases himg D hDC (hCP.trans hPD) with h0 | htop
    · exact absurd (hbot D hDC h0) hDQ
    have hCDQ : C = D ⊔ Q := by
      refine le_antisymm (fun x hx => ?_) (sup_le hDC hQC)
      have h1 : g ⟨x, hx⟩ ∈ (D.subgroupOf C).map g := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨d, hd, hdx⟩ := h1
      have hq : ((d⁻¹ * ⟨x, hx⟩ : ↥C) : G) ∈ Q :=
        hker _ (by rw [map_mul, map_inv, hdx, inv_mul_cancel])
      have hx' : x = (d : G) * ((d⁻¹ * ⟨x, hx⟩ : ↥C) : G) := by simp
      rw [hx']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right hq)
    have hDn : (D.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDC).2 (hCP.trans hPD)
    have : Group.IsNilpotent Q := h.facts.pGroup.isNilpotent
    have h1 := perfectCore_le_of_sup_solvable hDC hDn hCDQ inferInstance
    rwa [perfectCore_eq_self_of_perfect (perfectCore_perfect P)] at h1
  have hCN : C ≤ N := hCD.trans (perfectCore_le N)
  refine ⟨h.le_core.trans hCN, ?_⟩
  have hRC : pCoreOf 2 N ⊓ C ≤ C := inf_le_right
  have hCR : C ≤ Subgroup.normalizer ((pCoreOf 2 N ⊓ C : Subgroup G) : Set G) :=
    fun c hc => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf 2 N (hCN hc), Subgroup.le_normalizer hc⟩
  have hRQ : pCoreOf 2 N ⊓ C ≤ Q := by
    rcases himg _ hRC hCR with h0 | htop
    · exact hbot _ hRC h0
    exfalso
    have hRp : IsPGroup 2 ↥(pCoreOf 2 N ⊓ C) := (pCoreOf_isPGroup 2 N).to_le inf_le_left
    have : Finite T := Finite.of_surjective g hg
    have hTp : IsPGroup 2 T := by
      intro t
      have ht : t ∈ ((pCoreOf 2 N ⊓ C).subgroupOf C).map g := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨r, hr, rfl⟩ := ht
      obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
      refine ⟨k, ?_⟩
      have hr1 : r ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [← map_pow, hr1, map_one]
    have : Group.IsPerfect ↥C := Subgroup.isPerfect_iff.2 (perfectCore_perfect P)
    have : Group.IsPerfect T := Group.IsPerfect.ofSurjective hg
    exact Group.IsPerfect.not_isNilpotent T hTp.isNilpotent
  rw [eq_bot_iff, ← h.inf_eq]
  intro x hx
  exact ⟨hx.1, hRQ ⟨hx.2, h.le_core hx.1⟩⟩

end Abstract

section TwoLocal

variable {Y : Type*} [Group Y]

theorem isSylowTwoOf_top_map {X : Type*} [Group X] {U : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (e : X ≃* Y) : IsSylowTwoOf (U.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hU.2.1.map _, ?_⟩
  have h1 := hU.2.2
  rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h1
  rw [show ((U.map e.toMonoidHom).subgroupOf ⊤).index = (U.map e.toMonoidHom).index from
    Subgroup.relIndex_top_right _, MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
  exact h1

theorem exists_eq_map_conj_of_isMaximalTwoLocal [Finite Y] {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) {P Q : Fin 2 → Subgroup Y} (hP : ResidualOvergroupsAt Y U P)
    (hBT : Holds Y 2)
    (hQ : ∀ j, Q j ≠ ⊥ ∧ IsPGroup 2 (Q j) ∧ P j ≤ Subgroup.normalizer (Q j : Set Y))
    {T M : Subgroup Y} (hT : IsSylowTwoOf T ⊤) (hM : IsMaximalTwoLocal M)
    (hTM : Subgroup.normalizer (T : Set Y) ≤ M) :
    ∃ j, ∃ g : Y, M = (P j).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, -, hg⟩ := hU.exists_conj hT
  obtain ⟨R, hR1, hR2, hMR⟩ := hM.1
  have hMtop : M ≠ ⊤ := by
    obtain ⟨-, P', hP', hNP', -⟩ := hBT R hR1 hR2
    intro h
    apply hP'
    rw [eq_top_iff, ← h, hMR]
    exact hNP'
  have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Y := by
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  have hid' : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id Y := by
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  set M' := M.map (MulAut.conj g⁻¹).toMonoidHom with hM'
  have hUM' : U ≤ M' := by
    have h1 : T ≤ M := Subgroup.le_normalizer.trans hTM
    have h2 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h1
    rwa [hg, Subgroup.map_map, hid, Subgroup.map_id] at h2
  have hM'top : M' ≠ ⊤ := by
    intro h
    apply hMtop
    have h1 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h
    rwa [hM', Subgroup.map_map, hid', Subgroup.map_id,
      Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1
  obtain ⟨A, hA, hM'A⟩ := (eq_top_or_exists_le_coatom M').resolve_left hM'top
  obtain ⟨j, rfl⟩ := (hP.2.2.1 A (hUM'.trans hM'A)).1 hA.covBy_top
  obtain ⟨hQ1, hQ2, hPQ⟩ := hQ j
  have hPN : Subgroup.normalizer (Q j : Set Y) = P j := by
    rcases (hA.le_iff).1 hPQ with h | h
    · exfalso
      obtain ⟨-, P', hP', hNP', -⟩ := hBT (Q j) hQ1 hQ2
      apply hP'
      rw [eq_top_iff, ← h]
      exact hNP'
    · exact h
  refine ⟨j, g, (hM.2 _ ⟨(Q j).map (MulAut.conj g).toMonoidHom, ?_, hQ2.map _, ?_⟩ ?_).symm⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
  · rw [← Subgroup.map_equiv_normalizer_eq, hPN]
  · have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hM'A
    rwa [hM', Subgroup.map_map, hid', Subgroup.map_id] at h1

end TwoLocal

section Vertex

variable {G : Type} [Group G] [Finite G]

theorem exists_split_of_vertex {L B S : Subgroup G} {Y : Type} [Group Y] [Finite Y]
    {M Q X : Subgroup Y} {q : ℕ} (hRS : RootSplit M Q X q) (φ : ↥(L ⊔ B) ≃* ↥M)
    (hLB : L ⊔ B ≤ Subgroup.normalizer (L : Set G)) (hL : ¬ Group.IsSolvable L)
    (hS : IsSylowTwoOf (S ⊓ L) L) :
    ∃ E : Subgroup G, E ≤ S ⊓ L ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = q ∧
      E ⊓ pCoreOf 2 L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set χ : ↥M →* G := (L ⊔ B).subtype.comp φ.symm.toMonoidHom with hχ
  have hχi : Function.Injective χ := (L ⊔ B).subtype_injective.comp φ.symm.injective
  have hrange : (M.subgroupOf M).map χ = L ⊔ B := by
    rw [Subgroup.subgroupOf_self]
    ext x
    constructor
    · rintro ⟨m, -, rfl⟩
      exact (φ.symm m).2
    · intro hx
      refine ⟨φ ⟨x, hx⟩, Subgroup.mem_top _, ?_⟩
      simp [hχ]
  have hG := (hRS.subgroupOf le_rfl).map χ hχi
  rw [hrange] at hG
  obtain ⟨hXL, hXO⟩ := hG.le_and_inf_pCoreOf le_sup_left hLB hL
  set E₀ := (X.subgroupOf M).map χ with hE₀
  have hE₀p : IsPGroup 2 E₀ := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hG.elem.2 x x.2)⟩
  obtain ⟨S', hE₀S', hS'⟩ := exists_isSylowTwoOf_of_le hXL hE₀p
  obtain ⟨h, hh, hS'eq⟩ := hS.exists_conj hS'
  set c := (MulAut.conj h⁻¹).toMonoidHom with hc
  have hci : Function.Injective c := (MulAut.conj h⁻¹).injective
  have hcc : c.comp (MulAut.conj h).toMonoidHom = MonoidHom.id G := by
    ext x
    simp only [hc, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  have hO : (pCoreOf 2 L).map c = pCoreOf 2 L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (le_normalizer_pCoreOf 2 L (inv_mem hh))
  have hS'c : S'.map c = S ⊓ L := by rw [hS'eq, Subgroup.map_map, hcc, Subgroup.map_id]
  refine ⟨E₀.map c, ?_, isElemAbelian_map hG.elem c, ?_, ?_⟩
  · exact (Subgroup.map_mono hE₀S').trans hS'c.le
  · rw [Subgroup.card_map_of_injective hci, hG.card]
  · rw [← hO, ← Subgroup.map_inf_eq _ _ c hci, hXO, Subgroup.map_bot]

end Vertex

section G2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem rootSplit_g2
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (i : Fin Tag.G2.rank) :
    RootSplit (parabolicSubgroup Tag.G2 K {i}) (parabolicRadical Tag.G2 K {i})
      (CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K (Pi.single i 1)) (2 ^ f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨L, hLP, hL, hx, -, -⟩ := G2.leviL_data hK4 i
  have hXL : CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K (Pi.single i 1) ≤ L := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_single]
    exact hx c
  have hXM : CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K (Pi.single i 1) ≤
      parabolicLevi Tag.G2 K {i} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, pinnedX_single]
    exact xUnit_mem_parabolicLevi (Set.mem_singleton i) c
  refine ⟨?_, hXL.trans (le_perfectCore_of_perfect hLP hL), ?_, ⟨?_, fun x hx => ?_⟩, ?_⟩
  · rcases G2.fin_two_cases i with rfl | rfl
    · exact G2.parabolicFacts_zero hK hf
    · exact G2.parabolicFacts_one hK hf
  · rw [eq_bot_iff, ← parabolicRadical_inf_parabolicLevi (τ := Tag.G2) (K := K) {i}]
    exact fun x hx => ⟨hx.2, hXM hx.1⟩
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨c, rfl⟩ := (rootSubgroupEquiv Tag.G2 K (Pi.single i 1)).surjective a
    obtain ⟨d, rfl⟩ := (rootSubgroupEquiv Tag.G2 K (Pi.single i 1)).surjective b
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, mul_comm]
  · by_cases hx1 : x = 1
    · rw [hx1, one_pow]
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_eq_of_mem_rootSubgroup (p := 2) hx hx1]
  · rw [card_rootSubgroup, hK]

end G2

theorem g24LongRootSplit_holds :
    G24LongRootSplit := by
  intro G _ _ L1 L2 S f hf hyp hAm hQ1 hQ2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨φ⟩⟩ := hAm
  have hYm : ChevalleyExceptionalModel Y .G2 2 f := by
    rcases hY with ⟨rfl, -⟩ | ⟨-, hY⟩
    · omega
    rcases hY with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · simp [classicalTags] at h
    · exact h
    · simp [reeTitsTags] at h
    · exact absurd h (by decide)
  have hBT : Holds Y 2 := holds_of_chevalleyExceptionalModel_untwisted hYm (by decide) (by decide)
  obtain ⟨-, K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hYm
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  set C := adjointGroup Tag.G2 K with hC
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf C) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  have hRS : ∀ j : Fin 2, RootSplit
      (((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf C).map e.symm.toMonoidHom)
      (((parabolicRadical Tag.G2 K {g2Index j}).subgroupOf C).map e.symm.toMonoidHom)
      (((CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K (Pi.single (g2Index j) 1)).subgroupOf
        C).map e.symm.toMonoidHom) (2 ^ f) := fun j =>
    ((rootSplit_g2 hK hf (g2Index j)).subgroupOf
      (parabolicSubgroup_le_adjointGroup _ _ _)).map _ e.symm.injective
  have hvert : ∀ M : Subgroup Y, IsMaximalTwoLocal M → Subgroup.normalizer (T : Set Y) ≤ M →
      ∃ Q X : Subgroup Y, RootSplit M Q X (2 ^ f) := by
    intro M hM hTM
    obtain ⟨j, g, rfl⟩ := exists_eq_map_conj_of_isMaximalTwoLocal (isSylowTwoOf_top_map hU₀ e.symm)
      (G2_residualOvergroupsAt.map e.symm) hBT
      (Q := fun j => ((parabolicRadical Tag.G2 K {g2Index j}).subgroupOf C).map
        e.symm.toMonoidHom)
      (fun j => ⟨fun h0 => by
          obtain ⟨x, hx, y, -, hxy⟩ := (hRS j).facts.nonabelian
          rw [h0, Subgroup.mem_bot] at hx
          exact hxy (by rw [hx, one_mul, mul_one]),
        (hRS j).facts.pGroup, (hRS j).facts.normalizes⟩) hpair.1 hM hTM
    exact ⟨_, _, (hRS j).map _ (MulAut.conj g).injective⟩
  have hL : ∀ L : Subgroup G, IsL2Quot f (oTwoQuot ↥L) → ¬ Group.IsSolvable L := by
    intro L hQ hs
    obtain ⟨ψ⟩ := hQ
    have h4 : 3 < Nat.card (GaloisField 2 f) := by
      rw [GaloisField.card 2 f (by omega)]
      calc 3 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
      CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three _ h4
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact Group.IsPerfect.not_isSolvable _
      (Group.isSolvable_of_surjective (f := ψ.toMonoidHom.comp (QuotientGroup.mk' _))
        (ψ.surjective.comp (QuotientGroup.mk'_surjective _)))
  have hB1 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer (sup_le (sup_le
      ((inf_le_left : borelOf L1 S ≤ L1).trans Subgroup.le_normalizer) hyp.h1.borel_le)
      hyp.h1.normalizes)
  have hB2 : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer (sup_le (sup_le hyp.h2.borel_le
      ((inf_le_left : borelOf L2 S ≤ L2).trans Subgroup.le_normalizer)) hyp.h2.normalizes)
  obtain ⟨hM₁, hTM₁⟩ := (hpair.2.2 M₁).2 (Or.inl rfl)
  obtain ⟨hM₂, hTM₂⟩ := (hpair.2.2 M₂).2 (Or.inr rfl)
  obtain ⟨Q₁, X₁, h₁⟩ := hvert M₁ hM₁ hTM₁
  obtain ⟨Q₂, X₂, h₂⟩ := hvert M₂ hM₂ hTM₂
  exact ⟨exists_split_of_vertex h₁ φ.φ1 hB1 (hL L1 hQ1) hyp.h1.sylow,
    exists_split_of_vertex h₂ φ.φ2 hB2 (hL L2 hQ2) hyp.h2.sylow⟩

end CFSG.Quasithin.H13.NQCat.G24Split
