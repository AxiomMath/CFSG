module

public import CFSG.Quasithin.H13.A5W1618g

public section

namespace CFSG.Quasithin.H13.A7Blk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv Equiv.Perm

variable {G : Type} [Group G] {n : ℕ}

@[expose] noncomputable def permAutEquiv (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)

theorem coe_permAutEquiv_apply (hn : 5 ≤ n) (hn6 : n ≠ 6) (σ : Perm (Fin n))
    (a : alternatingGroup (Fin n)) :
    ((permAutEquiv hn hn6 σ a : alternatingGroup (Fin n)) : Perm (Fin n)) = σ * a * σ⁻¹ := rfl

section Act

variable {K : Subgroup G} (α : ↥K →* alternatingGroup (Fin n)) (hα : Function.Surjective α)
  (hker : α.ker = CFSG.pCore 2 ↥K)

include hker in
theorem map_ker_conjAct (g : ↥(Subgroup.normalizer (K : Set G))) :
    α.ker.map (conjAct K g : ↥K →* ↥K) = α.ker := by
  rw [hker]
  exact CFSG.pCore_map_iso 2 (conjAct K g)

@[expose] noncomputable def indAut (g : ↥(Subgroup.normalizer (K : Set G))) :
    MulAut (alternatingGroup (Fin n)) :=
  ((QuotientGroup.quotientKerEquivOfSurjective α hα).symm.trans
    (QuotientGroup.congr α.ker α.ker (conjAct K g) (map_ker_conjAct α hker g))).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)

theorem indAut_apply (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    indAut α hα hker g (α k) = α (conjAct K g k) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective α hα).symm (α k) =
      (QuotientGroup.mk k : ↥K ⧸ α.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show (QuotientGroup.quotientKerEquivOfSurjective α hα) (QuotientGroup.congr α.ker α.ker
    (conjAct K g) (map_ker_conjAct α hker g)
      ((QuotientGroup.quotientKerEquivOfSurjective α hα).symm (α k))) = _
  rw [h1]
  rfl

theorem indAut_mul (g h : ↥(Subgroup.normalizer (K : Set G))) :
    indAut α hα hker (g * h) = indAut α hα hker g * indAut α hα hker h := by
  refine MulEquiv.ext fun a => ?_
  obtain ⟨k, rfl⟩ := hα a
  rw [MulAut.mul_apply, indAut_apply, indAut_apply, indAut_apply, map_mul]
  rfl

@[expose] noncomputable def indAutHom :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (alternatingGroup (Fin n)) where
  toFun := indAut α hα hker
  map_one' := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨k, rfl⟩ := hα a
    rw [indAut_apply, map_one]
    rfl
  map_mul' := indAut_mul α hα hker

variable (hn : 5 ≤ n) (hn6 : n ≠ 6)

@[expose] noncomputable def permAct : ↥(Subgroup.normalizer (K : Set G)) →* Perm (Fin n) :=
  (permAutEquiv hn hn6).symm.toMonoidHom.comp (indAutHom α hα hker)

theorem permAutEquiv_permAct (g : ↥(Subgroup.normalizer (K : Set G))) :
    permAutEquiv hn hn6 (permAct α hα hker hn hn6 g) = indAut α hα hker g := by
  show permAutEquiv hn hn6 ((permAutEquiv hn hn6).symm (indAut α hα hker g)) = _
  exact MulEquiv.apply_symm_apply _ _

theorem permAct_spec (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    ((α (conjAct K g k) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      permAct α hα hker hn hn6 g * α k * (permAct α hα hker hn hn6 g)⁻¹ := by
  rw [← indAut_apply α hα hker, ← permAutEquiv_permAct α hα hker hn hn6]
  rfl

theorem permAct_of_mem (k : ↥K) :
    permAct α hα hker hn hn6 ⟨k, Subgroup.le_normalizer k.2⟩ = (α k : Perm (Fin n)) := by
  apply (permAutEquiv hn hn6).injective
  rw [permAutEquiv_permAct]
  refine MulEquiv.ext fun a => Subtype.ext ?_
  obtain ⟨k', rfl⟩ := hα a
  rw [indAut_apply, coe_permAutEquiv_apply]
  have e : conjAct K ⟨k, Subgroup.le_normalizer k.2⟩ k' = k * k' * k⁻¹ :=
    Subtype.ext (Setup.coe_conjAct_apply _ _)
  rw [e, map_mul, map_mul, map_inv]
  rfl

theorem exists_fixed [Finite G] (hodd : Odd n) {T : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (K : Set G)) (hT : IsPGroup 2 T) :
    ∃ i : Fin n, ∀ (t : G) (ht : t ∈ T), permAct α hα hker hn hn6 ⟨t, hTN ht⟩ i = i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup (Perm (Fin n)) :=
    (T.subgroupOf (Subgroup.normalizer (K : Set G))).map (permAct α hα hker hn hn6) with hP
  have hT' : IsPGroup 2 (T.subgroupOf (Subgroup.normalizer (K : Set G))) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm
  have hP2 : IsPGroup 2 P := hT'.map _
  have h := hP2.card_modEq_card_fixedPoints (Fin n)
  rw [Nat.card_fin] at h
  obtain ⟨i, hi⟩ : (MulAction.fixedPoints P (Fin n)).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : Nat.card ↥(MulAction.fixedPoints P (Fin n)) = 0 := by
      rw [hne]
      simp
    rw [h0] at h
    obtain ⟨m, hm⟩ := hodd
    unfold Nat.ModEq at h
    omega
  refine ⟨i, fun t ht => ?_⟩
  have hmem : permAct α hα hker hn hn6 ⟨t, hTN ht⟩ ∈ P := ⟨⟨t, hTN ht⟩, ht, rfl⟩
  exact hi ⟨_, hmem⟩

end Act

theorem le_pCore_of_normal {X : Type*} [Group X] {p : ℕ} {N : Subgroup X} (hN : N.Normal)
    (hP : IsPGroup p N) : N ≤ CFSG.pCore p X :=
  le_sSup ⟨hN, hP⟩

theorem stabilizer_eq_range (i : Fin n) :
    MulAction.stabilizer (alternatingGroup (Fin n)) i =
      (alternatingGroup.ofSubtype (Finset.univ.erase i)).range := by
  ext k
  rw [alternatingGroup.mem_range_ofSubtype_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro hk x hx
    rw [Finset.mem_erase]
    refine ⟨fun h => ?_, Finset.mem_univ _⟩
    subst h
    exact (Equiv.Perm.mem_support.mp hx) hk
  · intro hk
    by_contra h
    have hi : i ∈ (k : Perm (Fin n)).support := Equiv.Perm.mem_support.mpr h
    exact (Finset.mem_erase.mp (hk hi)).1 rfl

theorem card_erase (i : Fin n) : Nat.card ↥(Finset.univ.erase i) = n - 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]

@[expose] noncomputable def stabEquiv (i : Fin n) :
    ↥(MulAction.stabilizer (alternatingGroup (Fin n)) i) ≃* alternatingGroup (Fin (n - 1)) :=
  (MulEquiv.subgroupCongr (stabilizer_eq_range i)).trans
    ((MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).symm.trans
      (Equiv.altCongrHom (Finite.equivFinOfCardEq (card_erase i))))

theorem perfect_stabilizer (hn : 6 ≤ n) (i : Fin n) :
    ⁅MulAction.stabilizer (alternatingGroup (Fin n)) i,
      MulAction.stabilizer (alternatingGroup (Fin n)) i⁆ =
      MulAction.stabilizer (alternatingGroup (Fin n)) i := by
  have h : ⁅(⊤ : Subgroup (alternatingGroup ↥(Finset.univ.erase i))), ⊤⁆ = ⊤ :=
    commutator_alternatingGroup_eq_top (by rw [card_erase]; omega)
  rw [stabilizer_eq_range, MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

theorem isSimpleGroup_stabilizer (hn : 6 ≤ n) (i : Fin n) :
    IsSimpleGroup ↥(MulAction.stabilizer (alternatingGroup (Fin n)) i) := by
  have : IsSimpleGroup (alternatingGroup (Fin (n - 1))) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  exact (stabEquiv i).isSimpleGroup

theorem eq_or_eq_bot_of_subnormal {Γ : Type*} [Group Γ] {Q H : Subgroup Γ}
    (hQ : IsSimpleGroup ↥Q) (h : IsSubnormal H Q) : H = Q ∨ H = ⊥ :=
  (h.eq_bot_or_eq_of_isSimpleGroup hQ).symm

section Pt

variable {K : Subgroup G} (α : ↥K →* alternatingGroup (Fin n))

@[expose] noncomputable def ptPre (i : Fin n) : Subgroup G :=
  ((MulAction.stabilizer (alternatingGroup (Fin n)) i).comap α).map K.subtype

theorem ptPre_le (i : Fin n) : ptPre α i ≤ K := Subgroup.map_subtype_le _

theorem mem_ptPre {i : Fin n} {x : G} :
    x ∈ ptPre α i ↔ ∃ h : x ∈ K, (α ⟨x, h⟩ : Perm (Fin n)) i = i := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

@[expose] noncomputable def ptCore (i : Fin n) : Subgroup G := perfectCore (ptPre α i)

theorem ptCore_le (i : Fin n) : ptCore α i ≤ K := (perfectCore_le _).trans (ptPre_le α i)

theorem ptCore_le_ptPre (i : Fin n) : ptCore α i ≤ ptPre α i := perfectCore_le _

variable (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) (hn : 5 ≤ n) (hn6 : n ≠ 6)

theorem mem_normalizer_ptCore {i : Fin n} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hgi : permAct α hα hker hn hn6 ⟨g, hg⟩ i = i) :
    g ∈ Subgroup.normalizer (ptCore α i : Set G) := by
  refine normalizer_le_normalizer_perfectCore (ptPre α i) ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  set σ := permAct α hα hker hn hn6 ⟨g, hg⟩ with hσ
  have hσi : σ⁻¹ i = i := by rw [Perm.inv_eq_iff_eq, hgi]
  have key : ∀ hx : x ∈ K, ∀ hgx : g * x * g⁻¹ ∈ K,
      (α ⟨g * x * g⁻¹, hgx⟩ : Perm (Fin n)) = σ * α ⟨x, hx⟩ * σ⁻¹ := by
    intro hx hgx
    rw [← permAct_spec α hα hker hn hn6]
    congr 2
  rw [mem_ptPre, mem_ptPre]
  constructor
  · rintro ⟨hx, hxi⟩
    have hgx : g * x * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    refine ⟨hgx, ?_⟩
    rw [key hx hgx, Perm.mul_apply, Perm.mul_apply, hσi, hxi, hgi]
  · rintro ⟨hgx, hxi⟩
    have hx : x ∈ K := (Subgroup.mem_normalizer_iff.mp hg x).mpr hgx
    refine ⟨hx, ?_⟩
    rw [key hx hgx, Perm.mul_apply, Perm.mul_apply, hσi] at hxi
    exact σ.injective (hxi.trans hgi.symm)

variable [Finite G]

theorem subgroupOf_ptCore (i : Fin n) :
    (ptCore α i).subgroupOf K =
      perfectCore ((MulAction.stabilizer (alternatingGroup (Fin n)) i).comap α) := by
  rw [ptCore, ptPre, ← map_perfectCore]
  exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

include hα in
theorem map_ptCore (h6 : 6 ≤ n) (i : Fin n) :
    ((ptCore α i).subgroupOf K).map α = MulAction.stabilizer (alternatingGroup (Fin n)) i := by
  rw [subgroupOf_ptCore, map_perfectCore, Subgroup.map_comap_eq_self_of_surjective hα,
    perfectCore_eq_self_of_perfect (perfect_stabilizer h6 i)]

@[expose] noncomputable def ptHom (i : Fin n) :
    ↥(ptCore α i) →* ↥(MulAction.stabilizer (alternatingGroup (Fin n)) i) :=
  (α.comp (Subgroup.inclusion (ptCore_le α i))).codRestrict _ fun x => by
    obtain ⟨h, hx⟩ := (mem_ptPre α).mp (ptCore_le_ptPre α i x.2)
    exact hx

omit [Finite G] in
theorem coe_ptHom (i : Fin n) (x : ↥(ptCore α i)) :
    ((ptHom α i x : ↥(MulAction.stabilizer (alternatingGroup (Fin n)) i)) :
      alternatingGroup (Fin n)) = α ⟨x, ptCore_le α i x.2⟩ := rfl

include hα in
theorem ptHom_surjective (h6 : 6 ≤ n) (i : Fin n) : Function.Surjective (ptHom α i) := by
  rintro ⟨s, hs⟩
  rw [← map_ptCore α hα h6 i] at hs
  obtain ⟨y, hy, rfl⟩ := hs
  exact ⟨⟨y, hy⟩, Subtype.ext rfl⟩

omit [Finite G] in
include hker in
theorem isPGroup_ker_ptHom (i : Fin n) : IsPGroup 2 (ptHom α i).ker := by
  rintro ⟨x, hx⟩
  have hx1 : α ⟨x, ptCore_le α i x.2⟩ = 1 := congrArg Subtype.val ((ptHom α i).mem_ker.mp hx)
  have hxk : (⟨x, ptCore_le α i x.2⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := hker ▸ hx1
  obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup ⟨_, hxk⟩
  refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun y : ↥(CFSG.pCore 2 ↥K) => ((y : ↥K) : G)) hm
  simpa using this

include hα hker in
theorem ker_ptHom (h6 : 6 ≤ n) (i : Fin n) : (ptHom α i).ker = CFSG.pCore 2 ↥(ptCore α i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (le_pCore_of_normal (ptHom α i).normal_ker (isPGroup_ker_ptHom α hker i)) ?_
  have hsimp := isSimpleGroup_stabilizer h6 i
  have hN : ((CFSG.pCore 2 ↥(ptCore α i)).map (ptHom α i)).Normal :=
    Subgroup.Normal.map CFSG.pCore_normal _ (ptHom_surjective α hα h6 i)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((CFSG.pCore 2 ↥(ptCore α i)).map (ptHom α i)) with h | h
  · rw [← Subgroup.map_eq_bot_iff]
    exact h
  · exfalso
    have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥(ptCore α i)).map (ptHom α i)) :=
      CFSG.pCore_isPGroup.map _
    rw [h] at h2
    have hs : Group.IsSolvable ↥(MulAction.stabilizer (alternatingGroup (Fin n)) i) := by
      have h3 : IsPGroup 2 ↥(MulAction.stabilizer (alternatingGroup (Fin n)) i) :=
        h2.of_equiv Subgroup.topEquiv
      have := h3.isNilpotent
      infer_instance
    have hperf := perfect_stabilizer h6 i
    have hnt := hsimp.toNontrivial
    have h4 := (isSolvable_iff_perfectCore_eq_bot
      (MulAction.stabilizer (alternatingGroup (Fin n)) i)).mp hs
    rw [perfectCore_eq_self_of_perfect hperf] at h4
    rw [h4] at hnt
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hnt

include hα hker in
theorem nonempty_quot_ptCore (h6 : 6 ≤ n) (i : Fin n) :
    Nonempty (↥(ptCore α i) ⧸ CFSG.pCore 2 ↥(ptCore α i) ≃* alternatingGroup (Fin (n - 1))) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq (ker_ptHom α hα hker h6 i).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (ptHom_surjective α hα h6 i))).trans
      (stabEquiv i)⟩

include hα hker in
theorem mem_lFamily_ptCore (h6 : 6 ≤ n) {i : Fin n} {T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (ptCore α i : Set G)) : ptCore α i ∈ lFamily T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := ptCore α i with hBdef
  have hBK : B ≤ K := ptCore_le α i
  have hperf : ⁅B, B⁆ = B := perfectCore_perfect _
  have hsimp := isSimpleGroup_stabilizer h6 i
  have hmap := map_ptCore α hα h6 i
  set N : Subgroup G := B ⊓ (CFSG.pCore 2 ↥K).map K.subtype with hNdef
  have hNB : N ≤ B := inf_le_left
  have hN2 : IsPGroup 2 N :=
    (CFSG.pCore_isPGroup.map K.subtype).to_le inf_le_right
  have hNs : Group.IsSolvable ↥N := by
    have := hN2.isNilpotent
    infer_instance
  have hne : B ≠ ⊥ := by
    intro h
    have h' : ptCore α i = ⊥ := h
    have hnt := hsimp.toNontrivial
    rw [← hmap, h', Subgroup.bot_subgroupOf, Subgroup.map_bot] at hnt
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hnt
  refine ⟨hne, hperf, A3.subnormal_of_normal le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hT)), fun L hLB hLne hLp hLsub => ?_⟩
  have hLsubB : IsSubnormal L B := A3.subnormal_of_le_of_le hLsub hLB.le le_sup_left
  have himsub : IsSubnormal ((L.subgroupOf K).map α)
      (MulAction.stabilizer (alternatingGroup (Fin n)) i) := by
    have h1 : IsSubnormal (L.subgroupOf K) (B.subgroupOf K) := A3.subnormal_comap K.subtype hLsubB
    have h2 := A3.subnormal_map α h1
    rwa [hmap] at h2
  rcases eq_or_eq_bot_of_subnormal hsimp himsub with him | him
  ·
    apply hLB.ne
    refine A5.eq_of_subnormal_of_le_sup_solvable hNB hperf hNs hLsubB fun b hb => ?_
    have hbK := hBK hb
    have hbs : α ⟨b, hbK⟩ ∈ MulAction.stabilizer (alternatingGroup (Fin n)) i :=
      ((mem_ptPre α).mp (ptCore_le_ptPre α i hb)).2
    rw [← him] at hbs
    obtain ⟨y, hy, hyb⟩ := hbs
    have hyB : (y : G) ∈ B := hLB.le hy
    have hz : (y : G)⁻¹ * b ∈ N := by
      refine ⟨B.mul_mem (B.inv_mem hyB) hb, ⟨y⁻¹ * ⟨b, hbK⟩, ?_, rfl⟩⟩
      show y⁻¹ * ⟨b, hbK⟩ ∈ CFSG.pCore 2 ↥K
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyb, inv_mul_cancel]
    have e : b = (y : G) * ((y : G)⁻¹ * b) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hz)
  ·
    apply hLne
    have hLN : L ≤ N := by
      intro x hx
      have hxK := hBK (hLB.le hx)
      have h1 : α ⟨x, hxK⟩ ∈ (L.subgroupOf K).map α := ⟨⟨x, hxK⟩, hx, rfl⟩
      rw [him, Subgroup.mem_bot] at h1
      refine ⟨hLB.le hx, ⟨⟨x, hxK⟩, ?_, rfl⟩⟩
      show (⟨x, hxK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K
      rw [← hker]
      exact h1
    have hLs : Group.IsSolvable ↥L := by
      have := (hN2.to_le hLN).isNilpotent
      infer_instance
    have h4 := (isSolvable_iff_perfectCore_eq_bot L).mp hLs
    rwa [perfectCore_eq_self_of_perfect hLp] at h4

include hα hker in
theorem oTwoRes_le_ptCore (h6 : 6 ≤ n) {i : Fin n} {Y : Subgroup G} (hYK : oTwoRes Y ≤ K)
    (hfix : ∀ (x : G) (hx : x ∈ oTwoRes Y), (α ⟨x, hYK hx⟩ : Perm (Fin n)) i = i) :
    oTwoRes Y ≤ ptCore α i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxY, m, hm, hxm⟩
  have hxo : x ∈ oTwoRes Y := Subgroup.subset_closure ⟨hxY, m, hm, hxm⟩
  have hxK := hYK hxo
  have hxP : x ∈ ptPre α i := (mem_ptPre α).mpr ⟨hxK, hfix x hxo⟩
  have hxs : α ⟨x, hxK⟩ ∈ MulAction.stabilizer (alternatingGroup (Fin n)) i := hfix x hxo
  rw [← map_ptCore α hα h6 i] at hxs
  obtain ⟨y, hy, hyx⟩ := hxs
  have hyC : (y : G) ∈ ptCore α i := hy
  have hz : y⁻¹ * ⟨x, hxK⟩ ∈ CFSG.pCore 2 ↥K := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, hz⟩
  have hk' : ((y : G)⁻¹ * x) ^ 2 ^ k = 1 := by
    have := congrArg (fun w : ↥(CFSG.pCore 2 ↥K) => ((w : ↥K) : G)) hk
    simpa using this
  set P := ptPre α i with hPdef
  set C := (ptCore α i).subgroupOf P with hCdef
  have hCn : C.Normal := perfectCore_normal _
  set q := QuotientGroup.mk' C with hq
  have hyP : (y : G) ∈ P := ptCore_le_ptPre α i hyC
  have hqy : q ⟨y, hyP⟩ = 1 := (QuotientGroup.eq_one_iff (⟨y, hyP⟩ : ↥P)).mpr hyC
  have hx1 : q ⟨x, hxP⟩ ^ m = 1 := by
    rw [← map_pow]
    have : (⟨x, hxP⟩ : ↥P) ^ m = 1 := Subtype.ext (by simpa using hxm)
    rw [this, map_one]
  have hx2 : q ⟨x, hxP⟩ ^ 2 ^ k = 1 := by
    have e : (⟨x, hxP⟩ : ↥P) = ⟨y, hyP⟩ * (⟨y, hyP⟩⁻¹ * ⟨x, hxP⟩) := by group
    rw [e, map_mul, hqy, one_mul, ← map_pow]
    have : (⟨y, hyP⟩⁻¹ * ⟨x, hxP⟩ : ↥P) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [this, map_one]
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Odd.coprime_two_right hm)
  have h1 : q ⟨x, hxP⟩ = 1 := by
    have ho : orderOf (q ⟨x, hxP⟩) ∣ Nat.gcd m (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx1) (orderOf_dvd_of_pow_eq_one hx2)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at ho
    exact ho
  exact (QuotientGroup.eq_one_iff (⟨x, hxP⟩ : ↥P)).mp h1

end Pt

end CFSG.Quasithin.H13.A7Blk

end
