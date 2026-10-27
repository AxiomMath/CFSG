module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocks
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelToJ
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.PerfectSupCenter
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.OrbitSup

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

open CFSG.RankThree.Native.ONTriple CFSG.Sporadic.ON
open scoped commutatorElement

attribute [local irreducible] dotProduct


theorem orderOf_zG' : orderOf zG = 3 := by
  rw [← modelEquiv_zF, MulEquiv.orderOf_eq, orderOf_zF]

section General

open scoped Pointwise

variable {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
  [MulAction.IsPretransitive G X]

theorem le_normalizer_or_eq_top_of_prim {x₀ : X}
    (hblocks : ∀ B : Set X, x₀ ∈ B → MulAction.IsBlock G B → B = {x₀} ∨ B = Set.univ)
    (hidx : ∀ Y : Subgroup G, Y.index ≤ 6 → Y = ⊤)
    {T Y : Subgroup G} {ω : X} (hTω : T ≤ MulAction.stabilizer G ω)
    (hTS : 6 * Nat.card T = Nat.card (MulAction.stabilizer G ω))
    (hN : MulAction.stabilizer G ω ≤ Subgroup.normalizer (T : Set G))
    (horb : ∀ p : X, ∀ s ∈ MulAction.stabilizer G ω, ∃ t ∈ T, t • p = s • p)
    (hTY : T ≤ Y) : Y ≤ Subgroup.normalizer (T : Set G) ∨ Y = ⊤ := by
  classical
  set S := MulAction.stabilizer G ω with hSdef
  have hinv : ∀ s ∈ S, ∀ y ∈ MulAction.orbit Y ω, s • y ∈ MulAction.orbit Y ω := by
    rintro s hs _ ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨t, ht, hts⟩ := horb (y • ω) s hs
    refine ⟨⟨t * y, Y.mul_mem (hTY ht) hy⟩, ?_⟩
    change (t * y) • ω = s • (y • ω)
    rw [mul_smul]
    exact hts
  have horbsup := Proving.orbit_sup_eq_of_smul_mem hinv
  have hblock : MulAction.IsBlock G (MulAction.orbit Y ω) := by
    rw [← horbsup]
    exact MulAction.IsBlock.of_orbit le_sup_right
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x₀ ω
  have hblock' := hblock.translate g⁻¹
  have h0' : x₀ ∈ g⁻¹ • MulAction.orbit Y ω := by
    refine ⟨ω, MulAction.mem_orbit_self ω, ?_⟩
    change g⁻¹ • ω = x₀
    rw [← hg, inv_smul_smul]
  have hmem : ∀ y ∈ Y, y • ω ∈ g • (g⁻¹ • MulAction.orbit Y ω) := by
    intro y hy
    rw [smul_inv_smul]
    exact ⟨⟨y, hy⟩, rfl⟩
  rcases hblocks _ h0' hblock' with h | h
  · left
    intro y hy
    have hy' := hmem y hy
    rw [h, Set.smul_set_singleton, hg, Set.mem_singleton_iff] at hy'
    exact hN hy'
  · right
    have huniv : MulAction.orbit Y ω = Set.univ := by
      rw [← smul_inv_smul g (MulAction.orbit Y ω), h, Set.smul_set_univ]
    have hY : Nat.card X * Nat.card T ≤ Nat.card Y := by
      have h1 := (MulAction.stabilizer Y ω).card_mul_index
      rw [MulAction.index_stabilizer, huniv, Set.ncard_univ] at h1
      have hle : T.subgroupOf Y ≤ MulAction.stabilizer Y ω := by
        intro t ht
        rw [Subgroup.mem_subgroupOf] at ht
        exact hTω ht
      have h2 : Nat.card T ≤ Nat.card (MulAction.stabilizer Y ω) := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv]
        exact Subgroup.card_le_of_le hle
      rw [← h1, mul_comm]
      exact Nat.mul_le_mul_right _ h2
    have hG : Nat.card G = Nat.card X * (6 * Nat.card T) := by
      have h1 := S.card_mul_index
      rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, ← hTS] at h1
      rw [← h1, mul_comm]
    refine hidx Y ?_
    have h1 := Y.card_mul_index
    have hXpos : 0 < Nat.card X := Nat.card_pos_iff.2 ⟨⟨ω⟩, inferInstance⟩
    have hTpos : 0 < Nat.card T := Nat.card_pos
    by_contra hc
    have h7 : 7 ≤ Y.index := by omega
    have : Nat.card X * Nat.card T * 7 ≤ Nat.card G := by
      rw [← h1]
      exact Nat.mul_le_mul hY h7
    rw [hG] at this
    nlinarith [Nat.mul_pos hXpos hTpos]

omit
  [Finite G] [Finite X]
  [MulAction.IsPretransitive G X] in
theorem conj_inv_mem_stabilizer {g s : G} {x : X} (hs : s ∈ MulAction.stabilizer G (g • x)) :
    g⁻¹ * s * g ∈ MulAction.stabilizer G x := by
  rw [MulAction.mem_stabilizer_iff] at hs ⊢
  rw [mul_smul, mul_smul, hs, inv_smul_smul]

omit
  [Finite G] [Finite X]
  [MulAction.IsPretransitive G X] in
theorem conj_mem_stabilizer_smul {g s : G} {x : X} (hs : s ∈ MulAction.stabilizer G x) :
    g * s * g⁻¹ ∈ MulAction.stabilizer G (g • x) := by
  rw [MulAction.mem_stabilizer_iff] at hs ⊢
  rw [mul_smul, mul_smul, inv_smul_smul, hs]

omit
  [Finite G] [Finite X]
  [MulAction.IsPretransitive G X] in
theorem smul_conj_fix {s g s' : G} {x : X} (hq : s' • g⁻¹ • x = g⁻¹ • x) :
    (s * (g * s' * g⁻¹)) • x = s • x := by
  rw [mul_smul, mul_smul, mul_smul, hq, smul_inv_smul]

omit
  [Finite G] in
theorem conj_inv_conj (g s : G) : g⁻¹ * (g * s * g⁻¹) * g = s := by group

omit
  [Finite G] in
theorem conj_mul_conj (g s s' : G) : g⁻¹ * (s * (g * s' * g⁻¹)) * g = g⁻¹ * s * g * s' := by
  group

end General

theorem eq_top_of_index_le_six {Y : Subgroup GM} (h : Y.index ≤ 6) : Y = ⊤ := by
  have := CFSG.Sporadic.ON.isSimpleGroup_J
  have hfin : Finite GM := finite_GM
  set K := Y.map phiJ
  have hK : K.index ≤ 6 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Y.index_ne_zero_of_finite)
      (Subgroup.index_map_dvd Y phiJ_surjective)).trans h
  have hKtop : K = ⊤ := by
    rcases K.normalCore_normal.eq_bot_or_eq_top with hb | ht
    · exfalso
      have h1 := K.index_normalCore_le_factorial_index
      rw [hb, Subgroup.index_bot, card_J] at h1
      have h2 : Nat.factorial K.index ≤ Nat.factorial 6 := Nat.factorial_le hK
      have h3 : Nat.factorial 6 = 720 := rfl
      omega
    · exact eq_top_iff.2 (ht ▸ K.normalCore_le)
  have hdec : ∀ x : GM, ∃ y ∈ Y, ∃ n : ℤ, x = y * zG ^ n := by
    intro x
    have : phiJ x ∈ K := by rw [hKtop]; trivial
    obtain ⟨y, hy, hyx⟩ := this
    have hk : y⁻¹ * x ∈ phiJ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    rw [ker_phiJ, Subgroup.mem_zpowers_iff] at hk
    obtain ⟨n, hn⟩ := hk
    exact ⟨y, hy, n, by rw [hn]; group⟩
  have hzcen : zG ∈ Subgroup.center GM := by
    rw [← ker_phiJ_eq_center, ker_phiJ]
    exact Subgroup.mem_zpowers zG
  have hzY : zG ∈ Y := by
    obtain ⟨y₁, hy₁, n₁, h₁⟩ := hdec (xG 0)
    obtain ⟨y₂, hy₂, n₂, h₂⟩ := hdec (xG 3)
    rw [← comm_x0_x3, h₁, h₂,
      Proving.commutatorElement_mul_central_left (Subgroup.zpow_mem _ hzcen n₁),
      Proving.commutatorElement_mul_central_right (Subgroup.zpow_mem _ hzcen n₂),
      commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy₁ hy₂) (Y.inv_mem hy₁)) (Y.inv_mem hy₂)
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, n, rfl⟩ := hdec x
  exact Y.mul_mem hy (Y.zpow_mem hzY n)

theorem conj_mem_stab_W {g s : GM} (hs : s ∈ MulAction.stabilizer GM (g • W)) :
    g⁻¹ * s * g ∈ MulAction.stabilizer GM W :=
  conj_inv_mem_stabilizer hs

theorem conj_mem_stab_smul_W {g s : GM} (hs : s ∈ MulAction.stabilizer GM W) :
    g * s * g⁻¹ ∈ MulAction.stabilizer GM (g • W) :=
  conj_mem_stabilizer_smul hs

@[expose] noncomputable def chiAt (g : GM) : MulAction.stabilizer GM (g • W) →* (ZMod 7)ˣ :=
  chiW.comp
    { toFun := fun s => ⟨g⁻¹ * s * g, conj_mem_stab_W s.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by simp [mul_assoc]) }

theorem chiAt_apply (g : GM) (s : MulAction.stabilizer GM (g • W)) :
    chiAt g s = chiW ⟨g⁻¹ * s * g, conj_mem_stab_W s.2⟩ := rfl

theorem card_stab_smul_W (g : GM) :
    Nat.card (MulAction.stabilizer GM (g • W)) = 11261376 := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.card_map_of_injective
    (MulAut.conj g).injective, card_stab_W]

theorem card_ker_chiAt (g : GM) : Nat.card (chiAt g).ker = 1876896 := by
  have hsurj : Function.Surjective (chiAt g) := by
    intro u
    obtain ⟨s, -, hs⟩ := exists_fix_chiW (MulAction.mem_orbit_self (M := GM) W) u
    refine ⟨⟨g * s * g⁻¹, conj_mem_stab_smul_W s.2⟩, ?_⟩
    rw [chiAt_apply, ← hs]
    exact congrArg chiW (Subtype.ext (conj_inv_conj g (s : GM)))
  have h1 := (chiAt g).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.card_top,
    Nat.card_eq_fintype_card (α := (ZMod 7)ˣ), ZMod.card_units_eq_totient, card_stab_smul_W] at h1
  have h6 : Nat.totient 7 = 6 := rfl
  rw [h6] at h1
  omega

theorem chiAt_eq_one_of_perfect {g : GM} {T : Subgroup GM} [Group.IsPerfect T]
    (hT : T ≤ MulAction.stabilizer GM (g • W)) {t : GM} (ht : t ∈ T) :
    chiAt g ⟨t, hT ht⟩ = 1 := by
  set ψ : T →* (ZMod 7)ˣ := (chiAt g).comp (Subgroup.inclusion hT)
  have hker : ψ.ker = ⊤ := by
    rw [eq_top_iff, ← (Group.isPerfect_def (G := T)).1 inferInstance]
    exact Abelianization.commutator_subset_ker ψ
  have : (⟨t, ht⟩ : T) ∈ ψ.ker := by rw [hker]; trivial
  exact this

theorem le_normalizer_or_eq_top_of_perfect {T Y : Subgroup GM} [Group.IsPerfect T] {ω : Sub7}
    (hω : ω ∈ XW) (hTω : T ≤ MulAction.stabilizer GM ω) (hcard : Nat.card T = 1876896)
    (hTY : T ≤ Y) : Y ≤ Subgroup.normalizer (T : Set GM) ∨ Y = ⊤ := by
  classical
  have hfin : Finite GM := finite_GM
  obtain ⟨g, rfl⟩ := hω
  set S := MulAction.stabilizer GM (g • W)
  have hTker : T = (chiAt g).ker.map S.subtype := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro t ht
      exact ⟨⟨t, hTω ht⟩, chiAt_eq_one_of_perfect hTω ht, rfl⟩
    · rw [Subgroup.card_map_of_injective S.subtype_injective, card_ker_chiAt, hcard]
  have hmemT : ∀ x (hx : x ∈ S), chiAt g ⟨x, hx⟩ = 1 → x ∈ T := by
    intro x hx h
    rw [hTker]
    exact ⟨⟨x, hx⟩, h, rfl⟩
  have fwd : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T := by
    intro s hs t ht
    refine hmemT _ (S.mul_mem (S.mul_mem hs (hTω ht)) (S.inv_mem hs)) ?_
    have e : (⟨s * t * s⁻¹, S.mul_mem (S.mul_mem hs (hTω ht)) (S.inv_mem hs)⟩ : S) =
        ⟨s, hs⟩ * ⟨t, hTω ht⟩ * ⟨s, hs⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, chiAt_eq_one_of_perfect hTω ht, mul_one, mul_inv_cancel]
  have hN : S ≤ Subgroup.normalizer (T : Set GM) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨fwd s hs t, fun h => ?_⟩
    have := fwd s⁻¹ (S.inv_mem hs) _ h
    simpa [mul_assoc] using this
  have horb : ∀ p ∈ XW, ∀ s ∈ S, ∃ t ∈ T, t • p = s • p := by
    intro p hp s hs
    obtain ⟨a, ha⟩ := hp
    have ha' : a • W = p := ha
    subst ha'
    have hq : g⁻¹ • a • W ∈ XW := ⟨g⁻¹ * a, mul_smul _ _ _⟩
    set s0 : MulAction.stabilizer GM W := ⟨g⁻¹ * s * g, conj_mem_stab_W hs⟩
    obtain ⟨s', hs'q, hs'⟩ := exists_fix_chiW hq (chiW s0)⁻¹
    have hgs' : g * (s' : GM) * g⁻¹ ∈ S := conj_mem_stab_smul_W s'.2
    have htS : s * (g * (s' : GM) * g⁻¹) ∈ S := S.mul_mem hs hgs'
    refine ⟨_, hmemT _ htS ?_, ?_⟩
    · rw [chiAt_apply]
      have e : (⟨g⁻¹ * (s * (g * (s' : GM) * g⁻¹)) * g, conj_mem_stab_W htS⟩ :
          MulAction.stabilizer GM W) = s0 * s' := Subtype.ext (conj_mul_conj g s (s' : GM))
      rw [e, map_mul, hs', mul_inv_cancel]
    · exact smul_conj_fix hs'q
  have hXfin : Finite XW := (Set.finite_range _).to_subtype
  set ω' : XW := ⟨g • W, ⟨g, rfl⟩⟩
  have hstab : MulAction.stabilizer GM ω' = S := by
    ext s
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, Subtype.ext_iff]
    rfl
  refine le_normalizer_or_eq_top_of_prim (x₀ := (⟨W, MulAction.mem_orbit_self W⟩ : XW))
    (fun B h0 hB => isBlock_W_cases h0 hB) (fun Y h => eq_top_of_index_le_six h)
    (ω := ω') (hstab ▸ hTω) ?_ (hstab ▸ hN) ?_ hTY
  · rw [hstab, card_stab_smul_W, hcard]
  · intro p s hs
    rw [hstab] at hs
    obtain ⟨t, ht, e⟩ := horb p.1 p.2 s hs
    exact ⟨t, ht, Subtype.ext e⟩

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
