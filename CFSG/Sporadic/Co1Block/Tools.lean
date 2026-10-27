
module

public import CFSG.Sporadic.Co1.Module.InvSpec
public import CFSG.Sporadic.Co1.Module.TwoBTree

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.TwoB Matrix

section Trees

variable {G : Type*} [Group G] (μ : G →* Matrix (Fin 24) (Fin 24) (ZMod 2))

theorem map_inv_eq_of_mul {g : G} {N : Matrix (Fin 24) (Fin 24) (ZMod 2)} (h : μ g * N = 1) :
    μ g⁻¹ = N := by
  calc μ g⁻¹ = μ g⁻¹ * (μ g * N) := by rw [h, Matrix.mul_one]
    _ = (μ g⁻¹ * μ g) * N := by rw [Matrix.mul_assoc]
    _ = N := by rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]

theorem eq_of_rowsMatrix_eq {pts : Array (Array ℕ)}
    (hvalid : ∀ i < pts.size, validRows pts[i]! = true)
    (hdist : distinctKeys (pts.toList.map rowsKey) = true) {i j : ℕ} (hi : i < pts.size)
    (hj : j < pts.size) (hm : rowsMatrix 24 pts[i]! = rowsMatrix 24 pts[j]!) : i = j := by
  have hpe := rowsMatrix_injective_of_valid (hvalid i hi) (hvalid j hj) hm
  have hnd := distinctKeys_nodup hdist
  have hlen : (pts.toList.map rowsKey).length = pts.size := by simp
  have hgi : (pts.toList.map rowsKey)[i]'(hlen ▸ hi) = rowsKey pts[i]! := by
    simp [getElem!_pos pts i hi]
  have hgj : (pts.toList.map rowsKey)[j]'(hlen ▸ hj) = rowsKey pts[j]! := by
    simp [getElem!_pos pts j hj]
  exact (List.Nodup.getElem_inj_iff hnd).1 (hgi.trans ((congrArg rowsKey hpe).trans hgj.symm))

theorem conjTree_sound {Gs Gi : Array (Array ℕ)} {root : Array ℕ}
    {c : ConjCert} (h : ctOK Gs Gi root c = true) (kk : ℕ → G)
    (hk : ∀ l < Gs.size, μ (kk l) = rowsMatrix 24 Gs[l]!)
    (hki : ∀ l < Gs.size, mulRows 24 Gs[l]! Gi[l]! = idRows 24)
    (s : G) (hs : μ s = rowsMatrix 24 root) :
    ∃ f : ℕ → G,
      (∀ i < c.pts.size, (∃ x ∈ Subgroup.closure (kk '' {l | l < Gs.size}), f i = x * s * x⁻¹) ∧
        μ (f i) = rowsMatrix 24 c.pts[i]!) ∧
      ∀ i < c.pts.size, ∀ j < c.pts.size, f i = f j → i = j := by
  unfold ctOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hpos, hroot⟩, hall⟩, hdist⟩ := h
  have hpt := CFSG.Sporadic.Th.allIn_eq_true.1 hall
  have hinvmat : ∀ l < Gs.size, μ (kk l)⁻¹ = rowsMatrix 24 Gi[l]! := by
    intro l hl
    apply map_inv_eq_of_mul μ
    rw [hk l hl, ← rowsMatrix_mulRows, hki l hl, rowsMatrix_idRows]
  have hmain : ∀ i < c.pts.size, ∃ x ∈ Subgroup.closure (kk '' {l | l < Gs.size}),
      μ (x * s * x⁻¹) = rowsMatrix 24 c.pts[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hp := hpt i (Nat.zero_le _) hi
      simp only [ctPointOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
      by_cases hi0 : i = 0
      · subst hi0
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [hroot]
        simpa using hs
      · obtain ⟨-, hp2⟩ := hp
        rcases hp2 with h0 | ⟨⟨hpar, hlab⟩, hconj⟩
        · exact absurd h0 hi0
        · obtain ⟨x', hx', hx'e⟩ := ih (c.par[i]!) hpar (by omega)
          refine ⟨kk (c.lab[i]!) * x', Subgroup.mul_mem _
            (Subgroup.subset_closure ⟨_, hlab, rfl⟩) hx', ?_⟩
          rw [hconj, conjRows, rowsMatrix_mulRows, rowsMatrix_mulRows, ← hk _ hlab, ← hx'e,
            ← hinvmat _ hlab]
          simp only [map_mul, _root_.mul_inv_rev, Matrix.mul_assoc]
  choose! x hx using hmain
  refine ⟨fun i => x i * s * (x i)⁻¹, fun i hi => ⟨⟨x i, (hx i hi).1, rfl⟩, (hx i hi).2⟩, ?_⟩
  intro i hi j hj hij
  have hvalid : ∀ i < c.pts.size, validRows c.pts[i]! = true := by
    intro i hi
    have hp := hpt i (Nat.zero_le _) hi
    simp only [ctPointOK, Bool.and_eq_true] at hp
    exact hp.1
  refine eq_of_rowsMatrix_eq hvalid hdist hi hj ?_
  rw [← (hx i hi).2, ← (hx j hj).2]
  exact congrArg μ hij

theorem prodTree_sound (hμ : Function.Injective μ) {Gs : Array (Array ℕ)} {T : GTree}
    (h : gtOK Gs T = true) (gg : ℕ → G) (hg : ∀ l < Gs.size, μ (gg l) = rowsMatrix 24 Gs[l]!) :
    ∃ f : ℕ → G,
      (∀ i < T.pts.size, f i ∈ Submonoid.closure (gg '' {l | l < Gs.size}) ∧
        μ (f i) = rowsMatrix 24 T.pts[i]!) ∧
      (∀ i < T.pts.size, ∀ j < T.pts.size, f i = f j → i = j) ∧
      (∀ i < T.pts.size, ∀ l < Gs.size, ∃ j < T.pts.size, f j = f i * gg l) ∧
      f 0 = 1 ∧ 0 < T.pts.size := by
  unfold gtOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hpos, -⟩, -⟩, hall⟩, hdist⟩, hclosed⟩ := h
  have hpt := CFSG.Sporadic.Th.allIn_eq_true.1 hall
  have hvalid : ∀ i < T.pts.size, validRows T.pts[i]! = true := by
    intro i hi
    have hp := hpt i (Nat.zero_le _) hi
    simp only [gtPointOK, Bool.and_eq_true] at hp
    exact hp.1
  have hroot : T.pts[0]! = idRows 24 := by
    have hp := hpt 0 (Nat.zero_le _) hpos
    simp only [gtPointOK, Bool.and_eq_true, beq_self_eq_true, ↓reduceIte, beq_iff_eq] at hp
    exact hp.2
  have hmain : ∀ i < T.pts.size, ∃ x ∈ Submonoid.closure (gg '' {l | l < Gs.size}),
      μ x = rowsMatrix 24 T.pts[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hp := hpt i (Nat.zero_le _) hi
      simp only [gtPointOK, Bool.and_eq_true] at hp
      obtain ⟨-, hp2⟩ := hp
      by_cases hi0 : i = 0
      · subst hi0
        refine ⟨1, Submonoid.one_mem _, ?_⟩
        rw [hroot, map_one, rowsMatrix_idRows]
      · simp only [beq_iff_eq, hi0, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hp2
        obtain ⟨⟨hpar', hlab'⟩, hpt'⟩ := hp2
        obtain ⟨x', hx', hxe⟩ := ih (T.par[i]!) hpar' (by omega)
        refine ⟨x' * gg (T.lab[i]!), Submonoid.mul_mem _ hx'
          (Submonoid.subset_closure ⟨_, hlab', rfl⟩), ?_⟩
        rw [hpt', rowsMatrix_mulRows, map_mul, hxe, hg _ hlab']
  choose! x hx using hmain
  have hinj : ∀ i < T.pts.size, ∀ j < T.pts.size, x i = x j → i = j := by
    intro i hi j hj hij
    refine eq_of_rowsMatrix_eq hvalid hdist hi hj ?_
    rw [← (hx i hi).2, ← (hx j hj).2, hij]
  have hclosed' : ∀ i < T.pts.size, ∀ l < Gs.size,
      ∃ j < T.pts.size, T.pts[j]! = mulRows 24 T.pts[i]! Gs[l]! := by
    intro i hi l hl
    unfold gtClosed at hclosed
    have h1 := CFSG.Sporadic.Th.allIn_eq_true.1 hclosed i (Nat.zero_le _) hi
    have h2 := CFSG.Sporadic.Th.allIn_eq_true.1 h1 l (Nat.zero_le _) hl
    rw [Std.HashSet.contains_ofList] at h2
    have h3 := List.contains_iff_mem.1 h2
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem h3
    have hj' : j < T.pts.size := by simpa using hj
    refine ⟨j, hj', ?_⟩
    rw [getElem!_pos T.pts j hj']
    simpa using hje
  refine ⟨x, fun i hi => ⟨(hx i hi).1, (hx i hi).2⟩, hinj, ?_, ?_, hpos⟩
  · intro i hi l hl
    obtain ⟨j, hj, hje⟩ := hclosed' i hi l hl
    refine ⟨j, hj, ?_⟩
    apply hμ
    rw [(hx j hj).2, hje, rowsMatrix_mulRows, map_mul, (hx i hi).2, hg l hl]
  · apply hμ
    rw [(hx 0 hpos).2, hroot, rowsMatrix_idRows, map_one]

theorem prodTree_closure_eq [Finite G] (hμ : Function.Injective μ) {Gs : Array (Array ℕ)}
    {T : GTree} (h : gtOK Gs T = true) (gg : ℕ → G)
    (hg : ∀ l < Gs.size, μ (gg l) = rowsMatrix 24 Gs[l]!) :
    ∃ f : ℕ → G, (∀ i < T.pts.size, μ (f i) = rowsMatrix 24 T.pts[i]!) ∧
      Set.InjOn f (Set.Iio T.pts.size) ∧
      (Subgroup.closure (gg '' {l | l < Gs.size}) : Set G) = f '' Set.Iio T.pts.size := by
  obtain ⟨f, hf1, hf2, hf3, hf4, hpos⟩ := prodTree_sound μ hμ h gg hg
  refine ⟨f, fun i hi => (hf1 i hi).2, fun i hi j hj e => hf2 i hi j hj e, ?_⟩
  have hsub : ((Subgroup.closure (gg '' {l | l < Gs.size}) : Subgroup G) : Set G) =
      Submonoid.closure (gg '' {l | l < Gs.size}) := by
    have := congrArg (fun K : Submonoid G => (K : Set G))
      (Subgroup.closure_toSubmonoid_of_finite (s := gg '' {l | l < Gs.size}))
    simpa using this
  rw [hsub]
  ext x
  constructor
  · intro hx
    induction hx using Submonoid.closure_induction_right with
    | one => exact ⟨0, hpos, hf4⟩
    | mul_right x _ y hy ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨j, hj, hje⟩ := hf3 i hi l hl
      exact ⟨j, hj, hje⟩
  · rintro ⟨i, hi, rfl⟩
    exact (hf1 i hi).1

theorem prodTree_card [Finite G] (hμ : Function.Injective μ) {Gs : Array (Array ℕ)} {T : GTree}
    (h : gtOK Gs T = true) (gg : ℕ → G) (hg : ∀ l < Gs.size, μ (gg l) = rowsMatrix 24 Gs[l]!) :
    Nat.card ↥(Subgroup.closure (gg '' {l | l < Gs.size})) = T.pts.size := by
  obtain ⟨f, -, hinj, heq⟩ := prodTree_closure_eq μ hμ h gg hg
  have h1 : Nat.card ↥(Subgroup.closure (gg '' {l | l < Gs.size})) =
      ((Subgroup.closure (gg '' {l | l < Gs.size}) : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq (Subgroup.closure (gg '' {l | l < Gs.size}) : Set G)
  rw [h1, heq, Set.InjOn.ncard_image hinj, Set.ncard_Iio_nat]

theorem mem_closure_of_prodTree [Finite G] (hμ : Function.Injective μ) {Gs : Array (Array ℕ)}
    {T : GTree} (h : gtOK Gs T = true) (gg : ℕ → G)
    (hg : ∀ l < Gs.size, μ (gg l) = rowsMatrix 24 Gs[l]!) {y : G} {i : ℕ} (hi : i < T.pts.size)
    (hy : μ y = rowsMatrix 24 T.pts[i]!) : y ∈ Subgroup.closure (gg '' {l | l < Gs.size}) := by
  obtain ⟨f, hf, -, heq⟩ := prodTree_closure_eq μ hμ h gg hg
  have : f i ∈ (Subgroup.closure (gg '' {l | l < Gs.size}) : Set G) := by
    rw [heq]
    exact ⟨i, hi, rfl⟩
  rw [show y = f i from hμ (hy.trans (hf i hi).symm)] at *
  exact this

end Trees

section Tower

variable {G : Type*} [Group G] [Finite G]

@[expose] def towerStab (C : Subgroup G) (b : ℕ → G) : ℕ → Subgroup G
  | 0 => C
  | i + 1 => towerStab C b i ⊓ Subgroup.centralizer {b i}

@[expose] def conjOrbit (K : Subgroup G) (x : G) : Set G := {y | ∃ g ∈ K, g * x * g⁻¹ = y}

omit [Finite G] in
theorem card_towerStab (C : Subgroup G) (b : ℕ → G) (i : ℕ) :
    Nat.card (towerStab C b i) =
      (conjOrbit (towerStab C b i) (b i)).ncard * Nat.card (towerStab C b (i + 1)) := by
  set K := towerStab C b i
  let _ : MulAction K G := MulAction.compHom G (MulAut.conj.comp K.subtype)
  have hsmul : ∀ (g : K) (x : G), g • x = (g : G) * x * (g : G)⁻¹ := fun _ _ => rfl
  have horb : Nat.card (MulAction.orbit K (b i)) * Nat.card (MulAction.stabilizer K (b i)) =
      Nat.card K := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K (b i))
  have hset : MulAction.orbit K (b i) = conjOrbit K (b i) := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, (hsmul g (b i)).symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, hsmul _ _⟩
  have h1 : Nat.card (MulAction.orbit K (b i)) = (conjOrbit K (b i)).ncard := by
    rw [← Nat.card_coe_set_eq, hset]
  have h2 : Nat.card (MulAction.stabilizer K (b i)) = Nat.card (towerStab C b (i + 1)) := by
    refine Nat.card_congr ⟨fun g => ⟨g.1.1, Subgroup.mem_inf.2 ⟨g.1.2, ?_⟩⟩,
      fun g => ⟨⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · have hg := g.2
      rw [MulAction.mem_stabilizer_iff, hsmul] at hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g.1.1 * b i = g.1.1 * b i * (g.1.1)⁻¹ * g.1.1 := by group
        _ = b i * g.1.1 := by rw [hg]
    · rw [MulAction.mem_stabilizer_iff, hsmul]
      have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
      show g.1 * b i * g.1⁻¹ = b i
      rw [hc, mul_inv_cancel_right]
  rw [← horb, h1, h2]

theorem card_mul_card_towerStab_le (C : Subgroup G) (b : ℕ → G) (L : ℕ → Set G) (n : ℕ → ℕ)
    (k : ℕ) (hL : ∀ i < k, ∀ x ∈ L i, x ∈ C ∧ ∀ l < i, x * b l = b l * x)
    (hn : ∀ i < k, n i ≤ (conjOrbit (Subgroup.closure (L i)) (b i)).ncard) :
    (∏ i ∈ Finset.range k, n i) * Nat.card (towerStab C b k) ≤ Nat.card C := by
  have hle : ∀ i < k, Subgroup.closure (L i) ≤ towerStab C b i := by
    intro i hi
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨hxC, hxb⟩ := hL i hi x hx
    suffices ∀ j ≤ i, x ∈ towerStab C b j from this i le_rfl
    intro j
    induction j with
    | zero => exact fun _ => hxC
    | succ j ih =>
      intro hj
      exact Subgroup.mem_inf.2 ⟨ih (by omega),
        Subgroup.mem_centralizer_singleton_iff.2 (hxb j (by omega))⟩
  have horb : ∀ i < k, n i ≤ (conjOrbit (towerStab C b i) (b i)).ncard := by
    intro i hi
    refine (hn i hi).trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hle i hi hg, rfl⟩
  have key : ∀ j ≤ k, (∏ i ∈ Finset.range j, n i) * Nat.card (towerStab C b j) ≤
      Nat.card (towerStab C b 0) := by
    intro j
    induction j with
    | zero => intro _; rw [Finset.prod_range_zero, one_mul]
    | succ j ih =>
      intro hj
      refine le_trans ?_ (ih (by omega))
      rw [Finset.prod_range_succ, mul_assoc, card_towerStab C b j]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (horb j (by omega)))
  exact key k le_rfl

omit [Finite G] in
theorem mem_towerStab {C : Subgroup G} {b : ℕ → G} {g : G} (hg : g ∈ C)
    (hb : ∀ i, g * b i = b i * g) : ∀ k, g ∈ towerStab C b k
  | 0 => hg
  | k + 1 => Subgroup.mem_inf.2 ⟨mem_towerStab hg hb k,
      Subgroup.mem_centralizer_singleton_iff.2 (hb k)⟩

omit [Finite G] in
theorem mem_towerStab_of_lt {C : Subgroup G} {b : ℕ → G} {g : G} (hg : g ∈ C) :
    ∀ k, (∀ i < k, g * b i = b i * g) → g ∈ towerStab C b k
  | 0, _ => hg
  | k + 1, hb => Subgroup.mem_inf.2 ⟨mem_towerStab_of_lt hg k fun i hi => hb i (by omega),
      Subgroup.mem_centralizer_singleton_iff.2 (hb k (by omega))⟩

end Tower

end CFSG.Sporadic.Co1Block
