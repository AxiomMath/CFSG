module

public import CFSG.Monster.GMS.Facts.Interfaces
public import CFSG.Monster.GMS.S342
public import CFSG.Monster.Tri.TwoAShort

public section

namespace CFSG.Monster.Tri.CoverG

open SimpleGraph CFSG.YGroups CFSG.Monster.B.Recog CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

structure TableVIFacts (d₀ : B) (G : Type) [Group G] : Prop where
  sls : SLSStatement d₀
  tableV : TableVIn G
  leech : LeechStatement
  tableIII : BabyTableIII
  tableIVBaby : BabyTableIV
  threeSwap : DoubleCoverThreeSwapIn G
  leechPair : LeechPairStatement

theorem _root_.CFSG.Monster.GMS.GMSInterfaces.tableVIFacts {d₀ : B} {G : Type} [Group G]
    (I : GMSInterfaces d₀ G) : TableVIFacts d₀ G :=
  ⟨I.sls, I.tableV, I.leech, I.tableIII, I.tableIVBaby, I.threeSwap, I.leechPair⟩

section Block

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem eq_top_of_orbit_partition (a : Ω) (S : Subgroup G)
    (hS : S ≤ MulAction.stabilizer G a) {ι : Type*} [Fintype ι] (b : ι → Ω) (n : ι → ℕ)
    (i₀ j₀ : ι) (hb₀ : b i₀ = a) (hbmem : ∀ i, b i ∈ MulAction.orbit G a)
    (hn : ∀ i, (MulAction.orbit S (b i)).ncard = n i)
    (hne : ∀ i j, i ≠ j → MulAction.orbit S (b i) ≠ MulAction.orbit S (b j))
    (hfin : (MulAction.orbit G a).Finite)
    (hsumN : ∑ i, n i = (MulAction.orbit G a).ncard)
    (hsub : ∀ I : Finset ι, i₀ ∈ I → j₀ ∈ I → (∑ i ∈ I, n i) ∣ (MulAction.orbit G a).ncard →
      I = Finset.univ)
    (X : Subgroup G) (hX : MulAction.stabilizer G a ≤ X)
    (hj : b j₀ ∈ MulAction.orbit X a) : X = ⊤ := by
  classical
  set H := MulAction.stabilizer G a with hH
  set O := MulAction.orbit G a with hO
  set T : ι → Set Ω := fun i => MulAction.orbit S (b i) with hT
  have hTO : ∀ i, T i ⊆ O := fun i => by
    refine (MulAction.orbit_subgroup_subset S (b i)).trans ?_
    rw [MulAction.orbit_eq_iff.2 (hbmem i)]
  have hTfin : ∀ i, (T i).Finite := fun i => hfin.subset (hTO i)
  have hdisj : Pairwise (Function.onFun Disjoint T) := fun i j hij => by
    rw [Function.onFun, Set.disjoint_left]
    intro z hzi hzj
    apply hne i j hij
    rw [← MulAction.orbit_eq_iff.2 hzi, ← MulAction.orbit_eq_iff.2 hzj]
  have hcov : (⋃ i, T i) = O := by
    apply Set.eq_of_subset_of_ncard_le (Set.iUnion_subset hTO) _ hfin
    rw [Set.ncard_iUnion_of_finite hTfin hdisj, finsum_eq_sum_of_fintype]
    simp only [hT, hn]
    exact hsumN.ge
  set Y : Set Ω := MulAction.orbit X a with hY
  have hYO : Y ⊆ O := MulAction.orbit_subgroup_subset X a
  have hSY : ∀ s ∈ S, ∀ y ∈ Y, s • y ∈ Y := by
    intro s hs y hy
    obtain ⟨x, rfl⟩ := hy
    refine ⟨⟨s * x, X.mul_mem (hX (hS hs)) x.2⟩, ?_⟩
    change (s * (x : G)) • a = s • (x : G) • a
    rw [mul_smul]
  set I : Finset ι := Finset.univ.filter fun i => b i ∈ Y with hI
  have hYI : Y = ⋃ i ∈ (I : Set ι), T i := by
    ext y
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    constructor
    · intro hy
      have hyO := hYO hy
      rw [← hcov] at hyO
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyO
      refine ⟨i, ?_, hi⟩
      rw [hI, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨s, rfl⟩ := hi
      have := hSY ((s : G)⁻¹) (S.inv_mem s.2) _ hy
      simpa [Subgroup.smul_def] using this
    · rintro ⟨i, hi, hy⟩
      have hi' : b i ∈ Y := by simpa [hI] using hi
      obtain ⟨s, rfl⟩ := hy
      exact hSY s s.2 (b i) hi'
  have hYcard : Y.ncard = ∑ i ∈ I, n i := by
    rw [hYI, Set.Finite.ncard_biUnion I.finite_toSet (fun i _ => hTfin i)
      (hdisj.set_pairwise _), finsum_mem_coe_finset]
    exact Finset.sum_congr rfl fun i _ => hn i
  have hrel : H.relIndex X = Y.ncard := by
    rw [Subgroup.relIndex, hH, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer]
  have hidx : Y.ncard * X.index = O.ncard := by
    rw [← hrel, ← MulAction.index_stabilizer G a, Subgroup.relIndex_mul_index hX]
  have hdvd : (∑ i ∈ I, n i) ∣ O.ncard := ⟨X.index, by rw [← hYcard, hidx]⟩
  have hi₀ : i₀ ∈ I := by
    rw [hI, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hb₀ ▸ MulAction.mem_orbit_self a⟩
  have hj₀ : j₀ ∈ I := by
    rw [hI, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hj⟩
  have hI2 := hsub I hi₀ hj₀ hdvd
  have hpos : O.ncard ≠ 0 :=
    ((Set.ncard_pos hfin).2 ⟨a, MulAction.mem_orbit_self a⟩).ne'
  have h1 : Y.ncard = O.ncard := by
    rw [hYcard, hI2, hsumN]
  rw [h1] at hidx
  exact Subgroup.index_eq_one.1 (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos)
    (hidx.trans (mul_one _).symm))

end Block

abbrev Piece : Type := Option (Option TableVIClass)

local instance instFintypeTableVIClass : Fintype TableVIClass :=
  ⟨{.two_A, .two_B, .four_B, .four_A, .three_A, .six_A}, by intro K; cases K <;> decide⟩

@[expose] def pieceSize : Piece → ℕ
  | none => 1
  | some none => 1
  | some (some K) => tableVISize K

theorem sum_pieceSize : ∑ i, pieceSize i = 27143910000 := by
  rw [Fintype.sum_option, Fintype.sum_option]
  decide +kernel

theorem piece_sub : ∀ I : Finset Piece, none ∈ I → some (some TableVIClass.two_A) ∈ I →
    (∑ i ∈ I, pieceSize i) ∣ 27143910000 → I = Finset.univ := by
  decide +kernel

section Basic

variable {G : Type} [Group G] {d₀ : B} {a₀ z₀ a : G}

theorem mul_self_eq_one_of_gmsF1Type (hG : GMSF1Type d₀ a₀ z₀) : a₀ * a₀ = 1 := by
  have h := pow_orderOf_eq_one a₀
  rwa [hG.1.1, pow_two] at h

theorem ne_one_of_gmsF1Type (hG : GMSF1Type d₀ a₀ z₀) : a₀ ≠ 1 := by
  intro h
  have h1 := hG.1.1
  rw [h, orderOf_one] at h1
  exact absurd h1 (by norm_num)

theorem mul_self_of_conj (hG : GMSF1Type d₀ a₀ z₀) (ha : IsConj a₀ a) : a * a = 1 :=
  mul_self_eq_one_of_isConj (mul_self_eq_one_of_gmsF1Type hG) ha

theorem ne_one_of_conj (hG : GMSF1Type d₀ a₀ z₀) (ha : IsConj a₀ a) : a ≠ 1 :=
  ne_one_of_isConj (ne_one_of_gmsF1Type hG) ha

theorem mem_twoANbr_of_adj (ha : IsConj a₀ a) {u : ConjVert a}
    (hu : (twoAGraph a).Adj (baseVertex a) u) : (u : G) ∈ twoANbr a₀ a :=
  ⟨ha.trans u.2, ha.trans hu.2⟩

theorem adj_of_mem_twoANbr (hG : GMSF1Type d₀ a₀ z₀) (ha : IsConj a₀ a) {u : ConjVert a}
    (hu : (u : G) ∈ twoANbr a₀ a) : (twoAGraph a).Adj (baseVertex a) u := by
  refine ⟨fun e => ?_, ha.symm.trans hu.2⟩
  have e' : a = (u : G) := congrArg Subtype.val e
  have h1 : IsConj a₀ (a * (u : G)) := hu.2
  rw [← e', mul_self_of_conj hG ha] at h1
  exact ne_one_of_gmsF1Type hG (isConj_one_right.1 h1.symm)

end Basic

section Local

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a₀ z₀ a : G}

theorem exists_smul_eq_of_adj
    (I : TableVIFacts d₀ G) (hG : GMSF1Type d₀ a₀ z₀)
    (ha : IsConj a₀ a) {u u' : ConjVert a} (hu : (twoAGraph a).Adj (baseVertex a) u)
    (hu' : (twoAGraph a).Adj (baseVertex a) u') :
    ∃ g ∈ Subgroup.centralizer ({a} : Set G), g • u = u' := by
  obtain ⟨g, hg, h⟩ := isConj_of_mem_twoANbr I.sls I.tableV I.leech hG ha
    (mem_twoANbr_of_adj ha hu) (mem_twoANbr_of_adj ha hu')
  exact ⟨g, hg, Subtype.ext h⟩

omit [Finite G] in
theorem mem_tableVIOrbit_of_longTri (ha : IsConj a₀ a) {x b c : ConjVert a}
    (h : longTri a x b c) :
    (c : G) ∈ tableVIOrbit a₀ z₀ (x : G) (b : G) TableVIClass.two_A := by
  obtain ⟨-, hbc, hcx, hne⟩ := h
  exact ⟨⟨⟨ha.trans c.2, ha.trans hbc.2⟩, fun e => hcx.1 (Subtype.ext e), hne⟩,
    ha.trans hcx.symm.2⟩

theorem exists_smul_eq_of_longTri
    (I : TableVIFacts d₀ G) (hG : GMSF1Type d₀ a₀ z₀)
    (ha : IsConj a₀ a) {x b c c' : ConjVert a} (hxb : (twoAGraph a).Adj x b)
    (h : longTri a x b c) (h' : longTri a x b c') :
    ∃ g ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ Subgroup.centralizer ({(b : G)} : Set G),
      g • c = c' := by
  obtain ⟨g, hg, e⟩ := s341_transitive I.sls I.tableV I.leech I.tableIII I.tableIVBaby
    I.threeSwap I.leechPair hG (ha.trans x.2) ⟨ha.trans b.2, ha.trans hxb.2⟩
    (mem_tableVIOrbit_of_longTri ha h) (mem_tableVIOrbit_of_longTri ha h')
  exact ⟨g, hg, Subtype.ext e⟩

theorem exists_smul_eq_of_longTri_base
    (I : TableVIFacts d₀ G) (hG : GMSF1Type d₀ a₀ z₀)
    (ha : IsConj a₀ a) {y z y' z' : ConjVert a} (h : longTri a (baseVertex a) y z)
    (h' : longTri a (baseVertex a) y' z') :
    ∃ g ∈ Subgroup.centralizer ({a} : Set G), g • y = y' ∧ g • z = z' := by
  obtain ⟨g₁, hg₁, e₁⟩ := exists_smul_eq_of_adj I hG ha h.1 h'.1
  have hfix : g₁ • baseVertex a = baseVertex a := (smul_eq_self_iff g₁ (baseVertex a)).2 hg₁
  have h1 : longTri a (baseVertex a) y' (g₁ • z) := by
    have := (longTri_smul g₁ (baseVertex a) y z).2 h
    rwa [hfix, e₁] at this
  obtain ⟨g₂, hg₂, e₂⟩ := exists_smul_eq_of_longTri I hG ha h'.1 h1 h'
  refine ⟨g₂ * g₁, Subgroup.mul_mem _ hg₂.1 hg₁, ?_, ?_⟩
  · rw [mul_smul, e₁]
    exact (smul_eq_self_iff g₂ y').2 hg₂.2
  · rw [mul_smul, e₂]

end Local

section Orbits

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a₀ z₀ a : G}

omit [Finite G] in
theorem mem_orbit_stabilizer_iff {w c u : ConjVert a} :
    u ∈ MulAction.orbit (MulAction.stabilizer ↥(Subgroup.centralizer ({a} : Set G)) w) c ↔
      ∃ g ∈ Subgroup.centralizer ({(w : G)} : Set G) ⊓ Subgroup.centralizer ({a} : Set G),
        g • c = u := by
  constructor
  · rintro ⟨s, rfl⟩
    have hs := s.2
    rw [MulAction.mem_stabilizer_iff] at hs
    exact ⟨((s : ↥(Subgroup.centralizer ({a} : Set G))) : G),
      ⟨(smul_eq_self_iff _ w).1 hs, (s : ↥(Subgroup.centralizer ({a} : Set G))).2⟩, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨⟨g, hg.2⟩, ?_⟩, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    exact (smul_eq_self_iff g w).2 hg.1

theorem orbit_eq_neighbours
    (I : TableVIFacts d₀ G) (hG : GMSF1Type d₀ a₀ z₀)
    (ha : IsConj a₀ a) {w : ConjVert a} (hw : (twoAGraph a).Adj (baseVertex a) w) :
    MulAction.orbit ↥(Subgroup.centralizer ({a} : Set G)) w =
      {u | (twoAGraph a).Adj (baseVertex a) u} := by
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    have h := twoAGraph_adj_smul (g : G) hw
    have hfix : (g : G) • baseVertex a = baseVertex a := (smul_eq_self_iff _ _).2 g.2
    rw [hfix] at h
    exact h
  · intro hu
    obtain ⟨g, hg, e⟩ := exists_smul_eq_of_adj I hG ha hw hu
    exact ⟨⟨g, hg⟩, e⟩

theorem ncard_neighbours
    (I : TableVIFacts d₀ G) (hG : GMSF1Type d₀ a₀ z₀)
    (ha : IsConj a₀ a) :
    {u : ConjVert a | (twoAGraph a).Adj (baseVertex a) u}.ncard = 27143910000 := by
  have h1 : {u : ConjVert a | (twoAGraph a).Adj (baseVertex a) u} =
      Subtype.val ⁻¹' twoANbr a₀ a := by
    ext u
    exact ⟨mem_twoANbr_of_adj ha, adj_of_mem_twoANbr hG ha⟩
  rw [h1, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
    (fun c hc => ⟨⟨c, ha.symm.trans hc.1⟩, rfl⟩)]
  exact table7_ncard I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap I.leechPair hG ha
    TableVIIClass.two_A

theorem exists_orbit_data
    (I : TableVIFacts d₀ G) (hG : GMSF1Type d₀ a₀ z₀) (ha : IsConj a₀ a)
    {w : ConjVert a} (hw : (twoAGraph a).Adj (baseVertex a) w) :
    ∃ b : Piece → ConjVert a, b none = w ∧ (∀ i, (twoAGraph a).Adj (baseVertex a) (b i)) ∧
      longTri a (baseVertex a) w (b (some (some TableVIClass.two_A))) ∧
      (∀ i, (MulAction.orbit (MulAction.stabilizer ↥(Subgroup.centralizer ({a} : Set G)) w)
        (b i)).ncard = pieceSize i) ∧
      ∀ i j, i ≠ j →
        MulAction.orbit (MulAction.stabilizer ↥(Subgroup.centralizer ({a} : Set G)) w) (b i) ≠
          MulAction.orbit (MulAction.stabilizer ↥(Subgroup.centralizer ({a} : Set G)) w) (b j) := by
  classical
  have ha2 : a * a = 1 := mul_self_of_conj hG ha
  have ha1 : a ≠ 1 := ne_one_of_conj hG ha
  have hx : IsConj a₀ (w : G) := ha.trans w.2
  have hcomm : a * (w : G) = w * a := adj_comm ha2 hw
  have hb : a ∈ twoANbr a₀ (w : G) := ⟨ha, by rw [← hcomm]; exact ha.trans hw.2⟩
  let T : TableVIClass → Set G := fun K => tableVIOrbit a₀ z₀ (w : G) a K
  have hTne : ∀ K, (T K).Nonempty := fun K => by
    apply Set.nonempty_of_ncard_ne_zero
    rw [s341_ncard I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hx hb K]
    exact (tableVISize_pos K).ne'
  have hTconj : ∀ K, ∀ c ∈ T K, IsConj a c := fun K c hc => ha.symm.trans hc.1.1.1
  let cK : TableVIClass → ConjVert a := fun K =>
    ⟨(hTne K).some, hTconj K _ (hTne K).some_mem⟩
  let wp : ConjVert a := shortMid a (baseVertex a) w
  have hwp : (wp : G) = a * w := shortMid_coe hw
  let b : Piece → ConjVert a := fun i => i.elim w (fun j => j.elim wp cK)
  let PK : TableVIClass → Set (ConjVert a) := fun K => Subtype.val ⁻¹' T K
  let piece : Piece → Set (ConjVert a) := fun i => i.elim {w} (fun j => j.elim {wp} PK)
  have horb_w : MulAction.orbit (MulAction.stabilizer ↥(Subgroup.centralizer ({a} : Set G)) w) w =
      {w} := by
    ext u
    rw [mem_orbit_stabilizer_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (smul_eq_self_iff g w).2 hg.1
    · rintro rfl
      exact ⟨1, Subgroup.one_mem _, one_smul _ _⟩
  have horb_wp : MulAction.orbit
      (MulAction.stabilizer ↥(Subgroup.centralizer ({a} : Set G)) w) wp = {wp} := by
    ext u
    rw [mem_orbit_stabilizer_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      have h1 : g • baseVertex a = baseVertex a := (smul_eq_self_iff g _).2 hg.2
      have h2 : g • w = w := (smul_eq_self_iff g w).2 hg.1
      have := shortMid_smul (a := a) g (baseVertex a) w
      rw [h1, h2] at this
      exact this.symm
    · rintro rfl
      exact ⟨1, Subgroup.one_mem _, one_smul _ _⟩
  have horb_K : ∀ K, ∀ c : ConjVert a, (c : G) ∈ T K →
      MulAction.orbit (MulAction.stabilizer ↥(Subgroup.centralizer ({a} : Set G)) w) c =
        PK K := by
    intro K c hc
    ext u
    rw [mem_orbit_stabilizer_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨TableVICtx.conj_mem hg hc.1, TableVICtx.cond_conj hg hc.2⟩
    · intro hu
      obtain ⟨g, hg, e⟩ := s341_transitive I.sls I.tableV I.leech I.tableIII I.tableIVBaby
        I.threeSwap I.leechPair hG hx hb hc hu
      exact ⟨g, hg, Subtype.ext e⟩
  have hpiece : ∀ i, MulAction.orbit
      (MulAction.stabilizer ↥(Subgroup.centralizer ({a} : Set G)) w) (b i) = piece i := by
    intro i
    rcases i with _ | _ | K
    · exact horb_w
    · exact horb_wp
    · exact horb_K K (cK K) (hTne K).some_mem
  have hw_not : ∀ K, w ∉ PK K := fun K h => h.1.2.1 rfl
  have hwp_not : ∀ K, wp ∉ PK K := fun K h => h.1.2.2 (by rw [hwp, hcomm])
  have hwwp : w ≠ wp := by
    intro e
    have e' : (w : G) = a * w := by rw [← hwp]; exact congrArg Subtype.val e
    exact ha1 (mul_right_cancel (e'.symm.trans (one_mul _).symm))
  have hcls : ∀ K K', K ≠ K' → Disjoint (PK K) (PK K') := fun K K' hKK' =>
    Set.disjoint_left.2 fun u hK hK' => hKK'
      ((s341_classify I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hx hb hK.1).unique
        hK.2 hK'.2)
  have hdisj : ∀ i j, i ≠ j → Disjoint (piece i) (piece j) := by
    intro i j hij
    rcases i with _ | _ | K <;> rcases j with _ | _ | K'
    · exact absurd rfl hij
    · exact Set.disjoint_singleton.2 hwwp
    · exact Set.disjoint_singleton_left.2 (hw_not K')
    · exact Set.disjoint_singleton.2 hwwp.symm
    · exact absurd rfl hij
    · exact Set.disjoint_singleton_left.2 (hwp_not K')
    · exact Set.disjoint_singleton_right.2 (hw_not K)
    · exact Set.disjoint_singleton_right.2 (hwp_not K)
    · exact hcls K K' (fun e => hij (by rw [e]))
  have hsize : ∀ i, (piece i).ncard = pieceSize i := by
    intro i
    rcases i with _ | _ | K
    · exact Set.ncard_singleton w
    · exact Set.ncard_singleton wp
    · show (Subtype.val ⁻¹' T K).ncard = tableVISize K
      rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
        (fun c hc => ⟨⟨c, hTconj K c hc⟩, rfl⟩)]
      exact s341_ncard I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hx hb K
  have hadj_K : ∀ K, (twoAGraph a).Adj (baseVertex a) (cK K) := fun K =>
    adj_of_mem_twoANbr hG ha (hTne K).some_mem.1.1
  have hadj : ∀ i, (twoAGraph a).Adj (baseVertex a) (b i) := by
    intro i
    rcases i with _ | _ | K
    · exact hw
    · exact adj_shortMid_left ha2 ha1 hw
    · exact hadj_K K
  have hlong : longTri a (baseVertex a) w (cK TableVIClass.two_A) := by
    have hc := (hTne TableVIClass.two_A).some_mem
    refine ⟨hw, ⟨fun e => hc.1.2.1 (congrArg Subtype.val e).symm, ha.symm.trans hc.2⟩,
      (hadj_K _).symm, ?_⟩
    show ((cK TableVIClass.two_A : ConjVert a) : G) ≠ a * w
    rw [hcomm]
    exact hc.1.2.2
  refine ⟨b, rfl, hadj, hlong, fun i => by rw [hpiece i]; exact hsize i, ?_⟩
  intro i j hij heq
  have hmem : b i ∈ piece i := by
    rw [← hpiece i]
    exact MulAction.mem_orbit_self _
  have hmem' : b i ∈ piece j := by
    rw [← hpiece j, ← heq]
    exact MulAction.mem_orbit_self _
  exact Set.disjoint_left.1 (hdisj i j hij) hmem hmem'

end Orbits

section Link

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a₀ z₀ a : G}

theorem link_of_interfaces
    (I : TableVIFacts d₀ G) (hG : GMSF1Type d₀ a₀ z₀)
    (ha : IsConj a₀ a) {w w' : ConjVert a} (hw : (twoAGraph a).Adj (baseVertex a) w)
    (hw' : (twoAGraph a).Adj (baseVertex a) w') :
    Relation.ReflTransGen (longTri a (baseVertex a)) w w' := by
  classical
  have ha2 : a * a = 1 := mul_self_of_conj hG ha
  have hfix : ∀ g : ↥(Subgroup.centralizer ({a} : Set G)), g • baseVertex a = baseVertex a :=
    fun g => (smul_eq_self_iff (g : G) (baseVertex a)).2 g.2
  have hRsmul : ∀ (g : ↥(Subgroup.centralizer ({a} : Set G))) (u v : ConjVert a),
      longTri a (baseVertex a) u v → longTri a (baseVertex a) (g • u) (g • v) := by
    intro g u v h
    have := (longTri_smul (g : G) (baseVertex a) u v).2 h
    have h2 := hfix g
    rw [Subgroup.smul_def] at h2
    rwa [h2] at this
  have hRsymm : ∀ u v : ConjVert a, longTri a (baseVertex a) u v →
      longTri a (baseVertex a) v u := by
    rintro u v ⟨h1, h2, h3, h4⟩
    refine ⟨h3.symm, h2.symm, h1.symm, fun e => h4 ?_⟩
    show (v : G) = a * u
    rw [show (u : G) = a * v from e, ← mul_assoc, ha2, one_mul]
  have hrtg : ∀ (g : ↥(Subgroup.centralizer ({a} : Set G))) (u v : ConjVert a),
      Relation.ReflTransGen (longTri a (baseVertex a)) (g • u) (g • v) ↔
        Relation.ReflTransGen (longTri a (baseVertex a)) u v := by
    intro g u v
    constructor
    · intro h
      have := Relation.ReflTransGen.lift (fun x => g⁻¹ • x)
        (fun x y hxy => hRsmul g⁻¹ x y hxy) _ _ h
      simpa [Function.onFun] using this
    · exact fun h => Relation.ReflTransGen.lift (fun x => g • x)
        (fun x y hxy => hRsmul g x y hxy) _ _ h
  have hrtg_symm : ∀ {u v : ConjVert a},
      Relation.ReflTransGen (longTri a (baseVertex a)) u v →
        Relation.ReflTransGen (longTri a (baseVertex a)) v u := by
    intro u v h
    have : Std.Symm (longTri a (baseVertex a)) := ⟨hRsymm⟩
    exact (Relation.ReflTransGen.stdSymm (r := longTri a (baseVertex a))).symm u v h
  have hY_adj : ∀ u, Relation.ReflTransGen (longTri a (baseVertex a)) w u →
      (twoAGraph a).Adj (baseVertex a) u := by
    intro u hu
    induction hu with
    | refl => exact hw
    | tail _ h _ => exact h.2.2.1.symm
  have hcongr : ∀ y, Relation.ReflTransGen (longTri a (baseVertex a)) w y → ∀ v,
      Relation.ReflTransGen (longTri a (baseVertex a)) w v ↔
        Relation.ReflTransGen (longTri a (baseVertex a)) y v := by
    intro y hwy v
    exact ⟨fun h => hrtg_symm hwy |>.trans h, fun h => hwy.trans h⟩
  let X : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    { carrier := {g | ∀ u : ConjVert a, Relation.ReflTransGen (longTri a (baseVertex a)) w u ↔
        Relation.ReflTransGen (longTri a (baseVertex a)) w (g • u)}
      mul_mem' := fun {g h} hg hh u => by
        rw [mul_smul]
        exact (hh u).trans (hg _)
      one_mem' := fun u => by rw [one_smul]
      inv_mem' := fun {g} hg u => by
        have := hg (g⁻¹ • u)
        rw [smul_inv_smul] at this
        exact this.symm }
  have hXmem : ∀ y, Relation.ReflTransGen (longTri a (baseVertex a)) w y →
      ∃ g : ↥(Subgroup.centralizer ({a} : Set G)), g • w = y ∧ g ∈ X := by
    intro y hy
    obtain ⟨g, hg, e⟩ := exists_smul_eq_of_adj I hG ha hw (hY_adj y hy)
    refine ⟨⟨g, hg⟩, e, fun u => ?_⟩
    have h1 := hrtg ⟨g, hg⟩ w u
    have e' : (⟨g, hg⟩ : ↥(Subgroup.centralizer ({a} : Set G))) • w = y := e
    rw [e'] at h1
    exact (h1.symm.trans (hcongr y hy _).symm)
  have hX : MulAction.stabilizer ↥(Subgroup.centralizer ({a} : Set G)) w ≤ X := by
    intro g hg u
    have h1 := hrtg g w u
    rw [MulAction.mem_stabilizer_iff.1 hg] at h1
    exact h1.symm
  obtain ⟨b, hb₀, hbadj, hlong, hn, hne⟩ := exists_orbit_data I hG ha hw
  have horb := orbit_eq_neighbours I hG ha hw
  have hXtop : X = ⊤ := by
    refine eq_top_of_orbit_partition w
      (MulAction.stabilizer ↥(Subgroup.centralizer ({a} : Set G)) w) le_rfl b pieceSize none
      (some (some TableVIClass.two_A)) hb₀ ?_ hn hne (Set.toFinite _) ?_ ?_ X hX ?_
    · intro i
      rw [horb]
      exact hbadj i
    · rw [horb, ncard_neighbours I hG ha, sum_pieceSize]
    · intro I' h0 h2 hd
      rw [horb, ncard_neighbours I hG ha] at hd
      exact piece_sub I' h0 h2 hd
    · obtain ⟨g, e, hgX⟩ := hXmem _ (Relation.ReflTransGen.single hlong)
      exact ⟨⟨g, hgX⟩, e⟩
  obtain ⟨g, hg, e⟩ := exists_smul_eq_of_adj I hG ha hw hw'
  have hgX : (⟨g, hg⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ X := by
    rw [hXtop]
    exact Subgroup.mem_top _
  have := (hgX w).1 Relation.ReflTransGen.refl
  have e' : (⟨g, hg⟩ : ↥(Subgroup.centralizer ({a} : Set G))) • w = w' := e
  rwa [e'] at this

end Link

section Generation

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a₀ z₀ : G}

theorem closure_centralizer_inf_eq
    (I : TableVIFacts d₀ G) (hG : GMSF1Type d₀ a₀ z₀) {p : G}
    (hp : IsConj a₀ p) {u₀ : ConjVert p} {s : G} (hs : s ∈ Subgroup.centralizer ({p} : Set G))
    (hlong : longTri p (baseVertex p) u₀ (s • u₀)) :
    Subgroup.closure (((Subgroup.centralizer ({p} : Set G) ⊓
        Subgroup.centralizer ({(u₀ : G)} : Set G) : Subgroup G) : Set G) ∪ {s}) =
      Subgroup.centralizer ({p} : Set G) := by
  classical
  set F : Subgroup G := Subgroup.closure (((Subgroup.centralizer ({p} : Set G) ⊓
        Subgroup.centralizer ({(u₀ : G)} : Set G) : Subgroup G) : Set G) ∪ {s}) with hF
  have hinf : Subgroup.centralizer ({p} : Set G) ⊓ Subgroup.centralizer ({(u₀ : G)} : Set G) ≤
      F := fun g hg => Subgroup.subset_closure (Or.inl hg)
  have hsF : s ∈ F := Subgroup.subset_closure (Or.inr rfl)
  have hFC : F ≤ Subgroup.centralizer ({p} : Set G) := by
    rw [hF, Subgroup.closure_le]
    rintro g (hg | rfl)
    · exact hg.1
    · exact hs
  have hfix : ∀ g ∈ Subgroup.centralizer ({p} : Set G), g • baseVertex p = baseVertex p :=
    fun g hg => (smul_eq_self_iff g (baseVertex p)).2 hg
  have hu₀ : (twoAGraph p).Adj (baseVertex p) u₀ := hlong.1
  have hrtg : ∀ u : ConjVert p, Relation.ReflTransGen (longTri p (baseVertex p)) u₀ u →
      ∃ k ∈ F, k • u₀ = u := by
    intro u hr
    induction hr with
    | refl => exact ⟨1, F.one_mem, one_smul _ _⟩
    | tail _ hbc ih =>
      obtain ⟨k, hk, rfl⟩ := ih
      rename_i b c _
      have h1 : longTri p (baseVertex p) u₀ (k⁻¹ • c) := by
        have := (longTri_smul k⁻¹ (baseVertex p) (k • u₀) c).2 hbc
        rwa [hfix _ (Subgroup.inv_mem _ (hFC hk)), inv_smul_smul] at this
      obtain ⟨e, he, hec⟩ := exists_smul_eq_of_longTri I hG hp hu₀ hlong h1
      refine ⟨k * e * s, F.mul_mem (F.mul_mem hk (hinf he)) hsF, ?_⟩
      rw [mul_smul, mul_smul, hec, smul_inv_smul]
  refine le_antisymm hFC fun g hg => ?_
  have hgu : (twoAGraph p).Adj (baseVertex p) (g • u₀) := by
    have := twoAGraph_adj_smul g hu₀
    rwa [hfix g hg] at this
  obtain ⟨k, hk, e⟩ := hrtg _ (link_of_interfaces I hG hp hu₀ hgu)
  have hmem : k⁻¹ * g ∈ Subgroup.centralizer ({p} : Set G) ⊓
      Subgroup.centralizer ({(u₀ : G)} : Set G) := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hFC hk)) hg, ?_⟩
    refine (smul_eq_self_iff (k⁻¹ * g) u₀).1 ?_
    rw [mul_smul, ← e, inv_smul_smul]
  have h2 := hinf hmem
  have h3 := F.mul_mem hk h2
  rwa [mul_inv_cancel_left] at h3

end Generation

section TriMax

variable {G : Type} [Group G]

theorem map_conj_centralizer (g a : G) :
    (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
      _ = g * (a * y) * g⁻¹ := by rw [hy]
      _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : g * (g⁻¹ * x * g * a) * g⁻¹ = g * (a * (g⁻¹ * x * g)) * g⁻¹ :=
        calc g * (g⁻¹ * x * g * a) * g⁻¹ = x * (g * a * g⁻¹) := by group
          _ = g * a * g⁻¹ * x := hx
          _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

@[expose] def TriMax (x y z : G) : Prop :=
  ∀ F : Subgroup G,
    Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y} ⊓ Subgroup.centralizer {z} ≤ F →
    F ≤ Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y} →
      F = Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y} ⊓ Subgroup.centralizer {z} ∨
      F = Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y}

theorem TriMax.conj {x y z : G} (h : TriMax x y z) (g : G) :
    TriMax (g * x * g⁻¹) (g * y * g⁻¹) (g * z * g⁻¹) := by
  intro F hPF hFE
  set φ : G →* G := (MulAut.conj g).toMonoidHom with hφ
  have hmapcomap : ∀ K : Subgroup G, (K.comap φ).map φ = K := fun K =>
    Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective K
  have hcomapmap : ∀ K : Subgroup G, (K.map φ).comap φ = K := fun K =>
    Subgroup.comap_map_eq_self_of_injective (MulAut.conj g).injective K
  have hE : (Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y}).map φ =
      Subgroup.centralizer {g * x * g⁻¹} ⊓ Subgroup.centralizer {g * y * g⁻¹} := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hφ, map_conj_centralizer,
      map_conj_centralizer]
  have hP : (Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y} ⊓
      Subgroup.centralizer {z}).map φ =
      Subgroup.centralizer {g * x * g⁻¹} ⊓ Subgroup.centralizer {g * y * g⁻¹} ⊓
        Subgroup.centralizer {g * z * g⁻¹} := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hφ, map_conj_centralizer,
      map_conj_centralizer, map_conj_centralizer]
  have h1 : Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y} ⊓ Subgroup.centralizer {z} ≤
      F.comap φ := by
    rw [← hcomapmap (Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y} ⊓
      Subgroup.centralizer {z}), hP]
    exact Subgroup.comap_mono hPF
  have h2 : F.comap φ ≤ Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y} := by
    rw [← hcomapmap (Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y}), hE]
    exact Subgroup.comap_mono hFE
  rcases h _ h1 h2 with h3 | h3
  · left
    rw [← hmapcomap F, h3, hP]
  · right
    rw [← hmapcomap F, h3, hE]

theorem eq_or_eq_of_map_maximal {Q : Type*} [Group Q] {E P : Subgroup G} (f : ↥E →* Q)
    (hker : f.ker ≤ P.subgroupOf E)
    (hmax : ∀ B : Subgroup Q, (P.subgroupOf E).map f < B → B ≤ f.range → B = f.range)
    {F : Subgroup G} (hPF : E ⊓ P ≤ F) (hFE : F ≤ E) : F = E ⊓ P ∨ F = E := by
  have hAF : P.subgroupOf E ≤ F.subgroupOf E := fun g hg => hPF ⟨g.2, hg⟩
  by_cases hlt : P.subgroupOf E < F.subgroupOf E
  · right
    have hnot : ¬ (F.subgroupOf E).map f ≤ (P.subgroupOf E).map f := by
      intro hle
      have : F.subgroupOf E ≤ P.subgroupOf E := by
        intro g hg
        obtain ⟨a, ha, hag⟩ := hle (Subgroup.mem_map_of_mem f hg)
        have hk : a⁻¹ * g ∈ f.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hag, inv_mul_cancel]
        have h3 := (P.subgroupOf E).mul_mem ha (hker hk)
        rwa [mul_inv_cancel_left] at h3
      exact absurd hlt (not_lt_of_ge this)
    have h1 : (P.subgroupOf E).map f < (F.subgroupOf E).map f :=
      lt_of_le_of_ne (Subgroup.map_mono hAF) fun h => hnot (le_of_eq h.symm)
    have h2 : (F.subgroupOf E).map f = f.range := hmax _ h1 (by
      rw [Subgroup.map_le_iff_le_comap]
      exact fun g _ => ⟨g, rfl⟩)
    have h3 : F.subgroupOf E = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hg : f g ∈ (F.subgroupOf E).map f := by rw [h2]; exact ⟨g, rfl⟩
      obtain ⟨k, hk, hkg⟩ := hg
      have hkg' : k⁻¹ * g ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
      have h5 := (F.subgroupOf E).mul_mem hk (hAF (hker hkg'))
      rwa [mul_inv_cancel_left] at h5
    refine le_antisymm hFE fun g hg => ?_
    have hmem : (⟨g, hg⟩ : ↥E) ∈ F.subgroupOf E := by rw [h3]; exact Subgroup.mem_top _
    exact hmem
  · left
    have hFA : F.subgroupOf E = P.subgroupOf E := (eq_of_le_of_not_lt hAF hlt).symm
    refine le_antisymm (fun g hg => ?_) hPF
    have hgE : g ∈ E := hFE hg
    have hmem : (⟨g, hgE⟩ : ↥E) ∈ F.subgroupOf E := hg
    rw [hFA] at hmem
    exact ⟨hgE, hmem⟩

theorem triMax_of_map_maximal {Q : Type*} [Group Q] (x y z : G)
    (f : ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) →* Q)
    (hker : f.ker ≤ (Subgroup.centralizer ({z} : Set G)).subgroupOf
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)))
    (hmax : ∀ B : Subgroup Q, ((Subgroup.centralizer ({z} : Set G)).subgroupOf
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G))).map f < B →
        B ≤ f.range → B = f.range) :
    TriMax x y z :=
  fun _ hPF hFE => eq_or_eq_of_map_maximal f hker hmax hPF hFE

theorem TriMax.smul {a : G} {x y z : ConjVert a} (h : TriMax (x : G) y z) (g : G) :
    TriMax ((g • x : ConjVert a) : G) ((g • y : ConjVert a) : G) ((g • z : ConjVert a) : G) :=
  h.conj g

theorem triMax_of_longTri
    [Finite G] {d₀ : B} {a₀ z₀ a : G} (I : TableVIFacts d₀ G)
    (hG : GMSF1Type d₀ a₀ z₀) (ha : IsConj a₀ a) {x y z x' y' z' : ConjVert a}
    (h : longTri a x y z) (h' : longTri a x' y' z') (hm : TriMax (x : G) y z) :
    TriMax (x' : G) y' z' := by
  obtain ⟨k, hk⟩ := exists_smul_baseVertex_eq x
  obtain ⟨k', hk'⟩ := exists_smul_baseVertex_eq x'
  have hxy : longTri a (baseVertex a) (k⁻¹ • y) (k⁻¹ • z) := by
    have := (longTri_smul k⁻¹ x y z).2 h
    rwa [← hk, inv_smul_smul] at this
  have hxy' : longTri a (baseVertex a) (k'⁻¹ • y') (k'⁻¹ • z') := by
    have := (longTri_smul k'⁻¹ x' y' z').2 h'
    rwa [← hk', inv_smul_smul] at this
  obtain ⟨g, hg, hg1, hg2⟩ := exists_smul_eq_of_longTri_base I hG ha hxy hxy'
  have hfix : g • baseVertex a = baseVertex a := (smul_eq_self_iff g (baseVertex a)).2 hg
  have s1 := hm.smul k⁻¹
  rw [show k⁻¹ • x = baseVertex a from inv_smul_eq_iff.2 hk.symm] at s1
  have s2 := s1.smul g
  rw [hfix, hg1, hg2] at s2
  have s3 := s2.smul k'
  rw [hk', smul_inv_smul, smul_inv_smul] at s3
  exact s3

end TriMax

end CFSG.Monster.Tri.CoverG
