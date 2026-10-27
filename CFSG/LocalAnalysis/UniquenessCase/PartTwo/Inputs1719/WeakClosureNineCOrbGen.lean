module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNLift
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914

open CFSG.Quasithin CFSG.Open Subgroup

section Transport

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] {ι : G₁ →* G₂}

theorem nineFrattini_map (hι : Function.Injective ι) (Z : Subgroup G₁) :
    (nineFrattini Z).map ι = nineFrattini (Z.map ι) := by
  unfold nineFrattini
  rw [← NFW.map_frattini_mulEquiv (Z.equivMapOfInjective _ hι), map_map, map_map]
  rfl

theorem mem_normalizer_map_iff (hι : Function.Injective ι) {H : Subgroup G₁} {t : G₁} :
    ι t ∈ normalizer ((H.map ι : Subgroup G₂) : Set G₂) ↔ t ∈ normalizer (H : Set G₁) :=
  ⟨NFA6.mem_normalizer_of_map hι, NFA6.mem_normalizer_map⟩

theorem irredOnFrattiniQuot_map_iff (hι : Function.Injective ι) {S Z : Subgroup G₁} :
    IrredOnFrattiniQuot (S.map ι) (Z.map ι) ↔ IrredOnFrattiniQuot S Z := by
  rw [IrredOnFrattiniQuot, IrredOnFrattiniQuot, ← nineFrattini_map hι,
    map_lt_map_iff_of_injective hι]
  refine and_congr_right fun _ => ⟨fun h W hΦW hWZ hW => ?_, fun h W hΦW hWZ hW => ?_⟩
  · have hinv : ∀ s ∈ S.map ι ⊓ normalizer ((Z.map ι : Subgroup G₂) : Set G₂),
        ∀ y ∈ W.map ι, s * y * s⁻¹ ∈ W.map ι := by
      rintro _ ⟨⟨s, hs, rfl⟩, hsN⟩ _ ⟨w, hw, rfl⟩
      refine ⟨s * w * s⁻¹, hW s ⟨hs, (mem_normalizer_map_iff hι).1 hsN⟩ w hw, ?_⟩
      simp [map_mul, map_inv]
    rcases h (W.map ι) (map_mono hΦW) (map_mono hWZ) hinv with h1 | h1
    · exact Or.inl (map_injective hι h1)
    · exact Or.inr (map_injective hι h1)
  · obtain ⟨W₀, rfl⟩ : ∃ W₀ : Subgroup G₁, W = W₀.map ι :=
      ⟨W.comap ι, (map_comap_eq_self (hWZ.trans (map_le_range ι Z))).symm⟩
    rw [map_le_map_iff_of_injective hι] at hΦW hWZ
    have hinv : ∀ s ∈ S ⊓ normalizer (Z : Set G₁), ∀ y ∈ W₀, s * y * s⁻¹ ∈ W₀ := by
      intro s hs w hw
      have h1 := hW (ι s) ⟨mem_map_of_mem ι hs.1, (mem_normalizer_map_iff hι).2 hs.2⟩ (ι w)
        (mem_map_of_mem ι hw)
      rwa [← map_inv, ← map_mul, ← map_mul, mem_map_iff_mem hι] at h1
    rcases h W₀ hΦW hWZ hinv with h1 | h1
    · exact Or.inl (by rw [h1])
    · exact Or.inr (by rw [h1])

theorem oTwoPTwo_map_iff (hι : Function.Injective ι) {K : Subgroup G₁} {p : ℕ} :
    E1.oTwoPTwo ↥(K.map ι) p = ⊤ ↔ E1.oTwoPTwo ↥K p = ⊤ := by
  rw [← E1.oTwoPTwo_map_mulEquiv (K.equivMapOfInjective ι hι) p]
  exact E1.map_eq_top_iff_mulEquiv _ _

theorem twoPTwoIrred_map_iff (hι : Function.Injective ι) {K S Z : Subgroup G₁} {p : ℕ} :
    TwoPTwoIrred (K.map ι) (S.map ι) (Z.map ι) p ↔ TwoPTwoIrred K S Z p :=
  ⟨fun h => ⟨⟨h.prime, h.odd, (oTwoPTwo_map_iff hι).1 h.oTwoPTwo,
      (E1.isSylowIn_map_of_injective hι).1 h.sylowTwo,
      (E1.isSylowIn_map_of_injective hι).1 h.sylowP⟩, (irredOnFrattiniQuot_map_iff hι).1 h.irred⟩,
    fun h => ⟨⟨h.prime, h.odd, (oTwoPTwo_map_iff hι).2 h.oTwoPTwo,
      (E1.isSylowIn_map_of_injective hι).2 h.sylowTwo,
      (E1.isSylowIn_map_of_injective hι).2 h.sylowP⟩, (irredOnFrattiniQuot_map_iff hι).2 h.irred⟩⟩

theorem isElemAbelian_comap (hι : Function.Injective ι) {p : ℕ} {Z : Subgroup G₂}
    (h : IsElemAbelian p Z) : IsElemAbelian p (Z.comap ι) := by
  have := h.1
  refine ⟨⟨⟨fun a b => Subtype.ext (hι ?_)⟩⟩, fun x hx => hι ?_⟩
  · have hc := congrArg Subtype.val (mul_comm' (⟨ι a, a.2⟩ : Z) ⟨ι b, b.2⟩)
    simpa using hc
  · rw [map_pow, h.2 _ hx, map_one]

end Transport

theorem nineFrattini_eq_bot {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Z : Subgroup G} (hZ : IsElemAbelian p Z) : nineFrattini Z = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : CFSG.IsElementaryAbelian p Z := hZ.isElementaryAbelian
  have : Fact (IsPGroup p Z) := ⟨hZ.isPGroup⟩
  rw [nineFrattini, CFSG.frattini_eq_bot_of_isElementaryAbelian (p := p), Subgroup.map_bot]

theorem index_pi_dep {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Group (β i)]
    (K : ∀ i, Subgroup (β i)) : (Subgroup.pi Set.univ K).index = ∏ i, (K i).index := by
  simp_rw [index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

section Family

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι] [DecidableEq ι] {H : ι → Subgroup G}
  (hc : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
include hc

omit [DecidableEq ι] in
theorem noncommPiCoprod_mem_of {K : Subgroup G} (f : ∀ i, H i) (hf : ∀ i, (f i : G) ∈ K) :
    noncommPiCoprod hc f ∈ K := by
  rw [noncommPiCoprod_apply]
  exact noncommProd_mem K _ fun i _ => hf i

omit [DecidableEq ι] in
theorem exists_noncommPiCoprod_eq {x : G} (hx : x ∈ ⨆ i, H i) :
    ∃ f : ∀ i, H i, noncommPiCoprod hc f = x := by
  rw [← noncommPiCoprod_range (hcomm := hc)] at hx
  exact hx

theorem noncommPiCoprod_eq_mul_update (f : ∀ i, H i) (k : ι) :
    noncommPiCoprod hc f = (f k : G) * noncommPiCoprod hc (Function.update f k 1) := by
  have hf : Pi.mulSingle k (f k) * Function.update f k 1 = f := by
    funext j
    by_cases h : j = k
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]
  conv_lhs => rw [← hf]
  rw [map_mul, noncommPiCoprod_mulSingle]

theorem commute_noncommPiCoprod_update (f : ∀ i, H i) (k : ι) {y : G}
    (hy : ∀ j, j ≠ k → ∀ x ∈ H j, Commute y x) :
    Commute y (noncommPiCoprod hc (Function.update f k 1)) := by
  have h : noncommPiCoprod hc (Function.update f k 1) ∈ centralizer {y} := by
    refine noncommPiCoprod_mem_of hc _ fun j => ?_
    by_cases hj : j = k
    · subst hj
      simp
    · rw [Function.update_of_ne hj, mem_centralizer_singleton_iff]
      exact (hy j hj _ (f j).2).symm.eq
  exact (mem_centralizer_singleton_iff.mp h).symm

theorem map_pi_eq_iSup {P : ι → Subgroup G} (hP : ∀ i, P i ≤ H i) :
    (Subgroup.pi Set.univ fun i => (P i).subgroupOf (H i)).map (noncommPiCoprod hc) =
      ⨆ i, P i := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact noncommPiCoprod_mem_of hc f fun i => mem_iSup_of_mem i (hf i (Set.mem_univ i))
  · refine iSup_le fun i x hx => ⟨Pi.mulSingle i ⟨x, hP i hx⟩, fun j _ => ?_,
      noncommPiCoprod_mulSingle _ _⟩
    by_cases h : j = i
    · subst h
      simpa [mem_subgroupOf] using hx
    · simp [Pi.mulSingle_eq_of_ne h]

theorem not_dvd_relIndex_iSup {q : ℕ} (hq : q.Prime) {P : ι → Subgroup G}
    (hP : ∀ i, P i ≤ H i) (h : ∀ i, ¬ q ∣ (P i).relIndex (H i)) :
    ¬ q ∣ (⨆ i, P i).relIndex (⨆ i, H i) := by
  have h1 := map_pi_eq_iSup hc hP
  have h2 : (⊤ : Subgroup (∀ i, H i)).map (noncommPiCoprod hc) = ⨆ i, H i := by
    rw [← MonoidHom.range_eq_map, noncommPiCoprod_range]
  rw [← h1, ← h2, relIndex_map_map, top_sup_eq, relIndex_top_right]
  intro hd
  have h3 := hd.trans (index_dvd_of_le le_sup_left)
  rw [index_pi_dep] at h3
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hq.prime _).1 h3
  exact h i hi

omit [DecidableEq ι] in
theorem isElemAbelian_iSup {p : ℕ} (h : ∀ i, IsElemAbelian p (H i)) :
    IsElemAbelian p (⨆ i, H i) := by
  rw [← noncommPiCoprod_range (hcomm := hc)]
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, f, rfl⟩ := a
    obtain ⟨_, g, rfl⟩ := b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    funext i
    have := (h i).1
    exact mul_comm' (f i) (g i)
  · rintro _ ⟨f, rfl⟩
    rw [← map_pow]
    convert map_one (noncommPiCoprod hc)
    funext i
    exact Subtype.ext ((h i).2 _ (f i).2)

end Family

section Conj

variable {X : Type} [Group X]

theorem conjSub_eq_of_mem_normalizer {n : X} {M : Subgroup X}
    (hn : n ∈ normalizer (M : Set X)) : conjSub n M = M :=
  mem_normalizer_iff_map_conj_eq.mp hn

theorem conjSub_eq_of_mem {g : X} {M : Subgroup X} (hg : g ∈ M) : conjSub g M = M :=
  conjSub_eq_of_mem_normalizer (le_normalizer hg)

@[expose] def orb (C M : Subgroup X) : Subgroup X := ⨆ c : C, conjSub (c : X) M

theorem conjSub_le_orb {C M : Subgroup X} {c : X} (hc : c ∈ C) : conjSub c M ≤ orb C M :=
  le_iSup (fun c : C => conjSub (c : X) M) ⟨c, hc⟩

theorem le_orb (C M : Subgroup X) : M ≤ orb C M := by
  have := conjSub_le_orb (M := M) C.one_mem
  rwa [conjSub_one] at this

theorem orb_le {C M K : Subgroup X} (h : ∀ c ∈ C, conjSub c M ≤ K) : orb C M ≤ K :=
  iSup_le fun c => h c c.2

theorem orb_mono {C M M' : Subgroup X} (h : M ≤ M') : orb C M ≤ orb C M' :=
  orb_le fun _ hc => (conjSub_mono _ h).trans (conjSub_le_orb hc)

theorem orb_sup (C M M' : Subgroup X) : orb C (M ⊔ M') = orb C M ⊔ orb C M' := by
  simp only [orb, conjSub_sup]
  exact iSup_sup_eq

@[expose] def PermBy (C Nm : Subgroup X) (g : X) : Prop :=
  ∀ i ∈ C, ∃ j ∈ C, ∃ n ∈ Nm, g * i = j * n

theorem PermBy.mono {C Nm Nm' : Subgroup X} (h : Nm ≤ Nm') {g : X} (hg : PermBy C Nm g) :
    PermBy C Nm' g := fun i hi => by
  obtain ⟨j, hj, n, hn, he⟩ := hg i hi
  exact ⟨j, hj, n, h hn, he⟩

theorem permBy_of_mem {C Nm : Subgroup X} {g : X} (hg : g ∈ C) : PermBy C Nm g :=
  fun i hi => ⟨g * i, C.mul_mem hg hi, 1, Nm.one_mem, (mul_one _).symm⟩

theorem conjSub_orb_le {C M Nm : Subgroup X} (hNm : Nm ≤ normalizer (M : Set X)) {g : X}
    (hg : PermBy C Nm g) : conjSub g (orb C M) ≤ orb C M := by
  rw [orb, conjSub, Subgroup.map_iSup]
  refine iSup_le fun i => ?_
  obtain ⟨j, hj, n, hn, he⟩ := hg i i.2
  have h : (conjSub (i : X) M).map (MulAut.conj g).toMonoidHom = conjSub j M := by
    rw [← conjSub, ← conjSub_mul, he, conjSub_mul, conjSub_eq_of_mem_normalizer (hNm hn)]
  rw [h]
  exact conjSub_le_orb hj

theorem le_normalizer_orb {C M Nm T : Subgroup X} (hNm : Nm ≤ normalizer (M : Set X))
    (hT : ∀ t ∈ T, PermBy C Nm t) : T ≤ normalizer (orb C M : Set X) :=
  NFW.le_normalizer_of_conj_mem fun t ht _ hx => conjSub_orb_le hNm (hT t ht) (mul_mem_conjSub hx)

end Conj

end CFSG.LocalAnalysis.WeakClosure81.TC914
