module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

theorem IsComp.eq_of_mem {m : Fin 6} {P : Root m → Prop} {c c' : Finset (Root m)}
    (hc : IsComp m P c) (hc' : IsComp m P c') {i : Root m} (hi : i ∈ c) (hi' : i ∈ c') :
    c = c' := by
  classical
  have aux : ∀ {c c' : Finset (Root m)}, IsComp m P c → IsComp m P c' →
      i ∈ c → i ∈ c' → c ⊆ c' := by
    intro c c' hc hc' hi hi'
    let T := c.filter (fun x => x ∈ c')
    have hTsub : T ⊆ c := fun _ hx => (Finset.mem_filter.mp hx).1
    have hTnon : T.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hi'⟩⟩
    have hTclosed : ∀ x ∈ T, ∀ y ∈ c, Adj m x y → y ∈ T := by
      intro x hx y hy hxy
      have hx' : x ∈ c' := (Finset.mem_filter.mp hx).2
      have hy' : y ∈ c' := hc'.2.2.1 x hx' y (hc.2.1 y hy) hxy
      exact Finset.mem_filter.mpr ⟨hy, hy'⟩
    have hTc : T = c := hc.2.2.2 T hTsub hTnon hTclosed
    rw [← hTc]
    exact fun _ hx => (Finset.mem_filter.mp hx).2
  exact Finset.Subset.antisymm (aux hc hc' hi hi') (aux hc' hc hi' hi)

end CFSG.StandardType.GGQ2Frame.ExcRaw

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav CFSG.StandardType.TableCRes

noncomputable section

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
  {T₀ : Subgroup (ModGL τ L)} {m : Fin 6}

theorem exists_family_of_le_fullThreeTorus {A : Subgroup (ModGL τ L)}
    (hA : A ≤ fullThreeTorus S) :
    ∃ a : ↥A → Fin τ.rank → Lˣ, (∀ u, rootDiagUnit τ (a u) = u) ∧
      (∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) ∧ ∀ u j, a u j ^ 3 = 1 := by
  have key : ∀ u : ↥A, ∃ b : Fin τ.rank → Lˣ, rootDiagUnit τ b = u := by
    intro u
    have hu : (u : ModGL τ L) ∈ torusGroup τ L :=
      (inf_le_left : S.D.torus ≤ torusGroup τ L) (hA u.2).1
    obtain ⟨b, hb⟩ :=
      CFSG.RankThree.PartOne.KFU.exists_eq_rootDiagUnit_of_mem_torusGroup (K := L) hu
    exact ⟨b, hb.symm⟩
  choose a ha using key
  refine ⟨a, ha, ?_, ?_⟩
  · intro u
    rw [ha u]
    exact (hA u.2).1
  · intro u
    exact pow_eq_one_of_rootDiagUnit_pow (a := a u) (p := 3) (by
      rw [ha u]
      exact (hA u.2).2)

theorem exists_excFamily (d : ExcCoordDatum S T₀ m) {A : Subgroup (ModGL τ L)} (hA : A ≤ T₀) :
    ∃ a : ↥A → Fin τ.rank → Lˣ, (∀ u, rootDiagUnit τ (a u) = u) ∧
      (∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) ∧ ∀ u j, a u j ^ 3 = 1 :=
  exists_family_of_le_fullThreeTorus (hA.trans d.le_fullThreeTorus)

omit [IsAlgClosed L] in
theorem centralizer_range_excFamily {A : Subgroup (ModGL τ L)} {a : ↥A → Fin τ.rank → Lˣ}
    (ha : ∀ u, rootDiagUnit τ (a u) = u) :
    Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) =
      Subgroup.centralizer (A : Set (ModGL τ L)) := by
  have h : Set.range (fun u : ↥A => rootDiagUnit τ (a u)) = (A : Set (ModGL τ L)) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      show rootDiagUnit τ (a u) ∈ (A : Set (ModGL τ L))
      rw [ha u]
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, ha ⟨x, hx⟩⟩
  rw [h]

theorem rootChar_excFamily_eq_one_iff (d : ExcCoordDatum S T₀ m) {A : Subgroup (ModGL τ L)}
    (hA : A ≤ T₀) {a : ↥A → Fin τ.rank → Lˣ} (ha : ∀ u, rootDiagUnit τ (a u) = u)
    (i : ExcRaw.Root m) :
    (∀ u, rootChar (a u) (d.γ i) = 1) ↔
      ExcRaw.Vanish m (ggLinImage (p := 3) d.coord A) i := by
  have hord : orderOf d.ζ = 3 := by
    rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd (orderOf d.ζ)
      (orderOf_dvd_of_pow_eq_one d.ζ_pow_three) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) d.ζ_ne_one
    · exact h
  have hζ : ∀ k : ZMod 3, d.ζ ^ k.val = 1 ↔ k = 0 := by
    intro k
    rw [← orderOf_dvd_iff_pow_eq_one, hord, ← ZMod.val_eq_zero]
    exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt k), fun h => by
      rw [h]
      exact dvd_zero 3⟩
  constructor
  · intro h v hv
    let t : ↥T₀ := Additive.toMul (d.coord.symm v)
    have hvA : (t : ModGL τ L) ∈ A := (mem_ggLinImage d.coord A v).1 hv
    let u : ↥A := ⟨t, hvA⟩
    have htu : (t : ModGL τ L) = rootDiagUnit τ (a u) := (ha u).symm
    have htv : d.coord (Additive.ofMul t) = v := by simp [t]
    have h1 := d.rootChar_eq t (a u) htu i
    have h2 : d.ζ ^ (ExcRaw.root m i v).val = 1 := by
      rw [← htv, ← h1]
      exact h u
    exact (hζ (ExcRaw.root m i v)).1 h2
  · intro h u
    let t : ↥T₀ := ⟨u, hA u.2⟩
    have htu : (t : ModGL τ L) = rootDiagUnit τ (a u) := (ha u).symm
    have hmem : d.coord (Additive.ofMul t) ∈ ggLinImage (p := 3) d.coord A :=
      (ofMul_mem_ggLinImage (p := 3) d.coord A t).2 (by
        show (t : ModGL τ L) ∈ A
        exact u.2)
    rw [d.rootChar_eq t (a u) htu i, h (d.coord (Additive.ofMul t)) hmem]
    exact (hζ 0).2 rfl

theorem ExcCoordDatum.adj_iff_iform_ne_zero (d : ExcCoordDatum S T₀ m) (i j : ExcRaw.Root m) :
    ExcRaw.Adj m i j ↔ iform (d.γ i) (d.γ j) ≠ 0 := by
  have key : ∀ (β v : Fin τ.rank → ℤ), IsRoot τ β →
      (corootPair β v ≠ 0 ↔ iform β v ≠ 0) := by
    intro β v hβ
    have hpos := iform_self_pos_of_isRoot hβ
    constructor
    · intro h h0
      have hm := corootPair_mul hβ v
      rw [h0, mul_zero] at hm
      exact h ((mul_eq_zero.mp hm).resolve_right hpos.ne')
    · intro h h0
      apply h
      have hm := corootPair_mul hβ v
      rw [h0, zero_mul] at hm
      omega
  have h1 : ExcRaw.pairing m i j ≠ 0 ↔ iform (d.γ j) (d.γ i) ≠ 0 := by
    rw [d.pairing_eq i j]
    exact key (d.γ j) (d.γ i) (d.isRoot j)
  have h2 : ExcRaw.pairing m j i ≠ 0 ↔ iform (d.γ i) (d.γ j) ≠ 0 := by
    rw [d.pairing_eq j i]
    exact key (d.γ i) (d.γ j) (d.isRoot i)
  rw [ExcRaw.Adj, h1, h2, ← iform_comm (d.γ j) (d.γ i)]
  tauto

theorem exists_occurs_of_kernelComponent (d : ExcCoordDatum S T₀ m) {A : Subgroup (ModGL τ L)}
    (hA : A ≤ T₀) {a : ↥A → Fin τ.rank → Lˣ} (ha : ∀ u, rootDiagUnit τ (a u) = u)
    (j : KernelComponent (famCharHom a)) :
    ∃ c : Finset (ExcRaw.Root m), ExcRaw.occurs m (ggLinImage (p := 3) d.coord A) c ∧
      componentRoots (famCharHom a) j = codeRoots d.γ c := by
  classical
  let χ := famCharHom a
  set U := ggLinImage (p := 3) d.coord A with hU
  have hker : ∀ i : ExcRaw.Root m, d.γ i ∈ kernelRoots χ ↔ ExcRaw.Vanish m U i := by
    intro i
    change d.γ i ∈ kernelRoots (famCharHom a) ↔ ExcRaw.Vanish m U i
    rw [mem_kernelRoots_famChar, hU, rootChar_excFamily_eq_one_iff d hA ha i]
    exact ⟨fun h => h.2, fun h => ⟨d.isRoot i, h⟩⟩
  let c : Finset (ExcRaw.Root m) := Finset.univ.filter (fun i => d.γ i ∈ componentRoots χ j)
  have hmem : ∀ i : ExcRaw.Root m, i ∈ c ↔ d.γ i ∈ componentRoots χ j := by
    intro i
    simp [c]
  have hne : c.Nonempty := by
    obtain ⟨α, hαj⟩ := Quotient.exists_rep j
    obtain ⟨i, hi | hi⟩ := d.exists_eq α.1 α.2.1
    · refine ⟨i, (hmem i).2 ?_⟩
      rw [← hi]
      exact ⟨α.2, hαj⟩
    · refine ⟨i, (hmem i).2 ?_⟩
      have hn : -α.1 ∈ componentRoots χ j :=
        (isRootComponent_componentRoots (χ := χ) j).neg_mem α.1 ⟨α.2, hαj⟩
      have hγ : d.γ i = -α.1 := by rw [hi, neg_neg]
      rw [hγ]
      exact hn
  have hsub : ∀ i ∈ c, ExcRaw.Vanish m U i := by
    intro i hi
    obtain ⟨h, _⟩ := (hmem i).1 hi
    exact (hker i).1 h
  have hclosed : ∀ i ∈ c, ∀ j' : ExcRaw.Root m,
      ExcRaw.Vanish m U j' → ExcRaw.Adj m i j' → j' ∈ c := by
    intro i hi j' hj' hadj
    rw [hmem j']
    obtain ⟨hiK, hiJ⟩ := (hmem i).1 hi
    have hjK : d.γ j' ∈ kernelRoots χ := (hker j').2 hj'
    have hne' : iform (d.γ i) (d.γ j') ≠ 0 :=
      (ExcCoordDatum.adj_iff_iform_ne_zero d i j').1 hadj
    have heq : (⟦⟨d.γ i, hiK⟩⟧ : KernelComponent χ) = ⟦⟨d.γ j', hjK⟩⟧ :=
      mk_eq_of_iform_ne_zero (α := ⟨d.γ i, hiK⟩) (β := ⟨d.γ j', hjK⟩) hne'
    exact ⟨hjK, heq.symm.trans hiJ⟩
  have hidx : ∀ {v : Fin τ.rank → ℤ} {k l : ExcRaw.Root m},
      (v = d.γ k ∨ v = -d.γ k) → (v = d.γ l ∨ v = -d.γ l) → k = l := by
    intro v k l h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact d.eq_of_eq k l (Or.inl (h1.symm.trans h2))
    · exact d.eq_of_eq k l (Or.inr (h1.symm.trans h2))
    · exact d.eq_of_eq k l (Or.inr ((neg_eq_iff_eq_neg).mp (h1.symm.trans h2)))
    · exact d.eq_of_eq k l (Or.inl (neg_inj.mp (h1.symm.trans h2)))
  have hneg : ∀ u v : Fin τ.rank → ℤ, iform (-u) v = -iform u v := by
    intro u v
    rw [← neg_one_smul ℤ u, iform_smul_left]
    ring
  have hnegr : ∀ u v : Fin τ.rank → ℤ, iform u (-v) = -iform u v := by
    intro u v
    rw [iform_comm u (-v), hneg v u, iform_comm v u]
  have hsign : ∀ (u v : Fin τ.rank → ℤ) (k l : ExcRaw.Root m),
      (u = d.γ k ∨ u = -d.γ k) → (v = d.γ l ∨ v = -d.γ l) →
      iform u v ≠ 0 → iform (d.γ k) (d.γ l) ≠ 0 := by
    intro u v k l hu hv h
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact h
    · rw [hnegr] at h
      exact neg_ne_zero.mp h
    · rw [hneg] at h
      exact neg_ne_zero.mp h
    · rw [hneg, hnegr, neg_neg] at h
      exact h
  have hmin : ∀ T ⊆ c, T.Nonempty →
      (∀ i ∈ T, ∀ j' ∈ c, ExcRaw.Adj m i j' → j' ∈ T) → T = c := by
    intro T hTsub hTne hTclosed
    refine Finset.Subset.antisymm hTsub ?_
    intro i' hi'
    obtain ⟨i₀, hi₀⟩ := hTne
    obtain ⟨h₀K, h₀J⟩ := (hmem i₀).1 (hTsub hi₀)
    obtain ⟨h'K, h'J⟩ := (hmem i').1 hi'
    have hrel : (kernelRootSetoid χ).r ⟨d.γ i₀, h₀K⟩ ⟨d.γ i', h'K⟩ :=
      Quotient.exact (h₀J.trans h'J.symm)
    let memT : (Fin τ.rank → ℤ) → Prop :=
      fun v => ∀ k : ExcRaw.Root m, (v = d.γ k ∨ v = -d.γ k) → k ∈ T
    have hidxT : memT (d.γ i₀) := by
      intro k hk
      have hk₀ : k = i₀ := hidx hk (Or.inl rfl)
      rwa [hk₀]
    have key : ∀ x y : kernelRoots χ, (kernelRootSetoid χ).r x y →
        (memT (x : Fin τ.rank → ℤ) ↔ memT (y : Fin τ.rank → ℤ)) := by
      intro x y hxy
      induction hxy with
      | rel x y hxy =>
        rw [dotProduct_mulVec_eq_iform] at hxy
        constructor
        · intro hx k₂ hy
          obtain ⟨k₁, hxrep⟩ := d.exists_eq x.1 x.2.1
          have hk₁ : k₁ ∈ T := hx k₁ hxrep
          have hadj : ExcRaw.Adj m k₁ k₂ :=
            (ExcCoordDatum.adj_iff_iform_ne_zero d k₁ k₂).2
              (hsign x.1 y.1 k₁ k₂ hxrep hy hxy)
          have hyK : d.γ k₂ ∈ kernelRoots χ := by
            rcases hy with hy | hy
            · rw [← hy]
              exact y.2
            · rw [show d.γ k₂ = -y.1 by rw [hy, neg_neg]]
              exact ⟨IsRoot.neg y.2.1, chi_neg y.2.2⟩
          exact hTclosed k₁ hk₁ k₂
            (hclosed k₁ (hTsub hk₁) k₂ ((hker k₂).1 hyK) hadj) hadj
        · intro hy k₁ hx
          obtain ⟨k₂, hyrep⟩ := d.exists_eq y.1 y.2.1
          have hk₂ : k₂ ∈ T := hy k₂ hyrep
          have hadj : ExcRaw.Adj m k₁ k₂ :=
            (ExcCoordDatum.adj_iff_iform_ne_zero d k₁ k₂).2
              (hsign x.1 y.1 k₁ k₂ hx hyrep hxy)
          have hxK : d.γ k₁ ∈ kernelRoots χ := by
            rcases hx with hx | hx
            · rw [← hx]
              exact x.2
            · rw [show d.γ k₁ = -x.1 by rw [hx, neg_neg]]
              exact ⟨IsRoot.neg x.2.1, chi_neg x.2.2⟩
          have hadj' : ExcRaw.Adj m k₂ k₁ := by
            rcases hadj with h | h
            · exact Or.inr h
            · exact Or.inl h
          exact hTclosed k₂ hk₂ k₁
            (hclosed k₂ (hTsub hk₂) k₁ ((hker k₁).1 hxK) hadj') hadj'
      | refl x => exact Iff.rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact (key ⟨d.γ i₀, h₀K⟩ ⟨d.γ i', h'K⟩ hrel).1 hidxT i' (Or.inl rfl)
  have hocc : ExcRaw.occurs m U c := ⟨hne, hsub, hclosed, hmin⟩
  have hroots : componentRoots χ j = codeRoots d.γ c := by
    refine Set.Subset.antisymm ?_ ?_
    · intro α hα
      obtain ⟨hαK, hαJ⟩ := hα
      obtain ⟨i, hi | hi⟩ := d.exists_eq α hαK.1
      · refine ⟨i, ?_, Or.inl hi⟩
        rw [hmem i, ← hi]
        exact ⟨hαK, hαJ⟩
      · refine ⟨i, ?_, Or.inr hi⟩
        rw [hmem i]
        have hn : -α ∈ componentRoots χ j :=
          (isRootComponent_componentRoots (χ := χ) j).neg_mem α ⟨hαK, hαJ⟩
        have hγ : d.γ i = -α := by rw [hi, neg_neg]
        rw [hγ]
        exact hn
    · rintro δ ⟨i, hi, hδ⟩
      rcases hδ with hδ | hδ
      · rw [hδ]
        exact (hmem i).1 hi
      · rw [hδ]
        exact (isRootComponent_componentRoots (χ := χ) j).neg_mem (d.γ i) ((hmem i).1 hi)
  exact ⟨c, hocc, hroots⟩

theorem exists_kernelComponent_of_occurs (d : ExcCoordDatum S T₀ m) {A : Subgroup (ModGL τ L)}
    (hA : A ≤ T₀) {a : ↥A → Fin τ.rank → Lˣ} (ha : ∀ u, rootDiagUnit τ (a u) = u)
    {c : Finset (ExcRaw.Root m)} (hc : ExcRaw.occurs m (ggLinImage (p := 3) d.coord A) c) :
    ∃ j : KernelComponent (famCharHom a), componentRoots (famCharHom a) j = codeRoots d.γ c := by
  classical
  obtain ⟨i, hi⟩ := hc.1
  have hvan : ExcRaw.Vanish m (ggLinImage (p := 3) d.coord A) i := hc.2.1 i hi
  have hchar : ∀ u, rootChar (a u) (d.γ i) = 1 :=
    (rootChar_excFamily_eq_one_iff d hA ha i).2 hvan
  have hkeri : d.γ i ∈ kernelRoots (famCharHom a) := by
    rw [mem_kernelRoots_famChar]
    exact ⟨d.isRoot i, hchar⟩
  let j : KernelComponent (famCharHom a) := ⟦⟨d.γ i, hkeri⟩⟧
  obtain ⟨c', hocc, hroots⟩ := exists_occurs_of_kernelComponent d hA ha j
  have hi' : i ∈ c' := by
    have hmem : d.γ i ∈ codeRoots d.γ c' := by
      rw [← hroots]
      exact ⟨hkeri, rfl⟩
    obtain ⟨k, hk, hik⟩ := hmem
    rcases hik with hik | hik
    · have hEq : i = k := d.eq_of_eq i k (Or.inl hik)
      rw [hEq]
      exact hk
    · have hEq : i = k := d.eq_of_eq i k (Or.inr hik)
      rw [hEq]
      exact hk
  have hcc : c = c' := ExcRaw.IsComp.eq_of_mem hc hocc hi hi'
  refine ⟨j, ?_⟩
  rw [hcc]
  exact hroots

theorem rationalComponentM_eq_codeComponent (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ)
    (γ : ExcRaw.Root m → Fin τ.rank → ℤ) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (j : KernelComponent χ)
    {c : Finset (ExcRaw.Root m)} (hc : componentRoots χ j = codeRoots γ c) :
    rationalComponentM S.ρ S.Γ χ j = codeComponent S γ c := by
  have hrootc : ∀ α, α ∈ codeRoots γ c → IsRoot τ α := by
    intro α hα
    rw [← hc] at hα
    exact (isRootComponent_componentRoots j).isRoot α hα
  have hnegc : ∀ α, α ∈ codeRoots γ c → -α ∈ codeRoots γ c := by
    intro α hα
    rw [← hc] at hα ⊢
    exact (isRootComponent_componentRoots j).neg_mem α hα
  have hroots : rationalRootsM S.ρ χ j = codeRoots γ c := by
    ext x
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      have step : ∀ (k : ℕ) (δ : Fin τ.rank → ℤ), δ ∈ codeRoots γ c →
          ((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k]) δ ∈ codeRoots γ c := by
        intro k
        induction k with
        | zero => intro δ hδ; simpa using hδ
        | succ k ih =>
            intro δ hδ
            rw [Function.iterate_succ_apply', hρ _ (hrootc _ (ih δ hδ))]
            exact hnegc _ (ih δ hδ)
      exact step k δ (hc ▸ hδ)
    · intro hx
      exact ⟨0, x, hc ▸ hx, by simp⟩
  simp only [rationalComponentM, rationalSpanM, codeComponent, hroots]

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
