module

public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.FLcFlag

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace S153L

open scoped Matrix

private theorem exists_amb_hom {V : Type} [CommGroup V] {D : FFModel} (hker : D.ker = ⊥)
    {H : Subgroup (MulAut V)} {J : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H J ⊥ π) :
    ∃ φ : ↥J →* D.Amb, Function.Injective φ ∧
      ∀ (γ : D.Gam) (x y : ↥J), ((π γ : ↥H) : MulAut V) (x : V) = (y : V) →
        φ y = D.act γ (φ x) := by
  obtain ⟨-, -, -, hHJ, -, hsec, -, β, -, hβk, hβe⟩ := h
  let q : ↥D.sec ⧸ D.ker.subgroupOf D.sec →* D.Amb :=
    QuotientGroup.lift (D.ker.subgroupOf D.sec) D.sec.subtype (fun x hx => by
      have hx' : (x : D.Amb) ∈ D.ker := hx
      rw [hker, Subgroup.mem_bot] at hx'
      exact hx')
  refine ⟨q.comp β, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β x)
    have hmx : (m : D.Amb) = 1 := by
      have h1 : q (β x) = 1 := hx
      rw [← hm] at h1
      exact h1
    have hβx : β x = 1 := by
      rw [← hm]
      have : m = 1 := Subtype.ext hmx
      rw [this]
      rfl
    have h2 := (hβk x).1 hβx
    exact Subtype.ext (Subgroup.mem_bot.1 h2)
  · intro γ x y hxy
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β x)
    have hy : ((π γ : ↥H) : MulAut V) (x : V) ∈ J := hHJ (π γ) x x.2
    have hact : D.act γ (m : D.Amb) ∈ D.sec := hsec γ m m.2
    have h1 := hβe γ x m hy hact hm.symm
    have hy' : (⟨((π γ : ↥H) : MulAut V) (x : V), hy⟩ : ↥J) = y := Subtype.ext hxy
    rw [hy'] at h1
    show q (β y) = D.act γ (q (β x))
    rw [h1, ← hm]
    rfl

private theorem exists_nat_hom {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {J : Subgroup V}
    {π : ↥(StatedSL 4 (ZMod 2)) →* ↥L}
    (h : (FFModel.nat (StatedSL 4 (ZMod 2))).RealizesVia L J ⊥ π) :
    ∃ φ : ↥J →* Multiplicative (FLc.Vt 4), Function.Injective φ ∧
      ∀ (s : FLc.SLt 4) (x y : ↥J),
        ((π (specialLinearGroupEquivStatedSL 4 (ZMod 2) s) : ↥L) : MulAut V) (x : V) = (y : V) →
          Multiplicative.toAdd (φ y) = FLc.mat s *ᵥ Multiplicative.toAdd (φ x) := by
  obtain ⟨φ, hφi, hφ⟩ := exists_amb_hom (D := FFModel.nat (StatedSL 4 (ZMod 2))) rfl h
  refine ⟨φ, hφi, fun s x y hxy => ?_⟩
  exact congrArg Multiplicative.toAdd (hφ _ x y hxy)

private theorem decomp_exists {V : Type} [CommGroup V] {k : ℕ} (I : Fin k → Subgroup V) {x : V}
    (hx : x ∈ ⨆ i, I i) : ∃ f : Fin k → V, (∀ i, f i ∈ I i) ∧ ∏ i, f i = x := by
  classical
  refine Subgroup.iSup_induction I (C := fun x => ∃ f : Fin k → V, (∀ i, f i ∈ I i) ∧ ∏ i, f i = x)
    hx ?_ ?_ ?_
  · intro i x hxi
    refine ⟨fun j => if j = i then x else 1, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · simpa [hj] using hxi
      · simp [hj]
    · simp
  · exact ⟨fun _ => 1, fun i => (I i).one_mem, by simp⟩
  · rintro x y ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun i => f i * g i, fun i => (I i).mul_mem (hf i) (hg i), Finset.prod_mul_distrib⟩

private theorem decomp_unique {V : Type} [CommGroup V] {k : ℕ} (I : Fin k → Subgroup V)
    (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥) {f g : Fin k → V}
    (hf : ∀ i, f i ∈ I i) (hg : ∀ i, g i ∈ I i) (h : ∏ i, f i = ∏ i, g i) : f = g := by
  classical
  funext i
  have hd : ∏ j, (f j * (g j)⁻¹) = 1 := by
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, h, mul_inv_cancel]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)] at hd
  have h1 : f i * (g i)⁻¹ = (∏ j ∈ Finset.univ.erase i, (f j * (g j)⁻¹))⁻¹ :=
    eq_inv_of_mul_eq_one_left hd
  have hmem1 : f i * (g i)⁻¹ ∈ I i := (I i).mul_mem (hf i) ((I i).inv_mem (hg i))
  have hmem2 : f i * (g i)⁻¹ ∈ ⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j := by
    rw [h1]
    refine Subgroup.mem_sup_right ?_
    refine Subgroup.inv_mem _ (Subgroup.prod_mem _ fun j hj => ?_)
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    exact Subgroup.mem_iSup_of_mem j (Subgroup.mem_iSup_of_mem hji
      ((I j).mul_mem (hf j) ((I j).inv_mem (hg j))))
  have h2 : f i * (g i)⁻¹ ∈ I i ⊓ (⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) := ⟨hmem1, hmem2⟩
  rw [hind i] at h2
  exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 h2)

private theorem fixed_vec_unique (Q : Sylow 2 (FLc.SLt 4)) {m₁ m₂ : FLc.Vt 4} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0)
    (hf₁ : ∀ q ∈ (Q : Subgroup (FLc.SLt 4)), FLc.mat q *ᵥ m₁ = m₁)
    (hf₂ : ∀ q ∈ (Q : Subgroup (FLc.SLt 4)), FLc.mat q *ᵥ m₂ = m₂) : m₁ = m₂ := by
  obtain ⟨W, -, -, -, hW⟩ := FLc.exists_unique_flag (n := 4) (by norm_num) Q
  have hspan : ∀ m : FLc.Vt 4, m ≠ 0 → (∀ q ∈ (Q : Subgroup (FLc.SLt 4)), FLc.mat q *ᵥ m = m) →
      Submodule.span (ZMod 2) {m} = W 1 := by
    intro m hm hfm
    refine hW _ ?_ 1 (by norm_num) (finrank_span_singleton hm)
    intro q hq v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [Matrix.mulVec_smul, hfm q hq]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self m)
  have h12 : Submodule.span (ZMod 2) {m₁} = Submodule.span (ZMod 2) {m₂} :=
    (hspan _ h₁ hf₁).trans (hspan _ h₂ hf₂).symm
  have hm2 : m₂ ∈ Submodule.span (ZMod 2) {m₁} := by
    rw [h12]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm2
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact h₂ hc.symm
  have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  rw [key c hc0, one_smul] at hc
  exact hc

private theorem card_slt_four : Nat.card (FLc.SLt 4) = 20160 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
  decide

private theorem le_card_stabilizer {e : FLc.Vt 4} (he : e ≠ 0) :
    1344 ≤ Nat.card (MulAction.stabilizer (FLc.SLt 4) e) := by
  have horb : Nat.card (MulAction.orbit (FLc.SLt 4) e) ≤ 15 := by
    have hsub : MulAction.orbit (FLc.SLt 4) e ⊆ {v : FLc.Vt 4 | v ≠ 0} := by
      rintro _ ⟨g, rfl⟩ h0
      apply he
      have h0' : g • e = 0 := h0
      have h1 : g⁻¹ • (g • e) = g⁻¹ • (0 : FLc.Vt 4) := by rw [h0']
      rwa [inv_smul_smul, smul_zero] at h1
    calc Nat.card (MulAction.orbit (FLc.SLt 4) e) ≤ Nat.card ↥{v : FLc.Vt 4 | v ≠ 0} :=
          Nat.card_mono (Set.toFinite _) hsub
      _ = 15 := by
          rw [Nat.card_eq_fintype_card]
          decide +kernel
  have hmul : Nat.card (MulAction.orbit (FLc.SLt 4) e) *
      Nat.card (MulAction.stabilizer (FLc.SLt 4) e) = Nat.card (FLc.SLt 4) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (FLc.SLt 4) e)
  rw [card_slt_four] at hmul
  have h2 : Nat.card (MulAction.orbit (FLc.SLt 4) e) *
      Nat.card (MulAction.stabilizer (FLc.SLt 4) e) ≤
      15 * Nat.card (MulAction.stabilizer (FLc.SLt 4) e) := Nat.mul_le_mul_right _ horb
  omega

theorem natSum_stab {V : Type} [CommGroup V] [Finite V] {L B : Subgroup (MulAut V)} {U : Subgroup V}
    {k : ℕ} (hL : Nat.card ↥L = 20160) (hB : IsSylowTwoOf B L)
    (hdir : DirectSumOfCopies L U ⊥ (FFModel.nat (StatedSL 4 (ZMod 2))) k) :
    ∀ u ∈ U, (∀ b ∈ B, (b : MulAut V) u = u) →
      ∃ H : Subgroup (MulAut V), H ≤ L ∧ (∀ g ∈ H, (g : MulAut V) u = u) ∧ 1344 ≤ Nat.card ↥H := by
  intro u hu hfix
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := hdir
  have hU : U = ⨆ i, I i := by rw [← hsup, bot_sup_eq]
  have hu' : u ∈ ⨆ i, I i := by rw [← hU]; exact hu
  obtain ⟨f, hfI, hfu⟩ := decomp_exists I hu'
  by_cases hall : ∀ i, f i = 1
  · have hu1 : u = 1 := by rw [← hfu]; simp [hall]
    refine ⟨L, le_rfl, fun g _ => by rw [hu1, map_one], ?_⟩
    rw [hL]
    norm_num
  obtain ⟨i₀, hi₀⟩ := not_forall.1 hall
  have hπs : Function.Surjective π := (hreal i₀).1
  have hπi : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal i₀)
  let θ : FLc.SLt 4 →* ↥L :=
    π.comp (specialLinearGroupEquivStatedSL 4 (ZMod 2)).toMonoidHom
  have hθs : Function.Surjective θ := hπs.comp (specialLinearGroupEquivStatedSL 4 (ZMod 2)).surjective
  have hθi : Function.Injective θ := hπi.comp (specialLinearGroupEquivStatedSL 4 (ZMod 2)).injective
  have hBp : IsPGroup 2 ↥(B.subgroupOf L) :=
    hB.2.1.of_surjective (Subgroup.subgroupOfEquivOfLe hB.1).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hB.1).symm.surjective
  have hQp : IsPGroup 2 ↥((B.subgroupOf L).comap θ) := hBp.comap_of_injective θ hθi
  have hQi : ¬ 2 ∣ ((B.subgroupOf L).comap θ).index := by
    rw [Subgroup.index_comap_of_surjective _ hθs]
    exact hB.2.2
  let Q : Sylow 2 (FLc.SLt 4) := hQp.toSylow hQi
  have hQmem : ∀ s : FLc.SLt 4, s ∈ (Q : Subgroup (FLc.SLt 4)) ↔ ((θ s : ↥L) : MulAut V) ∈ B := by
    intro s
    show s ∈ (B.subgroupOf L).comap θ ↔ _
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  have hinvI : ∀ i, ∀ s : FLc.SLt 4, ∀ x ∈ I i, ((θ s : ↥L) : MulAut V) x ∈ I i :=
    fun i s x hx => (hreal i).2.2.2.1 (θ s) x hx
  have hQfix : ∀ s : FLc.SLt 4, s ∈ (Q : Subgroup (FLc.SLt 4)) →
      ∀ i, ((θ s : ↥L) : MulAut V) (f i) = f i := by
    intro s hs
    have hb : ((θ s : ↥L) : MulAut V) ∈ B := (hQmem s).1 hs
    have h1 : ((θ s : ↥L) : MulAut V) u = u := hfix _ hb
    have h2 : ∏ i, ((θ s : ↥L) : MulAut V) (f i) = ∏ i, f i := by
      have h3 := map_prod ((θ s : ↥L) : MulAut V) f Finset.univ
      rw [hfu, h1] at h3
      rw [← h3, hfu]
    have h4 := decomp_unique I hind (f := fun i => ((θ s : ↥L) : MulAut V) (f i)) (g := f)
      (fun i => hinvI i s _ (hfI i)) hfI h2
    exact fun i => congrFun h4 i
  choose φ hφi hφrel using fun i => exists_nat_hom (hreal i)
  let mv : Fin k → FLc.Vt 4 := fun i => Multiplicative.toAdd (φ i ⟨f i, hfI i⟩)
  have hmvfix : ∀ i, ∀ q ∈ (Q : Subgroup (FLc.SLt 4)), FLc.mat q *ᵥ mv i = mv i := by
    intro i q hq
    exact (hφrel i q ⟨f i, hfI i⟩ ⟨f i, hfI i⟩ (hQfix q hq i)).symm
  have hmvne : ∀ i, f i ≠ 1 → mv i ≠ 0 := by
    intro i hi h0
    apply hi
    have h1 : φ i ⟨f i, hfI i⟩ = 1 := h0
    have h2 := hφi i (h1.trans (map_one (φ i)).symm)
    exact congrArg Subtype.val h2
  have hmveq : ∀ i, f i ≠ 1 → mv i = mv i₀ := fun i hi =>
    fixed_vec_unique Q (hmvne i hi) (hmvne i₀ hi₀) (hmvfix i) (hmvfix i₀)
  have he : mv i₀ ≠ 0 := hmvne i₀ hi₀
  refine ⟨(MulAction.stabilizer (FLc.SLt 4) (mv i₀)).map (L.subtype.comp θ), ?_, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact (θ s).2
  · rintro _ ⟨s, hs, rfl⟩
    have hse : FLc.mat s *ᵥ mv i₀ = mv i₀ := MulAction.mem_stabilizer_iff.1 hs
    have hfs : ∀ i, ((θ s : ↥L) : MulAut V) (f i) = f i := by
      intro i
      by_cases hi : f i = 1
      · rw [hi, map_one]
      · have hy : ((θ s : ↥L) : MulAut V) (f i) ∈ I i := hinvI i s _ (hfI i)
        have h1 := hφrel i s ⟨f i, hfI i⟩ ⟨_, hy⟩ rfl
        have h2 : φ i ⟨_, hy⟩ = φ i ⟨f i, hfI i⟩ := by
          apply Multiplicative.toAdd.injective
          rw [h1]
          show FLc.mat s *ᵥ mv i = mv i
          rw [hmveq i hi, hse]
        exact congrArg Subtype.val (hφi i h2)
    have h3 := map_prod ((θ s : ↥L) : MulAut V) f Finset.univ
    rw [hfu] at h3
    show ((θ s : ↥L) : MulAut V) u = u
    rw [h3]
    simp only [hfs]
    exact hfu
  · have hρi : Function.Injective (L.subtype.comp θ) := fun a b hab => hθi (Subtype.ext hab)
    rw [Subgroup.card_map_of_injective hρi]
    exact le_card_stabilizer he

end S153L

end CFSG.Quasithin
