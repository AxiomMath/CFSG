module

public import CFSG.LocalAnalysis.StandardType.GGResXDatumARank
public import CFSG.LocalAnalysis.StandardType.GGHLFrame
public import CFSG.LocalAnalysis.StandardType.GGResHdRoNarrowDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma ggHLT_coxeter_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M = M.reindex (Equiv.refl ι) := by
  apply CoxeterMatrix.ext
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  simp

lemma ggHLT_odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  exact ⟨2 ^ k - 1, by omega⟩

lemma ggHLT_odd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  exact ⟨2 ^ k, by omega⟩

lemma ggHLT_odd_ggTorM {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    Odd (ggTorM lab) := by
  unfold ggTorM
  split_ifs with h
  · exact ggHLT_odd_two_pow_add_one hlab.1
  · exact ggHLT_odd_two_pow_sub_one hlab.1

lemma ggHLT_weyl_A {n : ℕ} (hn : 1 ≤ n) : GGIsWeylMatrix (CoxeterMatrix.A n) :=
  Or.inl ⟨n, Equiv.refl _, hn, Or.inl (ggHLT_coxeter_reindex_refl _)⟩

theorem ggHLT_lin {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G}
    (hm : Odd m) (hpm : p ∣ m) (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (w : GGTorusTorWit m N ↥X (ggGamma X hN).range) (hw : w.Holds C M)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {x : G} (hxB : x ∈ Bs) (hxX : x ∈ Subgroup.centralizer (X : Set G)) :
    ∃ (hnk : ∀ k, ((w.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G))
      (hbk : ∀ k, ((w.cor k (ggZetaP p m) : ↥X) : G) ∈ Bs)
      (α : Fin N → Module.Dual (ZMod p) V),
      (∀ i v, ggLin (p := p) ι (ggTDρB X Bs (ggTDnH w hnk i)) v =
        v - α i v • ι (Additive.ofMul ⟨_, hbk i⟩)) ∧
      (∀ i j, α i (ι (Additive.ofMul ⟨_, hbk j⟩)) = (C i j : ZMod p)) ∧
      (∀ i, α i (ι (Additive.ofMul ⟨x, hxB⟩)) = 0) := by
  obtain ⟨hnk, hbk, F, hFadd, hFφ, hFC, hF1, hFsep⟩ := ggTD_core hm hpm hBs hS hN w hw
  let f : Fin N → Additive ↥Bs →+ ZMod p := fun k =>
    AddMonoidHom.mk' (fun b => F k (Additive.toMul b)) (fun b b' => hFadd k _ _)
  let α : Fin N → Module.Dual (ZMod p) V := fun k =>
    ((f k).comp ι.symm.toAddMonoidHom).toZModLinearMap p
  have hα : ∀ k v, α k v = F k (Additive.toMul (ι.symm v)) := fun _ _ => rfl
  refine ⟨hnk, hbk, α, fun i v => ?_, fun i j => ?_, fun i => ?_⟩
  · rw [ggLin_apply]
    have hφb : ggTDρB X Bs (ggTDnH w hnk i) (Additive.toMul (ι.symm v)) =
        ((⟨_, hbk i⟩ : ↥Bs) ^ (F i (Additive.toMul (ι.symm v))).val)⁻¹ *
          Additive.toMul (ι.symm v) := by
      apply Subtype.ext
      rw [ggTDρB_apply]
      push_cast
      exact hFφ i _
    rw [hφb, ofMul_mul, ofMul_inv, ofMul_pow, map_add, map_neg, map_nsmul, ofMul_toMul,
      AddEquiv.apply_symm_apply, hα, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    abel
  · rw [hα, AddEquiv.symm_apply_apply, toMul_ofMul]
    exact hFC i j
  · rw [hα, AddEquiv.symm_apply_apply, toMul_ofMul]
    exact hF1 i ⟨x, hxB⟩ ((ggGamma_eq_one_iff X hN _).mpr hxX)

lemma ggHLT_not_excl_of_S {p : ℕ} {lab : LargeEvenLabel}
    (h : (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧
      p ∣ ggTorM lab) :
    ¬ GGTBWExcl lab := by
  rintro (hF4 | ⟨hBC, -⟩)
  · rcases h.1 with h | h <;> rw [h] at hF4 <;> exact absurd hF4 (by decide)
  · rcases h.1 with h | h <;> rw [h] at hBC <;> exact absurd hBC (by decide)

lemma ggHLT_ne_two_of_S {p : ℕ} {lab : LargeEvenLabel}
    (hpp : p.Prime) (hlab : LargeEvenInLambda2 lab)
    (h : (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧
      p ∣ ggTorM lab) :
    p ≠ 2 := by
  intro h2
  have heven : Even (ggTorM lab) := even_iff_two_dvd.mpr (h2 ▸ h.2.2.2)
  exact (Nat.not_even_iff_odd.mpr (ggHLT_odd_ggTorM hlab)) heven

lemma ggHLT_split_of_S {p : ℕ} {lab : LargeEvenLabel}
    (h : (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧
      p ∣ ggTorM lab) :
    LargeEvenSplit p lab := by
  obtain ⟨htag, -, -, hdvdM⟩ := h
  unfold LargeEvenSplit
  unfold ggTorM at hdvdM
  rcases htag with hA | htwA
  · left
    refine ⟨?_, ?_⟩
    · rw [hA]; simp [LargeEvenUntwisted]
    · rwa [if_neg (by rw [hA]; decide)] at hdvdM
  · right; left
    refine ⟨?_, ?_, ?_⟩
    · rw [htwA]; simp [LargeEvenUntwisted]
    · rw [htwA]; decide
    · rwa [if_pos (by rw [htwA]; decide)] at hdvdM

lemma ggHLT_not_twisted_of_S {p : ℕ} {lab : LargeEvenLabel}
    (h : (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧
      p ∣ ggTorM lab) :
    ¬ GGOutdiagTwistedLabel lab := by
  rintro (h6 | h3 | h2)
  · rcases h.1 with h | h <;> rw [h] at h6 <;> exact absurd h6 (by decide)
  · rcases h.1 with h | h <;> rw [h] at h3 <;> exact absurd h3 (by decide)
  · rcases h.1 with h | h <;> rw [h] at h2 <;> exact absurd h2 (by decide)

theorem ggResXDatumA_compat
    (hRig : GGLabelRigidInput) (hT : GGTBTorANarrow) (hLift : GGTBTorLiftADepRows)
    (hW : GGTBWNormLabelInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
      p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab) p Bs L) (hxB : x ∈ Bs) :
    ∃ (lab : LargeEvenLabel), LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) ∧ (lab.tag = .A ∨ lab.tag = .twA) ∧
      6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab ∧
      ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
        (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
        (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
        (e : Fin lab.rank ≃ Λ),
        M = (CoxeterMatrix.A lab.rank).reindex e ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
          (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
          (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
          (∃ f : M.Group ≃* ↥(ggAutomizer L Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
          ggAutomizer L Bs = Subgroup.closure (Set.range φ) ∧
          ∃ (S : ℕ → LargeEvenLabel → Prop) (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
            GGTBWNormInputOn S ∧ GGInnerDiagOnLab S p Bs L ∧
              (∃ T : Subgroup G, T ≤ L ∧ IsPGroup p T ∧ ¬ IsCyclic T) ∧
              ∃ ψ : Λ → MulAut ↥(ggGamma L hN).range,
                (∀ i (b : ↥Bs), ψ i ((ggGamma L hN).rangeRestrict b) =
                  (ggGamma L hN).rangeRestrict (φ i b)) ∧
                ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hN).range =
                  Subgroup.closure (Set.range ψ) := by
  have hp : p.Prime := Fact.out
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨hp', hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSdef : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBBs : B ≤ Bs := hH.1.2.1.1
  let S : ℕ → LargeEvenLabel → Prop := fun p lab =>
    (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab
  have hW' : GGTBWNormInputOn S :=
    ggTBWNormInputOn_of_labels fun p lab hpp hlab hSlab =>
      hW p hpp (ggHLT_ne_two_of_S hpp hlab hSlab) lab hlab (ggHLT_not_excl_of_S hSlab)
        (by rcases hSlab.1 with h | h <;> rw [h] <;> decide)
  have hM : GGInnerDiagOnLab S p Bs L :=
    largeEvenMarking_mono
      (fun lab R _ I F θ hP => ⟨hP.1, ggHLT_split_of_S hP.1, hP.2.1, hP.2.2⟩) h
  obtain ⟨lab, hN, hlab, hHas, htag, hrank, hdvd, hdvdM, hTor⟩ := ggResXDatumA_core_L hT hLift hH h
  obtain ⟨w, hw⟩ := hTor
  have hp2 : p ≠ 2 := ggHLT_ne_two_of_S hp hlab ⟨htag, hrank, hdvd, hdvdM⟩
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S :=
    ggLNoncyclicInputOn_not_twisted G p B x L hH.1.1
      (largeEvenMarking_mono
        (fun lab R _ I F θ hP =>
          ⟨ggHLT_not_twisted_of_S hP.1, ggHLT_split_of_S hP.1, hBBs.trans hP.2.1,
            fun b hb => hP.2.2 b (hBBs hb)⟩) h)
  obtain ⟨V, hVadd, hVmod, hι⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  obtain ⟨hnk, hbk, α, hlin, hpair, hxker⟩ :=
    ggHLT_lin (ggHLT_odd_ggTorM hlab) hdvdM hBs hSdef hN w hw V ι hxB hxL
  let φ : Fin lab.rank → MulAut ↥Bs := fun k => ggTDρB L Bs (ggTDnH w hnk k)
  let hvec : Fin lab.rank → V := fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))
  have hfx : ∀ i, α i (hvec i) = 2 := by
    intro i
    rw [hpair i i, (ggIntCartan_A lab.rank).1 i]
    norm_num
  have hrefl : ∀ i, GGIsReflection p (φ i) := fun i =>
    ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  let ψ : Fin lab.rank → MulAut ↥(ggGamma L hN).range :=
    fun k => ggConjAut (ggGamma L hN).range (w.hn k)
  have hcompat : ∀ i (b : ↥Bs), ψ i ((ggGamma L hN).rangeRestrict b) =
      (ggGamma L hN).rangeRestrict (φ i b) := by
    intro i b
    have hgb : (w.n i : G) * b * (w.n i : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp (hnk i) b).mp b.2
    have hconj : MulAut.conj (w.n i) =
        L.normalizerMonoidHom ⟨(w.n i : G), Subgroup.le_normalizer (w.n i).2⟩ := by
      ext l
      rfl
    apply Subtype.ext
    rw [show ψ i = ggConjAut (ggGamma L hN).range (w.hn i) from rfl, ggConjAut_apply,
      MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict, hconj]
    rw [show φ i b = (⟨(w.n i : G) * b * (w.n i : G)⁻¹, hgb⟩ : ↥Bs) from
      Subtype.ext (ggTDρB_apply (X := L) (Bs := Bs) (ggTDnH w hnk i) b)]
    exact ggGamma_conj_normalizer L hN
      ⟨(w.n i : G), Subgroup.le_normalizer (w.n i).2⟩ b hgb
  have hA : ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hN).range =
      Subgroup.closure (Set.range ψ) := by
    simpa only [ψ] using hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨lab, hlab, hHas, htag, hrank, hdvd, hdvdM, Fin lab.rank, inferInstance, inferInstance,
    CoxeterMatrix.A lab.rank, CartanMatrix.A lab.rank, V, hVadd, hVmod, ι, φ, hvec, α,
    Equiv.refl _, ggHLT_coxeter_reindex_refl _, ggHLT_weyl_A (by omega),
    ggIntCartan_A lab.rank, hlin, hrefl, hpair, ⟨e, he⟩, hcl, S, hN, hW', hM, hnc, ψ, hcompat, hA⟩

end CFSG.StandardType
