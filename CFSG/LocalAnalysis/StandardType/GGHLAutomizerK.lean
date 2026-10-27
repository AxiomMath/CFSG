module

public import CFSG.LocalAnalysis.StandardType.GGHLAutomizer
public import CFSG.LocalAnalysis.StandardType.GGXFixedReflK
public import CFSG.LocalAnalysis.StandardType.GGNbrCentralizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nQ6_hKy {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    K ≤ Subgroup.centralizer ({y} : Set G) :=
  hH.2.2.2.2.1.1.2.2.2.1

private lemma l05nQ6_hker_K {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (hBsN : Bs ≤ Subgroup.normalizer (K : Set G)) (hyB : y ∈ Bs) :
    ∀ b : ↥Bs, ggGamma K hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨y, hyB⟩ : ↥Bs) := by
  have hKy := l05nQ6_hKy hH
  intro b
  rw [ggGamma_eq_one_iff K hBsN b]
  constructor
  · intro hc
    have h2 : (b : G) ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := ⟨b.2, hc⟩
    rw [ggNbr_inf_centralizer hH hCent] at h2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  · intro hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hbG : (b : G) = y ^ k := by
      have h := congrArg Subtype.val hk
      rw [Subgroup.coe_zpow] at h
      exact h.symm
    have hycent : y ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subgroup.mem_centralizer_singleton_iff.mp (hKy hk)
    have hbcent : (b : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [hbG]
      exact Subgroup.zpow_mem _ hycent k
    exact hbcent

private lemma l05nQ6_automizer_ne_bot {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {K : Subgroup G} {Λ : Type} [Fintype Λ]
    (φ : Λ → MulAut ↥Bs) (hgen : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hΛ : Nonempty Λ) :
    ggAutomizer K Bs ≠ ⊥ := by
  obtain ⟨i⟩ := hΛ
  intro hbot
  have hmem : φ i ∈ ggAutomizer K Bs :=
    hgen.symm ▸ Subgroup.subset_closure (Set.mem_range_self i)
  rw [hbot] at hmem
  have hphi1 : φ i = 1 := by simpa using hmem
  have hcard : Nat.card {b : ↥Bs // φ i b = b} = Nat.card ↥Bs := by
    calc Nat.card {b : ↥Bs // φ i b = b}
        = Nat.card {b : ↥Bs // True} :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun b => by simp [hphi1]))
      _ = Nat.card ↥Bs := Nat.card_congr (Equiv.Set.univ _)
  have hmul : Nat.card ↥Bs * p = Nat.card ↥Bs := by
    have h := (hrefl i).2
    rw [hcard] at h
    exact h
  have hpos : 0 < Nat.card ↥Bs := Finite.card_pos_iff.mpr ⟨1⟩
  have hp1 : p = 1 := Nat.eq_of_mul_eq_mul_left hpos (by simpa using hmul)
  exact (Fact.out : p.Prime).ne_one hp1

private theorem l05nQ6_lines_of_compat_K
    {G : Type} [Group G] [Finite G] {S : ℕ → LargeEvenLabel → Prop}
    (hW : GGTBWNormInputNbr S) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (hM : GGInnerDiagOnLab S p Bs K) (hnt : ggAutomizer K Bs ≠ ⊥)
    (hBsN : Bs ≤ Subgroup.normalizer (K : Set G)) (hyB : y ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma K hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨y, hyB⟩ : ↥Bs))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hMw : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hxker : ∀ i, α i (ι (Additive.ofMul ⟨y, hyB⟩)) = 0)
    (ψ : Λ → MulAut ↥(ggGamma K hBsN).range)
    (hcompat : ∀ i (b : ↥Bs),
      ψ i ((ggGamma K hBsN).rangeRestrict b) = (ggGamma K hBsN).rangeRestrict (φ i b))
    (hA : ggAutomizer (MulAut.conj : K →* MulAut K).range (ggGamma K hBsN).range =
      Subgroup.closure (Set.range ψ))
    (t : MulAut ↥Bs) (ht : t ∈ ggInduced ⊤ Bs) (htr : GGIsReflection p t)
    (hty : t ⟨y, hyB⟩ = ⟨y, hyB⟩) :
    GGHLLines (ggHLRoots (fun i => ggLin (p := p) ι (φ i)) h) (ι (Additive.ofMul ⟨y, hyB⟩))
      (ggLin (p := p) ι t) := by
  obtain ⟨VA, hVAadd, hVAmod, ιA, q, hA', αA, hqι, hqsurj, hqker, hqh, hqα, hlinA⟩ :=
    ggHL_descent hBsN hyB hker ι φ h α hlin hxker ψ hcompat
  letI : AddCommGroup VA := hVAadd
  letI : Module (ZMod p) VA := hVAmod
  have hpairA : ∀ i j, αA i (hA' j) = (C i j : ZMod p) := by
    intro i j
    rw [← hqh j, hqα i, hpair i j]
  obtain ⟨g, hgB, hgK, hg, hconcl⟩ :=
    ggXFixedRefl_mem_ggHL_K hW hH hCent hM hnt hBsN ιA ψ hA' αA hMw hC hpairA hlinA hA t ht htr
      hyB hty
  let cg : MulAut K := K.normalizerMonoidHom ⟨g, hgK⟩
  have hcgN : cg ∈ Subgroup.normalizer
      (((ggGamma K hBsN).range : Subgroup (MulAut K)) : Set (MulAut K)) :=
    normalizerMonoidHom_mem_normalizer_range_ggGamma hBsN hgB hgK
  let φ' : MulAut ↥(ggGamma K hBsN).range := ggConjAut (ggGamma K hBsN).range hcgN
  have hφ' : ∀ a : ↥(ggGamma K hBsN).range,
      ((φ' a : ↥(ggGamma K hBsN).range) : MulAut K) = cg * a * cg⁻¹ :=
    fun a => ggConjAut_apply (ggGamma K hBsN).range hcgN a
  have hmem : ggLin (p := p) ιA φ' ∈ ggHL ιA ψ hA' αA := hconcl φ' hφ'
  have hkey : ∀ b : ↥Bs, φ' ((ggGamma K hBsN).rangeRestrict b) =
      (ggGamma K hBsN).rangeRestrict (t b) := by
    intro b
    apply Subtype.ext
    have hgb : g * (b : G) * g⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hgB b).mp b.2
    have htb : (⟨g * (b : G) * g⁻¹, hgb⟩ : ↥Bs) = t b := Subtype.ext (hg b).symm
    rw [hφ', MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict,
      ggGamma_conj_normalizer K hBsN ⟨g, hgK⟩ b hgb, htb]
  have htransfer : ∀ v : V, q (ggLin (p := p) ι t v) = ggLin (p := p) ιA φ' (q v) := by
    intro v
    obtain ⟨a, rfl⟩ := ι.surjective v
    set b : ↥Bs := Additive.toMul a with hb
    change q (ggLin (p := p) ι t (ι (Additive.ofMul b))) =
      ggLin (p := p) ιA φ' (q (ι (Additive.ofMul b)))
    calc q (ggLin (p := p) ι t (ι (Additive.ofMul b)))
        = q (ι (Additive.ofMul (t b))) := by rw [ggLin_apply_ofMul]
      _ = ιA (Additive.ofMul ((ggGamma K hBsN).rangeRestrict (t b))) := by rw [hqι]
      _ = ιA (Additive.ofMul (φ' ((ggGamma K hBsN).rangeRestrict b))) := by rw [hkey b]
      _ = ggLin (p := p) ιA φ'
            (ιA (Additive.ofMul ((ggGamma K hBsN).rangeRestrict b))) := by
            rw [ggLin_apply_ofMul]
      _ = ggLin (p := p) ιA φ' (q (ι (Additive.ofMul b))) := by rw [hqι]
  have hsqA : ∀ i, ψ i ^ 2 = 1 := by
    intro i
    apply MulEquiv.ext
    intro a
    obtain ⟨b, rfl⟩ := (ggGamma K hBsN).rangeRestrict_surjective a
    rw [pow_two, MulAut.mul_apply, hcompat i b, hcompat i (φ i b), ← MulAut.mul_apply,
      ← pow_two, (hrefl i).1, MulAut.one_apply]
    rfl
  have hrq : ∀ i (v : V),
      ggLin (p := p) ιA (ψ i) (q v) = q (ggLin (p := p) ι (φ i) v) := by
    intro i v
    rw [hlinA i (q v), hlin i v, map_sub, map_smul, hqα i v, hqh i]
  have hword_map := ggHLB_word_map (p := p) q (fun i => ggLin (p := p) ι (φ i))
    (fun i => ggLin (p := p) ιA (ψ i)) hrq
  have hword_lift := ggHLB_word_lift (p := p) q (fun i => ggLin (p := p) ι (φ i))
    (fun i => ggLin (p := p) ιA (ψ i)) hrq
  have hroot_map : ∀ v ∈ ggHLRoots (fun i => ggLin (p := p) ι (φ i)) h,
      q v ∈ ggHLRoots (fun i => ggLin (p := p) ιA (ψ i)) hA' := by
    rintro v ⟨w, hw, i, rfl⟩
    obtain ⟨wA, hwA, hwAeq⟩ := hword_map w hw
    exact ⟨wA, hwA, i, by rw [← hqh i, ← hwAeq]⟩
  have hroot_lift : ∀ wA ∈ ggHLRoots (fun i => ggLin (p := p) ιA (ψ i)) hA',
      ∃ w ∈ ggHLRoots (fun i => ggLin (p := p) ι (φ i)) h, q w = wA := by
    rintro wA ⟨wA', hwA', i, rfl⟩
    obtain ⟨w, hw, hweq⟩ := hword_lift wA' hwA'
    exact ⟨w (h i), ⟨w, hw, i, rfl⟩, by rw [← hqh i, hweq]⟩
  intro v hv
  obtain ⟨wA, hwA, c, hc, hcA⟩ :=
    ggHL_perm_lines ιA ψ hA' αA hlinA hsqA hmem (q v) (hroot_map v hv)
  obtain ⟨w, hw, hweq⟩ := hroot_lift wA hwA
  have hq0 : q (ggLin (p := p) ι t v - c • w) = 0 := by
    rw [map_sub, htransfer, hcA, map_smul, hweq, sub_self]
  have hker0 : ggLin (p := p) ι t v - c • w ∈ LinearMap.ker q := hq0
  rw [hqker] at hker0
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hker0
  refine ⟨w, hw, c, d, hc, ?_⟩
  rw [hd]
  abel

theorem ggHL_lines_of_lift_K {G : Type} [Group G] [Finite G]
    {S : ℕ → LargeEvenLabel → Prop} (hW : GGTBWNormInputNbr S) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (hM : GGInnerDiagOnLab S p Bs K)
    (hBsN : Bs ≤ Subgroup.normalizer (K : Set G)) (hyB : y ∈ Bs)
    (hlift : GGAutomizerLift K Bs hBsN)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hMw : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hgen : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (t : MulAut ↥Bs) (ht : t ∈ ggInduced ⊤ Bs) (htr : GGIsReflection p t)
    (hty : t ⟨y, hyB⟩ = ⟨y, hyB⟩) :
    GGHLLines (ggHLRoots (fun i => ggLin (p := p) ι (φ i)) h) (ι (Additive.ofMul ⟨y, hyB⟩))
      (ggLin (p := p) ι t) := by
  by_cases hΛ : Nonempty Λ
  · obtain ⟨i₀⟩ := hΛ
    have hKy := l05nQ6_hKy hH
    have hker := l05nQ6_hker_K hH hCent hBsN hyB
    have hpres := ggHLA_pres (Bs := Bs) (L := K) (x := y) hKy hyB
    let desc : ↥(ggAutomizer K Bs) →* MulAut ↥(ggGamma K hBsN).range :=
      ggHLA_desc hBsN hyB hker hpres
    have hφmem : ∀ i, φ i ∈ ggAutomizer K Bs := fun i =>
      hgen.symm ▸ Subgroup.subset_closure (Set.mem_range_self i)
    let ψ : Λ → MulAut ↥(ggGamma K hBsN).range := fun i => desc ⟨φ i, hφmem i⟩
    have hcompat : ∀ i (b : ↥Bs), ψ i ((ggGamma K hBsN).rangeRestrict b) =
        (ggGamma K hBsN).rangeRestrict (φ i b) := by
      intro i b
      show ggHLA_desc hBsN hyB hker hpres ⟨φ i, hφmem i⟩
        ((ggGamma K hBsN).rangeRestrict b) =
        (ggGamma K hBsN).rangeRestrict (φ i b)
      rw [ggHLA_desc_spec]
    have hψrange : Subgroup.closure (Set.range ψ) =
        (ggHLA_desc hBsN hyB hker hpres).range := by
      show Subgroup.closure (Set.range (fun i =>
        ggHLA_desc hBsN hyB hker hpres ⟨φ i, hφmem i⟩)) = _
      exact ggHLA_closure_desc hBsN hyB hker hpres φ hφmem hgen
    have hA' : ggAutomizer (MulAut.conj : K →* MulAut K).range (ggGamma K hBsN).range =
        Subgroup.closure (Set.range ψ) := by
      rw [hψrange]
      refine le_antisymm (fun g hg => ?_) ?_
      · obtain ⟨χ, hχ, hgχ⟩ := hlift g hg
        refine ⟨⟨χ, hχ⟩, ?_⟩
        apply MulEquiv.ext
        intro a
        obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma K hBsN) a
        rw [ggHLA_desc_spec, hgχ]
      · rintro _ ⟨χ, rfl⟩
        exact ggHLA_desc_mem hBsN hyB hker hpres χ
    have hxker : ∀ i, α i (ι (Additive.ofMul ⟨y, hyB⟩)) = 0 := by
      intro i
      have hfixi : φ i (⟨y, hyB⟩ : ↥Bs) = ⟨y, hyB⟩ :=
        ggHLA_fixes_x hKy hyB (φ i) (hφmem i)
      have hfixL : ggLin (p := p) ι (φ i) (ι (Additive.ofMul ⟨y, hyB⟩)) =
          ι (Additive.ofMul ⟨y, hyB⟩) :=
        (ggLin_fix_iff ι (φ i) ⟨y, hyB⟩).mp hfixi
      have hzero : α i (ι (Additive.ofMul ⟨y, hyB⟩)) • h i = 0 := by
        have h1 := hlin i (ι (Additive.ofMul ⟨y, hyB⟩))
        rw [hfixL] at h1
        exact (sub_eq_self.mp h1.symm)
      have h2 : α i (α i (ι (Additive.ofMul ⟨y, hyB⟩)) • h i) = 0 := by
        rw [hzero, map_zero]
      rw [map_smul] at h2
      rw [hpair i i] at h2
      have hz : (C i i : ZMod p) ≠ 0 := by
        rw [hC.1 i]
        simpa using zmod_two_ne_zero hH.1.1.2.2.2.2.2.1.2.1
      rw [smul_eq_mul] at h2
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hz
    have hnt : ggAutomizer K Bs ≠ ⊥ := l05nQ6_automizer_ne_bot φ hgen hrefl ⟨i₀⟩
    exact l05nQ6_lines_of_compat_K hW hH hCent hM hnt hBsN hyB hker hMw hC ι φ h α hlin
      hrefl hpair hxker ψ hcompat hA' t ht htr hty
  · intro v hv
    obtain ⟨w, -, i, -⟩ := hv
    exact absurd ⟨i⟩ hΛ

theorem ggHL_lines_of_automizer_K {G : Type} [Group G] [Finite G]
    {S : ℕ → LargeEvenLabel → Prop} (hW : GGTBWNormInputNbr S) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (hM : GGInnerDiagOnLab S p Bs K)
    (hBsN : Bs ≤ Subgroup.normalizer (K : Set G)) (hyB : y ∈ Bs)
    {Λ₁ : Type} (φ₁ : Λ₁ → MulAut ↥Bs) (ψ₁ : Λ₁ → MulAut ↥(ggGamma K hBsN).range)
    (hcompat₁ : ∀ i (b : ↥Bs), ψ₁ i ((ggGamma K hBsN).rangeRestrict b) =
      (ggGamma K hBsN).rangeRestrict (φ₁ i b))
    (hA₁ : ggAutomizer (MulAut.conj : K →* MulAut K).range (ggGamma K hBsN).range =
      Subgroup.closure (Set.range ψ₁))
    (hgen₁ : ggAutomizer K Bs = Subgroup.closure (Set.range φ₁))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hMw : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hgen : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (t : MulAut ↥Bs) (ht : t ∈ ggInduced ⊤ Bs) (htr : GGIsReflection p t)
    (hty : t ⟨y, hyB⟩ = ⟨y, hyB⟩) :
    GGHLLines (ggHLRoots (fun i => ggLin (p := p) ι (φ i)) h) (ι (Additive.ofMul ⟨y, hyB⟩))
      (ggLin (p := p) ι t) :=
  ggHL_lines_of_lift_K hW hH hCent hM hBsN hyB
    (ggAutomizerLift_of_system hBsN φ₁ ψ₁ hcompat₁ hA₁ hgen₁) hMw hC ι φ h α hlin hrefl hpair hgen
    t ht htr hty

end CFSG.StandardType
