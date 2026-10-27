module

public import CFSG.LocalAnalysis.StandardType.GGHLLines
public import CFSG.LocalAnalysis.StandardType.GGHLDescent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

lemma ggHLB_word_map {p : ℕ} {V VA : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup VA] [Module (ZMod p) VA] (q : V →ₗ[ZMod p] VA) {Λ : Type}
    (r : Λ → V ≃ₗ[ZMod p] V) (rA : Λ → VA ≃ₗ[ZMod p] VA)
    (hrq : ∀ i v, rA i (q v) = q (r i v)) :
    ∀ w ∈ Submonoid.closure (Set.range r),
      ∃ wA ∈ Submonoid.closure (Set.range rA), ∀ v, q (w v) = wA (q v) := by
  intro w hw
  induction hw using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨rA i, Submonoid.subset_closure ⟨i, rfl⟩, fun v => (hrq i v).symm⟩
  | one => exact ⟨1, Submonoid.one_mem _, fun v => by simp⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨xA, hxA, hxAeq⟩ := ihx
      obtain ⟨yA, hyA, hyAeq⟩ := ihy
      exact ⟨xA * yA, Submonoid.mul_mem _ hxA hyA, fun v => by
        rw [LinearEquiv.mul_apply, hxAeq, hyAeq, LinearEquiv.mul_apply]⟩

lemma ggHLB_word_lift {p : ℕ} {V VA : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup VA] [Module (ZMod p) VA] (q : V →ₗ[ZMod p] VA) {Λ : Type}
    (r : Λ → V ≃ₗ[ZMod p] V) (rA : Λ → VA ≃ₗ[ZMod p] VA)
    (hrq : ∀ i v, rA i (q v) = q (r i v)) :
    ∀ wA ∈ Submonoid.closure (Set.range rA),
      ∃ w ∈ Submonoid.closure (Set.range r), ∀ v, wA (q v) = q (w v) := by
  intro wA hwA
  induction hwA using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨r i, Submonoid.subset_closure ⟨i, rfl⟩, fun v => hrq i v⟩
  | one => exact ⟨1, Submonoid.one_mem _, fun v => by simp⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨x', hx', hxeq⟩ := ihx
      obtain ⟨y', hy', hyeq⟩ := ihy
      exact ⟨x' * y', Submonoid.mul_mem _ hx' hy', fun v => by
        rw [LinearEquiv.mul_apply, hyeq, hxeq, LinearEquiv.mul_apply]⟩

theorem ggHL_lines_of_compat {G : Type} [Group G] [Finite G] {S : ℕ → LargeEvenLabel → Prop}
    (hW : GGTBWNormInputOn S) {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hM : GGInnerDiagOnLab S p Bs L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hMw : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hxker : ∀ i, α i (ι (Additive.ofMul ⟨x, hxB⟩)) = 0)
    (ψ : Λ → MulAut ↥(ggGamma L hBsN).range)
    (hcompat : ∀ i (b : ↥Bs),
      ψ i ((ggGamma L hBsN).rangeRestrict b) = (ggGamma L hBsN).rangeRestrict (φ i b))
    (hA : ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range =
      Subgroup.closure (Set.range ψ))
    (t : MulAut ↥Bs) (ht : t ∈ ggInduced ⊤ Bs) (htr : GGIsReflection p t)
    (htx : t ⟨x, hxB⟩ = ⟨x, hxB⟩) :
    GGHLLines (ggHLRoots (fun i => ggLin (p := p) ι (φ i)) h) (ι (Additive.ofMul ⟨x, hxB⟩))
      (ggLin (p := p) ι t) := by
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs) := by
    intro b
    rw [ggGamma_eq_one_iff L hBsN b]
    constructor
    · intro hc
      have h2 : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨b.2, hc⟩
      rw [inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxB hS.2.2.1 hLx hS.2.2.2.2] at h2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    · intro hb
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hbG : (b : G) = x ^ k := by
        have h := congrArg Subtype.val hk
        rw [Subgroup.coe_zpow] at h
        exact h.symm
      have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
      have hbcent : (b : G) ∈ Subgroup.centralizer (L : Set G) := by
        rw [hbG]
        exact Subgroup.zpow_mem (Subgroup.centralizer (L : Set G)) hxcent k
      exact hbcent
  obtain ⟨VA, hVAadd, hVAmod, ιA, q, hA', αA, hqι, hqsurj, hqker, hqh, hqα, hlinA⟩ :=
    ggHL_descent hBsN hxB hker ι φ h α hlin hxker ψ hcompat
  letI : AddCommGroup VA := hVAadd
  letI : Module (ZMod p) VA := hVAmod
  have hpairA : ∀ i j, αA i (hA' j) = (C i j : ZMod p) := by
    intro i j
    rw [← hqh j, hqα i, hpair i j]
  obtain ⟨g, hgB, hgL, hg, hconcl⟩ :=
    ggXFixedRefl_mem_ggHL hW hcfg hM hnc hBsN ιA ψ hA' αA hMw hC hpairA hlinA hA t ht htr hxB htx
  let cg : MulAut L := L.normalizerMonoidHom ⟨g, hgL⟩
  have hcgN : cg ∈ Subgroup.normalizer
      (((ggGamma L hBsN).range : Subgroup (MulAut L)) : Set (MulAut L)) :=
    normalizerMonoidHom_mem_normalizer_range_ggGamma hBsN hgB hgL
  let φ' : MulAut ↥(ggGamma L hBsN).range := ggConjAut (ggGamma L hBsN).range hcgN
  have hφ' : ∀ a : ↥(ggGamma L hBsN).range,
      ((φ' a : ↥(ggGamma L hBsN).range) : MulAut L) = cg * a * cg⁻¹ :=
    fun a => ggConjAut_apply (ggGamma L hBsN).range hcgN a
  have hmem : ggLin (p := p) ιA φ' ∈ ggHL ιA ψ hA' αA := hconcl φ' hφ'
  have hkey : ∀ b : ↥Bs, φ' ((ggGamma L hBsN).rangeRestrict b) =
      (ggGamma L hBsN).rangeRestrict (t b) := by
    intro b
    apply Subtype.ext
    have hgb : g * (b : G) * g⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hgB b).mp b.2
    have htb : (⟨g * (b : G) * g⁻¹, hgb⟩ : ↥Bs) = t b := Subtype.ext (hg b).symm
    rw [hφ', MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict,
      ggGamma_conj_normalizer L hBsN ⟨g, hgL⟩ b hgb, htb]
  have htransfer : ∀ v : V, q (ggLin (p := p) ι t v) = ggLin (p := p) ιA φ' (q v) := by
    intro v
    obtain ⟨a, rfl⟩ := ι.surjective v
    set b : ↥Bs := Additive.toMul a with hb
    change q (ggLin (p := p) ι t (ι (Additive.ofMul b))) =
      ggLin (p := p) ιA φ' (q (ι (Additive.ofMul b)))
    calc q (ggLin (p := p) ι t (ι (Additive.ofMul b)))
        = q (ι (Additive.ofMul (t b))) := by rw [ggLin_apply_ofMul]
      _ = ιA (Additive.ofMul ((ggGamma L hBsN).rangeRestrict (t b))) := by rw [hqι]
      _ = ιA (Additive.ofMul (φ' ((ggGamma L hBsN).rangeRestrict b))) := by rw [hkey b]
      _ = ggLin (p := p) ιA φ'
            (ιA (Additive.ofMul ((ggGamma L hBsN).rangeRestrict b))) := by
            rw [ggLin_apply_ofMul]
      _ = ggLin (p := p) ιA φ' (q (ι (Additive.ofMul b))) := by rw [hqι]
  have hsqA : ∀ i, ψ i ^ 2 = 1 := by
    intro i
    apply MulEquiv.ext
    intro a
    obtain ⟨b, rfl⟩ := (ggGamma L hBsN).rangeRestrict_surjective a
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

end CFSG.StandardType
