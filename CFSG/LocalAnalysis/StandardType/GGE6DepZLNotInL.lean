module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLFrame
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLPair
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLDict
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLCore
public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownInputsDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepConjAssembly
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelIndep
public import CFSG.LocalAnalysis.StandardType.GGE6DepKRefl
public import CFSG.LocalAnalysis.StandardType.GGE6DepKMatrix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly E6Dep

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggE6DepPerpXNotInL_of_zl (hRig : GGLabelRigidInput) (hM : GGE6DepModelKnown)
    (hZL : GGE6DepZLKnown) : GGE6DepPerpXNotInL := by
  intro G _ _ p B Bs x L D J hcfg _hop hinn hnt y K hnbr hE hxL
  classical
  have hE0 := hE
  obtain ⟨hp3, hcardBs, hD, lab₀, hlab₀, -, hmarkK⟩ := hE
  subst hp3
  obtain ⟨hyBs, hxy, hKy, hxK⟩ := ggE6Dep_nbr_facts hcfg hnbr
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC := hcfg.2.1.2.2.2
  have hxord : orderOf x = 3 := hcfg.orderOf_x
  have hy1 : y ≠ 1 := fun h => hxy (h ▸ Subgroup.one_mem _)
  have hy3 : y ^ 3 = 1 := hBs.2 y hyBs
  obtain ⟨hxBs, ι, hιx, hι1, hι2⟩ := ggE6Dep_frameLIn hRig hZL hcfg hinn.1 hnt hE0 hxL
  obtain ⟨Λ, _, _, b, ρ, ρa, hρrefl, hρa, hLgen, hKgen⟩ := ggDatum_reflections hD
  have hρL : ∀ l, ρ l ∈ ggAutomizer L Bs := fun l => by
    rw [hLgen]
    exact Subgroup.subset_closure ⟨l, rfl⟩
  have hρK : ∀ l : Λ, l ≠ b → ρ l ∈ ggAutomizer K Bs := fun l hl => by
    rw [hKgen]
    exact Subgroup.subset_closure (Or.inl ⟨⟨l, hl⟩, rfl⟩)
  have hρaK : ρa ∈ ggAutomizer K Bs := by
    rw [hKgen]
    exact Subgroup.subset_closure (Or.inr rfl)
  have hKfix : ∀ φ ∈ ggAutomizer K Bs, φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ :=
    ggAutomizer_fix_of_centralizes hyBs hKy
  have hyC : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact ((Subgroup.mem_centralizer_iff.mp (hKy hk)) y (Set.mem_singleton y)).symm
  choose g hgW hgA using fun l => hι1 (ρ l) (hρL l)
  have hgR : ∀ l, ZL.IsRefl6 (g l) := fun l =>
    ZL.isRefl6_of_ggIsReflection (hgA l) (hρrefl l) hcardBs
  have hgen : ∀ m ∈ ZL.closureU, m ∈ Submonoid.closure (Set.range g) :=
    ZL.closure_of_automizer_gen ρ g hLgen hgA (fun l => (hgR l).1) hι2
  obtain ⟨r, hr⟩ := exists_actsAs ι ρa
  have hrR : ZL.IsRefl6 r := ZL.isRefl6_of_ggIsReflection hr hρa hcardBs
  obtain ⟨yv, hyv⟩ : ∃ yv : Vec6, yv = ι (Additive.ofMul ⟨y, hyBs⟩) := ⟨_, rfl⟩
  have hy : ZL.cartanM.mulVec yv ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := ZL.rad_eq yv h0
    apply hxy
    have h1 : ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) =
        ι (Additive.ofMul ((⟨x, hxBs⟩ : ↥Bs) ^ a.val)) := by
      rw [ofMul_pow, map_nsmul, hιx, ← hyv, ha, ← Nat.cast_smul_eq_nsmul (ZMod 3),
        ZMod.natCast_zmod_val]
    have h2 : (⟨y, hyBs⟩ : ↥Bs) = ⟨x, hxBs⟩ ^ a.val :=
      Additive.ofMul.injective (ι.injective h1)
    have h3 : y = x ^ a.val := congrArg Subtype.val h2
    rw [h3]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
  have hgy : ∀ l, l ≠ b → (g l).mulVec yv = yv := fun l hl => by
    have h1 := hgA l ⟨y, hyBs⟩
    rw [hKfix (ρ l) (hρK l hl)] at h1
    rw [hyv]
    exact h1.symm
  have hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
    apply le_antisymm
    · intro bb hbb
      rw [Subgroup.mem_inf] at hbb
      obtain ⟨hbbBs, hbbC⟩ := hbb
      have hfixbb : ∀ φ ∈ ggAutomizer K Bs, φ ⟨bb, hbbBs⟩ = ⟨bb, hbbBs⟩ := by
        intro φ hφ
        obtain ⟨k, hkK, -, hφk⟩ := mem_ggAutomizer_iff.mp hφ
        apply Subtype.ext
        rw [hφk]
        have hc : k * bb = bb * k := Subgroup.mem_centralizer_iff.mp hbbC k hkK
        rw [hc]
        group
      have hfixl : ∀ l, l ≠ b → (g l).mulVec (ι (Additive.ofMul ⟨bb, hbbBs⟩)) =
          ι (Additive.ofMul ⟨bb, hbbBs⟩) := fun l hl => by
        have h1 := hgA l ⟨bb, hbbBs⟩
        rw [hfixbb (ρ l) (hρK l hl)] at h1
        exact h1.symm
      obtain ⟨a, c, habc⟩ := ZL.zl_fixS b g yv hgW hgR hgen hy hgy hfixl
      have hbbeq : (⟨bb, hbbBs⟩ : ↥Bs) = ⟨x, hxBs⟩ ^ a * ⟨y, hyBs⟩ ^ c := by
        apply Additive.ofMul.injective
        apply ι.injective
        rw [habc, ofMul_mul, map_add, ofMul_pow, ofMul_pow, map_nsmul, map_nsmul, hιx, hyv]
      have hbbval : bb = x ^ a * y ^ c := congrArg Subtype.val hbbeq
      by_cases ha : 3 ∣ a
      · obtain ⟨a', rfl⟩ := ha
        have h1 : x ^ (3 * a') = 1 := by rw [pow_mul, hBs.2 x hxBs, one_pow]
        rw [hbbval, h1, one_mul]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) c
      · exfalso
        have hxa : x ^ a ∈ Subgroup.centralizer (K : Set G) := by
          have h4 : x ^ a = bb * (y ^ c)⁻¹ := by rw [hbbval]; group
          rw [h4]
          exact Subgroup.mul_mem _ hbbC (Subgroup.inv_mem _ (Subgroup.pow_mem _ hyC c))
        have h5 : a % 3 = 1 ∨ a % 3 = 2 := by omega
        have h6 : a * a % 3 = 1 := by
          rcases h5 with h | h <;> simp [Nat.mul_mod, h]
        have h7 : x = (x ^ a) ^ a := by
          have h8 := pow_mod_orderOf x (a * a)
          rw [hxord, h6, pow_one] at h8
          rw [← pow_mul]
          exact h8
        exact hxK (h7 ▸ Subgroup.pow_mem _ hxa a)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨hyBs, hyC⟩
  obtain ⟨κK, hκK⟩ :=
    ggE6Dep_frameK hRig hM hy1 hBs hSC hcardBs hlab₀ hmarkK (hinn.2 y K hnbr) hker
  have actsPow : ∀ (φ : MulAut ↥Bs) (m : Mat6), ActsAs ι φ m →
      ∀ n : ℕ, ActsAs ι (φ ^ n) (m ^ n) := by
    intro φ m h n
    induction n with
    | zero => simpa only [pow_zero] using ActsAs.one ι
    | succ n ihn =>
      rw [pow_succ, pow_succ]
      exact ihn.mul h
  have hpair : ∀ l, l ≠ b → (g l * r) ^ 2 = 1 ∨ (g l * r) ^ 3 = 1 := by
    intro l hl
    have hl' := ZL.ggE6Dep_pairOrder_K hyBs hy1 hBs hcardBs hκK hnt hKy (hρK l hl) hρaK
      (hρrefl l) hρa
    have hm := (hgA l).mul hr
    rcases hl' with h2 | h3
    · left
      have h4 := actsPow _ _ hm 2
      rw [h2] at h4
      exact actsAs_inj h4 (ActsAs.one ι)
    · right
      have h4 := actsPow _ _ hm 3
      rw [h3] at h4
      exact actsAs_inj h4 (ActsAs.one ι)
  have hrκ : r.mulVec ZL.kappa = ZL.kappa := ZL.zl_core b g r yv hgW hgR hgen hrR hy hgy hpair
  have hxfix : ggAutomizer K Bs ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxBs⟩ : ↥Bs) := by
    rw [hKgen, Subgroup.closure_le]
    rintro φ (⟨⟨l, hl⟩, rfl⟩ | rfl)
    · rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
      apply Additive.ofMul.injective
      apply ι.injective
      rw [hgA l ⟨x, hxBs⟩, hιx, ZL.closureU_fix_kappa (hgW l)]
    · rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
      apply Additive.ofMul.injective
      apply ι.injective
      rw [hr ⟨x, hxBs⟩, hιx, hrκ]
  have hκx : κK (Additive.ofMul ⟨x, hxBs⟩) = 0 := by
    apply ZL.closureL_fixed_zero (hκK.2.1 _)
    intro m hm
    obtain ⟨φ, hφ, hact⟩ := hκK.2.2.2.2 m hm
    have h1 := hact ⟨x, hxBs⟩
    have h2 : φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
      have := MulAction.mem_stabilizer_iff.mp (hxfix hφ)
      rwa [MulAut.smul_def] at this
    rw [h2] at h1
    exact h1.symm
  have hxy' : x ∈ Subgroup.zpowers y := (hκK.1 ⟨x, hxBs⟩).mp hκx
  apply hxy
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hxy'
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hcard : Nat.card (Subgroup.zpowers y) ≤ Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hyord]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  exact Subgroup.mem_zpowers y

end CFSG.StandardType

end
