module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBInputs
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableVec
import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableOrbits
import CFSG.LieType.Chevalley.WeylRoots
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitCount

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.NTPlane

variable {G : Type} [Group G] [Finite G]

private theorem glueRootTwE6Aux_pairVec_single_left (k : Fin Tag.E6.rank)
    (v : Fin Tag.E6.rank → ℤ) :
    pairVec (Pi.single k 1 : X3) v = (v k : ZMod 3) := by
  simp [pairVec, Pi.single_apply]

private theorem glueRootTwE6Aux_pairVec_neg (x : X3) (v : Fin Tag.E6.rank → ℤ) :
    pairVec x (-v) = -pairVec x v := by
  have hadd := pairVec_add x (-v) v
  rw [neg_add_cancel] at hadd
  have h0 : pairVec x (0 : Fin Tag.E6.rank → ℤ) = 0 := by simp [pairVec]
  rw [h0] at hadd
  exact eq_neg_of_add_eq_zero_left hadd.symm

private theorem glueRootTwE6Aux_pairVec_add_left (x y : X3)
    (v : Fin Tag.E6.rank → ℤ) :
    pairVec (x + y) v = pairVec x v + pairVec y v := by
  simp [pairVec, add_mul, Finset.sum_add_distrib]

open scoped CFSG.Decide.Bounded in
private theorem glueRootTwE6Aux_root_eq_of_coe_eq :
    ∀ α ∈ e6RootList, ∀ β ∈ e6RootList,
      (∀ k : Fin Tag.E6.rank, ((α k : ℤ) : ZMod 3) = ((β k : ℤ) : ZMod 3)) → α = β := by
  decide +kernel

omit [Finite G] in
private theorem glueRootTwE6Aux_exists {Bs L : Subgroup G} {x z : G}
    (hBs : IsElemAbelian 3 Bs) (hxBs : x ∈ Bs) (hzBs : z ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) {u : G → X3}
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu0 : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x)
    (hsurj : ∀ v : X3, ∃ b ∈ Bs, u b = v)
    (hW : ∀ w : WeylGroup Tag.E6, ∃ m ∈ L, m ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b ∈ Bs, u (m * b * m⁻¹) = w • u b)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hαz : pairVec (u z) α = 0) :
    ∃ ψ : MulAut ↥Bs, ψ ∈ frameReflSet (ggAutomizer L Bs) ∧
      ψ ⟨z, hzBs⟩ = ⟨z, hzBs⟩ ∧ ∀ b : ↥Bs, ψ b = b ↔ pairVec (u b) α = 0 := by
  classical
  obtain ⟨w, i, hw⟩ := isRoot_iff_exists_smul_single.mp hα
  let r : WeylGroup Tag.E6 := w * simple Tag.E6 i * w⁻¹
  have hrdef : r = w * simple Tag.E6 i * w⁻¹ := rfl
  have hr2 : r * r = 1 := by
    rw [hrdef]
    calc (w * simple Tag.E6 i * w⁻¹) * (w * simple Tag.E6 i * w⁻¹)
        = w * (simple Tag.E6 i * simple Tag.E6 i) * w⁻¹ := by group
      _ = 1 := by rw [(coxeterSystem Tag.E6).simple_mul_simple_self i]; group
  have hinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hr3 : r ^ 3 = r := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, hr2, one_mul]
  obtain ⟨m, hmL, hmN, hmu⟩ := hW r
  let φ : MulAut ↥Bs := ggConjAut Bs hmN
  have hφdef : φ = ggConjAut Bs hmN := rfl
  have hu1 : u 1 = 0 := (hu0 1 Bs.one_mem).mpr (Subgroup.one_mem (Subgroup.zpowers x))
  have hu_inv : ∀ b ∈ Bs, u b⁻¹ = -u b := by
    intro b hb
    have h := hadd b hb b⁻¹ (Subgroup.inv_mem _ hb)
    rw [mul_inv_cancel, hu1] at h
    exact (eq_neg_iff_add_eq_zero).mpr (by rw [add_comm]; exact h.symm)
  have hφx : φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
    rw [hφdef]
    apply Subtype.ext
    rw [ggConjAut_apply]
    have hcomm : x * m = m * x :=
      (Subgroup.mem_centralizer_iff.mp (hLx hmL)) x (Set.mem_singleton x)
    rw [← hcomm]
    group
  have huφ : ∀ b : ↥Bs, u (φ b) = r • u b := by
    intro b
    rw [hφdef, ggConjAut_apply]
    exact hmu b b.2
  have hpow : ∀ n : ℕ, ∀ b : ↥Bs, u (((φ ^ n) b : ↥Bs) : G) = r ^ n • u b := by
    intro n
    induction n with
    | zero =>
      intro b
      simp
    | succ n ih =>
      intro b
      calc u (((φ ^ (n + 1)) b : ↥Bs) : G)
          = u (φ ((φ ^ n) b)) := by rw [pow_succ', MulAut.mul_apply]
        _ = r • u (((φ ^ n) b : ↥Bs) : G) := huφ ((φ ^ n) b)
        _ = r • (r ^ n • u b) := by rw [ih b]
        _ = (r * r ^ n) • u b := by rw [smul_smul]
        _ = r ^ (n + 1) • u b := by rw [pow_succ']
  have hφ2u : ∀ b : ↥Bs, u (((φ ^ 2) b : ↥Bs) : G) = u b := by
    intro b
    rw [hpow 2 b]
    have h2 : r ^ 2 = 1 := by rw [pow_two]; exact hr2
    rw [h2, one_smul]
  have hφ2b : ∀ b : ↥Bs, ∃ k : ℤ, (φ ^ 2) b = (⟨x, hxBs⟩ : ↥Bs) ^ k * b := by
    intro b
    have hb2 : ((((φ ^ 2) b) * b⁻¹ : ↥Bs) : G) ∈ Subgroup.zpowers x := by
      refine (hu0 _ (Subgroup.mul_mem _ ((φ ^ 2) b).2 (Subgroup.inv_mem _ b.2))).mp ?_
      rw [hadd _ ((φ ^ 2) b).2 _ (Subgroup.inv_mem _ b.2), hφ2u b, hu_inv b b.2]
      abel
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb2
    refine ⟨k, ?_⟩
    have hk' : (⟨x, hxBs⟩ : ↥Bs) ^ k = ((φ ^ 2) b) * b⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk
    rw [hk']
    group
  have hφ2x : (φ ^ 2) ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
    rw [pow_two, MulAut.mul_apply, hφx, hφx]
  have hfix2 : ∀ n : ℤ,
      (φ ^ 2) ((⟨x, hxBs⟩ : ↥Bs) ^ n) = (⟨x, hxBs⟩ : ↥Bs) ^ n := by
    intro n
    rw [map_zpow, hφ2x]
  have hstep2 : ∀ (n : ℤ) (b : ↥Bs),
      (φ ^ 2) ((⟨x, hxBs⟩ : ↥Bs) ^ n * b) =
        (⟨x, hxBs⟩ : ↥Bs) ^ n * (φ ^ 2) b := by
    intro n b
    rw [map_mul, hfix2 n]
  have hx3 : (⟨x, hxBs⟩ : ↥Bs) ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBs.2 x hxBs
  have hφ6b : ∀ b : ↥Bs, (φ ^ 6) b = b := by
    intro b
    obtain ⟨k, hk⟩ := hφ2b b
    have h4 : (φ ^ 4) b = (⟨x, hxBs⟩ : ↥Bs) ^ (2 * k) * b := by
      have h4' : (φ ^ 4) b = (φ ^ 2) ((φ ^ 2) b) := by
        rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, MulAut.mul_apply]
      rw [h4', hk, hstep2, hk, ← mul_assoc, ← zpow_add, show k + k = 2 * k by ring]
    have h6 : (φ ^ 6) b = (φ ^ 2) ((φ ^ 4) b) := by
      rw [show (6 : ℕ) = 2 + 4 by norm_num, pow_add, MulAut.mul_apply]
    rw [h6, h4, hstep2, hk, ← mul_assoc, ← zpow_add,
      show 2 * k + k = 3 * k by ring, zpow_mul, hx3,
      one_zpow, one_mul]
  let ψ : MulAut ↥Bs := φ ^ 3
  have hψdef : ψ = φ ^ 3 := rfl
  have hψx : ψ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
    rw [hψdef, show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, MulAut.mul_apply, hφx, hφ2x]
  have hψ2 : ψ ^ 2 = 1 := by
    rw [hψdef]
    ext b
    have h6 : (φ ^ 3) ^ 2 = φ ^ 6 := by rw [← pow_mul]
    rw [h6, hφ6b b, MulAut.one_apply]
  have hψu : ∀ b : ↥Bs, u (ψ b) = r • u b := by
    intro b
    rw [hψdef, hpow 3 b, hr3]
  have hrα : r • α = -α := by
    rw [hrdef]
    have h := conj_simple_smul w i α
    have h2 : w⁻¹ • α = (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
      rw [← hw, ← mul_smul, inv_mul_cancel, one_smul]
    rw [h2, hw] at h
    have h3 : (∑ j, Tag.E6.cartan i j * (Pi.single i 1 : Fin Tag.E6.rank → ℤ) j) = 2 := by
      simp [Pi.single_apply, Tag.cartan_self]
    rw [h3] at h
    rw [h, two_zsmul]
    abel
  have hkey : ∀ y : X3, r • y = y ↔ pairVec y α = 0 := by
    intro y
    constructor
    · intro hy
      have h1 : pairVec (r • y) α = pairVec y α := by rw [hy]
      rw [pairVec_smul, hinv, hrα, glueRootTwE6Aux_pairVec_neg] at h1
      have hz3 : ∀ a : ZMod 3, -a = a → a = 0 := by decide
      exact hz3 _ h1
    · intro hy
      apply pairVec_eq_of_forall
      intro β
      rw [pairVec_smul, hinv]
      have h1 : r • β = β - (∑ j, Tag.E6.cartan i j * (w⁻¹ • β) j) • α := by
        rw [hrdef]
        have h := conj_simple_smul w i β
        rw [hw] at h
        exact h
      rw [h1, pairVec_sub, pairVec_zsmul, hy, mul_zero]
      simp
  have hstepψ : ∀ (n : ℤ) (b : ↥Bs),
      ψ ((⟨x, hxBs⟩ : ↥Bs) ^ n * b) = (⟨x, hxBs⟩ : ↥Bs) ^ n * ψ b := by
    intro n b
    have hfixψ : ψ ((⟨x, hxBs⟩ : ↥Bs) ^ n) = (⟨x, hxBs⟩ : ↥Bs) ^ n := by
      rw [map_zpow, hψx]
    rw [map_mul, hfixψ]
  have hfix : ∀ b : ↥Bs, ψ b = b ↔ pairVec (u b) α = 0 := by
    intro b
    constructor
    · intro hb
      have h1 : u (ψ b) = u b := by rw [hb]
      rw [hψu b] at h1
      exact (hkey (u b)).mp h1
    · intro hy
      have h1 : r • u b = u b := (hkey (u b)).mpr hy
      have h2 : u (ψ b) = u b := by rw [hψu b, h1]
      have hmem : (((ψ b) * b⁻¹ : ↥Bs) : G) ∈ Subgroup.zpowers x := by
        refine (hu0 _ (Subgroup.mul_mem _ (ψ b).2 (Subgroup.inv_mem _ b.2))).mp ?_
        rw [hadd _ (ψ b).2 _ (Subgroup.inv_mem _ b.2), h2, hu_inv b b.2]
        abel
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hk' : (⟨x, hxBs⟩ : ↥Bs) ^ k = (ψ b) * b⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow]
        exact hk
      have hψb : ψ b = (⟨x, hxBs⟩ : ↥Bs) ^ k * b := by
        rw [hk']
        group
      have hψψ : ψ (ψ b) = b := by
        have h := congrArg (fun τ : MulAut ↥Bs => τ b) hψ2
        simpa [pow_two, MulAut.mul_apply] using h
      have h2k : (⟨x, hxBs⟩ : ↥Bs) ^ (2 * k) * b = b := by
        calc (⟨x, hxBs⟩ : ↥Bs) ^ (2 * k) * b
            = (⟨x, hxBs⟩ : ↥Bs) ^ k * ((⟨x, hxBs⟩ : ↥Bs) ^ k * b) := by
              rw [← mul_assoc, ← zpow_add, show k + k = 2 * k by ring]
          _ = (⟨x, hxBs⟩ : ↥Bs) ^ k * ψ b := by rw [← hψb]
          _ = ψ ((⟨x, hxBs⟩ : ↥Bs) ^ k * b) := by rw [hstepψ]
          _ = ψ (ψ b) := by rw [← hψb]
          _ = b := hψψ
      have hx2k : (⟨x, hxBs⟩ : ↥Bs) ^ (2 * k) = 1 := by
        have h := congrArg (fun t : ↥Bs => t * b⁻¹) h2k
        simpa [mul_assoc] using h
      have h3k : (⟨x, hxBs⟩ : ↥Bs) ^ (3 * k) = 1 := by
        rw [zpow_mul, hx3, one_zpow]
      have hk1 : (⟨x, hxBs⟩ : ↥Bs) ^ k = 1 := by
        rw [show k = 3 * k + -(2 * k) by ring, zpow_add, h3k, one_mul, zpow_neg, hx2k,
          inv_one]
      rw [hψb, hk1, one_mul]
  let d : Additive ↥Bs →+ ZMod 3 :=
    AddMonoidHom.mk' (fun b => pairVec (u ((Additive.toMul b : ↥Bs) : G)) α) (by
      intro b b'
      show pairVec (u (((Additive.toMul b : ↥Bs) : G) *
          ((Additive.toMul b' : ↥Bs) : G))) α =
        pairVec (u ((Additive.toMul b : ↥Bs) : G)) α +
          pairVec (u ((Additive.toMul b' : ↥Bs) : G)) α
      rw [hadd _ (Additive.toMul b).2 _ (Additive.toMul b').2,
        glueRootTwE6Aux_pairVec_add_left])
  have hd : ∀ b : ↥Bs, d (Additive.ofMul b) = pairVec (u b) α := fun _ => rfl
  have hcard : Nat.card {b : ↥Bs // ψ b = b} = Nat.card ↥d.ker := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun b => ⟨Additive.ofMul b.1, ?_⟩
        invFun := fun z => ⟨Additive.toMul z.1, ?_⟩
        left_inv := fun b => Subtype.ext (by simp)
        right_inv := fun z => Subtype.ext (by simp) }
    · rw [AddMonoidHom.mem_ker, hd]
      exact (hfix b.1).mp b.2
    · apply (hfix (Additive.toMul z.1)).mpr
      change d z.1 = 0
      exact AddMonoidHom.mem_ker.mp z.2
  have hker : Nat.card ↥d.ker * 3 = Nat.card ↥Bs := by
    obtain ⟨b0, hb0Bs, hb0u⟩ := hsurj (w • (Pi.single i 1 : X3))
    have hb0val : pairVec (u b0) α = 1 := by
      rw [hb0u, pairVec_smul]
      have h2 : w⁻¹ • α = (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
        rw [← hw, ← mul_smul, inv_mul_cancel, one_smul]
      rw [h2, pairVec_single]
      simp
    have hd0 : d (Additive.ofMul ⟨b0, hb0Bs⟩) ≠ 0 := by
      rw [hd, hb0val]
      exact one_ne_zero
    have htop : AddSubgroup.zmultiples (d (Additive.ofMul ⟨b0, hb0Bs⟩)) = ⊤ :=
      zmultiples_eq_top_of_prime_card (Nat.card_zmod 3) hd0
    have hle : AddSubgroup.zmultiples (d (Additive.ofMul ⟨b0, hb0Bs⟩)) ≤ d.range :=
      AddSubgroup.zmultiples_le_of_mem (AddMonoidHom.mem_range.mpr ⟨_, rfl⟩)
    have hrange : d.range = ⊤ := top_le_iff.mp (htop ▸ hle)
    have h := AddSubgroup.card_ker_mul_card_range d
    rw [hrange, AddSubgroup.card_top, Nat.card_zmod] at h
    rw [Nat.card_congr Additive.toMul] at h
    exact h
  have hψrefl : GGIsReflection 3 ψ := ⟨hψ2, by rw [hcard, hker]⟩
  have hψmem : ψ ∈ ggAutomizer L Bs := by
    rw [hψdef]
    exact Subgroup.pow_mem _ (ggConjAut_mem_ggAutomizer hmL hmN) 3
  refine ⟨ψ, ⟨hψmem, hψrefl⟩, (hfix ⟨z, hzBs⟩).mpr hαz, hfix⟩

omit [Finite G] in
private theorem glueRootTwE6Aux_eq_or_neg {Bs : Subgroup G} {u : G → X3}
    (hBs : IsElemAbelian 3 Bs)
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hsurj : ∀ v : X3, ∃ b ∈ Bs, u b = v)
    {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (hker : ∀ b : ↥Bs, pairVec (u b) α = 0 ↔ pairVec (u b) β = 0) :
    α = β ∨ α = -β := by
  classical
  let f : Additive ↥Bs →+ ZMod 3 :=
    AddMonoidHom.mk' (fun b => pairVec (u ((Additive.toMul b : ↥Bs) : G)) α) (by
      intro b b'
      show pairVec (u (((Additive.toMul b : ↥Bs) : G) *
          ((Additive.toMul b' : ↥Bs) : G))) α =
        pairVec (u ((Additive.toMul b : ↥Bs) : G)) α +
          pairVec (u ((Additive.toMul b' : ↥Bs) : G)) α
      rw [hadd _ (Additive.toMul b).2 _ (Additive.toMul b').2,
        glueRootTwE6Aux_pairVec_add_left])
  let g : Additive ↥Bs →+ ZMod 3 :=
    AddMonoidHom.mk' (fun b => pairVec (u ((Additive.toMul b : ↥Bs) : G)) β) (by
      intro b b'
      show pairVec (u (((Additive.toMul b : ↥Bs) : G) *
          ((Additive.toMul b' : ↥Bs) : G))) β =
        pairVec (u ((Additive.toMul b : ↥Bs) : G)) β +
          pairVec (u ((Additive.toMul b' : ↥Bs) : G)) β
      rw [hadd _ (Additive.toMul b).2 _ (Additive.toMul b').2,
        glueRootTwE6Aux_pairVec_add_left])
  have hf0 : ∀ b : Additive ↥Bs, f b = 0 ↔ g b = 0 := fun b => hker (Additive.toMul b)
  obtain ⟨w, i, hw⟩ := isRoot_iff_exists_smul_single.mp hα
  obtain ⟨b0, hb0Bs, hb0u⟩ := hsurj (w • (Pi.single i 1 : X3))
  have hb0val : pairVec (u b0) α = 1 := by
    rw [hb0u, pairVec_smul]
    have h2 : w⁻¹ • α = (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
      rw [← hw, ← mul_smul, inv_mul_cancel, one_smul]
    rw [h2, pairVec_single]
    simp
  have hfne : f ≠ 0 := by
    intro hf
    have h : f (Additive.ofMul ⟨b0, hb0Bs⟩) = 0 := by rw [hf]; rfl
    rw [show f (Additive.ofMul ⟨b0, hb0Bs⟩) = pairVec (u b0) α from rfl, hb0val] at h
    exact one_ne_zero h
  let cg : CommGroup ↥Bs :=
    { (inferInstance : Group ↥Bs) with
      mul_comm := fun a b =>
        Subtype.ext (congrArg (fun t : ↥Bs => (t : G)) (hBs.1.is_comm.comm a b)) }
  obtain ⟨c, hc⟩ :=
    @CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.exists_smul_of_ker_eq_addHom
      (Additive ↥Bs) (@Additive.addCommGroup ↥Bs cg) 3 Nat.fact_prime_three
      f g hfne hf0
  have hcne : c ≠ 0 := by
    intro hc0
    have h := hc (Additive.ofMul ⟨b0, hb0Bs⟩)
    rw [show g (Additive.ofMul ⟨b0, hb0Bs⟩) = pairVec (u b0) β from rfl,
      show f (Additive.ofMul ⟨b0, hb0Bs⟩) = pairVec (u b0) α from rfl, hb0val, hc0,
      mul_one] at h
    have h' : pairVec (u b0) α = 0 := (hker ⟨b0, hb0Bs⟩).mpr h
    rw [hb0val] at h'
    exact one_ne_zero h'
  have hcoord : ∀ k : Fin Tag.E6.rank,
      ((β k : ℤ) : ZMod 3) = c * ((α k : ℤ) : ZMod 3) := by
    intro k
    obtain ⟨bk, hbkBs, hbku⟩ := hsurj (Pi.single k 1 : X3)
    have h := hc (Additive.ofMul ⟨bk, hbkBs⟩)
    rw [show g (Additive.ofMul ⟨bk, hbkBs⟩) = pairVec (u bk) β from rfl,
      show f (Additive.ofMul ⟨bk, hbkBs⟩) = pairVec (u bk) α from rfl, hbku] at h
    rw [glueRootTwE6Aux_pairVec_single_left k β,
      glueRootTwE6Aux_pairVec_single_left k α] at h
    exact h
  have hcases : c = 1 ∨ c = 2 := by
    have h : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = 2 := by decide
    exact h c hcne
  have hαlist : α ∈ e6RootList := (isRoot_iff_mem_e6RootList α).mp hα
  have hβlist : β ∈ e6RootList := (isRoot_iff_mem_e6RootList β).mp hβ
  rcases hcases with hc1 | hc2
  · left
    refine glueRootTwE6Aux_root_eq_of_coe_eq α hαlist β hβlist fun k => ?_
    rw [hcoord k, hc1, one_mul]
  · right
    have hneg : -α ∈ e6RootList := (isRoot_iff_mem_e6RootList (-α)).mp (IsRoot.neg hα)
    have h : β = -α := by
      refine glueRootTwE6Aux_root_eq_of_coe_eq β hβlist (-α) hneg fun k => ?_
      have h2 : ∀ a : ZMod 3, (2 : ZMod 3) * a = -a := by decide
      calc ((β k : ℤ) : ZMod 3) = c * ((α k : ℤ) : ZMod 3) := hcoord k
        _ = (2 : ZMod 3) * ((α k : ℤ) : ZMod 3) := by rw [hc2]
        _ = -((α k : ℤ) : ZMod 3) := h2 _
        _ = (((-α) k : ℤ) : ZMod 3) := by
            rw [Pi.neg_apply]
            exact (Int.cast_neg (α k)).symm
    rw [h, neg_neg]

theorem thirteen_le_of_kerRoots {Bs L : Subgroup G} {x z : G}
    (hBs : IsElemAbelian 3 Bs) (hxBs : x ∈ Bs) (hzBs : z ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) {u : G → NTPlane.X3}
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu0 : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x)
    (hsurj : ∀ v : NTPlane.X3, ∃ b ∈ Bs, u b = v)
    (hz : (NTPlane.kerRoots (u z)).ncard = 30 ∨ (NTPlane.kerRoots (u z)).ncard = 40)
    (hW : ∀ w : WeylGroup Tag.E6, ∃ m ∈ L, m ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b ∈ Bs, u (m * b * m⁻¹) = w • u b) :
    13 ≤ ({φ | φ ∈ frameReflSet (ggAutomizer L Bs) ∧ φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩} :
      Set (MulAut ↥Bs)).ncard := by
  classical
  let S : Finset (Fin Tag.E6.rank → ℤ) :=
    e6RootList.toFinset.filter (fun α => pairVec (u z) α = 0)
  let T : Set (MulAut ↥Bs) :=
    {φ | φ ∈ frameReflSet (ggAutomizer L Bs) ∧ φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩}
  have hSset : (S : Set (Fin Tag.E6.rank → ℤ)) = kerRoots (u z) := by
    ext α
    simp [S, kerRoots, isRoot_iff_mem_e6RootList]
  have hScard : S.card = 30 ∨ S.card = 40 := by
    rw [← Set.ncard_coe_finset S, hSset]
    exact hz
  have hSroot : ∀ α, α ∈ S → IsRoot Tag.E6 α := by
    intro α hα
    simp only [S, Finset.mem_filter, List.mem_toFinset] at hα
    exact (isRoot_iff_mem_e6RootList α).mpr hα.1
  have hSz : ∀ α, α ∈ S → pairVec (u z) α = 0 := by
    intro α hα
    simp only [S, Finset.mem_filter, List.mem_toFinset] at hα
    exact hα.2
  have hex : ∀ α : Fin Tag.E6.rank → ℤ, α ∈ S →
      ∃ φ : MulAut ↥Bs, φ ∈ T ∧ ∀ b : ↥Bs, φ b = b ↔ pairVec (u b) α = 0 := by
    intro α hα
    obtain ⟨φ, hφframe, hφz, hφfix⟩ :=
      glueRootTwE6Aux_exists hBs hxBs hzBs hLx hadd hu0 hsurj hW
        (hSroot α hα) (hSz α hα)
    exact ⟨φ, ⟨hφframe, hφz⟩, hφfix⟩
  let F : ↥S → ↥T := fun a => ⟨(hex a.1 a.2).choose, (hex a.1 a.2).choose_spec.1⟩
  have hFspec : ∀ a : ↥S, ∀ b : ↥Bs, (F a).1 b = b ↔ pairVec (u b) a.1 = 0 :=
    fun a => (hex a.1 a.2).choose_spec.2
  have hfib : ∀ b ∈ Finset.image F S.attach,
      (S.attach.filter (fun a => F a = b)).card ≤ 2 := by
    intro b hb
    obtain ⟨a0, -, rfl⟩ := Finset.mem_image.mp hb
    have hsub : (S.attach.filter (fun a => F a = F a0)).image Subtype.val ⊆
        ({a0.1, -a0.1} : Finset (Fin Tag.E6.rank → ℤ)) := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      have ha' : F a = F a0 := (Finset.mem_filter.mp ha).2
      have hker : ∀ b : ↥Bs, pairVec (u b) a.1 = 0 ↔ pairVec (u b) a0.1 = 0 := by
        intro b
        rw [← hFspec a b, ← hFspec a0 b, ha']
      rcases glueRootTwE6Aux_eq_or_neg hBs hadd hsurj (hSroot a.1 a.2)
        (hSroot a0.1 a0.2) hker with h | h
      · rw [h]
        simp
      · rw [h]
        simp
    calc (S.attach.filter (fun a => F a = F a0)).card
        = ((S.attach.filter (fun a => F a = F a0)).image Subtype.val).card := by
          rw [Finset.card_image_of_injective _ Subtype.val_injective]
      _ ≤ ({a0.1, -a0.1} : Finset (Fin Tag.E6.rank → ℤ)).card := Finset.card_le_card hsub
      _ ≤ 2 := by
          have h := Finset.card_insert_le a0.1
            ({-a0.1} : Finset (Fin Tag.E6.rank → ℤ))
          simpa using h
  have himage : 15 ≤ (Finset.image F S.attach).card := by
    have h := Finset.card_le_mul_card_image (f := F) S.attach 2 hfib
    rw [Finset.card_attach] at h
    rcases hScard with h30 | h40 <;> omega
  have hleT : (Finset.image F S.attach).card ≤ T.ncard := by
    have h := Set.ncard_le_ncard
      (Set.subset_univ ((Finset.image F S.attach : Finset ↥T) : Set ↥T))
    rw [Set.ncard_univ] at h
    rwa [Set.ncard_coe_finset, Nat.card_coe_set_eq] at h
  have hT : 15 ≤ T.ncard := le_trans himage hleT
  show 13 ≤ T.ncard
  omega

end CFSG.StandardType.FrameRoute

end
