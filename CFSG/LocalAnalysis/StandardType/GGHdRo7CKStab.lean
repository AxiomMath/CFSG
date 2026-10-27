module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7KNC
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSPerm
import CFSG.LocalAnalysis.StandardType.GGSCNoTVCyclic
import CFSG.GroupTheory.GL52.SylowTools

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7CKStabAux_nsmul_ofMul {Bs : Type} [Group Bs] (y : Bs) (n : ℕ) :
    n • (Additive.ofMul y : Additive Bs) = Additive.ofMul (y ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [succ_nsmul, ih, pow_succ]; rfl

private lemma hdRo7CKStabAux_toMul_ofMul {Bs : Type} [Group Bs] (y : Bs) :
    Additive.toMul (Additive.ofMul y) = y := rfl

private lemma hdRo7CKStabAux_coord_signChange {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V) (j : Fin m) :
    (b.coord j).comp (CFSG.StandardType.OrthF3.ggOrthSignChange b j : V →ₗ[ZMod 3] V) =
      -b.coord j := by
  apply b.ext
  intro i
  by_cases hij : i = j
  · rw [hij]
    change b.coord j ((CFSG.StandardType.OrthF3.ggOrthSignChange b j) (b j)) =
      -b.coord j (b j)
    rw [CFSG.StandardType.OrthF3.ggOrthSignChange_apply_self, map_neg]
  · change b.coord j ((CFSG.StandardType.OrthF3.ggOrthSignChange b j) (b i)) =
      -b.coord j (b i)
    rw [CFSG.StandardType.OrthF3.ggOrthSignChange_apply_of_ne (f := b) (i := j) (j := i) hij]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, hij]

private lemma hdRo7CKStabAux_signChange_c2sp {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {j : Fin (n + 1)} (hj : j ≠ 0) :
    C2SP 3 b (CFSG.StandardType.OrthF3.ggOrthSignChange b j) := by
  refine ⟨Equiv.refl _, fun i => if i = j then (-1 : ZMod 3) else 1, rfl, ?_, ?_, ?_⟩
  · dsimp only
    rw [if_neg (fun h : (0 : Fin (n + 1)) = j => hj h.symm)]
  · intro i
    dsimp only
    by_cases hi : i = j
    · rw [if_pos hi]; exact Or.inr rfl
    · rw [if_neg hi]; exact Or.inl rfl
  · intro i
    dsimp only
    by_cases hi : i = j
    · subst hi
      rw [CFSG.StandardType.OrthF3.ggOrthSignChange_apply_self]
      simp
    · rw [CFSG.StandardType.OrthF3.ggOrthSignChange_apply_of_ne (f := b) (i := j) (j := i) hi]
      simp [hi]

private lemma hdRo7CKStabAux_mem_zpowers
    {G : Type} [Group G] {Bs K : Subgroup G} {y : G} (hy : y ∈ Bs)
    {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (hiy : ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = b 0)
    (hAK : ∀ a, a ∈ (ggAutomizer K Bs).map (ggLin (p := 3) ι) ↔ C2SP 3 b a)
    {β : G} (hβ : β ∈ Bs ⊓ Subgroup.centralizer (K : Set G)) :
    β ∈ Subgroup.zpowers y := by
  let v : V := ι (Additive.ofMul (⟨β, hβ.1⟩ : ↥Bs))
  have hfix : ∀ a : V ≃ₗ[ZMod 3] V, C2SP 3 b a → a v = v := by
    intro a ha
    obtain ⟨φ, hφ, hφa⟩ := Subgroup.mem_map.mp ((hAK a).mpr ha)
    obtain ⟨g, hgK, -, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    have hβcomm : g * β * g⁻¹ = β := by
      have hc := (Subgroup.mem_centralizer_iff.mp hβ.2) g hgK
      rw [hc]; group
    have hφβ : φ ⟨β, hβ.1⟩ = ⟨β, hβ.1⟩ := by
      apply Subtype.ext
      rw [hφg]
      exact hβcomm
    have hv : a v = ι (Additive.ofMul (φ ⟨β, hβ.1⟩)) := by
      rw [show a = ggLin (p := 3) ι φ from hφa.symm]
      change (ggLin (p := 3) ι φ) (ι (Additive.ofMul (⟨β, hβ.1⟩ : ↥Bs))) =
        ι (Additive.ofMul (φ ⟨β, hβ.1⟩))
      rw [ggLin_apply]
      simp
    rw [hv, hφβ]
  have hzero : ∀ j : Fin (n + 1), j ≠ 0 → b.coord j v = 0 := by
    intro j hj
    have haj := hdRo7CKStabAux_signChange_c2sp b hj
    have h1 := hfix (CFSG.StandardType.OrthF3.ggOrthSignChange b j) haj
    have h2 : b.coord j ((CFSG.StandardType.OrthF3.ggOrthSignChange b j) v) =
        -b.coord j v := by
      have := LinearMap.congr_fun (hdRo7CKStabAux_coord_signChange b j) v
      simpa [LinearMap.comp_apply] using this
    have hff : b.coord j v = -b.coord j v := by
      rw [← h2]
      exact (congrArg (b.coord j) h1).symm
    have h2f : (2 : ZMod 3) * b.coord j v = 0 := by
      have hff' : b.coord j v + b.coord j v = 0 := by
        have := (sub_eq_zero (a := b.coord j v) (b := -b.coord j v)).mpr hff
        simpa [sub_neg_eq_add] using this
      rwa [two_mul]
    exact (mul_eq_zero.mp h2f).resolve_left (by decide)
  have hv_eq : v = (b.coord 0 v) • b 0 := by
    apply b.repr.injective
    rw [map_smul, Module.Basis.repr_self]
    ext i
    rw [Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hi : i = 0
    · subst hi
      simp [Module.Basis.coord_apply]
    · rw [if_neg (fun h : (0 : Fin (n + 1)) = i => hi h.symm), smul_zero]
      rw [← Module.Basis.coord_apply]
      exact hzero i hi
  have hv2 : v = (b.coord 0 v).val • b 0 := by
    calc v = (b.coord 0 v) • b 0 := hv_eq
      _ = ((b.coord 0 v).val : ZMod 3) • b 0 :=
            congrArg (fun c : ZMod 3 => c • b 0) (ZMod.natCast_zmod_val (b.coord 0 v)).symm
      _ = (b.coord 0 v).val • b 0 :=
            Nat.cast_smul_eq_nsmul (R := ZMod 3) (b.coord 0 v).val (b 0)
  have hmap : v = ι (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ (b.coord 0 v).val)) := by
    conv_lhs => rw [hv2]
    conv_lhs => rw [← hiy]
    rw [← map_nsmul]
    exact congrArg ι (hdRo7CKStabAux_nsmul_ofMul (⟨y, hy⟩ : ↥Bs) (b.coord 0 v).val)
  have hβeq : (⟨β, hβ.1⟩ : ↥Bs) = (⟨y, hy⟩ : ↥Bs) ^ (b.coord 0 v).val := by
    apply Additive.ofMul.injective
    apply ι.injective
    exact hmap
  refine Subgroup.mem_zpowers_iff.mpr ⟨((b.coord 0 v).val : ℤ), ?_⟩
  rw [zpow_natCast]
  exact (congrArg Subtype.val hβeq).symm

private lemma hdRo7CKStabAux_card_le
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {y : G} (hy : y ∈ Bs) (hy1 : y ≠ 1)
    (hE : CFSG.Open.IsElemAbelian 3 Bs)
    {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (hiy : ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = b 0)
    (hAK : ∀ a, a ∈ (ggAutomizer K Bs).map (ggLin (p := 3) ι) ↔ C2SP 3 b a) :
    Nat.card (Bs ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤ 3 := by
  have hle : (Bs ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤ Subgroup.zpowers y :=
    fun β hβ => hdRo7CKStabAux_mem_zpowers hy ι b hiy hAK hβ
  have hcard := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at hcard
  have hdvd : orderOf y ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (hE.2 y hy)
  have hne1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
  have horder : orderOf y = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne1
  rwa [horder] at hcard

private theorem hdRo7CKStabAux_stab
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) [Fact p.Prime]
    (hnc : ∃ S : Subgroup G, S ≤ K ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (hy : y ∈ Bs)
    (h3 : p = 3) (hn : 5 ≤ n)
    (hiy : ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = b 0)
    (hAK : ∀ a, a ∈ (ggAutomizer K Bs).map (ggLin (p := p) ι) ↔ C2SP p b a)
    {a : V ≃ₗ[ZMod p] V} (ha : a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι))
    (ha0 : a (b 0) = b 0) :
    ∀ s, C2SP p b s → C2SP p b (a * s * a⁻¹) := by
  subst h3
  obtain ⟨hConf, hOpAut, hIDAll, hNoTV, hNbr, hReflGen, hScalWeyl⟩ := hH
  obtain ⟨hThmI, hBstar, hStdSub⟩ := hConf
  obtain ⟨hSimple, hnonab, hKproper, hCharTwo, hRank, hBeta, hSstarL, hStdType⟩ := hThmI
  obtain ⟨hBle, hE, hBcard, hSC⟩ := hBstar
  have hSHat : CFSG.Assembly.LargeEvenSHat 3 B y K := hNbr.1
  have hNeighbor := hNbr.2
  obtain ⟨hIDL, hIDallK⟩ := hIDAll
  obtain ⟨hBmax, hyB, hy1, hKC, hPcomp, hiff⟩ := hSHat
  have hIDK := hIDallK y K hNbr
  have hcomp := isComponentOf_of_isNeighborOf hStdType (isNeighborOf_of_ggNbr hStdSub hNbr)
  have hcard := hdRo7CKStabAux_card_le hy hy1 hE ι b hiy hAK
  have hEC : Bs ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
    fun b hb => normalizer_le_normalizer_centralizer K (ggInnerDiagOn_le_normalizer hIDK hb)
  have hSstar : CFSG.Assembly.LargeEvenSStar 3 B y K :=
    ⟨hBmax, hyB, hy1, hcomp.1, fun S hSle hSp =>
      ggSCNoTV_isCyclic (p := 3) (by norm_num) hE hSC hNoTV hEC hcard hSle hSp⟩
  obtain ⟨φ, hφ, hφa⟩ := Subgroup.mem_map.mp ha
  obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  have hgy_eq : g * y * g⁻¹ = y := by
    have h1 : ((ggLin (p := 3) ι) φ) (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) =
        ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by
      rw [hiy, hφa]; exact ha0
    rw [ggLin_apply] at h1
    simp only [AddEquiv.symm_apply_apply] at h1
    have h2 := ι.injective h1
    have h3 : φ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ := by
      simpa only [hdRo7CKStabAux_toMul_ofMul] using congrArg Additive.toMul h2
    have h4 : ((φ (⟨y, hy⟩ : ↥Bs) : ↥Bs) : G) = y := congrArg Subtype.val h3
    rw [hφg] at h4
    exact h4
  have hgy : g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) :=
    CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem
      (Subgroup.mem_zpowers_iff.mpr ⟨1, by rw [zpow_one]; exact hgy_eq.symm⟩)
  have hgKn : g ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_of_sstar' hSstar hnc hgy
  have hφi := inv_apply_of_forall hφg
  have hφnorm : φ ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro ψ
    constructor
    · intro hψ
      obtain ⟨l, hl, hlN, hψl⟩ := mem_ggAutomizer_iff.mp hψ
      refine mem_ggAutomizer_iff.mpr ⟨g * l * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hgKn l).mp hl,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hlN) (Subgroup.inv_mem _ hgN), fun b => ?_⟩
      rw [MulAut.mul_apply, MulAut.mul_apply, hφg, hψl, hφi]
      group
    · intro hψ
      obtain ⟨l, hl, hlN, hψl⟩ := mem_ggAutomizer_iff.mp hψ
      have hgKn' := Subgroup.inv_mem _ hgKn
      have hgN' := Subgroup.inv_mem _ hgN
      refine mem_ggAutomizer_iff.mpr ⟨g⁻¹ * l * g, ?_, ?_, fun b => ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.mp hgKn' l).mp hl
      · simpa using Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN' hlN) hgN
      · have hψeq : ψ = φ⁻¹ * (φ * ψ * φ⁻¹) * φ := by group
        rw [hψeq, MulAut.mul_apply, MulAut.mul_apply, hφi, hψl, hφg]
        group
  intro s hs
  obtain ⟨ψ, hψ, hψs⟩ := Subgroup.mem_map.mp ((hAK s).mpr hs)
  have hconj : φ * ψ * φ⁻¹ ∈ ggAutomizer K Bs :=
    (Subgroup.mem_normalizer_iff.mp hφnorm ψ).mp hψ
  have heq : a * s * a⁻¹ = (ggLin (p := 3) ι) (φ * ψ * φ⁻¹) := by
    rw [← hφa, ← hψs]
    simp only [map_mul, map_inv]
  rw [heq]
  exact (hAK _).mp (Subgroup.mem_map.mpr ⟨φ * ψ * φ⁻¹, hconj, rfl⟩)

theorem c2_kstab_holds : C2KStabLeaf := by
  intro G _ _ p B Bs x L D J y K hH hp hrow n V _ _ ι b hy h3 hn hiy hAK a ha ha0 s hs
  exact hdRo7CKStabAux_stab hH
    (CFSG.StandardType.HdRo7KNC.knc_holds G p B Bs x L D J y K hH (Or.inl hrow))
    ι b hy h3 hn hiy hAK ha ha0 s hs

end CFSG.StandardType.HdRo7C
