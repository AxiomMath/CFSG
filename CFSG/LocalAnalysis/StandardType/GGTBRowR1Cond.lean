module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Datum
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Kg
import CFSG.LocalAnalysis.StandardType.GGSecFiveJReflOfCore
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTags
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcRefl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflCartan
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section NormalClosure

variable {G : Type} [Group G]

theorem conj_mem_ggAutNormalClosure_of_mem {L J Bs : Subgroup G} {c φ : MulAut ↥Bs}
    (hc : c ∈ ggAutomizer L Bs) (hφ : φ ∈ ggAutNormalClosure L J Bs) :
    c * φ * c⁻¹ ∈ ggAutNormalClosure L J Bs := by
  have hcI : c ∈ ggInduced L Bs := mem_ggAutomizer_iff.mp hc
  refine Subgroup.closure_induction
    (p := fun φ _ => c * φ * c⁻¹ ∈ ggAutNormalClosure L J Bs) ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨c', hc', a, ha, rfl⟩
    exact Subgroup.subset_closure ⟨c * c', mul_mem_ggInduced hcI hc', a, ha, by group⟩
  · simp
  · intro x y _ _ hx hy
    have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have e : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

end NormalClosure

section Fixed

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem ggFixedSubmodule_le_of_normal (hp2 : p ≠ 2) {Bs L : Subgroup G}
    (hNT : GGNoTransvection p Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) (h3 : 3 ≤ Fintype.card Λ) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (hno6 : ∀ i j, M i j ≠ 6) (par : Λ → Λ) (root : Λ) (depth : Λ → ℕ)
    (hpar : ∀ i j, i ≠ j → (C i j ≠ 0 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i)
    (hW : GGWeylOfType p M (ggAutomizer L Bs)) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V)
    (hfixA : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ιV (ggAutomizer L Bs)) ≤ 1)
    {N : Subgroup (MulAut ↥Bs)} (hNA : N ≤ ggAutomizer L Bs)
    (hnorm : ∀ c ∈ ggAutomizer L Bs, ∀ φ ∈ N, c * φ * c⁻¹ ∈ N)
    {a : MulAut ↥Bs} (haN : a ∈ N) (ha : a ≠ 1) :
    ggFixedSubmodule (p := p) ιV N ≤ ggFixedSubmodule (p := p) ιV (ggAutomizer L Bs) := by
  classical
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  set A := ggAutomizer L Bs with hA_def
  have hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs :=
    fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer hφ
  obtain ⟨e, h, α, hα, hrefl, hpair⟩ :=
    SecFiveRootRefl.exists_cartan_pairing_of_weylOfType' (p := p) hp2 hNT hC hno6 par root depth
      hpar hdepth hW hind ιV
  let φ : Λ → MulAut ↥Bs := fun i => ((e (M.simple i) : ↥A) : MulAut ↥Bs)
  have hφA : ∀ i, φ i ∈ A := fun i => (e (M.simple i)).2
  have hφ : ∀ i w, ggLin (p := p) ιV (φ i) w = w - α i w • h i :=
    fun i w => by rw [hrefl i]; exact Module.reflection_apply w (hα i)
  have hAL : A = Subgroup.closure (Set.range φ) := by
    have hmap : ((Subgroup.subtype A).comp e.toMonoidHom) '' Set.range M.simple =
        Set.range φ := by
      ext y
      constructor
      · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨M.simple i, ⟨i, rfl⟩, rfl⟩
    have hfr : ((Subgroup.subtype A).comp e.toMonoidHom).range = A := by
      ext y
      constructor
      · rintro ⟨m, rfl⟩
        exact (e m).2
      · intro hy
        obtain ⟨m, hm⟩ := e.surjective ⟨y, hy⟩
        exact ⟨m, congrArg Subtype.val hm⟩
    have hsimple_eq : (M.toCoxeterSystem).simple = M.simple := by
      funext i
      rw [CoxeterMatrix.toCoxeterSystem_simple]
    have hsimple_range : Set.range M.simple = Set.range (M.toCoxeterSystem).simple := by
      rw [hsimple_eq]
    rw [← hmap, ← MonoidHom.map_closure, hsimple_range,
      (M.toCoxeterSystem).subgroup_closure_range_simple, Subgroup.map_top, hfr]
  have hfix_of : ∀ v : V, (∀ i, ggLin (p := p) ιV (φ i) v = v) →
      v ∈ ggFixedSubmodule (p := p) ιV A := by
    intro v hv
    rw [mem_ggFixedSubmodule_iff]
    intro c hc
    rw [hAL] at hc
    induction hc using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hv i
    | one => simp
    | mul y z _ _ hy hz => rw [map_mul, LinearEquiv.mul_apply, hz, hy]
    | inv y _ hy =>
      rw [map_inv]
      exact (LinearEquiv.symm_apply_eq _).mpr hy.symm
  set U := ggFixedSubmodule (p := p) ιV N with hU_def
  have hUinv : ∀ c ∈ A, ∀ u ∈ U, ggLin (p := p) ιV c u ∈ U := by
    intro c hc u hu
    rw [mem_ggFixedSubmodule_iff] at hu ⊢
    intro ψ hψ
    have hψ' : c⁻¹ * ψ * c ∈ N := by
      have := hnorm c⁻¹ (A.inv_mem hc) ψ hψ
      rwa [inv_inv] at this
    have h1 := hu (c⁻¹ * ψ * c) hψ'
    rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h1
    have h2 := congrArg (ggLin (p := p) ιV c) h1
    rw [show ∀ w, ggLin (p := p) ιV c ((ggLin (p := p) ιV c)⁻¹ w) = w from
      fun w => (ggLin (p := p) ιV c).apply_symm_apply w] at h2
    exact h2
  suffices hclaim : ∀ i, ∀ u ∈ U, ggLin (p := p) ιV (φ i) u = u by
    intro u hu
    exact hfix_of u fun i => hclaim i u hu
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, u₀, hu₀, hmove⟩ := hcon
  have htwo : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hh0 : ∀ k, h k ≠ 0 := fun k => (ne_zero_of_apply_eq_two hp2 (hα k)).1
  have hcoroot : ∀ k (c : ZMod p) (w : V), w ∈ U → c ≠ 0 →
      ggLin (p := p) ιV (φ k) w = w - c • h k → h k ∈ U := by
    intro k c w hw hc hφw
    have hdiff : w - ggLin (p := p) ιV (φ k) w ∈ U := U.sub_mem hw (hUinv _ (hφA k) w hw)
    rw [hφw, sub_sub_cancel] at hdiff
    exact (Submodule.smul_mem_iff U hc).mp hdiff
  have hmemh : ∀ k, h k ∈ U := by
    have hS := ggCartan_closed_eq_univ hp2 hM hC h3 (S := {k | h k ∈ U})
      ⟨i₀, hcoroot i₀ (α i₀ u₀) u₀ hu₀ (fun h0 => hmove (by rw [hφ, h0, zero_smul, sub_zero]))
        (hφ i₀ u₀)⟩
      (fun k hk j hjk => hcoroot j (C j k : ZMod p) (h k) hk hjk (by rw [hφ, hpair]))
    intro k
    have hk : k ∈ {k | h k ∈ U} := hS ▸ Set.mem_univ k
    exact hk
  have haA : a ∈ A := hNA haN
  have hah : ∀ k, ggLin (p := p) ιV a (h k) = h k :=
    fun k => mem_ggFixedSubmodule_iff.mp (hmemh k) a haN
  have hαa : ∀ k v, α k (ggLin (p := p) ιV a v) = α k v := by
    intro k v
    by_contra hne
    set g : Module.Dual (ZMod p) V :=
      α k - (α k).comp (ggLin (p := p) ιV a).toLinearMap with hg_def
    have hgv : g v ≠ 0 := by
      intro h0
      apply hne
      have : α k v - α k (ggLin (p := p) ιV a v) = 0 := h0
      exact (sub_eq_zero.mp this).symm
    have hg0 : g ≠ 0 := fun h0 => hgv (by rw [h0, LinearMap.zero_apply])
    have hgh : g (h k) = 0 := by
      show α k (h k) - α k (ggLin (p := p) ιV a (h k)) = 0
      rw [hah k, sub_self]
    have hT : ∀ w, ggLin (p := p) ιV ((a⁻¹ * φ k * a) * φ k) w = w + g w • h k := by
      intro w
      have hainv : ggLin (p := p) ιV a⁻¹ (h k) = h k := by
        rw [map_inv]
        exact (LinearEquiv.symm_apply_eq _).mpr (hah k).symm
      simp only [map_mul, LinearEquiv.mul_apply, hφ, map_sub, map_smul, hainv, hg_def,
        LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      have hinv : ∀ y, ggLin (p := p) ιV a⁻¹ (ggLin (p := p) ιV a y) = y := by
        intro y
        rw [map_inv]
        exact (ggLin (p := p) ιV a).symm_apply_apply y
      rw [hinv, hinv, hah k]
      simp only [hα k]
      module
    have hTA : (a⁻¹ * φ k * a) * φ k ∈ A :=
      A.mul_mem (A.mul_mem (A.mul_mem (A.inv_mem haA) (hφA k)) haA) (hφA k)
    exact hNT _ (hind _ hTA) (ggIsTransvection_of_apply ιV (hh0 k) hg0 hgh hT)
  set F := ggFixedSubmodule (p := p) ιV A with hF_def
  have hwfix : ∀ v, ggLin (p := p) ιV a v - v ∈ F := by
    intro v
    refine hfix_of _ fun k => ?_
    rw [hφ k, map_sub, hαa k v, sub_self, zero_smul, sub_zero]
  have hafix : ∀ w ∈ F, ggLin (p := p) ιV a w = w :=
    fun w hw => mem_ggFixedSubmodule_iff.mp hw a haA
  set T : V →ₗ[ZMod p] V := LinearMap.id - (ggLin (p := p) ιV a).toLinearMap with hT_def
  have hTv : ∀ v, T v = -(ggLin (p := p) ιV a v - v) := by
    intro v
    simp [hT_def]
  have hTF : LinearMap.range T ≤ F := by
    rintro _ ⟨v, rfl⟩
    rw [hTv]
    exact F.neg_mem (hwfix v)
  have hT0 : T ≠ 0 := by
    intro h0
    apply ha
    apply ggLin_injective (p := p) ιV
    rw [map_one]
    refine LinearEquiv.ext fun v => ?_
    have := congrArg (fun S : V →ₗ[ZMod p] V => S v) h0
    simp only [hT_def, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
      LinearMap.zero_apply, sub_eq_zero] at this
    exact this.symm
  have hr1 : Module.finrank (ZMod p) (LinearMap.range T) = 1 := by
    have hle : Module.finrank (ZMod p) (LinearMap.range T) ≤ 1 :=
      (Submodule.finrank_mono hTF).trans hfixA
    have hpos : 0 < Module.finrank (ZMod p) (LinearMap.range T) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hT0 (LinearMap.ext hall)
      exact ⟨⟨T v, v, rfl⟩, fun h0 => hv (congrArg Subtype.val h0)⟩
    omega
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  refine hNT a (hind a haA) ⟨?_, fun b => ?_⟩
  · have hker : Nat.card {v : V // ggLin (p := p) ιV a v = v} = Nat.card (LinearMap.ker T) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => by
        rw [LinearMap.mem_ker, hT_def, LinearMap.sub_apply, LinearMap.id_apply,
          LinearEquiv.coe_coe, sub_eq_zero, eq_comm])
    rw [card_fixed_ggLin (p := p) ιV a, card_eq_of_ggLin ιV, hker,
      Module.natCard_eq_pow_finrank (K := ZMod p) (V := ↥(LinearMap.ker T)),
      Module.natCard_eq_pow_finrank (K := ZMod p) (V := V), Nat.card_zmod, ← pow_succ]
    congr 1
    omega
  · rw [ggLin_fix_iff (p := p) ιV]
    have hb : ιV (Additive.ofMul (b⁻¹ * a b)) =
        ggLin (p := p) ιV a (ιV (Additive.ofMul b)) - ιV (Additive.ofMul b) := by
      rw [ggLin_apply_ofMul, ofMul_mul, ofMul_inv, map_add, map_neg]
      abel
    rw [hb]
    exact hafix _ (hwfix _)

end Fixed

section Row

theorem ggTableBPos_mem_centralizer_of_fixed
    {p : ℕ} {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) (h3 : 3 ≤ bnRank t n) (hrange : ψ.range = X)
    (hpos : GGTableBPos p Bs X t n f ψ) {b : ↥Bs} (hb : ∀ φ ∈ ggAutomizer X Bs, φ b = b) :
    (b : G) ∈ Subgroup.centralizer (X : Set G) := by
  obtain ⟨ε, -, hεlevi, -⟩ := hpos
  have hdiv : (ggU t n f).D.divisible = ∅ := s2jn_ggU_divisible_eq_empty ht
  have hgen : ggSub (ggU t n f).D (ggU t n f).D.roots = ⊤ :=
    (ggTagFacts_of_admissible hadm h3).2.2.1
  have hle : X ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
    rw [← hrange, MonoidHom.range_eq_map, ← hgen, ggSub]
    simp only [Subgroup.map_iSup]
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨w, i, rfl⟩ := s2jn_exists_weylAction_of_mem_roots (ggU t n f).D hdiv hγ
    have hlevi := hεlevi w i
    simp only [ggRootLevi] at hlevi
    refine le_trans (Subgroup.map_mono (le_sup_left : (ggU t n f).D.rootGroup
      (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)) ≤
      (ggU t n f).D.rootGroup (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)) ⊔
      (ggU t n f).D.rootGroup (-(weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))))) ?_
    rw [← hlevi]
    refine (ggOTwoPrime_le _).trans (inf_le_right.trans (Subgroup.centralizer_le ?_))
    rw [Set.singleton_subset_iff]
    exact ⟨b, hb _ (ε _).2, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

theorem ggR1_finrank_fixed_normalClosure_le_one
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) (h3 : 3 ≤ bnRank t n) (hrange : ψ.range = L)
    (hpos : GGTableBPos p Bs L t n f ψ) (hJ : ∃ a ∈ ggAutomizer J Bs, a ≠ 1)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ιV (ggAutNormalClosure L J Bs)) ≤ 1 := by
  classical
  obtain ⟨hMW, hlab⟩ := ggTag_weylMatrix ht hadm
  obtain ⟨C, hC, par, root, depth, hpar, hdepth⟩ := ggR1Da_exists_cartanTree hMW
  have hno6 : ∀ i j, (coxeterMatrix (ggU t n f).D.isFiniteType) i j ≠ 6 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [CoxeterMatrix.diagonal]
      norm_num
    · have := hlab i j hij
      omega
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hNT : GGNoTransvection p Bs := hHyp.2.2.2.1
  have hpos' := hpos
  obtain ⟨ε, hε, -, -⟩ := hpos'
  have hW : GGWeylOfType p (coxeterMatrix (ggU t n f).D.isFiniteType) (ggAutomizer L Bs) :=
    ⟨ε, hε⟩
  have hrank : (ggU t n f).D.rank = bnRank t n :=
    lieUniversal_rank_eq_bnRank t n 2 f Nat.prime_two hadm h3
  have h3' : 3 ≤ Fintype.card (Fin (ggU t n f).D.rank) := by
    rw [Fintype.card_fin, hrank]
    exact h3
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hcardC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
    rw [inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2,
      Nat.card_zpowers, orderOf_eq_prime (hBs.2 x hxBs) hS.2.2.1]
  have hmem : ∀ v : ↥(ggFixedSubmodule (p := p) ιV (ggAutomizer L Bs)),
      ((Additive.toMul (ιV.symm (v : V)) : ↥Bs) : G) ∈
        Bs ⊓ Subgroup.centralizer (L : Set G) := by
    intro v
    refine ⟨(Additive.toMul (ιV.symm (v : V))).2, ggTableBPos_mem_centralizer_of_fixed ht hadm h3
      hrange hpos fun φ hφ => ?_⟩
    have hv := mem_ggFixedSubmodule_iff.mp v.2 φ hφ
    refine (ggLin_fix_iff (p := p) ιV φ _).mpr ?_
    have hb : ιV (Additive.ofMul (Additive.toMul (ιV.symm (v : V)))) = (v : V) := by simp
    rw [hb]
    exact hv
  have hcard : Nat.card ↥(ggFixedSubmodule (p := p) ιV (ggAutomizer L Bs)) ≤ p := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun v => (⟨_, hmem v⟩ : ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))) ?_) hcardC.le
    intro v₁ v₂ h12
    have h12g : ((Additive.toMul (ιV.symm (v₁ : V)) : ↥Bs) : G) =
        ((Additive.toMul (ιV.symm (v₂ : V)) : ↥Bs) : G) :=
      congrArg (fun s : ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) => (s : G)) h12
    have h12' : Additive.toMul (ιV.symm (v₁ : V)) = Additive.toMul (ιV.symm (v₂ : V)) :=
      Subtype.ext h12g
    exact Subtype.ext (ιV.symm.injective (Additive.toMul.injective h12'))
  have hfixA : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ιV (ggAutomizer L Bs)) ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod] at hcard
    have h1 : p ^ Module.finrank (ZMod p)
        ↥(ggFixedSubmodule (p := p) ιV (ggAutomizer L Bs)) ≤ p ^ 1 := by
      simpa using hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hJLA : ggAutomizer J Bs ≤ ggAutomizer L Bs := ggAutomizer_mono Bs hJL
  obtain ⟨a, haJ, ha1⟩ := hJ
  have haN : a ∈ ggAutNormalClosure L J Bs := by
    have := conj_mem_ggAutNormalClosure (L := L) (Subgroup.one_mem _) haJ
    rwa [one_mul, inv_one, mul_one] at this
  exact (Submodule.finrank_mono (ggFixedSubmodule_le_of_normal hp2 hNT hMW h3' hC hno6 par root
    depth hpar hdepth hW ιV hfixA (ggAutNormalClosure_le_ggAutomizer hJLA)
    (fun c hc φ hφ => conj_mem_ggAutNormalClosure_of_mem hc hφ) haN ha1)).trans hfixA

theorem ggR1_datum_of_tableBPos_of_ne_one
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) (h3 : 3 ≤ bnRank t n) (hrange : ψ.range = L)
    (hpos : GGTableBPos p Bs L t n f ψ) (hJ : ∃ a ∈ ggAutomizer J Bs, a ≠ 1) :
    Nonempty (GGExcReflTBWeylDatum p Bs L J) := by
  classical
  obtain ⟨hMW, hlab⟩ := ggTag_weylMatrix ht hadm
  obtain ⟨C, hC, par, root, depth, hpar, hdepth⟩ := ggR1Da_exists_cartanTree hMW
  have hno6 : ∀ i j, (coxeterMatrix (ggU t n f).D.isFiniteType) i j ≠ 6 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [CoxeterMatrix.diagonal]
      norm_num
    · have := hlab i j hij
      omega
  obtain ⟨-, hBs, -, -, -⟩ := hHyp.1.tableB_facts
  have hNT : GGNoTransvection p Bs := hHyp.2.2.2.1
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  have hpos' := hpos
  obtain ⟨ε, hε, -, -⟩ := hpos'
  have hW : GGWeylOfType p (coxeterMatrix (ggU t n f).D.isFiniteType) (ggAutomizer L Bs) :=
    ⟨ε, hε⟩
  have hrank : (ggU t n f).D.rank = bnRank t n :=
    lieUniversal_rank_eq_bnRank t n 2 f Nat.prime_two hadm h3
  have h3' : 3 ≤ Fintype.card (Fin (ggU t n f).D.rank) := by
    rw [Fintype.card_fin, hrank]
    exact h3
  exact ggExcReflTBWeylDatum_of_weylOfType hp2 hNT hMW h3' hC hno6 par root depth hpar hdepth hW
    ιV (Or.inr (ggR1_finrank_fixed_normalClosure_le_one hp2 hHyp ht hadm h3 hrange hpos hJ ιV))

theorem ggTBDatumRowTarget_of_noncomm
    {R : ℕ → LargeEvenLabel → Prop}
    (htag : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
      {L D J : Subgroup G}, GGCorFiveTwentyHyp p B Bs x L D J →
      GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ R p lab) p Bs L →
      ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        (t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) ∧
        StatedLieAdmissible t n 2 f ∧ ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = L ∧
        p ∣ 2 ^ f - 1)
    (hnc : GGTBJNoncommRowTarget R) : GGTBDatumRowTarget R := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL _
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  obtain ⟨t, n, f, ψ, ht, hadm, hker, hrange, hpf⟩ := htag hHyp hL
  obtain ⟨h3, ψ', -, hrange', hpos⟩ := ggR1_kgPos_of_witness hHyp hadm hker hrange ht hpf
  obtain ⟨a, ha, b, -, -, -, hab⟩ := hnc G p B Bs x L D J hHyp hq hN hL
  have hJ : ∃ a ∈ ggAutomizer J Bs, a ≠ 1 :=
    ⟨a, ha, fun h => hab (by rw [h, one_mul, mul_one])⟩
  exact ggR1_datum_of_tableBPos_of_ne_one hp2 hHyp ht hadm h3 hrange' hpos hJ

end Row

end CFSG.StandardType

end
