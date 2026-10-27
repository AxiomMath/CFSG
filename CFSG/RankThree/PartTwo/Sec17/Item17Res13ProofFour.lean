module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res12ProofNine
public import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
import CFSG.RankThree.PartTwo.Source.OrderThreeMinimalTwoGroup
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.LocalAnalysis.SignalizerFunctor.HyperplaneGeneration

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res13

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec3
open scoped IsMulCommutative commutatorElement

theorem eq_one_of_class_two {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) (hexp : ∀ x : P, x ^ p = 1)
    (hclass : commutator P ≤ Subgroup.center P) (hrank : CFSG.pRank p P ≤ 2)
    {σ₁ σ₂ τ : MulAut P} (h11 : σ₁ * σ₁ = 1) (h22 : σ₂ * σ₂ = 1) (h12 : σ₁ * σ₂ = σ₂ * σ₁)
    (hτ₁ : σ₁ * τ = τ * σ₂) (hτ₂ : σ₂ * τ = τ * (σ₁ * σ₂)) : σ₁ = 1 := by
  classical
  by_contra hσ
  have hp' : p.Prime := hp.out
  obtain ⟨hchar, hVcomm, hVexp, hVelem, d, hVcard, -⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient hP
  have : Finite (Additive (P ⧸ frattini P)) := inferInstanceAs (Finite (P ⧸ frattini P))
  have : FiniteDimensional (ZMod p) (Additive (P ⧸ frattini P)) := Module.Finite.of_finite
  let Elin : MulAut (P ⧸ frattini P) →* Module.End (ZMod p) (Additive (P ⧸ frattini P)) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap p
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hE : ∀ (σ : MulAut (P ⧸ frattini P)) (q : P ⧸ frattini P),
      Elin σ (Additive.ofMul q) = Additive.ofMul (σ q) := fun _ _ => rfl
  let q := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini P)
  have hq : ∀ (σ : MulAut P) (x : P), q σ (x : P ⧸ frattini P) = ((σ x : P) : P ⧸ frattini P) :=
    fun σ x => CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply _ σ x
  let ρW : MulAut P →* Module.End (ZMod p) (Additive (P ⧸ frattini P)) := Elin.comp q
  have hρW : ∀ (σ : MulAut P) (x : P), ρW σ (Additive.ofMul (x : P ⧸ frattini P)) =
      Additive.ofMul ((σ x : P) : P ⧸ frattini P) := fun σ x => by
    change Elin (q σ) _ = _
    rw [hE, hq]
  have hinv : ∀ σ (v : Additive (P ⧸ frattini P)), ρW σ⁻¹ (ρW σ v) = v := fun σ v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinj : ∀ σ, Function.Injective (ρW σ) := fun σ x y h => by
    rw [← hinv σ x, h, hinv σ y]
  have hσ₁ : ρW σ₁ ≠ 1 := by
    intro h1
    have hord : orderOf σ₁ = 2 := orderOf_eq_prime (by rw [pow_two, h11]) hσ
    apply hσ
    refine CFSG.OrderReductions.FrattiniAutomorphisms.prime_order_frattini_kernel_trivial 2
      σ₁ hord (not_two_dvd_card_of_odd hp2 hP) ?_
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro x
    have h := congrArg (fun f : Module.End (ZMod p) (Additive (P ⧸ frattini P)) =>
      f (Additive.ofMul (x : P ⧸ frattini P))) h1
    simp only [hρW, Module.End.one_apply] at h
    exact congrArg Additive.toMul h
  have hrank1 : CFSG.pRank p (fixedSubgroupOf (1 : MulAut P)) ≤ 2 := by
    refine le_trans ?_ hrank
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_top_le_of_injective hp'.one_lt
      (fixedSubgroupOf (1 : MulAut P)).subtype (fixedSubgroupOf (1 : MulAut P)).subtype_injective
  have h2 := finrank_eigenspace_le_two_of_pRank_le_two hp2 hP hexp hclass
    (σ := 1) (one_pow 2) hrank1 (ρW 1) (hρW 1)
  have htop : (ρW 1).eigenspace (1 : ZMod p) = ⊤ := by
    ext v
    simp only [Module.End.mem_eigenspace_iff, map_one, Module.End.one_apply, one_smul,
      Submodule.mem_top]
  rw [htop, finrank_top] at h2
  have h3 := three_le_finrank_eigenspace (σ₁ := ρW σ₁) (σ₂ := ρW σ₂) (τ := ρW τ)
    (β₁ := ρW 1) (β₂ := ρW 1) (ζ := ρW 1) (two_ne_zero_zmod hp' hp2)
    (by rw [← map_mul ρW, h11, map_one]) (by rw [← map_mul ρW, h22, map_one])
    (by rw [← map_mul ρW, ← map_mul ρW, h12]) (by rw [← map_mul ρW, ← map_mul ρW, hτ₁])
    (by rw [← map_mul ρW, ← map_mul ρW, ← map_mul ρW, hτ₂]) (hinj τ)
    (by rw [map_one, one_mul, mul_one]) (by rw [map_one, one_mul, mul_one])
    (by rw [map_one, one_mul, mul_one]) (by rw [map_one, one_mul, mul_one]) (hinj 1) (hinj 1)
    (by rw [map_one, one_mul, one_mul]) hσ₁ (by omega)
  rw [htop, finrank_top] at h3
  omega

section Group

variable {G : Type*} [Group G] [Finite G]

theorem le_centralizer_of_mem_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3)
    {P Z : Subgroup G} (hP : IsPGroup p P) (hZ4 : Nat.card Z = 4) (hZ2 : ∀ u ∈ Z, u ^ 2 = 1)
    (hZc : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u) (hZP : Z ≤ Subgroup.normalizer (P : Set G))
    {w : G} (hwP : w ∈ Subgroup.normalizer (P : Set G))
    (hwZ : w ∈ Subgroup.normalizer (Z : Set G)) (hw3 : w ^ 3 = 1) {d : G} (hd : d ∈ Z)
    (hwd : w * d * w⁻¹ ≠ d) {z : G} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hzP : z ∈ Subgroup.centralizer (P : Set G)) :
    Z ≤ Subgroup.centralizer (P : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hZC
  have hfix : ∀ u ∈ Z, w * u * w⁻¹ = u → u = 1 := fun u hu hwu =>
    Proof17Res12.eq_one_of_conj_eq hZ4 hZ2 hwZ hw3 hd hwd hu hwu
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hwd (by group)
  have hdC : d ∉ Subgroup.centralizer (P : Set G) := by
    intro hxC
    apply hZC
    have hwx : w * d * w⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hwZ d).mp hd
    have hwxC : w * d * w⁻¹ ∈ Subgroup.centralizer (P : Set G) :=
      Proof17Res12.conj_mem_centralizer hwP hxC
    have hwx1 : w * d * w⁻¹ ≠ 1 := fun h => hd1 (by
      calc d = w⁻¹ * (w * d * w⁻¹) * w := by group
        _ = 1 := by rw [h]; group)
    have hwxx : d ≠ w * d * w⁻¹ := fun h => hd1 (hfix d hd h.symm)
    intro u hu
    rcases Proof17Res12.eq_of_mem_four hZ4 hZ2 hd hwx hd1 hwx1 hwxx hu with h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact hxC
    · rw [h]; exact hwxC
    · rw [h]; exact Subgroup.mul_mem _ hxC hwxC
  have hw3' : w * w * w = 1 := by rw [← pow_three', hw3]
  set d₂ := w⁻¹ * d * w with hd₂
  have hd₂Z : d₂ ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hwZ) d).mp hd
    simpa [hd₂] using this
  have hd₂1 : d₂ ≠ 1 := fun h => hd1 (by
    calc d = w * d₂ * w⁻¹ := by rw [hd₂]; group
      _ = 1 := by rw [h]; group)
  have hdd₂ : d ≠ d₂ := fun h => hwd (by
    calc w * d * w⁻¹ = w * d₂ * w⁻¹ := by rw [← h]
      _ = d := by rw [hd₂]; group)
  have hd₃ : w⁻¹ * d₂ * w = d * d₂ := by
    have hd₃Z : w⁻¹ * d₂ * w ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hwZ) d₂).mp hd₂Z
      simpa using this
    rcases Proof17Res12.eq_of_mem_four hZ4 hZ2 hd hd₂Z hd1 hd₂1 hdd₂ hd₃Z with h | h | h | h
    · exact absurd (by
        calc d₂ = w * (w⁻¹ * d₂ * w) * w⁻¹ := by group
          _ = 1 := by rw [h]; group) hd₂1
    · exfalso
      apply hwd
      calc w * d * w⁻¹ = w * (w⁻¹ * d₂ * w) * w⁻¹ := by rw [h]
        _ = d₂ := by group
        _ = w⁻¹ * (w⁻¹ * d₂ * w) * w := by rw [h]
        _ = w⁻¹ * (w⁻¹ * (w⁻¹ * d * w) * w) * w := by rw [hd₂]
        _ = (w * w * w)⁻¹ * d * (w * w * w) := by group
        _ = d := by rw [hw3']; group
    · exfalso
      apply hd₂1
      refine hfix d₂ hd₂Z ?_
      calc w * d₂ * w⁻¹ = w * (w⁻¹ * d₂ * w) * w⁻¹ := by rw [h]
        _ = d₂ := by group
    · exact h
  set cn := P.normalizerMonoidHom with hcn
  have hcnapp : ∀ (x : Subgroup.normalizer (P : Set G)) (y : P),
      ((cn x y : P) : G) = (x : G) * y * (x : G)⁻¹ := fun x y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  set nd : Subgroup.normalizer (P : Set G) := ⟨d, hZP hd⟩ with hnd
  set nd₂ : Subgroup.normalizer (P : Set G) := ⟨d₂, hZP hd₂Z⟩ with hnd₂
  set nw : Subgroup.normalizer (P : Set G) := ⟨w, hwP⟩ with hnw
  have hmap : ∀ {x₁ x₂ x₃ x₄ : Subgroup.normalizer (P : Set G)},
      (x₁ : G) * x₂ = x₃ * x₄ → cn x₁ * cn x₂ = cn x₃ * cn x₄ := fun {x₁ x₂ x₃ x₄} h => by
    have he : x₁ * x₂ = x₃ * x₄ := Subtype.ext (by simpa only [Subgroup.coe_mul] using h)
    rw [← map_mul cn, ← map_mul cn, he]
  have hsq : ∀ {x : Subgroup.normalizer (P : Set G)}, (x : G) * x = 1 → cn x * cn x = 1 :=
    fun {x} h => by
      have he : x * x = 1 :=
        Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h)
      rw [← map_mul cn, he, map_one]
  have e11 : cn nd * cn nd = 1 := hsq (by rw [← pow_two]; exact hZ2 d hd)
  have e22 : cn nd₂ * cn nd₂ = 1 := hsq (by rw [← pow_two]; exact hZ2 d₂ hd₂Z)
  have e12 : cn nd * cn nd₂ = cn nd₂ * cn nd := hmap (hZc d hd d₂ hd₂Z)
  have eτ₁ : cn nd * cn nw = cn nw * cn nd₂ := hmap (by
    change d * w = w * (w⁻¹ * d * w)
    group)
  have eτ₂ : cn nd₂ * cn nw = cn nw * (cn nd * cn nd₂) := by
    rw [← map_mul cn nd nd₂]
    refine hmap ?_
    change d₂ * w = w * (d * d₂)
    rw [← hd₃]
    group
  have hσ₁ : cn nd ≠ 1 := by
    intro h1
    apply hdC
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have h := congrArg (fun σ : MulAut P => ((σ ⟨y, hy⟩ : P) : G)) h1
    simp only [hcnapp, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hnt : Nontrivial P := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hσ₁
    exact MulEquiv.ext fun x => Subsingleton.elim _ _
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hP
  set r := restrictCharacteristic D with hr
  have hrσ : r (cn nd) ≠ 1 := by
    intro hg
    have hfixg : cn nd ∈ fixingSubgroup (MulAut P) (D : Set P) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      have h := congrArg (fun σ : MulAut D => ((σ ⟨y, hy⟩ : D) : P)) hg
      exact h
    obtain ⟨k, hk⟩ := hDfix ⟨cn nd, hfixg⟩
    have hk' : (cn nd) ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have h1 : orderOf (cn nd) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf (cn nd) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, e11])
    have hcop : Nat.Coprime (p ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    exact hσ₁ (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2))
  have hrankD : CFSG.pRank p D ≤ 2 := by
    let f : D →* G := P.subtype.comp D.subtype
    have hf : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext h)
    have hfmap : (⊤ : Subgroup D).map f ≤ P ⊓ Subgroup.centralizer ({z} : Set G) := by
      rintro _ ⟨y, -, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨((y : P)).2, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hzP _ ((y : P)).2)⟩
    have hle : CFSG.Open.pRank p (⊤ : Subgroup D) ≤
        CFSG.Open.pRank p (P ⊓ Subgroup.centralizer ({z} : Set G)) :=
      (CFSG.SectionRank.pRank_le_map hp.one_lt f hf ⊤).trans
        (CFSG.SectionRank.pRank_mono hp.one_lt hfmap)
    obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
      (P ⊓ Subgroup.centralizer ({z} : Set G))
    have hloc' := le_localRank_of_commute_involution hp.one_lt hz1 hz2 hE.1 hE.2
      (hEH.trans inf_le_right) hcard
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    omega
  have hDp : IsPGroup p D := hP.to_subgroup D
  have hDexp' : ∀ x : D, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hDclass : commutator D ≤ Subgroup.center D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    have hxy : ⁅(x : P), (y : P)⁆ ∈ D ⊓ Subgroup.centralizer (D : Set P) :=
      hDcomm (Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _))
    have hcoe : ((⁅x, y⁆ : D) : P) = ⁅(x : P), (y : P)⁆ := by simp [commutatorElement_def]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]
    exact Subgroup.mem_centralizer_iff.mp hxy.2 u u.2
  refine hrσ (eq_one_of_class_two hp2 hDp hDexp' hDclass hrankD (σ₂ := r (cn nd₂))
    (τ := r (cn nw)) ?_ ?_ ?_ ?_ ?_)
  · rw [← map_mul r, e11, map_one]
  · rw [← map_mul r, e22, map_one]
  · rw [← map_mul r, ← map_mul r, e12]
  · rw [← map_mul r, ← map_mul r, eτ₁]
  · rw [← map_mul r, ← map_mul r, ← map_mul r, eτ₂]

theorem le_centralizer_of_elems {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3)
    {P Z : Subgroup G} (hP : IsPGroup p P) (hZ4 : Nat.card Z = 4) (hZ2 : ∀ u ∈ Z, u ^ 2 = 1)
    (hZc : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u) (hZP : Z ≤ Subgroup.normalizer (P : Set G))
    {w z b₁ b₂ : G} (hwP : w ∈ Subgroup.normalizer (P : Set G))
    (hzP : z ∈ Subgroup.normalizer (P : Set G)) (hb₁P : b₁ ∈ Subgroup.normalizer (P : Set G))
    (hb₂P : b₂ ∈ Subgroup.normalizer (P : Set G)) (hwZ : w ∈ Subgroup.normalizer (Z : Set G))
    (hw3 : w ^ 3 = 1) {d : G} (hd : d ∈ Z) (hwd : w * d * w⁻¹ ≠ d) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hzZ : ∀ u ∈ Z, z * u = u * z) (hwz : w * z = z * w)
    (hb₁Z : ∀ u ∈ Z, b₁ * u = u * b₁) (hb₂Z : ∀ u ∈ Z, b₂ * u = u * b₂)
    (hb : b₁ * b₂ = z * b₂ * b₁) :
    Z ≤ Subgroup.centralizer (P : Set G) := by
  rcases Proof17Res12.le_centralizer_or_mem_centralizer hp hp3 hloc hP hZ4 hZ2 hZc hZP hwP hzP
      hb₁P hb₂P hwZ hw3 hd hwd hz2 hz1 hzZ hwz hb₁Z hb₂Z hb with hZC | hzC
  · exact hZC
  · exact le_centralizer_of_mem_centralizer hp (by omega) hloc hP hZ4 hZ2 hZc hZP hwP hwZ hw3 hd
      hwd hz2 hz1 hzC

theorem exists_commutatorPiece_not_mem {X T : Subgroup G}
    (hX : CFSG.Assembly.IsElemAbelian 3 X) (hT : IsPGroup 2 T)
    (hXT : X ≤ Subgroup.normalizer (T : Set G)) {x : G} (hxX : x ∈ X)
    (hxT : ¬ T ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ S, Source.IsCommutatorPiece X T S ∧ x ∉ Subgroup.centralizer (S : Set G) := by
  have hX3 : IsPGroup 3 X := fun g => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, hX.2 g g.2, Subgroup.coe_one])⟩
  have hXne : X ≠ ⊥ := by
    intro h
    apply hxT
    rw [h, Subgroup.mem_bot] at hxX
    subst hxX
    intro t _
    rw [Subgroup.mem_centralizer_singleton_iff, one_mul, mul_one]
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_hyperplane_generation 3
    Nat.prime_three X T hX hXne hXT hcop
  obtain ⟨Y, hYX, hY3, hxW⟩ : ∃ Y : Subgroup G, Y ≤ X ∧ (Y.subgroupOf X).index = 3 ∧
      ¬ T ⊓ Subgroup.centralizer (Y : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hxT
    rw [← hgen]
    exact iSup_le fun Y => iSup_le fun hYX => iSup_le fun hY3 => hcon Y hYX hY3
  set W := T ⊓ Subgroup.centralizer (Y : Set G) with hW_def
  have hXY : X ≤ Subgroup.centralizer (Y : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hX.1.is_comm.comm ⟨y, hYX hy⟩ ⟨g, hg⟩)
  have hXW : X ≤ Subgroup.normalizer (W : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hXT hg,
      Source.mem_normalizer_centralizer (Subgroup.centralizer_le_normalizer _ (hXY hg))⟩
  have hW2 : IsPGroup 2 W := hT.to_le inf_le_left
  set U := ⁅W, X⁆ with hU_def
  have hUW : U ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hXW
  have hUX : ⁅U, X⁆ = U :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three X W
      hX3 (Source.not_three_dvd_card_of_isPGroup_two hW2) hXW
  have hUbot : U ≠ ⊥ := by
    intro h
    apply hxW
    rw [hU_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (h ht) x hxX).symm
  obtain ⟨S, ⟨hSU, hSX, hSbot⟩, hSmin⟩ := Source.exists_minimal_subgroup
    (fun S' => S' ≤ U ∧ ⁅S', X⁆ = S' ∧ S' ≠ ⊥) ⟨le_rfl, hUX, hUbot⟩
  have hSW : S ≤ W := hSU.trans hUW
  have hYS : Y ≤ X ⊓ Subgroup.centralizer (S : Set G) :=
    le_inf hYX (Subgroup.le_centralizer_iff.mp (hSW.trans inf_le_right))
  have hYcard : Nat.card Y * 3 = Nat.card X := by
    have h := Subgroup.relIndex_mul_card (H := Y) (K := X)
    rw [inf_of_le_left hYX] at h
    rw [← h, Subgroup.relIndex, hY3, mul_comm]
  have hSne : X ⊓ Subgroup.centralizer (S : Set G) ≠ X := by
    intro h
    apply hSbot
    rw [← hSX, Subgroup.commutator_eq_bot_iff_le_centralizer]
    have hXc : X ≤ Subgroup.centralizer (S : Set G) := by
      rw [← h]
      exact inf_le_right
    exact Subgroup.le_centralizer_iff.mp hXc
  have hYeq := Source.eq_of_le_of_le_of_card_mul_three hYS inf_le_left hSne hYcard
  refine ⟨S, ⟨hSW.trans inf_le_left, hSX, hSbot, ?_, ?_⟩, ?_⟩
  · intro S' hS'S hS'X hS'bot
    exact hSmin S' hS'S ⟨hS'S.trans hSU, hS'X, hS'bot⟩
  · rw [← hYeq]
    exact hYcard
  · intro hxS
    have hxY : x ∈ Y := by
      rw [hYeq]
      exact ⟨hxX, hxS⟩
    apply hxW
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp ht.2 x hxY).symm

theorem commutator_zpowers_eq_of_piece {X T S : Subgroup G}
    (hX : CFSG.Assembly.IsElemAbelian 3 X) (hT : IsPGroup 2 T)
    (hS : Source.IsCommutatorPiece X T S) {x : G} (hxX : x ∈ X)
    (hxS : x ∉ Subgroup.centralizer (S : Set G)) : ⁅S, Subgroup.zpowers x⁆ = S := by
  obtain ⟨hST, hSX, hSbot, hmin, -⟩ := hS
  have hXS : X ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hSX.le
  have hZX : Subgroup.zpowers x ≤ X := Subgroup.zpowers_le.mpr hxX
  have hZ3 : IsPGroup 3 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime (hX.2 x hxX) ?_
    rintro rfl
    apply hxS
    rw [Subgroup.mem_centralizer_iff]
    intro s _
    rw [one_mul, mul_one]
  have hZS : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set G) := hZX.trans hXS
  have hS3 : ¬ 3 ∣ Nat.card S := Source.not_three_dvd_card_of_isPGroup_two (hT.to_le hST)
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
    Nat.prime_three (Subgroup.zpowers x) S hZ3 hS3 hZS
  have hle : ⁅S, Subgroup.zpowers x⁆ ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hZS
  have hXC : X ≤ Subgroup.normalizer ((⁅S, Subgroup.zpowers x⁆ : Subgroup G) : Set G) := by
    intro g hg
    refine Source.mem_normalizer_commutator (hXS hg) ?_
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hX.1.is_comm.comm ⟨g, hg⟩ ⟨x, hxX⟩)
  refine hmin _ hle (le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hXC) ?_) ?_
  · calc ⁅S, Subgroup.zpowers x⁆ = ⁅⁅S, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ := hidem.symm
      _ ≤ ⁅⁅S, Subgroup.zpowers x⁆, X⁆ := Subgroup.commutator_mono le_rfl hZX
  · intro hbot
    apply hxS
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure] at hbot
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hbot hs))

end Group

end CFSG.RankThree.PartTwo.Sec17.Proof17Res13
