module

public import CFSG.Quasithin.Background.C48SporHyp
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_centralizer_of_perfect' {K L : Subgroup G} (hLK : L ≤ K) (hperf : ⁅L, L⁆ = L)
    {x : G} (hx1 : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Subgroup.centralizer (K : Set G))
    (hx2 : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ K) : x ∈ Subgroup.centralizer (L : Set G) := by
  let f : ↥L →* G :=
    { toFun := fun l => x * l * x⁻¹ * (l : G)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have hb := Subgroup.mem_centralizer_iff.mp (hx1 b b.2) (a : G)⁻¹ (K.inv_mem (hLK a.2))
        simp only [Subgroup.coe_mul]
        calc x * (a * b) * x⁻¹ * ((a : G) * b)⁻¹
            = x * a * x⁻¹ * ((x * b * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
          _ = x * a * x⁻¹ * ((a : G)⁻¹ * (x * b * x⁻¹ * (b : G)⁻¹)) := by rw [hb]
          _ = x * a * x⁻¹ * (a : G)⁻¹ * (x * b * x⁻¹ * (b : G)⁻¹) := by group }
  have hker : ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    change (x * a * x⁻¹ * (a : G)⁻¹) * (x * b * x⁻¹ * (b : G)⁻¹) =
      (x * b * x⁻¹ * (b : G)⁻¹) * (x * a * x⁻¹ * (a : G)⁻¹)
    exact (Subgroup.mem_centralizer_iff.mp (hx1 a a.2) _ (hx2 b b.2)).symm
  have htop : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = (⊤ : Subgroup ↥L) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperf]
  rw [htop, top_le_iff] at hker
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 : f ⟨l, hl⟩ = 1 := by
    have : (⟨l, hl⟩ : ↥L) ∈ f.ker := by rw [hker]; trivial
    exact this
  have h2 : x * l * x⁻¹ * l⁻¹ = 1 := h1
  calc l * x = (x * l * x⁻¹ * l⁻¹)⁻¹ * (x * l) := by group
    _ = x * l := by rw [h2, inv_one, one_mul]

theorem eq_zero_of_forall_mulVec_eq {m : ℕ} {F : Type} [Field F] (hm : 2 ≤ m)
    {w : Fin m → F}
    (hw : ∀ g : ↥(StatedSL m F),
      ((g : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F).mulVec w = w) :
    w = 0 := by
  funext j
  obtain ⟨i, hij⟩ : ∃ i : Fin m, i ≠ j := by
    by_cases hj : (j : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => hj (by simp [Fin.ext_iff] at h; omega)⟩
  let t : Matrix.SpecialLinearGroup (Fin m) F :=
    ⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne _ _ hij 1⟩
  have h1 := hw (specialLinearGroupEquivStatedSL m F t)
  rw [specialLinearGroupEquivStatedSL_coe] at h1
  have h2 := congrFun h1 i
  simp only [t, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply] at h2
  have h3 : (Matrix.single i j (1 : F)).mulVec w i = w j := by
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  rw [h3] at h2
  simpa using h2

theorem inf_centralizer_eq_bot_of_sum {L R V : Subgroup G} {m k : ℕ} (hm : 2 ≤ m)
    (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hs : IsSumOfNaturalModules (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R)) (StatedSL m (ZMod 2))
      false k) : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨α, hα, hαk, -, -, β, hβ, hβk, heq⟩ := hs
  rw [eq_bot_iff]
  rintro v ⟨hvV, hvL⟩
  have hfix : ∀ i : Fin k, Multiplicative.toAdd (β ⟨v, hvV⟩) i = 0 := by
    intro i
    refine eq_zero_of_forall_mulVec_eq hm fun g => ?_
    obtain ⟨y, rfl⟩ := hα g
    obtain ⟨l, hl, r, hr, hlr⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hRL).1 y.2
    have hy : y = ⟨l, Subgroup.mem_sup_left hl⟩ * ⟨r, Subgroup.mem_sup_right hr⟩ :=
      Subtype.ext hlr
    have hαr : α ⟨r, Subgroup.mem_sup_right hr⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]
      exact hr
    have hcomm : (v : G) = l * v * l⁻¹ := by
      rw [Subgroup.mem_centralizer_iff.mp hvL l hl]
      group
    have := heq ⟨l, Subgroup.mem_sup_left hl⟩ ⟨v, hvV⟩ ⟨v, hvV⟩ hcomm i
    rw [hy, map_mul, hαr, mul_one]
    exact this.symm
  have hβv : β ⟨v, hvV⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [hfix i]
    rfl
  have : (⟨v, hvV⟩ : ↥V) ∈ β.ker := hβv
  rw [hβk, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact this

section Hyp

variable [Finite G] {H R M L V K : Subgroup G}

theorem mem_R_of_centralizer (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) {y : G}
    (hy : y ∈ conjClosure L M ⊔ R) (hyC : y ∈ Subgroup.centralizer (K : Set G)) : y ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := Subgroup.centralizer (K : Set G) ⊓ (conjClosure L M ⊔ R) with hP
  have hRN : R ≤ Subgroup.normalizer (conjClosure L M : Set G) :=
    h.le_M.trans (le_normalizer_conjClosure L M)
  have hPp : IsPGroup 2 ↥P := by
    rintro ⟨p, hpC, hpY⟩
    obtain ⟨e, he⟩ := InternalSec.two_of_sup h.pgroup hRN p hpY
    have hz : p ^ 2 ^ e ∈ centerOf K := ⟨h31.1 he, Subgroup.pow_mem _ hpC _⟩
    obtain ⟨f, hf⟩ := h31.2.2 ⟨_, hz⟩
    refine ⟨e + f, Subtype.ext ?_⟩
    rw [pow_add, pow_mul]
    simpa using congrArg Subtype.val hf
  have hRP : R ≤ Subgroup.normalizer (P : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro p
    have hrK : r ∈ Subgroup.normalizer (K : Set G) := h31.2.1 (h.le_M hr)
    have hrY : r ∈ Subgroup.normalizer ((conjClosure L M ⊔ R : Subgroup G) : Set G) := by
      have h1 : r ∈ conjClosure L M ⊔ R := Subgroup.mem_sup_right hr
      exact Subgroup.le_normalizer h1
    constructor
    · rintro ⟨hp1, hp2⟩
      exact ⟨conj_mem_centralizer hrK hp1, (Subgroup.mem_normalizer_iff.mp hrY p).mp hp2⟩
    · rintro ⟨hp1, hp2⟩
      have h1 := conj_mem_centralizer (Subgroup.inv_mem _ hrK) hp1
      have e : r⁻¹ * (r * p * r⁻¹) * r⁻¹⁻¹ = p := by group
      rw [e] at h1
      exact ⟨h1, (Subgroup.mem_normalizer_iff.mp hrY p).mpr hp2⟩
  have hPR : IsPGroup 2 ↥(P ⊔ R) := IsPGroup.to_sup_of_normal_left' hPp h.pgroup hRP
  have hPC0 : P ≤ centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)) :=
    fun p hp => centralizer_le_centralizerSection h h31
      ⟨hp.1, M0R_le_sporX h h31 hp.2⟩
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp h.sylow).2.2
  have := hmax _ (sup_le hPC0 h.sylow.1) hPR le_sup_right
  exact this (Subgroup.mem_sup_left ⟨hyC, hy⟩)

theorem comap_imgHom_R (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    ((img (sporN H K) R).subgroupOf (img (sporN H K) (conjClosure L M ⊔ R))).comap
      (imgHom (M0R_le_sporX h h31)) = R.subgroupOf (conjClosure L M ⊔ R) := by
  ext y
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, coe_imgHom]
  constructor
  · intro hy
    obtain ⟨r, hr, hry⟩ := mem_img.1 hy
    have hc := QuotientGroup.eq.mp hry
    rw [mem_sporN] at hc
    have hc' : (r : G)⁻¹ * y ∈ Subgroup.centralizer (K : Set G) := by simpa using hc
    have hrY : (r : G) ∈ conjClosure L M ⊔ R := Subgroup.mem_sup_right hr
    have h1 := mem_R_of_centralizer h h31
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hrY) y.2) hc'
    have := R.mul_mem hr h1
    simpa using this
  · intro hy
    exact mk_mem_img hy

theorem mk_mem_centralizer_iff (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    {v : ↥(sporX H K)} (hvK : (v : G) ∈ K) :
    (v : ↥(sporX H K) ⧸ sporN H K) ∈
        Subgroup.centralizer (img (sporN H K) (conjClosure L M) : Set (↥(sporX H K) ⧸ sporN H K)) ↔
      (v : G) ∈ Subgroup.centralizer (conjClosure L M : Set G) := by
  constructor
  · intro hc
    refine mem_centralizer_of_perfect' h31.1 (C2Nine.perfect_conjClosure_of_hyp h)
      (fun m hm => ?_) (fun m hm => K.mul_mem (K.mul_mem (K.mul_mem hvK (h31.1 hm))
        (K.inv_mem hvK)) (K.inv_mem (h31.1 hm)))
    have hmX := M0_le_sporX h h31 hm
    have h1 := Subgroup.mem_centralizer_iff.mp hc _
      (mk_mem_img (N := sporN H K) (x := ⟨m, hmX⟩) hm)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_sporN] at h1
    have h2 : (v : G)⁻¹ * m⁻¹ * v * m ∈ Subgroup.centralizer (K : Set G) := by
      simpa [mul_assoc] using h1
    have hmv : m * (v : G) ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.le_normalizer (h31.1 hm))
        (Subgroup.le_normalizer hvK)
    have := conj_mem_centralizer hmv h2
    have heq : m * (v : G) * ((v : G)⁻¹ * m⁻¹ * v * m) * (m * v)⁻¹ = v * m * (v : G)⁻¹ * m⁻¹ := by
      group
    rwa [heq] at this
  · intro hc
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨m, hm, rfl⟩ := mem_img.1 hb
    have h1 := Subgroup.mem_centralizer_iff.mp hc m hm
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext h1

end Hyp

end CFSG.Quasithin.C48Spor
