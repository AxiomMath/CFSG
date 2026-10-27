module

public import CFSG.Quasithin.Background.C48Supp
public import CFSG.Quasithin.Background.C48AsmSteps
public import CFSG.Quasithin.Background.B69SL2
public import CFSG.Quasithin.Background.C126RFCases
public import CFSG.Quasithin.Background.C48SumBound
public import CFSG.Quasithin.Background.C48AsmLine
import CFSG.Open.StatedZModTwo
public import CFSG.Quasithin.Background.C2Thirteen

public section

namespace CFSG.Quasithin.C48

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Transfer

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {L R : Subgroup G} (hLR : L ≤ Subgroup.normalizer (R : Set G))
    {x : G} (hx : x ∈ L ⊔ R) : ∃ l ∈ L, ∃ r ∈ R, l * r = x := by
  have hx' : x ∈ (↑(L ⊔ R) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L R hLR] at hx'
  obtain ⟨l, hl, r, hr, hlr⟩ := hx'
  exact ⟨l, hl, r, hr, hlr⟩

theorem exists_hom_sup {Γ : Type*} [Group Γ] {L R : Subgroup G} (α₀ : ↥L →* Γ)
    (hα₀ : Function.Surjective α₀) (hLR : L ≤ Subgroup.normalizer (R : Set G))
    (hker : α₀.ker = R.subgroupOf L) :
    ∃ α : ↥(L ⊔ R) →* Γ, Function.Surjective α ∧ α.ker = R.subgroupOf (L ⊔ R) ∧
      ∀ l : ↥L, α (Subgroup.inclusion le_sup_left l) = α₀ l := by
  set X := L ⊔ R with hX
  set N := R.subgroupOf X with hN
  have hXR : X ≤ Subgroup.normalizer (R : Set G) :=
    sup_le hLR (Subgroup.le_normalizer)
  have hNn : N.Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hXR x.2) n).mp hn
    simpa using this
  set φ : ↥L →* ↥X ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion le_sup_left) with hφ
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨l, hl, r, hr, rfl⟩ := exists_mul_of_mem_sup hLR hx
    refine ⟨⟨l, hl⟩, ?_⟩
    simp only [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    show ((Subgroup.inclusion le_sup_left ⟨l, hl⟩)⁻¹ * ⟨l * r, hx⟩ : ↥X) ∈ N
    rw [hN, Subgroup.mem_subgroupOf]
    simpa using hr
  have hφk : φ.ker = α₀.ker := by
    rw [hker]
    ext l
    simp only [hφ, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    rfl
  let e : ↥L ⧸ φ.ker ≃* ↥X ⧸ N := QuotientGroup.quotientKerEquivOfSurjective φ hφs
  let e' : ↥L ⧸ φ.ker ≃* ↥L ⧸ α₀.ker := QuotientGroup.quotientMulEquivOfEq hφk
  refine ⟨(QuotientGroup.kerLift α₀).comp (e'.toMonoidHom.comp
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' N))), ?_, ?_, ?_⟩
  · intro g
    obtain ⟨l, rfl⟩ := hα₀ g
    refine ⟨Subgroup.inclusion le_sup_left l, ?_⟩
    have h1 : e.symm (QuotientGroup.mk' N (Subgroup.inclusion le_sup_left l)) = (l : ↥L ⧸ φ.ker) :=
      e.symm_apply_eq.mpr rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
    rfl
  · ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · intro hx
      have h1 := (QuotientGroup.kerLift_injective α₀) (hx.trans (map_one _).symm)
      have h2 : e.symm (QuotientGroup.mk' N x) = 1 := e'.injective (h1.trans (map_one _).symm)
      have h3 : QuotientGroup.mk' N x = 1 := e.symm.injective (h2.trans (map_one _).symm)
      exact (QuotientGroup.eq_one_iff x).mp h3
    · intro hx
      have h3 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [h3, map_one, map_one, map_one]
  · intro l
    have h1 : e.symm (QuotientGroup.mk' N (Subgroup.inclusion le_sup_left l)) = (l : ↥L ⧸ φ.ker) :=
      e.symm_apply_eq.mpr rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
    rfl

theorem le_normalizer_of_le_centralizer {R V : Subgroup G}
    (hRV : R ≤ Subgroup.centralizer (V : Set G)) : R ≤ Subgroup.normalizer (V : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro n
  have h := Subgroup.mem_centralizer_iff.mp (hRV hr)
  constructor
  · intro hn
    rw [show r * n * r⁻¹ = n by rw [← h n hn]; group]
    exact hn
  · intro hn
    have hn' : r⁻¹ * (r * n * r⁻¹) * r ∈ V := by
      have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ (hRV hr))
      rw [show r⁻¹ * (r * n * r⁻¹) * r = r * n * r⁻¹ by
        rw [← hc _ hn]; group]
      exact hn
    simpa [mul_assoc] using hn'

theorem conj_mul_eq_of_mem_centralizer {R V : Subgroup G}
    (hRV : R ≤ Subgroup.centralizer (V : Set G)) {l r u : G} (hr : r ∈ R) (hu : u ∈ V) :
    (l * r) * u * (l * r)⁻¹ = l * u * l⁻¹ := by
  have h : u * r = r * u := Subgroup.mem_centralizer_iff.mp (hRV hr) u hu
  calc (l * r) * u * (l * r)⁻¹ = l * (r * u) * r⁻¹ * l⁻¹ := by group
    _ = l * (u * r) * r⁻¹ * l⁻¹ := by rw [h]
    _ = l * u * l⁻¹ := by group

theorem hom_sup_apply {Γ : Type*} [Group Γ] {L R : Subgroup G} {α₀ : ↥L →* Γ}
    {α : ↥(L ⊔ R) →* Γ} (hαker : α.ker = R.subgroupOf (L ⊔ R))
    (hαl : ∀ l : ↥L, α (Subgroup.inclusion le_sup_left l) = α₀ l) {x : ↥(L ⊔ R)} {l r : G}
    (hl : l ∈ L) (hr : r ∈ R) (hlr : l * r = x) : α x = α₀ ⟨l, hl⟩ := by
  have hx : x = Subgroup.inclusion le_sup_left ⟨l, hl⟩ * ⟨r, Subgroup.mem_sup_right hr⟩ :=
    Subtype.ext hlr.symm
  have hr1 : α ⟨r, Subgroup.mem_sup_right hr⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hαker, Subgroup.mem_subgroupOf]
    exact hr
  rw [hx, map_mul, hαl, hr1, mul_one]

theorem isNaturalSection_sup {L R V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    (h : IsNaturalSection L V Z (R.subgroupOf L) Γ) (hLR : L ≤ Subgroup.normalizer (R : Set G))
    (hRV : R ≤ Subgroup.centralizer (V : Set G)) :
    IsNaturalSection (L ⊔ R) V Z (R.subgroupOf (L ⊔ R)) Γ := by
  obtain ⟨hLV, α₀, hα₀, hker, β, hβ, hβker, hβeq⟩ := h
  obtain ⟨α, hα, hαker, hαl⟩ := exists_hom_sup α₀ hα₀ hLR hker
  refine ⟨sup_le hLV (le_normalizer_of_le_centralizer hRV), α, hα, hαker, β, hβ, hβker, ?_⟩
  intro a u v huv
  obtain ⟨l, hl, r, hr, hlr⟩ := exists_mul_of_mem_sup hLR a.2
  rw [hom_sup_apply hαker hαl hl hr hlr]
  refine hβeq ⟨l, hl⟩ u v ?_
  rw [huv, Subgroup.coe_inv, ← hlr]
  exact conj_mul_eq_of_mem_centralizer hRV hr u.2

theorem isSumOfNaturalModules_sup {L R V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {dual : Bool} {k : ℕ}
    (h : IsSumOfNaturalModules L V Z (R.subgroupOf L) Γ dual k)
    (hLR : L ≤ Subgroup.normalizer (R : Set G)) (hRV : R ≤ Subgroup.centralizer (V : Set G)) :
    IsSumOfNaturalModules (L ⊔ R) V Z (R.subgroupOf (L ⊔ R)) Γ dual k := by
  obtain ⟨α₀, hα₀, hker, hLV, hZV, β, hβ, hβker, hβeq⟩ := h
  obtain ⟨α, hα, hαker, hαl⟩ := exists_hom_sup α₀ hα₀ hLR hker
  refine ⟨α, hα, hαker, sup_le hLV (le_normalizer_of_le_centralizer hRV), hZV, β, hβ, hβker, ?_⟩
  intro a u v huv i
  obtain ⟨l, hl, r, hr, hlr⟩ := exists_mul_of_mem_sup hLR a.2
  rw [hom_sup_apply hαker hαl hl hr hlr]
  refine hβeq ⟨l, hl⟩ u v ?_ i
  rw [huv, Subgroup.coe_inv, ← hlr]
  exact conj_mul_eq_of_mem_centralizer hRV hr u.2

theorem isAltNaturalSection_sup {L R V Z : Subgroup G} {m : ℕ}
    (h : IsAltNaturalSection L V Z (R.subgroupOf L) m)
    (hLR : L ≤ Subgroup.normalizer (R : Set G)) (hRV : R ≤ Subgroup.centralizer (V : Set G)) :
    IsAltNaturalSection (L ⊔ R) V Z (R.subgroupOf (L ⊔ R)) m := by
  obtain ⟨hLV, α₀, hα₀, hker, β, hβ, hβker, hβeq⟩ := h
  obtain ⟨α, hα, hαker, hαl⟩ := exists_hom_sup α₀ hα₀ hLR hker
  refine ⟨sup_le hLV (le_normalizer_of_le_centralizer hRV), α, hα, hαker, β, hβ, hβker, ?_⟩
  intro a u v huv x hx
  obtain ⟨l, hl, r, hr, hlr⟩ := exists_mul_of_mem_sup hLR a.2
  rw [hom_sup_apply hαker hαl hl hr hlr]
  refine hβeq ⟨l, hl⟩ u v ?_ x hx
  rw [huv, Subgroup.coe_inv, ← hlr]
  exact conj_mul_eq_of_mem_centralizer hRV hr u.2

end Transfer

section Hyp

variable {G : Type} [Group G] [Finite G] {H R M L V : Subgroup G}

theorem pCoreOf_conjClosure_le (h : HypC28 H R M L V) : pCoreOf 2 (conjClosure L M) ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM0M := C2Nine.conjClosure_le_M h
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp h.sylow).2.2
  have hPC := pCoreOf_le_centralizerSection hM0M
  have hRN : R ≤ Subgroup.normalizer (pCoreOf 2 (conjClosure L M) : Set G) :=
    h.sylow.1.trans (centralizerSection_le_normalizer_right _ _ _)
  have hP : IsPGroup 2 ↥(pCoreOf 2 (conjClosure L M) ⊔ R) :=
    IsPGroup.to_sup_of_normal_left' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) h.pgroup hRN
  exact le_sup_left.trans (hmax _ (sup_le hPC h.sylow.1) hP le_sup_right)

theorem le_centralizer_V (h : HypC28 H R M L V) : R ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM0R := (c2_9_two h).1
  have hRP : R ≤ pCoreOf 2 (conjClosure L M ⊔ R) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
      (sup_le hM0R Subgroup.le_normalizer) h.pgroup
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvZ := h.V_center hv
  exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hvZ).2) r (hRP hr)).symm

theorem inf_conjClosure_eq (h : HypC28 H R M L V) :
    R ⊓ conjClosure L M = pCoreOf 2 (conjClosure L M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    (h.pgroup.to_le inf_le_left)) (le_inf (pCoreOf_conjClosure_le h)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := (c2_9_two h).1 hg
  have h2 : g ∈ Subgroup.normalizer (conjClosure L M : Set G) := Subgroup.le_normalizer hg
  simp only [Subgroup.mem_inf]
  rw [← Subgroup.mem_normalizer_iff.mp h1 x, ← Subgroup.mem_normalizer_iff.mp h2 x]

theorem subgroupOf_conjClosure_eq (h : HypC28 H R M L V) :
    R.subgroupOf (conjClosure L M) = CFSG.pCore 2 ↥(conjClosure L M) := by
  apply Subgroup.map_injective (conjClosure L M).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, ← C2A3Orbits.pCoreOf_eq_map_pCore, inf_conjClosure_eq h]

end Hyp

section SL2

variable {G : Type} [Group G]

theorem inf_centralizer_le_of_isNaturalSection {A V Z : Subgroup G} {N : Subgroup ↥A}
    {F : Type} [Field F] (h : IsNaturalSection A V Z N (StatedSL 2 F)) :
    V ⊓ Subgroup.centralizer (A : Set G) ≤ Z := by
  obtain ⟨-, α, hαs, -, β, -, hβk, hβ⟩ := h
  refine fun v hv => ?_
  obtain ⟨hvV, hvA⟩ := Subgroup.mem_inf.mp hv
  have hfix : ∀ g : StatedSL 2 F, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
      (Multiplicative.toAdd (β ⟨v, hvV⟩)) = Multiplicative.toAdd (β ⟨v, hvV⟩) := by
    intro g
    obtain ⟨a, rfl⟩ := hαs g
    have hc : v = a * v * a⁻¹ := by
      have h1 := Subgroup.mem_centralizer_iff.mp hvA a a.2
      rw [h1, Subgroup.coe_inv, mul_inv_cancel_right]
    exact (hβ a ⟨v, hvV⟩ ⟨v, hvV⟩ hc).symm
  set w := Multiplicative.toAdd (β ⟨v, hvV⟩) with hw
  let u : StatedSL 2 F :=
    ⟨⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩,
      Subgroup.subset_closure (by simp [Matrix.det_fin_two_of])⟩
  let ut : StatedSL 2 F :=
    ⟨⟨!![1, 0; 1, 1], !![1, 0; -1, 1], by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩,
      Subgroup.subset_closure (by simp [Matrix.det_fin_two_of])⟩
  have h1 : w 1 = 0 := by
    have := congrFun (hfix u) 0
    simp [u, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    exact this
  have h0 : w 0 = 0 := by
    have := congrFun (hfix ut) 1
    simp [ut, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    exact this
  have hw0 : w = 0 := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have hmem : (⟨v, hvV⟩ : ↥V) ∈ β.ker := by
    rw [MonoidHom.mem_ker]
    have : Multiplicative.toAdd (β ⟨v, hvV⟩) = 0 := hw0
    exact this
  rw [hβk] at hmem
  have := Subgroup.mem_subgroupOf.mp hmem
  exact this

theorem inf_centralizer_eq_bot_of_isNaturalSection {A V : Subgroup G} {N : Subgroup ↥A}
    {F : Type} [Field F] (h : IsNaturalSection A V ⊥ N (StatedSL 2 F)) :
    V ⊓ Subgroup.centralizer (A : Set G) = ⊥ :=
  eq_bot_iff.mpr (inf_centralizer_le_of_isNaturalSection h)

end SL2

theorem isPSL_of_mulEquiv_statedSL {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    (e : X ≃* ↥(StatedSL n (ZMod 2))) : IsPSL n 2 1 X :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two hn e

theorem modO2_mulEquiv_of_surj {G : Type} [Group G] {A : Subgroup G} {Γ : Type*} [Group Γ]
    (α : ↥A →* Γ) (hα : Function.Surjective α) (hk : α.ker = CFSG.pCore 2 ↥A) :
    Nonempty (ModO2 A ≃* Γ) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

section C31

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

theorem c48Case1_of_c31Case1 (h : HypC28 H R M L V) (hL0 : L = conjClosure L M)
    (h1 : C31Case1 H R M L V K) : C48Case1 H R M L V K := by
  obtain ⟨n, -, -, hcore, hpsl, hnat⟩ := h1
  have hM0K : conjClosure L M ≤ K := hcore ▸ (perfectCore_le (M ⊓ K)).trans inf_le_right
  have hLR := (c2_9_two h).1
  have hRV := le_centralizer_V h
  rw [← subgroupOf_conjClosure_eq h] at hnat
  refine ⟨n, by rw [hL0]; exact hpsl, Or.inl ?_⟩
  rcases hnat with ⟨F, hF, hFt, hcard, hNS⟩ | ⟨-, F, hF, hFt, hcard, hNS⟩
  · refine ⟨F, hF, hFt, hcard, ?_⟩
    have hZ : V ⊓ Subgroup.centralizer (conjClosure L M : Set G) = V ⊓ centerOf K :=
      le_antisymm (inf_centralizer_le_of_isNaturalSection hNS)
        (le_inf inf_le_left (inf_le_right.trans ((inf_le_right : centerOf K ≤ _).trans
          (Subgroup.centralizer_le hM0K))))
    have h2 := isNaturalSection_sup hNS hLR hRV
    rw [← hZ, ← hL0] at h2
    exact h2
  · refine ⟨F, hF, hFt, hcard, ?_⟩
    have h2 := isNaturalSection_sup hNS hLR hRV
    rw [← hL0] at h2
    exact h2

theorem c48Case2_of_c31Case2 (h : HypC28 H R M L V) (hL0 : L = conjClosure L M)
    (h2 : C31Case2 H R M L V K) :
    C48Case2 H R M L V K ∧ ∃ m : ℕ, (m = 3 ∨ m = 4) ∧
      IsSumOfNaturalModules (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R)) (StatedSL m (ZMod 2)) false 1 := by
  obtain ⟨n, hn, -, -, -, hcase⟩ := h2
  have hLR := (c2_9_two h).1
  have hRV := le_centralizer_V h
  have key : ∀ m : ℕ, (m = 3 ∨ m = 4) →
      IsNaturalSection (conjClosure L M) V ⊥ (CFSG.pCore 2 ↥(conjClosure L M))
        (StatedSL m (ZMod 2)) →
      C48Case2 H R M L V K ∧ ∃ m : ℕ, (m = 3 ∨ m = 4) ∧
        IsSumOfNaturalModules (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R)) (StatedSL m (ZMod 2))
          false 1 := by
    intro m hm hNS
    have hpsl : IsPSL m 2 1 (ModO2 (conjClosure L M)) := by
      obtain ⟨-, α, hα, hk, -⟩ := hNS
      obtain ⟨e⟩ := modO2_mulEquiv_of_surj α hα hk
      exact isPSL_of_mulEquiv_statedSL (by omega) e
    rw [← subgroupOf_conjClosure_eq h] at hNS
    have hS := isSumOfNaturalModules_sup
      ((isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hNS) hLR hRV
    rw [← hL0] at hS hpsl
    exact ⟨⟨m, hm, hpsl, Or.inl ⟨1, le_rfl, hS⟩⟩, m, hm, hS⟩
  rcases hcase with ⟨-, -, hNS⟩ | ⟨rfl, -, hNS⟩
  · exact key (n - 1) (by omega) hNS
  · exact key 3 (Or.inl rfl) hNS

end C31

section SL32

theorem card_statedSL_three_two : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

@[expose] def firstColumn (w : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  if w 0 = 1 then !![1, 0, 0; w 1, 1, 0; w 2, 0, 1]
  else if w 1 = 1 then !![0, 1, 0; 1, 0, 0; w 2, 0, 1]
  else !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem firstColumn_spec : ∀ w : Fin 3 → ZMod 2, w ≠ 0 →
    (firstColumn w).det = 1 ∧ (firstColumn w).mulVec (Pi.single 0 1) = w := by
  unfold firstColumn
  decide

@[expose] def cycleMat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem cycleMat_spec : cycleMat.det = 1 ∧ cycleMat.mulVec (Pi.single 0 1) = Pi.single 1 1 ∧
    cycleMat.mulVec (Pi.single 1 1) = Pi.single 2 1 := by
  unfold cycleMat
  decide

@[expose] def toSL3 (m : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : m.det = 1) :
    ↥(StatedSL 3 (ZMod 2)) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero m (by rw [h]; exact one_ne_zero),
    Subgroup.subset_closure (by simpa using h)⟩

theorem toSL3_coe (m : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : m.det = 1) :
    (((toSL3 m h : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = m := rfl

theorem transvec12_det :
    (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
  decide

theorem transvec21_det :
    (!![1, 0, 0; 1, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
  decide

theorem transvec_ne : (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
    !![1, 0, 0; 1, 1, 0; 0, 0, 1] ≠
    !![1, 0, 0; 1, 1, 0; 0, 0, 1] * !![1, 1, 0; 0, 1, 0; 0, 0, 1] := by
  decide

theorem exists_ne_statedSL_three : ∃ a b : ↥(StatedSL 3 (ZMod 2)), a * b ≠ b * a := by
  refine ⟨toSL3 _ transvec12_det, toSL3 _ transvec21_det, fun hc => transvec_ne ?_⟩
  have hc' := congrArg (fun g : ↥(StatedSL 3 (ZMod 2)) =>
    ((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) hc
  simp [toSL3_coe] at hc'

theorem eq_top_of_statedSL_three {W : AddSubgroup (Fin 3 → ZMod 2)}
    (hW : ∀ g : ↥(StatedSL 3 (ZMod 2)), ∀ w ∈ W,
      ((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w ∈ W)
    {w : Fin 3 → ZMod 2} (hw : w ∈ W) (hw0 : w ≠ 0) : W = ⊤ := by
  obtain ⟨hdet, hcol⟩ := firstColumn_spec w hw0
  obtain ⟨hcd, hc0, hc1⟩ := cycleMat_spec
  set A := toSL3 (firstColumn w) hdet with hA
  have he0 : (Pi.single 0 1 : Fin 3 → ZMod 2) ∈ W := by
    have h := hW A⁻¹ w hw
    have : (((A⁻¹ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w = Pi.single 0 1 := by
      rw [← hcol]
      rw [Matrix.mulVec_mulVec]
      have h1 : (((A⁻¹ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) * firstColumn w = 1 := by
        rw [← toSL3_coe (firstColumn w) hdet, ← hA]
        rw [show (((A⁻¹ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2)) * ((A : GL (Fin 3) (ZMod 2)) :
              Matrix (Fin 3) (Fin 3) (ZMod 2)) =
            (((A⁻¹ * A : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
              Matrix (Fin 3) (Fin 3) (ZMod 2)) by rfl]
        rw [inv_mul_cancel]
        rfl
      rw [h1, Matrix.one_mulVec]
    rwa [this] at h
  set c := toSL3 cycleMat hcd with hc
  have he1 : (Pi.single 1 1 : Fin 3 → ZMod 2) ∈ W := by
    have h := hW c _ he0
    rwa [toSL3_coe, hc0] at h
  have he2 : (Pi.single 2 1 : Fin 3 → ZMod 2) ∈ W := by
    have h := hW c _ he1
    rwa [toSL3_coe, hc1] at h
  refine eq_top_iff.mpr fun v _ => ?_
  have hv : v = v 0 • (Pi.single 0 1 : Fin 3 → ZMod 2) + v 1 • Pi.single 1 1 +
      v 2 • Pi.single 2 1 := by
    funext i
    fin_cases i <;> simp
  have hsmul : ∀ (a : ZMod 2) (x : Fin 3 → ZMod 2), x ∈ W → a • x ∈ W := by
    intro a x hx
    have h01 : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases h01 a with rfl | rfl
    · rw [zero_smul]
      exact W.zero_mem
    · rw [one_smul]
      exact hx
  rw [hv]
  exact W.add_mem (W.add_mem (hsmul _ _ he0) (hsmul _ _ he1)) (hsmul _ _ he2)

end SL32

section B48

variable {G : Type} [Group G] [Finite G]

theorem eq_top_of_isPGroup_quotient {A : Subgroup G} (hperf : ⁅A, A⁆ = A) (N : Subgroup ↥A)
    [N.Normal] (hN : IsPGroup 2 (↥A ⧸ N)) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hperf
  have hQ : Group.IsPerfect (↥A ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hnil : Group.IsNilpotent (↥A ⧸ N) := hN.isNilpotent
  have hsolv : Group.IsSolvable (↥A ⧸ N) := inferInstance
  have hall : ∀ n, derivedSeries (↥A ⧸ N) n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [derivedSeries_succ, ih]
      exact Group.isPerfect_def.mp hQ
  obtain ⟨n, hn⟩ := (Group.isSolvable_def _).mp hsolv
  have htriv : (⊤ : Subgroup (↥A ⧸ N)) = ⊥ := (hall n).symm.trans hn
  rw [eq_top_iff]
  intro x _
  have hx : (x : ↥A ⧸ N) = 1 := by
    have := Subgroup.mem_top (x : ↥A ⧸ N)
    rw [htriv] at this
    exact this
  exact (QuotientGroup.eq_one_iff x).mp hx

theorem isLnBlock_of_isB48TwoModule {A V : Subgroup G} (hperf : ⁅A, A⁆ = A)
    (hVA : ⁅V, A⁆ = V) (hB : IsB48TwoModule A V) : IsLnBlock A 3 ∧ IsE2 4 ↥V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVle, hVe, hcard, hCV, -, hNS⟩ := hB
  have hNS' := hNS
  obtain ⟨hAV, α, hα, hker, β, hβ, hβker, hβeq⟩ := hNS'
  have hVp : IsPGroup 2 ↥V := C2Nine.isPGroup_two_of_isElemAbelian hVe
  have hQ : pCoreOf 2 A = V := by
    refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVle hAV hVp)
    have hsimp : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
      B69.isSimpleGroup_statedSL_two (Nat.card_zmod 2) le_rfl
    have hnorm : ((CFSG.pCore 2 ↥A).map α).Normal :=
      (inferInstance : (CFSG.pCore 2 ↥A).Normal).map α hα
    have := hnorm
    rcases hsimp.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥A).map α) with hb | ht
    · have hle : CFSG.pCore 2 ↥A ≤ α.ker := (Subgroup.map_eq_bot_iff _).mp hb
      rw [hker] at hle
      rw [C2A3Orbits.pCoreOf_eq_map_pCore]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact Subgroup.mem_subgroupOf.mp (hle hy)
    · exfalso
      have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥A).map α) := (CFSG.pCore_isPGroup).map α
      rw [ht] at hp
      have hp' : IsPGroup 2 ↥(StatedSL 3 (ZMod 2)) :=
        hp.of_equiv Subgroup.topEquiv
      obtain ⟨k, hk⟩ := hp'.exists_card_eq
      rw [card_statedSL_three_two] at hk
      have h7 : 7 ∣ 2 ^ k := hk ▸ (by norm_num : 7 ∣ 168)
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h7))
      omega
  have hQ' : CFSG.pCore 2 ↥A = V.subgroupOf A := by
    apply Subgroup.map_injective A.subtype_injective
    rw [← C2A3Orbits.pCoreOf_eq_map_pCore, hQ, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hVle]
  have hU : blockU A = V := by
    unfold blockU blockQ
    rw [hQ, hVA]
  have hZ : blockZ A = V ⊓ Subgroup.centralizer (A : Set G) := by
    unfold blockZ
    rw [hU]
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
    have := hVe.1
    exact setLike_mul_comm hx hy
  have hAU : A ≤ Subgroup.normalizer (blockU A : Set G) := by rw [hU]; exact hAV
  have hMB : IsMatrixBlockType A (StatedSL 3 (ZMod 2)) := by
    rw [isMatrixBlockType_iff_isNaturalSection A _ hAU, hU, hZ, hQ']
    exact hNS
  have hq : CFSG.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A) := by
    obtain ⟨e⟩ := modO2_mulEquiv_of_surj α hα (hker.trans hQ'.symm)
    have hsimp : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
      B69.isSimpleGroup_statedSL_two (Nat.card_zmod 2) le_rfl
    have : IsSimpleGroup (ModO2 A) := e.isSimpleGroup
    refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
    obtain ⟨a, b, hab⟩ := exists_ne_statedSL_three
    refine ⟨e.symm a, e.symm b, fun hc => hab (e.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact hc
  have hshort : IsShort2 A := by
    refine ⟨fun N _ hN => eq_top_of_isPGroup_quotient hperf N hN, ?_, ⟨?_, ?_⟩, Or.inl hq, ?_,
      ?_⟩
    · show A ⊓ Subgroup.centralizer (pCoreOf 2 A : Set G) ≤ pCoreOf 2 A
      rw [hQ, hCV]
    · rw [hU]
      unfold blockQ
      rw [hQ]
      exact le_inf le_rfl fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
    · intro x hx
      rw [hU] at hx
      exact hVe.2 x hx
    · rw [hZ, hU]
      refine lt_of_le_of_ne inf_le_left fun heq => ?_
      have hVC : V ≤ Subgroup.centralizer (A : Set G) := heq ▸ inf_le_right
      have hbot : ⁅V, A⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact hVC
      rw [hVA] at hbot
      rw [hbot] at hcard
      simp at hcard
    · intro W hZW hWU hAW
      rw [hZ] at hZW ⊢
      rw [hU] at hWU ⊢
      by_cases hWZ : W ≤ V ⊓ Subgroup.centralizer (A : Set G)
      · exact Or.inl (le_antisymm hWZ hZW)
      right
      obtain ⟨w, hwW, hwZ⟩ := Set.not_subset.mp hWZ
      let W' : AddSubgroup (Fin 3 → ZMod 2) :=
        { carrier := {x | ∃ v : ↥V, (v : G) ∈ W ∧ Multiplicative.toAdd (β v) = x}
          add_mem' := by
            rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
            exact ⟨a * b, W.mul_mem ha hb, by rw [map_mul]; rfl⟩
          zero_mem' := ⟨1, W.one_mem, by rw [map_one]; rfl⟩
          neg_mem' := by
            rintro _ ⟨a, ha, rfl⟩
            exact ⟨a⁻¹, W.inv_mem ha, by rw [map_inv]; rfl⟩ }
      have hW'inv : ∀ g : ↥(StatedSL 3 (ZMod 2)), ∀ x ∈ W',
          ((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x ∈ W' := by
        rintro g _ ⟨v, hvW, rfl⟩
        obtain ⟨a, rfl⟩ := hα g
        have hyW : (a : G) * v * (a : G)⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hAW a.2) v).mp hvW
        have hyV : (a : G) * v * (a : G)⁻¹ ∈ V := hWU hyW
        exact ⟨⟨_, hyV⟩, hyW, (hβeq a v ⟨_, hyV⟩ rfl)⟩
      have hw0 : Multiplicative.toAdd (β ⟨w, hWU hwW⟩) ≠ 0 := by
        intro h0
        apply hwZ
        have hk : (⟨w, hWU hwW⟩ : ↥V) ∈ β.ker := h0
        rw [hβker] at hk
        exact Subgroup.mem_subgroupOf.mp hk
      have htop := eq_top_of_statedSL_three hW'inv ⟨⟨w, hWU hwW⟩, hwW, rfl⟩ hw0
      refine le_antisymm hWU fun v hv => ?_
      have hmem : Multiplicative.toAdd (β ⟨v, hv⟩) ∈ W' := htop ▸ AddSubgroup.mem_top _
      obtain ⟨u, huW, hu⟩ := hmem
      have hk : u⁻¹ * ⟨v, hv⟩ ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have : β u = β ⟨v, hv⟩ := Multiplicative.toAdd.injective hu
        rw [this]
        exact inv_mul_cancel (β ⟨v, hv⟩)
      rw [hβker] at hk
      have hZv : (u : G)⁻¹ * v ∈ W := hZW (Subgroup.mem_subgroupOf.mp hk)
      have e : v = (u : G) * ((u : G)⁻¹ * v) := by group
      rw [e]
      exact W.mul_mem huW hZv
  refine ⟨⟨hshort, hMB⟩, ?_⟩
  exact CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := ↥V)
    (fun a b => Subtype.ext (hcomm a a.2 b b.2))
    (fun a => Subtype.ext (by simpa using hVe.2 a a.2)) hcard

end B48

section Blocks

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

theorem c48Case9_of_c31Case10 (h : HypC28 H R M L V) (hL0 : L = conjClosure L M)
    (h10 : C31Case10 H R M L V K) : C48Case9 H R M L V K := by
  obtain ⟨hK2, -, hB⟩ := h10
  obtain ⟨hblk, hE⟩ := isLnBlock_of_isB48TwoModule (C2Nine.perfect_conjClosure_of_hyp h)
    h.V_comm hB
  rw [← hL0] at hblk
  exact ⟨hK2, hblk, hE⟩

omit [Finite G] in
theorem le_normalizer_blockU (L : Subgroup G) :
    L ≤ Subgroup.normalizer (blockU L : Set G) :=
  le_sup_right.trans (A3.sup_le_normalizer_commutator (blockQ L) L)

theorem c48_of_c41Case1 (h : HypC28 H R M L V)
    (hL0 : L = conjClosure L M) (h1 : C41Case1 H R M L V K) :
    C48Case1 H R M L V K ∨ C48Case8 H R M L V K := by
  obtain ⟨n, hn, hblk, hV, hKblk, -, -⟩ := h1
  have hN := subgroupOf_conjClosure_eq h
  rw [← hL0] at hblk hV hN
  rcases hn with rfl | rfl
  · left
    obtain ⟨-, α, hα⟩ := hblk
    have hAlt := (exists_isAltBlockTypeWith_iff_isAltNaturalSection L 5
      (le_normalizer_blockU L)).mp ⟨α, hα⟩
    rw [← hV, ← hN] at hAlt
    have hZ : blockZ L = V ⊓ Subgroup.centralizer (L : Set G) := by
      unfold blockZ
      rw [← hV]
    rw [hZ] at hAlt
    have hLR : L ≤ Subgroup.normalizer (R : Set G) := hL0 ▸ (c2_9_two h).1
    have hA5 : 2 = 2 ∧ IsAltNaturalSection (L ⊔ R) V (V ⊓ Subgroup.centralizer (L : Set G))
        (R.subgroupOf (L ⊔ R)) 5 := ⟨rfl, isAltNaturalSection_sup hAlt hLR (le_centralizer_V h)⟩
    obtain ⟨e⟩ := modO2_mulEquiv_of_surj α hα.1 hα.2.1
    refine ⟨2, C126.isPSL_two_two_two_of_alternating_five _ ⟨e⟩, ?_⟩
    exact Or.inr (Or.inl hA5)
  · exact Or.inr ⟨hKblk, hblk⟩

end Blocks

section Ten

variable {G : Type} [Group G] [Finite G] {H R M L V : Subgroup G}

theorem c48Conclusion_of_le (hC129 : ASC129Statement G) (hC111 : ASC111Statement G)
    (hC19 : ASC19Statement G) (hA3 : A3Orbits G) (hStep : ASC213Step G)
    (h36 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A36Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (h : HypC28 H R M L V) (hMH : M < H) (hF : oTwoFstarIn H ≤ M) :
    C48Conclusion H R M L V := by
  obtain ⟨T, hT, hRT⟩ := B6.exists_isSylowTwoOf_ge h.pgroup h.le_M
  rcases c2_13 hC129 hC111 hC19 hA3 hStep h hT hRT hF with hHM | ⟨hM0, hLc, hMeq, hidx⟩
  · exact absurd hHM.symm hMH.ne
  · have hn : ¬ H ≤ Subgroup.normalizer (L : Set G) := by
      intro hHN
      apply hMH.ne
      rw [hMeq, hM0]
      exact inf_eq_left.mpr hHN
    obtain ⟨hq, htypes⟩ := a38_of_not_le_normalizer h36 h38 h.sqtk hLc hn
    refine ⟨hM0.symm, L, hLc, hq, le_rfl, Or.inl ⟨hF, ?_, hMeq, hidx⟩⟩
    rcases htypes with ⟨n, h1⟩ | ⟨n, h1⟩ | h1 | ⟨p, hp, hp3, h1⟩
    · exact Or.inl ⟨n, h1⟩
    · exact Or.inr (Or.inl ⟨n, h1⟩)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr ⟨p, hp, by omega, h1⟩))

end Ten

section Main

theorem or9_of_or7 {a b c d e f g h i : Prop} (x : a ∨ b ∨ c ∨ d ∨ e ∨ f ∨ g) :
    a ∨ b ∨ c ∨ d ∨ e ∨ f ∨ g ∨ h ∨ i := by
  tauto

theorem or9_eight {a b c d e f g h i : Prop} (x : h) : a ∨ b ∨ c ∨ d ∨ e ∨ f ∨ g ∨ h ∨ i := by
  tauto

theorem or9_nine {a b c d e f g h i : Prop} (x : i) : a ∨ b ∨ c ∨ d ∨ e ∨ f ∨ g ∨ h ∨ i := by
  tauto

variable {G : Type} [Group G] [Finite G]

theorem asc48Statement_of
    (hC31 : ASC31Statement G) (hC41 : ASC41Statement G)
    (hSpor : C48SporStep G) (hLine : C48C41LineStep G) (hFour : C48C41FourStep G)
    (hC129 : ASC129Statement G) (hC111 : ASC111Statement G) (hC19 : ASC19Statement G)
    (hA3 : A3Orbits G) (hStep : ASC213Step G)
    (h36 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A36Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) : ASC48Statement G := by
  intro H R M L V h hMH
  by_cases hF : oTwoFstarIn H ≤ M
  · exact c48Conclusion_of_le hC129 hC111 hC19 hA3 hStep h36 h38 h hMH hF
  obtain ⟨K, hK, hq, hKM⟩ := exists_cComp_not_le h (c2_11 hC129 hC19 h) hF
  rcases isComponentOf_or_charTwo (c2_10_one h) hK hq with hcomp | hchar
  ·
    have h31 := hC31 H R M L V K h hcomp
    obtain ⟨hL0, -, hM0K, hMK, -, hcases⟩ := id h31
    refine ⟨hL0, K, hK, hq, hL0.le.trans hM0K, Or.inr ⟨?_, hKM, hMK, Or.inl ⟨hcomp, h31⟩⟩⟩
    have hspor := fun hc => (hSpor H R M L V K h hcomp h31 hc).1
    rcases hcases with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
    · exact Or.inl (c48Case1_of_c31Case1 h hL0 c1)
    · exact Or.inr (Or.inl (c48Case2_of_c31Case2 h hL0 c2).1)
    · exact or9_of_or7 (hspor (Or.inl c3))
    · exact or9_of_or7 (hspor (Or.inr (Or.inl c4)))
    · exact or9_of_or7 (hspor (Or.inr (Or.inr (Or.inl c5))))
    · exact or9_of_or7 (hspor (Or.inr (Or.inr (Or.inr (Or.inl c6)))))
    · exact or9_of_or7 (hspor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c7))))))
    · exact or9_of_or7 (hspor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c8)))))))
    · exact or9_of_or7 (hspor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c9)))))))
    · exact or9_nine (c48Case9_of_c31Case10 h hL0 c10)
  ·
    have h41 := hC41 H R M L V K h hK hchar hq hKM
    obtain ⟨hL0, hM0K0, hK0, hcases⟩ := id h41
    have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
      have := le_normalizer_conjClosure K H
      rwa [hK0] at this
    refine ⟨hL0, K, hK, hq, hL0.le.trans (hM0K0.trans hK0.le),
      Or.inr ⟨?_, hKM, h.le_H.trans hHK, Or.inr ⟨hK, hchar, hq, hKM, h41⟩⟩⟩
    rcases hcases with c1 | c2 | c3 | c4
    · rcases c48_of_c41Case1 h hL0 c1 with h1 | h8
      · exact Or.inl h1
      · exact or9_eight h8
    · exact Or.inl (hLine H R M L V K h hK hchar hq hKM h41 (Or.inl c2))
    · exact Or.inl (hLine H R M L V K h hK hchar hq hKM h41 (Or.inr c3))
    · exact Or.inr (Or.inl (hFour H R M L V K h hK hchar hq hKM h41 c4).1)

end Main

section SumBound

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_of_isSumOfNaturalModules_bot {A V : Subgroup G} {N : Subgroup ↥A} {ι : Type}
    [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Fintype F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {dual : Bool} {k : ℕ}
    (h : IsSumOfNaturalModules A V ⊥ N Γ dual k) :
    Nat.card ↥V = Fintype.card F ^ (Fintype.card ι * k) := by
  obtain ⟨-, -, -, -, -, β, hβ, hker, -⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hinj, hβ⟩).toEquiv, Nat.card_eq_fintype_card]
  simp only [Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fin]
  ring

theorem card_of_isPSL_two_one {m : ℕ} (hm : m = 3 ∨ m = 4) {X : Type} [Group X]
    (h : IsPSL m 2 1 X) : Nat.card X = 168 ∨ Nat.card X = 20160 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega : 1 ≤ m), hK]
  rcases hm with rfl | rfl
  · left; decide
  · right; decide

theorem card_of_isPSL_two_two_ne {n : ℕ} {X : Type} [Group X] (h : IsPSL 2 2 n X) :
    Nat.card X ≠ 168 ∧ Nat.card X ≠ 20160 := by
  rw [card_psl_two_two h]
  have key : ∀ c : ℕ, c = 168 ∨ c = 20160 → 2 ^ n * (4 ^ n - 1) ≠ c := by
    rintro c hc hn
    have hdvd : 2 ^ n ∣ c := ⟨_, hn.symm⟩
    have hle : 2 ^ n ≤ 20160 := by
      rcases hc with rfl | rfl
      · exact (Nat.le_of_dvd (by norm_num) hdvd).trans (by norm_num)
      · exact Nat.le_of_dvd (by norm_num) hdvd
    have hn15 : n < 15 := by
      by_contra hn'
      have : 2 ^ 15 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> rcases hc with rfl | rfl <;> norm_num at hn
  exact ⟨key 168 (Or.inl rfl), key 20160 (Or.inr rfl)⟩

theorem not_isPSL_of_alt {n : ℕ} (hn : n = 5 ∨ n = 6) {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin n)) {m : ℕ} (hm : m = 3 ∨ m = 4) : ¬ IsPSL m 2 1 X := by
  intro h
  have h1 := card_of_isPSL_two_one hm h
  rw [Nat.card_congr e.toEquiv] at h1
  rcases hn with rfl | rfl <;>
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1 <;>
    norm_num at h1

theorem not_isPSL_of_isPSL_two_two {n m : ℕ} (hm : m = 3 ∨ m = 4) {X : Type} [Group X]
    (h2 : IsPSL 2 2 n X) : ¬ IsPSL m 2 1 X := by
  intro h
  have h1 := card_of_isPSL_two_one hm h
  have h3 := card_of_isPSL_two_two_ne h2
  omega

theorem c48SumBound_of (hC31 : ASC31Statement G) (hC41 : ASC41Statement G)
    (hSpor : C48SporStep G) (hFour : C48C41FourStep G)
    (hC129 : ASC129Statement G) (hC19 : ASC19Statement G) : C48SumBound G := by
  intro H R M L V m k h hMH hF hm hpsl hsum
  obtain ⟨K, hK, hq, hKM⟩ := exists_cComp_not_le h (c2_11 hC129 hC19 h) hF
  have hcardV : Nat.card ↥V = 2 ^ (m * k) := by
    rw [card_of_isSumOfNaturalModules_bot hsum, ZMod.card, Fintype.card_fin]
  rcases isComponentOf_or_charTwo (c2_10_one h) hK hq with hcomp | hchar
  · have h31 := hC31 H R M L V K h hcomp
    obtain ⟨hL0, -, -, -, -, hcases⟩ := id h31
    have hspor := fun hc =>
      ((hSpor H R M L V K h hcomp h31 hc).2 m k hm hpsl hsum).trans (by norm_num : 2 ≤ 4)
    rcases hcases with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
    · exfalso
      obtain ⟨n, -, -, -, h2, -⟩ := c1
      have hpsl' := hpsl
      rw [hL0] at hpsl'
      exact not_isPSL_of_isPSL_two_two hm h2 hpsl'
    · obtain ⟨-, m', hm', hs'⟩ := c48Case2_of_c31Case2 h hL0 c2
      have h1 := card_of_isSumOfNaturalModules_bot hs'
      rw [ZMod.card, Fintype.card_fin, hcardV] at h1
      have := Nat.pow_right_injective le_rfl h1
      rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl <;> omega
    · exact hspor (Or.inl c3)
    · exact hspor (Or.inr (Or.inl c4))
    · exact hspor (Or.inr (Or.inr (Or.inl c5)))
    · exact hspor (Or.inr (Or.inr (Or.inr (Or.inl c6))))
    · exact hspor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c7)))))
    · exact hspor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c8))))))
    · exact hspor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c9))))))
    · obtain ⟨-, -, hB⟩ := c10
      obtain ⟨-, -, h16, -⟩ := hB
      rw [hcardV] at h16
      have := Nat.pow_right_injective le_rfl h16
      rcases hm with rfl | rfl <;> omega
  · have h41 := hC41 H R M L V K h hK hchar hq hKM
    obtain ⟨hL0, -, -, hcases⟩ := id h41
    rcases hcases with c1 | c2 | c3 | c4
    · exfalso
      obtain ⟨n, hn, ⟨-, α, hα⟩, -⟩ := c1
      obtain ⟨e⟩ := modO2_mulEquiv_of_surj α hα.1 hα.2.1
      rw [← hL0] at e
      exact not_isPSL_of_alt hn e hm hpsl
    · exfalso
      obtain ⟨-, F, _, _, α, β, -, -, -, -, -, h2⟩ := c2
      have hpsl' := hpsl
      rw [hL0] at hpsl'
      exact not_isPSL_of_isPSL_two_two hm h2 hpsl'
    · exfalso
      obtain ⟨n, F, _, _, -, -, -, -, -, -, h2, -⟩ := c3
      have hpsl' := hpsl
      rw [hL0] at hpsl'
      exact not_isPSL_of_isPSL_two_two hm h2 hpsl'
    · exact (hFour H R M L V K h hK hchar hq hKM h41 c4).2 m k hm hpsl hsum

end SumBound

end CFSG.Quasithin.C48
