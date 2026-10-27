module

public import CFSG.Quasithin.Vol2.Ch11SecA15Q
public import CFSG.Quasithin.Vol2.Ch11SecA15MS3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_mem_of_perfect {L A B : Subgroup G} (hL : ⁅L, L⁆ = L) (hBA : B ≤ A)
    (hAB : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B)
    (hLA : ∀ l ∈ L, ∀ a ∈ A, l * a * l⁻¹ * a⁻¹ ∈ B) {z : G}
    (hz : ∀ l ∈ L, l * z * l⁻¹ * z⁻¹ ∈ A) : ∀ l ∈ L, l * z * l⁻¹ * z⁻¹ ∈ B := by
  have hBn : (B.subgroupOf A).Normal := by
    refine ⟨fun b hb a => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hb ⊢
    have h1 := hAB a a.2 b (hBA hb)
    have : ((a * b * a⁻¹ : ↥A) : G) = ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * b := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this]
    exact B.mul_mem h1 hb
  have hmk : ∀ a a' : ↥A, (a : G)⁻¹ * a' ∈ B →
      (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A) = QuotientGroup.mk a' := by
    intro a a' h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using h
  have hcomm : ∀ x y : ↥A ⧸ B.subgroupOf A, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H a' => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    apply hmk
    have := hAB _ (A.inv_mem a'.2) _ (A.inv_mem a.2)
    have e : ((a * a' : ↥A) : G)⁻¹ * ((a' * a : ↥A) : G) =
        (a' : G)⁻¹ * (a : G)⁻¹ * (a' : G)⁻¹⁻¹ * (a : G)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact this
  let D : ↥L → ↥A := fun l => ⟨(l : G) * z * (l : G)⁻¹ * z⁻¹, hz l l.2⟩
  have hD : ∀ x y : ↥L, (QuotientGroup.mk (D (x * y))⁻¹ : ↥A ⧸ B.subgroupOf A) =
      QuotientGroup.mk (D x)⁻¹ * QuotientGroup.mk (D y)⁻¹ := by
    intro x y
    rw [← QuotientGroup.mk_mul]
    apply hmk
    have e : (((D (x * y))⁻¹ : ↥A) : G)⁻¹ * (((D x)⁻¹ * (D y)⁻¹ : ↥A) : G) =
        (x : G) * (D y : G) * (x : G)⁻¹ * (D y : G)⁻¹ := by
      simp only [D, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hLA x x.2 _ (D y).2
  let φ : ↥L →* ↥A ⧸ B.subgroupOf A :=
    { toFun := fun l => QuotientGroup.mk (D l)⁻¹
      map_one' := by
        rw [← QuotientGroup.mk_one]
        apply hmk
        simp [D]
      map_mul' := hD }
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  have hker : commutator ↥L ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  intro l hl
  have h1 : φ ⟨l, hl⟩ = 1 := hker Group.IsPerfect.mem_commutator
  have h2 : (QuotientGroup.mk (D ⟨l, hl⟩)⁻¹ : ↥A ⧸ B.subgroupOf A) = QuotientGroup.mk 1 := h1
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
  simpa [D] using h2

theorem mem_centralizer_of_perfect {L A : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hLA : ∀ l ∈ L, ∀ a ∈ A, l * a = a * l) {c : G}
    (hc : ∀ l ∈ L, l * c * l⁻¹ * c⁻¹ ∈ A) : c ∈ Subgroup.centralizer (L : Set G) := by
  have h := commutator_mem_of_perfect (B := ⊥) hL bot_le
    (fun a ha a' ha' => by rw [hA a ha a' ha', Subgroup.mem_bot]; group)
    (fun l hl a ha => by rw [hLA l hl a ha, Subgroup.mem_bot]; group) hc
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := h l hl
  rw [Subgroup.mem_bot] at h1
  calc l * c = l * c * l⁻¹ * c⁻¹ * (c * l) := by group
    _ = c * l := by rw [h1, one_mul]

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem pCoreOf_LT_le_ROf (h : Hyp11 G T L I n) : pCoreOf 2 (L ⊔ T) ≤ ROf T L V₁ :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right)).trans le_sup_right)
    (sup_le (lOf_le_L.trans (le_sup_left.trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)))
      (le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem pCoreOf_msG0_le_ROf (h : Hyp11 G T L I n) :
    pCoreOf 2 (L ⊔ ROf T L V₁) ≤ ROf T L V₁ :=
  (pCoreOf_msG0_le_pCoreOf_LT h).trans (pCoreOf_LT_le_ROf h)

theorem centerOf_ROf_le_pCoreOf_msG0 (h : Hyp11 G T L I n) :
    centerOf (ROf T L V₁) ≤ pCoreOf 2 (L ⊔ ROf T L V₁) := by
  intro z hz
  refine charTwo_msG0 h ⟨Subgroup.mem_sup_right hz.1,
    Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  exact Subgroup.mem_centralizer_iff.mp hz.2 k (pCoreOf_msG0_le_ROf h hk)

theorem commutator_mem_pCoreOf_L (h : Hyp11 G T L I n) {z l : G}
    (hz : z ∈ pCoreOf 2 (L ⊔ ROf T L V₁)) (hl : l ∈ L) :
    l * z * l⁻¹ * z⁻¹ ∈ pCoreOf 2 L := by
  have hN : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ ROf T L V₁) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hle : L ⊓ pCoreOf 2 (L ⊔ ROf T L V₁) ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hN hx⟩)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  have hzL : z ∈ Subgroup.normalizer (L : Set G) :=
    ROf_le_normalizer_L h (pCoreOf_msG0_le_ROf h hz)
  refine hle ⟨?_, ?_⟩
  · have := L.mul_mem hl ((Subgroup.mem_normalizer_iff.mp hzL l⁻¹).mp (L.inv_mem hl))
    simpa [mul_assoc] using this
  · exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hN hl) z).mp hz)
      (Subgroup.inv_mem _ hz)

theorem commutator_mem_blockU (h : Hyp11 G T L I n) {z : G}
    (hz : z ∈ pCoreOf 2 (L ⊔ ROf T L V₁)) : ∀ l ∈ L, l * z * l⁻¹ * z⁻¹ ∈ blockU L := by
  have hLN : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  refine commutator_mem_of_perfect h.fsu.faithful.1.2.1.2.1
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hLN) (fun a ha a' ha' => ?_)
    (fun l hl a ha => ?_) (fun l hl => commutator_mem_pCoreOf_L h hz hl)
  · have := Subgroup.commutator_mem_commutator ha (CFSG.LieType.BorelTits.pCoreOf_le 2 L ha')
    rwa [commutatorElement_def] at this
  · have := Subgroup.commutator_mem_commutator hl ha
    rw [Subgroup.commutator_comm, commutatorElement_def] at this
    exact this

end CFSG.Quasithin.Vol2.Ch11.SecA
