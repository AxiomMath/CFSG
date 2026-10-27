module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarOrthFrameD4Frame

public section

namespace CFSG.StandardType

open Module Multiplicative CFSG.Assembly CFSG.StandardType.NoOffOm CFSG.StandardType.Triality
  CFSG.StandardType.D4Rank CFSG.StandardType.OrthD4
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace OrdPTri

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_frame {E : Subgroup (Om8 K)} (hE : IsElemAbelian 3 E)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set (Om8 K)), g ^ 3 = 1 → g ∈ E) :
    ∃ (r : ℕ) (ι₁ : Multiplicative (Fin r → ZMod 3) →* Om8 K), r ≤ 4 ∧ Function.Injective ι₁ ∧
      ι₁.range = E ∧
      (∀ s s' : Fin r → ZMod 3, (LinearMap.ker (omRep (ι₁ (ofAdd s')) - 1) ≤
        LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) ↔ SuppLE s s')) ∧
      (4 ≤ r → ∀ s : Fin r → ZMod 3, omFixDim (ι₁ (ofAdd s)) + 2 * (supp s).card = 8) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : NeZero (3 : ℕ) := ⟨by norm_num⟩
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hA := genMax_of_orth hnd hT Nat.prime_three (by norm_num) hE hSC (MonoidHom.id _)
    Function.injective_id (fun x _ => ⟨x, rfl⟩)
  obtain ⟨r, ι₀, hinj₀, hrange₀, hsupp₀⟩ := exists_genPieceFrame hA
  have hι₀A : ∀ s, ι₀ s ∈ (E.comap (MonoidHom.id _)).map
      (matrixDerived (coordinateQuadPlus 4 K)).subtype :=
    fun s => hrange₀ ▸ MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hι₀Γ : ∀ s, ι₀ s ∈ matrixDerived (coordinateQuadPlus 4 K) := fun s => hA.le (hι₀A s)
  set ι₁ : Multiplicative (Fin r → ZMod 3) →* Om8 K := ι₀.codRestrict _ hι₀Γ with hι₁def
  have hι₁ : ∀ s, ((ι₁ s : Om8 K) : GL (Fin (2 * 4)) K) = ι₀ s := fun s => rfl
  have hinj : Function.Injective ι₁ := fun s t hst =>
    hinj₀ (by rw [← hι₁, ← hι₁, hst])
  have hrange : ι₁.range = E := by
    ext b
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨Y, hY, hYs⟩ := hι₀A s
      have hYι : Y = ι₁ s := Subtype.ext hYs
      rw [← hYι]
      exact hY
    · intro hb
      have hYA : (b : GL (Fin (2 * 4)) K) ∈ ι₀.range := by rw [hrange₀]; exact ⟨b, hb, rfl⟩
      obtain ⟨s, hs⟩ := hYA
      exact ⟨s, Subtype.ext hs⟩
  have hker : ∀ s v, v ∈ LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) ↔
      glin (ι₀ (ofAdd s)) v = v := by
    intro s v
    rw [mem_ker_omRep_sub_one, glin_apply, hι₁]
  have hkerle : ∀ s s' : Fin r → ZMod 3, (LinearMap.ker (omRep (ι₁ (ofAdd s')) - 1) ≤
      LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) ↔ SuppLE s s') := by
    intro s s'
    rw [← hsupp₀ s s']
    constructor
    · intro h v hv
      rw [← hker] at hv ⊢
      exact h hv
    · intro h v hv
      rw [hker] at hv ⊢
      exact h v hv
  set d : (Fin r → ZMod 3) → ℕ := fun s => omFixDim (ι₁ (ofAdd s)) with hd
  have hle8 : ∀ s, d s ≤ 8 := fun s => by
    have := Submodule.finrank_le (LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1))
    rwa [Module.finrank_fin_fun] at this
  have h3 : ∀ s, ι₁ s ^ 3 = 1 := fun s => Subtype.ext (by
    rw [SubgroupClass.coe_pow, hι₁, OneMemClass.coe_one]
    exact hA.pow _ (hι₀A s))
  have heven : ∀ s, Even (d s) := fun s => omFixDim_even _ (h3 _)
  have hlt : ∀ s s', SuppLE s s' → ¬ SuppLE s' s → d s' + 2 ≤ d s := by
    intro s s' h1 h2
    have hle := (hkerle s s').mpr h1
    have hne : ¬ LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) ≤
        LinearMap.ker (omRep (ι₁ (ofAdd s')) - 1) := fun h => h2 ((hkerle s' s).mp h)
    have hlt' : d s' < d s := Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hle hne)
    obtain ⟨a, ha⟩ := heven s
    obtain ⟨b, hb⟩ := heven s'
    omega
  obtain ⟨hr, hcount⟩ := count_eq d hle8 hlt
  exact ⟨r, ι₁, hr, hinj, hrange, hkerle, hcount⟩

omit [Finite K] [CharP K 2] in
theorem card_eq_of_frame {r : ℕ} {ι₁ : Multiplicative (Fin r → ZMod 3) →* Om8 K}
    (hinj : Function.Injective ι₁) {E : Subgroup (Om8 K)} (hrange : ι₁.range = E) :
    Nat.card E = 3 ^ r := by
  have : NeZero (3 : ℕ) := ⟨by norm_num⟩
  rw [← hrange]
  exact NoOffUO.card_range_eq hinj

theorem isElemAbelian_sup_zpowers {G : Type*} [Group G] {A : Subgroup G}
    (hA : IsElemAbelian 3 A) {g : G} (hgA : g ∈ Subgroup.centralizer (A : Set G))
    (hg3 : g ^ 3 = 1) : IsElemAbelian 3 (A ⊔ Subgroup.zpowers g) := by
  have hcomm : ∀ a ∈ A, a * g = g * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp hgA a ha
  have hpair : ((A : Set G) ∪ (Subgroup.zpowers g : Set G)).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with hx | ⟨i, rfl⟩ <;> rcases hy with hy | ⟨j, rfl⟩
    · exact congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · exact ((Commute.zpow_right (hcomm x hx : Commute x g) j))
    · exact Commute.zpow_left (hcomm y hy : Commute y g).symm i
    · exact Commute.zpow_zpow_self g i j
  have hsup : A ⊔ Subgroup.zpowers g = Subgroup.closure ((A : Set G) ∪ Subgroup.zpowers g) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hsup]
    exact Subgroup.isMulCommutative_closure hpair
  · rw [hsup] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | ⟨i, rfl⟩
      · exact hA.2 y hy
      · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg3, one_zpow]
    | one => exact one_pow 3
    | mul y z hy hz ihy ihz =>
      have hc : Commute y z := by
        have h := Subgroup.isMulCommutative_closure hpair
        exact congrArg Subtype.val (h.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
      rw [hc.mul_pow, ihy, ihz, one_mul]
    | inv y hy ihy => rw [inv_pow, ihy, inv_one]

theorem card_le_81 {A : Subgroup (Om8 K)} (hA : IsElemAbelian 3 A) : Nat.card A ≤ 81 := by
  classical
  set S : Set (Subgroup (Om8 K)) := {B | A ≤ B ∧ IsElemAbelian 3 B} with hS
  have hSfin : S.Finite := Set.toFinite S
  obtain ⟨A', ⟨hAA', hA'⟩, hmax⟩ := Set.Finite.exists_maximalFor
    (fun B : Subgroup (Om8 K) => Nat.card B) S hSfin ⟨A, le_rfl, hA⟩
  have hSC : ∀ g ∈ Subgroup.centralizer (A' : Set (Om8 K)), g ^ 3 = 1 → g ∈ A' := by
    intro g hg hg3
    by_contra hgA
    have hel := isElemAbelian_sup_zpowers hA' hg hg3
    have hlt : A' < A' ⊔ Subgroup.zpowers g :=
      lt_of_le_of_ne le_sup_left fun h => hgA (h ▸ Subgroup.mem_sup_right
        (Subgroup.mem_zpowers g))
    have hcard : Nat.card A' < Nat.card ↥(A' ⊔ Subgroup.zpowers g) :=
      Subgroup.card_lt_of_lt hlt
    exact absurd (hmax ⟨hAA'.trans le_sup_left, hel⟩ hcard.le) (not_le.mpr hcard)
  obtain ⟨r, ι₁, hr, hinj, hrange, -, -⟩ := exists_frame hA' hSC
  have hcard := card_eq_of_frame hinj hrange
  calc Nat.card A ≤ Nat.card A' := Subgroup.card_le_of_le hAA'
    _ = 3 ^ r := hcard
    _ ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hr
    _ = 81 := by norm_num

theorem sc_of_card {E : Subgroup (Om8 K)} (hE : IsElemAbelian 3 E) (h81 : 81 ≤ Nat.card E) :
    ∀ g ∈ Subgroup.centralizer (E : Set (Om8 K)), g ^ 3 = 1 → g ∈ E := by
  intro g hg hg3
  by_contra hgE
  have hel := isElemAbelian_sup_zpowers hE hg hg3
  have hlt : E < E ⊔ Subgroup.zpowers g :=
    lt_of_le_of_ne le_sup_left fun h => hgE (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have hcard := Subgroup.card_lt_of_lt hlt
  have := card_le_81 hel
  omega

theorem exists_frame_four {E : Subgroup (Om8 K)} (hE : IsElemAbelian 3 E)
    (h81 : 81 ≤ Nat.card E) :
    ∃ ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K, Function.Injective ι₁ ∧ ι₁.range = E ∧
      (∀ s s' : Fin 4 → ZMod 3, (LinearMap.ker (omRep (ι₁ (ofAdd s')) - 1) ≤
        LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) ↔ SuppLE s s')) ∧
      ∀ s : Fin 4 → ZMod 3, omFixDim (ι₁ (ofAdd s)) + 2 * (supp s).card = 8 := by
  obtain ⟨r, ι₁, hr, hinj, hrange, hkerle, hcount⟩ := exists_frame hE (sc_of_card hE h81)
  have hcard := card_eq_of_frame hinj hrange
  have hr4 : 4 ≤ r := by
    rw [hcard] at h81
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (le_trans (by norm_num) h81)
  obtain rfl : r = 4 := le_antisymm hr hr4
  exact ⟨ι₁, hinj, hrange, hkerle, hcount le_rfl⟩

end OrdPTri

end CFSG.StandardType
