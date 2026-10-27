module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA0
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

variable {G : Type u} [Group G]

theorem mem_sup_iff_mul {H K : Subgroup G} (hK : K ≤ Subgroup.normalizer (H : Set G)) {g : G} :
    g ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, g = h * k := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left H K hK
  constructor
  · intro hg
    have hg' : g ∈ ((H ⊔ K : Subgroup G) : Set G) := hg
    rw [hset] at hg'
    obtain ⟨h, hh, k, hk, rfl⟩ := hg'
    exact ⟨h, hh, k, hk, rfl⟩
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact Subgroup.mul_mem_sup hh hk

theorem le_normalizer_sup {Q H K : Subgroup G} (hH : Q ≤ Subgroup.normalizer (H : Set G))
    (hK : Q ≤ Subgroup.normalizer (K : Set G)) :
    Q ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  (le_inf hH hK).trans (Subgroup.inf_normalizer_le_normalizer_sup H K)

theorem le_normalizer_inf {Q H K : Subgroup G} (hH : Q ≤ Subgroup.normalizer (H : Set G))
    (hK : Q ≤ Subgroup.normalizer (K : Set G)) :
    Q ≤ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) :=
  (le_inf hH hK).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem le_normalizer_sectionCentralizer {B X Y : Subgroup G}
    (hX : B ≤ Subgroup.normalizer (X : Set G)) (hY : B ≤ Subgroup.normalizer (Y : Set G)) :
    B ≤ Subgroup.normalizer ((sectionCentralizer X Y : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb x hx
  obtain ⟨hxX, hxY, hxc⟩ := mem_sectionCentralizer_iff.mp hx
  refine mem_sectionCentralizer_iff.mpr ⟨?_, ?_, fun y hy => ?_⟩
  · exact mul_mem (mul_mem (hX hb) hxX) (inv_mem (hX hb))
  · exact mul_mem (mul_mem (hY hb) hxY) (inv_mem (hY hb))
  · have hy' : b⁻¹ * y * b ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hY (inv_mem hb)) y).mp hy
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp (hX hb) _).mp (hxc _ hy')
    have e : ⁅b * x * b⁻¹, y⁆ = b * ⁅x, b⁻¹ * y * b⁆ * b⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h1

theorem isSolvableSection_of_comm {X₁ X₂ : Subgroup G}
    (h : ∀ x ∈ X₁, ∀ y ∈ X₁, ⁅x, y⁆ ∈ X₂) : IsSolvableSection X₁ X₂ := by
  refine ⟨1, ?_⟩
  rw [derivedSeries_one, commutator_def, Subgroup.commutator_def]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨a, -, b, -, rfl⟩
  exact h a a.2 b b.2

section Pairs

variable [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem pair_of_chief (hθ : NearFunctor p A θ) {X X₁ X₂ : Subgroup G}
    (hX : X ∈ mtil p A θ) (hX₁ : X₁ ≤ X)
    (hc : IsChiefFactorOf (X₁ ⊔ dsub A θ ⊔ A) X₁ X₂) (hns : ¬ IsSolvableSection X₁ X₂) :
    (X₁ ⊔ secCenIn (X₁ ⊔ dsub A θ) X₁ X₂, secCenIn (X₁ ⊔ dsub A θ) X₁ X₂) ∈ pairsP p A θ := by
  set D := dsub A θ with hD
  set E := X₁ ⊔ D ⊔ A with hE
  set C := secCenIn (X₁ ⊔ D) X₁ X₂ with hC
  obtain ⟨hn₂, hn₁, hlt, hmax⟩ := hc
  have hX₂X₁ : X₂ ≤ X₁ := hlt.le
  have hE₁ : E ≤ Subgroup.normalizer (X₁ : Set G) := hn₁.2
  have hE₂ : E ≤ Subgroup.normalizer (X₂ : Set G) := hn₂.2
  have hX₁E : X₁ ≤ E := le_sup_left.trans le_sup_left
  have hDE : D ≤ E := le_sup_right.trans le_sup_left
  have hAE : A ≤ E := le_sup_right
  have hG₁E : X₁ ⊔ D ≤ E := le_sup_left
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := admits_dsub hθ
  have hEG₁ : E ≤ Subgroup.normalizer ((X₁ ⊔ D : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer (le_normalizer_sup (hAE.trans hE₁) hAD)
  have hCE : C ≤ X₁ ⊔ D := inf_le_left
  have hCsc : ∀ c ∈ C, c ∈ Subgroup.normalizer (X₂ : Set G) ∧
      c ∈ Subgroup.normalizer (X₁ : Set G) ∧ ∀ y ∈ X₁, ⁅c, y⁆ ∈ X₂ := fun c hc' =>
    mem_sectionCentralizer_iff.mp (Subgroup.mem_inf.mp hc').2
  have hEC : E ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_inf hEG₁ (le_normalizer_sectionCentralizer hE₂ hE₁)
  have hX₂C : X₂ ≤ C := fun x hx => by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (hX₂X₁ hx),
      mem_sectionCentralizer_iff.mpr ⟨Subgroup.le_normalizer hx,
        Subgroup.le_normalizer (hX₂X₁ hx), fun y hy => ?_⟩⟩
    have hy2 : y ∈ Subgroup.normalizer (X₂ : Set G) := hE₂ (hX₁E hy)
    have h1 : y * x⁻¹ * y⁻¹ ∈ X₂ := (Subgroup.mem_normalizer_iff.mp hy2 x⁻¹).mp (inv_mem hx)
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hx h1
  have hX₁C : X₁ ⊓ C = X₂ := by
    refine le_antisymm ?_ (le_inf hX₂X₁ hX₂C)
    have hK : IsNormalIn (X₁ ⊓ sectionCentralizer X₂ X₁) E :=
      ⟨inf_le_left.trans hX₁E,
        le_normalizer_inf hE₁ (le_normalizer_sectionCentralizer hE₂ hE₁)⟩
    have hX₂K : X₂ ≤ X₁ ⊓ sectionCentralizer X₂ X₁ :=
      le_inf hX₂X₁ (fun x hx => (Subgroup.mem_inf.mp (hX₂C hx)).2)
    rcases hmax _ hK hX₂K inf_le_left with h | h
    · intro x hx
      obtain ⟨hx1, hxC⟩ := Subgroup.mem_inf.mp hx
      have : x ∈ X₁ ⊓ sectionCentralizer X₂ X₁ :=
        Subgroup.mem_inf.mpr ⟨hx1, (Subgroup.mem_inf.mp hxC).2⟩
      rw [h] at this
      exact this
    · exfalso
      refine hns (isSolvableSection_of_comm fun x hx y hy => ?_)
      have : x ∈ X₁ ⊓ sectionCentralizer X₂ X₁ := by
        rw [h]
        exact hx
      exact (mem_sectionCentralizer_iff.mp (Subgroup.mem_inf.mp this).2).2.2 y hy
  have hCN₁ : C ≤ Subgroup.normalizer (X₁ : Set G) := fun c hc' => (hCsc c hc').2.1
  have hXC_E : X₁ ⊔ C ≤ E := sup_le hX₁E (hCE.trans hG₁E)
  have hE' : (X₁ ⊔ C) ⊔ D ⊔ A = E :=
    le_antisymm (sup_le (sup_le hXC_E hDE) hAE)
      (sup_le_sup_right (sup_le_sup_right le_sup_left D) A)
  have hXCD : (X₁ ⊔ C) ⊔ D = X₁ ⊔ D :=
    le_antisymm (sup_le (sup_le le_sup_left hCE) le_sup_right)
      (sup_le_sup_right le_sup_left D)
  have hnC : IsNormalIn C E := ⟨hCE.trans hG₁E, hEC⟩
  have hnXC : IsNormalIn (X₁ ⊔ C) E := ⟨hXC_E, le_normalizer_sup hE₁ hEC⟩
  have hlt' : C < X₁ ⊔ C := by
    refine lt_of_le_of_ne le_sup_right fun h => ?_
    have hX₁C' : X₁ ≤ C := h ▸ le_sup_left
    rw [inf_eq_left.mpr hX₁C'] at hX₁C
    exact hlt.ne hX₁C.symm
  have hmax' : ∀ K : Subgroup G, IsNormalIn K E → C ≤ K → K ≤ X₁ ⊔ C →
      K = C ∨ K = X₁ ⊔ C := by
    intro K hK hCK hKX
    have hKX₁ : IsNormalIn (K ⊓ X₁) E :=
      ⟨inf_le_left.trans hK.1, le_normalizer_inf hK.2 hE₁⟩
    have hX₂KX : X₂ ≤ K ⊓ X₁ := le_inf (hX₂C.trans hCK) hX₂X₁
    rcases hmax _ hKX₁ hX₂KX inf_le_right with h | h
    · left
      refine le_antisymm (fun k hk => ?_) hCK
      obtain ⟨x, hx, c, hc', rfl⟩ := (mem_sup_iff_mul hCN₁).mp (hKX hk)
      have hxK : x ∈ K := by
        have := mul_mem hk (inv_mem (hCK hc'))
        simpa using this
      have : x ∈ X₂ := by
        rw [← h]
        exact Subgroup.mem_inf.mpr ⟨hxK, hx⟩
      exact mul_mem (hX₂C this) hc'
    · right
      exact le_antisymm hKX (sup_le (inf_eq_right.mp h) hCK)
  have hsc : secCenIn ((X₁ ⊔ C) ⊔ D) (X₁ ⊔ C) C = C := by
    rw [hXCD]
    refine le_antisymm (fun g hg => ?_) (fun c hc' => ?_)
    · obtain ⟨hgG, hgs⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨-, hgN, hgc⟩ := mem_sectionCentralizer_iff.mp hgs
      have hgE : g ∈ E := hG₁E hgG
      refine Subgroup.mem_inf.mpr ⟨hgG, mem_sectionCentralizer_iff.mpr
        ⟨hE₂ hgE, hE₁ hgE, fun y hy => ?_⟩⟩
      have h1 : ⁅g, y⁆ ∈ C := hgc y (Subgroup.mem_sup_left hy)
      have h2 : ⁅g, y⁆ ∈ X₁ := by
        have h3 := (Subgroup.mem_normalizer_iff.mp (hE₁ hgE) y).mp hy
        have e : ⁅g, y⁆ = (g * y * g⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact mul_mem h3 (inv_mem hy)
      rw [← hX₁C]
      exact Subgroup.mem_inf.mpr ⟨h2, h1⟩
    · have hcE : c ∈ E := hG₁E (hCE hc')
      refine Subgroup.mem_inf.mpr ⟨hCE hc', mem_sectionCentralizer_iff.mpr
        ⟨hEC hcE, le_normalizer_sup hE₁ hEC hcE, fun y hy => ?_⟩⟩
      have hyE : y ∈ E := hXC_E hy
      have h1 : y * c⁻¹ * y⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hEC hyE) c⁻¹).mp (inv_mem hc')
      have e : ⁅c, y⁆ = c * (y * c⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hc' h1
  have hadm : ∀ Z : Subgroup G, E ≤ Subgroup.normalizer (Z : Set G) → Admits (D ⊔ A) Z :=
    fun Z h => sup_le (hDE.trans h) (hAE.trans h)
  have hCX : C ≤ X := hCE.trans (sup_le hX₁ hX.2)
  have hX₁m : X₁ ∈ mhat p A θ := mem_mhat_of_le_mtil hθ.prime hX hX₁ (hadm X₁ hE₁)
  have hCm : C ∈ mhat p A θ := mem_mhat_of_le_mtil hθ.prime hX hCX (hadm C hEC)
  have hXCm : X₁ ⊔ C ∈ mhat p A θ :=
    mem_mhat_of_le_mtil hθ.prime hX (sup_le hX₁ hCX)
      (hadm _ (le_normalizer_sup hE₁ hEC))
  refine ⟨hXCm, hCm, ?_, ?_⟩
  · show IsChiefFactorOf ((X₁ ⊔ C) ⊔ D ⊔ A) (X₁ ⊔ C) C
    rw [hE']
    exact ⟨hnC, hnXC, hlt', hmax'⟩
  · show secCenIn ((X₁ ⊔ C) ⊔ D) (X₁ ⊔ C) C = C
    exact hsc

omit [Finite G] in
theorem isSolvable_of_isSolvableSection {X₁ X₂ : Subgroup G} (h₂₁ : X₂ ≤ X₁)
    (hnor : X₁ ≤ Subgroup.normalizer (X₂ : Set G)) (hsec : IsSolvableSection X₁ X₂)
    (hX₂ : Group.IsSolvable ↥X₂) : Group.IsSolvable ↥X₁ := by
  have : (X₂.subgroupOf X₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h₂₁).mpr hnor
  obtain ⟨n, hn⟩ := hsec
  have hq : Group.IsSolvable (↥X₁ ⧸ X₂.subgroupOf X₁) := by
    refine ⟨n, ?_⟩
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (X₂.subgroupOf X₁)) n]
    refine le_bot_iff.mp ?_
    calc (derivedSeries ↥X₁ n).map (QuotientGroup.mk' (X₂.subgroupOf X₁))
        ≤ (X₂.subgroupOf X₁).map (QuotientGroup.mk' (X₂.subgroupOf X₁)) :=
          Subgroup.map_mono hn
      _ = ⊥ := QuotientGroup.map_mk'_self _
  have hN : Group.IsSolvable ↥(X₂.subgroupOf X₁) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe h₂₁).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe h₂₁).injective
  exact Group.isSolvable_of_ker_le_range (X₂.subgroupOf X₁).subtype
    (QuotientGroup.mk' (X₂.subgroupOf X₁)) (by simp)

theorem exists_pair_le (hθ : NearFunctor p A θ) {X : Subgroup G} (hX : X ∈ mtil p A θ)
    (hns : ¬ Group.IsSolvable ↥X) : ∃ P ∈ pairsP p A θ, P.1 ≤ X := by
  set D := dsub A θ with hD
  let S : Set (Subgroup G) := {Z | Z ≤ X ∧ Admits (D ⊔ A) Z ∧ ¬ Group.IsSolvable ↥Z}
  have hXS : X ∈ S := ⟨le_rfl, sup_le (admits_dsub_of_le hX.2) hX.1.1, hns⟩
  obtain ⟨X₁, ⟨hX₁X, hX₁adm, hX₁ns⟩, hX₁min⟩ :=
    WellFounded.has_min (wellFounded_lt (α := Subgroup G)) S ⟨X, hXS⟩
  set E := X₁ ⊔ D ⊔ A with hE
  have hDAE : D ⊔ A ≤ E := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hX₁E : X₁ ≤ E := le_sup_left.trans le_sup_left
  have hE₁ : E ≤ Subgroup.normalizer (X₁ : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (le_sup_left.trans hX₁adm))
      (le_sup_right.trans hX₁adm)
  let N : Set (Subgroup G) := {K | IsNormalIn K E ∧ K < X₁}
  have hbot : (⊥ : Subgroup G) ∈ N := by
    refine ⟨⟨bot_le, fun g _ => Subgroup.mem_normalizer_iff.mpr fun h => ?_⟩, ?_⟩
    · simp only [Subgroup.mem_bot, mul_inv_eq_one, mul_eq_left]
    · refine bot_lt_iff_ne_bot.mpr fun h => hX₁ns ?_
      subst h
      infer_instance
  obtain ⟨X₂, ⟨hX₂n, hX₂lt⟩, hX₂max⟩ :=
    WellFounded.has_min (wellFounded_gt (α := Subgroup G)) N ⟨⊥, hbot⟩
  have hX₁n : IsNormalIn X₁ E := ⟨hX₁E, hE₁⟩
  have hc : IsChiefFactorOf E X₁ X₂ := by
    refine ⟨hX₂n, hX₁n, hX₂lt, fun K hK hX₂K hKX₁ => ?_⟩
    by_cases hlt : K < X₁
    · left
      exact (eq_of_le_of_not_lt hX₂K (hX₂max K ⟨hK, hlt⟩)).symm
    · right
      exact eq_of_le_of_not_lt hKX₁ hlt
  have hX₂sol : Group.IsSolvable ↥X₂ := by
    by_contra hns₂
    exact hX₁min X₂ ⟨hX₂lt.le.trans hX₁X, hDAE.trans hX₂n.2, hns₂⟩ hX₂lt
  have hsec : ¬ IsSolvableSection X₁ X₂ := fun h =>
    hX₁ns (isSolvable_of_isSolvableSection hX₂lt.le (hX₁E.trans hX₂n.2) h hX₂sol)
  refine ⟨_, pair_of_chief hθ hX hX₁X hc hsec, ?_⟩
  exact sup_le hX₁X (inf_le_left.trans (sup_le hX₁X hX.2))

omit [Finite G] in
theorem isSolvableSection_of_isSolvable_quotient {X₁ X₂ : Subgroup G}
    [(X₂.subgroupOf X₁).Normal] (h : Group.IsSolvable (↥X₁ ⧸ X₂.subgroupOf X₁)) :
    IsSolvableSection X₁ X₂ := by
  obtain ⟨⟨n, hn⟩⟩ := h
  refine ⟨n, fun x hx => ?_⟩
  have h1 := map_derivedSeries_eq (QuotientGroup.mk'_surjective (X₂.subgroupOf X₁)) n
  rw [hn] at h1
  have h2 : QuotientGroup.mk' (X₂.subgroupOf X₁) x ∈
      (derivedSeries ↥X₁ n).map (QuotientGroup.mk' (X₂.subgroupOf X₁)) := ⟨x, hx, rfl⟩
  rw [h1, Subgroup.mem_bot] at h2
  exact (QuotientGroup.eq_one_iff x).mp h2

omit [Finite G] in
theorem le_of_chief_of_isSolvable {E X₁ X₂ R : Subgroup G} (hc : IsChiefFactorOf E X₁ X₂)
    (hR : R ≤ X₁) (hRE : E ≤ Subgroup.normalizer (R : Set G)) (hRs : Group.IsSolvable ↥R)
    (hns : ¬ IsSolvableSection X₁ X₂) : R ≤ X₂ := by
  obtain ⟨hn₂, hn₁, hlt, hmax⟩ := hc
  have hX₁E : X₁ ≤ E := hn₁.1
  have hRM : IsNormalIn (R ⊔ X₂) E :=
    ⟨sup_le (hR.trans hX₁E) hn₂.1, le_normalizer_sup hRE hn₂.2⟩
  rcases hmax (R ⊔ X₂) hRM le_sup_right (sup_le hR hlt.le) with h | h
  · exact le_sup_left.trans h.le
  · exfalso
    have hnorm : (X₂.subgroupOf X₁).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hlt.le).mpr (hX₁E.trans hn₂.2)
    refine hns (isSolvableSection_of_isSolvable_quotient ?_)
    let φ : ↥R →* ↥X₁ ⧸ X₂.subgroupOf X₁ :=
      (QuotientGroup.mk' (X₂.subgroupOf X₁)).comp (Subgroup.inclusion hR)
    have hφ : Function.Surjective φ := by
      intro q
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (X₂.subgroupOf X₁) q
      have hx' : x ∈ R ⊔ X₂ := h ▸ hx
      obtain ⟨r, hr, m, hm, hrm⟩ := (mem_sup_iff_mul (hlt.le.trans (hX₁E.trans hRE))).mp hx'
      refine ⟨⟨r, hr⟩, ?_⟩
      show QuotientGroup.mk' (X₂.subgroupOf X₁) ⟨r, hR hr⟩ =
        QuotientGroup.mk' (X₂.subgroupOf X₁) ⟨x, hx⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simpa [hrm] using hm
    exact Group.isSolvable_of_surjective hφ

theorem exists_pair_perfRes (hθ : NearFunctor p A θ) {L : Subgroup G} (hL : L ∈ mtil p A θ)
    (hns : ¬ Group.IsSolvable ↥L) :
    ∃ M : Subgroup G, M < perfRes L ∧ IsNormalIn M (perfRes L ⊔ dsub A θ ⊔ A) ∧
      (perfRes L ⊔ secCenIn (perfRes L ⊔ dsub A θ) (perfRes L) M,
        secCenIn (perfRes L ⊔ dsub A θ) (perfRes L) M) ∈ pairsP p A θ ∧
      ∀ d ∈ dsub A θ, d ∈ sol L → d ∈ secCenIn (perfRes L ⊔ dsub A θ) (perfRes L) M := by
  set D := dsub A θ with hD
  set X₁ := perfRes L with hX₁
  set E := X₁ ⊔ D ⊔ A with hE
  have hX₁L : X₁ ≤ L := perfRes_le L
  have hLN : D ⊔ A ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (admits_dsub_of_le hL.2) hL.1.1
  have hDAX₁ : Admits (D ⊔ A) X₁ := admits_perfRes hLN
  have hDE : D ≤ E := le_sup_right.trans le_sup_left
  have hAE : A ≤ E := le_sup_right
  have hX₁E : X₁ ≤ E := le_sup_left.trans le_sup_left
  have hE₁ : E ≤ Subgroup.normalizer (X₁ : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (le_sup_left.trans hDAX₁))
      (le_sup_right.trans hDAX₁)
  have hX₁ne : X₁ ≠ ⊥ := fun h => hns ((perfRes_eq_bot_iff L).mp h)
  let N : Set (Subgroup G) := {K | IsNormalIn K E ∧ K < X₁}
  have hbot : (⊥ : Subgroup G) ∈ N := by
    refine ⟨⟨bot_le, fun g _ => Subgroup.mem_normalizer_iff.mpr fun h => ?_⟩,
      bot_lt_iff_ne_bot.mpr hX₁ne⟩
    simp only [Subgroup.mem_bot, mul_inv_eq_one, mul_eq_left]
  obtain ⟨M, ⟨hMn, hMlt⟩, hMmax⟩ :=
    WellFounded.has_min (wellFounded_gt (α := Subgroup G)) N ⟨⊥, hbot⟩
  have hX₁n : IsNormalIn X₁ E := ⟨hX₁E, hE₁⟩
  have hc : IsChiefFactorOf E X₁ M := by
    refine ⟨hMn, hX₁n, hMlt, fun K hK hMK hKX₁ => ?_⟩
    by_cases hlt : K < X₁
    · left
      exact (eq_of_le_of_not_lt hMK (hMmax K ⟨hK, hlt⟩)).symm
    · right
      exact eq_of_le_of_not_lt hKX₁ hlt
  have hperf : Group.IsPerfect ↥X₁ := isPerfect_perfRes L
  have hns' : ¬ IsSolvableSection X₁ M := by
    rintro ⟨n, hn⟩
    have := hperf
    rw [Group.IsPerfect.derivedSeries_eq_top (↥X₁) n] at hn
    refine hMlt.not_ge fun x hx => ?_
    have := hn (Subgroup.mem_top (⟨x, hx⟩ : ↥X₁))
    exact this
  have hEsol : E ≤ Subgroup.normalizer (sol L : Set G) :=
    sup_le (sup_le (hX₁L.trans (Nonsolv.SolQuot.le_nrm_sol L))
      (hL.2.trans (Nonsolv.SolQuot.le_nrm_sol L)))
      (hL.1.1.trans (Nonsolv.SolQuot.normalizer_le_nrm_sol L))
  refine ⟨M, hMlt, hMn, pair_of_chief hθ hL hX₁L hc hns', fun d hdD hdsol => ?_⟩
  have hdE : d ∈ E := hDE hdD
  have hsolL : Group.IsSolvable ↥(sol L) := isSolvable_sol L
  have hRs : Group.IsSolvable ↥(sol L ⊓ X₁) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : sol L ⊓ X₁ ≤ sol L))
      (Subgroup.inclusion_injective _)
  have hRM : sol L ⊓ X₁ ≤ M :=
    le_of_chief_of_isSolvable hc inf_le_right (le_normalizer_inf hEsol hE₁) hRs hns'
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hdD, mem_sectionCentralizer_iff.mpr
    ⟨hMn.2 hdE, hE₁ hdE, fun y hy => ?_⟩⟩
  have h1 : ⁅d, y⁆ ∈ sol L := by
    have hyL : y ∈ L := hX₁L hy
    have hy' : y * d⁻¹ * y⁻¹ ∈ sol L :=
      (Subgroup.mem_normalizer_iff.mp (Nonsolv.SolQuot.le_nrm_sol L hyL) d⁻¹).mp (inv_mem hdsol)
    have e : ⁅d, y⁆ = d * (y * d⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hdsol hy'
  have h2 : ⁅d, y⁆ ∈ X₁ := by
    have h3 := (Subgroup.mem_normalizer_iff.mp (hE₁ hdE) y).mp hy
    have e : ⁅d, y⁆ = (d * y * d⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact mul_mem h3 (inv_mem hy)
  exact hRM (Subgroup.mem_inf.mpr ⟨h1, h2⟩)

end Pairs

end Thm53A

end CFSG.SignalizerFunctorTheorem.McBride.Near
