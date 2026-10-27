module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iGen
public import CFSG.RankThree.PartTwo.Sec21.Hering233iAct
public import CFSG.RankThree.PartTwo.Sec21.Hering233iE16
import CFSG.RankThree.PartTwo.Sec21.Item229Pre

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

theorem false_of_exceptional_q {G : Type} [Group G] [Finite G]
    (hlocal : ∀ q : ℕ, q.Prime → 3 < q → localRank q G < 3) {L : Subgroup G}
    [Group.IsPerfect L] {K₀ : Subgroup L} [K₀.Normal] [IsSimpleGroup (L ⧸ K₀)]
    (hK₀ : Group.IsSolvable K₀) (hO2 : CFSG.pCore 2 L = ⊥)
    (hO3 : CFSG.pCore 3 L ≤ Subgroup.center L) {A B : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hAe : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hBA : B ≤ A) (hB3 : Nat.card B = 3)
    (hBL : ∀ b ∈ B, ∀ x ∈ L, b * x = x * b) {X : Subgroup G} (hXL : X ≤ L)
    [IsSimpleGroup X] (hXnc : ∃ x ∈ X, ∃ y ∈ X, x * y ≠ y * x)
    {w : G} (hXw : ∀ x ∈ X, x * w = w * x) (hw2 : orderOf w = 2)
    {a r₁ r₂ r₃ : G} (haX : a ∈ X) (ha1 : a ≠ 1)
    (hcover : ∀ h ∈ A, h ∉ B → ∃ i : Fin 4, ![a, r₁, r₂, r₃] i ∈ B ⊔ Subgroup.zpowers h)
    (h₁ : ∀ q : ℕ, q.Prime → 3 < q → ∀ d ∈ L, (∃ k : ℕ, d ^ q ^ k = 1) → d * r₁ = r₁ * d →
      d * w = w * d)
    (h₂ : ∀ q : ℕ, q.Prime → 3 < q → ∀ d ∈ L, (∃ k : ℕ, d ^ q ^ k = 1) → d * r₂ = r₂ * d →
      d * w = w * d)
    (h₃ : ∀ q : ℕ, q.Prime → 3 < q → ∀ d ∈ L, (∃ k : ℕ, d ^ q ^ k = 1) → d * r₃ = r₃ * d →
      d * w = w * d)
    (q : ℕ) (hq : q.Prime) (hpS : Subgroup.centralizer (CFSG.pCore q L : Set L) ≤ K₀) :
    False := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hK₀top : K₀ ≠ ⊤ := QuotientGroup.nontrivial_iff.mp inferInstance
  have hctop : ∀ N : Subgroup L, N ≤ Subgroup.center L →
      ¬ Subgroup.centralizer (N : Set L) ≤ K₀ := by
    intro N hN hle
    rw [Subgroup.centralizer_eq_top_iff_subset.mpr hN, top_le_iff] at hle
    exact hK₀top hle
  have hne : CFSG.pCore q L ≠ ⊥ := by
    intro h
    rw [h] at hpS
    exact hctop ⊥ bot_le hpS
  have hp2 : q ≠ 2 := by
    rintro rfl
    exact hne hO2
  have hp3 : 3 < q := by
    have hp3' : q ≠ 3 := by
      rintro rfl
      exact hctop _ hO3 hpS
    have := hq.two_le
    omega
  obtain ⟨D, hD, hDinv⟩ := exists_criticalAt_invariant hp2 hne
  set DG : Subgroup G := D.map L.subtype with hDG
  have hDGp : IsPGroup q DG := (CFSG.pCore_isPGroup.to_le hD.le : IsPGroup q D).map L.subtype
  have hDGL : DG ≤ L := Subgroup.map_subtype_le D
  have hAD : A ≤ Subgroup.normalizer (DG : Set G) := fun e he =>
    mem_normalizer_map_subtype_of_invariant hDinv (hAL he)
  have hXD : X ≤ Subgroup.normalizer (DG : Set G) := fun x hx =>
    mem_normalizer_map_subtype_of_invariant hDinv (Subgroup.le_normalizer (hXL hx))
  have hBD : ∀ b ∈ B, ∀ d ∈ DG, b * d = d * b := fun b hb d hd => hBL b hb d (hDGL hd)
  have h3 : ¬ 3 ∣ Nat.card DG := by
    obtain ⟨k, hk⟩ := hDGp.exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hqe : ∀ d ∈ DG, ∃ k : ℕ, d ^ q ^ k = 1 := by
    intro d hd
    obtain ⟨k, hk⟩ := hDGp ⟨d, hd⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hgen := le_iSup_inf_centralizer_of_cover hAD hAe hA27 hBA hB3 hBD h3
    ![a, r₁, r₂, r₃] hcover
  set D₁ : Subgroup G := DG ⊓ Subgroup.centralizer ({w} : Set G) with hD₁
  have hsub : ∀ (r : G), (∀ d ∈ L, (∃ k : ℕ, d ^ q ^ k = 1) → d * r = r * d →
      d * w = w * d) → DG ⊓ Subgroup.centralizer ({r} : Set G) ≤ D₁ := by
    intro r hr d hd
    obtain ⟨hdD, hdr⟩ := Subgroup.mem_inf.mp hd
    exact Subgroup.mem_inf.mpr ⟨hdD, Subgroup.mem_centralizer_singleton_iff.mpr
      (hr d (hDGL hdD) (hqe d hdD) (Subgroup.mem_centralizer_singleton_iff.mp hdr))⟩
  have hDsup : DG ≤ (DG ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ D₁ := by
    refine hgen.trans (iSup_le fun i => ?_)
    fin_cases i
    · exact le_sup_left
    · exact (hsub r₁ (h₁ q hq hp3)).trans le_sup_right
    · exact (hsub r₂ (h₂ q hq hp3)).trans le_sup_right
    · exact (hsub r₃ (h₃ q hq hp3)).trans le_sup_right
  have hD₁p : IsPGroup q D₁ := hDGp.to_le inf_le_left
  have hD₁p : IsPGroup q D₁ := hDGp.to_le inf_le_left
  have hDGexp : ∀ x ∈ DG, x ^ q = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hD.exp x hx, map_one]
  have hDGcl : ∀ a ∈ DG, ∀ b ∈ DG, ∀ c ∈ DG, ⁅a, b⁆ * c = c * ⁅a, b⁆ := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    have := (hD.comm a ha b (hD.le hb)).2 c hc
    rw [← map_commutatorElement, ← map_mul, ← map_mul, this]
  have hD₁G : ∀ x ∈ D₁, x ∈ DG := fun x hx => (Subgroup.mem_inf.mp hx).1
  have hD₁C : ∀ x ∈ D₁, x * w = w * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  have hexp : ∀ x : D₁, x ^ q = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDGexp x (hD₁G x x.2), Subgroup.coe_one])
  have hclass : commutator D₁ ≤ Subgroup.center D₁ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    have := hDGcl a (hD₁G a a.2) b (hD₁G b b.2) c (hD₁G c c.2)
    simp only [commutatorElement_def] at this ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact this.symm
  have hrank : CFSG.pRank q D₁ ≤ 2 := by
    have h1 : CFSG.pRank q D₁ ≤ localRank q G :=
      pRank_le_localRank_of_centralizes hq hp2 hw2
        (fun h hh => hD₁C h hh)
    have h2 := hlocal q hq hp3
    omega
  have hXD₁ : X ≤ Subgroup.normalizer (D₁ : Set G) := by
    have key : ∀ x ∈ X, ∀ h ∈ D₁, x * h * x⁻¹ ∈ D₁ := by
      intro x hx h hh
      obtain ⟨hhD, hhC⟩ := Subgroup.mem_inf.mp hh
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hXD hx) h).mp hhD,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hxy : x * w = w * x := hXw x hx
      have hyx' : w * x⁻¹ = x⁻¹ * w := by
        calc w * x⁻¹ = x⁻¹ * (x * w) * x⁻¹ := by group
          _ = x⁻¹ * (w * x) * x⁻¹ := by rw [hxy]
          _ = x⁻¹ * w := by group
      have hhy : h * w = w * h := Subgroup.mem_centralizer_singleton_iff.mp hhC
      calc (x * h * x⁻¹) * w = x * h * (x⁻¹ * w) := by group
        _ = x * h * (w * x⁻¹) := by rw [hyx']
        _ = x * (h * w) * x⁻¹ := by group
        _ = x * (w * h) * x⁻¹ := by rw [hhy]
        _ = (x * w) * h * x⁻¹ := by group
        _ = (w * x) * h * x⁻¹ := by rw [hxy]
        _ = w * (x * h * x⁻¹) := by group
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key x hx h, fun h' => ?_⟩
    have := key x⁻¹ (X.inv_mem hx) _ h'
    simpa [mul_assoc] using this
  let ρ : ↥X →* MulAut ↥D₁ := D₁.normalizerMonoidHom.comp (Subgroup.inclusion hXD₁)
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := hXnc
  have hρ : ρ = 1 := acts_trivially_of_rank_le_two
    ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩, fun h => hxy₀ (congrArg Subtype.val h)⟩ hp2 hD₁p hexp hclass hrank ρ
  have hXD₁c : ∀ x ∈ X, ∀ d ∈ D₁, x * d = d * x := by
    intro x hx d hd
    have h0 : ρ ⟨x, hx⟩ = 1 := by rw [hρ]; rfl
    have h1 := congrArg (fun f : MulAut D₁ => ((f ⟨d, hd⟩ : D₁) : G)) h0
    have h2 : x * d * x⁻¹ = d := h1
    calc x * d = x * d * x⁻¹ * x := by group
      _ = d * x := by rw [h2]
  have haDG : ∀ d ∈ DG, a * d = d * a := by
    have hle : (DG ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ D₁ ≤
        Subgroup.centralizer ({a} : Set G) :=
      sup_le inf_le_right fun d hd =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hXD₁c a haX d hd).symm
    intro d hd
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (hDsup hd))).symm
  have hXcent : ∀ x ∈ X, ∀ d ∈ DG, x * d = d * x := by
    set C : Subgroup G := Subgroup.centralizer (DG : Set G) with hC
    have hXC : X ≤ Subgroup.normalizer (C : Set G) := by
      have key : ∀ x ∈ X, ∀ y ∈ C, x * y * x⁻¹ ∈ C := by
        intro x hx y hy
        rw [hC, Subgroup.mem_centralizer_iff] at hy ⊢
        intro d hd
        have hd' : x⁻¹ * d * x ∈ DG := by
          have := (Subgroup.mem_normalizer_iff.mp (hXD (X.inv_mem hx)) d).mp hd
          simpa using this
        have h1 := hy _ hd'
        calc d * (x * y * x⁻¹) = x * ((x⁻¹ * d * x) * y) * x⁻¹ := by group
          _ = x * (y * (x⁻¹ * d * x)) * x⁻¹ := by rw [h1]
          _ = (x * y * x⁻¹) * d := by group
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨key x hx y, fun hy => ?_⟩
      have := key x⁻¹ (X.inv_mem hx) _ hy
      simpa [mul_assoc] using this
    haveI : (C.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXC
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.subgroupOf X) with h | h
    · exfalso
      have : (⟨a, haX⟩ : X) ∈ C.subgroupOf X :=
        Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_centralizer_iff.mpr fun d hd => (haDG d hd).symm)
      rw [h, Subgroup.mem_bot] at this
      exact ha1 (congrArg Subtype.val this)
    · intro x hx d hd
      have : (⟨x, hx⟩ : X) ∈ C.subgroupOf X := by rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp this) d hd).symm
  have hXK₀ : X.subgroupOf L ≤ K₀ := by
    have hC := hD.centralizer_le hK₀ hpS
    intro x hx
    apply hC
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    apply Subtype.ext
    exact (hXcent x (Subgroup.mem_subgroupOf.mp hx) (d : G) ⟨d, hd, rfl⟩).symm
  have hXsol : Group.IsSolvable X := by
    have h1 : Group.IsSolvable (X.subgroupOf L) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXK₀)
        (Subgroup.inclusion_injective hXK₀)
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hXL).toMonoidHom)
      (MulEquiv.surjective _)
  have hXperf : Group.IsPerfect X :=
    isPerfect_of_isSimpleGroup ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩, fun h => hxy₀ (congrArg Subtype.val h)⟩
  have : Nontrivial X := IsSimpleGroup.toNontrivial
  exact Group.IsPerfect.not_isSolvable X hXsol

end CFSG.RankThree.PartTwo.Sec21.Hering233i
