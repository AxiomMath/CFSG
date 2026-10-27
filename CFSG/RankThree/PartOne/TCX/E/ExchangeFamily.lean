module

public import CFSG.RankThree.PartOne.KE.TwoA2Exchange
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.E

open Matrix CFSG.RankThree.PartOne.KE CFSG.Assembly.LowTwoRank
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups Pointwise commutatorElement

section Exchange

variable {τ : Tag} {L : Type} [Field L]

theorem two_family_exchange' 
    (Fr : L →+* L) (n : ModGL τ L)
    {S₁ S₂ : Set (Fin τ.rank → ℤ)} (hS₁ : ∀ r ∈ S₁, IsRoot τ r) (hS₂ : ∀ r ∈ S₂, IsRoot τ r)
    (hT₁₂ : ∀ x ∈ rootSpan τ L S₁,
      n * Units.map (entrywiseHom Fr) x * n⁻¹ ∈ rootSpan τ L S₂)
    (hT₂₁ : ∀ x ∈ rootSpan τ L S₂,
      n * Units.map (entrywiseHom Fr) x * n⁻¹ ∈ rootSpan τ L S₁)
    (hcomm : ∀ x ∈ rootSpan τ L S₁, ∀ y ∈ rootSpan τ L S₂, x * y = y * x)
    (n₂ : ModGL τ L) (Φ₂ : ModGL τ L →* ModGL τ L)
    (hT2 : ∀ x, n₂ * Φ₂ x * n₂⁻¹ = n * Units.map (entrywiseHom Fr)
      (n * Units.map (entrywiseHom Fr) x * n⁻¹) * n⁻¹)
    (hfin : Finite ↥(rootSpan τ L S₁ ⊓ twistedFixedPoints n₂ Φ₂))
    (hq : CFSG.IsQuasisimple ↥(rootSpan τ L S₁ ⊓ twistedFixedPoints n₂ Φ₂))
    (hc₁ : ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S₁,
      (∀ u ∈ rootSpan τ L S₁ ⊓ twistedFixedPoints n₂ Φ₂, y * u = u * y) →
        y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer (rootSpan τ L S₁ : Set (ModGL τ L)))
    (hc₂ : ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S₂,
      (∀ u ∈ rootSpan τ L S₂ ⊓ twistedFixedPoints n₂ Φ₂, y * u = u * y) →
        y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer (rootSpan τ L S₂ : Set (ModGL τ L))) :
    ∃ P : Subgroup (ModGL τ L), IsSigmaFamily n Fr (S₁ ∪ S₂) (fun _ : Unit => P) ∧
      ∀ x, x ∈ P ↔ ∃ g ∈ rootSpan τ L S₁ ⊓ twistedFixedPoints n₂ Φ₂,
        x = g * (n * Units.map (entrywiseHom Fr) g * n⁻¹) := by
  classical
  set Φ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hΦ
  set Tf : ModGL τ L → ModGL τ L := fun x => n * Φ x * n⁻¹ with hTf
  have hTmul : ∀ x y, Tf (x * y) = Tf x * Tf y := fun x y => by
    simp only [hTf, map_mul]
    group
  have hTinv : ∀ x, Tf x⁻¹ = (Tf x)⁻¹ := fun x => by
    simp only [hTf, map_inv]
    group
  have hT1 : Tf 1 = 1 := by simp [hTf]
  set Q₁ := rootSpan τ L S₁ with hQ₁
  set Q₂ := rootSpan τ L S₂ with hQ₂
  set H := torusGroup τ L with hH
  set P₁ : Subgroup (ModGL τ L) := Q₁ ⊓ twistedFixedPoints n₂ Φ₂ with hP₁def
  have hS₁₂ : ∀ r ∈ S₁ ∪ S₂, IsRoot τ r := fun r hr => by
    rcases hr with hr | hr
    · exact hS₁ r hr
    · exact hS₂ r hr
  have hP₁Q : ∀ g ∈ P₁, g ∈ Q₁ := fun g hg => hg.1
  have hP₁T : ∀ g ∈ P₁, Tf (Tf g) = g := fun g hg => by
    have h := mem_twistedFixedPoints.1 hg.2
    rw [hT2 g] at h
    exact h
  have hP₁of : ∀ g ∈ Q₁, Tf (Tf g) = g → g ∈ P₁ := fun g hg h =>
    Subgroup.mem_inf.2 ⟨hg, mem_twistedFixedPoints.2 (by rw [hT2 g]; exact h)⟩
  have hcom21 : ∀ x ∈ Q₂, ∀ y ∈ Q₁, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hN₁H : H ≤ Subgroup.normalizer (Q₁ : Set (ModGL τ L)) :=
    KE.torusGroup_le_normalizer_rootSpan hS₁
  have hN₂H : H ≤ Subgroup.normalizer (Q₂ : Set (ModGL τ L)) :=
    KE.torusGroup_le_normalizer_rootSpan hS₂
  have hQ₂N₁ : Q₂ ≤ Subgroup.normalizer (Q₁ : Set (ModGL τ L)) := fun x hx =>
    mem_normalizer_of_forall_commute fun k hk => hcom21 x hx k hk
  have hQ₁N₂ : Q₁ ≤ Subgroup.normalizer (Q₂ : Set (ModGL τ L)) := fun x hx =>
    mem_normalizer_of_forall_commute fun k hk => hcomm x hx k hk
  have hN₁ : H ⊔ rootSpan τ L (S₁ ∪ S₂) ≤ Subgroup.normalizer (Q₁ : Set (ModGL τ L)) := by
    rw [rootSpan_union_eq]
    exact sup_le hN₁H (sup_le Subgroup.le_normalizer hQ₂N₁)
  have hN₂ : H ⊔ rootSpan τ L (S₁ ∪ S₂) ≤ Subgroup.normalizer (Q₂ : Set (ModGL τ L)) := by
    rw [rootSpan_union_eq]
    exact sup_le hN₂H (sup_le hQ₁N₂ Subgroup.le_normalizer)
  have hprod : ∀ g ∈ P₁, ∀ h ∈ P₁, (g * h) * Tf (g * h) = (g * Tf g) * (h * Tf h) := by
    intro g hg h hh
    have hc := hcomm h (hP₁Q h hh) (Tf g) (hT₁₂ g (hP₁Q g hg))
    rw [hTmul]
    calc g * h * (Tf g * Tf h) = g * (h * Tf g) * Tf h := by group
      _ = g * (Tf g * h) * Tf h := by rw [hc]
      _ = g * Tf g * (h * Tf h) := by group
  have hcomgT : ∀ g ∈ P₁, g * Tf g = Tf g * g := fun g hg =>
    hcomm g (hP₁Q g hg) (Tf g) (hT₁₂ g (hP₁Q g hg))
  let P : Subgroup (ModGL τ L) :=
    { carrier := {x | ∃ g ∈ P₁, x = g * Tf g}
      mul_mem' := by
        rintro _ _ ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
        exact ⟨g * h, mul_mem hg hh, (hprod g hg h hh).symm⟩
      one_mem' := ⟨1, one_mem _, by simp [hT1]⟩
      inv_mem' := by
        rintro _ ⟨g, hg, rfl⟩
        refine ⟨g⁻¹, inv_mem hg, ?_⟩
        rw [hTinv, hcomgT g hg, _root_.mul_inv_rev] }
  have hPmem : ∀ x, x ∈ P ↔ ∃ g ∈ P₁, x = g * Tf g := fun x => Iff.rfl
  have hPT : ∀ g ∈ P₁, Tf (g * Tf g) = g * Tf g := fun g hg => by
    rw [hTmul, hP₁T g hg, ← hcomgT g hg]
  let φ : P₁ →* P :=
    { toFun := fun g => ⟨(g : ModGL τ L) * Tf g, g, g.2, rfl⟩
      map_one' := Subtype.ext (by simp [hT1])
      map_mul' := fun g h => Subtype.ext (hprod g g.2 h h.2) }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  have hPfin : Finite P := Finite.of_surjective φ hφs
  have hφ1 : ∃ k, φ k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hab : ∀ a b : P₁, a * b = b * a := by
      intro a b
      have h1 : (a : ModGL τ L) * Tf a = 1 := congrArg Subtype.val (hcon a)
      have hmemQ₂ : (a : ModGL τ L) ∈ Q₂ := by
        have : (a : ModGL τ L) = (Tf a)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact inv_mem (hT₁₂ a (hP₁Q a a.2))
      apply Subtype.ext
      exact (hcomm b (hP₁Q b b.2) a hmemQ₂).symm
    obtain ⟨-, -, a, b, hab'⟩ := hq
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab a' b']
  have hPq : CFSG.IsQuasisimple P :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hφs hφ1
  refine ⟨P, ?_, fun x => Iff.rfl⟩
  unfold IsSigmaFamily
  refine ⟨fun _ => hPfin, fun _ => hPq, fun _ => ?_, fun _ => ?_, fun _ => ?_,
    fun _ y hy hyR u hu => ?_, fun y hy hyR hcomm' => ?_⟩
  ·
    rintro _ ⟨g, hg, rfl⟩
    have h1 : g ∈ rootSpan τ L (S₁ ∪ S₂) :=
      rootSpan_mono Set.subset_union_left (hP₁Q g hg)
    have h2 : Tf g ∈ rootSpan τ L (S₁ ∪ S₂) :=
      rootSpan_mono Set.subset_union_right (hT₁₂ g (hP₁Q g hg))
    exact mul_mem h1 h2
  ·
    rintro _ ⟨g, hg, rfl⟩
    exact mem_twistedFixedPoints.2 (hPT g hg)
  ·
    rintro _ ⟨g, hg, rfl⟩
    exact mul_mem (rootSpan_le_adjointGroup L S₁ (hP₁Q g hg))
      (rootSpan_le_adjointGroup L S₂ (hT₁₂ g (hP₁Q g hg)))
  ·
    obtain ⟨g, hg, rfl⟩ := hu
    have hTy : Tf y = y := mem_twistedFixedPoints.1 hyR
    have hg' : y * g * y⁻¹ ∈ P₁ := by
      have hQ : y * g * y⁻¹ ∈ Q₁ := (Subgroup.mem_normalizer_iff.1 (hN₁ hy) g).1 (hP₁Q g hg)
      refine hP₁of _ hQ ?_
      have e1 : Tf (y * g * y⁻¹) = y * Tf g * y⁻¹ := by
        rw [hTmul, hTmul, hTinv, hTy]
      rw [e1, hTmul, hTmul, hTinv, hTy, hP₁T g hg]
    refine ⟨y * g * y⁻¹, hg', ?_⟩
    have e1 : Tf (y * g * y⁻¹) = y * Tf g * y⁻¹ := by
      rw [hTmul, hTmul, hTinv, hTy]
    rw [e1]
    group
  ·
    have hTy : Tf y = y := mem_twistedFixedPoints.1 hyR
    have hcP : ∀ g ∈ P₁, y * (g * Tf g) = (g * Tf g) * y := fun g hg =>
      hcomm' () _ ⟨g, hg, rfl⟩
    have hSS : H ≤ Subgroup.normalizer (rootSpan τ L (S₁ ∪ S₂) : Set (ModGL τ L)) :=
      KE.torusGroup_le_normalizer_rootSpan hS₁₂
    have e := Subgroup.coe_mul_of_left_le_normalizer_right H (rootSpan τ L (S₁ ∪ S₂)) hSS
    have hy' : y ∈ ((H ⊔ rootSpan τ L (S₁ ∪ S₂) : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := hy
    rw [e] at hy'
    obtain ⟨t, ht, q, hq', hyeq⟩ := hy'
    have hq'' : q ∈ ((Q₁ ⊔ Q₂ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
      rw [← rootSpan_union_eq]
      exact hq'
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Q₁ Q₂ hQ₁N₂] at hq''
    obtain ⟨q₁, hq₁, q₂, hq₂, hqeq⟩ := hq''
    set a : ModGL τ L := t * q₁ with ha
    have hyeq' : y = a * q₂ := by
      rw [← hyeq, ← hqeq, ha]
      group
    have haN₁ : a ∈ Subgroup.normalizer (Q₁ : Set (ModGL τ L)) :=
      mul_mem (hN₁H ht) (Subgroup.le_normalizer hq₁)
    have hya : ∀ g ∈ Q₁, y * g * y⁻¹ = a * g * a⁻¹ := by
      intro g hg
      rw [hyeq']
      have e1 : q₂ * g = g * q₂ := hcom21 q₂ hq₂ g hg
      calc a * q₂ * g * (a * q₂)⁻¹ = a * (q₂ * g) * q₂⁻¹ * a⁻¹ := by group
        _ = a * (g * q₂) * q₂⁻¹ * a⁻¹ := by rw [e1]
        _ = a * g * a⁻¹ := by group
    have hζ2 : ∀ g ∈ P₁, a * g * a⁻¹ * g⁻¹ ∈ Q₂ := by
      intro g hg
      have hgQ := hP₁Q g hg
      have hb : y * Tf g * y⁻¹ ∈ Q₂ :=
        (Subgroup.mem_normalizer_iff.1 (hN₂ hy) (Tf g)).1 (hT₁₂ g hgQ)
      have hmain : (a * g * a⁻¹) * (y * Tf g * y⁻¹) = g * Tf g := by
        have h1 := hcP g hg
        calc (a * g * a⁻¹) * (y * Tf g * y⁻¹)
            = (y * g * y⁻¹) * (y * Tf g * y⁻¹) := by rw [hya g hgQ]
          _ = y * (g * Tf g) * y⁻¹ := by group
          _ = g * Tf g := by rw [h1]; group
      have hX : a * g * a⁻¹ = g * Tf g * (y * Tf g * y⁻¹)⁻¹ := eq_mul_inv_of_mul_eq hmain
      have hw : Tf g * (y * Tf g * y⁻¹)⁻¹ ∈ Q₂ := mul_mem (hT₁₂ g hgQ) (inv_mem hb)
      have hgw : g * (Tf g * (y * Tf g * y⁻¹)⁻¹) * g⁻¹ = Tf g * (y * Tf g * y⁻¹)⁻¹ := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hcomm g hgQ _ hw
      rw [hX]
      have e2 : g * Tf g * (y * Tf g * y⁻¹)⁻¹ * g⁻¹ =
          g * (Tf g * (y * Tf g * y⁻¹)⁻¹) * g⁻¹ := by group
      rw [e2, hgw]
      exact hw
    have hacomm : ∀ g ∈ P₁, a * g = g * a := by
      refine centralizes_of_discrepancy_central (Q := Q₁) (P₁ := P₁)
        (fun g hg => hP₁Q g hg) hq.1 a
        (fun g hg => (Subgroup.mem_normalizer_iff.1 haN₁ g).1 (hP₁Q g hg)) ?_
      intro g hg x hx
      exact (hcomm x hx _ (hζ2 g hg)).symm
    have haHQ : a ∈ H ⊔ Q₁ :=
      mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hq₁)
    obtain ⟨haH, haC⟩ := hc₁ a haHQ (fun u hu => hacomm u hu)
    have hyQ₂ : y ∈ H ∧ y ∈ Subgroup.centralizer (Q₂ : Set (ModGL τ L)) := by
      refine hc₂ y ?_ ?_
      · rw [hyeq']
        exact mul_mem (Subgroup.mem_sup_left haH) (Subgroup.mem_sup_right hq₂)
      · intro u hu
        have hu2Q : u ∈ Q₂ := hu.1
        have hu2T : Tf (Tf u) = u := by
          have h := mem_twistedFixedPoints.1 hu.2
          rw [hT2 u] at h
          exact h
        have hgQ : Tf u ∈ Q₁ := hT₂₁ u hu2Q
        have hgP : Tf u ∈ P₁ := hP₁of (Tf u) hgQ (by rw [hu2T])
        have h1 := hcP (Tf u) hgP
        rw [hu2T] at h1
        have h2 : y * Tf u * y⁻¹ = Tf u := by
          rw [hya (Tf u) hgQ, mul_inv_eq_iff_eq_mul]
          exact (Subgroup.mem_centralizer_iff.1 haC (Tf u) hgQ).symm
        have h3 : Tf u * (y * u * y⁻¹) = Tf u * u := by
          calc Tf u * (y * u * y⁻¹) = (y * Tf u * y⁻¹) * (y * u * y⁻¹) := by rw [h2]
            _ = y * (Tf u * u) * y⁻¹ := by group
            _ = Tf u * u := by rw [h1]; group
        have h4 : y * u * y⁻¹ = u := mul_left_cancel h3
        exact mul_inv_eq_iff_eq_mul.1 h4
    have hycent : y ∈ Subgroup.centralizer (rootSpan τ L (S₁ ∪ S₂) : Set (ModGL τ L)) := by
      have hle : rootSpan τ L (S₁ ∪ S₂) ≤ Subgroup.centralizer ({y} : Set (ModGL τ L)) := by
        rw [rootSpan_union_eq]
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff, hyeq']
          have hax : x * a = a * x := Subgroup.mem_centralizer_iff.1 haC x hx
          have hqx : q₂ * x = x * q₂ := hcom21 q₂ hq₂ x hx
          symm
          calc a * q₂ * x = a * (q₂ * x) := by group
            _ = a * (x * q₂) := by rw [hqx]
            _ = (a * x) * q₂ := by group
            _ = (x * a) * q₂ := by rw [hax]
            _ = x * (a * q₂) := by group
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.1 hyQ₂.2 x hx
      exact Subgroup.mem_centralizer_iff.2 fun h hh =>
        Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
    exact Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hyQ₂.1, hTy⟩, hycent⟩

end Exchange

end CFSG.RankThree.PartOne.TCX.E
