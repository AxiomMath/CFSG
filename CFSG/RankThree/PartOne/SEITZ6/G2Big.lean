module

public import CFSG.RankThree.PartOne.SEITZ6.G2Pair
public import CFSG.RankThree.PartOne.SEITZ6.G2Entry
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3

variable {K : Type} [Field K]

theorem map_conj_eq_self {G : Type*} [Group G] {R : Subgroup G} {g : G} (hg : g ∈ R) :
    R.map (MulAut.conj g).toMonoidHom = R := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact R.mul_mem (R.mul_mem hg hy) (R.inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, R.mul_mem (R.mul_mem (R.inv_mem hg) hx) hg, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

section Rational


theorem xp_entrywise_fixed (σ : K ≃+* K) {p : ℕ} (hp : p < 12) {c : K} (hc : σ c = c) :
    Units.map (entrywiseHom σ.toRingHom) ((xp p c : adjointGroup .G2 K) : ModGL .G2 K) =
      ((xp p c : adjointGroup .G2 K) : ModGL .G2 K) := by
  have hγ : IsRoot .G2 (rt p) := isRoot_rt hp
  refine Units.ext ?_
  rw [Units.coe_map]
  have hxp : (((xp p c : adjointGroup .G2 K) : ModGL .G2 K) : Module.End K (RootModule .G2 K)) =
      (rootOperatorFamily .G2).elt K ⟨rt p, hγ⟩ c := by
    simp only [xp, xPar_of_isRoot hγ]
    rfl
  rw [hxp]
  have hb : BaseChange σ.toRingHom ((rootOperatorFamily .G2).elt K ⟨rt p, hγ⟩ c)
      ((rootOperatorFamily .G2).elt K ⟨rt p, hγ⟩ (σ.toRingHom c)) :=
    BaseChange.elt (rootOperatorFamily .G2) _ c
  have he : BaseChange σ.toRingHom ((rootOperatorFamily .G2).elt K ⟨rt p, hγ⟩ c)
      (entrywise σ.toRingHom ((rootOperatorFamily .G2).elt K ⟨rt p, hγ⟩ c)) :=
    fun b => (entrywise_single σ.toRingHom _ b).symm
  have h := he.unique hb
  change entrywise σ.toRingHom _ = _
  rw [h]
  have : σ.toRingHom c = c := hc
  rw [this]

theorem entriesIn_entrywise_fixed (σ : K ≃+* K) {g : adjointGroup .G2 K}
    (hg : EntriesIn (fixSubfield σ) g) :
    Units.map (entrywiseHom σ.toRingHom) (g : ModGL .G2 K) = (g : ModGL .G2 K) := by
  refine Units.ext ?_
  rw [Units.coe_map]
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  change entrywise σ.toRingHom _ (Finsupp.single b 1) = _
  rw [entrywise_single]
  ext a
  rw [Finsupp.mapRange_apply]
  exact (mem_fixSubfield σ).1 (hg b a)

theorem mem_rat_of_entrywise_fixed [Finite K] (σ : K ≃+* K) {g : adjointGroup .G2 K}
    (h : Units.map (entrywiseHom σ.toRingHom) (g : ModGL .G2 K) = (g : ModGL .G2 K)) :
    g ∈ (fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K) := by
  rw [Subgroup.mem_subgroupOf,
    ← CFSG.ComponentClassification.UnbalancedCatalog.entrywiseFixedGroup_eq_fixedFieldImage σ]
  exact ⟨g.2, h⟩

end Rational

theorem card_eq_card_fixSubfield_pow [Finite K] (σ : K ≃+* K) :
    Nat.card K = Nat.card (fixSubfield σ) ^ orderOf σ := by
  have heq : fixSubfield σ = CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.fixedField σ :=
    Subfield.ext fun c => by
      rw [mem_fixSubfield, CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.mem_fixedField_iff]
  rw [heq]
  exact CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.fixedField_card_pow_order σ

section Main

variable [Finite K] [CharP K 2]

theorem subfieldPairG2Big (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hσ : orderOf σ = p) (h4 : 4 ∣ Nat.card (fixSubfield σ)) (g : adjointGroup .G2 K)
    (hne : ((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)).map
        (MulAut.conj g).toMonoidHom ≠ (fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)) :
    Subgroup.closure
      ((((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K) : Subgroup (adjointGroup .G2 K)) :
          Set (adjointGroup .G2 K)) ∪
        ((((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)).map
          (MulAut.conj g).toMonoidHom : Subgroup (adjointGroup .G2 K)) :
          Set (adjointGroup .G2 K))) = ⊤ := by
  set R : Subgroup (adjointGroup .G2 K) := (fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)
    with hRdef
  set k : Subfield K := fixSubfield σ with hkdef
  have hKcard : Nat.card K = Nat.card k ^ p := by
    have := card_eq_card_fixSubfield_pow σ
    rwa [hσ] at this
  have hkpos : 0 < Nat.card k := Nat.card_pos
  have hk4 : 4 ≤ Nat.card k := Nat.le_of_dvd hkpos h4
  have hR : ∀ q < 12, ∀ c ∈ k, xp q c ∈ R := fun q hq c hc =>
    mem_rat_of_entrywise_fixed σ (xp_entrywise_fixed σ hq ((mem_fixSubfield σ).1 hc))
  have hRent : ∀ x : adjointGroup .G2 K, EntriesIn k x → x ∈ R := fun x hx =>
    mem_rat_of_entrywise_fixed σ (entriesIn_entrywise_fixed σ hx)
  have hg : ¬ EntriesIn k g := fun hg => hne (map_conj_eq_self (hRent g hg))
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry k hk4 hR g hg
  set H : Subgroup (adjointGroup .G2 K) :=
    Subgroup.closure ((R : Set (adjointGroup .G2 K)) ∪
      ((R.map (MulAut.conj g).toMonoidHom : Subgroup (adjointGroup .G2 K)) :
        Set (adjointGroup .G2 K))) with hH
  have hRH : R ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hRgH : R.map (MulAut.conj g).toMonoidHom ≤ H := fun x hx =>
    Subgroup.subset_closure (Or.inr hx)
  have hH1 : ∀ c ∈ k, xp 7 c ∈ H := fun c hc => hRH (hR 7 (by norm_num) c hc)
  have hH2 : ∀ c ∈ k, (r * g * r') * xp 7 c * (r * g * r')⁻¹ ∈ H := by
    intro c hc
    have h1 : r' * xp 7 c * r'⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem hr' (hR 7 (by norm_num) c hc)) (R.inv_mem hr')
    have h2 : g * (r' * xp 7 c * r'⁻¹) * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom :=
      ⟨_, h1, by simp [MulAut.conj_apply]⟩
    have h3 : r * (g * (r' * xp 7 c * r'⁻¹) * g⁻¹) * r⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (hRH hr) (hRgH h2)) (H.inv_mem (hRH hr))
    have e : (r * g * r') * xp 7 c * (r * g * r')⁻¹ =
        r * (g * (r' * xp 7 c * r'⁻¹) * g⁻¹) * r⁻¹ := by group
    rw [e]
    exact h3
  have h7 : Full H 7 :=
    full_seven_of_pair k hp (by omega) hKcard h4 (r * g * r') hH1 hH2 hbad
  obtain ⟨t₁, t₂, t₃, h12, h13, h23, h1, h2, h3⟩ := exists_three_nonzero k hk4
  have hex : ∃ t : k, t ≠ 0 ∧ t ≠ 1 := by
    by_cases ht : t₁ = 1
    · exact ⟨t₂, h2, fun e => h12 (ht.trans e.symm)⟩
    · exact ⟨t₁, h1, ht⟩
  obtain ⟨t, ht0, ht1⟩ := hex
  exact eq_top_of_subfield k (t := (t : K)) t.2 (fun e => ht0 (Subtype.ext e))
    (fun e => ht1 (Subtype.ext e)) (fun q hq c hc => hRH (hR q hq c hc)) h7

end Main

end CFSG.RankThree.PartOne.SEITZ6
