module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem card_center_eq_card_inf_centralizer {M : Type} [Group M] (L' : Subgroup M) :
    Nat.card (Subgroup.center L') =
      Nat.card (L' ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) := by
  have hmap : (Subgroup.center L').map L'.subtype =
      L' ⊓ Subgroup.centralizer (L' : Set M) := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hy⟩)
    · rintro ⟨hgL, hgc⟩
      refine ⟨⟨g, hgL⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgc y.1 y.2)
  rw [← hmap]
  exact Nat.card_congr
    ((Subgroup.center L').equivMapOfInjective L'.subtype L'.subtype_injective).toEquiv

private theorem ggLAutImage_eq_inducedSub {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {θ : L' ⧸ Subgroup.center L' ≃* R}
    (hE : E ≤ Subgroup.normalizer (L' : Set M)) :
    ggLAutImage L' θ E = TypeA.inducedSub (ggQuotHom θ) (ggGamma L' hE).range := by
  ext a
  constructor
  · intro ha
    change a ∈ (E.subgroupOf (Subgroup.normalizer (L' : Set M))).map (ggLAut L' θ) at ha
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
    let b₀ : E := ⟨g.1, Subgroup.mem_subgroupOf.mp hg⟩
    refine ⟨ggGamma L' hE b₀, ⟨b₀, rfl⟩, ?_⟩
    intro l
    have h1 : ggLAut L' θ g = ggBeta L' θ hE b₀ := by
      rw [ggBeta_eq]
    rw [h1]
    exact ggBeta_ggQuotHom L' hE θ b₀ l
  · intro ha
    obtain ⟨γ, ⟨b, rfl⟩, hact⟩ := ha
    change a ∈ (E.subgroupOf (Subgroup.normalizer (L' : Set M))).map (ggLAut L' θ)
    refine Subgroup.mem_map.mpr ⟨⟨b.1, hE b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, ?_⟩
    symm
    refine TypeA.induced_unique (ggQuotHom θ) (ggQuotHom_surjective θ) hact ?_
    intro l
    have h1 : ggLAut L' θ ⟨b.1, hE b.2⟩ = ggBeta L' θ hE b := by
      rw [ggBeta_eq]
    rw [h1]
    exact ggBeta_ggQuotHom L' hE θ b l

private theorem ggTorusSelfCent_inducedSub {L' R : Type} [Group L'] [Finite L'] [Group R]
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {p : ℕ} (hp : p.Prime) (hZp : ¬ p ∣ Nat.card (Subgroup.center L'))
    {A : Subgroup (MulAut L')} (hA : GGTorusSelfCent p A)
    (hAind : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l : L', φ (ψ l) = ψ (a l)) :
    GGTorusSelfCent p (TypeA.inducedSub ψ A) := by
  intro n hn hnp
  obtain ⟨l₀, rfl⟩ := hψ n
  set N := Nat.card (Subgroup.center L') with hN
  have hcop : Nat.Coprime N p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hZp)
  have hcop' : Nat.Coprime p N := hcop.symm
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  set l : L' := l₀ ^ (N * u) with hl
  have himg : ψ l = ψ l₀ := by
    rw [hl, map_pow, ← Nat.div_add_mod (N * u) p, hu, pow_add, pow_mul, hnp, one_pow, one_mul,
      pow_one]
  have hlpker : l₀ ^ p ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hnp]
  have hlpC : l₀ ^ p ∈ Subgroup.center L' := hker hlpker
  have hlp : l ^ p = 1 := by
    have h1 : (⟨l₀ ^ p, hlpC⟩ : Subgroup.center L') ^ N = 1 := pow_card_eq_one'
    have h2 : (l₀ ^ p) ^ N = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    rw [hl, ← pow_mul, mul_comm (N * u) p, ← mul_assoc, pow_mul, pow_mul, h2, one_pow]
  have hfixA : ∀ a ∈ A, a l = l := by
    intro a ha
    obtain ⟨φa, hφa⟩ := hAind a ha
    have hmem : φa ∈ TypeA.inducedSub ψ A := ⟨a, ha, hφa⟩
    have hφl : ψ (a l) = ψ l := by
      rw [← hφa l, himg]
      exact hn φa hmem
    have hza : a l * l⁻¹ ∈ Subgroup.center L' := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφl, mul_inv_cancel]
    set z : Subgroup.center L' := ⟨a l * l⁻¹, hza⟩ with hzdef
    have hzc : ∀ y : L', (z : L') * y = y * z := fun y =>
      (Subgroup.mem_center_iff.mp hza y).symm
    have hmp : (a l) ^ p = 1 := by
      rw [← map_pow, hlp, map_one]
    have hzp : z ^ p = 1 := by
      apply Subtype.ext
      have e2 : a l = (z : L') * l := by rw [hzdef]; group
      have e3 : ((z : L') * l) ^ p = (z : L') ^ p * l ^ p := Commute.mul_pow (hzc l) p
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      calc (z : L') ^ p = (z : L') ^ p * l ^ p := by rw [hlp, mul_one]
        _ = ((z : L') * l) ^ p := e3.symm
        _ = (a l) ^ p := by rw [← e2]
        _ = 1 := hmp
    have hz1 : z = 1 := by
      rw [← orderOf_eq_one_iff]
      exact Nat.eq_one_of_dvd_coprimes hcop' (orderOf_dvd_of_pow_eq_one hzp)
        (orderOf_dvd_natCard z)
    have hml : a l = l := by
      have h1 : a l * l⁻¹ = 1 := by
        have := congrArg Subtype.val hz1
        simpa [hzdef] using this
      exact mul_inv_eq_one.mp h1
    exact hml
  have hlA : MulAut.conj l ∈ A := hA l hfixA hlp
  refine ⟨MulAut.conj l, hlA, fun l' => ?_⟩
  simp only [MulAut.conj_apply, map_mul, map_inv, himg]

theorem pow_le_card_ggLAutImage {M : Type} [Group M] [Finite M] {L' E : Subgroup M} {R : Type}
    [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p r : ℕ}
    (hP : GGTableBPosition p L' E I θ hE) (hp : p.Prime) (hL : GGTorusLift p r R) :
    p ^ r ≤ Nat.card (ggLAutImage L' θ E) := by
  have hγ := TableBBridge.pow_le_card_range_of_torusLift hP hp hL
  have hcard : Nat.card (TypeA.inducedSub (ggQuotHom θ) (ggGamma L' hE).range) =
      Nat.card (ggGamma L' hE).range :=
    TypeA.card_inducedSub (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hP.1
      (A := (ggGamma L' hE).range)
      (fun a ha => by
        obtain ⟨φ, -, hφ⟩ := TableBBridge.induces_range_gamma hP a ha
        exact ⟨φ, hφ⟩)
  calc p ^ r ≤ Nat.card (ggGamma L' hE).range := hγ
    _ = Nat.card (TypeA.inducedSub (ggQuotHom θ) (ggGamma L' hE).range) := hcard.symm
    _ = Nat.card (ggLAutImage L' θ E) :=
        (congrArg (fun H : Subgroup (MulAut R) => Nat.card H)
          (ggLAutImage_eq_inducedSub (E := E) (θ := θ) hE)).symm

theorem ggTorusSelfCent_ggLAutImage {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p : ℕ}
    (hP : GGTableBPosition p L' E I θ hE) (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (L' ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M)) :
    GGTorusSelfCent p (ggLAutImage L' θ E) := by
  have hZc : ¬ p ∣ Nat.card (Subgroup.center L') := by
    rw [card_center_eq_card_inf_centralizer L']
    exact hZ
  have hsc := ggTorusSelfCent_inducedSub (ψ := ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hp hZc (TableBBridge.ggTorusSelfCent_range hP)
    (fun a ha => by
      obtain ⟨φ, -, hφ⟩ := TableBBridge.induces_range_gamma hP a ha
      exact ⟨φ, hφ⟩)
  rw [← ggLAutImage_eq_inducedSub (E := E) (θ := θ) hE] at hsc
  exact hsc

end CFSG.StandardType
