module

public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Main
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Transfer
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG.Assembly TableB NbrInnerRest

private theorem f4t_conj_mem_zpowers {G : Type} [Group G] {a c x : G}
    (hca : c * a * c⁻¹ ∈ Subgroup.zpowers a) (hx : x ∈ Subgroup.zpowers a) :
    c * x * c⁻¹ ∈ Subgroup.zpowers a := by
  have hmap : (Subgroup.zpowers a).map (MulAut.conj c).toMonoidHom ≤ Subgroup.zpowers a := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, Subgroup.mem_comap]
    change (MulAut.conj c) a ∈ Subgroup.zpowers a
    rw [MulAut.conj_apply]
    exact hca
  have h1 : (MulAut.conj c).toMonoidHom x ∈ Subgroup.zpowers a :=
    hmap (Subgroup.mem_map_of_mem _ hx)
  change (MulAut.conj c) x ∈ Subgroup.zpowers a at h1
  rw [MulAut.conj_apply] at h1
  exact h1

theorem ggTorusNoLineComp_of_compIrred {R : Type} [Group R] [Finite R] {I : Set (MulAut R)}
    (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ 3 = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime 3 R)
    (h : ∀ E : Subgroup R, IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) →
      (∃ e ∈ E, e ≠ 1 ∧ GGFixCompCyclic 3 (MulAut.conj e : MulAut R)) → GGWeylIrred E) :
    GGTorusNoLineComp 3 3 R I := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ 3 = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  have hnorm_of : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ψ n ∈ Subgroup.normalizer (E : Set R) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro e
    have h1 := hn (Λ e)
    rw [← hΛn, ← map_inv, ← map_mul, ← map_mul] at h1
    exact h1
  have hnorm_to : ∀ n : L', ψ n ∈ Subgroup.normalizer (E : Set R) →
      MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro a
    constructor
    · intro ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have h1 := (hn e).mp ha
      rw [← hΛn, ← map_inv, ← map_mul, ← map_mul]
      exact h1
    · intro ha
      obtain ⟨e₁, he₁⟩ := hAΛ _ ha
      have he₁E : e₁ ∈ E := by
        show Λ e₁ ∈ A
        rw [he₁]
        exact ha
      have h2 : (ψ n)⁻¹ * e₁ * ψ n ∈ E := by
        refine (hn _).mpr ?_
        rw [show ψ n * ((ψ n)⁻¹ * e₁ * ψ n) * (ψ n)⁻¹ = e₁ by group]
        exact he₁E
      have h3' : a = Λ ((ψ n)⁻¹ * e₁ * ψ n) := by
        rw [map_mul, map_mul, map_inv, he₁, hΛn]
        group
      rw [h3']
      exact h2
  refine ⟨{n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))}, ?_, ?_⟩
  ·
    intro n hn a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have heE : e ∈ E := ha
    have hn' := hnorm_of n hn
    have he'E : ψ n * e * (ψ n)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hn' e).mp heE
    obtain ⟨x, hx, hxp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e) (hEab.2 e heE)
    have hlx : Λ e = MulAut.conj x := hΛeq hx
    have hy : ψ (n * x * n⁻¹) = ψ n * e * (ψ n)⁻¹ := by rw [map_mul, map_mul, map_inv, hx]
    have hyp : (n * x * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hxp, mul_one, mul_inv_cancel]
    have hcomm : x * (n * x * n⁻¹) = (n * x * n⁻¹) * x :=
      commute_of_lift_pow_eq_one hp hker hcpL
        (by rw [hy, hx]; exact TableB.IsElemAbelian.comm hEab heE he'E) hyp
    have hform : n * (Λ e n)⁻¹ = (n * x * n⁻¹) * x⁻¹ := by
      rw [hlx, MulAut.conj_apply]
      group
    refine ⟨?_, fun a' ha' => ?_⟩
    · have hc : Commute (n * x * n⁻¹) x⁻¹ :=
        (show Commute x (n * x * n⁻¹) from hcomm).symm.inv_right
      rw [hform, hc.mul_pow, hyp, inv_pow, hxp, inv_one, mul_one]
    · obtain ⟨e'', rfl⟩ := hAΛ a' ha'
      have he''E : e'' ∈ E := ha'
      obtain ⟨z, hz, hzp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e'')
        (hEab.2 e'' he''E)
      have hzx : z * x = x * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hx]; exact TableB.IsElemAbelian.comm hEab he''E heE) hxp
      have hzy : z * (n * x * n⁻¹) = (n * x * n⁻¹) * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hy]; exact TableB.IsElemAbelian.comm hEab he''E he'E) hyp
      have hcy : Commute z (n * x * n⁻¹) := hzy
      have hcx : Commute z x⁻¹ := (show Commute z x from hzx).inv_right
      rw [hform, hΛeq hz, MulAut.conj_apply, (hcy.mul_right hcx).eq, mul_inv_cancel_right]
  ·
    intro hN a₀ ha₀ ha₀ne hcyc
    by_contra hcon
    have hcon' : ∀ n ∈ {n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))},
        MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∈ Subgroup.zpowers a₀ := by
      intro n hn
      by_contra hnot
      exact hcon ⟨n, hn, hnot⟩
    obtain ⟨e₀, he₀⟩ := hAΛ a₀ ha₀
    obtain ⟨x, hx⟩ := hψ e₀
    have he₀E : e₀ ∈ E := by
      rw [hE, Subgroup.mem_comap, he₀]
      exact ha₀
    have he₀ne : e₀ ≠ 1 := fun h1 => ha₀ne (by rw [← he₀, h1, map_one])
    have hxconj : a₀ = MulAut.conj x := by rw [← he₀, hΛeq hx]
    have hlineE : ∃ e ∈ E, e ≠ 1 ∧ GGFixCompCyclic 3 (MulAut.conj e : MulAut R) := by
      refine ⟨e₀, he₀E, he₀ne, ?_⟩
      have hcx : GGFixCompCyclic 3 (MulAut.conj x) := by
        rw [hxconj] at hcyc
        exact hcyc
      have hc : ∀ l : L', MulAut.conj (ψ x) (ψ l) = ψ (MulAut.conj x l) := by
        intro l
        rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
      have hres := UnitSixThreeKG.ggFixCompCyclic_map hψ hker hc hcx
      rwa [hx] at hres
    have hirr : GGWeylIrred E :=
      h E hEab (by rw [hcardE]; exact hr) hscE hlineE
    set E' : Subgroup R := (Subgroup.zpowers a₀).comap Λ with hE'
    have hE'E : E' ≤ E := fun e he => (Subgroup.zpowers_le.mpr ha₀) he
    have hinvE : ∀ g ∈ Subgroup.normalizer (E : Set R), ∀ e ∈ E', g * e * g⁻¹ ∈ E' := by
      intro g hg e he
      obtain ⟨n, rfl⟩ := hψ g
      have h1 := f4t_conj_mem_zpowers (hcon' n (hnorm_to n hg)) he
      rw [← hΛn, ← map_inv, ← map_mul, ← map_mul] at h1
      exact h1
    rcases hirr E' hE'E hinvE with hbot | htop
    · have he₀E' : e₀ ∈ E' := by
        rw [hE', Subgroup.mem_comap, he₀]
        exact Subgroup.mem_zpowers a₀
      rw [hbot, Subgroup.mem_bot] at he₀E'
      exact he₀ne he₀E'
    · have hcardE' : Nat.card E' ≤ 3 := by
        have hcard_zp : Nat.card (Subgroup.zpowers a₀) ≤ 3 := by
          rw [Nat.card_zpowers]
          exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA.2 a₀ ha₀))
        have hle : Nat.card E' ≤ Nat.card (Subgroup.zpowers a₀) :=
          Nat.card_le_card_of_injective (fun e : E' => (⟨Λ e, e.2⟩ : Subgroup.zpowers a₀))
            (fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)))
        exact le_trans hle hcard_zp
      have h27 : 27 ≤ Nat.card E' := by
        have h : 3 ^ 3 ≤ Nat.card E' := by rw [htop, hcardE]; exact h3
        norm_num at h
        exact h
      omega

end Irred937

theorem ggNbrKGF4ThreeAdd_holds
    : GGNbrKGF4ThreeAdd := by
  intro K _ _ _ hpq
  haveI : Finite (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.F4 K) :=
    Subtype.finite
  haveI : Finite (TableBF4.RecipeGroup K) :=
    Finite.of_equiv (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.F4 K)
      (TableBF4.recipeEquiv K).toEquiv.symm
  exact Irred937.ggTorusNoLineComp_of_compIrred (TableBF4.center_recipeGroup_eq_bot K)
    (fun φ hφ _ => TableBF4.idImage_subset_inn K hφ)
    (ExcSplitL.ggCenterPrime_recipe_F4 Nat.prime_three (by norm_num))
    (Irred937.f4CompIrred_holds K hpq)

end CFSG.StandardType
