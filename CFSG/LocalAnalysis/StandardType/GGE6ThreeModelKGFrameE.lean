module

public import CFSG.LocalAnalysis.StandardType.GGKGAdjDefs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKGFrameAux
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAbelianLift

public section


namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc TableBExc.E6Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {R : Type} [Group R] [Finite R] {L' : Type} [Group L'] [Finite L'] (D : FrameData R)

theorem model_odd_of_good_diag (hAL : GGAbelianLift) (hD : D.Good)
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hcard : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 3)
    {ρ : MulAut L' →* MulAut R} (hρ : ∀ a l, ρ a (ψ l) = ψ (a l)) (hρinj : Function.Injective ρ)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) (hsc : GGTorusSelfCent 3 A)
    (hal : ∀ a ∈ A, ρ a ∈ D.diag.range) :
    ∃ Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3), (∀ a : A, D.diag (Φ a) = ρ a) ∧
      ∃ T w, (Body ψ.ker A Φ T w ∧ ∀ t ∈ T, Odd (orderOf t)) ∧
        ∀ i, ψ (w i) = D.nb i := by
  have hodd : Odd (Nat.card ψ.ker) := by
    rcases hcard with h | h <;> rw [h] <;> decide
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g.1 g.2)⟩
  choose w hw hw2 using fun i => exists_weyl_lift_odd D hD.weyl hψ hker hodd i
  let e : Multiplicative (Fin Tag.E6.rank → ZMod 3) ≃* D.diag.range :=
    MonoidHom.ofInjective hD.faithful
  let ρA : A →* D.diag.range := (ρ.comp A.subtype).codRestrict D.diag.range fun a => hal a a.2
  let Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3) := e.symm.toMonoidHom.comp ρA
  have hΦ : ∀ a : A, D.diag (Φ a) = ρ a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply (ρA a))
  have hinj : Function.Injective Φ := by
    intro a b hab
    apply Subtype.ext
    apply hρinj
    rw [← hΦ a, ← hΦ b, hab]
  obtain ⟨hTab, hTfix, -⟩ := abelianLift_apply D hAL hD hψ hker hcard hρ hAp hal hw
  have hinner := innerPoints_realized D hAL hD hψ hker hcard hρ hA hsc hal hw
  have hinner' : ∀ v ∈ NoOffRest.hypE6, ∃ a ∈ A, ρ a = D.ad v := by
    intro v hv
    obtain ⟨t, -, -, -, a, ha, -, hρa⟩ := hinner v hv
    exact ⟨a, ha, hρa⟩
  have hrange := range_clause D hD.faithful hΦ hinner'
  have hTodd : ∀ t ∈ D.Tor.comap ψ, Odd (orderOf t) := by
    intro t ht
    have hψt : ψ t ∈ D.Tor := ht
    have hm : Odd (orderOf (ψ t)) := hD.torus.2.1 (ψ t) hψt
    have hmem : t ^ orderOf (ψ t) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
    have h1 : (⟨t ^ orderOf (ψ t), hmem⟩ : ψ.ker) ^ Nat.card ψ.ker = 1 := pow_card_eq_one'
    have h2 : t ^ (orderOf (ψ t) * Nat.card ψ.ker) = 1 := by
      have := congrArg Subtype.val h1
      simpa [pow_mul] using this
    exact (hm.mul hodd).of_dvd_nat (orderOf_dvd_of_pow_eq_one h2)
  refine ⟨Φ, hΦ, D.Tor.comap ψ, w,
    ⟨⟨hinj, hrange, hTab, ?_, hTfix, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hTodd⟩, hw⟩
  ·
    intro z hz _
    show ψ z ∈ D.Tor
    rw [(MonoidHom.mem_ker).1 hz]
    exact D.Tor.one_mem
  · intro i t ht
    show ψ (w i * t * (w i)⁻¹) ∈ D.Tor
    rw [map_mul, map_mul, map_inv, hw i]
    exact hD.weyl.2.1 i (ψ t) ht
  · exact coboundary_clause D hAL hD hψ hker hcard hρ hAp hal hw
  · exact weyl_action_clause D hD.weyl hψ hρ hρinj hΦ hrange hw
  · intro x hx
    obtain ⟨t, htT, ht3, -, a, ha, hta, hρa⟩ := hinner x hx
    refine ⟨t, htT, ht3, ⟨a, ha⟩, hta.symm ▸ rfl, ?_⟩
    have h1 : D.diag (Φ ⟨a, ha⟩) = D.diag (Multiplicative.ofAdd x) := by
      rw [hΦ ⟨a, ha⟩, hρa]
      rfl
    exact congrArg Multiplicative.toAdd (hD.faithful h1)
  · exact inner_automizer_clause D hD hψ hρ hΦ hrange
  · exact full_automizer_clause D hD hψ hρ hΦ hrange
  · exact fun _ => ⟨hw2, normalizer_clause D hD hψ hρ hΦ hrange hw⟩

theorem kgFrame_core {K : Type} [Field K] [Finite K] [CharP K 2] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(adjointGroup Tag.E6 K)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) (hcard : Nat.card ψ₀.ker ∣ 3)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAH : ∀ a ∈ A, ∃ φ ∈ (hatAut Tag.E6 K).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l))
    (h5 : Nat.card A = 3 ^ 5) (hsc : GGTorusSelfCent 3 A) :
    ∃ (g : ModGL Tag.E6 K) (κ : A →* Multiplicative (Fin 6 → ZMod 3)),
      g ∈ adjointGroup Tag.E6 K ∧ Function.Injective κ ∧
      (∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6) ∧
      (∀ (a : A) (l : L'),
        ((ψ₀ ((a : MulAut L') l) : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * g⁻¹) *
            ((ψ₀ l : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) *
            (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * g⁻¹)⁻¹) ∧
      (∀ m : L', MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        ∃ u : WeylGroup Tag.E6, ∀ a b : A,
          (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ →
            Multiplicative.toAdd (κ b) = adAct Tag.E6 3 u (Multiplicative.toAdd (κ a))) ∧
      (∀ i : Fin 6, ∃ m : L', MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
        ∀ a b : A, (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ →
          Multiplicative.toAdd (κ b) = adRefl Tag.E6 3 i (Multiplicative.toAdd (κ a))) := by
  haveI : Finite ↥(adjointGroup Tag.E6 K) := Finite.of_surjective ψ₀ hψ₀
  let D : FrameData ↥(adjointGroup Tag.E6 K) := eFrame K ζ hζ
  have hDH : D.H = (hatAut Tag.E6 K).range := rfl
  have hgood : D.Good := eFrame_good hζo hζ
  have hZ : ψ₀.ker = Subgroup.center L' :=
    BstarDesc.ker_eq_center hψ₀ hker (eFrame_center (K := K))
  let ρ : MulAut L' →* MulAut ↥(adjointGroup Tag.E6 K) := BstarDesc.descAut hψ₀ hZ
  have hρ : ∀ a l, ρ a (ψ₀ l) = ψ₀ (a l) := fun a l => BstarDesc.descAut_apply hψ₀ hZ a l
  have hρinj : Function.Injective ρ := BstarDesc.descAut_injective hψ₀ hZ hperf
  have hAH' : ∀ a ∈ A, ρ a ∈ D.H := by
    intro a ha
    obtain ⟨φ, hφH, hφ⟩ := hAH a ha
    have hρφ : ρ a = φ := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ₀ r
      rw [hρ, hφ]
    rw [hρφ, hDH]
    exact hφH
  obtain ⟨γ, hγH, hγ⟩ := exists_align D hgood.shape hρinj hA h5.ge hAH'
  let ψ' : L' →* ↥(adjointGroup Tag.E6 K) := γ.toMonoidHom.comp ψ₀
  have hψ' : Function.Surjective ψ' := γ.surjective.comp hψ₀
  have hkerEq : ψ'.ker = ψ₀.ker := by
    ext l
    simp [ψ', MonoidHom.mem_ker]
  have hker' : ψ'.ker ≤ Subgroup.center L' := hkerEq ▸ hker
  have hcard' : Nat.card ψ'.ker = 1 ∨ Nat.card ψ'.ker = 3 := by
    have h3 : Nat.card ψ'.ker ∣ 3 := by rw [hkerEq]; exact hcard
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    exacts [Or.inl h, Or.inr h]
  let ρ' : MulAut L' →* MulAut ↥(adjointGroup Tag.E6 K) :=
    (MulAut.conj γ).toMonoidHom.comp ρ
  have hρ' : ∀ a l, ρ' a (ψ' l) = ψ' (a l) := by
    intro a l
    change (MulAut.conj γ (ρ a)) (γ (ψ₀ l)) = γ (ψ₀ (a l))
    rw [MulAut.conj_apply]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [hρ a l]
  have hρ'eq : ∀ a, ρ' a = γ * ρ a * γ⁻¹ := fun a => by
    simp only [ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hρ'inj : Function.Injective ρ' := (MulAut.conj γ).injective.comp hρinj
  have hal : ∀ a ∈ A, ρ' a ∈ D.diag.range := by
    intro a ha
    rw [hρ'eq a]
    exact hγ a ha
  obtain ⟨Φ, hΦ, T, w, ⟨hbody, -⟩, -⟩ :=
    model_odd_of_good_diag D ggAbelianLift hgood hψ' hker' hcard' hρ' hρ'inj hA hsc hal
  obtain ⟨hinj, hrange, -, -, -, -, -, hrefl, -, hinnaut, -, -⟩ := hbody
  obtain ⟨g, hgC, hg⟩ := kgFrame_exists_conj_diag (K := K) hζ (hDH ▸ hγH)
  refine ⟨g, Φ, hgC, hinj, kgFrame_range_eq_hyp hinj hrange h5, ?_, ?_, ?_⟩
  ·
    intro a l
    have hconj : γ⁻¹ * ρ' a * γ = ρ a := by
      rw [hρ'eq a]; group
    have key : (γ⁻¹ * D.diag (Φ a) * γ) (ψ₀ l) = ψ₀ ((a : MulAut L') l) := by
      rw [hΦ a, hconj]
      exact hρ a l
    have h2 := hg (Multiplicative.toAdd (Φ a)) (ψ₀ l)
    rw [ofAdd_toAdd (Φ a)] at h2
    exact (congrArg Subtype.val key).symm.trans h2
  · exact hinnaut
  · intro i
    haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [h5]; norm_num)
    refine ⟨w i, kgFrame_conj_mem_normalizer (w i)
      (fun a => (hrefl i a).imp fun b hb => hb.1), ?_⟩
    intro a b hb
    obtain ⟨b', hb', hΦb'⟩ := hrefl i a
    have hbb' : b = b' := Subtype.ext (hb.trans hb')
    rw [hbb']
    exact hΦb'

end CFSG.StandardType.E6ThreeModel

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc TableBExc.E6Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.E6ThreeModel

theorem kgFrameE6_holds : KGFrameE6 := by
  intro K _ _ n hn hK h3 ζ hζ hζo L' _ _ ψ A hTB h5
  obtain ⟨hψ, hker, hperf, hA, hAI, -, -, hsc⟩ := hTB
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  let ψ₀ : L' →* ↥(adjointGroup Tag.E6 K) := (recipeEquiv Tag.E6 K).toMonoidHom.comp ψ
  have hψ₀ : Function.Surjective ψ₀ := (recipeEquiv Tag.E6 K).surjective.comp hψ
  have hker₀ : ψ₀.ker = ψ.ker := by
    ext l
    simp [ψ₀, MonoidHom.mem_ker]
  have hcard : Nat.card ψ₀.ker ∣ 3 := by
    rw [hker₀]
    exact card_ker_dvd_three_e6 hn hK hψ hker hperf
  have hAH : ∀ a ∈ A, ∃ φ ∈ (hatAut Tag.E6 K).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l) := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    refine ⟨MulAut.congr (recipeEquiv Tag.E6 K) φ, (recipeID_iff_hatAut φ).1 hφI, fun l => ?_⟩
    simp [ψ₀, MulAut.congr_apply, hφ]
  obtain ⟨g, κ, hg, hκinj, hκr, h4, h5', h6⟩ :=
    kgFrame_core hζ hζo hψ₀ (hker₀ ▸ hker) hperf hcard hA hAH h5 hsc
  exact ⟨g, κ, hg, hκinj, hκr, h4, h5', h6⟩

end CFSG.StandardType.KGL
