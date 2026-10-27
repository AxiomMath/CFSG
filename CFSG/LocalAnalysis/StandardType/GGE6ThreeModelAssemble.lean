module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLiftBar
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelNormalizer
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelBody

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

variable {R : Type} [Group R] [Finite R] {L' : Type} [Group L'] [Finite L'] (D : FrameData R)

theorem range_clause {ρ : MulAut L' →* MulAut R} {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)} (hD : D.Faithful)
    (hΦ : ∀ a : A, D.diag (Φ a) = ρ a)
    (hinner : ∀ v ∈ NoOffRest.hypE6, ∃ a ∈ A, ρ a = D.ad v) :
    Φ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6 := by
  have hsub : ∀ v ∈ NoOffRest.hypE6, Multiplicative.ofAdd v ∈ Φ.range := by
    intro v hv
    obtain ⟨a, ha, hav⟩ := hinner v hv
    refine ⟨⟨a, ha⟩, ?_⟩
    apply hD
    rw [hΦ ⟨a, ha⟩]
    exact hav
  by_cases hall : ∀ x ∈ Φ.range, NoOffRest.kDotP 3 (Multiplicative.toAdd x) = 0
  · right
    intro x
    exact ⟨fun hx => NoOffRest.mem_hypE6.2 (hall _ hx), fun hx => hsub x hx⟩
  · left
    push Not at hall
    obtain ⟨x₀, hx₀, hne⟩ := hall
    rw [eq_top_iff]
    intro y _
    set k₀ := NoOffRest.kDotP 3 (Multiplicative.toAdd x₀)
    set c : ZMod 3 := NoOffRest.kDotP 3 (Multiplicative.toAdd y) * k₀⁻¹ with hc
    have hyc : Multiplicative.toAdd y - c • Multiplicative.toAdd x₀ ∈ NoOffRest.hypE6 := by
      rw [NoOffRest.mem_hypE6, NoOffRest.kDotP_sub, NoOffRest.kDotP_smul, hc, mul_assoc,
        inv_mul_cancel₀ hne, mul_one, sub_self]
    have h1 := hsub _ hyc
    have h2 : Multiplicative.ofAdd (c • Multiplicative.toAdd x₀) ∈ Φ.range := by
      have e : c • Multiplicative.toAdd x₀ = c.val • Multiplicative.toAdd x₀ := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod 3) c.val, ZMod.natCast_zmod_val]
      rw [e, ofAdd_nsmul]
      exact Subgroup.pow_mem _ (by simpa using hx₀) _
    have h3 := Subgroup.mul_mem _ h1 h2
    rwa [← ofAdd_add, sub_add_cancel] at h3

theorem model_odd_of_good (hAL : GGAbelianLift) (hD : D.Good)
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hcard : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 3)
    {ρ : MulAut L' →* MulAut R} (hρ : ∀ a l, ρ a (ψ l) = ψ (a l)) (hρinj : Function.Injective ρ)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) (hsc : GGTorusSelfCent 3 A)
    (hal : ∀ a ∈ A, ρ a ∈ D.diag.range) :
    ModelOdd ψ.ker A := by
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
  refine ⟨Φ, D.Tor.comap ψ, w, ⟨hinj, hrange, hTab, ?_, hTfix, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hTodd⟩
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

end CFSG.StandardType.E6ThreeModel
