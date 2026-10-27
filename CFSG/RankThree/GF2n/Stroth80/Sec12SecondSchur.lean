module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem schur_commute {K E : Type} [Field K] [Finite K] [AddCommGroup E] [Module K E]
    [Module.Finite K E] {ι : Type*} (Φ : ι → (E →ₗ[K] E))
    (hirr : ∀ W : Submodule K E, (∀ i, ∀ w ∈ W, Φ i w ∈ W) → W = ⊥ ∨ W = ⊤)
    (f g : E →ₗ[K] E) (hf : ∀ i, Φ i * f = f * Φ i) (hg : ∀ i, Φ i * g = g * Φ i) :
    f * g = g * f := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact LinearMap.ext fun e => Subsingleton.elim _ _
  haveI : Finite E := Module.finite_of_finite K
  haveI : Finite (E →ₗ[K] E) := Finite.of_injective (fun f : E →ₗ[K] E => (f : E → E))
    DFunLike.coe_injective
  let D : Subalgebra K (Module.End K E) := Subalgebra.centralizer K (Set.range Φ)
  haveI : Finite ↥D :=
    Finite.of_injective (fun x : ↥D => (x : Module.End K E)) Subtype.val_injective
  have hmemD : ∀ x : Module.End K E, x ∈ D ↔ ∀ i, Φ i * x = x * Φ i := by
    intro x
    rw [Subalgebra.mem_centralizer_iff]
    constructor
    · intro h i
      exact h _ ⟨i, rfl⟩
    · rintro h _ ⟨i, rfl⟩
      exact h i
  have hinj : ∀ x : Module.End K E, x ∈ D → x ≠ 0 → Function.Injective x := by
    intro x hx hx0
    have hker : ∀ i, ∀ w ∈ LinearMap.ker x, Φ i w ∈ LinearMap.ker x := by
      intro i w hw
      have := congrArg (fun T : Module.End K E => T w) ((hmemD x).mp hx i)
      simp only [Module.End.mul_apply] at this
      rw [LinearMap.mem_ker] at hw ⊢
      rw [← this, hw, map_zero]
    rcases hirr _ hker with h | h
    · exact LinearMap.ker_eq_bot.mp h
    · exact absurd (LinearMap.ker_eq_top.mp h) hx0
  haveI : IsDomain ↥D := by
    haveI : NoZeroDivisors ↥D := ⟨fun {a b} hab => by
      by_contra hcon
      push Not at hcon
      have ha : (a : Module.End K E) ≠ 0 := fun h => hcon.1 (Subtype.ext h)
      have hb : (b : Module.End K E) ≠ 0 := fun h => hcon.2 (Subtype.ext h)
      have hbi := hinj b b.2 hb
      have hbs : Function.Surjective (b : Module.End K E) := LinearMap.surjective_of_injective hbi
      have hab' : (a : Module.End K E) * b = 0 := congrArg Subtype.val hab
      apply ha
      ext e
      obtain ⟨e', rfl⟩ := hbs e
      have := congrArg (fun T : Module.End K E => T e') hab'
      simpa using this⟩
    exact NoZeroDivisors.to_isDomain _
  have hfield := Finite.isDomain_to_isField ↥D
  have := hfield.mul_comm ⟨f, (hmemD f).mpr fun i => (hf i)⟩ ⟨g, (hmemD g).mpr fun i => hg i⟩
  exact congrArg Subtype.val this


open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem commutators_mem_of_irreducible {G : Type} [Group G] [Finite G]
    {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {R D : Subgroup G} (hRH : R ≤ H0 M Z)
    (hDH : D ≤ H0 M Z)
    (hirr : ∀ A : Subgroup G, Z ≤ A → A ≤ Q → (∀ r ∈ R, conjSubgroup r A = A) →
      A = Z ∨ A = Q)
    (hcomm : ∀ d ∈ D, ∀ r ∈ R, ⁅d, r⁆ ∈ Q) : ∀ a ∈ D, ∀ b ∈ D, ⁅a, b⁆ ∈ Q := by
  obtain ⟨n, γ, M₀, -, h⟩ := stroth_globalModelDataGF H
  obtain ⟨φ, hφπ, hφker, -⟩ := exists_actionHom_H0 H h
  have hcommφ : ∀ u v : ↥(H0 M Z), ⁅(u : G), (v : G)⁆ ∈ Q → φ u * φ v = φ v * φ u := by
    intro u v huv
    have h1 : φ ⁅u, v⁆ = 1 := (hφker _).mpr (by simpa [commutatorElement_def] using huv)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  let Φ : ↥R → Module.End (GaloisField 2 n) M₀.E := fun r =>
    ((φ ⟨r, hRH r.2⟩ : M₀.E ≃ₗ[GaloisField 2 n] M₀.E) : M₀.E →ₗ[GaloisField 2 n] M₀.E)
  have hirr' : ∀ W : Submodule (GaloisField 2 n) M₀.E, (∀ r, ∀ w ∈ W, Φ r w ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let A : Subgroup G :=
      { carrier := {x | x ∈ Q ∧ M₀.π x ∈ W}
        mul_mem' := fun {x y} hx hy => ⟨Q.mul_mem hx.1 hy.1, by
          rw [M₀.π_mul x hx.1 y hy.1]
          exact W.add_mem hx.2 hy.2⟩
        one_mem' := ⟨Q.one_mem, by
          rw [Tim79.QuadModel.pi_one M₀]
          exact W.zero_mem⟩
        inv_mem' := fun {x} hx => ⟨Q.inv_mem hx.1, by
          rw [Tim79.QuadModel.pi_inv M₀ hx.1]
          exact W.neg_mem hx.2⟩ }
    have hZA : Z ≤ A := fun z hz => ⟨H.Z_normal.1 hz, by
      rw [(M₀.π_ker z (H.Z_normal.1 hz)).mpr hz]
      exact W.zero_mem⟩
    have hAQ : A ≤ Q := fun x hx => hx.1
    have hinv : ∀ r ∈ R, conjSubgroup r A = A := by
      intro r hr
      have hrM : r ∈ M := (hRH hr).1
      have hle : conjSubgroup r A ≤ A := by
        rintro _ ⟨a, ha, rfl⟩
        have haQ : a ∈ Q := ha.1
        have hyQ : r * a * r⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hrM) a).mp haQ
        have h1 : M₀.π (r * a * r⁻¹) = Φ ⟨r, hr⟩ (M₀.π a) := hφπ ⟨r, hRH hr⟩ a haQ
        show r * a * r⁻¹ ∈ Q ∧ M₀.π (r * a * r⁻¹) ∈ W
        exact ⟨hyQ, by rw [h1]; exact hW ⟨r, hr⟩ _ ha.2⟩
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
    rcases hirr A hZA hAQ hinv with hA | hA
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨x, hxQ, hx⟩ := M₀.π_surj w
      have hxA : x ∈ A := ⟨hxQ, hx ▸ hw⟩
      rw [hA] at hxA
      rw [Submodule.mem_bot, ← hx]
      exact (M₀.π_ker x hxQ).mpr hxA
    · right
      rw [eq_top_iff]
      intro e _
      obtain ⟨x, hxQ, hx⟩ := M₀.π_surj e
      have hxA : x ∈ A := by rw [hA]; exact hxQ
      rw [← hx]
      exact hxA.2
  intro a ha b hb
  have hf : ∀ (r : ↥R) (u : ↥(H0 M Z)), ⁅(u : G), (r : G)⁆ ∈ Q → Φ r * (φ u : Module.End _ _) =
      (φ u : Module.End _ _) * Φ r := by
    intro r u hu
    have := hcommφ ⟨r, hRH r.2⟩ u (by
      have := Q.inv_mem hu
      simpa [commutatorElement_def, mul_assoc] using this)
    refine LinearMap.ext fun e => ?_
    have h2 := congrArg (fun T : M₀.E ≃ₗ[GaloisField 2 n] M₀.E => T e) this
    exact h2
  have hmain := schur_commute Φ hirr' (φ ⟨a, hDH ha⟩ : Module.End _ _)
    (φ ⟨b, hDH hb⟩ : Module.End _ _) (fun r => hf r _ (hcomm a ha r r.2))
    (fun r => hf r _ (hcomm b hb r r.2))
  have h3 : φ ⟨a, hDH ha⟩ * φ ⟨b, hDH hb⟩ = φ ⟨b, hDH hb⟩ * φ ⟨a, hDH ha⟩ := by
    refine LinearEquiv.ext fun e => ?_
    exact congrArg (fun T : Module.End _ _ => T e) hmain
  have h4 : φ ⁅(⟨a, hDH ha⟩ : ↥(H0 M Z)), ⟨b, hDH hb⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr h3
  simpa [commutatorElement_def] using (hφker _).mp h4

end CFSG.RankThree.GF2n.Stroth80
