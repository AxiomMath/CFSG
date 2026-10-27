module

public import CFSG.Milestones.ASVolI.F429.C5Gen
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F429.bC7
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.H13.Sec53F.BA

section Generic

variable {Y : Type} [Group Y]

theorem burnsideF429b_mul_conj (τ : MulAut Y) (g : Y) :
    τ * MulAut.conj g = MulAut.conj (τ g) * τ := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem burnsideF429b_pow_conj_mul (g : Y) (τ : MulAut Y) (n : ℕ) :
    ∃ w : Y, (MulAut.conj g * τ) ^ n = MulAut.conj w * τ ^ n := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨w * (τ ^ n) g, ?_⟩
    rw [pow_succ, hw, pow_succ, map_mul]
    calc MulAut.conj w * τ ^ n * (MulAut.conj g * τ)
        = MulAut.conj w * (τ ^ n * MulAut.conj g) * τ := by simp only [mul_assoc]
      _ = MulAut.conj w * (MulAut.conj ((τ ^ n) g) * τ ^ n) * τ := by
          rw [burnsideF429b_mul_conj]
      _ = MulAut.conj w * MulAut.conj ((τ ^ n) g) * (τ ^ n * τ) := by simp only [mul_assoc]

variable {U H : Subgroup Y} {F : Subgroup (MulAut Y)}

theorem burnsideF429b_eq_one_of_inner (D : BorelAutData U H F) {τ : MulAut Y} (hτ : τ ∈ F)
    {x : Y} (hx : τ = MulAut.conj x) : τ = 1 := by
  have hxN : x ∈ Subgroup.normalizer (U : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := D.F_U τ hτ y
    rw [hx, MulAut.conj_apply] at this
    exact this.symm
  obtain ⟨u, hu, h₁, hh₁, rfl⟩ := D.B_eq x hxN
  refine D.F_faithful τ hτ fun h hh => ?_
  have hτh : τ h ∈ H := D.F_H τ hτ h hh
  have e : τ h = u * h * u⁻¹ := by
    rw [hx, MulAut.conj_apply]
    have hc : h₁ * h = h * h₁ := D.H_comm h₁ hh₁ h hh
    calc u * h₁ * h * (u * h₁)⁻¹ = u * (h₁ * h) * h₁⁻¹ * u⁻¹ := by group
      _ = u * (h * h₁) * h₁⁻¹ * u⁻¹ := by rw [hc]
      _ = u * h * u⁻¹ := by group
  have hU : τ h * h⁻¹ ∈ U := by
    rw [e]
    have h2 : h * u⁻¹ * h⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 (D.H_le hh) u⁻¹).1 (U.inv_mem hu)
    have e2 : u * h * u⁻¹ * h⁻¹ = u * (h * u⁻¹ * h⁻¹) := by group
    rw [e2]
    exact U.mul_mem hu h2
  exact mul_inv_eq_one.1 (D.U_inf_H _ hU (H.mul_mem hτh (H.inv_mem hh)))

theorem burnsideF429b_fix_of_conj_mul (D : BorelAutData U H F) {g : Y}
    (hg : g ∈ Subgroup.normalizer (U : Set Y)) {τ : MulAut Y} (hτ : τ ∈ F) {h : Y}
    (hh : h ∈ H) (hc : (MulAut.conj g * τ) h * h⁻¹ ∈ U) : τ h = h := by
  obtain ⟨u₀, hu₀, h₀, hh₀, rfl⟩ := D.B_eq g hg
  have hτh : τ h ∈ H := D.F_H τ hτ h hh
  rw [MulAut.mul_apply, MulAut.conj_apply] at hc
  have hcomm : h₀ * τ h = τ h * h₀ := D.H_comm h₀ hh₀ (τ h) hτh
  have e1 : u₀ * h₀ * τ h * (u₀ * h₀)⁻¹ * h⁻¹ = u₀ * τ h * u₀⁻¹ * h⁻¹ := by
    calc u₀ * h₀ * τ h * (u₀ * h₀)⁻¹ * h⁻¹ = u₀ * (h₀ * τ h) * h₀⁻¹ * u₀⁻¹ * h⁻¹ := by group
      _ = u₀ * (τ h * h₀) * h₀⁻¹ * u₀⁻¹ * h⁻¹ := by rw [hcomm]
      _ = u₀ * τ h * u₀⁻¹ * h⁻¹ := by group
  rw [e1] at hc
  have hu1 : h * u₀ * h⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (D.H_le hh) u₀).1 hu₀
  have hmem : τ h * h⁻¹ ∈ U := by
    have e2 : τ h * h⁻¹ = u₀⁻¹ * (u₀ * τ h * u₀⁻¹ * h⁻¹) * (h * u₀ * h⁻¹) := by group
    rw [e2]
    exact U.mul_mem (U.mul_mem (U.inv_mem hu₀) hc) hu1
  exact mul_inv_eq_one.1 (D.U_inf_H _ hmem (H.mul_mem hτh (H.inv_mem hh)))

theorem burnsideF429b_mem_oPPrime_of_mul_self {P : Subgroup Y} {x : Y} (hx : x ∈ P)
    (h : x * x = 1) : x ∈ oPPrime 2 P := by
  refine Subgroup.subset_closure ⟨hx, ?_⟩
  have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
  · exact ⟨0, by rw [h1, pow_zero]⟩
  · exact ⟨1, by rw [h2, pow_one]⟩

end Generic

section Transport

theorem burnsideF429b_keyL_of_borelAutData {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥) {C : Type} [Group C]
    (Ψ : C ≃* ↥Gp) {B U H : Subgroup C} {F : Subgroup (MulAut C)} (D : BorelAutData U H F)
    (hB : (M₁ ⊓ M₂).subgroupOf Gp = B.map Ψ.toMonoidHom) (hU : pCoreOf 2 B = U)
    {M : Subgroup E} {P : Subgroup C} (hM : M.subgroupOf Gp = P.map Ψ.toMonoidHom)
    {H₀ : Set C} (hH₀ : ∀ h ∈ H₀, h ∈ H ∧ h ∈ oPPrime 2 P ∧ h ∈ B)
    (hfaith : ∀ τ ∈ F, ∀ k : ℕ, τ ^ 2 ^ k = 1 → (∀ h ∈ H₀, τ h = h) → τ = 1) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  intro r hr k hk hcomm
  set φ : C →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hφx : ∀ x : C, φ x = ((Ψ x : ↥Gp) : E) := fun x => rfl
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = B.map φ := burnsideF429_inf_eq_map Ψ hB
  have hGM : Gp ⊓ M = P.map φ := burnsideF429_inf_eq_map Ψ hM
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = U.map φ := by
    rw [hGB, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ hφ, hU]
  have hO : oPPrime 2 (Gp ⊓ M) = (oPPrime 2 P).map φ := by
    rw [hGM, burnsideF4gF4Inv_oPPrime_map_inj _ hφ]
  have hrN := burnsideF429_le_normalizer_pCore_inf (Gp := Gp) (M₁ ⊓ M₂) hr
  let β : MulAut C := (Ψ.trans (burnsideF4d_rho Gp r)).trans Ψ.symm
  have hβφ : ∀ x : C, φ (β x) = r * φ x * r⁻¹ := by
    intro x
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp r (Ψ x))) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact burnsideF4d_rho_apply r (Ψ x)
  have hmemU : ∀ x : C, x ∈ U ↔ φ x ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
    intro x
    rw [hS]
    exact (Subgroup.mem_map_iff_mem hφ).symm
  have h1 : ∀ x, β x ∈ U ↔ x ∈ U := by
    intro x
    rw [hmemU, hmemU, hβφ]
    exact ((Subgroup.mem_normalizer_iff.1 hrN) (φ x)).symm
  have h2 : ∀ h ∈ H₀, β h * h⁻¹ ∈ U := by
    intro h hh
    obtain ⟨-, hhP, hhB⟩ := hH₀ h hh
    rw [hmemU, map_mul, map_inv, hβφ]
    refine hcomm (φ h) ⟨?_, ?_⟩
    · rw [hO]
      exact ⟨h, hhP, rfl⟩
    · have hb : φ h ∈ Gp ⊓ (M₁ ⊓ M₂) := by
        rw [hGB]
        exact ⟨h, hhB, rfl⟩
      exact hb.2
  have hpow : ∀ n : ℕ, ∀ x : C, φ ((β ^ n) x) = r ^ n * φ x * (r ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      simp only [pow_succ, MulAut.mul_apply]
      rw [ih, hβφ]
      group
  have hβk : β ^ 2 ^ k = 1 := by
    refine MulEquiv.ext fun x => hφ ?_
    rw [hpow, hk]
    simp
  obtain ⟨g, hg, τ, hτ, hβ⟩ := D.normal_form β h1
  have hτk : τ ^ 2 ^ k = 1 := by
    obtain ⟨w, hw⟩ := burnsideF429b_pow_conj_mul g τ (2 ^ k)
    rw [← hβ, hβk] at hw
    have e : τ ^ 2 ^ k = MulAut.conj w⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right hw.symm
    exact burnsideF429b_eq_one_of_inner D (Subgroup.pow_mem _ hτ _) e
  have hfix : ∀ h ∈ H₀, τ h = h := fun h hh =>
    burnsideF429b_fix_of_conj_mul D hg hτ (hH₀ h hh).1 (by rw [← hβ]; exact h2 h hh)
  have hτ1 : τ = 1 := hfaith τ hτ k hτk hfix
  rw [hτ1, mul_one] at hβ
  have hρ : burnsideF4d_rho Gp r = burnsideF4d_rho Gp ((Ψ g : ↥Gp) : E) := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    obtain ⟨x, rfl⟩ := Ψ.surjective y
    rw [burnsideF4d_rho_apply, burnsideF4d_rho_apply]
    have e1 := hβφ x
    rw [hβ, MulAut.conj_apply, map_mul, map_mul, map_inv] at e1
    rw [← hφx, ← hφx, ← e1]
  have hr' := burnsideF4d_rho_injective hc hρ
  rw [hr']
  exact (Ψ g).2

end Transport

section Torus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem burnsideF429b_xUnit_mul_self (i : Fin τ.rank) (c : K) :
    xUnit τ K i c * xUnit τ K i c = 1 := by
  have e : (xUnit τ K i c)⁻¹ = xUnit τ K i c :=
    Units.ext (by rw [coe_xUnit_inv, coe_xUnit, CharTwo.neg_eq])
  calc xUnit τ K i c * xUnit τ K i c = xUnit τ K i c * (xUnit τ K i c)⁻¹ := by rw [e]
    _ = 1 := mul_inv_cancel _

theorem burnsideF429b_yUnit_mul_self (i : Fin τ.rank) (c : K) :
    yUnit τ K i c * yUnit τ K i c = 1 := by
  have e : (yUnit τ K i c)⁻¹ = yUnit τ K i c :=
    Units.ext (by rw [coe_yUnit_inv, coe_yUnit, CharTwo.neg_eq])
  calc yUnit τ K i c * yUnit τ K i c = yUnit τ K i c * (yUnit τ K i c)⁻¹ := by rw [e]
    _ = 1 := mul_inv_cancel _

theorem burnsideF429b_torusElt_mem_oPPrime (i : Fin τ.rank) (t : Kˣ) :
    (⟨torusElt τ K i t, torusElt_mem_adjointGroup i t⟩ : ↥(adjointGroup τ K)) ∈
      oPPrime 2 ((parabolicSubgroup τ K {i}).subgroupOf (adjointGroup τ K)) := by
  have hx : ∀ c : K, (⟨xUnit τ K i c, xUnit_mem_adjointGroup i c⟩ : ↥(adjointGroup τ K)) ∈
      oPPrime 2 ((parabolicSubgroup τ K {i}).subgroupOf (adjointGroup τ K)) := fun c =>
    burnsideF429b_mem_oPPrime_of_mul_self
      (Subgroup.mem_subgroupOf.2 (borelGroup_le_parabolicSubgroup _ (xUnit_mem_borelGroup i c)))
      (Subtype.ext (burnsideF429b_xUnit_mul_self i c))
  have hy : ∀ c : K, (⟨yUnit τ K i c, yUnit_mem_adjointGroup i c⟩ : ↥(adjointGroup τ K)) ∈
      oPPrime 2 ((parabolicSubgroup τ K {i}).subgroupOf (adjointGroup τ K)) := fun c =>
    burnsideF429b_mem_oPPrime_of_mul_self
      (Subgroup.mem_subgroupOf.2 (yUnit_mem_parabolicSubgroup i c))
      (Subtype.ext (burnsideF429b_yUnit_mul_self i c))
  have e : (⟨torusElt τ K i t, torusElt_mem_adjointGroup i t⟩ : ↥(adjointGroup τ K)) =
      (⟨xUnit τ K i t, xUnit_mem_adjointGroup i _⟩ : ↥(adjointGroup τ K)) *
        ⟨yUnit τ K i (-((t⁻¹ : Kˣ) : K)), yUnit_mem_adjointGroup i _⟩ *
        ⟨xUnit τ K i t, xUnit_mem_adjointGroup i _⟩ *
        (⟨xUnit τ K i ((-1 : Kˣ) : K), xUnit_mem_adjointGroup i _⟩ *
          ⟨yUnit τ K i (-(((-1 : Kˣ)⁻¹ : Kˣ) : K)), yUnit_mem_adjointGroup i _⟩ *
          ⟨xUnit τ K i ((-1 : Kˣ) : K), xUnit_mem_adjointGroup i _⟩) := by
    apply Subtype.ext
    show torusElt τ K i t = xUnit τ K i t * yUnit τ K i (-((t⁻¹ : Kˣ) : K)) * xUnit τ K i t *
      (xUnit τ K i ((-1 : Kˣ) : K) * yUnit τ K i (-(((-1 : Kˣ)⁻¹ : Kˣ) : K)) *
        xUnit τ K i ((-1 : Kˣ) : K))
    rw [show torusElt τ K i t = weylElt τ K i t * weylElt τ K i (-1) from rfl,
      weylElt_eq_xUnit_mul, weylElt_eq_xUnit_mul]
  rw [e]
  exact mul_mem (mul_mem (mul_mem (hx _) (hy _)) (hx _))
    (mul_mem (mul_mem (hx _) (hy _)) (hx _))

theorem burnsideF429b_torusElt_injective (i : Fin τ.rank) {t u : Kˣ}
    (h : torusElt τ K i t = torusElt τ K i u) : t = u := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit] at h
  have h2 := congrFun (rootDiagUnit_injective h) i
  simp only [Tag.cartan_self] at h2
  have h3 : ((t : K)) ^ 2 = (u : K) ^ 2 := by
    have := congrArg Units.val h2
    simpa [zpow_two, sq] using this
  exact Units.ext (frobenius_inj K 2 (by simpa [frobenius_def] using h3))

end Torus

section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2


theorem burnsideF429b_G2_chartPB {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : HypF_4_4g .G2 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      ∃ Ψ : H13.F431.G2.C K ≃* ↥Gp,
        M₁.subgroupOf Gp = (H13.F431.G2.Cent.Pr K).map Ψ.toMonoidHom ∧
        M₂.subgroupOf Gp = (H13.F431.G2.Cent.Pa K).map Ψ.toMonoidHom ∧
        (M₁ ⊓ M₂).subgroupOf Gp = (borelSub Tag.G2 K).map Ψ.toMonoidHom := by
  obtain ⟨chart, hb, hpts, hlns⟩ := h.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, -⟩ | ⟨hk, hp, hd, K, fK, finK, card, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · letI := fK
    haveI := finK
    haveI : CharP K 2 := burnsideF4f_charP_of_card hd card
    let Ψ : H13.F431.G2.C K ≃* ↥Gp := (H13.F431.G2.mk K).trans marking
    have hΨ : ∀ L : Subgroup (G2Native.Parent K),
        G2Native.fullImage K marking L = L.map Ψ.toMonoidHom := by
      intro L
      unfold G2Native.fullImage G2Native.fullLocal
      rw [Subgroup.map_map]
      exact congrArg (fun φ => Subgroup.map φ L) (MonoidHom.ext fun y => rfl)
    have hsub : ∀ (X : Subgroup E) (L : Subgroup (G2Native.Parent K)),
        Gp ⊓ X = (G2Native.fullImage K marking L).map Gp.subtype →
          X.subgroupOf Gp = L.map Ψ.toMonoidHom := by
      intro X L hX
      rw [← Subgroup.inf_subgroupOf_left X Gp, hX, ← hΨ]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    refine ⟨K, fK, finK, inferInstance, card, Ψ, ?_, ?_, ?_⟩
    · rw [hsub _ _ (hpts.trans h2), burnsideF429b_G2_point_eq]
    · rw [hsub _ _ (hlns.trans h3), burnsideF429b_G2_line_eq]
    · rw [hsub _ _ (hb.trans h1), burnsideF429b_G2_positiveBorel_eq]
  all_goals exact absurd hk (by decide)

theorem burnsideF429b_G2_faithful {K : Type} [Field K] [CharP K 2] (i : Fin Tag.G2.rank) :
    ∀ τ ∈ (H13.Sec53F.G2.fieldAut K).range,
      (∀ t : Kˣ, τ ⟨torusElt Tag.G2 K i t, torusElt_mem_adjointGroup i t⟩ =
        ⟨torusElt Tag.G2 K i t, torusElt_mem_adjointGroup i t⟩) → τ = 1 := by
  rintro _ ⟨σ₀, rfl⟩ hfix
  have hu : ∀ t : Kˣ, σ₀ (t : K) = t := by
    intro t
    have h1 : Units.map (entrywiseHom σ₀.toRingHom) (torusElt Tag.G2 K i t) =
        torusElt Tag.G2 K i t := by
      have := congrArg (fun x : ↥(adjointGroup Tag.G2 K) => (x : ModGL Tag.G2 K)) (hfix t)
      simpa only [H13.Sec53F.G2.fieldAut_apply] using this
    rw [entrywise_torusElt] at h1
    exact congrArg Units.val (burnsideF429b_torusElt_injective i h1)
  have hσ : σ₀ = 1 := by
    refine RingEquiv.ext fun c => ?_
    by_cases hc : c = 0
    · subst hc
      simp
    · exact hu (Units.mk0 c hc)
  rw [hσ, map_one]

theorem burnsideF429b_G2_keyL {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f) {M : Subgroup E}
    (hM : ∀ (K : Type) (_ : Field K) (_ : CharP K 2) (Ψ : H13.F431.G2.C K ≃* ↥Gp),
      M₁.subgroupOf Gp = (H13.F431.G2.Cent.Pr K).map Ψ.toMonoidHom →
      M₂.subgroupOf Gp = (H13.F431.G2.Cent.Pa K).map Ψ.toMonoidHom →
      ∃ i : Fin Tag.G2.rank, M.subgroupOf Gp =
        ((parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K)).map
          Ψ.toMonoidHom) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  haveI := hyp.normal
  obtain ⟨K, fK, finK, cK, hcard, Ψ, h1, h2, hB⟩ := burnsideF429b_G2_chartPB hyp.toHypF_4_4g
  obtain ⟨i, hMi⟩ := hM K fK cK Ψ h1 h2
  have hHB : torusSub Tag.G2 K ≤ borelSub Tag.G2 K :=
    le_sup_right.trans (posUnipotentSub_sup_torusSub (τ := Tag.G2) (K := K)).le
  refine burnsideF429b_keyL_of_borelAutData hyp.centralizer_trivial Ψ
    (H13.Sec53F.G2.borelAutData_g2 hf hcard) hB burnsideF429b_G2_pCoreOf_borel hMi
    (H₀ := Set.range fun t : Kˣ =>
      (⟨torusElt Tag.G2 K i t, torusElt_mem_adjointGroup i t⟩ : ↥(adjointGroup Tag.G2 K)))
    ?_ ?_
  · rintro _ ⟨t, rfl⟩
    have hT : (⟨torusElt Tag.G2 K i t, torusElt_mem_adjointGroup i t⟩ :
        ↥(adjointGroup Tag.G2 K)) ∈ torusSub Tag.G2 K :=
      Subgroup.mem_subgroupOf.2 (torusElt_mem_torusGroup i t)
    exact ⟨hT, burnsideF429b_torusElt_mem_oPPrime i t, hHB hT⟩
  · intro τ hτ _ _ hfix
    exact burnsideF429b_G2_faithful i τ hτ fun t => hfix _ ⟨t, rfl⟩

theorem burnsideF429b_key1_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₁) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp :=
  burnsideF429b_G2_keyL hyp hf fun _ _ _ _ h1 _ => ⟨i1, h1⟩

theorem burnsideF429b_key2_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₂) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp :=
  burnsideF429b_G2_keyL hyp hf fun _ _ _ _ _ h2 => ⟨i0, h2⟩

end G2

section C5


theorem burnsideF429b_c5_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C5 .G2 Gp M₁ M₂ hyp T :=
  burnsideF429_c5i_of_keys hyp hT (burnsideF429b_key1_G2 hyp hf) (burnsideF429b_key2_G2 hyp hf)

end C5

end CFSG.ASVolI
