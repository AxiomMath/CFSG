module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

namespace S35.C56

theorem exists_principal_of_alt {L : Type*} [Group L] (ψ : L →* Equiv.Perm (Fin 5))
    (halt : ∀ l, ψ l ∈ alternatingGroup (Fin 5))
    (hsurj : ∀ a ∈ alternatingGroup (Fin 5), ∃ l, ψ l = a) (φ : L → orth.W)
    (hφ : ∀ l₁ l₂, φ (l₁ * l₂) = φ l₁ * orth.act (ψ l₁) (φ l₂))
    (hker : ∀ l, ψ l = 1 → φ l = 1) :
    ∃ w : orth.W, ∀ l, φ l = orth.act (ψ l) w * w⁻¹ := by
  have hwd : ∀ l l', ψ l = ψ l' → φ l = φ l' := by
    intro l l' h
    have h1 : ψ (l⁻¹ * l') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have := hφ l (l⁻¹ * l')
    rw [hker _ h1, map_one, mul_one, mul_inv_cancel_left] at this
    exact this.symm
  choose c hc using hsurj
  let f : alternatingGroup (Fin 5) → orth.W := fun a => φ (c a.1 a.2)
  have hf : ∀ a b, f (a * b) = f a * orth.act (a : Equiv.Perm (Fin 5)) (f b) := by
    intro a b
    have h1 : ψ (c (a * b).1 (a * b).2) = ψ (c a.1 a.2 * c b.1 b.2) := by
      rw [map_mul, hc, hc, hc]; rfl
    show φ (c (a * b).1 (a * b).2) = φ (c a.1 a.2) * orth.act (a : Equiv.Perm (Fin 5))
      (φ (c b.1 b.2))
    rw [hwd _ _ h1, hφ, hc]
  obtain ⟨w, hw⟩ := h1_alt5_orth f hf
  refine ⟨w, fun l => ?_⟩
  have := hw ⟨ψ l, halt l⟩
  rw [← hwd (c (ψ l) (halt l)) l (hc _ _)]
  exact this

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_secHom {X E F : Subgroup G} (h : IsOrthSec X E F) :
    ∃ (θ : ↥X →* Equiv.Perm (Fin 5)) (ρ : ↥F →* orth.W), Function.Surjective θ ∧
      θ.ker = (cSecIn X E F).subgroupOf X ∧ (∀ y : ↥F, ρ y = 1 ↔ (y : G) ∈ E) ∧
      Function.Surjective ρ ∧ ∀ (k : ↥X) (y : ↥F) (hky : (k : G) * y * (k : G)⁻¹ ∈ F),
        ρ ⟨k * y * k⁻¹, hky⟩ = orth.act (θ k) (ρ y) := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  let e := MulEquiv.ofBijective β ⟨hsd.inj, hsd.surj⟩
  let ρ : ↥F →* orth.W := e.symm.toMonoidHom.comp (QuotientGroup.mk' (E.subgroupOf F))
  refine ⟨θ, ρ, hθs, hθk, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, ?_, ?_⟩
  · have : (QuotientGroup.mk' (E.subgroupOf F)) y = 1 := by
      have h2 := congrArg e hy
      simpa [ρ] using h2
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp this)
  · have : (QuotientGroup.mk' (E.subgroupOf F)) y = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hy)
    show e.symm ((QuotientGroup.mk' (E.subgroupOf F)) y) = 1
    rw [this]
    exact map_one _
  · intro w
    obtain ⟨q, hq'⟩ := e.symm.surjective w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨y, hq'⟩
  · intro k y hky
    have hu : β (ρ y) = QuotientGroup.mk y := e.apply_symm_apply (QuotientGroup.mk y)
    obtain ⟨hkx, h2⟩ := hsd.equiv k (ρ y) y hu
    have : e.symm (β (orth.act (θ k) (ρ y))) = orth.act (θ k) (ρ y) := e.symm_apply_apply _
    rw [h2] at this
    exact this

theorem exists_fixed_mod {X E F : Subgroup G}
    (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5))) (h : IsOrthSec X E F) (hEF : E ≤ F)
    {b : G} (hbX : b ∈ X)
    (hb : ∀ l ∈ oTwoRes X, l * b * l⁻¹ * b⁻¹ ∈ F)
    (hbQ : ∀ x ∈ oTwoRes X ⊓ pCoreOf 2 X, x * b * x⁻¹ * b⁻¹ ∈ E) :
    ∃ f ∈ F, ∀ l ∈ oTwoRes X, l * (b * f) * l⁻¹ * (b * f)⁻¹ ∈ E := by
  have hs := IsModelSec.isSec h hEF
  have hc := IsModelSec.cSecIn_eq_pCoreOf h hq
  obtain ⟨θ, ρ, hθs, hθk, hρK, hρsurj, hρconj⟩ := exists_secHom h
  have hρ1 : ∀ y : ↥F, ρ y = 1 → (y : G) ∈ E := fun y hy => (hρK y).mp hy
  have hρE : ∀ y : ↥F, (y : G) ∈ E → ρ y = 1 := fun y hy => (hρK y).mpr hy
  have hFX : ∀ x ∈ X, ∀ y ∈ F, x * y * x⁻¹ ∈ F := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hs.normN hx) y).mp hy
  have hEX : ∀ x ∈ X, ∀ y ∈ E, x * y * x⁻¹ ∈ E := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hs.normL hx) y).mp hy
  have hbX' : b⁻¹ ∈ X := X.inv_mem hbX
  have hg : ∀ l : ↥(oTwoRes X), b⁻¹ * (l : G) * b * (l : G)⁻¹ ∈ F := by
    intro l
    have := hFX b⁻¹ hbX' _ (hb l l.2)
    simpa [mul_assoc] using this
  let ψ : ↥(oTwoRes X) →* Equiv.Perm (Fin 5) := θ.comp (Subgroup.inclusion (oTwoRes_le X))
  let φ : ↥(oTwoRes X) → orth.W := fun l => ρ ⟨b⁻¹ * (l : G) * b * (l : G)⁻¹, hg l⟩
  have hφ : ∀ l₁ l₂, φ (l₁ * l₂) = φ l₁ * orth.act (ψ l₁) (φ l₂) := by
    intro l₁ l₂
    have hl1 : (l₁ : G) ∈ X := oTwoRes_le X l₁.2
    have hy : (l₁ : G) * (b⁻¹ * l₂ * b * (l₂ : G)⁻¹) * (l₁ : G)⁻¹ ∈ F := hFX _ hl1 _ (hg l₂)
    have h1 : (⟨b⁻¹ * ((l₁ * l₂ : ↥(oTwoRes X)) : G) * b * ((l₁ * l₂ : ↥(oTwoRes X)) : G)⁻¹,
        hg _⟩ : ↥F) = ⟨b⁻¹ * (l₁ : G) * b * (l₁ : G)⁻¹, hg l₁⟩ *
          ⟨(l₁ : G) * (b⁻¹ * l₂ * b * (l₂ : G)⁻¹) * (l₁ : G)⁻¹, hy⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
    have h2 := hρconj ⟨l₁, hl1⟩ ⟨b⁻¹ * l₂ * b * (l₂ : G)⁻¹, hg l₂⟩ hy
    show ρ _ = ρ _ * orth.act (θ ⟨l₁, hl1⟩) (ρ _)
    rw [h1, map_mul]
    exact congrArg _ h2
  have hker : ∀ l, ψ l = 1 → φ l = 1 := by
    intro l hl
    have hl1 : (l : G) ∈ X := oTwoRes_le X l.2
    have hl2 : θ ⟨l, hl1⟩ = 1 := hl
    have hl3 : (l : G) ∈ pCoreOf 2 X := by
      rw [← hc]; exact (mem_cSecIn_iff_of_ker hθk hl1).mp hl2
    have := hEX b⁻¹ hbX' _ (hbQ l ⟨l.2, hl3⟩)
    apply hρE
    simpa [mul_assoc] using this
  have halt : ∀ l, ψ l ∈ alternatingGroup (Fin 5) := by
    intro l
    rw [← S43.map_oTwoRes_eq_alt hθs]
    exact ⟨⟨l, oTwoRes_le X l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  have hsurj : ∀ a ∈ alternatingGroup (Fin 5), ∃ l, ψ l = a := by
    intro a ha
    rw [← S43.map_oTwoRes_eq_alt hθs] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  obtain ⟨w, hw⟩ := exists_principal_of_alt ψ halt hsurj φ hφ hker
  obtain ⟨w', hw'⟩ := hρsurj w
  refine ⟨((w' : ↥F) : G)⁻¹, F.inv_mem w'.2, fun l hl => ?_⟩
  have hl1 : l ∈ X := oTwoRes_le X hl
  have hy : l * (w' : G) * l⁻¹ ∈ F := hFX l hl1 _ w'.2
  have hρy : ρ ⟨l * w' * l⁻¹, hy⟩ = orth.act (θ ⟨l, hl1⟩) w := by
    rw [← hw']; exact hρconj ⟨l, hl1⟩ w' hy
  have hc' : l * (w' : G)⁻¹ * l⁻¹ * (w' : G) ∈ F :=
    F.mul_mem (F.inv_mem hy) w'.2 |> fun h => by simpa [mul_assoc] using h
  have hprod : b⁻¹ * l * b * l⁻¹ * (l * (w' : G)⁻¹ * l⁻¹ * (w' : G)) ∈ E := by
    have hg' := F.mul_mem (hg ⟨l, hl⟩) hc'
    apply hρ1 ⟨_, hg'⟩
    rw [show (⟨_, hg'⟩ : ↥F) = ⟨b⁻¹ * l * b * l⁻¹, hg ⟨l, hl⟩⟩ * ⟨_, hc'⟩ from rfl, map_mul]
    have e1 : ρ ⟨b⁻¹ * l * b * l⁻¹, hg ⟨l, hl⟩⟩ = orth.act (θ ⟨l, hl1⟩) w * w⁻¹ := hw ⟨l, hl⟩
    have e2 : ρ ⟨l * (w' : G)⁻¹ * l⁻¹ * (w' : G), hc'⟩ = (orth.act (θ ⟨l, hl1⟩) w)⁻¹ * w := by
      have : (⟨l * (w' : G)⁻¹ * l⁻¹ * (w' : G), hc'⟩ : ↥F) = ⟨l * w' * l⁻¹, hy⟩⁻¹ * w' := by
        apply Subtype.ext
        simp [mul_assoc]
      rw [this, map_mul, map_inv, hρy, hw']
    rw [e1, e2, mul_mul_mul_comm]
    simp
  have := hEX b hbX _ hprod
  have heq : l * (b * (w' : G)⁻¹) * l⁻¹ * (b * (w' : G)⁻¹)⁻¹ =
      b * (b⁻¹ * l * b * l⁻¹ * (l * (w' : G)⁻¹ * l⁻¹ * (w' : G))) * b⁻¹ := by group
  rw [heq]
  exact this

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin
