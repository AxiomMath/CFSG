module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA9
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.H1Orth

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open scoped commutatorElement

theorem h1_of_surj {Γ : Type*} [Group Γ] (ρ : Γ →* alternatingGroup (Fin 5))
    (hρ : Function.Surjective ρ) (F : Γ → orth.W)
    (hF : ∀ γ γ', F (γ * γ') = F γ * orth.act ((ρ γ : alternatingGroup (Fin 5)) : Perm (Fin 5))
      (F γ'))
    (hk : ∀ n, ρ n = 1 → F n = 1) :
    ∃ w : orth.W, ∀ γ, F γ = orth.act ((ρ γ : alternatingGroup (Fin 5)) : Perm (Fin 5)) w * w⁻¹ := by
  classical
  choose r hr using hρ
  have hshift : ∀ γ n, ρ n = 1 → F (γ * n) = F γ := by
    intro γ n hn
    rw [hF, hk n hn, map_one, mul_one]
  have hf : ∀ a b : alternatingGroup (Fin 5),
      F (r (a * b)) = F (r a) * orth.act (a : Perm (Fin 5)) (F (r b)) := by
    intro a b
    have h1 : ρ ((r a * r b)⁻¹ * r (a * b)) = 1 := by
      simp [map_mul, map_inv, hr]
    have h2 : r (a * b) = (r a * r b) * ((r a * r b)⁻¹ * r (a * b)) := by group
    calc F (r (a * b)) = F ((r a * r b) * ((r a * r b)⁻¹ * r (a * b))) := by rw [← h2]
      _ = F (r a * r b) := hshift _ _ h1
      _ = F (r a) * orth.act (a : Perm (Fin 5)) (F (r b)) := by rw [hF, hr]
  obtain ⟨w, hw⟩ := h1_alt5_orth (fun a => F (r a)) hf
  refine ⟨w, fun γ => ?_⟩
  have h1 : ρ ((r (ρ γ))⁻¹ * γ) = 1 := by simp [map_mul, map_inv, hr]
  have h2 : γ = r (ρ γ) * ((r (ρ γ))⁻¹ * γ) := by group
  calc F γ = F (r (ρ γ) * ((r (ρ γ))⁻¹ * γ)) := by rw [← h2]
    _ = F (r (ρ γ)) := hshift _ _ h1
    _ = _ := hw (ρ γ)

section Main

variable {G : Type} [Group G] [Finite G] {X K V₀ : Subgroup G} {c : G}
  (hX : X ≤ Subgroup.normalizer (K : Set G)) (hKd : KData K V₀ c)
  (ψ : ↥X →* Perm (Fin 5)) (hψs : Function.Surjective ψ)
  (hker : ∀ x : ↥X, ψ x = 1 ↔ (x : G) ∈ K)

theorem conjClosure_le_X (hcX : c ∈ X) : conjClosure X c ≤ X := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  exact X.mul_mem (X.mul_mem hg hcX) (X.inv_mem hg)

include hX hKd hψs hker in
theorem sign_conjClosure (hcX : c ∈ X) {l : G} (hl : l ∈ conjClosure X c) :
    ∃ hlX : l ∈ X, Perm.sign (ψ ⟨l, hlX⟩) = 1 := by
  have hle : conjClosure X c ≤ ((Perm.sign.comp ψ).ker).map X.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨⟨g * c * g⁻¹, X.mul_mem (X.mul_mem hg hcX) (X.inv_mem hg)⟩, ?_, rfl⟩
    show Perm.sign (ψ _) = 1
    have := odd_sign_conj hX hKd ψ hψs hker (g := ⟨g, hg⟩) hcX
    exact this
  obtain ⟨y, hy, rfl⟩ := hle hl
  exact ⟨y.2, hy⟩

include hX hKd hψs hker in
theorem exists_o_of_cocycle (hK2 : IsPGroup 2 K) (hcX : c ∈ X) {q : G} (hq : q ∈ K) :
    ∃ o ∈ normClosure X V₀, ∀ l ∈ conjClosure X c,
      l * q * l⁻¹ * q⁻¹ = l * o * l⁻¹ * o⁻¹ := by
  have hs := isSec_normClosure hX hKd
  obtain ⟨e⟩ := normModel_iso_orth hX hKd ψ hψs hker hK2 hcX
  have hLX := conjClosure_le_X (X := X) (c := c) hcX
  let B : ↥(normClosure X V₀) →* orth.W := e.toMulEquiv.toMonoidHom.comp hs.proj
  have hBinj : Function.Injective B := by
    intro a b hab
    have h1 : hs.proj a = hs.proj b := e.toMulEquiv.injective hab
    rw [hs.proj_eq_proj_iff] at h1
    have h2 : (a : G)⁻¹ * (b : G) = 1 := by simpa using h1
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  have hBsurj : Function.Surjective B := e.toMulEquiv.surjective.comp hs.proj_surjective
  have hBact : ∀ (y : ↥X) (n : ↥(normClosure X V₀)),
      B (hs.conjN y n) = orth.act (ψ y) (B n) := by
    intro y n
    have h := e.map_act (ψ y) (hs.proj n)
    have h2 := secModule_act_proj hs ψ hψs (ker_le_cSec_normClosure hX hKd ψ hψs hker) y n
    exact (congrArg e.toMulEquiv h2).symm.trans h
  have hsg : ∀ l : ↥(conjClosure X c), Perm.sign (ψ ⟨l.1, hLX l.2⟩) = 1 := fun l =>
    (sign_conjClosure hX hKd ψ hψs hker hcX l.2).choose_spec
  let ρ0 : ↥(conjClosure X c) →* Perm (Fin 5) := ψ.comp (Subgroup.inclusion hLX)
  let ρ : ↥(conjClosure X c) →* alternatingGroup (Fin 5) :=
    ρ0.codRestrict (alternatingGroup (Fin 5)) (fun l => Perm.mem_alternatingGroup.mpr (hsg l))
  have hcne := psi_c_ne_one hX hKd ψ hψs hker hK2 hcX
  have hρsurj : Function.Surjective ρ := by
    intro a
    obtain ⟨y, hy, hya⟩ := alt5_le_map_conjClosure ψ hψs hcX hKd.c3 hcne a.2
    exact ⟨⟨y.1, hy⟩, Subtype.ext hya⟩
  have hmemN : ∀ l ∈ conjClosure X c, l * q * l⁻¹ * q⁻¹ ∈ normClosure X V₀ := fun l hl =>
    (comm_conjClosure_mem hX hKd hcX hl).2 q hq
  let F : ↥(conjClosure X c) → orth.W := fun l => B ⟨l * q * l⁻¹ * q⁻¹, hmemN l l.2⟩
  have hF : ∀ l l', F (l * l') = F l * orth.act ((ρ l : alternatingGroup (Fin 5)) : Perm (Fin 5))
      (F l') := by
    intro l l'
    have e1 : F (l * l') = B (hs.conjN ⟨l.1, hLX l.2⟩
        ⟨l'.1 * q * l'.1⁻¹ * q⁻¹, hmemN _ l'.2⟩ * ⟨l.1 * q * l.1⁻¹ * q⁻¹, hmemN _ l.2⟩) := by
      refine congrArg B (Subtype.ext ?_)
      show (l.1 * l'.1) * q * (l.1 * l'.1)⁻¹ * q⁻¹ =
        l.1 * (l'.1 * q * l'.1⁻¹ * q⁻¹) * l.1⁻¹ * (l.1 * q * l.1⁻¹ * q⁻¹)
      group
    show F (l * l') = F l * orth.act (ψ ⟨l.1, hLX l.2⟩) (F l')
    rw [e1, map_mul, hBact]
    exact mul_comm _ _
  have hk : ∀ n, ρ n = 1 → F n = 1 := by
    intro n hn
    have hn1 : ψ ⟨n.1, hLX n.2⟩ = 1 := by
      exact congrArg Subtype.val hn
    have hnK : n.1 ∈ K := (hker _).mp hn1
    set m : ↥(normClosure X V₀) := ⟨n.1 * q * n.1⁻¹ * q⁻¹, hmemN _ n.2⟩ with hm
    have hfix : B m ∈ fixW orth (alternatingGroup (Fin 5)) := by
      intro σ hσ
      obtain ⟨l', hl'⟩ := hρsurj ⟨σ, hσ⟩
      have hl'σ : ψ ⟨l'.1, hLX l'.2⟩ = σ := congrArg Subtype.val hl'
      rw [← hl'σ, ← hBact]
      congr 1
      apply Subtype.ext
      show l'.1 * (n.1 * q * n.1⁻¹ * q⁻¹) * l'.1⁻¹ = n.1 * q * n.1⁻¹ * q⁻¹
      have := derived_commute hX hKd hnK hq l'.2
      calc l'.1 * (n.1 * q * n.1⁻¹ * q⁻¹) * l'.1⁻¹
          = (l'.1 * (n.1 * q * n.1⁻¹ * q⁻¹)) * l'.1⁻¹ := by group
        _ = ((n.1 * q * n.1⁻¹ * q⁻¹) * l'.1) * l'.1⁻¹ := by rw [← this]
        _ = _ := by group
    rw [fixW_orth_alt5, Subgroup.mem_bot] at hfix
    exact hfix
  obtain ⟨w, hw⟩ := h1_of_surj ρ hρsurj F hF hk
  obtain ⟨o, rfl⟩ := hBsurj w
  refine ⟨o.1, o.2, fun l hl => ?_⟩
  have h1 := hw ⟨l, hl⟩
  have h2 : F ⟨l, hl⟩ = B (hs.conjN ⟨l, hLX hl⟩ o * o⁻¹) := by
    rw [h1, map_mul, map_inv, hBact]
    rfl
  have h3 := hBinj h2
  exact congrArg Subtype.val h3

include hX hKd hψs hker in
theorem exists_decomp (hK2 : IsPGroup 2 K) (hcX : c ∈ X) {q : G} (hq : q ∈ K) :
    ∃ y ∈ K ⊓ Subgroup.centralizer (conjClosure X c : Set G), ∃ o ∈ normClosure X V₀,
      q = y * o := by
  obtain ⟨o, ho, hE⟩ := exists_o_of_cocycle hX hKd ψ hψs hker hK2 hcX hq
  have hoK : o ∈ K := normClosure_le_K hX hKd ho
  have hoq : Commute o q := (normClosure_central hX hKd ho hq)
  refine ⟨q * o⁻¹, ⟨K.mul_mem hq (K.inv_mem hoK), Subgroup.mem_centralizer_iff.mpr ?_⟩, o, ho,
    by group⟩
  intro l hl
  have hp : l * o * l⁻¹ ∈ normClosure X V₀ :=
    conj_mem_normClosure ho ((comm_conjClosure_mem hX hKd hcX hl).1)
  have hpq : Commute (l * o * l⁻¹) q := normClosure_central hX hKd hp hq
  have hpo : Commute (l * o * l⁻¹) o := normClosure_central hX hKd hp hoK
  have key : l * (q * o⁻¹) * l⁻¹ = q * o⁻¹ := by
    have hE' := hE l hl
    set p := l * o * l⁻¹ with hpdef
    have hu : l * q * l⁻¹ = p * o⁻¹ * q := by
      have : l * q * l⁻¹ * q⁻¹ = p * o⁻¹ := hE'
      calc l * q * l⁻¹ = (l * q * l⁻¹ * q⁻¹) * q := by group
        _ = p * o⁻¹ * q := by rw [this]
    calc l * (q * o⁻¹) * l⁻¹ = (l * q * l⁻¹) * (l * o * l⁻¹)⁻¹ := by group
      _ = p * o⁻¹ * q * p⁻¹ := by rw [hu]
      _ = (o⁻¹ * p) * q * p⁻¹ := by rw [(hpo.inv_right).eq]
      _ = o⁻¹ * (p * q * p⁻¹) := by group
      _ = o⁻¹ * q := by rw [hpq.eq]; group
      _ = q * o⁻¹ := (hoq.inv_left).eq
  calc l * (q * o⁻¹) = (l * (q * o⁻¹) * l⁻¹) * l := by group
    _ = (q * o⁻¹) * l := by rw [key]

end Main

end CFSG.Quasithin.F53
