module

public import CFSG.Quasithin.Vol2.Ch3E213MP6EE
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model

public section

namespace CFSG.Quasithin.Ch3E213M.P6E

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252.A6 CFSG.QuasithinUnique.A6Facts

variable {A : Type} [Group A] {K : Subgroup A} [K.Normal]

@[expose] noncomputable def iota (φ : ↥K ≃* ↥A6Models.psl29) : A →* ↥A6Models.autA6 :=
  (Unc25K1.A6Model.thetaEquiv φ).toMonoidHom.comp MulAut.conjNormal

theorem iota_coe (φ : ↥K ≃* ↥A6Models.psl29) (k : K) :
    ((iota φ (k : A) : ↥A6Models.autA6) : P10) = ((φ k : ↥A6Models.psl29) : P10) := by
  have h := Unc25K1.A6Model.thetaEquiv_eq φ (MulAut.conjNormal (k : A))
    ⟨φ k, A6Facts.psl29_le_autA6 (φ k).2⟩ (fun k' => by
      have hk' : (MulAut.conjNormal (k : A)) k' = k * k' * k⁻¹ :=
        Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
      rw [hk', map_mul, map_mul, map_inv]
      rfl)
  exact congrArg Subtype.val h

theorem iota_injective (φ : ↥K ≃* ↥A6Models.psl29)
    (hC : ∀ a : A, (∀ x ∈ K, a * x = x * a) → a = 1) : Function.Injective (iota φ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker, iota, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff] at ha
  rw [Subgroup.mem_bot]
  refine hC a fun x hx => ?_
  have h1 := congrArg (fun f : MulAut ↥K => ((f ⟨x, hx⟩ : ↥K) : A)) ha
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc a * x = a * x * a⁻¹ * a := by group
    _ = x * a := by rw [h1]

theorem sign_of_not_mem {σ : Equiv.Perm (Fin 6)} (h : σ ∉ A6s) : Equiv.Perm.sign σ = -1 := by
  rw [Equiv.Perm.mem_alternatingGroup] at h
  exact (Int.units_eq_one_or _).resolve_left h

variable [Finite A]

theorem exists_chi {S E : Subgroup A} (hS2 : IsPGroup 2 S)
    (hC : ∀ a : A, (∀ x ∈ K, a * x = x * a) → a = 1) (e : ↥K ≃* M6)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = U6)
    (hEK : ((E ⊓ K).subgroupOf K).map e.toMonoidHom ≤ Ra ⊓ Rb)
    (hSE : S ≤ Subgroup.normalizer (E : Set A)) (hE2 : ∀ x ∈ E, x * x = 1)
    {v₀ : A} (hv₀ : v₀ ∈ E) (hv₀K : v₀ ∉ K) :
    ∃ χ : ↥(K ⊔ E) ≃* Equiv.Perm (Fin 6), ∀ (k : A) (hk : k ∈ K),
      (χ ⟨k, (le_sup_left : K ≤ K ⊔ E) hk⟩ : Equiv.Perm (Fin 6)) =
        (e ⟨k, hk⟩ : Equiv.Perm (Fin 6)) := by
  obtain ⟨θ, ψ, hθinj, hψθ⟩ := Unc25K1.A6Model.exists_pslEquiv
  set φ : ↥K ≃* ↥A6Models.psl29 := e.trans ψ.symm with hφ
  have hι : Function.Injective (iota φ) := iota_injective φ hC
  have hιK : ∀ k : K, ((iota φ k : A6Models.autA6) : P10) ∈ A6Models.psl29 := fun k => by
    rw [iota_coe]
    exact (φ k).2
  have hle : K ⊔ E ≤ s6.comap (A6Models.autA6.subtype.comp (iota φ)) :=
    sup_le (fun k hk => psl29_le_s6 (hιK ⟨k, hk⟩))
      (fun v hv => mem_s6_of_mem hS2 e he hEK hSE hE2 (iota φ) hι hιK hv)
  let ρ : ↥(K ⊔ E) →* ↥s6 :=
    MonoidHom.codRestrict ((A6Models.autA6.subtype.comp (iota φ)).comp (K ⊔ E).subtype) s6
      fun f => hle f.2
  let χ₀ : ↥(K ⊔ E) →* Equiv.Perm (Fin 6) := θ.comp ρ
  have hχ₀ : ∀ (k : A) (hk : k ∈ K), χ₀ ⟨k, (le_sup_left : K ≤ K ⊔ E) hk⟩ =
      (e ⟨k, hk⟩ : Equiv.Perm (Fin 6)) := by
    intro k hk
    have h1 : ρ ⟨k, (le_sup_left : K ≤ K ⊔ E) hk⟩ =
        Subgroup.inclusion psl29_le_s6 (φ ⟨k, hk⟩) := Subtype.ext (iota_coe φ ⟨k, hk⟩)
    show θ (ρ _) = _
    rw [h1, ← hψθ, hφ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hinj : Function.Injective χ₀ := by
    refine hθinj.comp fun a b h => Subtype.ext (hι (Subtype.val_injective ?_))
    exact congrArg (fun x : ↥s6 => (x : P10)) h
  have hev : ∀ σ ∈ A6s, ∃ f, χ₀ f = σ := by
    intro σ hσ
    refine ⟨⟨_, (le_sup_left : K ≤ K ⊔ E) (e.symm ⟨σ, hσ⟩).2⟩,
      (hχ₀ _ (e.symm ⟨σ, hσ⟩).2).trans ?_⟩
    simp
  have hτ : χ₀ ⟨v₀, (le_sup_right : E ≤ K ⊔ E) hv₀⟩ ∉ A6s := by
    intro h
    have h1 : χ₀ ⟨_, (le_sup_left : K ≤ K ⊔ E) (e.symm ⟨_, h⟩).2⟩ =
        χ₀ ⟨v₀, (le_sup_right : E ≤ K ⊔ E) hv₀⟩ := by
      rw [hχ₀ _ (e.symm ⟨_, h⟩).2]
      simp
    have h2 : ((e.symm ⟨_, h⟩ : K) : A) = v₀ := congrArg Subtype.val (hinj h1)
    exact hv₀K (h2 ▸ (e.symm ⟨_, h⟩).2)
  have hsurj : Function.Surjective χ₀ := by
    intro σ
    by_cases hσ : σ ∈ A6s
    · exact hev σ hσ
    · have h1 : σ * (χ₀ ⟨v₀, (le_sup_right : E ≤ K ⊔ E) hv₀⟩)⁻¹ ∈ A6s := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, sign_of_not_mem hσ,
          sign_of_not_mem hτ]
        decide
      obtain ⟨f, hf⟩ := hev _ h1
      refine ⟨f * ⟨v₀, (le_sup_right : E ≤ K ⊔ E) hv₀⟩, ?_⟩
      rw [map_mul, hf, inv_mul_cancel_right]
  exact ⟨MulEquiv.ofBijective χ₀ ⟨hinj, hsurj⟩, hχ₀⟩

end CFSG.Quasithin.Ch3E213M.P6E
