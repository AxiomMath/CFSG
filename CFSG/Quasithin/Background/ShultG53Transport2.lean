module

public import CFSG.Quasithin.Background.ShultG53Transport
public import CFSG.Quasithin.Background.ShultG53Iso

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.RonanG51 Equiv

variable {V₁ : Md ↥(alternatingGroup (Fin 6))} {k : Fin 2}

@[expose] noncomputable def TT (e : V₁.carrier ≃+ V4)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) m, e (V₁.ρ g m) = ρk k g (e m))
    (a : ℕ) (ha : a ≤ 5) :
    ↥(jradPow (permAct V₁) a (permCore V₁)) ≃+ ↥(Nk k a) :=
  (AddEquiv.addSubgroupMap (Theta e) _).trans
    (AddEquiv.addSubgroupCongr (Theta_jradPow_eq e he a ha))

theorem TT_coe (e : V₁.carrier ≃+ V4)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) m, e (V₁.ρ g m) = ρk k g (e m))
    (a : ℕ) (ha : a ≤ 5) (u : ↥(jradPow (permAct V₁) a (permCore V₁))) :
    ((TT e he a ha u : ↥(Nk k a)) : Fn) = Theta e (u : V₁.carrier → ZMod 2) := rfl

theorem transport_quot (e : V₁.carrier ≃+ V4)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) m, e (V₁.ρ g m) = ρk k g (e m))
    (a b : ℕ) (ha : a ≤ 5) (hb : b ≤ 5) (Ninv : InvSub (permAct (Mk k)) (Nk k a))
    {C : Md ↥(alternatingGroup (Fin 6))} (π : ↥(Nk k a) →+ C.carrier) (hs : Function.Surjective π)
    (hk : ∀ n : ↥(Nk k a), π n = 0 ↔ (n : Fn) ∈ Nk k b)
    (hρ : ∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k a)),
      π ⟨permAct (Mk k) g n, Ninv g n n.2⟩ = C.ρ g (π n)) :
    ∃ π' : ↥(jradPow (permAct V₁) a (permCore V₁)) →+ C.carrier, Function.Surjective π' ∧
      (∀ u, π' u = 0 ↔ (u : V₁.carrier → ZMod 2) ∈ jradPow (permAct V₁) b (permCore V₁)) ∧
      ∀ (g : ↥(alternatingGroup (Fin 6))) (u u' : ↥(jradPow (permAct V₁) a (permCore V₁))),
        permAct V₁ g (u : V₁.carrier → ZMod 2) = (u' : V₁.carrier → ZMod 2) →
          π' u' = C.ρ g (π' u) := by
  refine ⟨π.comp (TT e he a ha).toAddMonoidHom, hs.comp (TT e he a ha).surjective, fun u => ?_,
    fun g u u' hu => ?_⟩
  · show π (TT e he a ha u) = 0 ↔ _
    rw [hk, TT_coe, mem_jradPow_iff e he b hb]
  · show π (TT e he a ha u') = C.ρ g (π (TT e he a ha u))
    have h1 : permAct (Mk k) g ↑(TT e he a ha u) = ↑(TT e he a ha u') :=
      (congrArg (permAct (Mk k) g) (TT_coe e he a ha u)).trans ((Theta_permAct e he g _).trans
        ((congrArg (Theta e) hu).trans (TT_coe e he a ha u').symm))
    have h2 : (⟨permAct (Mk k) g ↑(TT e he a ha u), Ninv g _ (TT e he a ha u).2⟩ : ↥(Nk k a)) =
        TT e he a ha u' := Subtype.ext h1
    rw [← h2]
    exact hρ g _

theorem part3b_of_iso (e : V₁.carrier ≃+ V4)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) m, e (V₁.ρ g m) = ρk k g (e m))
    (hcov : ∃ (C : Md ↥(alternatingGroup (Fin 6))) (π : ↥(Nk k 0) →+ C.carrier),
      Function.Surjective π ∧ (∀ n : ↥(Nk k 0), π n = 0 ↔ (n : Fn) ∈ Nk k 2) ∧
      (∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k 0)),
        π ⟨permAct (Mk k) g n, N0_inv k g n n.2⟩ = C.ρ g (π n)) ∧ C.IsFiveDimCover (Mk k)) :
    ∃ (C : Md ↥(alternatingGroup (Fin 6)))
      (π : ↥(jradPow (permAct V₁) 0 (permCore V₁)) →+ C.carrier), Function.Surjective π ∧
      (∀ u, π u = 0 ↔ (u : V₁.carrier → ZMod 2) ∈ jradPow (permAct V₁) 2 (permCore V₁)) ∧
      (∀ (g : ↥(alternatingGroup (Fin 6))) (u u' : ↥(jradPow (permAct V₁) 0 (permCore V₁))),
        permAct V₁ g (u : V₁.carrier → ZMod 2) = (u' : V₁.carrier → ZMod 2) →
          π u' = C.ρ g (π u)) ∧ C.IsFiveDimCover V₁ := by
  obtain ⟨C, π, hs, hk, hρ, hC⟩ := hcov
  obtain ⟨π', hs', hk', hρ'⟩ := transport_quot e he 0 2 (by norm_num) (by norm_num)
    (N0_inv k) π hs hk hρ
  exact ⟨C, π', hs', hk', hρ', isFiveDimCover_of_iso_right' hC (iso_symm' ⟨e, he⟩)⟩

theorem part5_of_iso {V₂ : Md ↥(alternatingGroup (Fin 6))} (e : V₁.carrier ≃+ V4)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) m, e (V₁.ρ g m) = ρk k g (e m))
    (e₂ : V₂.Iso (Mk (1 - k)))
    (hcov : ∃ (C : Md ↥(alternatingGroup (Fin 6))) (π : ↥(Nk k 2) →+ C.carrier),
      Function.Surjective π ∧ (∀ n : ↥(Nk k 2), π n = 0 ↔ (n : Fn) ∈ Nk k 4) ∧
      (∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k 2)),
        π ⟨permAct (Mk k) g n, N2_inv k g n n.2⟩ = C.ρ g (π n)) ∧
        C.IsFiveDimCover (Mk (1 - k))) : Part5 V₁ V₂ := by
  obtain ⟨C, π, hs, hk, hρ, hC⟩ := hcov
  obtain ⟨π', hs', hk', hρ'⟩ := transport_quot e he 2 4 (by norm_num) (by norm_num)
    (N2_inv k) π hs hk hρ
  exact ⟨C, π', hs', hk', hρ', isFiveDimCover_of_iso_right' hC (iso_symm' e₂)⟩

end CFSG.Quasithin.ShultG53
