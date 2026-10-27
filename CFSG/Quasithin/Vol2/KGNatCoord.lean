module

public import CFSG.Quasithin.Background.JonesParshallG2Derived

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall

structure LinModel (D : FFModel) (K : Type) [Field K] (M : Type) [AddCommGroup M]
    [Module K M] where
  e : ↥D.sec ⧸ D.ker.subgroupOf D.sec ≃* Multiplicative M
  lin : D.Gam → M →ₗ[K] M
  e_act : ∀ (γ : D.Gam) (m : ↥D.sec) (hm : D.act γ (m : D.Amb) ∈ D.sec),
    Multiplicative.toAdd (e (QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩)) =
      lin γ (Multiplicative.toAdd (e (QuotientGroup.mk m)))

section Coord

variable {D : FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M]
variable {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}
  {π : D.Gam →* ↥H}

theorem exists_coord (LM : LinModel D K M) (h : D.RealizesVia H U Z π) :
    ∃ f : V → M, (∀ u ∈ U, ∀ u' ∈ U, f (u * u') = f u + f u') ∧
      (∀ u ∈ U, f u = 0 ↔ u ∈ Z) ∧ (∀ m : M, ∃ u ∈ U, f u = m) ∧
      ∀ (γ : D.Gam), ∀ u ∈ U, f (((π γ : ↥H) : MulAut V) u) = LM.lin γ (f u) := by
  classical
  obtain ⟨-, -, -, hU, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  refine ⟨fun v => if hv : v ∈ U then Multiplicative.toAdd (LM.e (β ⟨v, hv⟩)) else 0,
    fun u hu u' hu' => ?_, fun u hu => ?_, fun m => ?_, fun γ u hu => ?_⟩
  · simp only [dite_eq_left hu, dite_eq_left hu', dite_eq_left (U.mul_mem hu hu')]
    rw [show (⟨u * u', U.mul_mem hu hu'⟩ : ↥U) = ⟨u, hu⟩ * ⟨u', hu'⟩ from rfl, map_mul, map_mul]
    rfl
  · simp only [dite_eq_left hu]
    rw [← hβk ⟨u, hu⟩, ← LM.e.map_eq_one_iff]
    exact ⟨fun h0 => congrArg Multiplicative.ofAdd h0, fun h1 => congrArg Multiplicative.toAdd h1⟩
  · obtain ⟨q, hq⟩ := LM.e.surjective (Multiplicative.ofAdd m)
    obtain ⟨u, hu⟩ := hβs q
    refine ⟨u, u.2, ?_⟩
    simp only [dite_eq_left u.2, Subtype.coe_eta, hu, hq]
    rfl
  · have hu' := hU (π γ) u hu
    simp only [dite_eq_left hu, dite_eq_left hu']
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, hu⟩)
    have hact := hsec γ m m.2
    rw [hβe γ ⟨u, hu⟩ m hu' hact hm.symm, LM.e_act γ m hact, hm]

end Coord

section Nat

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def linModelNat (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    LinModel (FFModel.nat Γ) K (ι → K) where
  e := secEquivOfHom (FFModel.nat Γ) (FFModel.nat Γ).sec.subtype
    (fun _ hx => Subgroup.mem_subgroupOf.mpr (Subgroup.mem_bot.mpr hx))
    (fun _ hx => Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp hx))
    (fun m => ⟨⟨m, Subgroup.mem_top m⟩, rfl⟩)
  lin := fun γ : ↥Γ => Matrix.toLin' (((γ : Matrix.GeneralLinearGroup ι K)) : Matrix ι ι K)
  e_act _ _ _ := rfl

theorem linModelNat_lin (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (γ : ↥Γ) (x : ι → K) :
    (linModelNat Γ).lin γ x = ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec x := by
  rw [show (linModelNat Γ).lin γ = Matrix.toLin' _ from rfl, Matrix.toLin'_apply]

end Nat

section Zorn

variable {F : Type} [Field F]

theorem zI_smul (c : F) (w : Ix3 → F) : zI (c • w) = c • zI w := by
  rw [q6_eta w, q6_smul, zI_q6, zI_q6, zmk_smul]
  simp

@[expose] noncomputable def zornLin (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) :
    (Ix3 → F) →ₗ[F] (Ix3 → F) where
  toFun w := zP (g (zI w))
  map_add' w w' := by rw [zI_add, map_add, zP_add]
  map_smul' c w := by rw [zI_smul, map_smul, zP_smul, RingHom.id_apply]

theorem zornLin_apply (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) (w : Ix3 → F) :
    zornLin g w = zP (g (zI w)) := rfl

variable [CharP F 2]

@[expose] noncomputable def linModelZorn (Γ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F))
    (hΓ : Γ ≤ cayleyGroup F) : LinModel (FFModel.zornQ Γ) F (Ix3 → F) where
  e := zornSecEquiv Γ
  lin := fun γ : ↥Γ => zornLin (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
  e_act := fun (γ : ↥Γ) (m : ↥(zornO0 F)) _ =>
    g2_zP_apply ⟨(γ : quasithinZorn F ≃ₗ[F] quasithinZorn F), hΓ γ.2⟩
      (Multiplicative.toAdd (m : Multiplicative (quasithinZorn F))) m.2

theorem linModelZorn_lin (Γ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F))
    (hΓ : Γ ≤ cayleyGroup F) (γ : ↥Γ) (w : Ix3 → F) :
    (linModelZorn Γ hΓ).lin γ w = zP ((γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) (zI w)) := rfl

end Zorn

end CFSG.Quasithin.Vol2.KGNat
