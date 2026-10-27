module

public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Background.Sp4InfNorm
public import CFSG.Quasithin.Background.B5FinSp

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
open CFSG.Quasithin.H (StdMod)

namespace S6B

noncomputable abbrev thetaTwo : Equiv.Perm (Fin 6) ≃* ↥(StatedSp 2 (ZMod 2)) :=
  B5FinSp.theta (RingEquiv.refl (ZMod 2))

theorem sum_eq_zero_of_mem {x : Fin 6 → ZMod 2} (hx : x ∈ evenWeight 6) : ∑ i, x i = 0 := by
  simpa [evenWeight] using hx

theorem mem_of_sum_eq_zero {x : Fin 6 → ZMod 2} (hx : ∑ i, x i = 0) : x ∈ evenWeight 6 := by
  simpa [evenWeight] using hx

@[expose] def chiEven : ↥(evenWeight 6) →+ (Fin 4 → ZMod 2) where
  toFun x := B5FinSp.chi x
  map_zero' := B5FinSp.chi_const 0
  map_add' x y := B5FinSp.chi_add x y

theorem constWeight_le_ker_chiEven : constWeight 6 ≤ chiEven.ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  have h : (x : Fin 6 → ZMod 2) = fun _ => (x : Fin 6 → ZMod 2) 0 := funext fun i => hx i 0
  show B5FinSp.chi (x : Fin 6 → ZMod 2) = 0
  rw [h]
  exact B5FinSp.chi_const _

@[expose] def heartChi : AltHeart 6 →+ (Fin 4 → ZMod 2) :=
  QuotientAddGroup.lift (constWeight 6) chiEven constWeight_le_ker_chiEven

theorem heartChi_mk (x : ↥(evenWeight 6)) :
    heartChi (QuotientAddGroup.mk x : AltHeart 6) = B5FinSp.chi x := rfl

theorem heartChi_bijective : Function.Bijective heartChi := by
  refine ⟨(injective_iff_map_eq_zero heartChi).2 fun y hy => ?_, fun v => ?_⟩
  · obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [heartChi_mk] at hy
    rw [QuotientAddGroup.eq_zero_iff]
    intro i j
    rcases (B5FinSp.chi_eq_zero_iff x (sum_eq_zero_of_mem x.2)).1 hy with h | h <;> simp [h]
  · exact ⟨QuotientAddGroup.mk ⟨B5FinSp.phi v, mem_of_sum_eq_zero (B5FinSp.sum_phi v)⟩,
      B5FinSp.chi_phi v⟩

@[expose] def heartCrd : AltHeart 6 →+ (Fin 2 ⊕ Fin 2 → ZMod 2) where
  toFun y := B5FinSp.lfun (RingEquiv.refl (ZMod 2)) (heartChi y)
  map_zero' := by
    funext a
    simp [B5FinSp.lfun]
  map_add' y y' := by
    rw [map_add, B5FinSp.lfun_add]

theorem heartCrd_apply (y : AltHeart 6) :
    heartCrd y = B5FinSp.lfun (RingEquiv.refl (ZMod 2)) (heartChi y) := rfl

theorem heartCrd_bijective : Function.Bijective heartCrd :=
  ⟨(B5FinSp.lfun_injective _).comp heartChi_bijective.1,
    (B5FinSp.lfun_surjective _).comp heartChi_bijective.2⟩

theorem heartCrd_perm (σ : Equiv.Perm (Fin 6)) (x : ↥(evenWeight 6)) :
    heartCrd (QuotientAddGroup.mk (permWeight 6 σ x) : AltHeart 6) =
      (((thetaTwo σ : ↥(StatedSp 2 (ZMod 2))) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ
        heartCrd (QuotientAddGroup.mk x : AltHeart 6) := by
  have h1 := B5FinSp.chi_permute (B5FinSp.omegaEquiv.symm σ) x (sum_eq_zero_of_mem x.2)
  rw [← B5FinSp.omegaEquiv_apply, MulEquiv.apply_symm_apply] at h1
  rw [heartCrd_apply, heartCrd_apply, heartChi_mk, heartChi_mk, B5FinSp.theta_mulVec_lfun, ← h1]
  rfl

@[expose] def crdHom : Multiplicative (AltHeart 6) →* StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  AddMonoidHom.toMultiplicative heartCrd

theorem toAdd_crdHom (y : Multiplicative (AltHeart 6)) :
    Multiplicative.toAdd (crdHom y) = heartCrd (Multiplicative.toAdd y) := rfl

theorem crdHom_bijective : Function.Bijective crdHom := by
  refine ⟨fun y y' h => ?_, fun w => ?_⟩
  · exact Multiplicative.toAdd.injective (heartCrd_bijective.1 (congrArg Multiplicative.toAdd h))
  · obtain ⟨y, hy⟩ := heartCrd_bijective.2 (Multiplicative.toAdd w)
    exact ⟨Multiplicative.ofAdd y, Multiplicative.toAdd.injective hy⟩

theorem crdHom_conj {G : Type} [Group G] {L U : Subgroup G}
    {α : ↥L →* alternatingGroup (Fin 6)} {β : ↥U →* Multiplicative (AltHeart 6)}
    (hβ : ∀ (a : ↥L) (u v : ↥U), (v : G) = a * u * a⁻¹ →
      ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight 6 (α a : Equiv.Perm (Fin 6)) x) : AltHeart 6) =
          Multiplicative.toAdd (β v))
    (a : ↥L) (u v : ↥U) (huv : (v : G) = a * u * a⁻¹) :
    Multiplicative.toAdd (crdHom (β v)) =
      (((thetaTwo (α a : Equiv.Perm (Fin 6)) : ↥(StatedSp 2 (ZMod 2))) :
        GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (crdHom (β u)) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β u))
  rw [toAdd_crdHom, toAdd_crdHom, ← hβ a u v huv x hx, ← hx, heartCrd_perm]

theorem gl_ext {ι : Type} [Fintype ι] [DecidableEq ι] {A B : GL ι (ZMod 2)}
    (h : ∀ v : ι → ZMod 2, (A : Matrix ι ι (ZMod 2)) *ᵥ v = (B : Matrix ι ι (ZMod 2)) *ᵥ v) :
    A = B :=
  Units.ext (Matrix.ext_iff_mulVec.mpr h)

theorem exists_matHom {G : Type} [Group G] {M U Z : Subgroup G}
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) (hMZ : M ≤ Subgroup.normalizer (Z : Set G))
    (f : ↥U →* StdMod (Fin 2 ⊕ Fin 2) (ZMod 2)) (hf : Function.Surjective f)
    (hfk : f.ker = Z.subgroupOf U) :
    ∃ A : ↥M →* GL (Fin 2 ⊕ Fin 2) (ZMod 2), ∀ (m : ↥M) (u v : ↥U), (v : G) = m * u * m⁻¹ →
      Multiplicative.toAdd (f v) =
        (A m : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ Multiplicative.toAdd (f u) := by
  let c : ↥M → ↥U →* ↥U := fun m =>
    { toFun := fun u => ⟨m * u * m⁻¹, (Subgroup.mem_normalizer_iff.mp (hMU m.2) u).mp u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u u' => Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group) }
  have hc : ∀ (m : ↥M) (u : ↥U), ((c m u : ↥U) : G) = m * u * m⁻¹ := fun _ _ => rfl
  have hker : ∀ m : ↥M, f.ker ≤ (f.comp (c m)).ker := by
    intro m u hu
    rw [hfk, Subgroup.mem_subgroupOf] at hu
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hfk, Subgroup.mem_subgroupOf,
      hc]
    exact (Subgroup.mem_normalizer_iff.mp (hMZ m.2) u).mp hu
  let g : ↥M → StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) →* StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) := fun m =>
    f.liftOfSurjective hf ⟨f.comp (c m), hker m⟩
  have hg : ∀ (m : ↥M) (u : ↥U), g m (f u) = f (c m u) := fun m u =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨f.comp (c m), hker m⟩ u
  have hgmul : ∀ (m m' : ↥M) w, g (m * m') w = g m (g m' w) := by
    intro m m' w
    obtain ⟨u, rfl⟩ := hf w
    rw [hg, hg, hg]
    congr 1
    apply Subtype.ext
    simp only [hc, Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]
    group
  have hgone : ∀ w, g 1 w = w := by
    intro w
    obtain ⟨u, rfl⟩ := hf w
    rw [hg]
    congr 1
    apply Subtype.ext
    simp [hc]
  let ρ : ↥M →* MulAut (StdMod (Fin 2 ⊕ Fin 2) (ZMod 2)) :=
    { toFun := fun m =>
        { toFun := g m
          invFun := g m⁻¹
          left_inv := fun w => by rw [← hgmul, inv_mul_cancel, hgone]
          right_inv := fun w => by rw [← hgmul, mul_inv_cancel, hgone]
          map_mul' := (g m).map_mul }
      map_one' := MulEquiv.ext hgone
      map_mul' := fun m m' => MulEquiv.ext (hgmul m m') }
  let E : GL (Fin 2 ⊕ Fin 2) (ZMod 2) ≃* MulAut (StdMod (Fin 2 ⊕ Fin 2) (ZMod 2)) :=
    MulEquiv.ofBijective H.matHom ⟨H.matHom_injective, fun a =>
      (Sp4Inf.exists_matAut_zmod_two a).imp fun A h => h.symm⟩
  refine ⟨E.symm.toMonoidHom.comp ρ, fun m u v huv => ?_⟩
  have hE : H.matAut (E.symm (ρ m)) = ρ m := E.apply_symm_apply (ρ m)
  have hv : v = c m u := Subtype.ext huv
  have h1 := congrArg (fun φ : MulAut (StdMod (Fin 2 ⊕ Fin 2) (ZMod 2)) =>
    Multiplicative.toAdd (φ (f u))) hE
  rw [hv, ← hg]
  exact h1.symm

theorem sign_iotaSp_thetaTwo (σ : Equiv.Perm (Fin 6)) :
    Equiv.Perm.sign (Sp4Inf.iotaSp (thetaTwo σ)) = Equiv.Perm.sign σ := by
  have hs : Function.Surjective
      (Equiv.Perm.sign.comp (Sp4Inf.iotaSp.toMonoidHom.comp thetaTwo.toMonoidHom)) := by
    intro x
    obtain ⟨τ, hτ⟩ := Equiv.Perm.sign_surjective (Fin 6) x
    exact ⟨thetaTwo.symm (Sp4Inf.iotaSp.symm τ), by simp [hτ]⟩
  have h := Equiv.Perm.eq_sign_of_surjective_hom hs
  exact DFunLike.congr_fun h σ

end S6B

theorem sp4Two_of_altNaturalSection {G : Type} [Group G]
    {M L U Z : Subgroup G} {N : Subgroup ↥L} (hLM : L ≤ M)
    (hML : M ≤ Subgroup.normalizer (L : Set G)) (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hMZ : M ≤ Subgroup.normalizer (Z : Set G)) (hZU : Z ≤ U)
    (hA : IsAltNaturalSection L U Z N 6) :
    ∃ α : ↥M →* ↥(StatedSp 2 (ZMod 2)), IsSumOfNaturalModulesVia M U Z α false 1 ∧
      (Function.Surjective α ∨ ∀ m : ↥M, ∃ l : ↥L, α m = α ⟨l, hLM l.2⟩) := by
  obtain ⟨hLU, α₀, hα₀, -, β₀, hβ₀, hβ₀k, hβ₀e⟩ := hA
  set f : ↥U →* StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) := S6B.crdHom.comp β₀ with hf_def
  have hf : Function.Surjective f := S6B.crdHom_bijective.2.comp hβ₀
  have hfk : f.ker = Z.subgroupOf U := by
    rw [hf_def, MonoidHom.ker_comp_of_injective _ _ S6B.crdHom_bijective.1, hβ₀k]
  obtain ⟨A, hAf⟩ := S6B.exists_matHom hMU hMZ f hf hfk
  have hAL : ∀ a : ↥L, A ⟨a, hLM a.2⟩ =
      ((S6B.thetaTwo (α₀ a : Equiv.Perm (Fin 6)) : ↥(StatedSp 2 (ZMod 2))) :
        GL (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
    intro a
    refine S6B.gl_ext fun w => ?_
    obtain ⟨u, hu⟩ := hf (Multiplicative.ofAdd w)
    let v : ↥U := ⟨a * u * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hLU a.2) u).mp u.2⟩
    have h1 := hAf ⟨a, hLM a.2⟩ u v rfl
    have h2 := S6B.crdHom_conj hβ₀e a u v rfl
    have hw : Multiplicative.toAdd (f u) = w := by rw [hu]; rfl
    rw [← hw, ← h1]
    exact h2
  set D : Subgroup ↥(StatedSp 2 (ZMod 2)) :=
    (alternatingGroup (Fin 6)).comap Sp4Inf.iotaSp.toMonoidHom
  have hD : Sp4Inf.IsAlt6Sub D := Sp4Inf.isAlt6Sub_comap
  have hmemD' : ∀ γ : ↥(StatedSp 2 (ZMod 2)), γ ∈ D ↔ Equiv.Perm.sign (Sp4Inf.iotaSp γ) = 1 :=
    fun γ => Equiv.Perm.mem_alternatingGroup
  have hmemD : ∀ γ : ↥(StatedSp 2 (ZMod 2)),
      γ ∈ D ↔ ∃ a : ↥L, S6B.thetaTwo (α₀ a : Equiv.Perm (Fin 6)) = γ := by
    intro γ
    constructor
    · intro hγ
      have h1 : S6B.thetaTwo.symm γ ∈ alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup, ← S6B.sign_iotaSp_thetaTwo,
          MulEquiv.apply_symm_apply]
        exact (hmemD' γ).mp hγ
      obtain ⟨a, ha⟩ := hα₀ ⟨_, h1⟩
      refine ⟨a, ?_⟩
      rw [ha]
      exact MulEquiv.apply_symm_apply _ _
    · rintro ⟨a, rfl⟩
      rw [hmemD', S6B.sign_iotaSp_thetaTwo]
      exact Equiv.Perm.mem_alternatingGroup.mp (α₀ a).2
  have hconj : ∀ (m : ↥M) (a : ↥L), ∃ b : ↥L,
      A m * A ⟨a, hLM a.2⟩ * (A m)⁻¹ = A ⟨b, hLM b.2⟩ := by
    intro m a
    refine ⟨⟨m * a * m⁻¹, (Subgroup.mem_normalizer_iff.mp (hML m.2) a).mp a.2⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hSp : ∀ m : ↥M, A m ∈ StatedSp 2 (ZMod 2) := by
    intro m
    have h₁ : ∀ γ ∈ D, ∃ δ ∈ D, A m * (γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * (A m)⁻¹ =
        (δ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
      intro γ hγ
      obtain ⟨a, rfl⟩ := (hmemD γ).mp hγ
      obtain ⟨b, hb⟩ := hconj m a
      exact ⟨_, (hmemD _).mpr ⟨b, rfl⟩, by rw [← hAL, hb, hAL]⟩
    have h₂ : ∀ δ ∈ D, ∃ γ ∈ D, (A m)⁻¹ * (δ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * A m =
        (γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
      intro δ hδ
      obtain ⟨a, rfl⟩ := (hmemD δ).mp hδ
      obtain ⟨b, hb⟩ := hconj m⁻¹ a
      rw [map_inv, inv_inv] at hb
      exact ⟨_, (hmemD _).mpr ⟨b, rfl⟩, by rw [← hAL, hb, hAL]⟩
    obtain ⟨s, hs⟩ := Sp4Inf.mem_statedSp_of_normalizes hD (A m) h₁ h₂
    rw [← hs]
    exact s.2
  let α : ↥M →* ↥(StatedSp 2 (ZMod 2)) := A.codRestrict (StatedSp 2 (ZMod 2)) hSp
  have hα : ∀ m : ↥M, ((α m : ↥(StatedSp 2 (ZMod 2))) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) = A m :=
    fun _ => rfl
  have hαL : ∀ a : ↥L, α ⟨a, hLM a.2⟩ = S6B.thetaTwo (α₀ a : Equiv.Perm (Fin 6)) :=
    fun a => Subtype.ext (hAL a)
  refine ⟨α, ⟨hMU, hZU, ?_⟩, ?_⟩
  ·
    let e : Multiplicative (Fin 1 → Fin 2 ⊕ Fin 2 → ZMod 2) ≃*
        StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) :=
      AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (Fin 2 ⊕ Fin 2 → ZMod 2))
    refine ⟨e.symm.toMonoidHom.comp f, e.symm.surjective.comp hf, ?_, ?_⟩
    · rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective, hfk]
    · intro m u v huv i
      have h := hAf m u v huv
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simpa [moduleAct, e, hα] using h
  ·
    by_cases hall : ∀ m : ↥M, α m ∈ D
    · right
      intro m
      obtain ⟨a, ha⟩ := (hmemD _).mp (hall m)
      exact ⟨a, by rw [hαL, ha]⟩
    · left
      obtain ⟨m₀, hm₀⟩ := not_forall.mp hall
      intro y
      by_cases hy : y ∈ D
      · obtain ⟨a, ha⟩ := (hmemD y).mp hy
        exact ⟨⟨a, hLM a.2⟩, by rw [hαL, ha]⟩
      · have h1 : Equiv.Perm.sign (Sp4Inf.iotaSp y) = -1 :=
          (Int.units_eq_one_or _).resolve_left (mt (hmemD' y).mpr hy)
        have h2 : Equiv.Perm.sign (Sp4Inf.iotaSp (α m₀)) = -1 :=
          (Int.units_eq_one_or _).resolve_left (mt (hmemD' _).mpr hm₀)
        have hy' : y * (α m₀)⁻¹ ∈ D := by
          rw [hmemD', map_mul, map_inv, map_mul, map_inv, h1, h2]
          exact mul_inv_cancel _
        obtain ⟨a, ha⟩ := (hmemD _).mp hy'
        refine ⟨⟨a, hLM a.2⟩ * m₀, ?_⟩
        rw [map_mul, hαL, ha, inv_mul_cancel_right]

end CFSG.Quasithin.MS93
