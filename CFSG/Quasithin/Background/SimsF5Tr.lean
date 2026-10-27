module

public import CFSG.Quasithin.Background.SimsF5Bridge
public import CFSG.Quasithin.Background.SimsF5Model4
public import CFSG.Quasithin.Background.SimsF5Inv

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Quasithin.H13.F431.U42Aut
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Generic

variable {A B : Type} [Group A] [Group B] {ψ : A →* B}

theorem tr_mem_map_iff (hψ : Function.Injective ψ) {H : Subgroup A} {x : A} :
    ψ x ∈ H.map ψ ↔ x ∈ H := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← hψ hyx]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem tr_map_inf (hψ : Function.Injective ψ) (H K : Subgroup A) :
    (H ⊓ K).map ψ = H.map ψ ⊓ K.map ψ := by
  ext y
  constructor
  · rintro ⟨x, ⟨hH, hK⟩, rfl⟩
    exact ⟨⟨x, hH, rfl⟩, ⟨x, hK, rfl⟩⟩
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, (tr_mem_map_iff hψ).1 hy⟩, rfl⟩

theorem tr_map_centralizer (hψ : Function.Injective ψ) (S : Set A) :
    (Subgroup.centralizer S).map ψ = ψ.range ⊓ Subgroup.centralizer (ψ '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hx s hs]
  · rintro ⟨⟨x, rfl⟩, hc⟩
    refine ⟨x, Subgroup.mem_centralizer_iff.2 fun s hs => hψ ?_, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.1 hc (ψ s) ⟨s, hs, rfl⟩

theorem tr_map_centralizer_singleton (hψ : Function.Injective ψ) (a : A) :
    (Subgroup.centralizer ({a} : Set A)).map ψ =
      ψ.range ⊓ Subgroup.centralizer ({ψ a} : Set B) := by
  rw [tr_map_centralizer hψ, Set.image_singleton]

theorem tr_map_normalizer (hψ : Function.Injective ψ) (H : Subgroup A) :
    (Subgroup.normalizer (H : Set A)).map ψ =
      ψ.range ⊓ Subgroup.normalizer ((H.map ψ : Subgroup B) : Set B) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, Subgroup.mem_normalizer_iff.2 fun b => ⟨?_, ?_⟩⟩
    · rintro ⟨h, hh, rfl⟩
      refine ⟨x * h * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx h).1 hh, ?_⟩
      simp
    · rintro ⟨h, hh, hhb⟩
      refine ⟨x⁻¹ * h * x, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * h * x)).2
        apply this
        simpa [mul_assoc] using hh
      · rw [map_mul, map_mul, hhb, map_inv]
        group
  · rintro ⟨⟨x, rfl⟩, hN⟩
    refine ⟨x, Subgroup.mem_normalizer_iff.2 fun h => ?_, rfl⟩
    have := Subgroup.mem_normalizer_iff.1 hN (ψ h)
    rw [tr_mem_map_iff hψ, show ψ x * ψ h * (ψ x)⁻¹ = ψ (x * h * x⁻¹) by simp,
      tr_mem_map_iff hψ] at this
    exact this

theorem tr_map_oTwoRes (hψ : Function.Injective ψ) (K : Subgroup A) :
    (oTwoRes K).map ψ = oTwoRes (K.map ψ) := by
  unfold oTwoRes
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, m, hm, hxm⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, m, hm, by rw [← map_pow, hxm, map_one]⟩
  · rintro ⟨⟨x, hx, rfl⟩, m, hm, hxm⟩
    refine ⟨x, ⟨hx, m, hm, hψ ?_⟩, rfl⟩
    rw [map_pow, hxm, map_one]

theorem tr_isConj_iff (hψ : Function.Injective ψ) {a b : A} :
    IsConj a b ↔ ∃ g ∈ ψ.range, g * ψ a * g⁻¹ = ψ b := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨ψ c, ⟨c, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨c, rfl⟩, h⟩
    refine ⟨c, hψ ?_⟩
    rw [← h]
    simp

theorem tr_image_isConj (hψ : Function.Injective ψ) (a : A) :
    ψ '' {x : A | IsConj a x} = {y : B | ∃ g ∈ ψ.range, g * ψ a * g⁻¹ = y} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (tr_isConj_iff hψ).1 hx
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c * a * c⁻¹, (tr_isConj_iff hψ).2 ⟨ψ c, ⟨c, rfl⟩, by simp⟩, by simp⟩

theorem tr_isSylowOf (hψ : Function.Injective ψ) {p : ℕ} {S H : Subgroup A}
    (h : IsSylowOf p S H) : IsSylowOf p (S.map ψ) (H.map ψ) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map ψ, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective _ _ hψ]
  exact h.2.2

theorem tr_equiv (hψ : Function.Injective ψ) (H : Subgroup A) : Nonempty (↥H ≃* ↥(H.map ψ)) :=
  ⟨H.equivMapOfInjective ψ hψ⟩

end Generic

section Model

@[expose] noncomputable def lamG : Ah →* GL6 := M0Dot.subtype.comp lamA.toMonoidHom

theorem lamG_apply (a : Ah) : lamG a = ((lamA a : ↥M0Dot) : GL6) := rfl

theorem lamG_injective : Function.Injective lamG :=
  Subtype.val_injective.comp lamA.injective

theorem lamG_P1h : P1h.map lamG = M1Dot := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (lamA_mem_M1Dot a).2 ha
  · intro hg
    obtain ⟨a, ha⟩ := mc_exists_lamA (M1Dot_le_M0Dot hg)
    exact ⟨a, (lamA_mem_M1Dot a).1 (ha ▸ hg), ha⟩

theorem lamG_P2h : P2h.map lamG = M2Dot := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (lamA_mem_M2Dot a).2 ha
  · intro hg
    obtain ⟨a, ha⟩ := mc_exists_lamA (M2Dot_le_M0Dot hg)
    exact ⟨a, (lamA_mem_M2Dot a).1 (ha ▸ hg), ha⟩

theorem lamG_top : (⊤ : Subgroup Ah).map lamG = M0Dot := by
  ext g
  constructor
  · rintro ⟨a, -, rfl⟩
    exact (lamA a).2
  · intro hg
    obtain ⟨a, ha⟩ := mc_exists_lamA hg
    exact ⟨a, Subgroup.mem_top a, ha⟩

theorem M1Dot_sup_M2Dot : M1Dot ⊔ M2Dot = M0Dot := by
  rw [← lamG_P1h, ← lamG_P2h, ← Subgroup.map_sup, sup_P1h_P2h, lamG_top]

theorem tr_VA : VA.map lamG = Q2Dot := by
  rw [← pCoreOf_P2h_eq, ← br_pCoreOf_map lamG_injective, lamG_P2h, pCoreOf_M2Dot]

end Model

section Psi

variable {M : Type} [Group M]

@[expose] noncomputable def psiOf (Φ : M ≃* ↥MDot) : M →* GL6 :=
  MDot.subtype.comp Φ.toMonoidHom

theorem psiOf_apply (Φ : M ≃* ↥MDot) (x : M) : psiOf Φ x = ((Φ x : ↥MDot) : GL6) := rfl

theorem psiOf_injective (Φ : M ≃* ↥MDot) : Function.Injective (psiOf Φ) :=
  Subtype.val_injective.comp Φ.injective

theorem psiOf_range (Φ : M ≃* ↥MDot) : (psiOf Φ).range = MDot := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact (Φ x).2
  · intro hg
    exact ⟨Φ.symm ⟨g, hg⟩, by rw [psiOf_apply, MulEquiv.apply_symm_apply]⟩

theorem psiOf_symm (Φ : M ≃* ↥MDot) {g : GL6} (hg : g ∈ MDot) : psiOf Φ (Φ.symm ⟨g, hg⟩) = g := by
  rw [psiOf_apply, MulEquiv.apply_symm_apply]

theorem tr_cen (Φ : M ≃* ↥MDot) (a : M) :
    (Subgroup.centralizer ({a} : Set M)).map (psiOf Φ) =
      MDot ⊓ Subgroup.centralizer ({psiOf Φ a} : Set GL6) := by
  rw [tr_map_centralizer_singleton (psiOf_injective Φ), psiOf_range]

theorem tr_normalizer (Φ : M ≃* ↥MDot) (H : Subgroup M) :
    (Subgroup.normalizer (H : Set M)).map (psiOf Φ) =
      MDot ⊓ Subgroup.normalizer ((H.map (psiOf Φ) : Subgroup GL6) : Set GL6) := by
  rw [tr_map_normalizer (psiOf_injective Φ), psiOf_range]

end Psi

section Abstract

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {Tb : Subgroup E}
  {fb : ↥(M₁ ⊓ M₂)} {μ : Cpl M₁ M₂ ↥M0Dot} {zb : ↥M₁} {Φ : M ≃* ↥MDot}

@[expose] def PhiExt (β : Cpl M₁ M₂ Y) (ε : Y →* M) (μ : Cpl M₁ M₂ ↥M0Dot) (Φ : M ≃* ↥MDot) :
    Prop :=
  (∀ b : ↥M₁, ((Φ (ε (β.φ1 b)) : ↥MDot) : GL6) = ((μ.φ1 b : ↥M0Dot) : GL6)) ∧
    (∀ b : ↥M₂, ((Φ (ε (β.φ2 b)) : ↥MDot) : GL6) = ((μ.φ2 b : ↥M0Dot) : GL6))

theorem tr_phi1 (hΦ : PhiExt β ε μ Φ) (b : ↥M₁) :
    psiOf Φ (ε (β.φ1 b)) = ((μ.φ1 b : ↥M0Dot) : GL6) :=
  hΦ.1 b

theorem tr_phi2 (hΦ : PhiExt β ε μ Φ) (b : ↥M₂) :
    psiOf Φ (ε (β.φ2 b)) = ((μ.φ2 b : ↥M0Dot) : GL6) :=
  hΦ.2 b

theorem tr_bM (hΦ : PhiExt β ε μ Φ) (a : ↥(M₁ ⊓ M₂)) :
    psiOf Φ (bM β ε a) = ((μ.φ12 a : ↥M0Dot) : GL6) := by
  exact (tr_phi1 hΦ _).trans (congrArg Subtype.val (μ.comm1 a))

theorem tr_MiOne (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ) :
    (MiOne β ε).map (psiOf Φ) = M1Dot := by
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, rfl⟩
    have e : psiOf Φ (epsG β ε (f1 (c := β) b)) = ((μ.φ1 b : ↥M0Dot) : GL6) := tr_phi1 hΦ b
    rw [e, ← hμ.img1]
    exact ⟨_, ⟨b, rfl⟩, rfl⟩
  · intro hy
    rw [← hμ.img1] at hy
    obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := hy
    exact ⟨ε (β.φ1 b), ⟨_, ⟨b, rfl⟩, rfl⟩, tr_phi1 hΦ b⟩

theorem tr_MiTwo (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ) :
    (MiTwo β ε).map (psiOf Φ) = M2Dot := by
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, rfl⟩
    have e : psiOf Φ (epsG β ε (f2 (c := β) b)) = ((μ.φ2 b : ↥M0Dot) : GL6) := tr_phi2 hΦ b
    rw [e, ← hμ.img2]
    exact ⟨_, ⟨b, rfl⟩, rfl⟩
  · intro hy
    rw [← hμ.img2] at hy
    obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := hy
    exact ⟨ε (β.φ2 b), ⟨_, ⟨b, rfl⟩, rfl⟩, tr_phi2 hΦ b⟩

theorem tr_M0Of (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ) :
    (M0Of β ε).map (psiOf Φ) = M0Dot := by
  rw [M0Of, Subgroup.map_sup, tr_MiOne hμ hΦ, tr_MiTwo hμ hΦ, M1Dot_sup_M2Dot]

theorem tr_fOf (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ) : psiOf Φ (fOf β ε fb) = fDot :=
  (tr_bM hΦ fb).trans hμ.f_eq

theorem tr_z (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ) (hz : ε (β.φ1 zb) = z) :
    psiOf Φ z = zDot := by
  rw [← hz, tr_phi1 hΦ, hμ.z_eq]

theorem tr_TOf (hμ : IsMarkedMuIso μ zb fb Tb) (hΦ : PhiExt β ε μ Φ) :
    (TOf β ε Tb).map (psiOf Φ) = TDot := by
  rw [← hμ.2]
  ext y
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, (tr_bM hΦ a).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, tr_bM hΦ a⟩

theorem tr_cen_f (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ) :
    (Subgroup.centralizer ({fOf β ε fb} : Set M)).map (psiOf Φ) =
      MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
  rw [tr_cen, tr_fOf hμ hΦ]

theorem tr_EOf (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ) {Mi : Subgroup M}
    {MiDot : Subgroup GL6} (hMi : Mi.map (psiOf Φ) = MiDot) (hle : MiDot ≤ MDot) :
    (EOf Mi (fOf β ε fb)).map (psiOf Φ) = EDot MiDot := by
  rw [EOf, tr_map_inf (psiOf_injective Φ), hMi, tr_cen_f hμ hΦ, EDot, ← inf_assoc,
    inf_eq_left.2 hle]

theorem tr_AOf (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ) {Mi : Subgroup M}
    {MiDot : Subgroup GL6} (hMi : Mi.map (psiOf Φ) = MiDot) (hle : MiDot ≤ MDot) :
    (AOf Mi (fOf β ε fb)).map (psiOf Φ) = ADot MiDot := by
  rw [AOf, ← br_pCoreOf_map (psiOf_injective Φ), tr_EOf hμ hΦ hMi hle, ADot]

theorem tr_A1 (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ) :
    (AOf (MiOne β ε) (fOf β ε fb)).map (psiOf Φ) = ADot M1Dot :=
  tr_AOf hμ hΦ (tr_MiOne hμ hΦ) inf_le_left

theorem tr_A2 (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ) :
    (AOf (MiTwo β ε) (fOf β ε fb)).map (psiOf Φ) = ADot M2Dot :=
  tr_AOf hμ hΦ (tr_MiTwo hμ hΦ) inf_le_left

theorem tr_HOf (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ) :
    (HOf β ε fb).map (psiOf Φ) = MDot ⊓ Subgroup.normalizer ((ADot M2Dot : Subgroup GL6) : Set GL6) := by
  rw [HOf, tr_normalizer, tr_A2 hμ hΦ]

theorem tr_TfOf (hμ : IsMarkedMuIso μ zb fb Tb) (hΦ : PhiExt β ε μ Φ) :
    (TfOf β ε Tb fb).map (psiOf Φ) = TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
  rw [TfOf, tr_map_inf (psiOf_injective Φ), tr_TOf hμ hΦ, tr_cen_f hμ.1 hΦ, ← inf_assoc,
    inf_eq_left.2 (TDot_le_M12.trans (inf_le_left.trans (inf_le_left : M1Dot ≤ MDot)))]

end Abstract

section Compat

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {Tb : Subgroup E}
  {fb : ↥(M₁ ⊓ M₂)} {zb : ↥M₁} {Φ : M ≃* ↥MDot} {Θ : E ≃* ↥M0Dot} {hgen : M₁ ⊔ M₂ = ⊤}

theorem tr_Gi {Mi : Subgroup E} {MiDot : Subgroup GL6} (hMiDot : MiDot ≤ M0Dot)
    (hMi : ∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ MiDot ↔ x ∈ Mi) {G0 : Type} [Group G0]
    (j1 : ↥Mi →* G0) (j2 : G0 →* M)
    (hj : ∀ b : ↥Mi, psiOf Φ (j2 (j1 b)) = ((Θ (b : E) : ↥M0Dot) : GL6)) (X : Subgroup E)
    (X' : Subgroup GL6) (hX' : ∀ x : E, x ∈ Mi → (x ∈ X ↔ ((Θ x : ↥M0Dot) : GL6) ∈ X'))
    (hX'le : X' ≤ MiDot) :
    (((X.subgroupOf Mi).map j1).map j2).map (psiOf Φ) = X' := by
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
    rw [hj]
    exact (hX' _ b.2).1 hb
  · intro hy
    have hy0 : y ∈ M0Dot := hMiDot (hX'le hy)
    have hyv : ((Θ (Θ.symm ⟨y, hy0⟩) : ↥M0Dot) : GL6) = y := by rw [MulEquiv.apply_symm_apply]
    have hxM : Θ.symm ⟨y, hy0⟩ ∈ Mi := (hMi _).1 (by rw [hyv]; exact hX'le hy)
    refine ⟨j2 (j1 ⟨_, hxM⟩), ⟨j1 ⟨_, hxM⟩, ⟨⟨_, hxM⟩, (hX' _ hxM).2 (by rw [hyv]; exact hy), rfl⟩,
      rfl⟩, ?_⟩
    rw [hj]
    exact hyv

theorem tr_GiTwo (hC : NmCompat Θ Gp M₁ M₂) (hΦ : PhiExt β ε (muOfIso Θ hgen) Φ) :
    (GiTwo Gp β ε).map (psiOf Φ) = GDot ⊓ M2Dot :=
  tr_Gi M2Dot_le_M0Dot hC.2.1 (f2 (c := β)) (epsG β ε) (fun b => tr_phi2 hΦ b) (Gp ⊓ M₂)
    (GDot ⊓ M2Dot)
    (fun x hx => ⟨fun h => ⟨(hC.2.2 x).2 h.1, (hC.2.1 x).2 h.2⟩,
      fun h => ⟨(hC.2.2 x).1 h.1, hx⟩⟩)
    inf_le_right

theorem tr_cen_Theta (hf : ((Θ (fb : E) : ↥M0Dot) : GL6) = fDot) (x : E) :
    x ∈ Subgroup.centralizer ({(fb : E)} : Set E) ↔
      ((Θ x : ↥M0Dot) : GL6) ∈ Subgroup.centralizer ({fDot} : Set GL6) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← hf]
  constructor
  · intro h
    have := congrArg (fun w : E => ((Θ w : ↥M0Dot) : GL6)) h
    simpa using this
  · intro h
    apply Θ.injective
    apply Subtype.ext
    simpa using h

theorem tr_DOne (hC : NmCompat Θ Gp M₁ M₂) (hf : ((Θ (fb : E) : ↥M0Dot) : GL6) = fDot)
    (hΦ : PhiExt β ε (muOfIso Θ hgen) Φ) :
    (DOne Gp β ε fb).map (psiOf Φ) =
      GDot ⊓ M1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
  tr_Gi M1Dot_le_M0Dot hC.1 (f1 (c := β)) (epsG β ε) (fun b => tr_phi1 hΦ b)
    (cenIn (Gp ⊓ M₁) (fb : E)) (GDot ⊓ M1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6))
    (fun x hx => ⟨fun h => ⟨⟨(hC.2.2 x).2 h.1.1, (hC.1 x).2 h.1.2⟩, (tr_cen_Theta hf x).1 h.2⟩,
      fun h => ⟨⟨(hC.2.2 x).1 h.1.1, hx⟩, (tr_cen_Theta hf x).2 h.2⟩⟩)
    (inf_le_left.trans inf_le_right)

theorem tr_DTwo (hC : NmCompat Θ Gp M₁ M₂) (hf : ((Θ (fb : E) : ↥M0Dot) : GL6) = fDot)
    (hΦ : PhiExt β ε (muOfIso Θ hgen) Φ) :
    (DTwo Gp β ε fb).map (psiOf Φ) =
      GDot ⊓ M2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
  tr_Gi M2Dot_le_M0Dot hC.2.1 (f2 (c := β)) (epsG β ε) (fun b => tr_phi2 hΦ b)
    (cenIn (Gp ⊓ M₂) (fb : E)) (GDot ⊓ M2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6))
    (fun x hx => ⟨fun h => ⟨⟨(hC.2.2 x).2 h.1.1, (hC.2.1 x).2 h.1.2⟩, (tr_cen_Theta hf x).1 h.2⟩,
      fun h => ⟨⟨(hC.2.2 x).1 h.1.1, hx⟩, (tr_cen_Theta hf x).2 h.2⟩⟩)
    (inf_le_left.trans inf_le_right)

theorem tr_QTwo (hC : NmCompat Θ Gp M₁ M₂) (hΦ : PhiExt β ε (muOfIso Θ hgen) Φ) :
    (QTwoOf Gp β ε).map (psiOf Φ) = Q2Dot := by
  rw [QTwoOf, ← br_pCoreOf_map (psiOf_injective Φ), ← nm_oPPrime_map (psiOf_injective Φ),
    tr_GiTwo hC hΦ, oPPrime_GDot_inf_M2Dot, pCoreOf_GDot_inf_M2Dot, pCoreOf_M2Dot]

theorem tr_tInv (hμ : IsMuIso (muOfIso Θ hgen) zb fb) (hC : NmCompat Θ Gp M₁ M₂)
    (hΦ : PhiExt β ε (muOfIso Θ hgen) Φ) {t : M} (ht : IsTInv Gp β ε fb t) :
    psiOf Φ t = tDot := by
  have h1 := congrArg (Subgroup.map (psiOf Φ)) ht.2
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers, MonoidHom.map_zpowers, tr_QTwo hC hΦ,
    tr_fOf hμ hΦ, f53Model.2.2.2.2.2.1] at h1
  have hmem : psiOf Φ t ∈ Subgroup.zpowers tDot := by
    rw [h1]
    exact Subgroup.mem_zpowers _
  rcases mc_mem_zpowers_of_mul_self tDot_mul_self hmem with h | h
  · exact absurd ((psiOf_injective Φ) (h.trans (map_one _).symm)) ht.1
  · exact h

end Compat

section IsoTransport

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {Tb : Subgroup E}
  {fb : ↥(M₁ ⊓ M₂)} {μ : Cpl M₁ M₂ ↥M0Dot} {zb : ↥M₁} {Φ : M ≃* ↥MDot}

theorem tr_toG (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ)
    (b : ↥Bh) : psiOf Φ ((autIsoOfMarked h hμ).toG b) = lamG b := by
  obtain ⟨y, hy⟩ := br_lamA_mem_range12 hμ b
  have key : ∀ a : ↥(M₁ ⊓ M₂), μ.φ12 a = lamA (b : Ah) →
      psiOf Φ ((autIsoOfMarked h hμ).toG b) = lamG b := by
    intro a ha
    rw [autIsoOfMarked_toG h hμ ha.symm]
    exact (tr_bM hΦ a).trans (congrArg Subtype.val ha)
  exact key y hy

theorem tr_imgG (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb) (hΦ : PhiExt β ε μ Φ)
    {X : Subgroup Ah} (hX : X ≤ Bh) :
    ((autIsoOfMarked h hμ).imgG X).map (psiOf Φ) = X.map lamG := by
  ext y
  constructor
  · rintro ⟨_, hx, rfl⟩
    obtain ⟨b, hb, rfl⟩ := (AutIso.mem_imgG _).1 hx
    exact ⟨b, hb, (tr_toG h hμ hΦ b).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, (AutIso.mem_imgG _).2 ⟨⟨a, hX ha⟩, ha, rfl⟩, tr_toG h hμ hΦ ⟨a, hX ha⟩⟩

end IsoTransport

section Unique

theorem card_MDot_inf_cen_fDot :
    Nat.card ↥(MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = 2880 := by
  obtain ⟨R, hR, hTR⟩ := exists_R modelCtx
  obtain ⟨-, -, h55, -⟩ := autCtx_conf modelCtx hR hTR
  have hf : ((modelCtx.iso.toG fhB : ↥MDot) : GL6) = fDot := by
    rw [modelCtx_toG]
    exact lamA_fhatA
  have hmap : (cenOf (modelCtx.iso.toG fhB)).map MDot.subtype =
      MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
    rw [cenOf, tr_map_centralizer_singleton MDot.subtype_injective, MDot.range_subtype,
      Subgroup.subtype_apply, hf]
  rw [← hmap, Subgroup.card_map_of_injective MDot.subtype_injective]
  exact h55.1

end Unique

end CFSG.Quasithin.SimsF5
