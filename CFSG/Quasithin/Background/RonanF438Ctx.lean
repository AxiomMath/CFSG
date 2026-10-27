module

public import CFSG.Quasithin.Background.RonanF438Mark
public import CFSG.Quasithin.Background.SimsF5Bridge

public section

namespace CFSG.Quasithin.RonanF438

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Quasithin.H13.F431.U42Aut
  CFSG.Quasithin.SimsF5
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Iso


theorem exists_fullIso {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    (hcent : Subgroup.centralizer (Gp : Set E) = ⊥) (hne : Gp ≠ ⊤)
    (hout : ∃ n ∈ M₁ ⊓ M₂, n ∉ Gp) {K : Type} [Field K] [Finite K] (hKcard : Nat.card K = 4)
    {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2) (m : ↥Gp ≃* StatedProj (StatedSU 4 2 K))
    (point plane : Submodule K (Fin 4 → K)) (hp1 : Module.finrank K point = 1)
    (hp2 : Module.finrank K plane = 2) (hpp : point ≤ plane)
    (hiso : ∀ v ∈ plane, ∀ w ∈ plane, U42Hermitian K v w = 0)
    (hpar1 : U42ParabolicAt Gp (Gp ⊓ M₁) m point)
    (hpar2 : U42ParabolicAt Gp (Gp ⊓ M₂) m plane) :
    ∃ Θ : E ≃* Ah, (∀ x : E, Θ x ∈ Yh ↔ x ∈ Gp) ∧ (∀ x : E, Θ x ∈ P1h ↔ x ∈ M₁) ∧
      (∀ x : E, Θ x ∈ P2h ↔ x ∈ M₂) := by
  classical
  obtain ⟨Θ₀, hY0, hP10, hP20⟩ :=
    exists_markIso_nofb hcent hne hKcard hσ m point plane hp1 hp2 hpp hiso hpar1 hpar2
  obtain ⟨fb, hfb, hfbG⟩ := hout
  have hGp : Gp.Normal := inferInstance
  set Θ₁ : E ≃* ↥M0Dot := Θ₀.trans lamA with hΘ₁
  have hY1 : ∀ x : E, ((Θ₁ x : ↥M0Dot) : GL6) ∈ GDot ↔ x ∈ Gp := fun x =>
    (lamA_mem_GDot _).trans (hY0 x)
  have h1 := nm_full_of_Gp hGp M1Dot_le_M0Dot M0Dot_inf_normalizer_GDot_inf_M1Dot
    (by rw [card_GDot_inf_M1Dot, card_M1Dot]) hfb.1 hfbG hY1
    (fun x hx => (lamA_mem_M1Dot _).trans (hP10 x hx))
  have h2 := nm_full_of_Gp hGp M2Dot_le_M0Dot M0Dot_inf_normalizer_GDot_inf_M2Dot
    (by rw [card_GDot_inf_M2Dot, card_M2Dot]) hfb.2 hfbG hY1
    (fun x hx => (lamA_mem_M2Dot _).trans (hP20 x hx))
  exact ⟨Θ₀, hY0, fun x => (lamA_mem_M1Dot (Θ₀ x)).symm.trans (h1 x),
    fun x => (lamA_mem_M2Dot (Θ₀ x)).symm.trans (h2 x)⟩

theorem theta_zb {E : Type} [Group E] {Gp M₁ : Subgroup E} {Θ : E ≃* Ah}
    (hY : ∀ x : E, Θ x ∈ Yh ↔ x ∈ Gp) (h1 : ∀ x : E, Θ x ∈ P1h ↔ x ∈ M₁) {zb : ↥M₁}
    (hzb : zb ∈ ctr (oPPrime 2 ((Gp ⊓ M₁).subgroupOf M₁))) (hz1 : zb ≠ 1) :
    Θ (zb : E) = xA := by
  classical
  set Θ₁ : E ≃* ↥M0Dot := Θ.trans lamA with hΘ₁
  have hG1 : ∀ x : E, ((Θ₁ x : ↥M0Dot) : GL6) ∈ GDot ↔ x ∈ Gp := fun x =>
    (lamA_mem_GDot _).trans (hY x)
  have hM1 : ∀ x : E, ((Θ₁ x : ↥M0Dot) : GL6) ∈ M1Dot ↔ x ∈ M₁ := fun x =>
    (lamA_mem_M1Dot _).trans (h1 x)
  set ψ : ↥M₁ →* GL6 := M0Dot.subtype.comp (Θ₁.toMonoidHom.comp M₁.subtype) with hψ
  have hψinj : Function.Injective ψ :=
    Subtype.val_injective.comp (Θ₁.injective.comp Subtype.val_injective)
  have hKψ : ((Gp ⊓ M₁).subgroupOf M₁).map ψ = GDot ⊓ M1Dot := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hG1 _).2 hx.1, (hM1 _).2 x.2⟩
    · intro hg
      have hg0 : g ∈ M0Dot := GDot_le_M0Dot hg.1
      set y := Θ₁.symm ⟨g, hg0⟩ with hy
      have hyv : ((Θ₁ y : ↥M0Dot) : GL6) = g := by rw [hy, MulEquiv.apply_symm_apply]
      have hyM : y ∈ M₁ := (hM1 y).1 (hyv ▸ hg.2)
      have hyG : y ∈ Gp := (hG1 y).1 (hyv ▸ hg.1)
      exact ⟨⟨y, hyM⟩, ⟨hyG, hyM⟩, hyv⟩
  have hmem : ψ zb ∈ ctr (oPPrime 2 (GDot ⊓ M1Dot)) := by
    rw [← hKψ, nm_oPPrime_map hψinj, nm_ctr_map hψinj]
    exact ⟨zb, hzb, rfl⟩
  rcases ctr_oPPrime_GDot_inf_M1Dot hmem with h1' | h1'
  · exfalso
    apply hz1
    have : ψ zb = ψ 1 := by rw [h1', map_one]
    exact hψinj this
  · have h2 : ((Θ₁ (zb : E) : ↥M0Dot) : GL6) = zDot := h1'
    have h3 : Θ₁ (zb : E) = lamA xA := Subtype.ext (h2.trans lamA_xA.symm)
    exact lamA.injective h3

end Iso

section Ctx


noncomputable def autCtx_of_compat {E : Type} [Group E] {M₁ M₂ : Subgroup E} {M : Type} [Group M]
    [Finite M] {N₁ N₂ : Subgroup M} (Θ : E ≃* Ah) (h1 : ∀ x : E, Θ x ∈ P1h ↔ x ∈ M₁)
    (h2 : ∀ x : E, Θ x ∈ P2h ↔ x ∈ M₂) (b₁ : ↥M₁ →* M) (b₂ : ↥M₂ →* M)
    (hb₁ : Function.Injective b₁) (hb₂ : Function.Injective b₂) (hr₁ : b₁.range = N₁)
    (hr₂ : b₂.range = N₂)
    (hb : ∀ (x : E) (hx1 : x ∈ M₁) (hx2 : x ∈ M₂), b₁ ⟨x, hx1⟩ = b₂ ⟨x, hx2⟩)
    (hI : ∀ g ∈ N₁ ⊓ N₂, ∃ (x : E) (hx1 : x ∈ M₁) (_ : x ∈ M₂), b₁ ⟨x, hx1⟩ = g)
    {z : M} (zb : ↥M₁) (hzb : b₁ zb = z) (hΘz : Θ (zb : E) = xA)
    (hres : pResidual 2 M = ⊤) (hcz : Subgroup.centralizer ({z} : Set M) ≤ N₁)
    (hN1 : Subgroup.normalizer (centerOf (pCoreOf 2 N₁) : Set M) = N₁)
    (hN2 : Subgroup.normalizer (centerOf (pCoreOf 2 N₂) : Set M) = N₂) :
    AutCtx M N₁ N₂ z := by
  classical
  subst hr₁ hr₂
  let θ₁ : ↥P1h →* ↥M₁ := ((Θ.symm.toMonoidHom).comp P1h.subtype).codRestrict M₁ (fun x =>
    (h1 _).1 (by simpa using x.2))
  let θ₂ : ↥P2h →* ↥M₂ := ((Θ.symm.toMonoidHom).comp P2h.subtype).codRestrict M₂ (fun x =>
    (h2 _).1 (by simpa using x.2))
  have hθ₁ : ∀ x : ↥P1h, ((θ₁ x : ↥M₁) : E) = Θ.symm (x : Ah) := fun x => rfl
  have hθ₂ : ∀ x : ↥P2h, ((θ₂ x : ↥M₂) : E) = Θ.symm (x : Ah) := fun x => rfl
  have hθ₁inj : Function.Injective θ₁ := fun x y hxy =>
    Subtype.ext (Θ.symm.injective (congrArg Subtype.val hxy))
  have hθ₂inj : Function.Injective θ₂ := fun x y hxy =>
    Subtype.ext (Θ.symm.injective (congrArg Subtype.val hxy))
  have hθ₁surj : Function.Surjective θ₁ := fun y =>
    ⟨⟨Θ (y : E), (h1 _).2 y.2⟩, Subtype.ext (by rw [hθ₁]; simp)⟩
  have hθ₂surj : Function.Surjective θ₂ := fun y =>
    ⟨⟨Θ (y : E), (h2 _).2 y.2⟩, Subtype.ext (by rw [hθ₂]; simp)⟩
  let j₁ : ↥P1h →* M := b₁.comp θ₁
  let j₂ : ↥P2h →* M := b₂.comp θ₂
  have hj₁inj : Function.Injective j₁ := hb₁.comp hθ₁inj
  have hj₂inj : Function.Injective j₂ := hb₂.comp hθ₂inj
  have hr₁ : j₁.range = b₁.range := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨θ₁ x, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hθ₁surj y
      exact ⟨x, rfl⟩
  have hr₂ : j₂.range = b₂.range := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨θ₂ x, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hθ₂surj y
      exact ⟨x, rfl⟩
  have hB : ∀ b : ↥Bh, j₁ (Subgroup.inclusion Bh_le_P1h b) =
      j₂ (Subgroup.inclusion Bh_le_P2h b) := by
    intro b
    have hx1 : Θ.symm (b : Ah) ∈ M₁ := (h1 _).1 (by simpa using Bh_le_P1h b.2)
    have hx2 : Θ.symm (b : Ah) ∈ M₂ := (h2 _).1 (by simpa using Bh_le_P2h b.2)
    exact hb _ hx1 hx2
  have hI' : ∀ g ∈ b₁.range ⊓ b₂.range, ∃ b : ↥Bh,
      j₁ (Subgroup.inclusion Bh_le_P1h b) = g := by
    intro g hg
    obtain ⟨x, hx1, hx2, hxg⟩ := hI g hg
    refine ⟨⟨Θ x, (h1 x).2 hx1, (h2 x).2 hx2⟩, ?_⟩
    rw [← hxg]
    show b₁ (θ₁ ⟨Θ x, _⟩) = _
    congr 1
    exact Subtype.ext (by rw [hθ₁]; simp)
  let iso : AutIso b₁.range b₂.range :=
    autIsoOfHoms j₁ j₂ hj₁inj hj₂inj hr₁ hr₂ hB hI'
  have hz : iso.toG xB = z := by
    show b₁ (θ₁ (Subgroup.inclusion Bh_le_P1h xB)) = z
    rw [← hzb]
    congr 1
    apply Subtype.ext
    rw [hθ₁]
    exact (MulEquiv.symm_apply_eq Θ).2 hΘz.symm
  exact autCtxOf iso hz hres hcz hN1 hN2

end Ctx

section Normalizers

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y}
  {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem nmCompat_of_full {Θ : E ≃* Ah}
    (hY : ∀ x : E, Θ x ∈ Yh ↔ x ∈ Gp) (h1 : ∀ x : E, Θ x ∈ P1h ↔ x ∈ M₁)
    (h2 : ∀ x : E, Θ x ∈ P2h ↔ x ∈ M₂) : NmCompat (Θ.trans lamA) Gp M₁ M₂ :=
  ⟨fun x => (lamA_mem_M1Dot (Θ x)).trans (h1 x), fun x => (lamA_mem_M2Dot (Θ x)).trans (h2 x),
    fun x => (lamA_mem_GDot (Θ x)).trans (hY x)⟩

theorem hypF431_normalizers (h : HypF_4_31 GLKind.U4 1 Gp M₁ M₂ β ε z) {Θ : E ≃* ↥M0Dot}
    (hΘ : NmCompat Θ Gp M₁ M₂) :
    Subgroup.normalizer (centerOf (pCoreOf 2 (MiOne β ε)) : Set M) = MiOne β ε ∧
      Subgroup.normalizer (centerOf (pCoreOf 2 (MiTwo β ε)) : Set M) = MiTwo β ε := by
  set j1 : ↥M₁ →* β.G0 := f1 (c := β) with hj1
  set j2 : ↥M₂ →* β.G0 := f2 (c := β) with hj2
  have hj1inj : Function.Injective j1 := fun a b hab => by
    have : β.φ1 a = β.φ1 b := congrArg Subtype.val hab
    exact h.faithful.1 this
  have hj2inj : Function.Injective j2 := fun a b hab => by
    have : β.φ2 a = β.φ2 b := congrArg Subtype.val hab
    exact h.faithful.2.2 this
  have hεinj := h.inj
  have hG1 : GiOne Gp β ε = (((Gp ⊓ M₁).subgroupOf M₁).map j1).map (epsG β ε) := rfl
  have hG2 : GiTwo Gp β ε = (((Gp ⊓ M₂).subgroupOf M₂).map j2).map (epsG β ε) := rfl
  have hM1 : MiOne β ε = ((⊤ : Subgroup ↥M₁).map j1).map (epsG β ε) := by
    show j1.range.map (epsG β ε) = _
    exact congrArg (Subgroup.map (epsG β ε)) (MonoidHom.range_eq_map j1)
  have hM2 : MiTwo β ε = ((⊤ : Subgroup ↥M₂).map j2).map (epsG β ε) := by
    show j2.range.map (epsG β ε) = _
    exact congrArg (Subgroup.map (epsG β ε)) (MonoidHom.range_eq_map j2)
  have hc1 : pCoreOf 2 (GiOne Gp β ε) = pCoreOf 2 (MiOne β ε) := by
    rw [hG1, hM1, br_pCoreOf_map hεinj, br_pCoreOf_map hεinj, br_pCoreOf_map hj1inj,
      br_pCoreOf_map hj1inj,
      br_pCoreOf_eq M1Dot_le_M0Dot hΘ.1 hΘ.2.2 pCoreOf_GDot_inf_M1Dot]
  have hc2 : pCoreOf 2 (GiTwo Gp β ε) = pCoreOf 2 (MiTwo β ε) := by
    rw [hG2, hM2, br_pCoreOf_map hεinj, br_pCoreOf_map hεinj, br_pCoreOf_map hj2inj,
      br_pCoreOf_map hj2inj,
      br_pCoreOf_eq M2Dot_le_M0Dot hΘ.2.1 hΘ.2.2 pCoreOf_GDot_inf_M2Dot]
  obtain ⟨ha1, ha2⟩ := h.ha (Or.inr (Or.inl rfl))
  refine ⟨?_, ?_⟩
  · have := ha1
    rw [hc1] at this
    exact this
  · have := ha2
    rw [hc2] at this
    exact this

end Normalizers

end CFSG.Quasithin.RonanF438
