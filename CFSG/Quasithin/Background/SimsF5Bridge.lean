module

public import CFSG.Quasithin.Background.SimsF5Norm
public import CFSG.Quasithin.Background.SimsF5ModelCtx

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Quasithin.H13.F431.U42Aut
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

theorem br_pResidual_eq_top {M : Type} [Group M] [Finite M]
    (he : oTwoRes (⊤ : Subgroup M) = ⊤) : pResidual 2 M = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  rw [pResidual, Subgroup.mem_iInf]
  intro N
  rw [Subgroup.mem_iInf]
  intro hN
  rw [Subgroup.mem_iInf]
  intro hp
  have hodd : ∀ y : M, (∃ m : ℕ, Odd m ∧ y ^ m = 1) → y ∈ N := by
    rintro y ⟨m, hm, hym⟩
    obtain ⟨k, hk⟩ := hp y
    have hcop : (2 ^ k).Coprime (orderOf y) := by
      have hdvd : orderOf y ∣ m := orderOf_dvd_of_pow_eq_one hym
      have hodd' : Odd (orderOf y) := hm.of_dvd_nat hdvd
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd')
    obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hn]
    exact N.pow_mem hk n
  have hle : oTwoRes (⊤ : Subgroup M) ≤ N := by
    rw [oTwoRes, Subgroup.closure_le]
    rintro y ⟨-, hy⟩
    exact hodd y hy
  rw [he] at hle
  exact hle (Subgroup.mem_top x)

theorem br_pCoreOf_map {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) (p : ℕ) (L : Subgroup A) :
    pCoreOf p (L.map f) = (pCoreOf p L).map f := by
  let e : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  have he := CFSG.pCore_map_iso p e
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [← he] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨v, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨e v, ?_, rfl⟩
    rw [← he]
    exact ⟨v, hv, rfl⟩


section Normalizers

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {Tb : Subgroup E}
  {fb : ↥(M₁ ⊓ M₂)}

theorem br_pCoreOf_eq {Θ : E ≃* ↥M0Dot} {Mi : Subgroup E} {MiDot : Subgroup GL6}
    (hMiDot : MiDot ≤ M0Dot) (hMi : ∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ MiDot ↔ x ∈ Mi)
    (hGp : ∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ GDot ↔ x ∈ Gp)
    (hcore : pCoreOf 2 (GDot ⊓ MiDot) = pCoreOf 2 MiDot) :
    pCoreOf 2 ((Gp ⊓ Mi).subgroupOf Mi) = pCoreOf 2 (⊤ : Subgroup ↥Mi) := by
  set ψ : ↥Mi →* GL6 := M0Dot.subtype.comp (Θ.toMonoidHom.comp Mi.subtype) with hψ
  have hψinj : Function.Injective ψ :=
    Subtype.val_injective.comp (Θ.injective.comp Subtype.val_injective)
  have hsurj : ∀ g ∈ MiDot, ∃ x : ↥Mi, ψ x = g := by
    intro g hg
    set y := Θ.symm ⟨g, hMiDot hg⟩ with hy
    have hyv : ((Θ y : ↥M0Dot) : GL6) = g := by rw [hy, MulEquiv.apply_symm_apply]
    exact ⟨⟨y, (hMi y).1 (hyv ▸ hg)⟩, hyv⟩
  have h1 : ((Gp ⊓ Mi).subgroupOf Mi).map ψ = GDot ⊓ MiDot := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hGp _).2 hx.1, (hMi _).2 x.2⟩
    · intro hg
      obtain ⟨x, rfl⟩ := hsurj g hg.2
      exact ⟨x, ⟨(hGp _).1 hg.1, x.2⟩, rfl⟩
  have h2 : (⊤ : Subgroup ↥Mi).map ψ = MiDot := by
    ext g
    constructor
    · rintro ⟨x, -, rfl⟩
      exact (hMi _).2 x.2
    · intro hg
      obtain ⟨x, rfl⟩ := hsurj g hg
      exact ⟨x, Subgroup.mem_top _, rfl⟩
  apply Subgroup.map_injective hψinj
  rw [← br_pCoreOf_map hψinj, ← br_pCoreOf_map hψinj, h1, h2, hcore]

theorem hypF5_normalizers (h : HypF5 Gp M₁ M₂ β ε z Tb fb) {Θ : E ≃* ↥M0Dot}
    (hΘ : NmCompat Θ Gp M₁ M₂) :
    Subgroup.normalizer (centerOf (pCoreOf 2 (MiOne β ε)) : Set M) = MiOne β ε ∧
      Subgroup.normalizer (centerOf (pCoreOf 2 (MiTwo β ε)) : Set M) = MiTwo β ε := by
  set j1 : ↥M₁ →* β.G0 := f1 (c := β) with hj1
  set j2 : ↥M₂ →* β.G0 := f2 (c := β) with hj2
  have hj1inj : Function.Injective j1 := fun a b hab => by
    have : β.φ1 a = β.φ1 b := congrArg Subtype.val hab
    exact h.f431.faithful.1 this
  have hj2inj : Function.Injective j2 := fun a b hab => by
    have : β.φ2 a = β.φ2 b := congrArg Subtype.val hab
    exact h.f431.faithful.2.2 this
  have hεinj := h.f431.inj
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
  obtain ⟨ha1, ha2⟩ := h.f431.ha
  refine ⟨?_, ?_⟩
  · have := ha1
    rw [hc1] at this
    exact this
  · have := ha2
    rw [hc2] at this
    exact this

end Normalizers


section Marked

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {Tb : Subgroup E}
  {fb : ↥(M₁ ⊓ M₂)} {μ : Cpl M₁ M₂ ↥M0Dot} {zb : ↥M₁}

theorem br_lamA_mem_range1 (hμ : IsMuIso μ zb fb) (x : ↥P1h) : lamA (x : Ah) ∈ μ.φ1.range := by
  have hx : ((lamA (x : Ah) : ↥M0Dot) : GL6) ∈ M1Dot := (lamA_mem_M1Dot _).2 x.2
  rw [← hμ.img1] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = lamA (x : Ah) := Subtype.ext hyx
  rw [← this]
  exact hy

theorem br_lamA_mem_range2 (hμ : IsMuIso μ zb fb) (x : ↥P2h) : lamA (x : Ah) ∈ μ.φ2.range := by
  have hx : ((lamA (x : Ah) : ↥M0Dot) : GL6) ∈ M2Dot := (lamA_mem_M2Dot _).2 x.2
  rw [← hμ.img2] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = lamA (x : Ah) := Subtype.ext hyx
  rw [← this]
  exact hy

theorem br_lamA_mem_range12 (hμ : IsMuIso μ zb fb) (x : ↥Bh) : lamA (x : Ah) ∈ μ.φ12.range := by
  have hx : ((lamA (x : Ah) : ↥M0Dot) : GL6) ∈ M1Dot ⊓ M2Dot :=
    ⟨(lamA_mem_M1Dot _).2 x.2.1, (lamA_mem_M2Dot _).2 x.2.2⟩
  rw [← hμ.img12] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = lamA (x : Ah) := Subtype.ext hyx
  rw [← this]
  exact hy

theorem br_inj1 (hμ : IsMuIso μ zb fb) : Function.Injective μ.φ1 := hμ.faithful.1

theorem br_inj2 (hμ : IsMuIso μ zb fb) : Function.Injective μ.φ2 := hμ.faithful.2.2

theorem br_inj12 (hμ : IsMuIso μ zb fb) : Function.Injective μ.φ12 := hμ.faithful.2.1

@[expose] noncomputable def brJ1 (β : Cpl M₁ M₂ Y) (ε : Y →* M) (hμ : IsMuIso μ zb fb) :
    ↥P1h →* M :=
  ((epsG β ε).comp (f1 (c := β))).comp
    ((MonoidHom.ofInjective (br_inj1 hμ)).symm.toMonoidHom.comp
      ((lamA.toMonoidHom.comp P1h.subtype).codRestrict _ (br_lamA_mem_range1 hμ)))

@[expose] noncomputable def brJ2 (β : Cpl M₁ M₂ Y) (ε : Y →* M) (hμ : IsMuIso μ zb fb) :
    ↥P2h →* M :=
  ((epsG β ε).comp (f2 (c := β))).comp
    ((MonoidHom.ofInjective (br_inj2 hμ)).symm.toMonoidHom.comp
      ((lamA.toMonoidHom.comp P2h.subtype).codRestrict _ (br_lamA_mem_range2 hμ)))

theorem brJ1_eq (hμ : IsMuIso μ zb fb) {x : ↥P1h} {b : ↥M₁} (hxb : lamA (x : Ah) = μ.φ1 b) :
    brJ1 β ε hμ x = ε (β.φ1 b) := by
  have hpre : (MonoidHom.ofInjective (br_inj1 hμ)).symm
      (((lamA.toMonoidHom.comp P1h.subtype).codRestrict _ (br_lamA_mem_range1 hμ)) x) = b := by
    apply (MonoidHom.ofInjective (br_inj1 hμ)).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    exact hxb
  show epsG β ε (f1 (c := β) ((MonoidHom.ofInjective (br_inj1 hμ)).symm
      (((lamA.toMonoidHom.comp P1h.subtype).codRestrict _ (br_lamA_mem_range1 hμ)) x))) =
    ε (β.φ1 b)
  rw [hpre]
  rfl

theorem brJ2_eq (hμ : IsMuIso μ zb fb) {x : ↥P2h} {b : ↥M₂} (hxb : lamA (x : Ah) = μ.φ2 b) :
    brJ2 β ε hμ x = ε (β.φ2 b) := by
  have hpre : (MonoidHom.ofInjective (br_inj2 hμ)).symm
      (((lamA.toMonoidHom.comp P2h.subtype).codRestrict _ (br_lamA_mem_range2 hμ)) x) = b := by
    apply (MonoidHom.ofInjective (br_inj2 hμ)).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    exact hxb
  show epsG β ε (f2 (c := β) ((MonoidHom.ofInjective (br_inj2 hμ)).symm
      (((lamA.toMonoidHom.comp P2h.subtype).codRestrict _ (br_lamA_mem_range2 hμ)) x))) =
    ε (β.φ2 b)
  rw [hpre]
  rfl

end Marked


section MarkedIso

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {Tb : Subgroup E}
  {fb : ↥(M₁ ⊓ M₂)} {μ : Cpl M₁ M₂ ↥M0Dot} {zb : ↥M₁}

theorem br_kappa1_injective (h : HypF5 Gp M₁ M₂ β ε z Tb fb) :
    Function.Injective ((epsG β ε).comp (f1 (c := β))) := by
  refine h.f431.inj.comp fun a b hab => ?_
  have : β.φ1 a = β.φ1 b := congrArg Subtype.val hab
  exact h.f431.faithful.1 this

theorem br_kappa2_injective (h : HypF5 Gp M₁ M₂ β ε z Tb fb) :
    Function.Injective ((epsG β ε).comp (f2 (c := β))) := by
  refine h.f431.inj.comp fun a b hab => ?_
  have : β.φ2 a = β.φ2 b := congrArg Subtype.val hab
  exact h.f431.faithful.2.2 this

theorem brJ1_injective (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb) :
    Function.Injective (brJ1 β ε hμ) := by
  intro x y hxy
  have h1 := br_kappa1_injective h hxy
  have h2 := (MonoidHom.ofInjective (br_inj1 hμ)).symm.injective h1
  have h3 : lamA (x : Ah) = lamA (y : Ah) := congrArg Subtype.val h2
  exact Subtype.ext (lamA.injective h3)

theorem brJ2_injective (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb) :
    Function.Injective (brJ2 β ε hμ) := by
  intro x y hxy
  have h1 := br_kappa2_injective h hxy
  have h2 := (MonoidHom.ofInjective (br_inj2 hμ)).symm.injective h1
  have h3 : lamA (x : Ah) = lamA (y : Ah) := congrArg Subtype.val h2
  exact Subtype.ext (lamA.injective h3)

theorem br_exists_P1h (hμ : IsMuIso μ zb fb) (b : ↥M₁) :
    ∃ x : ↥P1h, lamA (x : Ah) = μ.φ1 b := by
  have hb : ((μ.φ1 b : ↥M0Dot) : GL6) ∈ M1Dot := by
    rw [← hμ.img1]
    exact ⟨_, ⟨b, rfl⟩, rfl⟩
  refine ⟨⟨lamA.symm (μ.φ1 b), (lamA_mem_M1Dot _).1 (by simpa using hb)⟩, by simp⟩

theorem br_exists_P2h (hμ : IsMuIso μ zb fb) (b : ↥M₂) :
    ∃ x : ↥P2h, lamA (x : Ah) = μ.φ2 b := by
  have hb : ((μ.φ2 b : ↥M0Dot) : GL6) ∈ M2Dot := by
    rw [← hμ.img2]
    exact ⟨_, ⟨b, rfl⟩, rfl⟩
  refine ⟨⟨lamA.symm (μ.φ2 b), (lamA_mem_M2Dot _).1 (by simpa using hb)⟩, by simp⟩

theorem br_exists_Bh (hμ : IsMuIso μ zb fb) (a : ↥(M₁ ⊓ M₂)) :
    ∃ x : ↥Bh, lamA (x : Ah) = μ.φ12 a := by
  have hb : ((μ.φ12 a : ↥M0Dot) : GL6) ∈ M1Dot ⊓ M2Dot := by
    rw [← hμ.img12]
    exact ⟨_, ⟨a, rfl⟩, rfl⟩
  refine ⟨⟨lamA.symm (μ.φ12 a), (lamA_mem_M1Dot _).1 (by simpa using hb.1),
    (lamA_mem_M2Dot _).1 (by simpa using hb.2)⟩, by simp⟩

theorem brJ1_range (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb) :
    (brJ1 β ε hμ).range = MiOne β ε := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := br_lamA_mem_range1 hμ x
    rw [brJ1_eq hμ hb.symm]
    exact ⟨f1 (c := β) b, ⟨b, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    obtain ⟨x, hx⟩ := br_exists_P1h hμ b
    exact ⟨x, brJ1_eq hμ hx⟩

theorem brJ2_range (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb) :
    (brJ2 β ε hμ).range = MiTwo β ε := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := br_lamA_mem_range2 hμ x
    rw [brJ2_eq hμ hb.symm]
    exact ⟨f2 (c := β) b, ⟨b, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    obtain ⟨x, hx⟩ := br_exists_P2h hμ b
    exact ⟨x, brJ2_eq hμ hx⟩

theorem brJ_Bh_eq (hμ : IsMuIso μ zb fb) {x : ↥Bh} {a : ↥(M₁ ⊓ M₂)}
    (hxa : lamA (x : Ah) = μ.φ12 a) :
    brJ1 β ε hμ (Subgroup.inclusion Bh_le_P1h x) = bM β ε a ∧
      brJ2 β ε hμ (Subgroup.inclusion Bh_le_P2h x) = bM β ε a := by
  refine ⟨?_, ?_⟩
  · rw [brJ1_eq hμ (b := (ofSubgroups M₁ M₂).α1 a) (hxa.trans (μ.comm1 a).symm)]
    rfl
  · rw [brJ2_eq hμ (b := (ofSubgroups M₁ M₂).α2 a) (hxa.trans (μ.comm2 a).symm)]
    show ε (β.φ2 ((ofSubgroups M₁ M₂).α2 a)) = epsG β ε (f1 (c := β) ((ofSubgroups M₁ M₂).α1 a))
    show ε (β.φ2 ((ofSubgroups M₁ M₂).α2 a)) = ε (β.φ1 ((ofSubgroups M₁ M₂).α1 a))
    exact congrArg ε ((β.comm2 a).trans (β.comm1 a).symm)

theorem brJ_B (hμ : IsMuIso μ zb fb) (x : ↥Bh) :
    brJ1 β ε hμ (Subgroup.inclusion Bh_le_P1h x) = brJ2 β ε hμ (Subgroup.inclusion Bh_le_P2h x) := by
  obtain ⟨a, ha⟩ := br_lamA_mem_range12 hμ x
  obtain ⟨h1, h2⟩ := brJ_Bh_eq (β := β) (ε := ε) hμ ha.symm
  rw [h1, h2]

theorem brJ_I (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb) :
    ∀ g ∈ MiOne β ε ⊓ MiTwo β ε, ∃ b : ↥Bh, brJ1 β ε hμ (Subgroup.inclusion Bh_le_P1h b) = g := by
  rintro g ⟨⟨_, ⟨a₁, rfl⟩, rfl⟩, h2⟩
  obtain ⟨_, ⟨a₂, rfl⟩, h2'⟩ := h2
  have heq : f1 (c := β) a₁ = f2 (c := β) a₂ := h.f431.inj h2'.symm
  have hY : β.φ1 a₁ = β.φ2 a₂ := congrArg Subtype.val heq
  have hmem : β.φ1 a₁ ∈ β.φ1.range ⊓ β.φ2.range := ⟨⟨a₁, rfl⟩, ⟨a₂, hY.symm⟩⟩
  rw [β.inter] at hmem
  obtain ⟨a, ha⟩ := hmem
  have ha1 : (ofSubgroups M₁ M₂).α1 a = a₁ := by
    apply h.f431.faithful.1
    exact (β.comm1 a).trans ha
  obtain ⟨x, hx⟩ := br_exists_Bh hμ a
  refine ⟨x, ?_⟩
  rw [(brJ_Bh_eq (β := β) (ε := ε) hμ hx).1]
  show epsG β ε (f1 (c := β) ((ofSubgroups M₁ M₂).α1 a)) = _
  rw [ha1]

@[expose] noncomputable def autIsoOfMarked (h : HypF5 Gp M₁ M₂ β ε z Tb fb)
    (hμ : IsMuIso μ zb fb) : AutIso (MiOne β ε) (MiTwo β ε) :=
  autIsoOfHoms (brJ1 β ε hμ) (brJ2 β ε hμ) (brJ1_injective h hμ) (brJ2_injective h hμ)
    (brJ1_range h hμ) (brJ2_range h hμ) (brJ_B hμ) (brJ_I h hμ)

theorem autIsoOfMarked_phi1 (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb)
    {x : ↥P1h} {b : ↥M₁} (hxb : lamA (x : Ah) = μ.φ1 b) :
    ((autIsoOfMarked h hμ).phi1 x : M) = ε (β.φ1 b) :=
  brJ1_eq hμ hxb

theorem autIsoOfMarked_phi2 (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb)
    {x : ↥P2h} {b : ↥M₂} (hxb : lamA (x : Ah) = μ.φ2 b) :
    ((autIsoOfMarked h hμ).phi2 x : M) = ε (β.φ2 b) :=
  brJ2_eq hμ hxb

theorem autIsoOfMarked_toG (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb)
    {x : ↥Bh} {a : ↥(M₁ ⊓ M₂)} (hxa : lamA (x : Ah) = μ.φ12 a) :
    (autIsoOfMarked h hμ).toG x = bM β ε a :=
  (brJ_Bh_eq hμ hxa).1

end MarkedIso


section Ctx

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {Tb : Subgroup E}
  {fb : ↥(M₁ ⊓ M₂)} {μ : Cpl M₁ M₂ ↥M0Dot} {zb : ↥M₁}

theorem autIsoOfMarked_toG_xB (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb)
    (hz : ε (β.φ1 zb) = z) : (autIsoOfMarked h hμ).toG xB = z := by
  obtain ⟨a, ha⟩ := br_lamA_mem_range12 hμ xB
  rw [autIsoOfMarked_toG h hμ ha.symm]
  have h1 : μ.φ1 ((ofSubgroups M₁ M₂).α1 a) = μ.φ1 zb := by
    rw [μ.comm1, ha]
    apply Subtype.ext
    show ((lamA xA : ↥M0Dot) : GL6) = ((μ.φ1 zb : ↥M0Dot) : GL6)
    rw [lamA_xA, hμ.z_eq]
  have h2 : (ofSubgroups M₁ M₂).α1 a = zb := br_inj1 hμ h1
  rw [← hz, ← h2]
  rfl

@[expose] noncomputable def ctxOfMarked (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb)
    (hz : ε (β.φ1 zb) = z)
    (hN : Subgroup.normalizer (centerOf (pCoreOf 2 (MiOne β ε)) : Set M) = MiOne β ε ∧
      Subgroup.normalizer (centerOf (pCoreOf 2 (MiTwo β ε)) : Set M) = MiTwo β ε) :
    @AutCtx M _ h.f431.finite_M (MiOne β ε) (MiTwo β ε) z :=
  haveI := h.f431.finite_M
  autCtxOf (autIsoOfMarked h hμ) (autIsoOfMarked_toG_xB h hμ hz)
    (br_pResidual_eq_top h.f431.he) h.f431.hb hN.1 hN.2

end Ctx


section CtxFacts

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {Tb : Subgroup E}
  {fb : ↥(M₁ ⊓ M₂)} {μ : Cpl M₁ M₂ ↥M0Dot} {zb : ↥M₁}

theorem autIsoOfMarked_toG_fhB (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb) :
    (autIsoOfMarked h hμ).toG fhB = fOf β ε fb := by
  refine autIsoOfMarked_toG h hμ (Subtype.ext ?_)
  show ((lamA fhatA : ↥M0Dot) : GL6) = ((μ.φ12 fb : ↥M0Dot) : GL6)
  rw [lamA_fhatA, hμ.f_eq]

theorem autIsoOfMarked_imgG_That (h : HypF5 Gp M₁ M₂ β ε z Tb fb)
    (hμ : IsMarkedMuIso μ zb fb Tb) :
    (autIsoOfMarked h hμ.1).imgG That = TOf β ε Tb := by
  have hT := hμ.2
  have hmemT : ∀ a : ↥(M₁ ⊓ M₂), ((μ.φ12 a : ↥M0Dot) : GL6) ∈ TDot ↔ (a : E) ∈ Tb := by
    intro a
    rw [← hT]
    constructor
    · rintro ⟨_, ⟨a', ha', rfl⟩, haa'⟩
      have : a' = a := br_inj12 hμ.1 (Subtype.ext haa')
      rw [← this]
      exact ha'
    · intro ha
      exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  ext g
  rw [AutIso.mem_imgG]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha⟩ := br_lamA_mem_range12 hμ.1 b
    rw [autIsoOfMarked_toG h hμ.1 ha.symm]
    have hbT : ((lamA (b : Ah) : ↥M0Dot) : GL6) ∈ TDot := (lamA_mem_TDot _).2 hb
    rw [← ha] at hbT
    exact ⟨a, (hmemT a).1 hbT, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb⟩ := br_exists_Bh hμ.1 a
    refine ⟨b, ?_, autIsoOfMarked_toG h hμ.1 hb⟩
    rw [← lamA_mem_TDot, hb]
    exact (hmemT a).2 ha

end CtxFacts

section MuOfIso

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

@[expose] noncomputable def muOfIso (Θ : E ≃* ↥M0Dot) (hgen : M₁ ⊔ M₂ = ⊤) :
    Cpl M₁ M₂ ↥M0Dot where
  φ1 := MonoidHom.mk' (fun a : (ofSubgroups M₁ M₂).G1 => Θ (Subtype.val a))
    (fun a b => map_mul Θ (Subtype.val a) (Subtype.val b))
  φ12 := MonoidHom.mk' (fun a : (ofSubgroups M₁ M₂).G12 => Θ (Subtype.val a))
    (fun a b => map_mul Θ (Subtype.val a) (Subtype.val b))
  φ2 := MonoidHom.mk' (fun a : (ofSubgroups M₁ M₂).G2 => Θ (Subtype.val a))
    (fun a b => map_mul Θ (Subtype.val a) (Subtype.val b))
  comm1 _ := rfl
  comm2 _ := rfl
  inter := by
    ext y
    simp only [Subgroup.mem_inf, MonoidHom.mem_range, MonoidHom.mk'_apply, ofSubgroups]
    constructor
    · rintro ⟨⟨⟨a, ha⟩, rfl⟩, ⟨⟨b, hb⟩, hbe⟩⟩
      have hab : b = a := Θ.injective hbe
      exact ⟨⟨a, ha, hab ▸ hb⟩, rfl⟩
    · rintro ⟨⟨a, ha⟩, rfl⟩
      exact ⟨⟨⟨a, ha.1⟩, rfl⟩, ⟨⟨a, ha.2⟩, rfl⟩⟩
  gen := by
    refine eq_top_iff.2 fun y _ => ?_
    have hy : Θ.symm y ∈ M₁ ⊔ M₂ := by rw [hgen]; exact Subgroup.mem_top _
    have hmap : (M₁ ⊔ M₂).map Θ.toMonoidHom ≤
        (MonoidHom.mk' (fun a : (ofSubgroups M₁ M₂).G1 => Θ (Subtype.val a))
          (fun a b => map_mul Θ (Subtype.val a) (Subtype.val b))).range ⊔
        (MonoidHom.mk' (fun a : (ofSubgroups M₁ M₂).G2 => Θ (Subtype.val a))
          (fun a b => map_mul Θ (Subtype.val a) (Subtype.val b))).range := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
    exact hmap (Subgroup.mem_map.2 ⟨Θ.symm y, hy, Θ.apply_symm_apply y⟩)

theorem muOfIso_faithful (Θ : E ≃* ↥M0Dot) (hgen : M₁ ⊔ M₂ = ⊤) :
    (muOfIso Θ hgen).IsFaithful :=
  ⟨fun a b hab => Subtype.ext (Θ.injective hab), fun a b hab => Subtype.ext (Θ.injective hab),
    fun a b hab => Subtype.ext (Θ.injective hab)⟩

theorem mu_range_map (Θ : E ≃* ↥M0Dot) {X : Subgroup E} {XDot : Subgroup GL6}
    (hXDot : XDot ≤ M0Dot) (hX : ∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ XDot ↔ x ∈ X)
    (φ : ↥X →* ↥M0Dot) (hφ : ∀ a : ↥X, φ a = Θ (a : E)) : φ.range.map M0Dot.subtype = XDot := by
  ext g
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    show ((φ a : ↥M0Dot) : GL6) ∈ XDot
    rw [hφ]
    exact (hX _).2 a.2
  · intro hg
    have hyv : ((Θ (Θ.symm ⟨g, hXDot hg⟩) : ↥M0Dot) : GL6) = g := by
      rw [MulEquiv.apply_symm_apply]
    exact ⟨_, ⟨⟨Θ.symm ⟨g, hXDot hg⟩, (hX _).1 (by rw [hyv]; exact hg)⟩, hφ _⟩, hyv⟩

theorem muOfIso_T (Θ : E ≃* ↥M0Dot) (hgen : M₁ ⊔ M₂ = ⊤) {Tb : Subgroup E}
    (hTb : Tb ≤ M₁ ⊓ M₂) (hT : ∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ TDot ↔ x ∈ Tb) :
    ((Tb.subgroupOf (M₁ ⊓ M₂)).map (muOfIso Θ hgen).φ12).map M0Dot.subtype = TDot := by
  ext g
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact (hT _).2 ha
  · intro hg
    have hg0 : g ∈ M0Dot := M1Dot_le_M0Dot (TDot_le_M12 hg).1
    have hyv : ((Θ (Θ.symm ⟨g, hg0⟩) : ↥M0Dot) : GL6) = g := by rw [MulEquiv.apply_symm_apply]
    have hyT : Θ.symm ⟨g, hg0⟩ ∈ Tb := (hT _).1 (by rw [hyv]; exact hg)
    exact ⟨_, ⟨⟨_, hTb hyT⟩, hyT, rfl⟩, hyv⟩

theorem muOfIso_marked (Θ : E ≃* ↥M0Dot) (hgen : M₁ ⊔ M₂ = ⊤) {zb : ↥M₁} {fb : ↥(M₁ ⊓ M₂)}
    {Tb : Subgroup E} (hC : NmCompat Θ Gp M₁ M₂) (hTb : Tb ≤ M₁ ⊓ M₂)
    (hT : ∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ TDot ↔ x ∈ Tb)
    (hf : ((Θ (fb : E) : ↥M0Dot) : GL6) = fDot) (hz : ((Θ (zb : E) : ↥M0Dot) : GL6) = zDot) :
    IsMarkedMuIso (muOfIso Θ hgen) zb fb Tb := by
  refine ⟨⟨muOfIso_faithful Θ hgen, ?_, ?_, ?_, hz, hf⟩, muOfIso_T Θ hgen hTb hT⟩
  · exact mu_range_map Θ M1Dot_le_M0Dot hC.1 (muOfIso Θ hgen).φ1 fun _ => rfl
  · exact mu_range_map Θ M2Dot_le_M0Dot hC.2.1 (muOfIso Θ hgen).φ2 fun _ => rfl
  · exact mu_range_map Θ (X := M₁ ⊓ M₂) (XDot := M1Dot ⊓ M2Dot) (inf_le_left.trans M1Dot_le_M0Dot)
      (fun x => ⟨fun h => ⟨(hC.1 x).1 h.1, (hC.2.1 x).1 h.2⟩,
        fun h => ⟨(hC.1 x).2 h.1, (hC.2.1 x).2 h.2⟩⟩) (muOfIso Θ hgen).φ12 fun _ => rfl

end MuOfIso

section Exists

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {Tb : Subgroup E}
  {fb : ↥(M₁ ⊓ M₂)}

theorem exists_marked_compat (h : HypF5 Gp M₁ M₂ β ε z Tb fb) :
    ∃ (Θ : E ≃* ↥M0Dot) (zb : ↥M₁), ε (β.φ1 zb) = z ∧ NmCompat Θ Gp M₁ M₂ ∧
      IsMarkedMuIso (muOfIso Θ h.f431.amalgam.gen) zb fb Tb := by
  obtain ⟨Θ, zb, hzb, hC, hT, hf, hz⟩ := exists_normIso h
  exact ⟨Θ, zb, hzb, hC, muOfIso_marked Θ _ hC h.Tb_syl.1 hT hf hz⟩

theorem exists_marked (h : HypF5 Gp M₁ M₂ β ε z Tb fb) :
    ∃ (μ : Cpl M₁ M₂ ↥M0Dot) (zb : ↥M₁), ε (β.φ1 zb) = z ∧ IsMarkedMuIso μ zb fb Tb := by
  obtain ⟨Θ, zb, hzb, -, hμ⟩ := exists_marked_compat h
  exact ⟨_, zb, hzb, hμ⟩

theorem hypF5_normalizers' (h : HypF5 Gp M₁ M₂ β ε z Tb fb) :
    Subgroup.normalizer (centerOf (pCoreOf 2 (MiOne β ε)) : Set M) = MiOne β ε ∧
      Subgroup.normalizer (centerOf (pCoreOf 2 (MiTwo β ε)) : Set M) = MiTwo β ε := by
  obtain ⟨Θ, -, -, hC, -⟩ := exists_marked_compat h
  exact hypF5_normalizers h hC

end Exists

section PhiM

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {Tb : Subgroup E}
  {fb : ↥(M₁ ⊓ M₂)} {μ : Cpl M₁ M₂ ↥M0Dot} {zb : ↥M₁}

theorem exists_PhiM (h : HypF5 Gp M₁ M₂ β ε z Tb fb) (hμ : IsMuIso μ zb fb)
    (hz : ε (β.φ1 zb) = z) :
    ∃ Φ : M ≃* ↥MDot,
      (∀ b : ↥M₁, ((Φ (ε (β.φ1 b)) : ↥MDot) : GL6) = ((μ.φ1 b : ↥M0Dot) : GL6)) ∧
      (∀ b : ↥M₂, ((Φ (ε (β.φ2 b)) : ↥MDot) : GL6) = ((μ.φ2 b : ↥M0Dot) : GL6)) := by
  haveI := h.f431.finite_M
  obtain ⟨Φ, h1, h2⟩ := autCtx_iso (ctxOfMarked h hμ hz (hypF5_normalizers' h)) modelCtx
  refine ⟨Φ, fun b => ?_, fun b => ?_⟩
  · obtain ⟨x, hx⟩ := br_exists_P1h hμ b
    have e1 : (((ctxOfMarked h hμ hz (hypF5_normalizers' h)).iso.phi1 x : ↥(MiOne β ε)) : M) =
        ε (β.φ1 b) := autIsoOfMarked_phi1 h hμ hx
    rw [← e1, h1 x, modelCtx_phi1, hx]
  · obtain ⟨x, hx⟩ := br_exists_P2h hμ b
    have e2 : (((ctxOfMarked h hμ hz (hypF5_normalizers' h)).iso.phi2 x : ↥(MiTwo β ε)) : M) =
        ε (β.φ2 b) := autIsoOfMarked_phi2 h hμ hx
    rw [← e2, h2 x, modelCtx_phi2, hx]

end PhiM

end CFSG.Quasithin.SimsF5
