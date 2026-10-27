module

public import CFSG.Quasithin.H13.VolIAltCoverUniversal
public import CFSG.Quasithin.Background.B4ModelsApi

public section

noncomputable section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Quasithin.H13.VolI Subgroup

abbrev FFModel.quotBy (D : FFModel) (N : Subgroup D.Amb) : FFModel where
  Gam := D.Gam
  Amb := D.Amb
  act := D.act
  sec := D.sec
  ker := N

namespace ModelCover

variable {D : FFModel}

theorem exists_quotient (αE : D.Gam →* MulAut ↥D.sec)
    (hαE : ∀ γ (m : ↥D.sec), (αE γ m : D.Amb) = D.act γ m)
    (hkfix : ∀ γ (m : ↥D.sec), (m : D.Amb) ∈ D.ker → αE γ m = m)
    (hgenE : ∀ m : ↥D.sec, m ∈ closure {x | ∃ γ y, x = αE γ y * y⁻¹})
    [Finite ↥D.sec] (hE2 : ∀ m : ↥D.sec, m ^ 2 = 1)
    (hbound : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ C : ModelCover D W, Nat.card C.β.ker ≤ Nat.card ↥(D.ker.subgroupOf D.sec))
    {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (C : ModelCover D V) :
    ∃ ψ : ↥D.sec →* V, Function.Surjective ψ ∧ (∀ m, ψ m = 1 → (m : D.Amb) ∈ D.ker) ∧
      (∀ γ m, ψ (αE γ m) = C.ρ γ (ψ m)) ∧ ∀ m, C.β (ψ m) = QuotientGroup.mk m := by
  classical
  set P := pullback C.β with hPdef
  set ρ₂ := prodAct αE C.ρ with hρ₂
  set W := pullComm αE C with hWdef
  have hP : ∀ γ, ∀ p ∈ P, ρ₂ γ p ∈ P := fun γ p hp => prodAct_mem_pullback hαE C γ hp
  have hWP : W ≤ P := pullComm_le_pullback hαE C
  have hWinv : ∀ l ∈ ρ₂.range, ∀ w ∈ W, l w ∈ W := by
    rintro _ ⟨δ, rfl⟩ w hw
    exact closure_comm_inv ρ₂ hP δ hw
  let ρW : D.Gam →* MulAut ↥W := (H13.VolI.resHom ρ₂.range W hWinv).comp ρ₂.rangeRestrict
  let fstW : ↥W →* V := (MonoidHom.fst V ↥D.sec).comp W.subtype
  let sndW : ↥W →* ↥D.sec := (MonoidHom.snd V ↥D.sec).comp W.subtype
  have hWmem : ∀ w : ↥W, C.β (fstW w) = QuotientGroup.mk (sndW w) := fun w => hWP w.2
  have hgW : ∀ γ (p : V × ↥D.sec), p ∈ P → ρ₂ γ p * p⁻¹ ∈ W := fun γ p hp =>
    Subgroup.subset_closure ⟨γ, p, hp, rfl⟩
  have hfst : Function.Surjective fstW := by
    intro v
    have hle : closure {x | ∃ γ w, x = C.ρ γ w * w⁻¹} ≤ W.map (MonoidHom.fst V ↥D.sec) := by
      rw [closure_le]
      rintro _ ⟨γ, u, rfl⟩
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (C.β u)
      exact ⟨_, hgW γ (u, m) hm.symm, rfl⟩
    obtain ⟨w, hw, hwv⟩ := hle (C.gen v)
    exact ⟨⟨w, hw⟩, hwv⟩
  have hsnd : Function.Surjective sndW := by
    intro m
    have hle : closure {x | ∃ γ y, x = αE γ y * y⁻¹} ≤ W.map (MonoidHom.snd V ↥D.sec) := by
      rw [closure_le]
      rintro _ ⟨γ, y, rfl⟩
      obtain ⟨u, hu⟩ := C.surj (QuotientGroup.mk y)
      exact ⟨_, hgW γ (u, y) hu, rfl⟩
    obtain ⟨w, hw, hwm⟩ := hle (hgenE m)
    exact ⟨⟨w, hw⟩, hwm⟩
  have hfixP : ∀ γ (k : V × ↥D.sec), k ∈ P → k.1 = 1 → ρ₂ γ k = k := by
    intro γ k hk hk1
    have h3 : (QuotientGroup.mk k.2 : D.Sec) = 1 := by
      rw [← mem_pullback.1 hk, hk1, map_one]
    have h2 : (k.2 : D.Amb) ∈ D.ker := mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h3)
    exact Prod.ext (by rw [prodAct_apply, hk1, map_one]) (hkfix γ _ h2)
  let CW : ModelCover D ↥W :=
    { ρ := ρW
      β := C.β.comp fstW
      surj := C.surj.comp hfst
      fix := fun γ w hw => by
        apply Subtype.ext
        have h1 : C.ρ γ (fstW w) = fstW w := C.fix γ _ hw
        have h3 : (QuotientGroup.mk (sndW w) : D.Sec) = 1 := by
          rw [← hWmem w]
          exact hw
        have h2 : (sndW w : D.Amb) ∈ D.ker := mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h3)
        exact Prod.ext h1 (hkfix γ _ h2)
      equiv := fun γ w m hm hwm => C.equiv γ (fstW w) m hm hwm
      gen := fun w => by
        have hle : pullComm αE C ≤
            (closure {x : ↥W | ∃ γ y, x = ρW γ y * y⁻¹}).map W.subtype := by
          rw [pullComm, closure_le]
          rintro _ ⟨γ, p, hp, rfl⟩
          obtain ⟨w', hw'⟩ := hfst p.1
          have hkP : p * (w' : V × ↥D.sec)⁻¹ ∈ P := mul_mem hp (inv_mem (hWP w'.2))
          have hk1 : (p * (w' : V × ↥D.sec)⁻¹).1 = 1 := by
            rw [Prod.fst_mul, Prod.fst_inv]
            exact mul_inv_eq_one.2 hw'.symm
          have hk := hfixP γ _ hkP hk1
          have e : p = p * (w' : V × ↥D.sec)⁻¹ * w' := (inv_mul_cancel_right p _).symm
          refine ⟨ρW γ w' * w'⁻¹, Subgroup.subset_closure ⟨γ, w', rfl⟩, ?_⟩
          show ρ₂ γ w' * (w' : V × ↥D.sec)⁻¹ = ρ₂ γ p * p⁻¹
          conv_rhs => rw [e, map_mul, hk]
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
        obtain ⟨x, hx, hxw⟩ := hle w.2
        rwa [show x = w from Subtype.ext hxw] at hx }
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    exact Prod.ext (by rw [Prod.pow_fst, hV2]; rfl) (by rw [Prod.pow_snd, hE2]; rfl)
  have hbW := hbound ↥W hW2 CW
  have hcW : Nat.card ↥W = Nat.card CW.β.ker * Nat.card D.Sec := CW.card_eq
  have hcE : Nat.card ↥D.sec = Nat.card D.Sec * Nat.card ↥(D.ker.subgroupOf D.sec) :=
    card_eq_card_quotient_mul_card_subgroup (D.ker.subgroupOf D.sec)
  have hle : Nat.card ↥W ≤ Nat.card ↥D.sec := by
    rw [hcW, hcE, mul_comm (Nat.card D.Sec)]
    exact Nat.mul_le_mul_right _ hbW
  have hsndb : Function.Bijective sndW := hsnd.bijective_of_nat_card_le hle
  let eE := MulEquiv.ofBijective sndW hsndb
  have heE : ∀ w, eE w = sndW w := fun _ => rfl
  refine ⟨fstW.comp eE.symm.toMonoidHom, hfst.comp eE.symm.surjective, fun m hm => ?_,
    fun γ m => ?_, fun m => ?_⟩
  · have h1 := hWmem (eE.symm m)
    have h2 : sndW (eE.symm m) = m := by rw [← heE, MulEquiv.apply_symm_apply]
    rw [h2] at h1
    have h3 : (QuotientGroup.mk m : D.Sec) = 1 := by
      rw [← h1]
      show C.β ((fstW.comp eE.symm.toMonoidHom) m) = 1
      rw [hm, map_one]
    exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h3)
  · set w := eE.symm m with hw
    have h2 : sndW w = m := by rw [hw, ← heE, MulEquiv.apply_symm_apply]
    have h3 : eE.symm (αE γ m) = ρW γ w := by
      apply eE.injective
      rw [MulEquiv.apply_symm_apply, heE]
      show αE γ m = αE γ (sndW w)
      rw [h2]
    show fstW (eE.symm (αE γ m)) = C.ρ γ (fstW w)
    rw [h3]
    rfl
  · have h1 := hWmem (eE.symm m)
    have h2 : sndW (eE.symm m) = m := by rw [← heE, MulEquiv.apply_symm_apply]
    rw [h2] at h1
    exact h1

end ModelCover

theorem realizes_quotBy {D : FFModel} (αE : D.Gam →* MulAut ↥D.sec)
    (hαE : ∀ γ (m : ↥D.sec), (αE γ m : D.Amb) = D.act γ m)
    {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} (π : D.Gam →* ↥H)
    (hπs : Function.Surjective π) (ψ : ↥D.sec →* V) (hψs : Function.Surjective ψ)
    (hψk : ∀ m, ψ m = 1 → (m : D.Amb) ∈ D.ker)
    (hψe : ∀ γ m, ψ (αE γ m) = (π γ : MulAut V) (ψ m)) :
    ∃ N ≤ D.ker, (FFModel.quotBy D N).Realizes H ⊤ ⊥ := by
  classical
  set N : Subgroup D.Amb := ψ.ker.map D.sec.subtype with hN
  have hNk : N ≤ D.ker := by
    rintro _ ⟨m, hm, rfl⟩
    exact hψk m hm
  have hNsec : N.subgroupOf D.sec = ψ.ker := by
    rw [hN]
    exact Subgroup.comap_map_eq_self_of_injective D.sec.subtype_injective ψ.ker
  let e : (↥D.sec ⧸ ψ.ker) ≃* V := QuotientGroup.quotientKerEquivOfSurjective ψ hψs
  have he : ∀ m : ↥D.sec, e (QuotientGroup.mk m) = ψ m := fun m => rfl
  have hsec : ∀ γ, ∀ m ∈ D.sec, D.act γ m ∈ D.sec := fun γ m hm => by
    rw [← hαE γ ⟨m, hm⟩]
    exact (αE γ ⟨m, hm⟩).2
  refine ⟨N, hNk, π, hπs, bot_le, ?_, fun _ _ _ => Subgroup.mem_top _, fun g z hz => ?_, hsec,
    fun γ m hm => ?_, ?_⟩
  · rintro _ ⟨m, -, rfl⟩
    exact m.2
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · obtain ⟨m', hm', rfl⟩ := hm
    have hγ : ψ (αE γ m') = 1 := by
      have h1 := hψe γ m'
      rw [h1, show ψ m' = 1 from hm', map_one]
    exact ⟨αE γ m', hγ, (hαE γ m').trans rfl⟩
  · let β : ↥(⊤ : Subgroup V) →* ↥D.sec ⧸ N.subgroupOf D.sec :=
      (QuotientGroup.quotientMulEquivOfEq hNsec.symm).toMonoidHom.comp
        (e.symm.toMonoidHom.comp (⊤ : Subgroup V).subtype)
    refine ⟨β, fun q => ?_, fun u => ?_, fun γ u m hu hm hum => ?_⟩
    · obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨⟨ψ m, Subgroup.mem_top _⟩, ?_⟩
      have h1 : e.symm (ψ m) = QuotientGroup.mk m := e.symm_apply_eq.2 (he m).symm
      show QuotientGroup.quotientMulEquivOfEq hNsec.symm (e.symm (ψ m)) = _
      rw [h1]
      rfl
    · show QuotientGroup.quotientMulEquivOfEq hNsec.symm (e.symm u) = 1 ↔ (u : V) ∈ ⊥
      rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, Subgroup.mem_bot]
    ·
      have hu' : (u : V) = ψ m := by
        have h1 : e.symm (u : V) = QuotientGroup.mk m := by
          apply (QuotientGroup.quotientMulEquivOfEq hNsec.symm).injective
          exact hum
        rw [← he, ← h1, MulEquiv.apply_symm_apply]
      show QuotientGroup.quotientMulEquivOfEq hNsec.symm
          (e.symm ((π γ : MulAut V) (u : V))) = QuotientGroup.mk ⟨D.act γ m, hm⟩
      have h2 : (π γ : MulAut V) (u : V) = ψ ⟨D.act γ m, hm⟩ := by
        rw [hu', ← hψe]
        congr 1
        exact Subtype.ext (hαE γ m)
      have h3 : e.symm (ψ ⟨D.act γ m, hm⟩) = QuotientGroup.mk ⟨D.act γ m, hm⟩ :=
        e.symm_apply_eq.2 (he _).symm
      rw [h2, h3]
      rfl

@[expose] def secAut {D : FFModel} (hD : D.IsActionModel) : D.Gam →* MulAut ↥D.sec where
  toFun γ :=
    { toFun := hD.actSec γ
      invFun := hD.actSec γ⁻¹
      left_inv := fun m => Subtype.ext (hD.act_inv_act γ m)
      right_inv := fun m => by
        apply Subtype.ext
        show D.act γ (D.act γ⁻¹ m) = m
        exact hD.act_act_inv γ m
      map_mul' := fun m n => map_mul (hD.actSec γ) m n }
  map_one' := MulEquiv.ext fun m => Subtype.ext (hD.act_one m)
  map_mul' γ δ := MulEquiv.ext fun m => Subtype.ext (hD.act_mul_act γ δ m)

theorem ModelCover.realizesVia_range {D : FFModel} (hD : D.IsActionModel) {W : Type*}
    [CommGroup W] (C : ModelCover D W) :
    D.RealizesVia C.ρ.range ⊤ C.β.ker C.ρ.rangeRestrict := by
  refine ⟨C.ρ.rangeRestrict_surjective, le_top, hD.ker_le, fun _ _ _ => Subgroup.mem_top _,
    fun h z hz => ?_, hD.sec_inv, hD.ker_inv, C.β.comp (⊤ : Subgroup W).subtype,
    fun q => ?_, fun u => ?_, fun γ u m hu hm hum => ?_⟩
  · obtain ⟨γ, hγ⟩ := h.2
    rw [MonoidHom.mem_ker] at hz ⊢
    have : (h : MulAut W) z = z := by rw [← hγ]; exact C.fix γ z hz
    rw [this, hz]
  · obtain ⟨w, hw⟩ := C.surj q
    exact ⟨⟨w, Subgroup.mem_top w⟩, hw⟩
  · rfl
  · exact C.equiv γ u m hm hum

theorem ModelCover.commOf_range {D : FFModel} {W : Type*} [CommGroup W] (C : ModelCover D W) :
    XMod.commOf ↥C.ρ.range (⊤ : Subgroup W) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  refine Subgroup.closure_mono ?_ (C.gen w)
  rintro _ ⟨γ, v, rfl⟩
  exact ⟨⟨C.ρ γ, γ, rfl⟩, v, Subgroup.mem_top v, rfl⟩

theorem exists_quotBy_of_realizes {D : FFModel} (hD : D.IsActionModel)
    (hkfix : ∀ γ, ∀ m ∈ D.ker, D.act γ m = m)
    (hgenE : ∀ m ∈ D.sec, m ∈ closure {x | ∃ γ, ∃ y ∈ D.sec, x = D.act γ y * y⁻¹})
    [Finite ↥D.sec] (hE2 : ∀ m ∈ D.sec, m ^ 2 = 1)
    (hbound : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (L : Subgroup (MulAut W)) (Z : Subgroup W) (π : D.Gam →* ↥L),
        D.RealizesVia L ⊤ Z π → Z ≤ fixV L → XMod.commOf ↥L (⊤ : Subgroup W) = ⊤ →
          Nat.card Z ≤ Nat.card ↥(D.ker.subgroupOf D.sec))
    {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    {Z : Subgroup V} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤) (h : D.Realizes H ⊤ Z) :
    ∃ N ≤ D.ker, (FFModel.quotBy D N).Realizes H ⊤ ⊥ := by
  obtain ⟨C, π, hπs, hρ, -⟩ := ModelCover.exists_of_realizes hZ hcomm h
  have hkfix' : ∀ γ (m : ↥D.sec), (m : D.Amb) ∈ D.ker → secAut hD γ m = m :=
    fun γ m hm => Subtype.ext (hkfix γ m hm)
  have hgen' : ∀ m : ↥D.sec, m ∈ closure {x | ∃ γ y, x = secAut hD γ y * y⁻¹} := by
    intro m
    have hle : closure {x | ∃ γ, ∃ y ∈ D.sec, x = D.act γ y * y⁻¹} ≤
        (closure {x : ↥D.sec | ∃ γ y, x = secAut hD γ y * y⁻¹}).map D.sec.subtype := by
      rw [closure_le]
      rintro _ ⟨γ, y, hy, rfl⟩
      exact ⟨secAut hD γ ⟨y, hy⟩ * ⟨y, hy⟩⁻¹, Subgroup.subset_closure ⟨γ, ⟨y, hy⟩, rfl⟩, rfl⟩
    obtain ⟨m', hm', hmm'⟩ := hle (hgenE m m.2)
    rwa [show m' = m from Subtype.ext hmm'] at hm'
  have hE2' : ∀ m : ↥D.sec, m ^ 2 = 1 := fun m => Subtype.ext (by simpa using hE2 m m.2)
  have hbound' : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ C : ModelCover D W, Nat.card C.β.ker ≤ Nat.card ↥(D.ker.subgroupOf D.sec) :=
    fun W _ _ hW C => hbound W hW C.ρ.range C.β.ker C.ρ.rangeRestrict (MS93.ModelCover.realizesVia_range hD C)
      (fun z hz x hx => by
        obtain ⟨γ, rfl⟩ := hx
        exact C.fix γ z (MonoidHom.mem_ker.1 hz))
      (MS93.ModelCover.commOf_range C)
  obtain ⟨ψ, hψs, hψk, hψe, -⟩ :=
    ModelCover.exists_quotient (secAut hD) (fun _ _ => rfl) hkfix' hgen' hE2' hbound' hV2 C
  exact realizes_quotBy (secAut hD) (fun _ _ => rfl) π hπs ψ hψs hψk
    (fun γ m => by rw [hψe, hρ])

end CFSG.Quasithin.MS93
