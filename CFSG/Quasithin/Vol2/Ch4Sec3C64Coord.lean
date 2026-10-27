module

public import CFSG.Quasithin.H13.A7NatI16
public import CFSG.Quasithin.H13.A7NatSchur
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Kernel

public section

namespace CFSG.Quasithin.H13.Ch4.C64

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv
open scoped IsMulCommutative

variable {G : Type} [Group G]

structure A7Blk (L : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (β : ↥(blockU L) →* Multiplicative (AltHeart 7)) : Prop where
  short : IsShort2 L
  surj : Function.Surjective α
  ker : α.ker = CFSG.pCore 2 ↥L
  bsurj : Function.Surjective β
  bker : β.ker = (blockZ L).subgroupOf (blockU L)
  equiv : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
    ∀ x : ↥(evenWeight 7), (QuotientAddGroup.mk x : AltHeart 7) = Multiplicative.toAdd (β u) →
      (QuotientAddGroup.mk (permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) x) : AltHeart 7) =
        Multiplicative.toAdd (β v)

theorem odd_seven : Odd 7 := by decide

@[expose] noncomputable def heartEquiv : ↥(evenWeight 7) ≃+ AltHeart 7 :=
  AddEquiv.ofBijective (QuotientAddGroup.mk' (constWeight 7)) (altHeart_mk_bijective odd_seven)

theorem heartEquiv_apply (x : ↥(evenWeight 7)) :
    heartEquiv x = (QuotientAddGroup.mk x : AltHeart 7) := rfl

theorem heartEquiv_symm_mk (x : ↥(evenWeight 7)) :
    heartEquiv.symm (QuotientAddGroup.mk x : AltHeart 7) = x := by
  rw [AddEquiv.symm_apply_eq]
  rfl

theorem mem_evenWeight_iff {e : Fin 7 → ZMod 2} :
    e ∈ evenWeight 7 ↔ e ∈ SteinbergCB.evenWeight 7 := by
  rw [SteinbergCB.mem_evenWeight]
  simp [evenWeight]

section Coords

variable {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
  {β : ↥(blockU L) →* Multiplicative (AltHeart 7)}

@[expose] noncomputable def crd (β : ↥(blockU L) →* Multiplicative (AltHeart 7))
    (u : ↥(blockU L)) : Fin 7 → ZMod 2 :=
  ((heartEquiv.symm (Multiplicative.toAdd (β u)) : ↥(evenWeight 7)) : Fin 7 → ZMod 2)

theorem crd_mul (u v : ↥(blockU L)) : crd β (u * v) = crd β u + crd β v := by
  simp [crd, map_mul, toAdd_mul]

theorem crd_one : crd β 1 = 0 := by
  simp [crd]

theorem crd_mem (u : ↥(blockU L)) : crd β u ∈ SteinbergCB.evenWeight 7 :=
  mem_evenWeight_iff.1 (heartEquiv.symm (Multiplicative.toAdd (β u))).2

theorem crd_eq_zero_iff (h : A7Blk L α β) (u : ↥(blockU L)) :
    crd β u = 0 ↔ (u : G) ∈ blockZ L := by
  constructor
  · intro hu
    have h1 : heartEquiv.symm (Multiplicative.toAdd (β u)) = 0 := Subtype.ext hu
    have h2 : β u = 1 := by
      have h3 := congrArg heartEquiv h1
      rw [AddEquiv.apply_symm_apply, map_zero] at h3
      exact Multiplicative.toAdd.injective (h3.trans toAdd_one.symm)
    have h4 : u ∈ β.ker := h2
    rw [h.bker] at h4
    exact h4
  · intro hu
    have h4 : u ∈ β.ker := by
      rw [h.bker]
      exact hu
    have h2 : β u = 1 := h4
    simp [crd, h2]

theorem exists_crd_eq (h : A7Blk L α β) {e : Fin 7 → ZMod 2}
    (he : e ∈ SteinbergCB.evenWeight 7) : ∃ u : ↥(blockU L), crd β u = e := by
  obtain ⟨u, hu⟩ := h.bsurj (Multiplicative.ofAdd (heartEquiv ⟨e, mem_evenWeight_iff.2 he⟩))
  refine ⟨u, ?_⟩
  simp [crd, hu]

theorem crd_conj (h : A7Blk L α β) (ℓ : ↥L) (u v : ↥(blockU L))
    (huv : (v : G) = ℓ * u * ℓ⁻¹) :
    crd β v = SteinbergCB.permAct7 (α ℓ : Perm (Fin 7)) (crd β u) := by
  set x := heartEquiv.symm (Multiplicative.toAdd (β u)) with hx
  have hmk : (QuotientAddGroup.mk x : AltHeart 7) = Multiplicative.toAdd (β u) := by
    rw [← heartEquiv_apply, hx, AddEquiv.apply_symm_apply]
  have h1 := h.equiv ℓ u v huv x hmk
  have h2 : heartEquiv.symm (Multiplicative.toAdd (β v)) =
      permWeight 7 (α ℓ : Perm (Fin 7)) x := by
    rw [← h1, heartEquiv_symm_mk]
  funext i
  simp only [crd]
  rw [h2]
  rfl

end Coords

section Natural

variable [Finite G] {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
  {β : ↥(blockU L) →* Multiplicative (AltHeart 7)}

@[expose] noncomputable def actU (L : Subgroup G) : ↥L →* ↥(autOn L (blockU L)) :=
  ((conjAct (blockU L)).comp (Subgroup.inclusion (C1.le_normalizer_blockU L))).codRestrict
    (autOn L (blockU L)) fun l => Subgroup.mem_map_of_mem _
      (show Subgroup.inclusion (C1.le_normalizer_blockU L) l ∈
        L.subgroupOf (Subgroup.normalizer (blockU L : Set G)) from l.2)

theorem actU_apply (l : ↥L) (u : ↥(blockU L)) :
    ((((actU L l : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) u : ↥(blockU L)) : G) =
      l * u * (l : G)⁻¹ := rfl

theorem actU_surjective : Function.Surjective (actU L) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨⟨g, hgN⟩, hgL, rfl⟩ := Subgroup.mem_map.1 hφ
  exact ⟨⟨g, hgL⟩, rfl⟩

theorem A7Blk.ker_le_ker (h : A7Blk L α β) : α.ker ≤ (actU L).ker := by
  intro l hl
  rw [h.ker] at hl
  have hlQ : (l : G) ∈ blockQ L := (L246.mem_blockQ_iff l).2 hl
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  rw [actU_apply]
  show (l : G) * u * (l : G)⁻¹ = u
  rw [← C1.blockU_comm h.short u u.2 l hlQ]
  group

theorem A7Blk.alternatingNatural [IsMulCommutative ↥(blockU L)] (h : A7Blk L α β) :
    AlternatingNatural (V := ↥(blockU L)) (autOn L (blockU L)) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf (blockU L)) 7 := by
  classical
  set e := QuotientGroup.quotientKerEquivOfSurjective α h.surj with he
  set π : ↥(alternatingGroup (Fin 7)) →* ↥(autOn L (blockU L)) :=
    (QuotientGroup.lift α.ker (actU L) h.ker_le_ker).comp e.symm.toMonoidHom with hπ
  have hπα : ∀ l : ↥L, π (α l) = actU L l := by
    intro l
    have h1 : e.symm (α l) = (l : ↥L ⧸ α.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
    rfl
  have hπs : Function.Surjective π := by
    intro φ
    obtain ⟨l, rfl⟩ := actU_surjective φ
    exact ⟨α l, hπα l⟩
  refine ⟨π, hπs, le_top, inf_le_right, fun _ _ _ => Subgroup.mem_top _, ?_, ?_, ?_, ?_⟩
  ·
    rintro φ z hz
    obtain ⟨l, rfl⟩ := actU_surjective φ
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    have hlz : (l : G) * z = z * l := Subgroup.mem_centralizer_iff.1 hz l l.2
    have e1 : (((actU L l : ↥(autOn L (blockU L))) : MulAut ↥(blockU L)) z : G) = z := by
      rw [actU_apply, hlz]
      group
    rw [e1]
    exact hz
  · intro γ m hm
    exact G6.permAct_mem_coreMod _ hm
  · intro γ m hm
    rw [L246.altDn_ker_eq_bot odd_seven] at hm ⊢
    rw [Subgroup.mem_bot] at hm ⊢
    rw [hm]
    show G6.permAct 7 _ 1 = 1
    exact map_one _
  ·
    let toQ : Multiplicative ↥(evenWeight 7) →*
        ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec :=
      (QuotientGroup.mk' _).comp (L246.coreEquiv 7).symm.toMonoidHom
    have htoQ : Function.Injective toQ := by
      intro a b hab
      have h1 := QuotientGroup.eq.1 hab
      rw [L246.altDn_ker_subgroupOf_eq_bot odd_seven, Subgroup.mem_bot, inv_mul_eq_one] at h1
      exact (L246.coreEquiv 7).symm.injective h1
    have htoQs : Function.Surjective toQ := by
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨L246.coreEquiv 7 m, by simp [toQ]⟩
    let hE : Multiplicative (AltHeart 7) →* Multiplicative ↥(evenWeight 7) :=
      AddMonoidHom.toMultiplicative heartEquiv.symm.toAddMonoidHom
    have hEinj : Function.Injective hE := fun a b hab =>
      Multiplicative.toAdd.injective (heartEquiv.symm.injective
        (congrArg Multiplicative.toAdd hab))
    have hEs : Function.Surjective hE := fun x =>
      ⟨Multiplicative.ofAdd (heartEquiv (Multiplicative.toAdd x)), by simp [hE]⟩
    let β'' : ↥(⊤ : Subgroup ↥(blockU L)) →*
        ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec :=
      toQ.comp (hE.comp (β.comp (⊤ : Subgroup ↥(blockU L)).subtype))
    refine ⟨β'', ?_, ?_, ?_⟩
    · intro q
      obtain ⟨x, rfl⟩ := htoQs q
      obtain ⟨y, rfl⟩ := hEs x
      obtain ⟨u, rfl⟩ := h.bsurj y
      exact ⟨⟨u, Subgroup.mem_top u⟩, rfl⟩
    · intro w
      have hw : β'' w = 1 ↔ β (w : ↥(blockU L)) = 1 := by
        constructor
        · intro h1
          apply hEinj
          apply htoQ
          rw [map_one, map_one]
          exact h1
        · intro h1
          show toQ (hE (β (w : ↥(blockU L)))) = 1
          rw [h1, map_one, map_one]
      rw [hw, ← MonoidHom.mem_ker, h.bker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact ⟨fun h1 => h1.2, fun h1 => ⟨(w : ↥(blockU L)).2, h1⟩⟩
    · intro γ w m hw hm hwm
      obtain ⟨l, rfl⟩ := h.surj γ
      have hmk_inj : ∀ a b : ↥(FFModel.altDn 7).sec,
          (QuotientGroup.mk a : ↥(FFModel.altDn 7).sec ⧸
            (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec) = QuotientGroup.mk b →
            a = b := by
        intro a b hab
        have h1 := QuotientGroup.eq.1 hab
        rw [L246.altDn_ker_subgroupOf_eq_bot odd_seven, Subgroup.mem_bot, inv_mul_eq_one] at h1
        exact h1
      set x := heartEquiv.symm (Multiplicative.toAdd (β (w : ↥(blockU L)))) with hx
      have hmx : m = (L246.coreEquiv 7).symm (Multiplicative.ofAdd x) := (hmk_inj _ _ hwm).symm
      have hconj : (((((π (α l) : ↥(autOn L (blockU L))) : MulAut ↥(blockU L))
          (w : ↥(blockU L))) : ↥(blockU L)) : G) = l * (w : ↥(blockU L)) * (l : G)⁻¹ := by
        rw [hπα l, actU_apply]
      generalize hw₁ : (((π (α l) : ↥(autOn L (blockU L))) : MulAut ↥(blockU L))
          (w : ↥(blockU L))) = w₁ at hw hconj
      have hmkx : (QuotientAddGroup.mk x : AltHeart 7) =
          Multiplicative.toAdd (β (w : ↥(blockU L))) := by
        rw [← heartEquiv_apply, hx, AddEquiv.apply_symm_apply]
      have h1 := h.equiv l (w : ↥(blockU L)) w₁ hconj x hmkx
      have h2 : heartEquiv.symm (Multiplicative.toAdd (β w₁)) =
          permWeight 7 (α l : Perm (Fin 7)) x := by
        rw [← h1, heartEquiv_symm_mk]
      show (QuotientGroup.mk ((L246.coreEquiv 7).symm (hE (β w₁))) :
        ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec) = _
      congr 1
      apply Subtype.ext
      subst hmx
      show ((L246.coreEquiv 7).symm (Multiplicative.ofAdd (heartEquiv.symm
        (Multiplicative.toAdd (β w₁)))) : (FFModel.altDn 7).Amb) =
        (FFModel.altDn 7).act (α l)
          (((L246.coreEquiv 7).symm (Multiplicative.ofAdd x)) : (FFModel.altDn 7).Amb)
      rw [h2]
      rfl

theorem A7Blk.blockZ_eq_bot (h : A7Blk L α β) : blockZ L = ⊥ := by
  have : IsMulCommutative ↥(blockU L) :=
    ⟨⟨fun a b => Subtype.ext (C1.blockU_comm h.short a a.2 b
      (C1.blockU_le_blockQ h.short b.2))⟩⟩
  exact H13.A7.asI16AltSevenCover_holds G L (blockU L) (C1.blockU_sq h.short)
    (C1.le_normalizer_blockU L) (C1.commutator_blockU h.short) h.alternatingNatural

theorem A7Blk.crd_injective (h : A7Blk L α β) : Function.Injective (crd β) := by
  intro u v huv
  have h1 : crd β (u⁻¹ * v) = 0 := by
    rw [crd_mul, ← huv, ← crd_mul, inv_mul_cancel, crd_one]
  rw [crd_eq_zero_iff h, h.blockZ_eq_bot, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.1 (Subtype.ext h1)

@[expose] noncomputable def A7Blk.psi (h : A7Blk L α β) :
    ↥(blockU L) ≃* Multiplicative ↥(SteinbergCB.evenWeight 7) :=
  MulEquiv.ofBijective
    ({ toFun := fun u => Multiplicative.ofAdd ⟨crd β u, crd_mem u⟩
       map_one' := by
         apply Multiplicative.toAdd.injective
         apply Subtype.ext
         exact crd_one
       map_mul' := fun u v => by
         apply Multiplicative.toAdd.injective
         apply Subtype.ext
         exact crd_mul u v } : ↥(blockU L) →* Multiplicative ↥(SteinbergCB.evenWeight 7))
    ⟨fun u v huv => h.crd_injective (congrArg Subtype.val (Multiplicative.toAdd.injective
      (congrArg Multiplicative.toAdd huv))), fun e => by
        obtain ⟨u, hu⟩ := exists_crd_eq h (Multiplicative.toAdd e).2
        exact ⟨u, Multiplicative.toAdd.injective (Subtype.ext hu)⟩⟩

theorem A7Blk.vec_psi (h : A7Blk L α β) (u : ↥(blockU L)) : H13.A7.vec h.psi u = crd β u := rfl

theorem A7Blk.isCoordAct (h : A7Blk L α β) (l : ↥L) :
    H13.A7.IsCoordAct h.psi (l : G) (α l : Perm (Fin 7)) := fun x y hxy => by
  rw [h.vec_psi, h.vec_psi]
  exact crd_conj h l x y hxy

theorem A7Blk.isCoordAct_of_normalizes (h : A7Blk L α β) {r : G}
    (hr : r ∈ Subgroup.normalizer (L : Set G)) {σ : Perm (Fin 7)}
    (hσ : ∀ k k' : ↥L, (k' : G) = r * k * r⁻¹ →
      ((α k' : alternatingGroup (Fin 7)) : Perm (Fin 7)) = σ * (α k : Perm (Fin 7)) * σ⁻¹) :
    H13.A7.IsCoordAct h.psi r σ := by
  classical
  set ψ := h.psi with hψ
  have hrU : r ∈ Subgroup.normalizer (blockU L : Set G) := C1.mem_normalizer_blockU hr
  let c : ↥(blockU L) → ↥(blockU L) := fun x =>
    ⟨r * x * r⁻¹, (Subgroup.mem_normalizer_iff.1 hrU x).1 x.2⟩
  have hcmul : ∀ x y : ↥(blockU L), c (x * y) = c x * c y := fun x y => Subtype.ext (by
    show r * (x * y : G) * r⁻¹ = r * x * r⁻¹ * (r * y * r⁻¹)
    group)
  let f : (Fin 7 → ZMod 2) → Fin 7 → ZMod 2 := fun e =>
    if he : e ∈ SteinbergCB.evenWeight 7 then
      H13.A7.vec ψ (c (ψ.symm (Multiplicative.ofAdd ⟨e, he⟩))) else 0
  have hsymm : ∀ x : ↥(blockU L),
      ψ.symm (Multiplicative.ofAdd ⟨H13.A7.vec ψ x, H13.A7.vec_mem ψ x⟩) = x := by
    intro x
    rw [MulEquiv.symm_apply_eq]
    rfl
  have hf : ∀ x : ↥(blockU L), f (H13.A7.vec ψ x) = H13.A7.vec ψ (c x) := by
    intro x
    simp only [f, H13.A7.vec_mem ψ x, ↓reduceDIte, hsymm]
  let g : (Fin 7 → ZMod 2) → Fin 7 → ZMod 2 := fun e => SteinbergCB.permAct7 σ⁻¹ (f e)
  have hgid := H13.A7.eq_self_of_commute_alternating (g := g)
    (fun e he => by
      obtain ⟨x, rfl⟩ := H13.A7.exists_vec_eq ψ he
      exact SteinbergCB.permAct7_mem_evenWeight _ (by rw [hf]; exact H13.A7.vec_mem ψ _))
    (fun e he e' he' => by
      obtain ⟨x, rfl⟩ := H13.A7.exists_vec_eq ψ he
      obtain ⟨y, rfl⟩ := H13.A7.exists_vec_eq ψ he'
      simp only [g]
      rw [← H13.A7.vec_mul, hf, hf, hf, hcmul, H13.A7.vec_mul, map_add])
    (fun e he hg0 => by
      obtain ⟨x, rfl⟩ := H13.A7.exists_vec_eq ψ he
      have h1 : f (H13.A7.vec ψ x) = 0 := by
        have h2 := congrArg (SteinbergCB.permAct7 σ) hg0
        simp only [g] at h2
        rw [← SteinbergCB.permAct7_mul, mul_inv_cancel, SteinbergCB.permAct7_one,
          map_zero] at h2
        exact h2
      rw [hf, H13.A7.vec_eq_zero_iff] at h1
      have hx : x = 1 := by
        have h3 : (r * x * r⁻¹ : G) = 1 := congrArg Subtype.val h1
        have h4 : (x : G) = 1 := by
          calc (x : G) = r⁻¹ * (r * x * r⁻¹) * r := by group
            _ = 1 := by rw [h3]; group
        exact Subtype.ext h4
      rw [hx, H13.A7.vec_one])
    (fun τ hτ e he => by
      obtain ⟨l, hl⟩ := h.surj ⟨τ, hτ⟩
      obtain ⟨x, rfl⟩ := H13.A7.exists_vec_eq ψ he
      have hτl : τ = (α l : Perm (Fin 7)) := by rw [hl]
      let y : ↥(blockU L) := ⟨l * x * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.1 (C1.le_normalizer_blockU L l.2) x).1 x.2⟩
      have hy : H13.A7.vec ψ y = SteinbergCB.permAct7 τ (H13.A7.vec ψ x) := by
        rw [hτl]
        exact h.isCoordAct l x y rfl
      let k' : ↥L := ⟨r * l * r⁻¹, (Subgroup.mem_normalizer_iff.1 hr l).1 l.2⟩
      have hk' := hσ l k' rfl
      have hcy : (c y : G) = k' * (c x) * (k' : G)⁻¹ := by
        show r * (l * x * (l : G)⁻¹) * r⁻¹ = r * l * r⁻¹ * (r * x * r⁻¹) * (r * l * r⁻¹)⁻¹
        group
      have h1 := h.isCoordAct k' (c x) (c y) hcy
      simp only [g]
      rw [← hy, hf, hf, h1, hk', ← SteinbergCB.permAct7_mul, ← SteinbergCB.permAct7_mul,
        hτl]
      congr 1
      group)
  intro x y hxy
  have hyx : y = c x := Subtype.ext hxy
  have h1 := hgid (H13.A7.vec ψ x) (H13.A7.vec_mem ψ x)
  simp only [g] at h1
  have h2 := congrArg (SteinbergCB.permAct7 σ) h1
  rw [← SteinbergCB.permAct7_mul, mul_inv_cancel, SteinbergCB.permAct7_one, hf] at h2
  rw [hyx, h2]

end Natural

end CFSG.Quasithin.H13.Ch4.C64
