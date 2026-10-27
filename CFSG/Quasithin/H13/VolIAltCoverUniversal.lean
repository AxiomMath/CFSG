module

public import CFSG.Quasithin.H13.VolII16SLNat

public section

noncomputable section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin Subgroup

structure ModelCover (D : FFModel) (V : Type*) [CommGroup V] where
  ρ : D.Gam →* MulAut V
  β : V →* D.Sec
  surj : Function.Surjective β
  fix : ∀ γ v, β v = 1 → ρ γ v = v
  equiv : ∀ γ v (m : ↥D.sec) (hm : D.act γ (m : D.Amb) ∈ D.sec), β v = QuotientGroup.mk m →
    β (ρ γ v) = QuotientGroup.mk (⟨D.act γ (m : D.Amb), hm⟩ : ↥D.sec)
  gen : ∀ v : V, v ∈ closure {x | ∃ γ w, x = ρ γ w * w⁻¹}

namespace ModelCover

variable {D : FFModel}

theorem exists_of_realizes {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {Z : Subgroup V}
    (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤) (h : D.Realizes H ⊤ Z) :
    ∃ (C : ModelCover D V) (π : D.Gam →* ↥H), Function.Surjective π ∧
      (∀ γ, C.ρ γ = (π γ : MulAut V)) ∧ ∀ v, C.β v = 1 ↔ v ∈ Z := by
  obtain ⟨π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  let β' : V →* D.Sec :=
    { toFun := fun v => β ⟨v, mem_top v⟩
      map_one' := map_one β
      map_mul' := fun x y => map_mul β ⟨x, mem_top x⟩ ⟨y, mem_top y⟩ }
  have hρH : ∀ γ, (H.subtype.comp π) γ ∈ H := fun γ => (π γ).2
  have hρs : ∀ x ∈ H, ∃ γ, (H.subtype.comp π) γ = x := fun x hx => by
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    exact ⟨γ, congrArg Subtype.val hγ⟩
  refine ⟨⟨H.subtype.comp π, β', fun s => ?_, fun γ v hv => ?_,
    fun γ v m hm hvm => hβe γ ⟨v, mem_top v⟩ m (mem_top _) hm hvm,
    mem_closure_of_commV hρH hρs hcomm⟩, π, hπs, fun _ => rfl, fun v => hβk ⟨v, mem_top v⟩⟩
  · obtain ⟨u, hu⟩ := hβs s
    exact ⟨u, hu⟩
  · exact hZ ((hβk ⟨v, mem_top v⟩).1 hv) _ (π γ).2

theorem card_eq {V : Type*} [CommGroup V] (C : ModelCover D V) :
    Nat.card V = Nat.card C.β.ker * Nat.card D.Sec := by
  rw [← card_ker_mul_card_range C.β, MonoidHom.range_eq_top.2 C.surj, card_top]

end ModelCover

section Pullback

variable {D : FFModel} {V : Type*} [CommGroup V]

@[expose] def prodAct (αE : D.Gam →* MulAut ↥D.sec) (ρ : D.Gam →* MulAut V) :
    D.Gam →* MulAut (V × ↥D.sec) where
  toFun γ := MulEquiv.prodCongr (ρ γ) (αE γ)
  map_one' := MulEquiv.ext fun x => by
    rw [map_one, map_one]
    rfl
  map_mul' γ δ := MulEquiv.ext fun x => by
    rw [map_mul, map_mul]
    rfl

theorem prodAct_apply (αE : D.Gam →* MulAut ↥D.sec) (ρ : D.Gam →* MulAut V) (γ : D.Gam)
    (x : V × ↥D.sec) : prodAct αE ρ γ x = (ρ γ x.1, αE γ x.2) := rfl

@[expose] def pullback (β : V →* D.Sec) : Subgroup (V × ↥D.sec) where
  carrier := {p | β p.1 = QuotientGroup.mk p.2}
  one_mem' := by
    show β 1 = QuotientGroup.mk 1
    rw [map_one, QuotientGroup.mk_one]
  mul_mem' := fun {p q} hp hq => by
    show β (p.1 * q.1) = QuotientGroup.mk (p.2 * q.2)
    rw [map_mul, QuotientGroup.mk_mul, show β p.1 = _ from hp, show β q.1 = _ from hq]
  inv_mem' := fun {p} hp => by
    show β p.1⁻¹ = QuotientGroup.mk p.2⁻¹
    rw [map_inv, QuotientGroup.mk_inv, show β p.1 = _ from hp]

theorem mem_pullback {β : V →* D.Sec} {p : V × ↥D.sec} :
    p ∈ pullback β ↔ β p.1 = QuotientGroup.mk p.2 := Iff.rfl

@[expose] def pullComm (αE : D.Gam →* MulAut ↥D.sec) (C : ModelCover D V) :
    Subgroup (V × ↥D.sec) :=
  closure {x | ∃ γ, ∃ p ∈ pullback C.β, x = prodAct αE C.ρ γ p * p⁻¹}

variable {αE : D.Gam →* MulAut ↥D.sec}

theorem prodAct_mem_pullback (hαE : ∀ γ (m : ↥D.sec), (αE γ m : D.Amb) = D.act γ m)
    (C : ModelCover D V) (γ : D.Gam) {p : V × ↥D.sec} (hp : p ∈ pullback C.β) :
    prodAct αE C.ρ γ p ∈ pullback C.β := by
  have hm : D.act γ (p.2 : D.Amb) ∈ D.sec := by
    rw [← hαE]
    exact (αE γ p.2).2
  show C.β (C.ρ γ p.1) = QuotientGroup.mk (αE γ p.2)
  rw [C.equiv γ p.1 p.2 hm hp]
  congr 1
  exact Subtype.ext (hαE γ p.2).symm

theorem pullComm_le_pullback (hαE : ∀ γ (m : ↥D.sec), (αE γ m : D.Amb) = D.act γ m)
    (C : ModelCover D V) : pullComm αE C ≤ pullback C.β := by
  rw [pullComm, closure_le]
  rintro _ ⟨γ, p, hp, rfl⟩
  exact mul_mem (prodAct_mem_pullback hαE C γ hp) (inv_mem hp)

end Pullback

theorem closure_comm_inv {G X : Type*} [Group G] [CommGroup X] (ρ : G →* MulAut X)
    {P : Subgroup X} (hP : ∀ γ, ∀ p ∈ P, ρ γ p ∈ P) (δ : G) {x : X}
    (hx : x ∈ closure {x | ∃ γ, ∃ p ∈ P, x = ρ γ p * p⁻¹}) :
    ρ δ x ∈ closure {x | ∃ γ, ∃ p ∈ P, x = ρ γ p * p⁻¹} := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, p, hp, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨δ * γ * δ⁻¹, ρ δ p, hP δ p hp, ?_⟩
    have e : ρ (δ * γ * δ⁻¹) (ρ δ p) = ρ δ (ρ γ p) := by
      rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [e, map_mul, map_inv]
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

namespace ModelCover

variable {D : FFModel}

theorem exists_mulEquiv (αE : D.Gam →* MulAut ↥D.sec)
    (hαE : ∀ γ (m : ↥D.sec), (αE γ m : D.Amb) = D.act γ m)
    (hkfix : ∀ γ (m : ↥D.sec), (m : D.Amb) ∈ D.ker → αE γ m = m)
    (hk2 : Nat.card ↥(D.ker.subgroupOf D.sec) = 2)
    (hgenE : ∀ m : ↥D.sec, m ∈ closure {x | ∃ γ y, x = αE γ y * y⁻¹})
    [Finite ↥D.sec] (hE2 : ∀ m : ↥D.sec, m ^ 2 = 1)
    (hbound : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ C : ModelCover D W, Nat.card C.β.ker ≤ 2)
    {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (C : ModelCover D V)
    (hZ : Nat.card C.β.ker = 2) :
    ∃ Φ : V ≃* ↥D.sec, ∀ γ v, Φ (C.ρ γ v) = αE γ (Φ v) := by
  classical
  set P := pullback C.β with hPdef
  set ρ₂ := prodAct αE C.ρ with hρ₂
  set W := pullComm αE C with hWdef
  have hP : ∀ γ, ∀ p ∈ P, ρ₂ γ p ∈ P := fun γ p hp => prodAct_mem_pullback hαE C γ hp
  have hWP : W ≤ P := pullComm_le_pullback hαE C
  have hWinv : ∀ l ∈ ρ₂.range, ∀ w ∈ W, l w ∈ W := by
    rintro _ ⟨δ, rfl⟩ w hw
    exact closure_comm_inv ρ₂ hP δ hw
  let ρW : D.Gam →* MulAut ↥W := (resHom ρ₂.range W hWinv).comp ρ₂.rangeRestrict
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
  have hcV : Nat.card V = 2 * Nat.card D.Sec := by rw [C.card_eq, hZ]
  have hVW : Nat.card V ≤ Nat.card ↥W := Nat.card_le_card_of_surjective _ hfst
  have hcard : Nat.card ↥W = Nat.card V := by
    have : Nat.card ↥W ≤ 2 * Nat.card D.Sec := by
      rw [hcW]
      exact Nat.mul_le_mul_right _ hbW
    omega
  have hcE : Nat.card ↥D.sec = Nat.card D.Sec * 2 := by
    rw [card_eq_card_quotient_mul_card_subgroup (D.ker.subgroupOf D.sec), hk2]
  have hfstb : Function.Bijective fstW := hfst.bijective_of_nat_card_le hcard.le
  have hsndb : Function.Bijective sndW := hsnd.bijective_of_nat_card_le (by omega)
  let eV := MulEquiv.ofBijective fstW hfstb
  let eE := MulEquiv.ofBijective sndW hsndb
  refine ⟨eV.symm.trans eE, fun γ v => ?_⟩
  obtain ⟨w, rfl⟩ := hfstb.2 v
  have h1 : eV.symm (fstW w) = w := eV.symm_apply_apply w
  have h2 : C.ρ γ (fstW w) = fstW (ρW γ w) := rfl
  have h3 : eV.symm (fstW (ρW γ w)) = ρW γ w := eV.symm_apply_apply (ρW γ w)
  show eE (eV.symm (C.ρ γ (fstW w))) = αE γ (eE (eV.symm (fstW w)))
  rw [h2, h3, h1]
  rfl

end ModelCover

theorem realizes_of_mulEquiv {E : FFModel} (hE : E.ker = ⊥) {V : Type*} [CommGroup V]
    {H : Subgroup (MulAut V)} (π : E.Gam →* ↥H) (hπs : Function.Surjective π)
    (Φ : V ≃* ↥E.sec) (hΦ : ∀ γ v, (Φ ((π γ : MulAut V) v) : E.Amb) = E.act γ (Φ v)) :
    E.Realizes H ⊤ ⊥ := by
  have hsec : ∀ γ, ∀ m ∈ E.sec, E.act γ m ∈ E.sec := fun γ m hm => by
    obtain ⟨v, hv⟩ := Φ.surjective ⟨m, hm⟩
    rw [← show (Φ v : E.Amb) = m from congrArg Subtype.val hv, ← hΦ]
    exact (Φ _).2
  have hact1 : ∀ γ, E.act γ 1 = 1 := fun γ => by
    have h := hΦ γ 1
    simp only [map_one, OneMemClass.coe_one] at h
    exact h.symm
  have hkeq : ∀ x : ↥E.sec, x ∈ E.ker.subgroupOf E.sec ↔ x = 1 := fun x => by
    rw [mem_subgroupOf, hE, mem_bot]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  let β : ↥(⊤ : Subgroup V) →* ↥E.sec ⧸ E.ker.subgroupOf E.sec :=
    (QuotientGroup.mk' _).comp (Φ.toMonoidHom.comp (⊤ : Subgroup V).subtype)
  refine ⟨π, hπs, bot_le, by rw [hE]; exact bot_le, fun _ _ _ => mem_top _,
    fun h z hz => by rw [mem_bot] at hz ⊢; rw [hz, map_one], hsec,
    fun γ m hm => by rw [hE, mem_bot] at hm ⊢; rw [hm, hact1], β, fun q => ?_,
    fun u => ?_, fun γ u m hu hm hum => ?_⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨v, rfl⟩ := Φ.surjective x
    exact ⟨⟨v, mem_top v⟩, rfl⟩
  · show (QuotientGroup.mk (Φ u) : ↥E.sec ⧸ E.ker.subgroupOf E.sec) = 1 ↔ (u : V) ∈ ⊥
    rw [QuotientGroup.eq_one_iff, hkeq, mem_bot, MulEquiv.map_eq_one_iff]
  · have h1 : Φ u = m := by
      have h := (QuotientGroup.eq (s := E.ker.subgroupOf E.sec) (a := Φ u) (b := m)).1 hum
      rw [hkeq, inv_mul_eq_one] at h
      exact h
    show (QuotientGroup.mk (Φ ((π γ : MulAut V) u)) : ↥E.sec ⧸ E.ker.subgroupOf E.sec) =
      QuotientGroup.mk ⟨E.act γ m, hm⟩
    congr 1
    apply Subtype.ext
    rw [hΦ, h1]

end CFSG.Quasithin.H13.VolI
