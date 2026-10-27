module

public import CFSG.Quasithin.H13.VolIAltCoverSixData
public import CFSG.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.G6 Subgroup Equiv

structure Cover6 (V : Type*) [CommGroup V] where
  H : Subgroup (MulAut V)
  Z : Subgroup V
  ρ : ↥(alternatingGroup (Fin 6)) →* MulAut V
  β : V →* DnQuot 6
  hV2 : ∀ v : V, v ^ 2 = 1
  hZ : Z ≤ fixV H
  hcomm : commV H = ⊤
  hρ : ∀ σ, ρ σ ∈ H
  hρs : ∀ h ∈ H, ∃ σ, ρ σ = h
  hβs : Function.Surjective β
  hβk : ∀ v, β v = 1 ↔ v ∈ Z
  hβe : ∀ σ (v : V) (m : ↥(coreMod 6)), β v = QuotientGroup.mk m →
    β (ρ σ v) = QuotientGroup.mk (coreAct 6 (σ : Perm (Fin 6)) m)

namespace Cover6

variable {V : Type*} [CommGroup V] (C : Cover6 V)

theorem ρ_fix {z : V} (hz : z ∈ C.Z) (σ : ↥(alternatingGroup (Fin 6))) : C.ρ σ z = z :=
  C.hZ hz _ (C.hρ σ)

theorem ρ_mul_apply (σ τ : ↥(alternatingGroup (Fin 6))) (v : V) :
    C.ρ (σ * τ) v = C.ρ σ (C.ρ τ v) := by
  rw [map_mul, MulAut.mul_apply]

theorem ρ_s_s (v : V) : C.ρ a6s (C.ρ a6s v) = v := by
  rw [← C.ρ_mul_apply, a6s_mul_self, map_one, MulAut.one_apply]

theorem β_act {σ : ↥(alternatingGroup (Fin 6))} {v : V} {m : ↥(coreMod 6)}
    (h : C.β v = QuotientGroup.mk m) : C.β (C.ρ σ v) = QuotientGroup.mk (act6 σ m) :=
  C.hβe σ v m h

theorem β_comm (σ : ↥(alternatingGroup (Fin 6))) {v : V} {m : ↥(coreMod 6)}
    (h : C.β v = QuotientGroup.mk m) :
    C.β (C.ρ σ v * v⁻¹) = QuotientGroup.mk (act6 σ m * m⁻¹) := by
  rw [map_mul, map_inv, C.β_act h, h, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem β_comm2 (σ τ : ↥(alternatingGroup (Fin 6))) {a b : PermMod 6} (ha : a ∈ coreMod 6)
    (hb : b ∈ coreMod 6) {v w : V} (hv : C.β v = QuotientGroup.mk ⟨a, ha⟩)
    (hw : C.β w = QuotientGroup.mk ⟨b, hb⟩) :
    C.β (C.ρ σ v * v⁻¹ * (C.ρ τ w * w⁻¹)) =
      QuotientGroup.mk ⟨comm2 σ τ a b, comm2_mem σ τ ha hb⟩ := by
  rw [map_mul, C.β_comm σ hv, C.β_comm τ hw, ← QuotientGroup.mk_mul]
  rfl

@[expose] def Y : Subgroup V := (commMap (C.ρ a6c012)).range ⊔ (commMap (C.ρ a6c234)).range

theorem comm_mem_Y {σ : ↥(alternatingGroup (Fin 6))} (hσ : (σ : Perm (Fin 6)) 5 = 5) (v : V) :
    C.ρ σ v * v⁻¹ ∈ C.Y :=
  comm_mem_sup_of_isWord6 ((alt6_words σ hσ).map C.ρ) v

theorem mem_Y {σ : ↥(alternatingGroup (Fin 6))} (hσ : (σ : Perm (Fin 6)) 5 = 5) {y : V}
    (hy : y ∈ C.Y) : C.ρ σ y ∈ C.Y := by
  have h := mul_mem (C.comm_mem_Y hσ y) hy
  rwa [inv_mul_cancel_right] at h

theorem card_Y_le [Finite V] : Nat.card C.Y ≤ 16 := by
  have h₁ : Nat.card (commMap (C.ρ a6c012)).range ≤ 4 := by
    have h := card_commMap_range_le (t := C.ρ a6c012) (γ := (a6c012 : Perm (Fin 6))) C.hV2
      C.hβk (by rw [← map_pow, a6c012_pow, map_one]) (fun z hz => C.ρ_fix hz a6c012)
      (C.hβe a6c012) (evenOn 0 1 2) comm_mem_evenOn_six_012
    rwa [evenOn_six_012_card] at h
  have h₂ : Nat.card (commMap (C.ρ a6c234)).range ≤ 4 := by
    have h := card_commMap_range_le (t := C.ρ a6c234) (γ := (a6c234 : Perm (Fin 6))) C.hV2
      C.hβk (by rw [← map_pow, a6c234_pow, map_one]) (fun z hz => C.ρ_fix hz a6c234)
      (C.hβe a6c234) (evenOn 2 3 4) comm_mem_evenOn_six_234
    rwa [evenOn_six_234_card] at h
  have hN : (commMap (C.ρ a6c012)).range ≤
      normalizer ((commMap (C.ρ a6c234)).range : Set V) := by
    rw [normalizer_eq_top]
    exact le_top
  have h64 := card_sup_mul_card_inf hN
  have hpos : 0 < Nat.card ↥((commMap (C.ρ a6c012)).range ⊓ (commMap (C.ρ a6c234)).range) :=
    Nat.card_pos
  calc Nat.card C.Y ≤ Nat.card (commMap (C.ρ a6c012)).range *
        Nat.card (commMap (C.ρ a6c234)).range := by
        rw [← h64]
        exact Nat.le_mul_of_pos_right _ hpos
    _ ≤ 4 * 4 := Nat.mul_le_mul h₁ h₂

theorem exists_mem_Y (q : DnQuot 6) : ∃ y ∈ C.Y, C.β y = q := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, ha, b, hb, hm⟩ := coreMod_six_eq m m.2
  obtain ⟨v, hv⟩ := C.hβs (QuotientGroup.mk ⟨a, lifts012_mem a ha⟩)
  obtain ⟨w, hw⟩ := C.hβs (QuotientGroup.mk ⟨b, lifts234_mem b hb⟩)
  refine ⟨C.ρ a6c012 v * v⁻¹ * (C.ρ a6c234 w * w⁻¹),
    mul_mem (mem_sup_left ⟨v, rfl⟩) (mem_sup_right ⟨w, rfl⟩), ?_⟩
  rw [C.β_comm2 a6c012 a6c234 _ _ hv hw]
  exact mk_eq_mk_iff_six.2 hm

theorem bijective_Y [Finite V] : Function.Bijective (C.β.comp C.Y.subtype) := by
  refine Function.Surjective.bijective_of_nat_card_le (fun q => ?_)
    (C.card_Y_le.trans card_dnQuot_six.symm.le)
  obtain ⟨y, hy, rfl⟩ := C.exists_mem_Y q
  exact ⟨⟨y, hy⟩, rfl⟩

theorem inj_Y [Finite V] {y y' : V} (hy : y ∈ C.Y) (hy' : y' ∈ C.Y) (h : C.β y = C.β y') :
    y = y' :=
  congrArg Subtype.val (C.bijective_Y.1 (a₁ := ⟨y, hy⟩) (a₂ := ⟨y', hy'⟩) h)

theorem card_Y [Finite V] : Nat.card C.Y = 16 := by
  rw [Nat.card_congr (Equiv.ofBijective _ C.bijective_Y), card_dnQuot_six]

theorem inf_Z [Finite V] : C.Y ⊓ C.Z = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hy1, hy2⟩ := mem_inf.1 hy
  exact mem_bot.2 (C.inj_Y hy1 (one_mem _) (by rw [(C.hβk y).2 hy2, map_one]))

theorem exists_mul [Finite V] (v : V) : ∃ y ∈ C.Y, ∃ z ∈ C.Z, v = y * z := by
  obtain ⟨y, hy, hβ⟩ := C.exists_mem_Y (C.β v)
  exact ⟨y, hy, y⁻¹ * v, (C.hβk _).1 (by rw [map_mul, map_inv, hβ, inv_mul_cancel]),
    (mul_inv_cancel_left y v).symm⟩

theorem sup_Z [Finite V] : C.Y ⊔ C.Z = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨y, hy, z, hz, rfl⟩ := C.exists_mul v
  exact mul_mem (mem_sup_left hy) (mem_sup_right hz)

theorem card_eq [Finite V] : Nat.card V = 16 * Nat.card C.Z := by
  have hN : C.Y ≤ normalizer (C.Z : Set V) := by
    rw [normalizer_eq_top]
    exact le_top
  have h := card_sup_mul_card_inf hN
  rw [C.sup_Z, C.inf_Z, card_top, card_bot, mul_one, C.card_Y] at h
  exact h

@[expose] def sY : Subgroup V := C.Y.map (C.ρ a6s).toMonoidHom

theorem s_mem_sY {y : V} (hy : y ∈ C.Y) : C.ρ a6s y ∈ C.sY := mem_map_of_mem _ hy

theorem comm_mem_sY {κ : ↥(alternatingGroup (Fin 6))}
    (hκ : ((a6s * κ * a6s : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) 5 = 5) (v : V) :
    C.ρ κ v * v⁻¹ ∈ C.sY := by
  refine mem_map.2 ⟨C.ρ (a6s * κ * a6s) (C.ρ a6s v) * (C.ρ a6s v)⁻¹, C.comm_mem_Y hκ _, ?_⟩
  show C.ρ a6s (C.ρ (a6s * κ * a6s) (C.ρ a6s v) * (C.ρ a6s v)⁻¹) = C.ρ κ v * v⁻¹
  simp only [map_mul, map_inv, MulAut.mul_apply, C.ρ_s_s]

@[expose] def W : Subgroup V := C.Y ⊔ C.sY

theorem mem_W_iff {w : V} : w ∈ C.W ↔ ∃ y ∈ C.Y, ∃ y' ∈ C.Y, y * C.ρ a6s y' = w := by
  show w ∈ C.Y ⊔ C.sY ↔ _
  rw [mem_sup]
  constructor
  · rintro ⟨y, hy, x, hx, rfl⟩
    obtain ⟨y', hy', rfl⟩ := mem_map.1 hx
    exact ⟨y, hy, y', hy', rfl⟩
  · rintro ⟨y, hy, y', hy', rfl⟩
    exact ⟨y, hy, _, C.s_mem_sY hy', rfl⟩

theorem mem_W_of {g : MulAut V} (h1 : ∀ y ∈ C.Y, g y ∈ C.W)
    (h2 : ∀ y ∈ C.Y, g (C.ρ a6s y) ∈ C.W) {w : V} (hw : w ∈ C.W) : g w ∈ C.W := by
  obtain ⟨y, hy, y', hy', rfl⟩ := C.mem_W_iff.1 hw
  rw [map_mul]
  exact mul_mem (h1 y hy) (h2 y' hy')

theorem Y_le_W : C.Y ≤ C.W := le_sup_left

theorem sY_le_W : C.sY ≤ C.W := le_sup_right

theorem mem_W_of_five [Finite V] {σ : ↥(alternatingGroup (Fin 6))}
    (hσ : (σ : Perm (Fin 6)) 5 = 5) {w : V} (hw : w ∈ C.W) : C.ρ σ w ∈ C.W := by
  refine C.mem_W_of (fun y hy => C.Y_le_W (C.mem_Y hσ hy)) (fun y hy => ?_) hw
  obtain ⟨y₁, hy₁, z, hz, he⟩ := C.exists_mul (C.ρ a6s y)
  have hz' : z = y₁⁻¹ * C.ρ a6s y := by rw [he, inv_mul_cancel_left]
  rw [he, map_mul, C.ρ_fix hz, hz']
  exact mul_mem (C.Y_le_W (C.mem_Y hσ hy₁))
    (mul_mem (inv_mem (C.Y_le_W hy₁)) (C.sY_le_W (C.s_mem_sY hy)))

theorem mem_W_s {w : V} (hw : w ∈ C.W) : C.ρ a6s w ∈ C.W :=
  C.mem_W_of (fun y hy => C.sY_le_W (C.s_mem_sY hy))
    (fun y hy => by rw [C.ρ_s_s]; exact C.Y_le_W hy) hw

theorem mem_W [Finite V] (σ : ↥(alternatingGroup (Fin 6))) {w : V} (hw : w ∈ C.W) :
    C.ρ σ w ∈ C.W := by
  rcases alt6_cosets σ with h5 | ⟨h, -, hh, hk⟩
  · exact C.mem_W_of_five h5 hw
  · obtain ⟨k, hk', rfl⟩ : ∃ k : ↥(alternatingGroup (Fin 6)), (k : Perm (Fin 6)) 5 = 5 ∧
        σ = h * a6s * k := ⟨_, hk, by group⟩
    rw [C.ρ_mul_apply, C.ρ_mul_apply]
    exact C.mem_W_of_five hh (C.mem_W_s (C.mem_W_of_five hk' hw))

theorem W_eq_top [Finite V] : C.W = ⊤ := by
  rw [eq_top_iff, ← C.hcomm]
  refine (closure_le _).2 ?_
  rintro _ ⟨x, hx, v, rfl⟩
  obtain ⟨σ, rfl⟩ := C.hρs x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := C.exists_mul v
  have e : C.ρ σ (y * z) * (y * z)⁻¹ = C.ρ σ y * y⁻¹ := by
    rw [map_mul, C.ρ_fix hz]
    group
  rw [e]
  exact mul_mem (C.mem_W σ (C.Y_le_W hy)) (inv_mem (C.Y_le_W hy))

theorem card_inf_ge [Finite V] : 8 ≤ Nat.card ↥(C.Y ⊓ C.sY) := by
  have hmem : ∀ x (hx : x ∈ evenP), ∃ u ∈ C.Y ⊓ C.sY,
      C.β u = QuotientGroup.mk ⟨x, mem_coreMod_of_mem_evenP hx⟩ := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := evenP_eq x hx
    obtain ⟨v, hv⟩ := C.hβs (QuotientGroup.mk ⟨a, lifts123_mem a ha⟩)
    obtain ⟨w, hw⟩ := C.hβs (QuotientGroup.mk ⟨b, lifts234_mem b hb⟩)
    exact ⟨_, mem_inf.2 ⟨mul_mem (C.comm_mem_Y a6c123_five v) (C.comm_mem_Y a6c234_five w),
      mul_mem (C.comm_mem_sY a6s_c123_five v) (C.comm_mem_sY a6s_c234_five w)⟩,
      C.β_comm2 a6c123 a6c234 _ _ hv hw⟩
  let f : ↥evenP → ↥((C.Y ⊓ C.sY).map C.β) := fun x =>
    ⟨QuotientGroup.mk ⟨x, mem_coreMod_of_mem_evenP x.2⟩, by
      obtain ⟨u, hu, he⟩ := hmem x x.2
      exact mem_map.2 ⟨u, hu, he⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    have h' : (QuotientGroup.mk ⟨x, mem_coreMod_of_mem_evenP hx⟩ : DnQuot 6) =
        QuotientGroup.mk ⟨y, mem_coreMod_of_mem_evenP hy⟩ := congrArg Subtype.val h
    rcases mk_eq_mk_iff_six.1 h' with h'' | h''
    · exact Subtype.ext h''.symm
    · exact absurd h''.symm (evenP_allOnes x hx y hy)
  calc 8 = Nat.card ↥evenP := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, evenP_card]
    _ ≤ Nat.card ↥((C.Y ⊓ C.sY).map C.β) := Nat.card_le_card_of_injective f hf
    _ ≤ Nat.card ↥(C.Y ⊓ C.sY) :=
        Nat.card_le_card_of_surjective _ (C.β.subgroupMap_surjective _)

include C in
theorem card_le [Finite V] : Nat.card V ≤ 32 := by
  have hN : C.Y ≤ normalizer (C.sY : Set V) := by
    rw [normalizer_eq_top]
    exact le_top
  have h := card_sup_mul_card_inf hN
  have hsY : Nat.card C.sY = 16 := by
    show Nat.card ↥(C.Y.map (C.ρ a6s).toMonoidHom) = 16
    rw [card_map_of_injective (f := (C.ρ a6s).toMonoidHom) (C.ρ a6s).injective, C.card_Y]
  have hW : C.Y ⊔ C.sY = ⊤ := C.W_eq_top
  rw [hW, card_top, C.card_Y, hsY] at h
  have h8 := C.card_inf_ge
  have : Nat.card V * 8 ≤ 16 * 16 :=
    calc Nat.card V * 8 ≤ Nat.card V * Nat.card ↥(C.Y ⊓ C.sY) := Nat.mul_le_mul_left _ h8
      _ = 16 * 16 := h
  omega

theorem card_Z_le [Finite V] : Nat.card C.Z ≤ 2 := by
  have h1 := C.card_eq
  have h2 := C.card_le
  omega

@[expose] def zpart (z : V) : ↥(coreMod 6) →* V where
  toFun x := if Multiplicative.toAdd (x : PermMod 6) 5 = 0 then 1 else z
  map_one' := ite_eq_left rfl
  map_mul' x y := by
    have hz : z * z = 1 := by rw [← pow_two]; exact C.hV2 z
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    show (if Multiplicative.toAdd (x : PermMod 6) 5 + Multiplicative.toAdd (y : PermMod 6) 5 = 0
      then (1 : V) else z) = (if Multiplicative.toAdd (x : PermMod 6) 5 = 0 then 1 else z) *
        (if Multiplicative.toAdd (y : PermMod 6) 5 = 0 then 1 else z)
    rcases zmod_two_cases (Multiplicative.toAdd (x : PermMod 6) 5) with h1 | h1 <;>
    rcases zmod_two_cases (Multiplicative.toAdd (y : PermMod 6) 5) with h2 | h2 <;>
    rw [h1, h2] <;> simp [hz, h11]

theorem zpart_of_eq_zero (z : V) {x : ↥(coreMod 6)}
    (h : Multiplicative.toAdd (x : PermMod 6) 5 = 0) : C.zpart z x = 1 := ite_eq_left h

theorem zpart_of_ne_zero (z : V) {x : ↥(coreMod 6)}
    (h : Multiplicative.toAdd (x : PermMod 6) 5 ≠ 0) : C.zpart z x = z := ite_eq_right h

theorem zpart_mem {z : V} (hz : z ∈ C.Z) (x : ↥(coreMod 6)) : C.zpart z x ∈ C.Z := by
  by_cases h : Multiplicative.toAdd (x : PermMod 6) 5 = 0
  · rw [C.zpart_of_eq_zero z h]
    exact one_mem _
  · rw [C.zpart_of_ne_zero z h]
    exact hz

variable [Finite V]

noncomputable def lam : DnQuot 6 →* V :=
  C.Y.subtype.comp (MulEquiv.ofBijective _ C.bijective_Y).symm.toMonoidHom

theorem lam_mem (q : DnQuot 6) : C.lam q ∈ C.Y :=
  ((MulEquiv.ofBijective _ C.bijective_Y).symm q).2

theorem β_lam (q : DnQuot 6) : C.β (C.lam q) = q :=
  (MulEquiv.ofBijective _ C.bijective_Y).apply_symm_apply q

theorem lam_β {y : V} (hy : y ∈ C.Y) : C.lam (C.β y) = y :=
  C.inj_Y (C.lam_mem _) hy (C.β_lam _)

theorem lam_act {σ : ↥(alternatingGroup (Fin 6))} (hσ : (σ : Perm (Fin 6)) 5 = 5)
    (m : ↥(coreMod 6)) :
    C.ρ σ (C.lam (QuotientGroup.mk m)) = C.lam (QuotientGroup.mk (act6 σ m)) :=
  C.inj_Y (C.mem_Y hσ (C.lam_mem _)) (C.lam_mem _) (by rw [C.β_act (C.β_lam _), C.β_lam])

@[expose] noncomputable def Ψ (z : V) : ↥(coreMod 6) →* V :=
  C.lam.comp (QuotientGroup.mk' _) * C.zpart z

theorem Ψ_apply (z : V) (x : ↥(coreMod 6)) :
    C.Ψ z x = C.lam (QuotientGroup.mk x) * C.zpart z x := rfl

theorem β_Ψ {z : V} (hz : z ∈ C.Z) (x : ↥(coreMod 6)) :
    C.β (C.Ψ z x) = QuotientGroup.mk x := by
  rw [Ψ_apply, map_mul, C.β_lam, (C.hβk _).2 (C.zpart_mem hz x), mul_one]

theorem Ψ_of_five (z : V) {x : ↥(coreMod 6)} (h : Multiplicative.toAdd (x : PermMod 6) 5 = 0) :
    C.Ψ z x = C.lam (QuotientGroup.mk x) := by
  rw [Ψ_apply, C.zpart_of_eq_zero z h, mul_one]

theorem Ψ_injective {z : V} (hz : z ∈ C.Z) (hz1 : z ≠ 1) : Function.Injective (C.Ψ z) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [Ψ_apply] at hx
  have hl : C.lam (QuotientGroup.mk x) ∈ C.Y ⊓ C.Z := by
    refine mem_inf.2 ⟨C.lam_mem _, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hx]
    exact inv_mem (C.zpart_mem hz x)
  rw [C.inf_Z, mem_bot] at hl
  rw [hl, one_mul] at hx
  have h5 : Multiplicative.toAdd (x : PermMod 6) 5 = 0 := by
    by_contra h
    exact hz1 ((C.zpart_of_ne_zero z h).symm.trans hx)
  have hq : (QuotientGroup.mk x : DnQuot 6) = QuotientGroup.mk 1 := by
    rw [← C.β_lam (QuotientGroup.mk x), hl, map_one, QuotientGroup.mk_one]
  rcases mk_eq_mk_iff_six.1 hq with h | h
  · exact Subtype.ext h.symm
  · exfalso
    have h' := congrArg (fun v : PermMod 6 => Multiplicative.toAdd v 5) h
    simp [h5, allOnes_six_five] at h'

theorem Ψ_bijective {z : V} (hz : z ∈ C.Z) (hz1 : z ≠ 1) : Function.Bijective (C.Ψ z) :=
  (C.Ψ_injective hz hz1).bijective_of_nat_card_le (C.card_le.trans card_coreMod_six.symm.le)

theorem Ψ_act_five {z : V} (hz : z ∈ C.Z) {σ : ↥(alternatingGroup (Fin 6))}
    (hσ : (σ : Perm (Fin 6)) 5 = 5) (x : ↥(coreMod 6)) :
    C.Ψ z (act6 σ x) = C.ρ σ (C.Ψ z x) := by
  rw [Ψ_apply, Ψ_apply, map_mul, C.lam_act hσ, C.ρ_fix (C.zpart_mem hz x)]
  congr 1
  by_cases h : Multiplicative.toAdd (x : PermMod 6) 5 = 0
  · rw [C.zpart_of_eq_zero z h, C.zpart_of_eq_zero z ((act6_five hσ x).trans h)]
  · rw [C.zpart_of_ne_zero z h,
      C.zpart_of_ne_zero z (fun h' => h ((act6_five hσ x).symm.trans h'))]

theorem Ψ_allOnes (z : V) : C.Ψ z ⟨allOnes 6, allOnes_six_mem⟩ = z := by
  rw [Ψ_apply, mk_allOnes_six, map_one, one_mul, C.zpart_of_ne_zero z (by
    show Multiplicative.toAdd (allOnes 6) 5 ≠ 0
    rw [allOnes_six_five]
    exact one_ne_zero)]

@[expose] noncomputable def Es (z : V) : Subgroup ↥(coreMod 6) :=
  ((C.Ψ z).comp (act6 a6s).toMonoidHom).eqLocus ((C.ρ a6s).toMonoidHom.comp (C.Ψ z))

theorem mem_Es {z : V} {x : ↥(coreMod 6)} :
    x ∈ C.Es z ↔ C.Ψ z (act6 a6s x) = C.ρ a6s (C.Ψ z x) := Iff.rfl

theorem comm_mem_Es {z : V} (hz : z ∈ C.Z) {κ : ↥(alternatingGroup (Fin 6))}
    (hκ : (κ : Perm (Fin 6)) 5 = 5)
    (hsκ : ((a6s * κ * a6s : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) 5 = 5)
    (a : ↥(coreMod 6)) : act6 κ a * a⁻¹ ∈ C.Es z := by
  rw [mem_Es]
  obtain ⟨e, he, hee⟩ : ∃ e ∈ C.Z, C.ρ a6s (C.Ψ z a) = C.Ψ z (act6 a6s a) * e := by
    refine ⟨(C.Ψ z (act6 a6s a))⁻¹ * C.ρ a6s (C.Ψ z a), (C.hβk _).1 ?_,
      (mul_inv_cancel_left _ _).symm⟩
    rw [map_mul, map_inv, C.β_act (C.β_Ψ hz a), C.β_Ψ hz, inv_mul_cancel]
  have hκ' : act6 a6s (act6 κ a) = act6 (a6s * κ * a6s) (act6 a6s a) := by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, mul_assoc _ a6s a6s,
      a6s_mul_self, mul_one]
  have hρκ : C.ρ a6s (C.ρ κ (C.Ψ z a)) = C.ρ (a6s * κ * a6s) (C.ρ a6s (C.Ψ z a)) := by
    simp only [map_mul, MulAut.mul_apply, C.ρ_s_s]
  have hL : C.Ψ z (act6 a6s (act6 κ a * a⁻¹)) =
      C.ρ (a6s * κ * a6s) (C.Ψ z (act6 a6s a)) * (C.Ψ z (act6 a6s a))⁻¹ := by
    conv_lhs => rw [map_mul, map_inv, map_mul, map_inv, hκ', C.Ψ_act_five hz hsκ]
  have hR : C.ρ a6s (C.Ψ z (act6 κ a * a⁻¹)) =
      C.ρ (a6s * κ * a6s) (C.Ψ z (act6 a6s a) * e) * (C.Ψ z (act6 a6s a) * e)⁻¹ := by
    conv_lhs => rw [map_mul, map_inv, map_mul, map_inv, C.Ψ_act_five hz hκ, hρκ, hee]
  rw [hL, hR, map_mul (C.ρ (a6s * κ * a6s)), C.ρ_fix he]
  group

theorem mem_Es_of_evenP {z : V} (hz : z ∈ C.Z) {p : ↥(coreMod 6)}
    (hp : (p : PermMod 6) ∈ evenP) : p ∈ C.Es z := by
  obtain ⟨a, ha, b, hb, hpe⟩ := evenP_eq _ hp
  have e : p = act6 a6c123 ⟨a, lifts123_mem a ha⟩ * ⟨a, lifts123_mem a ha⟩⁻¹ *
      (act6 a6c234 ⟨b, lifts234_mem b hb⟩ * ⟨b, lifts234_mem b hb⟩⁻¹) := Subtype.ext hpe
  rw [e]
  exact mul_mem (C.comm_mem_Es hz a6c123_five a6s_c123_five _)
    (C.comm_mem_Es hz a6c234_five a6s_c234_five _)

theorem mem_Es_e01 {z : V} (hz : z ∈ C.Z) (hz1 : z ≠ 1) (hzu : ∀ w ∈ C.Z, w ≠ 1 → w = z) :
    (⟨ev2 0 1, ev2_01_mem⟩ : ↥(coreMod 6)) ∈ C.Es z := by
  set x01 : ↥(coreMod 6) := ⟨ev2 0 1, ev2_01_mem⟩ with hx01
  obtain ⟨e, he, hee⟩ : ∃ e ∈ C.Z, C.ρ a6s (C.Ψ z x01) = C.Ψ z (act6 a6s x01) * e := by
    refine ⟨(C.Ψ z (act6 a6s x01))⁻¹ * C.ρ a6s (C.Ψ z x01), (C.hβk _).1 ?_,
      (mul_inv_cancel_left _ _).symm⟩
    rw [map_mul, map_inv, C.β_act (C.β_Ψ hz x01), C.β_Ψ hz, inv_mul_cancel]
  rw [mem_Es, hee]
  suffices h : e = 1 by rw [h, mul_one]
  by_contra hne
  have hez : e = z := hzu e he hne
  have hz2 : z * z = 1 := by rw [← pow_two]; exact C.hV2 z
  have hxx : x01 * x01 = 1 := Subtype.ext ev2_01_mul_self
  have hsY : ∀ y ∈ C.Y, C.ρ a6s y ∈ C.Y := by
    intro y hy
    obtain ⟨m, hm5, hm⟩ : ∃ m : ↥(coreMod 6), Multiplicative.toAdd (m : PermMod 6) 5 = 0 ∧
        (QuotientGroup.mk m : DnQuot 6) = C.β y := by
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (C.β y)
      rcases zmod_two_cases (Multiplicative.toAdd (m : PermMod 6) 5) with h | h
      · exact ⟨m, h, hm⟩
      · refine ⟨m * ⟨allOnes 6, allOnes_six_mem⟩, ?_, ?_⟩
        · show Multiplicative.toAdd (m : PermMod 6) 5 + Multiplicative.toAdd (allOnes 6) 5 = 0
          rw [h, allOnes_six_five]
          decide
        · rw [QuotientGroup.mk_mul, mk_allOnes_six, mul_one, hm]
    have hyΨ : y = C.Ψ z m := by rw [C.Ψ_of_five z hm5, hm, C.lam_β hy]
    rcases coreMod_six_five m m.2 hm5 with ⟨h0, hP⟩ | ⟨h1, hP⟩
    · have hE := C.mem_Es.1 (C.mem_Es_of_evenP hz hP)
      rw [hyΨ, ← hE, C.Ψ_of_five z (by rw [act6_s_five, h0])]
      exact C.lam_mem _
    · have hE := C.mem_Es.1 (C.mem_Es_of_evenP hz (p := m * x01) hP)
      have hm' : m = m * x01 * x01 := by rw [mul_assoc, hxx, mul_one]
      have h5 : Multiplicative.toAdd (act6 a6s m : PermMod 6) 5 ≠ 0 := by
        rw [act6_s_five, h1]
        exact one_ne_zero
      have hcalc : C.ρ a6s y = C.lam (QuotientGroup.mk (act6 a6s m)) :=
        calc C.ρ a6s y = C.ρ a6s (C.Ψ z (m * x01 * x01)) := by rw [← hm', hyΨ]
          _ = C.ρ a6s (C.Ψ z (m * x01)) * C.ρ a6s (C.Ψ z x01) := by
              rw [map_mul (C.Ψ z) (m * x01) x01, map_mul (C.ρ a6s)]
          _ = C.Ψ z (act6 a6s (m * x01)) * (C.Ψ z (act6 a6s x01) * e) := by rw [← hE, hee]
          _ = C.Ψ z (act6 a6s (m * x01 * x01)) * e := by
              rw [map_mul (act6 a6s) (m * x01) x01, map_mul (C.Ψ z), mul_assoc]
          _ = C.Ψ z (act6 a6s m) * e := by rw [← hm']
          _ = C.lam (QuotientGroup.mk (act6 a6s m)) * (z * z) := by
              rw [Ψ_apply, C.zpart_of_ne_zero z h5, hez, mul_assoc]
          _ = C.lam (QuotientGroup.mk (act6 a6s m)) := by rw [hz2, mul_one]
      rw [hcalc]
      exact C.lam_mem _
  have hW : C.W ≤ C.Y := sup_le le_rfl (map_le_iff_le_comap.2 fun y hy => hsY y hy)
  have hY : C.Y = ⊤ := top_le_iff.1 (by rw [← C.W_eq_top]; exact hW)
  have hzY : z ∈ C.Y ⊓ C.Z := mem_inf.2 ⟨by rw [hY]; exact mem_top z, hz⟩
  rw [C.inf_Z, mem_bot] at hzY
  exact hz1 hzY

theorem Es_eq_top {z : V} (hz : z ∈ C.Z) (hz1 : z ≠ 1) (hzu : ∀ w ∈ C.Z, w ≠ 1 → w = z) :
    C.Es z = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨p, hp, hx⟩ := coreMod_six_decomp x x.2
  have hpE : (⟨p, mem_coreMod_of_mem_evenP hp⟩ : ↥(coreMod 6)) ∈ C.Es z :=
    C.mem_Es_of_evenP hz hp
  have h1E : (⟨allOnes 6, allOnes_six_mem⟩ : ↥(coreMod 6)) ∈ C.Es z := by
    rw [mem_Es, act6_allOnes, C.Ψ_allOnes, C.ρ_fix hz]
  have heE := C.mem_Es_e01 hz hz1 hzu
  rcases hx with hx | hx | hx | hx
  · obtain rfl : x = ⟨p, mem_coreMod_of_mem_evenP hp⟩ := Subtype.ext hx
    exact hpE
  · obtain rfl : x = ⟨p, mem_coreMod_of_mem_evenP hp⟩ * ⟨allOnes 6, allOnes_six_mem⟩ :=
      Subtype.ext hx
    exact mul_mem hpE h1E
  · obtain rfl : x = ⟨p, mem_coreMod_of_mem_evenP hp⟩ * ⟨ev2 0 1, ev2_01_mem⟩ :=
      Subtype.ext hx
    exact mul_mem hpE heE
  · obtain rfl : x = ⟨p, mem_coreMod_of_mem_evenP hp⟩ * ⟨allOnes 6, allOnes_six_mem⟩ *
        ⟨ev2 0 1, ev2_01_mem⟩ := Subtype.ext hx
    exact mul_mem (mul_mem hpE h1E) heE

theorem Ψ_act {z : V} (hz : z ∈ C.Z) (hz1 : z ≠ 1) (hzu : ∀ w ∈ C.Z, w ≠ 1 → w = z)
    (σ : ↥(alternatingGroup (Fin 6))) (x : ↥(coreMod 6)) :
    C.Ψ z (act6 σ x) = C.ρ σ (C.Ψ z x) := by
  have hs : ∀ y, C.Ψ z (act6 a6s y) = C.ρ a6s (C.Ψ z y) := fun y =>
    C.mem_Es.1 (by rw [C.Es_eq_top hz hz1 hzu]; exact mem_top y)
  rcases alt6_cosets σ with h5 | ⟨h, -, hh, hk⟩
  · exact C.Ψ_act_five hz h5 x
  · obtain ⟨k, hk', rfl⟩ : ∃ k : ↥(alternatingGroup (Fin 6)), (k : Perm (Fin 6)) 5 = 5 ∧
        σ = h * a6s * k := ⟨_, hk, by group⟩
    rw [map_mul act6 (h * a6s) k, map_mul act6 h a6s, MulAut.mul_apply, MulAut.mul_apply,
      C.Ψ_act_five hz hh, hs, C.Ψ_act_five hz hk', C.ρ_mul_apply, C.ρ_mul_apply]

theorem exists_mulEquiv (h2 : Nat.card C.Z = 2) :
    ∃ Ψ : ↥(coreMod 6) ≃* V, ∀ σ x, Ψ (act6 σ x) = C.ρ σ (Ψ x) := by
  obtain ⟨a, ha, hu⟩ := (Nat.card_eq_two_iff' (1 : ↥C.Z)).1 h2
  have ha1 : (a : V) ≠ 1 := fun h => ha (Subtype.ext h)
  have hzu : ∀ w ∈ C.Z, w ≠ 1 → w = a := fun w hw hw1 =>
    congrArg Subtype.val (hu ⟨w, hw⟩ (fun h => hw1 (congrArg Subtype.val h)))
  exact ⟨MulEquiv.ofBijective (C.Ψ a) (C.Ψ_bijective a.2 ha1), C.Ψ_act a.2 ha1 hzu⟩

end Cover6

theorem altNaturalCoverSix_holds :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (H : Subgroup (MulAut V)) (Z : Subgroup V), Z ≤ fixV H → commV H = ⊤ →
        AlternatingNatural H ⊤ Z 6 →
          Z = ⊥ ∨ (Nat.card Z = 2 ∧ Nat.card V = 2 ^ 5 ∧
            FFModel.Realizes (altCoreModel 6) H ⊤ ⊥) := by
  intro V _ _ hV2 H Z hZ hcomm hnat
  obtain ⟨π₀, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hnat
  let π : ↥(alternatingGroup (Fin 6)) →* ↥H := π₀
  let C : Cover6 V :=
    { H := H
      Z := Z
      ρ := H.subtype.comp π
      β :=
        { toFun := fun v => β ⟨v, mem_top v⟩
          map_one' := map_one β
          map_mul' := fun x y => map_mul β ⟨x, mem_top x⟩ ⟨y, mem_top y⟩ }
      hV2 := hV2
      hZ := hZ
      hcomm := hcomm
      hρ := fun σ => (π σ).2
      hρs := fun h hh => by
        obtain ⟨σ, hσ⟩ := hπs ⟨h, hh⟩
        exact ⟨σ, congrArg Subtype.val hσ⟩
      hβs := fun q => by
        obtain ⟨⟨v, hv1⟩, hv⟩ := hβs q
        exact ⟨v, hv⟩
      hβk := fun v => hβk ⟨v, mem_top v⟩
      hβe := fun σ v m h =>
        hβe σ ⟨v, mem_top v⟩ m (mem_top _) (permAct_mem_coreMod _ m.2) h }
  have hle : Nat.card Z ≤ 2 := C.card_Z_le
  have hpos : 0 < Nat.card Z := Nat.card_pos
  rcases (show Nat.card Z = 1 ∨ Nat.card Z = 2 by omega) with h1 | h2
  · exact Or.inl (eq_bot_of_card_eq Z h1)
  right
  have hV : Nat.card V = 16 * Nat.card Z := C.card_eq
  refine ⟨h2, by rw [hV, h2]; norm_num, ?_⟩
  obtain ⟨Ψ, hΨ⟩ := C.exists_mulEquiv h2
  let N : Subgroup ↥(coreMod 6) := (⊥ : Subgroup (PermMod 6)).subgroupOf (coreMod 6)
  refine ⟨π, hπs, bot_le, bot_le, fun _ _ _ => mem_top _, fun h z hz => ?_,
    fun γ m hm => by exact permAct_mem_coreMod _ hm, fun γ m hm => ?_,
    (QuotientGroup.mk' N).comp (Ψ.symm.toMonoidHom.comp (⊤ : Subgroup V).subtype), ?_, ?_, ?_⟩
  · rw [mem_bot] at hz ⊢
    rw [hz, map_one]
  · have hm' : m = 1 := mem_bot.1 hm
    refine mem_bot.2 ?_
    rw [hm']
    exact map_one _
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨Ψ m, mem_top _⟩, ?_⟩
    show (QuotientGroup.mk (Ψ.symm (Ψ m)) : ↥(coreMod 6) ⧸ N) = QuotientGroup.mk m
    exact congrArg _ (Ψ.symm_apply_apply m)
  · intro u
    change (QuotientGroup.mk (Ψ.symm (u : V)) : ↥(coreMod 6) ⧸ N) = 1 ↔
      (u : V) ∈ (⊥ : Subgroup V)
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf, mem_bot, mem_bot, OneMemClass.coe_eq_one,
      MulEquiv.map_eq_one_iff]
  · intro γ u m hu hm h
    have h' : Ψ.symm (u : V) = m := by
      have h1 := (QuotientGroup.eq (s := (⊥ : Subgroup (PermMod 6)).subgroupOf (coreMod 6))
        (a := Ψ.symm (u : V)) (b := m)).1 h
      rw [mem_subgroupOf, mem_bot, OneMemClass.coe_eq_one] at h1
      exact inv_mul_eq_one.1 h1
    have hu' : (u : V) = Ψ m := by rw [← h', MulEquiv.apply_symm_apply]
    have hEq : Ψ.symm ((π γ : MulAut V) (u : V)) = act6 γ m := by
      rw [MulEquiv.symm_apply_eq, hu']
      exact (hΨ γ m).symm
    exact congrArg (QuotientGroup.mk' N) hEq

end CFSG.Quasithin.H13.VolI
