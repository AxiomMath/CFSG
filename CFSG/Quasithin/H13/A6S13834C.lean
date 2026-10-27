module

public import CFSG.Quasithin.H13.A6S13834F
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.H13.A6S1357

public section

namespace CFSG.Quasithin.H13.A6

open Equiv

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

abbrev onesV : Fin 6 → ZMod 2 := fun _ => 1

theorem constWeight_iff : ∀ v : Fin 6 → ZMod 2, (∀ i j, v i = v j) ↔ v = 0 ∨ v = onesV := by
  decide +kernel

theorem sum_ones : ∑ i : Fin 6, onesV i = 0 := by
  decide +kernel

theorem zmod2_neg_add : ∀ c d : ZMod 2, -c + d = c + d := by
  decide

theorem mk_eq_mk_iff (x y : ↥(evenWeight 6)) :
    (QuotientAddGroup.mk x : AltHeart 6) = QuotientAddGroup.mk y ↔
      (x : Fin 6 → ZMod 2) = y ∨ (x : Fin 6 → ZMod 2) = y + onesV := by
  rw [QuotientAddGroup.eq]
  change (∀ i j, ((-x + y : ↥(evenWeight 6)) : Fin 6 → ZMod 2) i =
    ((-x + y : ↥(evenWeight 6)) : Fin 6 → ZMod 2) j) ↔ _
  rw [constWeight_iff]
  have e : ((-x + y : ↥(evenWeight 6)) : Fin 6 → ZMod 2) =
      (x : Fin 6 → ZMod 2) + (y : Fin 6 → ZMod 2) := by
    funext i
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply]
    exact zmod2_neg_add _ _
  rw [e]
  constructor
  · rintro (h | h)
    · left
      have := congrArg (· + (y : Fin 6 → ZMod 2)) h
      simpa [add_assoc, vadd_self] using this
    · right
      have := congrArg (· + (y : Fin 6 → ZMod 2)) h
      simp only [add_assoc, vadd_self, add_zero] at this
      rw [this, add_comm]
  · rintro (h | h)
    · left
      rw [h, vadd_self]
    · right
      rw [h, add_right_comm, vadd_self, zero_add]

theorem mk_eq_zero_iff (x : ↥(evenWeight 6)) :
    (QuotientAddGroup.mk x : AltHeart 6) = 0 ↔
      (x : Fin 6 → ZMod 2) = 0 ∨ (x : Fin 6 → ZMod 2) = onesV := by
  have := mk_eq_mk_iff x 0
  rw [QuotientAddGroup.mk_zero] at this
  rw [this]
  simp only [AddSubgroup.coe_zero, zero_add]

theorem inLn_ones (a b : Fin 6 → ZMod 2) : InLn a b onesV :=
  Or.inr (Or.inl (vadd_self _))

theorem inL_maps {a b c d : Fin 6 → ZMod 2} {f : (Fin 6 → ZMod 2) → Fin 6 → ZMod 2}
    (hf : ∀ v w, f (v + w) = f v + f w) (ha : InL c d (f a)) (hb : InL c d (f b))
    {v : Fin 6 → ZMod 2} (hv : InL a b v) : InL c d (f v) := by
  have h0 : f 0 = 0 := by
    have h := hf 0 0
    rw [add_zero, vadd_self] at h
    exact h
  rcases hv with hv | hv | hv | hv <;> rw [hv]
  · rw [h0]; exact Or.inl rfl
  · exact ha
  · exact hb
  · rw [hf]; exact inL_add ha hb

theorem inLn_maps {a b c d : Fin 6 → ZMod 2} {f : (Fin 6 → ZMod 2) → Fin 6 → ZMod 2}
    (hf : ∀ v w, f (v + w) = f v + f w) (h1 : f onesV = onesV) (ha : InLn c d (f a))
    (hb : InLn c d (f b)) {v : Fin 6 → ZMod 2} (hv : InLn a b v) : InLn c d (f v) := by
  have h0 : f 0 = 0 := by
    have h := hf 0 0
    rw [add_zero, vadd_self] at h
    exact h
  have key : ∀ w, InL a b w → InLn c d (f w) := by
    intro w hw
    rcases hw with hw | hw | hw | hw <;> rw [hw]
    · rw [h0]; exact Or.inl (Or.inl rfl)
    · exact ha
    · exact hb
    · rw [hf]; exact inLn_add ha hb
  rcases hv with hv | hv
  · exact key v hv
  · have h2 := key _ hv
    rw [hf, h1] at h2
    have := inLn_add h2 (inLn_ones c d)
    rwa [add_assoc, vadd_self, add_zero] at this

theorem dv_facts : InW4 (dv 0 1) ∧ InW4 (dv 0 2) ∧ InW3 (dv 0 1) ∧ InW3 (dv 0 2) ∧
    InW2 (dv 0 1) ∧ dv 0 1 ≠ 1 ∧ dv 0 1 ≠ e0123 ∧ dv 0 2 ≠ 1 ∧ dv 0 2 ≠ e0123 ∧
    dv 0 2 * (dv 0 1)⁻¹ ≠ 1 ∧ dv 0 2 * (dv 0 1)⁻¹ ≠ e0123 ∧ dv 0 1 * dv 0 2 ≠ 1 ∧
    dv 0 1 * dv 0 2 ≠ e0123 ∧ dv 0 1 * dv 0 2 * (dv 0 1)⁻¹ ≠ 1 ∧
    dv 0 1 * dv 0 2 * (dv 0 1)⁻¹ ≠ e0123 := by
  decide +kernel

@[expose] def W3Case (y : P6) : Prop :=
  (y = 1 ∨ y = e0123) ∨ (y * (dv 0 1)⁻¹ = 1 ∨ y * (dv 0 1)⁻¹ = e0123) ∨
    (y * (dv 0 2)⁻¹ = 1 ∨ y * (dv 0 2)⁻¹ = e0123) ∨
    (y * (dv 0 1 * dv 0 2)⁻¹ = 1 ∨ y * (dv 0 1 * dv 0 2)⁻¹ = e0123)

instance : DecidablePred W3Case := fun y => by unfold W3Case; infer_instance

theorem w3_cases : ∀ y : P6, InW4 y → InW3 y → W3Case y := by
  decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

@[expose] noncomputable def u1 : G := ((S.frame.ψ.symm ⟨dv 0 1, dv_facts.1⟩ : ↥V) : G)

@[expose] noncomputable def u2 : G := ((S.frame.ψ.symm ⟨dv 0 2, dv_facts.2.1⟩ : ↥V) : G)

theorem u1_mem_V : S.u1 ∈ V := (S.frame.ψ.symm _).2

theorem u2_mem_V : S.u2 ∈ V := (S.frame.ψ.symm _).2

theorem psi_u1 : (S.frame.ψ ⟨S.u1, S.u1_mem_V⟩ : P6) = dv 0 1 := by
  have e : (⟨S.u1, S.u1_mem_V⟩ : ↥V) = S.frame.ψ.symm ⟨dv 0 1, dv_facts.1⟩ := rfl
  rw [e, MulEquiv.apply_symm_apply]

theorem psi_u2 : (S.frame.ψ ⟨S.u2, S.u2_mem_V⟩ : P6) = dv 0 2 := by
  have e : (⟨S.u2, S.u2_mem_V⟩ : ↥V) = S.frame.ψ.symm ⟨dv 0 2, dv_facts.2.1⟩ := rfl
  rw [e, MulEquiv.apply_symm_apply]

theorem u1_mem_V2 : S.u1 ∈ S.V2 :=
  S.mem_pre.2 ⟨S.u1_mem_V, by
    rw [Subgroup.mem_mk]; show InW2 _; rw [psi_u1]; exact dv_facts.2.2.2.2.1⟩

theorem u1_mem_V3 : S.u1 ∈ S.V3 := S.V2_le_V3 S.u1_mem_V2

theorem u2_mem_V3 : S.u2 ∈ S.V3 := S.symm_mem_V3 dv_facts.2.2.2.1

theorem mem_V1_iff_psi {x : G} (hx : x ∈ V) :
    x ∈ fsuV1 T V ↔ (S.frame.ψ ⟨x, hx⟩ : P6) = 1 ∨ (S.frame.ψ ⟨x, hx⟩ : P6) = e0123 := by
  rw [S.mem_V1_iff]
  constructor
  · rintro (rfl | rfl)
    · left
      have : (⟨(1 : G), hx⟩ : ↥V) = 1 := rfl
      rw [this, map_one]
      rfl
    · right
      rw [show (⟨S.z, hx⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ from rfl, S.psi_z]
  · rintro (h | h)
    · left
      have : S.frame.ψ ⟨x, hx⟩ = S.frame.ψ 1 := by rw [map_one]; exact Subtype.ext h
      exact congrArg Subtype.val (S.frame.ψ.injective this)
    · right
      have : S.frame.ψ ⟨x, hx⟩ = S.frame.ψ ⟨S.z, S.z_mem_V⟩ := by
        rw [S.psi_z]; exact Subtype.ext h
      exact congrArg Subtype.val (S.frame.ψ.injective this)

theorem V3_cases {x : G} (hx : x ∈ S.V3) :
    x ∈ fsuV1 T V ∨ x * S.u1⁻¹ ∈ fsuV1 T V ∨ x * S.u2⁻¹ ∈ fsuV1 T V ∨
      x * (S.u1 * S.u2)⁻¹ ∈ fsuV1 T V := by
  obtain ⟨hxV, hx3⟩ := S.mem_pre.1 hx
  have hy4 : InW4 (S.frame.ψ ⟨x, hxV⟩ : P6) := (S.frame.ψ ⟨x, hxV⟩).2
  have key : ∀ (w : G) (hw : w ∈ V), (S.frame.ψ ⟨w, hw⟩ : P6) = dv 0 1 ∨
      (S.frame.ψ ⟨w, hw⟩ : P6) = dv 0 2 ∨ (S.frame.ψ ⟨w, hw⟩ : P6) = dv 0 1 * dv 0 2 →
      ((S.frame.ψ ⟨x, hxV⟩ : P6) * (S.frame.ψ ⟨w, hw⟩ : P6)⁻¹ = 1 ∨
        (S.frame.ψ ⟨x, hxV⟩ : P6) * (S.frame.ψ ⟨w, hw⟩ : P6)⁻¹ = e0123) →
      x * w⁻¹ ∈ fsuV1 T V := by
    intro w hw _ h
    have hxw : x * w⁻¹ ∈ V := V.mul_mem hxV (V.inv_mem hw)
    refine (S.mem_V1_iff_psi hxw).2 ?_
    have e : (⟨x * w⁻¹, hxw⟩ : ↥V) = ⟨x, hxV⟩ * (⟨w, hw⟩ : ↥V)⁻¹ := rfl
    rw [e, map_mul, map_inv]
    exact h
  have hu12 : S.u1 * S.u2 ∈ V := V.mul_mem S.u1_mem_V S.u2_mem_V
  have psi12 : (S.frame.ψ ⟨S.u1 * S.u2, hu12⟩ : P6) = dv 0 1 * dv 0 2 := by
    have e : (⟨S.u1 * S.u2, hu12⟩ : ↥V) = ⟨S.u1, S.u1_mem_V⟩ * ⟨S.u2, S.u2_mem_V⟩ := rfl
    rw [e, map_mul, Subgroup.coe_mul, psi_u1, psi_u2]
  rcases w3_cases _ hy4 hx3 with h | h | h | h
  · exact Or.inl ((S.mem_V1_iff_psi hxV).2 h)
  · right; left
    exact key _ S.u1_mem_V (Or.inl S.psi_u1) (by rw [S.psi_u1]; exact h)
  · right; right; left
    exact key _ S.u2_mem_V (Or.inr (Or.inl S.psi_u2)) (by rw [S.psi_u2]; exact h)
  · right; right; right
    exact key _ hu12 (Or.inr (Or.inr psi12)) (by rw [psi12]; exact h)

theorem u1_not_V1 : S.u1 ∉ fsuV1 T V := by
  rw [S.mem_V1_iff_psi S.u1_mem_V, S.psi_u1]
  exact not_or.2 ⟨dv_facts.2.2.2.2.2.1, dv_facts.2.2.2.2.2.2.1⟩

theorem u2_not_V1 : S.u2 ∉ fsuV1 T V := by
  rw [S.mem_V1_iff_psi S.u2_mem_V, S.psi_u2]
  exact not_or.2 ⟨dv_facts.2.2.2.2.2.2.2.1, dv_facts.2.2.2.2.2.2.2.2.1⟩

theorem u21_not_V1 : S.u2 * S.u1⁻¹ ∉ fsuV1 T V := by
  have h : S.u2 * S.u1⁻¹ ∈ V := V.mul_mem S.u2_mem_V (V.inv_mem S.u1_mem_V)
  rw [S.mem_V1_iff_psi h]
  have e : (⟨S.u2 * S.u1⁻¹, h⟩ : ↥V) = ⟨S.u2, S.u2_mem_V⟩ * (⟨S.u1, S.u1_mem_V⟩ : ↥V)⁻¹ := rfl
  rw [e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, S.psi_u1, S.psi_u2]
  exact not_or.2 ⟨dv_facts.2.2.2.2.2.2.2.2.2.1, dv_facts.2.2.2.2.2.2.2.2.2.2.1⟩

theorem u12_not_V1 : S.u1 * S.u2 ∉ fsuV1 T V := by
  have h : S.u1 * S.u2 ∈ V := V.mul_mem S.u1_mem_V S.u2_mem_V
  rw [S.mem_V1_iff_psi h]
  have e : (⟨S.u1 * S.u2, h⟩ : ↥V) = ⟨S.u1, S.u1_mem_V⟩ * ⟨S.u2, S.u2_mem_V⟩ := rfl
  rw [e, map_mul, Subgroup.coe_mul, S.psi_u1, S.psi_u2]
  exact not_or.2 ⟨dv_facts.2.2.2.2.2.2.2.2.2.2.2.1, dv_facts.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

end Setting4

theorem eight_dvd_card_map {G : Type} [Group G] [Finite G] {H T : Subgroup G}
    (hT : IsSylowTwoOf T H) (ρ : ↥H →* Perm (Fin 6))
    (hker : ∀ h : ↥H, ρ h = 1 → (h : G) ∈ T)
    (hA : alternatingGroup (Fin 6) ≤ ρ.range) :
    8 ∣ Nat.card ((T.subgroupOf H).map ρ) := by
  obtain ⟨-, -, hodd⟩ := hT
  set f := ρ.rangeRestrict with hf
  have hfs : Function.Surjective f := MonoidHom.rangeRestrict_surjective ρ
  have hfk : f.ker ≤ T.subgroupOf H := by
    intro x hx
    have hx' : x ∈ ρ.ker := by rwa [hf, MonoidHom.ker_rangeRestrict] at hx
    exact Subgroup.mem_subgroupOf.mpr (hker x (MonoidHom.mem_ker.mp hx'))
  have hidx : ((T.subgroupOf H).map f).index = (T.subgroupOf H).index :=
    Subgroup.index_map_eq (T.subgroupOf H) hfs hfk
  have hcard := Subgroup.card_mul_index ((T.subgroupOf H).map f)
  rw [hidx] at hcard
  have h360 : 360 ∣ Nat.card ρ.range := by
    have := Subgroup.card_dvd_of_le hA
    rwa [card_alt6] at this
  have hcop : Nat.Coprime 8 (T.subgroupOf H).index := by
    have h2 : Nat.Coprime 2 (T.subgroupOf H).index := (Nat.Prime.coprime_iff_not_dvd
      Nat.prime_two).mpr hodd
    exact Nat.Coprime.pow_left 3 h2
  have h8 : 8 ∣ Nat.card ((T.subgroupOf H).map f) := by
    have : 8 ∣ Nat.card ((T.subgroupOf H).map f) * (T.subgroupOf H).index := by
      rw [hcard]
      exact (by norm_num : (8 : ℕ) ∣ 360).trans h360
    exact hcop.dvd_of_dvd_mul_right this
  have e : (T.subgroupOf H).map ρ = ((T.subgroupOf H).map f).map ρ.range.subtype := by
    rw [Subgroup.map_map]
    rfl
  rw [e, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact h8

theorem mem_stabSubN {a b : Fin 6 → ZMod 2} {σ : Perm (Fin 6)} :
    σ ∈ stabSubN a b ↔ StabLn a b σ := Iff.rfl

theorem mem_stabSub {a b : Fin 6 → ZMod 2} {σ : Perm (Fin 6)} :
    σ ∈ stabSub a b ↔ StabL a b σ := Iff.rfl

theorem stabSubN_conj {a b c d : Fin 6 → ZMod 2} {τ : Perm (Fin 6)}
    (h1 : InLn c d (vp τ⁻¹ a)) (h2 : InLn c d (vp τ⁻¹ b)) (h3 : InLn a b (vp τ c))
    (h4 : InLn a b (vp τ d)) (σ : Perm (Fin 6)) :
    σ ∈ stabSubN a b ↔ τ⁻¹ * σ * τ ∈ stabSubN c d := by
  rw [mem_stabSubN, mem_stabSubN]
  constructor
  · intro hσ
    refine ⟨?_, ?_⟩ <;> rw [vp_mul, vp_mul] <;>
      refine inLn_maps (vp_add τ⁻¹) (vp_const τ⁻¹) h1 h2 (stabLn_maps hσ ?_)
    · exact h3
    · exact h4
  · intro hσ
    have e : σ = τ * (τ⁻¹ * σ * τ) * τ⁻¹ := by group
    refine ⟨?_, ?_⟩ <;> rw [e, vp_mul, vp_mul] <;>
      refine inLn_maps (vp_add τ) (vp_const τ) h3 h4 (stabLn_maps hσ ?_)
    · exact h1
    · exact h2

theorem stabSub_conj {a b c d : Fin 6 → ZMod 2} {τ : Perm (Fin 6)}
    (h1 : InL c d (vp τ⁻¹ a)) (h2 : InL c d (vp τ⁻¹ b)) (h3 : InL a b (vp τ c))
    (h4 : InL a b (vp τ d)) (σ : Perm (Fin 6)) :
    σ ∈ stabSub a b ↔ τ⁻¹ * σ * τ ∈ stabSub c d := by
  rw [mem_stabSub, mem_stabSub]
  constructor
  · intro hσ
    refine ⟨?_, ?_⟩ <;> rw [vp_mul, vp_mul] <;>
      refine inL_maps (vp_add τ⁻¹) h1 h2 (stabL_maps hσ ?_)
    · exact h3
    · exact h4
  · intro hσ
    have e : σ = τ * (τ⁻¹ * σ * τ) * τ⁻¹ := by group
    refine ⟨?_, ?_⟩ <;> rw [e, vp_mul, vp_mul] <;>
      refine inL_maps (vp_add τ) h3 h4 (stabL_maps hσ ?_)
    · exact h1
    · exact h2

theorem card_eq_of_conj {X Y : Subgroup (Perm (Fin 6))} (τ : Perm (Fin 6))
    (h : ∀ σ, σ ∈ X ↔ τ⁻¹ * σ * τ ∈ Y) : Nat.card X = Nat.card Y := by
  have e : Y = X.map (MulAut.conj τ⁻¹).toMonoidHom := by
    ext σ
    rw [Subgroup.mem_map]
    constructor
    · intro hσ
      refine ⟨τ * σ * τ⁻¹, (h _).2 ?_, ?_⟩
      · have e1 : τ⁻¹ * (τ * σ * τ⁻¹) * τ = σ := by group
        rw [e1]
        exact hσ
      · show τ⁻¹ * (τ * σ * τ⁻¹) * τ⁻¹⁻¹ = σ
        group
    · rintro ⟨x, hx, rfl⟩
      show τ⁻¹ * x * τ⁻¹⁻¹ ∈ Y
      rw [inv_inv]
      exact (h x).1 hx
  rw [e, Subgroup.card_map_of_injective (MulAut.conj τ⁻¹).injective]

@[expose] def onesE : ↥(evenWeight 6) :=
  ⟨onesV, by simpa [evenWeight] using sum_ones⟩

theorem sum_eq_zero (x : ↥(evenWeight 6)) : ∑ i, (x : Fin 6 → ZMod 2) i = 0 := by
  have := x.2
  simpa [evenWeight] using this

theorem zmod2_add_one : ∀ c : ZMod 2, c ≠ 0 → c + 1 = 0 := by
  decide

theorem exists_rep5 (x : AltHeart 6) :
    ∃ r : ↥(evenWeight 6), (QuotientAddGroup.mk r : AltHeart 6) = x ∧
      (r : Fin 6 → ZMod 2) 5 = 0 := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective x
  by_cases h : (r : Fin 6 → ZMod 2) 5 = 0
  · exact ⟨r, rfl, h⟩
  · refine ⟨r + onesE, (mk_eq_mk_iff _ _).2 (Or.inr rfl), ?_⟩
    show (r : Fin 6 → ZMod 2) 5 + 1 = 0
    exact zmod2_add_one _ h

theorem mk_eq_of {r y : ↥(evenWeight 6)}
    (h : (r : Fin 6 → ZMod 2) = y ∨ (r : Fin 6 → ZMod 2) + onesV = y) :
    (QuotientAddGroup.mk r : AltHeart 6) = QuotientAddGroup.mk y := by
  refine (mk_eq_mk_iff r y).2 ?_
  rcases h with h | h
  · exact Or.inl h
  · right
    rw [← h, add_assoc, vadd_self, add_zero]

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem V3_le_UH : S.V3 ≤ conjClosure S.V3 S.G1 := le_conjClosure S.V3 S.G1

theorem beta_eq_of {M : Type} [Group M] {β : ↥(conjClosure S.V3 S.G1) →* M}
    (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V) {u w : ↥(conjClosure S.V3 S.G1)}
    (h : (u : G) * (w : G)⁻¹ ∈ fsuV1 T V) : β u = β w := by
  have := (hβk (u * w⁻¹)).2 h
  rwa [map_mul, map_inv, mul_inv_eq_one] at this

theorem mem_V1_of_beta_eq {M : Type} [Group M] {β : ↥(conjClosure S.V3 S.G1) →* M}
    (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V) {u w : ↥(conjClosure S.V3 S.G1)}
    (h : β u = β w) : (u : G) * (w : G)⁻¹ ∈ fsuV1 T V := by
  have := (hβk (u * w⁻¹)).1 (by rw [map_mul, map_inv, h, mul_inv_cancel])
  exact this

theorem V1_le_V3 : fsuV1 T V ≤ S.V3 := S.V1_le_V2.trans S.V2_le_V3

section Nat

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6)}
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
      (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) = Multiplicative.toAdd (β v))
  {ra rb : ↥(evenWeight 6)}
  (hra : (QuotientAddGroup.mk ra : AltHeart 6) =
    Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩))
  (hrb : (QuotientAddGroup.mk rb : AltHeart 6) =
    Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩))
include hβk hra hrb

theorem inLn_of_V3 {u : G} (hu : u ∈ S.V3) (r : ↥(evenWeight 6))
    (hr : (QuotientAddGroup.mk r : AltHeart 6) = Multiplicative.toAdd (β ⟨u, S.V3_le_UH hu⟩)) :
    InLn (ra : Fin 6 → ZMod 2) rb r := by
  have hc := S.V3_cases hu
  rcases hc with h | h | h | h
  · have hb : β ⟨u, S.V3_le_UH hu⟩ = 1 := (hβk _).2 h
    rw [hb, toAdd_one, mk_eq_zero_iff] at hr
    rcases hr with hr | hr
    · exact Or.inl (Or.inl hr)
    · exact Or.inr (Or.inl (by rw [hr]; exact vadd_self _))
  · have hb := S.beta_eq_of hβk (u := ⟨u, S.V3_le_UH hu⟩)
      (w := ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) h
    rw [hb, ← hra, mk_eq_mk_iff] at hr
    rcases hr with hr | hr
    · exact Or.inl (Or.inr (Or.inl hr))
    · exact Or.inr (Or.inr (Or.inl (by rw [hr, add_assoc, vadd_self, add_zero])))
  · have hb := S.beta_eq_of hβk (u := ⟨u, S.V3_le_UH hu⟩)
      (w := ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) h
    rw [hb, ← hrb, mk_eq_mk_iff] at hr
    rcases hr with hr | hr
    · exact Or.inl (Or.inr (Or.inr (Or.inl hr)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hr, add_assoc, vadd_self, add_zero]))))
  · have h12 : S.u1 * S.u2 ∈ S.V3 := S.V3.mul_mem S.u1_mem_V3 S.u2_mem_V3
    have hb := S.beta_eq_of hβk (u := ⟨u, S.V3_le_UH hu⟩) (w := ⟨S.u1 * S.u2, S.V3_le_UH h12⟩) h
    have e : β ⟨S.u1 * S.u2, S.V3_le_UH h12⟩ =
        β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ * β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩ := by
      rw [← map_mul]; rfl
    rw [hb, e, toAdd_mul, ← hra, ← hrb, ← QuotientAddGroup.mk_add, mk_eq_mk_iff] at hr
    rcases hr with hr | hr
    · exact Or.inl (Or.inr (Or.inr (Or.inr hr)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [hr, add_assoc, vadd_self, add_zero]; rfl))))

theorem mem_V3_of_inLn (w : ↥(conjClosure S.V3 S.G1)) (r : ↥(evenWeight 6))
    (hr : (QuotientAddGroup.mk r : AltHeart 6) = Multiplicative.toAdd (β w))
    (hl : InLn (ra : Fin 6 → ZMod 2) rb r) : (w : G) ∈ S.V3 := by
  have key : ∀ (x : G) (hx : x ∈ S.V3), β w = β ⟨x, S.V3_le_UH hx⟩ → (w : G) ∈ S.V3 := by
    intro x hx hwx
    have h := S.mem_V1_of_beta_eq hβk hwx
    have e : (w : G) = ((w : G) * x⁻¹) * x := by group
    rw [e]
    exact S.V3.mul_mem (S.V1_le_V3 h) hx
  have h12 : S.u1 * S.u2 ∈ S.V3 := S.V3.mul_mem S.u1_mem_V3 S.u2_mem_V3
  have e12 : β ⟨S.u1 * S.u2, S.V3_le_UH h12⟩ =
      β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ * β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩ := by
    rw [← map_mul]; rfl
  have cases : ∀ y : ↥(evenWeight 6), (QuotientAddGroup.mk r : AltHeart 6) =
      QuotientAddGroup.mk y → Multiplicative.toAdd (β w) = QuotientAddGroup.mk y := by
    intro y hy
    rw [← hr, hy]
  rcases hl with hl | hl <;> rcases hl with hl | hl | hl | hl
  · have := cases 0 (mk_eq_of (Or.inl hl))
    rw [QuotientAddGroup.mk_zero] at this
    exact key 1 (S.V3.one_mem) (by
      rw [show (⟨1, S.V3_le_UH S.V3.one_mem⟩ : ↥(conjClosure S.V3 S.G1)) = 1 from rfl, map_one]
      exact toAdd_eq_zero.mp this)
  · have := cases ra (mk_eq_of (Or.inl hl))
    exact key _ S.u1_mem_V3 (Multiplicative.toAdd.injective (by rw [this, hra]))
  · have := cases rb (mk_eq_of (Or.inl hl))
    exact key _ S.u2_mem_V3 (Multiplicative.toAdd.injective (by rw [this, hrb]))
  · have := cases (ra + rb) (mk_eq_of (Or.inl hl))
    exact key _ h12 (Multiplicative.toAdd.injective (by
      rw [this, e12, toAdd_mul, QuotientAddGroup.mk_add, hra, hrb]))
  · have := cases 0 (mk_eq_of (Or.inr hl))
    rw [QuotientAddGroup.mk_zero] at this
    exact key 1 (S.V3.one_mem) (by
      rw [show (⟨1, S.V3_le_UH S.V3.one_mem⟩ : ↥(conjClosure S.V3 S.G1)) = 1 from rfl, map_one]
      exact toAdd_eq_zero.mp this)
  · have := cases ra (mk_eq_of (Or.inr hl))
    exact key _ S.u1_mem_V3 (Multiplicative.toAdd.injective (by rw [this, hra]))
  · have := cases rb (mk_eq_of (Or.inr hl))
    exact key _ S.u2_mem_V3 (Multiplicative.toAdd.injective (by rw [this, hrb]))
  · have := cases (ra + rb) (mk_eq_of (Or.inr hl))
    exact key _ h12 (Multiplicative.toAdd.injective (by
      rw [this, e12, toAdd_mul, QuotientAddGroup.mk_add, hra, hrb]))

include hβe in
theorem mem_stabSubN_iff (g : ↥S.G1) :
    ρ g ∈ stabSubN (ra : Fin 6 → ZMod 2) rb ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G) := by
  have hUN : ∀ k : ↥S.G1, ∀ x ∈ conjClosure S.V3 S.G1, (k : G) * x * (k : G)⁻¹ ∈
      conjClosure S.V3 S.G1 := fun k x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 k.2) x).mp hx
  have fwd : ∀ k : ↥S.G1, ρ k ∈ stabSubN (ra : Fin 6 → ZMod 2) rb →
      ∀ x ∈ S.V3, (k : G) * x * (k : G)⁻¹ ∈ S.V3 := by
    intro k hk x hx
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective
      (Multiplicative.toAdd (β ⟨x, S.V3_le_UH hx⟩))
    have h1 := S.inLn_of_V3 hβk hra hrb hx r hr
    have h2 := hβe k ⟨x, S.V3_le_UH hx⟩ ⟨_, hUN k x (S.V3_le_UH hx)⟩ rfl r hr
    exact S.mem_V3_of_inLn hβk hra hrb ⟨_, hUN k x (S.V3_le_UH hx)⟩ _ h2
      (stabLn_maps hk h1)
  constructor
  · intro hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fwd g hg x
    · intro hx
      have h := fwd g⁻¹ (by rw [map_inv]; exact (stabSubN _ _).inv_mem hg) _ hx
      have e : ((g⁻¹ : ↥S.G1) : G) * ((g : G) * x * (g : G)⁻¹) * ((g⁻¹ : ↥S.G1) : G)⁻¹ = x := by
        simp only [InvMemClass.coe_inv]; group
      rwa [e] at h
  · intro hg
    have step : ∀ (u : G) (hu : u ∈ S.V3) (r : ↥(evenWeight 6)),
        (QuotientAddGroup.mk r : AltHeart 6) = Multiplicative.toAdd (β ⟨u, S.V3_le_UH hu⟩) →
        InLn (ra : Fin 6 → ZMod 2) rb (vp (ρ g) r) := by
      intro u hu r hr
      have hgu : (g : G) * u * (g : G)⁻¹ ∈ S.V3 := (Subgroup.mem_normalizer_iff.mp hg u).mp hu
      have h2 := hβe g ⟨u, S.V3_le_UH hu⟩ ⟨_, S.V3_le_UH hgu⟩ rfl r hr
      exact S.inLn_of_V3 hβk hra hrb hgu _ h2
    exact ⟨step _ S.u1_mem_V3 ra hra, step _ S.u2_mem_V3 rb hrb⟩

end Nat

end Setting4

theorem vp_vp_inv (τ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : vp τ (vp τ⁻¹ v) = v := by
  rw [← vp_mul, mul_inv_cancel, vp_one]

theorem vp_inv_vp (τ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : vp τ⁻¹ (vp τ v) = v := by
  rw [← vp_mul, inv_mul_cancel, vp_one]

theorem vp_injective (τ : Perm (Fin 6)) : Function.Injective (vp τ) := fun v w h => by
  rw [← vp_inv_vp τ v, h, vp_inv_vp]

theorem sum_vp (τ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : ∑ i, vp τ v i = ∑ i, v i :=
  Equiv.sum_comp τ⁻¹ v

theorem exists_norm5 (v : Fin 6 → ZMod 2) :
    ∃ w : Fin 6 → ZMod 2, (w = v ∨ w = v + onesV) ∧ w 5 = 0 := by
  by_cases h : v 5 = 0
  · exact ⟨v, Or.inl rfl, h⟩
  · exact ⟨v + onesV, Or.inr rfl, zmod2_add_one _ h⟩

theorem add_ones_add_ones (v : Fin 6 → ZMod 2) : v + onesV + onesV = v := by
  rw [add_assoc, vadd_self, add_zero]

theorem inLn_of_mem {c d v x : Fin 6 → ZMod 2} (hx : InL c d x) (h : v = x ∨ v = x + onesV) :
    InLn c d v := by
  rcases h with rfl | rfl
  · exact Or.inl hx
  · exact Or.inr (by rw [add_ones_add_ones]; exact hx)

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section NatTau

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6)}
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
      (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) = Multiplicative.toAdd (β v))
include hβk hβe

theorem exists_tau_nat (hT8 : 8 ∣ Nat.card ((T.subgroupOf S.G1).map ρ)) :
    ∃ τ : Perm (Fin 6), ∀ g : ↥S.G1,
      τ⁻¹ * ρ g * τ ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G) := by
  obtain ⟨ra, hra, -⟩ :=
    exists_rep5 (Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩))
  obtain ⟨rb, hrb, -⟩ :=
    exists_rep5 (Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩))
  have hstab := S.mem_stabSubN_iff hβk hβe hra hrb
  have h8 : 8 ∣ Nat.card (stabSubN (ra : Fin 6 → ZMod 2) rb) := by
    have hle : (T.subgroupOf S.G1).map ρ ≤ stabSubN (ra : Fin 6 → ZMod 2) rb := by
      rintro _ ⟨t, ht, rfl⟩
      exact (hstab t).2 (S.T_le_normalizer_V3 (Subgroup.mem_subgroupOf.mp ht))
    exact hT8.trans (Subgroup.card_dvd_of_le hle)
  have hmk0 : ∀ (u : G) (hu : u ∈ S.V3) (r : ↥(evenWeight 6)), u ∉ fsuV1 T V →
      (QuotientAddGroup.mk r : AltHeart 6) = Multiplicative.toAdd (β ⟨u, S.V3_le_UH hu⟩) →
      (r : Fin 6 → ZMod 2) ≠ 0 ∧ (r : Fin 6 → ZMod 2) ≠ onesV := by
    intro u hu r hn hr
    have h0 : (QuotientAddGroup.mk r : AltHeart 6) ≠ 0 := by
      intro h
      apply hn
      rw [h] at hr
      exact (hβk _).1 (toAdd_eq_zero.mp hr.symm)
    rw [Ne, mk_eq_zero_iff, not_or] at h0
    exact h0
  obtain ⟨ha0, ha1⟩ := hmk0 _ S.u1_mem_V3 ra S.u1_not_V1 hra
  obtain ⟨hb0, hb1⟩ := hmk0 _ S.u2_mem_V3 rb S.u2_not_V1 hrb
  have hab : ¬ ((rb : Fin 6 → ZMod 2) = ra ∨ (rb : Fin 6 → ZMod 2) = ra + onesV) := by
    intro h
    apply S.u21_not_V1
    have e := mk_eq_of (r := rb) (y := ra)
      (by rcases h with h | h; exact Or.inl h; exact Or.inr (by rw [h, add_ones_add_ones]))
    rw [hra, hrb] at e
    exact S.mem_V1_of_beta_eq hβk (Multiplicative.toAdd.injective e)
  obtain ⟨τ₁, -, h1⟩ := relabel_nat _ (sum_eq_zero ra) ha0 ha1
  obtain ⟨b₁, hb₁, hb₁5⟩ := exists_norm5 (vp τ₁⁻¹ (rb : Fin 6 → ZMod 2))
  have hE : InL e0123v b₁ e0123v := Or.inr (Or.inl rfl)
  have hB : InL e0123v b₁ b₁ := Or.inr (Or.inr (Or.inl rfl))
  have g1 : InLn e0123v b₁ (vp τ₁⁻¹ ra) := inLn_of_mem hE h1
  have g2 : InLn e0123v b₁ (vp τ₁⁻¹ rb) :=
    inLn_of_mem hB (by rcases hb₁ with h | h; exact Or.inl h.symm
                       exact Or.inr (by rw [h, add_ones_add_ones]))
  have g3 : InLn (ra : Fin 6 → ZMod 2) rb (vp τ₁ e0123v) := by
    refine inLn_of_mem (x := ra) (Or.inr (Or.inl rfl)) ?_
    rcases h1 with h | h
    · left; rw [← h, vp_vp_inv]
    · right; rw [← vp_vp_inv τ₁ ra, h, vp_add, vp_const, add_ones_add_ones]
  have g4 : InLn (ra : Fin 6 → ZMod 2) rb (vp τ₁ b₁) := by
    refine inLn_of_mem (x := rb) (Or.inr (Or.inr (Or.inl rfl))) ?_
    rcases hb₁ with h | h
    · left; rw [h, vp_vp_inv]
    · right; rw [h, vp_add, vp_vp_inv, vp_const]
  have hconj₁ := stabSubN_conj g1 g2 g3 g4
  have h8' : 8 ∣ (Finset.univ.filter (StabLn e0123v b₁)).card := by
    rw [← card_stabSubN, ← card_eq_of_conj τ₁ hconj₁]
    exact h8
  have hsum : ∑ i, b₁ i = 0 := by
    rcases hb₁ with h | h <;> rw [h]
    · rw [sum_vp]; exact sum_eq_zero rb
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, sum_vp, sum_eq_zero rb, sum_ones, add_zero]
  have hne0 : b₁ ≠ 0 := by
    intro h
    rcases hb₁ with h' | h'
    · apply hb0
      rw [← vp_vp_inv τ₁ rb, ← h', h, vp_zero]
    · apply hb1
      have : vp τ₁⁻¹ (rb : Fin 6 → ZMod 2) = onesV := by
        rw [← add_ones_add_ones (vp τ₁⁻¹ (rb : Fin 6 → ZMod 2)), ← h', h, zero_add]
      rw [← vp_vp_inv τ₁ rb, this, vp_const]
  have hneE : b₁ ≠ e0123v := by
    intro h
    apply hab
    have hb' : vp τ₁⁻¹ (rb : Fin 6 → ZMod 2) = e0123v ∨
        vp τ₁⁻¹ (rb : Fin 6 → ZMod 2) = e0123v + onesV := by
      rcases hb₁ with h' | h'
      · left; rw [← h', h]
      · right; rw [← h, h', add_ones_add_ones]
    have key : ∀ x y : Fin 6 → ZMod 2, x = e0123v ∨ x = e0123v + onesV →
        y = e0123v ∨ y = e0123v + onesV → y = x ∨ y = x + onesV := by
      intro x y hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr (add_ones_add_ones _).symm
      · exact Or.inl rfl
    rcases key _ _ h1 hb' with h2 | h2
    · left
      rw [← vp_vp_inv τ₁ rb, h2, vp_vp_inv]
    · right
      rw [← vp_vp_inv τ₁ rb, h2, vp_add, vp_vp_inv, vp_const]
  obtain ⟨τ₂, c1, c2, c3, c4⟩ := cls_nat b₁ ⟨hsum, hb₁5, hne0, hneE⟩ h8'
  have hconj₂ := stabSubN_conj (a := e0123v) (b := b₁) c3 c4 c1 c2
  refine ⟨τ₁ * τ₂, fun g => ?_⟩
  have e : (τ₁ * τ₂)⁻¹ * ρ g * (τ₁ * τ₂) = τ₂⁻¹ * (τ₁⁻¹ * ρ g * τ₁) * τ₂ := by group
  rw [e, ← hstab, hconj₁, hconj₂]
  constructor
  · intro hc
    exact (iota0_stab _ hc).2
  · intro hs
    exact mem_cList _ (stabN_iota0 _ hs)

end NatTau

end Setting4

theorem wtv_eq_zero : ∀ v : Fin 6 → ZMod 2, wtv v = 0 → v = 0 := by
  decide +kernel

theorem wtv_eq_six : ∀ v : Fin 6 → ZMod 2, wtv v = 6 → v = onesV := by
  decide +kernel

theorem wtv_ones : wtv onesV = 6 := by
  decide +kernel

theorem ew_add_self (x : ↥(evenWeight 6)) : x + x = 0 :=
  Subtype.ext (vadd_self (x : Fin 6 → ZMod 2))

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Cover

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
include hβk

omit hβk in
theorem cover_coe_eq {u w : ↥(conjClosure S.V3 S.G1)}
    (h : ((Multiplicative.toAdd (β u) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) =
      ((Multiplicative.toAdd (β w) : ↥(evenWeight 6)) : Fin 6 → ZMod 2)) : β u = β w :=
  Multiplicative.toAdd.injective (Subtype.ext h)

omit hβk in
theorem cover_mul (u w : G) (hu : u ∈ S.V3) (hw : w ∈ S.V3) :
    ((Multiplicative.toAdd (β ⟨u * w, S.V3_le_UH (S.V3.mul_mem hu hw)⟩) : ↥(evenWeight 6)) :
      Fin 6 → ZMod 2) =
    ((Multiplicative.toAdd (β ⟨u, S.V3_le_UH hu⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) +
      ((Multiplicative.toAdd (β ⟨w, S.V3_le_UH hw⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) := by
  have e : β ⟨u * w, S.V3_le_UH (S.V3.mul_mem hu hw)⟩ =
      β ⟨u, S.V3_le_UH hu⟩ * β ⟨w, S.V3_le_UH hw⟩ := by
    rw [← map_mul]; rfl
  rw [e, toAdd_mul]
  rfl

theorem cover_inL_of_V3 {u : G} (hu : u ∈ S.V3) :
    InL ((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2)
      ((Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2)
      ((Multiplicative.toAdd (β ⟨u, S.V3_le_UH hu⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) := by
  rcases S.V3_cases hu with h | h | h | h
  · have hb : β ⟨u, S.V3_le_UH hu⟩ = 1 := (hβk _).2 h
    rw [hb, toAdd_one]
    exact Or.inl rfl
  · rw [S.beta_eq_of hβk (u := ⟨u, S.V3_le_UH hu⟩) (w := ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) h]
    exact Or.inr (Or.inl rfl)
  · rw [S.beta_eq_of hβk (u := ⟨u, S.V3_le_UH hu⟩) (w := ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) h]
    exact Or.inr (Or.inr (Or.inl rfl))
  · have h12 : S.u1 * S.u2 ∈ S.V3 := S.V3.mul_mem S.u1_mem_V3 S.u2_mem_V3
    rw [S.beta_eq_of hβk (u := ⟨u, S.V3_le_UH hu⟩) (w := ⟨S.u1 * S.u2, S.V3_le_UH h12⟩) h]
    exact Or.inr (Or.inr (Or.inr (S.cover_mul _ _ S.u1_mem_V3 S.u2_mem_V3)))

theorem cover_mem_V3_of_inL (w : ↥(conjClosure S.V3 S.G1))
    (hl : InL ((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2)
      ((Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2)
      ((Multiplicative.toAdd (β w) : ↥(evenWeight 6)) : Fin 6 → ZMod 2)) : (w : G) ∈ S.V3 := by
  have key : ∀ (x : G) (hx : x ∈ S.V3), β w = β ⟨x, S.V3_le_UH hx⟩ → (w : G) ∈ S.V3 := by
    intro x hx hwx
    have h := S.mem_V1_of_beta_eq hβk hwx
    have e : (w : G) = ((w : G) * x⁻¹) * x := by group
    rw [e]
    exact S.V3.mul_mem (S.V1_le_V3 h) hx
  have h12 : S.u1 * S.u2 ∈ S.V3 := S.V3.mul_mem S.u1_mem_V3 S.u2_mem_V3
  rcases hl with hl | hl | hl | hl
  · refine key 1 S.V3.one_mem (S.cover_coe_eq ?_)
    rw [hl, show (⟨1, S.V3_le_UH S.V3.one_mem⟩ : ↥(conjClosure S.V3 S.G1)) = 1 from rfl,
      map_one, toAdd_one]
    rfl
  · exact key _ S.u1_mem_V3 (S.cover_coe_eq hl)
  · exact key _ S.u2_mem_V3 (S.cover_coe_eq hl)
  · refine key _ h12 (S.cover_coe_eq ?_)
    rw [hl, S.cover_mul _ _ S.u1_mem_V3 S.u2_mem_V3]

include hβe in
theorem cover_mem_stabSub_iff (g : ↥S.G1) :
    ρ g ∈ stabSub ((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) :
        ↥(evenWeight 6)) : Fin 6 → ZMod 2)
      ((Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2) ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G) := by
  have hUN : ∀ k : ↥S.G1, ∀ x ∈ conjClosure S.V3 S.G1, (k : G) * x * (k : G)⁻¹ ∈
      conjClosure S.V3 S.G1 := fun k x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 k.2) x).mp hx
  have fwd : ∀ k : ↥S.G1, ρ k ∈ stabSub
      ((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2)
      ((Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2) →
      ∀ x ∈ S.V3, (k : G) * x * (k : G)⁻¹ ∈ S.V3 := by
    intro k hk x hx
    have h1 := S.cover_inL_of_V3 hβk hx
    have h2 := hβe k ⟨x, S.V3_le_UH hx⟩ ⟨_, hUN k x (S.V3_le_UH hx)⟩ rfl
    refine S.cover_mem_V3_of_inL hβk ⟨_, hUN k x (S.V3_le_UH hx)⟩ ?_
    rw [h2]
    exact stabL_maps hk h1
  constructor
  · intro hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fwd g hg x
    · intro hx
      have h := fwd g⁻¹ (by rw [map_inv]; exact (stabSub _ _).inv_mem hg) _ hx
      have e : ((g⁻¹ : ↥S.G1) : G) * ((g : G) * x * (g : G)⁻¹) * ((g⁻¹ : ↥S.G1) : G)⁻¹ = x := by
        simp only [InvMemClass.coe_inv]; group
      rwa [e] at h
  · intro hg
    have step : ∀ (u : G) (hu : u ∈ S.V3), InL
        ((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) : ↥(evenWeight 6)) :
          Fin 6 → ZMod 2)
        ((Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) : ↥(evenWeight 6)) :
          Fin 6 → ZMod 2)
        (vp (ρ g) ((Multiplicative.toAdd (β ⟨u, S.V3_le_UH hu⟩) : ↥(evenWeight 6)) :
          Fin 6 → ZMod 2)) := by
      intro u hu
      have hgu : (g : G) * u * (g : G)⁻¹ ∈ S.V3 := (Subgroup.mem_normalizer_iff.mp hg u).mp hu
      have h2 := hβe g ⟨u, S.V3_le_UH hu⟩ ⟨_, S.V3_le_UH hgu⟩ rfl
      have h3 := S.cover_inL_of_V3 hβk hgu
      rw [h2] at h3
      exact h3
    exact ⟨step _ S.u1_mem_V3, step _ S.u2_mem_V3⟩

include hβe in
theorem cover_not_unique_weight (hL1T : S.L1 ⊔ T ≤ S.G1) {r : G} (hr : r ∈ S.V3)
    (hr1 : r ∉ fsuV1 T V)
    (huniq : ∀ (y : G) (hy : y ∈ S.V3),
      wtv ((Multiplicative.toAdd (β ⟨y, S.V3_le_UH hy⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) =
        wtv ((Multiplicative.toAdd (β ⟨r, S.V3_le_UH hr⟩) : ↥(evenWeight 6)) :
          Fin 6 → ZMod 2) →
      β ⟨y, S.V3_le_UH hy⟩ = β ⟨r, S.V3_le_UH hr⟩) : False := by
  let X : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ S.V3, β ⟨x, S.V3_le_UH hx⟩ = 1 ∨
        β ⟨x, S.V3_le_UH hx⟩ = β ⟨r, S.V3_le_UH hr⟩}
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨S.V3.mul_mem hx hy, ?_⟩
        have e : β ⟨x * y, S.V3_le_UH (S.V3.mul_mem hx hy)⟩ =
            β ⟨x, S.V3_le_UH hx⟩ * β ⟨y, S.V3_le_UH hy⟩ := by
          rw [← map_mul]; rfl
        rw [e]
        rcases hx' with h1 | h1 <;> rcases hy' with h2 | h2 <;> rw [h1, h2]
        · left; rw [one_mul]
        · right; rw [one_mul]
        · right; rw [mul_one]
        · left
          apply Multiplicative.toAdd.injective
          rw [toAdd_mul, ew_add_self, toAdd_one]
      one_mem' := ⟨S.V3.one_mem, Or.inl (by
        rw [show (⟨1, S.V3_le_UH S.V3.one_mem⟩ : ↥(conjClosure S.V3 S.G1)) = 1 from rfl,
          map_one])⟩
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨S.V3.inv_mem hx, ?_⟩
        have e : β ⟨x⁻¹, S.V3_le_UH (S.V3.inv_mem hx)⟩ = (β ⟨x, S.V3_le_UH hx⟩)⁻¹ := by
          rw [← map_inv]; rfl
        rw [e]
        rcases hx' with h1 | h1 <;> rw [h1]
        · left; rw [inv_one]
        · right
          apply Multiplicative.toAdd.injective
          rw [toAdd_inv, neg_eq_iff_add_eq_zero, ew_add_self] }
  have hmem : ∀ x, x ∈ X ↔ ∃ hx : x ∈ S.V3, β ⟨x, S.V3_le_UH hx⟩ = 1 ∨
      β ⟨x, S.V3_le_UH hx⟩ = β ⟨r, S.V3_le_UH hr⟩ := fun x => Iff.rfl
  have h1 : fsuV1 T V ≤ X := fun x hx =>
    (hmem x).2 ⟨S.V1_le_V3 hx, Or.inl ((hβk _).2 hx)⟩
  have h3 : X ≤ S.V3 := fun x hx => ((hmem x).1 hx).1
  have fwd : ∀ h ∈ S.L1 ⊔ T, ∀ x ∈ X, h * x * h⁻¹ ∈ X := by
    intro h hh x hx
    obtain ⟨hx3, hx'⟩ := (hmem x).1 hx
    have hhx : h * x * h⁻¹ ∈ S.V3 := (Subgroup.mem_normalizer_iff.mp (S.L1T_le_NV3 hh) x).mp hx3
    refine (hmem _).2 ⟨hhx, ?_⟩
    have he := hβe ⟨h, hL1T hh⟩ ⟨x, S.V3_le_UH hx3⟩ ⟨_, S.V3_le_UH hhx⟩ rfl
    rcases hx' with h1 | h1
    · left
      apply Multiplicative.toAdd.injective
      rw [he, h1, toAdd_one]
      rfl
    · right
      refine huniq _ hhx ?_
      rw [he, h1]
      exact wtv_vp _ _
  have hN : S.L1 ⊔ T ≤ Subgroup.normalizer (X : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fwd h hh x, fun hx => ?_⟩
    have := fwd h⁻¹ ((S.L1 ⊔ T).inv_mem hh) _ hx
    rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this
  rcases S.irred_V3 X h1 h3 hN with hX | hX
  · exact hr1 (hX ▸ (hmem r).2 ⟨hr, Or.inr rfl⟩)
  · have ha := (hmem S.u1).1 (hX ▸ S.u1_mem_V3)
    have hb := (hmem S.u2).1 (hX ▸ S.u2_mem_V3)
    obtain ⟨_, ha⟩ := ha
    obtain ⟨_, hb⟩ := hb
    rcases ha with ha | ha
    · exact S.u1_not_V1 ((hβk _).1 ha)
    rcases hb with hb | hb
    · exact S.u2_not_V1 ((hβk _).1 hb)
    apply S.u21_not_V1
    exact S.mem_V1_of_beta_eq hβk (u := ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩)
      (w := ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) (by rw [ha, hb])

end Cover

end Setting4

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section CoverTau

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
include hβk hβe

theorem exists_tau_cover (hL1T : S.L1 ⊔ T ≤ S.G1)
    (hT8 : 8 ∣ Nat.card ((T.subgroupOf S.G1).map ρ)) :
    ∃ τ : Perm (Fin 6), ∀ g : ↥S.G1,
      τ⁻¹ * ρ g * τ ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G) := by
  have h12 : S.u1 * S.u2 ∈ S.V3 := S.V3.mul_mem S.u1_mem_V3 S.u2_mem_V3
  set a : Fin 6 → ZMod 2 := ((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) :
    ↥(evenWeight 6)) : Fin 6 → ZMod 2) with ha_def
  set b : Fin 6 → ZMod 2 := ((Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) :
    ↥(evenWeight 6)) : Fin 6 → ZMod 2) with hb_def
  have hab_def : ((Multiplicative.toAdd (β ⟨S.u1 * S.u2, S.V3_le_UH h12⟩) :
      ↥(evenWeight 6)) : Fin 6 → ZMod 2) = a + b := S.cover_mul _ _ S.u1_mem_V3 S.u2_mem_V3
  have hstab : ∀ g : ↥S.G1, ρ g ∈ stabSub a b ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G) :=
    S.cover_mem_stabSub_iff hβk hβe
  have h8 : 8 ∣ Nat.card (stabSub a b) := by
    have hle : (T.subgroupOf S.G1).map ρ ≤ stabSub a b := by
      rintro _ ⟨t, ht, rfl⟩
      exact (hstab t).2 (S.T_le_normalizer_V3 (Subgroup.mem_subgroupOf.mp ht))
    exact hT8.trans (Subgroup.card_dvd_of_le hle)
  have hvec0 : ∀ (u : G) (hu : u ∈ S.V3), u ∉ fsuV1 T V →
      ((Multiplicative.toAdd (β ⟨u, S.V3_le_UH hu⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) ≠ 0 := by
    intro u hu hn h
    apply hn
    refine (hβk ⟨u, S.V3_le_UH hu⟩).1 (Multiplicative.toAdd.injective ?_)
    rw [toAdd_one]
    exact Subtype.ext h
  have ha0 : a ≠ 0 := hvec0 _ S.u1_mem_V3 S.u1_not_V1
  have hb0 : b ≠ 0 := hvec0 _ S.u2_mem_V3 S.u2_not_V1
  have hab0 : a + b ≠ 0 := by rw [← hab_def]; exact hvec0 _ h12 S.u12_not_V1
  have hba : b ≠ a := fun h => S.u21_not_V1 (S.mem_V1_of_beta_eq hβk (S.cover_coe_eq h))
  have hval : ∀ (y : G) (hy : y ∈ S.V3), InL a b
      ((Multiplicative.toAdd (β ⟨y, S.V3_le_UH hy⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) :=
    fun y hy => S.cover_inL_of_V3 hβk hy
  have uniq : ∀ (r : G) (hr : r ∈ S.V3), r ∉ fsuV1 T V → (∀ (y : G) (hy : y ∈ S.V3),
      wtv ((Multiplicative.toAdd (β ⟨y, S.V3_le_UH hy⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) =
        wtv ((Multiplicative.toAdd (β ⟨r, S.V3_le_UH hr⟩) : ↥(evenWeight 6)) :
          Fin 6 → ZMod 2) →
      ((Multiplicative.toAdd (β ⟨y, S.V3_le_UH hy⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) =
        ((Multiplicative.toAdd (β ⟨r, S.V3_le_UH hr⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2)) →
      False := fun r hr hr1 h =>
    S.cover_not_unique_weight hβk hβe hL1T hr hr1 fun y hy hw => S.cover_coe_eq (h y hy hw)
  have hw0 : wtv 0 = 0 := rfl
  have hwt : wtv b = wtv a ∧ wtv (a + b) = wtv a := by
    by_contra hcon
    by_cases h1 : wtv b = wtv a
    · have h2 : wtv (a + b) ≠ wtv a := fun h => hcon ⟨h1, h⟩
      refine uniq _ h12 S.u12_not_V1 fun y hy hw => ?_
      rw [hab_def] at hw ⊢
      rcases hval y hy with h | h | h | h
      · rw [h] at hw; exact absurd (wtv_eq_zero _ (hw0 ▸ hw).symm) hab0
      · rw [h] at hw; exact absurd hw.symm h2
      · rw [h] at hw; exact absurd (hw.symm.trans h1) h2
      · exact h
    · by_cases h2 : wtv (a + b) = wtv a
      · refine uniq _ S.u2_mem_V3 S.u2_not_V1 fun y hy hw => ?_
        change wtv _ = wtv b at hw
        change _ = b
        rcases hval y hy with h | h | h | h
        · rw [h] at hw; exact absurd (wtv_eq_zero _ (hw0 ▸ hw).symm) hb0
        · rw [h] at hw; exact absurd hw.symm h1
        · exact h
        · rw [h] at hw; exact absurd (hw.symm.trans h2).symm (Ne.symm h1)
      · refine uniq _ S.u1_mem_V3 S.u1_not_V1 fun y hy hw => ?_
        change wtv _ = wtv a at hw
        change _ = a
        rcases hval y hy with h | h | h | h
        · rw [h] at hw; exact absurd (wtv_eq_zero _ (hw0 ▸ hw).symm) ha0
        · exact h
        · rw [h] at hw; exact absurd hw h1
        · rw [h] at hw; exact absurd hw h2
  have ha1 : a ≠ onesV := by
    intro h
    apply hba
    rw [wtv_eq_six b (by rw [hwt.1, h, wtv_ones]), h]
  obtain ⟨τ₁, -, hd⟩ := relabel_cover a (sum_eq_zero _) ha0 ha1
  set d := vp τ₁⁻¹ a with hd_def
  set b₁ := vp τ₁⁻¹ b with hb₁_def
  have hconj₁ := stabSub_conj (a := a) (b := b) (c := d) (d := b₁) (τ := τ₁)
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))
    (by rw [hd_def, vp_vp_inv]; exact Or.inr (Or.inl rfl))
    (by rw [hb₁_def, vp_vp_inv]; exact Or.inr (Or.inr (Or.inl rfl)))
  have h8' : 8 ∣ (Finset.univ.filter (StabL d b₁)).card := by
    rw [← card_stabSub, ← card_eq_of_conj τ₁ hconj₁]
    exact h8
  have hyp : HypC d b₁ := by
    refine ⟨by rw [hb₁_def, sum_vp]; exact sum_eq_zero _, ?_, ?_, ?_, ?_⟩
    · intro h
      apply hb0
      rw [← vp_vp_inv τ₁ b, ← hb₁_def, h, vp_zero]
    · intro h
      exact hba (vp_injective τ₁⁻¹ h)
    · rw [hb₁_def, hd_def, wtv_vp, wtv_vp]; exact hwt.1
    · rw [hb₁_def, hd_def, ← vp_add, wtv_vp, wtv_vp]; exact hwt.2
  rcases hd with hd | hd
  · rw [hd] at hyp h8'
    exact absurd h8' (cls_cover45 b₁ hyp)
  · rw [hd] at hyp h8' hconj₁
    obtain ⟨τ₂, c1, c2, c3, c4⟩ := cls_cover b₁ hyp h8'
    have hconj₂ := stabSub_conj (a := e0123v) (b := b₁) c3 c4 c1 c2
    refine ⟨τ₁ * τ₂, fun g => ?_⟩
    have e : (τ₁ * τ₂)⁻¹ * ρ g * (τ₁ * τ₂) = τ₂⁻¹ * (τ₁⁻¹ * ρ g * τ₁) * τ₂ := by group
    rw [e, ← hstab, hconj₁, hconj₂]
    constructor
    · intro hc
      exact (iota0_stab _ hc).1
    · intro hs
      exact mem_cList _ (stab_iota0 _ hs)

end CoverTau

end Setting4

end CFSG.Quasithin.H13.A6
