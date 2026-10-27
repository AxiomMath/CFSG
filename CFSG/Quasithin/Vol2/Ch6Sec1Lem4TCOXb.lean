module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCOCoord
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCOCount

public section

namespace CFSG.Quasithin.H13.L216

open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipSL_mul_self unipSL_zero)
open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T M L V X : Subgroup G} {F : Type} [Field F] [Finite F]
  [CharP F 2]

@[expose] noncomputable def phiX (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F)) (hXL : X ≤ L) : ↥X →* SL(2, F) :=
  (coordHom hLV ψ).comp (Subgroup.inclusion hXL)

@[expose] noncomputable def Xb (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F)) (hXL : X ≤ L) : Subgroup SL(2, F) :=
  (⊤ : Subgroup ↥X).map (phiX hLV ψ hXL)

@[expose] noncomputable def Ub (T : Subgroup G) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F)) (hXL : X ≤ L) : Subgroup SL(2, F) :=
  ((X ⊓ T).subgroupOf X).map (phiX hLV ψ hXL)

section Basic

variable (hLV : L ≤ Subgroup.normalizer (V : Set G)) (ψ : ↥(autOn L V) ≃* SL(2, F))
  (hXL : X ≤ L)

theorem phiX_apply (x : ↥X) : phiX hLV ψ hXL x = coordHom hLV ψ ⟨(x : G), hXL x.2⟩ := rfl

theorem mem_Xb_iff (y : SL(2, F)) :
    y ∈ Xb hLV ψ hXL ↔ ∃ x : ↥X, phiX hLV ψ hXL x = y := by
  unfold Xb
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨x, _, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, Subgroup.mem_top x, hx⟩⟩

theorem mem_Ub_iff (y : SL(2, F)) :
    y ∈ Ub T hLV ψ hXL ↔ ∃ x : ↥X, (x : G) ∈ T ∧ phiX hLV ψ hXL x = y := by
  unfold Ub
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Subgroup.mem_subgroupOf.mp hx).2, rfl⟩
  · rintro ⟨x, hxT, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr ⟨x.2, hxT⟩, rfl⟩

theorem Ub_le_Xb : Ub T hLV ψ hXL ≤ Xb hLV ψ hXL := by
  unfold Ub Xb
  exact Subgroup.map_mono le_top

theorem ker_phiX_le (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (x : ↥X) (hx : phiX hLV ψ hXL x = 1) : (x : G) ∈ T := by
  have h := coordHom_ker_mem hLV ψ hψ hC ⟨(x : G), hXL x.2⟩ hx
  exact h.1

theorem Ub_unip (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    {y : SL(2, F)} (hy : y ∈ Ub T hLV ψ hXL) : ∃ b : F, y = unipSL b := by
  obtain ⟨x, hxT, rfl⟩ := (mem_Ub_iff hLV ψ hXL y).mp hy
  have hmem := coordHom_mem_U0 hLV ψ hψ hC ⟨(x : G), hXL x.2⟩ hxT
  exact (mem_U0_iff _).mp hmem

theorem Ub_conj (hXn : ((X ⊓ T).subgroupOf X).Normal) {y : SL(2, F)} (hy : y ∈ Xb hLV ψ hXL)
    {u : SL(2, F)} (hu : u ∈ Ub T hLV ψ hXL) : y * u * y⁻¹ ∈ Ub T hLV ψ hXL := by
  obtain ⟨x, rfl⟩ := (mem_Xb_iff hLV ψ hXL y).mp hy
  obtain ⟨t, htH, rfl⟩ := (show ∃ t, t ∈ ((X ⊓ T).subgroupOf X) ∧ phiX hLV ψ hXL t = u from by
    unfold Ub at hu
    rw [Subgroup.mem_map] at hu
    exact hu)
  have hn : x * t * x⁻¹ ∈ (X ⊓ T).subgroupOf X := hXn.conj_mem t htH x
  have heq : phiX hLV ψ hXL x * phiX hLV ψ hXL t * (phiX hLV ψ hXL x)⁻¹ =
      phiX hLV ψ hXL (x * t * x⁻¹) := by
    simp only [map_mul, map_inv]
  rw [heq]
  unfold Ub
  exact Subgroup.mem_map_of_mem _ hn

theorem Ub_relIndex (hX5 : (X ⊓ T).relIndex X = 5)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b) :
    (Ub T hLV ψ hXL).relIndex (Xb hLV ψ hXL) = 5 := by
  have hker : (phiX hLV ψ hXL).ker ≤ (X ⊓ T).subgroupOf X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, ker_phiX_le hLV ψ hXL hC hψ x hx⟩
  have key := Subgroup.relIndex_map_map (phiX hLV ψ hXL) ((X ⊓ T).subgroupOf X) ⊤
  rw [sup_eq_left.mpr hker, top_sup_eq] at key
  unfold Ub Xb
  rw [key, Subgroup.relIndex_top_right]
  exact hX5

theorem card_Xb (hX5 : (X ⊓ T).relIndex X = 5)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b) :
    Nat.card (Xb hLV ψ hXL) = 5 * Nat.card (Ub T hLV ψ hXL) := by
  have h1 := Subgroup.index_mul_card (H := (Ub T hLV ψ hXL).subgroupOf (Xb hLV ψ hXL))
  have hrel := Ub_relIndex hLV ψ hXL hX5 hC hψ
  unfold Subgroup.relIndex at hrel
  rw [hrel] at h1
  have h2 : Nat.card ((Ub T hLV ψ hXL).subgroupOf (Xb hLV ψ hXL)) = Nat.card (Ub T hLV ψ hXL) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Ub_le_Xb hLV ψ hXL)).toEquiv
  rw [h2] at h1
  omega


theorem conj_T_mem_Xb (hTX : T ≤ Subgroup.normalizer (X : Set G)) (ℓ : ↥L) (hℓ : (ℓ : G) ∈ T)
    {y : SL(2, F)} (hy : y ∈ Xb hLV ψ hXL) :
    coordHom hLV ψ ℓ * y * (coordHom hLV ψ ℓ)⁻¹ ∈ Xb hLV ψ hXL := by
  obtain ⟨x, rfl⟩ := (mem_Xb_iff hLV ψ hXL _).mp hy
  have hn : (ℓ : G) * (x : G) * (ℓ : G)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp (hTX hℓ) (x : G)).mp x.2
  have hL : (ℓ : G) * (x : G) * (ℓ : G)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem ℓ.2 (hXL x.2)) (L.inv_mem ℓ.2)
  have e : coordHom hLV ψ ℓ * phiX hLV ψ hXL x * (coordHom hLV ψ ℓ)⁻¹ =
      coordHom hLV ψ (ℓ * ⟨(x : G), hXL x.2⟩ * ℓ⁻¹) := by
    rw [phiX_apply, map_mul, map_mul, map_inv]
  have e2 : (ℓ * ⟨(x : G), hXL x.2⟩ * ℓ⁻¹ : ↥L) = ⟨(ℓ : G) * (x : G) * (ℓ : G)⁻¹, hL⟩ :=
    Subtype.ext rfl
  rw [e, e2, mem_Xb_iff]
  exact ⟨⟨(ℓ : G) * (x : G) * (ℓ : G)⁻¹, hn⟩, rfl⟩

theorem Xb_le_borel (hne : Ub T hLV ψ hXL ≠ ⊥)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (hXn : ((X ⊓ T).subgroupOf X).Normal) {y : SL(2, F)} (hy : y ∈ Xb hLV ψ hXL) :
    (y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨b, rfl⟩ := Ub_unip hLV ψ hXL hC hψ hu
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hu1
    apply Subtype.ext
    simp [unipSL_zero]
  exact lower_eq_zero_of_normalizes (Ub T hLV ψ hXL) (fun x hx => Ub_unip hLV ψ hXL hC hψ hx)
    (fun x hx => Ub_conj hLV ψ hXL hXn hy hx) hb0 hu

theorem Ub_ne_bot (hF : Nat.card F = 16)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hX5 : (X ⊓ T).relIndex X = 5) :
    Ub T hLV ψ hXL ≠ ⊥ := by
  classical
  intro hUb
  have hcard := card_Xb hLV ψ hXL hX5 hC hψ
  rw [hUb, Subgroup.card_bot, mul_one] at hcard
  have hXne : Xb hLV ψ hXL ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    omega
  obtain ⟨⟨s, hs⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hXne
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hord : orderOf s = 5 := by
    have h2 : orderOf s ∣ 5 := by
      rw [← hcard]
      exact Subgroup.orderOf_dvd_natCard _ hs
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h2 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hs1'
    · exact h
  have hzp : Subgroup.zpowers s = Xb hLV ψ hXL := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hs)
    rw [Nat.card_zpowers, hord, hcard]
  have hnorm : ∀ b : F, unipSL b * s * (unipSL b)⁻¹ ∈ Subgroup.zpowers s := by
    intro b
    rw [hzp]
    obtain ⟨ℓ, hℓT, hℓ⟩ := exists_of_mem_U0 hLV ψ hψ hC (g := unipSL b)
      ((mem_U0_iff _).mpr ⟨b, rfl⟩)
    rw [← hℓ]
    exact conj_T_mem_Xb hLV ψ hXL hTX ℓ hℓT.1 hs
  exact not_normalized_order_five hF hord hnorm


theorem upper_pow {s : SL(2, F)} (hs : (s : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (n : ℕ) :
    ((s ^ n : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ((s ^ n : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = (s : Matrix (Fin 2) (Fin 2) F) 0 0 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [pow_succ]
    exact ⟨upper_mul_lower h1 hs, by rw [upper_mul_zero_zero h1 hs, h2, pow_succ]⟩

theorem eq_unipSL_of_upper {s : SL(2, F)} (hs : (s : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h1 : (s : Matrix (Fin 2) (Fin 2) F) 0 0 = 1) :
    s = unipSL ((s : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have hs11 : (s : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have hd := det_sl s
    rw [h1, hs, mul_zero, sub_zero, one_mul] at hd
    exact hd
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_unipSL]
  fin_cases i <;> fin_cases j <;> simp [hs, h1, hs11]

theorem mem_Ub_of_unip (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    {y : SL(2, F)} (hy : y ∈ Xb hLV ψ hXL) {b : F} (hb : y = unipSL b) :
    y ∈ Ub T hLV ψ hXL := by
  obtain ⟨x, rfl⟩ := (mem_Xb_iff hLV ψ hXL _).mp hy
  have hT : (x : G) ∈ T :=
    (coordHom_mem_U0_iff hLV ψ hψ hC ⟨(x : G), hXL x.2⟩).mp ⟨b, hb⟩
  exact (mem_Ub_iff hLV ψ hXL _).mpr ⟨x, hT, rfl⟩

theorem exists_zeta (hF : Nat.card F = 16)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hXn : ((X ⊓ T).subgroupOf X).Normal) (hX5 : (X ⊓ T).relIndex X = 5) :
    ∃ s ∈ Xb hLV ψ hXL, (s : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 5 = 1 ∧
      (s : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 1 := by
  classical
  have hcard := card_Xb hLV ψ hXL hX5 hC hψ
  obtain ⟨s, hsX, hsU⟩ : ∃ s ∈ Xb hLV ψ hXL, s ∉ Ub T hLV ψ hXL := by
    by_contra hcon
    push Not at hcon
    have hle : Xb hLV ψ hXL ≤ Ub T hLV ψ hXL := fun s hs => hcon s hs
    have heq : Ub T hLV ψ hXL = Xb hLV ψ hXL := le_antisymm (Ub_le_Xb hLV ψ hXL) hle
    have h1 : Nat.card (Xb hLV ψ hXL) = Nat.card (Ub T hLV ψ hXL) := by rw [heq]
    have hpos : 0 < Nat.card (Ub T hLV ψ hXL) := Nat.card_pos
    omega
  haveI hN : ((Ub T hLV ψ hXL).subgroupOf (Xb hLV ψ hXL)).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using Ub_conj hLV ψ hXL hXn g.2 hn⟩
  have hidx : ((Ub T hLV ψ hXL).subgroupOf (Xb hLV ψ hXL)).index = 5 :=
    Ub_relIndex hLV ψ hXL hX5 hC hψ
  have hs5 : s ^ 5 ∈ Ub T hLV ψ hXL := by
    have h := Subgroup.pow_index_mem ((Ub T hLV ψ hXL).subgroupOf (Xb hLV ψ hXL)) ⟨s, hsX⟩
    rw [hidx] at h
    have h' := Subgroup.mem_subgroupOf.mp h
    simpa using h'
  have hsup : (s : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    Xb_le_borel hLV ψ hXL (Ub_ne_bot hLV ψ hXL hF hC hψ hTX hX5) hC hψ hXn hsX
  have hζ5 : (s : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 5 = 1 := by
    obtain ⟨c, hc⟩ := Ub_unip hLV ψ hXL hC hψ hs5
    have h := (upper_pow hsup 5).2
    rw [hc, coe_unipSL] at h
    simp at h
    exact h.symm
  have hζ1 : (s : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 1 := by
    intro h1
    apply hsU
    have hu := eq_unipSL_of_upper hsup h1
    exact mem_Ub_of_unip hLV ψ hXL hC hψ hsX hu
  exact ⟨s, hsX, hζ5, hζ1⟩

theorem unip_mem_Ub (hF : Nat.card F = 16)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (hXn : ((X ⊓ T).subgroupOf X).Normal) (hne : Ub T hLV ψ hXL ≠ ⊥)
    {s : SL(2, F)} (hs : s ∈ Xb hLV ψ hXL) (hsup : (s : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hζ5 : (s : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 5 = 1)
    (hζ1 : (s : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 1) (b : F) : unipSL b ∈ Ub T hLV ψ hXL := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  let W : AddSubgroup F :=
    { carrier := {b | unipSL b ∈ Ub T hLV ψ hXL}
      add_mem' := fun {a b} ha hb => by
        show unipSL (a + b) ∈ Ub T hLV ψ hXL
        rw [← unipSL_mul_unipSL']
        exact (Ub T hLV ψ hXL).mul_mem ha hb
      zero_mem' := by
        show unipSL 0 ∈ Ub T hLV ψ hXL
        rw [unipSL_zero]
        exact (Ub T hLV ψ hXL).one_mem
      neg_mem' := fun {a} ha => by
        show unipSL (-a) ∈ Ub T hLV ψ hXL
        have hinv : unipSL (-a) = (unipSL a)⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, unipSL_mul_unipSL', neg_add_cancel, unipSL_zero]
        rw [hinv]
        exact (Ub T hLV ψ hXL).inv_mem ha }
  set c : F := (s : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 with hc
  have hc5 : c ^ 5 = 1 := by
    rw [hc]
    calc ((s : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2) ^ 5
        = ((s : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 5) ^ 2 := by ring
      _ = 1 := by rw [hζ5, one_pow]
  have hc1 : c ≠ 1 := by
    intro h
    rw [hc] at h
    have h3 : ((s : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) ^ 2 = 0 := by
      linear_combination h - (s : Matrix (Fin 2) (Fin 2) F) 0 0 * h2 + h2
    exact hζ1 (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3))
  have hWc : ∀ b ∈ W, c * b ∈ W := by
    intro b hb
    have hb' : unipSL b ∈ Ub T hLV ψ hXL := hb
    have h := Ub_conj hLV ψ hXL hXn hs hb'
    rw [conj_unipSL_of_upper hsup b] at h
    show unipSL (c * b) ∈ Ub T hLV ψ hXL
    rw [hc]
    exact h
  have hW0 : W ≠ ⊥ := by
    intro hW
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    obtain ⟨b', rfl⟩ := Ub_unip hLV ψ hXL hC hψ hu
    have hb0 : b' ≠ 0 := by
      rintro rfl
      apply hu1
      apply Subtype.ext
      simp [unipSL_zero]
    have hmem : b' ∈ W := hu
    rw [hW, AddSubgroup.mem_bot] at hmem
    exact hb0 hmem
  have htop := eq_top_of_mul_closed hc5 hc1 hF W hWc hW0
  have hbW : b ∈ W := by
    rw [htop]
    exact AddSubgroup.mem_top b
  exact hbW

theorem conj_borel_mem_Xb (hU : ∀ b : F, unipSL b ∈ Xb hLV ψ hXL)
    (hsup : ∀ y ∈ Xb hLV ψ hXL, (y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    {g : SL(2, F)} (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    {y : SL(2, F)} (hy : y ∈ Xb hLV ψ hXL) : g * y * g⁻¹ ∈ Xb hLV ψ hXL := by
  have hy10 := hsup y hy
  have hyinv10 : ((y⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rw [coe_inv_sl]
    simp [hy10]
  have hginv10 : ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rw [coe_inv_sl]
    simp [hg]
  have hA10 : ((g * y * g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    upper_mul_lower (upper_mul_lower hg hy10) hginv10
  have hA00 : ((g * y * g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (y : Matrix (Fin 2) (Fin 2) F) 0 0 := upper_conj_zero_zero hy10 hg
  have hz10 : ((g * y * g⁻¹ * y⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    upper_mul_lower hA10 hyinv10
  have hz00 : ((g * y * g⁻¹ * y⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [upper_mul_zero_zero hA10 hyinv10, hA00, coe_inv_sl]
    have hd := det_sl y
    rw [hy10, mul_zero, sub_zero] at hd
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    linear_combination hd
  have hzeq := eq_unipSL_of_upper hz10 hz00
  have hzX : g * y * g⁻¹ * y⁻¹ ∈ Xb hLV ψ hXL := by
    rw [hzeq]
    exact hU _
  have hfin : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
  rw [hfin]
  exact (Xb hLV ψ hXL).mul_mem hzX hy

theorem X_le_normalizer_TL (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (hsup : ∀ y ∈ Xb hLV ψ hXL, (y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    X ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  intro x hx
  apply mem_normalizer_of_conj_mem
  intro t ht
  have hgX : phiX hLV ψ hXL ⟨x, hx⟩ ∈ Xb hLV ψ hXL := (mem_Xb_iff hLV ψ hXL _).mpr ⟨_, rfl⟩
  have hgup := hsup _ hgX
  have hL : x * t * x⁻¹ ∈ L := L.mul_mem (L.mul_mem (hXL hx) ht.2) (L.inv_mem (hXL hx))
  have hconj : coordHom hLV ψ ⟨x * t * x⁻¹, hL⟩ =
      phiX hLV ψ hXL ⟨x, hx⟩ * coordHom hLV ψ ⟨t, ht.2⟩ * (phiX hLV ψ hXL ⟨x, hx⟩)⁻¹ := by
    rw [phiX_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hU0 : coordHom hLV ψ ⟨x * t * x⁻¹, hL⟩ ∈ CFSG.PSL2Table.unipSL F := by
    rw [hconj]
    exact borel_le_normalizer_unipSL _ hgup _
      (coordHom_mem_U0 hLV ψ hψ hC ⟨t, ht.2⟩ ht.1)
  obtain ⟨t', ht'T, ht'⟩ := exists_of_mem_U0 hLV ψ hψ hC hU0
  have hk : coordHom hLV ψ (t'⁻¹ * ⟨x * t * x⁻¹, hL⟩) = 1 := by
    rw [map_mul, map_inv, ht', inv_mul_cancel]
  have hkT := coordHom_ker_mem hLV ψ hψ hC _ hk
  have hfac : x * t * x⁻¹ = (t' : G) * ((t'⁻¹ * ⟨x * t * x⁻¹, hL⟩ : ↥L) : G) := by
    simp
  rw [hfac]
  exact (T ⊓ L).mul_mem ht'T hkT

end Basic

end CFSG.Quasithin.H13.L216
