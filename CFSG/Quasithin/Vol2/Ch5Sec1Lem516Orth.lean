module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QW
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OrthFix

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Offender
open scoped IsMulCommutative MatrixGroups Matrix Pointwise
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField (ringAut_card_and_cyclic)

section FixField

variable {F : Type} [Field F] [CharP F 2]

variable (F) in
@[expose] def fixField (m : ℕ) : Subfield F :=
  (iterateFrobenius F 2 m).eqLocusField (RingHom.id F)

theorem mem_fixField {m : ℕ} {x : F} : x ∈ fixField F m ↔ x ^ 2 ^ m = x := by
  rw [fixField, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]

omit [CharP F 2] in
theorem pow_pow_two_pow [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ (2 * m)) (x : F) :
    (x ^ 2 ^ m) ^ 2 ^ m = x := by
  have := Fintype.ofFinite F
  rw [← pow_mul, ← pow_add, ← two_mul, ← hF, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem card_fixField [Finite F] {m : ℕ} (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ (2 * m)) :
    Nat.card (fixField F m) = 2 ^ m := by
  classical
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hup : Nat.card (fixField F m) ≤ 2 ^ m := by
    have : NeZero (2 ^ m - 1) := ⟨by omega⟩
    let f : (fixField F m)ˣ →* Fˣ := Units.map (fixField F m).subtype.toMonoidHom
    have hf : Function.Injective f := Units.map_injective Subtype.val_injective
    have hrange : f.range ≤ rootsOfUnity (2 ^ m - 1) F := by
      rintro _ ⟨u, rfl⟩
      rw [mem_rootsOfUnity]
      apply Units.ext
      have hu : ((u : fixField F m) : F) ^ 2 ^ m = ((u : fixField F m) : F) :=
        mem_fixField.mp (u : fixField F m).2
      have hu0 : ((u : fixField F m) : F) ≠ 0 := fun h0 => u.ne_zero (Subtype.ext h0)
      have h1 : ((u : fixField F m) : F) ^ (2 ^ m - 1) * ((u : fixField F m) : F) =
          ((u : fixField F m) : F) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), hu]
      have h2 := mul_right_cancel₀ hu0 (h1.trans (one_mul _).symm)
      simpa [f] using h2
    have h1 : Nat.card (fixField F m)ˣ ≤ 2 ^ m - 1 := by
      rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
      exact (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity F (2 ^ m - 1))
    rw [Nat.card_units] at h1
    omega
  have hlow : 2 ^ (2 * m) ≤ Nat.card (fixField F m) * Nat.card (fixField F m) := by
    let τ : F →+ F :=
      { toFun := fun x => x + x ^ 2 ^ m
        map_zero' := by simp
        map_add' := fun x y => by
          show (x + y) + (x + y) ^ 2 ^ m = (x + x ^ 2 ^ m) + (y + y ^ 2 ^ m)
          rw [add_pow_char_pow]
          ring }
    have hker : τ.ker = (fixField F m).toAddSubgroup := by
      ext x
      rw [AddMonoidHom.mem_ker, Subfield.mem_toAddSubgroup, mem_fixField]
      show x + x ^ 2 ^ m = 0 ↔ x ^ 2 ^ m = x
      constructor
      · intro h
        have := eq_neg_of_add_eq_zero_right h
        rwa [CharTwo.neg_eq] at this
      · intro h
        rw [h]
        exact CharTwo.add_self_eq_zero x
    have hrange : τ.range ≤ (fixField F m).toAddSubgroup := by
      rintro _ ⟨x, rfl⟩
      rw [Subfield.mem_toAddSubgroup, mem_fixField]
      show (x + x ^ 2 ^ m) ^ 2 ^ m = x + x ^ 2 ^ m
      rw [add_pow_char_pow, pow_pow_two_pow hF, add_comm]
    have h1 := AddSubgroup.card_ker_mul_card_range τ
    rw [hker, hF] at h1
    have e : Nat.card ↥(fixField F m).toAddSubgroup = Nat.card (fixField F m) := rfl
    rw [← h1, e]
    exact Nat.mul_le_mul_left _ ((AddSubgroup.card_le_of_le hrange).trans e.le)
  by_contra hne
  have hlt : Nat.card (fixField F m) < 2 ^ m := lt_of_le_of_ne hup hne
  have h3 := Nat.mul_self_lt_mul_self hlt
  rw [← pow_add, ← two_mul] at h3
  exact absurd hlow (not_le.mpr h3)

@[expose] noncomputable def normFix [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ (2 * m)) (c : F) :
    fixField F m :=
  ⟨c * c ^ 2 ^ m, by rw [mem_fixField, mul_pow, pow_pow_two_pow hF, mul_comm]⟩

theorem coe_normFix [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ (2 * m)) (c : F) :
    (normFix hF c : F) = c * c ^ 2 ^ m := rfl

end FixField

variable {G : Type} [Group G]

section Sylow

variable {L T V : Subgroup G} {F : Type} [Field F]

theorem exists_mem_borel_of_sylow [Finite G] (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F))
    (hP : ∀ x : ↥(autOn L V), (x : MulAut ↥V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T) {c : F} (hc0 : c ≠ 0) :
    ∃ (g : G) (hg : g ∈ borelL T L),
      (ψ (autHom hLV ⟨g, hg.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 = c := by
  obtain ⟨g', hg'L, hg'⟩ := mem_autOn_iff.mp (ψ.symm (Vol2.Ch10.SecA.diagSL hc0)).2
  set g : G := (g' : G) with hgdef
  have hψg : ψ (autHom hLV ⟨g, hg'L⟩) = Vol2.Ch10.SecA.diagSL hc0 := by
    have : autHom hLV ⟨g, hg'L⟩ = ψ.symm (Vol2.Ch10.SecA.diagSL hc0) := Subtype.ext hg'
    rw [this, MulEquiv.apply_symm_apply]
  have hgN : g ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_mem fun s hs => ?_
    have hsL : s ∈ L := (Subgroup.mem_inf.mp hs).2
    have hgs : g * s * g⁻¹ ∈ L := L.mul_mem (L.mul_mem hg'L hsL) (L.inv_mem hg'L)
    refine Subgroup.mem_inf.mpr ⟨?_, hgs⟩
    have hsS : ((autHom hLV ⟨s, hsL⟩ : ↥(autOn L V)) : MulAut ↥V) ∈ autOn (T ⊓ L) V :=
      mem_autOn_iff.mpr ⟨⟨s, hLV hsL⟩, hs, rfl⟩
    obtain ⟨b, hb⟩ := (hP _).mp hsS
    have hgsb : ψ (autHom hLV ⟨g * s * g⁻¹, hgs⟩) = unipSL (c ^ 2 * b) := by
      have : (autHom hLV ⟨g * s * g⁻¹, hgs⟩ : ↥(autOn L V)) =
          autHom hLV ⟨g, hg'L⟩ * autHom hLV ⟨s, hsL⟩ * (autHom hLV ⟨g, hg'L⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [this, map_mul, map_mul, map_inv, hψg, hb, Vol2.Ch10.SecA.diagSL_conj]
    have hmem : ((autHom hLV ⟨g * s * g⁻¹, hgs⟩ : ↥(autOn L V)) : MulAut ↥V) ∈
        autOn (T ⊓ L) V := (hP _).mpr ⟨_, hgsb⟩
    exact mem_of_conjAct_mem_autOn hC ⟨g * s * g⁻¹, hLV hgs⟩ (Subgroup.mem_sup_left hgs) hmem
  refine ⟨g, Subgroup.mem_inf.mpr ⟨hg'L, hgN⟩, ?_⟩
  rw [hψg, Vol2.Ch10.SecA.coe_diagSL]
  simp

theorem exists_mem_D_of_sylow [Finite G] {D : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (ψ : ↥(autOn L V) ≃* SL(2, F))
    (hP : ∀ x : ↥(autOn L V), (x : MulAut ↥V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T) (hS : IsSylowTwoOf (T ⊓ L) L)
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) {c : F} (hc0 : c ≠ 0) :
    ∃ (δ : G) (hδ : δ ∈ D),
      (ψ (autHom hLV ⟨δ, (Subgroup.mem_inf.mp (hD.1 hδ)).1⟩) :
        Matrix (Fin 2) (Fin 2) F) 0 0 = c := by
  obtain ⟨g, hg, hgc⟩ := exists_mem_borel_of_sylow hLV ψ hP hC hc0
  have hSB : IsSylowTwoOf (T ⊓ L) (borelL T L) :=
    A4.isSylowTwoOf_mono hS (Hyp5_0_1.inf_le_borel T L) inf_le_left
  have hB : D ⊔ (T ⊓ L) = borelL T L := sup_eq_of_isHall_isSylow hD hSB
  have hDN : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    hD.1.trans inf_le_right
  have hgmem : g ∈ ((D ⊔ (T ⊓ L) : Subgroup G) : Set G) := by
    rw [hB]
    exact hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D (T ⊓ L) hDN] at hgmem
  obtain ⟨δ, hδ, s, hs, rfl⟩ := hgmem
  refine ⟨δ, hδ, ?_⟩
  have hδL : δ ∈ L := (Subgroup.mem_inf.mp (hD.1 hδ)).1
  have hδN : δ ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := hDN hδ
  have hsL : s ∈ L := (Subgroup.mem_inf.mp hs).2
  have hsN : s ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hs
  have hmul : (autHom hLV ⟨δ * s, (Subgroup.mem_inf.mp hg).1⟩ : ↥(autOn L V)) =
      autHom hLV ⟨δ, hδL⟩ * autHom hLV ⟨s, hsL⟩ := by
    rw [← map_mul]
    rfl
  have hsS : ((autHom hLV ⟨s, hsL⟩ : ↥(autOn L V)) : MulAut ↥V) ∈ autOn (T ⊓ L) V :=
    mem_autOn_iff.mpr ⟨⟨s, hLV hsL⟩, hs, rfl⟩
  obtain ⟨b, hb⟩ := (hP _).mp hsS
  have hδu : (ψ (autHom hLV ⟨δ, hδL⟩) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    upper_of_mem_normalizer ψ hP _ (conjAct_mem_normalizer_autOn ⟨δ, hLV hδL⟩ hδN)
  have hsu : (ψ (autHom hLV ⟨s, hsL⟩) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    upper_of_mem_normalizer ψ hP _ (conjAct_mem_normalizer_autOn ⟨s, hLV hsL⟩ hsN)
  have h1 := (upper_mul hδu hsu).2
  rw [← map_mul, ← hmul, hgc, hb, coe_unipSL] at h1
  simpa using h1.symm

end Sylow

namespace Setting516

variable {T L D R : Subgroup G}

theorem exists_mul_of_mem_borel [Finite G] (hS : Setting516 T L D R) {b : G}
    (hb : b ∈ borelL T L) : ∃ δ ∈ D, ∃ s ∈ T ⊓ L, δ * s = b := by
  have hB : D ⊔ (T ⊓ L) = borelL T L := sup_eq_of_isHall_isSylow hS.hall
    (A4.isSylowTwoOf_mono hS.sylow (Hyp5_0_1.inf_le_borel T L) inf_le_left)
  have hb' : b ∈ ((D ⊔ (T ⊓ L) : Subgroup G) : Set G) := by
    rw [hB]
    exact hb
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D (T ⊓ L)
    (hS.hall.1.trans inf_le_right)] at hb'
  obtain ⟨δ, hδ, s, hs, rfl⟩ := hb'
  exact ⟨δ, hδ, s, hs, rfl⟩

theorem T_le_normalizer_inf (hS : Setting516 T L D R) :
    T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hS.le_normalizer ht⟩

theorem T_le_normalizer_borel (hS : Setting516 T L D R) :
    T ≤ Subgroup.normalizer ((borelL T L : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hS.le_normalizer ht,
    mem_normalizer_normalizer (hS.T_le_normalizer_inf ht)⟩

end Setting516

structure OrthCtx (T L D R : Subgroup G) (m : ℕ) (F : Type) [Field F] [CharP F 2]
    (ψ : ↥(autOn L R) ≃* SL(2, F)) (Y : ↥R →* Multiplicative (Matrix (Fin 2) (Fin 2) F)) :
    Prop where
  setting : Setting516 T L D R
  one_le : 1 ≤ m
  card : Nat.card F = 2 ^ (2 * m)
  le_normalizer : L ≤ Subgroup.normalizer (R : Set G)
  inj : Function.Injective Y
  herm : ∀ w, (frobPow m (Multiplicative.toAdd (Y w)))ᵀ = Multiplicative.toAdd (Y w)
  surj : ∀ X : Matrix (Fin 2) (Fin 2) F, (frobPow m X)ᵀ = X →
    ∃ w, Multiplicative.toAdd (Y w) = X
  intertwine : ∀ (x : ↥(autOn L R)) (w : ↥R), Multiplicative.toAdd (Y ((x : MulAut ↥R) w)) =
    (ψ x : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (Y w) *
      (frobPow m (ψ x : Matrix (Fin 2) (Fin 2) F))ᵀ
  sylow : ∀ x : ↥(autOn L R), (x : MulAut ↥R) ∈ autOn (T ⊓ L) R ↔ ∃ b : F, ψ x = unipSL b
  line : ∀ v : ↥R, (v : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) →
    (Multiplicative.toAdd (Y v)) 0 1 = 0 ∧ (Multiplicative.toAdd (Y v)) 1 0 = 0 ∧
      (Multiplicative.toAdd (Y v)) 1 1 = 0

theorem Setting516.exists_orthCtx [Finite G] {T L D R : Subgroup G} {m : ℕ}
    (hS : Setting516 T L D R) (hR : IsOrthCh5 L R (2 * m)) (hm : 1 ≤ m) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (ψ : ↥(autOn L R) ≃* SL(2, F))
      (Y : ↥R →* Multiplicative (Matrix (Fin 2) (Fin 2) F)), OrthCtx T L D R m F ψ Y := by
  obtain ⟨F, _, _, _, hF, ψ, Y, hYinj, hYherm, hYsurj, hYint, hP, hline, -⟩ :=
    hR.exists_lineCoord hS.sylow
  exact ⟨F, inferInstance, inferInstance, inferInstance, ψ, Y,
    ⟨hS, hm, hF, hR.le_normalizer, hYinj, hYherm, hYsurj, hYint, hP, hline⟩⟩

namespace OrthCtx

variable {T L D R : Subgroup G} {m : ℕ} {F : Type} [Field F] [CharP F 2]
  {ψ : ↥(autOn L R) ≃* SL(2, F)} {Y : ↥R →* Multiplicative (Matrix (Fin 2) (Fin 2) F)}

abbrev U (_h : OrthCtx T L D R m F ψ Y) : Subgroup G :=
  R ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)

variable (h : OrthCtx T L D R m F ψ Y)
include h

theorem upper {b : G} (hb : b ∈ borelL T L) :
    (ψ (autHom h.le_normalizer ⟨b, hb.1⟩) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  upper_of_mem_normalizer ψ h.sylow _ (conjAct_mem_normalizer_autOn ⟨b, h.le_normalizer hb.1⟩ hb.2)

theorem entry_ne_zero {b : G} (hb : b ∈ borelL T L) :
    (ψ (autHom h.le_normalizer ⟨b, hb.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 :=
  left_ne_zero_of_mul_eq_one (upper_det (h.upper hb))

@[expose] noncomputable def chiB (h : OrthCtx T L D R m F ψ Y) : ↥(borelL T L) →* Fˣ where
  toFun b := Units.mk0 ((ψ (autHom h.le_normalizer ⟨b, b.2.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h.entry_ne_zero b.2)
  map_one' := by
    apply Units.ext
    rw [Units.val_mk0, Units.val_one]
    rw [show (⟨((1 : ↥(borelL T L)) : G), (1 : ↥(borelL T L)).2.1⟩ : ↥L) = 1 from rfl, map_one,
      map_one]
    simp
  map_mul' a b := by
    apply Units.ext
    rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0]
    rw [show (⟨((a * b : ↥(borelL T L)) : G), (a * b).2.1⟩ : ↥L) = ⟨a, a.2.1⟩ * ⟨b, b.2.1⟩ from
      rfl, map_mul, map_mul]
    exact (upper_mul (h.upper a.2) (h.upper b.2)).2

theorem coe_chiB (b : ↥(borelL T L)) :
    (h.chiB b : F) = (ψ (autHom h.le_normalizer ⟨b, b.2.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 :=
  rfl

theorem chiB_eq_one_of_mem {s : G} (hs : s ∈ T ⊓ L) (hsB : s ∈ borelL T L) :
    h.chiB ⟨s, hsB⟩ = 1 := by
  apply Units.ext
  rw [coe_chiB, Units.val_one]
  have hsS : ((autHom h.le_normalizer ⟨s, hsB.1⟩ : ↥(autOn L R)) : MulAut ↥R) ∈
      autOn (T ⊓ L) R := mem_autOn_iff.mpr ⟨⟨s, h.le_normalizer hsB.1⟩, hs, rfl⟩
  obtain ⟨b, hb⟩ := (h.sylow _).mp hsS
  rw [hb, coe_unipSL]
  simp

theorem eq_one_of_mem_D [Finite G] {δ : G} (hδ : δ ∈ D)
    (h1 : h.chiB ⟨δ, h.setting.hall.1 hδ⟩ = 1) : δ = 1 := by
  have hδB := h.setting.hall.1 hδ
  have h00 : (ψ (autHom h.le_normalizer ⟨δ, hδB.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have := congrArg Units.val h1
    rwa [coe_chiB, Units.val_one] at this
  have hu := eq_unipSL_of_upper (h.upper hδB) h00
  have hmem : ((autHom h.le_normalizer ⟨δ, hδB.1⟩ : ↥(autOn L R)) : MulAut ↥R) ∈
      autOn (T ⊓ L) R := (h.sylow _).mpr ⟨_, hu⟩
  have hδT : δ ∈ T := mem_of_conjAct_mem_autOn h.setting.centralizer_le
    ⟨δ, h.le_normalizer hδB.1⟩ (Subgroup.mem_sup_left hδB.1) hmem
  exact eq_one_of_mem_of_odd h.setting.hall.2.1 h.setting.isPGroup hδ hδT

theorem exists_mem_D [Finite G] {c : F} (hc0 : c ≠ 0) :
    ∃ (δ : G) (hδ : δ ∈ D), (h.chiB ⟨δ, h.setting.hall.1 hδ⟩ : F) = c := by
  obtain ⟨δ, hδ, hδc⟩ := exists_mem_D_of_sylow h.le_normalizer ψ h.sylow
    h.setting.centralizer_le h.setting.sylow h.setting.hall hc0
  exact ⟨δ, hδ, hδc⟩

theorem mem_of_chiB_pow [Finite G] {Dp : Subgroup G} (hDp : Dp ≤ D)
    (hcard : Nat.card Dp = 2 ^ m - 1) {d : G} (hd : d ∈ D)
    (hd1 : h.chiB ⟨d, h.setting.hall.1 hd⟩ ^ (2 ^ m - 1) = 1) : d ∈ Dp := by
  have hm := h.one_le
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have : NeZero (2 ^ m - 1) := ⟨by omega⟩
  set χ : ↥D →* Fˣ := h.chiB.comp (Subgroup.inclusion h.setting.hall.1) with hχ
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro δ hδ
    exact Subtype.ext (h.eq_one_of_mem_D δ.2 hδ)
  set Z : Subgroup ↥D := (rootsOfUnity (2 ^ m - 1) F).comap χ with hZ
  have hZcard : Nat.card Z ≤ 2 ^ m - 1 :=
    calc Nat.card Z = Nat.card (Z.map χ) := (Subgroup.card_map_of_injective hinj).symm
      _ ≤ Nat.card (rootsOfUnity (2 ^ m - 1) F) :=
          Subgroup.card_le_of_le (Subgroup.map_comap_le _ _)
      _ ≤ 2 ^ m - 1 := card_rootsOfUnity F (2 ^ m - 1)
  have hle : Dp.subgroupOf D ≤ Z := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [hZ, Subgroup.mem_comap, mem_rootsOfUnity, ← map_pow]
    have hx1 : x ^ (2 ^ m - 1) = 1 := by
      have h1 : (⟨(x : G), hx⟩ : ↥Dp) ^ Nat.card Dp = 1 := pow_card_eq_one'
      rw [hcard] at h1
      exact Subtype.ext (by simpa using congrArg Subtype.val h1)
    rw [hx1, map_one]
  have hcardDp : Nat.card (Dp.subgroupOf D) = 2 ^ m - 1 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDp).toEquiv
  have heq : Dp.subgroupOf D = Z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardDp]; exact hZcard)
  have hdZ : (⟨d, hd⟩ : ↥D) ∈ Z := by
    rw [hZ, Subgroup.mem_comap, mem_rootsOfUnity]
    exact hd1
  rw [← heq, Subgroup.mem_subgroupOf] at hdZ
  exact hdZ

theorem chiB_pow_of_mem [Finite G] {Dp : Subgroup G} (hDp : Dp ≤ D)
    (hcard : Nat.card Dp = 2 ^ m - 1) {d : G} (hd : d ∈ Dp) :
    h.chiB ⟨d, h.setting.hall.1 (hDp hd)⟩ ^ (2 ^ m - 1) = 1 := by
  have h1 : (⟨d, hd⟩ : ↥Dp) ^ Nat.card Dp = 1 := pow_card_eq_one'
  rw [hcard] at h1
  have h2 : d ^ (2 ^ m - 1) = 1 := by simpa using congrArg Subtype.val h1
  rw [← map_pow]
  have h3 : (⟨d, h.setting.hall.1 (hDp hd)⟩ : ↥(borelL T L)) ^ (2 ^ m - 1) = 1 :=
    Subtype.ext (by simpa using h2)
  rw [h3, map_one]

theorem normalizer_sup_Dp [Finite G] {Dp : Subgroup G} (hDp : Dp ≤ D)
    (hcard : Nat.card Dp = 2 ^ m - 1) {X : Subgroup G}
    (hXB : X ≤ Subgroup.normalizer ((borelL T L : Subgroup G) : Set G))
    (hXS : X ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) :
    X ≤ Subgroup.normalizer (((T ⊓ L) ⊔ Dp : Subgroup G) : Set G) := by
  intro x hx
  have hDpS : Dp ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    hDp.trans (h.setting.hall.1.trans inf_le_right)
  refine mem_normalizer_of_conj_mem fun g hg => ?_
  have hg' : g ∈ (((T ⊓ L) ⊔ Dp : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (T ⊓ L) Dp hDpS] at hg'
  obtain ⟨s, hs, δ, hδ, rfl⟩ := hg'
  have hδB : δ ∈ borelL T L := h.setting.hall.1 (hDp hδ)
  have hxδ : x * δ * x⁻¹ ∈ borelL T L := (Subgroup.mem_normalizer_iff.mp (hXB hx) δ).mp hδB
  obtain ⟨d, hd, s', hs', hds⟩ := h.setting.exists_mul_of_mem_borel hxδ
  have hdB : d ∈ borelL T L := h.setting.hall.1 hd
  have hs'B : s' ∈ borelL T L := Hyp5_0_1.inf_le_borel T L hs'
  have hcd : h.chiB ⟨d, hdB⟩ = h.chiB ⟨x * δ * x⁻¹, hxδ⟩ := by
    have e : (⟨x * δ * x⁻¹, hxδ⟩ : ↥(borelL T L)) = ⟨d, hdB⟩ * ⟨s', hs'B⟩ :=
      Subtype.ext hds.symm
    rw [e, map_mul, h.chiB_eq_one_of_mem hs' hs'B, mul_one]
  have hpow : h.chiB ⟨x * δ * x⁻¹, hxδ⟩ ^ (2 ^ m - 1) = 1 := by
    have h1 : (⟨δ, hδ⟩ : ↥Dp) ^ Nat.card Dp = 1 := pow_card_eq_one'
    rw [hcard] at h1
    have h2 : δ ^ (2 ^ m - 1) = 1 := by simpa using congrArg Subtype.val h1
    have h3 : (⟨x * δ * x⁻¹, hxδ⟩ : ↥(borelL T L)) ^ (2 ^ m - 1) = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, conj_pow, h2]
      simp
    rw [← map_pow, h3, map_one]
  have hdDp : d ∈ Dp := h.mem_of_chiB_pow hDp hcard hd (by rw [hcd]; exact hpow)
  have e : x * (s * δ) * x⁻¹ = (x * s * x⁻¹) * (d * s') := by
    rw [hds]
    group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hXS hx) s).mp hs))
    (mul_mem (Subgroup.mem_sup_right hdDp) (Subgroup.mem_sup_left hs'))

theorem entry_mem_fixField (w : ↥R) : (Multiplicative.toAdd (Y w)) 0 0 ∈ fixField F m := by
  rw [mem_fixField]
  have := congrFun (congrFun (h.herm w) 0) 0
  simpa [frobPow, Matrix.transpose_apply] using this

@[expose] noncomputable def coordHom (h : OrthCtx T L D R m F ψ Y) :
    ↥h.U →* Multiplicative (Fin 1 → fixField F m) where
  toFun w := Multiplicative.ofAdd fun _ =>
    ⟨(Multiplicative.toAdd (Y (Subgroup.inclusion inf_le_left w))) 0 0, h.entry_mem_fixField _⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext i
    apply Subtype.ext
    simp

theorem coe_coordHom (w : ↥h.U) (i : Fin 1) :
    ((Multiplicative.toAdd (h.coordHom w)) i : F) =
      (Multiplicative.toAdd (Y (Subgroup.inclusion inf_le_left w))) 0 0 := rfl

theorem coordHom_bijective : Function.Bijective h.coordHom := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro w hw
    have h0 : (Multiplicative.toAdd (Y (Subgroup.inclusion inf_le_left w))) 0 0 = 0 := by
      have := congrArg Subtype.val (congrFun (congrArg Multiplicative.toAdd hw) 0)
      rw [coe_coordHom] at this
      exact this
    obtain ⟨h01, h10, h11⟩ := h.line (Subgroup.inclusion inf_le_left w) w.2.2
    have hY : Y (Subgroup.inclusion inf_le_left w) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      exact mat2_ext (by rw [h0]; rfl) (by rw [h01]; rfl) (by rw [h10]; rfl) (by rw [h11]; rfl)
    have := h.inj (hY.trans (map_one Y).symm)
    exact Subtype.ext (congrArg (Subtype.val : ↥R → G) this)
  · intro v
    obtain ⟨a, ha⟩ : ∃ a : F, a = ((Multiplicative.toAdd v) 0 : F) := ⟨_, rfl⟩
    have haF : a ^ 2 ^ m = a := by
      rw [ha]
      exact mem_fixField.mp ((Multiplicative.toAdd v) 0).2
    have h0 : (0 : F) ^ 2 ^ m = 0 := zero_pow (by positivity)
    have hXh : (frobPow m !![a, 0; 0, 0])ᵀ = !![a, 0; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [frobPow, Matrix.transpose_apply, haF, h0]
    obtain ⟨w, hw⟩ := h.surj _ hXh
    have hwS : (w : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hsL : s ∈ L := (Subgroup.mem_inf.mp hs).2
      obtain ⟨b, hb⟩ := (h.sylow (autHom h.le_normalizer ⟨s, hsL⟩)).mp
        (mem_autOn_iff.mpr ⟨⟨s, h.le_normalizer hsL⟩, hs, rfl⟩)
      have h1 := h.intertwine (autHom h.le_normalizer ⟨s, hsL⟩) w
      rw [hb, hw] at h1
      have h2 : ((autHom h.le_normalizer ⟨s, hsL⟩ : ↥(autOn L R)) : MulAut ↥R) w = w := by
        apply h.inj
        apply Multiplicative.toAdd.injective
        rw [h1, hw]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [frobPow, coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
            h0]
      have h3 := congrArg Subtype.val h2
      rw [autHom_apply_coe] at h3
      calc s * w = s * w * s⁻¹ * s := by group
        _ = w * s := by rw [h3]
    refine ⟨⟨w, w.2, hwS⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    rw [Fin.fin_one_eq_zero i]
    apply Subtype.ext
    rw [coe_coordHom]
    have e : Subgroup.inclusion (inf_le_left : h.U ≤ R) ⟨(w : G), w.2, hwS⟩ = w := rfl
    rw [e, hw, ← ha]
    simp

@[expose] noncomputable def coord1 (h : OrthCtx T L D R m F ψ Y) :
    ↥h.U ≃* Multiplicative (Fin 1 → fixField F m) :=
  MulEquiv.ofBijective h.coordHom h.coordHom_bijective

theorem coe_coord1 (w : ↥h.U) (i : Fin 1) :
    ((Multiplicative.toAdd (h.coord1 w)) i : F) =
      (Multiplicative.toAdd (Y (Subgroup.inclusion inf_le_left w))) 0 0 := rfl

theorem card_U [Finite F] : Nat.card h.U = 2 ^ m := by
  rw [Nat.card_congr h.coord1.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp [card_fixField h.one_le h.card]

theorem borel_le_normalizer_U : borelL T L ≤ Subgroup.normalizer (h.U : Set G) := fun _ hb =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨h.le_normalizer (Subgroup.mem_inf.mp hb).1,
    F7.normalizer_le_normalizer_centralizer _ (Subgroup.mem_inf.mp hb).2⟩

theorem T_le_normalizer_U : T ≤ Subgroup.normalizer (h.U : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨h.setting.reduced.2.1 (Subgroup.mem_sup_right ht),
    F7.normalizer_le_normalizer_centralizer _ (h.setting.T_le_normalizer_inf ht)⟩

theorem act_eq_smul [Finite F] {b : G} (hb : b ∈ borelL T L) (x : Fin 1 → fixField F m) :
    Semi516.act h.coord1 b (h.borel_le_normalizer_U hb) x =
      normFix h.card (h.chiB ⟨b, hb⟩ : F) • x := by
  rw [Semi516.act, Semi516.coordPerm_apply]
  obtain ⟨w, hw⟩ : ∃ w, w = h.coord1.symm (Multiplicative.ofAdd x) := ⟨_, rfl⟩
  rw [← hw]
  have hx0 : (Multiplicative.toAdd (Y (Subgroup.inclusion inf_le_left w))) 0 0 = (x 0 : F) := by
    have h1 : Multiplicative.toAdd (h.coord1 w) = x := by
      rw [hw, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have := congrArg Subtype.val (congrFun h1 0)
    rwa [coe_coord1] at this
  have hconj : Subgroup.inclusion (inf_le_left : h.U ≤ R)
      (conjAct h.U ⟨b, h.borel_le_normalizer_U hb⟩ w) =
      ((autHom h.le_normalizer ⟨b, hb.1⟩ : ↥(autOn L R)) : MulAut ↥R)
        (Subgroup.inclusion inf_le_left w) := by
    apply Subtype.ext
    rw [autHom_apply_coe]
    exact conjAct_apply_coe _ _
  obtain ⟨h01, h10, h11⟩ := h.line (Subgroup.inclusion inf_le_left w) w.2.2
  have ht := (twist_upper m (h.upper hb) h01 h10 h11).1
  rw [← h.intertwine] at ht
  funext i
  rw [Fin.fin_one_eq_zero i]
  apply Subtype.ext
  rw [coe_coord1, hconj, ht, hx0, Pi.smul_apply, smul_eq_mul, Subfield.coe_mul, coe_normFix,
    coe_chiB]
  ring

theorem exists_mem_D_smul [Finite G] [Finite F] {a : fixField F m} (ha : a ≠ 0) :
    ∃ (δ : G) (hδ : δ ∈ D), ∀ x, Semi516.act h.coord1 δ
      (h.borel_le_normalizer_U (h.setting.hall.1 hδ)) x = a • x := by
  have ha0 : (a : F) ≠ 0 := fun h0 => ha (Subtype.ext h0)
  obtain ⟨c, hc0, hc⟩ := exists_pow_add_one_eq h.card ha0 (mem_fixField.mp a.2)
  obtain ⟨δ, hδ, hδc⟩ := h.exists_mem_D hc0
  refine ⟨δ, hδ, fun x => ?_⟩
  rw [h.act_eq_smul (h.setting.hall.1 hδ), hδc]
  congr 1
  apply Subtype.ext
  rw [coe_normFix, ← hc, pow_succ, mul_comm]

theorem semilinear_T [Finite G] [Finite F] {t : G} (ht : t ∈ T) :
    ∃ σ : fixField F m ≃+* fixField F m,
      IsSemilinearWith (Semi516.act h.coord1 t (h.T_le_normalizer_U ht)) σ := by
  refine Semi516.exists_isSemilinearWith_of_conj_smul _ (Semi516.act_add _ _) fun c => ?_
  by_cases hc : c = 0
  · refine ⟨0, fun x => ?_⟩
    rw [hc, zero_smul, zero_smul, Semi516.act_zero]
  · obtain ⟨δ, hδ, hδc⟩ := h.exists_mem_D_smul hc
    have hδB := h.setting.hall.1 hδ
    have hb : t * δ * t⁻¹ ∈ borelL T L :=
      (Subgroup.mem_normalizer_iff.mp (h.setting.T_le_normalizer_borel ht) δ).mp hδB
    refine ⟨normFix h.card (h.chiB ⟨t * δ * t⁻¹, hb⟩ : F), fun x => ?_⟩
    have e1 : Semi516.act h.coord1 (t * δ * t⁻¹) (h.borel_le_normalizer_U hb) =
        Semi516.act h.coord1 t (h.T_le_normalizer_U ht) *
          Semi516.act h.coord1 δ (h.borel_le_normalizer_U hδB) *
            (Semi516.act h.coord1 t (h.T_le_normalizer_U ht))⁻¹ := by
      rw [← Semi516.act_inv h.coord1 (h.T_le_normalizer_U ht),
        ← Semi516.act_mul h.coord1 (h.T_le_normalizer_U ht) (h.borel_le_normalizer_U hδB),
        ← Semi516.act_mul h.coord1
          (Subgroup.mul_mem _ (h.T_le_normalizer_U ht) (h.borel_le_normalizer_U hδB))
          (Subgroup.inv_mem _ (h.T_le_normalizer_U ht))]
    rw [← hδc, ← h.act_eq_smul hb x, e1]
    rfl

theorem T_le_centralizer_of_odd [Finite G] [Finite F] (hm : Odd m) :
    T ≤ Subgroup.centralizer (h.U : Set G) := by
  intro t ht
  obtain ⟨σ, hσ⟩ := h.semilinear_T ht
  obtain ⟨k, hk⟩ := h.setting.isPGroup ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set p := Semi516.act h.coord1 t (h.T_le_normalizer_U ht) with hp
  have hpow : ∀ j : ℕ, IsSemilinearWith (p ^ j) (σ ^ j) := by
    intro j
    induction j with
    | zero =>
      intro c x
      simp only [pow_zero]
      rfl
    | succ j ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul hσ
  have hp1 : p ^ 2 ^ k = 1 := by
    rw [hp, ← Semi516.act_pow h.coord1 (h.T_le_normalizer_U ht)]
    exact (Semi516.act_eq_one_iff _ _).mpr (by rw [htk]; exact Subgroup.one_mem _)
  have hσk : σ ^ 2 ^ k = 1 := by
    have h1 := hpow (2 ^ k)
    rw [hp1] at h1
    refine RingEquiv.ext fun c => ?_
    have h2 := congrFun (h1 c (fun _ => 1)) 0
    simp only [Equiv.Perm.one_apply, Pi.smul_apply, smul_eq_mul, mul_one] at h2
    exact h2.symm
  have hcardF₀ := card_fixField h.one_le h.card
  have hcardAut : Nat.card (RingAut (fixField F m)) = m :=
    (ringAut_card_and_cyclic hcardF₀).1
  have : Finite (RingAut (fixField F m)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; exact hm.pos.ne')
  have hσm : σ ^ m = 1 := by
    have h1 : σ ^ Nat.card (RingAut (fixField F m)) = 1 := pow_card_eq_one'
    rwa [hcardAut] at h1
  have hσ1 : σ = 1 := by
    have hg : σ ^ Nat.gcd (2 ^ k) m = 1 := pow_gcd_eq_one.mpr ⟨hσk, hσm⟩
    have hcop : Nat.gcd (2 ^ k) m = 1 := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
    rwa [hcop, pow_one] at hg
  subst hσ1
  exact Semi516.mem_centralizer_of_linear_line h.coord1 _ htk hσ

theorem hyp [Finite G] [Finite F] {Dp : Subgroup G} (hDp : Dp ≤ D)
    (hcard : Nat.card Dp = 2 ^ m - 1) (hm2 : 2 ≤ m) :
    Semi516.Hyp h.coord1 T ((T ⊓ L) ⊔ Dp) Dp := by
  have hDpS : Dp ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    hDp.trans (h.setting.hall.1.trans inf_le_right)
  have hBp : (T ⊓ L) ⊔ Dp ≤ borelL T L :=
    sup_le (Hyp5_0_1.inf_le_borel T L) (hDp.trans h.setting.hall.1)
  have hTBp : T ≤ Subgroup.normalizer (((T ⊓ L) ⊔ Dp : Subgroup G) : Set G) :=
    h.normalizer_sup_Dp hDp hcard h.setting.T_le_normalizer_borel h.setting.T_le_normalizer_inf
  have h2m : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  refine
    { one_le := le_rfl
      isPGroup := h.setting.isPGroup
      odd := ?_
      le_T := inf_le_left.trans h.setting.le_T
      T_le := h.T_le_normalizer_U
      B_le := hBp.trans h.borel_le_normalizer_U
      T_le_B := hTBp
      D_le := le_sup_right
      decomp := ?_
      scalar := fun b hb => ⟨_, h.act_eq_smul (hBp hb)⟩
      surj := ?_
      linear := ?_
      faithful := ?_ }
  · rw [hcard]
    exact Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  · intro x hx
    have hx' : x ∈ ((T ⊔ ((T ⊓ L) ⊔ Dp) : Subgroup G) : Set G) :=
      sup_le_sup_left (le_sup_right : Dp ≤ (T ⊓ L) ⊔ Dp) T hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T _ hTBp] at hx'
    obtain ⟨t, ht, b, hb, rfl⟩ := hx'
    have hb' : b ∈ (((T ⊓ L) ⊔ Dp : Subgroup G) : Set G) := hb
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (T ⊓ L) Dp hDpS] at hb'
    obtain ⟨s, hs, δ, hδ, rfl⟩ := hb'
    exact ⟨t * s, T.mul_mem ht (Subgroup.mem_inf.mp hs).1, δ, hδ, by group⟩
  ·
    intro a ha
    obtain ⟨k, hk⟩ := isSquare_of_charTwo' a
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact ha (by rw [hk, mul_zero])
    have hk0' : (k : F) ≠ 0 := fun h0 => hk0 (Subtype.ext h0)
    obtain ⟨c, hc0, hc⟩ := exists_pow_add_one_eq h.card hk0' (mem_fixField.mp k.2)
    obtain ⟨δ, hδ, hδc⟩ := h.exists_mem_D hc0
    have hδB := h.setting.hall.1 hδ
    have hδpB : δ ^ (2 ^ m + 1) ∈ borelL T L := Subgroup.pow_mem _ hδB _
    have hchi : (h.chiB ⟨δ ^ (2 ^ m + 1), hδpB⟩ : F) = k := by
      have e : (⟨δ ^ (2 ^ m + 1), hδpB⟩ : ↥(borelL T L)) = ⟨δ, hδB⟩ ^ (2 ^ m + 1) :=
        Subtype.ext (by simp)
      rw [e, map_pow, Units.val_pow_eq_pow_val, hδc, hc]
    have hδDp : δ ^ (2 ^ m + 1) ∈ Dp := by
      refine h.mem_of_chiB_pow hDp hcard (Subgroup.pow_mem _ hδ _) ?_
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hchi, Units.val_one]
      have hkF : (k : F) ^ 2 ^ m = k := mem_fixField.mp k.2
      have h1 : (k : F) ^ (2 ^ m - 1) * k = k := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), hkF]
      exact mul_right_cancel₀ hk0' (h1.trans (one_mul _).symm)
    refine ⟨δ ^ (2 ^ m + 1), hδDp, fun x => ?_⟩
    rw [h.act_eq_smul hδpB, hchi]
    congr 1
    apply Subtype.ext
    rw [coe_normFix, mem_fixField.mp k.2, hk, Subfield.coe_mul]
  · intro t ht hlin
    obtain ⟨k, hk⟩ := h.setting.isPGroup ⟨t, ht⟩
    have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Semi516.mem_centralizer_of_linear_line h.coord1 (h.T_le_normalizer_U ht) htk hlin
  · rw [eq_bot_iff]
    intro δ hδ
    obtain ⟨hδD, hδC⟩ := Subgroup.mem_inf.mp hδ
    rw [Subgroup.mem_bot]
    have hδB := h.setting.hall.1 (hDp hδD)
    have h1 : Semi516.act h.coord1 δ (h.borel_le_normalizer_U hδB) = 1 :=
      (Semi516.act_eq_one_iff _ _).mpr hδC
    have h2 := h.act_eq_smul hδB (fun _ => 1)
    rw [h1, Equiv.Perm.one_apply] at h2
    have h3 := congrArg Subtype.val (congrFun h2 0)
    simp only [Pi.smul_apply, smul_eq_mul, mul_one, OneMemClass.coe_one, coe_normFix] at h3
    obtain ⟨c, hc⟩ : ∃ c : F, c = (h.chiB ⟨δ, hδB⟩ : F) := ⟨_, rfl⟩
    rw [← hc] at h3
    have hp : c ^ (2 ^ m - 1) = 1 := by
      have h4 := congrArg Units.val (h.chiB_pow_of_mem hDp hcard hδD)
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h4
      rw [hc]
      exact h4
    have hcF : c ^ 2 ^ m = c := by
      calc c ^ 2 ^ m = c ^ (2 ^ m - 1) * c := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        _ = c := by rw [hp, one_mul]
    rw [hcF] at h3
    have hc1 : c = 1 := by
      have h5 : c ^ 2 = 1 ^ 2 := by rw [sq, one_pow]; exact h3.symm
      exact CharTwo.sq_inj.mp h5
    exact h.eq_one_of_mem_D (hDp hδD)
      (Units.ext (by rw [Units.val_one]; exact hc.symm.trans hc1))

theorem le_four [Finite G] [Finite F] {Dp : Subgroup G} (hDp : Dp ≤ D)
    (hcard : Nat.card Dp = 2 ^ m - 1) (hm2 : 2 ≤ m) (hW : IsElemAbelian 2 h.U)
    (hq : qhatInt (T ⊔ Dp) h.U hW ≤ 2) : m ≤ 4 := by
  by_contra hn
  push Not at hn
  have h16 : 16 < Nat.card h.U := by
    rw [h.card_U]
    calc 16 < 2 ^ 5 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hn
  exact absurd hq (not_le.mpr ((h.hyp hDp hcard hm2).two_lt_qhatInt hW h16))

end OrthCtx

theorem fact516Orth : Fact516Orth := by
  intro G _ _ T L D R m hS hR hm
  obtain ⟨F, _, _, _, ψ, Y, h⟩ := hS.exists_orthCtx hR hm
  exact ⟨h.card_U, fun hodd => h.T_le_centralizer_of_odd hodd, fun Dp hDp hcard hm2 =>
    ⟨fun X hXB hXS => h.normalizer_sup_Dp hDp hcard hXB hXS, (h.hyp hDp hcard hm2).isTDMod,
      fun hW hq => h.le_four hDp hcard hm2 hW hq⟩⟩

end CFSG.Quasithin.H13
