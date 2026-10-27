module

public import CFSG.Quasithin.H13.AS91Sec4EightB
public import CFSG.LargeExtraspecial.DW3Main
public import CFSG.Quasithin.Vol2.Asc94.L52Hstruct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour
open scoped Pointwise

namespace Two

theorem tOK48_spec :
    (∀ A ∈ pbar (), A ∈ s48 ()) ∧ (∀ g ∈ d7Gens, ok7 g = true) ∧ id7 ∈ enum7 d7Gens ∧
      (∀ x ∈ enum7 d7Gens, ∀ g ∈ d7Gens, mul7 x g ∈ enum7 d7Gens) ∧
      (enum7 d7Gens).dedup.length = 64 ∧ (∀ x ∈ enum7 d7Gens, x ∈ t7List ()) ∧
      (∀ x ∈ enum7 d7Gens, x ∈ b7List () → x = id7) ∧
      (∀ g ∈ r7Gens, ok7 g = true) ∧ id7 ∈ enum7 r7Gens ∧
      (∀ x ∈ enum7 r7Gens, ∀ g ∈ r7Gens, mul7 x g ∈ enum7 r7Gens) ∧
      (enum7 r7Gens).dedup.length = 64 ∧ (∀ x ∈ enum7 r7Gens, x ∈ t7List ()) ∧
      (∀ x ∈ enum7 r7Gens, ∀ y ∈ enum7 r7Gens, mul7 x y = mul7 y x) ∧
      (∀ x ∈ enum7 r7Gens, mul7 x x = id7) := by
  have h := ok48_parts.2.2.2.2.1
  simp only [tOK48, closed7, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    List.contains_iff_mem, Std.HashSet.contains_ofList, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, -⟩, -⟩, -⟩ := h
  refine ⟨fun A hA => (h1 A hA).2, h4, h5, h6, h7, h8, fun x hx hB => ?_, h10, h11, h12, h13,
    h14, h15, h16⟩
  rcases h9 x hx with h' | h'
  · exact absurd (List.contains_iff_mem.mpr hB) (by rw [h']; decide)
  · exact h'

theorem app7_id7 : ∀ n < 128, app7 id7 n = n := by decide

theorem mul7_id7 {X : Array ℕ} (hX : ok7 X = true) : mul7 id7 X = X := by
  simp only [ok7, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at hX
  apply Array.ext
  · simp [mul7]
  · intro i h1 h2
    simp only [mul7, Array.getElem_map]
    exact app7_id7 _ (hX.2 i h2)

theorem mem_enum7_of_mem_gens {gs : List (Array ℕ)} (hok : ∀ g ∈ gs, ok7 g = true)
    (hid : id7 ∈ enum7 gs) (hcl : ∀ x ∈ enum7 gs, ∀ g ∈ gs, mul7 x g ∈ enum7 gs) {g : Array ℕ}
    (hg : g ∈ gs) : g ∈ enum7 gs := by
  have := hcl id7 hid g hg
  rwa [mul7_id7 (hok g hg)] at this

theorem t7List_sub_c3List {X : Array ℕ} (hX : X ∈ t7List ()) :
    X ∈ c3List () := by
  simp only [t7List, List.mem_flatMap, List.mem_map, List.mem_range] at hX
  obtain ⟨A, hA, l, hl, rfl⟩ := hX
  exact mem_c3List.mpr ⟨A, tOK48_spec.1 A hA, l, hl, rfl⟩

theorem d7Gens_sub : ∀ g ∈ d7Gens, g ∈ c3List () := fun g hg => by
  obtain ⟨-, hok, hid, hcl, -, hT, -⟩ := tOK48_spec
  exact t7List_sub_c3List (hT g (mem_enum7_of_mem_gens hok hid hcl hg))

end Two

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

section Gen

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

@[expose] noncomputable def ofC3 (X : Array ℕ) : ↥D.Mb := by
  classical
  exact if hX : ∃ φ ∈ D.C3, D.kap (φ : MulAut ↥D.E) = X then hX.choose else 1

include hOut hTw hHat

theorem ofC3_spec {X : Array ℕ} (hX : X ∈ Two.c3List ()) :
    D.ofC3 X ∈ D.C3 ∧ D.kap (D.ofC3 X : MulAut ↥D.E) = X := by
  have hex := D.exists_of_mem_c3List hOut hTw hHat hX
  unfold ofC3
  rw [dif_pos hex]
  exact hex.choose_spec

@[expose] noncomputable def genC3 (gs : List (Array ℕ)) : Subgroup ↥D.Mb :=
  closure (Set.range fun g : {g // g ∈ gs} => D.ofC3 (g : Array ℕ))

theorem genC3_spec {gs : List (Array ℕ)} (hgs : ∀ g ∈ gs, g ∈ Two.c3List ())
    (hid : Two.id7 ∈ Two.enum7 gs)
    (hcl : ∀ x ∈ Two.enum7 gs, ∀ g ∈ gs, Two.mul7 x g ∈ Two.enum7 gs) :
    (∀ φ ∈ D.genC3 gs, φ ∈ D.C3 ∧ D.kap (φ : MulAut ↥D.E) ∈ Two.enum7 gs) ∧
      ∀ X ∈ Two.enum7 gs, ∃ φ ∈ D.genC3 gs, D.kap (φ : MulAut ↥D.E) = X := by
  constructor
  · intro φ hφ
    have hφ' : φ ∈ Submonoid.closure (Set.range fun g : {g // g ∈ gs} => D.ofC3 (g : Array ℕ)) := by
      rw [← Subgroup.closure_toSubmonoid_of_finite]
      exact hφ
    refine Submonoid.closure_induction_right ?_ ?_ hφ'
    · refine ⟨one_mem _, ?_⟩
      rw [Subgroup.coe_one, D.kap_one]
      exact hid
    · rintro x - _ ⟨g, rfl⟩ ⟨hxC, hxk⟩
      obtain ⟨hgC, hgk⟩ := D.ofC3_spec hOut hTw hHat (hgs g g.2)
      refine ⟨mul_mem hxC hgC, ?_⟩
      rw [Subgroup.coe_mul, D.kap_mul (D.presE1_of_mem_Mz hOut hTw hxC.1)
        (D.presE1_of_mem_Mz hOut hTw hgC.1), hgk]
      exact hcl _ hxk g g.2
  · intro X hX
    refine bfsClosure_inv (P := fun X => ∃ φ ∈ D.genC3 gs, D.kap (φ : MulAut ↥D.E) = X)
      (fun x : Array ℕ => x) _ ?_ _ _ _ _ ?_ (by simp) X hX
    · intro f hf Y ⟨φ, hφ, hφY⟩
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      obtain ⟨hgC, hgk⟩ := D.ofC3_spec hOut hTw hHat (hgs g hg)
      have hφC : φ ∈ D.C3 := by
        have hφ' : φ ∈ Submonoid.closure
            (Set.range fun g : {g // g ∈ gs} => D.ofC3 (g : Array ℕ)) := by
          rw [← Subgroup.closure_toSubmonoid_of_finite]
          exact hφ
        refine Submonoid.closure_induction_right (one_mem _) ?_ hφ'
        rintro x - _ ⟨g', rfl⟩ hx
        exact mul_mem hx (D.ofC3_spec hOut hTw hHat (hgs g' g'.2)).1
      refine ⟨φ * D.ofC3 g, mul_mem hφ (subset_closure ⟨⟨g, hg⟩, rfl⟩), ?_⟩
      rw [Subgroup.coe_mul, D.kap_mul (D.presE1_of_mem_Mz hOut hTw hφC.1)
        (D.presE1_of_mem_Mz hOut hTw hgC.1), hgk, hφY]
    · simp only [List.mem_singleton, forall_eq]
      exact ⟨1, one_mem _, by rw [Subgroup.coe_one, D.kap_one]⟩

theorem card_genC3 {gs : List (Array ℕ)} (hgs : ∀ g ∈ gs, g ∈ Two.c3List ())
    (hid : Two.id7 ∈ Two.enum7 gs)
    (hcl : ∀ x ∈ Two.enum7 gs, ∀ g ∈ gs, Two.mul7 x g ∈ Two.enum7 gs) :
    Nat.card (D.genC3 gs) = (Two.enum7 gs).dedup.length := by
  obtain ⟨h1, h2⟩ := D.genC3_spec hOut hTw hHat hgs hid hcl
  let f : ↥(D.genC3 gs) → ↥(Two.enum7 gs).toFinset := fun φ =>
    ⟨D.kap ((φ : ↥D.Mb) : MulAut ↥D.E), List.mem_toFinset.mpr (h1 φ φ.2).2⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun φ ψ hφψ => Subtype.ext (D.eq_of_kap_eq hOut hTw hHat (h1 φ φ.2).1.1
      (h1 ψ ψ.2).1.1 (congrArg Subtype.val hφψ)), fun X => ?_⟩
    obtain ⟨φ, hφ, hX⟩ := h2 X (List.mem_toFinset.mp X.2)
    exact ⟨⟨φ, hφ⟩, Subtype.ext hX⟩
  rw [Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.card_toFinset]

end Gen

section D0

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

@[expose] noncomputable def D0 : Subgroup ↥D.Mb := D.genC3 Two.d7Gens

include hOut hTw hHat

theorem D0_spec : ∀ φ ∈ D.D0, φ ∈ D.C3 ∧ D.kap (φ : MulAut ↥D.E) ∈ Two.enum7 Two.d7Gens := by
  obtain ⟨-, -, hid, hcl, -⟩ := Two.tOK48_spec
  exact (D.genC3_spec hOut hTw hHat (Two.d7Gens_sub) hid hcl).1

theorem D0_le_C3 : D.D0 ≤ D.C3 := fun φ hφ => (D.D0_spec hOut hTw hHat φ hφ).1

theorem card_D0 : Nat.card D.D0 = 64 := by
  obtain ⟨-, -, hid, hcl, h64, -⟩ := Two.tOK48_spec
  rw [D0, D.card_genC3 hOut hTw hHat (Two.d7Gens_sub) hid hcl, h64]

theorem D0_inf_Bb : D.D0 ⊓ D.Bb = ⊥ := by
  obtain ⟨-, -, -, -, -, -, hB, -⟩ := Two.tOK48_spec
  rw [eq_bot_iff]
  rintro φ ⟨hφD, hφB⟩
  have hk := hB _ (D.D0_spec hOut hTw hHat φ hφD).2 (D.kap_mem_b7List hOut hTw hHat hφB)
  rw [mem_bot]
  refine D.eq_of_kap_eq hOut hTw hHat (D.Bb_le_C3 hOut hTw hHat hφB).1 (one_mem _) ?_
  rw [hk, Subgroup.coe_one, D.kap_one]

theorem D0_le_normalizer : D.D0 ≤ normalizer (D.Bb : Set ↥D.Mb) := fun φ hφ =>
  mem_normalizer_fintype fun _ hb => D.conj_mem_Bb (D.D0_le_C3 hOut hTw hHat hφ).2 hb

theorem card_D0_sup_Bb : Nat.card (D.D0 ⊔ D.Bb : Subgroup ↥D.Mb) = 1024 := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer (D.D0_le_normalizer hOut hTw hHat)
  rw [D.D0_inf_Bb hOut hTw hHat, Subgroup.card_bot, mul_one, D.card_D0 hOut hTw hHat,
    D.card_Bb hOut hTw hHat] at h1
  rw [h1]

theorem D0_sup_Bb_le_Cb : D.D0 ⊔ D.Bb ≤ D.Cb :=
  sup_le (fun φ hφ => (D.D0_le_C3 hOut hTw hHat hφ).2) D.Bb_le_Cb

end D0

section Rec

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

@[expose] noncomputable def BC : Subgroup ↥D.Cb := D.Bb.subgroupOf D.Cb

include hOut hTw hHat

theorem BC_normal : (D.BC).Normal :=
  ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr (D.conj_mem_Bb g.2 (Subgroup.mem_subgroupOf.mp hn))⟩

theorem isElementaryAbelian_BC : CFSG.IsElementaryAbelian 2 ↥(D.BC) := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    exact D.Bb_comm hOut hTw hHat (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
    apply Subtype.ext
    apply Subtype.ext
    rw [pow_two]
    exact D.Bb_mul_self hOut hTw hHat (Subgroup.mem_subgroupOf.mp x.2)

theorem card_BC : Nat.card ↥(D.BC) = 16 := by
  rw [BC, Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.Bb_le_Cb).toEquiv,
    D.card_Bb hOut hTw hHat]

theorem exists_compl_BC : ∃ K : Subgroup ↥D.Cb, D.BC ⊓ K = ⊥ ∧ D.BC ⊔ K = ⊤ := by
  haveI := D.BC_normal hOut hTw hHat
  haveI := D.isElementaryAbelian_BC hOut hTw hHat
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card ↥D.Cb).factorization 2 = 10 := by
    rw [D.card_Cb hOut hTw hHat, show (21504 : ℕ) = 2 ^ 10 * 21 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd]
  set P : Subgroup ↥D.Cb := (D.D0 ⊔ D.Bb).subgroupOf D.Cb with hP
  have hPcard : Nat.card P = 2 ^ (Nat.card ↥D.Cb).factorization 2 := by
    rw [hfac, hP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (D.D0_sup_Bb_le_Cb hOut hTw hHat)).toEquiv,
      D.card_D0_sup_Bb hOut hTw hHat]
    norm_num
  let S : Sylow 2 ↥D.Cb := Sylow.ofCard P hPcard
  have hS : (S : Subgroup ↥D.Cb) = P := Sylow.coe_ofCard _ _
  have hVp : IsPGroup 2 ↥(D.BC) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hD0C : D.D0 ≤ D.Cb := fun φ hφ => (D.D0_le_C3 hOut hTw hHat hφ).2
  refine (CFSG.Quasithin.gaschutz hVp S).mpr ⟨(D.D0).subgroupOf D.Cb, ?_, ?_, ?_⟩
  · rw [hS, hP]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr
      ((le_sup_left : D.D0 ≤ D.D0 ⊔ D.Bb) (Subgroup.mem_subgroupOf.mp hx))
  · rw [eq_bot_iff]
    rintro x ⟨hxB, hxD⟩
    have hx : (x : ↥D.Mb) ∈ D.D0 ⊓ D.Bb :=
      ⟨Subgroup.mem_subgroupOf.mp hxD, Subgroup.mem_subgroupOf.mp hxB⟩
    rw [D.D0_inf_Bb hOut hTw hHat, mem_bot] at hx
    exact mem_bot.mpr (Subtype.ext hx)
  · rw [hS, hP, BC, sup_comm D.D0, Subgroup.subgroupOf_sup D.Bb_le_Cb hD0C]

theorem tb_mem_Cb : D.tb ∈ D.Cb := mem_centralizer_singleton_iff.mpr rfl

open scoped IsMulCommutative in
theorem nonempty_cb_mulEquiv : Nonempty (↥D.Cb ≃* CFSG.Quasithin.A94.L52.Hc) := by
  haveI := D.BC_normal hOut hTw hHat
  haveI := D.isElementaryAbelian_BC hOut hTw hHat
  obtain ⟨K, hVK, hVK'⟩ := D.exists_compl_BC hOut hTw hHat
  set V : Subgroup ↥D.Cb := D.BC with hVdef
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : FiniteDimensional (ZMod 2) (Additive V) := Module.Finite.of_finite
  have : Finite (Additive V ≃ₗ[ZMod 2] Additive V) :=
    Finite.of_injective (fun f : Additive V ≃ₗ[ZMod 2] Additive V => (f : Additive V → Additive V))
      fun _ _ h => LinearEquiv.ext (congrFun h)
  set tC : ↥D.Cb := ⟨D.tb, D.tb_mem_Cb hOut hTw hHat⟩ with htC
  have htV : tC ∈ V := Subgroup.mem_subgroupOf.mpr (D.tb_mem_Bb hOut hTw hHat)
  set z'' : Additive V := Additive.ofMul ⟨tC, htV⟩ with hz''
  set Γ := MulAction.stabilizer (Additive V ≃ₗ[ZMod 2] Additive V) z'' with hΓ
  have hcentV : centralizer (V : Set ↥D.Cb) ≤ V := by
    intro g hg
    refine Subgroup.mem_subgroupOf.mpr (D.mem_Bb_of_centralizes hOut hTw hHat g.2 fun b hb => ?_)
    have := mem_centralizer_iff.mp hg ⟨b, D.Bb_le_Cb hb⟩ (Subgroup.mem_subgroupOf.mpr hb)
    exact (congrArg Subtype.val this).symm
  have hmem : ∀ k : ↥D.Cb, CFSG.GroupTheory.GLnTwoSplitting.conjLinear V k ∈ Γ := by
    intro k
    change CFSG.GroupTheory.GLnTwoSplitting.conjLinear V k z'' = z''
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [CFSG.GroupTheory.GLnTwoSplitting.coe_conjLinear_apply]
    apply Subtype.ext
    change (k : ↥D.Mb) * D.tb * (k : ↥D.Mb)⁻¹ = D.tb
    rw [mem_centralizer_singleton_iff.mp k.2, mul_inv_cancel_right]
  have hKcard : Nat.card K = 1344 := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer (H := K) (N := V)
      (fun x _ => mem_normalizer_fintype fun _ hv => (inferInstance : V.Normal).conj_mem _ hv x)
    rw [inf_comm, hVK, Subgroup.card_bot, mul_one, sup_comm, hVK', Subgroup.card_top,
      D.card_Cb hOut hTw hHat, hVdef, D.card_BC hOut hTw hHat] at h1
    omega
  let ψ : K →* Γ :=
    ((CFSG.GroupTheory.GLnTwoSplitting.conjLinear V).comp K.subtype).codRestrict Γ fun c => hmem c
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    have h1 : CFSG.GroupTheory.GLnTwoSplitting.conjLinear V (c : ↥D.Cb) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
    obtain ⟨e, he⟩ := (CFSG.GroupTheory.GLnTwoSplitting.conjLinear_eq_one_iff V hcentV _).mp h1
    have hcV : (c : ↥D.Cb) ∈ V := he ▸ (Additive.toMul e).2
    have : (c : ↥D.Cb) ∈ V ⊓ K := ⟨hcV, c.2⟩
    rw [hVK, mem_bot] at this
    exact mem_bot.mpr (Subtype.ext this)
  have hfinV : finrank (ZMod 2) (Additive V) = 4 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have h16 : Nat.card (Additive V) = 16 := D.card_BC hOut hTw hHat
    rw [Nat.card_zmod, h16] at h1
    exact Nat.pow_right_injective le_rfl (h1.symm.trans (by norm_num))
  have hz0 : z'' ≠ 0 := fun h0 => by
    have h1 : (⟨tC, htV⟩ : V) = 1 := Additive.ofMul.injective (h0.trans ofMul_one.symm)
    have h2 : D.tb = 1 := congrArg (fun x : V => ((x : ↥D.Cb) : ↥D.Mb)) h1
    have h3 := D.kap_tb
    rw [h2, Subgroup.coe_one, D.kap_one] at h3
    exact absurd h3 (by decide)
  have hΓcard : Nat.card Γ = 1344 :=
    CFSG.LargeExtraspecial.DW.W3.card_stabilizer_of_finrank_four hfinV hz0
  have hψ : Function.Bijective ψ :=
    hψinj.bijective_of_nat_card_le (by rw [hΓcard, hKcard])
  let X' : CFSG.LargeExtraspecial.DW.W4.SplittingOn V Γ :=
    { centralizer_le := hcentV
      mem := hmem
      σ := K.subtype.comp (MulEquiv.ofBijective ψ hψ).symm.toMonoidHom
      conjLinear_σ := fun f =>
        congrArg Subtype.val ((MulEquiv.ofBijective ψ hψ).apply_symm_apply f) }
  obtain ⟨b, hb⟩ := CFSG.LargeExtraspecial.DW.exists_basis_eq hfinV (by norm_num) hz0
  obtain ⟨e₁⟩ := X'.nonempty_centralizer_mulEquiv b (by norm_num) htV hb (fun f hf => by
    change f z'' = z''
    rw [← hb]
    exact hf)
  have htop : centralizer ({tC} : Set ↥D.Cb) = ⊤ := eq_top_iff.mpr fun g _ =>
    mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp g.2))
  exact ⟨((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm.trans e₁⟩

end Rec

end Data41

end CFSG.Quasithin.H13.AS91
