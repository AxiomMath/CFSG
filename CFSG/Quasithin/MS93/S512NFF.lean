module

public import CFSG.Quasithin.MS93.S38ETypes
public import CFSG.Quasithin.MS93.S36SpEType
public import CFSG.Quasithin.MS93.S512NA6
public import CFSG.Quasithin.MS93.S38OffHatMod
public import CFSG.Quasithin.MS93.S5Q2Par
public import CFSG.Quasithin.MS93.S310MQ

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512N

section Lstar

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem card_lstar_of_data (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) :
    (k = 1 ∧ Nat.card (S32.Lstar L) = 360) ∨
      (2 ≤ k ∧ Nat.card (S32.Lstar L) = ordBC 2 (2 ^ k)) := by
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  have hO : ∀ o ∈ CFSG.pCore 2 ↥L, a (Subgroup.inclusion h.L_le o) = 1 := fun o ho =>
    S310.map_eq_one_of_mem_pCoreOf hd.2.2.1
      (pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer
        (mem_pCoreOf_of_mem_pCore_two ho))
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    refine Or.inl ⟨rfl, ?_⟩
    have hF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hd.2.1, pow_one]
    obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hF
    have hLa := S5Q2.map_L_eq_commutator h hd
    have hmem : ∀ l : ↥L, (B5FinSp.theta c).symm (a (Subgroup.inclusion h.L_le l)) ∈
        alternatingGroup (Fin 6) := by
      intro l
      have h1 : a (Subgroup.inclusion h.L_le l) ∈ commutator (MSP.Sp4 F) := by
        rw [← hLa]
        exact ⟨Subgroup.inclusion h.L_le l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
      rw [MSP.mem_commutator_iff_sign c] at h1
      exact Equiv.Perm.mem_alternatingGroup.2 h1
    let α : ↥L →* alternatingGroup (Fin 6) :=
      ((B5FinSp.theta c).symm.toMonoidHom.comp (a.comp (Subgroup.inclusion h.L_le))).codRestrict
        _ hmem
    refine S36E.card_lstar_of_alt h (α := α) ?_ fun o ho => ?_
    · rintro ⟨σ, hσ⟩
      have h1 : B5FinSp.theta c σ ∈ commutator (MSP.Sp4 F) := by
        rw [MSP.mem_commutator_iff_sign c, MulEquiv.symm_apply_apply]
        exact Equiv.Perm.mem_alternatingGroup.1 hσ
      rw [← hLa] at h1
      obtain ⟨m, hm, hma⟩ := h1
      refine ⟨⟨m, Subgroup.mem_subgroupOf.1 hm⟩, Subtype.ext ?_⟩
      show (B5FinSp.theta c).symm (a m) = σ
      rw [hma, MulEquiv.symm_apply_apply]
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show (B5FinSp.theta c).symm (a (Subgroup.inclusion h.L_le o)) = 1
      rw [hO o ho, map_one]
  · refine Or.inr ⟨hk, ?_⟩
    have hF : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
    have : Finite F := Finite.of_fintype F
    have hLa := S5B.map_L_eq_top h hd hk
    refine S36E.card_lstar_of_sp4 h hF hk (α := a.comp (Subgroup.inclusion h.L_le)) ?_
      fun o ho => ?_
    · intro g
      have : g ∈ (L.subgroupOf M).map a := by rw [hLa]; exact Subgroup.mem_top g
      obtain ⟨m, hm, rfl⟩ := this
      exact ⟨⟨m, Subgroup.mem_subgroupOf.1 hm⟩, rfl⟩
    · rw [MonoidHom.mem_ker]
      exact hO o ho

end Lstar

section Hat

variable {S : Type} [CommGroup S]

theorem mem_fixV_zpowers {x : MulAut S} {s : S} : s ∈ fixV (Subgroup.zpowers x) ↔ x s = s :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem eq_one_of_hat (hS2 : ∀ s : S, s ^ 2 = 1) {K : Subgroup (MulAut S)} (hK : FFCaseHatA6 K)
    {x : MulAut S} (hxN : x ∈ Subgroup.normalizer (K : Set (MulAut S)))
    (hidx : (fixV (Subgroup.zpowers x)).index ≤ 2) : x = 1 := by
  have hH := S38H.HatMod.of_tripleA6Six hS2 hK.1
  have := hH.finite
  obtain ⟨z, hcen, hz3, hfp⟩ := hH.exists_z
  set zz : MulAut S := (z : MulAut S) with hzz
  have hcard : Nat.card S = 2 ^ 6 := hH.card
  have hwK : x * zz * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hxN zz).1 z.2
  have hwc : (⟨x * zz * x⁻¹, hwK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg' : x⁻¹ * (g : MulAut S) * x⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem hxN) g).1 g.2
    have hzc : z ∈ Subgroup.center ↥K := by rw [hcen]; exact Subgroup.mem_zpowers z
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨_, hg'⟩)
    simp only [Subgroup.coe_mul] at h1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (g : MulAut S) * (x * zz * x⁻¹) = x * ((x⁻¹ * g * x⁻¹⁻¹) * zz) * x⁻¹ := by group
      _ = x * (zz * (x⁻¹ * g * x⁻¹⁻¹)) * x⁻¹ := by rw [← h1]
      _ = x * zz * x⁻¹ * g := by group
  rw [hcen] at hwc
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hwc
  have hw : x * zz * x⁻¹ = zz ^ n := by
    have := congrArg Subtype.val hn
    simpa using this.symm
  have hz1 : zz ≠ 1 := by
    intro h1
    have hnt : Nontrivial S := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      norm_num
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    exact hs (hfp s (by rw [h1, MulAut.one_apply]))
  have hz3' : zz ^ (3 : ℤ) = 1 := by exact_mod_cast hz3
  have hcases : zz ^ n = 1 ∨ zz ^ n = zz ∨ zz ^ n = zz⁻¹ := by
    have hmod : zz ^ n = zz ^ (n % 3) := zpow_eq_zpow_emod n hz3'
    have h0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
    have h3 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
    rw [hmod]
    rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h | h <;> rw [h]
    · left; simp
    · right; left; simp
    · right; right
      have : zz ^ (2 : ℤ) = zz ^ (3 : ℤ) * zz⁻¹ := by group
      rw [this, hz3', one_mul]
  rcases hcases with h1 | h1 | h1
  · exfalso
    apply hz1
    have : x * zz * x⁻¹ = 1 := hw.trans h1
    have h2 : zz = x⁻¹ * (x * zz * x⁻¹) * x := by group
    rw [h2, this]
    group
  ·
    have hxz : x * zz = zz * x := by
      have := hw.trans h1
      calc x * zz = x * zz * x⁻¹ * x := by group
        _ = zz * x := by rw [this]
    let d : S →* S :=
      { toFun := fun s => x s * s⁻¹
        map_one' := by simp
        map_mul' := fun s t => by
          simp only [map_mul, mul_inv_rev]
          rw [mul_comm t⁻¹ s⁻¹]
          simp only [mul_assoc, mul_left_comm (x t), mul_comm (x t)] }
    have hker : d.ker = fixV (Subgroup.zpowers x) := by
      ext s
      rw [MonoidHom.mem_ker, mem_fixV_zpowers]
      exact mul_inv_eq_one
    have hcardR : Nat.card d.range ≤ 2 := by
      rw [← Subgroup.index_ker, hker]
      exact hidx
    have hinv : ∀ w ∈ d.range, zz w ∈ d.range := by
      rintro _ ⟨s, rfl⟩
      refine ⟨zz s, ?_⟩
      show x (zz s) * (zz s)⁻¹ = zz (x s * s⁻¹)
      rw [map_mul, map_inv]
      congr 1
      have := congrArg (fun φ : MulAut S => φ s) hxz
      simpa using this
    have hd1 : ∀ s, d s = 1 := by
      intro s
      by_contra hne
      have hmem : d s ∈ d.range := ⟨s, rfl⟩
      have hzmem := hinv _ hmem
      have hz1' : zz (d s) ≠ 1 := fun h0 => hne (by
        have := congrArg zz.symm h0
        simpa using this)
      have hzne : zz (d s) ≠ d s := fun h0 => hne (hfp _ h0)
      have h3 : 3 ≤ Nat.card d.range := by
        classical
        have : Fintype d.range := Fintype.ofFinite _
        set f : Finset d.range := {⟨1, d.range.one_mem⟩, ⟨d s, hmem⟩, ⟨zz (d s), hzmem⟩}
        have hc3 : f.card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair]
          · intro h0
            exact hzne (congrArg Subtype.val h0).symm
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h0 => hne (congrArg Subtype.val h0).symm,
              fun h0 => hz1' (congrArg Subtype.val h0).symm⟩
        have := Finset.card_le_univ f
        rw [hc3] at this
        rw [Nat.card_eq_fintype_card]
        exact this
      omega
    refine MulEquiv.ext fun s => ?_
    have := hd1 s
    rw [MulAut.one_apply]
    exact mul_inv_eq_one.1 this
  ·
    have hxz : ∀ s, x (zz s) = zz⁻¹ (x s) := by
      intro s
      have h2 : x * zz = zz⁻¹ * x := by
        have := hw.trans h1
        calc x * zz = x * zz * x⁻¹ * x := by group
          _ = zz⁻¹ * x := by rw [this]
      have := congrArg (fun φ : MulAut S => φ s) h2
      simpa using this
    set C := fixV (Subgroup.zpowers x) with hC
    set C' := C.comap zz.toMonoidHom with hC'
    have hbot : C ⊓ C' = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hv, hv'⟩
      rw [Subgroup.mem_bot]
      have h2 : x v = v := mem_fixV_zpowers.1 hv
      have h3 : x (zz v) = zz v := mem_fixV_zpowers.1 hv'
      rw [hxz, h2] at h3
      have h4 : zz (zz v) = v := by
        have := congrArg zz h3
        simpa using this.symm
      have h5 : zz v = v := by
        have e : zz (zz (zz v)) = zz v := by rw [h4]
        have hz3v : zz (zz (zz v)) = v := by
          have := congrArg (fun φ : MulAut S => φ v) hz3
          simpa [pow_succ, mul_assoc] using this
        exact e.symm.trans hz3v
      exact hfp v h5
    have hC'idx : C'.index = C.index :=
      Subgroup.index_comap_of_surjective C zz.surjective
    have h4 : (C ⊓ C').index ≤ 4 := by
      calc (C ⊓ C').index ≤ C.index * C'.index := Subgroup.index_inf_le
        _ ≤ 2 * 2 := by rw [hC'idx]; exact Nat.mul_le_mul hidx hidx
        _ = 4 := by norm_num
    rw [hbot, Subgroup.index_bot, hcard] at h4
    norm_num at h4

end Hat

section Coord

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem injective_of_coord {S₀ : Type} [CommGroup S₀] {X : Subgroup (MulAut S₀)} {F' : Type}
    [Field F'] {φ : ↥X →* MSP.Sp4 F'} {θ : S₀ ≃* Multiplicative (MSP.V4 F')}
    (hθ : ∀ (x : ↥X) (s : S₀), Multiplicative.toAdd (θ ((x : MulAut S₀) s)) =
      MSP.mat (φ x) *ᵥ Multiplicative.toAdd (θ s)) : Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine MulEquiv.ext fun s => θ.injective (Multiplicative.toAdd.injective ?_)
  rw [hθ, hx, MSP.mat_one, Matrix.one_mulVec]
  rfl

theorem exists_coord (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {S₀ : Type} [CommGroup S₀] [Finite S₀] {ρ : ↥M →* MulAut S₀} (hρ : S38E.IsIrrRep L ρ)
    {A : Subgroup (MulAut S₀)} (hAX : A ≤ ρ.range) (hA : IsElemAbelian2 A)
    (hAc : 2 ^ k ≤ Nat.card A) (hAf : Nat.card S₀ ≤ 2 ^ k * Nat.card (fixV A))
    (hk2 : 2 ≤ k → ρ.range ≤ S38E.IsIrrRep.imL L ρ) :
    ∃ (F' : Type) (_ : Field F') (_ : Fintype F') (φ : ↥ρ.range →* MSP.Sp4 F')
      (θ : S₀ ≃* Multiplicative (MSP.V4 F')), Fintype.card F' = 2 ^ k ∧ Function.Surjective φ ∧
      ∀ (x : ↥ρ.range) (s : S₀), Multiplicative.toAdd (θ ((x : MulAut S₀) s)) =
        MSP.mat (φ x) *ᵥ Multiplicative.toAdd (θ s) := by
  have hS2 := hρ.sq
  have hk := hd.1
  have hq2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hA1 : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAc
    omega
  have hFF : IsFFModule ρ.range :=
    ⟨A, hAX, hA1, hA, hAf.trans (Nat.mul_le_mul_right _ hAc)⟩
  have hH := hρ.ffHyp h hSQ hFF
  obtain ⟨-, -, hcases, -⟩ := h14 S₀ hS2 _ _ hH
  have htype := card_lstar_of_data h hd
  have hidxA : (fixV A).index ≤ 2 ^ k := by
    have h1 := (fixV A).card_mul_index
    have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : 2 ^ k * Nat.card (fixV A) < (fixV A).index * Nat.card (fixV A) :=
      Nat.mul_lt_mul_of_pos_right hlt hpos
    rw [mul_comm ((fixV A).index), h1] at this
    omega
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
  have hidxx : (fixV (Subgroup.zpowers (x : MulAut S₀))).index ≤ 2 ^ k := by
    have hle : fixV A ≤ fixV (Subgroup.zpowers (x : MulAut S₀)) := fun v hv y hy =>
      hv y ((Subgroup.zpowers_le.2 x.2) hy)
    exact (Subgroup.index_antitone hle).trans hidxA
  have hx1' : (x : MulAut S₀) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  rcases hcases with hSL | hhat | hsp | hG2
  ·
    exfalso
    obtain ⟨n, hn, hc⟩ := S38E.card_lstar_of_ffCaseSL3 hρ h hSL
    rcases htype with ⟨-, h360⟩ | ⟨hk2', hBC⟩
    · exact S32.ordA_two_ne_360 hn (hc.symm.trans h360)
    · exact S36E.ordA_two_ne_ordBC_two hk2' (hc.symm.trans hBC)
  ·
    exfalso
    have hc := S38E.card_lstar_of_ffCaseHatA6 hρ h hhat
    rcases htype with ⟨rfl, -⟩ | ⟨hk2', hBC⟩
    · exact hx1' (eq_one_of_hat hS2 hhat
        (S38E.IsIrrRep.range_le_normalizer h (hAX x.2)) (by simpa using hidxx))
    · exact (S32.ordBC_two_ne (by omega)).2.1 (hBC.symm.trans hc)
  · rcases hsp with ⟨n, hn2, F', iF, fF, hcard, π, hπ⟩ | ⟨π, hπ⟩
    ·
      have hc := S38E.card_lstar_of_sp4Nat hρ h hn2 ⟨F', iF, fF, hcard, π, hπ⟩
      rcases htype with ⟨rfl, h360⟩ | ⟨hk2', hBC⟩
      · exact absurd (hc.symm.trans h360) (S32.ordBC_two_ne (by omega)).2.1
      have hnk : n = k := S36E.eq_of_ordBC_two_eq (by omega) (by omega) (hc.symm.trans hBC)
      subst hnk
      have : Fintype F' := Fintype.ofFinite F'
      obtain ⟨φK, θ, hθ⟩ := S36E.coord_of_natSp4 hπ
      have hXK : ρ.range = S38E.IsIrrRep.imL L ρ :=
        le_antisymm (hk2 hk2') (S38E.IsIrrRep.imL_le)
      set e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
      have hφKi : Function.Injective φK := injective_of_coord hθ
      have hφKs : Function.Surjective φK := by
        have : Finite ↥(StatedSp 2 F') := Finite.of_equiv _ e.symm.toEquiv
        exact (Finite.injective_iff_surjective_of_equiv e.symm.toEquiv).1 hφKi
      refine ⟨F', iF, this, φK.comp (Subgroup.inclusion hXK.le), θ, ?_, ?_, fun x s => ?_⟩
      · rw [Fintype.card_eq_nat_card, hcard]
      · intro g
        obtain ⟨y, rfl⟩ := hφKs g
        exact ⟨Subgroup.inclusion hXK.ge y, rfl⟩
      · exact hθ (Subgroup.inclusion hXK.le x) s
    ·
      have hc := S38E.card_lstar_of_altNat hρ h ⟨π, hπ⟩
      rcases htype with ⟨rfl, -⟩ | ⟨hk2', hBC⟩
      swap
      · exact absurd (hBC.symm.trans hc) (S32.ordBC_two_ne (by omega)).2.1
      obtain ⟨φ, θ, hθ⟩ := S36E.coord_of_altDn hπ (S38E.IsIrrRep.range_le_normalizer h)
      have hφi : Function.Injective φ := injective_of_coord hθ
      refine ⟨ZMod 2, inferInstance, inferInstance, φ, θ, by simp, ?_, hθ⟩
      have hxK : (x : MulAut S₀) ∉ S38E.IsIrrRep.imL L ρ := by
        intro hxK
        have h4 := four_mul_card_fixV_le_of_alt ⟨π, hπ⟩ hxK hx1'
        have h1 := (fixV (Subgroup.zpowers (x : MulAut S₀))).card_mul_index
        have hpos : 0 < Nat.card (fixV (Subgroup.zpowers (x : MulAut S₀))) := Nat.card_pos
        have h2 : (fixV (Subgroup.zpowers (x : MulAut S₀))).index ≤ 2 := by simpa using hidxx
        have h3 : Nat.card S₀ ≤ Nat.card (fixV (Subgroup.zpowers (x : MulAut S₀))) * 2 := by
          rw [← h1]
          exact Nat.mul_le_mul_left _ h2
        omega
      set K := S38E.IsIrrRep.imL L ρ
      have hKX : K ≤ ρ.range := S38E.IsIrrRep.imL_le
      have hcK : Nat.card K = 360 := by
        rw [← Nat.card_congr (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ).toEquiv]
        show Nat.card ↥(alternatingGroup (Fin 6)) = 360
        rw [H13.card_alternatingGroup_fin 6 (by norm_num)]
        decide
      have hKne : K.subgroupOf ρ.range ≠ ⊤ := by
        intro htop
        apply hxK
        have : (⟨x, hAX x.2⟩ : ↥ρ.range) ∈ K.subgroupOf ρ.range := by rw [htop]; exact trivial
        exact Subgroup.mem_subgroupOf.1 this
      have hidx2 : 2 ≤ (K.subgroupOf ρ.range).index := by
        rcases Nat.lt_or_ge (K.subgroupOf ρ.range).index 2 with hlt | hge
        · exfalso
          have h0 : (K.subgroupOf ρ.range).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
          have h1 : (K.subgroupOf ρ.range).index = 1 := by omega
          exact hKne (Subgroup.index_eq_one.1 h1)
        · exact hge
      have hcX : 720 ≤ Nat.card ρ.range := by
        have h1 := (K.subgroupOf ρ.range).card_mul_index
        have h2 : Nat.card (K.subgroupOf ρ.range) = 360 := by
          rw [← hcK]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
        rw [h2] at h1
        omega
      have hcSp : Nat.card (MSP.Sp4 (ZMod 2)) = 720 := by
        rw [← Nat.card_congr (B5FinSp.theta (RingEquiv.refl (ZMod 2))).toEquiv,
          Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
        rfl
      have hrange : φ.range = ⊤ := by
        refine Subgroup.eq_top_of_card_eq _ ?_
        refine le_antisymm (Subgroup.card_le_card_group _) ?_
        rw [hcSp, ← Nat.card_congr (MonoidHom.ofInjective hφi).toEquiv]
        exact hcX
      exact MonoidHom.range_eq_top.1 hrange
  ·
    exfalso
    rcases S38E.card_lstar_of_ffCaseG2 hρ h hT hG2 with ⟨n, hn2, hc⟩ | hc
    · rcases htype with ⟨-, h360⟩ | ⟨hk2', hBC⟩
      · exact (S32.ordG2_ne (by omega)).2.1 (hc.symm.trans h360)
      · exact S36E.ordG2_ne_ordBC_two (by omega) (by omega) (hc.symm.trans hBC)
    · rcases htype with ⟨-, h360⟩ | ⟨hk2', hBC⟩
      · rw [hc] at h360
        norm_num at h360
      · exact (S32.ordBC_two_ne (by omega)).2.2 (hBC.symm.trans hc)

end Coord

end S512N

end CFSG.Quasithin.MS93
