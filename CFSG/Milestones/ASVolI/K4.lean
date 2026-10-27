module

public import Mathlib
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Milestones.ASVolI.K1
public import CFSG.Quasithin.Background.SmithB45MatMain
public import CFSG.Quasithin.Background.HFCode22Dual
public import CFSG.Quasithin.Background.HMathieuFacts
public import CFSG.Quasithin.Background.SmithB45Holds
public import CFSG.Quasithin.Background.SmithB45MatQ
public import CFSG.Quasithin.Background.SmithB45J2Main
public import CFSG.Quasithin.Background.ConjTransport
public import CFSG.Quasithin.EmptyFaithful.S153ZP
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithAltSporSporadic
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import Certificates.Certificate7275
public import Certificates.Certificate7276
public import Certificates.Certificate7277
public import Certificates.Certificate7278
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Quasithin.EmptyFaithful.S153ZN
public import CFSG.Quasithin.EmptyFaithful.S153ZO
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Monster.Code

@[expose] def IsTwoCentralIn {X : Type} [Group X] (M : Subgroup X) (t : X) : Prop :=
  t ∈ M ∧ t ^ 2 = 1 ∧ t ≠ 1 ∧
    ∃ S : Subgroup X, IsSylowTwoOf S M ∧ t ∈ S ∧ ∀ x ∈ S, x * t = t * x

section M24Vocab

variable {V : Type} [CommGroup V] {M : Subgroup (MulAut V)}

@[expose] def imgOf (π : ↥CFSG.Monster.Code.AutPerm →* ↥M) (S : Subgroup (Equiv.Perm (Fin 24))) :
    Subgroup (MulAut V) :=
  ((S.subgroupOf CFSG.Monster.Code.AutPerm).map π).map M.subtype

@[expose] def octadPts (e : G6.PermMod 24) : Set (Fin 24) := {x | Multiplicative.toAdd e x = 1}

@[expose] def KO (π : ↥CFSG.Monster.Code.AutPerm →* ↥M) (e : G6.PermMod 24) : Subgroup (MulAut V) :=
  imgOf π (fixingSubgroup (Equiv.Perm (Fin 24)) (octadPts e))

@[expose] def MO (π : ↥CFSG.Monster.Code.AutPerm →* ↥M) (e : G6.PermMod 24) : Subgroup (MulAut V) :=
  imgOf π (m24Fix e)

structure M24Setup (V : Type) [CommGroup V] [Finite V] (M : Subgroup (MulAut V))
    (π : ↥CFSG.Monster.Code.AutPerm →* ↥M) (e : G6.PermMod 24) (V5 : Subgroup V) (z : MulAut V) :
    Prop where
  elem2 : ∀ v : V, v ^ 2 = 1
  realizes : (FFModel.golaySec CFSG.Monster.Code.AutPerm golayC
    (Subgroup.zpowers (G6.allOnes 24))).RealizesVia M ⊤ ⊥ π
  octad : e ∈ golayC ∧ hammingNorm (Multiplicative.toAdd e) = 8
  z_mem : z ∈ KO π e ∧ z ≠ 1
  V5_inv : ∀ m ∈ MO π e, ∀ v ∈ V5, m v ∈ V5
  V5_rank : rk ↥V5 = 5
  V1_le : fixV (KO π e) ≤ V5

@[expose] def Vz (V5 : Subgroup V) (z : MulAut V) : Subgroup V := V5 ⊓ fixV (Subgroup.zpowers z)

@[expose] def Dz (M : Subgroup (MulAut V)) (V5 : Subgroup V) (z : MulAut V) : Subgroup (MulAut V) :=
  M ⊓ centSub (Vz V5 z)

@[expose] def Dd (M : Subgroup (MulAut V)) (d : MulAut V) : Subgroup (MulAut V) :=
  M ⊓ centSub (commV (Subgroup.zpowers d))

end M24Vocab

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Monster.Code

@[expose] def K_4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    (∃ s : TauCeti.SporadicName, IsSporadic s (Lbar L)) →
    ((IsSporadic .M12 ↥L ∧ M12Ten L ⊤ ⊥ ∧ Nat.card V = 2 ^ 10) ∨
      (Mhat22Twelve L ⊤ ⊥ ∧ Nat.card V = 2 ^ 12) ∨
      (IsSporadic .M22 ↥L ∧ (MathieuCode22 L ⊤ ⊥ ∨ MathieuCocode22 L ⊤ ⊥) ∧
        Nat.card V = 2 ^ 10) ∨
      (IsSporadic .M23 ↥L ∧ (MathieuCode23 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥) ∧
        Nat.card V = 2 ^ 11) ∨
      (IsSporadic .M24 ↥L ∧ (MathieuCode24 L ⊤ ⊥ ∨ MathieuCocode24 L ⊤ ⊥) ∧
        Nat.card V = 2 ^ 11) ∨
      (IsSporadic .J2 ↥L ∧ J2Twelve L ⊤ ⊥ ∧ Nat.card V = 2 ^ 12)) ∧
    ¬ IsFFModule G ∧ qc 1 < qhatOf G

section BurnsideKF

open CFSG.Quasithin CFSG.Quasithin.J2Row CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
  CFSG.CharacterTheory.SteinbergBY.FieldFour CFSG.Quasithin.H in
private theorem burnsideKF_card_bound (hcard : Nat.card Γ₆ = 604800)
    (hAut : Nat.card (MulAut ↥L6) ≤ 2 * Nat.card ↥L6) (hZ : Subgroup.center ↥L6 = ⊥)
    {X : Subgroup (MulAut W6)} (hXN : X ≤ natNorm Γ₆)
    (hrank : ∀ A : Subgroup (MulAut W6), A ≤ X → IsElemAbelian2 A → Nat.card A ≤ 16)
    {A : Subgroup (MulAut W6)} (hA : IsA2 X A) :
    (Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 4096 ∧
      (commSeries A 2 = ⊥ → Nat.card A ^ 2 * Nat.card ↥(fixV A) < 4096)) ∧
    (4096 ≤ Nat.card A ^ 2 * Nat.card ↥(fixV A) →
      A ≤ L6 ∧ Nat.card A = 16 ∧ Nat.card ↥(fixV A) = 16) := by
  have hAX := hA.le
  have hAN : A ≤ natNorm Γ₆ := hAX.trans hXN
  have hel := hA.isElemAbelian2
  have hA16 := hrank A hAX hel
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hel.2 x hx
  have hA2 : 2 ≤ Nat.card A := by
    have := (Subgroup.one_lt_card_iff_ne_bot A).mpr hA.ne_bot
    omega
  set A₀ := A ⊓ L6 with hA₀
  have hlin : A ⊓ linSub ≤ A₀ := by
    rintro t ⟨htA, htl⟩
    exact ⟨htA, mem_natImage_of_linear hAut hZ (hAN htA) htl (hsq t htA)⟩
  have hcard2 : Nat.card A ≤ 2 * Nat.card A₀ := by
    have h1 : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ linSub) :=
      card_le_two_mul_card_inf_linSub hasScalarCommutant_Γ₆ (n := 2) (by norm_num)
        (by rw [FieldFour.natCard_eq]; norm_num) hAN fun x hx => hel.2 x hx
    exact h1.trans (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le hlin))
  set B₀ := A₀.comap matHom with hB₀
  have hA₀L : A₀ ≤ L6 := inf_le_right
  have hB₀Γ : B₀ ≤ Γ₆ := comap_matHom_le hA₀L
  have hB₀c : Nat.card B₀ = Nat.card A₀ := card_comap_matHom hA₀L
  have hB₀comm : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x := fun x hx y hy =>
    matHom_injective (by rw [map_mul, map_mul]; exact hel.1 _ hx.1 _ hy.1)
  have hB₀sq : ∀ x ∈ B₀, x * x = 1 := fun x hx =>
    matHom_injective (by rw [map_mul, map_one]; exact hsq _ hx.1)
  obtain ⟨b2, b3, b5⟩ := inner_bounds hcard hB₀Γ hB₀comm hB₀sq
  by_cases hAL : A ≤ L6
  · have hAA₀ : A₀ = A := inf_eq_left.mpr hAL
    have hC : Nat.card ↥(fixV A) ≤ Nat.card ↥(mFix B₀) := by
      rw [hB₀, hAA₀]
      exact card_fixV_le_mFix A
    rw [hAA₀] at hB₀c
    by_cases h5 : 5 ≤ Nat.card A
    · obtain ⟨h16, x, hx, y, hy, hxy⟩ := b5 (by rw [hB₀c]; exact h5)
      have hx' : x ∈ A.comap matHom := by rw [← hAA₀]; exact hx
      have hy' : y ∈ A.comap matHom := by rw [← hAA₀]; exact hy
      have hC16 : Nat.card ↥(fixV A) ≤ 16 := hC.trans h16
      refine ⟨⟨?_, fun hq => absurd (quad_of_commSeries hq x hx' y hy') hxy⟩, fun hge => ?_⟩
      · calc Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 16 ^ 2 * 16 :=
              Nat.mul_le_mul (Nat.pow_le_pow_left hA16 2) hC16
          _ = 4096 := by norm_num
      · have hA16' : Nat.card A = 16 := by
          by_contra hne
          have h15 : Nat.card A ≤ 15 := by omega
          have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 15 ^ 2 * 16 :=
            Nat.mul_le_mul (Nat.pow_le_pow_left h15 2) hC16
          omega
        rw [hA16'] at hge
        refine ⟨hAL, hA16', ?_⟩
        omega
    · by_cases h3 : 3 ≤ Nat.card A
      · have h64 := hC.trans (b3 (by rw [hB₀c]; exact h3))
        have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 4 ^ 2 * 64 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) h64
        exact ⟨⟨by omega, fun _ => by omega⟩, fun hge => by omega⟩
      · have h256 := hC.trans (b2 (by rw [hB₀c]; exact hA2))
        have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 2 ^ 2 * 256 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) h256
        exact ⟨⟨by omega, fun _ => by omega⟩, fun hge => by omega⟩
  · obtain ⟨t, htA, htL⟩ : ∃ t ∈ A, t ∉ L6 := by
      by_contra h
      push Not at h
      exact hAL h
    obtain ⟨σ, hσ⟩ := exists_semilinear hasScalarCommutant_Γ₆ (hAN htA)
    have hσω : σ FieldFour.ω ≠ FieldFour.ω := by
      intro h
      have e := eq_refl_of_apply_ω h
      subst e
      exact htL (mem_natImage_of_linear hAut hZ (hAN htA) hσ (hsq t htA))
    have hC : Nat.card ↥(fixV A) ≤ Nat.card {v : V6 // v ∈ mFix B₀ ∧ toAddMap t v = v} := by
      refine Nat.card_le_card_of_injective (fun v => ⟨Multiplicative.toAdd (v : W6),
        toAdd_mem_mFix (fun x hx => v.2 x hx.1),
        congrArg Multiplicative.toAdd (v.2 t htA)⟩) fun v w h => ?_
      apply Subtype.ext
      have h1 := congrArg Subtype.val h
      exact Multiplicative.toAdd.injective h1
    have hhalf := card_sq_le_of_semilinear (U := mFix B₀) hσ hσω
    set s := Nat.card {v : V6 // v ∈ mFix B₀ ∧ toAddMap t v = v} with hs
    have hn1 : 1 ≤ Nat.card A₀ := Nat.card_pos
    suffices h : Nat.card A ^ 2 * Nat.card ↥(fixV A) < 4096 from
      ⟨⟨h.le, fun _ => h⟩, fun hge => absurd hge (not_le.mpr h)⟩
    by_cases h5 : 5 ≤ Nat.card A₀
    · have hs4 : s ≤ 4 := le_of_sq_le hhalf ((b5 (by rw [hB₀c]; exact h5)).1.trans (by norm_num))
      have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 16 ^ 2 * 4 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hA16 2) (hC.trans hs4)
      omega
    by_cases h3 : 3 ≤ Nat.card A₀
    · have hs8 : s ≤ 8 := le_of_sq_le hhalf ((b3 (by rw [hB₀c]; exact h3)).trans (by norm_num))
      have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 8 ^ 2 * 8 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (hC.trans hs8)
      omega
    by_cases h2 : 2 ≤ Nat.card A₀
    · have hs16 : s ≤ 16 := le_of_sq_le hhalf ((b2 (by rw [hB₀c]; exact h2)).trans (by norm_num))
      have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 4 ^ 2 * 16 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (hC.trans hs16)
      omega
    · have hm : Nat.card ↥(mFix B₀) ≤ 64 ^ 2 :=
        (card_mono le_top).trans (by rw [card_top]; norm_num)
      have hs64 : s ≤ 64 := le_of_sq_le hhalf hm
      have : Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 2 ^ 2 * 64 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (hC.trans hs64)
      omega

open CFSG.Quasithin CFSG.Quasithin.J2Model CFSG.Quasithin.J2Row CFSG.Quasithin.H
  CFSG.CharacterTheory.SteinbergBY CFSG.Blueprint CFSG.QuasithinUnique.Setup.X1 in
private theorem burnsideKF_j2_bound
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (hT : B45TypeSpor .J2 ↥L)
    (h2 : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) :
    J2Twelve L ⊤ ⊥ ∧ Nat.card V = 4096 ∧ ∀ A : Subgroup (MulAut V), IsA2 G A →
      (Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ 4096 ∧
        (IsQuadratic A → Nat.card A ^ 2 * Nat.card ↥(fixV A) < 4096)) ∧
      (4096 ≤ Nat.card A ^ 2 * Nat.card ↥(fixV A) →
        A ≤ L ∧ Nat.card A = 16 ∧ Nat.card ↥(fixV A) = 16) := by
  have hcard : Nat.card V < 2 ^ 24 := card_lt_of_j2 hV hHyp hT h2
  obtain ⟨hZ, ⟨θ⟩⟩ := hT
  obtain ⟨π, hπ⟩ := J2Mod.j2SmallModules_holds V hV L ⟨θ⟩ hHyp.2.2.2 hcard
  obtain ⟨e, he⟩ := exists_equiv_of_zornQ hπ
  have hL6 : L.map (MulAut.congr e).toMonoidHom = L6 := map_congr_eq_L6 hπ.1 e he
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr : IsIrrOn L :=
    CFSG.QuasithinUnique.Bridge.Dichotomy.isIrrOn_of_isIrrSec hHyp.2.2.2
  have hperf : Group.IsPerfect ↥L := hHyp.2.2.1.1
  have hGN := B42L2.le_normalizer_of_b4Hyp hHyp
  let φ : ↥L ≃* ↥L6 := ((MulAut.congr e).subgroupMap L).trans (MulEquiv.subgroupCongr hL6)
  have hJ2 : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  have hcardL6 : Nat.card ↥L6 = 604800 := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_congr θ.toEquiv, hJ2]
  have hcardΓ : Nat.card ↥Γ₆ = 604800 := by
    have hinj : Function.Injective (natAut Γ₆) := matHom_injective.comp Subtype.val_injective
    rw [← hcardL6]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hAut : Nat.card (MulAut ↥L6) ≤ 2 * Nat.card ↥L6 := by
    obtain ⟨Φ, -⟩ := CFSG.QuasithinUnique.Bridge.J2Excl.j2_aut_model
    have h1 : Nat.card (MulAut ↥L6) = Nat.card (MulAut (NativeSporadic.Carrier .J2)) :=
      Nat.card_congr (MulAut.congr (φ.symm.trans θ)).toEquiv
    have h2 : Nat.card (MulAut (NativeSporadic.Carrier .J2)) = 1209600 := by
      rw [← Nat.card_congr Φ.toEquiv, CFSG.QuasithinUnique.Bridge.J2Excl.card_j2R]
    rw [h1, h2, hcardL6]
  have hZ6 : Subgroup.center ↥L6 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : φ.symm z ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz (φ y)]
    rw [hZ, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply φ z, hz', map_one]
  set G' := G.map (MulAut.congr e).toMonoidHom with hG'
  have hXN : G' ≤ natNorm Γ₆ := by
    have h := Subgroup.map_mono (f := (MulAut.congr e).toMonoidHom) hGN
    rw [Subgroup.map_equiv_normalizer_eq L (MulAut.congr e), hL6] at h
    exact h
  have hrank : ∀ A : Subgroup (MulAut W6), A ≤ G' → IsElemAbelian2 A → Nat.card A ≤ 16 := by
    intro A hA hAel
    obtain ⟨A₀, hA₀G, rfl⟩ := exists_eq_map_congrHom e hA
    have hA₀el : IsElemAbelian2 A₀ := by
      refine ⟨fun a ha b hb => (MulAut.congr e).injective ?_, fun a ha =>
        (MulAut.congr e).injective ?_⟩
      · rw [map_mul, map_mul]
        exact hAel.1 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      · rw [map_pow, map_one]
        exact hAel.2 _ ⟨a, ha, rfl⟩
    rw [show A₀.map (congrHom e) = A₀.map (MulAut.congr e).toMonoidHom from rfl,
      card_map_congr]
    exact card_le_sixteen hW hperf hirr hZ θ (hA₀G.trans hGN) hA₀el
  have hcardV : Nat.card V = 4096 := by rw [Nat.card_congr e.toEquiv, card_W6]
  refine ⟨⟨FieldFour, inferInstance, inferInstance, j2Γ₀, FieldFour.natCard_eq,
    j2Γ₀_le_quasithinG2, ⟨π, hπ⟩⟩, hcardV, fun A hA => ?_⟩
  have key := burnsideKF_card_bound hcardΓ hAut hZ6 hXN hrank (isA2_map_congr e hA)
  rw [card_map_congr, card_fixV_map_congr] at key
  refine ⟨⟨key.1.1, fun hq => key.1.2 (quad_map_congr e
    ((isQuadratic_iff_commSeries_two A).mp hq))⟩, fun hge => ?_⟩
  obtain ⟨hL6le, h16, hc16⟩ := key.2 hge
  refine ⟨?_, h16, hc16⟩
  rw [← hL6] at hL6le
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.congr e).injective).mp hL6le

private theorem burnsideKF_center_eq_bot {X S : Type} [Group X] [Group S] [IsSimpleGroup S]
    (hperf : Group.IsPerfect X) (θ : X ≃* S) : Subgroup.center X = ⊥ := by
  have hmap : ((Subgroup.center X).map θ.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance θ.toMonoidHom θ.surjective
  haveI := hmap
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.center X).map θ.toMonoidHom) with h | h
  · exact (Subgroup.map_eq_bot_iff_of_injective _ θ.injective).mp h
  · exfalso
    have hX : Subgroup.center X = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : θ x ∈ (Subgroup.center X).map θ.toMonoidHom := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := this
      have : y = x := θ.injective hyx
      rwa [← this]
    have hc : commutator X = ⊥ := (commutator_eq_bot_iff_center_eq_top X).mpr hX
    have h1 := Group.IsPerfect.commutator_eq_top (G := X)
    rw [hc] at h1
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    have : θ.symm s ∈ (⊤ : Subgroup X) := Subgroup.mem_top _
    rw [← h1, Subgroup.mem_bot] at this
    exact hs (by simpa using congrArg θ this)

open CFSG.QuasithinUnique in
open scoped Pointwise in
private theorem burnsideKF_exists_conj_le {X : Type} [Group X] [Finite X] {G T A : Subgroup X}
    (hT : IsSylowTwoOf T G) (hAG : A ≤ G) (hA : IsPGroup 2 A) :
    ∃ g ∈ G, A.map (MulAut.conj g).toMonoidHom ≤ T := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 (T.subgroupOf G) :=
    hT.2.1.comap_of_injective G.subtype G.subtype_injective
  let P : Sylow 2 ↥G := hT'.toSylow hT.2.2
  have hA' : IsPGroup 2 (A.subgroupOf G) :=
    hA.comap_of_injective G.subtype G.subtype_injective
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥G Q P
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have haQ : (⟨a, hAG ha⟩ : ↥G) ∈ (Q : Subgroup ↥G) := hQ (Subgroup.mem_subgroupOf.mpr ha)
  have hP' : (P : Subgroup ↥G) = MulAut.conj g • (Q : Subgroup ↥G) := by
    have := congrArg (fun S : Sylow 2 ↥G => (S : Subgroup ↥G)) hg
    simpa [Sylow.coe_subgroup_smul] using this.symm
  have hmem : g * (⟨a, hAG ha⟩ : ↥G) * g⁻¹ ∈ (P : Subgroup ↥G) := by
    rw [hP']
    exact (Subgroup.mem_smul_pointwise_iff_exists _ (MulAut.conj g) _).2
      ⟨_, haQ, by simp [MulAut.smul_def]⟩
  have hP2 : (P : Subgroup ↥G) = T.subgroupOf G := IsPGroup.toSylow_coe _ _
  rw [hP2, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

open CFSG.Quasithin in
private theorem burnsideKF_index_le_two {V : Type} [CommGroup V] [Finite V] {G L : Subgroup
    (MulAut V)}
    (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (hAut : Nat.card (MulAut ↥L) ≤ 2 * Nat.card ↥L) : (L.subgroupOf G).index ≤ 2 := by
  have hLG : L ≤ G := by
    rw [hHyp.2.1]
    exact quasithinGenFitting_le G
  have hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := B42L2.le_normalizer_of_b4Hyp hHyp
  let c : ↥G →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hGN)
  have hinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : ∀ l ∈ L, (g : MulAut V) * l = l * (g : MulAut V) := by
      intro l hl
      have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : MulAut V)) hg
      have h2 : (g : MulAut V) * l * (g : MulAut V)⁻¹ = l := h1
      calc (g : MulAut V) * l = (g : MulAut V) * l * (g : MulAut V)⁻¹ * (g : MulAut V) := by group
        _ = l * (g : MulAut V) := by rw [h2]
    exact Subtype.ext
      (CFSG.QuasithinUnique.Bridge.FStarSimple.cent_trivial hHyp.2.1 hZ g g.2 hc)
  have hfin : Finite (MulAut ↥L) := MulEquiv.finite_left
  have h1 : Nat.card ↥G ≤ Nat.card (MulAut ↥L) := Nat.card_le_card_of_injective c hinj
  have h2 := Subgroup.index_mul_card (L.subgroupOf G)
  have h3 : Nat.card ↥(L.subgroupOf G) = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLG).toEquiv
  rw [h3] at h2
  have hpos : 0 < Nat.card ↥L := Nat.card_pos
  by_contra h
  push Not at h
  have : 3 * Nat.card ↥L ≤ (L.subgroupOf G).index * Nat.card ↥L := Nat.mul_le_mul_right _ h
  omega

private theorem burnsideKF_j2_aut_le
    {L : Type} [Group L]
    (θ : L ≃* CFSG.Blueprint.NativeSporadic.Carrier .J2) : Nat.card (MulAut L) ≤ 2 * Nat.card L := by
  obtain ⟨Φ, -⟩ := CFSG.QuasithinUnique.Bridge.J2Excl.j2_aut_model
  have h1 : Nat.card (MulAut L) = Nat.card (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .J2)) :=
    Nat.card_congr (MulAut.congr θ).toEquiv
  have h2 : Nat.card (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .J2)) = 1209600 := by
    rw [← Nat.card_congr Φ.toEquiv, CFSG.QuasithinUnique.Bridge.J2Excl.card_j2R]
  have h3 : Nat.card L = 604800 := by
    rw [Nat.card_congr θ.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  rw [h1, h2, h3]

private theorem burnsideKF_conjAut_eq {V : Type} [CommGroup V] (g : MulAut V) (A : Subgroup
    (MulAut V)) :
    CFSG.Quasithin.B1.conjAut g A = A.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [CFSG.Quasithin.B1.mem_conjAut, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha

def burnsideKF_orders : List ℕ :=
  [2 ^ 4 * 495, 2 ^ 6 * 1485, 2 ^ 7 * 3465, 2 ^ 7 * 79695, 2 ^ 10 * 239085, 2 ^ 3 * 21945,
   2 ^ 7 * 4725, 2 ^ 7 * 392445, 2 ^ 21 * 41377816699065, 2 ^ 9 * 86625, 2 ^ 7 * 7016625,
   2 ^ 10 * 3935925, 2 ^ 14 * 8906625, 2 ^ 13 * 54729675, 2 ^ 9 * 900030285,
   2 ^ 21 * 1982582476875, 2 ^ 18 * 161382375, 2 ^ 10 * 484147125, 2 ^ 17 * 492567075,
   2 ^ 18 * 15600091832325, 2 ^ 21 * 598528723330813275, 2 ^ 14 * 16664484375,
   2 ^ 8 * 202207730484375, 2 ^ 15 * 2769346432125, 2 ^ 41 * 1889375872099856765625,
   2 ^ 46 * 11482618231106483731969943632999939453125]

private theorem burnsideKF_mem_orders {T S : Type*} [Group T] [Group S] (θ : T ≃* S) {N : ℕ}
    (h : Nat.card S = N) (hN : N ∈ burnsideKF_orders) : Nat.card T ∈ burnsideKF_orders := by
  rw [Nat.card_congr θ.toEquiv, h]
  exact hN

open CFSG.Blueprint in
private theorem burnsideKF_card_sporadic
    {T : Type} [Group T] [IsSimpleGroup T]
    {s : TauCeti.SporadicName} (θ : T ≃* NativeSporadic.Carrier s) :
    Nat.card T ∈ burnsideKF_orders := by
  cases s
  case M11 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 4 * 495)
      (CFSG.Sporadic.Mathieu.card_M11.trans (by norm_num)) (by decide)
  case M12 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 6 * 1485)
      (CFSG.Sporadic.Mathieu.card_M12.trans (by norm_num)) (by decide)
  case M22 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 7 * 3465)
      (CFSG.Sporadic.Mathieu.card_M22.trans (by norm_num)) (by decide)
  case M23 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 7 * 79695)
      (CFSG.EvenSmallLie.CatalogOrders.card_M23.trans (by norm_num)) (by decide)
  case M24 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 10 * 239085)
      (CFSG.Sporadic.Mathieu.card_M24.trans (by norm_num)) (by decide)
  case J1 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 3 * 21945)
      (CFSG.Sporadic.J1.card_J1.trans (by norm_num)) (by decide)
  case J2 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 7 * 4725)
      (CFSG.Sporadic.J2.card_J2.trans (by norm_num)) (by decide)
  case J3 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 7 * 392445)
      (CFSG.Sporadic.J3.card_J3.trans (by norm_num)) (by decide)
  case J4 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 21 * 41377816699065)
      (CFSG.Sporadic.J4.card_J4.trans (by norm_num)) (by decide)
  case HS =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 9 * 86625)
      (CFSG.Sporadic.HS.card_HS.trans (by norm_num)) (by decide)
  case McL =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 7 * 7016625)
      (CFSG.Sporadic.McL.card_McL.trans (by norm_num)) (by decide)
  case He =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 10 * 3935925)
      (CFSG.Sporadic.He.fam_he_order.1.trans (by norm_num)) (by decide)
  case Ru =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 14 * 8906625)
      (CFSG.Sporadic.Ru.card_Ru.trans (by norm_num)) (by decide)
  case Suz =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 13 * 54729675)
      (CFSG.Sporadic.Suz.card_Suz.trans (by norm_num)) (by decide)
  case ONan =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 9 * 900030285)
      (CFSG.Sporadic.ON.card_ON.trans (by norm_num)) (by decide)
  case Co1 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 21 * 1982582476875)
      (CFSG.Sporadic.Co1.card_Co1.trans (by norm_num)) (by decide)
  case Co2 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 18 * 161382375)
      (CFSG.Sporadic.Co2.card_Co2.trans (by norm_num)) (by decide)
  case Co3 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 10 * 484147125)
      (CFSG.Sporadic.Co3.card_Co3.trans (by norm_num)) (by decide)
  case Fi22 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 17 * 492567075)
      (CFSG.Sporadic.Fi22.card_Fi22.trans (by norm_num)) (by decide)
  case Fi23 =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 18 * 15600091832325)
      (CFSG.Sporadic.Fi23.card_Fi23.trans (by norm_num)) (by decide)
  case Fi24Prime =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 21 * 598528723330813275)
      (CFSG.Sporadic.Fi24.card_Fi24prime.trans (by norm_num)) (by decide)
  case HN =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 14 * 16664484375)
      (CFSG.Sporadic.HN.card_HN.trans (by norm_num)) (by decide)
  case Ly =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 8 * 202207730484375)
      (CFSG.Sporadic.Ly.card_Ly.trans (by norm_num)) (by decide)
  case Th =>
    have hTh : Nat.card NativeSporadic.Th = 90745943887872000 := by
      have hJ : Nat.card CFSG.Sporadic.Th.J = 90745943887872000 :=
        CFSG.Sporadic.Th.Kernel.card_J_eq CFSG.Sporadic.Th.th_kernel_facts
      rw [Nat.card_congr CFSG.Sporadic.Th.thEquivJ.toEquiv, hJ]
    exact burnsideKF_mem_orders θ (N := 2 ^ 15 * 2769346432125) (hTh.trans (by norm_num)) (by decide)
  case B =>
    exact burnsideKF_mem_orders θ (N := 2 ^ 41 * 1889375872099856765625)
      (CFSG.Monster.Existence.card_nativeB.trans
        (by norm_num [CFSG.Open.monsterBabyOrder])) (by decide)
  case M =>
    have h : Nat.card T = 2 ^ 46 * 11482618231106483731969943632999939453125 :=
      (CFSG.SeitzReduction.RankOne.card_of_mulEquiv_nativeM θ).trans (by norm_num [CFSG.Open.monsterOrder])
    rw [h]
    decide

open CFSG.EvenSmallLie.CatalogOrders in
def burnsideKF_tags : List (StatedLieTag × ℕ) :=
  [(.PSL, 2), (.PSL, 3), (.PSU, 3), (.PSp, 2), (.G2, 0), (.twistedB2, 0)]

open CFSG.EvenSmallLie.CatalogOrders in
def burnsideKF_noFam (N : ℕ) : Bool :=
  (List.range (Nat.log 2 N + 1)).all (fun f => f == 0 ||
    burnsideKF_tags.all (fun tn => lieOrd tn.1 tn.2 (2 ^ f) != N)) &&
  [60, 360, 2520, 6048, 20160, 9999360].all (fun m => m != N)

private theorem burnsideKF_noFam_orders : burnsideKF_orders.all burnsideKF_noFam = true := by
  decide +kernel

open CFSG.EvenSmallLie.CatalogOrders in
private theorem burnsideKF_lie_ne {N : ℕ} (hN : N ≠ 0) (hchk : burnsideKF_noFam N = true)
    {t : StatedLieTag} {n f : ℕ} (htn : (t, n) ∈ burnsideKF_tags) (hf : 1 ≤ f) :
    lieOrd t n (2 ^ f) ≠ N := by
  intro h
  have hts : t ∈ searchTags ∧ lieMin t ≤ n := by
    simp only [burnsideKF_tags, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at htn
    rcases htn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨by decide, by decide⟩
  obtain ⟨ht, hn⟩ := hts
  have hqd : (2 ^ f) ^ lieExp t n ∣ N := h ▸ pow_lieExp_dvd hn (2 ^ f)
  have he := one_le_lieExp ht hn
  have hfl : f ≤ Nat.log 2 N := by
    have h1 : 2 ^ (f * lieExp t n) ∣ N := by rw [pow_mul]; exact hqd
    have h2 := le_log_of_pow_dvd hN (le_refl 2) h1
    have h3 : f ≤ f * lieExp t n := Nat.le_mul_of_pos_right f he
    omega
  unfold burnsideKF_noFam at hchk
  rw [Bool.and_eq_true, List.all_eq_true] at hchk
  have h1 := hchk.1 f (List.mem_range.2 (by omega))
  rw [Bool.or_eq_true, List.all_eq_true] at h1
  rcases h1 with h1 | h1
  · have : f = 0 := by simpa using h1
    omega
  · have := h1 (t, n) htn
    simp [h] at this

open CFSG.Quasithin CFSG.EvenSmallLie.CatalogOrders CFSG.Blueprint in
private theorem burnsideKF_ni14
    {X : Type} [Group X] [IsSimpleGroup (X ⧸ Subgroup.center X)] {s : TauCeti.SporadicName}
    (hs : IsSporadic s (X ⧸ Subgroup.center X)) (hF : B42FamilyType X) :
    B42TypeTrialityD4 X ∨ B42TypeReeF4 X := by
  obtain ⟨θ⟩ := hs
  have hN : Nat.card (X ⧸ Subgroup.center X) ∈ burnsideKF_orders := burnsideKF_card_sporadic θ
  have hchk := List.all_eq_true.mp burnsideKF_noFam_orders _ hN
  have hN0 : Nat.card (X ⧸ Subgroup.center X) ≠ 0 := by
    have : ∀ N ∈ burnsideKF_orders, N ≠ 0 := by decide
    exact this _ hN
  have hfix : ∀ m ∈ [60, 360, 2520, 6048, 20160, 9999360], m ≠ Nat.card (X ⧸ Subgroup.center X) := by
    intro m hm hmN
    have h2 := (Bool.and_eq_true _ _).mp hchk |>.2
    have h3 := List.all_eq_true.mp h2 m hm
    simp [hmN] at h3
  have hlie : ∀ {t : StatedLieTag} {n f : ℕ}, (t, n) ∈ burnsideKF_tags → 1 ≤ f →
      Nat.card (X ⧸ Subgroup.center X) = lieOrd t n (2 ^ f) → False := fun htn hf h =>
    burnsideKF_lie_ne hN0 hchk htn hf h.symm
  have halt : ∀ {k : ℕ}, 2 ≤ k → Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin k)) →
      Nat.card (X ⧸ Subgroup.center X) = k.factorial / 2 := by
    intro k hk he
    obtain ⟨e⟩ := he
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  rcases hF with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨f, hf, hm⟩ := h
    exact (hlie (by simp [burnsideKF_tags]) (by omega) (card_eq_lieOrd_of_classical hm)).elim
  · obtain ⟨f, -, hf, hm⟩ := h
    exact (hlie (t := .twistedB2) (n := 0) (by simp [burnsideKF_tags]) (by omega)
      (card_eq_lieOrd_of_suzuki hm).2.2).elim
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨-, f, hf, hm⟩ := h
    exact (hlie (by simp [burnsideKF_tags]) (by omega) (card_eq_lieOrd_of_classical hm)).elim
  · obtain ⟨-, hm⟩ := h
    exact (hlie (t := .PSL) (n := 3) (f := 1) (by simp [burnsideKF_tags]) le_rfl
      (by simpa using card_eq_lieOrd_of_classical hm)).elim
  · obtain ⟨f, hf, hm⟩ := h
    exact (hlie (by simp [burnsideKF_tags]) (by omega) (card_eq_lieOrd_of_classical hm)).elim
  · obtain ⟨-, f, hf, hm⟩ := h
    exact (hlie (by simp [burnsideKF_tags]) (by omega) (card_eq_lieOrd_of_classical hm)).elim
  · obtain ⟨-, f, hf, hm⟩ := h
    exact (hlie (t := .G2) (n := 0) (by simp [burnsideKF_tags]) (by omega)
      (card_eq_lieOrd_of_exceptional hm)).elim
  · obtain ⟨-, hm⟩ := h
    have h1 := card_eq_lieOrd_of_classical hm
    have h2 : lieOrd .PSU 3 (3 ^ 1) = 6048 := by decide +kernel
    exact (hfix 6048 (by simp) (by rw [h1, h2])).elim
  · obtain ⟨-, hm, -⟩ := h
    have h1 := card_eq_lieOrd_of_classical hm
    have h2 : lieOrd .PSL 4 (2 ^ 1) = 20160 := by decide +kernel
    exact (hfix 20160 (by simp) (by rw [h1, h2])).elim
  · obtain ⟨-, hm⟩ := h
    have h1 := card_eq_lieOrd_of_classical hm
    have h2 : lieOrd .PSL 5 (2 ^ 1) = 9999360 := by decide +kernel
    exact (hfix 9999360 (by simp) (by rw [h1, h2])).elim
  · obtain ⟨-, he, -⟩ := h
    exact (hfix 60 (by simp) (by rw [halt (by norm_num) he]; norm_num)).elim
  · obtain ⟨-, he⟩ := h
    exact (hfix 360 (by simp) (by rw [halt (by norm_num) he]; norm_num)).elim
  · obtain ⟨-, -, he⟩ := h
    exact (hfix 360 (by simp) (by rw [halt (by norm_num) he]; norm_num)).elim
  · obtain ⟨-, he⟩ := h
    exact (hfix 2520 (by simp) (by rw [halt (by norm_num) he]; norm_num)).elim

open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.QuasithinUnique.Setup.Family in
private theorem burnsideKF_m24
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) (hT : B45TypeSpor .M24 ↥L) (h2 : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) :
    (MathieuCode24 L ⊤ ⊥ ∨ MathieuCocode24 L ⊤ ⊥) ∧ Nat.card V = 2 ^ 11 := by
  obtain ⟨hZ, ⟨θ⟩⟩ := hT
  have θ' : ↥L ≃* S24 := θ
  obtain ⟨hnt, hirr, -, hGN⟩ := b4Hyp_facts hHyp
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr' : IsIrrOn L := ⟨hnt, hirr⟩
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp h2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  have e := cqEquiv hZ θ'
  have hAL : A ≤ L := le_of_autInner hW hHyp.2.2.1.1 hirr' (hA.1.trans hGN) hA.isElemAbelian2 e
    (autInner_of_card_le m24_center_eq_bot' m24_mulAut_card)
  have hcardA : Nat.card A ≤ 2 ^ 6 :=
    card_le_two_pow_of_le hW hirr' hAL hA.isElemAbelian2 e m24_rank_le
  obtain ⟨⟨b, hbA⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.ne_bot
  have hV36 : Nat.card V ≤ 2 ^ 36 := card_le_of_offender_mem θ' m24_gen3 hirr
    hA.isElemAbelian2 hAV hcardA hbA (hAL hbA) (fun h => hb1 (Subtype.ext h))
  have hc := mathieuSmallIrr24_holds V hW L ⟨θ⟩ hirr hV36
  refine ⟨hc, ?_⟩
  rcases hc with hc | hc
  · exact code24_card hc
  · exact cocode24_card hc

open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.QuasithinUnique.Setup.Family in
private theorem burnsideKF_m23
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) (hT : B45TypeSpor .M23 ↥L) (h2 : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) :
    (MathieuCode23 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥) ∧ Nat.card V = 2 ^ 11 := by
  obtain ⟨hZ, ⟨θ⟩⟩ := hT
  have θ' : ↥L ≃* S23 := θ
  obtain ⟨hnt, hirr, -, hGN⟩ := b4Hyp_facts hHyp
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr' : IsIrrOn L := ⟨hnt, hirr⟩
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp h2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  have e := cqEquiv hZ θ'
  have hAL : A ≤ L := le_of_autInner hW hHyp.2.2.1.1 hirr' (hA.1.trans hGN) hA.isElemAbelian2 e
    m23_autInner
  have hcardA : Nat.card A ≤ 2 ^ 4 :=
    card_le_two_pow_of_le hW hirr' hAL hA.isElemAbelian2 e m23_rank_le
  obtain ⟨⟨b, hbA⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.ne_bot
  have hV24 : Nat.card V ≤ 2 ^ 24 := card_le_of_offender_mem θ' m23_gen3 hirr
    hA.isElemAbelian2 hAV hcardA hbA (hAL hbA) (fun h => hb1 (Subtype.ext h))
  have hc := mathieuSmallIrr23_holds V hW L ⟨θ⟩ hirr hV24
  refine ⟨hc, ?_⟩
  rcases hc with hc | hc
  · exact code23_card hc
  · exact cocode23_card hc

open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.QuasithinUnique.Setup.Family in
private theorem burnsideKF_m22
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) (hT : B45TypeSpor .M22 ↥L) (h2 : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) :
    (MathieuCode22 L ⊤ ⊥ ∨ MathieuCocode22 L ⊤ ⊥) ∧ Nat.card V = 2 ^ 10 := by
  obtain ⟨hZ, ⟨θ⟩⟩ := hT
  have θ' : ↥L ≃* S22 := θ
  obtain ⟨hnt, hirr, -, hGN⟩ := b4Hyp_facts hHyp
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr' : IsIrrOn L := ⟨hnt, hirr⟩
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp h2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  have hAidx := B45Exc.index_le_sq_of_offender2 A hAV
  have e := cqEquiv hZ θ'
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hV30 : Nat.card V ≤ 2 ^ 30 := by
    rcases out2_dichotomy_gen hW hHyp.2.2.1.1 hirr' (hA.1.trans hGN) hA.isElemAbelian2 e
      m22_center_eq_bot' m22_mulAut_card (k := 3 + 1) (p := 11) (by norm_num)
      (fun ψ hψ hψ2 => m22_outer_gen ψ hψ2 hψ) with hAL | ⟨hdisp, hcardE⟩
    · have hcardA : Nat.card A ≤ 2 ^ 4 :=
        card_le_two_pow_of_le hW hirr' hAL hA.isElemAbelian2 e m22_rank_le
      obtain ⟨⟨b, hbA⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.ne_bot
      have := card_le_of_offender_mem θ' m22_gen3 hirr hA.isElemAbelian2 hAV hcardA hbA
        (hAL hbA) (fun h => hb1 (Subtype.ext h))
      calc Nat.card V ≤ 2 ^ (6 * 4) := this
        _ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    · rw [orderOf_two_zmod_11] at hdisp
      have hE0el : IsElemAbelian2 (A ⊓ L) :=
        ⟨fun a ha b hb => hA.isElemAbelian2.1 a ha.1 b hb.1, fun a ha => hA.isElemAbelian2.2 a ha.1⟩
      have hE0card : Nat.card ↥(A ⊓ L) ≤ 2 ^ 4 :=
        card_le_two_pow_of_le hW hirr' inf_le_right hE0el e m22_rank_le
      have hA4 : 4 ≤ Nat.card A := by
        by_contra hlt
        push Not at hlt
        have hc := B45Mat.card_eq_two_pow_rk hA.isElemAbelian2
        have hA2 : Nat.card A ≤ 2 := by
          rw [hc] at hlt ⊢
          have : rk ↥A < 2 := by
            by_contra h
            push Not at h
            have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
            omega
          calc 2 ^ rk ↥A ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 2 := by norm_num
        have h1 : (fixV A).index ≤ 2 ^ 2 := hAidx.trans (Nat.pow_le_pow_left hA2 2)
        have h2 : (fixV A).index ^ (3 + 1) ≤ (2 ^ 2) ^ (3 + 1) := Nat.pow_le_pow_left h1 _
        have h3 := hdisp.trans h2
        norm_num at h3
      have hE02 : 2 ≤ Nat.card ↥(A ⊓ L) := by omega
      obtain ⟨b, hb, hb1⟩ := exists_ne_one_of_two_le hE02
      have hcardA : Nat.card A ≤ 2 ^ 5 := by
        calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L) := hcardE
          _ ≤ 2 * 2 ^ 4 := Nat.mul_le_mul le_rfl hE0card
          _ = 2 ^ 5 := by norm_num
      exact card_le_of_offender_mem θ' m22_gen3 hirr hA.isElemAbelian2 hAV hcardA hb.1 hb.2 hb1
  have hc := mathieuSmallIrr22_holds V hW L ⟨θ⟩ hirr hV30
  refine ⟨hc, ?_⟩
  rcases hc with hc | hc
  · exact code22_card hc
  · exact cocode22_card hc

open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.QuasithinUnique.Setup.Family in
private theorem burnsideKF_m12
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) (hT : B45TypeSpor .M12 ↥L) (h2 : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) :
    M12Ten L ⊤ ⊥ ∧ Nat.card V = 2 ^ 10 := by
  obtain ⟨hZ, ⟨θ⟩⟩ := hT
  have θ' : ↥L ≃* S12 := θ
  obtain ⟨hnt, hirr, -, hGN⟩ := b4Hyp_facts hHyp
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr' : IsIrrOn L := ⟨hnt, hirr⟩
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp h2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  have hAidx := B45Exc.index_le_sq_of_offender2 A hAV
  have e := cqEquiv hZ θ'
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hV24 : Nat.card V ≤ 2 ^ 24 := by
    rcases out2_dichotomy hW hHyp.2.2.1.1 hirr' (hA.1.trans hGN) hA.isElemAbelian2 e
      m12_center_eq_bot' m12_mulAut_card (r := 3) (p := 11) (by norm_num) m12_rank_le
      m12_outer_dihedral with hAL | ⟨hdisp, hcardA⟩
    · have hcardA : Nat.card A ≤ 2 ^ 3 :=
        card_le_two_pow_of_le hW hirr' hAL hA.isElemAbelian2 e m12_rank_le
      obtain ⟨⟨b, hbA⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.ne_bot
      have := card_le_of_offender_mem θ' m12_gen3 hirr hA.isElemAbelian2 hAV hcardA hbA
        (hAL hbA) (fun h => hb1 (Subtype.ext h))
      calc Nat.card V ≤ 2 ^ (6 * 3) := this
        _ ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    · rw [orderOf_two_zmod_11] at hdisp
      have hE0el : IsElemAbelian2 (A ⊓ L) :=
        ⟨fun a ha b hb => hA.isElemAbelian2.1 a ha.1 b hb.1, fun a ha => hA.isElemAbelian2.2 a ha.1⟩
      have hA4 : 4 ≤ Nat.card A := by
        by_contra hlt
        push Not at hlt
        have h1 : (fixV A).index ≤ 3 ^ 2 :=
          hAidx.trans (Nat.pow_le_pow_left (by omega) 2)
        have h2 : (fixV A).index ^ 2 ≤ (3 ^ 2) ^ 2 := Nat.pow_le_pow_left h1 _
        have h3 := hdisp.trans h2
        norm_num at h3
      have hcardE := card_le_two_mul_inf hW hHyp.2.2.1.1 hirr' (hA.1.trans hGN) hA.isElemAbelian2
        e m12_center_eq_bot' m12_mulAut_card
      have hE02 : 2 ≤ Nat.card ↥(A ⊓ L) := by omega
      obtain ⟨b, hb, hb1⟩ := exists_ne_one_of_two_le hE02
      exact card_le_of_offender_mem θ' m12_gen3 hirr hA.isElemAbelian2 hAV hcardA hb.1 hb.2 hb1
  have hc := mathieuSmallIrr12_holds V hW L ⟨θ⟩ hirr hV24
  exact ⟨hc, CFSG.Quasithin.H13.A5.M12.m12_card hc⟩

private theorem burnsideKF_card_realizes_nat {ι K V : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CommGroup V] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)}
    (h : (CFSG.Quasithin.FFModel.nat Γ).Realizes H ⊤ ⊥) :
    Nat.card V = Nat.card (Multiplicative (ι → K)) := by
  obtain ⟨-, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  have e1 := Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩)
  have e2 : Nat.card (↥(CFSG.Quasithin.FFModel.nat Γ).sec ⧸
      (CFSG.Quasithin.FFModel.nat Γ).ker.subgroupOf (CFSG.Quasithin.FFModel.nat Γ).sec) =
      Nat.card (Multiplicative (ι → K)) := by
    show Nat.card (↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
      (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf ⊤) = _
    rw [Subgroup.bot_subgroupOf]
    show (⊥ : Subgroup ↥(⊤ : Subgroup (Multiplicative (ι → K)))).index = _
    rw [Subgroup.index_bot, Subgroup.card_top]
  have e3 : Nat.card ↥(⊤ : Subgroup V) = Nat.card V := Subgroup.card_top
  rw [← e3, e1, e2]

open CFSG.Quasithin CFSG.Quasithin.HatM22 CFSG.CharacterTheory.SteinbergBY in
private theorem burnsideKF_hatM22
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) (hT : B45TypeHatM22 ↥L) (h2 : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) :
    Mhat22Twelve L ⊤ ⊥ ∧ Nat.card V = 2 ^ 12 := by
  have hcard : Nat.card V < 2 ^ 30 :=
    lt_of_le_of_lt (card_le_of_hatM22 hV hHyp hT h2) (by norm_num)
  have hR := hatM22SmallModules_holds V hV L hT hHyp.2.2.2 hcard
  refine ⟨⟨FieldFour, inferInstance, inferInstance, hatM22Γ₀, FieldFour.natCard_eq,
    isHat_hatM22Γ₀, ⟨hatM22Form, hatM22Form_det_ne_zero, hatM22Form_hermitian,
      hatM22Form_invariant⟩, hR⟩, ?_⟩
  rw [burnsideKF_card_realizes_nat hR]
  have : Nat.card (Multiplicative (Fin 6 → FieldFour)) = 4096 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    exact CFSG.Quasithin.J2Row.card_V6
  rw [this]
  norm_num

end BurnsideKF

section
open CFSG.Quasithin CFSG.Quasithin.J2Row CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
open CFSG.Quasithin CFSG.Quasithin.J2Model CFSG.Quasithin.J2Row CFSG.Quasithin.H
open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

open CFSG.Quasithin in
theorem as_K_4
    : K_4 := by
  intro V _ _ G L hK hex
  obtain ⟨s, hs⟩ := hex
  have hV := hK.elem2
  have hHyp := hK.hyp
  have h2 := hK.qhat
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hHyp.2.2.1.2.1
  have hnFF : ¬ IsFFModule G := by
    rintro ⟨A, hAG, hAne, hAel, hAV⟩
    have hA2 : IsA2 G A := ⟨hAG, hAne, hAel⟩
    have hr : rAV A ≤ 1 := (rAV_le_one_iff hV hA2).mpr hAV
    obtain ⟨B, -, hB, -⟩ := B1_4_4_le hV hA2 hr
    rcases burnsideKF_ni14 hs (b42FamilyType_of_offender hV hHyp hB) with h3 | h4
    · exact asB42TrialityD4_holds V hV G L hHyp h3 B hB
    · exact asB42ReeF4_of_large asB42ReeF4Large_holds V hV G L hHyp h4 B hB
  have hq1 : ChIJK.qc 1 < qhatOf G := by
    by_contra hn
    push Not at hn
    obtain ⟨A, hA, -, hr⟩ := kq_le_iff.mp hn
    exact hnFF ⟨A, hA.1, hA.2.1, hA.2.2, (rAV_le_one_iff hV hA).mp hr⟩
  refine ⟨?_, hnFF, hq1⟩
  obtain ⟨A, hA, hA3, hr⟩ := kq_le_iff.mp h2
  rcases b45FamilyType_of_cubic asB45DichotomyNat_holds hV hHyp hA hA3 hr with
    hB42 | hM12 | hHat | hM22 | hM23 | hM24 | hJ2
  · exfalso
    rcases burnsideKF_ni14 hs hB42 with h3 | h4
    · exact absurd h2 (not_le.mpr (asB45TrialityD4_holds V hV G L hHyp h3))
    · exact absurd h2 (not_le.mpr (asB45ReeF4_holds V hV G L hHyp h4))
  · obtain ⟨hc, hcard⟩ := burnsideKF_m12 hV hHyp hM12 h2
    exact Or.inl ⟨hM12.2, hc, hcard⟩
  · obtain ⟨hc, hcard⟩ := burnsideKF_hatM22 hV hHyp hHat h2
    exact Or.inr (Or.inl ⟨hc, hcard⟩)
  · obtain ⟨hc, hcard⟩ := burnsideKF_m22 hV hHyp hM22 h2
    exact Or.inr (Or.inr (Or.inl ⟨hM22.2, hc, hcard⟩))
  · obtain ⟨hc, hcard⟩ := burnsideKF_m23 hV hHyp hM23 h2
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hM23.2, hc, hcard⟩)))
  · obtain ⟨hc, hcard⟩ := burnsideKF_m24 hV hHyp hM24 h2
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM24.2, hc, hcard⟩))))
  · obtain ⟨hc, hcard, -⟩ := burnsideKF_j2_bound hV hHyp hJ2 h2
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hJ2.2, hc, by rw [hcard]; norm_num⟩))))

end

@[expose] def K_4_star : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    (((IsSporadic .M24 ↥L ∧ (MathieuCode24 L ⊤ ⊥ ∨ MathieuCocode24 L ⊤ ⊥)) ∨
        (IsSporadic .M23 ↥L ∧ (MathieuCode23 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥)) ∨
        (IsSporadic .M22 ↥L ∧ (MathieuCode22 L ⊤ ⊥ ∨ MathieuCocode22 L ⊤ ⊥)) ∨
        (IsSporadic .M12 ↥L ∧ M12Ten L ⊤ ⊥) ∨
        Mhat22Twelve L ⊤ ⊥) →
      (2 : ℚ) < (E3.mParam G : ℚ) ∧
      ∀ T, IsSylowTwoOf T G → ∀ A, IsA2 T A → rAV A ≤ 2 →
        (rkIdx (fixV A) : ℚ) ≤ 2 * (rk ↥A : ℚ) ∧ 1 < rk ↥A) ∧
    ((IsSporadic .J2 ↥L ∧ J2Twelve L ⊤ ⊥) →
      E3.mParam G = 4 ∧
      ∀ T, IsSylowTwoOf T G → ∀ A, IsA2 T A → rAV A ≤ 2 →
        (rkIdx (fixV A) : ℚ) ≤ 2 * (rk ↥A : ℚ) ∧ 1 < rk ↥A)

@[expose] def K_4_1_bound : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ M : Subgroup (MulAut V), (MathieuCode24 M ⊤ ⊥ ∨ MathieuCocode24 M ⊤ ⊥) →
      ∀ B : Subgroup (MulAut V), B ≤ M → IsElemAbelian2 B → rk ↥B = 2 → rk ↥(fixV B) ≤ 6

section BurnsideKG

private theorem burnsideKG_two_mul_le {V : Type} [CommGroup V] [Finite V] {X A : Subgroup
    (MulAut V)}
    (hq : ((2 : ℚ) : WithTop ℚ) ≤ CFSG.Quasithin.qOf X) (hA : CFSG.Quasithin.IsA2 X A)
    (hAq : CFSG.Quasithin.IsQuadratic A) :
    2 * CFSG.Quasithin.rk ↥A ≤ CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV A) := by
  unfold CFSG.Quasithin.qOf at hq
  rw [CFSG.Quasithin.le_kq_iff] at hq
  have h := hq A hA ((CFSG.Quasithin.isQuadratic_iff_commSeries_two A).1 hAq)
  have hr : (0 : ℚ) < (CFSG.Quasithin.rk ↥A : ℚ) := by exact_mod_cast hA.rk_pos
  unfold CFSG.Quasithin.rAV at h
  rw [le_div_iff₀ hr] at h
  have h2 : ((2 * CFSG.Quasithin.rk ↥A : ℕ) : ℚ) ≤
      (CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV A) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast h2

private theorem burnsideKG_two_mul_lt {V : Type} [CommGroup V] [Finite V] {X A : Subgroup
    (MulAut V)}
    (hq : ((2 : ℚ) : WithTop ℚ) < CFSG.Quasithin.qOf X) (hA : CFSG.Quasithin.IsA2 X A)
    (hAq : CFSG.Quasithin.IsQuadratic A) :
    2 * CFSG.Quasithin.rk ↥A < CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV A) := by
  unfold CFSG.Quasithin.qOf at hq
  rw [CFSG.Quasithin.lt_kq_iff] at hq
  have h := hq A hA ((CFSG.Quasithin.isQuadratic_iff_commSeries_two A).1 hAq)
  have hr : (0 : ℚ) < (CFSG.Quasithin.rk ↥A : ℚ) := by exact_mod_cast hA.rk_pos
  unfold CFSG.Quasithin.rAV at h
  rw [lt_div_iff₀ hr] at h
  have h2 : ((2 * CFSG.Quasithin.rk ↥A : ℕ) : ℚ) <
      (CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV A) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast h2

private theorem burnsideKG_mem_fixV_zpowers {V : Type} [CommGroup V] {x : MulAut V} {v : V} :
    v ∈ CFSG.Quasithin.fixV (Subgroup.zpowers x) ↔ x v = v := by
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x)
  · intro h y hy
    have hle : Subgroup.zpowers x ≤ MulAction.stabilizer (MulAut V) v :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h)
    exact MulAction.mem_stabilizer_iff.1 (hle hy)

private theorem burnsideKG_isQuadratic_of_fixV_eq {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1)
    {B : Subgroup (MulAut V)} (hB : CFSG.Quasithin.IsElemAbelian2 B)
    (h : ∀ b ∈ B, b ≠ 1 →
      CFSG.Quasithin.fixV (Subgroup.zpowers b) ≤ CFSG.Quasithin.fixV B) :
    CFSG.Quasithin.IsQuadratic B := by
  unfold CFSG.Quasithin.IsQuadratic CFSG.Quasithin.commV
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  by_cases hx1 : x = 1
  · subst hx1
    simp
  · refine h x hx hx1 (burnsideKG_mem_fixV_zpowers.2 ?_)
    have hx2 : x * x = 1 := by rw [← sq]; exact hB.2 x hx
    have hw : (x v * v⁻¹) * (x v * v⁻¹) = 1 := by
      have := hV (x v * v⁻¹)
      rwa [sq] at this
    have h1 : x (x v * v⁻¹) = v * (x v)⁻¹ := by
      rw [map_mul, map_inv]
      have : x (x v) = v := by
        change (x * x) v = v
        rw [hx2]
        rfl
      rw [this]
    rw [h1]
    have := mul_eq_one_iff_eq_inv.1 hw
    rw [this, mul_inv_rev, inv_inv, mul_comm]

private theorem burnsideKG_isElemAbelian2_dualSub {V : Type} [CommGroup V] {A : Subgroup (MulAut V)}
    (hA : CFSG.Quasithin.IsElemAbelian2 A) :
    CFSG.Quasithin.IsElemAbelian2 (CFSG.Quasithin.dualSub A) := by
  obtain ⟨hcomm, hsq⟩ := hA
  refine ⟨?_, ?_⟩
  · rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have : CFSG.Quasithin.dualAct V (a * b) = CFSG.Quasithin.dualAct V (b * a) := by
      rw [hcomm a ha b hb]
    exact (map_mul (CFSG.Quasithin.dualAct V) a b).symm.trans
      (this.trans (map_mul (CFSG.Quasithin.dualAct V) b a))
  · rintro x ⟨a, ha, rfl⟩
    exact (map_pow (CFSG.Quasithin.dualAct V) a 2).symm.trans (by rw [hsq a ha, map_one]; rfl)

private theorem burnsideKG_two_le_rk {V : Type} [CommGroup V] [Finite V] {D : Subgroup (MulAut V)}
    (hDe : CFSG.Quasithin.IsElemAbelian2 D) (hDc : ¬ IsCyclic ↥D) :
    2 ≤ CFSG.Quasithin.rk ↥D := by
  by_contra hlt
  push Not at hlt
  apply hDc
  have hc : Nat.card ↥D = 2 ^ CFSG.Quasithin.rk ↥D :=
    CFSG.Quasithin.card_eq_two_pow_of_isPGroup hDe.isPGroup
  interval_cases h : CFSG.Quasithin.rk ↥D
  · have h1 : Nat.card ↥D = 1 := by simpa using hc
    haveI : Subsingleton ↥D := (Nat.card_eq_one_iff_unique.1 h1).1
    infer_instance
  · have h2 : Nat.card ↥D = 2 := by simpa using hc
    haveI : Fact (Nat.Prime (Nat.card ↥D)) := ⟨by rw [h2]; exact Nat.prime_two⟩
    exact isCyclic_of_prime_card h2

end BurnsideKG

section

theorem as_K_4_1_bound : K_4_1_bound := by
  intro V _ _ hV M hM B hBM hBe hBr
  have hLM : CFSG.Quasithin.H.Mathieu.IsOver M M := ⟨le_rfl, Subgroup.le_normalizer⟩
  obtain ⟨hcard, h4, hq⟩ : Nat.card V = 2 ^ 11 ∧
      (∀ t ∈ M, orderOf t = 2 →
        4 ≤ CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV (Subgroup.zpowers t))) ∧
      ((2 : ℚ) : WithTop ℚ) < CFSG.Quasithin.qOf M := by
    rcases hM with h | h
    · exact ⟨CFSG.Quasithin.H.Mathieu.code24_card h,
        fun t ht ho => CFSG.Quasithin.H.Mathieu.code24_four_le_rkIdx hLM h ht ho,
        CFSG.Quasithin.B45Mat.two_lt_qOf_code24 hLM h⟩
    · exact ⟨CFSG.Quasithin.H.Mathieu.cocode24_card h,
        fun t ht ho => CFSG.Quasithin.H.Mathieu.cocode24_four_le_rkIdx hLM h ht ho,
        CFSG.Quasithin.B45Mat.two_lt_qOf_cocode24 hLM h⟩
  have hrkV : CFSG.Quasithin.rk V = 11 := by
    unfold CFSG.Quasithin.rk
    rw [hcard, padicValNat.prime_pow]
  have hne : B ≠ ⊥ := by
    rintro rfl
    rw [CFSG.Quasithin.rk_bot] at hBr
    omega
  have h5 : 5 ≤ CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV B) := by
    by_contra hlt
    push Not at hlt
    have hfix : ∀ b ∈ B, b ≠ 1 →
        CFSG.Quasithin.fixV (Subgroup.zpowers b) ≤ CFSG.Quasithin.fixV B := by
      intro b hb hb1
      have hb2 : orderOf b = 2 := orderOf_eq_prime (hBe.2 b hb) hb1
      have hle : CFSG.Quasithin.fixV B ≤ CFSG.Quasithin.fixV (Subgroup.zpowers b) :=
        fun v hv x hx => hv x ((Subgroup.zpowers_le.2 hb) hx)
      have h1 := CFSG.Quasithin.rkIdx_anti hle
      have h2 := h4 b (hBM hb) hb2
      have h3 := CFSG.Quasithin.rk_add_rkIdx (CFSG.Quasithin.fixV B)
      have h3' := CFSG.Quasithin.rk_add_rkIdx (CFSG.Quasithin.fixV (Subgroup.zpowers b))
      exact (CFSG.Quasithin.eq_of_le_of_rk_le hV hle (by omega)).ge
    have hq' : CFSG.Quasithin.IsQuadratic B := burnsideKG_isQuadratic_of_fixV_eq hV hBe hfix
    have h6 := burnsideKG_two_mul_lt hq ⟨hBM, hne, hBe⟩ hq'
    omega
  have h7 := CFSG.Quasithin.rk_add_rkIdx (CFSG.Quasithin.fixV B)
  omega

end

@[expose] def K_4_1_lemma : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ((IsSporadic .M23 ↥L ∧ (MathieuCode23 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥)) ∨
      (IsSporadic .M24 ↥L ∧ (MathieuCode24 L ⊤ ⊥ ∨ MathieuCocode24 L ⊤ ⊥))) →
    ∀ T, IsSylowTwoOf T G → ∀ A ∈ Qset T, 2 < rk ↥A

section

theorem as_K_4_1_lemma : K_4_1_lemma := by
  intro V _ _ G L hK hL T hT A hA
  exfalso
  obtain ⟨-, -, hLG, hGN⟩ := CFSG.Quasithin.B45Mat.b4Hyp_facts hK.hyp
  have hLG' : CFSG.Quasithin.H.Mathieu.IsOver L G := ⟨hLG, hGN⟩
  have hq : ((2 : ℚ) : WithTop ℚ) < CFSG.Quasithin.qOf G := by
    rcases hL with ⟨-, hc | hc⟩ | ⟨-, hc | hc⟩
    · exact CFSG.Quasithin.B45Mat.two_lt_qOf_code23 hLG' hc
    · exact CFSG.Quasithin.B45Mat.two_lt_qOf_cocode23 hLG' hc
    · exact CFSG.Quasithin.B45Mat.two_lt_qOf_code24 hLG' hc
    · exact CFSG.Quasithin.B45Mat.two_lt_qOf_cocode24 hLG' hc
  obtain ⟨⟨hA2, hAr⟩, hAq⟩ := hA
  have hAG : CFSG.Quasithin.IsA2 G A := ⟨hA2.1.trans hT.1, hA2.2.1, hA2.2.2⟩
  exact absurd (CFSG.Quasithin.kq_le_iff.2 ⟨A, hAG, hAq, hAr⟩) (not_le.2 hq)

end

@[expose] def K_4_2_lemma : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ M : Subgroup (MulAut V), (MathieuCode24 M ⊤ ⊥ ∨ MathieuCocode24 M ⊤ ⊥) →
      ∀ t : MulAut V, t ∈ M → t ^ 2 = 1 → t ≠ 1 → ¬ IsTwoCentralIn M t →
        ∀ D : Subgroup (MulAut V), D ≤ M → IsElemAbelian2 D → ¬ IsCyclic ↥D → IsQuadratic D →
          (∀ d ∈ D, d ≠ 1 → ∃ g ∈ M, d = g * t * g⁻¹) → rk ↥D ≤ 2

section BurnsideK42

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat in
private theorem burnsideK42_quad_searches :
    forallGreedyAll pos24s2 inv24s2 (noQuadRank3 11 act24s2) 6 [] = true ∧
    forallGreedyAll pos24s2 inv24s2 (noQuadRank3 11 actC24s2) 6 [] = true := by
  obtain ⟨h1, h2⟩ := Certificates.certificate7275
  exact ⟨h1, h2⟩

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.Code in
private theorem burnsideK42_rk_le_two
    {V : Type} [CommGroup V] [Finite V] {M : Subgroup (MulAut V)}
    (hM : MathieuCode24 M ⊤ ⊥ ∨ MathieuCocode24 M ⊤ ⊥) {D : Subgroup (MulAut V)} (hDM : D ≤ M)
    (hDe : IsElemAbelian2 D) (hDq : IsQuadratic D) : rk ↥D ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have hLM : IsOver M M := ⟨le_rfl, Subgroup.le_normalizer⟩
  have hc : Nat.card D = 2 ^ rk ↥D := card_eq_two_pow_rk hDe
  have hq : commSeries D 2 = ⊥ := (isQuadratic_iff_commSeries_two D).1 hDq
  rcases hM with h | h
  · obtain ⟨e, he⟩ := code24_std h
    have hk := code24_card_le hLM h hDM hDe hc
    obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psiC24 (rhoC11_injective _ _) phi24
      (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2)
      ((forallGreedyP_eq pos24s2_eq _ _ []).symm.trans
        (forallGreedyAll_le 6 [] burnsideK42_quad_searches.2 _ hk)) e
      (map_le_of_normalizer hLM he normalizer_rhoC11_autPerm hDM) hDe hc
    have hact : ChainAct (MaskCoords.ofEquiv (twistEquiv e psiC24 g)) (chainAut e psiC24 phi24 g)
        actC24s2 :=
      chainAct_twist e psiC24 phi24 g (fun s _ hm => psiC24_phi24 s hm)
        (fun s _ hm => by
          rw [actC24s2, actM_matsC11 T24s2 (mats := matsC24) rfl s hm]
          exact actC11_lt _ _)
    have hqb := quadBasisOK_of_quadratic hact hchain hq
    have hlen := rk_of_chain hchain
      (chainAut_injective (rhoC11_injective _ _) (T24s2.toSub_injective _ _) g) hind
    simp only [noQuadRank3, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hpred
    rcases hpred with h3 | h3
    · omega
    · rw [hqb] at h3
      exact absurd h3 (by simp)
  · obtain ⟨e, he⟩ := cocode24_std h
    have hk := cocode24_card_le hLM h hDM hDe hc
    obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel rhoM24 (rho11_injective _ _) phi24
      (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2)
      ((forallGreedyP_eq pos24s2_eq _ _ []).symm.trans
        (forallGreedyAll_le 6 [] burnsideK42_quad_searches.1 _ hk)) e
      (map_le_range24 hLM he hDM) hDe hc
    have hqb := quadBasisOK_of_quadratic (chainAct24 e g) hchain hq
    have hlen := rk_of_chain hchain (chainAut24_injective e g) hind
    simp only [noQuadRank3, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hpred
    rcases hpred with h3 | h3
    · omega
    · rw [hqb] at h3
      exact absurd h3 (by simp)

section Chain
variable {G X : Type*} [Group G] [MulAction G X]

private theorem burnsideK42_card_mul_stab_le [Finite G] (H : Subgroup G) (x : X) (R : Finset X)
    (hR : ∀ y ∈ R, ∃ h ∈ H, h • x = y) :
    R.card * Nat.card ↥(H ⊓ MulAction.stabilizer G x) ≤ Nat.card ↥H := by
  classical
  set N : Subgroup G := H ⊓ MulAction.stabilizer G x with hN
  have hNH : N ≤ H := inf_le_left
  set N' : Subgroup ↥H := N.subgroupOf H with hN'
  have hcard : Nat.card ↥H = Nat.card (↥H ⧸ N') * Nat.card ↥N' :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N'
  have hNN' : Nat.card ↥N' = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  have hle : R.card ≤ Nat.card (↥H ⧸ N') := by
    choose! f hfH hfx using hR
    let g : R → ↥H ⧸ N' := fun y => QuotientGroup.mk (⟨f y, hfH y y.2⟩ : ↥H)
    have hinj : Function.Injective g := by
      intro y y' hyy'
      have h1 : (QuotientGroup.mk (⟨f y, hfH y y.2⟩ : ↥H) : ↥H ⧸ N') =
          QuotientGroup.mk ⟨f y', hfH y' y'.2⟩ := hyy'
      rw [QuotientGroup.eq] at h1
      have h2 : (⟨f y, hfH y y.2⟩ : ↥H)⁻¹ * ⟨f y', hfH y' y'.2⟩ ∈ N' := h1
      rw [hN', Subgroup.mem_subgroupOf] at h2
      have h3 : ((f y)⁻¹ * f y') ∈ MulAction.stabilizer G x := (Subgroup.mem_inf.1 h2).2
      rw [MulAction.mem_stabilizer_iff, mul_smul] at h3
      have h4 : f y' • x = f y • x := by
        have := congrArg (fun z => f y • z) h3
        simpa using this
      apply Subtype.ext
      rw [← hfx y y.2, ← hfx y' y'.2]
      exact h4.symm
    have := Nat.card_le_card_of_injective g hinj
    simpa using this
  calc R.card * Nat.card ↥N ≤ Nat.card (↥H ⧸ N') * Nat.card ↥N' := by
        rw [hNN']; exact Nat.mul_le_mul_right _ hle
    _ = Nat.card ↥H := hcard.symm

def burnsideK42_ChainHyp : Subgroup G → List (X × Finset X) → Prop
  | _, [] => True
  | H, (x, R) :: L => (∀ y ∈ R, ∃ h ∈ H, h • x = y) ∧
      burnsideK42_ChainHyp (H ⊓ MulAction.stabilizer G x) L

def burnsideK42_chainFinal : Subgroup G → List (X × Finset X) → Subgroup G
  | H, [] => H
  | H, (x, _) :: L => burnsideK42_chainFinal (H ⊓ MulAction.stabilizer G x) L

private theorem burnsideK42_chain_card_le [Finite G] :
    ∀ (L : List (X × Finset X)) (H : Subgroup G), burnsideK42_ChainHyp H L →
      (L.map fun p => p.2.card).prod * Nat.card ↥(burnsideK42_chainFinal H L) ≤ Nat.card ↥H
  | [], H, _ => by simp [burnsideK42_chainFinal]
  | (x, R) :: L, H, ⟨h1, h2⟩ => by
    have ih := burnsideK42_chain_card_le L (H ⊓ MulAction.stabilizer G x) h2
    have h3 := burnsideK42_card_mul_stab_le H x R h1
    simp only [List.map_cons, List.prod_cons, burnsideK42_chainFinal]
    calc R.card * (L.map fun p => p.2.card).prod * Nat.card ↥(burnsideK42_chainFinal
          (H ⊓ MulAction.stabilizer G x) L)
        = R.card * ((L.map fun p => p.2.card).prod * Nat.card ↥(burnsideK42_chainFinal
          (H ⊓ MulAction.stabilizer G x) L)) := by ring
      _ ≤ R.card * Nat.card ↥(H ⊓ MulAction.stabilizer G x) := Nat.mul_le_mul_left _ ih
      _ ≤ Nat.card ↥H := h3

private theorem burnsideK42_mem_chainFinal : ∀ (L : List (X × Finset X)) (H : Subgroup G) (g : G),
    g ∈ burnsideK42_chainFinal H L ↔ g ∈ H ∧ ∀ p ∈ L, g • p.1 = p.1
  | [], H, g => by simp [burnsideK42_chainFinal]
  | (x, R) :: L, H, g => by
    rw [burnsideK42_chainFinal, burnsideK42_mem_chainFinal L, Subgroup.mem_inf,
      MulAction.mem_stabilizer_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

private theorem burnsideK42_chainHyp_of_levels : ∀ (L : List (X × Finset X)) (H : Subgroup G),
    (∀ j (hj : j < L.length), ∀ y ∈ (L[j]).2,
      ∃ h ∈ burnsideK42_chainFinal H (L.take j), h • (L[j]).1 = y) →
    burnsideK42_ChainHyp H L
  | [], H, _ => trivial
  | (x, R) :: L, H, h => by
    refine ⟨fun y hy => ?_, burnsideK42_chainHyp_of_levels L _ fun j hj y hy => ?_⟩
    · exact h 0 (by simp) y hy
    · exact h (j + 1) (by simpa using hj) y hy

end Chain

section ElemAbelian

private theorem burnsideK42_isE2 {X : Type} [Group X] (hc : ∀ a b : X, a * b = b * a)
    (hsq : ∀ a : X, a ^ 2 = 1) {n : ℕ} (hcard : Nat.card X = 2 ^ n) :
    Nonempty (X ≃* Multiplicative (Fin n → ZMod 2)) := by
  letI : CommGroup X := { ‹Group X› with mul_comm := hc }
  have h2 : ∀ x : Additive X, (2 : ℕ) • x = 0 := fun x => by
    have := hsq (Additive.toMul x)
    apply Additive.toMul.injective
    simpa using this
  letI : Module (ZMod 2) (Additive X) := AddCommGroup.zmodModule h2
  haveI : Finite (Additive X) := by
    have : 0 < Nat.card X := by rw [hcard]; positivity
    exact Nat.finite_of_card_ne_zero this.ne'
  have hfr : Module.finrank (ZMod 2) (Additive X) = n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X)
    rw [Nat.card_zmod] at h1
    have h3 : Nat.card (Additive X) = Nat.card X := rfl
    rw [h3, hcard] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  let e : Additive X ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    (Module.finBasisOfFinrankEq (ZMod 2) (Additive X) hfr).equivFun
  exact ⟨{ toFun := fun x => Multiplicative.ofAdd (e (Additive.ofMul x))
           invFun := fun y => Additive.toMul (e.symm (Multiplicative.toAdd y))
           left_inv := fun x => by simp
           right_inv := fun y => by simp
           map_mul' := fun a b => by simp [ofAdd_add] }⟩

end ElemAbelian

section Zpowers

private theorem burnsideK42_zpowers_sq {G : Type*} [Group G] {a : G} (ha : a * a = 1) {x : G}
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
  · left
    show a ^ (2 * j) = 1
    rw [zpow_mul, h2, one_zpow]
  · right
    show a ^ (2 * j + 1) = a
    rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

end Zpowers

section Arr
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

abbrev burnsideK42_K : Type := ↥CFSG.Monster.Code.AutPerm

@[expose] def burnsideK42_permArr (σ : Equiv.Perm (Fin 24)) : Array ℕ :=
  Array.ofFn (n := 24) fun i => (σ i : ℕ)

private theorem burnsideK42_hasArr_permArr (σ : Equiv.Perm (Fin 24)) :
    HasArr σ (burnsideK42_permArr σ) := by
  intro i
  simp [burnsideK42_permArr]

private theorem burnsideK42_arrMul_get (a b : Array ℕ) (i : Fin 24) :
    (arrMul a b)[(i : ℕ)]! = a[b[(i : ℕ)]!]! := by
  rw [arrMul, getElem!_pos _ (i : ℕ) (by simp), Array.getElem_ofFn]

private theorem burnsideK42_hasArr_mul {σ τ : Equiv.Perm (Fin 24)} {a b : Array ℕ} (hσ : HasArr σ a)
    (hτ : HasArr τ b) : HasArr (σ * τ) (arrMul a b) := by
  intro i
  rw [Equiv.Perm.mul_apply, burnsideK42_arrMul_get, hσ (τ i), hτ i]

private theorem burnsideK42_hasArr_one : HasArr (1 : Equiv.Perm (Fin 24)) idArr := by
  intro i
  simp [idArr]

private theorem burnsideK42_hasArr_ext {σ τ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a)
    (hτ : HasArr τ a) : σ = τ := by
  ext i
  exact (hσ i).trans (hτ i).symm

theorem burnsideK42_inAutOK_parts {a : Array ℕ} (h : inAutOK a = true) :
    InvPairOK 24 a (invArr a) = true ∧ autArrOK a (invArr a) = true := by
  simpa [inAutOK] using h

@[expose] def burnsideK42_kOfArr (a : Array ℕ) (h : inAutOK a = true) : burnsideK42_K :=
  ⟨permOfArr 24 a (invArr a) (burnsideK42_inAutOK_parts h).1,
    mem_AutPerm_of_arr (burnsideK42_inAutOK_parts h).1 (burnsideK42_inAutOK_parts h).2⟩

private theorem burnsideK42_kOfArr_hasArr (a : Array ℕ) (h : inAutOK a = true) :
    HasArr (burnsideK42_kOfArr a h : Equiv.Perm (Fin 24)) a :=
  hasArr_permOfArr (burnsideK42_inAutOK_parts h).1

private theorem burnsideK42_kOfArr_inv_hasArr (a : Array ℕ) (h : inAutOK a = true) :
    HasArr ((burnsideK42_kOfArr a h)⁻¹ : burnsideK42_K) (invArr a) :=
  hasArr_permOfArr_inv (burnsideK42_inAutOK_parts h).1

private theorem burnsideK42_derivOK_sound {step : ℕ → ℕ → ℕ} {ngen x0 : ℕ} {tab : Array (ℕ × ℕ × ℕ)}
    (h : derivOK step ngen x0 tab = true) (P : ℕ → Prop) (hx0 : P x0)
    (hstep : ∀ g < ngen, ∀ y, P y → P (step g y)) : ∀ i < tab.size, P tab[i]!.1 := by
  simp only [derivOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨hpos, h0⟩, hall⟩ := h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [h0]
      exact hx0
    · have := hall i hi
      simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at this
      rcases this with h | ⟨⟨hpar, hgen⟩, hval⟩
      · exact absurd h hi0
      · rw [hval]
        exact hstep _ hgen _ (ih _ hpar (by omega))

private theorem burnsideK42_smul_point (σ : burnsideK42_K) (i : Fin 24) :
    σ • i = (σ : Equiv.Perm (Fin 24)) i := rfl

@[expose] def burnsideK42_ptL : List (Fin 24 × Finset (Fin 24)) :=
  (List.range 6).map fun i =>
    (Fin.ofNat 24 ptBase[i]!, ((ptTab i).toList.map fun e => Fin.ofNat 24 e.1).toFinset)

private theorem burnsideK42_ptL_getElem (j : ℕ) (hj : j < 6) :
    burnsideK42_ptL[j]'(by simpa [burnsideK42_ptL] using hj) =
      (Fin.ofNat 24 ptBase[j]!, ((ptTab j).toList.map fun e => Fin.ofNat 24 e.1).toFinset) := by
  simp [burnsideK42_ptL]

private theorem burnsideK42_ptChain_parts :
    ptBase.length = 6 ∧ ptGens.length = 6 ∧ (∀ x ∈ ptBase, x < 24) ∧ ∀ i < 6,
      ((∀ g ∈ ptGens[i]!, inAutOK g = true ∧ ∀ b ∈ ptBase.take i, g[b]! = b) ∧
      derivOK (fun g y => ((ptGens[i]!)[g]!)[y]!) (ptGens[i]!).length ptBase[i]! (ptTab i) = true ∧
      tabNodupLt 24 (ptTab i) = true ∧ (ptTab i).size = [24, 23, 22, 21, 20, 3][i]!) := by
  have hok := (Certificates.certificate7276).2.1
  simp only [ptChainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨⟨⟨hbl, hgl⟩, hlt⟩, hlev⟩ := hok
  refine ⟨hbl, hgl, hlt, fun i hi => ?_⟩
  obtain ⟨⟨⟨hg, hd⟩, hn⟩, hs⟩ := hlev i hi
  exact ⟨hg, hd, hn, hs⟩

private theorem burnsideK42_ofNat_val {b : ℕ} (hb : b < 24) : ((Fin.ofNat 24 b : Fin 24) : ℕ) =
    b := by
  simp [Fin.ofNat, Nat.mod_eq_of_lt hb]

private theorem burnsideK42_apply_ofNat {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (h : HasArr σ
    a) {b : ℕ}
    (hb : b < 24) : ((σ (Fin.ofNat 24 b) : Fin 24) : ℕ) = a[b]! := by
  have := h (Fin.ofNat 24 b)
  rwa [burnsideK42_ofNat_val hb] at this

private theorem burnsideK42_ptL_hyp :
    burnsideK42_ChainHyp (⊤ : Subgroup burnsideK42_K) burnsideK42_ptL := by
  obtain ⟨hbl, hgl, hlt, hlev⟩ := burnsideK42_ptChain_parts
  apply burnsideK42_chainHyp_of_levels
  intro j hj y hy
  have hj6 : j < 6 := by simpa [burnsideK42_ptL] using hj
  rw [burnsideK42_ptL_getElem j hj6] at hy ⊢
  obtain ⟨hg, hd, hn, -⟩ := hlev j hj6
  set H : Subgroup burnsideK42_K := burnsideK42_chainFinal ⊤ (burnsideK42_ptL.take j) with hH
  have hgenH : ∀ g (hgm : g ∈ ptGens[j]!), burnsideK42_kOfArr g (hg g hgm).1 ∈ H := by
    intro g hgm
    rw [hH, burnsideK42_mem_chainFinal]
    refine ⟨Subgroup.mem_top _, fun p hp => ?_⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hp
    have hlj : l < j := by have := hl; simp only [List.length_take] at this; omega
    have hl6 : l < 6 := by omega
    rw [List.getElem_take, burnsideK42_ptL_getElem l hl6, burnsideK42_smul_point]
    have hb : ptBase[l]! < 24 := hlt _ (by
      rw [getElem!_pos ptBase l (by omega)]; exact List.getElem_mem _)
    have hfix := (hg g hgm).2 ptBase[l]! (by
      rw [getElem!_pos ptBase l (by omega)]
      exact List.mem_iff_getElem.2 ⟨l, by simp [List.length_take]; omega, by simp⟩)
    apply Fin.ext
    simp only
    rw [burnsideK42_apply_ofNat (burnsideK42_kOfArr_hasArr g (hg g hgm).1) hb, hfix,
      burnsideK42_ofNat_val hb]
  have hP := burnsideK42_derivOK_sound hd
    (fun v => v < 24 ∧ ∃ h ∈ H, h • (Fin.ofNat 24 ptBase[j]! : Fin 24) = Fin.ofNat 24 v)
    ⟨hlt _ (by rw [getElem!_pos ptBase j (by omega)]; exact List.getElem_mem _), 1, H.one_mem,
      by simp⟩
    (by
      intro g hgl v ⟨hv, h, hhH, hh⟩
      have hgm : (ptGens[j]!)[g]! ∈ ptGens[j]! := by
        rw [getElem!_pos (ptGens[j]!) g hgl]; exact List.getElem_mem _
      set σ := burnsideK42_kOfArr ((ptGens[j]!)[g]!) (hg _ hgm).1 with hσ
      have hσarr := burnsideK42_kOfArr_hasArr ((ptGens[j]!)[g]!) (hg _ hgm).1
      have hlt' : ((ptGens[j]!)[g]!)[v]! < 24 := by
        have := burnsideK42_apply_ofNat hσarr hv
        rw [← this]; exact (((σ : burnsideK42_K) : Equiv.Perm (Fin 24)) (Fin.ofNat 24 v)).2
      refine ⟨hlt', σ * h, H.mul_mem (hgenH _ hgm) hhH, ?_⟩
      rw [mul_smul, hh, burnsideK42_smul_point]
      apply Fin.ext
      rw [burnsideK42_apply_ofNat hσarr hv, burnsideK42_ofNat_val hlt'])
  have hy' : y ∈ ((ptTab j).toList.map fun e => Fin.ofNat 24 e.1) := by
    simpa using hy
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy'
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 he
  have hi' : i < (ptTab j).size := by simpa using hi
  have hPi := hP i hi'
  have hei : (ptTab j)[i]!.1 = e.1 := by
    rw [getElem!_pos (ptTab j) i hi', ← hie]
    simp
  rw [hei] at hPi
  exact hPi.2

private theorem burnsideK42_ofNat_injOn {x y : ℕ} (hx : x < 24) (hy : y < 24)
    (h : (Fin.ofNat 24 x : Fin 24) = Fin.ofNat 24 y) : x = y := by
  have := congrArg Fin.val h
  rwa [burnsideK42_ofNat_val hx, burnsideK42_ofNat_val hy] at this

private theorem burnsideK42_ptL_card_get (j : ℕ) (hj : j < 6) :
    (burnsideK42_ptL[j]'(by simpa [burnsideK42_ptL] using hj)).2.card =
      [24, 23, 22, 21, 20, 3][j]! := by
  obtain ⟨-, -, -, hlev⟩ := burnsideK42_ptChain_parts
  obtain ⟨-, -, hn, hs⟩ := hlev j hj
  rw [burnsideK42_ptL_getElem j hj]
  simp only [tabNodupLt, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at hn
  obtain ⟨hnd, hlt⟩ := hn
  have hlt' : ∀ x ∈ (ptTab j).toList.map (·.1), x < 24 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
    have := hlt i (by simpa using hi)
    simpa using this
  have hnd' : ((ptTab j).toList.map fun e => Fin.ofNat 24 e.1).Nodup := by
    have h1 := hnd.map_on (f := fun x : ℕ => (Fin.ofNat 24 x : Fin 24))
      (fun x hx y hy h => burnsideK42_ofNat_injOn (hlt' x hx) (hlt' y hy) h)
    have h2 : ((ptTab j).toList.map fun e => (Fin.ofNat 24 e.1 : Fin 24)) =
        ((ptTab j).toList.map (·.1)).map (fun x : ℕ => (Fin.ofNat 24 x : Fin 24)) := by
      rw [List.map_map]; rfl
    rw [h2]
    exact h1
  rw [List.toFinset_card_of_nodup hnd', List.length_map, Array.length_toList, hs]

private theorem burnsideK42_ptL_cards :
    burnsideK42_ptL.map (fun p => p.2.card) = [24, 23, 22, 21, 20, 3] := by
  apply List.ext_getElem
  · simp [burnsideK42_ptL]
  · intro j h1 h2
    have hj : j < 6 := by simpa [burnsideK42_ptL] using h2
    have := burnsideK42_ptL_card_get j hj
    simp only [List.getElem_map]
    rw [this]
    interval_cases j <;> rfl

private theorem burnsideK42_ptL_final_card :
    Nat.card ↥(burnsideK42_chainFinal (⊤ : Subgroup burnsideK42_K) burnsideK42_ptL) ≤ 16 := by
  have h := burnsideK42_chain_card_le burnsideK42_ptL ⊤ burnsideK42_ptL_hyp
  rw [burnsideK42_ptL_cards, Subgroup.card_top, CFSG.Monster.Code.card_AutPerm] at h
  norm_num at h
  omega

@[expose] def burnsideK42_e0 : G6.PermMod 24 := Multiplicative.ofAdd (bvec 24 e0mask)

private theorem burnsideK42_octadPts_e0 :
    CFSG.ASVolI.ChIJK.octadPts burnsideK42_e0 = {x : Fin 24 | (x : ℕ) ∈ octPts} := by
  ext x
  simp only [CFSG.ASVolI.ChIJK.octadPts, burnsideK42_e0, Set.mem_ofPred_eq, toAdd_ofAdd, bvec_apply]
  fin_cases x <;> decide

@[expose] def burnsideK42_KO0 : Subgroup burnsideK42_K :=
  (fixingSubgroup (Equiv.Perm (Fin 24)) (CFSG.ASVolI.ChIJK.octadPts burnsideK42_e0)).subgroupOf
    CFSG.Monster.Code.AutPerm

private theorem burnsideK42_mem_KO0 {γ : burnsideK42_K} :
    γ ∈ burnsideK42_KO0 ↔ ∀ i ∈ octPts, ∀ h : i < 24, (γ : Equiv.Perm (Fin 24)) ⟨i, h⟩ = ⟨i, h⟩ := by
  simp only [burnsideK42_KO0, Subgroup.mem_subgroupOf, mem_fixingSubgroup_iff,
    burnsideK42_octadPts_e0, Set.mem_ofPred_eq, Equiv.Perm.smul_def]
  constructor
  · intro hγ i hi h
    exact hγ ⟨i, h⟩ hi
  · intro hγ y hy
    exact hγ y.1 hy y.2

private theorem burnsideK42_length_le_card {G : Type*} [Group G] [Finite G] (H : Subgroup G) (l
    : List G)
    (hnd : l.Nodup) (hl : ∀ x ∈ l, x ∈ H) : l.length ≤ Nat.card H := by
  classical
  have hsub : ((l.toFinset : Finset G) : Set G) ⊆ (H : Set G) := by
    intro x hx
    simp only [Finset.mem_coe, List.mem_toFinset] at hx
    exact hl x hx
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ = ((l.toFinset : Finset G) : Set G).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (H : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card H := Nat.card_coe_set_eq _

private theorem burnsideK42_octPts_lt : ∀ i ∈ octPts, i < 24 := by decide

private theorem burnsideK42_ptBase_mem : ∀ x ∈ ptBase, x ∈ octPts := by decide

private theorem burnsideK42_ptBase_lt : ∀ x ∈ ptBase, x < 24 := by decide

private theorem burnsideK42_KO0_le_chain :
    burnsideK42_KO0 ≤ burnsideK42_chainFinal (⊤ : Subgroup burnsideK42_K) burnsideK42_ptL := by
  intro γ hγ
  rw [burnsideK42_mem_chainFinal]
  refine ⟨Subgroup.mem_top _, fun p hp => ?_⟩
  obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hp
  have hl6 : l < 6 := by simpa [burnsideK42_ptL] using hl
  rw [burnsideK42_ptL_getElem l hl6, burnsideK42_smul_point]
  have hbl : ptBase.length = 6 := by decide
  have hmem : ptBase[l]! ∈ ptBase := by
    rw [getElem!_pos ptBase l (by omega)]; exact List.getElem_mem _
  have hb : ptBase[l]! < 24 := burnsideK42_ptBase_lt _ hmem
  have := (burnsideK42_mem_KO0.1 hγ) ptBase[l]! (burnsideK42_ptBase_mem _ hmem) hb
  apply Fin.ext
  have h2 : (Fin.ofNat 24 ptBase[l]! : Fin 24) = ⟨ptBase[l]!, hb⟩ := Fin.ext (burnsideK42_ofNat_val hb)
  rw [h2, this]

private theorem burnsideK42_KO0_card_le :
    Nat.card ↥burnsideK42_KO0 ≤ 16 :=
  (Subgroup.card_le_of_le burnsideK42_KO0_le_chain).trans burnsideK42_ptL_final_card

section TArr

@[expose] def burnsideK42_Tsub : Subgroup burnsideK42_K := (phi24 : T24s2.Elem →* burnsideK42_K).range

private theorem burnsideK42_phi24_hasArr (s : T24s2.Elem) :
    HasArr ((phi24 s : burnsideK42_K) : Equiv.Perm (Fin 24)) (tArr s.idx) :=
  T24s2.hasArr_toSub _ _ s

private theorem burnsideK42_phi24_injective : Function.Injective (phi24 : T24s2.Elem →*
    burnsideK42_K) :=
  T24s2.toSub_injective _ _

theorem burnsideK42_kIdx_lt {p : ℕ} (hp : p ∈ kIdx ()) : p < T24s2.n := by
  simp only [kIdx, List.mem_filter, List.mem_range] at hp
  exact hp.1

private theorem burnsideK42_kIdx_fixes {p : ℕ} (hp : p ∈ kIdx ()) : fixesOct (tArr p) = true := by
  simp only [kIdx, List.mem_filter] at hp
  exact hp.2

private theorem burnsideK42_phi24_mem_KO0 (s : T24s2.Elem) (h : fixesOct (tArr s.idx) = true) :
    (phi24 s : burnsideK42_K) ∈ burnsideK42_KO0 := by
  rw [burnsideK42_mem_KO0]
  intro i hi hi24
  apply Fin.ext
  have h1 := burnsideK42_phi24_hasArr s ⟨i, hi24⟩
  simp only at h1
  rw [h1]
  simp only [fixesOct, List.all_eq_true, beq_iff_eq] at h
  exact h i hi

@[expose] def burnsideK42_kList : List burnsideK42_K :=
  (kIdx ()).pmap (fun p hp => (phi24 (⟨p, hp⟩ : T24s2.Elem) : burnsideK42_K))
    (fun _ hp => burnsideK42_kIdx_lt hp)

private theorem burnsideK42_kList_length (hk : (kIdx ()).length = 16) :
    burnsideK42_kList.length = 16 := by
  simp [burnsideK42_kList, hk]

private theorem burnsideK42_kList_nodup (hnd : (kIdx ()).Nodup) : burnsideK42_kList.Nodup := by
  refine List.Nodup.pmap (fun p hp q hq h => ?_) hnd
  have := burnsideK42_phi24_injective h
  exact congrArg (fun q : T24s2.Elem => q.idx) this

structure burnsideK42_Lists : Prop where
  z0_lt : z0Idx < T24s2.n
  z0_arr : tArr z0Idx = z0Arr
  z0_central : ∀ p < T24s2.n, T24s2.mulIdx p z0Idx = T24s2.mulIdx z0Idx p
  k_len : (kIdx ()).length = 16
  dz_len : (dzIdx ()).length = 16
  w5_len : (w5Masks ()).length = 32
  vz_len : (vzMasks ()).length = 16
  w5_nodup : (combos w5Basis).Nodup
  z0_sq : arrMul z0Arr z0Arr = idArr
  z0_ne : ∃ i < 24, z0Arr[i]! ≠ i
  k_comm : ∀ p ∈ kIdx (), arrMul (tArr p) z0Arr = arrMul z0Arr (tArr p)
  dz_comm : ∀ p ∈ dzIdx (), arrMul (tArr p) z0Arr = arrMul z0Arr (tArr p)
  dz_abel : ∀ p ∈ dzIdx (), ∀ q ∈ dzIdx (), arrMul (tArr p) (tArr q) = arrMul (tArr q) (tArr p)
  dz_sq : ∀ p ∈ dzIdx (), arrMul (tArr p) (tArr p) = idArr
  t_size : ∀ p < T24s2.n, (tArr p).size = 24
  dz_k : ∀ p ∈ dzIdx (), fixesOct (tArr p) = true ↔ (tArr p = idArr ∨ tArr p = z0Arr)
  vbase_vz : ∀ b ∈ vBase, b ∈ vzMasks ()
  z0_fixes : fixesOct z0Arr = true
  z0_fix_iff : ∀ j < 24, z0Arr[j]! = j ↔ j ∈ octPts

private theorem burnsideK42_lists_facts : burnsideK42_Lists := by
  have h := (Certificates.certificate7277).1
  simp only [listsOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h8a, h8b, h9, h10, h11, h12, hsz, h13, h14, h15, h16⟩ := h
  refine ⟨h1, h2, ?_, h4, h5, h6, h7, h8, h8a, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun b hb => List.contains_iff_mem.1 (List.all_eq_true.1 h14 b hb), h15, ?_⟩
  · intro p hp
    exact (List.all_eq_true.1 h3 p (List.mem_range.2 hp) : _ == _) |> beq_iff_eq.1
  · obtain ⟨i, hi, hne⟩ := List.any_eq_true.1 h8b
    exact ⟨i, List.mem_range.1 hi, by simpa using hne⟩
  · intro p hp
    exact beq_iff_eq.1 (List.all_eq_true.1 h9 p hp)
  · intro p hp
    exact beq_iff_eq.1 (List.all_eq_true.1 h10 p hp)
  · intro p hp q hq
    exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 h11 p hp) q hq)
  · intro p hp
    exact beq_iff_eq.1 (List.all_eq_true.1 h12 p hp)
  · intro p hp
    exact beq_iff_eq.1 (List.all_eq_true.1 hsz p (List.mem_range.2 hp))
  · intro p hp
    have := List.all_eq_true.1 h13 p hp
    have h := beq_iff_eq.1 this
    rw [h]
    simp only [Bool.or_eq_true, beq_iff_eq]
  · intro j hj
    have := List.all_eq_true.1 h16 j (List.mem_range.2 hj)
    have h := beq_iff_eq.1 this
    constructor
    · intro h1
      have : (octPts.contains j) = true := by rw [← h]; simpa using h1
      simpa using this
    · intro h1
      have h2 : (octPts.contains j) = true := by simpa using h1
      have : (z0Arr[j]! == j) = true := by rw [h]; exact h2
      simpa using this

private theorem burnsideK42_KO0_le_Tsub :
    burnsideK42_KO0 ≤ burnsideK42_Tsub := by
  have hk := burnsideK42_lists_facts.k_len
  have hnd : (kIdx ()).Nodup := by
    unfold kIdx
    exact List.nodup_range.filter _
  have hlist : ∀ x ∈ burnsideK42_kList, x ∈ burnsideK42_Tsub ⊓ burnsideK42_KO0 := by
    intro x hx
    simp only [burnsideK42_kList, List.mem_pmap] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨⟨_, rfl⟩, burnsideK42_phi24_mem_KO0 _ (burnsideK42_kIdx_fixes hp)⟩
  have h16 : 16 ≤ Nat.card ↥(burnsideK42_Tsub ⊓ burnsideK42_KO0) := by
    have := burnsideK42_length_le_card _ burnsideK42_kList (burnsideK42_kList_nodup hnd) hlist
    rwa [burnsideK42_kList_length hk] at this
  have heq : burnsideK42_Tsub ⊓ burnsideK42_KO0 = burnsideK42_KO0 :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (burnsideK42_KO0_card_le.trans h16)
  rw [← heq]
  exact inf_le_left

end TArr

noncomputable abbrev burnsideK42_rho : burnsideK42_K →* MulAut W11 :=
  rhoC11 CFSG.Monster.Code.AutPerm le_rfl

private theorem burnsideK42_rho_toW (σ : burnsideK42_K) {a : Array ℕ}
    (ha : HasArr (σ : Equiv.Perm (Fin 24)) a) (m : ℕ) :
    burnsideK42_rho σ (toW 11 m) = toW 11 (actC11 a m) :=
  rhoC11_toW _ _ σ ha m

@[expose] def burnsideK42_vecL : List (W11 × Finset W11) :=
  (List.range 3).map fun i =>
    (toW 11 vBase[i]!, ((vecTab i).toList.map fun e => toW 11 e.1).toFinset)

private theorem burnsideK42_vecL_getElem (j : ℕ) (hj : j < 3) :
    burnsideK42_vecL[j]'(by simpa [burnsideK42_vecL] using hj) =
      (toW 11 vBase[j]!, ((vecTab j).toList.map fun e => toW 11 e.1).toFinset) := by
  simp [burnsideK42_vecL]

private theorem burnsideK42_vecChain_parts :
    vBase.length = 3 ∧ vGens.length = 3 ∧ (∀ x ∈ vBase, x < 2048) ∧ ∀ i < 3,
      ((∀ g ∈ vGens[i]!, inAutOK g = true ∧ ∀ b ∈ vBase.take i, actC11 g b = b) ∧
      derivOK (gStep (vGens[i]!) actC11) (vGens[i]!).length vBase[i]! (vecTab i) = true ∧
      tabNodupLt 2048 (vecTab i) = true ∧ (vecTab i).size = [759, 280, 72][i]!) := by
  have hok := (Certificates.certificate7276).2.2
  simp only [vecChainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨⟨⟨hbl, hgl⟩, hlt⟩, hlev⟩ := hok
  refine ⟨hbl, hgl, hlt, fun i hi => ?_⟩
  obtain ⟨⟨⟨hg, hd⟩, hn⟩, hs⟩ := hlev i hi
  exact ⟨hg, hd, hn, hs⟩

@[expose] def burnsideK42_centK (ms : List ℕ) : Subgroup burnsideK42_K where
  carrier := {γ | ∀ m ∈ ms, burnsideK42_rho γ (toW 11 m) = toW 11 m}
  mul_mem' {a b} ha hb := fun m hm => by
    rw [map_mul, MulAut.mul_apply, hb m hm, ha m hm]
  one_mem' := fun m _ => by simp
  inv_mem' {a} ha := fun m hm => by
    have h := ha m hm
    rw [map_inv, MulAut.inv_def, MulEquiv.symm_apply_eq]
    exact h.symm

private theorem burnsideK42_centK_anti {ms ms' : List ℕ} (h : ∀ m ∈ ms', m ∈ ms) :
    burnsideK42_centK ms ≤ burnsideK42_centK ms' :=
  fun _ hγ m hm => hγ m (h m hm)

private theorem burnsideK42_vecL_card_get (j : ℕ) (hj : j < 3) :
    (burnsideK42_vecL[j]'(by simpa [burnsideK42_vecL] using hj)).2.card =
      [759, 280, 72][j]! := by
  obtain ⟨-, -, -, hlev⟩ := burnsideK42_vecChain_parts
  obtain ⟨-, -, hn, hs⟩ := hlev j hj
  rw [burnsideK42_vecL_getElem j hj]
  simp only [tabNodupLt, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at hn
  obtain ⟨hnd, hlt⟩ := hn
  have hlt' : ∀ x ∈ (vecTab j).toList.map (·.1), x < 2048 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
    have := hlt i (by simpa using hi)
    simpa using this
  have hnd' : ((vecTab j).toList.map fun e => toW 11 e.1).Nodup := by
    have h1 := hnd.map_on (f := fun x : ℕ => toW 11 x)
      (fun x hx y hy h => toW_inj (hlt' x hx) (hlt' y hy) h)
    have h2 : ((vecTab j).toList.map fun e => toW 11 e.1) =
        ((vecTab j).toList.map (·.1)).map (fun x : ℕ => toW 11 x) := by
      rw [List.map_map]; rfl
    rw [h2]
    exact h1
  rw [List.toFinset_card_of_nodup hnd', List.length_map, Array.length_toList, hs]

private theorem burnsideK42_vecL_cards :
    burnsideK42_vecL.map (fun p => p.2.card) = [759, 280, 72] := by
  apply List.ext_getElem
  · simp [burnsideK42_vecL]
  · intro j h1 h2
    have hj : j < 3 := by simpa [burnsideK42_vecL] using h2
    have := burnsideK42_vecL_card_get j hj
    simp only [List.getElem_map]
    rw [this]
    interval_cases j <;> rfl

private theorem burnsideK42_vecStab_card_le :
    Nat.card ↥(burnsideK42_centK vBase) ≤ 16 := by
  letI : MulAction burnsideK42_K W11 := MulAction.compHom W11 burnsideK42_rho
  have hsm : ∀ (σ : burnsideK42_K) (w : W11), σ • w = burnsideK42_rho σ w := fun _ _ => rfl
  obtain ⟨hbl, hgl, hlt, hlev⟩ := burnsideK42_vecChain_parts
  have hyp : burnsideK42_ChainHyp (⊤ : Subgroup burnsideK42_K) burnsideK42_vecL := by
    apply burnsideK42_chainHyp_of_levels
    intro j hj y hy
    have hj3 : j < 3 := by simpa [burnsideK42_vecL] using hj
    rw [burnsideK42_vecL_getElem j hj3] at hy ⊢
    obtain ⟨hg, hd, hn, -⟩ := hlev j hj3
    set H : Subgroup burnsideK42_K := burnsideK42_chainFinal ⊤ (burnsideK42_vecL.take j) with hH
    have hgenH : ∀ g (hgm : g ∈ vGens[j]!), burnsideK42_kOfArr g (hg g hgm).1 ∈ H := by
      intro g hgm
      rw [hH, burnsideK42_mem_chainFinal]
      refine ⟨Subgroup.mem_top _, fun p hp => ?_⟩
      obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hp
      have hlj : l < j := by have := hl; simp only [List.length_take] at this; omega
      have hl3 : l < 3 := by omega
      rw [List.getElem_take, burnsideK42_vecL_getElem l hl3, hsm,
        burnsideK42_rho_toW _ (burnsideK42_kOfArr_hasArr g (hg g hgm).1)]
      have hfix := (hg g hgm).2 vBase[l]! (by
        rw [getElem!_pos vBase l (by omega)]
        exact List.mem_iff_getElem.2 ⟨l, by simp [List.length_take]; omega, by simp⟩)
      rw [hfix]
    have hP := burnsideK42_derivOK_sound hd
      (fun v => v < 2048 ∧ ∃ h ∈ H, h • (toW 11 vBase[j]! : W11) = toW 11 v)
      ⟨hlt _ (by rw [getElem!_pos vBase j (by omega)]; exact List.getElem_mem _), 1, H.one_mem,
        by simp [hsm]⟩
      (by
        intro g hgl v ⟨hv, h, hhH, hh⟩
        have hgm : (vGens[j]!)[g]! ∈ vGens[j]! := by
          rw [getElem!_pos (vGens[j]!) g hgl]; exact List.getElem_mem _
        set σ := burnsideK42_kOfArr ((vGens[j]!)[g]!) (hg _ hgm).1 with hσ
        have hσarr := burnsideK42_kOfArr_hasArr ((vGens[j]!)[g]!) (hg _ hgm).1
        refine ⟨actC11_lt _ _, σ * h, H.mul_mem (hgenH _ hgm) hhH, ?_⟩
        rw [mul_smul, hh, hsm, burnsideK42_rho_toW σ hσarr]
        rfl)
    have hy' : y ∈ ((vecTab j).toList.map fun e => toW 11 e.1) := by
      simpa using hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy'
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 he
    have hi' : i < (vecTab j).size := by simpa using hi
    have hPi := hP i hi'
    have hei : (vecTab j)[i]!.1 = e.1 := by
      rw [getElem!_pos (vecTab j) i hi', ← hie]
      simp
    rw [hei] at hPi
    exact hPi.2
  have hcard := burnsideK42_chain_card_le burnsideK42_vecL ⊤ hyp
  rw [burnsideK42_vecL_cards, Subgroup.card_top, CFSG.Monster.Code.card_AutPerm] at hcard
  have hle : burnsideK42_centK vBase ≤ burnsideK42_chainFinal ⊤ burnsideK42_vecL := by
    intro γ hγ
    rw [burnsideK42_mem_chainFinal]
    refine ⟨Subgroup.mem_top _, fun p hp => ?_⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hp
    have hl3 : l < 3 := by simpa [burnsideK42_vecL] using hl
    rw [burnsideK42_vecL_getElem l hl3, hsm]
    have hbl' : vBase.length = 3 := by decide
    exact hγ vBase[l]! (by
      rw [getElem!_pos vBase l (by omega)]; exact List.getElem_mem _)
  have := Subgroup.card_le_of_le hle
  norm_num at hcard
  omega

section TArr2

private theorem burnsideK42_le_Tsub_of_card (H : Subgroup burnsideK42_K) (idx : List ℕ)
    (hlen : idx.length = 16) (hnd : idx.Nodup) (hlt : ∀ p ∈ idx, p < T24s2.n)
    (hmem : ∀ p (hp : p ∈ idx), (phi24 (⟨p, hlt p hp⟩ : T24s2.Elem) : burnsideK42_K) ∈ H)
    (hcard : Nat.card ↥H ≤ 16) : H ≤ burnsideK42_Tsub := by
  let l : List burnsideK42_K :=
    idx.pmap (fun p hp => (phi24 (⟨p, hp⟩ : T24s2.Elem) : burnsideK42_K)) hlt
  have hl_nd : l.Nodup := List.Nodup.pmap (fun p hp q hq h =>
    congrArg (fun q : T24s2.Elem => q.idx) (burnsideK42_phi24_injective h)) hnd
  have hl_len : l.length = 16 := by simp [l, hlen]
  have hl_mem : ∀ x ∈ l, x ∈ burnsideK42_Tsub ⊓ H := by
    intro x hx
    simp only [l, List.mem_pmap] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨⟨_, rfl⟩, hmem p hp⟩
  have h16 : 16 ≤ Nat.card ↥(burnsideK42_Tsub ⊓ H) := by
    have := burnsideK42_length_le_card _ l hl_nd hl_mem
    rwa [hl_len] at this
  have heq : burnsideK42_Tsub ⊓ H = H :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (hcard.trans h16)
  rw [← heq]
  exact inf_le_left

private theorem burnsideK42_ge_of_list (H : Subgroup burnsideK42_K) (idx : List ℕ)
    (hlen : idx.length = 16) (hnd : idx.Nodup) (hlt : ∀ p ∈ idx, p < T24s2.n)
    (hmem : ∀ p (hp : p ∈ idx), (phi24 (⟨p, hlt p hp⟩ : T24s2.Elem) : burnsideK42_K) ∈ H) :
    16 ≤ Nat.card ↥H := by
  let l : List burnsideK42_K :=
    idx.pmap (fun p hp => (phi24 (⟨p, hp⟩ : T24s2.Elem) : burnsideK42_K)) hlt
  have hl_nd : l.Nodup := List.Nodup.pmap (fun p hp q hq h =>
    congrArg (fun q : T24s2.Elem => q.idx) (burnsideK42_phi24_injective h)) hnd
  have hl_len : l.length = 16 := by simp [l, hlen]
  have hl_mem : ∀ x ∈ l, x ∈ H := by
    intro x hx
    simp only [l, List.mem_pmap] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact hmem p hp
  have := burnsideK42_length_le_card _ l hl_nd hl_mem
  rwa [hl_len] at this

private theorem burnsideK42_dzIdx_lt {p : ℕ} (hp : p ∈ dzIdx ()) : p < T24s2.n := by
  simp only [dzIdx, List.mem_filter, List.mem_range] at hp
  exact hp.1

private theorem burnsideK42_dzIdx_fixes {p : ℕ} (hp : p ∈ dzIdx ()) :
    (vzMasks ()).all (fun m => actC11 (tArr p) m == m) = true := by
  simp only [dzIdx, List.mem_filter] at hp
  exact hp.2

private theorem burnsideK42_phi24_mem_DZ (s : T24s2.Elem)
    (h : (vzMasks ()).all (fun m => actC11 (tArr s.idx) m == m) = true) :
    (phi24 s : burnsideK42_K) ∈ burnsideK42_centK (vzMasks ()) := by
  intro m hm
  rw [burnsideK42_rho_toW _ (burnsideK42_phi24_hasArr s)]
  have := List.all_eq_true.1 h m hm
  simp only [beq_iff_eq] at this
  rw [this]

private theorem burnsideK42_DZ_le_Tsub :
    burnsideK42_centK (vzMasks ()) ≤ burnsideK42_Tsub := by
  have hd := burnsideK42_lists_facts.dz_len
  have hb := burnsideK42_lists_facts.vbase_vz
  have hnd : (dzIdx ()).Nodup := by
    unfold dzIdx
    exact List.nodup_range.filter _
  refine burnsideK42_le_Tsub_of_card _ (dzIdx ()) hd hnd (fun p hp => burnsideK42_dzIdx_lt hp)
    (fun p hp => burnsideK42_phi24_mem_DZ _ (burnsideK42_dzIdx_fixes hp)) ?_
  exact (Subgroup.card_le_of_le (burnsideK42_centK_anti hb)).trans burnsideK42_vecStab_card_le

private theorem burnsideK42_DZ_card :
    Nat.card ↥(burnsideK42_centK (vzMasks ())) = 16 := by
  have hd := burnsideK42_lists_facts.dz_len
  have hb := burnsideK42_lists_facts.vbase_vz
  have hnd : (dzIdx ()).Nodup := by
    unfold dzIdx
    exact List.nodup_range.filter _
  refine le_antisymm
    ((Subgroup.card_le_of_le (burnsideK42_centK_anti hb)).trans burnsideK42_vecStab_card_le) ?_
  exact burnsideK42_ge_of_list _ (dzIdx ()) hd hnd (fun p hp => burnsideK42_dzIdx_lt hp)
    (fun p hp => burnsideK42_phi24_mem_DZ _ (burnsideK42_dzIdx_fixes hp))

end TArr2

private theorem burnsideK42_oct_parts :
    (∀ a ∈ gensK, inAutOK a = true) ∧ (∀ x ∈ octPts, x < 24) ∧ octPts.Nodup ∧ octPts.length = 8 ∧
    derivOK (gStep gensK permM) gensK.length e0mask (octTab ()) = true ∧
    octMiss (octTab ()) = 0 := by
  have h := (Certificates.certificate7276).1
  simp only [octOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    and_assoc] at h
  exact h

private theorem burnsideK42_treeSumN_mono {F G : ℕ → ℕ} (h : ∀ x, F x ≤ G x) (m : ℕ → ℕ) :
    ∀ k a, treeSumN F m k a ≤ treeSumN G m k a
  | 0, a => h a
  | k + 1, a => by
    simp only [treeSumN]
    exact Nat.add_le_add (burnsideK42_treeSumN_mono h m k a) (burnsideK42_treeSumN_mono h m k _)

private theorem burnsideK42_e0_eq : burnsideK42_e0 = Multiplicative.ofAdd (bvec 24 e0mask) := rfl

private theorem burnsideK42_permAct_bvec {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (h : HasArr σ
    a) (x : ℕ) :
    G6.permAct 24 σ (Multiplicative.ofAdd (bvec 24 x)) =
      Multiplicative.ofAdd (bvec 24 (permM a x)) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_permAct, toAdd_ofAdd, toAdd_ofAdd, permWord_bvec h]

private theorem burnsideK42_octad_trans (e : G6.PermMod 24)
    (he : e ∈ golayC) (hw : hammingNorm (Multiplicative.toAdd e) = 8) :
    ∃ τ : burnsideK42_K, G6.permAct 24 (τ : Equiv.Perm (Fin 24)) burnsideK42_e0 = e := by
  obtain ⟨hgens, -, -, -, hderiv, hmiss⟩ := burnsideK42_oct_parts
  have hP := burnsideK42_derivOK_sound hderiv
    (fun x => ∃ τ : burnsideK42_K, G6.permAct 24 (τ : Equiv.Perm (Fin 24)) burnsideK42_e0 =
      Multiplicative.ofAdd (bvec 24 x))
    ⟨1, by simp [burnsideK42_e0_eq]⟩
    (by
      intro g hg x ⟨τ, hτ⟩
      have hgm : gensK[g]! ∈ gensK := by
        rw [getElem!_pos gensK g hg]; exact List.getElem_mem _
      refine ⟨burnsideK42_kOfArr (gensK[g]!) (hgens _ hgm) * τ, ?_⟩
      rw [Subgroup.coe_mul, map_mul, MulAut.mul_apply, hτ,
        burnsideK42_permAct_bvec (burnsideK42_kOfArr_hasArr _ (hgens _ hgm))]
      rfl)
  have hcov : ∃ i, ∃ hi : i < (octTab ()).size,
      bvec 24 ((octTab ())[i]!).1 = Multiplicative.toAdd e := by
    by_contra hno
    push Not at hno
    have hmem : Multiplicative.toAdd e ∈ Finset.univ.filter (· ∈ CFSG.Monster.Code.C) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, (mem_golayC_iff e).1 he⟩
    let F : (Fin 24 → ZMod 2) → ℕ := fun x =>
      if hammingNorm x = 8 ∧ ∀ i, ∀ hi : i < (octTab ()).size,
        bvec 24 ((octTab ())[i]!).1 ≠ x then 1 else 0
    have hsum := sum_C_eq_treeSumN (M := ℕ) F
    have hle : treeSumN (fun a => F (bvec 24 a)) Bmask 12 0 ≤ octMiss (octTab ()) := by
      refine burnsideK42_treeSumN_mono (fun a => ?_) Bmask 12 0
      by_cases hG : (popc 24 a == 8 && !((octTab ()).any (·.1 == a))) = true
      · rw [if_pos hG]
        simp only [F]
        split_ifs <;> omega
      · rw [if_neg hG]
        simp only [F]
        rw [if_neg]
        rintro ⟨hw8, hall⟩
        rw [hammingNorm_bvec] at hw8
        apply hG
        have hany : (octTab ()).any (·.1 == a) = false := by
          by_contra hne
          have hne' : (octTab ()).any (·.1 == a) = true := by simpa using hne
          obtain ⟨i, hi, hia⟩ := Array.any_eq_true.1 hne'
          apply hall i hi
          rw [getElem!_pos (octTab ()) i hi]
          simp only [beq_iff_eq] at hia
          rw [hia]
        simp [hw8, hany]
    have h0 : ∑ x ∈ Finset.univ.filter (· ∈ CFSG.Monster.Code.C), F x = 0 := by
      rw [hsum]
      have := hle
      rw [hmiss] at this
      omega
    have hF := Finset.sum_eq_zero_iff.1 h0 _ hmem
    simp only [F] at hF
    rw [if_pos ⟨hw, fun i hi => hno i hi⟩] at hF
    exact absurd hF (by simp)
  obtain ⟨i, hi, hie⟩ := hcov
  obtain ⟨τ, hτ⟩ := hP i hi
  exact ⟨τ, by rw [hτ, hie]; rfl⟩

private theorem burnsideK42_f3_parts :
    (∀ kg ∈ f3Wit, inAutOK kg.2 = true ∧ permM kg.2 e0mask = e0mask ∧
      arrConj kg.2 z0Arr = kg.1) ∧
    (∀ p ∈ kIdx (), tArr p = idArr ∨ ∃ kg ∈ f3Wit, kg.1 = tArr p) := by
  have h := (Certificates.certificate7277).2.1
  simp only [f3OK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun kg hkg => ?_, fun p hp => ?_⟩
  · obtain ⟨⟨ha, hb⟩, hc⟩ := h1 kg hkg
    exact ⟨ha, hb, hc⟩
  · rcases h2 p hp with h | ⟨kg, hkg, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨kg, hkg, by simpa using h⟩

private theorem burnsideK42_hasArr_conj {σ τ : Equiv.Perm (Fin 24)} {a g : Array ℕ} (hσ :
    HasArr σ a)
    (hτ : HasArr τ g) (hτi : HasArr τ⁻¹ (invArr g)) : HasArr (τ * σ * τ⁻¹) (arrConj g a) :=
  burnsideK42_hasArr_mul (burnsideK42_hasArr_mul hτ hσ) hτi

private theorem burnsideK42_permAct_e0 {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (h : HasArr σ a)
    (ha : permM a e0mask = e0mask) : G6.permAct 24 σ burnsideK42_e0 = burnsideK42_e0 := by
  rw [burnsideK42_e0_eq, burnsideK42_permAct_bvec h, ha]

private theorem burnsideK42_w5_lt' : ∀ x ∈ w5Masks (), x < 2048 := by
  intro x hx
  unfold w5Masks at hx
  exact combos_lt (n := 11) (by decide) x hx

section Conj

private theorem burnsideK42_KO0_arr
    {γ : burnsideK42_K} (hγ : γ ∈ burnsideK42_KO0) :
    ∃ p ∈ kIdx (), HasArr (γ : Equiv.Perm (Fin 24)) (tArr p) := by
  obtain ⟨s, rfl⟩ := burnsideK42_KO0_le_Tsub hγ
  have h1 := burnsideK42_phi24_hasArr s
  refine ⟨s.idx, ?_, h1⟩
  simp only [kIdx, List.mem_filter, List.mem_range]
  refine ⟨s.lt, ?_⟩
  simp only [fixesOct, List.all_eq_true, beq_iff_eq]
  intro i hi
  have hi24 : i < 24 := by
    have := burnsideK42_octPts_lt i hi
    exact this
  have := (burnsideK42_mem_KO0.1 hγ) i hi hi24
  have h2 := h1 ⟨i, hi24⟩
  rw [this] at h2
  exact h2.symm

private theorem burnsideK42_KO0_conj
    {z0K : burnsideK42_K}
    (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) {γ : burnsideK42_K}
    (hγ : γ ∈ burnsideK42_KO0) (hne : γ ≠ 1) :
    ∃ c : burnsideK42_K, G6.permAct 24 (c : Equiv.Perm (Fin 24)) burnsideK42_e0 = burnsideK42_e0 ∧
      c * z0K * c⁻¹ = γ := by
  obtain ⟨p, hp, hγp⟩ := burnsideK42_KO0_arr hγ
  obtain ⟨hw, hcov⟩ := burnsideK42_f3_parts
  rcases hcov p hp with hid | ⟨kg, hkg, hk⟩
  · exfalso
    apply hne
    apply Subtype.ext
    exact burnsideK42_hasArr_ext hγp (hid ▸ burnsideK42_hasArr_one)
  · obtain ⟨ha, hb, hc⟩ := hw kg hkg
    refine ⟨burnsideK42_kOfArr kg.2 ha, ?_, ?_⟩
    · exact burnsideK42_permAct_e0 (burnsideK42_kOfArr_hasArr kg.2 ha) hb
    · apply Subtype.ext
      have := burnsideK42_hasArr_conj hz0 (burnsideK42_kOfArr_hasArr kg.2 ha)
        (burnsideK42_kOfArr_inv_hasArr kg.2 ha)
      rw [hc, hk] at this
      exact burnsideK42_hasArr_ext this hγp

private theorem burnsideK42_reduce
    {z0K : burnsideK42_K}
    (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) (e : G6.PermMod 24) (he : e ∈ golayC)
    (hw : hammingNorm (Multiplicative.toAdd e) = 8) (k : burnsideK42_K) (hk1 : k ≠ 1)
    (hk : k ∈ (fixingSubgroup (Equiv.Perm (Fin 24))
      (CFSG.ASVolI.ChIJK.octadPts e)).subgroupOf CFSG.Monster.Code.AutPerm) :
    ∃ κ : burnsideK42_K, G6.permAct 24 (κ : Equiv.Perm (Fin 24)) burnsideK42_e0 = e ∧
      κ * z0K * κ⁻¹ = k := by
  obtain ⟨τ, hτ⟩ := burnsideK42_octad_trans e he hw
  have hk' : τ⁻¹ * k * τ ∈ burnsideK42_KO0 := by
    rw [burnsideK42_mem_KO0]
    intro i hi hi24
    have hx : (⟨i, hi24⟩ : Fin 24) ∈ CFSG.ASVolI.ChIJK.octadPts burnsideK42_e0 := by
      rw [burnsideK42_octadPts_e0]; exact hi
    have hτx : (τ : Equiv.Perm (Fin 24)) ⟨i, hi24⟩ ∈ CFSG.ASVolI.ChIJK.octadPts e := by
      have h1 : Multiplicative.toAdd burnsideK42_e0 ⟨i, hi24⟩ = 1 := hx
      simp only [CFSG.ASVolI.ChIJK.octadPts, Set.mem_ofPred_eq]
      rw [← hτ, toAdd_permAct]
      simp only [permWord, Function.comp_apply]
      have h2 : ((τ : Equiv.Perm (Fin 24))⁻¹) ((τ : Equiv.Perm (Fin 24)) ⟨i, hi24⟩) = ⟨i, hi24⟩ := by
        simp
      rw [h2]
      exact h1
    have hfix : (k : Equiv.Perm (Fin 24)) ((τ : Equiv.Perm (Fin 24)) ⟨i, hi24⟩) =
        (τ : Equiv.Perm (Fin 24)) ⟨i, hi24⟩ := by
      have := (mem_fixingSubgroup_iff _ |>.1 (Subgroup.mem_subgroupOf.1 hk)) _ hτx
      simpa using this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    rw [hfix]
    simp
  have hne : τ⁻¹ * k * τ ≠ 1 := by
    intro h
    apply hk1
    have : k = τ * (τ⁻¹ * k * τ) * τ⁻¹ := by group
    rw [this, h]
    group
  obtain ⟨c, hc1, hc2⟩ := burnsideK42_KO0_conj hz0 hk' hne
  refine ⟨τ * c, ?_, ?_⟩
  · rw [Subgroup.coe_mul, map_mul, MulAut.mul_apply, hc1, hτ]
  · have : τ * c * z0K * (τ * c)⁻¹ = τ * (c * z0K * c⁻¹) * τ⁻¹ := by group
    rw [this, hc2]
    group

private theorem burnsideK42_vz_lt : ∀ m ∈ vzMasks (), m < 2048 := by
  intro m hm
  unfold vzMasks at hm
  exact burnsideK42_w5_lt' m (List.mem_filter.1 hm).1

private theorem burnsideK42_DZ_arr
    {γ : burnsideK42_K}
    (hγ : γ ∈ burnsideK42_centK (vzMasks ())) :
    ∃ p ∈ dzIdx (), HasArr (γ : Equiv.Perm (Fin 24)) (tArr p) := by
  obtain ⟨s, rfl⟩ := burnsideK42_DZ_le_Tsub hγ
  have h1 := burnsideK42_phi24_hasArr s
  refine ⟨s.idx, ?_, h1⟩
  simp only [dzIdx, List.mem_filter, List.mem_range]
  refine ⟨s.lt, ?_⟩
  simp only [List.all_eq_true, beq_iff_eq]
  intro m hm
  have h2 := hγ m hm
  rw [burnsideK42_rho_toW _ h1] at h2
  exact toW_inj (actC11_lt _ _) (burnsideK42_vz_lt m hm) h2

private theorem burnsideK42_KO0_arr_conv
    {p : ℕ} (hp : p ∈ kIdx ()) :
    ∃ γ ∈ burnsideK42_KO0, HasArr (γ : Equiv.Perm (Fin 24)) (tArr p) :=
  ⟨_, burnsideK42_phi24_mem_KO0 (⟨p, burnsideK42_kIdx_lt hp⟩ : T24s2.Elem)
    (burnsideK42_kIdx_fixes hp), burnsideK42_phi24_hasArr (⟨p, burnsideK42_kIdx_lt hp⟩ : T24s2.Elem)⟩

private theorem burnsideK42_DZ_arr_conv
    {p : ℕ} (hp : p ∈ dzIdx ()) :
    ∃ γ ∈ burnsideK42_centK (vzMasks ()), HasArr (γ : Equiv.Perm (Fin 24)) (tArr p) :=
  ⟨_, burnsideK42_phi24_mem_DZ (⟨p, burnsideK42_dzIdx_lt hp⟩ : T24s2.Elem)
    (burnsideK42_dzIdx_fixes hp), burnsideK42_phi24_hasArr (⟨p, burnsideK42_dzIdx_lt hp⟩ : T24s2.Elem)⟩

end Conj

end Arr

section Mod
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

@[expose] def burnsideK42_MO0 : Subgroup burnsideK42_K :=
  (m24Fix burnsideK42_e0).subgroupOf CFSG.Monster.Code.AutPerm

private theorem burnsideK42_mem_MO0 {γ : burnsideK42_K} :
    γ ∈ burnsideK42_MO0 ↔ G6.permAct 24 (γ : Equiv.Perm (Fin 24)) burnsideK42_e0 = burnsideK42_e0 := by
  simp only [burnsideK42_MO0, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨γ.2, h⟩

structure burnsideK42_Std {V : Type} [CommGroup V] (θ : burnsideK42_K →* MulAut V)
    (ε : V ≃* W11) (V5 : Subgroup V) : Prop where
  hε : ∀ (γ : burnsideK42_K) (v : V), ε (θ γ v) = burnsideK42_rho γ (ε v)
  inv : ∀ γ ∈ burnsideK42_MO0, ∀ v ∈ V5, θ γ v ∈ V5
  card : Nat.card V5 = 32

variable {V : Type} [CommGroup V] {θ : burnsideK42_K →* MulAut V} {ε : V ≃* W11}
  {V5 : Subgroup V}

private theorem burnsideK42_theta_vm (hε : ∀ (γ : burnsideK42_K) (v : V), ε (θ γ v) =
    burnsideK42_rho γ (ε v))
    {γ : burnsideK42_K} {a : Array ℕ} (h : HasArr (γ : Equiv.Perm (Fin 24)) a) (m : ℕ) :
    θ γ ((MaskCoords.ofEquiv ε).vm m) = (MaskCoords.ofEquiv ε).vm (actC11 a m) := by
  rw [MaskCoords.ofEquiv_vm, MaskCoords.ofEquiv_vm]
  apply ε.injective
  rw [hε, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, burnsideK42_rho_toW γ h]

private theorem burnsideK42_f4_parts :
    (∀ g ∈ moGens, inAutOK g = true ∧ permM g e0mask = e0mask) ∧
    ∀ m < 2048, m ∈ w5Masks () ∨
      indep6 ((wordPool moGens.length 2).map fun w => applyWord moGens w m) = true := by
  have h := (Certificates.certificate7277).2.2
  simp only [f4OK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun g hg => ?_, fun m hm => ?_⟩
  · obtain ⟨ha, hb⟩ := h1 g hg
    exact ⟨ha, hb⟩
  · have := h2 m hm
    simp only [Bool.or_eq_true, List.contains_iff_mem] at this
    exact this

private theorem burnsideK42_wordsOfLen_lt (n : ℕ) : ∀ (k : ℕ), ∀ w ∈ wordsOfLen k n, ∀ g ∈ w, g < n
  | 0, w, hw, g, hg => by
    simp only [wordsOfLen, List.mem_singleton] at hw
    subst hw
    simp at hg
  | k + 1, w, hw, g, hg => by
    simp only [wordsOfLen, List.mem_flatMap, List.mem_map, List.mem_range] at hw
    obtain ⟨w', hw', j, hj, rfl⟩ := hw
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hj
    · exact burnsideK42_wordsOfLen_lt n k w' hw' g hg

private theorem burnsideK42_wordPool_lt (n L : ℕ) : ∀ w ∈ wordPool n L, ∀ g ∈ w, g < n := by
  intro w hw g hg
  simp only [wordPool, List.mem_flatMap, List.mem_range] at hw
  obtain ⟨k, -, hk⟩ := hw
  exact burnsideK42_wordsOfLen_lt n k w hk g hg

private theorem burnsideK42_applyWord_lt (gens : List (Array ℕ)) {m : ℕ} (hm : m < 2048) :
    ∀ w : List ℕ, applyWord gens w m < 2048
  | [] => by simpa [applyWord] using hm
  | g :: w => by
    have := burnsideK42_applyWord_lt gens hm w
    simp only [applyWord, List.foldr_cons] at this ⊢
    exact actC11_lt _ _

private theorem burnsideK42_applyWord_mem
    (hS : burnsideK42_Std θ ε V5) {m : ℕ}
    (hm : (MaskCoords.ofEquiv ε).vm m ∈ V5) :
    ∀ w : List ℕ, (∀ g ∈ w, g < moGens.length) →
      (MaskCoords.ofEquiv ε).vm (applyWord moGens w m) ∈ V5
  | [], _ => by simpa [applyWord] using hm
  | g :: w, hw => by
    have ih := burnsideK42_applyWord_mem hS hm w (fun g' hg' => hw g' (List.mem_cons_of_mem g hg'))
    have hgl : g < moGens.length := hw g List.mem_cons_self
    have hgm : moGens[g]! ∈ moGens := by
      rw [getElem!_pos moGens g hgl]; exact List.getElem_mem _
    obtain ⟨hg1, hg2⟩ := (burnsideK42_f4_parts).1 _ hgm
    set σ := burnsideK42_kOfArr (moGens[g]!) hg1 with hσ
    have hσarr := burnsideK42_kOfArr_hasArr (moGens[g]!) hg1
    have hσO : σ ∈ burnsideK42_MO0 :=
      burnsideK42_mem_MO0.2 (burnsideK42_permAct_e0 hσarr hg2)
    have := hS.inv σ hσO _ ih
    rw [burnsideK42_theta_vm hS.hε hσarr] at this
    simpa [applyWord] using this

private theorem burnsideK42_indep6_spec {cands : List ℕ} (h : indep6 cands = true) :
    ∃ bs : List ℕ, bs.length = 6 ∧ (combos bs).Nodup ∧ ∀ b ∈ bs, b ∈ cands := by
  unfold indep6 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  exact ⟨pick6 cands, h.1.1, h.1.2, h.2⟩

private theorem burnsideK42_w5_nodup :
    (w5Masks ()).Nodup := by
  exact burnsideK42_lists_facts.w5_nodup

private theorem burnsideK42_V5_mask
    (hS : burnsideK42_Std θ ε V5) (m : ℕ) (hm : m < 2048) :
    (MaskCoords.ofEquiv ε).vm m ∈ V5 ↔ m ∈ w5Masks () := by
  classical
  set c := MaskCoords.ofEquiv ε with hc
  obtain ⟨hgens, hcov⟩ := burnsideK42_f4_parts
  have hsub : ∀ m < 2048, c.vm m ∈ V5 → m ∈ w5Masks () := by
    intro m hm hmV
    rcases hcov m hm with h | h
    · exact h
    · exfalso
      obtain ⟨bs, hlen, hnd, hmem⟩ := burnsideK42_indep6_spec h
      have hbV : ∀ b ∈ bs, c.vm b ∈ V5 := by
        intro b hb
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (hmem b hb)
        exact burnsideK42_applyWord_mem hS hmV w (burnsideK42_wordPool_lt _ _ w hw)
      have hblt : ∀ b ∈ bs, b < 2 ^ 11 := by
        intro b hb
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (hmem b hb)
        exact burnsideK42_applyWord_lt moGens hm w
      have := c.pow_le_card V5 bs hnd hblt hbV
      rw [hlen, hS.card] at this
      norm_num at this
  constructor
  · exact hsub m hm
  · intro hmw
    have hcard := c.card_eq V5 (fun m => decide (c.vm m ∈ V5)) (fun m hm => by simp)
    rw [hS.card] at hcard
    have hnd5 := burnsideK42_w5_nodup
    have hfin : ((List.range (2 ^ 11)).filter fun m => decide (c.vm m ∈ V5)).toFinset ⊆
        (w5Masks ()).toFinset := by
      intro x hx
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx ⊢
      exact hsub x hx.1 hx.2
    have hcardf : ((List.range (2 ^ 11)).filter fun m => decide (c.vm m ∈ V5)).toFinset.card =
        (w5Masks ()).toFinset.card := by
      rw [List.toFinset_card_of_nodup ((List.nodup_range).filter _),
        List.toFinset_card_of_nodup hnd5, ← hcard]
      have := burnsideK42_lists_facts.w5_len
      omega
    have heq := Finset.eq_of_subset_of_card_le hfin (le_of_eq hcardf.symm)
    have : m ∈ ((List.range (2 ^ 11)).filter fun m => decide (c.vm m ∈ V5)).toFinset := by
      rw [heq]; simpa using hmw
    simpa [hm] using this

private theorem burnsideK42_card_masks {n : ℕ} (c : MaskCoords V n) (U : Subgroup V) (l : List ℕ)
    (hnd : l.Nodup) (hlt : ∀ m ∈ l, m < 2 ^ n) (h : ∀ m < 2 ^ n, c.vm m ∈ U ↔ m ∈ l) :
    Nat.card U = l.length := by
  classical
  have h1 := c.card_eq U (fun m => decide (m ∈ l)) (fun m hm => by simp [h m hm])
  rw [h1]
  have h2 : ((List.range (2 ^ n)).filter fun m => decide (m ∈ l)).toFinset = l.toFinset := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun hx => hx.2, fun hx => ⟨hlt x hx, hx⟩⟩
  rw [← List.toFinset_card_of_nodup hnd, ← h2,
    List.toFinset_card_of_nodup ((List.nodup_range).filter _)]

private theorem burnsideK42_vm_inv {n : ℕ} (c : MaskCoords V n) (m : ℕ) : (c.vm m)⁻¹ = c.vm m :=
  inv_eq_of_mul_eq_one_right (by rw [← c.vm_xor, Nat.xor_self, c.vm_zero])

private theorem burnsideK42_vm_eq_iff {n : ℕ} (c : MaskCoords V n) {a b : ℕ} (ha : a < 2 ^ n)
    (hb : b < 2 ^ n) : c.vm a = c.vm b ↔ a = b :=
  ⟨c.vm_inj a b ha hb, fun h => by rw [h]⟩

variable [Finite V]

private theorem burnsideK42_Vz_mask
    (hS : burnsideK42_Std θ ε V5) {z0K : burnsideK42_K}
    (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) (m : ℕ) (hm : m < 2048) :
    (MaskCoords.ofEquiv ε).vm m ∈ CFSG.ASVolI.ChIJK.Vz V5 (θ z0K) ↔ m ∈ vzMasks () := by
  simp only [CFSG.ASVolI.ChIJK.Vz, Subgroup.mem_inf, mem_fixV_zpowers_iff_apply]
  rw [burnsideK42_V5_mask hS m hm, burnsideK42_theta_vm hS.hε hz0,
    burnsideK42_vm_eq_iff _ (actC11_lt _ _) hm]
  unfold vzMasks
  simp only [List.mem_filter, beq_iff_eq]

private theorem burnsideK42_rk_Vz
    (hS : burnsideK42_Std θ ε V5) {z0K : burnsideK42_K}
    (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) :
    rk ↥(CFSG.ASVolI.ChIJK.Vz V5 (θ z0K)) = 4 := by
  have hcard := burnsideK42_card_masks (MaskCoords.ofEquiv ε) _ (vzMasks ())
    (by unfold vzMasks; exact (burnsideK42_w5_nodup).filter _) 
    (fun m hm => burnsideK42_vz_lt m hm) (fun m hm => burnsideK42_Vz_mask hS hz0 m hm)
  unfold rk
  rw [hcard, burnsideK42_lists_facts.vz_len]
  have : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [this, padicValNat.prime_pow]

private theorem burnsideK42_centK_iff_arr {ms : List ℕ} (hms : ∀ m ∈ ms, m < 2048) {γ :
    burnsideK42_K}
    {a : Array ℕ} (ha : HasArr (γ : Equiv.Perm (Fin 24)) a) :
    γ ∈ burnsideK42_centK ms ↔ ∀ m ∈ ms, actC11 a m = m := by
  constructor
  · intro h m hm
    have := h m hm
    rw [burnsideK42_rho_toW γ ha] at this
    exact toW_inj (actC11_lt _ _) (hms m hm) this
  · intro h m hm
    rw [burnsideK42_rho_toW γ ha, h m hm]

private theorem burnsideK42_exists_z0K :
    ∃ z0K : burnsideK42_K, HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr := by
  have h := burnsideK42_lists_facts
  refine ⟨phi24 (⟨z0Idx, h.z0_lt⟩ : T24s2.Elem), ?_⟩
  have := burnsideK42_phi24_hasArr (⟨z0Idx, h.z0_lt⟩ : T24s2.Elem)
  simpa [h.z0_arr] using this

section Z0
variable
  {z0K : burnsideK42_K} (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr)
include hz0

private theorem burnsideK42_z0K_sq : z0K * z0K = 1 := by
  apply Subtype.ext
  have := burnsideK42_hasArr_mul hz0 hz0
  rw [burnsideK42_lists_facts.z0_sq] at this
  exact burnsideK42_hasArr_ext this burnsideK42_hasArr_one

private theorem burnsideK42_z0K_ne : z0K ≠ 1 := by
  intro h
  obtain ⟨i, hi, hne⟩ := burnsideK42_lists_facts.z0_ne
  apply hne
  have := hz0 ⟨i, hi⟩
  rw [h] at this
  simpa using this.symm

private theorem burnsideK42_z0K_mem_KO0 : z0K ∈ burnsideK42_KO0 := by
  rw [burnsideK42_mem_KO0]
  intro i hi hi24
  apply Fin.ext
  rw [hz0 ⟨i, hi24⟩]
  have := burnsideK42_lists_facts.z0_fixes
  simp only [fixesOct, List.all_eq_true, beq_iff_eq] at this
  exact this i hi

private theorem burnsideK42_z0K_mem_DZ : z0K ∈ burnsideK42_centK (vzMasks ()) := by
  rw [burnsideK42_centK_iff_arr (fun m hm => burnsideK42_vz_lt m hm) hz0]
  intro m hm
  unfold vzMasks at hm
  have := (List.mem_filter.1 hm).2
  simpa using this

end Z0

private theorem burnsideK42_theta_inj
    (hε : ∀ (γ : burnsideK42_K) (v : V), ε (θ γ v) = burnsideK42_rho γ (ε v)) :
    Function.Injective θ := by
  intro a b h
  apply rhoC11_injective _ le_rfl
  refine MulEquiv.ext fun w => ?_
  have h1 := hε a (ε.symm w)
  have h2 := hε b (ε.symm w)
  rw [MulEquiv.apply_symm_apply] at h1 h2
  show burnsideK42_rho a w = burnsideK42_rho b w
  rw [← h1, ← h2, h]

section Dz
variable
  (hS : burnsideK42_Std θ ε V5) {z0K : burnsideK42_K}
  (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr)
include hS hz0

private theorem burnsideK42_mem_Dz_iff (m : MulAut V) :
    m ∈ CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K) ↔
      ∃ γ ∈ burnsideK42_centK (vzMasks ()), θ γ = m := by
  simp only [CFSG.ASVolI.ChIJK.Dz, Subgroup.mem_inf, mem_centSub, MonoidHom.mem_range]
  constructor
  · rintro ⟨⟨γ, rfl⟩, hcent⟩
    refine ⟨γ, ?_, rfl⟩
    rw [burnsideK42_centK_iff_arr (fun m hm => burnsideK42_vz_lt m hm)
      (burnsideK42_hasArr_permArr _)]
    intro m hm
    have hm' := burnsideK42_vz_lt m hm
    have := hcent _ ((burnsideK42_Vz_mask hS hz0 m hm').2 hm)
    rw [burnsideK42_theta_vm hS.hε (burnsideK42_hasArr_permArr _),
      burnsideK42_vm_eq_iff _ (actC11_lt _ _) hm'] at this
    exact this
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨⟨γ, rfl⟩, fun u hu => ?_⟩
    obtain ⟨m, hm, rfl⟩ := (MaskCoords.ofEquiv ε).vm_surj u
    have hmv := (burnsideK42_Vz_mask hS hz0 m hm).1 hu
    have := (burnsideK42_centK_iff_arr (fun m hm => burnsideK42_vz_lt m hm)
      (burnsideK42_hasArr_permArr _)).1 hγ m hmv
    rw [burnsideK42_theta_vm hS.hε (burnsideK42_hasArr_permArr _), this]

private theorem burnsideK42_Dz_eq : CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K) =
    (burnsideK42_centK (vzMasks ())).map θ := by
  ext m
  rw [burnsideK42_mem_Dz_iff hS hz0, Subgroup.mem_map]

end Dz

private theorem burnsideK42_mod_parts :
    (∀ m ∈ vzMasks (), m ∈ combos (dmasks z0Arr)) ∧
    (∀ m < 2048, actC11 z0Arr m ^^^ m ∈ vzMasks ()) ∧
    ∀ ax ∈ (dzIdx ()).map tArr, ax = idArr ∨ ax = z0Arr ∨
      modOKx ax ((dzIdx ()).map tArr) = true := by
  have h := (Certificates.certificate7278).2.2
  simp only [modOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.contains_iff_mem,
    Bool.or_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun ax hax => or_assoc.1 (h3 ax hax)⟩

private theorem burnsideK42_modOKx_parts {ax : Array ℕ} {dz : List (Array ℕ)} (h : modOKx ax dz
    = true) :
    (∀ p ∈ dz, (∀ m < 2048, actC11 p (actC11 ax m ^^^ m) = actC11 ax m ^^^ m) →
      p = idArr ∨ p = ax ∨ p = z0Arr ∨ p = arrMul ax z0Arr) ∧
    (∀ f ∈ [idArr, ax, z0Arr, arrMul ax z0Arr], f ∈ dz ∧
      ∀ m < 2048, actC11 f (actC11 ax m ^^^ m) = actC11 ax m ^^^ m) ∧
    ((List.range 2048).filter fun m => actC11 ax m == m && actC11 z0Arr m == m).length = 64 ∧
    (∀ m < 2048, ∀ y ∈ [ax, z0Arr, arrMul ax z0Arr],
      actC11 ax (actC11 y m ^^^ m) = actC11 y m ^^^ m ∧
      actC11 z0Arr (actC11 y m ^^^ m) = actC11 y m ^^^ m) ∧
    indep6 (dmasks ax ++ dmasks z0Arr) = true ∧ indep6 (vzMasks () ++ dmasks ax) = true := by
  unfold modOKx at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, List.contains_iff_mem,
    beq_iff_eq, and_assoc, List.mem_filter] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, h3, ?_, h5, h6⟩
  · intro p hp hall
    have := h1 p ⟨hp, by simpa using hall⟩
    simpa using this
  · intro f hf
    obtain ⟨hfd, hfa⟩ := h2 f hf
    exact ⟨hfd, fun m hm => by simpa using hfa m hm⟩
  · intro m hm y hy
    have := h4 m hm y hy
    simpa using this

private theorem burnsideK42_mem_sup_zpowers {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) {x : G} :
    x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  constructor
  · intro hx
    have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ fourSub a b ha hb hab :=
      sup_le (Subgroup.zpowers_le.2 ((mem_fourSub ha hb hab a).2 (Or.inr (Or.inl rfl))))
        (Subgroup.zpowers_le.2 ((mem_fourSub ha hb hab b).2 (Or.inr (Or.inr (Or.inl rfl)))))
    exact (mem_fourSub ha hb hab x).1 (hle hx)
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

section DZfacts

private theorem burnsideK42_DZ_comm {γ₁ γ₂ : burnsideK42_K} (h₁ : γ₁ ∈ burnsideK42_centK
    (vzMasks ()))
    (h₂ : γ₂ ∈ burnsideK42_centK (vzMasks ())) : γ₁ * γ₂ = γ₂ * γ₁ := by
  obtain ⟨p₁, hp₁, hγ₁⟩ := burnsideK42_DZ_arr h₁
  obtain ⟨p₂, hp₂, hγ₂⟩ := burnsideK42_DZ_arr h₂
  apply Subtype.ext
  have := burnsideK42_hasArr_mul hγ₁ hγ₂
  rw [burnsideK42_lists_facts.dz_abel p₁ hp₁ p₂ hp₂] at this
  exact burnsideK42_hasArr_ext this (burnsideK42_hasArr_mul hγ₂ hγ₁)

private theorem burnsideK42_DZ_sq {γ : burnsideK42_K} (h : γ ∈ burnsideK42_centK (vzMasks ())) :
    γ * γ = 1 := by
  obtain ⟨p, hp, hγ⟩ := burnsideK42_DZ_arr h
  apply Subtype.ext
  have := burnsideK42_hasArr_mul hγ hγ
  rw [burnsideK42_lists_facts.dz_sq p hp] at this
  exact burnsideK42_hasArr_ext this burnsideK42_hasArr_one

end DZfacts

private theorem burnsideK42_dmasks_lt (a : Array ℕ) : ∀ b ∈ dmasks a, b < 2048 := by
  intro b hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
  have hj' : j < 11 := List.mem_range.1 hj
  exact Nat.xor_lt_two_pow (actC11_lt _ _) (Nat.pow_lt_pow_right (by norm_num) hj')

private theorem burnsideK42_commV_mono {X Y : Subgroup (MulAut V)} (h : X ≤ Y) : commV X ≤
    commV Y := by
  unfold commV
  apply Subgroup.closure_mono
  rintro _ ⟨x, hx, v, rfl⟩
  exact ⟨x, h hx, v, rfl⟩

section SCb
variable (hS : burnsideK42_Std θ ε V5)
include hS

private theorem burnsideK42_comm_gen (γ : burnsideK42_K) (m : ℕ) :
    θ γ ((MaskCoords.ofEquiv ε).vm m) * ((MaskCoords.ofEquiv ε).vm m)⁻¹ =
      (MaskCoords.ofEquiv ε).vm (actC11 (burnsideK42_permArr (γ : Equiv.Perm (Fin 24))) m ^^^ m) := by
  rw [burnsideK42_theta_vm hS.hε (burnsideK42_hasArr_permArr _), (MaskCoords.ofEquiv ε).vm_xor,
    burnsideK42_vm_inv]

private theorem burnsideK42_comm_gen' {γ : burnsideK42_K} {a : Array ℕ}
    (ha : HasArr (γ : Equiv.Perm (Fin 24)) a) (m : ℕ) :
    θ γ ((MaskCoords.ofEquiv ε).vm m) * ((MaskCoords.ofEquiv ε).vm m)⁻¹ =
      (MaskCoords.ofEquiv ε).vm (actC11 a m ^^^ m) := by
  rw [burnsideK42_theta_vm hS.hε ha, (MaskCoords.ofEquiv ε).vm_xor, burnsideK42_vm_inv]

private theorem burnsideK42_cent_commV_of {γ : burnsideK42_K} {a : Array ℕ}
    (ha : HasArr (γ : Equiv.Perm (Fin 24)) a) (hd2 : θ γ * θ γ = 1) {g : MulAut V}
    {a' : Array ℕ} {γ' : burnsideK42_K} (hg : g = θ γ') (ha' : HasArr (γ' : Equiv.Perm (Fin 24)) a')
    (hfix : ∀ m < 2048, actC11 a' (actC11 a m ^^^ m) = actC11 a m ^^^ m) :
    g ∈ centSub (commV (Subgroup.zpowers (θ γ))) := by
  intro u hu
  have hle : commV (Subgroup.zpowers (θ γ)) ≤ fixV (Subgroup.zpowers g) := by
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨m, hm, rfl⟩ := (MaskCoords.ofEquiv ε).vm_surj v
    rcases burnsideK42_zpowers_sq hd2 hx with rfl | rfl
    · simp only [SetLike.mem_coe, MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
    · show θ γ _ * _ ∈ _
      rw [burnsideK42_comm_gen' hS ha m, SetLike.mem_coe, mem_fixV_zpowers_iff_apply, hg,
        burnsideK42_theta_vm hS.hε ha', hfix m hm]
  exact mem_fixV_zpowers_iff_apply.1 (hle hu)

private theorem burnsideK42_fix_of_cent_commV {γ : burnsideK42_K} {a : Array ℕ}
    (ha : HasArr (γ : Equiv.Perm (Fin 24)) a) {γ' : burnsideK42_K} {a' : Array ℕ}
    (ha' : HasArr (γ' : Equiv.Perm (Fin 24)) a')
    (hg : θ γ' ∈ centSub (commV (Subgroup.zpowers (θ γ)))) :
    ∀ m < 2048, actC11 a' (actC11 a m ^^^ m) = actC11 a m ^^^ m := by
  intro m hm
  have hmem : θ γ ((MaskCoords.ofEquiv ε).vm m) * ((MaskCoords.ofEquiv ε).vm m)⁻¹ ∈
      commV (Subgroup.zpowers (θ γ)) :=
    Subgroup.subset_closure ⟨θ γ, Subgroup.mem_zpowers _, _, rfl⟩
  have h := hg _ hmem
  rw [burnsideK42_comm_gen' hS ha m, burnsideK42_theta_vm hS.hε ha',
    burnsideK42_vm_eq_iff _ (actC11_lt _ _) (Nat.xor_lt_two_pow (actC11_lt _ _) hm)] at h
  exact h

private theorem burnsideK42_dmask_mem_commV {γ : burnsideK42_K} {a : Array ℕ}
    (ha : HasArr (γ : Equiv.Perm (Fin 24)) a) {X : Subgroup (MulAut V)} (hX : θ γ ∈ X) :
    ∀ b ∈ dmasks a, (MaskCoords.ofEquiv ε).vm b ∈ commV X := by
  intro b hb
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hb
  rw [← burnsideK42_comm_gen' hS ha]
  exact Subgroup.subset_closure ⟨θ γ, hX, _, rfl⟩

end SCb

section SC
variable
  (hS : burnsideK42_Std θ ε V5) {z0K : burnsideK42_K}
  (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr)
include hS hz0

private theorem burnsideK42_Dz_inf_KO :
    CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K) ⊓ burnsideK42_KO0.map θ =
      Subgroup.zpowers (θ z0K) := by
  rw [burnsideK42_Dz_eq hS hz0]
  apply le_antisymm
  · rintro m ⟨⟨γ, hγ, rfl⟩, ⟨γ', hγ', hθ⟩⟩
    have hγγ : γ' = γ := burnsideK42_theta_inj hS.hε hθ
    subst hγγ
    obtain ⟨p, hp, hγp⟩ := burnsideK42_DZ_arr hγ
    have hfix : fixesOct (tArr p) = true := by
      simp only [fixesOct, List.all_eq_true, beq_iff_eq]
      intro i hi
      have hi24 := burnsideK42_octPts_lt i hi
      have := (burnsideK42_mem_KO0.1 hγ') i hi hi24
      have h2 := hγp ⟨i, hi24⟩
      rw [this] at h2
      exact h2.symm
    rcases (burnsideK42_lists_facts.dz_k p hp).1 hfix with h | h
    · have : γ' = 1 := Subtype.ext (burnsideK42_hasArr_ext hγp (h ▸ burnsideK42_hasArr_one))
      rw [this, map_one]
      exact Subgroup.one_mem _
    · have : γ' = z0K := Subtype.ext (burnsideK42_hasArr_ext hγp (h ▸ hz0))
      rw [this]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨Subgroup.mem_map_of_mem θ (burnsideK42_z0K_mem_DZ hz0),
      Subgroup.mem_map_of_mem θ (burnsideK42_z0K_mem_KO0 hz0)⟩

private theorem burnsideK42_isE2_Dz : IsE2 4 ↥(CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K)) := by
  rw [burnsideK42_Dz_eq hS hz0]
  have hcard : Nat.card ↥((burnsideK42_centK (vzMasks ())).map θ) = 2 ^ 4 := by
    rw [Subgroup.card_map_of_injective (burnsideK42_theta_inj hS.hε), burnsideK42_DZ_card]
    norm_num
  refine burnsideK42_isE2 (n := 4) ?_ ?_ hcard
  · rintro ⟨_, ⟨γ₁, h₁, rfl⟩⟩ ⟨_, ⟨γ₂, h₂, rfl⟩⟩
    apply Subtype.ext
    show θ γ₁ * θ γ₂ = θ γ₂ * θ γ₁
    rw [← map_mul, ← map_mul, burnsideK42_DZ_comm h₁ h₂]
  · rintro ⟨_, ⟨γ, h, rfl⟩⟩
    apply Subtype.ext
    show (θ γ) ^ 2 = 1
    rw [sq, ← map_mul, burnsideK42_DZ_sq h, map_one]

private theorem burnsideK42_commV_z :
    commV (Subgroup.zpowers (θ z0K)) = CFSG.ASVolI.ChIJK.Vz V5 (θ z0K) := by
  set c := MaskCoords.ofEquiv ε with hc
  have hz2 : θ z0K * θ z0K = 1 := by
    rw [← map_mul, burnsideK42_z0K_sq hz0, map_one]
  have harr : ∀ m, actC11 (burnsideK42_permArr (z0K : Equiv.Perm (Fin 24))) m = actC11 z0Arr m := by
    intro m
    have h1 := burnsideK42_rho_toW z0K (burnsideK42_hasArr_permArr _) m
    have h2 := burnsideK42_rho_toW z0K hz0 m
    exact toW_inj (actC11_lt _ _) (actC11_lt _ _) (h1.symm.trans h2)
  apply le_antisymm
  · unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨m, hm, rfl⟩ := c.vm_surj v
    rcases burnsideK42_zpowers_sq hz2 hx with rfl | rfl
    · simp only [SetLike.mem_coe, MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
    · show θ z0K (c.vm m) * (c.vm m)⁻¹ ∈ _
      rw [burnsideK42_comm_gen hS z0K m, harr]
      exact (burnsideK42_Vz_mask hS hz0 _ (by
        have := actC11_lt z0Arr m
        exact Nat.xor_lt_two_pow this hm)).2 ((burnsideK42_mod_parts).2.1 m hm)
  · intro u hu
    obtain ⟨m, hm, rfl⟩ := c.vm_surj u
    have hmv := (burnsideK42_Vz_mask hS hz0 m hm).1 hu
    have hcomb := (burnsideK42_mod_parts).1 m hmv
    refine c.vm_mem_of_combos (commV (Subgroup.zpowers (θ z0K))) (fun a ha => ?_) m hcomb
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    have := burnsideK42_comm_gen hS z0K (2 ^ j)
    rw [harr] at this
    rw [← this]
    exact Subgroup.subset_closure ⟨θ z0K, Subgroup.mem_zpowers _, _, rfl⟩

private theorem burnsideK42_d_data {d : MulAut V}
    (hd : d ∈ CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K))
    (hdz : d ∉ Subgroup.zpowers (θ z0K)) :
    ∃ γ : burnsideK42_K, θ γ = d ∧ γ ∈ burnsideK42_centK (vzMasks ()) ∧ ∃ p : ℕ,
      p ∈ dzIdx () ∧ HasArr (γ : Equiv.Perm (Fin 24)) (tArr p) ∧
      modOKx (tArr p) ((dzIdx ()).map tArr) = true := by
  obtain ⟨γ, hγ, rfl⟩ := (burnsideK42_mem_Dz_iff hS hz0 d).1 hd
  obtain ⟨p, hp, hγp⟩ := burnsideK42_DZ_arr hγ
  refine ⟨γ, rfl, hγ, p, hp, hγp, ?_⟩
  rcases (burnsideK42_mod_parts).2.2 (tArr p) (List.mem_map_of_mem hp) with h | h | h
  · exfalso
    apply hdz
    have : γ = 1 := Subtype.ext (burnsideK42_hasArr_ext hγp (h ▸ burnsideK42_hasArr_one))
    rw [this, map_one]
    exact Subgroup.one_mem _
  · exfalso
    apply hdz
    have : γ = z0K := Subtype.ext (burnsideK42_hasArr_ext hγp (h ▸ hz0))
    rw [this]
    exact Subgroup.mem_zpowers _
  · exact h

private theorem burnsideK42_conj3 {d : MulAut V}
    (hd : d ∈ CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K))
    (hdz : d ∉ Subgroup.zpowers (θ z0K)) :
    Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K) =
      CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K) ⊓ CFSG.ASVolI.ChIJK.Dd θ.range d := by
  obtain ⟨γ, rfl, hγ, p, hp, hax, hmod⟩ := burnsideK42_d_data hS hz0 hd hdz
  obtain ⟨hstab, hfour, -, -, -, -⟩ := burnsideK42_modOKx_parts hmod
  set ax := tArr p with hax_def
  have hd2 : θ γ * θ γ = 1 := by rw [← map_mul, burnsideK42_DZ_sq hγ, map_one]
  have hfix1 : ∀ m < 2048, actC11 ax (actC11 ax m ^^^ m) = actC11 ax m ^^^ m :=
    (hfour ax (by simp)).2
  have hfix2 : ∀ m < 2048, actC11 z0Arr (actC11 ax m ^^^ m) = actC11 ax m ^^^ m :=
    (hfour z0Arr (by simp)).2
  have hdD : θ γ ∈ CFSG.ASVolI.ChIJK.Dd θ.range (θ γ) :=
    ⟨⟨γ, rfl⟩, burnsideK42_cent_commV_of hS hax hd2 rfl hax hfix1⟩
  have hzD : θ z0K ∈ CFSG.ASVolI.ChIJK.Dd θ.range (θ γ) :=
    ⟨⟨z0K, rfl⟩, burnsideK42_cent_commV_of hS hax hd2 rfl hz0 hfix2⟩
  have hzDz : θ z0K ∈ CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K) := by
    rw [burnsideK42_Dz_eq hS hz0]
    exact Subgroup.mem_map_of_mem θ (burnsideK42_z0K_mem_DZ hz0)
  apply le_antisymm
  · refine sup_le (Subgroup.zpowers_le.2 ⟨hd, hdD⟩) (Subgroup.zpowers_le.2 ⟨hzDz, hzD⟩)
  · rintro m ⟨hmDz, -, hmcent⟩
    obtain ⟨γ', hγ', rfl⟩ := (burnsideK42_mem_Dz_iff hS hz0 m).1 hmDz
    obtain ⟨p', hp', hγp'⟩ := burnsideK42_DZ_arr hγ'
    have hfix := burnsideK42_fix_of_cent_commV hS hax hγp' hmcent
    have h4 := hstab (tArr p') (List.mem_map_of_mem hp') hfix
    have hz2 : θ z0K * θ z0K = 1 := by rw [← map_mul, burnsideK42_z0K_sq hz0, map_one]
    have hcomm : θ γ * θ z0K = θ z0K * θ γ := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have h1 := burnsideK42_hasArr_mul hax hz0
      have h2 := burnsideK42_hasArr_mul hz0 hax
      rw [burnsideK42_lists_facts.dz_comm p hp] at h1
      exact burnsideK42_hasArr_ext h1 h2
    rw [burnsideK42_mem_sup_zpowers hd2 hz2 hcomm]
    rcases h4 with h | h | h | h
    · left
      have : γ' = 1 := Subtype.ext (burnsideK42_hasArr_ext hγp' (h ▸ burnsideK42_hasArr_one))
      rw [this, map_one]
    · right; left
      have : γ' = γ := Subtype.ext (burnsideK42_hasArr_ext hγp' (h ▸ hax))
      rw [this]
    · right; right; left
      have : γ' = z0K := Subtype.ext (burnsideK42_hasArr_ext hγp' (h ▸ hz0))
      rw [this]
    · right; right; right
      have : γ' = γ * z0K := Subtype.ext (burnsideK42_hasArr_ext hγp'
        (h ▸ burnsideK42_hasArr_mul hax hz0))
      rw [this, map_mul]

private theorem burnsideK42_conj5 {d : MulAut V}
    (hd : d ∈ CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K))
    (hdz : d ∉ Subgroup.zpowers (θ z0K)) :
    fixV (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K)) =
        commV (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K)) ∧
      commV (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K)) =
        CFSG.ASVolI.ChIJK.Vz V5 (θ z0K) ⊔ commV (Subgroup.zpowers d) ∧
      rk ↥(fixV (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K))) = 6 := by
  obtain ⟨γ, rfl, hγ, p, hp, hax, hmod⟩ := burnsideK42_d_data hS hz0 hd hdz
  obtain ⟨hstab, hfour, hfixE, hquad, hi1, hi2⟩ := burnsideK42_modOKx_parts hmod
  clear hmod
  have hd2 : θ γ * θ γ = 1 := by rw [← map_mul, burnsideK42_DZ_sq hγ, map_one]
  have hz2 : θ z0K * θ z0K = 1 := by rw [← map_mul, burnsideK42_z0K_sq hz0, map_one]
  have hcomm : θ γ * θ z0K = θ z0K * θ γ := by
    have h1 := burnsideK42_hasArr_mul hax hz0
    have h2 := burnsideK42_hasArr_mul hz0 hax
    rw [burnsideK42_lists_facts.dz_comm p hp] at h1
    have hK : γ * z0K = z0K * γ := Subtype.ext (burnsideK42_hasArr_ext h1 h2)
    rw [← map_mul, ← map_mul, hK]
  have hdE : θ γ ∈ Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hzE : θ z0K ∈ Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have haxz : HasArr ((γ * z0K : burnsideK42_K) : Equiv.Perm (Fin 24)) (arrMul (tArr p) z0Arr) :=
    burnsideK42_hasArr_mul hax hz0
  have hfixmask : ∀ m < 2048, (MaskCoords.ofEquiv ε).vm m ∈
      fixV (Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K)) ↔
      actC11 (tArr p) m = m ∧ actC11 z0Arr m = m := by
    intro m hm
    constructor
    · intro h
      have h1 := (mem_fixV.1 h) _ hdE
      have h2 := (mem_fixV.1 h) _ hzE
      rw [burnsideK42_theta_vm hS.hε hax, burnsideK42_vm_eq_iff _ (actC11_lt _ _) hm] at h1
      rw [burnsideK42_theta_vm hS.hε hz0, burnsideK42_vm_eq_iff _ (actC11_lt _ _) hm] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [mem_fixV]
      intro x hx
      rcases (burnsideK42_mem_sup_zpowers hd2 hz2 hcomm).1 hx with rfl | rfl | rfl | rfl
      · simp
      · rw [burnsideK42_theta_vm hS.hε hax, h1]
      · rw [burnsideK42_theta_vm hS.hε hz0, h2]
      · rw [MulAut.mul_apply, burnsideK42_theta_vm hS.hε hz0, h2,
          burnsideK42_theta_vm hS.hε hax, h1]
  have hfixcard : Nat.card ↥(fixV (Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K))) = 64 := by
    have hnd : ((List.range 2048).filter fun m => actC11 (tArr p) m == m &&
        actC11 z0Arr m == m).Nodup := (List.nodup_range).filter _
    have := burnsideK42_card_masks (MaskCoords.ofEquiv ε) _ _ hnd
      (fun m hm => by
        have := (List.mem_filter.1 hm).1
        simpa using this)
      (fun m hm => by
        rw [hfixmask m hm, List.mem_filter, List.mem_range]
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨fun h => ⟨hm, h⟩, fun h => h.2⟩)
    rw [this, hfixE]
  have hle : commV (Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K)) ≤
      fixV (Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K)) := by
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨m, hm, rfl⟩ := (MaskCoords.ofEquiv ε).vm_surj v
    rcases (burnsideK42_mem_sup_zpowers hd2 hz2 hcomm).1 hx with rfl | rfl | rfl | rfl
    · simp only [SetLike.mem_coe, MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
    · show θ γ _ * _ ∈ _
      rw [burnsideK42_comm_gen' hS hax m, SetLike.mem_coe,
        hfixmask _ (Nat.xor_lt_two_pow (actC11_lt _ _) hm)]
      exact hquad m hm _ (by simp)
    · show θ z0K _ * _ ∈ _
      rw [burnsideK42_comm_gen' hS hz0 m, SetLike.mem_coe,
        hfixmask _ (Nat.xor_lt_two_pow (actC11_lt _ _) hm)]
      exact hquad m hm _ (by simp)
    · show (θ γ * θ z0K) _ * _ ∈ _
      rw [show θ γ * θ z0K = θ (γ * z0K) from (map_mul _ _ _).symm,
        burnsideK42_comm_gen' hS haxz m, SetLike.mem_coe,
        hfixmask _ (Nat.xor_lt_two_pow (actC11_lt _ _) hm)]
      exact hquad m hm _ (by simp)
  have hcommE : ∀ (g : MulAut V) (hg : g ∈ Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K)) (m : ℕ),
      g ((MaskCoords.ofEquiv ε).vm m) * ((MaskCoords.ofEquiv ε).vm m)⁻¹ ∈
        commV (Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K)) :=
    fun g hg m => Subgroup.subset_closure ⟨g, hg, _, rfl⟩
  have hlower : 2 ^ 6 ≤ Nat.card ↥(commV (Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K))) := by
    obtain ⟨bs, hlen, hnd, hmem⟩ := burnsideK42_indep6_spec hi1
    have hlt : ∀ b ∈ bs, b < 2 ^ 11 := by
      intro b hb
      rcases List.mem_append.1 (hmem b hb) with hb' | hb'
      · exact burnsideK42_dmasks_lt _ b hb'
      · exact burnsideK42_dmasks_lt _ b hb'
    have hU : ∀ b ∈ bs, (MaskCoords.ofEquiv ε).vm b ∈
        commV (Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K)) := by
      intro b hb
      rcases List.mem_append.1 (hmem b hb) with hb' | hb'
      · exact burnsideK42_dmask_mem_commV hS hax hdE b hb'
      · exact burnsideK42_dmask_mem_commV hS hz0 hzE b hb'
    have := (MaskCoords.ofEquiv ε).pow_le_card _ bs hnd hlt hU
    rwa [hlen] at this
  have heq : commV (Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K)) =
      fixV (Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K)) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hfixcard]; omega)
  have hcommcard : Nat.card ↥(commV (Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K))) = 64 := by
    rw [heq, hfixcard]
  refine ⟨heq.symm, ?_, ?_⟩
  ·
    have hVz := burnsideK42_commV_z hS hz0
    have hsub : CFSG.ASVolI.ChIJK.Vz V5 (θ z0K) ⊔ commV (Subgroup.zpowers (θ γ)) ≤
        commV (Subgroup.zpowers (θ γ) ⊔ Subgroup.zpowers (θ z0K)) := by
      refine sup_le ?_ (burnsideK42_commV_mono le_sup_left)
      rw [← hVz]
      exact burnsideK42_commV_mono le_sup_right
    have hlow : 2 ^ 6 ≤ Nat.card ↥(CFSG.ASVolI.ChIJK.Vz V5 (θ z0K) ⊔
        commV (Subgroup.zpowers (θ γ))) := by
      obtain ⟨bs, hlen, hnd, hmem⟩ := burnsideK42_indep6_spec hi2
      have hlt : ∀ b ∈ bs, b < 2 ^ 11 := by
        intro b hb
        rcases List.mem_append.1 (hmem b hb) with hb' | hb'
        · exact burnsideK42_vz_lt b hb'
        · exact burnsideK42_dmasks_lt _ b hb'
      have hU : ∀ b ∈ bs, (MaskCoords.ofEquiv ε).vm b ∈ CFSG.ASVolI.ChIJK.Vz V5 (θ z0K) ⊔
          commV (Subgroup.zpowers (θ γ)) := by
        intro b hb
        rcases List.mem_append.1 (hmem b hb) with hb' | hb'
        · exact Subgroup.mem_sup_left ((burnsideK42_Vz_mask hS hz0 b
            (burnsideK42_vz_lt b hb')).2 hb')
        · exact Subgroup.mem_sup_right (burnsideK42_dmask_mem_commV hS hax
            (Subgroup.mem_zpowers _) b hb')
      have := (MaskCoords.ofEquiv ε).pow_le_card _ bs hnd hlt hU
      rwa [hlen] at this
    exact (Subgroup.eq_of_le_of_card_ge hsub (by rw [hcommcard]; omega)).symm
  · unfold rk
    rw [hfixcard]
    have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [h64, padicValNat.prime_pow]

end SC

end Mod

section PCoreGen

private theorem burnsideK42_pCoreOf_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (C : Subgroup G) :
    CFSG.Open.pCoreOf 2 (C.map f) = (CFSG.Open.pCoreOf 2 C).map f := by
  show (CFSG.pCore 2 ↥(C.map f)).map (C.map f).subtype =
    ((CFSG.pCore 2 ↥C).map C.subtype).map f
  have h := CFSG.pCore_map_iso 2 (Subgroup.equivMapOfInjective C f hf)
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem burnsideK42_le_pCoreOf {G : Type*} [Group G] {C N : Subgroup G} (hNC : N ≤ C)
    (hn : (N.subgroupOf C).Normal) (hp : IsPGroup 2 N) : N ≤ CFSG.Open.pCoreOf 2 C := by
  intro x hx
  show x ∈ (CFSG.pCore 2 ↥C).map C.subtype
  refine ⟨⟨x, hNC hx⟩, ?_, rfl⟩
  have hp' : IsPGroup 2 (N.subgroupOf C) := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNC).symm
  have hmem : N.subgroupOf C ∈ {K : Subgroup ↥C | K.Normal ∧ IsPGroup 2 K} := ⟨hn, hp'⟩
  exact (le_sSup hmem : N.subgroupOf C ≤ CFSG.pCore 2 ↥C) (Subgroup.mem_subgroupOf.2 hx)

end PCoreGen

section SylowC
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

private theorem burnsideK42_card_Tsub :
    Nat.card ↥burnsideK42_Tsub = 1024 := by
  have h1 : Nat.card ↥burnsideK42_Tsub = Nat.card T24s2.Elem :=
    (Nat.card_congr (MonoidHom.ofInjective burnsideK42_phi24_injective).toEquiv).symm
  rw [h1, PT.card_elem, T24s2_ok.2.1]

private theorem burnsideK42_Tsub_le_cent
    {z0K : burnsideK42_K} (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) :
    burnsideK42_Tsub ≤ Subgroup.centralizer ({z0K} : Set burnsideK42_K) := by
  have h := burnsideK42_lists_facts
  let z : T24s2.Elem := ⟨z0Idx, h.z0_lt⟩
  have hzK : phi24 z = z0K := by
    apply Subtype.ext
    apply burnsideK42_hasArr_ext _ hz0
    have := burnsideK42_phi24_hasArr z
    simpa [z, h.z0_arr] using this
  rintro _ ⟨s, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← hzK, ← map_mul, ← map_mul]
  congr 1
  apply PT.Elem.ext'
  rw [PT.idx_mul, PT.idx_mul]
  exact h.z0_central s.idx s.lt

private theorem burnsideK42_exists_sylowC
    {z0K : burnsideK42_K}
    (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) :
    ∃ P : Sylow 2 ↥(Subgroup.centralizer ({z0K} : Set burnsideK42_K)),
      ∀ x : ↥(Subgroup.centralizer ({z0K} : Set burnsideK42_K)),
        x ∈ P ↔ (x : burnsideK42_K) ∈ burnsideK42_Tsub := by
  have hT := burnsideK42_Tsub_le_cent hz0
  set C := Subgroup.centralizer ({z0K} : Set burnsideK42_K) with hC
  have hcardT := burnsideK42_card_Tsub
  have hCK : Nat.card ↥C ∣ Nat.card burnsideK42_K := Subgroup.card_subgroup_dvd_card C
  have hTC : Nat.card ↥burnsideK42_Tsub ∣ Nat.card ↥C := Subgroup.card_dvd_of_le hT
  have hK : Nat.card burnsideK42_K = 2 ^ 10 * 239085 := by
    rw [burnsideK42_K, CFSG.Monster.Code.card_AutPerm]; norm_num
  have hCpos : Nat.card ↥C ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card ↥C).factorization 2 = 10 := by
    have h1 : 2 ^ 10 ∣ Nat.card ↥C := by rw [← show (1024 : ℕ) = 2 ^ 10 by norm_num, ← hcardT]; exact hTC
    have h2 : ¬ 2 ^ 11 ∣ Nat.card ↥C := by
      intro h
      have := h.trans hCK
      rw [hK] at this
      omega
    have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hCpos).1 h1
    have h4 : ¬ 11 ≤ (Nat.card ↥C).factorization 2 := fun h =>
      h2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hCpos).2 h)
    omega
  have hcard : Nat.card ↥(burnsideK42_Tsub.subgroupOf C) =
      2 ^ (Nat.card ↥C).factorization 2 := by
    rw [hfac, show (2 : ℕ) ^ 10 = 1024 by norm_num, ← hcardT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv
  refine ⟨Sylow.ofCard _ hcard, fun x => ?_⟩
  have := Sylow.coe_ofCard (burnsideK42_Tsub.subgroupOf C) hcard
  change x ∈ ((Sylow.ofCard _ hcard : Sylow 2 ↥C) : Subgroup ↥C) ↔ _
  rw [this, Subgroup.mem_subgroupOf]

end SylowC

section Arrays
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

private theorem burnsideK42_arr_eq {σ : Equiv.Perm (Fin 24)} {a b : Array ℕ} (ha : HasArr σ a)
    (hb : HasArr σ b) (hsa : a.size = 24) (hsb : b.size = 24) : a = b := by
  apply Array.ext (hsa.trans hsb.symm)
  intro i hi1 hi2
  have h1 := ha ⟨i, hsa ▸ hi1⟩
  have h2 := hb ⟨i, hsa ▸ hi1⟩
  simp only at h1 h2
  rw [getElem!_pos a i hi1] at h1
  rw [getElem!_pos b i hi2] at h2
  exact h1.symm.trans h2

private theorem burnsideK42_arrMul_size (a b : Array ℕ) : (arrMul a b).size = 24 := by
  simp [arrMul]

private theorem burnsideK42_tArr_size
    {p : ℕ} (hp : p < T24s2.n) :
    (tArr p).size = 24 :=
  burnsideK42_lists_facts.t_size p hp

private theorem burnsideK42_mem_elems_of_Tsub
    {y : burnsideK42_K} (hy : y ∈ burnsideK42_Tsub) {a : Array ℕ}
    (ha : HasArr (y : Equiv.Perm (Fin 24)) a) (hsa : a.size = 24) : a ∈ T24s2.elems := by
  obtain ⟨s, rfl⟩ := hy
  have h1 := burnsideK42_phi24_hasArr s
  have h2 := burnsideK42_arr_eq h1 ha (burnsideK42_tArr_size s.lt) hsa
  rw [← h2]
  have hs : s.idx < T24s2.elems.size := by rw [PT.size_elems]; exact s.lt
  change T24s2.elems[s.idx]! ∈ T24s2.elems
  rw [getElem!_pos T24s2.elems s.idx hs]
  exact Array.getElem_mem hs

end Arrays

section Sylow2
open scoped Pointwise

private theorem burnsideK42_smul_mem {G : Type*} [Group G] (P : Sylow 2 G) (g x : G) :
    x ∈ (g • P) ↔ g⁻¹ * x * g ∈ P := by
  change x ∈ (MulAut.conj g • (P : Subgroup G)) ↔ _
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]
  rfl

private theorem burnsideK42_pCore_mem_sylow_conj {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (P : Sylow 2 ↥C) (x : ↥C) (hx : (x : G) ∈ CFSG.Open.pCoreOf 2 C) (c : ↥C) :
    c⁻¹ * x * c ∈ P := by
  have hxp : x ∈ CFSG.pCore 2 ↥C := (Subgroup.mem_map_iff_mem C.subtype_injective).1 hx
  have hle : CFSG.pCore 2 ↥C ≤ ((c • P : Sylow 2 ↥C) : Subgroup ↥C) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥C)).le_sylow_of_normal (c • P)
  exact (burnsideK42_smul_mem P c x).1 (hle hxp)

private theorem burnsideK42_exists_conj_sylow {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (P : Sylow 2 ↥C) (x : ↥C) (hx : x * x = 1) : ∃ g : ↥C, g * x * g⁻¹ ∈ P := by
  have hX : IsPGroup 2 (Subgroup.zpowers x) := by
    intro y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have h2 : x ^ ((2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_two, hx]
    show (y : ↥C) ^ (2 ^ 1) = 1
    rw [← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, h2, one_zpow]
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C Q P
  refine ⟨g, ?_⟩
  have hxQ : x ∈ Q := hQ (Subgroup.mem_zpowers x)
  have : g * x * g⁻¹ ∈ (g • Q : Sylow 2 ↥C) := by
    rw [burnsideK42_smul_mem]
    have h3 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [h3]
    exact hxQ
  rwa [hg] at this

end Sylow2

section PCoreK
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

private theorem burnsideK42_z0K_fix_iff
    {z0K : burnsideK42_K} (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) (u : Fin 24) :
    (z0K : Equiv.Perm (Fin 24)) u = u ↔ (u : ℕ) ∈ octPts := by
  have h := burnsideK42_lists_facts.z0_fix_iff u u.2
  rw [← h, ← hz0 u]
  exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩

private theorem burnsideK42_isPGroup_Tsub : IsPGroup 2
    ↥burnsideK42_Tsub :=
  IsPGroup.of_card (n := 10) (by rw [burnsideK42_card_Tsub]; norm_num)

private theorem burnsideK42_KO0_conj_mem
    {z0K : burnsideK42_K} (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) {c : burnsideK42_K}
    (hc : c ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K)) {γ : burnsideK42_K}
    (hγ : γ ∈ burnsideK42_KO0) : c * γ * c⁻¹ ∈ burnsideK42_KO0 := by
  rw [burnsideK42_mem_KO0]
  intro i hi hi24
  have hcz : (c : Equiv.Perm (Fin 24)) * z0K = z0K * c := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hc
    exact congrArg Subtype.val this
  have hcz' : (c : Equiv.Perm (Fin 24))⁻¹ * z0K = z0K * (c : Equiv.Perm (Fin 24))⁻¹ := by
    calc (c : Equiv.Perm (Fin 24))⁻¹ * z0K
        = (c : Equiv.Perm (Fin 24))⁻¹ * (z0K * c) * (c : Equiv.Perm (Fin 24))⁻¹ := by group
      _ = (c : Equiv.Perm (Fin 24))⁻¹ * (c * z0K) * (c : Equiv.Perm (Fin 24))⁻¹ := by rw [hcz]
      _ = z0K * (c : Equiv.Perm (Fin 24))⁻¹ := by group
  set x : Fin 24 := ⟨i, hi24⟩ with hxdef
  have hx : (z0K : Equiv.Perm (Fin 24)) x = x := (burnsideK42_z0K_fix_iff hz0 x).2 hi
  set u : Fin 24 := (c : Equiv.Perm (Fin 24))⁻¹ x with hu
  have hzu : (z0K : Equiv.Perm (Fin 24)) u = u := by
    have h1 : (z0K : Equiv.Perm (Fin 24)) ((c : Equiv.Perm (Fin 24))⁻¹ x) =
        (c : Equiv.Perm (Fin 24))⁻¹ ((z0K : Equiv.Perm (Fin 24)) x) := by
      have := congrArg (fun f : Equiv.Perm (Fin 24) => f x) hcz'
      simp only [Equiv.Perm.mul_apply] at this
      exact this.symm
    rw [hu, h1, hx]
  have hu1 : (u : ℕ) ∈ octPts := (burnsideK42_z0K_fix_iff hz0 u).1 hzu
  have hγu : (γ : Equiv.Perm (Fin 24)) u = u := by
    have := (burnsideK42_mem_KO0.1 hγ) u hu1 u.2
    exact this
  apply Fin.ext
  show (((c * γ * c⁻¹ : burnsideK42_K) : Equiv.Perm (Fin 24)) x : ℕ) = i
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
  rw [← hu, hγu, hu]
  simp
  rfl

end PCoreK

section Parts
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

private theorem burnsideK42_syl_parts :
    (∀ c ∈ sylConj, inAutOK c = true ∧ arrMul c z0Arr = arrMul z0Arr c) ∧
    ∀ p < T24s2.n, (∀ c ∈ sylConj, arrMul (arrMul (invArr c) (tArr p)) c ∈ T24s2.elems) →
      ∃ k ∈ (kIdx ()).map tArr, ∃ d ∈ (dzIdx ()).map tArr, arrMul k d = tArr p := by
  have h := (Certificates.certificate7278).1
  simp only [sylOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun p hp hall => ?_⟩
  rcases h2 p hp with h | h
  · exfalso
    have : (sylConj.all fun c =>
        T24s2.elems.contains (arrMul (arrMul (invArr c) (tArr p)) c)) = true := by
      rw [List.all_eq_true]
      intro c hc
      simpa using hall c hc
    rw [this] at h
    exact Bool.noConfusion h
  · exact h

private theorem burnsideK42_class_parts :
    (∀ p < T24s2.n, arrMul (tArr p) (tArr p) = idArr → tArr p ≠ idArr → tArr p ≠ z0Arr →
        quadPair z0Arr (tArr p) = true → p ∈ dzIdx ()) ∧
    (∀ xg ∈ classWit, inAutOK xg.1 = true ∧ inAutOK xg.2 = true ∧
        arrMul xg.2 z0Arr = arrMul z0Arr xg.2 ∧
        (arrConj xg.2 (classWit[0]!).1 = xg.1 ∨ arrConj xg.2 (classWit[0]!).1 = arrMul xg.1 z0Arr)) ∧
    (∀ p ∈ dzIdx (), tArr p ≠ idArr → tArr p ≠ z0Arr → ∃ xg ∈ classWit, xg.1 = tArr p) := by
  have h := (Certificates.certificate7278).2.1
  simp only [classOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_true, beq_iff_eq, decide_eq_true_eq, List.mem_filter,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := h
  refine ⟨fun p hp haa h1' h2' hq => ?_, fun xg hxg => ?_, fun p hp hp1 hp2 => h3 p ⟨hp, hp1, hp2⟩⟩
  · rcases h1 p hp with h | h
    · exfalso
      have : (arrMul (tArr p) (tArr p) == idArr && tArr p != idArr && tArr p != z0Arr &&
          quadPair z0Arr (tArr p)) = true := by
        simp [haa, h1', h2', hq]
      rw [this] at h
      exact Bool.noConfusion h
    · simpa using h
  · obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h2 xg hxg
    exact ⟨a, b, c, d⟩

end Parts

section PCoreK2
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

private theorem burnsideK42_pCore_le
    {z0K : burnsideK42_K} (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z0K} : Set burnsideK42_K)) ≤
      burnsideK42_KO0 ⊔ burnsideK42_centK (vzMasks ()) := by
  intro x hx
  obtain ⟨P, hP⟩ := burnsideK42_exists_sylowC hz0
  have hxC : x ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K) := Subgroup.map_subtype_le _ hx
  have hconj : ∀ c : ↥(Subgroup.centralizer ({z0K} : Set burnsideK42_K)),
      (c : burnsideK42_K)⁻¹ * x * c ∈ burnsideK42_Tsub := by
    intro c
    exact (hP _).1 (burnsideK42_pCore_mem_sylow_conj P ⟨x, hxC⟩ hx c)
  have hxT : x ∈ burnsideK42_Tsub := by
    have := hconj 1
    simpa using this
  obtain ⟨s, rfl⟩ := hxT
  obtain ⟨hsylc, hsyl2⟩ := burnsideK42_syl_parts
  have hsx := burnsideK42_phi24_hasArr s
  obtain ⟨k, hk, d, hd, hkd⟩ := hsyl2 s.idx s.lt (fun c hc => by
    obtain ⟨hcin, hcz⟩ := hsylc c hc
    have hcarr := burnsideK42_kOfArr_hasArr c hcin
    have hcinv := burnsideK42_kOfArr_inv_hasArr c hcin
    have hcC : burnsideK42_kOfArr c hcin ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have h1 := burnsideK42_hasArr_mul hcarr hz0
      have h2 := burnsideK42_hasArr_mul hz0 hcarr
      rw [hcz] at h1
      exact burnsideK42_hasArr_ext h1 h2
    have hy := hconj ⟨burnsideK42_kOfArr c hcin, hcC⟩
    have harr : HasArr ((((burnsideK42_kOfArr c hcin)⁻¹ * phi24 s * burnsideK42_kOfArr c hcin :
        burnsideK42_K)) : Equiv.Perm (Fin 24)) (arrMul (arrMul (invArr c) (tArr s.idx)) c) :=
      burnsideK42_hasArr_mul (burnsideK42_hasArr_mul hcinv hsx) hcarr
    exact burnsideK42_mem_elems_of_Tsub hy harr (burnsideK42_arrMul_size _ _))
  obtain ⟨pk, hpk, rfl⟩ := List.mem_map.1 hk
  obtain ⟨pd, hpd, rfl⟩ := List.mem_map.1 hd
  obtain ⟨κ, hκ, hκarr⟩ := burnsideK42_KO0_arr_conv hpk
  obtain ⟨δ, hδ, hδarr⟩ := burnsideK42_DZ_arr_conv hpd
  have : phi24 s = κ * δ :=
    Subtype.ext (burnsideK42_hasArr_ext hsx (hkd ▸ burnsideK42_hasArr_mul hκarr hδarr))
  rw [this]
  exact Subgroup.mul_mem_sup hκ hδ

private theorem burnsideK42_pCore_eq
    {z0K : burnsideK42_K} (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr)
    (hDZ : ∀ c ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K),
      ∀ γ ∈ burnsideK42_centK (vzMasks ()), c * γ * c⁻¹ ∈ burnsideK42_centK (vzMasks ())) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z0K} : Set burnsideK42_K)) =
      burnsideK42_KO0 ⊔ burnsideK42_centK (vzMasks ()) := by
  have hTC := burnsideK42_Tsub_le_cent hz0
  refine le_antisymm (burnsideK42_pCore_le hz0) (sup_le ?_ ?_)
  · refine burnsideK42_le_pCoreOf (burnsideK42_KO0_le_Tsub.trans hTC) ?_
      (burnsideK42_isPGroup_Tsub.to_le burnsideK42_KO0_le_Tsub)
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact burnsideK42_KO0_conj_mem hz0 g.2 hn
  · refine burnsideK42_le_pCoreOf (burnsideK42_DZ_le_Tsub.trans hTC) ?_
      (burnsideK42_isPGroup_Tsub.to_le burnsideK42_DZ_le_Tsub)
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hDZ g g.2 n hn

end PCoreK2

section VLevel
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

private theorem burnsideK42_e0_apply (y : Fin 24) :
    Multiplicative.toAdd burnsideK42_e0 y = if (y : ℕ) ∈ octPts then 1 else 0 := by
  simp only [burnsideK42_e0, toAdd_ofAdd, bvec_apply]
  fin_cases y <;> decide

private theorem burnsideK42_z0K_cinv_apply {z0K c : burnsideK42_K}
    (hc : c ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K)) (x : Fin 24) :
    (z0K : Equiv.Perm (Fin 24)) ((c : Equiv.Perm (Fin 24))⁻¹ x) =
      (c : Equiv.Perm (Fin 24))⁻¹ ((z0K : Equiv.Perm (Fin 24)) x) := by
  have hcz : (c : Equiv.Perm (Fin 24)) * z0K = z0K * c :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)
  have hcz' : (c : Equiv.Perm (Fin 24))⁻¹ * z0K = z0K * (c : Equiv.Perm (Fin 24))⁻¹ := by
    calc (c : Equiv.Perm (Fin 24))⁻¹ * z0K
        = (c : Equiv.Perm (Fin 24))⁻¹ * (z0K * c) * (c : Equiv.Perm (Fin 24))⁻¹ := by group
      _ = (c : Equiv.Perm (Fin 24))⁻¹ * (c * z0K) * (c : Equiv.Perm (Fin 24))⁻¹ := by rw [hcz]
      _ = z0K * (c : Equiv.Perm (Fin 24))⁻¹ := by group
  have := congrArg (fun f : Equiv.Perm (Fin 24) => f x) hcz'
  simp only [Equiv.Perm.mul_apply] at this
  exact this.symm

private theorem burnsideK42_C_le_MO0
    {z0K : burnsideK42_K} (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) :
    Subgroup.centralizer ({z0K} : Set burnsideK42_K) ≤ burnsideK42_MO0 := by
  intro c hc
  rw [burnsideK42_mem_MO0]
  apply Multiplicative.toAdd.injective
  funext x
  rw [G6.permAct_apply, burnsideK42_e0_apply, burnsideK42_e0_apply]
  have key : (((c : Equiv.Perm (Fin 24))⁻¹ x : Fin 24) : ℕ) ∈ octPts ↔ (x : ℕ) ∈ octPts := by
    rw [← burnsideK42_z0K_fix_iff hz0, ← burnsideK42_z0K_fix_iff hz0,
      burnsideK42_z0K_cinv_apply hc]
    exact (EmbeddingLike.apply_eq_iff_eq _)
  simp only [key]

end VLevel

section VLevel2
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

variable {V : Type} [CommGroup V] [Finite V] {θ : burnsideK42_K →* MulAut V} {ε : V ≃* W11}
  {V5 : Subgroup V}

private theorem burnsideK42_Vz_inv
    (hS : burnsideK42_Std θ ε V5) {z0K : burnsideK42_K}
    (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) {c : burnsideK42_K}
    (hc : c ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K)) {v : V}
    (hv : v ∈ CFSG.ASVolI.ChIJK.Vz V5 (θ z0K)) : θ c v ∈ CFSG.ASVolI.ChIJK.Vz V5 (θ z0K) := by
  simp only [CFSG.ASVolI.ChIJK.Vz, Subgroup.mem_inf, mem_fixV_zpowers_iff_apply] at hv ⊢
  refine ⟨hS.inv c (burnsideK42_C_le_MO0 hz0 hc) v hv.1, ?_⟩
  have hcz : z0K * c = c * z0K := (Subgroup.mem_centralizer_singleton_iff.1 hc).symm
  calc θ z0K (θ c v) = θ (z0K * c) v := by rw [map_mul]; rfl
    _ = θ (c * z0K) v := by rw [hcz]
    _ = θ c (θ z0K v) := by rw [map_mul]; rfl
    _ = θ c v := by rw [hv.2]

private theorem burnsideK42_mem_centK_iff_V
    (hS : burnsideK42_Std θ ε V5) {z0K : burnsideK42_K}
    (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) {γ : burnsideK42_K} :
    γ ∈ burnsideK42_centK (vzMasks ()) ↔ ∀ v ∈ CFSG.ASVolI.ChIJK.Vz V5 (θ z0K), θ γ v = v := by
  constructor
  · intro hγ v hv
    obtain ⟨m, hm, rfl⟩ := (MaskCoords.ofEquiv ε).vm_surj v
    have hmv := (burnsideK42_Vz_mask hS hz0 m hm).1 hv
    have := (burnsideK42_centK_iff_arr (fun m hm => burnsideK42_vz_lt m hm)
      (burnsideK42_hasArr_permArr _)).1 hγ m hmv
    rw [burnsideK42_theta_vm hS.hε (burnsideK42_hasArr_permArr _), this]
  · intro h
    rw [burnsideK42_centK_iff_arr (fun m hm => burnsideK42_vz_lt m hm)
      (burnsideK42_hasArr_permArr _)]
    intro m hm
    have hm' := burnsideK42_vz_lt m hm
    have := h _ ((burnsideK42_Vz_mask hS hz0 m hm').2 hm)
    rw [burnsideK42_theta_vm hS.hε (burnsideK42_hasArr_permArr _),
      burnsideK42_vm_eq_iff _ (actC11_lt _ _) hm'] at this
    exact this

private theorem burnsideK42_DZ_conj_mem
    (hS : burnsideK42_Std θ ε V5) {z0K : burnsideK42_K}
    (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) {c : burnsideK42_K}
    (hc : c ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K)) {γ : burnsideK42_K}
    (hγ : γ ∈ burnsideK42_centK (vzMasks ())) : c * γ * c⁻¹ ∈ burnsideK42_centK (vzMasks ()) := by
  rw [burnsideK42_mem_centK_iff_V hS hz0] at hγ ⊢
  intro v hv
  have hc' : c⁻¹ ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K) := Subgroup.inv_mem _ hc
  have h1 := burnsideK42_Vz_inv hS hz0 hc' hv
  have h2 := hγ _ h1
  calc θ (c * γ * c⁻¹) v = θ c (θ γ (θ c⁻¹ v)) := by rw [map_mul, map_mul]; rfl
    _ = θ c (θ c⁻¹ v) := by rw [h2]
    _ = v := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl

private theorem burnsideK42_conj1a
    (hS : burnsideK42_Std θ ε V5) {z0K : burnsideK42_K}
    (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) :
    CFSG.Open.pCoreOf 2 (θ.range ⊓ Subgroup.centralizer ({θ z0K} : Set (MulAut V))) =
      burnsideK42_KO0.map θ ⊔ CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K) := by
  have hinj : Function.Injective θ := burnsideK42_theta_inj hS.hε
  have h1 : θ.range ⊓ Subgroup.centralizer ({θ z0K} : Set (MulAut V)) =
      (Subgroup.centralizer ({z0K} : Set burnsideK42_K)).map θ := by
    ext g
    constructor
    · rintro ⟨⟨γ, rfl⟩, hg⟩
      have hg' : θ γ ∈ Subgroup.centralizer ({θ z0K} : Set (MulAut V)) := hg
      refine ⟨γ, ?_, rfl⟩
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 hg'
      show γ ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hinj (by rw [map_mul, map_mul]; exact h2)
    · rintro ⟨γ, hγ, rfl⟩
      refine ⟨⟨γ, rfl⟩, ?_⟩
      show θ γ ∈ Subgroup.centralizer ({θ z0K} : Set (MulAut V))
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.1 hγ]
  rw [h1, burnsideK42_pCoreOf_map θ hinj, burnsideK42_pCore_eq hz0
    (fun c hc γ hγ => burnsideK42_DZ_conj_mem hS hz0 hc hγ), Subgroup.map_sup,
    burnsideK42_Dz_eq hS hz0]

end VLevel2

section SubgroupAlg

@[expose] def burnsideK42_cj {G : Type*} [Group G] (g : G) (S : Subgroup G) : Subgroup G :=
  S.map (MulAut.conj g).toMonoidHom

private theorem burnsideK42_mem_cj {G : Type*} [Group G] (g : G) (S : Subgroup G) {x : G} :
    x ∈ burnsideK42_cj g S ↔ g⁻¹ * x * g ∈ S := by
  unfold burnsideK42_cj
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem burnsideK42_cj_cj {G : Type*} [Group G] (g h : G) (S : Subgroup G) :
    burnsideK42_cj h (burnsideK42_cj g S) = burnsideK42_cj (h * g) S := by
  ext x
  rw [burnsideK42_mem_cj, burnsideK42_mem_cj, burnsideK42_mem_cj]
  have : g⁻¹ * (h⁻¹ * x * h) * g = (h * g)⁻¹ * x * (h * g) := by group
  rw [this]

private theorem burnsideK42_cj_one {G : Type*} [Group G] (S : Subgroup G) : burnsideK42_cj 1 S
    = S := by
  ext x
  rw [burnsideK42_mem_cj]
  simp

private theorem burnsideK42_cj_sup {G : Type*} [Group G] (g : G) (S T : Subgroup G) :
    burnsideK42_cj g (S ⊔ T) = burnsideK42_cj g S ⊔ burnsideK42_cj g T :=
  Subgroup.map_sup _ _ _

private theorem burnsideK42_cj_zpowers {G : Type*} [Group G] (g a : G) :
    burnsideK42_cj g (Subgroup.zpowers a) = Subgroup.zpowers (g * a * g⁻¹) := by
  unfold burnsideK42_cj
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

private theorem burnsideK42_sup_mul_right {G : Type*} [Group G] {a z : G} (hz : z * z = 1) :
    Subgroup.zpowers (a * z) ⊔ Subgroup.zpowers z = Subgroup.zpowers a ⊔ Subgroup.zpowers z := by
  apply le_antisymm
  · refine sup_le (Subgroup.zpowers_le.2 (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))) le_sup_right
  · refine sup_le (Subgroup.zpowers_le.2 ?_) le_sup_right
    have h1 : a * z ∈ Subgroup.zpowers (a * z) ⊔ Subgroup.zpowers z :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have h2 : z ∈ Subgroup.zpowers (a * z) ⊔ Subgroup.zpowers z :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have := Subgroup.mul_mem _ h1 h2
    rwa [mul_assoc, hz, mul_one] at this

end SubgroupAlg

section QuadW
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

@[expose] def burnsideK42_QuadW (a b : burnsideK42_K) : Prop :=
  ∀ u : W11, burnsideK42_rho a (burnsideK42_rho b u * u) = burnsideK42_rho b u * u

private theorem burnsideK42_quadW_conj {a b c : burnsideK42_K} (hq : burnsideK42_QuadW a b)
    (hac : c * a = a * c) : burnsideK42_QuadW a (c * b * c⁻¹) := by
  intro u
  obtain ⟨v, hv⟩ : ∃ v, burnsideK42_rho c⁻¹ u = v := ⟨_, rfl⟩
  have hu : burnsideK42_rho c v = u := by
    rw [← hv, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have h1 : burnsideK42_rho (c * b * c⁻¹) u = burnsideK42_rho c (burnsideK42_rho b v) := by
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hv]
  obtain ⟨w, hw⟩ : ∃ w, w = burnsideK42_rho b v * v := ⟨_, rfl⟩
  have h2 : burnsideK42_rho (c * b * c⁻¹) u * u = burnsideK42_rho c w := by
    rw [h1, hw, map_mul, hu]
  have h3 : burnsideK42_rho a w = w := by rw [hw]; exact hq v
  rw [h2]
  calc burnsideK42_rho a (burnsideK42_rho c w) = (burnsideK42_rho a * burnsideK42_rho c) w := rfl
    _ = burnsideK42_rho (a * c) w := by rw [← map_mul]
    _ = burnsideK42_rho (c * a) w := by rw [hac]
    _ = (burnsideK42_rho c * burnsideK42_rho a) w := by rw [map_mul]
    _ = burnsideK42_rho c (burnsideK42_rho a w) := rfl
    _ = burnsideK42_rho c w := by rw [h3]

private theorem burnsideK42_quadW_of_mask {a b : burnsideK42_K} {aa ab : Array ℕ}
    (haa : HasArr (a : Equiv.Perm (Fin 24)) aa) (hab : HasArr (b : Equiv.Perm (Fin 24)) ab)
    (h : ∀ m < 2048, actC11 aa (actC11 ab m ^^^ m) = actC11 ab m ^^^ m) :
    burnsideK42_QuadW a b := by
  intro u
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 u
  rw [burnsideK42_rho_toW b hab, ← toW_xor, burnsideK42_rho_toW a haa, h m hm]

private theorem burnsideK42_mask_of_quadW {a b : burnsideK42_K} {aa ab : Array ℕ}
    (haa : HasArr (a : Equiv.Perm (Fin 24)) aa) (hab : HasArr (b : Equiv.Perm (Fin 24)) ab)
    (hq : burnsideK42_QuadW a b) :
    ∀ m < 2048, actC11 aa (actC11 ab m ^^^ m) = actC11 ab m ^^^ m := by
  intro m hm
  have h := hq (toW 11 m)
  rw [burnsideK42_rho_toW b hab, ← toW_xor, burnsideK42_rho_toW a haa] at h
  exact toW_inj (actC11_lt _ _) (Nat.xor_lt_two_pow (actC11_lt _ _) hm) h

end QuadW

section FourK
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

private theorem burnsideK42_idArr_size : idArr.size = 24 := by simp [idArr]

private theorem burnsideK42_classWit_zero_mem : (classWit[0]!) ∈ classWit := by
  have h : 0 < classWit.length := by decide
  rw [getElem!_pos classWit 0 h]
  exact List.getElem_mem h

private theorem burnsideK42_class_conj
    {z0K : burnsideK42_K}
    (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) :
    ∃ x0K : burnsideK42_K, ∀ w : burnsideK42_K, ∀ p ∈ dzIdx (),
      HasArr (w : Equiv.Perm (Fin 24)) (tArr p) → w ≠ 1 → w ≠ z0K →
      ∃ g ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K),
        burnsideK42_cj g (Subgroup.zpowers x0K ⊔ Subgroup.zpowers z0K) =
          Subgroup.zpowers w ⊔ Subgroup.zpowers z0K := by
  obtain ⟨-, hc2, hc3⟩ := burnsideK42_class_parts
  have h0 := (hc2 _ burnsideK42_classWit_zero_mem).1
  refine ⟨burnsideK42_kOfArr (classWit[0]!).1 h0, fun w p hp hwarr hw1 hwz => ?_⟩
  have hne : tArr p ≠ idArr := by
    intro h
    rw [h] at hwarr
    exact hw1 (Subtype.ext (burnsideK42_hasArr_ext hwarr burnsideK42_hasArr_one))
  have hnz : tArr p ≠ z0Arr := by
    intro h
    rw [h] at hwarr
    exact hwz (Subtype.ext (burnsideK42_hasArr_ext hwarr hz0))
  obtain ⟨xg, hxg, hxg1⟩ := hc3 p hp hne hnz
  obtain ⟨-, hin2, hcomm, hconj⟩ := hc2 xg hxg
  have hgarr := burnsideK42_kOfArr_hasArr xg.2 hin2
  have hginv := burnsideK42_kOfArr_inv_hasArr xg.2 hin2
  have hx0arr := burnsideK42_kOfArr_hasArr (classWit[0]!).1 h0
  have hgC : burnsideK42_kOfArr xg.2 hin2 ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have h1 := burnsideK42_hasArr_mul hgarr hz0
    have h2 := burnsideK42_hasArr_mul hz0 hgarr
    rw [hcomm] at h1
    exact burnsideK42_hasArr_ext h1 h2
  refine ⟨burnsideK42_kOfArr xg.2 hin2, hgC, ?_⟩
  have hconjarr := burnsideK42_hasArr_conj hx0arr hgarr hginv
  have hgc : Commute (burnsideK42_kOfArr xg.2 hin2) z0K := Subgroup.mem_centralizer_singleton_iff.1 hgC
  have hzc : burnsideK42_kOfArr xg.2 hin2 * z0K * (burnsideK42_kOfArr xg.2 hin2)⁻¹ = z0K := by
    rw [hgc.eq, mul_inv_cancel_right]
  rw [burnsideK42_cj_sup, burnsideK42_cj_zpowers, burnsideK42_cj_zpowers, hzc]
  rcases hconj with h | h
  · rw [h, hxg1] at hconjarr
    have : burnsideK42_kOfArr xg.2 hin2 * burnsideK42_kOfArr (classWit[0]!).1 h0 *
        (burnsideK42_kOfArr xg.2 hin2)⁻¹ = w := Subtype.ext (burnsideK42_hasArr_ext hconjarr hwarr)
    rw [this]
  · rw [h, hxg1] at hconjarr
    have hwz : HasArr ((w * z0K : burnsideK42_K) : Equiv.Perm (Fin 24)) (arrMul (tArr p) z0Arr) :=
      burnsideK42_hasArr_mul hwarr hz0
    have : burnsideK42_kOfArr xg.2 hin2 * burnsideK42_kOfArr (classWit[0]!).1 h0 *
        (burnsideK42_kOfArr xg.2 hin2)⁻¹ = w * z0K :=
      Subtype.ext (burnsideK42_hasArr_ext hconjarr hwz)
    rw [this]
    exact burnsideK42_sup_mul_right (burnsideK42_z0K_sq hz0)

private theorem burnsideK42_four_conj
    {z0K : burnsideK42_K} (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr)
    {x : burnsideK42_K} (hxx : x * x = 1) (hx1 : x ≠ 1) (hxz : x ≠ z0K)
    (hxc : x * z0K = z0K * x) (hq : burnsideK42_QuadW z0K x)
    {y : burnsideK42_K} (hy : y ∈ burnsideK42_centK (vzMasks ())) (hy1 : y ≠ 1) (hyz : y ≠ z0K) :
    ∃ g ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K),
      burnsideK42_cj g (Subgroup.zpowers x ⊔ Subgroup.zpowers z0K) =
        Subgroup.zpowers y ⊔ Subgroup.zpowers z0K := by
  obtain ⟨x0K, hx0⟩ := burnsideK42_class_conj hz0
  obtain ⟨py, hpy, hyarr⟩ := burnsideK42_DZ_arr hy
  obtain ⟨gy, hgyC, hgy⟩ := hx0 y py hpy hyarr hy1 hyz
  have hxC : x ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxc
  obtain ⟨P, hP⟩ := burnsideK42_exists_sylowC hz0
  obtain ⟨g1, hg1⟩ := burnsideK42_exists_conj_sylow P ⟨x, hxC⟩ (Subtype.ext hxx)
  have hcC : (g1 : burnsideK42_K) ∈ Subgroup.centralizer ({z0K} : Set burnsideK42_K) := g1.2
  have hσT : (g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹ ∈ burnsideK42_Tsub :=
    (hP _).1 hg1
  obtain ⟨s, hs⟩ := hσT
  have hσarr : HasArr (((g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹ : burnsideK42_K) :
      Equiv.Perm (Fin 24)) (tArr s.idx) := by
    rw [← hs]
    exact burnsideK42_phi24_hasArr s
  have hcc : Commute (g1 : burnsideK42_K) z0K := Subgroup.mem_centralizer_singleton_iff.1 hcC
  have hxcomm : Commute x z0K := hxc
  have hσcomm : Commute ((g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹) z0K :=
    (hcc.mul_left hxcomm).mul_left hcc.inv_left
  have hσσ : ((g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹) *
      ((g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹) = 1 := by
    calc ((g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹) *
        ((g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹)
        = (g1 : burnsideK42_K) * (x * x) * (g1 : burnsideK42_K)⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  have hσ1 : (g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have : x = (g1 : burnsideK42_K)⁻¹ * ((g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹) *
        (g1 : burnsideK42_K) := by group
    rw [this, h]
    group
  have hσz : (g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹ ≠ z0K := by
    intro h
    apply hxz
    have : x = (g1 : burnsideK42_K)⁻¹ * ((g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹) *
        (g1 : burnsideK42_K) := by group
    rw [this, h]
    calc (g1 : burnsideK42_K)⁻¹ * z0K * (g1 : burnsideK42_K)
        = (g1 : burnsideK42_K)⁻¹ * (z0K * (g1 : burnsideK42_K)) := by group
      _ = (g1 : burnsideK42_K)⁻¹ * ((g1 : burnsideK42_K) * z0K) := by rw [hcc.eq]
      _ = z0K := by group
  have hσq : burnsideK42_QuadW z0K ((g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹) :=
    burnsideK42_quadW_conj hq hcc.eq
  have haa : arrMul (tArr s.idx) (tArr s.idx) = idArr := by
    have h1 : HasArr ((((g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹) *
        ((g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹) : burnsideK42_K) :
        Equiv.Perm (Fin 24)) (arrMul (tArr s.idx) (tArr s.idx)) :=
      burnsideK42_hasArr_mul hσarr hσarr
    rw [hσσ] at h1
    exact burnsideK42_arr_eq h1 burnsideK42_hasArr_one (burnsideK42_arrMul_size _ _)
      burnsideK42_idArr_size
  have hane : tArr s.idx ≠ idArr := by
    intro h
    rw [h] at hσarr
    exact hσ1 (Subtype.ext (burnsideK42_hasArr_ext hσarr burnsideK42_hasArr_one))
  have hanz : tArr s.idx ≠ z0Arr := by
    intro h
    rw [h] at hσarr
    exact hσz (Subtype.ext (burnsideK42_hasArr_ext hσarr hz0))
  have hquad : quadPair z0Arr (tArr s.idx) = true := by
    have := burnsideK42_mask_of_quadW hz0 hσarr hσq
    simp only [quadPair, List.all_eq_true, List.mem_range, beq_iff_eq]
    exact this
  have hpσ : s.idx ∈ dzIdx () :=
    (burnsideK42_class_parts).1 s.idx s.lt haa hane hanz hquad
  obtain ⟨gσ, hgσC, hgσ⟩ := hx0 _ s.idx hpσ hσarr hσ1 hσz
  refine ⟨gy * (gσ⁻¹ * (g1 : burnsideK42_K)), ?_, ?_⟩
  · exact Subgroup.mul_mem _ hgyC (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgσC) hcC)
  · have hzc : (g1 : burnsideK42_K) * z0K * (g1 : burnsideK42_K)⁻¹ = z0K := by
      rw [hcc.eq, mul_inv_cancel_right]
    have hA : burnsideK42_cj (g1 : burnsideK42_K) (Subgroup.zpowers x ⊔ Subgroup.zpowers z0K) =
        Subgroup.zpowers ((g1 : burnsideK42_K) * x * (g1 : burnsideK42_K)⁻¹) ⊔
          Subgroup.zpowers z0K := by
      rw [burnsideK42_cj_sup, burnsideK42_cj_zpowers, burnsideK42_cj_zpowers, hzc]
    calc burnsideK42_cj (gy * (gσ⁻¹ * (g1 : burnsideK42_K)))
          (Subgroup.zpowers x ⊔ Subgroup.zpowers z0K)
        = burnsideK42_cj gy (burnsideK42_cj gσ⁻¹ (burnsideK42_cj (g1 : burnsideK42_K)
          (Subgroup.zpowers x ⊔ Subgroup.zpowers z0K))) := by
          rw [burnsideK42_cj_cj, burnsideK42_cj_cj, mul_assoc]
      _ = burnsideK42_cj gy (burnsideK42_cj gσ⁻¹ (burnsideK42_cj gσ
          (Subgroup.zpowers x0K ⊔ Subgroup.zpowers z0K))) := by rw [hA, hgσ]
      _ = burnsideK42_cj gy (Subgroup.zpowers x0K ⊔ Subgroup.zpowers z0K) := by
          rw [burnsideK42_cj_cj gσ gσ⁻¹, inv_mul_cancel, burnsideK42_cj_one]
      _ = Subgroup.zpowers y ⊔ Subgroup.zpowers z0K := hgy

end FourK

section Conj4
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

private theorem burnsideK42_cj_map {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G)
    (S : Subgroup G) : (burnsideK42_cj g S).map f = burnsideK42_cj (f g) (S.map f) := by
  unfold burnsideK42_cj
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

variable {V : Type} [CommGroup V] [Finite V] {θ : burnsideK42_K →* MulAut V} {ε : V ≃* W11}
  {V5 : Subgroup V}

private theorem burnsideK42_conj4
    (hS : burnsideK42_Std θ ε V5) (hV2 : ∀ v : V, v ^ 2 = 1) (hM : MathieuCode24 θ.range ⊤ ⊥)
    {z0K : burnsideK42_K} (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) {d : MulAut V}
    (hd : d ∈ CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K)) (hdz : d ∉ Subgroup.zpowers (θ z0K))
    {D : Subgroup (MulAut V)} (hDM : D ≤ θ.range) (hDe : IsElemAbelian2 D) (hDc : ¬ IsCyclic ↥D)
    (hzD : θ z0K ∈ D) (hDq : IsQuadratic D ∨ IsQuadratic (dualSub D)) :
    ∃ g ∈ burnsideK42_MO0.map θ,
      D = burnsideK42_cj g (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K)) := by
  have hinj : Function.Injective θ := burnsideK42_theta_inj hS.hε
  have hDq' : IsQuadratic D := hDq.elim id (fun h => (isQuadratic_dualSub_iff hV2 D).2 h)
  have hrk : rk ↥D ≤ 2 := burnsideK42_rk_le_two (Or.inl hM) hDM hDe hDq'
  have hcard : Nat.card ↥D ≤ 4 := by
    rw [CFSG.Quasithin.B45Mat.card_eq_two_pow_rk hDe]
    calc 2 ^ rk ↥D ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hrk
      _ = 4 := by norm_num
  obtain ⟨xD, hxD, hxDz⟩ : ∃ xD ∈ D, xD ∉ Subgroup.zpowers (θ z0K) := by
    by_contra hne
    push Not at hne
    apply hDc
    have : D = Subgroup.zpowers (θ z0K) := le_antisymm hne (Subgroup.zpowers_le.2 hzD)
    rw [this]
    infer_instance
  obtain ⟨x, rfl⟩ := hDM hxD
  have hz2 : θ z0K * θ z0K = 1 := by rw [← map_mul, burnsideK42_z0K_sq hz0, map_one]
  have hxx : x * x = 1 := by
    apply hinj
    rw [map_mul, map_one]
    have := hDe.2 _ hxD
    rwa [sq] at this
  have hx1' : θ x ≠ 1 := by
    intro h
    apply hxDz
    rw [h]
    exact Subgroup.one_mem _
  have hx1 : x ≠ 1 := fun h => hx1' (by rw [h, map_one])
  have hxz' : θ x ≠ θ z0K := by
    intro h
    apply hxDz
    rw [h]
    exact Subgroup.mem_zpowers _
  have hxz : x ≠ z0K := fun h => hxz' (by rw [h])
  have hxc : x * z0K = z0K * x := by
    apply hinj
    rw [map_mul, map_mul]
    exact hDe.1 _ hxD _ hzD
  have hmask : ∀ m < 2048, actC11 z0Arr (actC11 (burnsideK42_permArr (x : Equiv.Perm (Fin 24))) m ^^^ m) =
      actC11 (burnsideK42_permArr (x : Equiv.Perm (Fin 24))) m ^^^ m := by
    intro m hm
    have hmem : θ x ((MaskCoords.ofEquiv ε).vm m) * ((MaskCoords.ofEquiv ε).vm m)⁻¹ ∈ commV D :=
      Subgroup.subset_closure ⟨θ x, hxD, _, rfl⟩
    have h1 := (mem_fixV.1 ((show commV D ≤ fixV D from hDq') hmem)) (θ z0K) hzD
    rw [burnsideK42_comm_gen hS x m, burnsideK42_theta_vm hS.hε hz0,
      burnsideK42_vm_eq_iff _ (actC11_lt _ _) (Nat.xor_lt_two_pow (actC11_lt _ _) hm)] at h1
    exact h1
  have hq : burnsideK42_QuadW z0K x :=
    burnsideK42_quadW_of_mask hz0 (burnsideK42_hasArr_permArr _) hmask
  obtain ⟨y, hy, rfl⟩ := (burnsideK42_mem_Dz_iff hS hz0 d).1 hd
  have hy1 : y ≠ 1 := by
    intro h
    apply hdz
    rw [h, map_one]
    exact Subgroup.one_mem _
  have hyz : y ≠ z0K := by
    intro h
    apply hdz
    rw [h]
    exact Subgroup.mem_zpowers _
  obtain ⟨g, hgC, hg⟩ := burnsideK42_four_conj hz0 hxx hx1 hxz hxc hq hy hy1 hyz
  have hDeq : Subgroup.zpowers (θ x) ⊔ Subgroup.zpowers (θ z0K) = D := by
    have hle : Subgroup.zpowers (θ x) ⊔ Subgroup.zpowers (θ z0K) ≤ D :=
      sup_le (Subgroup.zpowers_le.2 hxD) (Subgroup.zpowers_le.2 hzD)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hz1 : θ z0K ≠ 1 := fun h => burnsideK42_z0K_ne hz0 (hinj (by rw [h, map_one]))
    have hxzz : θ x * θ z0K ≠ 1 := by
      intro h
      apply hxDz
      have : θ x = θ z0K := by
        have := mul_eq_one_iff_eq_inv.1 h
        rw [this]
        exact (inv_eq_of_mul_eq_one_right hz2).symm ▸ rfl
      rw [this]
      exact Subgroup.mem_zpowers _
    have hxzz2 : θ x * θ z0K ≠ θ z0K := by
      intro h
      exact hx1' (mul_eq_right.1 h)
    have hxzz3 : θ x * θ z0K ≠ θ x := by
      intro h
      exact hz1 (mul_eq_left.1 h)
    have hnd : [1, θ z0K, θ x, θ x * θ z0K].Nodup := by
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_,
        List.nodup_singleton _⟩⟩⟩
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
        exact ⟨hz1.symm, hx1'.symm, hxzz.symm⟩
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
        exact ⟨hxz'.symm, hxzz2.symm⟩
      · simp only [List.mem_singleton]
        exact hxzz3.symm
    have hl : ∀ w ∈ [1, θ z0K, θ x, θ x * θ z0K],
        w ∈ Subgroup.zpowers (θ x) ⊔ Subgroup.zpowers (θ z0K) := by
      intro w hw
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have := burnsideK42_length_le_card _ _ hnd hl
    simpa using le_trans hcard this
  refine ⟨θ g⁻¹, Subgroup.mem_map_of_mem θ (burnsideK42_C_le_MO0 hz0 (Subgroup.inv_mem _ hgC)),
    ?_⟩
  have h1 : (Subgroup.zpowers x ⊔ Subgroup.zpowers z0K).map θ =
      Subgroup.zpowers (θ x) ⊔ Subgroup.zpowers (θ z0K) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  have h2 : (Subgroup.zpowers y ⊔ Subgroup.zpowers z0K).map θ =
      Subgroup.zpowers (θ y) ⊔ Subgroup.zpowers (θ z0K) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  have hE : burnsideK42_cj (θ g) D = Subgroup.zpowers (θ y) ⊔ Subgroup.zpowers (θ z0K) := by
    rw [← hDeq, ← h1, ← burnsideK42_cj_map, hg, h2]
  calc D = burnsideK42_cj (θ g)⁻¹ (burnsideK42_cj (θ g) D) := by
        rw [burnsideK42_cj_cj, inv_mul_cancel, burnsideK42_cj_one]
    _ = burnsideK42_cj (θ g)⁻¹ (Subgroup.zpowers (θ y) ⊔ Subgroup.zpowers (θ z0K)) := by rw [hE]
    _ = burnsideK42_cj (θ g⁻¹) (Subgroup.zpowers (θ y) ⊔ Subgroup.zpowers (θ z0K)) := by
        rw [map_inv]

end Conj4

section StdMain
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

variable {V : Type} [CommGroup V] [Finite V] {θ : burnsideK42_K →* MulAut V} {ε : V ≃* W11}
  {V5 : Subgroup V}

private theorem burnsideK42_std_main
    (hS : burnsideK42_Std θ ε V5) (hV2 : ∀ v : V, v ^ 2 = 1) (hM : MathieuCode24 θ.range ⊤ ⊥)
    {z0K : burnsideK42_K} (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr) {d : MulAut V}
    (hd : d ∈ CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K)) (hdz : d ∉ Subgroup.zpowers (θ z0K)) :
    (CFSG.Open.pCoreOf 2 (θ.range ⊓ Subgroup.centralizer ({θ z0K} : Set (MulAut V))) =
        burnsideK42_KO0.map θ ⊔ CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K) ∧
      CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K) ⊓ burnsideK42_KO0.map θ =
        Subgroup.zpowers (θ z0K) ∧
      rk ↥(CFSG.ASVolI.ChIJK.Vz V5 (θ z0K)) = 4 ∧
      IsE2 4 ↥(CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K))) ∧
    (commV (Subgroup.zpowers (θ z0K)) = CFSG.ASVolI.ChIJK.Vz V5 (θ z0K) ∧
      rk ↥(commV (Subgroup.zpowers (θ z0K))) = 4) ∧
    (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K) =
      CFSG.ASVolI.ChIJK.Dz θ.range V5 (θ z0K) ⊓ CFSG.ASVolI.ChIJK.Dd θ.range d) ∧
    (∀ D : Subgroup (MulAut V), D ≤ θ.range → IsElemAbelian2 D → ¬ IsCyclic ↥D →
      θ z0K ∈ D → (IsQuadratic D ∨ IsQuadratic (dualSub D)) →
      ∃ g ∈ burnsideK42_MO0.map θ,
        D = (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K)).map (MulAut.conj g).toMonoidHom) ∧
    (fixV (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K)) =
        commV (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K)) ∧
      commV (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K)) =
        CFSG.ASVolI.ChIJK.Vz V5 (θ z0K) ⊔ commV (Subgroup.zpowers d) ∧
      rk ↥(fixV (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K))) = 6) ∧
    rkIdx (fixV (dualSub (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K)))) = 6 := by
  have h5 := burnsideK42_conj5 hS hz0 hd hdz
  refine ⟨⟨burnsideK42_conj1a hS hz0, burnsideK42_Dz_inf_KO hS hz0, burnsideK42_rk_Vz hS hz0,
    burnsideK42_isE2_Dz hS hz0⟩, ⟨burnsideK42_commV_z hS hz0, ?_⟩,
    burnsideK42_conj3 hS hz0 hd hdz, fun D hDM hDe hDc hzD hDq => ?_, h5, ?_⟩
  · rw [burnsideK42_commV_z hS hz0]
    exact burnsideK42_rk_Vz hS hz0
  · exact burnsideK42_conj4 hS hV2 hM hz0 hd hdz hDM hDe hDc hzD hDq
  · have h6 : rkIdx (fixV (dualSub (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K)))) =
        rk ↥(commV (Subgroup.zpowers d ⊔ Subgroup.zpowers (θ z0K))) := by
      unfold rkIdx rk
      rw [index_fixV_dualSub hV2]
    rw [h6, ← h5.1]
    exact h5.2.2

end StdMain

section Remark
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

private theorem burnsideK42_octadPts_perm {κ : burnsideK42_K} {e : G6.PermMod 24}
    (hκ : G6.permAct 24 (κ : Equiv.Perm (Fin 24)) burnsideK42_e0 = e) (y : Fin 24) :
    y ∈ CFSG.ASVolI.ChIJK.octadPts e ↔
      (κ : Equiv.Perm (Fin 24))⁻¹ y ∈ CFSG.ASVolI.ChIJK.octadPts burnsideK42_e0 := by
  show Multiplicative.toAdd e y = 1 ↔
    Multiplicative.toAdd burnsideK42_e0 ((κ : Equiv.Perm (Fin 24))⁻¹ y) = 1
  rw [← hκ, G6.permAct_apply]

private theorem burnsideK42_mem_KOgen (e : G6.PermMod 24) (γ : burnsideK42_K) :
    γ ∈ (fixingSubgroup (Equiv.Perm (Fin 24)) (CFSG.ASVolI.ChIJK.octadPts e)).subgroupOf
        CFSG.Monster.Code.AutPerm ↔
      ∀ y ∈ CFSG.ASVolI.ChIJK.octadPts e, (γ : Equiv.Perm (Fin 24)) y = y := by
  simp only [Subgroup.mem_subgroupOf, mem_fixingSubgroup_iff, Equiv.Perm.smul_def]

private theorem burnsideK42_cj_KO0 {κ : burnsideK42_K} {e : G6.PermMod 24}
    (hκ : G6.permAct 24 (κ : Equiv.Perm (Fin 24)) burnsideK42_e0 = e) :
    burnsideK42_cj κ burnsideK42_KO0 =
      (fixingSubgroup (Equiv.Perm (Fin 24)) (CFSG.ASVolI.ChIJK.octadPts e)).subgroupOf
        CFSG.Monster.Code.AutPerm := by
  ext x
  rw [burnsideK42_mem_cj, burnsideK42_KO0, burnsideK42_mem_KOgen, burnsideK42_mem_KOgen]
  constructor
  · intro h y hy
    have h1 := h _ ((burnsideK42_octadPts_perm hκ y).1 hy)
    have hk : (κ : Equiv.Perm (Fin 24)) ((κ : Equiv.Perm (Fin 24))⁻¹ y) = y := by simp
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hk] at h1
    exact ((κ : Equiv.Perm (Fin 24))⁻¹).injective h1
  · intro h u hu
    have hu' : (κ : Equiv.Perm (Fin 24)) u ∈ CFSG.ASVolI.ChIJK.octadPts e := by
      rw [burnsideK42_octadPts_perm hκ]
      simpa using hu
    have h1 := h _ hu'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    rw [h1]
    simp

private theorem burnsideK42_cj_MO0 {κ : burnsideK42_K} {e : G6.PermMod 24}
    (hκ : G6.permAct 24 (κ : Equiv.Perm (Fin 24)) burnsideK42_e0 = e) :
    burnsideK42_cj κ burnsideK42_MO0 =
      (m24Fix e).subgroupOf CFSG.Monster.Code.AutPerm := by
  ext x
  rw [burnsideK42_mem_cj, burnsideK42_mem_MO0, Subgroup.mem_subgroupOf]
  change _ ↔ (x : Equiv.Perm (Fin 24)) ∈ CFSG.Monster.Code.AutPerm ∧
    G6.permAct 24 (x : Equiv.Perm (Fin 24)) e = e
  rw [← hκ]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have h1 : G6.permAct 24 ((x : Equiv.Perm (Fin 24)) * κ) burnsideK42_e0 =
        G6.permAct 24 (κ : Equiv.Perm (Fin 24)) burnsideK42_e0 := by
      have : (x : Equiv.Perm (Fin 24)) * κ =
          (κ : Equiv.Perm (Fin 24)) * (((κ⁻¹ * x * κ : burnsideK42_K)) : Equiv.Perm (Fin 24)) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this, map_mul, MulAut.mul_apply, h]
    rw [map_mul, MulAut.mul_apply] at h1
    exact h1
  · rintro ⟨-, h⟩
    have h1 : G6.permAct 24 (((κ⁻¹ * x * κ : burnsideK42_K)) : Equiv.Perm (Fin 24)) burnsideK42_e0 =
        G6.permAct 24 (κ : Equiv.Perm (Fin 24))⁻¹
          (G6.permAct 24 (x : Equiv.Perm (Fin 24)) (G6.permAct 24 (κ : Equiv.Perm (Fin 24))
            burnsideK42_e0)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, MulAut.mul_apply]
    rw [h1, h]
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

end Remark

end BurnsideK42

section

theorem as_K_4_2_lemma : K_4_2_lemma := by
  intro V _ _ _ M hM _ _ _ _ _ D hDM hDe _ hDq _
  have := burnsideK42_rk_le_two hM hDM hDe hDq
  exact this

end

@[expose] def K_4_3_lemma : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (M : Subgroup (MulAut V))
    (π : ↥CFSG.Monster.Code.AutPerm →* ↥M) (e : G6.PermMod 24) (V5 : Subgroup V) (z : MulAut V),
    M24Setup V M π e V5 z →
    ∀ d ∈ Dz M V5 z, d ∉ Subgroup.zpowers z →
      (pCoreOf 2 (M ⊓ Subgroup.centralizer ({z} : Set (MulAut V))) = KO π e ⊔ Dz M V5 z ∧
        Dz M V5 z ⊓ KO π e = Subgroup.zpowers z ∧ rk ↥(Vz V5 z) = 4 ∧ IsE2 4 ↥(Dz M V5 z)) ∧
      (commV (Subgroup.zpowers z) = Vz V5 z ∧ rk ↥(commV (Subgroup.zpowers z)) = 4) ∧
      (Subgroup.zpowers d ⊔ Subgroup.zpowers z = Dz M V5 z ⊓ Dd M d) ∧
      (∀ D : Subgroup (MulAut V), D ≤ M → IsElemAbelian2 D → ¬ IsCyclic ↥D → z ∈ D →
        (IsQuadratic D ∨ IsQuadratic (dualSub D)) →
        ∃ g ∈ MO π e, D = (Subgroup.zpowers d ⊔ Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom) ∧
      (fixV (Subgroup.zpowers d ⊔ Subgroup.zpowers z) =
          commV (Subgroup.zpowers d ⊔ Subgroup.zpowers z) ∧
        commV (Subgroup.zpowers d ⊔ Subgroup.zpowers z) =
          Vz V5 z ⊔ commV (Subgroup.zpowers d) ∧
        rk ↥(fixV (Subgroup.zpowers d ⊔ Subgroup.zpowers z)) = 6) ∧
      rkIdx (fixV (dualSub (Subgroup.zpowers d ⊔ Subgroup.zpowers z))) = 6

section

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data CFSG.ASVolI.ChIJK in
theorem as_K_4_3_lemma : K_4_3_lemma := by
  intro V _ _ M π e V5 z hS d hd hdz
  have hV2 := hS.elem2
  have hM : MathieuCode24 M ⊤ ⊥ := ⟨π, hS.realizes⟩
  obtain ⟨β, hβ⟩ := (realizesVia_iff _ _ _ _ _).1 hS.realizes
  obtain ⟨ε0, hε0⟩ := codeCoords.exists_equiv (fun σ hσ => preserves_code hσ) hβ
  have hε0' : ∀ (γ : burnsideK42_K) (v : V),
      ε0 (((π γ : ↥M) : MulAut V) v) = burnsideK42_rho γ (ε0 v) := hε0
  obtain ⟨hzKO, hz1⟩ := hS.z_mem
  have hzKO' : z ∈ ((((fixingSubgroup (Equiv.Perm (Fin 24)) (octadPts e)).subgroupOf
      CFSG.Monster.Code.AutPerm).map π).map M.subtype) := hzKO
  obtain ⟨m, hm, hmz⟩ := Subgroup.mem_map.1 hzKO'
  obtain ⟨k, hk, hkm⟩ := Subgroup.mem_map.1 hm
  have hzk : ((π k : ↥M) : MulAut V) = z := by rw [hkm]; exact hmz
  have hk1 : k ≠ 1 := by
    intro h
    apply hz1
    rw [← hzk, h, map_one]
    rfl
  obtain ⟨z0K, hz0⟩ := burnsideK42_exists_z0K
  obtain ⟨κ, hκe, hκz⟩ := burnsideK42_reduce hz0 e hS.octad.1 hS.octad.2 k hk1 hk
  let θ0 : burnsideK42_K →* MulAut V := M.subtype.comp π
  let θ : burnsideK42_K →* MulAut V := θ0.comp (MulAut.conj κ).toMonoidHom
  have hθ : ∀ γ : burnsideK42_K, θ γ = ((π (κ * γ * κ⁻¹) : ↥M) : MulAut V) := by
    intro γ
    show ((π ((MulAut.conj κ) γ) : ↥M) : MulAut V) = _
    rw [MulAut.conj_apply]
  have hMO : burnsideK42_MO0.map θ = MO π e := by
    have h1 : burnsideK42_MO0.map θ = (burnsideK42_cj κ burnsideK42_MO0).map θ0 := by
      unfold burnsideK42_cj
      rw [Subgroup.map_map]
    rw [h1, burnsideK42_cj_MO0 hκe]
    show _ = (((m24Fix e).subgroupOf CFSG.Monster.Code.AutPerm).map π).map M.subtype
    rw [Subgroup.map_map]
  have hKO : burnsideK42_KO0.map θ = KO π e := by
    have h1 : burnsideK42_KO0.map θ = (burnsideK42_cj κ burnsideK42_KO0).map θ0 := by
      unfold burnsideK42_cj
      rw [Subgroup.map_map]
    rw [h1, burnsideK42_cj_KO0 hκe]
    show _ = (((fixingSubgroup (Equiv.Perm (Fin 24)) (octadPts e)).subgroupOf
      CFSG.Monster.Code.AutPerm).map π).map M.subtype
    rw [Subgroup.map_map]
  have hMeq : θ.range = M := by
    ext y
    constructor
    · rintro ⟨γ, rfl⟩
      rw [hθ]
      exact (π _).2
    · intro hy
      obtain ⟨γ', hγ'⟩ : ∃ γ' : burnsideK42_K, π γ' = ⟨y, hy⟩ := hS.realizes.1 ⟨y, hy⟩
      refine ⟨κ⁻¹ * γ' * κ, ?_⟩
      rw [hθ]
      have : κ * (κ⁻¹ * γ' * κ) * κ⁻¹ = γ' := by group
      rw [this, hγ']
  have hzθ : θ z0K = z := by
    rw [hθ, hκz]
    exact hzk
  have hcard : Nat.card ↥V5 = 32 := by
    have hp : IsPGroup 2 ↥V5 := fun g => ⟨1, by
      apply Subtype.ext
      show (g : V) ^ (2 ^ 1) = 1
      rw [pow_one]
      exact hV2 g⟩
    have h1 := CFSG.Quasithin.card_eq_two_pow_of_isPGroup hp
    rw [hS.V5_rank] at h1
    rw [h1]
    norm_num
  let ε : V ≃* W11 := ε0.trans (burnsideK42_rho κ⁻¹)
  have hS' : burnsideK42_Std θ ε V5 := by
    refine ⟨?_, ?_, hcard⟩
    · intro γ v
      show burnsideK42_rho κ⁻¹ (ε0 (θ γ v)) = burnsideK42_rho γ (burnsideK42_rho κ⁻¹ (ε0 v))
      rw [hθ, hε0']
      have e1 : burnsideK42_rho κ⁻¹ (burnsideK42_rho (κ * γ * κ⁻¹) (ε0 v)) =
          burnsideK42_rho (κ⁻¹ * (κ * γ * κ⁻¹)) (ε0 v) := by
        rw [map_mul burnsideK42_rho κ⁻¹ (κ * γ * κ⁻¹), MulAut.mul_apply]
      have e2 : burnsideK42_rho γ (burnsideK42_rho κ⁻¹ (ε0 v)) =
          burnsideK42_rho (γ * κ⁻¹) (ε0 v) := by
        rw [map_mul burnsideK42_rho γ κ⁻¹, MulAut.mul_apply]
      rw [e1, e2]
      have : κ⁻¹ * (κ * γ * κ⁻¹) = γ * κ⁻¹ := by group
      rw [this]
    · intro γ hγ v hv
      have h1 : θ γ ∈ MO π e := by
        rw [← hMO]
        exact Subgroup.mem_map_of_mem θ hγ
      exact hS.V5_inv _ h1 v hv
  have hd' : d ∈ Dz θ.range V5 (θ z0K) := by
    rw [hMeq, hzθ]
    exact hd
  have hdz' : d ∉ Subgroup.zpowers (θ z0K) := by
    rw [hzθ]
    exact hdz
  have hM' : MathieuCode24 θ.range ⊤ ⊥ := by
    rw [hMeq]
    exact hM
  have key := burnsideK42_std_main hS' hV2 hM' hz0 hd' hdz'
  rw [hMeq, hKO, hMO, hzθ] at key
  exact key

end

@[expose] def K_4_4_lemma : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    IsSporadic .M22 ↥L → MathieuCode22 L ⊤ ⊥ →
      (∀ D : Subgroup (MulAut V), D ≤ G → IsElemAbelian2 D → ¬ IsCyclic ↥D → IsQuadratic D →
        rk ↥D = 2 ∧ 4 ≤ rkIdx (fixV D)) ∧
      (∀ D : Subgroup (MulAut V), D ≤ G → IsElemAbelian2 D → ¬ IsCyclic ↥D →
        IsQuadratic (dualSub D) → rk ↥D = 2 ∧ 5 ≤ rkIdx (fixV (dualSub D)))

section

theorem as_K_4_4_lemma : K_4_4_lemma := by
  intro V _ _ G L hK _ hC
  have hV : ∀ v : V, v ^ 2 = 1 := hK.elem2
  obtain ⟨-, -, hLG, hGN⟩ := CFSG.Quasithin.B45Mat.b4Hyp_facts hK.hyp
  have hLG' : CFSG.Quasithin.H.Mathieu.IsOver L G := ⟨hLG, hGN⟩
  have hLG'' : CFSG.Quasithin.H.Mathieu.IsOver (CFSG.Quasithin.dualSub L)
      (CFSG.Quasithin.dualSub G) :=
    ⟨Subgroup.map_mono hLG, (Subgroup.map_mono hGN).trans (Subgroup.le_normalizer_map _)⟩
  have hq2 := CFSG.Quasithin.B45Mat.two_le_qOf_code22 hLG' hC
  have hq3 := CFSG.Quasithin.B45Mat.two_lt_qOf_cocode22 hLG''
    (CFSG.Quasithin.H.Mathieu.cocode22_dual hC)
  have hcard : Nat.card V = 2 ^ 10 := CFSG.Quasithin.H.Mathieu.code22_card hC
  have hrkV : CFSG.Quasithin.rk V = 10 := by
    unfold CFSG.Quasithin.rk
    rw [hcard, padicValNat.prime_pow]
  have key : ∀ D : Subgroup (MulAut V), D ≤ G → CFSG.Quasithin.IsElemAbelian2 D →
      ¬ IsCyclic ↥D → CFSG.Quasithin.IsQuadratic D →
      CFSG.Quasithin.rk ↥D = 2 ∧ 4 ≤ CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV D) ∧
        5 ≤ CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV (CFSG.Quasithin.dualSub D)) := by
    intro D hDG hDe hDc hDq
    have hD2 := burnsideKG_two_le_rk hDe hDc
    have hne : D ≠ ⊥ := by
      rintro rfl
      simp [CFSG.Quasithin.rk] at hD2
    have hDA : CFSG.Quasithin.IsA2 G D := ⟨hDG, hne, hDe⟩
    have h1 := burnsideKG_two_mul_le hq2 hDA hDq
    have hdne : CFSG.Quasithin.dualSub D ≠ ⊥ := by
      intro hbot
      apply hne
      rw [Subgroup.eq_bot_iff_forall]
      intro a ha
      have hmem : CFSG.Quasithin.dualAct V a ∈ CFSG.Quasithin.dualSub D := ⟨a, ha, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact CFSG.Quasithin.dualAct_injective hV (hmem.trans (map_one _).symm)
    have hdA : CFSG.Quasithin.IsA2 (CFSG.Quasithin.dualSub G) (CFSG.Quasithin.dualSub D) :=
      ⟨Subgroup.map_mono hDG, hdne, burnsideKG_isElemAbelian2_dualSub hDe⟩
    have h2 := burnsideKG_two_mul_lt hq3 hdA ((CFSG.Quasithin.isQuadratic_dualSub_iff hV D).1 hDq)
    have hrk : CFSG.Quasithin.rk ↥(CFSG.Quasithin.dualSub D) = CFSG.Quasithin.rk ↥D := by
      unfold CFSG.Quasithin.rk
      rw [CFSG.Quasithin.card_dualSub hV]
    have hidx : CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV (CFSG.Quasithin.dualSub D)) =
        CFSG.Quasithin.rk ↥(CFSG.Quasithin.commV D) := by
      unfold CFSG.Quasithin.rkIdx CFSG.Quasithin.rk
      rw [CFSG.Quasithin.index_fixV_dualSub hV]
    have h3 : CFSG.Quasithin.rk ↥(CFSG.Quasithin.commV D) ≤
        CFSG.Quasithin.rk ↥(CFSG.Quasithin.fixV D) := CFSG.Quasithin.rk_mono hDq
    have h4 := CFSG.Quasithin.rk_add_rkIdx (CFSG.Quasithin.fixV D)
    have h2' : 2 * CFSG.Quasithin.rk ↥D <
        CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV (CFSG.Quasithin.dualSub D)) :=
      lt_of_eq_of_lt (congrArg (2 * ·) hrk.symm) h2
    omega
  refine ⟨fun D hDG hDe hDc hDq => ?_, fun D hDG hDe hDc hDq => ?_⟩
  · obtain ⟨hk, hi, -⟩ := key D hDG hDe hDc hDq
    exact ⟨hk, hi⟩
  · obtain ⟨hk, -, hj⟩ := key D hDG hDe hDc ((CFSG.Quasithin.isQuadratic_dualSub_iff hV D).2 hDq)
    exact ⟨hk, hj⟩

end

@[expose] def K_4_3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    (((IsSporadic .M24 ↥L ∧ (MathieuCode24 L ⊤ ⊥ ∨ MathieuCocode24 L ⊤ ⊥)) ∨
        (IsSporadic .M23 ↥L ∧ (MathieuCode23 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥)) ∨
        (IsSporadic .M22 ↥L ∧ MathieuCocode22 L ⊤ ⊥)) → qc 2 < qOf G) ∧
    ((IsSporadic .M22 ↥L ∧ MathieuCode22 L ⊤ ⊥) → qc 2 ≤ qOf G)

section

theorem as_K_4_3 : K_4_3 := by
  intro V _ _ G L hK
  obtain ⟨-, -, hLG, hGN⟩ := CFSG.Quasithin.B45Mat.b4Hyp_facts hK.hyp
  have hLG' : CFSG.Quasithin.H.Mathieu.IsOver L G := ⟨hLG, hGN⟩
  refine ⟨?_, ?_⟩
  · rintro (⟨-, h | h⟩ | ⟨-, h | h⟩ | ⟨-, h⟩)
    · exact CFSG.Quasithin.B45Mat.two_lt_qOf_code24 hLG' h
    · exact CFSG.Quasithin.B45Mat.two_lt_qOf_cocode24 hLG' h
    · exact CFSG.Quasithin.B45Mat.two_lt_qOf_code23 hLG' h
    · exact CFSG.Quasithin.B45Mat.two_lt_qOf_cocode23 hLG' h
    · exact CFSG.Quasithin.B45Mat.two_lt_qOf_cocode22 hLG' h
  · rintro ⟨-, h⟩
    exact CFSG.Quasithin.B45Mat.two_le_qOf_code22 hLG' h

end

@[expose] def K_4_4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    IsSporadic .M12 ↥L → M12Ten L ⊤ ⊥ → qc 2 < qOf G

section

theorem as_K_4_4 : K_4_4 := by
  intro V _ _ G L hK _ h
  obtain ⟨-, -, hLG, hGN⟩ := CFSG.Quasithin.B45Mat.b4Hyp_facts hK.hyp
  exact CFSG.Quasithin.B45Mat.two_lt_qOf_m12Ten ⟨hLG, hGN⟩ h

end

@[expose] def K_4_5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    IsSporadic .J2 ↥L → J2Twelve L ⊤ ⊥ →
      (L.subgroupOf G).index ≤ 2 ∧ (∀ A, ¬ IsFFStarOffender G A) ∧ qc 1 < qhatOf G ∧
      qhatOf G = qc 2 ∧ qc 2 < qOf G ∧
      (∀ T : Subgroup (MulAut V), IsSylowTwoOf T G →
        ∀ A : Subgroup (MulAut V), IsA2 T A → rAV A ≤ 2 →
          A ≤ L ∧ rk ↥A = 4 ∧ rk ↥(fixV A) = 4 ∧ ¬ IsQuadratic A) ∧
      (∀ T : Subgroup (MulAut V), IsSylowTwoOf T G →
        ∃ A : Subgroup (MulAut V), IsA2 T A ∧ commSeries A 3 = ⊥ ∧ rAV A = 2 ∧
          A ≤ L ∧ rk ↥A = 4 ∧ rk ↥(fixV A) = 4 ∧ ¬ IsQuadratic A)

section
open CFSG.Quasithin CFSG.Quasithin.J2Row CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
open CFSG.Quasithin CFSG.Quasithin.J2Model CFSG.Quasithin.J2Row CFSG.Quasithin.H

open CFSG.Quasithin in
theorem as_K_4_5 : K_4_5 := by
  intro V _ _ G L hK hJ _
  have hV := hK.elem2
  have hHyp := hK.hyp
  have h2 := hK.qhat
  obtain ⟨θ⟩ := hJ
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
    CFSG.Sporadic.J2.isSimpleGroup_J2
  have hZ := burnsideKF_center_eq_bot hHyp.2.2.1.1 θ
  have hT : B45TypeSpor .J2 ↥L := ⟨hZ, ⟨θ⟩⟩
  obtain ⟨-, hcardV, hbound⟩ := burnsideKF_j2_bound hV hHyp hT h2
  have hqhat2 : ((2 : ℚ) : WithTop ℚ) ≤ qhatOf G := by
    unfold qhatOf
    rw [le_kq_iff]
    intro A hA _
    rw [J2Row.two_le_rAV_iff hV hA, hcardV]
    exact (hbound A hA).1.1
  have hq2 : ((2 : ℚ) : WithTop ℚ) < qOf G := by
    unfold qOf
    rw [lt_kq_iff]
    intro A hA hAq
    rw [J2Row.two_lt_rAV_iff hV hA, hcardV]
    exact (hbound A hA).1.2 ((isQuadratic_iff_commSeries_two A).mpr hAq)
  have hqhat : qhatOf G = ((2 : ℚ) : WithTop ℚ) := le_antisymm h2 hqhat2
  have h6 : ∀ T : Subgroup (MulAut V), CFSG.QuasithinUnique.IsSylowTwoOf T G →
      ∀ A : Subgroup (MulAut V), IsA2 T A → rAV A ≤ 2 →
        A ≤ L ∧ rk ↥A = 4 ∧ rk ↥(fixV A) = 4 ∧ ¬ IsQuadratic A := by
    intro T hT A hA hr
    have hAG : IsA2 G A := ⟨hA.1.trans hT.1, hA.2.1, hA.2.2⟩
    have hge : 4096 ≤ Nat.card A ^ 2 * Nat.card ↥(fixV A) := by
      rw [← hcardV]
      exact (rAV_le_two_iff hV hAG).mp hr
    obtain ⟨hAL, h16, hc16⟩ := (hbound A hAG).2 hge
    have hp : padicValNat 2 16 = 4 := by simpa using padicValNat.prime_pow (p := 2) 4
    refine ⟨hAL, ?_, ?_, fun hq => absurd ((hbound A hAG).1.2 hq) (not_lt.mpr hge)⟩
    · rw [rk, h16]
      exact hp
    · rw [rk, hc16]
      exact hp
  refine ⟨burnsideKF_index_le_two hHyp hZ (burnsideKF_j2_aut_le θ), ?_,
    lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hqhat2, hqhat, hq2, h6, ?_⟩
  · rintro A ⟨hAG, hAne, hAel, hmin⟩
    have hAG2 : IsA2 G A := ⟨hAG, hAne, hAel⟩
    have hoff : Nat.card V ≤ Nat.card A * Nat.card ↥(fixV A) := by
      have h := hmin ⊥ bot_le
      rwa [B1.card_bot_mul_card_fixV] at h
    have h1 := (hbound A hAG2).1.1
    have hA2 : 2 ≤ Nat.card A := by
      have := (Subgroup.one_lt_card_iff_ne_bot A).mpr hAne
      omega
    have hCpos : 0 < Nat.card ↥(fixV A) := Nat.card_pos
    rw [hcardV] at hoff
    have : 2 * (Nat.card A * Nat.card ↥(fixV A)) ≤ Nat.card A ^ 2 * Nat.card ↥(fixV A) :=
      calc 2 * (Nat.card A * Nat.card ↥(fixV A)) ≤ Nat.card A * (Nat.card A * Nat.card ↥(fixV A)) :=
            Nat.mul_le_mul_right _ hA2
        _ = Nat.card A ^ 2 * Nat.card ↥(fixV A) := by ring
    have hpos : 0 < Nat.card A * Nat.card ↥(fixV A) := Nat.mul_pos (by omega) hCpos
    omega
  · intro T hT
    obtain ⟨A, hAG, hA3, hAr⟩ := (kq_eq_coe_iff.mp hqhat).1
    obtain ⟨g, hg, hgA⟩ := burnsideKF_exists_conj_le hT hAG.1 hAG.isElemAbelian2.isPGroup
    have hA'G : IsA2 G (A.map (MulAut.conj g).toMonoidHom) := by
      rw [← burnsideKF_conjAut_eq]
      exact B1.isA2_conjAut hAG hg
    have hA'T : IsA2 T (A.map (MulAut.conj g).toMonoidHom) := ⟨hgA, hA'G.2.1, hA'G.2.2⟩
    have hr : rAV (A.map (MulAut.conj g).toMonoidHom) = 2 := by
      rw [← burnsideKF_conjAut_eq, RAV.rAV_conjAut]
      exact hAr
    obtain ⟨hAL, h4, h4', hnq⟩ := h6 T hT _ hA'T hr.le
    refine ⟨_, hA'T, ?_, hr, hAL, h4, h4', hnq⟩
    rw [Z391.commSeries_map_conj g A 3, hA3, Subgroup.map_bot]

end

end CFSG.ASVolI
