module

public import CFSG.Quasithin.MS93.S32Dict
public import CFSG.Quasithin.Background.B5Irr

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.MS93
open scoped commutatorElement

variable {G : Type} [Group G] {M T L : Subgroup G}
variable {F : Type} [CommGroup F]

structure IsIrrRep (L : Subgroup G) (ρ : ↥M →* MulAut F) : Prop where
  sq : ∀ v : F, v ^ 2 = 1
  pCore : ∀ m : ↥M, (m : G) ∈ pCoreOf 2 M → ρ m = 1
  irr : ∀ W : Subgroup F, (∀ m : ↥M, ∀ w ∈ W, ρ m w ∈ W) → W = ⊥ ∨ W = ⊤
  ne : ∃ l : ↥M, (l : G) ∈ L ∧ ρ l ≠ 1

namespace IsIrrRep

variable {ρ : ↥M →* MulAut F}

abbrev imL (L : Subgroup G) (ρ : ↥M →* MulAut F) : Subgroup (MulAut F) :=
  (L.subgroupOf M).map ρ

theorem imL_le : imL L ρ ≤ ρ.range := Subgroup.map_le_range _ _

theorem range_le_normalizer [Finite G] (h : PUHyp M T L) :
    ρ.range ≤ Subgroup.normalizer (imL L ρ : Set (MulAut F)) := by
  rintro _ ⟨m, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ m : ↥M, ∀ k ∈ imL L ρ, ρ m * k * (ρ m)⁻¹ ∈ imL L ρ := by
    rintro m _ ⟨l, hl, rfl⟩
    refine ⟨m * l * m⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (h.le_normalizer m.2) l).mp hl
  intro k
  refine ⟨key m k, fun hk => ?_⟩
  have := key m⁻¹ _ hk
  simpa [mul_assoc] using this

noncomputable def toImL [Finite G] (L : Subgroup G) (ρ : ↥M →* MulAut F) (h : PUHyp M T L) :
    ↥L →* ↥(imL L ρ) :=
  (ρ.comp (Subgroup.inclusion h.L_le)).codRestrict _ fun l =>
    ⟨Subgroup.inclusion h.L_le l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩

theorem toImL_surjective [Finite G] (h : PUHyp M T L) : Function.Surjective (toImL L ρ h) := by
  rintro ⟨_, ⟨m, hm, rfl⟩⟩
  refine ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, Subtype.ext ?_⟩
  rfl

theorem pCore_le_ker [Finite G] (hρ : IsIrrRep L ρ) (h : PUHyp M T L) :
    CFSG.pCore 2 ↥L ≤ (toImL L ρ h).ker := by
  intro o ho
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  have hoQ : (o : G) ∈ pCoreOf 2 M :=
    pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer (mem_pCoreOf_of_mem_pCore_two ho)
  exact hρ.pCore _ hoQ

noncomputable def quotHom [Finite G] (hρ : IsIrrRep L ρ) (h : PUHyp M T L) :
    ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(imL L ρ) :=
  QuotientGroup.lift _ (toImL L ρ h) (hρ.pCore_le_ker h)

theorem quotHom_surjective [Finite G] (hρ : IsIrrRep L ρ) (h : PUHyp M T L) :
    Function.Surjective (hρ.quotHom h) := by
  intro k
  obtain ⟨l, rfl⟩ := toImL_surjective h k
  exact ⟨QuotientGroup.mk l, rfl⟩

theorem quotHom_ne_one [Finite G] (hρ : IsIrrRep L ρ) (h : PUHyp M T L) :
    ∃ k, hρ.quotHom h k ≠ 1 := by
  obtain ⟨l, hl, hne⟩ := hρ.ne
  refine ⟨QuotientGroup.mk ⟨l, hl⟩, fun h1 => hne ?_⟩
  have := congrArg Subtype.val h1
  exact this

theorem quasisimple [Finite G] (hρ : IsIrrRep L ρ) (h : PUHyp M T L) :
    CFSG.IsQuasisimple ↥(imL L ρ) :=
  CFSG.LieType.CurtisTits.isQuasisimple_of_surjective h.quasisimple (hρ.quotHom_surjective h)
    (hρ.quotHom_ne_one h)

theorem rankTwo [Finite G] (hρ : IsIrrRep L ρ) (h : PUHyp M T L) :
    IsRankTwoLie2Derived (↥(imL L ρ) ⧸ Subgroup.center ↥(imL L ρ)) :=
  isRankTwoLie2Derived_of_mulEquiv
    (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple h.quasisimple
      (hρ.quotHom_surjective h)
      (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple h.quasisimple
        (hρ.quotHom_ne_one h))) h.rankTwo

theorem sqtk [Finite G] [Finite F] (hρ : IsIrrRep L ρ) (h : PUHyp M T L) (hSQ : SQTKQuot) :
    SQTKGroup ↥(imL L ρ) := by
  have hL : SQTKGroup ↥(L.subgroupOf M) := InternalSec.sqtkGroup_subgroup h.sqtk _
  let f : ↥(L.subgroupOf M) →* ↥(imL L ρ) :=
    (toImL L ρ h).comp (Subgroup.subgroupOfEquivOfLe h.L_le).toMonoidHom
  refine hSQ _ _ hL f ?_ (hρ.quasisimple h)
  intro y
  obtain ⟨l, rfl⟩ := toImL_surjective h y
  exact ⟨(Subgroup.subgroupOfEquivOfLe h.L_le).symm l, by simp [f]⟩

abbrev kerG (ρ : ↥M →* MulAut F) : Subgroup G := ρ.ker.map M.subtype

theorem le_normalizer_kerG : M ≤ Subgroup.normalizer (kerG ρ : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ m : ↥M, ∀ x ∈ kerG ρ, (m : G) * x * (m : G)⁻¹ ∈ kerG ρ := by
    rintro m _ ⟨k, hk, rfl⟩
    refine ⟨m * k * m⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hk
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    rw [map_mul, map_mul, hk, mul_one, map_inv, mul_inv_cancel]
  intro x
  refine ⟨key ⟨m, hm⟩ x, fun hx => ?_⟩
  have := key ⟨m, hm⟩⁻¹ _ hx
  simpa [mul_assoc] using this

theorem not_le_kerG (hρ : IsIrrRep L ρ) : ¬ L ≤ kerG ρ := by
  intro hL
  obtain ⟨l, hl, hne⟩ := hρ.ne
  obtain ⟨k, hk, hkl⟩ := hL hl
  apply hne
  have : k = l := Subtype.ext hkl
  rw [← this]
  exact hk

theorem cent [Finite G] (hρ : IsIrrRep L ρ) (h : PUHyp M T L) :
    ∀ c ∈ ρ.range, (∀ k ∈ imL L ρ, c * k = k * c) → ∀ e : ℕ, c ^ 2 ^ e = 1 → c = 1 := by
  rintro _ ⟨m, rfl⟩ hck e he
  obtain ⟨k, hk, f, hf⟩ := exists_pow_isTwoElt ρ m he
  rw [← hk]
  set m' := m ^ k
  have hm'Q : (m' : G) ∈ pCoreOf 2 M := by
    refine h.mem_pCoreOf_of_rel le_normalizer_kerG hρ.not_le_kerG m'.2
      ⟨f, by simpa using congrArg Subtype.val hf⟩ fun l hl => ?_
    refine ⟨⁅m', ⟨l, h.L_le hl⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm, hk]
    exact hck _ ⟨⟨l, h.L_le hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  exact hρ.pCore _ hm'Q

theorem two [Finite G] (h : PUHyp M T L) : ∀ x ∈ ρ.range, ∃ e : ℕ, x ^ 2 ^ e ∈ imL L ρ := by
  rintro _ ⟨m, rfl⟩
  obtain ⟨e, he⟩ := h.exists_pow_mem_L m.2
  refine ⟨e, ⟨m ^ 2 ^ e, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩⟩
  simpa using he

theorem nontrivial (hρ : IsIrrRep L ρ) : Nontrivial F := by
  by_contra hF
  rw [not_nontrivial_iff_subsingleton] at hF
  obtain ⟨l, -, hne⟩ := hρ.ne
  exact hne (MulEquiv.ext fun v => Subsingleton.elim _ _)

theorem fixV_ne_bot [Finite F] (hρ : IsIrrRep L ρ) {P : Subgroup (MulAut F)}
    (hP : IsPGroup 2 ↥P) : fixV P ≠ ⊥ := by
  have : Nontrivial F := hρ.nontrivial
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints F
  have hfix : Nat.card (MulAction.fixedPoints ↥P F) = Nat.card (fixV P) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  rw [hfix] at hmod
  have hV2 : IsPGroup 2 F := fun v => ⟨1, by rw [pow_one]; exact hρ.sq v⟩
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
  have heven : Nat.card F % 2 = 0 := by
    rw [hn]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn0)
  intro hbot
  rw [hbot, Subgroup.card_bot] at hmod
  have := hmod.symm
  unfold Nat.ModEq at this
  omega

theorem ffHyp [Finite G] [Finite F] (hρ : IsIrrRep L ρ) (h : PUHyp M T L) (hSQ : SQTKQuot)
    (hFF : IsFFModule ρ.range) : FFHyp ρ.range (imL L ρ) := by
  refine ⟨imL_le, range_le_normalizer h, hρ.quasisimple h, hρ.sqtk h hSQ, hρ.rankTwo h,
    hρ.cent h, two h, ?_, ?_, hFF⟩
  · obtain ⟨S, hS⟩ := B5.exists_isSylowTwoOf (imL L ρ)
    refine ⟨S, hS, ?_⟩
    have hne : fixV S ≠ ⊥ := hρ.fixV_ne_bot hS.2.1
    have hinv : ∀ m : ↥M, ∀ w ∈ G6.submoduleClosure ρ.range (fixV S),
        ρ m w ∈ G6.submoduleClosure ρ.range (fixV S) :=
      fun m w hw => submoduleClosure_inv (ρ.mem_range.mpr ⟨m, rfl⟩) hw
    rcases hρ.irr _ hinv with hb | ht
    · exact absurd (eq_bot_iff.mpr ((le_submoduleClosure _ _).trans hb.le)) hne
    · exact ht
  · have hinv : ∀ m : ↥M, ∀ w ∈ fixV ρ.range, ρ m w ∈ fixV ρ.range := by
      intro m w hw x hx
      rw [hw (ρ m) ⟨m, rfl⟩]
      exact hw x hx
    rcases hρ.irr _ hinv with hb | ht
    · exact hb
    · exfalso
      obtain ⟨l, -, hne⟩ := hρ.ne
      apply hne
      refine MulEquiv.ext fun v => ?_
      have hv : v ∈ fixV ρ.range := by rw [ht]; exact Subgroup.mem_top v
      exact hv _ ⟨l, rfl⟩

end IsIrrRep

end CFSG.Quasithin.MS93.S38E
