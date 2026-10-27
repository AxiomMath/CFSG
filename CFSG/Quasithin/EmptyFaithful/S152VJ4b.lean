module

public import CFSG.Quasithin.EmptyFaithful.S152VJ4a
public import CFSG.Quasithin.EmptyFaithful.S152VL2
public import CFSG.Quasithin.H13.J4TypeFinal
public import CFSG.Quasithin.EmptyFaithful.R3c3Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Transport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open scoped commutatorElement

namespace S152V

theorem two_mul_card_J4_ne (p : ℕ) : 2 * (86775571046077562880 : ℕ) ≠ p * (p ^ 2 - 1) := by
  intro h
  have hmono : ∀ a b : ℕ, a ≤ b → a * (a ^ 2 - 1) ≤ b * (b ^ 2 - 1) := fun a b hab =>
    Nat.mul_le_mul hab (Nat.sub_le_sub_right (Nat.pow_le_pow_left hab 2) 1)
  by_cases hp : p ≤ 5577965
  · have h1 := hmono p 5577965 hp
    rw [← h] at h1
    norm_num at h1
  · push Not at hp
    have h2 := hmono 5577966 p hp
    rw [← h] at h2
    norm_num at h2

theorem card_eq_of_centerBot {X Y : Type} [Group X] [Group Y] (hZ : Subgroup.center X = ⊥)
    (φ : (X ⧸ Subgroup.center X) ≃* Y) : Nat.card X = Nat.card Y := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  rw [Nat.card_congr φ.toEquiv] at h1
  have h2 : Nat.card (Subgroup.center X) = 1 := by rw [hZ]; exact Subgroup.card_bot
  rw [h2, mul_one] at h1
  exact h1

section Action

variable {G : Type} [Group G]

theorem inner_mul_self_eq_one {L : Subgroup G} {z l : G} (hZ : Subgroup.center ↥L = ⊥) (hz2 : z ^ 2 = 1)
    (hl : l ∈ L) (h : ∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l) : l * l = 1 := by
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hc : ∀ x ∈ L, (l * l) * x = x * (l * l) := by
    intro x hx
    have hy : z⁻¹ * x * z = l⁻¹ * x * l := h x hx
    have hyL : l⁻¹ * x * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
    have h1 : z⁻¹ * (z⁻¹ * x * z) * z = x := by
      rw [hzinv]
      calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
        _ = x := by rw [hzz]; group
    have h2 : z⁻¹ * (z⁻¹ * x * z) * z = l⁻¹ * (l⁻¹ * x * l) * l := by
      rw [hy]
      exact h _ hyL
    have h3 : x = (l * l)⁻¹ * x * (l * l) := by
      calc x = l⁻¹ * (l⁻¹ * x * l) * l := h1.symm.trans h2
        _ = (l * l)⁻¹ * x * (l * l) := by group
    calc (l * l) * x = (l * l) * ((l * l)⁻¹ * x * (l * l)) := by rw [← h3]
      _ = x * (l * l) := by group
  have hmem : (⟨l * l, L.mul_mem hl hl⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  rw [hZ] at hmem
  exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)

theorem commute_of_commutator_centralizes {L P : Subgroup G} {l : G} (hZ : Subgroup.center ↥L = ⊥)
    (hPL : P ≤ L) (hl : l ∈ L) (hcom : ∀ p ∈ P, ⁅p, l⁆ ∈ Subgroup.centralizer (L : Set G)) {p : G}
    (hp : p ∈ P) : p * l = l * p := by
  have hpL : p ∈ L := hPL hp
  have hcL : ⁅p, l⁆ ∈ L := by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hpL hl) (L.inv_mem hpL)) (L.inv_mem hl)
  have hmem : (⟨⁅p, l⁆, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hcom p hp) g g.2)
  rw [hZ] at hmem
  have h1 : ⁅p, l⁆ = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem subgroupOf_centralizer_eq {L : Subgroup G} {z l : G} (hl : l ∈ L)
    (h : ∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l) :
    (L ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf L =
      Subgroup.centralizer ({(⟨l, hl⟩ : ↥L)} : Set ↥L) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, hx⟩
    have hzx : z * (x : G) = (x : G) * z := hx z (Set.mem_singleton z)
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    apply Subtype.ext
    show l * (x : G) = (x : G) * l
    have h1 : z⁻¹ * (x : G) * z = x := by
      calc z⁻¹ * (x : G) * z = z⁻¹ * ((x : G) * z) := by group
        _ = z⁻¹ * (z * (x : G)) := by rw [hzx]
        _ = x := by group
    have h2 := h x x.2
    rw [h1] at h2
    calc l * (x : G) = l * (l⁻¹ * (x : G) * l) := by rw [← h2]
      _ = (x : G) * l := by group
  · intro hx
    refine ⟨x.2, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hlx : l * (x : G) = (x : G) * l := congrArg Subtype.val (hx _ (Set.mem_singleton _))
    have h1 : l⁻¹ * (x : G) * l = x := by
      calc l⁻¹ * (x : G) * l = l⁻¹ * ((x : G) * l) := by group
        _ = l⁻¹ * (l * (x : G)) := by rw [hlx]
        _ = x := by group
    have h2 : z⁻¹ * (x : G) * z = x := by rw [h x x.2, h1]
    calc z * (x : G) = z * (z⁻¹ * (x : G) * z) := by rw [h2]
      _ = (x : G) * z := by group

theorem map_subgroupOf_centralizer_eq {L : Subgroup G} {z l : G} {Y : Type} [Group Y] (e : ↥L ≃* Y)
    (hl : l ∈ L) (h : ∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l) :
    ((L ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf L).map e.toMonoidHom =
      Subgroup.centralizer ({e ⟨l, hl⟩} : Set Y) := by
  rw [subgroupOf_centralizer_eq hl h]
  exact H13.J4.map_centralizer_singleton e _

noncomputable def centralizerEquiv {L : Subgroup G} {z l : G} {Y : Type} [Group Y] (e : ↥L ≃* Y)
    (hl : l ∈ L) (h : ∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l) :
    ↥(L ⊓ Subgroup.centralizer ({z} : Set G)) ≃* ↥(Subgroup.centralizer ({e ⟨l, hl⟩} : Set Y)) :=
  (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : L ⊓ Subgroup.centralizer ({z} : Set G) ≤ L)).symm.trans
    (H13.J4.subgroupEquivOfMap e (map_subgroupOf_centralizer_eq e hl h))

end Action

end S152V

open S152V in
theorem hasSectionIso_of_isAutTripleM22 {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {z l : G} {Y : Type} [Group Y] (e : ↥L ≃* Y) (hl : l ∈ L) (hlz : ∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l)
    (hX : H13.J4.IsAutTripleM22 (↥(Subgroup.centralizer ({e ⟨l, hl⟩} : Set Y)) ⧸
      CFSG.pCore 2 ↥(Subgroup.centralizer ({e ⟨l, hl⟩} : Set Y)))) :
    S152U.HasSectionIso (oPrimeResidualOf 3 (L ⊓ Subgroup.centralizer ({z} : Set G)))
      (NativeSporadic.Carrier .M22) := by
  obtain ⟨f, hf⟩ := exists_surjective_oPrimeResidual (centralizerEquiv e hl hlz) hX
  exact ⟨oPrimeResidualOf 3 (L ⊓ Subgroup.centralizer ({z} : Set G)), f.ker, inferInstance, le_rfl,
    ⟨QuotientGroup.quotientKerEquivOfSurjective f hf⟩⟩

theorem j4_twoCentral_aut
    {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.J4) {x : X}
    (hx : orderOf x = 2) (S : Sylow 2 X)
    (hxS : x ∈ (Subgroup.center (S : Subgroup X)).map (S : Subgroup X).subtype) :
    H13.J4.IsAutTripleM22 (↥(Subgroup.centralizer ({e x} : Set NativeSporadic.J4)) ⧸
      CFSG.pCore 2 ↥(Subgroup.centralizer ({e x} : Set NativeSporadic.J4))) := by
  obtain ⟨hord, S', hS'⟩ :=
    @H13.J4.twoCentral_of_mulEquiv X NativeSporadic.J4 _ Units.instGroup _ x (e x) S hxS e rfl
  obtain ⟨-, -, -, -, htype⟩ := H13.J4.concreteJ4_typeJ4
  obtain ⟨-, -, -, hX, -⟩ := htype (e x) (hord.trans hx) ⟨S', hS'⟩
  exact hX

open S152V in
theorem tail15215J4_of :
    Tail15215J4 := by
  intro G _ _ I S Mi L L₀ K P z cfg hJ
  obtain ⟨e⟩ : Nonempty (↥L ≃* NativeSporadic.J4) := hJ
  obtain ⟨hsimJ, -, -, -, -⟩ := H13.J4.concreteJ4_typeJ4
  have hfinJ : Finite NativeSporadic.J4 := (CFSG.Sporadic.J4.fam_j4_simplicity).1
  have hcardJ : Nat.card NativeSporadic.J4 = 86775571046077562880 := CFSG.Sporadic.J4.card_J4
  have hsimL : IsSimpleGroup ↥L := @MulEquiv.isSimpleGroup ↥L _ NativeSporadic.J4 _ hsimJ e
  have hperfL : Group.IsPerfect ↥L := (BenderBranch.isQuasisimple_of_isComponentIn cfg.comp).1
  have hZ : Subgroup.center ↥L = ⊥ := CFSG.Quasithin.R3c3.center_eq_bot_of_simple_perfect hsimL hperfL
  have hcardL : Nat.card ↥L = 86775571046077562880 := by
    rw [Nat.card_congr e.toEquiv]
    exact hcardJ
  have hF : InducesTwoCentralInner z L := by
    rcases cfg.cases with ⟨-, hlie, -⟩ | ⟨hne, -, -, -⟩ | ⟨φ, σ, -, -, -⟩ | ⟨φ, σ, -, -, -⟩ |
      ⟨hmodel, -⟩ | ⟨-, hF⟩
    · exact absurd (Lemma115LieCharTwo.of_mulEquiv
        (CFSG.Quasithin.R3c3.quotCenterEquivOfSimple hsimL hperfL) hlie) cfg.notLie
    · exact absurd hZ hne
    · exfalso
      have h6 := card_eq_of_centerBot hZ φ
      rw [hcardL, card_alternatingGroup_six'] at h6
      omega
    · exfalso
      have h7 := card_eq_of_centerBot hZ φ
      rw [hcardL, card_alternatingGroup_seven'] at h7
      omega
    · exfalso
      rcases hmodel with h | ⟨p, hFM, h⟩
      · have h33 := CFSG.Quasithin.F420.card_of_l33 (Or.inl h)
        rw [hcardL] at h33
        omega
      · have h2 := CFSG.Quasithin.F420.two_mul_card_of_statedPSL_two_odd hFM.1 (fm_ne_two hFM) h
        rw [hcardL] at h2
        exact two_mul_card_J4_ne p h2
    · exact hF
  obtain ⟨l, hl, hlz, hnc, P', hP, hcom⟩ := hF
  have hll : l * l = 1 := inner_mul_self_eq_one hZ cfg.z2 hl hlz
  have hl1 : l ≠ 1 := by
    intro h1
    obtain ⟨x, hx, hxne⟩ := hnc
    apply hxne
    rw [hlz x hx, h1]
    simp
  have hcommP : ∀ p ∈ P', p * l = l * p := fun p hp =>
    commute_of_commutator_centralizes hZ hP.1 hl hcom hp
  let lam : ↥L := ⟨l, hl⟩
  have hlam2 : lam ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hll)
  have hlam1 : lam ≠ 1 := fun h => hl1 (congrArg Subtype.val h)
  have hordlam : orderOf lam = 2 := orderOf_eq_prime hlam2 hlam1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPl2 : IsPGroup 2 ↥(P'.subgroupOf L) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  let Sy : Sylow 2 ↥L := hPl2.toSylow hP.2.2
  have hSyc : (Sy : Subgroup ↥L) = P'.subgroupOf L := IsPGroup.toSylow_coe _ _
  have hSy : ∀ s ∈ (Sy : Subgroup ↥L), s * lam = lam * s := by
    intro s hs
    rw [hSyc, Subgroup.mem_subgroupOf] at hs
    exact Subtype.ext (hcommP s hs)
  have hlamS : lam ∈ (Sy : Subgroup ↥L) := by
    have hP2 : IsPGroup 2 ↥(Subgroup.zpowers lam) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hordlam, pow_one]
    have hS : (Sy : Subgroup ↥L) ≤ Subgroup.centralizer ({lam} : Set ↥L) := fun s hs =>
      Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (hSy s hs).symm
    have hle : (Sy : Subgroup ↥L) ≤
        Subgroup.normalizer ((Subgroup.zpowers lam : Subgroup ↥L) : Set ↥L) := by
      intro s hs
      have h1 : s ∈ Subgroup.centralizer ((Subgroup.zpowers lam : Subgroup ↥L) : Set ↥L) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        exact hS hs
      exact Subgroup.centralizer_le_normalizer _ h1
    have hmax := Sy.is_maximal' (Sy.isPGroup'.to_sup_of_normal_right' hP2 hle) le_sup_left
    rw [← hmax]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)
  have hlamC : lam ∈ (Subgroup.center (Sy : Subgroup ↥L)).map (Sy : Subgroup ↥L).subtype :=
    H13.J4.mem_center_map_iff.2 ⟨hlamS, hSy⟩
  exact @hasSectionIso_of_isAutTripleM22 G _ _ L z l NativeSporadic.J4 Units.instGroup e hl hlz
    (j4_twoCentral_aut e hordlam Sy hlamC)

end CFSG.Quasithin
