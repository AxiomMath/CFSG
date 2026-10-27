module

public import CFSG.Quasithin.Background.RonanF13Hall
public import CFSG.Quasithin.Recognition.St84.Gen.L2SecDim
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzSmall
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.Quasithin.Background.RonanF13Singer
public import CFSG.Quasithin.Recognition.Stroth.BenderNoFF
public import CFSG.Quasithin.Vol2.Ch1Quotient

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement
open CFSG.Quasithin.RonanF13 (HallTwoPrime)

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.H13.NFa2
open CFSG.RankThree.GF2n.Tim81.Sec2

variable {G : Type} [Group G] [Finite G]

private theorem isSimpleGroup_sz {a : ℕ} (ha : 1 ≤ a) : IsSimpleGroup ↥(Sz a) := by
  haveI : IsSimpleGroup (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :=
    (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_6 a (by omega)).1
  exact (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a).isSimpleGroup

private theorem not_isMulCommutative_sz {a : ℕ} (ha : 1 ≤ a) :
    ¬ IsMulCommutative ↥(Sz a) := by
  intro hcomm
  haveI : IsMulCommutative ↥(Sz a) := hcomm
  obtain ⟨x, y, hxy⟩ := CFSG.SectionRank.suzukiMatrixGroup_nonabelian a (by omega)
  have hxy' : (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a).symm x *
      (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a).symm y =
      (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a).symm y *
      (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a).symm x :=
    mul_comm' _ _
  exact hxy (by
    have h := congrArg (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a) hxy'
    simpa using h)

private theorem exists_trivSubgroup {V Z L : Subgroup G} (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G)) :
    ∃ N : Subgroup ↥L, N.Normal ∧
      ∀ x : ↥L, x ∈ N ↔ ∀ v ∈ V, ⁅(x : G), v⁆ ∈ Z := by
  classical
  let N : Subgroup ↥L :=
    { carrier := {x | ∀ v ∈ V, ⁅(x : G), v⁆ ∈ Z}
      one_mem' := by
        intro v _
        simp
      mul_mem' := by
        intro x y hx hy v hv
        have e : ⁅((x * y : ↥L) : G), v⁆ =
            (x : G) * ⁅(y : G), v⁆ * (x : G)⁻¹ * ⁅(x : G), v⁆ := by
          simp only [Subgroup.coe_mul, commutatorElement_def]
          group
        rw [e]
        exact Z.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp (hL x.2)).2 _).mp
            (hy v hv))
          (hx v hv)
      inv_mem' := by
        intro x hx v hv
        have e : ⁅((x⁻¹ : ↥L) : G), v⁆ =
            (x : G)⁻¹ * ⁅(x : G), v⁆⁻¹ * (x : G) := by
          simp only [Subgroup.coe_inv, commutatorElement_def]
          group
        rw [e]
        have hxZ : (x : G)⁻¹ ∈ Subgroup.normalizer (Z : Set G) :=
          Subgroup.inv_mem _ (Subgroup.mem_inf.mp (hL x.2)).2
        simpa using (Subgroup.mem_normalizer_iff.mp hxZ _).mp (Z.inv_mem (hx v hv)) }
  refine ⟨N, ⟨fun n hn x => ?_⟩, fun x => Iff.rfl⟩
  intro v hv
  have hxV : (x : G) ∈ Subgroup.normalizer (V : Set G) := (Subgroup.mem_inf.mp (hL x.2)).1
  have hxZ : (x : G) ∈ Subgroup.normalizer (Z : Set G) := (Subgroup.mem_inf.mp (hL x.2)).2
  have hconjV : (x : G)⁻¹ * v * (x : G) ∈ V := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxV) v).mp hv
  have e : ⁅((x * n * x⁻¹ : ↥L) : G), v⁆ =
      (x : G) * ⁅(n : G), (x : G)⁻¹ * v * (x : G)⁆ * (x : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hxZ _).mp (hn _ hconjV)

private theorem eq_top_of_pCore_le_of_map_ne_bot {L : Subgroup G} {N : Subgroup ↥L}
    (hN : N.Normal) (hP : CFSG.pCore 2 ↥L ≤ N)
    (hs : IsSimpleGroup (oTwoQuot ↥L))
    (hne : N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≠ ⊥) : N = ⊤ := by
  classical
  let q : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  haveI hmap : (N.map q).Normal :=
    hN.map q (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map q) with hbot | htop
  · exact absurd hbot hne
  · rw [eq_top_iff]
    intro x _
    have hx : q x ∈ N.map q := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hnq⟩ := Subgroup.mem_map.mp hx
    have hmem : n⁻¹ * x ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.eq_one_iff]
      change q (n⁻¹ * x) = 1
      rw [map_mul, map_inv, hnq, inv_mul_cancel]
    simpa using N.mul_mem hn (hP hmem)

private theorem exists_sq_map_ne_one_of_sz
    {L T : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L) :
    ∃ t : ↥L, (t : G) ∈ T ∧ (QuotientGroup.mk' (CFSG.pCore 2 ↥L) t) ^ 2 ≠ 1 := by
  classical
  obtain ⟨eSz⟩ := hSz
  let q : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let P : Subgroup ↥(Sz a) := ((T.subgroupOf L).map q).map eSz.toMonoidHom
  have hSyl0 : IsSylowTwoOf (T.subgroupOf L) ⊤ := by
    obtain ⟨hTL, hT2, hTi⟩ := hT
    refine ⟨le_top, hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm, ?_⟩
    rwa [show ((T.subgroupOf L).subgroupOf ⊤).index = (T.subgroupOf L).index from
      Subgroup.relIndex_top_right _]
  have hSyl1 : IsSylowTwoOf ((T.subgroupOf L).map q) ⊤ :=
    isSylowTwoOf_top_map_of_surjective hSyl0 q (QuotientGroup.mk'_surjective _)
  have hSylP : IsSylowTwoOf P ⊤ :=
    isSylowTwoOf_top_map_of_surjective hSyl1 eSz.toMonoidHom eSz.surjective
  obtain ⟨y, hy⟩ := CFSG.Timmesfeld.RankOne.exists_orderOf_eq_four_suzuki (k := a) (by omega)
  let x : ↥(Sz a) := (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a).symm y
  have hx : orderOf x = 4 :=
    (MulEquiv.orderOf_eq (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a).symm y).trans
      hy
  have hzp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨g, -, hg⟩ :=
    CFSG.Quasithin.F7.isSylowTwoOf_exists_conj_le hSylP
      (le_top : Subgroup.zpowers x ≤ ⊤) hzp
  have hxg : x ∈ conjSub g P := hg (Subgroup.mem_zpowers x)
  rw [mem_conjSub] at hxg
  have hxconj : orderOf (g⁻¹ * x * g) = 4 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
    simpa [MulAut.conj_apply] using h.trans hx
  obtain ⟨y', hy'P, hy'e⟩ := Subgroup.mem_map.mp hxg
  obtain ⟨z, hzT, hzq⟩ := Subgroup.mem_map.mp hy'P
  have hy'e' : eSz y' = g⁻¹ * x * g := hy'e
  have hy'4 : orderOf y' = 4 := by
    rw [← MulEquiv.orderOf_eq eSz y', hy'e']
    exact hxconj
  have hz4 : orderOf (q z) = 4 := by
    rw [hzq]
    exact hy'4
  have hsq : (q z) ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf (q z) ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hz4] at hdvd
    norm_num at hdvd
  exact ⟨z, Subgroup.mem_subgroupOf.mp hzT, by simpa [q] using hsq⟩

private theorem two_pow_le_relIndex_of_irreducible_of_sz
    {V Z L : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hirr : ∀ W : Subgroup G, Z ≤ W → W ≤ V → L ≤ Subgroup.normalizer (W : Set G) →
      W = Z ∨ W = V)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) :
    2 ^ (4 * (2 * a + 1)) ≤ Z.relIndex V := by
  classical
  have hVZ : Z ≤ V := hsec.1
  have hnormalZV : V ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono le_rfl hVZ).trans hsec.2.1)
  have hsecHyp : SecHyp L Z V :=
    { le := hVZ
      norm₀ := hL.trans inf_le_right
      norm₁ := hL.trans inf_le_left
      normal := hnormalZV
      comm := fun a ha b hb => hsec.2.1 (Subgroup.commutator_mem_commutator ha hb)
      sq := fun a ha => by simpa [pow_two] using hsec.2.2 a ha }
  have hChief : IsChiefPair L Z V :=
    { lt := lt_of_le_of_ne hVZ (by
        intro heq
        obtain ⟨l, hl, v, hv, hne⟩ := hnt
        apply hne
        rw [heq]
        exact V.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp (hL hl)).1 v).mp hv)
          (V.inv_mem hv))
      norm₀ := hL.trans inf_le_right
      norm₁ := hL.trans inf_le_left
      normal := hnormalZV
      min := fun N hZN hNV hLN => hirr N hZN hNV hLN }
  obtain ⟨l₀, hl₀, v₀, hv₀, hne₀⟩ := hnt
  let l₀' : ↥L := ⟨l₀, hl₀⟩
  let v₀' : ↥V := ⟨v₀, hv₀⟩
  obtain ⟨W, hWadd, hWmod, hWfin, ⟨s⟩⟩ := exists_secRep hsecHyp
  letI : AddCommGroup W := hWadd
  letI : Module (ZMod 2) W := hWmod
  letI : Finite W := hWfin
  have hfix : s.ρ l₀' (s.cl v₀') ≠ s.cl v₀' := by
    intro h
    exact hne₀ ((SecRep.fix_iff hsecHyp s l₀' v₀').mp h)
  have hkerP : CFSG.pCore 2 ↥L ≤ s.ρ.ker :=
    CFSG.Quasithin.St84.pCore_le_secRep_ker s hsecHyp hChief
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨eSz⟩ := hSz
  let e : oTwoQuot ↥L ≃* CFSG.Blueprint.suzukiGroup a K :=
    eSz.trans (suzukiGroupEquivSz a K hK).symm
  let q : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let bar : oTwoQuot ↥L →* (W ≃ₗ[ZMod 2] W) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) s.ρ hkerP
  let Φ : ↥(CFSG.Blueprint.suzukiGroup a K) →* (W ≃ₗ[ZMod 2] W) :=
    bar.comp e.symm.toMonoidHom
  let ρ : Representation (ZMod 2) ↥(CFSG.Blueprint.suzukiGroup a K) W :=
    { toFun := fun g => (Φ g).toLinearMap
      map_one' := by rw [map_one]; rfl
      map_mul' := fun g h => by rw [map_mul]; rfl }
  have hρ_mk : ∀ l : ↥L, ρ (e (q l)) = (s.ρ l).toLinearMap := by
    intro l
    rw [show ρ (e (q l)) = (Φ (e (q l))).toLinearMap from rfl]
    simp [Φ, bar, q, QuotientGroup.lift_mk']
  haveI : Nontrivial W := ⟨s.ρ l₀' (s.cl v₀'), s.cl v₀', hfix⟩
  have hirrρ : ρ.IsIrreducible := by
    haveI : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⊥, ⊤, ?_⟩
      intro h
      exact bot_ne_top (α := Submodule (ZMod 2) W)
        (congrArg Subrepresentation.toSubmodule h)
    refine { eq_bot_or_eq_top := fun U => ?_ }
    have hS : ∀ l : ↥L, ∀ w ∈ U.toSubmodule, s.ρ l w ∈ U.toSubmodule := by
      intro l w hw
      have h1 := U.apply_mem_toSubmodule (e (q l)) hw
      rwa [hρ_mk l] at h1
    rcases SecRep.irreducible hChief hsecHyp s U.toSubmodule hS with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  letI : Fact ρ.IsIrreducible := ⟨hirrρ⟩
  have hntρ : ∃ g, ρ g ≠ 1 := by
    by_contra h
    push Not at h
    have hbar : s.ρ l₀' = 1 := by
      refine LinearEquiv.ext fun w => ?_
      have h1 : (s.ρ l₀').toLinearMap w = w := by
        rw [← hρ_mk l₀']
        exact LinearMap.congr_fun (h (e (q l₀'))) w
      simpa using h1
    exact hfix (by rw [hbar]; rfl)
  have hmain :=
    CFSG.RankThree.GF2n.Tim81.Sec2.isSzNatural_or_le_card (a := a) (K := K) hK ρ hntρ
  have hker : s.cls.ker = Z.subgroupOf V := by
    ext n
    rw [MonoidHom.mem_ker, s.ker n, Subgroup.mem_subgroupOf]
  haveI hNZV : (Z.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVZ).mpr hnormalZV
  have hquotW : Nat.card (↥V ⧸ Z.subgroupOf V) = Nat.card W := by
    have eW : (↥V ⧸ Z.subgroupOf V) ≃* Multiplicative W :=
      (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective s.cls s.surj)
    exact (Nat.card_congr eW.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
  have hcardW : Nat.card W = Z.relIndex V := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, hquotW]
  have hbound : 2 ^ (4 * (2 * a + 1)) ≤ Nat.card W := by
    rcases hmain with hnat | hbig
    · obtain ⟨-, φ, -⟩ := hnat
      have hWK : Nat.card W = Nat.card (Fin 4 → K) := Nat.card_congr φ.toEquiv
      have hK4 : Nat.card (Fin 4 → K) = 2 ^ (4 * (2 * a + 1)) := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin, hK,
          ← pow_mul]
        congr 1
        ring
      rw [hWK, hK4]
    · exact le_trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith)) hbig
  rwa [hcardW] at hbound

private theorem false_of_trivial_on_quotients_of_sz
    {V Z W L : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ Z)
    (hWV : W ≤ V)
    (htrivW : ∀ l ∈ L, ∀ w ∈ W, ⁅l, w⁆ ∈ Z)
    (htrivV : ∀ l ∈ L, ∀ v ∈ V, ⁅l, v⁆ ∈ W)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) : False := by
  classical
  obtain ⟨N, hNnormal, hNmem⟩ := exists_trivSubgroup hsec hL
  have hpCoreN : CFSG.pCore 2 ↥L ≤ N := by
    intro p hp
    exact (hNmem p).mpr fun v hv =>
      hQ (p : G) (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩) v hv
  have hsqN : ∀ x : ↥L, x ^ 2 ∈ N := by
    intro x
    exact (hNmem _).mpr fun v hv => by
      have hwW : ⁅(x : G), v⁆ ∈ W := htrivV (x : G) x.2 v hv
      have hw2Z : ⁅(x : G), v⁆ ^ 2 ∈ Z := hsec.2.2 _ (hWV hwW)
      have hxwZ : ⁅(x : G), ⁅(x : G), v⁆⁆ ∈ Z := htrivW (x : G) x.2 _ hwW
      have e : ⁅((x ^ 2 : ↥L) : G), v⁆ =
          ⁅(x : G), ⁅(x : G), v⁆⁆ * ⁅(x : G), v⁆ ^ 2 := by
        simp only [Subgroup.coe_pow, Subgroup.coe_mul, commutatorElement_def, pow_two]
        group
      rw [e]
      exact Z.mul_mem hxwZ hw2Z
  let X := oTwoQuot ↥L
  let q : ↥L →* X := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hsimple : IsSimpleGroup X := by
    haveI : IsSimpleGroup ↥(Sz a) := isSimpleGroup_sz ha
    exact (Classical.choice hSz).isSimpleGroup
  haveI hNmap : (N.map q).Normal :=
    hNnormal.map q (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map q) with hbot | htop
  · have hsqX : ∀ y : X, y ^ 2 = 1 := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
      change (q x) ^ 2 = 1
      have hx2 : q (x ^ 2) ∈ N.map q := Subgroup.mem_map.mpr ⟨x ^ 2, hsqN x, rfl⟩
      rw [hbot] at hx2
      have h1 : q (x ^ 2) = 1 := Subgroup.mem_bot.mp hx2
      rwa [map_pow] at h1
    have hcomm : IsMulCommutative X :=
      CFSG.BenderSuzuki.isMulCommutative_of_forall_sq_one hsqX
    obtain ⟨e⟩ := hSz
    exact not_isMulCommutative_sz ha (e.surjective.isMulCommutative hcomm)
  · have hNtop : N = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hxmap : q x ∈ N.map q := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnq⟩ := Subgroup.mem_map.mp hxmap
      have hmem : n⁻¹ * x ∈ CFSG.pCore 2 ↥L := by
        rw [← QuotientGroup.eq_one_iff]
        change q (n⁻¹ * x) = 1
        rw [map_mul, map_inv, hnq, inv_mul_cancel]
      simpa using N.mul_mem hn (hpCoreN hmem)
    obtain ⟨l, hl, v, hv, hne⟩ := hnt
    exact hne ((hNmem ⟨l, hl⟩).mp (by rw [hNtop]; exact Subgroup.mem_top _) v hv)

private theorem two_pow_le_relIndex_aux_of_sz
    {V Z L : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ Z)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) :
    2 ^ (4 * (2 * a + 1)) ≤ Z.relIndex V := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (V Z : Subgroup G), IsElemSec Z V →
    L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G) →
    (∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ Z) →
    (∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) → Z.relIndex V = n →
    2 ^ (4 * (2 * a + 1)) ≤ Z.relIndex V
  have key : ∀ n, P n := fun n =>
    Nat.strongRecOn (motive := P) n (fun n ih => by
      intro V Z hsec hL hQ hnt hrel
      by_cases hchief : ∀ W : Subgroup G, Z ≤ W → W ≤ V →
          L ≤ Subgroup.normalizer (W : Set G) → W = Z ∨ W = V
      · exact two_pow_le_relIndex_of_irreducible_of_sz ha hSz hsec hL hchief hnt
      · push Not at hchief
        obtain ⟨W, hZW, hWV, hLW, hWneZ, hWneV⟩ := hchief
        have hrelmul : Z.relIndex V = Z.relIndex W * W.relIndex V :=
          (Subgroup.relIndex_mul_relIndex Z W V hZW hWV).symm
        have hrelZW_pos : 0 < Z.relIndex W := by
          rw [Subgroup.relIndex, Subgroup.index]
          exact Nat.card_pos
        have hrelWV_pos : 0 < W.relIndex V := by
          rw [Subgroup.relIndex, Subgroup.index]
          exact Nat.card_pos
        have hrelZW_gt1 : 1 < Z.relIndex W := by
          have hne1 : Z.relIndex W ≠ 1 := fun h =>
            hWneZ (le_antisymm (Subgroup.relIndex_eq_one.mp h) hZW)
          omega
        have hrelWV_gt1 : 1 < W.relIndex V := by
          have hne1 : W.relIndex V ≠ 1 := fun h =>
            hWneV (le_antisymm hWV (Subgroup.relIndex_eq_one.mp h))
          omega
        have hsec_ZW : IsElemSec Z W :=
          ⟨hZW, (Subgroup.commutator_mono hWV hWV).trans hsec.2.1,
            fun e he => hsec.2.2 e (hWV he)⟩
        have hsec_WV : IsElemSec W V :=
          ⟨hWV, hsec.2.1.trans hZW, fun e he => hZW (hsec.2.2 e he)⟩
        have hL_ZW : L ≤ Subgroup.normalizer (W : Set G) ⊓
            Subgroup.normalizer (Z : Set G) :=
          le_inf hLW (hL.trans inf_le_right)
        have hL_VW : L ≤ Subgroup.normalizer (V : Set G) ⊓
            Subgroup.normalizer (W : Set G) :=
          le_inf (hL.trans inf_le_left) hLW
        have hQ_ZW : ∀ p ∈ pCoreOf 2 L, ∀ w ∈ W, ⁅p, w⁆ ∈ Z :=
          fun p hp w hw => hQ p hp w (hWV hw)
        have hQ_VW : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ W :=
          fun p hp v hv => hZW (hQ p hp v hv)
        by_cases hntW : ∃ l ∈ L, ∃ w ∈ W, ⁅l, w⁆ ∉ Z
        · have hlt : Z.relIndex W < n := by
            rw [← hrel, hrelmul]
            exact lt_mul_of_one_lt_right hrelZW_pos hrelWV_gt1
          have hIH : 2 ^ (4 * (2 * a + 1)) ≤ Z.relIndex W :=
            ih (Z.relIndex W) hlt W Z hsec_ZW hL_ZW hQ_ZW hntW rfl
          rw [hrelmul]
          exact hIH.trans (Nat.le_mul_of_pos_right _ hrelWV_pos)
        · push Not at hntW
          by_cases hntV : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ W
          · have hlt : W.relIndex V < n := by
              rw [← hrel, hrelmul]
              exact lt_mul_of_one_lt_left hrelWV_pos hrelZW_gt1
            have hIH : 2 ^ (4 * (2 * a + 1)) ≤ W.relIndex V :=
              ih (W.relIndex V) hlt V W hsec_WV hL_VW hQ_VW hntV rfl
            rw [hrelmul]
            exact hIH.trans (Nat.le_mul_of_pos_left _ hrelZW_pos)
          · push Not at hntV
            exfalso
            exact false_of_trivial_on_quotients_of_sz ha hSz hsec hL hQ hWV hntW hntV hnt)
  exact key (Z.relIndex V) V Z hsec hL hQ hnt rfl

section Vertex

variable {L T : Subgroup G}

theorem commutator_mem_of_quadratic_of_sz {V Z : Subgroup G}
    {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ Z)
    (hquad : ∀ t ∈ T, ∀ v ∈ V, ⁅t, ⁅t, v⁆⁆ ∈ Z) : ∀ l ∈ L, ∀ v ∈ V, ⁅l, v⁆ ∈ Z := by
  classical
  obtain ⟨N, hNnormal, hNmem⟩ := exists_trivSubgroup hsec hL
  have hpCoreN : CFSG.pCore 2 ↥L ≤ N := by
    intro p hp
    exact (hNmem p).mpr fun v hv =>
      hQ (p : G) (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩) v hv
  have hsimple : IsSimpleGroup (oTwoQuot ↥L) := by
    haveI : IsSimpleGroup ↥(Sz a) := isSimpleGroup_sz ha
    exact (Classical.choice hSz).isSimpleGroup
  obtain ⟨t, htT, htsq⟩ := exists_sq_map_ne_one_of_sz ha hSz hT
  have ht2p : t ^ 2 ∉ CFSG.pCore 2 ↥L := by
    intro hmem
    apply htsq
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (t ^ 2)).mpr hmem
  have ht2N : t ^ 2 ∈ N := by
    refine (hNmem _).mpr fun v hv => ?_
    have hcommV : ⁅(t : G), v⁆ ∈ V := by
      have hconj : (t : G) * v * (t : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp (hL t.2)).1 v).mp hv
      rw [commutatorElement_def]
      exact V.mul_mem hconj (V.inv_mem hv)
    have hq := hquad (t : G) htT v hv
    have hsq : ⁅(t : G), v⁆ ^ 2 ∈ Z := hsec.2.2 _ hcommV
    have e : ⁅((t ^ 2 : ↥L) : G), v⁆ =
        ⁅(t : G), ⁅(t : G), v⁆⁆ * ⁅(t : G), v⁆ ^ 2 := by
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, commutatorElement_def, pow_two]
      group
    rw [e]
    exact Z.mul_mem hq hsq
  have hmapne : N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≠ ⊥ := by
    intro hbot
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (t ^ 2) ∈
        N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      Subgroup.mem_map.mpr ⟨t ^ 2, ht2N, rfl⟩
    rw [hbot] at hmem
    exact ht2p ((QuotientGroup.eq_one_iff (t ^ 2)).mp (Subgroup.mem_bot.mp hmem))
  have hNtop := eq_top_of_pCore_le_of_map_ne_bot hNnormal hpCoreN hsimple hmapne
  intro l hl v hv
  exact (hNmem ⟨l, hl⟩).mp (by rw [hNtop]; exact Subgroup.mem_top _) v hv

theorem two_pow_le_relIndex_of_nontrivial_of_sz
    {V Z : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ Z)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) : 2 ^ (4 * (2 * a + 1)) ≤ Z.relIndex V :=
  two_pow_le_relIndex_aux_of_sz ha hSz hsec hL hQ hnt

end Vertex

end CFSG.Quasithin.Stroth

end
