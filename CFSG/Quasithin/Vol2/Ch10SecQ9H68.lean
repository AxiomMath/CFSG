module

public import CFSG.Quasithin.Vol2.Ch10SecKITa
public import CFSG.Quasithin.H13.LocDblCComp
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Sporadic.J4.QT2LocX0CentMain
public import CFSG.Sporadic.J4.QT2LocOrder
public import CFSG.Sporadic.J4.QT2LocX0Main
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.QuasithinUnique
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

namespace J4Block

theorem subsingleton_of_perfect {R : Type*} [Group R] [hs : Group.IsSolvable R]
    (hR : ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ = ⊤) : Subsingleton R := by
  obtain ⟨n, hn⟩ := hs.solvable
  have h : ∀ k, derivedSeries R k = ⊤ := by
    intro k
    induction k with
    | zero => exact derivedSeries_zero R
    | succ k ih => rw [derivedSeries_succ, ih, hR]
  rw [h n] at hn
  constructor
  intro a b
  have ha : a ∈ (⊥ : Subgroup R) := hn ▸ Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup R) := hn ▸ Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  rw [ha, hb]

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_dvd_of_normal {Y : Type} [Group Y] [Finite Y] {B : Subgroup Y} (hperf : ⁅B, B⁆ = B)
    (W : Subgroup ↥B) [W.Normal] (hW : Nat.card ↥W ∣ 16) (e : ↥B ⧸ W ≃* alternatingGroup (Fin 5))
    {N : Subgroup Y} (hNB : N ≤ B) (hBN : B ≤ Subgroup.normalizer (N : Set Y)) (hne : N ≠ B) :
    Nat.card ↥N ∣ 16 := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := Vol2Native.A312L.Seven.alt5_simple
  have : IsSimpleGroup (↥B ⧸ W) := e.isSimpleGroup
  have hN' : (N.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNB).mpr hBN
  have hcN : Nat.card ↥(N.subgroupOf B) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv
  have hmap : ((N.subgroupOf B).map (QuotientGroup.mk' W)).Normal :=
    hN'.map _ (QuotientGroup.mk'_surjective W)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf B).map (QuotientGroup.mk' W)) with
    h | h
  · have hle : N.subgroupOf B ≤ W := by
      intro n hn
      have h1 : QuotientGroup.mk' W n ∈ (N.subgroupOf B).map (QuotientGroup.mk' W) := ⟨n, hn, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff n).mp h1
    rw [← hcN]
    exact (Subgroup.card_dvd_of_le hle).trans hW
  · exfalso
    apply hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsurj : Function.Surjective ((QuotientGroup.mk' (N.subgroupOf B)).comp W.subtype) := by
      intro q
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf B) q
      have hb : QuotientGroup.mk' W b ∈ (N.subgroupOf B).map (QuotientGroup.mk' W) := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnb⟩ := hb
      have hw : n⁻¹ * b ∈ W := QuotientGroup.eq.mp hnb
      refine ⟨⟨n⁻¹ * b, hw⟩, ?_⟩
      show QuotientGroup.mk' (N.subgroupOf B) (n⁻¹ * b) = QuotientGroup.mk' (N.subgroupOf B) b
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have he : (n⁻¹ * b)⁻¹ * b = b⁻¹ * n * b⁻¹⁻¹ := by group
      rw [he]
      exact hN'.conj_mem n hn b⁻¹
    have hQ : Nat.card (↥B ⧸ N.subgroupOf B) ∣ 2 ^ 4 :=
      (Subgroup.card_dvd_of_surjective hsurj).trans (hW.trans (by norm_num))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hQ
    have hp : IsPGroup 2 (↥B ⧸ N.subgroupOf B) := IsPGroup.of_card hj
    have : Group.IsNilpotent (↥B ⧸ N.subgroupOf B) := hp.isNilpotent
    have hBtop : ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ = ⊤ := by
      apply Subgroup.map_injective B.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperf]
    have hQtop : ⁅(⊤ : Subgroup (↥B ⧸ N.subgroupOf B)), (⊤ : Subgroup (↥B ⧸ N.subgroupOf B))⁆ =
        ⊤ := by
      rw [← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (N.subgroupOf B)),
        ← Subgroup.map_commutator, hBtop]
    have hsub := subsingleton_of_perfect hQtop
    have htop : N.subgroupOf B = ⊤ := by
      rw [eq_top_iff]
      intro b _
      exact (QuotientGroup.eq_one_iff b).mp (Subsingleton.elim _ _)
    exact le_antisymm hNB (Subgroup.subgroupOf_eq_top.mp htop)

theorem le_normalizer_of_lFamily {Y : Type} [Group Y] [Finite Y] (h25 : ¬ 25 ∣ Nat.card Y)
    {T B : Subgroup Y} (hB : B ∈ lFamily T) (hB5 : 5 ∣ Nat.card ↥B)
    (hBn : ∀ N : Subgroup Y, N ≤ B → B ≤ Subgroup.normalizer (N : Set Y) → N ≠ B →
      Nat.card ↥N ∣ 16) :
    T ≤ Subgroup.normalizer (B : Set Y) := by
  intro t ht
  by_contra hnt
  have hBX : B ∈ cComp (B ⊔ T) := hB
  have htX : t ∈ B ⊔ T := (le_sup_right : T ≤ B ⊔ T) ht
  have hXt : (B ⊔ T).map (MulAut.conj t).toMonoidHom = B ⊔ T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htX)
  set Bt := B.map (MulAut.conj t).toMonoidHom with hBt
  have hBtX : Bt ∈ cComp (B ⊔ T) := by
    have h := cComp_map_mulEquiv (MulAut.conj t) hBX
    rwa [hXt] at h
  have hne : Bt ≠ B := fun h => hnt (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hn₁ : Bt ≤ Subgroup.normalizer (B : Set Y) := H13.LocDbl.le_normalizer_of_mem_cComp hBX hBtX
  have hn₂ : B ≤ Subgroup.normalizer (Bt : Set Y) := H13.LocDbl.le_normalizer_of_mem_cComp hBtX hBX
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hn₁
  have hcBt : Nat.card ↥Bt = Nat.card ↥B := Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hD : ¬ 5 ∣ Nat.card ↥(B ⊓ Bt) := by
    intro h5
    have hD16 := hBn (B ⊓ Bt) inf_le_left
      (fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hb, hn₂ hb⟩)
      (fun h => hne (Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp h) (le_of_eq hcBt)).symm)
    have h516 : (5 : ℕ) ∣ 16 := h5.trans hD16
    norm_num at h516
  have h25' : 25 ∣ Nat.card ↥(B ⊔ Bt) := by
    have h1 : 5 ^ 2 ∣ Nat.card ↥(B ⊔ Bt) * Nat.card ↥(B ⊓ Bt) := by
      rw [hprod, hcBt, pow_two]
      exact Nat.mul_dvd_mul hB5 hB5
    have hcop : Nat.Coprime (5 ^ 2) (Nat.card ↥(B ⊓ Bt)) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hD)
    have h2 := hcop.dvd_of_dvd_mul_right h1
    norm_num at h2
    exact h2
  exact h25 (h25'.trans (Subgroup.card_subgroup_dvd_card _))

theorem card_centralizer_le {G : Type} [Group G] [Finite G] (h25 : ¬ 25 ∣ Nat.card G)
    {x y : G} (hx : orderOf x = 5) (hy : orderOf y = 5) :
    Nat.card ↥(Subgroup.centralizer {y}) ≤ Nat.card ↥(Subgroup.centralizer {x}) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hidx : ∀ z : G, orderOf z = 5 → ¬ 5 ∣ (Subgroup.zpowers z).index := by
    intro z hz h5
    apply h25
    rw [← (Subgroup.zpowers z).index_mul_card, Nat.card_zpowers, hz]
    exact Nat.mul_dvd_mul_right h5 5
  have hp : ∀ z : G, orderOf z = 5 → IsPGroup 5 ↥(Subgroup.zpowers z) := fun z hz =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G ((hp y hy).toSylow (hidx y hy))
    ((hp x hx).toSylow (hidx x hx))
  have h' : (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x := by
    have h := congrArg (fun P : Sylow 5 G => (P : Subgroup G)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    exact h
  have hxm : x ∈ (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom := by
    rw [h']
    exact Subgroup.mem_zpowers x
  obtain ⟨w, hw, hwx⟩ := hxm
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hle : (Subgroup.centralizer {y}).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer {x} := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z * y = y * z := Subgroup.mem_centralizer_singleton_iff.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff, ← hwx]
    exact (((show Commute z y from hz').zpow_right k).map (MulAut.conj g).toMonoidHom).eq
  calc Nat.card ↥(Subgroup.centralizer {y})
      = Nat.card ↥((Subgroup.centralizer {y}).map (MulAut.conj g).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
    _ ≤ Nat.card ↥(Subgroup.centralizer {x}) := Subgroup.card_le_of_le hle

theorem false_of_block {Y : Type} [Group Y] [Finite Y] (h25 : ¬ 25 ∣ Nat.card Y)
    (hcent : ∀ x : Y, orderOf x = 5 → Nat.card ↥(Subgroup.centralizer {x}) = 6720)
    {T B : Subgroup Y} (hT : 2 ^ 21 ∣ Nat.card ↥T) (hT2 : IsPGroup 2 ↥T) (hB : B ∈ lFamily T)
    (W : Subgroup ↥B) [W.Normal] (hW : Nat.card ↥W ∣ 16)
    (e : ↥B ⧸ W ≃* alternatingGroup (Fin 5)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hperf : ⁅B, B⁆ = B := perfect_of_mem_cComp (show B ∈ cComp (B ⊔ T) from hB)
  have hcB : Nat.card ↥B = 60 * Nat.card ↥W := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup W, Nat.card_congr e.toEquiv, card_alt5]
  have hB5 : 5 ∣ Nat.card ↥B := by
    rw [hcB]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hBle : Nat.card ↥B ≤ 960 := by
    have := Nat.le_of_dvd (by norm_num) hW
    omega
  have hTN : T ≤ Subgroup.normalizer (B : Set Y) :=
    le_normalizer_of_lFamily h25 hB hB5 fun N hNB hBN hne =>
      card_dvd_of_normal hperf W hW e hNB hBN hne
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 5 hB5
  have hx5 : orderOf (x : Y) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  let _ : MulAction ↥T ↥B :=
    MulAction.compHom ↥B ((B.normalizerMonoidHom).comp (Subgroup.inclusion hTN))
  have hsmul : ∀ (t : ↥T) (b : ↥B), ((t • b : ↥B) : Y) = (t : Y) * b * (t : Y)⁻¹ :=
    fun _ _ => rfl
  have hob : (MulAction.orbit ↥T x).ncard ≤ Nat.card ↥B := Set.ncard_le_card _
  have hSc : Nat.card ↥(MulAction.stabilizer ↥T x) ∣ 6720 := by
    rw [← Subgroup.card_map_of_injective T.subtype_injective, ← hcent _ hx5]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (s : Y) * x * (s : Y)⁻¹ = x := by
      rw [← hsmul]
      exact congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hs)
    show (s : Y) * x = x * s
    calc (s : Y) * x = (s : Y) * x * (s : Y)⁻¹ * s := by group
      _ = x * s := by rw [h1]
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hT2.to_subgroup (MulAction.stabilizer ↥T x))
  have hj6 : j ≤ 6 := by
    by_contra hj6
    have h7 : 2 ^ 7 ∣ 6720 := (Nat.pow_dvd_pow 2 (by omega)).trans (hj ▸ hSc)
    norm_num at h7
  have hS : Nat.card ↥(MulAction.stabilizer ↥T x) ≤ 64 := by
    rw [hj]
    calc 2 ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hj6
      _ = 64 := by norm_num
  have htot : Nat.card ↥T = (MulAction.orbit ↥T x).ncard *
      Nat.card ↥(MulAction.stabilizer ↥T x) := by
    rw [← MulAction.index_stabilizer, Subgroup.index_mul_card]
  have h21 : 2 ^ 21 ≤ Nat.card ↥T := Nat.le_of_dvd Nat.card_pos hT
  have hle : Nat.card ↥T ≤ 960 * 64 := by
    rw [htot]
    exact Nat.mul_le_mul (hob.trans hBle) hS
  omega

end J4Block

theorem kgJ4NoA5Block_holds :
    KGJ4NoA5Block := by
  intro Y _ _ hY T hT B hB
  obtain ⟨e⟩ : Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4) := hY
  obtain ⟨e'⟩ : Nonempty (Y ≃* ↥CFSG.Sporadic.J4.J) :=
    ⟨(e : Y ≃* CFSG.Blueprint.NativeSporadic.J4).trans
      (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)⟩
  have hcY : Nat.card Y = Nat.card ↥CFSG.Sporadic.J4.J := Nat.card_congr e'.toEquiv
  have h25 : ¬ 25 ∣ Nat.card Y := hcY ▸ CFSG.Sporadic.J4.QT2.not_twentyfive_dvd_card_J
  have hξ : orderOf (e'.symm CFSG.Sporadic.J4.QT2.fiveElt) = 5 := by
    rw [MulEquiv.orderOf_eq]
    exact CFSG.Sporadic.J4.QT2.orderOf_fiveElt_J4
  have hcξ : Nat.card ↥(Subgroup.centralizer {e'.symm CFSG.Sporadic.J4.QT2.fiveElt}) = 6720 := by
    rw [← CFSG.Sporadic.J4.QT2.card_centralizer_fiveElt CFSG.Sporadic.J4.j4Facts]
    refine Nat.card_congr (e'.toEquiv.subtypeEquiv fun z => ?_)
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    show z * e'.symm _ = e'.symm _ * z ↔ e' z * _ = _ * e' z
    constructor
    · intro h
      have h1 := congrArg e' h
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
      exact h1
    · intro h
      apply e'.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h
  have hcent : ∀ x : Y, orderOf x = 5 → Nat.card ↥(Subgroup.centralizer {x}) = 6720 :=
    fun x hx => le_antisymm (hcξ ▸ J4Block.card_centralizer_le h25 hξ hx)
      (hcξ ▸ J4Block.card_centralizer_le h25 hx hξ)
  have hT21 : 2 ^ 21 ∣ Nat.card ↥T := by
    have hidx : ¬ 2 ∣ T.index := by
      have h := hT.2.2
      rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
    have hY21 : 2 ^ 21 ∣ Nat.card Y := by
      rw [hcY, CFSG.Sporadic.J4.card_J CFSG.Sporadic.J4.j4Facts]
      norm_num
    rw [← T.card_mul_index] at hY21
    exact (Nat.Coprime.pow_left 21 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      hidx)).dvd_of_dvd_mul_right hY21
  refine ⟨fun hA => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · obtain ⟨eA⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 5)) := hA
    exact J4Block.false_of_block h25 hcent hT21 hT.2.1 hB ⊥ (by rw [Subgroup.card_bot]; norm_num)
      (QuotientGroup.quotientBot.trans eA)
  · obtain ⟨eA⟩ : Nonempty (ModO2 B ≃* alternatingGroup (Fin 5)) := h2
    obtain ⟨eV⟩ : Nonempty (↥(CFSG.pCore 2 ↥B) ≃* Multiplicative (Fin 4 → ZMod 2)) := h1
    have hV : Nat.card ↥(CFSG.pCore 2 ↥B) = 16 := by
      rw [Nat.card_congr eV.toEquiv, Nat.card_eq_fintype_card]
      rfl
    exact J4Block.false_of_block h25 hcent hT21 hT.2.1 hB (CFSG.pCore 2 ↥B) (by rw [hV]) eA

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
