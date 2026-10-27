module

public import CFSG.RankThree.GF2n.Tim81.Sec4.CentralTIBasic
public import CFSG.RankThree.GF2n.Tim81.Sec4.SL2Borel
public import CFSG.Timmesfeld.Bridge.OddLocalRootCore
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.RankThree.GF2n.Tim81.CentralTI

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim81.Sec4 CFSG.ABGLocalTools
  CFSG.SignalizerFunctorTheorem.McBride
open scoped MatrixGroups commutatorElement CharTwo

variable {Y : Type*} [Group Y] [Finite Y] {T Z : Subgroup Y} [Z.Normal]

private theorem not_isMulCommutative_sl2 {F : Type} [Field F] [CharP F 2] :
    ¬ IsMulCommutative (SL(2, F)) := by
  intro h
  haveI := h
  have htop : Subgroup.center (SL(2, F)) = ⊤ := Subgroup.center_eq_top
  rw [center_sl2_eq_bot] at htop
  haveI : Subsingleton (SL(2, F)) := by
    refine ⟨fun a b => ?_⟩
    have ha : a = 1 := Subgroup.mem_bot.mp (htop.symm ▸ Subgroup.mem_top a)
    have hb : b = 1 := Subgroup.mem_bot.mp (htop.symm ▸ Subgroup.mem_top b)
    rw [ha, hb]
  exact utriElt_ne_one (one_ne_zero : (1 : F) ≠ 0) (Subsingleton.elim _ _)

private theorem sl2_T'_data (hTZ : T ⊓ Z = ⊥) (hTp : IsPGroup 2 T) (hTne : T ≠ ⊥)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)))
    (hZ : Z ≤ Subgroup.center Y) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (e : Y ⧸ Z ≃* SL(2, F)) :
    ∃ (T' : Subgroup SL(2, F)) (x : SL(2, F)),
      IsPGroup 2 T' ∧ T' ≠ ⊥ ∧
      (∀ g : SL(2, F), conjSubgroup g T' ≤
        Subgroup.normalizer (T' : Set SL(2, F)) → conjSubgroup g T' = T') ∧
      T' = (T.map (QuotientGroup.mk' Z)).map e.toMonoidHom ∧
      T' = conjSubgroup x (utri F) ∧ Nat.card T' = Nat.card F := by

  obtain ⟨hTpbar, hTnebar⟩ := isPGroup_map_mk'_and_ne_bot (Z := Z) hTp hTZ hTne
  set T' : Subgroup SL(2, F) :=
    (T.map (QuotientGroup.mk' Z)).map e.toMonoidHom with hT'
  have hT'p : IsPGroup 2 T' := hTpbar.map e.toMonoidHom
  have hT'ne : T' ≠ ⊥ := by
    obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hTnebar
    intro hbot
    have hmem : e x ∈ T' := by
      rw [hT']
      exact Subgroup.mem_map_of_mem e.toMonoidHom x.2
    rw [hbot] at hmem
    exact hx (Subtype.ext (e.injective (by simpa using Subgroup.mem_bot.1 hmem)))
  have hT'wc : ∀ g : SL(2, F), conjSubgroup g T' ≤
      Subgroup.normalizer (T' : Set SL(2, F)) → conjSubgroup g T' = T' :=
    weaklyClosed_map_mulEquiv e (weaklyClosed_map_mk' hZ hwc)
  obtain ⟨x, hx⟩ := exists_conj_eq_utri hT'p hT'ne hT'wc
  obtain ⟨D, hDle, hDcard, -, hDfpf⟩ := exists_frobeniusComplement hT'p hT'ne hT'wc
  have hcardT' : Nat.card T' = Nat.card F := by
    rw [hx, card_conjSubgroup, card_utri]
  exact ⟨T', x, hT'p, hT'ne, hT'wc, hT', hx, hcardT'⟩

private theorem sl2_lift_torus (hTZ : T ⊓ Z = ⊥)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)))
    (hZ : Z ≤ Subgroup.center Y) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : 4 ≤ Fintype.card F) (e : Y ⧸ Z ≃* SL(2, F))
    {T' : Subgroup SL(2, F)} {x : SL(2, F)}
    (hT'def : T' = (T.map (QuotientGroup.mk' Z)).map e.toMonoidHom)
    (hT'p : IsPGroup 2 T') (hT'ne : T' ≠ ⊥)
    (hT'wc : ∀ g : SL(2, F), conjSubgroup g T' ≤
      Subgroup.normalizer (T' : Set SL(2, F)) → conjSubgroup g T' = T')
    (hx : T' = conjSubgroup x (utri F)) :
    ∃ d : Y, d ∈ Subgroup.normalizer (T : Set Y) ∧
      (∀ y ∈ T, d * y * d⁻¹ = y → y = 1) := by

  obtain ⟨D, hDle, hDcard, -, hDfpf⟩ := exists_frobeniusComplement hT'p hT'ne hT'wc
  have hcardT' : Nat.card T' = Nat.card F := by
    rw [hx, card_conjSubgroup, card_utri]
  have hFcard : 4 ≤ Nat.card F := by rw [Nat.card_eq_fintype_card]; exact hF
  have hcardD : Nat.card D = Nat.card F - 1 := by rw [hDcard, hcardT']
  have hDne : D ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card D = 1 := by rw [hbot]; simp
    rw [h1] at hcardD
    omega
  obtain ⟨d0, hd0ne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hd0ne' : (d0 : SL(2, F)) ≠ 1 := fun h => hd0ne (Subtype.ext h)
  set dbar : Y ⧸ Z := e.symm (d0 : SL(2, F)) with hdbar
  have hdbar_e : e dbar = (d0 : SL(2, F)) := e.apply_symm_apply _
  have hdbarN : dbar ∈ Subgroup.normalizer
      ((T.map (QuotientGroup.mk' Z)) : Set (Y ⧸ Z)) := by
    rw [mem_normalizer_iff_conjSubgroup_eq]
    have hconj0 : conjSubgroup (d0 : SL(2, F)) T' = T' :=
      mem_normalizer_iff_conjSubgroup_eq.1 (hDle d0.2)
    rw [hT'def] at hconj0
    have hmap : conjSubgroup (e dbar) ((T.map (QuotientGroup.mk' Z)).map e.toMonoidHom) =
        (conjSubgroup dbar (T.map (QuotientGroup.mk' Z))).map e.toMonoidHom :=
      (map_conjSubgroup e.toMonoidHom dbar (T.map (QuotientGroup.mk' Z))).symm
    rw [hdbar_e] at hmap
    have h2 : (conjSubgroup dbar (T.map (QuotientGroup.mk' Z))).map e.toMonoidHom =
        (T.map (QuotientGroup.mk' Z)).map e.toMonoidHom := by rw [← hmap, hconj0]
    exact Subgroup.map_injective e.injective h2
  have hfpfTbar : ∀ y ∈ T.map (QuotientGroup.mk' Z), dbar * y * dbar⁻¹ = y → y = 1 := by
    intro y hy hfix
    have hy' : e y ∈ T' := by
      rw [hT'def]
      exact Subgroup.mem_map_of_mem _ hy
    have hfix' : (d0 : SL(2, F)) * e y * (d0 : SL(2, F))⁻¹ = e y := by
      have h := congrArg e hfix
      rw [map_mul, map_mul, map_inv, hdbar_e] at h
      exact h
    exact e.injective (by rw [hDfpf d0 d0.2 hd0ne' (e y) hy' hfix', map_one])
  obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective Z dbar
  obtain ⟨hdN, hfpfT⟩ :=
    normalize_and_fixedPointFree_of_map hZ hTZ hwc hd hdbarN hfpfTbar
  exact ⟨d, hdN, hfpfT⟩

private theorem sl2_center_eq_center (hZ : Z ≤ Subgroup.center Y) {F : Type} [Field F]
    [Fintype F] [CharP F 2] (e : Y ⧸ Z ≃* SL(2, F)) :
    Z = Subgroup.center Y := by
  have hcenterq : Subgroup.center (Y ⧸ Z) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_center_iff] at hy
    have hy' : e y ∈ Subgroup.center (SL(2, F)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨w, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hy w]
    rw [center_sl2_eq_bot, Subgroup.mem_bot] at hy'
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hy', map_one])
  have hZc : Z = Subgroup.center Y := center_eq_of_center_quotient_eq_bot hZ hcenterq
  exact hZc

private theorem sl2_N_data (hZ : Z ≤ Subgroup.center Y) :
    ∃ N : Subgroup Y, N ≤ Z ∧ IsPGroup 2 N ∧ N.Normal ∧ IsSylowOf 2 N Z := by
  obtain ⟨PZ⟩ := (inferInstance : Nonempty (Sylow 2 ↥Z))
  set N : Subgroup Y := (PZ : Subgroup ↥Z).map Z.subtype with hN
  have hNle : N ≤ Z := Subgroup.map_subtype_le _
  have hNp : IsPGroup 2 N := PZ.isPGroup'.map Z.subtype
  have hNnormal : N.Normal := Subgroup.normal_of_le_center (hNle.trans hZ)
  have htopSub : Subgroup.map Z.subtype (⊤ : Subgroup ↥Z) = Z := by
    ext y
    constructor
    · rintro ⟨w, -, rfl⟩
      exact w.2
    · intro hy
      exact ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  have hNsyl : IsSylowOf 2 N Z := by
    have h := (isSylowOf_map_subtype_iff (p := 2) Z (A := (PZ : Subgroup ↥Z))
      (B := ⊤)).mpr ?_
    · rw [← hN, htopSub] at h
      exact h
    · rw [isSylowOf_iff]
      exact ⟨le_top, PZ.isPGroup', by rw [Subgroup.relIndex_top_right]; exact PZ.not_dvd_index⟩
  exact ⟨N, hNle, hNp, hNnormal, hNsyl⟩

private theorem sl2_index_odd {F : Type} [Field F] [Fintype F] [CharP F 2]
    (e : Y ⧸ Z ≃* SL(2, F))
    {T' : Subgroup SL(2, F)} (hT'def : T' = (T.map (QuotientGroup.mk' Z)).map e.toMonoidHom)
    {x : SL(2, F)} (hx : T' = conjSubgroup x (utri F))
    {N : Subgroup Y} (hNle : N ≤ Z) (hNnormal : N.Normal) (hNsyl : IsSylowOf 2 N Z)
    (hTZ : T ⊓ Z = ⊥) : ¬ 2 ∣ (T ⊔ N).index := by
  haveI : N.Normal := hNnormal

  have hTZcomap : (T ⊔ Z : Subgroup Y) = (T.map (QuotientGroup.mk' Z)).comap
      (QuotientGroup.mk' Z) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hidx : (T.map (QuotientGroup.mk' Z)).index = T'.index := by
    rw [hT'def]
    exact (Subgroup.index_map_equiv (T.map (QuotientGroup.mk' Z)) e).symm
  have hoddT' : ¬ 2 ∣ T'.index := by
    rw [hx]
    rw [show (conjSubgroup x (utri F)).index = (utri F).index from
      Subgroup.index_map_equiv (utri F) (MulAut.conj x), ← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr odd_index_utri
  have h2 : ¬ 2 ∣ (T ⊔ Z).index := by
    rw [← Subgroup.relIndex_top_right (H := T ⊔ Z), hTZcomap, Subgroup.relIndex_comap]
    rw [show (⊤ : Subgroup Y).map (QuotientGroup.mk' Z) = ⊤ from
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z),
      Subgroup.relIndex_top_right, hidx]
    exact hoddT'
  have h1 : ¬ 2 ∣ (T ⊔ N).relIndex (T ⊔ Z) := by
    have hTZeq : T ⊔ Z = Z ⊔ (T ⊔ N) := by
      rw [← sup_assoc, sup_eq_left.mpr (hNle.trans le_sup_left), sup_comm]
    rw [hTZeq, relIndex_sup_eq_relIndex_of_normal Z (T ⊔ N)]
    have hmod : (T ⊔ N) ⊓ Z = N := by
      refine le_antisymm ?_ ?_
      · intro y hy
        obtain ⟨t, ht, n, hn, rfl⟩ :=
          (Subgroup.mem_sup_of_normal_right (s := T) (t := N)).1 hy.1
        have hnZ : n ∈ Z := hNle hn
        have htZ : t ∈ Z := by
          have ht' : t = (t * n) * n⁻¹ := by group
          rw [ht']
          exact Z.mul_mem hy.2 (Z.inv_mem hnZ)
        have htbot : t ∈ (⊥ : Subgroup Y) := by
          rw [← hTZ]
          exact ⟨ht, htZ⟩
        rw [Subgroup.mem_bot.1 htbot, one_mul]
        exact hn
      · intro y hy
        exact ⟨(le_sup_right : N ≤ T ⊔ N) hy, hNle hy⟩
    rw [show (T ⊔ N).relIndex Z = ((T ⊔ N) ⊓ Z).relIndex Z from
      (Subgroup.inf_relIndex_right (H := T ⊔ N) (K := Z)).symm, hmod]
    exact (isSylowOf_iff.mp hNsyl).2.2
  have hmul : (T ⊔ N).relIndex (T ⊔ Z) * (T ⊔ Z).index = (T ⊔ N).index :=
    Subgroup.relIndex_mul_index (H := T ⊔ N) (K := T ⊔ Z)
      (sup_le le_sup_left (hNle.trans le_sup_right))
  have hoddTN : ¬ 2 ∣ (T ⊔ N).index := by
    rw [← hmul]
    exact fun h => (Nat.prime_two.dvd_mul.mp h).elim h1 (fun h' => h2 h')
  exact hoddTN

private theorem sl2_sylow_sup (hTp : IsPGroup 2 T)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (e : Y ⧸ Z ≃* SL(2, F))
    {T' : Subgroup SL(2, F)} (hT'def : T' = (T.map (QuotientGroup.mk' Z)).map e.toMonoidHom)
    {x : SL(2, F)} (hx : T' = conjSubgroup x (utri F))
    {N : Subgroup Y} (hNle : N ≤ Z) (hNp : IsPGroup 2 N) (hNnormal : N.Normal)
    (hNsyl : IsSylowOf 2 N Z) (hTZ : T ⊓ Z = ⊥) :
    ∃ S : Sylow 2 Y, IsSylowOf 2 (T ⊔ N) ⊤ ∧ (S : Subgroup Y) = T ⊔ N := by
  haveI : N.Normal := hNnormal
  have hPgroupTN : IsPGroup 2 ↥(T ⊔ N : Subgroup Y) := by
    rw [sup_comm]
    exact hNp.to_sup_of_normal_left hTp
  have hoddTN := sl2_index_odd e hT'def hx hNle hNnormal hNsyl hTZ
  have hSylTN : IsSylowOf 2 (T ⊔ N) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, hPgroupTN, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact hoddTN
  set S : Sylow 2 Y := IsPGroup.toSylow (P := (T ⊔ N : Subgroup Y)) hPgroupTN hoddTN with hS
  have hcoe : (S : Subgroup Y) = T ⊔ N := by
    rw [hS]
    exact IsPGroup.toSylow_coe hPgroupTN hoddTN
  exact ⟨S, hSylTN, hcoe⟩
private theorem sl2_N_eq_bot (hZ : Z ≤ Subgroup.center Y) (hperf : commutator Y = ⊤)
    {N : Subgroup Y} (hNle : N ≤ Z) (hNp : IsPGroup 2 N) (hNnormal : N.Normal)
    (hNcomm : IsMulCommutative N) (hTZ : T ⊓ Z = ⊥) {S : Sylow 2 Y}
    (hScoe : (S : Subgroup Y) = T ⊔ N) : N = ⊥ := by
  haveI : N.Normal := hNnormal
  haveI : IsMulCommutative N := hNcomm
  obtain ⟨C, hNC, hNsup⟩ :=
    exists_complement_of_sylow_complement (G := Y) Nat.prime_two hNp S
      (by rw [hScoe]; exact le_sup_right)
      (by
        have hle : N ⊓ T ≤ T ⊓ Z := fun y hy => ⟨hy.2, hNle hy.1⟩
        rw [hTZ] at hle
        exact le_bot_iff.mp hle)
      (by rw [hScoe, sup_comm])
  have hCconj : ∀ g : Y, conjSubgroup g C = C := by
    intro g
    obtain ⟨n, hn, c, hc, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := N) (t := C)).1 (hNsup ▸ Subgroup.mem_top g)
    have hn1 : conjSubgroup n C = C := by
      rw [← mem_normalizer_iff_conjSubgroup_eq]
      exact Subgroup.center_le_normalizer (C : Set Y) (hZ (hNle hn))
    have hc1 : conjSubgroup c C = C := by
      rw [← mem_normalizer_iff_conjSubgroup_eq]
      exact Subgroup.le_normalizer hc
    rw [← conjSubgroup_conjSubgroup n c C, hc1, hn1]
  have hCnormal : C.Normal :=
    ⟨fun x hx g => by
      have h := hCconj g
      rw [← h]
      exact conj_mem_conjSubgroup g hx⟩
  have hNtop : ⁅N, (⊤ : Subgroup Y)⁆ = (⊥ : Subgroup Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((hNle.trans hZ).trans (Subgroup.center_le_centralizer (⊤ : Set Y)))
  have hcommC : commutator Y ≤ C := by
    haveI : C.Normal := hCnormal
    haveI : (N ⊔ C).Normal := inferInstance
    have hNN : ⁅N, N⁆ = (⊥ : Subgroup Y) :=
      le_bot_iff.mp ((Subgroup.commutator_mono le_rfl le_top).trans_eq hNtop)
    have hNC : ⁅N, C⁆ = (⊥ : Subgroup Y) :=
      le_bot_iff.mp ((Subgroup.commutator_mono le_rfl le_top).trans_eq hNtop)
    have hCN : ⁅C, N⁆ = (⊥ : Subgroup Y) := by rw [Subgroup.commutator_comm C N, hNC]
    have hkey : ⁅(N ⊔ C : Subgroup Y), (N ⊔ C : Subgroup Y)⁆ = ⁅C, C⁆ := by
      rw [Subgroup.commutator_sup_right N C (N ⊔ C),
        Subgroup.commutator_sup_left N N C, Subgroup.commutator_sup_left C N C,
        hNN, hNC, hCN]
      simp
    calc commutator Y = ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ := rfl
      _ = ⁅(N ⊔ C : Subgroup Y), (N ⊔ C : Subgroup Y)⁆ := by rw [hNsup]
      _ = ⁅C, C⁆ := hkey
      _ ≤ C := Subgroup.commutator_le.mpr fun a ha b hb => by
          show a * b * a⁻¹ * b⁻¹ ∈ C
          exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hCtop : C = ⊤ := by
    have h := hcommC
    rw [hperf] at h
    exact top_le_iff.mp h
  have hNbot : N = ⊥ := by
    have h := hNC
    rw [hCtop, inf_top_eq] at h
    exact h
  exact hNbot

private theorem sl2_center_eq_bot
    (hperf : commutator Y = ⊤)
    (hZc : Z = Subgroup.center Y) {N : Subgroup Y} (hNbot : N = ⊥) (hNle : N ≤ Z)
    (hNsyl : IsSylowOf 2 N Z) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (e : Y ⧸ Z ≃* SL(2, F)) : Z = ⊥ := by
  have hoddZ : Odd (Nat.card Z) := by
    have hNcard : Nat.card N = 1 := by rw [hNbot]; simp
    have h1 : N.relIndex Z = Nat.card Z := by
      have h := Subgroup.relIndex_mul_card (H := N) (K := Z)
      rw [inf_eq_left.mpr hNle, hNcard, mul_one] at h
      exact h
    rw [← h1]
    exact Nat.not_even_iff_odd.mp fun he =>
      (isSylowOf_iff.mp hNsyl).2.2 (even_iff_two_dvd.mp he)
  have hoddY : Odd (Nat.card (Subgroup.center Y)) := hZc ▸ hoddZ
  obtain ⟨n, -, hcardF⟩ := FiniteField.card F 2
  haveI : Fintype (GaloisField 2 (n : ℕ)) := Fintype.ofFinite _
  have hn0 : (n : ℕ) ≠ 0 := n.pos.ne'
  have hGal : Fintype.card (GaloisField 2 (n : ℕ)) = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card (p := 2) (n := (n : ℕ)) hn0, hcardF]
  let ρ : F ≃+* GaloisField 2 (n : ℕ) := (FiniteField.ringEquivOfCardEq hGal).symm
  let slEq : SL(2, F) ≃* SL(2, GaloisField 2 (n : ℕ)) :=
    { toFun := Matrix.SpecialLinearGroup.map ρ.toRingHom
      invFun := Matrix.SpecialLinearGroup.map ρ.symm.toRingHom
      left_inv := fun A => Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe]
        ext i j
        simp)
      right_inv := fun A => Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe]
        ext i j
        simp)
      map_mul' := fun A B => map_mul _ A B }
  have e1 : Y ⧸ Subgroup.center Y ≃* SL(2, F) := hZc ▸ e
  have e3 : Y ⧸ Subgroup.center Y ≃* CFSG.Theory.Comparator.PSL2Model (n : ℕ) :=
    (e1.trans slEq).trans
      (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 (n : ℕ))).symm
  have hcenterbot : Subgroup.center Y = ⊥ :=
    CFSG.Timmesfeld.Bridge.OddLocal.center_eq_bot_of_psl2 hperf hoddY e3
  exact hZc.trans hcenterbot

private theorem centralTI_sl2_aux
    (hT : Assembly.IsElemAbelian 2 T)
    (hgen : Subgroup.normalClosure (T : Set Y) = ⊤) (hTI : IsTI T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)))
    (hZ : Z ≤ Subgroup.center Y) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : 4 ≤ Fintype.card F) (e : Y ⧸ Z ≃* SL(2, F)) :
    Z = ⊥ ∧ IsSylowOf 2 T ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : ¬ IsMulCommutative (Y ⧸ Z) := by
    intro h
    haveI := h
    exact not_isMulCommutative_sl2 (IsMulCommutative.of_comm fun a b => by
      obtain ⟨x, rfl⟩ := e.surjective a
      obtain ⟨y, rfl⟩ := e.surjective b
      rw [← map_mul, ← map_mul, mul_comm' x y])
  have hTZ : T ⊓ Z = ⊥ := inf_eq_bot_of_not_isMulCommutative hT hgen hTI hZ hq
  have hTp : IsPGroup 2 T :=
    Timmesfeld.Bridge.OddLocal.isPGroup_two_of_mul_self fun x hx => by
      simpa [pow_two] using hT.2 x hx
  haveI hQnt : Nontrivial (Y ⧸ Z) :=
    ⟨⟨e.symm (utriElt (1 : F)), 1, fun h =>
      utriElt_ne_one one_ne_zero (e.symm.injective (by rw [h, map_one]))⟩⟩
  haveI hYnt : Nontrivial Y := (QuotientGroup.mk'_surjective Z).nontrivial
  have hTne : T ≠ ⊥ := by
    intro hbot
    have htop : (⊤ : Subgroup Y) = ⊥ := by
      rw [← hgen, hbot]
      simp
    exact top_ne_bot htop
  obtain ⟨T', x, hT'p, hT'ne, hT'wc, hT'def, hx, -⟩ :=
    sl2_T'_data hTZ hTp hTne hwc hZ e
  obtain ⟨d, hdN, hfpfT⟩ :=
    sl2_lift_torus hTZ hwc hZ hF e hT'def hT'p hT'ne hT'wc hx
  have hperf : commutator Y = ⊤ := commutator_eq_top_of_fixedPointFree hdN hfpfT hgen
  have hZc : Z = Subgroup.center Y := sl2_center_eq_center hZ e
  obtain ⟨N, hNle, hNp, hNnormal, hNsyl⟩ := sl2_N_data hZ
  haveI : N.Normal := hNnormal
  have hNcomm : IsMulCommutative N := IsMulCommutative.of_comm fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.1 (hZ (hNle a.2)) (b : Y)).symm
  obtain ⟨S, hSylTN, hScoe⟩ := sl2_sylow_sup hTp e hT'def hx hNle hNp hNnormal hNsyl hTZ
  have hNbot : N = ⊥ := sl2_N_eq_bot hZ hperf hNle hNp hNnormal hNcomm hTZ hScoe
  have hTsyl : IsSylowOf 2 T ⊤ := by
    rw [hNbot, sup_bot_eq] at hSylTN
    exact hSylTN
  exact ⟨sl2_center_eq_bot hperf hZc hNbot hNle hNsyl e, hTsyl⟩

theorem centralTI_sl2
    (hT : Assembly.IsElemAbelian 2 T)
    (hgen : Subgroup.normalClosure (T : Set Y) = ⊤) (hTI : IsTI T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)))
    (hZ : Z ≤ Subgroup.center Y) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : 4 ≤ Fintype.card F) (e : Y ⧸ Z ≃* SL(2, F)) : Z = ⊥ :=
  (centralTI_sl2_aux hT hgen hTI hwc hZ hF e).1

end CFSG.RankThree.GF2n.Tim81.CentralTI
