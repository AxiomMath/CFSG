module

public import CFSG.Quasithin.Vol2.Ch3Sec2Conj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523Sz
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Quasithin.Vol2.Ch11L2Q5cL34
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523F
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SzOff

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedProj StatedScalars
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Pointwise commutatorElement

section Dictionary

variable {G : Type} [Group G] {A : Subgroup G}

theorem mem_irrPlusOn_of_isIrrPlusIn [IsMulCommutative ↥A] {X T I : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (A : Set G)) (hT : T ≤ Subgroup.normalizer (A : Set G))
    (hI : IsIrrPlusIn X A T I) :
    I.subgroupOf A ∈ IrrPlusOn (onA A X) ⊤ (onA A T) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  have hbase : I.subgroupOf A ∈ IrrPlus (onA A X) ⊤ :=
    (isIrrPlusBase_iff hX h1).1 ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨hbase, ?_⟩
  have hI'map : (I.subgroupOf A).map A.subtype = I := Subgroup.map_subgroupOf_eq_of_le h1
  have hC : (modFix (onA A X) ⊤).map A.subtype = A ⊓ Subgroup.centralizer (X : Set G) := by
    rw [map_modFix hX, map_subtype_top]
  have hW : (⨆ y ∈ onA A T, y • I.subgroupOf A).map A.subtype = conjClosure I T := by
    rw [map_biSup_smul hT, hI'map]
  have hirrI := (isIrr_tilde hbase).1
  refine ⟨hirrI, tilde_mono ?_, fun L' hL'W hL'irr hL'iso => ?_⟩
  · have := le_biSup_smul (V := ↥A) (onA A T) (I.subgroupOf A) (onA A T).one_mem
    rwa [one_smul] at this
  · set π := QuotientGroup.mk' (modFix (V := ↥A) (onA A X) ⊤) with hπ
    have hL'eq : tilde (onA A X) ⊤ (L'.comap π) = L' :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) L'
    have hfix : modFix (V := ↥A) (onA A X) ⊤ ≤ L'.comap π := fun v hv => by
      rw [Subgroup.mem_comap, hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff v).mpr hv]
      exact L'.one_mem
    have hJinv : IsModInv (onA A X) (L'.comap π) := fun a v hv => by
      rw [Subgroup.mem_comap] at hv ⊢
      exact hL'irr.1 a _ hv
    have hCJ : A ⊓ Subgroup.centralizer (X : Set G) ≤ (L'.comap π).map A.subtype := by
      rw [← hC]
      exact Subgroup.map_mono hfix
    have hJW : (L'.comap π).map A.subtype ≤ conjClosure I T ⊔
        A ⊓ Subgroup.centralizer (X : Set G) := by
      have h1' : L'.comap π ≤ (⨆ y ∈ onA A T, y • I.subgroupOf A) ⊔ modFix (onA A X) ⊤ := by
        rw [← comap_tilde]
        exact Subgroup.comap_mono hL'W
      have h2' := Subgroup.map_mono (f := A.subtype) h1'
      rwa [Subgroup.map_sup, hW, hC] at h2'
    have hXJ : X ≤ Subgroup.normalizer (((L'.comap π).map A.subtype : Subgroup G) : Set G) :=
      (isModInv_iff hX _).1 hJinv
    have hKinv : IsModInv (onA A X) (I.subgroupOf A ⊔ modFix (onA A X) ⊤) :=
      XMod.IsInv.sup hbase.2.1 (XMod.isInv_fixed ⊤)
    have hti : XMod.Iso ↥(onA A X) (tilde (onA A X) ⊤ (L'.comap π))
        (tilde (onA A X) ⊤ (I.subgroupOf A ⊔ modFix (onA A X) ⊤)) := by
      rw [hL'eq, tilde_sup_modFix]
      exact hL'iso
    have hiso₂ := isXSectionIso₂_of_iso_tilde hX hti
    have hJA : (L'.comap π).map A.subtype ≤ A := Subgroup.map_subtype_le _
    have hJC : (L'.comap π).map A.subtype ⊓ Subgroup.centralizer (X : Set G) =
        A ⊓ Subgroup.centralizer (X : Set G) :=
      le_antisymm (inf_le_inf_right _ hJA) (le_inf hCJ inf_le_right)
    have hKmap : (I.subgroupOf A ⊔ modFix (onA A X) ⊤).map A.subtype =
        I ⊔ A ⊓ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.map_sup, hI'map, hC]
    have hKC : (I ⊔ A ⊓ Subgroup.centralizer (X : Set G)) ⊓ Subgroup.centralizer (X : Set G) =
        A ⊓ Subgroup.centralizer (X : Set G) :=
      le_antisymm (inf_le_inf_right _ (sup_le h1 inf_le_left)) (le_inf le_sup_right inf_le_right)
    rw [hJC, hKmap, hKC] at hiso₂
    have hle := h7 _ hCJ hJW hXJ hiso₂
    rw [← hKmap, Subgroup.map_le_map_iff_of_injective A.subtype_injective] at hle
    have hle' := tilde_mono (X := onA A X) (W := ⊤) hle
    rwa [hL'eq, tilde_sup_modFix] at hle'

theorem actCompat_autOn_onA [IsMulCommutative ↥A] (X : Subgroup G) :
    ActCompat (MonoidHom.id ↥A) (autOn X A) (onA A X) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, fun p => rfl⟩
  · intro a ha
    exact ⟨conjAct A a, ⟨a, ha, rfl⟩, fun p => rfl⟩

theorem biSup_smul_eq_of_actCompat {G₁ G₂ P : Type*} [Group G₁] [Group G₂] [CommGroup P]
    [MulDistribMulAction G₁ P] [MulDistribMulAction G₂ P] {X₁ : Subgroup G₁} {X₂ : Subgroup G₂}
    (h : ActCompat (MonoidHom.id P) X₁ X₂) (J : Subgroup P) :
    (⨆ y ∈ X₁, y • J) = ⨆ y ∈ X₂, y • J := by
  have key : ∀ (y₁ : G₁) (y₂ : G₂), (∀ p : P, y₁ • p = y₂ • p) → y₁ • J = y₂ • J := by
    intro y₁ y₂ hy
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨j, hj, hx⟩ => ⟨j, hj, (hy j).symm.trans hx⟩,
      fun ⟨j, hj, hx⟩ => ⟨j, hj, (hy j).trans hx⟩⟩
  refine le_antisymm (iSup₂_le fun y hy => ?_) (iSup₂_le fun y hy => ?_)
  · obtain ⟨a, ha, hya⟩ := h.fwd y hy
    rw [key y a hya]
    exact le_iSup₂_of_le a ha le_rfl
  · obtain ⟨b, hb, hby⟩ := h.bwd y hy
    rw [← key b y hby]
    exact le_iSup₂_of_le b hb le_rfl

end Dictionary

section Arith

open CFSG.Timmesfeld.Orders

theorem exists_odd_card_sl_three {m : ℕ} (hm : 1 ≤ m) :
    ∃ r, Odd r ∧ (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1) = 2 ^ (m * 3) * r :=
  ⟨((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1),
    (odd_pow_sub_one hm two_pos).mul (odd_pow_sub_one hm three_pos), by rw [pow_mul]; ring⟩

theorem exists_odd_card_sp_four {m : ℕ} (hm : 1 ≤ m) :
    ∃ r, Odd r ∧ (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) = 2 ^ (m * 4) * r :=
  ⟨((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1),
    (odd_pow_sub_one hm two_pos).mul (odd_pow_sub_one hm four_pos), by rw [pow_mul]⟩

theorem card_sl_three_ne {x : ℕ} (hx : 2 ≤ x) :
    x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) ≠ x ^ 3 * ((x ^ 3) ^ 2 - 1) := by
  intro h
  have h3 : 0 < x ^ 3 := by positivity
  have h' : (x ^ 2 - 1) * (x ^ 3 - 1) = (x ^ 3) ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_left h3 (by rw [← mul_assoc]; exact h)
  have h1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ (x ^ 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h6] at h'
  have hx' : (2 : ℤ) ≤ x := by exact_mod_cast hx
  nlinarith [pow_pos (show (0 : ℤ) < x by omega) 5, pow_pos (show (0 : ℤ) < x by omega) 2]

theorem card_sp_four_ne {x : ℕ} (hx : 2 ≤ x) :
    x ^ 4 * ((x ^ 2 - 1) * (x ^ 4 - 1)) ≠ x ^ 4 * ((x ^ 4) ^ 2 - 1) := by
  intro h
  have h4 : 0 < x ^ 4 := by positivity
  have h' : (x ^ 2 - 1) * (x ^ 4 - 1) = (x ^ 4) ^ 2 - 1 := Nat.eq_of_mul_eq_mul_left h4 h
  have h1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ x ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h8 : 1 ≤ (x ^ 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h8] at h'
  have hx' : (2 : ℤ) ≤ x := by exact_mod_cast hx
  nlinarith [pow_pos (show (0 : ℤ) < x by omega) 6, pow_pos (show (0 : ℤ) < x by omega) 4,
    pow_pos (show (0 : ℤ) < x by omega) 2]

theorem card_l_two_ne {n e r : ℕ} (hn : 1 ≤ n) (hr : Odd r)
    (hne : 2 ^ e * ((2 ^ e) ^ 2 - 1) ≠ 2 ^ e * r) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 2 ^ e * r := by
  intro h
  have := eq_of_two_pow_mul_odd (odd_pow_sub_one hn two_pos) hr h
  subst this
  exact hne h

end Arith

section Groups

theorem isQuasisimple_of_isSimpleGroup_of_noncomm {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : CFSG.IsQuasisimple X := by
  obtain ⟨a, b, hab⟩ := hnc
  have := hs
  have hcomm : commutator X = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      have hc : ⁅a, b⁆ ∈ commutator X :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hab hc
    · exact h
  have hcen : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      have ha : a ∈ Subgroup.center X := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  refine ⟨Group.isPerfect_def.mpr hcomm, MulEquiv.isSimpleGroup e, e.symm a, e.symm b,
    fun h => ?_⟩
  apply hab
  have := congrArg e h
  simpa using this

theorem card_of_isPSL_two {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two h

theorem card_of_isPSL_three_four {X : Type} [Group X] (h : IsPSL 3 2 2 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

theorem isQuasisimple_of_isPSL {X : Type} [Group X] {d n : ℕ} (h : IsPSL d 2 n X)
    (hne : Nat.card X ≠ 0) (hp : ¬ (Nat.card X).Prime) : CFSG.IsQuasisimple X := by
  have hs : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X d 2 n h).2
  have : Finite X := Nat.finite_of_card_ne_zero hne
  refine isQuasisimple_of_isSimpleGroup_of_noncomm hs ?_
  by_contra hc
  push Not at hc
  let _ : CommGroup X := { ‹Group X› with mul_comm := fun a b => hc a b }
  exact hp (IsSimpleGroup.prime_card (α := X))

theorem isPSL_of_mulEquiv {X Y : Type} [Group X] [Group Y] {d p n : ℕ} (h : IsPSL d p n Y)
    (e : X ≃* Y) : IsPSL d p n X := by
  obtain ⟨hadm, K, hK1, hK2, hK, ⟨ψ⟩⟩ := h
  exact ⟨hadm, K, hK1, hK2, hK, ⟨e.trans ψ⟩⟩

theorem card_eq_or_eq_one_of_isSimpleGroup {X Y : Type*} [Group X] [Group Y] [IsSimpleGroup X]
    (π : X →* Y) (hπ : Function.Surjective π) : Nat.card Y = Nat.card X ∨ Nat.card Y = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact Or.inl (Nat.card_congr (Equiv.ofBijective π
      ⟨(MonoidHom.ker_eq_bot_iff π).mp h, hπ⟩)).symm
  · refine Or.inr (Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩)
    obtain ⟨x, rfl⟩ := hπ a
    obtain ⟨y, rfl⟩ := hπ b
    have hx : x ∈ π.ker := h ▸ Subgroup.mem_top x
    have hy : y ∈ π.ker := h ▸ Subgroup.mem_top y
    rw [MonoidHom.mem_ker] at hx hy
    rw [hx, hy]

theorem card_alternatingGroup_fin_six : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_alternatingGroup_fin_seven : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_statedSL_four_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(StatedSL 4 K) = 20160 :=
  CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two hK

theorem card_statedSL_five_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(StatedSL 5 K) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_of_card_eq_two hK

theorem card_statedSp_two {K : Type} [Field K] [Finite K] :
    Nat.card ↥(StatedSp 2 K) =
      Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by norm_num)]
  norm_num

theorem isPSL_of_statedSL_two {X : Type} [Group X] {d : ℕ} (hd : 3 ≤ d) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) (e : ↥(StatedSL d K) ≃* X) : IsPSL d 2 1 X := by
  have hunits : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, hK]
  have hsub : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hunits).1
  have hbot : (StatedScalars (Fin d) K).subgroupOf (StatedSL d K) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨u, hu⟩
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hx : (x : Matrix.GeneralLinearGroup (Fin d) K) =
        Matrix.GeneralLinearGroup.scalar (Fin d) u := hu.symm
    rw [hx, Subsingleton.elim u 1, map_one]
    rfl
  let ψ : StatedProj (StatedSL d K) ≃* ↥(StatedSL d K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨⟨Nat.prime_two, le_rfl, by omega, fun h => ?_, fun h => ?_⟩, K, inferInstance,
    inferInstance, by rw [hK, pow_one], ⟨e.symm.trans ψ.symm⟩⟩
  · have := congrArg Prod.fst h
    simp only at this
    omega
  · have := congrArg Prod.fst h
    simp only at this
    omega

theorem injective_of_realizesVia_nat {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {U Z : Subgroup V} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι F)) {π : Γ →* ↥L}
    (hR : (FFModel.nat Γ).RealizesVia L U Z π) : Function.Injective π := by
  obtain ⟨-, -, -, hUinv, -, -, -, β, hβs, hβker, hβact⟩ := hR
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have hfix : ∀ m : Multiplicative (ι → F), natAct Γ γ m = m := by
    intro m
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk (⟨m, trivial⟩ : ↥(FFModel.nat Γ).sec))
    have hU' : ((π γ : ↥L) : MulAut V) (u : V) ∈ U := hUinv (π γ) u u.2
    have hm' : (FFModel.nat Γ).act γ m ∈ (FFModel.nat Γ).sec := trivial
    have h1 := hβact γ u ⟨m, trivial⟩ hU' hm' hu
    have hπ1 : ∀ w : V, ((π γ : ↥L) : MulAut V) w = w := by
      intro w
      rw [hγ]
      rfl
    have h2 : (⟨((π γ : ↥L) : MulAut V) (u : V), hU'⟩ : ↥U) = u := Subtype.ext (hπ1 _)
    have hmk := ((congrArg β h2).symm.trans h1).symm.trans hu
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hmk
    have h0 := Subgroup.mem_bot.mp hmk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h0
    exact inv_mul_eq_one.mp h0
  have hM : ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    have := congrArg Multiplicative.toAdd (hfix (Multiplicative.ofAdd (Pi.single i 1)))
    rw [Matrix.one_mulVec]
    exact this
  exact Subtype.ext (Units.ext hM)

theorem nonempty_mulEquiv_of_realizes_nat {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {U Z : Subgroup V} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} (h : (FFModel.nat Γ).Realizes L U Z) :
    Nonempty (↥L ≃* ↥Γ) := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨(MulEquiv.ofBijective π ⟨injective_of_realizesVia_nat Γ hπ, hπ.1⟩).symm⟩

end Groups

section Exclusions

variable {V : Type} [CommGroup V]

theorem not_d310Two_of_isPSL_two {X : Type} [Group X] {n : ℕ} (hX : IsPSL 2 2 n X)
    (T L : Subgroup (MulAut V)) (U : Subgroup V) (e : ↥L ≃* X) : ¬ D310Two T L U := by
  have hn : 1 ≤ n := hX.1.2.1
  have hcard : Nat.card ↥L = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, card_of_isPSL_two hX]
  have hgt : 1 < Nat.card ↥L := by
    have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    have h3 : 3 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    rw [hcard]
    nlinarith
  rintro ⟨hmod, -, -⟩
  rcases hmod with ⟨m, K, _, _, hK, hR⟩ | ⟨m, K, _, _, hK, hR⟩ | ⟨π, hπ⟩ | ⟨K, _, _, hK, hR⟩ |
    ⟨K, _, _, hK, hR⟩ | ⟨α, π, hπ⟩
  ·
    obtain ⟨φ⟩ := nonempty_mulEquiv_of_realizes_nat hR
    have h1 := Nat.card_congr φ.toEquiv
    rw [CFSG.SectionRank.OddCover.card_statedSL_three, hK] at h1
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num at h1
      omega
    obtain ⟨r, hr, hre⟩ := exists_odd_card_sl_three hm
    rw [hcard] at h1
    refine card_l_two_ne hn hr ?_ (h1.trans hre)
    rw [← hre, pow_mul]
    exact (card_sl_three_ne (Nat.le_self_pow (by omega) 2)).symm
  ·
    obtain ⟨φ⟩ := nonempty_mulEquiv_of_realizes_nat hR
    have h1 := Nat.card_congr φ.toEquiv
    rw [card_statedSp_two, hK] at h1
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num at h1
      omega
    obtain ⟨r, hr, hre⟩ := exists_odd_card_sp_four hm
    rw [hcard] at h1
    refine card_l_two_ne hn hr ?_ (h1.trans hre)
    rw [← hre, pow_mul]
    exact (card_sp_four_ne (Nat.le_self_pow (by omega) 2)).symm
  ·
    change ↥(alternatingGroup (Fin 6)) →* ↥L at π
    have := alternatingGroup.isSimpleGroup (α := Fin 6) (by norm_num)
    rcases card_eq_or_eq_one_of_isSimpleGroup π hπ.1 with h | h
    · rw [card_alternatingGroup_fin_six, hcard] at h
      exact card_l_two_ne (e := 3) (r := 45) hn ⟨22, rfl⟩ (by norm_num) (h.trans (by norm_num))
    · omega
  ·
    obtain ⟨φ⟩ := nonempty_mulEquiv_of_realizes_nat hR
    have h1 := Nat.card_congr φ.toEquiv
    rw [card_statedSL_four_of_card_two (by rw [hK, pow_one]), hcard] at h1
    exact card_l_two_ne (e := 6) (r := 315) hn ⟨157, rfl⟩ (by norm_num) (h1.trans (by norm_num))
  ·
    obtain ⟨φ⟩ := nonempty_mulEquiv_of_realizes_nat hR
    have h1 := Nat.card_congr φ.toEquiv
    rw [card_statedSL_five_of_card_two (by rw [hK, pow_one]), hcard] at h1
    exact card_l_two_ne (e := 10) (r := 9765) hn ⟨4882, rfl⟩ (by norm_num)
      (h1.trans (by norm_num))
  ·
    change ↥(alternatingGroup (Fin 7)) →* ↥L at π
    have := alternatingGroup.isSimpleGroup (α := Fin 7) (by norm_num)
    rcases card_eq_or_eq_one_of_isSimpleGroup π hπ.1 with h | h
    · rw [card_alternatingGroup_fin_seven, hcard] at h
      exact card_l_two_ne (e := 3) (r := 315) hn ⟨157, rfl⟩ (by norm_num) (h.trans (by norm_num))
    · omega

theorem not_d310Two_of_isPSL_three_four {X : Type} [Group X] (hX : IsPSL 3 2 2 X)
    (T L : Subgroup (MulAut V)) (U : Subgroup V) (e : ↥L ≃* X) : ¬ D310Two T L U := by
  have hL : IsPSL 3 2 2 ↥L := isPSL_of_mulEquiv hX e
  have hcard : Nat.card ↥L = 20160 := card_of_isPSL_three_four hL
  rintro ⟨hmod, -, -⟩
  rcases hmod with ⟨m, K, _, _, hK, hR⟩ | ⟨m, K, _, _, hK, hR⟩ | ⟨π, hπ⟩ | ⟨K, _, _, hK, hR⟩ |
    ⟨K, _, _, hK, hR⟩ | ⟨α, π, hπ⟩
  ·
    obtain ⟨φ⟩ := nonempty_mulEquiv_of_realizes_nat hR
    have h1 := Nat.card_congr φ.toEquiv
    rw [CFSG.SectionRank.OddCover.card_statedSL_three, hK, hcard] at h1
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num at h1
    obtain ⟨r, hr, hre⟩ := exists_odd_card_sl_three hm
    have hm2 : 6 = m * 3 :=
      CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (r := 315) ⟨157, rfl⟩ hr
        ((show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num).symm.trans (h1.trans hre))
    obtain rfl : m = 2 := by omega
    norm_num at h1
  ·
    obtain ⟨φ⟩ := nonempty_mulEquiv_of_realizes_nat hR
    have h1 := Nat.card_congr φ.toEquiv
    rw [card_statedSp_two, hK, hcard] at h1
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num at h1
    obtain ⟨r, hr, hre⟩ := exists_odd_card_sp_four hm
    have hm2 : 6 = m * 4 :=
      CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (r := 315) ⟨157, rfl⟩ hr
        ((show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num).symm.trans (h1.trans hre))
    omega
  ·
    change ↥(alternatingGroup (Fin 6)) →* ↥L at π
    have h1 := Nat.card_le_card_of_surjective π hπ.1
    rw [card_alternatingGroup_fin_six, hcard] at h1
    omega
  ·
    obtain ⟨φ⟩ := nonempty_mulEquiv_of_realizes_nat hR
    exact Vol2.Ch11.SecB.not_isPSL_four_two_one_of_isPSL_three_two_two hL
      (isPSL_of_statedSL_two (by norm_num) (by rw [hK, pow_one]) φ.symm)
  ·
    obtain ⟨φ⟩ := nonempty_mulEquiv_of_realizes_nat hR
    have h1 := Nat.card_congr φ.toEquiv
    rw [card_statedSL_five_of_card_two (by rw [hK, pow_one]), hcard] at h1
    omega
  ·
    change ↥(alternatingGroup (Fin 7)) →* ↥L at π
    have h1 := Nat.card_le_card_of_surjective π hπ.1
    rw [card_alternatingGroup_fin_seven, hcard] at h1
    omega

end Exclusions

section Bridge

variable {Γ : Type} [Group Γ]

theorem autOn_sup_eq {A X Y : Subgroup Γ} (hX : X ≤ Subgroup.normalizer (A : Set Γ))
    (hY : Y ≤ Subgroup.normalizer (A : Set Γ)) : autOn (X ⊔ Y) A = autOn X A ⊔ autOn Y A := by
  have h1 : (X ⊔ Y).subgroupOf (Subgroup.normalizer (A : Set Γ)) =
      X.subgroupOf (Subgroup.normalizer (A : Set Γ)) ⊔
        Y.subgroupOf (Subgroup.normalizer (A : Set Γ)) := by
    apply Subgroup.map_injective (Subgroup.normalizer (A : Set Γ)).subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (sup_le hX hY),
      Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY]
  unfold autOn
  rw [h1, Subgroup.map_sup]

theorem map_subgroupOf_conjAct_eq_autOn {A X H : Subgroup Γ} (hXH : X ≤ H)
    (hH : H ≤ Subgroup.normalizer (A : Set Γ)) :
    (X.subgroupOf H).map ((conjAct A).comp (Subgroup.inclusion hH)) = autOn X A := by
  ext φ
  constructor
  · rintro ⟨⟨x, hxH⟩, hxX, rfl⟩
    exact ⟨⟨x, hH hxH⟩, hxX, rfl⟩
  · rintro ⟨⟨x, hxN⟩, hxX, rfl⟩
    exact ⟨⟨x, hXH hxX⟩, hxX, rfl⟩

variable [Finite Γ]

theorem d3Std_of_internal {M K T I : Subgroup Γ} (hM : SQTKGroup ↥M) (hT : IsSylowTwoOf T M)
    (hMK : M ≤ Subgroup.normalizer (K : Set Γ)) (hMKT : M = K ⊔ T)
    (hI : IsIrrPlusIn K (conjClosure I T) T I) [IsMulCommutative ↥(conjClosure I T)]
    (hexp : ∀ w ∈ conjClosure I T, w ^ 2 = 1) (hO2 : pCoreOf 2 (autOn M (conjClosure I T)) = ⊥)
    (hKq : CFSG.IsQuasisimple ↥(autOn K (conjClosure I T)))
    (hq : qhatOf (autOn M (conjClosure I T)) ≤ ((2 : ℚ) : WithTop ℚ)) :
    D3Std (autOn M (conjClosure I T)) (autOn K (conjClosure I T)) (autOn T (conjClosure I T))
      (autOn K (conjClosure I T)) (I.subgroupOf (conjClosure I T)) := by
  set W := conjClosure I T with hWdef
  have hTM : T ≤ M := hT.1
  have hTK : T ≤ Subgroup.normalizer (K : Set Γ) := hTM.trans hMK
  have hTW : T ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_conjClosure I T
  have hKW : K ≤ Subgroup.normalizer (W : Set Γ) :=
    CFSG.Quasithin.le_normalizer_conjClosure_of_le hI.2.2.1 hTK
  have hMW : M ≤ Subgroup.normalizer (W : Set Γ) := hMKT ▸ sup_le hKW hTW
  have hsup : autOn K W ⊔ autOn T W = autOn M W := by rw [hMKT, autOn_sup_eq hKW hTW]
  have hexpW : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hexp w w.2)
  have hTbL : autOn T W ≤ Subgroup.normalizer (autOn K W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn_of_normalizes hTK
  have hMbL : autOn M W ≤ Subgroup.normalizer (autOn K W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn_of_normalizes hMK
  have hLM : autOn K W ≤ autOn M W := hsup ▸ le_sup_left
  have hTbM : autOn T W ≤ autOn M W := hsup ▸ le_sup_right
  have hqsqtk : IsQuotientOfSQTKTC ↥(autOn M W) :=
    ⟨↥M, inferInstance, inferInstance, fun p hp hp2 => hM.1 p hp hp2, hM.2,
      InternalSec.autOnHom hMW, InternalSec.autOnHom_surjective hMW⟩
  have hsyl : IsSylowTwoOf (autOn T W) (autOn M W) := by
    have := isSylowTwoOf_map_subgroupOf ((conjAct W).comp (Subgroup.inclusion hMW)) hT
    rwa [map_subgroupOf_conjAct_eq_autOn hTM hMW, map_subgroupOf_conjAct_eq_autOn le_rfl hMW]
      at this
  have hcomp : autOn K W ∈ cComp (autOn M W) :=
    mem_cComp_of_isQuasisimple_of_isSubnormal hKq (A3.subnormal_of_normal hLM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr hMbL))
  have hMpeq : autOn K W = conjClosure (autOn K W) (autOn T W) :=
    (le_antisymm (conjClosure_le fun t ht x hx => (Subgroup.mem_normalizer_iff.mp (hTbL ht) x).mp
      hx) (le_conjClosure _ _)).symm
  have hbiSup : (⨆ y ∈ autOn T W, y • I.subgroupOf W) =
      ⨆ y ∈ onA W T, y • I.subgroupOf W :=
    biSup_smul_eq_of_actCompat (actCompat_autOn_onA T) _
  have hirrT : I.subgroupOf W ∈ IrrPlusOn (autOn K W) (orbSup (autOn T W) (I.subgroupOf W))
      (autOn T W) := by
    rw [orbSup_eq_biSup_smul]
    refine (actCompat_autOn_onA K).mem_irrPlusOn_of_map Function.injective_id
      (actCompat_autOn_onA T) hTbL (H13.le_normalizer_subgroupOf hTK) (Wq := ⊤)
      (fun _ _ _ _ => trivial) ?_
    rw [Subgroup.map_id]
    exact mem_irrPlusOn_of_isIrrPlusIn hKW hTW hI
  have htop : orbSup (autOn T W) (I.subgroupOf W) = ⊤ := by
    rw [orbSup_eq_biSup_smul, hbiSup]
    apply Subgroup.map_injective W.subtype_injective
    rw [map_biSup_smul hTW, Subgroup.map_subgroupOf_eq_of_le (le_conjClosure I T),
      map_subtype_top]
  have hgen : (⨆ m ∈ autOn M W, (I.subgroupOf W).map m.toMonoidHom) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup₂_le fun τ hτ => le_iSup₂_of_le τ (hTbM hτ) le_rfl
  have ho2 : ∀ g ∈ pCoreOf 2 (autOn K W ⊔ autOn T W), ∀ v ∈ I.subgroupOf W,
      g v ∈ I.subgroupOf W := by
    intro g hg v hv
    rw [hsup, hO2, Subgroup.mem_bot] at hg
    rw [hg]
    exact hv
  have hqhat : qhatOf (autSub (autOn K W ⊔ autOn T W) (orbSup (autOn T W) (I.subgroupOf W))) ≤
      ((2 : ℚ) : WithTop ℚ) := by
    rw [qhatOf_autSub_congr htop, hsup]
    exact qhatOf_autSub_top_le hexpW hq
  exact ⟨⟨hexpW, hqsqtk, hsyl, hcomp, hKq, hMpeq, hMbL, ⟨le_top, hirrT.1.2⟩, ho2, hgen⟩, hqhat,
    hirrT⟩

end Bridge

end CFSG.Quasithin.H13
