module

public import CFSG.Sporadic.Schreier.LySylowParts
public import CFSG.Sporadic.SchreierLemmas.FrattiniCoset
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Sporadic.Schreier.LyDoubleCover

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier.Native
open scoped commutatorElement

@[expose] def sE
    (i : ℕ) : lyS := if h : i < 256 then ⟨sTree i, sTree_mem i h⟩ else 1

theorem sE_val
    {i : ℕ} (hi : i < 256) : (sE i : J) = sTree i := by simp [sE, hi]

theorem tm_sTab (i j : ℕ) : tm sTab i j = stm i j := rfl

theorem sE_mul
    {i j : ℕ} (hi : i < 256) (hj : j < 256) : sE i * sE j = sE (stm i j) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, sE_val hi, sE_val hj, sE_val (mulTab_parts.1 i hi j hj),
    sTree_mul i hi j hj]

theorem sE_inj
    {i j : ℕ} (hi : i < 256) (hj : j < 256) (h : sE i = sE j) : i = j := by
  apply sTree_inj hi hj
  rw [← sE_val hi, ← sE_val hj, h]

theorem sE_zero : sE 0 = 1 := by
  apply Subtype.ext
  rw [sE_val (by norm_num), sTree_zero]
  rfl

theorem exists_sE
    (g : lyS) : ∃ i < 256, sE i = g := by
  obtain ⟨g, hg⟩ := g
  let K : Subgroup J :=
    { carrier := {x | ∃ i < 256, sTree i = x}
      mul_mem' := by
        rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
        exact ⟨stm i j, mulTab_parts.1 i hi j hj, (sTree_mul i hi j hj).symm⟩
      one_mem' := ⟨0, by norm_num, sTree_zero⟩
      inv_mem' := by
        rintro _ ⟨i, hi, rfl⟩
        obtain ⟨h1, h2⟩ := tableFacts.inv i hi
        refine ⟨stinv i, h1, ?_⟩
        have := sTree_mul i hi (stinv i) h1
        rw [h2, sTree_zero] at this
        exact eq_inv_of_mul_eq_one_right this }
  have hle : lyS ≤ K := by
    rw [lyS, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨(sLam[k.val]!)[0]!, (enum_parts.2.2.2.2.1 k.val k.isLt).2 0 (by norm_num), ?_⟩
    rw [← sylowGen_mul_sTree k (by norm_num), sTree_zero, mul_one]
  obtain ⟨i, hi, he⟩ := hle hg
  exact ⟨i, hi, Subtype.ext (by rw [sE_val hi, he])⟩

@[expose] def sEquiv :
    Fin 256 ≃ lyS :=
  Equiv.ofBijective (fun i => sE i) ⟨fun i j h => Fin.ext (sE_inj i.isLt j.isLt h),
    fun g => by obtain ⟨i, hi, he⟩ := exists_sE g; exact ⟨⟨i, hi⟩, he⟩⟩

theorem card_lyS :
    Nat.card lyS = 256 := by
  rw [← Nat.card_congr sEquiv, Nat.card_fin]

theorem sE_six :
    (sE 6 : J) = lyz := by
  rw [sE_val (by norm_num)]
  have h := (repM_sTree 6 (by norm_num)).1
  rw [sylow_parts.2.1] at h
  exact h.unique repM_matA

theorem lyz_mem_lyS :
    lyz ∈ lyS := by rw [← sE_six]; exact (sE 6).2

theorem card_J_factorization : (Nat.card J).factorization 2 = 8 := by
  rw [card_J, show (51765179004000000 : ℕ) = 2 ^ 8 * 202207730484375 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

@[expose] def lySylow :
    Sylow 2 J :=
  Sylow.ofCard lyS (by rw [card_lyS, card_J_factorization]; norm_num)

theorem lySylow_coe :
    (lySylow : Subgroup J) = lyS := rfl

@[expose] def zS :
    lyS := ⟨lyz, lyz_mem_lyS⟩

theorem zS_eq :
    zS = sE 6 := Subtype.ext sE_six.symm

theorem orderOf_zS :
    orderOf zS = 2 := by
  rw [← Subgroup.orderOf_coe, show ((zS : lyS) : J) = a from rfl, orderOf_a]

theorem mem_zpowers_zS
    {g : lyS} : g ∈ Subgroup.zpowers zS ↔ g = 1 ∨ g = zS := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [← zpow_mod_orderOf, orderOf_zS, Nat.cast_ofNat]
    rcases Int.emod_two_eq k with h0 | h1
    · left; rw [h0, zpow_zero]
    · right; rw [h1, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem center_lyS :
    Subgroup.center lyS = Subgroup.zpowers zS := by
  ext g
  obtain ⟨i, hi, rfl⟩ := exists_sE g
  rw [mem_zpowers_zS, Subgroup.mem_center_iff, zS_eq]
  have key : (∀ h : lyS, h * sE i = sE i * h) ↔ ∀ j < 256, stm i j = stm j i := by
    constructor
    · intro H j hj
      have := H (sE j)
      rw [sE_mul hj hi, sE_mul hi hj] at this
      exact (sE_inj (mulTab_parts.1 j hj i hi) (mulTab_parts.1 i hi j hj) this).symm
    · intro H h
      obtain ⟨j, hj, rfl⟩ := exists_sE h
      rw [sE_mul hj hi, sE_mul hi hj, H j hj]
  rw [key, tableFacts.center i hi]
  constructor
  · rintro (rfl | rfl)
    · left; exact sE_zero
    · right; rfl
  · rintro (h | h)
    · left; exact sE_inj hi (by norm_num) (h.trans sE_zero.symm)
    · right; exact sE_inj hi (by norm_num) h

theorem sE_inv
    {i : ℕ} (hi : i < 256) : (sE i)⁻¹ = sE (stinv i) := by
  obtain ⟨h1, h2⟩ := tableFacts.inv i hi
  apply inv_eq_of_mul_eq_one_right
  rw [sE_mul hi h1, h2, sE_zero]

theorem stinv_lt
    {i : ℕ} (hi : i < 256) : stinv i < 256 := (tableFacts.inv i hi).1

theorem sE_commutator
    {a b : ℕ} (ha : a < 256) (hb : b < 256) :
    ⁅sE a, sE b⁆ = sE (tcomm sTab 256 a b) := by
  have hab := mulTab_parts.1 a ha b hb
  have h1 := mulTab_parts.1 _ hab _ (stinv_lt ha)
  rw [commutatorElement_def, sE_inv ha, sE_inv hb, sE_mul ha hb, sE_mul hab (stinv_lt ha),
    sE_mul h1 (stinv_lt hb), tcomm_eq]

theorem sD_lt
    {d : ℕ} (hd : d ∈ sD) : d < 256 := tableFacts.dLt d hd

theorem sD_get_mem
    {k : ℕ} (hk : k < 32) : sDT.1[k]! ∈ sD := by
  have hsz : sDT.1.size = 32 := by
    have := tableFacts.dLen
    simpa [sD] using this
  rw [getElem!_pos sDT.1 k (by rw [hsz]; exact hk)]
  exact Array.getElem_mem_toList _

theorem mem_commutator_lyS
    (g : lyS) : g ∈ commutator lyS ↔ ∃ d ∈ sD, sE d = g := by
  have hF := tableFacts
  constructor
  · intro hg
    rw [commutator_def, Subgroup.commutator_def] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g₁, -, g₂, -, rfl⟩ := hx
      obtain ⟨a, ha, rfl⟩ := exists_sE g₁
      obtain ⟨b, hb, rfl⟩ := exists_sE g₂
      exact ⟨_, hF.dComm a ha b hb, (sE_commutator ha hb).symm⟩
    | one => exact ⟨0, hF.dZero, sE_zero⟩
    | mul x y _ _ hx hy =>
      obtain ⟨d, hd, rfl⟩ := hx
      obtain ⟨e, he, rfl⟩ := hy
      exact ⟨stm d e, hF.dClosed d hd e he, (sE_mul (hF.dLt d hd) (hF.dLt e he)).symm⟩
    | inv x _ hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      exact ⟨stinv d, hF.dInv d hd, (sE_inv (hF.dLt d hd)).symm⟩
  · rintro ⟨d, hd, rfl⟩
    have key : ∀ k < 32, sE (sDT.1[k]!) ∈ commutator lyS := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · rw [hF.d0, sE_zero]; exact Subgroup.one_mem _
        · obtain ⟨hp, ha, hb, he⟩ := hF.dTree k hpos hk
          have hpk := ih _ hp (by omega)
          have hDp : sDT.1[sDT.2.1[k]!]! < 256 := hF.dLt _ (sD_get_mem (by omega))
          rw [← he, ← sE_mul (sD_lt (hF.dComm _ ha _ hb)) hDp, ← sE_commutator ha hb]
          exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
            (Subgroup.mem_top _)) hpk
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    have hk' : k < 32 := by rw [← hF.dLen]; exact hk
    have := key k hk'
    rwa [getElem!_pos sDT.1 k (by simpa [sD] using hk)] at this

theorem card_commutator_lyS :
    Nat.card (commutator lyS) = 32 := by
  have hF := tableFacts
  have e : (commutator lyS : Set lyS) = (sD.toFinset.image sE : Finset lyS) := by
    ext g
    simp only [SetLike.mem_coe, mem_commutator_lyS, Finset.coe_image, Set.mem_image,
      List.coe_toFinset, Set.mem_ofPred_eq]
  rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_image_of_injOn, List.toFinset_card_of_nodup hF.dNodup, hF.dLen]
  intro x hx y hy h
  exact sE_inj (hF.dLt x (by simpa using hx)) (hF.dLt y (by simpa using hy)) h

theorem zS_mem_commutator :
    zS ∈ commutator lyS :=
  (mem_commutator_lyS zS).2 ⟨6, tableFacts.dSix, zS_eq.symm⟩

theorem card_quotient_lyS :
    Nat.card (lyS ⧸ commutator lyS) = 8 := by
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator lyS)
  rw [card_lyS, card_commutator_lyS] at this
  omega

theorem isElementaryAbelian_quotient :
    CFSG.IsElementaryAbelian 2 (lyS ⧸ commutator lyS) where
  is_comm := ⟨fun x y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by rw [commutatorElement_def]; group
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    obtain ⟨i, hi, rfl⟩ := exists_sE x
    rw [pow_two, sE_mul hi hi, mem_commutator_lyS]
    exact ⟨_, tableFacts.dSq i hi, rfl⟩

theorem ea_comm {G : Type*} [Group G] {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 2 E)
    {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  have := hE.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem ea_sq {G : Type*} [Group G] {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 2 E)
    {x : G} (hx : x ∈ E) : x * x = 1 := by
  rw [← pow_two]
  exact @CFSG.elemPow_eq_one_of_isElementaryAbelian 2 G _ E hE x hx

theorem mk_ea {G : Type*} [Group G] (E : Subgroup G) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hs : ∀ x ∈ E, x * x = 1) : CFSG.IsElementaryAbelian 2 E :=
  CFSG.IsElementaryAbelian.two_of_forall_mul_self hc hs

@[expose] def Lists
    (l : List ℕ) (E : Subgroup lyS) : Prop :=
  (∀ i ∈ l, i < 256) ∧ ∀ i < 256, (i ∈ l ↔ sE i ∈ E)

theorem eq_of_lists
    {l : List ℕ} {E F : Subgroup lyS} (hE : Lists l E) (hF : Lists l F) :
    E = F := by
  ext g
  obtain ⟨i, hi, rfl⟩ := exists_sE g
  rw [← hE.2 i hi, hF.2 i hi]

theorem sEA_zero : sEA 0 = [[0]] := rfl

theorem ext_step
    {k : ℕ} (hk : k < 4) : extOK sTab 256 (sEA k) (sEA (k + 1)) = true := by
  interval_cases k
  · exact tableFacts.ext1
  · exact tableFacts.ext2
  · exact tableFacts.ext3
  · exact tableFacts.ext4

theorem mem_of_extOK {L L' : List (List ℕ)} (h : extOK sTab 256 L L' = true) {E : List ℕ}
    (hE : E ∈ L) {x : ℕ} (hx : x < 256) (hext : extendsBy sTab E x = true) :
    spanBy sTab E x ∈ L' := by
  unfold extOK at h
  rw [List.all_eq_true] at h
  have := h E hE
  rw [List.all_eq_true] at this
  have := this x (List.mem_range.2 hx)
  rw [hext] at this
  simpa using this

theorem mem_spanBy {E : List ℕ} {x i : ℕ} :
    i ∈ spanBy sTab E x ↔ i ∈ E ∨ ∃ e ∈ E, stm x e = i := by
  unfold spanBy
  rw [List.mem_mergeSort, List.mem_append, List.mem_map]
  rfl

theorem ea_chain :
    ∀ k ≤ 4, ∀ E : Subgroup lyS, CFSG.IsElementaryAbelian 2 E →
    Nat.card E = 2 ^ k → ∃ l ∈ sEA k, Lists l E := by
  intro k
  induction k with
  | zero =>
    intro _ E _ hE
    refine ⟨[0], by rw [sEA_zero]; exact List.mem_singleton_self _, ?_, fun i hi => ?_⟩
    · intro i hi; rw [List.mem_singleton] at hi; omega
    · rw [pow_zero] at hE
      have hbot : E = ⊥ := Subgroup.eq_bot_of_card_eq E hE
      rw [hbot, Subgroup.mem_bot, List.mem_singleton]
      constructor
      · rintro rfl; exact sE_zero
      · intro h; exact sE_inj hi (by norm_num) (h.trans sE_zero.symm)
  | succ k ih =>
    intro hk E hEA hE
    have hdvd : 2 ^ k ∣ Nat.card E := by rw [hE]; exact pow_dvd_pow 2 (Nat.le_succ k)
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    set E' : Subgroup lyS := K.map E.subtype with hE'def
    have hE'card : Nat.card E' = 2 ^ k := by
      rw [hE'def, Subgroup.card_map_of_injective E.subtype_injective, hK]
    have hE'E : E' ≤ E := Subgroup.map_subtype_le K
    have hE'EA : CFSG.IsElementaryAbelian 2 E' :=
      mk_ea E' (fun x hx y hy => ea_comm hEA (hE'E hx) (hE'E hy))
        (fun x hx => ea_sq hEA (hE'E hx))
    obtain ⟨l', hl', hlists⟩ := ih (by omega) E' hE'EA hE'card
    obtain ⟨x, hxE, hxE'⟩ : ∃ x ∈ E, x ∉ E' := by
      by_contra hcon
      push Not at hcon
      have := Nat.card_mono (Set.toFinite (E' : Set lyS)) (fun y hy => hcon y hy)
      simp only [SetLike.coe_sort_coe] at this
      rw [hE, hE'card, pow_succ] at this
      have hpos : 0 < 2 ^ k := by positivity
      omega
    obtain ⟨ix, hix, rfl⟩ := exists_sE x
    have hext : extendsBy sTab l' ix = true := by
      unfold extendsBy isInv
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true',
        List.all_eq_true, tm_sTab]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, fun e he => ?_⟩
      · rintro rfl; exact hxE' (by rw [sE_zero]; exact E'.one_mem)
      · apply sE_inj (mulTab_parts.1 ix hix ix hix) (by norm_num)
        rw [← sE_mul hix hix, ea_sq hEA hxE, sE_zero]
      · rw [Bool.eq_false_iff]
        intro hmem
        exact hxE' ((hlists.2 ix hix).1 (List.contains_iff_mem.1 hmem))
      · have he' := hlists.1 e he
        apply sE_inj (mulTab_parts.1 ix hix e he') (mulTab_parts.1 e he' ix hix)
        rw [← sE_mul hix he', ← sE_mul he' hix]
        exact ea_comm hEA hxE (hE'E ((hlists.2 e he').1 he))
    refine ⟨spanBy sTab l' ix, mem_of_extOK (ext_step (by omega)) hl' hix hext, ?_, ?_⟩
    · intro i hi
      rcases mem_spanBy.1 hi with h | ⟨e, he, rfl⟩
      · exact hlists.1 i h
      · exact mulTab_parts.1 ix hix e (hlists.1 e he)
    · intro i hi
      rw [mem_spanBy]
      constructor
      · rintro (h | ⟨e, he, rfl⟩)
        · exact hE'E ((hlists.2 i hi).1 h)
        · have he' := hlists.1 e he
          rw [← sE_mul hix he']
          exact E.mul_mem hxE (hE'E ((hlists.2 e he').1 he))
      · intro hiE
        by_cases hiE' : sE i ∈ E'
        · exact Or.inl ((hlists.2 i hi).2 hiE')
        · right
          have hidx : (E'.subgroupOf E).index = 2 := by
            have h1 := (E'.subgroupOf E).index_mul_card
            rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'E).toEquiv, hE, hE'card,
              pow_succ] at h1
            have hpos : 0 < 2 ^ k := by positivity
            exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, mul_comm])
          have hmem : (⟨(sE ix)⁻¹ * sE i, E.mul_mem (E.inv_mem hxE) hiE⟩ : E) ∈
              E'.subgroupOf E := by
            have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨(sE ix)⁻¹, E.inv_mem hxE⟩)
              (b := ⟨sE i, hiE⟩)).2
            apply this
            simp only [Subgroup.mem_subgroupOf]
            exact ⟨fun h => absurd (by simpa using E'.inv_mem h) hxE', fun h => absurd h hiE'⟩
          rw [Subgroup.mem_subgroupOf] at hmem
          obtain ⟨e, he, he'⟩ := exists_sE ((sE ix)⁻¹ * sE i)
          refine ⟨e, (hlists.2 e he).2 (he' ▸ hmem), ?_⟩
          apply sE_inj (mulTab_parts.1 ix hix e he) hi
          rw [← sE_mul hix he, he', mul_inv_cancel_left]

@[expose] def listSubgroup
    (l : List ℕ) (hl : ∀ i ∈ l, i < 256)
    (hc : ∀ a ∈ l, ∀ b ∈ l, stm a b ∈ l) (h0 : 0 ∈ l)
    (hinv : ∀ a ∈ l, stinv a ∈ l) : Subgroup lyS where
  carrier := {g | ∃ i ∈ l, sE i = g}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨stm a b, hc a ha b hb, (sE_mul (hl a ha) (hl b hb)).symm⟩
  one_mem' := ⟨0, h0, sE_zero⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨stinv a, hinv a ha, (sE_inv (hl a ha)).symm⟩

theorem lists_listSubgroup
    (l : List ℕ) (hl hc h0 hinv) :
    Lists l (listSubgroup l hl hc h0 hinv) := by
  refine ⟨hl, fun i hi => ⟨fun h => ⟨i, h, rfl⟩, ?_⟩⟩
  rintro ⟨j, hj, he⟩
  rw [sE_inj (hl j hj) hi he] at hj
  exact hj

theorem ea4_mem
    {E : List ℕ} (hE : E ∈ sEA 4) : (∀ i ∈ E, i < 256) ∧
    (∀ a ∈ E, ∀ b ∈ E, stm a b ∈ E) ∧ 0 ∈ E ∧ (∀ a ∈ E, stinv a ∈ E) ∧
    (∀ a ∈ E, a = 0 ∨ stm a a = 0) := by
  obtain ⟨hc, h0, hinvol⟩ := tableFacts.eaClosed E hE
  obtain ⟨-, -, hlt⟩ := tableFacts.eaLen E hE
  refine ⟨hlt, hc, h0, fun a ha => ?_, fun a ha => ?_⟩
  ·
    have hsq : stm a a = 0 := by
      rcases hinvol a ha with rfl | ⟨-, h⟩
      · exact mulTab_parts.2.1 0 (by norm_num)
      · exact h
    have : stinv a = a := by
      apply sE_inj (stinv_lt (hlt a ha)) (hlt a ha)
      rw [← sE_inv (hlt a ha)]
      apply inv_eq_of_mul_eq_one_right
      rw [sE_mul (hlt a ha) (hlt a ha), hsq, sE_zero]
    rw [this]; exact ha
  · rcases hinvol a ha with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h

@[expose] def eaSub
    {E : List ℕ} (hE : E ∈ sEA 4) : Subgroup lyS :=
  listSubgroup E (ea4_mem hE).1 (ea4_mem hE).2.1 (ea4_mem hE).2.2.1 (ea4_mem hE).2.2.2.1

theorem eaSub_ea
    {E : List ℕ} (hE : E ∈ sEA 4) : CFSG.IsElementaryAbelian 2 (eaSub hE) := by
  obtain ⟨hlt, -, -, -, hsq⟩ := ea4_mem hE
  apply mk_ea
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [sE_mul (hlt a ha) (hlt b hb), sE_mul (hlt b hb) (hlt a ha),
      tableFacts.eaComm E hE a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [sE_mul (hlt a ha) (hlt a ha)]
    rcases hsq a ha with rfl | h
    · rw [mulTab_parts.2.1 0 (by norm_num), sE_zero]
    · rw [h, sE_zero]

theorem eaSub_card
    {E : List ℕ} (hE : E ∈ sEA 4) : Nat.card (eaSub hE) = 16 := by
  obtain ⟨hlen, hnd, hlt⟩ := tableFacts.eaLen E hE
  have e : (eaSub hE : Set lyS) = (E.toFinset.image sE : Finset lyS) := by
    ext g
    simp only [eaSub, listSubgroup, Subgroup.coe_set_mk, Finset.coe_image, List.coe_toFinset]
    rfl
  rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd, hlen]
  intro x hx y hy h
  exact sE_inj (hlt x (by simpa using hx)) (hlt y (by simpa using hy)) h

theorem e16a_mem :
    e16a ∈ sEA 4 := by rw [tableFacts.ea4]; exact List.mem_cons_self
theorem e16b_mem :
    e16b ∈ sEA 4 := by rw [tableFacts.ea4]; simp

@[expose] def lyE1 :
    Subgroup lyS := eaSub e16a_mem
@[expose] def lyE2 :
    Subgroup lyS := eaSub e16b_mem

theorem lists_eaSub
    {E : List ℕ} (hE : E ∈ sEA 4) : Lists E (eaSub hE) :=
  lists_listSubgroup _ _ _ _ _

theorem ea16_iff
    (E : Subgroup lyS) :
    (CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 16) ↔ E = lyE1 ∨ E = lyE2 := by
  constructor
  · rintro ⟨hEA, hcard⟩
    obtain ⟨l, hl, hlists⟩ := ea_chain 4 le_rfl E hEA (by rw [hcard]; norm_num)
    have hl' := hl
    rw [tableFacts.ea4] at hl'
    rcases List.mem_pair.1 hl' with rfl | rfl
    · left; exact eq_of_lists hlists (lists_eaSub e16a_mem)
    · right; exact eq_of_lists hlists (lists_eaSub e16b_mem)
  · rintro (rfl | rfl)
    · exact ⟨eaSub_ea _, eaSub_card _⟩
    · exact ⟨eaSub_ea _, eaSub_card _⟩

theorem lyE1_ne_lyE2 :
    lyE1 ≠ lyE2 := by
  intro h
  have h3a : 3 ∈ e16a := by decide
  have h3b : 3 ∉ e16b := by decide
  have := (lists_eaSub e16a_mem).2 3 (by norm_num)
  rw [show eaSub e16a_mem = lyE2 from h] at this
  exact h3b ((lists_eaSub e16b_mem).2 3 (by norm_num) |>.2 (this.1 h3a))

@[expose] def qSub :
    Subgroup lyS :=
  listSubgroup qList tableFacts.qLt tableFacts.qClosed tableFacts.qZero tableFacts.qInv

theorem lists_qSub :
    Lists qList qSub := lists_listSubgroup _ _ _ _ _

theorem sylowElt_q
    {q : ℕ} (hq : q ∈ qList) : sylowElt q = (sE q : J) := by
  rw [sylowElt_eq (tableFacts.qLt q hq), sE_val (tableFacts.qLt q hq)]

theorem lyQ_eq_map :
    lyQ = qSub.map lyS.subtype := by
  apply le_antisymm
  · rw [lyQ, Subgroup.closure_le]
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨sE q, ⟨q, hq, rfl⟩, (sylowElt_q hq).symm⟩
  · rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    rw [Subgroup.coe_subtype, ← sylowElt_q hq]
    exact Subgroup.subset_closure ⟨q, hq, rfl⟩

theorem qSub_eq_sup :
    qSub = lyE1 ⊔ lyE2 := by
  apply le_antisymm
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := tableFacts.qProd q hq
    rw [← sE_mul ((lists_eaSub e16a_mem).1 a ha) ((lists_eaSub e16b_mem).1 b hb)]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, ha, rfl⟩)
      (Subgroup.mem_sup_right ⟨b, hb, rfl⟩)
  · apply sup_le
    · rintro _ ⟨a, ha, rfl⟩; exact ⟨a, tableFacts.qSub _ e16a_mem a ha, rfl⟩
    · rintro _ ⟨b, hb, rfl⟩; exact ⟨b, tableFacts.qSub _ e16b_mem b hb, rfl⟩

theorem lyQ_eq :

    lyQ = (lyE1 ⊔ lyE2).map lyS.subtype := by rw [lyQ_eq_map, qSub_eq_sup]

theorem card_qSub :
    Nat.card qSub = 64 := by
  have e : (qSub : Set lyS) = (qList.toFinset.image sE : Finset lyS) := by
    ext g
    simp only [qSub, listSubgroup, Subgroup.coe_set_mk, Finset.coe_image, List.coe_toFinset]
    rfl
  rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_image_of_injOn, List.toFinset_card_of_nodup tableFacts.qNodup, tableFacts.qLen]
  intro x hx y hy h
  exact sE_inj (tableFacts.qLt x (by simpa using hx)) (tableFacts.qLt y (by simpa using hy)) h

theorem card_lyQ :
    Nat.card lyQ = 64 := by
  rw [lyQ_eq_map, Subgroup.card_map_of_injective lyS.subtype_injective, card_qSub]

theorem lyQ_le :

    lyQ ≤ lyS := by rw [lyQ_eq_map]; exact Subgroup.map_subtype_le _

theorem lyQ_subgroupOf :
    lyQ.subgroupOf lyS = lyE1 ⊔ lyE2 := by
  rw [lyQ_eq, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective lyS.subtype_injective]

theorem mem_lyQ
    {x : J} : x ∈ lyQ ↔ ∃ q ∈ qList, (sE q : J) = x := by
  rw [lyQ_eq_map]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨sE q, ⟨q, hq, rfl⟩, rfl⟩

theorem isKleinFour_of_card_four {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem mem_center_lyQ
    {q : ℕ} (hq : q ∈ qList) (hqQ : (sE q : J) ∈ lyQ) :
    (⟨(sE q : J), hqQ⟩ : lyQ) ∈ Subgroup.center lyQ ↔ q ∈ zqList := by
  rw [Subgroup.mem_center_iff, ← tableFacts.qCenter q hq]
  have hql := tableFacts.qLt q hq
  constructor
  · intro H r hr
    have hrl := tableFacts.qLt r hr
    have := congrArg Subtype.val (H ⟨(sE r : J), mem_lyQ.2 ⟨r, hr, rfl⟩⟩)
    simp only [Subgroup.coe_mul] at this
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, sE_mul hrl hql, sE_mul hql hrl] at this
    exact (sE_inj (mulTab_parts.1 r hrl q hql) (mulTab_parts.1 q hql r hrl)
      (Subtype.ext this)).symm
  · intro H y
    obtain ⟨r, hr, hry⟩ := mem_lyQ.1 y.2
    have hrl := tableFacts.qLt r hr
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hry, ← Subgroup.coe_mul, ← Subgroup.coe_mul, sE_mul hrl hql, sE_mul hql hrl, H r hr]

theorem mem_center_lyQ_iff
    (x : lyQ) :
    x ∈ Subgroup.center lyQ ↔ ∃ q ∈ zqList, (sE q : J) = x := by
  obtain ⟨q, hq, hqx⟩ := mem_lyQ.1 x.2
  have hxe : x = ⟨(sE q : J), mem_lyQ.2 ⟨q, hq, rfl⟩⟩ := Subtype.ext hqx.symm
  constructor
  · intro hx
    rw [hxe, mem_center_lyQ hq] at hx
    exact ⟨q, hx, hqx⟩
  · rintro ⟨r, hr, hrx⟩
    have hrQ := (tableFacts.zq r hr).1
    have : x = ⟨(sE r : J), mem_lyQ.2 ⟨r, hrQ, rfl⟩⟩ := Subtype.ext hrx.symm
    rw [this, mem_center_lyQ hrQ]
    exact hr

theorem isKleinFour_center_lyQ :
    IsKleinFour (Subgroup.center lyQ) := by
  have hzq : ∀ q ∈ zqList, q < 256 := fun q hq => tableFacts.qLt q (tableFacts.zq q hq).1
  apply isKleinFour_of_card_four
  · rw [← Subgroup.card_map_of_injective lyQ.subtype_injective]
    have e : (((Subgroup.center lyQ).map lyQ.subtype : Subgroup J) : Set J) =
        ((zqList.toFinset.image fun q => (sE q : J)) : Finset J) := by
      ext x
      simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Subgroup.coe_subtype,
        Finset.coe_image, List.coe_toFinset, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (mem_center_lyQ_iff y).1 hy
      · rintro ⟨q, hq, rfl⟩
        exact ⟨⟨_, mem_lyQ.2 ⟨q, (tableFacts.zq q hq).1, rfl⟩⟩,
          (mem_center_lyQ_iff _).2 ⟨q, hq, rfl⟩, rfl⟩
    rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      Finset.card_image_of_injOn]
    · decide
    · intro x hx y hy h
      exact sE_inj (hzq x (by simpa using hx)) (hzq y (by simpa using hy)) (Subtype.ext h)
  · intro x
    obtain ⟨⟨y, hyQ⟩, hy⟩ := x
    obtain ⟨q, hq, rfl⟩ := (mem_center_lyQ_iff _).1 hy
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_two, ← Subgroup.coe_mul, sE_mul (hzq q hq) (hzq q hq), (tableFacts.zq q hq).2,
      sE_zero]
    rfl

theorem ea_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : CFSG.IsElementaryAbelian 2 G) : CFSG.IsElementaryAbelian 2 H :=
  CFSG.IsElementaryAbelian.of_mulEquiv e hG

theorem map_ea16
    {E : Subgroup lyS} (hE : E = lyE1 ∨ E = lyE2) (f : lyS →* lyS)
    (hf : Function.Injective f) : E.map f = lyE1 ∨ E.map f = lyE2 := by
  have h := (ea16_iff E).2 hE
  apply (ea16_iff _).1
  refine ⟨ea_of_mulEquiv (G := E) (H := E.map f) (E.equivMapOfInjective f hf) h.1, ?_⟩
  rw [Subgroup.card_map_of_injective hf, h.2]

theorem sup_le_of_maps
    {f : lyS →* lyS} (hf : Function.Injective f) :
    (lyE1 ⊔ lyE2).map f ≤ lyE1 ⊔ lyE2 := by
  rw [Subgroup.map_sup]
  apply sup_le
  · rcases map_ea16 (Or.inl rfl) f hf with h | h <;> rw [h]
    · exact le_sup_left
    · exact le_sup_right
  · rcases map_ea16 (Or.inr rfl) f hf with h | h <;> rw [h]
    · exact le_sup_left
    · exact le_sup_right

theorem lyQ_characteristic :
    (lyQ.subgroupOf lyS).Characteristic := by
  rw [lyQ_subgroupOf, Subgroup.characteristic_iff_map_le]
  intro φ
  exact sup_le_of_maps φ.injective

theorem lyQ_weakly_closed
    (g : J) (hg : lyQ.map (MulAut.conj g).toMonoidHom ≤ lyS) :
    lyQ.map (MulAut.conj g).toMonoidHom = lyQ := by
  set φ := (MulAut.conj g).toMonoidHom
  have hφ : Function.Injective φ := (MulAut.conj g).injective
  have key : ∀ E : Subgroup lyS, (E = lyE1 ∨ E = lyE2) → (E.map lyS.subtype).map φ ≤ lyQ := by
    intro E hE
    have hEQ : E.map lyS.subtype ≤ lyQ := by
      rw [lyQ_eq]
      apply Subgroup.map_mono
      rcases hE with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    have hle : (E.map lyS.subtype).map φ ≤ lyS := le_trans (Subgroup.map_mono hEQ) hg
    set F := ((E.map lyS.subtype).map φ).subgroupOf lyS
    have h16 := (ea16_iff E).2 hE
    have eqv : E ≃* F :=
      ((E.equivMapOfInjective lyS.subtype lyS.subtype_injective).trans
        ((E.map lyS.subtype).equivMapOfInjective φ hφ)).trans
        (Subgroup.subgroupOfEquivOfLe hle).symm
    have hF : F = lyE1 ∨ F = lyE2 :=
      (ea16_iff F).1 ⟨ea_of_mulEquiv (G := E) (H := F) eqv h16.1,
        by rw [← Nat.card_congr eqv.toEquiv, h16.2]⟩
    have hmapF : (E.map lyS.subtype).map φ = F.map lyS.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hle]
    rw [hmapF, lyQ_eq]
    apply Subgroup.map_mono
    rcases hF with h | h <;> rw [h]
    · exact le_sup_left
    · exact le_sup_right
  have hle : lyQ.map φ ≤ lyQ := by
    have e : lyQ.map φ = (lyE1.map lyS.subtype).map φ ⊔ (lyE2.map lyS.subtype).map φ := by
      rw [lyQ_eq, Subgroup.map_sup, Subgroup.map_sup]
    rw [e]
    exact sup_le (key lyE1 (Or.inl rfl)) (key lyE2 (Or.inr rfl))
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective hφ])

theorem sE_pow
    {i : ℕ} (hi : i < 256) :
    ∀ n, tpow sTab i n < 256 ∧ sE i ^ n = sE (tpow sTab i n) := by
  intro n
  induction n with
  | zero => exact ⟨by rw [tpow_eq_zero]; norm_num, by rw [pow_zero, tpow_eq_zero, sE_zero]⟩
  | succ n ih =>
    refine ⟨by rw [tpow_succ]; exact mulTab_parts.1 _ ih.1 _ hi, ?_⟩
    rw [pow_succ, ih.2, sE_mul ih.1 hi, tpow_succ]

theorem mem_center_sE
    {i : ℕ} (hi : i < 256) :
    sE i ∈ Subgroup.center lyS ↔ i = 0 ∨ i = 6 := by
  rw [center_lyS, mem_zpowers_zS, zS_eq]
  constructor
  · rintro (h | h)
    · left; exact sE_inj hi (by norm_num) (h.trans sE_zero.symm)
    · right; exact sE_inj hi (by norm_num) h
  · rintro (rfl | rfl)
    · left; exact sE_zero
    · right; rfl

theorem quot_pow_eq_one
    {i : ℕ} (hi : i < 256) (n : ℕ) :
    ((sE i : lyS) : lyS ⧸ Subgroup.center lyS) ^ n = 1 ↔ tpow sTab i n = 0 ∨ tpow sTab i n = 6 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, (sE_pow hi n).2,
    mem_center_sE (sE_pow hi n).1]

theorem orderOf_quotient_center
    (i : ℕ) (hi : i < 256) :
    orderOf ((sE i : lyS) : lyS ⧸ Subgroup.center lyS) = 8 ↔
      ord8Mod sTab [0, 6] i = true := by
  have h8 := quot_pow_eq_one hi 8
  have h4 := quot_pow_eq_one hi 4
  have hc : ∀ n : ℕ, [0, 6].contains n = true ↔ n = 0 ∨ n = 6 := fun n => by
    rw [List.contains_iff_mem]; simp
  have hord : ord8Mod sTab [0, 6] i = true ↔
      (tpow sTab i 8 = 0 ∨ tpow sTab i 8 = 6) ∧ ¬(tpow sTab i 4 = 0 ∨ tpow sTab i 4 = 6) := by
    unfold ord8Mod
    rw [Bool.and_eq_true_iff, Bool.not_eq_true', ← Bool.not_eq_true, hc, hc]
  rw [hord, ← h8, ← h4]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro ho
    refine ⟨by rw [← ho]; exact pow_orderOf_eq_one _, fun h => ?_⟩
    have := orderOf_dvd_of_pow_eq_one h
    rw [ho] at this
    norm_num at this
  · rintro ⟨e8, e4⟩
    exact orderOf_eq_prime_pow (p := 2) (n := 2) e4 e8

theorem isSolvable_mulAut_lyS :
    Group.IsSolvable (MulAut lyS) := by
  have hS : IsPGroup 2 lyS := IsPGroup.of_card (n := 8) (by rw [card_lyS]; norm_num)
  apply CFSG.Sporadic.SchreierLemmas.characteristic_Frattini_coset_automorphisms hS
    (Subgroup.center lyS) (k := 8) isElementaryAbelian_quotient card_quotient_lyS
  have hF := tableFacts
  have h38 : (38 : ℕ) < 256 := by norm_num
  have hmk : ∀ i < 256, ∀ j < 256, ((sE i : lyS) : lyS ⧸ commutator lyS) = (sE j : lyS) ↔
      stm (stinv i) j ∈ sD := by
    intro i hi j hj
    rw [QuotientGroup.eq, sE_inv hi, sE_mul (stinv_lt hi) hj, mem_commutator_lyS]
    constructor
    · rintro ⟨d, hd, he⟩
      rw [sE_inj (hF.dLt d hd) (mulTab_parts.1 _ (stinv_lt hi) _ hj) he] at hd
      exact hd
    · intro h
      exact ⟨_, h, rfl⟩
  refine ⟨((sE 38 : lyS) : lyS ⧸ commutator lyS), ⟨?_, ?_⟩, ?_⟩
  · rw [Ne, QuotientGroup.eq_one_iff, mem_commutator_lyS]
    rintro ⟨d, hd, he⟩
    rw [sE_inj (hF.dLt d hd) h38 he] at hd
    exact hF.i0Out hd
  · intro y hy
    obtain ⟨j, hj, rfl⟩ := exists_sE y
    rw [eq_comm, hmk 38 h38 j hj] at hy
    obtain ⟨d, hd⟩ : ∃ d, d = stm (stinv 38) j := ⟨_, rfl⟩
    rw [← hd] at hy
    have hdl : d < 256 := hF.dLt d hy
    have hj' : stm 38 d = j := by
      apply sE_inj (mulTab_parts.1 38 h38 d hdl) hj
      rw [← sE_mul (i := 38) h38 hdl, hd, ← sE_mul (stinv_lt h38) hj, ← sE_inv h38,
        mul_inv_cancel_left]
    rw [← hj', orderOf_quotient_center _ (mulTab_parts.1 38 h38 d hdl)]
    exact hF.i0Ord d hy
  · intro c ⟨hc1, hc8⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨i, hi, rfl⟩ := exists_sE y
    rcases hF.i0Uniq i hi with h | ⟨d, hd, hdo⟩ | h
    · exfalso
      apply hc1
      rw [QuotientGroup.eq_one_iff, mem_commutator_lyS]
      exact ⟨i, h, rfl⟩
    · exfalso
      have hdl := hF.dLt d hd
      have hidl := mulTab_parts.1 i hi d hdl
      have hy : ((sE (stm i d) : lyS) : lyS ⧸ commutator lyS) = (sE i : lyS) := by
        rw [QuotientGroup.eq, ← sE_mul hi hdl, mul_inv_rev, mul_assoc, inv_mul_cancel,
          mul_one]
        exact Subgroup.inv_mem _ ((mem_commutator_lyS _).2 ⟨d, hd, rfl⟩)
      have h' := (orderOf_quotient_center _ hidl).1 (hc8 _ hy)
      exact Bool.false_ne_true (hdo.symm.trans h')
    · exact ((hmk 38 h38 i hi).2 h).symm

theorem sylowGen_mem_lyC'
    (k : Fin 6) : sylowGen k ∈ lyC := by
  unfold sylowGen
  split_ifs
  · exact evalWord_mem fun l _ => cStar_mem _
  · exact lyz_mem_lyC

theorem lyS_le_lyC : lyS ≤ lyC := by
  rw [lyS, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact sylowGen_mem_lyC' k

theorem commutator_alternating_eleven : commutator (alternatingGroup (Fin 11)) = ⊤ := by
  have := alternatingGroup.isSimpleGroup (α := Fin 11) (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 11))) with
    h | h
  · exfalso
    have hmem := Subgroup.commutator_mem_commutator (Subgroup.mem_top
      (⟨pGen 0, pGen_mem_alternating 0⟩ : alternatingGroup (Fin 11)))
      (Subgroup.mem_top (⟨pGen 1, pGen_mem_alternating 1⟩ : alternatingGroup (Fin 11)))
    rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    have := congrArg Subtype.val hmem
    simp only [Subgroup.coe_mul] at this
    exact absurd this (by decide +kernel)
  · exact h

theorem zC_mem_commutator :
    zC ∈ commutator lyC := by
  have hle : (commutator lyS).map (Subgroup.inclusion lyS_le_lyC) ≤ commutator lyC := by
    rw [map_commutator_eq, _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  exact hle ⟨zS, zS_mem_commutator, rfl⟩

theorem commutator_quotient_zGroup :
    commutator (lyC ⧸ zGroup) = ⊤ := by
  have h : (commutator (alternatingGroup (Fin 11))).map lyCoverEquiv.symm.toMonoidHom =
      commutator (lyC ⧸ zGroup) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ lyCoverEquiv.symm.surjective,
      _root_.commutator_def]
  rw [← h, commutator_alternating_eleven,
    Subgroup.map_top_of_surjective _ lyCoverEquiv.symm.surjective]

theorem commutator_lyC :
    commutator lyC = ⊤ := by
  rw [eq_top_iff]
  intro c _
  have hmap : (commutator lyC).map (QuotientGroup.mk' zGroup) = commutator (lyC ⧸ zGroup) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _
      (QuotientGroup.mk'_surjective zGroup), _root_.commutator_def]
  have hc : (c : lyC ⧸ zGroup) ∈ (commutator lyC).map (QuotientGroup.mk' zGroup) := by
    rw [hmap, commutator_quotient_zGroup]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, hnc⟩ := hc
  have hz : n⁻¹ * c ∈ zGroup := by
    rw [← QuotientGroup.eq]
    exact hnc
  have hz' : n⁻¹ * c ∈ commutator lyC := by
    rcases mem_zGroup.1 hz with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact zC_mem_commutator
  have := Subgroup.mul_mem _ hn hz'
  rwa [mul_inv_cancel_left] at this

theorem sylow_structure_automorphisms :
    (∃ P : Sylow 2 J, (P : Subgroup J) = lyS) ∧ Nat.card lyS = 256 ∧
    Subgroup.center lyS = Subgroup.zpowers ⟨lyz, lyz_mem_lyS⟩ ∧
    Nat.card (commutator lyS) = 32 ∧ (⟨lyz, lyz_mem_lyS⟩ : lyS) ∈ commutator lyS ∧
    CFSG.IsElementaryAbelian 2 (lyS ⧸ commutator lyS) ∧ Nat.card (lyS ⧸ commutator lyS) = 8 ∧
    (∃ E₁ E₂ : Subgroup lyS, E₁ ≠ E₂ ∧
      (∀ E : Subgroup lyS, (CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 16) ↔
        E = E₁ ∨ E = E₂) ∧
      lyQ = (E₁ ⊔ E₂).map lyS.subtype) ∧
    Nat.card lyQ = 64 ∧ Nonempty (Subgroup.center lyQ ≃* Multiplicative (ZMod 2 × ZMod 2)) ∧
    lyQ ≤ lyS ∧ (lyQ.subgroupOf lyS).Characteristic ∧
    (∀ g : J, lyQ.map (MulAut.conj g).toMonoidHom ≤ lyS →
      lyQ.map (MulAut.conj g).toMonoidHom = lyQ) ∧
    Group.IsSolvable (MulAut lyS) ∧ commutator lyC = ⊤ := by
  have := isKleinFour_center_lyQ
  exact ⟨⟨lySylow, rfl⟩, card_lyS, center_lyS, card_commutator_lyS, zS_mem_commutator,
    isElementaryAbelian_quotient, card_quotient_lyS,
    ⟨lyE1, lyE2, lyE1_ne_lyE2, ea16_iff, lyQ_eq⟩, card_lyQ,
    IsKleinFour.nonempty_mulEquiv (G₁ := Subgroup.center lyQ),
    lyQ_le, lyQ_characteristic, lyQ_weakly_closed, isSolvable_mulAut_lyS, commutator_lyC⟩

end CFSG.Sporadic.LySchreier
