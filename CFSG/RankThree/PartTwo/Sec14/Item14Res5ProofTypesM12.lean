module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesModel
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofGenM12
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
public import CFSG.RankThree.PartTwo.Sec12.KS128BCensusM12
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Res5TypesM12

open CFSG.GH74.M12.Hyp (G12 tbl tid tmul tpow)
open CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
  Res5GenM12 Res5Types Subgroup

theorem le_of_index_eq_pow_three {C : Type*} [Group C] [Finite C] (V : Subgroup C) [V.Normal]
    {k : ℕ} (hV : V.index = 3 ^ k) {U : Subgroup C} (hU3 : ¬ 3 ∣ Nat.card U) : U ≤ V := by
  have h1 : Nat.card (U.map (QuotientGroup.mk' V)) ∣ 3 ^ k := by
    rw [← hV, Subgroup.index]
    exact Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card (U.map (QuotientGroup.mk' V)) ∣ Nat.card U := Subgroup.card_map_dvd _ _
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  have hm0 : m = 0 := by
    rcases m with _ | m
    · rfl
    · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero m)).trans (hm ▸ h2)) hU3
  have hbot : U.map (QuotientGroup.mk' V) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [hm, hm0, pow_zero])
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

theorem eq_of_le_four {X : Type*} [Group X] {V U : Subgroup X} {a b t : X}
    (hV : ∀ v, v ∈ V ↔ v = 1 ∨ v = a ∨ v = b ∨ v = a * b)
    (hta : t * a * t⁻¹ = a * b) (htb : t * b * t⁻¹ = a)
    (htU : t ∈ Subgroup.normalizer (U : Set X)) (hUV : U ≤ V) (hU : U ≠ ⊥) : U = V := by
  obtain ⟨u, huU, hu1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left hU
  have hcU : ∀ g ∈ U, t * g * t⁻¹ ∈ U := fun g hg => (Subgroup.mem_normalizer_iff.mp htU g).mp hg
  have hcU' : ∀ g ∈ U, t⁻¹ * g * t ∈ U := fun g hg => by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem htU) g).mp hg
    simpa using h1
  have haU : a ∈ U := by
    rcases (hV u).mp (hUV huU) with h | h | h | h
    · exact absurd h hu1
    · exact h ▸ huU
    · have h1 := hcU u huU
      rwa [h, htb] at h1
    · have h1 := hcU' u huU
      rw [h, ← hta] at h1
      simpa [mul_assoc] using h1
  have habU : a * b ∈ U := hta ▸ hcU a haU
  have hbU : b ∈ U := by
    have h1 := mul_mem (inv_mem haU) habU
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1
  refine le_antisymm hUV fun v hv => ?_
  rcases (hV v).mp hv with rfl | rfl | rfl | rfl
  · exact one_mem U
  · exact haU
  · exact hbU
  · exact habU

theorem wP_mem_VT : ∀ i : Fin 3, ∀ j : Fin 2, tbl (wP i j) ∈ VT i := by
  decide +kernel

theorem mem_W_iff (i : Fin 3) (v : G12) :
    v ∈ W i ↔ v = 1 ∨ v = wG i 0 ∨ v = wG i 1 ∨ v = wG i 0 * wG i 1 :=
  Iff.rfl

theorem W_eq_V (i : Fin 3) : W i = V i := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_V, card_W])
  intro v hv
  have h0 : wG i 0 ∈ V i := mem_V.mpr (wP_mem_VT i 0)
  have h1 : wG i 1 ∈ V i := mem_V.mpr (wP_mem_VT i 1)
  rcases (mem_W_iff i v).mp hv with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact h0
  · exact h1
  · exact mul_mem h0 h1

theorem ai_mem_A (i : Fin 3) : ai i ∈ basisA.sub :=
  mul_mem (pow_mem z_mem_A _) a_mem_A

theorem aiT_ne_tid : ∀ i : Fin 3, aiT i ≠ tid := by
  decide +kernel

theorem ai_ne_one (i : Fin 3) : ai i ≠ 1 := fun h => by
  have h1 : tbl (ai i).1 = tbl (1 : G12).1 := congrArg (fun g : G12 => tbl g.1) h
  rw [tbl_ai, tblG_one] at h1
  exact aiT_ne_tid i h1

theorem z_val : ((⁅x, y⁆ : G12) : Equiv.Perm (Fin 12)) = zP := by
  change ⁅((x : G12) : Equiv.Perm (Fin 12)), ((y : G12) : Equiv.Perm (Fin 12))⁆ = zP
  rw [show ((x : G12) : Equiv.Perm (Fin 12)) = xP from wordP_wX,
    show ((y : G12) : Equiv.Perm (Fin 12)) = yP from wordP_wY, commutator_xP_yP]

theorem z_facts : ∀ i : Fin 3,
    (zP * zP) * wP i 0 * (zP * zP)⁻¹ = wP i 0 * wP i 1 ∧
      (zP * zP) * wP i 1 * (zP * zP)⁻¹ = wP i 0 ∧ wP i 0 * zP ≠ zP * wP i 0 ∧
      wP i 1 * zP ≠ zP * wP i 1 ∧ wP i 0 * wP i 1 * zP ≠ zP * (wP i 0 * wP i 1) := by
  decide +kernel

theorem z2_conj (i : Fin 3) :
    ⁅x, y⁆ ^ 2 * wG i 0 * (⁅x, y⁆ ^ 2)⁻¹ = wG i 0 * wG i 1 ∧
      ⁅x, y⁆ ^ 2 * wG i 1 * (⁅x, y⁆ ^ 2)⁻¹ = wG i 0 := by
  obtain ⟨h1, h2, -⟩ := z_facts i
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, z_val, pow_two]
    exact h1
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, z_val, pow_two]
    exact h2

theorem eq_one_of_mem_W {i : Fin 3} {u : G12} (hu : u ∈ W i) (huz : u * ⁅x, y⁆ = ⁅x, y⁆ * u) :
    u = 1 := by
  obtain ⟨-, -, h3, h4, h5⟩ := z_facts i
  have hval := congrArg Subtype.val huz
  simp only [Subgroup.coe_mul, z_val] at hval
  rcases (mem_W_iff i u).mp hu with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd hval h3
  · exact absurd hval h4
  · exact absurd hval h5

theorem theta_ai (i : Fin 3) :
    inSubgroup (aschbacherSolvableCore 3) (centralizer ({ai i} : Set G12)) = V i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({ai i} : Set G12) with hC
  obtain ⟨-, -, hθ3, hmax, -⟩ := solvable_prime_complement_core_characterization (H := ↥C)
    Nat.prime_three
  have hp : IsPGroup 2 ((V i).subgroupOf C) := (isPGroup_V i).comap_of_injective _ (by
    intro a b h; exact Subtype.ext (by simpa using congrArg Subtype.val h))
  have := normal_V i
  have hs : Group.IsSolvable ((V i).subgroupOf C) := by
    have := hp.isNilpotent
    infer_instance
  have hV' : (V i).subgroupOf C ≤ aschbacherSolvableCore 3 ↥C := hmax _ (normal_V i) hs (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (V_le_C i)).toEquiv, card_V]
    norm_num)
  have h1 : V i ≤ inSubgroup (aschbacherSolvableCore 3) C := fun v hv =>
    ⟨⟨v, V_le_C i hv⟩, hV' (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
  refine (Subgroup.eq_of_le_of_card_ge h1 ?_).symm
  rw [card_V, inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
  have hdvd : Nat.card (aschbacherSolvableCore 3 ↥C) ∣ 4 * 9 := by
    rw [show 4 * 9 = Nat.card C from (card_C i).symm]
    exact Subgroup.card_subgroup_dvd_card _
  have hcop : Nat.Coprime (Nat.card (aschbacherSolvableCore 3 ↥C)) 9 :=
    (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)).symm
  exact Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hdvd)

theorem aut_eq_one_M12
    {τ : MulAut G12}
    (hτ : ∀ p ∈ basisA.sub, τ p = p) {n : ℕ} (hn : ¬ 3 ∣ n) (hτn : τ ^ n = 1) : τ = 1 := by
  have hW : ∀ i, ∀ v ∈ W i, τ v = v := by
    intro i
    have hai : τ (ai i) = ai i := hτ _ (ai_mem_A i)
    have hτV : ∀ v ∈ W i, τ v ∈ W i := fun v hv => by
      rw [W_eq_V, ← theta_ai, ← map_theta_centralizer_eq hai]
      exact ⟨v, (theta_ai i).symm ▸ (W_eq_V i) ▸ hv, rfl⟩
    have hne : ∀ {u w : G12}, (u : Equiv.Perm (Fin 12)) ≠ w → u ≠ w := fun h e => h (e ▸ rfl)
    obtain ⟨-, -, -, f1, f2, f3⟩ := wP_facts i
    obtain ⟨h1, h2⟩ := z2_conj i
    exact fix_four hn hτn (mem_W_iff i) hτV (wG_sq0 i) (wG_sq1 i) (wG_comm i) (hne f1)
      (hne f2) (hne f3) (hτ _ (pow_mem z_mem_A 2)) h1 h2
  refine eq_one_of_top_le_fixSubgroup ?_
  rw [← iSup_W_eq_top]
  exact iSup_le fun i v hv => hW i v hv

theorem A_comm {f g : G12} (hf : f ∈ basisA.sub) (hg : g ∈ basisA.sub) : f * g = g * f :=
  congrArg Subtype.val (basisA.isElementaryAbelian.toIsMulCommutative.is_comm.comm ⟨f, hf⟩ ⟨g, hg⟩)

theorem A_le_normalizer_centralizer {e : G12} (he : e ∈ basisA.sub) :
    basisA.sub ≤ normalizer ((centralizer ({e} : Set G12) : Subgroup G12) : Set G12) :=
  fun _ hf => Subgroup.le_normalizer (mem_centralizer_singleton_iff.mpr (A_comm hf he))

theorem centralizer_cases {e : G12} (he : e ∈ basisA.sub) (he1 : e ≠ 1) :
    centralizer ({e} : Set G12) = centralizer ({⁅x, y⁆} : Set G12) ∨
      ∃ k : Fin 3, centralizer ({e} : Set G12) = centralizer ({ai k} : Set G12) := by
  obtain ⟨i, j, hi, hj, rfl⟩ := basisA.exists_pow_mul_pow he
  have key : ∀ g : G12, tmul (tpow zT i) (tpow aT j) = tbl g.1 →
      basisA.a ^ i * basisA.b ^ j = g := fun g hg => eq_iff_tbl.mpr ((tbl_f i j).trans hg)
  interval_cases i <;> interval_cases j
  · exact absurd (by simp) he1
  · exact Or.inr ⟨0, by rw [key (ai 0) (by rw [tbl_ai]; decide +kernel)]⟩
  · refine Or.inr ⟨0, ?_⟩
    rw [key (ai 0)⁻¹ (by rw [tblG_inv, tbl_ai]; decide +kernel), centralizer_singleton_inv]
  · exact Or.inl (by rw [key ⁅x, y⁆ (by rw [tbl_z]; decide +kernel)])
  · exact Or.inr ⟨1, by rw [key (ai 1) (by rw [tbl_ai]; decide +kernel)]⟩
  · refine Or.inr ⟨2, ?_⟩
    rw [key (ai 2)⁻¹ (by rw [tblG_inv, tbl_ai]; decide +kernel), centralizer_singleton_inv]
  · refine Or.inl ?_
    rw [key ⁅x, y⁆⁻¹ (by rw [tblG_inv, tbl_z]; decide +kernel), centralizer_singleton_inv]
  · exact Or.inr ⟨2, by rw [key (ai 2) (by rw [tbl_ai]; decide +kernel)]⟩
  · refine Or.inr ⟨1, ?_⟩
    rw [key (ai 1)⁻¹ (by rw [tblG_inv, tbl_ai]; decide +kernel), centralizer_singleton_inv]

theorem inf_centralizer_z_eq_bot
    {Y : Subgroup G12}
    (hY3 : ¬ 3 ∣ Nat.card Y) (hYA : basisA.sub ≤ normalizer (Y : Set G12)) :
    Y ⊓ centralizer ({⁅x, y⁆} : Set G12) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := Y ⊓ centralizer ({⁅x, y⁆} : Set G12) with hU
  have hsq : ∀ u ∈ U, u ^ 2 = 1 := by
    intro u hu
    have huN : u ∈ normalizer (P0 : Set G12) := Sec12.BCensus.centralizer_z_le_normalizer hu.2
    have h1 : u ^ 2 ∈ P0 := by
      have hQ : CFSG.IsElementaryAbelian 2 QP := isElementaryAbelian_QP
      have h2 : (QuotientGroup.mk ⟨u, huN⟩ : QP) ^ 2 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hQ.exponent_dvd_p _
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
      exact h2
    have h3 : (u ^ 2) ^ 3 = 1 := cube_of_mem_P0 h1
    have h4 : orderOf (u ^ 2) ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y (pow_mem hu.1 2)
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ h4) hY3
  have hU2 : IsPGroup 2 U := fun u => ⟨1, Subtype.ext (by simpa using hsq u u.2)⟩
  have hUA : basisA.sub ≤ normalizer (U : Set G12) :=
    Late.le_normalizer_inf hYA (A_le_normalizer_centralizer z_mem_A)
  by_contra hne
  obtain ⟨j, hj⟩ := le_V_of_mem_invariant
    ((mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hU2, hUA⟩) hne
  obtain ⟨u, huU, hu1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left hne
  have huW : u ∈ W j := (W_eq_V j).symm ▸ hj huU
  exact hu1 (eq_one_of_mem_W huW (mem_centralizer_singleton_iff.mp huU.2))

theorem inf_centralizer_ai
    {Y : Subgroup G12}
    (hY3 : ¬ 3 ∣ Nat.card Y) (hYA : basisA.sub ≤ normalizer (Y : Set G12)) (i : Fin 3) :
    Y ⊓ centralizer ({ai i} : Set G12) = ⊥ ∨ Y ⊓ centralizer ({ai i} : Set G12) = V i := by
  set C := centralizer ({ai i} : Set G12) with hC
  set U := Y ⊓ C with hU
  have hUV : U ≤ V i := by
    have := normal_V i
    have hidx : ((V i).subgroupOf C).index = 3 ^ 2 := by
      have h1 := Subgroup.card_mul_index ((V i).subgroupOf C)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (V_le_C i)).toEquiv, card_V,
        card_C] at h1
      omega
    have hU3 : ¬ 3 ∣ Nat.card (U.subgroupOf C) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
      exact fun h => hY3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    have h1 := le_of_index_eq_pow_three ((V i).subgroupOf C) hidx hU3
    intro u hu
    exact Subgroup.mem_subgroupOf.mp (h1 (Subgroup.mem_subgroupOf.mpr (show u ∈ U from hu) :
      (⟨u, hu.2⟩ : C) ∈ U.subgroupOf C))
  have hUA : basisA.sub ≤ normalizer (U : Set G12) :=
    Late.le_normalizer_inf hYA (A_le_normalizer_centralizer (ai_mem_A i))
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨h1, h2⟩ := z2_conj i
    have h := eq_of_le_four (mem_W_iff i) h1 h2 (hUA (pow_mem z_mem_A 2))
      ((W_eq_V i).symm ▸ hUV) hbot
    rw [h, W_eq_V]

theorem pair_facts : ∀ i j : Fin 3, i ≠ j →
    ((wP i 0 * wP j 0 * wP i 0 * wP j 1) ^ 2) ^ 3 = 1 ∧
      (wP i 0 * wP j 0 * wP i 0 * wP j 1) ^ 2 ≠ 1 := by
  decide +kernel

theorem not_le_of_ne {Y : Subgroup G12} (hY3 : ¬ 3 ∣ Nat.card Y) {i j : Fin 3} (hij : i ≠ j)
    (hi : W i ≤ Y) (hj : W j ≤ Y) : False := by
  obtain ⟨h1, h2⟩ := pair_facts i j hij
  set g := wG i 0 * wG j 0 * wG i 0 * wG j 1 with hg
  have hgY : g ^ 2 ∈ Y := by
    have hi0 : wG i 0 ∈ Y := hi (Or.inr (Or.inl rfl))
    have hj0 : wG j 0 ∈ Y := hj (Or.inr (Or.inl rfl))
    have hj1 : wG j 1 ∈ Y := hj (Or.inr (Or.inr (Or.inl rfl)))
    exact pow_mem (mul_mem (mul_mem (mul_mem hi0 hj0) hi0) hj1) 2
  have ho : orderOf (g ^ 2) = 3 :=
    orderOf_eq_prime (Subtype.ext h1) fun h => h2 (congrArg Subtype.val h)
  exact hY3 (ho ▸ Subgroup.orderOf_dvd_natCard Y hgY)

theorem isElemAbelian_A : CFSG.Assembly.IsElemAbelian 3 basisA.sub :=
  ⟨basisA.isElementaryAbelian.toIsMulCommutative, fun g hg => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      basisA.isElementaryAbelian.exponent_dvd_p ⟨g, hg⟩
    simpa using congrArg Subtype.val h⟩

theorem le_V_of_invariant
    {Y : Subgroup G12}
    (hY3 : ¬ 3 ∣ Nat.card Y) (hYA : basisA.sub ≤ normalizer (Y : Set G12)) :
    ∃ i, Y ≤ V i := by
  have hgen : ∀ M : Subgroup G12, (∀ k, Y ⊓ centralizer ({ai k} : Set G12) ≤ M) → Y ≤ M := by
    intro M hM
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three isElemAbelian_A
      (by rw [basisA.card]; norm_num) hYA ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3)
      fun e he he1 => ?_
    rcases centralizer_cases he he1 with h | ⟨k, h⟩
    · rw [h, inf_centralizer_z_eq_bot hY3 hYA]
      exact bot_le
    · rw [h]
      exact hM k
  by_cases hex : ∃ i, V i ≤ Y
  · obtain ⟨i, hi⟩ := hex
    refine ⟨i, hgen _ fun k => ?_⟩
    rcases inf_centralizer_ai hY3 hYA k with h | h
    · rw [h]
      exact bot_le
    · rw [h]
      by_cases hki : k = i
      · rw [hki]
      · exact absurd (not_le_of_ne hY3 hki ((W_eq_V k).symm ▸ h ▸ inf_le_left)
          ((W_eq_V i).symm ▸ hi)) id
  · push Not at hex
    refine ⟨0, hgen _ fun k => ?_⟩
    rcases inf_centralizer_ai hY3 hYA k with h | h
    · rw [h]
      exact bot_le
    · exact absurd (h ▸ inf_le_left) (hex k)

theorem card_centralizer_A :
    Nat.card (centralizer (basisA.sub : Set G12)) = 9 :=
  CFSG.RankThree.PartTwo.Toolkit.M12.card_centralizer_basisA

variable {G : Type} [Group G] [Finite G]

theorem typesOne_M12
    (h131 : Item131)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) [(ker142 A (lB A) c).Normal] {Q : Subgroup G}
    (hQ : Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3))
    (hK : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) :
    ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
      img142 A (lB A) c Q =
        thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c := by
  have hspor := Sec13.sporadicModels131
  obtain ⟨-, h9, hAc⟩ := point_facts_of_inner h131 hspor h.toSec13Data
    (center_eq_bot_of_mulEquiv φ hspor.2.1.2)
    (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M12)
  obtain ⟨g, hg⟩ := exists_conj_mem_A h hAc h9 (autIn_perm_three_of_M12 h131 h φ) φ
  obtain ⟨φ', hφ'E⟩ := exists_equiv_map_eq_of_conj φ hg
    (by rw [basisA.card, Res5Gen.card_image_inf h h9])
  have hcent := cent_of_rigid h φ' hφ'E fun τ hτ n hn hτn => aut_eq_one_M12 hτ hn hτn
  have d : Inner142 A c L := ⟨h, hAc, hK, hcent⟩
  exact d.typesOne_of_model φ' hφ'E V ai ai_mem_A ai_ne_one theta_ai
    (fun i => by rw [card_V]; norm_num) A_le_normalizer_V
    (fun Y hY3 hYP => le_V_of_invariant hY3 hYP)
    (IsPGroup.of_card (n := 2) (by rw [card_centralizer_A]; norm_num)) hQ

end Res5TypesM12

end CFSG.RankThree.PartTwo.Sec14
