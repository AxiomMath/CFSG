module

public import CFSG.Quasithin.EmptyFaithful.S1421Lem14
public import CFSG.Quasithin.EmptyFaithful.S14117Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S1421

section L2

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem s2_le_normalizer_y (h : Hyp1421 G T M) :
    s2Of T H (yOfL22 T M) ≤ Subgroup.normalizer (yOfL22 T M : Set G) :=
  (s2_le_T h).trans (T_le_normalizer_y h)

theorem mem_l2_iff (h : Hyp1421 G T M) {x : G} :
    x ∈ l2Of T H (yOfL22 T M) ↔
      ∃ y ∈ yOfL22 T M, ∃ s ∈ s2Of T H (yOfL22 T M), y * s = x := by
  have h1 := Subgroup.coe_mul_of_right_le_normalizer_left (yOfL22 T M)
    (s2Of T H (yOfL22 T M)) (s2_le_normalizer_y h)
  change x ∈ ((yOfL22 T M ⊔ s2Of T H (yOfL22 T M) : Subgroup G) : Set G) ↔ _
  rw [h1, Set.mem_mul]
  constructor
  · rintro ⟨y, hy, s, hs, rfl⟩
    exact ⟨y, hy, s, hs, rfl⟩
  · rintro ⟨y, hy, s, hs, rfl⟩
    exact ⟨y, hy, s, hs, rfl⟩


theorem mem_pCoreOf_y_of_two_element (F : Facts1422 T M)
    (e : OTwoQuot (yOfL22 T M ⊔ T) ≃* Equiv.Perm (Fin 3)) {y : G} (hy : y ∈ yOfL22 T M) {k : ℕ}
    (hk : y ^ 2 ^ k = 1) : y ∈ pCoreOf 2 (yOfL22 T M) := by
  have hyP : y ∈ yOfL22 T M ⊔ T := Subgroup.mem_sup_left hy
  have h3 := psi_y_pow_three e hy
  have h2 : psi e ⟨y, hyP⟩ ^ 2 = 1 := by
    refine perm3_two (k := k) ?_
    rw [← map_pow]
    have : (⟨y, hyP⟩ : ↥(yOfL22 T M ⊔ T)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have h1 : psi e ⟨y, hyP⟩ = 1 := by
    calc psi e ⟨y, hyP⟩ = psi e ⟨y, hyP⟩ ^ 3 * (psi e ⟨y, hyP⟩ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  rw [pCoreOf_y_eq_inf F]
  exact ⟨hy, (psi_eq_one_iff e hyP).mp h1⟩

theorem y_inf_s2 (h : Hyp1421 G T M) (F : Facts1422 T M) :
    yOfL22 T M ⊓ s2Of T H (yOfL22 T M) = pCoreOf 2 (yOfL22 T M) := by
  obtain ⟨e⟩ := F.sThree
  apply le_antisymm
  · rintro x ⟨hxY, hxS⟩
    have hxT : x ∈ T := s2_le_T h hxS
    obtain ⟨k, hk⟩ := h.sylow.1 ⟨x, hxT⟩
    exact mem_pCoreOf_y_of_two_element F e hxY (k := k) (by simpa using congrArg Subtype.val hk)
  · exact le_inf (pCoreOf_le 2 _) le_sup_left

theorem relIndex_pCoreOf_y (h : Hyp1421 G T M) (F : Facts1422 T M) :
    (pCoreOf 2 (yOfL22 T M)).relIndex (yOfL22 T M) = 3 := by
  have hYN : yOfL22 T M ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (yOfL22_le T M).trans (isTwoReducedIn_VZ_of_hyp h).1.2.1
  have h1 := card_autOn_eq_relIndex hYN
  rw [F.y_card, ← F.y_oTwo] at h1
  exact h1.symm

theorem isSylowTwoOf_s2_l2 (h : Hyp1421 G T M) (F : Facts1422 T M) :
    IsSylowTwoOf (s2Of T H (yOfL22 T M)) (l2Of T H (yOfL22 T M)) := by
  refine ⟨le_sup_right, h.sylow.1.to_le (s2_le_T h), ?_⟩
  have hN := s2_le_normalizer_y h (H := H)
  have h1 := B6.relIndex_inf_eq_relIndex_sup hN
  rw [inf_comm, y_inf_s2 h F, relIndex_pCoreOf_y h F, sup_comm] at h1
  change ¬ 2 ∣ (s2Of T H (yOfL22 T M)).relIndex (yOfL22 T M ⊔ s2Of T H (yOfL22 T M))
  rw [← h1]
  norm_num

theorem inf_l2_eq (h : Hyp1421 G T M) (F : Facts1422 T M) {S : Subgroup G}
    (hS₂ : s2Of T H (yOfL22 T M) ≤ S) (hST : S ≤ T) :
    S ⊓ l2Of T H (yOfL22 T M) = s2Of T H (yOfL22 T M) := by
  obtain ⟨e⟩ := F.sThree
  apply le_antisymm
  · rintro x ⟨hxS, hxL⟩
    obtain ⟨y, hy, s, hs, rfl⟩ := (mem_l2_iff h).mp hxL
    have hyS : y ∈ S := by
      have := S.mul_mem hxS (S.inv_mem (hS₂ hs))
      simpa using this
    have hyT : y ∈ T := hST hyS
    obtain ⟨k, hk⟩ := h.sylow.1 ⟨y, hyT⟩
    have hyO : y ∈ pCoreOf 2 (yOfL22 T M) :=
      mem_pCoreOf_y_of_two_element F e hy (k := k) (by simpa using congrArg Subtype.val hk)
    exact (s2Of T H (yOfL22 T M)).mul_mem (Subgroup.mem_sup_left hyO) hs
  · exact le_inf hS₂ le_sup_right


theorem commutator_mem_y (h : Hyp1421 G T M) {y s : G} (hy : y ∈ yOfL22 T M) (hs : s ∈ T) :
    ⁅y, s⁆ ∈ yOfL22 T M := by
  have h1 : s * y⁻¹ * s⁻¹ ∈ yOfL22 T M :=
    (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_y h hs) y⁻¹).mp ((yOfL22 T M).inv_mem hy)
  have : ⁅y, s⁆ = y * (s * y⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact (yOfL22 T M).mul_mem hy h1

theorem perm3_no_normal_two (N : Subgroup (Equiv.Perm (Fin 3))) [N.Normal] (hp : IsPGroup 2 N) :
    N = ⊥ := by
  have key : ∀ x : Equiv.Perm (Fin 3), ¬ (x ^ 2 = 1 ∧ x ≠ 1 ∧
      (x * ((Equiv.swap 0 1 * Equiv.swap 1 2) * x * (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹)) ^ 2 =
        1) := by decide
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  have hx1' : x ≠ 1 := by simpa using hx1
  have hx2 : x ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := hp ⟨x, hx⟩
    exact perm3_two (k := k) (by simpa using congrArg Subtype.val hk)
  have hxc : (Equiv.swap 0 1 * Equiv.swap 1 2) * x * (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ ∈ N :=
    Subgroup.Normal.conj_mem inferInstance x hx _
  have hprod := N.mul_mem hx hxc
  have h2 : (x * ((Equiv.swap 0 1 * Equiv.swap 1 2) * x *
      (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹)) ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := hp ⟨_, hprod⟩
    exact perm3_two (k := k) (by simpa using congrArg Subtype.val hk)
  exact key x ⟨hx2, hx1', h2⟩

theorem perm3_gen2_aux : ∀ a b x : Equiv.Perm (Fin 3),
    ¬ (a ^ 3 = 1 ∧ b ^ 2 = 1 ∧ a * b ≠ b * a ∧
      ∀ (i : Fin 3) (j : Fin 2), x ≠ a ^ (i : ℕ) * b ^ (j : ℕ)) := by decide

theorem perm3_gen2 {a b : Equiv.Perm (Fin 3)} (ha : a ^ 3 = 1) (hb : b ^ 2 = 1)
    (hab : a * b ≠ b * a) (x : Equiv.Perm (Fin 3)) :
    ∃ (i j : ℕ), x = a ^ i * b ^ j := by
  by_contra hcon
  push Not at hcon
  exact perm3_gen2_aux a b x ⟨ha, hb, hab, fun i j => hcon i j⟩


theorem exists_noncomm (h : Hyp1421 G T M) (F : Facts1422 T M)
    (e : OTwoQuot (yOfL22 T M ⊔ T) ≃* Equiv.Perm (Fin 3))
    (hc : ⁅yOfL22 T M, s2Of T H (yOfL22 T M)⁆ = yOfL22 T M) :
    ∃ (y : G) (hy : y ∈ yOfL22 T M) (s : G) (hs : s ∈ s2Of T H (yOfL22 T M)),
      psi e ⟨y, Subgroup.mem_sup_left hy⟩ * psi e ⟨s, Subgroup.mem_sup_right (s2_le_T h hs)⟩ ≠
        psi e ⟨s, Subgroup.mem_sup_right (s2_le_T h hs)⟩ * psi e ⟨y, Subgroup.mem_sup_left hy⟩ := by
  by_contra hcon
  push Not at hcon
  have hle : ⁅yOfL22 T M, s2Of T H (yOfL22 T M)⁆ ≤ pCoreOf 2 (yOfL22 T M) := by
    refine Subgroup.commutator_le.mpr fun y hy s hs => ?_
    exact (comm_mem_pCore_iff h F e hy (s2_le_T h hs)).mpr (hcon y hy s hs)
  rw [hc] at hle
  have h3 := relIndex_pCoreOf_y h F
  have h1 : (pCoreOf 2 (yOfL22 T M)).relIndex (yOfL22 T M) = 1 :=
    Subgroup.relIndex_eq_one.mpr hle
  omega

theorem l2_inf_normalizer_s2 (h : Hyp1421 G T M) (F : Facts1422 T M)
    (hc : ⁅yOfL22 T M, s2Of T H (yOfL22 T M)⁆ = yOfL22 T M) :
    l2Of T H (yOfL22 T M) ⊓ Subgroup.normalizer (s2Of T H (yOfL22 T M) : Set G) =
      s2Of T H (yOfL22 T M) := by
  obtain ⟨e⟩ := F.sThree
  apply le_antisymm
  · rintro x ⟨hxL, hxN⟩
    obtain ⟨y, hy, s, hs, rfl⟩ := (mem_l2_iff h).mp hxL
    have hyN : y ∈ Subgroup.normalizer (s2Of T H (yOfL22 T M) : Set G) := by
      have := Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ (Subgroup.le_normalizer hs))
      simpa using this
    have hyO : y ∈ pCoreOf 2 (yOfL22 T M) := by
      by_contra hyO
      have hyP : y ∈ yOfL22 T M ⊔ T := Subgroup.mem_sup_left hy
      have hψy : psi e ⟨y, hyP⟩ ≠ 1 := fun h1 => hyO (by
        rw [pCoreOf_y_eq_inf F]
        exact ⟨hy, (psi_eq_one_iff e hyP).mp h1⟩)
      have hall : ∀ s' (hs' : s' ∈ s2Of T H (yOfL22 T M)),
          psi e ⟨s', Subgroup.mem_sup_right (s2_le_T h hs')⟩ = 1 := by
        intro s' hs'
        have hs'T : s' ∈ T := s2_le_T h hs'
        have hcomm1 : ⁅y, s'⁆ ∈ pCoreOf 2 (yOfL22 T M) := by
          rw [← y_inf_s2 h F (H := H)]
          refine ⟨commutator_mem_y h hy hs'T, ?_⟩
          have e1 : ⁅y, s'⁆ = (y * s' * y⁻¹) * s'⁻¹ := by simp only [commutatorElement_def]
          rw [e1]
          exact (s2Of T H (yOfL22 T M)).mul_mem
            ((Subgroup.mem_normalizer_iff.mp hyN s').mp hs') ((s2Of T H (yOfL22 T M)).inv_mem hs')
        have hmul := (comm_mem_pCore_iff h F e hy hs'T).mp hcomm1
        have hb2 : psi e ⟨s', Subgroup.mem_sup_right hs'T⟩ ^ 2 = 1 := by
          obtain ⟨k, hk⟩ := h.sylow.1 ⟨s', hs'T⟩
          refine perm3_two (k := k) ?_
          rw [← map_pow]
          have : (⟨s', Subgroup.mem_sup_right hs'T⟩ : ↥(yOfL22 T M ⊔ T)) ^ 2 ^ k = 1 :=
            Subtype.ext (by simpa using congrArg Subtype.val hk)
          rw [this, map_one]
        rcases perm3_comm (psi_y_pow_three e hy) hb2 hmul with h1 | h1
        · exact absurd h1 hψy
        · exact h1
      have hle : ⁅yOfL22 T M, s2Of T H (yOfL22 T M)⁆ ≤ pCoreOf 2 (yOfL22 T M) := by
        refine Subgroup.commutator_le.mpr fun y' hy' s' hs' => ?_
        rw [comm_mem_pCore_iff h F e hy' (s2_le_T h hs'), hall s' hs', mul_one, one_mul]
      rw [hc] at hle
      exact hyO (hle hy)
    exact (s2Of T H (yOfL22 T M)).mul_mem (Subgroup.mem_sup_left hyO) hs
  · exact le_inf le_sup_right Subgroup.le_normalizer


theorem oTwoQuot_l2_equiv_perm3 (h : Hyp1421 G T M) (F : Facts1422 T M)
    (hc : ⁅yOfL22 T M, s2Of T H (yOfL22 T M)⁆ = yOfL22 T M) :
    Nonempty (OTwoQuot (l2Of T H (yOfL22 T M)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := F.sThree
  have hS2P : s2Of T H (yOfL22 T M) ≤ yOfL22 T M ⊔ T := (s2_le_T h).trans le_sup_right
  have hLP : l2Of T H (yOfL22 T M) ≤ yOfL22 T M ⊔ T := sup_le le_sup_left hS2P
  let φ : ↥(l2Of T H (yOfL22 T M)) →* Equiv.Perm (Fin 3) :=
    (psi e).comp (Subgroup.inclusion hLP)
  have hφ : ∀ z : ↥(l2Of T H (yOfL22 T M)), φ z = psi e ⟨(z : G), hLP z.2⟩ := fun z => rfl
  have hsurj : Function.Surjective φ := by
    obtain ⟨y0, hy0, s0, hs0, hne⟩ := exists_noncomm h F e hc
    intro x
    have ha := psi_y_pow_three e hy0
    have hs0T : s0 ∈ T := s2_le_T h hs0
    have hb2 : psi e ⟨s0, Subgroup.mem_sup_right hs0T⟩ ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := h.sylow.1 ⟨s0, hs0T⟩
      refine perm3_two (k := k) ?_
      rw [← map_pow]
      have : (⟨s0, Subgroup.mem_sup_right hs0T⟩ : ↥(yOfL22 T M ⊔ T)) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    obtain ⟨i, j, hij⟩ := perm3_gen2 ha hb2 hne x
    let y0' : ↥(l2Of T H (yOfL22 T M)) := ⟨y0, Subgroup.mem_sup_left hy0⟩
    let s0' : ↥(l2Of T H (yOfL22 T M)) := ⟨s0, Subgroup.mem_sup_right hs0⟩
    refine ⟨y0' ^ i * s0' ^ j, ?_⟩
    rw [map_mul, map_pow, map_pow, hφ y0', hφ s0', hij]
  have hker : φ.ker = (pCoreOf 2 (yOfL22 T M ⊔ T)).subgroupOf (l2Of T H (yOfL22 T M)) := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ]
    exact psi_eq_one_iff e (hLP z.2)
  have hpc : CFSG.Open.pCore 2 ↥(l2Of T H (yOfL22 T M)) = φ.ker := by
    apply le_antisymm
    · intro z hz
      have hN : (CFSG.Open.pCore 2 ↥(l2Of T H (yOfL22 T M))).map φ = ⊥ := by
        have : ((CFSG.Open.pCore 2 ↥(l2Of T H (yOfL22 T M))).map φ).Normal :=
          Subgroup.Normal.map (CFSG.LieType.BorelTits.pCore_normal 2) φ hsurj
        exact perm3_no_normal_two _ ((CFSG.LieType.BorelTits.pCore_isPGroup 2).map φ)
      have hz' : φ z ∈ (CFSG.Open.pCore 2 ↥(l2Of T H (yOfL22 T M))).map φ := ⟨z, hz, rfl⟩
      rw [hN, Subgroup.mem_bot] at hz'
      exact hz'
    · rw [hker]
      refine le_pCore 2 ?_ ?_
      · exact Subgroup.normal_subgroupOf_of_le_normalizer (hLP.trans (le_normalizer_pCoreOf 2 _))
      · rw [← Subgroup.inf_subgroupOf_right]
        exact A4.isPGroup_subgroupOf_of_le inf_le_right
          ((pCoreOf_isPGroup 2 (yOfL22 T M ⊔ T)).to_le inf_le_left)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩


theorem vz_le_y (h : Hyp1421 G T M) (F : Facts1422 T M) : VZ T M ≤ yOfL22 T M := by
  obtain ⟨hVred, hVT⟩ := isTwoReducedIn_VZ_of_hyp h
  have hYM := yOfL22_le T M
  have hYV : yOfL22 T M ≤ Subgroup.normalizer (VZ T M : Set G) := hYM.trans hVred.2.1
  have hVY : VZ T M ≤ Subgroup.normalizer (yOfL22 T M : Set G) :=
    (hVT.trans (T_le_M h)).trans (le_normalizer_yOfL22 T M)
  have hV2 : ∀ v ∈ VZ T M, v ^ 2 = 1 := hVred.2.2.1.2
  have hVc : ∀ v ∈ VZ T M, ∀ w ∈ VZ T M, v * w = w * v := fun v hv w hw =>
    hVred.2.2.1.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩ |> fun hh => congrArg Subtype.val hh
  set W : Subgroup G := ⁅yOfL22 T M, VZ T M⁆ with hW
  have hWY : W ≤ yOfL22 T M := by
    refine Subgroup.commutator_le.mpr fun y hy v hv => ?_
    have h1 : v * y⁻¹ * v⁻¹ ∈ yOfL22 T M :=
      (Subgroup.mem_normalizer_iff.mp (hVY hv) y⁻¹).mp ((yOfL22 T M).inv_mem hy)
    have : ⁅y, v⁆ = y * (v * y⁻¹ * v⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact (yOfL22 T M).mul_mem hy h1
  have hWV : W ≤ VZ T M := by
    refine Subgroup.commutator_le.mpr fun y hy v hv => ?_
    have h1 : y * v * y⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hYV hy) v).mp hv
    have : ⁅y, v⁆ = (y * v * y⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact (VZ T M).mul_mem h1 ((VZ T M).inv_mem hv)
  have hYW : yOfL22 T M ≤ Subgroup.normalizer (W : Set G) := le_normalizer_commutator_left'
  have hdvd : Nat.card W ∣ 4 := h.rank_two ▸ Subgroup.card_dvd_of_le hWV
  by_cases h4 : Nat.card W = 4
  · have hWeq : W = VZ T M := Subgroup.eq_of_le_of_card_ge hWV (by rw [h4, h.rank_two])
    rw [← hWeq]
    exact hWY
  exfalso
  have hYcW : yOfL22 T M ≤ Subgroup.centralizer (W : Set G) := by
    have h12 : Nat.card W = 1 ∨ Nat.card W = 2 := by
      have : Nat.card W ∈ ({1, 2, 4} : Finset ℕ) := by
        have h' : Nat.card W ∈ Nat.divisors 4 := by simp [hdvd]
        simpa [show Nat.divisors 4 = {1, 2, 4} by decide] using h'
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
    rcases h12 with h1 | h2
    · intro y _
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hW1 : W = ⊥ := Subgroup.card_eq_one.mp h1
      have hw1 : w ∈ W := hw
      rw [hW1, Subgroup.mem_bot] at hw1
      simp [hw1]
    · exact hYW.trans (normalizer_le_centralizer_of_card_two h2)
  have hsq : ∀ y ∈ yOfL22 T M, y ^ 2 ∈ pCoreOf 2 (yOfL22 T M) := by
    intro y hy
    rw [F.y_oTwo]
    refine ⟨(yOfL22 T M).pow_mem hy 2, ?_⟩
    show y ^ 2 ∈ Subgroup.centralizer (VZ T M : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    set t := ⁅y, v⁆ with ht
    have htW : t ∈ W := Subgroup.commutator_mem_commutator hy hv
    have htV : t ∈ VZ T M := hWV htW
    have hyt : y * t * y⁻¹ = t := by
      have := (Subgroup.mem_centralizer_iff.mp (hYcW hy)) t htW
      calc y * t * y⁻¹ = (y * t) * y⁻¹ := rfl
        _ = (t * y) * y⁻¹ := by rw [← this]
        _ = t := by group
    have hyv : y * v * y⁻¹ = t * v := by simp only [ht, commutatorElement_def]; group
    have ht2 : t ^ 2 = 1 := hV2 t htV
    have e1 : y * (y * v * y⁻¹) * y⁻¹ = v := by
      calc y * (y * v * y⁻¹) * y⁻¹ = y * (t * v) * y⁻¹ := by rw [hyv]
        _ = (y * t * y⁻¹) * (y * v * y⁻¹) := by group
        _ = t * (t * v) := by rw [hyt, hyv]
        _ = t ^ 2 * v := by rw [sq, mul_assoc]
        _ = v := by rw [ht2, one_mul]
    have e2 : y * y * v = v * (y * y) := by
      calc y * y * v = (y * (y * v * y⁻¹) * y⁻¹) * (y * y) := by group
        _ = v * (y * y) := by rw [e1]
    rw [sq]
    exact e2.symm
  have hrel := relIndex_pCoreOf_y h F
  have : (pCoreOf 2 (yOfL22 T M)).subgroupOf (yOfL22 T M) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_pCoreOf 2 _)
  have hcard : Nat.card (↥(yOfL22 T M) ⧸ (pCoreOf 2 (yOfL22 T M)).subgroupOf (yOfL22 T M)) = 3 := by
    rw [← hrel]
    rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥(yOfL22 T M) ⧸
    (pCoreOf 2 (yOfL22 T M)).subgroupOf (yOfL22 T M)) 3 (by rw [hcard])
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hy2 : (y : ↥(yOfL22 T M) ⧸ (pCoreOf 2 (yOfL22 T M)).subgroupOf (yOfL22 T M)) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (hsq y y.2)
  have := orderOf_dvd_of_pow_eq_one hy2
  rw [hq] at this
  omega


theorem not_y_le_normalizer_Z (h : Hyp1421 G T M) (F : Facts1422 T M) :
    ¬ yOfL22 T M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
  intro hYN
  obtain ⟨hVred, hVT⟩ := isTwoReducedIn_VZ_of_hyp h
  have hZ2 := h.card_omegaOneCenter
  have hYC : yOfL22 T M ≤ mcOf T :=
    hYN.trans (normalizer_le_centralizer_of_card_two hZ2)
  have hCC : Subgroup.centralizer (VZ T M : Set G) ≤ mcOf T :=
    Subgroup.centralizer_le (le_conjClosure _ _)
  have hRN : M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (M ⊓ mcOf T) : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans hCC)).trans (le_normalizer_pCoreOf 2 _)
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right
    (M ⊓ Subgroup.centralizer (VZ T M : Set G)) (pCoreOf 2 (M ⊓ mcOf T)) hRN
  have hRT : pCoreOf 2 (M ⊓ mcOf T) ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf
      (isSylowTwoOf_of_isSylowTwo h.sylow (le_inf (T_le_M h) h.toQTFE14.t_le_mc))
  have hle : autOn (yOfL22 T M) (VZ T M) ≤ autOn T (VZ T M) := by
    intro a ha
    obtain ⟨y, hyV, hyY, rfl⟩ := mem_autOn_iff_exists.mp ha
    have hy : y ∈ M ⊓ mcOf T := Subgroup.mem_inf.mpr ⟨yOfL22_le T M hyY, hYC hyY⟩
    rw [F.mmc_eq] at hy
    have hy' : y ∈ (((M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ pCoreOf 2 (M ⊓ mcOf T) :
        Subgroup G) : Set G) := hy
    rw [hmul] at hy'
    obtain ⟨c, hc, r, hr, rfl⟩ := hy'
    have hrT : r ∈ T := hRT hr
    have hrV : r ∈ Subgroup.normalizer (VZ T M : Set G) := hVred.2.1 (T_le_M h hrT)
    have hcV : c ∈ Subgroup.normalizer (VZ T M : Set G) := hVred.2.1 hc.1
    refine mem_autOn_iff_exists.mpr ⟨r, hrV, hrT, ?_⟩
    have e1 : (⟨c * r, hyV⟩ : Subgroup.normalizer (VZ T M : Set G)) = ⟨c, hcV⟩ * ⟨r, hrV⟩ := rfl
    have hc1 : conjAct (VZ T M) ⟨c, hcV⟩ = 1 := A4.conjAct_eq_one_iff.mpr hc.2
    rw [e1, map_mul, hc1, one_mul]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card (autOn (yOfL22 T M) (VZ T M)) := by rw [F.y_card]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := autOn (yOfL22 T M) (VZ T M)) 3 h3
  have haT := hle a.2
  obtain ⟨x, hxV, hxT, hxa⟩ := mem_autOn_iff_exists.mp haT
  obtain ⟨k, hk⟩ := h.sylow.1 ⟨x, hxT⟩
  have hk' : (⟨x, hxV⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hak : (a : MulAut ↥(VZ T M)) ^ 2 ^ k = 1 := by
    rw [← hxa, ← map_pow, hk', map_one]
  have h1 : orderOf (a : MulAut ↥(VZ T M)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hak
  rw [Subgroup.orderOf_coe, ha] at h1
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
  omega

end L2

end S1421

end CFSG.Quasithin
