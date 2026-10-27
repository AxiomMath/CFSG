module

public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Background.G2
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S1421

section S3

theorem perm3_comm_aux : ∀ a b : Equiv.Perm (Fin 3),
    ¬ (a ^ 3 = 1 ∧ b ^ 2 = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1) := by decide

theorem perm3_inv_aux : ∀ a b : Equiv.Perm (Fin 3),
    ¬ (a ^ 3 = 1 ∧ b ^ 2 = 1 ∧ a * b ≠ b * a ∧ b * a * b⁻¹ ≠ a⁻¹) := by decide

theorem perm3_mul_aux : ∀ a b : Equiv.Perm (Fin 3),
    ¬ (a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ (a * b) ^ 3 ≠ 1) := by decide

theorem perm3_gen_aux : ∀ a b : Equiv.Perm (Fin 3),
    ¬ (a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ b ≠ 1 ∧ a ≠ 1 ∧ a ≠ b ∧ a ≠ b ^ 2) := by decide

theorem perm3_comm {a b : Equiv.Perm (Fin 3)} (ha : a ^ 3 = 1) (hb : b ^ 2 = 1)
    (hab : a * b = b * a) : a = 1 ∨ b = 1 := by
  by_contra h
  push Not at h
  exact perm3_comm_aux a b ⟨ha, hb, hab, h.1, h.2⟩

theorem perm3_inv {a b : Equiv.Perm (Fin 3)} (ha : a ^ 3 = 1) (hb : b ^ 2 = 1)
    (hab : a * b ≠ b * a) : b * a * b⁻¹ = a⁻¹ := by
  by_contra h
  exact perm3_inv_aux a b ⟨ha, hb, hab, h⟩

theorem perm3_mul {a b : Equiv.Perm (Fin 3)} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (a * b) ^ 3 = 1 := by
  by_contra h
  exact perm3_mul_aux a b ⟨ha, hb, h⟩

theorem perm3_gen {a b : Equiv.Perm (Fin 3)} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hb1 : b ≠ 1) :
    a = 1 ∨ a = b ∨ a = b ^ 2 := by
  by_contra h
  push Not at h
  exact perm3_gen_aux a b ⟨ha, hb, hb1, h.1, h.2.1, h.2.2⟩

theorem orderOf_dvd_six (a : Equiv.Perm (Fin 3)) : orderOf a ∣ 6 := by
  have := orderOf_dvd_card (G := Equiv.Perm (Fin 3)) (x := a)
  simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using this

theorem perm3_odd {a : Equiv.Perm (Fin 3)} (h : Odd (orderOf a)) : a ^ 3 = 1 := by
  have h1 := orderOf_dvd_six a
  have h3 : orderOf a ∣ 3 := by
    have hle : orderOf a ≤ 6 := Nat.le_of_dvd (by norm_num) h1
    have hpos : 0 < orderOf a := orderOf_pos a
    interval_cases hn : orderOf a
    · simp
    · exact absurd h (by decide)
    · simp
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h (by decide)
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem perm3_two {a : Equiv.Perm (Fin 3)} {k : ℕ} (h : a ^ 2 ^ k = 1) : a ^ 2 = 1 := by
  have h1 := orderOf_dvd_six a
  have h2 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h3 : orderOf a ∣ 2 := by
    have hle : orderOf a ≤ 6 := Nat.le_of_dvd (by norm_num) h1
    have hpos : 0 < orderOf a := orderOf_pos a
    have h3k : ¬ 3 ∣ 2 ^ k := fun h3 =>
      absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    interval_cases hn : orderOf a
    · simp
    · simp
    · exact absurd (hn ▸ h2) h3k
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd ((show 3 ∣ 6 from by norm_num).trans (hn ▸ h2)) h3k
  exact orderOf_dvd_iff_pow_eq_one.mp h3

end S3

section Psi

variable {G : Type} [Group G]

@[expose] def A3 : Subgroup (Equiv.Perm (Fin 3)) where
  carrier := {a | a ^ 3 = 1}
  mul_mem' := fun {a b} ha hb => perm3_mul ha hb
  one_mem' := one_pow 3
  inv_mem' := fun {a} ha => by
    show a⁻¹ ^ 3 = 1
    rw [inv_pow, show a ^ 3 = 1 from ha, inv_one]

@[expose] noncomputable def psi {P : Subgroup G} (e : OTwoQuot P ≃* Equiv.Perm (Fin 3)) :
    ↥P →* Equiv.Perm (Fin 3) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥P))

theorem psi_eq_one_iff {P : Subgroup G} (e : OTwoQuot P ≃* Equiv.Perm (Fin 3)) {x : G}
    (hx : x ∈ P) : psi e ⟨x, hx⟩ = 1 ↔ x ∈ pCoreOf 2 P := by
  unfold psi
  rw [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    QuotientGroup.mk'_apply, e.map_eq_one_iff, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : (⟨x, hx⟩ : ↥P) = y := Subtype.ext hyx.symm
    rw [this]
    exact hy

theorem psi_commutator {P : Subgroup G} (e : OTwoQuot P ≃* Equiv.Perm (Fin 3)) {y s : G}
    (hy : y ∈ P) (hs : s ∈ P) :
    psi e ⟨⁅y, s⁆, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hs)
      (Subgroup.inv_mem _ hy)) (Subgroup.inv_mem _ hs)⟩ = ⁅psi e ⟨y, hy⟩, psi e ⟨s, hs⟩⁆ := by
  rw [← map_commutatorElement]
  congr 1

end Psi

section Commutator

variable {G : Type} [Group G]

theorem le_normalizer_commutator_left' {X A : Subgroup G} :
    X ≤ Subgroup.normalizer ((⁅X, A⁆ : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun y hy c hc => ?_
  have hle : ⁅X, A⁆ ≤ (⁅X, A⁆).comap (MulAut.conj y).toMonoidHom := by
    refine Subgroup.commutator_le.mpr fun x hx a ha => ?_
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj y).toMonoidHom ⁅x, a⁆ = ⁅y * x, a⁆ * ⁅y, a⁆⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (X.mul_mem hy hx) ha)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hy ha))
  exact hle hc

theorem commutator_le_left_of_le_normalizer {Y A : Subgroup G}
    (h : A ≤ Subgroup.normalizer (Y : Set G)) : ⁅Y, A⁆ ≤ Y := by
  refine Subgroup.commutator_le.mpr fun y hy a ha => ?_
  have h1 : a * y⁻¹ * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (h ha) y⁻¹).mp (Y.inv_mem hy)
  have : ⁅y, a⁆ = y * (a * y⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact Y.mul_mem hy h1

theorem eq_of_forall_mul_two_element [Finite G] {Y C : Subgroup G} (hCY : C ≤ Y)
    (hN : Y ≤ Subgroup.normalizer (C : Set G)) (hY : oTwoUpper Y = Y)
    (h : ∀ y ∈ Y, ∃ c ∈ C, ∃ o ∈ Y, (∃ m : ℕ, o ^ 2 ^ m = 1) ∧ y = c * o) : C = Y := by
  refine le_antisymm hCY ?_
  rw [← hY]
  refine oTwoUpper_le_of_pow_mem fun y hy => ?_
  obtain ⟨c, hc, o, ho, ⟨m, hm⟩, rfl⟩ := h y hy
  refine ⟨m, ?_⟩
  have : (C.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCY).mpr hN
  have hcY : c ∈ Y := hCY hc
  have h1 : (⟨c * o, Y.mul_mem hcY ho⟩ : ↥Y) ^ 2 ^ m ∈ C.subgroupOf Y := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    have e1 : (⟨c * o, Y.mul_mem hcY ho⟩ : ↥Y) = ⟨c, hcY⟩ * ⟨o, ho⟩ := rfl
    have hc1 : QuotientGroup.mk' (C.subgroupOf Y) ⟨c, hcY⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hc)
    rw [e1, map_mul, hc1, one_mul, ← map_pow]
    have : (⟨o, ho⟩ : ↥Y) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
    rw [this, map_one]
  exact Subgroup.mem_subgroupOf.mp h1

end Commutator

section YS2

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem T_le_M (h : Hyp1421 G T M) : T ≤ M := h.m_max.1.2

theorem T_le_normalizer_y (h : Hyp1421 G T M) :
    T ≤ Subgroup.normalizer (yOfL22 T M : Set G) := (T_le_M h).trans (le_normalizer_yOfL22 T M)

theorem isTwoReducedIn_VZ_of_hyp (h : Hyp1421 G T M) :
    IsTwoReducedIn M (VZ T M) ∧ VZ T M ≤ T := by
  obtain ⟨S, hS⟩ := h.toQTFE14.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ h.m_max.1.2
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.qtke.2.1 M h.m_max.1.1.1 ⟨S, hSM⟩
  have hVred : IsTwoReducedIn M (VZ T M) := by
    have := isTwoReducedIn_conjClosure M S hSM hF le_rfl
    rwa [hS] at this
  refine ⟨hVred, ?_⟩
  have := le_sylow_of_isTwoReducedIn S hSM hVred
  rwa [hS] at this

theorem pCoreOf_y_le (h : Hyp1421 G T M) : pCoreOf 2 (yOfL22 T M) ≤ T := by
  have h1 : pCoreOf 2 (yOfL22 T M) ≤ pCoreOf 2 M :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (yOfL22_le T M))
      (F7.le_normalizer_pCoreOf_of_le_normalizer (le_normalizer_yOfL22 T M))
      (pCoreOf_isPGroup 2 _)
  exact h1.trans (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo h.sylow (T_le_M h)))

theorem s2_le_T (h : Hyp1421 G T M) : s2Of T H (yOfL22 T M) ≤ T :=
  sup_le (pCoreOf_y_le h) inf_le_left

theorem T_le_normalizer_s2 (h : Hyp1421 G T M) (hTH : T ≤ H) :
    T ≤ Subgroup.normalizer (s2Of T H (yOfL22 T M) : Set G) := by
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := hTH.trans (le_normalizer_oTwoUpper H)
  have hTTK : T ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hTK hx⟩
  exact F1.le_normalizer_sup (F7.le_normalizer_pCoreOf_of_le_normalizer (T_le_normalizer_y h)) hTTK

theorem isSylowTwoOf_s2 (h : Hyp1421 G T M) (hTH : T ≤ H) :
    IsSylowTwoOf (s2Of T H (yOfL22 T M)) (oTwoUpper H ⊔ s2Of T H (yOfL22 T M)) := by
  set S2 := s2Of T H (yOfL22 T M) with hS2
  set K := oTwoUpper H with hK
  have hS2T : S2 ≤ T := s2_le_T h
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans (le_normalizer_oTwoUpper H)
  have hS2N : S2 ≤ Subgroup.normalizer (K : Set G) := hS2T.trans hTK
  refine ⟨le_sup_right, h.sylow.1.to_le hS2T, ?_⟩
  have hSyl : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_isSylowTwo h.sylow hTH) (oTwoUpper_le H)
      (le_normalizer_oTwoUpper H)
  have hEq : S2 ⊓ K = T ⊓ K :=
    le_antisymm (inf_le_inf_right K hS2T) (le_inf le_sup_right inf_le_right)
  have h1 := B6.relIndex_inf_eq_relIndex_sup hS2N
  rw [hEq] at h1
  rw [sup_comm]
  have h2 := hSyl.2.2
  rw [Subgroup.relIndex] at h1
  exact fun hd => h2 (by rw [h1]; exact hd)

end YS2

section Dichotomy

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem pCoreOf_y_eq_inf (F : Facts1422 T M) :
    pCoreOf 2 (yOfL22 T M) = yOfL22 T M ⊓ pCoreOf 2 (yOfL22 T M ⊔ T) := by
  rw [F.y_oTwo, ← F.centralizer_yT]
  ext x
  simp only [Subgroup.mem_inf]
  exact ⟨fun ⟨hx, hc⟩ => ⟨hx, Subgroup.mem_sup_left hx, hc⟩, fun ⟨hx, _, hc⟩ => ⟨hx, hc⟩⟩

theorem comm_mem_pCore_iff (h : Hyp1421 G T M) (F : Facts1422 T M)
    (e : OTwoQuot (yOfL22 T M ⊔ T) ≃* Equiv.Perm (Fin 3)) {y s : G} (hy : y ∈ yOfL22 T M)
    (hs : s ∈ T) :
    ⁅y, s⁆ ∈ pCoreOf 2 (yOfL22 T M) ↔
      psi e ⟨y, Subgroup.mem_sup_left hy⟩ * psi e ⟨s, Subgroup.mem_sup_right hs⟩ =
        psi e ⟨s, Subgroup.mem_sup_right hs⟩ * psi e ⟨y, Subgroup.mem_sup_left hy⟩ := by
  have hyP : y ∈ yOfL22 T M ⊔ T := Subgroup.mem_sup_left hy
  have hsP : s ∈ yOfL22 T M ⊔ T := Subgroup.mem_sup_right hs
  have hcP : ⁅y, s⁆ ∈ yOfL22 T M ⊔ T :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyP hsP) (Subgroup.inv_mem _ hyP))
      (Subgroup.inv_mem _ hsP)
  have hcY : ⁅y, s⁆ ∈ yOfL22 T M := by
    have h1 : s * y⁻¹ * s⁻¹ ∈ yOfL22 T M :=
      (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_y h hs) y⁻¹).mp
        ((yOfL22 T M).inv_mem hy)
    have : ⁅y, s⁆ = y * (s * y⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact (yOfL22 T M).mul_mem hy h1
  rw [pCoreOf_y_eq_inf F, Subgroup.mem_inf, ← psi_eq_one_iff e hcP]
  have e1 : psi e ⟨⁅y, s⁆, hcP⟩ = ⁅psi e ⟨y, hyP⟩, psi e ⟨s, hsP⟩⁆ := psi_commutator e hyP hsP
  rw [e1, commutatorElement_eq_one_iff_mul_comm]
  exact ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨hcY, hh⟩⟩

omit [Finite G] in
theorem psi_y_pow_three (e : OTwoQuot (yOfL22 T M ⊔ T) ≃* Equiv.Perm (Fin 3))
    {y : G} (hy : y ∈ yOfL22 T M) : psi e ⟨y, Subgroup.mem_sup_left hy⟩ ^ 3 = 1 := by
  have hY : oTwoUpper (yOfL22 T M) = yOfL22 T M := oTwoUpper_yOfL22 T M
  have hle : oTwoUpper (yOfL22 T M) ≤ ((A3.comap (psi e)).map (yOfL22 T M ⊔ T).subtype) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxY, hxodd⟩
    refine ⟨⟨x, Subgroup.mem_sup_left hxY⟩, ?_, rfl⟩
    show psi e ⟨x, Subgroup.mem_sup_left hxY⟩ ^ 3 = 1
    apply perm3_odd
    have h1 := orderOf_map_dvd (psi e) (⟨x, Subgroup.mem_sup_left hxY⟩ : ↥(yOfL22 T M ⊔ T))
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hxodd h1
  rw [← hY] at hy
  obtain ⟨z, hz, hzy⟩ := hle hy
  have : z = ⟨y, Subgroup.mem_sup_left (hY ▸ hy)⟩ := Subtype.ext hzy
  rw [this] at hz
  exact hz

theorem y_normalizes_or_commutator (h : Hyp1421 G T M) (F : Facts1422 T M) {S2 : Subgroup G}
    (hS2T : S2 ≤ T) (hO : pCoreOf 2 (yOfL22 T M) ≤ S2) :
    yOfL22 T M ≤ Subgroup.normalizer (S2 : Set G) ∨ ⁅yOfL22 T M, S2⁆ = yOfL22 T M := by
  obtain ⟨e⟩ := F.sThree
  set Y := yOfL22 T M with hYdef
  have hYP : Y ≤ Y ⊔ T := le_sup_left
  have hTP : T ≤ Y ⊔ T := le_sup_right
  by_cases hc : ∀ y (hy : y ∈ Y) s (hs : s ∈ S2),
      psi e ⟨y, hYP hy⟩ * psi e ⟨s, hTP (hS2T hs)⟩ = psi e ⟨s, hTP (hS2T hs)⟩ * psi e ⟨y, hYP hy⟩
  · left
    refine le_normalizer_of_conj_mem fun y hy w hw => ?_
    have e1 : y * w * y⁻¹ = ⁅y, w⁆ * w := by simp only [commutatorElement_def]; group
    rw [e1]
    exact S2.mul_mem (hO ((comm_mem_pCore_iff h F e hy (hS2T hw)).mpr (hc y hy w hw))) hw
  · right
    push Not at hc
    obtain ⟨y0, hy0, s0, hs0, hne⟩ := hc
    have hCY : ⁅Y, S2⁆ ≤ Y :=
      commutator_le_left_of_le_normalizer (fun x hx => T_le_normalizer_y h (hS2T hx))
    set a := psi e ⟨y0, hYP hy0⟩ with ha
    set b := psi e ⟨s0, hTP (hS2T hs0)⟩ with hb
    have ha3 : a ^ 3 = 1 := psi_y_pow_three e hy0
    have hb2 : b ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := h.sylow.1 ⟨s0, hS2T hs0⟩
      have hk' : (⟨s0, hTP (hS2T hs0)⟩ : ↥(Y ⊔ T)) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      refine perm3_two (k := k) ?_
      rw [hb, ← map_pow, hk', map_one]
    have hinv := perm3_inv ha3 hb2 hne
    have ha1 : a ≠ 1 := fun h1 => hne (by rw [h1, one_mul, mul_one])
    have hcomm : ⁅a, b⁆ = a ^ 2 := by
      have : ⁅a, b⁆ = a * (b * a * b⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
      rw [this, hinv, inv_inv, sq]
    have hb03 : (a ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ha3, one_pow]
    have hb01 : a ^ 2 ≠ 1 := by
      intro h2
      apply ha1
      calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
        _ = 1 := by rw [ha3, h2]; simp
    set c0 := ⁅y0, s0⁆ with hc0
    have hc0C : c0 ∈ ⁅Y, S2⁆ := Subgroup.commutator_mem_commutator hy0 hs0
    have hc0P : c0 ∈ Y ⊔ T := hYP (hCY hc0C)
    have hpc0 : psi e ⟨c0, hc0P⟩ = a ^ 2 := by
      have e1 : psi e ⟨c0, hc0P⟩ = ⁅a, b⁆ :=
        psi_commutator e (hYP hy0) (hTP (hS2T hs0))
      rw [e1, hcomm]
    have hrep : ∀ y ∈ Y, ∃ c ∈ ⁅Y, S2⁆, ∃ o ∈ Y, (∃ m : ℕ, o ^ 2 ^ m = 1) ∧ y = c * o := by
      intro y hy
      have hyP : y ∈ Y ⊔ T := hYP hy
      have hy3 := psi_y_pow_three e hy
      obtain ⟨c, hcC, hpc⟩ : ∃ c ∈ ⁅Y, S2⁆, ∃ hcP : c ∈ Y ⊔ T,
          psi e ⟨c, hcP⟩ = psi e ⟨y, hyP⟩ := by
        rcases perm3_gen hy3 hb03 hb01 with h1 | h1 | h1
        · exact ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, by rw [h1]; exact map_one _⟩
        · exact ⟨c0, hc0C, hc0P, by rw [hpc0, h1]⟩
        · refine ⟨c0 ^ 2, Subgroup.pow_mem _ hc0C 2, Subgroup.pow_mem _ hc0P 2, ?_⟩
          have : (⟨c0 ^ 2, Subgroup.pow_mem _ hc0P 2⟩ : ↥(Y ⊔ T)) = ⟨c0, hc0P⟩ ^ 2 := rfl
          rw [this, map_pow, hpc0, h1]
      obtain ⟨hcP, hpc⟩ := hpc
      have hcY : c ∈ Y := hCY hcC
      have hoY : c⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem hcY) hy
      have hoP : c⁻¹ * y ∈ Y ⊔ T := hYP hoY
      have hpo : psi e ⟨c⁻¹ * y, hoP⟩ = 1 := by
        have : (⟨c⁻¹ * y, hoP⟩ : ↥(Y ⊔ T)) = ⟨c, hcP⟩⁻¹ * ⟨y, hyP⟩ := rfl
        rw [this, map_mul, map_inv, hpc, inv_mul_cancel]
      have hoO : c⁻¹ * y ∈ pCoreOf 2 Y := by
        rw [pCoreOf_y_eq_inf F]
        exact ⟨hoY, (psi_eq_one_iff e hoP).mp hpo⟩
      obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 Y ⟨c⁻¹ * y, hoO⟩
      refine ⟨c, hcC, c⁻¹ * y, hoY, ⟨m, ?_⟩, by group⟩
      simpa using congrArg Subtype.val hm
    exact eq_of_forall_mul_two_element hCY le_normalizer_commutator_left'
      (oTwoUpper_yOfL22 T M) hrep

end Dichotomy

section Main

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem inH_yT (h : Hyp1421 G T M) : InH T (yOfL22 T M ⊔ T) := by
  refine ⟨le_sup_right, ?_⟩
  obtain ⟨hVred, hVT⟩ := isTwoReducedIn_VZ_of_hyp h
  have hle : VZ T M ≤ pCoreOf 2 (yOfL22 T M ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hVT.trans le_sup_right)
      (sup_le ((yOfL22_le T M).trans hVred.2.1) ((T_le_M h).trans hVred.2.1))
      (isPGroup_of_isElemAbelian hVred.2.2.1)
  intro hbot
  exact VZ_ne_bot h.toQTFE14.omegaOneCenter_ne_bot (le_bot_iff.mp (hbot ▸ hle))


theorem inf_ne_bot (N : Notation1428 T M H K1) : T ⊓ K1 ≠ ⊥ := by
  intro hbot
  have h1 := N.sylow.2.2
  rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h1
  have hodd : Odd (Nat.card K1) := Nat.odd_iff.mpr (by
    rcases Nat.even_or_odd (Nat.card K1) with h2 | h2
    · exact absurd (even_iff_two_dvd.mp h2) h1
    · exact Nat.odd_iff.mp h2)
  exact not_isSolvable_of_mem_cComp N.cComp_mem (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

end Main

theorem lemma_14_2_14 {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}
    (h311 : Theorem311) (st : Setting1427 T M H K1) :
    ⁅yOfL22 T M, s2Of T H (yOfL22 T M)⁆ = yOfL22 T M := by
  have hyp := st.hyp
  have F := st.facts
  have hStar := st.hStar
  have hTH : T ≤ H := hStar.1.1
  have hS2T : s2Of T H (yOfL22 T M) ≤ T := s2_le_T hyp
  rcases y_normalizes_or_commutator hyp F hS2T (le_sup_left : pCoreOf 2 (yOfL22 T M) ≤
      s2Of T H (yOfL22 T M)) with hYN | hcomm
  swap
  · exact hcomm
  exfalso
  have hNS2 : yOfL22 T M ⊔ T ≤ Subgroup.normalizer (s2Of T H (yOfL22 T M) : Set G) :=
    sup_le hYN (T_le_normalizer_s2 hyp hTH)
  have hS2ne : s2Of T H (yOfL22 T M) ≠ ⊥ := by
    intro hb
    apply inf_ne_bot st.notation_
    refine le_bot_iff.mp ?_
    rw [← hb]
    exact (inf_le_inf_left T st.notation_.le_K).trans le_sup_right
  obtain ⟨R0, hR0, hR0S, hR0N⟩ := h311 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
    (yOfL22 T M ⊔ T) H (s2Of T H (yOfL22 T M)) (inH_yT hyp) hStar.1
    ⟨H ⊓ M, (hyp.minParabolic hStar).uniqueMax⟩ hS2ne hS2T (isSylowTwoOf_s2 hyp hTH) hNS2
  have hR02 : IsPGroup 2 R0 := hyp.sylow.1.to_le (hR0S.trans hS2T)
  obtain ⟨M1, hM1, hM1le⟩ := exists_maxTwoLocal_ge
    (L := Subgroup.normalizer (R0 : Set G)) ⟨R0, hR0, hR02, rfl⟩
  have hM1M : M1 = M :=
    F.unique.2 M1 ⟨hM1, le_sup_left.trans (hR0N.trans hM1le)⟩
  exact hStar.2.1 (hM1M ▸ (le_sup_right.trans hR0N).trans hM1le)

end S1421

end CFSG.Quasithin
