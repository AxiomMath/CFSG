module

public import CFSG.Quasithin.Background.C1PackS15205D
public import CFSG.Quasithin.Background.C1PackS15205C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack5

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_autOn_dvd {A V V' : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hA' : A ≤ Subgroup.normalizer (V' : Set G))
    (h : A ⊓ Subgroup.centralizer (V : Set G) ≤ A ⊓ Subgroup.centralizer (V' : Set G)) :
    Nat.card (autOn A V') ∣ Nat.card (autOn A V) := by
  rw [card_autOn_eq_relIndex hA', card_autOn_eq_relIndex hA]
  exact Subgroup.relIndex_dvd_of_le_left A h

omit [Finite G] in
theorem eq_three_of_dvd {n : ℕ} (h3 : n ∣ 3) (h1 : n ≠ 1) : n = 3 :=
  ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left h1

variable {T Mc M M₁ : Subgroup G}

theorem Ctr5.le_centralizer_VZ₁ (c : Ctr5 T Mc M M₁) {W : Subgroup G} (hWT : W ≤ T)
    (hWH : M₁ ⊓ M ≤ Subgroup.normalizer (W : Set G)) :
    W ≤ Subgroup.centralizer (VZ T M₁ : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  unfold VZ conjClosure at hv
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨m, hm, z, hz, rfl⟩ := hx
    obtain ⟨a, ha, hmz⟩ := conj_of_ordLE c.ordLE hm (le_conjClosure _ _ hz)
    rw [hmz]
    have hw' : a⁻¹ * w * a ∈ W := (Subgroup.mem_normalizer_iff''.mp (hWH ha) w).mp hw
    have hzc : (a⁻¹ * w * a) * z = z * (a⁻¹ * w * a) :=
      Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_center T hz).2 _ (hWT hw')
    calc a * z * a⁻¹ * w = a * (z * (a⁻¹ * w * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * w * a) * z) * a⁻¹ := by rw [hzc]
      _ = w * (a * z * a⁻¹) := by group
  | one => simp
  | mul x y _ _ hx hy =>
    calc x * y * w = x * (y * w) := by group
      _ = x * (w * y) := by rw [hy]
      _ = (x * w) * y := by group
      _ = (w * x) * y := by rw [hx]
      _ = w * (x * y) := by group
  | inv x _ hx =>
    calc x⁻¹ * w = x⁻¹ * (w * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * w) * x⁻¹ := by rw [hx]
      _ = w * x⁻¹ := by group

end General

section Q

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ : Subgroup G}

structure QD5 (T Mc M M₁ : Subgroup G) (Q : Subgroup (MulAut (V154 T Mc M))) : Prop where
  le_P : Q ≤ oTwoUpper (mBar0 T Mc M)
  card : Nat.card Q = 3
  norm : ∀ g ∈ autOn M (V154 T Mc M), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q
  eq : autOn (M₁ ⊓ M) (V154 T Mc M) = Q ⊔ autOn T (V154 T Mc M)

variable {Q : Subgroup (MulAut (V154 T Mc M))}

theorem QD5.le_Mb (c : Ctr5 T Mc M M₁) (hQ : QD5 T Mc M M₁ Q) :
    Q ≤ autOn M (V154 T Mc M) := by
  obtain ⟨-, hA, -⟩ := c.case_three
  rw [hA]
  exact hQ.le_P.trans (oTwoUpper_le _)

theorem QD5.le_Hb (hQ : QD5 T Mc M M₁ Q) : Q ≤ autOn (M₁ ⊓ M) (V154 T Mc M) := by
  rw [hQ.eq]
  exact le_sup_left

theorem QD5.not_le_Mcb (c : Ctr5 T Mc M M₁) (hQ : QD5 T Mc M M₁ Q) :
    ¬ Q ≤ autOn (M ⊓ Mc) (V154 T Mc M) := by
  intro h
  apply c.not_Hb_le_Mcb
  rw [hQ.eq]
  exact sup_le h (A4.autOn_mono (le_inf c.T_le_M c.qtfe.t_le_mc))

theorem QD5.autOn_Y0 (c : Ctr5 T Mc M M₁) (hQ : QD5 T Mc M M₁ Q) :
    autOn (preOn M (V154 T Mc M) Q) (V154 T Mc M) = Q :=
  autOn_preOn (hQ.le_Mb c)

theorem QD5.M_le_normalizer_preOn (c : Ctr5 T Mc M M₁) (hQ : QD5 T Mc M M₁ Q) :
    M ≤ Subgroup.normalizer (preOn M (V154 T Mc M) Q : Set G) :=
  le_normalizer_preOn c.std.data.hMV hQ.norm

theorem QD5.exists_mul_preOn_T (c : Ctr5 T Mc M M₁) (hQ : QD5 T Mc M M₁ Q) {h : G}
    (hh : h ∈ M₁ ⊓ M) :
    ∃ y ∈ preOn M (V154 T Mc M) Q, y ∈ M₁ ⊓ M ∧ ∃ t ∈ T, h = y * t := by
  have hd := c.std.data
  have hhM : h ∈ M := hh.2
  have hhN : h ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hd.hMV hhM
  have h1 : conjAct _ ⟨h, hhN⟩ ∈ autOn (M₁ ⊓ M) (V154 T Mc M) :=
    mem_autOn_iff_exists.mpr ⟨h, hhN, hh, rfl⟩
  rw [hQ.eq] at h1
  have hTbN : autOn T (V154 T Mc M) ≤ Subgroup.normalizer (Q : Set (MulAut (V154 T Mc M))) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    obtain ⟨t, htN, htT, rfl⟩ := mem_autOn_iff_exists.mp hg
    have htM : t ∈ M := c.T_le_M htT
    have hmem : conjAct _ ⟨t, htN⟩ ∈ autOn M (V154 T Mc M) := mem_autOn_iff_exists.mpr ⟨t, htN, htM, rfl⟩
    exact ⟨fun hx => hQ.norm _ hmem x hx, fun hx => by
      have hmem' : (conjAct _ ⟨t, htN⟩)⁻¹ ∈ autOn M (V154 T Mc M) := (autOn M _).inv_mem hmem
      have := hQ.norm _ hmem' _ hx
      simpa [mul_assoc] using this⟩
  have h2 : (conjAct _ ⟨h, hhN⟩ : MulAut (V154 T Mc M)) ∈ ((Q ⊔ autOn T (V154 T Mc M) : Subgroup _) : Set _) := h1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q _ hTbN] at h2
  obtain ⟨q, hq, tb, htb, hqt⟩ := Set.mem_mul.mp h2
  obtain ⟨t, htN, htT, rfl⟩ := mem_autOn_iff_exists.mp htb
  have htM : t ∈ M := c.T_le_M htT
  refine ⟨h * t⁻¹, ?_, ?_, t, htT, by group⟩
  · refine mem_preOn.mpr ⟨M.mul_mem hhM (M.inv_mem htM), (Subgroup.normalizer _).mul_mem hhN
      ((Subgroup.normalizer _).inv_mem htN), ?_⟩
    have : conjAct (V154 T Mc M) ⟨h * t⁻¹, (Subgroup.normalizer _).mul_mem hhN
        ((Subgroup.normalizer _).inv_mem htN)⟩ = conjAct _ ⟨h, hhN⟩ * (conjAct _ ⟨t, htN⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [this, ← hqt]
    simpa using hq
  · exact (M₁ ⊓ M).mul_mem hh ((M₁ ⊓ M).inv_mem (c.T_le_H htT))

structure Yd5 (T Mc M M₁ Yh : Subgroup G) : Prop where
  le_H : Yh ≤ M₁ ⊓ M
  H_norm : M₁ ⊓ M ≤ Subgroup.normalizer (Yh : Set G)
  card : Nat.card (autOn Yh (VZ T M₁)) = 3
  fac : ∀ m ∈ M₁, ∃ y ∈ Yh, ∃ a ∈ M₁ ⊓ Mc, m = y * a

theorem Ctr5.centralizer_V_le (c : Ctr5 T Mc M M₁) :
    M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G) :=
  centralizer_VZ_le_of_ordLE_of_isHv c.ordLE c.isHv

theorem yd5_of_VZ (c : Ctr5 T Mc M M₁) (hV : V154 T Mc M = VZ T M) (hQ : QD5 T Mc M M₁ Q) :
    Yd5 T Mc M M₁ (preOn M (V154 T Mc M) Q) := by
  have hd := c.std.data
  have hCV : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G) :=
    by rw [hV]; exact c.centralizer_V_le
  have hle : preOn M (V154 T Mc M) Q ≤ M₁ ⊓ M := by
    intro y hy
    obtain ⟨hyM, hyN, hyQ⟩ := mem_preOn.mp hy
    obtain ⟨a, ha, k, hk, rfl⟩ := exists_mul_of_conjAct_mem hd.hMV inf_le_right hyM
      (hQ.le_Hb hyQ)
    exact (M₁ ⊓ M).mul_mem ha ⟨(hCV hk).1, hk.1⟩
  refine ⟨hle, inf_le_right.trans (hQ.M_le_normalizer_preOn c), ?_, ?_⟩
  · have hY0N : preOn M (V154 T Mc M) Q ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
      (preOn_le _ _ _).trans hd.hMV
    have hY0N₁ : preOn M (V154 T Mc M) Q ≤ Subgroup.normalizer (VZ T M₁ : Set G) :=
      hle.trans (inf_le_left.trans (le_normalizer_VZ T M₁))
    have hcen : preOn M (V154 T Mc M) Q ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤
        preOn M (V154 T Mc M) Q ⊓ Subgroup.centralizer (VZ T M₁ : Set G) := fun y hy =>
      ⟨hy.1, (hCV ⟨preOn_le _ _ _ hy.1, hy.2⟩).2⟩
    have hdvd := card_autOn_dvd hY0N hY0N₁ hcen
    rw [hQ.autOn_Y0 c, hQ.card] at hdvd
    refine eq_three_of_dvd hdvd ?_
    intro h1
    have hbot : autOn (preOn M (V154 T Mc M) Q) (VZ T M₁) = ⊥ := Subgroup.card_eq_one.mp h1
    have hcent := le_centralizer_of_autOn_eq_bot hY0N₁ hbot
    have hMc : preOn M (V154 T Mc M) Q ≤ M ⊓ Mc := fun y hy =>
      ⟨preOn_le _ _ _ hy, c.C₁_le_Mc ⟨(hle hy).1, hcent hy⟩⟩
    apply hQ.not_le_Mcb c
    rw [← hQ.autOn_Y0 c]
    exact A4.autOn_mono hMc
  · intro m hm
    obtain ⟨h, hh, k, hk, rfl⟩ := c.exists_mul m hm
    obtain ⟨y, hy, -, t, ht, rfl⟩ := hQ.exists_mul_preOn_T c hh
    refine ⟨y, hy, t * k, ⟨M₁.mul_mem (c.T_le_M₁ ht) hk.1,
      Mc.mul_mem (c.qtfe.t_le_mc ht) (c.C₁_le_Mc hk)⟩, by group⟩

section Six

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ : Subgroup G}

omit [Finite G] in
theorem autOn_commutator {V X R : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hR : R ≤ Subgroup.normalizer (V : Set G)) :
    autOn ⁅X, R⁆ V = ⁅autOn X V, autOn R V⁆ := by
  unfold autOn
  rw [S152Y.commutator_subgroupOf_eq hX hR, Subgroup.map_commutator]

omit [Finite G] in
theorem isPGroup_autOn' {P V : Subgroup G} (hP : IsPGroup 2 P)
    (hPV : P ≤ Subgroup.normalizer (V : Set G)) : IsPGroup 2 (autOn P V) :=
  (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPV).symm).map (conjAct V)

omit [Finite G] in
theorem le_normalizer_of_conj' {A : Type*} [Group A] {S Q : Subgroup A}
    (h : ∀ g ∈ S, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) : S ≤ Subgroup.normalizer (Q : Set A) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => h g hg x hx, fun hx => by
    have := h g⁻¹ (S.inv_mem hg) _ hx
    simpa [mul_assoc] using this⟩

omit [Finite G] in
theorem eq_one_of_pow_two_pow_of_pow_three {A : Type*} [Group A] {z : A} {k : ℕ}
    (h2 : z ^ 2 ^ k = 1) (h3 : z ^ 3 = 1) : z = 1 := by
  have h : orderOf z ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  have hc : Nat.gcd (2 ^ k) 3 = 1 :=
    Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)
  rw [hc] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

theorem inf_eq_bot_of_two_group_card_three {A : Type*} [Group A] {P Q : Subgroup A}
    (hP : IsPGroup 2 P) [Finite Q] (hQ : Nat.card Q = 3) : P ⊓ Q = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hP ⟨z, hz.1⟩
  have h3 : (⟨z, hz.2⟩ : Q) ^ 3 = 1 := by
    rw [← hQ]
    exact pow_card_eq_one'
  exact eq_one_of_pow_two_pow_of_pow_three (by simpa using congrArg Subtype.val hk)
    (by simpa using congrArg Subtype.val h3)

theorem yd5_of_Six (hOm : Om4IsoStatement) (c : Ctr5 T Mc M M₁) (hSix : Case1512Six T Mc M)
    {Q : Subgroup (MulAut (V154 T Mc M))} (hQ : QD5 T Mc M M₁ Q) :
    Yd5 T Mc M M₁ (yOf152 T Mc M) ∧
      yOf152 T Mc M ⊓ Subgroup.centralizer (VZ T M₁ : Set G) ≤ pCoreOf 2 M := by
  classical
  have hd := c.std.data
  have c3 := c.std.c1523
  have h3 := c.case_three
  obtain ⟨-, hA, -⟩ := id h3
  have sh : OmShape (mBar0 T Mc M) := S152Y.omShape_mBar0 hOm h3
  obtain ⟨-, -, -, -, -, -, -, hidx⟩ := id hSix
  have hMcV : M ⊓ Mc ≤ Subgroup.normalizer (V154 T Mc M : Set G) := inf_le_left.trans hd.hMV
  have hCV_le : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ M ⊓ Mc := fun x hx =>
    ⟨hx.1, c.std.c1515.centralizer_le hx.2⟩
  have hcard : Nat.card (autOn M (V154 T Mc M)) = Nat.card (autOn (M ⊓ Mc) (V154 T Mc M)) * 3 := by
    rw [card_autOn_eq_relIndex hd.hMV, card_autOn_eq_relIndex hMcV]
    have e : (M ⊓ Mc) ⊓ Subgroup.centralizer (V154 T Mc M : Set G) =
        M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
      le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) (fun x hx => ⟨hCV_le hx, hx.2⟩)
    rw [e, ← hidx]
    exact (Subgroup.relIndex_mul_relIndex _ (M ⊓ Mc) M hCV_le inf_le_left).symm
  have hMb36 : Nat.card (autOn M (V154 T Mc M)) = 36 := by rw [hA]; exact sh.card_X
  have hsyl : IsSylowTwoOf (autOn T (V154 T Mc M)) (mBar0 T Mc M) := by
    rw [← hA]; exact S152Y.isSylowTwoOf_Tb hd
  have hT4 : Nat.card (autOn T (V154 T Mc M)) = 4 :=
    card_eq_four_of_isSylowTwoOf sh.card_X hsyl
  have hMcle : autOn (M ⊓ Mc) (V154 T Mc M) ≤ mBar0 T Mc M := by
    rw [← hA]; exact A4.autOn_mono inf_le_left
  have hTMc : autOn T (V154 T Mc M) ≤ autOn (M ⊓ Mc) (V154 T Mc M) :=
    A4.autOn_mono (le_inf c.T_le_M c.qtfe.t_le_mc)
  have hne1 : autOn (M ⊓ Mc) (V154 T Mc M) ≠ autOn T (V154 T Mc M) := fun h => by
    rw [h] at hcard; omega
  have hneM : autOn (M ⊓ Mc) (V154 T Mc M) ≠ mBar0 T Mc M := fun h => by
    have : Nat.card (autOn (M ⊓ Mc) (V154 T Mc M)) = 36 := by rw [h]; exact sh.card_X
    omega
  obtain ⟨Qc, hQcP, hQc3, hQcn, hMcQ⟩ := abstract_three sh hsyl hTMc hMcle hne1 hneM
  have hQQc : Q ≠ Qc := by
    intro h
    apply c.not_Hb_le_Mcb
    rw [hQ.eq, hMcQ, ← h]
  have hsupP : Q ⊔ Qc = oTwoUpper (mBar0 T Mc M) := by
    have hle : Q ⊔ Qc ≤ oTwoUpper (mBar0 T Mc M) := sup_le hQ.le_P hQcP
    have hd1 : 3 ∣ Nat.card (Q ⊔ Qc : Subgroup _) := hQ.card ▸ Subgroup.card_dvd_of_le le_sup_left
    have hd2 : Nat.card (Q ⊔ Qc : Subgroup _) ∣ 9 :=
      sh.card_O ▸ Subgroup.card_dvd_of_le hle
    have hne : Nat.card (Q ⊔ Qc : Subgroup _) ≠ 3 := by
      intro h3'
      have h1 : Q ⊔ Qc = Q := (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3', hQ.card])).symm
      have h2 : Q ⊔ Qc = Qc :=
        (Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h3', hQc3])).symm
      exact hQQc (h1.symm.trans h2)
    have h9 : Nat.card (Q ⊔ Qc : Subgroup _) = 9 := by
      have hle9 : Nat.card (Q ⊔ Qc : Subgroup _) ≤ 9 := Nat.le_of_dvd (by norm_num) hd2
      generalize Nat.card (Q ⊔ Qc : Subgroup _) = n at *
      interval_cases n <;> omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [sh.card_O, h9])
  have hQcM : Qc ≤ autOn M (V154 T Mc M) := by
    rw [hA]; exact hQcP.trans (oTwoUpper_le _)
  have hQcN : Qc ≤ Subgroup.normalizer (Q : Set (MulAut (V154 T Mc M))) :=
    le_normalizer_of_conj' fun g hg q hq => hQ.norm g (hQcM hg) q hq
  have hP : ∀ x ∈ oTwoUpper (mBar0 T Mc M), ∃ q ∈ Q, ∃ q' ∈ Qc, x = q * q' := by
    intro x hx
    rw [← hsupP] at hx
    have hx' : x ∈ ((Q ⊔ Qc : Subgroup _) : Set _) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Q Qc hQcN] at hx'
    obtain ⟨q, hq, q', hq', rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨q, hq, q', hq', rfl⟩
  have hRcM : rcOf Mc M ≤ M ⊓ Mc := fun x hx =>
    ⟨(pCoreOf_le 2 _ hx).2, (pCoreOf_le 2 _ hx).1⟩
  have hRbMc : autOn (rcOf Mc M) (V154 T Mc M) ≤ autOn (M ⊓ Mc) (V154 T Mc M) :=
    A4.autOn_mono hRcM
  have hRbN : ∀ g ∈ autOn (M ⊓ Mc) (V154 T Mc M), ∀ r ∈ autOn (rcOf Mc M) (V154 T Mc M),
      g * r * g⁻¹ ∈ autOn (rcOf Mc M) (V154 T Mc M) := by
    intro g hg r hr
    obtain ⟨a, haN, haM, rfl⟩ := mem_autOn_iff_exists.mp hg
    obtain ⟨ρ, hρN, hρR, rfl⟩ := mem_autOn_iff_exists.mp hr
    have haρ : a * ρ * a⁻¹ ∈ rcOf Mc M :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (Mc ⊓ M) ⟨haM.2, haM.1⟩) ρ).mp hρR
    have haρN : a * ρ * a⁻¹ ∈ Subgroup.normalizer (V154 T Mc M : Set G) :=
      hd.hMV (hd.rc_le_M haρ)
    rw [← conjAct_conj haN hρN haρN]
    exact mem_autOn_iff_exists.mpr ⟨_, haρN, haρ, rfl⟩
  have hRb2 : IsPGroup 2 (autOn (rcOf Mc M) (V154 T Mc M)) :=
    isPGroup_autOn' (pCoreOf_isPGroup 2 _) (hd.rc_le_M.trans hd.hMV)
  have hMbA : ∀ g ∈ autOn M (V154 T Mc M), g ∈ mBar0 T Mc M := fun g hg => hA ▸ hg
  have hRbMb : autOn (rcOf Mc M) (V154 T Mc M) ≤ autOn M (V154 T Mc M) :=
    A4.autOn_mono hd.rc_le_M
  have hRQc : ∀ r ∈ autOn (rcOf Mc M) (V154 T Mc M), ∀ q ∈ Qc, r * q = q * r := by
    intro r hr q hq
    have hqM : q ∈ autOn (M ⊓ Mc) (V154 T Mc M) := by rw [hMcQ]; exact Subgroup.mem_sup_left hq
    have h1 : r * q * r⁻¹ * q⁻¹ ∈ autOn (rcOf Mc M) (V154 T Mc M) := by
      have : r * q * r⁻¹ * q⁻¹ = r * (q * r⁻¹ * q⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hr (hRbN q hqM r⁻¹ (Subgroup.inv_mem _ hr))
    have h2 : r * q * r⁻¹ * q⁻¹ ∈ Qc :=
      Qc.mul_mem (hQcn r (hMbA r (hRbMb hr)) q hq) (Qc.inv_mem hq)
    have h3 : r * q * r⁻¹ * q⁻¹ ∈ autOn (rcOf Mc M) (V154 T Mc M) ⊓ Qc := ⟨h1, h2⟩
    rw [inf_eq_bot_of_two_group_card_three hRb2 hQc3, Subgroup.mem_bot] at h3
    calc r * q = (r * q * r⁻¹ * q⁻¹) * (q * r) := by group
      _ = q * r := by rw [h3, one_mul]
  have hYP : autOn (yOf152 T Mc M) (V154 T Mc M) ≤ oTwoUpper (mBar0 T Mc M) := by
    rw [← hd.autOn_y0Of]
    exact A4.autOn_mono hd.yOf_le_y0Of
  have hYQ : autOn (yOf152 T Mc M) (V154 T Mc M) ≤ Q := by
    calc autOn (yOf152 T Mc M) (V154 T Mc M)
        = ⁅autOn (yOf152 T Mc M) (V154 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆ := c3.comm_eq
      _ ≤ Q := by
        refine Subgroup.commutator_le.mpr fun a ha r hr => ?_
        obtain ⟨q, hq, q', hq', rfl⟩ := hP a (hYP ha)
        have hq'r : q' * r * q'⁻¹ = r := by
          rw [← hRQc r hr q' hq']; group
        have hrN : r * q⁻¹ * r⁻¹ ∈ Q := hQ.norm r (hRbMb hr) q⁻¹ (Q.inv_mem hq)
        have e : ⁅q * q', r⁆ = q * (r * q⁻¹ * r⁻¹) := by
          calc ⁅q * q', r⁆ = q * (q' * r * q'⁻¹) * q⁻¹ * r⁻¹ := by
                rw [commutatorElement_def]; group
            _ = q * r * q⁻¹ * r⁻¹ := by rw [hq'r]
            _ = q * (r * q⁻¹ * r⁻¹) := by group
        rw [e]
        exact Q.mul_mem hq hrN
  have hYQeq : autOn (yOf152 T Mc M) (V154 T Mc M) = Q := by
    have hdvd : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) ∣ 3 :=
      hQ.card ▸ Subgroup.card_dvd_of_le hYQ
    have hn1 : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) ≠ 1 := fun h =>
      c3.ne_bot (Subgroup.card_eq_one.mp h)
    exact Subgroup.eq_of_le_of_card_ge hYQ (by rw [hQ.card, eq_three_of_dvd hdvd hn1])
  have hYC : yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ pCoreOf 2 M := by
    have hY3 : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) = 3 := by rw [hYQeq]; exact hQ.card
    rcases c3.cases with hi | hii | hiii
    · exfalso
      have h1 := hi.1
      rw [h1, sh.card_O] at hY3
      omega
    · exfalso
      have h1 : oTwoUpper (mBar0 T Mc M) = oTwoUpper (autOn M (V154 T Mc M)) := hii.2.2.2.1
      have h2 : oTwoUpper (autOn M (V154 T Mc M)) = autOn (yOf152 T Mc M) (V154 T Mc M) :=
        hii.2.2.2.2.1
      rw [← h2, ← h1, sh.card_O] at hY3
      omega
    · exact hiii.2.2.2.2.1
  have hYN : M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) := c3.normal
  have hYM : yOf152 T Mc M ≤ M := hd.yOf_le_M
  have hSyl : IsSylowTwoOf T M := isSylowTwoOf_of_le151 c.qtfe.sylow c.T_le_M
  have hPT : pCoreOf 2 M ≤ T := pCoreOf_le_of_isSylowTwoOf hSyl
  have hTH : T ≤ M₁ ⊓ M := c.T_le_H
  have hrcT : rcOf Mc M ≤ T := hd.rc_le_T
  have hYhk : ∀ y ∈ yOf152 T Mc M, ∃ h ∈ M₁ ⊓ M,
      ∃ k ∈ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G), y = h * k := by
    intro y hy
    have hyM : y ∈ M := hYM hy
    have hyN := hd.hMV hyM
    have hmem : conjAct _ ⟨y, hyN⟩ ∈ Q := hYQeq ▸ mem_autOn_iff_exists.mpr ⟨y, hyN, hy, rfl⟩
    exact exists_mul_of_conjAct_mem hd.hMV (inf_le_right : M₁ ⊓ M ≤ M) hyM (hQ.le_Hb hmem)
  have hHcomm : ∀ a b, a ∈ M₁ ⊓ M → b ∈ M₁ ⊓ M → ⁅a, b⁆ ∈ M₁ ⊓ M := fun a b ha hb => by
    rw [commutatorElement_def]
    exact (M₁ ⊓ M).mul_mem ((M₁ ⊓ M).mul_mem ((M₁ ⊓ M).mul_mem ha hb) ((M₁ ⊓ M).inv_mem ha))
      ((M₁ ⊓ M).inv_mem hb)
  have hcommH : ⁅yOf152 T Mc M, rcOf Mc M⁆ ≤ M₁ ⊓ M := by
    refine Subgroup.commutator_le.mpr fun y hy r hr => ?_
    obtain ⟨h, hh, k, hk, rfl⟩ := hYhk y hy
    have hkr : ⁅k, r⁆ ∈ pCoreOf 2 M := by
      have h1 : ⁅r, k⁆ ∈ pCoreOf 2 M :=
        c3.centralizes (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hr) hk)
      rw [← commutatorElement_inv]
      exact (pCoreOf 2 M).inv_mem h1
    have hrH : r ∈ M₁ ⊓ M := hTH (hrcT hr)
    have hkrH : ⁅k, r⁆ ∈ M₁ ⊓ M := hTH (hPT hkr)
    have e : ⁅h * k, r⁆ = (h * ⁅k, r⁆ * h⁻¹) * ⁅h, r⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (M₁ ⊓ M).mul_mem ((M₁ ⊓ M).mul_mem ((M₁ ⊓ M).mul_mem hh hkrH) ((M₁ ⊓ M).inv_mem hh))
      (hHcomm h r hh hrH)
  have hcommY : ⁅yOf152 T Mc M, rcOf Mc M⁆ ≤ yOf152 T Mc M := by
    refine Subgroup.commutator_le.mpr fun y hy r hr => ?_
    have h1 : r * y⁻¹ * r⁻¹ ∈ yOf152 T Mc M :=
      (Subgroup.mem_normalizer_iff.mp (hYN (hd.rc_le_M hr)) y⁻¹).mp ((yOf152 T Mc M).inv_mem hy)
    rw [commutatorElement_def]
    have : y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) := by group
    rw [this]
    exact (yOf152 T Mc M).mul_mem hy h1
  have hYdec : ∀ y ∈ yOf152 T Mc M, ∃ w ∈ ⁅yOf152 T Mc M, rcOf Mc M⁆,
      ∃ κ ∈ yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G), y = w * κ := by
    intro y hy
    have hyM := hYM hy
    have hyN := hd.hMV hyM
    have hmem : conjAct _ ⟨y, hyN⟩ ∈ autOn ⁅yOf152 T Mc M, rcOf Mc M⁆ (V154 T Mc M) := by
      rw [autOn_commutator (hYM.trans hd.hMV) (hd.rc_le_M.trans hd.hMV), ← c3.comm_eq]
      exact mem_autOn_iff_exists.mpr ⟨y, hyN, hy, rfl⟩
    obtain ⟨w, hwN, hwC, hwy⟩ := mem_autOn_iff_exists.mp hmem
    have h2 : conjAct (V154 T Mc M) ((⟨w, hwN⟩ : Subgroup.normalizer (V154 T Mc M : Set G))⁻¹ *
        ⟨y, hyN⟩) = 1 := by
      rw [map_mul, map_inv, hwy]
      exact inv_mul_cancel _
    have h3 : w⁻¹ * y ∈ Subgroup.centralizer (V154 T Mc M : Set G) := A4.conjAct_eq_one_iff.mp h2
    exact ⟨w, hwC, w⁻¹ * y, ⟨(yOf152 T Mc M).mul_mem ((yOf152 T Mc M).inv_mem (hcommY hwC)) hy, h3⟩,
      by group⟩
  have hYH : yOf152 T Mc M ≤ M₁ ⊓ M := by
    intro y hy
    obtain ⟨w, hw, κ, hκ, rfl⟩ := hYdec y hy
    exact (M₁ ⊓ M).mul_mem (hcommH hw) (hTH (hPT (hYC hκ)))
  have hY_not_Mc : ¬ yOf152 T Mc M ≤ M ⊓ Mc := by
    intro h
    apply hQ.not_le_Mcb c
    rw [← hYQeq]
    exact A4.autOn_mono h
  have hYN₁ : yOf152 T Mc M ≤ Subgroup.normalizer (VZ T M₁ : Set G) :=
    hYH.trans (inf_le_left.trans (le_normalizer_VZ T M₁))
  have hYNV : yOf152 T Mc M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hYM.trans hd.hMV
  have hWT : yOf152 T Mc M ⊓ pCoreOf 2 M ≤ T := inf_le_right.trans hPT
  have hWH : M₁ ⊓ M ≤ Subgroup.normalizer ((yOf152 T Mc M ⊓ pCoreOf 2 M : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hYN hg.2, le_normalizer_pCoreOf 2 M hg.2⟩
  have hWV := c.le_centralizer_VZ₁ hWT hWH
  have hcen : yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤
      yOf152 T Mc M ⊓ Subgroup.centralizer (VZ T M₁ : Set G) := fun y hy =>
    ⟨hy.1, hWV ⟨hy.1, hYC hy⟩⟩
  have hcard3 : Nat.card (autOn (yOf152 T Mc M) (VZ T M₁)) = 3 := by
    have hdvd := card_autOn_dvd hYNV hYN₁ hcen
    rw [hYQeq, hQ.card] at hdvd
    refine eq_three_of_dvd hdvd ?_
    intro h1
    have hbot : autOn (yOf152 T Mc M) (VZ T M₁) = ⊥ := Subgroup.card_eq_one.mp h1
    have hcent := le_centralizer_of_autOn_eq_bot hYN₁ hbot
    apply hY_not_Mc
    exact fun y hy => ⟨hYM hy, c.C₁_le_Mc ⟨(hYH hy).1, hcent hy⟩⟩
  have hC1 : yOf152 T Mc M ⊓ Subgroup.centralizer (VZ T M₁ : Set G) ≤ pCoreOf 2 M := by
    have e1 := card_autOn_eq_relIndex hYNV
    have e2 := card_autOn_eq_relIndex hYN₁
    rw [hYQeq, hQ.card] at e1
    rw [hcard3] at e2
    have e3 := Subgroup.relIndex_mul_relIndex
      (yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))
      (yOf152 T Mc M ⊓ Subgroup.centralizer (VZ T M₁ : Set G)) (yOf152 T Mc M) hcen inf_le_left
    rw [← e1, ← e2] at e3
    have e4 : (yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)).relIndex
        (yOf152 T Mc M ⊓ Subgroup.centralizer (VZ T M₁ : Set G)) = 1 := by omega
    exact fun y hy => hYC ⟨hy.1, (Subgroup.relIndex_eq_one.mp e4 hy).2⟩
  refine ⟨⟨hYH, inf_le_right.trans hYN, hcard3, ?_⟩, hC1⟩
  ·
    have hTK : T ≤ M ⊓ Mc := le_inf c.T_le_M c.qtfe.t_le_mc
    have hTM : ¬ 2 ∣ T.relIndex M := hSyl.2.2
    have hrel : (M ⊓ Mc).relIndex (M₁ ⊓ M) = 3 :=
      relIndex_eq_three_of_index_three hidx hTK hTM hTH inf_le_right
        (fun h => c.not_H_le_Mc (h.trans inf_le_right))
    have hTHodd : ¬ 2 ∣ T.relIndex (M₁ ⊓ M) := by
      intro h2
      apply hTM
      rw [← Subgroup.relIndex_mul_relIndex T (M₁ ⊓ M) M hTH inf_le_right]
      exact h2.mul_right _
    have hTN : T ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) := c.T_le_M.trans hYN
    have hYTle : yOf152 T Mc M ⊔ T ≤ M₁ ⊓ M := sup_le hYH hTH
    have hYTK : ¬ yOf152 T Mc M ⊔ T ≤ M ⊓ Mc := fun h => hY_not_Mc (le_sup_left.trans h)
    have hfac2 := exists_mul_of_index_three hrel hTK hTHodd le_sup_right hYTle hYTK
    intro m hm
    obtain ⟨h, hh, k₁, hk₁, rfl⟩ := c.exists_mul m hm
    obtain ⟨w, hw, k, hk, hhk⟩ := hfac2 h hh
    have hw' : w ∈ ((yOf152 T Mc M ⊔ T : Subgroup G) : Set G) := hw
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ T hTN] at hw'
    obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_mul.mp hw'
    have hkH : k ∈ M₁ ⊓ M := by
      have : k = (y * t)⁻¹ * h := by rw [hhk]; group
      rw [this]
      exact (M₁ ⊓ M).mul_mem ((M₁ ⊓ M).inv_mem (hYTle hw)) hh
    refine ⟨y, hy, t * k * k₁, ⟨?_, ?_⟩, ?_⟩
    · exact M₁.mul_mem (M₁.mul_mem (c.T_le_M₁ ht) hkH.1) hk₁.1
    · exact Mc.mul_mem (Mc.mul_mem (c.qtfe.t_le_mc ht) hk.2) (c.C₁_le_Mc hk₁)
    · rw [hhk]; group

end Six

end Q

end C1Pack5

end CFSG.Quasithin
