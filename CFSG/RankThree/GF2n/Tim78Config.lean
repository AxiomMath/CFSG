module

public import CFSG.RankThree.GF2n.Tim78Involution
import CFSG.RankThree.GF2n.Tim77TI
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.RankThree.GF2n.Tim78Frattini
import CFSG.RankThree.GF2n.Tim78RootType
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Hyp218 (M V Q P W : Subgroup G) (g : G) : Prop where
  maxLocal : IsMaximalTwoLocal M
  fitting : generalizedFitting M = pCore 2 M
  maxAb : Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
    IsMulCommutative U) V
  sq_eq_one : ∀ x ∈ V, x ^ 2 = 1
  ti : IsTI V
  ne : conjSubgroup g V ≠ V
  le : conjSubgroup g V ≤ Q
  hQ : Q = inSubgroup (pCore 2) M
  hP : P = Q ⊓ Subgroup.centralizer (V : Set G)
  hW : W = V ⊔ conjSubgroup g V

structure IsOpp (V P : Subgroup G) (g y : G) : Prop where
  le : conjSubgroup y V ≤ P
  ne : conjSubgroup y V ≠ V
  cent : ∀ b ∈ conjSubgroup y V, (∀ a ∈ conjSubgroup g V, b * a = a * b) → b = 1
  cent' : ∀ b ∈ conjSubgroup y V, b ≠ 1 → ∀ a ∈ conjSubgroup g V, a * b = b * a → a = 1

omit [Finite G] in
theorem mem_centralizer_of_forall {W : Subgroup G} {p : G} (h : ∀ w ∈ W, p * w = w * p) :
    p ∈ Subgroup.centralizer (W : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun w hw => (h w hw).symm

omit [Finite G] in
theorem conj_mem_conjSubgroup {V : Subgroup G} {x y a : G} (ha : a ∈ conjSubgroup y V) :
    x * a * x⁻¹ ∈ conjSubgroup (x * y) V := by
  rw [mem_conjSubgroup] at ha ⊢
  rw [show (x * y)⁻¹ * (x * a * x⁻¹) * (x * y) = y⁻¹ * a * y by group]
  exact ha

omit [Finite G] in
theorem conjSubgroup_bot' (g : G) : conjSubgroup g (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _

theorem centralizer_le_normalizer_W (W : Subgroup G) :
    Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (W : Set G) := fun z hz =>
  Subgroup.mem_normalizer_fintype fun w hw => by
    rw [(Subgroup.mem_centralizer_iff.mp hz w hw).symm, mul_inv_cancel_right]
    exact hw

theorem commute_of_inf_centralizer_ne {A V U U' : Subgroup G} {n : ℕ}
    (hA : Assembly.IsElemAbelian 2 A) (hAcard : Nat.card A = 2 ^ (2 * n))
    (hVcard : Nat.card V = 2 ^ n) (hVTI : IsTI V) (hVA : V ≤ A) (hU : U ∈ classIn V A)
    (hU' : U' ∈ classIn V A) (hUV : U ≠ V) (hU'V : U' ≠ V) (hUU' : U ≠ U') {t : G}
    (htV : V ≤ Subgroup.centralizer ({t} : Set G))
    (hC : A ⊓ Subgroup.centralizer ({t} : Set G) ≠ V) : ∀ a ∈ A, t * a = a * t := by
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => comm_of_isElemAbelian hA ha hb
  obtain ⟨⟨g₁, hU⟩, hUA⟩ := hU
  obtain ⟨⟨g₂, hW⟩, hWA⟩ := hU'
  have hUcard : Nat.card U = 2 ^ n := by rw [hU, card_conjSubgroup, hVcard]
  have hWcard : Nat.card U' = 2 ^ n := by rw [hW, card_conjSubgroup, hVcard]
  have hUTI : IsTI U := hU ▸ isTI_conjSubgroup hVTI g₁
  have hWTI : IsTI U' := hW ▸ isTI_conjSubgroup hVTI g₂
  have hVU : V ⊓ U = ⊥ := hU ▸ inf_conjSubgroup_eq_bot_of_isTI hVTI (hU ▸ hUV)
  have hVW : V ⊓ U' = ⊥ := hW ▸ inf_conjSubgroup_eq_bot_of_isTI hVTI (hW ▸ hU'V)
  have hUWbot : U ⊓ U' = ⊥ := by
    have e : U' = conjSubgroup (g₂ * g₁⁻¹) U := by
      rw [hU, hW, ← conjSubgroup_mul, inv_mul_cancel_right]
    rw [e]
    exact inf_conjSubgroup_eq_bot_of_isTI hUTI (e ▸ hUU'.symm)
  have hAVU : V ⊔ U = A := sup_eq_of_inf_eq_bot hA hAcard hVA hUA hVcard hUcard hVU
  have hAVW : V ⊔ U' = A := sup_eq_of_inf_eq_bot hA hAcard hVA hWA hVcard hWcard hVW
  set C := A ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
  have hVC : V ≤ C := le_inf hVA htV
  have hVltC : V < C := lt_of_le_of_ne hVC (Ne.symm hC)
  have hCA : C ≤ A := inf_le_left
  have hA2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  obtain ⟨k, hk⟩ := (hA2.to_le hCA).exists_card_eq
  have hkn : n < k := by
    have := Subgroup.card_lt_of_lt hVltC
    rw [hVcard, hk] at this
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hXC : ∀ X : Subgroup G, X ≤ A → Nat.card X = 2 ^ n → C ⊓ X ≠ ⊥ := by
    intro X hXA hXcard hbot
    have hCX : C ≤ Subgroup.normalizer (X : Set G) := le_normalizer_of_comm fun c hc x hx =>
      hAc c (hCA hc) x (hXA hx)
    have h := PartTwo.Sec6.card_sup_mul_card_inf hCX
    rw [hbot, Subgroup.card_bot, mul_one, hk, hXcard] at h
    have hle : Nat.card (C ⊔ X : Subgroup G) ≤ Nat.card A :=
      Subgroup.card_le_of_le (sup_le hCA hXA)
    rw [h, hAcard, ← pow_add] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    omega
  have hnorm : ∀ X : Subgroup G, IsTI X → X ≤ A → Nat.card X = 2 ^ n →
      ∀ x ∈ X, t * x * t⁻¹ ∈ X := by
    intro X hXTI hXA hXcard
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (hXC X hXA hXcard)
    have hut : t * u = u * t := (Subgroup.mem_centralizer_singleton_iff.mp hu.1.2).symm
    have hmem : u ∈ X ⊓ conjSubgroup t X := by
      refine Subgroup.mem_inf.mpr ⟨hu.2, ?_⟩
      rw [mem_conjSubgroup]
      have : t⁻¹ * u * t = u := by
        calc t⁻¹ * u * t = t⁻¹ * (u * t) := by group
          _ = t⁻¹ * (t * u) := by rw [hut]
          _ = u := by group
      rw [this]
      exact hu.2
    have heq : conjSubgroup t X = X := conjSubgroup_eq_of_isTI hXTI fun h => by
      rw [h] at hmem
      exact hu1 (Subtype.ext (Subgroup.mem_bot.mp hmem))
    intro x hx
    have : t * x * t⁻¹ ∈ conjSubgroup t X := by
      rw [mem_conjSubgroup]
      group
      exact hx
    rwa [heq] at this
  have htU := hnorm U hUTI hUA hUcard
  have htW := hnorm U' hWTI hWA hWcard
  intro a ha
  have hd : ∀ X : Subgroup G, V ⊔ X = A → (∀ x ∈ X, t * x * t⁻¹ ∈ X) → X ≤ A →
      dlt t a ∈ X := by
    intro X hVX htX hXA
    have hXV : X ≤ Subgroup.normalizer (V : Set G) := le_normalizer_of_comm fun x hx v hv =>
      hAc x (hXA hx) v (hVA hv)
    obtain ⟨v, hv, x, hx, rfl⟩ := exists_mul_of_mem_sup hXV (hVX ▸ ha)
    have hvt : t * v * t⁻¹ = v := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (htV hv)
      rw [← this]
      group
    have : dlt t (v * x) = dlt t x := by
      unfold dlt
      calc (v * x)⁻¹ * (t * (v * x) * t⁻¹)
          = x⁻¹ * v⁻¹ * ((t * v * t⁻¹) * (t * x * t⁻¹)) := by group
        _ = x⁻¹ * v⁻¹ * (v * (t * x * t⁻¹)) := by rw [hvt]
        _ = x⁻¹ * (t * x * t⁻¹) := by group
    rw [this]
    exact dlt_mem htX hx
  have h1 : dlt t a ∈ U ⊓ U' := ⟨hd U hAVU htU hUA, hd U' hAVW htW hWA⟩
  rw [hUWbot, Subgroup.mem_bot] at h1
  exact dlt_eq_one_iff.mp h1

namespace Hyp218

variable {M V Q P W : Subgroup G} {g : G} (h : Hyp218 M V Q P W g)
include h

omit [Finite G] in
theorem V_le_M : V ≤ M := h.maxAb.prop.1

omit [Finite G] in
theorem M_le_normalizer : M ≤ Subgroup.normalizer (V : Set G) := h.maxAb.prop.2.1

omit [Finite G] in
theorem elemAb : Assembly.IsElemAbelian 2 V := ⟨h.maxAb.prop.2.2, h.sq_eq_one⟩

omit [Finite G] in
theorem V_comm {a b : G} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a :=
  comm_of_isElemAbelian h.elemAb ha hb

omit [Finite G] in
theorem isPGroup_V : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using h.sq_eq_one x x.2)⟩

omit [Finite G] in
theorem V_ne_bot : V ≠ ⊥ := fun hV => h.ne (by rw [hV, conjSubgroup_bot'])

omit [Finite G] in
theorem normalizer_eq : Subgroup.normalizer (V : Set G) = M := by
  have hloc : IsPLocal 2 (Subgroup.normalizer (V : Set G)) :=
    ⟨V, h.V_ne_bot, h.isPGroup_V, rfl⟩
  by_contra hne
  exact h.maxLocal.2 _ (lt_of_le_of_ne h.M_le_normalizer (Ne.symm hne)) hloc

omit [Finite G] in
theorem isPGroup_Q : IsPGroup 2 Q := h.hQ ▸ (inSubgroup_pCore_two M).1

omit [Finite G] in
theorem Q_le_M : Q ≤ M := h.hQ ▸ (inSubgroup_pCore_two M).2.1

omit [Finite G] in
theorem M_le_normalizer_Q : M ≤ Subgroup.normalizer (Q : Set G) :=
  h.hQ ▸ (inSubgroup_pCore_two M).2.2

omit [Finite G] in
theorem V_le_Q : V ≤ Q := h.hQ ▸ le_inSubgroup_pCore h.V_le_M h.M_le_normalizer h.isPGroup_V

omit [Finite G] in
theorem P_le_Q : P ≤ Q := h.hP ▸ inf_le_left

omit [Finite G] in
theorem P_le_M : P ≤ M := h.P_le_Q.trans h.Q_le_M

omit [Finite G] in
theorem isPGroup_P : IsPGroup 2 P := h.isPGroup_Q.to_le h.P_le_Q

omit [Finite G] in
theorem P_le_centralizer : P ≤ Subgroup.centralizer (V : Set G) := h.hP ▸ inf_le_right

omit [Finite G] in
theorem V_le_P : V ≤ P := by
  rw [h.hP]
  exact le_inf h.V_le_Q fun v hv => mem_centralizer_of_forall fun w hw => h.V_comm hv hw

omit [Finite G] in
theorem M_le_normalizer_P : M ≤ Subgroup.normalizer (P : Set G) := fun m hm => by
  rw [h.hP]
  exact mem_normalizer_inf (h.M_le_normalizer_Q hm)
    (mem_normalizer_centralizer (h.M_le_normalizer hm))

omit [Finite G] in
theorem V1_le_normalizer : conjSubgroup g V ≤ Subgroup.normalizer (V : Set G) :=
  h.le.trans (h.Q_le_M.trans h.M_le_normalizer)

theorem W_elemAb : Assembly.IsElemAbelian 2 W :=
  h.hW ▸ Tim77.tim77_2_3 h.elemAb h.ti h.V1_le_normalizer

theorem W_comm {a b : G} (ha : a ∈ W) (hb : b ∈ W) : a * b = b * a :=
  comm_of_isElemAbelian h.W_elemAb ha hb

omit [Finite G] in
theorem V_le_W : V ≤ W := h.hW ▸ le_sup_left

omit [Finite G] in
theorem V1_le_W : conjSubgroup g V ≤ W := h.hW ▸ le_sup_right

theorem V1_le_P : conjSubgroup g V ≤ P := by
  rw [h.hP]
  exact le_inf h.le fun a ha => mem_centralizer_of_forall fun v hv =>
    h.W_comm (h.V1_le_W ha) (h.V_le_W hv)

theorem W_le_P : W ≤ P := h.hW ▸ sup_le h.V_le_P h.V1_le_P

theorem inf_V1 : V ⊓ conjSubgroup g V = ⊥ := inf_conjSubgroup_eq_bot_of_isTI h.ti h.ne

omit [Finite G] in
theorem exists_mul_of_mem_W {w : G} (hw : w ∈ W) :
    ∃ v ∈ V, ∃ a ∈ conjSubgroup g V, w = v * a :=
  exists_mul_of_mem_sup h.V1_le_normalizer (h.hW ▸ hw)

omit [Finite G] in
theorem hP' : P = inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G) := by
  rw [h.hP, h.hQ]

theorem frattini_P_le : inSubgroup frattini P ≤ V :=
  (tim78_2_9_beta_of_elementary h.fitting h.maxAb h.sq_eq_one h.hP').1

theorem V_eq_center : V = P ⊓ Subgroup.centralizer (P : Set G) :=
  (tim78_2_9_beta_of_elementary h.fitting h.maxAb h.sq_eq_one h.hP').2

theorem M_inf_centralizer_P : M ⊓ Subgroup.centralizer (P : Set G) = V := by
  rw [tim78_2_9_alpha h.fitting h.V_le_M h.M_le_normalizer h.maxAb.prop.2.2 h.hP',
    ← h.V_eq_center]

theorem commutator_mem {a b : G} (ha : a ∈ P) (hb : b ∈ P) : ⁅a, b⁆ ∈ V :=
  h.frattini_P_le (commutatorElement_mem_inSubgroup_frattini h.isPGroup_P ha hb)

theorem sq_mem {a : G} (ha : a ∈ P) : a ^ 2 ∈ V :=
  h.frattini_P_le (sq_mem_inSubgroup_frattini h.isPGroup_P ha)

omit [Finite G] in
theorem central {a v : G} (ha : a ∈ P) (hv : v ∈ V) : a * v = v * a :=
  (Subgroup.mem_centralizer_iff.mp (h.P_le_centralizer ha) v hv).symm

theorem P_le_normalizer_W : P ≤ Subgroup.normalizer (W : Set G) := fun p hp =>
  Subgroup.mem_normalizer_fintype fun w hw => by
    have h1 : p * w * p⁻¹ = ⁅p, w⁆ * w := by rw [commutatorElement_def]; group
    rw [h1]
    exact W.mul_mem (h.V_le_W (h.commutator_mem hp (h.W_le_P hw))) hw

theorem inf_conj (y : G) (hUV : conjSubgroup y V ≠ V) : V ⊓ conjSubgroup y V = ⊥ :=
  inf_conjSubgroup_eq_bot_of_isTI h.ti hUV

theorem comm_of_mem_normalizer {y : G} (hU : conjSubgroup y V ≤ P) (hUV : conjSubgroup y V ≠ V)
    {p : G} (hp : p ∈ P) (hpU : p ∈ Subgroup.normalizer (conjSubgroup y V : Set G)) :
    ∀ a ∈ conjSubgroup y V, p * a = a * p := by
  intro a ha
  have h1 : ⁅p, a⁆ ∈ V := h.commutator_mem hp (hU ha)
  have h2 : ⁅p, a⁆ ∈ conjSubgroup y V := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (conj_mem_of_mem_normalizer hpU ha) (Subgroup.inv_mem _ ha)
  have h3 : ⁅p, a⁆ ∈ V ⊓ conjSubgroup y V := ⟨h1, h2⟩
  rw [h.inf_conj y hUV, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
  exact h3

theorem comm_of_comm {y : G} (hU : conjSubgroup y V ≤ P) (hUV : conjSubgroup y V ≠ V)
    {p : G} (hp : p ∈ P) {u : G} (hu : u ∈ conjSubgroup y V) (hu1 : u ≠ 1)
    (hpu : p * u = u * p) : ∀ a ∈ conjSubgroup y V, p * a = a * p := by
  refine h.comm_of_mem_normalizer hU hUV hp ?_
  rw [← conjSubgroup_eq_self_iff, ← conjSubgroup_mul]
  refine conjSubgroup_eq_of_inf_ne_bot h.ti fun hbot => hu1 ?_
  have hmem : u ∈ conjSubgroup (p * y) V ⊓ conjSubgroup y V := by
    refine Subgroup.mem_inf.mpr ⟨?_, hu⟩
    rw [conjSubgroup_mul, mem_conjSubgroup]
    have : p⁻¹ * u * p = u := by
      calc p⁻¹ * u * p = p⁻¹ * (u * p) := by group
        _ = p⁻¹ * (p * u) := by rw [hpu]
        _ = u := by group
    rw [this]
    exact hu
  rw [hbot] at hmem
  exact hmem

theorem conj_le_P {m : G} (hm : m ∈ M) : conjSubgroup (m * g) V ≤ P := by
  intro a ha
  have h1 : m⁻¹ * a * m ∈ conjSubgroup g V := by
    rw [mem_conjSubgroup] at ha ⊢
    rw [show g⁻¹ * (m⁻¹ * a * m) * g = (m * g)⁻¹ * a * (m * g) by group]
    exact ha
  have h2 := conj_mem_of_mem_normalizer (h.M_le_normalizer_P hm) (h.V1_le_P h1)
  rwa [show m * (m⁻¹ * a * m) * m⁻¹ = a by group] at h2

theorem exists_noncomm : ∃ m ∈ M, ∃ a ∈ conjSubgroup g V, ∃ b ∈ conjSubgroup (m * g) V,
    a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hcc : ∀ m₁ ∈ M, ∀ m₂ ∈ M, ∀ a ∈ conjSubgroup (m₁ * g) V,
      ∀ b ∈ conjSubgroup (m₂ * g) V, a * b = b * a := by
    intro m₁ hm₁ m₂ hm₂ a ha b hb
    have ha' : m₁⁻¹ * a * m₁ ∈ conjSubgroup g V := by
      rw [mem_conjSubgroup] at ha ⊢
      rw [show g⁻¹ * (m₁⁻¹ * a * m₁) * g = (m₁ * g)⁻¹ * a * (m₁ * g) by group]
      exact ha
    have hb' : m₁⁻¹ * b * m₁ ∈ conjSubgroup ((m₁⁻¹ * m₂) * g) V := by
      rw [mem_conjSubgroup] at hb ⊢
      rw [show (m₁⁻¹ * m₂ * g)⁻¹ * (m₁⁻¹ * b * m₁) * (m₁⁻¹ * m₂ * g) =
        (m₂ * g)⁻¹ * b * (m₂ * g) by group]
      exact hb
    have := hcon _ (M.mul_mem (M.inv_mem hm₁) hm₂) _ ha' _ hb'
    calc a * b = m₁ * ((m₁⁻¹ * a * m₁) * (m₁⁻¹ * b * m₁)) * m₁⁻¹ := by group
      _ = m₁ * ((m₁⁻¹ * b * m₁) * (m₁⁻¹ * a * m₁)) * m₁⁻¹ := by rw [this]
      _ = b * a := by group
  set S : Set G := (V : Set G) ∪ {x | ∃ m ∈ M, x ∈ conjSubgroup (m * g) V} with hS
  have hSP : ∀ x ∈ S, x ∈ P := by
    rintro x (hx | ⟨m, hm, hx⟩)
    · exact h.V_le_P hx
    · exact h.conj_le_P hm hx
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x (hx | ⟨m, hm, hx⟩) y (hy | ⟨m', hm', hy⟩)
    · exact h.V_comm hx hy
    · exact (h.central (h.conj_le_P hm' hy) hx).symm
    · exact h.central (h.conj_le_P hm hx) hy
    · exact hcc m hm m' hm' x hx y hy
  set N := Subgroup.closure S with hN
  have hNc : IsMulCommutative N := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have key : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
      intro a ha b hb
      induction ha using Subgroup.closure_induction with
      | mem a ha =>
        induction hb using Subgroup.closure_induction with
        | mem b hb => exact hScomm a ha b hb
        | one => simp
        | mul b c _ _ hb hc => rw [← mul_assoc, hb, mul_assoc, hc, mul_assoc]
        | inv b _ hb =>
          calc a * b⁻¹ = b⁻¹ * (b * a) * b⁻¹ := by group
            _ = b⁻¹ * (a * b) * b⁻¹ := by rw [hb]
            _ = b⁻¹ * a := by group
      | one => simp
      | mul a c _ _ ha hc => rw [mul_assoc, hc, ← mul_assoc, ha, mul_assoc]
      | inv a _ ha =>
        calc a⁻¹ * b = a⁻¹ * (b * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * b) * a⁻¹ := by rw [ha]
          _ = b * a⁻¹ := by group
    exact key x x.2 y y.2
  have hNM : N ≤ M := (Subgroup.closure_le _).mpr fun x hx => h.P_le_M (hSP x hx)
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := by
    intro m hm
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hle : N ≤ N.comap (MulAut.conj m).toMonoidHom := by
      rw [hN, Subgroup.closure_le]
      rintro x (hx | ⟨m', hm', hx⟩)
      · exact Subgroup.subset_closure (Or.inl (conj_mem_of_mem_normalizer
          (h.M_le_normalizer hm) hx))
      · refine Subgroup.subset_closure (Or.inr ⟨m * m', M.mul_mem hm hm', ?_⟩)
        have := conj_mem_conjSubgroup (x := m) hx
        rwa [← mul_assoc] at this
    exact hle hn
  have hVN : V ≤ N := fun v hv => Subgroup.subset_closure (Or.inl hv)
  have hNV : N ≤ V := h.maxAb.le_of_ge ⟨hNM, hMN, hNc⟩ hVN
  have hV1 : conjSubgroup g V ≤ V := fun a ha =>
    hNV (Subgroup.subset_closure (Or.inr ⟨1, M.one_mem, by rwa [one_mul]⟩))
  exact h.ne (Subgroup.eq_of_le_of_card_ge hV1 (by rw [card_conjSubgroup]))

theorem exists_isOpp : ∃ y : G, IsOpp V P g y := by
  obtain ⟨m, hm, a₀, ha₀, b₀, hb₀, hab⟩ := h.exists_noncomm
  have hle : conjSubgroup (m * g) V ≤ P := h.conj_le_P hm
  have hne : conjSubgroup (m * g) V ≠ V := by
    intro heq
    apply h.ne
    have e : conjSubgroup g V = conjSubgroup m⁻¹ (conjSubgroup (m * g) V) := by
      rw [← conjSubgroup_mul, inv_mul_cancel_left]
    rw [e, heq, conjSubgroup_eq_self_iff]
    exact h.M_le_normalizer (M.inv_mem hm)
  have hcent : ∀ b ∈ conjSubgroup (m * g) V, (∀ a ∈ conjSubgroup g V, b * a = a * b) → b = 1 := by
    intro b hb hba
    by_contra hb1
    apply hab
    by_cases ha1 : a₀ = 1
    · rw [ha1, one_mul, mul_one]
    · exact h.comm_of_comm hle hne (h.V1_le_P ha₀) hb hb1 (hba a₀ ha₀).symm b₀ hb₀
  refine ⟨m * g, hle, hne, hcent, fun b hb hb1 a ha hab' => ?_⟩
  by_contra ha1
  exact hb1 (hcent b hb fun a' ha' =>
    h.comm_of_comm (y := g) h.V1_le_P h.ne (hle hb) ha ha1 hab'.symm a' ha')

theorem conj_V1_le_W {b : G} (hb : b ∈ P) : conjSubgroup (b * g) V ≤ W := by
  intro x hx
  have h1 : b⁻¹ * x * b ∈ conjSubgroup g V := by
    rw [mem_conjSubgroup] at hx ⊢
    rw [show g⁻¹ * (b⁻¹ * x * b) * g = (b * g)⁻¹ * x * (b * g) by group]
    exact hx
  have h2 := conj_mem_of_mem_normalizer (h.P_le_normalizer_W hb) (h.V1_le_W h1)
  rwa [show b * (b⁻¹ * x * b) * b⁻¹ = x by group] at h2

omit [Finite G] in
theorem conj_V1_ne {b : G} (hb : b ∈ P) : conjSubgroup (b * g) V ≠ V := by
  intro heq
  apply h.ne
  have e : conjSubgroup g V = conjSubgroup b⁻¹ (conjSubgroup (b * g) V) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_left]
  rw [e, heq, conjSubgroup_eq_self_iff]
  exact h.M_le_normalizer (M.inv_mem (h.P_le_M hb))

theorem mem_centralizer_W {p : G} (hp : p ∈ P)
    (hpV1 : p ∈ Subgroup.normalizer (conjSubgroup g V : Set G)) :
    p ∈ Subgroup.centralizer (W : Set G) := by
  have h1 := h.comm_of_mem_normalizer h.V1_le_P h.ne hp hpV1
  refine mem_centralizer_of_forall fun w hw => ?_
  obtain ⟨v, hv, a, ha, rfl⟩ := h.exists_mul_of_mem_W hw
  rw [← mul_assoc, h.central hp hv, mul_assoc, h1 a ha, mul_assoc]

variable {y : G} (hy : IsOpp V P g y)
include hy

theorem exists_commutator_eq {a : G} (ha : a ∈ conjSubgroup g V) (ha1 : a ≠ 1) {v : G}
    (hv : v ∈ V) : ∃ b ∈ conjSubgroup y V, ⁅b, a⁆ = v := by
  let f : conjSubgroup y V → V := fun b => ⟨⁅(b : G), a⁆, h.commutator_mem (hy.le b.2)
    (h.V1_le_P ha)⟩
  have hf : Function.Injective f := by
    intro b b' hbb'
    have e : ⁅(b : G), a⁆ = ⁅(b' : G), a⁆ := congrArg Subtype.val hbb'
    rw [commutatorElement_def, commutatorElement_def] at e
    have e' : ((b' : G)⁻¹ * b) * a = a * ((b' : G)⁻¹ * b) := by
      have : (b : G) * a * (b : G)⁻¹ = (b' : G) * a * (b' : G)⁻¹ := by
        simpa using congrArg (· * a) e
      calc ((b' : G)⁻¹ * b) * a = (b' : G)⁻¹ * ((b : G) * a * (b : G)⁻¹) * b := by group
        _ = (b' : G)⁻¹ * ((b' : G) * a * (b' : G)⁻¹) * b := by rw [this]
        _ = a * ((b' : G)⁻¹ * b) := by group
    have hmem : (b' : G)⁻¹ * b ∈ conjSubgroup y V :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ b'.2) b.2
    by_contra hne
    have hne' : (b' : G)⁻¹ * b ≠ 1 := by
      intro h1
      apply hne
      apply Subtype.ext
      calc (b : G) = b' * ((b' : G)⁻¹ * b) := by group
        _ = b' := by rw [h1, mul_one]
    exact ha1 (hy.cent' _ hmem hne' a ha e'.symm)
  have hcard : Nat.card V ≤ Nat.card (conjSubgroup y V) := by rw [card_conjSubgroup]
  obtain ⟨b, hb⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨v, hv⟩
  exact ⟨b, b.2, congrArg Subtype.val hb⟩

theorem mem_cover {w : G} (hw : w ∈ W) :
    w ∈ V ∨ ∃ b ∈ conjSubgroup y V, w ∈ conjSubgroup (b * g) V := by
  obtain ⟨v, hv, a, ha, rfl⟩ := h.exists_mul_of_mem_W hw
  by_cases ha1 : a = 1
  · left
    rw [ha1, mul_one]
    exact hv
  right
  obtain ⟨b, hb, hba⟩ := h.exists_commutator_eq hy ha ha1 hv
  refine ⟨b, hb, ?_⟩
  have e : v * a = b * a * b⁻¹ := by
    rw [← hba, commutatorElement_def]
    group
  rw [e]
  exact conj_mem_conjSubgroup ha

theorem mem_classIn_iff {U : Subgroup G} :
    U ∈ classIn V W ↔ U = V ∨ ∃ b ∈ conjSubgroup y V, U = conjSubgroup (b * g) V := by
  constructor
  · rintro ⟨⟨x, rfl⟩, hUW⟩
    by_cases hUV : conjSubgroup x V = V
    · exact Or.inl hUV
    right
    have hne : conjSubgroup x V ≠ ⊥ := fun hb => h.V_ne_bot (by
      have := card_conjSubgroup x V
      rw [hb, Subgroup.card_bot] at this
      exact Subgroup.card_eq_one.mp this.symm)
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
    rcases h.mem_cover hy (hUW hu) with huV | ⟨b, hb, hub⟩
    · exfalso
      have : u ∈ V ⊓ conjSubgroup x V := ⟨huV, hu⟩
      rw [h.inf_conj x hUV] at this
      exact hu1' this
    refine ⟨b, hb, conjSubgroup_eq_of_inf_ne_bot h.ti fun hbot => hu1' ?_⟩
    have : u ∈ conjSubgroup x V ⊓ conjSubgroup (b * g) V := ⟨hu, hub⟩
    rw [hbot] at this
    exact this
  · rintro (hU | ⟨b, hb, hU⟩)
    · rw [hU]
      exact ⟨⟨1, (conjSubgroup_one V).symm⟩, h.V_le_W⟩
    · rw [hU]
      exact ⟨⟨b * g, rfl⟩, h.conj_V1_le_W (hy.le hb)⟩

theorem partition {w : G} (hw : w ∈ W) (hw1 : w ≠ 1) : ∃! U, U ∈ classIn V W ∧ w ∈ U := by
  have hex : ∃ U, U ∈ classIn V W ∧ w ∈ U := by
    rcases h.mem_cover hy hw with hwV | ⟨b, hb, hwb⟩
    · exact ⟨V, (h.mem_classIn_iff hy).mpr (Or.inl rfl), hwV⟩
    · exact ⟨_, (h.mem_classIn_iff hy).mpr (Or.inr ⟨b, hb, rfl⟩), hwb⟩
  obtain ⟨U, hU, hwU⟩ := hex
  refine ⟨U, ⟨hU, hwU⟩, fun U' ⟨hU', hwU'⟩ => ?_⟩
  obtain ⟨⟨x, rfl⟩, -⟩ := hU
  obtain ⟨⟨x', rfl⟩, -⟩ := hU'
  refine conjSubgroup_eq_of_inf_ne_bot h.ti fun hbot => hw1 ?_
  have : w ∈ conjSubgroup x' V ⊓ conjSubgroup x V := ⟨hwU', hwU⟩
  rw [hbot] at this
  exact this

theorem exists_conj_eq {U U' : Subgroup G} (hU : U ∈ classIn V W) (hUV : U ≠ V)
    (hU' : U' ∈ classIn V W) (hU'V : U' ≠ V) : ∃ p ∈ P, conjSubgroup p U = U' := by
  obtain hU | ⟨b, hb, rfl⟩ := (h.mem_classIn_iff hy).mp hU
  · exact absurd hU hUV
  obtain hU' | ⟨b', hb', rfl⟩ := (h.mem_classIn_iff hy).mp hU'
  · exact absurd hU' hU'V
  refine ⟨b' * b⁻¹, hy.le (Subgroup.mul_mem _ hb' (Subgroup.inv_mem _ hb)), ?_⟩
  rw [← conjSubgroup_mul, show b' * b⁻¹ * (b * g) = b' * g by group]

theorem exists_mem_mul_mem_centralizer {p : G} (hp : p ∈ P) :
    ∃ b ∈ conjSubgroup y V, b⁻¹ * p ∈ Subgroup.centralizer (W : Set G) := by
  have hU : conjSubgroup (p * g) V ∈ classIn V W := ⟨⟨p * g, rfl⟩, h.conj_V1_le_W hp⟩
  obtain hU' | ⟨b, hb, hbU⟩ := (h.mem_classIn_iff hy).mp hU
  · exact absurd hU' (h.conj_V1_ne hp)
  refine ⟨b, hb, h.mem_centralizer_W (P.mul_mem (P.inv_mem (hy.le hb)) hp) ?_⟩
  rw [← conjSubgroup_eq_self_iff, ← conjSubgroup_mul, mul_assoc, conjSubgroup_mul, hbU,
    ← conjSubgroup_mul, inv_mul_cancel_left]

theorem mem_of_commute {p : G} (hp : p ∈ P) (hpW : p ∉ Subgroup.centralizer (W : Set G))
    {w : G} (hw : w ∈ W) (hpw : p * w = w * p) : w ∈ V := by
  by_contra hwV
  rcases h.mem_cover hy hw with hwV' | ⟨b, hb, hwb⟩
  · exact hwV hwV'
  have hw1 : w ≠ 1 := fun h1 => hwV (h1 ▸ V.one_mem)
  have hUP : conjSubgroup (b * g) V ≤ P := (h.conj_V1_le_W (hy.le hb)).trans h.W_le_P
  have hpU := h.comm_of_comm hUP (h.conj_V1_ne (hy.le hb)) hp hwb hw1 hpw
  apply hpW
  have hsup : V ⊔ conjSubgroup (b * g) V = W := by
    have hUV : V ≤ Subgroup.normalizer (conjSubgroup (b * g) V : Set G) :=
      le_normalizer_of_comm fun v hv u hu => h.W_comm (h.V_le_W hv)
        (h.conj_V1_le_W (hy.le hb) hu)
    have hc := PartTwo.Sec6.card_sup_mul_card_inf hUV
    rw [h.inf_conj _ (h.conj_V1_ne (hy.le hb)), Subgroup.card_bot, mul_one,
      card_conjSubgroup] at hc
    have hc' := PartTwo.Sec6.card_sup_mul_card_inf h.V1_le_normalizer
    rw [inf_comm, h.inf_V1, Subgroup.card_bot, mul_one, card_conjSubgroup, sup_comm,
      ← h.hW] at hc'
    exact Subgroup.eq_of_le_of_card_ge (sup_le h.V_le_W (h.conj_V1_le_W (hy.le hb)))
      (by rw [hc, hc'])
  refine mem_centralizer_of_forall fun x hx => ?_
  rw [← hsup] at hx
  have hN : conjSubgroup (b * g) V ≤ Subgroup.normalizer (V : Set G) :=
    le_normalizer_of_comm fun u hu v hv => h.W_comm (h.conj_V1_le_W (hy.le hb) hu)
      (h.V_le_W hv)
  obtain ⟨v, hv, u, hu, rfl⟩ := exists_mul_of_mem_sup hN hx
  rw [← mul_assoc, h.central hp hv, mul_assoc, hpU u hu, mul_assoc]

omit hy in
theorem card_W : Nat.card W = Nat.card V * Nat.card V := by
  have hc' := PartTwo.Sec6.card_sup_mul_card_inf h.V1_le_normalizer
  rw [inf_comm, h.inf_V1, Subgroup.card_bot, mul_one, card_conjSubgroup, sup_comm,
    ← h.hW] at hc'
  exact hc'

omit [Finite G] hy in
theorem conj_ne_bot (x : G) : conjSubgroup x V ≠ ⊥ := fun hb => h.V_ne_bot (by
  have := card_conjSubgroup x V
  rw [hb, Subgroup.card_bot] at this
  exact Subgroup.card_eq_one.mp this.symm)

theorem mem_V_of_commute {z : G} (hzP : z ∈ P)
    (hzD : ∀ d ∈ P ⊓ Subgroup.centralizer (W : Set G), z * d = d * z) {x : G}
    (hx : x ∈ conjSubgroup y V) (hx1 : x ≠ 1) (hxz : x * z = z * x) : z ∈ V := by
  have hzV2 := h.comm_of_comm hy.le hy.ne hzP hx hx1 hxz.symm
  rw [h.V_eq_center]
  refine ⟨hzP, mem_centralizer_of_forall fun p hp => ?_⟩
  obtain ⟨b, hb, hbp⟩ := h.exists_mem_mul_mem_centralizer hy hp
  have hd := hzD _ ⟨P.mul_mem (P.inv_mem (hy.le hb)) hp, hbp⟩
  calc z * p = z * (b * (b⁻¹ * p)) := by group
    _ = b * (z * (b⁻¹ * p)) := by rw [← mul_assoc, hzV2 b hb, mul_assoc]
    _ = b * ((b⁻¹ * p) * z) := by rw [hd]
    _ = p * z := by group

theorem inf_centralizer_D :
    P ⊓ Subgroup.centralizer ((P ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) =
      W := by
  set D : Subgroup G := P ⊓ Subgroup.centralizer (W : Set G) with hD
  set Z : Subgroup G := P ⊓ Subgroup.centralizer (D : Set G) with hZ
  have hWZ : W ≤ Z := le_inf h.W_le_P fun w hw => mem_centralizer_of_forall fun d hd =>
    Subgroup.mem_centralizer_iff.mp hd.2 w hw
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (h.conj_ne_bot y)
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hxP : x ∈ P := hy.le hx
  let f : Z →* V :=
    { toFun := fun z => ⟨⁅x, (z : G)⁆, h.commutator_mem hxP z.2.1⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun z z' => Subtype.ext (by
        show ⁅x, (z : G) * z'⁆ = ⁅x, (z : G)⁆ * ⁅x, (z' : G)⁆
        have hc : (z : G) * ⁅x, (z' : G)⁆ = ⁅x, (z' : G)⁆ * z :=
          h.central z.2.1 (h.commutator_mem hxP z'.2.1)
        calc ⁅x, (z : G) * z'⁆ = ⁅x, (z : G)⁆ * ((z : G) * ⁅x, (z' : G)⁆ * (z : G)⁻¹) := by
              simp only [commutatorElement_def]; group
          _ = ⁅x, (z : G)⁆ * ⁅x, (z' : G)⁆ := by rw [hc, mul_inv_cancel_right]) }
  have hker : ∀ z : Z, f z = 1 → (z : G) ∈ V := by
    intro z hz
    have hxz : x * z = z * x :=
      commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hz)
    exact h.mem_V_of_commute hy z.2.1
      (fun d hd => (Subgroup.mem_centralizer_iff.mp z.2.2 d hd).symm)
      hx hx1' hxz
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card f.ker ≤ Nat.card V :=
    Nat.card_le_card_of_injective (fun z => (⟨((z : Z) : G), hker z z.2⟩ : V))
      fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab))
  have h3 : Nat.card (Set.range f) ≤ Nat.card V :=
    Nat.card_le_card_of_injective (fun r : Set.range f => (r : V)) Subtype.val_injective
  have hcard : Nat.card Z ≤ Nat.card W := by
    rw [h.card_W, ← h1]
    exact Nat.mul_le_mul h2 h3
  exact (Subgroup.eq_of_le_of_card_ge hWZ hcard).symm

omit hy in
theorem mem_Q_of_commutator_mem {t : G} (htM : t ∈ M) (htV : ∀ v ∈ V, t * v = v * t)
    (htP : ∀ p ∈ P, ⁅t, p⁆ ∈ V) : t ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Subgroup G :=
    { carrier := {m | m ∈ M ∧ (∀ v ∈ V, m * v = v * m) ∧ ∀ p ∈ P, ⁅m, p⁆ ∈ V}
      one_mem' := ⟨M.one_mem, fun v _ => by group, fun p _ => by simp⟩
      mul_mem' := by
        rintro m₁ m₂ ⟨hm₁, hv₁, hp₁⟩ ⟨hm₂, hv₂, hp₂⟩
        refine ⟨M.mul_mem hm₁ hm₂, fun v hv => by rw [mul_assoc, hv₂ v hv, ← mul_assoc,
          hv₁ v hv, mul_assoc], fun p hp => ?_⟩
        have e : ⁅m₁ * m₂, p⁆ = (m₁ * ⁅m₂, p⁆ * m₁⁻¹) * ⁅m₁, p⁆ := by
          simp only [commutatorElement_def]; group
        have hc : m₁ * ⁅m₂, p⁆ * m₁⁻¹ = ⁅m₂, p⁆ := by
          rw [hv₁ _ (hp₂ p hp), mul_inv_cancel_right]
        rw [e, hc]
        exact V.mul_mem (hp₂ p hp) (hp₁ p hp)
      inv_mem' := by
        rintro m ⟨hm, hv, hp⟩
        refine ⟨M.inv_mem hm, fun v hv' => ?_, fun p hp' => ?_⟩
        · calc m⁻¹ * v = m⁻¹ * (v * m) * m⁻¹ := by group
            _ = m⁻¹ * (m * v) * m⁻¹ := by rw [hv v hv']
            _ = v * m⁻¹ := by group
        · have hp'' : m⁻¹ * p * m ∈ P := by
            have := conj_mem_of_mem_normalizer (h.M_le_normalizer_P (M.inv_mem hm)) hp'
            rwa [inv_inv] at this
          have e : ⁅m⁻¹, p⁆ = ⁅m, m⁻¹ * p * m⁆⁻¹ := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact V.inv_mem (hp _ hp'') }
  have hTM : T ≤ M := fun m hm => hm.1
  have hMT : M ≤ Subgroup.normalizer (T : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun m ⟨hm, hv, hp⟩ => ⟨M.mul_mem (M.mul_mem hx hm)
      (M.inv_mem hx), fun v hv' => ?_, fun p hp' => ?_⟩
    · have hv'' : x⁻¹ * v * x ∈ V := by
        have := conj_mem_of_mem_normalizer (h.M_le_normalizer (M.inv_mem hx)) hv'
        rwa [inv_inv] at this
      calc x * m * x⁻¹ * v = x * (m * (x⁻¹ * v * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * v * x) * m) * x⁻¹ := by rw [hv _ hv'']
        _ = v * (x * m * x⁻¹) := by group
    · have hp'' : x⁻¹ * p * x ∈ P := by
        have := conj_mem_of_mem_normalizer (h.M_le_normalizer_P (M.inv_mem hx)) hp'
        rwa [inv_inv] at this
      have e : ⁅x * m * x⁻¹, p⁆ = x * ⁅m, x⁻¹ * p * x⁆ * x⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact conj_mem_of_mem_normalizer (h.M_le_normalizer hx) (hp _ hp'')
  have hT2 : IsPGroup 2 T := by
    intro u
    obtain ⟨a, ha, -⟩ := exists_odd_orderOf_pow (u : G)
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    set w := (u : G) ^ 2 ^ a with hw
    have hwT : w ∈ T := T.pow_mem u.2 _
    obtain ⟨hwM, hwV, hwP⟩ := hwT
    have hwc : ∀ p ∈ P, w * p = p * w := by
      intro p hp
      set v := ⁅w, p⁆ with hv
      have hvV : v ∈ V := hwP p hp
      have hconj : w * p * w⁻¹ = v * p := by rw [hv, commutatorElement_def]; group
      have hk : ∀ k : ℕ, w ^ k * p * (w ^ k)⁻¹ = v ^ k * p := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          calc w ^ (k + 1) * p * (w ^ (k + 1))⁻¹ = w * (w ^ k * p * (w ^ k)⁻¹) * w⁻¹ := by
                rw [pow_succ']; group
            _ = w * (v ^ k * p) * w⁻¹ := by rw [ih]
            _ = (w * v ^ k * w⁻¹) * (w * p * w⁻¹) := by group
            _ = v ^ k * (v * p) := by
                rw [hconj, (Commute.pow_right (hwV v hvV) k).eq, mul_inv_cancel_right]
            _ = v ^ (k + 1) * p := by rw [pow_succ]; group
      have h1 := hk (orderOf w)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, right_eq_mul] at h1
      have hv1 : v = 1 := by
        obtain ⟨j, hj⟩ := ha
        have hv2 : v ^ 2 = 1 := h.sq_eq_one v hvV
        rw [hj, pow_succ, pow_mul, hv2, one_pow, one_mul] at h1
        exact h1
      have := commutatorElement_eq_one_iff_mul_comm.mp (hv ▸ hv1)
      exact this
    have hwV' : w ∈ V := by
      rw [← h.M_inf_centralizer_P]
      exact ⟨hwM, mem_centralizer_of_forall hwc⟩
    exact eq_one_of_odd_of_isPGroup h.isPGroup_V hwV' ha
  have hTQ : T ≤ Q := h.hQ ▸ le_inSubgroup_pCore hTM hMT hT2
  exact hTQ ⟨htM, htV, htP⟩

omit hy in
theorem mem_M_of_mem_centralizer {z : G} (hz : z ∈ Subgroup.centralizer (W : Set G)) : z ∈ M := by
  rw [← h.normalizer_eq]
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  rw [(Subgroup.mem_centralizer_iff.mp hz v (h.V_le_W hv)).symm, mul_inv_cancel_right]
  exact hv

omit hy in
theorem isPGroup_W : IsPGroup 2 W := fun x => ⟨1, Subtype.ext (by simpa using h.W_elemAb.2 x x.2)⟩

omit [Finite G] hy in
theorem mem_normalizer_D {z : G} (hzM : z ∈ M) (hzW : z ∈ Subgroup.normalizer (W : Set G)) :
    z ∈ Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) :=
  mem_normalizer_inf (h.M_le_normalizer_P hzM) (mem_normalizer_centralizer hzW)

theorem star {S : Subgroup G} (hSW : S ≤ Subgroup.centralizer (W : Set G)) (hS2 : IsPGroup 2 S)
    (hSmax : ∀ T : Subgroup G, T ≤ Subgroup.centralizer (W : Set G) → IsPGroup 2 T → S ≤ T →
      T = S) (z : G) :
    z ∈ W ↔ z ∈ S ∧ z ∈ Subgroup.centralizer (S : Set G) ∧ z ^ 2 = 1 := by
  have hWC : W ≤ Subgroup.centralizer (W : Set G) := fun w hw =>
    mem_centralizer_of_forall fun w' hw' => h.W_comm hw hw'
  have hWS : W ≤ S := by
    have hSN : S ≤ Subgroup.normalizer (W : Set G) := hSW.trans (centralizer_le_normalizer_W W)
    have hT := hSmax (S ⊔ W) (sup_le hSW hWC)
      (IsPGroup.to_sup_of_normal_right' hS2 h.isPGroup_W hSN) le_sup_left
    rw [← hT]
    exact le_sup_right
  constructor
  · intro hz
    exact ⟨hWS hz, mem_centralizer_of_forall fun s hs =>
      (Subgroup.mem_centralizer_iff.mp (hSW hs) z hz), h.W_elemAb.2 z hz⟩
  rintro ⟨hzS, hzC, hz2⟩
  by_contra hzW
  set D : Subgroup G := P ⊓ Subgroup.centralizer (W : Set G) with hD
  have hzCW : z ∈ Subgroup.centralizer (W : Set G) := hSW hzS
  have hzM : z ∈ M := h.mem_M_of_mem_centralizer hzCW
  have hDS : D ≤ S := by
    have hSN : S ≤ Subgroup.normalizer (D : Set G) := fun s hs =>
      h.mem_normalizer_D (h.mem_M_of_mem_centralizer (hSW hs))
        (centralizer_le_normalizer_W W (hSW hs))
    have hT := hSmax (S ⊔ D) (sup_le hSW inf_le_right)
      (IsPGroup.to_sup_of_normal_right' hS2 (h.isPGroup_P.to_le inf_le_left) hSN) le_sup_left
    rw [← hT]
    exact le_sup_right
  have hzD : ∀ d ∈ D, z * d = d * z := fun d hd =>
    (Subgroup.mem_centralizer_iff.mp hzC d (hDS hd)).symm
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left (by rw [← hz2, sq])
  have hxz : ∀ x ∈ conjSubgroup y V, ⁅x, z⁆ ∈ V := by
    intro x hx
    have hxP : x ∈ P := hy.le hx
    by_cases hx1 : x = 1
    · rw [hx1, commutatorElement_one_left]
      exact V.one_mem
    set c := ⁅x, z⁆ with hc
    have hcP : c ∈ P := by
      rw [hc, commutatorElement_def, mul_assoc, mul_assoc]
      refine P.mul_mem hxP ?_
      have := conj_mem_of_mem_normalizer (h.M_le_normalizer_P hzM) (P.inv_mem hxP)
      rwa [← mul_assoc]
    have hxD : x ∈ Subgroup.normalizer (D : Set G) :=
      h.mem_normalizer_D (h.P_le_M hxP) (h.P_le_normalizer_W hxP)
    have hcD : ∀ d ∈ D, c * d = d * c := by
      intro d hd
      have hd' : x⁻¹ * d * x ∈ D := by
        have := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hxD) hd
        rwa [inv_inv] at this
      have hzd : z⁻¹ * d = d * z⁻¹ := by
        calc z⁻¹ * d = z⁻¹ * (d * z) * z⁻¹ := by group
          _ = z⁻¹ * (z * d) * z⁻¹ := by rw [hzD d hd]
          _ = d * z⁻¹ := by group
      calc c * d = x * z * x⁻¹ * (z⁻¹ * d) := by rw [hc, commutatorElement_def]; group
        _ = x * z * x⁻¹ * (d * z⁻¹) := by rw [hzd]
        _ = x * (z * (x⁻¹ * d * x)) * x⁻¹ * z⁻¹ := by group
        _ = x * ((x⁻¹ * d * x) * z) * x⁻¹ * z⁻¹ := by rw [hzD _ hd']
        _ = d * c := by rw [hc, commutatorElement_def]; group
    have hcW : c ∈ W := by
      rw [← h.inf_centralizer_D hy]
      exact ⟨hcP, mem_centralizer_of_forall hcD⟩
    have hxW : x ∉ Subgroup.centralizer (W : Set G) := fun hxW => hx1 (hy.cent x hx fun a ha =>
      (Subgroup.mem_centralizer_iff.mp hxW a (h.V1_le_W ha)).symm)
    have hx2 : x * x = 1 := by
      have h2 := h.sq_eq_one _ (mem_conjSubgroup.mp hx)
      rw [sq] at h2
      calc x * x = y * ((y⁻¹ * x * y) * (y⁻¹ * x * y)) * y⁻¹ := by group
        _ = 1 := by rw [h2]; group
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx2
    have hzc : z * c = c * z := (Subgroup.mem_centralizer_iff.mp hzCW c hcW).symm
    have hc' : c = x * z * x * z := by rw [hc, commutatorElement_def, hxinv, hzinv]
    have hz2' : z * z = 1 := by rw [← hz2, sq]
    have key : x * z * x * z = z * x * z * x := by
      have e1 : z * (x * z * x * z) = (x * z * x * z) * z := by rw [← hc']; exact hzc
      calc x * z * x * z = z * z * (x * z * x * z) := by rw [hz2', one_mul]
        _ = z * (z * (x * z * x * z)) := by group
        _ = z * ((x * z * x * z) * z) := by rw [e1]
        _ = z * (x * z * x * (z * z)) := by group
        _ = z * x * z * x := by rw [hz2', mul_one]; group
    have hxc : x * c = c * x := by
      rw [hc']
      calc x * (x * z * x * z) = (x * x) * z * x * z := by group
        _ = z * x * z := by rw [hx2, one_mul]
        _ = z * x * z * (x * x) := by rw [hx2, mul_one]
        _ = (z * x * z * x) * x := by group
        _ = (x * z * x * z) * x := by rw [key]
    exact h.mem_of_commute hy hxP hxW hcW hxc
  have hzP : ∀ p ∈ P, ⁅z, p⁆ ∈ V := by
    intro p hp
    obtain ⟨b, hb, hbp⟩ := h.exists_mem_mul_mem_centralizer hy hp
    have hd := hzD _ ⟨P.mul_mem (P.inv_mem (hy.le hb)) hp, hbp⟩
    have hdz : z * (b⁻¹ * p) * z⁻¹ = b⁻¹ * p := by rw [hd, mul_inv_cancel_right]
    have e : ⁅z, p⁆ = ⁅b, z⁆⁻¹ := by
      calc ⁅z, p⁆ = z * b * z⁻¹ * (z * (b⁻¹ * p) * z⁻¹) * p⁻¹ := by
            rw [commutatorElement_def]; group
        _ = z * b * z⁻¹ * (b⁻¹ * p) * p⁻¹ := by rw [hdz]
        _ = ⁅b, z⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact V.inv_mem (hxz b hb)
  have hzQ : z ∈ Q := h.mem_Q_of_commutator_mem hzM
    (fun v hv => (Subgroup.mem_centralizer_iff.mp hzCW v (h.V_le_W hv)).symm) hzP
  have hzP' : z ∈ P := by
    rw [h.hP]
    exact ⟨hzQ, mem_centralizer_of_forall fun v hv =>
      (Subgroup.mem_centralizer_iff.mp hzCW v (h.V_le_W hv)).symm⟩
  apply hzW
  rw [← h.inf_centralizer_D hy]
  exact ⟨hzP', mem_centralizer_of_forall hzD⟩

omit hy in
theorem conj_mem_M_of_commute {s : G} (hs : ∀ a ∈ conjSubgroup g V, s * a = a * s) :
    g⁻¹ * s * g ∈ M := by
  rw [← h.normalizer_eq]
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  have hgv : g * v * g⁻¹ ∈ conjSubgroup g V := by
    rw [mem_conjSubgroup, show g⁻¹ * (g * v * g⁻¹) * g = v by group]
    exact hv
  have e : g⁻¹ * s * g * v * (g⁻¹ * s * g)⁻¹ = g⁻¹ * (s * (g * v * g⁻¹) * s⁻¹) * g := by group
  rw [e, hs _ hgv, mul_inv_cancel_right, show g⁻¹ * (g * v * g⁻¹) * g = v by group]
  exact hv

theorem exists_conj_eq_V1 :
    ∃ x ∈ Subgroup.normalizer (W : Set G), conjSubgroup x V = conjSubgroup g V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  let _ : Fintype (Subgroup G) := Fintype.ofFinite _
  obtain ⟨S, hSmem, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun T : Subgroup G =>
      T ≤ Subgroup.centralizer (W : Set G) ∧ IsPGroup 2 T)
    (fun T : Subgroup G => Nat.card T) ⟨⊥, by simp [IsPGroup.of_bot]⟩
  obtain ⟨hSW, hS2⟩ := (Finset.mem_filter.mp hSmem).2
  have hSmax : ∀ T : Subgroup G, T ≤ Subgroup.centralizer (W : Set G) → IsPGroup 2 T →
      S ≤ T → T = S := fun T hTW hT2 hST =>
    (Subgroup.eq_of_le_of_card_ge hST
      (hmax T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTW, hT2⟩))).symm
  have hstar := h.star hy hSW hS2 hSmax
  have hPg2 : IsPGroup 2 (conjSubgroup g P) := h.isPGroup_P.map _
  have hPgC : ∀ u ∈ conjSubgroup g P, ∀ a ∈ conjSubgroup g V, u * a = a * u := by
    intro u hu a ha
    have := h.central (mem_conjSubgroup.mp hu) (mem_conjSubgroup.mp ha)
    calc u * a = g * ((g⁻¹ * u * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * (g⁻¹ * u * g)) * g⁻¹ := by rw [this]
      _ = a * u := by group
  have hSV1 : ∀ s ∈ S, ∀ a ∈ conjSubgroup g V, s * a = a * s := fun s hs a ha =>
    (Subgroup.mem_centralizer_iff.mp (hSW hs) a (h.V1_le_W ha)).symm
  have hSN : S ≤ Subgroup.normalizer (conjSubgroup g P : Set G) := by
    intro s hs
    have hm := h.conj_mem_M_of_commute (hSV1 s hs)
    refine Subgroup.mem_normalizer_fintype fun u hu => ?_
    rw [SetLike.mem_coe, mem_conjSubgroup] at hu ⊢
    have := conj_mem_of_mem_normalizer (h.M_le_normalizer_P hm) hu
    rwa [show g⁻¹ * s * g * (g⁻¹ * u * g) * (g⁻¹ * s * g)⁻¹ = g⁻¹ * (s * u * s⁻¹) * g by
      group] at this
  set R := S ⊔ conjSubgroup g P with hR
  have hR2 : IsPGroup 2 R := IsPGroup.to_sup_of_normal_right' hS2 hPg2 hSN
  have hPgS : ¬ conjSubgroup g P ≤ S := by
    intro hle
    apply h.ne
    have hgV : ∀ v ∈ V, g⁻¹ * v * g ∈ V := by
      intro v hv
      rw [← h.M_inf_centralizer_P]
      refine ⟨h.conj_mem_M_of_commute fun a ha => h.W_comm (h.V_le_W hv) (h.V1_le_W ha),
        mem_centralizer_of_forall fun p hp => ?_⟩
      have hgp : g * p * g⁻¹ ∈ conjSubgroup g P := by
        rw [mem_conjSubgroup, show g⁻¹ * (g * p * g⁻¹) * g = p by group]
        exact hp
      have hvC := ((hstar v).mp (h.V_le_W hv)).2.1
      have := Subgroup.mem_centralizer_iff.mp hvC _ (hle hgp)
      calc g⁻¹ * v * g * p = g⁻¹ * (v * (g * p * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * p * g⁻¹) * v) * g := by rw [this]
        _ = p * (g⁻¹ * v * g) := by group
    have hle' : conjSubgroup g⁻¹ V ≤ V := fun x hx => by
      rw [mem_conjSubgroup, inv_inv] at hx
      have := hgV _ hx
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
    have heq : conjSubgroup g⁻¹ V = V :=
      Subgroup.eq_of_le_of_card_ge hle' (by rw [card_conjSubgroup])
    rw [conjSubgroup_eq_self_iff] at heq ⊢
    have := Subgroup.inv_mem _ heq
    rwa [inv_inv] at this
  have hSR : S < R := lt_of_le_of_ne le_sup_left fun heq =>
    hPgS (le_sup_right.trans heq.symm.le)
  have hRnil : Group.IsNilpotent R := hR2.isNilpotent
  have hS'lt : S.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hSR.ne
    refine le_antisymm le_sup_left fun r hr => ?_
    have : (⟨r, hr⟩ : R) ∈ S.subgroupOf R := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨r, hrN, hrS⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hS'lt)
  set s : G := (r : G) with hsdef
  have hsS : s ∉ S := fun h' => hrS (Subgroup.mem_subgroupOf.mpr h')
  have hsN : s ∈ Subgroup.normalizer (S : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    have htR : t ∈ R := le_sup_left (a := S) ht
    have h1 : (⟨t, htR⟩ : R) ∈ S.subgroupOf R := Subgroup.mem_subgroupOf.mpr ht
    have h2 := (Subgroup.mem_normalizer_iff.mp hrN ⟨t, htR⟩).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  have hs2 : IsPGroup 2 (Subgroup.zpowers s) :=
    hR2.to_le (Subgroup.zpowers_le.mpr r.2)
  have hsV1 : ∀ a ∈ conjSubgroup g V, s * a = a * s := by
    have hRC : R ≤ Subgroup.centralizer (conjSubgroup g V : Set G) :=
      sup_le (fun t ht => mem_centralizer_of_forall (hSV1 t ht))
        (fun u hu => mem_centralizer_of_forall (hPgC u hu))
    exact fun a ha => (Subgroup.mem_centralizer_iff.mp (hRC r.2) a ha).symm
  have hsW : s ∈ Subgroup.normalizer (W : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    obtain ⟨hwS, hwC, hw2⟩ := (hstar w).mp hw
    refine (hstar _).mpr ⟨conj_mem_of_mem_normalizer hsN hwS, ?_, ?_⟩
    · refine mem_centralizer_of_forall fun t ht => ?_
      have ht' : s⁻¹ * t * s ∈ S := by
        have := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hsN) ht
        rwa [inv_inv] at this
      have := Subgroup.mem_centralizer_iff.mp hwC _ ht'
      calc s * w * s⁻¹ * t = s * (w * (s⁻¹ * t * s)) * s⁻¹ := by group
        _ = s * ((s⁻¹ * t * s) * w) * s⁻¹ := by rw [this]
        _ = t * (s * w * s⁻¹) := by group
    · rw [show (s * w * s⁻¹) ^ 2 = s * w ^ 2 * s⁻¹ by rw [pow_two, pow_two]; group, hw2]
      group
  have hsCW : s ∉ Subgroup.centralizer (W : Set G) := by
    intro hsC
    have hT := hSmax (Subgroup.zpowers s ⊔ S) (sup_le (Subgroup.zpowers_le.mpr hsC) hSW)
      (IsPGroup.to_sup_of_normal_right' hs2 hS2 (Subgroup.zpowers_le.mpr hsN)) le_sup_right
    apply hsS
    rw [← hT]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers s)
  obtain ⟨n, hn⟩ := h.isPGroup_V.exists_card_eq
  have hCWs : ∀ w ∈ W, s * w = w * s → w ∈ conjSubgroup g V := by
    intro w hw hsw
    by_contra hwV1
    obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (h.conj_ne_bot y)
    have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
    have hbP : b ∈ P := hy.le hb
    have hWcard : Nat.card W = 2 ^ (2 * n) := by rw [h.card_W, hn, two_mul, pow_add]
    have hV1card : Nat.card (conjSubgroup g V) = 2 ^ n := by rw [card_conjSubgroup, hn]
    have hU : V ∈ classIn (conjSubgroup g V) W :=
      ⟨⟨g⁻¹, by rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]⟩, h.V_le_W⟩
    have hU' : conjSubgroup b (conjSubgroup g V) ∈ classIn (conjSubgroup g V) W :=
      ⟨⟨b, rfl⟩, by rw [← conjSubgroup_mul]; exact h.conj_V1_le_W hbP⟩
    have hU'V1 : conjSubgroup b (conjSubgroup g V) ≠ conjSubgroup g V := by
      intro heq
      have hbW := h.mem_centralizer_W hbP (conjSubgroup_eq_self_iff.mp heq)
      exact hb1' (hy.cent b hb fun a ha =>
        (Subgroup.mem_centralizer_iff.mp hbW a (h.V1_le_W ha)).symm)
    have hU'V : V ≠ conjSubgroup b (conjSubgroup g V) := by
      rw [← conjSubgroup_mul]
      exact (h.conj_V1_ne hbP).symm
    have hC : W ⊓ Subgroup.centralizer ({s} : Set G) ≠ conjSubgroup g V := by
      intro heq
      apply hwV1
      rw [← heq]
      exact ⟨hw, Subgroup.mem_centralizer_singleton_iff.mpr hsw.symm⟩
    have hall := commute_of_inf_centralizer_ne h.W_elemAb hWcard hV1card
      (isTI_conjSubgroup h.ti g) h.V1_le_W hU hU' (Ne.symm h.ne) hU'V1 hU'V
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hsV1 a ha).symm) hC
    exact hsCW (mem_centralizer_of_forall hall)
  have hsV : conjSubgroup s V ≠ V := by
    intro heq
    have hsNV : s ∈ Subgroup.normalizer (V : Set G) := conjSubgroup_eq_self_iff.mp heq
    obtain ⟨d, hdV, hd1, hdc⟩ := exists_mem_not_mem_commutator_mem (p := 2)
      (P := Subgroup.zpowers s ⊔ V) (B := ⊥) (N := V)
      (IsPGroup.to_sup_of_normal_right' hs2 h.isPGroup_V (Subgroup.zpowers_le.mpr hsNV))
      (bot_lt_iff_ne_bot.mpr h.V_ne_bot) le_sup_right
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      (sup_le (Subgroup.zpowers_le.mpr hsNV) Subgroup.le_normalizer)
    have h1 := hdc s (Subgroup.mem_sup_left (Subgroup.mem_zpowers s))
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    have hdV1 := hCWs d (h.V_le_W hdV) h1.symm
    have : d ∈ V ⊓ conjSubgroup g V := ⟨hdV, hdV1⟩
    rw [h.inf_V1] at this
    exact hd1 this
  have hsVW : conjSubgroup s V ∈ classIn V W := by
    refine ⟨⟨s, rfl⟩, fun x hx => ?_⟩
    have := conj_mem_of_mem_normalizer hsW (h.V_le_W (mem_conjSubgroup.mp hx))
    rwa [show s * (s⁻¹ * x * s) * s⁻¹ = x by group] at this
  obtain ⟨p, hp, hpeq⟩ := h.exists_conj_eq hy hsVW hsV ⟨⟨g, rfl⟩, h.V1_le_W⟩ h.ne
  refine ⟨p * s, Subgroup.mul_mem _ (h.P_le_normalizer_W hp) hsW, ?_⟩
  rw [conjSubgroup_mul, hpeq]

end Hyp218

end CFSG.RankThree.GF2n.Tim78
