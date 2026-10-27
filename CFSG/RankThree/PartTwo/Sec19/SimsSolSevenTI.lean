module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolSevenStruct
public import CFSG.CGT.Timmesfeld75.Defs
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolSeven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open CFSG.CGT.PushingUpLit.SolK (pCoreOf_le_self isPGroup_pCoreOf' le_pCoreOf_of_normalized
  pCoreOf_normalized)
open scoped commutatorElement

theorem inf_centralizer_le_of_fitting {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    (hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y) :
    Y ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 Y : Set G) ≤ CFSG.Open.pCoreOf 2 Y := by
  rintro y ⟨hyY, hyC⟩
  have h1 : (⟨y, hyY⟩ : Y) ∈ Subgroup.centralizer (generalizedFitting ↥Y : Set ↥Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hF] at hz
    have hz' : (z : G) ∈ CFSG.Open.pCoreOf 2 Y := ⟨z, hz, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC _ hz')
  have h2 := centralizer_generalizedFitting_le ↥Y h1
  rw [hF] at h2
  exact ⟨⟨y, hyY⟩, h2, rfl⟩

theorem mem_conjSubgroup_inv {G : Type*} [Group G] {g x : G} {T : Subgroup G} :
    x ∈ conjSubgroup g⁻¹ T ↔ g * x * g⁻¹ ∈ T := by
  rw [mem_conjSubgroup, inv_inv]

namespace Setting

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : Setting G M X)
include S

theorem M_normalizes_C {m : G} (hm : m ∈ M) {c : G} (hc : c ∈ Subgroup.centralizer (X : Set G)) :
    m * c * m⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro x hx
  have hx' : m⁻¹ * x * m ∈ X := by
    have := S.normal (M.inv_mem hm) hx
    simpa using this
  have h := hc _ hx'
  calc x * (m * c * m⁻¹) = m * ((m⁻¹ * x * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * x * m)) * m⁻¹ := by rw [h]
    _ = m * c * m⁻¹ * x := by group

theorem M_normalizes_R {m : G} (hm : m ∈ M) {r : G}
    (hr : r ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G))) :
    m * r * m⁻¹ ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G)) := by
  set C := Subgroup.centralizer (X : Set G)
  let N : Subgroup G := (CFSG.Open.pCoreOf 2 C).map (MulAut.conj m).toMonoidHom
  have hNC : N ≤ C := by
    rintro _ ⟨z, hz, rfl⟩
    exact S.M_normalizes_C hm (pCoreOf_le_self C hz)
  have hN2 : IsPGroup 2 N := (isPGroup_pCoreOf' C).map (MulAut.conj m).toMonoidHom
  have hNnorm : ∀ c ∈ C, ∀ z ∈ N, c * z * c⁻¹ ∈ N := by
    rintro c hc _ ⟨z, hz, rfl⟩
    have h1 : m⁻¹ * c * m ∈ C := by
      have := S.M_normalizes_C (M.inv_mem hm) hc
      simpa using this
    refine ⟨(m⁻¹ * c * m) * z * (m⁻¹ * c * m)⁻¹, pCoreOf_normalized C h1 hz, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  exact le_pCoreOf_of_normalized hNC hNnorm hN2 ⟨r, hr, rfl⟩

theorem R_le_Q :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G)) ≤ CFSG.Open.pCoreOf 2 M :=
  le_pCoreOf_of_normalized ((pCoreOf_le_self _).trans S.centralizer_le)
    (fun _ hm _ hr => S.M_normalizes_R hm hr) (isPGroup_pCoreOf' _)

theorem Q_inf_C_le_R :
    CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (X : Set G) ≤
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G)) := by
  refine le_pCoreOf_of_normalized inf_le_right (fun c hc z hz => ?_)
    ((isPGroup_pCoreOf' M).to_le inf_le_left)
  exact ⟨pCoreOf_normalized M (S.centralizer_le hc) hz.1,
    (Subgroup.centralizer (X : Set G)).mul_mem
      ((Subgroup.centralizer (X : Set G)).mul_mem hc hz.2)
      ((Subgroup.centralizer (X : Set G)).inv_mem hc)⟩

theorem exists_eq_mul_R {q : G} (hq : q ∈ CFSG.Open.pCoreOf 2 M) :
    ∃ v ∈ blockU X, ∃ r ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G)), q = v * r := by
  obtain ⟨v, hv, r, hr, rfl⟩ := S.exists_eq_mul_of_mem_Q hq
  exact ⟨v, hv, r, S.Q_inf_C_le_R hr, rfl⟩

theorem W_comm_C {w c : G} (hw : w ∈ blockU X) (hc : c ∈ Subgroup.centralizer (X : Set G)) :
    w * c = c * w :=
  Subgroup.mem_centralizer_iff.mp hc w (S.W_le_X hw)

variable (hRab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G)),
    ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G)), a * b = b * a)
  (hR2 : ∀ c ∈ Subgroup.centralizer (X : Set G), ∀ k : ℕ, c ^ (2 ^ k) = 1 →
    c ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G)))

include hRab in
theorem Q_comm {a b : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) (hb : b ∈ CFSG.Open.pCoreOf 2 M) :
    a * b = b * a := by
  obtain ⟨v, hv, r, hr, rfl⟩ := S.exists_eq_mul_R ha
  obtain ⟨v', hv', r', hr', rfl⟩ := S.exists_eq_mul_R hb
  have hrC : ∀ {z}, z ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G)) →
      z ∈ Subgroup.centralizer (X : Set G) := fun hz => pCoreOf_le_self _ hz
  have h1 := S.W_comm hv hv'
  have h2 := hRab r hr r' hr'
  have h3 := S.W_comm_C hv (hrC hr')
  have h4 := S.W_comm_C hv' (hrC hr)
  calc v * r * (v' * r') = v * (r * v') * r' := by group
    _ = v * (v' * r) * r' := by rw [h4]
    _ = (v * v') * (r * r') := by group
    _ = (v' * v) * (r' * r) := by rw [h1, h2]
    _ = v' * (v * r') * r := by group
    _ = v' * (r' * v) * r := by rw [h3]
    _ = v' * r' * (v * r) := by group

include hR2 in
theorem mem_Q_of_pi_eq_one {p : ↥M} (hp : S.pi p = 1) {k : ℕ} (hk : (p : G) ^ (2 ^ k) = 1) :
    (p : G) ∈ CFSG.Open.pCoreOf 2 M := by
  obtain ⟨v, hv, hvc⟩ := S.exists_of_pi_eq_one hp
  have hvc' : v * (v⁻¹ * (p : G)) = (v⁻¹ * (p : G)) * v := S.W_comm_C hv hvc
  have hcomm : Commute v⁻¹ (p : G) := by
    show v⁻¹ * (p : G) = (p : G) * v⁻¹
    calc v⁻¹ * (p : G) = (v⁻¹ * (p : G)) * v * v⁻¹ := by group
      _ = v * (v⁻¹ * (p : G)) * v⁻¹ := by rw [hvc']
      _ = (p : G) * v⁻¹ := by group
  have hpow : (v⁻¹ * (p : G)) ^ (2 ^ k) = v⁻¹ ^ (2 ^ k) := by
    rw [hcomm.mul_pow, hk, mul_one]
  have hc1 : (v⁻¹ * (p : G)) ^ (2 ^ k) = 1 := by
    rw [hpow]
    refine S.eq_one_of_mem_W_of_mem_C ((blockU X).pow_mem ((blockU X).inv_mem hv) _) ?_
    rw [← hpow]
    exact (Subgroup.centralizer (X : Set G)).pow_mem hvc _
  have hcR := hR2 _ hvc k hc1
  have e : (p : G) = v * (v⁻¹ * (p : G)) := by group
  rw [e]
  exact (CFSG.Open.pCoreOf 2 M).mul_mem (S.W_le_Q hv) (S.R_le_Q hcR)

theorem Q_ne_bot : CFSG.Open.pCoreOf 2 M ≠ ⊥ := by
  intro h
  have hW : blockU X ≤ ⊥ := h ▸ S.W_le_Q
  have h1 := Subgroup.card_le_of_le hW
  rw [S.card_blockU, Subgroup.card_bot] at h1
  omega

theorem eq_of_le_of_isPLocal {H : Subgroup G} (hMH : M ≤ H) (hH : CFSG.IsPLocal 2 H) : H = M := by
  by_contra hne
  exact S.maxLocal.2 H (lt_of_le_of_ne hMH (Ne.symm hne)) hH

theorem normalizer_eq_of_normalized {P : Subgroup G} (hP2 : IsPGroup 2 P) (hP1 : P ≠ ⊥)
    (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P) : Subgroup.normalizer (P : Set G) = M := by
  refine S.eq_of_le_of_isPLocal (fun m hm => ?_) ⟨P, hP1, hP2, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · exact hMP m hm p
  · intro h
    have := hMP m⁻¹ (M.inv_mem hm) _ h
    simpa [mul_assoc] using this

theorem normalizer_Q : Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) = M :=
  S.normalizer_eq_of_normalized (isPGroup_pCoreOf' M) S.Q_ne_bot fun _ hm _ hp =>
    pCoreOf_normalized M hm hp

include hR2 in
theorem le_Q_of_normalized {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hPM : P ≤ M) (hPx : ∀ p ∈ P, p * x = x * p)
    (hPn : ∀ m ∈ M, m * x = x * m → ∀ p ∈ P, m * p * m⁻¹ ∈ P) :
    P ≤ CFSG.Open.pCoreOf 2 M := by
  obtain ⟨θ⟩ := S.nonempty_theta
  obtain ⟨v, hv, r, hr, rfl⟩ := S.exists_eq_mul_R hx
  have hrC : r ∈ Subgroup.centralizer (X : Set G) := pCoreOf_le_self _ hr
  let A : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) := (P.subgroupOf M).map S.pi
  have hA2 : IsPGroup 2 A := by
    have : IsPGroup 2 (P.subgroupOf M) := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
    exact this.map S.pi
  have hnorm : ∀ a : ↥X, (a : G) * v * (a : G)⁻¹ = v →
      ((a : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ Subgroup.normalizer (A : Set _) := by
    have key : ∀ a : ↥X, (a : G) * v * (a : G)⁻¹ = v → ∀ n ∈ A,
        ((a : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) * n * ((a : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X)⁻¹ ∈ A := by
      rintro a ha _ ⟨p, hp, rfl⟩
      have hax : (a : G) * (v * r) = (v * r) * (a : G) := by
        have h1 : (a : G) * v = v * (a : G) := by
          calc (a : G) * v = (a : G) * v * (a : G)⁻¹ * (a : G) := by group
            _ = v * (a : G) := by rw [ha]
        have h2 : (a : G) * r = r * (a : G) := (Subgroup.mem_centralizer_iff.mp hrC _ a.2)
        calc (a : G) * (v * r) = ((a : G) * v) * r := by group
          _ = v * ((a : G) * r) := by rw [h1]; group
          _ = (v * r) * (a : G) := by rw [h2]; group
      have hpa : (a : G) * (p : G) * (a : G)⁻¹ ∈ P := hPn _ (S.le a.2) hax _ hp
      refine ⟨⟨(a : G) * (p : G) * (a : G)⁻¹, M.mul_mem (M.mul_mem (S.le a.2) p.2)
        (M.inv_mem (S.le a.2))⟩, hpa, ?_⟩
      have e : (⟨(a : G) * (p : G) * (a : G)⁻¹, M.mul_mem (M.mul_mem (S.le a.2) p.2)
          (M.inv_mem (S.le a.2))⟩ : ↥M) = ⟨(a : G), S.le a.2⟩ * p * ⟨(a : G), S.le a.2⟩⁻¹ :=
        Subtype.ext rfl
      rw [e, map_mul, map_mul, map_inv, S.pi_of_mem_X a.2]
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨key a ha n, fun h => ?_⟩
    have ha' : ((a⁻¹ : ↥X) : G) * v * ((a⁻¹ : ↥X) : G)⁻¹ = v := by
      have e : ((a⁻¹ : ↥X) : G) = (a : G)⁻¹ := rfl
      rw [e, inv_inv]
      calc (a : G)⁻¹ * v * (a : G) = (a : G)⁻¹ * ((a : G) * v * (a : G)⁻¹) * (a : G) := by
            rw [ha]
        _ = v := by group
    have := key a⁻¹ ha' _ h
    simpa [mul_assoc] using this
  have hA : A = ⊥ := by
    by_cases hv1 : v = 1
    ·
      have hW1 : ∃ w ∈ blockU X, w ≠ 1 := by
        by_contra hcon
        have hle : blockU X ≤ ⊥ := fun w hw => by
          rw [Subgroup.mem_bot]
          by_contra h
          exact hcon ⟨w, hw, h⟩
        have h1 := Subgroup.card_le_of_le hle
        rw [S.card_blockU, Subgroup.card_bot] at h1
        omega
      obtain ⟨w, hw, hw1⟩ := hW1
      refine eq_bot_of_stab_le_normalizer θ S.card_blockU S.phi (v := ⟨w, hw⟩)
        (fun h => hw1 (congrArg Subtype.val h)) hA2 (fun γ _ => ?_)
      induction γ using QuotientGroup.induction_on with
      | H a =>
        exact hnorm a (by rw [hv1]; group)
    · refine eq_bot_of_stab_le_normalizer θ S.card_blockU S.phi (v := ⟨v, hv⟩)
        (fun h => hv1 (congrArg Subtype.val h)) hA2 (fun γ hγ => ?_)
      induction γ using QuotientGroup.induction_on with
      | H a =>
        apply hnorm a
        have := congrArg Subtype.val hγ
        rwa [S.phi_mk] at this
  intro p hp
  have hpA : S.pi ⟨p, hPM hp⟩ ∈ A := ⟨⟨p, hPM hp⟩, hp, rfl⟩
  rw [hA, Subgroup.mem_bot] at hpA
  obtain ⟨k, hk⟩ := hP2 ⟨p, hp⟩
  have hk' : p ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact S.mem_Q_of_pi_eq_one hR2 hpA hk'

include hRab in
theorem Q_le_centralizer {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) :
    CFSG.Open.pCoreOf 2 M ≤ Subgroup.centralizer ({x} : Set G) := fun q hq =>
  Subgroup.mem_centralizer_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff.mp hy]
    exact S.Q_comm hRab hx hq

include hRab hR2 in
theorem pCoreOf_centralizer_eq {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) (hx1 : x ≠ 1) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) = CFSG.Open.pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({x} : Set G) with hH
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  set Qx := CFSG.Open.pCoreOf 2 H with hQx
  have hQH : Q ≤ H := S.Q_le_centralizer hRab hx
  have hxH : ∀ {h : G}, h ∈ H ↔ h * x = x * h := fun {h} => by
    rw [hH, Subgroup.mem_centralizer_iff]
    constructor
    · intro hh; exact (hh x (Set.mem_singleton x)).symm
    · intro hh y hy; rw [Set.mem_singleton_iff.mp hy]; exact hh.symm
  have hQnorm : Q ≤ Subgroup.normalizer (Qx : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => pCoreOf_normalized H (hQH hq) hn, fun hn => ?_⟩
    have := pCoreOf_normalized H (H.inv_mem (hQH hq)) hn
    simpa [mul_assoc] using this
  have hQxM : Qx ⊓ M ≤ Q := by
    refine S.le_Q_of_normalized hR2 hx ((isPGroup_pCoreOf' H).to_le inf_le_left) inf_le_right
      (fun p hp => hxH.mp (pCoreOf_le_self H hp.1)) (fun m hm hmx p hp => ?_)
    exact ⟨pCoreOf_normalized H (hxH.mpr hmx) hp.1, M.mul_mem (M.mul_mem hm hp.2) (M.inv_mem hm)⟩
  set P := Qx ⊔ Q with hP
  have hP2 : IsPGroup 2 P := IsPGroup.to_sup_of_normal_left' (isPGroup_pCoreOf' H)
    (isPGroup_pCoreOf' M) hQnorm
  have hQP : Q ≤ P := le_sup_right
  have hself : ∀ g ∈ P, g ∈ Subgroup.normalizer (Q : Set G) → g ∈ Q := by
    intro g hg hgN
    rw [S.normalizer_Q] at hgN
    have hg' : g ∈ ((Qx ⊔ Q : Subgroup G) : Set G) := hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Qx Q hQnorm] at hg'
    obtain ⟨k, hk, q, hq, rfl⟩ := hg'
    have hkM : k ∈ M := by
      have := M.mul_mem hgN (M.inv_mem (pCoreOf_le_self M hq))
      simpa using this
    exact Q.mul_mem (hQxM ⟨hk, hkM⟩) hq
  have hQtop : Q.subgroupOf P = ⊤ := by
    haveI : Group.IsNilpotent ↥P := hP2.isNilpotent
    refine (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (normalizerCondition_of_isNilpotent (G := ↥P))) _ ?_
    refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_subgroupOf]
    refine hself g g.2 ?_
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have h1 := (Subgroup.mem_normalizer_iff.mp hg ⟨q, hQP hq⟩).mp
        (Subgroup.mem_subgroupOf.mpr hq)
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    · intro hq
      have hqP : q ∈ P := by
        have := P.mul_mem (P.mul_mem (P.inv_mem g.2) (hQP hq)) g.2
        simpa [mul_assoc] using this
      have h1 := (Subgroup.mem_normalizer_iff.mp hg ⟨q, hqP⟩).mpr
        (Subgroup.mem_subgroupOf.mpr (by simpa using hq))
      rw [Subgroup.mem_subgroupOf] at h1
      exact h1
  have hQxQ : Qx ≤ Q := by
    intro k hk
    have hkP : k ∈ P := le_sup_left (a := Qx) hk
    have : (⟨k, hkP⟩ : ↥P) ∈ Q.subgroupOf P := hQtop ▸ Subgroup.mem_top _
    exact this
  have hQQx : Q ≤ Qx := fun q hq =>
    inf_centralizer_le_of_fitting (S.cent x hx hx1) (Subgroup.mem_inf.mpr ⟨hQH hq,
      Subgroup.mem_centralizer_iff.mpr fun k hk => S.Q_comm hRab (hQxQ hk) hq⟩)
  exact le_antisymm hQxQ hQQx

include hRab hR2 in
theorem Q_isTI (g : G) :
    CFSG.Open.pCoreOf 2 M ⊓ conjSubgroup g (CFSG.Open.pCoreOf 2 M) = ⊥ ∨
      CFSG.Open.pCoreOf 2 M ⊓ conjSubgroup g (CFSG.Open.pCoreOf 2 M) = CFSG.Open.pCoreOf 2 M := by
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  by_cases h : Q ⊓ conjSubgroup g Q = ⊥
  · exact Or.inl h
  right
  obtain ⟨⟨x, hxQ, hxg⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
  have hq : g⁻¹ * x * g ∈ Q := mem_conjSubgroup.mp hxg
  have hq1 : g⁻¹ * x * g ≠ 1 := fun h' => hx1' (by
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group)
  have hQx := S.pCoreOf_centralizer_eq hRab hR2 hxQ hx1'
  have hQq := S.pCoreOf_centralizer_eq hRab hR2 hq hq1
  have hle : conjSubgroup g Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) := by
    refine le_pCoreOf_of_normalized (fun y hy => ?_) (fun c hc y hy => ?_)
      ((isPGroup_pCoreOf' M).map _)
    ·
      have hy' : g⁻¹ * y * g ∈ Q := mem_conjSubgroup.mp hy
      have hc := S.Q_comm hRab hq hy'
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      rw [Set.mem_singleton_iff.mp hz]
      calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
        _ = y * x := by group
    ·
      have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({g⁻¹ * x * g} : Set G) := by
        rw [Subgroup.mem_centralizer_iff] at hc ⊢
        intro z hz
        rw [Set.mem_singleton_iff.mp hz]
        have := hc x (Set.mem_singleton x)
        calc g⁻¹ * x * g * (g⁻¹ * c * g) = g⁻¹ * (x * c) * g := by group
          _ = g⁻¹ * (c * x) * g := by rw [this]
          _ = g⁻¹ * c * g * (g⁻¹ * x * g) := by group
      have hy' : g⁻¹ * y * g ∈ Q := mem_conjSubgroup.mp hy
      have h1 := pCoreOf_normalized _ hc' (by rw [hQq]; exact hy')
      rw [hQq] at h1
      refine mem_conjSubgroup.mpr ?_
      have e : g⁻¹ * (c * y * c⁻¹) * g = (g⁻¹ * c * g) * (g⁻¹ * y * g) * (g⁻¹ * c * g)⁻¹ := by
        group
      rw [e]
      exact h1
  rw [hQx] at hle
  have hcard : Nat.card Q ≤ Nat.card (conjSubgroup g Q) := by
    rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [Subgroup.eq_of_le_of_card_ge hle hcard, inf_idem]

@[expose] def omegaQ : Subgroup G where
  carrier := {q | q ∈ CFSG.Open.pCoreOf 2 M ∧ q ^ 2 = 1}
  one_mem' := ⟨(CFSG.Open.pCoreOf 2 M).one_mem, one_pow 2⟩
  mul_mem' := fun {a b} ha hb => ⟨(CFSG.Open.pCoreOf 2 M).mul_mem ha.1 hb.1, by
    have hc : Commute a b := S.Q_comm hRab ha.1 hb.1
    rw [hc.mul_pow, ha.2, hb.2, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨(CFSG.Open.pCoreOf 2 M).inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

include hRab in
theorem mem_omegaQ {q : G} :
    q ∈ S.omegaQ hRab ↔ q ∈ CFSG.Open.pCoreOf 2 M ∧ q ^ 2 = 1 := Iff.rfl

include hRab in
theorem omegaQ_le_Q : S.omegaQ hRab ≤ CFSG.Open.pCoreOf 2 M := fun _ h =>
  ((S.mem_omegaQ hRab).mp h).1

include hRab in
theorem W_le_omegaQ : blockU X ≤ S.omegaQ hRab := fun _ hw =>
  (S.mem_omegaQ hRab).mpr ⟨S.W_le_Q hw, S.W_sq hw⟩

include hRab in
theorem isElemAbelian_omegaQ : CFSG.Open.IsElemAbelian 2 (S.omegaQ hRab) :=
  ⟨⟨⟨fun a b => Subtype.ext (S.Q_comm hRab ((S.mem_omegaQ hRab).mp a.2).1
    ((S.mem_omegaQ hRab).mp b.2).1)⟩⟩, fun _ h => ((S.mem_omegaQ hRab).mp h).2⟩

include hRab in
theorem sixteen_le_card_omegaQ : 16 ≤ Nat.card (S.omegaQ hRab) := by
  rw [← S.card_blockU]
  exact Subgroup.card_le_of_le (S.W_le_omegaQ hRab)

include hRab in
theorem omegaQ_ne_bot : S.omegaQ hRab ≠ ⊥ := by
  intro h
  have h1 := Subgroup.card_le_of_le ((S.W_le_omegaQ hRab).trans h.le)
  rw [S.card_blockU, Subgroup.card_bot] at h1
  omega

include hRab in
theorem isPGroup_omegaQ : IsPGroup 2 (S.omegaQ hRab) :=
  (isPGroup_pCoreOf' M).to_le (S.omegaQ_le_Q hRab)

include hRab in
theorem conj_mem_omegaQ {b g : G} (hb : b ∈ S.omegaQ hRab)
    (hg : g * b * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M) : g * b * g⁻¹ ∈ S.omegaQ hRab :=
  (S.mem_omegaQ hRab).mpr ⟨hg, by
    rw [conj_pow, ((S.mem_omegaQ hRab).mp hb).2, mul_one, mul_inv_cancel]⟩

include hRab in
theorem normalizer_omegaQ : Subgroup.normalizer (S.omegaQ hRab : Set G) = M :=
  S.normalizer_eq_of_normalized (S.isPGroup_omegaQ hRab) (S.omegaQ_ne_bot hRab)
    fun _ hm _ hp => S.conj_mem_omegaQ hRab hp
      (pCoreOf_normalized M hm ((S.mem_omegaQ hRab).mp hp).1)

include hRab hR2 in
theorem omegaQ_isTI (g : G) :
    S.omegaQ hRab ⊓ conjSubgroup g⁻¹ (S.omegaQ hRab) = ⊥ ∨
      S.omegaQ hRab ⊓ conjSubgroup g⁻¹ (S.omegaQ hRab) = S.omegaQ hRab := by
  rcases S.Q_isTI hRab hR2 g⁻¹ with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    have hyQ : y ∈ CFSG.Open.pCoreOf 2 M ⊓ conjSubgroup g⁻¹ (CFSG.Open.pCoreOf 2 M) :=
      Subgroup.mem_inf.mpr ⟨((S.mem_omegaQ hRab).mp hy1).1,
        mem_conjSubgroup_inv.mpr ((S.mem_omegaQ hRab).mp (mem_conjSubgroup_inv.mp hy2)).1⟩
    rw [h] at hyQ
    exact hyQ
  · right
    refine inf_eq_left.mpr fun b hb => mem_conjSubgroup_inv.mpr (S.conj_mem_omegaQ hRab hb ?_)
    exact mem_conjSubgroup_inv.mp ((inf_eq_left.mp h) ((S.mem_omegaQ hRab).mp hb).1)

include hRab hR2 in
theorem omegaQ_weaklyClosed (g : G)
    (hg : conjSubgroup g⁻¹ (S.omegaQ hRab) ≤ Subgroup.normalizer (S.omegaQ hRab : Set G)) :
    conjSubgroup g⁻¹ (S.omegaQ hRab) = S.omegaQ hRab := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := S.omegaQ hRab with hB
  set B' := conjSubgroup g⁻¹ B with hB'
  have hcard : Nat.card B' = Nat.card B := by
    rw [hB', conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  rw [S.normalizer_omegaQ hRab] at hg
  by_cases hBQ : B' ⊓ CFSG.Open.pCoreOf 2 M = ⊥
  · exfalso
    let f : ↥(B'.subgroupOf M) →* ↥X ⧸ CFSG.pCore 2 ↥X := S.pi.comp (B'.subgroupOf M).subtype
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro p hp
      have hpB' : ((p : ↥M) : G) ∈ B' := Subgroup.mem_subgroupOf.mp p.2
      have hsq : ((p : ↥M) : G) ^ (2 ^ 1) = 1 := by
        have h1 := ((S.mem_omegaQ hRab).mp (mem_conjSubgroup_inv.mp hpB')).2
        rw [conj_pow] at h1
        calc ((p : ↥M) : G) ^ (2 ^ 1) = g⁻¹ * (g * ((p : ↥M) : G) ^ 2 * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      have hpQ := S.mem_Q_of_pi_eq_one hR2 (p := (p : ↥M)) hp hsq
      have hmem : ((p : ↥M) : G) ∈ B' ⊓ CFSG.Open.pCoreOf 2 M := Subgroup.mem_inf.mpr ⟨hpB', hpQ⟩
      rw [hBQ, Subgroup.mem_bot] at hmem
      exact Subtype.ext (Subtype.ext hmem)
    have h1 : Nat.card ↥(B'.subgroupOf M) ∣ 2520 := by
      rw [← SimsTheoremC.card_quot_of_isA7FourType S.type,
        Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hg).toEquiv, hcard] at h1
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (S.isPGroup_omegaQ hRab)
    have h16 := S.sixteen_le_card_omegaQ hRab
    rw [← hB, hn] at h16
    rw [hn] at h1
    have hn4 : 4 ≤ n := by
      by_contra h
      have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 := (pow_dvd_pow 2 hn4).trans h1
    norm_num at h2
  · obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBQ
    obtain ⟨hxB', hxQ⟩ := Subgroup.mem_inf.mp hx
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxsq : x ^ 2 = 1 := by
      have h1 := ((S.mem_omegaQ hRab).mp (mem_conjSubgroup_inv.mp hxB')).2
      rw [conj_pow] at h1
      calc x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have hxB : x ∈ B := (S.mem_omegaQ hRab).mpr ⟨hxQ, hxsq⟩
    rcases S.omegaQ_isTI hRab hR2 g with h | h
    · exfalso
      have hmem : x ∈ B ⊓ B' := Subgroup.mem_inf.mpr ⟨hxB, hxB'⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hx1' hmem
    · exact (Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp h) hcard.le).symm

include hRab hR2 in
theorem exists_ti : ∃ B : Subgroup G, CFSG.Open.IsElemAbelian 2 B ∧ 4 ≤ Nat.card B ∧
    (∀ g : G, B ⊓ conjSubgroup g⁻¹ B = ⊥ ∨ B ⊓ conjSubgroup g⁻¹ B = B) ∧
    (∀ g : G, conjSubgroup g⁻¹ B ≤ Subgroup.normalizer (B : Set G) → conjSubgroup g⁻¹ B = B) :=
  ⟨S.omegaQ hRab, S.isElemAbelian_omegaQ hRab,
    le_trans (by norm_num) (S.sixteen_le_card_omegaQ hRab), S.omegaQ_isTI hRab hR2,
    S.omegaQ_weaklyClosed hRab hR2⟩

end Setting

end CFSG.RankThree.PartTwo.Sec19.SolSeven
