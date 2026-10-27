module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenTight
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenTheta
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenW
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenPi
import CFSG.CGT.PushingUpLit.SolKNA.PairLemma
public import CFSG.CGT.PushingUpLit.SolK.RSmallI

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.CGT.PushingUpLit.SolK Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup IsTI)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

section Setting

variable (S : Setting G M X n)
include S

theorem R_normalized {m r : G} (hm : m ∈ M) (hr : r ∈ Rc X) : m * r * m⁻¹ ∈ Rc X :=
  pCoreOf_normalized_of_normal (fun _ hm' _ hc => Theta.conj_mem_centralizer_of_mem S hm' hc) hm hr

omit S in
theorem card_conj (g : G) : Nat.card ↥(conjSubgroup g (Rc X)) = Nat.card ↥(Rc X) :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem inf_conj_eq_bot {g : G} (hne : conjSubgroup g (Rc X) ≠ Rc X) :
    Rc X ⊓ conjSubgroup g (Rc X) = ⊥ := by
  rcases S.isTI_R g with h | h
  · exact h
  · exfalso
    apply hne
    have hle : Rc X ≤ conjSubgroup g (Rc X) := h.symm.le.trans inf_le_right
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conj])).symm

theorem comm_R_conj (hR : Rc X ≠ ⊥) {g : G} (hTM : conjSubgroup g (Rc X) ≤ M)
    (hne : conjSubgroup g (Rc X) ≠ Rc X) {r τ : G} (hr : r ∈ Rc X)
    (hτ : τ ∈ conjSubgroup g (Rc X)) : r * τ = τ * r := by
  have hB1 : conjSubgroup g (Rc X) ≠ ⊥ := by
    intro h
    apply hR
    have := card_conj (G := G) (X := X) g
    rw [h, Subgroup.card_bot] at this
    exact (Subgroup.card_eq_one.1 this.symm)
  have hBN : conjSubgroup g (Rc X) ≤ Subgroup.normalizer ((Rc X : Subgroup G) : Set G) := by
    rw [S.normalizer_R hR]
    exact hTM
  exact CFSG.CGT.PushingUpLit.SolKNA.commute_of_le_normalizer (isPGroup_pCoreOf' _) S.isTI_R
    hne hB1 hBN r hr τ hτ

theorem conj_mem_of_comm {g t c : G} (ht : t ∈ conjSubgroup g (Rc X)) (ht1 : t ≠ 1)
    (hc : c * t = t * c) : g⁻¹ * c * g ∈ M := by
  have hr : g⁻¹ * t * g ∈ Rc X := mem_conjSubgroup.1 ht
  have hr1 : g⁻¹ * t * g ≠ 1 := by
    intro h
    apply ht1
    have : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    rw [this, h]
    group
  refine S.centralizer_le_of_mem_R hr hr1 (Subgroup.mem_centralizer_singleton_iff.2 ?_)
  calc g⁻¹ * c * g * (g⁻¹ * t * g) = g⁻¹ * (c * t) * g := by group
    _ = g⁻¹ * (t * c) * g := by rw [hc]
    _ = g⁻¹ * t * g * (g⁻¹ * c * g) := by group

theorem conj_normalized {g c τ : G} (hc : g⁻¹ * c * g ∈ M) (hτ : τ ∈ conjSubgroup g (Rc X)) :
    c * τ * c⁻¹ ∈ conjSubgroup g (Rc X) := by
  rw [mem_conjSubgroup] at hτ ⊢
  have h := R_normalized S hc hτ
  have e : g⁻¹ * (c * τ * c⁻¹) * g = g⁻¹ * c * g * (g⁻¹ * τ * g) * (g⁻¹ * c * g)⁻¹ := by group
  rw [e]
  exact h

omit S in
theorem two_pow_of_mem_conj {g τ : G} (hτ : τ ∈ conjSubgroup g (Rc X)) :
    ∃ j : ℕ, τ ^ (2 ^ j) = 1 := by
  have h0 : g⁻¹ * τ * g ∈ Rc X := mem_conjSubgroup.1 hτ
  obtain ⟨j, hj⟩ := isPGroup_pCoreOf' (Subgroup.centralizer (X : Set G)) ⟨_, h0⟩
  refine ⟨j, ?_⟩
  have h1 : (g⁻¹ * τ * g) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  rw [inv_conj_pow] at h1
  have : τ ^ (2 ^ j) = g * (g⁻¹ * τ ^ (2 ^ j) * g) * g⁻¹ := by group
  rw [this, h1]
  group

theorem mem_of_le_conj {g : G} (h : ∀ x ∈ X, g⁻¹ * x * g ∈ M) : g ∈ M := by
  have h1 : g⁻¹ ∈ M := S.mem_of_conj_le fun x hx => by simpa using h x hx
  simpa using M.inv_mem h1

end Setting

section Cfg

variable (C : Cfg G M X n)

theorem Q_le_K : CFSG.Open.pCoreOf 2 M ≤ C.K := fun q hq =>
  C.mem_K.2 ⟨pCoreOf_le_self M hq, C.theta_Q C.S.five_le_degree hq⟩

theorem K_comm_W {k w : G} (hk : k ∈ C.K) (hw : w ∈ blockU X) : k * w = w * k := by
  have hkW : ∀ k' ∈ C.K, ∀ v ∈ blockU X, ⁅k', v⁆ ∈ blockZ X := by
    intro k' hk' v hv
    have hkv : k' * v * k'⁻¹ ∈ blockU X := C.S.W_normalized (C.K_le hk') hv
    have hβ := C.β_conj_K ⟨k', hk'⟩ ⟨v, hv⟩ ⟨k' * v * k'⁻¹, hkv⟩ rfl
    have hmem : (⟨k' * v * k'⁻¹, hkv⟩ : ↥(blockU X)) * (⟨v, hv⟩ : ↥(blockU X))⁻¹ ∈
        C.β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, Multiplicative.toAdd.injective hβ,
        mul_inv_cancel]
    rw [C.β_ker, Subgroup.mem_subgroupOf] at hmem
    simpa [commutatorElement_def] using hmem
  set Z : Subgroup G := Subgroup.zpowers k with hZ
  have hW_comm : ∀ a ∈ blockU X, ∀ b ∈ blockU X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (C.S.elemU.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h1 : ⁅⁅X, Z⁆, blockU X⁆ = ⊥ := by
    have hle : ⁅X, Z⁆ ≤ blockU X := by
      rw [Subgroup.commutator_le]
      intro x hx z hz
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      have := C.comm_mem_W ⟨k ^ i, C.K.zpow_mem hk i⟩ hx
      rw [← commutator_inv']
      exact (blockU X).inv_mem this
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hW_comm v hv y (hle hy)
  have h2 : ⁅⁅Z, blockU X⁆, X⁆ = ⊥ := by
    have hle : ⁅Z, blockU X⁆ ≤ blockZ X := by
      rw [Subgroup.commutator_le]
      intro z hz v hv
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact hkW _ (C.K.zpow_mem hk i) v hv
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    exact (Subgroup.mem_inf.1 (hle hy)).2
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [C.commutator_W_eq, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
  exact (Subgroup.mem_centralizer_iff.1 (h3 hw) k (Subgroup.mem_zpowers k))

include C in
theorem W_comm_Q {w q : G} (hw : w ∈ blockU X) (hq : q ∈ CFSG.Open.pCoreOf 2 M) :
    w * q = q * w :=
  (K_comm_W C (Q_le_K C hq) hw).symm

theorem exists_lift_pow_three {c : Perm (Fin n)} (hc : c.IsThreeCycle) :
    ∃ x : ↥X, (x : G) ^ 3 = 1 ∧ (C.α x : Perm (Fin n)) = c := by
  obtain ⟨x₀, hx₀⟩ := C.α_surj ⟨c, hc.mem_alternatingGroup⟩
  have hc3 : c ^ 3 = 1 := by rw [← hc.orderOf]; exact pow_orderOf_eq_one c
  have hY : x₀ ^ 3 ∈ C.α.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx₀]
    exact Subtype.ext (by simpa using hc3)
  rw [C.α_ker] at hY
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨x₀ ^ 3, hY⟩
  have hj' : (x₀ ^ 3) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have h4 : (4 : ℕ) ^ j = 2 ^ j * 2 ^ j := by
    rw [← mul_pow]
    norm_num
  refine ⟨x₀ ^ (4 ^ j), ?_, ?_⟩
  · have : (x₀ ^ (4 ^ j)) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, h4, pow_mul, hj', one_pow]
    simpa using congrArg Subtype.val this
  · have hmod : 4 ^ j % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [map_pow, hx₀]
    show c ^ (4 ^ j) = c
    rw [← pow_mod_orderOf, hc.orderOf, hmod, pow_one]

variable {C}

theorem comm_of_pow_three (D : C.PiData) {k : ↥C.K} {x : ↥X} (hx3 : (x : G) ^ 3 = 1)
    (hfix : barAct (C.α x : Perm (Fin n)) (Multiplicative.toAdd (D.π k)) =
      Multiplicative.toAdd (D.π k)) : (x : G) * k = k * x := by
  have hcW : (k : G) * x * (k : G)⁻¹ * (x : G)⁻¹ ∈ blockU X := D.comm_mem k x x.2
  have hspec := D.spec k x ⟨_, hcW⟩ rfl
  rw [hfix, sub_self] at hspec
  have hβ0 : Multiplicative.toAdd (C.β ⟨_, hcW⟩) = 0 :=
    heartToBar_injective (hspec.trans (map_zero heartToBar).symm)
  have hker : (⟨_, hcW⟩ : ↥(blockU X)) ∈ C.β.ker :=
    Multiplicative.toAdd.injective (hβ0.trans toAdd_one.symm)
  rw [C.β_ker, Subgroup.mem_subgroupOf] at hker
  set z : G := (k : G) * x * (k : G)⁻¹ * (x : G)⁻¹ with hz
  have hzX : (x : G) * z = z * x :=
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hker).2 x x.2)
  have hz2 : z * z = 1 := by
    have := C.S.elemU.2 z hcW
    rwa [pow_two] at this
  have e1 : (x : G) * (k : G)⁻¹ * (x : G)⁻¹ = (k : G)⁻¹ * z := by rw [hz]; group
  have hxz : (x : G) * z * (x : G)⁻¹ = z := by rw [hzX]; group
  have e2 : (x : G) * x * (k : G)⁻¹ * ((x : G) * x)⁻¹ = (k : G)⁻¹ := by
    calc (x : G) * x * (k : G)⁻¹ * ((x : G) * x)⁻¹ =
        (x : G) * ((x : G) * (k : G)⁻¹ * (x : G)⁻¹) * (x : G)⁻¹ := by group
      _ = (x : G) * ((k : G)⁻¹ * z) * (x : G)⁻¹ := by rw [e1]
      _ = ((x : G) * (k : G)⁻¹ * (x : G)⁻¹) * ((x : G) * z * (x : G)⁻¹) := by group
      _ = (k : G)⁻¹ * z * z := by rw [e1, hxz]
      _ = (k : G)⁻¹ := by rw [mul_assoc, hz2, mul_one]
  have e3 : (x : G) * x * x * (k : G)⁻¹ * ((x : G) * x * x)⁻¹ = (k : G)⁻¹ * z := by
    calc (x : G) * x * x * (k : G)⁻¹ * ((x : G) * x * x)⁻¹ =
        (x : G) * ((x : G) * x * (k : G)⁻¹ * ((x : G) * x)⁻¹) * (x : G)⁻¹ := by group
      _ = (k : G)⁻¹ * z := by rw [e2, e1]
  have hx3' : (x : G) * x * x = 1 := by rw [← hx3, pow_three']
  rw [hx3', one_mul, inv_one, mul_one] at e3
  have hz1 : z = 1 := by
    have := congrArg (fun a => (k : G) * a) e3
    simpa using this.symm
  have : (k : G) * x * (k : G)⁻¹ * (x : G)⁻¹ = 1 := hz1
  calc (x : G) * k = ((k : G) * x * (k : G)⁻¹ * (x : G)⁻¹)⁻¹ * (k * x) := by group
    _ = k * x := by rw [this, inv_one, one_mul]

theorem mem_Q_of_pi_eq (D : C.PiData)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    {k : ↥C.K} (hk2 : ∃ j : ℕ, (k : G) ^ (2 ^ j) = 1) {q : G} (hq : q ∈ CFSG.Open.pCoreOf 2 M)
    (hπ : D.π k = D.π ⟨q, Q_le_K C hq⟩) : (k : G) ∈ CFSG.Open.pCoreOf 2 M := by
  set q' : ↥C.K := ⟨q, Q_le_K C hq⟩ with hq'
  have hC : (k : G) * q⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    have h1 : D.π (k * q'⁻¹) = 1 := by rw [map_mul, map_inv, hπ, mul_inv_cancel]
    exact (D.ker (k * q'⁻¹)).1 h1
  have hk2' : IsPGroup 2 (Subgroup.zpowers (k : G)) := by
    obtain ⟨j, hj⟩ := hk2
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hj)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hkN : Subgroup.zpowers (k : G) ≤
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => pCoreOf_normalized M (C.K_le k.2) hy, fun hy => ?_⟩
    have := pCoreOf_normalized M (M.inv_mem (C.K_le k.2)) hy
    simpa [mul_assoc] using this
  have hP2 := hk2'.to_sup_of_normal_right' (isPGroup_pCoreOf' M) hkN
  have hkq : (k : G) * q⁻¹ ∈ Subgroup.zpowers (k : G) ⊔ CFSG.Open.pCoreOf 2 M :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_right ((CFSG.Open.pCoreOf 2 M).inv_mem hq))
  have hR := hRsyl ((Subgroup.zpowers (k : G) ⊔ CFSG.Open.pCoreOf 2 M) ⊓
    Subgroup.centralizer (X : Set G)) (isPGroup_of_le hP2 inf_le_left) inf_le_right ⟨hkq, hC⟩
  rw [C.S.R_eq_inf] at hR
  have : (k : G) = ((k : G) * q⁻¹) * q := by group
  rw [this]
  exact (CFSG.Open.pCoreOf 2 M).mul_mem (Subgroup.mem_inf.1 hR).1 hq

end Cfg

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall
