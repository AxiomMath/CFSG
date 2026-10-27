module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.S12.Sec159Act
public import CFSG.RankThree.PartOne.S12.Sec159Tools
public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree
open Sec159Cfg

namespace Sec159Five

structure Cfg5 (p : ℕ) {M : Type} [Group M] [Finite M] (X E A P N : Subgroup M) [X.Normal]
    (θ : Subgroup ↥X) [θ.Characteristic] (x : M) : Prop where
  prime : p.Prime
  p5 : 5 ≤ p
  sup : X ⊔ E = ⊤
  Eel : IsElementaryAbelian p ↥E
  Ecard : Nat.card ↥E = p ^ 4
  AE : A ≤ E
  Acard : Nat.card ↥A = p ^ 3
  θp : ¬ p ∣ Nat.card ↥θ
  quasi : CFSG.IsQuasisimple (↥X ⧸ θ)
  Zp : ¬ p ∣ Nat.card ↥(Subgroup.center (↥X ⧸ θ))
  xA : x ∈ A
  x1 : x ≠ 1
  xX : ∀ y ∈ X, x * y = y * x
  hA : ∀ a ∈ A, (∀ y ∈ X, a * y * a⁻¹ * y⁻¹ ∈ θ.map X.subtype) → a ∈ Subgroup.zpowers x
  Psyl : IsSylowOf p P ⊤
  EP : E ≤ P
  PN : P ≤ N
  Pomega : omegaOne p P = E
  normA : ∀ B : Subgroup M, B ≤ A → ¬ IsCyclic ↥B → Subgroup.normalizer (B : Set M) ≤ N
  normE : ∀ R : Subgroup M, R ≤ E → p ^ 3 ≤ Nat.card ↥R → Subgroup.normalizer (R : Set M) ≤ N
  XN : ¬ X ≤ N

variable {p : ℕ} {M : Type} [Group M] [Finite M] {X E A P N : Subgroup M} [X.Normal]
  {θ : Subgroup ↥X} [θ.Characteristic] {x : M}

theorem Cfg5.pow_E (h : Cfg5 p X E A P N θ x) : ∀ e ∈ E, e ^ p = 1 := fun e he => by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.Eel
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he

theorem Cfg5.Ael (h : Cfg5 p X E A P N θ x) : IsElementaryAbelian p ↥A :=
  Sec159.isElementaryAbelian_of_le h.Eel h.AE

theorem Cfg5.orderOf_x (h : Cfg5 p X E A P N θ x) : orderOf x = p := by
  have : Fact p.Prime := ⟨h.prime⟩
  exact orderOf_eq_prime (h.pow_E x (h.AE h.xA)) h.x1

theorem Cfg5.x_mem_ker (h : Cfg5 p X E A P N θ x) : x ∈ (actQ X θ).ker := by
  rw [mem_ker_actQ]
  intro y hy
  have : x * y * x⁻¹ * y⁻¹ = 1 := by rw [h.xX y hy]; group
  rw [this]
  exact (θ.map X.subtype).one_mem

theorem Cfg5.pElt (h : Cfg5 p X E A P N θ x) {z : M} (hzX : z ∈ X) (hzK : z ∈ (actQ X θ).ker)
    {k : ℕ} (hk : z ^ (p ^ k) = 1) : z = 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hc := mk_mem_center_of_mem_ker hzX hzK
  set z' : ↥X := ⟨z, hzX⟩ with hz'
  have hz'k : z' ^ (p ^ k) = 1 := Subtype.ext hk
  have hq1 : ((z' : ↥X) : ↥X ⧸ θ) = 1 := by
    have h1 : orderOf ((z' : ↥X) : ↥X ⧸ θ) ∣ p ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow, hz'k, QuotientGroup.mk_one]
    have h2 : orderOf ((z' : ↥X) : ↥X ⧸ θ) ∣ Nat.card ↥(Subgroup.center (↥X ⧸ θ)) := by
      have := orderOf_dvd_natCard (⟨_, hc⟩ : ↥(Subgroup.center (↥X ⧸ θ)))
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (p ^ k) (Nat.card ↥(Subgroup.center (↥X ⧸ θ))) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd h.prime).2 h.Zp)
    exact orderOf_eq_one_iff.1 ((hcop.coprime_dvd_left h1).eq_one_of_dvd h2)
  have hzθ : z' ∈ θ := (QuotientGroup.eq_one_iff z').1 hq1
  have h1 : orderOf z' ∣ p ^ k := orderOf_dvd_of_pow_eq_one hz'k
  have h2 : orderOf z' ∣ Nat.card ↥θ := by
    have := orderOf_dvd_natCard (⟨z', hzθ⟩ : ↥θ)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (p ^ k) (Nat.card ↥θ) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd h.prime).2 h.θp)
  have : z' = 1 := orderOf_eq_one_iff.1 ((hcop.coprime_dvd_left h1).eq_one_of_dvd h2)
  exact congrArg Subtype.val this

theorem Cfg5.U_inf_X (h : Cfg5 p X E A P N θ x) : (actQ X θ).ker ⊓ E ⊓ X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  exact h.pElt hz.2 hz.1.1 (k := 1) (by rw [pow_one]; exact h.pow_E z hz.1.2)

theorem Cfg5.ker_inf_A (h : Cfg5 p X E A P N θ x) :
    (actQ X θ).ker ⊓ A = Subgroup.zpowers x := by
  refine le_antisymm (fun a ha => h.hA a ha.2 (mem_ker_actQ.1 ha.1)) ?_
  exact Subgroup.zpowers_le.2 ⟨h.x_mem_ker, h.xA⟩

theorem Cfg5.ker_inf_P (h : Cfg5 p X E A P N θ x) :
    (actQ X θ).ker ⊓ P = (actQ X θ).ker ⊓ E := by
  have : Fact p.Prime := ⟨h.prime⟩
  refine le_antisymm (fun y hy => ?_) (inf_le_inf_left _ h.EP)
  obtain ⟨hyK, hyP⟩ := hy
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h.Psyl.2.1) ⟨y, hyP⟩
  have hyk : y ^ (p ^ k) = 1 := by
    have := pow_orderOf_eq_one (⟨y, hyP⟩ : ↥P)
    rw [hk] at this
    exact congrArg Subtype.val this
  have hp1 : y ^ p = 1 := by
    refine h.pElt (pow_mem_of_sup_eq_top h.sup h.pow_E y) ((actQ X θ).ker.pow_mem hyK p) (k := k) ?_
    rw [← pow_mul, mul_comm, pow_mul, hyk, one_pow]
  have hyE : y ∈ E := h.Pomega ▸ Subgroup.subset_closure ⟨hyP, hp1⟩
  exact ⟨hyK, hyE⟩

theorem Cfg5.isSylowOf_U_ker (h : Cfg5 p X E A P N θ x) :
    CFSG.ABGLocalTools.IsSylowOf p ((actQ X θ).ker ⊓ E) (actQ X θ).ker := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.2 h.Psyl
  have hnorm : (⊤ : Subgroup M) ≤ Subgroup.normalizer (((actQ X θ).ker : Subgroup M) : Set M) := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => (actQ X θ).normal_ker.conj_mem y hy g, fun hy => ?_⟩
    have := (actQ X θ).normal_ker.conj_mem _ hy g⁻¹
    simpa [mul_assoc] using this
  have := hP.inf_of_le_normalizer (N := (actQ X θ).ker) le_top hnorm
  rwa [inf_comm, h.ker_inf_P] at this

theorem Cfg5.index_dvd (h : Cfg5 p X E A P N θ x) : X.index ∣ p ^ 4 := by
  have e1 : X.index = X.relIndex (E ⊔ X) := by
    rw [sup_comm, h.sup, Subgroup.relIndex_top_right]
  rw [e1, Subgroup.relIndex_sup_right E X, ← h.Ecard]
  exact Subgroup.relIndex_dvd_card (H := X) (K := E)

theorem Cfg5.ker_le_sup (h : Cfg5 p X E A P N θ x) :
    (actQ X θ).ker ≤ ((actQ X θ).ker ⊓ X) ⊔ ((actQ X θ).ker ⊓ E) := by
  have : Fact p.Prime := ⟨h.prime⟩
  set K := (actQ X θ).ker with hK
  set T := (K ⊓ X) ⊔ (K ⊓ E) with hT
  have h1 : T.relIndex K ∣ (K ⊓ E).relIndex K :=
    Subgroup.relIndex_dvd_of_le_left K le_sup_right
  have h2 : T.relIndex K ∣ (K ⊓ X).relIndex K := Subgroup.relIndex_dvd_of_le_left K le_sup_left
  have h3 : (K ⊓ X).relIndex K = X.relIndex K := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right X K
  have h4 : X.relIndex K ∣ X.index := Subgroup.relIndex_dvd_index_of_normal X K
  have h6 : T.relIndex K ∣ p ^ 4 := h2.trans (h3 ▸ h4.trans h.index_dvd)
  have h7 : ¬ p ∣ (K ⊓ E).relIndex K :=
    (CFSG.ABGLocalTools.isSylowOf_iff.1 h.isSylowOf_U_ker).2.2
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow h.prime).1 h6
  have hm0 : m = 0 := by
    by_contra hm0
    exact h7 ((dvd_pow_self p hm0).trans (hm ▸ h1))
  rw [hm0, pow_zero] at hm
  exact Subgroup.relIndex_eq_one.1 hm

theorem Cfg5.ker_inf_X_le_N (h : Cfg5 p X E A P N θ x) : (actQ X θ).ker ⊓ X ≤ N := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hKn : (actQ X θ).ker.Normal := (actQ X θ).normal_ker
  have hZn : ((actQ X θ).ker ⊓ X).Normal := inferInstance
  have hnorm : A ≤ Subgroup.normalizer ((((actQ X θ).ker ⊓ X : Subgroup M)) : Set M) := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hZn.conj_mem y hy g, fun hy => ?_⟩
    have := hZn.conj_mem _ hy g⁻¹
    simpa [mul_assoc] using this
  have hZp : ¬ p ∣ Nat.card ↥((actQ X θ).ker ⊓ X) := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥((actQ X θ).ker ⊓ X)) p hdvd
    have hz1 : (z : M) ^ (p ^ 1) = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      rw [pow_one]
      exact congrArg Subtype.val this
    have := h.pElt z.2.2 z.2.1 hz1
    have hzone : z = 1 := Subtype.ext this
    rw [hzone, orderOf_one] at hz
    exact h.prime.one_lt.ne hz
  exact Sec159.le_of_pPrime_normalized h.prime h.Ael h.Acard h.normA hnorm hZp

theorem Cfg5.U_le_N (h : Cfg5 p X E A P N θ x) : (actQ X θ).ker ⊓ E ≤ N :=
  fun _ hy => h.PN (h.EP hy.2)

theorem Cfg5.ker_le_N (h : Cfg5 p X E A P N θ x) : (actQ X θ).ker ≤ N :=
  h.ker_le_sup.trans (sup_le h.ker_inf_X_le_N h.U_le_N)

end Sec159Five

end CFSG.RankThree.PartOne
