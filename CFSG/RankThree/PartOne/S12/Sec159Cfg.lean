module

public import CFSG.RankThree.PartOne.S12.Sec159Act
public import CFSG.RankThree.PartOne.S12.Sec159Tools
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree

namespace Sec159Cfg

structure Cfg159 (p : ℕ) {M : Type} [Group M] [Finite M] (X E P N : Subgroup M) [X.Normal]
    (θ : Subgroup ↥X) [θ.Characteristic] (b : M) : Prop where
  prime : p.Prime
  p5 : 5 ≤ p
  sup : X ⊔ E = ⊤
  Eel : IsElementaryAbelian p ↥E
  Ecard : Nat.card ↥E = p ^ 3
  θp : ¬ p ∣ Nat.card ↥θ
  quasi : CFSG.IsQuasisimple (↥X ⧸ θ)
  Zp : ¬ p ∣ Nat.card ↥(Subgroup.center (↥X ⧸ θ))
  bE : b ∈ E
  b1 : b ≠ 1
  bX : ∀ x ∈ X, b * x = x * b
  hU : ∀ e ∈ E, (∀ x ∈ X, e * x * e⁻¹ * x⁻¹ ∈ θ.map X.subtype) → e ∈ Subgroup.zpowers b
  Psyl : IsSylowOf p P ⊤
  EP : E ≤ P
  PN : P ≤ N
  Pomega : omegaOne p P = E
  norm2 : ∀ B : Subgroup M, B ≤ E → ¬ IsCyclic ↥B → Subgroup.normalizer (B : Set M) ≤ N
  XN : ¬ X ≤ N

variable {p : ℕ} {M : Type} [Group M] [Finite M] {X E P N : Subgroup M} [X.Normal]
  {θ : Subgroup ↥X} [θ.Characteristic] {b : M}

theorem Cfg159.pow_E (h : Cfg159 p X E P N θ b) : ∀ e ∈ E, e ^ p = 1 := fun e he => by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.Eel
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he

theorem Cfg159.orderOf_b (h : Cfg159 p X E P N θ b) : orderOf b = p := by
  have : Fact p.Prime := ⟨h.prime⟩
  exact orderOf_eq_prime (h.pow_E b h.bE) h.b1

theorem Cfg159.b_mem_ker (h : Cfg159 p X E P N θ b) : b ∈ (actQ X θ).ker := by
  rw [mem_ker_actQ]
  intro x hx
  have : b * x * b⁻¹ * x⁻¹ = 1 := by rw [h.bX x hx]; group
  rw [this]
  exact (θ.map X.subtype).one_mem

theorem Cfg159.b_not_mem (h : Cfg159 p X E P N θ b) : b ∉ X := by
  intro hb
  have : Fact p.Prime := ⟨h.prime⟩
  set b' : ↥X := ⟨b, hb⟩
  have hb'p : b' ^ p = 1 := Subtype.ext (h.pow_E b h.bE)
  have hc : ((b' : ↥X) : ↥X ⧸ θ) ∈ Subgroup.center (↥X ⧸ θ) :=
    mk_mem_center_of_mem_ker hb h.b_mem_ker
  have hord : orderOf ((b' : ↥X) : ↥X ⧸ θ) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hb'p, QuotientGroup.mk_one]
  rcases (Nat.dvd_prime h.prime).1 hord with h1 | h1
  ·
    have h2 : ((b' : ↥X) : ↥X ⧸ θ) = 1 := orderOf_eq_one_iff.1 h1
    have hbθ : b' ∈ θ := (QuotientGroup.eq_one_iff b').1 h2
    have h3 : orderOf (⟨b', hbθ⟩ : ↥θ) ∣ Nat.card ↥θ := orderOf_dvd_natCard _
    have h4 : orderOf b' = p := by
      have := h.orderOf_b
      rw [← this]
      exact (Subgroup.orderOf_mk b hb).symm ▸ rfl
    rw [Subgroup.orderOf_mk, h4] at h3
    exact h.θp h3
  · have h3 : orderOf (⟨(b' : ↥X) , hc⟩ : ↥(Subgroup.center (↥X ⧸ θ))) ∣
        Nat.card ↥(Subgroup.center (↥X ⧸ θ)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, h1] at h3
    exact h.Zp h3

theorem Cfg159.zpowers_inf_X (h : Cfg159 p X E P N θ b) : Subgroup.zpowers b ⊓ X = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  obtain ⟨hzb, hzX⟩ := hz
  have hdvd : orderOf z ∣ p := h.orderOf_b ▸ orderOf_dvd_of_mem_zpowers hzb
  have hzp : orderOf z = p := by
    rcases (Nat.dvd_prime h.prime).1 hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hz1
    · exact h1
  have hle : Subgroup.zpowers z ≤ Subgroup.zpowers b := Subgroup.zpowers_le.2 hzb
  have hcard : Nat.card ↥(Subgroup.zpowers b) ≤ Nat.card ↥(Subgroup.zpowers z) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hzp, h.orderOf_b]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hbz : b ∈ Subgroup.zpowers z := heq ▸ Subgroup.mem_zpowers b
  exact h.b_not_mem (Subgroup.zpowers_le.2 hzX hbz)

theorem Cfg159.pElt (h : Cfg159 p X E P N θ b) {z : M} (hzX : z ∈ X) (hzK : z ∈ (actQ X θ).ker)
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

theorem Cfg159.ker_inf_E (h : Cfg159 p X E P N θ b) :
    (actQ X θ).ker ⊓ E = Subgroup.zpowers b := by
  refine le_antisymm (fun e he => h.hU e he.2 (mem_ker_actQ.1 he.1)) ?_
  exact Subgroup.zpowers_le.2 ⟨h.b_mem_ker, h.bE⟩

theorem Cfg159.ker_inf_P (h : Cfg159 p X E P N θ b) :
    (actQ X θ).ker ⊓ P = Subgroup.zpowers b := by
  have : Fact p.Prime := ⟨h.prime⟩
  refine le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.2 ⟨h.b_mem_ker, h.EP h.bE⟩)
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
  exact h.ker_inf_E ▸ ⟨hyK, hyE⟩

theorem Cfg159.isSylowOf_zpowers_ker (h : Cfg159 p X E P N θ b) :
    CFSG.ABGLocalTools.IsSylowOf p (Subgroup.zpowers b) (actQ X θ).ker := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.2 h.Psyl
  have hnorm : (⊤ : Subgroup M) ≤ Subgroup.normalizer (((actQ X θ).ker : Subgroup M) : Set M) := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => (actQ X θ).normal_ker.conj_mem x hx g, fun hx => ?_⟩
    have := (actQ X θ).normal_ker.conj_mem _ hx g⁻¹
    simpa [mul_assoc] using this
  have := hP.inf_of_le_normalizer (N := (actQ X θ).ker) le_top hnorm
  rwa [inf_comm, h.ker_inf_P] at this

theorem Cfg159.ker_le_sup (h : Cfg159 p X E P N θ b) :
    (actQ X θ).ker ≤ ((actQ X θ).ker ⊓ X) ⊔ Subgroup.zpowers b := by
  have : Fact p.Prime := ⟨h.prime⟩
  set K := (actQ X θ).ker with hK
  set T := (K ⊓ X) ⊔ Subgroup.zpowers b with hT
  have hbK : Subgroup.zpowers b ≤ K := Subgroup.zpowers_le.2 h.b_mem_ker
  have h1 : T.relIndex K ∣ (Subgroup.zpowers b).relIndex K :=
    Subgroup.relIndex_dvd_of_le_left K le_sup_right
  have h2 : T.relIndex K ∣ (K ⊓ X).relIndex K := Subgroup.relIndex_dvd_of_le_left K le_sup_left
  have h3 : (K ⊓ X).relIndex K = X.relIndex K := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right X K
  have h4 : X.relIndex K ∣ X.index := Subgroup.relIndex_dvd_index_of_normal X K
  have h5 : X.index ∣ p ^ 3 := by
    have e1 : X.index = X.relIndex (E ⊔ X) := by
      rw [sup_comm, h.sup, Subgroup.relIndex_top_right]
    rw [e1, Subgroup.relIndex_sup_right E X, ← h.Ecard]
    exact Subgroup.relIndex_dvd_card (H := X) (K := E)
  have h6 : T.relIndex K ∣ p ^ 3 := h2.trans (h3 ▸ h4.trans h5)
  have h7 : ¬ p ∣ (Subgroup.zpowers b).relIndex K :=
    (CFSG.ABGLocalTools.isSylowOf_iff.1 h.isSylowOf_zpowers_ker).2.2
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow h.prime).1 h6
  have hm0 : m = 0 := by
    by_contra hm0
    exact h7 ((dvd_pow_self p hm0).trans (hm ▸ h1))
  rw [hm0, pow_zero] at hm
  exact Subgroup.relIndex_eq_one.1 hm

theorem Cfg159.not_isCyclic_of_ne (h : Cfg159 p X E P N θ b) {R : Subgroup M} (hRE : R ≤ E)
    (hbR : b ∈ R) (hRne : R ≠ Subgroup.zpowers b) : ¬ IsCyclic ↥R := by
  intro hcyc
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgp : (g : M) ^ p = 1 := h.pow_E g (hRE g.2)
  have hord : orderOf g = Nat.card ↥R := orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : Nat.card ↥R ∣ p := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext hgp)
  have hbp : p ∣ Nat.card ↥R := by
    have := orderOf_dvd_natCard (⟨b, hbR⟩ : ↥R)
    rwa [Subgroup.orderOf_mk, h.orderOf_b] at this
  have hcard : Nat.card ↥R = p := Nat.dvd_antisymm hdvd hbp
  have hle : Subgroup.zpowers b ≤ R := Subgroup.zpowers_le.2 hbR
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_zpowers, h.orderOf_b])
  exact hRne heq.symm

theorem Cfg159.normN (h : Cfg159 p X E P N θ b) {R : Subgroup M} (hRE : R ≤ E) (hbR : b ∈ R)
    (hRne : R ≠ Subgroup.zpowers b) : Subgroup.normalizer (R : Set M) ≤ N :=
  h.norm2 R hRE (h.not_isCyclic_of_ne hRE hbR hRne)

theorem Cfg159.ker_inf_X_le_N (h : Cfg159 p X E P N θ b) : (actQ X θ).ker ⊓ X ≤ N := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hKn : (actQ X θ).ker.Normal := (actQ X θ).normal_ker
  have hZn : ((actQ X θ).ker ⊓ X).Normal := inferInstance
  have hnorm : E ≤ Subgroup.normalizer ((((actQ X θ).ker ⊓ X : Subgroup M)) : Set M) := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hZn.conj_mem x hx g, fun hx => ?_⟩
    have := hZn.conj_mem _ hx g⁻¹
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
  exact Sec159.le_of_pPrime_normalized h.prime h.Eel h.Ecard h.norm2 hnorm hZp

theorem Cfg159.ker_le_N (h : Cfg159 p X E P N θ b) : (actQ X θ).ker ≤ N := by
  refine h.ker_le_sup.trans (sup_le h.ker_inf_X_le_N ?_)
  exact Subgroup.zpowers_le.2 (h.PN (h.EP h.bE))

end Sec159Cfg

end CFSG.RankThree.PartOne
