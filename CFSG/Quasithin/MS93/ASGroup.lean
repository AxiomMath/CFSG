module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem mem_of_isSubnormal_of_odd {R : Subgroup G} (hR : IsPGroup 2 R) {H K : Subgroup G}
    (hHK : IsSubnormal H K) (hK : ∀ k ∈ K, ∃ h ∈ H, ∃ r ∈ R, k = h * r) {g : G} (hg : g ∈ K)
    (hodd : Odd (orderOf g)) : g ∈ H := by
  induction hHK generalizing g with
  | refl => exact hg
  | @step H M K hHM hn _ ih =>
    have hgM : g ∈ M := ih (fun k hk => by
      obtain ⟨h, hh, r, hr, rfl⟩ := hK k hk
      exact ⟨h, hHM hh, r, hr, rfl⟩) hg hodd
    obtain ⟨h, hh, r, hr, rfl⟩ := hK _ hg
    have hrM : r ∈ M := by
      have : r = h⁻¹ * (h * r) := by group
      rw [this]
      exact M.mul_mem (M.inv_mem (hHM hh)) hgM
    obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
    have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    let x : ↥M ⧸ H.subgroupOf M := QuotientGroup.mk ⟨h * r, hgM⟩
    have hxr : x = QuotientGroup.mk ⟨r, hrM⟩ := by
      apply QuotientGroup.eq.mpr
      have hc := hn.conj_mem ⟨h⁻¹, M.inv_mem (hHM hh)⟩
        (by rw [Subgroup.mem_subgroupOf]; exact H.inv_mem hh) ⟨r⁻¹, M.inv_mem hrM⟩
      rw [Subgroup.mem_subgroupOf] at hc ⊢
      convert hc using 1
      simp [mul_assoc]
    have h1 : orderOf x ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hxr, ← QuotientGroup.mk_pow]
      have : (⟨r, hrM⟩ : ↥M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, QuotientGroup.mk_one]
    have h2 : orderOf x ∣ orderOf (h * r) := by
      apply orderOf_dvd_of_pow_eq_one
      show (QuotientGroup.mk ⟨h * r, hgM⟩ : ↥M ⧸ H.subgroupOf M) ^ orderOf (h * r) = 1
      rw [← QuotientGroup.mk_pow]
      have : (⟨h * r, hgM⟩ : ↥M) ^ orderOf (h * r) = 1 :=
        Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this, QuotientGroup.mk_one]
    have hcop : Nat.Coprime (2 ^ k) (orderOf (h * r)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    have hx1 : orderOf x = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2)
    have hx : x = 1 := orderOf_eq_one_iff.mp hx1
    have := (QuotientGroup.eq_one_iff _).mp hx
    rwa [Subgroup.mem_subgroupOf] at this

@[expose] def oddGen (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ X ∧ Odd (orderOf x)}

theorem oddGen_le (X : Subgroup G) : oddGen X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem le_normalizer_oddGen (X : Subgroup G) :
    X ≤ Subgroup.normalizer (oddGen X : Set G) := by
  have key : ∀ l ∈ X, ∀ x ∈ oddGen X, l * x * l⁻¹ ∈ oddGen X := by
    intro l hl x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      refine Subgroup.subset_closure ⟨X.mul_mem (X.mul_mem hl hy.1) (X.inv_mem hl), ?_⟩
      have := MulEquiv.orderOf_eq (MulAut.conj l) y
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hy.2
    | one => simp
    | mul y z _ _ hy hz =>
      have : l * (y * z) * l⁻¹ = (l * y * l⁻¹) * (l * z * l⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
      have : l * y⁻¹ * l⁻¹ = (l * y * l⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hy
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key l hl x
  · intro hx
    have := key l⁻¹ (X.inv_mem hl) _ hx
    simpa [mul_assoc] using this

theorem exists_pow_mem_oddGen [Finite G] {X : Subgroup G} {x : G} (hx : x ∈ X) :
    ∃ a : ℕ, x ^ 2 ^ a ∈ oddGen X := by
  obtain ⟨a, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨a, Subgroup.subset_closure ⟨X.pow_mem hx _, ?_⟩⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, he⟩, he,
    Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  exact hm

theorem oddGen_eq_of_perfect [Finite G] {L : Subgroup G} (hL : ⁅L, L⁆ = L) : oddGen L = L := by
  refine le_antisymm (oddGen_le L) ?_
  set N : Subgroup ↥L := (oddGen L).subgroupOf L with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddGen L g.2) n).mp hn
    simpa using this
  have hp : IsPGroup 2 (↥L ⧸ N) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha⟩ := exists_pow_mem_oddGen hx
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    simpa using ha
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  have htop : N = ⊤ := by
    by_contra hne
    have : Nontrivial (↥L ⧸ N) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hs
      apply hne
      refine eq_top_iff.mpr fun x _ => ?_
      exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Group.IsPerfect.not_isNilpotent (↥L ⧸ N) hp.isNilpotent
  intro x hx
  have : (⟨x, hx⟩ : ↥L) ∈ N := htop ▸ Subgroup.mem_top _
  rwa [hN, Subgroup.mem_subgroupOf] at this

theorem le_of_coe_eq_mul_left {G₀ L R : Subgroup G}
    (hG : (G₀ : Set G) = (L : Set G) * (R : Set G)) : L ≤ G₀ := by
  intro l hl
  have : l ∈ (L : Set G) * (R : Set G) := ⟨l, hl, 1, R.one_mem, mul_one l⟩
  rw [← hG] at this
  exact this

theorem le_of_coe_eq_mul_right {G₀ L R : Subgroup G}
    (hG : (G₀ : Set G) = (L : Set G) * (R : Set G)) : R ≤ G₀ := by
  intro r hr
  have : r ∈ (L : Set G) * (R : Set G) := ⟨1, L.one_mem, r, hr, one_mul r⟩
  rw [← hG] at this
  exact this

theorem eq_sup_of_coe_eq_mul {G₀ L R : Subgroup G}
    (hG : (G₀ : Set G) = (L : Set G) * (R : Set G)) : G₀ = L ⊔ R := by
  refine le_antisymm (fun g hg => ?_) (sup_le (le_of_coe_eq_mul_left hG)
    (le_of_coe_eq_mul_right hG))
  have hg' : g ∈ (L : Set G) * (R : Set G) := hG ▸ hg
  obtain ⟨l, hl, r, hr, rfl⟩ := hg'
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hr)

theorem eq_oddGen_of_isSubnormal [Finite G] {L G₀ R : Subgroup G} (hsub : IsSubnormal L G₀)
    (hL : ⁅L, L⁆ = L) (hR : IsPGroup 2 R) (hG : (G₀ : Set G) = (L : Set G) * (R : Set G)) :
    L = oddGen G₀ := by
  have hK : ∀ k ∈ G₀, ∃ h ∈ L, ∃ r ∈ R, k = h * r := by
    intro k hk
    have hk' : k ∈ (L : Set G) * (R : Set G) := hG ▸ hk
    obtain ⟨h, hh, r, hr, rfl⟩ := hk'
    exact ⟨h, hh, r, hr, rfl⟩
  refine le_antisymm ?_ ?_
  · rw [← oddGen_eq_of_perfect hL]
    exact Subgroup.closure_mono fun x hx => ⟨le_of_coe_eq_mul_left hG hx.1, hx.2⟩
  · exact (Subgroup.closure_le L).mpr fun x hx => mem_of_isSubnormal_of_odd hR hsub hK hx.1 hx.2

theorem sq_eq_one_of_isE2 {n : ℕ} {X : Type} [Group X] (h : IsE2 n X) (x : X) : x ^ 2 = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat]
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]

variable [Finite G]

theorem pCoreOf_le_of_odd_relIndex {H G₀ : Subgroup G} (hHG : H ≤ G₀)
    (hodd : ¬ 2 ∣ H.relIndex G₀) : pCoreOf 2 G₀ ≤ H := by
  obtain ⟨S, hS, -⟩ :=
    EscapingLocal.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup G) ≤ H) IsPGroup.of_bot
  have hSG : IsSylowTwoOf S G₀ := by
    refine ⟨hS.1.trans hHG, hS.2.1, ?_⟩
    change ¬ 2 ∣ S.relIndex G₀
    rw [← Subgroup.relIndex_mul_relIndex S H G₀ hS.1 hHG]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hS.2.2 h
    · exact hodd h
  exact (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSG).trans hS.1

theorem isPGroup_cfsgPCore (X : Type) [Group X] [Finite X] : IsPGroup 2 (CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.pCore_isPGroup 2

theorem isMSPair_isPGroup_and_pCoreOf_le {G₀ R : Subgroup G} (h : IsMSPair G₀ R) :
    IsPGroup 2 R ∧ pCoreOf 2 G₀ ≤ R := by
  obtain ⟨⟨-, -, L, -, hG, -⟩, h2, -⟩ := h
  have hRG := le_of_coe_eq_mul_right hG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h2 with ⟨H', hlt, hodd, rfl⟩ | ⟨-, hO, -, -, -, -, -, hE⟩
  · refine ⟨CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H', ?_⟩
    have hHG : H' ≤ G₀ := hlt.le
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (pCoreOf_le_of_odd_relIndex hHG hodd)
      (hHG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₀))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀)
  · refine ⟨?_, hO⟩
    rintro ⟨r, hr⟩
    set q : ↥G₀ ⧸ CFSG.pCore 2 ↥G₀ := QuotientGroup.mk' (CFSG.pCore 2 ↥G₀) ⟨r, hRG hr⟩ with hq
    have hqmem : q ∈ (R.subgroupOf G₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥G₀)) :=
      ⟨⟨r, hRG hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
    have hq2 : q ^ 2 = 1 := by
      have := sq_eq_one_of_isE2 hE ⟨q, hqmem⟩
      simpa using congrArg Subtype.val this
    have hmem : (⟨r, hRG hr⟩ : ↥G₀) ^ 2 ∈ CFSG.pCore 2 ↥G₀ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hq2
    obtain ⟨k, hk⟩ := isPGroup_cfsgPCore ↥G₀ ⟨_, hmem⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : ((⟨r, hRG hr⟩ : ↥G₀) ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have : r ^ 2 ^ (k + 1) = 1 := by
      have := congrArg Subtype.val hk'
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
      rw [← pow_mul, ← pow_succ'] at this
      exact this
    simpa using this

theorem isMSPair_pCoreOf_ne_bot {G₀ R : Subgroup G} (h : IsMSPair G₀ R) :
    pCoreOf 2 G₀ ≠ ⊥ := by
  obtain ⟨⟨-, hC, L, hL, hG, -⟩, -, -⟩ := h
  intro hO
  apply ne_bot_of_mem_cComp hL
  refine eq_bot_iff.mpr ((le_of_coe_eq_mul_left hG).trans ?_)
  intro x hx
  have : x ∈ G₀ ⊓ Subgroup.centralizer (pCoreOf 2 G₀ : Set G) := by
    refine ⟨hx, ?_⟩
    rw [hO]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      rw [hy, one_mul, mul_one]
  have := hC this
  rwa [hO] at this

theorem isMSPair_ne_bot {G₀ R : Subgroup G} (h : IsMSPair G₀ R) : R ≠ ⊥ := fun hR =>
  isMSPair_pCoreOf_ne_bot h (eq_bot_iff.mpr (hR ▸ (isMSPair_isPGroup_and_pCoreOf_le h).2))

theorem isMSPair_eq_oddGen {G₀ R L : Subgroup G} (h : IsMSPair G₀ R) (hL : L ∈ cComp G₀)
    (hG : (G₀ : Set G) = (L : Set G) * (R : Set G)) : L = oddGen G₀ :=
  eq_oddGen_of_isSubnormal hL.2.2.1 hL.2.1 (isMSPair_isPGroup_and_pCoreOf_le h).1 hG


section Commutators

variable {G : Type} [Group G]

theorem three_subgroups_le {N H₁ H₂ H₃ : Subgroup G}
    (hn₁ : H₁ ≤ Subgroup.normalizer (N : Set G)) (hn₂ : H₂ ≤ Subgroup.normalizer (N : Set G))
    (hn₃ : H₃ ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N)
    (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  have hconj : ∀ g ∈ Subgroup.normalizer (N : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have key : ∀ w ∈ ⁅H₁, H₂⁆, w ∈ Subgroup.normalizer (N : Set G) ∧ ∀ z ∈ H₃, ⁅w, z⁆ ∈ N := by
    intro w hw
    have hw' : w ∈ Subgroup.closure {g : G | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = g} := hw
    clear hw
    induction hw' using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hw
      refine ⟨?_, fun z hz => ?_⟩
      · rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hn₁ hx) (hn₂ hy))
          (Subgroup.inv_mem _ (hn₁ hx))) (Subgroup.inv_mem _ (hn₂ hy))
      · have hu : ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ ∈ N := by
          rw [← commutatorElement_inv]
          exact N.inv_mem (h2 (Subgroup.commutator_mem_commutator
            (Subgroup.commutator_mem_commutator (H₃.inv_mem hz) (H₁.inv_mem hx)) hy))
        have hv : ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ ∈ N := by
          rw [← commutatorElement_inv]
          exact N.inv_mem (h1 (Subgroup.commutator_mem_commutator
            (Subgroup.commutator_mem_commutator (H₂.inv_mem hy) hz) (H₁.inv_mem hx)))
        have hxz := Subgroup.mul_mem _ (hn₁ hx) (hn₃ hz)
        have hxy := Subgroup.mul_mem _ (hn₁ hx) (hn₂ hy)
        have e1 : ⁅⁅x, y⁆, z⁆ = (x * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ * (x * y)⁻¹) *
            (x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ * (x * z)⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e1]
        exact N.mul_mem (hconj _ hxy _ hv) (hconj _ hxz _ hu)
    | one => exact ⟨Subgroup.one_mem _, fun z _ => by simp⟩
    | mul a b _ _ iha ihb =>
      refine ⟨Subgroup.mul_mem _ iha.1 ihb.1, fun z hz => ?_⟩
      have e1 : ⁅a * b, z⁆ = (a * ⁅b, z⁆ * a⁻¹) * ⁅a, z⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact N.mul_mem (hconj _ iha.1 _ (ihb.2 z hz)) (iha.2 z hz)
    | inv a _ iha =>
      refine ⟨Subgroup.inv_mem _ iha.1, fun z hz => ?_⟩
      have e1 : ⁅a⁻¹, z⁆ = a⁻¹ * (⁅a, z⁆)⁻¹ * a := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      have := hconj _ (Subgroup.inv_mem _ iha.1) _ (N.inv_mem (iha.2 z hz))
      simpa using this
  exact Subgroup.commutator_le.mpr fun w hw z hz => (key w hw).2 z hz

theorem le_normalizer_commutator_of {M A B : Subgroup G}
    (hA : M ≤ Subgroup.normalizer (A : Set G)) (hB : M ≤ Subgroup.normalizer (B : Set G)) :
    M ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ M, ∀ x ∈ ⁅A, B⁆, g * x * g⁻¹ ∈ ⁅A, B⁆ := by
    intro g hg
    have hle : ⁅A, B⁆ ≤ ⁅A, B⁆.comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      show (MulAut.conj g) ⁅a, b⁆ ∈ ⁅A, B⁆
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 (hA hg) a).1 ha)
        ((Subgroup.mem_normalizer_iff.1 (hB hg) b).1 hb)
    intro x hx
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem commutator_eq_commutator_commutator {M X L : Subgroup G} (hXM : X ≤ M) (hLM : L ≤ M)
    (hX : M ≤ Subgroup.normalizer (X : Set G)) (hL : M ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) : ⁅X, L⁆ = ⁅⁅X, L⁆, L⁆ := by
  have hXL : M ≤ Subgroup.normalizer ((⁅X, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of hX hL
  have hN : M ≤ Subgroup.normalizer ((⁅⁅X, L⁆, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of hXL hL
  refine le_antisymm ?_ ?_
  · have h3 : ⁅⁅L, L⁆, X⁆ ≤ ⁅⁅X, L⁆, L⁆ := by
      refine three_subgroups_le (hLM.trans hN) (hLM.trans hN) (hXM.trans hN) ?_ le_rfl
      rw [Subgroup.commutator_comm L X]
    rw [hperf, Subgroup.commutator_comm] at h3
    exact h3
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hLM.trans hXL)

variable [Finite G]

theorem pCoreOf_le_pCoreOf_of_le_normalizer {G₀ L : Subgroup G} (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) : pCoreOf 2 L ≤ pCoreOf 2 G₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLG)
    (hGL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem inf_le_pCoreOf {G₀ L : Subgroup G} (hLG : L ≤ G₀) :
    pCoreOf 2 G₀ ⊓ L ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀).to_le inf_le_left)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf,
    Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₀ (hLG hg)) x,
    Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) x]

theorem commutator_le_pCoreOf {G₀ L : Subgroup G} (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) : ⁅pCoreOf 2 G₀, L⁆ ≤ pCoreOf 2 L := by
  refine le_trans (le_inf ?_ ?_) (inf_le_pCoreOf hLG)
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hLG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₀))
  · rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 G₀).trans hGL)

theorem commutator_eq_blockU {G₀ L : Subgroup G} (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅L, L⁆ = L) :
    ⁅pCoreOf 2 G₀, L⁆ = blockU L := by
  refine le_antisymm ?_ (Subgroup.commutator_mono (pCoreOf_le_pCoreOf_of_le_normalizer hLG hGL)
    le_rfl)
  rw [commutator_eq_commutator_commutator (CFSG.LieType.BorelTits.pCoreOf_le 2 G₀) hLG
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₀) hGL hperf]
  exact Subgroup.commutator_mono (commutator_le_pCoreOf hLG hGL) le_rfl

end Commutators

section Coprime

variable {G : Type} [Group G]

theorem eq_one_of_conj_eq_mul {z x c : G} (hzc : z * c = c * z) (hzx : z * x * z⁻¹ = c * x)
    (hodd : Odd (orderOf z)) (hc : ∃ k : ℕ, c ^ 2 ^ k = 1) : c = 1 := by
  have hpow : ∀ n : ℕ, z ^ n * x * (z ^ n)⁻¹ = c ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hzcn : z * c ^ n = c ^ n * z := (Commute.pow_right hzc n).eq
      calc z ^ (n + 1) * x * (z ^ (n + 1))⁻¹ = z * (z ^ n * x * (z ^ n)⁻¹) * z⁻¹ := by
            rw [pow_succ']; group
        _ = z * (c ^ n * x) * z⁻¹ := by rw [ih]
        _ = c ^ n * (z * x * z⁻¹) := by
            rw [← mul_assoc, hzcn]; group
        _ = c ^ (n + 1) * x := by rw [hzx, pow_succ]; group
  have h1 : c ^ orderOf z = 1 := by
    have := hpow (orderOf z)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at this
    exact (mul_eq_right.mp this.symm)
  obtain ⟨k, hk⟩ := hc
  have hd1 : orderOf c ∣ orderOf z := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf z) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd2 hd1))

variable [Finite G]

theorem eq_one_of_odd_of_commutator_mem {G₀ L : Subgroup G} (hC : CharTwo G₀) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) {z : G} (hz : z ∈ L)
    (hodd : Odd (orderOf z))
    (htriv : ∀ v ∈ ⁅pCoreOf 2 G₀, L⁆, z * v * z⁻¹ * v⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 G₀ with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀
  have h2elt : ∀ c ∈ Q, ∃ k : ℕ, c ^ 2 ^ k = 1 := fun c hc => by
    obtain ⟨k, hk⟩ := hQ2 ⟨c, hc⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hVQ : ⁅Q, L⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hLG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₀))
  have hVn : L ≤ Subgroup.normalizer ((⁅Q, L⁆ : Subgroup G) : Set G) :=
    hLG.trans (le_normalizer_commutator_of (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₀)
      hGL)
  have hV : ∀ v ∈ ⁅Q, L⁆, z * v = v * z := by
    intro v hv
    set c := z * v * z⁻¹ * v⁻¹ with hc
    have hcC := htriv v hv
    have hcV : c ∈ ⁅Q, L⁆ := Subgroup.mul_mem _
      ((Subgroup.mem_normalizer_iff.mp (hVn hz) v).mp hv) (Subgroup.inv_mem _ hv)
    have hzc : z * c = c * z := Subgroup.mem_centralizer_iff.mp hcC z hz
    have hc1 := eq_one_of_conj_eq_mul (x := v) hzc (by rw [hc]; group) hodd (h2elt c (hVQ hcV))
    have : z * v * z⁻¹ = v := by
      have h := hc1
      rw [hc] at h
      calc z * v * z⁻¹ = z * v * z⁻¹ * v⁻¹ * v := by group
        _ = v := by rw [h, one_mul]
    calc z * v = z * v * z⁻¹ * z := by group
      _ = v * z := by rw [this]
  have hzQ : z ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    set d := z * x * z⁻¹ * x⁻¹ with hd
    have hdV : d ∈ ⁅Q, L⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hz hx
    have hzd : z * d = d * z := hV d hdV
    have hd1 := eq_one_of_conj_eq_mul (x := x) hzd (by rw [hd]; group) hodd (h2elt d (hVQ hdV))
    have : z * x * z⁻¹ = x := by
      calc z * x * z⁻¹ = z * x * z⁻¹ * x⁻¹ * x := by group
        _ = x := by rw [← hd, hd1, one_mul]
    calc x * z = z * x * z⁻¹ * z := by rw [this]
      _ = z * x := by group
  have hzQ' : z ∈ Q := hC ⟨hLG hz, hzQ⟩
  obtain ⟨k, hk⟩ := h2elt z hzQ'
  have hd2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf z) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd2 dvd_rfl))

end Coprime

end CFSG.Quasithin.MS93
