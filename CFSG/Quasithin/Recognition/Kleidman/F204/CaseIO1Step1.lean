module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIO1Basic
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIO1Abs

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

section CentMod

variable {G : Type*} [Group G]

def centMod (A T W : Subgroup G) (hA : ∀ a ∈ A, ∀ w ∈ W, a * w * a⁻¹ ∈ W) : Subgroup G where
  carrier := {m | m ∈ A ∧ ∀ t ∈ T, ⁅m, t⁆ ∈ W}
  mul_mem' := by
    rintro m m' ⟨hmA, hm⟩ ⟨hm'A, hm'⟩
    refine ⟨A.mul_mem hmA hm'A, fun t ht => ?_⟩
    have e : ⁅m * m', t⁆ = m * ⁅m', t⁆ * m⁻¹ * ⁅m, t⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem (hA m hmA _ (hm' t ht)) (hm t ht)
  one_mem' := ⟨A.one_mem, fun t _ => by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro m ⟨hmA, hm⟩
    refine ⟨A.inv_mem hmA, fun t ht => ?_⟩
    have e : ⁅m⁻¹, t⁆ = m⁻¹ * ⁅m, t⁆⁻¹ * m⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hA m⁻¹ (A.inv_mem hmA) _ (W.inv_mem (hm t ht))

theorem five_stab {R : Type*} [Group R] {m f : R} (hf5 : f ^ 5 = 1) (hn : ⁅⁅m, f⁆, f⁆ = 1) :
    ⁅m, f⁆ ^ 5 = 1 := by
  set n : R := ⁅m, f⁆ with hn'
  have hc : Commute f n := by
    have := commutatorElement_eq_one_iff_mul_comm.mp hn
    exact this.symm
  have key : ∀ j : ℕ, ⁅m, f ^ j⁆ = n ^ j := by
    intro j
    induction j with
    | zero => simp [commutatorElement_def]
    | succ j ih =>
      have e : ⁅m, f ^ (j + 1)⁆ = ⁅m, f⁆ * (f * ⁅m, f ^ j⁆ * f⁻¹) := by
        simp only [commutatorElement_def, pow_succ]; group
      rw [e, ih, ← hn']
      have : f * n ^ j * f⁻¹ = n ^ j := by
        have := (hc.pow_right j).eq
        calc f * n ^ j * f⁻¹ = (n ^ j * f) * f⁻¹ := by rw [this]
          _ = n ^ j := by group
      rw [this, pow_succ']
  have := key 5
  rw [hf5] at this
  simpa [commutatorElement_def] using this.symm

theorem exists_central_mod {G : Type*} [Group G] [Finite G] {Q W : Subgroup G} (hQ : IsPGroup 2 Q)
    (hWQ : W ≤ Q) (hW : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W) (hne : W ≠ Q) :
    ∃ m ∈ Q, m ∉ W ∧ ∀ q ∈ Q, ⁅m, q⁆ ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥Q := W.subgroupOf Q with hN
  have hNn : N.Normal := ⟨fun n hn q => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hW q q.2 n hn⟩
  have hp : IsPGroup 2 (↥Q ⧸ N) := hQ.to_quotient N
  have hnil : Group.IsNilpotent (↥Q ⧸ N) := hp.isNilpotent
  obtain ⟨x, hxQ, hxW⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hWQ hne)
  have : Nontrivial (↥Q ⧸ N) := ⟨⟨QuotientGroup.mk ⟨x, hxQ⟩, 1, by
    intro h
    have := (QuotientGroup.eq_one_iff (N := N) (⟨x, hxQ⟩ : ↥Q)).mp h
    exact hxW this⟩⟩
  have hc : Subgroup.center (↥Q ⧸ N) ≠ ⊥ := Group.IsNilpotent.center_ne_bot _
  obtain ⟨⟨c, hc1⟩, hc2⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hc
  obtain ⟨c0, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨(c0 : G), c0.2, fun hW0 => hc2 ?_, fun q hq => ?_⟩
  · apply Subtype.ext
    exact (QuotientGroup.eq_one_iff c0).mpr hW0
  · have hcomm : ⁅(QuotientGroup.mk c0 : ↥Q ⧸ N), (QuotientGroup.mk ⟨q, hq⟩ : ↥Q ⧸ N)⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact ((Subgroup.mem_center_iff.mp hc1) _).symm
    have h2 : (QuotientGroup.mk' N) ⁅c0, ⟨q, hq⟩⁆ = 1 := by
      rw [map_commutatorElement]; exact hcomm
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)

end CentMod

section Step1

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

def PN2 (L1 L2 S : Subgroup G) (W : Subgroup G) : Prop :=
  ∀ p ∈ P2 L1 L2 S, ∀ w ∈ W, p * w * p⁻¹ ∈ W

theorem exists_phi_Q1_surj (F : Frame L1 L2 S D X) :
    ∃ φ : ↥(P2 L1 L2 S) →* Alt5, Function.Surjective φ ∧
      (∀ p : ↥(P2 L1 L2 S), φ p = 1 ↔ (p : G) ∈ Q2 L1 L2 S) ∧
      ∃ T : Subgroup Alt5, Nat.card T = 4 ∧
        (∀ k ∈ T, ∃ q : ↥(P2 L1 L2 S), (q : G) ∈ Q1 L1 L2 S ∧ φ q = k) ∧
        ∀ p : ↥(P2 L1 L2 S),
          φ p ∈ Subgroup.normalizer (T : Set Alt5) ↔ (p : G) ∈ bigB L1 L2 S := by
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_P2 F
  obtain ⟨T, hT, hlift, hN⟩ := exists_klein_phi F hφs hφk
  exact ⟨φ, hφs, hφk, T, hT, hlift, hN⟩

variable (F : Frame L1 L2 S D X)
include F

theorem claimB (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S) (hgB : g ∉ bigB L1 L2 S)
    (hnot : NotLe L1 L2 S g) {W W' : Subgroup G}
    (hWn : PN2 L1 L2 S W) (hZW : Z2q L1 L2 S ≤ W) (hW'Q : W' ≤ Q2 L1 L2 S)
    (hcomm : ∀ m ∈ W', ∀ q ∈ Q2 L1 L2 S, ⁅m, q⁆ ∈ W) :
    ∀ k ∈ Q1 L1 L2 S ⊓ W', ∀ s ∈ S, ⁅k, s⁆ ∈ W := by
  have hA : ∀ a ∈ S, ∀ w ∈ W, a * w * a⁻¹ ∈ W := fun a ha => hWn a (S_le_P2 F ha)
  set B' := centMod S (Q1 L1 L2 S ⊓ W') W hA with hB'
  have hmem : ∀ s ∈ S, s ∈ B' := by
    intro s hs
    obtain ⟨z, hz, q, hq, rfl⟩ := S_eq_mul F h hg hgB hnot s hs
    refine B'.mul_mem ?_ ?_
    · refine ⟨conjZ2q_le_S F hg hz, fun t ht => ?_⟩
      have ht' : t ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S := ⟨ht.1, hW'Q ht.2⟩
      have := comm_Q1Q2_conjZ F h hg hgB hnot t ht' z hz
      rw [← commutatorElement_inv]
      exact W.inv_mem (hZW (Z_le_Z2q this))
    · refine ⟨F.Q2_le_S hq, fun t ht => ?_⟩
      rw [← commutatorElement_inv]
      exact W.inv_mem (hcomm t ht.2 q hq)
  intro k hk s hs
  have := (hmem s hs).2 k hk
  rw [← commutatorElement_inv]
  exact W.inv_mem this

theorem exists_central_class (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hgB : g ∉ bigB L1 L2 S) (hnot : NotLe L1 L2 S g)
    {W W' : Subgroup G} (hWn : PN2 L1 L2 S W) (hW'n : PN2 L1 L2 S W') (hWW' : W ≤ W')
    (hZW : Z2q L1 L2 S ≤ W) (hW'Q : W' ≤ Q2 L1 L2 S) (hne : W ≠ W')
    (hcomm : ∀ m ∈ W', ∀ q ∈ Q2 L1 L2 S, ⁅m, q⁆ ∈ W) :
    ∃ c ∈ W', c ∉ W ∧ ∀ p ∈ P2 L1 L2 S, ⁅c, p⁆ ∈ W := by
  obtain ⟨φ, hφs, hφk, T, hT4, hlift, hN⟩ := exists_phi_Q1_surj F
  have hWQ : W ≤ Q2 L1 L2 S := hWW'.trans hW'Q
  have hB := claimB F h hg hgB hnot hWn hZW hW'Q hcomm
  have hnormOf : ∀ V : Subgroup G, PN2 L1 L2 S V → (V.subgroupOf (P2 L1 L2 S)).Normal := by
    intro V hV
    exact ⟨fun n hn p => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hV p p.2 n hn⟩
  have hWnorm : (W.subgroupOf (P2 L1 L2 S)).Normal := hnormOf W hWn
  have hW'norm : (W'.subgroupOf (P2 L1 L2 S)).Normal := hnormOf W' hW'n
  set N : Subgroup ↥(P2 L1 L2 S) := W.subgroupOf (P2 L1 L2 S) with hN'
  set π : ↥(P2 L1 L2 S) →* ↥(P2 L1 L2 S) ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hπ1 : ∀ x : ↥(P2 L1 L2 S), π x = 1 ↔ (x : G) ∈ W := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; rfl
  have hNle : N ≤ φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker, hφk]
    exact hWQ hn
  set φ' : (↥(P2 L1 L2 S) ⧸ N) →* Alt5 := QuotientGroup.lift N φ hNle with hφ'
  have hφ'π : ∀ x : ↥(P2 L1 L2 S), φ' (π x) = φ x := fun x => rfl
  have hφ's : Function.Surjective φ' := by
    intro k
    obtain ⟨x, rfl⟩ := hφs k
    exact ⟨π x, hφ'π x⟩
  set A : Subgroup (↥(P2 L1 L2 S) ⧸ N) := (W'.subgroupOf (P2 L1 L2 S)).map π with hA
  have : A.Normal := Subgroup.Normal.map hW'norm π hπs
  set K : Subgroup (↥(P2 L1 L2 S) ⧸ N) := ((Q1 L1 L2 S ⊓ W').subgroupOf (P2 L1 L2 S)).map π with hK
  set Ŝ : Subgroup (↥(P2 L1 L2 S) ⧸ N) := (S.subgroupOf (P2 L1 L2 S)).map π with hŜ
  obtain ⟨c0, hc0W', hc0W⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hWW' hne)
  have hc0P : c0 ∈ (P2 L1 L2 S) := S_le_P2 F (F.Q2_le_S (hW'Q hc0W'))
  have hA1 : A ≠ ⊥ := by
    intro hbot
    have : π ⟨c0, hc0P⟩ ∈ A := ⟨⟨c0, hc0P⟩, hc0W', rfl⟩
    rw [hbot, Subgroup.mem_bot, hπ1] at this
    exact hc0W this
  have hAQ : ∀ a ∈ A, ∀ q ∈ φ'.ker, a * q = q * a := by
    rintro _ ⟨a0, ha0, rfl⟩ q hq
    obtain ⟨q0, rfl⟩ := hπs q
    have hq0 : (q0 : G) ∈ Q2 L1 L2 S := by
      rw [← hφk, ← hφ'π]; exact hq
    have h1 : ⁅a0, q0⁆ ∈ N := hcomm a0 ha0 q0 hq0
    have : ⁅π a0, π q0⁆ = 1 := by rw [← map_commutatorElement, hπ1]; exact h1
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  obtain ⟨d, hd, hd1⟩ := F.exists_ne_one_D
  have hdP : d ∈ (P2 L1 L2 S) := (le_sup_left : L2 ≤ P2 L1 L2 S) (F.D_le hd)
  have hd3 : d ^ 3 = 1 := pow_three_of_mem_D F hd
  have hr3 : (π ⟨d, hdP⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdP⟩ : ↥(P2 L1 L2 S)) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have hdQ : d ∉ Q2 L1 L2 S := by
    intro hdQ
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (P2 L1 L2 S) ⟨d, hdQ⟩
    have hk' : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hg3 : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hk', hd3⟩
    rw [hg3, pow_one] at this
    exact hd1 this
  have hr1 : φ' (π ⟨d, hdP⟩) ≠ 1 := by
    rw [hφ'π]
    intro h1
    exact hdQ ((hφk _).mp h1)
  have hrT : φ' (π ⟨d, hdP⟩) ∈ Subgroup.normalizer (T : Set Alt5) := by
    rw [hφ'π]
    exact (hN _).mpr (F.D_le_B hd)
  have hS : ∀ k ∈ T, ∃ s ∈ Ŝ, φ' s = k := by
    intro k hk
    obtain ⟨q, hqQ1, hφq⟩ := hlift k hk
    exact ⟨π q, ⟨q, F.Q1_le_S hqQ1, rfl⟩, by rw [hφ'π]; exact hφq⟩
  have hiii : ∀ a ∈ A, ⁅a, π ⟨d, hdP⟩⁆ ∈ K := by
    rintro _ ⟨a0, ha0, rfl⟩
    refine ⟨⁅a0, ⟨d, hdP⟩⁆, ?_, by rw [map_commutatorElement]⟩
    have ha0S : (a0 : G) ∈ S := F.Q2_le_S (hW'Q ha0)
    have h1 : d * (a0 : G) * d⁻¹ * (a0 : G)⁻¹ ∈ Q1 L1 L2 S := comm_D_S_mem_Q1 F hd ha0S
    have e : ((⁅a0, ⟨d, hdP⟩⁆ : ↥(P2 L1 L2 S)) : G) = ⁅(a0 : G), d⁆ := rfl
    show ⁅a0, ⟨d, hdP⟩⁆ ∈ (Q1 L1 L2 S ⊓ W').subgroupOf (P2 L1 L2 S)
    rw [Subgroup.mem_subgroupOf, e]
    refine ⟨?_, ?_⟩
    · have : ⁅(a0 : G), d⁆ = (d * (a0 : G) * d⁻¹ * (a0 : G)⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [this]; exact (Q1 L1 L2 S).inv_mem h1
    · have : ⁅(a0 : G), d⁆ = (a0 : G) * (d * (a0 : G)⁻¹ * d⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact W'.mul_mem ha0 (hW'n d hdP _ (W'.inv_mem ha0))
  have hiv : ∀ x ∈ A, x ∈ K → ∀ s ∈ Ŝ, x * s = s * x := by
    rintro _ _ ⟨k0, hk0, rfl⟩ _ ⟨s0, hs0, rfl⟩
    have h1 : ⁅k0, s0⁆ ∈ N := hB k0 hk0 s0 hs0
    have : ⁅π k0, π s0⁆ = 1 := by rw [← map_commutatorElement, hπ1]; exact h1
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  obtain ⟨m, ⟨a0, ha0, rfl⟩, hm1, hmc⟩ := exists_central_of_acts_trivially φ' hφ's hA1 hAQ hr3
    hr1 hT4 hrT hS hiii hiv
  refine ⟨(a0 : G), ha0, fun hW0 => hm1 ((hπ1 a0).mpr hW0), fun p hp => ?_⟩
  have := hmc (π ⟨p, hp⟩)
  have h2 : ⁅π a0, π ⟨p, hp⟩⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr this
  rw [← map_commutatorElement, hπ1] at h2
  exact h2

theorem stab_step {W W₁ : Subgroup G} (hWQ : W ≤ Q2 L1 L2 S) (hW₁Q : W₁ ≤ Q2 L1 L2 S)
    (hP : ∀ f ∈ P2 L1 L2 S, f ^ 5 = 1 → ∀ w ∈ W, ⁅w, f⁆ ∈ Z2q L1 L2 S)
    (hW₁ : ∀ m ∈ W₁, ∀ p ∈ P2 L1 L2 S, ⁅m, p⁆ ∈ W) :
    ∀ f ∈ P2 L1 L2 S, f ^ 5 = 1 → ∀ m ∈ W₁, ⁅m, f⁆ ∈ Z2q L1 L2 S := by
  intro f hf hf5 m hm
  have hmP : m ∈ P2 L1 L2 S := pCoreOf_le 2 (P2 L1 L2 S) (hW₁Q hm)
  have hZn : (Z2q L1 L2 S).subgroupOf (P2 L1 L2 S) |>.Normal := ⟨fun n hn p => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using Z2q_normal p.2 hn⟩
  set N : Subgroup ↥(P2 L1 L2 S) := (Z2q L1 L2 S).subgroupOf (P2 L1 L2 S) with hN
  set π : ↥(P2 L1 L2 S) →* ↥(P2 L1 L2 S) ⧸ N := QuotientGroup.mk' N with hπ
  have hπ1 : ∀ x : ↥(P2 L1 L2 S), π x = 1 ↔ (x : G) ∈ Z2q L1 L2 S := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; rfl
  set m' : ↥(P2 L1 L2 S) := ⟨m, hmP⟩ with hm'
  set f' : ↥(P2 L1 L2 S) := ⟨f, hf⟩ with hf'
  have hn : ⁅m, f⁆ ∈ W := hW₁ m hm f hf
  have hcomm : ⁅⁅π m', π f'⁆, π f'⁆ = 1 := by
    rw [← map_commutatorElement, ← map_commutatorElement, hπ1]
    exact hP f hf hf5 _ hn
  have hf5' : (π f') ^ 5 = 1 := by
    rw [← map_pow]
    have : f' ^ 5 = 1 := Subtype.ext (by simpa using hf5)
    rw [this, map_one]
  have h5 := five_stab hf5' hcomm
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (P2 L1 L2 S) ⟨⁅m, f⁆, hWQ hn⟩
  have hk' : ⁅m, f⁆ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hk'' : (π ⁅m', f'⁆) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : ⁅m', f'⁆ ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk')
    rw [this, map_one]
  have h5' : (π ⁅m', f'⁆) ^ 5 = 1 := by rw [map_commutatorElement]; exact h5
  have hg : Nat.gcd 5 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  have := pow_gcd_eq_one.mpr ⟨h5', hk''⟩
  rw [hg, pow_one] at this
  exact (hπ1 ⁅m', f'⁆).mp this

theorem step1_extend (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hgB : g ∉ bigB L1 L2 S) (hnot : NotLe L1 L2 S g)
    {W : Subgroup G} (hWn : PN2 L1 L2 S W) (hZW : Z2q L1 L2 S ≤ W) (hWQ : W ≤ Q2 L1 L2 S)
    (hne : W ≠ Q2 L1 L2 S) :
    ∃ W₁ : Subgroup G, PN2 L1 L2 S W₁ ∧ W ≤ W₁ ∧ W₁ ≤ Q2 L1 L2 S ∧ W ≠ W₁ ∧
      ∀ m ∈ W₁, ∀ p ∈ P2 L1 L2 S, ⁅m, p⁆ ∈ W := by
  have hQP : Q2 L1 L2 S ≤ P2 L1 L2 S := pCoreOf_le 2 _
  have hA₁ : ∀ a ∈ Q2 L1 L2 S, ∀ w ∈ W, a * w * a⁻¹ ∈ W := fun a ha => hWn a (hQP ha)
  set W' : Subgroup G := centMod (Q2 L1 L2 S) (Q2 L1 L2 S) W hA₁ with hW'
  have hW'Q : W' ≤ Q2 L1 L2 S := fun m hm => hm.1
  have hW'n : PN2 L1 L2 S W' := by
    intro p hp m hm
    have hpQ : p * m * p⁻¹ ∈ Q2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (P2_le_normalizer_Q2 L1 L2 S hp) m).mp (hW'Q hm)
    refine ⟨hpQ, fun q hq => ?_⟩
    have hq' : p⁻¹ * q * p ∈ Q2 L1 L2 S := by
      have := (Subgroup.mem_normalizer_iff.mp
        (P2_le_normalizer_Q2 L1 L2 S ((P2 L1 L2 S).inv_mem hp)) q).mp hq
      simpa using this
    have e : ⁅p * m * p⁻¹, q⁆ = p * ⁅m, p⁻¹ * q * p⁆ * p⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hWn p hp _ (hm.2 _ hq')
  have hWW' : W ≤ W' := fun w hw => ⟨hWQ hw, fun q hq => by
    have e : ⁅w, q⁆ = w * (q * w⁻¹ * q⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem hw (hA₁ q hq _ (W.inv_mem hw))⟩
  have hcomm : ∀ m ∈ W', ∀ q ∈ Q2 L1 L2 S, ⁅m, q⁆ ∈ W := fun m hm q hq => hm.2 q hq
  have hne' : W ≠ W' := by
    intro heq
    obtain ⟨m, hmQ, hmW, hmc⟩ := exists_central_mod (pCoreOf_isPGroup 2 (P2 L1 L2 S)) hWQ hA₁ hne
    exact hmW (heq ▸ ⟨hmQ, hmc⟩)
  obtain ⟨c, hcW', hcW, hcP⟩ := exists_central_class F h hg hgB hnot hWn hW'n hWW' hZW hW'Q hne' hcomm
  have hA₂ : ∀ a ∈ W', ∀ w ∈ W, a * w * a⁻¹ ∈ W := fun a ha => hA₁ a (hW'Q ha)
  set W₁ : Subgroup G := centMod W' (P2 L1 L2 S) W hA₂ with hW₁
  refine ⟨W₁, ?_, ?_, fun m hm => hW'Q hm.1, ?_, fun m hm p hp => hm.2 p hp⟩
  · intro p hp m hm
    refine ⟨hW'n p hp m hm.1, fun t ht => ?_⟩
    have e : ⁅p * m * p⁻¹, t⁆ = p * ⁅m, p⁻¹ * t * p⁆ * p⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have ht' : p⁻¹ * t * p ∈ P2 L1 L2 S :=
      (P2 L1 L2 S).mul_mem ((P2 L1 L2 S).mul_mem ((P2 L1 L2 S).inv_mem hp) ht) hp
    exact hWn p hp _ (hm.2 _ ht')
  · intro w hw
    refine ⟨hWW' hw, fun t ht => ?_⟩
    have e : ⁅w, t⁆ = w * (t * w⁻¹ * t⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem hw (hWn t ht _ (W.inv_mem hw))
  · intro heq
    exact hcW (heq ▸ (⟨hcW', hcP⟩ : c ∈ W₁))

theorem step1_main (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hgB : g ∉ bigB L1 L2 S) (hnot : NotLe L1 L2 S g) :
    ∀ f ∈ P2 L1 L2 S, f ^ 5 = 1 → ∀ w ∈ Q2 L1 L2 S, ⁅w, f⁆ ∈ Z2q L1 L2 S := by
  set 𝒮 : Set (Subgroup G) := {W | PN2 L1 L2 S W ∧ Z2q L1 L2 S ≤ W ∧ W ≤ Q2 L1 L2 S ∧
    ∀ f ∈ P2 L1 L2 S, f ^ 5 = 1 → ∀ w ∈ W, ⁅w, f⁆ ∈ Z2q L1 L2 S} with h𝒮
  have hZ : Z2q L1 L2 S ∈ 𝒮 := by
    refine ⟨fun p hp w hw => Z2q_normal hp hw, le_rfl, Z2q_le_Q2 F, fun f hf _ w hw => ?_⟩
    have e : ⁅w, f⁆ = w * (f * w⁻¹ * f⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Z2q L1 L2 S).mul_mem hw (Z2q_normal hf ((Z2q L1 L2 S).inv_mem hw))
  obtain ⟨W, hW⟩ := Set.Finite.exists_maximal (Set.toFinite 𝒮) ⟨_, hZ⟩
  obtain ⟨hWn, hZW, hWQ, hWP⟩ := hW.prop
  have hWeq : W = Q2 L1 L2 S := by
    by_contra hne
    obtain ⟨W₁, hW₁n, hWW₁, hW₁Q, hWne, hW₁⟩ := step1_extend F h hg hgB hnot hWn hZW hWQ hne
    have hW₁𝒮 : W₁ ∈ 𝒮 := ⟨hW₁n, hZW.trans hWW₁, hW₁Q, stab_step F hWQ hW₁Q hWP hW₁⟩
    exact hWne (le_antisymm hWW₁ (hW.2 hW₁𝒮 hWW₁))
  intro f hf hf5 w hw
  exact hWP f hf hf5 w (hWeq ▸ hw)

end Step1

end CFSG.Quasithin.Kleidman.F204
