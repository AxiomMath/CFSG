module

public import CFSG.Quasithin.Recognition.Stroth.Str86XOne3
public import CFSG.Quasithin.Recognition.Stroth.BenderCaseIIFacts
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem str86_vU3Big_of_stated {L1 : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    VU3Big L1 :=
  ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩

theorem str86_sup_s_eq_q1 {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F]
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    L1 ⊔ S = L1 ⊔ Q1 L1 L2 S :=
  sup_eq_of_S_eq (eq_sup_pCoreOf_of_bender_left hF.1 hSB
    (Or.inr (Or.inl (str86_vU3Big_of_stated hk hFc hU3))))

theorem str86_pCoreOf_sup_s_eq_q1 {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F]
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
  rw [str86_sup_s_eq_q1 hF hSB hk hFc hU3]
  exact pCoreOf_sup_pCoreOf hF.1

theorem str86_sup_normalizes_z1 {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F]
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
  rw [str86_sup_s_eq_q1 hF hSB hk hFc hU3]
  refine sup_le ?_ ?_
  · exact (le_sup_left : L1 ≤ P1 L1 L2 S).trans
      ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
        (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
  · exact (Q1_le_centralizer_Z1 L1 L2 S).trans
      (Subgroup.centralizer_le_normalizer (Z1 L1 L2 S : Set G))

theorem str86_centralizer_z1_sup_eq_bot
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G)) :
    Z1 L1 L2 S ⊓ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) = ⊥ := by
  classical
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := str86_sup_s_eq_q1 hF hSB hk hFc hU3
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzZ1, hzC⟩ := Subgroup.mem_inf.mp hz
  have hzQ1 : z ∈ Q1 L1 L2 S := omegaOneCenterOf_le (Q1 L1 L2 S) hzZ1
  have hzS : z ∈ S := hQ1S hzQ1
  have hz2 : z ^ 2 = 1 :=
    (SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)).2 z hzZ1
  have hzsq : z * z = 1 := by simpa [pow_two] using hz2
  have hzCS : z ∈ Subgroup.centralizer (S : Set G) :=
    Subgroup.centralizer_le (le_sup_right : S ≤ L1 ⊔ S) hzC
  have hzCQ2 : z ∈ Subgroup.centralizer (Q2 L1 L2 S : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hzCS ⊢
    intro q hq
    exact hzCS q (hQ2S hq)
  have hzQ2 : z ∈ Q2 L1 L2 S :=
    inf_centralizer_pCoreOf_right_of_hyp111 hF.1
      (Subgroup.mem_inf.mpr ⟨(le_sup_right : S ≤ L2 ⊔ S) hzS, hzCQ2⟩)
  have hzZ2 : z ∈ Z2 L1 L2 S :=
    Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hzQ2, hzCQ2⟩, hz2⟩
  have hzC1 : z ∈ Subgroup.centralizer (L1 : Set G) :=
    Subgroup.centralizer_le (le_sup_left : L1 ≤ L1 ⊔ S) hzC
  have hzC2 : z ∈ Subgroup.centralizer (L2 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp
      (hIIa ((le_sup_left : L2 ≤ L2 ⊔ Q2 L1 L2 S) hl)) z hzZ2).symm
  have hzG0C : z ∈ Subgroup.centralizer ((L1 ⊔ L2 ⊔ S : Subgroup G) : Set G) := by
    have h12 : Subgroup.zpowers z ≤ Subgroup.centralizer ((L1 ⊔ L2 : Subgroup G) : Set G) :=
      CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
        (Subgroup.zpowers_le.mpr hzC1) (Subgroup.zpowers_le.mpr hzC2)
    have h123 : Subgroup.zpowers z ≤
        Subgroup.centralizer ((L1 ⊔ L2 ⊔ S : Subgroup G) : Set G) :=
      CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers h12
        (Subgroup.zpowers_le.mpr hzCS)
    exact Subgroup.zpowers_le.mp h123
  have hzG0 : z ∈ L1 ⊔ L2 ⊔ S :=
    (le_sup_right : S ≤ L1 ⊔ L2 ⊔ S) hzS
  have hconj : ∀ (u : G), u * z = z * u → ∀ k : ℤ, u * z ^ k * u⁻¹ = z ^ k := by
    intro u hu k
    have hu' : u * z * u⁻¹ = z := by rw [hu]; group
    calc u * z ^ k * u⁻¹ = (MulAut.conj u) (z ^ k) := rfl
      _ = ((MulAut.conj u) z) ^ k := map_zpow _ _ _
      _ = z ^ k := by rw [MulAut.conj_apply, hu']
  have hnorm : (L1 ⊔ L2 ⊔ S : Subgroup G) ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    intro x hx
    have hxz : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hzG0C) x hx
    have hxz' : x⁻¹ * z = z * x⁻¹ := by
      have h := congrArg (fun t => x⁻¹ * t * x⁻¹) hxz
      simpa [mul_assoc] using h.symm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [hconj x hxz j]
      exact Subgroup.zpow_mem_zpowers z j
    · intro hy
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h1 : y = x⁻¹ * z ^ j * x := by
        rw [hj]
        group
      rw [h1, show x⁻¹ * z ^ j * x = z ^ j from by simpa using hconj x⁻¹ hxz' j]
      exact Subgroup.zpow_mem_zpowers z j
  have h2 : IsPGroup 2 (Subgroup.zpowers z) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by_cases hz1 : z = 1
    · rw [hz1, Subgroup.zpowers_one_eq_bot]
      exact IsPGroup.of_bot
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]
  have hzO : z ∈ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    le_pCoreOf_of_le_normalizer (Subgroup.zpowers_le.mpr hzG0) hnorm h2
      (Subgroup.mem_zpowers z)
  rw [hF.1.o2] at hzO
  simpa using hzO

theorem str86_isSzU3Quot_sup {L1 L2 S : Subgroup G} {k : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) {F : Type} [Field F] [Finite F]
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) := by
  have hVU3 : VU3Big L1 := str86_vU3Big_of_stated hk hFc hU3
  have hmain : Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* StatedProj (StatedSU 3 (2 ^ k) F)) := by
    rw [show (L1 ⊔ S : Subgroup G) = u3LS L1 L2 S from rfl]
    exact u3HQU3 hF hSB hU3 hVU3
  rcases hmain with h | h
  · obtain ⟨e⟩ := h
    exact IsSzU3Quot.of_mulEquiv e
      (Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, Or.inl ⟨MulEquiv.refl _⟩⟩)
  · obtain ⟨e⟩ := h
    exact IsSzU3Quot.of_mulEquiv e
      (Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, Or.inr ⟨MulEquiv.refl _⟩⟩)

@[expose] def Str86AtomIn (H U N : Subgroup G) : Prop :=
  IsNormalIn H U N ∧ N ≠ ⊥ ∧
    ∀ M : Subgroup G, IsNormalIn H U M → M ≠ ⊥ → M ≤ N → M = N

theorem Str86AtomIn.isChiefStep_bot {H U N : Subgroup G} (h : Str86AtomIn H U N) :
    IsChiefStep H U ⊥ N := by
  refine ⟨h.1, D15Proof.isNormalIn_bot H U, bot_lt_iff_ne_bot.mpr h.2.1, ?_⟩
  intro K hK _ hKN
  by_cases hKbot : K = ⊥
  · exact Or.inl hKbot
  · exact Or.inr (h.2.2 K hK hKbot hKN)

theorem Str86AtomIn.not_isCentralStep_bot {H U N : Subgroup G} (h : Str86AtomIn H U N)
    (hC : U ⊓ Subgroup.centralizer (H : Set G) = ⊥) :
    ¬ IsCentralStep H ⊥ N := by
  intro hcent
  have hNleC : N ≤ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : g * x * g⁻¹ * x⁻¹ = 1 := by
      have := hcent g hg x hx
      simpa using this
    calc x * g = (g * x * g⁻¹ * x⁻¹) * (x * g) := by rw [h1, one_mul]
      _ = g * x := by group
  apply h.2.1
  have hle : N ≤ U ⊓ Subgroup.centralizer (H : Set G) := le_inf h.1.1 hNleC
  rw [hC] at hle
  exact le_bot_iff.mp hle

theorem str86_z1_le_sup {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) :
    Z1 L1 L2 S ≤ L1 ⊔ S :=
  ((omegaOneCenterOf_le (Q1 L1 L2 S)).trans
    (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW))).trans
    (le_sup_right : S ≤ L1 ⊔ S)

theorem str86_exists_atom {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {k : ℕ} {F : Type} [Field F] [Finite F]
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    ∃ N : Subgroup G, Str86AtomIn (L1 ⊔ S) (Z1 L1 L2 S) N := by
  classical
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    str86_sup_normalizes_z1 hF hSB hk hFc hU3
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    intro hbot
    refine hII ?_
    rw [hbot, show Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ from by simp]
    exact le_top
  have hZ1normal : IsNormalIn (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) :=
    F112W.isNormalIn_of_le_normalizer le_rfl hHZ1
  obtain ⟨N, hN⟩ := (Set.toFinite
    {M : Subgroup G | IsNormalIn (L1 ⊔ S) (Z1 L1 L2 S) M ∧ M ≠ ⊥}).exists_minimal
    ⟨Z1 L1 L2 S, hZ1normal, hZ1ne⟩
  exact ⟨N, hN.1.1, hN.1.2, fun _ hM hMne hMN => le_antisymm hMN (hN.2 ⟨hM, hMne⟩ hMN)⟩

theorem str86_atom_unique {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hC : Z1 L1 L2 S ⊓ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) = ⊥)
    (hc1 : IsChiefSeriesFrom (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) 1)
    {N1 N2 : Subgroup G} (h1 : Str86AtomIn (L1 ⊔ S) (Z1 L1 L2 S) N1)
    (h2 : Str86AtomIn (L1 ⊔ S) (Z1 L1 L2 S) N2) : N1 = N2 := by
  classical
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    str86_sup_normalizes_z1 hF hSB hk hFc hU3
  have hZ1H : Z1 L1 L2 S ≤ L1 ⊔ S := str86_z1_le_sup hF
  by_contra hne
  have hinf : N1 ⊓ N2 = ⊥ := by
    by_cases hM : N1 ⊓ N2 = ⊥
    · exact hM
    · have hEq : N1 ⊓ N2 = N2 :=
        h2.2.2 (N1 ⊓ N2) (F112W.isNormalIn_inf h1.1 h2.1) hM inf_le_right
      have hN2le : N2 ≤ N1 := hEq ▸ inf_le_left
      exact absurd ((h1.2.2 N2 h2.1 h2.2.1 hN2le).symm) hne
  have hsupN : IsNormalIn (L1 ⊔ S) (Z1 L1 L2 S) (N1 ⊔ N2) :=
    F112W.isNormalIn_sup h1.1 h2.1
  have hN1lt : N1 < N1 ⊔ N2 := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    have hN2le : N2 ≤ N1 := heq ▸ le_sup_right
    exact hne (h1.2.2 N2 h2.1 h2.2.1 hN2le).symm
  have hstepSup : IsChiefStep (L1 ⊔ S) (Z1 L1 L2 S) N1 (N1 ⊔ N2) := by
    refine ⟨hsupN, h1.1, hN1lt, ?_⟩
    intro K hK hN1K hKsup
    by_cases hK2 : K ⊓ N2 = ⊥
    ·
      left
      refine le_antisymm ?_ hN1K
      intro x hxK
      have hxZ : x ∈ N1 ⊔ N2 := hKsup hxK
      let Z : Subgroup G := N1 ⊔ N2
      have hZea : IsElemAbelian 2 Z :=
        (SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)).mono
          (sup_le h1.1.1 h2.1.1)
      letI : CommGroup ↥Z := commGroupOfElemAbelian hZea
      have htop : (N1.subgroupOf Z) ⊔ (N2.subgroupOf Z) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup (le_sup_left : N1 ≤ Z) (le_sup_right : N2 ≤ Z),
          Subgroup.subgroupOf_self]
      have hxmem : (⟨x, hxZ⟩ : ↥Z) ∈ (N1.subgroupOf Z) ⊔ (N2.subgroupOf Z) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hxmem
      have hyN1 : (y : G) ∈ N1 := Subgroup.mem_subgroupOf.mp hy
      have hzN2 : (z : G) ∈ N2 := Subgroup.mem_subgroupOf.mp hz
      have hyK : (y : G) ∈ K := hN1K hyN1
      have hval : (y : G) * (z : G) = x := congrArg Subtype.val hyz
      have hzeq : (z : G) = (y : G)⁻¹ * x := by
        rw [← hval]
        group
      have hzK : (z : G) ∈ K := by
        rw [hzeq]
        exact K.mul_mem (K.inv_mem hyK) hxK
      have hzBot : (z : G) ∈ (⊥ : Subgroup G) := by
        rw [← hK2]
        exact Subgroup.mem_inf.mpr ⟨hzK, hzN2⟩
      have hz1 : (z : G) = 1 := Subgroup.mem_bot.mp hzBot
      have hxy : (y : G) = x := by
        rw [hz1, mul_one] at hval
        exact hval
      rw [← hxy]
      exact hyN1
    ·
      right
      have hK2eq : K ⊓ N2 = N2 := h2.2.2 (K ⊓ N2) (F112W.isNormalIn_inf hK h2.1) hK2 inf_le_right
      exact le_antisymm hKsup (sup_le hN1K (hK2eq.symm ▸ inf_le_left))
  have hncSup : ¬ IsCentralStep (L1 ⊔ S) N1 (N1 ⊔ N2) := by
    intro hcent
    exact h2.not_isCentralStep_bot hC (by
      intro g hg x hx
      have h1' : g * x * g⁻¹ * x⁻¹ ∈ N1 := hcent g hg x (Subgroup.mem_sup_right hx)
      have h2' : g * x * g⁻¹ * x⁻¹ ∈ N2 :=
        N2.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (D14.le_normalizer_of_isNormalIn h2.1 hg) x).mp hx)
          (N2.inv_mem hx)
      have := Subgroup.mem_inf.mpr ⟨h1', h2'⟩
      rw [hinf] at this
      simpa using this)
  have hZ1normal : IsNormalIn (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) :=
    F112W.isNormalIn_of_le_normalizer le_rfl hHZ1
  have hstep1 : IsChiefStep (L1 ⊔ S) (Z1 L1 L2 S) ⊥ N1 := h1.isChiefStep_bot
  have hnc1 : ¬ IsCentralStep (L1 ⊔ S) ⊥ N1 := h1.not_isCentralStep_bot hC
  have hserN1 : IsChiefSeriesFrom (L1 ⊔ S) (Z1 L1 L2 S) N1 1 :=
    IsChiefSeriesFrom.noncentral hstep1 hnc1 IsChiefSeriesFrom.bot
  have hetaN1 : F112W.eta (L1 ⊔ S) (Z1 L1 L2 S) N1 = 1 :=
    (F112W.isChiefSeriesFrom_iff_eta hZ1H h1.1).mp hserN1
  have hbetween : F112W.IsChiefSeriesBetween (L1 ⊔ S) (Z1 L1 L2 S) N1 (N1 ⊔ N2) 1 :=
    F112W.IsChiefSeriesBetween.noncentral hstepSup hncSup F112W.IsChiefSeriesBetween.refl
  have hetaSup : F112W.eta (L1 ⊔ S) (Z1 L1 L2 S) (N1 ⊔ N2) =
      F112W.eta (L1 ⊔ S) (Z1 L1 L2 S) N1 + 1 :=
    F112W.eta_eq_add hZ1H h1.1 hbetween
  have hetaZ1 : F112W.eta (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) = 1 :=
    (F112W.isChiefSeriesFrom_iff_eta hZ1H hZ1normal).mp hc1
  have hle : F112W.eta (L1 ⊔ S) (Z1 L1 L2 S) (N1 ⊔ N2) ≤
      F112W.eta (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) :=
    F112W.eta_le_of_le hZ1H hsupN hZ1normal (sup_le h1.1.1 h2.1.1)
  omega


private theorem str86_map_conj_isNormalIn {H U M : Subgroup G} {g : G}
    (hGH : g ∈ Subgroup.normalizer (H : Set G))
    (hGU : g ∈ Subgroup.normalizer (U : Set G))
    (hM : IsNormalIn H U M) :
    IsNormalIn H U (M.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · calc M.map (MulAut.conj g).toMonoidHom ≤ U.map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hM.1
      _ = U := Subgroup.mem_normalizer_iff_map_conj_eq.mp hGU
  · intro h hh x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    have hgH : g⁻¹ * h * g ∈ H := by
      have hinv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
        (Subgroup.normalizer (H : Set G)).inv_mem hGH
      simpa using (Subgroup.mem_normalizer_iff.mp hinv h).mp hh
    have hmid : (g⁻¹ * h * g) * m * (g⁻¹ * h * g)⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp ((D14.le_normalizer_of_isNormalIn hM) hgH) m).mp hm
    refine Subgroup.mem_map.mpr ⟨_, hmid, ?_⟩
    show g * ((g⁻¹ * h * g) * m * (g⁻¹ * h * g)⁻¹) * g⁻¹ = h * (g * m * g⁻¹) * h⁻¹
    group

theorem str86_atom_le_of_normal {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hC : Z1 L1 L2 S ⊓ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) = ⊥)
    (hc1 : IsChiefSeriesFrom (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) 1)
    {N : Subgroup G} (h1 : Str86AtomIn (L1 ⊔ S) (Z1 L1 L2 S) N)
    {W : Subgroup G} (hW : IsNormalIn (L1 ⊔ S) (Z1 L1 L2 S) W) (hWne : W ≠ ⊥) :
    N ≤ W := by
  classical
  obtain ⟨N0, hN0⟩ := (Set.toFinite
    {M : Subgroup G | IsNormalIn (L1 ⊔ S) (Z1 L1 L2 S) M ∧ M ≠ ⊥ ∧ M ≤ W}).exists_minimal
    ⟨W, hW, hWne, le_rfl⟩
  have hN0atom : Str86AtomIn (L1 ⊔ S) (Z1 L1 L2 S) N0 := by
    refine ⟨hN0.1.1, hN0.1.2.1, ?_⟩
    intro M hM hMne hMN
    exact le_antisymm hMN (hN0.2 ⟨hM, hMne, hMN.trans hN0.1.2.2⟩ hMN)
  rw [str86_atom_unique hF hSB hk hFc hU3 hC hc1 h1 hN0atom]
  exact hN0.1.2.2

theorem str86_atom_normalizer_P1 {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hC : Z1 L1 L2 S ⊓ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) = ⊥)
    (hc1 : IsChiefSeriesFrom (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) 1)
    {N : Subgroup G} (h1 : Str86AtomIn (L1 ⊔ S) (Z1 L1 L2 S) N) :
    P1 L1 L2 S ≤ Subgroup.normalizer (N : Set G) := by
  have hP1H : P1 L1 L2 S ≤ Subgroup.normalizer ((L1 ⊔ S : Subgroup G) : Set G) :=
    sup_le ((le_sup_left : L1 ≤ L1 ⊔ S).trans Subgroup.le_normalizer)
      (F1.le_normalizer_sup (bigB_le_normalizer_of_hyp111 hF.1) hSB)
  have hP1Z1 : P1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    refine sup_le ?_ ?_
    · exact (le_sup_left : L1 ≤ P1 L1 L2 S).trans
        ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
          (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
    · exact (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans
        ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
          (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
  intro g hg
  have hmapnorm : IsNormalIn (L1 ⊔ S) (Z1 L1 L2 S)
      (N.map (MulAut.conj g).toMonoidHom) :=
    str86_map_conj_isNormalIn (hP1H hg) (hP1Z1 hg) h1.1
  have hmapne : N.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
    intro hbot
    have hle : N ≤ (MulAut.conj g).toMonoidHom.ker := (Subgroup.map_eq_bot_iff N).mp hbot
    rw [(MonoidHom.ker_eq_bot_iff (MulAut.conj g).toMonoidHom).mpr
      (MulAut.conj g).injective] at hle
    exact h1.2.1 (le_bot_iff.mp hle)
  have hNle : N ≤ N.map (MulAut.conj g).toMonoidHom :=
    str86_atom_le_of_normal hF hSB hk hFc hU3 hC hc1 h1 hmapnorm hmapne
  have hcard : Nat.card ↥(N.map (MulAut.conj g).toMonoidHom) = Nat.card ↥N :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hNle (le_of_eq hcard)).symm


theorem str86_inf_centralizer_atom_eq_q1 {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hC : Z1 L1 L2 S ⊓ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) = ⊥)
    {N : Subgroup G} (h1 : Str86AtomIn (L1 ⊔ S) (Z1 L1 L2 S) N) :
    S ⊓ Subgroup.centralizer (N : Set G) = Q1 L1 L2 S := by
  classical
  have hpCoreH : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S :=
    str86_pCoreOf_sup_s_eq_q1 hF hSB hk hFc hU3
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ1H : Q1 L1 L2 S ≤ L1 ⊔ S := hQ1S.trans le_sup_right
  have hNS : N ≤ S := h1.1.1.trans (omegaOneCenterOf_le (Q1 L1 L2 S) |>.trans hQ1S)
  have hQ1N : Q1 L1 L2 S ≤ Subgroup.centralizer (N : Set G) :=
    Subgroup.le_centralizer_iff.mpr
      (h1.1.1.trans (Z1_le_centralizer_Q1 L1 L2 S))
  set K : Subgroup G := (L1 ⊔ S) ⊓ Subgroup.centralizer (N : Set G) with hKdef
  have hKH : K ≤ L1 ⊔ S := inf_le_left
  have hKcentralizer : L1 ⊔ S ≤ Subgroup.normalizer (Subgroup.centralizer (N : Set G) : Set G) :=
    (D14.le_normalizer_of_isNormalIn h1.1).trans
      (normalizer_le_normalizer_centralizer N)
  have hKnormal : L1 ⊔ S ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_inf (Subgroup.le_normalizer (H := L1 ⊔ S)) hKcentralizer
  have hQ1K : pCoreOf 2 (L1 ⊔ S) ≤ K := by
    rw [hpCoreH]
    exact le_inf hQ1H hQ1N
  have hKne : K ≠ L1 ⊔ S := by
    intro htop
    have hHcent : L1 ⊔ S ≤ Subgroup.centralizer (N : Set G) := htop ▸ inf_le_right
    have hNcent : N ≤ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mpr hHcent
    have hle : N ≤ Z1 L1 L2 S ⊓ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) :=
      le_inf h1.1.1 hNcent
    rw [hC] at hle
    exact h1.2.1 (le_bot_iff.mp hle)
  have hBender : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) :=
    str86_isSzU3Quot_sup hF hSB hk hFc hU3
  have hm4 := eq_or_mem_pCoreOf_of_normal hBender hKH hKnormal hQ1K
  rcases hm4 with htop | h2elem
  · exact absurd htop hKne
  · refine le_antisymm ?_ (le_inf hQ1S hQ1N)
    intro s hs
    obtain ⟨hsS, hsC⟩ := Subgroup.mem_inf.mp hs
    have hsK : s ∈ K := Subgroup.mem_inf.mpr ⟨(le_sup_right : S ≤ L1 ⊔ S) hsS, hsC⟩
    have hs2 : ∃ n : ℕ, s ^ (2 ^ n) = 1 := by
      obtain ⟨n, hn⟩ := (f112_isSylowTwoOf_P1 hF.toW).2.1 ⟨s, hsS⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    have := h2elem s hsK hs2
    rwa [hpCoreH] at this


end CFSG.Quasithin.Stroth
