module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoChain
public import CFSG.Quasithin.Recognition.Stroth.BenderQrcHyp
public import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
public import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv
public import CFSG.Quasithin.H13.A5W1618g
public import TauCeti.Algebra.Group.Coprime

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem eq_or_mem_pCoreOf_of_normal_of_isSimple {H K : Subgroup G}
    (hsim : IsSimpleGroup (oTwoQuot ↥H)) (hKH : K ≤ H)
    (hK : H ≤ Subgroup.normalizer (K : Set G)) (hQK : pCoreOf 2 H ≤ K) :
    K = H ∨ ∀ k ∈ K, (∃ n : ℕ, k ^ (2 ^ n) = 1) → k ∈ pCoreOf 2 H := by
  classical
  let Kq : Subgroup (oTwoQuot ↥H) :=
    (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))
  have hKnorm : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hK
  have hKqnorm : Kq.Normal :=
    Subgroup.Normal.map hKnorm _ (QuotientGroup.mk'_surjective _)
  rcases (haveI := hKqnorm; IsSimpleGroup.eq_bot_or_eq_top_of_normal Kq) with hbot | htop
  · right
    intro k hk hkpow
    obtain ⟨n, hn⟩ := hkpow
    have hkH : k ∈ H := hKH hk
    let z : oTwoQuot ↥H := QuotientGroup.mk' (pCore 2 ↥H) (⟨k, hkH⟩ : ↥H)
    have hzKq : z ∈ Kq :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
    rw [hbot] at hzKq
    have hz1 : z = 1 := Subgroup.mem_bot.mp hzKq
    have hkR : (⟨k, hkH⟩ : ↥H) ∈ pCore 2 ↥H := by
      rw [← QuotientGroup.eq_one_iff]
      exact hz1
    exact (CFSG.mem_openPCoreOf_iff (⟨k, hkH⟩ : ↥H)).mpr hkR
  · left
    refine le_antisymm hKH ?_
    intro x hx
    have hmem : QuotientGroup.mk' (pCore 2 ↥H) (⟨x, hx⟩ : ↥H) ∈ Kq := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
    have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
    have hdiff : (y : G)⁻¹ * x ∈ pCoreOf 2 H := by
      have h1 : (y⁻¹ * (⟨x, hx⟩ : ↥H) : ↥H) ∈ pCore 2 ↥H := by
        have hq : (QuotientGroup.mk' (pCore 2 ↥H)) (y⁻¹ * (⟨x, hx⟩ : ↥H)) = 1 := by
          rw [map_mul, map_inv, hyx, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff (N := pCore 2 ↥H)
          (x := y⁻¹ * (⟨x, hx⟩ : ↥H))).mp hq
      exact (CFSG.mem_openPCoreOf_iff (y⁻¹ * (⟨x, hx⟩ : ↥H))).mpr h1
    have hxeq : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [hxeq]
    exact K.mul_mem hyK (hQK hdiff)

theorem eq_of_forall_pow_mem_of_isPerfect {H K : Subgroup G}
    (hperf : Group.IsPerfect (oTwoQuot ↥H)) (hKH : K ≤ H)
    (hK : H ≤ Subgroup.normalizer (K : Set G)) (hQK : pCoreOf 2 H ≤ K)
    (h2 : ∀ h ∈ H, ∃ n : ℕ, h ^ (2 ^ n) ∈ K) : K = H := by
  classical
  let Kq : Subgroup (oTwoQuot ↥H) :=
    (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))
  have hKnorm : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hK
  haveI : Kq.Normal :=
    Subgroup.Normal.map hKnorm _ (QuotientGroup.mk'_surjective _)
  haveI : Group.IsPerfect (oTwoQuot ↥H) := hperf
  have hKqtop : Kq = ⊤ := by
    refine CFSG.Quasithin.MS93.S36.eq_top_of_perfect_of_pow_mem Kq ?_
    intro z
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨n, hn⟩ := h2 h h.2
    refine ⟨n, ?_⟩
    change (QuotientGroup.mk h : oTwoQuot ↥H) ^ (2 ^ n) ∈ Kq
    rw [← QuotientGroup.mk_pow]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hn)
  refine le_antisymm hKH ?_
  intro x hx
  have hmem : QuotientGroup.mk' (pCore 2 ↥H) (⟨x, hx⟩ : ↥H) ∈ Kq := by
    rw [hKqtop]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
  have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
  have hdiff : (y : G)⁻¹ * x ∈ pCoreOf 2 H := by
    have h1 : (y⁻¹ * (⟨x, hx⟩ : ↥H) : ↥H) ∈ pCore 2 ↥H := by
      have hq : (QuotientGroup.mk' (pCore 2 ↥H)) (y⁻¹ * (⟨x, hx⟩ : ↥H)) = 1 := by
        rw [map_mul, map_inv, hyx, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (N := pCore 2 ↥H)
        (x := y⁻¹ * (⟨x, hx⟩ : ↥H))).mp hq
    exact (CFSG.mem_openPCoreOf_iff (y⁻¹ * (⟨x, hx⟩ : ↥H))).mpr h1
  have hxeq : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [hxeq]
  exact K.mul_mem hyK (hQK hdiff)

theorem str83_caseI_basics {L1 L2 S : Subgroup G} {a : ℕ}
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Z1 L1 L2 S = omegaOneCenterOf S ∧ Z1 L1 L2 S ≤ Z2 L1 L2 S ∧
      Z2 L1 L2 S ⊓
        Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) = ⊥ ∧
      S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S ∧
      Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hSle1 : S ≤ L1 ⊔ Q1 L1 L2 S := by
    calc S = (S ⊓ L1) ⊔ Q1 L1 L2 S := hS1
      _ ≤ L1 ⊔ Q1 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hSle2 : S ≤ L2 ⊔ Q2 L1 L2 S := by
    calc S = (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2
      _ ≤ L2 ⊔ Q2 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hZ1eq : Z1 L1 L2 S = omegaOneCenterOf S :=
    omegaOneCenterOf_pCoreOf_eq hF.1 hSle1 hZI
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    rw [hZ1eq]
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S := by
    rw [hZ1eq]
    have h := omegaOneCenterOf_le_omegaOneCenterOf_pCoreOf
      (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Z1, Z2, Q1, Q2, P1, P2, bigB_comm] using h
  have hZ2bot : Z2 L1 L2 S ⊓
      Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) = ⊥ :=
    z2_inf_centralizer_eq_bot_of_caseI hF hS1 hS2 hZI
  have hHNZ2 : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (sup_le le_sup_left (pCoreOf_le 2 (P2 L1 L2 S))).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hQ2C : Q2 L1 L2 S ≤
      Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hCeq : (L2 ⊔ Q2 L1 L2 S) ⊓
      Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S := by
    have hK0 : (L2 ⊔ Q2 L1 L2 S) ⊓
        Subgroup.centralizer (Z2 L1 L2 S : Set G) ≤ L2 ⊔ Q2 L1 L2 S := inf_le_left
    have hQK0 : Q2 L1 L2 S ≤ (L2 ⊔ Q2 L1 L2 S) ⊓
        Subgroup.centralizer (Z2 L1 L2 S : Set G) := le_inf le_sup_right hQ2C
    have hKn0 : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer
        (((L2 ⊔ Q2 L1 L2 S) ⊓
          Subgroup.centralizer (Z2 L1 L2 S : Set G) : Subgroup G) : Set G) := by
      have hHnC : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer
          (Subgroup.centralizer (Z2 L1 L2 S : Set G) : Set G) :=
        hHNZ2.trans (F7.normalizer_le_normalizer_centralizer (Z2 L1 L2 S))
      intro x hx
      exact CFSG.Quasithin.A4.mem_normalizer_inf (Subgroup.le_normalizer hx) (hHnC hx)
    rcases eq_or_eq_sup_of_normal_of_isL2Quot hF (by omega : 2 ≤ 2 * a + 1) hL2 hK0 hKn0 hQK0
      with hQ | hH
    · exact hQ
    · exfalso
      have hHC : L2 ⊔ Q2 L1 L2 S ≤
          Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
        rw [← hH]
        exact inf_le_right
      have hZ2leC : Z2 L1 L2 S ≤
          Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (Subgroup.mem_centralizer_iff.mp (hHC hx) z hz).symm
      have hZ2le : Z2 L1 L2 S ≤ Z2 L1 L2 S ⊓
          Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) :=
        le_inf le_rfl hZ2leC
      have hZ2eq : Z2 L1 L2 S = ⊥ :=
        le_bot_iff.mp (hZ2le.trans (le_of_eq hZ2bot))
      exact hZ1ne (le_bot_iff.mp (hZ1Z2.trans (le_of_eq hZ2eq)))
  have hSQ2C : S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S := by
    calc S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)
        = (S ⊓ (L2 ⊔ Q2 L1 L2 S)) ⊓
            Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
          rw [inf_eq_left.mpr hSle2]
      _ = S ⊓ ((L2 ⊔ Q2 L1 L2 S) ⊓
            Subgroup.centralizer (Z2 L1 L2 S : Set G)) := by rw [inf_assoc]
      _ = S ⊓ Q2 L1 L2 S := by rw [hCeq]
      _ = Q2 L1 L2 S := inf_eq_right.mpr hQ2S
  refine ⟨hZ1eq, hZ1Z2, hZ2bot, hSQ2C, ?_⟩
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxZ2 : x ∈ Z2 L1 L2 S := (Subgroup.mem_inf.mp hx).1
    have hxCS : x ∈ Subgroup.centralizer (S : Set G) := (Subgroup.mem_inf.mp hx).2
    have hxQ2 : x ∈ Q2 L1 L2 S := (omegaOneCenterOf_le (Q2 L1 L2 S)) hxZ2
    have hxS : x ∈ S := hQ2S hxQ2
    have hx2 : x ^ 2 = 1 :=
      (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 x hxZ2
    rw [hZ1eq]
    exact Subgroup.subset_closure
      ⟨Subgroup.mem_inf.mpr ⟨hxS, hxCS⟩, hx2⟩
  · intro x hx
    have hxZ2 : x ∈ Z2 L1 L2 S := hZ1Z2 hx
    have hxCS : x ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (Subgroup.mem_centralizer_iff.mp (hZI (hSle1 hs)) x hx).symm
    exact Subgroup.mem_inf.mpr ⟨hxZ2, hxCS⟩

theorem isTwoReducedIn_z2_of_caseI {L1 L2 S : Subgroup G} {a : ℕ}
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    IsTwoReducedIn (L2 ⊔ S) (Z2 L1 L2 S) := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  obtain ⟨hZ1eq, hZ1Z2, hZ2bot, hSQ2C, -⟩ :=
    str83_caseI_basics hF hB ha hSz hL2 hZI
  have hZ2ne : Z2 L1 L2 S ≠ ⊥ := by
    intro hbot
    have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
      rw [hZ1eq]
      exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
    exact hZ1ne (le_bot_iff.mp (hZ1Z2.trans (le_of_eq hbot)))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hL2sup : IsL2Quot (2 * a + 1) (oTwoQuot ↥(L2 ⊔ S)) := by
    have hsupQ : L2 ⊔ S = L2 ⊔ Q1 L2 L1 S := by
      rw [hsup2]
      simp [Q1, Q2, P1, P2, bigB_comm]
    rw [hsupQ]
    obtain ⟨eL⟩ := hL2
    exact ⟨(oTwoQuotSupEquiv hF.1.symm).trans eL⟩
  haveI : IsSimpleGroup (oTwoQuot ↥(L2 ⊔ S)) :=
    CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot (by omega) hL2sup
  have hperfect : Group.IsPerfect (oTwoQuot ↥(L2 ⊔ S)) :=
    CFSG.Quasithin.F112R.isPerfect_of_isL2Quot (by omega) hL2sup
  have hnotCentral : ¬ L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
    intro hle
    have hle' : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
      rwa [← hsup2]
    have hZ2le : Z2 L1 L2 S ≤
        Z2 L1 L2 S ⊓ Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) := by
      refine le_inf le_rfl ?_
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hle' hx) z hz).symm
    exact hZ2ne (le_bot_iff.mp (hZ2le.trans (le_of_eq hZ2bot)))
  have hQ2H : Q2 L1 L2 S ≤ L2 ⊔ S := hQ2S.trans le_sup_right
  have hVQ : Z2 L1 L2 S ≤ Q2 L1 L2 S := omegaOneCenterOf_le _
  have hVH : Z2 L1 L2 S ≤ L2 ⊔ S := hVQ.trans hQ2H
  have hHleP2 : L2 ⊔ S ≤ P2 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hHV : L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    hHleP2.trans (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  refine ⟨hVH, hHV, SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S), ?_⟩
  intro D hDH hDN hD
  set C : Subgroup G := (L2 ⊔ S) ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) with hC
  have hCH : C ≤ L2 ⊔ S := by rw [hC]; exact inf_le_left
  have hCn : L2 ⊔ S ≤ Subgroup.normalizer (C : Set G) := by
    intro x hx
    rw [hC]
    exact A4.mem_normalizer_inf (Subgroup.le_normalizer hx)
      (F7.normalizer_le_normalizer_centralizer (Z2 L1 L2 S) (hHV hx))
  have hQ2C : Q2 L1 L2 S ≤ C := by
    rw [hC]
    exact le_inf hQ2H (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S))
  have hKH : D ⊔ C ≤ L2 ⊔ S := sup_le hDH hCH
  have hKn : L2 ⊔ S ≤ Subgroup.normalizer ((D ⊔ C : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hDN hCn
  have hQ2K : pCoreOf 2 (L2 ⊔ S) ≤ D ⊔ C := by
    rw [hpCore2]
    exact hQ2C.trans le_sup_right
  have hD' : ∀ d ∈ D, ∃ n : ℕ, d ^ (2 ^ n) ∈ C := fun d hd => by
    obtain ⟨n, hn⟩ := hD d hd
    exact ⟨n, (L2 ⊔ S).pow_mem (hDH hd) (2 ^ n), hn⟩
  rcases eq_or_mem_pCoreOf_of_normal_of_isSimple (H := L2 ⊔ S) (K := D ⊔ C)
      inferInstance hKH hKn hQ2K with htop | h2el
  · have h2 : ∀ x ∈ L2 ⊔ S, ∃ n : ℕ, x ^ (2 ^ n) ∈ C :=
      exists_pow_mem_of_sup_eq_of_normalizes hCH hCn hDN htop hD'
    have hCe : C = L2 ⊔ S :=
      eq_of_forall_pow_mem_of_isPerfect hperfect hCH hCn (by rwa [hpCore2]) h2
    exact absurd hCe (fun heq => hnotCentral (heq ▸ inf_le_right))
  · intro d hd
    obtain ⟨k, hk⟩ := hD d hd
    have htpos : orderOf d ≠ 0 := (isOfFinOrder_of_finite d).orderOf_pos.ne'
    obtain ⟨e, m, hm_odd, ht⟩ := Nat.exists_eq_two_pow_mul_odd htpos
    have hdm2 : (d ^ m) ^ (2 ^ e) = 1 := by
      rw [← pow_mul, mul_comm, ← ht, pow_orderOf_eq_one]
    have hdmC : d ^ m ∈ C :=
      hQ2C (by
        rw [← hpCore2]
        exact h2el (d ^ m) (Subgroup.mem_sup_left (D.pow_mem hd m)) ⟨e, hdm2⟩)
    have hkC : d ^ (2 ^ k) ∈ C :=
      ⟨(L2 ⊔ S).pow_mem (hDH hd) (2 ^ k), hk⟩
    obtain ⟨i, j, hij⟩ := TauCeti.exists_zpow_mul_zpow_eq_of_coprime (G := G)
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm_odd))
    have hdC : d ∈ C := by
      rw [← hij d]
      exact C.mul_mem (C.zpow_mem hdmC i) (C.zpow_mem hkC j)
    exact hdC.2

theorem d11Hyp_of_caseI {L1 L2 S : Subgroup G} {a : ℕ}
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    D11Hyp (L2 ⊔ S) (L1 ⊔ S) S (Z2 L1 L2 S) (borelOf L1 S ⊔ S) := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) :=
      congrArg (fun X => L1 ⊔ X) hS1
    rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  obtain ⟨hZ1eq, hZ1Z2, -, hSQ2C, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hZ2ne : Z2 L1 L2 S ≠ ⊥ := by
    intro hbot
    have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
      rw [hZ1eq]
      exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
    exact hZ1ne (le_bot_iff.mp (hZ1Z2.trans (le_of_eq hbot)))
  have hsylow1 : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hsylow2 : IsSylowTwoOf S (L2 ⊔ S) := by
    rw [hsup2]
    have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      (by simpa [Q1, Q2, P1, P2, bigB_comm] using hS2)
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hG0le : (L2 ⊔ S) ⊔ (L1 ⊔ S) ≤ L1 ⊔ L2 ⊔ S := by
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact (le_sup_right : L2 ≤ L1 ⊔ L2).trans le_sup_left
    · exact le_sup_right
    · exact (le_sup_left : L1 ≤ L1 ⊔ L2).trans le_sup_left
    · exact le_sup_right
  have hG0ge : L1 ⊔ L2 ⊔ S ≤ (L2 ⊔ S) ⊔ (L1 ⊔ S) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (le_sup_left : L1 ≤ L1 ⊔ S).trans le_sup_right
    · exact (le_sup_left : L2 ≤ L2 ⊔ S).trans le_sup_left
    · exact (le_sup_right : S ≤ L2 ⊔ S).trans le_sup_left
  have hG0 : (L2 ⊔ S) ⊔ (L1 ⊔ S) = L1 ⊔ L2 ⊔ S := le_antisymm hG0le hG0ge
  refine
    { sylow₁ := hsylow2
      sylow₂ := hsylow1
      reduced := isTwoReducedIn_z2_of_caseI hF hB ha hSz hL2 hZI
      nontrivial := hZ2ne
      unique_max := CFSG.Quasithin.H13.A5.isUniqueMaxOver_borelOf_sup
        (L := L1) (T := S) (Hyp111R.of_hyp111 rankOneListedFacts hF.1).r1
        hF.1.h1.normalizes
      centralizer := by rw [hpCore2, hSQ2C]
      no_normal := fun N hN hNn => ?_ }
  have hNQ : N ≤ Q2 L1 L2 S := by rwa [hpCore2] at hN
  have hQ2H : Q2 L1 L2 S ≤ L2 ⊔ S := hQ2S.trans le_sup_right
  have hNG : N ≤ (L2 ⊔ S) ⊔ (L1 ⊔ S) := hNQ.trans (hQ2H.trans le_sup_left)
  have hNGn : (L2 ⊔ S) ⊔ (L1 ⊔ S) ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNG).mp hNn
  have hNle : N ≤ pCoreOf 2 ((L2 ⊔ S) ⊔ (L1 ⊔ S)) :=
    le_pCoreOf_of_le_normalizer 2 hNG hNGn ((pCoreOf_isPGroup 2 (L2 ⊔ S)).to_le hN)
  rw [hG0, hF.1.o2] at hNle
  exact le_bot_iff.mp hNle

theorem z2_le_q1_of_rq
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2)) :
    Z2 L1 L2 S ≤ Q1 L1 L2 S := by
  let q : ℕ := 2 ^ (2 * a + 1)
  have hq4 : 4 ≤ q := by
    have h : 4 ≤ 2 ^ (2 * a + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [q] using h
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) :=
      congrArg (fun X => L1 ⊔ X) hS1
    rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hqU3 : IsSzU3Quot (oTwoQuot ↥L1) q := by
    obtain ⟨e⟩ := hSz
    exact Or.inl ⟨a, ha, rfl, ⟨e⟩⟩
  have hbender1 : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) q := by
    rw [hsup1]
    exact IsSzU3Quot.of_mulEquiv (oTwoQuotSupEquiv hF.1) hqU3
  intro z hz
  by_contra hzQ1
  have hzS : z ∈ S := hQ2S ((omegaOneCenterOf_le (Q2 L1 L2 S)) hz)
  have hz2 : z ^ 2 = 1 :=
    (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 z hz
  have hzsq : z * z ∈ Q1 L1 L2 S := by
    rw [← pow_two, hz2]
    exact (Q1 L1 L2 S).one_mem
  have hzH : z ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) hzS
  set X : Subgroup G := conjClosure (Z2 L1 L2 S ⊓ Q1 L1 L2 S) (L1 ⊔ S) with hX
  have hXq1 : X ≤ Q1 L1 L2 S := by
    refine conjClosure_le fun g hg x hx => ?_
    have hHleP1 : L1 ⊔ S ≤ P1 L1 L2 S :=
      sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
    exact (Subgroup.mem_normalizer_iff.mp
      ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)) (hHleP1 hg)) x).mp hx.2
  have hXn : L1 ⊔ S ≤ Subgroup.normalizer (X : Set G) := le_normalizer_conjClosure _ _
  have hXH : X ≤ L1 ⊔ S := hXq1.trans (hQ1S.trans le_sup_right)
  have hXS : X ≤ S := hXq1.trans hQ1S
  have hXp : IsPGroup 2 X := (pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le hXq1
  have hnorm : IsNormalIn (L1 ⊔ S) X X := by
    refine ⟨le_rfl, fun g hg x hx => ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hXn hg) x).mp hx
  obtain ⟨c, hser⟩ := D15Proof.exists_isChiefSeriesFrom X hnorm
  have hzsq' : z * z ∈ pCoreOf 2 (L1 ⊔ S) := by
    rw [hpCore1]
    exact hzsq
  have hzO' : z ∉ pCoreOf 2 (L1 ⊔ S) := by
    rwa [hpCore1]
  have hbig := pow_sq_le_relIndex_centralizer (H := L1 ⊔ S) (U := X) (q := q) (c := c)
    hbender1 hXp hXH hser hzH hzsq' hzO'
  have hcent : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) =
      Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hCQ : X ⊓ Q2 L1 L2 S ≤ X ⊓ Subgroup.centralizer ({z} : Set G) := by
    refine le_inf inf_le_left ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hQ2C hx.2) z hz).symm
  have hQ2X : (X ⊓ Q2 L1 L2 S).relIndex X ≤ q := by
    rw [Subgroup.inf_relIndex_left]
    calc (Q2 L1 L2 S).relIndex X ≤ (Q2 L1 L2 S).relIndex S :=
          Subgroup.relIndex_le_of_le_right hXS (D15Proof.relIndex_ne_zero _ _)
      _ = q := by
          have h := str86_relIndex_q2_s (n := 2 * a + 1) hF hB (by omega) hL2
          simpa [q] using h
  have hsmall : (Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)).relIndex X ≤
      q := by
    rw [hcent, ← Subgroup.inf_relIndex_left (H := X)
      (K := Subgroup.centralizer ({z} : Set G))]
    exact (Subgroup.relIndex_le_of_le_left hCQ (D15Proof.relIndex_ne_zero _ _)).trans hQ2X
  have hin : (q ^ 2) ^ c ≤ q := hbig.trans hsmall
  have hq1 : 1 < q := by omega
  have hc0 : c = 0 := by
    have hin' : q ^ (2 * c) ≤ q ^ 1 := by
      simpa [pow_mul] using hin
    have h2c : 2 * c ≤ 1 := (Nat.pow_le_pow_iff_right hq1).mp hin'
    omega
  have hcomm : ⁅X, oTwoUpper (L1 ⊔ S)⁆ = ⊥ := D14.commutator_eq_bot_of_zero hXp hser hc0
  have hc : ∀ x ∈ Q1 L1 L2 S, x * z * x⁻¹ * z⁻¹ ∈ X := by
    intro x hx
    refine le_conjClosure (Z2 L1 L2 S ⊓ Q1 L1 L2 S) (L1 ⊔ S)
      (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have hxP2 : x ∈ P2 L1 L2 S :=
        ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right) (hQ1S hx)
      have hconjZ : x * z * x⁻¹ ∈ Z2 L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp
          (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S) hxP2) z).mp hz
      exact (Z2 L1 L2 S).mul_mem hconjZ ((Z2 L1 L2 S).inv_mem hz)
    · have hzP1 : z ∈ P1 L1 L2 S :=
        ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right) hzS
      have hconjQ : z * x * z⁻¹ ∈ Q1 L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp
          ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)) hzP1) x).mp hx
      have hmul : x * (z * x * z⁻¹)⁻¹ ∈ Q1 L1 L2 S :=
        (Q1 L1 L2 S).mul_mem hx ((Q1 L1 L2 S).inv_mem hconjQ)
      convert hmul using 1
      group
  exact false_of_commutator_le_of_bender hF.1 hB hS1 hqU3 hXq1 hXn hcomm hzS hzQ1 hc

theorem caseI_conclusion_of_str83CaseI (h : Str83CaseI)
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hVBig : VBig L2) (hVL2 : VL2 L2) :
    L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
  h G L1 L2 S a hF hB ha hSz hVBig hVL2

end CFSG.Quasithin.Stroth

end
