module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rn
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rf
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rh

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22r_normalizes_calC (D : Data G) (h201 : S20_1_124 D) (h1930 : H1930 D) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) {L K' : Subgroup G} (hL : L ∈ calLOf D.T D.M H) (hK : K' ∈ calC L)
    (hKM : ¬ K' ≤ D.M) {x : G} {q : ℕ} (hq : q.Prime) (hxo : orderOf x = q) (hxH : x ∈ H) (hxM : x ∈ D.M)
    (hU : ∀ h ∈ H, h⁻¹ * x * h ∈ D.M → h ∈ D.M) : x ∈ normalizer (K' : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKsub, hKperf⟩ := uc22p22r_K_subnormal hL hK
  have hKH : K' ≤ H := hKsub.le
  have hOinf : OInf H ≤ D.M := (h201 h1930 H hH).2.2
  have hTH : D.T ≤ H := hH.1
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 (D.T.subgroupOf H) ⊤ := by
    have h1 : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := D.sylowG.of_le hTH le_top
    have h2 : CFSG.ABGLocalTools.IsSylowOf 2 ((D.T.subgroupOf H).map H.subtype)
        ((⊤ : Subgroup ↥H).map H.subtype) := by
      rw [Subgroup.map_subgroupOf_eq_of_le hTH, Subgroup.map_top, Subgroup.range_subtype]
      exact h1
    exact (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).1 h2
  have hR : CFSG.solvableRadical ↥H ≤ D.M.subgroupOf H := fun r hr => hOinf ⟨r, hr, rfl⟩
  have hU' : ∀ h : ↥H, h⁻¹ * (⟨x, hxH⟩ : ↥H) * h ∈ D.M.subgroupOf H → h ∈ D.M.subgroupOf H :=
    fun h hh => hU h h.2 hh
  have hNR : ∀ n ∈ (uc22p22rPhi hKH).ker,
      ((n : ↥(K'.subgroupOf H)) : ↥H) ∈ CFSG.solvableRadical ↥H := by
    intro n hn
    obtain ⟨r, hr, hrn⟩ := uc22p22r_pCoreOf_le_oinf hKsub (uc22p22rPhi_ker hKH n hn)
    have : r = ((n : ↥(K'.subgroupOf H)) : ↥H) := Subtype.ext hrn
    rw [← this]
    exact hr
  have hKM' : ¬ K'.subgroupOf H ≤ D.M.subgroupOf H := by
    intro h
    apply hKM
    intro k hk
    exact h (show (⟨k, hKH hk⟩ : ↥H) ∈ K'.subgroupOf H from hk)
  have hxN' := uc22p22r_normalizes hq (x := (⟨x, hxH⟩ : ↥H)) (by rw [Subgroup.orderOf_mk]; exact hxo)
    hT' (fun t ht => D.sylowM.le ht) (show x ∈ D.M from hxM) hR hU'
    (uc22p22r_isPerfect_subgroupOf hKH hKperf) hKsub.subgroupOf (N := (uc22p22rPhi hKH).ker) hNR
    (uc22p22r_quasisimple_quot hKH hK.2.2) hKM'
  exact uc22p22r_mem_normalizer_of_subgroupOf hKH hxH hxN'

theorem uc22p22r_mem_normalizer_iSup {ι : Type*} {F : ι → Subgroup G} {x : G}
    (h : ∀ i, x ∈ normalizer ((F i : Subgroup G) : Set G)) : x ∈ normalizer (((⨆ i, F i) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  congr 1
  funext i
  exact Subgroup.mem_normalizer_iff_map_conj_eq.1 (h i)

theorem uc22p22r_exists_calC_not_le (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) (hLM : ¬ L ≤ D.M) :
    ∃ K ∈ calC L, L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom ∧ ¬ K ≤ D.M := by
  obtain ⟨K, hK, hLK⟩ := hL.2.2.2
  refine ⟨K, hK, hLK, fun hKM => hLM ?_⟩
  rw [hLK]
  refine iSup_le fun t => ?_
  rintro _ ⟨k, hk, rfl⟩
  have htM : (t : G) ∈ D.M := D.sylowM.le t.2
  exact D.M.mul_mem (D.M.mul_mem htM (hKM hk)) (D.M.inv_mem htM)

theorem uc22p22r_normalizes_calL (D : Data G) (h201 : S20_1_124 D) (h1930 : H1930 D) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) {L : Subgroup G} (hL : L ∈ calLOf D.T D.M H) (hLM : ¬ L ≤ D.M) {x : G} {q : ℕ}
    (hq : q.Prime) (hxo : orderOf x = q) (hxH : x ∈ H) (hxM : x ∈ D.M)
    (hU : ∀ h ∈ H, h⁻¹ * x * h ∈ D.M → h ∈ D.M) : x ∈ normalizer (L : Set G) := by
  obtain ⟨K, hK, hLK, hKM⟩ := uc22p22r_exists_calC_not_le D hL.1 hLM
  rw [hLK]
  refine uc22p22r_mem_normalizer_iSup fun t => ?_
  have hTL : D.T ≤ normalizer (L : Set G) := hL.1.1
  have hKt : uniqueFourConj (t : G)⁻¹ K ∈ calC L := uc22p22u_calC_conj hTL hK (D.T.inv_mem t.2)
  have he : uniqueFourConj (t : G)⁻¹ K = K.map (MulAut.conj (t : G)).toMonoidHom := by
    unfold uniqueFourConj
    rw [inv_inv]
  rw [he] at hKt
  have hKtM : ¬ K.map (MulAut.conj (t : G)).toMonoidHom ≤ D.M := by
    intro h
    apply hKM
    intro k hk
    have h1 : (t : G) * k * (t : G)⁻¹ ∈ D.M := h ⟨k, hk, rfl⟩
    have htM : (t : G) ∈ D.M := D.sylowM.le t.2
    have h2 : k = (t : G)⁻¹ * ((t : G) * k * (t : G)⁻¹) * (t : G) := by group
    rw [h2]
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem htM) h1) htM
  exact uc22p22r_normalizes_calC D h201 h1930 hH hL hKt hKtM hq hxo hxH hxM hU

theorem uc22p22r_le_normalizer_calC_of_odd {L B K : Subgroup G} (hBL : B ≤ normalizer (L : Set G))
    (hBo : Odd (Nat.card B)) (hcount : ∀ K₁ ∈ calC L, ∀ K₂ ∈ calC L, ∀ K₃ ∈ calC L, K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃)
    (hK : K ∈ calC L) : B ≤ normalizer (K : Set G) := by
  intro b hb
  have hb2 : b * b ∈ B := B.mul_mem hb hb
  have h1 : uniqueFourConj b K ∈ calC L := uc22p22u_calC_conj hBL hK hb
  have h2 : uniqueFourConj (b * b) K ∈ calC L := uc22p22u_calC_conj hBL hK hb2
  have hnorm : ∀ g : G, (∀ y, y ∈ K ↔ g * y * g⁻¹ ∈ K) → g ∈ normalizer (K : Set G) :=
    fun g hg => Subgroup.mem_normalizer_iff.2 hg
  have hodd : Odd (orderOf b) := by
    have hdvd : orderOf b ∣ Nat.card B := by
      have := orderOf_dvd_natCard (⟨b, hb⟩ : ↥B)
      rwa [Subgroup.orderOf_mk] at this
    exact hBo.of_dvd_nat hdvd
  rcases hcount K hK _ h1 _ h2 with h | h | h
  ·
    refine hnorm b fun y => ?_
    rw [← uc22p22f_mem_conj K b y, ← h]
  ·
    have hb2N : b * b ∈ normalizer (K : Set G) := hnorm (b * b) fun y => by
      rw [← uc22p22f_mem_conj K (b * b) y, ← h]
    obtain ⟨k, hk⟩ := hodd
    have hpow : b = (b * b) ^ (k + 1) := by
      rw [← pow_two, ← pow_mul]
      have : 2 * (k + 1) = orderOf b + 1 := by omega
      rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
    rw [hpow]
    exact Subgroup.pow_mem _ hb2N _
  ·
    refine hnorm b fun y => ?_
    have h3 := congrArg (fun J : Subgroup G => b⁻¹ * y * b ∈ J) h
    simp only [uc22p22f_mem_conj] at h3
    have e1 : b * (b⁻¹ * y * b) * b⁻¹ = y := by group
    have e2 : b * b * (b⁻¹ * y * b) * (b * b)⁻¹ = b * y * b⁻¹ := by group
    rw [e1, e2] at h3
    exact Iff.of_eq h3

end CFSG.LocalAnalysis.UniquenessCase.UC22
