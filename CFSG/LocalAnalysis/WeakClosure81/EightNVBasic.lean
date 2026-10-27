module

public import CFSG.LocalAnalysis.WeakClosure81.EightNineteenAux

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem le_normalizer_inf_of_le {T H C : Subgroup G} (hTH : T ≤ H)
    (hHC : H ≤ normalizer (C : Set G)) : T ≤ normalizer ((T ⊓ C : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hT : y ∈ T ↔ t * y * t⁻¹ ∈ T :=
    ⟨fun hy => T.mul_mem (T.mul_mem ht hy) (T.inv_mem ht), fun hy => by
      have := T.mul_mem (T.mul_mem (T.inv_mem ht) hy) ht
      simpa [mul_assoc] using this⟩
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hT, (Subgroup.mem_normalizer_iff.mp (hHC (hTH ht)) y)]

theorem Sit813.v1Grp_le_omegaOneCenterOf_pCoreOf {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : v1Grp V H T A K ≤ omegaOneCenterOf (pCoreOf 2 H) := by
  intro v hv
  obtain ⟨hvV, hvS⟩ := Subgroup.mem_inf.mp hv
  refine mem_omegaOneCenterOf (h.calH0.2 hvV) (fun y hy => ?_)
    (h.minCex.hyp.hyp7.1.2 v hvV)
  have hyS : y ∈ sGrp H T A K := (le_sup_left : rGrp H T K ≤ sGrp H T A K) (h.pCoreOf_le_rGrp hy)
  exact Subgroup.mem_centralizer_iff.mp hvS y hyS

private def oTwoSetNV (N K : Subgroup G) : Set (Subgroup G) :=
  {W | N ≤ W ∧ W ≤ K ∧ (W.subgroupOf K).Normal ∧ ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k ∈ N}

theorem exists_two_pow_mem_of_mem_oTwoMod {C K : Subgroup G} (hC : (C.subgroupOf K).Normal)
    {n : G} (hn : n ∈ oTwoMod C K) : ∃ k : ℕ, n ^ 2 ^ k ∈ C := by
  haveI : (C.subgroupOf K).Normal := hC
  let Sset : Set (Subgroup G) := oTwoSetNV C K
  have hsup : (⨆ x : Sset, (x : Subgroup G)) = oTwoMod C K :=
    (iSup_subtype'' Sset id).trans rfl
  have hnK : n ∈ K := oTwoMod_le_self hn
  let Q := ↥K ⧸ (C.subgroupOf K)
  let q : ↥K →* Q := QuotientGroup.mk' (C.subgroupOf K)
  let P : Subgroup Q := ⨆ W ∈ Sset, (W.subgroupOf K).map q
  have hP2 : IsPGroup 2 P := by
    refine Sylow.biSup_of_normal Sset (fun W => (W.subgroupOf K).map q) ?_ ?_
    · intro W hW
      intro y
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp y.2
      have hk := hW.2.2.2 (w : G) (by simpa [Subgroup.mem_subgroupOf] using hw)
      obtain ⟨k, hk⟩ := hk
      refine ⟨k, ?_⟩
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hwy, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (by simpa [Subgroup.mem_subgroupOf] using hk)
    · intro W hW
      exact (hW.2.2.1).map q (QuotientGroup.mk'_surjective _)
  have hC' : ∃ (hnK : n ∈ K), (q ⟨n, hnK⟩ : Q) ∈ P := by
    have hn' : n ∈ ⨆ x : Sset, (x : Subgroup G) := by rwa [hsup]
    have aux : ∀ a ∈ ⨆ x : Sset, (x : Subgroup G),
        ∃ (haK : a ∈ K), (q ⟨a, haK⟩ : Q) ∈ P := by
      intro a ha
      refine Subgroup.iSup_induction (fun x : Sset => (x : Subgroup G))
        (C := fun a => ∃ (haK : a ∈ K), (q ⟨a, haK⟩ : Q) ∈ P) ha ?_ ?_ ?_
      · intro x b hbx
        have hbK : b ∈ K := x.2.2.1 hbx
        refine ⟨hbK, ?_⟩
        have hmem : q ⟨b, hbK⟩ ∈ (x.1.subgroupOf K).map q :=
          Subgroup.mem_map.mpr ⟨⟨b, hbK⟩, by simpa [Subgroup.mem_subgroupOf] using hbx, rfl⟩
        exact le_iSup₂ (f := fun W (_ : W ∈ Sset) => (W.subgroupOf K).map q) x.1 x.2 hmem
      · refine ⟨K.one_mem, ?_⟩
        convert P.one_mem using 1
        show q (1 : ↥K) = 1
        exact map_one q
      · intro a b ha hb
        obtain ⟨haK, hqa⟩ := ha
        obtain ⟨hbK, hqb⟩ := hb
        refine ⟨K.mul_mem haK hbK, ?_⟩
        have hqab : q ⟨a * b, K.mul_mem haK hbK⟩ = q ⟨a, haK⟩ * q ⟨b, hbK⟩ := by
          rw [show (⟨a * b, K.mul_mem haK hbK⟩ : ↥K) = ⟨a, haK⟩ * ⟨b, hbK⟩ from rfl,
            map_mul]
        rw [hqab]
        exact P.mul_mem hqa hqb
    exact aux n hn'
  obtain ⟨hnK', hqnP⟩ := hC'
  obtain ⟨k, hk⟩ := hP2 ⟨q ⟨n, hnK'⟩, hqnP⟩
  refine ⟨k, ?_⟩
  have hk' : (q ⟨n, hnK'⟩ : Q) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [← map_pow] at hk'
  have hkN : (⟨n, hnK'⟩ : ↥K) ^ 2 ^ k ∈ C.subgroupOf K :=
    (QuotientGroup.eq_one_iff _).mp hk'
  simpa [Subgroup.mem_subgroupOf] using hkN

theorem Sit813.exists_mul_eq_of_mem_oTwoMod {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) {n : G} (hn : n ∈ oTwoMod (cGrp H T) K) :
    ∃ s ∈ T ⊓ oTwoMod (cGrp H T) K, ∃ c ∈ cGrp H T, n = s * c := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCnormK : ((cGrp H T).subgroupOf K).Normal := h.cGrp_normal
  have hCD : cGrp H T ≤ oTwoMod (cGrp H T) K := h.cGrp_le_oTwoMod
  have hDK : oTwoMod (cGrp H T) K ≤ K := oTwoMod_le_self
  have hDnormC : ((cGrp H T).subgroupOf (oTwoMod (cGrp H T) K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCD).mpr
      (hDK.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer h.concl813.ge_C).mp hCnormK))
  have hq : ∀ x ∈ oTwoMod (cGrp H T) K, ∃ k : ℕ, x ^ 2 ^ k ∈ cGrp H T := fun x hx =>
    exists_two_pow_mem_of_mem_oTwoMod hCnormK hx
  exact exists_mul_eq_of_pow_mem hDnormC hq
    (h.isSylowIn_oTwoMod_of_isSylowIn_inf h.concl813.t_sylow) n hn

end CFSG.LocalAnalysis.WeakClosure81

end
