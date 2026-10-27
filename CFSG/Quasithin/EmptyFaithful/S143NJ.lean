module

public import CFSG.Quasithin.EmptyFaithful.S143NI
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma116
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.Quasithin.Vol2.Ch1Eleven
public import CFSG.Quasithin.Vol2.Ch1Lem125

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace S143

open A6Model

section Component

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {Vl Vr : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)} (hP : Conf6Plus cm Vl Vr s)
  (hVl : ∀ σ ∈ Vl, ∃ u ∈ uOfL22 T M, mm cm (matOf6 σ) = mm (cmat z a r r1 u) cm)
  (hVr : ∀ σ ∈ Vr, ∃ ρ' ∈ rOf T M, mm cm (matOf6 σ) = mm (cmat z a r r1 ρ') cm)
  (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)
  {δ : G} (hδD : δ ∈ dOf T M) (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
  (hδA : δ ∉ c.Ac hrW hrV hr2) {p : Fin 6} (hps : s p ≠ p)
  (hcoc : ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ.1)
  {y₅ : G} (hy₅ : y₅ ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) (hy₅o : orderOf y₅ = 5)
  (hemb : ∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X))
  (hc18c : Concl18c T (c.Ac hrW hrV hr2))
  (hrq : (rOf T M ⊔ qOf T).relIndex T = 2)
  (hAAt : rOf T M = c.Ac hrW hrV hr2 ⊔ conjSubgroup (c.Ac hrW hrV hr2) t)
  (hNAK : Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) =
    Subgroup.normalizer (kOf T M (c.Ac hrW hrV hr2) : Set G))
  (hNA : Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) =
    kOf T M (c.Ac hrW hrV hr2) ⊔ dOf T M)
  (hnc : ∀ x' : G, x' * z * x'⁻¹ ≠ δ) (hnc' : ∀ x' : G, x' * z * x'⁻¹ ≠ z * δ)
  (hAab : IsElemAbelian 2 (c.Ac hrW hrV hr2))

include hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hy₅ hy₅o hemb hc18c hrq hAAt hNAK hNA
  hnc hnc' hAab

theorem exists_component_Ld
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hlist : Lemma115_3_List) :
    ∃ L : Subgroup G, IsComponentIn L (Subgroup.centralizer ({δ} : Set G)) ∧ z ∈ L ∧
      kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤ L ∧ Lemma115Cases L z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple := c.hyp.simple
  have hnonab := c.hyp.nonabelian
  have hQ := c.hyp.qtke
  have hz := hS.z_mem
  have hz1 := hS.z_ne
  have hδ2 : δ * δ = 1 := Gamma_sq hS htT htRQ hM hC1 hδ
  have hδ1 : δ ≠ 1 := fun e => hδA (e ▸ (c.Ac hrW hrV hr2).one_mem)
  have hAkd := A_le_kdOf hS hM hδD hδ hδA hcoc
  have hkdG : kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤ Subgroup.centralizer ({δ} : Set G) :=
    inf_le_right
  have hkdN : kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    kdOf_le_normalizer
  have hOeq := pCoreOf_gd_eq hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hy₅ hy₅o hemb hc18c
    hrq hAAt hNAK hNA hnc hnc'
  have hδO : δ ∈ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) :=
    hOeq ▸ Subgroup.mem_zpowers δ
  have hH : pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) ≠ ⊥ := fun h =>
    hδ1 (Subgroup.mem_bot.mp (h ▸ hδO))
  have hSyl := isSylowTwoOf_tdOf_gd hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb hnc hnc'
  have hRS : sdOf T M δ ≤ tdOf T δ := fun w hw => ⟨rq_le_of_hyp c.h1281 hw.1, hw.2⟩
  have hidx := relIndex_sdOf_le c (δ := δ) hrq
  have hL := isLocal_kd_sd c hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o hC1 hNAK
  obtain ⟨Ld, hLd, hKdLd⟩ := lemma_1_2_5_exists hQ hsimple hnonab h37 h39 hH hSyl hRS hidx hL hkdG
  have hzT : z ∈ T := (quasithinOmegaOneCenter_le_center T hz).1
  have hzcT : z ∈ Subgroup.centralizer (T : Set G) := (quasithinOmegaOneCenter_le_center T hz).2
  have hzGd : z ∈ Subgroup.centralizer ({δ} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h' hh' => by
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      exact (z_comm_dOf hS hδD).symm
  have hzLd : z ∈ Ld := hKdLd (hAkd hS.z_A)
  have hKdop : kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤
      opResidual 2 (Subgroup.centralizer ({δ} : Set G) ⊓
        Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) := by
    have hperf := kd_perfect hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o
    rw [eq_oTwoUpper_of_perfect hperf]
    refine (Subgroup.closure_le _).mpr fun w hw => ?_
    exact mem_opResidual_of_coprime ⟨hkdG hw.1, hkdN hw.1⟩ (Nat.coprime_two_right.mpr hw.2)
  have hzop : z ∈ ⁅c.Ac hrW hrV hr2, opResidual 2 (Subgroup.centralizer ({δ} : Set G) ⊓
      Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))⁆ :=
    Subgroup.commutator_mono le_rfl hKdop
      (le_commutator_A_kd hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o hS.z_A)
  have hb : T ⊓ Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) : Set G) ≤
      T ⊓ Subgroup.centralizer ({δ} : Set G) := by
    rw [hOeq]
    exact fun w hw => ⟨hw.1, Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers δ)) hw.2⟩
  have hhQ := lemma_1_2_11 hQ c.hyp.sylow hH hSyl hLd hz hz1 hzLd ⟨hzT, hzGd⟩
    ⟨c.Ac hrW hrV hr2, hAkd.trans hkdG, hAab, hzop⟩ hb
  rcases hhQ with hq | hchar
  swap
  ·
    exfalso
    have hy₅G : y₅ ∈ Subgroup.centralizer ({δ} : Set G) := hkdG hy₅
    have hmem : y₅ ∈ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) := by
      refine hchar ⟨hy₅G, ?_⟩
      rw [hOeq]
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hc : δ * y₅ = y₅ * δ := (Subgroup.mem_centralizer_iff.mp hy₅G δ rfl)
      exact ((Commute.zpow_left (show Commute δ y₅ from hc) k).eq)
    rw [hOeq] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hδ2' : δ ^ 2 = 1 := by rw [pow_two]; exact hδ2
    have h2 : y₅ ^ 2 = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hδ2', one_zpow]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hy₅o] at this
    omega
  have hcomp : IsComponentIn Ld (Subgroup.centralizer ({δ} : Set G)) :=
    Id2519.isComponentIn_of_mem_cComp hLd hq
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers δ) := by
    have hord : orderOf δ = 2 := orderOf_eq_prime (by rw [← pow_two] at hδ2; exact hδ2) hδ1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
  have hHyp : Lemma115Hyp (Subgroup.centralizer ({δ} : Set G)) (tdOf T δ) (mcOf T) z :=
    lemma116 hQ.2.1 hzp (by rw [Ne, Subgroup.zpowers_eq_bot]; exact hδ1)
      (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun h' hh' => by
          rw [Set.mem_singleton_iff] at hh'; subst hh'; rfl))
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers δ))))
      (centralizer_singleton_le_normalizer_zpowers δ) hSyl
      (isSylowTwoOf_of_quasithinIsSylowTwo c.hyp.sylow le_top) inf_le_left hzT hzcT hz1
      (by have := sq_eq_one_of_mem_omegaOneCenter T hz; exact this) c.hyp.mc_max
      (fun w hw => Subgroup.mem_centralizer_iff.mpr fun u hu => by
        rcases c.mem_Z_cases hz hz1 hu with h | h
        · rw [h]; simp
        · rw [h]; exact (Subgroup.mem_centralizer_iff.mp hw z rfl))
  exact ⟨Ld, hcomp, hzLd, hKdLd,
    hlist G hsimple hnonab (qtkeCore_of_cat hnonab hQ) _ _ _ z hHyp Ld hcomp⟩

end Component

end S143

end CFSG.Quasithin
