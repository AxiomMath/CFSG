module

public import CFSG.Quasithin.H13.L32A770e
public import CFSG.Quasithin.H13.L32A770f

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem normalizer_sup_u0_le (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    hz T V ⊓ Subgroup.normalizer ((V ⊔ u0 T V : Subgroup G) : Set G) ≤
      L₁Of L (fsuV1 T V) ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := hz T V ⊓ Subgroup.normalizer ((V ⊔ u0 T V : Subgroup G) : Set G) with hN
  set P := L₁Of L (fsuV1 T V) ⊔ T with hP
  set Q := pCoreOf 2 (hz T V) with hQ
  obtain ⟨φ, hs, hk⟩ := exists_phi h h63
  have hTH : T ≤ hz T V := hF.T_le_H
  have hPH : P ≤ hz T V := hF.L₁T_le_H
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hPN : P ≤ N := by
    refine le_inf hPH fun l hl => ?_
    rw [← conjSub_eq_self_iff, conjSub_sup, conjSub_eq_self_iff.mpr (hF.L₁T_normalizes_Vp hl),
      conjSub_eq_self_iff.mpr (hz_le_normalizer_u0 h hMod (hPH hl))]
  have hQT : Q ≤ T := pCoreOf_le_of_le h hTH
  have hQP : Q ≤ P := hQT.trans le_sup_right
  have hNH : N ≤ hz T V := inf_le_left
  have h120 : Q.relIndex (hz T V) = 120 := by
    rw [← card_map_phi hk le_rfl, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective φ hs,
      Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hTi : ¬ 2 ∣ (T.subgroupOf (hz T V)).index := by
    intro hd
    apply h.fsu.sylow.2
    rw [← Subgroup.relIndex_mul_index hTH]
    exact Dvd.dvd.mul_right hd _
  have h8 : Q.relIndex T = 8 := relIndex_phi_sylow hs hk hTH h.fsu.sylow.1 hTi
  have hd8 : 8 ∣ Q.relIndex P := by
    rw [← Subgroup.relIndex_mul_relIndex Q T P hQT le_sup_right, h8]
    exact dvd_mul_right 8 _
  obtain ⟨x, hxL1, hx3, hx1⟩ := exists_x3_l1 h hMod h1222 h1332 h1334
  have hxP : x ∈ P := Subgroup.mem_sup_left hxL1
  have hxQ : x ∉ Q := fun hxQ => hx1 (eq_one_of_pow_three_of_isPGroup
    (pCoreOf_isPGroup 2 _) hxQ hx3)
  have hd3 : 3 ∣ Q.relIndex P := by
    rw [← card_map_phi hk hPH]
    have hmem : φ ⟨x, hPH hxP⟩ ∈ (P.subgroupOf (hz T V)).map φ :=
      ⟨_, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
    have hord : orderOf (φ ⟨x, hPH hxP⟩) = 3 := by
      apply orderOf_eq_prime
      · rw [← map_pow]
        have e : (⟨x, hPH hxP⟩ : ↥(hz T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
        rw [e, map_one]
      · intro e
        apply hxQ
        rw [← MonoidHom.mem_ker, hk] at e
        exact mem_pCoreOf_iff'.mpr e
    have := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [hord] at this
  have hd24 : 24 ∣ Q.relIndex P :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) hd8 hd3
  have hPNd := Subgroup.relIndex_mul_relIndex Q P N hQP hPN
  have hNHd := Subgroup.relIndex_mul_relIndex Q N (hz T V) (hQP.trans hPN) hNH
  have hNe : Q.relIndex N ≠ 120 := by
    intro e
    rw [h120, e] at hNHd
    have h1 : N.relIndex (hz T V) = 1 := by omega
    have hHN : hz T V ≤ N := Subgroup.relIndex_eq_one.mp h1
    have hKN : kz T V ≤ Subgroup.normalizer ((V ⊔ u0 T V : Subgroup G) : Set G) :=
      fun k hk => (hHN (oTwoUpper_le _ hk)).2
    have hne : V ⊔ u0 T V ≠ u0 T V := by
      intro e'
      have h4 := (relIndex_sup_u0 h hMod h63 hF).1
      rw [e', Subgroup.relIndex_self] at h4
      omega
    have e' := eq_fsuU_of_lt h hMod h63 le_sup_right (sup_le hVU hU0U) hKN hne
    have h4 := (relIndex_sup_u0 h hMod h63 hF).2
    rw [e', Subgroup.relIndex_self] at h4
    omega
  have hdN : Q.relIndex N ∣ 120 := by
    rw [← h120, ← hNHd]
    exact dvd_mul_right _ _
  obtain ⟨m, hm⟩ : 24 ∣ Q.relIndex N := hd24.trans ⟨_, hPNd.symm⟩
  have hm5 : m ∣ 5 := by
    rw [hm] at hdN
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 24) (by simpa using hdN)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hm5 with rfl | rfl
  · have h24 : Q.relIndex N = 24 := by rw [hm]
    have hP24 : Q.relIndex P = 24 :=
      Nat.dvd_antisymm (h24 ▸ ⟨_, hPNd.symm⟩) hd24
    rw [hP24, h24] at hPNd
    have h1 : P.relIndex N = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1
  · exact absurd hm hNe

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem T_le_normalizer_F (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) {s : G} (hsW : s ∈ conjSub ((k : G) * g) (fsuU T V))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) (hsT : ∀ t ∈ T, t * s * t⁻¹ * s⁻¹ ∈ pCoreOf 2 (hz T V)) :
    T ≤ Subgroup.normalizer
      ((⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ : Subgroup G) : Set G) := by
  set W := conjSub ((k : G) * g) (fsuU T V) with hW
  set Q := pCoreOf 2 (hz T V) with hQ
  have hWR : W ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    rw [hW, ← uα_eq (g := g) (k := k) h hMod]
    exact N.uα_le hF
  have hWH : W ≤ hz T V := hWR.trans ((pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H)
  have hWQ : W ≤ Subgroup.normalizer (Q : Set G) := hWH.trans (le_normalizer_pCoreOf 2 _)
  have hV1F := N.v1_le h hMod h63 hF h1222 h1332 h1334 h69 h2
  have hFeq : ⁅fsuU T V, W⁆ = ⁅fsuU T V, W ⊔ Q⁆ := by
    refine le_antisymm (Subgroup.commutator_mono le_rfl le_sup_left) ?_
    have := commutator_sup_le (U := fsuU T V) (V₁ := fsuV1 T V) (X := W) (Q := Q)
      (hWH.trans hF.H_normalizes_V₁) hWQ fun q hq u hu => comm_mem_of_pCoreOf h hMod hF hq hu
    rwa [sup_eq_left.mpr hV1F] at this
  have hWs := N.mem_or_mul_mem h hMod hF h2 hsW hsQ
  intro t ht
  have htH : t ∈ hz T V := hF.T_le_H ht
  rw [← conjSub_eq_self_iff, hFeq, ← conjSub_commutator,
    conjSub_eq_self_iff.mpr (hz_le_normalizer_U h hMod htH)]
  congr 1
  refine conjSub_eq_of_le ?_
  rw [conjSub_sup, conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ htH)]
  refine sup_le ?_ le_sup_right
  rintro _ ⟨w, hw, rfl⟩
  show t * w * t⁻¹ ∈ W ⊔ Q
  rcases hWs w hw with hwQ | hwQ
  · exact Subgroup.mem_sup_right
      ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ htH) w).mp hwQ)
  · have h1 : t * (s⁻¹ * w) * t⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ htH) _).mp hwQ
    have hsN : s⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      inv_mem (le_normalizer_pCoreOf 2 _ (hWH hsW))
    have h3 : s⁻¹ * (t * s * t⁻¹ * s⁻¹) * s⁻¹⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hsN _).mp (hsT t ht)
    rw [inv_inv] at h3
    rw [show t * w * t⁻¹ = s * (s⁻¹ * (t * s * t⁻¹ * s⁻¹) * s) * (t * (s⁻¹ * w) * t⁻¹) by group]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left hsW) (Subgroup.mem_sup_right h3))
      (Subgroup.mem_sup_right h1)

end Not1471

end CFSG.Quasithin.H13.L32A
