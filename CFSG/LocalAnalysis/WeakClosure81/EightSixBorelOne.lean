module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelve
import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitBridge
public import CFSG.LocalAnalysis.WeakClosure81.EightSixIn

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}


theorem exists_central_of_shape86DeltaT' (hConf : SpURootConfiguration) (h : Hyp83 V H T)
    (hKT : H = kGenIn V H ⊔ T) (hδ : Shape86DeltaT' V H T) :
    ∃ z ∈ T, z ≠ 1 ∧ (∀ t ∈ T, z * t = t * z) ∧ ∀ k ∈ kGenIn V H, z * k = k * z := by
  obtain ⟨m, n, hn, hrk, X, instX, φ, hφ, hroot⟩ := hδ
  letI := instX
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  obtain ⟨φ', hφ', hbar⟩ := exists_ambient_barMap h hKT hφ
  have h2 : Nat.card (barSub (kGenIn V H) φ V) = 2 := by
    rw [Hyp83.card_barSub_eq_two_pow_rankBarV h hKT hφ, hrk]
    norm_num
  have hbar_ne : barSub (kGenIn V H) φ V ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, h2]
    norm_num
  obtain ⟨s, hs⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbar_ne
  have hs' : (s : X) ≠ 1 := fun h1 => hs (Subtype.ext h1)
  have hX : IsSpGp (X ⧸ Subgroup.center X) m n ∨
      IsPSUGp (X ⧸ Subgroup.center X) m n := by
    rcases hroot with ⟨-, hr⟩ | ⟨hm3, hr⟩
    · obtain ⟨k, hmk, F, hF, hFin, hcard, e, -⟩ := hr (s : X) s.2 hs'
      exact Or.inl ⟨k, hmk, F, hF, hFin, hcard, ⟨e⟩⟩
    · obtain ⟨F, hF, hFin, hcard, e, -⟩ := hr (s : X) s.2 hs'
      have hneq : (m, 2 ^ n) ≠ (3, 2) := by
        intro h3
        have h2n : 2 ^ n = 2 := by simpa using congrArg Prod.snd h3
        have hge : 2 ^ 2 ≤ 2 ^ n :=
          Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ n)
        rw [h2n] at hge
        omega
      refine Or.inr ?_
      exact Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, hm3, hneq⟩, F, hF, hFin,
        hcard, ⟨e⟩⟩
  have hroot' : ∀ k : ↥(ambK V H T), (k : ↥H) ∈ ambV V H →
      (k : ↥H) ∉ pCoreOf 2 (ambK V H T) →
        IsSymplecticTransvection X m n (φ' k) ∨ IsUnitaryTransvection X m n (φ' k) := by
    intro k hkV hkO
    have hkbar : φ' k ∈ barSub (kGenIn V H) φ V := by
      have h1 : φ' k ∈ barSub (ambK V H T) φ' (ambV V H) :=
        mem_barSub.mpr ⟨k, hkV, rfl⟩
      rwa [hbar] at h1
    have hkne : φ' k ≠ 1 := fun h1 => hkO ((hφ'.ker_iff k).mp h1)
    rcases hroot with ⟨-, hr⟩ | ⟨-, hr⟩
    · exact Or.inl (hr (φ' k) hkbar hkne)
    · exact Or.inr (hr (φ' k) hkbar hkne)
  have hN0 : iSub (V.subgroupOf H) ⊤ (ambE V H T) ⊓
      Subgroup.centralizer (ambK V H T : Set ↥H) ≠ ⊥ :=
    seven_twelve (G := ↥H) hConf (AmbientH.hyp711 h hKT) hφ' hn hX
      (by rw [hbar]; exact h2) hroot'
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN0
  have hw_i : (w : ↥H) ∈ iSub (V.subgroupOf H) ⊤ (ambE V H T) := w.2.1
  have hw_c : (w : ↥H) ∈
      Subgroup.centralizer (ambK V H T : Set ↥H) := w.2.2
  have hwneG : (w : G) ≠ 1 := by
    intro h1
    exact hw1 (Subtype.ext (Subtype.ext h1))
  have hwO : (w : G) ∈ pCoreOf 2 (kGenIn V H) := by
    have h1 : (w : ↥H) ∈ pCoreOf 2 (ambK V H T) :=
      iSub_le_pCoreOf_kSub (le_top) hw_i
    change (w : ↥H) ∈ pCoreOf 2 (kSub (V.subgroupOf H) ⊤
      (eSub (V.subgroupOf H) ⊤ (T.subgroupOf H))) at h1
    rw [AmbientH.kSub_eq_kGenIn h hKT, pCoreOf_subgroupOf (kGenIn_le_H h.le_H)] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hwC : (w : G) ∈ Subgroup.centralizer (kGenIn V H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkH : k ∈ H := kGenIn_le_H h.le_H hk
    have hmemK : (⟨k, hkH⟩ : ↥H) ∈ ambK V H T := by
      change (⟨k, hkH⟩ : ↥H) ∈ kSub (V.subgroupOf H) ⊤
        (eSub (V.subgroupOf H) ⊤ (T.subgroupOf H))
      rw [AmbientH.kSub_eq_kGenIn h hKT]
      exact Subgroup.mem_subgroupOf.mpr hk
    have hcomm := Subgroup.mem_centralizer_iff.mp hw_c ⟨k, hkH⟩ hmemK
    have hval := congrArg Subtype.val hcomm
    simpa using hval
  let K : Subgroup G := kGenIn V H
  let O : Subgroup G := pCoreOf 2 K
  let N : Subgroup G := O ⊓ Subgroup.centralizer (K : Set G)
  have hKH : K ≤ H := kGenIn_le_H h.le_H
  have hOH : O ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH
  have hNH : N ≤ H := fun _ hx => hOH hx.1
  have hwN : (w : G) ∈ N := ⟨hwO, hwC⟩
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hw1' : (w : G) = 1 := by
      have hmem := hwN
      rw [hbot] at hmem
      simpa using hmem
    exact hwneG hw1'
  have hKnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr
      (h.le_normalizer_kGenIn_of_eq_sup hKT)
  have hOnormal : (O.subgroupOf H).Normal := pCoreOf_subgroupOf_normal hKH hKnormal
  have hH_le_NO : H ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mp hOnormal
  have hCnormal : ((Subgroup.centralizer (K : Set G)).subgroupOf
      (Subgroup.normalizer (K : Set G))).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer (K : Set G)
  have hH_le_NC : H ≤ Subgroup.normalizer
      ((Subgroup.centralizer (K : Set G)) : Set G) :=
    (h.le_normalizer_kGenIn_of_eq_sup hKT).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (K : Set G))).mp hCnormal)
  have hH_le_NN : H ≤ Subgroup.normalizer (N : Set G) :=
    (le_inf hH_le_NO hH_le_NC).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := O)
        (K := Subgroup.centralizer (K : Set G)))
  have hNnormal : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hH_le_NN
  have hN2 : IsPGroup 2 N := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_inf_left
  have hNT : N ≤ T := IsSylowIn.le_of_normal h.sylow_H hNH hNnormal hN2
  have hT_le_H : T ≤ H := h.T_le_H
  have hNsubT_normal : (N.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).mpr (hT_le_H.trans hH_le_NN)
  haveI : (N.subgroupOf T).Normal := hNsubT_normal
  have hNsubT_ne : N.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hNne
    have hmap : (N.subgroupOf T).map T.subtype = N :=
      Subgroup.map_subgroupOf_eq_of_le hNT
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  haveI : Group.IsNilpotent ↥T := h.sylow_H.isPGroup.isNilpotent
  have hZ : N.subgroupOf T ⊓ Subgroup.center ↥T ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hNsubT_ne
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hzN : ((z : ↥T) : G) ∈ N := Subgroup.mem_subgroupOf.mp z.2.1
  refine ⟨((z : ↥T) : G), (z : ↥T).2, ?_, ?_, ?_⟩
  · intro h1
    exact hz1 (Subtype.ext (Subtype.ext h1))
  · intro t ht
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2.2 ⟨t, ht⟩)
    simpa using h.symm
  · intro k hk
    have h := Subgroup.mem_centralizer_iff.mp hzN.2 k hk
    simpa using h.symm

theorem not_shape86DeltaT'_of_centralizersInM (hConf : SpURootConfiguration) (h : Hyp83 V H T)
    (hKT : H = kGenIn V H ⊔ T) (hC : CentralizersInM V H T) : ¬ Shape86DeltaT' V H T := by
  intro hδ
  obtain ⟨z, hzT, hz1, hzT', hzK⟩ := exists_central_of_shape86DeltaT' hConf h hKT hδ
  have hcent : kGenIn V H ⊔ T ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hzK k hk).symm)
      (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (hzT' t ht).symm)
  exact h.not_isCalH0 (isCalH0_of_le_normalizer h.elemAbelian h.isCalH
    ((le_inf le_rfl (hKT.le.trans hcent)).trans (hC z hzT hzT' hz1)))

end CFSG.LocalAnalysis.WeakClosure81

end
