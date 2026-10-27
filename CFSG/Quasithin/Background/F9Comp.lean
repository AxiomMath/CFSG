module

public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_le_of_commutator_commutator_le {Q A P : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (Q : Set G)) (hP : P ≤ Subgroup.normalizer (Q : Set G))
    (hperf : ⁅P, P⁆ = P) (h : ⁅⁅P, A⁆, P⁆ ≤ Q) : ⁅A, P⁆ ≤ Q := by
  let M : Subgroup G := Subgroup.normalizer (Q : Set G)
  let Q' : Subgroup ↥M := Q.subgroupOf M
  let φ : ↥M →* ↥M ⧸ Q' := QuotientGroup.mk' Q'
  let A' : Subgroup ↥M := A.subgroupOf M
  let P' : Subgroup ↥M := P.subgroupOf M
  have hA' : A'.map M.subtype = A := Subgroup.map_subgroupOf_eq_of_le hA
  have hP' : P'.map M.subtype = P := Subgroup.map_subgroupOf_eq_of_le hP
  have hPP : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, hP', hperf]
  have h1 : ⁅⁅P', A'⁆, P'⁆ ≤ Q' := by
    have : (⁅⁅P', A'⁆, P'⁆).map M.subtype ≤ Q := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator, hP', hA']; exact h
    exact Subgroup.map_le_iff_le_comap.mp this
  have h2 : ⁅⁅P'.map φ, A'.map φ⁆, P'.map φ⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact h1
  have h3 : ⁅⁅A'.map φ, P'.map φ⁆, P'.map φ⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (A'.map φ)]; exact h2
  have h4 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h3
  rw [← Subgroup.map_commutator, hPP] at h4
  have h5 : ⁅A', P'⁆ ≤ Q' := by
    have : (⁅A', P'⁆).map φ = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.commutator_comm]; exact h4
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at this
  have h6 : (⁅A', P'⁆).map M.subtype ≤ Q := Subgroup.map_le_iff_le_comap.mpr h5
  rwa [Subgroup.map_commutator, hA', hP'] at h6


theorem commutator_le_pCoreOf_of_solvable {K D : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K))
    (hDK : D ≤ K) (hKD : K ≤ Subgroup.normalizer (D : Set G)) (hD : Group.IsSolvable ↥D) :
    ⁅D, K⁆ ≤ pCoreOf 2 K := by
  let R : Subgroup ↥K := (pCoreOf 2 K).subgroupOf K
  let ψ : ↥K →* ↥K ⧸ R := QuotientGroup.mk' R
  let D' : Subgroup ↥K := D.subgroupOf K
  have hD'n : D'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDK).mpr hKD
  let Db : Subgroup (↥K ⧸ R) := D'.map ψ
  have hDbn : Db.Normal := hD'n.map ψ (QuotientGroup.mk'_surjective R)
  have hD's : Group.IsSolvable ↥D' := Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hDK).toMonoidHom) (Subgroup.subgroupOfEquivOfLe hDK).injective
  have hDs : Group.IsSolvable ↥Db :=
    Group.isSolvable_of_surjective (f := ψ.subgroupMap D') (ψ.subgroupMap_surjective D')
  have hDbZ : Db ≤ Subgroup.center (↥K ⧸ R) := by
    obtain ⟨-, hsimple, ⟨a, b, hab⟩⟩ := hq
    let Z := Subgroup.center (↥K ⧸ R)
    let π : (↥K ⧸ R) →* (↥K ⧸ R) ⧸ Z := QuotientGroup.mk' Z
    have hnorm : (Db.map π).Normal := hDbn.map π (QuotientGroup.mk'_surjective Z)
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Db.map π) with hbot | htop
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
      exact hbot
    · exfalso
      have hsolv : Group.IsSolvable ((↥K ⧸ R) ⧸ Z) := by
        refine Group.isSolvable_of_surjective (f := π.comp Db.subtype) fun y => ?_
        have hy : y ∈ Db.map π := htop ▸ Subgroup.mem_top y
        obtain ⟨d, hd, hdy⟩ := hy
        exact ⟨⟨d, hd⟩, hdy⟩
      exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)
  refine Subgroup.commutator_le.mpr fun d hd k hk => ?_
  let dK : ↥K := ⟨d, hDK hd⟩
  let kK : ↥K := ⟨k, hk⟩
  have hψd : ψ dK ∈ Db := Subgroup.mem_map_of_mem ψ (show dK ∈ D' from hd)
  have hc : ⁅ψ dK, ψ kK⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hDbZ hψd) (ψ kK)).symm
  have h1 : ψ ⁅dK, kK⁆ = 1 := by rw [map_commutatorElement]; exact hc
  have h2 : ⁅dK, kK⁆ ∈ R := (QuotientGroup.eq_one_iff _).mp h1
  have h3 : ((⁅dK, kK⁆ : ↥K) : G) ∈ pCoreOf 2 K := h2
  simpa [commutatorElement_def] using h3

section Fin

variable [Finite G]

theorem pCoreOf_le_pCoreOf_of_isSubnormal {H K : Subgroup G} (h : IsSubnormal H K) :
    pCoreOf 2 H ≤ pCoreOf 2 K := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN _ ih =>
    refine le_trans ?_ ih
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 H).trans hle) ?_ (pCoreOf_isPGroup 2 H)
    intro m hm
    have hmH : m ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN hm
    exact normalizer_le_normalizer_pCoreOf 2 H hmH

omit [Finite G] in
theorem conjSub_mem_cComp_of_mem {H K : Subgroup G} (hK : K ∈ cComp H) {t : G} (ht : t ∈ H) :
    conjSub t K ∈ cComp H := by
  have h1 := cComp_map_mulEquiv (MulAut.conj t) hK
  have h2 : H.map (MulAut.conj t).toMonoidHom = H := F7.conjSub_eq_of_mem ht
  rw [h2] at h1
  exact h1

theorem exists_le_or_commutator_le_pCoreOf {H T K N : Subgroup G}
    (hK : K ∈ cComp H) (hTH : T ≤ H)
    (hq : CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K))
    (hNK₀ : N ≤ conjClosure K T) (hK₀N : conjClosure K T ≤ Subgroup.normalizer (N : Set G))
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) :
    conjClosure K T ≤ N ∨ ⁅N, conjClosure K T⁆ ≤ pCoreOf 2 H := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hK₀H : conjClosure K T ≤ H := conjClosure_le fun t ht z hz =>
    H.mul_mem (H.mul_mem (hTH ht) (hKH hz)) (H.inv_mem (hTH ht))
  have hNH : N ≤ H := hNK₀.trans hK₀H
  have hspan : conjClosure K T ≤ cCompSpan H := by
    refine conjClosure_le fun t ht z hz => ?_
    have h1 : conjSub t K ∈ cComp H := conjSub_mem_cComp_of_mem hK (hTH ht)
    exact le_cCompSpan h1 (mem_conjSub.mpr (by simpa [mul_assoc] using hz))
  have hnormK : cCompSpan H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_cCompSpan hK)).mp
      (cComp_normal_span_of_le hK).2
  have hNnK : N ≤ Subgroup.normalizer (K : Set G) := hNK₀.trans (hspan.trans hnormK)
  rcases cComp_commutator_dichotomy_of_le hK hNH with ⟨-, hsolv⟩ | hconj
  · right
    have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
    have hDK : ⁅K, N⁆ ≤ K := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hNnK
    have hKD : K ≤ Subgroup.normalizer ((⁅K, N⁆ : Subgroup G) : Set G) :=
      Subgroup.normalizer_commutator_ge_left K N
    have hD := commutator_le_pCoreOf_of_solvable hq hDK hKD hsolv
    have hKQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
      pCoreOf_le_pCoreOf_of_isSubnormal (subnormal_of_mem_cComp hK)
    have hKperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hK
    have hKN : ⁅N, K⁆ ≤ pCoreOf 2 H :=
      commutator_le_of_commutator_commutator_le (hNH.trans hQn) (hKH.trans hQn) hKperf
        (hD.trans hKQ)
    have hKN' : ⁅K, N⁆ ≤ pCoreOf 2 H := by rw [Subgroup.commutator_comm]; exact hKN
    have hS : conjClosure K T ≤ centralizerMod (pCoreOf 2 H) H N := by
      refine conjClosure_le fun t ht z hz => ?_
      have htH : t ∈ H := hTH ht
      have hxH : t * z * t⁻¹ ∈ H := H.mul_mem (H.mul_mem htH (hKH hz)) (H.inv_mem htH)
      refine ⟨hxH, hQn hxH, fun n hn => ?_⟩
      have hn' : t⁻¹ * n * t ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (hTN (T.inv_mem ht)) n).mp hn
        simpa [mul_assoc] using this
      have h1 : z * (t⁻¹ * n * t) * z⁻¹ * (t⁻¹ * n * t)⁻¹ ∈ pCoreOf 2 H :=
        hKN' (Subgroup.commutator_mem_commutator hz hn')
      have h2 := (Subgroup.mem_normalizer_iff.mp (hQn htH) _).mp h1
      have e : t * (z * (t⁻¹ * n * t) * z⁻¹ * (t⁻¹ * n * t)⁻¹) * t⁻¹ =
          (t * z * t⁻¹) * n * (t * z * t⁻¹)⁻¹ * n⁻¹ := by group
      rwa [e] at h2
    refine Subgroup.commutator_le.mpr fun n hn k hk => ?_
    have h1 : k * n * k⁻¹ * n⁻¹ ∈ pCoreOf 2 H := (hS hk).2.2 n hn
    have h2 := (pCoreOf 2 H).inv_mem h1
    have e : (k * n * k⁻¹ * n⁻¹)⁻¹ = ⁅n, k⁆ := by simp [commutatorElement_def, mul_assoc]
    rwa [e] at h2
  · left
    have h1 : K ≤ ⁅K, N⁆ := hconj ▸ le_conjClosure K N
    have h2 : ⁅K, N⁆ ≤ N :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp ((le_conjClosure K T).trans hK₀N)
    have hKN : K ≤ N := h1.trans h2
    exact conjClosure_le fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (hTN ht) z).mp (hKN hz)

end Fin

end CFSG.Quasithin
