module

public import CFSG.Quasithin.Vol2.Ch3Sec3KGSylow
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S4c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

theorem not_forall_comm (hB : IsB₀ X T D B₀) : ¬ ∀ d ∈ D, ∀ t ∈ T, ⁅d, t⁆ ∈ B₀ := by
  intro hc
  apply H.hD
  obtain ⟨-, hT₀, -⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  refine Main3324.le_normalizer_of_conj fun d hd r hr => ?_
  have hrT := H.R_le_T hr
  have hdr : d * r * d⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (H.h.DN hd) r).mp hrT
  have hb : ⁅d, r⁆ ∈ T ⊓ B₀ := by
    refine ⟨?_, hc d hd r hrT⟩
    rw [commutatorElement_def]
    exact T.mul_mem hdr (T.inv_mem hrT)
  rw [hT₀] at hb
  have e : d * r * d⁻¹ = ⁅d, r⁆ * r := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (pCoreOf 2 (X ⊔ T)).mul_mem (H.pCoreOf_le_R hb) hr

theorem false_of_oddNorm_comm (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    (key : ∀ q ∈ Subgroup.normalizer ((star (X ⊔ T ⊔ D) B₀ T :
      Subgroup (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D))) :
        Set (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D))),
      Odd (orderOf q) → ∀ s ∈ star (X ⊔ T ⊔ D) B₀ T, q * s = s * q) : False := by
  apply H.not_forall_comm hB
  intro d hd t ht
  have hdB : d ∈ X ⊔ T ⊔ D := Subgroup.mem_sup_right hd
  have htB : t ∈ X ⊔ T ⊔ D := (le_sup_right.trans le_sup_left : T ≤ X ⊔ T ⊔ D) ht
  have hodd : Odd (orderOf (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨d, hdB⟩)) := by
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd _ _)
    rw [Subgroup.orderOf_mk]
    have h1 : orderOf (⟨d, hd⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat H.h.Dodd h1
  exact (mk_comm_iff hdB htB).mp (key _ (mk_mem_normalizer_star hdB (H.h.DN hd)) hodd _
    (mk_mem_star htB ht))

theorem exists_conj (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] {K : Subgroup G} (hK : K ∈ cComp (X ⊔ T ⊔ D))
    (hBK : X ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G)) (hKB₀ : ¬ K ≤ B₀) :
    ∃ φ : (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) →* MulAut ↥(star (X ⊔ T ⊔ D) B₀ K),
      Function.Injective φ ∧
        (∀ k : ↥(star (X ⊔ T ⊔ D) B₀ K),
          φ (k : ↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) = MulAut.conj k) ∧
        IsSylowTwoOf ((star (X ⊔ T ⊔ D) B₀ T).map φ) φ.range := by
  have hNn : (star (X ⊔ T ⊔ D) B₀ K).Normal := star_normal hBK
  let φ : (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) →*
      MulAut ↥(star (X ⊔ T ⊔ D) B₀ K) := MulAut.conjNormal
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    have hc := H.centralizer_star_Y hA hB
    rw [← H.star_eq_star_Y hB hK hBK hKB₀] at hc
    rw [← hc, Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := congrArg (fun a : MulAut ↥(star (X ⊔ T ⊔ D) B₀ K) =>
      ((a ⟨n, hn⟩ : ↥(star (X ⊔ T ⊔ D) B₀ K)) : ↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)))
      (MonoidHom.mem_ker.mp hq)
    simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc n * q = q * n * q⁻¹ * q := by rw [h1]
      _ = q * n := by group
  refine ⟨φ, hinj, fun k => MulAut.conjNormal_val, ?_⟩
  have hsyl := H.isSylowTwoOf_star_T (B₀ := B₀)
  refine ⟨Subgroup.map_le_range φ _, hsyl.2.1.map φ, fun h2 => hsyl.2.2 ?_⟩
  have h1 := Subgroup.relIndex_map_map_of_injective (star (X ⊔ T ⊔ D) B₀ T) ⊤ hinj
  rw [← MonoidHom.range_eq_map] at h1
  have h3 : ((star (X ⊔ T ⊔ D) B₀ T).map φ).relIndex φ.range =
      (star (X ⊔ T ⊔ D) B₀ T).relIndex ⊤ := h1
  have h4 : 2 ∣ ((star (X ⊔ T ⊔ D) B₀ T).map φ).relIndex φ.range := h2
  rw [h3] at h4
  exact h4

theorem not_autOddNormCent (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] {K : Subgroup G} (hK : K ∈ cComp (X ⊔ T ⊔ D))
    (hBK : X ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G)) (hKB₀ : ¬ K ≤ B₀) :
    ¬ AutOddNormCent ↥(star (X ⊔ T ⊔ D) B₀ K) := by
  intro hAut
  obtain ⟨φ, hinj, hφK, hS⟩ := H.exists_conj hA hB hK hBK hKB₀
  have hInn : (MulAut.conj : ↥(star (X ⊔ T ⊔ D) B₀ K) →* MulAut ↥(star (X ⊔ T ⊔ D) B₀ K)).range ≤
      φ.range := by
    rintro _ ⟨n, rfl⟩
    exact ⟨_, hφK n⟩
  refine H.false_of_oddNorm_comm hB fun q hq hoq s hs => ?_
  have hqN : φ q ∈ Subgroup.normalizer (((star (X ⊔ T ⊔ D) B₀ T).map φ :
      Subgroup (MulAut ↥(star (X ⊔ T ⊔ D) B₀ K))) : Set (MulAut ↥(star (X ⊔ T ⊔ D) B₀ K))) ⊓
      φ.range :=
    ⟨Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ hq), ⟨q, rfl⟩⟩
  have hc := hAut φ.range _ hInn hS (φ q) hqN (Odd.of_dvd_nat hoq (orderOf_map_dvd φ q)) (φ s)
    (Subgroup.mem_map_of_mem φ hs)
  rw [← map_mul, ← map_mul] at hc
  exact hinj hc

end Hyp3320

end S3320

end CFSG.Quasithin.H13
