module

public import CFSG.Quasithin.H13.A6S13813f
public import CFSG.Quasithin.H13.A6S13813e
public import CFSG.Quasithin.H13.A6S1388

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

attribute [local instance] commGroupOfFact

theorem A6P.conjSub_eq_of_mem_normalizer {G : Type} [Group G] {N : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) : conjSub x N = N := by
  ext z
  rw [mem_conjSub]
  have := (Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * z * x))
  rw [show x * (x⁻¹ * z * x) * x⁻¹ = z by group] at this
  exact this

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section PSec

variable (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
  [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))]
  {hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G)}
  {hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G)} {p : ℕ}
  {P : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)))}
  (hP : A6P.PData S.L1 T L H (actH hV₁ hIH)
    (((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH)) p P)
include hS hH hP

theorem gen_of_P {K : Subgroup G} (hKH : K ≤ H) (hKQ : ¬ K ≤ pCoreOf 2 H)
    (hconj : ∃ h' ∈ H, conjSub h' K ≤ pCoreOf 2 (S.L1 ⊔ T)) :
    H = conjClosure K H ⊔ (S.L1 ⊔ T) := by
  have hF := (hS.hF H hH).toHypF91
  set φ := actH hV₁ hIH with hφ
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  obtain ⟨h', hh'H, hK'⟩ := hconj
  obtain ⟨u, huK, huQ⟩ : ∃ u ∈ K, u ∉ pCoreOf 2 H := by
    by_contra hcon
    push Not at hcon
    exact hKQ fun x hx => hcon x hx
  have hu'H : h' * u * h'⁻¹ ∈ H := H.mul_mem (H.mul_mem hh'H (hKH huK)) (H.inv_mem hh'H)
  have hu'R : h' * u * h'⁻¹ ∈ pCoreOf 2 (S.L1 ⊔ T) := hK' (mul_mem_conjSub huK)
  have hs : φ ⟨_, hu'H⟩ ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map φ :=
    ⟨⟨_, hu'H⟩, Subgroup.mem_subgroupOf.2 hu'R, rfl⟩
  have hs1 : φ ⟨_, hu'H⟩ ≠ 1 := by
    rw [Ne, hker]
    intro hq
    apply huQ
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hh'H)) _).mp hq
    simpa [mul_assoc] using this
  have hPC := S.P_le_closure hS hH hP hs hs1
  set N := conjClosure K H with hN
  have hCN : Subgroup.closure {y | ∃ x ∈ φ.range, y = x * φ ⟨_, hu'H⟩ * x⁻¹} ≤
      (N.subgroupOf H).map φ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, ⟨h₁, rfl⟩, rfl⟩
    refine ⟨h₁ * ⟨_, hu'H⟩ * h₁⁻¹, Subgroup.mem_subgroupOf.2 ?_, by
      rw [map_mul, map_mul, map_inv]⟩
    have e : ((h₁ * ⟨_, hu'H⟩ * h₁⁻¹ : ↥H) : G) = ((h₁ : G) * h') * u * ((h₁ : G) * h')⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact mem_conjClosure (H.mul_mem h₁.2 hh'H) huK
  have hQT : pCoreOf 2 H ≤ T :=
    pCoreOf_le_of_sylow S.h13.sylow (le_sup_right.trans hH.1.1)
  have hPhH : oTwoRes ((P.comap φ).map H.subtype) ≤ H :=
    (oTwoRes_le _).trans (Subgroup.map_subtype_le _)
  have hPh : oTwoRes ((P.comap φ).map H.subtype) ≤ N ⊔ T := by
    intro x hx
    have hφx := hP.map_mem ⟨x, hPhH hx⟩ hx
    obtain ⟨n, hnN, hn⟩ := Subgroup.mem_map.1 (hCN (hPC hφx))
    have hq : ((n⁻¹ * ⟨x, hPhH hx⟩ : ↥H) : G) ∈ pCoreOf 2 H :=
      (hker _).1 (by rw [map_mul, map_inv, hn, inv_mul_cancel])
    have e : x = (n : G) * ((n⁻¹ * ⟨x, hPhH hx⟩ : ↥H) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hnN))
      (Subgroup.mem_sup_right (hQT hq))
  have hNH : N ≤ H := conjClosure_le fun k hk z hz => H.mul_mem (H.mul_mem hk (hKH hz))
    (H.inv_mem hk)
  apply le_antisymm
  · calc H = (oTwoRes ((P.comap φ).map H.subtype) ⊔ S.L1) ⊔ T := hP.eq
      _ ≤ N ⊔ (S.L1 ⊔ T) := by
        refine sup_le (sup_le (hPh.trans (sup_le le_sup_left (le_sup_right.trans le_sup_right)))
          (le_sup_left.trans le_sup_right)) (le_sup_right.trans le_sup_right)
  · exact sup_le hNH hF.L₁T_le_H

end PSec

theorem stab_gen (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hgenH : ∀ K : Subgroup G, K ≤ H → ¬ K ≤ pCoreOf 2 H →
      (∃ h' ∈ H, conjSub h' K ≤ pCoreOf 2 (S.L1 ⊔ T)) → H = conjClosure K H ⊔ (S.L1 ⊔ T))
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (hDH : F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H) :
    stab γ = conjClosure (conjClosure S.V3 H) (stab γ) ⊔ (stab γ ⊓ stab γ') := by
  have hF := hS.hF H hH
  obtain ⟨δ, δ', k, y, sk, hyγ, -, hUδ, -, hDHk, hDγk⟩ :=
    hF.exists_symmetric_setup s (hF.not_Vγ_le_ballStab_of_lt s hDγ)
  set Uδ := F8.Uγ S.V3 H (k : G) with hUδdef
  have hUδH : Uδ ≤ H := hF.Uγ_le_H sk
  have hUδQ : ¬ Uδ ≤ pCoreOf 2 H := by
    intro hle
    have hlt : F8.Dγ S.V3 (fsuV1 T V) H (k : G) < Uδ := by
      rw [hDγk, hUδ]
      refine lt_of_le_of_ne (conjSub_mono _ hDH.le) fun he => hDH.ne ?_
      exact (conjSub_inj _).1 he
    rw [hF.Dγ_eq_inf_pCoreOf sk, inf_of_le_left hle] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨h', hh', hβ'⟩ := A6P.exists_conj_Vγ_le hF sk
  have hHN := hgenH Uδ hUδH hUδQ ⟨h', hh', (conjSub_mono _ hF.Uγ_le_Vγ).trans hβ'⟩
  have hnb : y • γ' ∈ nbrs (F8.γ₁ T L H) := by
    rw [← hyγ]
    exact (smul_adj y).2 (mem_nbrs_symm s.nbr)
  have hγ₀ : F8.γ₀ T L H ∈ nbrs (F8.γ₁ T L H) := adj_γ₀_γ₁.symm
  obtain ⟨x, hxst, hxγ⟩ := stab_transitive_on_nbrs hγ₀ hnb
  have hxH : (x : G) ∈ H := by rwa [stab_γ₁ hF.amalgamHypV.le₂] at hxst
  have hstab1 : stab (y • γ') = conjSub (x : G) (L ⊔ T) := by
    rw [← hxγ, stab_smul, stab_γ₀ hF.amalgamHypV.le₁]
  have hHx : conjSub (x : G) H = H := A6P.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hxH)
  have hNx : conjSub (x : G) (conjClosure Uδ H) = conjClosure Uδ H :=
    A6P.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Uδ H hxH)
  have hinf : H ⊓ stab (y • γ') = conjSub (x : G) (S.L1 ⊔ T) := by
    calc H ⊓ stab (y • γ') = conjSub (x : G) H ⊓ conjSub (x : G) (L ⊔ T) := by
          rw [hstab1, hHx]
      _ = conjSub (x : G) ((L ⊔ T) ⊓ H) := by rw [← conjSub_inf, inf_comm]
      _ = conjSub (x : G) (S.L1 ⊔ T) := by rw [hF.toHypF91.LT_inf_H]; rfl
  have hH2 : H = conjClosure Uδ H ⊔ (H ⊓ stab (y • γ')) := by
    rw [hinf]
    calc H = conjSub (x : G) H := hHx.symm
      _ = conjSub (x : G) (conjClosure Uδ H ⊔ (S.L1 ⊔ T)) := congrArg (conjSub (x : G)) hHN
      _ = conjClosure Uδ H ⊔ conjSub (x : G) (S.L1 ⊔ T) := by rw [conjSub_sup, hNx]
  have hstabγ : stab γ = conjSub (y : G)⁻¹ H := by
    have h3 := stab_smul y γ
    rw [hyγ, stab_γ₁ hF.amalgamHypV.le₂] at h3
    calc stab γ = conjSub (y : G)⁻¹ (conjSub (y : G) (stab γ)) := (conjSub_conjSub_inv _ _).symm
      _ = conjSub (y : G)⁻¹ H := by rw [← h3]
  have hstabγ' : stab γ' = conjSub (y : G)⁻¹ (stab (y • γ')) := by
    rw [stab_smul, conjSub_conjSub_inv]
  have hUHy : conjSub (y : G)⁻¹ Uδ = conjClosure S.V3 H := by
    rw [hUδ, conjSub_conjSub_inv]
  have h2 := congrArg (conjSub (y : G)⁻¹) hH2
  rw [conjSub_sup, conjSub_inf, conjSub_conjClosure_eq, hUHy, ← hstabγ, ← hstabγ'] at h2
  exact h2

theorem false_of_noFour (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h139 : Stmt13_3_9) (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hsol : Group.IsSolvable ↥H)
    (hmin : ∀ K ∈ S.Hz, K ≤ H → K = H)
    (hno : ∀ a ∈ pCoreOf 2 (S.L1 ⊔ T), ∀ b ∈ pCoreOf 2 (S.L1 ⊔ T), a ∈ H → b ∈ H →
      a * a ∈ pCoreOf 2 H → b * b ∈ pCoreOf 2 H → a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 H →
      a ∈ pCoreOf 2 H ∨ b ∈ pCoreOf 2 H ∨ a⁻¹ * b ∈ pCoreOf 2 H) : False := by
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF1.isElemAbelian_tilde⟩
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF1.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  set φ := actH hV₁ hIH with hφ
  set Q := pCoreOf 2 H with hQ
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ Q := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hQ, hF1.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  have hQconj : ∀ x ∈ H, ∀ q, x * q * x⁻¹ ∈ Q ↔ q ∈ Q := by
    intro x hx q
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hx) q)
    exact this.symm
  have hnt := S.no_transv_of_solvable hS hH hsol
  obtain ⟨γ, γ', g, s, hDγ, hDH, hpos, hle, -⟩ := S.case2_of_no_transv hF hnt
  obtain ⟨h, hhH, hβ⟩ := A6P.exists_conj_Vγ_le hF s
  have hVγH : F8.Uγ V H (g : G) ≤ H := hF.Vγ_le_H s
  have hUV : F8.Uγ S.V3 H (g : G) ≤ F8.Uγ V H (g : G) := hF.Uγ_le_Vγ
  have hVab := hF.isElemAbelian_Vγ (g := g)
  have hVcomm : ∀ a ∈ F8.Uγ V H (g : G), ∀ b ∈ F8.Uγ V H (g : G), a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hVab.1.is_comm.comm (⟨a, ha⟩ : ↥(F8.Uγ V H (g : G)))
      ⟨b, hb⟩)
  have hVsq : ∀ a ∈ F8.Uγ V H (g : G), a * a = 1 := fun a ha => by
    rw [← sq]; exact hVab.2 a ha
  have hDγQ := hF.Dγ_eq_inf_pCoreOf s
  obtain ⟨u₀, hu₀U, hu₀Q⟩ : ∃ u ∈ F8.Uγ S.V3 H (g : G), u ∉ Q := by
    by_contra hcon
    push Not at hcon
    rw [hDγQ, inf_of_le_left (fun x hx => hcon x hx)] at hDγ
    exact lt_irrefl _ hDγ
  have hu₀V := hUV hu₀U
  have huH : h * u₀ * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hhH (hVγH hu₀V)) (H.inv_mem hhH)
  have huR : h * u₀ * h⁻¹ ∈ pCoreOf 2 (S.L1 ⊔ T) := hβ (mul_mem_conjSub hu₀V)
  have huQ : h * u₀ * h⁻¹ ∉ Q := fun h1 => hu₀Q ((hQconj h hhH u₀).1 h1)
  have key : ∀ v ∈ F8.Uγ V H (g : G), v ∈ Q ∨ u₀⁻¹ * v ∈ Q := by
    intro v hv
    have hwH : h * v * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hhH (hVγH hv)) (H.inv_mem hhH)
    have hwR : h * v * h⁻¹ ∈ pCoreOf 2 (S.L1 ⊔ T) := hβ (mul_mem_conjSub hv)
    have hsq : ∀ a ∈ F8.Uγ V H (g : G), h * a * h⁻¹ * (h * a * h⁻¹) ∈ Q := fun a ha => by
      rw [show h * a * h⁻¹ * (h * a * h⁻¹) = h * (a * a) * h⁻¹ by group, hVsq a ha]
      simp
    have hcm : h * u₀ * h⁻¹ * (h * v * h⁻¹) * (h * u₀ * h⁻¹)⁻¹ * (h * v * h⁻¹)⁻¹ ∈ Q := by
      rw [show h * u₀ * h⁻¹ * (h * v * h⁻¹) * (h * u₀ * h⁻¹)⁻¹ * (h * v * h⁻¹)⁻¹ =
        h * (u₀ * v * u₀⁻¹ * v⁻¹) * h⁻¹ by group, hVcomm u₀ hu₀V v hv]
      simp
    rcases hno _ huR _ hwR huH hwH (hsq u₀ hu₀V) (hsq v hv) hcm with h1 | h1 | h1
    · exact absurd h1 huQ
    · exact Or.inl ((hQconj h hhH v).1 h1)
    · right
      rw [show (h * u₀ * h⁻¹)⁻¹ * (h * v * h⁻¹) = h * (u₀⁻¹ * v) * h⁻¹ by group] at h1
      exact (hQconj h hhH _).1 h1
  have hVUQ : F8.Uγ V H (g : G) ≤ F8.Uγ S.V3 H (g : G) ⊔ Q := by
    intro v hv
    rcases key v hv with h1 | h1
    · exact Subgroup.mem_sup_right h1
    · rw [show v = u₀ * (u₀⁻¹ * v) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu₀U) (Subgroup.mem_sup_right h1)
  have h1 : mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1 := by
    have hU2 : IsPGroup 2 ↥(F8.Uγ S.V3 H (g : G)) :=
      isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
    have hidx := HypF98.relIndex_eq_two_pow_mIdx
      (Y := F8.Dγ S.V3 (fsuV1 T V) H (g : G)) hU2
    have hdvd : ((F8.Dγ S.V3 (fsuV1 T V) H (g : G)).subgroupOf
        (F8.Uγ S.V3 H (g : G))).index ∣ 2 := by
      rw [Subgroup.index_dvd_two_iff]
      refine ⟨(⟨u₀, hu₀U⟩ : ↥(F8.Uγ S.V3 H (g : G)))⁻¹, fun b => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hDγQ]
      rcases key b (hUV b.2) with h2 | h2
      · exact Or.inr ⟨b.2, h2⟩
      · left
        refine ⟨(b * (⟨u₀, hu₀U⟩ : ↥(F8.Uγ S.V3 H (g : G)))⁻¹).2, ?_⟩
        have hc : (b : G) * u₀⁻¹ = u₀⁻¹ * b :=
          (hVcomm _ (hUV b.2) _ (hUV ((F8.Uγ S.V3 H (g : G)).inv_mem hu₀U))).trans rfl
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hc]
        exact h2
    have h2 : 2 ^ mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) ∣ 2 ^ 1 := by
      rw [← hidx, pow_one]
      exact hdvd
    have h3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 h2
    omega
  have hV1 := S.V1_le_Uγ_of_solvable hS hH hsol s hDγ hDH hle h1
  have hA2 : IsPGroup 2 ↥(((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map φ) := fun x => by
    obtain ⟨k, hk⟩ := S.pow_two_pow_eq_one_of_mem_R1 x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hA1 : ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map φ ≠ ⊥ := by
    intro hbot
    have hmem : φ ⟨_, huH⟩ ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map φ :=
      ⟨⟨_, huH⟩, Subgroup.mem_subgroupOf.2 huR, rfl⟩
    rw [hbot, Subgroup.mem_bot, hker] at hmem
    exact huQ hmem
  obtain ⟨p, P, hP⟩ := S.exists_P h139 hS hH hsol hmin hV₁ hIH le_rfl hA2 hA1
  have hgen := S.stab_gen hS hH (fun K hKH hKQ hc => S.gen_of_P hS hH hP hKH hKQ hc) s hDγ hDH
  exact S.lemma13_8_11_one hS.hNS h13315 h1356two hH hF h13314 s hgen (Or.inl hV1) hVUQ

end Setting4

@[expose] def Case13813Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, Group.IsSolvable ↥H → (∀ K ∈ S.Hz, K ≤ H → K = H) →
      ∀ a ∈ pCoreOf 2 (S.L1 ⊔ T), ∀ b ∈ pCoreOf 2 (S.L1 ⊔ T), a ∈ H → b ∈ H →
        a * a ∈ pCoreOf 2 H → b * b ∈ pCoreOf 2 H → a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 H →
        a ∉ pCoreOf 2 H → b ∉ pCoreOf 2 H → a⁻¹ * b ∉ pCoreOf 2 H → False

theorem lem13813_of (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h139 : Stmt13_3_9)
    (hfour : Case13813Four) : Lem13813 := by
  refine lem13813_of_core fun G _ _ T L V S hS H hH hsol hmin => ?_
  refine S.false_of_noFour h13314 h13315 h1356two h139 hS hH hsol hmin
    fun a ha b hb haH hbH haa hbb hab => ?_
  by_contra hcon
  push Not at hcon
  exact hfour G T L V S hS H hH hsol hmin a ha b hb haH hbH haa hbb hab hcon.1 hcon.2.1 hcon.2.2

end CFSG.Quasithin.H13.A6

