module

public import CFSG.Quasithin.H13.L32AC41f
public import CFSG.Quasithin.H13.L32ACSk12

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem l1_star_le_centralizer_of_oddCore (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hl1K : ¬ l1 T L V ≤ K)
    (hO : CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) = modO2Image H (l1 T L V)) :
    modO2Image H (l1 T L V) ≤
      Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lb := modO2Image H (l1 T L V) with hLb
  set Kb := modO2Image H K with hKb
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hl1H : l1 T L V ≤ H := Setting147.l1H' S
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨ψ, hψ⟩ := S14.exists_rep
  obtain ⟨x, hxL, hx3, hfpf⟩ := exists_l1_fpf S.hyp hMod h1222 h1332 h1334
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hx : x ∈ l1 T L V := hl1 ▸ hxL
  have hxH : x ∈ H := hl1H hx
  have hxX := S14.L1_le_X hxL
  have hxLL : x ∈ L := (oTwoUpper_le _ hx).1
  have hψx : ψ ⟨x, hxX⟩ ≠ 1 := by
    intro h
    have hxt := (hψ _).mp h
    have hle : V ≤ fsuV1 T V := fun v hv => hfpf v hv ((L32NSet14.mem_trivSub.mp hxt).2.2 v hv)
    have := Subgroup.card_le_of_le hle
    rw [S14.card_V, S14.card_V1] at this
    omega
  have hψx3 : ψ ⟨x, hxX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxX⟩ : ↥(L32NSet14.nX T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hKbN : Kb.Normal := by
    have : (K.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
    exact Subgroup.Normal.map this _ (QuotientGroup.mk'_surjective _)
  have hLbN : Lb.Normal := hO ▸ (inferInstance : (CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H)).Normal)
  have hx1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ ≠ 1 := by
    intro h
    have hxO : x ∈ pCoreOf 2 H := by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
        Subgroup.mem_subgroupOf] at h
    exact hψx ((hψ _).mpr (pCoreOf_le_trivSub S S14 hxO))
  have hxLb : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ ∈ Lb :=
    mem_modO2Image'.mpr ⟨⟨x, hxH⟩, hx, rfl⟩
  have hcard : Nat.card ↥Lb = 3 := by
    have hodd : Odd (Nat.card ↥Lb) := hO ▸ odd_card_oddCore
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 (l1 T L V)).exists_card_eq
    have hl1c : Nat.card ↥(l1 T L V) = 3 * 2 ^ m := by
      have h := Subgroup.relIndex_mul_card (pCoreOf 2 (l1 T L V)) (l1 T L V)
      rw [relIndex_l1 h1222 h1332 h1334 S.hyp, inf_eq_left.mpr (pCoreOf_le 2 _), hm] at h
      exact h.symm
    have hdvd : Nat.card ↥Lb ∣ 3 * 2 ^ m := by
      have := Subgroup.card_map_dvd (H := (l1 T L V).subgroupOf H)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hl1H).toEquiv, hl1c] at this
    rcases eq_one_or_three_of_odd_dvd hodd hdvd with h1 | h3
    · exfalso
      exact hx1 (Subgroup.mem_bot.mp (Subgroup.eq_bot_of_card_eq Lb h1 ▸ hxLb))
    · exact h3
  have hinf : Lb ⊓ Kb = ⊥ := by
    have hdvd : Nat.card ↥(Lb ⊓ Kb) ∣ 3 := hcard ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hle : Lb ≤ Kb := by
        have := Subgroup.eq_of_le_of_card_ge (inf_le_left : Lb ⊓ Kb ≤ Lb)
          (h3.trans hcard.symm).ge
        rw [← this]
        exact inf_le_right
      exact hl1K (l1_le_of_psi_eq S S14 hψ hK hKn hxX hψx hψx3 hxLL hxX hxH (hle hxLb) rfl)
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ Lb ⊓ Kb := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have : b * a⁻¹ * b⁻¹ ∈ Lb := hLbN.conj_mem _ (inv_mem ha) b
      have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [e]
      exact mul_mem ha this
    · exact mul_mem (hKbN.conj_mem _ hb a) (inv_mem hb)
  rw [hinf, Subgroup.mem_bot] at h1
  have h2 : a * b * a⁻¹ = b := by
    calc a * b * a⁻¹ = a * b * a⁻¹ * b⁻¹ * b := by group
      _ = b := by rw [h1, one_mul]
  calc b * a = a * b * a⁻¹ * a := by rw [h2]
    _ = a * b := by group

theorem l1_star_le_centralizer_of (hN1 : LieSylowOver3) (hN3 : LieBorelThreeInner)
    (h28 : Lemma14_7_28) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (hPGL : Lemma14741PGL) (S : Setting147 G T L V H) {K : Subgroup G}
    (hK : K ∈ cComp H) (hq : CFSG.IsQuasisimple (cStar K))
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHeq : H = K ⊔ (l1 T L V ⊔ T)) {n : ℕ}
    (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    (hl1K : ¬ l1 T L V ≤ K) :
    modO2Image H (l1 T L V) ≤
      Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  by_cases hP : IsPSL 3 2 2 (cStar K ⧸ Subgroup.center (cStar K))
  · rcases h28 G T L V H S with hO | hO
    · exact absurd hP (hPGL G T L V H S K hK hHeq n hn hLie hl1K hO)
    · exact l1_star_le_centralizer_of_oddCore h1222 h1332 h1334 S hK hKn hl1K hO
  · exact l1_star_le_centralizer hN1 hN3 h29 h1222 h1332 h1334 S hK hq hKn hn hLie hl1K hP

end CFSG.Quasithin.H13.L32A.C
