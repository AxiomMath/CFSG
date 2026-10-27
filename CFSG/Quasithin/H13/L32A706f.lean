module

public import CFSG.Quasithin.H13.L32A706e
public import CFSG.Quasithin.H13.L32ATJ1a

public section

namespace CFSG.Quasithin.H13.L32A.M76

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem relIndex_l1_T (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3 ∧
      (pCoreOf 2 (l1 T L V ⊔ T)).relIndex T = 2 := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  have h3 := S14.Lp3
  have h2 := S14.index2_eq
  rw [show L₁Of L (fsuV1 T V) = l1 T L V from oTwoRes_eq_oTwoUpper _] at h3 h2
  exact ⟨h3, h2⟩

omit [Finite G] in
theorem normal_pCoreOf_l1 : ((pCoreOf 2 (l1 T L V)).subgroupOf (l1 T L V)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_pCoreOf 2 _)

theorem l1_cube_eq_one (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {x : G} (hx : x ∈ l1 T L V) (hodd : Odd (orderOf x)) : x ^ 3 = 1 := by
  have := normal_pCoreOf_l1 (T := T) (L := L) (V := V)
  have h3 := TJ1.pow_mem_of_relIndex (relIndex_l1_T S h1222 h1332 h1334).1 hx
  obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 (l1 T L V) ⟨_, h3⟩
  have hj' : (x ^ 3) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have h1 : orderOf (x ^ 3) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
  have h2 : orderOf (x ^ 3) ∣ orderOf x := orderOf_pow_dvd 3
  have hcop : Nat.Coprime (orderOf x) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h2) h1)

theorem pCoreOf_l1_le_R1 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2) :
    pCoreOf 2 (l1 T L V) ≤ pCoreOf 2 (l1 T L V ⊔ T) :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
    ((sup_le Subgroup.le_normalizer (Setting147.T_le_N_l1 S h1332)).trans
      (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem mem_cosets (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {l x : G} (hl : l ∈ l1 T L V) (hlO : l ∉ pCoreOf 2 (l1 T L V))
    (hx : x ∈ l1 T L V) :
    x ∈ pCoreOf 2 (l1 T L V) ∨ l⁻¹ * x ∈ pCoreOf 2 (l1 T L V) ∨
      l * x ∈ pCoreOf 2 (l1 T L V) := by
  have h3 := (relIndex_l1_T S h1222 h1332 h1334).1
  have hn := normal_pCoreOf_l1 (T := T) (L := L) (V := V)
  set O := pCoreOf 2 (l1 T L V) with hO
  have hN : l1 T L V ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 _
  have hconj : ∀ g ∈ l1 T L V, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (Subgroup.mem_normalizer_iff.mp (hN hg) o).mp ho
  have hsub : O ⊔ Subgroup.zpowers l ≤ l1 T L V :=
    sup_le (pCoreOf_le 2 _) (Subgroup.zpowers_le.mpr hl)
  rcases TJ1.eq_or_eq_of_relIndex_prime Nat.prime_three h3 le_sup_left hsub with he | he
  · exact absurd (he ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers l)) hlO
  have hxF : x ∈ O ⊔ Subgroup.zpowers l := he ▸ hx
  obtain ⟨o, ho, z, hz, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
    ((Subgroup.zpowers_le.mpr hl).trans hN)).mp hxF
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hl3 : l ^ 3 ∈ O := TJ1.pow_mem_of_relIndex h3 hl
  have hl3z : l ^ (3 * (k / 3)) ∈ O := by
    rw [zpow_mul]
    exact O.zpow_mem (by simpa using hl3) _
  have hk : l ^ k = l ^ (3 * (k / 3)) * l ^ (k % 3) := by
    rw [← zpow_add, Int.mul_ediv_add_emod]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have ho' : o * l ^ (3 * (k / 3)) ∈ O := O.mul_mem ho hl3z
  rw [hk, ← mul_assoc]
  set o' := o * l ^ (3 * (k / 3))
  rcases hr with hr | hr | hr <;> rw [hr]
  · left; simpa using ho'
  · right; left
    simpa [mul_assoc] using hconj _ (inv_mem hl) _ ho'
  · right; right
    have e : l * (o' * l ^ (2 : ℤ)) = (l * o' * l⁻¹) * l ^ 3 := by group
    rw [e]
    exact O.mul_mem (hconj _ hl _ ho') hl3

theorem conj_mul_mem_of_not_mem (S : Setting147 G T L V H) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {t l : G} (ht : t ∈ T)
    (htR : t ∉ pCoreOf 2 (l1 T L V ⊔ T)) (hl : l ∈ l1 T L V) (hlO : l ∉ pCoreOf 2 (l1 T L V)) :
    t * l * t⁻¹ * l ∈ pCoreOf 2 (l1 T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h3, h2⟩ := relIndex_l1_T S h1222 h1332 h1334
  set O := pCoreOf 2 (l1 T L V) with hO
  set R := pCoreOf 2 (l1 T L V ⊔ T) with hR
  have hTN : T ≤ Subgroup.normalizer (l1 T L V : Set G) := Setting147.T_le_N_l1 S h1332
  have hTO : T ≤ Subgroup.normalizer (O : Set G) := hTN.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hOR : O ≤ R := pCoreOf_l1_le_R1 S h1332
  have hRT : R ≤ T := Setting147.R1_le_T S
  have hLO : l1 T L V ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 _
  have hconjO : ∀ g ∈ l1 T L V, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (Subgroup.mem_normalizer_iff.mp (hLO hg) o).mp ho
  have htl : t * l * t⁻¹ ∈ l1 T L V := (Subgroup.mem_normalizer_iff.mp (hTN ht) l).mp hl
  have htlO : t * l * t⁻¹ ∉ O := fun h =>
    hlO ((Subgroup.mem_normalizer_iff.mp (hTO ht) l).mpr h)
  rcases mem_cosets S h1222 h1332 h1334 hl hlO htl with hc | hc | hc
  · exact absurd hc htlO
  ·
    exfalso
    apply htR
    have hlt : l * t * l⁻¹ * t⁻¹ ∈ O := by
      have e : l * t * l⁻¹ * t⁻¹ = l * (l⁻¹ * (t * l * t⁻¹))⁻¹ * l⁻¹ := by group
      rw [e]
      exact hconjO _ hl _ (inv_mem hc)
    have hRn : l1 T L V ⊔ T ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 _
    have hlT : l ∈ Subgroup.normalizer (T : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun s hs => ?_
      by_cases hsR : s ∈ R
      · exact hRT ((Subgroup.mem_normalizer_iff.mp (hRn (Subgroup.mem_sup_left hl)) s).mp hsR)
      · have hts : t⁻¹ * s ∈ R := by
          have hidx : (R.subgroupOf T).index = 2 := h2
          have := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨t, ht⟩ : ↥T)⁻¹)
            (b := ⟨s, hs⟩)).mpr ⟨fun h => absurd (by
              simpa using Subgroup.mem_subgroupOf.mp (inv_mem h)) htR,
              fun h => absurd (Subgroup.mem_subgroupOf.mp h) hsR⟩
          simpa using Subgroup.mem_subgroupOf.mp this
        have e : l * s * l⁻¹ = (l * t * l⁻¹ * t⁻¹) * t * (l * (t⁻¹ * s) * l⁻¹) := by group
        rw [e]
        refine T.mul_mem (T.mul_mem (hRT (hOR hlt)) ht) (hRT ?_)
        exact (Subgroup.mem_normalizer_iff.mp (hRn (Subgroup.mem_sup_left hl)) _).mp hts
    have hL : l1 T L V ≤ Subgroup.normalizer (T : Set G) := by
      have hsub : O ⊔ Subgroup.zpowers l ≤ l1 T L V :=
        sup_le (pCoreOf_le 2 _) (Subgroup.zpowers_le.mpr hl)
      rcases TJ1.eq_or_eq_of_relIndex_prime Nat.prime_three h3 le_sup_left hsub with he | he
      · exact absurd (he ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers l)) hlO
      rw [← he]
      exact sup_le ((hOR.trans hRT).trans Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr hlT)
    exact le_pCoreOf_of_le_normalizer 2 le_sup_right (sup_le hL Subgroup.le_normalizer)
      S.hyp.fsu.sylow.1 ht
  · have e : t * l * t⁻¹ * l = l⁻¹ * (l * (t * l * t⁻¹)) * l := by group
    rw [e]
    simpa using hconjO _ (inv_mem hl) _ hc

theorem H_le_N_l1_of_comm (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h91 : HypF91 T V L (fsuV1 T V) V H) {Y : Subgroup G}
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (hHYL : H = Y ⊔ (l1 T L V ⊔ T))
    (hc : ∀ l : ↥H, (l : G) ∈ l1 T L V → (l : G) ^ 3 = 1 → ∀ y : ↥H, (y : G) ∈ Y →
      FixR.rho h91 l * FixR.rho h91 y = FixR.rho h91 y * FixR.rho h91 l) :
    H ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  have hL1H := Setting147.l1H' S
  have hTH := Setting147.TH' S
  have hYH' : Y ≤ H := hHYL ▸ le_sup_left
  set C : Subgroup ↥H := (Subgroup.centralizer
    (((Y.subgroupOf H).map (FixR.rho h91) : Subgroup _) : Set _)).comap (FixR.rho h91) with hC
  have hmemC : ∀ x : ↥H, x ∈ C ↔ ∀ y : ↥H, (y : G) ∈ Y →
      FixR.rho h91 y * FixR.rho h91 x = FixR.rho h91 x * FixR.rho h91 y := by
    intro x
    rw [hC, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      exact h _ (Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩)
    · rintro h _ ⟨y, hy, rfl⟩
      exact h y (Subgroup.mem_subgroupOf.mp hy)
  have hL1C : l1 T L V ≤ C.map H.subtype := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hxL : x ∈ l1 T L V := Subgroup.subset_closure hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hL1H hxL⟩, (hmemC _).mpr fun y hy => ?_, rfl⟩
    exact (hc ⟨x, hL1H hxL⟩ hxL (l1_cube_eq_one S h1222 h1332 h1334 hxL hx.2) y hy).symm
  have hcomm : ∀ l ∈ l1 T L V, ∀ y : ↥H, (y : G) ∈ Y → ∀ hl : l ∈ H,
      FixR.rho h91 y * FixR.rho h91 ⟨l, hl⟩ = FixR.rho h91 ⟨l, hl⟩ * FixR.rho h91 y := by
    intro l hl y hy hlH
    obtain ⟨x, hx, hxl⟩ := Subgroup.mem_map.mp (hL1C hl)
    have : x = ⟨l, hlH⟩ := Subtype.ext hxl
    rw [← this]
    exact (hmemC x).mp hx y hy
  have hKN : l1 T L V ⊔ T ≤ Subgroup.normalizer (l1 T L V : Set G) :=
    sup_le Subgroup.le_normalizer (Setting147.T_le_N_l1 S h1332)
  have hKY : l1 T L V ⊔ T ≤ Subgroup.normalizer (Y : Set G) :=
    (sup_le hL1H hTH).trans hHY
  have hN : (modO2Image H (l1 T L V)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨l, hl, rfl⟩ := mem_modO2Image'.mp hn
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) g
    obtain ⟨y, hy, k, hk, hyk⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hKY).mp (hHYL ▸ h.2 : (h : G) ∈ Y ⊔ _)
    have hl' : (k * l * k⁻¹ : G) ∈ l1 T L V := (Subgroup.mem_normalizer_iff.mp (hKN hk) l).mp hl
    have hl'H : (k * l * k⁻¹ : G) ∈ H := hL1H hl'
    refine mem_modO2Image'.mpr ⟨⟨k * l * k⁻¹, hl'H⟩, hl', ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul]
    apply mk_eq_of_rho_eq h91
    have hyH : y ∈ H := hYH' hy
    have e : h * l * h⁻¹ = (⟨y, hyH⟩ : ↥H) * ⟨k * l * k⁻¹, hl'H⟩ * (⟨y, hyH⟩ : ↥H)⁻¹ :=
      Subtype.ext (by simp [hyk, mul_assoc])
    rw [e, map_mul, map_mul, map_inv, hcomm _ hl' ⟨y, hyH⟩ hy hl'H, mul_inv_cancel_right]
  exact Setting147.H_le_N_l1 S h1332 hN

theorem rho_mem_zpowers (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h91 : HypF91 T V L (fsuV1 T V) V H)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) {l x : ↥H} (hl : (l : G) ∈ l1 T L V)
    (hlO : (l : G) ∉ pCoreOf 2 (l1 T L V)) (hx : (x : G) ∈ l1 T L V) :
    FixR.rho h91 x ∈ Subgroup.zpowers (FixR.rho h91 l) := by
  have hOQ : pCoreOf 2 (l1 T L V) ≤ pCoreOf 2 H := by
    rw [← Setting147.inf_O2H S hHL]; exact inf_le_left
  have hker : ∀ z : ↥H, (z : G) ∈ pCoreOf 2 (l1 T L V) → FixR.rho h91 z = 1 := fun z hz =>
    (FixR.rho_eq_one_iff h91 z).mpr (hOQ hz)
  rcases mem_cosets S h1222 h1332 h1334 hl hlO hx with h | h | h
  · rw [hker x h]; exact Subgroup.one_mem _
  · have h1 := hker (l⁻¹ * x) (by simpa using h)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← h1]; exact Subgroup.mem_zpowers _
  · have h1 := hker (l * x) (by simpa using h)
    rw [map_mul] at h1
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_mem (Subgroup.mem_zpowers _)

theorem rho_fix_eq_one (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h91 : HypF91 T V L (fsuV1 T V) V H)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) {l : ↥H} (hl : (l : G) ∈ l1 T L V)
    (hlO : (l : G) ∉ pCoreOf 2 (l1 T L V)) (w : ↥(tildeOf (fsuV1 T V) (conjClosure V H)))
    (hw : FixR.rho h91 l w = w) : w = 1 := by
  obtain ⟨w', hw'⟩ := w
  obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hw'
  have h1 := congrArg Subtype.val hw
  simp only [FixR.rho_coe, FixR.sig_apply] at h1
  have h2 := (FixR.conj_secMk_eq_iff _ _).mp h1
  have h3 := Setting147.mem_V1_of_fix S h1222 h1332 h1334 hHL hl hlO hu h2
  exact Subtype.ext ((secMk_eq_one_iff).mpr h3)

end CFSG.Quasithin.H13.L32A.M76
