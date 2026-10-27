module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec10Two
public import CFSG.RankThree.GF2n.Stroth80.Sec123Order
public import CFSG.RankThree.GF2n.Stroth80.Sec310Perp
public import CFSG.RankThree.GF2n.Stroth80.Sec711Setup

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem n12Lemma4_of_notQB (h34 : Stroth34Statement) {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs5 : Sec5Hyp hc n t)
    (hr : Sec7A hc t r) (hnot : ¬ Vt M (LB M Q B) B Z t ≤ QB B) :
    Z ≤ QB (conjSubgroup r B) ∧
    (∀ x ∈ n12X hc t, ∀ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, a⁆ ∈ B ⊔ Z) ∧
    (∀ x ∈ n12X hc t, ∀ a ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅x, a⁆ ∈ Q ⊓ QB (conjSubgroup r B)) ∧
    (∀ y ∈ n12Y hc t r, ∀ a ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅y, a⁆ ∈ Q ⊓ QB (conjSubgroup r B)) ∧
    (B ⊔ Z) ⊓ (Q ⊓ QB (conjSubgroup r B)) = Z := by
  classical
  have ht : t ∈ LB M Q B := hs5.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  set V := Vt M (LB M Q B) B Z t with hV
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hBV : B ≤ V := by
    have := sec39_conjB_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) (t := t) M.one_mem
      (by rw [conjSubgroup_one]; exact ht)
    rwa [conjSubgroup_one] at this
  have hCV : conjSubgroup r B ≤ V := by
    intro x hx
    have hx' : r⁻¹ * x * r ∈ B := mem_conjSubgroup.mp hx
    have hnorm := hc.Rt_normalizes_Vt ht hr.mem
    have h1 := (Subgroup.mem_normalizer_iff.mp hnorm (r⁻¹ * x * r)).mp (hBV hx')
    have e : r * (r⁻¹ * x * r) * r⁻¹ = x := by group
    rwa [e] at h1
  have hZC : Z ≤ QB (conjSubgroup r B) := hcC.Z_le_QB.1
  have hCZV : conjSubgroup r B ⊔ Z ≤ V := sup_le hCV hZV
  refine ⟨hZC, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx a ha
    obtain ⟨g, hg⟩ := hc.conj
    have hQBe := (Ctx.QB_eq hc hg).2
    have hxQB : x ∈ conjSubgroup g Q := hQBe ▸ hx.1.1
    have haQB : a ∈ conjSubgroup g Q := hQBe ▸ ha.1
    have : ⁅x, a⁆ ∈ B := hg ▸ hc.hyp.toHyp79.comm_mem_conj g hxQB haQB
    exact Subgroup.mem_sup_left this
  ·
    intro x hx a ha
    have hxM : x ∈ M := hx.1.2
    have hxCN : x ∈ hc.CN t := hx.2
    have hle : conjSubgroup x (conjSubgroup r B) ≤ Z ⊔ conjSubgroup r B := by
      intro y hy
      have hc' : x⁻¹ * y * x ∈ conjSubgroup r B := mem_conjSubgroup.mp hy
      have e : y = ⁅x, x⁻¹ * y * x⁆ * (x⁻¹ * y * x) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem_sup ((Ctx.mem_CN.1 hxCN).2 _ (hCV hc')) hc'
    obtain ⟨p, hpQ, hp⟩ := hcC.exists_conj_of_le_ZB (hcC.conj_of_mem hxM) hle
    have hpM : p ∈ M := hc.hyp.Q_normal.1 hpQ
    have hν : p⁻¹ * x ∈ Subgroup.normalizer ((conjSubgroup r B : Subgroup G) : Set G) := by
      rw [← conjSubgroup_eq_self_iff, conjSubgroup_mul, ← hp, ← conjSubgroup_mul,
        inv_mul_cancel, conjSubgroup_one]
    have haQ : a ∈ Q := ha.2.1
    have hνM : p⁻¹ * x ∈ M := M.mul_mem (M.inv_mem hpM) hxM
    have hu1 : (p⁻¹ * x) * a * (p⁻¹ * x)⁻¹ ∈ QB (conjSubgroup r B) :=
      hcC.conj_QB_of_mem_normalizer hν ha.1
    have hu2 : (p⁻¹ * x) * a * (p⁻¹ * x)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hνM) a).mp haQ
    set u := (p⁻¹ * x) * a * (p⁻¹ * x)⁻¹ with hu
    have hxa : x * a * x⁻¹ = ⁅p, u⁆ * u := by
      simp only [commutatorElement_def, hu]; group
    have hpu : ⁅p, u⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hpQ hu2
    have hmem : x * a * x⁻¹ ∈ Q ⊓ QB (conjSubgroup r B) := by
      rw [hxa]
      exact ⟨Q.mul_mem (hc.hyp.toHyp79.comm_mem_V hpQ hu2 |> fun h => hc.Z_le_Q h) hu2,
        (QB (conjSubgroup r B)).mul_mem (hZC hpu) hu1⟩
    have e2 : ⁅x, a⁆ = (x * a * x⁻¹) * a⁻¹ := by simp only [commutatorElement_def]
    rw [e2]
    exact (Q ⊓ QB (conjSubgroup r B)).mul_mem hmem
      ((Q ⊓ QB (conjSubgroup r B)).inv_mem ⟨haQ, ha.1⟩)
  ·
    intro y hy a ha
    have hyM : y ∈ M := hy.1.2
    have haQ : a ∈ Q := ha.1
    have haC : a ∈ Subgroup.normalizer ((conjSubgroup r B : Subgroup G) : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun c hc' => ?_
      have := Subgroup.mem_centralizer_iff.mp ha.2 c (hCV hc')
      have e : a * c * a⁻¹ = c := by rw [← this]; group
      rw [e]; exact hc'
    have h1 : a * y⁻¹ * a⁻¹ ∈ QB (conjSubgroup r B) :=
      hcC.conj_QB_of_mem_normalizer haC ((QB (conjSubgroup r B)).inv_mem hy.1.1)
    have e : ⁅y, a⁆ = y * (a * y⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    have e2 : ⁅y, a⁆ = (y * a * y⁻¹) * a⁻¹ := by simp only [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · rw [e2]
      exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hyM) a).mp haQ)
        (Q.inv_mem haQ)
    · rw [e]
      exact (QB (conjSubgroup r B)).mul_mem hy.1.1 h1
  ·
    have hB8 : B ⊓ QB (conjSubgroup r B) = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      rw [Subgroup.mem_bot]
      by_contra hb1
      obtain ⟨g, hg⟩ := hc.conj
      have hCQ : conjSubgroup r B ≤ QB B :=
        hc.hyp.le_QB_of_mem_QB (X := conjSubgroup r B) (Y := B)
          ⟨r * g, by rw [hg, conjSubgroup_mul]⟩ ⟨g, hg⟩ hb.1 hb1 hb.2
      obtain ⟨ĉ, hĉQ, hĉ, b', hb'B, hb'ne⟩ := hr.plane
      have hvV : ⁅ĉ, t⁆ ∈ V := hCZV hĉ
      have hvQB : ⁅ĉ, t⁆ ∈ QB B := (sup_le hCQ hc.Z_le_QB.1) hĉ
      have hperp := (stroth310Perp_of_34 h34 G M Q Z B hc n t hs5 hnot ⁅ĉ, t⁆ hvV).mp hvQB
        b' hb'B ĉ hĉQ (by rw [mul_inv_cancel]; exact Z.one_mem)
      exact hb'ne hperp
    apply le_antisymm
    · intro x hx
      obtain ⟨hxBZ, hxP⟩ := hx
      obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
        (H := B) (K := Z) (fun b hb => hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hb))) hxBZ
      have hzP : z ∈ Q ⊓ QB (conjSubgroup r B) := ⟨hc.Z_le_Q hz, hZC hz⟩
      have hbP : b ∈ Q ⊓ QB (conjSubgroup r B) := by
        have := (Q ⊓ QB (conjSubgroup r B)).mul_mem hxP ((Q ⊓ QB (conjSubgroup r B)).inv_mem hzP)
        simpa using this
      have hb1 : b ∈ B ⊓ QB (conjSubgroup r B) := ⟨hb, hbP.2⟩
      rw [hB8, Subgroup.mem_bot] at hb1
      rw [hb1, one_mul]
      exact hz
    · exact le_inf le_sup_right (le_inf (hc.Z_le_Q) hZC)

end CFSG.RankThree.GF2n.Stroth80
