module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsComm
public import CFSG.RankThree.GF2n.Stroth80.Sec34TI

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Subgroups

variable {G : Type} [Group G]

private def centW (R W Z : Subgroup G) (hZ : ∀ y ∈ R, ∀ z ∈ Z, y * z * y⁻¹ ∈ Z) : Subgroup G where
  carrier := {y | y ∈ R ∧ ∀ w ∈ W, ⁅y, w⁆ ∈ Z}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨R.mul_mem ha1 hb1, fun w hw => ?_⟩
    have e : ⁅a * b, w⁆ = a * ⁅b, w⁆ * a⁻¹ * ⁅a, w⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Z.mul_mem (hZ a ha1 _ (hb2 w hw)) (ha2 w hw)
  one_mem' := by
    refine ⟨R.one_mem, fun w _ => ?_⟩
    rw [commutatorElement_one_left]
    exact Z.one_mem
  inv_mem' := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := ha
    refine ⟨R.inv_mem ha1, fun w hw => ?_⟩
    have e : ⁅a⁻¹, w⁆ = a⁻¹ * ⁅a, w⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have h3 := hZ a⁻¹ (R.inv_mem ha1) _ (Z.inv_mem (ha2 w hw))
    rwa [inv_inv] at h3

private theorem mem_centW {R W Z : Subgroup G} {hZ : ∀ y ∈ R, ∀ z ∈ Z, y * z * y⁻¹ ∈ Z} {y : G} :
    y ∈ centW R W Z hZ ↔ y ∈ R ∧ ∀ w ∈ W, ⁅y, w⁆ ∈ Z := Iff.rfl

private def commInto (R : Subgroup G) (S : Set G) (Z0 : Subgroup G)
    (hZ0 : ∀ y ∈ R, ∀ z ∈ Z0, y * z * y⁻¹ ∈ Z0) : Subgroup G where
  carrier := {x | x ∈ R ∧ ∀ k ∈ S, ⁅k, x⁆ ∈ Z0}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨R.mul_mem ha1 hb1, fun k hk => ?_⟩
    have e : ⁅k, a * b⁆ = ⁅k, a⁆ * (a * ⁅k, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Z0.mul_mem (ha2 k hk) (hZ0 a ha1 _ (hb2 k hk))
  one_mem' := by
    refine ⟨R.one_mem, fun k _ => ?_⟩
    rw [commutatorElement_one_right]
    exact Z0.one_mem
  inv_mem' := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := ha
    refine ⟨R.inv_mem ha1, fun k hk => ?_⟩
    have e : ⁅k, a⁻¹⁆ = a⁻¹ * ⁅k, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have h3 := hZ0 a⁻¹ (R.inv_mem ha1) _ (Z0.inv_mem (ha2 k hk))
    rwa [inv_inv] at h3

private theorem mem_commInto {R : Subgroup G} {S : Set G} {Z0 : Subgroup G}
    {hZ0 : ∀ y ∈ R, ∀ z ∈ Z0, y * z * y⁻¹ ∈ Z0} {x : G} :
    x ∈ commInto R S Z0 hZ0 ↔ x ∈ R ∧ ∀ k ∈ S, ⁅k, x⁆ ∈ Z0 := Iff.rfl

end Subgroups

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7CRW_of_centre (h310chi : Stroth310ChiStatement) (hA : Sec7AExistsStatement)
    (hMpr : Sec7CentreMprStatement) (hSch : Sec7SchurStatement) : Sec7CRWStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 κ hκR hκW
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQc : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  have hVW := sec7_V_le_W h310chi hc hs
  have hZ0n : ∀ y ∈ Rt M (LB M Q B) t, ∀ z ∈ Z0, y * z * y⁻¹ ∈ Z0 := fun y hy z hz =>
    (Subgroup.mem_normalizer_iff.mp (hZ0.mem_normalizer
      (fun ρ hρ q hq => hQc ρ (hRM hρ) q hq) hy) z).mp hz
  have hQn : ∀ y ∈ Rt M (LB M Q B) t, ∀ z ∈ Q, y * z * y⁻¹ ∈ Q := fun y hy z hz =>
    hQc y (hRM hy) z hz
  have hRW : ∀ r ∈ Rt M (LB M Q B) t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      r * w * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun r hr w hw =>
    conj_mem_Wt (hc.hyp.Q_normal.2 (hRM hr)) (hc.Rt_normalizes_Vt ht hr) hw
  let K : Subgroup G := centW (Rt M (LB M Q B) t) (Wt Q (Vt M (LB M Q B) B Z t)) Z
    (fun y hy z hz => hZn y (hRM hy) z hz)
  have hκK : κ ∈ K := ⟨hκR, hκW⟩
  have hKconj : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ K, r * y * r⁻¹ ∈ K := by
    intro r hr y hy
    obtain ⟨hyR, hyW⟩ := mem_centW.mp hy
    refine mem_centW.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hr hyR) (Subgroup.inv_mem _ hr),
      fun w hw => ?_⟩
    have hw' : r⁻¹ * w * r ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      have := hRW r⁻¹ (Subgroup.inv_mem _ hr) w hw
      simpa using this
    have e : ⁅r * y * r⁻¹, w⁆ = r * ⁅y, r⁻¹ * w * r⁆ * r⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hZn r (hRM hr) _ (hyW _ hw')
  have hKN : ∀ y ∈ K, y ∈ hc.CN t := fun y hy =>
    Ctx.mem_CN.mpr ⟨(mem_centW.mp hy).1, fun v hv => (mem_centW.mp hy).2 v (hVW hv)⟩
  have hBV : B ≤ Vt M (LB M Q B) B Z t := by
    have := sec39_conjB_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) (t := t) (m := 1)
      M.one_mem (by rw [conjSubgroup_one]; exact ht)
    rwa [conjSubgroup_one] at this
  have hNL : ∀ k ∈ hc.CN t, ∀ l ∈ LB M Q B, k * l * k⁻¹ ∈ LB M Q B := by
    intro k hk l hl
    have hkM : k ∈ M := hRM (Ctx.mem_CN.mp hk).1
    have hle : conjSubgroup k B ≤ B ⊔ Z := by
      intro x hx
      rw [mem_conjSubgroup] at hx
      have hz : ⁅k, k⁻¹ * x * k⁆ ∈ Z := (Ctx.mem_CN.mp hk).2 _ (hBV hx)
      have e : x = ⁅k, k⁻¹ * x * k⁆ * (k⁻¹ * x * k) := by
        simp only [commutatorElement_def]
        group
      have h1 : ⁅k, k⁻¹ * x * k⁆ * (k⁻¹ * x * k) ∈ Z ⊔ B := Subgroup.mul_mem_sup hz hx
      rw [sup_comm] at h1
      rwa [← e] at h1
    have hconj := hc.conj_LB_eq_of_le_sup_Z hkM hle
    have hmem : k * l * k⁻¹ ∈ conjSubgroup k (LB M Q B) := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hl
    rwa [hconj] at hmem
  have hKL : ∀ k ∈ K, ∀ l ∈ LB M Q B, ⁅k, l⁆ ∈ Z0 := by
    intro k hk l hl
    have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hl
    have h1 : l * k⁻¹ * l⁻¹ ∈ K := hKconj l hlR k⁻¹ (K.inv_mem hk)
    have h2 : ⁅k, l⁆ = k * (l * k⁻¹ * l⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hmemK : ⁅k, l⁆ ∈ K := by
      rw [h2]
      exact K.mul_mem hk h1
    have hmemL : ⁅k, l⁆ ∈ LB M Q B := by
      have h3 := hNL k (hKN k hk) l hl
      rw [commutatorElement_def]
      exact (LB M Q B).mul_mem h3 ((LB M Q B).inv_mem hl)
    exact hMpr G M Q Z B hc n t hs Z0 hZ0 _ hmemL (mem_centW.mp hmemK).2
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hrR := hr.mem
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) := hc.LB_conj (hRM hrR)
  have hKA : ∀ k ∈ K, ∀ l ∈ LB M Q (conjSubgroup r B), ⁅k, l⁆ ∈ Z0 := by
    intro k hk l hl
    rw [hLA, mem_conjSubgroup] at hl
    have hk' : r⁻¹ * k * r ∈ K := by
      have := hKconj r⁻¹ (Subgroup.inv_mem _ hrR) k hk
      simpa using this
    have h1 := hKL _ hk' _ hl
    have e : ⁅k, l⁆ = r * ⁅r⁻¹ * k * r, r⁻¹ * l * r⁆ * r⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hZ0n r hrR _ h1
  have hKR : ∀ k ∈ K, ∀ x ∈ Rt M (LB M Q B) t, ⁅k, x⁆ ∈ Z0 := by
    have hLB_T : LB M Q B ≤ commInto (Rt M (LB M Q B) t) (K : Set G) Z0 hZ0n := fun l hl =>
      mem_commInto.mpr ⟨le_Rt (M := M) (LB M Q B) ht hl, fun k hk => hKL k hk l hl⟩
    have hLA_T : LB M Q (conjSubgroup r B) ≤ commInto (Rt M (LB M Q B) t) (K : Set G) Z0 hZ0n :=
      fun l hl => mem_commInto.mpr ⟨by rw [hr.gen]; exact Subgroup.mem_sup_right hl,
        fun k hk => hKA k hk l hl⟩
    have hR_T : Rt M (LB M Q B) t ≤ commInto (Rt M (LB M Q B) t) (K : Set G) Z0 hZ0n :=
      hr.gen.le.trans (sup_le hLB_T hLA_T)
    exact fun k hk x hx => (mem_commInto.mp (hR_T hx)).2 k hk
  have h3sub : ∀ r₁ ∈ Rt M (LB M Q B) t, ∀ r₂ ∈ Rt M (LB M Q B) t, ⁅κ, ⁅r₁, r₂⁆⁆ ∈ Q := by
    intro r₁ hr₁ r₂ hr₂
    have hr₂' : r₂⁻¹ ∈ Rt M (LB M Q B) t := Subgroup.inv_mem _ hr₂
    have h2 : ⁅⁅r₂⁻¹, κ⁻¹⁆⁻¹, r₁⁆ ∈ Q := by
      have h20 : ⁅κ⁻¹, r₂⁻¹⁆ ∈ Z0 := hKR _ (K.inv_mem hκK) _ hr₂'
      have h21 : ⁅r₂⁻¹, κ⁻¹⁆⁻¹ ∈ Z0 := by
        rw [commutatorElement_inv]
        exact h20
      exact hZ0.comm_mem h21 hr₁
    have h3 : ⁅⁅κ, r₁⁻¹⁆⁻¹, r₂⁻¹⁆ ∈ Q := by
      have h30 : ⁅κ, r₁⁻¹⁆ ∈ Z0 := hKR _ hκK _ (Subgroup.inv_mem _ hr₁)
      exact hZ0.comm_mem (Z0.inv_mem h30) hr₂'
    have key := three_subgroup_mod Q r₁ r₂⁻¹ κ (fun n hn => hQn r₁ hr₁ n hn)
      (fun n hn => by simpa using hQn r₂ hr₂ n hn) (fun n hn => hQn κ hκR n hn) h2 h3
    simp only [inv_inv] at key
    have hcR : ⁅r₁, r₂⁆ ∈ Rt M (LB M Q B) t := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hr₁ hr₂) (inv_mem hr₁)) (inv_mem hr₂)
    have e : ⁅κ, ⁅r₁, r₂⁆⁆ = ⁅r₁, r₂⁆ * ⁅⁅r₁, r₂⁆⁻¹, κ⁆ * ⁅r₁, r₂⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hQn _ hcR _ key
  have hRR : ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆ ≤
      commInto (Rt M (LB M Q B) t) ({κ} : Set G) Q hQn := by
    refine Subgroup.commutator_le.mpr fun r₁ hr₁ r₂ hr₂ => mem_commInto.mpr ⟨?_, fun k hk => ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hr₁ hr₂) (inv_mem hr₁)) (inv_mem hr₂)
    · rw [Set.mem_singleton_iff] at hk
      rw [hk]
      exact h3sub r₁ hr₁ r₂ hr₂
  exact hSch G M Q Z B hc n t hs Z0 hZ0 κ (hc.Rt_le_H0 t hκR)
    (fun a ha => (mem_commInto.mp (hRR ha)).2 κ (Set.mem_singleton κ)) hκW

end CFSG.RankThree.GF2n.Stroth80
