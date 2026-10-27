module

public import CFSG.OddTranspositions.PartThree.Twelve.FiveDefs
import CFSG.OddTranspositions.PartThree.Twelve.FiveChartBasic
import CFSG.OddTranspositions.PartThree.Twelve.SixFiveLocal
import CFSG.OddTranspositions.PartFour.Fourteen.FiveConnect

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] {D : Set G}

namespace FiveChart

variable {hC : HypothesisC D} {n : ℕ}

private theorem mem_commSet_of_commute {w a : G} (hwd : ¬ Commute w hC.d)
    (ha : a ∈ commSet D hC.d) (haw : Commute a w) : a ∈ commSet D w :=
  ⟨ha.1, haw, by rintro rfl; exact hwd ha.2.1⟩

private theorem b_perp_of_norm_one_perp (c : FiveChart hC n) {w u x : G}
    {z z' : Fin n → ZMod 5} (hu : u ∈ commSet D hC.d ∩ commSet D w)
    (hx : x ∈ commSet D hC.d)
    (hPu : ∀ y ∈ commSet D hC.d ∩ commSet D u, (Commute y w ↔ c.b (c.vec y) z = 0))
    (hPx : ∀ y ∈ commSet D hC.d ∩ commSet D x, (Commute y w ↔ c.b (c.vec y) z' = 0)) :
    ∀ y, c.b y y = 1 → c.b y (c.vec u) = 0 → c.b y (c.vec x) = 0 → c.b y z = 0 →
      c.b y z' = 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro y hy hyu hyx hyz
  obtain ⟨a, ha, hva⟩ := c.exists_vec y hy
  have hay_u : c.b (c.vec a) (c.vec u) = 0 := (c.b_vec_eq_zero_iff hva).2 hyu
  have hay_x : c.b (c.vec a) (c.vec x) = 0 := (c.b_vec_eq_zero_iff hva).2 hyx
  have hay_z : c.b (c.vec a) z = 0 := (c.b_vec_eq_zero_iff hva).2 hyz
  have ha_ne_u : a ≠ u := by
    intro h
    rw [h] at hay_u
    rw [c.norm_vec u hu.1] at hay_u
    exact one_ne_zero hay_u
  have ha_ne_x : a ≠ x := by
    intro h
    rw [h] at hay_x
    rw [c.norm_vec x hx] at hay_x
    exact one_ne_zero hay_x
  have ha_u : a ∈ commSet D u :=
    ⟨ha.1, (c.commute_iff a ha u hu.1 ha_ne_u).2 hay_u, ha_ne_u⟩
  have ha_x : a ∈ commSet D x :=
    ⟨ha.1, (c.commute_iff a ha x hx ha_ne_x).2 hay_x, ha_ne_x⟩
  have haw : Commute a w := (hPu a ⟨ha, ha_u⟩).2 hay_z
  exact (c.b_vec_eq_zero_iff hva).1 ((hPx a ⟨ha, ha_x⟩).1 haw)

theorem local_three_of_perp (c : FiveChart hC n) (hn : 5 ≤ n) {w u x : G} (hw : w ∈ D)
    (hwd : ¬ Commute w hC.d) (h3 : orderOf (hC.d * w) = 3) {z : Fin n → ZMod 5}
    (hz : c.b z z = 2) (hu : u ∈ commSet D hC.d ∩ commSet D w) (hzu : c.b z (c.vec u) = 0)
    (hPu : ∀ y ∈ commSet D hC.d ∩ commSet D u, (Commute y w ↔ c.b (c.vec y) z = 0))
    (hx : x ∈ commSet D hC.d) (hxu : c.b (c.vec x) (c.vec u) = 0) (hxz : c.b (c.vec x) z = 0) :
    x ∈ commSet D w ∧ ∀ y ∈ commSet D hC.d ∩ commSet D x, (Commute y w ↔ c.b (c.vec y) z = 0) := by
  have h3ne : orderOf (hC.d * w) ≠ 5 := by rw [h3]; decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hu_norm : c.b (c.vec u) (c.vec u) = 1 := c.norm_vec u hu.1
  have hx_norm : c.b (c.vec x) (c.vec x) = 1 := c.norm_vec x hx
  have hxu' : c.b (c.vec u) (c.vec x) = 0 := by rw [c.hsym]; exact hxu
  have hx_ne_u : x ≠ u := by
    intro h
    have h1 : c.b (c.vec u) (c.vec u) = 0 := h ▸ hxu'
    rw [hu_norm] at h1
    exact one_ne_zero h1
  have hx_comm_u : Commute x u := (c.commute_iff x hx u hu.1 hx_ne_u).2 hxu
  have hx_comm_w : Commute x w :=
    (hPu x ⟨hx, hx.1, hx_comm_u, hx_ne_u⟩).2 hxz
  have hxw : x ∈ commSet D w := mem_commSet_of_commute hwd hx hx_comm_w
  obtain ⟨z', hz'0, hz'x, hz'norm, hPx⟩ := exists_local_hyperplane c hn hw hwd ⟨hx, hxw⟩
  have hz' : c.b z' z' = 2 := by
    rw [if_neg h3ne] at hz'norm
    exact hz'norm
  have hu_comm_x : Commute u x := hx_comm_u.symm
  have huz' : c.b (c.vec u) z' = 0 :=
    (hPx u ⟨hu.1, hu.1.1, hu_comm_x, Ne.symm hx_ne_u⟩).1 hu.2.2.1
  have hz'u : c.b z' (c.vec u) = 0 := by rw [c.hsym]; exact huz'
  have hperp := b_perp_of_norm_one_perp c hu hx hPu hPx
  have hzx : c.b z (c.vec x) = 0 := by rw [c.hsym]; exact hxz
  obtain ⟨l, hl⟩ :=
    CFSG.OddTranspositions.PartFour.FiveConnect.eq_smul_of_forall_perp_aniso c.hsym c.hnd hn
      hu_norm hx_norm hxu' hz hzu hzx hz'u hz'x hperp
  have hl0 : l ≠ 0 := by
    intro h
    exact hz'0 (by rw [hl, h, zero_smul])
  refine ⟨hxw, fun y hy => ?_⟩
  have h1 := hPx y hy
  rw [hl, LinearMap.BilinForm.smul_right] at h1
  exact ⟨fun h => eq_zero_of_ne_zero_of_mul_left_eq_zero hl0 (h1.1 h),
    fun h => h1.2 (by rw [h, mul_zero])⟩

private theorem cutout_of_walk_three (c : FiveChart hC n) (hn : 5 ≤ n) {w v₀ y : G}
    (hw : w ∈ D) (hwd : ¬ Commute w hC.d) (h3 : orderOf (hC.d * w) = 3) {z : Fin n → ZMod 5}
    (hz : c.b z z = 2) (hv₀ : v₀ ∈ commSet D hC.d ∩ commSet D w) (hzv₀ : c.b z (c.vec v₀) = 0)
    (hP : ∀ x ∈ commSet D hC.d ∩ commSet D v₀, (Commute x w ↔ c.b (c.vec x) z = 0))
    (hy : y ∈ commSet D hC.d) (hyz : c.b (c.vec y) z = 0) :
    y ∈ commSet D w ∧ ∀ x ∈ commSet D hC.d ∩ commSet D y, (Commute x w ↔ c.b (c.vec x) z = 0) := by
  have hzv₀' : c.b (c.vec v₀) z = 0 := by rw [c.hsym]; exact hzv₀
  obtain ⟨u₁, u₂, hu₁, hu₁z, hu₂, hu₂z, hv₀u₁, hu₁u₂, hu₂y⟩ :=
    CFSG.OddTranspositions.PartFour.FiveConnect.exists_walk_three c.hsym c.hnd hn hz
      (c.norm_vec v₀ hv₀.1) hzv₀' (c.norm_vec y hy) hyz
  obtain ⟨a₁, ha₁, hva₁⟩ := c.exists_vec u₁ hu₁
  obtain ⟨a₂, ha₂, hva₂⟩ := c.exists_vec u₂ hu₂
  have hv₀u₁' : c.b u₁ (c.vec v₀) = 0 := by rw [c.hsym]; exact hv₀u₁
  have ha₁v₀ : c.b (c.vec a₁) (c.vec v₀) = 0 := (c.b_vec_eq_zero_iff hva₁).2 hv₀u₁'
  have ha₁z : c.b (c.vec a₁) z = 0 := (c.b_vec_eq_zero_iff hva₁).2 hu₁z
  have ha₁w := local_three_of_perp c hn hw hwd h3 hz hv₀ hzv₀ hP ha₁ ha₁v₀ ha₁z
  have hz_a₁ : c.b z (c.vec a₁) = 0 := by rw [c.hsym]; exact ha₁z
  have hvec_a₁_u₂ : c.b (c.vec a₁) u₂ = 0 := (c.b_vec_eq_zero_iff hva₁).2 hu₁u₂
  have hu₂a₁ : c.b u₂ (c.vec a₁) = 0 := by rw [c.hsym]; exact hvec_a₁_u₂
  have ha₂a₁ : c.b (c.vec a₂) (c.vec a₁) = 0 := (c.b_vec_eq_zero_iff hva₂).2 hu₂a₁
  have ha₂z : c.b (c.vec a₂) z = 0 := (c.b_vec_eq_zero_iff hva₂).2 hu₂z
  have ha₂w := local_three_of_perp c hn hw hwd h3 hz ⟨ha₁, ha₁w.1⟩ hz_a₁ ha₁w.2 ha₂ ha₂a₁ ha₂z
  have hz_a₂ : c.b z (c.vec a₂) = 0 := by rw [c.hsym]; exact ha₂z
  have hvec_a₂_y : c.b (c.vec a₂) (c.vec y) = 0 := (c.b_vec_eq_zero_iff hva₂).2 hu₂y
  have hy_a₂ : c.b (c.vec y) (c.vec a₂) = 0 := by rw [c.hsym]; exact hvec_a₂_y
  exact local_three_of_perp c hn hw hwd h3 hz ⟨ha₂, ha₂w.1⟩ hz_a₂ ha₂w.2 hy hy_a₂ hyz

theorem isFiveHyperplane_three (c : FiveChart hC n) (hn : 5 ≤ n) {w : G} (hw : w ∈ D)
    (hwd : ¬ Commute w hC.d) (h3 : orderOf (hC.d * w) = 3)
    (hΓ : (commSet D hC.d ∩ commSet D w).Nonempty) : ∃ z, IsFiveHyperplane c w z := by
  obtain ⟨v₀, hv₀⟩ := hΓ
  obtain ⟨z, hz0, hzv₀, hznorm, hP⟩ := exists_local_hyperplane c hn hw hwd hv₀
  have hz : c.b z z = 2 := by
    rw [if_neg (by rw [h3]; decide)] at hznorm
    exact hznorm
  have hzif : (if orderOf (hC.d * w) = 5 then c.b z z = 0 else c.b z z = 2) := by
    rw [if_neg (by rw [h3]; decide)]
    exact hz
  refine ⟨z, hz0, hzif, ?_⟩
  intro y hy
  constructor
  · intro hyw
    obtain ⟨u, hu, huz, huy⟩ :=
      CFSG.OddTranspositions.PartFour.FiveConnect.exists_norm_one_perp_aniso c.hsym c.hnd hn hz
        (c.norm_vec y hy)
    obtain ⟨a, ha, hva⟩ := c.exists_vec u hu
    have haz : c.b (c.vec a) z = 0 := (c.b_vec_eq_zero_iff hva).2 huz
    have hQ := cutout_of_walk_three c hn hw hwd h3 hz hv₀ hzv₀ hP ha haz
    have haw : Commute a w := hQ.1.2.1
    by_cases hya : y = a
    · rw [hya]; exact haz
    · have hcomm : Commute y a :=
        (c.commute_iff y hy a ha hya).2 (by
          rw [c.hsym]
          exact (c.b_vec_eq_zero_iff hva).2 huy)
      exact (hQ.2 y ⟨hy, hy.1, hcomm, hya⟩).1 hyw
  · intro hyz
    exact (cutout_of_walk_three c hn hw hwd h3 hz hv₀ hzv₀ hP hy hyz).1.2.1

end FiveChart

end CFSG.OddTranspositions.PartThree
