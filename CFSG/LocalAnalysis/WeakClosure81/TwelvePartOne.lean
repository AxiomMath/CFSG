module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveGen
public import CFSG.LocalAnalysis.WeakClosure81.TwelveRankOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender

section PartOne

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] {n m : ℕ}

private theorem b12_TwelvePartOne_fixMod_conj {K : Subgroup (LGL 2 V)} {d x : LGL 2 V}
    (hd : d ∈ K) (h : fixMod (cE K) (d * x * d⁻¹) ⊓ commSub K ≤ cE K) :
    fixMod (cE K) x ⊓ commSub K ≤ cE K := by
  intro e he
  have hefix : x e - e ∈ cE K := he.1
  have hecomm : e ∈ commSub K := he.2
  have hdecomm : d e ∈ commSub K := map_mem_commSub K hd hecomm
  have hdefix : (d * x * d⁻¹) (d e) - d e ∈ cE K := by
    have h1 : (d * x * d⁻¹) (d e) = d (x e) := by
      change d (x (d⁻¹ (d e))) = d (x e)
      rw [inv_apply_apply']
    rw [h1, ← map_sub]
    exact map_mem_cE K hd hefix
  have hdeE : d e ∈ cE K := h ⟨hdefix, hdecomm⟩
  have hback : d⁻¹ (d e) ∈ cE K := map_mem_cE K (K.inv_mem hd) hdeE
  rwa [inv_apply_apply'] at hback

private theorem b12_TwelvePartOne_not_mem_borel
    {ρ : G →* LGL 2 V} {B A : Subgroup G} {Z : Submodule (ZMod 2) V}
    (h : Setting12One ρ B Z A n m) {a a' g w c : G} (ha : a ∈ A) (ha2 : a * a = 1)
    (ha'2 : a' * a' = 1) (hga : g * a * g⁻¹ = a') (hcw : c * w * c⁻¹ = a * a')
    (hwodd : Odd (orderOf w)) (hw1 : w ≠ 1) : g ∉ B := by
  intro hgB
  obtain ⟨S, rfl⟩ := exists_sylow_of_isBorelIn h.borel
  have hAS : A ≤ (S : Subgroup G) :=
    le_sylow_of_le_normalizer (IsElemAbelian.isPGroup h.A_elem) h.A_le_B
  have haS : a ∈ (S : Subgroup G) := hAS ha
  have ha'S : a' ∈ (S : Subgroup G) := by
    rw [← hga]
    exact (Subgroup.mem_normalizer_iff.mp hgB a).mp haS
  obtain ⟨i, t, hc⟩ := rankOne_exists_benderCore h.type S
  have hcomm : a' * a = a * a' :=
    (mem_rootCenter_iff.mp (hc.mem_rootCenter_of_mul_self haS ha2)).2 a' ha'S
  have hsq : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [hcomm]
      _ = (a * a) * (a' * a') := by group
      _ = 1 := by rw [ha2, ha'2, one_mul]
  have hdvd : orderOf (a * a') ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (n := 2) (by rw [pow_two]; exact hsq)
  have hsem : SemiconjBy c w (a * a') := by
    show c * w = (a * a') * c
    calc c * w = (c * w * c⁻¹) * c := by group
      _ = (a * a') * c := by rw [hcw]
  have hdvdw : orderOf w ∣ 2 := by rw [SemiconjBy.orderOf_eq c hsem]; exact hdvd
  have h1 : orderOf w = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvdw with h1 | h2
    · exact h1
    · rw [h2] at hwodd
      exact absurd hwodd (by norm_num)
  exact hw1 (orderOf_eq_one_iff.mp h1)

theorem Setting12One.injective {ρ : G →* LGL 2 V} {B A : Subgroup G}
    {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m) : Function.Injective ρ := by
  haveI : IsSimpleGroup G := CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz h.type
  rcases Subgroup.Normal.eq_bot_or_eq_top ρ.ker with hbot | htop
  · exact (MonoidHom.ker_eq_bot_iff ρ).mp hbot
  · exfalso
    obtain ⟨S, hSB⟩ := exists_sylow_of_isBorelIn h.borel
    have hBtop : B = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro g
      rw [h.stab g]
      intro z hz
      have hgker : g ∈ ρ.ker := by rw [htop]; trivial
      have hg1 : ρ g = 1 := (MonoidHom.mem_ker).mp hgker
      rw [hg1]
      simpa using hz
    have hne := rankOne_borel_ne_top h.type S
    rw [← hSB] at hne
    exact hne hBtop

theorem twelveOne_fix_of_involutions {ρ : G →* LGL 2 V}
    {B A : Subgroup G} {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m)
    (hmin : ∀ L : Subgroup G, A ≤ L → ¬ L ≤ B → L = ⊤) {u v : G} (hu : u * u = 1)
    (hv : v * v = 1) (huv : Odd (orderOf (u * v))) (huv1 : u * v ≠ 1) :
    fixMod (cE ρ.range) (ρ (u * v)) ⊓ commSub ρ.range ≤ cE ρ.range := by
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card A = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [h.A_card] at h1
    have hgt : 1 < 2 ^ m :=
      Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp (Nat.lt_trans Nat.zero_lt_one h.one_lt_m))
        (by norm_num)
    exact absurd h1 (ne_of_gt hgt)
  obtain ⟨a0, ha0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  set a : G := (a0 : G) with ha_def
  have ha : a ∈ A := by rw [ha_def]; exact a0.2
  have ha1 : a ≠ 1 := by
    rw [ha_def]
    exact fun h1 => ha0ne (Subtype.ext h1)
  have ha2 : a * a = 1 := by
    have hh := h.A_elem.2 a ha
    rwa [pow_two] at hh
  have hu1 : u ≠ 1 := by
    intro hu'
    rw [hu', one_mul] at huv huv1
    have hdvd : orderOf v ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (n := 2) (by rw [pow_two]; exact hv)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact huv1 (orderOf_eq_one_iff.mp h1)
    · rw [h2] at huv
      exact absurd huv (by norm_num)
  have hv1 : v ≠ 1 := by
    intro hv'
    rw [hv', mul_one] at huv huv1
    have hdvd : orderOf u ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (n := 2) (by rw [pow_two]; exact hu)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact huv1 (orderOf_eq_one_iff.mp h1)
    · rw [h2] at huv
      exact absurd huv (by norm_num)
  obtain ⟨c₁, hc₁⟩ := isConj_iff.mp (rankOne_isConj_of_involutions h.type hu hu1 ha2 ha1)
  let a1 : G := c₁ * v * c₁⁻¹
  have ha1_def : a1 = c₁ * v * c₁⁻¹ := rfl
  have ha1_2 : a1 * a1 = 1 := by
    rw [ha1_def]
    calc (c₁ * v * c₁⁻¹) * (c₁ * v * c₁⁻¹) = c₁ * (v * v) * c₁⁻¹ := by group
      _ = 1 := by rw [hv]; simp
  have ha1_ne : a1 ≠ 1 := by
    intro h1
    apply hv1
    rw [ha1_def] at h1
    calc v = c₁⁻¹ * (c₁ * v * c₁⁻¹) * c₁ := by group
      _ = c₁⁻¹ * 1 * c₁ := by rw [h1]
      _ = 1 := by group
  obtain ⟨g, hg⟩ :=
    isConj_iff.mp (rankOne_isConj_of_involutions h.type ha2 ha1 ha1_2 ha1_ne)
  have hcw : c₁ * (u * v) * c₁⁻¹ = a * a1 := by
    rw [ha1_def, ← hc₁]
    group
  have hgB : g ∉ B := b12_TwelvePartOne_not_mem_borel h ha ha2 ha1_2 hg hcw huv huv1
  have hgen : A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤ :=
    hmin _ le_sup_left fun hLB =>
      rankOne_conj_not_le_borel h.type h.borel h.A_le_B h.A_elem hAne hgB
        (le_sup_right.trans hLB)
  have H := twelveOne_partOne h hgen
  have hmap : ρ a ∈ A.map ρ := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hP : ∃ a₀ ∈ A, a₀ ≠ 1 ∧ ρ a₀ = ρ a := ⟨a, ha, ha1, rfl⟩
  have h4 := H.2.2.2 (ρ a) hmap hP
  have hρga : (MulAut.conj (ρ g)) (ρ a) = ρ a1 := by
    rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul, hg]
  have hdeq : ρ a * (MulAut.conj (ρ g)) (ρ a) = ρ c₁ * ρ (u * v) * (ρ c₁)⁻¹ := by
    rw [hρga, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← hcw]
  have h4' : fixMod (cE ρ.range) (ρ c₁ * ρ (u * v) * (ρ c₁)⁻¹) ⊓ commSub ρ.range ≤
      cE ρ.range := by
    rw [← hdeq]
    exact h4
  exact b12_TwelvePartOne_fixMod_conj (K := ρ.range) (d := ρ c₁) (x := ρ (u * v))
    (MonoidHom.mem_range.mpr ⟨c₁, rfl⟩) h4'

theorem twelveOne_fix_of_inverted {ρ : G →* LGL 2 V}
    {B A : Subgroup G} {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m)
    (hmin : ∀ L : Subgroup G, A ≤ L → ¬ L ≤ B → L = ⊤) {t x : G} (ht : t * t = 1)
    (htx : t * x * t = x⁻¹) (hx : Odd (orderOf x)) (hx1 : x ≠ 1) :
    fixMod (cE ρ.range) (ρ x) ⊓ commSub ρ.range ≤ cE ρ.range := by
  have hv : (t * x) * (t * x) = 1 := by
    calc (t * x) * (t * x) = (t * x * t) * x := by group
      _ = x⁻¹ * x := by rw [htx]
      _ = 1 := inv_mul_cancel x
  have htv : t * (t * x) = x := by rw [← mul_assoc, ht, one_mul]
  have hres := twelveOne_fix_of_involutions h hmin ht hv
    (by rw [htv]; exact hx) (by rw [htv]; exact hx1)
  rwa [htv] at hres

end PartOne

end CFSG.LocalAnalysis.WeakClosure81
