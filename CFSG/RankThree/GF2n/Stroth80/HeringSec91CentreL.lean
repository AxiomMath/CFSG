module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreA
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreM

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix


namespace HS9

theorem arith91 {j N₁ e m : ℕ} (he : 1 ≤ e) (hj : 2 ≤ j) (h : j ^ 2 * 2 ^ N₁ = 2 ^ (2 * e * m))
    (hdvd : 2 * e ∣ N₁) : 2 ^ e ≤ j := by
  obtain ⟨s, rfl⟩ := hdvd
  have hle : 2 * e * s ≤ 2 * e * m := by
    have : 2 ^ (2 * e * s) ∣ 2 ^ (2 * e * m) := ⟨j ^ 2, by rw [← h]; ring⟩
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hsm : s ≤ m := Nat.le_of_mul_le_mul_left hle (by omega)
  have h2 : j ^ 2 = 2 ^ (2 * e * (m - s)) := by
    have h3 : 2 ^ (2 * e * m) = 2 ^ (2 * e * (m - s)) * 2 ^ (2 * e * s) := by
      rw [← pow_add]; congr 1; rw [← Nat.mul_add, Nat.sub_add_cancel hsm]
    rw [h3] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  have h4 : j = 2 ^ (e * (m - s)) := by
    have : (2 ^ (e * (m - s))) ^ 2 = j ^ 2 := by rw [h2, ← pow_mul]; congr 1; ring
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) this).symm
  have hms : 1 ≤ m - s := by
    by_contra hcon
    have : m - s = 0 := by omega
    rw [this, mul_zero, pow_zero] at h4
    omega
  rw [h4]
  exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem centre95CardLower_holds91 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
        Nat.card Q * Nat.card Z ≤ Nat.card Z0 := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0
  classical
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  obtain ⟨r, hr⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc n t hs
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hcr : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) := hc.LB_conj hrM
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hL'R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := by
    rw [hr.gen]; exact le_sup_right
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have hQL' : Q ≤ LB M Q (conjSubgroup r B) := sec39_Q_le_LB
  obtain ⟨hprod, hcomm, hNN⟩ := sec9_N51 h34 h311a hNC hs hr
  have heq := isCentrePre_eq_inf91 hs hr hprod hcomm hZ0
  have hZN : Z0 ≤ hc.CN t := isCentrePre_le_CN91 hs hZ0
  have hZL : Z0 ≤ LB M Q B := by rw [heq]; exact inf_le_left
  have hZL' : Z0 ≤ LB M Q (conjSubgroup r B) := by rw [heq]; exact inf_le_right
  have hQnorm : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    conj_mem_Q91 hc (hc.Rt_le_M t hρ) hy
  have hZnorm : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Z0, ρ * x * ρ⁻¹ ∈ Z0 := fun ρ hρ x hx =>
    (Subgroup.mem_normalizer_iff.mp (hZ0.mem_normalizer hQnorm hρ) x).mp hx
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := sec9_CN_le_Rt hc t
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := exists_pts91 h34 hs
  haveI := hn
  let r' : ↥(Rt M (LB M Q B) t) := ⟨r, hrR⟩
  have hne : polar (quadPlus 2 K) u ((φ r' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) ≠ 0 :=
    (hypPlane_iff_polar91 h34 hs P r').mp hr.plane
  set u' := (φ r' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u with hu'def
  have hrX : (φ r' : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedOmega (StatedQuadPlus 2 K) :=
    P.range ▸ MonoidHom.mem_range.mpr ⟨r', rfl⟩
  have hu : quadPlus 2 K u = 0 := P.sing
  have hu' : quadPlus 2 K u' = 0 := by rw [hu'def, E.quad_mulVec hrX]; exact P.sing
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  have hu'u : polar (quadPlus 2 K) u' u ≠ 0 := by rw [polar_comm]; exact hne
  have hL₁ : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u := P.root
  have hL₂ : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      E.LomGL u' := by
    rw [hLA]
    exact sec7_conj_LomGL E φ P.range r' P.root
  obtain ⟨e, kk, hZ2, -⟩ := hc.hyp.cp
  have hKe : Nat.card K = 2 ^ e := P.card.trans hZ2
  obtain ⟨a, ha, ha', hc2⟩ := exists_nonsingular_perp91 hQ hu hu' hne
  obtain ⟨A₁, hA₁eq, hA₁mem, hA₁app⟩ := exists_X_eichler91 E ha'
  obtain ⟨A₂, hA₂eq, hA₂mem, hA₂app⟩ := exists_X_eichler91 E ha
  obtain ⟨x₀, hx₀L, hx₀φ⟩ : ∃ x₀ ∈ (LB M Q (conjSubgroup r B)).subgroupOf
      (Rt M (LB M Q B) t), φ x₀ = (A₁ : GL (Fin 2 ⊕ Fin 2) K) := by
    rw [← hL₂] at hA₁mem
    obtain ⟨x₀, hx₀, hx₀φ⟩ := hA₁mem
    exact ⟨x₀, hx₀, hx₀φ⟩
  obtain ⟨y₀, hy₀L, hy₀φ⟩ : ∃ y₀ ∈ (LB M Q B).subgroupOf (Rt M (LB M Q B) t),
      φ y₀ = (A₂ : GL (Fin 2 ⊕ Fin 2) K) := by
    rw [← hL₁] at hA₂mem
    obtain ⟨y₀, hy₀, hy₀φ⟩ := hA₂mem
    exact ⟨y₀, hy₀, hy₀φ⟩
  have hx₀ne : polar (quadPlus 2 K) u
      ((φ x₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) ≠ 0 := by
    rw [hx₀φ, hA₁app]
    exact polar_eichler_ne_zero91 hu hu' hne ha' ha hc2
  have hy₀ne : polar (quadPlus 2 K) u'
      ((φ y₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u') ≠ 0 := by
    rw [hy₀φ, hA₂app]
    exact polar_eichler_ne_zero91 hu' hu hu'u ha ha' hc2
  have pack : ∀ z₀ : ↥(Rt M (LB M Q B) t),
      polar (quadPlus 2 K) u ((φ z₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) ≠ 0 →
      ∀ w ∈ LB M Q B ⊓ LB M Q (conjSubgroup (z₀ : G) B), w ∈ Z0 := by
    intro z₀ hz₀ w hw
    have hz := sec7A_of_polar91 h34 h311a hNC hs P z₀ hz₀
    obtain ⟨-, hcomm', -⟩ := sec9_N51 h34 h311a hNC hs hz
    refine (hZ0 w).mpr ⟨hLR hw.1, fun g hg => ?_⟩
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hcomm' g hg w hw)
  have key : ∀ (z₀ : ↥(Rt M (LB M Q B) t)), polar (quadPlus 2 K) u
      ((φ z₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) ≠ 0 → ∀ c ∈ LB M Q B,
      ⁅(z₀ : G), c⁆ ∈ Z0 → c ∈ Z0 := by
    intro z₀ hz₀ c hc' hzc
    have hz₀M : (z₀ : G) ∈ M := hc.Rt_le_M t z₀.2
    have e : (z₀ : G) * c * (z₀ : G)⁻¹ = ⁅(z₀ : G), c⁆ * c := by
      simp only [commutatorElement_def]; group
    have hm1 : (z₀ : G) * c * (z₀ : G)⁻¹ ∈ LB M Q B := by
      rw [e]; exact (LB M Q B).mul_mem (hZL hzc) hc'
    have hm2 : (z₀ : G) * c * (z₀ : G)⁻¹ ∈ LB M Q (conjSubgroup (z₀ : G) B) := by
      rw [hc.LB_conj hz₀M, mem_conjSubgroup]
      have e2 : (z₀ : G)⁻¹ * ((z₀ : G) * c * (z₀ : G)⁻¹) * (z₀ : G) = c := by group
      rw [e2]; exact hc'
    have := pack z₀ hz₀ _ ⟨hm1, hm2⟩
    have := hZnorm (z₀ : G)⁻¹ ((Rt M (LB M Q B) t).inv_mem z₀.2) _ this
    have e3 : (z₀ : G)⁻¹ * ((z₀ : G) * c * (z₀ : G)⁻¹) * ((z₀ : G)⁻¹)⁻¹ = c := by group
    rwa [e3] at this
  have h9 : ∀ x ∈ hc.CN t, (∀ l ∈ LB M Q B, ⁅l, x⁆ ∈ Z0) → x ∈ LB M Q B ⊓ hc.CN t := by
    intro x hx hxl
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    have haR : a ∈ Rt M (LB M Q B) t := hNR ha.2
    have hb1 : ∀ l ∈ LB M Q B, ⁅l, b⁆ ∈ Z0 := by
      intro l hl
      have e : ⁅l, a * b⁆ = ⁅l, a⁆ * (a * ⁅l, b⁆ * a⁻¹) := by
        simp only [commutatorElement_def]; group
      have h1 : ⁅l, a⁆ ∈ Z0 :=
        hQZ0 (hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator hl ha.1))
      have h2 : a * ⁅l, b⁆ * a⁻¹ ∈ Z0 := by
        have h3 : ⁅l, a⁆⁻¹ * ⁅l, a * b⁆ ∈ Z0 := Z0.mul_mem (Z0.inv_mem h1) (hxl l hl)
        have e2 : ⁅l, a⁆⁻¹ * ⁅l, a * b⁆ = a * ⁅l, b⁆ * a⁻¹ := by rw [e]; group
        rw [e2] at h3
        exact h3
      have h4 := hZnorm a⁻¹ ((Rt M (LB M Q B) t).inv_mem haR) _ h2
      have e4 : a⁻¹ * (a * ⁅l, b⁆ * a⁻¹) * a⁻¹⁻¹ = ⁅l, b⁆ := by group
      rw [e4] at h4
      exact h4
    have hbA : b ∈ conjSubgroup r (LB M Q B) := hLA ▸ hb.1
    have hb' : r⁻¹ * b * r ∈ LB M Q B := mem_conjSubgroup.mp hbA
    let y'' : ↥(Rt M (LB M Q B) t) := r'⁻¹ * y₀ * r'
    have hy''coe : (y'' : G) = r⁻¹ * (y₀ : G) * r := by simp [y'', r']
    have hy''ne : polar (quadPlus 2 K) u
        ((φ y'' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) ≠ 0 := by
      have e : φ y'' = (φ r')⁻¹ * φ y₀ * φ r' := by simp [y'', map_mul, map_inv]
      rw [e, E.polar_conj_mulVec hrX u]
      exact hy₀ne
    have hyb : ⁅(y'' : G), r⁻¹ * b * r⁆ ∈ Z0 := by
      have e : ⁅(y'' : G), r⁻¹ * b * r⁆ = r⁻¹ * ⁅(y₀ : G), b⁆ * r := by
        rw [hy''coe]; simp only [commutatorElement_def]; group
      rw [e]
      have h5 := hZnorm r⁻¹ ((Rt M (LB M Q B) t).inv_mem hrR) _
        (hb1 (y₀ : G) (Subgroup.mem_subgroupOf.mp hy₀L))
      simpa using h5
    have hb'Z := key y'' hy''ne _ hb' hyb
    have hbZ := hZnorm r hrR _ hb'Z
    have e5 : r * (r⁻¹ * b * r) * r⁻¹ = b := by group
    rw [e5] at hbZ
    have hbZ' : b ∈ Z0 := hbZ
    exact ⟨(LB M Q B).mul_mem ha.1 (hZL hbZ'), hc.CN t |>.mul_mem ha.2 hb.2⟩
  have h10 : ∀ x ∈ hc.CN t, (∀ l ∈ LB M Q (conjSubgroup r B), ⁅l, x⁆ ∈ Z0) →
      x ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t := by
    intro x hx hxl
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    have haR : a ∈ Rt M (LB M Q B) t := hNR ha.2
    have ha1 : ∀ l ∈ LB M Q (conjSubgroup r B), ⁅l, a⁆ ∈ Z0 := by
      intro l hl
      have e : ⁅l, a * b⁆ = ⁅l, a⁆ * (a * ⁅l, b⁆ * a⁻¹) := by
        simp only [commutatorElement_def]; group
      have h1 : ⁅l, b⁆ ∈ Z0 :=
        hQZ0 (hcr.commutator_LB_le_Q (Subgroup.commutator_mem_commutator hl hb.1))
      have h2 : a * ⁅l, b⁆ * a⁻¹ ∈ Z0 := hZnorm a haR _ h1
      have h3 : ⁅l, a * b⁆ * (a * ⁅l, b⁆ * a⁻¹)⁻¹ ∈ Z0 := Z0.mul_mem (hxl l hl) (Z0.inv_mem h2)
      have e6 : ⁅l, a * b⁆ * (a * ⁅l, b⁆ * a⁻¹)⁻¹ = ⁅l, a⁆ := by rw [e]; group
      rw [e6] at h3
      exact h3
    have hx₀a := ha1 (x₀ : G) (Subgroup.mem_subgroupOf.mp hx₀L)
    have e : (x₀ : G) * a * (x₀ : G)⁻¹ = ⁅(x₀ : G), a⁆ * a := by
      simp only [commutatorElement_def]; group
    have hm1 : (x₀ : G) * a * (x₀ : G)⁻¹ ∈ LB M Q B := by
      rw [e]; exact (LB M Q B).mul_mem (hZL hx₀a) ha.1
    have hm2 : (x₀ : G) * a * (x₀ : G)⁻¹ ∈ LB M Q (conjSubgroup (x₀ : G) B) := by
      rw [hc.LB_conj (hc.Rt_le_M t x₀.2), mem_conjSubgroup]
      have e2 : (x₀ : G)⁻¹ * ((x₀ : G) * a * (x₀ : G)⁻¹) * (x₀ : G) = a := by group
      rw [e2]; exact ha.1
    have h6 := pack x₀ hx₀ne _ ⟨hm1, hm2⟩
    have h7 := hZnorm (x₀ : G)⁻¹ ((Rt M (LB M Q B) t).inv_mem x₀.2) _ h6
    have e3 : (x₀ : G)⁻¹ * ((x₀ : G) * a * (x₀ : G)⁻¹) * ((x₀ : G)⁻¹)⁻¹ = a := by group
    rw [e3] at h7
    exact ⟨(LB M Q (conjSubgroup r B)).mul_mem (hZL' h7) hb.1, (hc.CN t).mul_mem ha.2 hb.2⟩
  have hsq : ∀ x ∈ hc.CN t, x ^ 2 ∈ Z0 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    have ha2 : a ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB ha.1
    have hb2 : b ^ 2 ∈ Q := hcr.sq_mem_Q_of_mem_LB hb.1
    have hcom : ⁅b, a⁆ ∈ Z0 := by
      rw [heq]; exact hNN (Subgroup.commutator_mem_commutator hb.2 ha.2)
    have hconj := hZnorm a (hNR ha.2) _ hcom
    have e : (a * b) ^ 2 = (a * ⁅b, a⁆ * a⁻¹) * a ^ 2 * b ^ 2 := by
      simp only [commutatorElement_def, pow_two]; group
    rw [e]
    exact Z0.mul_mem (Z0.mul_mem hconj (hQZ0 ha2)) (hQZ0 hb2)
  have hNN' : ⁅hc.CN t, hc.CN t⁆ ≤ Z0 := by rw [heq]; exact hNN
  have hd : IsOppDecomp (hc.CN t) Z0 (LB M Q B) (LB M Q (conjSubgroup r B))
      (LB M Q B ⊓ hc.CN t) (LB M Q (conjSubgroup r B) ⊓ hc.CN t) := by
    refine ⟨le_inf hZL hZN, inf_le_right, le_inf hZL' hZN, inf_le_right, ?_, ?_, ?_, hsq, ?_, ?_⟩
    · refine le_antisymm (sup_le inf_le_right inf_le_right) fun x hx => ?_
      obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
      exact Subgroup.mul_mem_sup ha hb
    · refine le_antisymm ?_ (le_inf (le_inf hZL hZN) (le_inf hZL' hZN))
      rintro x ⟨⟨hx1, -⟩, ⟨hx3, -⟩⟩
      rw [heq]
      exact ⟨hx1, hx3⟩
    · intro x hx y hy
      exact hNN' (Subgroup.commutator_mem_commutator hx hy)
    · intro x hx
      refine ⟨fun hxA l hl => hQZ0 (hc.commutator_LB_le_Q
        (Subgroup.commutator_mem_commutator hl hxA.1)), h9 x hx⟩
    · intro x hx
      refine ⟨fun hxA l hl => hQZ0 (hcr.commutator_LB_le_Q
        (Subgroup.commutator_mem_commutator hl hxA.1)), h10 x hx⟩
  have hP : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ hc.CN t, ρ * x * ρ⁻¹ ∈ hc.CN t :=
    fun ρ hρ x hx => hc.CN_conj_mem ht hρ hx
  obtain ⟨N₁, hN₁, h2e⟩ := card_sec_two_pow91 E φ P.range P.ker hQ hu hu' hne hL₁ hL₂ hLR hL'R
    hP hZnorm hd hKe
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hLcard := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.2.1
  have hrel := relIndex_LB_CN h34 hs
  have hn3 : n - 1 = (n - 3) + 2 := by have := hs5.n_gt; omega
  have hXcard : Nat.card ↥(LB M Q B ⊓ hc.CN t) = Nat.card Q * Nat.card Z ^ (n - 3) := by
    have h1 := Subgroup.relIndex_mul_card (H := hc.CN t) (K := LB M Q B)
    rw [hrel, hLcard, inf_comm, hn3, pow_add] at h1
    refine Nat.eq_of_mul_eq_mul_left (pow_pos hqpos 2) ?_
    rw [h1]; ring
  have hNnorm : r ∈ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => hc.CN_conj_mem ht hrR hx
  have hYconj : LB M Q (conjSubgroup r B) ⊓ hc.CN t = conjSubgroup r (LB M Q B ⊓ hc.CN t) := by
    rw [conjSubgroup_inf, ← hc.LB_conj hrM, conjSubgroup_eq_self_iff.mpr hNnorm]
  have hYcard : Nat.card ↥(LB M Q (conjSubgroup r B) ⊓ hc.CN t) =
      Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
    rw [hYconj]; exact card_conjSubgroup r _
  have hZX : Z0 ≤ LB M Q B ⊓ hc.CN t := le_inf hZL hZN
  have hNY : (LB M Q (conjSubgroup r B) ⊓ hc.CN t) ≤
      Subgroup.normalizer ((LB M Q B ⊓ hc.CN t : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    refine Subgroup.commutator_le.mpr fun b hb a ha => ?_
    exact hZX (hNN' (Subgroup.commutator_mem_commutator hb.2 ha.2))
  have hXYsup : (LB M Q B ⊓ hc.CN t) ⊔ (LB M Q (conjSubgroup r B) ⊓ hc.CN t) = hc.CN t := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) fun x hx => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    exact Subgroup.mul_mem_sup ha hb
  have hXYinf : (LB M Q B ⊓ hc.CN t) ⊓ (LB M Q (conjSubgroup r B) ⊓ hc.CN t) = Z0 := by
    refine le_antisymm ?_ (le_inf hZX (le_inf hZL' hZN))
    rintro x ⟨⟨hx1, -⟩, ⟨hx3, -⟩⟩
    rw [heq]
    exact ⟨hx1, hx3⟩
  have hcnt := card_sup_mul_card_inf_of_le_normalizer hNY
  rw [hXYsup, hXYinf, hYcard, hXcard] at hcnt
  have hj := Subgroup.relIndex_mul_card (H := Q) (K := Z0)
  rw [inf_of_le_left hQZ0] at hj
  set j := Q.relIndex Z0 with hjdef
  have hj2 : 2 ≤ j := by
    by_contra hlt
    have hj1 : j ≤ 1 := by omega
    have hjpos : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · exfalso
        have := Nat.card_pos (α := ↥Z0)
        rw [← hj, h0, zero_mul] at this
        omega
      · exact h0
    have hj1' : j = 1 := by omega
    rw [hj1', one_mul] at hj
    have heq' : Q = Z0 := Subgroup.eq_of_le_of_card_ge hQZ0 (le_of_eq hj.symm)
    have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
    rw [← heq'] at htZ0
    exact hs5.notQ htZ0
  rw [hN₁, ← hj] at hcnt
  have hmain : j ^ 2 * 2 ^ N₁ = 2 ^ (2 * e * (n - 3)) := by
    have h1 : Nat.card Q ^ 2 * (j ^ 2 * 2 ^ N₁) = Nat.card Q ^ 2 * 2 ^ (2 * e * (n - 3)) := by
      calc Nat.card Q ^ 2 * (j ^ 2 * 2 ^ N₁)
          = j * Nat.card Q * 2 ^ N₁ * (j * Nat.card Q) := by ring
        _ = (Nat.card Q * Nat.card Z ^ (n - 3)) * (Nat.card Q * Nat.card Z ^ (n - 3)) := hcnt
        _ = Nat.card Q ^ 2 * 2 ^ (2 * e * (n - 3)) := by
          rw [hZ2, ← pow_mul]; ring_nf
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hQpos 2) h1
  have he1 : 1 ≤ e := by
    by_contra h
    have : e = 0 := by omega
    have h1 : 1 < Nat.card Z := hc.hyp.q4 |> fun h => by omega
    rw [hZ2, this] at h1
    simp at h1
  have hge := arith91 he1 hj2 hmain h2e
  calc Nat.card Q * Nat.card Z = Nat.card Q * 2 ^ e := by rw [hZ2]
    _ ≤ Nat.card Q * j := Nat.mul_le_mul_left _ hge
    _ = Nat.card ↥Z0 := by rw [mul_comm]; exact hj

end HS9

end CFSG.RankThree.GF2n.Stroth80
