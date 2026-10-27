module

public import CFSG.RankThree.GF2n.Tim79a34BigDirectGroup

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

theorem bigEps_K_le_Q {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}
    (hc : MinCex M V Q P H) (hPP : ⁅P, P⁆ = V ⊓ wOf V H)
    (hCP : Subgroup.centralizer (P : Set G) = V) :
    ∀ m ∈ M, (∀ p ∈ P, ⁅m, p⁆ ∈ V ⊓ wOf V H) → m ∈ Q := by
  have hcz : ∀ v ∈ V, ∀ p ∈ P, v * p = p * v := fun v hv p hp => hc.commute_of_mem_P hp hv
  have hVP : V ≤ P := hc.V_le_P
  have hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P := fun m hm p hp =>
    (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hm) p).mp hp
  have hAnorm : ∀ g ∈ M, ∀ x ∈ V ⊓ wOf V H, g * x * g⁻¹ ∈ V ⊓ wOf V H := by
    intro g hg x hx
    have hx' : x ∈ ⁅P, P⁆ := by
      rw [hPP]
      exact hx
    have h := bigDirect_conj_mem_commutator hc.M_le_normalizer_P g hg x hx'
    rw [hPP] at h
    exact h
  have L1 : ∀ a g h : G, a * h = h * a → ⁅a * g, h⁆ = a * ⁅g, h⁆ * a⁻¹ := by
    intro a g h hah
    have hinv : a⁻¹ * h⁻¹ = h⁻¹ * a⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hah]
    have e1 : ⁅a * g, h⁆ = a * g * h * g⁻¹ * (a⁻¹ * h⁻¹) := by
      simp only [commutatorElement_def]
      group
    have e2 : a * ⁅g, h⁆ * a⁻¹ = a * g * h * g⁻¹ * (h⁻¹ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e1, e2, hinv]
  have L2 : ∀ b g h : G, g * b = b * g → ⁅g, b * h⁆ = b * ⁅g, h⁆ * b⁻¹ := by
    intro b g h hgb
    have e1 : ⁅g, b * h⁆ = g * b * h * g⁻¹ * (h⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    have e2 : b * ⁅g, h⁆ * b⁻¹ = b * g * h * g⁻¹ * (h⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e1, e2, hgb]
  have KL : ∀ a ∈ V, ∀ b ∈ V, ∀ x ∈ P, ∀ y ∈ P, ⁅a * x, b * y⁆ = ⁅x, y⁆ := by
    intro a ha b hb x hx y hy
    have hby : b * y ∈ P := P.mul_mem (hVP hb) hy
    have hz : ⁅x, y⁆ ∈ P := by
      simp only [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)
    have hbx : x * b = b * x := (hcz b hb x hx).symm
    have hzb : b * ⁅x, y⁆ = ⁅x, y⁆ * b := hcz b hb _ hz
    have hza : a * ⁅x, y⁆ = ⁅x, y⁆ * a := hcz a ha _ hz
    rw [L1 a x (b * y) (hcz a ha _ hby), L2 b x y hbx, hzb, mul_inv_cancel_right, hza,
      mul_inv_cancel_right]
  have key4 : ∀ x ∈ M, (∀ p ∈ P, ⁅x, p⁆ ∈ V ⊓ wOf V H) → x * x * (x * x) = 1 := by
    intro x hxM hxA
    have hconj : ∀ u ∈ P, ∀ w ∈ P, x * ⁅u, w⁆ * x⁻¹ = ⁅u, w⁆ := by
      intro u hu w hw
      have hu' : x * u * x⁻¹ = ⁅x, u⁆ * u := by
        simp only [commutatorElement_def]
        group
      have hw' : x * w * x⁻¹ = ⁅x, w⁆ * w := by
        simp only [commutatorElement_def]
        group
      have hid : x * ⁅u, w⁆ * x⁻¹ = ⁅x * u * x⁻¹, x * w * x⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [hid, hu', hw']
      exact KL _ (Subgroup.mem_inf.mp (hxA u hu)).1 _ (Subgroup.mem_inf.mp (hxA w hw)).1 u hu w hw
    have hcentr : ∀ z ∈ ⁅P, P⁆, x * z * x⁻¹ = z := by
      have hle : ⁅P, P⁆ ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.commutator_le]
        intro u hu w hw
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        calc x * ⁅u, w⁆ = (x * ⁅u, w⁆ * x⁻¹) * x := by group
          _ = ⁅u, w⁆ * x := by rw [hconj u hu w hw]
      intro z hz
      have h1 := Subgroup.mem_centralizer_iff.mp (hle hz) x (Set.mem_singleton x)
      rw [h1, mul_inv_cancel_right]
    have hsq : ∀ p ∈ P, x * x * p * (x * x)⁻¹ = p := by
      intro p hp
      have hmp : x * p * x⁻¹ = ⁅x, p⁆ * p := by
        simp only [commutatorElement_def]
        group
      have haA : ⁅x, p⁆ ∈ V ⊓ wOf V H := hxA p hp
      have haPP : ⁅x, p⁆ ∈ ⁅P, P⁆ := by
        rw [hPP]
        exact haA
      have hma : x * ⁅x, p⁆ * x⁻¹ = ⁅x, p⁆ := hcentr _ haPP
      have haa : ⁅x, p⁆ * ⁅x, p⁆ = 1 := hc.elemAb.mul_self_eq_one (Subgroup.mem_inf.mp haA).1
      calc x * x * p * (x * x)⁻¹ = x * (x * p * x⁻¹) * x⁻¹ := by group
        _ = x * (⁅x, p⁆ * p) * x⁻¹ := by rw [hmp]
        _ = (x * ⁅x, p⁆ * x⁻¹) * (x * p * x⁻¹) := by group
        _ = ⁅x, p⁆ * (⁅x, p⁆ * p) := by rw [hma, hmp]
        _ = (⁅x, p⁆ * ⁅x, p⁆) * p := by group
        _ = p := by rw [haa, one_mul]
    have hxxV : x * x ∈ V := by
      have hmem : x * x ∈ Subgroup.centralizer (P : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr (fun h hh => ?_)
        exact (mul_inv_eq_iff_eq_mul.mp (hsq h hh)).symm
      rw [hCP] at hmem
      exact hmem
    exact hc.elemAb.mul_self_eq_one hxxV
  intro m hmM hmA
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G,
      ∀ x, x ∈ K ↔ (x ∈ M ∧ ∀ p ∈ P, ⁅x, p⁆ ∈ V ⊓ wOf V H) := by
    refine ⟨{ carrier := {x | x ∈ M ∧ ∀ p ∈ P, ⁅x, p⁆ ∈ V ⊓ wOf V H}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun x => Iff.rfl⟩
    · intro a b ha hb
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      show a * b ∈ M ∧ ∀ p ∈ P, ⁅a * b, p⁆ ∈ V ⊓ wOf V H
      refine ⟨M.mul_mem ha1 hb1, fun p hp => ?_⟩
      have e : ⁅a * b, p⁆ = (a * ⁅b, p⁆ * a⁻¹) * ⁅a, p⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (V ⊓ wOf V H).mul_mem (hAnorm a ha1 _ (hb2 p hp)) (ha2 p hp)
    · show (1 : G) ∈ M ∧ ∀ p ∈ P, ⁅(1 : G), p⁆ ∈ V ⊓ wOf V H
      refine ⟨M.one_mem, fun p _ => ?_⟩
      rw [commutatorElement_one_left]
      exact (V ⊓ wOf V H).one_mem
    · intro a ha
      obtain ⟨ha1, ha2⟩ := ha
      show a⁻¹ ∈ M ∧ ∀ p ∈ P, ⁅a⁻¹, p⁆ ∈ V ⊓ wOf V H
      refine ⟨M.inv_mem ha1, fun p hp => ?_⟩
      have e : ⁅a⁻¹, p⁆ = a⁻¹ * (⁅a, p⁆)⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hAnorm a⁻¹ (M.inv_mem ha1) _ ((V ⊓ wOf V H).inv_mem (ha2 p hp))
  have hKnorm : ∀ g ∈ M, ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
    intro g hg x hx
    obtain ⟨hxM, hxA⟩ := (hK x).mp hx
    rw [hK]
    refine ⟨M.mul_mem (M.mul_mem hg hxM) (M.inv_mem hg), fun p hp => ?_⟩
    have hq : g⁻¹ * p * g ∈ P := by
      simpa using hMP g⁻¹ (M.inv_mem hg) p hp
    have e : ⁅g * x * g⁻¹, p⁆ = g * ⁅x, g⁻¹ * p * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hAnorm g hg _ (hxA _ hq)
  have hpow4 : ∀ x ∈ K, x ^ 2 ^ 2 = 1 := by
    intro x hx
    obtain ⟨hxM, hxA⟩ := (hK x).mp hx
    have e : x ^ 2 ^ 2 = x * x * (x * x) := by
      rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, sq, sq]
    rw [e]
    exact key4 x hxM hxA
  have hNnorm : (K.subgroupOf M).Normal := by
    refine ⟨fun n hn g => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hn ⊢
    exact hKnorm _ g.2 _ hn
  have hNpg : IsPGroup 2 ↥(K.subgroupOf M) := by
    intro g
    refine ⟨2, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hx := hpow4 ((g : ↥M) : G) (Subgroup.mem_subgroupOf.mp g.2)
    simpa using hx
  have hNle : K.subgroupOf M ≤ pCore 2 ↥M := le_sSup ⟨hNnorm, hNpg⟩
  have hmem : (⟨m, hmM⟩ : ↥M) ∈ K.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr ((hK m).mpr ⟨hmM, hmA⟩)
  rw [hc.hQ]
  exact Subgroup.mem_map.mpr ⟨⟨m, hmM⟩, hNle hmem, rfl⟩

end CFSG.RankThree.GF2n.Tim79a
