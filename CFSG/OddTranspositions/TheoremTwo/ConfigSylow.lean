module

public import CFSG.OddTranspositions.PartThree.WidthThree
public import CFSG.OddTranspositions.PartThree.LocalBenderInvolutions
public import CFSG.OddTranspositions.PartThree.LocalBenderCenter
import CFSG.GroupTheory.OddCoreQuotient

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartThree
open scoped Pointwise

variable {G : Type} [Group G] {D : Set G}

theorem exists_commute_of_conj_mem_triple {a x y z : G} (hx : x * x = 1) (hz : z * z = 1)
    (hxy : Commute x y) (hxz : Commute x z) (haz : Commute a z) (ha : a * a = 1)
    (hmem : a * x * a⁻¹ = x ∨ a * x * a⁻¹ = y ∨ a * x * a⁻¹ = x * y * z) :
    Commute a x ∨ Commute a y ∨ Commute a (x * y * z) := by
  have hcz : a * z * a⁻¹ = z := by rw [haz.eq, mul_inv_cancel_right]
  have hcomm_of : ∀ c, a * c * a⁻¹ = c → Commute a c := fun c h => by
    have : a * c = c * a := by
      calc a * c = a * c * a⁻¹ * a := by group
        _ = c * a := by rw [h]
    exact this
  have hback : ∀ c, a * (a * c * a⁻¹) * a⁻¹ = c := fun c => by
    rw [show a * (a * c * a⁻¹) * a⁻¹ = (a * a) * c * (a * a)⁻¹ by group, ha]; group
  rcases hmem with h1 | h1 | h1
  · exact Or.inl (hcomm_of x h1)
  ·
    have h2 : a * y * a⁻¹ = x := by have := hback x; rwa [h1] at this
    refine Or.inr (Or.inr (hcomm_of _ ?_))
    rw [show a * (x * y * z) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) * (a * z * a⁻¹) by group,
      h1, h2, hcz, hxy.eq]
  ·
    have h2 : a * (x * y * z) * a⁻¹ = x := by have := hback x; rwa [h1] at this
    refine Or.inr (Or.inl (hcomm_of _ ?_))
    have hyb : y = x * (x * y * z) * z := by
      calc y = (x * x) * y * (z * z) := by rw [hx, hz]; group
        _ = x * (x * y * z) * z := by group
    have hval : a * y * a⁻¹ = (x * y * z) * x * z := by
      conv_lhs => rw [hyb]
      rw [show a * (x * (x * y * z) * z) * a⁻¹ =
        (a * x * a⁻¹) * (a * (x * y * z) * a⁻¹) * (a * z * a⁻¹) by group, h1, h2, hcz]
    have hfin : (x * y * z) * x * z = y := by
      rw [show (x * y * z) * x * z = x * y * (z * x) * z by group, ← hxz.eq,
        show x * y * (x * z) * z = x * (y * x) * (z * z) by group, hz, mul_one, ← hxy.eq,
        ← mul_assoc, hx, one_mul]
    exact hval.trans hfin

theorem mem_sylow_smul_iff (S : Sylow 2 G) (k x : G) :
    x ∈ (k • S : Sylow 2 G) ↔ k⁻¹ * x * k ∈ S := by
  change x ∈ ((k • S : Sylow 2 G) : Subgroup G) ↔ k⁻¹ * x * k ∈ (S : Subgroup G)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

variable [Finite G]

theorem exists_sylow_conj_data (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {z u v : G} (hz1 : z ≠ 1) (hzD : z ∉ D)
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v) (hc : Commute u v)
    (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z, ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z))) :
    ∃ (S : Sylow 2 G) (a : G), z ∈ S ∧ (∀ s ∈ S, Commute s z) ∧ a ∈ S ∧ a ≠ z ∧
      IsConj z a ∧ a * a = 1 ∧ Commute a u ∧
      ¬ ∃ d ∈ D ∩ (S : Set G), ∃ e ∈ D ∩ (S : Set G), d ≠ e ∧ Commute a d ∧ Commute a e := by
  classical
  have hR := solvableRadical_le_center_localGroup hS hu hv huv hc huvz htrans hQ
  have hZ2 := eq_one_or_eq_of_mem_center_localGroup hS hz1 hu hv huv hc huvz htrans hQ hB
  have hH' := not_mem_commutator_localGroup hS hz1 hu hv huv hc huvz htrans hQ hB
  have hmul := mul_mul_mem_of_isBenderGroup hS hu hv huv htrans hR hZ2 hB hH'
  have hconj := conj_eq_of_isBenderGroup hS hu hv huv hc huvz hzD htrans hR hZ2 hB
  obtain ⟨S₀, hu₀, hv₀, hd₀, hzS, hz2, hzuvd⟩ := exists_sylow_inter_data hS hu hv huv hc hmul
  have hLcomm : ∀ d ∈ D ∩ (S₀ : Set G), ∀ e ∈ D ∩ (S₀ : Set G), Commute d e :=
    fun d hd e he => hS.oddT.commute_of_isPGroup S₀.isPGroup' hd.1 he.1 hd.2 he.2
  have hLC : D ∩ (S₀ : Set G) ⊆ centSet D z :=
    sylow_inter_le_centSet hS.oddT S₀ hu₀ hv₀ hd₀ hzuvd
  have hLz : ∀ d ∈ D ∩ (S₀ : Set G), Commute d z := fun d hd => (hLC hd).2
  have hmulL : ∀ d ∈ D ∩ (S₀ : Set G), ∀ e ∈ D ∩ (S₀ : Set G), d ≠ e →
      d * e * z ∈ D ∩ (S₀ : Set G) := fun d hd e he hde =>
    ⟨hmul d (hLC hd) e (hLC he) hde (hLcomm d hd e he),
      S₀.mul_mem (S₀.mul_mem hd.2 he.2) hzS⟩
  have hzc : ∀ s ∈ S₀, Commute s z :=
    commute_of_mem_sylow_of_conj_eq hS S₀ hu₀ hv₀ hd₀ hzuvd hLC hconj
  obtain ⟨g, hgc', hgne⟩ := exists_conj_commute_of_solvable_radical_bot hrad hz1 hz2
  have hbb : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hz2, mul_one,
      mul_inv_cancel]
  obtain ⟨a, haS, hane, haconj, haa, haz⟩ := CFSG.GroupTheory.exists_conj_mem_sylow_of_commute
    S₀ hzc (isConj_iff.mpr ⟨g, rfl⟩) hgc' hgne hbb
  have haL : ∀ d ∈ D ∩ (S₀ : Set G), a * d * a⁻¹ ∈ D ∩ (S₀ : Set G) := fun d hd =>
    ⟨hS.normal a d hd.1, S₀.mul_mem (S₀.mul_mem haS hd.2) (S₀.inv_mem haS)⟩
  have hfix : ¬ ∃ d ∈ D ∩ (S₀ : Set G), ∃ e ∈ D ∩ (S₀ : Set G), d ≠ e ∧
      Commute a d ∧ Commute a e :=
    not_exists_two_commute_of_conj_eq hS S₀ haz haconj hane hLcomm hmulL hconj
  have hcard : (D ∩ (S₀ : Set G)).ncard ≤ 3 :=
    ncard_inter_sylow_le_three hS S₀ hz2 hzD hLz hmulL haa haz haL hfix
  have hu1 : u * u = 1 := hS.oddT.mul_self_eq_one hu.1
  have hne1 : u ≠ u * v * z := fun h => by
    have hvz : v * z = 1 := by
      have : u * (v * z) = u * 1 := by rw [mul_one, ← mul_assoc]; exact h.symm
      exact mul_left_cancel this
    have hzv : z = v := by
      rw [eq_inv_of_mul_eq_one_right hvz,
        inv_eq_of_mul_eq_one_right (hS.oddT.mul_self_eq_one hv.1)]
    exact hzD (hzv ▸ hv.1)
  have hne2 : v ≠ u * v * z := fun h => by
    have huz : u * z = 1 := by
      have : v * (u * z) = v * 1 := by
        rw [mul_one, ← mul_assoc, ← hc.eq]; exact h.symm
      exact mul_left_cancel this
    have hzu : z = u := by
      rw [eq_inv_of_mul_eq_one_right huz, inv_eq_of_mul_eq_one_right hu1]
    exact hzD (hzu ▸ hu.1)
  have htri : ({u, v, u * v * z} : Set G) = D ∩ (S₀ : Set G) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · rintro x (rfl | rfl | rfl)
      exacts [hu₀, hv₀, hd₀]
    · rw [Set.ncard_eq_three.mpr ⟨u, v, u * v * z, huv, hne1, hne2, rfl⟩]
      exact hcard
  have hmem : a * u * a⁻¹ = u ∨ a * u * a⁻¹ = v ∨ a * u * a⁻¹ = u * v * z := by
    have := haL u hu₀
    rw [← htri] at this
    simpa using this
  have hcomm3 := exists_commute_of_conj_mem_triple hu1 hz2 hc hu.2 haz haa hmem
  have huvzC : u * v * z ∈ centSet D z := ⟨huvz, (hu.2.mul_left hv.2).mul_left (Commute.refl z)⟩
  obtain ⟨c, hcC, hac⟩ : ∃ c ∈ centSet D z, Commute a c := by
    rcases hcomm3 with h | h | h
    exacts [⟨u, hu, h⟩, ⟨v, hv, h⟩, ⟨_, huvzC, h⟩]
  obtain ⟨k, hkK, hkc⟩ := htrans c hcC u hu
  have hkz : Commute k z := commute_of_mem_localGroup hkK
  have hkz' : k * z * k⁻¹ = z := by rw [hkz.eq, mul_inv_cancel_right]
  refine ⟨k • S₀, k * a * k⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_sylow_smul_iff]
    rw [show k⁻¹ * z * k = z by rw [mul_assoc, ← hkz.eq, inv_mul_cancel_left]]
    exact hzS
  · intro s hs
    rw [mem_sylow_smul_iff] at hs
    have h1 := (hzc _ hs).conj k
    rw [show k * (k⁻¹ * s * k) * k⁻¹ = s by group, hkz'] at h1
    exact h1
  · rw [mem_sylow_smul_iff, show k⁻¹ * (k * a * k⁻¹) * k = a by group]
    exact haS
  · intro h
    apply hane
    calc a = k⁻¹ * (k * a * k⁻¹) * k := by group
      _ = k⁻¹ * z * k := by rw [h]
      _ = z := by rw [mul_assoc, ← hkz.eq, inv_mul_cancel_left]
  · exact haconj.trans (isConj_iff.mpr ⟨k, rfl⟩)
  · rw [show k * a * k⁻¹ * (k * a * k⁻¹) = k * (a * a) * k⁻¹ by group, haa, mul_one,
      mul_inv_cancel]
  · rw [← hkc]
    exact hac.conj k
  · rintro ⟨d, hd, e, he, hde, had, hae⟩
    have hconjD : ∀ x ∈ D ∩ ((k • S₀ : Sylow 2 G) : Set G),
        k⁻¹ * x * k ∈ D ∩ (S₀ : Set G) :=
      fun x hx => ⟨by simpa using hS.normal k⁻¹ x hx.1, (mem_sylow_smul_iff S₀ k x).mp hx.2⟩
    have hcomm' : ∀ x, Commute (k * a * k⁻¹) x → Commute a (k⁻¹ * x * k) := fun x h => by
      have := h.conj k⁻¹
      simpa [mul_assoc] using this
    exact hfix ⟨_, hconjD d hd, _, hconjD e he, fun h => hde (by
      have := congrArg (fun y => k * y * k⁻¹) h
      simpa [mul_assoc] using this), hcomm' d had, hcomm' e hae⟩

end CFSG.OddTranspositions

end
