module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockCentral
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylSlOnIso
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylCentOmega

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf
open scoped commutatorElement

namespace GGHalf

private theorem mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      mul_mem' := by
        rintro x y ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
        refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
        calc (a1 * a2) * (b1 * b2) = a1 * (a2 * (b1 * b2)) := by group
          _ = a1 * ((a2 * b1) * b2) := by group
          _ = a1 * ((b1 * a2) * b2) := by rw [h a2 ha2 b1 hb1]
          _ = (a1 * b1) * (a2 * b2) := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [_root_.mul_inv_rev]
        exact h a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb) }
  have hA : A ≤ P := fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩
  have hB : B ≤ P := fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩
  have hsup : A ⊔ B ≤ P := sup_le hA hB
  exact hsup hx

private theorem commutator_mul_left_of_commute {G : Type*} [Group G] {x y z : G}
    (hxz : x * z = z * x) : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ := by
  have hxz' : x⁻¹ * z⁻¹ = z⁻¹ * x⁻¹ := by
    rw [← _root_.mul_inv_rev, ← hxz, _root_.mul_inv_rev]
  rw [commutatorElement_def, commutatorElement_def]
  calc x * y * z * (x * y)⁻¹ * z⁻¹ = x * (y * z * y⁻¹) * (x⁻¹ * z⁻¹) := by group
    _ = x * (y * z * y⁻¹) * (z⁻¹ * x⁻¹) := by rw [hxz']
    _ = x * (y * z * y⁻¹ * z⁻¹) * x⁻¹ := by group

private theorem commutator_sup_le_of_commute {G : Type*} [Group G] {A S : Subgroup G}
    (hAA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAS : ∀ a ∈ A, ∀ s ∈ S, a * s = s * a) :
    ⁅A ⊔ S, A ⊔ S⁆ ≤ S := by
  rw [Subgroup.commutator_le]
  intro h1 h1h h2 h2h
  obtain ⟨a1, ha1, s1, hs1, rfl⟩ := mem_sup_of_commute hAS h1h
  obtain ⟨a2, ha2, s2, hs2, rfl⟩ := mem_sup_of_commute hAS h2h
  have hbase : ⁅s1, s2⁆ ∈ S := by
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem hs1 hs2) (S.inv_mem hs1)) (S.inv_mem hs2)
  have hE2 : ⁅s1, a2 * s2⁆ ∈ S := by
    have hconj : ⁅s1, a2 * s2⁆ = a2 * ⁅s1, s2⁆ * a2⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc s1 * (a2 * s2) * s1⁻¹ * (a2 * s2)⁻¹
          = s1 * a2 * s2 * s1⁻¹ * (a2 * s2)⁻¹ := by group
        _ = a2 * s1 * s2 * s1⁻¹ * (a2 * s2)⁻¹ := by rw [← hAS a2 ha2 s1 hs1]
        _ = a2 * s1 * s2 * s1⁻¹ * (s2⁻¹ * a2⁻¹) := by rw [_root_.mul_inv_rev]
        _ = a2 * (s1 * s2 * s1⁻¹ * s2⁻¹) * a2⁻¹ := by group
    rw [hconj]
    have hc : a2 * ⁅s1, s2⁆ = ⁅s1, s2⁆ * a2 := hAS a2 ha2 _ hbase
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hbase
  have hcomm_a1 : a1 * (a2 * s2) = (a2 * s2) * a1 := by
    calc a1 * (a2 * s2) = (a1 * a2) * s2 := by group
      _ = (a2 * a1) * s2 := by rw [hAA a1 ha1 a2 ha2]
      _ = a2 * (a1 * s2) := by group
      _ = a2 * (s2 * a1) := by rw [hAS a1 ha1 s2 hs2]
      _ = (a2 * s2) * a1 := by group
  rw [commutator_mul_left_of_commute hcomm_a1]
  have hc : a1 * ⁅s1, a2 * s2⁆ = ⁅s1, a2 * s2⁆ * a1 := hAS a1 ha1 _ hE2
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  exact hE2

theorem eq_map_slOn_of_perfect {G : Type} [Group G] {m : ℕ} (hm : 3 ≤ m)
    {ψ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G} (hψ : Function.Injective ψ)
    {x : G} {P : Fin (m + 1 + 1)} {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (ht : t ∈ Subgroup.zpowers (omegaBlock (m + 1 + 1) P)) (ht1 : t ≠ 1)
    (hx : GGHalfActsAs ψ.range ψ x t) {J : Subgroup G} (hJψ : J ≤ ψ.range)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set G)) (hJp : commutator J = ⊤)
    (hcard : Nat.card J = Nat.card (SpecialLinearGroup (Fin (m + 1)) F2)) :
    J = (slOn (m + 1 + 1 + 1) {i | i ≠ P.castSucc ∧ i ≠ P.succ}).map ψ := by
  classical
  set ω : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := omegaBlock (m + 1 + 1) P
  set A : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) := Subgroup.zpowers ω
  set S : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :=
    slOn (m + 1 + 1 + 1) {i | i ≠ P.castSucc ∧ i ≠ P.succ}
  set A' : Subgroup G := A.map ψ
  set S' : Subgroup G := S.map ψ
  have hω3 : ω ^ 3 = 1 := omegaBlock_pow_three (m + 1 + 1) P
  have hωne : ω ≠ 1 := omegaBlock_ne_one (m + 1 + 1) P
  have hωord : orderOf ω = 3 := orderOf_eq_prime hω3 hωne
  have htnord : orderOf t = 3 := by
    have hdvd : orderOf t ∣ 3 := by
      have := orderOf_dvd_of_mem_zpowers ht
      rwa [hωord] at this
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) ht1
    · exact h3
  have hω_mem_t : ω ∈ Subgroup.zpowers t := by
    have hle : Subgroup.zpowers t ≤ Subgroup.zpowers ω := by
      rw [Subgroup.zpowers_le]
      exact ht
    have hcardt : Nat.card (Subgroup.zpowers t) = 3 := by
      rw [Nat.card_zpowers, htnord]
    have hcardω : Nat.card (Subgroup.zpowers ω) = 3 := by
      rw [Nat.card_zpowers, hωord]
    have heq : Subgroup.zpowers t = Subgroup.zpowers ω :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardt, hcardω])
    rw [heq]
    exact Subgroup.mem_zpowers ω
  have hcomm_t_to_ω : ∀ g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2,
      g * t = t * g → g * ω = ω * g := by
    intro g hgt
    have hcomm : Commute g t := (commute_iff_eq g t).mpr hgt
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hω_mem_t
    rw [← hk]
    exact (hcomm.zpow_right k).eq
  have hJ_le : J ≤ A' ⊔ S' := by
    intro j hj
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hJψ hj)
    have hjx : j * x = x * j := Subgroup.mem_centralizer_singleton_iff.mp (hJx hj)
    have hxj : x * j * x⁻¹ = j := by
      rw [← hjx, mul_assoc, mul_inv_cancel, mul_one]
    have htj : ψ t * j * (ψ t)⁻¹ = j := by
      rw [← hx j (hJψ hj), hxj]
    have hconj : ψ (t * g * t⁻¹) = ψ g := by
      have h := htj
      rw [← hg] at h
      simpa only [map_mul, map_inv] using h
    have htg : t * g * t⁻¹ = g := hψ hconj
    have hgt : g * t = t * g := by
      calc g * t = (t * g * t⁻¹) * t := by rw [htg]
        _ = t * g := by group
    have hωg : g * ω = ω * g := hcomm_t_to_ω g hgt
    obtain ⟨a, ha, s, hs, hgs⟩ := mem_centralizer_omegaBlock m P g hωg
    have hj_eq : j = ψ a * ψ s := by
      rw [← hg, hgs, map_mul]
    rw [hj_eq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem ψ ha) (Subgroup.mem_map_of_mem ψ hs)
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← _root_.zpow_add, ← _root_.zpow_add, Int.add_comm]
  have hA'comm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hAcomm a₀ ha₀ b₀ hb₀]
  have hA'S' : ∀ a ∈ A', ∀ s ∈ S', a * s = s * a := by
    intro a ha s hs
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
    rw [← map_mul, ← map_mul]
    congr 1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₀
    have hωs0 : Commute ω s₀ := by
      have hk : P.castSucc ∉ {i : Fin (m + 1 + 1 + 1) | i ≠ P.castSucc ∧ i ≠ P.succ} ∧
          P.succ ∉ {i : Fin (m + 1 + 1 + 1) | i ≠ P.castSucc ∧ i ≠ P.succ} := by
        constructor <;> simp
      exact (commute_iff_eq ω s₀).mpr (commute_omegaBlock_slOn (n := m + 1 + 1) (k := P) hk hs₀)
    exact (hωs0.zpow_left k).eq
  have hJJ : ⁅J, J⁆ = J := by
    rw [← Subgroup.map_subtype_commutator J, hJp, Subgroup.map_top, Subgroup.range_subtype]
  have hJ_le_S' : J ≤ S' := by
    calc J = ⁅J, J⁆ := hJJ.symm
      _ ≤ ⁅A' ⊔ S', A' ⊔ S'⁆ := Subgroup.commutator_mono hJ_le hJ_le
      _ ≤ S' := commutator_sup_le_of_commute hA'comm hA'S'
  have hS'card : Nat.card S' = Nat.card J := by
    rw [show S' = S.map ψ from rfl, Subgroup.card_map_of_injective hψ, hcard]
    obtain ⟨e⟩ := exists_mulEquiv_slOn_compl m P
    exact Nat.card_congr e.toEquiv
  haveI : Finite ↥S' := by
    have hsurj : Function.Surjective (fun s : ↥S => (⟨ψ s, Subgroup.mem_map_of_mem ψ s.2⟩ : ↥S')) := by
      intro y
      obtain ⟨s, hs, hys⟩ := Subgroup.mem_map.mp y.2
      refine ⟨⟨s, hs⟩, ?_⟩
      apply Subtype.ext
      exact hys
    exact Finite.of_surjective _ hsurj
  exact Subgroup.eq_of_le_of_card_ge hJ_le_S' (by rw [hS'card])

end GGHalf

end CFSG.StandardType

end
