module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXJ1
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXJ2
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXE9
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXOT
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4Defs
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXQT
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec15.Item1512
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Toolkit.M12Local
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open CFSG.Open
open scoped CFSG.ASVolI.ChIJK

theorem isElemAbelian_map_aux {X Y : Type} [Group X] [Group Y] {E : Subgroup X} {p : ℕ}
    (h : IsElemAbelian p E) (f : X →* Y) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hax, ← hby, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (h.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, h.2 a ha, map_one]

theorem alt2_impossible {Γ : Type} [Group Γ] [Finite Γ] {KX J J' : Subgroup Γ} {r z : Γ}
    (hKX : CFSG.IsQuasisimple ↥KX) (hKXz : Nat.card ↥(Subgroup.center ↥KX) = 6)
    (E0 : Subgroup (↥KX ⧸ Subgroup.center ↥KX)) (hE0 : IsElemAbelian 3 E0)
    (hE0c : Nat.card E0 = 9)
    (hrK : ∀ k ∈ KX, r * k = k * r)
    (hzKX : z ∈ KX) (hzc : ∀ k ∈ KX, z * k = k * z)
    (hJcomm : ∀ j ∈ J, ∀ j' ∈ J', j * j' = j' * j)
    (hKXJ : KX ≤ J ⊔ J')
    (hJ'conj : ∀ j ∈ J, r * j * r⁻¹ ∈ J') (hJ'conj' : ∀ j' ∈ J', r⁻¹ * j' * r ∈ J)
    (hJZ : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card (↥KX ⧸ Subgroup.center ↥KX))
    (hiso : (↥J ⧸ CFSG.ASVolI.ChIJK.oddTwoCore ↥J) ≃*
      (↥KX ⧸ CFSG.ASVolI.ChIJK.oddTwoCore ↥KX))
    (hoT : CFSG.ASVolI.ChIJK.oddTwoCore ↥KX = Subgroup.center ↥KX)
    (hpz : CFSG.Open.pRank 3 (Subgroup.centralizer ({z} : Set Γ)) ≤ 2) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzr : z * r = r * z := (hrK z hzKX).symm
  have hzrinv : z * r⁻¹ = r⁻¹ * z := by
    calc z * r⁻¹ = r⁻¹ * (r * z) * r⁻¹ := by group
      _ = r⁻¹ * (z * r) * r⁻¹ := by rw [hzr]
      _ = r⁻¹ * z := by group
  have hzcen : (⟨z, hzKX⟩ : ↥KX) ∈ Subgroup.center ↥KX :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hzc g.1 g.2).symm
  have hzJ : ∀ j ∈ J, z * j = j * z := fun j hj =>
    center_centralizes_of_card hKX hKXz hJcomm hKXJ hrK hJ'conj' hJZ ⟨z, hzKX⟩ hzcen j hj
  have hzJ' : ∀ j' ∈ J', z * j' = j' * z := by
    intro j' hj'
    have hX : r⁻¹ * j' * r ∈ J := hJ'conj' j' hj'
    have e : j' = r * (r⁻¹ * j' * r) * r⁻¹ := by group
    calc z * j' = z * (r * (r⁻¹ * j' * r) * r⁻¹) := by rw [← e]
      _ = (z * r) * (r⁻¹ * j' * r) * r⁻¹ := by group
      _ = (r * z) * (r⁻¹ * j' * r) * r⁻¹ := by rw [hzr]
      _ = r * (z * (r⁻¹ * j' * r)) * r⁻¹ := by group
      _ = r * ((r⁻¹ * j' * r) * z) * r⁻¹ := by rw [hzJ _ hX]
      _ = (r * (r⁻¹ * j' * r)) * (z * r⁻¹) := by group
      _ = (r * (r⁻¹ * j' * r)) * (r⁻¹ * z) := by rw [hzrinv]
      _ = (r * (r⁻¹ * j' * r) * r⁻¹) * z := by group
      _ = j' * z := by rw [← e]
  have hcentK : ∀ x : Γ, (∀ j ∈ J, x * j = j * x) → (∀ j' ∈ J', x * j' = j' * x) →
      ∀ k ∈ KX, x * k = k * x := by
    intro x hxJ hxJ' k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_decomp hJcomm (hKXJ hk)
    calc x * (a * b) = (x * a) * b := by group
      _ = (a * x) * b := by rw [hxJ a ha]
      _ = a * (x * b) := by group
      _ = a * (b * x) := by rw [hxJ' b hb]
      _ = (a * b) * x := by group
  obtain ⟨AK0, hAK0, hAKc⟩ := exists_e9_of_quotient (Subgroup.center ↥KX) E0 hE0 hE0c
  have hAKel : IsElemAbelian 3 (AK0.map KX.subtype) := isElemAbelian_map_aux hAK0 KX.subtype
  have hAKc' : Nat.card (AK0.map KX.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective KX.subtype_injective, hAKc]
  have hAKle : AK0.map KX.subtype ≤ KX := Subgroup.map_subtype_le AK0
  have hAKz : AK0.map KX.subtype ≤ Subgroup.centralizer ({z} : Set Γ) := by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hzc _ (hAKle ⟨a, ha, rfl⟩)).symm
  have hZ3 : ∀ p : Γ, p ∈ J → (∀ j ∈ J, p * j = j * p) → p ^ 3 = 1 → p ≠ 1 → p ∈ KX := by
    intro p hpJm hpJ hp3 hp1
    by_contra hpK
    have hpJ' : ∀ j' ∈ J', p * j' = j' * p := fun j' hj' => hJcomm p hpJm j' hj'
    have hpC : p ∈ Subgroup.centralizer ({z} : Set Γ) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hzJ p hpJm).symm
    have hcomm : ∀ a ∈ AK0.map KX.subtype, a * p = p * a := fun a ha =>
      (hcentK p hpJ hpJ' a (hAKle ha)).symm
    exact false_of_E9_elt hpz hAKz hAKel hAKc' hpC hp3 hp1 (fun hpA => hpK (hAKle hpA)) hcomm
  obtain ⟨eJ⟩ : Nonempty ((↥J ⧸ CFSG.ASVolI.ChIJK.oddTwoCore ↥J) ≃* (↥KX ⧸ Subgroup.center ↥KX)) :=
    ⟨hiso.trans (QuotientGroup.quotientMulEquivOfEq hoT)⟩
  have hE0J : IsElemAbelian 3 (E0.map eJ.symm.toMonoidHom) := isElemAbelian_map_aux hE0 _
  have hE0Jc : Nat.card (E0.map eJ.symm.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective eJ.symm.injective, hE0c]
  obtain ⟨AJ0, hAJ0, hAJc⟩ :=
    exists_e9_of_quotient (CFSG.ASVolI.ChIJK.oddTwoCore ↥J) _ hE0J hE0Jc
  obtain ⟨A₁, hA₁el, hA₁c, hA₁J⟩ : ∃ A₁ : Subgroup Γ,
      IsElemAbelian 3 A₁ ∧ Nat.card A₁ = 9 ∧ A₁ ≤ J :=
    ⟨AJ0.map J.subtype, isElemAbelian_map_aux hAJ0 J.subtype,
      by rw [Subgroup.card_map_of_injective J.subtype_injective, hAJc],
      Subgroup.map_subtype_le AJ0⟩
  obtain ⟨A₂, hA₂el, hA₂c, hA₂J'⟩ : ∃ A₂ : Subgroup Γ,
      IsElemAbelian 3 A₂ ∧ Nat.card A₂ = 9 ∧ A₂ ≤ J' := by
    refine ⟨A₁.map (MulAut.conj r).toMonoidHom, isElemAbelian_map_aux hA₁el _, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj r).injective, hA₁c]
    · rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hJ'conj a (hA₁J ha)
  have hD : A₁ ⊓ A₂ ≤ (Subgroup.center ↥KX).map KX.subtype := by
    intro d hd
    obtain ⟨hdA₁, hdA₂⟩ := Subgroup.mem_inf.mp hd
    by_cases hd1 : d = 1
    · rw [hd1]
      exact Subgroup.one_mem _
    · have hdJ : d ∈ J := hA₁J hdA₁
      have hdJ' : d ∈ J' := hA₂J' hdA₂
      have hdcen : ∀ j ∈ J, d * j = j * d := fun j hj => (hJcomm j hj d hdJ').symm
      have hdJ'all : ∀ j' ∈ J', d * j' = j' * d := fun j' hj' => hJcomm d hdJ j' hj'
      have hdKX : d ∈ KX := hZ3 d hdJ hdcen (hA₁el.2 d hdA₁) hd1
      have hmemZ : (⟨d, hdKX⟩ : ↥KX) ∈ Subgroup.center ↥KX := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact (hcentK d hdcen hdJ'all g.1 g.2).symm
      exact Subgroup.mem_map.mpr ⟨⟨d, hdKX⟩, hmemZ, rfl⟩
  have hZKc : Nat.card ((Subgroup.center ↥KX).map KX.subtype) = 6 := by
    rw [Subgroup.card_map_of_injective KX.subtype_injective, hKXz]
  have hint : Nat.card ↥(A₁ ⊓ A₂) ≤ 3 := by
    have h9 : Nat.card ↥(A₁ ⊓ A₂) ∣ 9 := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : A₁ ⊓ A₂ ≤ A₁)
      rwa [hA₁c] at h
    have h6 : Nat.card ↥(A₁ ⊓ A₂) ∣ 6 := by
      have h := Subgroup.card_dvd_of_le hD
      rwa [hZKc] at h
    have hg : Nat.card ↥(A₁ ⊓ A₂) ∣ Nat.gcd 9 6 := Nat.dvd_gcd h9 h6
    have h3 : Nat.gcd 9 6 = 3 := by norm_num
    rw [h3] at hg
    exact Nat.le_of_dvd (by norm_num) hg
  have hA₁C : A₁ ≤ Subgroup.centralizer ({z} : Set Γ) := by
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hzJ a (hA₁J ha)).symm
  have hA₂C : A₂ ≤ Subgroup.centralizer ({z} : Set Γ) := by
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hzJ' a (hA₂J' ha)).symm
  have hcomm12 : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := fun a ha b hb =>
    hJcomm a (hA₁J ha) b (hA₂J' hb)
  exact false_of_two_E9 hpz hA₁C hA₂C hA₁el hA₂el hA₁c hA₂c hcomm12 hint

end CFSG.Quasithin.H13.Ch4.J4KX
