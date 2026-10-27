module

public import CFSG.Quasithin.Vol2.Ch11SecBK2I
public import CFSG.Quasithin.Vol2.Ch11SecAKA1
public import CFSG.Quasithin.Vol2.Ch10SecABasicAut
public import CFSG.Quasithin.Vol2.Ch11SecA02Eight
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBK2H

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open scoped IsMulCommutative

theorem factA2InL_holds : FactA2InL := by
  intro G _ _ L V X n hV hn hLV hVL hnat hLX hXN
  obtain ⟨_, hnat⟩ := hnat
  show ∀ A : Subgroup (MulAut ↥V), A ∈ E3.aSet 2 (autOn X V) → A ≤ autOn L V
  intro A hA
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  have hW : commV (autOn L V) = ⊤ := by
    rw [Ch10.SecA.commV_autOn_eq hLV, hVL, Subgroup.subgroupOf_self]
  have hZ : ∀ h ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, h z = z :=
    fun h hh z hz => SecA.autOn_fixes_cV h hh z hz
  obtain ⟨hAX, -, hAab, hAfix⟩ := hA
  have hAX' : ∀ a ∈ A, a ∈ autOn X V := fun a ha => hAX ha
  have hAZ : ∀ a ∈ A, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V,
      a z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V := by
    intro a ha z hz
    obtain ⟨x, hxX, hxV, rfl⟩ := SecA.mem_autOn_iff.mp (hAX' a ha)
    exact G2Q8.conjV_mem_centralizer (hXN ⟨hxX, hxV⟩) hxV hz
  have hAH : ∀ a ∈ A, ∀ h ∈ autOn L V, a * h * a⁻¹ ∈ autOn L V := by
    intro a ha h hh
    obtain ⟨x, hxX, hxV, rfl⟩ := SecA.mem_autOn_iff.mp (hAX' a ha)
    exact G2Q8.conjV_mul_conjV_inv_mem (hXN ⟨hxX, hxV⟩) hxV hh
  have ha2 : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hAab.2 a ha
  rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    refine BK2.le_of_aSet_two hK hf (fun T hT => KGNat.commutant_statedSL (by norm_num) T hT)
      (x₀ := (![1, 0, 0] : Fin 3 → K)) (fun h => one_ne_zero (congrFun h 0)) hAab hAfix hAZ hAH
      (fun a ha hl => BK2.mem_of_lin_SL3 hf hZ hW (hAH a ha) (hAZ a ha) (ha2 a ha) hl)
      fun B hBH hB2 => BK2.exists_fixed_line hf
        (fun T hT => KGNat.commutant_statedSL (by norm_num) T hT) hsq hZ ?_ ?_ ?_ hBH hB2
    · intro P hP
      obtain ⟨U₁, -, -, hU₁, -⟩ := KGNat.factFlagSL3_holds K n hn hK _ hsq _ _ π hπ P hP
      exact ⟨U₁, by rw [hK]; exact hU₁⟩
    · intro P U hP hU
      exact KGNat.factSylowLeviSL3_holds K n hn hK _ hsq _ _ π hπ P hP U (by rw [← hK]; exact hU)
    · intro P U hP hU
      exact KGNat.factPointSL3_holds K n hn hK _ hsq _ _ π hπ P hP U (by rw [← hK]; exact hU)
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    refine BK2.le_of_aSet_two hK hf (fun T hT => KGNat.commutant_statedSp T hT)
      (x₀ := KGNat.vec4 (1 : K) 0 0 0) (fun h => one_ne_zero (congrFun h (.inl 0))) hAab hAfix
      hAZ hAH (fun a ha hl => BK2.mem_of_lin_Sp4 hf hZ hW (hAH a ha) (hAZ a ha) (ha2 a ha) hl)
      fun B hBH hB2 => BK2.exists_fixed_line hf (fun T hT => KGNat.commutant_statedSp T hT) hsq
        hZ ?_ ?_ ?_ hBH hB2
    · intro P hP
      obtain ⟨U₁, -, -, hU₁, -⟩ := KGNat.factFlagSp4_holds K n hn hK _ hsq _ _ π hπ P hP
      exact ⟨U₁, by rw [hK]; exact hU₁⟩
    · intro P U hP hU
      exact KGNat.factSylowLeviSp4_holds K n hn hK _ hsq _ _ π hπ P hP U (by rw [← hK]; exact hU)
    · intro P U hP hU
      exact KGNat.factPointSp4_holds K n hn hK _ hsq _ _ π hπ P hP U (by rw [← hK]; exact hU)
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (G2Q8.lmG K) hπ
    refine BK2.le_of_aSet_two hK hf
      (fun T hT => G2Q8.commutant_g2Derived hc0 hc1 G2Q8.g2Derived_le T hT)
      (x₀ := q6 (1 : K) 0 0 0 0 0) (fun h => one_ne_zero (congrFun h (.inl 0))) hAab hAfix hAZ
      hAH (fun a ha hl => BK2.mem_of_lin_G2 hf hc0 hc1 hK hn hW hXN (hAX' a ha) (ha2 a ha)
        (hAZ a ha) hl)
      fun B hBH hB2 => BK2.exists_fixed_line hf
        (fun T hT => G2Q8.commutant_g2Derived hc0 hc1 G2Q8.g2Derived_le T hT) hsq hZ ?_ ?_ ?_
        hBH hB2
    · intro P hP
      obtain ⟨U₁, -, -, hU₁, -⟩ := G2Q8.factFlagG2_holds K n hn hK _ hsq _ _ π hπ P hP
      exact ⟨U₁, by rw [hK]; exact hU₁⟩
    · intro P U hP hU
      exact G2Q8.factSylowLeviG2_holds K n hn hK _ hsq _ _ π hπ P hP U (by rw [← hK]; exact hU)
    · intro P U hP hU
      exact G2Q8.factPointG2A_holds K n hn hK _ hsq _ _ π hπ P hP U (by rw [← hK]; exact hU)

end CFSG.Quasithin.Vol2.Ch11.SecB
