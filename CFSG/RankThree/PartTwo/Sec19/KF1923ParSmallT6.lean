module

public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSmallGroups
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LL34A5
public import CFSG.RankThree.PartTwo.KFacts.KS14SL34

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19 (IsTripleA6 IsProperParabolic)

theorem ksm_ker_conj {X : Type} [Group X] :
    (MulAut.conj : X →* MulAut X).ker = Subgroup.center X := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hx g
    have h1 := DFunLike.congr_fun hx g
    rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  · intro hx
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul, hx g]

theorem ksm_tripleA6_card {X : Type} [Group X] (hT : IsTripleA6 X) : Nat.card X = 1080 := by
  obtain ⟨hZ3, ⟨φ⟩⟩ := hT
  have h1 := Subgroup.card_mul_index (Subgroup.center X)
  have h2 : (Subgroup.center X).index = 360 := by
    rw [Subgroup.index, Nat.card_congr φ.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  rw [hZ3, h2] at h1
  omega

theorem ksm_tripleA6_nine {X : Type} [Group X] [Finite X]
    (hT : IsTripleA6 X) (hX : CFSG.IsQuasisimple X) : KSmNoNineMap X := by
  obtain ⟨hZ3, ⟨φ⟩⟩ := hT
  haveI : Group.IsPerfect X := hX.1
  have hXc : Nat.card X = 1080 := ksm_tripleA6_card ⟨hZ3, ⟨φ⟩⟩
  have hA6c : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hQc : Nat.card (X ⧸ Subgroup.center X) = 360 :=
    (Nat.card_congr φ.toEquiv).trans hA6c
  have hNF : CFSG.AGLEmbedding.ParabHub.NineFreeOver (alternatingGroup (Fin 6)) :=
    CFSG.AGLEmbedding.ParabHub.nineFreeOver_alt_six
  intro P hP hdvd
  unfold ParabolicShape at hP
  rcases hP with ⟨-, hprop⟩ | ⟨-, hext⟩
  swap
  · exact ksm_nine_ext hext (dvd_trans hdvd (Subgroup.card_map_dvd (H := P) _))
  obtain ⟨hPtop, T, hTN⟩ := hprop
  have hA : Nat.card (P.map (MulAut.conj : X →* MulAut X)) =
      Nat.card (P.map (QuotientGroup.mk' (Subgroup.center X))) := by
    have h1 := CFSG.RankThree.PartTwo.Sec4.Ronan148L.card_map_mul_card_inf_ker
      (MulAut.conj : X →* MulAut X) P
    have h2 := CFSG.RankThree.PartTwo.Sec4.Ronan148L.card_map_mul_card_inf_ker
      (QuotientGroup.mk' (Subgroup.center X)) P
    rw [ksm_ker_conj] at h1
    rw [QuotientGroup.ker_mk'] at h2
    haveI : Nonempty ↥(P ⊓ Subgroup.center X) := ⟨1⟩
    have hpos : 0 < Nat.card ↥(P ⊓ Subgroup.center X) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
  rw [hA] at hdvd
  set Pbar : Subgroup (X ⧸ Subgroup.center X) :=
    P.map (QuotientGroup.mk' (Subgroup.center X)) with hPbar
  set Q : Subgroup (alternatingGroup (Fin 6)) := Pbar.map φ.toMonoidHom with hQdef
  have hQcard : Nat.card Q = Nat.card Pbar := Subgroup.card_map_of_injective φ.injective
  obtain ⟨T', hT'⟩ : ∃ T' : Subgroup X, T' = (T : Subgroup X) := ⟨_, rfl⟩
  have hTP : T' ≤ P := by
    rw [hT']
    exact le_trans Subgroup.le_normalizer hTN
  have hT'syl : CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ := by
    rw [hT']
    exact ksm_isSylow_top_of_sylow T
  have hT'pg : IsPGroup 2 T' := by
    rw [hT']
    exact T.isPGroup'
  have hT'idx : ¬ 2 ∣ T'.index := by
    have := (CFSG.ABGLocalTools.isSylowOf_iff.1 hT'syl).2.2
    rwa [Subgroup.relIndex_top_right] at this
  have hTZ : T' ⊓ Subgroup.center X = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzT, hzZ⟩ := Subgroup.mem_inf.1 hz
    have h3w : (⟨z, hzZ⟩ : Subgroup.center X) ^ 3 = 1 := by
      have hcard : Nat.card (Subgroup.center X) = 3 := hZ3
      rw [← hcard]
      exact pow_card_eq_one'
    have hz3 : z ^ 3 = 1 := by
      have := congrArg Subtype.val h3w
      simpa using this
    obtain ⟨k, hk⟩ := hT'pg ⟨z, hzT⟩
    have hzk : z ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact Subgroup.mem_bot.2 (ksm_eq_one hz3 hzk)
  have hT'Pbar : Nat.card T' = Nat.card (T'.map (QuotientGroup.mk' (Subgroup.center X))) := by
    have h1 := CFSG.RankThree.PartTwo.Sec4.Ronan148L.card_map_mul_card_inf_ker
      (QuotientGroup.mk' (Subgroup.center X)) T'
    rw [QuotientGroup.ker_mk', hTZ, Subgroup.card_bot] at h1
    omega
  set T6 : Subgroup (alternatingGroup (Fin 6)) :=
    (T'.map (QuotientGroup.mk' (Subgroup.center X))).map φ.toMonoidHom with hT6def
  have hT6card : Nat.card T6 = Nat.card T' := by
    rw [hT6def, Subgroup.card_map_of_injective φ.injective]
    exact hT'Pbar.symm
  have hidx1 := Subgroup.card_mul_index T'
  have hidx2 := Subgroup.card_mul_index T6
  rw [hXc] at hidx1
  rw [hA6c] at hidx2
  have hTpos : 0 < Nat.card T' := Nat.card_pos
  have h360 : Nat.card T' * T6.index = 360 := by
    rw [← hT6card, hidx2]
  have hrel : T'.index = 3 * T6.index := by
    apply Nat.eq_of_mul_eq_mul_left hTpos
    rw [hidx1, mul_left_comm, h360] <;> norm_num
  have hT6idx : ¬ 2 ∣ T6.index := by omega
  have hT6pg : IsPGroup 2 T6 :=
    (hT'pg.map (QuotientGroup.mk' (Subgroup.center X))).map φ.toMonoidHom
  have hT6syl : CFSG.RankThree.PartOne.IsSylowOf 2 T6 ⊤ := by
    refine ⟨le_top, hT6pg, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact hT6idx
  have hT6S := CFSG.CGT.PushingUpLit.BHS6.isSylowTwoOf_of_isSylowOf hT6syl
  have hT6Q : T6 ≤ Q :=
    Subgroup.map_mono (Subgroup.map_mono hTP)
  have h9Q : 9 ∣ Nat.card Q := by
    rw [hQcard]
    exact hdvd
  have hQtop : Q = ⊤ := hNF T6 Q hT6S hT6Q h9Q
  have hPb360 : Nat.card Pbar = 360 := by
    rw [← hQcard, hQtop, Subgroup.card_top, hA6c]
  have hPbtop : Pbar = ⊤ :=
    Subgroup.eq_top_of_card_eq Pbar (by rw [hPb360, hQc])
  have hmZ : Nat.card ↥(P ⊓ Subgroup.center X) ∣ 3 := by
    have hle : P ⊓ Subgroup.center X ≤ Subgroup.center X := inf_le_right
    have := Subgroup.card_dvd_of_le hle
    rwa [hZ3] at this
  have hPcard : Nat.card P = 360 * Nat.card ↥(P ⊓ Subgroup.center X) := by
    have h2 := CFSG.RankThree.PartTwo.Sec4.Ronan148L.card_map_mul_card_inf_ker
      (QuotientGroup.mk' (Subgroup.center X)) P
    rw [QuotientGroup.ker_mk', hPb360] at h2
    exact h2
  rcases (Nat.dvd_prime Nat.prime_three).1 hmZ with hm1 | hm3
  ·
    have hPidx : P.index = 3 := by
      have h := Subgroup.card_mul_index P
      rw [hPcard, hm1, hXc] at h
      omega
    exact CFSG.RankThree.PartTwo.KFacts.KS14.index_ne_three_of_isPerfect P hPidx
  ·
    have hinf : P ⊓ Subgroup.center X = Subgroup.center X :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [hZ3, hm3]))
    apply hPtop
    rw [eq_top_iff]
    intro x _
    have hx : (QuotientGroup.mk x : X ⧸ Subgroup.center X) ∈ Pbar := by
      rw [hPbtop]
      exact Subgroup.mem_top _
    obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.1 hx
    have hpx' : p⁻¹ * x ∈ Subgroup.center X := QuotientGroup.eq.1 hpx
    have hzP : p⁻¹ * x ∈ P := by
      have hz' : p⁻¹ * x ∈ P ⊓ Subgroup.center X := by
        rw [hinf]
        exact hpx'
      exact (Subgroup.mem_inf.1 hz').1
    have hxeq : x = p * (p⁻¹ * x) := by group
    rw [hxeq]
    exact P.mul_mem hp hzP

end CFSG.RankThree.PartTwo.Late
