module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425B

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

namespace Set425

variable {T M L Mm I H : Subgroup G} (s : Set425 G T M L Mm I H)
include s

theorem L_le_inf (c : Inp425 G) : L ≤ H ⊓ M := le_inf (s.lemma_4_2_7_one c).2.1 s.hyp.L_le

theorem H0_le (c : Inp425 G) : conjClosure L H ≤ H ⊓ M :=
  CFSG.Quasithin.conjClosure_le fun _ hg _ hl =>
    (Subgroup.mem_normalizer_iff.mp (s.le_normalizer_inf c hg) _).mp (s.L_le_inf c hl)

theorem H0_le_normalizer (c : Inp425 G) :
    conjClosure L H ≤ Subgroup.normalizer (L : Set G) := by
  have h := s.H0_le c
  rw [s.inf_eq c] at h
  exact h.trans inf_le_right

theorem H0_perfect : ⁅conjClosure L H, conjClosure L H⁆ = conjClosure L H :=
  A3.conjClosure_perfect s.hyp.perfect

theorem pCoreOf_L_ne_bot (c : Inp425 G) : pCoreOf 2 L ≠ ⊥ := by
  intro h0
  have hLc : CharTwo L :=
    CharTwo.of_isSubnormal s.charTwo_M s.hyp.L_le
      ((isSubnormal_iff_subgroupOf s.hyp.L_le).mp
        (subnormal_of_mem_cComp (s.hyp.mem_cComp c.a37 c.a39)))
  have hL : L ≤ pCoreOf 2 L := by
    have h1 : L ≤ L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
      rw [h0]
      exact le_inf le_rfl fun x _ => by simp [Subgroup.mem_centralizer_iff]
    exact h1.trans hLc
  rw [h0] at hL
  exact ne_bot_of_mem_cComp (s.hyp.mem_cComp c.a37 c.a39) (le_bot_iff.mp hL)

theorem pCoreOf_H0_ne_bot (c : Inp425 G) : pCoreOf 2 (conjClosure L H) ≠ ⊥ := by
  intro h0
  have hle : pCoreOf 2 L ≤ pCoreOf 2 (conjClosure L H) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans (le_conjClosure L H))
      ((s.H0_le_normalizer c).trans (normalizer_le_normalizer_pCoreOf 2 L))
      (pCoreOf_isPGroup 2 L)
  rw [h0] at hle
  exact s.pCoreOf_L_ne_bot c (le_bot_iff.mp hle)

theorem lemma_4_2_8 (c : Inp425 G) : Subgroup.normalizer (conjClosure L H : Set G) = H := by
  have hX : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (conjClosure L H) : Set G)) :=
    ⟨_, s.pCoreOf_H0_ne_bot c, pCoreOf_isPGroup 2 _, rfl⟩
  have hHX : H ≤ Subgroup.normalizer (pCoreOf 2 (conjClosure L H) : Set G) :=
    (CFSG.Quasithin.le_normalizer_conjClosure L H).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have heq := s.inM.1.2 _ hX hHX
  refine le_antisymm ?_ (CFSG.Quasithin.le_normalizer_conjClosure L H)
  calc Subgroup.normalizer (conjClosure L H : Set G)
      ≤ Subgroup.normalizer (pCoreOf 2 (conjClosure L H) : Set G) :=
        normalizer_le_normalizer_pCoreOf 2 _
    _ = H := heq

theorem exists_h : ∃ h ∈ H, h ∉ M := by
  by_contra hcon
  push Not at hcon
  exact s.not_le hcon

theorem conj_h (c : Inp425 G) {h : G} (hh : h ∈ H) (hhM : h ∉ M) :
    L.map (MulAut.conj h).toMonoidHom ∈ cComp H ∧ L.map (MulAut.conj h).toMonoidHom ≠ L ∧
      L.map (MulAut.conj h).toMonoidHom ≤ conjClosure L H := by
  refine ⟨map_conj_mem_cComp (s.lemma_4_2_7_one c).2.2 hh, fun he => hhM ?_, ?_⟩
  · have hN : h ∈ H ⊓ Subgroup.normalizer (L : Set G) :=
      ⟨hh, Subgroup.mem_normalizer_iff_map_conj_eq.mpr he⟩
    rw [← s.inf_eq c] at hN
    exact hN.2
  · rintro _ ⟨l, hl, rfl⟩
    exact mem_conjClosure hh hl

theorem lemma_4_2_9 (c : Inp425 G) : oTwoFIn M ≤ H := by
  by_contra hnot
  have hnot' : ¬ oTwoFIn M ≤ H ⊓ M := fun h => hnot (h.trans inf_le_left)
  have hO := s.oddCoreIn_M
  obtain ⟨r, Lb, hLb, hprod⟩ :=
    c2_6_two c.c129 s.hypC23 (charTwo_oTwoFIn_of_oddCore_eq_bot hO) hnot'
  have hr : 0 < r := by
    by_contra hr0
    obtain rfl : r = 0 := Nat.eq_zero_of_not_pos hr0
    apply hnot'
    intro x hx
    obtain ⟨m, hm, y, -, rfl⟩ := hprod x hx
    simpa using hm.1
  obtain ⟨hXb, hX3, hXM⟩ := hLb ⟨0, hr⟩
  set X : Subgroup G := Lb ⟨0, hr⟩ with hXdef
  have hXH : IsBlock2 M X := C2Eleven.isBlock2_of_isBlock2_oTwoFIn hXb
  obtain ⟨y, hyX, hyp, hy2, hyc⟩ :=
    exists_noncentral_odd_prime_of_isChi0Block (X := oTwoFIn M) (B := X)
      ⟨hXb, Or.inr (Or.inl hX3)⟩
  have hH0M : conjClosure L H ≤ M := (s.H0_le c).trans inf_le_right
  have hnorm := perfect_le_normalizer_of_odd_prime c.c19 s.hypC23.sqtk hO hH0M s.H0_perfect hXH
    hyX hyp hy2 hyc
  have hcent := perfect_le_centralizer_of_isAltType_three hXH.1 hX3 hnorm s.H0_perfect
  have hXN : X ≤ Subgroup.normalizer (conjClosure L H : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (hcent hz) x hx).symm)
  rw [s.lemma_4_2_8 c] at hXN
  exact hXM (le_inf hXN hXH.2.1)

end Set425

end CFSG.Quasithin.H13.Ch4
