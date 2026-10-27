module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2M0
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Set
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtB
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6Stmt

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem exists_triv_y (S : B2Set F L T a) {x : G} (hx : x ∈ MulAction.stabilizer G (xv T a 6))
    (hxo : orderOf x = 5)
    (hN : ∀ g ∈ MulAction.stabilizer G (xv T a 6), ∀ h ∈ labSpan2 L (xv T a 6),
      g * h * g⁻¹ ∈ labSpan2 L (xv T a 6))
    (hE : ∃ q ∈ nbrStab Γ G (xv T a 6), x * q * x⁻¹ * q⁻¹ ∉ ballStab Γ G 2 (xv T a 6))
    (hxT : ActsTriv (ballStab Γ G 2 (xv T a 6)) (labSpan2 L (xv T a 6)) x) :
    ∃ y ∈ MulAction.stabilizer G (xv T a 6),
      ActsTriv (ballStab Γ G 2 (xv T a 6)) (labSpan2 L (xv T a 6)) y ∧
        y • xv T a 5 = xv T a 7 ∧ y • xv T a 4 = xv T a 8 := by
  classical
  have hv5 : valence Γ (xv T a 6) = 5 := by simpa using S.val_even 3
  have hxo' : orderOf x = valence Γ (xv T a 6) := by rw [hv5]; exact hxo
  have hB : ∀ g ∈ MulAction.stabilizer G (xv T a 6), ∀ b ∈ ballStab Γ G 2 (xv T a 6),
      g * b * g⁻¹ ∈ ballStab Γ G 2 (xv T a 6) := by
    intro g hg b hb
    have := ballStab_conj F g hb
    rwa [MulAction.mem_stabilizer_iff.1 hg] at this
  have h56 : Γ.Adj (xv T a 6) (xv T a 5) := by simpa using xv_adj' T a 5
  have h57 : Γ.Adj (xv T a 6) (xv T a 7) := by simpa using xv_adj T a 6
  obtain ⟨q, hqK, hq⟩ := hE
  have hqS : q ∈ MulAction.stabilizer G (xv T a 6) := F.nbrStab_le_stabilizer _ hqK
  have hz0T := ActsTriv.comm hB hN hx hqS hxT
  have hxv : x • xv T a 6 = xv T a 6 := MulAction.mem_stabilizer_iff.1 hx
  have hz0K : x * q * x⁻¹ * q⁻¹ ∈ nbrStab Γ G (xv T a 6) :=
    (nbrStab Γ G (xv T a 6)).mul_mem (nbrStab_conj_mem F hxv hqK)
      ((nbrStab Γ G (xv T a 6)).inv_mem hqK)
  obtain ⟨ν, hν, hzν⟩ := exists_nbr_not_nbrStab F hz0K hq
  obtain ⟨i, hi⟩ := F.exists_pow_smul_eq hx hxo' hν h56
  have hhS : x ^ i ∈ MulAction.stabilizer G (xv T a 6) := Subgroup.pow_mem _ hx i
  have hhv : x ^ i • xv T a 6 = xv T a 6 := MulAction.mem_stabilizer_iff.1 hhS
  set y₀ : G := x ^ i * (x * q * x⁻¹ * q⁻¹) * (x ^ i)⁻¹ with hy₀
  have hy0T : ActsTriv (ballStab Γ G 2 (xv T a 6)) (labSpan2 L (xv T a 6)) y₀ :=
    hz0T.conj hB hN hhS
  have hy0K : y₀ ∈ nbrStab Γ G (xv T a 6) := nbrStab_conj_mem F hhv hz0K
  have hy0S : y₀ ∈ MulAction.stabilizer G (xv T a 6) := F.nbrStab_le_stabilizer _ hy0K
  have hy0n : y₀ ∉ nbrStab Γ G (xv T a 5) := by
    intro h
    rw [← hi] at h
    have := (F.mem_nbrStab_smul_iff (x ^ i) ν).1 h
    have e : (x ^ i)⁻¹ * y₀ * x ^ i = x * q * x⁻¹ * q⁻¹ := by rw [hy₀]; group
    rw [e] at this
    exact hzν this
  have h45 : Γ.Adj (xv T a 5) (xv T a 4) := by simpa using xv_adj' T a 4
  have hne46 : xv T a 4 ≠ xv T a 6 := by simpa using xv_ne T a 4
  have hy0mv : y₀ • xv T a 4 ≠ xv T a 4 :=
    smul_ne_of_not_nbrStab F (MulAction.mem_stabilizer_iff.1 hy0S) h56.symm h45 hne46 hy0n
  obtain ⟨k, hk⟩ := F.exists_pow_smul_eq hx hxo' h56 h57
  have hkv : x ^ k • xv T a 6 = xv T a 6 :=
    MulAction.mem_stabilizer_iff.1 (Subgroup.pow_mem _ hx k)
  have h78 : Γ.Adj (xv T a 7) (xv T a 8) := by simpa using xv_adj T a 7
  have hne68 : xv T a 6 ≠ xv T a 8 := by simpa using xv_ne T a 6
  by_cases hc : x ^ k • xv T a 4 = xv T a 8
  · exact ⟨x ^ k, Subgroup.pow_mem _ hx k, hxT.pow hN hx k, hk, hc⟩
  · have hy05 : y₀ • xv T a 5 = xv T a 5 := mem_nbrStab.1 hy0K _ h56
    refine ⟨x ^ k * y₀, (MulAction.stabilizer G (xv T a 6)).mul_mem
      (Subgroup.pow_mem _ hx k) hy0S, ActsTriv.mul hN (Subgroup.pow_mem _ hx k)
      (hxT.pow hN hx k) hy0T, ?_, ?_⟩
    · rw [mul_smul, hy05, hk]
    · rw [mul_smul]
      by_contra hne
      have hc3 : valence Γ (xv T a 7) = 3 := by simpa using S.val_odd 3
      have hy0v : y₀ • xv T a 6 = xv T a 6 := MulAction.mem_stabilizer_iff.1 hy0S
      have hadj4 : Γ.Adj (xv T a 7) (x ^ k • xv T a 4) := by
        have := (F.adj_smul (x ^ k) _ _).2 h45
        rwa [hk] at this
      have hadj4' : Γ.Adj (xv T a 7) (x ^ k • y₀ • xv T a 4) := by
        have h1 : Γ.Adj (xv T a 5) (y₀ • xv T a 4) := by
          have := (F.adj_smul y₀ _ _).2 h45
          rwa [hy05] at this
        have := (F.adj_smul (x ^ k) _ _).2 h1
        rwa [hk] at this
      refine F.false_of_four_nbrs hc3 h57.symm h78 hadj4 hadj4' (a₁ := xv T a 6)
        (a₂ := xv T a 8) (a₃ := x ^ k • xv T a 4) (a₄ := x ^ k • y₀ • xv T a 4) hne68 ?_ ?_
        (Ne.symm hc) ?_ ?_
      · intro h
        have := congrArg (fun w => (x ^ k)⁻¹ • w) h
        simp only [inv_smul_smul] at this
        rw [← hkv, inv_smul_smul] at this
        exact hne46 this.symm
      · intro h
        have h2 : y₀ • xv T a 6 = y₀ • xv T a 4 := by
          have := congrArg (fun w => (x ^ k)⁻¹ • w) h
          simp only [inv_smul_smul] at this
          rw [← hkv, inv_smul_smul] at this
          rw [hy0v]
          exact this
        exact hne46 (MulAction.injective y₀ h2).symm
      · exact Ne.symm hne
      · intro h
        exact hy0mv (MulAction.injective (x ^ k) h).symm

end P518

end CFSG.Quasithin.Fan86
