module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2M1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Far

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem mLayer_of (S : B2Set F L T a) {x : G} (hx : x ∈ MulAction.stabilizer G (xv T a 6))
    (hxo : orderOf x = 5)
    (hN : ∀ g ∈ MulAction.stabilizer G (xv T a 6), ∀ h ∈ labSpan2 L (xv T a 6),
      g * h * g⁻¹ ∈ labSpan2 L (xv T a 6))
    (hC : ∀ g ∈ ballStab Γ G 2 (xv T a 6), ∀ h ∈ labSpan2 L (xv T a 6), g * h = h * g)
    (hE : ∃ q ∈ nbrStab Γ G (xv T a 6), x * q * x⁻¹ * q⁻¹ ∉ ballStab Γ G 2 (xv T a 6)) :
    ∃ g ∈ ballStab Γ G 2 (xv T a 6), x * g * x⁻¹ * g⁻¹ ∉ labSpan2 L (xv T a 6) := by
  classical
  by_contra hcon
  push Not at hcon
  have hxT : ActsTriv (ballStab Γ G 2 (xv T a 6)) (labSpan2 L (xv T a 6)) x := hcon
  obtain ⟨y, hyS, hyT, hy5, hy4⟩ := exists_triv_y S hx hxo hN hE hxT
  have h57 : Γ.Adj (xv T a 6) (xv T a 7) := by simpa using xv_adj T a 6
  have h78 : Γ.Adj (xv T a 7) (xv T a 8) := by simpa using xv_adj T a 7
  have hv2 : valence Γ (xv T a 2) = 5 := by simpa using S.val_even 1
  have hA1B : L.z (xv T a 2) ∈ ballStab Γ G 2 (xv T a 6) := by
    have := S.claimA_fwd 1
    simpa [zA] using this
  have hfix : ∀ i : ℤ, L.z (xv T a 2) • xv T a i = xv T a i ↔ -4 ≤ i ∧ i ≤ 8 := by
    intro i
    have := S.zA_fix_iff 1 i
    simp only [zA] at this
    norm_num at this
    exact this
  have hA7 : L.z (xv T a 2) • xv T a 7 = xv T a 7 := (hfix 7).2 ⟨by norm_num, by norm_num⟩
  have hA8 : L.z (xv T a 2) • xv T a 8 = xv T a 8 := (hfix 8).2 ⟨by norm_num, by norm_num⟩
  have hA9 : L.z (xv T a 2) • xv T a 9 ≠ xv T a 9 := fun h => by
    have := (hfix 9).1 h
    omega
  have h89 : Γ.Adj (xv T a 8) (xv T a 9) := by simpa using xv_adj T a 8
  have h43 : Γ.Adj (xv T a 4) (xv T a 3) := by simpa using xv_adj' T a 3
  have h32 : Γ.Adj (xv T a 3) (xv T a 2) := by simpa using xv_adj' T a 2
  have ht8 : Γ.Adj (xv T a 8) (y • xv T a 3) := by
    have := (F.adj_smul y _ _).2 h43
    rwa [hy4] at this
  have hts : Γ.Adj (y • xv T a 3) (y • xv T a 2) := (F.adj_smul y _ _).2 h32
  have hne35 : xv T a 3 ≠ xv T a 5 := by simpa using xv_ne T a 3
  have ht7 : y • xv T a 3 ≠ xv T a 7 := by
    rw [← hy5]
    exact fun h => hne35 (MulAction.injective y h)
  have hct : L.z (xv T a 2) • y • xv T a 3 ≠ y • xv T a 3 := by
    intro h
    have hnb : L.z (xv T a 2) ∈ nbrStab Γ G (xv T a 8) :=
      F.fix_two_nbrs ht8 h78.symm ht7 h hA7
    exact hA9 (mem_nbrStab.1 hnb _ h89)
  have hne82 : xv T a 8 ≠ y • xv T a 2 := by
    have hne24 : xv T a 2 ≠ xv T a 4 := by simpa using xv_ne T a 2
    rw [← hy4]
    exact fun h => hne24 (MulAction.injective y h).symm
  have hcs : L.z (xv T a 2) • y • xv T a 2 ≠ y • xv T a 2 := by
    intro h
    have h1 : Γ.Adj (xv T a 8) (L.z (xv T a 2) • y • xv T a 3) := by
      have := (F.adj_smul (L.z (xv T a 2)) _ _).2 ht8
      rwa [hA8] at this
    have h2 : Γ.Adj (L.z (xv T a 2) • y • xv T a 3) (y • xv T a 2) := by
      have := (F.adj_smul (L.z (xv T a 2)) _ _).2 hts
      rwa [h] at this
    exact hct (F.eq_of_adj_adj ht8 hts h1 h2 hne82).symm
  have hsq : L.z (xv T a 2) * L.z (xv T a 2) = 1 := z_sq hv2
  have hcinv : (L.z (xv T a 2))⁻¹ = L.z (xv T a 2) := z_inv hv2
  have hzs : L.z (y • xv T a 2) = y * L.z (xv T a 2) * y⁻¹ := z_smul hv2 y
  have hw' : L.z (y • xv T a 2) * L.z (xv T a 2) ∈ labSpan2 L (xv T a 6) := by
    have := hyT _ hA1B
    rwa [hcinv, ← hzs] at this
  have hcomm := hC _ hA1B _ hw'
  have hcz : L.z (xv T a 2) * L.z (y • xv T a 2) = L.z (y • xv T a 2) * L.z (xv T a 2) := by
    have h' : L.z (xv T a 2) * L.z (y • xv T a 2) * L.z (xv T a 2) = L.z (y • xv T a 2) := by
      have e1 : (L.z (y • xv T a 2) * L.z (xv T a 2)) * L.z (xv T a 2) = L.z (y • xv T a 2) := by
        rw [mul_assoc, hsq, mul_one]
      rw [e1] at hcomm
      simpa [mul_assoc] using hcomm
    calc L.z (xv T a 2) * L.z (y • xv T a 2)
        = L.z (xv T a 2) * L.z (y • xv T a 2) * (L.z (xv T a 2) * L.z (xv T a 2)) := by
          rw [hsq, mul_one]
      _ = (L.z (xv T a 2) * L.z (y • xv T a 2) * L.z (xv T a 2)) * L.z (xv T a 2) := by
          simp only [mul_assoc]
      _ = L.z (y • xv T a 2) * L.z (xv T a 2) := by rw [h']
  have hv5s : valence Γ (y • xv T a 2) = 5 := by rw [F.valence_smul_eq]; exact hv2
  have hv5cs : valence Γ (L.z (xv T a 2) • y • xv T a 2) = 5 := by
    rw [F.valence_smul_eq]; exact hv5s
  have hzc : L.z (L.z (xv T a 2) • y • xv T a 2) = L.z (y • xv T a 2) := by
    rw [z_smul hv5s, hcinv, hcz, mul_assoc, hsq, mul_one]
  have hd2 : Γ.dist (xv T a 8) (y • xv T a 2) = 2 := by
    rw [← hy4, dist_smul F y]
    simpa using xv_dist_two' F T a 2
  have hd2' : Γ.dist (L.z (xv T a 2) • y • xv T a 2) (xv T a 8) = 2 := by
    calc Γ.dist (L.z (xv T a 2) • y • xv T a 2) (xv T a 8)
        = Γ.dist (L.z (xv T a 2) • y • xv T a 2) (L.z (xv T a 2) • xv T a 8) := by rw [hA8]
      _ = Γ.dist (y • xv T a 2) (xv T a 8) := dist_smul F _ _ _
      _ = Γ.dist (xv T a 8) (y • xv T a 2) := SimpleGraph.dist_comm
      _ = 2 := hd2
  have hconn := F.isTree.connected
  have hpos := hconn.pos_dist_of_ne hcs
  have hev := P71.dist_even F hv5cs hv5s
  have hle : Γ.dist (L.z (xv T a 2) • y • xv T a 2) (y • xv T a 2) ≤ 4 := by
    have := hconn.dist_triangle (u := L.z (xv T a 2) • y • xv T a 2) (v := xv T a 8)
      (w := y • xv T a 2)
    rw [hd2', hd2] at this
    omega
  have hdist : Γ.dist (L.z (xv T a 2) • y • xv T a 2) (y • xv T a 2) = 2 ∨
      Γ.dist (L.z (xv T a 2) • y • xv T a 2) (y • xv T a 2) = 4 := by omega
  exact S.lab.hyp.dist _ _ hcs hv5cs hv5s hdist hzc


end P518

end CFSG.Quasithin.Fan86
