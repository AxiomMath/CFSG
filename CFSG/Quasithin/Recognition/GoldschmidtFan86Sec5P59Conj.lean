module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P59Gen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Core

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P59

theorem cen_conj_stab1 {g z : G} {u : V}
    (hz : z ∈ Cen (MulAction.stabilizer G u : Set G)) :
    g * z * g⁻¹ ∈ Cen (MulAction.stabilizer G (g • u) : Set G) := by
  refine (P55.cen_conj_iff g (fun k => ?_) z).2 hz
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul, inv_smul_smul]
  exact (MulAction.injective g).eq_iff

variable {ℓ : Line Γ}

theorem cen_conj_swap {a : ℤ} {x z : G} (hx1 : x • ℓ.vert a = ℓ.vert a)
    (hx2 : x • ℓ.vert (a + 1) = ℓ.vert (a - 1))
    (hz : z ∈ Cen (ℓ.edgeStab (G := G) a : Set G)) :
    x * z * x⁻¹ ∈ Cen (ℓ.edgeStab (G := G) (a - 1) : Set G) := by
  have h := cen_conj_stab (g := x) (u := ℓ.vert a) (w := ℓ.vert (a + 1)) hz
  rw [hx1, hx2] at h
  have e : ℓ.edgeStab (G := G) (a - 1) = MulAction.stabilizer G (ℓ.vert a) ⊓
      MulAction.stabilizer G (ℓ.vert (a - 1)) := by
    unfold Line.edgeStab
    rw [sub_add_cancel, inf_comm]
  rw [e]
  exact h

theorem cen_edge_left {i : ℤ} {z : G} (h0 : z • ℓ.vert i = ℓ.vert i)
    (h1 : z • ℓ.vert (i + 1) = ℓ.vert (i + 1))
    (hz : z ∈ Cen (MulAction.stabilizer G (ℓ.vert i) : Set G)) :
    z ∈ Cen (ℓ.edgeStab (G := G) i : Set G) :=
  ⟨⟨MulAction.mem_stabilizer_iff.2 h0, MulAction.mem_stabilizer_iff.2 h1⟩,
    fun h hh => hz.2 h hh.1⟩

theorem cen_edge_right {i : ℤ} {z : G} (h0 : z • ℓ.vert i = ℓ.vert i)
    (h1 : z • ℓ.vert (i + 1) = ℓ.vert (i + 1))
    (hz : z ∈ Cen (MulAction.stabilizer G (ℓ.vert (i + 1)) : Set G)) :
    z ∈ Cen (ℓ.edgeStab (G := G) i : Set G) :=
  ⟨⟨MulAction.mem_stabilizer_iff.2 h0, MulAction.mem_stabilizer_iff.2 h1⟩,
    fun h hh => hz.2 h hh.2⟩

theorem cen_unconj {x z : G} {u v : V} (huv : x • v = u)
    (h : x * z * x⁻¹ ∈ Cen (MulAction.stabilizer G u : Set G)) :
    z ∈ Cen (MulAction.stabilizer G v : Set G) := by
  have := cen_conj_stab1 (g := x⁻¹) h
  rw [← huv, inv_smul_smul] at this
  simpa [mul_assoc] using this

theorem z1_core (F : FanTree Γ G) (h40 : Fan40 F) (h53a : Fan53a F) (hfin : ZcFin F)
    (T : Track Γ G) {z x : G} {a tL tR : ℤ} (hz : z ∈ T.line.ZZ) (hz1 : z ≠ 1)
    (hd : T.line.IsCoreFix z a (a + 1) tL tR) (hx1 : x • T.line.vert a = T.line.vert a)
    (hx2 : x • T.line.vert (a + 1) = T.line.vert (a - 1)) :
    x * z * x⁻¹ ∈ T.line.ZZ ∧ x * z * x⁻¹ ≠ 1 ∧
      ∃ tL1 tR1 : ℤ, T.line.IsCoreFix (x * z * x⁻¹) (a - 1) a tL1 tR1 := by
  have hcen : z ∈ Cen (T.line.edgeStab (G := G) a : Set G) := hd.core.2.2.1 a le_rfl (by omega)
  have h1 := cen_conj_swap hx1 hx2 hcen
  have hz1ZZ : x * z * x⁻¹ ∈ T.line.ZZ := ⟨P55.sq_conj x hz.1, a - 1, h1⟩
  have hz1ne : x * z * x⁻¹ ≠ 1 := fun h => hz1 (by
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this, h]
    group)
  refine ⟨hz1ZZ, hz1ne, ?_⟩
  obtain ⟨tL1, tR1, hfix⟩ := hfin T _ (P55.zz_le_zc hz1ZZ) hz1ne
  have hP : ∀ k, x * z * x⁻¹ ∈ Cen (T.line.edgeStab (G := G) k : Set G) →
      k ∈ T.line.fixIdx (x * z * x⁻¹) ∧ k + 1 ∈ T.line.fixIdx (x * z * x⁻¹) := fun k hk =>
    ⟨MulAction.mem_stabilizer_iff.1 hk.1.1, MulAction.mem_stabilizer_iff.1 hk.1.2⟩
  obtain ⟨a1, b1, ha1, hb1, hcore⟩ := exists_core T.line
    (P := fun k => x * z * x⁻¹ ∈ Cen (T.line.edgeStab (G := G) k : Set G)) hfix hP h1
  have hr1 : 1 ≤ tR - (a + 1) := (h53a h40 T.line z a (a + 1) tL tR hz hd).1
  have hl1 : 1 ≤ a - tL := (h53a h40 T.line z a (a + 1) tL tR hz hd).2.1
  have hzfix : ∀ i, tL ≤ i → i ≤ tR → z • T.line.vert i = T.line.vert i := fun i h1 h2 =>
    (hd.fix i).2 ⟨h1, h2⟩
  have hbeq : b1 = a := by
    by_contra hne
    have hPa := hcore.2.2.1 a (by omega) (by omega)
    have e : a - 1 + 1 = a := by omega
    have h2 : x * z * x⁻¹ ∈ Cen (T.line.edgeStab (G := G) (a - 1 + 1) : Set G) := by
      rw [e]
      exact hPa
    have hst := cen_stab_of_edges F T.line (a - 1) h1 h2
    rw [e] at hst
    have hzc := cen_unconj hx1 hst
    have hf0 : z • T.line.vert (a - 1) = T.line.vert (a - 1) := hzfix _ (by omega) (by omega)
    have hf1 : z • T.line.vert (a - 1 + 1) = T.line.vert (a - 1 + 1) := by
      rw [e]
      exact hzfix a (by omega) (by omega)
    have hE : z ∈ Cen (T.line.edgeStab (G := G) (a - 1) : Set G) :=
      cen_edge_right hf0 hf1 (by rw [e]; exact hzc)
    exact hd.core.2.2.2.1 ⟨hf0, by simpa using hE⟩
  have haeq : a1 = a - 1 := by
    by_contra hne
    have hPa := hcore.2.2.1 (a - 2) (by omega) (by omega)
    have e : a - 2 + 1 = a - 1 := by omega
    have h2 : x * z * x⁻¹ ∈ Cen (T.line.edgeStab (G := G) (a - 2 + 1) : Set G) := by
      rw [e]
      exact h1
    have hst := cen_stab_of_edges F T.line (a - 2) hPa h2
    rw [e] at hst
    have hzc := cen_unconj hx2 hst
    have hE : z ∈ Cen (T.line.edgeStab (G := G) (a + 1) : Set G) :=
      cen_edge_left (hzfix _ (by omega) (by omega)) (hzfix _ (by omega) (by omega)) hzc
    exact hd.core.2.2.2.2 ⟨hzfix _ (by omega) (by omega), hE⟩
  subst hbeq haeq
  exact ⟨tL1, tR1, hfix, hcore⟩

end P59

end CFSG.Quasithin.Fan86
