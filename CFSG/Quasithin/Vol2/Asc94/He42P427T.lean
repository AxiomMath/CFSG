module

public import CFSG.Quasithin.Vol2.Asc94.He42P427H4
public import CFSG.Quasithin.Vol2.Asc94.HeM2
public import CFSG.Quasithin.Vol2.Asc94.TSSetting
public import CFSG.Quasithin.Vol2.Asc94.HeJ5

public section

namespace CFSG.Quasithin.A94.He42P427T

open CFSG.Quasithin.A94.L52 CFSG.Quasithin.A94 Subgroup

variable {G : Type} [Group G] [Finite G] {z : G} (e : ↥(Cz z) ≃* L52.Hc)

theorem tr_cent1 (x : L52.Hc) :
    centralizer ({z} : Set G) ⊓ centralizer ({emb e x} : Set G) =
      tr e (centralizer ({x} : Set L52.Hc)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgz, hgx⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨y, rfl⟩ := exists_emb e hgz
    have hc : y * x = x * y := (emb_mul_comm e).1 (mem_centralizer_singleton_iff.1 hgx)
    exact emb_mem_tr e (mem_centralizer_singleton_iff.2 hc)
  · intro hg
    obtain ⟨y, hy, rfl⟩ := hg
    refine Subgroup.mem_inf.2 ⟨emb_mem_Cz e y, mem_centralizer_singleton_iff.2 ?_⟩
    exact (emb_mul_comm e).2 (mem_centralizer_singleton_iff.1 hy)

theorem tr_cent2 (x c : L52.Hc) :
    centralizer ({z} : Set G) ⊓ centralizer ({emb e x} : Set G) ⊓ centralizer ({emb e c} : Set G) =
      tr e (centralizer ({x} : Set L52.Hc) ⊓ centralizer ({c} : Set L52.Hc)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgzx, hgc⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hgz, hgx⟩ := Subgroup.mem_inf.1 hgzx
    obtain ⟨y, rfl⟩ := exists_emb e hgz
    have hx : y * x = x * y := (emb_mul_comm e).1 (mem_centralizer_singleton_iff.1 hgx)
    have hc : y * c = c * y := (emb_mul_comm e).1 (mem_centralizer_singleton_iff.1 hgc)
    exact emb_mem_tr e (Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 hx,
      mem_centralizer_singleton_iff.2 hc⟩)
  · intro hg
    obtain ⟨y, hy, rfl⟩ := hg
    obtain ⟨hyx, hyc⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨emb_mem_Cz e y,
      mem_centralizer_singleton_iff.2 ((emb_mul_comm e).2 (mem_centralizer_singleton_iff.1 hyx))⟩,
      mem_centralizer_singleton_iff.2 ((emb_mul_comm e).2 (mem_centralizer_singleton_iff.1 hyc))⟩

open CFSG.Quasithin.A94.He42P427H in
theorem zC_abar : L52.zC abar = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L52.zC_apply, cm_abar, L52.rIdx, L52.cIdx, Matrix.one_apply]

open CFSG.Quasithin.A94.He42P427H in
theorem a_eq_emb_abar {a : G} (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1) :
    a = emb e abar := by
  obtain ⟨ã, hã1, hã⟩ := (Subgroup.mem_inf.1 ha).1
  obtain ⟨ã', hã2, hã'⟩ := (Subgroup.mem_inf.1 ha).2
  have hEq : ã = ã' := emb_injective e (hã.trans hã'.symm)
  subst hEq
  have hz : L52.zC ã = 1 := by
    rw [← HeJ.mG_emb e ã, hã, ham]
  have hzA : L52.zC abar = 1 := zC_abar
  have hAbar : abar ∈ L52.A1 ⊓ L52.A2 := Subgroup.mem_inf.2 ⟨abar_mem_A1, abar_mem_A2⟩
  have heq : ã = abar := L52.zC_injOn (Subgroup.mem_inf.2 ⟨hã1, hã2⟩) hAbar (hz.trans hzA.symm)
  rw [← hã, heq]

end CFSG.Quasithin.A94.He42P427T
