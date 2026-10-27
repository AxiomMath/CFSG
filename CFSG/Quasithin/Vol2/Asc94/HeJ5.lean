module

public import CFSG.Quasithin.Vol2.Asc94.HeJ2
public import CFSG.Quasithin.Vol2.Asc94.HeM1
public import CFSG.Quasithin.Vol2.Asc94.HeK1

public section

namespace CFSG.Quasithin.A94.HeJ

open Subgroup CFSG.CGT.M24S

variable {G : Type} [Group G] [Finite G] {z : G} (e : ↥(Cz z) ≃* L52.Hc)

open Classical in
@[expose] noncomputable def toH (x : G) : L52.Hc := if h : x ∈ Cz z then e ⟨x, h⟩ else 1

theorem toH_emb (y : L52.Hc) : toH e (emb e y) = y := by
  unfold toH
  rw [dif_pos (emb_mem_Cz e y)]
  simp [emb]

@[expose] noncomputable def uG (x : G) : V2 := L52.uC (toH e x)

@[expose] noncomputable def wG (x : G) : V2 := L52.wC (toH e x)

@[expose] noncomputable def mG (x : G) : M2 := L52.zC (toH e x)

theorem uG_emb (y : L52.Hc) : uG e (emb e y) = L52.uC y := by rw [uG, toH_emb]

theorem wG_emb (y : L52.Hc) : wG e (emb e y) = L52.wC y := by rw [wG, toH_emb]

theorem mG_emb (y : L52.Hc) : mG e (emb e y) = L52.zC y := by rw [mG, toH_emb]

theorem tdata : TData (tr e L52.A1) (tr e L52.A2) (uG e) (wG e) (mG e) where
  cu :=
    { mul := by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [← map_mul, uG_emb, uG_emb, uG_emb, L52.uC_mul hx hy]
      zero := by
        rintro _ ⟨x, hx, rfl⟩
        rw [uG_emb, L52.uC_eq_zero_iff hx, emb_mem_tr_iff]
      surj := fun v => by
        obtain ⟨x, hx, hxv⟩ := L52.exists_uC v
        exact ⟨emb e x, emb_mem_tr e hx, by rw [uG_emb, hxv]⟩ }
  cw :=
    { mul := by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [← map_mul, wG_emb, wG_emb, wG_emb, L52.wC_mul hx hy]
      zero := by
        rintro _ ⟨x, hx, rfl⟩
        rw [wG_emb, L52.wC_eq_zero_iff hx, emb_mem_tr_iff]
      surj := fun v => by
        obtain ⟨x, hx, hxv⟩ := L52.exists_wC v
        exact ⟨emb e x, emb_mem_tr e hx, by rw [wG_emb, hxv]⟩ }
  mmul := by
    rw [← tr_inf]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, mG_emb, mG_emb, mG_emb, L52.zC_mul hx hy]
  minj := by
    rw [← tr_inf]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
    rw [mG_emb, mG_emb] at h
    rw [L52.zC_injOn hx hy h]
  msurj := fun M => by
    rw [← tr_inf]
    obtain ⟨x, hx, hxm⟩ := L52.exists_zC M
    exact ⟨emb e x, emb_mem_tr e hx, by rw [mG_emb, hxm]⟩
  comm := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨hm, hz⟩ := L52.comm_coord hx hy
    have : emb e x * emb e y * (emb e x)⁻¹ * (emb e y)⁻¹ = emb e (x * y * x⁻¹ * y⁻¹) := by
      simp [map_mul, map_inv]
    rw [this, ← tr_inf]
    exact ⟨emb_mem_tr e hm, by rw [mG_emb, hz, uG_emb, wG_emb]⟩

end CFSG.Quasithin.A94.HeJ
