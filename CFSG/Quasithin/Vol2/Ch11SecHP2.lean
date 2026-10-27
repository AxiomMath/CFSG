module

public import CFSG.Quasithin.Vol2.Ch11SecHP

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem sq_Bh {b' : G} (hb' : b' ∈ conjSubgroup (bOf T I H) h) : b' ^ 2 = 1 := by
  have h1 := (SecA.isElemAbelian_fsuV d.c.s.hyp).2 _ (mem_conjSubgroup_iff.mp hb').1
  have : h * b' ^ 2 * h⁻¹ = 1 := by rw [← h1, pow_two, pow_two]; group
  have h2 : b' ^ 2 = h⁻¹ * (h * b' ^ 2 * h⁻¹) * h := by group
  rw [h2, this]
  group

theorem isElemAbelian_P (i : Inp32) : IsElemAbelian 2 (pOf T I H h) := by
  have hVab := SecA.isElemAbelian_fsuV d.c.s.hyp
  have hBV : bOf T I H ≤ fsuV T I := inf_le_left
  have hBhV : conjSubgroup (bOf T I H) h ≤ conjSubgroup (fsuV T I) h :=
    E3.conjSubgroup_mono_left _ hBV
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨b₁, hb₁, b₁', hb₁', h1⟩ := (d.mem_P_iff i).mp a.2
    obtain ⟨b₂, hb₂, b₂', hb₂', h2⟩ := (d.mem_P_iff i).mp b.2
    simp only [Subgroup.coe_mul, h1, h2]
    have c1 : b₁' * b₂ = b₂ * b₁' := (d.comm_B_Bh i hb₂ hb₁').symm
    have c2 : b₁ * b₂ = b₂ * b₁ := comm_of_isElemAbelian hVab (hBV hb₁) (hBV hb₂)
    have c3 : b₁' * b₂' = b₂' * b₁' := comm_of_conj hVab (hBhV hb₁') (hBhV hb₂')
    have c4 : b₁ * b₂' = b₂' * b₁ := d.comm_B_Bh i hb₁ hb₂'
    calc b₁ * b₁' * (b₂ * b₂') = b₁ * (b₁' * b₂) * b₂' := by group
      _ = b₁ * (b₂ * b₁') * b₂' := by rw [c1]
      _ = (b₁ * b₂) * (b₁' * b₂') := by group
      _ = (b₂ * b₁) * (b₂' * b₁') := by rw [c2, c3]
      _ = b₂ * (b₁ * b₂') * b₁' := by group
      _ = b₂ * (b₂' * b₁) * b₁' := by rw [c4]
      _ = b₂ * b₂' * (b₁ * b₁') := by group
  · obtain ⟨b, hb, b', hb', rfl⟩ := (d.mem_P_iff i).mp hx
    have c : b' * b = b * b' := (d.comm_B_Bh i hb hb').symm
    have hb2 : b ^ 2 = 1 := hVab.2 b (hBV hb)
    have hb'2 := d.sq_Bh hb'
    calc (b * b') ^ 2 = b * (b' * b) * b' := by rw [pow_two]; group
      _ = b * (b * b') * b' := by rw [c]
      _ = b ^ 2 * b' ^ 2 := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hb2, hb'2, one_mul]

theorem fsuV_le_normalizer_P (i : Inp32) :
    fsuV T I ≤ Subgroup.normalizer (pOf T I H h : Set G) := by
  have hVab := SecA.isElemAbelian_fsuV d.c.s.hyp
  intro v hv
  apply mem_normalizer_of_conj_le
  have hsub : bOf T I H ⊔ conjSubgroup (bOf T I H) h ≤
      (pOf T I H h).comap (MulAut.conj v).toMonoidHom := by
    refine sup_le (fun b hb => ?_) (fun b' hb' => ?_)
    · show v * b * v⁻¹ ∈ pOf T I H h
      rw [comm_of_isElemAbelian hVab hv ((inf_le_left : bOf T I H ≤ fsuV T I) hb),
        mul_inv_cancel_right]
      exact Subgroup.mem_sup_left hb
    · show v * b' * v⁻¹ ∈ pOf T I H h
      have hb'O := (d.Bh_eq i ▸ hb' : b' ∈ conjSubgroup (fsuV T I) h ⊓ pCoreOf 2 H).2
      have hc : v * b' * v⁻¹ * b'⁻¹ ∈ bOf T I H := by
        rw [d.bOf_eq i]
        refine ⟨?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (d.pCoreOf_le_normalizer_V hb'O) v⁻¹).mp
            ((fsuV T I).inv_mem hv)
          have h2 : v * b' * v⁻¹ * b'⁻¹ = v * (b' * v⁻¹ * b'⁻¹) := by group
          rw [h2]
          exact (fsuV T I).mul_mem hv this
        · refine (pCoreOf 2 H).mul_mem ?_ ((pCoreOf 2 H).inv_mem hb'O)
          exact (Subgroup.mem_normalizer_iff.mp
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (d.c.V_le_H hv)) b').mp hb'O
      have : v * b' * v⁻¹ = (v * b' * v⁻¹ * b'⁻¹) * b' := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hb')
  exact fun s hs => hsub hs

theorem Vh_le_normalizer_P (i : Inp32) :
    conjSubgroup (fsuV T I) h ≤ Subgroup.normalizer (pOf T I H h : Set G) := by
  have hVab := SecA.isElemAbelian_fsuV d.c.s.hyp
  intro v hv
  apply mem_normalizer_of_conj_le
  have hsub : bOf T I H ⊔ conjSubgroup (bOf T I H) h ≤
      (pOf T I H h).comap (MulAut.conj v).toMonoidHom := by
    refine sup_le (fun b hb => ?_) (fun b' hb' => ?_)
    · show v * b * v⁻¹ ∈ pOf T I H h
      have hbO := (d.bOf_eq i ▸ hb : b ∈ fsuV T I ⊓ pCoreOf 2 H).2
      have hc : v * b * v⁻¹ * b⁻¹ ∈ conjSubgroup (bOf T I H) h := by
        rw [d.Bh_eq i]
        refine ⟨?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (d.pCoreOf_le_normalizer_Vh hbO) v⁻¹).mp
            ((conjSubgroup (fsuV T I) h).inv_mem hv)
          have h2 : v * b * v⁻¹ * b⁻¹ = v * (b * v⁻¹ * b⁻¹) := by group
          rw [h2]
          exact (conjSubgroup (fsuV T I) h).mul_mem hv this
        · refine (pCoreOf 2 H).mul_mem ?_ ((pCoreOf 2 H).inv_mem hbO)
          exact (Subgroup.mem_normalizer_iff.mp
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (d.Vh_le_H hv)) b).mp hbO
      have : v * b * v⁻¹ = (v * b * v⁻¹ * b⁻¹) * b := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hb)
    · show v * b' * v⁻¹ ∈ pOf T I H h
      have hb'V : b' ∈ conjSubgroup (fsuV T I) h := E3.conjSubgroup_mono_left _ inf_le_left hb'
      rw [comm_of_conj hVab hv hb'V, mul_inv_cancel_right]
      exact Subgroup.mem_sup_right hb'
  exact fun s hs => hsub hs

theorem le_normalizer_P (i : Inp32) : fsuV T I ⊔ conjSubgroup (fsuV T I) h ≤
    Subgroup.normalizer (pOf T I H h : Set G) :=
  sup_le (d.fsuV_le_normalizer_P i) (d.Vh_le_normalizer_P i)

theorem K_le_normalizer_P (i : Inp32) :
    oTwoUpper H ≤ Subgroup.normalizer (pOf T I H h : Set G) :=
  (d.K_le_I i).trans (d.le_normalizer_P i)

theorem B_le_centralizer_V : bOf T I H ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact comm_of_isElemAbelian (SecA.isElemAbelian_fsuV d.c.s.hyp) hv
    ((inf_le_left : bOf T I H ≤ fsuV T I) hb)

theorem P_inf_centralizer_V (i : Inp32) :
    pOf T I H h ⊓ Subgroup.centralizer (fsuV T I : Set G) = bOf T I H := by
  have hVab := SecA.isElemAbelian_fsuV d.c.s.hyp
  refine le_antisymm ?_ (le_inf le_sup_left d.B_le_centralizer_V)
  rintro x ⟨hx, hxC⟩
  obtain ⟨b, hb, b', hb', rfl⟩ := (d.mem_P_iff i).mp hx
  have hbC := d.B_le_centralizer_V hb
  have hb'C : b' ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    have := (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem hbC) hxC
    simpa using this
  have hb'V : b' ∈ conjSubgroup (fsuV T I) h := E3.conjSubgroup_mono_left _ inf_le_left hb'
  have hb'Vh : b' ∈ Subgroup.centralizer (conjSubgroup (fsuV T I) h : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact comm_of_conj hVab hv hb'V
  have hK : b' ∈ conjSubgroup (fsuV T I) h ⊓ Subgroup.centralizer (oTwoUpper H : Set G) :=
    ⟨hb'V, d.mem_centralizer_K i hb'C hb'Vh⟩
  rw [d.Vh_inf_centralizer_K, Subgroup.mem_bot] at hK
  rw [hK, mul_one]
  exact hb

theorem P_inf_centralizer_K (i : Inp32) :
    pOf T I H h ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ := by
  have hPab := d.isElemAbelian_P i
  rw [eq_bot_iff, ← d.fsuV_inf_centralizer_K]
  rintro x ⟨hxP, hxK⟩
  have hxV : x ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨k, hk, b, hb, rfl⟩ := d.exists_decomp i hv
    have h1 : k * x = x * k := Subgroup.mem_centralizer_iff.mp hxK k hk.2
    have hbP : b ∈ pOf T I H h := Subgroup.mem_sup_left (by rw [d.bOf_eq i]; exact hb)
    have h2 : b * x = x * b := comm_of_isElemAbelian hPab hbP hxP
    calc k * b * x = k * (b * x) := by group
      _ = k * (x * b) := by rw [h2]
      _ = (k * x) * b := by group
      _ = x * k * b := by rw [h1]
      _ = x * (k * b) := by group
  have hxB := (d.P_inf_centralizer_V i).le ⟨hxP, hxV⟩
  exact ⟨(inf_le_left : bOf T I H ≤ fsuV T I) hxB, hxK⟩

theorem autOn_V_le_autOn_K (i : Inp32) :
    autOn (fsuV T I) (pOf T I H h) ≤ autOn (oTwoUpper H) (pOf T I H h) := by
  have hPab := d.isElemAbelian_P i
  rintro _ ⟨⟨v, hvN⟩, hv, rfl⟩
  have hv' := Subgroup.mem_subgroupOf.mp hv
  obtain ⟨k, hk, b, hb, hvkb⟩ := d.exists_decomp i hv'
  have hbP : b ∈ pOf T I H h := Subgroup.mem_sup_left (by rw [d.bOf_eq i]; exact hb)
  have hkN := d.K_le_normalizer_P i hk.2
  refine ⟨⟨k, hkN⟩, Subgroup.mem_subgroupOf.mpr hk.2, ?_⟩
  ext w
  rw [conjAct_apply_coe, conjAct_apply_coe]
  change k * (w : G) * k⁻¹ = v * w * v⁻¹
  have hvkb' : v = k * b := hvkb
  rw [hvkb', mul_inv_rev]
  have : b * (w : G) * b⁻¹ = w := by
    rw [comm_of_isElemAbelian hPab hbP w.2, mul_inv_cancel_right]
  calc k * (w : G) * k⁻¹ = k * (b * (w : G) * b⁻¹) * k⁻¹ := by rw [this]
    _ = k * b * w * (b⁻¹ * k⁻¹) := by group

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
