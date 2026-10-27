module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdTwo
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSAssemble

public section

namespace CFSG.Quasithin.H13.F431.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.NF
open scoped commutatorElement

section Orient

structure StdOrient (C : Type) [Group C] (U P P' : Subgroup C) (z t v nr na : C)
    (Zd Qd Xd Yd : Subgroup C) (q n : ℕ) : Prop where
  cz : Subgroup.centralizer ({z} : Set C) ≤ P
  ct : Subgroup.centralizer ({t} : Set C) ≤ P'
  nz : ¬ Subgroup.centralizer ({z} : Set C) ≤ P'
  nt : ¬ Subgroup.centralizer ({t} : Set C) ≤ P
  Zperf : Zd ≤ centerOf (perfectCore P)
  conj_tv : IsConj t v
  U_le_P : U ≤ P
  U_le_P' : U ≤ P'
  Z_le_Q : Zd ≤ Qd
  Q_le_T : Qd ≤ U
  Q_norm : ∀ s ∈ U, ∀ x ∈ Qd, s * x * s⁻¹ ∈ Qd
  Z_central : ∀ x ∈ Zd, ∀ s ∈ U, s * x = x * s
  Z_exp : ∀ x ∈ Zd, x * x = 1
  card_Z : Nat.card Zd = q
  z_mem : z ∈ Zd
  z_ne : z ≠ 1
  Q_comm : ∀ x ∈ Qd, ∀ y ∈ Qd, ⁅x, y⁆ ∈ Zd
  Q_sq : ∀ x ∈ Qd, x * x ∈ Zd
  card_Q : Nat.card Qd = q ^ (2 * n + 1)
  card_T : Nat.card U = q ^ (3 * n)
  T_comm : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ Qd
  elem_abelian : ∀ E : Subgroup C, E ≤ Qd → (∀ x ∈ E, x * x = 1) →
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ q ^ (n + 1)
  aut_Z : ∀ φ : MulAut C, φ ∈ autStab P → ∀ x ∈ Zd, φ x ∈ Zd
  aut_Q : ∀ φ : MulAut C, φ ∈ autStab P → ∀ x ∈ Qd, φ x ∈ Qd
  trans : ∀ x ∈ Zd, ∀ y ∈ Zd, x ≠ 1 → y ≠ 1 → ∃ d ∈ P, d * x * d⁻¹ = y
  X_le : Xd ≤ Qd
  Y_le : Yd ≤ Qd
  Z_le_comm : Zd ≤ ⁅Xd, Yd⁆
  v_mem : v ∈ Qd
  v_not_mem : v ∉ Zd
  v_comm_X : ∀ a ∈ Xd, a * v = v * a
  v_comm_Y : ∀ b ∈ Yd, b * v = v * b
  v_not_cent : ∀ φ : MulAut C, φ ∈ autStab P → ∃ s ∈ U, ⁅s, φ v⁆ ∉ Zd
  nr_mem : nr ∈ P
  na_mem : na ∈ P'
  X_eq : Xd = cj nr Yd
  Y_eq : Yd = cj na Zd


variable {D C : Type} [Group D] [Group C] (A : LieAmalgamExt D) (ε : D ≃* C)

theorem orientD_of_std {U P P' : Subgroup C} {z t v nr na : C} {Zd Qd Xd Yd : Subgroup C}
    {q n : ℕ} (S : StdOrient C U P P' z t v nr na Zd Qd Xd Yd q n) {Q Q' : Subgroup D}
    (hQP : Q.map ε.toMonoidHom = P) (hQP' : Q'.map ε.toMonoidHom = P')
    (hU : A.TD.map ε.toMonoidHom = U) :
    OrientD A Q Q' (A.Mbar ⊓ autStab Q) (A.Mbar ⊓ autStab Q') (ε.symm z) (ε.symm t) (ε.symm v)
      (ε.symm nr) (ε.symm na) (Zd.map ε.symm.toMonoidHom) (Qd.map ε.symm.toMonoidHom)
      (Xd.map ε.symm.toMonoidHom) (Yd.map ε.symm.toMonoidHom) q n := by
  have hinj : Function.Injective ε.symm.toMonoidHom := ε.symm.injective
  have hcard : ∀ X : Subgroup C, Nat.card (X.map ε.symm.toMonoidHom) = Nat.card X := fun X =>
    Subgroup.card_map_of_injective hinj
  have hcongr : ∀ (φ : MulAut D) (x : D), (MulAut.congr ε φ) (ε x) = ε (φ x) := fun φ x => by
    simp [MulAut.congr_apply]
  have hTDmem : ∀ {u : D}, u ∈ A.TD ↔ ε u ∈ U := fun {u} => (mem_iff_of_map_eq ε hU).symm
  have hQmem : ∀ {u : D}, u ∈ Q ↔ ε u ∈ P := fun {u} => (mem_iff_of_map_eq ε hQP).symm
  have hQmem' : ∀ {u : D}, u ∈ Q' ↔ ε u ∈ P' := fun {u} => (mem_iff_of_map_eq ε hQP').symm
  have hmapmem : ∀ {S' : Subgroup C} {x : D}, x ∈ S'.map ε.symm.toMonoidHom ↔ ε x ∈ S' :=
    fun {S'} {x} => mem_map_symm_iff ε
  have hN : ∀ {φ : MulAut D}, φ ∈ A.Mbar ⊓ autStab Q → MulAut.congr ε φ ∈ autStab P := fun {φ} h =>
    congr_mem_autStab ε hQP h.2
  have hinnN : ∀ {d : D}, d ∈ Q → MulAut.conj d ∈ A.Mbar ⊓ autStab Q := fun {d} hd =>
    ⟨A.inn_le ⟨d, rfl⟩, inn_mem_autStab hd⟩
  have hinnN' : ∀ {d : D}, d ∈ Q' → MulAut.conj d ∈ A.Mbar ⊓ autStab Q' := fun {d} hd =>
    ⟨A.inn_le ⟨d, rfl⟩, inn_mem_autStab hd⟩
  have hcomm : ∀ x y : D, ε ⁅x, y⁆ = ⁅ε x, ε y⁆ := fun x y => by
    simp [commutatorElement_def]
  have hperf : perfectCore P = (perfectCore Q).map ε.toMonoidHom := by
    rw [← hQP]
    exact perfectCore_map_of_injective ε.toMonoidHom ε.injective Q
  have hcenter : centerOf (perfectCore P) = (centerOf (perfectCore Q)).map ε.toMonoidHom := by
    rw [hperf]
    exact centerOf_map_of_injective ε.toMonoidHom ε.injective _
  refine
    { cz := ?_, ct := ?_, nz := ?_, nt := ?_, Zperf := ?_, conj_tv := ?_,
      nfd :=
        { TD_le_N := ?_, TD_le_N' := ?_, Z_le_Q := ?_, Q_le_T := ?_, Q_norm := ?_,
          Z_central := ?_, Z_exp := ?_, card_Z := ?_, z_mem := ?_, z_ne := ?_, Q_comm := ?_,
          Q_sq := ?_, card_Q := ?_, card_T := ?_, T_comm := ?_, elem_abelian := ?_,
          aut_Z := ?_, aut_Q := ?_, trans := ?_, X_le := ?_, Y_le := ?_, Z_le_comm := ?_,
          v_mem := ?_, v_not_mem := ?_, v_comm_X := ?_, v_comm_Y := ?_, v_not_cent := ?_,
          nr_mem := ?_, na_mem := ?_, X_eq := ?_, Y_eq := ?_ } }
  · exact (centralizer_le_transport ε hQP z).mpr S.cz
  · exact (centralizer_le_transport ε hQP' t).mpr S.ct
  · intro h
    exact S.nz ((centralizer_le_transport ε hQP' z).mp h)
  · intro h
    exact S.nt ((centralizer_le_transport ε hQP t).mp h)
  · intro x hx
    have h1 := S.Zperf (hmapmem.mp hx)
    rw [hcenter] at h1
    exact (mem_iff_of_map_eq ε rfl).mp h1
  · intro u hu
    exact hinnN (hQmem.mpr (S.U_le_P (hTDmem.mp hu)))
  · intro u hu
    exact hinnN' (hQmem'.mpr (S.U_le_P' (hTDmem.mp hu)))
  · exact Subgroup.map_mono S.Z_le_Q
  · intro x hx
    exact hTDmem.mpr (S.Q_le_T (hmapmem.mp hx))
  · intro s hs x hx
    rw [hmapmem] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    exact S.Q_norm _ (hTDmem.mp hs) _ hx
  · intro x hx s hs
    apply ε.injective
    rw [map_mul, map_mul]
    exact S.Z_central _ (hmapmem.mp hx) _ (hTDmem.mp hs)
  · intro x hx
    apply ε.injective
    rw [map_mul, map_one]
    exact S.Z_exp _ (hmapmem.mp hx)
  · rw [hcard, S.card_Z]
  · exact hmapmem.mpr (by simpa using S.z_mem)
  · intro h
    exact S.z_ne (ε.symm.injective (by rw [h, map_one]))
  · intro x hx y hy
    rw [hmapmem, hcomm]
    exact S.Q_comm _ (hmapmem.mp hx) _ (hmapmem.mp hy)
  · intro x hx
    rw [hmapmem, map_mul]
    exact S.Q_sq _ (hmapmem.mp hx)
  · rw [hcard, S.card_Q]
  · have : Nat.card A.TD = Nat.card U := by
      rw [← hU]
      exact (Subgroup.card_map_of_injective ε.injective).symm
    rw [this, S.card_T]
  · intro x hx y hy
    rw [hmapmem, hcomm]
    exact S.T_comm _ (hTDmem.mp hx) _ (hTDmem.mp hy)
  · intro E hE h2 hab
    have hEQ : E.map ε.toMonoidHom ≤ Qd := by
      rintro _ ⟨x, hx, rfl⟩
      exact hmapmem.mp (hE hx)
    have := S.elem_abelian (E.map ε.toMonoidHom) hEQ
      (by rintro _ ⟨x, hx, rfl⟩; rw [← map_mul, h2 x hx, map_one])
      (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; rw [← map_mul, ← map_mul, hab x hx y hy])
    rwa [Subgroup.card_map_of_injective ε.injective] at this
  · intro φ hφ x hx
    rw [hmapmem] at hx ⊢
    have := S.aut_Z _ (hN hφ) _ hx
    rwa [hcongr] at this
  · intro φ hφ x hx
    rw [hmapmem] at hx ⊢
    have := S.aut_Q _ (hN hφ) _ hx
    rwa [hcongr] at this
  · intro x hx y hy hx1 hy1
    obtain ⟨d, hd, hdxy⟩ := S.trans (ε x) (hmapmem.mp hx) (ε y) (hmapmem.mp hy)
      (fun h => hx1 (ε.injective (by rw [h, map_one])))
      (fun h => hy1 (ε.injective (by rw [h, map_one])))
    refine ⟨ε.symm d, hinnN (hQmem.mpr (by simpa using hd)), ε.injective ?_⟩
    simpa using hdxy
  · exact Subgroup.map_mono S.X_le
  · exact Subgroup.map_mono S.Y_le
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono S.Z_le_comm
  · exact hmapmem.mpr (by simpa using S.v_mem)
  · intro h
    exact S.v_not_mem (by simpa using hmapmem.mp h)
  · intro a ha
    apply ε.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact S.v_comm_X _ (hmapmem.mp ha)
  · intro b hb
    apply ε.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact S.v_comm_Y _ (hmapmem.mp hb)
  · intro φ hφ
    obtain ⟨s, hs, hsv⟩ := S.v_not_cent _ (hN hφ)
    refine ⟨ε.symm s, hTDmem.mpr (by rwa [MulEquiv.apply_symm_apply]), ?_⟩
    intro h
    apply hsv
    have h1 := hmapmem.mp h
    rw [hcomm, MulEquiv.apply_symm_apply] at h1
    have e : (MulAut.congr ε φ) v = ε (φ (ε.symm v)) := by
      have := hcongr φ (ε.symm v)
      rwa [MulEquiv.apply_symm_apply] at this
    rwa [e]
  · exact hinnN (hQmem.mpr (by rw [MulEquiv.apply_symm_apply]; exact S.nr_mem))
  · exact hinnN' (hQmem'.mpr (by rw [MulEquiv.apply_symm_apply]; exact S.na_mem))
  · rw [S.X_eq, ← map_cj_equiv ε.symm]
  · rw [S.Y_eq, ← map_cj_equiv ε.symm]
  · exact (ε.symm.toMonoidHom).map_isConj S.conj_tv

end Orient

section Final

variable {D C : Type} [Group D] [Group C] [Finite D] {G : Type} [Group G] [Finite G]
  {M1 M2 : Subgroup G} (E : LieExt D M1 M2) (ε : D ≃* C)

theorem f431Local_of_std {U P P' : Subgroup C} {z t v nr na : C} {V L Zd Qd Xd Yd : Subgroup C}
    {q n : ℕ} (S1 : StdTwo C U P P' z t) (S2 : StdLoc C U z t V L)
    (S3 : StdOrient C U P P' z t v nr na Zd Qd Xd Yd q n)
    {Q Q' : Subgroup D} (hQ : (Q = E.P1 ∧ Q' = E.P2) ∨ (Q = E.P2 ∧ Q' = E.P1))
    (hQP : Q.map ε.toMonoidHom = P) (hQP' : Q'.map ε.toMonoidHom = P')
    (hU : E.TD.map ε.toMonoidHom = U) (hcen : Subgroup.center D = ⊥)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ E.K)
    (hodd : ¬ 2 ∣ (iK E.toLieAmalgamExt hgen).range.index)
    (hag : ∀ E' : Subgroup ↥E.K, IsAGMember (E.TD.map (iK E.toLieAmalgamExt hgen)) E' →
      Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb1 ∨ Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb2)
    (hyp1 : ∀ w ∈ centerOf (perfectCore M1), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set G) ≤ M1)
    (hyp2 : ∀ w ∈ centerOf (perfectCore M2), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set G) ≤ M2) :
    ∃ (T : Subgroup ↥E.K) (I : Finset ↥E.K) (z : ↥E.K), F431LieK T E.Mb1 E.Mb2 I z ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ¬ IsConj (amalgamMap E.b1 E.b2 i) (amalgamMap E.b1 E.b2 j)) ∧
      (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb1 →
        Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M1) ∧
      (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb2 →
        Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M2) := by
  refine f431Local_of_dlevel E hcen hgen hodd
    (twoClassD_of_std E.toLieAmalgamExt ε S1 hQ hQP hQP' hU)
    (locD_of_std E.toLieAmalgamExt ε S2 hU) hag hyp1 hyp2 ?_
  rcases hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨ε.symm v, ε.symm nr, ε.symm na, Zd.map ε.symm.toMonoidHom,
      Qd.map ε.symm.toMonoidHom, Xd.map ε.symm.toMonoidHom, Yd.map ε.symm.toMonoidHom, q, n,
      orientD_of_std E.toLieAmalgamExt ε S3 hQP hQP' hU⟩
  · exact Or.inr ⟨ε.symm v, ε.symm nr, ε.symm na, Zd.map ε.symm.toMonoidHom,
      Qd.map ε.symm.toMonoidHom, Xd.map ε.symm.toMonoidHom, Yd.map ε.symm.toMonoidHom, q, n,
      orientD_of_std E.toLieAmalgamExt ε S3 hQP hQP' hU⟩

end Final
end CFSG.Quasithin.H13.F431.Lift
