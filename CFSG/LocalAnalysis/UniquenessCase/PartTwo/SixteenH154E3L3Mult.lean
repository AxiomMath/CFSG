module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3MultA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3MultB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private abbrev s16h_e3_K {W : Type} [CommGroup W] (X L L' : Subgroup (MulAut W)) :
    Subgroup (MulAut W) :=
  X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))

private lemma s16h_e3_map_commSub_of_mem_normalizer {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ∀ u ∈ commSub ⊤ L, g u ∈ commSub ⊤ L := by
  intro u hu
  have h : commSub ⊤ L ≤ Subgroup.comap g.toMonoidHom (commSub ⊤ L) := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, -, rfl⟩
    change g (x w * w⁻¹) ∈ commSub ⊤ L
    have hconj : g * x * g⁻¹ ∈ L := by
      have hmem : MulAut.conj g x ∈ MulAut.conj g '' (L : Set (MulAut W)) := ⟨x, hx, rfl⟩
      rw [Subgroup.mem_normalizer_iff_conj_image_eq.mp hg, MulAut.conj_apply] at hmem
      exact hmem
    have hgx : g (x w) = (g * x * g⁻¹) (g w) := by
      simp [MulAut.mul_apply, MulAut.conj_apply]
    rw [map_mul, map_inv, hgx]
    exact Subgroup.subset_closure ⟨g * x * g⁻¹, hconj, g w, trivial, rfl⟩
  simpa [Subgroup.mem_comap] using h hu

private noncomputable def s16h_e3_actU {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (k : ↥(s16h_e3_K X L L')) : ↥U →* ↥U where
  toFun u := ⟨(k : MulAut W) (u : W), by
    have hmem : (k : MulAut W) (u : W) ∈ commSub ⊤ L :=
      s16h_e3_map_commSub_of_mem_normalizer
        ((Subgroup.centralizer_le_normalizer (L : Set (MulAut W)))
          ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)) k.2.2))
        (u : W) (by rw [← F.u_eq]; exact u.2)
    rwa [← F.u_eq] at hmem⟩
  map_one' := Subtype.ext (map_one (k : MulAut W))
  map_mul' a b := Subtype.ext (map_mul (k : MulAut W) (a : W) (b : W))

private noncomputable def s16h_e3_Lact {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (l : ↥L) : ↥U →* ↥U where
  toFun u := ⟨(l : MulAut W) (u : W), by
    have hmem : (l : MulAut W) (u : W) ∈ commSub ⊤ L :=
      s16h_e3_map_commSub_of_mem_normalizer (L.le_normalizer l.2) (u : W)
        (by rw [← F.u_eq]; exact u.2)
    rwa [← F.u_eq] at hmem⟩
  map_one' := Subtype.ext (map_one (l : MulAut W))
  map_mul' a b := Subtype.ext (map_mul (l : MulAut W) (a : W) (b : W))

private lemma s16h_e3_psi_Lact {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (C : s16h_L3Coord L U) (l : ↥L) (u : ↥U) :
    C.ψ (s16h_e3_Lact F l u) = Multiplicative.ofAdd
      ((C.ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (C.ψ u)) :=
  C.equivariant l (u : W) u.2 (s16h_e3_Lact F l u).2

private lemma s16h_e3_actU_comm {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (k : ↥(s16h_e3_K X L L')) (l : ↥L) (u : ↥U) :
    s16h_e3_actU F k (s16h_e3_Lact F l u) = s16h_e3_Lact F l (s16h_e3_actU F k u) := by
  apply Subtype.ext
  show (k : MulAut W) ((l : MulAut W) (u : W)) = (l : MulAut W) ((k : MulAut W) (u : W))
  have hcomm : (k : MulAut W) * (l : MulAut W) = (l : MulAut W) * (k : MulAut W) :=
    (Subgroup.mem_centralizer_iff.mp k.2.2 (l : MulAut W) (Subgroup.mem_sup_left l.2)).symm
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, hcomm]

private noncomputable def s16h_e3_Tfun {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (C : s16h_L3Coord L U)
    (k : ↥(s16h_e3_K X L L')) (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Multiplicative.toAdd (C.ψ (s16h_e3_actU F k (C.ψ.symm (Multiplicative.ofAdd M))))

private noncomputable def s16h_e3_transport {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (C : s16h_L3Coord L U)
    (k : ↥(s16h_e3_K X L L')) :
    Matrix (Fin 3) (Fin 3) (ZMod 2) →+ Matrix (Fin 3) (Fin 3) (ZMod 2) where
  toFun := s16h_e3_Tfun F C k
  map_zero' := by
    simp [s16h_e3_Tfun]
  map_add' M N := by
    simp [s16h_e3_Tfun]

private lemma s16h_e3_Tfun_mul_left {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (C : s16h_L3Coord L U)
    (k : ↥(s16h_e3_K X L L')) (l : ↥L) (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    s16h_e3_Tfun F C k ((C.ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M) =
      (C.ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * s16h_e3_Tfun F C k M := by
  let u : ↥U := C.ψ.symm (Multiplicative.ofAdd M)
  have hsymm : C.ψ.symm (Multiplicative.ofAdd ((C.ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M)) =
      s16h_e3_Lact F l u := by
    rw [MulEquiv.symm_apply_eq, s16h_e3_psi_Lact]
    simp only [u, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  unfold s16h_e3_Tfun
  rw [hsymm, s16h_e3_actU_comm, s16h_e3_psi_Lact]
  rfl

private lemma s16h_e3_Tfun_eq_mul {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (C : s16h_L3Coord L U)
    (k : ↥(s16h_e3_K X L L')) (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    s16h_e3_Tfun F C k M = M * s16h_e3_Tfun F C k 1 := by
  refine s16h_e3_mul_eq_right_of_commute_left (s16h_e3_transport F C k) ?_ M
  intro A X
  obtain ⟨l, hl⟩ : ∃ l : ↥L, (C.ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    ⟨C.ρ.symm A, by rw [MulEquiv.apply_symm_apply]⟩
  rw [← hl]
  exact s16h_e3_Tfun_mul_left F C k l X

private noncomputable def s16h_e3_A {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (C : s16h_L3Coord L U)
    (k : ↥(s16h_e3_K X L L')) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  s16h_e3_Tfun F C k 1

private lemma s16h_e3_Tfun_mul {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (C : s16h_L3Coord L U)
    (k₁ k₂ : ↥(s16h_e3_K X L L')) (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    s16h_e3_Tfun F C (k₁ * k₂) M = s16h_e3_Tfun F C k₁ (s16h_e3_Tfun F C k₂ M) := by
  rw [s16h_e3_Tfun, s16h_e3_Tfun, s16h_e3_Tfun]
  rw [show s16h_e3_actU F (k₁ * k₂) (C.ψ.symm (Multiplicative.ofAdd M)) =
      s16h_e3_actU F k₁ (s16h_e3_actU F k₂ (C.ψ.symm (Multiplicative.ofAdd M))) from
    Subtype.ext rfl]
  rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]

private lemma s16h_e3_A_mul {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (C : s16h_L3Coord L U)
    (k₁ k₂ : ↥(s16h_e3_K X L L')) :
    s16h_e3_A F C (k₁ * k₂) = s16h_e3_A F C k₂ * s16h_e3_A F C k₁ := by
  rw [s16h_e3_A, s16h_e3_Tfun_mul, s16h_e3_Tfun_eq_mul]
  rfl

private lemma s16h_e3_actU_one_apply {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (x : ↥U) :
    s16h_e3_actU F (1 : ↥(s16h_e3_K X L L')) x = x := by
  apply Subtype.ext
  show ((1 : ↥(s16h_e3_K X L L')) : MulAut W) (x : W) = (x : W)
  rw [OneMemClass.coe_one]
  rfl

private lemma s16h_e3_A_one {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (C : s16h_L3Coord L U) :
    s16h_e3_A F C 1 = 1 := by
  rw [s16h_e3_A, s16h_e3_Tfun, s16h_e3_actU_one_apply]
  simp

private noncomputable def s16h_e3_matHom {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (C : s16h_L3Coord L U) :
    ↥(s16h_e3_K X L L') →* Matrix (Fin 3) (Fin 3) (ZMod 2) where
  toFun k := (s16h_e3_A F C k).transpose
  map_one' := by rw [s16h_e3_A_one, Matrix.transpose_one]
  map_mul' k₁ k₂ := by rw [s16h_e3_A_mul, Matrix.transpose_mul]

private noncomputable def s16h_e3_pi {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (C : s16h_L3Coord L U) :
    ↥(s16h_e3_K X L L') →* GL (Fin 3) (ZMod 2) :=
  (s16h_e3_matHom F C).toHomUnits

private lemma s16h_e3_pi_spec {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (C : s16h_L3Coord L U)
    (k : ↥(s16h_e3_K X L L')) (u : W) (hu : u ∈ U) (hku : (k : MulAut W) u ∈ U) :
    C.ψ ⟨(k : MulAut W) u, hku⟩ = Multiplicative.ofAdd
      (Multiplicative.toAdd (C.ψ ⟨u, hu⟩) *
        ((s16h_e3_pi F C k : GL (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose) := by
  have hsub : (⟨(k : MulAut W) u, hku⟩ : ↥U) =
      s16h_e3_actU F k ⟨u, hu⟩ := Subtype.ext rfl
  rw [hsub]
  have hmat : ((s16h_e3_pi F C k : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose = s16h_e3_A F C k := by
    rw [show ((s16h_e3_pi F C k : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) = (s16h_e3_A F C k).transpose from rfl,
      Matrix.transpose_transpose]
  rw [hmat]
  have hT : s16h_e3_Tfun F C k (Multiplicative.toAdd (C.ψ ⟨u, hu⟩)) =
      Multiplicative.toAdd (C.ψ (s16h_e3_actU F k ⟨u, hu⟩)) := by
    simp only [s16h_e3_Tfun, MulEquiv.symm_apply_apply, ofAdd_toAdd]
  rw [show C.ψ (s16h_e3_actU F k ⟨u, hu⟩) =
      Multiplicative.ofAdd (Multiplicative.toAdd (C.ψ (s16h_e3_actU F k ⟨u, hu⟩))) from
    (ofAdd_toAdd _).symm]
  rw [← hT, s16h_e3_Tfun_eq_mul]
  rfl

public theorem s16h_e3_l3_mult_seven {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    (hL : IsL3 ↥L 1) (C : s16h_L3Coord L U)
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ X ⊓ normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom)
    (π : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))) →*
        GL (Fin 3) (ZMod 2))
    (hπ : ∀ (k : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))))
        (u : W) (hu : u ∈ U) (hku : (k : MulAut W) u ∈ U),
        C.ψ ⟨(k : MulAut W) u, hku⟩ = Multiplicative.ofAdd
          (Multiplicative.toAdd (C.ψ ⟨u, hu⟩) *
            (π k : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose)) :
    7 ∣ Nat.card ↥π.range := by
  obtain ⟨k, hk⟩ := s16h_e3_l3_mult_seven_cycle F hL C htrans π hπ
  rw [← hk]
  have hmem : π k ∈ π.range := MonoidHom.mem_range.mpr ⟨k, rfl⟩
  have h1 : orderOf (⟨π k, hmem⟩ : π.range) ∣ Nat.card π.range := orderOf_dvd_natCard _
  rwa [Subgroup.orderOf_mk] at h1

theorem s16h_e3_l3_mult {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    (hL : IsL3 ↥L 1) (C : s16h_L3Coord L U)
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ X ⊓ normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom) :
    ∃ π : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))) →*
        GL (Fin 3) (ZMod 2),
      (∀ (k : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))))
          (u : W) (hu : u ∈ U) (hku : (k : MulAut W) u ∈ U),
        C.ψ ⟨(k : MulAut W) u, hku⟩ = Multiplicative.ofAdd
          (Multiplicative.toAdd (C.ψ ⟨u, hu⟩) *
            (π k : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose)) ∧
      7 ∣ Nat.card ↥π.range := by
  refine ⟨s16h_e3_pi F C, ?_, ?_⟩
  · intro k u hu hku
    exact s16h_e3_pi_spec F C k u hu hku
  · exact s16h_e3_l3_mult_seven F hL C htrans (s16h_e3_pi F C)
      (fun k u hu hku => s16h_e3_pi_spec F C k u hu hku)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
