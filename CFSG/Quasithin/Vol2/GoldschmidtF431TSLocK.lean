module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TSLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442QMain

public section

namespace CFSG.Quasithin.H13.F431.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.F45
  CFSG.LieType.BorelTits

universe u

section Loc

variable {D : Type} [Group D] [Finite D] (A : LieAmalgamExt D)
  (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)

theorem cent_le_Mb1 (hcen : Subgroup.center D = ⊥) {w : D}
    (hC : Subgroup.centralizer ({w} : Set D) ≤ A.P1)
    (haut : ∀ φ ∈ A.N1 ⊓ A.N2, ∃ b ∈ A.P1 ⊓ A.P2, φ w = b * w * b⁻¹) :
    Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) ≤ A.Mb1 := fun k hk =>
  mem_Mb1_of_stab A
    (stab_of_fix A (Or.inl rfl) hC haut k ((mem_centralizer_iK_iff A hgen hcen w k).mp hk))

theorem cent_le_Mb2 (hcen : Subgroup.center D = ⊥) {w : D}
    (hC : Subgroup.centralizer ({w} : Set D) ≤ A.P2)
    (haut : ∀ φ ∈ A.N1 ⊓ A.N2, ∃ b ∈ A.P1 ⊓ A.P2, φ w = b * w * b⁻¹) :
    Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) ≤ A.Mb2 := fun k hk =>
  mem_Mb2_of_stab A
    (stab_of_fix A (Or.inr rfl) hC haut k ((mem_centralizer_iK_iff A hgen hcen w k).mp hk))

theorem cent_le_P1_of_Mb1 {w : D}
    (h : Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) ≤ A.Mb1) :
    Subgroup.centralizer ({w} : Set D) ≤ A.P1 := by
  intro d hd
  have hd' : iK A hgen d ∈ Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg _ (Subgroup.mem_centralizer_singleton_iff.mp hd)
  exact (iK_mem_Mb1_iff A hgen d).mp (h hd')

theorem cent_le_P2_of_Mb2 {w : D}
    (h : Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) ≤ A.Mb2) :
    Subgroup.centralizer ({w} : Set D) ≤ A.P2 := by
  intro d hd
  have hd' : iK A hgen d ∈ Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg _ (Subgroup.mem_centralizer_singleton_iff.mp hd)
  exact (iK_mem_Mb2_iff A hgen d).mp (h hd')

end Loc

section LocDatum

variable {D : Type} [Group D] [Finite D] (A : LieAmalgamExt D)

structure LocD (z0 t0 : D) (V L : Subgroup D) : Prop where
  comm : z0 * t0 = t0 * z0
  sylow_t : IsSylowTwoOf (A.TD ⊓ Subgroup.centralizer ({t0} : Set D))
    (Subgroup.centralizer ({t0} : Set D))
  V_le : V ≤ Subgroup.centralizer ({t0} : Set D)
  V_ab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  V_two : ∀ a ∈ V, a ^ 2 = 1
  V_ne : V ≠ ⊥
  V_aut : ∀ φ ∈ A.Mbar, φ t0 = t0 → ∀ v ∈ V, φ v ∈ V
  V_z : ∀ v ∈ V, v ≠ 1 → ∃ x ∈ Subgroup.centralizer ({t0} : Set D), v = x * z0 * x⁻¹
  L_le : L ≤ Subgroup.centralizer ({t0} : Set D)
  L_ns : ¬ Group.IsSolvable ↥L
  L_V : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (V : Set D))

variable (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)

omit [Finite D] in
theorem iK_mem_centralizer_iff (hcen : Subgroup.center D = ⊥) (w d : D) :
    iK A hgen d ∈ Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) ↔
      d ∈ Subgroup.centralizer ({w} : Set D) := by
  rw [mem_centralizer_iK_iff A hgen hcen, iK_coe, MulAut.conj_apply,
    Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

omit [Finite D] in
theorem centralizer_inf_range (hcen : Subgroup.center D = ⊥) (w : D) :
    Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) ⊓ (iK A hgen).range =
      (Subgroup.centralizer ({w} : Set D)).map (iK A hgen) := by
  ext x
  constructor
  · rintro ⟨hx, d, rfl⟩
    exact ⟨d, (iK_mem_centralizer_iff A hgen hcen w d).mp hx, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨(iK_mem_centralizer_iff A hgen hcen w d).mpr hd, d, rfl⟩

omit [Finite D] in
theorem map_inf_centralizer (hcen : Subgroup.center D = ⊥) (w : D) :
    (A.TD.map (iK A hgen)) ⊓ Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) =
      (A.TD ⊓ Subgroup.centralizer ({w} : Set D)).map (iK A hgen) := by
  ext x
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hx⟩
    exact ⟨u, ⟨hu, (iK_mem_centralizer_iff A hgen hcen w u).mp hx⟩, rfl⟩
  · rintro ⟨u, ⟨hu, hc⟩, rfl⟩
    exact ⟨⟨u, hu, rfl⟩, (iK_mem_centralizer_iff A hgen hcen w u).mpr hc⟩

omit [Finite D] in
theorem sylow_cent_K (hcen : Subgroup.center D = ⊥) (hodd : ¬ 2 ∣ (iK A hgen).range.index)
    {t0 : D} (h : IsSylowTwoOf (A.TD ⊓ Subgroup.centralizer ({t0} : Set D))
      (Subgroup.centralizer ({t0} : Set D))) :
    IsSylowTwoOf ((A.TD.map (iK A hgen)) ⊓ Subgroup.centralizer ({iK A hgen t0} : Set ↥A.K))
      (Subgroup.centralizer ({iK A hgen t0} : Set ↥A.K)) := by
  have := range_normal A hgen
  rw [map_inf_centralizer A hgen hcen]
  refine isSylowTwoOf_of_odd_inf (N := (iK A hgen).range) hodd ?_
  rw [centralizer_inf_range A hgen hcen]
  exact isSylowTwoOf_map_inj _ (iK_injective A hgen hcen) h

omit [Finite D] in
theorem conj_iK (k : ↥A.K) (d : D) :
    k * iK A hgen d * k⁻¹ = iK A hgen ((k : MulAut D) d) := by
  apply Subtype.ext
  have := aut_conj_conj (k : MulAut D) d
  simpa [iK_coe] using this

omit [Finite D] in
theorem not_solvable_map (hinj : Function.Injective (iK A hgen)) {X : Subgroup D}
    (h : ¬ Group.IsSolvable ↥X) : ¬ Group.IsSolvable ↥(X.map (iK A hgen)) := fun _hs =>
  h (Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective X (iK A hgen) hinj).toMonoidHom)
    (Subgroup.equivMapOfInjective X (iK A hgen) hinj).injective)

omit [Finite D] in
theorem solvable_map (hinj : Function.Injective (iK A hgen)) {X : Subgroup D}
    (h : Group.IsSolvable ↥X) : Group.IsSolvable ↥(X.map (iK A hgen)) :=
  Group.isSolvable_of_surjective
    (f := (Subgroup.equivMapOfInjective X (iK A hgen) hinj).toMonoidHom)
    (Subgroup.equivMapOfInjective X (iK A hgen) hinj).surjective

omit [Finite D] in
theorem map_inf_centralizer_set (hinj : Function.Injective (iK A hgen)) (L V : Subgroup D) :
    L.map (iK A hgen) ⊓ Subgroup.centralizer ((V.map (iK A hgen) : Subgroup ↥A.K) : Set ↥A.K) =
      (L ⊓ Subgroup.centralizer (V : Set D)).map (iK A hgen) := by
  ext x
  constructor
  · rintro ⟨⟨l, hl, rfl⟩, hx⟩
    refine ⟨l, ⟨hl, ?_⟩, rfl⟩
    show l ∈ Subgroup.centralizer (V : Set D)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := Subgroup.mem_centralizer_iff.mp hx (iK A hgen v) ⟨v, hv, rfl⟩
    exact hinj (by simpa [map_mul] using this)
  · rintro ⟨l, ⟨hl, hc⟩, rfl⟩
    refine ⟨⟨l, hl, rfl⟩, ?_⟩
    show iK A hgen l ∈ Subgroup.centralizer ((V.map (iK A hgen) : Subgroup ↥A.K) : Set ↥A.K)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc v hv
    simp only [← map_mul]
    exact congrArg _ this

section Main

variable {D : Type} [Group D] [Finite D] {G : Type} [Group G] [Finite G] {M1 M2 : Subgroup G}
  (E : LieExt D M1 M2)

theorem hnfI_of_hnf {Mb : Type*} [Group Mb] {M : Type*} [Group M] {z t : Mb} {φ : Mb → M}
    (hnf : ¬ IsConj (φ z) (φ t)) [DecidableEq Mb] :
    ∀ i ∈ ({z, t} : Finset Mb), ∀ j ∈ ({z, t} : Finset Mb), i ≠ j → ¬ IsConj (φ i) (φ j) := by
  intro i hi j hj hij
  rw [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact absurd rfl hij
  · exact hnf
  · exact fun h => hnf h.symm
  · exact absurd rfl hij

end Main

section LocK

structure LocK {Mb : Type*} [Group Mb] (T : Subgroup Mb) (z t : Mb) (Vb L : Subgroup Mb) :
    Prop where
  comm : z * t = t * z
  sylow : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t} : Set Mb))
    (Subgroup.centralizer ({t} : Set Mb))
  V_le : Vb ≤ Subgroup.centralizer ({t} : Set Mb)
  V_n : ∀ x ∈ Subgroup.centralizer ({t} : Set Mb), ∀ v ∈ Vb, x * v * x⁻¹ ∈ Vb
  V_ab : ∀ a ∈ Vb, ∀ b ∈ Vb, a * b = b * a
  V_two : ∀ a ∈ Vb, a ^ 2 = 1
  V_ne : Vb ≠ ⊥
  V_z : ∀ v ∈ Vb, v ≠ 1 → ∃ x ∈ Subgroup.centralizer ({t} : Set Mb), v = x * z * x⁻¹
  L_le : L ≤ Subgroup.centralizer ({t} : Set Mb)
  L_ns : ¬ Group.IsSolvable ↥L
  L_V : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (Vb : Set Mb))

variable {D : Type} [Group D] [Finite D] (A : LieAmalgamExt D)
  (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)

omit [Finite D] in
theorem locK_of_dlevel (hcen : Subgroup.center D = ⊥) (hodd : ¬ 2 ∣ (iK A hgen).range.index)
    {z0 t0 : D} {V L : Subgroup D} (HL : LocD A z0 t0 V L) :
    LocK (A.TD.map (iK A hgen)) (iK A hgen z0) (iK A hgen t0) (V.map (iK A hgen))
      (L.map (iK A hgen)) := by
  have hinj := iK_injective A hgen hcen
  refine ⟨?_, sylow_cent_K A hgen hcen hodd HL.sylow_t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, HL.comm]
  · rintro _ ⟨v, hv, rfl⟩
    exact (iK_mem_centralizer_iff A hgen hcen t0 v).mpr (HL.V_le hv)
  · rintro x hx _ ⟨v, hv, rfl⟩
    rw [conj_iK A hgen]
    exact ⟨_, HL.V_aut _ (K_le_Mbar A x.2) ((mem_centralizer_iK_iff A hgen hcen t0 x).mp hx) v hv,
      rfl⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb', rfl⟩
    rw [← map_mul, ← map_mul, HL.V_ab a ha b hb']
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, HL.V_two a ha, map_one]
  · intro h
    apply HL.V_ne
    rw [eq_bot_iff]
    intro v hv
    have : iK A hgen v ∈ (V.map (iK A hgen)) := ⟨v, hv, rfl⟩
    rw [h] at this
    exact hinj ((Subgroup.mem_bot.mp this).trans (map_one _).symm)
  · rintro _ ⟨v, hv, rfl⟩ hv1
    obtain ⟨x, hx, hxv⟩ := HL.V_z v hv (fun h => hv1 (by rw [h, map_one]))
    refine ⟨iK A hgen x, (iK_mem_centralizer_iff A hgen hcen t0 x).mpr hx, ?_⟩
    rw [hxv, map_mul, map_mul, map_inv]
  · rintro _ ⟨l, hl, rfl⟩
    exact (iK_mem_centralizer_iff A hgen hcen t0 l).mpr (HL.L_le hl)
  · exact not_solvable_map A hgen hinj HL.L_ns
  · rw [map_inf_centralizer_set A hgen hinj]
    exact solvable_map A hgen hinj HL.L_V

end LocK

section Loc442

variable {Mb : Type u} [Group Mb] [Finite Mb] [DecidableEq Mb] {G : Type} [Group G] [Finite G]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z t : Mb} {b1 : ↥M1 →* G} {b2 : ↥M2 →* G}

open CFSG.Quasithin.Loc442Q in
theorem cent_t_le_oriented (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hI : I = {z, t}) {V L : Subgroup Mb} (K : LocK T z t V L)
    (cz : Subgroup.centralizer ({z} : Set Mb) ≤ M1) (ct : Subgroup.centralizer ({t} : Set Mb) ≤ M2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set G) ≤ b1.range)
    (hnf : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t)) :
    Subgroup.centralizer ({amalgamMap b1 b2 t} : Set G) ≤ b2.range := by
  classical
  have hI' : ∀ i ∈ I, i = z ∨ i = t := by
    intro i hi
    rw [hI, Finset.mem_insert, Finset.mem_singleton] at hi
    exact hi
  have ht : t ∈ I := by
    rw [hI]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hnfI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
    rw [hI]
    exact hnfI_of_hnf hnf
  exact loc442Q_of_sub_hnfI D C hI' ht K.comm cz ct K.sylow hb hnfI K.V_le K.V_n K.V_ab K.V_two
    K.V_ne K.V_z K.L_le K.L_ns K.L_V

end Loc442

end LocDatum

end CFSG.Quasithin.H13.F431.Lift
