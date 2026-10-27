module

public import CFSG.Quasithin.H13.ZCentLieCore
public import CFSG.Quasithin.EmptyFaithful.R3c5Pgl

public section

namespace CFSG.Quasithin.H13.ZCentLie

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank CFSG.LinearGroups

variable {f : ℕ} {K : Type} [Field K]

section Heisenberg

variable (h : UnitaryFieldData 2 f K)

@[expose] def rootEF (K : Type) [Field K] : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  single (.inl 0) (.inr (.inr 0)) 1

theorem rootEF_mul_self : rootEF K * rootEF K = 0 := by
  rw [rootEF, single_mul_single_of_ne]
  decide

theorem rkOneQ_zero (b : K) : rkOneQ h 0 b = 1 + b • rootEF K := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    obtain rfl := Fin.fin_one_eq_zero i <;> obtain rfl := Fin.fin_one_eq_zero j <;>
    simp [rkOneQ, heisenbergMatrix, hypIndexFin3, rootEF]

theorem eq_zero_of_forall_commute {a b : K} (hab : h.norm a + h.trace b = 0)
    (hc : ∀ (c d : K) (hcd : h.norm c + h.trace d = 0),
      rkOneQElt h c d hcd * rkOneQElt h a b hab = rkOneQElt h a b hab * rkOneQElt h c d hcd) :
    a = 0 := by
  by_contra ha
  obtain ⟨l, hl⟩ := h.exists_bar_ne
  obtain ⟨d, hd⟩ := exists_norm_add_trace_eq_zero h (l * a)
  have h1 := congrArg (fun g : hypSU h 1 1 =>
    ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl 0) (.inr (.inr 0)))
    (hc (l * a) d hd)
  simp only [rkOneQElt_mul, coe_rkOneQElt, rkOneQ_ef] at h1
  have h2 : (l - h.bar l) * (h.bar a * a) = 0 := by
    rw [map_mul] at h1
    linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact hl (sub_eq_zero.1 h3).symm
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact ha ((map_eq_zero h.bar).1 h4)
    · exact ha h4

theorem center_hypUnitriangular {g : hypSU h 1 1} (hg : g ∈ hypUnitriangular h 1 1)
    (hc : ∀ v ∈ hypUnitriangular h 1 1, v * g = g * v) :
    ∃ b : K, ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      1 + b • rootEF K := by
  obtain ⟨a, b, hab, rfl⟩ := exists_eq_rkOneQElt h hg
  have ha := eq_zero_of_forall_commute h hab fun c d hcd => hc _ (rkOneQElt_mem h hcd)
  subst ha
  exact ⟨b, by rw [coe_rkOneQElt, rkOneQ_zero]⟩

theorem commute_of_hypProj {g v : hypSU h 1 1} (hg : g ∈ hypUnitriangular h 1 1)
    (hv : v ∈ hypUnitriangular h 1 1)
    (hcomm : hypProj h 1 1 v * hypProj h 1 1 g = hypProj h 1 1 g * hypProj h 1 1 v) :
    v * g = g * v := by
  obtain ⟨-, -, hUZ, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have h1 : v * g * v⁻¹ * g⁻¹ ∈ hypScalars h 1 1 := by
    rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have h2 : v * g * v⁻¹ * g⁻¹ ∈ hypUnitriangular h 1 1 :=
    mul_mem (mul_mem (mul_mem hv hg) (inv_mem hv)) (inv_mem hg)
  have h3 : v * g * v⁻¹ * g⁻¹ = 1 := by
    have := Subgroup.mem_inf.2 ⟨h2, h1⟩
    rwa [hUZ, Subgroup.mem_bot] at this
  calc v * g = (v * g * v⁻¹ * g⁻¹) * (g * v) := by group
    _ = g * v := by rw [h3, one_mul]

end Heisenberg

section PSU

variable (h : UnitaryFieldData 2 f K)

theorem zCentAt_hypPSU : ZCentAt (hypProjUnitriangular h 1 1) := by
  have : CharP K 2 := h.charP
  refine zCentAt_of_scalar (n := HypIndex 1 1) CharTwo.two_eq_zero (hypSU h 1 1).subtype
    (Subgroup.subtype_injective _) (hypProj h 1 1) (hypProj_surjective h 1 1)
    (fun g hg => ?_) (rootEF_mul_self (K := K)) ?_
  · rw [← MonoidHom.mem_ker, ker_hypProj] at hg
    obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hg
    refine ⟨c, ?_⟩
    change ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = _
    rw [hc, GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]
  · rintro _ ⟨g, hg, rfl⟩ hcen
    obtain ⟨b, hb⟩ := center_hypUnitriangular h hg fun v hv =>
      commute_of_hypProj h hg hv (hcen _ ⟨v, hv, rfl⟩).symm
    exact ⟨g, b, rfl, hb⟩

theorem zCentAt_sylow_of_psu {X : Type} [Group X] [Finite X]
    (hX : StatedClassicalModel X .PSU 3 2 f) (P : Sylow 2 X) : ZCentAt (P : Subgroup X) := by
  obtain ⟨⟨hp, hf1, -⟩, L, _, _, hL, ⟨e₀⟩⟩ := hX
  have h : UnitaryFieldData 2 f L := ⟨hp, hf1, by rw [hL, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  let e : X ≃* hypPSU h 1 1 := e₀.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm
  refine zCentAt_sylow_of_mulEquiv e (fun Q => ?_) P
  obtain ⟨-, -, -, -, ⟨P₀, hP₀⟩, -, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have : Finite (hypPSU h 1 1) := Finite.of_equiv X e.toEquiv
  refine zCentAt_sylow (P₀ := P₀) ?_ Q
  rw [hP₀]
  exact zCentAt_hypPSU h

end PSU

section PGU

abbrev pguKer (K : Type) [Field K] (q : ℕ) : Subgroup ↥(StatedGU 3 q K) :=
  (StatedScalars (Fin 3) K).subgroupOf (StatedGU 3 q K)

theorem unitarySU_le_statedGU (h : UnitaryFieldData 2 f K) :
    unitarySU 2 f K 3 ≤ StatedGU 3 (2 ^ f) K := by
  rw [A318P.statedGU_eq_unitaryIsom3 h]
  exact CFSG.RankThree.PartTwo.KFacts.unitarySU_le_unitaryIsom3 (h := h)

variable (h : UnitaryFieldData 2 f K) {R : Matrix (Fin (2 * 1 + 1)) (HypIndex 1 1) K}

@[expose] noncomputable def pguHom (hR : IsHypTransport h R) :
    hypSU h 1 1 →* StatedGU 3 (2 ^ f) K :=
  (Subgroup.inclusion (unitarySU_le_statedGU h)).comp (hypTransport h hR).toMonoidHom

theorem coe_pguHom (hR : IsHypTransport h R) (g : hypSU h 1 1) :
    (((pguHom h hR g : StatedGU 3 (2 ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      R * ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
        transportInv h R :=
  rfl

theorem eq_one_of_pguHom_mem (hR : IsHypTransport h R) {g : hypSU h 1 1}
    (hg : g ∈ hypUnitriangular h 1 1) (hk : pguHom h hR g ∈ pguKer K (2 ^ f)) : g = 1 := by
  obtain ⟨c, hc₀⟩ := hk
  have hc' : GeneralLinearGroup.scalar (Fin 3) c =
      ((pguHom h hR g : StatedGU 3 (2 ^ f) K) : GL (Fin 3) K) := hc₀
  have hc : (((pguHom h hR g : StatedGU 3 (2 ^ f) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (c : K) := by
    rw [← hc', GeneralLinearGroup.coe_scalar]
  rw [coe_pguHom] at hc
  have hg' : ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      scalar (HypIndex 1 1) (c : K) := by
    have := congrArg (fun M => transportInv h R * M * R) hc
    rw [transportInv_scalar hR] at this
    rw [← this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, transportInv_mul hR, Matrix.one_mul,
      Matrix.mul_assoc, transportInv_mul hR, Matrix.mul_one]
  have hd := (mem_hypUnitriangular.1 hg).2 (.inl 0)
  rw [hg', scalar_apply, diagonal_apply_eq] at hd
  apply Subtype.ext
  apply Units.ext
  rw [hg', hd]
  simp

@[expose] noncomputable def pguSylow (hR : IsHypTransport h R) :
    Subgroup (StatedProj (StatedGU 3 (2 ^ f) K)) :=
  ((hypUnitriangular h 1 1).map (pguHom h hR)).map (QuotientGroup.mk' (pguKer K (2 ^ f)))

theorem exists_sylow_pguSylow (hR : IsHypTransport h R) :
    ∃ P : Sylow 2 (StatedProj (StatedGU 3 (2 ^ f) K)), (P : Subgroup _) = pguSylow h hR := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.finite
  set φ := (QuotientGroup.mk' (pguKer K (2 ^ f))).comp (pguHom h hR) with hφ
  have hinj : Function.Injective (φ.comp (hypUnitriangular h 1 1).subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg1
    have h1 : pguHom h hR g ∈ pguKer K (2 ^ f) :=
      (QuotientGroup.eq_one_iff (N := pguKer K (2 ^ f)) _).1 hg1
    exact Subtype.ext (eq_one_of_pguHom_mem h hR g.2 h1)
  have hrange : (φ.comp (hypUnitriangular h 1 1).subtype).range = pguSylow h hR := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, pguSylow, hφ, Subgroup.map_map]
  obtain ⟨hU, -, -, -, -, -, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have hcard : Nat.card (pguSylow h hR) = (2 ^ f) ^ 3 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hU]
  have hp : IsPGroup 2 (pguSylow h hR) := IsPGroup.of_card (n := f * 3) (by
    rw [hcard, ← pow_mul])
  refine ⟨hp.toSylow fun h2 => ?_, rfl⟩
  have hidx := (pguSylow h hR).index_mul_card
  rw [hcard, CFSG.Quasithin.R3c5.card_statedProj_statedGU_three h] at hidx
  have hq : (2 ^ f) ^ 3 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ two_ne_zero)
  have hidx' : (pguSylow h hR).index = ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) := by
    rw [mul_comm] at hidx
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) hidx
  rw [hidx'] at h2
  have hf : f ≠ 0 := by have := h.one_le; omega
  have hev : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, hf⟩
  have ho2 : Odd ((2 ^ f) ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ two_ne_zero)))
      (hev.pow_of_ne_zero two_ne_zero) odd_one
  have ho3 : Odd ((2 ^ f) ^ 3 + 1) := (hev.pow_of_ne_zero three_ne_zero).add_one
  exact (Nat.not_even_iff_odd.2 (ho2.mul ho3)) (even_iff_two_dvd.2 h2)

theorem zCentAt_pgu (hR : IsHypTransport h R) : ZCentAt (pguSylow h hR) := by
  have : CharP K 2 := h.charP
  refine zCentAt_of_scalar (n := Fin 3) CharTwo.two_eq_zero (StatedGU 3 (2 ^ f) K).subtype
    (Subgroup.subtype_injective _) (QuotientGroup.mk' (pguKer K (2 ^ f)))
    (QuotientGroup.mk'_surjective _) (fun x hx => ?_)
    (N := R * rootEF K * transportInv h R) ?_ ?_
  · obtain ⟨c, hc₀⟩ := (QuotientGroup.eq_one_iff (N := pguKer K (2 ^ f)) x).1 hx
    have hc : GeneralLinearGroup.scalar (Fin 3) c = (x : GL (Fin 3) K) := hc₀
    refine ⟨c, ?_⟩
    change ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [← hc, GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]
  · rw [show R * rootEF K * transportInv h R * (R * rootEF K * transportInv h R) =
      R * (rootEF K * (transportInv h R * R) * rootEF K) * transportInv h R by
        simp only [Matrix.mul_assoc], transportInv_mul hR, Matrix.mul_one, rootEF_mul_self,
      Matrix.mul_zero, Matrix.zero_mul]
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩ hcen
    have hcomm : ∀ v ∈ hypUnitriangular h 1 1, v * g = g * v := by
      intro v hv
      have h1 := (hcen _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩).symm
      have h2 : pguHom h hR (v * g * v⁻¹ * g⁻¹) ∈ pguKer K (2 ^ f) := by
        rw [← QuotientGroup.eq_one_iff (N := pguKer K (2 ^ f))]
        simp only [QuotientGroup.mk'_apply] at h1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
          h1]
        group
      have h3 := eq_one_of_pguHom_mem h hR
        (mul_mem (mul_mem (mul_mem hv hg) (inv_mem hv)) (inv_mem hg)) h2
      calc v * g = (v * g * v⁻¹ * g⁻¹) * (g * v) := by group
        _ = g * v := by rw [h3, one_mul]
    obtain ⟨b, hb⟩ := center_hypUnitriangular h hg hcomm
    refine ⟨pguHom h hR g, b, rfl, ?_⟩
    change (((pguHom h hR g : StatedGU 3 (2 ^ f) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = _
    rw [coe_pguHom, hb, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, mul_transportInv hR,
      Matrix.mul_smul, Matrix.smul_mul]

theorem zCentAt_sylow_of_pgu {X : Type} [Group X] [Finite X] (hf : 1 ≤ f)
    (hX : IsPGLEps3 false (2 ^ f) X) (P : Sylow 2 X) : ZCentAt (P : Subgroup X) := by
  obtain ⟨L, _, _, hL, ⟨e⟩⟩ := hX
  have h : UnitaryFieldData 2 f L := ⟨Nat.prime_two, hf, by rw [hL, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  refine zCentAt_sylow_of_mulEquiv e (fun Q => ?_) P
  have : Finite (StatedProj (StatedGU 3 (2 ^ f) L)) := Finite.of_equiv X e.toEquiv
  obtain ⟨P₀, hP₀⟩ := exists_sylow_pguSylow h hR
  refine zCentAt_sylow (P₀ := P₀) ?_ Q
  rw [hP₀]
  exact zCentAt_pgu h hR

end PGU

end CFSG.Quasithin.H13.ZCentLie
