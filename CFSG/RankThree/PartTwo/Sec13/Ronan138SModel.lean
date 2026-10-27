module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec17.Item1730Conj

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}
variable {π : Bool} {p f : ℕ} {F : Type} [Field F]

@[expose] def ActsPGL (ψ : K ⧸ aschbacherSolvableCore 3 K ≃* projImage (slPi π 3 (p ^ f) F))
    (x : G) (y : GL (Fin 3) F) : Prop :=
  ∃ hx : x ∈ Subgroup.normalizer (K : Set G), y ∈ glPi π 3 (p ^ f) F ∧
    ∀ z : K ⧸ aschbacherSolvableCore 3 K,
      ((ψ (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hx⟩) z) :
          projImage (slPi π 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) =
        ProjGenLinGroup.mk y * (ψ z : ProjGenLinGroup (Fin 3) F) * (ProjGenLinGroup.mk y)⁻¹

variable {ψ : K ⧸ aschbacherSolvableCore 3 K ≃* projImage (slPi π 3 (p ^ f) F)}

theorem thetaQuotMulAut_mul {x x' : G} (hx : x ∈ Subgroup.normalizer (K : Set G))
    (hx' : x' ∈ Subgroup.normalizer (K : Set G)) (z : K ⧸ aschbacherSolvableCore 3 K) :
    Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x * x', mul_mem hx hx'⟩) z =
      Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hx⟩)
        (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x', hx'⟩) z) := by
  have : (⟨x * x', mul_mem hx hx'⟩ : Subgroup.normalizer (K : Set G)) = ⟨x, hx⟩ * ⟨x', hx'⟩ :=
    rfl
  rw [this, map_mul, map_mul, MulAut.mul_apply]

theorem ActsPGL.mul {x x' : G} {y y' : GL (Fin 3) F} (h : ActsPGL ψ x y)
    (h' : ActsPGL ψ x' y') : ActsPGL ψ (x * x') (y * y') := by
  obtain ⟨hx, hy, hact⟩ := h
  obtain ⟨hx', hy', hact'⟩ := h'
  refine ⟨mul_mem hx hx', mul_mem hy hy', fun z => ?_⟩
  rw [thetaQuotMulAut_mul hx hx', hact, hact', map_mul]
  group

theorem actsPGL_one (hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F) :
    ActsPGL ψ (1 : G) 1 := by
  refine ⟨one_mem _, one_mem _, fun z => ?_⟩
  have : (⟨1, one_mem _⟩ : Subgroup.normalizer (K : Set G)) = 1 := rfl
  rw [this, map_one, map_one, MulAut.one_apply, map_one, one_mul, inv_one, mul_one]

theorem ActsPGL.pow (hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F)
    {x : G} {y : GL (Fin 3) F} (h : ActsPGL ψ x y) (n : ℕ) : ActsPGL ψ (x ^ n) (y ^ n) := by
  induction n with
  | zero => simpa using actsPGL_one (ψ := ψ) hπ
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem actsPGL_of_mem (hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F)
    {k : G} (hk : k ∈ K) {s : GL (Fin 3) F} (hs : s ∈ slPi π 3 (p ^ f) F)
    (hψ : ((ψ ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) : projImage (slPi π 3 (p ^ f) F)) :
      ProjGenLinGroup (Fin 3) F) = ProjGenLinGroup.mk s) :
    ActsPGL ψ k s := by
  refine ⟨Subgroup.le_normalizer hk, Sec4.slPi_le_glPi hπ hs, fun z => ?_⟩
  have h1 := Sec17.thetaQuotMulAut_normalizerMonoidHom_of_mem (K := K) ⟨k, hk⟩
  rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ]

theorem actsPGL_of_mem_thetaQuotCentralizer {x : G} (hx : x ∈ Sec4.thetaQuotCentralizer K) :
    ActsPGL ψ x 1 := by
  obtain ⟨⟨x', hxN⟩, hker, hxx⟩ := Subgroup.mem_map.mp hx
  change x' = x at hxx
  subst hxx
  refine ⟨hxN, one_mem _, fun z => ?_⟩
  have h1 : Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x', hxN⟩) = 1 := hker
  rw [h1, MulAut.one_apply, map_one, one_mul, inv_one, mul_one]

theorem ActsPGL.mk_eq (hK : PiField π p f F) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) F))] {x : G} {y y' : GL (Fin 3) F}
    (h : ActsPGL ψ x y) (h' : ActsPGL ψ x y') :
    ProjGenLinGroup.mk y = ProjGenLinGroup.mk y' := by
  obtain ⟨hx, -, hact⟩ := h
  obtain ⟨hx', -, hact'⟩ := h'
  have hw : y⁻¹ * y' ∈ StatedScalars (Fin 3) F := by
    refine Sec4.mem_statedScalars_of_comm_mod hK hq fun s hs => ?_
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars]
    obtain ⟨z, hz⟩ := ψ.surjective ⟨ProjGenLinGroup.mk s, Subgroup.mem_map_of_mem _ hs⟩
    have e1 := hact z
    have e2 := hact' z
    rw [hz] at e1 e2
    have e3 : ProjGenLinGroup.mk y * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y)⁻¹ =
        ProjGenLinGroup.mk y' * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y')⁻¹ := by
      rw [← e1, ← e2]
    simp only [map_mul, map_inv]
    calc (ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk y' * ProjGenLinGroup.mk s *
          ((ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk y')⁻¹ * (ProjGenLinGroup.mk s)⁻¹ =
        (ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk y' * ProjGenLinGroup.mk s *
          (ProjGenLinGroup.mk y')⁻¹) * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk s)⁻¹ := by
          group
      _ = 1 := by rw [← e3]; group
  have := (Sec4.mk_eq_one_iff_mem_statedScalars).mpr hw
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this

theorem ActsPGL.mem_thetaQuotCentralizer {x : G} {y : GL (Fin 3) F} (h : ActsPGL ψ x y)
    (hy : ProjGenLinGroup.mk y = 1) : x ∈ Sec4.thetaQuotCentralizer K := by
  obtain ⟨hx, -, hact⟩ := h
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
  ext z
  apply ψ.injective
  apply Subtype.ext
  have := hact z
  rw [hy, one_mul, inv_one, mul_one] at this
  exact this

theorem ActsPGL.inv {x : G} {y : GL (Fin 3) F} (h : ActsPGL ψ x y) : ActsPGL ψ x⁻¹ y⁻¹ := by
  obtain ⟨hx, hy, hact⟩ := h
  refine ⟨inv_mem hx, inv_mem hy, fun z => ?_⟩
  have e1 : (⟨x⁻¹, inv_mem hx⟩ : Subgroup.normalizer (K : Set G)) = (⟨x, hx⟩)⁻¹ := rfl
  set w := Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x⁻¹, inv_mem hx⟩) z with hw
  have hzw : Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hx⟩) w = z := by
    rw [hw, e1, map_inv, map_inv, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have h2 := hact w
  rw [hzw] at h2
  rw [h2, map_inv]
  group

theorem ActsPGL.zpow (hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F)
    {x : G} {y : GL (Fin 3) F} (h : ActsPGL ψ x y) (n : ℤ) : ActsPGL ψ (x ^ n) (y ^ n) := by
  cases n with
  | ofNat n => simpa using h.pow hπ n
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc]
    exact (h.pow hπ (n + 1)).inv

theorem ActsPGL.inv_mul_mem_thetaQuotCentralizer {x x' : G} {y y' : GL (Fin 3) F}
    (h : ActsPGL ψ x y) (h' : ActsPGL ψ x' y')
    (hyy : ProjGenLinGroup.mk y = ProjGenLinGroup.mk y') :
    x⁻¹ * x' ∈ Sec4.thetaQuotCentralizer K := by
  refine (h.inv.mul h').mem_thetaQuotCentralizer ?_
  rw [map_mul, map_inv, hyy, inv_mul_cancel]

theorem ActsPGL.commute (hK : PiField π p f F) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) F))] {x x' : G} {y y' : GL (Fin 3) F}
    (h : ActsPGL ψ x y) (h' : ActsPGL ψ x' y') (hxx : x * x' = x' * x) :
    ProjGenLinGroup.mk y * ProjGenLinGroup.mk y' =
      ProjGenLinGroup.mk y' * ProjGenLinGroup.mk y := by
  have h1 := h.mul h'
  have h2 := h'.mul h
  rw [hxx] at h1
  have := ActsPGL.mk_eq hK hq h1 h2
  rwa [map_mul, map_mul] at this

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
