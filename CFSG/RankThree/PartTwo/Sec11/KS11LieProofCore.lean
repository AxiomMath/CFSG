module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofAut
public import CFSG.RankThree.PartTwo.Sec11.FieldCentRigidProof
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

variable {G : Type} [Group G] [Finite G]

theorem not_isSolvable_thetaQuot {Y K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G))) :
    ¬ Group.IsSolvable (Y ⧸ aschbacherSolvableCore 3 Y) := by
  intro hs
  exact fieldCent_false_of_isSolvable hcN hc3 hK inferInstance

theorem exists_model {Y K : Subgroup G} {c : G}
    (hY : Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y))
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G))) :
    ∃ (π : Bool) (p f : ℕ) (Kf : Type) (_ : Field Kf), PiField π p f Kf ∧
      ModThree π (p ^ f) ∧ 2 < p ^ f ∧
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf)) := by
  obtain ⟨p, e, hp, he, hiso⟩ := hY
  obtain ⟨π, Kf, _, hKf, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
  refine ⟨π, p, e, Kf, inferInstance, hKf, hq, ?_, ⟨φ⟩⟩
  by_contra hle
  have h2 : p ^ e = 2 := by
    have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
    omega
  apply not_isSolvable_thetaQuot hcN hc3 hK
  cases π
  · have hs : Group.IsSolvable (slPi false 3 (p ^ e) Kf) := Sec13.isSolvable_slPi_two hKf h2
    have hs' : Group.IsSolvable (projImage (slPi false 3 (p ^ e) Kf)) :=
      Group.isSolvable_of_surjective (projOf_surjective _)
    exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
  · change p ^ e % 3 = 1 at hq
    omega

theorem thetaQuotMulAut_pow_three {Y : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (Y : Set G)) (hx3 : x ^ 3 = 1) :
    Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨x, hxN⟩) ^ 3 = 1 := by
  have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hx3)
  rw [← map_pow, ← map_pow, h1, map_one, map_one]

theorem thetaQuotMulAut_of_mem {Y : Subgroup G} {x : G} (hxY : x ∈ Y)
    (hxN : x ∈ Subgroup.normalizer (Y : Set G)) :
    Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨x, hxN⟩) =
      MulAut.conj ((⟨x, hxY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H z =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

theorem core_cases {Y K : Subgroup G} {c : G} (hcN : c ∈ Subgroup.normalizer (Y : Set G))
    (hc3 : c ^ 3 = 1) (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf] (hKf : PiField π p f Kf)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf)) :
    c ∈ Sec4.thetaQuotCentralizer Y ∨
    (∃ f₀ : ℕ, f = 3 * f₀ ∧ ∃ σ : Kf ≃+* Kf,
      ((∀ x, σ x = x ^ piCard π (p ^ f₀)) ∨ ∀ x, σ x = x ^ (piCard π (p ^ f₀) ^ 2)) ∧
      ∃ g ∈ glPi π 3 (p ^ f) Kf, ∀ s (hs : s ∈ slPi π 3 (p ^ f) Kf),
        (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩))
          (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) Kf) =
          ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹)) ∨
    (∃ g ∈ glPi π 3 (p ^ f) Kf, ∃ e : Kfˣ, (e : Kf) ^ 3 = 1 ∧ e ≠ 1 ∧
      (∀ m, (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩)) m :
          ProjGenLinGroup (Fin 3) Kf) =
        ProjGenLinGroup.mk (g * diagE e * g⁻¹) * m *
          (ProjGenLinGroup.mk (g * diagE e * g⁻¹))⁻¹) ∧
      ∀ y : Y, (y : G) ∈ K → ∃ B ∈ glPi π 2 (p ^ f) Kf, GeneralLinearGroup.det B = 1 ∧
        (φ (y : Y ⧸ aschbacherSolvableCore 3 Y) : ProjGenLinGroup (Fin 3) Kf) =
          ProjGenLinGroup.mk (g * blockHom B * g⁻¹)) := by
  set τc := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) with hτc
  set α := MulAut.congr φ τc with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow, hτc, thetaQuotMulAut_pow_three hcN hc3, map_one]
  have hπ : π = false → UnitaryFieldData p f Kf := fun h => by subst h; exact hKf.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have : Group.IsPerfect (projImage (slPi π 3 (p ^ f) Kf)) :=
    Sec13.isPerfect_projImage_slPi hKf hq2
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hKf hq
  rcases aut_pgl_or_field hKf hq2 α hα3 with ⟨y₀, hy₀H, hy₀⟩ | hfield
  swap
  · exact Or.inr (Or.inl hfield)
  have hmk1 : ∀ w ∈ StatedScalars (Fin 3) Kf, ProjGenLinGroup.mk w = 1 := fun w hw =>
    mk_eq_one_iff_mem_statedScalars.mpr hw
  by_cases hy₀Z : y₀ ∈ zPi π 3 (p ^ f) Kf
  ·
    left
    have hy₀s : y₀ ∈ StatedScalars (Fin 3) Kf := by
      rw [zPi_eq hπ hq' hτ hτ1] at hy₀Z
      exact hy₀Z.2
    have hα1 : α = 1 := by
      ext m
      have h1 := hy₀ m
      rw [hmk1 y₀ hy₀s, one_mul, inv_one, mul_one] at h1
      exact h1
    have hτ1' : τc = 1 := by
      apply (MulAut.congr φ).injective
      rw [← hα, hα1, map_one]
    exact ⟨⟨c, hcN⟩, MonoidHom.mem_ker.mpr hτ1', rfl⟩
  right
  right
  have hα3m : ∀ m : projImage (slPi π 3 (p ^ f) Kf), α (α (α m)) = m := by
    intro m
    have h := congrArg (fun β : MulAut (projImage (slPi π 3 (p ^ f) Kf)) => β m) hα3
    simpa [pow_succ, MulAut.mul_apply] using h
  have hy₀3s : y₀ ^ 3 ∈ StatedScalars (Fin 3) Kf := by
    refine mem_statedScalars_of_comm_mod hKf hq fun s hs => ?_
    rw [← mk_eq_one_iff_mem_statedScalars]
    have h1 := congrArg (fun m : projImage (slPi π 3 (p ^ f) Kf) =>
      (m : ProjGenLinGroup (Fin 3) Kf)) (hα3m (projOf _ ⟨s, hs⟩))
    rw [hy₀, hy₀, hy₀, coe_projOf] at h1
    simp only [map_mul, map_inv, map_pow]
    have h2 : ProjGenLinGroup.mk y₀ ^ 3 * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y₀ ^ 3)⁻¹ =
        ProjGenLinGroup.mk s := by
      calc ProjGenLinGroup.mk y₀ ^ 3 * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y₀ ^ 3)⁻¹ =
          ProjGenLinGroup.mk y₀ * (ProjGenLinGroup.mk y₀ * (ProjGenLinGroup.mk y₀ *
            ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y₀)⁻¹) * (ProjGenLinGroup.mk y₀)⁻¹) *
              (ProjGenLinGroup.mk y₀)⁻¹ := by rw [pow_three]; group
        _ = ProjGenLinGroup.mk s := h1
    rw [h2, mul_inv_cancel]
  have hy₀3 : y₀ ^ 3 ∈ zPi π 3 (p ^ f) Kf := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hy₀H 3, hy₀3s⟩
  obtain ⟨y, ⟨z, hz, rfl⟩, hcases⟩ := rank3II_4_10_one hKf hq hτ hτ1 hy₀H hy₀Z hy₀3
  have hzs : z ∈ StatedScalars (Fin 3) Kf := by
    rw [zPi_eq hπ hq' hτ hτ1] at hz
    exact hz.2
  have hmkz : ProjGenLinGroup.mk (y₀ * z) = ProjGenLinGroup.mk y₀ := by
    rw [map_mul, hmk1 z hzs, mul_one]
  have hfix : ∀ m : projImage (slPi π 3 (p ^ f) Kf), α m = m →
      ∃ s ∈ centMod (slPi π 3 (p ^ f) Kf) (y₀ * z),
        (m : ProjGenLinGroup (Fin 3) Kf) = ProjGenLinGroup.mk s := by
    intro m hm
    obtain ⟨⟨s, hs⟩, rfl⟩ := projOf_surjective _ m
    have h1 := congrArg (fun m : projImage (slPi π 3 (p ^ f) Kf) =>
      (m : ProjGenLinGroup (Fin 3) Kf)) hm
    rw [hy₀, coe_projOf] at h1
    have h2 : y₀ * s * y₀⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) Kf := by
      rw [← mk_eq_one_iff_mem_statedScalars]
      simp only [map_mul, map_inv]
      rw [h1, mul_inv_cancel]
    refine ⟨s, mem_centMod_iff_scalar.mpr ⟨hs, (y₀ * s * y₀⁻¹ * s⁻¹)⁻¹, inv_mem h2, ?_⟩, rfl⟩
    have hc1 := commute_of_mem_statedScalars hzs s⁻¹
    have hc2 := commute_of_mem_statedScalars (inv_mem h2) (y₀ * s)
    calc s * (y₀ * z) * s⁻¹ = s * y₀ * (z * s⁻¹) := by group
      _ = s * y₀ * (s⁻¹ * z) := by rw [hc1]
      _ = (y₀ * s * y₀⁻¹ * s⁻¹)⁻¹ * (y₀ * z) := by group
  have hsolv : Group.IsSolvable ↥(slPi π 3 (p ^ f) Kf ⊓ Subgroup.centralizer {y₀ * z}) →
      False := by
    intro hCs
    set C := centMod (slPi π 3 (p ^ f) Kf) (y₀ * z) with hC
    set C₀ := slPi π 3 (p ^ f) Kf ⊓ Subgroup.centralizer {y₀ * z} with hC₀
    have hC₀C : C₀ ≤ C := centralizer_le_centMod _ _
    have : Group.IsSolvable (C₀.subgroupOf C) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hC₀C).toMonoidHom) (MulEquiv.injective _)
    have : Group.IsSolvable (StatedScalars (Fin 3) Kf) := by
      refine Group.isSolvable_of_comm fun u v => Subtype.ext ?_
      exact commute_of_mem_statedScalars v.2 (u : GL (Fin 3) Kf)
    have hCs : Group.IsSolvable C := by
      refine Group.isSolvable_of_ker_le_range (C₀.subgroupOf C).subtype (commHom _ (y₀ * z)) ?_
      rw [ker_commHom, Subgroup.range_subtype]
    set S : Subgroup (ProjGenLinGroup (Fin 3) Kf) := C.map ProjGenLinGroup.mk with hS
    have hSs : Group.IsSolvable S :=
      Group.isSolvable_of_surjective (f := ProjGenLinGroup.mk.subgroupMap C)
        (MonoidHom.subgroupMap_surjective _ _)
    set F := α.toMonoidHom.eqLocus (MonoidHom.id (projImage (slPi π 3 (p ^ f) Kf))) with hF
    have hFS : ∀ m : F, ((m : projImage (slPi π 3 (p ^ f) Kf)) :
        ProjGenLinGroup (Fin 3) Kf) ∈ S := by
      intro m
      obtain ⟨s, hsC, hms⟩ := hfix m m.2
      rw [hms]
      exact Subgroup.mem_map_of_mem _ hsC
    set ι : F →* S := ((projImage (slPi π 3 (p ^ f) Kf)).subtype.comp F.subtype).codRestrict S
      hFS with hι
    have hιinj : Function.Injective ι := by
      intro m m' h
      have h' : ((ι m : S) : ProjGenLinGroup (Fin 3) Kf) =
          ((ι m' : S) : ProjGenLinGroup (Fin 3) Kf) := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    have hFs : Group.IsSolvable F := Group.isSolvable_of_isSolvable_injective hιinj
    obtain ⟨eF⟩ := fieldCent_nonempty_eqLocus_congr φ τc
    have hτs : Group.IsSolvable (τc.toMonoidHom.eqLocus
        (MonoidHom.id (Y ⧸ aschbacherSolvableCore 3 Y))) :=
      Group.isSolvable_of_isSolvable_injective (f := eF.toMonoidHom) eF.injective
    exact fieldCent_false_of_isSolvable hcN hc3 hK hτs
  rcases hcases with ⟨-, ⟨eT⟩, -⟩ | ⟨⟨g, hg, e, he, hD⟩, -, hcent⟩ | ⟨-, -, -, hcyc, -⟩
  · exfalso
    apply hsolv
    have : Group.IsSolvable (Multiplicative (ZMod (qSubPi π (p ^ f))) ×
        Multiplicative (ZMod (qSubPi π (p ^ f)))) := inferInstance
    exact Group.isSolvable_of_isSolvable_injective (f := eT.toMonoidHom) eT.injective
  swap
  · exfalso
    apply hsolv
    have : CommGroup ↥(slPi π 3 (p ^ f) Kf ⊓ Subgroup.centralizer {y₀ * z}) :=
      IsCyclic.commGroup
    infer_instance
  have hy : y₀ * z = g * diagE e * g⁻¹ := eq_conj_of_inv_conj hD
  have he3 : (e : Kf) ^ 3 = 1 := by
    rcases he with he | he <;> rw [he]
    · exact hτ
    · rw [← pow_mul, pow_mul', hτ, one_pow]
  have he1 : e ≠ 1 := by
    intro h1
    rw [h1, Units.val_one] at he
    rcases he with he | he
    · exact hτ1 he.symm
    · apply hτ1
      have hτ0 : τ ≠ 0 := by
        rintro rfl
        simp at hτ
      calc τ = τ ^ 3 / τ ^ 2 := by field_simp
        _ = 1 := by rw [hτ, ← he, div_one]
  refine ⟨g, hg, e, he3, he1, fun m => ?_, ?_⟩
  · rw [hy₀, ← hy, hmkz]
  obtain ⟨K', hK', rfl⟩ := hK
  set Φ : GL (Fin 2) Kf →* ProjGenLinGroup (Fin 3) Kf :=
    (ProjGenLinGroup.mk : GL (Fin 3) Kf →* ProjGenLinGroup (Fin 3) Kf).comp
      ((MulAut.conj g).toMonoidHom.comp blockHom) with hΦ
  have hfixΦ : ∀ m : projImage (slPi π 3 (p ^ f) Kf), α m = m →
      (m : ProjGenLinGroup (Fin 3) Kf) ∈ (glPi π 2 (p ^ f) Kf).map Φ := by
    intro m hm
    obtain ⟨s, hsC, hms⟩ := hfix m hm
    rw [hcent, hy, ← map_conj_centralizer hπ hg, centralizer_diagE_eq hKf he1] at hsC
    obtain ⟨s', ⟨B, hB, rfl⟩, rfl⟩ := hsC
    exact ⟨B, hB, hms.symm⟩
  set KX : Subgroup (ProjGenLinGroup (Fin 3) Kf) :=
    ((K'.map (cMap Y c)).map φ.toMonoidHom).map (projImage (slPi π 3 (p ^ f) Kf)).subtype
    with hKX
  have hKXle : KX ≤ (glPi π 2 (p ^ f) Kf).map Φ := by
    rintro _ ⟨_, ⟨_, ⟨k, -, rfl⟩, rfl⟩, rfl⟩
    apply hfixΦ
    have h1 : τc (cMap Y c k) = cMap Y c k := by
      have hk : cMap Y c k ∈ (cMap Y c).range := ⟨k, rfl⟩
      rw [range_cMap hcN hc3] at hk
      exact hk
    change φ (τc (φ.symm (φ (cMap Y c k)))) = φ (cMap Y c k)
    rw [MulEquiv.symm_apply_apply, h1]
  have hKXp : Group.IsPerfect KX := by
    have : Group.IsPerfect K' := hK'.1
    have : Group.IsPerfect (K'.map (cMap Y c)) := Group.IsPerfect.map _
    have : Group.IsPerfect ((K'.map (cMap Y c)).map φ.toMonoidHom) := Group.IsPerfect.map _
    exact Group.IsPerfect.map _
  have hcomm : ⁅glPi π 2 (p ^ f) Kf, glPi π 2 (p ^ f) Kf⁆ ≤
      glPi π 2 (p ^ f) Kf ⊓ (GeneralLinearGroup.det : GL (Fin 2) Kf →* Kfˣ).ker := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)
    · rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
  have hKX2 : KX ≤ (glPi π 2 (p ^ f) Kf ⊓
      (GeneralLinearGroup.det : GL (Fin 2) Kf →* Kfˣ).ker).map Φ := by
    calc KX = ⁅KX, KX⁆ := (Subgroup.isPerfect_iff.mp hKXp).symm
      _ ≤ ⁅(glPi π 2 (p ^ f) Kf).map Φ, (glPi π 2 (p ^ f) Kf).map Φ⁆ :=
          Subgroup.commutator_mono hKXle hKXle
      _ = ⁅glPi π 2 (p ^ f) Kf, glPi π 2 (p ^ f) Kf⁆.map Φ := (Subgroup.map_commutator _ _ _).symm
      _ ≤ _ := Subgroup.map_mono hcomm
  intro y hyK
  obtain ⟨k, hk, hky⟩ := hyK
  have hmem : (φ (y : Y ⧸ aschbacherSolvableCore 3 Y) : ProjGenLinGroup (Fin 3) Kf) ∈ KX := by
    refine ⟨φ (y : Y ⧸ aschbacherSolvableCore 3 Y), ⟨(y : Y ⧸ aschbacherSolvableCore 3 Y),
      ⟨k, hk, ?_⟩, rfl⟩, rfl⟩
    change ((Subgroup.inclusion inf_le_left k : Y) : Y ⧸ aschbacherSolvableCore 3 Y) = _
    congr 1
    exact Subtype.ext hky
  obtain ⟨B, ⟨hB, hBdet⟩, hBe⟩ := hKX2 hmem
  exact ⟨B, hB, hBdet, hBe.symm⟩

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11
