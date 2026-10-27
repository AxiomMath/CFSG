module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofField
import CFSG.RankThree.PartTwo.Sec6.Item65UsedTools

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

theorem false_of_image {F Q : Type} [Group F] [Finite F] [Group Q] (K₁ : Subgroup F)
    (hK₁sn : K₁.IsSubnormal) (hK₁p : Group.IsPerfect K₁) (hK₁ne : K₁ ≠ ⊥)
    (hcyc : ∀ P : Sylow 3 K₁, IsCyclic P) (hQ : IsQuasisimple Q) (ρ : Q →* F)
    (hle : K₁ ≤ ρ.range) {u v : Q} (hu3 : ρ u ^ 3 = 1) (hv3 : ρ v ^ 3 = 1) (hu1 : ρ u ≠ 1)
    (huv : ρ u * ρ v = ρ v * ρ u) (hvu : ρ v ∉ Subgroup.zpowers (ρ u)) : False := by
  have hP := hK₁sn.comap ρ
  have hmapcomap : (K₁.comap ρ).map ρ = K₁ := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hle]
  rcases Sec6.subnormal_le_center_or_eq_top_of_isQuasisimple hQ hP with hPZ | hPtop
  · apply hK₁ne
    have hcomm : ⁅K₁, K₁⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx y hy
      rw [← hmapcomap] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp (hPZ hb)) a]
    rw [← Subgroup.isPerfect_iff.mp hK₁p, hcomm]
  · have hmem : ∀ w : Q, ρ w ∈ K₁ := fun w =>
      (show w ∈ K₁.comap ρ from hPtop ▸ Subgroup.mem_top w)
    refine false_of_isCyclic_sylow hcyc (u := ⟨ρ u, hmem u⟩) (v := ⟨ρ v, hmem v⟩)
      (Subtype.ext hu3) (Subtype.ext hv3) (fun h1 => hu1 (congrArg Subtype.val h1))
      (Subtype.ext huv) ?_
    intro hmem'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem'
    apply hvu
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this

variable {G : Type} [Group G] [Finite G]

theorem image_facts {Y K : Subgroup G} {c : G} (hcN : c ∈ Subgroup.normalizer (Y : Set G))
    (hc3 : c ^ 3 = 1) (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hT : IsType424 (K ⧸ aschbacherSolvableCore 3 K)) {X : Type} [Group X]
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* X) :
    ∃ K₁ : Subgroup ((MulAut.congr φ (Sec4.thetaQuotMulAut Y
        (Sec4.compAction Y ⟨c, hcN⟩))).toMonoidHom.eqLocus (MonoidHom.id X)),
      K₁.IsSubnormal ∧ Group.IsPerfect K₁ ∧ K₁ ≠ ⊥ ∧ (∀ P : Sylow 3 K₁, IsCyclic P) ∧
        ∀ z, z ∈ K₁ ↔ ∃ y : Y, (y : G) ∈ K ∧
          φ (y : Y ⧸ aschbacherSolvableCore 3 Y) = (z : X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set τc := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) with hτc
  set α := MulAut.congr φ τc with hαdef
  set F := α.toMonoidHom.eqLocus (MonoidHom.id X) with hF
  obtain ⟨K', hK', rfl⟩ := hK
  have hψmem : ∀ m : (Y ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G),
      φ (cMap Y c m) ∈ F := by
    intro m
    have h1 : τc (cMap Y c m) = cMap Y c m := by
      have hk : cMap Y c m ∈ (cMap Y c).range := ⟨m, rfl⟩
      rw [range_cMap hcN hc3] at hk
      exact hk
    change φ (τc (φ.symm (φ (cMap Y c m)))) = φ (cMap Y c m)
    rw [MulEquiv.symm_apply_apply, h1]
  set ψY : (Y ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) →* F :=
    (φ.toMonoidHom.comp (cMap Y c)).codRestrict F hψmem with hψYdef
  have hψs : Function.Surjective ψY := by
    rintro ⟨z, hz⟩
    have hz' : τc (φ.symm z) = φ.symm z := by
      have := congrArg φ.symm hz
      change φ.symm (φ (τc (φ.symm z))) = φ.symm z at this
      rwa [MulEquiv.symm_apply_apply] at this
    have hmem : φ.symm z ∈ (cMap Y c).range := by
      rw [range_cMap hcN hc3]
      exact hz'
    obtain ⟨m, hm⟩ := hmem
    refine ⟨m, Subtype.ext ?_⟩
    change φ (cMap Y c m) = z
    rw [hm, MulEquiv.apply_symm_apply]
  have : Group.IsPerfect K' := hK'.1
  refine ⟨K'.map ψY, hK'.2.1.map hψs, Group.IsPerfect.map _, ?_, ?_, fun z => ?_⟩
  · intro hbot
    apply fieldCent_map_cMap_ne_bot hK'
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨k, hk, rfl⟩
    have h1 : ψY k ∈ K'.map ψY := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : φ (cMap Y c k) = 1 := congrArg Subtype.val h1
    exact (MulEquiv.map_eq_one_iff φ).mp h2
  · set eK : K' ≃* K'.map (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype :=
      K'.equivMapOfInjective _ (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype_injective
      with heK
    set eQK : K' ⧸ aschbacherSolvableCore 3 K' ≃*
        K'.map (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype ⧸
          aschbacherSolvableCore 3 (K'.map (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype) :=
      QuotientGroup.congr _ _ eK (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three eK) with heQK
    have hQK : IsQuasisimple (K'.map (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype ⧸
        aschbacherSolvableCore 3 (K'.map (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eQK hK'.2.2
    have hcycK := isCyclic_sylow_three_of_isType424 hT hQK
    have hcycK' : ∀ P : Sylow 3 K', IsCyclic P := by
      refine isCyclic_sylow_of_quotient (aschbacherSolvableCore 3 K')
        (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1 ?_
      exact isCyclic_sylow_of_mulEquiv eQK.symm hcycK
    exact isCyclic_sylow_of_surjective (ψY.subgroupMap K') (MonoidHom.subgroupMap_surjective _ _)
      hcycK'
  · constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨(m : G), m.2.1⟩, ⟨m, hm, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨m, hm, hmy⟩, hy⟩
      refine ⟨m, hm, Subtype.ext ?_⟩
      have hm' : (⟨(m : G), m.2.1⟩ : Y) = y := Subtype.ext hmy
      rw [← hy, ← hm']
      rfl

theorem false_of_trivial {Y K : Subgroup G} {c : G} (hcN : c ∈ Subgroup.normalizer (Y : Set G))
    (hc3 : c ^ 3 = 1) (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hT : IsType424 (K ⧸ aschbacherSolvableCore 3 K))
    {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf] (hKf : PiField π p f Kf)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf))
    (hc1 : c ∈ Sec4.thetaQuotCentralizer Y) : False := by
  have hπ : π = false → UnitaryFieldData p f Kf := fun h => by subst h; exact hKf.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hKf.finite
  have hτ1 : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) = 1 := by
    obtain ⟨y, hy, hyc⟩ := hc1
    obtain rfl : y = ⟨c, hcN⟩ := Subtype.ext hyc
    exact hy
  obtain ⟨K₁, hK₁sn, hK₁p, hK₁ne, hcyc, -⟩ := image_facts hcN hc3 hK hT φ
  let F := (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩))).toMonoidHom
    |>.eqLocus (MonoidHom.id (projImage (slPi π 3 (p ^ f) Kf)))
  have hFtop : ∀ m, m ∈ F := by
    intro m
    change MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩)) m = m
    rw [hτ1, map_one]
    rfl
  let ρ : slPi π 3 (p ^ f) Kf →* F := (projOf _).codRestrict F (fun s => hFtop _)
  have hρs : Function.Surjective ρ := by
    rintro ⟨m, hm⟩
    obtain ⟨s, rfl⟩ := projOf_surjective _ m
    exact ⟨s, rfl⟩
  have hle : K₁ ≤ ρ.range := fun z _ => hρs z
  have hQ : IsQuasisimple (slPi π 3 (p ^ f) Kf) := Sec13.isQuasisimple_slPi hKf hq2
  obtain ⟨τ, hτ, hτ1'⟩ := exists_tau hKf hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  let u : slPi π 3 (p ^ f) Kf := ⟨diagTau hτ, diagTau_mem_slPi hπ hq' hτ⟩
  let v : slPi π 3 (p ^ f) Kf := ⟨cycThree, cycThree_mem_slPi hπ⟩
  have hu' : ((u : slPi π 3 (p ^ f) Kf) : GL (Fin 3) Kf) = diagTau hτ := rfl
  have hv' : ((v : slPi π 3 (p ^ f) Kf) : GL (Fin 3) Kf) = cycThree := rfl
  have hcoe : ∀ s : slPi π 3 (p ^ f) Kf, (((ρ s : F) : projImage (slPi π 3 (p ^ f) Kf)) :
      ProjGenLinGroup (Fin 3) Kf) = ProjGenLinGroup.mk (s : GL (Fin 3) Kf) := fun s => rfl
  have hinjF : ∀ x y : F, (((x : projImage (slPi π 3 (p ^ f) Kf)) :
      ProjGenLinGroup (Fin 3) Kf)) = (((y : projImage (slPi π 3 (p ^ f) Kf)) :
        ProjGenLinGroup (Fin 3) Kf)) → x = y := fun x y hxy =>
    Subtype.ext (Subtype.ext hxy)
  refine false_of_image K₁ hK₁sn hK₁p hK₁ne hcyc hQ ρ hle (u := u) (v := v) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow]
    have : u ^ 3 = 1 := Subtype.ext (diagTau_pow_three hτ)
    rw [this, map_one]
  · rw [← map_pow]
    have : v ^ 3 = 1 := Subtype.ext cycThree_pow_three
    rw [this, map_one]
  · intro h1
    have h2 := congrArg (fun x : F => ((x : projImage (slPi π 3 (p ^ f) Kf)) :
      ProjGenLinGroup (Fin 3) Kf)) h1
    simp only [hcoe, Subgroup.coe_one, hu'] at h2
    obtain ⟨z, hz⟩ := mk_eq_one_iff_mem_statedScalars.mp h2
    have e00 : (z : Kf) = τ := by
      have := congrArg (fun A : GL (Fin 3) Kf => (A : Matrix (Fin 3) (Fin 3) Kf) 0 0) hz
      simpa [GeneralLinearGroup.coe_scalar, coe_diagTau] using this
    have e22 : (z : Kf) = 1 := by
      have := congrArg (fun A : GL (Fin 3) Kf => (A : Matrix (Fin 3) (Fin 3) Kf) 2 2) hz
      simpa [GeneralLinearGroup.coe_scalar, coe_diagTau] using this
    exact hτ1' (e00.symm.trans e22)
  · apply hinjF
    simp only [Subgroup.coe_mul, hcoe, hu', hv']
    exact mk_diagTau_mul_mk_cycThree hτ hτ0
  · intro hmem
    have hfin : IsOfFinOrder (ρ u) := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, by
      rw [← map_pow]
      have : u ^ 3 = 1 := Subtype.ext (diagTau_pow_three hτ)
      rw [this, map_one]⟩
    rw [← hfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨n, hn⟩ := hmem
    apply mk_cycThree_ne_mk_pow hτ n
    have h1 := congrArg (fun x : F => ((x : projImage (slPi π 3 (p ^ f) Kf)) :
      ProjGenLinGroup (Fin 3) Kf)) hn
    simp only [← map_pow, hcoe, SubgroupClass.coe_pow, hu', hv'] at h1
    rw [← h1]

theorem core_block {Y K : Subgroup G} {c : G} (hcN : c ∈ Subgroup.normalizer (Y : Set G))
    (hc3 : c ^ 3 = 1) (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hT : IsType424 (K ⧸ aschbacherSolvableCore 3 K))
    {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf] (hKf : PiField π p f Kf)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf)) :
    ∃ g ∈ glPi π 3 (p ^ f) Kf, ∃ e : Kfˣ, (e : Kf) ^ 3 = 1 ∧ e ≠ 1 ∧
      (∀ m, (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩)) m :
          ProjGenLinGroup (Fin 3) Kf) =
        ProjGenLinGroup.mk (g * diagE e * g⁻¹) * m *
          (ProjGenLinGroup.mk (g * diagE e * g⁻¹))⁻¹) ∧
      ∀ y : Y, (y : G) ∈ K → ∃ B ∈ glPi π 2 (p ^ f) Kf, GeneralLinearGroup.det B = 1 ∧
        (φ (y : Y ⧸ aschbacherSolvableCore 3 Y) : ProjGenLinGroup (Fin 3) Kf) =
          ProjGenLinGroup.mk (g * blockHom B * g⁻¹) := by
  rcases core_cases hcN hc3 hK hKf hq hq2 φ with hc1 | ⟨f₀, hf, σ, hσ, g₀, hg₀, hα⟩ | hblock
  · exact (false_of_trivial hcN hc3 hK hT hKf hq hq2 φ hc1).elim
  · exact (false_of_field hcN hc3 hK hT hKf hq hq2 φ hf hσ hg₀ hα).elim
  · exact hblock

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11
