module

public import CFSG.Quasithin.MS93.ML3Syl
public import CFSG.Quasithin.MS93.FFTypes
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.MS93.ML3Ext2

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix

variable {F : Type} [Field F] [CharP F 2] [Finite F]
variable {V : Type} [CommGroup V] {ρ : SL3 F →* MulAut V}

namespace NatNatExt

variable (E : NatNatExt ρ)
include E

@[expose] noncomputable def rangeEquiv : SL3 F ≃* ↥ρ.range :=
  MonoidHom.ofInjective E.ρ_injective

omit [CharP F 2] in
theorem isQuasisimple_range : CFSG.IsQuasisimple ↥ρ.range :=
  (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr E.rangeEquiv).mp
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num)))

omit [CharP F 2] in
theorem isRankTwoLie2Derived_range {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    IsRankTwoLie2Derived (↥ρ.range ⧸ Subgroup.center ↥ρ.range) :=
  Or.inl ⟨n, (isPSL_quot_of_equiv_statedSL_three hF
    ((specialLinearGroupEquivStatedSL 3 F).symm.trans E.rangeEquiv)).2.1⟩

omit [CharP F 2] [Finite F] in
theorem cent_range (c : MulAut V) (hc : c ∈ ρ.range)
    (hcomm : ∀ k ∈ ρ.range, c * k = k * c) (e : ℕ) (he : c ^ 2 ^ e = 1) : c = 1 := by
  obtain ⟨g, rfl⟩ := hc
  have hg : g ∈ Subgroup.center (SL3 F) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply E.ρ_injective
    rw [map_mul, map_mul]
    exact (hcomm (ρ h) ⟨h, rfl⟩).symm
  obtain ⟨r, hr3, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  rw [Fintype.card_fin] at hr3
  have hge : g ^ 2 ^ e = 1 := E.ρ_injective (by rw [map_pow, he, map_one])
  have hre : r ^ 2 ^ e = 1 := by
    have h1 : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) ^ 2 ^ e = 1 := by
      have := congrArg (fun x : SL3 F => ((x : SL3 F) : Matrix (Fin 3) (Fin 3) F)) hge
      exact this
    rw [← hrg, ← map_pow, ← (Matrix.scalar (Fin 3)).map_one] at h1
    exact Matrix.scalar_inj.mp h1
  have hr : r = 1 := by
    have h1 : orderOf r ∣ 3 := orderOf_dvd_of_pow_eq_one hr3
    have h2 : orderOf r ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hre
    have hcop : Nat.Coprime 3 (2 ^ e) := Nat.Coprime.pow_right e (by norm_num)
    have := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2)
    exact orderOf_eq_one_iff.mp this
  have hg1 : g = 1 := by
    apply Subtype.ext
    rw [← hrg, hr, map_one]
    rfl
  rw [hg1, map_one]

omit [CharP F 2] in
theorem isSylowTwoOf_sStar {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    IsSylowTwoOf (sStar.map ρ) ρ.range := by
  refine ⟨Subgroup.map_le_range ρ sStar, (isPGroup_sStar hF).map ρ, ?_⟩
  have hcomap : ((sStar.map ρ).subgroupOf ρ.range).comap ρ.rangeRestrict = sStar := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MonoidHom.coe_rangeRestrict,
      Subgroup.mem_map_iff_mem E.ρ_injective]
  rw [← Subgroup.index_comap_of_surjective _ ρ.rangeRestrict_surjective, hcomap]
  exact not_two_dvd_index_sStar hF

variable (hV : ∀ v : V, v ^ 2 = 1)
include hV

theorem isFFModule_range [Finite V] : IsFFModule ρ.range := by
  refine ⟨qLn.map ρ, Subgroup.map_le_range ρ qLn, ?_, ⟨?_, ?_⟩, E.ms18_card_le hV⟩
  · intro h
    have hmem : ρ (tLn 1 0) ∈ qLn.map ρ := ⟨tLn 1 0, tLn_mem_qLn 1 0, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one ρ] at hmem
    have h2 := congrArg (fun g : SL3 F => ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1])
      (E.ρ_injective hmem)
    simp only [tLn_mulVec] at h2
    have := congrFun h2 0
    simp at this
  · rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
    obtain ⟨a, b, rfl⟩ := mem_qLn_iff_tLn.mp ht
    obtain ⟨a', b', rfl⟩ := mem_qLn_iff_tLn.mp ht'
    rw [← map_mul, ← map_mul, tLn_comm]
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨a, b, rfl⟩ := mem_qLn_iff_tLn.mp ht
    rw [← map_pow, sq, tLn_mul_self, map_one]

theorem ffHyp [Finite V] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hsq : SQTKGroup ↥ρ.range) :
    FFHyp ρ.range ρ.range where
  le := le_rfl
  le_normalizer := Subgroup.le_normalizer
  quasisimple := E.isQuasisimple_range
  sqtk := hsq
  rankTwo := E.isRankTwoLie2Derived_range hF
  cent := E.cent_range
  two := fun x hx => ⟨0, by simpa using hx⟩
  gen := ⟨sStar.map ρ, E.isSylowTwoOf_sStar hF, E.ms18_gen hV⟩
  fix := E.ms18_fixV
  ff := E.isFFModule_range hV

theorem ffConclusion [Finite V] (h14 : MS14AS) {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hsq : SQTKGroup ↥ρ.range) : FFConclusion ρ.range ρ.range :=
  h14 V hV ρ.range ρ.range (E.ffHyp hV hF hsq)

end NatNatExt

end CFSG.Quasithin.MS93
