module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalPSL2ToPGammaL2Apply
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylowParameter
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13.S3320

open CFSG.QuasithinUnique CFSG.GorensteinWalter

variable {Q : Type} [Group Q] [Finite Q] {Y : Subgroup Q}

theorem dihedral_not_comm {m : ℕ} (hm : 2 ≤ m) :
    (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * DihedralGroup.r 1 := by
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
  intro h
  have h1 : (0 - 1 : ZMod (2 ^ m)) = 0 + 1 := DihedralGroup.sr.inj h
  have h2 : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by
    have : (2 : ZMod (2 ^ m)) = 0 := by
      have h3 : (0 - 1 : ZMod (2 ^ m)) - (0 + 1) = 0 := by rw [h1, sub_self]
      have h4 : (0 - 1 : ZMod (2 ^ m)) - (0 + 1) = -2 := by ring
      rw [h4, neg_eq_zero] at h3
      exact h3
    exact_mod_cast this
  rw [ZMod.natCast_eq_zero_iff] at h2
  have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem eq_top_of_L2prime [Y.Normal] (hC : Subgroup.centralizer (Y : Set Q) = ⊥) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hp5 : 5 ≤ p) (eY : ↥Y ≃* PSL2 (GaloisField p 1))
    {S : Subgroup Q} (hS : IsSylowTwoOf S ⊤) (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    Y = ⊤ := by
  classical
  set K := GaloisField p 1 with hKdef
  have hKcard : Nat.card K = p ^ 1 := GaloisField.card p 1 one_ne_zero
  have hK : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp.out, hp.out.odd_of_ne_two hp2, le_refl 1, hKcard⟩
  have hcard : 3 < Nat.card K := by rw [hKcard, pow_one]; omega
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKcard hK hcard
  set φ := normalPSL2ToPGammaL2 Y K hK hcard eY hsurj with hφ
  have hφinj := normalPSL2ToPGammaL2_injective Y K hK hcard eY hC hsurj
  have hAut : ∀ σ : K ≃+* K, σ = 1 := by
    obtain ⟨-, -, -, -, h1, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        hp.out le_rfl hKcard
    have : Subsingleton (K ≃+* K) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact fun σ => Subsingleton.elim σ 1
  have hPGL : ∀ x : PGammaL2 K, x ∈ pGammaL2PGLRange K := by
    intro x
    refine ⟨x.left, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · rw [SemidirectProduct.right_inl, hAut x.right]
  have hPSLY : ∀ z ∈ pGammaL2PSLRange K, ∃ y : ↥Y, φ y = z := by
    intro z hz
    obtain ⟨w, rfl⟩ := (mem_pGammaL2PSLRange_iff K z).mp hz
    refine ⟨eY.symm w, ?_⟩
    rw [hφ, normalPSL2ToPGammaL2_apply_subtype, MulEquiv.apply_symm_apply]
  have hle1 : pGammaL2PSLRange K ≤ φ.range :=
    normalPSL2ToPGammaL2_range_contains_psl Y K hK hcard eY hsurj
  have hle2 : φ.range ≤ pGammaL2PGLRange K := fun x _ => hPGL x
  have hrel := Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  rw [pGammaL2_psl_range_relIndex_pgl_eq_two K hK] at hrel
  have hcase : (pGammaL2PSLRange K).relIndex φ.range = 1 ∨
      φ.range.relIndex (pGammaL2PGLRange K) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ hrel) with h1 | h1
    · exact Or.inl h1
    · right
      rw [h1] at hrel
      omega
  rcases hcase with h | h
  ·
    rw [eq_top_iff]
    intro x _
    have hx : φ x ∈ pGammaL2PSLRange K :=
      (Subgroup.relIndex_eq_one.mp h) ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hPSLY _ hx
    rw [← hφinj hy]
    exact y.2
  ·
    exfalso
    have heq : φ.range = pGammaL2PGLRange K :=
      le_antisymm hle2 (Subgroup.relIndex_eq_one.mp h)
    let E : Q ≃* PGL2 K := (MonoidHom.ofInjective hφinj).trans
      ((MulEquiv.subgroupCongr heq).trans (pGammaL2PGLRangeEquiv K).symm)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, hS2, hSodd⟩ := hS
    have h3 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
    rw [h3] at hSodd
    let P : Sylow 2 Q := hS2.toSylow hSodd
    let P' : Sylow 2 (PGL2 K) := P.mapSurjective (f := E.toMonoidHom) E.surjective
    obtain ⟨m, -, ⟨eD⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model K hK P'
    have hm := pgl2_dihedral_sylow_parameter_ge_two K hK P' eD
    apply dihedral_not_comm hm
    have hcomm : ∀ a b : ↥(P' : Subgroup (PGL2 K)), a * b = b * a := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      apply Subtype.ext
      change a ∈ (S.map E.toMonoidHom) at ha
      change b ∈ (S.map E.toMonoidHom) at hb
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      simp only [Subgroup.coe_mul, ← map_mul, hab a' ha' b' hb']
    have := hcomm (eD.symm (DihedralGroup.r 1)) (eD.symm (DihedralGroup.sr 0))
    have := congrArg eD this
    simpa using this

end CFSG.Quasithin.H13.S3320
