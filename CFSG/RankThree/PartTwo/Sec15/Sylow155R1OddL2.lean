module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1AutDefs
public import CFSG.Open.PGLModelDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
import CFSG.Dihedral.DihedralFusionAutomorphisms
import CFSG.GroupTheory.IndexFourQuotientKernel
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

theorem fix_of_hasDihedralSylowTwo {S : Type} [Group S] [Finite S]
    (hS : CFSG.GorensteinWalter.HasDihedralSylowTwo S) {R : Subgroup S} (hR : IsPGroup 2 R)
    {γ : MulAut S} (hγR : ∀ r ∈ R, γ r ∈ R) (hγ : Nat.Coprime (orderOf γ) 6) :
    ∀ r ∈ R, γ r = r := by
  let β₀ : R →* R :=
    { toFun := fun r => ⟨γ r, hγR r r.2⟩
      map_one' := Subtype.ext (map_one γ)
      map_mul' := fun x y => Subtype.ext (map_mul γ (x : S) (y : S)) }
  have hβinj : Function.Injective β₀ := fun x y h =>
    Subtype.ext (γ.injective (congrArg Subtype.val h))
  have hβbij : Function.Bijective β₀ := ⟨hβinj, Finite.injective_iff_surjective.mp hβinj⟩
  let β : MulAut R := MulEquiv.ofBijective β₀ hβbij
  have hβpow : ∀ (n : ℕ) (r : R), (((β ^ n) r : R) : S) = (γ ^ n) (r : S) := by
    intro n
    induction n with
    | zero => intro r; rfl
    | succ n ih =>
      intro r
      rw [pow_succ, MulAut.mul_apply, ih (β r), pow_succ, MulAut.mul_apply]
      rfl
  have hβm : β ^ orderOf γ = 1 := by
    ext r
    rw [hβpow, pow_orderOf_eq_one]
    rfl
  have hβord : orderOf β ∣ orderOf γ := orderOf_dvd_of_pow_eq_one hβm
  have hβ1 : β = 1 := by
    by_cases hK : IsKleinFour R
    · have h6 := CFSG.GroupTheory.card_mulAut_dvd_six_of_card_eq_four (V := R) hK.card_four
      have h1 : orderOf β ∣ Nat.gcd (orderOf γ) 6 :=
        Nat.dvd_gcd hβord ((orderOf_dvd_natCard β).trans h6)
      rw [hγ.gcd_eq_one] at h1
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
    · obtain ⟨T, hRT⟩ := hR.exists_le_sylow
      obtain ⟨m, hm, ⟨e⟩⟩ := hS T
      obtain ⟨k, hk⟩ := CFSG.GorensteinWalter.dihedral_subgroup_automorphism_isTwoGroup T hm e R
        hRT hK β
      have hc : Nat.Coprime (2 ^ k) (orderOf γ) :=
        ((Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hγ).pow_right k).symm
      have h1 : orderOf β ∣ Nat.gcd (2 ^ k) (orderOf γ) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) hβord
      rw [hc.gcd_eq_one] at h1
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  intro r hr
  exact congrArg (fun ψ : MulAut R => ((ψ ⟨r, hr⟩ : R) : S)) hβ1

theorem res1AutCent_of_fix {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (hOut : ∀ α β : MulAut S, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : S →* MulAut S).range)
    (hfix : ∀ R : Subgroup S, IsPGroup 2 R → ∀ γ : MulAut S, (∀ r ∈ R, γ r ∈ R) →
      Nat.Coprime (orderOf γ) 6 → ∀ r ∈ R, γ r = r) :
    Res1AutCent S := by
  intro α V y _ hα _ hV hαV _ v hv
  have hinj := CFSG.mulAutConj_injective_of_center_eq_bot hZ
  have hconj : ∀ (σ : MulAut S) (g : S), σ * MulAut.conj g * σ⁻¹ = MulAut.conj (σ g) := by
    intro σ g
    ext x
    simp [MulAut.conj_apply]
  obtain ⟨d, hd⟩ : ∃ d : MulAut S, d = v⁻¹ * (α * v * α⁻¹) := ⟨_, rfl⟩
  have hdV : d ∈ V := by
    rw [hd]
    exact V.mul_mem (V.inv_mem hv) (hαV v hv)
  have hdI : d ∈ (MulAut.conj : S →* MulAut S).range := by
    have h := hOut v⁻¹ α
    rw [inv_inv] at h
    rw [hd]
    simpa only [mul_assoc] using h
  obtain ⟨s, hs⟩ := hdI
  have hsV : (MulAut.conj s : MulAut S) ∈ V := by
    rw [hs]
    exact hdV
  have hR1 : IsPGroup 2 (V.comap (MulAut.conj : S →* MulAut S)) :=
    hV.of_injective ((MulAut.conj : S →* MulAut S).subgroupComap V)
      (MonoidHom.subgroupComap_injective _ _ hinj)
  have hstab : ∀ r ∈ V.comap (MulAut.conj : S →* MulAut S),
      α r ∈ V.comap (MulAut.conj : S →* MulAut S) := by
    intro r hr
    rw [Subgroup.mem_comap] at hr ⊢
    rw [← hconj]
    exact hαV _ hr
  have hfixs : α s = s := hfix _ hR1 α hstab hα s hsV
  have hαd : α * d * α⁻¹ = d := by
    rw [← hs, hconj, hfixs]
  have hvd : α * v * α⁻¹ = v * d := by
    rw [hd, mul_inv_cancel_left]
  have hpow : ∀ k : ℕ, α ^ k * v * (α ^ k)⁻¹ = v * d ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc α ^ (k + 1) * v * (α ^ (k + 1))⁻¹
          = α * (α ^ k * v * (α ^ k)⁻¹) * α⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            simp only [mul_assoc]
        _ = α * (v * d ^ k) * α⁻¹ := by rw [ih]
        _ = (α * v * α⁻¹) * (α * d * α⁻¹) ^ k := by
            rw [conj_pow]
            simp only [mul_assoc, inv_mul_cancel_left]
        _ = v * d ^ (k + 1) := by rw [hvd, hαd, pow_succ', mul_assoc]
  have hdm : d ^ orderOf α = 1 := by
    have h := hpow (orderOf α)
    rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one] at h
    exact mul_left_cancel (a := v) (by rw [mul_one]; exact h.symm)
  obtain ⟨j, hj⟩ := hV ⟨d, hdV⟩
  have hdj : d ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hc : Nat.Coprime (2 ^ j) (orderOf α) :=
    ((Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hα).pow_right j).symm
  have hd1 : d = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hdj, hdm⟩
    rwa [hc.gcd_eq_one, pow_one] at h
  have h3 : α * v * α⁻¹ = v := by
    rw [hvd, hd1, mul_one]
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem res1AutCent_psl2 (K : Type) [Field K] [Finite K]
    (hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K)) :
    Res1AutCent (CFSG.GorensteinWalter.PSL2 K) := by
  refine res1AutCent_of_fix (CFSG.GorensteinWalter.psl2_center_eq_bot K) ?_ ?_
  · intro α β
    set q := QuotientGroup.mk'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (CFSG.GorensteinWalter.PSL2 K))
    have h := CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm K (q α) (q β)
    have h1 : q (α * β * α⁻¹ * β⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h, mul_inv_cancel_right, mul_inv_cancel]
    have h2 : α * β * α⁻¹ * β⁻¹ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (CFSG.GorensteinWalter.PSL2 K) :=
      (QuotientGroup.eq_one_iff _).mp h1
    exact h2
  · intro R hR γ hγR hγ
    exact fix_of_hasDihedralSylowTwo
      (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hodd) hR hγR hγ

theorem res1AutCent_projSL_two_of_odd {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Res1AutCent ↥(CFSG.PGLModel.projSL 2 (GaloisField p f)) := by
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp2, hf,
      GaloisField.card p f (by omega)⟩
  exact Res1AutCent.of_mulEquiv (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField p f))
    (res1AutCent_psl2 (GaloisField p f) hodd)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
