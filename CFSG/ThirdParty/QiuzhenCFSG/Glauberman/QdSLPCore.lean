module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Glauberman

/-- The standard upper-unipotent subgroup of `SL₂(ZMod p)`, a Sylow
`p`-subgroup. -/
private def qdU (p : ℕ) [Fact p.Prime] : Subgroup (qdSL p) :=
  GorensteinWalter.sl2UpperUnipotentSubgroup (ZMod p)

private theorem qdU_card (p : ℕ) [Fact p.Prime] : Nat.card (qdU p) = p := by
  let e : Multiplicative (ZMod p) ≃* qdU p :=
    MulEquiv.ofBijective (GorensteinWalter.sl2UpperUnipotentHom (ZMod p)).rangeRestrict
      ⟨(MonoidHom.rangeRestrict_injective_iff
          (f := GorensteinWalter.sl2UpperUnipotentHom (ZMod p))).2
          GorensteinWalter.sl2UpperUnipotentHom_injective,
        MonoidHom.rangeRestrict_surjective _⟩
  calc
    Nat.card (qdU p) = Nat.card (Multiplicative (ZMod p)) := Nat.card_congr e.symm.toEquiv
    _ = p := by simp

private theorem qdSL_factorization (p : ℕ) [Fact p.Prime] (_hpodd : p ≠ 2) :
    (Nat.card (qdSL p)).factorization p = 1 := by
  have hp' : p.Prime := Fact.out
  have hpgt1 : 1 < p := hp'.one_lt
  have hp0 : 0 < p := by omega
  have hp2ne : p ^ 2 - 1 ≠ 0 := by
    intro h
    have hle : p ^ 2 ≤ 1 := Nat.sub_eq_zero_iff_le.mp h
    nlinarith [sq_pos_of_pos hp0]
  have hcard : Nat.card (qdSL p) = p * (p ^ 2 - 1) := by
    calc
      Nat.card (qdSL p) = Nat.card (ZMod p) * (Nat.card (ZMod p) ^ 2 - 1) :=
        GorensteinWalter.sl2_card_formula (ZMod p)
      _ = p * (p ^ 2 - 1) := by simp
  have hnot : ¬ p ∣ p ^ 2 - 1 := by
    intro h
    have hfac : p ^ 2 - 1 = (p + 1) * (p - 1) := by
      simpa [mul_comm] using (sq_tsub_sq p 1)
    have h' : p ∣ (p + 1) * (p - 1) := by
      simpa [hfac] using h
    rcases hp'.dvd_mul.mp h' with h1 | h2
    · have h1' : p ∣ 1 := Nat.dvd_add_self_left.mp h1
      have hp_le : p ≤ 1 := Nat.le_of_dvd (by omega : 0 < 1) h1'
      omega
    · have hp1pos : 0 < p - 1 := by omega
      have hp_le : p ≤ p - 1 := Nat.le_of_dvd hp1pos h2
      omega
  rw [hcard, Nat.factorization_mul (by omega) hp2ne, Finsupp.add_apply,
    Nat.Prime.factorization_self hp', Nat.factorization_eq_zero_of_not_dvd hnot]

private noncomputable def qdUSylow (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) : Sylow p (qdSL p) :=
  Sylow.ofCard (qdU p) (by
    rw [qdU_card, qdSL_factorization p hpodd]
    simp)

private def qdW (p : ℕ) [Fact p.Prime] : qdSL p :=
  GorensteinWalter.sl2SymplecticMatrix (ZMod p)

private theorem qdU_inter_conjW_eq_bot (p : ℕ) [Fact p.Prime] :
    qdU p ⊓ (qdU p).map (MulAut.conj (qdW p)).toMonoidHom = ⊥ := by
  apply eq_bot_iff.mpr
  intro A hA
  have hAU : A ∈ qdU p := hA.1
  have hAUw : A ∈ (qdU p).map (MulAut.conj (qdW p)).toMonoidHom := hA.2
  rcases (GorensteinWalter.mem_sl2UpperUnipotentSubgroup_iff A).mp hAU with ⟨x, rfl⟩
  rcases Subgroup.mem_map.mp hAUw with ⟨B, hB, hBA⟩
  rcases (GorensteinWalter.mem_sl2UpperUnipotentSubgroup_iff B).mp hB with ⟨y, rfl⟩
  have hB'A : GorensteinWalter.sl2UpperUnipotent x =
      (GorensteinWalter.sl2UpperUnipotent y)⁻¹.transpose := by
    rw [← hBA]
    simpa [qdW, MulAut.conj_apply] using
      (GorensteinWalter.sl2_transpose_inv_eq_conj_symplectic (ZMod p)
        (GorensteinWalter.sl2UpperUnipotent y)).symm
  have hx : x = 0 := by
    have h0 := congrFun (congrFun (congrArg Subtype.val hB'A) 0) 1
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl] at h0
    simp [GorensteinWalter.sl2UpperUnipotent] at h0
    exact h0
  rw [hx]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The p-core of `SL₂(p)` is trivial for odd prime `p`. -/
public theorem qdSL_pCore_eq_bot (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    pCore p (qdSL p) = ⊥ := by
  classical
  let U : Subgroup (qdSL p) := qdU p
  let US : Sylow p (qdSL p) := qdUSylow p hpodd
  let W : qdSL p := qdW p
  let UW : Sylow p (qdSL p) :=
    Sylow.mapSurjective (f := (MulAut.conj W).toMonoidHom)
      (MulAut.conj W).surjective US
  have h1 : pCore p (qdSL p) ≤ U := by
    simpa [U, US, qdUSylow, qdU] using
      (IsPGroup.le_sylow_of_normal (N := pCore p (qdSL p))
        (pCore_isPGroup (G := qdSL p) (p := p)) US)
  have h2 : pCore p (qdSL p) ≤ (UW : Subgroup (qdSL p)) :=
    IsPGroup.le_sylow_of_normal (pCore_isPGroup (G := qdSL p) (p := p)) UW
  have hUW : (UW : Subgroup (qdSL p)) = U.map (MulAut.conj W).toMonoidHom := by
    dsimp [UW, US, qdUSylow]
  apply le_bot_iff.mp
  intro x hx
  have hxU : x ∈ U := h1 hx
  have hxUW : x ∈ U.map (MulAut.conj W).toMonoidHom := by
    rw [← hUW]
    exact h2 hx
  have hbot : U ⊓ (U.map (MulAut.conj W).toMonoidHom) = ⊥ := by
    simpa [U, W] using qdU_inter_conjW_eq_bot p
  exact (eq_bot_iff.mp hbot) (Subgroup.mem_inf.mpr ⟨hxU, hxUW⟩)

end CFSG.Glauberman
