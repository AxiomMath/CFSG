module

public import CFSG.RankThree.PartOne.KEXC.RootTrivial
public import CFSG.RankThree.PartOne.KEXC.ReeModel
public import CFSG.RankThree.PartOne.KEXC.Torsion
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.KEXC.TorusParam

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]
  (D : ReeFrameData K L a)

theorem sector_no_plane (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {w : WeylGroup ReeTag.F4.tag} {m : ℕ} (hmodd : Odd m)
    {U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ}
    (hP : ParamData a L D.F w m U) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K - 1) (hpm : p ∣ m)
    (hSyl : p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ m ^ 2)
    (hroots : ∀ α : Fin ReeTag.F4.tag.rank → ℤ, IsRoot ReeTag.F4.tag α →
      ¬ ((p : ℤ) ∣ ∑ i, U 0 i * α i ∧ (p : ℤ) ∣ ∑ i, U 1 i * α i))
    {Uγ Eγ : Subgroup (ReeTag.F4.reeGamma K a)} (hU2 : IsPGroup 2 Uγ) (hU0 : Uγ ≠ ⊥)
    (hE : IsElementaryAbelian p Eγ) (hEc : Nat.card Eγ = p ^ 2)
    (hEU : Eγ ≤ Subgroup.normalizer (Uγ : Set (ReeTag.F4.reeGamma K a))) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨Φ, hΦinj, hΦ, -, hΦF⟩ := hP.param
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  have hnadj : n ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w
  obtain ⟨h, hh⟩ := D.lang ⟨n, hnadj⟩
  have hFh : D.F h = h * ⟨n, hnadj⟩ := by
    rw [hh]
    group
  set g₀ : ModGL ReeTag.F4.tag L := (h : ModGL ReeTag.F4.tag L) with hg₀
  have hg₀adj : g₀ ∈ adjointGroup ReeTag.F4.tag L := h.2
  have hFg₀ : Fext D.F g₀ = g₀ * n := by
    rw [Fext_of_mem D.F hg₀adj]
    have : (⟨g₀, hg₀adj⟩ : adjointGroup ReeTag.F4.tag L) = h := rfl
    rw [this, hFh]
    rfl
  have hΦrange : Φ.range ≤ twistedFixed D.F n := by
    rintro _ ⟨z, rfl⟩
    exact hΦF z
  obtain ⟨T, hTmem, -, hTcard⟩ := exists_twisted_embedding D hg₀adj hFg₀ Φ.range hΦrange
  have hTdvd : p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ Nat.card T := by
    rw [hTcard, card_range_of_odd hmodd Φ hΦinj]
    exact hSyl
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨c, hc⟩ := exists_conj_le_of_card_dvd T hTdvd hE.isPGroup
  let ψ : ReeTag.F4.reeGamma K a →* ModGL ReeTag.F4.tag L :=
    ((MulAut.conj g₀⁻¹).toMonoidHom.comp (thetaGamma L a)).comp (MulAut.conj c).toMonoidHom
  have hψ : ∀ x, ψ x = g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ := fun x => by
    simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := by
    intro d₁ d₂ h12
    rw [hψ, hψ] at h12
    have h1 := mul_left_cancel (mul_right_cancel h12)
    exact mul_left_cancel (mul_right_cancel (thetaGamma_injective L h1))
  have hψmem : ∀ x, ψ x ∈ adjointGroup ReeTag.F4.tag L := fun x => by
    rw [hψ]
    exact mul_mem (mul_mem (inv_mem hg₀adj) (thetaGamma_mem_adjointGroup L _)) hg₀adj
  have hψtw : ∀ x, ψ x ∈ twistedFixed D.F n := fun x => by
    rw [hψ]
    exact conj_mem_twistedFixed D.F hg₀adj hFg₀ (thetaGamma_mem_adjointGroup L _)
      (D.fext_theta _)
  have hψΦ : ∀ x ∈ Eγ, ψ x ∈ Φ.range := fun x hx => by
    rw [hψ]
    exact (hTmem _).1 (hc x hx)
  have hEcomm : ∀ x ∈ Eγ, ∀ y ∈ Eγ, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : Eγ) ⟨y, hy⟩)
  have hEexp : ∀ x ∈ Eγ, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hEle : Eγ.map ψ ≤ (pTors m p).map Φ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz⟩ := hψΦ x hx
    have h1 : Φ (z ^ p) = 1 := by rw [map_pow, hz, ← map_pow, hEexp x hx, map_one]
    have h2 : z ^ p = 1 := hΦinj (h1.trans (map_one Φ).symm)
    exact ⟨z, (mem_pTors z).2 ⟨congrArg (fun y => (y.1 : Lˣ)) h2,
      congrArg (fun y => (y.2 : Lˣ)) h2⟩, hz⟩
  have hcardE : Nat.card ((pTors m p).map Φ) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hΦinj, card_pTors hp hp2 hpm]
  have : Finite ((pTors m p).map Φ) :=
    Nat.finite_of_card_ne_zero (by rw [hcardE]; exact (pow_pos hp.pos 2).ne')
  have hcardψ : Nat.card (Eγ.map ψ) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hψinj]
    exact hEc
  have hEeq : Eγ.map ψ = (pTors m p).map Φ :=
    Subgroup.eq_of_le_of_card_ge hEle (by rw [hcardE, hcardψ])
  obtain ⟨e, he, he1, t, htU, ht1, ht2, het⟩ :=
    exists_centralizing_involution hp hp2 hU2 hU0 hE hEc hEU
  set Rγ := invCentralizer Uγ e with hRγ
  have hRγ0 : Rγ ≠ ⊥ := by
    intro hbot
    have htR : t ∈ Rγ := mem_invCentralizer_of htU ht2 het.symm
    rw [hbot, Subgroup.mem_bot] at htR
    exact ht1 htR
  have hRγ2 : IsPGroup 2 Rγ := hU2.to_le invCentralizer_le
  have hRγN : Eγ ≤ Subgroup.normalizer (Rγ : Set (ReeTag.F4.reeGamma K a)) :=
    invCentralizer_normalized hEU hEcomm he
  obtain ⟨z₀, hz₀⟩ := hψΦ e he
  set b₀ := expTuple (z₀.1 : Lˣ) (z₀.2 : Lˣ) U with hb₀
  have hb₀eq : rootDiagUnit ReeTag.F4.tag b₀ = ψ e := (hΦ z₀).symm.trans hz₀
  have hbp₀ : ∀ i, b₀ i ^ p = 1 :=
    pow_eq_one_of_rootDiagUnit_pow_eq_one (by rw [hb₀eq, ← map_pow, hEexp e he, map_one])
  have hb₀1 : b₀ ≠ 1 := by
    intro h1
    rw [h1, rootDiagUnit_one] at hb₀eq
    exact he1 (hψinj (hb₀eq.symm.trans (map_one ψ).symm))
  have hR₀S : Rγ.map ψ ≤ rootSpan ReeTag.F4.tag L (rootCharKernel b₀) ⊓ twistedFixed D.F n := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨-, hx2, hxe⟩
    refine ⟨?_, hψtw x⟩
    refine involution_mem_rootSpan hp hp3 hbp₀ hb₀1 (hψmem x) ?_ ?_
    · rw [hb₀eq, ← map_mul, ← map_mul, hxe]
    · rw [← map_mul, ← sq, hx2, map_one]
  have hEN : Eγ.map ψ ≤ Subgroup.normalizer ((Rγ.map ψ : Subgroup _) : Set _) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_normalizer_map ψ (hRγN hx)
  have hEtw : Eγ.map ψ ≤ twistedFixed D.F n := by
    rintro _ ⟨x, hx, rfl⟩
    exact hψtw x
  have hEp : ∀ y ∈ Eγ.map ψ, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hEexp x hx, map_one]
  obtain ⟨α, hαS, hαtriv⟩ := exists_root_trivial_on D ha hK w hp hp3 hpq hEN
    (fun h0 => hRγ0 ((Subgroup.map_eq_bot_iff_of_injective Rγ hψinj).1 h0)) (hRγ2.map ψ)
    hEtw hEp ⟨e, he, hb₀eq.symm⟩ hb₀1 hR₀S
  obtain ⟨ζ, hζp, hζ⟩ := exists_pTors_elt (L := L) (m := m) hp hp2 hpm
  have hmem1 : ((ζ, 1) : (rootsOfUnity m L) × (rootsOfUnity m L)) ∈ pTors m p :=
    (mem_pTors _).2 ⟨hζp, by simp⟩
  have hmem2 : ((1, ζ) : (rootsOfUnity m L) × (rootsOfUnity m L)) ∈ pTors m p :=
    (mem_pTors _).2 ⟨by simp, hζp⟩
  have hΦE : ∀ z ∈ pTors (L := L) m p,
      rootDiagUnit ReeTag.F4.tag (expTuple (z.1 : Lˣ) (z.2 : Lˣ) U) ∈ Eγ.map ψ := by
    intro z hz
    rw [hEeq, ← hΦ z]
    exact ⟨z, hz, rfl⟩
  have c1 := hαtriv _ (hΦE _ hmem1)
  have c2 := hαtriv _ (hΦE _ hmem2)
  rw [rootChar_expTuple] at c1 c2
  simp only [Subgroup.coe_one, one_zpow, mul_one, one_mul] at c1 c2
  exact hroots α hαS.1 ⟨hζ _ c1, hζ _ c2⟩

end CFSG.RankThree.PartOne.KEXC
