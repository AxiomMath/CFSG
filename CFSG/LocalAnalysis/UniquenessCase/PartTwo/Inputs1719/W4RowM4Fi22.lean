module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowMGe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFi22Pack
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHeisOut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCenter
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

private theorem m4_orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have h1 : (2 : ZMod 3) ≠ 1 := by decide
  exact orderOf_eq_prime h2 h1

theorem fi22_involution_inverts_heis
    {r : Equiv.Perm (Fin 3510)} (hr : r ∈ fi22R) (hr2 : r * r = 1) (hr1 : r ≠ 1) :
    ∃ (x y : Fin 3 → Equiv.Perm (Fin 3510)) (z : Equiv.Perm (Fin 3510)),
      (∀ i, x i ∈ fi22P) ∧ (∀ i, y i ∈ fi22P) ∧ z ∈ fi22P ∧ HeisCfg 3 3 x y z ∧
        (∀ i, y i ^ 3 = 1) ∧ r * x 0 * r⁻¹ = (x 0)⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf r = 2 := orderOf_eq_prime (by rwa [pow_two]) hr1
  obtain ⟨k, hk, s, hs, hsr⟩ := fi22R_involution_conj hr ho
  obtain ⟨x, y, z, hxP, hyP, hzP, hcfg, hy3, hinv⟩ := fi22_ext_heisCfg hk
  have hsP : ∀ {g : Equiv.Perm (Fin 3510)}, g ∈ fi22P → s⁻¹ * g * s ∈ fi22P := by
    intro g hg
    have hsN : s⁻¹ ∈ Subgroup.normalizer (fi22P : Set (Equiv.Perm (Fin 3510))) :=
      Subgroup.inv_mem _ (fi22R_le_normalizer hs)
    have hg' := (Subgroup.mem_normalizer_iff.1 hsN g).1 hg
    simpa using hg'
  let f : Equiv.Perm (Fin 3510) →* Equiv.Perm (Fin 3510) := (MulAut.conj s⁻¹).toMonoidHom
  have hf : ∀ g, f g = s⁻¹ * g * s := by
    intro g
    show (MulAut.conj s⁻¹) g = s⁻¹ * g * s
    rw [MulAut.conj_apply, inv_inv]
  have hfz : f z ≠ 1 := fun h =>
    hcfg.z1 ((MulAut.conj s⁻¹).injective (by
      rw [show (MulAut.conj s⁻¹) z = 1 from h, map_one]))
  have hmap : HeisCfg 3 3 (fun i => s⁻¹ * x i * s) (fun i => s⁻¹ * y i * s)
      (s⁻¹ * z * s) := by
    have h' := hcfg.map f hfz
    simpa only [hf] using h'
  refine ⟨fun i => s⁻¹ * x i * s, fun i => s⁻¹ * y i * s, s⁻¹ * z * s,
    fun i => hsP (hxP i), fun i => hsP (hyP i), hsP hzP, hmap, ?_, ?_⟩
  · intro i
    show (s⁻¹ * y i * s) ^ 3 = 1
    rw [show s⁻¹ * y i * s = f (y i) from (hf (y i)).symm, ← map_pow, hy3 i, map_one]
  · calc r * (s⁻¹ * x 0 * s) * r⁻¹
        = s⁻¹ * ((s * r * s⁻¹) * x 0 * (s * r * s⁻¹)⁻¹) * s := by group
      _ = s⁻¹ * (fi22ExtRep k * x 0 * (fi22ExtRep k)⁻¹) * s := by rw [hsr]
      _ = s⁻¹ * (x 0)⁻¹ * s := by rw [hinv]
      _ = (s⁻¹ * x 0 * s)⁻¹ := by group

private theorem m4_fi22_exists_heisCfg_subtype
    {r : Equiv.Perm (Fin 3510)} (hr : r ∈ fi22R) (hr2 : r * r = 1) (hr1 : r ≠ 1) :
    ∃ (x y : Fin 3 → ↥fi22P) (z : ↥fi22P), HeisCfg 3 3 x y z ∧ (∀ i, y i ^ 3 = 1) ∧
      r * (x 0 : Equiv.Perm (Fin 3510)) * r⁻¹ = (x 0 : Equiv.Perm (Fin 3510))⁻¹ := by
  obtain ⟨x, y, z, hxP, hyP, hzP, hcfg, hy3, hinv⟩ := fi22_involution_inverts_heis hr hr2 hr1
  refine ⟨fun i => ⟨x i, hxP i⟩, fun i => ⟨y i, hyP i⟩, ⟨z, hzP⟩, ?_, ?_, ?_⟩
  · refine HeisCfg.ofSubgroup fi22P (MonoidHom.id ↥fi22P) hxP hyP hzP hcfg ?_
    intro h
    exact hcfg.z1 (Subtype.ext_iff.mp h)
  · intro i
    exact Subtype.ext (by simpa using hy3 i)
  · simpa using hinv

@[expose] def W4Fi22RowM4CentreThree : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L → Nat.card (Subgroup.center ↥L) = 3 →
      IsSpor (↥L ⧸ Subgroup.center ↥L) .Fi22 → 4 ≤ E3.mParam Y

theorem w4Fi22RowM4CentreOne_holds :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (Y L : Subgroup (MulAut W)),
        L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
        IsQuasisimple ↥L → O2Trivial L → Nat.card (Subgroup.center ↥L) = 1 →
        IsSpor (↥L ⧸ Subgroup.center ↥L) .Fi22 → 4 ≤ E3.mParam Y := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hZ hs
  obtain ⟨e0⟩ := hs
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h2S : 2 ∣ Nat.card ↥fi22P := by rw [card_fi22P]; norm_num
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) := by rw [hZ]; norm_num
  have hρ : 2 * 4 < (3 - 1) * 3 ^ 2 * orderOf (2 : ZMod 3) + 2 := by
    rw [m4_orderOf_two_zmod_three]
    norm_num
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥fi22P := e0.trans fi22PermEquiv
  have hgen : ∀ t : ↥fi22P, t * t = 1 → t ≠ 1 →
      ∃ (x y : Fin 3 → ↥fi22P) (z : ↥fi22P),
        HeisCfg 3 3 x y z ∧ (∀ i, y i ^ 3 = 1) ∧ t * x 0 * t⁻¹ = (x 0)⁻¹ := by
    intro t ht2 ht1
    have htR : (t : Equiv.Perm (Fin 3510)) ∈ fi22R := fi22P_le_R t.2
    have ht2' : (t : Equiv.Perm (Fin 3510)) * (t : Equiv.Perm (Fin 3510)) = 1 := by
      simpa using congrArg Subtype.val ht2
    have ht1' : (t : Equiv.Perm (Fin 3510)) ≠ 1 := fun h => ht1 (Subtype.ext h)
    obtain ⟨x, y, z, hcfg, hy3, hinv⟩ :=
      m4_fi22_exists_heisCfg_subtype (r := (t : Equiv.Perm (Fin 3510))) htR ht2' ht1'
    exact ⟨x, y, z, hcfg, hy3, Subtype.ext (by simpa using hinv)⟩
  have hD : ∀ ψ : MulAut ↥fi22P, ψ ∉ (MulAut.conj : ↥fi22P →* MulAut ↥fi22P).range →
      ψ * ψ = 1 →
      ∃ (x y : Fin 3 → ↥fi22P) (z : ↥fi22P),
        HeisCfg 3 3 x y z ∧ (∀ i, y i ^ 3 = 1) ∧ ψ (x 0) = (x 0)⁻¹ := by
    intro ψ hψr hψ2
    obtain ⟨ρ', hρ'⟩ := fi22RAut.surjective ψ
    have hρ'2 : ρ' * ρ' = 1 := by
      apply fi22RAut.injective
      rw [map_mul, map_one, hρ', hψ2]
    have hρ'1 : ρ' ≠ 1 := by
      intro h
      exact hψr ⟨1, by rw [← hρ', h]; simp⟩
    have hρ'R : (ρ' : Equiv.Perm (Fin 3510)) ∈ fi22R := ρ'.2
    have hρ'2' : (ρ' : Equiv.Perm (Fin 3510)) * (ρ' : Equiv.Perm (Fin 3510)) = 1 := by
      simpa using congrArg Subtype.val hρ'2
    have hρ'1' : (ρ' : Equiv.Perm (Fin 3510)) ≠ 1 := fun h => hρ'1 (Subtype.ext h)
    obtain ⟨x, y, z, hcfg, hy3, hinv⟩ :=
      m4_fi22_exists_heisCfg_subtype (r := (ρ' : Equiv.Perm (Fin 3510))) hρ'R hρ'2' hρ'1'
    refine ⟨x, y, z, hcfg, hy3, ?_⟩
    rw [← hρ']
    apply Subtype.ext
    rw [fi22RAut_apply, fi22ConjHom_apply]
    exact hinv
  exact le_mParam_of_heisCfg_out2 (W := W) hW hLY hLn hF hq hO2 e h2S (p := 3) (n := 2)
    (ρ := 4) (by norm_num) hZ3 hρ hgen hD

theorem w4Thm11_1RowM4_Fi22_of_centre_three
    (h3 : W4Fi22RowM4CentreThree) : W4Thm11_1RowM4 .Fi22 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e0⟩ := hs
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := odd_card_center_of_o2Trivial hO2
  have hdvd : Nat.card (Subgroup.center ↥L) ∣ 6 :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.fi22_center_dvd ↥L hq ⟨e0⟩
  rcases CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.eq_one_or_three_of_odd_dvd_six
    hodd hdvd with h1 | h3'
  · exact w4Fi22RowM4CentreOne_holds W hW Y L hLY hLn hF hq hO2 h1 ⟨e0⟩
  · exact h3 W hW Y L hLY hLn hF hq hO2 h3' ⟨e0⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
