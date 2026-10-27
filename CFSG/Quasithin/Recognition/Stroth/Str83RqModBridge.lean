module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
import CFSG.Quasithin.Recognition.Stroth.Str83RqMod
import CFSG.Quasithin.Recognition.St84.Gen.L2SecDim
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.Quasithin.H13.NFa2
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem r8mb_exists_irreducible_SL2_rep {L Z : Subgroup G} {f : ℕ}
    (hL2 : IsL2Quot f (oTwoQuot ↥L)) (hsec : SecHyp L ⊥ Z) (hchief : IsChiefPair L ⊥ Z)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W]
    (s : SecRep L ⊥ Z W) (hkerP : CFSG.pCore 2 ↥L ≤ s.ρ.ker) :
    ∃ ρ : Representation (ZMod 2) SL(2, GaloisField 2 f) W,
      ρ.IsIrreducible ∧ ∃ ψ : ↥L →* SL(2, GaloisField 2 f),
        Function.Surjective ψ ∧ ∀ l, ρ (ψ l) = (s.ρ l).toLinearMap := by
  classical
  obtain ⟨e⟩ := hL2
  let eSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f) ≃*
      SL(2, GaloisField 2 f) := CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 f)
  let q : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let bar : oTwoQuot ↥L →* (W ≃ₗ[ZMod 2] W) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) s.ρ hkerP
  let Φ : SL(2, GaloisField 2 f) →* (W ≃ₗ[ZMod 2] W) :=
    bar.comp (e.symm.toMonoidHom.comp eSL.symm.toMonoidHom)
  let ρSL : Representation (ZMod 2) SL(2, GaloisField 2 f) W :=
    { toFun := fun g => (Φ g).toLinearMap
      map_one' := by rw [map_one]; rfl
      map_mul' := fun g h => by rw [map_mul]; rfl }
  have hΦ_mk : ∀ l : ↥L, Φ (eSL (e (q l))) = s.ρ l := by
    intro l
    simp [Φ, bar, q, QuotientGroup.lift_mk']
  have hρSL_mk : ∀ l : ↥L, ρSL (eSL (e (q l))) = (s.ρ l).toLinearMap := by
    intro l
    rw [show ρSL (eSL (e (q l))) = (Φ (eSL (e (q l)))).toLinearMap from rfl, hΦ_mk l]
  haveI : Nontrivial (Subrepresentation ρSL) := by
    refine ⟨⊥, ⊤, ?_⟩
    intro h
    exact bot_ne_top (α := Submodule (ZMod 2) W)
      (congrArg Subrepresentation.toSubmodule h)
  have hirrSL : ρSL.IsIrreducible := by
    refine { eq_bot_or_eq_top := fun U => ?_ }
    have hS : ∀ l : ↥L, ∀ w ∈ U.toSubmodule, s.ρ l w ∈ U.toSubmodule := by
      intro l w hw
      have h1 := U.apply_mem_toSubmodule (eSL (e (q l))) hw
      rwa [hρSL_mk l] at h1
    rcases SecRep.irreducible hchief hsec s U.toSubmodule hS with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  exact ⟨ρSL, hirrSL, eSL.toMonoidHom.comp (e.toMonoidHom.comp q),
    eSL.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _)), hρSL_mk⟩

theorem exists_odd_inf_centralizer_eq_bot_of_isL2Quot {L Z : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (hL : IsL2Quot f (oTwoQuot ↥L)) (hLZ : L ≤ normalizer (Z : Set G))
    (hZc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hZ2 : ∀ x ∈ Z, x ^ 2 = 1)
    (hcard : Nat.card Z = (2 ^ f) ^ 2)
    (hirr : ∀ U : Subgroup G, U ≤ Z → L ≤ normalizer (U : Set G) → U = ⊥ ∨ U = Z) :
    ∃ w ∈ L, Odd (orderOf w) ∧ Z ⊓ centralizer ({w} : Set G) = ⊥ := by
  classical
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have h1 : (2 ^ f) * (2 ^ f) = 1 := by
      rw [← sq, ← hcard, hbot, Subgroup.card_bot]
    have hge : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmul : 2 * 2 ≤ (2 ^ f) * (2 ^ f) := Nat.mul_le_mul hge hge
    omega
  have hsec : SecHyp L ⊥ Z :=
    { le := bot_le
      norm₀ := fun x _ => Subgroup.mem_normalizer_iff.mpr (fun y => by simp)
      norm₁ := hLZ
      normal := fun x _ => Subgroup.mem_normalizer_iff.mpr (fun y => by simp)
      comm := fun a ha b hb => by
        rw [Subgroup.mem_bot]
        have h : a * b = b * a := hZc a ha b hb
        rw [h]
        group
      sq := fun a ha => by
        rw [Subgroup.mem_bot]
        simpa [sq] using hZ2 a ha }
  have hchief : IsChiefPair L ⊥ Z :=
    { lt := bot_lt_iff_ne_bot.mpr hZne
      norm₀ := fun x _ => Subgroup.mem_normalizer_iff.mpr (fun y => by simp)
      norm₁ := hLZ
      normal := fun x _ => Subgroup.mem_normalizer_iff.mpr (fun y => by simp)
      min := fun N _ hNZ hLN => hirr N hNZ hLN }
  obtain ⟨W, hWadd, hWmod, hWfin, ⟨s⟩⟩ := exists_secRep hsec
  letI : AddCommGroup W := hWadd
  letI : Module (ZMod 2) W := hWmod
  letI : Finite W := hWfin
  have hcl_inj : Function.Injective s.cls := fun a b hab => by
    have h1 : s.cls (a * b⁻¹) = 1 := by rw [map_mul, hab, map_inv, mul_inv_cancel]
    have h2 := (s.ker (a * b⁻¹)).mp h1
    exact Subtype.ext (mul_inv_eq_one.mp (by simpa using h2))
  have hWcard : Nat.card W = 2 ^ (2 * f) := by
    let eZW : ↥Z ≃* Multiplicative W := MulEquiv.ofBijective s.cls ⟨hcl_inj, s.surj⟩
    have h1 : Nat.card Z = Nat.card W := Nat.card_congr eZW.toEquiv
    rw [← h1, hcard, sq, ← pow_add]
    congr 1
    ring
  haveI : Nontrivial W :=
    Finite.one_lt_card_iff_nontrivial.mp
      (by rw [hWcard]; exact Nat.one_lt_pow (by omega) (by norm_num))
  obtain ⟨ρ, hirrρ, ψ, hψsurj, hψeq⟩ :=
    r8mb_exists_irreducible_SL2_rep hL hsec hchief s
      (CFSG.Quasithin.St84.pCore_le_secRep_ker s hsec hchief)
  obtain ⟨g, hgord⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := GaloisField 2 f)
  letI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hFintype : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 f (by omega)
  have hgord' : orderOf g = 2 ^ f + 1 := by
    rw [hgord, GaloisField.card 2 f (by omega)]
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hgord'
    have hle : 1 ≤ 2 ^ f := Nat.one_le_pow' f 1
    omega
  have hgpow : g ^ (2 ^ f + 1) = 1 := by
    rw [← hgord']
    exact pow_orderOf_eq_one g
  obtain ⟨ℓ, hℓ⟩ := hψsurj g
  have hℓne : orderOf ℓ ≠ 0 := (orderOf_pos ℓ).ne'
  obtain ⟨e, m, hm_odd, hℓord⟩ := Nat.exists_eq_two_pow_mul_odd hℓne
  let wL : ↥L := ℓ ^ 2 ^ e
  have hwL_ord : orderOf wL = m := by
    rw [show wL = ℓ ^ 2 ^ e from rfl,
      orderOf_pow_of_dvd (pow_pos (by norm_num) e).ne'
        (by rw [hℓord]; exact dvd_mul_right _ _), hℓord]
    exact Nat.mul_div_cancel_left m (pow_pos (by norm_num) e)
  have hψwL : ψ wL = g ^ 2 ^ e := by rw [show wL = ℓ ^ 2 ^ e from rfl, map_pow, hℓ]
  have hodd2f : Odd (2 ^ f + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hcop : Nat.Coprime (orderOf g) (2 ^ e) := by
    rw [hgord']
    exact Nat.Coprime.pow_right e hodd2f.coprime_two_right
  have hψw_ord : orderOf (ψ wL) = 2 ^ f + 1 := by
    rw [hψwL, hcop.orderOf_pow, hgord']
  have hψw_ne : ψ wL ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hψw_ord
    have hle : 1 ≤ 2 ^ f := Nat.one_le_pow' f 1
    omega
  have hψw_pow : (ψ wL) ^ (2 ^ f + 1) = 1 := by
    rw [← hψw_ord]
    exact pow_orderOf_eq_one _
  refine ⟨(wL : G), wL.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hwL_ord]
    exact hm_odd
  · rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzZ : z ∈ Z := hz.1
    have hcomm : (wL : G) * z * (wL : G)⁻¹ = z := by
      have h1 : (wL : G) * z = z * (wL : G) :=
        (Subgroup.mem_centralizer_iff.mp hz.2) (wL : G) (by simp)
      rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    have hfixed : ρ (ψ wL) (SecRep.cl s ⟨z, hzZ⟩) = SecRep.cl s ⟨z, hzZ⟩ := by
      rw [hψeq wL]
      change s.ρ wL (SecRep.cl s ⟨z, hzZ⟩) = SecRep.cl s ⟨z, hzZ⟩
      exact s.act wL ⟨z, hzZ⟩ ⟨z, hzZ⟩ hcomm.symm
    have hzero : SecRep.cl s ⟨z, hzZ⟩ = 0 :=
      eq_zero_of_fixed_of_pow_two_pow_succ (n := f) hFintype ρ hirrρ hWcard hψw_ne
        hψw_pow hfixed
    have hz1 : z = 1 := by
      have := (SecRep.cl_eq_zero_iff s ⟨z, hzZ⟩).mp hzero
      simpa using this
    exact hz1

end CFSG.Quasithin.Stroth.Rq

end
