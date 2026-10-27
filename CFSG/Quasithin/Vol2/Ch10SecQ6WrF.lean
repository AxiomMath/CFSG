module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrW
public import CFSG.Quasithin.Background.E3Basic
public import CFSG.Quasithin.Vol2.Ch10SecQ6WrA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

theorem aParam_le_one_of {W : Type*} [CommGroup W] {X : Subgroup (MulAut W)}
    (h : E3.aSet 2 X = ∅) : E3.aParam X ≤ 1 := by
  unfold E3.aParam
  split_ifs
  · apply csSup_le'
    rintro k ⟨-, A, hA⟩
    by_contra hk1
    have hA2 : A ∈ E3.aSet 2 X := E3.aSet_anti (by omega) X hA
    rw [h] at hA2
    exact hA2
  · norm_num

variable {W : Type*} [CommGroup W]

theorem false_of_hypFix (hW : ∀ w : W, w ^ 2 = 1) {ρ : SymFiveWrTwo →* MulAut W}
    (hρ : Function.Injective ρ) {c : W} (hc : c ∈ fixV (Y0.map ρ)) {V : AddSubgroup PMod}
    (hV : ∀ g : SymFiveWrTwo, ∀ v ∈ V, gP g v ∈ V)
    (hirr : ∀ K : AddSubgroup PMod, K ≤ V → (∀ g : SymFiveWrTwo, ∀ k ∈ K, gP g k ∈ K) →
      K ≠ ⊥ → V ≤ K)
    (hne : ∃ m ∈ V, Phi ρ c m ≠ 1) {A : Subgroup (MulAut W)} (hAρ : A ≤ ρ.range)
    (hfix : ∀ B : Subgroup (MulAut W), B ≤ A → E3.mQuot A B < 2 → fixV B = fixV A)
    (hH : HypFix V (A.comap ρ)) : False := by
  obtain ⟨B', hB'A, ⟨x, hxA, hxB, hcov⟩, m, hmV, hmfix, a, haA, ham⟩ := hH
  have hB : (B'.map ρ).relIndex A = 2 := by
    refine relIndex_eq_two_of_cover hxA (fun h => hxB ?_) fun g hg => ?_
    · obtain ⟨b, hb, hbx⟩ := h
      rwa [← hρ hbx]
    · obtain ⟨g', rfl⟩ := hAρ hg
      rcases hcov g' hg with h | h
      · exact Or.inl ⟨g', h, rfl⟩
      · exact Or.inr ⟨g' * x, h, map_mul ρ g' x⟩
  have hmq : E3.mQuot A (B'.map ρ) < 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    unfold E3.mQuot
    rw [hB, padicValNat_self]
    norm_num
  have hBA : B'.map ρ ≤ A := by
    rintro _ ⟨b, hb, rfl⟩
    exact hB'A hb
  have hPhi : Phi ρ c m ∈ fixV (B'.map ρ) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Phi_gP ρ hc, hmfix b hb]
  rw [hfix _ hBA hmq] at hPhi
  have h1 := hPhi (ρ a) haA
  rw [Phi_gP ρ hc] at h1
  exact ham (Phi_inj ρ hW hc hV hirr hne (hV a m hmV) hmV h1)

theorem rep_four : rep (4, 4) = 1 :=
  RegularWreathProduct.ext (funext fun q => by
    change (if q = 1 then swap (4 : Fin 5) 4 else swap 4 4) = 1
    rw [swap_self]
    split_ifs <;> rfl) rfl

theorem exists_Phi_ne (hW : ∀ w : W, w ^ 2 = 1) {ρ : SymFiveWrTwo →* MulAut W}
    (hρ : Function.Injective ρ)
    (hgen : (⨆ h : SymFiveWrTwo, (fixV (Y0.map ρ)).map (ρ h).toMonoidHom) = ⊤) :
    ∃ c ∈ fixV (Y0.map ρ), (∃ m ∈ Mcl, Phi ρ c m ≠ 1) ∨ (∃ n ∈ Ncl, Phi ρ c n ≠ 1) := by
  by_contra hno
  push Not at hno
  let F : Subgroup W :=
    { carrier := {w | ρ wrT w = w}
      one_mem' := map_one _
      mul_mem' := fun {a b} ha hb => by
        change ρ wrT (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        change ρ wrT a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hle : (⨆ h : SymFiveWrTwo, (fixV (Y0.map ρ)).map (ρ h).toMonoidHom) ≤ F := by
    refine iSup_le fun h => ?_
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hM, hN⟩ := hno c hc
    have h1 : ρ h c = Phi ρ c (fun _ _ => 1) := by
      rw [← mul_one h, ← rep_four, rho_mul_rep ρ hc, ← Phi_delta, delta_eq, Phi_add ρ hW,
        Phi_add ρ hW, hN _ (Rv_mem_Ncl _), hM _ (Tv_mem_Mcl _), one_mul, one_mul]
    change ρ wrT (ρ h c) = ρ h c
    rw [h1, Phi_gP ρ hc, gP_const]
  rw [hgen] at hle
  have hT : ρ wrT = 1 := MulEquiv.ext fun w => hle (Subgroup.mem_top w)
  have h1 := hρ (hT.trans (map_one ρ).symm)
  exact zs_ne_one (congrArg RegularWreathProduct.right h1)

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
