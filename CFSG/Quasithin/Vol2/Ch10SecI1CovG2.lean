module

public import CFSG.Quasithin.Vol2.Ch10SecI1CovNat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq

public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ASInputs.C10KH

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
open CFSG.Open (quasithinG2 quasithinZorn)

section Polar

variable {K : Type} [Field K]

theorem cayleyPolar_add_left (x y z : quasithinZorn K) :
    cayleyPolar (x + y) z = cayleyPolar x z + cayleyPolar y z := by
  simp only [cayleyPolar_eq, Fin.sum_univ_three, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

theorem cayleyPolar_add_right (x y z : quasithinZorn K) :
    cayleyPolar x (y + z) = cayleyPolar x y + cayleyPolar x z := by
  simp only [cayleyPolar_eq, Fin.sum_univ_three, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

theorem cayleyPolar_comm (x y : quasithinZorn K) : cayleyPolar x y = cayleyPolar y x := by
  simp only [cayleyPolar_eq, Fin.sum_univ_three]
  ring

theorem cayleyPolar_smul_right (x y : quasithinZorn K) (t : K) :
    cayleyPolar x (t • y) = t * cayleyPolar x y := by
  simp only [cayleyPolar_eq, Fin.sum_univ_three, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem cayleyPolar_cayleyGroup {g : quasithinZorn K ≃ₗ[K] quasithinZorn K}
    (hg : g ∈ cayleyGroup K) (x y : quasithinZorn K) :
    cayleyPolar (g x) (g y) = cayleyPolar x y := by
  have hN := hg.2.2.2
  rw [cayleyPolar, cayleyPolar, ← map_add, hN, hN, hN]

end Polar

section Pair

variable {K : Type} [Field K]

@[expose] def zornPair (ℓ : K →+ ZMod 2) (x y : Multiplicative (quasithinZorn K)) : ZMod 2 :=
  ℓ (cayleyPolar (Multiplicative.toAdd x) (Multiplicative.toAdd y))

theorem mem_zornO0 {x : Multiplicative (quasithinZorn K)} :
    x ∈ zornO0 K ↔ cayleyTr (Multiplicative.toAdd x) = 0 :=
  Iff.rfl

theorem zornPair_mul_left (ℓ : K →+ ZMod 2) (x y z : Multiplicative (quasithinZorn K)) :
    zornPair ℓ (x * y) z = zornPair ℓ x z + zornPair ℓ y z := by
  simp only [zornPair, toAdd_mul, cayleyPolar_add_left, map_add]

theorem zornPair_mul_right (ℓ : K →+ ZMod 2) (x y z : Multiplicative (quasithinZorn K)) :
    zornPair ℓ x (y * z) = zornPair ℓ x y + zornPair ℓ x z := by
  simp only [zornPair, toAdd_mul, cayleyPolar_add_right, map_add]

variable [CharP K 2]

theorem zornPair_radical {k y : Multiplicative (quasithinZorn K)} (hk : k ∈ zornR K)
    (hy : y ∈ zornO0 K) : cayleyPolar (Multiplicative.toAdd k) (Multiplicative.toAdd y) = 0 := by
  obtain ⟨c, hc⟩ := hk
  have htr : cayleyTr (Multiplicative.toAdd k) = 0 := by
    rw [hc, cayleyTr]
    exact CharTwo.add_self_eq_zero c
  exact (cayleyPolar_radical htr).mpr ⟨c, hc⟩ _ (mem_zornO0.mp hy)

theorem zornPair_secPairing (ℓ : K →+ ZMod 2)
    (Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)) :
    SecPairing (FFModel.zornQ Γ) (zornPair ℓ) where
  add_left := zornPair_mul_left ℓ
  add_right := zornPair_mul_right ℓ
  ker_left k hk y hy := by
    change ℓ (cayleyPolar (Multiplicative.toAdd (k : Multiplicative (quasithinZorn K)))
      (Multiplicative.toAdd (y : Multiplicative (quasithinZorn K)))) = 0
    rw [zornPair_radical hk hy, map_zero]
  ker_right x hx k hk := by
    change ℓ (cayleyPolar (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K)))
      (Multiplicative.toAdd (k : Multiplicative (quasithinZorn K)))) = 0
    rw [cayleyPolar_comm, zornPair_radical hk hx, map_zero]

theorem zornPair_nondeg {ℓ : K →+ ZMod 2} (hℓ : ℓ 1 = 1) {x : Multiplicative (quasithinZorn K)}
    (hx : x ∈ zornO0 K) (h : ∀ y ∈ zornO0 K, zornPair ℓ x y = 0) : x ∈ zornR K := by
  have h0 : ∀ y : quasithinZorn K, cayleyTr y = 0 →
      cayleyPolar (Multiplicative.toAdd x) y = 0 := by
    intro y hy
    by_contra hp
    have hty : Multiplicative.ofAdd ((cayleyPolar (Multiplicative.toAdd x) y)⁻¹ • y) ∈
        zornO0 K := by
      rw [mem_zornO0, toAdd_ofAdd, cayleyTr]
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ← mul_add]
      rw [← cayleyTr, hy, mul_zero]
    have h1 := h _ hty
    rw [zornPair, toAdd_ofAdd, cayleyPolar_smul_right, inv_mul_cancel₀ hp, hℓ] at h1
    exact one_ne_zero h1
  exact (cayleyPolar_radical (mem_zornO0.mp hx)).mp h0

end Pair

section G2Cover

variable {K : Type} [Field K] [CharP K 2]

theorem zornPair_invariant (ℓ : K →+ ZMod 2) (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆)
    (x y : Multiplicative (quasithinZorn K)) :
    zornPair ℓ (zornAct _ γ x) (zornAct _ γ y) = zornPair ℓ x y := by
  have hγ : (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈ cayleyGroup K := by
    rw [← CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
    exact Subgroup.commutator_le_self _ γ.2
  simp only [zornPair, zornAct, toAdd_ofAdd]
  rw [cayleyPolar_cayleyGroup hγ]

variable [Finite K] {W : Type} [CommGroup W] [Finite W]

theorem g2Cover_card_le (hW2 : ∀ w : W, w ^ 2 = 1) {Gm : Subgroup (MulAut W)} {Z : Subgroup W}
    (hZ : Z ≤ fixV Gm) (hcomm : commV Gm = ⊤)
    (hR : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Realizes Gm ⊤ Z) {d : ℕ}
    (hH1 : ∀ {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (ρ : Representation (ZMod 2) (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Gam M),
        (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).IsModel ρ →
          Module.finrank (ZMod 2) (H1 ρ) ≤ d) :
    Nat.card Z ≤ 2 ^ d := by
  obtain ⟨ℓ, hℓ⟩ := exists_addHom_one K
  have : Finite (quasithinZorn K ≃ₗ[K] quasithinZorn K) :=
    Finite.of_injective (fun e : quasithinZorn K ≃ₗ[K] quasithinZorn K =>
      (e : quasithinZorn K → quasithinZorn K)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have : Finite (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Gam :=
    inferInstanceAs (Finite ↥⁅quasithinG2 K, quasithinG2 K⁆)
  exact cover_card_le_of_form hW2 hZ hcomm hR
    (FFModel.zornQ_isActionModel _ (Subgroup.commutator_le_self _))
    (sec_sq_eq_one fun x => sq_eq_one_of_charTwo (K := K) (A := quasithinZorn K) x)
    (zornPair_secPairing ℓ _) (fun x hx h => zornPair_nondeg hℓ hx h)
    (fun γ x _ y _ => zornPair_invariant ℓ γ x y) hH1

end G2Cover

end CFSG.Quasithin.ASInputs.C10KH
