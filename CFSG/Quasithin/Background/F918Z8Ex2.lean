module

public import CFSG.Quasithin.Background.F918Z8Ex2a
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

theorem d321x_inner {W : Type} [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    {L S : Subgroup (MulAut W)} {U Z V : Subgroup W} (hZU : Z ≤ U)
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) (hf : L ⊓ centSec U Z = ⊥)
    (hpsl : IsPSL 3 2 1 ↥L)
    (hds : DirectSumOfCopies L U Z (FFModel.nat (StatedSL 3 (ZMod 2))) 4)
    (hVU : V ≤ U) (hVinv : ∀ l ∈ L, ∀ v ∈ V, l v ∈ V) (hVZ : ¬ V ≤ Z)
    (hVirr : ∀ X : Subgroup W, X ≤ V → (∀ l ∈ L, ∀ x ∈ X, l x ∈ X) → V ⊓ Z ≤ X →
      X = V ⊓ Z ∨ X = V)
    (hSN : S ≤ Subgroup.normalizer (L : Set (MulAut W))) (hSU : S ≤ stabSub U)
    (hSZ : S ≤ stabSub Z) (hSV : S ≤ stabSub V) :
    ∀ a ∈ S, ∃ b ∈ L, ∀ l ∈ L, a * l * a⁻¹ = b * l * b⁻¹ := by
  have _ := hexp
  have _ := hZU
  have _ := hLU
  have _ := hf
  have _ := hpsl
  have _ := hSU
  obtain ⟨I, π, -, hind, hsum, hreal⟩ := hds
  have hZinv : ∀ l ∈ L, ∀ z ∈ Z, l z ∈ Z := fun l hl z hz => (hLZ hl z).2 hz
  obtain ⟨i, hi⟩ := d321i_exists_secIsoL hreal hZinv hind hsum hVU hVinv hVZ hVirr
  have hVreal : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia L V (V ⊓ Z) π :=
    d321i_realizesVia_of_secIsoL (hreal i) hi
  intro a ha
  have hσL : ∀ x ∈ L, a * x * a⁻¹ ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hSN ha) x).1 hx
  have hVmap : V.map a.toMonoidHom = V := map_eq_of_mem_stabSub (hSV ha)
  have hVZmap : (V ⊓ Z).map a.toMonoidHom = V ⊓ Z :=
    map_eq_of_mem_stabSub fun u => by
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hSV ha u, hSZ ha u]
  have hiso : SecIsoL L (V.map a.toMonoidHom) ((V ⊓ Z).map a.toMonoidHom) V (V ⊓ Z) := by
    rw [hVmap, hVZmap]
    exact B5.secIsoL_refl hVinv (fun l hl z hz => ⟨hVinv l hl z hz.1, hZinv l hl z hz.2⟩)
      inf_le_left
  obtain ⟨l₀, hl₀, hc⟩ :=
    exists_inner_of_twist_sl3 (F := ZMod 2) (by simp) hVreal hσL rfl rfl hiso
  refine ⟨l₀, hl₀, fun l hl => ?_⟩
  have h := hc _ (L.mul_mem (L.mul_mem hl₀ hl) (L.inv_mem hl₀))
  calc a * l * a⁻¹
      = (a * l₀⁻¹) * (l₀ * l * l₀⁻¹) * (a * l₀⁻¹)⁻¹ := by group
    _ = (l₀ * l * l₀⁻¹) * (a * l₀⁻¹) * (a * l₀⁻¹)⁻¹ := by rw [h]
    _ = l₀ * l * l₀⁻¹ := by group

end CFSG.Quasithin
