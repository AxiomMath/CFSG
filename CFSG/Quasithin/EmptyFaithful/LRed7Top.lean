module

public import CFSG.Quasithin.EmptyFaithful.LRed7Zorn
public import CFSG.Quasithin.Background.FFC2G2

public section

namespace CFSG.Quasithin.LRed7

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open


theorem g2FixBound : LRed6.G2FixBound := by
  intro K _ _ hK Wm hWO hRW hcard
  classical
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  let ZH : Multiplicative (quasithinZorn K) →* Multiplicative (quasithinZorn (ZMod 2)) :=
    { toFun := fun x => Multiplicative.ofAdd (zornMap ε (Multiplicative.toAdd x))
      map_one' := by
        show Multiplicative.ofAdd (zornMap ε (0 : quasithinZorn K)) = 1
        have h0 : zornMap ε (0 : quasithinZorn K) = 0 := by
          simp [zornMap]
          rfl
        rw [h0]
        rfl
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (zornMap ε (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
        rw [zornMap_add]
        rfl }
  have hZH : ∀ x, ZH x = Multiplicative.ofAdd (zornMap ε (Multiplicative.toAdd x)) := fun x => rfl
  have hZHinj : Function.Injective ZH := by
    intro x y h
    have h1 : zornMap ε (Multiplicative.toAdd x) = zornMap ε (Multiplicative.toAdd y) :=
      Multiplicative.ofAdd.injective h
    have h2 := congrArg (zornMap ε.symm) h1
    rw [zornMap_symm_apply, zornMap_symm_apply] at h2
    exact Multiplicative.toAdd.injective h2
  have hZHR : ∀ r ∈ zornR K, ZH r ∈ zornR (ZMod 2) := by
    rintro r ⟨c, hc⟩
    refine ⟨ε c, ?_⟩
    rw [hZH, hc]
    simp [zornMap]
    rfl
  set Wm' : Subgroup (Multiplicative (quasithinZorn (ZMod 2))) := Wm.map ZH with hWm'
  have hWO' : Wm' ≤ zornO0 (ZMod 2) := by
    rintro _ ⟨m, hm, rfl⟩
    have h1 : cayleyTr (Multiplicative.toAdd m) = 0 := hWO hm
    show cayleyTr (zornMap ε (Multiplicative.toAdd m)) = 0
    rw [cayleyTr_zornMap, h1, map_zero]
  have hRW' : zornR (ZMod 2) ≤ Wm' := by
    rintro r' ⟨c', hc'⟩
    have h1 : zornMap ε (ε.symm c', 0, 0, ε.symm c') = (c', 0, 0, c') := by
      simp [zornMap]
      rfl
    refine ⟨Multiplicative.ofAdd (ε.symm c', 0, 0, ε.symm c'), hRW ⟨ε.symm c', rfl⟩, ?_⟩
    rw [hZH, toAdd_ofAdd, h1, ← hc', ofAdd_toAdd]
  have hcard' : Nat.card Wm' = 32 := by
    rw [hWm', Subgroup.card_map_of_injective hZHinj, hcard]
  have hbound := g2FixBound_two Wm' hWO' hRW' hcard'
  have hG : quasithinG2 K = cayleyGroup K := CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup
  have hG2 : quasithinG2 (ZMod 2) = cayleyGroup (ZMod 2) :=
    CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup
  have hcomm : (⁅quasithinG2 K, quasithinG2 K⁆).map (zornConj ε : (quasithinZorn K ≃ₗ[K] quasithinZorn K) →*
      (quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2))) =
      ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := by
    rw [hG, hG2]
    exact map_cayley_commutator ε
  have hfin : Finite (quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) :=
    Finite.of_injective (fun f : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2) =>
      (f : quasithinZorn (ZMod 2) → quasithinZorn (ZMod 2))) (fun f g h => LinearEquiv.ext (congrFun h))
  refine le_trans (Nat.card_le_card_of_injective
    (fun γ => (⟨⟨zornConj ε γ.1.1, hcomm ▸ Subgroup.mem_map_of_mem _ γ.1.2⟩, ?_⟩ :
      {γ : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ //
        ∀ m ∈ Wm', zornAct ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ γ m * m⁻¹ ∈
          zornR (ZMod 2)})) ?_) hbound
  · intro m' hm'
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hm'
    have hact : zornAct ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆
        ⟨zornConj ε γ.1.1, hcomm ▸ Subgroup.mem_map_of_mem _ γ.1.2⟩ (ZH m) =
        ZH (zornAct ⁅quasithinG2 K, quasithinG2 K⁆ γ.1 m) := by
      show Multiplicative.ofAdd ((zornConj ε γ.1.1 : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2]
        quasithinZorn (ZMod 2)) (zornMap ε (Multiplicative.toAdd m))) =
          Multiplicative.ofAdd (zornMap ε ((γ.1.1 : quasithinZorn K ≃ₗ[K] quasithinZorn K)
            (Multiplicative.toAdd m)))
      rw [zornConj_apply, zornMap_symm_apply]
    rw [hact, ← map_inv, ← map_mul]
    exact hZHR _ (γ.2 m hm)
  · intro a b hab
    have h1 := congrArg (fun x : {γ : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ //
      ∀ m ∈ Wm', zornAct ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ γ m * m⁻¹ ∈
        zornR (ZMod 2)} => (x.1.1 : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2))) hab
    have h2 : a.1.1 = b.1.1 := (zornConj ε).injective h1
    exact Subtype.ext (Subtype.ext h2)

end CFSG.Quasithin.LRed7
