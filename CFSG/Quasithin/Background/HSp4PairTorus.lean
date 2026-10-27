module

public import CFSG.Quasithin.Background.HSp4PairNPrime
public import CFSG.Quasithin.Background.HSp4Bridge
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix PairG CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent borelSubgroup diagHom
  ker_diagHom torus_le_borelSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (normalizer_unipotent)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open scoped Matrix Pointwise

variable {K : Type} [Field K]

theorem exists_torus_mul {b : StatedSp 2 K} (hb : b ∈ borelSubgroup 2 K) :
    ∃ t : Fin 2 → Kˣ, ∃ u ∈ unipotent 2 K, b = SymplecticTorusWeyl.torusHom t * u := by
  set bb : borelSubgroup 2 K := ⟨b, hb⟩ with hbb
  set t := diagHom 2 K bb with ht
  have hd : SymplecticTorusWeyl.torusHom t ∈ borelSubgroup 2 K :=
    torus_le_borelSubgroup ⟨t, rfl⟩
  set dd : borelSubgroup 2 K := ⟨_, hd⟩ with hdd
  have hdt : diagHom 2 K dd = t := by
    funext i
    apply Units.ext
    simp [dd, diagHom, SymplecticFlag.diagEntry, SymplecticTorusWeyl.coe_torusHom]
  have hu : dd⁻¹ * bb ∈ (diagHom 2 K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdt, inv_mul_cancel]
  rw [ker_diagHom, Subgroup.mem_subgroupOf] at hu
  refine ⟨t, _, hu, ?_⟩
  change b = SymplecticTorusWeyl.torusHom t * ((SymplecticTorusWeyl.torusHom t)⁻¹ * b)
  group

variable [Finite K] [CharP K 2]

theorem le_nPrime {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hX1 : pairSp K ≤ X)
    (hX2 : X ≤ pairNormSp K) : n ≤ E3.nPrime X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) := MulEquiv.finite_left
  set ρ := pairHom (StatedSp 2 K) tauSp with hρ
  have hρrange : ρ.range = pairSp K := rfl
  obtain ⟨P₀, hP₀⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 2
  set U₀ := (unipotent 2 K).map ρ with hU₀
  have hU₀L : U₀ ≤ pairSp K := by
    rw [← hρrange]
    exact Subgroup.map_le_range _ _
  have hU₀p : IsPGroup 2 U₀ := by
    rw [hU₀, ← hP₀]
    exact P₀.isPGroup'.map _
  obtain ⟨S, hS, hUS⟩ := exists_isSylowIn_ge 2 (hU₀L.trans hX1) hU₀p
  have hSU : S ⊓ pairSp K = U₀ := by
    refine le_antisymm (fun x hx => ?_) (le_inf hUS hU₀L)
    obtain ⟨g, rfl⟩ := hx.2
    have hQ : IsPGroup 2 ((S ⊓ pairSp K).comap ρ) :=
      hS.isPGroup.to_inf_left.comap_of_injective _ pairHom_injective
    have hle : (P₀ : Subgroup ↥(StatedSp 2 K)) ≤ (S ⊓ pairSp K).comap ρ := by
      rw [hP₀]
      intro u hu
      exact ⟨hUS ⟨u, hu, rfl⟩, ⟨u, rfl⟩⟩
    have heq := P₀.is_maximal' hQ hle
    have hg : g ∈ (S ⊓ pairSp K).comap ρ := hx
    rw [heq, hP₀] at hg
    exact ⟨g, hg, rfl⟩
  have hSN : ∀ s ∈ S, s ∈ Subgroup.normalizer (U₀ : Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) := by
    intro s hs
    rw [← hSU, Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hs) x,
      Subgroup.mem_normalizer_iff.mp (hX2 (hS.le hs)) x]
  set B := (ρ.comp SymplecticTorusWeyl.torusHom).range with hB
  have hSB : (S : Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) * B ⊆ B * S := by
    rintro _ ⟨s, hs, _, ⟨p, rfl⟩, rfl⟩
    have h1 : s * ρ (SymplecticTorusWeyl.torusHom p) * s⁻¹ ∈ pairSp K :=
      (Subgroup.mem_normalizer_iff.mp (hX2 (hS.le hs)) _).mp ⟨_, rfl⟩
    obtain ⟨b, hb⟩ := h1
    have hbN : ρ b ∈ Subgroup.normalizer (U₀ : Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) := by
      rw [hb]
      have htN : ρ (SymplecticTorusWeyl.torusHom p) ∈
          Subgroup.normalizer (U₀ : Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) := by
        apply Subgroup.le_normalizer_map
        refine ⟨SymplecticTorusWeyl.torusHom p, ?_, rfl⟩
        rw [SetLike.mem_coe, normalizer_unipotent]
        exact torus_le_borelSubgroup ⟨p, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hSN s hs) htN)
        (Subgroup.inv_mem _ (hSN s hs))
    have hbU : b ∈ borelSubgroup 2 K := by
      rw [← normalizer_unipotent, Subgroup.mem_normalizer_iff]
      intro u
      have h2 := Subgroup.mem_normalizer_iff.mp hbN (ρ u)
      rw [Subgroup.mem_map_iff_mem pairHom_injective, ← map_inv, ← map_mul, ← map_mul,
        Subgroup.mem_map_iff_mem pairHom_injective] at h2
      exact h2
    obtain ⟨p', u, hu, hbe⟩ := exists_torus_mul hbU
    refine ⟨ρ (SymplecticTorusWeyl.torusHom p'), ⟨p', rfl⟩, ρ u * s,
      S.mul_mem (hUS ⟨u, hu, rfl⟩) hs, ?_⟩
    change ρ (SymplecticTorusWeyl.torusHom p') * (ρ u * s) =
      s * ρ (SymplecticTorusWeyl.torusHom p)
    rw [← mul_assoc, ← map_mul, ← hbe, hb]
    group
  have hBS : (B : Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) * S = S * B :=
    SL3Pair.mul_comm_of_subset hSB
  have hBX : B ≤ X := by
    refine le_trans ?_ hX1
    rw [hB, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm p q]
  have hq : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hBodd : Odd (Nat.card B) := by
    have hinj : Function.Injective (ρ.comp SymplecticTorusWeyl.torusHom) :=
      pairHom_injective.comp SymplecticTorusWeyl.torusHom_injective
    rw [hB, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi,
      Fin.prod_univ_two, Nat.card_units, hK]
    exact hq.mul hq
  let δ : Kˣ →* (Fin 2 → Kˣ) := MonoidHom.mulSingle (fun _ => Kˣ) 0
  set φ : Kˣ →* MulAut (PairMod (Fin 2 ⊕ Fin 2) K) :=
    ρ.comp (SymplecticTorusWeyl.torusHom.comp δ) with hφ
  have hδ : Function.Injective δ := fun a b h => by
    have h0 := congrFun h 0
    simpa [δ] using h0
  have hφi : Function.Injective φ :=
    pairHom_injective.comp (SymplecticTorusWeyl.torusHom_injective.comp hδ)
  have hYB : φ.range ≤ B := by
    rintro _ ⟨t, rfl⟩
    exact ⟨δ t, rfl⟩
  have hYc : Nat.card φ.range = 2 ^ n - 1 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφi).toEquiv, Nat.card_units, hK]
  have hYcyc : IsCyclic φ.range :=
    isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  exact E3.le_nPrime hYB hBX hYcyc hYc hBab hBodd hS hBS

theorem nPrime_eq {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hX1 : pairSp K ≤ X)
    (hX2 : X ≤ pairNormSp K) : E3.nPrime X = n :=
  le_antisymm (nPrime_le hn hK hX1 hX2) (le_nPrime (by omega) hK hX1 hX2)

omit [Finite K] [CharP K 2] in
theorem H7_Sp4Pair_nPrime {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} {n : ℕ} (hn : 2 ≤ n) (hreal : BinaryNaturalSp4 H V₁ ⊥ n) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) (hHM : H ≤ M)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) : E3.nPrime M = n := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ n) hK
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have h1 : pairSp K ≤ M.map (congrHom e) := he ▸ Subgroup.map_mono hHM
  have h2 := map_le_pairNormSp e he hMN
  rw [← nPrime_map_congrHom e M]
  exact nPrime_eq hn hK h1 h2

end Sp4

end H

end CFSG.Quasithin
