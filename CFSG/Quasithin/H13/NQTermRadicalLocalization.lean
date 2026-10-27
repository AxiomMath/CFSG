module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_mul (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  rfl

omit [Finite G] in
theorem isPGroup_iSup_of_eq_or_commute {ι : Type*} [Finite ι] {p : ℕ} (f : ι → Subgroup G)
    (hf : ∀ i, IsPGroup p (f i)) (hc : ∀ i j, f i ≠ f j → ⁅f i, f j⁆ = ⊥) :
    IsPGroup p ↥(⨆ i, f i) := by
  classical
  have := Fintype.ofFinite ι
  suffices h : ∀ s : Finset ι, IsPGroup p ↥(⨆ i ∈ s, f i) by
    have h1 : (⨆ i ∈ (Finset.univ : Finset ι), f i) = ⨆ i, f i :=
      le_antisymm (iSup₂_le fun i _ => le_iSup f i)
        (iSup_le fun i => le_biSup f (Finset.mem_univ i))
    exact h1 ▸ h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    have h1 : (⨆ i ∈ (∅ : Finset ι), f i) = ⊥ :=
      le_antisymm (iSup₂_le fun i hi => by simp at hi) bot_le
    rw [h1]
    exact IsPGroup.of_bot
  | insert a s ha ih =>
    rw [Finset.iSup_insert]
    by_cases hex : ∃ i ∈ s, f i = f a
    · obtain ⟨i, hi, hia⟩ := hex
      have hle : f a ≤ ⨆ i ∈ s, f i := hia ▸ le_biSup f hi
      rw [sup_eq_right.mpr hle]
      exact ih
    · push Not at hex
      refine (hf a).to_sup_of_normal_right' ih ?_
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      rw [Subgroup.le_centralizer_iff]
      refine iSup₂_le fun i hi => ?_
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hc i a (hex i hi))

theorem le_of_isPGroup_of_le_normalizer {p : ℕ} [Fact p.Prime] {S W : Subgroup G}
    (hS : IsPGroup p S) (hSO : S = pCoreOf p (normalizer (S : Set G))) (hW : IsPGroup p W)
    (hKW : normalizer (S : Set G) ≤ normalizer (W : Set G)) : W ≤ S := by
  have hSK : S ≤ normalizer (S : Set G) := Subgroup.le_normalizer
  have hWK : W ⊓ normalizer (S : Set G) ≤ S := by
    refine le_trans ?_ hSO.ge
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p inf_le_right (fun k hk => ?_)
      (hW.to_le inf_le_left)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hKW hk, Subgroup.le_normalizer hk⟩
  have hP : IsPGroup p ↥(S ⊔ W) := hS.to_sup_of_normal_right' hW (hSK.trans hKW)
  by_contra hWS
  have hne : S ≠ S ⊔ W := fun h => hWS (h ▸ le_sup_right)
  obtain ⟨x, hx, hxS⟩ := CFSG.QuasithinUnique.exists_mem_inf_normalizer_of_ne hP le_sup_left hne
  obtain ⟨hxSW, hxK⟩ := Subgroup.mem_inf.mp hx
  have hx' : x ∈ (S : Set G) * (W : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right S W (hSK.trans hKW)]
    exact hxSW
  obtain ⟨s, hs, w, hw, hsw⟩ := hx'
  have hsw' : s * w = x := hsw
  have hwK : w ∈ normalizer (S : Set G) := by
    have h1 : w = s⁻¹ * x := by rw [← hsw', inv_mul_cancel_left]
    rw [h1]
    exact mul_mem (inv_mem (hSK hs)) hxK
  apply hxS
  rw [← hsw']
  exact mul_mem hs (hWK (Subgroup.mem_inf.mpr ⟨hw, hwK⟩))

theorem le_of_le_of_normalizer_inf_le {p : ℕ} [Fact p.Prime] {S : Subgroup G}
    (hS : IsPGroup p S) (hSO : S = pCoreOf p (normalizer (S : Set G))) {Δ : Set (Subgroup G)}
    (hΔK : ∀ k ∈ normalizer (S : Set G), ∀ M ∈ Δ, M.map (MulAut.conj k).toMonoidHom ∈ Δ)
    (hΔc : ∀ L₁ ∈ Δ, ∀ L₂ ∈ Δ, L₁ ≠ L₂ → ⁅L₁, L₂⁆ = ⊥) {L : Subgroup G} (hL : L ∈ Δ)
    {U : Subgroup G} (hUL : U ≤ L) (hU : IsPGroup p U)
    (hUN : normalizer (S : Set G) ⊓ normalizer (L : Set G) ≤ normalizer (U : Set G)) : U ≤ S := by
  set K := normalizer (S : Set G) with hK
  let f : K → Subgroup G := fun k => U.map (MulAut.conj (k : G)).toMonoidHom
  have hfL : ∀ k : K, f k ≤ L.map (MulAut.conj (k : G)).toMonoidHom := fun k =>
    Subgroup.map_mono hUL
  have hc : ∀ i j : K, f i ≠ f j → ⁅f i, f j⁆ = ⊥ := by
    intro i j hij
    have hLij : L.map (MulAut.conj (i : G)).toMonoidHom ≠
        L.map (MulAut.conj (j : G)).toMonoidHom := by
      intro hL'
      apply hij
      have hn : (j : G)⁻¹ * i ∈ K ⊓ normalizer (L : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem j.2) i.2, ?_⟩
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        change L.map (MulAut.conj ((j : G)⁻¹ * i)).toMonoidHom = L
        rw [map_conj_mul, hL', ← map_conj_mul, inv_mul_cancel, map_one]
        exact Subgroup.map_id L
      have hUn : U.map (MulAut.conj ((j : G)⁻¹ * i)).toMonoidHom = U :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUN hn)
      change U.map (MulAut.conj (i : G)).toMonoidHom = U.map (MulAut.conj (j : G)).toMonoidHom
      rw [show (i : G) = j * ((j : G)⁻¹ * i) by group, map_conj_mul, hUn]
    have h := hΔc _ (hΔK i i.2 L hL) _ (hΔK j j.2 L hL) hLij
    exact le_bot_iff.mp (h ▸ Subgroup.commutator_mono (hfL i) (hfL j))
  have hW : IsPGroup p ↥(⨆ k, f k) :=
    isPGroup_iSup_of_eq_or_commute f (fun k => hU.map _) hc
  have hmap : ∀ y ∈ K, (⨆ k, f k).map (MulAut.conj y).toMonoidHom ≤ ⨆ k, f k := by
    intro y hy
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun k => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have h1 : (f k).map (MulAut.conj y).toMonoidHom = f ⟨y * k, mul_mem hy k.2⟩ := by
      change (U.map (MulAut.conj (k : G)).toMonoidHom).map (MulAut.conj y).toMonoidHom =
        U.map (MulAut.conj (y * k)).toMonoidHom
      rw [map_conj_mul]
    rw [h1]
    exact le_iSup f _
  have hKW : K ≤ normalizer ((⨆ k, f k : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (hmap y hy) fun w hw => ?_
    refine ⟨y⁻¹ * w * y, ?_, ?_⟩
    · have h1 : (MulAut.conj y⁻¹).toMonoidHom w ∈ ⨆ k, f k :=
        hmap y⁻¹ (inv_mem hy) ⟨w, hw, rfl⟩
      simpa [MulAut.conj_apply] using h1
    · show y * (y⁻¹ * w * y) * y⁻¹ = w
      group
  have hUW : U ≤ ⨆ k, f k := by
    have h1 : f 1 = U := by
      change U.map (MulAut.conj (1 : G)).toMonoidHom = U
      rw [map_one]
      exact Subgroup.map_id U
    exact h1 ▸ le_iSup f 1
  exact hUW.trans (le_of_isPGroup_of_le_normalizer hS hSO hW hKW)

theorem prime_radical_localization_on_commuting_orbits {p : ℕ} (hp : p.Prime) {S : Subgroup G}
    (hS : IsPGroup p S) (hSO : S = pCoreOf p (normalizer (S : Set G))) {Δ : Set (Subgroup G)}
    (hΔK : ∀ k ∈ normalizer (S : Set G), ∀ M ∈ Δ, M.map (MulAut.conj k).toMonoidHom ∈ Δ)
    (hΔc : ∀ L₁ ∈ Δ, ∀ L₂ ∈ Δ, L₁ ≠ L₂ → ⁅L₁, L₂⁆ = ⊥) {L : Subgroup G} (hL : L ∈ Δ) :
    (∀ U : Subgroup G, U ≤ L → IsPGroup p U →
      normalizer (S : Set G) ⊓ normalizer (L : Set G) ≤ normalizer (U : Set G) → U ≤ S) ∧
    S ⊓ L = pCoreOf p (L ⊓ normalizer (S : Set G)) ∧
    pCoreOf p (L ⊓ normalizer (S : Set G)) =
      pCoreOf p (L ⊓ normalizer ((S ⊓ L : Subgroup G) : Set G)) ∧
    ((L : Set G) * ((S ⊓ normalizer (L : Set G) : Subgroup G) : Set G) =
        ((L ⊔ (S ⊓ normalizer (L : Set G)) : Subgroup G) : Set G) ∧
      S ⊓ normalizer (L : Set G) = pCoreOf p ((L ⊔ (S ⊓ normalizer (L : Set G))) ⊓
        normalizer ((S ⊓ normalizer (L : Set G) : Subgroup G) : Set G))) := by
  have : Fact p.Prime := ⟨hp⟩
  set K := normalizer (S : Set G) with hK
  set NKL := K ⊓ normalizer (L : Set G) with hNKL
  have key : ∀ U : Subgroup G, U ≤ L → IsPGroup p U → NKL ≤ normalizer (U : Set G) → U ≤ S :=
    fun U hUL hU hUN => le_of_le_of_normalizer_inf_le hS hSO hΔK hΔc hL hUL hU hUN
  have hSK : S ≤ K := Subgroup.le_normalizer
  have hNKL_K : NKL ≤ normalizer (K : Set G) := fun n hn => Subgroup.le_normalizer hn.1
  have hNKL_L : NKL ≤ normalizer (L : Set G) := inf_le_right
  have hNKL_S : NKL ≤ normalizer (S : Set G) := inf_le_left
  have hNSL : NKL ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hNKL_S hn, hNKL_L hn⟩
  have hNY1 : NKL ≤ normalizer ((L ⊓ K : Subgroup G) : Set G) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hNKL_L hn, hNKL_K hn⟩
  have hNY2 : NKL ≤ normalizer ((L ⊓ normalizer ((S ⊓ L : Subgroup G) : Set G) : Subgroup G) :
      Set G) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hNKL_L hn, Subgroup.le_normalizer (hNSL hn)⟩
  have hSLp : IsPGroup p ↥(S ⊓ L) := hS.to_le inf_le_left
  have hcore_le : ∀ H : Subgroup G, pCoreOf p H ≤ H := fun H =>
    CFSG.LieType.BorelTits.pCoreOf_le p H
  have hcore_p : ∀ H : Subgroup G, IsPGroup p ↥(pCoreOf p H) := fun H =>
    CFSG.LieType.BorelTits.pCoreOf_isPGroup p H
  have hcore_n : ∀ H : Subgroup G, normalizer (H : Set G) ≤ normalizer (pCoreOf p H : Set G) :=
    fun H => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p H
  have h1 : S ⊓ L = pCoreOf p (L ⊓ K) := by
    apply le_antisymm
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
        (le_inf inf_le_right (inf_le_left.trans hSK))
        (fun n hn => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨(Subgroup.mem_inf.mp hn).2, Subgroup.le_normalizer (Subgroup.mem_inf.mp hn).1⟩) hSLp
    · exact le_inf (key _ ((hcore_le _).trans inf_le_left) (hcore_p _) (hNY1.trans (hcore_n _)))
        ((hcore_le _).trans inf_le_left)
  have h2 : S ⊓ L = pCoreOf p (L ⊓ normalizer ((S ⊓ L : Subgroup G) : Set G)) := by
    apply le_antisymm
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
        (le_inf inf_le_right Subgroup.le_normalizer) inf_le_right hSLp
    · exact le_inf (key _ ((hcore_le _).trans inf_le_left) (hcore_p _) (hNY2.trans (hcore_n _)))
        ((hcore_le _).trans inf_le_left)
  set R := S ⊓ normalizer (L : Set G) with hR
  have hRL : R ≤ normalizer (L : Set G) := inf_le_right
  have hLR : (L : Set G) * (R : Set G) = ((L ⊔ R : Subgroup G) : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left L R hRL).symm
  have hRp : IsPGroup p R := hS.to_le inf_le_left
  have hNR : NKL ≤ normalizer (R : Set G) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hNKL_S hn, Subgroup.le_normalizer (hNKL_L hn)⟩
  have hNLR : NKL ≤ normalizer ((L ⊔ R : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNKL_L hn),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNR hn)]
  set Y := (L ⊔ R) ⊓ normalizer (R : Set G) with hY
  have hNY : NKL ≤ normalizer (Y : Set G) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hNLR hn, Subgroup.le_normalizer (hNR hn)⟩
  have hRD : R ≤ pCoreOf p Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
      (le_inf le_sup_right Subgroup.le_normalizer) inf_le_right hRp
  have hDL : pCoreOf p Y ⊓ L ≤ S :=
    key _ inf_le_right ((hcore_p Y).to_le inf_le_left) fun n hn =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨(hNY.trans (hcore_n Y)) hn, hNKL_L hn⟩
  have h3 : R = pCoreOf p Y := by
    refine le_antisymm hRD fun d hd => ?_
    have hdY : d ∈ Y := hcore_le Y hd
    have hdLR : d ∈ (L : Set G) * (R : Set G) := by
      rw [hLR]
      exact (Subgroup.mem_inf.mp hdY).1
    obtain ⟨l, hl, r, hr, hlr⟩ := hdLR
    have hlr' : l * r = d := hlr
    have hlD : l ∈ pCoreOf p Y := by
      have hl' : l = d * r⁻¹ := by rw [← hlr', mul_inv_cancel_right]
      rw [hl']
      exact mul_mem hd (inv_mem (hRD hr))
    have hlS : l ∈ S := hDL (Subgroup.mem_inf.mpr ⟨hlD, hl⟩)
    have hlR : l ∈ R := Subgroup.mem_inf.mpr ⟨hlS, Subgroup.le_normalizer hl⟩
    rw [← hlr']
    exact mul_mem hlR hr
  exact ⟨key, h1, h1.symm.trans h2, hLR, h3⟩

end CFSG.Quasithin.H13.NQTerm
