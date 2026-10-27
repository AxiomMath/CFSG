module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporRu
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row18Common
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import Certificates.Certificate4215

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.Ch1.SporLat.Ru CFSG.QuasithinUnique.Ch1.SporLat.RuCert
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.Blueprint
  CFSG.Quasithin.S151S9T CFSG.Quasithin.E6.Spor
open CFSG.Sporadic.Ru.Native (ruData)

namespace Stellmacher.L3YC

section Row20Center

theorem ru_centralizer_z0 :
    ∃ z₀ : J ruData, orderOf z₀ = 2 ∧ centerOf ruCtx.S = Subgroup.zpowers z₀ ∧
      Nat.card (Subgroup.centralizer ({z₀} : Set (J ruData))) = 15 * 2 ^ 14 := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := ruCtx_centre
  refine ⟨z₀, hz2, hZ, ?_⟩
  have : FaithfulSMul (J ruData) (Fin ruData.n) :=
    faithfulSMul_of_base (base_lt ru_facts) (base_property ru_facts)
  have hsT : ruCtx.D.sTabs = ruSTabsL := ru_D_sTabs
  obtain ⟨-, hr, hnc⟩ := Certificates.certificate4215
  have hnc2 : ncChk ruData.n ruCtx.ta ruSLPL[154]! = true := hnc
  have hnc' := not_central_of_ncChk (n := ruData.n) ruCtx.ha hzT hnc2
  obtain ⟨us, uTabs, OH, y, x, hus, hucomm, hOH, hOHm, -⟩ :=
    rChk_sound ruCtx hsT hzT (r := 5) (m := 15) (by norm_num) hr
  have hk : ruCtx.k = 14 := rfl
  have hHcard := card_gen hus hOH
  rw [hOHm, hk] at hHcard
  have hHle := genOver_le_centralizer ruCtx hZ hucomm
  have hne : Subgroup.centralizer ({z₀} : Set (J ruData)) ≠ ⊤ := fun h => hnc' fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (h ▸ Subgroup.mem_top g)
  have hSC : ruCtx.S ≤ Subgroup.centralizer ({z₀} : Set (J ruData)) :=
    (S_le_genOver ruCtx us).trans hHle
  obtain ⟨j, hj5, hCj⟩ := ru_complete _ hSC
  have hj : j < 5 := by
    rcases Nat.lt_or_ge j 5 with h | h
    · exact h
    · exfalso
      have : j = 5 := by omega
      subst this
      exact hne (by simpa [memberOrTop] using hCj)
  have hm : memberOrTop 5 ruCtx.Y j = ruCtx.Y j := by simp [memberOrTop, hj]
  rw [hm] at hCj
  have hdvd : 15 * 2 ^ 14 ∣ Nat.card (Subgroup.centralizer ({z₀} : Set (J ruData))) := by
    rw [← hHcard]
    exact Subgroup.card_dvd_of_le hHle
  rw [hCj, ru_member_card j hj] at hdvd ⊢
  interval_cases j <;> simp at hdvd ⊢

theorem ru_pCore_lt
    {j : ℕ} (hj : j < 5)
    (hj0 : j ≠ 0) : Nat.card (pCoreOf 2 (ruCtx.Y j)) < 2 ^ 14 := by
  obtain ⟨m, hm, h1, h2, -⟩ := ru_row j hj
  have hc := ru_member_card j hj
  rw [h2]
  interval_cases j
  · exact absurd rfl hj0
  all_goals
    simp only [ruMems, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp at hc h1 ⊢; all_goals omega

theorem ru_center_trivial_J
    {B : Subgroup (J ruData)} (hSB : ruCtx.S ≤ B) (hB : Nat.card B = 2 ^ 14 * 21) {z : J ruData}
    (hzB : z ∈ B) (hz : ∀ b ∈ B, z * b = b * z) : z = 1 := by
  obtain ⟨z₀, hz2, hZ, hC⟩ := ru_centralizer_z0
  have hzc : z ∈ Subgroup.centralizer (ruCtx.S : Set (J ruData)) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => (hz h (hSB hh)).symm
  have hzS : z ∈ ruCtx.S := by
    set K : Subgroup (J ruData) := ruCtx.S ⊔ Subgroup.zpowers z with hK
    have hzK : z ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    have hKB : K ≤ B := sup_le hSB ((Subgroup.zpowers_le).mpr hzB)
    have hKn : K ≤ Subgroup.normalizer (ruCtx.S : Set (J ruData)) :=
      sup_le Subgroup.le_normalizer
        ((Subgroup.zpowers_le).mpr (Subgroup.centralizer_le_normalizer _ hzc))
    have hKne : K ≠ ⊤ := fun h => by
      have := Subgroup.card_le_of_le (h ▸ hKB : (⊤ : Subgroup (J ruData)) ≤ B)
      rw [Subgroup.card_top, ru_card, hB] at this
      omega
    obtain ⟨j, hj5, hKj⟩ := ru_complete K le_sup_left
    have hj : j < 5 := by
      rcases Nat.lt_or_ge j 5 with h | h
      · exact h
      · exfalso
        have : j = 5 := by omega
        subst this
        exact hKne (by simpa [memberOrTop] using hKj)
    have hm : memberOrTop 5 ruCtx.Y j = ruCtx.Y j := by simp [memberOrTop, hj]
    rw [hm] at hKj
    by_cases hj0 : j = 0
    · subst hj0
      rw [ruCtx.Y_zero] at hKj
      exact hKj ▸ hzK
    · exfalso
      have hle : ruCtx.S ≤ pCoreOf 2 K :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_left hKn ruCtx.S_isPGroup
      have := Subgroup.card_le_of_le hle
      rw [hKj, ru_card_S] at this
      have := ru_pCore_lt hj hj0
      omega
  have hzZ : z ∈ centerOf ruCtx.S := Subgroup.mem_inf.mpr ⟨hzS, hzc⟩
  rw [hZ] at hzZ
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzZ
  have hmod := zpow_mod_orderOf z₀ i
  rw [hz2] at hmod
  rcases Int.emod_two_eq_zero_or_one i with h | h
  · rw [← hmod]
    simp [h]
  · exfalso
    have hz1 : z₀ ^ i = z₀ := by
      rw [← hmod]
      simp [h]
    have hBC : B ≤ Subgroup.centralizer ({z₀} : Set (J ruData)) := fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← hz1]; exact (hz b hb).symm)
    have := Subgroup.card_le_of_le hBC
    rw [hB, hC] at this
    omega

theorem exists_iso_sylow_eq {X Γ : Type} [Group X] [Group Γ] [Finite Γ] (e : X ≃* Γ)
    {T : Subgroup X} {S : Subgroup Γ} (hT : IsSylowTwoOf T ⊤) (hS : IsSylowTwoOf S ⊤) :
    ∃ ψ : X ≃* Γ, T.map ψ.toMonoidHom = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' := isSylowTwoOf_map e hT
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT'
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S = (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg
    exact this.symm
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hST, Subgroup.map_map]
  rfl

theorem center_trivial_of_sylow_lattice {X Γ : Type} [Group X] [Group Γ] [Finite Γ]
    {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) {N : ℕ}
    (hJ : ∀ B : Subgroup Γ, S ≤ B → Nat.card B = N → ∀ z ∈ B, (∀ b ∈ B, z * b = b * z) → z = 1)
    (hX : Nonempty (X ≃* Γ)) {T B : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTB : T ≤ B)
    (hB : Nat.card B = N) {z : X} (hzB : z ∈ B) (hz : ∀ b ∈ B, z * b = b * z) : z = 1 := by
  obtain ⟨e⟩ := hX
  obtain ⟨ψ, hψ⟩ := exists_iso_sylow_eq e hT hS
  have hSB : S ≤ B.map ψ.toMonoidHom := by
    rw [← hψ]
    exact Subgroup.map_mono hTB
  have hBc : Nat.card (B.map ψ.toMonoidHom) = N := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hB
  have h1 := hJ _ hSB hBc (ψ z) ⟨z, hzB, rfl⟩ (by
    rintro _ ⟨b, hb, rfl⟩
    show ψ z * ψ b = ψ b * ψ z
    rw [← map_mul, ← map_mul, hz b hb])
  exact ψ.injective (by rw [h1, map_one])

theorem nonempty_equiv_J_ru {X : Type} [Group X]
    (hX : Nonempty (X ≃* NativeSporadic.Carrier .Ru)) : Nonempty (X ≃* J ruData) := by
  obtain ⟨e⟩ := hX
  exact ⟨e.trans (seedEquiv ru_facts.toBaseFacts)⟩

theorem card_of_equiv_Ru {X : Type} [Group X]
    (hX : Nonempty (X ≃* NativeSporadic.Carrier .Ru)) : Nat.card X = 2 ^ 14 * 8906625 := by
  obtain ⟨e⟩ := nonempty_equiv_J_ru hX
  rw [Nat.card_congr e.toEquiv]
  exact ru_card

theorem ru_center_trivial
    {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* NativeSporadic.Carrier .Ru))
    {T B : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTB : T ≤ B) (hB : Nat.card B = 2 ^ 14 * 21)
    {z : X} (hzB : z ∈ B) (hz : ∀ b ∈ B, z * b = b * z) : z = 1 :=
  center_trivial_of_sylow_lattice ru_S_sylow
    (fun _ hSB hB' _ hzB' hz' => ru_center_trivial_J hSB hB' hzB' hz')
    (nonempty_equiv_J_ru hX) hT hTB hB hzB hz

theorem row20_center_trivial
    {K : Type} [Group K] [Finite K] {N Lb S₀ : Subgroup K}
    (hN : Nonempty (↥N ≃* NativeSporadic.Carrier .Ru)) (hS₀ : IsSylowTwoOf S₀ N) (hLN : Lb ≤ N)
    (hS₀L : S₀ ≤ Lb) (hLc : Nat.card Lb = 2 ^ 14 * 21) {z : K} (hzL : z ∈ Lb)
    (hz : ∀ b ∈ Lb, z * b = b * z) : z = 1 := by
  have hT := isSylowTwoOf_top_subgroupOf hS₀
  have hTB : S₀.subgroupOf N ≤ Lb.subgroupOf N := fun x hx => hS₀L hx
  have hBc : Nat.card (Lb.subgroupOf N) = 2 ^ 14 * 21 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv]
    exact hLc
  have := ru_center_trivial hN hT hTB hBc (z := ⟨z, hLN hzL⟩) hzL (fun b hb =>
    Subtype.ext (hz b.1 hb))
  exact congrArg Subtype.val this

end Row20Center

end Stellmacher.L3YC

end CFSG.Quasithin
