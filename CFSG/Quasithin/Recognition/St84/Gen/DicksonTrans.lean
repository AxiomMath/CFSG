module

public import CFSG.Quasithin.Recognition.St84.L2Facts

import CFSG.Quasithin.Recognition.St84.EdgeStabB
import CFSG.Quasithin.Recognition.St84.Gen.DicksonGen

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open
open scoped MatrixGroups

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace IsLocL2

variable {v : V} {n : ℕ} {N : Subgroup G}

private theorem images_ne_of_fixes (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 3 ≤ n)
    {A B : Subgroup G} (hAN : A ≤ N) (hBN : B ≤ N) {a b : V}
    (ha : Γ.Adj v a) (hb : Γ.Adj v b) (hab : a ≠ b)
    (hAa : ∀ x ∈ A, x • a = a) (hBb : ∀ x ∈ B, x • b = b)
    (hAc : 2 ^ (n - 1) ≤ (pCoreOf 2 (MulAction.stabilizer G v)).relIndex A)
    (hBQ : ¬ B ≤ pCoreOf 2 (MulAction.stabilizer G v))
    {P P' : Sylow 2 (PSL(2, GaloisField 2 n))}
    (hAP : (A.subgroupOf N).map hN.phi ≤ P)
    (hBP : (B.subgroupOf N).map hN.phi ≤ P') :
    P ≠ P' := by
  classical
  have hn1 : 1 ≤ n := by omega
  intro hPP'
  have hBP' : (B.subgroupOf N).map hN.phi ≤ P := hPP'.symm ▸ hBP
  have hrange : P ≤ hN.phi.range := by
    rw [MonoidHom.range_eq_top.mpr hN.phi_surjective]
    exact le_top
  let S : Sylow 2 N := P.comapOfKerIsPGroup hN.phi hN.phi_ker_isPGroup hrange
  have hScoe : (S : Subgroup N) = P.comap hN.phi :=
    Sylow.coe_comapOfKerIsPGroup P hN.phi hN.phi_ker_isPGroup hrange
  have hAne : ¬ A ≤ pCoreOf 2 (MulAction.stabilizer G v) := by
    intro hle
    have h1 : (pCoreOf 2 (MulAction.stabilizer G v)).relIndex A = 1 :=
      Subgroup.relIndex_eq_one.mpr hle
    rw [h1] at hAc
    have h4 : 4 ≤ 2 ^ (n - 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨x, hxA, hxQ⟩ := Set.not_subset.mp hAne
  obtain ⟨y, hyB, hyQ⟩ := Set.not_subset.mp hBQ
  have hxN : x ∈ N := hAN hxA
  have hyN : y ∈ N := hBN hyB
  have hxS : (⟨x, hxN⟩ : N) ∈ (S : Subgroup N) := by
    rw [hScoe]
    exact Subgroup.mem_comap.mpr
      (hAP (Subgroup.mem_map_of_mem hN.phi (Subgroup.mem_subgroupOf.mpr hxA)))
  have hyS : (⟨y, hyN⟩ : N) ∈ (S : Subgroup N) := by
    rw [hScoe]
    exact Subgroup.mem_comap.mpr
      (hBP' (Subgroup.mem_map_of_mem hN.phi (Subgroup.mem_subgroupOf.mpr hyB)))
  obtain ⟨e, ⟨he_adj, he_fix⟩, _he_uniq⟩ :=
    hN.sylow_fixes_unique hadj hfin hcard hn1 S
  have hxe : x • e = e := he_fix ⟨x, hxN⟩ hxS
  have hye : y • e = e := he_fix ⟨y, hyN⟩ hyS
  have hae : a = e := by
    obtain ⟨u, _, hu_uniq⟩ :=
      hN.fixes_unique_of_mem_sylow_not_pcore hadj hfin hcard hn1 S hxS hxQ
    exact (hu_uniq a ⟨ha, hAa x hxA⟩).trans (hu_uniq e ⟨he_adj, hxe⟩).symm
  have hbe : b = e := by
    obtain ⟨u, _, hu_uniq⟩ :=
      hN.fixes_unique_of_mem_sylow_not_pcore hadj hfin hcard hn1 S hyS hyQ
    exact (hu_uniq b ⟨hb, hBb y hyB⟩).trans (hu_uniq e ⟨he_adj, hye⟩).symm
  exact hab (hae.trans hbe.symm)

theorem transitive_of_two_pGroups (hN : IsLocL2 Γ G v n N)
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 3 ≤ n)
    {H A B : Subgroup G} (hAH : A ≤ H) (hBH : B ≤ H) (hAN : A ≤ N) (hBN : B ≤ N)
    (hA2 : IsPGroup 2 A) (hB2 : IsPGroup 2 B) {a b : V}
    (ha : Γ.Adj v a) (hb : Γ.Adj v b) (hab : a ≠ b)
    (hAa : ∀ x ∈ A, x • a = a) (hBb : ∀ x ∈ B, x • b = b)
    (hAc : 2 ^ (n - 1) ≤ (pCoreOf 2 (MulAction.stabilizer G v)).relIndex A)
    (hBQ : ¬ B ≤ pCoreOf 2 (MulAction.stabilizer G v)) {c d : V}
    (hc : Γ.Adj v c) (hd : Γ.Adj v d) :
    ∃ h ∈ H ⊓ N, h • c = d := by
  classical
  have hn1 : 1 ≤ n := by omega
  let Qv := pCoreOf 2 (MulAction.stabilizer G v)
  let Abar := (A.subgroupOf N).map hN.phi
  let Bbar := (B.subgroupOf N).map hN.phi
  let Hbar := (H.subgroupOf N).map hN.phi
  have hker : MonoidHom.ker hN.phi = Qv.subgroupOf N := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hN.phi_ker y
  have hA2sub : IsPGroup 2 (A.subgroupOf N) :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAN).symm
  have hB2sub : IsPGroup 2 (B.subgroupOf N) :=
    hB2.of_equiv (Subgroup.subgroupOfEquivOfLe hBN).symm
  have hA2bar : IsPGroup 2 Abar := hA2sub.map hN.phi
  have hB2bar : IsPGroup 2 Bbar := hB2sub.map hN.phi
  have hAcard : Nat.card Abar = Qv.relIndex A := by
    rw [show Abar = (A.subgroupOf N).map hN.phi from rfl]
    rw [← Subgroup.relIndex_ker (K := A.subgroupOf N) hN.phi, hker,
      Subgroup.relIndex_subgroupOf hAN]
  obtain ⟨P, hAP⟩ := hA2bar.exists_le_sylow
  obtain ⟨P', hBP⟩ := hB2bar.exists_le_sylow
  have hAHbar : Abar ≤ Hbar := by
    show (A.subgroupOf N).map hN.phi ≤ (H.subgroupOf N).map hN.phi
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono N hAH)
  have hBHbar : Bbar ≤ Hbar := by
    show (B.subgroupOf N).map hN.phi ≤ (H.subgroupOf N).map hN.phi
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono N hBH)
  have hB1 : Bbar ≠ ⊥ := by
    intro hbot
    apply hBQ
    intro b hb
    have hbN : b ∈ N := hBN hb
    have hmem : hN.phi (⟨b, hbN⟩ : N) ∈ Bbar :=
      Subgroup.mem_map_of_mem hN.phi (Subgroup.mem_subgroupOf.mpr hb)
    rw [hbot] at hmem
    exact (hN.phi_ker ⟨b, hbN⟩).mp (Subgroup.mem_bot.mp hmem)
  have hPP' : P ≠ P' :=
    images_ne_of_fixes hN hadj hfin hcard hn hAN hBN ha hb hab hAa hBb hAc hBQ hAP hBP
  have hHbar_top : Hbar = ⊤ := by
    apply psl2_eq_top_of_sylow_ne hn hPP' hAP hBP hAHbar hBHbar
    · rw [hAcard]
      exact hAc
    · exact hB1
  obtain ⟨g, hgN, hgc⟩ := hN.trans c d hc hd
  have hmem : hN.phi (⟨g, hgN⟩ : N) ∈ Hbar := by
    rw [hHbar_top]
    exact Subgroup.mem_top _
  obtain ⟨y, hyH, hyphi⟩ := Subgroup.mem_map.mp hmem
  refine ⟨(y : G), ⟨Subgroup.mem_subgroupOf.mp hyH, y.2⟩, ?_⟩
  have hkerQ : ((y⁻¹ * ⟨g, hgN⟩ : N) : G) ∈ Qv := by
    refine (hN.phi_ker (y⁻¹ * ⟨g, hgN⟩)).mp ?_
    rw [map_mul, map_inv, hyphi, inv_mul_cancel]
  have hfix : ((y : G)⁻¹ * g) • c = c := by
    have h := hN.Q_fixes_neighbors hadj hfin hcard hn1 c hc
      ((y⁻¹ * ⟨g, hgN⟩ : N) : G) hkerQ
    simpa using h
  have h2 : (y : G) • c = g • c := by
    calc (y : G) • c = (y : G) • (((y : G)⁻¹ * g) • c) := by rw [hfix]
      _ = ((y : G) * ((y : G)⁻¹ * g)) • c := (mul_smul _ _ _).symm
      _ = g • c := by rw [mul_inv_cancel_left]
  exact h2.trans hgc

end IsLocL2

namespace Setup

variable (X : Setup Γ G)

theorem transitive_of_two_pGroups (j : ℤ) (hn : 3 ≤ X.n j)
    {H A B : Subgroup G} (hAH : A ≤ H) (hBH : B ≤ H) (hAL : A ≤ X.L j)
    (hBL : B ≤ X.L j) (hA2 : IsPGroup 2 A) (hB2 : IsPGroup 2 B)
    (hAa : A ≤ X.Gi (j - 1)) (hBb : B ≤ X.Gi (j + 1))
    (hAc : 2 ^ (X.n j - 1) ≤ (X.Q j).relIndex A) (hBQ : ¬ B ≤ X.Q j) {c d : V}
    (hc : Γ.Adj (X.vert j) c) (hd : Γ.Adj (X.vert j) d) :
    ∃ h ∈ H ⊓ X.L j, h • c = d := by
  have hleft : Γ.Adj (X.vert j) (X.vert (j - 1)) := by
    have h := (X.adj (j - 1)).symm
    rwa [show j - 1 + 1 = j by omega] at h
  have hne : X.vert (j - 1) ≠ X.vert (j + 1) := by
    intro h
    have := X.vert_injective h
    omega
  have hN : IsLocL2 Γ G (X.vert j) (X.n j) (X.L j) := X.hyp.isLocL2_oTwoPrime (X.vert j)
  exact IsLocL2.transitive_of_two_pGroups hN X.hyp.adj_smul
    (X.hyp.finite_stab (X.vert j)) (X.hyp.valency (X.vert j)).2 hn hAH hBH hAL hBL
    hA2 hB2 hleft (X.adj j) hne
    (fun x hx => MulAction.mem_stabilizer_iff.mp (hAa hx))
    (fun x hx => MulAction.mem_stabilizer_iff.mp (hBb hx))
    (by simpa [Setup.Q, Setup.Gi] using hAc)
    (by simpa [Setup.Q, Setup.Gi] using hBQ) hc hd

end Setup

end CFSG.Quasithin.St84
