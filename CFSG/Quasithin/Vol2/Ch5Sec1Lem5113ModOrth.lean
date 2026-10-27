module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Mod
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113DMinus
public import CFSG.Quasithin.Vol2.Ch5Sec1BorelTorus

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem le_normalizer_oThreePrimeResidual (X : Subgroup G) :
    X ≤ Subgroup.normalizer (oThreePrimeResidual X : Set G) := by
  rw [oThreePrimeResidual, Subgroup.le_normalizer_closure_iff]
  rintro c hc g ⟨hg, k, hk⟩
  refine Subgroup.subset_closure ⟨X.mul_mem (X.mul_mem hc hg) (X.inv_mem hc), k, ?_⟩
  rw [conj_pow, hk, mul_one, mul_inv_cancel]

theorem stmt5_1_13_mod_orth_of (h513 : Stmt5_1_3) (h432 : Stmt4_3_2) : Stmt5_1_13_mod_orth := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hty hX k hk2 hVo
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hN := m.nota
  have hV := m.module
  set Z := quasithinOmegaOneCenter T with hZdef
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) := Main513.T_le_centralizer_omega T
  have hTX : T ≤ X := hX ▸ hTZ
  have hKh₁X : Kh₁ ≤ X := A3.subnormal_le m.hat.1.2.2.1
  have hKhX : conjClosure Kh₁ T ≤ X := conjClosure_le fun t ht y hy =>
    X.mul_mem (X.mul_mem (hTX ht) (hKh₁X hy)) (X.inv_mem (hTX ht))
  obtain ⟨-, hKhres, D₃, hD₃, hD₃3, -, hDKh, t, htTK, htinv⟩ := id hty
  obtain ⟨d, hdD₃, hd1⟩ : ∃ d ∈ D₃, d ≠ 1 := by
    by_contra hall
    push Not at hall
    have hb : D₃ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hall x hx)
    rw [hb, Subgroup.card_bot] at hD₃3
    omega
  have hdL : d ∈ L := (hN.2.1.1 (hD₃ hdD₃).1).1
  have hd3 : d ^ 3 = 1 := by
    have := orderOf_dvd_natCard (⟨d, hdD₃⟩ : ↥D₃)
    rw [hD₃3, Subgroup.orderOf_mk] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hdZ : d ∈ Subgroup.centralizer (Z : Set G) := by
    have := hKhX (hD₃ hdD₃).2
    rw [hX] at this
    exact this
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hKT : oTwoUpper H ⊔ T = H := by
    rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hTH
  have hKZ : oTwoUpper H ≤ Subgroup.centralizer (Z : Set G) :=
    (m.lt.le.trans hKhX).trans hX.le
  have hHZ : H ≤ Subgroup.centralizer (Z : Set G) := hKT ▸ sup_le hKZ hTZ
  have hZL := m.inf_centralizer_eq_bot h432 hHZ
  have hred := hV.isTwoReducedIn
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hS := h.isSylowTwoOf_inf
  have hD := hN.2.1
  have hCV : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T :=
    (h.setting516 hD hV).sup_inf_centralizer_le hred.2.1 fun hle => hV.2.2
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle))
  obtain ⟨F, _, _, _, hF, ψ, -, -, -, -, -, hP⟩ := hVo.exists_sylowCoord hS
  have hn : n = 2 * k := by
    have h1 := (h.isCyclic_card_of_isHall l2TorusFact hD).2
    have h2 := card_hall_eq_card_units hLV ψ hP hCV hS hD
    rw [Nat.card_units, hF, h1] at h2
    have h3 : 2 ^ n = 2 ^ (2 * k) := by
      have := Nat.one_le_two_pow (n := n)
      have := Nat.one_le_two_pow (n := 2 * k)
      omega
    exact Nat.pow_right_injective le_rfl h3
  have hn2 : n ≠ 2 := by omega
  set R := reducedAggregate (L ⊔ T) with hRdef
  have hR : IsCh5Module T L R := hV.isCh5Module_reducedAggregate
  have hredR := hR.isTwoReducedIn
  have hRel : IsElemAbelian 2 R := hredR.2.2.1
  have hRT : R ≤ T := h.V_le_T hR
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := le_sup_right.trans hredR.2.1
  have hRne : R ≠ ⊥ := fun hb => hR.2.2 (by rw [hb]; exact Subgroup.commutator_bot_left L)
  rcases h513 G T M L R n h hR with ⟨W₁, W₂, hL₁, hL₂, hdisj, hsup, hW₁, hW₂⟩ |
    ⟨hn2', -, -⟩ | h3 | h4 | ⟨-, h5', -⟩
  ·
    obtain ⟨z, hzR, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hRel le_rfl hRT hTR hRne
    have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
      hRel.1.is_comm.comm ⟨a, hsup ▸ Subgroup.mem_sup_left ha⟩
        ⟨b, hsup ▸ Subgroup.mem_sup_right hb⟩ |> congrArg Subtype.val
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm (hsup.symm ▸ hzR)
    have hfix : d * (a * b) * d⁻¹ = a * b := by
      rw [← Subgroup.mem_centralizer_iff.mp hdZ (a * b) hzZ, mul_inv_cancel_right]
    have hda : d * a * d⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hL₁ hdL) a).mp ha
    have hdb : d * b * d⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (hL₂ hdL) b).mp hb
    have hab := eq_of_mul_eq hdisj hda ha hdb hb
      (by rw [← hfix]; group)
    by_cases ha1 : a = 1
    · have hb1 : b ≠ 1 := fun hb1 => hz1 (by rw [ha1, hb1, mul_one])
      exact h.conj_ne_of_isNatModCh5 hW₂ hdL hd3 hd1 hb hb1 hab.2
    · exact h.conj_ne_of_isNatModCh5 hW₁ hdL hd3 hd1 ha ha1 hab.1
  · exact hn2 hn2'
  ·
    set N := ⁅R, L⁆ with hNdef
    have hLR : L ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hredR.2.1
    have hNR : N ≤ R := Subgroup.le_normalizer_iff_commutator_le_left.mp hLR
    have hTN : T ≤ Subgroup.normalizer (N : Set G) :=
      le_normalizer_commutator_of hTR h.T_le_normalizer
    obtain ⟨F', _, _, _, -, ψ', Y', hc⟩ := h3.exists_qcoord hS
    have hNL : ⁅N, L⁆ ≠ ⊥ := fun hb =>
      hc.not_le_centralizer (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb))
    have hCL := h.inf_centralizer_le hc.le_normalizer hNL
    have hNne : N ≠ ⊥ := hR.2.2
    obtain ⟨z, hzN, hz1, hzZ⟩ :=
      exists_mem_omegaOneCenter hT2 hRel hNR hRT hTN hNne
    have hzC : z ∉ Subgroup.centralizer (L : Set G) := fun hzC => hz1 (by
      have hmem : z ∈ Z ⊓ Subgroup.centralizer (L : Set G) := ⟨hzZ, hzC⟩
      rwa [hZL, Subgroup.mem_bot] at hmem)
    have hY : Y' ⟨z, hzN⟩ ≠ 1 := fun hY => hzC ((hc.ker _).mp hY)
    have hfix : d * z * d⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hdZ z hzZ, mul_inv_cancel_right]
    exact hd1 (hc.eq_one_of_fix_three hCL hdL hd3 hY hfix)
  ·
    obtain ⟨Dm, hDmD, hDmc⟩ := exists_dMinus hLV ψ hP hF hCV hS hD
    have hker := orthKernelFact G L R (T ⊓ L) Dm k (hn ▸ h4) hS (hDmD.trans hD.1) hDmc
    have hZC := h.omega_le_inf_centralizer
    have hDmZ : Dm ≤ Subgroup.centralizer (Z : Set G) := fun x hx => by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (hker (hZC hz)) x hx).symm
    have hXK : X ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) := by
      rw [hKhres]
      exact le_normalizer_oThreePrimeResidual X
    have hle := le_one_of_dMinus hLV ψ hP hF h.T_le_normalizer hTV hCV hS hD hDmD hDmc
      htTK.1 (hD₃ hdD₃).1 hd1 hd3 (htinv d hdD₃) htTK.2 ((hX ▸ hDmZ).trans hXK)
      ((inf_le_left.trans hTX).trans hXK) hDKh hD₃3
    omega
  ·
    exact hn2 (h.n_eq_two_of_isBarS5 hR h5')

theorem stmt5_1_13_mod_of_inputs (h513 : Stmt5_1_3) (h432 : Stmt4_3_2) : Stmt5_1_13_mod :=
  stmt5_1_13_mod_of h513 h432 (stmt5_1_13_mod_orth_of h513 h432)

end CFSG.Quasithin.H13
