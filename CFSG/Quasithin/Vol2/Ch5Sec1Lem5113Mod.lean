module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Steps
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Cases
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QW
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped MatrixGroups

@[expose] def Stmt5_1_13_mod_orth : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    X = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    ∀ m : ℕ, 2 ≤ m → IsOrthCh5 L V (2 * m) → False

section Fix

variable {G : Type} [Group G]

theorem QCoord.eq_one_of_fix_three [Finite G] {L N S : Subgroup G} {F : Type} [Field F]
    [CharP F 2] {ψ : ↥(autOn L N) ≃* SL(2, F)} {Y : ↥N →* Multiplicative (Fin 2 → F)}
    (hc : QCoord L N S F ψ Y) (hCL : L ⊓ Subgroup.centralizer (N : Set G) ≤ pCoreOf 2 L)
    {d : G} (hd : d ∈ L) (hd3 : d ^ 3 = 1) {x : ↥N} (hx : Y x ≠ 1)
    (hfix : d * x * d⁻¹ = x) : d = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a := autHom hc.le_normalizer ⟨d, hd⟩ with ha
  have hax : ((a : ↥(autOn L N)) : MulAut ↥N) x = x :=
    Subtype.ext (by rw [ha, autHom_apply_coe]; exact hfix)
  have hAv : ((ψ a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (Y x)) =
      Multiplicative.toAdd (Y x) := by
    rw [ha, ← hc.toAdd_Y_conj hd x, ← ha, hax]
  have hv : Multiplicative.toAdd (Y x) ≠ 0 := fun h0 => hx (by simpa using h0)
  have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hA2 : ψ a * ψ a = 1 :=
    Subtype.ext (sl2_mul_self_eq_one_of_fix h2F _ (ψ a).2 hv hAv)
  have hA3 : ψ a ^ 3 = 1 := by
    rw [← map_pow, ha, ← map_pow]
    have hd3' : (⟨d, hd⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [hd3', map_one, map_one]
  have hA1 : ψ a = 1 := by
    have e : ψ a ^ 3 = ψ a * (ψ a * ψ a) := by rw [pow_succ', sq]
    rw [e, hA2, mul_one] at hA3
    exact hA3
  have hone : a = 1 := ψ.injective (by rw [hA1, map_one])
  have hdC := mem_centralizer_of_autHom_eq_one hc.le_normalizer hone
  exact eq_one_of_mem_of_pow_three (pCoreOf_isPGroup 2 L) (hCL ⟨hd, hdC⟩) hd3

end Fix

namespace Main513

variable {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem T_le_centralizer_omega (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_inf T hz).2 t ht).symm

theorem inf_centralizer_eq_bot (h432 : Stmt4_3_2) (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (hHZ : H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  obtain ⟨huniq, -⟩ := h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le
    h.maximal h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩
  set Y := quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) with hY
  by_contra hne
  have hY2 : IsPGroup 2 Y :=
    h.sylow.1.to_le (inf_le_left.trans (quasithinOmegaOneCenter_le_self T))
  have hloc : IsTwoLocal (Subgroup.normalizer (Y : Set G)) := ⟨Y, hne, hY2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
    refine le_trans (fun l hl => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp hy.2 l hl).symm
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := by
    refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (hHZ hx) y hy.1
  have hM'eq : M' = M := huniq M' hM' (hLY.trans hle)
  exact m.hyp.hStar.2.1 (hM'eq ▸ hHY.trans hle)

end Main513

theorem stmt5_1_13_mod_of (h513 : Stmt5_1_3) (h432 : Stmt4_3_2)
    (horth : Stmt5_1_13_mod_orth) : Stmt5_1_13_mod := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hty hX
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
  obtain ⟨-, -, D₃, hD₃, hD₃3, -, -⟩ := id hty
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
  have hVel : IsElemAbelian 2 V := hred.2.2.1
  have hVT : V ≤ T := h.V_le_T hV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hVne : V ≠ ⊥ := fun hb => hV.2.2 (by rw [hb]; exact Subgroup.commutator_bot_left L)
  have hS := h.isSylowTwoOf_inf
  rcases h513 G T M L V n h hV with ⟨W₁, W₂, hL₁, hL₂, hdisj, hsup, hW₁, hW₂⟩ |
    ⟨hn2, -, h2⟩ | h3 | h4 | ⟨h5, h5', h5''⟩
  ·
    exfalso
    obtain ⟨z, hzV, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hVel le_rfl hVT hTV hVne
    have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
      hVel.1.is_comm.comm ⟨a, hsup ▸ Subgroup.mem_sup_left ha⟩
        ⟨b, hsup ▸ Subgroup.mem_sup_right hb⟩ |> congrArg Subtype.val
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm (hsup.symm ▸ hzV)
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
  ·
    exact ⟨hn2, isA5ModuleSum_of_s5 (Or.inr h2) h.commutator_eq hT2 h.T_le_normalizer⟩
  ·
    exfalso
    set N := ⁅V, L⁆ with hNdef
    have hNV : N ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
    have hTN : T ≤ Subgroup.normalizer (N : Set G) :=
      le_normalizer_commutator_of hTV h.T_le_normalizer
    obtain ⟨F, _, _, _, -, ψ, Y, hc⟩ := h3.exists_qcoord hS
    have hNL : ⁅N, L⁆ ≠ ⊥ := fun hb =>
      hc.not_le_centralizer (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb))
    have hCL := h.inf_centralizer_le hc.le_normalizer hNL
    have hNne : N ≠ ⊥ := hV.2.2
    obtain ⟨z, hzN, hz1, hzZ⟩ :=
      exists_mem_omegaOneCenter hT2 hVel hNV hVT hTN hNne
    have hzC : z ∉ Subgroup.centralizer (L : Set G) := fun hzC => hz1 (by
      have hmem : z ∈ Z ⊓ Subgroup.centralizer (L : Set G) := ⟨hzZ, hzC⟩
      rwa [hZL, Subgroup.mem_bot] at hmem)
    have hY : Y ⟨z, hzN⟩ ≠ 1 := fun hY => hzC ((hc.ker _).mp hY)
    have hfix : d * z * d⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hdZ z hzZ, mul_inv_cancel_right]
    exact hd1 (hc.eq_one_of_fix_three hCL hdL hd3 hY hfix)
  ·
    obtain ⟨k, hk, -⟩ := id h4
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by have := h.two_le; omega
      subst hk1
      have hn2 : n = 2 := by omega
      subst hn2
      exact ⟨rfl, Or.inl h4.isA5ModuleUnder⟩
    · exact (horth G T M L V H B D K₁ X Kh₁ n m hc5 hty hX k hk2 (hk ▸ h4)).elim
  ·
    have hC : V ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxZ : x ∈ Z := mem_quasithinOmegaOneCenter_iff.mpr ⟨hVT hx.1,
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) hx.2,
        hVel.2 x hx.1⟩
      have hxL : x ∈ Subgroup.centralizer (L : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hx.2
      have hmem : x ∈ Z ⊓ Subgroup.centralizer (L : Set G) := ⟨hxZ, hxL⟩
      rwa [hZL] at hmem
    have hVeq : ⁅V, L⁆ = V := by
      have := h5.2
      rwa [hC, sup_bot_eq] at this
    refine ⟨h.n_eq_two_of_isBarS5 hV h5', Or.inl ?_⟩
    rw [← hVeq]
    exact isA5ModuleUnder_of_isS5ModCh5 h5'' h.commutator_eq hT2 h.T_le_normalizer

end CFSG.Quasithin.H13
