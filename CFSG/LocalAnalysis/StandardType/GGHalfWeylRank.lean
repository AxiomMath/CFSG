module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylBasic
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylAutomizer
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylInduced
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylTorusCoord
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylSignedConj
public import CFSG.LocalAnalysis.StandardType.GGSpJoinOrbitBound
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockCentral
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfWeylCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  (h : GGHalfWeylCtx p B Bs x L D J m y K)

private lemma inv_ne_self_of_ne_one (g : Multiplicative (ZMod 3)) (hg : g ≠ 1) : g⁻¹ ≠ g := by
  revert g
  decide

include h

theorem card_bs {ψL : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (hL : GGHalfTorusFrame Bs L (halfTorus (m + 1 + 1)) ψL) :
    Nat.card Bs = 3 ^ ((m + 1 + 1 + 1) / 2 + 1) := by
  obtain ⟨-, hpow3, hxBs, -, hxne, -, hLx, -, -, hcentL⟩ := h.basic
  classical
  let T : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) := halfTorus (m + 1 + 1)
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (L : Set G)
  have hTmap_inf : T.map ψL ⊓ C = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨hzT, hzC⟩ := hz
    rw [Subgroup.mem_map] at hzT
    obtain ⟨t, ht, rfl⟩ := hzT
    rw [Subgroup.mem_inf] at hzC
    have hcomm : ∀ s : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2,
        ψL t * ψL s = ψL s * ψL t := by
      intro s
      have hsL : ψL s ∈ L := by
        rw [← hL.range]
        exact ⟨s, rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp hzC.2 (ψL s) hsL).symm
    have ht1 : t = 1 := eq_one_of_commute_range hL.inj hcomm
    rw [ht1, map_one]
  have hCeq : C = Subgroup.zpowers x := by
    apply le_antisymm
    · intro g hg
      rw [Subgroup.mem_inf] at hg
      exact hcentL g hg.1 fun l hl =>
        (Subgroup.mem_centralizer_iff.mp hg.2 l hl).symm
    · rw [Subgroup.zpowers_le]
      exact ⟨hxBs, Subgroup.mem_centralizer_iff.mpr fun l hl => (hLx l hl).symm⟩
  have hxord : orderOf x = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime (hpow3 x hxBs) hxne
  have hCcard : Nat.card C = 3 := by
    rw [hCeq, Nat.card_zpowers, hxord]
  let f : ↥T × ↥C → ↥Bs := fun p =>
    ⟨ψL (p.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) * (p.2 : G), by
      exact Bs.mul_mem (hL.torus_le (Subgroup.mem_map_of_mem ψL p.1.2)) p.2.2.1⟩
  have hf_inj : Function.Injective f := by
    intro p q hp
    have hp' : ψL (p.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) * (p.2 : G) =
        ψL (q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) * (q.2 : G) :=
      Subtype.ext_iff.mp hp
    have h1 : (ψL (q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))⁻¹ *
        ψL (p.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) =
        (q.2 : G) * (p.2 : G)⁻¹ := by
      calc (ψL (q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))⁻¹ *
              ψL (p.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)
          = (ψL (q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))⁻¹ *
              (ψL (p.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) * (p.2 : G)) *
              (p.2 : G)⁻¹ := by group
        _ = (ψL (q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))⁻¹ *
              (ψL (q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) * (q.2 : G)) *
              (p.2 : G)⁻¹ := by rw [hp']
        _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
    have hmem : (ψL (q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))⁻¹ *
        ψL (p.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) ∈ T.map ψL ⊓ C := by
      rw [Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_map]
        exact ⟨(q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)⁻¹ *
          (p.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2),
          T.mul_mem (T.inv_mem q.1.2) p.1.2, by rw [map_mul, map_inv]⟩
      · rw [h1]
        exact C.mul_mem q.2.2 (C.inv_mem p.2.2)
    have hz1 : (ψL (q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))⁻¹ *
        ψL (p.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) = 1 := by
      rw [hTmap_inf] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hp1 : p.1 = q.1 := by
      apply Subtype.ext
      apply hL.inj
      calc ψL (p.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)
          = ψL (q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) *
            ((ψL (q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))⁻¹ *
              ψL (p.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) := by group
        _ = ψL (q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) * 1 := by rw [hz1]
        _ = ψL (q.1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) := by rw [mul_one]
    have hp2 : p.2 = q.2 := by
      apply Subtype.ext
      have hc : (q.2 : G) * (p.2 : G)⁻¹ = 1 := by rw [← h1, hz1]
      calc (p.2 : G) = 1 * (p.2 : G) := by rw [one_mul]
        _ = ((q.2 : G) * (p.2 : G)⁻¹) * (p.2 : G) := by rw [hc]
        _ = (q.2 : G) := by group
    exact Prod.ext hp1 hp2
  have hf_surj : Function.Surjective f := by
    intro b
    obtain ⟨t, ht, hact⟩ := hL.act (b : G) b.2
    let c : G := (ψL t)⁻¹ * (b : G)
    have hcC : c ∈ C := by
      rw [Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · exact Bs.mul_mem (Bs.inv_mem (hL.torus_le (Subgroup.mem_map_of_mem ψL ht))) b.2
      · rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hconj : c * l * c⁻¹ = l := by
          have h := hact l hl
          calc c * l * c⁻¹ = (ψL t)⁻¹ * ((b : G) * l * (b : G)⁻¹) * (ψL t) := by
                rw [show c = (ψL t)⁻¹ * (b : G) from rfl]; group
            _ = (ψL t)⁻¹ * (ψL t * l * (ψL t)⁻¹) * (ψL t) := by rw [h]
            _ = l := by group
        have hcomm : c * l = l * c := by
          calc c * l = (c * l * c⁻¹) * c := by group
            _ = l * c := by rw [hconj]
        exact hcomm.symm
    refine ⟨(⟨t, ht⟩, ⟨c, hcC⟩), ?_⟩
    apply Subtype.ext
    show ψL t * c = (b : G)
    rw [show c = (ψL t)⁻¹ * (b : G) from rfl]
    group
  have hcard : Nat.card Bs = Nat.card T * Nat.card C := by
    have e : ↥T × ↥C ≃ ↥Bs := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
    calc Nat.card Bs = Nat.card (↥T × ↥C) := (Nat.card_congr e).symm
      _ = Nat.card T * Nat.card C := Nat.card_prod _ _
  have hTcard : Nat.card T = 3 ^ ((m + 1 + 1 + 1) / 2) := by
    simpa [T] using card_halfTorus (m + 1 + 1)
  rw [hcard, hTcard, hCcard, ← pow_succ]

theorem weylRank_eq {ψL ψK : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (hL : GGHalfTorusFrame Bs L (halfTorus (m + 1 + 1)) ψL)
    (hK : GGHalfTorusFrame Bs K (halfTorus (m + 1 + 1)) ψK) {r : ℕ}
    (hr : GGWeylOfType p (CoxeterMatrix.B r) (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    r = (m + 1 + 1 + 1) / 2 + 1 := by
  obtain ⟨-, hp3, -, -, -, -, -⟩ := h.nbr
  subst hp3
  obtain ⟨-, hpow3, hxBs, -, hxne, -, hLx, -, hxnotK, -⟩ := h.basic
  have hp : Nat.Prime 3 := h.cfg.1.2.2.2.2.2.1.1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hBs : IsElemAbelian 3 Bs := h.cfg.2.1.2.1
  have hcardBs : Nat.card Bs = 3 ^ ((m + 1 + 1 + 1) / 2 + 1) := card_bs h hL
  have hle : r ≤ (m + 1 + 1 + 1) / 2 + 1 := by
    by_cases h2 : 2 ≤ r
    · have hpow := pow_le_card_of_weylOfType_B hp hp2 hBs h2 hr
      rw [hcardBs] at hpow
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow
    · omega
  have hge : (m + 1 + 1 + 1) / 2 + 1 ≤ r := by
    by_contra hnot
    have hrk : r ≤ (m + 1 + 1 + 1) / 2 := by omega
    obtain ⟨e, -⟩ := hr
    let AL : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs
    let AK : Subgroup (MulAut ↥Bs) := ggAutomizer K Bs
    let A : Subgroup (MulAut ↥Bs) := AL ⊔ AK
    have hcardA : Nat.card A ≤ 2 ^ r * r.factorial := by
      calc Nat.card A = Nat.card (CoxeterMatrix.B r).Group := by
            simpa [A, AL, AK] using (Nat.card_congr e.toEquiv).symm
        _ ≤ 2 ^ r * r.factorial := card_coxeterB_le r
    have hALge : 2 ^ ((m + 1 + 1 + 1) / 2) * ((m + 1 + 1 + 1) / 2).factorial ≤
        Nat.card AL := by
      have h := hL.card_automizer_ge (G := G) (X := L) (n := m + 1 + 1) (by omega)
      simpa [AL] using h
    have hALleA : AL ≤ A := le_sup_left
    have hmono : 2 ^ r * r.factorial ≤
        2 ^ ((m + 1 + 1 + 1) / 2) * ((m + 1 + 1 + 1) / 2).factorial :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num : 0 < 2) hrk) (Nat.factorial_le hrk)
    have hALeqA : AL = A := by
      apply Subgroup.eq_of_le_of_card_ge hALleA
      exact le_trans hcardA (le_trans hmono hALge)
    have hAKleAL : AK ≤ AL := by
      have h1 : AK ≤ AL ⊔ AK := le_sup_right
      rw [show AL ⊔ AK = AL from hALeqA.symm] at h1
      exact h1
    have hxcent : x ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun l hl => (hLx l hl).symm
    have hfixAL : ∀ ψ ∈ AL, ((ψ ⟨x, hxBs⟩ : ↥Bs) : G) = x := by
      intro ψ hψ
      exact SpJoin.ggAutomizer_fixes_of_mem_centralizer (K := L) hxBs hxcent ψ
        (by simpa [AL] using hψ)
    obtain ⟨t, ht, hact⟩ := hK.act x hxBs
    have ht_ne : t ≠ 1 := by
      intro ht1
      apply hxnotK
      intro k hk
      have h := hact k hk
      rw [ht1, map_one, one_mul, inv_one, mul_one] at h
      calc x * k = (x * k * x⁻¹) * x := by group
        _ = k * x := by rw [h]
    let c0 : G := (ψK t)⁻¹ * x
    have hc0Bs : c0 ∈ Bs :=
      Bs.mul_mem (Bs.inv_mem (hK.torus_le (Subgroup.mem_map_of_mem ψK ht))) hxBs
    have hc0cent : c0 ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hconj : c0 * k * c0⁻¹ = k := by
        have h := hact k hk
        calc c0 * k * c0⁻¹ = (ψK t)⁻¹ * (x * k * x⁻¹) * (ψK t) := by
              rw [show c0 = (ψK t)⁻¹ * x from rfl]; group
          _ = (ψK t)⁻¹ * (ψK t * k * (ψK t)⁻¹) * (ψK t) := by rw [h]
          _ = k := by group
      have hcomm : c0 * k = k * c0 := by
        calc c0 * k = (c0 * k * c0⁻¹) * c0 := by group
          _ = k * c0 := by rw [hconj]
      exact hcomm.symm
    obtain ⟨Φ, hΦ⟩ := exists_torusCoord (m + 1 + 1)
    let Tb : ↥(halfTorus (m + 1 + 1)) := ⟨t, ht⟩
    let a : Fin ((m + 1 + 1 + 1) / 2) → Multiplicative (ZMod 3) := Φ.symm Tb
    have hΦa : (Φ a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) = t := by
      have h1 : Φ (Φ.symm Tb) = Tb := by
        simpa using (Equiv.apply_symm_apply (e := Φ.toEquiv) Tb)
      show ((Φ (Φ.symm Tb)) : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) = t
      exact congrArg Subtype.val h1
    have ha_ne : a ≠ 1 := by
      intro ha1
      have h1 : Φ (Φ.symm Tb) = Tb := by
        simpa using (Equiv.apply_symm_apply (e := Φ.toEquiv) Tb)
      have h2 : Φ a = 1 := by rw [ha1, map_one]
      have h3 : Tb = 1 := h1.symm.trans h2
      have h4 : t = 1 := congrArg Subtype.val h3
      exact ht_ne h4
    have hex : ∃ j : Fin ((m + 1 + 1 + 1) / 2), a j ≠ 1 := by
      by_contra hcon
      apply ha_ne
      funext j
      by_contra hj
      exact hcon ⟨j, hj⟩
    obtain ⟨j, haj⟩ := hex
    let ρ : Equiv.Perm (Fin ((m + 1 + 1 + 1) / 2) → Multiplicative (ZMod 3)) :=
      SpJoin.coordInv ((m + 1 + 1 + 1) / 2) 3 j
    have hρmem : ρ ∈ SpJoin.spSignedGroup ((m + 1 + 1 + 1) / 2) 3 :=
      SpJoin.coordInv_mem_spSignedGroup (n := (m + 1 + 1 + 1) / 2) (p := 3) j
    obtain ⟨σ, hσA, hσprop⟩ := hK.exists_aut_signed (n := m + 1 + 1) Φ hΦ ρ hρmem
    have hxsplit : ψK (Φ a) * c0 = x := by
      rw [hΦa, show c0 = (ψK t)⁻¹ * x from rfl]
      group
    have hb0 : ψK (Φ a) * c0 ∈ Bs := by rw [hxsplit]; exact hxBs
    have hσx : ((σ ⟨x, hxBs⟩ : ↥Bs) : G) = ψK (Φ (ρ a)) * c0 := by
      have h1 := hσprop a c0 hb0 hc0cent
      have heq : (⟨ψK (Φ a) * c0, hb0⟩ : ↥Bs) = ⟨x, hxBs⟩ := Subtype.ext hxsplit
      rwa [heq] at h1
    have hσx_ne : ((σ ⟨x, hxBs⟩ : ↥Bs) : G) ≠ x := by
      rw [hσx, ← hxsplit]
      intro hcontra
      have h2 : ψK (Φ (ρ a)) = ψK (Φ a) := mul_right_cancel hcontra
      have h3 : Φ (ρ a) = Φ a := Subtype.ext (hK.inj h2)
      have h4 : ρ a = a := Φ.injective h3
      have h5 : ρ a ≠ a := by
        intro heq
        have hval : (a j)⁻¹ = a j := by
          have hc := congrFun heq j
          change SpJoin.coordInv ((m + 1 + 1 + 1) / 2) 3 j a j = a j at hc
          rwa [SpJoin.coordInv_apply, Function.update_self] at hc
        exact (inv_ne_self_of_ne_one (a j) haj) hval
      exact h5 h4
    have hfixAK : ∀ ψ ∈ AK, ((ψ ⟨x, hxBs⟩ : ↥Bs) : G) = x :=
      fun ψ hψ => hfixAL ψ (hAKleAL hψ)
    have hσAK : σ ∈ AK := by simpa [AK] using hσA
    exact hσx_ne (hfixAK σ hσAK)
  exact le_antisymm hle hge

end GGHalfWeylCtx

end CFSG.StandardType

end
