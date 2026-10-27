module

public import CFSG.Quasithin.Vol2.Ch3y319
public import CFSG.Quasithin.Vol2.Ch3Sec1Lem319Aux

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

private theorem qMinC_relIndex_eq_sq {r₁ r₂ p q x u : ℕ} (h₁ : r₁ * x = u) (h₂ : r₂ * q = p)
    (h : p ^ 2 * x = q ^ 2 * u) (hx : 0 < x) (hq : 0 < q) : r₁ = r₂ ^ 2 := by
  subst h₁ h₂
  have h' : (q ^ 2 * x) * r₂ ^ 2 = (q ^ 2 * x) * r₁ := by
    calc (q ^ 2 * x) * r₂ ^ 2 = (r₂ * q) ^ 2 * x := by ring
      _ = q ^ 2 * (r₁ * x) := h
      _ = (q ^ 2 * x) * r₁ := by ring
  exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (pow_pos hq 2) hx) h').symm

section Counting

variable {G : Type} [Group G] [Finite G]

private theorem qMinC_relIndex_mul_card {K N : Subgroup G} (h : K ≤ N) :
    K.relIndex N * Nat.card K = Nat.card N := by
  have e := Subgroup.relIndex_mul_card K N
  rwa [inf_eq_left.mpr h] at e

private theorem qMinC_secRank_eq (N L : Subgroup G) :
    secRank N L = padicValNat 2 (L.relIndex N) := rfl

end Counting

section Main

variable {G : Type} [Group G] [Finite G] {T M M₀ H V : Subgroup G}

theorem Hyp319.qMin_le_of_concl (hT : quasithinIsSylowTwo T) (h : Hyp319 T M M₀ H V) {hyp5 : Prop}
    (hconcl : Concl319 T M V H hyp5) {A : Subgroup G} (hA : IsMinOffender T H V A) :
    qMin M V h.reduced.2.2.1 ≤ secRank A (A ⊓ pCoreOf 2 H) := by
  have hRT : pCoreOf 2 H ≤ T := h.pCoreOf_le hT
  have hV := h.reduced.2.2.1
  have hAel : IsElemAbelian 2 A := hA.1.2.1
  have e1 : 2 * secRank A (A ⊓ pCoreOf 2 H) =
      secRank (conjClosure V H) (conjClosure V H ⊓ Subgroup.centralizer (A : Set G)) := by
    have hr := qMinC_relIndex_eq_sq
      (qMinC_relIndex_mul_card (inf_le_left : conjClosure V H ⊓ Subgroup.centralizer (A : Set G) ≤ conjClosure V H))
      (qMinC_relIndex_mul_card (inf_le_left : A ⊓ pCoreOf 2 H ≤ A)) (hconcl.count_one A hA)
      Nat.card_pos Nat.card_pos
    rw [qMinC_secRank_eq A, qMinC_secRank_eq (conjClosure V H), hr, padicValNat.pow]
  have e2 : secRank (conjClosure V H) (conjClosure V H ⊓ Subgroup.centralizer (A : Set G)) =
      2 * secRank (A ⊓ pCoreOf 2 H)
        (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V H : Set G)) := by
    have hc2 : Nat.card (A ⊓ pCoreOf 2 H : Subgroup G) ^ 2 *
        Nat.card (conjClosure V H ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) =
        Nat.card (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V H : Set G) : Subgroup G) ^ 2 *
          Nat.card (conjClosure V H) :=
      (hconcl.count_two A hA).symm.trans (mul_comm _ _)
    have hr := qMinC_relIndex_eq_sq
      (qMinC_relIndex_mul_card (inf_le_left : conjClosure V H ⊓ Subgroup.centralizer (A : Set G) ≤ conjClosure V H))
      (qMinC_relIndex_mul_card (inf_le_left :
        A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V H : Set G) ≤ A ⊓ pCoreOf 2 H))
      hc2 Nat.card_pos Nat.card_pos
    rw [qMinC_secRank_eq (conjClosure V H), qMinC_secRank_eq (A ⊓ pCoreOf 2 H), hr, padicValNat.pow]
  have hBA : A ⊓ pCoreOf 2 H ≤ A := inf_le_left
  have h1 : 1 ≤ secRank A (A ⊓ pCoreOf 2 H) :=
    one_le_secRank_of_not_le (B6.isPGroup_of_isElemAbelian hAel)
      fun hle => hA.not_le hRT (hle.trans inf_le_right)
  have h2 : secRank (A ⊓ pCoreOf 2 H)
      (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V H : Set G)) =
      secRank A (A ⊓ pCoreOf 2 H) := by omega
  have hBU : ¬ A ⊓ pCoreOf 2 H ≤ Subgroup.centralizer (conjClosure V H : Set G) := by
    intro hle
    rw [inf_eq_left.mpr hle, secRank_self] at h2
    omega
  obtain ⟨g, hgH, hg⟩ := exists_conj_not_comm hBU
  have hg' : ⁅A ⊓ pCoreOf 2 H, conjSubgroup V g⁆ ≠ ⊥ := by
    rwa [Subgroup.commutator_comm]
  have e3 : secRank (conjSubgroup V g)
      (conjSubgroup V g ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G)) =
      2 * secRank (A ⊓ pCoreOf 2 H)
        (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) := by
    have hr := qMinC_relIndex_eq_sq
      (qMinC_relIndex_mul_card (inf_le_left :
        conjSubgroup V g ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G) ≤
          conjSubgroup V g))
      (qMinC_relIndex_mul_card (inf_le_left :
        A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) ≤ A ⊓ pCoreOf 2 H))
      (hconcl.count_three A hA g hgH hg') Nat.card_pos Nat.card_pos
    rw [qMinC_secRank_eq (conjSubgroup V g), qMinC_secRank_eq (A ⊓ pCoreOf 2 H), hr, padicValNat.pow]
  have hB'H : B6.conjSub g (A ⊓ pCoreOf 2 H) ≤ pCoreOf 2 H := by
    intro x hx
    rw [B6.mem_conjSub] at hx
    have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hgH) (g⁻¹ * x * g)).mp
      hx.2
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h2
  have hB'T : B6.conjSub g (A ⊓ pCoreOf 2 H) ≤ T := hB'H.trans hRT
  have hB'M : B6.conjSub g (A ⊓ pCoreOf 2 H) ≤ M := hB'T.trans h.T_le_M
  have hB'N : B6.conjSub g (A ⊓ pCoreOf 2 H) ≤ Subgroup.normalizer (V : Set G) :=
    hB'T.trans (h.T_le.trans h.reduced.2.1)
  have hBel : IsElemAbelian 2 (A ⊓ pCoreOf 2 H) := by
    have hAel' := hAel
    rw [B6.isElemAbelian_iff] at hAel' ⊢
    exact ⟨fun a ha b hb => hAel'.1 a ha.1 b hb.1, fun a ha => hAel'.2 a ha.1⟩
  have hB'el : IsElemAbelian 2 (B6.conjSub g (A ⊓ pCoreOf 2 H)) := B6.isElemAbelian_conjSub hBel g
  have hPV : B6.conjSub g (conjSubgroup V g) = V := conjSub_conjSubgroup g V
  have hcentV : Subgroup.centralizer (V : Set G) =
      B6.conjSub g (Subgroup.centralizer (conjSubgroup V g : Set G)) := by
    rw [B6conjSub_centralizer, hPV]
  have hnc : ¬ B6.conjSub g (A ⊓ pCoreOf 2 H) ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    rw [hcentV] at hle
    have hle' : A ⊓ pCoreOf 2 H ≤ Subgroup.centralizer (conjSubgroup V g : Set G) :=
      (B6.conjSub g).le_iff_le.mp hle
    apply hg
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hle'
  have hVgU : conjSubgroup V g ≤ conjClosure V H := conjSubgroup_le_conjClosure hgH
  have hq : ⁅⁅V, B6.conjSub g (A ⊓ pCoreOf 2 H)⁆, B6.conjSub g (A ⊓ pCoreOf 2 H)⁆ = ⊥ := by
    have hle : ⁅⁅conjSubgroup V g, A ⊓ pCoreOf 2 H⁆, A ⊓ pCoreOf 2 H⁆ ≤ ⊥ := by
      rw [← hA.2.2.2]
      exact Subgroup.commutator_mono (Subgroup.commutator_mono hVgU hBA) hBA
    have h3 : B6.conjSub g ⁅⁅conjSubgroup V g, A ⊓ pCoreOf 2 H⁆, A ⊓ pCoreOf 2 H⁆ = ⊥ := by
      apply le_bot_iff.mp
      rw [← (B6.conjSub g).map_bot]
      exact (B6.conjSub g).monotone hle
    rw [B6conjSub_commutator, B6conjSub_commutator, hPV] at h3
    exact h3
  have eB : secRank (B6.conjSub g (A ⊓ pCoreOf 2 H))
      (B6.conjSub g (A ⊓ pCoreOf 2 H) ⊓ Subgroup.centralizer (V : Set G)) =
      secRank (A ⊓ pCoreOf 2 H)
        (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) := by
    have := secRank_conjSub g (A ⊓ pCoreOf 2 H)
      (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V g : Set G))
    have hinf : B6.conjSub g
        (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) =
        B6.conjSub g (A ⊓ pCoreOf 2 H) ⊓ Subgroup.centralizer (V : Set G) := by
      rw [OrderIso.map_inf (B6.conjSub g) (A ⊓ pCoreOf 2 H)
        (Subgroup.centralizer (conjSubgroup V g : Set G)), ← hcentV]
    rw [hinf] at this
    exact this
  have eV : secRank V
      (V ⊓ Subgroup.centralizer ((B6.conjSub g (A ⊓ pCoreOf 2 H) : Subgroup G) : Set G)) =
      secRank (conjSubgroup V g)
        (conjSubgroup V g ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G)) := by
    have := secRank_conjSub g (conjSubgroup V g)
      (conjSubgroup V g ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G))
    have hinf : B6.conjSub g
        (conjSubgroup V g ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G)) =
        V ⊓ Subgroup.centralizer ((B6.conjSub g (A ⊓ pCoreOf 2 H) : Subgroup G) : Set G) := by
      rw [OrderIso.map_inf (B6.conjSub g) (conjSubgroup V g)
        (Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G)), hPV, B6conjSub_centralizer]
    rw [hinf, hPV] at this
    exact this
  have hr : secRank V
      (V ⊓ Subgroup.centralizer ((B6.conjSub g (A ⊓ pCoreOf 2 H) : Subgroup G) : Set G)) =
      2 * secRank (B6.conjSub g (A ⊓ pCoreOf 2 H))
        (B6.conjSub g (A ⊓ pCoreOf 2 H) ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [eV, eB]
    exact e3
  obtain ⟨hQ, hrk⟩ := mem_Qset_autOn (M := M) hV hB'M hB'N hB'el hnc hq hr
  have hmono : secRank (A ⊓ pCoreOf 2 H)
      (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) ≤
      secRank (A ⊓ pCoreOf 2 H)
        (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V H : Set G)) :=
    secRank_anti (inf_le_inf_left _ (Subgroup.centralizer_le hVgU))
  calc qMin M V hV ≤ rk ↥(autOn (B6.conjSub g (A ⊓ pCoreOf 2 H)) V) :=
        Nat.sInf_le ⟨_, hQ, rfl⟩
    _ = _ := hrk
    _ = _ := eB
    _ ≤ _ := hmono
    _ = secRank A (A ⊓ pCoreOf 2 H) := h2

end Main

end CFSG.Quasithin
