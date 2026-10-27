module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec64Cor
public import CFSG.RankThree.GF2n.Stroth80.HeringSec65NAbs
public import CFSG.RankThree.GF2n.Stroth80.HeringSec65NBar
public import CFSG.RankThree.GF2n.Stroth80.HeringSec65NNorm
public import CFSG.RankThree.GF2n.Stroth80.HeringSec65NLam
public import CFSG.RankThree.GF2n.Stroth80.Sec123SL2Grp
public import CFSG.RankThree.GF2n.Stroth80.Sec123SL2Sylow

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

namespace HS6

section SL2Data

variable {G : Type} [Group G] {M Q : Subgroup G} [(Q.subgroupOf M).Normal]

theorem sl2_data {S : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M) [(Q.subgroupOf S).Normal] {q : ℕ}
    (hq2 : ∃ e : ℕ, q = 2 ^ e) (hq4 : 4 ≤ q)
    (hsl : IsSLModel 2 q (↥S ⧸ Q.subgroupOf S)) :
    Nat.card (bar M Q S) = q * (q ^ 2 - 1) ∧ q = 2 ^ (Nat.card (bar M Q S)).factorization 2 ∧
      IsSimpleGroup ↥(bar M Q S) ∧ ∃ a b : ↥(bar M Q S), a * b ≠ b * a := by
  obtain ⟨K, fK, finK, hKq, ⟨e₀⟩⟩ := hsl
  obtain ⟨ee, hee⟩ := hq2
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hee)
  have hK4 : 4 ≤ Nat.card K := hKq ▸ hq4
  let eSL : ↥S ⧸ Q.subgroupOf S ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    e₀.trans (specialLinearGroupEquivStatedSL 2 K).symm
  let eS : ↥(bar M Q S) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (barEquiv hQS hSM).symm.trans eSL
  have hcard : Nat.card (bar M Q S) = q * (q ^ 2 - 1) := by
    rw [Nat.card_congr eS.toEquiv, SL2Grp.sl2_card K, hKq]
  refine ⟨hcard, ?_, ?_, ?_⟩
  · rw [hcard, ← hKq]
    exact (SL2Grp.sl2_card_factorization K).trans (by rw [SL2Grp.sl2_card K])
  · haveI := SL2Grp.sl2_isSimpleGroup (K := K) hK4
    exact eS.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := SL2Grp.sl2_nonabelian (K := K)
    refine ⟨eS.symm a, eS.symm b, fun h => hab ?_⟩
    have := congrArg eS h
    simpa using this

end SL2Data

section General

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conj_Lgen_eq {L : Subgroup G} {g : G} (hg : g ∈ M) :
    conjSubgroup g (Lgen M L) = Lgen M L := by
  have hle : Lgen M L ≤ (Lgen M L).comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun m hm y hy => ?_
    show g * y * g⁻¹ ∈ Lgen M L
    have hy' : g * y * g⁻¹ ∈ conjSubgroup (g * m) L := by
      rw [mem_conjSubgroup]
      have : (g * m)⁻¹ * (g * y * g⁻¹) * (g * m) = m⁻¹ * y * m := by group
      rw [this]
      exact mem_conjSubgroup.mp hy
    exact (le_iSup₂ (f := fun m' (_ : m' ∈ M) => conjSubgroup m' L) (g * m)
      (M.mul_mem hg hm)) hy'
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_conjSubgroup])
  intro y hy
  obtain ⟨r, hr, rfl⟩ := hy
  exact hle hr

theorem Lgen_le_M' {L : Subgroup G} (hL : L ≤ M) (hM : ∀ m ∈ M, conjSubgroup m M = M) :
    Lgen M L ≤ M := by
  refine iSup₂_le fun m hm => ?_
  calc conjSubgroup m L ≤ conjSubgroup m M := Subgroup.map_mono hL
    _ = M := hM m hm

theorem Lgen_mono' {L L' : Subgroup G} (h : L ≤ L') : Lgen M L ≤ Lgen M L' :=
  iSup₂_mono fun m _ => Subgroup.map_mono h

theorem exists_Cgrp (hc : Ctx M Q Z B) (X : Subgroup G) :
    ∃ C : Subgroup G, ∀ h, h ∈ C ↔ h ∈ H0 M Z ∧ ∀ x ∈ X, ⁅h, x⁆ ∈ Q := by
  have hQn : ∀ a ∈ M, ∀ q ∈ Q, a * q * a⁻¹ ∈ Q := fun a ha q hq =>
    (hc.conj_mem_Q_of_mem_M ha).1 q hq
  refine ⟨{ carrier := {h | h ∈ H0 M Z ∧ ∀ x ∈ X, ⁅h, x⁆ ∈ Q}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun h => Iff.rfl⟩
  · rintro a b ⟨ha, hax⟩ ⟨hb, hbx⟩
    refine ⟨(H0 M Z).mul_mem ha hb, fun x hx => ?_⟩
    have e : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem (hQn a ha.1 _ (hbx x hx)) (hax x hx)
  · refine ⟨(H0 M Z).one_mem, fun x _ => ?_⟩
    rw [show ⁅(1 : G), x⁆ = 1 by simp [commutatorElement_def]]
    exact Q.one_mem
  · rintro a ⟨ha, hax⟩
    refine ⟨(H0 M Z).inv_mem ha, fun x hx => ?_⟩
    have e : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := hQn a⁻¹ (M.inv_mem ha.1) _ (Q.inv_mem (hax x hx))
    simpa using this

end General

section Core


theorem stroth65XNormal_core (I : Inputs) (h63b : Stroth63bStatement)
    (h64 : Stroth64Statement) : Stroth65XNormalStatement := by
  intro G _ _ M Q Z B hc n t hs m hm hn hΩ X hQX hXR hNX hNXQ hcen hXsat
  classical
  have e : Env hc n t m X := ⟨hs, hm, hn, hΩ, hQX, hXR, hNX, hNXQ, hcen⟩
  haveI hQnM : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht := hs.toSec5.mem
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hNM : hc.CN t ≤ M := e.CN_le_M
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN ht
  have hXM : X ≤ M := e.X_le_M
  have hMconj : ∀ g ∈ M, conjSubgroup g M = M := fun g hg => hc.conj_M_eq hg
  have hQS : Q ≤ Lgen M (hc.CN t) := hQN.trans (le_Lgen_self M (hc.CN t))
  have hSM : Lgen M (hc.CN t) ≤ M := Lgen_le_M' hNM hMconj
  have hSH0 : Lgen M (hc.CN t) ≤ H0 M Z :=
    (Lgen_mono' (e.N_le_LB I)).trans (ActionData.Lgen_le_H0 hc)
  have hSnorm : ∀ g ∈ M, conjSubgroup g (Lgen M (hc.CN t)) = Lgen M (hc.CN t) :=
    fun g hg => conj_Lgen_eq hg
  have h64' := h64 G M Q Z B hc n t hs m hm hΩ
  obtain ⟨hSn, hsl⟩ := h64'
  haveI := hSn
  obtain ⟨e', -, he', -⟩ := hc.hyp.cp
  have hq4 := hc.hyp.q4
  obtain ⟨hScard, hsyl, hSsimple, hSnonab⟩ := sl2_data hQS hSM ⟨e', he'⟩ hq4 hsl
  have hUcard : Nat.card (bar M Q (hc.CN t)) = Nat.card Z := by
    have h1 := card_bar_mul hQN hNM
    rw [e.hs.cardN] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hQpos (by rw [h1, mul_comm])
  have hcardU : Nat.card (bar M Q (hc.CN t)) =
      2 ^ (Nat.card (bar M Q (Lgen M (hc.CN t)))).factorization 2 := by rw [hUcard, hsyl]
  have hScard' : Nat.card (bar M Q (Lgen M (hc.CN t))) = Nat.card (bar M Q (hc.CN t)) *
      (Nat.card (bar M Q (hc.CN t)) ^ 2 - 1) := by rw [hScard, hUcard]
  have hq4' : 4 ≤ Nat.card (bar M Q (hc.CN t)) := hUcard ▸ hq4
  have hUS : bar M Q (hc.CN t) ≤ bar M Q (Lgen M (hc.CN t)) :=
    bar_mono (le_Lgen_self M (hc.CN t))
  haveI hSbarnorm : (bar M Q (Lgen M (hc.CN t))).Normal := bar_normal hQM hSnorm
  have hCor := e.corBHyp I (h63b G M Q Z B hc n t hs m hm hΩ)
  have hTI : ∀ g : ↥M ⧸ Q.subgroupOf M, bar M Q (hc.CN t) ⊓ conjSubgroup g (bar M Q (hc.CN t)) = ⊥ ∨
      conjSubgroup g (bar M Q (hc.CN t)) = bar M Q (hc.CN t) := by
    intro g
    rcases hCor.2.1 g with h | h
    · exact Or.inl h
    · right
      have h1 : bar M Q (hc.CN t) ≤ conjSubgroup g (bar M Q (hc.CN t)) := inf_eq_left.mp h
      exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [card_conjSubgroup])).symm
  have hUab : ∀ a ∈ bar M Q (hc.CN t), ∀ b ∈ bar M Q (hc.CN t), a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', ha'M, rfl⟩ := (mem_bar a).mp ha
    obtain ⟨b', hb', hb'M, rfl⟩ := (mem_bar b).mp hb
    exact piM_comm_of_comm_mem ha'M hb'M ((e.N_mod_Q I.h34).1 a' ha' b' hb')
  obtain ⟨hXn, hXcomm⟩ := commutator_quot_eq_top hm ⟨e', he'⟩ (hXsat.imp (·.2) (·.2))
  haveI := hXn
  have hYperf : ⁅bar M Q X, bar M Q X⁆ = bar M Q X := by
    haveI : Group.IsPerfect (↥X ⧸ Q.subgroupOf X) := Group.isPerfect_def.mpr hXcomm
    haveI : Group.IsPerfect ↥(bar M Q X) :=
      Group.IsPerfect.ofSurjective (f := (barEquiv hQX hXM).toMonoidHom)
        (barEquiv hQX hXM).surjective
    exact Subgroup.isPerfect_iff.mp this
  have hYU : ∀ y ∈ bar M Q X, ∀ u ∈ bar M Q (hc.CN t), y * u = u * y := by
    intro y hy u hu
    obtain ⟨x, hx, hxM, rfl⟩ := (mem_bar y).mp hy
    obtain ⟨a, ha, haM, rfl⟩ := (mem_bar u).mp hu
    exact (piM_comm_of_comm_mem haM hxM (hcen a ha x hx)).symm
  have hcent := centralizes_of_perfect hUS hcardU hScard' hq4' hSsimple hTI hUab hYU hYperf
  have hSX : ∀ s ∈ Lgen M (hc.CN t), ∀ x ∈ X, ⁅x, s⁆ ∈ Q := by
    intro s hs' x hx
    refine comm_mem_Q_of_piM_comm (hXM hx) (hSM hs') ?_
    exact hcent _ (piM_mem_bar hx (hXM hx)) _ (piM_mem_bar hs' (hSM hs'))
  have hFr := frattini_two hUS hcardU
  have hdecomp : ∀ g ∈ M, ∃ n' ∈ M, conjSubgroup n' (hc.CN t) = hc.CN t ∧
      ∃ s ∈ Lgen M (hc.CN t), g = n' * s * (n' * s)⁻¹ * g ∧ (n' * s)⁻¹ * g ∈ Q := by
    intro g hg
    have hmem : piM M Q g ∈ Subgroup.normalizer ((bar M Q (hc.CN t) : Subgroup _) : Set _) ⊔
        bar M Q (Lgen M (hc.CN t)) := by rw [hFr]; exact Subgroup.mem_top _
    obtain ⟨nb, hnb, sb, hsb, hmul⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    obtain ⟨s, hsS, hsM, rfl⟩ := (mem_bar sb).mp hsb
    obtain ⟨n', hn'M, hpn', hn'N⟩ := exists_lift_normalizer hQM (conj_Q_mem hc) hQN hNM hnb
    refine ⟨n', hn'M, hn'N, s, hsS, by group, ?_⟩
    rw [← hpn', ← piM_mul hn'M hsM] at hmul
    exact (piM_eq_iff (M.mul_mem hn'M hsM) hg).mp hmul
  have hXnorm : ∀ g ∈ M, ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g hg x hx
    obtain ⟨n', hn'M, hn'N, s, hsS, -, hq⟩ := hdecomp g hg
    set q := (n' * s)⁻¹ * g with hqdef
    have hgq : g = n' * s * q := by rw [hqdef]; group
    have h1 : q * x * q⁻¹ ∈ X := X.mul_mem (X.mul_mem (hQX hq) hx) (X.inv_mem (hQX hq))
    have h2 : s * (q * x * q⁻¹) * s⁻¹ ∈ X := by
      have e1 : s * (q * x * q⁻¹) * s⁻¹ = (⁅(q * x * q⁻¹), s⁆)⁻¹ * (q * x * q⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e1]
      exact X.mul_mem (X.inv_mem (hQX (hSX s hsS _ h1))) h1
    have h3 : n' * (s * (q * x * q⁻¹) * s⁻¹) * n'⁻¹ ∈ X := by
      have := e.conj_X_le I hXcomm hn'M hn'N
      exact this (by
        rw [mem_conjSubgroup, show n'⁻¹ * (n' * (s * (q * x * q⁻¹) * s⁻¹) * n'⁻¹) * n' =
          s * (q * x * q⁻¹) * s⁻¹ by group]
        exact h2)
    rw [hgq, show n' * s * q * x * (n' * s * q)⁻¹ = n' * (s * (q * x * q⁻¹) * s⁻¹) * n'⁻¹ by
      group]
    exact h3
  obtain ⟨C₀, hC₀⟩ := exists_Cgrp hc X
  obtain ⟨ι, _, _, K, _, _, _, Q', X', E, φ, _, ψ, u, hK, hXsc, hgeom, hmod⟩ :=
    e.exists_model_scalar I
  have hSC : ∀ s ∈ Lgen M (hc.CN t), s ∈ C₀ := fun s hs' =>
    (hC₀ s).mpr ⟨hSH0 hs', fun x hx => by
      have := Q.inv_mem (hSX s hs' x hx)
      rwa [commutatorElement_inv] at this⟩
  have hBhat : Nat.card ↥(Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) ⊓
      Lgen M (hc.CN t)) = Nat.card ↥(hc.CN t) * (Nat.card Z - 1) := by
    have hQnorm : Q ≤ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) ⊓ M :=
      le_inf (hQN.trans Subgroup.le_normalizer) hQM
    have hbar : bar M Q (Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) ⊓
        Lgen M (hc.CN t)) = Subgroup.normalizer ((bar M Q (hc.CN t) : Subgroup _) : Set _) ⊓
          bar M Q (Lgen M (hc.CN t)) := by
      rw [show Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) ⊓ Lgen M (hc.CN t) =
        (Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) ⊓ M) ⊓ Lgen M (hc.CN t) by
          rw [inf_assoc, inf_eq_right.mpr hSM],
        bar_inf hQnorm hQS, bar_normalizer hQM hQN hNM]
    have h1 := card_bar_mul (S := Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) ⊓
      Lgen M (hc.CN t)) (le_inf (hQN.trans Subgroup.le_normalizer) hQS)
      (inf_le_right.trans hSM)
    rw [hbar, card_normalizer_inf hUS hcardU hScard' hq4' hSsimple hTI] at h1
    have h2 := card_bar_mul hQN hNM
    rw [← h1, ← h2, hUcard]
    ring
  have hcard𝒩 := hmod.card_le_of_lambda I e hXsc hK C₀ hC₀
  have hB𝒩 : Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) ⊓ Lgen M (hc.CN t) ≤
      C₀ ⊓ Subgroup.normalizer ((Vt M (LB M Q B) B Z t : Subgroup G) : Set G) := by
    rintro b ⟨hbN, hbS⟩
    refine ⟨hSC b hbS, ?_⟩
    exact conjSubgroup_eq_self_iff.mp (e.conj_Vt_eq I (hSM hbS) (conjSubgroup_eq_self_iff.mpr hbN))
  have heq := Subgroup.eq_of_le_of_card_ge hB𝒩 (by rw [hBhat]; exact hcard𝒩)
  have hSeq : Lgen M (hc.CN t) = C₀ := by
    refine le_antisymm (fun s hs' => hSC s hs') (fun h hh => ?_)
    have hhM : h ∈ M := ((hC₀ h).mp hh).1.1
    obtain ⟨n', hn'M, hn'N, s, hsS, -, hq⟩ := hdecomp h hhM
    have hn'C : n' ∈ C₀ := by
      have : n' = h * ((n' * s)⁻¹ * h)⁻¹ * s⁻¹ := by group
      rw [this]
      exact C₀.mul_mem (C₀.mul_mem hh (C₀.inv_mem (hSC _ (hQS hq)))) (C₀.inv_mem (hSC s hsS))
    have hn'V : n' ∈ Subgroup.normalizer ((Vt M (LB M Q B) B Z t : Subgroup G) : Set G) :=
      conjSubgroup_eq_self_iff.mp (e.conj_Vt_eq I hn'M hn'N)
    have hn'B : n' ∈ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) ⊓
        Lgen M (hc.CN t) := by
      rw [heq]
      exact ⟨hn'C, hn'V⟩
    have : h = n' * s * ((n' * s)⁻¹ * h) := by group
    rw [this]
    exact (Lgen M (hc.CN t)).mul_mem ((Lgen M (hc.CN t)).mul_mem hn'B.2 hsS) (hQS hq)
  have hCX : C₀ ⊓ X = Q := by
    refine le_antisymm ?_ (le_inf (fun q hq => hSC q (hQS hq)) hQX)
    rintro x ⟨hxC, hxX⟩
    rw [← hSeq] at hxC
    have hxM : x ∈ M := hXM hxX
    have hz : (⟨piM M Q x, piM_mem_bar hxC hxM⟩ : ↥(bar M Q (Lgen M (hc.CN t)))) ∈
        Subgroup.center ↥(bar M Q (Lgen M (hc.CN t))) := by
      rw [Subgroup.mem_center_iff]
      intro s
      exact Subtype.ext (hcent _ (piM_mem_bar hxX hxM) _ s.2).symm
    rcases hSsimple.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(bar M Q (Lgen M (hc.CN t)))) with h | h
    · rw [h, Subgroup.mem_bot] at hz
      exact (piM_eq_one_iff hxM).mp (congrArg Subtype.val hz)
    · exfalso
      obtain ⟨a, b, hab⟩ := hSnonab
      apply hab
      have : a ∈ Subgroup.center ↥(bar M Q (Lgen M (hc.CN t))) := by
        rw [h]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp this b).symm
  refine ⟨?_, C₀, hC₀, hSeq, hCX, ?_⟩
  · refine ⟨fun y hy g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact hXnorm g g.2 y hy
  · rw [← hSeq]
    exact h64 G M Q Z B hc n t hs m hm hΩ

end Core



end HS6

section Certs

theorem stroth65XNormal_of_64 (h64 : Stroth64Statement) : HS6.Stroth65XNormalStatement :=
  HS6.stroth65XNormal_core ⟨stroth34Statement_unconditional,
    stroth310Root_of_34 stroth34Statement_unconditional, stroth51Statement_unconditional,
    strothNtStatement_unconditional⟩ stroth63b_holds h64

theorem stroth65Statement_of_64 (h54 : Stroth54Statement) (h64 : Stroth64Statement) :
    Stroth65Statement :=
  stroth65Statement_of_normal h54 (stroth65XNormal_of_64 h64)

end Certs

end CFSG.RankThree.GF2n.Stroth80
