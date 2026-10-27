module

public import CFSG.RankThree.GF2n.Stroth80.Core4Line
public import CFSG.RankThree.GF2n.Stroth80.Sec97FiveLineX
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91Cent
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreA

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem not_le_sup_of_hard (hc : Ctx M Q Z B) {X : Subgroup G} {h : G} (hh : h ∈ M)
    (hex : ∃ x ∈ LB M Q B ⊓ X, x ∉ Q)
    (hhard : ∀ x ∈ LB M Q B ⊓ X, x ∉ Q → x ∉ conjSubgroup h (LB M Q B)) :
    ¬ conjSubgroup h B ≤ Z ⊔ B := by
  intro hle
  have hle' : conjSubgroup h B ≤ B ⊔ Z := by rwa [sup_comm]
  have hL := hc.conj_LB_eq_of_le_sup_Z hh hle'
  obtain ⟨x, hxE, hxQ⟩ := hex
  apply hhard x hxE hxQ
  rw [hL]
  exact hxE.1

theorem comm_mem_Z_of_normalizes_LF (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B) (hFsup : ¬ conjSubgroup h B ≤ Z ⊔ B)
    (h35F : CQt Q Z (LB M Q (conjSubgroup h B)) =
      ((conjSubgroup h B ⊔ Z : Subgroup G) : Set G)) {x : G} (hxL : x ∈ LB M Q B)
    (hxN : conjSubgroup x (LB M Q (conjSubgroup h B)) = LB M Q (conjSubgroup h B)) :
    ∀ f ∈ conjSubgroup h B, ⁅x, f⁆ ∈ Z := by
  intro f hf
  have hcF : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hxM : x ∈ M := hc.LB_le_M hxL
  have hxN' : x ∈ Subgroup.normalizer ((conjSubgroup h B ⊔ Z : Subgroup G) : Set G) :=
    (hcF.mem_normalizer_LB_iff h35F hxM).mp (conjSubgroup_eq_self_iff.mp hxN)
  have h1 : ⁅x, f⁆ ∈ (Z ⊔ B : Subgroup G) :=
    hc.comm_LB_inf_QB_mem_sup hxL ⟨hcF.le hf, hFB hf⟩
  have h2 : ⁅x, f⁆ ∈ (Z ⊔ conjSubgroup h B : Subgroup G) := by
    have h3 : x * f * x⁻¹ ∈ (conjSubgroup h B ⊔ Z : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp hxN' f).mp (Subgroup.mem_sup_left hf)
    have h4 : f⁻¹ ∈ (conjSubgroup h B ⊔ Z : Subgroup G) :=
      Subgroup.inv_mem _ (Subgroup.mem_sup_left hf)
    have h5 : x * f * x⁻¹ * f⁻¹ ∈ (conjSubgroup h B ⊔ Z : Subgroup G) :=
      Subgroup.mul_mem _ h3 h4
    rw [sup_comm]
    simpa [commutatorElement_def] using h5
  obtain ⟨z, hz, f', hf', hzf⟩ := (Smith81.Ctx.mem_sup_iff hcF).mp h2
  have hf'W : f' ∈ (Z ⊔ B : Subgroup G) := by
    have e : f' = z⁻¹ * ⁅x, f⁆ := by rw [hzf]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hz)) h1
  have hf'1 : f' = 1 := eq_one_of_mem_sup_of_not_le hc hcF hFsup hf' hf'W
  rw [hzf, hf'1, mul_one]
  exact hz

theorem comm_congr_mem_Q (hc : Ctx M Q Z B) {y k : G} (hyM : y ∈ M) (hkM : k ∈ M) {q : G}
    (hq : q ∈ Q) : ⁅y, k⁆⁻¹ * ⁅y, k * q⁆ ∈ Q := by
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have e : ⁅y, k⁆⁻¹ * ⁅y, k * q⁆ = k * ⁅y, q⁆ * k⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  have hyq : ⁅y, q⁆ ∈ Q := by
    have h5 := (Subgroup.mem_normalizer_iff.mp (hQn hyM) q).mp hq
    have e5 : ⁅y, q⁆ = (y * q * y⁻¹) * q⁻¹ := by
      simp only [commutatorElement_def]
    rw [e5]
    exact Q.mul_mem h5 (Q.inv_mem hq)
  exact (Subgroup.mem_normalizer_iff.mp (hQn hkM) _).mp hyq

theorem kappaBar_comm_mem_Q (hc : Ctx M Q Z B) {X : Subgroup G} {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B) (hne : conjSubgroup h B ≠ B)
    (hhard : ∀ x ∈ LB M Q B ⊓ X, x ∉ Q → h * x * h⁻¹ ∉ LB M Q B) {y : G} (hy : y ∈ LB M Q B)
    (hyN : conjSubgroup y (LB M Q (conjSubgroup h B)) ≠ LB M Q (conjSubgroup h B)) {k : G}
    (hk : k ∈ conjSubgroup h (LB M Q B ⊓ X)) (hyk : ⁅y, k⁆ ∈ Q) : k ∈ Q := by
  have hLF : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hQh : conjSubgroup h Q = Q := hc.conj_Q_eq hh
  have hkLF : k ∈ LB M Q (conjSubgroup h B) := by
    rw [hLF]
    exact Subgroup.map_mono inf_le_left hk
  have hyk' : y * k * y⁻¹ ∈ conjSubgroup y (LB M Q (conjSubgroup h B)) :=
    ⟨k, hkLF, by simp [MulAut.conj_apply]⟩
  have hykF : y * k * y⁻¹ ∈ LB M Q (conjSubgroup h B) := by
    have e2 : y * k * y⁻¹ = ⁅y, k⁆ * k := by
      simp only [commutatorElement_def]
      group
    rw [e2]
    exact (LB M Q (conjSubgroup h B)).mul_mem (Subgroup.mem_sup_left hyk) hkLF
  have hykL := mem_LB_of_mem_conj_swap hc hh hFB hne hy hyN hykF hyk'
  have hkL : k ∈ LB M Q B := by
    have e3 : k = y⁻¹ * (y * k * y⁻¹) * y := by group
    rw [e3]
    exact (LB M Q B).mul_mem ((LB M Q B).mul_mem ((LB M Q B).inv_mem hy) hykL) hy
  by_contra hkQ
  have hxE : h⁻¹ * k * h ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp hk
  have hxQ : h⁻¹ * k * h ∉ Q := by
    intro hxQ'
    apply hkQ
    have : h * (h⁻¹ * k * h) * h⁻¹ ∈ conjSubgroup h Q := ⟨_, hxQ', by simp [MulAut.conj_apply]⟩
    rw [hQh, show h * (h⁻¹ * k * h) * h⁻¹ = k by group] at this
    exact this
  apply hhard _ hxE hxQ
  rw [show h * (h⁻¹ * k * h) * h⁻¹ = k by group]
  exact hkL

theorem kappaBar_comm_inj (hc : Ctx M Q Z B) {X : Subgroup G} {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B) (hne : conjSubgroup h B ≠ B)
    (hhard : ∀ x ∈ LB M Q B ⊓ X, x ∉ Q → h * x * h⁻¹ ∉ LB M Q B) {y : G} (hy : y ∈ LB M Q B)
    (hyN : conjSubgroup y (LB M Q (conjSubgroup h B)) ≠ LB M Q (conjSubgroup h B)) {k₁ k₂ : G}
    (hk₁ : k₁ ∈ conjSubgroup h (LB M Q B ⊓ X)) (hk₂ : k₂ ∈ conjSubgroup h (LB M Q B ⊓ X))
    (hc12 : ⁅y, k₁⁆⁻¹ * ⁅y, k₂⁆ ∈ Q) : k₁⁻¹ * k₂ ∈ Q := by
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hLF : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hLFM : conjSubgroup h (LB M Q B) ≤ M := by
    rw [← hLF]
    exact (hc.conj_of_mem hh).LB_le_M
  have hk₁M : k₁ ∈ M := hLFM (Subgroup.map_mono inf_le_left hk₁)
  have hkK : k₁⁻¹ * k₂ ∈ conjSubgroup h (LB M Q B ⊓ X) :=
    (conjSubgroup h (LB M Q B ⊓ X)).mul_mem (Subgroup.inv_mem _ hk₁) hk₂
  have e : ⁅y, k₁⁆⁻¹ * ⁅y, k₂⁆ = k₁ * ⁅y, k₁⁻¹ * k₂⁆ * k₁⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e] at hc12
  have hycomm : ⁅y, k₁⁻¹ * k₂⁆ ∈ Q := by
    have h5 := (Subgroup.mem_normalizer_iff.mp (hQn (M.inv_mem hk₁M)) _).mp hc12
    simpa [mul_assoc] using h5
  exact kappaBar_comm_mem_Q hc hh hFB hne hhard hy hyN hkK hycomm

theorem conj_conj_LF_of_mem (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B) (hne : conjSubgroup h B ≠ B) {y : G} (hy : y ∈ LB M Q B)
    {k : G} (hkF : k ∈ LB M Q (conjSubgroup h B)) (hkL : conjSubgroup k (LB M Q B) = LB M Q B) :
    conjSubgroup k (conjSubgroup y (LB M Q (conjSubgroup h B))) =
      conjSubgroup y (LB M Q (conjSubgroup h B)) := by
  have hcF : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hyM : y ∈ M := hc.LB_le_M hy
  have hline := lineGeom_of_QB hc hh hFB
  have hlineS := lineGeom_swap hc hh hFB hne
  have hFy : conjSubgroup y (conjSubgroup h B) ≤
      Z ⊔ conjSubgroup h B ⊔ conjSubgroup h⁻¹ (conjSubgroup h B) := by
    rw [conjSubgroup_inv_conj_self]
    have h1 : conjSubgroup y (Z ⊔ B ⊔ conjSubgroup h B) = Z ⊔ B ⊔ conjSubgroup h B :=
      hline.1 y (Subgroup.mem_sup_left hy)
    calc conjSubgroup y (conjSubgroup h B)
        ≤ conjSubgroup y (Z ⊔ B ⊔ conjSubgroup h B) := Subgroup.map_mono le_sup_right
      _ = Z ⊔ B ⊔ conjSubgroup h B := h1
      _ = Z ⊔ conjSubgroup h B ⊔ B := sup_right_comm _ _ _
  have hP := hlineS.2 (conjSubgroup y (conjSubgroup h B)) ⟨y, hyM, rfl⟩ hFy
  rw [hcF.LB_conj hyM, conjSubgroup_inv_conj_self] at hP
  rcases hP with h1 | ⟨ε, hε, h2⟩
  · rw [h1]
    exact conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hkF)
  · rw [h2]
    have hq : ⁅ε⁻¹, k⁆ ∈ Q := hcF.commutator_LB_le_Q
      (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hε) hkF)
    have hQL : Q ≤ LB M Q B := le_sup_left
    have hc1 : conjSubgroup (ε⁻¹ * k * ε) (LB M Q B) = LB M Q B := by
      have e : ε⁻¹ * k * ε = ⁅ε⁻¹, k⁆ * k := by
        simp only [commutatorElement_def]
        group
      rw [e, conjSubgroup_mul, hkL]
      exact conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer (hQL hq))
    calc conjSubgroup k (conjSubgroup ε (LB M Q B))
        = conjSubgroup (k * ε) (LB M Q B) := (conjSubgroup_mul _ _ _).symm
      _ = conjSubgroup (ε * (ε⁻¹ * k * ε)) (LB M Q B) := by
          rw [show ε * (ε⁻¹ * k * ε) = k * ε by group]
      _ = conjSubgroup ε (conjSubgroup (ε⁻¹ * k * ε) (LB M Q B)) := conjSubgroup_mul _ _ _
      _ = conjSubgroup ε (LB M Q B) := by rw [hc1]

theorem comm_mem_normalizer_of_mem (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B) (hne : conjSubgroup h B ≠ B) {y : G} (hy : y ∈ LB M Q B)
    {k : G} (hkF : k ∈ LB M Q (conjSubgroup h B)) (hkL : conjSubgroup k (LB M Q B) = LB M Q B) :
    conjSubgroup ⁅y, k⁆ (LB M Q (conjSubgroup h B)) = LB M Q (conjSubgroup h B) := by
  have h1 := conj_conj_LF_of_mem hc hh hFB hne ((LB M Q B).inv_mem hy) hkF hkL
  have e : ⁅y, k⁆ = (y * k * y⁻¹) * k⁻¹ := by simp only [commutatorElement_def]
  have hk' : conjSubgroup k⁻¹ (LB M Q (conjSubgroup h B)) = LB M Q (conjSubgroup h B) :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.inv_mem _ (Subgroup.le_normalizer hkF))
  have h2 : conjSubgroup (y * k * y⁻¹) (LB M Q (conjSubgroup h B)) =
      LB M Q (conjSubgroup h B) := by
    rw [conjSubgroup_mul, conjSubgroup_mul, h1, ← conjSubgroup_mul, mul_inv_cancel,
      conjSubgroup_one]
  rw [e, conjSubgroup_mul, hk', h2]

theorem relIndex_Q_LB_inf_CN (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) : Q.relIndex (LB M Q B ⊓ hc.CN t) = Nat.card Z ^ (n - 3) := by
  have hQT : Q ≤ LB M Q B ⊓ hc.CN t := le_inf le_sup_left (sec9_Q_le_CN hc hs.toSec5.mem)
  have h1 := Subgroup.relIndex_mul_relIndex Q (LB M Q B ⊓ hc.CN t) (LB M Q B) hQT inf_le_left
  have h2 : (LB M Q B ⊓ hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact relIndex_LB_CN h34 hs
  rw [h2, relIndex_Q_LB h34 hc hs.toSec5] at h1
  have hn3 : 3 ≤ n := hs.toSec5.n_gt
  have hpow : Nat.card Z ^ (n - 1) = Nat.card Z ^ (n - 3) * Nat.card Z ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hpos : 0 < Nat.card Z ^ 2 := pow_pos Nat.card_pos 2
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, hpow])

theorem inf_CN_le_normalizer (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y) (h2 : TwoConcl M Q B X) {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B)
    (hhard : ∀ x ∈ LB M Q B ⊓ X, x ∉ Q →
      h * x * h⁻¹ ∉ LB M Q B ∧ x ∉ conjSubgroup h (LB M Q B))
    (hHK : ∀ k ∈ conjSubgroup h (LB M Q B ⊓ X) ⊓
      Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G),
      conjSubgroup k (LB M Q B ⊓ hc.CN t) = LB M Q B ⊓ hc.CN t) :
    ∀ y ∈ LB M Q B ⊓ hc.CN t,
      conjSubgroup y (LB M Q (conjSubgroup h B)) = LB M Q (conjSubgroup h B) := by
  classical
  intro y hy
  by_contra hyN
  have hex := exists_mem_E_not_Q h34 hc hs hsplit h4
  have hne : conjSubgroup h B ≠ B := conj_ne_of_hard h34 hc hs hsplit h4 hh hhard
  have hhard1 : ∀ x ∈ LB M Q B ⊓ X, x ∉ Q → h * x * h⁻¹ ∉ LB M Q B :=
    fun x hx hxQ => (hhard x hx hxQ).1
  have hLF : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hLM : LB M Q B ≤ M := hc.LB_le_M
  have hLFM : conjSubgroup h (LB M Q B) ≤ M := by
    rw [← hLF]
    exact (hc.conj_of_mem hh).LB_le_M
  have hyL : y ∈ LB M Q B := hy.1
  have hyM : y ∈ M := hLM hyL
  set T := LB M Q B ⊓ hc.CN t with hTdef
  set LF := LB M Q (conjSubgroup h B) with hLFdef
  set K := conjSubgroup h (LB M Q B ⊓ X) ⊓
    Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G) with hKdef
  let S : Subgroup G := T ⊓ Subgroup.normalizer (LF : Set G)
  have hQLF : Q ≤ LF := le_sup_left
  have hQT : Q ≤ T := le_inf le_sup_left (sec9_Q_le_CN hc hs.toSec5.mem)
  have hQS : Q ≤ S := le_inf hQT (hQLF.trans Subgroup.le_normalizer)
  have hKL : ∀ k ∈ K, conjSubgroup k (LB M Q B) = LB M Q B := fun k hk =>
    conj_LB_eq_of_mem_kappaBar hc hh hFB (fun x hx hxQ => (hhard x hx hxQ).2) hex hk.1
      (conjSubgroup_eq_self_iff.mpr hk.2)
  have hKF : ∀ k ∈ K, k ∈ LF := fun k hk => by
    show k ∈ LB M Q (conjSubgroup h B)
    rw [hc.LB_conj hh]
    exact Subgroup.map_mono inf_le_left hk.1
  have hmap : ∀ k ∈ K, ⁅y, k⁆ ∈ S := by
    intro k hk
    refine ⟨?_, conjSubgroup_eq_self_iff.mp
      (comm_mem_normalizer_of_mem hc hh hFB hne hyL (hKF k hk) (hKL k hk))⟩
    have hmem : k * y⁻¹ * k⁻¹ ∈ conjSubgroup k T :=
      ⟨y⁻¹, T.inv_mem hy, by simp [MulAut.conj_apply]⟩
    rw [hHK k hk] at hmem
    have e : ⁅y, k⁆ = y * (k * y⁻¹ * k⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact T.mul_mem hy hmem
  have hcongr : ∀ k ∈ K, ∀ r ∈ Q, ⁅y, k⁆⁻¹ * ⁅y, k * r⁆ ∈ Q := fun k hk r hr =>
    comm_congr_mem_Q hc hyM (hLFM (Subgroup.map_mono inf_le_left hk.1)) hr
  have hinj : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ⁅y, k₁⁆⁻¹ * ⁅y, k₂⁆ ∈ Q → k₁⁻¹ * k₂ ∈ Q :=
    fun k₁ hk₁ k₂ hk₂ hc12 => kappaBar_comm_inj hc hh hFB hne hhard1 hyL hyN hk₁.1 hk₂.1 hc12
  have hle := relIndex_le_of_commutator_injective (R := Q) (K := K) (Q := Q) (S := S) y hmap
    hcongr hinj
  have hge := relIndex_kappaBar_ge h34 hc hs hsplit h4 h2 hh
    (relIndex_normalizer_LB_le_swap hc hh hFB hne)
  have hTcard := relIndex_Q_LB_inf_CN h34 hc hs
  have hmul := Subgroup.relIndex_mul_relIndex Q S T hQS (inf_le_left : S ≤ T)
  have hpos : 0 < S.relIndex T := relIndex_pos' _ _
  have h3 : Nat.card Z ^ (n - 3) ≤ Q.relIndex S := hge.trans hle
  have ha : 0 < Q.relIndex S := lt_of_lt_of_le (pow_pos Nat.card_pos _) h3
  rw [hTcard] at hmul
  have h5 : Q.relIndex S * S.relIndex T ≤ Q.relIndex S * 1 := by
    rw [mul_one, hmul]
    exact h3
  have h6 : S.relIndex T ≤ 1 := Nat.le_of_mul_le_mul_left h5 ha
  have h1' : S.relIndex T = 1 := by omega
  have hTS : T ≤ S := Subgroup.relIndex_eq_one.mp h1'
  exact hyN (conjSubgroup_eq_self_iff.mpr (hTS hy).2)

theorem hard_false_of_normalizes_inf_CN (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hn5 : Sec9NGeFiveStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y)
    (h1 : OneConcl hc X Y) (h2 : TwoConcl M Q B X) {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B)
    (hhard : ∀ x ∈ LB M Q B ⊓ X, x ∉ Q →
      h * x * h⁻¹ ∉ LB M Q B ∧ x ∉ conjSubgroup h (LB M Q B))
    (hHK : ∀ k ∈ conjSubgroup h (LB M Q B ⊓ X) ⊓
      Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G),
      conjSubgroup k (LB M Q B ⊓ hc.CN t) = LB M Q B ⊓ hc.CN t) : False := by
  classical
  have hs5 := hs.toSec5
  have hex := exists_mem_E_not_Q h34 hc hs hsplit h4
  have hne : conjSubgroup h B ≠ B := conj_ne_of_hard h34 hc hs hsplit h4 hh hhard
  have hcF : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hFsup : ¬ conjSubgroup h B ≤ Z ⊔ B :=
    not_le_sup_of_hard hc hh hex (fun x hx hxQ => (hhard x hx hxQ).2)
  have h35F : CQt Q Z (LB M Q (conjSubgroup h B)) =
      ((conjSubgroup h B ⊔ Z : Subgroup G) : Set G) :=
    (stroth_3_5 h34 hcF hs5.width hs5.n_gt (hc.noA2_conj hs5.noA2 hh)
      (hs5.gen.conj_of_mem hh)).2.1
  have hT := inf_CN_le_normalizer h34 hc hs hsplit h4 h2 hh hFB hhard hHK
  have hS := S_normalizes_LF_of_hard h34 hc hs (hn5 G M Q Z B hc n t hs) hsplit h4 h1 h2 hh hFB
    hhard
  have hFV : conjSubgroup h B ≤ Vt M (LB M Q B) B Z t := fun f hf =>
    centLam91 h34 hs f ⟨hcF.le hf, hFB hf⟩ (fun l hl =>
      comm_mem_Z_of_normalizes_LF hc hh hFB hFsup h35F (Subgroup.mem_sup_right hl.1)
        (hT l ⟨Subgroup.mem_sup_right hl.1, hl.2⟩) f hf)
  have hFU : ∀ f ∈ conjSubgroup h B, f ∈ Uline Z B X := fun f hf =>
    mem_ulineX_of_fix h34 h311a hc hs hsplit h4 (hFV hf)
      (fun y hy => comm_mem_Z_of_normalizes_LF hc hh hFB hFsup h35F hy.1 (hS y hy) f hf)
  obtain ⟨f₀, hf₀, hf₀1⟩ := exists_ne_one_mem hcF
  obtain ⟨-, -, hcover, -⟩ := ulineX_data h34 h311a hc hs hsplit
  obtain ⟨x, hxX, hfx⟩ := hcover f₀ (hFU f₀ hf₀)
  have hxR : x ∈ Rt M (LB M Q B) t := hsplit.1.2.1 hxX
  have hxM : x ∈ M := hc.Rt_le_M t hxR
  have hcx : Ctx M Q Z (conjSubgroup x B) := hc.conj_of_mem hxM
  have hFx : conjSubgroup h B ≤ Z ⊔ conjSubgroup x B := by
    by_contra hnot
    exact hf₀1 (eq_one_of_mem_sup_of_not_le hcx hcF hnot hf₀ (by rwa [sup_comm] at hfx))
  have hLx : conjSubgroup h (LB M Q B) = conjSubgroup x (LB M Q B) := by
    have hle : conjSubgroup (h * x⁻¹) (conjSubgroup x B) ≤ conjSubgroup x B ⊔ Z := by
      rw [← conjSubgroup_mul, show h * x⁻¹ * x = h by group, sup_comm]
      exact hFx
    have hL := hcx.conj_LB_eq_of_le_sup_Z (M.mul_mem hh (M.inv_mem hxM)) hle
    rw [hc.LB_conj hxM, ← conjSubgroup_mul, show h * x⁻¹ * x = h by group] at hL
    exact hL
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre hs5.mem
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) hs5.mem hZ0
  have htN : t ∈ hc.CN t := isCentrePre_le_CN91 hs hZ0 htZ0
  have htX : t ∈ X := (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1 htN
  have htF : t ∈ conjSubgroup h (LB M Q B) := by
    rw [hLx, mem_conjSubgroup]
    have hxinv : x⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem hxR
    have hq : ⁅x⁻¹, t⁆ ∈ Q := hc.Rt_comm_mem_Q hxinv
    have e : x⁻¹ * t * x = ⁅x⁻¹, t⁆ * t := by
      simp only [commutatorElement_def, inv_inv]
      group
    rw [e]
    exact (LB M Q B).mul_mem (Subgroup.mem_sup_left hq) hs5.mem
  exact (hhard t ⟨hs5.mem, htX⟩ hs5.notQ).2 htF

end HS9

end CFSG.RankThree.GF2n.Stroth80
