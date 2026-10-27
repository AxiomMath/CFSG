module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSTwo

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace SixInv

theorem eq_zero_or_eq_of_fix {i j : Fin 6} (hij : i ≠ j) {v : permBar 6}
    (hv : ∀ σ ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)),
      barAct σ v = v) :
    v = 0 ∨ v = barInd ({i, j} : Finset (Fin 6)) := by
  classical
  have hJ := SixS.card_compl_pair hij
  have hF := klein4_fourGroup hJ
  have hN1 : klein4 ({i, j}ᶜ : Finset (Fin 6)) ≠ ⊥ := by
    intro hb
    have h4 := card_klein4 hJ
    rw [hb, Subgroup.card_bot] at h4
    omega
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
  obtain ⟨a, ha⟩ : ({i, j}ᶜ : Finset (Fin 6)).Nonempty := Finset.card_pos.1 (by omega)
  have ha' := Finset.mem_compl.1 ha
  have hai : a ≠ i := fun e => ha' (by simp [e])
  have haj : a ≠ j := fun e => ha' (by simp [e])
  have hyij : y i = y j := (Comb.fixed_swap_iff hai haj y).1
    (hv _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
  have hyJ : ∀ b ∈ ({i, j}ᶜ : Finset (Fin 6)), y b = y a := by
    intro b hb
    obtain ⟨σ, hσ, hσb⟩ := hF.transitive hJ hN1 hb ha
    have h1 := (Comb.barAct_mk_eq_self_iff (SixS.klein4_fix hij hσ).1 y).1
      (hv σ (Subgroup.mem_sup_right hσ)) b
    rwa [hσb] at h1
  have hy : ∀ m, y m = if m ∈ ({i, j} : Finset (Fin 6)) then y i else y a := by
    intro m
    split_ifs with hm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl
      · rfl
      · exact hyij.symm
    · exact hyJ m (Finset.mem_compl.2 hm)
  rcases zmod_two_cases' (y i) with h1 | h1 <;> rcases zmod_two_cases' (y a) with h2 | h2
  · left
    show (y : permBar 6) = ((0 : Fin 6 → ZMod 2) : permBar 6)
    refine bar_mk_eq_iff.2 (Or.inl fun m => ?_)
    rw [hy m, h1, h2]
    split_ifs <;> rfl
  · right
    show (y : permBar 6) = (indVec ({i, j} : Finset (Fin 6)) : permBar 6)
    refine bar_mk_eq_iff.2 (Or.inr fun m => ?_)
    rw [hy m, h1, h2]
    unfold indVec
    split_ifs <;> decide
  · right
    show (y : permBar 6) = (indVec ({i, j} : Finset (Fin 6)) : permBar 6)
    refine bar_mk_eq_iff.2 (Or.inl fun m => ?_)
    rw [hy m, h1, h2]
    unfold indVec
    split_ifs <;> rfl
  · left
    show (y : permBar 6) = ((0 : Fin 6 → ZMod 2) : permBar 6)
    refine bar_mk_eq_iff.2 (Or.inr fun m => ?_)
    rw [hy m, h1, h2]
    split_ifs <;> exact (by decide : (0 : ZMod 2) = 1 + 1)

variable {G : Type} [Group G]

theorem commutator_sup_le {K A B : Subgroup G} (hAK : A ≤ K) (hBK : B ≤ K)
    (hBn : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B) (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) :
    ⁅A, B ⊔ A⁆ ≤ B := by
  let S : Subgroup G :=
    { carrier := {w | w ∈ K ∧ ∀ a ∈ A, a * w * a⁻¹ * w⁻¹ ∈ B}
      mul_mem' := by
        rintro w₁ w₂ ⟨h₁K, h₁⟩ ⟨h₂K, h₂⟩
        refine ⟨K.mul_mem h₁K h₂K, fun a ha => ?_⟩
        have e : a * (w₁ * w₂) * a⁻¹ * (w₁ * w₂)⁻¹ =
            (a * w₁ * a⁻¹ * w₁⁻¹) * (w₁ * (a * w₂ * a⁻¹ * w₂⁻¹) * w₁⁻¹) := by group
        rw [e]
        exact B.mul_mem (h₁ a ha) (hBn w₁ h₁K _ (h₂ a ha))
      one_mem' := ⟨K.one_mem, fun a _ => by simp⟩
      inv_mem' := by
        rintro w ⟨hK, hw⟩
        refine ⟨K.inv_mem hK, fun a ha => ?_⟩
        have e : a * w⁻¹ * a⁻¹ * w⁻¹⁻¹ = w⁻¹ * (a * w * a⁻¹ * w⁻¹)⁻¹ * w⁻¹⁻¹ := by group
        rw [e]
        exact hBn _ (K.inv_mem hK) _ (B.inv_mem (hw a ha)) }
  have hBS : B ≤ S := fun b hb =>
    ⟨hBK hb, fun a ha => B.mul_mem (hBn a (hAK ha) b hb) (B.inv_mem hb)⟩
  have hAS : A ≤ S := fun a' ha' => ⟨hAK ha', fun a ha => by
    rw [hA a ha a' ha', mul_inv_cancel_right, mul_inv_cancel]
    exact B.one_mem⟩
  rw [Subgroup.commutator_le]
  intro a ha w hw
  rw [commutatorElement_def]
  exact (sup_le hBS hAS hw).2 a ha

variable [Finite G] {M X : Subgroup G}

theorem map_theta_P {n : ℕ} (C : Cfg G M X n) (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x) :
    ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ = C.thetaN x := by
  have hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M := (le_sup_left.trans h.le).trans (TOf_le_M M x)
  have e : C.thetaN x =
      ((CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M).subgroupOf M).map C.θ := by
    show ((TOf M x).subgroupOf M).map C.θ = _
    rw [h]
  rw [e, Subgroup.subgroupOf_sup hPM (pCoreOf_le_self M), Subgroup.map_sup]
  have hQ0 : ((CFSG.Open.pCoreOf 2 M).subgroupOf M).map C.θ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, C.theta_ker_eq hR]
  rw [hQ0, sup_bot_eq]

section PiData

variable {C : Cfg G M X 6}

theorem mem_T2_of_mem_centerP (D : C.PiData) (hR : Nat.card ↥(Rc X) ≤ 2)
    (hsurj : Function.Surjective C.θ) (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j})
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x) {z : G}
    (hz : z ∈ H4b.centerP x) : z ∈ C.T2 i j := by
  obtain ⟨hzP, hzc⟩ := Subgroup.mem_inf.1 hz
  have hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M := (le_sup_left.trans h.le).trans (TOf_le_M M x)
  have hcomm : ⁅CFSG.Open.pCoreOf 2 M, TOf M x⁆ ≤ CFSG.Open.pCoreOf 2 (CGOf x) := by
    rw [← h]
    exact commutator_sup_le (H4b.Q_le_CGOf C hR hx) (pCoreOf_le_self _)
      (fun k hk p hp => pCoreOf_normalized _ hk hp) (C.Q_comm hR)
  refine D.centralizer_commutator_le_T2 hR hsurj hQ16 hx hij hπ
    (Subgroup.mem_inf.2 ⟨hPM hzP, ?_⟩)
  exact Subgroup.mem_centralizer_iff.2 fun c hc => Subgroup.mem_centralizer_iff.1 hzc c (hcomm hc)

theorem piQ_cases_of_comm (D : C.PiData) (hR : Nat.card ↥(Rc X) ≤ 2)
    (hsurj : Function.Surjective C.θ) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6}
    (hij : i ≠ j) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j})
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x) {z : G}
    (hz : z ∈ CFSG.Open.pCoreOf 2 M) (hzc : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * z = z * p) :
    Multiplicative.toAdd (D.piQ ⟨z, hz⟩) = 0 ∨
      Multiplicative.toAdd (D.piQ ⟨z, hz⟩) = barInd ({i, j} : Finset (Fin 6)) := by
  refine eq_zero_or_eq_of_fix hij fun σ hσ => ?_
  rw [← D.thetaN_eq_sym hR hsurj hx hij hπ, ← map_theta_P C hR h] at hσ
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hσ
  have hcomm : z = (p : G) * z * (p : G)⁻¹ := by
    rw [hzc _ (Subgroup.mem_subgroupOf.1 hp)]
    group
  exact (D.piQ_conj p ⟨z, hz⟩ ⟨z, hz⟩ hcomm).symm

theorem conj_eq_of_mem_Q (D : C.PiData) (hR : Nat.card ↥(Rc X) ≤ 2)
    (hsurj : Function.Surjective C.θ) {r : G} (hrR : r ∈ Rc X) (hr1 : r ≠ 1) {g : G}
    (hg : g * r * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M) : g * r * g⁻¹ = r := by
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    have h' := hrR
    rw [C.S.R_eq_inf] at h'
    exact h'.1
  have hl : barLen (Multiplicative.toAdd (D.piQ ⟨r, hrQ⟩)) ≠ 2 := by
    rw [SixTwoAux.piQ_eq_one_of_mem_Rc D hrQ hrR, toAdd_one, H2.barLen_zero]
    norm_num
  exact C.R_central hR g (D.mem_M_of_conj_len_ne_two hR hsurj hrQ hr1 hl hg) r hrR

theorem conj_mul_ne (D : C.PiData) (hR : Nat.card ↥(Rc X) ≤ 2)
    (hsurj : Function.Surjective C.θ) {r : G} (hrR : r ∈ Rc X) (hr1 : r ≠ 1) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) (hx1 : x ≠ 1) {k : G} (hk : k ∈ CGOf x) (k' : G) :
    k * r * k⁻¹ * x ≠ k' * r * k'⁻¹ := by
  intro heq
  have hkx : k * x * k⁻¹ = x := mem_centralizer_zpowers_iff.1 hk
  have hkx' : k⁻¹ * x * k = x := by
    calc k⁻¹ * x * k = k⁻¹ * (k * x * k⁻¹) * k := by rw [hkx]
      _ = x := by group
  have hg : (k⁻¹ * k') * r * (k⁻¹ * k')⁻¹ = r * x := by
    calc (k⁻¹ * k') * r * (k⁻¹ * k')⁻¹ = k⁻¹ * (k' * r * k'⁻¹) * k := by group
      _ = k⁻¹ * (k * r * k⁻¹ * x) * k := by rw [heq]
      _ = r * (k⁻¹ * x * k) := by group
      _ = r * x := by rw [hkx']
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    have h' := hrR
    rw [C.S.R_eq_inf] at h'
    exact h'.1
  have h1 := conj_eq_of_mem_Q D hR hsurj hrR hr1
    (hg ▸ (CFSG.Open.pCoreOf 2 M).mul_mem hrQ hx)
  rw [hg] at h1
  exact hx1 (mul_left_cancel (h1.trans (mul_one r).symm))

theorem exists_r (D : C.PiData) (hR2 : Nat.card ↥(Rc X) = 2) (hsurj : Function.Surjective C.θ)
    {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) (hx1 : x ≠ 1) (hK : ¬ CGOf x ≤ M)
    (hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M) :
    ∃ r ∈ Rc X, r ≠ 1 ∧ r ∈ H4b.centerP x ∧
      ∃ k ∈ CGOf x, k * r * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M := by
  have hR := hR2.le
  have hQK : CFSG.Open.pCoreOf 2 M ≤ CGOf x := H4b.Q_le_CGOf C hR hx
  have hRb : Rc X ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hR2
    omega
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRb
  have hr1' : r ≠ 1 := fun h' => hr1 (Subtype.ext h')
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    have h' := hr
    rw [C.S.R_eq_inf] at h'
    exact h'.1
  have hrc : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * r = r * p := fun p hp => by
    have := C.R_central hR p (hPM hp) r hr
    calc p * r = (p * r * p⁻¹) * p := by group
      _ = r * p := by rw [this]
  have hrP : r ∈ CFSG.Open.pCoreOf 2 (CGOf x) := H4b.twoConstrained_P C hR hx hx1
    (Subgroup.mem_inf.2 ⟨hQK hrQ, Subgroup.mem_centralizer_iff.2 hrc⟩)
  have hlr : barLen (Multiplicative.toAdd (D.piQ ⟨r, hrQ⟩)) ≠ 2 := by
    rw [SixTwoAux.piQ_eq_one_of_mem_Rc D hrQ hr, toAdd_one, H2.barLen_zero]
    norm_num
  obtain ⟨k, hkK, hkQ⟩ : ∃ k ∈ CGOf x, k * r * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M := by
    by_contra hcon
    push Not at hcon
    exact hK (fun k hk => D.mem_M_of_conj_len_ne_two hR hsurj hrQ hr1' hlr (hcon k hk))
  exact ⟨r, hr, hr1', Subgroup.mem_inf.2 ⟨hrP, Subgroup.mem_centralizer_iff.2 hrc⟩, k, hkK, hkQ⟩

end PiData

end SixInv

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

section Residual

variable (hR2 : Nat.card ↥(Rc X) = 2) (hsurj : Function.Surjective C.θ)
  (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) {x : G}
  (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
  (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) (hK : ¬ CGOf x ≤ M)
  (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x)
include hR2 hsurj hQ16 hij hπ hK h

theorem sixInv_exists :
    ∃ r ∈ Rc X, r ≠ 1 ∧ ∃ t : ↥M, (t : G) * t = 1 ∧ C.θ t = swap i j ∧
      (∀ z : G, (∃ k ∈ CGOf x, z = k * r * k⁻¹) ↔ z = r ∨ z = t ∨ z = t * (x * r)) ∧
      ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * t * q⁻¹ * t⁻¹ = 1 ∨ q * t * q⁻¹ * t⁻¹ = x * r := by
  classical
  have hR := hR2.le
  have hQab := C.Q_comm hR
  have hx1 : x ≠ 1 := D.ne_one_of_len_two hx (Finset.card_pair hij) hπ
  have hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M := (le_sup_left.trans h.le).trans (TOf_le_M M x)
  have hQK : CFSG.Open.pCoreOf 2 M ≤ CGOf x := H4b.Q_le_CGOf C hR hx
  obtain ⟨r, hrR, hr1, hrZ, k₀, hk₀K, hk₀Q⟩ := SixInv.exists_r D hR2 hsurj hx hx1 hK hPM
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    have h' := hrR
    rw [C.S.R_eq_inf] at h'
    exact h'.1
  have hrx : r * x = x * r := hQab r hrQ x hx
  have hxP : x ∈ CFSG.Open.pCoreOf 2 (CGOf x) := H4b.twoConstrained_P C hR hx hx1
    (Subgroup.mem_inf.2 ⟨mem_centralizer_zpowers_iff.2 (by group),
      Subgroup.mem_centralizer_iff.2 fun p hp => by
        have h1 := mem_centralizer_zpowers_iff.1 (pCoreOf_le_self _ hp)
        calc p * x = (p * x * p⁻¹) * p := by group
          _ = x * p := by rw [h1]⟩)
  have hZ : ∀ k ∈ CGOf x, k * r * k⁻¹ ∈ H4b.centerP x := fun k hk =>
    (Subgroup.mem_normalizer_iff.1 (H4b.mem_normalizer_centerP hk) r).1 hrZ
  have hZx : ∀ z ∈ H4b.centerP x, z * x = x * z := fun z hz =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 x hxP).symm
  have hZr : ∀ z ∈ H4b.centerP x, z * r = r * z := fun z hz =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 r (Subgroup.mem_inf.1 hrZ).1).symm
  have hθZ : ∀ k ∈ CGOf x, ∀ hzM : k * r * k⁻¹ ∈ M, k * r * k⁻¹ ≠ r →
      C.θ ⟨k * r * k⁻¹, hzM⟩ = swap i j := by
    intro k hk hzM hne
    obtain ⟨hzM', hmem⟩ := C.mem_thetaPre.1
      (SixInv.mem_T2_of_mem_centerP D hR hsurj hQ16 hx hij hπ h (hZ k hk))
    rcases SixS.mem_zpowers_swap hmem with h1 | h1
    · exact absurd (SixInv.conj_eq_of_mem_Q D hR hsurj hrR hr1
        (SixTwoAux.mem_Q_of_theta_eq_one C hR hzM' h1)) hne
    · exact h1
  obtain ⟨t, ht⟩ : ∃ t : G, t = k₀ * r * k₀⁻¹ := ⟨_, rfl⟩
  have htZ : t ∈ H4b.centerP x := ht ▸ hZ k₀ hk₀K
  have htM : t ∈ M := hPM (Subgroup.mem_inf.1 htZ).1
  have hθt : C.θ ⟨t, htM⟩ = swap i j := by
    subst ht
    exact hθZ k₀ hk₀K htM fun h' => hk₀Q (by rw [h']; exact hrQ)
  have htt : t * t = 1 := by
    rw [ht]
    calc k₀ * r * k₀⁻¹ * (k₀ * r * k₀⁻¹) = k₀ * (r * r) * k₀⁻¹ := by group
      _ = 1 := by rw [Rc_mul_self hR hrR]; group
  have htx : t * x = x * t := hZx t htZ
  have htr : t * r = r * t := hZr t htZ
  have hqt : ∀ g : G, g * t * g⁻¹ = (g * k₀) * r * (g * k₀)⁻¹ := fun g => by rw [ht]; group
  have hct : ∀ q : G, q * t * q⁻¹ = (q * t * q⁻¹ * t⁻¹) * t := fun q => by group
  have hcQ : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * t * q⁻¹ * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
    intro q hq
    have e : q * t * q⁻¹ * t⁻¹ = q * (t * q⁻¹ * t⁻¹) := by group
    rw [e]
    exact (CFSG.Open.pCoreOf 2 M).mul_mem hq
      (pCoreOf_normalized M htM ((CFSG.Open.pCoreOf 2 M).inv_mem hq))
  have hdisj : ∀ k ∈ CGOf x, ∀ k' : G, k * r * k⁻¹ * x ≠ k' * r * k'⁻¹ := fun k hk k' =>
    SixInv.conj_mul_ne D hR hsurj hrR hr1 hx hx1 hk k'
  have hcx : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * t * q⁻¹ * t⁻¹ ≠ x := by
    intro q _ hc
    apply hdisj k₀ hk₀K (q * k₀)
    rw [← ht, ← hqt, hct q, hc, htx]
  have hcases : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * t * q⁻¹ * t⁻¹ = 1 ∨
      q * t * q⁻¹ * t⁻¹ = r ∨ q * t * q⁻¹ * t⁻¹ = r * x := by
    intro q hq
    rcases SixTwoAux.piQ_comm_cases D htM hθt ⟨q, hq⟩ (hcQ q hq) with h0 | h0
    · have h1 : D.piQ ⟨q * t * q⁻¹ * t⁻¹, hcQ q hq⟩ = 1 := by
        apply Multiplicative.toAdd.injective
        rw [h0]
        rfl
      rcases SixTwoAux.Rc_eq_one_or_eq hR hrR hr1 ((D.piQ_eq_one_iff _).1 h1) with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl h3)
    · have h1 : D.piQ ⟨q * t * q⁻¹ * t⁻¹, hcQ q hq⟩ = D.piQ ⟨x, hx⟩ :=
        Multiplicative.toAdd.injective (h0.trans hπ.symm)
      obtain ⟨ρ, hρ, hρe⟩ := SixTwoAux.exists_mem_Rc_of_piQ_eq D (hcQ q hq) hx h1
      rcases SixTwoAux.Rc_eq_one_or_eq hR hrR hr1 hρ with h3 | h3
      · exact absurd (by rw [hρe, h3, one_mul]) (hcx q hq)
      · exact Or.inr (Or.inr (by rw [hρe, h3]))
  obtain ⟨q₀, hq₀Q, hq₀c⟩ : ∃ q₀ ∈ CFSG.Open.pCoreOf 2 M, q₀ * t * q₀⁻¹ * t⁻¹ = r * x := by
    obtain ⟨w, -, hwc, hπw⟩ := SixTwoAux.exists_W_comm D htM hij hθt
    have hnR : (w : G) * t * (w : G)⁻¹ * t⁻¹ ∉ Rc X := by
      intro hmem
      rw [SixTwoAux.piQ_eq_one_of_mem_Rc D hwc hmem, toAdd_one] at hπw
      have h3 := congrArg barLen hπw
      rw [H2.barLen_zero, SixS.barLen_barInd_pair hij] at h3
      omega
    refine ⟨w, w.2, ?_⟩
    rcases hcases w w.2 with h1 | h1 | h1
    · exact absurd (by rw [h1]; exact (Rc X).one_mem) hnR
    · exact absurd (by rw [h1]; exact hrR) hnR
    · exact h1
  have hcomm : r * t * x = t * x * r := by
    rw [← htr, mul_assoc, hrx, ← mul_assoc]
  have hrxt : r * x * t = t * x * r := by
    rw [mul_assoc, ← htx, ← mul_assoc, hcomm]
  have hq₀t : q₀ * t * q₀⁻¹ = t * x * r := by
    rw [hct q₀, hq₀c, hrxt]
  have hcr : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * t * q⁻¹ * t⁻¹ ≠ r := by
    intro q hq hc
    apply hdisj (q * k₀) ((CGOf x).mul_mem (hQK hq) hk₀K) (q₀ * k₀)
    rw [← hqt, ← hqt, hct q, hc, hq₀t, hcomm]
  refine ⟨r, hrR, hr1, ⟨t, htM⟩, htt, hθt, fun z => ⟨?_, ?_⟩, fun q hq => ?_⟩
  · rintro ⟨k, hk, hzk⟩
    show z = r ∨ z = t ∨ z = t * (x * r)
    by_cases hzr : z = r
    · exact Or.inl hzr
    right
    have hzZ : z ∈ H4b.centerP x := hzk ▸ hZ k hk
    have hzM : z ∈ M := hPM (Subgroup.mem_inf.1 hzZ).1
    have hθz : C.θ ⟨z, hzM⟩ = swap i j := by
      subst hzk
      exact hθZ k hk hzM hzr
    have hwZ : z * t⁻¹ ∈ H4b.centerP x :=
      (H4b.centerP x).mul_mem hzZ ((H4b.centerP x).inv_mem htZ)
    have hwM : z * t⁻¹ ∈ M := M.mul_mem hzM (M.inv_mem htM)
    have hwQ : z * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
      refine SixTwoAux.mem_Q_of_theta_eq_one C hR hwM ?_
      have e : (⟨z * t⁻¹, hwM⟩ : ↥M) = ⟨z, hzM⟩ * ⟨t, htM⟩⁻¹ := rfl
      rw [e, map_mul, map_inv, hθz, hθt, mul_inv_cancel]
    have hzw : z = (z * t⁻¹) * t := by group
    rcases SixInv.piQ_cases_of_comm D hR hsurj hx hij hπ h hwQ
      (fun p hp => Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hwZ).2 p hp) with h0 | h0
    · have h1 : D.piQ ⟨z * t⁻¹, hwQ⟩ = 1 := by
        apply Multiplicative.toAdd.injective
        rw [h0]
        rfl
      rcases SixTwoAux.Rc_eq_one_or_eq hR hrR hr1 ((D.piQ_eq_one_iff _).1 h1) with h3 | h3
      ·
        change z * t⁻¹ = 1 at h3
        left
        rw [hzw, h3, one_mul]
      ·
        change z * t⁻¹ = r at h3
        exfalso
        apply hdisj k hk (q₀ * k₀)
        rw [← hzk, ← hqt, hq₀t, hzw, h3, hcomm]
    · have h1 : D.piQ ⟨z * t⁻¹, hwQ⟩ = D.piQ ⟨x, hx⟩ :=
        Multiplicative.toAdd.injective (h0.trans hπ.symm)
      obtain ⟨ρ, hρ, hρe⟩ := SixTwoAux.exists_mem_Rc_of_piQ_eq D hwQ hx h1
      rcases SixTwoAux.Rc_eq_one_or_eq hR hrR hr1 hρ with h3 | h3
      ·
        exfalso
        apply hdisj k₀ hk₀K k
        rw [← ht, ← hzk, hzw, hρe, h3, one_mul, htx]
      ·
        right
        rw [hzw, hρe, h3, hrxt, mul_assoc]
  · rintro (hz | hz | hz)
    · exact ⟨1, (CGOf x).one_mem, by rw [hz]; group⟩
    · exact ⟨k₀, hk₀K, hz.trans ht⟩
    · refine ⟨q₀ * k₀, (CGOf x).mul_mem (hQK hq₀Q) hk₀K, ?_⟩
      rw [hz]
      show t * (x * r) = _
      rw [← hqt, hq₀t, mul_assoc]
  · show q * t * q⁻¹ * t⁻¹ = 1 ∨ q * t * q⁻¹ * t⁻¹ = x * r
    rcases hcases q hq with h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd h1 (hcr q hq)
    · exact Or.inr (h1.trans hrx)

end Residual

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
