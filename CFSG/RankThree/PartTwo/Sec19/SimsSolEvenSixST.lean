module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSBase

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace SixS

variable {i j : Fin 6}

theorem card_compl_pair (hij : i ≠ j) : ({i, j}ᶜ : Finset (Fin 6)).card = 4 := by
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hij]

theorem two_mul_card_pair_lt (hij : i ≠ j) : 2 * ({i, j} : Finset (Fin 6)).card < 6 := by
  rw [Finset.card_pair hij]
  norm_num

theorem barLen_barInd_pair (hij : i ≠ j) : barLen (barInd ({i, j} : Finset (Fin 6))) = 2 := by
  rw [barLen_barInd, Finset.card_pair hij]
  rfl

theorem altOn_fix {c : Perm (Fin 6)} (hc : c ∈ altOn ({i, j}ᶜ : Finset (Fin 6))) :
    c i = i ∧ c j = j := by
  have h := (mem_altOn.1 hc).1
  exact ⟨h i (by simp), h j (by simp)⟩

theorem klein4_fix (hij : i ≠ j) {v : Perm (Fin 6)} (hv : v ∈ klein4 ({i, j}ᶜ : Finset (Fin 6))) :
    v i = i ∧ v j = j :=
  altOn_fix (klein4_le_altOn (card_compl_pair hij) hv)

theorem commute_swap_of_fix {v : Perm (Fin 6)} (hi : v i = i) (hj : v j = j) :
    v * swap i j = swap i j * v := by
  have h := Equiv.swap_apply_apply v i j
  rw [hi, hj] at h
  calc v * swap i j = (v * swap i j * v⁻¹) * v := by group
    _ = swap i j * v := by rw [← h]

theorem conj_swap_of_mem_setStab (hij : i ≠ j) {σ : Perm (Fin 6)}
    (hσ : σ ∈ setStab ({i, j} : Finset (Fin 6))) : σ * swap i j * σ⁻¹ = swap i j := by
  have hi : σ i ∈ ({i, j} : Finset (Fin 6)) := (mem_setStab.1 hσ i).2 (by simp)
  have hj : σ j ∈ ({i, j} : Finset (Fin 6)) := (mem_setStab.1 hσ j).2 (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  have hne : σ i ≠ σ j := fun h => hij (σ.injective h)
  rw [← Equiv.swap_apply_apply]
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact absurd (hi.trans hj.symm) hne
  · rw [hi, hj]
  · rw [hi, hj, Equiv.swap_comm]
  · exact absurd (hi.trans hj.symm) hne

theorem swap_mem_setStab : swap i j ∈ setStab ({i, j} : Finset (Fin 6)) := by
  rw [mem_setStab]
  intro y
  by_cases hyi : y = i
  · subst hyi
    simp
  · by_cases hyj : y = j
    · subst hyj
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne hyi hyj]

theorem klein4_le_setStab (hij : i ≠ j) :
    klein4 ({i, j}ᶜ : Finset (Fin 6)) ≤ setStab ({i, j} : Finset (Fin 6)) := fun _ hv =>
  setStab_compl_le _ ((klein4_fourGroup (card_compl_pair hij)).stab hv)

theorem zpowers_swap_le_setStab :
    Subgroup.zpowers (swap i j) ≤ setStab ({i, j} : Finset (Fin 6)) :=
  Subgroup.zpowers_le.2 swap_mem_setStab

theorem mul_self_of_mem_zpowers_swap {σ : Perm (Fin 6)} (hσ : σ ∈ Subgroup.zpowers (swap i j)) :
    σ * σ = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hσ
  rw [← zpow_add, ← two_mul, zpow_mul]
  have : swap i j ^ (2 : ℤ) = 1 := by
    rw [zpow_two, Equiv.swap_mul_self]
  rw [this, one_zpow]

theorem mem_zpowers_swap {σ : Perm (Fin 6)} (hσ : σ ∈ Subgroup.zpowers (swap i j)) :
    σ = 1 ∨ σ = swap i j := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hσ
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, Equiv.swap_mul_self, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, Equiv.swap_mul_self, one_zpow, one_mul, zpow_one]

theorem mem_sup_iff (hij : i ≠ j) {σ : Perm (Fin 6)} :
    σ ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)) ↔
      σ ∈ klein4 ({i, j}ᶜ : Finset (Fin 6)) ∨
        σ * swap i j ∈ klein4 ({i, j}ᶜ : Finset (Fin 6)) := by
  set K := klein4 ({i, j}ᶜ : Finset (Fin 6)) with hK
  set τ := swap i j with hτ
  have hcomm : ∀ v ∈ K, v * τ = τ * v := fun v hv =>
    commute_swap_of_fix (klein4_fix hij hv).1 (klein4_fix hij hv).2
  have hττ : τ * τ = 1 := Equiv.swap_mul_self i j
  constructor
  · intro hσ
    let S : Subgroup (Perm (Fin 6)) :=
      { carrier := {σ | σ ∈ K ∨ σ * τ ∈ K}
        mul_mem' := by
          rintro a b (ha | ha) (hb | hb)
          · exact Or.inl (K.mul_mem ha hb)
          · right
            rw [mul_assoc]
            exact K.mul_mem ha hb
          · right
            have e : a * b * τ = (a * τ) * b := by
              rw [mul_assoc, hcomm b hb, ← mul_assoc]
            rw [e]
            exact K.mul_mem ha hb
          · left
            have e : a * b = (a * τ) * (b * τ) := by
              have h1 : b * τ * τ = b := by rw [mul_assoc, hττ, mul_one]
              calc a * b = a * (τ * τ) * b := by rw [hττ, mul_one]
                _ = (a * τ) * (τ * b) := by group
                _ = (a * τ) * (b * τ) := by
                    rw [show τ * b = b * τ from by
                      have := hcomm (b * τ) hb
                      calc τ * b = τ * (b * τ * τ) := by rw [h1]
                        _ = τ * (b * τ) * τ := by group
                        _ = (b * τ) * τ * τ := by rw [← this]
                        _ = b * τ := by rw [mul_assoc (b * τ), hττ, mul_one]]
            rw [e]
            exact K.mul_mem ha hb
        one_mem' := Or.inl K.one_mem
        inv_mem' := by
          rintro a (ha | ha)
          · exact Or.inl (K.inv_mem ha)
          · right
            have h1 : (a * τ)⁻¹ ∈ K := K.inv_mem ha
            have h2 := hcomm _ h1
            have e : a⁻¹ * τ = (a * τ)⁻¹ := by
              calc a⁻¹ * τ = τ * (τ * a⁻¹) * τ := by
                    rw [← mul_assoc, hττ, one_mul]
                _ = τ * (a * τ)⁻¹ * τ := by rw [mul_inv_rev, show τ⁻¹ = τ from Equiv.swap_inv i j]
                _ = (a * τ)⁻¹ * τ * τ := by rw [← h2]
                _ = (a * τ)⁻¹ := by rw [mul_assoc, hττ, mul_one]
            rw [e]
            exact h1 }
    have hle : Subgroup.zpowers τ ⊔ K ≤ S := sup_le
      (Subgroup.zpowers_le.2 (Or.inr (by rw [hττ]; exact K.one_mem))) (fun v hv => Or.inl hv)
    exact hle hσ
  · rintro (h | h)
    · exact Subgroup.mem_sup_right h
    · have e : σ = (σ * τ) * τ := by rw [mul_assoc, hττ, mul_one]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers τ))

theorem exists_conj_ne (hij : i ≠ j) {v : Perm (Fin 6)}
    (hv : v ∈ klein4 ({i, j}ᶜ : Finset (Fin 6))) (hv1 : v ≠ 1) :
    ∃ c ∈ altOn ({i, j}ᶜ : Finset (Fin 6)), c * v * c⁻¹ ≠ v := by
  classical
  set J : Finset (Fin 6) := {i, j}ᶜ with hJdef
  have hJ : J.card = 4 := card_compl_pair hij
  have hF := klein4_fourGroup hJ
  obtain ⟨a, haJ, hva⟩ : ∃ a ∈ J, v a ≠ a := by
    by_contra hcon
    push Not at hcon
    apply hv1
    ext y
    by_cases hy : y ∈ J
    · simp [hcon y hy]
    · simp [hF.fix v hv y hy]
  set b := v a with hb
  have hbJ : b ∈ J := (mem_setStab.1 (hF.stab hv) a).2 haJ
  obtain ⟨c', hc'J, hc's⟩ := exists_fourth hJ {a, b} (Finset.card_le_two.trans (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc's
  obtain ⟨hc'a, hc'b⟩ := hc's
  obtain ⟨c'', hc''J, hc''s⟩ := exists_fourth hJ {a, b, c'} Finset.card_le_three
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc''s
  obtain ⟨hc''a, hc''b, hc''c'⟩ := hc''s
  refine ⟨cyc a c'' c', cyc_mem_altOn_of_mem haJ hc''J hc'J (Ne.symm hc''a) (Ne.symm hc'a)
    hc''c', fun heq => ?_⟩
  have hca : cyc a c'' c' a = c' := cyc_apply_first (Ne.symm hc'a) hc''c'
  have hcb : cyc a c'' c' b = b := cyc_apply_of_ne hva (Ne.symm hc''b) (Ne.symm hc'b)
  have hcinv : (cyc a c'' c')⁻¹ c' = a := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hca.symm
  have h1 := congrArg (fun f : Perm (Fin 6) => f c') heq
  simp only [Perm.mul_apply, hcinv] at h1
  rw [← hb, hcb] at h1
  exact hc'a (v.injective (h1.symm.trans hb))

theorem perm_cases (hij : i ≠ j) {F : Subgroup (Perm (Fin 6))}
    (hF : F ≤ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)))
    (hn : ∀ c ∈ altOn ({i, j}ᶜ : Finset (Fin 6)), ∀ σ ∈ F, c * σ * c⁻¹ ∈ F) :
    F = ⊥ ∨ F = Subgroup.zpowers (swap i j) ∨ F = klein4 ({i, j}ᶜ : Finset (Fin 6)) ∨
      F = Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)) := by
  classical
  set K := klein4 ({i, j}ᶜ : Finset (Fin 6)) with hK
  set τ := swap i j with hτ
  have hJ := card_compl_pair hij
  have hFK := klein4_fourGroup hJ
  have hττ : τ * τ = 1 := Equiv.swap_mul_self i j
  have hτinv : τ⁻¹ = τ := Equiv.swap_inv i j
  have hKn : ∀ c ∈ altOn ({i, j}ᶜ : Finset (Fin 6)), ∀ v ∈ K, c * v * c⁻¹ ∈ K := fun c hc v hv =>
    klein4_conj_mem hJ (altOn_le_setStab _ hc) hv
  set F₀ : Subgroup (Perm (Fin 6)) := F ⊓ K with hF₀
  have hF₀n : ∀ c ∈ altOn ({i, j}ᶜ : Finset (Fin 6)), ∀ σ ∈ F₀, c * σ * c⁻¹ ∈ F₀ :=
    fun c hc σ hσ => Subgroup.mem_inf.2 ⟨hn c hc σ (Subgroup.mem_inf.1 hσ).1,
      hKn c hc σ (Subgroup.mem_inf.1 hσ).2⟩
  by_cases hF₀bot : F₀ = ⊥
  ·
    have hFle : F ≤ Subgroup.zpowers τ := by
      intro σ hσ
      rcases (mem_sup_iff hij).1 (hF hσ) with h | h
      · have : σ ∈ F₀ := Subgroup.mem_inf.2 ⟨hσ, h⟩
        rw [hF₀bot, Subgroup.mem_bot] at this
        rw [this]
        exact Subgroup.one_mem _
      · set v := σ * τ with hvdef
        have hσv : σ = v * τ := by rw [hvdef, mul_assoc, hττ, mul_one]
        by_cases hv1 : v = 1
        · rw [hσv, hv1, one_mul]
          exact Subgroup.mem_zpowers τ
        · exfalso
          obtain ⟨c, hc, hcv⟩ := exists_conj_ne hij h hv1
          have hcτ : c * τ = τ * c := commute_swap_of_fix (altOn_fix hc).1 (altOn_fix hc).2
          have hw : c * σ * c⁻¹ * σ⁻¹ = (c * v * c⁻¹) * v⁻¹ := by
            have hcτ' : c * τ * c⁻¹ = τ := by rw [hcτ]; group
            calc c * σ * c⁻¹ * σ⁻¹ = (c * v * c⁻¹) * (c * τ * c⁻¹) * (τ⁻¹ * v⁻¹) := by
                  rw [hσv]; group
              _ = (c * v * c⁻¹) * v⁻¹ := by rw [hcτ', hτinv, ← mul_assoc, mul_assoc _ τ τ, hττ,
                  mul_one]
          have hwF : (c * v * c⁻¹) * v⁻¹ ∈ F₀ := by
            rw [← hw]
            refine Subgroup.mem_inf.2 ⟨F.mul_mem (hn c hc σ hσ) (F.inv_mem hσ), ?_⟩
            rw [hw]
            exact K.mul_mem (hKn c hc v h) (K.inv_mem h)
          rw [hF₀bot, Subgroup.mem_bot, mul_inv_eq_one] at hwF
          exact hcv hwF
    by_cases hFbot : F = ⊥
    · exact Or.inl hFbot
    · right; left
      refine le_antisymm hFle (Subgroup.zpowers_le.2 ?_)
      obtain ⟨⟨σ, hσ⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hFbot
      have hσ1' : σ ≠ 1 := fun h => hσ1 (Subtype.ext h)
      rcases mem_zpowers_swap (hFle hσ) with h | h
      · exact absurd h hσ1'
      · rw [hτ, ← h]
        exact hσ
  ·
    have hF₀K : F₀ = K := hFK.eq_of_le hJ inf_le_right hF₀bot hF₀n
    have hKF : K ≤ F := fun v hv => (Subgroup.mem_inf.1 (hF₀K.symm ▸ hv : v ∈ F₀)).1
    by_cases hFK' : F = K
    · right; right; left
      exact hFK'
    · right; right; right
      refine le_antisymm hF (sup_le (Subgroup.zpowers_le.2 ?_) hKF)
      obtain ⟨σ, hσF, hσK⟩ : ∃ σ ∈ F, σ ∉ K := by
        by_contra hcon
        push Not at hcon
        exact hFK' (le_antisymm hcon hKF)
      rcases (mem_sup_iff hij).1 (hF hσF) with h | h
      · exact absurd h hσK
      · have e : τ = σ⁻¹ * (σ * τ) := by group
        rw [e]
        exact F.mul_mem (F.inv_mem hσF) (hKF h)

end SixS

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

variable (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ) {x : G}
  (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
  (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j})
include hR hsurj hij hπ

theorem CMOf_eq_thetaPre :
    CMOf M x = C.thetaPre (setStab ({i, j} : Finset (Fin 6))) := by
  ext m
  rw [C.mem_thetaPre]
  constructor
  · intro hm
    have hmM : m ∈ M := (Subgroup.mem_inf.1 hm).1
    exact ⟨hmM, D.theta_mem_setStab_of_mem_CMOf_six hx (SixS.two_mul_card_pair_lt hij) hπ
      (k := ⟨m, hmM⟩) hm⟩
  · rintro ⟨hmM, hθ⟩
    refine Subgroup.mem_inf.2 ⟨hmM, mem_centralizer_zpowers_iff.2 ?_⟩
    have hfix : barAct (C.θ ⟨m, hmM⟩) (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) =
        Multiplicative.toAdd (D.piQ ⟨x, hx⟩) := by
      rw [hπ]
      exact (barAct_barInd_eq_self_iff (SixS.two_mul_card_pair_lt hij) _).2 hθ
    have hl : barLen (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) = 2 := by
      rw [hπ]
      exact SixS.barLen_barInd_pair hij
    exact D.comm_of_barAct_eq_len_two hR hx hl (m := ⟨m, hmM⟩) hfix

theorem thetaPre_le_TOf {F : Subgroup (Perm (Fin 6))}
    (hFs : F ≤ setStab ({i, j} : Finset (Fin 6)))
    (hFn : ∀ σ ∈ setStab ({i, j} : Finset (Fin 6)), ∀ f ∈ F, σ * f * σ⁻¹ ∈ F)
    (hFsq : ∀ f ∈ F, f * f = 1) : C.thetaPre F ≤ TOf M x := by
  have hCM := D.CMOf_eq_thetaPre hR hsurj hx hij hπ
  have hle : C.thetaPre F ≤ CMOf M x := by
    rw [hCM]
    exact C.thetaPre_mono hFs
  refine le_pCoreOf_of_normalized hle (fun k hk u hu => ?_) ?_
  · have hk' : k ∈ CMOf M x := hk
    rw [hCM] at hk'
    obtain ⟨hkM, hkθ⟩ := C.mem_thetaPre.1 hk'
    obtain ⟨huM, huθ⟩ := C.mem_thetaPre.1 hu
    refine C.mem_thetaPre.2 ⟨M.mul_mem (M.mul_mem hkM huM) (M.inv_mem hkM), ?_⟩
    have e : (⟨k * u * k⁻¹, M.mul_mem (M.mul_mem hkM huM) (M.inv_mem hkM)⟩ : ↥M) =
        ⟨k, hkM⟩ * ⟨u, huM⟩ * ⟨k, hkM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact hFn _ hkθ _ huθ
  · refine isPGroup_two_of_forall fun u hu => ?_
    obtain ⟨huM, huθ⟩ := C.mem_thetaPre.1 hu
    have hK : u * u ∈ C.K := by
      refine C.mem_K.2 ⟨M.mul_mem huM huM, ?_⟩
      have e : (⟨u * u, M.mul_mem huM huM⟩ : ↥M) = ⟨u, huM⟩ * ⟨u, huM⟩ := rfl
      rw [e, map_mul, hFsq _ huθ]
    rw [C.K_eq_Q hR] at hK
    obtain ⟨j', hj'⟩ := exists_two_pow_of_mem_pCoreOf M hK
    refine ⟨j' + 1, ?_⟩
    rw [pow_succ, mul_comm, pow_mul, pow_two]
    exact hj'

theorem T2_le_TOf : C.T2 i j ≤ TOf M x :=
  D.thetaPre_le_TOf hR hsurj hx hij hπ SixS.zpowers_swap_le_setStab
    (fun σ hσ f hf => by
      rcases SixS.mem_zpowers_swap hf with rfl | rfl
      · rw [mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [SixS.conj_swap_of_mem_setStab hij hσ]
        exact Subgroup.mem_zpowers _)
    (fun f hf => SixS.mul_self_of_mem_zpowers_swap hf)

theorem T1_le_TOf : C.T1 i j ≤ TOf M x :=
  D.thetaPre_le_TOf hR hsurj hx hij hπ (SixS.klein4_le_setStab hij)
    (fun σ hσ f hf => klein4_conj_mem (SixS.card_compl_pair hij) (mem_setStab_compl hσ) hf)
    (fun f hf => ((mem_klein4_iff (SixS.card_compl_pair hij)).1 hf).2)

theorem thetaN_eq_sym :
    C.thetaN x = Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)) := by
  classical
  set K := klein4 ({i, j}ᶜ : Finset (Fin 6)) with hK
  set τ := swap i j with hτ
  have hJ := SixS.card_compl_pair hij
  have hτT : τ ∈ C.thetaN x := by
    obtain ⟨m, hm⟩ := hsurj τ
    refine C.mem_thetaN.2 ⟨m, D.T2_le_TOf hR hsurj hx hij hπ (C.mem_thetaPre.2 ⟨m.2, ?_⟩), hm⟩
    rw [show (⟨(m : G), m.2⟩ : ↥M) = m from rfl, hm]
    exact Subgroup.mem_zpowers _
  have hKT : K ≤ C.thetaN x := D.klein4_le_thetaN_six hR hx (Finset.card_pair hij) hπ
  refine le_antisymm (fun σ hσ => ?_) (sup_le (Subgroup.zpowers_le.2 hτT) hKT)
  let F₀ : Subgroup (Perm (Fin 6)) :=
    { carrier := {σ | σ ∈ C.thetaN x ∧ σ i = i ∧ σ j = j}
      mul_mem' := fun {a b} ha hb => ⟨(C.thetaN x).mul_mem ha.1 hb.1, by
        simp [Perm.mul_apply, ha.2.1, hb.2.1], by simp [Perm.mul_apply, ha.2.2, hb.2.2]⟩
      one_mem' := ⟨(C.thetaN x).one_mem, rfl, rfl⟩
      inv_mem' := fun {a} ha => ⟨(C.thetaN x).inv_mem ha.1, by
        rw [Equiv.Perm.inv_eq_iff_eq]; exact ha.2.1.symm, by
        rw [Equiv.Perm.inv_eq_iff_eq]; exact ha.2.2.symm⟩ }
  have hstabT : ∀ σ ∈ C.thetaN x, σ ∈ setStab ({i, j} : Finset (Fin 6)) := fun σ hσ =>
    D.thetaN_le_setStab_six hx (SixS.two_mul_card_pair_lt hij) hπ hσ
  have hF₀ : FourGroup ({i, j}ᶜ : Finset (Fin 6)) F₀ :=
    { two := (C.isPGroup_thetaN x).to_le (fun σ hσ => hσ.1)
      stab := fun σ hσ => mem_setStab_compl (hstabT σ hσ.1)
      fix := fun σ hσ y hy => by
        have hy' : y ∈ ({i, j} : Finset (Fin 6)) := by
          rw [Finset.mem_compl, not_not] at hy
          exact hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
        rcases hy' with rfl | rfl
        · exact hσ.2.1
        · exact hσ.2.2
      norm := fun c hc σ hσ => by
        obtain ⟨hci, hcj⟩ := SixS.altOn_fix hc
        have hci' : c⁻¹ i = i := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hci.symm
        have hcj' : c⁻¹ j = j := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hcj.symm
        refine ⟨D.thetaN_normalized_six hx (SixS.two_mul_card_pair_lt hij) hπ (Or.inr rfl) c hc σ
          hσ.1, ?_, ?_⟩
        · simp [Perm.mul_apply, hci', hσ.2.1, hci]
        · simp [Perm.mul_apply, hcj', hσ.2.2, hcj] }
  have hKF₀ : K ≤ F₀ := fun v hv =>
    ⟨hKT hv, (SixS.klein4_fix hij hv).1, (SixS.klein4_fix hij hv).2⟩
  have hF₀K : F₀ = K := (Subgroup.eq_of_le_of_card_ge hKF₀ (by
    rw [card_klein4 hJ]; exact hF₀.card_le_four hJ)).symm
  have hσs := hstabT σ hσ
  have hi : σ i ∈ ({i, j} : Finset (Fin 6)) := (mem_setStab.1 hσs i).2 (by simp)
  have hj : σ j ∈ ({i, j} : Finset (Fin 6)) := (mem_setStab.1 hσs j).2 (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  have hne : σ i ≠ σ j := fun h => hij (σ.injective h)
  rw [SixS.mem_sup_iff hij]
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact absurd (hi.trans hj.symm) hne
  · left
    have : σ ∈ F₀ := ⟨hσ, hi, hj⟩
    rwa [hF₀K] at this
  · right
    have hmem : σ * τ ∈ F₀ := ⟨(C.thetaN x).mul_mem hσ hτT, by
      simp [hτ, Perm.mul_apply, Equiv.swap_apply_left, hj], by
      simp [hτ, Perm.mul_apply, Equiv.swap_apply_right, hi]⟩
    rwa [hF₀K] at hmem
  · exact absurd (hi.trans hj.symm) hne

theorem TOf_eq_thetaPre :
    TOf M x = C.thetaPre (Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6))) := by
  rw [← D.thetaN_eq_sym hR hsurj hx hij hπ]
  exact C.eq_thetaPre hR (Q_le_TOf (C.Q_comm hR) hx) (TOf_le_M M x)

theorem normal_cases {N : Subgroup G} (hQN : CFSG.Open.pCoreOf 2 M ≤ N) (hNT : N ≤ TOf M x)
    (hNn : ∀ k ∈ CMOf M x, ∀ u ∈ N, k * u * k⁻¹ ∈ N) :
    N = CFSG.Open.pCoreOf 2 M ∨ N = C.T2 i j ∨ N = C.T1 i j ∨ N = TOf M x := by
  have hNM : N ≤ M := hNT.trans (TOf_le_M M x)
  set F : Subgroup (Perm (Fin 6)) := (N.subgroupOf M).map C.θ with hFdef
  have hFT : F ≤ C.thetaN x := Subgroup.map_mono fun m hm => hNT hm
  rw [D.thetaN_eq_sym hR hsurj hx hij hπ] at hFT
  have hFn : ∀ c ∈ altOn ({i, j}ᶜ : Finset (Fin 6)), ∀ σ ∈ F, c * σ * c⁻¹ ∈ F := by
    intro c hc σ hσ
    obtain ⟨k, hkC, hkθ⟩ := Subgroup.mem_map.1
      (D.altOn_le_theta_CMOf_six hx (SixS.two_mul_card_pair_lt hij) hπ (Or.inr rfl) hc)
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hσ
    have hkC' : (k : G) ∈ CMOf M x := Subgroup.mem_subgroupOf.1 hkC
    have hkuN : (k : G) * (u : G) * (k : G)⁻¹ ∈ N :=
      hNn _ hkC' _ (Subgroup.mem_subgroupOf.1 hu)
    refine Subgroup.mem_map.2 ⟨k * u * k⁻¹, Subgroup.mem_subgroupOf.2 hkuN, ?_⟩
    rw [map_mul, map_mul, map_inv, hkθ]
  have hN := C.eq_thetaPre hR hQN hNM
  rw [← hFdef] at hN
  have hbot : C.thetaPre ⊥ = CFSG.Open.pCoreOf 2 M := by
    refine le_antisymm (fun g hg => ?_) (C.Q_le_thetaPre hR ⊥)
    obtain ⟨hgM, hgθ⟩ := C.mem_thetaPre.1 hg
    have : (⟨g, hgM⟩ : ↥M) ∈ C.θ.ker := by
      rw [MonoidHom.mem_ker]
      exact Subgroup.mem_bot.1 hgθ
    rw [C.theta_ker_eq hR] at this
    exact this
  rcases SixS.perm_cases hij hFT hFn with h | h | h | h
  · left
    rw [hN, h, hbot]
  · right; left
    rw [hN, h]
  · right; right; left
    rw [hN, h]
  · right; right; right
    rw [hN, h, ← D.TOf_eq_thetaPre hR hsurj hx hij hπ]

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
