module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517A5Phi

public section

namespace CFSG.Quasithin.H13.A5Push

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin Equiv

variable {G : Type} [Group G]

theorem conj_map_conj_map (X : Subgroup G) (a b : G) :
    (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      X.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem conj_map_one (X : Subgroup G) : X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
  ext x
  rw [mem_conj_map]
  simp

theorem isElemAbelian_conj_map {X : Subgroup G} (hX : IsElemAbelian 2 X) (k : G) :
    IsElemAbelian 2 (X.map (MulAut.conj k).toMonoidHom) := by
  refine isElemAbelian_of_mul_self fun y hy => ?_
  rw [mem_conj_map] at hy
  have h1 : (k⁻¹ * y * k) * (k⁻¹ * y * k) = 1 := by rw [← pow_two]; exact hX.2 _ hy
  have e : y * y = k * ((k⁻¹ * y * k) * (k⁻¹ * y * k)) * k⁻¹ := by group
  rw [e, h1]
  group

theorem mem_centralizer_sup {H K : Subgroup G} {x : G}
    (hH : x ∈ Subgroup.centralizer (H : Set G)) (hK : x ∈ Subgroup.centralizer (K : Set G)) :
    x ∈ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) := by
  have h1 : Subgroup.zpowers x ≤ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hH))
      (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hK))
  exact h1 (Subgroup.mem_zpowers x)

theorem two_mul_le_of_dvd_of_lt {d N : ℕ} (hd : d ∣ N) (hlt : d < N) : 2 * d ≤ N := by
  obtain ⟨e, rfl⟩ := hd
  rcases e with _ | _ | e
  · omega
  · omega
  · nlinarith

theorem sup_eq_of_card_ge [Finite G] {H₁ H₂ K : Subgroup G} (h₁ : H₁ ≤ K) (h₂ : H₂ ≤ K)
    (hc₁ : Nat.card K ≤ 2 * Nat.card H₁) (hc₂ : Nat.card K ≤ 2 * Nat.card H₂) (hne : H₁ ≠ H₂) :
    H₁ ⊔ H₂ = K := by
  have hJ : H₁ ⊔ H₂ ≤ K := sup_le h₁ h₂
  by_contra hJK
  have hlt : Nat.card ↥(H₁ ⊔ H₂) < Nat.card K := by
    rcases (Subgroup.card_le_of_le hJ).lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hJ h.ge) hJK
  have h2 := two_mul_le_of_dvd_of_lt (Subgroup.card_dvd_of_le hJ) hlt
  have e₁ : H₁ = H₁ ⊔ H₂ := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
  have e₂ : H₂ = H₁ ⊔ H₂ := Subgroup.eq_of_le_of_card_ge le_sup_right (by omega)
  exact hne (e₁.trans e₂.symm)

@[expose] def e4List : List (Perm (Fin 5)) := [1, swap 0 1, swap 2 3, swap 0 1 * swap 2 3]

theorem mem_e4List {σ : Perm (Fin 5)} (h : InE4 σ) : σ ∈ e4List := by
  rcases (inE4_iff σ).1 h with rfl | rfl | rfl | rfl <;> simp [e4List]

theorem e4_cases_aux : ∀ σ ∈ e4List, ∀ τ ∈ e4List, ∀ ε ∈ e4List, σ ≠ 1 → τ ≠ 1 → τ ≠ σ →
    (ε = 1 ∨ ε = σ ∨ ε = τ ∨ ε = σ * τ) := by
  decide +kernel

theorem e4_cases (σ τ ε : Perm (Fin 5)) (hσ : InE4 σ) (hτ : InE4 τ) (hε : InE4 ε) (h1 : σ ≠ 1)
    (h2 : τ ≠ 1) (h3 : τ ≠ σ) : ε = 1 ∨ ε = σ ∨ ε = τ ∨ ε = σ * τ :=
  e4_cases_aux σ (mem_e4List hσ) τ (mem_e4List hτ) ε (mem_e4List hε) h1 h2 h3

theorem fixCard2_swap_swap : fixCard2 (swap 0 1) (swap 2 3) = 4 ∧
    fixCard2 (swap 2 3) (swap 0 1) = 4 := by
  decide +kernel

variable [Finite G]

namespace Setting

variable {T M L W : Subgroup G} {F : S5Frame (L ⊔ T) W} {n : ℕ}

theorem mem_of_commute {A : Subgroup G} (hA : IsMaxElemAbelian T A) {x : G} (hxT : x ∈ T)
    (hx2 : x * x = 1) (hxA : ∀ a ∈ A, a * x = x * a) : x ∈ A := by
  have hzN : Subgroup.zpowers x ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj (fun a ha => ?_) fun a ha => ?_
    · rw [← hxA a ha, mul_inv_cancel_right]
      exact ha
    · have h1 : x⁻¹ * a * x = a := by
        calc x⁻¹ * a * x = x⁻¹ * (a * x) := by group
          _ = x⁻¹ * (x * a) := by rw [hxA a ha]
          _ = a := by group
      rw [h1]
      exact ha
  have hB : IsElemAbelian 2 (A ⊔ Subgroup.zpowers x) := by
    refine isElemAbelian_of_mul_self fun y hy => ?_
    have hy' : y ∈ ((A ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A _ hzN] at hy'
    obtain ⟨a, ha, z, hz, rfl⟩ := Set.mem_mul.mp hy'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hc : Commute a (x ^ j) := (Commute.zpow_right (hxA a ha) j)
    have ha2 : a * a = 1 := by rw [← pow_two]; exact hA.2.1.2 a ha
    have hxj : x ^ j * x ^ j = 1 := by
      rw [← zpow_add, ← two_mul, zpow_mul]
      have : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx2
      rw [this, one_zpow]
    rw [← hc.mul_mul_mul_comm a (x ^ j), ha2, hxj, one_mul]
  have hBT : A ⊔ Subgroup.zpowers x ≤ T := sup_le hA.1 (Subgroup.zpowers_le.mpr hxT)
  have heq : A = A ⊔ Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (hA.2.2 _ hBT hB)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem isMax_Q (hs : Setting T M L W F n)
    (hQ : IsElemAbelian 2 (baum T ⊓ Subgroup.centralizer (W : Set G))) :
    IsMaxElemAbelian T (baum T ⊓ Subgroup.centralizer (W : Set G)) := by
  obtain ⟨A, hA, hAW⟩ := hs.hB.exists_offender
  have heq := (hs.hB.offender_eq hA hAW).2
  have hmax := isMaxElemAbelian_sup_of_eq hs.hB.el hs.hB.WT
    (isMaxElemAbelian_iff_corank_zero.mp hA) (by rw [pow_zero, mul_one]; exact heq)
  have hAS : A ≤ baum T :=
    (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ T).trans (B2F.thompsonJ_le_baum T)
  have hle : (A ⊓ Subgroup.centralizer (W : Set G)) ⊔ W ≤
      baum T ⊓ Subgroup.centralizer (W : Set G) :=
    sup_le (inf_le_inf_right _ hAS) hs.W_le_Q
  refine ⟨inf_le_left.trans (S_le_T T), hQ, fun B hBT hB => ?_⟩
  exact (hmax.2.2 B hBT hB).trans (Subgroup.card_le_of_le hle)

omit [Finite G] in
theorem isMax_conj {A : Subgroup G} (hA : IsMaxElemAbelian T A) (hAS : A ≤ baum T) {k : G}
    (hk : k ∈ Subgroup.normalizer (baum T : Set G)) :
    IsMaxElemAbelian T (A.map (MulAut.conj k).toMonoidHom) := by
  refine ⟨(conj_le_S hAS hk).trans (S_le_T T), isElemAbelian_conj_map hA.2.1 k,
    fun B hBT hB => ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
  exact hA.2.2 B hBT hB

theorem sup_eq_of_surj (hs : Setting T M L W F n) {R : Subgroup G} (hR : R ≤ baum T)
    (h : ∀ ε : Perm (Fin 5), InE4 ε → ∃ r : ↥(L ⊔ T), (r : G) ∈ R ∧ F.ρ r = ε) :
    (baum T ⊓ Subgroup.centralizer (W : Set G)) ⊔ R = baum T := by
  refine le_antisymm (sup_le inf_le_left hR) fun s hsS => ?_
  set s' : ↥(L ⊔ T) := ⟨s, Subgroup.mem_sup_right (S_le_T T hsS)⟩ with hs'
  obtain ⟨r, hrR, hr⟩ := h (F.ρ s') (hs.hB.rho_baum s' hsS)
  have hqS : ((s' * r⁻¹ : ↥(L ⊔ T)) : G) ∈ baum T :=
    (baum T).mul_mem hsS ((baum T).inv_mem (hR hrR))
  have hq : ((s' * r⁻¹ : ↥(L ⊔ T)) : G) ∈ baum T ⊓ Subgroup.centralizer (W : Set G) := by
    rw [← hs.rho_eq_one_iff _ hqS, map_mul, map_inv, hr, mul_inv_cancel]
  have e : s = ((s' * r⁻¹ : ↥(L ⊔ T)) : G) * r := by simp [hs']
  rw [e]
  exact Subgroup.mul_mem_sup hq hrR

theorem exists_partner (hs : Setting T M L W F n)
    (hQ : IsElemAbelian 2 (baum T ⊓ Subgroup.centralizer (W : Set G))) {k₀ : G}
    (hk₀ : k₀ ∈ Subgroup.normalizer (baum T : Set G))
    (hk₀W : ¬ W.map (MulAut.conj k₀).toMonoidHom ≤ baum T ⊓ Subgroup.centralizer (W : Set G)) :
    ∃ k ∈ Subgroup.normalizer (baum T : Set G),
      (baum T ⊓ Subgroup.centralizer (W : Set G)) ⊔
        (baum T ⊓ Subgroup.centralizer (W : Set G)).map (MulAut.conj k).toMonoidHom =
        baum T := by
  classical
  set Q := baum T ⊓ Subgroup.centralizer (W : Set G) with hQdef
  have hQmax := hs.isMax_Q hQ
  have hQS : Q ≤ baum T := inf_le_left
  set R := Q.map (MulAut.conj k₀).toMonoidHom with hRdef
  have hRS : R ≤ baum T := conj_le_S hQS hk₀
  have hRmax : IsMaxElemAbelian T R := isMax_conj hQmax hQS hk₀
  by_cases hQR : Q ⊔ R = baum T
  · exact ⟨k₀, hk₀, hQR⟩
  have hRY : R ≤ L ⊔ T := hRS.trans ((S_le_T T).trans le_sup_right)
  have hWR : W.map (MulAut.conj k₀).toMonoidHom ≤ R := Subgroup.map_mono hs.W_le_Q
  obtain ⟨w₀, hw₀, hw₀Q⟩ := Set.not_subset.mp hk₀W
  set r₀ : ↥(L ⊔ T) := ⟨w₀, hRY (hWR hw₀)⟩ with hr₀
  have hr₀R : (r₀ : G) ∈ R := hWR hw₀
  have hσ1 : F.ρ r₀ ≠ 1 := fun h1 => hw₀Q ((hs.rho_eq_one_iff r₀ (hRS hr₀R)).1 h1)
  have hσE : InE4 (F.ρ r₀) := hs.hB.rho_baum r₀ (hRS hr₀R)
  have hRσ : ∀ r : ↥(L ⊔ T), (r : G) ∈ R → F.ρ r = 1 ∨ F.ρ r = F.ρ r₀ := by
    intro r hr
    by_contra hcon
    push Not at hcon
    apply hQR
    refine hs.sup_eq_of_surj hRS fun ε hε => ?_
    rcases e4_cases (F.ρ r₀) (F.ρ r) ε hσE (hs.hB.rho_baum r (hRS hr)) hε hσ1 hcon.1 hcon.2 with
      h | h | h | h
    · exact ⟨1, R.one_mem, by rw [h, map_one]⟩
    · exact ⟨r₀, hr₀R, h.symm⟩
    · exact ⟨r, hr, h.symm⟩
    · exact ⟨r₀ * r, R.mul_mem hr₀R hr, by rw [map_mul, h]⟩
  have hrange : Nat.card (F.ρOn hRY).range ≤ 2 := by
    have hsub : ((F.ρOn hRY).range : Set (Perm (Fin 5))) ⊆ ({1, F.ρ r₀} : Finset _) := by
      rintro _ ⟨r, rfl⟩
      rcases hRσ (Subgroup.inclusion hRY r) r.2 with h | h
      · simp [S5Frame.ρOn, h]
      · simp [S5Frame.ρOn, h]
    have h1 := Nat.card_mono (Finset.finite_toSet _) hsub
    rw [Nat.card_coe_set_eq (({1, F.ρ r₀} : Finset (Perm (Fin 5))) : Set (Perm (Fin 5))),
      Set.ncard_coe_finset] at h1
    exact h1.trans (Finset.card_le_two)
  have hineq := card_le_relIndex_mul_card hs.hB.el hs.hB.WT hRmax
  rw [F.relIndex_eq_card_range hRY, F.card_W] at hineq
  have hCW : 8 ≤ Nat.card ↥(W ⊓ Subgroup.centralizer (R : Set G)) := by
    have := Nat.mul_le_mul_right (Nat.card ↥(W ⊓ Subgroup.centralizer (R : Set G))) hrange
    omega
  have hfix := F.card_fix_le (A := R) hr₀R
  have hσsw := d5_transposition_of_fix _ hσE hσ1 (by omega)
  obtain ⟨t, htT, ht⟩ := hs.hB.DT (swap 0 2 * swap 1 3) (by decide)
  have htD : InD8 (F.ρ t) := by rw [ht]; decide
  have htE : ¬ InE4 (F.ρ t) := by rw [ht]; decide
  have hcs := d5_conj_swap (F.ρ t) htD htE
  have htN : (t : G) ∈ Subgroup.normalizer (baum T : Set G) := T_le_normalizer_S T htT
  set R' := R.map (MulAut.conj (t : G)).toMonoidHom with hR'def
  have hR'S : R' ≤ baum T := conj_le_S hRS htN
  have hR'max : IsMaxElemAbelian T R' := isMax_conj hRmax hRS htN
  have hR'Y : R' ≤ L ⊔ T := hR'S.trans ((S_le_T T).trans le_sup_right)
  set r₀' : ↥(L ⊔ T) := t * r₀ * t⁻¹ with hr₀'
  have hr₀'R : (r₀' : G) ∈ R' := conj_mem_conj_map hr₀R
  have hσ' : F.ρ r₀' = F.ρ t * F.ρ r₀ * (F.ρ t)⁻¹ := by rw [hr₀', map_mul, map_mul, map_inv]
  have hX : W ⊓ Subgroup.centralizer (R : Set G) ≤ R := by
    intro x hx
    refine mem_of_commute hRmax (hs.hB.WT hx.1) ?_ fun a ha => ?_
    · rw [← pow_two]; exact hs.hB.el.2 x hx.1
    · exact Subgroup.mem_centralizer_iff.mp hx.2 a ha
  have hne : Q ⊓ R ≠ Q ⊓ R' := by
    intro heq
    have hXR' : W ⊓ Subgroup.centralizer (R : Set G) ≤ R' := fun x hx =>
      (heq ▸ (⟨hs.W_le_Q hx.1, hX hx⟩ : x ∈ Q ⊓ R) : x ∈ Q ⊓ R').2
    have hle : W ⊓ Subgroup.centralizer (R : Set G) ≤
        W ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
      intro x hx
      refine ⟨hx.1, mem_centralizer_sup hx.2 ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := hR'max.2.1.1
      exact setLike_mul_comm hy (hXR' hx)
    have h4 := F.card_fix_le_two (A := R ⊔ R') (a := r₀) (b := r₀')
      (Subgroup.mem_sup_left hr₀R) (Subgroup.mem_sup_right hr₀'R)
    have h5 : fixCard2 (F.ρ r₀) (F.ρ r₀') = 4 := by
      rw [hσ']
      rcases hσsw with h | h
      · rw [h, hcs.1]; exact fixCard2_swap_swap.1
      · rw [h, hcs.2]; exact fixCard2_swap_swap.2
    have h6 := Subgroup.card_le_of_le hle
    omega
  have hcardR : Nat.card R ≤ 2 * Nat.card ↥(Q ⊓ R) := by
    have h1 := Subgroup.relIndex_mul_card (R ⊓ Subgroup.centralizer (W : Set G)) R
    rw [F.relIndex_eq_card_range hRY] at h1
    have h2 : (R ⊓ Subgroup.centralizer (W : Set G)) ⊓ R = Q ⊓ R := by
      ext x
      simp only [Subgroup.mem_inf, hQdef]
      exact ⟨fun h => ⟨⟨hRS h.2, h.1.2⟩, h.2⟩, fun h => ⟨⟨h.2, h.1.2⟩, h.2⟩⟩
    rw [h2] at h1
    have := Nat.mul_le_mul_right (Nat.card ↥(Q ⊓ R)) hrange
    omega
  have hcardR' : Nat.card R' ≤ 2 * Nat.card ↥(Q ⊓ R') := by
    have hR'σ : ∀ r : ↥(L ⊔ T), (r : G) ∈ R' → F.ρ r = 1 ∨ F.ρ r = F.ρ r₀' := by
      intro r hr
      rw [mem_conj_map] at hr
      set r₁ : ↥(L ⊔ T) := t⁻¹ * r * t with hr₁
      have hr₁R : (r₁ : G) ∈ R := by rw [hr₁]; exact hr
      have e : r = t * r₁ * t⁻¹ := by rw [hr₁]; group
      rcases hRσ r₁ hr₁R with h | h
      · left; rw [e, map_mul, map_mul, map_inv, h, mul_one, mul_inv_cancel]
      · right; rw [e, map_mul, map_mul, map_inv, h, hσ']
    have hrange' : Nat.card (F.ρOn hR'Y).range ≤ 2 := by
      have hsub : ((F.ρOn hR'Y).range : Set (Perm (Fin 5))) ⊆ ({1, F.ρ r₀'} : Finset _) := by
        rintro _ ⟨r, rfl⟩
        rcases hR'σ (Subgroup.inclusion hR'Y r) r.2 with h | h
        · simp [S5Frame.ρOn, h]
        · simp [S5Frame.ρOn, h]
      have h1 := Nat.card_mono (Finset.finite_toSet _) hsub
      rw [Nat.card_coe_set_eq (({1, F.ρ r₀'} : Finset (Perm (Fin 5))) : Set (Perm (Fin 5))),
        Set.ncard_coe_finset] at h1
      exact h1.trans (Finset.card_le_two)
    have h1 := Subgroup.relIndex_mul_card (R' ⊓ Subgroup.centralizer (W : Set G)) R'
    rw [F.relIndex_eq_card_range hR'Y] at h1
    have h2 : (R' ⊓ Subgroup.centralizer (W : Set G)) ⊓ R' = Q ⊓ R' := by
      ext x
      simp only [Subgroup.mem_inf, hQdef]
      exact ⟨fun h => ⟨⟨hR'S h.2, h.1.2⟩, h.2⟩, fun h => ⟨⟨h.2, h.1.2⟩, h.2⟩⟩
    rw [h2] at h1
    have := Nat.mul_le_mul_right (Nat.card ↥(Q ⊓ R')) hrange'
    omega
  have hcQR : Nat.card R = Nat.card Q :=
    Subgroup.card_map_of_injective (MulAut.conj k₀).injective
  have hcQR' : Nat.card R' = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj (t : G)).injective
  have hQRR : Q ≤ R ⊔ R' := by
    have h1 := sup_eq_of_card_ge (inf_le_left : Q ⊓ R ≤ Q) (inf_le_left : Q ⊓ R' ≤ Q)
      (by omega) (by omega) hne
    rw [← h1]
    exact sup_le_sup inf_le_right inf_le_right
  have hSRR : R ⊔ R' = baum T := by
    refine le_antisymm (sup_le hRS hR'S) ?_
    have h1 : Q ⊔ (R ⊔ R') = baum T := by
      refine hs.sup_eq_of_surj (sup_le hRS hR'S) fun ε hε => ?_
      have hσ'E : InE4 (F.ρ r₀') := hs.hB.rho_baum r₀' (hR'S hr₀'R)
      have hσ'1 : F.ρ r₀' ≠ 1 := by
        rw [hσ']
        rcases hσsw with h | h
        · rw [h, hcs.1]; decide
        · rw [h, hcs.2]; decide
      have hσ'ne : F.ρ r₀' ≠ F.ρ r₀ := by
        rw [hσ']
        rcases hσsw with h | h
        · rw [h, hcs.1]; decide
        · rw [h, hcs.2]; decide
      rcases e4_cases (F.ρ r₀) (F.ρ r₀') ε hσE hσ'E hε hσ1 hσ'1 hσ'ne with h | h | h | h
      · exact ⟨1, Subgroup.one_mem _, by rw [h, map_one]⟩
      · exact ⟨r₀, Subgroup.mem_sup_left hr₀R, h.symm⟩
      · exact ⟨r₀', Subgroup.mem_sup_right hr₀'R, h.symm⟩
      · exact ⟨r₀ * r₀', Subgroup.mul_mem _ (Subgroup.mem_sup_left hr₀R)
          (Subgroup.mem_sup_right hr₀'R), by rw [map_mul, h]⟩
    rw [← h1]
    exact sup_le hQRR le_rfl
  refine ⟨k₀⁻¹ * t * k₀, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hk₀) htN) hk₀
  have hSk : (baum T).map (MulAut.conj k₀⁻¹).toMonoidHom = baum T :=
    Subgroup.eq_of_le_of_card_ge (conj_le_S le_rfl (Subgroup.inv_mem _ hk₀))
      (Subgroup.card_map_of_injective (MulAut.conj k₀⁻¹).injective).ge
  rw [← hSk, ← hSRR, Subgroup.map_sup, hR'def, hRdef, conj_map_conj_map, conj_map_conj_map,
    conj_map_conj_map, inv_mul_cancel, conj_map_one, mul_assoc]

theorem conj_W_not_le_of_partner (hs : Setting T M L W F n)
    (hQ : IsElemAbelian 2 (baum T ⊓ Subgroup.centralizer (W : Set G))) {k : G}
    (hk : k ∈ Subgroup.normalizer (baum T : Set G))
    (hpart : (baum T ⊓ Subgroup.centralizer (W : Set G)) ⊔
      (baum T ⊓ Subgroup.centralizer (W : Set G)).map (MulAut.conj k).toMonoidHom = baum T) :
    ¬ W.map (MulAut.conj k).toMonoidHom ≤ baum T ⊓ Subgroup.centralizer (W : Set G) := by
  intro hle
  set Q := baum T ⊓ Subgroup.centralizer (W : Set G) with hQdef
  have hWQk : W ≤ Q.map (MulAut.conj k).toMonoidHom := by
    intro w hw
    rw [mem_conj_map]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk) w).mp
        (hs.hB.le_baum hw)
      simpa using this
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 := (hle (conj_mem_conj_map hv : k * v * k⁻¹ ∈ W.map _)).2
      have h2 := Subgroup.mem_centralizer_iff.mp h1 w hw
      calc v * (k⁻¹ * w * k) = k⁻¹ * ((k * v * k⁻¹) * w) * k := by group
        _ = k⁻¹ * (w * (k * v * k⁻¹)) * k := by rw [h2]
        _ = k⁻¹ * w * k * v := by group
  have hQkC : Q.map (MulAut.conj k).toMonoidHom ≤ Subgroup.centralizer (W : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := (isElemAbelian_conj_map hQ k).1
    exact setLike_mul_comm (hWQk hw) hx
  have hSC : baum T ≤ Subgroup.centralizer (W : Set G) := by
    rw [← hpart]
    exact sup_le inf_le_right hQkC
  obtain ⟨s, hsS, hs1⟩ := hs.hB.rho_baum_surj (swap 0 1) (by decide)
  have h1 := (F.ρ_eq_one_iff s).2 (hSC hsS)
  rw [hs1] at h1
  exact absurd h1 (by decide)

theorem QC_le_partner (hs : Setting T M L W F n)
    (hQ : IsElemAbelian 2 (baum T ⊓ Subgroup.centralizer (W : Set G))) {k : G}
    (hk : k ∈ Subgroup.normalizer (baum T : Set G))
    (hpart : (baum T ⊓ Subgroup.centralizer (W : Set G)) ⊔
      (baum T ⊓ Subgroup.centralizer (W : Set G)).map (MulAut.conj k).toMonoidHom = baum T) :
    baum T ⊓ Subgroup.centralizer (L : Set G) ≤
      (baum T ⊓ Subgroup.centralizer (W : Set G)).map (MulAut.conj k).toMonoidHom := by
  have hki : k⁻¹ ∈ Subgroup.normalizer (baum T : Set G) := Subgroup.inv_mem _ hk
  set Q := baum T ⊓ Subgroup.centralizer (W : Set G) with hQdef
  have hpart' : Q ⊔ Q.map (MulAut.conj k⁻¹).toMonoidHom = baum T := by
    have hSk : (baum T).map (MulAut.conj k⁻¹).toMonoidHom = baum T :=
      Subgroup.eq_of_le_of_card_ge (conj_le_S le_rfl hki)
        (Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective).ge
    rw [← hSk, ← hpart, Subgroup.map_sup, conj_map_conj_map, inv_mul_cancel, conj_map_one,
      sup_comm]
  have h1 := hs.QC_conj_le hki (hs.conj_W_not_le_of_partner hQ hki hpart')
  intro c hc
  rw [mem_conj_map]
  have h2 := h1 (conj_mem_conj_map hc)
  rwa [inv_inv] at h2

end Setting

end CFSG.Quasithin.H13.A5Push
