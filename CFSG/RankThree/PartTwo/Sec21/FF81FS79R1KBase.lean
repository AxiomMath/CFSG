module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79SZ
public import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79KStmt
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Quo

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

structure FS79Hyp1 {G : Type} [Group G] (b t c : G) (J : Subgroup G) : Prop where
  ord_b : orderOf b = 3
  ord_t : orderOf t = 2
  inv_b : t * b * t⁻¹ = b⁻¹
  J_perm : Nonempty (↥J ≃* Equiv.Perm (Fin 3))
  J_le_cen_b : J ≤ Cen b
  J_le_cen_t : J ≤ Cen t
  N_le_NJ : Nor (Subgroup.zpowers b) ≤ Nor J
  N_eq : setMul (Opp 3 (Nor (Subgroup.zpowers b))) (Subgroup.closure {b, t} ⊔ J) =
    Nor (Subgroup.zpowers b)
  c_mem : c ∈ J
  ord_c : orderOf c = 3
  N_c : setMul (Opp 3 (Nor (Subgroup.zpowers c)))
    (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers c)) = Nor (Subgroup.zpowers c)
  no_two : ∀ R : Subgroup G, IsPGroup 2 R → Subgroup.closure {b, c} ≤ Nor R → R = ⊥
  weak : ∀ h : G, conjBy h (Subgroup.zpowers b) ≤ Nor (Subgroup.zpowers b) →
    conjBy h (Subgroup.zpowers b) = Subgroup.zpowers b

theorem prop2OneAt_iff (G : Type) [Group G] [Finite G] :
    Prop2OneAt G ↔ ∀ (b t c : G) (J : Subgroup G), FS79Hyp1 b t c J →
      setMul (Opp 3 (⊤ : Subgroup G)) (Nor (Subgroup.zpowers b)) = Set.univ := by
  constructor
  · intro h b t c J hH
    exact h b t c J hH.ord_b hH.ord_t hH.inv_b hH.J_perm hH.J_le_cen_b hH.J_le_cen_t
      hH.N_le_NJ hH.N_eq hH.c_mem hH.ord_c hH.N_c hH.no_two hH.weak
  · intro h b t c J hb ht htb hJ hJb hJt hNJ hN hc hcord hNc hno hweak
    exact h b t c J ⟨hb, ht, htb, hJ, hJb, hJt, hNJ, hN, hc, hcord, hNc, hno, hweak⟩

section Perm3

theorem perm3_normal : ∀ x : Perm (Fin 3), x ≠ 1 →
    ∃ σ : Perm (Fin 3), x * (σ * x * σ⁻¹) ≠ 1 ∧ (x * (σ * x * σ⁻¹)) ^ 3 = 1 := by
  decide +kernel

end Perm3

variable {G : Type} [Group G] [Finite G]
variable {b t c : G} {J : Subgroup G}

theorem FS79Hyp1.t_sq (h : FS79Hyp1 b t c J) : t * t = 1 := by
  rw [← pow_two, ← h.ord_t]
  exact pow_orderOf_eq_one t

theorem FS79Hyp1.b_pow_three (h : FS79Hyp1 b t c J) : b ^ 3 = 1 := by
  rw [← h.ord_b]
  exact pow_orderOf_eq_one b

theorem FS79Hyp1.b_ne_one (h : FS79Hyp1 b t c J) : b ≠ 1 := by
  intro h1
  have := h.ord_b
  rw [h1, orderOf_one] at this
  omega

theorem FS79Hyp1.c_pow_three (h : FS79Hyp1 b t c J) : c ^ 3 = 1 := by
  rw [← h.ord_c]
  exact pow_orderOf_eq_one c

theorem FS79Hyp1.c_ne_one (h : FS79Hyp1 b t c J) : c ≠ 1 := by
  intro h1
  have := h.ord_c
  rw [h1, orderOf_one] at this
  omega

theorem FS79Hyp1.eq_bot_of_normal_in_J (h : FS79Hyp1 b t c J) {X : Subgroup G} (hXJ : X ≤ J)
    (hXn : ∀ j ∈ J, ∀ x ∈ X, j * x * j⁻¹ ∈ X) (hX : Nat.Coprime 3 (Nat.card X)) : X = ⊥ := by
  classical
  obtain ⟨e⟩ := h.J_perm
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  have hxJ : x ∈ J := hXJ hx
  have hxne : e ⟨x, hxJ⟩ ≠ 1 := by
    intro h1
    apply hx1
    have := e.injective (h1.trans (map_one e).symm)
    simpa using congrArg Subtype.val this
  obtain ⟨σ, hσ1, hσ3⟩ := perm3_normal _ hxne
  obtain ⟨j, hj⟩ := e.surjective σ
  set y : G := x * ((j : G) * x * (j : G)⁻¹) with hy
  have hyX : y ∈ X := X.mul_mem hx (hXn j j.2 x hx)
  have hy3 : y ^ 3 = 1 := by
    have : (⟨y, J.mul_mem hxJ (J.mul_mem (J.mul_mem j.2 hxJ) (J.inv_mem j.2))⟩ : ↥J) ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      have e1 : e ⟨y, J.mul_mem hxJ (J.mul_mem (J.mul_mem j.2 hxJ) (J.inv_mem j.2))⟩ =
          e ⟨x, hxJ⟩ * (σ * e ⟨x, hxJ⟩ * σ⁻¹) := by
        rw [← hj]
        have : (⟨y, J.mul_mem hxJ (J.mul_mem (J.mul_mem j.2 hxJ) (J.inv_mem j.2))⟩ : ↥J) =
            ⟨x, hxJ⟩ * (j * ⟨x, hxJ⟩ * j⁻¹) := rfl
        rw [this]
        simp
      rw [e1]
      exact hσ3
    simpa using congrArg Subtype.val this
  have hy1 : y ≠ 1 := by
    intro h1
    apply hσ1
    have e1 : e ⟨x, hxJ⟩ * (σ * e ⟨x, hxJ⟩ * σ⁻¹) = 1 := by
      rw [← hj]
      have : (⟨x, hxJ⟩ : ↥J) * (j * ⟨x, hxJ⟩ * j⁻¹) = 1 := by
        apply Subtype.ext
        simpa [hy] using h1
      have h2 := congrArg e this
      simpa using h2
    exact e1
  exact hy1 (eq_one_of_mem_coprime_of_pow_three hX hyX hy3)

theorem FS79Hyp1.b_not_mem_J (h : FS79Hyp1 b t c J) : b ∉ J := by
  intro hbJ
  obtain ⟨e⟩ := h.J_perm
  have hcen : e ⟨b, hbJ⟩ = 1 := by
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro τ
    obtain ⟨j, rfl⟩ := e.surjective τ
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b j.2) |>.symm
  have : (⟨b, hbJ⟩ : ↥J) = 1 := e.injective (hcen.trans (map_one e).symm)
  exact h.b_ne_one (congrArg Subtype.val this)

theorem FS79Hyp1.zpowers_inf_J (h : FS79Hyp1 b t c J) : Subgroup.zpowers b ⊓ J = ⊥ := by
  have hcard : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, h.ord_b]
  have hdvd : Nat.card ↥(Subgroup.zpowers b ⊓ J) ∣ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers b ⊓ J ≤ Subgroup.zpowers b)
    rwa [hcard] at this
  apply Subgroup.eq_bot_of_card_eq
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact h1
  · exfalso
    have heq : Subgroup.zpowers b ⊓ J = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcard])
    have hbJ : b ∈ J := by
      have : b ∈ Subgroup.zpowers b ⊓ J := by rw [heq]; exact Subgroup.mem_zpowers b
      exact this.2
    exact h.b_not_mem_J hbJ

theorem FS79Hyp1.J_le_Nor (h : FS79Hyp1 b t c J) : J ≤ Nor (Subgroup.zpowers b) :=
  fun x hx => fs79_cen_le_nor_zpowers b (h.J_le_cen_b hx)

theorem FS79Hyp1.K_comm_J (h : FS79Hyp1 b t c J) {k j : G}
    (hk : k ∈ Opp 3 (Nor (Subgroup.zpowers b))) (hj : j ∈ J) : k * j = j * k := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K : Subgroup G := Opp 3 (Nor (Subgroup.zpowers b)) with hK
  have hKN : K ≤ Nor (Subgroup.zpowers b) := L14.Opp_le 3 _
  have hX : J ⊓ K = ⊥ := by
    refine h.eq_bot_of_normal_in_J inf_le_left ?_ ?_
    · intro j' hj' x hx
      exact ⟨J.mul_mem (J.mul_mem hj' hx.1) (J.inv_mem hj'),
        L14.Opp_conj_mem (h.J_le_Nor hj') hx.2⟩
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (L14.Opp_coprime 3 _)
  have hmem : k * j * k⁻¹ * j⁻¹ ∈ J ⊓ K := by
    constructor
    · have h1 : k * j * k⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (h.N_le_NJ (hKN hk)) j).mp hj
      exact J.mul_mem h1 (J.inv_mem hj)
    · have h2 : j * k⁻¹ * j⁻¹ ∈ K := L14.Opp_conj_mem (h.J_le_Nor hj) (K.inv_mem hk)
      have : k * j * k⁻¹ * j⁻¹ = k * (j * k⁻¹ * j⁻¹) := by group
      rw [this]
      exact K.mul_mem hk h2
  rw [hX, Subgroup.mem_bot] at hmem
  calc k * j = (k * j * k⁻¹ * j⁻¹) * (j * k) := by group
    _ = j * k := by rw [hmem, one_mul]

theorem FS79Hyp1.K_cen_b (h : FS79Hyp1 b t c J) {k : G}
    (hk : k ∈ Opp 3 (Nor (Subgroup.zpowers b))) : k * b = b * k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkN : k ∈ Nor (Subgroup.zpowers b) := L14.Opp_le 3 _ hk
  have h1 : k * b * k⁻¹ = b := by
    refine conj_eq_of_coprime_normal (X := Nor (Subgroup.zpowers b))
      (Q := Opp 3 (Nor (Subgroup.zpowers b))) (fun g hg q hq => L14.Opp_conj_mem hg hq)
      (L14.Opp_coprime 3 _) (mem_Nor_self b) h.b_pow_three h.b_ne_one hk ?_
    exact (Subgroup.mem_normalizer_iff.mp hkN b).mp (Subgroup.mem_zpowers b)
  calc k * b = (k * b * k⁻¹) * k := by group
    _ = b * k := by rw [h1]

theorem FS79Hyp1.Y_comm_J (h : FS79Hyp1 b t c J) {y j : G}
    (hy : y ∈ Subgroup.closure ({b, t} : Set G)) (hj : j ∈ J) : y * j = j * y := by
  have hle : Subgroup.closure ({b, t} : Set G) ≤ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.mpr fun j hj =>
        Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b hj)
    · exact Subgroup.mem_centralizer_iff.mpr fun j hj =>
        Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t hj)
  exact (Subgroup.mem_centralizer_iff.mp (hle hy) j hj).symm

theorem FS79Hyp1.nor_decomp (h : FS79Hyp1 b t c J) {n : G}
    (hn : n ∈ Nor (Subgroup.zpowers b)) :
    ∃ k ∈ Opp 3 (Nor (Subgroup.zpowers b)), ∃ y ∈ Subgroup.closure ({b, t} : Set G),
      ∃ j ∈ J, n = k * y * j := by
  have hmem : n ∈ setMul (Opp 3 (Nor (Subgroup.zpowers b)))
      (Subgroup.closure {b, t} ⊔ J) := by
    rw [h.N_eq]
    exact hn
  obtain ⟨k, hk, m, hm, hnkm⟩ := hmem
  obtain ⟨y, hy, j, hj, hyj⟩ := (CFSG.mem_sup_of_commute
    (A := Subgroup.closure ({b, t} : Set G)) (B := J)
    (fun a ha c hc => h.Y_comm_J ha hc)).mp hm
  refine ⟨k, hk, y, hy, j, hj, ?_⟩
  rw [hnkm, ← hyj, mul_assoc]

theorem FS79Hyp1.conj_eq_of_decomp (h : FS79Hyp1 b t c J) {k y j x : G}
    (hk : k ∈ Opp 3 (Nor (Subgroup.zpowers b))) (hy : y ∈ Subgroup.closure ({b, t} : Set G))
    (hj : j ∈ J) (hx : x ∈ J) : (k * y * j) * x * (k * y * j)⁻¹ = j * x * j⁻¹ := by
  have hw : j * x * j⁻¹ ∈ J := J.mul_mem (J.mul_mem hj hx) (J.inv_mem hj)
  have hyw : y * (j * x * j⁻¹) = (j * x * j⁻¹) * y := h.Y_comm_J hy hw
  have hkw : k * (j * x * j⁻¹) = (j * x * j⁻¹) * k := h.K_comm_J hk hw
  calc (k * y * j) * x * (k * y * j)⁻¹ = k * (y * (j * x * j⁻¹) * y⁻¹) * k⁻¹ := by group
    _ = k * ((j * x * j⁻¹) * y * y⁻¹) * k⁻¹ := by rw [hyw]
    _ = k * (j * x * j⁻¹) * k⁻¹ := by group
    _ = (j * x * j⁻¹) * k * k⁻¹ := by rw [hkw]
    _ = j * x * j⁻¹ := by group

theorem pgroup_le_cen_gen {b : G} (hb : orderOf b = 3)
    (hweak : ∀ h : G, conjBy h (Subgroup.zpowers b) ≤ Nor (Subgroup.zpowers b) →
      conjBy h (Subgroup.zpowers b) = Subgroup.zpowers b)
    {S₀ : Subgroup G} (hS : IsPGroup 3 S₀) (hbS : b ∈ S₀) : S₀ ≤ Cen b := by
  classical
  by_contra hle
  obtain ⟨p, hpP', hpC⟩ := Set.not_subset.mp hle
  let x : S₀ := ⟨b, hbS⟩
  have hx_not_center : x ∉ Subgroup.center S₀ := by
    intro hx
    apply hpC
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hx) (⟨p, hpP'⟩ : S₀)))
  obtain ⟨g, hgne, hgcomm⟩ :=
    CFSG.exists_commuting_conjugate_of_noncentral (by norm_num : Nat.Prime 3) hS hx_not_center
  let gH : G := (g : S₀)
  let y : G := gH * b * gH⁻¹
  have hgneH : y ≠ b := by
    intro hy
    apply hgne
    apply Subtype.ext
    simpa [y, gH, x] using hy
  have hgcommH : y * b = b * y := by
    have hh := congrArg Subtype.val hgcomm
    simpa [y, gH, x] using hh
  have hyCen : y ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.mpr hgcommH
  have hy_le : Subgroup.zpowers y ≤ Cen b := Subgroup.zpowers_le.mpr hyCen
  have hconj : conjBy gH (Subgroup.zpowers b) = Subgroup.zpowers y := by
    simpa [y, MulAut.conj_apply] using MonoidHom.map_zpowers (MulAut.conj gH).toMonoidHom b
  have hleNor : conjBy gH (Subgroup.zpowers b) ≤ Nor (Subgroup.zpowers b) := by
    rw [hconj]
    exact hy_le.trans (fun z hz => fs79_cen_le_nor_zpowers b hz)
  have hweak_eq : Subgroup.zpowers y = Subgroup.zpowers b := by
    rw [← hconj]
    exact hweak gH hleNor
  have hy_mem : y ∈ Subgroup.zpowers b := by
    rw [← hweak_eq]
    exact Subgroup.mem_zpowers y
  have hb_ne_one : b ≠ 1 := by
    intro hb1
    rw [hb1, orderOf_one] at hb
    omega
  have hy_ne_one : y ≠ 1 := by
    intro hy1
    apply hb_ne_one
    have hy1' : gH * b * gH⁻¹ = 1 := by simpa [y] using hy1
    calc b = gH⁻¹ * (gH * b * gH⁻¹) * gH := by group
      _ = gH⁻¹ * (1 : G) * gH := by rw [hy1']
      _ = 1 := by group
  have hb3 : b ^ 3 = 1 := by
    rw [← hb]
    exact pow_orderOf_eq_one b
  rcases eq_or_inv_of_mem_zpowers_of_pow_three hb3 hb_ne_one hy_mem hy_ne_one with hyb | hybinv
  · exact hgneH hyb
  ·
    obtain ⟨k, hk⟩ := hS.exists_pow_pow_eq_one g
    have hgn : gH ^ (3 ^ k) = 1 := by
      have hval := congrArg Subtype.val hk
      simpa [gH] using hval
    have hodd : Odd (orderOf gH) := by
      have hd : orderOf gH ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hgn
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
      rw [hj]
      exact (show Odd 3 by decide).pow
    have hfix := conj_eq_self_of_odd_of_mem_zpowers hb hodd (by
      show gH * b * gH⁻¹ ∈ Subgroup.zpowers b
      exact hy_mem)
    exact hgneH hfix

theorem conj_mem_zpowers_of_pgroup_gen {b : G} (hb : orderOf b = 3)
    (hweak : ∀ h : G, conjBy h (Subgroup.zpowers b) ≤ Nor (Subgroup.zpowers b) →
      conjBy h (Subgroup.zpowers b) = Subgroup.zpowers b)
    {S₀ : Subgroup G} (hS : IsPGroup 3 S₀) (hbS : b ∈ S₀) {g : G} (hg : g * b * g⁻¹ ∈ S₀) :
    g * b * g⁻¹ ∈ Subgroup.zpowers b := by
  have hcen : g * b * g⁻¹ ∈ Cen b := pgroup_le_cen_gen hb hweak hS hbS hg
  have hle : conjBy g (Subgroup.zpowers b) ≤ Nor (Subgroup.zpowers b) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have e : (MulAut.conj g).toMonoidHom (b ^ k) = (g * b * g⁻¹) ^ k := by
      simp [MulAut.conj_apply]
    rw [e]
    exact fs79_cen_le_nor_zpowers b (Subgroup.zpow_mem _ hcen k)
  have heq := hweak g hle
  rw [← heq]
  exact ⟨b, Subgroup.mem_zpowers b, by simp [MulAut.conj_apply]⟩

theorem FS79Hyp1.mem_Nor_of_conj_pgroup (h : FS79Hyp1 b t c J) {S₀ : Subgroup G}
    (hS : IsPGroup 3 S₀) (hbS : b ∈ S₀) {g : G} (hg : g * b * g⁻¹ ∈ S₀) :
    g ∈ Nor (Subgroup.zpowers b) :=
  mem_Nor_zpowers_of_conj (conj_mem_zpowers_of_pgroup_gen h.ord_b h.weak hS hbS hg)

theorem FS79Hyp1.mem_zpowers_of_comm (h : FS79Hyp1 b t c J) {y : G}
    (hy : y ∈ Subgroup.closure ({b, t} : Set G)) (hc : y * b = b * y) :
    y ∈ Subgroup.zpowers b := by
  obtain ⟨i, hi | hi⟩ := mem_closure_bt_iff h.inv_b h.t_sq hy
  · rw [hi]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i
  · exfalso
    rw [hi] at hc
    have h1 : t * b = b * t := by
      have : b ^ i * (t * b) = b ^ i * (b * t) := by
        calc b ^ i * (t * b) = b ^ i * t * b := by group
          _ = b * (b ^ i * t) := hc
          _ = b ^ i * (b * t) := by
            rw [← mul_assoc, ← mul_assoc, (Commute.zpow_left (Commute.refl b) i).eq]
      exact mul_left_cancel this
    have h2 : b = b⁻¹ := by
      rw [← h.inv_b]
      calc b = (t * b) * t⁻¹ := by rw [h1]; group
        _ = t * b * t⁻¹ := rfl
    have hb2 : b ^ 2 = 1 := by
      rw [pow_two]
      exact eq_inv_iff_mul_eq_one.mp h2
    have hdvd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hb2
    rw [h.ord_b] at hdvd
    norm_num at hdvd

theorem eq_one_of_pow_three_pow {S : Subgroup G} (hS : Nat.Coprime 3 (Nat.card S)) {x : G}
    (hx : x ∈ S) {m : ℕ} (h : x ^ (3 ^ m) = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : ↥S) ∣ 3 ^ m :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h))
  have h2 : orderOf (⟨x, hx⟩ : ↥S) ∣ Nat.card S := orderOf_dvd_natCard _
  have h3 : Nat.Coprime (orderOf (⟨x, hx⟩ : ↥S)) (3 ^ m) :=
    Nat.Coprime.pow_right m (Nat.Coprime.coprime_dvd_left h2 hS.symm)
  have h4 : orderOf (⟨x, hx⟩ : ↥S) = 1 := Nat.eq_one_of_dvd_coprimes h3 (dvd_refl _) h1
  have := orderOf_eq_one_iff.1 h4
  simpa using congrArg Subtype.val this

theorem FS79Hyp1.J_center (h : FS79Hyp1 b t c J) {x : G} (hx : x ∈ J)
    (hc : ∀ j ∈ J, x * j = j * x) : x = 1 := by
  obtain ⟨e⟩ := h.J_perm
  have hcen : e ⟨x, hx⟩ = 1 := by
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro τ
    obtain ⟨j, rfl⟩ := e.surjective τ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc j j.2)
  have : (⟨x, hx⟩ : ↥J) = 1 := e.injective (hcen.trans (map_one e).symm)
  exact congrArg Subtype.val this

theorem FS79Hyp1.card_J (h : FS79Hyp1 b t c J) : Nat.card ↥J = 6 := by
  obtain ⟨e⟩ := h.J_perm
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

theorem FS79Hyp1.bc_comm (h : FS79Hyp1 b t c J) : b * c = c * b :=
  (Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b h.c_mem)).symm

theorem FS79Hyp1.card_zpowers_sup_J (h : FS79Hyp1 b t c J) :
    Nat.card ↥(Subgroup.zpowers b ⊔ J) = 18 := by
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ x ∈ J, Commute a x := by
    intro a ha x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp
      (h.J_le_cen_b hx) : Commute x b).symm k)
  rw [CFSG.card_sup_eq_mul_of_commute _ _ hcomm h.zpowers_inf_J, h.card_J,
    Nat.card_zpowers, h.ord_b]

theorem FS79Hyp1.K_inf_E₀ (h : FS79Hyp1 b t c J) :
    Opp 3 (Nor (Subgroup.zpowers b)) ⊓ (Subgroup.zpowers b ⊔ J) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card (Opp 3 (Nor (Subgroup.zpowers b)))) :=
    L14.Opp_coprime 3 _
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ x ∈ J, Commute a x := by
    intro a ha x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp
      (h.J_le_cen_b hx) : Commute x b).symm k)
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxE⟩
  obtain ⟨u, hu, j', hj', rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hxE
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hbi : ∀ j ∈ J, b ^ i * j = j * b ^ i := fun j hj =>
    (hcomm _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i) j hj).eq
  have hj'1 : j' = 1 := by
    refine h.J_center hj' fun j hj => ?_
    have h1 : (b ^ i * j') * j = j * (b ^ i * j') := h.K_comm_J hxK hj
    calc j' * j = (b ^ i)⁻¹ * ((b ^ i * j') * j) := by group
      _ = (b ^ i)⁻¹ * (j * (b ^ i * j')) := by rw [h1]
      _ = (b ^ i)⁻¹ * (b ^ i * (j * j')) := by rw [← mul_assoc j, ← hbi j hj]; group
      _ = j * j' := by group
  rw [hj'1, mul_one] at hxK ⊢
  have hbi3 : (b ^ i) ^ 3 = 1 := by
    have e : (b ^ i) ^ (3 : ℕ) = (b ^ (3 : ℕ)) ^ i := by
      rw [← zpow_natCast, ← zpow_natCast b 3, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [e, h.b_pow_three, one_zpow]
  rw [eq_one_of_mem_coprime_of_pow_three hcop hxK hbi3]
  exact Subgroup.one_mem _

theorem closure_pair_eq_sup (x y : G) :
    Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
  rw [Subgroup.zpowers_eq_closure x, Subgroup.zpowers_eq_closure y, ← Subgroup.closure_union]
  congr 1

theorem FS79Hyp1.B_comm (h : FS79Hyp1 b t c J) {u v : G}
    (hu : u ∈ Subgroup.closure ({b, c} : Set G)) (hv : v ∈ Subgroup.closure ({b, c} : Set G)) :
    u * v = v * u := by
  have hbc : Commute b c := h.bc_comm
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ x ∈ Subgroup.zpowers c, Commute a x := by
    intro a ha x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Commute.zpow_zpow hbc i j
  rw [closure_pair_eq_sup] at hu hv
  obtain ⟨a, ha, x, hx, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hu
  obtain ⟨a', ha', x', hx', rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hv
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨i', rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
  obtain ⟨j', rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
  have h1 : Commute (b ^ i * c ^ j) (b ^ i' * c ^ j') := by
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · exact Commute.zpow_zpow_self b i i'
    · exact Commute.zpow_zpow hbc i j'
    · exact (Commute.zpow_zpow hbc i' j).symm
    · exact Commute.zpow_zpow_self c j j'
  exact h1.eq

theorem FS79Hyp1.isPGroup_B (h : FS79Hyp1 b t c J) :
    IsPGroup 3 (Subgroup.closure ({b, c} : Set G)) :=
  isPGroup_closure_pair h.bc_comm h.b_pow_three h.c_pow_three

theorem FS79Hyp1.card_B (h : FS79Hyp1 b t c J) :
    Nat.card ↥(Subgroup.closure ({b, c} : Set G)) = 9 := by
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ x ∈ Subgroup.zpowers c, Commute a x := by
    intro a ha x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Commute.zpow_zpow h.bc_comm i j
  have hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff, ← h.zpowers_inf_J]
    exact inf_le_inf_left _ (Subgroup.zpowers_le.mpr h.c_mem)
  rw [closure_pair_eq_sup, CFSG.card_sup_eq_mul_of_commute _ _ hcomm hdisj, Nat.card_zpowers,
    Nat.card_zpowers, h.ord_b, h.ord_c]

theorem FS79Hyp1.B_le_cen_b (h : FS79Hyp1 b t c J) :
    Subgroup.closure ({b, c} : Set G) ≤ Cen b := by
  intro u hu
  refine Subgroup.mem_centralizer_singleton_iff.mpr (h.B_comm hu ?_)
  rw [closure_pair_eq_sup]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)

theorem FS79Hyp1.b_mem_B (b c : G) : b ∈ Subgroup.closure ({b, c} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem FS79Hyp1.c_mem_B (b c : G) : c ∈ Subgroup.closure ({b, c} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem FS79Hyp1.pgroup_le_E₀ (h : FS79Hyp1 b t c J) {P : Subgroup G} (hP : IsPGroup 3 P)
    (hbP : b ∈ P) : P ≤ Subgroup.zpowers b ⊔ J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPC : P ≤ Cen b := pgroup_le_cen_gen h.ord_b h.weak hP hbP
  intro p hp
  have hpN : p ∈ Nor (Subgroup.zpowers b) := fs79_cen_le_nor_zpowers b (hPC hp)
  obtain ⟨k, hk, y, hy, j, hj, hpkyj⟩ := h.nor_decomp hpN
  have hpb : p * b = b * p := Subgroup.mem_centralizer_singleton_iff.mp (hPC hp)
  have hkb : k * b = b * k := h.K_cen_b hk
  have hjb : j * b = b * j := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b hj)
  have hyb : y * b = b * y := by
    rw [hpkyj] at hpb
    have e : k * (y * b) * j = k * (b * y) * j := by
      calc k * (y * b) * j = k * y * (b * j) := by group
        _ = k * y * (j * b) := by rw [hjb]
        _ = k * y * j * b := by group
        _ = b * (k * y * j) := hpb
        _ = (b * k) * y * j := by group
        _ = (k * b) * y * j := by rw [hkb]
        _ = k * (b * y) * j := by group
    exact mul_right_cancel (mul_left_cancel (a := k) (by simpa [mul_assoc] using e))
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (h.mem_zpowers_of_comm hy hyb)
  obtain ⟨m, hm⟩ := hP.exists_pow_pow_eq_one ⟨p, hp⟩
  have hm' : p ^ (3 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have hcb : ∀ i' : ℤ, k * b ^ i' = b ^ i' * k := fun i' =>
    (Commute.zpow_right (show Commute k b from hkb) i').eq
  have hkx : Commute k (b ^ i * j) :=
    ((show Commute k (b ^ i) from hcb i).mul_right (show Commute k j from h.K_comm_J hk hj))
  have hpow : p ^ (3 ^ m) = k ^ (3 ^ m) * (b ^ i * j) ^ (3 ^ m) := by
    rw [hpkyj, mul_assoc k (b ^ i) j]
    exact hkx.mul_pow _
  have hxE : (b ^ i * j) ^ (3 ^ m) ∈ Subgroup.zpowers b ⊔ J :=
    Subgroup.pow_mem _ (Subgroup.mul_mem_sup (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i) hj) _
  have hkE : k ^ (3 ^ m) ∈ Opp 3 (Nor (Subgroup.zpowers b)) ⊓ (Subgroup.zpowers b ⊔ J) := by
    refine ⟨Subgroup.pow_mem _ hk _, ?_⟩
    have : k ^ (3 ^ m) = ((b ^ i * j) ^ (3 ^ m))⁻¹ := by
      rw [hm'] at hpow
      exact eq_inv_of_mul_eq_one_left hpow.symm
    rw [this]
    exact Subgroup.inv_mem _ hxE
  rw [h.K_inf_E₀, Subgroup.mem_bot] at hkE
  have hk1 : k = 1 := eq_one_of_pow_three_pow (L14.Opp_coprime 3 _) hk hkE
  rw [hpkyj, hk1, one_mul]
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i) hj

theorem FS79Hyp1.isSylowOf_B_top (h : FS79Hyp1 b t c J) :
    IsSylowOf 3 (Subgroup.closure ({b, c} : Set G)) ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hBP⟩ := h.isPGroup_B.exists_le_sylow
  have hPp : IsPGroup 3 (P : Subgroup G) := P.isPGroup'
  have hbP : b ∈ (P : Subgroup G) := hBP (FS79Hyp1.b_mem_B b c)
  have hPE := h.pgroup_le_E₀ hPp hbP
  have hdvd : Nat.card (P : Subgroup G) ∣ 18 := by
    have := Subgroup.card_dvd_of_le hPE
    rwa [h.card_zpowers_sup_J] at this
  obtain ⟨n, hn⟩ := hPp.exists_card_eq
  have hn2 : n ≤ 2 := by
    by_contra hcon
    have h27 : 27 ∣ 18 := by
      have : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
      rw [← hn] at this
      exact (by norm_num : (27 : ℕ) = 3 ^ 3) ▸ this.trans hdvd
    omega
  have hcardle : Nat.card (P : Subgroup G) ≤ 9 := by
    rw [hn]
    calc 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
      _ = 9 := by norm_num
  have hPB : Subgroup.closure ({b, c} : Set G) = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hBP (by rw [h.card_B]; exact hcardle)
  refine ⟨le_top, h.isPGroup_B, ?_⟩
  rw [Subgroup.relIndex_top_right, hPB]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr P.not_dvd_index

theorem FS79Hyp1.mem_Nor_of_conj_b (h : FS79Hyp1 b t c J) {g : G}
    (hg : g * b * g⁻¹ ∈ Subgroup.closure ({b, c} : Set G)) :
    g ∈ Nor (Subgroup.zpowers b) :=
  h.mem_Nor_of_conj_pgroup h.isPGroup_B (FS79Hyp1.b_mem_B b c) hg

theorem odd_Opp_of_no_two_sub {N A : Subgroup G} (hAN : A ≤ N) (hA : IsPGroup 3 A)
    (hno : ∀ R : Subgroup G, IsPGroup 2 R → A ≤ Nor R → R = ⊥) :
    Odd (Nat.card (Opp 3 N)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup G := Opp 3 N with hO
  by_contra hodd
  have h2dvd : 2 ∣ Nat.card O := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have hOcop : Nat.Coprime 3 (Nat.card O) := L14.Opp_coprime 3 N
  have h3dvd : ¬ 3 ∣ Nat.card O := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hOcop hd
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha z hz
    exact L14.Opp_conj_mem (hAN ha) hz
  obtain ⟨R, hRsyl, -, hAR⟩ := CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime
    (q := 3) (r := 2) (A := A) (K := O) (P := ⊥) Nat.prime_three Nat.prime_two hA hAO h3dvd
    bot_le IsPGroup.of_bot Subgroup.le_normalizer_of_normal
  have hR2 : IsPGroup 2 R := CFSG.ABGLocalTools.IsSylowOf.isPGroup hRsyl
  have hRbot : R = ⊥ := hno R hR2 hAR
  have hndvd : ¬ 2 ∣ R.relIndex O := (CFSG.ABGLocalTools.isSylowOf_iff.mp hRsyl).2.2
  exact hndvd (by rw [hRbot, Subgroup.relIndex_bot_left]; exact h2dvd)

theorem FS79Hyp1.odd_K (h : FS79Hyp1 b t c J) : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers b)))) :=
  odd_Opp_of_no_two_sub (fun x hx => fs79_cen_le_nor_zpowers b (h.B_le_cen_b hx)) h.isPGroup_B
    (fun R hR hBR => h.no_two R hR hBR)

theorem FS79Hyp1.cen_decomp (h : FS79Hyp1 b t c J) {p : G} (hp : p ∈ Cen b) :
    ∃ k ∈ Opp 3 (Nor (Subgroup.zpowers b)), ∃ i : ℤ, ∃ j ∈ J, p = k * b ^ i * j := by
  have hpN : p ∈ Nor (Subgroup.zpowers b) := fs79_cen_le_nor_zpowers b hp
  obtain ⟨k, hk, y, hy, j, hj, hpkyj⟩ := h.nor_decomp hpN
  have hpb : p * b = b * p := Subgroup.mem_centralizer_singleton_iff.mp hp
  have hkb : k * b = b * k := h.K_cen_b hk
  have hjb : j * b = b * j := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b hj)
  have hyb : y * b = b * y := by
    rw [hpkyj] at hpb
    have e : k * (y * b) * j = k * (b * y) * j := by
      calc k * (y * b) * j = k * y * (b * j) := by group
        _ = k * y * (j * b) := by rw [hjb]
        _ = k * y * j * b := by group
        _ = b * (k * y * j) := hpb
        _ = (b * k) * y * j := by group
        _ = (k * b) * y * j := by rw [hkb]
        _ = k * (b * y) * j := by group
    exact mul_right_cancel (mul_left_cancel (a := k) (by simpa [mul_assoc] using e))
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (h.mem_zpowers_of_comm hy hyb)
  exact ⟨k, hk, i, j, hj, hpkyj⟩

theorem isSolvable_sup_of_commute {A B : Subgroup G} (hA : Group.IsSolvable A)
    (hB : Group.IsSolvable B) (hAB : ∀ a ∈ A, ∀ x ∈ B, a * x = x * a) :
    Group.IsSolvable ↥(A ⊔ B) := by
  let f : ↥A × ↥B →* ↥(A ⊔ B) :=
    { toFun := fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro p q
        apply Subtype.ext
        have := hAB (q.1 : G) q.1.2 (p.2 : G) p.2.2
        calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
            = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [this]
          _ = (p.1 : G) * (p.2 : G) * ((q.1 : G) * (q.2 : G)) := by group }
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, y, hy, rfl⟩ := (CFSG.mem_sup_of_commute (fun a ha y hy => (hAB a ha y hy))).mp hx
    exact ⟨(⟨a, ha⟩, ⟨y, hy⟩), rfl⟩
  exact Group.isSolvable_of_surjective hsurj

theorem FS79Hyp1.isSolvable_J (h : FS79Hyp1 b t c J) : Group.IsSolvable ↥J := by
  obtain ⟨e⟩ := h.J_perm
  haveI : IsZGroup (Equiv.Perm (Fin 3)) := by
    refine IsZGroup.of_squarefree ?_
    rw [Nat.card_perm, Nat.card_fin]
    have h6 : Squarefree (2 * 3 : ℕ) :=
      (Nat.squarefree_mul (by norm_num : Nat.Coprime 2 3)).mpr
        ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
    exact h6
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem FS79Hyp1.isSolvable_cen_b (h : FS79Hyp1 b t c J) : Group.IsSolvable ↥(Cen b) := by
  classical
  haveI : Group.IsSolvable ↥(Opp 3 (Nor (Subgroup.zpowers b))) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ h.odd_K
  haveI : Group.IsSolvable ↥J := h.isSolvable_J
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ x ∈ J, a * x = x * a := by
    intro a ha x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp
      (h.J_le_cen_b hx) : Commute x b).symm k).eq
  haveI : Group.IsSolvable ↥(Subgroup.zpowers b ⊔ J) :=
    isSolvable_sup_of_commute (by infer_instance) inferInstance hcomm
  haveI : Group.IsSolvable ↥(Opp 3 (Nor (Subgroup.zpowers b)) ⊔ (Subgroup.zpowers b ⊔ J)) := by
    refine isSolvable_sup_of_commute inferInstance inferInstance ?_
    intro k hk x hx
    obtain ⟨u, hu, j', hj', rfl⟩ :=
      (CFSG.mem_sup_of_commute (fun a ha y hy => (hcomm a ha y hy))).mp hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hkb : ∀ i' : ℤ, k * b ^ i' = b ^ i' * k := fun i' =>
      (Commute.zpow_right (show Commute k b from h.K_cen_b hk) i').eq
    calc k * (b ^ i * j') = (k * b ^ i) * j' := by group
      _ = (b ^ i * k) * j' := by rw [hkb i]
      _ = b ^ i * (k * j') := by group
      _ = b ^ i * (j' * k) := by rw [h.K_comm_J hk hj']
      _ = (b ^ i * j') * k := by group
  have hle : Cen b ≤ Opp 3 (Nor (Subgroup.zpowers b)) ⊔ (Subgroup.zpowers b ⊔ J) := by
    intro p hp
    obtain ⟨k, hk, i, j, hj, rfl⟩ := h.cen_decomp hp
    rw [mul_assoc]
    exact Subgroup.mul_mem_sup hk (Subgroup.mul_mem_sup
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i) hj)
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

end CFSG.RankThree.PartTwo.Sec21.FF81
