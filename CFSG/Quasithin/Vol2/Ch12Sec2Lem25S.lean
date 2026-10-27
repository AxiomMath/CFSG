module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25Q

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem25

variable {G : Type} [Group G]

theorem card_ne_one_add_one {X : Type*} [Group X] [Finite X] :
    Nat.card {x : X // x ≠ 1} + 1 = Nat.card X := by
  classical
  have := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]
  have := Fintype.card_pos (α := X)
  omega

theorem false_of_hat_seven {X : Type} [Group X] [Finite X]
    (hX : IsHat X (alternatingGroup (Fin 7))) {D : Subgroup X}
    (hDZ : D ⊓ Subgroup.center X = ⊥) (hD : D.index ≤ 18) : False := by
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hX
  have hX7 : Nat.card X = 2520 * 3 := by
    rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e.toEquiv,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin, hZ]
    decide
  set W := D ⊔ Subgroup.center X with hW
  have hZD : Subgroup.center X ≤ Subgroup.centralizer (D : Set X) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun d _ => (Subgroup.mem_center_iff.mp hz d)
  have hWc : Nat.card W = Nat.card D * 3 := by
    rw [hW, card_sup_eq_mul hZD hDZ, hZ]
  have hDi := D.card_mul_index
  have hWi := W.card_mul_index
  rw [hX7] at hDi hWi
  rw [hWc] at hWi
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hidx : D.index = 3 * W.index := by
    have : Nat.card D * D.index = Nat.card D * (3 * W.index) := by rw [hDi, ← hWi]; ring
    exact Nat.eq_of_mul_eq_mul_left hDpos this
  have hW6 : W.index ≤ 6 := by omega
  have hWtop : W = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (Subgroup.normalCore_normal W) with
      htop | hcen
    · exact eq_top_iff.mpr (htop ▸ W.normalCore_le)
    · exfalso
      have h1 := W.index_normalCore_dvd_factorial_index
      have h2 : Nat.factorial W.index ≤ Nat.factorial 6 := Nat.factorial_le hW6
      have h3 := Nat.le_of_dvd (Nat.factorial_pos _) h1
      have h4 : Nat.factorial 6 = 720 := by decide
      have h5 := W.normalCore.card_mul_index
      have h6 : Nat.card W.normalCore ≤ 3 := hZ ▸ Subgroup.card_le_of_le hcen
      rw [hX7] at h5
      have h7 : 2520 ≤ W.normalCore.index := by nlinarith
      omega
  have hDn : D.Normal := by
    refine ⟨fun d hd x => ?_⟩
    have hx : x ∈ D ⊔ Subgroup.center X := hW ▸ hWtop ▸ Subgroup.mem_top x
    obtain ⟨d', hd', z, hz, rfl⟩ := exists_mul_of_mem_sup_centralizer hZD hx
    have hzd : z * d * z⁻¹ = d := by
      rw [(Subgroup.mem_center_iff.mp hz d).symm, mul_inv_cancel_right]
    rw [show d' * z * d * (d' * z)⁻¹ = d' * (z * d * z⁻¹) * d'⁻¹ by group, hzd]
    exact D.mul_mem (D.mul_mem hd' hd) (D.inv_mem hd')
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hDn with htop | hcen
  · rw [htop, top_inf_eq] at hDZ
    have := Subgroup.card_bot (G := X)
    rw [← hDZ, hZ] at this
    omega
  · have hbot : D = ⊥ := by
      rw [← hDZ]
      exact (inf_eq_left.mpr hcen).symm
    rw [hbot, Subgroup.index_bot, hX7] at hD
    omega

theorem index_normalizer_inf_V_le (h1216 : Stmt12_2_16) (h1222 : Stmt12_2_2) [Finite G]
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn4 : n = 4)
    (hR7 : Nat.card (RR T U) ≤ 2 ^ 7) {K : Subgroup G}
    (hKR : K ≤ Subgroup.normalizer ((RR T U : Subgroup G) : Set G)) :
    ((Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)).subgroupOf K).index ≤ 18 := by
  classical
  have hTI := h1216 G T L V hH hNE
  have hA : Nat.card ↥(U ⊓ V) = 8 := by rw [card_inf_V hC, hn4]; norm_num
  have hAR := inf_V_le_RR hH hC
  have hRV := inf_V_eq h1222 hH hC
  set D := (Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)).subgroupOf K with hD
  have hmemR : ∀ (k : ↥K) (a : ↥(U ⊓ V)), (k : G) * a * (k : G)⁻¹ ∈ RR T U := fun k a =>
    (Subgroup.mem_normalizer_iff.mp (hKR k.2) a).mp (hAR a.2)
  have hconj1 : ∀ {g a : G}, g * a * g⁻¹ = 1 → a = 1 := fun {g a} h' => by
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group
  let Φ : (↥K ⧸ D) × {a : ↥(U ⊓ V) // a ≠ 1} → {r : ↥(RR T U) // r ≠ 1} := fun x =>
    ⟨⟨(x.1.out : G) * (x.2.1 : G) * (x.1.out : G)⁻¹, hmemR _ _⟩, fun h1 => x.2.2
      (Subtype.ext (hconj1 (congrArg Subtype.val h1)))⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨q, a, ha⟩ ⟨q', a', ha'⟩ hqq
    have e1 : (q.out : G) * a * (q.out : G)⁻¹ = (q'.out : G) * a' * (q'.out : G)⁻¹ :=
      congrArg (fun r => ((r.1 : ↥(RR T U)) : G)) hqq
    set g : G := (q.out : G)⁻¹ * q'.out with hg
    have hgK : g ∈ K := K.mul_mem (K.inv_mem q.out.2) q'.out.2
    have hag : (a : G) = g * a' * g⁻¹ := by
      calc (a : G) = (q.out : G)⁻¹ * ((q.out : G) * a * (q.out : G)⁻¹) * q.out := by group
        _ = (q.out : G)⁻¹ * ((q'.out : G) * a' * (q'.out : G)⁻¹) * q.out := by rw [e1]
        _ = g * a' * g⁻¹ := by rw [hg]; group
    have hconj : CFSG.conjugate V g⁻¹ = V := by
      rcases hTI g⁻¹ with h1 | h1
      · exact h1
      · exfalso
        have ha1 : (a : G) ≠ 1 := fun h' => ha (Subtype.ext h')
        have hmem : (a : G) ∈ V ⊓ CFSG.conjugate V g⁻¹ := by
          refine ⟨a.2.2, BlueprintB2.mem_conjugate_iff.mpr ?_⟩
          rw [hag, inv_inv, show g⁻¹ * (g * (a' : G) * g⁻¹) * g = a' by group]
          exact a'.2.2
        rw [h1] at hmem
        exact ha1 hmem
    have hgV : g ∈ Subgroup.normalizer (V : Set G) := by
      refine mem_normalizer_of_conj_mem fun v hv => ?_
      have : g * v * g⁻¹ ∈ CFSG.conjugate V g⁻¹ := BlueprintB2.mem_conjugate_iff.mpr (by
        rw [inv_inv, show g⁻¹ * (g * v * g⁻¹) * g = v by group]
        exact hv)
      rwa [hconj] at this
    have hgA : g ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) := by
      have := Subgroup.inf_normalizer_le_normalizer_inf ⟨hKR hgK, hgV⟩
      rwa [hRV] at this
    have hqeq : q = q' := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)
      simpa [hg] using hgA
    subst hqeq
    have haa : (a : G) = a' := mul_left_cancel (mul_right_cancel e1)
    have : a = a' := Subtype.ext haa
    subst this
    rfl
  have h1 := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_prod] at h1
  have h2 := card_ne_one_add_one (X := ↥(U ⊓ V))
  have h3 := card_ne_one_add_one (X := ↥(RR T U))
  rw [hA] at h2
  have h4 : Nat.card (↥K ⧸ D) = D.index := rfl
  rw [h4] at h1
  have h7 : Nat.card {a : ↥(U ⊓ V) // a ≠ 1} = 7 := by omega
  rw [h7] at h1
  omega

theorem eq_one_of_map_mem_center
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn4 : n = 4) {K : Subgroup G}
    (hKR : K ≤ Subgroup.normalizer ((RR T U : Subgroup G) : Set G)) (hYK : YY L U V ≤ K)
    {X : Type*} [Group X] (χ : ↥K →* X)
    (hkerY : ∀ k : ↥K, χ k = 1 → (k : G) ∈ YY L U V →
      (k : G) ∈ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G))
    {c : ↥K} (hcA : (c : G) ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G))
    (hc3 : c ^ 3 = 1) (hcZ : χ c ∈ Subgroup.center X) : c = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Nat.card ↥(U ⊓ V) = 8 := by rw [card_inf_V hC, hn4]; norm_num
  have hc3' : (c : G) ^ 3 = 1 := congrArg Subtype.val hc3
  have hmod := card_inf_centralizer_elem_modEq (S := U ⊓ V) hc3' hcA
  rw [hA] at hmod
  have hB : U ⊓ V ⊓ Subgroup.centralizer ({(c : G)} : Set G) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
  have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
  obtain ⟨-, -, -, hcY⟩ := mem_normalizer_Y_of_fix h1222 h323 hH hNE hC (hKR c.2) ha.1 ha1'
    (Subgroup.mem_centralizer_singleton_iff.mp ha.2).symm
  have hYB : YY L U V ≤ Subgroup.normalizer
      ((U ⊓ V ⊓ Subgroup.centralizer ({(c : G)} : Set G) : Subgroup G) : Set G) := by
    intro y hy
    refine mem_normalizer_of_conj_mem fun b hb => ?_
    have hybA : y * b * y⁻¹ ∈ U ⊓ V :=
      (Subgroup.mem_normalizer_iff.mp (YY_le_normalizer hy) b).mp hb.1
    refine ⟨hybA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    set yk : ↥K := ⟨y, hYK hy⟩
    set mk : ↥K := c * yk * c⁻¹ * yk⁻¹ with hmk
    have hmY : (mk : G) ∈ YY L U V := by
      have : (c : G) * y * (c : G)⁻¹ ∈ YY L U V := (Subgroup.mem_normalizer_iff.mp hcY y).mp hy
      exact (YY L U V).mul_mem this ((YY L U V).inv_mem hy)
    have hχm : χ mk = 1 := by
      rw [hmk]
      simp only [map_mul, map_inv]
      rw [(Subgroup.mem_center_iff.mp hcZ (χ yk)).symm]
      group
    have hmA := hkerY mk hχm hmY
    have hm : (mk : G) * (y * b * y⁻¹) = (y * b * y⁻¹) * mk :=
      (Subgroup.mem_centralizer_iff.mp hmA _ hybA).symm
    have hcb : (c : G) * b = b * c := (Subgroup.mem_centralizer_singleton_iff.mp hb.2).symm
    have hmk' : (mk : G) = c * y * (c : G)⁻¹ * y⁻¹ := rfl
    have e : (c : G) * (y * b * y⁻¹) * (c : G)⁻¹ = y * b * y⁻¹ := by
      calc (c : G) * (y * b * y⁻¹) * (c : G)⁻¹ =
          ((mk : G) * y) * ((c : G) * b * (c : G)⁻¹) * ((mk : G) * y)⁻¹ := by
            rw [hmk']; group
        _ = (mk : G) * (y * b * y⁻¹) * (mk : G)⁻¹ := by
            rw [show (c : G) * b * (c : G)⁻¹ = b by rw [hcb, mul_inv_cancel_right]]; group
        _ = y * b * y⁻¹ := by rw [hm, mul_inv_cancel_right]
    calc y * b * y⁻¹ * c = (c : G) * (y * b * y⁻¹) * (c : G)⁻¹ * c := by rw [e]
      _ = c * (y * b * y⁻¹) := by group
  have hBA := eq_inf_V_of_le h1222 h1220 hH hNE hC hn4 inf_le_left hB hYB
  have hcA' : ∀ a ∈ U ⊓ V, (c : G) * a = a * c := by
    intro a ha
    rw [← hBA] at ha
    exact (Subgroup.mem_centralizer_singleton_iff.mp ha.2).symm
  have hodd : Odd (orderOf (c : G)) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hc3') with h1 | h1 <;>
      rw [h1] <;> decide
  exact Subtype.ext (eq_one_of_centralizes h331 h1222 h323 h1216 h1220 hH hNE hC hn4 (hKR c.2)
    hodd hcA')

theorem false_of_hat_seven_config
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn4 : n = 4) (hR7 : Nat.card (RR T U) ≤ 2 ^ 7)
    {K : Subgroup G} (hKR : K ≤ Subgroup.normalizer ((RR T U : Subgroup G) : Set G))
    (hYK : YY L U V ≤ K) {X : Type} [Group X] [Finite X]
    (hX : IsHat X (alternatingGroup (Fin 7))) (χ : ↥K →* X) (hχ : Function.Surjective χ)
    (hker : IsPGroup 2 χ.ker)
    (hkerY : ∀ k : ↥K, χ k = 1 → (k : G) ∈ YY L U V →
      (k : G) ∈ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G)) : False := by
  set D := (Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)).subgroupOf K with hD
  have hDi := index_normalizer_inf_V_le h1216 h1222 hH hNE hC hn4 hR7 hKR
  have hDbi : (D.map χ).index ≤ 18 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (Subgroup.index_map_dvd D hχ)).trans hDi
  have hZ3 : Nat.card (Subgroup.center X) = 3 := hX.2.1
  have hDZ : D.map χ ⊓ Subgroup.center X = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzD, hzZ⟩
    have hz3 : z ^ 3 = 1 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.center X) hzZ
      rw [hZ3] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    let ψ : ↥D →* ↥(D.map χ) := (χ.comp D.subtype).codRestrict (D.map χ) fun d =>
      ⟨d, d.2, rfl⟩
    have hψ : Function.Surjective ψ := by
      rintro ⟨_, ⟨d, hd, rfl⟩⟩
      exact ⟨⟨d, hd⟩, rfl⟩
    have hzo : Odd (orderOf (⟨z, hzD⟩ : ↥(D.map χ))) := by
      rw [Subgroup.orderOf_mk]
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hz3) with h1 | h1 <;>
        rw [h1] <;> decide
    obtain ⟨x, hxo, hx⟩ := exists_odd_lift ψ hψ hzo
    have hχx : χ (x : ↥K) = z := congrArg Subtype.val hx
    have hx3 : (x : ↥K) ^ 3 = 1 := by
      have h1 : χ ((x : ↥K) ^ 3) = 1 := by rw [map_pow, hχx, hz3]
      obtain ⟨i, hi⟩ := hker ⟨_, h1⟩
      have h2 : ((x : ↥K) ^ 3) ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
      have hodd : Odd (orderOf ((x : ↥K) ^ 3)) := Odd.of_dvd_nat hxo (orderOf_pow_dvd _)
      have hcop : Nat.Coprime (orderOf ((x : ↥K) ^ 3)) (2 ^ i) :=
        Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one h2))
    have hx1 := eq_one_of_map_mem_center h331 h1222 h323 h1216 h1220 hH hNE hC hn4 hKR hYK χ
      hkerY (c := (x : ↥K)) x.2 hx3 (hχx ▸ hzZ)
    rw [← hχx, hx1, map_one]
    exact Subgroup.one_mem _
  exact false_of_hat_seven hX hDZ hDbi

end Lem25

end CFSG.Quasithin.H13
