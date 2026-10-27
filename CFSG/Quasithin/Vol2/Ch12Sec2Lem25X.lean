module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25V
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25W
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25J

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G]

theorem exists_z_w_three
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn : n = 3)
    (hz : T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    ∃ z w e₀ : G, z ∈ T ⊓ Subgroup.centralizer (L : Set G) ∧ z ≠ 1 ∧
      (∀ c ∈ T ⊓ Subgroup.centralizer (L : Set G), c = 1 ∨ c = z) ∧
      w ∈ T ⊓ Subgroup.centralizer (I : Set G) ∧ e₀ ∈ U ⊓ V ∧ e₀ ≠ 1 ∧ w = e₀ * z ∧
      Nat.card (RR T U) = 32 := by
  classical
  obtain ⟨hc1, hc2, -, -, -, -, hc7, -, hc9, -⟩ := lem12225Star_of h331 h1222 h323 h1216 h1220 G
    T L V H P U I h n p hH hNE hC
  obtain ⟨hKR, hKV, hKA, hAK, hR⟩ := CTL_facts h331 h1222 h323 h1216 h1220 hH hNE hC
  obtain ⟨v₀, hD⟩ := exists_phiData h1222 hH hC
  obtain ⟨hSeq, -⟩ := inf_centralizer_V_eq_three h331 h1222 h323 h1216 h1220 hH hNE hC hn hD
  have hU : Nat.card U = 16 := by rw [card_U hC, hn]; norm_num
  obtain ⟨⟨z, hzK⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hz
  have hz1' : z ≠ 1 := fun h' => hz1 (Subtype.ext h')
  have hK2 : Nat.card ↥(T ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
    have h1 : Nat.card ↥(T ⊓ Subgroup.centralizer (L : Set G)) ≠ 1 := fun h1 =>
      hz (Subgroup.eq_bot_of_card_eq _ h1)
    have h0 := Nat.card_pos (α := ↥(T ⊓ Subgroup.centralizer (L : Set G)))
    omega
  have hzc : ∀ c ∈ T ⊓ Subgroup.centralizer (L : Set G), c = 1 ∨ c = z := fun c hc => by
    by_cases hc1 : c = 1
    · exact Or.inl hc1
    · exact Or.inr (eq_of_card_le_two hc9 hc hzK hc1 hz1')
  have hR32 : Nat.card (RR T U) = 32 := by rw [hR, hU, hK2]
  have hIR : T ⊓ Subgroup.centralizer (I : Set G) ≤ RR T U := by
    show _ ≤ T ⊓ Subgroup.centralizer (U : Set G)
    rw [hc1]
    exact le_sup_right
  have hIU : T ⊓ Subgroup.centralizer (I : Set G) ≤ Subgroup.centralizer (U : Set G) :=
    fun c hc => (hIR hc).2
  have hUI : U ⊓ (T ⊓ Subgroup.centralizer (I : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, -, hxI⟩
    have : x ∈ U ⊓ Subgroup.centralizer (I : Set G) := ⟨hxU, hxI⟩
    rw [hc2] at this
    exact this
  have hRI : Nat.card (RR T U) =
      Nat.card U * Nat.card ↥(T ⊓ Subgroup.centralizer (I : Set G)) := by
    show Nat.card ↥(T ⊓ Subgroup.centralizer (U : Set G)) = _
    rw [hc1, card_sup_eq_mul hIU hUI]
  have hI2 : Nat.card ↥(T ⊓ Subgroup.centralizer (I : Set G)) = 2 := by
    rw [hR32, hU] at hRI
    omega
  obtain ⟨⟨w, hwI⟩, hw1⟩ : ∃ w : ↥(T ⊓ Subgroup.centralizer (I : Set G)), w ≠ 1 := by
    by_contra hno
    push Not at hno
    have : Nat.card ↥(T ⊓ Subgroup.centralizer (I : Set G)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [hno a, hno b]⟩, ⟨1⟩⟩
    omega
  have hw1' : w ≠ 1 := fun h' => hw1 (Subtype.ext h')
  have hVI : V ≤ I := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hI, -⟩ := hC
    rw [hI]
    exact le_sup_left
  have hwV : w ∈ RR T U ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨hIR hwI, Subgroup.centralizer_le hVI hwI.2⟩
  rw [hSeq] at hwV
  obtain ⟨a, ha, c, hc, hac⟩ := exists_mul_of_mem_sup_centralizer hKA hwV
  have hc1' : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hac
    apply hw1'
    have : w ∈ U ⊓ Subgroup.centralizer (I : Set G) := ⟨hac ▸ ha.1, hwI.2⟩
    rw [hc2] at this
    exact this
  have hcz : c = z := (hzc c hc).resolve_left hc1'
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [one_mul, hcz] at hac
    have : z ∈ T ⊓ Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer (I : Set G) :=
      ⟨hzK, hac ▸ hwI.2⟩
    rw [hc7] at this
    exact hz1' this
  exact ⟨z, w, a, hzK, hz1', hzc, hwI, ha, ha1, by rw [← hac, hcz], hR32⟩


theorem h_mem_NR
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) :
    h ∈ Subgroup.normalizer ((RR T U : Subgroup G) : Set G) ∧ h ∈ I ∧
      h ∈ Subgroup.normalizer (U : Set G) := by
  obtain ⟨hc1, -⟩ := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h n p hH hNE hC
  obtain ⟨-, -, -, -, -, -, -, -, hP, -, hhH, -, -, -, -, -, -, -, -, -, -, -, -, -, hHU, -,
    hIP, -⟩ := hC
  have hhI : h ∈ I := by
    rw [hIP]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hP ▸ Subgroup.mem_zpowers h))
  have hhU : h ∈ Subgroup.normalizer (U : Set G) := hHU hhH
  have hCIU : T ⊓ Subgroup.centralizer (I : Set G) ≤ Subgroup.centralizer (U : Set G) := by
    intro c hc
    have : c ∈ T ⊓ Subgroup.centralizer (U : Set G) := by rw [hc1]; exact Subgroup.mem_sup_right hc
    exact this.2
  have hgR : ∀ g ∈ Subgroup.normalizer (U : Set G), g ∈ I → ∀ x ∈ RR T U,
      g * x * g⁻¹ ∈ RR T U := by
    intro g hgU hgI x hx
    show g * x * g⁻¹ ∈ T ⊓ Subgroup.centralizer (U : Set G)
    have hx' : x ∈ T ⊓ Subgroup.centralizer (U : Set G) := hx
    rw [hc1] at hx' ⊢
    obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer hCIU hx'
    have hcg : g * c * g⁻¹ = c := by
      rw [Subgroup.mem_centralizer_iff.mp hc.2 g hgI, mul_inv_cancel_right]
    rw [show g * (u * c) * g⁻¹ = (g * u * g⁻¹) * (g * c * g⁻¹) by group, hcg]
    exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp hgU u).mp hu) hc
  refine ⟨mem_normalizer_of_conj_mem (hgR h hhU hhI), hhI, hhU⟩

theorem bpow_mul_bpow_eq_one {e₀ e₁ : G} (he₀ : e₀ ≠ 1) (he₁ : e₁ ≠ 1) (he : e₀ ≠ e₁)
    (hsq : e₁ * e₁ = 1) {b b' : Bool} (h1 : bpow e₀ b * bpow e₁ b' = 1) :
    b = false ∧ b' = false := by
  cases b <;> cases b' <;> simp [bpow] at h1 ⊢
  · exact he₁ h1
  · exact he₀ h1
  · apply he
    calc e₀ = e₀ * e₁ * e₁ := by rw [mul_assoc, hsq, mul_one]
      _ = e₁ := by rw [h1, one_mul]

theorem exists_basis_three
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn : n = 3) {z e₀ : G}
    (hzK : z ∈ T ⊓ Subgroup.centralizer (L : Set G)) (hz1 : z ≠ 1) (he₀ : e₀ ∈ U ⊓ V)
    (he₀1 : e₀ ≠ 1) (hR32 : Nat.card (RR T U) = 32) :
    ∃ e₁ : G, e₁ ∈ U ⊓ V ∧ e₁ ≠ 1 ∧ e₁ ≠ e₀ ∧
      IsBasis5 (RR T U) ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z] := by
  classical
  obtain ⟨-, -, -, hc4, -, -, -, hc8, -⟩ := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V
    H P U I h n p hH hNE hC
  obtain ⟨hKR, -⟩ := CTL_facts h331 h1222 h323 h1216 h1220 hH hNE hC
  obtain ⟨hhR, -, hhU⟩ := h_mem_NR h331 h1222 h323 h1216 h1220 hH hNE hC
  have hA : Nat.card ↥(U ⊓ V) = 4 := by rw [card_inf_V hC, hn]; norm_num
  have hAR := inf_V_le_RR hH hC
  have hRab : ∀ a ∈ RR T U, ∀ b ∈ RR T U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hc8.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hRsq : ∀ a ∈ RR T U, a * a = 1 := fun a ha => by rw [← pow_two]; exact hc8.2 a ha
  obtain ⟨e₁, he₁, he₁1, he₁0⟩ : ∃ e₁ ∈ U ⊓ V, e₁ ≠ 1 ∧ e₁ ≠ e₀ := by
    by_contra hno
    push Not at hno
    have hsub : ((U ⊓ V : Subgroup G) : Set G) ⊆ {1, e₀} := fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hno x hx hx1)
    have h1 : Nat.card ↥(U ⊓ V) ≤ Nat.card ({1, e₀} : Set G) := by
      rw [← SetLike.coe_sort_coe]
      exact Nat.card_mono (Set.toFinite _) hsub
    have h2 : Nat.card ({1, e₀} : Set G) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    omega
  refine ⟨e₁, he₁, he₁1, he₁0, ?_⟩
  have hTI := h1216 G T L V hH hNE
  have hNVM : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    Lem20.normalizer_le_of_hyp1223 (stmt12_2_6_of h1222 h323) hH
  have hhM : h ∉ Subgroup.normalizer (L : Set G) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hhM, -⟩ := hC
    exact hhM
  have hVhV : V ⊓ CFSG.conjugate V h⁻¹ = ⊥ := by
    rcases hTI h⁻¹ with h1 | h1
    · exfalso
      have hinv : h⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
        refine mem_normalizer_of_conj_mem fun v hv => ?_
        have : v ∈ CFSG.conjugate V h⁻¹ := by rw [h1]; exact hv
        exact BlueprintB2.mem_conjugate_iff.mp this
      exact hhM ((Subgroup.inv_mem_iff _).mp (hNVM hinv))
    · exact h1
  have hAhA : ∀ a ∈ U ⊓ V, ∀ a' ∈ U ⊓ V, a = h * a' * h⁻¹ → a = 1 := by
    intro a ha a' ha' heq
    have hmem : a ∈ V ⊓ CFSG.conjugate V h⁻¹ := by
      refine ⟨ha.2, BlueprintB2.mem_conjugate_iff.mpr ?_⟩
      rw [heq, show h⁻¹ * (h * a' * h⁻¹) * h⁻¹⁻¹ = a' by group]
      exact ha'.2
    rw [hVhV] at hmem
    exact hmem
  have hbA : ∀ (x : G) (b : Bool), x ∈ U ⊓ V → bpow x b ∈ U ⊓ V := fun x b hx => by
    cases b
    · exact (U ⊓ V).one_mem
    · exact hx
  have hsq₁ : e₁ * e₁ = 1 := hRsq _ (hAR he₁)
  refine ⟨fun i => ?_, hRab, hRsq, fun c hc => ?_, hR32⟩
  · fin_cases i
    · exact hAR he₀
    · exact hAR he₁
    · exact (Subgroup.mem_normalizer_iff.mp hhR e₀).mp (hAR he₀)
    · exact (Subgroup.mem_normalizer_iff.mp hhR e₁).mp (hAR he₁)
    · exact hKR hzK
  · set X := bpow e₀ (c 0) * bpow e₁ (c 1) with hX
    set Y := h * (bpow e₀ (c 2) * bpow e₁ (c 3)) * h⁻¹ with hY
    have hXA : X ∈ U ⊓ V := (U ⊓ V).mul_mem (hbA _ _ he₀) (hbA _ _ he₁)
    have hY' : bpow e₀ (c 2) * bpow e₁ (c 3) ∈ U ⊓ V :=
      (U ⊓ V).mul_mem (hbA _ _ he₀) (hbA _ _ he₁)
    have hYU : Y ∈ U := (Subgroup.mem_normalizer_iff.mp hhU _).mp hY'.1
    have hsplit : ofCoord ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z] c = X * Y * bpow z (c 4) := by
      show bpow e₀ (c 0) * bpow e₁ (c 1) * bpow (h * e₀ * h⁻¹) (c 2) *
        bpow (h * e₁ * h⁻¹) (c 3) * bpow z (c 4) = _
      rw [← conj_bpow, ← conj_bpow, hX, hY]
      group
    rw [hsplit] at hc
    have hc4f : c 4 = false := by
      by_contra h4
      have h4' : c 4 = true := by simpa using h4
      rw [h4', bpow_true] at hc
      have hzU : z ∈ U := by
        have : z = (X * Y)⁻¹ := eq_inv_of_mul_eq_one_right hc
        rw [this]
        exact U.inv_mem (U.mul_mem hXA.1 hYU)
      have : z ∈ U ⊓ Subgroup.centralizer (L : Set G) := ⟨hzU, hzK.2⟩
      rw [hc4] at this
      exact hz1 this
    rw [hc4f, bpow_false, mul_one] at hc
    have hX1 : X = 1 := by
      refine hAhA X hXA _ ((U ⊓ V).inv_mem hY') ?_
      rw [eq_inv_of_mul_eq_one_left hc, hY]
      group
    have hY1 : bpow e₀ (c 2) * bpow e₁ (c 3) = 1 := by
      have h1 : Y = 1 := by rw [hX1, one_mul] at hc; exact hc
      rw [hY] at h1
      calc bpow e₀ (c 2) * bpow e₁ (c 3) =
          h⁻¹ * (h * (bpow e₀ (c 2) * bpow e₁ (c 3)) * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨h0, h1⟩ := bpow_mul_bpow_eq_one he₀1 he₁1 he₁0.symm hsq₁ hX1
    obtain ⟨h2, h3⟩ := bpow_mul_bpow_eq_one he₀1 he₁1 he₁0.symm hsq₁ hY1
    funext i
    fin_cases i <;> assumption


theorem conj_sq_eq {U : Subgroup G} {h u : G} (hh3 : h ^ 3 = 1)
    (hhU : h ∈ Subgroup.normalizer (U : Set G)) (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hUsq : ∀ a ∈ U, a * a = 1) (hUh : ∀ x ∈ U, h * x * h⁻¹ = x → x = 1) (hu : u ∈ U) :
    h * (h * u * h⁻¹) * h⁻¹ = u * (h * u * h⁻¹) := by
  set u₁ := h * u * h⁻¹ with hu₁
  set u₂ := h * u₁ * h⁻¹ with hu₂
  have hu₁U : u₁ ∈ U := (Subgroup.mem_normalizer_iff.mp hhU u).mp hu
  have hu₂U : u₂ ∈ U := (Subgroup.mem_normalizer_iff.mp hhU u₁).mp hu₁U
  have hu₃ : h * u₂ * h⁻¹ = u := by
    have hhh : h * (h * h) = 1 := by simpa [pow_succ, mul_assoc] using hh3
    calc h * u₂ * h⁻¹ = (h * (h * h)) * u * (h * (h * h))⁻¹ := by rw [hu₂, hu₁]; group
      _ = u := by rw [hhh]; group
  have hx : u * u₁ * u₂ = 1 := by
    apply hUh _ (U.mul_mem (U.mul_mem hu hu₁U) hu₂U)
    calc h * (u * u₁ * u₂) * h⁻¹ = (h * u * h⁻¹) * (h * u₁ * h⁻¹) * (h * u₂ * h⁻¹) := by group
      _ = u₁ * u₂ * u := by rw [hu₃]
      _ = u * (u₁ * u₂) := hUab _ (U.mul_mem hu₁U hu₂U) _ hu
      _ = u * u₁ * u₂ := by group
  calc u₂ = (u * u₁) * (u * u₁) * u₂ := by
        rw [hUsq _ (U.mul_mem hu hu₁U), one_mul]
    _ = (u * u₁) * (u * u₁ * u₂) := by group
    _ = u * u₁ := by rw [hx, mul_one]

theorem matB_h_eq {R U : Subgroup G} {h e₀ e₁ z w : G}
    (hB : IsBasis5 R ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z]) (hh3 : h ^ 3 = 1)
    (hhU : h ∈ Subgroup.normalizer (U : Set G)) (hUR : U ≤ R)
    (hUh : ∀ x ∈ U, h * x * h⁻¹ = x → x = 1) (he₀ : e₀ ∈ U) (he₁ : e₁ ∈ U)
    (hwh : h * w * h⁻¹ = w) (hw : w = e₀ * z) :
    matB ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z] h = Bh := by
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => hB.comm a (hUR ha) b (hUR hb)
  have hUsq : ∀ a ∈ U, a * a = 1 := fun a ha => hB.sq a (hUR ha)
  have h₂ := conj_sq_eq hh3 hhU hUab hUsq hUh he₀
  have h₃ := conj_sq_eq hh3 hhU hUab hUsq hUh he₁
  have he₀R : e₀ ∈ R := hUR he₀
  have hzR : z ∈ R := hB.mem 4
  have he₂R : h * e₀ * h⁻¹ ∈ R := hB.mem 2
  have hz : z = e₀ * w := by rw [hw, ← mul_assoc, hB.sq _ he₀R, one_mul]
  have h₄ : h * z * h⁻¹ = e₀ * (h * e₀ * h⁻¹) * z := by
    calc h * z * h⁻¹ = (h * e₀ * h⁻¹) * (h * w * h⁻¹) := by rw [hz]; group
      _ = (h * e₀ * h⁻¹) * (e₀ * z) := by rw [hwh, hw]
      _ = e₀ * (h * e₀ * h⁻¹) * z := by
        rw [← mul_assoc, hB.comm _ he₂R _ he₀R]
  refine hB.matB_eq_of_cols fun j => ?_
  fin_cases j
  · show h * e₀ * h⁻¹ = ofCoord _ _
    simp [ofCoord, bpow, Bh, ofRows]
  · show h * e₁ * h⁻¹ = ofCoord _ _
    simp [ofCoord, bpow, Bh, ofRows]
  · show h * (h * e₀ * h⁻¹) * h⁻¹ = ofCoord _ _
    rw [h₂]
    simp [ofCoord, bpow, Bh, ofRows]
  · show h * (h * e₁ * h⁻¹) * h⁻¹ = ofCoord _ _
    rw [h₃]
    simp [ofCoord, bpow, Bh, ofRows]
  · show h * z * h⁻¹ = ofCoord _ _
    rw [h₄]
    simp [ofCoord, bpow, Bh, ofRows]


theorem exists_bpow_of_mem [Finite G] {A : Subgroup G} (hA : Nat.card A = 4) {e₀ e₁ : G}
    (he₀A : e₀ ∈ A) (he₁A : e₁ ∈ A) (he₀ : e₀ ≠ 1) (he₁ : e₁ ≠ 1) (he : e₀ ≠ e₁)
    (hsq : ∀ a ∈ A, a * a = 1) {a : G} (ha : a ∈ A) :
    ∃ p₀ p₁ : Bool, a = bpow e₀ p₀ * bpow e₁ p₁ := by
  classical
  by_contra hno
  push Not at hno
  have h1 : a ≠ 1 := fun h' => hno false false (by rw [h', bpow_false, bpow_false, mul_one])
  have h2 : a ≠ e₀ := fun h' => hno true false (by rw [h']; simp [bpow])
  have h3 : a ≠ e₁ := fun h' => hno false true (by rw [h']; simp [bpow])
  have h4 : a ≠ e₀ * e₁ := fun h' => hno true true (by rw [h', bpow_true, bpow_true])
  have h01 : e₀ * e₁ ≠ 1 := fun h' => he (by
    calc e₀ = e₀ * e₁ * e₁ := by rw [mul_assoc, hsq _ he₁A, mul_one]
      _ = e₁ := by rw [h', one_mul])
  have h0e : e₀ * e₁ ≠ e₀ := fun h' => he₁ (mul_eq_left.mp h')
  have h1e : e₀ * e₁ ≠ e₁ := fun h' => he₀ (mul_eq_right.mp h')
  set F : Finset G := {a, 1, e₀, e₁, e₀ * e₁} with hF
  have hFc : F.card = 5 := by
    rw [hF, Finset.card_insert_of_notMem (by simp [h1, h2, h3, h4]),
      Finset.card_insert_of_notMem (by simp [he₀.symm, he₁.symm, h01.symm]),
      Finset.card_insert_of_notMem (by simp [he, h0e.symm]),
      Finset.card_insert_of_notMem (by simp [h1e.symm]), Finset.card_singleton]
  have hsub : ((F : Set G)) ⊆ (A : Set G) := by
    intro x hx
    simp only [hF, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ha
    · exact A.one_mem
    · exact he₀A
    · exact he₁A
    · exact A.mul_mem he₀A he₁A
  have hle : Nat.card (F : Set G) ≤ Nat.card A := by
    rw [← SetLike.coe_sort_coe]
    exact Nat.card_mono (Set.toFinite _) hsub
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hFc, hA] at hle
  omega

theorem matB_v_eq {R V A : Subgroup G} [Finite G] {v₀ h e₀ e₁ z : G}
    (hB : IsBasis5 R ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z]) (hD : PhiData R V A v₀)
    (hA : Nat.card A = 4) (hAR : A ≤ R) (he₀A : e₀ ∈ A) (he₁A : e₁ ∈ A) (he₀ : e₀ ≠ 1)
    (he₁ : e₁ ≠ 1) (he : e₀ ≠ e₁) (hvz : v₀ * z * v₀⁻¹ = z)
    (hvh : bmul (bmul (matB ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z] v₀) Bh)
      (matB ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z] v₀) = bmul Bh Bh) :
    matB ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z] v₀ = Bv := by
  have hsqA : ∀ a ∈ A, a * a = 1 := fun a ha => hB.sq a (hAR ha)
  have hvA : ∀ a ∈ A, v₀ * a * v₀⁻¹ = a := fun a ha => by
    rw [hD.comm v₀ hD.mem a (hD.le ha), mul_inv_cancel_right]
  have hvr : ∀ r ∈ R, ∃ p₀ p₁ : Bool, v₀ * r * v₀⁻¹ = bpow e₀ p₀ * bpow e₁ p₁ * r := by
    intro r hr
    have hm := A.inv_mem (hD.comm_mem hr)
    obtain ⟨p₀, p₁, hp⟩ := exists_bpow_of_mem hA he₀A he₁A he₀ he₁ he hsqA hm
    refine ⟨p₀, p₁, ?_⟩
    rw [← hp]
    group
  obtain ⟨p₀, p₁, hp⟩ := hvr _ (hB.mem 2)
  obtain ⟨q₀, q₁, hq⟩ := hvr _ (hB.mem 3)
  have hM : matB ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z] v₀ = Bvs p₀ p₁ q₀ q₁ := by
    refine hB.matB_eq_of_cols fun j => ?_
    fin_cases j
    · show v₀ * e₀ * v₀⁻¹ = ofCoord _ _
      rw [hvA _ he₀A]
      simp [ofCoord, bpow, Bvs, ofRows]
    · show v₀ * e₁ * v₀⁻¹ = ofCoord _ _
      rw [hvA _ he₁A]
      simp [ofCoord, bpow, Bvs, ofRows]
    · show v₀ * (h * e₀ * h⁻¹) * v₀⁻¹ = ofCoord _ _
      rw [show v₀ * (h * e₀ * h⁻¹) * v₀⁻¹ = bpow e₀ p₀ * bpow e₁ p₁ * (h * e₀ * h⁻¹) from hp]
      simp [ofCoord, bpow_true, bpow_false, Bvs, ofRows]
    · show v₀ * (h * e₁ * h⁻¹) * v₀⁻¹ = ofCoord _ _
      rw [show v₀ * (h * e₁ * h⁻¹) * v₀⁻¹ = bpow e₀ q₀ * bpow e₁ q₁ * (h * e₁ * h⁻¹) from hq]
      simp [ofCoord, bpow_true, bpow_false, Bvs, ofRows]
    · show v₀ * z * v₀⁻¹ = ofCoord _ _
      rw [hvz]
      simp [ofCoord, bpow, Bvs, ofRows]
  rw [hM] at hvh ⊢
  exact bv_eq_of_inv p₀ p₁ q₀ q₁ hvh


theorem matB_one {R : Subgroup G} {e : Fin 5 → G} (hB : IsBasis5 R e) : matB e 1 = bone :=
  (hB.matB_eq_bone_iff (Subgroup.one_mem _)).mpr (Subgroup.one_mem _)

theorem matB_comm_of_phi {R V A : Subgroup G} {v₀ y : G} {e : Fin 5 → G}
    (hB : IsBasis5 R e) (hD : PhiData R V A v₀)
    (hyR : y ∈ Subgroup.normalizer (R : Set G)) (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) (hvR : v₀ ∈ Subgroup.normalizer (R : Set G)) :
    bmul (matB e y) (matB e v₀) = bmul (matB e v₀) (matB e y) := by
  rw [← hB.matB_mul hyR hvR, ← hB.matB_mul hvR hyR]
  funext i j
  rw [matB_apply, matB_apply]
  congr 1
  have hs : e j ∈ R := hB.mem j
  have e1 := hD.comm_conj hyR hyV hyA hs
  have hys : y * e j * y⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hyR _).mp hs
  calc y * v₀ * e j * (y * v₀)⁻¹ =
      y * (e j * v₀ * (e j)⁻¹ * v₀⁻¹)⁻¹ * y⁻¹ * (y * e j * y⁻¹) := by group
    _ = ((y * e j * y⁻¹) * v₀ * (y * e j * y⁻¹)⁻¹ * v₀⁻¹)⁻¹ * (y * e j * y⁻¹) := by
        rw [e1]; group
    _ = v₀ * y * e j * (v₀ * y)⁻¹ := by group

theorem matB_y_eq [Finite G] {R V A : Subgroup G} {v₀ h e₀ e₁ z y : G}
    (hB : IsBasis5 R ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z]) (hD : PhiData R V A v₀)
    (hA : Nat.card A = 4) (hAR : A ≤ R) (he₀A : e₀ ∈ A) (he₁A : e₁ ∈ A) (he₀ : e₀ ≠ 1)
    (he₁ : e₁ ≠ 1) (he : e₀ ≠ e₁)
    (hyR : y ∈ Subgroup.normalizer (R : Set G)) (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) (hvR : v₀ ∈ Subgroup.normalizer (R : Set G))
    (hy3 : y ^ 3 = 1) (hyz : y * z * y⁻¹ = z) (hmove : ∃ a ∈ A, y * a * y⁻¹ ≠ a)
    (hMv : matB ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z] v₀ = Bv) :
    ∃ (a b c d : Bool) (x₃ x₄ : Fin 3 → Bool),
      matB ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z] y = By a b c d x₃ x₄ ∧
      (a, b, c, d) ≠ (true, false, false, true) ∧
      bmul (bmul (By a b c d x₃ x₄) (By a b c d x₃ x₄)) (By a b c d x₃ x₄) = bone := by
  set e : Fin 5 → G := ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z] with he_def
  set M := matB e y with hM
  have hsqA : ∀ x ∈ A, x * x = 1 := fun x hx => hB.sq x (hAR hx)
  obtain ⟨a, c, hac⟩ := exists_bpow_of_mem hA he₀A he₁A he₀ he₁ he hsqA
    ((Subgroup.mem_normalizer_iff.mp hyA e₀).mp he₀A)
  obtain ⟨b, d, hbd⟩ := exists_bpow_of_mem hA he₀A he₁A he₀ he₁ he hsqA
    ((Subgroup.mem_normalizer_iff.mp hyA e₁).mp he₁A)
  have hcol : ∀ j (v : Fin 5 → Bool), y * e j * y⁻¹ = ofCoord e v → ∀ i, M i j = v i := by
    intro j v hv i
    rw [hM, matB_apply, hv, hB.coord_ofCoord]
  have h0 := hcol 0 ![a, c, false, false, false] (by
    show y * e₀ * y⁻¹ = _
    rw [hac]; simp [ofCoord, he_def, bpow_false])
  have h1 := hcol 1 ![b, d, false, false, false] (by
    show y * e₁ * y⁻¹ = _
    rw [hbd]; simp [ofCoord, he_def, bpow_false])
  have h4 := hcol 4 ![false, false, false, false, true] (by
    show y * z * y⁻¹ = _
    rw [hyz]; simp [ofCoord, he_def, bpow_false, bpow_true])
  have hcomm := matB_comm_of_phi hB hD hyR hyV hyA hvR
  rw [hMv] at hcomm
  have hent : ∀ i j, bmul M Bv i j = bmul Bv M i j := fun i j => by rw [hcomm]
  have e02 := hent 0 2
  have e12 := hent 1 2
  have e03 := hent 0 3
  have e13 := hent 1 3
  simp only [bmul, Bv, Bvs, ofRows] at e02 e12 e03 e13
  simp at e02 e12 e03 e13
  have hM22 : M 2 2 = M 0 0 := by
    revert e02; cases M 0 0 <;> cases M 2 2 <;> cases M 0 2 <;> simp
  have hM32 : M 3 2 = M 1 0 := by
    revert e12; cases M 1 0 <;> cases M 3 2 <;> cases M 1 2 <;> simp
  have hM23 : M 2 3 = M 0 1 := by
    revert e03; cases M 0 1 <;> cases M 2 3 <;> cases M 0 3 <;> simp
  have hM33 : M 3 3 = M 1 1 := by
    revert e13; cases M 1 1 <;> cases M 3 3 <;> cases M 1 3 <;> simp
  have hMeq : M = By a b c d ![M 0 2, M 1 2, M 4 2] ![M 0 3, M 1 3, M 4 3] := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [By, ofRows, h0, h1, h4, hM22, hM32, hM23, hM33]
  refine ⟨a, b, c, d, _, _, hMeq, ?_, ?_⟩
  ·
    rintro ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨x, hx, hyx⟩ := hmove
    obtain ⟨p₀, p₁, rfl⟩ := exists_bpow_of_mem hA he₀A he₁A he₀ he₁ he hsqA hx
    apply hyx
    have hy0 : y * e₀ * y⁻¹ = e₀ := by rw [hac]; simp [bpow]
    have hy1 : y * e₁ * y⁻¹ = e₁ := by rw [hbd]; simp [bpow]
    have hb0 : y * bpow e₀ p₀ * y⁻¹ = bpow e₀ p₀ := by rw [conj_bpow, hy0]
    have hb1 : y * bpow e₁ p₁ * y⁻¹ = bpow e₁ p₁ := by rw [conj_bpow, hy1]
    calc y * (bpow e₀ p₀ * bpow e₁ p₁) * y⁻¹ =
        (y * bpow e₀ p₀ * y⁻¹) * (y * bpow e₁ p₁ * y⁻¹) := by group
      _ = bpow e₀ p₀ * bpow e₁ p₁ := by rw [hb0, hb1]
  · rw [← hMeq, hM, ← hB.matB_mul hyR hyR, ← hB.matB_mul (Subgroup.mul_mem _ hyR hyR) hyR]
    have : y * y * y = 1 := by rw [← hy3, pow_succ, pow_two]
    rw [this]
    exact matB_one hB


theorem bmul_bone_left (M : B5) : bmul bone M = M := by
  funext i j
  fin_cases i <;> simp [bmul, bone]

theorem card_comap_of_surjective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (H : Subgroup Y) :
    Nat.card (H.comap f) = Nat.card H * Nat.card f.ker := by
  let g : ↥(H.comap f) →* ↥H := (f.comp (H.comap f).subtype).codRestrict H fun x => x.2
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hker : g.ker = f.ker.subgroupOf (H.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hle : f.ker ≤ H.comap f := fun x hx => by
    show f x ∈ H
    rw [MonoidHom.mem_ker.mp hx]
    exact H.one_mem
  rw [← Subgroup.card_ker_mul_card_range g, MonoidHom.range_eq_top.mpr hg, Subgroup.card_top,
    hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, mul_comm]

theorem false_of_D8 [Finite G] {R : Subgroup G} {e : Fin 5 → G} (hB : IsBasis5 R e)
    (hCR : Subgroup.centralizer (R : Set G) ≤ R)
    (hT : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) {a b : G}
    (ha : a ∈ Subgroup.normalizer (R : Set G)) (hb : b ∈ Subgroup.normalizer (R : Set G))
    (hD8 : D8 (matB e a) (matB e b)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨haa, hbb, hab4, hab2⟩ := hD8
  set N := Subgroup.normalizer (R : Set G) with hN
  have hRN : R ≤ N := Subgroup.le_normalizer
  set Rn := R.subgroupOf N with hRn
  have : Rn.Normal := Subgroup.normal_subgroupOf_iff_le_normalizer hRN |>.mpr le_rfl
  set π := QuotientGroup.mk' Rn with hπ
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 5) (by rw [hB.card]; norm_num)
  have hmat : ∀ x : ↥N, matB e (x : G) = bone ↔ π x = 1 := by
    intro x
    rw [hB.matB_eq_bone_iff x.2, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      hRn, Subgroup.mem_subgroupOf]
    exact ⟨fun h => hCR h, fun h => Subgroup.mem_centralizer_iff.mpr fun r hr =>
      hB.comm r hr _ h⟩
  set a' : ↥N := ⟨a, ha⟩
  set b' : ↥N := ⟨b, hb⟩
  have hmul : ∀ x y : ↥N, matB e ((x * y : ↥N) : G) = bmul (matB e x) (matB e y) :=
    fun x y => hB.matB_mul x.2 y.2
  have h1 : π a' * π a' = 1 := by
    rw [← map_mul, ← hmat, hmul]
    exact haa
  have h2 : π b' * π b' = 1 := by
    rw [← map_mul, ← hmat, hmul]
    exact hbb
  have h4 : (π a' * π b') ^ 4 = 1 := by
    rw [show (π a' * π b') ^ 4 = π ((a' * b') * (a' * b') * ((a' * b') * (a' * b'))) by
      simp only [map_mul, pow_succ, pow_zero, one_mul, mul_assoc]]
    rw [← hmat]
    simp only [hmul]
    exact hab4
  have h2' : (π a' * π b') ^ 2 ≠ 1 := by
    rw [show (π a' * π b') ^ 2 = π ((a' * b') * (a' * b')) by
      simp only [map_mul, pow_succ, pow_zero, one_mul, mul_assoc]]
    intro hc
    apply hab2
    have := (hmat _).mpr hc
    simpa only [hmul] using this
  obtain ⟨hD2, hD8c⟩ := isPGroup_closure_of_D8 h1 h2 h4 h2'
  set D := (Subgroup.closure {π a', π b'}).comap π with hD
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hR2.comap_of_injective N.subtype N.subtype_injective
  have hDp : IsPGroup 2 D := hD2.comap_of_ker_isPGroup π hker
  have hDc : Nat.card D = Nat.card (Subgroup.closure {π a', π b'}) * Nat.card π.ker :=
    card_comap_of_surjective π (QuotientGroup.mk'_surjective Rn) _
  have hkc : Nat.card π.ker = 32 := by
    rw [hπ, QuotientGroup.ker_mk', hRn, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv,
      hB.card]
  have hP := hT (D.map N.subtype) (hDp.map N.subtype)
  rw [Subgroup.card_map_of_injective N.subtype_injective, hDc, hkc] at hP
  omega


theorem dihedral_three_inv : ∀ x y : DihedralGroup 3, x ^ 2 = 1 → x ≠ 1 → y ^ 3 = 1 →
    x * y * x⁻¹ * y = 1 := by
  decide

theorem conj_h_mem_U [Finite G] {T L V H P U I : Subgroup G} {h : G} {n : ℕ}
    (hC : Config12_2_24 T L V H P U I h n 3) {v₀ : G} (hv₀I : v₀ ∈ I) (hv₀U : v₀ ∉ U)
    (hv₀2 : v₀ * v₀ = 1) (hhI : h ∈ I) (hh3 : h ^ 3 = 1) : v₀ * h * v₀⁻¹ * h ∈ U := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨_, ⟨eD⟩⟩, -⟩ := hC
  set ψ : ↥I →* DihedralGroup 3 := eD.toMonoidHom.comp (QuotientGroup.mk' (U.subgroupOf I))
    with hψ
  have hker : ∀ x : ↥I, ψ x = 1 → (x : G) ∈ U := by
    intro x hx
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  set v' : ↥I := ⟨v₀, hv₀I⟩
  set h' : ↥I := ⟨h, hhI⟩
  have h1 : ψ v' ^ 2 = 1 := by
    rw [← map_pow, pow_two]
    have : v' * v' = 1 := Subtype.ext hv₀2
    rw [this, map_one]
  have h2 : ψ v' ≠ 1 := fun h' => hv₀U (hker v' h')
  have h3 : ψ h' ^ 3 = 1 := by
    rw [← map_pow]
    have : h' ^ 3 = 1 := Subtype.ext hh3
    rw [this, map_one]
  have h4 := dihedral_three_inv _ _ h1 h2 h3
  have h5 : ψ (v' * h' * v'⁻¹ * h') = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv]
    exact h4
  exact hker _ h5


end Lem25

open Lem25

theorem lem12225CTL3_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) : Lem12225CTL3 := by
  intro G _ _ T L V H P U I h n p hH hNE hC hn
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hz
  obtain ⟨z, w, e₀, hzK, hz1, -, hwI, he₀, he₀1, hw, hR32⟩ :=
    exists_z_w_three h331 h1222 h323 h1216 h1220 hH hNE hC hn hz
  obtain ⟨e₁, he₁, he₁1, he₁0, hB⟩ :=
    exists_basis_three h331 h1222 h323 h1216 h1220 hH hNE hC hn hzK hz1 he₀ he₀1 hR32
  set e : Fin 5 → G := ![e₀, e₁, h * e₀ * h⁻¹, h * e₁ * h⁻¹, z] with he_def
  have hp3 : p = 3 := prime_eq_three_of_three h331 h1222 h323 h1216 h1220 hH hNE hC hn
  subst hp3
  obtain ⟨hhR, hhI, hhU⟩ := h_mem_NR h331 h1222 h323 h1216 h1220 hH hNE hC
  have hA : Nat.card ↥(U ⊓ V) = 4 := by rw [card_inf_V hC, hn]; norm_num
  have hAR := inf_V_le_RR hH hC
  obtain ⟨hKR, -⟩ := CTL_facts h331 h1222 h323 h1216 h1220 hH hNE hC
  have hUR : U ≤ RR T U := by
    obtain ⟨-, -, hc3, -⟩ := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h n 3 hH
      hNE hC
    intro u hu
    show u ∈ T ⊓ Subgroup.centralizer (U : Set G)
    rw [hc3]
    exact Subgroup.mem_sup_left hu
  have hh3 : h ^ 3 = 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hord, -⟩ := hC
    rw [← hord]
    exact pow_orderOf_eq_one h
  have hUh : ∀ x ∈ U, h * x * h⁻¹ = x → x = 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, hP, -, -, -, -, -, -, -, -, -, hUP, -⟩ := hC
    intro x hx hfix
    have hxP : x ∈ U ⊓ Subgroup.centralizer (P : Set G) := by
      refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      rw [hP] at hk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      have hc : Commute h x := by
        calc h * x = h * x * h⁻¹ * h := by group
          _ = x * h := by rw [hfix]
      exact (hc.zpow_left j).eq
    rw [hUP, Subgroup.mem_bot] at hxP
    exact hxP
  have hwh : h * w * h⁻¹ = w := by
    rw [Subgroup.mem_centralizer_iff.mp hwI.2 h hhI, mul_inv_cancel_right]
  have hMh : matB e h = Bh := matB_h_eq hB hh3 hhU hUR hUh he₀.1 he₁.1 hwh hw
  obtain ⟨v₀, hD⟩ := exists_phiData h1222 hH hC
  have hVT : V ≤ T := S125.le_of_hyp1223 hH
  have hvR : v₀ ∈ Subgroup.normalizer ((RR T U : Subgroup G) : Set G) :=
    le_normalizer_R hC (hVT hD.mem)
  have hVL := V_le_L' hH
  have hvz : v₀ * z * v₀⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hzK.2 v₀ (hVL hD.mem), mul_inv_cancel_right]
  have hv2 : v₀ * v₀ = 1 := by
    have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
    rw [← pow_two]
    exact hVe.2 _ hD.mem
  have hVI : V ≤ I := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hI, -⟩ := hC
    rw [hI]
    exact le_sup_left
  have hv₀U : v₀ ∉ U := fun h' => hD.not_mem ⟨h', hD.mem⟩
  have hxU := conj_h_mem_U hC (hVI hD.mem) hv₀U hv2 hhI hh3
  have hvh : bmul (bmul (matB e v₀) Bh) (matB e v₀) = bmul Bh Bh := by
    have hxN : v₀ * h * v₀⁻¹ * h ∈ Subgroup.normalizer ((RR T U : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hvR hhR)
        (Subgroup.inv_mem _ hvR)) hhR
    have hx1 : matB e (v₀ * h * v₀⁻¹ * h) = bone :=
      (hB.matB_eq_bone_iff hxN).mpr
        (Subgroup.mem_centralizer_iff.mpr fun r hr => hB.comm r hr _ (hUR hxU))
    have hv' : v₀⁻¹ = v₀ := inv_eq_of_mul_eq_one_right hv2
    have hhh : h * (h * h) = 1 := by simpa [pow_succ, mul_assoc] using hh3
    have eq1 : v₀ * h * v₀ = (v₀ * h * v₀⁻¹ * h) * (h * h) := by
      rw [hv']
      calc v₀ * h * v₀ = v₀ * h * v₀ * (h * (h * h)) := by rw [hhh, mul_one]
        _ = (v₀ * h * v₀ * h) * (h * h) := by group
    rw [← hMh, ← hB.matB_mul hvR hhR, ← hB.matB_mul (Subgroup.mul_mem _ hvR hhR) hvR, eq1,
      hB.matB_mul hxN (Subgroup.mul_mem _ hhR hhR), hx1, bmul_bone_left,
      hB.matB_mul hhR hhR]
  have hMv : matB e v₀ = Bv := matB_v_eq hB hD hA hAR he₀ he₁ he₀1 he₁1 he₁0.symm hvz hvh
  obtain ⟨y, hyY, hy3, -, hmove⟩ := exists_Y_three h1222 h1220 hH hNE hC hn
  have hyR : y ∈ Subgroup.normalizer ((RR T U : Subgroup G) : Set G) :=
    YY_le_NR h331 h1222 h323 h1216 h1220 hH hNE hC hyY
  have hyL : y ∈ L := (oTwoUpper_le _).trans inf_le_left hyY
  have hyV : y ∈ Subgroup.normalizer (V : Set G) := le_normalizer_of_hyp1223 hH hyL
  have hyA := YY_le_normalizer hyY
  have hyz : y * z * y⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hzK.2 y hyL, mul_inv_cancel_right]
  obtain ⟨a, b, c, d, x₃, x₄, hMy, hne, hcube⟩ := matB_y_eq hB hD hA hAR he₀ he₁ he₀1 he₁1
    he₁0.symm hyR hyV hyA hvR hy3 hyz hmove hMv
  obtain ⟨i, j, hW⟩ := wit_of_cube a b c d x₃ x₄ hcube hne
  set N := Subgroup.normalizer ((RR T U : Subgroup G) : Set G) with hN
  set h' : ↥N := ⟨h, hhR⟩
  set v' : ↥N := ⟨v₀, hvR⟩
  set y' : ↥N := ⟨y, hyR⟩
  have hmul : ∀ x x' : ↥N, matB e ((x * x' : ↥N) : G) = bmul (matB e x) (matB e x') :=
    fun x x' => hB.matB_mul x.2 x'.2
  have hh' : matB e (h' : G) = Bh := hMh
  have hv'' : matB e (v' : G) = Bv := hMv
  have hy' : matB e (y' : G) = By a b c d x₃ x₄ := hMy
  let gA : Fin 2 → ↥N := ![v', y' * h' * (y' * y') * v']
  let gB : Fin 5 → ↥N := ![h' * y' * (h' * h') * (y' * y'), h' * y' * h' * (y' * y'),
    h' * y' * h' * (y' * y') * h' * v', h' * y' * (h' * h') * (y' * y') * h' * v',
    h' * (y' * y') * (h' * h') * y' * h' * v']
  have hgA : matB e ((gA i : ↥N) : G) = wA i (By a b c d x₃ x₄) := by
    fin_cases i
    · show matB e (v' : G) = Bv
      exact hv''
    · show matB e ((y' * h' * (y' * y') * v' : ↥N) : G) =
        bmul (bmul (bmul (By a b c d x₃ x₄) Bh) (bmul (By a b c d x₃ x₄) (By a b c d x₃ x₄))) Bv
      simp only [hmul, hh', hv'', hy']
  have hgB : matB e ((gB j : ↥N) : G) = wB j (By a b c d x₃ x₄) := by
    set Y := By a b c d x₃ x₄
    fin_cases j
    · show matB e ((h' * y' * (h' * h') * (y' * y') : ↥N) : G) =
        bmul (bmul (bmul Bh Y) (bmul Bh Bh)) (bmul Y Y)
      simp only [hmul, hh', hy']
    · show matB e ((h' * y' * h' * (y' * y') : ↥N) : G) = bmul (bmul (bmul Bh Y) Bh) (bmul Y Y)
      simp only [hmul, hh', hy']
    · show matB e ((h' * y' * h' * (y' * y') * h' * v' : ↥N) : G) =
        bmul (bmul (bmul (bmul (bmul Bh Y) Bh) (bmul Y Y)) Bh) Bv
      simp only [hmul, hh', hv'', hy']
    · show matB e ((h' * y' * (h' * h') * (y' * y') * h' * v' : ↥N) : G) =
        bmul (bmul (bmul (bmul (bmul Bh Y) (bmul Bh Bh)) (bmul Y Y)) Bh) Bv
      simp only [hmul, hh', hv'', hy']
    · show matB e ((h' * (y' * y') * (h' * h') * y' * h' * v' : ↥N) : G) =
        bmul (bmul (bmul (bmul (bmul Bh (bmul Y Y)) (bmul Bh Bh)) Y) Bh) Bv
      simp only [hmul, hh', hv'', hy']
  rw [← hgA, ← hgB] at hW
  have hT : ∀ Q : Subgroup G, IsPGroup 2 Q → Nat.card Q ≤ 2 ^ 7 := by
    intro Q hQ
    obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
    obtain ⟨S', hS'⟩ := hQ.exists_le_sylow
    have h1 := Subgroup.card_le_of_le hS'
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S] at h1
    exact h1.trans (card_T_le_three h331 h1222 h323 h1216 h1220 hH hNE hC hn)
  exact false_of_D8 hB (centralizer_R_le hH hC) hT (gA i).2 (gB j).2 hW

end CFSG.Quasithin.H13
