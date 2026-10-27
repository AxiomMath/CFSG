module

public import CFSG.Quasithin.Background.FixVTransport
public import CFSG.Quasithin.Background.Asc81cTenFour
public import CFSG.Quasithin.Background.B1Coprime

public section

namespace CFSG.Quasithin

namespace Asc81c

open scoped Pointwise

variable {W : Type*} [CommGroup W]

section Conj

theorem commSub_map_conj (X : Subgroup (MulAut W)) (φ : MulAut W) :
    commSub ⊤ (X.map (MulAut.conj φ).toMonoidHom) = (commSub ⊤ X).map φ.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, w, -, rfl⟩
    refine ⟨x (φ⁻¹ w) * (φ⁻¹ w)⁻¹, ⟨x, hx, φ⁻¹ w, Subgroup.mem_top _, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]
  · rintro ⟨d, ⟨x, hx, w, -, rfl⟩, rfl⟩
    refine ⟨φ * x * φ⁻¹, ⟨x, hx, rfl⟩, φ w, Subgroup.mem_top _, ?_⟩
    simp [MulAut.mul_apply]

theorem fixV_map_conj (X : Subgroup (MulAut W)) (φ : MulAut W) :
    fixV (X.map (MulAut.conj φ).toMonoidHom) = (fixV X).map φ.toMonoidHom :=
  fixV_map_conj_eq X φ

end Conj

section Coprime

variable [Finite W]

omit [Finite W] in
theorem commSub_stable' {X : Subgroup (MulAut W)} {x : MulAut W} (hx : x ∈ X) {u : W}
    (hu : u ∈ commSub (⊤ : Subgroup W) X) : x u ∈ commSub (⊤ : Subgroup W) X := by
  have h := commSub_map_conj X x
  have hX : X.map (MulAut.conj x).toMonoidHom = X := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact X.mul_mem (X.mul_mem hx hz) (X.inv_mem hx)
    · intro hy
      exact ⟨x⁻¹ * y * x, X.mul_mem (X.mul_mem (X.inv_mem hx) hy) hx, by
        simp [MulAut.conj_apply, mul_assoc]⟩
  rw [hX] at h
  rw [h]
  exact ⟨u, hu, rfl⟩

theorem fixV_inf_commSub_eq_bot' (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hY : Odd (Nat.card Y)) : fixV Y ⊓ commSub ⊤ Y = ⊥ := by
  have h := (B1.coprime_decomp hW hY (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)).2
  rwa [top_inf_eq] at h

theorem fixV_sup_commSub_eq_top' (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hY : Odd (Nat.card Y)) : fixV Y ⊔ commSub ⊤ Y = ⊤ := by
  have h := (B1.coprime_decomp hW hY (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)).1
  rwa [top_inf_eq] at h

theorem commSub_commSub_eq' (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hY : Odd (Nat.card Y)) : commSub (commSub ⊤ Y) Y = commSub ⊤ Y := by
  have h := (B1.coprime_decomp hW hY (M := commSub ⊤ Y)
    (fun y hy m hm => commSub_stable' hy hm)).1
  have hbot : commSub (⊤ : Subgroup W) Y ⊓ fixV Y = ⊥ := by
    rw [inf_comm]
    exact fixV_inf_commSub_eq_bot' hW hY
  rwa [hbot, bot_sup_eq] at h

theorem card_fixV_mul_card_commSub (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hY : Odd (Nat.card Y)) : Nat.card (fixV Y) * Nat.card (commSub ⊤ Y) = Nat.card W := by
  have h := card_sup_mul_card_inf (fixV Y) (commSub ⊤ Y)
  rw [fixV_inf_commSub_eq_bot' hW hY, fixV_sup_commSub_eq_top' hW hY, Subgroup.card_bot,
    mul_one, Subgroup.card_top] at h
  exact h.symm

end Coprime

section Hyp

theorem hyp102_map_conj {G X : Subgroup (MulAut W)} (h : Hyp102 G X) {φ : MulAut W}
    (hφ : φ ∈ G) : Hyp102 G (X.map (MulAut.conj φ).toMonoidHom) := by
  obtain ⟨⟨hXG, hX1, hcyc, hodd, hreg, hnorm⟩, hrk⟩ := h
  have hinj : Function.Injective (MulAut.conj φ).toMonoidHom := (MulAut.conj φ).injective
  have hcard : Nat.card (X.map (MulAut.conj φ).toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective hinj
  have hcomm := commSub_map_conj X φ
  have hfix := fixV_map_conj X φ
  have hφinj : Function.Injective φ.toMonoidHom := φ.injective
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact G.mul_mem (G.mul_mem hφ (hXG hx)) (G.inv_mem hφ)
  · intro h0
    exact hX1 ((Subgroup.map_eq_bot_iff_of_injective X hinj).1 h0)
  · exact isCyclic_of_surjective (Subgroup.equivMapOfInjective X _ hinj).toMonoidHom
      (Subgroup.equivMapOfInjective X _ hinj).surjective
  · rw [hcard]
    exact hodd
  · intro v hv hv1 w hw hw1
    rw [hcomm] at hv hw
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    have hv₀1 : v₀ ≠ 1 := fun h => hv1 (by rw [h]; exact map_one _)
    have hw₀1 : w₀ ≠ 1 := fun h => hw1 (by rw [h]; exact map_one _)
    obtain ⟨x, hx, huniq⟩ := hreg v₀ hv₀ hv₀1 w₀ hw₀ hw₀1
    refine ⟨⟨φ * x * φ⁻¹, ⟨x, x.2, rfl⟩⟩, ?_, ?_⟩
    · show (φ * (x : MulAut W) * φ⁻¹) (φ v₀) = φ w₀
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hx]
    · rintro ⟨y, ⟨y₀, hy₀, rfl⟩⟩ hy
      have hy' : y₀ v₀ = w₀ := by
        have h1 : (φ * y₀ * φ⁻¹) (φ v₀) = φ w₀ := hy
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self] at h1
        exact φ.injective h1
      have h2 := huniq ⟨y₀, hy₀⟩ hy'
      apply Subtype.ext
      show φ * y₀ * φ⁻¹ = φ * (x : MulAut W) * φ⁻¹
      rw [show y₀ = (x : MulAut W) from congrArg Subtype.val h2]
  · rintro g hg hgfix _ ⟨x, hx, rfl⟩
    have hg' : φ⁻¹ * g * φ ∈ G := G.mul_mem (G.mul_mem (G.inv_mem hφ) hg) hφ
    have hg'fix : (fixV X).map (φ⁻¹ * g * φ).toMonoidHom = fixV X := by
      rw [hfix] at hgfix
      ext v
      constructor
      · rintro ⟨u, hu, rfl⟩
        have h1 : g (φ u) ∈ (fixV X).map φ.toMonoidHom := by
          rw [← hgfix]
          exact ⟨φ u, ⟨u, hu, rfl⟩, rfl⟩
        obtain ⟨u', hu', hu'e⟩ := h1
        have : (φ⁻¹ * g * φ) u = u' := by
          rw [MulAut.mul_apply, MulAut.mul_apply]
          have h2 : φ u' = g (φ u) := hu'e
          rw [← h2, MulAut.inv_apply_self]
        show (φ⁻¹ * g * φ) u ∈ fixV X
        rw [this]
        exact hu'
      · intro hv
        have h1 : φ v ∈ ((fixV X).map φ.toMonoidHom).map g.toMonoidHom := by
          rw [hgfix]
          exact ⟨v, hv, rfl⟩
        obtain ⟨_, ⟨u, hu, rfl⟩, hue⟩ := h1
        refine ⟨u, hu, ?_⟩
        show (φ⁻¹ * g * φ) u = v
        rw [MulAut.mul_apply, MulAut.mul_apply]
        have h2 : g (φ u) = φ v := hue
        rw [h2, MulAut.inv_apply_self]
    have h3 := hnorm _ hg' hg'fix x hx
    refine ⟨(φ⁻¹ * g * φ) * x * (φ⁻¹ * g * φ)⁻¹, h3, ?_⟩
    show φ * ((φ⁻¹ * g * φ) * x * (φ⁻¹ * g * φ)⁻¹) * φ⁻¹ = g * (φ * x * φ⁻¹) * g⁻¹
    group
  · rw [hcomm]
    unfold rk
    rw [Subgroup.card_map_of_injective hφinj]
    exact hrk

end Hyp

section Odd

theorem odd_card_iSup_of_commute {ι : Type*} [Fintype ι] {Γ : Type*} [Group Γ] [Finite Γ]
    {L : ι → Subgroup Γ} (hcomm : ∀ i j, i ≠ j → ∀ a ∈ L i, ∀ b ∈ L j, a * b = b * a)
    (hodd : ∀ i, Odd (Nat.card (L i))) : Odd (Nat.card ↥(⨆ i, L i)) := by
  have hc : Pairwise fun i j => ∀ (x y : Γ), x ∈ L i → y ∈ L j → Commute x y :=
    fun i j hij x y hx hy => hcomm i j hij x hx y hy
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hc)]
  have hdvd := Subgroup.card_range_dvd (Subgroup.noncommPiCoprod hc)
  rw [Nat.card_pi] at hdvd
  have hprod : Odd (∏ i, Nat.card (L i)) := by
    rw [← Nat.coprime_two_left]
    exact Nat.Coprime.prod_right fun i _ => Nat.coprime_two_left.2 (hodd i)
  exact Odd.of_dvd_nat hprod hdvd

end Odd

section Frob

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem exists_pow_sq_eq_self {d : Γ} (hodd : Odd (orderOf d)) : ∃ k : ℕ, (d ^ 2) ^ k = d := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨m + 1, ?_⟩
  rw [← pow_mul, show 2 * (m + 1) = orderOf d + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]

omit [Finite Γ] in
theorem eq_one_or_of_mem_zpowers_three {x y : Γ} (hx : orderOf x = 3)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hmod : x ^ k = x ^ (k % 3) := by
    rw [← zpow_mod_orderOf, hx]
    norm_num
  rw [hmod]
  rcases hk with h | h | h
  · left
    rw [h, zpow_zero]
  · right; left
    rw [h, zpow_one]
  · right; right
    rw [h, eq_inv_iff_mul_eq_one, ← zpow_add_one]
    norm_num
    exact_mod_cast hx3

theorem mem_centralizer_of_odd_of_card_three {X : Subgroup Γ} (hX : Nat.card X = 3) {f : Γ}
    (hf : Odd (orderOf f)) (hfN : f ∈ Subgroup.normalizer (X : Set Γ)) :
    f ∈ Subgroup.centralizer (X : Set Γ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨x, hxX⟩, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hX])
  have hx' : orderOf x = 3 := by rwa [Subgroup.orderOf_mk] at hx
  have hXz : X = Subgroup.zpowers x := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxX)
    rw [Nat.card_zpowers, hx', hX]
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx'; omega
  have hfx : f * x * f⁻¹ = x := by
    have hy : f * x * f⁻¹ ∈ Subgroup.zpowers x :=
      hXz ▸ (Subgroup.mem_normalizer_iff.1 hfN x).1 hxX
    rcases eq_one_or_of_mem_zpowers_three hx' hy with h | h | h
    · exfalso
      apply hx1
      have : x = f⁻¹ * (f * x * f⁻¹) * f := by group
      rw [this, h]
      group
    · exact h
    · exfalso
      have h2 : f * f * x = x * (f * f) := by
        calc f * f * x = f * (f * x * f⁻¹) * f := by group
          _ = f * x⁻¹ * f := by rw [h]
          _ = (f * x * f⁻¹)⁻¹ * (f * f) := by group
          _ = x * (f * f) := by rw [h, inv_inv]
      obtain ⟨k, hk⟩ := exists_pow_sq_eq_self hf
      have hc : f * x = x * f := by
        have h2' : Commute (f ^ 2) x := by
          rw [sq]
          exact h2
        have := (Commute.pow_left h2' k).eq
        rwa [hk] at this
      have h3 : f * x * f⁻¹ = x := by rw [hc]; group
      rw [h3] at h
      have h4 : x * x = 1 := by
        calc x * x = x * x⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel x
      have h5 : x ^ 2 = 1 := by rw [sq]; exact h4
      have h6 := orderOf_dvd_of_pow_eq_one h5
      rw [hx'] at h6
      omega
  rw [Subgroup.mem_centralizer_iff, hXz]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hc : x * f = f * x := by
    calc x * f = f * x * f⁻¹ * f := by rw [hfx]
      _ = f * x := by group
  exact (Commute.zpow_left (show Commute x f from hc) k).eq

omit [Finite Γ] in
theorem comm_of_card_prime {P : Subgroup Γ} {p : ℕ} (hp : p.Prime) (hP : Nat.card P = p) :
    ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic P := isCyclic_of_prime_card hP
  let _ : CommGroup P := IsCyclic.commGroup
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : P) ⟨b, hb⟩)

theorem exists_card_seven {F : Subgroup Γ} (hF : Nat.card F = 21) :
    ∃ P : Subgroup Γ, P ≤ F ∧ Nat.card P = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) 7 (n := 1)
    (by rw [hF]; norm_num)
  refine ⟨K.map F.subtype, Subgroup.map_subtype_le K, ?_⟩
  rw [Subgroup.card_map_of_injective F.subtype_injective, hK, pow_one]

theorem sup_eq_of_card_three_seven {F X P : Subgroup Γ} (hF : Nat.card F = 21) (hXF : X ≤ F)
    (hPF : P ≤ F) (hX : Nat.card X = 3) (hP : Nat.card P = 7) : X ⊔ P = F := by
  apply Subgroup.eq_of_le_of_card_ge (sup_le hXF hPF)
  have h3 : 3 ∣ Nat.card ↥(X ⊔ P) := hX ▸ Subgroup.card_dvd_of_le le_sup_left
  have h7 : 7 ∣ Nat.card ↥(X ⊔ P) := hP ▸ Subgroup.card_dvd_of_le le_sup_right
  have h21 : 21 ∣ Nat.card ↥(X ⊔ P) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 7) h3 h7
  have hle : Nat.card ↥(X ⊔ P) ∣ 21 := hF ▸ Subgroup.card_dvd_of_le (sup_le hXF hPF)
  rw [hF]
  exact (Nat.dvd_antisymm hle h21).ge

theorem not_le_normalizer_of_frob21 {F X : Subgroup Γ} (hF : Nat.card F = 21)
    (hna : ∃ a ∈ F, ∃ b ∈ F, a * b ≠ b * a) (hXF : X ≤ F) (hX : Nat.card X = 3) :
    ¬ F ≤ Subgroup.normalizer (X : Set Γ) := by
  intro hFN
  have hFC : F ≤ Subgroup.centralizer (X : Set Γ) := fun f hf =>
    mem_centralizer_of_odd_of_card_three hX
      (Odd.of_dvd_nat (by decide) (hF ▸ Subgroup.orderOf_dvd_natCard F hf)) (hFN hf)
  obtain ⟨P, hPF, hP⟩ := exists_card_seven hF
  have hXP := sup_eq_of_card_three_seven hF hXF hPF hX hP
  have hPN : P ≤ Subgroup.normalizer (X : Set Γ) := hPF.trans hFN
  have hcoe : ((X ⊔ P : Subgroup Γ) : Set Γ) = (X : Set Γ) * (P : Set Γ) :=
    Subgroup.coe_mul_of_right_le_normalizer_left X P hPN
  have hXc := comm_of_card_prime Nat.prime_three hX
  have hPc := comm_of_card_prime (by norm_num : Nat.Prime 7) hP
  have hcen : ∀ x ∈ X, ∀ f ∈ F, x * f = f * x := fun x hx f hf =>
    Subgroup.mem_centralizer_iff.1 (hFC hf) x hx
  obtain ⟨a, ha, b, hb, hab⟩ := hna
  apply hab
  have ha' : a ∈ ((X ⊔ P : Subgroup Γ) : Set Γ) := by rw [hXP]; exact ha
  have hb' : b ∈ ((X ⊔ P : Subgroup Γ) : Set Γ) := by rw [hXP]; exact hb
  rw [hcoe] at ha' hb'
  obtain ⟨x₁, hx₁, p₁, hp₁, rfl⟩ := ha'
  obtain ⟨x₂, hx₂, p₂, hp₂, rfl⟩ := hb'
  have hp₁F := hPF hp₁
  have hp₂F := hPF hp₂
  calc x₁ * p₁ * (x₂ * p₂) = x₁ * (p₁ * x₂) * p₂ := by group
    _ = x₁ * (x₂ * p₁) * p₂ := by rw [hcen x₂ hx₂ p₁ hp₁F]
    _ = (x₁ * x₂) * (p₁ * p₂) := by group
    _ = (x₂ * x₁) * (p₂ * p₁) := by rw [hXc x₁ hx₁ x₂ hx₂, hPc p₁ hp₁ p₂ hp₂]
    _ = x₂ * (x₁ * p₂) * p₁ := by group
    _ = x₂ * (p₂ * x₁) * p₁ := by rw [hcen x₁ hx₁ p₂ hp₂F]
    _ = x₂ * p₂ * (x₁ * p₁) := by group

theorem sup_eq_of_frob21 {F X X' : Subgroup Γ} (hF : Nat.card F = 21) (hXF : X ≤ F)
    (hX'F : X' ≤ F) (hX : Nat.card X = 3) (hX' : Nat.card X' = 3) (hne : X ≠ X') :
    X ⊔ X' = F := by
  apply Subgroup.eq_of_le_of_card_ge (sup_le hXF hX'F)
  have h3 : 3 ∣ Nat.card ↥(X ⊔ X') := hX ▸ Subgroup.card_dvd_of_le le_sup_left
  have hle : Nat.card ↥(X ⊔ X') ∣ 21 := hF ▸ Subgroup.card_dvd_of_le (sup_le hXF hX'F)
  obtain ⟨k, hk⟩ := h3
  have hk7 : k ∣ 7 := by
    rw [hk, show (21 : ℕ) = 3 * 7 by norm_num] at hle
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hle
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hk7 with h1 | h7
  · exfalso
    rw [h1, mul_one] at hk
    apply hne
    have e1 : X = X ⊔ X' := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk, hX])
    have e2 : X' = X ⊔ X' := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hk, hX'])
    rw [e1, ← e2]
  · rw [hF, hk, h7]

theorem map_conj_ne_of_frob21 {F X P : Subgroup Γ} (hF : Nat.card F = 21)
    (hna : ∃ a ∈ F, ∃ b ∈ F, a * b ≠ b * a) (hXF : X ≤ F) (hX : Nat.card X = 3) (hPF : P ≤ F)
    (hP : Nat.card P = 7) {a : Γ} (ha : a ∈ P) (ha1 : a ≠ 1) :
    X.map (MulAut.conj a).toMonoidHom ≠ X := by
  intro heq
  have haN : a ∈ Subgroup.normalizer (X : Set Γ) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 heq
  have hPz : P = Subgroup.zpowers a := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ha)
    rw [Nat.card_zpowers, hP]
    have h1 : orderOf a ∣ 7 := hP ▸ Subgroup.orderOf_dvd_natCard P ha
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha1
    · rw [h]
  have hPN : P ≤ Subgroup.normalizer (X : Set Γ) := by
    rw [hPz]
    exact Subgroup.zpowers_le.2 haN
  apply not_le_normalizer_of_frob21 hF hna hXF hX
  rw [← sup_eq_of_card_three_seven hF hXF hPF hX hP]
  exact sup_le Subgroup.le_normalizer hPN

theorem eq_of_card_seven {F P P' : Subgroup Γ} (hF : Nat.card F = 21) (hPF : P ≤ F)
    (hP'F : P' ≤ F) (hP : Nat.card P = 7) (hP' : Nat.card P' = 7) : P = P' := by
  by_contra hne
  have hinf : P' ⊓ P = ⊥ := by
    have hdvd : Nat.card ↥(P' ⊓ P) ∣ 7 := hP ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      apply hne
      have e1 : P' ⊓ P = P := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hP])
      have e2 : P' ⊓ P = P' := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hP'])
      rw [← e1, e2]
  have h1 : P'.relIndex P = 7 := by
    have := Subgroup.relIndex_mul_card P' P
    rw [hinf, Subgroup.card_bot, mul_one, hP] at this
    exact this
  have h2 : P'.relIndex F = 3 := by
    have := Subgroup.relIndex_mul_card P' F
    rw [inf_eq_left.2 hP'F, hP', hF] at this
    omega
  have h3 : P'.relIndex P ≤ P'.relIndex F :=
    Subgroup.relIndex_le_of_le_right hPF (by rw [h2]; norm_num)
  omega

theorem closure_conj_eq_of_frob21 {F X : Subgroup Γ} (hF : Nat.card F = 21)
    (hna : ∃ a ∈ F, ∃ b ∈ F, a * b ≠ b * a) (hXF : X ≤ F) (hX : Nat.card X = 3) :
    Subgroup.closure {ψ | ∃ φ ∈ F, ∃ ξ ∈ X, ψ = φ * ξ * φ⁻¹} = F := by
  set N := Subgroup.closure {ψ | ∃ φ ∈ F, ∃ ξ ∈ X, ψ = φ * ξ * φ⁻¹} with hNdef
  have hNF : N ≤ F := (Subgroup.closure_le _).2 fun ψ ⟨φ, hφ, ξ, hξ, hψ⟩ =>
    hψ ▸ F.mul_mem (F.mul_mem hφ (hXF hξ)) (F.inv_mem hφ)
  have hXN : X ≤ N := fun ξ hξ => Subgroup.subset_closure ⟨1, F.one_mem, ξ, hξ, by group⟩
  have hmap : ∀ φ ∈ F, N.map (MulAut.conj φ).toMonoidHom ≤ N := by
    intro φ hφ
    rw [hNdef, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨ψ, ⟨φ', hφ', ξ, hξ, rfl⟩, rfl⟩
    exact ⟨φ * φ', F.mul_mem hφ hφ', ξ, hξ, by simp [MulAut.conj_apply]; group⟩
  have hFN : F ≤ Subgroup.normalizer (N : Set Γ) := by
    intro φ hφ
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge (hmap φ hφ)
      (Subgroup.card_map_of_injective (MulAut.conj φ).injective).ge
  apply Subgroup.eq_of_le_of_card_ge hNF
  have h3 : 3 ∣ Nat.card N := hX ▸ Subgroup.card_dvd_of_le hXN
  have hle : Nat.card N ∣ 21 := hF ▸ Subgroup.card_dvd_of_le hNF
  obtain ⟨k, hk⟩ := h3
  have hk7 : k ∣ 7 := by
    rw [hk, show (21 : ℕ) = 3 * 7 by norm_num] at hle
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hle
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hk7 with h1 | h7
  · exfalso
    rw [h1, mul_one] at hk
    have hNX : N = X := (Subgroup.eq_of_le_of_card_ge hXN (by rw [hk, hX])).symm
    rw [hNX] at hFN
    exact not_le_normalizer_of_frob21 hF hna hXF hX hFN
  · rw [hF, hk, h7]

end Frob

section FrobModule

variable [Finite W]

omit [Finite W] in
theorem card_diff_one (S : Subgroup W) : Nat.card ↥((S : Set W) \ {1}) = Nat.card S - 1 := by
  rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem S.one_mem, ← Nat.card_coe_set_eq]
  rfl

omit [Finite W] in
theorem pow_mul_apply_eq {a : MulAut W} {v : W} {k : ℕ} (h : (a ^ k) v = v) (m : ℕ) :
    (a ^ (k * m)) v = v := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, pow_add, MulAut.mul_apply, h, ih]

omit [Finite W] in
theorem apply_eq_of_pow_seven {a : MulAut W} (ha : a ^ 7 = 1) {v : W} {k : ℕ} (hk1 : 1 ≤ k)
    (hk3 : k ≤ 3) (h : (a ^ k) v = v) : a v = v := by
  have key : ∀ m t : ℕ, k * m = 7 * t + 1 → a v = v := by
    intro m t hkm
    have h1 := pow_mul_apply_eq h m
    rw [hkm, pow_add, pow_mul, ha, one_pow, one_mul, pow_one] at h1
    exact h1
  interval_cases k
  · exact key 1 0 rfl
  · exact key 4 1 rfl
  · exact key 5 2 rfl

theorem card_commSub_frob21 (hW : ∀ w : W, w ^ 2 = 1) {F X : Subgroup (MulAut W)}
    (hF : Nat.card F = 21) (hna : ∃ a ∈ F, ∃ b ∈ F, a * b ≠ b * a) (hXF : X ≤ F)
    (hX : Nat.card X = 3) (hXW : Nat.card (commSub ⊤ X) = 4) : Nat.card (commSub ⊤ F) = 8 := by
  classical
  have hFodd : Odd (Nat.card F) := by rw [hF]; decide
  have hXodd : Odd (Nat.card X) := by rw [hX]; decide
  set VF := commSub (⊤ : Subgroup W) F with hVFdef
  have hVFinv : ∀ y ∈ F, ∀ m ∈ VF, y m ∈ VF := fun y hy m hm => commSub_stable' hy hm
  obtain ⟨hdec1, hdec2⟩ := B1.coprime_decomp hW hXodd (M := VF)
    (fun y hy m hm => hVFinv y (hXF hy) m hm)
  have htop : fixV F ⊔ VF = ⊤ := fixV_sup_commSub_eq_top' hW hFodd
  have hceq : commSub VF X = commSub ⊤ X := by
    refine le_antisymm (commSub_mono le_top le_rfl) ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨ξ, hξ, w, -, rfl⟩
    have hw : w ∈ fixV F ⊔ VF := by rw [htop]; exact Subgroup.mem_top w
    obtain ⟨c, hc, v, hv, rfl⟩ := Subgroup.mem_sup.1 hw
    have hξc : ξ c = c := hc ξ (hXF hξ)
    have h1 : ξ (c * v) * (c * v)⁻¹ = ξ v * v⁻¹ := by
      rw [map_mul, hξc, mul_inv_rev, mul_comm c (ξ v), mul_assoc, ← mul_assoc c,
        mul_comm c v⁻¹, mul_assoc, mul_inv_cancel, mul_one]
    rw [h1]
    exact Subgroup.subset_closure ⟨ξ, hξ, v, hv, rfl⟩
  set C := VF ⊓ fixV X with hCdef
  have hcardVF : Nat.card VF = Nat.card C * 4 := by
    have h := card_sup_mul_card_inf C (commSub VF X)
    rw [hdec1, hdec2, Subgroup.card_bot, mul_one, hceq, hXW] at h
    exact h
  obtain ⟨P, hPF, hP⟩ := exists_card_seven hF
  have hmaps : ∀ (a : P) (v : ↥((C : Set W) \ {1})),
      (a : MulAut W) (v : W) ∈ (VF : Set W) \ {1} := by
    rintro ⟨a, ha⟩ ⟨v, hvC, hv1⟩
    refine ⟨hVFinv a (hPF ha) v hvC.1, fun h => hv1 ?_⟩
    have h' : a v = a 1 := by rw [map_one]; exact h
    exact a.injective h'
  let Φ : ↥P × ↥((C : Set W) \ {1}) → ↥((VF : Set W) \ {1}) := fun p =>
    ⟨(p.1 : MulAut W) (p.2 : W), hmaps p.1 p.2⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨⟨a, ha⟩, ⟨v, hvC, hv1⟩⟩ ⟨⟨b, hb⟩, ⟨w, hwC, hw1⟩⟩ heq
    have heq' : a v = b w := congrArg Subtype.val heq
    have hc : (b⁻¹ * a) v = w := by
      rw [MulAut.mul_apply, heq', MulAut.inv_apply_self]
    by_cases hc1 : b⁻¹ * a = 1
    · have hab : a = b := by
        have := congrArg (fun x => b * x) hc1
        simpa using this
      subst hab
      have hvw : v = w := by
        rw [hc1, MulAut.one_apply] at hc
        exact hc
      subst hvw
      rfl
    · exfalso
      have hcP : b⁻¹ * a ∈ P := P.mul_mem (P.inv_mem hb) ha
      have hne := map_conj_ne_of_frob21 hF hna hXF hX hPF hP hcP hc1
      have hXcF : X.map (MulAut.conj (b⁻¹ * a)).toMonoidHom ≤ F := by
        rintro _ ⟨x, hx, rfl⟩
        exact F.mul_mem (F.mul_mem (hPF hcP) (hXF hx)) (F.inv_mem (hPF hcP))
      have hXc3 : Nat.card (X.map (MulAut.conj (b⁻¹ * a)).toMonoidHom) = 3 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj (b⁻¹ * a)).injective, hX]
      have hsup := sup_eq_of_frob21 hF hXF hXcF hX hXc3 hne.symm
      have hwX : w ∈ fixV X := hwC.2
      have hwXc : w ∈ fixV (X.map (MulAut.conj (b⁻¹ * a)).toMonoidHom) := by
        rw [fixV_map_conj]
        exact ⟨v, hvC.2, hc⟩
      have hwF : w ∈ fixV F := by
        have hle : X ⊔ X.map (MulAut.conj (b⁻¹ * a)).toMonoidHom ≤
            MulAction.stabilizer (MulAut W) w := by
          refine sup_le (fun x hx => ?_) (fun x hx => ?_)
          · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
            exact hwX x hx
          · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
            exact hwXc x hx
        intro f hf
        rw [← hsup] at hf
        have := hle hf
        rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
      have hw0 : w ∈ fixV F ⊓ VF := ⟨hwF, hwC.1⟩
      rw [fixV_inf_commSub_eq_bot' hW hFodd] at hw0
      exact hw1 hw0
  have hcard := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_prod, card_diff_one, card_diff_one, hP, hcardVF] at hcard
  have hC1 : 1 ≤ Nat.card C := Nat.card_pos
  have hC2 : Nat.card C ≤ 2 := by omega
  obtain ⟨k, hk⟩ : ∃ k, Nat.card C = 2 ^ k := ⟨rk C, card_eq_two_pow hW C⟩
  have hk1 : k ≤ 1 := by
    by_contra hk2
    push Not at hk2
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  interval_cases k
  ·
    exfalso
    rw [pow_zero] at hk
    have hVF4 : Nat.card VF = 4 := by rw [hcardVF, hk, one_mul]
    obtain ⟨a, ha, ha1⟩ : ∃ a ∈ P, a ≠ 1 := by
      by_contra hall
      push Not at hall
      have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 hall
      rw [this, Subgroup.card_bot] at hP
      omega
    have ha7 : a ^ 7 = 1 := by
      have := Subgroup.orderOf_dvd_natCard P ha
      rw [hP] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    have hfixVF : ∀ v ∈ VF, a v = v := by
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1, map_one]
      have hmem : ∀ i : ℕ, (a ^ i) v ∈ (VF : Set W) \ {1} := by
        intro i
        refine ⟨?_, fun h => hv1 ?_⟩
        · induction i with
          | zero => simpa using hv
          | succ i ih =>
            rw [pow_succ', MulAut.mul_apply]
            exact hVFinv a (hPF ha) _ ih
        · have h' : (a ^ i) v = (a ^ i) 1 := by rw [map_one]; exact h
          exact (a ^ i).injective h'
      let g : Fin 4 → ↥((VF : Set W) \ {1}) := fun i => ⟨(a ^ (i : ℕ)) v, hmem i⟩
      have : Fintype ↥((VF : Set W) \ {1}) := Fintype.ofFinite _
      have hlt : Fintype.card ↥((VF : Set W) \ {1}) < Fintype.card (Fin 4) := by
        rw [← Nat.card_eq_fintype_card, card_diff_one, hVF4, Fintype.card_fin]
        norm_num
      obtain ⟨i, j, hij, hgij⟩ := Fintype.exists_ne_map_eq_of_card_lt g hlt
      have hgij' : (a ^ (i : ℕ)) v = (a ^ (j : ℕ)) v := congrArg Subtype.val hgij
      have key : ∀ i j : ℕ, i < j → j < 4 → (a ^ i) v = (a ^ j) v → a v = v := by
        intro i j hij hj h
        have h1 : (a ^ j) v = (a ^ i) ((a ^ (j - i)) v) := by
          rw [← MulAut.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le]
        rw [h1] at h
        have h2 : (a ^ (j - i)) v = v := (a ^ i).injective h.symm
        exact apply_eq_of_pow_seven ha7 (by omega) (by omega) h2
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact key i j h j.2 hgij'
      · exact key j i h i.2 hgij'.symm
    apply ha1
    ext w
    have hw : w ∈ fixV F ⊔ VF := by rw [htop]; exact Subgroup.mem_top w
    obtain ⟨c, hc, v, hv, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [MulAut.one_apply, map_mul, hc a (hPF ha), hfixVF v hv]
  · rw [pow_one] at hk
    rw [hcardVF, hk]

end FrobModule

section Structure

variable {ι : Type*} {Ω : Set (Subgroup (MulAut W))} {L : ι → Subgroup (MulAut W)}

theorem le_sSup_inter (hsup : (⨆ i, L i) = sSup Ω) (hind : iSupIndep L)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ L i, ∀ b ∈ L j, a * b = b * a)
    (hdich : ∀ X ∈ Ω, ∃ j, X ≤ L j) (i : ι) : L i ≤ sSup {Y | Y ∈ Ω ∧ Y ≤ L i} := by
  set A := sSup {Y | Y ∈ Ω ∧ Y ≤ L i} with hAdef
  set B := ⨆ (j) (_ : j ≠ i), L j with hBdef
  have hAL : A ≤ L i := sSup_le fun Y hY => hY.2
  have hΩ : sSup Ω ≤ A ⊔ B := sSup_le fun Y hY => by
    obtain ⟨j, hj⟩ := hdich Y hY
    by_cases hji : j = i
    · subst hji
      exact le_sup_of_le_left (le_sSup ⟨hY, hj⟩)
    · exact le_sup_of_le_right (hj.trans (le_iSup₂_of_le j hji le_rfl))
  have hBC : B ≤ Subgroup.centralizer (L i : Set (MulAut W)) :=
    iSup₂_le fun j hj b hb => Subgroup.mem_centralizer_iff.2 fun a ha => hcomm i j (Ne.symm hj)
      a ha b hb
  have hBN : B ≤ Subgroup.normalizer (A : Set (MulAut W)) :=
    (hBC.trans (Subgroup.centralizer_le hAL)).trans (Subgroup.centralizer_le_normalizer _)
  intro x hx
  have hx' : x ∈ A ⊔ B := hΩ (hsup ▸ (le_iSup L i hx : x ∈ ⨆ i, L i))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A B hBN] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  have hbL : b ∈ L i := by
    have h1 := (L i).mul_mem ((L i).inv_mem (hAL ha)) hx
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1
  have hb1 : b = 1 := Subgroup.disjoint_def.1 (hind i) hbL hb
  show a * b ∈ A
  rw [hb1, mul_one]
  exact ha

theorem exists_mem_le_of_ne_bot (hsup : (⨆ i, L i) = sSup Ω) (hind : iSupIndep L)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ L i, ∀ b ∈ L j, a * b = b * a)
    (hdich : ∀ X ∈ Ω, ∃ j, X ≤ L j) {i : ι} (hi : L i ≠ ⊥) : ∃ Y ∈ Ω, Y ≤ L i := by
  by_contra hno
  push Not at hno
  apply hi
  have h := le_sSup_inter hsup hind hcomm hdich i
  have hempty : {Y | Y ∈ Ω ∧ Y ≤ L i} = ∅ := by
    ext Y
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact hno Y
  rw [hempty, sSup_empty] at h
  exact le_bot_iff.1 h

omit [CommGroup W] in
theorem eq_of_le_of_le {M : Type*} [Group M] {L : ι → Subgroup M} (hind : iSupIndep L)
    {Y : Subgroup M} (hY : Y ≠ ⊥) {i j : ι} (hi : Y ≤ L i) (hj : Y ≤ L j) : i = j := by
  by_contra hij
  apply hY
  have := (hind.pairwiseDisjoint hij).le_bot
  exact le_bot_iff.1 ((le_inf hi hj).trans this)

end Structure

end Asc81c

end CFSG.Quasithin
