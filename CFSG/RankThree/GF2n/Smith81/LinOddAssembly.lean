module

public import CFSG.RankThree.GF2n.Smith81.LinOddEval
public import CFSG.RankThree.GF2n.Smith81.LinRank
public import CFSG.RankThree.GF2n.Smith81.LinStmt

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

theorem LinSetup.basic {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (hS : LinSetup M Q Z B n V₁ V₂) :
    Z ≤ V₁ ∧ V₁ ≤ Q ∧ Z ≤ V₂ ∧ V₂ ≤ Q ∧ V₁ ⊓ V₂ = Z ∧ V₁ ⊔ V₂ = Q ∧
      Lgen M (LB M Q B) ≤ Subgroup.normalizer (V₁ : Set G) ∧
      Lgen M (LB M Q B) ≤ Subgroup.normalizer (V₂ : Set G) ∧
      Nat.card V₁ = Nat.card Z ^ (n + 1) ∧ Nat.card V₂ = Nat.card Z ^ (n + 1) := by
  obtain ⟨K, hK, hfin, hcard, φ, hrange, hker, hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup,
    hs₁, hs₂, hswap, hcent⟩ := hS
  obtain ⟨hN₁, hn₁, ψ₁, -⟩ := hs₁
  obtain ⟨hN₂, hn₂, ψ₂, -⟩ := hs₂
  exact ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup, hN₁, hN₂,
    card_eq_pow_of_sectionIso hZV₁ hcard ψ₁, card_eq_pow_of_sectionIso hZV₂ hcard ψ₂⟩

theorem abelian_of_sq {V : Subgroup G} (h : ∀ v ∈ V, v * v = 1) :
    ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
  intro a ha b hb
  have h1 := h (a * b) (V.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h b hb)
  have h2 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, ha', hb'] at h2
  exact h2.symm

section Assembly

variable [Finite G] {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem OddSetup.of_linSetup (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (h31 : ∀ v ∈ Q, v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂)) : OddSetup M Q Z B V₁ V₂ := by
  obtain ⟨hZ₁, hV₁Q, hZ₂, hV₂Q, hint, -, hN₁, hN₂, -, -⟩ := hS.basic
  have h31' : ∀ v ∈ Q, v ≠ 1 → (InZClass Z v ↔ v ∈ V₂ ∨ v ∈ V₁) := fun v hv hv1 => by
    rw [h31 v hv hv1]; exact or_comm
  have hsq₁ := Lin31Prop.sq_eq_one hc.hyp hV₁Q h31
  have hsq₂ := Lin31Prop.sq_eq_one hc.hyp hV₂Q h31'
  exact ⟨hc.hyp, hZ₁, hV₁Q, hZ₂, hV₂Q, hint, LinSetup.exists_mul hc.hyp hS,
    LinSetup.exists_mul hc.hyp hS.symm, abelian_of_sq hsq₁, abelian_of_sq hsq₂, hsq₁, hsq₂,
    fun t ht => hN₁ ht, fun t ht => hN₂ ht, h31⟩

theorem exists_sit_Y {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) (hQX : Q ⊓ QB X = ⊥)
    {g : G} (hg : X = conjSubgroup g Z) :
    ∃ y₁, Sit M Q Z (conjSubgroup g⁻¹ Z) y₁ ∧ Q ⊓ QB (conjSubgroup g⁻¹ Z) = ⊥ := by
  have H := hs.hyp
  have h12 := smith_1_12 hs
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Z_ne_bot H)
  have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  have hXC : ∀ z ∈ Z, ∀ z' ∈ Z, z * (g * z' * g⁻¹) = g * z' * g⁻¹ * z := by
    intro z hz z' hz'
    have hmem : g * z' * g⁻¹ ∈ X := by
      rw [hg, mem_conjSubgroup]; simpa [mul_assoc] using hz'
    exact Subgroup.mem_centralizer_iff.mp (h12.1 hmem).2 z hz
  have hYC : ∀ z ∈ Z, (g⁻¹ * z₀ * g) * z = z * (g⁻¹ * z₀ * g) := by
    intro z hz
    have h := hXC z₀ hz₀ z hz
    have : g⁻¹ * (z₀ * (g * z * g⁻¹)) * g = g⁻¹ * (g * z * g⁻¹ * z₀) * g := by rw [h]
    simpa [mul_assoc] using this
  have hyM : g⁻¹ * z₀ * g ∈ M := by
    have := Tim77.mem_normalizer_of_commute_of_isTI H.ti hz₀ hz₀1' (hYC z₀ hz₀)
    rwa [H.normalizer_Z.1] at this
  have hyQ : g⁻¹ * z₀ * g ∉ Q := by
    intro h
    have : z₀ ∈ QB X := by
      rw [hg, QB_conj_eq H g, mem_conjSubgroup]; exact h
    have hmem : z₀ ∈ Z ⊓ QB X := ⟨hz₀, this⟩
    rw [Z_inf_QB_eq_bot hs h12, Subgroup.mem_bot] at hmem
    exact hz₀1' hmem
  have hs' := Sit.of_conj H (g := g⁻¹) hz₀ hz₀1' (by simpa using hyM) (by simpa using hyQ)
  refine ⟨_, hs', ?_⟩
  rw [QB_conj_eq H g⁻¹]
  have h1 : conjSubgroup g (Q ⊓ conjSubgroup g⁻¹ Q) = ⊥ := by
    rw [conjSubgroup_inf, conjSubgroup_conj_inv, inf_comm, ← QB_conj_eq H g, ← hg]
    exact hQX
  exact (conjSubgroup_eq_bot_iff g _).mp h1

theorem hasDim_of_sit (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) {m : ℕ}
    (hn : n = 2 * m + 1) (hm : 1 ≤ m) {A : Subgroup G} {t : G} (hs : Sit M Q Z A t)
    (hQA : Q ⊓ QB A = ⊥) (hL : t ∈ Lgen M (LB M Q B)) :
    HasDimOn V₁ Z m t ∧ HasDimOn V₂ Z m t := by
  have h := lin115RankStatement_holds G M Q Z B A t n V₁ V₂ hc hS (by omega) hs hL hQA
  have e : n / 2 = m := by omega
  rwa [e] at h

theorem step6 (hF : LinSwapStatement) (hN : LinNonswapStatement) (hΓ : LinGammaStatement)
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (S : OddSetup M Q Z B V₁ V₂) {m : ℕ}
    (hn : n = 2 * m + 1) (hm : 1 ≤ m) {Y : Subgroup G} {y₁ : G} (hsY : Sit M Q Z Y y₁)
    (hQY : Q ⊓ QB Y = ⊥) (T : Subgroup G) (hTL : T ≤ Lx M Y)
    (hrank : ∀ a ∈ T, a ≠ 1 → a ∈ Lgen M (LB M Q B) →
      HasDimOn V₁ Z m a ∧ HasDimOn V₂ Z m a)
    (hcard : Nat.card Z ^ (m + 1) < Nat.card T) : False := by
  have h12 := smith_1_12 hsY
  have hn3 : 3 ≤ n := by omega
  have hY4 : 4 ≤ Nat.card Y := by
    rw [IsZConjugate.card_eq (Z := Z) hsY.conj]; exact hc.hyp.q4
  obtain ⟨y₀, hy₀Y, hy₀1, hy₀V₁, -⟩ := exists_nonswap hY4 hsY.X_sq
    (fun t ht => hF G M Q Z B n V₁ V₂ hc hS hn3 t (h12.1 ht))
  have hsY0 : Sit M Q Z Y y₀ :=
    ⟨hsY.hyp, hsY.conj, hy₀Y, hy₀1, (h12.1 hy₀Y).1, fun hyQ => hy₀1 (by
      have : y₀ ∈ Y ⊓ Q := ⟨hy₀Y, hyQ⟩
      rw [h12.2, Subgroup.mem_bot] at this
      exact this)⟩
  have hy₀L : y₀ ∈ Lgen M (LB M Q B) :=
    hN G M Q Z B n V₁ V₂ hc hS hn3 y₀ (h12.1 hy₀Y) (by rw [hsY0.x_sq]; exact Q.one_mem) hy₀V₁
  obtain ⟨-, -, V, hVmem, hD, -, -⟩ :=
    hΓ G M Q Z B Y y₀ n m V₁ V₂ hc hS hn hm S.sqV S.sqV' hsY0 hy₀L hQY
  obtain ⟨-, -, -, -, -, -, -, -, hcard₁, hcard₂⟩ := hS.basic
  have hc₁ : Nat.card V₁ = Nat.card Z ^ (2 * m + 2) := by rw [hcard₁, hn]
  have hc₂ : Nat.card V₂ = Nat.card Z ^ (2 * m + 2) := by rw [hcard₂, hn]
  rcases hVmem with h | h
  · rw [h] at hD
    exact step6_aux S (e := 2 * m + 2) (d := m + 2) (r := m + 1) (by omega) (by omega)
      (by omega) (hF G M Q Z B n V₁ V₂ hc hS hn3) (hN G M Q Z B n V₁ V₂ hc hS hn3)
      hc₁ hsY0 hQY hD T hTL (fun a ha ha1 hL => (hrank a ha ha1 hL).1)
      (by rw [show m + 2 - 1 = m + 1 by omega]; exact hcard)
  · have h' : V = V₂ := h
    rw [h'] at hD
    exact step6_aux S.symm (e := 2 * m + 2) (d := m + 2) (r := m + 1) (by omega) (by omega)
      (by omega) (hF G M Q Z B n V₂ V₁ hc hS.symm hn3)
      (hN G M Q Z B n V₂ V₁ hc hS.symm hn3) hc₂ hsY0 hQY hD T hTL
      (fun a ha ha1 hL => (hrank a ha ha1 hL).2)
      (by rw [show m + 2 - 1 = m + 1 by omega]; exact hcard)

end Assembly

end CFSG.RankThree.GF2n.Smith81
