module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB5
public import CFSG.RankThree.GF2n.Smith81.Lin212C7

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} {x : G}

theorem exists_centralized_not_mem {V Z : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (ht2 : t * t = 1) (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V)
    (hcard : Nat.card Z ^ 2 < Nat.card V) : ∃ b ∈ V, b ∉ Z ∧ t * b * t⁻¹ = b := by
  by_contra hcon
  push Not at hcon
  have hle : V ⊓ Subgroup.centralizer ({t} : Set G) ≤ Z := by
    intro c hc
    by_contra hcZ
    exact hcon c hc.1 hcZ (mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_iff.mp hc.2 t (Set.mem_singleton t)))
  have h1 := card_le_sq_centralizer hV ht2 htV
  have h2 : Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card Z :=
    Subgroup.card_le_of_le hle
  have h3 := Nat.pow_le_pow_left h2 2
  omega

theorem lin_x_mem_Lgen_of_sit (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x) :
    x ∈ Lgen M (LB M Q B) := by
  have H := hc.hyp
  have h12 := smith_1_12 hs
  have hF : LinSwapStatement := linSwapStatement_holds
  have hN : LinNonswapStatement := linNonswapStatement_holds
  have hxH : x ∈ H0 M Z := h12.1 hs.mem
  have hX4 : 4 ≤ Nat.card X := by
    rw [IsZConjugate.card_eq (Z := Z) hs.conj]; exact H.q4
  obtain ⟨x₀, hx₀X, hx₀1, hx₀V₁, -⟩ := exists_nonswap hX4 hs.X_sq
    (fun t ht => hF G M Q Z B n V₁ V₂ hc hS hn t (h12.1 ht))
  have hx₀2 : x₀ * x₀ = 1 := hs.X_sq x₀ hx₀X
  have S := OddSetup.of_linSetup hc hS (p31_of hb hc hS hn)
  obtain ⟨-, hV₁Q, -, -, hint, -, -, -, hc₁, -⟩ := hS.basic
  have hx₀n : ∀ v ∈ V₁, x₀ * v * x₀⁻¹ ∈ V₁ := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hx₀V₁) v).mp hv
  have hV₁ : IsElemAbelian 2 V₁ :=
    ⟨⟨⟨fun a b => Subtype.ext (S.abV a a.2 b b.2)⟩⟩, fun v hv => by
      rw [pow_two]; exact S.sqV v hv⟩
  obtain ⟨b, hbV, hbZ, hbc⟩ := exists_centralized_not_mem hV₁ hx₀2 hx₀n
    (Z := Z) (by rw [hc₁]; exact Nat.pow_lt_pow_right (by have := H.q4; omega) (by omega))
  have hb1 : b ≠ 1 := fun h => hbZ (h ▸ Z.one_mem)
  have hbQ : b ∈ Q := hV₁Q hbV
  obtain ⟨g₁, z₁, hz₁, -, hbz⟩ := (S.p31 b hbQ hb1).mpr (Or.inl hbV)
  obtain ⟨g', hg'Q, hbg'⟩ := stroth_2_6 H hbQ hbZ ⟨g₁, z₁, hz₁, hbz⟩
  have hB'c : IsZConjugate Z (conjSubgroup g' Z) := ⟨g', rfl⟩
  have hB'Z : conjSubgroup g' Z ≠ Z := fun h => hbZ (h ▸ hbg')
  have hcB' : Ctx M Q Z (conjSubgroup g' Z) := ⟨H, hB'c, hg'Q, hB'Z⟩
  have hx₀N : x₀ ∈ Subgroup.normalizer (conjSubgroup g' Z : Set G) :=
    hB'c.mem_normalizer_of_commute H hb1 hbg' (mul_inv_eq_iff_eq_mul.mp hbc)
  by_cases hx₀QB : x₀ ∈ QB (conjSubgroup g' Z)
  · have hXle : X ≤ QB (conjSubgroup g' Z) :=
      IsZConjugate.le_QB_of_mem H hB'c hs.conj hx₀1 hx₀X hx₀QB
    have hxL : x ∈ LB M Q (conjSubgroup g' Z) :=
      Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hXle hs.mem, hs.memM⟩)
    rw [← hS.Lgen_eq hc hn hcB']
    exact le_Lgen_self M (LB M Q (conjSubgroup g' Z)) hxL
  · have hS' := sit_conj_back H hs.conj hx₀X hx₀1 hx₀N hx₀QB
    have h12' := smith_1_12 hS'
    have hxc : g'⁻¹ * x * g' ∈ H0 M Z := by
      apply h12'.1
      rw [mem_conjSubgroup]
      have e : (g'⁻¹)⁻¹ * (g'⁻¹ * x * g') * g'⁻¹ = x := by group
      rw [e]; exact hs.mem
    have hxb : x * b = b * x := by
      have hz : g'⁻¹ * b * g' ∈ Z := mem_conjSubgroup.mp hbg'
      have hcomm := Subgroup.mem_centralizer_iff.mp hxc.2 _ hz
      calc x * b = g' * ((g'⁻¹ * x * g') * (g'⁻¹ * b * g')) * g'⁻¹ := by group
        _ = g' * ((g'⁻¹ * b * g') * (g'⁻¹ * x * g')) * g'⁻¹ := by rw [hcomm]
        _ = b * x := by group
    have hxn₁ : conjSubgroup x V₁ = V₁ := by
      rcases hF G M Q Z B n V₁ V₂ hc hS hn x hxH with h | h
      · exact h.1
      · exfalso
        apply hbZ
        have hbx : x⁻¹ * b * x = b := by
          calc x⁻¹ * b * x = x⁻¹ * (b * x) := by group
            _ = x⁻¹ * (x * b) := by rw [hxb]
            _ = b := by group
        have hmem : b ∈ conjSubgroup x V₁ := by
          rw [mem_conjSubgroup, hbx]; exact hbV
        rw [h.1] at hmem
        rw [← hint]
        exact ⟨hbV, hmem⟩
    exact hN G M Q Z B n V₁ V₂ hc hS hn x hxH (by rw [hs.x_sq]; exact Q.one_mem) hxn₁

theorem exists_root_of_mem_module (hc : Ctx M Q Z B) (hs : Sit M Q Z X x) {d : G}
    (hd : d ∈ Q ⊓ QB X) (hdZ : d ∉ Z) (hcl : InZClass Z d) :
    ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ⊓ QB X := by
  have H := hc.hyp
  have hd1 : d ≠ 1 := fun h => hdZ (h ▸ Z.one_mem)
  obtain ⟨g₁, z₁, hz₁, -, hdz⟩ := hcl
  obtain ⟨g', hg'Q, hdg'⟩ := stroth_2_6 H hd.1 hdZ ⟨g₁, z₁, hz₁, hdz⟩
  have hA : IsZConjugate Z (conjSubgroup g' Z) := ⟨g', rfl⟩
  exact ⟨conjSubgroup g' Z, hA, le_inf hg'Q
    (IsZConjugate.le_QB_of_mem H hs.conj hA hd1 hdg' hd.2)⟩

end CFSG.RankThree.GF2n.Smith81
