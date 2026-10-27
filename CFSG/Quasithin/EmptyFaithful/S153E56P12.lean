module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

namespace S153E56p

open scoped commutatorElement Pointwise

section CardSup

variable {D : Type*} [Group D]

theorem card_sup_mul_card_inf_of_normalizing [Finite D] (A B : Subgroup D)
    (hAB : A ≤ Subgroup.normalizer (B : Set D)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  set N : Subgroup D := A ⊔ B with hN
  have hAN : A ≤ N := le_sup_left
  have hBN : B ≤ N := le_sup_right
  have hnorm : (B.subgroupOf N).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hBN).2 fun b n hb hn => ?_
    have h1 : N ≤ Subgroup.normalizer (B : Set D) := sup_le hAB Subgroup.le_normalizer
    exact (Subgroup.mem_normalizer_iff.1 (h1 hn) b).1 hb
  have htop : A.subgroupOf N ⊔ B.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAN hBN, ← hN, Subgroup.subgroupOf_self]
  have h1 := Subgroup.relIndex_sup_right (H := A.subgroupOf N) (K := B.subgroupOf N)
  rw [htop, Subgroup.relIndex_top_right] at h1
  have h2 := Subgroup.card_mul_index (B.subgroupOf N)
  have h3 := Subgroup.relIndex_mul_card (B.subgroupOf N) (A.subgroupOf N)
  rw [← h1] at h3
  have e1 : Nat.card ↥(B.subgroupOf N) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  have e2 : Nat.card ↥(A.subgroupOf N) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have e3 : Nat.card ↥(B.subgroupOf N ⊓ A.subgroupOf N) = Nat.card ↥(A ⊓ B) := by
    have : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
      ext x
      simp [Subgroup.mem_subgroupOf, and_comm]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans inf_le_left hAN)).toEquiv
  rw [e1] at h2
  rw [e3, e2] at h3
  calc Nat.card ↥N * Nat.card ↥(A ⊓ B)
      = (Nat.card B * (B.subgroupOf N).index) * Nat.card ↥(A ⊓ B) := by rw [h2]
    _ = Nat.card B * ((B.subgroupOf N).index * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card B * Nat.card A := by rw [h3]
    _ = Nat.card A * Nat.card B := by ring

end CardSup

section Extra

theorem isExtraspecial_two_of {Gd : Type*} [Group Gd] [Finite Gd]
    (hZ : Nat.card (Subgroup.center Gd) = 2)
    (hcomm : ∀ x y : Gd, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center Gd)
    (hsq : ∀ x : Gd, x * x ∈ Subgroup.center Gd) (hnt : 2 < Nat.card Gd) :
    CFSG.IsExtraspecial 2 Gd := by
  have hcom : ∀ a b : Gd ⧸ Subgroup.center Gd, a * b = b * a := by
    intro a b
    refine QuotientGroup.induction_on a fun x => QuotientGroup.induction_on b fun y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have := hcomm y⁻¹ x⁻¹
    have e : (x * y)⁻¹ * (y * x) = y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact this
  have hexp : Monoid.exponent (Gd ⧸ Subgroup.center Gd) ∣ 2 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
    refine QuotientGroup.induction_on a fun x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two]
    exact hsq x
  have : IsMulCommutative (Gd ⧸ Subgroup.center Gd) := ⟨⟨hcom⟩⟩
  have : CFSG.IsElementaryAbelian 2 (Gd ⧸ Subgroup.center Gd) := { exponent_dvd_p := hexp }
  refine ⟨hZ, inferInstance, ?_⟩
  have h1 := Subgroup.card_mul_index (Subgroup.center Gd)
  rw [hZ] at h1
  have h2 : 1 < Nat.card (Gd ⧸ Subgroup.center Gd) := by
    change 1 < (Subgroup.center Gd).index
    omega
  exact Finite.one_lt_card_iff_nontrivial.1 h2

variable {D : Type*} [Group D]

theorem comm_mem_sup (P Q V : Subgroup D) (hVc : ∀ v ∈ V, ∀ d ∈ P ⊔ Q, d * v = v * d) {x : D}
    (hP : ∀ b ∈ P, ⁅x, b⁆ ∈ V) (hQ : ∀ b ∈ Q, ⁅x, b⁆ ∈ V) : ∀ b ∈ P ⊔ Q, ⁅x, b⁆ ∈ V := by
  let K : Subgroup D :=
    { carrier := {b | b ∈ P ⊔ Q ∧ ⁅x, b⁆ ∈ V}
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro b b' ⟨hb, hxb⟩ ⟨hb', hxb'⟩
        refine ⟨Subgroup.mul_mem _ hb hb', ?_⟩
        have e : ⁅x, b * b'⁆ = ⁅x, b⁆ * (b * ⁅x, b'⁆ * b⁻¹) := by
          simp only [commutatorElement_def]
          group
        have h1 : b * ⁅x, b'⁆ * b⁻¹ = ⁅x, b'⁆ := by rw [hVc _ hxb' b hb]; group
        rw [e, h1]
        exact V.mul_mem hxb hxb'
      inv_mem' := by
        rintro b ⟨hb, hxb⟩
        refine ⟨Subgroup.inv_mem _ hb, ?_⟩
        have e : ⁅x, b⁻¹⁆ = b⁻¹ * ⁅x, b⁆⁻¹ * b := by
          simp only [commutatorElement_def]
          group
        have h1 : b⁻¹ * ⁅x, b⁆⁻¹ * b = ⁅x, b⁆⁻¹ := by
          have := hVc _ (V.inv_mem hxb) b hb
          rw [mul_assoc, ← this]
          group
        rw [e, h1]
        exact V.inv_mem hxb }
  have : P ⊔ Q ≤ K := sup_le (fun b hb => ⟨Subgroup.mem_sup_left hb, hP b hb⟩)
    (fun b hb => ⟨Subgroup.mem_sup_right hb, hQ b hb⟩)
  exact fun b hb => (this hb).2

theorem comm_mem_sup' (P Q V : Subgroup D) (hVc : ∀ v ∈ V, ∀ d ∈ P ⊔ Q, d * v = v * d) {b : D}
    (hP : ∀ a ∈ P, ⁅a, b⁆ ∈ V) (hQ : ∀ a ∈ Q, ⁅a, b⁆ ∈ V) : ∀ a ∈ P ⊔ Q, ⁅a, b⁆ ∈ V := by
  intro a ha
  have := comm_mem_sup P Q V hVc (x := b) (fun a ha => by
      rw [← commutatorElement_inv]; exact V.inv_mem (hP a ha))
    (fun a ha => by rw [← commutatorElement_inv]; exact V.inv_mem (hQ a ha)) a ha
  rw [← commutatorElement_inv]
  exact V.inv_mem this

theorem isD8Power_of_pair [Finite D] (s : ℕ) (P Q V : Subgroup D)
    (hV : Nat.card V = 2) (hVP : V ≤ P) (hVQ : V ≤ Q) (hPQ : P ⊓ Q ≤ V)
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hPs : ∀ a ∈ P, a * a = 1)
    (hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hQs : ∀ a ∈ Q, a * a = 1)
    (hcomm : ∀ g ∈ P, ∀ h ∈ Q, ⁅h, g⁆ ∈ V)
    (hradQ : ∀ h ∈ Q, (∀ g ∈ P, h * g = g * h) → h ∈ V)
    (hradP : ∀ g ∈ P, (∀ h ∈ Q, h * g = g * h) → g ∈ V)
    (hcP : Nat.card P = 2 ^ (s + 1)) (hcQ : Nat.card Q = 2 ^ (s + 1)) :
    IsD8Power153 s (P ⊔ Q) := by
  classical
  have hPQV : P ⊓ Q = V := le_antisymm hPQ (le_inf hVP hVQ)
  have hVc : ∀ v ∈ V, ∀ d ∈ P ⊔ Q, d * v = v * d := by
    intro v hv d hd
    have h1 : P ⊔ Q ≤ Subgroup.centralizer ({v} : Set D) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff.1 hx]
        exact (hPc a ha v (hVP hv)).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff.1 hx]
        exact (hQc a ha v (hVQ hv)).symm
    exact (Subgroup.mem_centralizer_iff.1 (h1 hd) v (Set.mem_singleton v)).symm
  have hQV : ∀ g ∈ P, ∀ h ∈ Q, ⁅g, h⁆ ∈ V := fun g hg h hh => by
    rw [← commutatorElement_inv h g]
    exact V.inv_mem (hcomm g hg h hh)
  have hNP : Q ≤ Subgroup.normalizer (P : Set D) := le_normalizer_of_conj_mem fun h hh g hg => by
    have e : h * g * h⁻¹ = ⁅h, g⁆ * g := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact P.mul_mem (hVP (hcomm g hg h hh)) hg
  have hNQ : P ≤ Subgroup.normalizer (Q : Set D) := le_normalizer_of_conj_mem fun g hg h hh => by
    have e : g * h * g⁻¹ = ⁅g, h⁆ * h := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem (hVQ (hQV g hg h hh)) hh
  have hcard : Nat.card ↥(P ⊔ Q) = 2 ^ (1 + 2 * s) := by
    have h := card_sup_mul_card_inf_of_normalizing P Q hNQ
    rw [hPQV, hV, hcP, hcQ] at h
    have h2 : 2 ^ (s + 1) * 2 ^ (s + 1) = 2 ^ (1 + 2 * s) * 2 := by ring
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · left
    exact ⟨rfl, by simpa using hcard⟩
  right
  refine ⟨hs, ?_, hcard, P, le_sup_left, B6.isElemAbelian_iff.2 ⟨hPc, fun a ha => by
    rw [pow_two]; exact hPs a ha⟩, hcP⟩
  have hmem : ∀ d ∈ P ⊔ Q, ∃ g ∈ P, ∃ h ∈ Q, d = g * h := by
    intro d hd
    have := Subgroup.coe_mul_of_right_le_normalizer_left P Q hNP
    have hd' : d ∈ (P : Set D) * (Q : Set D) := by rw [← this]; exact hd
    obtain ⟨g, hg, h, hh, rfl⟩ := hd'
    exact ⟨g, hg, h, hh, rfl⟩
  have hD₀comm : ∀ a ∈ P ⊔ Q, ∀ b ∈ P ⊔ Q, ⁅a, b⁆ ∈ V := by
    intro a ha b hb
    have hA : ∀ x ∈ P ⊔ Q, ∀ b ∈ P ⊔ Q, (∀ c ∈ P, ⁅x, c⁆ ∈ V) → (∀ c ∈ Q, ⁅x, c⁆ ∈ V) → ⁅x, b⁆ ∈ V :=
      fun x _ b hb hP hQ => comm_mem_sup P Q V hVc hP hQ b hb
    refine comm_mem_sup' P Q V hVc (b := b) (fun g hg => ?_) (fun h hh => ?_) a ha
    · refine comm_mem_sup P Q V hVc (fun c hc => ?_) (fun c hc => ?_) b hb
      · rw [commutatorElement_eq_one_iff_mul_comm.2 (hPc g hg c hc)]
        exact V.one_mem
      · exact hQV g hg c hc
    · refine comm_mem_sup P Q V hVc (fun c hc => ?_) (fun c hc => ?_) b hb
      · exact hcomm c hc h hh
      · rw [commutatorElement_eq_one_iff_mul_comm.2 (hQc h hh c hc)]
        exact V.one_mem
  have hcenter : ∀ d : ↥(P ⊔ Q), d ∈ Subgroup.center ↥(P ⊔ Q) ↔ (d : D) ∈ V := by
    intro d
    constructor
    · intro hd
      obtain ⟨g, hg, h, hh, hdg⟩ := hmem d d.2
      have hd' := Subgroup.mem_center_iff.1 hd
      have hhV : h ∈ V := hradQ h hh fun g' hg' => by
        have h0 := congrArg Subtype.val (hd' ⟨g', Subgroup.mem_sup_left hg'⟩)
        have h1 : g' * (g * h) = g * h * g' := by
          have : (g' : D) * (d : D) = (d : D) * g' := h0
          rwa [hdg] at this
        have h2 : g * (g' * h) = g * (h * g') := by
          calc g * (g' * h) = (g * g') * h := (mul_assoc _ _ _).symm
            _ = (g' * g) * h := by rw [hPc g' hg' g hg]
            _ = g' * (g * h) := mul_assoc _ _ _
            _ = g * h * g' := h1
            _ = g * (h * g') := mul_assoc _ _ _
        exact (mul_left_cancel h2).symm
      have hgV : g ∈ V := hradP g hg fun h' hh' => by
        have h0 := congrArg Subtype.val (hd' ⟨h', Subgroup.mem_sup_right hh'⟩)
        have h1 : h' * (g * h) = g * h * h' := by
          have : (h' : D) * (d : D) = (d : D) * h' := h0
          rwa [hdg] at this
        have h2 : (h' * g) * h = (g * h') * h := by
          calc (h' * g) * h = h' * (g * h) := mul_assoc _ _ _
            _ = (g * h) * h' := h1
            _ = g * (h * h') := mul_assoc _ _ _
            _ = g * (h' * h) := by rw [hQc h hh h' hh']
            _ = (g * h') * h := (mul_assoc _ _ _).symm
        exact mul_right_cancel h2
      rw [hdg]
      exact V.mul_mem hgV hhV
    · intro hd
      exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (hVc d hd g g.2)
  apply isExtraspecial_two_of
  · have : Subgroup.center ↥(P ⊔ Q) = V.subgroupOf (P ⊔ Q) := by
      ext d
      rw [hcenter, Subgroup.mem_subgroupOf]
    rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hVP.trans le_sup_left)).toEquiv, hV]
  · intro x y
    rw [hcenter]
    exact hD₀comm x x.2 y y.2
  · intro x
    rw [hcenter]
    obtain ⟨g, hg, h, hh, hx⟩ := hmem x x.2
    have hc : ⁅h, g⁆ ∈ V := hcomm g hg h hh
    have hgc : g * ⁅h, g⁆ = ⁅h, g⁆ * g := hVc _ hc g (Subgroup.mem_sup_left hg)
    have e1 : (g * h) * (g * h) = (g * ⁅h, g⁆) * g * (h * h) := by
      simp only [commutatorElement_def]
      group
    have e2 : ((x * x : ↥(P ⊔ Q)) : D) = (g * h) * (g * h) := by
      rw [Subgroup.coe_mul, hx]
    rw [e2, e1, hgc]
    have e3 : ⁅h, g⁆ * g * g * (h * h) = ⁅h, g⁆ * (g * g) * (h * h) := by group
    rw [e3, hPs g hg, hQs h hh]
    simpa using hc
  · rw [hcard]
    have : 2 ^ 3 ≤ 2 ^ (1 + 2 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end Extra

end S153E56p

end CFSG.Quasithin
