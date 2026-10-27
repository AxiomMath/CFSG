module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42DihA
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42DihB
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MSym2
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaFHolds
import CFSG.RankThree.PartTwo.Sec21.Item233TablesBasic
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MSetup
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MSym1

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem m42_V4g {L : Subgroup G} (hL : M42A5 L) {b : G} (hb : b ∈ L) (hb3 : orderOf b = 3) :
    ∃ u v : G, u ∈ L ∧ v ∈ L ∧ u * u = 1 ∧ v * v = 1 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧
      u * v = v * u ∧ b * u * b⁻¹ = v ∧ b * v * b⁻¹ = u * v ∧
      Nat.card (Subgroup.closure ({u, v} : Set G)) = 4 := by
  obtain ⟨eL⟩ := hL
  let w₀ : ↥L := ⟨b, hb⟩
  obtain ⟨u, v, hu2, hv2, hu1, hv1, huv1, hcuv, hwu, hwv⟩ := m42_a5_V4 (eL w₀)
    (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hb3])
  let a : ↥L := eL.symm u
  let c : ↥L := eL.symm v
  have hs : ∀ z : alternatingGroup (Fin 5),
      eL.symm (eL w₀ * z * (eL w₀)⁻¹) = w₀ * eL.symm z * w₀⁻¹ := by
    intro z; simp
  have e1 : w₀ * a * w₀⁻¹ = c := by rw [← hs, hwu]
  have e2 : w₀ * c * w₀⁻¹ = a * c := by
    have := hs v
    rw [hwv] at this
    simpa [a, c] using this.symm
  have ha2 : a * a = 1 := by
    have := congrArg eL.symm hu2; simpa [a] using this
  have hc2 : c * c = 1 := by
    have := congrArg eL.symm hv2; simpa [c] using this
  have hac : a * c = c * a := by
    have := congrArg eL.symm hcuv; simpa [a, c] using this
  have ha1 : a ≠ 1 := by
    intro h; apply hu1; simpa [a] using congrArg eL h
  have hc1 : c ≠ 1 := by
    intro h; apply hv1; simpa [c] using congrArg eL h
  have hac1 : a ≠ c := by
    intro h; apply huv1; simpa [a, c] using congrArg eL h
  let u' : G := a.1
  let v' : G := c.1
  have hu'2 : u' * u' = 1 := by simpa using congrArg Subtype.val ha2
  have hv'2 : v' * v' = 1 := by simpa using congrArg Subtype.val hc2
  have hu'1 : u' ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hv'1 : v' ≠ 1 := fun h => hc1 (Subtype.ext h)
  have huv' : u' ≠ v' := fun h => hac1 (Subtype.ext h)
  have hcom : u' * v' = v' * u' := by simpa using congrArg Subtype.val hac
  have hbu : b * u' * b⁻¹ = v' := by simpa using congrArg Subtype.val e1
  have hbv : b * v' * b⁻¹ = u' * v' := by simpa using congrArg Subtype.val e2
  have hou : orderOf u' = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hu'2) hu'1
  have hov : orderOf v' = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hv'2) hv'1
  have hint : Subgroup.zpowers u' ⊓ Subgroup.zpowers v' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    rcases m42_zpowers_two hu'2 z hz.1 with h | h
    · exact h
    · rcases m42_zpowers_two hv'2 z hz.2 with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') huv'
  have hu'L : u' ∈ L := a.2
  have hv'L : v' ∈ L := c.2
  exact ⟨u', v', hu'L, hv'L, hu'2, hv'2, hu'1, hv'1, huv', hcom, hbu, hbv,
    m42_card_pair2 hou hov hcom hint⟩

theorem m42_sym_false' (hN : FF79LemmaN) (hQ : FF84.LemmaQ)
    {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h : FF79Sec4 b J B b₁ b₂)
    {H K L X : Subgroup G} (hC1 : Subgroup.zpowers (b₁ * b₂) ⊔ H = Cen (b₁ * b₂))
    (S : M42Sit (b₁ * b₂) b (b₁ ^ 2 * b₂) H K L X) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup ↥K := S.Λiso.simple
  haveI : IsSimpleGroup ↥L := S.Δiso.simple
  set β := b₁ * b₂ with hβdef
  set γ := b₁ ^ 2 * b₂ with hγdef
  obtain ⟨u, v, huL, hvL, hu2, hv2, hu1, hv1, huv, hcuv, hbu, hbv, hU4⟩ :=
    m42_V4g S.Δiso S.e_Δ S.ord_e
  set U : Subgroup G := Subgroup.closure ({u, v} : Set G) with hUdef
  have hUL : U ≤ L := by
    rw [hUdef, Subgroup.closure_le]
    rintro z (rfl | rfl)
    exacts [huL, hvL]
  have hbU : ∀ x ∈ U, b * x * b⁻¹ ∈ U :=
    m42_closure_conj_mem (g := b) (S := {u, v}) (by
      rintro z (rfl | rfl)
      · rw [hbu]; exact Subgroup.subset_closure (by simp)
      · rw [hbv]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
  have huU : u ∈ U := Subgroup.subset_closure (by simp)
  have hvU : v ∈ U := Subgroup.subset_closure (by simp)
  have huvU : u * v ∈ U := U.mul_mem huU hvU
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  have hUne : U ≠ ⊥ := by
    intro h0
    rw [h0] at hU4
    simp at hU4
  have hbNor : b ∈ Nor U := m42_mem_Nor_of_le hbU
  have hKU : ∀ k ∈ K, ∀ x ∈ U, k * x = x * k := fun k hk x hx =>
    S.comm_ΛΔ hN hQ k hk x (hUL hx)
  have hKNor : ∀ k ∈ K, k ∈ Nor U := fun k hk => m42_mem_Nor_of_le (fun x hx => by
    have e : k * x * k⁻¹ = x := by rw [hKU k hk x hx]; group
    rw [e]; exact hx)
  set V := Op 2 (Nor U) with hV
  have hVp : IsPGroup 2 V := m42_Op_isPGroup 2 _
  have hUV : U ≤ V := m42_le_Op Subgroup.le_normalizer hU2
    (fun m hm x hx => (Subgroup.mem_normalizer_iff.mp hm x).mp hx)
  have hchar := m42_char2 h.char2 hU2 hUne
  have hVnorm : ∀ g ∈ Nor U, ∀ x ∈ V, g * x * g⁻¹ ∈ V := fun g hg x hx => m42_Op_conj_mem hg hx
  set W := V ⊓ Cen β with hW
  have hWp : IsPGroup 2 W := hVp.to_le inf_le_left
  have hW3 : ∀ x ∈ W, orderOf x ≠ 3 := fun x hx => m42_orderOf_pGroup_ne_three hWp hx
  have hWH : W ≤ H := by
    intro x hx
    apply S.H3 x hx.2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hWp) ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
  have hcomβ : ∀ g ∈ Cen β, ∀ x ∈ Cen β, g * x * g⁻¹ ∈ Cen β := by
    intro g hg x hx
    have hc1 : Commute β g := m42_cen_comm hg
    have hc2 : Commute β x := m42_cen_comm hx
    exact m42_mem_cen ((hc1.mul_right hc2).mul_right hc1.inv_right).eq
  have hbW : ∀ g ∈ Nor U, g ∈ Cen β → ∀ x ∈ W, g * x * g⁻¹ ∈ W := fun g hg hgβ x hx =>
    ⟨hVnorm g hg x hx.1, hcomβ g hgβ x hx.2⟩
  have hKW : ∀ k ∈ K, ∀ x ∈ W, k * x * k⁻¹ ∈ W := fun k hk x hx =>
    hbW k (hKNor k hk) (S.cenβ (S.Λ_le_H hk)) x hx
  have hKWnor : ∀ k ∈ K, k ∈ Nor W := fun k hk => m42_mem_Nor_of_le (hKW k hk)
  have hKWcomm : ∀ s ∈ K, ∀ n ∈ W, s * n = n * s :=
    m42_comm_of_normal (S := K) (N := W) (Y := Nor W ⊓ H)
      (fun k hk => ⟨hKWnor k hk, S.Λ_le_H hk⟩)
      (fun x hx => ⟨Subgroup.le_normalizer hx, hWH hx⟩)
      (fun y hy s hs => S.Λ_normal hN hQ y hy.2 s hs)
      (fun y hy n hn => (Subgroup.mem_normalizer_iff.mp hy.1 n).mp hn)
      (fun hle => hW3 γ (hle S.f_Λ) S.ord_f)
  have hbcen : b ∈ Cen β := m42_mem_cen h.comm_bβ.symm
  have hbWnor : b ∈ Nor W := m42_mem_Nor_of_le (hbW b hbNor hbcen)
  have hVcU : ∀ x ∈ V, ∀ y ∈ U, x * y = y * x :=
    m42_U_cen_V hVp (hUV huU) (hUV hvU) hu2 hv2 hu1 hcuv hbu hbv
      (fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (m42_Op_le 2 (Nor U) hx) y).mp hy)
      (fun x hx => by simpa using hVnorm b⁻¹ ((Nor U).inv_mem hbNor) x hx)
  have hCβ : ∀ x ∈ V, x ∈ Cen β → x ∈ U := by
    intro w hwV hwβ
    have hwW : w ∈ W := ⟨hwV, hwβ⟩
    have hwH : w ∈ H := hWH hwW
    have hwL : ∀ x ∈ L, w * x * w⁻¹ ∈ L := S.Δ_normal hN hQ w hwH
    have hwL' : ∀ x ∈ L, w⁻¹ * x * w ∈ L := by
      intro x hx
      simpa using S.Δ_normal hN hQ w⁻¹ (H.inv_mem hwH) x hx
    obtain ⟨t, ht, hwt⟩ := m42_aut_V4 S.Δiso huL hvL hu2 hv2 hu1 hv1 huv hcuv hwL hwL'
      (hVcU w hwV u huU) (hVcU w hwV v hvU)
    have htU : t ∈ U := by
      rcases ht with rfl | rfl | rfl | rfl
      · exact U.one_mem
      · exact huU
      · exact hvU
      · exact huvU
    have htL : t ∈ L := hUL htU
    set z := t⁻¹ * w with hz
    have hzV : z ∈ V := V.mul_mem (V.inv_mem (hUV htU)) hwV
    have hzH : z ∈ H := H.mul_mem (H.inv_mem (S.Δ_le_H htL)) hwH
    have hzK : ∀ y ∈ K, y * z = z * y := by
      intro y hy
      have h1 := S.comm_ΛΔ hN hQ y hy t htL
      have h2 := hKWcomm y hy w hwW
      have h3 : y * t⁻¹ = t⁻¹ * y := by
        calc y * t⁻¹ = t⁻¹ * (t * y) * t⁻¹ := by group
          _ = t⁻¹ * (y * t) * t⁻¹ := by rw [h1]
          _ = t⁻¹ * y := by group
      calc y * (t⁻¹ * w) = (y * t⁻¹) * w := by group
        _ = (t⁻¹ * y) * w := by rw [h3]
        _ = t⁻¹ * (y * w) := by group
        _ = t⁻¹ * (w * y) := by rw [h2]
        _ = t⁻¹ * w * y := by group
    have hzL : ∀ y ∈ L, y * z = z * y := by
      intro y hy
      have h1 := hwt y hy
      calc y * (t⁻¹ * w) = t⁻¹ * (t * y * t⁻¹) * w := by group
        _ = t⁻¹ * (w * y * w⁻¹) * w := by rw [h1]
        _ = t⁻¹ * w * y := by group
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hVp) ⟨z, hzV⟩
    rw [Subgroup.orderOf_mk] at hk
    have hz1 : z = 1 := S.two_cen_eq_one hN hQ hzH hk hzK hzL
    have : w = t := by
      have : t⁻¹ * w = 1 := hz1
      calc w = t * (t⁻¹ * w) := by group
        _ = t := by rw [this, mul_one]
    rw [this]; exact htU
  set Z : Subgroup G := Cen β ⊓ Cen γ with hZ
  have hβZ : β ∈ Z := ⟨m42_mem_cen rfl, m42_mem_cen h.comm_γβ⟩
  have hYZ : H ⊓ Cen γ ≤ Z := fun x hx => ⟨S.cenβ hx.1, hx.2⟩
  have hdec : ∀ z ∈ Z, ∃ i : ℤ, ∃ y ∈ H ⊓ Cen γ, z = β ^ i * y := by
    intro z hz
    have hz' : z ∈ Subgroup.zpowers β ⊔ H := by rw [hC1]; exact hz.1
    obtain ⟨a, ha, y, hy, rfl⟩ := m42_mem_sup_of_comm (fun a ha y hy => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact ((show Commute β y from m42_cen_comm (S.cenβ hy)).zpow_left i).eq) hz'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    refine ⟨i, y, ⟨hy, ?_⟩, rfl⟩
    have hcγz : Commute γ (β ^ i * y) := m42_cen_comm hz.2
    have hcγβ : Commute γ (β ^ i) := (show Commute γ β from h.comm_γβ).zpow_right i
    have := hcγβ.inv_right.mul_right hcγz
    have e : (β ^ i)⁻¹ * (β ^ i * y) = y := by group
    rw [e] at this
    exact m42_mem_cen this.eq
  have hcomm : ⁅Z, Z⁆ ≤ H ⊓ Cen γ :=
    m42_comm_le hβZ (fun z hz => m42_cen_comm hz.1) hYZ hdec
  have hLayZ : Lay Z ≤ H ⊓ Cen γ := inSubgroup_layer_le_of_commutator_le hcomm
  have hLZ1 : Lay Z ≤ L := by
    rw [S.Δdef]
    exact m42_Lay_le_Lay hYZ hLayZ
  have hLZ2 : L ≤ Lay Z := by
    have hLle : L ≤ Z := fun x hx => hYZ (S.Δ_le hx)
    have hLn : ∀ z ∈ Z, ∀ x ∈ L, z * x * z⁻¹ ∈ L := by
      intro z hz x hx
      rw [S.Δdef] at hx ⊢
      exact m42_Lay_conj_mem_of_normalizes (S.norm_HCen hz.1 hz.2) hx
    exact m42_simple_le_Lay hLle hLn S.Δ_nonab
  have hLZ : L = Lay Z := le_antisymm hLZ2 hLZ1
  obtain ⟨n₀, -, h0b, h0b₁, h0b₂⟩ := h.mono.2.2.2.1
  obtain ⟨n₁, -, h1b, h1b₁, h1b₂⟩ := h.mono.2.2.2.2.1
  have hb₁3 : b₁ ^ 3 = 1 := h.pow3_B h.b₁_mem
  have e1 : n₁⁻¹ * b * n₁ = b₁ := by
    calc n₁⁻¹ * b * n₁ = n₁⁻¹ * (n₁ * b₁ * n₁⁻¹) * n₁ := by rw [h1b₁]
      _ = b₁ := by group
  have e2 : n₁⁻¹ * b₁ * n₁ = b := by
    calc n₁⁻¹ * b₁ * n₁ = n₁⁻¹ * (n₁ * b * n₁⁻¹) * n₁ := by rw [h1b]
      _ = b := by group
  have e3 : n₁⁻¹ * b₂ * n₁ = b₂ := by
    calc n₁⁻¹ * b₂ * n₁ = n₁⁻¹ * (n₁ * b₂ * n₁⁻¹) * n₁ := by rw [h1b₂]
      _ = b₂ := by group
  set ψ := n₁ * n₀ * n₁⁻¹ with hψ
  have hψb₁ : ψ * b₁ * ψ⁻¹ = b₁⁻¹ := by
    have : ψ * b₁ * ψ⁻¹ = n₁ * (n₀ * (n₁⁻¹ * b₁ * n₁) * n₀⁻¹) * n₁⁻¹ := by
      simp only [hψ]; group
    rw [this, e2, h0b]
    have : n₁ * b⁻¹ * n₁⁻¹ = (n₁ * b * n₁⁻¹)⁻¹ := by group
    rw [this, h1b]
  have hψb₂ : ψ * b₂ * ψ⁻¹ = b₂ := by
    have : ψ * b₂ * ψ⁻¹ = n₁ * (n₀ * (n₁⁻¹ * b₂ * n₁) * n₀⁻¹) * n₁⁻¹ := by
      simp only [hψ]; group
    rw [this, e3, h0b₂, h1b₂]
  have hb₁inv : b₁⁻¹ = b₁ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hb₁3)
  have hb₁inv2 : b₁⁻¹ * b₁⁻¹ = b₁ := by
    calc b₁⁻¹ * b₁⁻¹ = b₁ ^ 3 * (b₁⁻¹ * b₁⁻¹) := by rw [hb₁3, one_mul]
      _ = b₁ := by group
  have hψβ : ψ * β * ψ⁻¹ = γ := by
    have : ψ * (b₁ * b₂) * ψ⁻¹ = (ψ * b₁ * ψ⁻¹) * (ψ * b₂ * ψ⁻¹) := by group
    rw [hβdef, this, hψb₁, hψb₂, hb₁inv]
  have hψγ : ψ * γ * ψ⁻¹ = β := by
    have : ψ * (b₁ * b₁ * b₂) * ψ⁻¹ = (ψ * b₁ * ψ⁻¹) * (ψ * b₁ * ψ⁻¹) * (ψ * b₂ * ψ⁻¹) := by
      group
    rw [hγdef, pow_two, this, hψb₁, hψb₂, hb₁inv2]
  have hconjZ : ∀ m ∈ Z, ψ * m * ψ⁻¹ ∈ Z := by
    intro m hm
    refine ⟨?_, ?_⟩
    · have hc : Commute γ m := m42_cen_comm hm.2
      have := hc.map (MulAut.conj ψ)
      simp only [MulAut.conj_apply] at this
      rw [hψγ] at this
      exact m42_mem_cen this.eq
    · have hc : Commute β m := m42_cen_comm hm.1
      have := hc.map (MulAut.conj ψ)
      simp only [MulAut.conj_apply] at this
      rw [hψβ] at this
      exact m42_mem_cen this.eq
  have hψL : ∀ x ∈ L, ψ * x * ψ⁻¹ ∈ L := by
    intro x hx
    rw [hLZ] at hx ⊢
    exact m42_Lay_conj_mem_of_normalizes
      (Subgroup.mem_normalizer_iff.mp (m42_mem_Nor_of_le hconjZ)) hx
  set U₂ := U.map (MulAut.conj ψ).toMonoidHom with hU₂
  have hU₂L : U₂ ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact hψL x (hUL hx)
  have hU₂4 : Nat.card U₂ = 4 := by
    rw [hU₂, Subgroup.card_map_of_injective (MulAut.conj ψ).injective, hU4]
  have hfac : (Nat.card L).factorization 2 = 2 := by rw [S.Δiso.card]; exact m42_fact_fact60_two
  obtain ⟨g, hgL, hg⟩ := m42_conj_sylow 2 (M := L) (P := U) (Q := U₂) hUL hU₂L
    (by rw [hU4, hfac]; norm_num) (by rw [hU₂4, hfac]; norm_num)
  set ψ' := g⁻¹ * ψ with hψ'
  have hψ'U : ∀ x ∈ U, ψ' * x * ψ'⁻¹ ∈ U := by
    intro x hx
    have hx2 : ψ * x * ψ⁻¹ ∈ U₂ := ⟨x, hx, rfl⟩
    rw [← hg] at hx2
    obtain ⟨x', hx', hxx'⟩ := hx2
    have hxx'' : g * x' * g⁻¹ = ψ * x * ψ⁻¹ := hxx'
    have e : ψ' * x * ψ'⁻¹ = g⁻¹ * (ψ * x * ψ⁻¹) * g := by simp only [hψ']; group
    rw [e, ← hxx'']
    have : g⁻¹ * (g * x' * g⁻¹) * g = x' := by group
    rw [this]; exact hx'
  have hψ'Nor : ψ' ∈ Nor U := m42_mem_Nor_of_le hψ'U
  have hψ'β : ψ' * β * ψ'⁻¹ = γ := by
    have hc : γ * g = g * γ := m42_cen_comm (S.Δ_le hgL).2
    have e : ψ' * β * ψ'⁻¹ = g⁻¹ * (ψ * β * ψ⁻¹) * g := by simp only [hψ']; group
    rw [e, hψβ]
    calc g⁻¹ * γ * g = g⁻¹ * (γ * g) := by group
      _ = g⁻¹ * (g * γ) := by rw [hc]
      _ = γ := by group
  have hCγ : ∀ x ∈ V, γ * x = x * γ → x ∈ U := by
    intro x hx hxγ
    have hy : ψ'⁻¹ * x * ψ' ∈ V := by
      have := hVnorm ψ'⁻¹ ((Nor U).inv_mem hψ'Nor) x hx
      simpa using this
    have hβeq : β = ψ'⁻¹ * γ * ψ' := by rw [← hψ'β]; group
    have hyβ : ψ'⁻¹ * x * ψ' ∈ Cen β := by
      refine m42_mem_cen ?_
      have e1 : ψ'⁻¹ * γ * ψ' * (ψ'⁻¹ * x * ψ') = ψ'⁻¹ * (γ * x) * ψ' := by group
      have e2 : ψ'⁻¹ * x * ψ' * (ψ'⁻¹ * γ * ψ') = ψ'⁻¹ * (x * γ) * ψ' := by group
      rw [hβeq, e1, e2, hxγ]
    have hyU := hCβ _ hy hyβ
    have := hψ'U _ hyU
    have e : ψ' * (ψ'⁻¹ * x * ψ') * ψ'⁻¹ = x := by group
    rwa [e] at this
  have hVU : V ≤ U := by
    haveI : (((⊥ : Subgroup G).subgroupOf K)).Normal := by
      rw [Subgroup.bot_subgroupOf]; infer_instance
    let e : ↥K ⧸ ((⊥ : Subgroup G).subgroupOf K) ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf K)).trans
        QuotientGroup.quotientBot
    refine FF84.lemmaF_holds G K ⊥ V U γ bot_le IsPGroup.of_bot (MulEquiv.isSimpleGroup e)
      (by rw [Nat.card_congr e.toEquiv, S.Λiso.card]) S.f_Λ S.ord_f hVp hUV ?_
      (fun k hk => m42_mem_Nor_of_le (hVnorm k (hKNor k hk))) (fun k hk => hKNor k hk) ?_
    · exact ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact (Subgroup.mem_normalizer_iff.mp (m42_Op_le 2 _ g.2) n.1).mp hn⟩
    · intro x hx ⟨n, hn, hxn⟩
      have hγ3 : γ ^ 3 = 1 := by
        have := pow_orderOf_eq_one γ
        rwa [S.ord_f] at this
      have h2 : γ * n * γ⁻¹ = n := by
        have := hKU γ S.f_Λ n hn
        rw [this]; group
      have ec2 : γ * (γ * x * γ⁻¹) * γ⁻¹ = x * n * n := by
        rw [hxn]
        have : γ * (x * n) * γ⁻¹ = (γ * x * γ⁻¹) * (γ * n * γ⁻¹) := by group
        rw [this, hxn, h2]
      have ec3 : γ * (γ * (γ * x * γ⁻¹) * γ⁻¹) * γ⁻¹ = x * n * n * n := by
        rw [ec2]
        have : γ * (x * n * n) * γ⁻¹ =
            (γ * x * γ⁻¹) * (γ * n * γ⁻¹) * (γ * n * γ⁻¹) := by group
        rw [this, hxn, h2]
      have e1 : γ * (γ * (γ * x * γ⁻¹) * γ⁻¹) * γ⁻¹ = x := by
        have h111 : γ * γ * γ = 1 := by rw [← hγ3, pow_succ, pow_two]
        have : γ * (γ * (γ * x * γ⁻¹) * γ⁻¹) * γ⁻¹ = (γ * γ * γ) * x * (γ * γ * γ)⁻¹ := by
          group
        rw [this, h111]; group
      have hn3 : n ^ 3 = 1 := by
        have h3 : x * n * n * n = x := by rw [← ec3, e1]
        have h4 : n * n * n = 1 := by
          have h5 : x * (n * n * n) = x * 1 := by
            calc x * (n * n * n) = x * n * n * n := by group
              _ = x := h3
              _ = x * 1 := (mul_one x).symm
          exact mul_left_cancel h5
        calc n ^ 3 = n * n * n := by rw [pow_succ, pow_two]
          _ = 1 := h4
      have hn1 : n = 1 := by
        have hd : orderOf n ∣ 3 := orderOf_dvd_of_pow_eq_one hn3
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU2) ⟨n, hn⟩
        rw [Subgroup.orderOf_mk] at hk
        rw [hk] at hd
        have hk0 : k = 0 := by
          by_contra hne
          have : 2 ∣ 2 ^ k := dvd_pow_self 2 hne
          have := this.trans hd
          omega
        rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
        exact hk
      rw [hn1, mul_one] at hxn
      exact hCγ x hx (by
        have : γ * x = x * γ := by
          calc γ * x = (γ * x * γ⁻¹) * γ := by group
            _ = x * γ := by rw [hxn]
        exact this)
  have hγV : γ ∈ V := hchar γ (hKNor γ S.f_Λ) (fun v hv => (hKU γ S.f_Λ v (hVU hv)).symm)
  exact m42_orderOf_pGroup_ne_three hVp hγV S.ord_f

end CFSG.RankThree.PartTwo.Sec21.FF79
