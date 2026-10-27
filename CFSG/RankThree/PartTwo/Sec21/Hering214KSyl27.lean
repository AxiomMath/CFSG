module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KNine
public import CFSG.RankThree.PartTwo.Sec21.Hering214KMaschke
public import CFSG.RankThree.Asc83Table.Reduction
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open Subgroup CFSG.SectionRank.LocalWitness
open scoped commutatorElement

section Helpers

variable {Y : Type} [Group Y]

theorem isElemAbelian_of_comm_exp {p : ℕ} {H : Subgroup Y} (hc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (he : ∀ x ∈ H, x ^ p = 1) : IsElemAbelian p H :=
  ⟨⟨⟨fun x y => Subtype.ext (hc x.1 x.2 y.1 y.2)⟩⟩, he⟩

theorem isElemAbelian_closure_of_comm_sq {S : Set Y} (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hsq : ∀ a ∈ S, a * a = 1) : IsElemAbelian 2 (closure S) := by
  have h1 : ∀ a ∈ S, ∀ b ∈ closure S, a * b = b * a := by
    intro a ha b hb
    have hle : closure S ≤ Subgroup.centralizer {a} := by
      rw [Subgroup.closure_le]
      intro s hs
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hcomm a ha s hs
    exact (Subgroup.mem_centralizer_iff.mp (hle hb)) a (Set.mem_singleton a)
  have hcm : ∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a := by
    intro a ha b hb
    have hle : closure S ≤ Subgroup.centralizer {b} := by
      rw [Subgroup.closure_le]
      intro s hs
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (h1 s hs b hb).symm
    exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) b (Set.mem_singleton b)).symm
  refine isElemAbelian_of_comm_exp hcm (fun x hx => ?_)
  induction hx using Subgroup.closure_induction with
  | mem a ha => rw [pow_two]; exact hsq a ha
  | one => simp
  | mul a b ha hb iha ihb =>
    rw [(show Commute a b from hcm a ha b hb).mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

end Helpers

section Stable

open Pointwise

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_sylow_conj_inner (hZ : Subgroup.center Y = ⊥)
    (hout : ∀ α : MulAut Y, α ^ 3 = 1 → ∃ y : Y, α = MulAut.conj y) (P₀ : Sylow 3 Y)
    {Ē : Subgroup (MulAut Y)} (hE3 : IsElemAbelian 3 Ē) (hE9 : Nat.card Ē = 9) :
    ∃ (g : Y) (B : Subgroup Y), B ≤ (P₀ : Subgroup Y) ∧ (∀ b ∈ B, b ^ 3 = 1) ∧ Nat.card B = 9 ∧
      (∀ σ ∈ Ē, ∃ x : Y, MulAut.conj x = σ) ∧
      ∀ x : Y, MulAut.conj x ∈ Ē ↔ g * x * g⁻¹ ∈ B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconjinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    Item211LieProof.conj_injective_of_center_eq_bot hZ
  have hrange : ∀ σ ∈ Ē, ∃ x : Y, MulAut.conj x = σ := fun σ hσ => by
    obtain ⟨y, hy⟩ := hout σ (hE3.2 σ hσ)
    exact ⟨y, hy.symm⟩
  have hrange' : Ē ≤ (MulAut.conj : Y →* MulAut Y).range := fun σ hσ => hrange σ hσ
  set Et : Subgroup Y := Ē.comap (MulAut.conj : Y →* MulAut Y) with hEt
  have hEtcard : Nat.card Et = 9 := by
    rw [hEt, Item211LieProof.card_comap_conj hZ hrange', hE9]
  have hEtexp : ∀ x ∈ Et, x ^ 3 = 1 := by
    intro x hx
    apply hconjinj
    rw [map_pow, map_one]
    exact hE3.2 _ hx
  have hEtp : IsPGroup 3 Et := fun g => ⟨1, Subtype.ext (by simpa using hEtexp g.1 g.2)⟩
  obtain ⟨P₁, hP₁⟩ := hEtp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P₁ P₀
  have hconjP : ∀ x ∈ Et, g * x * g⁻¹ ∈ (P₀ : Subgroup Y) := by
    intro x hx
    have h1 : (P₀ : Subgroup Y) = MulAut.conj g • (P₁ : Subgroup Y) := by
      rw [← hg]; rfl
    rw [h1]
    have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P₁ : Subgroup Y) (hP₁ hx)
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  set B : Subgroup Y := Et.map (MulAut.conj g).toMonoidHom with hB
  have hBmem : ∀ b, b ∈ B ↔ ∃ x ∈ Et, g * x * g⁻¹ = b := by
    intro b
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  refine ⟨g, B, ?_, ?_, ?_, hrange, ?_⟩
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := (hBmem b).mp hb
    exact hconjP x hx
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := (hBmem b).mp hb
    rw [conj_pow, hEtexp x hx, mul_one, mul_inv_cancel]
  · rw [hB, Subgroup.card_map_of_injective (show Function.Injective
      (MulAut.conj g).toMonoidHom from (MulAut.conj g).injective), hEtcard]
  · intro x
    constructor
    · intro hx
      exact (hBmem _).mpr ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨x', hx', hxx⟩ := (hBmem _).mp hx
      have : x' = x := by
        have h2 : x' = g⁻¹ * (g * x' * g⁻¹) * g := by group
        rw [h2, hxx]
        group
      rw [← this]
      exact hx'

theorem eInvNine_of_sylow_conj_data (hZ : Subgroup.center Y = ⊥)
    (hout : ∀ α : MulAut Y, α ^ 3 = 1 → ∃ y : Y, α = MulAut.conj y) (P₀ : Sylow 3 Y)
    (H : ∀ B : Subgroup Y, B ≤ (P₀ : Subgroup Y) → (∀ b ∈ B, b ^ 3 = 1) → Nat.card B = 9 →
      ∃ W : Subgroup Y, IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ (∀ b ∈ B, ∀ w ∈ W, b * w * b⁻¹ ∈ W) ∧
        ∃ b ∈ B, ∃ w ∈ W, b * w * b⁻¹ ≠ w) : EInvNine Y := by
  intro Ē hE3 hE9
  obtain ⟨g, B, hBle, hBexp, hB9, hrange, hBiff⟩ := exists_sylow_conj_inner hZ hout P₀ hE3 hE9
  obtain ⟨W, hWab, hW4, hWinv, b, hb, w, hw, hne⟩ := H B hBle hBexp hB9
  set W' : Subgroup Y := W.map (MulAut.conj g⁻¹).toMonoidHom with hW'
  have hmem : ∀ v, v ∈ W' ↔ ∃ w ∈ W, g⁻¹ * w * g = v := by
    intro v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  refine ⟨W', CFSG.Open.IsElemAbelian.map hWab _, ?_, ?_, ?_⟩
  · rw [hW', Subgroup.card_map_of_injective (show Function.Injective
      (MulAut.conj g⁻¹).toMonoidHom from (MulAut.conj g⁻¹).injective), hW4]
  · intro σ hσ v hv
    obtain ⟨w', hw', rfl⟩ := (hmem v).mp hv
    obtain ⟨x, hx⟩ := hrange σ hσ
    have hxB : g * x * g⁻¹ ∈ B := (hBiff x).mp (hx ▸ hσ)
    rw [← hx]
    refine (hmem _).mpr ⟨(g * x * g⁻¹) * w' * (g * x * g⁻¹)⁻¹, hWinv _ hxB w' hw', ?_⟩
    simp only [MulAut.conj_apply]
    group
  · have hxB : g * (g⁻¹ * b * g) * g⁻¹ ∈ B := by
      have : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
      rw [this]
      exact hb
    refine ⟨MulAut.conj (g⁻¹ * b * g), (hBiff _).mpr hxB, g⁻¹ * w * g,
      (hmem _).mpr ⟨w, hw, rfl⟩, fun h => hne ?_⟩
    simp only [MulAut.conj_apply] at h
    have h2 : g * (g⁻¹ * b * g * (g⁻¹ * w * g) * (g⁻¹ * b * g)⁻¹) * g⁻¹ =
        g * (g⁻¹ * w * g) * g⁻¹ := by rw [h]
    calc b * w * b⁻¹ = g * (g⁻¹ * b * g * (g⁻¹ * w * g) * (g⁻¹ * b * g)⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * w * g) * g⁻¹ := h2
      _ = w := by group

theorem eInvNine_of_sylow_stable (hZ : Subgroup.center Y = ⊥)
    (hout : ∀ α : MulAut Y, α ^ 3 = 1 → ∃ y : Y, α = MulAut.conj y)
    (P₀ : Sylow 3 Y) {R : Subgroup Y} (hR : IsElemAbelian 2 R)
    (hst : ∀ p ∈ (P₀ : Subgroup Y), ∀ r ∈ R, p * r * p⁻¹ ∈ R)
    (hnt : ∀ B : Subgroup Y, B ≤ (P₀ : Subgroup Y) → (∀ b ∈ B, b ^ 3 = 1) → Nat.card B = 9 →
      ∃ b ∈ B, ∃ r ∈ R, b * r * b⁻¹ ≠ r) : EInvNine Y := by
  intro Ē hE3 hE9
  obtain ⟨g, B, hBle, hBexp, hB9, hrange, hBiff⟩ := exists_sylow_conj_inner hZ hout P₀ hE3 hE9
  set R' : Subgroup Y := R.map (MulAut.conj g⁻¹).toMonoidHom with hR'
  have hmemR' : ∀ v, v ∈ R' ↔ ∃ r ∈ R, g⁻¹ * r * g = v := by
    intro v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  refine eInvFour_of_elemAbelian_two hE3 hE9 (R := R') (CFSG.Open.IsElemAbelian.map hR _) ?_ ?_
  · intro σ hσ v hv
    obtain ⟨r, hr, rfl⟩ := (hmemR' v).mp hv
    obtain ⟨x, hx⟩ := hrange σ hσ
    have hxB : g * x * g⁻¹ ∈ B := (hBiff x).mp (hx ▸ hσ)
    rw [← hx]
    refine (hmemR' _).mpr ⟨(g * x * g⁻¹) * r * (g * x * g⁻¹)⁻¹, hst _ (hBle hxB) r hr, ?_⟩
    simp only [MulAut.conj_apply]
    group
  · obtain ⟨b, hb, r, hr, hne⟩ := hnt B hBle hBexp hB9
    have hxB : g * (g⁻¹ * b * g) * g⁻¹ ∈ B := by
      have : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
      rw [this]
      exact hb
    refine ⟨MulAut.conj (g⁻¹ * b * g), (hBiff _).mpr hxB, g⁻¹ * r * g,
      (hmemR' _).mpr ⟨r, hr, rfl⟩, fun h => hne ?_⟩
    simp only [MulAut.conj_apply] at h
    have h2 : g * (g⁻¹ * b * g * (g⁻¹ * r * g) * (g⁻¹ * b * g)⁻¹) * g⁻¹ =
        g * (g⁻¹ * r * g) * g⁻¹ := by rw [h]
    calc b * r * b⁻¹ = g * (g⁻¹ * b * g * (g⁻¹ * r * g) * (g⁻¹ * b * g)⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * r * g) * g⁻¹ := h2
      _ = r := by group

end Stable

section Closure

variable {Y : Type} [Group Y] [Finite Y]

theorem conj_mem_of_closure_pair {a b : Y} {W : Subgroup Y}
    (ha : ∀ w ∈ W, a * w * a⁻¹ ∈ W) (hb : ∀ w ∈ W, b * w * b⁻¹ ∈ W) :
    ∀ e ∈ closure ({a, b} : Set Y), ∀ w ∈ W, e * w * e⁻¹ ∈ W := by
  intro e he
  induction he using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hb
  | one => intro w hw; simpa using hw
  | mul x y _ _ hx hy =>
    intro w hw
    have := hx _ (hy w hw)
    simpa [mul_assoc] using this
  | inv x _ hx =>
    intro w hw
    let f : W → W := fun v => ⟨x * v * x⁻¹, hx v v.2⟩
    have hfinj : Function.Injective f := by
      intro v v' h
      have h' : x * (v : Y) * x⁻¹ = x * (v' : Y) * x⁻¹ := congrArg Subtype.val h
      exact Subtype.ext (by simpa using h')
    obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hfinj) ⟨w, hw⟩
    have hv' : x * v * x⁻¹ = w := congrArg Subtype.val hv
    have : x⁻¹ * w * (x⁻¹)⁻¹ = v := by
      rw [← hv']; group
    rw [this]
    exact v.2

@[expose] def FourDatum (z w : Y) : Prop :=
  ∃ u₁ u₂ : Y, u₁ * u₁ = 1 ∧ u₂ * u₂ = 1 ∧ u₁ * u₂ = u₂ * u₁ ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₁ ≠ u₂ ∧
    Four4 u₁ u₂ (z * u₁ * z⁻¹) ∧ Four4 u₁ u₂ (z * u₂ * z⁻¹) ∧
    Four4 u₁ u₂ (w * u₁ * w⁻¹) ∧ Four4 u₁ u₂ (w * u₂ * w⁻¹) ∧
    (z * u₁ * z⁻¹ ≠ u₁ ∨ w * u₁ * w⁻¹ ≠ u₁)

theorem FourDatum.exists_four {z w : Y} (h : FourDatum z w) :
    ∃ W : Subgroup Y, IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      (∀ e ∈ closure ({z, w} : Set Y), ∀ v ∈ W, e * v * e⁻¹ ∈ W) ∧
      ∃ e ∈ closure ({z, w} : Set Y), ∃ v ∈ W, e * v * e⁻¹ ≠ v := by
  obtain ⟨u₁, u₂, hu₁, hu₂, hu, hu₁1, hu₂1, hu₁₂, hz₁, hz₂, hw₁, hw₂, hmove⟩ := h
  set W₀ : Subgroup Y := closure ({u₁, u₂} : Set Y) with hW₀
  have hmemW : ∀ t : Y, Four4 u₁ u₂ t → t ∈ W₀ := by
    intro t ht
    rcases ht with h | h | h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hmapW : ∀ g : Y, Four4 u₁ u₂ (g * u₁ * g⁻¹) → Four4 u₁ u₂ (g * u₂ * g⁻¹) →
      ∀ w ∈ W₀, g * w * g⁻¹ ∈ W₀ := by
    intro g h1 h2 w hw
    have hle : W₀.map (MulAut.conj g).toMonoidHom ≤ W₀ := by
      rw [hW₀, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with hx | hx
      · rw [hx]
        have := hmemW _ h1
        simpa [MulAut.conj_apply] using this
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        have := hmemW _ h2
        simpa [MulAut.conj_apply] using this
    exact hle ⟨w, hw, rfl⟩
  have hzmem : z ∈ closure ({z, w} : Set Y) := Subgroup.subset_closure (Set.mem_insert _ _)
  have hwmem : w ∈ closure ({z, w} : Set Y) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine ⟨W₀, isElemAbelian_closure_pair hu₁ hu₂ hu, card_closure_pair hu₁ hu₂ hu hu₁1 hu₂1 hu₁₂,
    conj_mem_of_closure_pair (hmapW z hz₁ hz₂) (hmapW w hw₁ hw₂), ?_⟩
  have hu₁W : u₁ ∈ W₀ := Subgroup.subset_closure (Set.mem_insert _ _)
  rcases hmove with hm | hm
  · exact ⟨z, hzmem, u₁, hu₁W, hm⟩
  · exact ⟨w, hwmem, u₁, hu₁W, hm⟩

end Closure

section Extra27

variable {Y : Type} [Group Y] [Finite Y] {x y : Y}

theorem eInvNine_of_extraspecial27 (hZ : Subgroup.center Y = ⊥)
    (hout : ∀ α : MulAut Y, α ^ 3 = 1 → ∃ y : Y, α = MulAut.conj y)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hz1 : ⁅x, y⁆ ≠ 1) (hL : (Nat.card Y).factorization 3 = 3) {u : Y} (hu : u * u = 1)
    (hcomm : ∀ i j k : Fin 3, u * ((x ^ (i : ℕ) * y ^ (j : ℕ) * ⁅x, y⁆ ^ (k : ℕ)) * u *
        (x ^ (i : ℕ) * y ^ (j : ℕ) * ⁅x, y⁆ ^ (k : ℕ))⁻¹) =
      ((x ^ (i : ℕ) * y ^ (j : ℕ) * ⁅x, y⁆ ^ (k : ℕ)) * u *
        (x ^ (i : ℕ) * y ^ (j : ℕ) * ⁅x, y⁆ ^ (k : ℕ))⁻¹) * u)
    (hmove : ⁅x, y⁆ * u * ⁅x, y⁆⁻¹ ≠ u) : EInvNine Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := closure ({x, y} : Set Y) with hP
  have hPcard : Nat.card P = 27 := Asc83Table.ex27_card hx hy hzx hzy hz1
  have hPsyl : Nat.card P = 3 ^ (Nat.card Y).factorization 3 :=
    Asc83Table.ex27_card_sylow hx hy hzx hzy hz1 hL
  let P₀ : Sylow 3 Y := Sylow.ofCard P hPsyl
  have hP₀ : (P₀ : Subgroup Y) = P := Sylow.coe_ofCard P hPsyl
  set S : Set Y := {s | ∃ p ∈ P, s = p * u * p⁻¹} with hS
  have hSpair : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    have hr : q⁻¹ * p ∈ P := P.mul_mem (P.inv_mem hq) hp
    obtain ⟨i, j, k, hi, hj, hk, hrr⟩ :=
      mem_closure_normalForm (by norm_num) hx hy hzx hzy hr
    have hc := hcomm ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩
    simp only at hc
    rw [← hrr] at hc
    have key : (q⁻¹ * p) * u * (q⁻¹ * p)⁻¹ * u = u * ((q⁻¹ * p) * u * (q⁻¹ * p)⁻¹) := hc.symm
    have h2 : q⁻¹ * (p * u * p⁻¹ * (q * u * q⁻¹)) * q =
        q⁻¹ * (q * u * q⁻¹ * (p * u * p⁻¹)) * q := by
      calc q⁻¹ * (p * u * p⁻¹ * (q * u * q⁻¹)) * q
          = (q⁻¹ * p) * u * (q⁻¹ * p)⁻¹ * u := by group
        _ = u * ((q⁻¹ * p) * u * (q⁻¹ * p)⁻¹) := key
        _ = q⁻¹ * (q * u * q⁻¹ * (p * u * p⁻¹)) * q := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hSsq : ∀ a ∈ S, a * a = 1 := by
    rintro _ ⟨p, hp, rfl⟩
    calc p * u * p⁻¹ * (p * u * p⁻¹) = p * (u * u) * p⁻¹ := by group
      _ = 1 := by rw [hu]; group
  have hRab : IsElemAbelian 2 (closure S) := isElemAbelian_closure_of_comm_sq hSpair hSsq
  have hst : ∀ p ∈ P, ∀ r ∈ closure S, p * r * p⁻¹ ∈ closure S := by
    intro p hp r hr
    induction hr using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨q, hq, rfl⟩ := hs
      refine subset_closure ⟨p * q, P.mul_mem hp hq, ?_⟩
      group
    | one => simpa using (closure S).one_mem
    | mul a b _ _ iha ihb =>
      have := (closure S).mul_mem iha ihb
      convert this using 1
      group
    | inv a _ iha =>
      have := (closure S).inv_mem iha
      convert this using 1
      group
  have huS : u ∈ S := ⟨1, P.one_mem, by group⟩
  have hmemP : ∀ p, p ∈ (P₀ : Subgroup Y) → p ∈ P := fun p hp => by
    rw [hP₀] at hp
    exact hp
  refine eInvNine_of_sylow_stable hZ hout P₀ hRab (fun p hp r hr => hst p (hmemP p hp) r hr) ?_
  intro B hBle _ hB9
  have hzB : ⁅x, y⁆ ∈ B :=
    Asc83Table.commutator_mem_of_card_eq_nine hPcard (le_of_le_of_eq hBle hP₀) hB9
  exact ⟨⁅x, y⁆, hzB, u, subset_closure huS, hmove⟩

theorem eInvNine_of_extraspecial27_four (hZ : Subgroup.center Y = ⊥)
    (hout : ∀ α : MulAut Y, α ^ 3 = 1 → ∃ y : Y, α = MulAut.conj y)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hz1 : ⁅x, y⁆ ≠ 1) (hL : (Nat.card Y).factorization 3 = 3)
    (h₁ : FourDatum ⁅x, y⁆ x) (h₂ : FourDatum ⁅x, y⁆ y) (h₃ : FourDatum ⁅x, y⁆ (x * y))
    (h₄ : FourDatum ⁅x, y⁆ (x * y ^ 2)) : EInvNine Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := closure ({x, y} : Set Y) with hP
  have hPcard : Nat.card P = 27 := Asc83Table.ex27_card hx hy hzx hzy hz1
  have hPsyl : Nat.card P = 3 ^ (Nat.card Y).factorization 3 :=
    Asc83Table.ex27_card_sylow hx hy hzx hzy hz1 hL
  let P₀ : Sylow 3 Y := Sylow.ofCard P hPsyl
  have hP₀ : (P₀ : Subgroup Y) = P := Sylow.coe_ofCard P hPsyl
  refine eInvNine_of_sylow_conj_data hZ hout P₀ ?_
  intro B hBle _ hB9
  have hB := Asc83Table.eq_of_le_of_card_eq_nine hx hy hzx hzy hPcard (le_of_le_of_eq hBle hP₀) hB9
  rcases hB with h | h | h | h <;> rw [h]
  · obtain ⟨W, hW, hW4, hinv, e, he, v, hv, hne⟩ := h₁.exists_four
    exact ⟨W, hW, hW4, hinv, e, he, v, hv, hne⟩
  · obtain ⟨W, hW, hW4, hinv, e, he, v, hv, hne⟩ := h₂.exists_four
    exact ⟨W, hW, hW4, hinv, e, he, v, hv, hne⟩
  · obtain ⟨W, hW, hW4, hinv, e, he, v, hv, hne⟩ := h₃.exists_four
    exact ⟨W, hW, hW4, hinv, e, he, v, hv, hne⟩
  · obtain ⟨W, hW, hW4, hinv, e, he, v, hv, hne⟩ := h₄.exists_four
    exact ⟨W, hW, hW4, hinv, e, he, v, hv, hne⟩

end Extra27

end CFSG.RankThree.PartTwo.Sec21.Hering214
