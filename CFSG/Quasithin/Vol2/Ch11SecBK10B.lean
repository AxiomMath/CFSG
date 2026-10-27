module

public import CFSG.Quasithin.Vol2.Ch11SecBK10A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

namespace BK10

section Quot

variable {L : Type*} [Group L]

@[expose] noncomputable def quotAut (M : Subgroup L) [M.Characteristic] :
    MulAut L →* MulAut (L ⧸ M) where
  toFun φ := QuotientGroup.congr M M φ (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem quotAut_mk (M : Subgroup L) [M.Characteristic] (φ : MulAut L) (l : L) :
    quotAut M φ (l : L ⧸ M) = ((φ l : L) : L ⧸ M) := rfl

theorem eq_one_of_quotAut_center [Group.IsPerfect L] {α : MulAut L}
    (h : quotAut (Subgroup.center L) α = 1) : α = 1 := by
  have hc : ∀ x : L, x⁻¹ * α x ∈ Subgroup.center L := fun x => by
    have h1 := congrArg (fun φ : MulAut (L ⧸ Subgroup.center L) =>
      φ (x : L ⧸ Subgroup.center L)) h
    simp only [quotAut_mk, MulAut.one_apply] at h1
    exact QuotientGroup.eq.mp h1.symm
  let f : L →* Subgroup.center L :=
    { toFun := fun x => ⟨x⁻¹ * α x, hc x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change (x * y)⁻¹ * α (x * y) = x⁻¹ * α x * (y⁻¹ * α y)
        have h1 := Subgroup.mem_center_iff.mp (hc x) y⁻¹
        rw [map_mul]
        calc (x * y)⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [h1]
          _ = x⁻¹ * α x * (y⁻¹ * α y) := by group) }
  have hker : commutator L ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [Group.IsPerfect.commutator_eq_top] at hker
  ext x
  have hx := hker (Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  have h1 : x⁻¹ * α x = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  calc α x = x * (x⁻¹ * α x) := by group
    _ = x := by rw [h1, mul_one]

end Quot

theorem IsCoprimePrimeAut.conj {X : Type} [Group X] {β : MulAut X} (hβ : IsCoprimePrimeAut β)
    (γ : MulAut X) : IsCoprimePrimeAut (γ * β * γ⁻¹) := by
  obtain ⟨r, hr, hβr, hβ1, hrX⟩ := hβ
  refine ⟨r, hr, ?_, fun h => hβ1 ?_, hrX⟩
  · rw [conj_pow, hβr, mul_one, mul_inv_cancel]
  · have h1 : β = γ⁻¹ * (γ * β * γ⁻¹) * γ := by group
    rw [h1, h]
    group

section Lift

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_normalizer_of_conj_mem {Y S R : Subgroup G} (hS2 : IsPGroup 2 S)
    (hQ : IsSylowTwoOf (S ⊓ Y) Y)
    (hQR : S ⊓ Y ≤ R) (hRY : R ≤ Y) (hSR : S ≤ Subgroup.normalizer (R : Set G)) {b : G}
    (hb : b ∈ Y) (hbS : ∀ s ∈ S, s * b * s⁻¹ * b⁻¹ ∈ R) :
    ∃ d ∈ Y, d ∈ Subgroup.normalizer (S : Set G) ∧ d * b⁻¹ ∈ R := by
  set Q := S ⊓ Y with hQdef
  have hWcoe : ((R ⊔ S : Subgroup G) : Set G) = (R : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left R S hSR
  have hRS : R ⊓ S = Q :=
    le_antisymm (fun x hx => ⟨hx.2, hRY hx.1⟩) (fun x hx => ⟨hQR hx, hx.1⟩)
  have hQS : Q ≤ S := inf_le_left
  have hSW : S ≤ R ⊔ S := le_sup_right
  have hRW : R ≤ R ⊔ S := le_sup_left
  have hidx1 : R.relIndex (R ⊔ S) = Q.relIndex S := by
    have h1 := CFSG.Quasithin.A4.relIndex_sup_eq_of_le_normalizer' hSR
    rw [sup_comm] at h1
    rw [h1, ← Subgroup.inf_relIndex_right R S, hRS]
  have hcardS : Nat.card S ≠ 0 := Nat.card_pos.ne'
  have hQSne : Q.relIndex S ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_mul_card Q S
    rw [h0, zero_mul] at this
    exact hcardS this.symm
  have hidx2 : S.relIndex (R ⊔ S) = Q.relIndex R := by
    have h1 := Subgroup.relIndex_mul_relIndex Q S (R ⊔ S) hQS hSW
    have h2 := Subgroup.relIndex_mul_relIndex Q R (R ⊔ S) hQR hRW
    have h3 : Q.relIndex S * S.relIndex (R ⊔ S) = Q.relIndex S * Q.relIndex R := by
      rw [h1, ← h2, hidx1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hQSne) h3
  have hodd : ¬ 2 ∣ Q.relIndex R := by
    have h1 := Subgroup.relIndex_mul_relIndex Q R Y hQR hRY
    intro h2
    apply hQ.2.2
    change 2 ∣ Q.relIndex Y
    rw [← h1]
    exact Dvd.dvd.mul_right h2 _
  have hSsyl : IsSylowTwoOf S (R ⊔ S) := ⟨hSW, hS2, by
    change ¬ 2 ∣ S.relIndex (R ⊔ S)
    rw [hidx2]
    exact hodd⟩
  set S' := S.map (MulAut.conj b).toMonoidHom with hS'
  have hS'W : S' ≤ R ⊔ S := by
    rintro _ ⟨s, hs, rfl⟩
    change b * s * b⁻¹ ∈ R ⊔ S
    have h1 : b * s * b⁻¹ * s⁻¹ ∈ R := by
      have h2 := hbS s⁻¹ (S.inv_mem hs)
      have h3 := (Subgroup.mem_normalizer_iff.mp (hSR hs) _).mp h2
      have h4 : s * (s⁻¹ * b * s⁻¹⁻¹ * b⁻¹) * s⁻¹ = b * s * b⁻¹ * s⁻¹ := by group
      rwa [h4] at h3
    have h5 : b * s * b⁻¹ = (b * s * b⁻¹ * s⁻¹) * s := by group
    rw [h5]
    exact (R ⊔ S).mul_mem (hRW h1) (hSW hs)
  have hcardS' : Nat.card S' = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj b).injective
  have hS'syl : IsSylowTwoOf S' (R ⊔ S) := by
    refine ⟨hS'W, hS2.map _, ?_⟩
    change ¬ 2 ∣ S'.relIndex (R ⊔ S)
    have h1 := Subgroup.relIndex_mul_card S' (R ⊔ S)
    have h2 := Subgroup.relIndex_mul_card S (R ⊔ S)
    rw [inf_eq_left.mpr hS'W] at h1
    rw [inf_eq_left.mpr hSW] at h2
    have h3 : S'.relIndex (R ⊔ S) = S.relIndex (R ⊔ S) := by
      rw [hcardS'] at h1
      rw [← h2] at h1
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hcardS) h1
    rw [h3]
    exact hSsyl.2.2
  obtain ⟨w, hwW, hw⟩ := CFSG.Quasithin.A4.exists_conj_of_isSylowTwoOf hSsyl hS'syl
  have hwRS : w ∈ (R : Set G) * (S : Set G) := by
    rw [← hWcoe]
    exact hwW
  obtain ⟨r, hr, s₀, hs₀, rfl⟩ := hwRS
  refine ⟨r⁻¹ * b, Y.mul_mem (Y.inv_mem (hRY hr)) hb, ?_, by
    rw [mul_inv_cancel_right]
    exact R.inv_mem hr⟩
  apply CFSG.Quasithin.A4.mem_normalizer_of_conj_mem
  intro x hx
  have h1 : b * x * b⁻¹ ∈ S' := ⟨x, hx, rfl⟩
  have h2 := (hw _).mp h1
  have h3 : s₀ * ((r * s₀)⁻¹ * (b * x * b⁻¹) * (r * s₀)) * s₀⁻¹ ∈ S :=
    S.mul_mem (S.mul_mem hs₀ h2) (S.inv_mem hs₀)
  have h4 : s₀ * ((r * s₀)⁻¹ * (b * x * b⁻¹) * (r * s₀)) * s₀⁻¹ = r⁻¹ * b * x * (r⁻¹ * b)⁻¹ := by
    group
  rwa [h4] at h3

omit [Finite G] in
theorem exists_eq_mul_of_isHallTwoPrimeOf {Y S D : Subgroup G}
    (hQ : IsSylowTwoOf (S ⊓ Y) Y)
    (hD : Lin2.IsHallTwoPrimeOf D (Y ⊓ Subgroup.normalizer (S : Set G))) {d : G}
    (hd : d ∈ Y ⊓ Subgroup.normalizer (S : Set G)) : ∃ q ∈ S ⊓ Y, ∃ d' ∈ D, d = q * d' := by
  set M := Y ⊓ Subgroup.normalizer (S : Set G) with hM
  set Q := S ⊓ Y with hQdef
  have hQM : Q ≤ M := fun x hx => ⟨hx.2, Subgroup.le_normalizer hx.1⟩
  have hMY : M ≤ Y := inf_le_left
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp hm.2 x
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hm.1) x
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  obtain ⟨hDM, -, k, hk⟩ := hD
  have hcoe : ((Q ⊔ D : Subgroup G) : Set G) = (Q : Set G) * (D : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Q D (hDM.trans hMQ)
  have hle : Q ⊔ D ≤ M := sup_le hQM hDM
  have h1 : (Q ⊔ D).relIndex M ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.relIndex_dvd_of_le_left M le_sup_right
  have h2 : ¬ 2 ∣ Q.relIndex M := by
    intro h
    apply hQ.2.2
    change 2 ∣ Q.relIndex Y
    rw [← Subgroup.relIndex_mul_relIndex Q M Y hQM hMY]
    exact Dvd.dvd.mul_right h _
  have h3 : (Q ⊔ D).relIndex M ∣ Q.relIndex M := Subgroup.relIndex_dvd_of_le_left M le_sup_left
  have h4 : (Q ⊔ D).relIndex M = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases j with _ | j
    · simpa using hj
    · exfalso
      apply h2
      rw [hj, pow_succ] at h3
      exact (Dvd.intro_left _ rfl).trans h3
  have hdQD : d ∈ ((Q ⊔ D : Subgroup G) : Set G) := (Subgroup.relIndex_eq_one.mp h4) hd
  rw [hcoe] at hdQD
  obtain ⟨q, hq, d', hd', rfl⟩ := hdQD
  exact ⟨q, hq, d', hd', rfl⟩

end Lift

section Core

variable {G : Type*} [Group G] [Finite G] {X : Type} [Group X]

theorem not_isCoprimePrimeAut_of_lift {Y S R D : Subgroup G} (hS2 : IsPGroup 2 S)
    (hQ : IsSylowTwoOf (S ⊓ Y) Y)
    (hQR : S ⊓ Y ≤ R) (hRY : R ≤ Y) (hSR : S ≤ Subgroup.normalizer (R : Set G))
    (hD : Lin2.IsHallTwoPrimeOf D (Y ⊓ Subgroup.normalizer (S : Set G)))
    (φ : ↥Y →* X) {P : Subgroup X} (hφR : ∀ z (hz : z ∈ R), φ ⟨z, hRY hz⟩ ∈ P)
    {y : X} (hy : ∀ y' : X, y' * y⁻¹ ∈ P → Odd (orderOf y') →
        ∀ β : MulAut X, IsCoprimePrimeAut β → β y' = y' → β = 1)
    {b : G} (hb : b ∈ Y) (hby : φ ⟨b, hb⟩ = y) (hbS : ∀ s ∈ S, s * b * s⁻¹ * b⁻¹ ∈ R)
    {β : MulAut X} (hβD : ∀ z (hz : z ∈ D), β (φ ⟨z, (hD.1 hz).1⟩) = φ ⟨z, (hD.1 hz).1⟩) :
    ¬ IsCoprimePrimeAut β := by
  intro hβc
  obtain ⟨d, hdY, hdS, hdR⟩ := exists_mem_normalizer_of_conj_mem hS2 hQ hQR hRY hSR hb hbS
  obtain ⟨q, hq, d', hd', rfl⟩ := exists_eq_mul_of_isHallTwoPrimeOf hQ hD ⟨hdY, hdS⟩
  have hd'Y : d' ∈ Y := (hD.1 hd').1
  have hqY : q ∈ Y := hq.2
  have h1 : φ ⟨d', hd'Y⟩ * y⁻¹ ∈ P := by
    have hq' := hφR q (hQR hq)
    have hdR' := hφR _ hdR
    have h2 : φ ⟨d', hd'Y⟩ * y⁻¹ =
        (φ ⟨q, hRY (hQR hq)⟩)⁻¹ * φ ⟨q * d' * b⁻¹, hRY hdR⟩ := by
      rw [← hby, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h2]
    exact P.mul_mem (P.inv_mem hq') hdR'
  have h3 : Odd (orderOf (φ ⟨d', hd'Y⟩)) := by
    have h4 : orderOf (φ ⟨d', hd'Y⟩) ∣ orderOf (⟨d', hd'Y⟩ : ↥Y) := orderOf_map_dvd φ _
    have h5 : orderOf (⟨d', hd'Y⟩ : ↥Y) = orderOf d' := Subgroup.orderOf_mk d' hd'Y
    have h6 : orderOf d' ∣ Nat.card D := Subgroup.orderOf_dvd_natCard D hd'
    exact Odd.of_dvd_nat (hD.2.1.of_dvd_nat h6) (h5 ▸ h4)
  have h7 : β (φ ⟨d', hd'Y⟩) = φ ⟨d', hd'Y⟩ := hβD d' hd'
  have hβ1 : β ≠ 1 := by
    obtain ⟨r, -, -, h, -⟩ := hβc
    exact h
  exact hβ1 (hy _ h1 h3 β hβc h7)

end Core

end BK10

end CFSG.Quasithin.Vol2.Ch11.SecD
