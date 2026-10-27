module

public import CFSG.Quasithin.Background.C116Three.L3LocalA
public import CFSG.Quasithin.Background.B4L3Key
public import CFSG.Quasithin.EmptyFaithful.R3c23Def
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {M C : Subgroup V}

section Std

open Classical in
noncomputable def jwBg (D : L3Data G M C) (B : Subgroup (MulAut V)) : Finset L3.Γ :=
  Finset.univ.filter fun γ => L3F.Ustd γ ∧ D.rho γ ∈ B

theorem mem_jwBg {D : L3Data G M C} {B : Subgroup (MulAut V)} {γ : L3.Γ} :
    γ ∈ jwBg D B ↔ L3F.Ustd γ ∧ D.rho γ ∈ B := by
  classical
  simp [jwBg]

theorem jw_card_B (D : L3Data G M C) {B : Subgroup (MulAut V)}
    (hBU : ∀ b ∈ B, ∃ γ : L3.Γ, L3F.Ustd γ ∧ D.rho γ = b) :
    Nat.card B = (jwBg D B).card := by
  have h1 : (B : Set (MulAut V)) = D.rho '' (jwBg D B : Set L3.Γ) := by
    ext b
    constructor
    · intro hb
      obtain ⟨γ, hγ, rfl⟩ := hBU b hb
      exact ⟨γ, mem_jwBg.2 ⟨hγ, hb⟩, rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact (mem_jwBg.1 hγ).2
  calc Nat.card B = (B : Set (MulAut V)).ncard := Nat.card_coe_set_eq _
    _ = (D.rho '' (jwBg D B : Set L3.Γ)).ncard := by rw [h1]
    _ = (jwBg D B : Set L3.Γ).ncard := Set.ncard_image_of_injective _ D.rho_injective
    _ = (jwBg D B).card := Set.ncard_coe_finset _

open Classical in
noncomputable def jwS (D : L3Data G M C) (B : Subgroup (MulAut V)) : Finset L3.Vec :=
  Finset.univ.filter fun ξ => ∀ γ ∈ jwBg D B, L3.act γ ξ = ξ

theorem mem_jwS {D : L3Data G M C} {B : Subgroup (MulAut V)} {ξ : L3.Vec} :
    ξ ∈ jwS D B ↔ ∀ γ ∈ jwBg D B, L3.act γ ξ = ξ := by
  classical
  simp [jwS]

theorem jwS_zero (D : L3Data G M C) (B : Subgroup (MulAut V)) : (0 : L3.Vec) ∈ jwS D B := by
  rw [mem_jwS]
  intro γ _
  exact L3.act_zero γ

theorem jwS_add (D : L3Data G M C) (B : Subgroup (MulAut V)) :
    ∀ x ∈ jwS D B, ∀ y ∈ jwS D B, x + y ∈ jwS D B := by
  intro x hx y hy
  rw [mem_jwS] at hx hy ⊢
  intro γ hγ
  rw [L3.act_add, hx γ hγ, hy γ hγ]

noncomputable def jwSub (D : L3Data G M C) (B : Subgroup (MulAut V)) :
    Subgroup (Multiplicative L3.Vec) :=
  SubOf (jwS D B) (jwS_zero D B) (jwS_add D B)

theorem jw_fixMod_eq (D : L3Data G M C) {B : Subgroup (MulAut V)}
    (hBU : ∀ b ∈ B, ∃ γ : L3.Γ, L3F.Ustd γ ∧ D.rho γ = b) :
    fixMod B M C = D.pre (jwSub D B) := by
  ext x
  rw [mem_fixMod, D.mem_pre]
  constructor
  · rintro ⟨hxM, hx⟩
    refine ⟨hxM, ?_⟩
    show Multiplicative.toAdd (D.β ⟨x, hxM⟩) ∈ jwS D B
    rw [mem_jwS]
    intro γ hγ
    have hγB := (mem_jwBg.1 hγ).2
    have h1 := hx _ hγB
    have hρx : D.rho γ x ∈ M := D.inv_U _ (D.rho_mem γ) x hxM
    have hmem : D.rho γ x * x⁻¹ ∈ M := M.mul_mem hρx (M.inv_mem hxM)
    have hc := D.β_comm γ ⟨x, hxM⟩ hρx hmem
    have h2 : D.β ⟨D.rho γ x * x⁻¹, hmem⟩ = 1 := (D.ker_β _).2 h1
    rw [hc] at h2
    have h3 : Multiplicative.toAdd (D.β ⟨x, hxM⟩) |> fun ξ => L3.act γ ξ - ξ = 0 := by
      have := congrArg Multiplicative.toAdd h2
      simpa using this
    exact sub_eq_zero.1 h3
  · rintro ⟨hxM, hS⟩
    refine ⟨hxM, fun b hb => ?_⟩
    obtain ⟨γ, hγ, rfl⟩ := hBU b hb
    have hγB : γ ∈ jwBg D B := mem_jwBg.2 ⟨hγ, hb⟩
    have hS' : ∀ γ ∈ jwBg D B, L3.act γ (Multiplicative.toAdd (D.β ⟨x, hxM⟩)) =
        Multiplicative.toAdd (D.β ⟨x, hxM⟩) := mem_jwS.1 hS
    have hρx : D.rho γ x ∈ M := D.inv_U _ (D.rho_mem γ) x hxM
    have hmem : D.rho γ x * x⁻¹ ∈ M := M.mul_mem hρx (M.inv_mem hxM)
    have hc := D.β_comm γ ⟨x, hxM⟩ hρx hmem
    rw [hS' γ hγB, sub_self] at hc
    exact (D.ker_β _).1 (by rw [hc]; rfl)

theorem jw_card_fixMod [Finite V] (D : L3Data G M C) {B : Subgroup (MulAut V)}
    (hBU : ∀ b ∈ B, ∃ γ : L3.Γ, L3F.Ustd γ ∧ D.rho γ = b) :
    Nat.card ↥(fixMod B M C) = Nat.card C * (jwS D B).card := by
  rw [jw_fixMod_eq D hBU, D.card_pre]
  unfold jwSub
  rw [card_SubOf]

theorem jw_fixV_le [Finite V] (B : Subgroup (MulAut V)) (M C : Subgroup V) :
    fixV B ⊓ M ≤ fixMod B M C := by
  rintro x ⟨hxB, hxM⟩
  rw [mem_fixMod]
  refine ⟨hxM, fun b hb => ?_⟩
  rw [(mem_fixV.1 hxB) b hb, mul_inv_cancel]
  exact C.one_mem

theorem jw_cases (D : L3Data G M C) {B : Subgroup (MulAut V)} (hBel : IsElemAbelian2 B) :
    jwBg D B ⊆ L3F.B1 ∨ jwBg D B ⊆ L3F.B2 := by
  by_cases h : jwBg D B ⊆ L3F.B1
  · exact Or.inl h
  · right
    obtain ⟨δ, hδ, hδ1⟩ := Finset.not_subset.1 h
    intro γ hγ
    have hδ' := mem_jwBg.1 hδ
    have hγ' := mem_jwBg.1 hγ
    have hcomm : γ * δ = δ * γ := by
      apply D.rho_injective
      rw [map_mul, map_mul]
      exact hBel.1 _ hγ'.2 _ hδ'.2
    have hγ2 : γ * γ = 1 := by
      apply D.rho_injective
      rw [map_mul, map_one]
      have := hBel.2 _ hγ'.2
      rwa [pow_two] at this
    have hδ2 : δ * δ = 1 := by
      apply D.rho_injective
      rw [map_mul, map_one]
      have := hBel.2 _ hδ'.2
      rwa [pow_two] at this
    rcases L3F.U_comm γ hγ'.1 hγ2 δ hδ'.1 hδ2 hcomm with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact absurd h1 hδ1
    · exact h1

theorem jw_claim [Finite V] (D : L3Data G M C) {B : Subgroup (MulAut V)}
    (hBU : ∀ b ∈ B, ∃ γ : L3.Γ, L3F.Ustd γ ∧ D.rho γ = b) (hBel : IsElemAbelian2 B) :
    jwBg D B = L3F.B1 ∨ (jwBg D B).card * (jwS D B).card ≤ 8 := by
  classical
  have hcard := jw_card_B D hBU
  have hpow : Nat.card B = 2 ^ rk B := B1.card_elemAbelian hBel
  have hle4 : (jwBg D B).card ≤ 4 := by
    rcases jw_cases D hBel with h | h
    · exact (Finset.card_le_card h).trans (by rw [L3F.card_B1])
    · exact (Finset.card_le_card h).trans (by rw [L3F.card_B2])
  have hk : rk B ≤ 2 := by
    have h1 : 2 ^ rk B ≤ 2 ^ 2 := by rw [← hpow, hcard]; omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hSle : (jwS D B).card ≤ 8 := by
    have := Finset.card_le_univ (jwS D B)
    simpa [ZMod.card] using this
  have hc : (jwBg D B).card = 2 ^ rk B := by rw [← hcard, hpow]
  rcases (by omega : rk B = 0 ∨ rk B = 1 ∨ rk B = 2) with h0 | h1 | h2
  · right
    rw [hc, h0]
    simpa using hSle
  · right
    rw [hc, h1]
    have h2 : 1 < (jwBg D B).card := by rw [hc, h1]; norm_num
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2
    obtain ⟨δ, hδ, hδ1⟩ : ∃ δ ∈ jwBg D B, δ ≠ 1 := by
      by_cases ha1 : a = 1
      · exact ⟨b, hb, fun h => hab (ha1.trans h.symm)⟩
      · exact ⟨a, ha, ha1⟩
    have hsub : jwS D B ⊆ L3.fixS δ := by
      intro ξ hξ
      simp only [L3.fixS, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (mem_jwS.1 hξ) δ hδ
    have h4 := (Finset.card_le_card hsub).trans (L3F.fixS_card_le δ hδ1)
    norm_num
    omega
  · rcases jw_cases D hBel with hT | hT
    · left
      exact Finset.eq_of_subset_of_card_le hT (by rw [L3F.card_B1, hc, h2]; norm_num)
    · right
      have hTe : jwBg D B = L3F.B2 :=
        Finset.eq_of_subset_of_card_le hT (by rw [L3F.card_B2, hc, h2]; norm_num)
      have hsub : jwS D B ⊆ ({0, L3F.e1} : Finset L3.Vec) := by
        intro ξ hξ
        have := L3F.B2_fix ξ (fun b hb => (mem_jwS.1 hξ) b (by rw [hTe]; exact hb))
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact this
      have h4 : (jwS D B).card ≤ 2 := (Finset.card_le_card hsub).trans Finset.card_le_two
      rw [hc, h2]
      omega

theorem bounds_std [Finite V] (D : L3Data G M C) (hCfix : ∀ g ∈ G, ∀ c ∈ C, g c = c) {m : V}
    (hm : IsLift D m) (hII : ∃ s : L3.Γ, L3F.Ustd s ∧ D.rho s m ≠ m) {B : Subgroup (MulAut V)}
    (hBU : ∀ b ∈ B, ∃ γ : L3.Γ, L3F.Ustd γ ∧ D.rho γ = b) (hBel : IsElemAbelian2 B) :
    Nat.card B * Nat.card ↥(fixV B ⊓ M) ≤ Nat.card M ∧
      Nat.card B ^ 2 * Nat.card ↥(fixV B ⊓ M) * Nat.card ↥(fixMod B M C) ≤ Nat.card M ^ 2 := by
  classical
  have hM8 : Nat.card M = 8 * Nat.card C := D.card_U
  have hB := jw_card_B D hBU
  have hY := jw_card_fixMod D hBU
  have hZY : Nat.card ↥(fixV B ⊓ M) ≤ Nat.card ↥(fixMod B M C) :=
    Subgroup.card_le_of_le (jw_fixV_le B M C)
  have hCpos : 0 < Nat.card C := Nat.card_pos
  rcases jw_claim D hBU hBel with hB1 | hle
  · have hZC : fixV B ⊓ M ≤ C := by
      rintro x ⟨hxB, hxM⟩
      refine fix_B1_le_C D hCfix hm hII x hxM (fun b hb => ?_)
      have hb' : b ∈ jwBg D B := by rw [hB1]; exact hb
      exact (mem_fixV.1 hxB) _ (mem_jwBg.1 hb').2
    have hZ : Nat.card ↥(fixV B ⊓ M) ≤ Nat.card C := Subgroup.card_le_of_le hZC
    have hS : (jwS D B).card = 4 := by
      have : jwS D B = L3F.plane12 := by
        ext ξ
        rw [mem_jwS, hB1]
        constructor
        · intro h
          exact L3F.B1_fix ξ (fun b hb => h b hb)
        · intro h γ hγ
          exact (L3F.mem_B1.1 hγ) ξ h
      rw [this]
      exact L3F.isPlane_plane12.1
    have hB4 : Nat.card B = 4 := by rw [hB, hB1]; exact L3F.card_B1
    rw [hS] at hY
    rw [hB4, hM8, hY]
    constructor
    · omega
    · nlinarith [Nat.mul_le_mul_right (Nat.card C) hZ]
  · have hBY : Nat.card B * Nat.card ↥(fixMod B M C) ≤ Nat.card M := by
      rw [hB, hY, hM8]
      calc (jwBg D B).card * (Nat.card C * (jwS D B).card)
          = Nat.card C * ((jwBg D B).card * (jwS D B).card) := by ring
        _ ≤ Nat.card C * 8 := Nat.mul_le_mul_left _ hle
        _ = 8 * Nat.card C := by ring
    constructor
    · exact (Nat.mul_le_mul_left _ hZY).trans hBY
    · calc Nat.card B ^ 2 * Nat.card ↥(fixV B ⊓ M) * Nat.card ↥(fixMod B M C)
          ≤ Nat.card B ^ 2 * Nat.card ↥(fixMod B M C) * Nat.card ↥(fixMod B M C) :=
            Nat.mul_le_mul (Nat.mul_le_mul le_rfl hZY) le_rfl
        _ = (Nat.card B * Nat.card ↥(fixMod B M C)) ^ 2 := by ring
        _ ≤ Nat.card M ^ 2 := Nat.pow_le_pow_left hBY 2

theorem tight_std [Finite V] (D : L3Data G M C) (hCfix : ∀ g ∈ G, ∀ c ∈ C, g c = c) {m : V}
    (hm : IsLift D m) (hII : ∃ s : L3.Γ, L3F.Ustd s ∧ D.rho s m ≠ m) {B : Subgroup (MulAut V)}
    (hBU : ∀ b ∈ B, ∃ γ : L3.Γ, L3F.Ustd γ ∧ D.rho γ = b) (hBel : IsElemAbelian2 B)
    (ht : Nat.card B * Nat.card ↥(fixV B ⊓ M) = Nat.card M) : ∀ b ∈ B, b m = m := by
  classical
  have hM8 : Nat.card M = 8 * Nat.card C := D.card_U
  have hB := jw_card_B D hBU
  have hY := jw_card_fixMod D hBU
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hBpos : 0 < Nat.card B := Nat.card_pos
  rcases jw_claim D hBU hBel with hB1 | hle
  · exfalso
    have hZC : fixV B ⊓ M ≤ C := by
      rintro x ⟨hxB, hxM⟩
      refine fix_B1_le_C D hCfix hm hII x hxM (fun b hb => ?_)
      have hb' : b ∈ jwBg D B := by rw [hB1]; exact hb
      exact (mem_fixV.1 hxB) _ (mem_jwBg.1 hb').2
    have hZ : Nat.card ↥(fixV B ⊓ M) ≤ Nat.card C := Subgroup.card_le_of_le hZC
    have hB4 : Nat.card B = 4 := by rw [hB, hB1]; exact L3F.card_B1
    rw [hB4, hM8] at ht
    omega
  · have hBY : Nat.card B * Nat.card ↥(fixMod B M C) ≤ Nat.card B * Nat.card ↥(fixV B ⊓ M) := by
      rw [ht, hB, hY, hM8]
      calc (jwBg D B).card * (Nat.card C * (jwS D B).card)
          = Nat.card C * ((jwBg D B).card * (jwS D B).card) := by ring
        _ ≤ Nat.card C * 8 := Nat.mul_le_mul_left _ hle
        _ = 8 * Nat.card C := by ring
    have hYZ : Nat.card ↥(fixMod B M C) ≤ Nat.card ↥(fixV B ⊓ M) :=
      Nat.le_of_mul_le_mul_left hBY hBpos
    have hEq : fixV B ⊓ M = fixMod B M C :=
      Subgroup.eq_of_le_of_card_ge (jw_fixV_le B M C) hYZ
    obtain ⟨hmM, hβm⟩ := hm
    have hmY : m ∈ fixMod B M C := by
      rw [mem_fixMod]
      refine ⟨hmM, fun b hb => ?_⟩
      obtain ⟨γ, hγ, rfl⟩ := hBU b hb
      exact lift_comm_mem D ⟨hmM, hβm⟩ hγ.1
    rw [← hEq] at hmY
    intro b hb
    exact (mem_fixV.1 hmY.1) b hb

end Std

end CFSG.Quasithin.C116Three
