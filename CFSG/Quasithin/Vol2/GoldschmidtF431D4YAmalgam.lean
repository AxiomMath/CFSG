module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4OverB
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocV
public import CFSG.Quasithin.Recognition.CertTwoLocal

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.D4Hex
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

set_option linter.unusedSectionVars false


section Elements

theorem g7_mem_N : d4GenG 7 ∈ d4N := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := ovZeta_parts
  exact mem_d4N_of_rep (act_gen (j := 7) (by norm_num)) h10

theorem g7_not_mem_H : d4GenG 7 ∉ d4H := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := ovZeta_parts
  intro h
  apply h9
  have h0 := (mem_d4H_iff_act _).1 h
  have h1 : (permArrs[7]!)[0]! = ((act (d4GenG 7) pt0 : Fin 819) : ℕ) :=
    (act_gen (j := 7) (by norm_num)) pt0
  rw [h0] at h1
  exact h1

theorem g3_mem_H : d4GenG 3 ∈ d4H := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := ovZeta_parts
  exact mem_d4H_of_rep (act_gen (j := 3) (by norm_num)) h11

theorem pt0_mem_base_line : pt0 ∈ line0 :=
  Finset.mem_insert_self _ _

theorem pt1_mem_base_line : (⟨1, by norm_num⟩ : Fin 819) ∈ line0 :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem pt5_mem_base_line : (⟨5, by norm_num⟩ : Fin 819) ∈ line0 :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem perm3_aux (x0 x1 x5 a0 a1 a5 : ℕ) (c0 : x0 = 0 ∨ x0 = 1 ∨ x0 = 5)
    (c1 : x1 = 0 ∨ x1 = 1 ∨ x1 = 5) (c5 : x5 = 0 ∨ x5 = 1 ∨ x5 = 5) (d01 : x0 ≠ x1)
    (d05 : x0 ≠ x5) (d15 : x1 ≠ x5) (v0 : x0 = a0) (v1 : x1 = a1) (v5 : x5 = a5) :
    (a0 = 0 ∧ a1 = 1 ∧ a5 = 5) ∨ (a0 = 0 ∧ a1 = 5 ∧ a5 = 1) ∨ (a0 = 1 ∧ a1 = 0 ∧ a5 = 5) ∨
      (a0 = 1 ∧ a1 = 5 ∧ a5 = 0) ∨ (a0 = 5 ∧ a1 = 0 ∧ a5 = 1) ∨ (a0 = 5 ∧ a1 = 1 ∧ a5 = 0) := by
  subst v0 v1 v5
  rcases c0 with h0 | h0 | h0 <;> rcases c1 with h1 | h1 | h1 <;>
    rcases c5 with h5 | h5 | h5 <;> simp_all

theorem fixesLine0_of_mem_d4N {g : D} {a : Array ℕ} (hr : Rep 819 a (act g)) (hg : g ∈ d4N) :
    fixesLine0 a = true := by
  have himg := (mem_d4N_iff_image g).1 hg
  have key : ∀ p : Fin 819, p ∈ line0 →
      ((act g p : Fin 819) : ℕ) = 0 ∨ ((act g p : Fin 819) : ℕ) = 1 ∨
        ((act g p : Fin 819) : ℕ) = 5 := by
    intro p hp
    have : act g p ∈ line0 := by
      rw [← himg]
      exact Finset.mem_image_of_mem _ hp
    simp only [line0, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at this
    exact this
  have c0 := key _ pt0_mem_base_line
  have c1 := key _ pt1_mem_base_line
  have c5 := key _ pt5_mem_base_line
  have inj := (act g).injective
  have v0 : ((act g pt0 : Fin 819) : ℕ) = a[0]! := (hr pt0).symm
  have v1 : ((act g (⟨1, by norm_num⟩ : Fin 819) : Fin 819) : ℕ) = a[1]! :=
    (hr ⟨1, by norm_num⟩).symm
  have v5 : ((act g (⟨5, by norm_num⟩ : Fin 819) : Fin 819) : ℕ) = a[5]! :=
    (hr ⟨5, by norm_num⟩).symm
  have d01 : ((act g pt0 : Fin 819) : ℕ) ≠ ((act g (⟨1, by norm_num⟩ : Fin 819) : Fin 819) : ℕ) :=
    fun h => by
      have := inj (Fin.ext h)
      simp [pt0] at this
  have d05 : ((act g pt0 : Fin 819) : ℕ) ≠ ((act g (⟨5, by norm_num⟩ : Fin 819) : Fin 819) : ℕ) :=
    fun h => by
      have := inj (Fin.ext h)
      simp [pt0, Fin.ext_iff] at this
  have d15 : ((act g (⟨1, by norm_num⟩ : Fin 819) : Fin 819) : ℕ) ≠
      ((act g (⟨5, by norm_num⟩ : Fin 819) : Fin 819) : ℕ) := fun h => by
    have := inj (Fin.ext h)
    simp [Fin.ext_iff] at this
  have hperm := perm3_aux _ _ _ _ _ _ c0 c1 c5 d01 d05 d15 v0 v1 v5
  rcases hperm with ⟨h0, h1, h5⟩ | ⟨h0, h1, h5⟩ | ⟨h0, h1, h5⟩ | ⟨h0, h1, h5⟩ | ⟨h0, h1, h5⟩ |
    ⟨h0, h1, h5⟩ <;> simp [fixesLine0, sortKey, lineKey, h0, h1, h5]

theorem g3_not_mem_N : d4GenG 3 ∉ d4N := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12⟩ := ovZeta_parts
  intro h
  have := fixesLine0_of_mem_d4N (act_gen (j := 3) (by norm_num)) h
  rw [h12] at this
  exact absurd this (by decide)

end Elements

section Strict

theorem d4H_ne_d4B : d4H ≠ d4B := fun h =>
  g3_not_mem_N (Subgroup.mem_inf.1 (h ▸ g3_mem_H : d4GenG 3 ∈ d4B)).2

theorem d4N_ne_d4B : d4N ≠ d4B := fun h =>
  g7_not_mem_H (Subgroup.mem_inf.1 (h ▸ g7_mem_N : d4GenG 7 ∈ d4B)).1

theorem d4H_ne_d4N : d4H ≠ d4N := fun h => g3_not_mem_N (h ▸ g3_mem_H)

theorem not_d4H_le_d4N : ¬ d4H ≤ d4N := fun h => g3_not_mem_N (h g3_mem_H)

theorem not_d4N_le_d4H : ¬ d4N ≤ d4H := fun h => g7_not_mem_H (h g7_mem_N)

theorem d4B_le_d4H : d4B ≤ d4H := inf_le_left

theorem d4B_le_d4N : d4B ≤ d4N := inf_le_right

variable (hs : IsSimpleGroup D)
include hs

theorem d4_hNN : ∀ g : D, (∀ x, x ∈ d4N ↔ g * x * g⁻¹ ∈ d4N) → g ∈ d4N := by
  intro g hg
  have hgM : g ∈ Subgroup.normalizer (d4N : Set D) := Subgroup.mem_normalizer_iff.2 hg
  have hNM : d4N ≤ Subgroup.normalizer (d4N : Set D) := Subgroup.le_normalizer
  rcases d4_lattice _ (d4B_le_d4N.trans hNM) with h | h | h | h
  · exact absurd (h ▸ hNM) (fun hle => d4N_ne_d4B (le_antisymm (h ▸ hNM) d4B_le_d4N))
  · exact absurd (h ▸ hNM) not_d4N_le_d4H
  · rw [h] at hgM
    exact hgM
  · exfalso
    have hnorm : d4N.Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases hs.eq_bot_or_eq_top_of_normal d4N with h1 | h1
    · have : d4GenG 7 = 1 := by
        have := g7_mem_N
        rw [h1] at this
        exact this
      exact g7_not_mem_H (this ▸ one_mem _)
    · exact g3_not_mem_N (h1 ▸ Subgroup.mem_top _)

theorem d4_hHH :
    ∀ g : D, (∀ x, x ∈ d4H ↔ g * x * g⁻¹ ∈ d4H) → g ∈ d4H := by
  intro g hg
  have hzH : d4z ∈ d4H := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hw : g * d4z * g⁻¹ ∈ d4H := (hg d4z).1 hzH
  have hcent : ∀ h ∈ d4H, h * (g * d4z * g⁻¹) = (g * d4z * g⁻¹) * h := by
    intro h hh
    have h1 : g⁻¹ * h * g ∈ d4H := by
      refine (hg _).2 ?_
      have : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
      rw [this]
      exact hh
    have hc : (g⁻¹ * h * g) * d4z = d4z * (g⁻¹ * h * g) :=
      Subgroup.mem_centralizer_singleton_iff.1
        (show g⁻¹ * h * g ∈ Subgroup.centralizer {d4z} from h1)
    calc h * (g * d4z * g⁻¹) = g * ((g⁻¹ * h * g) * d4z) * g⁻¹ := by group
      _ = g * (d4z * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc]
      _ = (g * d4z * g⁻¹) * h := by group
  rcases d4_hZH hs _ hw hcent with h1 | h1
  · exfalso
    apply d4z_sq.2
    have : d4z = g⁻¹ * (g * d4z * g⁻¹) * g := by group
    rw [this, h1]
    simp
  · exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h1)

end Strict

section TwoLocal

theorem mem_zpowers_involution {G : Type*} [Group G] {z x : G} (hz : z * z = 1) :
    x ∈ Subgroup.zpowers z ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, zpow_two, hz, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, hz, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

theorem d4H_eq_normalizer_zpowers :
    d4H = Subgroup.normalizer (Subgroup.zpowers d4z : Set D) := by
  have hz := d4z_sq
  ext g
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hg h
    have hc : g * d4z = d4z * g :=
      Subgroup.mem_centralizer_singleton_iff.1 (show g ∈ Subgroup.centralizer {d4z} from hg)
    have hgz : g * d4z * g⁻¹ = d4z := by rw [hc]; group
    have hgz' : g⁻¹ * d4z * g = d4z := by rw [mul_assoc, ← hc]; group
    rw [mem_zpowers_involution hz.1, mem_zpowers_involution hz.1]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl (by simp)
      · exact Or.inr hgz
    · rintro (h1 | h1)
      · left
        have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
        rw [this, h1]
        group
      · right
        have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
        rw [this, h1, hgz']
  · intro hg
    have h1 := (hg d4z).1 (Subgroup.mem_zpowers _)
    rw [mem_zpowers_involution hz.1] at h1
    rcases h1 with h1 | h1
    · exact absurd (by simpa using h1) hz.2
    · exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h1)

theorem d4H_isTwoLocal : IsTwoLocal d4H := by
  refine ⟨Subgroup.zpowers d4z, ?_, ?_, d4H_eq_normalizer_zpowers⟩
  · intro h
    have : d4z ∈ Subgroup.zpowers d4z := Subgroup.mem_zpowers _
    rw [h] at this
    exact d4z_sq.2 this
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_d4z]; rfl)

theorem zElt_ne_one (p : Fin 819) : zElt p ≠ 1 := by
  obtain ⟨g, hg⟩ := exists_smul_pt0_eq p
  have h := zElt_act g pt0
  rw [zElt_zero, ← smul_pt_def, hg] at h
  rw [h]
  intro h1
  have : d4z = 1 := by
    have := congrArg (fun x => g⁻¹ * x * g) h1
    simpa [mul_assoc] using this
  exact d4z_sq.2 this

theorem zElt_mem_V {p : Fin 819} (hp : p ∈ line0) : zElt p ∈ d4V := by
  simp only [line0, Finset.mem_insert, Finset.mem_singleton] at hp
  rw [mem_d4V_iff]
  rcases hp with rfl | rfl | rfl
  · exact Or.inr (Or.inl zElt_zero)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem mem_line0_of_zElt_mem_V {p : Fin 819} (hp : zElt p ∈ d4V) : p ∈ line0 := by
  rw [mem_d4V_iff] at hp
  rcases hp with h | h | h | h
  · exact absurd h (zElt_ne_one p)
  · have : p = pt0 := zElt_injective (h.trans zElt_zero.symm)
    rw [this]
    exact pt0_mem_base_line
  · have : p = pt1 := zElt_injective h
    rw [this]
    exact pt1_mem_base_line
  · have : p = pt5 := zElt_injective h
    rw [this]
    exact pt5_mem_base_line

theorem d4N_eq_normalizer_V :
    d4N = Subgroup.normalizer (d4V : Set D) := by
  have : Finite D := finite_D'
  ext g
  constructor
  · intro hg
    apply Subgroup.mem_normalizer_fintype
    intro v hv
    have himg := (mem_d4N_iff_image g).1 hg
    have hmem : ∀ p ∈ line0, act g p ∈ line0 := fun p hp => by
      rw [← himg]
      exact Finset.mem_image_of_mem _ hp
    rcases mem_d4V_iff.1 hv with rfl | rfl | rfl | rfl
    · simp
    · have h := zElt_act g pt0
      rw [zElt_zero] at h
      show g * d4z * g⁻¹ ∈ d4V
      rw [← h]
      exact zElt_mem_V (hmem _ pt0_mem_base_line)
    · have h := zElt_act g pt1
      show g * zElt pt1 * g⁻¹ ∈ d4V
      rw [← h]
      exact zElt_mem_V (hmem _ pt1_mem_base_line)
    · have h := zElt_act g pt5
      show g * zElt pt5 * g⁻¹ ∈ d4V
      rw [← h]
      exact zElt_mem_V (hmem _ pt5_mem_base_line)
  · intro hg
    have hnorm := Subgroup.mem_normalizer_iff.1 hg
    have key : ∀ p ∈ line0, act g p ∈ line0 := fun p hp => by
      apply mem_line0_of_zElt_mem_V
      rw [zElt_act]
      exact (hnorm _).1 (zElt_mem_V hp)
    rw [mem_d4N_iff_image]
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hr
      exact key q hq
    · rw [Finset.card_image_of_injective _ (act g).injective]

theorem d4N_isTwoLocal : IsTwoLocal d4N := by
  refine ⟨d4V, ?_, ?_, d4N_eq_normalizer_V⟩
  · intro h
    have : d4z ∈ d4V := (mem_d4V_iff).2 (Or.inr (Or.inl rfl))
    rw [h] at this
    exact d4z_sq.2 this
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 2) (by rw [card_d4V]; rfl)

end TwoLocal

section Pair

variable (hs : IsSimpleGroup D)
include hs

theorem d4_not_twoLocal_top : ¬ IsTwoLocal (⊤ : Subgroup D) := by
  rintro ⟨P, hP, hPp, hPeq⟩
  have : Finite D := finite_D'
  have hnorm : P.Normal := Subgroup.normalizer_eq_top_iff.1 hPeq.symm
  rcases hs.eq_bot_or_eq_top_of_normal P with h | h
  · exact hP h
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    subst h
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [Subgroup.card_top, card_trialityGroup8] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3)
    omega

theorem d4H_isMaximalTwoLocal : IsMaximalTwoLocal d4H := by
  refine ⟨d4H_isTwoLocal, fun M hM hle => ?_⟩
  rcases d4_lattice M (d4B_le_d4H.trans hle) with h | h | h | h
  · exact absurd (le_antisymm (h ▸ hle) d4B_le_d4H) d4H_ne_d4B
  · exact h
  · exact absurd (h ▸ hle) not_d4H_le_d4N
  · rw [h] at hM
    exact absurd hM (d4_not_twoLocal_top hs)

theorem d4N_isMaximalTwoLocal : IsMaximalTwoLocal d4N := by
  refine ⟨d4N_isTwoLocal, fun M hM hle => ?_⟩
  rcases d4_lattice M (d4B_le_d4N.trans hle) with h | h | h | h
  · exact absurd (le_antisymm (h ▸ hle) d4B_le_d4N) d4N_ne_d4B
  · exact absurd (h ▸ hle) not_d4N_le_d4H
  · exact h
  · rw [h] at hM
    exact absurd hM (d4_not_twoLocal_top hs)

theorem d4_isYAmalgamPair :
    IsYAmalgamPair d4U d4H d4N := by
  refine ⟨d4_sylow, d4H_ne_d4N, fun M => ⟨?_, ?_⟩⟩
  · rintro ⟨hM, hle⟩
    rw [normalizer_d4U_eq_d4B hs] at hle
    rcases d4_lattice M hle with h | h | h | h
    · exfalso
      have hH := hM.2 d4H d4H_isTwoLocal (by rw [h]; exact d4B_le_d4H)
      rw [h] at hH
      exact d4H_ne_d4B hH
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at hM
      exact absurd hM.1 (d4_not_twoLocal_top hs)
  · rintro (rfl | rfl)
    · exact ⟨d4H_isMaximalTwoLocal hs, by rw [normalizer_d4U_eq_d4B hs]; exact d4B_le_d4H⟩
    · exact ⟨d4N_isMaximalTwoLocal hs, by rw [normalizer_d4U_eq_d4B hs]; exact d4B_le_d4N⟩

omit hs in
theorem exists_conj_sylow [Finite D] {S₁ S₂ : Subgroup D} (h₁ : IsSylowTwoOf S₁ ⊤)
    (h₂ : IsSylowTwoOf S₂ ⊤) : ∃ g : D, S₁.map (MulAut.conj g).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ S : Subgroup D, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P₁ : Sylow 2 D := h₁.2.1.toSylow (hidx S₁ h₁)
  let P₂ : Sylow 2 D := h₂.2.1.toSylow (hidx S₂ h₂)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 D => (T : Subgroup D)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h

theorem d4_yamalgam_classify
    {T P₁ P₂ : Subgroup D} (h : IsYAmalgamPair T P₁ P₂) :
    ∃ x : D, T.map (MulAut.conj x).toMonoidHom = d4U ∧
      ((P₁.map (MulAut.conj x).toMonoidHom = d4H ∧ P₂.map (MulAut.conj x).toMonoidHom = d4N) ∨
        (P₁.map (MulAut.conj x).toMonoidHom = d4N ∧
          P₂.map (MulAut.conj x).toMonoidHom = d4H)) := by
  have : Finite D := finite_D'
  obtain ⟨x, hx⟩ := exists_conj_sylow h.1 d4_sylow
  refine ⟨x, hx, ?_⟩
  have hmap := IsYAmalgamPair.map (MulAut.conj x) h
  rw [hx] at hmap
  obtain ⟨-, hne, hiff⟩ := hmap
  have h1 := (hiff (P₁.map (MulAut.conj x).toMonoidHom)).2 (Or.inl rfl)
  have h2 := (hiff (P₂.map (MulAut.conj x).toMonoidHom)).2 (Or.inr rfl)
  have hY := d4_isYAmalgamPair hs
  have h1' := (hY.2.2 _).1 h1
  have h2' := (hY.2.2 _).1 h2
  rcases h1' with e1 | e1 <;> rcases h2' with e2 | e2
  · exact absurd (e1.trans e2.symm) hne
  · exact Or.inl ⟨e1, e2⟩
  · exact Or.inr ⟨e1, e2⟩
  · exact absurd (e1.trans e2.symm) hne

end Pair

end CFSG.Quasithin.D4Hex
