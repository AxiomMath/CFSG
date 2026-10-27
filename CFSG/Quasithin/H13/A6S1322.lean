module

public import CFSG.Quasithin.H13.A6S134V1
public import CFSG.Quasithin.H13.A6S1342
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.A5Setting

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem exists_even_inW1 : ∀ x : P6, x ∈ G6.coreMod 6 → x ≠ 1 →
    ∃ σ : Perm (Fin 6), Equiv.Perm.sign σ = 1 ∧ InW1 (G6.permAct 6 σ x) := by
  intro x hx
  rw [G6.mem_coreMod] at hx
  revert x
  decide +kernel

namespace Setting134

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting134 G T L V)
include S

theorem psi_ne_one {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) : (S.frame.ψ ⟨v, hv⟩ : P6) ≠ 1 := by
  intro h
  apply hv1
  have h1 : S.frame.ψ ⟨v, hv⟩ = S.frame.ψ 1 := by
    rw [map_one]
    exact Subtype.ext h
  exact congrArg Subtype.val (S.frame.ψ.injective h1)

theorem psi_conj_val (g : ↥(Subgroup.normalizer (V : Set G))) {v : G} (hv : v ∈ V) :
    (S.frame.ψ ⟨(g : G) * v * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 v).mp hv⟩ : P6) =
      G6.permAct 6 (S.frame.ρ g) (S.frame.ψ ⟨v, hv⟩ : P6) := by
  rw [S.psi_conj g ⟨v, hv⟩, G6.coreAct_coe]

theorem conj_eq_of_rho_eq {g h : ↥(Subgroup.normalizer (V : Set G))}
    (hgh : S.frame.ρ g = S.frame.ρ h) {v : G} (hv : v ∈ V) :
    (g : G) * v * (g : G)⁻¹ = (h : G) * v * (h : G)⁻¹ := by
  have h1 := S.psi_conj g ⟨v, hv⟩
  have h2 := S.psi_conj h ⟨v, hv⟩
  rw [hgh, ← h2] at h1
  exact congrArg Subtype.val (S.frame.ψ.injective h1)

theorem exists_conj_mem_V1 {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    ∃ l ∈ L, l * v * l⁻¹ ∈ fsuV1 T V := by
  obtain ⟨σ, hσ, hW⟩ := exists_even_inW1 _ (S.frame.ψ ⟨v, hv⟩).2 (S.psi_ne_one hv hv1)
  obtain ⟨g, hgL, hgσ⟩ := (S.frame.image_L σ).2 (Equiv.Perm.mem_alternatingGroup.2 hσ)
  refine ⟨g, hgL, S.mem_V1_iff.2 ⟨(Subgroup.mem_normalizer_iff.mp g.2 v).mp hv, ?_⟩⟩
  rw [S.psi_conj_val g hv, hgσ]
  exact hW

omit [Finite G] S in
theorem V1_le_center (x : G) (hx : x ∈ fsuV1 T V) :
    x ∈ T ∧ x ∈ Subgroup.centralizer (T : Set G) := by
  obtain ⟨h1, h2, -⟩ := mem_quasithinOmegaOneCenter_iff.1 hx.2
  exact ⟨h1, h2⟩

theorem exists_odd_T {m : ↥(Subgroup.normalizer (V : Set G))}
    (hm : Equiv.Perm.sign (S.frame.ρ m) ≠ 1) :
    ∃ t : ↥(Subgroup.normalizer (V : Set G)), (t : G) ∈ T ∧
      Equiv.Perm.sign (S.frame.ρ t) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  let φ : ↥(Subgroup.normalizer (V : Set G)) →* ℤˣ := Equiv.Perm.sign.comp S.frame.ρ
  have hTk : T.subgroupOf (Subgroup.normalizer (V : Set G)) ≤ φ.ker := fun t ht =>
    hcon t ht
  have hsurj : Function.Surjective φ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one φ⟩
    · refine ⟨m, ?_⟩
      rcases Int.units_eq_one_or (φ m) with h | h
      · exact absurd h hm
      · exact h
  have hidx : φ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hsyl := A5.isSylowTwoOf_of_le S.h13.sylow S.frame.T_le
  apply hsyl.2.2
  rw [← hidx]
  exact Subgroup.index_dvd_of_le hTk

theorem exists_act_eq (m : ↥(Subgroup.normalizer (V : Set G))) :
    ∃ h ∈ L ⊔ T, ∀ v ∈ V, (m : G) * v * (m : G)⁻¹ = h * v * h⁻¹ := by
  by_cases hm : Equiv.Perm.sign (S.frame.ρ m) = 1
  · obtain ⟨g, hgL, hgσ⟩ := (S.frame.image_L (S.frame.ρ m)).2
      (Equiv.Perm.mem_alternatingGroup.2 hm)
    exact ⟨g, le_sup_left (a := L) hgL, fun v hv => S.conj_eq_of_rho_eq hgσ.symm hv⟩
  · obtain ⟨t, htT, ht⟩ := S.exists_odd_T hm
    have heven : Equiv.Perm.sign (S.frame.ρ (m * t⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_inv]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (S.frame.ρ m)) with h1 | h1
      · exact absurd h1 hm
      · rcases Int.units_eq_one_or (Equiv.Perm.sign (S.frame.ρ t)) with h2 | h2
        · exact absurd h2 ht
        · rw [h1, h2]
          exact mul_inv_cancel _
    obtain ⟨g, hgL, hgσ⟩ := (S.frame.image_L (S.frame.ρ (m * t⁻¹))).2
      (Equiv.Perm.mem_alternatingGroup.2 heven)
    refine ⟨(g : G) * t, (L ⊔ T).mul_mem (le_sup_left (a := L) hgL) (le_sup_right (b := T) htT),
      fun v hv => ?_⟩
    have hρ : S.frame.ρ m = S.frame.ρ (g * t) := by
      rw [map_mul, hgσ, map_mul, map_inv, inv_mul_cancel_right]
    rw [S.conj_eq_of_rho_eq hρ hv, Subgroup.coe_mul]

theorem lemma13_2_2_five (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {v w : G} (hv : v ∈ V)
    (hw : w ∈ V) {g : G} (hg : g⁻¹ * v * g = w) : ∃ h ∈ L ⊔ T, h⁻¹ * v * h = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hv1 : v = 1
  · subst hv1
    refine ⟨1, (L ⊔ T).one_mem, ?_⟩
    rw [← hg]
    group
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hv1
    have : v = g * 1 * g⁻¹ := by rw [← hg]; group
    rw [this]
    group
  obtain ⟨l₁, hl₁L, hl₁⟩ := S.exists_conj_mem_V1 hv hv1
  obtain ⟨l₂, hl₂L, hl₂⟩ := S.exists_conj_mem_V1 hw hw1
  let P : Sylow 2 G := IsPGroup.toSylow S.h13.sylow.1 S.h13.sylow.2
  have hPT : (P : Subgroup G) = T := rfl
  have hv' : l₁ * v * l₁⁻¹ ∈ Subgroup.centralizer (P : Set G) := (V1_le_center _ hl₁).2
  have hw' : l₂ * w * l₂⁻¹ ∈ Subgroup.centralizer (P : Set G) := (V1_le_center _ hl₂).2
  have hk : (l₁ * g * l₂⁻¹)⁻¹ * (l₁ * v * l₁⁻¹) * (l₁ * g * l₂⁻¹) = l₂ * w * l₂⁻¹ := by
    rw [← hg]
    group
  obtain ⟨n, hn, hn'⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer P (l₁ * v * l₁⁻¹)
    (l₁ * g * l₂⁻¹) hv' (by rw [hk]; exact hw')
  rw [hk] at hn'
  have hnM : n ∈ Subgroup.normalizer (V : Set G) := by
    have hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (L : Set G) :=
      (h331 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow).1 _ L S.uniqueM.1.1
        S.T_le_NL S.maximal Subgroup.le_normalizer S.fsu.quasisimple
    exact S.normalizer_L_le h1222 (hNT hn)
  obtain ⟨h, hh, hhv⟩ := S.exists_act_eq ⟨n⁻¹, (Subgroup.normalizer (V : Set G)).inv_mem hnM⟩
  have hv'V : l₁ * v * l₁⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (S.frame.L_le hl₁L) v).mp hv
  have h1 := hhv _ hv'V
  simp only [inv_inv] at h1
  refine ⟨l₁⁻¹ * h⁻¹ * l₂, ?_, ?_⟩
  · exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((L ⊔ T).inv_mem (le_sup_left (a := L) hl₁L))
      ((L ⊔ T).inv_mem hh)) (le_sup_left (a := L) hl₂L)
  · have h2 : h * (l₁ * v * l₁⁻¹) * h⁻¹ = l₂ * w * l₂⁻¹ := by rw [← h1, hn']
    calc (l₁⁻¹ * h⁻¹ * l₂)⁻¹ * v * (l₁⁻¹ * h⁻¹ * l₂) =
        l₂⁻¹ * (h * (l₁ * v * l₁⁻¹) * h⁻¹) * l₂ := by group
      _ = l₂⁻¹ * (l₂ * w * l₂⁻¹) * l₂ := by rw [h2]
      _ = w := by group

end Setting134

end CFSG.Quasithin.H13.A6
