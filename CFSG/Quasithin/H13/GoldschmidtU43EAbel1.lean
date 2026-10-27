module

public import CFSG.Quasithin.H13.GoldschmidtU43EExcl2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem normalizes_sup {A B : Subgroup G} {g : G} (hA : ∀ x, x ∈ A ↔ g * x * g⁻¹ ∈ A)
    (hB : ∀ x, x ∈ B ↔ g * x * g⁻¹ ∈ B) (x : G) :
    x ∈ A ⊔ B ↔ g * x * g⁻¹ ∈ A ⊔ B := by
  have hmap : (A ⊔ B).map (MulAut.conj g).toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup]
    have h1 : A.map (MulAut.conj g).toMonoidHom = A := by
      ext y
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (hA w).1 hw
      · intro hy
        refine ⟨g⁻¹ * y * g, ?_, by simp [MulAut.conj_apply]; group⟩
        rw [hA]
        have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        rw [this]
        exact hy
    have h2 : B.map (MulAut.conj g).toMonoidHom = B := by
      ext y
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (hB w).1 hw
      · intro hy
        refine ⟨g⁻¹ * y * g, ?_, by simp [MulAut.conj_apply]; group⟩
        rw [hB]
        have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        rw [this]
        exact hy
    rw [h1, h2]
  constructor
  · intro hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hmap] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    have : w = x := by
      have : g * w * g⁻¹ = g * x * g⁻¹ := hwx
      simpa using this
    rwa [← this]

theorem normalizes_inf_centralizer {K : Subgroup G} {g y : G} (hK : ∀ x, x ∈ K ↔ g * x * g⁻¹ ∈ K)
    (hy : g * y = y * g) (x : G) :
    x ∈ K ⊓ Subgroup.centralizer ({y} : Set G) ↔
      g * x * g⁻¹ ∈ K ⊓ Subgroup.centralizer ({y} : Set G) := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hK x, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y)) := by group
      _ = g * (x * (y * g⁻¹)) := by rw [show g⁻¹ * y = y * g⁻¹ by
            calc g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
              _ = g⁻¹ * (g * y) * g⁻¹ := by rw [hy]
              _ = y * g⁻¹ := by group]
      _ = g * (y * x) * g⁻¹ := by rw [← mul_assoc x y, h]; group
      _ = y * (g * x * g⁻¹) := by
          calc g * (y * x) * g⁻¹ = (g * y) * x * g⁻¹ := by group
            _ = (y * g) * x * g⁻¹ := by rw [hy]
            _ = y * (g * x * g⁻¹) := by group
  · have h' : g * x * g⁻¹ * y = y * (g * x * g⁻¹) := h
    calc x * y = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * (y * g * g⁻¹)) * g := by rw [hy]
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [h']
      _ = y * x := by
          calc g⁻¹ * (y * (g * x * g⁻¹)) * g = (g⁻¹ * y * g) * x := by group
            _ = y * x := by
                rw [show g⁻¹ * y * g = y by
                  calc g⁻¹ * y * g = g⁻¹ * (y * g) := by group
                    _ = g⁻¹ * (g * y) := by rw [hy]
                    _ = y := by group]

namespace JWSetup

variable {z : G} (S : JWSetup z)
include S

@[expose] noncomputable def T1 [Finite G] : Subgroup G :=
  S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G)

@[expose] noncomputable def T2 [Finite G] : Subgroup G :=
  S.Mg ⊓ Subgroup.centralizer ({z * (S.u : G)} : Set G)

theorem z_normalizes_Tg (x : G) : x ∈ S.Tg ↔ z * x * z⁻¹ ∈ S.Tg :=
  Subgroup.mem_normalizer_iff.mp S.z_normalizer_Tg x

theorem u_normalizes_Tg (x : G) : x ∈ S.Tg ↔ (S.u : G) * x * (S.u : G)⁻¹ ∈ S.Tg :=
  Subgroup.mem_normalizer_iff.mp S.u_normalizer_Tg x

variable [Finite G]

theorem card_T1 : Nat.card S.T1 = 9 := by
  have h := S.card_Mg_eq
  rw [S.card_Mg_eq_81] at h
  have : Nat.card S.T1 =
      Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G)) := rfl
  rw [this]
  have h9 : Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G)) ^ 2 = 9 ^ 2 := by
    rw [← h]
    norm_num
  exact (Nat.pow_left_injective (by norm_num)) h9

theorem card_T2 : Nat.card S.T2 = 9 := by
  have : Nat.card S.T2 =
      Nat.card ↥(S.Mg ⊓ Subgroup.centralizer ({z * (S.u : G)} : Set G)) := rfl
  rw [this, S.card_CMzu]
  exact S.card_T1

theorem T1_le_Mg : S.T1 ≤ S.Mg := inf_le_left

theorem T2_le_Mg : S.T2 ≤ S.Mg := inf_le_left

theorem Mg_inf_cent_z : S.Mg ⊓ Subgroup.centralizer ({z} : Set G) = S.Tg := S.Mg_inf_Hz

theorem z_normalizes_Mg (x : G) : x ∈ S.Mg ↔ z * x * z⁻¹ ∈ S.Mg :=
  S.normalizer_Mg_iff S.z_normalizer_Tg x

theorem u_normalizes_Mg (x : G) : x ∈ S.Mg ↔ (S.u : G) * x * (S.u : G)⁻¹ ∈ S.Mg :=
  S.normalizer_Mg_iff S.u_normalizer_Tg x

theorem Mg_eq_sup : S.Tg ⊔ S.T1 ⊔ S.T2 = S.Mg := by
  set X := S.Tg ⊔ S.T1 ⊔ S.T2 with hX
  have hXM : X ≤ S.Mg := sup_le (sup_le S.Tg_le_Mg S.T1_le_Mg) S.T2_le_Mg
  have hTX : S.Tg ≤ X := le_sup_left.trans le_sup_left
  have h1X : S.T1 ≤ X := le_sup_right.trans le_sup_left
  have h2X : S.T2 ≤ X := le_sup_right
  have hzu : (z : G) * (S.u : G) = (S.u : G) * z := S.u_comm_z.eq
  have hzT1 : ∀ x, x ∈ S.T1 ↔ z * x * z⁻¹ ∈ S.T1 :=
    normalizes_inf_centralizer S.z_normalizes_Mg hzu
  have hzT2 : ∀ x, x ∈ S.T2 ↔ z * x * z⁻¹ ∈ S.T2 :=
    normalizes_inf_centralizer S.z_normalizes_Mg (by
      calc z * (z * (S.u : G)) = z * ((S.u : G) * z) := by rw [hzu]
        _ = z * (S.u : G) * z := by group)
  have huT1 : ∀ x, x ∈ S.T1 ↔ (S.u : G) * x * (S.u : G)⁻¹ ∈ S.T1 :=
    normalizes_inf_centralizer S.u_normalizes_Mg rfl
  have huT2 : ∀ x, x ∈ S.T2 ↔ (S.u : G) * x * (S.u : G)⁻¹ ∈ S.T2 :=
    normalizes_inf_centralizer S.u_normalizes_Mg (by
      calc (S.u : G) * (z * (S.u : G)) = ((S.u : G) * z) * (S.u : G) := by group
        _ = (z * (S.u : G)) * (S.u : G) := by rw [← hzu])
  have hzX : ∀ x, x ∈ X ↔ z * x * z⁻¹ ∈ X :=
    normalizes_sup (normalizes_sup S.z_normalizes_Tg hzT1) hzT2
  have huX : ∀ x, x ∈ X ↔ (S.u : G) * x * (S.u : G)⁻¹ ∈ X :=
    normalizes_sup (normalizes_sup S.u_normalizes_Tg huT1) huT2
  have hodd : Odd (Nat.card X) := Odd.of_dvd_nat S.odd_card_Mg (Subgroup.card_dvd_of_le hXM)
  have hW := CFSG.Walter.J1.card_mul_card_sq_eq_mul S.z_sq S.u_sq S.hyp.z_ne_one S.u_ne_one
    S.u_ne_z.symm S.u_comm_z X (Subgroup.mem_normalizer_iff.mpr hzX)
    (Subgroup.mem_normalizer_iff.mpr huX) hodd
  have eZ : X ⊓ Subgroup.centralizer ({z} : Set G) = S.Tg := by
    apply le_antisymm
    · rintro x ⟨hx, hxz⟩
      rw [← S.Mg_inf_cent_z]
      exact ⟨hXM hx, hxz⟩
    · exact le_inf hTX S.Tg_le_Hz
  have eU : X ⊓ Subgroup.centralizer ({(S.u : G)} : Set G) = S.T1 := by
    apply le_antisymm
    · rintro x ⟨hx, hxu⟩
      exact ⟨hXM hx, hxu⟩
    · exact le_inf h1X inf_le_right
  have eZU : X ⊓ Subgroup.centralizer ({z * (S.u : G)} : Set G) = S.T2 := by
    apply le_antisymm
    · rintro x ⟨hx, hxu⟩
      exact ⟨hXM hx, hxu⟩
    · exact le_inf h2X inf_le_right
  rw [eZ, eU, eZU, S.card_Tg, S.card_T1, S.card_T2, S.card_Tg_inf_u] at hW
  have h81 : Nat.card X = 81 := by omega
  exact Subgroup.eq_of_le_of_card_ge hXM (by rw [h81, S.card_Mg_eq_81])

end JWSetup

end CFSG.Quasithin.H13.U43
