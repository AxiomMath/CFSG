module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec2
public import CFSG.Quasithin.Vol2.Asc94.He42PData
public import CFSG.Quasithin.Vol2.Asc94.He42Alg

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ CFSG.Quasithin.A94.He42PD

variable {G : Type} [Group G] [Finite G]

private lemma he42br_comm_B {Γ : Type*} [Group Γ] {B : Subgroup Γ} {v l : Γ} (hvv : v * v = 1)
    (hlB : ∀ b ∈ B, l * b = b * l) (hvB : ∀ b ∈ B, v * b * v⁻¹ ∈ B) :
    ∀ b ∈ B, (v * l * v⁻¹ * l⁻¹) * b = b * (v * l * v⁻¹ * l⁻¹) := by
  intro b hb
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hconj : v⁻¹ * b * v = v * b * v⁻¹ := by rw [hvinv]
  have hlb' : l * (v * b * v⁻¹) = (v * b * v⁻¹) * l := hlB _ (hvB b hb)
  have hx : (v * l * v⁻¹) * b = b * (v * l * v⁻¹) := by
    calc (v * l * v⁻¹) * b = v * (l * (v⁻¹ * b * v)) * v⁻¹ := by group
      _ = v * (l * (v * b * v⁻¹)) * v⁻¹ := by rw [hconj]
      _ = v * ((v * b * v⁻¹) * l) * v⁻¹ := by rw [hlb']
      _ = (v * v) * b * (v⁻¹ * l * v⁻¹) := by group
      _ = b * (v * l * v⁻¹) := by rw [hvv, one_mul, hvinv]
  have hl' : l⁻¹ * b = b * l⁻¹ := ((show Commute l b from hlB b hb).inv_left).eq
  calc (v * l * v⁻¹ * l⁻¹) * b = (v * l * v⁻¹) * (l⁻¹ * b) := by group
    _ = (v * l * v⁻¹) * (b * l⁻¹) := by rw [hl']
    _ = ((v * l * v⁻¹) * b) * l⁻¹ := by group
    _ = (b * (v * l * v⁻¹)) * l⁻¹ := by rw [hx]
    _ = b * (v * l * v⁻¹ * l⁻¹) := by group

private lemma he42br_conj_y0 {Γ : Type*} [Group Γ] {y₁ y₂ l : Γ} (hcy : y₁ * y₂ = y₂ * y₁)
    (h2 : y₂ ^ 3 = 1) (hL1 : l * y₁ * l⁻¹ = y₂) (hL2 : l * y₂ * l⁻¹ = (y₁ * y₂)⁻¹) :
    l * (y₁ * y₂⁻¹) * l⁻¹ = y₁ * y₂⁻¹ := by
  have hy2 : y₂ * y₂ = y₂⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact h2)
  calc l * (y₁ * y₂⁻¹) * l⁻¹ = (l * y₁ * l⁻¹) * (l * y₂ * l⁻¹)⁻¹ := by group
    _ = y₂ * (y₁ * y₂) := by rw [hL1, hL2, inv_inv]
    _ = (y₂ * y₁) * y₂ := by group
    _ = (y₁ * y₂) * y₂ := by rw [← hcy]
    _ = y₁ * (y₂ * y₂) := by group
    _ = y₁ * y₂⁻¹ := by rw [hy2]

private lemma he42br_inv_y0 {Γ : Type*} [Group Γ] {y₁ y₂ v : Γ} (hcy : y₁ * y₂ = y₂ * y₁)
    (hv₁ : v * y₁ * v⁻¹ = y₁⁻¹) (hv₂ : v * y₂ * v⁻¹ = y₂⁻¹) :
    v * (y₁ * y₂⁻¹) * v⁻¹ = (y₁ * y₂⁻¹)⁻¹ := by
  have hc : Commute y₁⁻¹ y₂ := (show Commute y₁ y₂ from hcy).inv_left
  calc v * (y₁ * y₂⁻¹) * v⁻¹ = (v * y₁ * v⁻¹) * (v * y₂⁻¹ * v⁻¹) := by group
    _ = y₁⁻¹ * y₂ := by
        rw [hv₁, show v * y₂⁻¹ * v⁻¹ = (v * y₂ * v⁻¹)⁻¹ by group, hv₂, inv_inv]
    _ = y₂ * y₁⁻¹ := hc.eq
    _ = (y₁ * y₂⁻¹)⁻¹ := by group

private lemma he42br_chain {Γ : Type*} [Group Γ] {y₁ y₂ l v : Γ} {B L1 : Subgroup Γ}
    (hcy : y₁ * y₂ = y₂ * y₁) (h1 : y₁ ^ 3 = 1) (h2 : y₂ ^ 3 = 1)
    (hlB : ∀ b ∈ B, l * b = b * l) (hL1 : l * y₁ * l⁻¹ = y₂)
    (hL2 : l * y₂ * l⁻¹ = (y₁ * y₂)⁻¹)
    (hcube1 : l ^ 3 * y₁ = y₁ * l ^ 3) (hcube2 : l ^ 3 * y₂ = y₂ * l ^ 3)
    (hvv : v * v = 1) (hv₁ : v * y₁ * v⁻¹ = y₁⁻¹) (hv₂ : v * y₂ * v⁻¹ = y₂⁻¹)
    (hvB : ∀ b ∈ B, v * b * v⁻¹ ∈ B)
    (h422 : ∀ c : Γ, c * y₁ = y₁ * c → c * y₂ = y₂ * c → (∀ b ∈ B, c * b = b * c) → c ∈ L1)
    (hzp : ∀ c ∈ L1 ⊓ Subgroup.centralizer ({y₁} : Set Γ), c * (y₁ * y₂⁻¹) = (y₁ * y₂⁻¹) * c →
      c ∈ Subgroup.zpowers (y₁ * y₂⁻¹))
    (hy1 : y₁ * y₂⁻¹ ≠ 1) : l ^ 3 = 1 := by
  have hy3 : (y₁ * y₂⁻¹) ^ 3 = 1 := by
    rw [((show Commute y₁ y₂ from hcy).inv_right).mul_pow, h1, inv_pow, h2, inv_one, one_mul]
  have hly : l * (y₁ * y₂⁻¹) = (y₁ * y₂⁻¹) * l :=
    mul_inv_eq_iff_eq_mul.mp (he42br_conj_y0 hcy h2 hL1 hL2)
  have hl3L1 : l ^ 3 ∈ L1 :=
    h422 _ hcube1 hcube2 (fun b hb => ((show Commute l b from hlB b hb).pow_left 3).eq)
  have hl3C : l ^ 3 ∈ Subgroup.centralizer ({y₁} : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hcube1.symm
  have hl3y0 : l ^ 3 * (y₁ * y₂⁻¹) = (y₁ * y₂⁻¹) * l ^ 3 :=
    ((show Commute (l ^ 3) y₁ from hcube1).mul_right
      (show Commute (l ^ 3) y₂ from hcube2).inv_right).eq
  have hl3 : l ^ 3 ∈ Subgroup.zpowers (y₁ * y₂⁻¹) :=
    hzp _ (Subgroup.mem_inf.mpr ⟨hl3L1, hl3C⟩) hl3y0
  obtain ⟨hc1, hc2⟩ := CFSG.Quasithin.A94.He42Alg.commutator_comm hcy h1 h2 hvv hv₁ hv₂ hL1 hL2
  have hcB : ∀ b ∈ B, (v * l * v⁻¹ * l⁻¹) * b = b * (v * l * v⁻¹ * l⁻¹) :=
    he42br_comm_B hvv hlB hvB
  have hcL1 : v * l * v⁻¹ * l⁻¹ ∈ L1 := h422 _ hc1 hc2 hcB
  have hcC : v * l * v⁻¹ * l⁻¹ ∈ Subgroup.centralizer ({y₁} : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hc1.symm
  have hcy0 : (v * l * v⁻¹ * l⁻¹) * (y₁ * y₂⁻¹) = (y₁ * y₂⁻¹) * (v * l * v⁻¹ * l⁻¹) :=
    ((show Commute (v * l * v⁻¹ * l⁻¹) y₁ from hc1).mul_right
      (show Commute (v * l * v⁻¹ * l⁻¹) y₂ from hc2).inv_right).eq
  have hczp : v * l * v⁻¹ * l⁻¹ ∈ Subgroup.zpowers (y₁ * y₂⁻¹) :=
    hzp _ (Subgroup.mem_inf.mpr ⟨hcL1, hcC⟩) hcy0
  have hvl : ∃ t ∈ Subgroup.zpowers (y₁ * y₂⁻¹), v * l * v⁻¹ = t * l :=
    ⟨v * l * v⁻¹ * l⁻¹, hczp, by group⟩
  exact CFSG.Quasithin.A94.He42Alg.pow_three_eq_one hvv (he42br_inv_y0 hcy hv₁ hv₂) hy3 hy1 hly
    hl3 hvl

theorem HeSetup.braid (S : HeSetup G) (hB : S.BaseFacts) (hP : S.StepPsi) {y₁ y₂ : G}
    (hY : YSpec S y₁ y₂) (hn : S.StepYnorm y₁ y₂) (hf : S.StepYfpf y₁ y₂)
    (h0 : S.StepY0 y₁ y₂) (hV : S.StepV y₁ y₂) (hc : S.StepComm y₁ y₂) {l₁ l₂ : G}
    (hl : WSpec S y₁ y₂ l₁ l₂) (h422 : Open422 S y₁ y₂) : (l₁ * l₂) ^ 3 = 1 := by
  have hcy : y₁ * y₂ = y₂ * y₁ := hY.comm
  have h1 : y₁ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y₁
    rwa [hY.ord₁] at h
  have h2 : y₂ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y₂
    rwa [hY.ord₂] at h
  have hcB1 : ∀ b ∈ S.B, Commute l₁ b := fun b hb =>
    ((Subgroup.mem_centralizer_iff.mp (hB.L1_le_centralizer hl.mem₁)) b hb).symm
  have hcB2 : ∀ b ∈ S.B, Commute l₂ b := fun b hb =>
    ((Subgroup.mem_centralizer_iff.mp (hB.L2_le_centralizer hl.mem₂)) b hb).symm
  have hlB : ∀ b ∈ S.B, l₁ * l₂ * b = b * (l₁ * l₂) := fun b hb =>
    ((hcB1 b hb).mul_left (hcB2 b hb)).eq
  have hL1 : (l₁ * l₂) * y₁ * (l₁ * l₂)⁻¹ = y₂ :=
    CFSG.Quasithin.A94.He42Alg.l_conj_y1 hcy h1 h2 hl.cent₁ hl.inv₁ hl.cent₂ hl.inv₂
  have hL2 : (l₁ * l₂) * y₂ * (l₁ * l₂)⁻¹ = (y₁ * y₂)⁻¹ :=
    CFSG.Quasithin.A94.He42Alg.l_conj_y2 hcy h1 h2 hl.cent₁ hl.inv₁ hl.cent₂ hl.inv₂
  obtain ⟨hcube1, hcube2⟩ :=
    CFSG.Quasithin.A94.He42Alg.l_cube_comm hcy h1 h2 hl.cent₁ hl.inv₁ hl.cent₂ hl.inv₂
  obtain ⟨ψ, hPD⟩ := hP.1
  have h3 : ¬ 3 ∣ Nat.card S.A := by rw [hB.card_A]; norm_num
  have hcompl := hPD.exists_mul_centralizer hn.1.1 h1 hc.1 h3
  have hAy : S.A ⊓ Subgroup.centralizer ({y₁} : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxy : y₁ * x = x * y₁ := Subgroup.mem_centralizer_iff.mp hxC y₁ (Set.mem_singleton y₁)
    exact hf.1 x hxA hxy.symm
  have hy0A : y₁ * y₂⁻¹ ∉ S.A := fun h => h0.2.1 (hB.A_le_J h)
  have hy0C : y₁ * y₂⁻¹ ∈ Subgroup.centralizer ({y₁} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (Commute.refl y₁).mul_right (show Commute y₁ y₂ from hcy).inv_right
  have hzp := hPD.mem_zpowers_of_commute hcompl hAy
    (Subgroup.mem_inf.mpr ⟨hB.K_le_L1 h0.1, hy0C⟩) h0.1 hy0A h0.2.2
  have hy1 : y₁ * y₂⁻¹ ≠ 1 := fun h => h0.2.1 (by rw [h]; exact S.J.one_mem)
  obtain ⟨v, hvv, hv₁, hv₂, hvB⟩ := hV
  exact he42br_chain (B := S.B) (L1 := S.L1) hcy h1 h2 hlB hL1 hL2 hcube1 hcube2 hvv hv₁ hv₂ hvB
    h422 hzp hy1

end CFSG.Quasithin.A94.He42
