module

public import CFSG.Quasithin.EmptyFaithful.S153E56E2
public import CFSG.Quasithin.EmptyFaithful.S153E56E3
public import CFSG.Quasithin.EmptyFaithful.S153E56E6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise MatrixGroups

namespace S153E56e

open CFSG.Quasithin.S153E

section RLe

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t}

theorem comm_P_mem_V (H : Hyps56 cx N₁ N₂ g s y) {a b : G} (ha : a ∈ Pgp153 T M V₁ Mc g)
    (hb : b ∈ Pgp153 T M V₁ Mc g) : a * b * a⁻¹ * b⁻¹ ∈ VZ T M := by
  have pd := S153E55.pdecomp cx H.c.toChain15354
  have hsq : ∀ x ∈ Pgp153 T M V₁ Mc g, x * x ∈ VZ T M := fun x hx =>
    pd.sq_mem_V (S153E55.sq_mem_of_nat H.c.h54.four_nat₁)
      (S153E55.sq_mem_of_nat H.c.h54.four_nat₂) hx
  have hcen : ∀ v ∈ VZ T M, ∀ p ∈ Pgp153 T M V₁ Mc g, v * p = p * v := pd.V_central
  have hva : a * a ∈ VZ T M := hsq a ha
  have hvb : b * b ∈ VZ T M := hsq b hb
  have hw : (a * b) * (a * b) ∈ VZ T M := hsq _ (Subgroup.mul_mem _ ha hb)
  have hc : b * (a * a)⁻¹ * b⁻¹ = (a * a)⁻¹ := by
    have := hcen _ ((VZ T M).inv_mem hva) b hb
    calc b * (a * a)⁻¹ * b⁻¹ = ((a * a)⁻¹ * b) * b⁻¹ := by rw [this]
      _ = (a * a)⁻¹ := by group
  have e : a * b * a⁻¹ * b⁻¹ = ((a * b) * (a * b)) * (a * a)⁻¹ * (b * b)⁻¹ := by
    calc a * b * a⁻¹ * b⁻¹ = a * b * a * (b * (a * a)⁻¹ * b⁻¹) * b⁻¹ := by rw [hc]; group
      _ = ((a * b) * (a * b)) * (a * a)⁻¹ * (b * b)⁻¹ := by group
  rw [e]
  exact (VZ T M).mul_mem ((VZ T M).mul_mem hw ((VZ T M).inv_mem hva)) ((VZ T M).inv_mem hvb)

theorem card_P₁ (H : Hyps56 cx N₁ N₂ g s y) :
    Nat.card ↥(Pi153 T Mc M V₁ N₁ g) = 2 ^ (2 * s + 4) := by
  obtain ⟨β₁, φ₁, -, -, hφs, hφk, -⟩ := H.c.h54.four_nat₁
  have hVP₁ : VZ T M ≤ Pi153 T Mc M V₁ N₁ g := le_sup_right
  rw [card_eq_card_mul_of_surj φ₁ hφs hφk hVP₁, card_MR, cx.c.hyp.card_VZ]
  ring

theorem J_norm_E (H : Hyps56 cx N₁ N₂ g s y) {j e : G} (hj : j ∈ Jgp153 T M V₁ Mc y)
    (he : e ∈ Egp153 T M V₁ Mc y) : j * e * j⁻¹ ∈ Egp153 T M V₁ Mc y := by
  have h1 : ⁅e, j⁆ ∈ quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y :=
    H.iJ.E_comm (Subgroup.commutator_mem_commutator he hj)
  have h2 : e * j * e⁻¹ * j⁻¹ ∈ Egp153 T M V₁ Mc y := by
    have := V0_le_E H h1
    rwa [commutatorElement_def] at this
  have e1 : j * e * j⁻¹ = (e * j * e⁻¹ * j⁻¹)⁻¹ * e := by group
  rw [e1]
  exact (Egp153 T M V₁ Mc y).mul_mem ((Egp153 T M V₁ Mc y).inv_mem h2) he

theorem bar_j (H : Hyps56 cx N₁ N₂ g s y) {j : G} (hj : j ∈ Jgp153 T M V₁ Mc y)
    (hjy : y⁻¹ * j ∈ Subgroup.centralizer (VZ T M : Set G)) :
    S153E55.bar cx (J_le_YU (T := T) (M := M) (V₁ := V₁) (Mc := Mc) (y_mem_Y H) hj) = ybar H := by
  have hV := cx.c.hyp.elemAbelian
  have hyYU := y_mem_YU H
  have hjYU := J_le_YU (T := T) (M := M) (V₁ := V₁) (Mc := Mc) (y_mem_Y H) hj
  have hyiYU : y⁻¹ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.inv_mem _ hyYU
  have hyijYU : y⁻¹ * j ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.mul_mem _ hyiYU hjYU
  have h1 : S153E55.bar cx hyijYU = 1 :=
    (convI_eq_one_iff hV ⟨y⁻¹ * j, S153E55.YU_le_normalizer_V cx hyijYU⟩).2 hjy
  rw [bar_mul' cx hyiYU hjYU, bar_inv' cx hyYU hyiYU] at h1
  exact (inv_mul_eq_one.1 h1).symm

theorem fpf_of_sq_ne_one : ∀ b : SL(2, ZMod 2), b ^ 2 ≠ 1 → ∀ v : Fin 2 → ZMod 2, b • v = v →
    v = 0 := by decide

theorem r_le (H : Hyps56 cx N₁ N₂ g s y) {r : ℕ}
    {β : ↥(Jgp153 T M V₁ Mc y) →* SL(2, ZMod 2)}
    {φ : ↥(pCoreOf 2 (Jgp153 T M V₁ Mc y)) →* MR r}
    (h : NatStr (Jgp153 T M V₁ Mc y) (pCoreOf 2 (Jgp153 T M V₁ Mc y)) (Egp153 T M V₁ Mc y) r β φ) :
    r ≤ s + 1 := by
  obtain ⟨z, hz⟩ := exists_ZGen cx
  obtain ⟨j, hj, hjy⟩ := exists_j H
  have hV := cx.c.hyp.elemAbelian
  have hI := H.c.h54.one
  have hyY := y_mem_Y H
  have hyYU := y_mem_YU H
  have hJYU := J_le_YU (T := T) (M := M) (V₁ := V₁) (Mc := Mc) hyY
  have hjYU := hJYU hj
  have hyiYU : y⁻¹ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.inv_mem _ hyYU
  have hP : y⁻¹ * j ∈ Pgp153 T M V₁ Mc g :=
    S153E55.centralizer_le_P hI cx ⟨Subgroup.mul_mem _ hyiYU hjYU, hjy⟩
  have hjv : ∀ v ∈ VZ T M, j * v * j⁻¹ = y * v * y⁻¹ := by
    intro v hv
    have hpv : (y⁻¹ * j) * v = v * (y⁻¹ * j) := (Subgroup.mem_centralizer_iff.1 hjy v hv).symm
    calc j * v * j⁻¹ = y * ((y⁻¹ * j) * v * (y⁻¹ * j)⁻¹) * y⁻¹ := by group
      _ = y * v * y⁻¹ := by rw [hpv]; group
  have hbj := bar_j H hj hjy
  have hRJ : pCoreOf 2 (Jgp153 T M V₁ Mc y) ≤ Jgp153 T M V₁ Mc y := pCoreOf_le 2 _
  have hJR : ∀ j' ∈ Jgp153 T M V₁ Mc y, ∀ x ∈ pCoreOf 2 (Jgp153 T M V₁ Mc y),
      j' * x * j'⁻¹ ∈ pCoreOf 2 (Jgp153 T M V₁ Mc y) := fun j' hj' x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hj') x).mp hx
  have hb2 : (β ⟨j, hj⟩) ^ 2 ≠ 1 := by
    intro h2
    have hjjR : j * j ∈ pCoreOf 2 (Jgp153 T M V₁ Mc y) := by
      have h3 : β (⟨j, hj⟩ * ⟨j, hj⟩) = 1 := by rw [map_mul, ← pow_two]; exact h2
      exact (h.β_ker _).1 h3
    obtain ⟨k, hk⟩ := R_two_pow _ hjjR
    have hjjYU : j * j ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.mul_mem _ hjYU hjYU
    have hbar := bar_pow_eq_one cx hjjYU hk
    rw [bar_mul' cx hjYU hjYU, hbj] at hbar
    exact ybar_ne_one H (eq_one_of_sq_two_pow (ybar_pow_three H) hbar)
  have hb : ∀ v : Fin 2 → ZMod 2, β ⟨j, hj⟩ • v = v → v = 0 := fun v hv =>
    fpf_of_sq_ne_one _ hb2 v hv
  have hQR : Jgp153 T M V₁ Mc y ⊓ Pgp153 T M V₁ Mc g ≤ pCoreOf 2 (Jgp153 T M V₁ Mc y) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((S153E55.P_isPGroup hI).to_le inf_le_right)
    intro a ha
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ha, S153E55.YU_le_normalizer_P hI (hJYU ha)⟩
  have hRQ : ∀ x ∈ pCoreOf 2 (Jgp153 T M V₁ Mc y), ∃ q ∈ Jgp153 T M V₁ Mc y ⊓ Pgp153 T M V₁ Mc g,
      x * q⁻¹ ∈ Egp153 T M V₁ Mc y := by
    intro x hx
    obtain ⟨x', hx'R, hxe⟩ := h.exists_comm hJR hj hb x hx
    have hqJ : j * x' * j⁻¹ * x'⁻¹ ∈ Jgp153 T M V₁ Mc y :=
      (Jgp153 T M V₁ Mc y).mul_mem ((Jgp153 T M V₁ Mc y).mul_mem
        ((Jgp153 T M V₁ Mc y).mul_mem hj (hRJ hx'R)) ((Jgp153 T M V₁ Mc y).inv_mem hj))
        ((Jgp153 T M V₁ Mc y).inv_mem (hRJ hx'R))
    refine ⟨j * x' * j⁻¹ * x'⁻¹, ⟨hqJ, ?_⟩, hxe⟩
    exact S153E55.centralizer_le_P hI cx ⟨hJYU hqJ, comm_j_R_mem_C H hj hjy hx'R⟩
  let C : Subgroup G := Subgroup.closure
    {c | ∃ q ∈ Jgp153 T M V₁ Mc y ⊓ Pgp153 T M V₁ Mc g, c = j * q * j⁻¹ * q⁻¹}
  have hCR : C ≤ pCoreOf 2 (Jgp153 T M V₁ Mc y) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨q, hq, rfl⟩
    have hqR := hQR hq
    exact (pCoreOf 2 (Jgp153 T M V₁ Mc y)).mul_mem (hJR j hj q hqR)
      ((pCoreOf 2 (Jgp153 T M V₁ Mc y)).inv_mem hqR)
  have hCgen : ∀ q ∈ Jgp153 T M V₁ Mc y ⊓ Pgp153 T M V₁ Mc g, j * q * j⁻¹ * q⁻¹ ∈ C :=
    fun q hq => Subgroup.subset_closure ⟨q, hq, rfl⟩
  have hC : ∀ ρ ∈ pCoreOf 2 (Jgp153 T M V₁ Mc y), ∃ c ∈ C, ρ * c⁻¹ ∈ Egp153 T M V₁ Mc y := by
    intro ρ hρ
    obtain ⟨x, hxR, hρx⟩ := h.exists_comm hJR hj hb ρ hρ
    obtain ⟨q, hq, hxq⟩ := hRQ x hxR
    have hqJ : q ∈ Jgp153 T M V₁ Mc y := hq.1
    have hcJ : j * q * j⁻¹ * q⁻¹ ∈ Jgp153 T M V₁ Mc y :=
      (Jgp153 T M V₁ Mc y).mul_mem ((Jgp153 T M V₁ Mc y).mul_mem
        ((Jgp153 T M V₁ Mc y).mul_mem hj hqJ) ((Jgp153 T M V₁ Mc y).inv_mem hj))
        ((Jgp153 T M V₁ Mc y).inv_mem hqJ)
    refine ⟨j * q * j⁻¹ * q⁻¹, hCgen q hq, ?_⟩
    have e1 : ρ * (j * q * j⁻¹ * q⁻¹)⁻¹ =
        (ρ * (j * x * j⁻¹ * x⁻¹)⁻¹) * (j * (x * q⁻¹) * j⁻¹) *
          ((j * q * j⁻¹ * q⁻¹) * (x * q⁻¹)⁻¹ * (j * q * j⁻¹ * q⁻¹)⁻¹) := by group
    rw [e1]
    exact (Egp153 T M V₁ Mc y).mul_mem ((Egp153 T M V₁ Mc y).mul_mem hρx (J_norm_E H hj hxq))
      (J_norm_E H hcJ ((Egp153 T M V₁ Mc y).inv_mem hxq))
  have hCP : C ≤ Pi153 T Mc M V₁ N₁ g := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨q, hq, rfl⟩
    have hqP : q ∈ Pgp153 T M V₁ Mc g := hq.2
    have hd := comm_P_mem_V H hP hqP
    have e1 : j * q * j⁻¹ * q⁻¹ =
        (y * ((y⁻¹ * j) * q * (y⁻¹ * j)⁻¹ * q⁻¹) * y⁻¹) * (q * y * q⁻¹ * y⁻¹)⁻¹ := by group
    rw [e1]
    have hyN := y_mem_N H
    have h1 : y * ((y⁻¹ * j) * q * (y⁻¹ * j)⁻¹ * q⁻¹) * y⁻¹ ∈ VZ T M :=
      (Subgroup.mem_normalizer_iff.mp hyN _).mp hd
    have h2 : q * y * q⁻¹ * y⁻¹ ∈ ⁅Pgp153 T M V₁ Mc g, Yi153 T Mc M V₁ N₁⁆ :=
      Subgroup.commutator_mem_commutator hqP H.hy.1
    exact (Pi153 T Mc M V₁ N₁ g).mul_mem (Subgroup.mem_sup_right h1)
      ((Pi153 T Mc M V₁ N₁ g).inv_mem (Subgroup.mem_sup_left h2))
  have hzV := hz.memV cx
  have hzpV := zp_memV H hz
  have hVP : VZ T M ≤ Pgp153 T M V₁ Mc g := H.c.h54.two_center.trans inf_le_left
  have hzQ : z ∈ Jgp153 T M V₁ Mc y ⊓ Pgp153 T M V₁ Mc g :=
    ⟨U_le_J T M V₁ Mc y (Z_le_U cx hz.mem), hVP hzV⟩
  have hzpQ : y⁻¹ * z * y ∈ Jgp153 T M V₁ Mc y ⊓ Pgp153 T M V₁ Mc g :=
    ⟨U_le_J T M V₁ Mc y (zp_mem_U H hz), hVP hzpV⟩
  have hzpC : y⁻¹ * z * y ∈ C := by
    have h1 := hCgen z hzQ
    have e1 : j * z * j⁻¹ * z⁻¹ = y⁻¹ * z * y := by
      rw [hjv z hzV, yz_eq H hz]
      have hcomm := B2F.isElemAbelian_comm hV hzV hzpV
      calc z * (y⁻¹ * z * y) * z⁻¹ = (y⁻¹ * z * y) * z * z⁻¹ := by rw [hcomm]
        _ = y⁻¹ * z * y := by group
    rwa [e1] at h1
  have hzzpC : z * (y⁻¹ * z * y) ∈ C := by
    have h1 := hCgen _ hzpQ
    have e1 : j * (y⁻¹ * z * y) * j⁻¹ * (y⁻¹ * z * y)⁻¹ = z * (y⁻¹ * z * y) := by
      rw [hjv _ hzpV]
      have hzp2 : (y⁻¹ * z * y) * (y⁻¹ * z * y) = 1 := by
        calc (y⁻¹ * z * y) * (y⁻¹ * z * y) = y⁻¹ * (z * z) * y := by group
          _ = 1 := by rw [hz.sq]; group
      have hzp_inv : (y⁻¹ * z * y)⁻¹ = y⁻¹ * z * y := inv_eq_of_mul_eq_one_right hzp2
      rw [hzp_inv]
      group
    rwa [e1] at h1
  have hzC : z ∈ C := by
    have e1 : z = (z * (y⁻¹ * z * y)) * (y⁻¹ * z * y)⁻¹ := by group
    rw [e1]
    exact C.mul_mem hzzpC (C.inv_mem hzpC)
  have hV₀C : quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤ C := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rcases hz.mem_Z_iff.1 hx with h1 | h1
      · rw [h1]
        exact C.one_mem
      · rw [h1]
        exact hzC
    · rcases (hz.mem_conj_iff y).1 hx with h1 | h1
      · rw [h1]
        exact C.one_mem
      · rw [h1]
        exact hzpC
  have hV₀ : quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤
      C ⊓ Egp153 T M V₁ Mc y := le_inf hV₀C (V0_le_E H)
  have hcard := h.card_ge hCR hC hV₀
  rw [H.iJ.V0_card] at hcard
  have hCle : Nat.card C ≤ 2 ^ (2 * s + 4) := by
    rw [← card_P₁ H]
    exact Subgroup.card_le_of_le hCP
  have h4 : 2 ^ (2 * r + 2) ≤ 2 ^ (2 * s + 4) := by
    calc 2 ^ (2 * r + 2) = 4 * 2 ^ (2 * r) := by ring
      _ ≤ Nat.card C := hcard
      _ ≤ 2 ^ (2 * s + 4) := hCle
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h4
  omega

end RLe

end S153E56e

end CFSG.Quasithin
