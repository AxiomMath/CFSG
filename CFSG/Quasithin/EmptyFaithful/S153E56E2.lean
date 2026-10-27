module

public import CFSG.Quasithin.EmptyFaithful.S153E56E1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E56e

open CFSG.Quasithin.S153E

section Index

variable {G : Type} [Group G]

theorem card_eq_of_mIdx [Finite G] {A B : Subgroup G} (hBA : B ≤ A) (hA : IsPGroup 2 A) {k : ℕ}
    (hk : mIdx A B = k) : Nat.card A = Nat.card B * 2 ^ k := by
  have hmul := Subgroup.card_mul_index (B.subgroupOf A)
  have hcard : Nat.card ↥(B.subgroupOf A) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
  rw [hcard] at hmul
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hA
  have hdvd : B.relIndex A ∣ 2 ^ n := by
    rw [← hn, ← hmul]
    exact Dvd.intro_left _ rfl
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hkm : mIdx A B = m := by
    unfold mIdx
    rw [hm]
    exact padicValNat.prime_pow m
  rw [hkm] at hk
  rw [← hmul]
  change Nat.card B * B.relIndex A = _
  rw [hm, hk]

theorem mIdx_eq_of_card [Finite G] {A B : Subgroup G} (hBA : B ≤ A) {k : ℕ}
    (hk : Nat.card A = Nat.card B * 2 ^ k) : mIdx A B = k := by
  have hmul := Subgroup.card_mul_index (B.subgroupOf A)
  have hcard : Nat.card ↥(B.subgroupOf A) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
  rw [hcard] at hmul
  have hpos : 0 < Nat.card B := Nat.card_pos_iff.2 ⟨⟨1⟩, inferInstance⟩
  have hidx : B.relIndex A = 2 ^ k := by
    change (B.subgroupOf A).index = 2 ^ k
    exact Nat.eq_of_mul_eq_mul_left hpos (hmul.trans hk)
  unfold mIdx
  rw [hidx]
  exact padicValNat.prime_pow k

end Index

section PartA

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t}

theorem Z_le_U (cx : Ctx15350 T Mc M V₁ V₂ t) : quasithinOmegaOneCenter T ≤ UH153 T M V₁ Mc :=
  (Z_le_ZS cx).trans (ZS_le_U cx)

theorem U_le_centralizer_Z (cx : Ctx15350 T Mc M V₁ V₂ t) :
    UH153 T M V₁ Mc ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  fun _ hu => cx.hF.H_le_centralizer ((U_le_T cx).trans (T_le_Mc cx) hu)

theorem U'_le_centralizer_Z' (cx : Ctx15350 T Mc M V₁ V₂ t) (y : G) :
    conjSubgroup (UH153 T M V₁ Mc) y ≤
      Subgroup.centralizer (conjSubgroup (quasithinOmegaOneCenter T) y : Set G) :=
  (conjSubgroup_mono (U_le_centralizer_Z cx) y).trans (conjSubgroup_centralizer _ y).le

theorem card_U (H : Hyps56 cx N₁ N₂ g s y) : Nat.card (UH153 T M V₁ Mc) = 2 ^ (2 * s + 5) := by
  have h := card_eq_of_mIdx (Z_le_U cx) cx.hF.isPGroup_conjClosure H.hrank
  rw [S153E57.Z_card cx] at h
  rw [h]
  ring

theorem Z'_le_U (H : Hyps56 cx N₁ N₂ g s y) :
    conjSubgroup (quasithinOmegaOneCenter T) y ≤ UH153 T M V₁ Mc := by
  obtain ⟨z, hz⟩ := exists_ZGen cx
  intro x hx
  rcases (hz.mem_conj_iff y).1 hx with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact zp_mem_U H hz

theorem Z_le_U' (H : Hyps56 cx N₁ N₂ g s y) :
    quasithinOmegaOneCenter T ≤ conjSubgroup (UH153 T M V₁ Mc) y := by
  obtain ⟨z, hz⟩ := exists_ZGen cx
  intro x hx
  rw [mem_conjSubgroup_iff]
  rcases hz.mem_Z_iff.1 hx with h | h
  · rw [h]
    simp
  · rw [h, yz_eq H hz]
    exact Subgroup.mul_mem _ (Z_le_U cx hz.mem) (zp_mem_U H hz)

theorem Z_inf_Z' (H : Hyps56 cx N₁ N₂ g s y) :
    quasithinOmegaOneCenter T ⊓ conjSubgroup (quasithinOmegaOneCenter T) y = ⊥ := by
  obtain ⟨z, hz⟩ := exists_ZGen cx
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot]
  rcases hz.mem_Z_iff.1 hx1 with h | h
  · exact h
  · rcases (hz.mem_conj_iff y).1 hx2 with h' | h'
    · exact h'
    · exact absurd (h'.symm.trans h) (zp_ne H hz)

theorem Z'_le_V (H : Hyps56 cx N₁ N₂ g s y) :
    conjSubgroup (quasithinOmegaOneCenter T) y ≤ VZ T M := by
  obtain ⟨z, hz⟩ := exists_ZGen cx
  intro x hx
  rcases (hz.mem_conj_iff y).1 hx with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact zp_memV H hz

theorem F_eq (cx : Ctx15350 T Mc M V₁ V₂ t) (y : G) :
    Fgp153 T M V₁ Mc y = UH153 T M V₁ Mc ⊓
      Subgroup.centralizer (conjSubgroup (quasithinOmegaOneCenter T) y : Set G) := by
  show UH153 T M V₁ Mc ⊓ conjSubgroup Mc y = _
  have h : conjSubgroup Mc y = Subgroup.centralizer (conjSubgroup (quasithinOmegaOneCenter T) y : Set G) := by
    rw [← conjSubgroup_centralizer]
    exact congrArg (fun K => conjSubgroup K y) (Mc_eq cx)
  rw [h]

theorem X_eq (H : Hyps56 cx N₁ N₂ g s y) :
    Xgp153 T M V₁ Mc y = conjSubgroup (UH153 T M V₁ Mc) y ⊓
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨z, hz⟩ := exists_ZGen cx
  show conjSubgroup (Fgp153 T M V₁ Mc y) y = _
  rw [F_eq cx y, conjSubgroup_inf, conjSubgroup_centralizer, conjSubgroup_conjSubgroup]
  have hzq : (y * y)⁻¹ * z * (y * y) = z * (y⁻¹ * z * y) := by
    calc (y * y)⁻¹ * z * (y * y) = y⁻¹ * (y⁻¹ * z * y) * y := by group
      _ = y⁻¹ * (y * (y * z * y⁻¹) * y⁻¹) * y := by rw [y_sq_conj H (hz.memV cx)]
      _ = y * z * y⁻¹ := by group
      _ = z * (y⁻¹ * z * y) := yz_eq H hz
  have hzpmem : y⁻¹ * z * y ∈ conjSubgroup (quasithinOmegaOneCenter T) y :=
    (hz.mem_conj_iff y).2 (Or.inr rfl)
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hxU, hxC⟩
    refine ⟨hxU, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
    have hxzp := Subgroup.mem_centralizer_iff.1 (U'_le_centralizer_Z' cx y hxU) _ hzpmem
    rcases hz.mem_Z_iff.1 hw with h | h
    · rw [h]
      simp
    · rw [h]
      have hzz := Subgroup.mem_centralizer_iff.1 hxC (z * (y⁻¹ * z * y))
        ((hz.mem_conj_iff (y * y)).2 (Or.inr hzq.symm))
      apply mul_right_cancel (b := y⁻¹ * z * y)
      calc z * x * (y⁻¹ * z * y) = z * (x * (y⁻¹ * z * y)) := by group
        _ = z * ((y⁻¹ * z * y) * x) := by rw [hxzp]
        _ = (z * (y⁻¹ * z * y)) * x := by group
        _ = x * (z * (y⁻¹ * z * y)) := hzz
        _ = x * z * (y⁻¹ * z * y) := by group
  · rintro ⟨hxU, hxC⟩
    refine ⟨hxU, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
    have hxzp := Subgroup.mem_centralizer_iff.1 (U'_le_centralizer_Z' cx y hxU) _ hzpmem
    have hxz := Subgroup.mem_centralizer_iff.1 hxC z hz.mem
    rcases (hz.mem_conj_iff (y * y)).1 hw with h | h
    · rw [h]
      simp
    · rw [h, hzq]
      calc z * (y⁻¹ * z * y) * x = z * ((y⁻¹ * z * y) * x) := by group
        _ = z * (x * (y⁻¹ * z * y)) := by rw [hxzp]
        _ = (z * x) * (y⁻¹ * z * y) := by group
        _ = (x * z) * (y⁻¹ * z * y) := by rw [hxz]
        _ = x * (z * (y⁻¹ * z * y)) := by group

theorem E_eq (H : Hyps56 cx N₁ N₂ g s y) :
    Egp153 T M V₁ Mc y = UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) y := by
  show Fgp153 T M V₁ Mc y ⊓ Xgp153 T M V₁ Mc y = _
  rw [F_eq cx y, X_eq H]
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨hxU, -⟩, hxU', -⟩
    exact ⟨hxU, hxU'⟩
  · rintro ⟨hxU, hxU'⟩
    exact ⟨⟨hxU, U'_le_centralizer_Z' cx y hxU'⟩, hxU', U_le_centralizer_Z cx hxU⟩

theorem E_le_U (H : Hyps56 cx N₁ N₂ g s y) : Egp153 T M V₁ Mc y ≤ UH153 T M V₁ Mc :=
  (E_eq H).le.trans inf_le_left

theorem E_le_U' (H : Hyps56 cx N₁ N₂ g s y) :
    Egp153 T M V₁ Mc y ≤ conjSubgroup (UH153 T M V₁ Mc) y :=
  (E_eq H).le.trans inf_le_right

theorem X_le_Mc (H : Hyps56 cx N₁ N₂ g s y) : Xgp153 T M V₁ Mc y ≤ Mc := by
  rw [X_eq H]
  exact inf_le_right.trans (Mc_eq cx).ge

theorem V0_le_E (H : Hyps56 cx N₁ N₂ g s y) :
    quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤
      Egp153 T M V₁ Mc y := by
  rw [E_eq H]
  exact sup_le (le_inf (Z_le_U cx) (Z_le_U' H))
    (le_inf (Z'_le_U H) (conjSubgroup_mono (Z_le_U cx) y))

theorem Z_le_E (H : Hyps56 cx N₁ N₂ g s y) : quasithinOmegaOneCenter T ≤ Egp153 T M V₁ Mc y :=
  le_sup_left.trans (V0_le_E H)

theorem Z'_le_E (H : Hyps56 cx N₁ N₂ g s y) :
    conjSubgroup (quasithinOmegaOneCenter T) y ≤ Egp153 T M V₁ Mc y :=
  le_sup_right.trans (V0_le_E H)

theorem E_sq (H : Hyps56 cx N₁ N₂ g s y) {e : G} (he : e ∈ Egp153 T M V₁ Mc y) : e * e = 1 := by
  have hU : e ∈ UH153 T M V₁ Mc := E_le_U H he
  have hU' : e ∈ conjSubgroup (UH153 T M V₁ Mc) y := E_le_U' H he
  rw [mem_conjSubgroup_iff] at hU'
  have h1 : e * e ∈ quasithinOmegaOneCenter T := sq_U_mem cx hU
  have h2 : e * e ∈ conjSubgroup (quasithinOmegaOneCenter T) y := by
    rw [mem_conjSubgroup_iff]
    have := sq_U_mem cx hU'
    have e1 : y * (e * e) * y⁻¹ = (y * e * y⁻¹) * (y * e * y⁻¹) := by group
    rw [e1]
    exact this
  have h3 : e * e ∈ quasithinOmegaOneCenter T ⊓ conjSubgroup (quasithinOmegaOneCenter T) y :=
    ⟨h1, h2⟩
  rw [Z_inf_Z' H, Subgroup.mem_bot] at h3
  exact h3

theorem E_comm (H : Hyps56 cx N₁ N₂ g s y) {e₁ e₂ : G} (h₁ : e₁ ∈ Egp153 T M V₁ Mc y)
    (h₂ : e₂ ∈ Egp153 T M V₁ Mc y) : e₁ * e₂ = e₂ * e₁ := by
  have hU₁ : e₁ ∈ UH153 T M V₁ Mc := E_le_U H h₁
  have hU₂ : e₂ ∈ UH153 T M V₁ Mc := E_le_U H h₂
  have hU₁' : e₁ ∈ conjSubgroup (UH153 T M V₁ Mc) y := E_le_U' H h₁
  have hU₂' : e₂ ∈ conjSubgroup (UH153 T M V₁ Mc) y := E_le_U' H h₂
  rw [mem_conjSubgroup_iff] at hU₁' hU₂'
  have h1 : e₁ * e₂ * e₁⁻¹ * e₂⁻¹ ∈ quasithinOmegaOneCenter T := commutator_U_mem cx hU₁ hU₂
  have h2 : e₁ * e₂ * e₁⁻¹ * e₂⁻¹ ∈ conjSubgroup (quasithinOmegaOneCenter T) y := by
    rw [mem_conjSubgroup_iff]
    have := commutator_U_mem cx hU₁' hU₂'
    have e1 : y * (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) * y⁻¹ =
        (y * e₁ * y⁻¹) * (y * e₂ * y⁻¹) * (y * e₁ * y⁻¹)⁻¹ * (y * e₂ * y⁻¹)⁻¹ := by group
    rw [e1]
    exact this
  have h3 : e₁ * e₂ * e₁⁻¹ * e₂⁻¹ ∈
      quasithinOmegaOneCenter T ⊓ conjSubgroup (quasithinOmegaOneCenter T) y := ⟨h1, h2⟩
  rw [Z_inf_Z' H, Subgroup.mem_bot] at h3
  calc e₁ * e₂ = (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) * (e₂ * e₁) := by group
    _ = e₂ * e₁ := by rw [h3, one_mul]

theorem isElemAbelian_E (H : Hyps56 cx N₁ N₂ g s y) : IsElemAbelian 2 (Egp153 T M V₁ Mc y) := by
  rw [F7.isElemAbelian_iff]
  exact ⟨fun a ha b hb => E_comm H ha hb, fun a ha => by rw [pow_two]; exact E_sq H ha⟩

theorem V0_le_V (H : Hyps56 cx N₁ N₂ g s y) :
    quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤ VZ T M :=
  sup_le cx.c.hyp.Z_le_VZ (Z'_le_V H)

theorem V_le_normalizer_V0 (H : Hyps56 cx N₁ N₂ g s y) :
    VZ T M ≤ Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G) := by
  intro v hv
  have hmem : v ∈ Subgroup.centralizer
      ((quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) :
        Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact B2F.isElemAbelian_comm cx.c.hyp.elemAbelian (V0_le_V H hw) hv
  exact Subgroup.centralizer_le_normalizer _ hmem

end PartA

end S153E56e

end CFSG.Quasithin
