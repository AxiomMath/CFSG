module

public import Certificates.Certificate899101
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp8
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFSp8
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp82

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (H8 sp8Z sp8T sp8E)
open CFSG.RankThree.PartTwo.Sec21.FF79 (IsElemAb IsSylowOf Cen CenS Nor)

section General

variable {G : Type} [Group G]

theorem isElemAb_iff {p k : ℕ} {B : Subgroup G} : IsElemAb p k B ↔
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ (∀ x ∈ B, x ^ p = 1) ∧ Nat.card B = p ^ k := by
  constructor
  · rintro ⟨hab, hc⟩
    refine ⟨fun x hx y hy => congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩),
      fun x hx => ?_, hc⟩
    haveI := hab
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  · rintro ⟨hc, hp, hcard⟩
    exact ⟨{ is_comm := ⟨fun a b => Subtype.ext (hc _ a.2 _ b.2)⟩
             exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
               Subtype.ext (by simpa using hp x x.2) }, hcard⟩

theorem card_of_isSylowOf [Finite G] {p : ℕ} (hp : p.Prime) {H P : Subgroup G}
    (h : IsSylowOf p P H) : Nat.card P = p ^ (Nat.card H).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hle, hpg, hcop⟩ := h
  obtain ⟨a, ha⟩ := hpg.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_of_le_left hle, ha] at h1
  have hne : P.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have hf : (P.relIndex H).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop)
  rw [← h1, Nat.factorization_mul hne (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply, hf,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same, zero_add, ha]

theorem card_cen_conj (g x : G) : Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) =
    Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have e : Subgroup.centralizer ({g * x * g⁻¹} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
    constructor
    · intro h
      calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h]
        _ = x * (g⁻¹ * y * g) := by group
    · intro h
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
        _ = g * x * g⁻¹ * y := by group
  rw [e, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem cen_sq_eq {x : G} (h3 : x ^ 3 = 1) :
    Subgroup.centralizer ({x ^ 2} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hx : (x ^ 2) ^ 2 = x := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
    have := (Commute.pow_right (show Commute y (x ^ 2) from h) 2).eq
    rwa [hx] at this
  · intro h
    exact (Commute.pow_right (show Commute y x from h) 2).eq

end General

section Model

open CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8 (y0 orderOf_y0 not_sq_seven_dvd eq_of_commute_y0)

theorem isElemAb_map_conj {B : Subgroup H8} (hB : IsElemAb 3 4 B) (g : H8) :
    IsElemAb 3 4 (B.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hc, hp, hcard⟩ := isElemAb_iff.mp hB
  refine isElemAb_iff.mpr ⟨?_, ?_, by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    hcard]⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group, hc x hx y hy]
    group
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hp x hx]
    group

theorem exists_eq_conj_E0 {E : Subgroup H8} (hE : IsElemAb 3 4 E) :
    ∃ g : H8, E = E0.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨hc, hp, hcard⟩ := isElemAb_iff.mp hE
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 E := IsPGroup.of_card hcard
  obtain ⟨g, hg⟩ := exists_le_conj_P0 hpg
  have hle := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le hg
  have he := eq_E0_of_le_P0 hle (isElemAb_map_conj hE g⁻¹)
  refine ⟨g, ?_⟩
  rw [← he, CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_map_conj_inv]

theorem clause1_H8 {Q : Subgroup H8} (hQ : Nat.card Q = 243) {B₁ B₂ : Subgroup H8} (h₁ : B₁ ≤ Q)
    (h₂ : B₂ ≤ Q) (hB₁ : IsElemAb 3 4 B₁) (hB₂ : IsElemAb 3 4 B₂) : B₁ = B₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 Q := IsPGroup.of_card (n := 5) (by rw [hQ]; norm_num)
  obtain ⟨g, hg⟩ := exists_le_conj_P0 hpg
  have hle := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le hg
  have e₁ := eq_E0_of_le_P0 ((Subgroup.map_mono h₁).trans hle) (isElemAb_map_conj hB₁ g⁻¹)
  have e₂ := eq_E0_of_le_P0 ((Subgroup.map_mono h₂).trans hle) (isElemAb_map_conj hB₂ g⁻¹)
  have h := congrArg (fun K => K.map (MulAut.conj g).toMonoidHom) (e₁.trans e₂.symm)
  simpa only [CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_map_conj_inv] using h

theorem normalizer_map_conj (K : Subgroup H8) (g : H8) :
    Subgroup.normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup H8) : Set H8) =
      (Subgroup.normalizer (K : Set H8)).map (MulAut.conj g).toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq K (MulAut.conj g)).symm

theorem clause2_H8 {E : Subgroup H8} (hE : IsElemAb 3 4 E) :
    Nat.card (Subgroup.normalizer (E : Set H8)) = 2 ^ 7 * 3 ^ 5 ∧
      ∀ x : H8, orderOf x = 3 → ∃ y : H8, y * x * y⁻¹ ∈ E := by
  obtain ⟨g, rfl⟩ := exists_eq_conj_E0 hE
  refine ⟨?_, fun x hx => ?_⟩
  · rw [normalizer_map_conj, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      card_normalizer_E0]
    norm_num
  · obtain ⟨y, hy⟩ := exists_conj_E0 hx
    refine ⟨g * y, ⟨y * x * y⁻¹, hy, ?_⟩⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem conj_e_of_seven_dvd {x : H8} (h3 : orderOf x = 3)
    (h7 : 7 ∣ Nat.card (Subgroup.centralizer ({x} : Set H8))) :
    ∃ v : H8, v⁻¹ * x * v = sp8E ∨ v⁻¹ * x * v = sp8E ^ 2 := by
  obtain ⟨v, hv⟩ := CFSG.RankThree.PartTwo.Sec4.RonanK429F.exists_conj_commute_of_dvd
    Nat.prime_seven orderOf_y0 not_sq_seven_dvd h7
  have hx3 : x ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one x
  have hv3 : (v⁻¹ * x * v) ^ 3 = 1 := by
    rw [show v⁻¹ * x * v = v⁻¹ * x * v⁻¹⁻¹ by rw [inv_inv], conj_pow, hx3]
    group
  rcases eq_of_commute_y0 _ hv hv3 with h | h | h
  · exfalso
    have : x = 1 := by
      calc x = v * (v⁻¹ * x * v) * v⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at h3
    norm_num at h3
  · exact ⟨v, Or.inl h⟩
  · exact ⟨v, Or.inr h⟩

theorem fixCount_inv (g : H8) : fixCount g⁻¹ = fixCount g := by
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun v => ?_)
  constructor
  · intro h
    rw [← h, matS_mulVec_mulVec, mul_inv_cancel, map_one, Matrix.one_mulVec, h]
  · intro h
    conv_lhs => rw [← h]
    rw [matS_mulVec_mulVec, inv_mul_cancel, map_one, Matrix.one_mulVec]

theorem sp8E_pow_three : sp8E ^ 3 = 1 := CFSG.RankThree.PartTwo.Sec4.RonanK432.sp8E_pow_three

theorem fixCount_e_sq : fixCount (sp8E ^ 2) = 64 := by
  have h : sp8E ^ 2 = sp8E⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, sp8E_pow_three]
  rw [h, fixCount_inv, fixCount_e]

theorem mem_l1S_of_seven_dvd {w : H8} (hw : w ∈ E0) (h3 : orderOf w = 3)
    (h7 : 7 ∣ Nat.card (Subgroup.centralizer ({w} : Set H8))) : codeS w ∈ l1S := by
  obtain ⟨v, hv⟩ := conj_e_of_seven_dvd h3 h7
  refine mem_l1S_of_fix hw ?_
  have e : w = v * (v⁻¹ * w * v) * v⁻¹ := by group
  rw [e, fixCount_conj]
  rcases hv with h | h <;> rw [h]
  · exact fixCount_e
  · exact fixCount_e_sq

theorem prod_conj_zz {w₁ w₂ : H8} {a₁ a₂ : ℕ} (ha₁ : a₁ < 8) (ha₂ : a₂ < 8)
    (e₁ : l1S.getD a₁ [] = codeS w₁) (e₂ : l1S.getD a₂ [] = codeS w₂) (hne : a₁ / 2 ≠ a₂ / 2) :
    ∃ n : H8, n * zz * n⁻¹ = w₁ * w₂ := by
  have h := cert899104_parts.2.2.2.2
  dsimp only [prodChk899104] at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  have h' := (h a₁ ha₁ a₂ ha₂).resolve_left hne
  rw [e₁, e₂, ← codeS_mul, ← codeS_zz] at h'
  obtain ⟨n, -, hn⟩ := conj_of_cfoundS n0_parts.1 h'
  exact ⟨n, hn⟩

theorem card_cen_one : Nat.card (Subgroup.centralizer ({(1 : H8)} : Set H8)) = 47377612800 := by
  rw [show Subgroup.centralizer ({(1 : H8)} : Set H8) = ⊤ by
    ext y; simp [Subgroup.mem_centralizer_singleton_iff], Subgroup.card_top, card_H8]

theorem clause3_H8 {E : Subgroup H8} (hE : IsElemAb 3 4 E) {x₁ x₂ : H8} (h₁ : x₁ ∈ E)
    (h₂ : x₂ ∈ E)
    (hc₁ : Nat.card (Subgroup.centralizer ({x₁} : Set H8)) = 2 ^ 9 * 3 ^ 5 * 5 * 7)
    (hc₂ : Nat.card (Subgroup.centralizer ({x₂} : Set H8)) = 2 ^ 9 * 3 ^ 5 * 5 * 7)
    (hne : x₂ ∉ Subgroup.zpowers x₁) :
    Nat.card (Subgroup.centralizer ({x₁ * x₂} : Set H8)) = 2 ^ 5 * 3 ^ 4 * 5 := by
  obtain ⟨g, rfl⟩ := exists_eq_conj_E0 hE
  obtain ⟨w₁, hw₁, rfl⟩ := h₁
  obtain ⟨w₂, hw₂, rfl⟩ := h₂
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc₁ hc₂ hne ⊢
  rw [card_cen_conj] at hc₁ hc₂
  have hord : ∀ {w : H8}, w ∈ E0 →
      Nat.card (Subgroup.centralizer ({w} : Set H8)) = 2 ^ 9 * 3 ^ 5 * 5 * 7 → orderOf w = 3 := by
    intro w hw hc
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime (E0_pow_three hw) fun h1 => ?_
    rw [h1, card_cen_one] at hc
    norm_num at hc
  have hl₁ := mem_l1S_of_seven_dvd hw₁ (hord hw₁ hc₁) (by rw [hc₁]; norm_num)
  have hl₂ := mem_l1S_of_seven_dvd hw₂ (hord hw₂ hc₂) (by rw [hc₂]; norm_num)
  obtain ⟨a₁, ha₁, e₁⟩ := exists_l1S_index hl₁
  obtain ⟨a₂, ha₂, e₂⟩ := exists_l1S_index hl₂
  have hlines : a₁ / 2 ≠ a₂ / 2 := by
    intro e
    apply hne
    rcases l1S_lines a₁ ha₁ a₂ ha₂ e with h | h
    · rw [e₁, e₂] at h
      rw [codeS_injective h]
      exact ⟨1, by simp⟩
    · rw [e₁, e₂, ← codeS_mul] at h
      rw [codeS_injective h]
      refine ⟨2, ?_⟩
      simp only [zpow_two]
      group
  obtain ⟨n, hn⟩ := prod_conj_zz ha₁ ha₂ e₁ e₂ hlines
  rw [show g * w₁ * g⁻¹ * (g * w₂ * g⁻¹) = g * (w₁ * w₂) * g⁻¹ by group, card_cen_conj, ← hn,
    card_cen_conj, card_cen_zz]
  norm_num

theorem card_cen_e_seven : 7 ∣ Nat.card (Subgroup.centralizer ({sp8E} : Set H8)) := by
  have hy : y0 ∈ Subgroup.centralizer ({sp8E} : Set H8) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply matS_injective
    simp only [map_mul]
    decide +kernel
  have h := Subgroup.orderOf_dvd_natCard _ hy
  rwa [orderOf_y0] at h

theorem P0_le_cen {z : H8} (hz : z ∈ E0) (ht : sp8T * z = z * sp8T) :
    P0 ≤ Subgroup.centralizer ({z} : Set H8) := by
  refine subS_le fun γ hγ => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [pGens, List.mem_cons, List.not_mem_nil, or_false] at hγ
  rcases hγ with hγ | hγ | hγ | hγ | hγ
  · rw [← codeS_z0] at hγ
    rw [codeS_injective hγ]
    exact E0_comm (sp8Z_mem_E0 0) hz
  · rw [← codeS_z1] at hγ
    rw [codeS_injective hγ]
    exact E0_comm (sp8Z_mem_E0 1) hz
  · rw [← codeS_z2] at hγ
    rw [codeS_injective hγ]
    exact E0_comm (sp8Z_mem_E0 2) hz
  · rw [← codeS_e] at hγ
    rw [codeS_injective hγ]
    exact E0_comm sp8E_mem_E0 hz
  · rw [← codeS_t] at hγ
    rw [codeS_injective hγ]
    exact ht

theorem conj_zz_of_card {x : H8} (h3 : orderOf x = 3)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set H8)) = 2 ^ 5 * 3 ^ 4 * 5) :
    ∃ h : H8, h * zz * h⁻¹ = x := by
  obtain ⟨y, hy⟩ := exists_conj_E0 h3
  have hcw : Nat.card (Subgroup.centralizer ({y * x * y⁻¹} : Set H8)) = 2 ^ 5 * 3 ^ 4 * 5 := by
    rw [card_cen_conj, hc]
  have hx : x = y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ := by group
  rcases E0_cases hy with h1 | ⟨-, -, n, -, hn | hn⟩ | ⟨-, n, -, hn⟩ | ⟨-, n, -, hn⟩ |
      ⟨-, n, -, hn⟩
  · exfalso
    rw [h1, card_cen_one] at hcw
    norm_num at hcw
  · exfalso
    rw [← hn, card_cen_conj] at hcw
    have := card_cen_e_seven
    rw [hcw] at this
    norm_num at this
  · exfalso
    rw [← hn, card_cen_conj, cen_sq_eq sp8E_pow_three] at hcw
    have := card_cen_e_seven
    rw [hcw] at this
    norm_num at this
  · exact ⟨y⁻¹ * n, by rw [hx, ← hn]; group⟩
  · exfalso
    rw [← hn, card_cen_conj] at hcw
    have h := Subgroup.card_dvd_of_le (P0_le_cen z012_mem_E0 sp8T_comm.1)
    rw [hcw, card_P0] at h
    norm_num at h
  · exfalso
    rw [← hn, card_cen_conj] at hcw
    have h := Subgroup.card_dvd_of_le (P0_le_cen z0123_mem_E0 sp8T_comm.2)
    rw [hcw, card_P0] at h
    norm_num at h

theorem clause4_H8 {t : H8} (ht : orderOf t = 2) {x : H8} (h3 : orderOf x = 3)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set H8)) = 2 ^ 5 * 3 ^ 4 * 5) :
    ∃ y : H8, y * x * y⁻¹ ∈ Subgroup.centralizer ({t} : Set H8) := by
  obtain ⟨h, rfl⟩ := conj_zz_of_card h3 hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨g, hg⟩ := exists_le_conj_U0 hp
  obtain ⟨u, huU, hut⟩ := hg (Subgroup.mem_zpowers t)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hut
  have hu2 : u * u = 1 := by
    have h2 : t * t = 1 := by
      rw [← sq]
      have := pow_orderOf_eq_one t
      rwa [ht] at this
    rw [← hut] at h2
    calc u * u = g⁻¹ * (g * u * g⁻¹ * (g * u * g⁻¹)) * g := by group
      _ = 1 := by rw [h2]; group
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [← hut, show g * 1 * g⁻¹ = 1 by group, orderOf_one] at ht
    norm_num at ht
  obtain ⟨y', hy'⟩ := exists_conj_comm_zz huU hu2 hu1
  refine ⟨g * y' * h⁻¹, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← hut]
  calc g * y' * h⁻¹ * (h * zz * h⁻¹) * (g * y' * h⁻¹)⁻¹ * (g * u * g⁻¹)
      = g * ((y' * zz * y'⁻¹) * u) * g⁻¹ := by group
    _ = g * (u * (y' * zz * y'⁻¹)) * g⁻¹ := by rw [hy']
    _ = g * u * g⁻¹ * (g * y' * h⁻¹ * (h * zz * h⁻¹) * (g * y' * h⁻¹)⁻¹) := by group

theorem clause7_H8 {U : Subgroup H8} (hU : Nat.card U = 2 ^ 16) {z₁ z₂ : H8} (h₁ : z₁ ∈ U)
    (h₂ : z₂ ∈ U) (hc₁ : ∀ u ∈ U, z₁ * u = u * z₁) (hc₂ : ∀ u ∈ U, z₂ * u = u * z₂) {y : H8}
    (hy : y * z₁ * y⁻¹ = z₂) : z₁ = z₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_le_conj_U0 (IsPGroup.of_card hU)
  have heq : U = U0.map (MulAut.conj g).toMonoidHom := Subgroup.eq_of_le_of_card_ge hg (by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_U0, hU]; norm_num)
  have hmem : ∀ {z : H8}, z ∈ U → g⁻¹ * z * g ∈ U0 := by
    intro z hz
    rw [heq] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : g⁻¹ * (g * w * g⁻¹) * g = w := by group
    rw [e]
    exact hw
  have hcen : ∀ {z : H8}, (∀ u ∈ U, z * u = u * z) →
      ∀ u ∈ U0, g⁻¹ * z * g * u = u * (g⁻¹ * z * g) := by
    intro z hz u hu
    have hu' : g * u * g⁻¹ ∈ U := by
      rw [heq]
      exact ⟨u, hu, rfl⟩
    have e := hz _ hu'
    calc g⁻¹ * z * g * u = g⁻¹ * (z * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * z) * g := by rw [e]
      _ = u * (g⁻¹ * z * g) := by group
  have h := eq_of_conj_center (hmem h₁) (hmem h₂) (hcen hc₁) (hcen hc₂) (g := g⁻¹ * y * g)
    (by rw [← hy]; group)
  calc z₁ = g * (g⁻¹ * z₁ * g) * g⁻¹ := by group
    _ = g * (g⁻¹ * z₂ * g) * g⁻¹ := by rw [h]
    _ = z₂ := by group

end Model

section CentE

open CFSG.RankThree.PartTwo.Sec4.RonanK429F
open CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8 (iota6 matH8 matH6 matH8_iota6 iota6_injective
  mem_range_iota6 commutator_mem_range_iota6 isBlockDiag_of_commute_e rho2 e8 emb6)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6 mat6 ε6 dec6 card_H6 submatrix_ε6_symm)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII (zH tH aElt mat6_zH)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (baseA vecElt)

private theorem matH6_zH (i : Fin 3) : matH6 (zH i) =
    (dec6 (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.zCode i)).submatrix ε6.symm ε6.symm := by
  rw [← mat6_zH, CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.mat6_apply, submatrix_ε6_symm]
  rfl

private theorem iota6_zH (i : Fin 3) : iota6 (zH i) = sp8Z i := by
  apply matS_injective
  show matH8 (iota6 (zH i)) = matS (sp8Z i)
  rw [matH8_iota6, matH6_zH]
  fin_cases i <;> decide +kernel

private theorem rho2_cases : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 2), A * rho2 = rho2 * A →
    A = 0 ∨ A = 1 ∨ A = rho2 ∨ A = rho2 ^ 2 := by
  decide +kernel

private theorem rho2_pow_eq_one {m : ℕ} (h : rho2 ^ m = 1) : 3 ∣ m := by
  have h3 : rho2 ^ 3 = 1 := by decide +kernel
  have hm : rho2 ^ m = rho2 ^ (m % 3) := by
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [hm] at h
  have hr : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have : m % 3 = 0 := by
    interval_cases hmod : m % 3
    · rfl
    · exact absurd h (by decide +kernel)
    · exact absurd h (by decide +kernel)
  exact Nat.dvd_of_mod_eq_zero this

private theorem mem_range_iota6_of_coprime {g : H8} (hg : g * sp8E = sp8E * g)
    (hcop : Nat.Coprime (orderOf g) 3) : g ∈ iota6.range := by
  have hX : ∀ h : H8, h * sp8E = sp8E * h → matH8 h * matH8 sp8E = matH8 sp8E * matH8 h :=
    fun h e => by rw [← map_mul, ← map_mul, e]
  have hgi : g⁻¹ * sp8E = sp8E * g⁻¹ := by
    calc g⁻¹ * sp8E = g⁻¹ * (sp8E * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * sp8E) * g⁻¹ := by rw [hg]
      _ = sp8E * g⁻¹ := by group
  obtain ⟨hbd, hrho⟩ := isBlockDiag_of_commute_e (hX g hg)
  obtain ⟨hbd', -⟩ := isBlockDiag_of_commute_e (hX g⁻¹ hgi)
  refine mem_range_iota6 g hbd hbd' ?_
  set Q := (bl e8 (matH8 g)).toBlocks₂₂
  have hpow : Q ^ orderOf g = 1 := by
    have e := congrArg (fun z => (bl e8 (matH8 z)).toBlocks₂₂) (pow_orderOf_eq_one g)
    simp only [map_pow, bl_pow, map_one, bl_one, toBlocks₂₂_one] at e
    rw [eq_fromBlocks_of_isBlockDiag hbd, fromBlocks_diag_pow] at e
    simpa using e
  have hpos : 0 < orderOf g := orderOf_pos g
  rcases rho2_cases Q hrho with h0 | h1 | h1 | h2
  · exfalso
    rw [h0, zero_pow hpos.ne'] at hpow
    exact absurd hpow (by decide)
  · exact h1
  · exfalso
    rw [h1] at hpow
    have := rho2_pow_eq_one hpow
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_eq_left this] at hcop
    norm_num at hcop
  · exfalso
    rw [h2, ← pow_mul] at hpow
    have h3 := rho2_pow_eq_one hpow
    have : 3 ∣ orderOf g := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_eq_left this] at hcop
    norm_num at hcop

private theorem iota6_range_le_cen_e : iota6.range ≤ Subgroup.centralizer ({sp8E} : Set H8) := by
  rintro _ ⟨g, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply matS_injective
  show matH8 (iota6 g * sp8E) = matH8 (sp8E * iota6 g)
  rw [map_mul, map_mul]
  apply bl_injective e8
  rw [bl_mul, bl_mul, matH8_iota6, Sp8.bl_emb6, Sp8.bl_sp8E, fromBlocks_diag_mul,
    fromBlocks_diag_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]

private theorem card_range_iota6 : Nat.card iota6.range = 1451520 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective iota6_injective).toEquiv, card_H6]

private theorem iota6_baseA_le :
    (baseA zH).map iota6 ≤ E0 := by
  rw [baseA, Subgroup.map_sup, Subgroup.map_sup]
  refine sup_le (sup_le ?_ ?_) ?_ <;> rw [MonoidHom.map_zpowers, Subgroup.zpowers_le, iota6_zH]
  · exact sp8Z_mem_E0 0
  · exact sp8Z_mem_E0 1
  · exact sp8Z_mem_E0 2

private theorem inf_cen_e_eq_bot {R : Subgroup H8} (hR : Nat.Coprime (Nat.card R) 3)
    (hE : E0 ≤ Subgroup.normalizer (R : Set H8)) :
    R ⊓ Subgroup.centralizer ({sp8E} : Set H8) = ⊥ := by
  set R' := R ⊓ Subgroup.centralizer ({sp8E} : Set H8) with hR'def
  have hR'cop : Nat.Coprime (Nat.card R') 3 :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hR
  have hle : R' ≤ iota6.range := fun g hg =>
    mem_range_iota6_of_coprime (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
      (Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard R' hg) hR'cop)
  set Y := R'.comap iota6 with hYdef
  have hY : Y.map iota6 = R' := Subgroup.map_comap_eq_self hle
  have hYcard : Nat.card Y = Nat.card R' := by
    conv_rhs => rw [← hY]
    rw [Subgroup.card_map_of_injective iota6_injective]
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    rw [hYcard]
    intro h
    have := Nat.Coprime.coprime_dvd_right h hR'cop.symm
    norm_num at this
  have hA : baseA zH ≤ Subgroup.normalizer (Y : Set H6) := by
    intro a ha
    have hN := hE (iota6_baseA_le ⟨a, ha, rfl⟩)
    have hC : iota6 a ∈ Subgroup.centralizer ({sp8E} : Set H8) := iota6_range_le_cen_e ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [hYdef, Subgroup.mem_comap, map_mul, map_inv, hR'def, Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hN _).mp h1,
        mul_mem (mul_mem hC h2) (inv_mem hC)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hN _).mpr h1, ?_⟩
      have e : iota6 y = (iota6 a)⁻¹ * (iota6 a * iota6 y * (iota6 a)⁻¹) * iota6 a := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hC) h2) hC
  have hbot := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.eq_bot_of_baseA_le_normalizer hY3 hA
  rw [← hY, hbot, Subgroup.map_bot]

theorem mul_self_eq_inv_of_E0 {w : H8} (hw : w ∈ E0) : w * w = w⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_three']
  exact E0_pow_three hw

theorem fixCount_of_mem_l1S {h : H8} (hc : codeS h ∈ l1S) : fixCount h = 64 := by
  have key : ∀ i : Fin 4, codeS h = codeS (zE i) ∨ codeS h = codeS (zE i * zE i) →
      fixCount h = 64 := by
    rintro i (e | e) <;> rw [codeS_injective e]
    · exact fixCount_zE i
    · rw [mul_self_eq_inv_of_E0 (zE_mem_E0 i), fixCount_inv, fixCount_zE]
  simp only [l1S, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with e | e | e | e | e | e | e | e
  · exact key 0 (Or.inl (e.trans (codeS_zE 0).symm))
  · exact key 0 (Or.inr (by rw [e, codeS_mul, codeS_zE]; rfl))
  · exact key 1 (Or.inl (e.trans (codeS_zE 1).symm))
  · exact key 1 (Or.inr (by rw [e, codeS_mul, codeS_zE]; rfl))
  · exact key 2 (Or.inl (e.trans (codeS_zE 2).symm))
  · exact key 2 (Or.inr (by rw [e, codeS_mul, codeS_zE]; rfl))
  · exact key 3 (Or.inl (e.trans (codeS_zE 3).symm))
  · exact key 3 (Or.inr (by rw [e, codeS_mul, codeS_zE]; rfl))

private theorem eq_one_of_comm_type1 {R : Subgroup H8} (hR : Nat.Coprime (Nat.card R) 3)
    (hE : E0 ≤ Subgroup.normalizer (R : Set H8)) {z : H8} (hz : z ∈ E0) (hfix : fixCount z = 64)
    {y : H8} (hy : y ∈ R) (hyz : y * z = z * y) : y = 1 := by
  obtain ⟨n, hnN, hn⟩ : ∃ n ∈ N0, n * sp8E * n⁻¹ = z ∨ n * sp8E ^ 2 * n⁻¹ = z := by
    rcases E0_cases hz with h1 | ⟨-, -, hn⟩ | ⟨h16, -⟩ | ⟨h4, -⟩ | ⟨h1', -⟩
    · rw [h1, fixCount_one] at hfix; norm_num at hfix
    · exact hn
    · rw [hfix] at h16; norm_num at h16
    · rw [hfix] at h4; norm_num at h4
    · rw [hfix] at h1'; norm_num at h1'
  have hnorm := N0_le_normalizer hnN
  set R' := R.map (MulAut.conj n⁻¹).toMonoidHom
  have hR' : Nat.Coprime (Nat.card R') 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective]
    exact hR
  have hE' : E0 ≤ Subgroup.normalizer (R' : Set H8) := by
    intro a ha
    have ha' : n * a * n⁻¹ ∈ E0 := (Subgroup.mem_normalizer_iff.mp hnorm a).mp ha
    have hN := hE ha'
    rw [Subgroup.mem_normalizer_iff]
    intro r
    simp only [R', Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    rw [Subgroup.mem_normalizer_iff] at hN
    rw [hN (n * r * n⁻¹)]
    constructor
    · intro h
      convert h using 1
      group
    · intro h
      convert h using 1
      group
  have hbot := inf_cen_e_eq_bot hR' hE'
  have hmem : n⁻¹ * y * n ∈ R' ⊓ Subgroup.centralizer ({sp8E} : Set H8) := by
    refine Subgroup.mem_inf.mpr ⟨⟨y, hy, by simp [MulAut.conj_apply]⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyz' : y * z * y⁻¹ = z := by rw [hyz]; group
    rcases hn with e | e
    · rw [← e] at hyz
      calc n⁻¹ * y * n * sp8E = n⁻¹ * (y * (n * sp8E * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * sp8E * n⁻¹) * y) * n := by rw [hyz]
        _ = sp8E * (n⁻¹ * y * n) := by group
    · have hc : (n⁻¹ * y * n) * sp8E ^ 2 = sp8E ^ 2 * (n⁻¹ * y * n) := by
        rw [← e] at hyz
        calc n⁻¹ * y * n * sp8E ^ 2 = n⁻¹ * (y * (n * sp8E ^ 2 * n⁻¹)) * n := by group
          _ = n⁻¹ * ((n * sp8E ^ 2 * n⁻¹) * y) * n := by rw [hyz]
          _ = sp8E ^ 2 * (n⁻¹ * y * n) := by group
      have hm : n⁻¹ * y * n ∈ Subgroup.centralizer ({sp8E ^ 2} : Set H8) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hc
      rw [cen_sq_eq sp8E_pow_three] at hm
      exact Subgroup.mem_centralizer_singleton_iff.mp hm
  rw [hbot, Subgroup.mem_bot] at hmem
  calc y = n * (n⁻¹ * y * n) * n⁻¹ := by group
    _ = 1 := by rw [hmem]; group

private theorem fl1_conj_z0 : fl1 * sp8Z 0 * fl1⁻¹ = sp8Z 0 := by
  rw [fl1_comm_z0]; group

private theorem fl1_conj_z2 : fl1 * sp8Z 2 * fl1⁻¹ = sp8Z 2 := by
  rw [fl1_comm_z2]; group

private theorem fl1_conj_e : fl1 * sp8E * fl1⁻¹ = sp8E := by
  rw [fl1_comm_e]; group

theorem conj_mul' (g a b : H8) : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group

private theorem fl1_mem_normalizer : fl1 ∈ Subgroup.normalizer (E0 : Set H8) := by
  refine mem_normalizer_of_map_le ?_
  change (Subgroup.closure {g | codeS g ∈ e0Gens}).map _ ≤ E0
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨z, hz, rfl⟩
  simp only [Set.mem_setOf_eq, e0Gens, List.mem_cons, List.not_mem_nil, or_false] at hz
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rcases hz with h | h | h | h
  · rw [← codeS_z0] at h; rw [codeS_injective h, fl1_conj_z0]; exact sp8Z_mem_E0 0
  · rw [← codeS_z1] at h
    rw [codeS_injective h, fl1_conj_z1]
    exact mul_mem (sp8Z_mem_E0 1) (sp8Z_mem_E0 1)
  · rw [← codeS_z2] at h; rw [codeS_injective h, fl1_conj_z2]; exact sp8Z_mem_E0 2
  · rw [← codeS_e] at h; rw [codeS_injective h, fl1_conj_e]; exact sp8E_mem_E0

private theorem E9_le_cen_fl1 {i : ℕ} (hi : i = 0 ∨ i = 2) :
    E9 i 3 ≤ Subgroup.centralizer ({fl1} : Set H8) := by
  refine subS_le fun g hg => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h
  · rcases hi with rfl | rfl
    · rw [show e0Gens.getD 0 [] = z0S from rfl, ← codeS_z0] at h
      rw [codeS_injective h, fl1_comm_z0]
    · rw [show e0Gens.getD 2 [] = z2S from rfl, ← codeS_z2] at h
      rw [codeS_injective h, fl1_comm_z2]
  · rw [show e0Gens.getD 3 [] = z3S from rfl, ← codeS_e] at h
    rw [codeS_injective h, fl1_comm_e]

private theorem mem_E0_of_cz {y h23 h03 : H8} (hy : y ∈ CZ) (c23 : codeS h23 ∈ w2S 2 3)
    (c03 : codeS h03 ∈ w2S 0 3) (y23 : y * h23 = h23 * y) (y03 : y * h03 = h03 * y) : y ∈ E0 := by
  have hc := allCheck_mem cz_parts.1 hyp_parts hy
  have h := List.all_eq_true.mp (List.all_eq_true.mp hc _ c23) _ c03
  have e1 : commS (codeS y) (codeS h23) = true := by simpa [commS] using codeS_comm y23
  have e2 : commS (codeS y) (codeS h03) = true := by simpa [commS] using codeS_comm y03
  rw [e1, e2] at h
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h
  exact mem_subS_of_found e0_parts.1 h

private theorem mem_E0_of_comm_hyp {y h01 h23 h03 : H8} (c01 : codeS h01 ∈ w2S 0 1)
    (c23 : codeS h23 ∈ w2S 2 3) (c03 : codeS h03 ∈ w2S 0 3) (m23 : h23 ∈ E9 2 3)
    (m03 : h03 ∈ E9 0 3) (y01 : y * h01 = h01 * y) (y23 : y * h23 = h23 * y)
    (y03 : y * h03 = h03 * y) : y ∈ E0 := by
  have hcz : ∀ y' : H8, y' * zz = zz * y' → y' * h23 = h23 * y' → y' * h03 = h03 * y' →
      y' ∈ E0 := fun y' h0 h2 h3 =>
    mem_E0_of_cz (by rw [← cen_zz_eq]; exact Subgroup.mem_centralizer_singleton_iff.mpr h0) c23 c03
      h2 h3
  have hzz3 : zz ^ 3 = 1 := E0_pow_three zz_mem_E0
  have hcz2 : ∀ y' : H8, y' * zz ^ 2 = zz ^ 2 * y' → y' * zz = zz * y' := fun y' h => by
    have hm : y' ∈ Subgroup.centralizer ({zz ^ 2} : Set H8) :=
      Subgroup.mem_centralizer_singleton_iff.mpr h
    rw [cen_sq_eq hzz3] at hm
    exact Subgroup.mem_centralizer_singleton_iff.mp hm
  have hc01 : sp8Z 0 * sp8Z 1 = sp8Z 1 * sp8Z 0 := E0_comm (sp8Z_mem_E0 0) (sp8Z_mem_E0 1)
  have hzz2 : zz ^ 2 = sp8Z 0 * sp8Z 0 * (sp8Z 1 * sp8Z 1) := by
    calc zz ^ 2 = sp8Z 0 * (sp8Z 1 * sp8Z 0) * sp8Z 1 := by rw [zz, pow_two]; group
      _ = sp8Z 0 * (sp8Z 0 * sp8Z 1) * sp8Z 1 := by rw [← hc01]
      _ = sp8Z 0 * sp8Z 0 * (sp8Z 1 * sp8Z 1) := by group
  have hz1 : sp8Z 1 * sp8Z 1 * (sp8Z 1 * sp8Z 1) = sp8Z 1 := by
    have h := E0_pow_three (sp8Z_mem_E0 1)
    calc sp8Z 1 * sp8Z 1 * (sp8Z 1 * sp8Z 1) = sp8Z 1 ^ 3 * sp8Z 1 := by
          rw [pow_three]; group
      _ = sp8Z 1 := by rw [h, one_mul]
  have hfl : ∀ a : H8, y * a = a * y →
      fl1 * y * fl1⁻¹ * (fl1 * a * fl1⁻¹) = fl1 * a * fl1⁻¹ * (fl1 * y * fl1⁻¹) := by
    intro a e
    rw [show fl1 * y * fl1⁻¹ * (fl1 * a * fl1⁻¹) = fl1 * (y * a) * fl1⁻¹ by group, e]
    group
  have hfix : ∀ a ∈ Subgroup.centralizer ({fl1} : Set H8), fl1 * a * fl1⁻¹ = a := fun a ha => by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp ha]; group
  have h23' : fl1 * h23 * fl1⁻¹ = h23 := hfix _ (E9_le_cen_fl1 (Or.inr rfl) m23)
  have h03' : fl1 * h03 * fl1⁻¹ = h03 := hfix _ (E9_le_cen_fl1 (Or.inl rfl) m03)
  have hflip : fl1 * y * fl1⁻¹ ∈ E0 → y ∈ E0 := fun h => by
    have e : y = fl1⁻¹ * (fl1 * y * fl1⁻¹) * fl1⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (inv_mem fl1_mem_normalizer) _).mp h
  have y23' := hfl _ y23
  have y03' := hfl _ y03
  rw [h23'] at y23'
  rw [h03'] at y03'
  have hw : w2S 0 1 = [codeS (sp8Z 0 * sp8Z 1), codeS (sp8Z 0 * (sp8Z 1 * sp8Z 1)),
      codeS (sp8Z 0 * sp8Z 0 * sp8Z 1), codeS (sp8Z 0 * sp8Z 0 * (sp8Z 1 * sp8Z 1))] := by
    simp only [codeS_mul, codeS_z0, codeS_z1]
    rfl
  rw [hw] at c01
  simp only [List.mem_cons, List.not_mem_nil, or_false] at c01
  rcases c01 with e | e | e | e <;> rw [codeS_injective e] at y01
  · exact hcz y y01 y23 y03
  ·
    have h := hfl _ y01
    rw [conj_mul', conj_mul', fl1_conj_z0, fl1_conj_z1, hz1] at h
    exact hflip (hcz _ h y23' y03')
  ·
    have h := hfl _ y01
    rw [conj_mul', conj_mul', fl1_conj_z0, fl1_conj_z1, ← hzz2] at h
    exact hflip (hcz _ (hcz2 _ h) y23' y03')
  · exact hcz y (hcz2 y (by rw [hzz2]; exact y01)) y23 y03

theorem clause6_H8 {x : H8} (h3 : orderOf x = 3) {R : Subgroup H8}
    (hN : Subgroup.centralizer ({x} : Set H8) ≤ Subgroup.normalizer (R : Set H8))
    (hcop : (Nat.card R).Coprime 3) : R = ⊥ := by
  obtain ⟨y, hy⟩ := exists_conj_E0 h3
  set w := y * x * y⁻¹ with hwdef
  set R' := R.map (MulAut.conj y).toMonoidHom with hR'def
  have hR'cop : (Nat.card R').Coprime 3 := by
    rw [hR'def, Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact hcop
  have hE : E0 ≤ Subgroup.normalizer (R' : Set H8) := by
    intro a ha
    have haw : a * w = w * a := E0_comm ha hy
    have ha' : y⁻¹ * a * y ∈ Subgroup.centralizer ({x} : Set H8) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc y⁻¹ * a * y * x = y⁻¹ * (a * w) * y := by rw [hwdef]; group
        _ = y⁻¹ * (w * a) * y := by rw [haw]
        _ = x * (y⁻¹ * a * y) := by rw [hwdef]; group
    have hNR := hN ha'
    rw [Subgroup.mem_normalizer_iff] at hNR ⊢
    intro r
    simp only [hR'def, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [hNR (y⁻¹ * r * y)]
    constructor
    · intro h
      convert h using 1
      group
    · intro h
      convert h using 1
      group
  have hV : CFSG.Open.IsElemAbelian 3 E0 :=
    ⟨isElementaryAbelian_E0.toIsMulCommutative, fun z hz => E0_pow_three hz⟩
  have hR' : R' = ⊥ := by
    rw [eq_bot_iff]
    refine CFSG.RankThree.PartTwo.Sec5.le_of_forall_inf_centralizer_sub_le (k := 3)
      Nat.prime_three hV (by rw [card_E0]; norm_num) hE hR'cop.symm fun H hHE hH => ?_
    intro z hz
    obtain ⟨hzR, hzC⟩ := Subgroup.mem_inf.mp hz
    have hzH : ∀ h ∈ H, z * h = h * z := fun h hh =>
      (Subgroup.mem_centralizer_iff.mp hzC h hh).symm
    rw [Subgroup.mem_bot]
    obtain ⟨h01, m01, e01, c01⟩ := exists_mem_E9 hHE hH (i := 0) (j := 1) (by simp)
      (by norm_num) (by norm_num)
    obtain ⟨h23, m23, e23, c23⟩ := exists_mem_E9 hHE hH (i := 2) (j := 3) (by simp)
      (by norm_num) (by norm_num)
    obtain ⟨h03, m03, e03, c03⟩ := exists_mem_E9 hHE hH (i := 0) (j := 3) (by simp)
      (by norm_num) (by norm_num)
    rcases c01 with c01 | c01
    · exact eq_one_of_comm_type1 hR'cop hE (hHE m01) (fixCount_of_mem_l1S c01) hzR (hzH _ m01)
    rcases c23 with c23 | c23
    · exact eq_one_of_comm_type1 hR'cop hE (hHE m23) (fixCount_of_mem_l1S c23) hzR (hzH _ m23)
    rcases c03 with c03 | c03
    · exact eq_one_of_comm_type1 hR'cop hE (hHE m03) (fixCount_of_mem_l1S c03) hzR (hzH _ m03)
    have hzE : z ∈ E0 :=
      mem_E0_of_comm_hyp c01 c23 c03 e23 e03 (hzH _ m01) (hzH _ m23) (hzH _ m03)
    have h1 : orderOf z ∣ Nat.card R' := Subgroup.orderOf_dvd_natCard _ hzR
    have h2 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (E0_pow_three hzE)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hR'cop) h2)
  rw [eq_bot_iff]
  intro r hr
  have hm : y * r * y⁻¹ ∈ R' := ⟨r, hr, rfl⟩
  rw [hR', Subgroup.mem_bot] at hm
  rw [Subgroup.mem_bot]
  calc r = y⁻¹ * (y * r * y⁻¹) * y := by group
    _ = 1 := by rw [hm]; group

end CentE

section H6Classes

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit

private theorem syl_spec6 : ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ j < 3,
    (zH 0 ^ a * zH 1 ^ b * zH 2 ^ c * Sec4.Item434SmallTwoIII.tH ^ j) ^ 3 = 1 →
    zH 0 ^ a * zH 1 ^ b * zH 2 ^ c * Sec4.Item434SmallTwoIII.tH ^ j ≠ 1 →
    (∃ g : H6, zH 0 ^ a * zH 1 ^ b * zH 2 ^ c * Sec4.Item434SmallTwoIII.tH ^ j = g * zH 1 * g⁻¹) ∨
      (∃ g : H6, zH 0 ^ a * zH 1 ^ b * zH 2 ^ c * Sec4.Item434SmallTwoIII.tH ^ j = g * (zH 0 * zH 1) * g⁻¹) ∨
      (∃ g : H6, zH 0 ^ a * zH 1 ^ b * zH 2 ^ c * Sec4.Item434SmallTwoIII.tH ^ j = g * (zH 0 * zH 1 * zH 2) * g⁻¹) := by
  obtain ⟨⟨⟨s, hs⟩, ⟨f0, hf0⟩, ⟨f2, hf2⟩, hq⟩, h⟩ := Certificates.certificate899101
  choose q hq using hq
  exact (h zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH s f0 f2 q mat6_zH mat6_tH hs hf0 hf2 hq).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem exists_conj_rep_H6 {a : H6} (ha : orderOf a = 3) : ∃ m : H6, m * a * m⁻¹ = zH 1 ∨
    m * a * m⁻¹ = aElt 3 ∨ m * a * m⁻¹ = vecElt zH ![1, 1, 1] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH) (by rw [card_wreathW_zH, factorization_card_H6]; norm_num) hp
  obtain ⟨w, hw, hgw⟩ := hg (Subgroup.mem_zpowers a)
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgw
  obtain ⟨v, j, rfl⟩ := mem_wreathW wreathFacts_zH hw
  have hw3 : orderOf (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ)) = 3 := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgw, ha] at h
    exact h.symm
  have hw3' : (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ)) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))
    rwa [hw3] at h
  have h1 : vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hw3
    exact absurd hw3 (by norm_num)
  have fin : ∀ y : H6, (∃ h : H6, vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) = h * y * h⁻¹) →
      ∃ m : H6, m * a * m⁻¹ = y := by
    rintro y ⟨h, hh⟩
    refine ⟨(g * h)⁻¹, ?_⟩
    rw [← hgw, hh]
    group
  have e3 : zH 0 * zH 1 = aElt 3 := by
    change _ = zH 0 ^ 1 * zH 1 ^ 1 * zH 2 ^ 0
    rw [pow_zero, pow_one, pow_one, mul_one]
  have e111 : zH 0 * zH 1 * zH 2 = vecElt zH ![1, 1, 1] := by
    change _ = zH 0 ^ 1 * zH 1 ^ 1 * zH 2 ^ 1
    rw [pow_one, pow_one, pow_one]
  rcases syl_spec6 _ (ZMod.val_lt (v 0)) _ (ZMod.val_lt (v 1)) _ (ZMod.val_lt (v 2)) _ j.2 hw3'
    h1 with h | h | h
  · exact (fin _ h).imp fun _ => Or.inl
  · rw [e3] at h
    exact (fin _ h).imp fun _ => Or.inr ∘ Or.inl
  · rw [e111] at h
    exact (fin _ h).imp fun _ => Or.inr ∘ Or.inr

end H6Classes

section Clause5

open CFSG.RankThree.PartTwo.Sec4.RonanK429F
open CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8 (iota6 iota6_injective commutator_mem_range_iota6)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6 card_H6)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII (zH aElt)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

private theorem iota6_aElt3 : iota6 (aElt 3) = zz := by
  show iota6 (zH 0 ^ (1 : ZMod 3).val * zH 1 ^ (1 : ZMod 3).val * zH 2 ^ (0 : ZMod 3).val) = zz
  rw [show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_one,
    pow_zero, mul_one, map_mul, iota6_zH, iota6_zH, zz]

private theorem iota6_vec111 : iota6 (vecElt zH ![1, 1, 1]) = z012 := by
  show iota6 (zH 0 ^ (1 : ZMod 3).val * zH 1 ^ (1 : ZMod 3).val * zH 2 ^ (1 : ZMod 3).val) = z012
  rw [show (1 : ZMod 3).val = 1 from rfl, pow_one, pow_one, pow_one, map_mul, map_mul, iota6_zH,
    iota6_zH, iota6_zH, z012, zz]

private theorem fixCount_iota6_rep {a : H6} (ha : orderOf a = 3) :
    ∃ m : H6, (m * a * m⁻¹ = zH 1 ∧ fixCount (iota6 a) = 64) ∨
      (m * a * m⁻¹ = aElt 3 ∧ fixCount (iota6 a) = 16) ∨
      (m * a * m⁻¹ = vecElt zH ![1, 1, 1] ∧ fixCount (iota6 a) = 4) := by
  obtain ⟨m, h⟩ := exists_conj_rep_H6 ha
  have key : ∀ r : H6, m * a * m⁻¹ = r → fixCount (iota6 a) = fixCount (iota6 r) := by
    intro r e
    rw [← e, map_mul, map_mul, map_inv, fixCount_conj]
  refine ⟨m, ?_⟩
  rcases h with h | h | h
  · exact Or.inl ⟨h, by rw [key _ h, iota6_zH]; exact fixCount_zE 1⟩
  · exact Or.inr (Or.inl ⟨h, by rw [key _ h, iota6_aElt3, fixCount_zz]⟩)
  · exact Or.inr (Or.inr ⟨h, by rw [key _ h, iota6_vec111, fixCount_z012]⟩)

private theorem conj_H6_of_fixCount {a₁ a₂ : H6} (h₁ : orderOf a₁ = 3) (h₂ : orderOf a₂ = 3)
    (hf : fixCount (iota6 a₁) = fixCount (iota6 a₂)) : ∃ m : H6, m * a₁ * m⁻¹ = a₂ := by
  obtain ⟨m₁, h₁'⟩ := fixCount_iota6_rep h₁
  obtain ⟨m₂, h₂'⟩ := fixCount_iota6_rep h₂
  have conj : ∀ r : H6, m₁ * a₁ * m₁⁻¹ = r → m₂ * a₂ * m₂⁻¹ = r →
      ∃ m : H6, m * a₁ * m⁻¹ = a₂ := fun r e₁ e₂ =>
    ⟨m₂⁻¹ * m₁, by
      calc m₂⁻¹ * m₁ * a₁ * (m₂⁻¹ * m₁)⁻¹ = m₂⁻¹ * (m₁ * a₁ * m₁⁻¹) * m₂ := by group
        _ = m₂⁻¹ * (m₂ * a₂ * m₂⁻¹) * m₂ := by rw [e₁, e₂]
        _ = a₂ := by group⟩
  rcases h₁' with ⟨e₁, f₁⟩ | ⟨e₁, f₁⟩ | ⟨e₁, f₁⟩ <;>
    rcases h₂' with ⟨e₂, f₂⟩ | ⟨e₂, f₂⟩ | ⟨e₂, f₂⟩
  · exact conj _ e₁ e₂
  · rw [f₁, f₂] at hf; norm_num at hf
  · rw [f₁, f₂] at hf; norm_num at hf
  · rw [f₁, f₂] at hf; norm_num at hf
  · exact conj _ e₁ e₂
  · rw [f₁, f₂] at hf; norm_num at hf
  · rw [f₁, f₂] at hf; norm_num at hf
  · rw [f₁, f₂] at hf; norm_num at hf
  · exact conj _ e₁ e₂

theorem clause5_H8 {x : H8} (h3 : orderOf x = 3) {K : Subgroup H8}
    (hK : K ≤ Subgroup.centralizer ({x} : Set H8)) (hperf : Group.IsPerfect K)
    (hcard : Nat.card K = 1451520) {x₁ x₂ : H8} (h₁ : x₁ ∈ K) (h₂ : x₂ ∈ K)
    (h13 : orderOf x₁ = 3) {y : H8} (hy : y * x₁ * y⁻¹ = x₂) : ∃ k ∈ K, k * x₁ * k⁻¹ = x₂ := by
  have h7 : 7 ∣ Nat.card (Subgroup.centralizer ({x} : Set H8)) :=
    (show 7 ∣ Nat.card K by rw [hcard]; norm_num).trans (Subgroup.card_dvd_of_le hK)
  obtain ⟨v, hv⟩ := conj_e_of_seven_dvd h3 h7
  set K' := K.map (MulAut.conj v⁻¹).toMonoidHom with hK'def
  have hK'e : K' ≤ Subgroup.centralizer ({sp8E} : Set H8) := by
    rintro _ ⟨k, hk, rfl⟩
    have hkx := Subgroup.mem_centralizer_singleton_iff.mp (hK hk)
    have hc : v⁻¹ * k * v ∈ Subgroup.centralizer ({v⁻¹ * x * v} : Set H8) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc v⁻¹ * k * v * (v⁻¹ * x * v) = v⁻¹ * (k * x) * v := by group
        _ = v⁻¹ * (x * k) * v := by rw [hkx]
        _ = v⁻¹ * x * v * (v⁻¹ * k * v) := by group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rcases hv with e | e
    · rwa [e] at hc
    · rwa [e, cen_sq_eq sp8E_pow_three] at hc
  have hperf' : Group.IsPerfect K' :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.equivMapOfInjective K _ (MulAut.conj v⁻¹).injective).toMonoidHom)
      (Subgroup.equivMapOfInjective K _ (MulAut.conj v⁻¹).injective).surjective
  have hK'le : K' ≤ iota6.range :=
    le_of_commutator_mem (fun a ha b hb => commutator_mem_range_iota6 a ha b hb) hK'e hperf'
  have hK'eq : K' = iota6.range := Subgroup.eq_of_le_of_card_ge hK'le (by
    rw [card_range_iota6, hK'def, Subgroup.card_map_of_injective (MulAut.conj v⁻¹).injective,
      hcard])
  have hmem : ∀ {z : H8}, z ∈ K → v⁻¹ * z * v ∈ iota6.range := fun {z} hz => by
    rw [← hK'eq]
    exact ⟨z, hz, by simp [MulAut.conj_apply]⟩
  obtain ⟨a₁, ha₁⟩ := hmem h₁
  obtain ⟨a₂, ha₂⟩ := hmem h₂
  have hord : ∀ {a : H6} {z : H8}, iota6 a = v⁻¹ * z * v → orderOf z = 3 → orderOf a = 3 := by
    intro a z e hz
    rw [← orderOf_injective iota6 iota6_injective a, e, ← hz]
    exact orderOf_injective (MulAut.conj v⁻¹).toMonoidHom (MulAut.conj v⁻¹).injective z |>.trans
      (by simp [MulAut.conj_apply])
  have h23 : orderOf x₂ = 3 := by
    rw [← hy, ← h13]
    exact orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective x₁
  have hfc : ∀ z : H8, fixCount (v⁻¹ * z * v) = fixCount z := fun z => by
    simpa using fixCount_conj z v⁻¹
  have hf : fixCount (iota6 a₁) = fixCount (iota6 a₂) := by
    rw [ha₁, ha₂, hfc, hfc, ← hy, fixCount_conj]
  obtain ⟨m, hm⟩ := conj_H6_of_fixCount (hord ha₁ h13) (hord ha₂ h23) hf
  obtain ⟨k, hk, hkv⟩ : ∃ k ∈ K, v⁻¹ * k * v = iota6 m := by
    have : iota6 m ∈ K' := by rw [hK'eq]; exact ⟨m, rfl⟩
    obtain ⟨k, hk, e⟩ := this
    exact ⟨k, hk, by simpa [MulAut.conj_apply] using e⟩
  refine ⟨k, hk, ?_⟩
  have e := congrArg iota6 hm
  rw [map_mul, map_mul, map_inv, ha₁, ha₂, ← hkv] at e
  calc k * x₁ * k⁻¹ = v * ((v⁻¹ * k * v) * (v⁻¹ * x₁ * v) * (v⁻¹ * k * v)⁻¹) * v⁻¹ := by group
    _ = v * (v⁻¹ * x₂ * v) * v⁻¹ := by rw [e]
    _ = x₂ := by group

end Clause5

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

def KF_Sp8Local' : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X), StatedClassicalModel ↥Y .PSp 4 2 1 →
    (∀ Q : Subgroup X, IsSylowOf 3 Q Y → ∀ B₁ B₂ : Subgroup X, B₁ ≤ Q → B₂ ≤ Q →
      IsElemAb 3 4 B₁ → IsElemAb 3 4 B₂ → B₁ = B₂) ∧
    (∀ E : Subgroup X, E ≤ Y → IsElemAb 3 4 E → Nat.card ↥(Y ⊓ Nor E) = 2 ^ 7 * 3 ^ 5 ∧
      ∀ x ∈ Y, orderOf x = 3 → ∃ y ∈ Y, y * x * y⁻¹ ∈ E) ∧
    (∀ E : Subgroup X, E ≤ Y → IsElemAb 3 4 E → ∀ x₁ ∈ E, ∀ x₂ ∈ E,
      Nat.card ↥(Y ⊓ Cen x₁) = 2 ^ 9 * 3 ^ 5 * 5 * 7 →
      Nat.card ↥(Y ⊓ Cen x₂) = 2 ^ 9 * 3 ^ 5 * 5 * 7 → x₂ ∉ Subgroup.zpowers x₁ →
      Nat.card ↥(Y ⊓ Cen (x₁ * x₂)) = 2 ^ 5 * 3 ^ 4 * 5) ∧
    (∀ t ∈ Y, orderOf t = 2 → ∀ x ∈ Y, orderOf x = 3 → Nat.card ↥(Y ⊓ Cen x) = 2 ^ 5 * 3 ^ 4 * 5 →
      ∃ y ∈ Y, y * x * y⁻¹ ∈ Cen t) ∧
    (∀ x ∈ Y, orderOf x = 3 → ∀ K : Subgroup X, K ≤ Y → Subgroup.zpowers x ⊔ K = Y ⊓ Cen x →
      StatedClassicalModel K .PSp 3 2 1 → ∀ x₁ ∈ K, ∀ x₂ ∈ K, orderOf x₁ = 3 →
      (∃ y ∈ Y, y * x₁ * y⁻¹ = x₂) → ∃ k ∈ K, k * x₁ * k⁻¹ = x₂) ∧
    (∀ x ∈ Y, orderOf x = 3 → ∀ R : Subgroup X, R ≤ Y ⊓ Cen x → Y ⊓ Cen x ≤ Nor R →
      (Nat.card R).Coprime 3 → R = ⊥) ∧
    ∀ U : Subgroup X, IsSylowOf 2 U Y → ∀ z₁ ∈ U, ∀ z₂ ∈ U, (∀ u ∈ U, z₁ * u = u * z₁) →
      (∀ u ∈ U, z₂ * u = u * z₂) → (∃ y ∈ Y, y * z₁ * y⁻¹ = z₂) → z₁ = z₂

end CFSG.RankThree.PartTwo.Sec21.FF81

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

open CFSG.RankThree.PartTwo.Sec4.RonanK432 (H8)
open CFSG.RankThree.PartTwo.Sec21.FF79 (IsElemAb IsSylowOf Cen Nor)

section Transport

variable {H X : Type} [Group H] [Group X] {f : H →* X}

theorem map_cen_eq (hf : Function.Injective f) (a : H) :
    (Subgroup.centralizer ({a} : Set H)).map f =
      f.range ⊓ Subgroup.centralizer ({f a} : Set X) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← map_mul, hc, map_mul]
  · rintro ⟨⟨c, rfl⟩, hc⟩
    refine ⟨c, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    exact hf (by rw [map_mul, hc, map_mul])

theorem map_nor_eq (hf : Function.Injective f) (B : Subgroup H) :
    (Subgroup.normalizer (B : Set H)).map f =
      f.range ⊓ Subgroup.normalizer ((B.map f : Subgroup X) : Set X) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, ?_⟩
    rw [Subgroup.mem_normalizer_iff] at hc ⊢
    intro x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨c * b * c⁻¹, (hc b).mp hb, by simp [map_mul, map_inv]⟩
    · rintro ⟨b, hb, e⟩
      refine ⟨c⁻¹ * b * c, ?_, ?_⟩
      · have := (hc (c⁻¹ * b * c)).mpr
        exact this (by rwa [show c * (c⁻¹ * b * c) * c⁻¹ = b by group])
      · rw [map_mul, map_mul, map_inv, e]
        group
  · rintro ⟨⟨c, rfl⟩, hc⟩
    refine ⟨c, ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hc ⊢
    intro b
    have h := hc (f b)
    constructor
    · intro hb
      obtain ⟨b', hb', e⟩ := h.mp ⟨b, hb, rfl⟩
      have : b' = c * b * c⁻¹ := hf (by rw [e, map_mul, map_mul, map_inv])
      rwa [← this]
    · intro hb
      obtain ⟨b', hb', e⟩ := h.mpr ⟨c * b * c⁻¹, hb, by simp [map_mul, map_inv]⟩
      rwa [← hf e]

theorem card_comap_eq (hf : Function.Injective f) {A : Subgroup X} (hA : A ≤ f.range) :
    Nat.card (A.comap f) = Nat.card A := by
  conv_rhs => rw [← Subgroup.map_comap_eq_self hA]
  rw [Subgroup.card_map_of_injective hf]

theorem isElemAb_comap (hf : Function.Injective f) {p k : ℕ} {A : Subgroup X}
    (hA : A ≤ f.range) (h : IsElemAb p k A) : IsElemAb p k (A.comap f) := by
  obtain ⟨hc, hp, hcard⟩ := isElemAb_iff.mp h
  refine isElemAb_iff.mpr ⟨fun x hx y hy => hf (by rw [map_mul, map_mul, hc _ hx _ hy]),
    fun x hx => hf (by rw [map_pow, hp _ hx, map_one]), by rw [card_comap_eq hf hA, hcard]⟩

end Transport

theorem nonempty_mulEquiv_H8_of_stated {K : Type} [Group K]
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSp 4 2 1) : Nonempty (K ≃* H8) := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : F ≃+* ZMod 2 :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 1 one_pos hcard).trans
      (GaloisField.equivZmodP 2).toRingEquiv
  exact ⟨e.trans ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ 4)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans
      CFSG.RankThree.PartTwo.Sec4.RonanK432.statedProjSp8Equiv)⟩

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp8
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (H8)

theorem kf_sp8Local' : KF_Sp8Local' := by
  intro X _ _ Y hY
  classical
  obtain ⟨θ⟩ := nonempty_mulEquiv_H8_of_stated hY
  set f : H8 →* X := Y.subtype.comp θ.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp θ.symm.injective
  have hfθ : ∀ x (hx : x ∈ Y), f (θ ⟨x, hx⟩) = x := fun x hx => by simp [hfdef]
  have hrange : f.range = Y := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (θ.symm a).2
    · intro hx
      exact ⟨θ ⟨x, hx⟩, hfθ x hx⟩
  have hpre : ∀ x ∈ Y, ∃ a, f a = x := fun x hx => ⟨_, hfθ x hx⟩
  have hfY : ∀ a, f a ∈ Y := fun a => hrange ▸ ⟨a, rfl⟩
  have hle : ∀ {A : Subgroup X}, A ≤ Y → A ≤ f.range := fun hA => hrange.symm ▸ hA
  have hcardY : Nat.card Y = Nat.card H8 := Nat.card_congr θ.toEquiv
  have hcen : ∀ a : H8,
      Nat.card ↥(Y ⊓ Cen (f a)) = Nat.card (Subgroup.centralizer ({a} : Set H8)) :=
    fun a => by rw [← hrange, ← map_cen_eq hf, Subgroup.card_map_of_injective hf]
  have hord : ∀ a : H8, orderOf (f a) = orderOf a := fun a => orderOf_injective f hf a
  have hconj : ∀ y a : H8, f y * f a * (f y)⁻¹ = f (y * a * y⁻¹) := fun y a => by
    simp [map_mul, map_inv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro Q hQ B₁ B₂ h₁ h₂ hB₁ hB₂
    have hQcard : Nat.card (Q.comap f) = 243 := by
      rw [card_comap_eq hf (hle hQ.1), card_of_isSylowOf Nat.prime_three hQ, hcardY,
        factorization_three_H8]
      norm_num
    have e := clause1_H8 hQcard (Subgroup.comap_mono h₁) (Subgroup.comap_mono h₂)
      (isElemAb_comap hf (hle (h₁.trans hQ.1)) hB₁) (isElemAb_comap hf (hle (h₂.trans hQ.1)) hB₂)
    rw [← Subgroup.map_comap_eq_self (hle (h₁.trans hQ.1)),
      ← Subgroup.map_comap_eq_self (hle (h₂.trans hQ.1)), e]
  ·
    intro E hEY hE
    have hE' := isElemAb_comap hf (hle hEY) hE
    obtain ⟨hN, hcj⟩ := clause2_H8 hE'
    refine ⟨?_, fun x hx h3 => ?_⟩
    · have e := map_nor_eq hf (E.comap f)
      rw [Subgroup.map_comap_eq_self (hle hEY), hrange] at e
      rw [← e, Subgroup.card_map_of_injective hf, hN]
    · obtain ⟨a, rfl⟩ := hpre x hx
      obtain ⟨y, hy⟩ := hcj a (by rw [← hord]; exact h3)
      exact ⟨f y, hfY y, by rw [hconj]; exact hy⟩
  ·
    intro E hEY hE x₁ h₁ x₂ h₂ hc₁ hc₂ hne
    obtain ⟨a₁, rfl⟩ := hpre x₁ (hEY h₁)
    obtain ⟨a₂, rfl⟩ := hpre x₂ (hEY h₂)
    rw [hcen] at hc₁ hc₂
    have hne' : a₂ ∉ Subgroup.zpowers a₁ := by
      rintro ⟨k, rfl⟩
      exact hne ⟨k, by simp [map_zpow]⟩
    have h := clause3_H8 (isElemAb_comap hf (hle hEY) hE) (Subgroup.mem_comap.mpr h₁)
      (Subgroup.mem_comap.mpr h₂) hc₁ hc₂ hne'
    rw [← map_mul, hcen, h]
  ·
    intro t ht h2 x hx h3 hc
    obtain ⟨t', rfl⟩ := hpre t ht
    obtain ⟨x', rfl⟩ := hpre x hx
    rw [hcen] at hc
    obtain ⟨y, hy⟩ := clause4_H8 (by rw [← hord]; exact h2) (by rw [← hord]; exact h3) hc
    refine ⟨f y, hfY y, ?_⟩
    rw [hconj, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hy]
  ·
    intro x hx h3 K hKY hKeq hKm x₁ h₁ x₂ h₂ h13 hy
    obtain ⟨x', rfl⟩ := hpre x hx
    obtain ⟨a₁, rfl⟩ := hpre x₁ (hKY h₁)
    obtain ⟨a₂, rfl⟩ := hpre x₂ (hKY h₂)
    obtain ⟨y, hyY, hyc⟩ := hy
    obtain ⟨y', rfl⟩ := hpre y hyY
    rw [hconj] at hyc
    have hKC : K ≤ Cen (f x') := le_sup_right.trans (hKeq.le.trans inf_le_right)
    set K' := K.comap f
    have hK'C : K' ≤ Subgroup.centralizer ({x'} : Set H8) := by
      intro k hk
      have := Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hf (by rw [map_mul, map_mul, this])
    obtain ⟨eK⟩ := CFSG.RankThree.PartTwo.Sec21.nonempty_mulEquiv_H6_of_stated hKm
    have hK'K : K'.map f = K := Subgroup.map_comap_eq_self (hle hKY)
    let φ : K' ≃* K := (Subgroup.equivMapOfInjective K' f hf).trans (MulEquiv.subgroupCongr hK'K)
    have hcardK' : Nat.card K' = 1451520 := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_congr eK.toEquiv,
        CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.card_H6]
    haveI : IsSimpleGroup CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.H6 :=
      CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8.isSimpleGroup_H6
    have hperfH6 : Group.IsPerfect CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.H6 :=
      CFSG.RankThree.PartTwo.Sec4.RonanK429F.isPerfect_of_simple
        CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8.exists_not_comm_H6
    haveI := hperfH6
    have hperf : Group.IsPerfect K' :=
      Group.IsPerfect.ofSurjective (f := (eK.symm.trans φ.symm).toMonoidHom)
        (eK.symm.trans φ.symm).surjective
    obtain ⟨k, hk, hkc⟩ := clause5_H8 (by rw [← hord]; exact h3) hK'C hperf hcardK'
      (Subgroup.mem_comap.mpr h₁) (Subgroup.mem_comap.mpr h₂) (by rw [← hord]; exact h13)
      (hf hyc)
    exact ⟨f k, hk, by rw [hconj, hkc]⟩
  ·
    intro x hx h3 R hRle hN hcop
    obtain ⟨x', rfl⟩ := hpre x hx
    have hRY : R ≤ Y := hRle.trans inf_le_left
    set R' := R.comap f
    have hN' : Subgroup.centralizer ({x'} : Set H8) ≤ Subgroup.normalizer (R' : Set H8) := by
      intro c hc
      have hfc : f c ∈ Y ⊓ Cen (f x') := by
        refine Subgroup.mem_inf.mpr ⟨hfY c, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
        rw [← map_mul, hc, map_mul]
      have hNc := hN hfc
      rw [Subgroup.mem_normalizer_iff] at hNc ⊢
      intro r
      simp only [R', Subgroup.mem_comap, map_mul, map_inv]
      exact hNc (f r)
    have hcop' : (Nat.card R').Coprime 3 := by rw [card_comap_eq hf (hle hRY)]; exact hcop
    have hbot := clause6_H8 (by rw [← hord]; exact h3) hN' hcop'
    rw [← Subgroup.map_comap_eq_self (hle hRY)]
    change R'.map f = ⊥
    rw [hbot, Subgroup.map_bot]
  ·
    intro U hU z₁ h₁ z₂ h₂ hc₁ hc₂ hy
    obtain ⟨c₁, rfl⟩ := hpre z₁ (hU.1 h₁)
    obtain ⟨c₂, rfl⟩ := hpre z₂ (hU.1 h₂)
    obtain ⟨y, hyY, hyc⟩ := hy
    obtain ⟨y', rfl⟩ := hpre y hyY
    rw [hconj] at hyc
    have hUcard : Nat.card (U.comap f) = 2 ^ 16 := by
      rw [card_comap_eq hf (hle hU.1), card_of_isSylowOf Nat.prime_two hU, hcardY,
        factorization_two_H8]
    have hcen' : ∀ {c : H8}, (∀ u ∈ U, f c * u = u * f c) → ∀ u ∈ U.comap f, c * u = u * c :=
      fun {c} hc u hu => hf (by rw [map_mul, map_mul]; exact hc _ hu)
    rw [clause7_H8 hUcard (Subgroup.mem_comap.mpr h₁) (Subgroup.mem_comap.mpr h₂) (hcen' hc₁)
      (hcen' hc₂) (hf hyc)]

end CFSG.RankThree.PartTwo.Sec21.FF81

