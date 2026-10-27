module

public import CFSG.Walter.ReeOrder.Ward.PSLTable
public import CFSG.CharacterTheory.PSL2Table.Blocks
public import CFSG.Walter.ReeOrder.Ward.PSLData

public section

open scoped BigOperators Classical MatrixGroups

namespace CFSG.Walter.Ward

open CFSG CFSG.PSL2Table Matrix

namespace PSLTable

section Five

variable {F : Type} [Field F] [Fintype F]

theorem five_sq (hF : ringChar F ≠ 2) (h8 : Fintype.card F % 8 = 5) : IsSquare (-1 : F) := by
  rw [isSquare_neg_one_iff_mod_four hF]
  omega

theorem five_eps [DecidableEq F] (hF : ringChar F ≠ 2) (h8 : Fintype.card F % 8 = 5) :
    epsSign F = 1 := by
  rw [epsSign, ite_eq_left (five_sq hF h8)]

theorem five_S_odd [DecidableEq F] (hF : ringChar F ≠ 2) (h8 : Fintype.card F % 8 = 5) {ν : F}
    (hν : ¬ IsSquare ν) : Odd (Nat.card (nonsplitTorus ν)) := by
  have := card_nonsplitTorus hF hν
  exact Nat.odd_iff.mpr (by omega)

theorem five_O_card [DecidableEq F] (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) :
    2 * (Nat.card (nonsplitTorus ν) : ℤ) = (Fintype.card F : ℤ) + (1 : ℤ) := by
  have := card_nonsplitTorus hF hν
  omega

theorem five_E_card (hF : ringChar F ≠ 2) :
    2 * (Nat.card (splitTorus F) : ℤ) = (Fintype.card F : ℤ) - (1 : ℤ) := by
  have := card_splitTorus (Ring.two_ne_zero hF) (F := F)
  have hq := Fintype.card_pos (α := F)
  omega

theorem five_O_centralizer [DecidableEq F] (hF : ringChar F ≠ 2) (hq7 : 7 ≤ Fintype.card F)
    (h8 : Fintype.card F % 8 = 5) {ν : F} (hν : ¬ IsSquare ν) {x : PSL(2, F)}
    (hx : x ∈ nonsplitTorus ν) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.centralizer ({x} : Set PSL(2, F))) = Nat.card (nonsplitTorus ν) := by
  rw [card_centralizer_nonsplitTorus hF (by omega) hν hx hx1, ite_eq_right]
  intro hx2
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h3 : orderOf x ∣ Nat.card (nonsplitTorus ν) := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : nonsplitTorus ν)
    rwa [Subgroup.orderOf_mk] at this
  have h4 : orderOf x ∣ Nat.gcd 2 (Nat.card (nonsplitTorus ν)) := Nat.dvd_gcd h1 h3
  rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr (five_S_odd hF h8 hν))] at h4
  exact hx1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4))

theorem five_E_centralizer [DecidableEq F] (hF : ringChar F ≠ 2) (hq7 : 7 ≤ Fintype.card F)
    {x : PSL(2, F)} (hx : x ∈ splitTorus F) (hx2 : orderOf x = 2) :
    Nat.card (Subgroup.centralizer ({x} : Set PSL(2, F))) = 2 * Nat.card (splitTorus F) := by
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx2; omega
  rw [card_centralizer_splitTorus hF (by omega) hx hx1, ite_eq_left]
  have := pow_orderOf_eq_one x
  rw [hx2] at this
  exact this

theorem five_card_R [DecidableEq F] (hF : ringChar F ≠ 2) (hq7 : 7 ≤ Fintype.card F)
    (h8 : Fintype.card F % 8 = 5) {ν : F} (hν : ¬ IsSquare ν) :
    4 * ((discreteSet ν).card : ℤ) = (Fintype.card F : ℤ) + (1 : ℤ) - 2 := by
  have h1 := card_discreteSet hF (by omega) hν
  have h2 := card_nonsplitTorus hF hν
  rw [ite_eq_left (five_sq hF h8)] at h1
  omega

theorem five_card_S [DecidableEq F] (hF : ringChar F ≠ 2) (hq7 : 7 ≤ Fintype.card F)
    (h8 : Fintype.card F % 8 = 5) {ν : F} (hν : ¬ IsSquare ν) :
    4 * ((principalSet F).card : ℤ) = (Fintype.card F : ℤ) - (1 : ℤ) - 4 := by
  have h1 := card_principalSet hF (by omega) hν
  have h2 := card_splitTorus (Ring.two_ne_zero hF) (F := F)
  rw [ite_eq_left (five_sq hF h8)] at h1
  omega

theorem five_irr [DecidableEq F] (hF : ringChar F ≠ 2) (hq7 : 7 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    BlocksIrr PSL(2, F) = insert 1 (insert (halfPlus hF ψ ν)
    (insert (halfMinus hF ψ ν) (insert (steinberg F)
      ((discreteSet ν : Set (PSL(2, F) → ℂ)) ∪ principalSet F)))) := by
  rw [(psl2_character_table hF (by omega) hν hψ).1]
  ext χ
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_union, Finset.mem_coe,
    mem_principalSet_iff, mem_discreteSet_iff]
  constructor
  · rintro (h | h | ⟨α, hα, rfl⟩ | ⟨β, hβ, rfl⟩ | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨α, hα, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨β, hβ, rfl⟩))))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rintro (h | h | h | h | ⟨β, hβ, rfl⟩ | ⟨α, hα, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨β, hβ, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨α, hα, rfl⟩))

theorem five_principal [DecidableEq F] (hF : ringChar F ≠ 2) (hq7 : 7 ≤ Fintype.card F)
    (h8 : Fintype.card F % 8 = 5) {ν : F} (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (hm2 : (2 : BlocksAlgInt) ∈ m) :
    BlocksPrincipalBlock m PSL(2, F) =
      {1, halfPlus hF ψ ν, halfMinus hF ψ ν, steinberg F} := by
  rw [(psl2_blocks_of_mod_eight_eq_five hF (by omega) hν hψ h8 m hm hm2).1]
  ext χ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem five_conj_ηp [DecidableEq F] (hF : ringChar F ≠ 2) (h8 : Fintype.card F % 8 = 5)
    {ν : F} (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {x : PSL(2, F)}
    (hx : x ∈ unipotent F) (hx1 : x ≠ 1) :
    starRingEnd ℂ (halfPlus hF ψ ν x) = halfPlus hF ψ ν x := by
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
  have ht : t ≠ 0 := fun h => hx1 (by rw [h, unip_zero, map_one])
  have hconjg : starRingEnd ℂ (quadGauss ψ) = quadGauss ψ := by
    rw [conj_quadGauss, quadChar_apply, quadraticChar_one_iff_isSquare (neg_ne_zero.mpr
      one_ne_zero) |>.mpr (five_sq hF h8)]
    simp
  rw [halfPlus_unip hF hψ hν ht, map_div₀, map_add, map_mul, quadChar_real, hconjg,
    five_eps hF h8, map_one, map_ofNat]

theorem five_conj_ηm [DecidableEq F] (hF : ringChar F ≠ 2) (h8 : Fintype.card F % 8 = 5)
    {ν : F} (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {x : PSL(2, F)}
    (hx : x ∈ unipotent F) (hx1 : x ≠ 1) :
    starRingEnd ℂ (halfMinus hF ψ ν x) = halfMinus hF ψ ν x := by
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
  have ht : t ≠ 0 := fun h => hx1 (by rw [h, unip_zero, map_one])
  have hconjg : starRingEnd ℂ (quadGauss ψ) = quadGauss ψ := by
    rw [conj_quadGauss, quadChar_apply, quadraticChar_one_iff_isSquare (neg_ne_zero.mpr
      one_ne_zero) |>.mpr (five_sq hF h8)]
    simp
  rw [halfMinus_unip hF hψ hν ht, map_div₀, map_sub, map_mul, quadChar_real, hconjg,
    five_eps hF h8, map_one, map_ofNat]

theorem exists_pslData_five [DecidableEq F] (hF : ringChar F ≠ 2) (hq7 : 7 ≤ Fintype.card F)
    (h8 : Fintype.card F % 8 = 5) : Nonempty (PSLData PSL(2, F) (Fintype.card F) 1) := by
  have h2 := Ring.two_ne_zero hF
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF
  obtain ⟨ψ, hψ⟩ := exists_psi (F := F)
  have hq4 : Fintype.card F % 4 = 1 := by omega
  have hε := five_eps hF h8
  obtain ⟨-, -, -, -, -, -, hpm, hReq, -, -, -⟩ := psl2_character_table hF (by omega) hν hψ
  obtain ⟨⟨St1, StU, StT, StS⟩, hR, hD, -, -, hp1, hm1, hU, hT, hS, hα0, -⟩ :=
    psl2_character_values hF hν hψ
  obtain ⟨hα0ne, hα0sq⟩ := hα0 hq4
  have hcU : ∀ x ∈ unipotent F, x ≠ 1 → ∃ t : F, t ≠ 0 ∧ x = mk (unip t) := by
    intro x hx hx1
    obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
    exact ⟨t, fun h => hx1 (by rw [h, unip_zero, map_one]), rfl⟩
  exact ⟨{
    e_eq := Or.inl rfl
    q_mod := by omega
    q_ge := hq7
    card := by rw [mul_comm]; exact card_PSL h2
    p := ringChar F
    p_prime := CharP.char_is_prime F _
    p_dvd := p_dvd_card
    O := nonsplitTorus ν
    E := splitTorus F
    U := unipotent F
    O_cyclic := nonsplit_isCyclic hν
    E_cyclic := splitTorus_isCyclic
    O_card := five_O_card hF hν
    E_card := five_E_card hF
    U_order := U_order hF
    classes := fun g => by
      rcases classes' hF (by omega) hν g with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
    U_O := (not_isConj_families hF hν).2.1
    O_centralizer := fun x hx hx1 => five_O_centralizer hF hq7 h8 hν hx hx1
    E_centralizer := fun x hx hx2 => five_E_centralizer hF hq7 hx hx2
    u := mk (unip 1)
    u_mem := (mem_unipotent_iff_exists _).mpr ⟨1, rfl⟩
    u_ne := by rw [Ne, mk_unip_eq_one_iff h2]; exact one_ne_zero
    St := steinberg F
    ηp := halfPlus hF ψ ν
    ηm := halfMinus hF ψ ν
    XO := discrete
    XE := principal
    RFam := discreteSet ν
    SFam := principalSet F
    mem_RFam := mem_discreteSet_iff
    mem_SFam := mem_principalSet_iff
    card_RFam := five_card_R hF hq7 h8 hν
    card_SFam := five_card_S hF hq7 h8 hν
    irr := five_irr hF hq7 hν hψ
    ηp_ne_ηm := hpm
    XE_eq_iff := fun α α' hα => hReq α α' hα
    χ₀ := splitQuadChar F
    χ₀_ne := hα0ne
    χ₀_sq := hα0sq
    St_one := St1
    ηp_one := by rw [hp1, hε]; push_cast; ring
    ηm_one := by rw [hm1, hε]; push_cast; ring
    XO_one := fun β => by rw [(hD β).1]; push_cast; ring
    XE_one := fun α => by rw [(hR α).1]; push_cast; ring
    St_U := StU
    η_U := fun x hx hx1 => by
      obtain ⟨t, ht, rfl⟩ := hcU x hx hx1
      rw [(hU t ht).1, (hU t ht).2, hε]
      push_cast
      ring
    XO_U := fun β x hx hx1 => by rw [(hD β).2.1 x hx hx1]; push_cast; ring
    XE_U := fun α x hx hx1 => by rw [(hR α).2.1 x hx hx1]; push_cast; ring
    St_O := fun x hx hx1 => by rw [StS x hx hx1]; push_cast; ring
    ηp_O := fun x hx hx1 => by rw [(hS x hx hx1).1, ite_eq_left hq4]
    ηm_O := fun x hx hx1 => by rw [(hS x hx hx1).2, ite_eq_left hq4]
    XO_O := fun β x hx hx1 => by
      rw [(hD β).2.2.2 x hx hx1, map_inv]
      push_cast
      ring
    XE_O := fun α x hx hx1 => (hR α).2.2.2 x hx hx1
    St_E := fun x hx hx1 => by rw [StT x hx hx1]; push_cast; ring
    ηp_E := fun x hx hx1 => by
      rw [(hT x hx hx1).1, ite_eq_left hq4]
      push_cast
      ring
    ηm_E := fun x hx hx1 => by
      rw [(hT x hx hx1).2, ite_eq_left hq4]
      push_cast
      ring
    XO_E := fun β x hx hx1 => (hD β).2.2.1 x hx hx1
    XE_E := fun α x hx hx1 => by
      rw [(hR α).2.2.1 x hx hx1, map_inv]
      push_cast
      ring
    conj_ηp := fun x hx hx1 => by
      rw [ite_eq_right (by norm_num)]
      exact five_conj_ηp hF h8 hν hψ hx hx1
    conj_ηm := fun x hx hx1 => by
      rw [ite_eq_right (by norm_num)]
      exact five_conj_ηm hF h8 hν hψ hx hx1
    galois_U := galois_U' hF (Or.inr h8) hν hψ
    principal := fun m hm hm2 => five_principal hF hq7 h8 hν hψ m hm hm2 }⟩

end Five

end PSLTable

end CFSG.Walter.Ward
