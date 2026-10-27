module

public import CFSG.Quasithin.Recognition.J2RecCzIso

public section

namespace CFSG.Quasithin.Kleidman

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.J2Cz

theorem QM.sq_eq : ∀ p : QM, p * p = 1 ∨ p * p = QM.z := by decide +kernel

theorem QM.commutator_eq : ∀ p q : QM, p * q * p⁻¹ * q⁻¹ = 1 ∨ p * q * p⁻¹ * q⁻¹ = QM.z := by
  decide +kernel

theorem QM.eq_of_comm_of_sq : ∀ u p : QM, u * u = 1 → u ≠ 1 → u ≠ QM.z → p * u = u * p →
    p * p = 1 → p = 1 ∨ p = QM.z ∨ p = u ∨ p = QM.z * u := by
  decide +kernel

theorem QM.twelve_le_card_sq : ∀ u : QM, u * u = 1 → u ≠ 1 → u ≠ QM.z →
    12 ≤ (Finset.univ.filter fun p : QM => p * u = u * p ∧ p * p = QM.z).card := by
  decide +kernel

theorem QM.sixteen_le_card_comm : ∀ u : QM, u * u = 1 → u ≠ 1 → u ≠ QM.z →
    16 ≤ (Finset.univ.filter fun p : QM => p * u = u * p).card := by
  decide +kernel

theorem QM.card_noncentral :
    (Finset.univ.filter fun p : QM => p * p = 1 ∧ p ≠ 1 ∧ p ≠ QM.z).card = 10 := by
  decide +kernel

namespace IsTypeH2

variable {G : Type} [Group G] {z : G}

theorem ncard_eq_card_filter (χ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ≃* QM) (P : QM → Prop) [DecidablePred P] :
    {x : G | ∃ hx : x ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)), P (χ ⟨x, hx⟩)}.ncard = (Finset.univ.filter P).card := by
  classical
  have h : {x : G | ∃ hx : x ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)), P (χ ⟨x, hx⟩)} =
      (fun p : QM => ((χ.symm p : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) : G)) '' ↑(Finset.univ.filter P) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hP⟩
      exact ⟨χ ⟨x, hx⟩, hP, by simp⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(χ.symm p).2, by simpa using hp⟩
  rw [h, Set.ncard_image_of_injective _ (fun p q hpq => χ.symm.injective (Subtype.ext hpq)),
    Set.ncard_coe_finset]

variable (h : IsTypeH2 G z)
include h

theorem sq_eq_one_or_eq {q : G} (hq : q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) : q * q = 1 ∨ q * q = z := by
  obtain ⟨χ, hχz⟩ := h.exists_equiv_QM
  rcases QM.sq_eq (χ ⟨q, hq⟩) with h1 | h1
  · left
    have : (⟨q, hq⟩ * ⟨q, hq⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) = 1 := χ.injective (by rw [map_mul, h1, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨q, hq⟩ * ⟨q, hq⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) = χ.symm QM.z := χ.injective (by rw [map_mul, h1]; simp)
    rw [← hχz, ← this]
    rfl

theorem commutator_eq_one_or_eq {p q : G} (hp : p ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hq : q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) :
    p * q * p⁻¹ * q⁻¹ = 1 ∨ p * q * p⁻¹ * q⁻¹ = z := by
  obtain ⟨χ, hχz⟩ := h.exists_equiv_QM
  set a : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) := ⟨p, hp⟩
  set b : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) := ⟨q, hq⟩
  have hval : ((a * b * a⁻¹ * b⁻¹ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) : G) = p * q * p⁻¹ * q⁻¹ := rfl
  rcases QM.commutator_eq (χ a) (χ b) with h1 | h1
  · left
    have : a * b * a⁻¹ * b⁻¹ = 1 := χ.injective (by simp only [map_mul, map_inv, h1, map_one])
    rw [← hval, this]
    rfl
  · right
    have : a * b * a⁻¹ * b⁻¹ = χ.symm QM.z :=
      χ.injective (by simp only [map_mul, map_inv, h1, MulEquiv.apply_symm_apply])
    rw [← hval, this, hχz]

theorem eq_of_comm_of_sq_eq_one {u q : G} (hu : u ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huz : u ≠ z) (hq : q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hqu : q * u = u * q) (hq2 : q * q = 1) :
    q = 1 ∨ q = z ∨ q = u ∨ q = z * u := by
  obtain ⟨χ, hχz⟩ := h.exists_equiv_QM
  set a : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) := ⟨u, hu⟩
  set b : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) := ⟨q, hq⟩
  have hz' : ((χ.symm QM.z : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) : G) = z := hχz
  have ha2 : χ a * χ a = 1 := by
    rw [← map_mul, show a * a = 1 from Subtype.ext hu2, map_one]
  have ha1 : χ a ≠ 1 := fun h1 => hu1 (congrArg Subtype.val (χ.injective (h1.trans (map_one χ).symm)))
  have haz : χ a ≠ QM.z := fun h1 => huz (by rw [← hz', ← h1, MulEquiv.symm_apply_apply])
  have hba : χ b * χ a = χ a * χ b := by
    rw [← map_mul, ← map_mul, show b * a = a * b from Subtype.ext hqu]
  have hb2 : χ b * χ b = 1 := by
    rw [← map_mul, show b * b = 1 from Subtype.ext hq2, map_one]
  rcases QM.eq_of_comm_of_sq (χ a) (χ b) ha2 ha1 haz hba hb2 with h1 | h1 | h1 | h1
  · left
    exact congrArg Subtype.val (χ.injective (h1.trans (map_one χ).symm))
  · right; left
    rw [← hz', ← h1, MulEquiv.symm_apply_apply]
  · right; right; left
    exact congrArg Subtype.val (χ.injective h1)
  · right; right; right
    have : b = χ.symm QM.z * a := χ.injective (by rw [map_mul, MulEquiv.apply_symm_apply, h1])
    rw [show q = (b : G) from rfl, this, Subgroup.coe_mul, hz']

theorem twelve_le_ncard_sq_eq {u : G} (hu : u ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huz : u ≠ z) : 12 ≤ {q : G | q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧ q * u = u * q ∧ q * q = z}.ncard := by
  classical
  obtain ⟨χ, hχz⟩ := h.exists_equiv_QM
  set a : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) := ⟨u, hu⟩
  have hz' : ((χ.symm QM.z : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) : G) = z := hχz
  have ha2 : χ a * χ a = 1 := by
    rw [← map_mul, show a * a = 1 from Subtype.ext hu2, map_one]
  have ha1 : χ a ≠ 1 := fun h1 => hu1 (congrArg Subtype.val (χ.injective (h1.trans (map_one χ).symm)))
  have haz : χ a ≠ QM.z := fun h1 => huz (by rw [← hz', ← h1, MulEquiv.symm_apply_apply])
  have hset : {q : G | q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧ q * u = u * q ∧ q * q = z} =
      {x : G | ∃ hx : x ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)), (fun p : QM => p * χ a = χ a * p ∧ p * p = QM.z) (χ ⟨x, hx⟩)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hxu, hx2⟩
      refine ⟨hx, ?_, ?_⟩
      · rw [← map_mul, ← map_mul, show (⟨x, hx⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) * a = a * ⟨x, hx⟩ from Subtype.ext hxu]
      · rw [← map_mul, show (⟨x, hx⟩ * ⟨x, hx⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) = χ.symm QM.z from Subtype.ext
          (by rw [hz']; exact hx2), MulEquiv.apply_symm_apply]
    · rintro ⟨hx, hxu, hx2⟩
      refine ⟨hx, ?_, ?_⟩
      · have := congrArg Subtype.val (χ.injective (show χ (⟨x, hx⟩ * a) = χ (a * ⟨x, hx⟩) by
          rw [map_mul, map_mul, hxu]))
        exact this
      · have := congrArg Subtype.val (χ.injective (show χ (⟨x, hx⟩ * ⟨x, hx⟩) = χ (χ.symm QM.z) by
          rw [map_mul, hx2, MulEquiv.apply_symm_apply]))
        rw [hz'] at this
        exact this
  rw [hset, ncard_eq_card_filter χ (fun p : QM => p * χ a = χ a * p ∧ p * p = QM.z)]
  exact QM.twelve_le_card_sq (χ a) ha2 ha1 haz

theorem sixteen_le_ncard_comm {u : G} (hu : u ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huz : u ≠ z) : 16 ≤ {q : G | q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧ q * u = u * q}.ncard := by
  classical
  obtain ⟨χ, hχz⟩ := h.exists_equiv_QM
  set a : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) := ⟨u, hu⟩
  have hz' : ((χ.symm QM.z : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) : G) = z := hχz
  have ha2 : χ a * χ a = 1 := by
    rw [← map_mul, show a * a = 1 from Subtype.ext hu2, map_one]
  have ha1 : χ a ≠ 1 := fun h1 => hu1 (congrArg Subtype.val (χ.injective (h1.trans (map_one χ).symm)))
  have haz : χ a ≠ QM.z := fun h1 => huz (by rw [← hz', ← h1, MulEquiv.symm_apply_apply])
  have hset : {q : G | q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧ q * u = u * q} =
      {x : G | ∃ hx : x ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)), (fun p : QM => p * χ a = χ a * p) (χ ⟨x, hx⟩)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hxu⟩
      refine ⟨hx, ?_⟩
      rw [← map_mul, ← map_mul, show (⟨x, hx⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) * a = a * ⟨x, hx⟩ from Subtype.ext hxu]
    · rintro ⟨hx, hxu⟩
      exact ⟨hx, congrArg Subtype.val (χ.injective (show χ (⟨x, hx⟩ * a) = χ (a * ⟨x, hx⟩) by
        rw [map_mul, map_mul, hxu]))⟩
  rw [hset, ncard_eq_card_filter χ (fun p : QM => p * χ a = χ a * p)]
  exact QM.sixteen_le_card_comm (χ a) ha2 ha1 haz

theorem ncard_noncentral : {q : G | q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧ q * q = 1 ∧ q ≠ 1 ∧ q ≠ z}.ncard = 10 := by
  classical
  obtain ⟨χ, hχz⟩ := h.exists_equiv_QM
  have hz' : ((χ.symm QM.z : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) : G) = z := hχz
  have hset : {q : G | q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧ q * q = 1 ∧ q ≠ 1 ∧ q ≠ z} =
      {x : G | ∃ hx : x ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)),
        (fun p : QM => p * p = 1 ∧ p ≠ 1 ∧ p ≠ QM.z) (χ ⟨x, hx⟩)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hx2, hx1, hxz⟩
      refine ⟨hx, ?_, ?_, ?_⟩
      · rw [← map_mul, show (⟨x, hx⟩ * ⟨x, hx⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) = 1 from Subtype.ext hx2, map_one]
      · intro h1
        exact hx1 (congrArg Subtype.val (χ.injective (h1.trans (map_one χ).symm)))
      · intro h1
        exact hxz (by rw [← hz', ← h1, MulEquiv.symm_apply_apply])
    · rintro ⟨hx, hx2, hx1, hxz⟩
      refine ⟨hx, ?_, ?_, ?_⟩
      · exact congrArg Subtype.val (χ.injective (show χ (⟨x, hx⟩ * ⟨x, hx⟩) = χ 1 by
          rw [map_mul, hx2, map_one]))
      · intro h1
        apply hx1
        rw [show (⟨x, hx⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) = 1 from Subtype.ext h1, map_one]
      · intro h1
        apply hxz
        rw [show (⟨x, hx⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) = χ.symm QM.z from Subtype.ext (h1.trans hz'.symm),
          MulEquiv.apply_symm_apply]
  rw [hset, ncard_eq_card_filter χ (fun p : QM => p * p = 1 ∧ p ≠ 1 ∧ p ≠ QM.z)]
  exact QM.card_noncentral

end IsTypeH2

end CFSG.Quasithin.Kleidman
