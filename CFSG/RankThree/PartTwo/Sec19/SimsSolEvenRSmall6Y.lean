module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallBase
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenComb10

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.CGT.PushingUpLit.SolK Equiv Equiv.Perm
open CFSG.RankThree.PartTwo.Sec19.SolEven.Comb (barPar barPar_mk mem_range_heartToBar_iff)

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

theorem barPar_barAct (hn : Even n) (σ : Perm (Fin n)) (v : permBar n) :
    barPar hn (barAct σ v) = barPar hn v := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [barAct_mk, barPar_mk, barPar_mk]
  simp only [vecPerm_apply]
  exact Equiv.sum_comp σ⁻¹ x

theorem Y_le_K (C : Cfg G M X n) : CFSG.Open.pCoreOf 2 X ≤ C.K := fun _ hy =>
  RSmall.Q_le_K C (C.S.Y_le_Q hy)

theorem even_six : Even 6 := ⟨3, rfl⟩

variable {C : Cfg G M X 6}

@[expose] noncomputable def parK (D : C.PiData) (k : ↥C.K) : ZMod 2 :=
  barPar even_six (Multiplicative.toAdd (D.π k))

theorem parK_mul (D : C.PiData) (k k' : ↥C.K) : parK D (k * k') = parK D k + parK D k' := by
  simp only [parK, map_mul, toAdd_mul, map_add]

theorem parK_one (D : C.PiData) : parK D 1 = 0 := by
  simp only [parK, map_one, toAdd_one, map_zero]

theorem parK_inv (D : C.PiData) (k : ↥C.K) : parK D k⁻¹ = parK D k := by
  have h := parK_mul D k⁻¹ k
  rw [inv_mul_cancel, parK_one] at h
  have h2 : ∀ a b : ZMod 2, 0 = a + b → a = b := by decide
  exact h2 _ _ h

theorem parK_conj (D : C.PiData) (m : ↥M) (k k' : ↥C.K) (h : (k' : G) = m * k * m⁻¹) :
    parK D k' = parK D k := by
  rw [parK, D.equivar m k k' h, barPar_barAct]
  rfl

theorem exists_mem_W_pi_eq (D : C.PiData) (k : ↥C.K) (hk : parK D k = 0) :
    ∃ w, ∃ hw : w ∈ blockU X, D.π ⟨w, RSmall.Q_le_K C (C.S.W_le_Q hw)⟩ = D.π k := by
  have hmem : Multiplicative.toAdd (D.π k) ∈ (heartToBar : altHeart 6 →+ permBar 6).range :=
    (mem_range_heartToBar_iff even_six _).2 hk
  obtain ⟨u, hu⟩ := hmem
  obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd u)
  refine ⟨w, w.2, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [D.π_W _ w rfl, hw, toAdd_ofAdd, hu]

theorem exists_eq_mul_of_parK (D : C.PiData) {y : G} (hy : y ∈ CFSG.Open.pCoreOf 2 X)
    (hpar : parK D ⟨y, Y_le_K C hy⟩ = 0) :
    ∃ c ∈ CFSG.Open.pCoreOf 2 X, c ∈ Subgroup.centralizer (X : Set G) ∧
      ∃ w ∈ blockU X, y = c * w := by
  obtain ⟨w, hw, hπ⟩ := exists_mem_W_pi_eq D _ hpar
  have hwY : w ∈ CFSG.Open.pCoreOf 2 X := C.S.W_le_Y hw
  have hcK : y * w⁻¹ ∈ C.K := C.K.mul_mem (Y_le_K C hy) (C.K.inv_mem (Y_le_K C hwY))
  have hc : D.π ⟨y * w⁻¹, hcK⟩ = 1 := by
    have e : (⟨y * w⁻¹, hcK⟩ : ↥C.K) =
        ⟨y, Y_le_K C hy⟩ * (⟨w, RSmall.Q_le_K C (C.S.W_le_Q hw)⟩ : ↥C.K)⁻¹ := rfl
    rw [e, map_mul, map_inv, hπ, mul_inv_cancel]
  refine ⟨y * w⁻¹, (CFSG.Open.pCoreOf 2 X).mul_mem hy ((CFSG.Open.pCoreOf 2 X).inv_mem hwY),
    (D.ker _).1 hc, w, hw, by group⟩

theorem mul_self_eq_one_of_parK (D : C.PiData)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    (hRel : ∀ r ∈ Rc X, r * r = 1) {y : G} (hy : y ∈ CFSG.Open.pCoreOf 2 X)
    (hpar : parK D ⟨y, Y_le_K C hy⟩ = 0) : y * y = 1 := by
  obtain ⟨c, hcY, hcX, w, hw, rfl⟩ := exists_eq_mul_of_parK D hy hpar
  have hcR : c ∈ Rc X := by
    have h2 : IsPGroup 2 (Subgroup.zpowers c) := by
      obtain ⟨j, hj⟩ := isPGroup_pCoreOf' X ⟨c, hcY⟩
      have hj' : c ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hj')
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    exact hRsyl _ h2 (Subgroup.zpowers_le.2 hcX) (Subgroup.mem_zpowers c)
  have hwX : w ∈ X := pCoreOf_le_self X (C.S.W_le_Y hw)
  have hcw : c * w = w * c := Subgroup.mem_centralizer_iff.1 hcX w hwX |>.symm
  have hww : w * w = 1 := by
    have := C.S.elemU.2 w hw
    rwa [pow_two] at this
  calc c * w * (c * w) = (c * c) * (w * w) := by
        calc c * w * (c * w) = c * (w * c) * w := by group
          _ = c * (c * w) * w := by rw [hcw]
          _ = (c * c) * (w * w) := by group
    _ = 1 := by rw [hRel c hcR, hww, one_mul]

theorem exists_mem_Y_pi_eq (D : C.PiData) (k : ↥C.K)
    (hk : parK D k = 0 ∨
      ∃ y₀, ∃ hy₀ : y₀ ∈ CFSG.Open.pCoreOf 2 X, parK D ⟨y₀, Y_le_K C hy₀⟩ = 1) :
    ∃ y, ∃ hy : y ∈ CFSG.Open.pCoreOf 2 X, D.π ⟨y, Y_le_K C hy⟩ = D.π k := by
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h01 (parK D k) with h | h
  · obtain ⟨w, hw, hπ⟩ := exists_mem_W_pi_eq D k h
    exact ⟨w, C.S.W_le_Y hw, hπ⟩
  · obtain ⟨y₀, hy₀, hp₀⟩ := hk.resolve_left (by rw [h]; decide)
    set k' : ↥C.K := (⟨y₀, Y_le_K C hy₀⟩ : ↥C.K)⁻¹ * k with hk'
    have hp' : parK D k' = 0 := by
      rw [hk', parK_mul, parK_inv, hp₀, h]
      decide
    obtain ⟨w, hw, hπ⟩ := exists_mem_W_pi_eq D k' hp'
    have hwY : w ∈ CFSG.Open.pCoreOf 2 X := C.S.W_le_Y hw
    have hyw : y₀ * w ∈ CFSG.Open.pCoreOf 2 X := (CFSG.Open.pCoreOf 2 X).mul_mem hy₀ hwY
    refine ⟨y₀ * w, hyw, ?_⟩
    have e : (⟨y₀ * w, Y_le_K C hyw⟩ : ↥C.K) =
        ⟨y₀, Y_le_K C hy₀⟩ * ⟨w, RSmall.Q_le_K C (C.S.W_le_Q hw)⟩ := rfl
    rw [e, map_mul, hπ, hk', map_mul, ← mul_assoc, map_inv, mul_inv_cancel, one_mul]

theorem mem_Y_of_mem_centralizer (C : Cfg G M X 6) {x : G} (hx : x ∈ X)
    (hxc : x ∈ Subgroup.centralizer (X : Set G)) : x ∈ CFSG.Open.pCoreOf 2 X := by
  have hcen : C.α ⟨x, hx⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro σ
    obtain ⟨y, rfl⟩ := C.α_surj σ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc y y.2)
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hcen
  have hk : (⟨x, hx⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := by
    rw [← C.α_ker]
    exact hcen
  exact ⟨⟨x, hx⟩, hk, rfl⟩

theorem mem_Y_of_mem_K (C : Cfg G M X 6) {x : G} (hx : x ∈ X) (hxK : x ∈ C.K) :
    x ∈ CFSG.Open.pCoreOf 2 X := by
  obtain ⟨hxM, hθ⟩ := C.mem_K.1 hxK
  have hα : C.α ⟨x, hx⟩ = 1 := by
    apply Subtype.ext
    rw [← C.θ_X ⟨x, hx⟩]
    exact hθ
  have hk : (⟨x, hx⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := by
    rw [← C.α_ker]
    exact hα
  exact ⟨⟨x, hx⟩, hk, rfl⟩

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6
