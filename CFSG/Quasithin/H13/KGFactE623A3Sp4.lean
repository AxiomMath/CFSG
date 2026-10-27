module

public import CFSG.Quasithin.Background.ONanE68Sp4Cube
public import CFSG.Quasithin.H13.KGFactE623Sp4
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisStructure

public section

namespace CFSG.Quasithin.H13.KGE623A3

open Matrix CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b

section Counting

variable {G : Type} [Group G] [Finite G]

theorem card_le_mul_card_fixed (φ : G → G) (hφ : ∀ g h, φ (g * h) = φ g * φ h)
    (hφi : ∀ g, φ g⁻¹ = (φ g)⁻¹) {A : Subgroup G} {E : Finset G}
    (hE : ∀ r ∈ A, φ r * r⁻¹ ∈ E) :
    Nat.card A ≤ E.card * Nat.card {r : A // φ r = r} := by
  classical
  have : Fintype A := Fintype.ofFinite _
  have hfib : ∀ e ∈ E, (Finset.univ.filter (fun r : A => φ r * (r : G)⁻¹ = e)).card ≤
      Nat.card {r : A // φ r = r} := by
    intro e _
    rcases (Finset.univ.filter (fun r : A => φ r * (r : G)⁻¹ = e)).eq_empty_or_nonempty with
      h0 | ⟨r₀, hr₀⟩
    · rw [h0, Finset.card_empty]
      exact Nat.zero_le _
    · have hr₀e : φ r₀ * (r₀ : G)⁻¹ = e := (Finset.mem_filter.mp hr₀).2
      rw [← Nat.card_eq_finsetCard]
      refine Nat.card_le_card_of_injective (fun r => ⟨r₀⁻¹ * r.1, ?_⟩) fun r s hrs => ?_
      · have hre : φ r.1 * ((r.1 : A) : G)⁻¹ = e := (Finset.mem_filter.mp r.2).2
        show φ ((r₀⁻¹ * r.1 : A) : G) = ((r₀⁻¹ * r.1 : A) : G)
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ, hφi]
        have h1 : φ r₀ = e * r₀ := by
          calc φ r₀ = (φ r₀ * (r₀ : G)⁻¹) * r₀ := by group
            _ = e * r₀ := by rw [hr₀e]
        have h2 : φ r.1 = e * r.1 := by
          calc φ r.1 = (φ r.1 * ((r.1 : A) : G)⁻¹) * r.1 := by group
            _ = e * r.1 := by rw [hre]
        rw [h1, h2]
        group
      · have h1 : r₀⁻¹ * r.1 = r₀⁻¹ * s.1 := congrArg Subtype.val hrs
        exact Subtype.ext (mul_left_cancel h1)
  have hcount := Finset.card_le_mul_card_image_of_maps_to (s := (Finset.univ : Finset A))
    (t := E) (f := fun r : A => φ r * (r : G)⁻¹) (fun r _ => hE r r.2) _ hfib
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hcount
  rw [mul_comm]
  exact hcount

end Counting

section Model

variable {K : Type} [Field K]

@[expose] def nilShort : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]

@[expose] def nilLong : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

theorem uMat_short (t : K) : uMat 0 t 0 0 = 1 + t • (nilShort : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, nilShort, one_apply]

theorem uMat_long (t : K) : uMat 0 0 t 0 = 1 + t • (nilLong : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, nilLong, one_apply]

theorem comm_of_comm_lin {M N : Matrix (Fin 4) (Fin 4) K} {β : K} (hβ : β ≠ 0)
    (h : M * (1 + β • N) = (1 + β • N) * M) (t : K) : M * (1 + t • N) = (1 + t • N) * M := by
  have h1 : β • (M * N) = β • (N * M) := by
    have := h
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul] at this
    exact add_left_cancel this
  have h2 : M * N = N * M := by
    have := congrArg (fun X => β⁻¹ • X) h1
    simpa [smul_smul, inv_mul_cancel₀ hβ] using this
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, h2]

variable [CharP K 2]

theorem upper_of_comm_c2 {g : antiSp K} {β γ : K} (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (h : g * uElt 0 β γ 0 = uElt 0 β γ 0 * g) : E6.E68Proof.Sp4.Upper g := by
  set G := glMat (g : GL (Fin 4) K) with hG
  have hm : G * uMat 0 β γ 0 = uMat 0 β γ 0 * G := by
    have := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h
    simpa [glMat_uElt] using this
  have hsp : Gᵀ * minorJ K * G = minorJ K := g.2
  have e := fun i j => congrFun (congrFun hm i) j
  have e00 := e 0 0
  have e10 := e 1 0
  have e01 := e 0 1
  have e11 := e 1 1
  have e12 := e 1 2
  have e02 := e 0 2
  simp [uMat, Matrix.mul_apply, Fin.sum_univ_four] at e00 e10 e01 e11 e12 e02
  have s02 := congrFun (congrFun hsp 0) 2
  simp [minorJ_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] at s02
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h30 : G 3 0 = 0 := e10.resolve_left hβ
  have h31 : G 3 1 = 0 := e11.resolve_left hβ
  have h20 : G 2 0 = 0 := by
    have h' : β * G 2 0 = 0 := by linear_combination (-1 : K) * e00 - γ * h30
    exact (mul_eq_zero.mp h').resolve_left hβ
  have h21 : G 2 1 = 0 := by
    have h' : β * G 2 1 = 0 := by linear_combination (-1 : K) * e01 - γ * h31
    exact (mul_eq_zero.mp h').resolve_left hβ
  have h1032 : G 1 0 = G 3 2 := by
    have h' : β * (G 1 0 - G 3 2) = 0 := by linear_combination e12
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hβ)
  have hA : β * G 0 0 = β * G 2 2 + γ * G 3 2 := by linear_combination e02
  have hB : G 3 2 * G 2 2 + G 0 0 * G 3 2 = 0 := by
    rw [h30, h20, h1032] at s02
    linear_combination s02
  have hx : γ * (G 3 2 * G 3 2) = 0 := by
    linear_combination (-(G 3 2)) * hA + β * hB + (-(β * G 2 2 * G 3 2)) * h2
  have h32 : G 3 2 = 0 := mul_self_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hγ)
  have h10 : G 1 0 = 0 := h1032.trans h32
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij <;> assumption

end Model

section Main

open CFSG.RankThree.PartOne.KCRootAxis

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem isElemAbelian_rootA (i : Axis) : CFSG.Open.IsElemAbelian 2 (rootA K i) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun g hg => ?_⟩
  · cases i
    · exact radA1_comm x.2 y.2
    · exact radA2_comm x.2 y.2
  · rw [pow_two]
    cases i
    · exact mul_self_of_mem_radA1 hg
    · exact mul_self_of_mem_radA2 hg

theorem card_rootA (i : Axis) : Nat.card (rootA K i) = Nat.card K ^ 3 := by
  cases i
  · exact (card_radicals (K := K)).2.1
  · exact (card_radicals (K := K)).2.2.1

theorem false_of_antiSp_four (hK : Nat.card K = 4) (hSp : KGE623.Sp44OrderThreeCent)
    {y b : antiSp K} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hb : b ∈ antiUnipotentCenter K)
    (hb1 : b ≠ 1) (hyb : y * b = b * y) {E : Finset (antiSp K)} (hE : E.card ≤ 4)
    (hbd : ∀ r ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({b} : Set (antiSp K))),
      y * r * y⁻¹ * r⁻¹ ∈ E) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  set C := Subgroup.centralizer ({b} : Set (antiSp K)) with hC
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hyb
  have hcount : ∀ A : Subgroup (antiSp K), A ≤ CFSG.Open.pCoreOf 2 C →
      Nat.card A ≤ 4 * Nat.card (A ⊓ Subgroup.centralizer ({y} : Set (antiSp K)) : Subgroup _) := by
    intro A hA
    have h1 := card_le_mul_card_fixed (fun g => y * g * y⁻¹) (fun g h => by group)
      (fun g => by group) (A := A) (E := E) (fun r hr => by
        show y * r * y⁻¹ * r⁻¹ ∈ E
        exact hbd r (hA hr))
    have h2 : Nat.card {r : A // y * (r : antiSp K) * y⁻¹ = r} =
        Nat.card (A ⊓ Subgroup.centralizer ({y} : Set (antiSp K)) : Subgroup _) := by
      refine Nat.card_congr ⟨fun r => ⟨r.1, r.1.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩,
        fun r => ⟨⟨r.1, r.2.1⟩, ?_⟩, ?_, ?_⟩
      · have := r.2
        calc (r.1 : antiSp K) * y = y * r.1 * y⁻¹ * y := by rw [this]
          _ = y * r.1 := by group
      · have := Subgroup.mem_centralizer_singleton_iff.mp r.2.2
        show y * r.1 * y⁻¹ = r.1
        rw [← this]
        group
      · intro r
        rfl
      · intro r
        rfl
    rw [← h2]
    exact h1.trans (Nat.mul_le_mul_right _ hE)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  obtain ⟨β, γ, rfl⟩ := hb
  have root_case : ∀ i : Axis, uElt 0 β γ 0 ∈ rootU K i →
      C ≤ Subgroup.centralizer (rootU K i : Set (antiSp K)) → False := by
    intro i hbU hCU
    have hRA := even_symplectic_four_root_axis_centralizer_structure (K := K) hK2 le_rfl i
    have hAC : rootA K i ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hRA.A_le_C ha)) _ hbU).symm
    have hAN : C ≤ Subgroup.normalizer (rootA K i : Set (antiSp K)) := by
      intro g hg
      have h1 : g ∈ Subgroup.normalizer (rootU K i : Set (antiSp K)) :=
        Subgroup.centralizer_le_normalizer _ (hCU hg)
      rwa [hRA.N_eq] at h1
    have hA2 : IsPGroup 2 (rootA K i) := by
      refine (card_and_isSylowTwoOf_antiUnipotent (K := K)).2.2.1.to_le ?_
      cases i
      · exact radA1_le_antiUnipotent
      · exact radA2_le_antiUnipotent
    have hAO : rootA K i ≤ CFSG.Open.pCoreOf 2 C :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hAC hAN hA2
    have hcnt := hcount _ hAO
    rw [card_rootA, hK] at hcnt
    set E' := rootA K i ⊓ Subgroup.centralizer ({y} : Set (antiSp K)) with hE'
    have hE'ab : CFSG.Open.IsElemAbelian 2 E' := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => (isElemAbelian_rootA i).2 g hg.1⟩
      have h := (isElemAbelian_rootA i).1.is_comm.comm (⟨a.1, a.2.1⟩ : rootA K i)
        (⟨b.1, b.2.1⟩ : rootA K i)
      have h' : a.1 * b.1 = b.1 * a.1 := congrArg Subtype.val h
      exact h'
    set e := antiProjEquiv K with he
    have hab'' := CFSG.SectionRank.isElemAbelian_map hE'ab e.toMonoidHom
    have hle : E'.map e.toMonoidHom ≤ Subgroup.centralizer ({e y} : Set _) := by
      rintro _ ⟨g, hg, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp hg.2
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, this]
    have hey3 : e y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have hey1 : e y ≠ 1 := fun h => hy1 (e.injective (h.trans (map_one e).symm))
    have hcard := hSp K hK (e y) hey3 hey1 _ hab'' hle
    rw [Subgroup.card_map_of_injective e.injective] at hcard
    omega
  by_cases hβ : β = 0
  · by_cases hγ : γ = 0
    · apply hb1
      rw [hβ, hγ]
      exact uElt_zero_eq_one
    ·
      subst hβ
      refine root_case Axis.two ⟨γ, rfl⟩ fun g hg => ?_
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨t, rfl⟩
      have h1 : glMat (g : GL (Fin 4) K) * uMat 0 0 γ 0 =
          uMat 0 0 γ 0 * glMat (g : GL (Fin 4) K) := by
        have := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K))
          (Subgroup.mem_centralizer_singleton_iff.mp hg)
        simpa [glMat_uElt] using this
      rw [uMat_long] at h1
      have h2 := comm_of_comm_lin hγ h1 t
      rw [← uMat_long] at h2
      refine antiSp_ext ?_
      simpa [glMat_uElt] using h2.symm
  · by_cases hγ : γ = 0
    ·
      subst hγ
      refine root_case Axis.one ⟨β, rfl⟩ fun g hg => ?_
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨t, rfl⟩
      have h1 : glMat (g : GL (Fin 4) K) * uMat 0 β 0 0 =
          uMat 0 β 0 0 * glMat (g : GL (Fin 4) K) := by
        have := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K))
          (Subgroup.mem_centralizer_singleton_iff.mp hg)
        simpa [glMat_uElt] using this
      rw [uMat_short] at h1
      have h2 := comm_of_comm_lin hβ h1 t
      rw [← uMat_short] at h2
      refine antiSp_ext ?_
      simpa [glMat_uElt] using h2.symm
    ·
      have hCN : C ≤ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := fun g hg =>
        E6.E68Proof.Sp4.mem_normalizer_iff_upper.mpr (upper_of_comm_c2 hβ hγ
          (Subgroup.mem_centralizer_singleton_iff.mp hg))
      have hUC : antiUnipotent K ≤ C := by
        intro u hu
        have := ((mem_antiUnipotentCenter_iff_central (uElt 0 β γ 0)).mp ⟨β, γ, rfl⟩).2 u hu
        exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
      have hU2 : IsPGroup 2 (antiUnipotent K) :=
        (card_and_isSylowTwoOf_antiUnipotent (K := K)).2.2.1
      have hUO : antiUnipotent K ≤ CFSG.Open.pCoreOf 2 C :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUC hCN hU2
      have hcnt := hcount _ hUO
      have h4 := E6.E68Proof.Sp4.four_lt_relIndex hK2 le_rfl (hCN hyC) hyo
      have hrel := Subgroup.relIndex_mul_card
        (antiUnipotent K ⊓ Subgroup.centralizer ({y} : Set (antiSp K))) (antiUnipotent K)
      rw [inf_assoc, inf_comm _ (antiUnipotent K), ← inf_assoc, inf_idem] at hrel
      have hpos : 0 < Nat.card (antiUnipotent K ⊓ Subgroup.centralizer ({y} : Set (antiSp K)) :
          Subgroup _) := Nat.card_pos
      nlinarith

end Main

end CFSG.Quasithin.H13.KGE623A3
