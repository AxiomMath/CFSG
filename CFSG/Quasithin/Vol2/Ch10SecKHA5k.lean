module

public import CFSG.Quasithin.Vol2.Ch10SecKHA5a
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3L3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.X7a
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.A5.G3

theorem not_isSL25_perfectCore_parabolic {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P)
    (hPj : ∀ j, ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore (P j))) {Pa : Subgroup S}
    (hpar : CFSG.Quasithin.IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) :
    ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore Pa) := by
  intro hD
  rcases perfectCore_parabolic_cases hU hP hpar hne with h | ⟨j, ⟨e⟩⟩
  · rw [h] at hD
    exact not_isSL25_bot hD
  · exact hPj j (hD.of_equiv e)

theorem not_isSL25_perfectCore_of_equiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) {Pa : Subgroup X}
    (h : ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore (Pa.map e.toMonoidHom))) :
    ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore Pa) := fun hD =>
  h (hD.of_equiv (((CFSG.Quasithin.perfectCore Pa).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr (CFSG.Quasithin.map_perfectCore e.toMonoidHom Pa))))

theorem not_isSL25_perfectCore_of_subgroupOf {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hP : CFSG.Quasithin.IsParabolic2 L P) (hne : P ≠ L)
    (h : ∀ Pa : Subgroup ↥L, CFSG.Quasithin.IsParabolic2 (⊤ : Subgroup ↥L) Pa → Pa ≠ ⊤ →
      ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore Pa)) :
    ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore P) := by
  have hPL : P ≤ L := hP.1
  have hmap : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  have hpar : CFSG.Quasithin.IsParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
    rw [CFSG.Quasithin.A312.isParabolic2_top_iff, hmap]
    exact hP
  have hne' : P.subgroupOf L ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map L.subtype) htop
    rw [hmap, Subgroup.map_top, Subgroup.range_subtype] at this
    exact this
  intro hD
  refine h _ hpar hne' ?_
  have hcore : (CFSG.Quasithin.perfectCore (P.subgroupOf L)).map L.subtype =
      CFSG.Quasithin.perfectCore P := by
    rw [CFSG.Quasithin.map_perfectCore, hmap]
  exact hD.of_equiv (((CFSG.Quasithin.perfectCore (P.subgroupOf L)).equivMapOfInjective L.subtype
    L.subtype_injective).trans (MulEquiv.subgroupCongr hcore)).symm

theorem not_isSL25_perfectCore_subgroupOf_of {G : Type} [Group G] [Finite G] {C P : Subgroup G}
    (hPC : P ≤ C) (h : ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore P)) :
    ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore (P.subgroupOf C)) := fun hD => by
  have hcore : (CFSG.Quasithin.perfectCore (P.subgroupOf C)).map C.subtype =
      CFSG.Quasithin.perfectCore P := by
    rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPC]
  exact h (hD.of_equiv (((CFSG.Quasithin.perfectCore (P.subgroupOf C)).equivMapOfInjective
    C.subtype C.subtype_injective).trans (MulEquiv.subgroupCongr hcore)))

section Three

variable {K : Type} [Field K] [Finite K]

theorem not_isSL25_perfectCore_Q3_four [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore (Q3 K j)) := by
  intro hD
  have := sl2_isSimple hK4
  obtain ⟨x, u, hx3, hu2, hu1, hxu⟩ := hD.exists_three_comm
  have hpc : CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore (Q3 K j)) = (blk3 j).ker :=
    pCore_two_eq_ker (sl2_nonabelian hK4) (blk3 j) (blk3_surjective hK4 j)
      (blk3_ker_isPGroup hK j)
  have hu : blk3 j u = 1 := MonoidHom.mem_ker.mp (hpc ▸ hu2)
  have hx : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3] at this
  have hxk : blk3 j x ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := blk3_ker_isPGroup hK j ⟨x, MonoidHom.mem_ker.mpr h1⟩
    have h2 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  have hA3 : (blk3 j x) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  have hfix : ∃ w : Fin 2 → K, w ≠ 0 ∧
      ((w ᵥ* ((blk3 j x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = w ∨
        (((blk3 j x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = w) := by
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) j with rfl | rfl
    · obtain ⟨w, hw, h⟩ := Q3_fixed_zero x u hu hu1 hxu
      exact ⟨w, hw, Or.inl h⟩
    · obtain ⟨w, hw, h⟩ := Q3_fixed_one x u hu hu1 hxu
      exact ⟨w, hw, Or.inr h⟩
  exact hxk (sl2_eq_one_of_fixed _ hA3 hfix)

theorem not_isSL25_perfectCore_Q3 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hf1 : 1 ≤ f) (j : Fin 2) : ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore (Q3 K j)) := by
  by_cases h4 : 4 ≤ Nat.card K
  · exact not_isSL25_perfectCore_Q3_four ⟨f, hf⟩ (exists_finset_card_four h4) j
  · have hf1' : f = 1 := by
      by_contra hne
      apply h4
      rw [hf]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    subst hf1'
    have hK2 : Nat.card K = 2 := by rw [hf]; norm_num
    rw [perfectCore_Q3_eq_bot_of_card_two hK2 j]
    exact not_isSL25_bot

theorem not_isSL25_perfectCore_of_cover [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hf1 : 1 ≤ f) {S : Type} [Group S] [Finite S] (π : SpecialLinearGroup (Fin 3) K →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ scalars 3 K)
    (hSyl : IsSylowTwoOf ((unitriangular 3 K).map π) ⊤) {Pa : Subgroup S}
    (hpar : CFSG.Quasithin.IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) :
    ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore Pa) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hres := linear_three_residual_of_cover hK π hπ hker
  have hinj : ∀ j : Fin 2, ∀ x ∈ CFSG.Quasithin.perfectCore (Q3 K j),
      ∀ y ∈ CFSG.Quasithin.perfectCore (Q3 K j), π x = π y → x = y := by
    intro j x hx y hy hxy
    have hz : x⁻¹ * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have hzN : x⁻¹ * y ∈ CFSG.Quasithin.perfectCore (Q3 K j) := mul_mem (inv_mem hx) hy
    have h1 := blk3_scalars j ⟨x⁻¹ * y, hzN⟩ (hker hz)
    exact inv_mul_eq_one.mp (congrArg Subtype.val h1)
  refine not_isSL25_perfectCore_parabolic hSyl hres (fun j h => ?_) hpar hne
  exact not_isSL25_perfectCore_Q3 hf hf1 j
    (h.of_equiv (perfectCoreMapEquiv π (Q3 K j) (hinj j)).symm)

end Three

theorem not_isSL25_perfectCore_l3 {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 1 ≤ f) (hL : CFSG.Quasithin.IsPSL 3 2 f ↥L ∨ CFSG.Quasithin.IsSL3 (2 ^ f) ↥L)
    (hP : CFSG.Quasithin.IsMaxParabolic2 L P) :
    ¬ IsSL25Group ↥(CFSG.Quasithin.perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine not_isSL25_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  rcases hL with hX | hX
  · obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    let e' : ↥L ≃* projectiveSL 3 K := e.trans (statedSLEquivProjectiveSL 3 K)
    obtain ⟨P₀, hP₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
    have hT₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ :=
      hP₀ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine not_isSL25_perfectCore_of_equiv e' ?_
    exact not_isSL25_perfectCore_of_cover hcard hf (proj 3 K) (proj_surjective 3 K)
      (ker_proj 3 K).le hT₀ (isParabolic2_top_map_equiv e' hpa) (map_ne_top_of_equiv e' hna)
  · obtain ⟨K, hF, hFin, hcard, ⟨φ⟩⟩ := hX
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    let e' : ↥L ≃* SpecialLinearGroup (Fin 3) K :=
      φ.trans (specialLinearGroupEquivStatedSL 3 K).symm
    obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
    have hT₀ : IsSylowTwoOf (unitriangular 3 K) ⊤ :=
      hP₀ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
    refine not_isSL25_perfectCore_of_equiv e' ?_
    exact not_isSL25_perfectCore_of_cover hcard hf (MonoidHom.id _) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact bot_le) (by rw [Subgroup.map_id]; exact hT₀)
      (isParabolic2_top_map_equiv e' hpa) (map_ne_top_of_equiv e' hna)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
