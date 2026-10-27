module

public import CFSG.LieType.CentralExt.SL2Lift
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeRecognition

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix
open scoped MatrixGroups

theorem scalar_fin_two_one {F : Type*} [Field F] : Matrix.scalar (Fin 2) (1 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem scalar_fin_two_neg_one {F : Type*} [Field F] :
    Matrix.scalar (Fin 2) (-1 : F) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem natCard_center_sl2 {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) :
    Nat.card (Subgroup.center SL(2, F)) = 2 := by
  classical
  have hneg : (-1 : SL(2, F)) ≠ 1 := by
    intro h
    have := CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf F h2
    simp [CFSG.Semidihedral.OddFieldSL2.minusIdentity, h] at this
  have hmem : ∀ A : SL(2, F), A ∈ Subgroup.center SL(2, F) ↔ A = 1 ∨ A = -1 := by
    intro A
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    constructor
    · rintro ⟨r, hr, hrA⟩
      rw [Fintype.card_fin] at hr
      rcases CFSG.SectionRank.Ccomm.eq_one_or_neg_one_of_sq hr with rfl | rfl
      · left
        exact Subtype.ext (by rw [← hrA, scalar_fin_two_one]; rfl)
      · right
        exact Subtype.ext (by rw [← hrA, scalar_fin_two_neg_one]; rfl)
    · rintro (rfl | rfl)
      · exact ⟨1, by simp, by rw [scalar_fin_two_one]; rfl⟩
      · exact ⟨-1, by norm_num, by rw [scalar_fin_two_neg_one]; rfl⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, (hmem 1).mpr (Or.inl rfl)⟩, ⟨-1, (hmem (-1)).mpr (Or.inr rfl)⟩,
    fun h => hneg (congrArg Subtype.val h).symm, ?_⟩
  ext ⟨A, hA⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases (hmem A).mp hA with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem natCard_sl2_eq {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) :
    Nat.card SL(2, F) = Nat.card (ProjectiveSpecialLinearGroup (Fin 2) F) * 2 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, F)),
    natCard_center_sl2 h2]

theorem nonempty_mulEquiv_sl2_of_quotient {J : Type*} [Group J] [Finite J] {F : Type*} [Field F]
    [Finite F] (hF : ringChar F ≠ 2) {Z : Subgroup J} [Z.Normal] (hZc : Z ≤ Subgroup.center J)
    (hZ2 : Nat.card Z = 2) (hinv : ∀ t : J, orderOf t = 2 → t ∈ Z)
    (e : J ⧸ Z ≃* ProjectiveSpecialLinearGroup (Fin 2) F) : Nonempty (J ≃* SL(2, F)) := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  let π : J →* ProjectiveSpecialLinearGroup (Fin 2) F := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : ∀ x : J, π x = 1 ↔ x ∈ Z := by
    intro x
    change e (QuotientGroup.mk' Z x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hkerZ : π.ker = Z := by
    ext x
    exact hker x
  have hcen : π.ker ≤ Subgroup.center J := hkerZ ▸ hZc
  have h2grp : IsPGroup 2 π.ker := by
    rw [hkerZ]
    exact IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one])
  obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hF hπ hcen h2grp
    (QuotientGroup.mk' (Subgroup.center SL(2, F)))
  have hβx : ∀ x, π (β x) = (QuotientGroup.mk x : ProjectiveSpecialLinearGroup (Fin 2) F) :=
    fun x => DFunLike.congr_fun hβ x
  have hβneg : β (-1) ≠ 1 := by
    intro hneg
    let w := CFSG.Semidihedral.OddLinearNormals.quarterTurn F
    have hw2 : w ^ 2 = -1 := CFSG.Semidihedral.OddFieldSL2.quarterTurn_square F
    have hβw2 : (β w) ^ 2 = 1 := by rw [← map_pow, hw2, hneg]
    have hwc : (QuotientGroup.mk w : ProjectiveSpecialLinearGroup (Fin 2) F) ≠ 1 := fun h1 =>
      CFSG.Semidihedral.OddLinearNormals.quarterTurn_not_mem_center F
        ((QuotientGroup.eq_one_iff w).mp h1)
    have hβw1 : β w ≠ 1 := by
      intro h1
      apply hwc
      rw [← hβx w, h1, map_one]
    have hord : orderOf (β w) = 2 := orderOf_eq_prime hβw2 hβw1
    exact hwc (by rw [← hβx w]; exact (hker _).mpr (hinv _ hord))
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : β x = 1 := hx
    have hx2 : (QuotientGroup.mk x : ProjectiveSpecialLinearGroup (Fin 2) F) = 1 := by
      rw [← hβx x, hx1, map_one]
    have hxc : x ∈ Subgroup.center SL(2, F) := (QuotientGroup.eq_one_iff x).mp hx2
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at hxc
    obtain ⟨r, hr, hrx⟩ := hxc
    rw [Fintype.card_fin] at hr
    rcases CFSG.SectionRank.Ccomm.eq_one_or_neg_one_of_sq hr with rfl | rfl
    · have : x = 1 := Subtype.ext (by rw [← hrx, scalar_fin_two_one]; rfl)
      rw [this]
      exact Subgroup.one_mem _
    · have : x = -1 := Subtype.ext (by rw [← hrx, scalar_fin_two_neg_one]; rfl)
      rw [this] at hx1
      exact absurd hx1 hβneg
  have hcard : Nat.card SL(2, F) = Nat.card J := by
    rw [natCard_sl2_eq h2, ← Nat.card_congr e.toEquiv,
      Subgroup.card_eq_card_quotient_mul_card_subgroup Z, hZ2]
  exact ⟨(MulEquiv.ofBijective β (hinj.bijective_of_nat_card_le hcard.ge)).symm⟩

theorem perfect_gl2_mulEquiv {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (J : Subgroup (GL (Fin 2) (ZMod p))) [Group.IsPerfect J] (hJ : J ≠ ⊥) :
    Nonempty (J ≃* SL(2, ZMod p)) ∨ Nonempty (J ≃* SL(2, ZMod 5)) := by
  classical
  obtain ⟨-, hcen, -, -, hdiv, hndiv⟩ :=
    CFSG.SectionRank.Ccomm.perfect_prime_linear_recognition hp2 J hJ
  by_cases hp : p ∣ Nat.card J
  · left
    have hJeq := (hdiv hp).1
    let f : SL(2, ZMod p) →* GL (Fin 2) (ZMod p) := SpecialLinearGroup.toGL
    have hf : Function.Injective f := SpecialLinearGroup.toGL_injective
    exact ⟨((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hJeq.symm)).symm⟩
  · right
    obtain ⟨e⟩ := hndiv hp
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)
    have hneg1 : (-1 : GL (Fin 2) (ZMod p)) ≠ 1 := by
      intro h
      have := congrArg (fun A : GL (Fin 2) (ZMod p) => (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
      simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at this
      exact h2 (by linear_combination -this)
    have hnegJ : (-1 : GL (Fin 2) (ZMod p)) ∈ J :=
      CFSG.SectionRank.Ccomm.neg_one_mem_of_perfect hp2 J hJ
    have hZ2 : Nat.card (Subgroup.center J) = 2 := by
      rw [Nat.card_eq_two_iff]
      refine ⟨⟨1, (hcen 1).mpr (Or.inl rfl)⟩, ⟨⟨-1, hnegJ⟩, (hcen _).mpr (Or.inr rfl)⟩,
        fun h => hneg1 (congrArg (fun x : Subgroup.center J => ((x : J) : GL (Fin 2) (ZMod p)))
          h).symm, ?_⟩
      ext ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rcases (hcen x).mp hx with h | h
      · left
        exact Subtype.ext (Subtype.ext h)
      · right
        exact Subtype.ext (Subtype.ext h)
    have hinv : ∀ t : J, orderOf t = 2 → t ∈ Subgroup.center J := by
      intro t ht
      rw [hcen]
      right
      let s : SL(2, ZMod p) := ⟨((t : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)),
        CFSG.SectionRank.Ccomm.det_eq_one_of_perfect J t.2⟩
      have hs : SpecialLinearGroup.toGL s = (t : GL (Fin 2) (ZMod p)) := Units.ext rfl
      have hso : orderOf s = 2 := by
        rw [← orderOf_injective _ SpecialLinearGroup.toGL_injective s, hs, Subgroup.orderOf_coe,
          ht]
      have hs1 : s = -1 := (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff (ZMod p) h2 s).mp hso
      rw [← hs, hs1]
      exact Units.ext rfl
    have hF5 : ringChar (ZMod 5) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      norm_num
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact nonempty_mulEquiv_sl2_of_quotient hF5 le_rfl hZ2 hinv e


theorem perfect_hom_eq_one_of_commute {G H : Type*} [Group G] (hG : Group.IsPerfect G) [Group H]
    (f : G →* H) (hcomm : ∀ a ∈ f.range, ∀ b ∈ f.range, a * b = b * a) : f = 1 := by
  have : IsMulCommutative f.range := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  ext g
  have := Subsingleton.elim (⟨f g, g, rfl⟩ : f.range) 1
  exact congrArg Subtype.val this

theorem not_isPerfect_pgl2 {F : Type*} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    ¬ Group.IsPerfect (Matrix.ProjGenLinGroup (Fin 2) F) := by
  classical
  intro hperf
  let S : Subgroup Fˣ := (powMonoidHom 2 : Fˣ →* Fˣ).range
  let δ : GL (Fin 2) F →* Fˣ ⧸ S := (QuotientGroup.mk' S).comp Matrix.GeneralLinearGroup.det
  have hδ : ∀ g, δ g = 1 ↔ Matrix.GeneralLinearGroup.det g ∈ S := fun g => by
    simp [δ, QuotientGroup.eq_one_iff]
  have hcen : Subgroup.center (GL (Fin 2) F) ≤ δ.ker := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker, hδ]
    refine ⟨u, ?_⟩
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.scalar, pow_two]
  let δ' : Matrix.ProjGenLinGroup (Fin 2) F →* Fˣ ⧸ S :=
    QuotientGroup.lift (Subgroup.center (GL (Fin 2) F)) δ hcen
  have hδ' : δ' = 1 := perfect_hom_eq_one_of_commute hperf δ' fun a _ b _ => mul_comm a b
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hF
  have ha0 : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
  let g : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![a, 1])
    (by simp [ha0])
  have h1 : δ g = 1 := by
    have := DFunLike.congr_fun hδ' (Matrix.ProjGenLinGroup.mk g)
    rwa [MonoidHom.one_apply] at this
  obtain ⟨u, hu⟩ := (hδ g).mp h1
  apply ha
  refine ⟨u, ?_⟩
  have := congrArg Units.val hu
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val] at this
  rw [← pow_two, this]
  simp [g, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem nonempty_mulEquiv_sl2_of_map {F : Type*} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    {F₀ : Type*} [Field F₀] [Finite F₀] (hF₀ : ringChar F₀ ≠ 2) (P : Subgroup SL(2, F))
    (e : P.map (QuotientGroup.mk' (Subgroup.center SL(2, F))) ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F₀) :
    Nonempty (P ≃* SL(2, F₀)) := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h20 : (2 : F₀) ≠ 0 := Ring.two_ne_zero hF₀
  let π : SL(2, F) →* ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.mk' (Subgroup.center SL(2, F))
  let ψ : P →* ProjectiveSpecialLinearGroup (Fin 2) F := π.comp P.subtype
  have hψrange : ψ.range = P.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hψker : ∀ x : P, x ∈ ψ.ker ↔ (x : SL(2, F)) ∈ Subgroup.center SL(2, F) := fun x => by
    simp [ψ, π, QuotientGroup.eq_one_iff]
  have hinvSL := CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff F h2
  have heven : 2 ∣ Nat.card P := by
    have hord := CFSG.Semidihedral.OddLinearNormals.projective_quarterTurn_order F₀
    have h2' : 2 ∣ Nat.card (ProjectiveSpecialLinearGroup (Fin 2) F₀) := by
      have := orderOf_dvd_natCard (QuotientGroup.mk' (Subgroup.center SL(2, F₀))
        (CFSG.Semidihedral.OddLinearNormals.quarterTurn F₀))
      rwa [hord] at this
    have h3 : Nat.card (P.map π) ∣ Nat.card P := by
      rw [← hψrange]
      exact Subgroup.card_range_dvd ψ
    rw [Nat.card_congr e.toEquiv] at h3
    exact h2'.trans h3
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 heven
  have htneg : (t : SL(2, F)) = -1 := by
    have : orderOf (t : SL(2, F)) = 2 := by rw [Subgroup.orderOf_coe, ht]
    exact (hinvSL _).mp this
  have hnegP : (-1 : SL(2, F)) ∈ P := htneg ▸ t.2
  have hcenSL : ∀ x : SL(2, F), x ∈ Subgroup.center SL(2, F) ↔ x = 1 ∨ x = -1 := by
    intro x
    constructor
    · intro hx
      obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
      rw [Fintype.card_fin] at hr
      rcases CFSG.SectionRank.Ccomm.eq_one_or_neg_one_of_sq hr with rfl | rfl
      · exact Or.inl (Subtype.ext (by rw [← hrx, scalar_fin_two_one]; rfl))
      · exact Or.inr (Subtype.ext (by rw [← hrx, scalar_fin_two_neg_one]; rfl))
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F
  have hneg1 : (-1 : SL(2, F)) ≠ 1 := by
    intro h
    have := CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf F h2
    simp [CFSG.Semidihedral.OddFieldSL2.minusIdentity, h] at this
  have hZc : ψ.ker ≤ Subgroup.center P := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp ((hψker x).mp hx) y)
  have hZ2 : Nat.card ψ.ker = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, (hψker 1).mpr (Subgroup.one_mem _)⟩,
      ⟨⟨-1, hnegP⟩, (hψker _).mpr ((hcenSL _).mpr (Or.inr rfl))⟩,
      fun h => hneg1 (congrArg (fun x : ψ.ker => ((x : P) : SL(2, F))) h).symm, ?_⟩
    ext ⟨x, hx⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (hcenSL _).mp ((hψker x).mp hx) with h | h
    · left
      exact Subtype.ext (Subtype.ext h)
    · right
      exact Subtype.ext (Subtype.ext h)
  have hinv : ∀ s : P, orderOf s = 2 → s ∈ ψ.ker := by
    intro s hs
    rw [hψker, hcenSL]
    right
    exact (hinvSL _).mp (by rw [Subgroup.orderOf_coe, hs])
  let e' : P ⧸ ψ.ker ≃* ProjectiveSpecialLinearGroup (Fin 2) F₀ :=
    (QuotientGroup.quotientKerEquivRange ψ).trans
      ((MulEquiv.subgroupCongr hψrange).trans e)
  exact nonempty_mulEquiv_sl2_of_quotient hF₀ hZc hZ2 hinv e'

theorem perfect_sl2_mulEquiv {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (P : Subgroup SL(2, F)) [Group.IsPerfect P]
    (hP : P ≠ ⊥) :
    Nonempty (P ≃* SL(2, ZMod 5)) ∨
      ∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧ Nonempty (P ≃* SL(2, GaloisField p m)) := by
  classical
  have hFchar : ringChar F ≠ 2 := by
    intro h2
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
    rw [h2, ← Nat.card_eq_fintype_card, hF] at hn
    have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    rw [hn] at hodd
    have heven : Even (2 ^ (n : ℕ)) := (Nat.even_pow' n.ne_zero).mpr even_two
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  let π : SL(2, F) →* ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.mk' (Subgroup.center SL(2, F))
  have : Group.IsPerfect (P.map π) := Group.IsPerfect.map π
  have hPne : P.map π ≠ ⊥ := by
    intro h
    have hle : P ≤ Subgroup.center SL(2, F) := by
      intro x hx
      have : π x ∈ P.map π := Subgroup.mem_map_of_mem π hx
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).mp this
    have : IsMulCommutative P :=
      ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hle a.2) b).symm⟩⟩
    have : Subsingleton P := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact hP (Subgroup.eq_bot_of_subsingleton P)
  have : Nontrivial (P.map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
  have hnotsolv : ¬ Group.IsSolvable (P.map π) := Group.IsPerfect.not_isSolvable (P.map π)
  have hnotcomm : ¬ IsMulCommutative (P.map π) := fun _ =>
    hnotsolv (Group.isSolvable_of_comm fun a b => mul_comm' a b)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF
      (P.map π) with
    hel | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨eD⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, t, -, -, N, C, hNn, hNel, -, hCcyc, -, -, hNC⟩ | ⟨m, hm0, hmf, ⟨ePSL⟩⟩ |
      ⟨m, hm0, hmf, ⟨ePGL⟩⟩
  · exact absurd hel.toIsMulCommutative hnotcomm
  · exact absurd hcyc.isMulCommutative hnotcomm
  · exfalso
    have : Group.IsPerfect (DihedralGroup z) :=
      Group.IsPerfect.ofSurjective (f := eD.toMonoidHom) eD.surjective
    have : Subsingleton (DihedralGroup z) :=
      CFSG.SectionRank.Ccomm.DihedralGroup.subsingleton_of_isPerfect
    have : Subsingleton (P.map π) := eD.injective.subsingleton
    exact hPne (Subgroup.eq_bot_of_subsingleton _)
  · exfalso
    have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact hnotsolv (Group.isSolvable_of_isSolvable_injective (f := eA4.toMonoidHom) eA4.injective)
  · exfalso
    have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact hnotsolv (Group.isSolvable_of_isSolvable_injective (f := eS4.toMonoidHom) eS4.injective)
  · left
    obtain ⟨e5⟩ := CFSG.SectionRank.Ccomm.projective_five_alternating
    exact nonempty_mulEquiv_sl2_of_map hFchar (by rw [ZMod.ringChar_zmod_n]; norm_num) P
      (eA5.trans e5.symm)
  · exfalso
    have : IsMulCommutative N := hNel.toIsMulCommutative
    have : Group.IsSolvable N := Group.isSolvable_of_comm fun a b => mul_comm' a b
    have hmapC : C.map (QuotientGroup.mk' N) = ⊤ := by
      have h := congrArg (Subgroup.map (QuotientGroup.mk' N)) hNC
      rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp C.subtype) := by
      intro q
      have hq : q ∈ C.map (QuotientGroup.mk' N) := hmapC ▸ Subgroup.mem_top q
      obtain ⟨c, hc, rfl⟩ := hq
      exact ⟨⟨c, hc⟩, rfl⟩
    have : IsCyclic (P.map π ⧸ N) := isCyclic_of_surjective _ hsurj
    have : Group.IsSolvable (P.map π ⧸ N) :=
      Group.isSolvable_of_comm fun a b => IsCyclic.isMulCommutative.is_comm.comm a b
    exact hnotsolv (Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))
  · right
    refine ⟨m, hm0, hmf, nonempty_mulEquiv_sl2_of_map hFchar ?_ P ePSL⟩
    rw [ringChar.eq (GaloisField p m) p]
    exact hp2
  · exfalso
    have : Group.IsPerfect (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) :=
      Group.IsPerfect.ofSurjective (f := ePGL.toMonoidHom) ePGL.surjective
    exact not_isPerfect_pgl2 (by rw [ringChar.eq (GaloisField p m) p]; exact hp2) this

end CFSG.RankThree.SubgroupLists
