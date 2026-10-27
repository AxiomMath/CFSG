module

public import CFSG.Quasithin.Vol2.Ch11SecDO22
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch11SecAViLevi
public import CFSG.Quasithin.Vol2.Ch11SecDFacts3
public import CFSG.Quasithin.Vol2.Ch11SecDK

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

def negOneSL (R : Type) [CommRing R] : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨-1, by simp [Matrix.det_neg]⟩

theorem negOneSL_comm (R : Type) [CommRing R] (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    g * negOneSL R = negOneSL R * g :=
  Subtype.ext (show (g : Matrix (Fin 2) (Fin 2) R) * (-1) = (-1) * (g : Matrix _ _ R) by simp)

theorem negOneSL_sq (R : Type) [CommRing R] : negOneSL R ^ 2 = 1 := by
  rw [pow_two]
  exact Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) R) * (-1) = 1 by simp)

theorem negOneSL_ne_one (p : ℕ) (hp : 5 ≤ p) : negOneSL (ZMod p) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
    (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  simp [negOneSL] at h1
  have : Fact (2 < p) := ⟨by omega⟩
  exact ZMod.neg_one_ne_one h1

theorem isPGroup_zpowers_negOneSL (R : Type) [CommRing R] :
    IsPGroup 2 (Subgroup.zpowers (negOneSL R)) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, negOneSL_sq, one_zpow]

theorem normal_zpowers_negOneSL (R : Type) [CommRing R] :
    (Subgroup.zpowers (negOneSL R)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hc : Commute g (negOneSL R) := negOneSL_comm R g
  rw [(hc.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.zpow_mem_zpowers _ _

variable {G : Type} [Group G]

theorem not_oTwoTwoPrime_le_pCoreOf [Finite G] {K : Subgroup G} (hK : Case11_1_2One K) :
    ¬ oTwoTwoPrime K ≤ pCoreOf 2 K := by
  intro hPQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, -, hp5, φ, hφ, hker⟩ := hK
  have hp5' : 5 ≤ p := by rcases hp5 with rfl | h <;> omega
  have : (Subgroup.zpowers (negOneSL (ZMod p))).Normal := normal_zpowers_negOneSL _
  set N := (Subgroup.zpowers (negOneSL (ZMod p))).comap φ with hN
  have hNn : N.Normal := Subgroup.Normal.comap this φ
  have hker2 : IsPGroup 2 φ.ker := by
    rw [hker]
    exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hPQ).of_equiv
      (Subgroup.subgroupOfEquivOfLe (oTwoTwoPrime_le K)).symm
  have hN2 : IsPGroup 2 N := (isPGroup_zpowers_negOneSL _).comap_of_ker_isPGroup φ hker2
  have hNle : N ≤ CFSG.pCore 2 ↥K :=
    (CFSG.LieType.BorelTits.le_pCore 2 hNn hN2).trans_eq (SecA.open_pCore_eq 2 ↥K)
  obtain ⟨k, hk⟩ := hφ (negOneSL (ZMod p))
  have hkN : k ∈ N := by
    rw [hN, Subgroup.mem_comap, hk]
    exact Subgroup.mem_zpowers _
  have hkQ := hNle hkN
  rw [← pCoreOf_subgroupOf, Subgroup.mem_subgroupOf] at hkQ
  have hk1 : φ k = 1 := by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact pCoreOf_le_oTwoTwoPrime K hkQ
  exact negOneSL_ne_one p hp5' (by rw [← hk]; exact hk1)

theorem conjV_pow (V : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (k : ℕ) :
    SecA.conjV V x hx ^ k = SecA.conjV V (x ^ k) (Subgroup.pow_mem _ hx k) := by
  change CFSG.Quasithin.conjAct V ⟨x, hx⟩ ^ k = CFSG.Quasithin.conjAct V ⟨x ^ k, _⟩
  rw [← map_pow]
  rfl

theorem conjV_conj' (V : Subgroup G) {x y : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G)) :
    (SecA.conjV V y hy)⁻¹ * SecA.conjV V x hx * SecA.conjV V y hy =
      SecA.conjV V (y⁻¹ * x * y) (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy)
        hx) hy) := by
  rw [← SecA.conjV_inv, ← SecA.conjV_mul, ← SecA.conjV_mul]

theorem mem_centralizer_of_conjV_eq_one {V : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (h1 : SecA.conjV V x hx = 1) :
    x ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h2 : x * v * x⁻¹ = v := by
    have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h1
    simpa [SecA.conjV_apply_coe] using this
  calc v * x = x * v * x⁻¹ * x := by rw [h2]
    _ = x * v := by group

theorem isPGroup_of_autOn {S V : Subgroup G} (hSN : S ≤ Subgroup.normalizer (V : Set G))
    (h1 : IsPGroup 2 ↥(autOn S V)) (h2 : IsPGroup 2 ↥(S ⊓ Subgroup.centralizer (V : Set G))) :
    IsPGroup 2 ↥S := isPGroup_two_of_forall fun x hx => by
  obtain ⟨k, hk⟩ := h1 ⟨_, SecA.conjV_mem_autOn hx (hSN hx)⟩
  have hk' : SecA.conjV V (x ^ 2 ^ k) (Subgroup.pow_mem _ (hSN hx) _) = 1 := by
    rw [← conjV_pow]
    simpa using congrArg Subtype.val hk
  obtain ⟨j, hj⟩ := exists_pow_two_pow_eq_one_of_mem h2
    ⟨S.pow_mem hx _, mem_centralizer_of_conjV_eq_one _ hk'⟩
  exact ⟨k + j, by rw [pow_add, pow_mul, hj]⟩

theorem autOn_le_normalizer_autOn {S X V : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (S : Set G)) :
    autOn X V ≤ Subgroup.normalizer (autOn S V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hX

theorem isSolvable_autOn {S V : Subgroup G} (hSN : S ≤ Subgroup.normalizer (V : Set G))
    (hS : Group.IsSolvable ↥S) : Group.IsSolvable ↥(autOn S V) := by
  have : Group.IsSolvable ↥(S.subgroupOf (Subgroup.normalizer (V : Set G))) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hSN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hSN).symm.surjective
  exact Group.isSolvable_of_surjective ((CFSG.Quasithin.conjAct V).subgroupMap_surjective _)

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem isPGroup_of_solvPoint (hFact : FactSolvPointG2) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) [IsMulCommutative ↥(fsuV T I)]
    (hreal : G2NaturalDerived (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) {S : Subgroup G} (hSL : S ≤ L)
    (hSC : S ≤ Subgroup.centralizer (V₁ : Set G))
    (hN : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (S : Set G))
    (hsolv : Group.IsSolvable ↥S) : IsPGroup 2 ↥S := by
  have hSN : S ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    hSL.trans (SecA.L_le_normalizer_fsuV h)
  have hV₁V : V₁ ≤ fsuV T I := SecA.IsVi.le_fsuV hV₁
  obtain ⟨KF, _, _, hKF, π, hπ⟩ := hreal
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV h).2 w w.2)
  have hS'le : autOn S (fsuV T I) ≤
      autOn L (fsuV T I) ⊓ SecA.stabW (V₁.subgroupOf (fsuV T I)) := by
    rw [← SecA.autOn_inf_normalizer hV₁V]
    intro φ hφ
    obtain ⟨x, hxS, hxV, rfl⟩ := SecA.mem_autOn_iff.mp hφ
    exact SecA.conjV_mem_autOn (L := L ⊓ Subgroup.normalizer (V₁ : Set G))
      ⟨hSL hxS, Subgroup.centralizer_le_normalizer _ (hSC hxS)⟩ hxV
  have hS'N : autOn L (fsuV T I) ⊓ SecA.stabW (V₁.subgroupOf (fsuV T I)) ≤
      Subgroup.normalizer (autOn S (fsuV T I) : Set (MulAut ↥(fsuV T I))) := by
    rw [← SecA.autOn_inf_normalizer hV₁V]
    exact autOn_le_normalizer_autOn hN
  have hS'triv : ∀ s ∈ autOn S (fsuV T I), ∀ u ∈ V₁.subgroupOf (fsuV T I),
      s u * u⁻¹ ∈ (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) := by
    intro s hs u hu
    obtain ⟨x, hxS, hxV, rfl⟩ := SecA.mem_autOn_iff.mp hs
    have hxu : SecA.conjV (fsuV T I) x hxV u = u := Subtype.ext (by
      rw [SecA.conjV_apply_coe, ← (Subgroup.mem_centralizer_iff.mp (hSC hxS)) u
        (Subgroup.mem_subgroupOf.mp hu), mul_inv_cancel_right])
    rw [hxu, mul_inv_cancel]
    exact Subgroup.one_mem _
  have h2 := hFact KF n h.one_lt hKF ↥(fsuV T I) hsq (autOn L (fsuV T I)) _ π hπ
    (autOn (T ⊓ L) (fsuV T I)) (SecA.isSylowTwoOf_P h) (V₁.subgroupOf (fsuV T I))
    (SecA.isFlagW_of_isVi h hV₁) (autOn S (fsuV T I)) hS'le hS'N (isSolvable_autOn hSN hsolv)
    hS'triv
  refine isPGroup_of_autOn hSN h2 ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le ?_)
  rw [← SecA.centralizer_eq_pCoreOf h1102 h]
  exact inf_le_inf_right _ hSL

theorem not_oTwoTwoPrime_le_M (hFact : FactSolvPointG2) (hMult : SL2pMultFact)
    (hTI : PointsTIFact) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2)
    (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h : Hyp11 G T L I n)
    [IsMulCommutative ↥(fsuV T I)]
    (hreal : G2NaturalDerived (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hK1 : Case11_1_2One (KOf L V₁ V₁)) :
    ¬ oTwoTwoPrime (KOf L V₁ V₁) ≤ Subgroup.normalizer (L : Set G) := by
  intro hPM
  have hne := not_oTwoTwoPrime_le_pCoreOf hK1
  set K := KOf L V₁ V₁ with hKdef
  set P := oTwoTwoPrime K with hPdef
  set Q := pCoreOf 2 K with hQdef
  have : Group.IsSolvable ↥P := isSolvable_oTwoTwoPrime K
  have hKC : K ≤ Subgroup.centralizer (V₁ : Set G) :=
    kOf_le_centralizer hTI h1102 h1141 h1143 h hV₁
  have hKc := kOf_cComp h1110 h1112 h hV₁
  have hL₁K : LOf L V₁ ≤ K := le_conjClosure _ _
  have hNK := normalizer_le_normalizer_kOf L V₁ V₁
  have hNP : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (P : Set G) :=
    normalizer_le_normalizer_oTwoTwoPrime K
  have hNQ : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer.trans hNP
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hPK : P ≤ K := oTwoTwoPrime_le K
  have hS2 : IsPGroup 2 ↥(L ⊓ P) := isPGroup_of_solvPoint hFact h1102 h hreal hV₁ inf_le_left
    (inf_le_right.trans (hPK.trans hKC))
    (fun x hx => mem_normalizer_inf (Subgroup.le_normalizer hx.1) (hNP (hNK hx.2)))
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (inf_le_right : L ⊓ P ≤ P)))
  have hSQ : L ⊓ P ≤ Q := le_pCoreOf_of_le_oTwoTwoPrime hS2 inf_le_right
  have hPL₁ : ∀ x ∈ P, ∀ l ∈ LOf L V₁, l * x * l⁻¹ * x⁻¹ ∈ Q := by
    intro x hx l hl
    have hlL : l ∈ L := ((perfectCore_le _).trans inf_le_left) hl
    refine hSQ ⟨?_, P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKP (hL₁K hl)) x).mp hx)
      (P.inv_mem hx)⟩
    have hx' : x * l⁻¹ * x⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hPM hx) _).mp (L.inv_mem hlL)
    have e : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
    rw [e]
    exact L.mul_mem hlL hx'
  have hKsc : K ≤ sectionCentralizer P Q := conjClosure_le fun g hg l hl =>
    conj_mem_sectionCentralizer (hNP (hNK hg)) (hNQ (hNK hg))
      ⟨hKP (hL₁K hl), hKQ (hL₁K hl), fun x hx => hPL₁ x hx l hl⟩
  have hPKQ : ⁅P, K⁆ ≤ Q := Subgroup.commutator_le.mpr fun x hx k hk => by
    have hkx := (hKsc hk).2.2 x hx
    rw [commutatorElement_def]
    have e : x * k * x⁻¹ * k⁻¹ = (k * x * k⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact Q.inv_mem hkx
  obtain ⟨p, hp, hp5, φ, hφ, hker⟩ := hK1
  have hPQ := hMult G K P Q p hp (by rcases hp5 with rfl | h <;> omega) hKc.2.1
    (pCoreOf_le_oTwoTwoPrime K) hPK hKP hKQ hPKQ ⟨φ, hφ, hker⟩
  exact hne hPQ.le

end CFSG.Quasithin.Vol2.Ch11.SecD
