module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts2
public import CFSG.Quasithin.Vol2.Ch11SecB21J
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem cComp_of_normal {X N K : Subgroup G} (hXN : X ≤ N)
    (hX : N ≤ Subgroup.normalizer (X : Set G)) (hK : quasithinIsCComponent K X) :
    quasithinIsCComponent K N := by
  refine ⟨hK.1, hK.2.1, A3.subnormal_trans hK.2.2.1 (A3.subnormal_of_normal hXN
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mpr hX)), ?_⟩
  intro J hJK hJ1 hJp hJN
  exact hK.2.2.2 J hJK hJ1 hJp
    (A3.subnormal_of_le_of_le hJN ((le_of_lt hJK).trans (A3.subnormal_le hK.2.2.1)) hXN)

theorem cComp_eq_of_normal [Finite G] {N K K₁ A : Subgroup G} (hK : quasithinIsCComponent K N)
    (hK₁ : quasithinIsCComponent K₁ N) (hK₁n : N ≤ Subgroup.normalizer (K₁ : Set G))
    (hA : A ≠ ⊥) (hAp : ⁅A, A⁆ = A) (hAK : A ≤ K) (hAK₁ : A ≤ K₁) : K = K₁ := by
  have hKN : K ≤ N := A3.subnormal_le hK.2.2.1
  have hAP : A ≤ perfectCore (K ⊓ K₁) := le_perfectCore_of_perfect (le_inf hAK hAK₁) hAp
  have hP1 : perfectCore (K ⊓ K₁) ≠ ⊥ := fun h => hA (le_bot_iff.mp (h ▸ hAP))
  have hnorm : ((K ⊓ K₁).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (B2F.le_normalizer_inf Subgroup.le_normalizer (hKN.trans hK₁n))
  have hsub : IsSubnormal (perfectCore (K ⊓ K₁)) N :=
    A3.subnormal_perfectCore (A3.subnormal_trans (A3.subnormal_of_normal inf_le_left hnorm)
      hK.2.2.1)
  have hPK : perfectCore (K ⊓ K₁) = K := by
    by_contra hne
    exact hK.2.2.2 _ (lt_of_le_of_ne ((perfectCore_le _).trans inf_le_left) hne) hP1
      (perfectCore_perfect _) hsub
  have hKK₁ : K ≤ K₁ := hPK ▸ ((perfectCore_le _).trans inf_le_right)
  by_contra hne
  exact hK₁.2.2.2 K (lt_of_le_of_ne hKK₁ hne) hK.1 hK.2.1 hK.2.2.1

theorem isElemAbelian_autOn {E : Subgroup G} (V : Subgroup G) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (autOn E V) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨x, hx, hxV, hxa⟩ := SecA.mem_autOn_iff.mp a.2
    obtain ⟨y, hy, hyV, hyb⟩ := SecA.mem_autOn_iff.mp b.2
    apply Subtype.ext
    change (a : MulAut ↥V) * b = b * a
    rw [hxa, hyb, ← SecA.conjV_mul, ← SecA.conjV_mul]
    have hxy : x * y = y * x := B2F.isElemAbelian_comm hE hx hy
    simp only [hxy]
  · obtain ⟨x, hx, hxV, rfl⟩ := SecA.mem_autOn_iff.mp ha
    rw [pow_two, ← SecA.conjV_mul]
    ext v
    simp only [SecA.conjV_apply_coe, MulAut.one_apply]
    have hx2 : x * x = 1 := by rw [← pow_two]; exact hE.2 x hx
    rw [hx2]
    group

theorem commSpace_autOn_le (E V : Subgroup G) :
    commSpace (autOn E V) ≤ ⁅V, E⁆.subgroupOf V := by
  rw [commSpace, Subgroup.closure_le]
  rintro w ⟨a, ha, u, rfl⟩
  obtain ⟨x, hx, hxV, rfl⟩ := SecA.mem_autOn_iff.mp ha
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, SecA.conjV_apply_coe,
    Subgroup.coe_inv]
  have hc : x * (u : G) * x⁻¹ * (u : G)⁻¹ = ⁅(u : G), x⁆⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hc]
  exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator u.2 hx)

theorem card_commSpace_autOn_le [Finite G] (E V : Subgroup G) :
    Nat.card (commSpace (autOn E V)) ≤ Nat.card ↥⁅V, E⁆ := by
  refine (Subgroup.card_le_of_le (commSpace_autOn_le E V)).trans ?_
  refine Nat.card_le_card_of_injective (fun x => ⟨(x : ↥V), x.2⟩) fun x y hxy => ?_
  exact Subtype.ext (Subtype.ext (congrArg Subtype.val hxy :))

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem inf_centralizer_le_pCoreOf_lOf (h3228 : Ch10.TmpL6_3_2_2_eight) (h : Hyp11 G T L I n)
    (U : Subgroup G) :
    T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (LOf L U ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hO2⟩ := h3228 G T L I h.fsu
  rw [SecA.fsuL0_eq h] at hO2
  rw [← hO2]
  have hsub : LOf L U ⊔ T ≤ L ⊔ T := sup_le_sup_right ((perfectCore_le _).trans inf_le_left) T
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_
    (hsub.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  rw [hO2]
  exact inf_le_left.trans le_sup_right

theorem flag24_of (hF : SecA.NatFacts) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n)
    {V₁ V₂ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂) :
    SecB.Flag24 L (fsuV T I) ⊤ T V₁ V₂ n :=
  { elem := SecA.isElemAbelian_fsuV h
    two_le := h.one_lt
    le_normalizer := SecA.L_le_normalizer_fsuV h
    commutator_eq := SecB.commutator_fsuV_eq_self h
    nat := SecB.natModuleOf_fsuV h1102 h
    kind := hk
    cL_two := SecB.isPGroup_cL_fsuV h1102 h
    le_X := le_top
    normalizer_le := inf_le_right.trans (SecA.normalizer_fsuV_le h331 h)
    sylow := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right
    T_le_V := SecA.T_le_normalizer_fsuV T I
    T_le_L := h.normal
    cV_le := SecA.IsVi.cV_le hV₁
    le₁₂ := SecA.IsVi.mono₁₂ hF h1102 h hV₁ hV₂
    le₂ := SecA.IsVi.le_fsuV hV₂
    stable₁ := SecA.IsVi.isEndStable hV₁
    stable₂ := SecA.IsVi.isEndStable hV₂
    index₁ := by rw [SecA.IsVi.relIndex_eq hV₁, mul_one]
    index₂ := SecA.IsVi.relIndex_eq hV₂
    T_le_V₁ := SecA.IsVi.le_normalizer hV₁
    T_le_V₂ := SecA.IsVi.le_normalizer hV₂ }

end CFSG.Quasithin.Vol2.Ch11.SecE
