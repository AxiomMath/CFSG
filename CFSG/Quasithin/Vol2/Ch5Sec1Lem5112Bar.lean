module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Ctx
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def barMap {X B : Subgroup G} (hBX : B ≤ X) :
    ↥B →* ↥(modO2Image X B) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).subgroupMap (B.subgroupOf X)).comp
    (Subgroup.subgroupOfEquivOfLe hBX).symm.toMonoidHom

omit [Finite G] in
theorem barMap_surjective {X B : Subgroup G} (hBX : B ≤ X) : Function.Surjective (barMap hBX) :=
  (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hBX).symm.surjective

omit [Finite G] in
theorem isPGroup_ker_barMap {X B : Subgroup G} (hBX : B ≤ X) : IsPGroup 2 ↥(barMap hBX).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x
  have hx : Subgroup.inclusion hBX (x : ↥B) ∈ CFSG.pCore 2 ↥X := by
    have h0 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) (Subgroup.inclusion hBX (x : ↥B)) = 1 :=
      congrArg Subtype.val x.2
    exact (QuotientGroup.eq_one_iff _).1 h0
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨_, hx⟩
  refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
  have h1 : (Subgroup.inclusion hBX (x : ↥B)) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have h2 : ((Subgroup.inclusion hBX (x : ↥B)) : G) ^ 2 ^ m = 1 := by
    simpa using congrArg Subtype.val h1
  simpa using h2

omit [Finite G] in
theorem le_normalizer_hat {S X K Kh : Subgroup G} (hhat : IsHatComp X K Kh) (hSX : S ≤ X)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) : S ≤ Subgroup.normalizer (Kh : Set G) := by
  intro t ht
  have hKt : Kh.map (MulAut.conj t).toMonoidHom ∈ cComp X := map_conj_mem_cComp hhat.1 (hSX ht)
  have hKKt : K ≤ Kh.map (MulAut.conj t).toMonoidHom := by
    intro x hx
    have hx' : t⁻¹ * x * t⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hSK (S.inv_mem ht)) x).mp hx
    refine ⟨t⁻¹ * x * t, hhat.2.1 (by simpa using hx'), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  exact A38.map_conj_eq_iff.mp (hhat.2.2 _ hKt hKKt)

namespace EmbLoc

variable {S X K Kh : Subgroup G} (l : EmbLoc G S X K Kh)
include l

theorem S_le_normalizer_hat : S ≤ Subgroup.normalizer (Kh : Set G) :=
  le_normalizer_hat l.hat l.S_le_X l.normalizes

theorem conjClosure_hat : conjClosure Kh S = Kh :=
  Emb512.conjClosure_hat_eq l.S_le_normalizer_hat

theorem bar_ne : modO2Image X K ≠ modO2Image X Kh := by
  intro h
  have h1 := Vol2.Ch11.SecA.eq_of_modO2Image_eq l.sylowX l.hat_le_X l.le_hat
    (perfect_of_mem_cComp l.hat_cComp) l.normalizes h
  exact l.lt.ne h1

theorem bar_lt : modO2Image X K < modO2Image X Kh :=
  lt_of_le_of_ne (Subgroup.map_mono fun _ hx => l.le_hat hx) l.bar_ne

theorem cases (h312 : A312ForSQTK) :
    A312Case (modO2Image X K) (modO2Image X Kh) ∨
      A312Nonquasi (modO2Image X K) (modO2Image X Kh) := by
  rcases lemma_1_2_4_list l.qtke l.simple l.nonabelian h312 l.pCoreX l.sylowX l.le_X
      l.mem_lFamily l.hat_cComp l.le_hat with h1 | h1 | h1
  · exact absurd h1 l.bar_ne
  · exact Or.inl h1
  · exact Or.inr h1

theorem hat_equiv : Nonempty (O2Q Kh ≃* ↥(modO2Image X Kh)) := modO2_mulEquiv l.hat_cComp

theorem bar_equiv : Nonempty (O2Q K ≃* ModO2 (modO2Image X K)) :=
  Vol2.Ch11.SecA.modO2Image_quotEquiv l.le_X

theorem sylowBar : IsSylowTwoOf (o2Img X S) ⊤ :=
  isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf l.sylowX) _
    (QuotientGroup.mk'_surjective _)

theorem bar_lFamily : modO2Image X K ∈ lFamily (o2Img X S) :=
  modO2Image_mem_lFamily l.sylowX l.le_X l.mem_lFamily

theorem hatBar_cComp : modO2Image X Kh ∈ cComp (⊤ : Subgroup (O2Q X)) :=
  modO2Image_mem_cComp l.hat_cComp

end EmbLoc

namespace Emb512

variable {T M L H B D K₁ X Kh₁ : Subgroup G} {n k : ℕ}
  (e : Emb512 G T M L H B D K₁ X Kh₁ n k)
include e

theorem T_le_normalizer_hat_of_eq (heq : K₁ = oTwoUpper H) :
    T ≤ Subgroup.normalizer (Kh₁ : Set G) :=
  le_normalizer_hat e.hat e.T_le_X (e.T_le_normalizer₁ heq)

theorem conjClosure_hat_eq_of_eq (heq : K₁ = oTwoUpper H) : conjClosure Kh₁ T = Kh₁ :=
  conjClosure_hat_eq (e.T_le_normalizer_hat_of_eq heq)

theorem lt_hat_of_eq (heq : K₁ = oTwoUpper H) : K₁ < Kh₁ := by
  have h := e.lt
  rw [e.conjClosure_hat_eq_of_eq heq, ← heq] at h
  exact h

theorem toLoc (heq : K₁ = oTwoUpper H) : EmbLoc G T X K₁ Kh₁ :=
  ⟨e.hyp.toHyp5_0_1.simple, e.hyp.toHyp5_0_1.nonabelian, e.hyp.toHyp5_0_1.qtke, e.pCoreX,
    e.sylowX, e.K₁_le_X, e.K₁_lFamily, e.T_le_normalizer₁ heq, e.hat, e.lt_hat_of_eq heq⟩

end Emb512

end CFSG.Quasithin.H13
