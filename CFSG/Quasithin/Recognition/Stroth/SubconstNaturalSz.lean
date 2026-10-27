module

public import CFSG.Quasithin.Recognition.Stroth.LemmaSDegree
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzuki
public import Mathlib.LinearAlgebra.Projectivization.Action
public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open scoped LinearAlgebra.Projectivization

private theorem suzuki_bruhat (m : ℕ) (hm : 0 < m) :
    ∀ g : ↥(SuzukiMatrixGroup m),
      g ∈ SuzukiAut.rootSub m ⊔ SuzukiAut.torusSub m ∨
        ∃ b₁ ∈ SuzukiAut.rootSub m ⊔ SuzukiAut.torusSub m,
          ∃ b₂ ∈ SuzukiAut.rootSub m ⊔ SuzukiAut.torusSub m,
            g = b₁ * SuzukiAut.weyl m * b₂ := by
  let K := BinaryGaloisField (2 * m + 1)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  have hF_le : F ≤ SuzukiMatrixGroup m := by
    change Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b} ≤
      SuzukiMatrixGroup m
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hH_le : H ≤ SuzukiMatrixGroup m := by
    change Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x} ≤
      SuzukiMatrixGroup m
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  have hroot : SuzukiAut.rootSub m = F.subgroupOf (SuzukiMatrixGroup m) := rfl
  have htor : SuzukiAut.torusSub m = H.subgroupOf (SuzukiMatrixGroup m) := rfl
  have hB : SuzukiAut.rootSub m ⊔ SuzukiAut.torusSub m =
      (F ⊔ H).subgroupOf (SuzukiMatrixGroup m) := by
    rw [hroot, htor, Subgroup.subgroupOf_sup hF_le hH_le]
  have hbru := CFSG.BenderSuzuki.External.suzukiMatrixGroup_bruhat_decomposition
    m (SuzukiAut.tits m) (SuzukiAut.tits_tits m) (SuzukiAut.tits_apply m)
  intro g
  rcases hbru (g : GL (Fin 4) K) g.2 with hg | ⟨b, f, hb, hf, hg⟩
  · left
    rw [hB]
    exact Subgroup.mem_subgroupOf.mpr hg
  · right
    have hbN : b ∈ SuzukiMatrixGroup m := (show F ⊔ H ≤ SuzukiMatrixGroup m from
      sup_le hF_le hH_le) hb
    have hfF : f ∈ F := by
      change f ∈ Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
      exact hf
    have hfN : f ∈ SuzukiMatrixGroup m := hF_le hfF
    refine ⟨⟨b, hbN⟩, ?_, ⟨f, hfN⟩, ?_, ?_⟩
    · rw [hB]
      exact Subgroup.mem_subgroupOf.mpr hb
    · rw [hB]
      exact Subgroup.mem_subgroupOf.mpr (show f ∈ F ⊔ H from Subgroup.mem_sup_left hf)
    · exact Subtype.ext (by simpa [SuzukiAut.weyl] using hg)

private theorem suzuki_borel_index (m : ℕ) (hm : 0 < m)
    (hUcard : Nat.card (SuzukiAut.rootSub m) = (2 ^ (2 * m + 1)) ^ 2) :
    (SuzukiAut.rootSub m ⊔ SuzukiAut.torusSub m).index =
      Nat.card (SuzukiAut.rootSub m) + 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := SuzukiAut.tits m
  have hpi : ∀ x : K, pi x = x ^ 2 ^ (m + 1) := SuzukiAut.tits_apply m
  let pinf : ℙ K (Fin 4 → K) := Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K × K → ℙ K (Fin 4 → K) := fun z =>
    Projectivization.mk K ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range p
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  have hF_le : F ≤ SuzukiMatrixGroup m := by
    change Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b} ≤
      SuzukiMatrixGroup m
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hH_le : H ≤ SuzukiMatrixGroup m := by
    change Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x} ≤
      SuzukiMatrixGroup m
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  have h3 := CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_3 m hm pi hpi
  rcases h3 with ⟨hOstable, -, -, h2tr, -, hOcard, -, hstab⟩
  letI : MulAction ↥(SuzukiMatrixGroup m) (ℙ K (Fin 4 → K)) :=
    MulAction.compHom _ (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (Subgroup.subtype (SuzukiMatrixGroup m)))
  let Ω := {z : ℙ K (Fin 4 → K) // z ∈ O}
  letI : MulAction ↥(SuzukiMatrixGroup m) Ω :=
    { smul := fun g z => ⟨g • z.1, hOstable g z.1 z.2⟩
      one_smul := fun z => Subtype.ext (one_smul (↥(SuzukiMatrixGroup m)) z.1)
      mul_smul := fun g h z => Subtype.ext (mul_smul g h z.1) }
  let pinfΩ : Ω := ⟨pinf, by left; rfl⟩
  have h2trΩ : MulAction.IsMultiplyPretransitive ↥(SuzukiMatrixGroup m) Ω 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    have hab' : (a : ℙ K (Fin 4 → K)) ≠ b := fun h => hab (Subtype.ext h)
    have hcd' : (c : ℙ K (Fin 4 → K)) ≠ d := fun h => hcd (Subtype.ext h)
    obtain ⟨g, hg1, hg2⟩ :=
      h2tr a.1 b.1 c.1 d.1 a.2 b.2 c.2 d.2 hab' hcd'
    refine ⟨g, Subtype.ext ?_, Subtype.ext ?_⟩
    · change (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K)).toLinearEquiv •
        (a : ℙ K (Fin 4 → K)) = c
      exact hg1
    · change (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K)).toLinearEquiv •
        (b : ℙ K (Fin 4 → K)) = d
      exact hg2
  haveI : MulAction.IsMultiplyPretransitive ↥(SuzukiMatrixGroup m) Ω 2 := h2trΩ
  haveI : MulAction.IsPretransitive ↥(SuzukiMatrixGroup m) Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hidx : (MulAction.stabilizer ↥(SuzukiMatrixGroup m) pinfΩ).index = Nat.card Ω :=
    MulAction.index_stabilizer_of_transitive ↥(SuzukiMatrixGroup m) pinfΩ
  have hstabΩ : MulAction.stabilizer ↥(SuzukiMatrixGroup m) pinfΩ =
      (F ⊔ H).subgroupOf (SuzukiMatrixGroup m) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (hstab g).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((hstab g).mpr h)
  have hB : SuzukiAut.rootSub m ⊔ SuzukiAut.torusSub m =
      (F ⊔ H).subgroupOf (SuzukiMatrixGroup m) := by
    rw [show SuzukiAut.rootSub m = F.subgroupOf (SuzukiMatrixGroup m) from rfl,
      show SuzukiAut.torusSub m = H.subgroupOf (SuzukiMatrixGroup m) from rfl,
      Subgroup.subgroupOf_sup hF_le hH_le]
  rw [hB, ← hstabΩ, hidx, hOcard, hUcard]

theorem rankOneData_sz (a : ℕ) (ha : 1 ≤ a) :
    ∃ U B : Subgroup (Sz a), RankOneData (Sz a) U B ∧
      Nat.card U = (2 ^ (2 * a + 1)) ^ 2 := by
  let m := a
  let q := 2 ^ (2 * m + 1)
  have hm : 0 < m := by omega
  obtain ⟨S, hS⟩ := SuzukiAut.exists_sylow_eq_rootSub m hm
  have hBorel := CFSG.Open.bender_suzukiMatrixGroup_borel m hm
  have hUcard : Nat.card (SuzukiAut.rootSub m) = q ^ 2 := by
    rw [← hS]
    rcases hBorel S with ⟨-, -, -, -, hcard⟩
    simpa [q, pow_two] using hcard
  have hBindex : (SuzukiAut.rootSub m ⊔ SuzukiAut.torusSub m).index =
      Nat.card (SuzukiAut.rootSub m) + 1 := suzuki_borel_index m hm hUcard
  have hNnormalizer : Subgroup.normalizer
      ((SuzukiAut.rootSub m : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m)) =
      SuzukiAut.rootSub m ⊔ SuzukiAut.torusSub m := by
    apply le_antisymm
    · intro g hg
      obtain ⟨r, hr, h, hh, rfl⟩ := (SuzukiAut.normalizer_and_card_sylow m hm).1 g hg
      exact (SuzukiAut.rootSub m ⊔ SuzukiAut.torusSub m).mul_mem
        (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hh)
    · refine sup_le ?_ (SuzukiAut.torusSub_le_normalizer m)
      intro x hx
      exact Subgroup.le_normalizer hx
  have hweylsq : SuzukiAut.weyl m * SuzukiAut.weyl m = 1 :=
    Subtype.ext (CFSG.BenderSuzuki.External.suzukiWeylGL_mul_self m)
  have hweylinv : (SuzukiAut.weyl m)⁻¹ = SuzukiAut.weyl m :=
    inv_eq_of_mul_eq_one_right hweylsq
  have htorT : ∀ t ∈ SuzukiAut.torusSub m,
      (SuzukiAut.weyl m)⁻¹ * t * SuzukiAut.weyl m ∈ SuzukiAut.torusSub m := by
    intro t ht
    obtain ⟨x, rfl⟩ := (SuzukiAut.mem_torusSub m hm).mp ht
    have h := SuzukiAut.weyl_conj_torus m x
    rw [hweylinv] at h
    rw [hweylinv]
    rw [h]
    exact SuzukiAut.torus_mem m x⁻¹
  have hUbot : SuzukiAut.rootSub m ≠ ⊥ := by
    intro h
    have h1 : Nat.card (SuzukiAut.rootSub m) = 1 := by rw [h, Subgroup.card_bot]
    rw [hUcard] at h1
    have : 2 ≤ q := by
      dsimp [q]
      exact Nat.one_lt_two_pow (by omega)
    have : 1 < q ^ 2 := by nlinarith
    omega
  have hTcard_le : Nat.card (SuzukiAut.torusSub m) ≤ q - 1 := by
    have hsurj : Function.Surjective fun x : (BinaryGaloisField (2 * m + 1))ˣ =>
        (⟨SuzukiAut.torus m x, SuzukiAut.torus_mem m x⟩ : SuzukiAut.torusSub m) := by
      intro y
      obtain ⟨x, hx⟩ := (SuzukiAut.mem_torusSub m hm).mp y.2
      exact ⟨x, Subtype.ext hx.symm⟩
    have hle := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_units] at hle
    have hK : Nat.card (BinaryGaloisField (2 * m + 1)) = q := by
      simpa [q] using GaloisField.card 2 (2 * m + 1) (by omega)
    rwa [hK] at hle
  haveI : IsSimpleGroup (SuzukiMatrixGroup m) :=
    SuzukiAut.isSimpleGroup_suzukiMatrixGroup m hm
  have hdata_m : RankOneData (SuzukiMatrixGroup m)
      (SuzukiAut.rootSub m) (SuzukiAut.rootSub m ⊔ SuzukiAut.torusSub m) := by
    refine ⟨?_, hUbot, ⟨S, hS⟩, le_sup_left, ?_, ?_, ?_⟩
    · rw [← hS]
      exact S.isPGroup'
    · intro M hUM hM
      rcases le_B_or_eq_top_of_bruhat rfl (SuzukiAut.torusSub_le_normalizer m) htorT hweylsq
        hUbot (suzuki_bruhat m hm) M hUM with h | h
      · exact h
      · exact absurd h hM.ne
    · simpa [Nat.add_comm] using hBindex
    · have hle : (SuzukiAut.rootSub m).relIndex
          (SuzukiAut.rootSub m ⊔ SuzukiAut.torusSub m) ≤ Nat.card (SuzukiAut.torusSub m) :=
        relIndex_le_card_right_of_sup_eq rfl (SuzukiAut.torusSub_le_normalizer m)
      calc
        _ ≤ Nat.card (SuzukiAut.torusSub m) := hle
        _ ≤ q - 1 := hTcard_le
        _ < q ^ 2 := by
          have hq1 : 1 ≤ q := by
            dsimp [q]
            exact Nat.one_le_two_pow
          have h1 : q - 1 < q := Nat.sub_one_lt (by omega)
          have h2 : q ≤ q ^ 2 := by
            calc
              q = q * 1 := by ring
              _ ≤ q * q := Nat.mul_le_mul_left q hq1
              _ = q ^ 2 := by ring
          exact lt_of_lt_of_le h1 h2
        _ = Nat.card (SuzukiAut.rootSub m) := hUcard.symm
  let e := SuzukiAut.suzukiEquiv m
  let U : Subgroup (Sz m) := (SuzukiAut.rootSub m).map e.toMonoidHom
  let B : Subgroup (Sz m) := (SuzukiAut.rootSub m ⊔ SuzukiAut.torusSub m).map e.toMonoidHom
  have hdata : RankOneData (Sz m) U B := hdata_m.map e
  have hUcard' : Nat.card U = q ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective, hUcard]
  exact ⟨U, B, hdata, by simpa [m, q] using hUcard'⟩

theorem card_eq_of_hasNormalCopy_sz :
    ∀ (Y : Type) [Group Y] [Finite Y] (Ω : Type) [Fintype Ω] [MulAction Y Ω]
      [FaithfulSMul Y Ω] (a : ℕ), 1 ≤ a →
      MulAction.IsMultiplyPretransitive Y Ω 2 →
      (∃ e : ℕ, 1 ≤ e ∧ Fintype.card Ω = 1 + 2 ^ e) →
      HasNormalCopy Y ↥(Sz a) →
      Fintype.card Ω = 2 ^ (2 * (2 * a + 1)) + 1 := by
  intro Y _ _ Ω _ _ _ a ha h2 hdeg hcopy
  obtain ⟨M, hMnormal, hMequiv⟩ := hcopy
  let φ : ↥M ≃* Sz a := Classical.choice hMequiv
  letI : M.Normal := hMnormal
  obtain ⟨U, B, hdata, hUcard⟩ := rankOneData_sz a ha
  let U' : Subgroup M := U.map φ.symm.toMonoidHom
  let B' : Subgroup M := B.map φ.symm.toMonoidHom
  have hdata' : RankOneData M U' B' := hdata.map φ.symm
  have hU'card : Nat.card U' = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.symm.injective, hUcard]
  have hMbot : M ≠ ⊥ := by
    intro hbot
    apply hdata'.ne_bot
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subgroup.mem_bot.mp (by simpa [hbot] using x.2))
  have hdeg' := card_eq_one_add_of_rankOneData M hMbot h2 hdeg
    ⟨U', B', hdata', hU'card⟩
  rw [hdeg']
  rw [show (2 ^ (2 * a + 1)) ^ 2 = 2 ^ (2 * (2 * a + 1)) by
    rw [← pow_mul, mul_comm]]
  omega

end CFSG.Quasithin.Stroth
