module

public import CFSG.LocalAnalysis.UniquenessCase.UC6ProjRepL2
import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofPGroup
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearData
import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofKO3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiL2

open Subgroup CFSG.SectionRank.EvenCover CFSG.LieType.Steinberg
open scoped MatrixGroups

section SL2


theorem sl2_rep_eq_one {F : Type} [Field F] [Finite F] (hF2 : ringChar F = 2)
    (h16 : 16 ≤ Nat.card F) {L : Type*} [Field L] [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (hV : Module.finrank L V ≤ 4) (R : SL(2, F) →* Module.End L V) : R = 1 := by
  have hrL : ((ringChar F : ℕ) : L) ≠ 0 := by rw [hF2]; exact_mod_cast h2
  have hU : ∀ c : F, R (sl2Upper c) = 1 := fun c => by
    by_contra hne
    have := UCK.sl2_finrank_of_unipotent_ne_one hrL R ⟨c, hne⟩
    omega
  have hLo : ∀ c : F, R (sl2Lower c) = 1 := fun c => by
    obtain ⟨w, hw⟩ := UCK.exists_sl2Lower_eq_conj c
    rw [hw, map_mul, map_mul, hU, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have hR : R.toHomUnits = 1 := sl2_hom_ext (fun c => Units.ext (by simp [hU]))
    (fun c => Units.ext (by simp [hLo]))
  refine MonoidHom.ext fun x => ?_
  have := congrArg Units.val (DFunLike.congr_fun hR x)
  simpa using this

theorem sl2_projRep_eq_one {F : Type} [Field F] [Finite F] (hF2 : ringChar F = 2)
    (h16 : 16 ≤ Nat.card F) {L : Type*} [Field L] [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (hV : Module.finrank L V ≤ 4)
    (g : SL(2, F) →* (Module.End L V)ˣ ⧸ center (Module.End L V)ˣ) : g = 1 := by
  obtain ⟨ρ, hρ⟩ := UCK.exists_lift_of_sl2 (by omega) (by omega) g
  have h1 := sl2_rep_eq_one hF2 h16 h2 hV ((Units.coeHom _).comp ρ)
  have hρ1 : ρ = 1 := MonoidHom.ext fun x => Units.ext (by
    have := DFunLike.congr_fun h1 x
    simpa using this)
  rw [← hρ, hρ1]
  ext x
  simp

end SL2

theorem range_eq_bot_of_not_dvd {K H : Type*} [Group K] [Group H] [Finite K]
    [Group.IsPerfect K] (hS : IsSimpleGroup (K ⧸ CFSG.pCore 2 K)) (f : K →* H)
    (hf : ¬ Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card f.range) : f.range = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := CFSG.pCore 2 K with hVdef
  have hNn : (f.ker.map (QuotientGroup.mk' V)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective V)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map (QuotientGroup.mk' V)) with
    hbot | htop
  · exfalso
    have hNV : f.ker ≤ V := by
      intro n hn
      have h1 : QuotientGroup.mk' V n ∈ f.ker.map (QuotientGroup.mk' V) :=
        Subgroup.mem_map_of_mem _ hn
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    apply hf
    have h1 : Nat.card f.range = f.ker.index := by
      rw [Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    rw [h1]
    exact Subgroup.index_dvd_of_le hNV
  · have hcov : ∀ k : K, ∃ v ∈ V, f k = f v := by
      intro k
      have hk : QuotientGroup.mk' V k ∈ f.ker.map (QuotientGroup.mk' V) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnk⟩ := hk
      refine ⟨n⁻¹ * k, ?_, ?_⟩
      · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnk
        exact hnk
      · rw [map_mul, map_inv, (MonoidHom.mem_ker).mp hn, inv_one, one_mul]
    have hr2 : IsPGroup 2 f.range := by
      rintro ⟨_, k, rfl⟩
      obtain ⟨v, hv, hkv⟩ := hcov k
      obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := K) ⟨v, hv⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change f k ^ 2 ^ a = 1
      rw [hkv, ← map_pow]
      have : v ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
      rw [this, map_one]
    rw [CFSG.RankThree.PartTwo.Sec20.Res11.eq_one_of_isPGroup_range f hr2]
    exact MonoidHom.range_one

theorem card_of_isL2 {X : Type} [Group X] {m : ℕ} (hX : UC22.IsL2 X m) (hm : 1 ≤ m) :
    Nat.card X = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  rw [CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hX, CFSG.Open.ordA]
  have hpos : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hodd : Nat.gcd 2 (2 ^ m - 1) = 1 := by
    have h1 : Odd (2 ^ m - 1) := by
      have : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
      obtain ⟨k, hk⟩ := this
      exact ⟨k - 1, by omega⟩
    exact (Nat.coprime_two_left.mpr h1)
  simp [hodd]

theorem not_card_dvd_20160_of_isL2 {X : Type} [Group X] {m : ℕ} (hX : UC22.IsL2 X m)
    (hm : 4 ≤ m) : ¬ Nat.card X ∣ 20160 := by
  rw [card_of_isL2 hX (by omega)]
  intro hd
  rcases Nat.lt_or_ge m 5 with h5 | h5
  · obtain rfl : m = 4 := by omega
    norm_num at hd
  · have h32 : 32 ≤ 2 ^ m := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h5
    have hsq : 1024 ≤ (2 ^ m) ^ 2 := by nlinarith
    have hle := Nat.le_of_dvd (by norm_num) hd
    have : 32 * 1023 ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) :=
      Nat.mul_le_mul h32 (by omega)
    omega

theorem exists_mulEquiv_sl2_of_isL2 {X : Type} [Group X] {m : ℕ} (hX : UC22.IsL2 X m) :
    Nonempty (X ≃* SL(2, GaloisField 2 m)) := by
  obtain ⟨e⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Subgroup.center (SL(2, GaloisField 2 m)) = ⊥ :=
    CFSG.RankThree.PartOne.KCRootAxis.sl2_center_eq_bot
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)⟩

theorem galoisField_facts {m : ℕ} (hm : 4 ≤ m) :
    ringChar (GaloisField 2 m) = 2 ∧ 16 ≤ Nat.card (GaloisField 2 m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨ringChar.eq (GaloisField 2 m) 2, ?_⟩
  rw [GaloisField.card 2 m (by omega)]
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

section Split

variable {K : Type*} [Group K] {L : Type*} [Field L] {V : Type*} [AddCommGroup V] [Module L V]

theorem apply_eq_of_subrepresentation_eq_one {ρ : Representation L K V} {W : Submodule L V}
    {hW : ∀ k, W ≤ W.comap (ρ k)} (h : ρ.subrepresentation W hW = 1) (k : K) {w : V}
    (hw : w ∈ W) : ρ k w = w := by
  have := congrArg Subtype.val (LinearMap.congr_fun (DFunLike.congr_fun h k) ⟨w, hw⟩)
  simpa [LinearMap.restrict_apply] using this

theorem eq_one_of_isCompl {ρ : Representation L K V} {W₁ W₂ : Submodule L V}
    (h : IsCompl W₁ W₂) (h₁ : ∀ k, ∀ w ∈ W₁, ρ k w = w) (h₂ : ∀ k, ∀ w ∈ W₂, ρ k w = w) :
    ρ = 1 := by
  refine MonoidHom.ext fun k => LinearMap.ext fun v => ?_
  have hv : v ∈ W₁ ⊔ W₂ := by rw [h.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  simp [map_add, h₁ k a ha, h₂ k b hb]

theorem eq_one_of_isCompl_of_ih [FiniteDimensional L V]
    (ih : ∀ W : Submodule L V, W ≠ ⊤ → ∀ ρ' : Representation L K W, ρ' = 1)
    {ρ : Representation L K V} {W₁ W₂ : Submodule L V} (h : IsCompl W₁ W₂) (hW₁ : W₁ ≠ ⊥)
    (hW₂ : W₂ ≠ ⊥) (hi₁ : ∀ k, ∀ w ∈ W₁, ρ k w ∈ W₁) (hi₂ : ∀ k, ∀ w ∈ W₂, ρ k w ∈ W₂) :
    ρ = 1 := by
  have ht₁ : W₁ ≠ ⊤ := fun h1 => hW₂ (by
    have := h.inf_eq_bot
    rwa [h1, top_inf_eq] at this)
  have ht₂ : W₂ ≠ ⊤ := fun h2 => hW₁ (by
    have := h.inf_eq_bot
    rwa [h2, inf_top_eq] at this)
  exact eq_one_of_isCompl h
    (fun k w hw => apply_eq_of_subrepresentation_eq_one
      (ih W₁ ht₁ (ρ.subrepresentation W₁ fun k w hw => hi₁ k w hw)) k hw)
    (fun k w hw => apply_eq_of_subrepresentation_eq_one
      (ih W₂ ht₂ (ρ.subrepresentation W₂ fun k w hw => hi₂ k w hw)) k hw)

theorem exists_isCompl_of_commute [IsAlgClosed L] [FiniteDimensional L V] [Nontrivial V]
    {ρ : Representation L K V} {z : Module.End L V} (hz : ∀ k, Commute (ρ k) z) {N : ℕ}
    (hN : (N : L) ≠ 0) (hzN : z ^ N = 1)
    (hzs : ∀ c : L, z ≠ algebraMap L (Module.End L V) c) :
    ∃ W₁ W₂ : Submodule L V, IsCompl W₁ W₂ ∧ W₁ ≠ ⊥ ∧ W₂ ≠ ⊥ ∧
      (∀ k, ∀ w ∈ W₁, ρ k w ∈ W₁) ∧ (∀ k, ∀ w ∈ W₂, ρ k w ∈ W₂) := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue z
  set f := z - algebraMap L (Module.End L V) c with hf
  have hzss : z.IsSemisimple := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := Polynomial.X ^ N - Polynomial.C 1) ?_ ?_
    · exact (Polynomial.separable_X_pow_sub_C (1 : L) hN one_ne_zero).squarefree
    · simp [hzN]
  have hfss : f.IsSemisimple := Module.End.isSemisimple_sub_algebraMap_iff.mpr hzss
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
  set n := n₀ + 1 with hn
  have hcompl := hn₀ n (by omega)
  have hcomm : ∀ k, Commute (ρ k) (f ^ n) := fun k =>
    ((hz k).sub_right (Algebra.commutes c (ρ k)).symm).pow_right n
  refine ⟨LinearMap.ker (f ^ n), LinearMap.range (f ^ n), hcompl, ?_, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    rw [Submodule.ne_bot_iff]
    refine ⟨v, ?_, hv.2⟩
    have hfv : f v = 0 := by
      have := hv.apply_eq_smul
      simp [hf, this]
    rw [LinearMap.mem_ker, hn, pow_succ, Module.End.mul_apply, hfv, map_zero]
  · intro h0
    have hnil : IsNilpotent f := ⟨n, LinearMap.range_eq_bot.mp h0⟩
    have hf0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hfss
    exact hzs c (sub_eq_zero.mp hf0)
  · intro k w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [← Module.End.mul_apply, ← (hcomm k).eq, Module.End.mul_apply, hw, map_zero]
  · rintro k _ ⟨u, rfl⟩
    exact ⟨ρ k u, by rw [← Module.End.mul_apply, ← (hcomm k).eq, Module.End.mul_apply]⟩

end Split

section Act

theorem card_GL_two_dvd {n : ℕ} (hn : n ≤ 4) : Nat.card (GL (Fin n) (ZMod 2)) ∣ 20160 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2)]
  interval_cases n <;> simp [Fin.prod_univ_succ]

private def conjOn {K H : Type*} [Group K] [Group H] (f : K →* H) (M : Subgroup H)
    (hM : ∀ k, ∀ x ∈ M, f k * x * (f k)⁻¹ ∈ M) : K →* MulAut M where
  toFun k :=
    { toFun := fun x => ⟨f k * x * (f k)⁻¹, hM k x x.2⟩
      invFun := fun x => ⟨(f k)⁻¹ * x * f k, by simpa [map_inv] using hM k⁻¹ x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [mul_assoc]

theorem conj_eq_of_elementary {K H : Type*} [Group K] [Finite K] [Group.IsPerfect K] [Group H]
    (hS : IsSimpleGroup (K ⧸ CFSG.pCore 2 K)) (hnd : ¬ Nat.card (K ⧸ CFSG.pCore 2 K) ∣ 20160)
    (f : K →* H) {M : Subgroup H} [Finite M] (hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (hM2 : ∀ x ∈ M, x ^ 2 = 1) (hMcard : Nat.card M ≤ 16)
    (hMn : ∀ k, ∀ x ∈ M, f k * x * (f k)⁻¹ ∈ M) (k : K) {x : H} (hx : x ∈ M) :
    f k * x * (f k)⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 M := fun y => ⟨1, Subtype.ext (by simpa using hM2 y y.2)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hn4 : n ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b : M => Subtype.ext (hMc a a.2 b b.2)) (fun a : M => Subtype.ext (by simpa using hM2 a a.2))
    hn
  have hAut : Nat.card (MulAut M) ∣ 20160 := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e]
    exact card_GL_two_dvd hn4
  have hr := range_eq_bot_of_not_dvd hS (conjOn f M hMn) (fun hd =>
    hnd (hd.trans ((Subgroup.card_subgroup_dvd_card _).trans hAut)))
  have hk : conjOn f M hMn k = 1 := by
    have : conjOn f M hMn k ∈ (conjOn f M hMn).range := ⟨k, rfl⟩
    rwa [hr, Subgroup.mem_bot] at this
  have := congrArg Subtype.val (DFunLike.congr_fun hk ⟨x, hx⟩)
  simpa [conjOn] using this

theorem exists_mem_centralInvolutions {H : Type*} [Group H] {N : Subgroup H} [Finite N]
    (hN : IsPGroup 2 N) (hN1 : N ≠ ⊥) :
    ∃ z ∈ CFSG.GH74.Uniqueness.Hering.centralInvolutions N, z ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN1
  have hZ : Nontrivial (center N) := hN.center_nontrivial
  have h2 : 2 ∣ Nat.card (center N) := by
    obtain ⟨k, hk⟩ := (hN.to_subgroup (center N)).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hzc : ∀ w : N, w * (z : N) = (z : N) * w := Subgroup.mem_center_iff.mp z.2
  refine ⟨((z : N) : H), ⟨(z : N).2, fun y hy => ?_, ?_⟩, ?_⟩
  · exact (congrArg Subtype.val (hzc ⟨y, hy⟩)).symm
  · have h := pow_orderOf_eq_one z
    rw [hz] at h
    have h' := congrArg Subtype.val (congrArg Subtype.val h)
    simpa using h'
  · intro h1
    have : z = 1 := Subtype.ext (Subtype.ext (by simpa using h1))
    rw [this, orderOf_one] at hz
    norm_num at hz

end Act

section Scalar


theorem rep_eq_one_of_pCore_center {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {m : ℕ}
    (hL : UC22.IsL2 (K ⧸ CFSG.pCore 2 K) m) (hm : 4 ≤ m)
    {L : Type*} [Field L] [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (hV : Module.finrank L V ≤ 4) (ρ : Representation L K V)
    (hO : ∀ o ∈ CFSG.pCore 2 K, ρ.asGroupHom o ∈ center (Module.End L V)ˣ) : ρ = 1 := by
  obtain ⟨e⟩ := exists_mulEquiv_sl2_of_isL2 hL
  obtain ⟨hF2, h16⟩ := galoisField_facts hm
  let φ : K →* (Module.End L V)ˣ ⧸ center (Module.End L V)ˣ :=
    (QuotientGroup.mk' (center (Module.End L V)ˣ)).comp ρ.asGroupHom
  have hle : CFSG.pCore 2 K ≤ φ.ker := fun o ho => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hO o ho
  let g := (QuotientGroup.lift (CFSG.pCore 2 K) φ hle).comp e.symm.toMonoidHom
  have hg := sl2_projRep_eq_one hF2 h16 h2 hV g
  have hφ : ∀ k, ρ.asGroupHom k ∈ center (Module.End L V)ˣ := fun k => by
    have h1 : φ k = g (e (QuotientGroup.mk k)) := by
      simp [g, QuotientGroup.lift_mk]
    rw [hg, MonoidHom.one_apply] at h1
    have h3 : (QuotientGroup.mk' (center (Module.End L V)ˣ)) (ρ.asGroupHom k) = 1 := h1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  have h1 := CFSG.RankThree.PartTwo.Sec20.Res11.eq_one_of_commute_image ρ.asGroupHom
    (fun a b => (Subgroup.mem_center_iff.mp (hφ b) (ρ.asGroupHom a)))
  refine MonoidHom.ext fun k => ?_
  have := congrArg Units.val (DFunLike.congr_fun h1 k)
  simpa [Representation.asGroupHom_apply] using this

end Scalar

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiL2
