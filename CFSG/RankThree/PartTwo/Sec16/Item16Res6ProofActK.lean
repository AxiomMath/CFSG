module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res6ProofCyc
import CFSG.RankThree.PartTwo.Sec21.Item22L2
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res6Act

open CFSG

@[expose] def ActHyp (S : Type) [Group S] : Prop :=
  Group.IsPerfect S ∧
    (∀ (H : Type) [Group H] (f : S →* H), ¬ 3 ∣ Nat.card f.range → f.range = ⊥) ∧
    ∀ (H : Type) [Group H] (f : S →* H),
      (∀ h ∈ f.range, h * h = 1 → ∀ g ∈ f.range, h * g = g * h) → f.range = ⊥

section Transvections

variable (F : Type) [Field F]

@[expose] def transvU : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def transvL : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem transvU_mul_self [CharP F 2] : transvU F * transvU F = 1 := by
  apply Subtype.ext
  change !![1, 1; 0, 1] * !![1, 1; 0, 1] = (1 : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [CharTwo.add_self_eq_zero]

theorem transvU_mul_transvL_ne [CharP F 2] :
    transvU F * transvL F ≠ transvL F * transvU F := by
  intro h
  have h1 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
    (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
  change (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 =
    (!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 at h1
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at h1
  simp [CharTwo.add_self_eq_zero] at h1

end Transvections

theorem range_eq_bot_of_inv {K H : Type*} [Group K] [Group H] [Finite K]
    (hK : Group.IsPerfect K) {V : Subgroup K} [V.Normal]
    (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ v ∈ V, v * v = 1) (hVK : V = ⁅V, ⊤⁆)
    (hS : IsSimpleGroup (K ⧸ V)) {u l : K ⧸ V} (hu : u * u = 1) (hul : u * l ≠ l * u)
    (f : K →* H) (hf : ∀ h ∈ f.range, h * h = 1 → ∀ g ∈ f.range, h * g = g * h) :
    f.range = ⊥ := by
  have hNn : (f.ker.map (QuotientGroup.mk' V)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective V)
  have := hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map (QuotientGroup.mk' V)) with
    hbot | htop
  ·
    have hNV : f.ker ≤ V := by
      intro n hn
      have h1 : QuotientGroup.mk' V n ∈ f.ker.map (QuotientGroup.mk' V) :=
        Subgroup.mem_map_of_mem _ hn
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hVN : V ≤ f.ker := by
      rw [hVK, Subgroup.commutator_le]
      intro v hv k _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
      have hc := hf (f v) ⟨v, rfl⟩ (by rw [← map_mul, hV2 v hv, map_one]) (f k) ⟨k, rfl⟩
      rw [hc, mul_inv_cancel_right, mul_inv_cancel]
    exfalso
    apply hul
    obtain ⟨uu, rfl⟩ := QuotientGroup.mk'_surjective V u
    obtain ⟨ll, rfl⟩ := QuotientGroup.mk'_surjective V l
    have hu2 : uu * uu ∈ V := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      exact hu
    have hc := hf (f uu) ⟨uu, rfl⟩ (by rw [← map_mul]; exact hVN hu2) (f ll) ⟨ll, rfl⟩
    have hmem : uu * ll * (ll * uu)⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
    have h2 := hNV hmem
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      mul_inv_eq_one] at h2
    rw [← map_mul, ← map_mul]
    exact h2
  ·
    have hcov : ∀ k : K, ∃ v ∈ V, f k = f v := by
      intro k
      have hk : QuotientGroup.mk' V k ∈ f.ker.map (QuotientGroup.mk' V) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnk⟩ := hk
      refine ⟨n⁻¹ * k, ?_, ?_⟩
      · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnk
        exact hnk
      · rw [map_mul, map_inv, (MonoidHom.mem_ker).mp hn, inv_one, one_mul]
    have hcomm : ⁅f.range, f.range⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨k, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k', rfl⟩
      obtain ⟨v, hv, hkv⟩ := hcov k
      obtain ⟨v', hv', hkv'⟩ := hcov k'
      rw [hkv, hkv', ← map_mul, ← map_mul, hV v' hv' v hv]
    have := hK
    have : Group.IsPerfect f.range := Group.IsPerfect.range f
    rw [← Subgroup.commutator_eq_self (H := f.range), hcomm]

theorem actHyp_of_data {G : Type} [Group G] [Finite G] {K V : Subgroup G} {m : ℕ}
    (hKp : Group.IsPerfect ↥K) (hVK : V ≤ K) (hVe : CFSG.Assembly.IsElemAbelian 2 V)
    (hVc : V = ⁅V, K⁆) (hF4 : 4 ≤ Nat.card (GaloisField 2 m))
    (hquot : ∃ _ : (V.subgroupOf K).Normal,
      Nonempty (↥K ⧸ V.subgroupOf K ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 m))) :
    ActHyp ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVn, ⟨e⟩⟩ := hquot
  set F := GaloisField 2 m with hF
  have hsimp : IsSimpleGroup (↥K ⧸ V.subgroupOf K) := by
    have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4
    exact (e.trans (Sec4.projSLEquivPSL F)).isSimpleGroup
  have hQc : Nat.card (↥K ⧸ V.subgroupOf K) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr (e.trans (Sec21.projSLTwoEquivSL F)).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hVab : ∀ a ∈ V.subgroupOf K, ∀ b ∈ V.subgroupOf K, a * b = b * a := by
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    apply Subtype.ext
    have := isMulCommutative_iff.mp hVe.1 ⟨(a : G), ha⟩ ⟨(b : G), hb⟩
    simpa using congrArg Subtype.val this
  have hV2 : ∀ v ∈ V.subgroupOf K, v * v = 1 := by
    intro v hv
    rw [Subgroup.mem_subgroupOf] at hv
    apply Subtype.ext
    have := hVe.2 _ hv
    simpa [sq] using this
  have hVK' : V.subgroupOf K = ⁅V.subgroupOf K, ⊤⁆ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, inf_of_le_left hVK]
    exact hVc
  refine ⟨hKp, fun H _ f hf => ?_, fun H _ f hf => ?_⟩
  · exact Res6Cyc.range_eq_bot_of_not_three_dvd hKp hVab hsimp
      (hQc ▸ Res6Cyc.three_dvd_mul_sq_sub_one _) f hf
  · set e' := e.trans (Sec21.projSLTwoEquivSL F) with he'
    refine range_eq_bot_of_inv hKp hVab hV2 hVK' hsimp (u := e'.symm (transvU F))
      (l := e'.symm (transvL F)) ?_ ?_ f hf
    · rw [← map_mul, transvU_mul_self, map_one]
    · intro h
      apply transvU_mul_transvL_ne F
      apply e'.symm.injective
      rw [map_mul, map_mul]
      exact h

end CFSG.RankThree.PartTwo.Sec16.Res6Act
