module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.HardMathSupport.Solomon.Proving.PSU32Centre
import CFSG.Open.PGLModelStated
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec18.Item187NAut

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck159

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

private theorem map_eq_of_forall_iff {M Γ : Type*} [Group M] [Group Γ] (ρ : Γ →* MulAut M)
    (S : Subgroup M) (γ : Γ) (h : ∀ m, m ∈ S ↔ ρ γ m ∈ S) : S.map (ρ γ : M →* M) = S := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (h z).1 hz
  · intro hy
    refine ⟨(ρ γ).symm y, (h _).2 ?_, by simp⟩
    simpa using hy

private theorem exists_act_map_mk {M Γ : Type*} [Group M] [Group Γ] (K J' : Subgroup M)
    [K.Normal] (H : Subgroup (M ⧸ K)) (hHdef : H = J'.map (QuotientGroup.mk' K))
    (ρ : Γ →* MulAut M) (hK : ∀ γ m, m ∈ K ↔ ρ γ m ∈ K) (hJ : ∀ γ m, m ∈ J' ↔ ρ γ m ∈ J') :
    ∃ act : Γ →* MulAut ↥H, ∀ (γ : Γ) (m : M) (x : ↥H), (x : M ⧸ K) = QuotientGroup.mk m →
      ((act γ x : ↥H) : M ⧸ K) = QuotientGroup.mk (ρ γ m) := by
  subst hHdef
  let σ : Γ → MulAut (M ⧸ K) := fun γ =>
    QuotientGroup.congr K K (ρ γ) (map_eq_of_forall_iff ρ K γ (hK γ))
  have hσmk : ∀ γ (m : M), σ γ (QuotientGroup.mk m) = QuotientGroup.mk (ρ γ m) := fun γ m => rfl
  have hσmul : ∀ γ δ (q : M ⧸ K), σ (γ * δ) q = σ γ (σ δ q) := by
    intro γ δ q
    induction q using QuotientGroup.induction_on with
    | H m => rw [hσmk, hσmk, hσmk, map_mul]; rfl
  have hH : ∀ γ, (J'.map (QuotientGroup.mk' K)).map (σ γ : M ⧸ K →* M ⧸ K) =
      J'.map (QuotientGroup.mk' K) := by
    intro γ
    have hcomp : (σ γ : M ⧸ K →* M ⧸ K).comp (QuotientGroup.mk' K) =
        (QuotientGroup.mk' K).comp (ρ γ : M →* M) := MonoidHom.ext fun m => rfl
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, map_eq_of_forall_iff ρ J' γ (hJ γ)]
  refine ⟨MonoidHom.mk' (fun γ => Sec18.Item187Proof.restrictAut (σ γ) _ (hH γ))
    fun γ δ => ?_, ?_⟩
  · ext x
    exact hσmul γ δ x.1
  · intro γ m x hx
    show σ γ x.1 = _
    rw [hx]
    rfl

omit [Finite G] in
theorem exists_act_img148 {A J : Subgroup G} [(ker148 A J).Normal]
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    ∃ act : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (A : Set G)) →*
        MulAut ↥(img148 A J J),
      ∀ (n : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (A : Set G)))
        (j j' : ↥(J ⊔ A)) (x : ↥(img148 A J J)),
        (x : ↥(J ⊔ A) ⧸ ker148 A J) = QuotientGroup.mk j → (j' : G) = (n : G) * j * (n : G)⁻¹ →
        ((act n x : ↥(img148 A J J)) : ↥(J ⊔ A) ⧸ ker148 A J) = QuotientGroup.mk j' := by
  let ρ : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (A : Set G)) →*
      MulAut ↥(J ⊔ A) :=
    (J ⊔ A).normalizerMonoidHom.comp
      (Subgroup.inclusion (Subgroup.inf_normalizer_le_normalizer_sup J A))
  have hρ : ∀ n j, ((ρ n j : ↥(J ⊔ A)) : G) = (n : G) * j * (n : G)⁻¹ := fun n j => rfl
  obtain ⟨act, hact⟩ := exists_act_map_mk (ker148 A J) (J.subgroupOf (J ⊔ A)) (img148 A J J) rfl ρ
    (fun n m => by
      have hn := normalizer_le_normalizer_pPrimeCoreOf 3 J n.2.1
      have := Subgroup.mem_normalizer_iff.mp hn (m : G)
      simpa [ker148, Subgroup.mem_subgroupOf, hρ] using this)
    (fun n m => by
      have := Subgroup.mem_normalizer_iff.mp n.2.1 (m : G)
      simpa [Subgroup.mem_subgroupOf, hρ] using this)
  refine ⟨act, fun n j j' x hx hj' => ?_⟩
  rw [hact n j x hx]
  exact congrArg _ (Subtype.ext (by rw [hρ, hj']))

omit [Finite G] in
theorem center_img148_eq_bot {A J : Subgroup G} [(ker148 A J).Normal] {k : ℕ} (hk : 1 ≤ k)
    (hX : Sec4.IsoLThreePi ↥(img148 A J J) 2 k) : Subgroup.center ↥(img148 A J J) = ⊥ := by
  have key : ∀ {Y : Type} [Group Y], Subgroup.center Y = ⊥ →
      Nonempty (↥(img148 A J J) ≃* Y) → Subgroup.center ↥(img148 A J J) = ⊥ := by
    rintro Y _ hY ⟨φ⟩
    rw [← Subgroup.map_center_eq φ.symm, hY, Subgroup.map_bot]
  rcases hX with ⟨hq, hφ⟩ | ⟨hq, hφ⟩
  · exact key (Sec13.isPerfect_center_projSL 2 k hk hq).2 hφ
  · by_cases hq2 : 2 < 2 ^ k
    · exact key (Sec13.isPerfect_center_projSU 2 k hk hq hq2).2 hφ
    · have hk1 : k = 1 := by
        by_contra hne
        have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hk1
      have hK : Nat.card (GaloisField 2 (2 * 1)) = 4 := by
        rw [GaloisField.card 2 (2 * 1) (by norm_num)]
        norm_num
      exact key (HardMathSupport.Solomon.Proving.center_eq_bot_of_su_three_two _ hK _
        (PGLModel.projSUEquivStatedProj 3 2 1)) hφ

theorem act_facts {A J L : Subgroup G} [(ker148 A J).Normal]
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hBJ : A ⊓ L ≤ J)
    (act : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (A : Set G)) →*
        MulAut ↥(img148 A J J))
    (hact : ∀ (n : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (A : Set G)))
        (j j' : ↥(J ⊔ A)) (x : ↥(img148 A J J)),
        (x : ↥(J ⊔ A) ⧸ ker148 A J) = QuotientGroup.mk j → (j' : G) = (n : G) * j * (n : G)⁻¹ →
        ((act n x : ↥(img148 A J J)) : ↥(J ⊔ A) ⧸ ker148 A J) = QuotientGroup.mk j')
    {E : Subgroup ↥(img148 A J J)}
    (hEmap : E.map (img148 A J J).subtype = img148 A J (A ⊓ L)) :
    (∀ n : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (A : Set G)),
        (∀ b ∈ A ⊓ L, (n : G) * b = b * n) → ∀ b ∈ E, act n b = b) ∧
    (∀ n : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (A : Set G)),
        (n : G) ∈ A ⊓ L → (n : G) ≠ 1 → (n : G) ^ 3 = 1 →
        ∃ e₀ ∈ E, e₀ ≠ 1 ∧ act n = MulAut.conj e₀) := by
  refine ⟨fun n hn b hb => ?_, fun n hnB hn1 hn3 => ?_⟩
  · obtain ⟨g, hg, hgB, hgb⟩ := mem_img148_iff.mp
      (hEmap ▸ Subgroup.mem_map_of_mem (img148 A J J).subtype hb)
    have hgb' : (b : ↥(J ⊔ A) ⧸ ker148 A J) = QuotientGroup.mk ⟨g, hg⟩ := hgb.symm
    refine Subtype.ext ?_
    rw [hact n ⟨g, hg⟩ ⟨g, hg⟩ b hgb' (by simp [hn g hgB]), hgb']
  · have hnM : (n : G) ∈ J ⊔ A := Subgroup.mem_sup_right hnB.1
    obtain ⟨y, hy, hyv⟩ : alpha148 A J n hnB.1 ∈ E.map (img148 A J J).subtype :=
      hEmap ▸ mem_img148_iff.mpr ⟨n, hnM, hnB, rfl⟩
    refine ⟨y, hy, fun h => ?_, ?_⟩
    · exact Main148.alpha148_ne_one hnB.1 hn1 hn3 (hyv.symm.trans (congrArg Subtype.val h))
    · ext x
      obtain ⟨g, hg, -, hgx⟩ := mem_img148_iff.mp x.2
      have hnM' : (n : G) * g * (n : G)⁻¹ ∈ J ⊔ A :=
        (J ⊔ A).mul_mem ((J ⊔ A).mul_mem hnM hg) ((J ⊔ A).inv_mem hnM)
      rw [hact n ⟨g, hg⟩ ⟨_, hnM'⟩ x hgx.symm rfl, MulAut.conj_apply]
      show _ = (y : ↥(J ⊔ A) ⧸ ker148 A J) * (x : ↥(J ⊔ A) ⧸ ker148 A J) *
        (y : ↥(J ⊔ A) ⧸ ker148 A J)⁻¹
      rw [← hgx, show (y : ↥(J ⊔ A) ⧸ ker148 A J) =
        QuotientGroup.mk' (ker148 A J) ⟨n, hnM⟩ from hyv]
      simp only [← map_inv, ← map_mul]
      rfl

end CFSG.RankThree.PartTwo.Sec15.Liebeck159
