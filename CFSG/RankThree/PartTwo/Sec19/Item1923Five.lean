module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofIndexN
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.RankThree.PartTwo.Sec19.Item194Five

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

section ClassStab

variable {X : Type} [Group X]

private theorem step1923_five_map_one (Q : Subgroup X) :
    Q.map (1 : MulAut X).toMonoidHom = Q.map (MulAut.conj (1 : X)).toMonoidHom := by
  have h1 : (1 : MulAut X).toMonoidHom = MonoidHom.id X := rfl
  have h2 : (MulAut.conj (1 : X)).toMonoidHom = MonoidHom.id X := by
    ext x; simp
  rw [h1, h2]

private theorem step1923_five_map_conj_one (Q : Subgroup X) :
    Q.map (MulAut.conj (1 : X)).toMonoidHom = Q := by
  have h2 : (MulAut.conj (1 : X)).toMonoidHom = MonoidHom.id X := by
    ext x; simp
  rw [h2, Subgroup.map_id]

private theorem step1923_five_map_mul (Q : Subgroup X) {σ τ : MulAut X} {k l : X}
    (hσ : Q.map σ.toMonoidHom = Q.map (MulAut.conj k).toMonoidHom)
    (hτ : Q.map τ.toMonoidHom = Q.map (MulAut.conj l).toMonoidHom) :
    Q.map (σ * τ).toMonoidHom = Q.map (MulAut.conj (σ l * k)).toMonoidHom := by
  have e1 : (σ * τ).toMonoidHom = σ.toMonoidHom.comp τ.toMonoidHom := rfl
  have e2 : σ.toMonoidHom.comp (MulAut.conj l).toMonoidHom =
      (MulAut.conj (σ l)).toMonoidHom.comp σ.toMonoidHom := by
    ext x; simp [MulAut.conj_apply, mul_assoc]
  have e3 : (MulAut.conj (σ l)).toMonoidHom.comp (MulAut.conj k).toMonoidHom =
      (MulAut.conj (σ l * k)).toMonoidHom := by
    ext x; simp [MulAut.conj_apply, mul_assoc]
  rw [e1, ← Subgroup.map_map, hτ, Subgroup.map_map, e2, ← Subgroup.map_map, hσ,
    Subgroup.map_map, e3]

private theorem step1923_five_map_rel (Q : Subgroup X) {σ τ : MulAut X} {g : X}
    (h : Q.map τ.toMonoidHom = (Q.map σ.toMonoidHom).map (MulAut.conj g).toMonoidHom) :
    Q.map (σ⁻¹ * τ).toMonoidHom = Q.map (MulAut.conj (σ⁻¹ g)).toMonoidHom := by
  have hinv : ∀ x : X, σ⁻¹ (σ x) = x := fun x => by
    show σ.symm (σ x) = x
    exact σ.symm_apply_apply x
  have e1 : (σ⁻¹ * τ).toMonoidHom = σ⁻¹.toMonoidHom.comp τ.toMonoidHom := rfl
  have e2 : (σ⁻¹.toMonoidHom.comp (MulAut.conj g).toMonoidHom).comp σ.toMonoidHom =
      (MulAut.conj (σ⁻¹ g)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc, hinv]
  rw [e1, ← Subgroup.map_map, h, Subgroup.map_map, Subgroup.map_map, e2]

private theorem step1923_five_map_inv (Q : Subgroup X) {σ : MulAut X} {k : X}
    (h : Q.map σ.toMonoidHom = Q.map (MulAut.conj k).toMonoidHom) :
    Q.map σ⁻¹.toMonoidHom = Q.map (MulAut.conj (σ⁻¹ k⁻¹)).toMonoidHom := by
  have h1 : Q.map (1 : MulAut X).toMonoidHom =
      (Q.map σ.toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom := by
    rw [h, Subgroup.map_map]
    have e : (MulAut.conj k⁻¹).toMonoidHom.comp (MulAut.conj k).toMonoidHom =
        (MulAut.conj (k⁻¹ * k)).toMonoidHom := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [e, inv_mul_cancel]
    exact step1923_five_map_one Q
  have := step1923_five_map_rel Q (σ := σ) (τ := 1) (g := k⁻¹) h1
  rwa [mul_one] at this

end ClassStab

private theorem step1923_five_K_le (hK : K ∈ scriptJ M N) : K ≤ M := by
  obtain ⟨L, -, hL⟩ := hK.1
  rw [← hL]
  rintro _ ⟨y, -, rfl⟩
  exact y.2

private theorem step1923_five_barAut_eq_conj {K : Subgroup G} {k : G} (hk : k ∈ K)
    (hkN : k ∈ Subgroup.normalizer (K : Set G)) :
    Sec3.Sims321.barAut K ⟨k, hkN⟩ =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 K) (⟨k, hk⟩ : K)) := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) z
  rw [QuotientGroup.mk'_apply, Sec3.Sims321.barAut_mk, MulAut.conj_apply,
    QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  congr 1

private theorem step1923_five_barAut_inv_mul {K : Subgroup G} {a b : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hb : b ∈ Subgroup.normalizer (K : Set G))
    (hab : a⁻¹ * b ∈ Subgroup.normalizer (K : Set G)) :
    Sec3.Sims321.barAut K ⟨a⁻¹ * b, hab⟩ =
      (Sec3.Sims321.barAut K ⟨a, ha⟩)⁻¹ * Sec3.Sims321.barAut K ⟨b, hb⟩ := by
  rw [← map_inv, ← map_mul]
  rfl

private theorem step1923_five_map_barAut_starIm {K N : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) (hxN : x ∈ N) :
    (starIm K N).map (Sec3.Sims321.barAut K ⟨x, hx⟩).toMonoidHom = starIm K N := by
  unfold starIm
  have hconjK : ∀ y ∈ K, x * y * x⁻¹ ∈ K := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hx y).mp hy
  have hconjK' : ∀ y ∈ K, x⁻¹ * y * x ∈ K := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp hy
    simpa using this
  have hconjN : ∀ y ∈ N, x * y * x⁻¹ ∈ N := fun y hy =>
    N.mul_mem (N.mul_mem hxN hy) (N.inv_mem hxN)
  have hconjN' : ∀ y ∈ N, x⁻¹ * y * x ∈ N := fun y hy =>
    N.mul_mem (N.mul_mem (N.inv_mem hxN) hy) hxN
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
    have hyN : (y : G) ∈ N := Subgroup.mem_subgroupOf.mp hy
    show Sec3.Sims321.barAut K ⟨x, hx⟩ (QuotientGroup.mk' (CFSG.pCore 2 K) y) ∈ _
    rw [QuotientGroup.mk'_apply, Sec3.Sims321.barAut_mk]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hconjN _ hyN))
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hyN : (y : G) ∈ N := Subgroup.mem_subgroupOf.mp hy
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (CFSG.pCore 2 K)
      (⟨x⁻¹ * y * x, hconjK' _ y.2⟩ : K), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hconjN' _ hyN))
    · show Sec3.Sims321.barAut K ⟨x, hx⟩
        (QuotientGroup.mk' (CFSG.pCore 2 K) (⟨x⁻¹ * y * x, hconjK' _ y.2⟩ : K)) = _
      rw [QuotientGroup.mk'_apply, Sec3.Sims321.barAut_mk, QuotientGroup.mk'_apply]
      congr 1
      exact Subtype.ext (by simp [mul_assoc])

private theorem step1923_five_inv_stab {K N : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hQ : (starIm K N).map (Sec3.Sims321.barAut K ⟨g, hg⟩).toMonoidHom = starIm K N) :
    (starIm K N).map
        (Sec3.Sims321.barAut K ⟨g⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem hg⟩).toMonoidHom =
      starIm K N := by
  have e : Sec3.Sims321.barAut K ⟨g⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem hg⟩ =
      (Sec3.Sims321.barAut K ⟨g, hg⟩)⁻¹ :=
    map_inv (Sec3.Sims321.barAut K) (⟨g, hg⟩ : Subgroup.normalizer (K : Set G))
  rw [e]
  have h1 : (starIm K N).map (Sec3.Sims321.barAut K ⟨g, hg⟩).toMonoidHom =
      (starIm K N).map (MulAut.conj (1 : K ⧸ CFSG.pCore 2 K)).toMonoidHom := by
    rw [hQ, step1923_five_map_conj_one]
  rw [step1923_five_map_inv (starIm K N) h1, inv_one, map_one]
  exact step1923_five_map_conj_one _

private theorem step1923_five_conj_inf_mem {K N : Subgroup G} (hOKN : CFSG.Open.pCoreOf 2 K ≤ N)
    {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hQ : (starIm K N).map (Sec3.Sims321.barAut K ⟨g, hg⟩).toMonoidHom = starIm K N)
    {x : G} (hx : x ∈ N ⊓ K) : g * x * g⁻¹ ∈ N ⊓ K := by
  have hxK : x ∈ K := hx.2
  have hgxK : g * x * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg x).mp hxK
  refine ⟨?_, hgxK⟩
  have hmem : (QuotientGroup.mk' (CFSG.pCore 2 K) (⟨g * x * g⁻¹, hgxK⟩ : K)) ∈ starIm K N := by
    rw [← hQ]
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (CFSG.pCore 2 K) (⟨x, hxK⟩ : K), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx.1)
    · exact Sec3.Sims321.barAut_mk K ⟨g, hg⟩ ⟨x, hxK⟩
  unfold starIm at hmem
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hyeq
  have hpc := (CFSG.mem_openPCoreOf_iff (y⁻¹ * (⟨g * x * g⁻¹, hgxK⟩ : K))).mpr
    (QuotientGroup.eq.mp hyeq)
  have hpcG : (y : G)⁻¹ * (g * x * g⁻¹) ∈ CFSG.Open.pCoreOf 2 K := by
    simpa using hpc
  have e : g * x * g⁻¹ = (y : G) * ((y : G)⁻¹ * (g * x * g⁻¹)) := by group
  rw [e]
  exact N.mul_mem (Subgroup.mem_subgroupOf.mp hy) (hOKN hpcG)

private theorem step1923_five_mem_normalizer_of {X : Subgroup G} {g : G}
    (h1 : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (h2 : ∀ x ∈ X, g⁻¹ * x * g⁻¹⁻¹ ∈ X) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h1 x
  · intro hx
    have := h2 (g * x * g⁻¹) hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this

private theorem step1923_five_sup_conj {A B : Subgroup G} {g : G}
    (hA : ∀ x ∈ A, g * x * g⁻¹ ∈ A) (hB : ∀ x ∈ B, g * x * g⁻¹ ∈ B) :
    ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ A ⊔ B := by
  have hA' : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact hA x hx
  have hB' : B.map (MulAut.conj g).toMonoidHom ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hB x hx
  have hmap : (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    exact sup_le (hA'.trans le_sup_left) (hB'.trans le_sup_right)
  intro x hx
  exact hmap ⟨x, hx, rfl⟩

private theorem step1923_five_conj_mem {M : Subgroup G} {y o : G} (hy : y ∈ M)
    (ho : o ∈ CFSG.Open.pCoreOf 2 M) : y * o * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hy) o).mp ho

private theorem step1923_five_isSimple {X : Type} [Group X] (hL3 : IsL3OddType X) :
    IsSimpleGroup X := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hL3
  have hs3 : IsSimpleGroup
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 n)) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
  exact (e.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 _)).isSimpleGroup

private theorem step1923_five_relIndex_le_two {H M : Subgroup G}
    (h : ∀ a ∈ M, ∀ b ∈ M, ∀ c ∈ M, a⁻¹ * b ∈ H ∨ a⁻¹ * c ∈ H ∨ b⁻¹ * c ∈ H) :
    H.relIndex M ≤ 2 := by
  classical
  rw [Subgroup.relIndex, Subgroup.index]
  by_contra hlt
  push Not at hlt
  have : Fintype (M ⧸ H.subgroupOf M) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hlt
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hlt
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective z
  rcases h a a.2 b b.2 c c.2 with h1 | h1 | h1
  · exact hxy (QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (by simpa using h1)))
  · exact hxz (QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (by simpa using h1)))
  · exact hyz (QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (by simpa using h1)))

private theorem step1923_five_core (kfl3 : KFL3Par) (h : Hyp1921 G A M N L)
    (hK : K ∈ scriptJ M N) (hKM : M ≤ Subgroup.normalizer (K : Set G))
    (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K))
    (hpar : Sec18.IsMaxParabolicRankTwo (starIm K N)) :
    ∃ M₀ : Subgroup G, K ≤ M₀ ∧ M₀ ≤ M ∧ M₀.relIndex M ≤ 2 ∧ M ⊓ N ≤ M₀ ∧
      ∀ m ∈ M₀, ∃ k : K ⧸ CFSG.pCore 2 K, ∃ hm : m ∈ Subgroup.normalizer (K : Set G),
        (starIm K N).map (Sec3.Sims321.barAut K ⟨m, hm⟩).toMonoidHom =
          (starIm K N).map (MulAut.conj k).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM' : K ≤ M := step1923_five_K_le hK
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : Subgroup G, ∀ m, m ∈ M₀ ↔ ∃ hm : m ∈ M, ∃ y : K ⧸ CFSG.pCore 2 K,
      (starIm K N).map (Sec3.Sims321.barAut K ⟨m, hKM hm⟩).toMonoidHom =
        (starIm K N).map (MulAut.conj y).toMonoidHom := by
    obtain ⟨S, hS⟩ : ∃ S : Set G, ∀ m, m ∈ S ↔ ∃ hm : m ∈ M, ∃ y : K ⧸ CFSG.pCore 2 K,
        (starIm K N).map (Sec3.Sims321.barAut K ⟨m, hKM hm⟩).toMonoidHom =
          (starIm K N).map (MulAut.conj y).toMonoidHom := ⟨_, fun m => Iff.rfl⟩
    refine ⟨{ carrier := S, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun m => hS m⟩
    · intro a b ha hb
      obtain ⟨ha, σk, hk⟩ := (hS a).mp ha
      obtain ⟨hb, l, hl⟩ := (hS b).mp hb
      refine (hS (a * b)).mpr ⟨M.mul_mem ha hb, Sec3.Sims321.barAut K ⟨a, hKM ha⟩ l * σk, ?_⟩
      have e : Sec3.Sims321.barAut K ⟨a * b, hKM (M.mul_mem ha hb)⟩ =
          Sec3.Sims321.barAut K ⟨a, hKM ha⟩ * Sec3.Sims321.barAut K ⟨b, hKM hb⟩ :=
        map_mul (Sec3.Sims321.barAut K) (⟨a, hKM ha⟩ : Subgroup.normalizer (K : Set G))
          (⟨b, hKM hb⟩ : Subgroup.normalizer (K : Set G))
      rw [e]
      exact step1923_five_map_mul _ hk hl
    · refine (hS 1).mpr ⟨M.one_mem, 1, ?_⟩
      have e : Sec3.Sims321.barAut K ⟨1, hKM M.one_mem⟩ = 1 :=
        map_one (Sec3.Sims321.barAut K)
      rw [e]
      exact step1923_five_map_one _
    · intro a ha
      obtain ⟨ha, σk, hk⟩ := (hS a).mp ha
      refine (hS a⁻¹).mpr ⟨M.inv_mem ha, (Sec3.Sims321.barAut K ⟨a, hKM ha⟩)⁻¹ σk⁻¹, ?_⟩
      have e : Sec3.Sims321.barAut K ⟨a⁻¹, hKM (M.inv_mem ha)⟩ =
          (Sec3.Sims321.barAut K ⟨a, hKM ha⟩)⁻¹ :=
        map_inv (Sec3.Sims321.barAut K) (⟨a, hKM ha⟩ : Subgroup.normalizer (K : Set G))
      rw [e]
      exact step1923_five_map_inv _ hk
  have hthree : ∀ a ∈ M, ∀ b ∈ M, ∀ c' ∈ M,
      a⁻¹ * b ∈ M₀ ∨ a⁻¹ * c' ∈ M₀ ∨ b⁻¹ * c' ∈ M₀ := by
    intro a ha b hb c' hc'
    obtain ⟨n, hn, ⟨e⟩⟩ := hL3
    have hA := CFSG.RankThree.PartTwo.Sec20.Res7.isMaxParabolicRankTwo_map
      (Sec3.Sims321.barAut K ⟨a, hKM ha⟩) hpar
    have hB := CFSG.RankThree.PartTwo.Sec20.Res7.isMaxParabolicRankTwo_map
      (Sec3.Sims321.barAut K ⟨b, hKM hb⟩) hpar
    have hC := CFSG.RankThree.PartTwo.Sec20.Res7.isMaxParabolicRankTwo_map
      (Sec3.Sims321.barAut K ⟨c', hKM hc'⟩) hpar
    rcases (kfl3 (K ⧸ CFSG.pCore 2 K) n hn ⟨e⟩).2 _ _ _ hA hB hC with
      ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
    · left
      rw [hM₀]
      refine ⟨M.mul_mem (M.inv_mem ha) hb, (Sec3.Sims321.barAut K ⟨a, hKM ha⟩)⁻¹ g, ?_⟩
      rw [step1923_five_barAut_inv_mul (hKM ha) (hKM hb) (hKM (M.mul_mem (M.inv_mem ha) hb))]
      exact step1923_five_map_rel _ hg
    · right; left
      rw [hM₀]
      refine ⟨M.mul_mem (M.inv_mem ha) hc', (Sec3.Sims321.barAut K ⟨a, hKM ha⟩)⁻¹ g, ?_⟩
      rw [step1923_five_barAut_inv_mul (hKM ha) (hKM hc') (hKM (M.mul_mem (M.inv_mem ha) hc'))]
      exact step1923_five_map_rel _ hg
    · right; right
      rw [hM₀]
      refine ⟨M.mul_mem (M.inv_mem hb) hc', (Sec3.Sims321.barAut K ⟨b, hKM hb⟩)⁻¹ g, ?_⟩
      rw [step1923_five_barAut_inv_mul (hKM hb) (hKM hc') (hKM (M.mul_mem (M.inv_mem hb) hc'))]
      exact step1923_five_map_rel _ hg
  refine ⟨M₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hM₀]
    refine ⟨hKM' hk, QuotientGroup.mk' (CFSG.pCore 2 K) (⟨k, hk⟩ : K), ?_⟩
    rw [step1923_five_barAut_eq_conj hk (hKM (hKM' hk))]
  · intro m hm
    exact ((hM₀ m).mp hm).1
  · exact step1923_five_relIndex_le_two hthree
  · rintro m ⟨hmM, hmN⟩
    rw [hM₀]
    refine ⟨hmM, 1, ?_⟩
    rw [step1923_five_map_barAut_starIm (hKM hmM) hmN, step1923_five_map_conj_one]
  · intro m hm
    obtain ⟨hmM, y, hy⟩ := (hM₀ m).mp hm
    exact ⟨y, hKM hmM, hy⟩

private theorem step1923_five_pCore_K_le (h : Hyp1921 G A M N L) (hKM' : K ≤ M)
    (hKM : M ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 M ∧ CFSG.Open.pCoreOf 2 K ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOKM : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKM')
      (hKM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  exact ⟨hOKM, hOKM.trans (h.setting194.twoCore_M_le.trans
    (CFSG.LieType.BorelTits.pCoreOf_le 2 N))⟩

private theorem step1923_five_key (kfl3two : KFL3Two) (h : Hyp1921 G A M N L)
    (hK : K ∈ scriptJ M N) (hKM : M ≤ Subgroup.normalizer (K : Set G))
    (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K))
    (hpar : Sec18.IsMaxParabolicRankTwo (starIm K N))
    (hC : ∀ m ∈ M, (∀ k ∈ K, m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) → m ∈ N) :
    ∀ z (hz : z ∈ M), (starIm K N).map (Sec3.Sims321.barAut K ⟨z, hKM hz⟩).toMonoidHom =
      starIm K N → z ∈ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM' : K ≤ M := step1923_five_K_le hK
  obtain ⟨hOKM, hOKN⟩ := step1923_five_pCore_K_le h hKM' hKM
  have hset := h.setting194
  obtain ⟨C, hCmem⟩ : ∃ C : Subgroup G, ∀ x, x ∈ C ↔ x ∈ M ∧
      ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
    obtain ⟨S, hS⟩ : ∃ S : Set G, ∀ x, x ∈ S ↔ x ∈ M ∧
        ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M := ⟨_, fun x => Iff.rfl⟩
    refine ⟨{ carrier := S, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun x => hS x⟩
    · intro x y hx hy
      obtain ⟨hxM, hxk⟩ := (hS x).mp hx
      obtain ⟨hyM, hyk⟩ := (hS y).mp hy
      refine (hS (x * y)).mpr ⟨M.mul_mem hxM hyM, fun k hk => ?_⟩
      have e : x * y * k * (x * y)⁻¹ * k⁻¹ =
          x * (y * k * y⁻¹ * k⁻¹) * x⁻¹ * (x * k * x⁻¹ * k⁻¹) := by group
      rw [e]
      exact (CFSG.Open.pCoreOf 2 M).mul_mem (step1923_five_conj_mem hxM (hyk k hk)) (hxk k hk)
    · refine (hS 1).mpr ⟨M.one_mem, fun k hk => ?_⟩
      simp
    · intro x hx
      obtain ⟨hxM, hxk⟩ := (hS x).mp hx
      refine (hS x⁻¹).mpr ⟨M.inv_mem hxM, fun k hk => ?_⟩
      have ho : x * k⁻¹ * x⁻¹ * k ∈ CFSG.Open.pCoreOf 2 M := by
        simpa using hxk k⁻¹ (K.inv_mem hk)
      have e : x⁻¹ * k * x⁻¹⁻¹ * k⁻¹ = x⁻¹ * (k * (x * k⁻¹ * x⁻¹ * k) * k⁻¹) * x⁻¹⁻¹ := by
        group
      rw [e]
      exact step1923_five_conj_mem (M.inv_mem hxM) (step1923_five_conj_mem (hKM' hk) ho)
  have hCN : C ≤ N := fun x hx => hC x ((hCmem x).mp hx).1 ((hCmem x).mp hx).2
  have hCM : ∀ z ∈ M, ∀ x ∈ C, z * x * z⁻¹ ∈ C := by
    intro z hz x hx
    obtain ⟨hxM, hxk⟩ := (hCmem x).mp hx
    refine (hCmem _).mpr ⟨M.mul_mem (M.mul_mem hz hxM) (M.inv_mem hz), fun k hk => ?_⟩
    have hk' : z⁻¹ * k * z ∈ K := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hKM (M.inv_mem hz)) k).mp hk
    have h1 := hxk (z⁻¹ * k * z) hk'
    have e : z * x * z⁻¹ * k * (z * x * z⁻¹)⁻¹ * k⁻¹ =
        z * (x * (z⁻¹ * k * z) * x⁻¹ * (z⁻¹ * k * z)⁻¹) * z⁻¹ := by group
    rw [e]
    exact step1923_five_conj_mem hz h1
  intro z hz hQz
  have hQzinv := step1923_five_inv_stab (hKM hz) hQz
  have hzinc : ∀ x ∈ N ⊓ K, z * x * z⁻¹ ∈ N ⊓ K := fun x hx =>
    step1923_five_conj_inf_mem hOKN (hKM hz) hQz hx
  have hzinc' : ∀ x ∈ N ⊓ K, z⁻¹ * x * z⁻¹⁻¹ ∈ N ⊓ K := fun x hx =>
    step1923_five_conj_inf_mem hOKN ((Subgroup.normalizer (K : Set G)).inv_mem (hKM hz)) hQzinv hx
  have hXz : z ∈ Subgroup.normalizer (((N ⊓ K) ⊔ C : Subgroup G) : Set G) :=
    step1923_five_mem_normalizer_of
      (step1923_five_sup_conj hzinc (fun x hx => hCM z hz x hx))
      (step1923_five_sup_conj hzinc' (fun x hx => hCM z⁻¹ (M.inv_mem hz) x hx))
  have hpar' : Sec18.IsMaxParabolicRankTwo
      (((N ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) := by
    have e : (N ⊓ K).subgroupOf K = N.subgroupOf K := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h' => h'.1, fun h' => ⟨h', x.2⟩⟩
    rw [e]
    exact hpar
  have hSX : ∀ s ∈ CFSG.Open.pCoreOf 2 N, s ∈ (N ⊓ K) ⊔ C := by
    intro s hs
    have hsN : s ∈ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N hs
    have hsM : s ∈ M := hset.twoCore_le_M hs
    have hsnorm : s ∈ Subgroup.normalizer (K : Set G) := hKM hsM
    have hQs := step1923_five_map_barAut_starIm hsnorm hsN
    have hpow : ∃ j : ℕ, Sec3.Sims321.barAut K ⟨s, hsnorm⟩ ^ 2 ^ j = 1 := by
      obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N ⟨s, hs⟩
      refine ⟨j, ?_⟩
      have hs1 : (⟨s, hsnorm⟩ : Subgroup.normalizer (K : Set G)) ^ 2 ^ j = 1 := by
        apply Subtype.ext
        simpa using congrArg Subtype.val hj
      rw [← map_pow, hs1, map_one]
    have hstab : ∃ g : K ⧸ CFSG.pCore 2 K,
        (starIm K N).map (Sec3.Sims321.barAut K ⟨s, hsnorm⟩).toMonoidHom =
          (starIm K N).map (MulAut.conj g).toMonoidHom :=
      ⟨1, by rw [hQs, step1923_five_map_conj_one]⟩
    have hin := kfl3two (K ⧸ CFSG.pCore 2 K) hL3 (starIm K N) hpar _ hpow hstab
    obtain ⟨g', hg'⟩ := MonoidHom.mem_range.mp hin
    obtain ⟨gt, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) g'
    have hbar' : Sec3.Sims321.barAut K ⟨(gt : G), hKM (hKM' gt.2)⟩ =
        MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 K) gt) :=
      step1923_five_barAut_eq_conj gt.2 (hKM (hKM' gt.2))
    have hQgt : (starIm K N).map (Sec3.Sims321.barAut K ⟨(gt : G), hKM (hKM' gt.2)⟩).toMonoidHom =
        starIm K N := by
      rw [hbar', hg', hQs]
    have hgtNK : (gt : G) ∈ Subgroup.normalizer ((N ⊓ K : Subgroup G) : Set G) :=
      step1923_five_mem_normalizer_of
        (fun x hx => step1923_five_conj_inf_mem hOKN (hKM (hKM' gt.2)) hQgt hx)
        (fun x hx => step1923_five_conj_inf_mem hOKN
          ((Subgroup.normalizer (K : Set G)).inv_mem (hKM (hKM' gt.2)))
          (step1923_five_inv_stab (hKM (hKM' gt.2)) hQgt) hx)
    have hgtNK' : (gt : G) ∈ N ⊓ K :=
      CFSG.RankThree.PartTwo.Sec20.Res7.mem_of_mem_normalizer_parabolic
        (le_inf hOKN (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
        (step1923_five_isSimple hL3) hpar' gt.2 hgtNK
    obtain ⟨c, hc⟩ : ∃ c : G, c = s * (gt : G)⁻¹ := ⟨_, rfl⟩
    have hcM : c ∈ M := by
      rw [hc]
      exact M.mul_mem hsM (M.inv_mem (hKM' gt.2))
    have hc1 : Sec3.Sims321.barAut K ⟨c, hKM hcM⟩ = 1 := by
      have e : Sec3.Sims321.barAut K ⟨c, hKM hcM⟩ =
          Sec3.Sims321.barAut K ⟨s, hsnorm⟩ *
            (Sec3.Sims321.barAut K ⟨(gt : G), hKM (hKM' gt.2)⟩)⁻¹ := by
        rw [← map_inv, ← map_mul]
        congr 1
        exact Subtype.ext (by simp [hc])
      rw [e, hbar', ← hg', mul_inv_cancel]
    have hcK : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
      intro k hk
      have hfix : Sec3.Sims321.barAut K ⟨c, hKM hcM⟩
          (QuotientGroup.mk' (CFSG.pCore 2 K) (⟨k, hk⟩ : K)) =
            QuotientGroup.mk' (CFSG.pCore 2 K) (⟨k, hk⟩ : K) := by
        rw [hc1]
        rfl
      rw [QuotientGroup.mk'_apply, Sec3.Sims321.barAut_mk] at hfix
      have hq := QuotientGroup.eq.mp hfix
      have ht : (c * k * c⁻¹)⁻¹ * k ∈ CFSG.Open.pCoreOf 2 K := by
        have := (CFSG.mem_openPCoreOf_iff _).mpr hq
        simpa using this
      have e : c * k * c⁻¹ * k⁻¹ = k * ((c * k * c⁻¹)⁻¹ * k)⁻¹ * k⁻¹ := by group
      rw [e]
      exact step1923_five_conj_mem (hKM' hk) ((CFSG.Open.pCoreOf 2 M).inv_mem (hOKM ht))
    have hcC : c ∈ C := (hCmem c).mpr ⟨hcM, hcK⟩
    have hsc : s = c * (gt : G) := by
      rw [hc]
      group
    rw [hsc]
    exact ((N ⊓ K) ⊔ C).mul_mem (Subgroup.mem_sup_right hcC) (Subgroup.mem_sup_left hgtNK')
  have hX₁N : (N ⊓ K) ⊔ C ≤ N := sup_le inf_le_left hCN
  have hX₁M : (N ⊓ K) ⊔ C ≤ M :=
    sup_le (inf_le_right.trans hKM') (fun x hx => ((hCmem x).mp hx).1)
  have hSsub : CFSG.Open.pCoreOf 2 N ≤ CFSG.Open.pCoreOf 2 ((N ⊓ K) ⊔ C) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSX
      (by rw [hset.normalizer_twoCore]; exact hX₁N) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
  have hX₁norm : ∀ n ∈ N ⊓ M, n ∈ Subgroup.normalizer (((N ⊓ K) ⊔ C : Subgroup G) : Set G) := by
    intro n hn
    have hnK : n ∈ Subgroup.normalizer (K : Set G) := hKM hn.2
    have hQn := step1923_five_map_barAut_starIm hnK hn.1
    have hconj : ∀ x ∈ (N ⊓ K) ⊔ C, n * x * n⁻¹ ∈ (N ⊓ K) ⊔ C :=
      step1923_five_sup_conj (fun y hy => step1923_five_conj_inf_mem hOKN hnK hQn hy)
        (fun y hy => hCM n hn.2 y hy)
    have hconj' : ∀ x ∈ (N ⊓ K) ⊔ C, n⁻¹ * x * n⁻¹⁻¹ ∈ (N ⊓ K) ⊔ C :=
      step1923_five_sup_conj
        (fun y hy => step1923_five_conj_inf_mem hOKN
          ((Subgroup.normalizer (K : Set G)).inv_mem hnK) (step1923_five_inv_stab hnK hQn) hy)
        (fun y hy => hCM n⁻¹ (M.inv_mem hn.2) y hy)
    exact step1923_five_mem_normalizer_of hconj hconj'
  have hSeq : CFSG.Open.pCoreOf 2 ((N ⊓ K) ⊔ C) = CFSG.Open.pCoreOf 2 N := by
    have h1 : (N ⊓ K) ⊔ C ≤ N ⊓ M := le_inf hX₁N hX₁M
    have h2 : CFSG.Open.pCoreOf 2 ((N ⊓ K) ⊔ C) ≤ CFSG.Open.pCoreOf 2 (N ⊓ M) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans h1)
        (fun n hn => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
          (hX₁norm n hn))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    rw [hset.twoCore_inf] at h2
    exact le_antisymm h2 hSsub
  have hz2 : z ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 ((N ⊓ K) ⊔ C) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hXz
  rw [hSeq, hset.normalizer_twoCore] at hz2
  exact hz2

theorem item1923_five_b (kfl3two : KFL3Two) (h : Hyp1921 G A M N L)
    (hK : K ∈ scriptJ M N) (hKM : M ≤ Subgroup.normalizer (K : Set G))
    (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K))
    (hpar : Sec18.IsMaxParabolicRankTwo (starIm K N)) {M₀ : Subgroup G} (hM₀ : M₀ ≤ M)
    (hKM₀ : K ≤ M₀)
    (hM₀K : ∀ m ∈ M₀, ∃ k : K ⧸ CFSG.pCore 2 K, ∃ hm : m ∈ Subgroup.normalizer (K : Set G),
        (starIm K N).map (Sec3.Sims321.barAut K ⟨m, hm⟩).toMonoidHom =
          (starIm K N).map (MulAut.conj k).toMonoidHom)
    (hC : ∀ m ∈ M, (∀ k ∈ K, m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) → m ∈ N) :
    M₀ = K ⊔ (M₀ ⊓ N) := by
  have hKM' : K ≤ M := step1923_five_K_le hK
  have hkey := step1923_five_key kfl3two h hK hKM hL3 hpar hC
  apply le_antisymm
  · intro y hy
    obtain ⟨k', hyk, hyeq⟩ := hM₀K y hy
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) k'
    have hkK : (k : G) ∈ K := k.2
    have hkM : (k : G) ∈ M := hKM' hkK
    have hzM : (k : G)⁻¹ * y ∈ M := M.mul_mem (M.inv_mem hkM) (hM₀ hy)
    have hrel : (starIm K N).map (Sec3.Sims321.barAut K ⟨y, hyk⟩).toMonoidHom =
        ((starIm K N).map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 K) k)).toMonoidHom).map
          (MulAut.conj (1 : K ⧸ CFSG.pCore 2 K)).toMonoidHom := by
      rw [hyeq, step1923_five_map_conj_one]
    have hQz : (starIm K N).map
        (Sec3.Sims321.barAut K ⟨(k : G)⁻¹ * y, hKM hzM⟩).toMonoidHom = starIm K N := by
      have e : Sec3.Sims321.barAut K ⟨(k : G)⁻¹ * y, hKM hzM⟩ =
          (Sec3.Sims321.barAut K ⟨(k : G), hKM hkM⟩)⁻¹ * Sec3.Sims321.barAut K ⟨y, hyk⟩ :=
        step1923_five_barAut_inv_mul (hKM hkM) hyk (hKM hzM)
      rw [e, step1923_five_barAut_eq_conj hkK (hKM hkM)]
      have := step1923_five_map_rel (starIm K N)
        (σ := MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 K) k))
        (τ := Sec3.Sims321.barAut K ⟨y, hyk⟩) (g := 1) hrel
      rw [this, map_one, step1923_five_map_conj_one]
    have hzN : (k : G)⁻¹ * y ∈ N := hkey _ hzM hQz
    have hzM₀ : (k : G)⁻¹ * y ∈ M₀ := M₀.mul_mem (M₀.inv_mem (hKM₀ hkK)) hy
    have hyk' : y = (k : G) * ((k : G)⁻¹ * y) := by group
    rw [hyk']
    exact (K ⊔ (M₀ ⊓ N)).mul_mem (Subgroup.mem_sup_left hkK)
      (Subgroup.mem_sup_right ⟨hzM₀, hzN⟩)
  · exact sup_le hKM₀ inf_le_left

private theorem step1923_five_relIndex_K (h : Hyp1921 G A M N L) (hKM' : K ≤ M)
    (hKM : M ≤ Subgroup.normalizer (K : Set G)) :
    (K ⊓ N).relIndex K = (starIm K N).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hOKN⟩ := step1923_five_pCore_K_le h hKM' hKM
  have hsub : (K ⊓ N).subgroupOf K = N.subgroupOf K := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h' => h'.2, fun h' => ⟨x.2, h'⟩⟩
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 K)).ker ≤ N.subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hOKN ((CFSG.mem_openPCoreOf_iff x).mpr hx))
  rw [Subgroup.relIndex, hsub]
  unfold starIm
  exact (Subgroup.index_map_eq (N.subgroupOf K) (QuotientGroup.mk'_surjective _) hker).symm

private theorem step1923_five_relIndex_eq {M₀ : Subgroup G} (hKM₀ : K ≤ M₀)
    (hM₀N : M₀ ≤ Subgroup.normalizer (K : Set G)) (hM₀eq : M₀ = K ⊔ (M₀ ⊓ N)) :
    (M₀ ⊓ N).relIndex M₀ = (K ⊓ N).relIndex K := by
  have hXM₀ : M₀ ⊓ N ≤ M₀ := inf_le_left
  have hXN : M₀ ⊓ N ≤ Subgroup.normalizer (K : Set G) := hXM₀.trans hM₀N
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hXN
  rw [← hM₀eq] at hcard
  have hKX : K ⊓ (M₀ ⊓ N) = K ⊓ N := by
    apply le_antisymm
    · exact fun x hx => ⟨hx.1, hx.2.2⟩
    · exact fun x hx => ⟨hx.1, hKM₀ hx.1, hx.2⟩
  rw [hKX] at hcard
  have h1 := Subgroup.relIndex_mul_card (H := M₀ ⊓ N) (K := M₀)
  have hXinf : (M₀ ⊓ N) ⊓ M₀ = M₀ ⊓ N := inf_eq_left.mpr hXM₀
  rw [hXinf] at h1
  have h2 := Subgroup.relIndex_mul_card (H := K ⊓ N) (K := K)
  have hKNK : (K ⊓ N) ⊓ K = K ⊓ N := inf_eq_left.mpr inf_le_left
  rw [hKNK] at h2
  have hpos : 0 < Nat.card (K ⊓ N : Subgroup G) * Nat.card (M₀ ⊓ N : Subgroup G) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (M₀ ⊓ N).relIndex M₀ * (Nat.card (K ⊓ N : Subgroup G) * Nat.card (M₀ ⊓ N : Subgroup G))
      = ((M₀ ⊓ N).relIndex M₀ * Nat.card (M₀ ⊓ N : Subgroup G)) *
          Nat.card (K ⊓ N : Subgroup G) := by ring
    _ = Nat.card M₀ * Nat.card (K ⊓ N : Subgroup G) := by rw [h1]
    _ = Nat.card K * Nat.card (M₀ ⊓ N : Subgroup G) := hcard
    _ = ((K ⊓ N).relIndex K * Nat.card (K ⊓ N : Subgroup G)) *
          Nat.card (M₀ ⊓ N : Subgroup G) := by rw [h2]
    _ = (K ⊓ N).relIndex K * (Nat.card (K ⊓ N : Subgroup G) *
          Nat.card (M₀ ⊓ N : Subgroup G)) := by ring

private theorem step1923_five_of_index (kfl3 : KFL3Par) (kfl3two : KFL3Two)
    (h : Hyp1921 G A M N L) (hK : K ∈ scriptJ M N) (hKM : M ≤ Subgroup.normalizer (K : Set G))
    (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K)) (hpar : Sec18.IsMaxParabolicRankTwo (starIm K N))
    (hC : ∀ m ∈ M, (∀ k ∈ K, m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) → m ∈ N) {n : ℕ}
    (hidx : (starIm K N).index = (2 ^ n) ^ 2 + 2 ^ n + 1) :
    ∃ ε : ℕ, (ε = 1 ∨ ε = 2) ∧ (M ⊓ N).relIndex M = ((2 ^ n) ^ 2 + 2 ^ n + 1) * ε := by
  have hKM' : K ≤ M := step1923_five_K_le hK
  obtain ⟨M₀, hKM₀, hM₀M, hrel, hMN, hM₀K⟩ := step1923_five_core kfl3 h hK hKM hL3 hpar
  have hM₀eq := item1923_five_b kfl3two h hK hKM hL3 hpar hM₀M hKM₀ hM₀K hC
  have hMN_eq : M ⊓ N = M₀ ⊓ N :=
    le_antisymm (le_inf hMN inf_le_right) (inf_le_inf_right N hM₀M)
  refine ⟨M₀.relIndex M, ?_, ?_⟩
  · have h0 : M₀.relIndex M ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    omega
  · rw [← Subgroup.relIndex_mul_relIndex (M ⊓ N) M₀ M hMN hM₀M, hMN_eq,
      step1923_five_relIndex_eq hKM₀ (hM₀M.trans hKM) hM₀eq,
      step1923_five_relIndex_K h hKM' hKM, hidx]

private theorem step1923_five_card_ne (n : ℕ) (hn : Odd n) :
    Nat.card (projSL 3 (GaloisField 2 n)) ≠ 1814400 := by
  intro h
  obtain ⟨m, rfl⟩ := hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  have hmul := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSL_three_mul_gcd
    (GaloisField 2 (2 * m + 1))
  rw [hq, h] at hmul
  have hmod : 2 ^ (2 * m + 1) % 3 = 2 := by
    have h4 : 4 ^ m % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    have h2 : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
      rw [pow_succ, pow_mul]; ring
    rw [h2]; omega
  have hg : Nat.gcd 3 (2 ^ (2 * m + 1) - 1) = 1 := by
    have hnd : ¬ 3 ∣ 2 ^ (2 * m + 1) - 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnd
  rw [hg, mul_one] at hmul
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · norm_num at hmul
  · have hq8 : 8 ≤ 2 ^ (2 * m + 1) :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 2 ^ (2 * m + 1) = q at hmul hq8
    have h2q : 64 ≤ q ^ 2 := by nlinarith
    have h3q : 512 ≤ q ^ 3 := by nlinarith
    have h1' : 63 ≤ q ^ 2 - 1 := by omega
    have h2' : 511 ≤ q ^ 3 - 1 := by omega
    have key := Nat.mul_le_mul h3q (Nat.mul_le_mul h1' h2')
    linarith

private theorem step1923_five_false_alt10 {X : Type} [Group X] (hL3 : IsL3OddType X)
    (hA : Nonempty (X ≃* alternatingGroup (Fin 10))) : False := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hL3
  obtain ⟨eA⟩ := hA
  have h1 : Nat.card (projSL 3 (GaloisField 2 n)) = Nat.card X :=
    Nat.card_congr e.toEquiv.symm
  have h2 : Nat.card X = Nat.card (alternatingGroup (Fin 10)) := Nat.card_congr eA.toEquiv
  have h3 : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
    rw [nat_card_alternatingGroup]; simp [Nat.factorial]
  exact step1923_five_card_ne n hn (h1.trans (h2.trans h3))

private theorem step1923_five_orderOf_mk {K : Subgroup G} {c : G} (hcK : c ∈ K)
    (h3 : orderOf c = 3) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K)) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : c ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one c
  apply orderOf_eq_prime
  · have hx3 : (⟨c, hcK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [← map_pow, hx3, map_one]
  · intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hcO : c ∈ CFSG.Open.pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff _).mpr h1
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨c, hcO⟩
    have hck : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := by
      rw [← h3]; exact orderOf_dvd_of_pow_eq_one hck
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at this

theorem item1923_five (hkf : KFacts1923) (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ scriptJ M N) (hKM : M ≤ Subgroup.normalizer (K : Set G))
    (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K))
    (hpar : Sec18.IsMaxParabolicRankTwo (starIm K N)) (hcK : c ∈ K)
    (hC : ∀ m ∈ M, (∀ k ∈ K, m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) → m ∈ N) :
    ∃ n : ℕ, Odd n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n)) ∧
      ∃ ε : ℕ, (ε = 1 ∨ ε = 2) ∧ (M ⊓ N).relIndex M = ((2 ^ n) ^ 2 + 2 ^ n + 1) * ε := by
  have hL3' := hL3
  obtain ⟨n, hn, ⟨e⟩⟩ := hL3'
  have hcA : c ∈ A := by
    rw [hF.eq_sup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hcN : c ∈ N := h.le_N hcA
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K) ∈ starIm K N :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hcN)
  have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K)) = 3 :=
    step1923_five_orderOf_mk hcK hF.orderOf_c
  have hproper : IsProperParabolic (starIm K N) := by
    obtain ⟨-, hshape⟩ := step1923_list hkf.h194 h hK
    rcases hshape with ⟨-, hp⟩ | ⟨hA, -⟩
    · exact hp
    · exact (step1923_five_false_alt10 hL3 hA).elim
  have hidx : (starIm K N).index = (2 ^ n) ^ 2 + 2 ^ n + 1 :=
    ((hkf.kfl3par (K ⧸ CFSG.pCore 2 K) n hn ⟨e⟩).1 (starIm K N) hproper ⟨_, hmem, hord⟩).2
  obtain ⟨ε, hε, hrel⟩ :=
    step1923_five_of_index hkf.kfl3par hkf.kfl3two h hK hKM hL3 hpar hC hidx
  exact ⟨n, hn, ⟨e⟩, ε, hε, hrel⟩

end CFSG.RankThree.PartTwo.Late
