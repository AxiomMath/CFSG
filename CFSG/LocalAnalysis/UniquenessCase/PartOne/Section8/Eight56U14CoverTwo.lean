module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight5xAShared
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import CFSG.GroupTheory.SylowIntersectionControl.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordsLift
import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 calC)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (IsA6Z3 IsA7Z3 IsM22Z3)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)

theorem card_sup_zpowers_of_commute_three {G : Type} [Group G] [Finite G] {S : Subgroup G} {g : G}
    (hS : ∀ s ∈ S, s * g = g * s) (hg3 : g ^ 3 = 1) (hgS : g ∉ S) :
    Nat.card ↥(S ⊔ zpowers g) = Nat.card S * 3 := by
  have hg1 : g ≠ 1 := fun h => hgS (h ▸ S.one_mem)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hN : zpowers g ≤ normalizer (S : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    by_cases hh : h ∈ S
    · have : g * h * g⁻¹ = h := by rw [← hS h hh, mul_inv_cancel_right]
      simp [this, hh]
    · constructor
      · intro h'; exact absurd h' hh
      · intro h'
        exfalso; apply hh
        have h2 := hS _ h'
        have : h = g * h * g⁻¹ := by
          calc h = g⁻¹ * (g * h * g⁻¹ * g) := by group
            _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [h2]
            _ = g * h * g⁻¹ := by group
        rw [this]; exact h'
  have hcard := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hN
  rw [Nat.card_zpowers, hord, sup_comm] at hcard
  have hinf : Nat.card ↥(zpowers g ⊓ S) = 1 := by
    have hdvd : Nat.card ↥(zpowers g ⊓ S) ∣ 3 := by
      rw [← hord, ← Nat.card_zpowers]; exact card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso; apply hgS
      have heq : zpowers g ⊓ S = zpowers g :=
        eq_of_le_of_card_ge inf_le_left (by rw [h, Nat.card_zpowers, hord])
      have : g ∈ zpowers g ⊓ S := by rw [heq]; exact mem_zpowers g
      exact this.2
  rw [hinf, mul_one] at hcard
  rw [hcard, mul_comm]

theorem isElemAbelian_sup_zpowers_of_commute_three {G : Type} [Group G] [Finite G]
    {S : Subgroup G} {g : G} (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hS3 : ∀ a ∈ S, a ^ 3 = 1) (hS : ∀ s ∈ S, s * g = g * s) (hg3 : g ^ 3 = 1) :
    (∀ a ∈ S ⊔ zpowers g, ∀ b ∈ S ⊔ zpowers g, a * b = b * a) ∧
      ∀ a ∈ S ⊔ zpowers g, a ^ 3 = 1 := by
  have hcent : S ⊔ zpowers g ≤ centralizer ((S ⊔ zpowers g : Subgroup G) : Set G) := by
    have h1 : S ⊔ zpowers g ≤ centralizer (S : Set G) := by
      refine sup_le (fun a ha => mem_centralizer_iff.mpr fun b hb => hSc b hb a ha) ?_
      rw [zpowers_le]; exact mem_centralizer_iff.mpr fun b hb => hS b hb
    have h2 : S ⊔ zpowers g ≤ centralizer ((zpowers g : Subgroup G) : Set G) := by
      refine sup_le ?_ ?_
      · intro a ha
        rw [mem_centralizer_iff]
        intro b hb
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
        exact ((Commute.zpow_left (show Commute g a from (hS a ha).symm) k)).eq
      · rw [zpowers_le, mem_centralizer_iff]
        intro b hb
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
        exact ((Commute.zpow_left (Commute.refl g) k)).eq
    rw [← le_centralizer_iff] at h1 h2
    rw [le_centralizer_iff]
    exact sup_le h1 h2
  have hcomm : ∀ a ∈ S ⊔ zpowers g, ∀ b ∈ S ⊔ zpowers g, a * b = b * a :=
    fun a ha b hb => (mem_centralizer_iff.mp (hcent hb) a ha)
  refine ⟨hcomm, ?_⟩
  let T : Subgroup G :=
    { carrier := {a | a ∈ S ⊔ zpowers g ∧ a ^ 3 = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hcomm a ha.1 b hb.1) 3), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow 3⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hT : S ⊔ zpowers g ≤ T := by
    refine sup_le (fun a ha => ⟨mem_sup_left ha, hS3 a ha⟩) ?_
    rw [zpowers_le]; exact ⟨mem_sup_right (mem_zpowers g), hg3⟩
  exact fun a ha => (hT ha).2

theorem false_of_two_commuting_extraspecial {G : Type} [Group G] [Finite G]
    {P Q Q₁ X : Subgroup G}
    (hQ : IsExtraspecialExpP 3 1 ↥Q) (hQ₁ : IsExtraspecialExpP 3 1 ↥Q₁)
    (hQP : Q ≤ P) (hQ₁P : Q₁ ≤ P) (hPrank : CFSG.Open.pRank 3 P ≤ 3)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q₁, a * b = b * a)
    (hXQ : ∀ x ∈ X, ∀ a ∈ Q, x * a = a * x) (hXQ₁ : ∀ x ∈ X, ∀ b ∈ Q₁, x * b = b * x)
    (hXP : X ≤ P) (hX : Nat.card X = 3) (hXZ : ¬ X ≤ Q ⊓ centralizer (Q : Set G)) : False := by
  have noncentral : ∀ {R : Subgroup G}, IsExtraspecialExpP 3 1 ↥R →
      ∃ a ∈ R, a ∉ R ⊓ centralizer (R : Set G) := by
    intro R hR
    unfold IsExtraspecialExpP at hR
    by_contra h; push Not at h
    have hab : center ↥R = ⊤ := by
      rw [eq_top_iff]; intro a _
      rw [mem_center_iff]; intro b
      exact Subtype.ext ((mem_centralizer_iff.mp (h a a.2).2 b b.2))
    have := hR.2.2.2; rw [hab, card_top, hR.1] at this; norm_num at this
  obtain ⟨a, haQ, haZ⟩ := noncentral hQ
  obtain ⟨b, hbQ₁, hbZ⟩ := noncentral hQ₁
  unfold IsExtraspecialExpP at hQ hQ₁
  have hexpQ : ∀ a ∈ Q, a ^ 3 = 1 := fun a ha => by
    have := Monoid.pow_exponent_eq_one (⟨a, ha⟩ : Q); rw [hQ.2.1] at this
    exact congrArg Subtype.val this
  have hexpQ₁ : ∀ a ∈ Q₁, a ^ 3 = 1 := fun a ha => by
    have := Monoid.pow_exponent_eq_one (⟨a, ha⟩ : Q₁); rw [hQ₁.2.1] at this
    exact congrArg Subtype.val this
  have hexpX : ∀ a ∈ X, a ^ 3 = 1 := fun a ha => by
    have h : (⟨a, ha⟩ : X) ^ Nat.card X = 1 := pow_card_eq_one'
    rw [hX] at h
    exact congrArg Subtype.val h
  have hZ3 := hQ.2.2.2
  obtain ⟨c, hc⟩ : ∃ c : center ↥Q, c ≠ 1 := by
    by_contra h; push Not at h
    have : Nat.card (center ↥Q) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => (h a).trans (h b).symm⟩
    omega
  set z : G := ((c : Q) : G) with hz
  have hzQ : z ∈ Q := (c : Q).2
  have hzc : ∀ a ∈ Q, z * a = a * z := fun a ha => by
    have := (mem_center_iff.mp c.2 ⟨a, ha⟩).symm
    exact congrArg Subtype.val this
  have hz1 : z ≠ 1 := fun h => hc (Subtype.ext (Subtype.ext h))
  obtain ⟨x, hxX, hxZ⟩ := Set.not_subset.mp hXZ
  set S₁ : Subgroup G := zpowers z
  set S₂ : Subgroup G := S₁ ⊔ zpowers x
  set S₃ : Subgroup G := S₂ ⊔ zpowers a
  set S₄ : Subgroup G := S₃ ⊔ zpowers b
  have cQ1 : S₁ ≤ centralizer (Q : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]; exact fun y hy => (hzc y hy).symm
  have cQ2 : S₂ ≤ centralizer (Q : Set G) := sup_le cQ1 (by
    rw [zpowers_le, mem_centralizer_iff]; exact fun y hy => (hXQ x hxX y hy).symm)
  have cQ₁1 : S₁ ≤ centralizer (Q₁ : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]; exact fun y hy => (hcomm z hzQ y hy).symm
  have cQ₁3 : S₃ ≤ centralizer (Q₁ : Set G) := sup_le (sup_le cQ₁1 (by
    rw [zpowers_le, mem_centralizer_iff]; exact fun y hy => (hXQ₁ x hxX y hy).symm)) (by
    rw [zpowers_le, mem_centralizer_iff]; exact fun y hy => (hcomm a haQ y hy).symm)
  have cx1 : S₁ ≤ centralizer ({x} : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]; intro y hy; rw [Set.mem_singleton_iff.mp hy]
    exact hXQ x hxX z hzQ
  have ca2 : S₂ ≤ centralizer ({a} : Set G) := sup_le (by
      rw [zpowers_le, mem_centralizer_iff]; intro y hy; rw [Set.mem_singleton_iff.mp hy]
      exact (hzc a haQ).symm) (by
      rw [zpowers_le, mem_centralizer_iff]; intro y hy; rw [Set.mem_singleton_iff.mp hy]
      exact (hXQ x hxX a haQ).symm)
  have toS : ∀ {S : Subgroup G} {g : G}, S ≤ centralizer ({g} : Set G) → ∀ s ∈ S, s * g = g * s :=
    fun {_ g} h s hs => (mem_centralizer_iff.mp (h hs) g rfl).symm
  have cb3 : S₃ ≤ centralizer ({b} : Set G) := fun y hy =>
    mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff.mp hw]; exact (mem_centralizer_iff.mp (cQ₁3 hy) b hbQ₁)
  have hx2 : x ∉ S₁ := fun h =>
    hxZ ⟨(mem_zpowers_iff.mp h).elim fun k hk => hk ▸ zpow_mem hzQ k, cQ1 h⟩
  have ha3 : a ∉ S₂ := fun h => haZ ⟨haQ, cQ2 h⟩
  have hb4 : b ∉ S₃ := fun h => hbZ ⟨hbQ₁, cQ₁3 h⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : Nat.card S₁ = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hexpQ z hzQ) hz1]
  have h2 : Nat.card S₂ = 9 := by
    rw [card_sup_zpowers_of_commute_three (toS cx1) (hexpX x hxX) hx2, h1]
  have h3 : Nat.card S₃ = 27 := by
    rw [card_sup_zpowers_of_commute_three (toS ca2) (hexpQ a haQ) ha3, h2]
  have h4 : Nat.card S₄ = 3 ^ 4 := by
    rw [card_sup_zpowers_of_commute_three (toS cb3) (hexpQ₁ b hbQ₁) hb4, h3]; norm_num
  have e1 : (∀ u ∈ S₁, ∀ v ∈ S₁, u * v = v * u) ∧ ∀ u ∈ S₁, u ^ 3 = 1 := by
    have := isElemAbelian_sup_zpowers_of_commute_three (S := ⊥) (g := z) (by simp) (by simp)
      (by simp) (hexpQ z hzQ)
    simpa [S₁] using this
  have e2 := isElemAbelian_sup_zpowers_of_commute_three e1.1 e1.2 (toS cx1) (hexpX x hxX)
  have e3 := isElemAbelian_sup_zpowers_of_commute_three e2.1 e2.2 (toS ca2) (hexpQ a haQ)
  have e4 := isElemAbelian_sup_zpowers_of_commute_three e3.1 e3.2 (toS cb3) (hexpQ₁ b hbQ₁)
  have hE : IsElemAbelian 3 S₄ :=
    ⟨⟨⟨fun u v => Subtype.ext (e4.1 u u.2 v v.2)⟩⟩, e4.2⟩
  have hS₄P : S₄ ≤ P := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_ <;> rw [zpowers_le]
    · exact hQP hzQ
    · exact hXP hxX
    · exact hQP haQ
    · exact hQ₁P hbQ₁
  have := CFSG.SectionRank.le_pRank (by norm_num) hS₄P hE h4
  omega

theorem ChoiceX.centralizes_sylowQ {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P X : Subgroup G} (h : ChoiceX D L Q P X) (h859 : R859 D)
    (hXL : ⁅L, X⁆ ≤ pCoreOf 2 L) :
    ∀ x ∈ X, ∀ a ∈ Q, x * a = a * x := by
  intro x hx a ha
  have hxN := h.cex.le_normalizer_sylowQ h859 (h.le hx)
  have h1 : ⁅a, x⁆ ∈ pCoreOf 2 L :=
    hXL (Subgroup.commutator_mem_commutator (h.cex.sylowQ.le ha) hx)
  have h2 : ⁅a, x⁆ ∈ Q := by
    have h3 : x * a⁻¹ * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxN a⁻¹).mp (Q.inv_mem ha)
    have h4 : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [h4]
    exact Q.mul_mem ha h3
  have h5 : ⁅a, x⁆ ∈ Q ⊓ pCoreOf 2 L := ⟨h2, h1⟩
  rw [h.cex.inf_pCore_eq_bot] at h5
  exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h5)).symm

private theorem covtwoa_map_conj_map_conj {G : Type} [Group G] (K : Subgroup G) (g h : G) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      K.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem covtwoa_map_conj_one {G : Type} [Group G] (K : Subgroup G) :
    K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map]

private theorem covtwoa_mem_self {G : Type} [Group G] (M L : Subgroup G) : L ∈ MConjSet M L :=
  ⟨1, M.one_mem, (covtwoa_map_conj_one L).symm⟩

private theorem covtwoa_mem_map {G : Type} [Group G] {M L K : Subgroup G} {m : G} (hm : m ∈ M)
    (hK : K ∈ MConjSet M L) : K.map (MulAut.conj m).toMonoidHom ∈ MConjSet M L := by
  obtain ⟨g, hg, rfl⟩ := hK
  exact ⟨m * g, M.mul_mem hm hg, covtwoa_map_conj_map_conj L g m⟩

private def covtwoa_perm {G : Type} [Group G] (M L : Subgroup G) :
    ↥M →* Equiv.Perm ↥(MConjSet M L) where
  toFun m :=
    { toFun := fun K => ⟨K.1.map (MulAut.conj (m : G)).toMonoidHom, covtwoa_mem_map m.2 K.2⟩
      invFun := fun K =>
        ⟨K.1.map (MulAut.conj (m : G)⁻¹).toMonoidHom, covtwoa_mem_map (M.inv_mem m.2) K.2⟩
      left_inv := fun K => Subtype.ext (by
        simp only [covtwoa_map_conj_map_conj, inv_mul_cancel, covtwoa_map_conj_one])
      right_inv := fun K => Subtype.ext (by
        simp only [covtwoa_map_conj_map_conj, mul_inv_cancel, covtwoa_map_conj_one]) }
  map_one' := Equiv.ext fun K => Subtype.ext (by
    simp only [Equiv.coe_fn_mk, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq,
      covtwoa_map_conj_one])
  map_mul' a b := Equiv.ext fun K => Subtype.ext (by
    simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_mul, Function.comp_apply,
      covtwoa_map_conj_map_conj, Subgroup.coe_mul])

private theorem covtwoa_eq_or {G : Type} [Group G] [Finite G] {M L L' K : Subgroup G}
    (hcard : (MConjSet M L).ncard = 2) (hL' : L' ∈ MConjSet M L) (hne : L' ≠ L)
    (hK : K ∈ MConjSet M L) : K = L ∨ K = L' := by
  have hsub : ({L, L'} : Set (Subgroup G)) ⊆ MConjSet M L := by
    intro X hX
    rcases hX with h | h
    · rw [h]; exact covtwoa_mem_self M L
    · rw [Set.mem_singleton_iff.mp h]; exact hL'
  have heq : ({L, L'} : Set (Subgroup G)) = MConjSet M L :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, Set.ncard_pair hne.symm]) (Set.toFinite _)
  rw [← heq] at hK
  exact hK

private theorem covtwoa_mem_normalizer_other {G : Type} [Group G] [Finite G] {M L L' : Subgroup G}
    (hcard : (MConjSet M L).ncard = 2) (hL' : L' ∈ MConjSet M L) (hne : L' ≠ L) {m : G}
    (hm : m ∈ M) (hmL : m ∈ normalizer (L : Set G)) : m ∈ normalizer (L' : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hmL ⊢
  rcases covtwoa_eq_or hcard hL' hne (covtwoa_mem_map hm hL') with h | h
  · exact absurd (Subgroup.map_injective (MulAut.conj m).injective (h.trans hmL.symm)) hne
  · exact h

private theorem covtwoa_le_normalizer {G : Type} [Group G] [Finite G] {M L L' : Subgroup G}
    (hcard : (MConjSet M L).ncard = 2) (hL'M : L' ≤ M) (hperf : ⁅L', L'⁆ = L') :
    L' ≤ normalizer (L : Set G) := by
  have hLS := covtwoa_mem_self M L
  have : IsMulCommutative (Equiv.Perm ↥(MConjSet M L)) :=
    (Equiv.Perm.isCyclic_of_card_le_two (by rw [Nat.card_coe_set_eq, hcard])).isMulCommutative
  have : Group.IsPerfect ↥L' := Subgroup.isPerfect_iff.mpr hperf
  let φ : ↥L' →* Equiv.Perm ↥(MConjSet M L) :=
    (covtwoa_perm M L).comp (Subgroup.inclusion hL'M)
  have hker : commutator ↥L' ≤ φ.ker := Abelianization.commutator_subset_ker φ
  intro m hm
  have h1 : φ ⟨m, hm⟩ = 1 := hker Group.IsPerfect.mem_commutator
  have h2 := congrArg
    (fun σ : Equiv.Perm ↥(MConjSet M L) => ((σ ⟨L, hLS⟩ : ↥(MConjSet M L)) : Subgroup G)) h1
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2

theorem exists_other_conj_of_ncard_two {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (hL : L ∈ calC D.M) (hcard : (MConjSet D.M L).ncard = 2)
    (hPM : P ≤ D.M) (hPL : P ≤ normalizer (L : Set G)) :
    ∃ L' ∈ MConjSet D.M L, L' ≠ L ∧ P ≤ normalizer (L' : Set G) ∧
      L ≤ normalizer (L' : Set G) ∧ L' ≤ normalizer (L : Set G) := by
  obtain ⟨x, y, hxy, hS⟩ := Set.ncard_eq_two.mp hcard
  have hLS := covtwoa_mem_self D.M L
  obtain ⟨L', hL'S, hne⟩ : ∃ L' ∈ MConjSet D.M L, L' ≠ L := by
    rw [hS] at hLS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hLS
    rcases hLS with h | h
    · exact ⟨y, by rw [hS]; exact Or.inr rfl, fun hyL => hxy (h.symm.trans hyL.symm)⟩
    · exact ⟨x, by rw [hS]; exact Or.inl rfl, fun hxL => hxy (hxL.trans h)⟩
  have hLM : L ≤ D.M := hL.1.le
  obtain ⟨m₀, hm₀, hL'eq⟩ := id hL'S
  have hL'M : L' ≤ D.M := by
    rw [hL'eq]
    rintro _ ⟨y, hy, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem hm₀ (hLM hy)) (D.M.inv_mem hm₀)
  have hperf : ⁅L', L'⁆ = L' := by
    rw [hL'eq, ← Subgroup.map_commutator, hL.2.1]
  exact ⟨L', hL'S, hne,
    fun z hz => covtwoa_mem_normalizer_other hcard hL'S hne (hPM hz) (hPL hz),
    fun z hz => covtwoa_mem_normalizer_other hcard hL'S hne (hLM hz) (Subgroup.le_normalizer hz),
    covtwoa_le_normalizer hcard hL'M hperf⟩

private theorem covtwob_map_conj_self {G : Type} [Group G] {M : Subgroup G} {m : G} (hm : m ∈ M) :
    M.map (MulAut.conj m).toMonoidHom = M :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hm)

private theorem covtwob_map_conj_le {G : Type} [Group G] {M K : Subgroup G} {m : G} (hm : m ∈ M)
    (hK : K ≤ M) : K.map (MulAut.conj m).toMonoidHom ≤ M :=
  (Subgroup.map_mono hK).trans_eq (covtwob_map_conj_self hm)

private theorem covtwob_mem_map_conj {G : Type} [Group G] {K : Subgroup G} {g x : G} :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem covtwob_nonempty_bar2 {G : Type} [Group G] (L : Subgroup G) (m : G) :
    Nonempty (Bar2 L ≃* Bar2 (L.map (MulAut.conj m).toMonoidHom)) := by
  set f : L ≃* L.map (MulAut.conj m).toMonoidHom :=
    L.equivMapOfInjective _ (MulAut.conj m).injective
  exact ⟨QuotientGroup.congr _ _ f (CFSG.pCore_map_iso 2 f)⟩

private theorem covtwob_nonempty_quot {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nonempty (X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) :=
  ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

private theorem covtwob_center_card {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (Subgroup.center Y) = Nat.card (Subgroup.center X) := by
  rw [← Subgroup.map_center_eq e]
  exact Subgroup.card_map_of_injective e.injective

private theorem covtwob_isQuasisimple {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.IsQuasisimple X) : CFSG.IsQuasisimple Y :=
  CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr
    (CFSG.Open.IsQuasisimple.of_mulEquiv e.symm (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp h))

private theorem covtwob_clause2 {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : List857Clause2 X) : List857Clause2 Y := by
  obtain ⟨e'⟩ := covtwob_nonempty_quot e
  have hc := covtwob_center_card e
  have hq := covtwob_isQuasisimple e
  unfold List857Clause2 IsA6Z3 IsA7Z3 IsM22Z3 at h ⊢
  rcases h with ⟨h1, h2, ⟨h3⟩⟩ | ⟨h1, h2, ⟨h3⟩⟩ | ⟨h1, h2, ⟨h3⟩⟩
  · exact Or.inl ⟨hq h1, hc.trans h2, ⟨e'.symm.trans h3⟩⟩
  · exact Or.inr (Or.inl ⟨hq h1, hc.trans h2, ⟨e'.symm.trans h3⟩⟩)
  · exact Or.inr (Or.inr ⟨hq h1, hc.trans h2, ⟨e'.symm.trans h3⟩⟩)

open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover) in
private theorem covtwob_threeCover {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {S : ∀ (Z : Type) [Group Z], Prop}
    (hS : ∀ (A B : Type) [Group A] [Group B], (A ≃* B) → S A → S B)
    (h : ThreeCover S X) : ThreeCover S Y := by
  obtain ⟨hq, hc, hS'⟩ := h
  obtain ⟨e'⟩ := covtwob_nonempty_quot e
  exact ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq, (covtwob_center_card e).trans hc,
    hS _ _ e' hS'⟩

private theorem covtwob_isSL3PiType {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSL3PiType X) : IsSL3PiType Y := by
  unfold IsSL3PiType at h ⊢
  rcases h with ⟨p, f, hp, hm⟩ | ⟨p, f, hp, hm⟩ | ⟨p, f, hp, hc⟩ | ⟨p, f, hp, hc⟩
  · exact Or.inl ⟨p, f, hp, CFSG.Blueprint.LieModel.of_mulEquiv e hm⟩
  · exact Or.inr (Or.inl ⟨p, f, hp, CFSG.Blueprint.LieModel.of_mulEquiv e hm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, covtwob_threeCover e
      (S := fun Y _ => CFSG.Blueprint.LieModel Y .PSL 3 p f)
      (fun _ _ _ _ e' => CFSG.Blueprint.LieModel.of_mulEquiv e') hc⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨p, f, hp, covtwob_threeCover e
      (S := fun Y _ => CFSG.Blueprint.LieModel Y .PSU 3 p f)
      (fun _ _ _ _ e' => CFSG.Blueprint.LieModel.of_mulEquiv e') hc⟩))

private theorem covtwob_sylow_inf {G : Type} [Group G] [Finite G] {M P L' : Subgroup G}
    (hP : IsSylowOf 3 P M) (hL'M : L' ≤ M) (hPN : P ≤ normalizer (L' : Set G)) :
    IsSylowOf 3 (P ⊓ L') L' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (hP.of_le (le_inf hP.le hPN) inf_le_left).inf_of_le_normalizer
    (le_inf hL'M Subgroup.le_normalizer) inf_le_right

private theorem covtwob_gamma {G : Type} [Group G] [Finite G] {M Q P L : Subgroup G} {m : G}
    (hm : m ∈ M) (hQ : IsSylowOf 3 Q L) (hΓ : rankThreeGamma 1 3 Q ≤ M)
    (hL'M : L.map (MulAut.conj m).toMonoidHom ≤ M)
    (hS : IsSylowOf 3 (P ⊓ L.map (MulAut.conj m).toMonoidHom) (L.map (MulAut.conj m).toMonoidHom)) :
    rankThreeGamma 1 3 (P ⊓ L.map (MulAut.conj m).toMonoidHom) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, hkx⟩ := (CFSG.GroupTheory.isSylowOf_map_conj hQ m).exists_mem_conj hS
  have hPQ : P ⊓ L.map (MulAut.conj m).toMonoidHom = Q.map (MulAut.conj (k * m)).toMonoidHom := by
    ext x
    rw [hkx x, covtwob_mem_map_conj, covtwob_mem_map_conj]
    rw [show (k * m)⁻¹ * x * (k * m) = m⁻¹ * (k⁻¹ * x * k) * m by group]
  calc rankThreeGamma 1 3 (P ⊓ L.map (MulAut.conj m).toMonoidHom)
      = (rankThreeGamma 1 3 Q).map (MulAut.conj (k * m)).toMonoidHom := by
        rw [hPQ]
        exact CFSG.AGLEmbedding.Norton.OrdinaryProofs.GLBCore_map_conj (k * m) Q
    _ ≤ M.map (MulAut.conj (k * m)).toMonoidHom := Subgroup.map_mono hΓ
    _ = M := covtwob_map_conj_self (M.mul_mem (hL'M hk) hm)

theorem Cex856.conj_other {G : Type} [Group G] [Finite G] {D : Data G} {L Q P L' : Subgroup G}
    (h : Cex856 D L Q P) (hL' : L' ∈ MConjSet D.M L) (hP : P ≤ normalizer (L' : Set G)) :
    Cex856 D L' (P ⊓ L') P ∧ (List857Clause2 (Bar2 L) → List857Clause2 (Bar2 L')) := by
  obtain ⟨m, hm, rfl⟩ := hL'
  have hL'M : L.map (MulAut.conj m).toMonoidHom ≤ D.M := covtwob_map_conj_le hm h.mem.1.le
  obtain ⟨e⟩ := covtwob_nonempty_bar2 L m
  have hsyl := covtwob_sylow_inf h.sylowP hL'M hP
  have hmem : L.map (MulAut.conj m).toMonoidHom ∈ calC D.M := by
    refine ⟨?_, ?_, CFSG.Open.IsQuasisimple.of_mulEquiv e.symm h.mem.2.2⟩
    · simpa only [covtwob_map_conj_self hm] using h.mem.1.map (MulAut.conj m).toMonoidHom
    · rw [← Subgroup.map_commutator, h.mem.2.1]
  refine ⟨⟨hmem, ?_, hsyl, covtwob_gamma hm h.sylowQ h.gamma hL'M hsyl, h.notStrong,
    fun hS => h.notSL3 (covtwob_isSL3PiType e.symm hS), h.sylowP, inf_le_left⟩,
    covtwob_clause2 e⟩
  rw [CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Coords.pRank_map_conj (by norm_num) m L]
  exact h.rank

private theorem covtwoc_three_subgroups_mem {G : Type} [Group G] {N H₁ H₂ H₃ : Subgroup G}
    (hn₁ : H₁ ≤ normalizer (N : Set G)) (hn₂ : H₂ ≤ normalizer (N : Set G))
    (hn₃ : H₃ ≤ normalizer (N : Set G)) (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N)
    (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) {x y z : G} (hx : x ∈ H₁) (hy : y ∈ H₂) (hz : z ∈ H₃) :
    ⁅⁅x, y⁆, z⁆ ∈ N := by
  have hconj : ∀ g ∈ normalizer (N : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have hu : ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ ∈ N := by
    rw [← commutatorElement_inv]
    exact N.inv_mem (h2 (Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (H₃.inv_mem hz) (H₁.inv_mem hx)) hy))
  have hv : ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ ∈ N := by
    rw [← commutatorElement_inv]
    exact N.inv_mem (h1 (Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (H₂.inv_mem hy) hz) (H₁.inv_mem hx)))
  have hxz := mul_mem (hn₁ hx) (hn₃ hz)
  have hxy := mul_mem (hn₁ hx) (hn₂ hy)
  have e1 : ⁅⁅x, y⁆, z⁆ = (x * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ * (x * y)⁻¹) *
      (x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ * (x * z)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e1]
  exact mul_mem (hconj _ hxy _ hv) (hconj _ hxz _ hu)

private theorem covtwoc_three_subgroups_le {G : Type} [Group G] {N H₁ H₂ H₃ : Subgroup G}
    (hn₁ : H₁ ≤ normalizer (N : Set G)) (hn₂ : H₂ ≤ normalizer (N : Set G))
    (hn₃ : H₃ ≤ normalizer (N : Set G)) (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N)
    (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  have hconj : ∀ g ∈ normalizer (N : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have key : ∀ w ∈ ⁅H₁, H₂⁆, w ∈ normalizer (N : Set G) ∧ ∀ z ∈ H₃, ⁅w, z⁆ ∈ N := by
    intro w hw
    have hw' : w ∈ Subgroup.closure {g : G | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = g} := hw
    clear hw
    induction hw' using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hw
      refine ⟨?_, fun z hz => covtwoc_three_subgroups_mem hn₁ hn₂ hn₃ h1 h2 hx hy hz⟩
      have hxN := hn₁ hx
      have hyN := hn₂ hy
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxN hyN) (inv_mem hxN)) (inv_mem hyN)
    | one => exact ⟨one_mem _, fun z _ => by simp⟩
    | mul a b _ _ iha ihb =>
      refine ⟨mul_mem iha.1 ihb.1, fun z hz => ?_⟩
      have e1 : ⁅a * b, z⁆ = (a * ⁅b, z⁆ * a⁻¹) * ⁅a, z⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem (hconj _ iha.1 _ (ihb.2 z hz)) (iha.2 z hz)
    | inv a _ iha =>
      refine ⟨inv_mem iha.1, fun z hz => ?_⟩
      have e1 : ⁅a⁻¹, z⁆ = a⁻¹ * (⁅a, z⁆)⁻¹ * a := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      have := hconj _ (inv_mem iha.1) _ (N.inv_mem (iha.2 z hz))
      simpa using this
  exact Subgroup.commutator_le.mpr fun w hw z hz => (key w hw).2 z hz

private theorem covtwoc_commutator_le_inf {G : Type} [Group G] {X Y : Subgroup G}
    (hX : X ≤ normalizer (Y : Set G)) (hY : Y ≤ normalizer (X : Set G)) : ⁅X, Y⁆ ≤ X ⊓ Y := by
  refine le_inf (Subgroup.commutator_le.mpr fun x hx y hy => ?_)
    (Subgroup.commutator_le.mpr fun x hx y hy => ?_)
  · rw [show ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) by rw [commutatorElement_def]; group]
    exact X.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hY hy) x⁻¹).mp (X.inv_mem hx))
  · rw [show ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ by rw [commutatorElement_def]]
    exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hX hx) y).mp hy) (Y.inv_mem hy)

private theorem covtwoc_subsingleton {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (h : IsPGroup 2 Y) : Subsingleton Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hns
  have : Nontrivial Y := not_subsingleton_iff_nontrivial.mp hns
  exact Group.IsPerfect.not_isNilpotent Y h.isNilpotent

private theorem covtwoc_eq_bot_of_le_pCoreOf {G : Type} [Group G] [Finite G] {L L' : Subgroup G}
    (hperf : ⁅L, L⁆ = L) (hle : L ≤ pCoreOf 2 L') : L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have : Subsingleton ↥L :=
    covtwoc_subsingleton ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L').to_le hle)
  exact Subgroup.eq_bot_of_subsingleton L

private theorem covtwoc_ne_bot {G : Type} [Group G] {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) : L ≠ ⊥ := by
  intro h
  subst h
  have : Subsingleton (Bar2 (⊥ : Subgroup G)) := (QuotientGroup.mk'_surjective _).subsingleton
  have : Subsingleton (Bar2 (⊥ : Subgroup G) ⧸ Subgroup.center (Bar2 (⊥ : Subgroup G))) :=
    (QuotientGroup.mk'_surjective _).subsingleton
  have := hq.2.toNontrivial
  exact not_subsingleton _ ‹_›

private theorem covtwoc_normal_dichotomy {G : Type} [Group G] [Finite G] {L' K : Subgroup G}
    (hperf : ⁅L', L'⁆ = L') (hq : CFSG.Open.IsQuasisimple (Bar2 L')) (hKL : K ≤ L')
    (hKn : (K.subgroupOf L').Normal) : L' ≤ K ∨ ⁅K, L'⁆ ≤ pCoreOf 2 L' := by
  have : Group.IsPerfect ↥L' := Subgroup.isPerfect_iff.mpr hperf
  have : (K.subgroupOf L').Normal := hKn
  let π : ↥L' →* Bar2 L' := QuotientGroup.mk' (CFSG.pCore 2 ↥L')
  have : ((K.subgroupOf L').map π).Normal := hKn.map π (QuotientGroup.mk'_surjective _)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
    ((K.subgroupOf L').map π) with hc | htop
  · right
    refine Subgroup.commutator_le.mpr fun k hk x hx => ?_
    have hπ : π ⟨k, hKL hk⟩ ∈ Subgroup.center (Bar2 L') :=
      hc (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk))
    have h1 : π ⁅(⟨k, hKL hk⟩ : ↥L'), ⟨x, hx⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hπ (π ⟨x, hx⟩)).symm
    refine Subgroup.mem_map.mpr ⟨⁅(⟨k, hKL hk⟩ : ↥L'), ⟨x, hx⟩⁆, ?_, ?_⟩
    · rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L')]
      exact h1
    · simp [commutatorElement_def]
  · left
    have h1 : K.subgroupOf L' ⊔ CFSG.pCore 2 ↥L' = ⊤ := by
      have h := congrArg (Subgroup.comap π) htop
      rwa [Subgroup.comap_map_eq π, show π.ker = CFSG.pCore 2 ↥L' from
        QuotientGroup.ker_mk' _, Subgroup.comap_top] at h
    let ρ : ↥L' →* ↥L' ⧸ K.subgroupOf L' := QuotientGroup.mk' (K.subgroupOf L')
    have h2 : (CFSG.pCore 2 ↥L').map ρ = ⊤ := by
      have h := Subgroup.comap_map_eq ρ (CFSG.pCore 2 ↥L')
      rw [show ρ.ker = K.subgroupOf L' from QuotientGroup.ker_mk' _, sup_comm, h1,
        ← Subgroup.comap_top ρ] at h
      exact Subgroup.comap_injective (QuotientGroup.mk'_surjective _) h
    have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥L').map ρ) := CFSG.pCore_isPGroup.map ρ
    rw [h2] at hp
    have : Subsingleton (↥L' ⧸ K.subgroupOf L') :=
      covtwoc_subsingleton (hp.of_equiv Subgroup.topEquiv)
    have hK0 : K.subgroupOf L' = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      have := Subsingleton.elim (QuotientGroup.mk x : ↥L' ⧸ K.subgroupOf L') (QuotientGroup.mk 1)
      rw [QuotientGroup.eq] at this
      simpa using this
    exact Subgroup.subgroupOf_eq_top.mp hK0

private theorem covtwoc_not_le {G : Type} [Group G] [Finite G] {M L L' : Subgroup G}
    (hL : L ∈ calC M) (hL' : L' ∈ calC M) (hne : L ≠ L')
    (hnorm : L' ≤ normalizer (L : Set G)) : ¬ L ≤ L' := by
  intro hLL
  have hnormal : (L.subgroupOf L').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLL).mpr hnorm
  rcases covtwoc_normal_dichotomy hL'.2.1 hL'.2.2 hLL hnormal with h | h
  · exact hne (le_antisymm hLL h)
  · refine covtwoc_ne_bot hL.2.2 (covtwoc_eq_bot_of_le_pCoreOf (L' := L') hL.2.1 ?_)
    calc L = ⁅L, L⁆ := hL.2.1.symm
      _ ≤ ⁅L, L'⁆ := Subgroup.commutator_mono le_rfl hLL
      _ ≤ pCoreOf 2 L' := h

private theorem covtwoc_commutator_inf_le {G : Type} [Group G] [Finite G] {M L L' : Subgroup G}
    (hL : L ∈ calC M) (hL' : L' ∈ calC M) (hne : L ≠ L')
    (hLL' : L ≤ normalizer (L' : Set G)) (hL'L : L' ≤ normalizer (L : Set G)) :
    ⁅L ⊓ L', L'⁆ ≤ pCoreOf 2 L' := by
  have hnot : ¬ L' ≤ L := covtwoc_not_le hL' hL hne.symm hLL'
  have hnormal : ((L ⊓ L').subgroupOf L').Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp (hL'L hg) x),
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) x)]
  rcases covtwoc_normal_dichotomy hL'.2.1 hL'.2.2 inf_le_right hnormal with h | h
  · exact absurd (h.trans inf_le_left) hnot
  · exact h

private theorem covtwoc_commutator_le {G : Type} [Group G] [Finite G] {M L L' Q : Subgroup G}
    (hL : L ∈ calC M) (hL' : L' ∈ calC M) (hne : L ≠ L')
    (hLL' : L ≤ normalizer (L' : Set G)) (hL'L : L' ≤ normalizer (L : Set G)) (hQL : Q ≤ L)
    (hQN : Q ≤ normalizer (L' : Set G)) : ⁅L', Q⁆ ≤ pCoreOf 2 L' := by
  have hZ := covtwoc_commutator_inf_le hL hL' hne hLL' hL'L
  have hN : L' ≤ normalizer (pCoreOf 2 L' : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L'
  have hNQ : Q ≤ normalizer (pCoreOf 2 L' : Set G) :=
    hQN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L')
  have hLQ : ⁅L', Q⁆ ≤ L ⊓ L' := by
    calc ⁅L', Q⁆ ≤ ⁅L', L⁆ := Subgroup.commutator_mono le_rfl hQL
      _ ≤ L' ⊓ L := covtwoc_commutator_le_inf hL'L hLL'
      _ = L ⊓ L' := inf_comm _ _
  have h1 : ⁅⁅L', Q⁆, L'⁆ ≤ pCoreOf 2 L' := (Subgroup.commutator_mono hLQ le_rfl).trans hZ
  have h2 : ⁅⁅Q, L'⁆, L'⁆ ≤ pCoreOf 2 L' := by rwa [Subgroup.commutator_comm Q L']
  have h3 := covtwoc_three_subgroups_le hN hN hNQ h1 h2
  rwa [hL'.2.1] at h3

theorem commute_of_ne_calC_sylow {G : Type} [Group G] [Finite G] {D : Data G}
    {L L' Q Q₁ P : Subgroup G} (hL : L ∈ calC D.M) (hL' : L' ∈ calC D.M) (hne : L ≠ L')
    (hLL' : L ≤ normalizer (L' : Set G)) (hL'L : L' ≤ normalizer (L : Set G))
    (hP3 : IsPGroup 3 P) (hQ : IsSylowOf 3 Q L) (hQ₁ : IsSylowOf 3 Q₁ L')
    (hQP : Q ≤ P) (hQ₁P : Q₁ ≤ P) (hPL : P ≤ normalizer (L : Set G))
    (hPL' : P ≤ normalizer (L' : Set G)) :
    ∀ a ∈ Q, ∀ b ∈ Q₁, a * b = b * a := by
  have _ := hPL
  intro a ha b hb
  have hba : ⁅b, a⁆ ∈ pCoreOf 2 L' :=
    covtwoc_commutator_le hL hL' hne hLL' hL'L hQ.le (hQP.trans hPL')
      (Subgroup.commutator_mem_commutator (hQ₁.le hb) ha)
  have hbaP : ⁅b, a⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem (hQ₁P hb) (hQP ha)) (P.inv_mem (hQ₁P hb)))
      (P.inv_mem (hQP ha))
  have hbot : P ⊓ pCoreOf 2 L' = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 L') hP3
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L')).eq_bot
  have h1 : ⁅b, a⁆ ∈ (⊥ : Subgroup G) := hbot ▸ (Subgroup.mem_inf.mpr ⟨hbaP, hba⟩)
  exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)).symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
