module

public import CFSG.RankThree.Asc83Table.MatGroup
public import CFSG.RankThree.PartTwo.KFacts.HeringKS12Config
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import Certificates.Certificate3084
public import Certificates.Certificate3168
public import Certificates.Certificate3169

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native

theorem isPGroup_two_closure_pair {Q : Type*} [Group Q] {a b : Q} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) :
    IsPGroup 2 (Subgroup.closure ({a, b} : Set Q)) := by
  have hSc : ∀ u ∈ ({a, b} : Set Q), ∀ v ∈ ({a, b} : Set Q), u * v = v * u := by
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · exact hab
    · exact hab.symm
    · rfl
  have hpair : ({a, b} : Set Q).Pairwise Commute := fun u hu v hv _ => hSc u hu v hv
  have hcomm : ∀ u ∈ Subgroup.closure ({a, b} : Set Q), ∀ v ∈ Subgroup.closure ({a, b} : Set Q),
      u * v = v * u := by
    intro u hu v hv
    exact congrArg Subtype.val
      ((Subgroup.isMulCommutative_closure hpair).is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hsq : ∀ w ∈ Subgroup.closure ({a, b} : Set Q), w * w = 1 := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    | one => exact one_mul 1
    | mul x y hx hy hxe hye =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hcomm y hy x hx]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hxe, hye, one_mul]
    | inv x _ hxe =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [hxe, inv_one]
  intro w
  exact ⟨1, Subtype.ext (by simpa [pow_two] using hsq w w.2)⟩

theorem hasOrd_pair' {C : MCert} {r s : ℕ} (hr : ∃ e, MFact.ord r e ∈ C.facts)
    (hs : ∃ e, MFact.ord s e ∈ C.facts) (a b : ℕ) : HasOrd C [(r, a), (s, b)] := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  exacts [hr, hs]

theorem hasOrd_single' {C : MCert} {r : ℕ} (hr : ∃ e, MFact.ord r e ∈ C.facts) (a : ℕ) :
    HasOrd C [(r, a)] := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl
  exact hr

structure KS12Facts (C : MCert) (rx ry rg rh r1 r2 : ℕ) : Prop where
  ox : MFact.ord rx 3 ∈ C.facts
  oy : MFact.ord ry 3 ∈ C.facts
  og : ∃ e, MFact.ord rg e ∈ C.facts
  oh : ∃ e, MFact.ord rh e ∈ C.facts
  o1 : MFact.ord r1 2 ∈ C.facts
  o2 : MFact.ord r2 2 ∈ C.facts
  xy : MFact.eq [(rx, 1), (ry, 1)] [(ry, 1), (rx, 1)] ∈ C.facts
  x1 : ∃ t, MFact.ne [(rx, 1)] [] t ∈ C.facts
  y1 : ∃ t, MFact.ne [(ry, 1)] [] t ∈ C.facts
  yx : ∃ t, MFact.ne [(ry, 1)] [(rx, 1)] t ∈ C.facts
  yx2 : ∃ t, MFact.ne [(ry, 1)] [(rx, 2)] t ∈ C.facts
  t1 : ∃ t, MFact.ne [(r1, 1)] [] t ∈ C.facts
  t12 : MFact.eq [(r1, 1), (r2, 1)] [(r2, 1), (r1, 1)] ∈ C.facts
  gx : MFact.conj rg [(rx, 1)] [(rx, 2), (ry, 0)] ∈ C.facts
  gy : MFact.conj rg [(ry, 1)] [(rx, 0), (ry, 1)] ∈ C.facts
  hy : MFact.conj rh [(ry, 1)] [(rx, 0), (ry, 2)] ∈ C.facts
  xt1 : ∃ a b, MFact.conj rx [(r1, 1)] [(r1, a), (r2, b)] ∈ C.facts
  xt2 : ∃ a b, MFact.conj rx [(r2, 1)] [(r1, a), (r2, b)] ∈ C.facts
  yt1 : ∃ a b, MFact.conj ry [(r1, 1)] [(r1, a), (r2, b)] ∈ C.facts
  yt2 : ∃ a b, MFact.conj ry [(r2, 1)] [(r1, a), (r2, b)] ∈ C.facts

section Config

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d) [Inhabited M]
  {sA sB : String} {C : MCert} (hC : mcertCheck O sA sB C = true)
  {rx ry rg rh r1 r2 : ℕ} (hF : KS12Facts C rx ry rg rh r1 r2)

include Sp hC hF in
theorem KS12Facts.config [NeZero p] : KS12ConfigN (certMonoid p d sA sB)ˣ := by
  have : Finite (certMonoid p d sA sB)ˣ := finite_certUnits
  have hox : ∃ e, MFact.ord rx e ∈ C.facts := ⟨3, hF.ox⟩
  have hoy : ∃ e, MFact.ord ry e ∈ C.facts := ⟨3, hF.oy⟩
  have ho1 : ∃ e, MFact.ord r1 e ∈ C.facts := ⟨2, hF.o1⟩
  have ho2 : ∃ e, MFact.ord r2 e ∈ C.facts := ⟨2, hF.o2⟩
  have hx3 : regUnit Sp hC rx ^ 3 = 1 := regUnit_pow Sp hC hF.ox
  have hy3 : regUnit Sp hC ry ^ 3 = 1 := regUnit_pow Sp hC hF.oy
  have ht1sq : regUnit Sp hC r1 ^ 2 = 1 := regUnit_pow Sp hC hF.o1
  have ht2sq : regUnit Sp hC r2 ^ 2 = 1 := regUnit_pow Sp hC hF.o2
  have hxy : Commute (regUnit Sp hC rx) (regUnit Sp hC ry) :=
    regUnit_comm' Sp hC hF.xy (hasOrd_pair' hox hoy 1 1) (hasOrd_pair' hoy hox 1 1)
  have htt : Commute (regUnit Sp hC r1) (regUnit Sp hC r2) :=
    regUnit_comm' Sp hC hF.t12 (hasOrd_pair' ho1 ho2 1 1) (hasOrd_pair' ho2 ho1 1 1)
  obtain ⟨a1, ha1⟩ := hF.x1
  obtain ⟨a2, ha2⟩ := hF.y1
  obtain ⟨a3, ha3⟩ := hF.yx
  obtain ⟨a4, ha4⟩ := hF.yx2
  obtain ⟨a5, ha5⟩ := hF.t1
  have hx1 : regUnit Sp hC rx ≠ 1 := regUnit_ne_one' Sp hC ha1 (hasOrd_single' hox 1)
  have hy1 : regUnit Sp hC ry ≠ 1 := regUnit_ne_one' Sp hC ha2 (hasOrd_single' hoy 1)
  have hyx : regUnit Sp hC ry ≠ regUnit Sp hC rx := by
    have := regUnit_ne_pow' Sp hC ha3 (hasOrd_single' hoy 1) (hasOrd_single' hox 1)
    rwa [pow_one] at this
  have hyx2 : regUnit Sp hC ry ≠ regUnit Sp hC rx ^ 2 :=
    regUnit_ne_pow' Sp hC ha4 (hasOrd_single' hoy 1) (hasOrd_single' hox 2)
  have ht1 : regUnit Sp hC r1 ≠ 1 := regUnit_ne_one' Sp hC ha5 (hasOrd_single' ho1 1)
  obtain ⟨eg, heg⟩ := hF.og
  obtain ⟨eh, heh⟩ := hF.oh
  have hgx : regUnit Sp hC rg * regUnit Sp hC rx * (regUnit Sp hC rg)⁻¹ =
      (regUnit Sp hC rx)⁻¹ := by
    have := regUnit_conj' Sp hC hF.gx heg (hasOrd_single' hox 1) (hasOrd_pair' hox hoy 2 0)
    rw [this, pow_zero, mul_one]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hx3])
  have hgy : regUnit Sp hC rg * regUnit Sp hC ry * (regUnit Sp hC rg)⁻¹ = regUnit Sp hC ry := by
    have := regUnit_conj' Sp hC hF.gy heg (hasOrd_single' hoy 1) (hasOrd_pair' hox hoy 0 1)
    rw [this, pow_zero, one_mul, pow_one]
  have hhy : regUnit Sp hC rh * regUnit Sp hC ry * (regUnit Sp hC rh)⁻¹ =
      (regUnit Sp hC ry)⁻¹ := by
    have := regUnit_conj' Sp hC hF.hy heh (hasOrd_single' hoy 1) (hasOrd_pair' hox hoy 0 2)
    rw [this, pow_zero, one_mul]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hy3])
  set t₁ := regUnit Sp hC r1 with ht₁
  set t₂ := regUnit Sp hC r2 with ht₂
  have hmem : ∀ a b : ℕ, t₁ ^ a * t₂ ^ b ∈ Subgroup.closure ({t₁, t₂} : Set _) := fun a b =>
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _)
  have hnormX : regUnit Sp hC rx ∈ Subgroup.normalizer
      (Subgroup.closure ({t₁, t₂} : Set (certMonoid p d sA sB)ˣ) : Set _) := by
    apply mem_normalizer_closure_of_conj_mem
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · obtain ⟨a, b, hab⟩ := hF.xt1
      have := regUnit_conj' Sp hC hab hF.ox (hasOrd_single' ho1 1) (hasOrd_pair' ho1 ho2 a b)
      rw [this]
      exact hmem a b
    · obtain ⟨a, b, hab⟩ := hF.xt2
      have := regUnit_conj' Sp hC hab hF.ox (hasOrd_single' ho2 1) (hasOrd_pair' ho1 ho2 a b)
      rw [this]
      exact hmem a b
  have hnormY : regUnit Sp hC ry ∈ Subgroup.normalizer
      (Subgroup.closure ({t₁, t₂} : Set (certMonoid p d sA sB)ˣ) : Set _) := by
    apply mem_normalizer_closure_of_conj_mem
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · obtain ⟨a, b, hab⟩ := hF.yt1
      have := regUnit_conj' Sp hC hab hF.oy (hasOrd_single' ho1 1) (hasOrd_pair' ho1 ho2 a b)
      rw [this]
      exact hmem a b
    · obtain ⟨a, b, hab⟩ := hF.yt2
      have := regUnit_conj' Sp hC hab hF.oy (hasOrd_single' ho2 1) (hasOrd_pair' ho1 ho2 a b)
      rw [this]
      exact hmem a b
  have hT2 : IsPGroup 2 (Subgroup.closure ({t₁, t₂} : Set (certMonoid p d sA sB)ˣ)) :=
    isPGroup_two_closure_pair (by rw [← pow_two]; exact ht1sq) (by rw [← pow_two]; exact ht2sq)
      htt.eq
  have hT1 : Subgroup.closure ({t₁, t₂} : Set (certMonoid p d sA sB)ˣ) ≠ ⊥ := by
    intro hbot
    apply ht1
    have : t₁ ∈ Subgroup.closure ({t₁, t₂} : Set (certMonoid p d sA sB)ˣ) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    rwa [hbot, Subgroup.mem_bot] at this
  exact ⟨regUnit Sp hC rx, regUnit Sp hC ry, regUnit Sp hC rg, regUnit Sp hC rh,
    Subgroup.closure ({t₁, t₂} : Set _), hx3, hy3, hxy.eq,
    ks12_card_closure_pair hx3 hy3 hxy.eq hx1 hy1 hyx hyx2, hgx, hgy, hhy, hT2, hT1, hnormX,
    hnormY⟩

end Config

end CFSG.RankThree.PartTwo.KFacts
