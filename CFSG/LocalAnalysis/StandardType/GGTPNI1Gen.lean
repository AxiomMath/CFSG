module

public import CFSG.LocalAnalysis.StandardType.GGTPNI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGI1OfPairLOn (P : ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    ∀ labL labJ : LargeEvenLabel, LargeEvenInLambda2 labL → LargeEvenInLambda2 labJ →
      P p labL labJ → GGHasLabel labL (L ⧸ Subgroup.center L) →
      GGHasLabel labJ (J ⧸ Subgroup.center J) → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D

private theorem tpi1g_isElemAbelian_range_of_comm {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    (hcomm : ∀ a b : X, a * b = b * a) (hexp : ∀ a : X, a ^ p = 1) (f : X →* Y) :
    IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨a, rfl⟩⟩ := u
    obtain ⟨_, ⟨b, rfl⟩⟩ := v
    apply Subtype.ext
    change f a * f b = f b * f a
    rw [← map_mul, ← map_mul, hcomm a b]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hexp a, map_one]

private theorem tpi1g_isElemAbelian_ggAutsOf {G : Type*} [Group G] {X S : Subgroup G} {p : ℕ}
    (h : S ≤ Subgroup.normalizer (X : Set G)) (hS : IsElemAbelian p S) :
    IsElemAbelian p (ggAutsOf X S h) := by
  rw [ggAutsOf]
  exact tpi1g_isElemAbelian_range_of_comm (fun a b => hS.1.is_comm.comm a b)
    (fun a => Subtype.ext (by simpa using hS.2 a a.2))
    (X.normalizerMonoidHom.comp (Subgroup.inclusion h))

theorem ggI1OfPairLOn_of_rank {P : ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (h : GGI1PairRankOn P) : GGI1OfPairLOn P := by
  intro G _ _ p B Bs x L D J hc hL labL labJ hlabL hlabJ hpair hhL hhJ
  have hI : GGThmIHyp p B x L := hc.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hpre : LargeEvenStdSubPre p B x L D J := hc.2.2.1
  have hBs : GGBstar p B Bs := hc.2.1
  have hBsElem : IsElemAbelian p Bs := hBs.2.1
  have hBsB : B ≤ Bs := hBs.1
  have hβ : p ∈ LargeEvenBeta 4 G := hI.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) →
      IsPGroup p S → IsCyclic S := hS.2.2.2.2
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  have hCBs : C ≤ Bs := inf_le_left
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) := ggInnerDiagOn_le_normalizer hL
  have hCL : C ≤ Subgroup.normalizer (L : Set G) := fun c hc => hBsN hc.1
  have hD_le_B : D ≤ B := hpre.1
  have hD_le_CJ : D ≤ Subgroup.centralizer (J : Set G) := by
    rw [hpre.2.2.2.2.2.2]; exact inf_le_right
  have hDC : D ≤ C := fun d hd => ⟨hBsB (hD_le_B hd), hD_le_CJ hd⟩
  have hJL : J ≤ L := hpre.2.2.2.2.2.1.1.trans inf_le_left
  have hzxcard : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  have hzxD : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hpre.2.2.2.1
  have hne : Subgroup.zpowers x ≠ D := by
    intro heq
    rw [heq, hpre.2.2.1] at hzxcard
    have hpp : p < p ^ 2 := by nlinarith [hp.two_le]
    exact (ne_of_gt hpp) hzxcard
  obtain ⟨y₀, hy₀D, hy₀z⟩ : ∃ y₀ ∈ D, y₀ ∉ Subgroup.zpowers x := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hne (le_antisymm hzxD fun z hz => hcon z hz)
  have hy₀B : y₀ ∈ B := hD_le_B hy₀D
  have hy₀C : y₀ ∈ C := hDC hy₀D
  have hy₀N : y₀ ∈ Subgroup.normalizer (L : Set G) := hCL hy₀C
  let ybar : MulAut ↥L := L.normalizerMonoidHom ⟨y₀, hy₀N⟩
  let E : Subgroup (MulAut ↥L) := ggAutsOf L C hCL
  have hD_cl : D = Subgroup.closure ({x, y₀} : Set G) :=
    eq_closure_pair_of_mem hI hc.2.2 hy₀D hy₀z
  have hJc_y : IsComponentOf J (L ⊓ Subgroup.centralizer ({y₀} : Set G)) := by
    have hCD : Subgroup.centralizer (D : Set G) =
        Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y₀} : Set G) := by
      rw [hD_cl, Subgroup.centralizer_closure]
      ext g
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    have hLD : L ⊓ Subgroup.centralizer (D : Set G) =
        L ⊓ Subgroup.centralizer ({y₀} : Set G) := by
      rw [hCD, ← inf_assoc, inf_eq_left.mpr hLx]
    rw [← hLD]
    exact hpre.2.2.2.2.2.1
  have hcomp : IsComponentOf (J.subgroupOf L) (ggAutFixedSubgroup ybar) :=
    isComponentOf_subgroupOf_ggAutFixed hy₀N hJL hJc_y
  have hC_elem : IsElemAbelian p C := TableB.isElemAbelian_mono hBsElem inf_le_left
  have hE_elem : IsElemAbelian p E := tpi1g_isElemAbelian_ggAutsOf hCL hC_elem
  have hy₀E : ybar ∈ E := (mem_ggAutsOf hCL).2 ⟨y₀, hy₀C, rfl⟩
  have hybar_ne : ybar ≠ 1 := by
    intro h1
    have hy₀cent : y₀ ∈ Subgroup.centralizer (L : Set G) :=
      (normalizerMonoidHom_eq_one_iff hy₀N).1 h1
    have hy₀inf : y₀ ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨hy₀B, hy₀cent⟩
    rw [inf_centralizer_eq_zpowers_of_sstar hp hS] at hy₀inf
    exact hy₀z hy₀inf
  have hEJ : ∀ e ∈ E, ∀ j ∈ J.subgroupOf L, e j = j := by
    intro e he j hj
    obtain ⟨c, hcC, hce⟩ := (mem_ggAutsOf hCL).1 he
    rw [← hce]
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe]
    have hcJ : c ∈ Subgroup.centralizer (J : Set G) := hcC.2
    have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
    have hcomm : c * (j : G) = (j : G) * c :=
      (Subgroup.mem_centralizer_iff.mp hcJ (j : G) hjJ).symm
    calc c * (j : G) * c⁻¹ = (j : G) * c * c⁻¹ := by rw [hcomm]
      _ = (j : G) := by group
  have hmark : LargeEvenMarking ↥L (fun _ _ _ I _ θ => GGInducedInn E θ I) := by
    refine largeEvenMarking_mono ?_ hL
    rintro lab R _ I F θ hθ
    have h3 : ∀ b ∈ C, ∃ φ ∈ I, LargeEvenInduces θ
        (fun l l' => (l' : G) = b⁻¹ * l * b) φ := fun b hb => hθ.2 b (hCBs hb)
    intro a ha
    obtain ⟨c, hcC, rfl⟩ := (mem_ggAutsOf hCL).1 ha
    rw [← ggLAut_eq_ggInducedAut L θ ⟨c, hCL hcC⟩]
    exact ggLAut_mem_of_induces L θ hCL h3 hcC
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL).symm hhJ
  have hE_le_zp : E ≤ Subgroup.zpowers ybar :=
    h p hp hp2 ↥L (J.subgroupOf L) ybar E labL labJ hlabL hlabJ hpair hhL hhJ'
      hybar_ne hy₀E hE_elem hcomp hEJ hmark
  have hE_le : Nat.card E ≤ p := by
    have h1 : Nat.card E ≤ Nat.card (Subgroup.zpowers ybar) := Subgroup.card_le_of_le hE_le_zp
    rw [Nat.card_zpowers, orderOf_eq_prime (hE_elem.2 ybar hy₀E) hybar_ne] at h1
    exact h1
  have hker_elem : IsElemAbelian p (C ⊓ Subgroup.centralizer (L : Set G)) :=
    TableB.isElemAbelian_mono hC_elem inf_le_left
  have hker_cyc : IsCyclic ↥(C ⊓ Subgroup.centralizer (L : Set G)) :=
    hcyc _ inf_le_right (isPGroup_of_isElemAbelian hker_elem)
  have hker_le : Nat.card ↥(C ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    TableB.card_le_of_isCyclic hp.pos hker_cyc hker_elem.2
  have hcardC : Nat.card E * Nat.card ↥(C ⊓ Subgroup.centralizer (L : Set G)) = Nat.card C :=
    card_ggAutsOf_mul_card hCL
  have hcard_le : Nat.card C ≤ Nat.card D := by
    rw [← hcardC, hpre.2.2.1]
    calc Nat.card E * Nat.card ↥(C ⊓ Subgroup.centralizer (L : Set G))
        ≤ p * p := Nat.mul_le_mul hE_le hker_le
      _ = p ^ 2 := by ring
  have hCeqD : D = C := Subgroup.eq_of_le_of_card_ge hDC hcard_le
  exact hCeqD.ge

end CFSG.StandardType

end
