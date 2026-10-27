module

public import CFSG.Milestones.ASVolI.F4Native
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

section Generic

theorem burnsideF45_quotEquiv {S Q : Type*} [Group S] [Group Q] (ι : S →* Q)
    {S₁ : Subgroup S} {Q₁ : Subgroup Q} (h : S₁ = Q₁.comap ι)
    (hcov : ∀ q : Q, ∃ s : S, (ι s)⁻¹ * q ∈ Q₁) :
    ∃ e : S ⧸ S₁ ≃ Q ⧸ Q₁, ∀ s : S, e (s : S ⧸ S₁) = ((ι s : Q) : Q ⧸ Q₁) := by
  subst h
  have hm : ∀ a b : S, a⁻¹ * b ∈ Q₁.comap ι ↔ (ι a)⁻¹ * ι b ∈ Q₁ := fun a b => by
    rw [Subgroup.mem_comap, map_mul, map_inv]
  refine ⟨Equiv.ofBijective (Quotient.map' ι (fun a b hab => ?_)) ⟨?_, ?_⟩, fun s => rfl⟩
  · rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact (hm a b).1 hab
  · intro x y
    induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
        intro hab
        have hab' : ((ι a : Q) : Q ⧸ Q₁) = ((ι b : Q) : Q ⧸ Q₁) := hab
        rw [QuotientGroup.eq] at hab'
        exact QuotientGroup.eq.2 ((hm a b).2 hab')
  · intro y
    induction y using QuotientGroup.induction_on with
    | H q =>
      obtain ⟨s, hs⟩ := hcov q
      exact ⟨(s : S ⧸ Q₁.comap ι), QuotientGroup.eq.2 hs⟩

theorem burnsideF45_cosetGeom_equiv {A B : Type} [Group A] [Group B]
    {G₀ G₁ G₂ : Subgroup A} {H₀ H₁ H₂ : Subgroup B} (ι : ↥G₀ →* ↥H₀)
    (h1 : G₁.subgroupOf G₀ = (H₁.subgroupOf H₀).comap ι)
    (h2 : G₂.subgroupOf G₀ = (H₂.subgroupOf H₀).comap ι)
    (hcov : ∀ q : ↥H₀, ∃ s : ↥G₀, ∃ b ∈ H₁.subgroupOf H₀ ⊓ H₂.subgroupOf H₀, q = ι s * b) :
    ∃ φ : CosetGeom G₀ G₁ G₂ ≃ CosetGeom H₀ H₁ H₂,
      (∀ a b, (CosetGeom.graph H₀ H₁ H₂).Adj (φ a) (φ b) ↔
        (CosetGeom.graph G₀ G₁ G₂).Adj a b) ∧
      ∀ g : ↥G₀, φ (vtx1 g) = vtx1 (ι g) ∧ φ (vtx2 g) = vtx2 (ι g) := by
  have hc1 : ∀ q : ↥H₀, ∃ s : ↥G₀, (ι s)⁻¹ * q ∈ H₁.subgroupOf H₀ := fun q => by
    obtain ⟨s, b, hb, rfl⟩ := hcov q
    exact ⟨s, by simpa using hb.1⟩
  have hc2 : ∀ q : ↥H₀, ∃ s : ↥G₀, (ι s)⁻¹ * q ∈ H₂.subgroupOf H₀ := fun q => by
    obtain ⟨s, b, hb, rfl⟩ := hcov q
    exact ⟨s, by simpa using hb.2⟩
  obtain ⟨e1, he1⟩ := burnsideF45_quotEquiv ι h1 hc1
  obtain ⟨e2, he2⟩ := burnsideF45_quotEquiv ι h2 hc2
  have step : ∀ (x : ↥G₀ ⧸ G₁.subgroupOf G₀) (y : ↥G₀ ⧸ G₂.subgroupOf G₀),
      (∃ g' : ↥H₀, (g' : ↥H₀ ⧸ H₁.subgroupOf H₀) = e1 x ∧
          (g' : ↥H₀ ⧸ H₂.subgroupOf H₀) = e2 y) ↔
        ∃ g : ↥G₀, (g : ↥G₀ ⧸ G₁.subgroupOf G₀) = x ∧ (g : ↥G₀ ⧸ G₂.subgroupOf G₀) = y := by
    intro x y
    constructor
    · rintro ⟨g', hg1, hg2⟩
      obtain ⟨s, b, hb, rfl⟩ := hcov g'
      have e0 : (ι s * b)⁻¹ * ι s = b⁻¹ := by group
      have k1 : ((ι s * b : ↥H₀) : ↥H₀ ⧸ H₁.subgroupOf H₀) =
          ((ι s : ↥H₀) : ↥H₀ ⧸ H₁.subgroupOf H₀) :=
        QuotientGroup.eq.2 (by rw [e0]; exact (H₁.subgroupOf H₀).inv_mem hb.1)
      have k2 : ((ι s * b : ↥H₀) : ↥H₀ ⧸ H₂.subgroupOf H₀) =
          ((ι s : ↥H₀) : ↥H₀ ⧸ H₂.subgroupOf H₀) :=
        QuotientGroup.eq.2 (by rw [e0]; exact (H₂.subgroupOf H₀).inv_mem hb.2)
      refine ⟨s, e1.injective ?_, e2.injective ?_⟩
      · rw [he1, ← k1, hg1]
      · rw [he2, ← k2, hg2]
    · rintro ⟨g, hg1, hg2⟩
      exact ⟨ι g, by rw [← hg1, he1], by rw [← hg2, he2]⟩
  refine ⟨Equiv.sumCongr e1 e2, ?_, fun g => ⟨?_, ?_⟩⟩
  · intro a b
    rcases a with x | y <;> rcases b with x' | y'
    · exact iff_of_false CosetGeom.not_adj_inl_inl CosetGeom.not_adj_inl_inl
    · show (CosetGeom.graph H₀ H₁ H₂).Adj (Sum.inl (e1 x)) (Sum.inr (e2 y')) ↔
        (CosetGeom.graph G₀ G₁ G₂).Adj (Sum.inl x) (Sum.inr y')
      rw [CosetGeom.adj_inl_inr, CosetGeom.adj_inl_inr]
      exact step x y'
    · show (CosetGeom.graph H₀ H₁ H₂).Adj (Sum.inr (e2 y)) (Sum.inl (e1 x')) ↔
        (CosetGeom.graph G₀ G₁ G₂).Adj (Sum.inr y) (Sum.inl x')
      rw [CosetGeom.adj_inr_inl, CosetGeom.adj_inr_inl]
      exact step x' y
    · exact iff_of_false CosetGeom.not_adj_inr_inr CosetGeom.not_adj_inr_inr
  · show Sum.inl (e1 (g : ↥G₀ ⧸ G₁.subgroupOf G₀)) =
      Sum.inl ((ι g : ↥H₀) : ↥H₀ ⧸ H₁.subgroupOf H₀)
    rw [he1]
  · show Sum.inr (e2 (g : ↥G₀ ⧸ G₂.subgroupOf G₀)) =
      Sum.inr ((ι g : ↥H₀) : ↥H₀ ⧸ H₂.subgroupOf H₀)
    rw [he2]

theorem burnsideF45_cover_of_index_two {G : Type*} [Group G] {R B : Subgroup G}
    (hR : R.index = 2) (hB : ¬ B ≤ R) (q : G) : ∃ r ∈ R, ∃ b ∈ B, q = r * b := by
  by_cases hq : q ∈ R
  · exact ⟨q, hq, 1, B.one_mem, (mul_one q).symm⟩
  · obtain ⟨b, hbB, hbR⟩ := SetLike.not_le_iff_exists.1 hB
    refine ⟨q * b⁻¹, ?_, b, hbB, by group⟩
    rw [Subgroup.mul_mem_iff_of_index_two hR]
    exact iff_of_false hq (fun h => hbR (by simpa using R.inv_mem h))

theorem burnsideF45_center_quotient_eq_bot {G : Type*} [Group G]
    (h : Subgroup.center G = ⊥) : Subgroup.center (G ⧸ Subgroup.center G) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  induction z using QuotientGroup.induction_on with
  | H g =>
    have hg : g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun k => by
      have hk := Subgroup.mem_center_iff.1 hz (k : G ⧸ Subgroup.center G)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, h,
        Subgroup.mem_bot] at hk
      exact inv_mul_eq_one.1 hk
    rw [h, Subgroup.mem_bot] at hg
    rw [hg, QuotientGroup.mk_one]
    exact Subgroup.one_mem _

theorem burnsideF45_isLongRootParabolic {G : Type} [Group G] {B P₁ P₂ L : Subgroup G} {z : G}
    (hlie : IsLieParabolics 2 ⊤ B P₁ P₂) (hcenter : Subgroup.center G = ⊥)
    (hzP : z ∈ P₁) (hzL : z ∈ L) (hz1 : z ≠ 1) (hL : ∀ x ∈ L, x = 1 ∨ x = z)
    (hN : P₁ ≤ Subgroup.normalizer (L : Set G)) : IsLongRootParabolic 2 ⊤ P₁ := by
  have hzz : z * z = 1 := by
    rcases hL (z * z) (L.mul_mem hzL hzL) with h | h
    · exact h
    · exact absurd (mul_eq_left.1 h) hz1
  have hcomm : ∀ y ∈ P₁, y * z = z * y := by
    intro y hy
    have hconj : y * z * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hN hy) z).1 hzL
    rcases hL _ hconj with h | h
    · rw [mul_inv_eq_one, mul_eq_left] at h
      exact absurd h hz1
    · calc y * z = y * z * y⁻¹ * y := by group
        _ = z * y := by rw [h]
  have hmax := (hlie.2.2.2 P₁).2 (Or.inl rfl)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : oPPrime 2 P₁ ≤ P₁ := (Subgroup.closure_le _).2 fun x hx => hx.1
  refine ⟨z, Subgroup.subset_closure ⟨hzP, 1, ?_⟩, hz1, fun y hy => hcomm y (hle hy), ?_⟩
  · rw [pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  · intro g _ hg
    by_contra hgP
    have hPC : P₁ ≤ Subgroup.centralizer ({z} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (hcomm y hy)
    have hgC : g ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hg
    have hlt : P₁ < Subgroup.centralizer ({z} : Set G) :=
      lt_of_le_of_ne hPC (fun h => hgP (by rw [h]; exact hgC))
    have htop := hmax.2.2.2 _ hlt le_top
    apply hz1
    have hzc : z ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun k => by
      have hk : k ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [htop]
        exact Subgroup.mem_top k
      exact Subgroup.mem_centralizer_singleton_iff.1 hk
    rw [hcenter, Subgroup.mem_bot] at hzc
    exact hzc

theorem burnsideF45_clause2_of_embedding {E Gs : Type} [Group E] [Group Gs] {M₁ M₂ : Subgroup E}
    (j : E →* Gs) (hidx : j.range.index = 2) {B₀ P₁ P₂ : Subgroup Gs}
    (hlie : IsLieParabolics 2 ⊤ B₀ P₁ P₂) (hgen : M₁ ⊔ M₂ = ⊤)
    (h1 : ∀ e, e ∈ M₁ ↔ j e ∈ P₁) (h2 : ∀ e, e ∈ M₂ ↔ j e ∈ P₂) (hB : ¬ B₀ ≤ j.range) :
    M₁.map j = j.range ⊓ P₁ ∧ M₂.map j = j.range ⊓ P₂ ∧
      (M₁.map j).relIndex P₁ = 2 ∧ (M₂.map j).relIndex P₂ = 2 ∧
      ∃ φ : CosetGeom (M₁ ⊔ M₂) M₁ M₂ ≃ CosetGeom (⊤ : Subgroup Gs) P₁ P₂,
        (∀ a b, (CosetGeom.graph (⊤ : Subgroup Gs) P₁ P₂).Adj (φ a) (φ b) ↔
          (CosetGeom.graph (M₁ ⊔ M₂) M₁ M₂).Adj a b) ∧
        ∀ g : ↥(M₁ ⊔ M₂),
          φ (vtx1 g) = vtx1 ⟨j g, Subgroup.mem_top _⟩ ∧
            φ (vtx2 g) = vtx2 ⟨j g, Subgroup.mem_top _⟩ := by
  have e1 : M₁ = P₁.comap j := by
    ext e
    exact h1 e
  have e2 : M₂ = P₂.comap j := by
    ext e
    exact h2 e
  have hBP : P₁ ⊓ P₂ = B₀ := hlie.2.2.1
  have hB1 : B₀ ≤ P₁ := hBP ▸ inf_le_left
  have hB2 : B₀ ≤ P₂ := hBP ▸ inf_le_right
  have hm1 : M₁.map j = j.range ⊓ P₁ := by rw [e1, Subgroup.map_comap_eq]
  have hm2 : M₂.map j = j.range ⊓ P₂ := by rw [e2, Subgroup.map_comap_eq]
  refine ⟨hm1, hm2, ?_, ?_, ?_⟩
  · rw [hm1, Subgroup.inf_relIndex_right]
    exact burnsideF4h_g2_relIndex_eq_two hidx (fun h => hB (hB1.trans h))
  · rw [hm2, Subgroup.inf_relIndex_right]
    exact burnsideF4h_g2_relIndex_eq_two hidx (fun h => hB (hB2.trans h))
  · let ι : ↥(M₁ ⊔ M₂) →* ↥(⊤ : Subgroup Gs) :=
      MonoidHom.codRestrict (j.comp (M₁ ⊔ M₂).subtype) (⊤ : Subgroup Gs)
        (fun _ => Subgroup.mem_top _)
    have k1 : M₁.subgroupOf (M₁ ⊔ M₂) = (P₁.subgroupOf ⊤).comap ι := by
      ext g
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact h1 g
    have k2 : M₂.subgroupOf (M₁ ⊔ M₂) = (P₂.subgroupOf ⊤).comap ι := by
      ext g
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact h2 g
    have hcov : ∀ q : ↥(⊤ : Subgroup Gs), ∃ s : ↥(M₁ ⊔ M₂),
        ∃ b ∈ P₁.subgroupOf ⊤ ⊓ P₂.subgroupOf ⊤, q = ι s * b := by
      intro q
      obtain ⟨r, hr, b, hb, hq⟩ := burnsideF45_cover_of_index_two hidx hB (q : Gs)
      obtain ⟨e, rfl⟩ := MonoidHom.mem_range.1 hr
      have he : e ∈ M₁ ⊔ M₂ := by
        rw [hgen]
        exact Subgroup.mem_top e
      refine ⟨⟨e, he⟩, ⟨b, Subgroup.mem_top b⟩,
        ⟨Subgroup.mem_subgroupOf.2 (hB1 hb), Subgroup.mem_subgroupOf.2 (hB2 hb)⟩, ?_⟩
      exact Subtype.ext hq
    obtain ⟨φ, hadj, hv⟩ := burnsideF45_cosetGeom_equiv ι k1 k2 hcov
    exact ⟨φ, hadj, hv⟩

end Generic

section G2dRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley


theorem burnsideF45_g2_isLongRootParabolic (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    IsLongRootParabolic 2 ⊤ (G2Native.fullLocal K (G2Native.pointParabolic K)) := by
  have hlie := (burnsideF4h_g2_full K 2 1 Nat.prime_two le_rfl (by rw [hK, pow_one])).1
  have hP : Subgroup.center (G2Native.Parent K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hinj : Function.Injective
      (QuotientGroup.mk' (Subgroup.center (G2Native.Parent K))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hP]
  have hLeq : G2Native.longRoot K =
      (rootSubgroup Tag.G2 K ![2, 3]).subgroupOf (adjointGroup Tag.G2 K) := by
    unfold G2Native.longRoot G2Native.highestLong
    exact burnsideF4h_g2_rootSubgroup_eq burnsideF4h_g2_cRoot_isRoot
  obtain ⟨x₁, hx₁⟩ : ∃ x : G2Native.Parent K, (x : ModGL Tag.G2 K) = pinnedX Tag.G2 K ![2, 3] 1 :=
    ⟨⟨_, pinnedX_mem_adjointGroup _ _⟩, rfl⟩
  have hx₁L : x₁ ∈ G2Native.longRoot K := by
    rw [hLeq, Subgroup.mem_subgroupOf, hx₁]
    exact mem_rootSubgroup.2 ⟨1, rfl⟩
  have hLB : G2Native.longRoot K ≤ G2Native.positiveBorel K := by
    unfold G2Native.longRoot G2Native.rootSubgroup G2Native.positiveBorel
    exact Subgroup.closure_mono fun x hx => Or.inr ⟨_, by decide, hx⟩
  refine burnsideF45_isLongRootParabolic hlie (burnsideF45_center_quotient_eq_bot hP)
    (z := (x₁ : G2Native.FullModel K)) (L := G2Native.fullLocal K (G2Native.longRoot K))
    ?_ ⟨x₁, hx₁L, rfl⟩ ?_ ?_ burnsideF4h_g2_fullLocal_point_le_normalizer
  · exact ⟨x₁, (le_sup_left : G2Native.positiveBorel K ≤ G2Native.pointParabolic K) (hLB hx₁L),
      rfl⟩
  · intro h
    have h' : x₁ = 1 := hinj (by rw [map_one]; exact h)
    have h'' : pinnedX Tag.G2 K ![2, 3] 1 = pinnedX Tag.G2 K ![2, 3] 0 :=
      hx₁.symm.trans ((congrArg Subtype.val h').trans (pinnedX_zero Tag.G2 K ![2, 3]).symm)
    exact one_ne_zero (pinnedX_injective Tag.G2 K _ h'')
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ (rootSubgroup Tag.G2 K ![2, 3]).subgroupOf (adjointGroup Tag.G2 K) :=
      hLeq ▸ hx
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 (Subgroup.mem_subgroupOf.1 hx')
    rcases CFSG.Quasithin.eq_zero_or_eq_one_of_card_two hK c with rfl | rfl
    · left
      have hx1 : x = 1 := Subtype.ext (hc.symm.trans (pinnedX_zero Tag.G2 K ![2, 3]))
      rw [hx1, map_one]
    · right
      have hx1 : x = x₁ := Subtype.ext (hc.symm.trans hx₁.symm)
      rw [hx1]
      rfl

end G2dRoot

section G2d

open CFSG.Blueprint CFSG.Blueprint.Chevalley


theorem burnsideF45_clause2_G2d {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2d p f Gp M₁ M₂) (hGp : Gp = ⊤) :
    ∃ (Gs : Type) (_ : Group Gs) (j : E →* Gs), Function.Injective j ∧ j.range.index = 2 ∧
      IsGenLie Gs .G2 2 1 ∧
      ∃ B₀ P₁ P₂ : Subgroup Gs, IsLieParabolics 2 ⊤ B₀ P₁ P₂ ∧ IsLongRootParabolic 2 ⊤ P₁ ∧
        M₁.map j = j.range ⊓ P₁ ∧ M₂.map j = j.range ⊓ P₂ ∧
        (M₁.map j).relIndex P₁ = 2 ∧ (M₂.map j).relIndex P₂ = 2 ∧
        ∃ φ : CosetGeom (M₁ ⊔ M₂) M₁ M₂ ≃ CosetGeom (⊤ : Subgroup Gs) P₁ P₂,
          (∀ a b, (CosetGeom.graph (⊤ : Subgroup Gs) P₁ P₂).Adj (φ a) (φ b) ↔
            (CosetGeom.graph (M₁ ⊔ M₂) M₁ M₂).Adj a b) ∧
          ∀ g : ↥(M₁ ⊔ M₂),
            φ (vtx1 g) = vtx1 ⟨j g, Subgroup.mem_top _⟩ ∧
              φ (vtx2 g) = vtx2 ⟨j g, Subgroup.mem_top _⟩ := by
  subst hGp
  obtain ⟨chart, -, hpts, hlines⟩ := hyp.toHypF_4_4g.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, -, -, K, fK, finK, card, marking, -, h2, h3, -, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K', fK', finK', charK', scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · exact absurd hk (by decide)
  · letI := fK
    haveI := finK
    let π : E ≃* G2Native.SmallModel K := Subgroup.topEquiv.symm.trans marking.symm
    have hπ : ∀ (L : Subgroup (G2Native.Parent K)) (M : Subgroup E),
        ⊤ ⊓ M = (G2Native.smallImage K marking L).map (⊤ : Subgroup E).subtype →
        ∀ e : E, e ∈ M ↔ π e ∈ G2Native.smallLocal K L := by
      intro L M hM e
      have h0 : e ∈ M ↔ e ∈ (⊤ : Subgroup E) ⊓ M := by simp
      rw [h0, hM]
      unfold G2Native.smallImage
      constructor
      · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
        have hs' : π ((marking s : ↥(⊤ : Subgroup E)) : E) = s := by
          show marking.symm (Subgroup.topEquiv.symm _) = s
          rw [MulEquiv.symm_apply_eq]
          rfl
        rw [show (⊤ : Subgroup E).subtype (marking.toMonoidHom s) =
          ((marking s : ↥(⊤ : Subgroup E)) : E) from rfl, hs']
        exact hs
      · intro h
        refine ⟨marking (π e), ⟨π e, h, rfl⟩, ?_⟩
        show ((marking (marking.symm (Subgroup.topEquiv.symm e)) : ↥(⊤ : Subgroup E)) : E) = e
        rw [MulEquiv.apply_symm_apply]
        rfl
    let j : E →* G2Native.FullModel K := (burnsideF4h_g2_incl K card).comp π.toMonoidHom
    have hm1 : ∀ e, e ∈ M₁ ↔ j e ∈ G2Native.fullLocal K (G2Native.pointParabolic K) := fun e =>
      (hπ _ M₁ (hpts.trans h2) e).trans (burnsideF4h_g2_incl_mem card _ (π e)).symm
    have hm2 : ∀ e, e ∈ M₂ ↔ j e ∈ G2Native.fullLocal K (G2Native.lineParabolic K) := fun e =>
      (hπ _ M₂ (hlines.trans h3) e).trans (burnsideF4h_g2_incl_mem card _ (π e)).symm
    have hrange : j.range = (burnsideF4h_g2_incl K card).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 π.surjective, ← MonoidHom.range_eq_map]
    have hidx : j.range.index = 2 := by
      rw [hrange]
      exact burnsideF4h_g2_incl_index card
    have hfull := burnsideF4h_g2_full K 2 1 Nat.prime_two le_rfl (by rw [card, pow_one])
    refine ⟨G2Native.FullModel K, inferInstance, j,
      (burnsideF4h_g2_incl_injective card).comp π.injective, hidx, ?_,
      G2Native.fullLocal K (G2Native.positiveBorel K),
      G2Native.fullLocal K (G2Native.pointParabolic K),
      G2Native.fullLocal K (G2Native.lineParabolic K), hfull.1,
      burnsideF45_g2_isLongRootParabolic K card,
      burnsideF45_clause2_of_embedding j hidx hfull.1 hyp.gen hm1 hm2 ?_⟩
    · show Nat.Prime 2 ∧ 1 ≤ 1 ∧ UntwistedChevalleyModel (G2Native.FullModel K) Tag.G2 (2 ^ 1)
      exact ⟨Nat.prime_two, le_rfl, K, fK, finK, by rw [card, pow_one], ⟨MulEquiv.refl _⟩⟩
    · rw [hrange]
      exact burnsideF4h_g2_borel_not_le_range card
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

end G2d

section TitsRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots


theorem burnsideF45_tits_isLongRootParabolic (K : Type) [Field K] [Finite K] [CharP K 2]
    (scope : ReeScope K 0) :
    IsLongRootParabolic 2 ⊤ (NativeFrame.ree K 0).pointParabolic := by
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
  have hK : Nat.card K = 2 := by simpa [ReeScope] using scope
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := scope
  have hloc := burnsideF4h_reeOrderedLocals_core K 0 scope
  have hZ := burnsideF4h_ree_center_trivial hK'
  have hinj : Function.Injective
      (QuotientGroup.mk' (Subgroup.center ↥(reeGroup K 0))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  obtain ⟨x₁, hx₁⟩ : ∃ x : ↥(reeGroup K 0), (x : ModGL Tag.F4 K) =
      CFSG.LieType.Chevalley.f4x K 44 1 * CFSG.LieType.Chevalley.f4x K 47 1 :=
    ⟨⟨_, burnsideF4h_tits_f4x_mem_reeGroup hK⟩, rfl⟩
  refine burnsideF45_isLongRootParabolic hloc.1 (burnsideF45_center_quotient_eq_bot hZ)
    (z := (x₁ : ↥(reeGroup K 0) ⧸ Subgroup.center ↥(reeGroup K 0)))
    (L := (NativeFrame.ree K 0).longRoot) ?_ ?_ ?_ ?_ hloc.2.2.2
  · refine ⟨x₁, ?_, rfl⟩
    show ((x₁ : ↥(reeGroup K 0)) : ModGL Tag.F4 K) ∈ reeParabolic K 0 1
    rw [hx₁]
    exact (le_sup_left : reeBorel K 0 ≤ reeParabolic K 0 1) (burnsideF4h_tits_f4x_mem_reeBorel hK)
  · refine ⟨x₁, ?_, rfl⟩
    show ((x₁ : ↥(reeGroup K 0)) : ModGL Tag.F4 K) ∈ reeLongRoot K 0
    rw [hx₁]
    exact burnsideF4h_tits_f4x_mem_reeLongRoot hK
  · intro h
    apply (burnsideF4h_tits_f4x_inv hK).1
    have h' : x₁ = 1 := hinj (by rw [map_one]; exact h)
    rw [← hx₁, h', OneMemClass.coe_one]
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : ModGL Tag.F4 K) ∈ reeLongRoot K 0 := hx
    rcases burnsideF4h_tits_reeLongRoot_bound hK hx' with h | h
    · left
      rw [show x = 1 from Subtype.ext h, map_one]
    · right
      rw [show x = x₁ from Subtype.ext (h.trans hx₁.symm)]
      rfl

end TitsRoot

section Tits

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots


theorem burnsideF45_clause2_Tits {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Tits p f Gp M₁ M₂) (hGp : Gp = ⊤) :
    ∃ (Gs : Type) (_ : Group Gs) (j : E →* Gs), Function.Injective j ∧ j.range.index = 2 ∧
      IsGenLie Gs .F4tw 2 1 ∧
      ∃ B₀ P₁ P₂ : Subgroup Gs, IsLieParabolics 2 ⊤ B₀ P₁ P₂ ∧ IsLongRootParabolic 2 ⊤ P₁ ∧
        M₁.map j = j.range ⊓ P₁ ∧ M₂.map j = j.range ⊓ P₂ ∧
        (M₁.map j).relIndex P₁ = 2 ∧ (M₂.map j).relIndex P₂ = 2 ∧
        ∃ φ : CosetGeom (M₁ ⊔ M₂) M₁ M₂ ≃ CosetGeom (⊤ : Subgroup Gs) P₁ P₂,
          (∀ a b, (CosetGeom.graph (⊤ : Subgroup Gs) P₁ P₂).Adj (φ a) (φ b) ↔
            (CosetGeom.graph (M₁ ⊔ M₂) M₁ M₂).Adj a b) ∧
          ∀ g : ↥(M₁ ⊔ M₂),
            φ (vtx1 g) = vtx1 ⟨j g, Subgroup.mem_top _⟩ ∧
              φ (vtx2 g) = vtx2 ⟨j g, Subgroup.mem_top _⟩ := by
  subst hGp
  obtain ⟨chart, -, hpts, hlines⟩ := hyp.toHypF_4_4g.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨-, -, he, marking, -, h2, h3, -, -⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · subst he
    letI := fK
    haveI := finK
    haveI := charK
    have hK : Nat.card K = 2 := by simpa [ReeScope] using scope
    obtain ⟨-, -, -, ι, hιinj, hιidx, -, hB, hP1, hP2, -, -, hBi, -, -⟩ :=
      burnsideF4h_titsParentAssembly K scope
    let π : E ≃* DerivedCentralQuotient (reeGroup K 0) :=
      Subgroup.topEquiv.symm.trans marking.symm
    have hπ : ∀ (R : Subgroup (ModGL Tag.F4 K)) (M : Subgroup E),
        ⊤ ⊓ M = ((derivedImage (reeGroup K 0) R).map marking.toMonoidHom).map
          (⊤ : Subgroup E).subtype →
        ∀ e : E, e ∈ M ↔ π e ∈ derivedImage (reeGroup K 0) R := by
      intro R M hM e
      have h0 : e ∈ M ↔ e ∈ (⊤ : Subgroup E) ⊓ M := by simp
      rw [h0, hM]
      constructor
      · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
        have hs' : π ((marking s : ↥(⊤ : Subgroup E)) : E) = s := by
          show marking.symm (Subgroup.topEquiv.symm _) = s
          rw [MulEquiv.symm_apply_eq]
          rfl
        rw [show (⊤ : Subgroup E).subtype (marking.toMonoidHom s) =
          ((marking s : ↥(⊤ : Subgroup E)) : E) from rfl, hs']
        exact hs
      · intro h
        refine ⟨marking (π e), ⟨π e, h, rfl⟩, ?_⟩
        show ((marking (marking.symm (Subgroup.topEquiv.symm e)) : ↥(⊤ : Subgroup E)) : E) = e
        rw [MulEquiv.apply_symm_apply]
        rfl
    have hι : ∀ {S' : Subgroup (DerivedCentralQuotient (reeGroup K 0))}
        {F : Subgroup (reeGroup K 0 ⧸ Subgroup.center (reeGroup K 0))},
        S'.map ι = ι.range ⊓ F → ∀ s, s ∈ S' ↔ ι s ∈ F := by
      intro S' F h s
      rw [← Subgroup.mem_map_iff_mem hιinj, h]
      exact ⟨fun h' => h'.2, fun h' => ⟨⟨s, rfl⟩, h'⟩⟩
    let j : E →* (reeGroup K 0 ⧸ Subgroup.center (reeGroup K 0)) := ι.comp π.toMonoidHom
    have hm1 : ∀ e, e ∈ M₁ ↔ j e ∈ (NativeFrame.ree K 0).pointParabolic := fun e =>
      (hπ _ M₁ (hpts.trans h2) e).trans (hι hP1 (π e))
    have hm2 : ∀ e, e ∈ M₂ ↔ j e ∈ (NativeFrame.ree K 0).lineParabolic := fun e =>
      (hπ _ M₂ (hlines.trans h3) e).trans (hι hP2 (π e))
    have hrange : j.range = ι.range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 π.surjective, ← MonoidHom.range_eq_map]
    have hidx : j.range.index = 2 := by
      rw [hrange]
      exact hιidx
    have hloc := burnsideF4h_reeOrderedLocals_core K 0 scope
    refine ⟨reeGroup K 0 ⧸ Subgroup.center (reeGroup K 0), inferInstance, j,
      hιinj.comp π.injective, hidx, ⟨rfl, odd_one, Or.inl ⟨rfl, K, fK, finK, hK,
        ⟨MulEquiv.refl _⟩⟩⟩,
      (NativeFrame.ree K 0).borel, (NativeFrame.ree K 0).pointParabolic,
      (NativeFrame.ree K 0).lineParabolic, hloc.1,
      burnsideF45_tits_isLongRootParabolic K scope,
      burnsideF45_clause2_of_embedding j hidx hloc.1 hyp.gen hm1 hm2 ?_⟩
    rw [hrange]
    intro hle
    have h1 := hBi
    rw [hB, Subgroup.inf_relIndex_right, Subgroup.relIndex_eq_one.2 hle] at h1
    exact absurd h1 (by norm_num)

end Tits

section Clause2


theorem burnsideF45_clause2 {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    ((Gp = ⊤ ∧ (κ = .G2d ∨ κ = .Tits)) →
      ∃ (Gs : Type) (_ : Group Gs) (j : E →* Gs), Function.Injective j ∧ j.range.index = 2 ∧
        IsGenLie Gs (if κ = .G2d then .G2 else .F4tw) 2 1 ∧
        ∃ B₀ P₁ P₂ : Subgroup Gs, IsLieParabolics 2 ⊤ B₀ P₁ P₂ ∧ IsLongRootParabolic 2 ⊤ P₁ ∧
          M₁.map j = j.range ⊓ P₁ ∧ M₂.map j = j.range ⊓ P₂ ∧
          (M₁.map j).relIndex P₁ = 2 ∧ (M₂.map j).relIndex P₂ = 2 ∧
          ∃ φ : CosetGeom (M₁ ⊔ M₂) M₁ M₂ ≃ CosetGeom (⊤ : Subgroup Gs) P₁ P₂,
            (∀ a b, (CosetGeom.graph (⊤ : Subgroup Gs) P₁ P₂).Adj (φ a) (φ b) ↔
              (CosetGeom.graph (M₁ ⊔ M₂) M₁ M₂).Adj a b) ∧
            ∀ g : ↥(M₁ ⊔ M₂),
              φ (vtx1 g) = vtx1 ⟨j g, Subgroup.mem_top _⟩ ∧
                φ (vtx2 g) = vtx2 ⟨j g, Subgroup.mem_top _⟩) := by
  rintro ⟨hGp, rfl | rfl⟩
  · exact burnsideF45_clause2_G2d hyp hGp
  · exact burnsideF45_clause2_Tits hyp hGp

end Clause2

end CFSG.ASVolI
