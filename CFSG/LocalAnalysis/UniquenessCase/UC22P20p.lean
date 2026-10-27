module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
public import CFSG.Quasithin.Background.A3Structure314Radical
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Background.A3Structure313SL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open scoped Pointwise

section GroupTheory

theorem uc22p20p_odd_center_bar2 (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (Subgroup.center (X ⧸ CFSG.pCore 2 X))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have hev : 2 ∣ Nat.card (Subgroup.center (X ⧸ CFSG.pCore 2 X)) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.center (X ⧸ CFSG.pCore 2 X))) with h | h
    · exact even_iff_two_dvd.mp h
    · exact absurd h hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hev
  have hzY : orderOf (z : X ⧸ CFSG.pCore 2 X) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hcomm : ∀ g : X ⧸ CFSG.pCore 2 X, Commute g (z : X ⧸ CFSG.pCore 2 X) := fun g =>
    Subgroup.mem_center_iff.mp z.2 g
  have hN : (Subgroup.zpowers (z : X ⧸ CFSG.pCore 2 X)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : g * (z : X ⧸ CFSG.pCore 2 X) ^ k * g⁻¹ = (z : X ⧸ CFSG.pCore 2 X) ^ k := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Commute.zpow_right (hcomm g) k).eq
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hP : IsPGroup 2 (Subgroup.zpowers (z : X ⧸ CFSG.pCore 2 X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzY]; simp)
  have hle : Subgroup.zpowers (z : X ⧸ CFSG.pCore 2 X) ≤ CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) :=
    le_sSup ⟨hN, hP⟩
  have hbot := uc22p20c_pCore_quotient_pCore (H := X) (p := 2)
  have hz1 : (z : X ⧸ CFSG.pCore 2 X) = 1 := by
    have h := hle (Subgroup.mem_zpowers (z : X ⧸ CFSG.pCore 2 X))
    rw [hbot] at h
    exact Subgroup.mem_bot.1 h
  rw [hz1, orderOf_one] at hzY
  omega


theorem uc22p20p_sylow_sup {Y : Type} [Group Y] [Finite Y] {A₁ A₂ P₁ P₂ : Subgroup Y}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hsup : A₁ ⊔ A₂ = ⊤)
    (h₁ : CFSG.ABGLocalTools.IsSylowOf 2 P₁ A₁) (h₂ : CFSG.ABGLocalTools.IsSylowOf 2 P₂ A₂) :
    CFSG.ABGLocalTools.IsSylowOf 2 (P₁ ⊔ P₂) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₁, hQ₁⟩ := h₁.exists_sylow_eq_subgroupOf
  obtain ⟨Q₂, hQ₂⟩ := h₂.exists_sylow_eq_subgroupOf
  have hc : ∀ (a : ↥A₁) (b : ↥A₂), Commute (A₁.subtype a) (A₂.subtype b) := fun a b =>
    hcomm a a.2 b b.2
  set μ : ↥A₁ × ↥A₂ →* Y := MonoidHom.noncommCoprod A₁.subtype A₂.subtype hc with hμdef
  have hμapp : ∀ (a : ↥A₁) (b : ↥A₂), μ (a, b) = (a : Y) * (b : Y) := fun a b => by
    rw [hμdef, MonoidHom.noncommCoprod_apply]
    rfl
  have hμ : Function.Surjective μ := by
    have hrange : μ.range = ⊤ := by
      rw [hμdef, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype, hsup]
    exact MonoidHom.range_eq_top.1 hrange
  set R : Subgroup (↥A₁ × ↥A₂) := (Q₁ : Subgroup ↥A₁).prod (Q₂ : Subgroup ↥A₂) with hR
  have hR2 : IsPGroup 2 R := by
    obtain ⟨a, ha⟩ := Q₁.isPGroup'.exists_card_eq
    obtain ⟨b, hb⟩ := Q₂.isPGroup'.exists_card_eq
    refine IsPGroup.of_card (n := a + b) ?_
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, ha, hb, pow_add]
  have hRi : ¬ 2 ∣ R.index := by
    rw [hR, Subgroup.index_prod]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h1 | h1
    · exact Q₁.not_dvd_index h1
    · exact Q₂.not_dvd_index h1
  let Q : Sylow 2 (↥A₁ × ↥A₂) := hR2.toSylow hRi
  have hmap : R.map μ = P₁ ⊔ P₂ := by
    have hQ1m : ∀ a : ↥A₁, a ∈ (Q₁ : Subgroup ↥A₁) ↔ (a : Y) ∈ P₁ := fun a => by
      rw [hQ₁]
      exact Subgroup.mem_subgroupOf
    have hQ2m : ∀ b : ↥A₂, b ∈ (Q₂ : Subgroup ↥A₂) ↔ (b : Y) ∈ P₂ := fun b => by
      rw [hQ₂]
      exact Subgroup.mem_subgroupOf
    apply le_antisymm
    · rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact Subgroup.mul_mem_sup ((hQ1m a).1 ha) ((hQ2m b).1 hb)
    · refine sup_le ?_ ?_
      · intro x hx
        refine ⟨(⟨x, h₁.le hx⟩, 1), ⟨(hQ1m _).2 hx, one_mem _⟩, ?_⟩
        rw [hμapp]
        simp
      · intro x hx
        refine ⟨(1, ⟨x, h₂.le hx⟩), ⟨one_mem _, (hQ2m _).2 hx⟩, ?_⟩
        rw [hμapp]
        simp
  have hcoe : ((Q.mapSurjective hμ : Sylow 2 Y) : Subgroup Y) = P₁ ⊔ P₂ := by
    rw [Sylow.coe_mapSurjective]
    exact hmap
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hcoe]
    exact (Q.mapSurjective hμ).isPGroup'
  · rw [Subgroup.relIndex_top_right, ← hcoe]
    exact (Q.mapSurjective hμ).not_dvd_index

theorem uc22p20p_sylow_split {Y : Type} [Group Y] [Finite Y] {A₁ A₂ S : Subgroup Y}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hsup : A₁ ⊔ A₂ = ⊤)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) : S = (S ⊓ A₁) ⊔ (S ⊓ A₂) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn₁ : (⊤ : Subgroup Y) ≤ normalizer (A₁ : Set Y) := by
    rw [← hsup]
    refine sup_le Subgroup.le_normalizer (fun b hb => ?_)
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun a ha => hcomm a ha b hb)
  have hn₂ : (⊤ : Subgroup Y) ≤ normalizer (A₂ : Set Y) := by
    rw [← hsup]
    refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)
  have h1 := hS.inf_of_le_normalizer (le_top : A₁ ≤ ⊤) hn₁
  have h2 := hS.inf_of_le_normalizer (le_top : A₂ ≤ ⊤) hn₂
  have h3 := uc22p20p_sylow_sup hcomm hsup h1 h2
  exact h3.eq_of_le (sup_le inf_le_left inf_le_left) le_top hS.isPGroup

theorem uc22p20p_normalizer_sup {Y : Type} [Group Y] {A₂ P₁ P₂ : Subgroup Y} {x : Y}
    (hx : x ∈ normalizer (P₁ : Set Y)) (hc : ∀ b ∈ A₂, x * b = b * x) (hP₂ : P₂ ≤ A₂) :
    x ∈ normalizer ((P₁ ⊔ P₂ : Subgroup Y) : Set Y) :=
  Subgroup.inf_normalizer_le_normalizer_sup P₁ P₂ ⟨hx, Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun b hb => (hc b (hP₂ hb)).symm)⟩

theorem uc22p20p_sup_elemAbelian {Y : Type} [Group Y] [Finite Y] {A₁ A₂ E₁ E₂ : Subgroup Y}
    {p a b : ℕ} (hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) (h₁ : E₁ ≤ A₁) (h₂ : E₂ ≤ A₂)
    (hE₁ : IsElemAbelian p E₁) (hE₂ : IsElemAbelian p E₂) (hc₁ : Nat.card E₁ = p ^ a)
    (hc₂ : Nat.card E₂ = p ^ b) (hdisj : ∀ x ∈ A₁ ⊓ A₂, x ^ p = 1 → x = 1) :
    IsElemAbelian p (E₁ ⊔ E₂) ∧ Nat.card (E₁ ⊔ E₂ : Subgroup Y) = p ^ (a + b) := by
  have hc : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy => hcomm x (h₁ hx) y (h₂ hy)
  have hD : Disjoint E₁ E₂ := by
    rw [Subgroup.disjoint_def]
    intro x hx1 hx2
    exact hdisj x ⟨h₁ hx1, h₂ hx2⟩ (hE₁.2 x hx1)
  refine ⟨?_, ?_⟩
  · have hsup : E₁ ⊔ E₂ = Subgroup.closure ((E₁ : Set Y) ∪ (E₂ : Set Y)) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    haveI h1 : IsMulCommutative E₁ := hE₁.1
    haveI h2 : IsMulCommutative E₂ := hE₂.1
    have hpair : ((E₁ : Set Y) ∪ (E₂ : Set Y)).Pairwise Commute := by
      intro x hx y hy _
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact setLike_mul_comm hx hy
      · exact hc x hx y hy
      · exact (hc y hy x hx).symm
      · exact setLike_mul_comm hx hy
    haveI hcommE : IsMulCommutative (E₁ ⊔ E₂ : Subgroup Y) := by
      rw [hsup]
      exact Subgroup.isMulCommutative_closure hpair
    refine ⟨hcommE, fun y hy => ?_⟩
    rw [hsup] at hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with hz | hz
      · exact hE₁.2 z hz
      · exact hE₂.2 z hz
    | one => exact one_pow p
    | mul u v hu hv ihu ihv =>
      rw [← hsup] at hu hv
      rw [(show Commute u v from setLike_mul_comm hu hv).mul_pow, ihu, ihv, one_mul]
    | inv u hu ihu => rw [inv_pow, ihu, inv_one]
  · rw [uc22p20d_card_sup E₁ E₂ hc hD, hc₁, hc₂, pow_add]


theorem uc22p20p_embed_rankWit {X Y : Type} [Group X] [Group Y] {A : Subgroup Y} (e : X ≃* ↥A)
    {p k : ℕ} (hX : uc22p20oRankWit X p k) :
    ∃ E : Subgroup Y, E ≤ A ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  obtain ⟨E₀, hE₀, hc⟩ := hX
  let f : X →* Y := A.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := A.subtype_injective.comp e.injective
  refine ⟨E₀.map f, ?_, uc22p20d_isElemAbelian_map f hf hE₀, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (e y).2
  · rw [Subgroup.card_map_of_injective hf, hc]

theorem uc22p20p_embed_borelWit {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    {A P : Subgroup Y} (e : X ≃* ↥A) (hP : CFSG.ABGLocalTools.IsSylowOf 2 P A) {p k : ℕ}
    (hX : uc22p20oBorelWit X p k) :
    ∃ F : Subgroup Y, F ≤ A ∧ F ≤ normalizer (P : Set Y) ∧ IsElemAbelian p F ∧
      Nat.card F = p ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  let Q' : Sylow 2 X := Q.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hmem : ∀ z : X, z ∈ (Q' : Subgroup X) ↔ ((e z : ↥A) : Y) ∈ P := by
    intro z
    have h1 : (Q' : Subgroup X) = (Q : Subgroup ↥A).map e.symm.toMonoidHom :=
      Sylow.coe_mapSurjective _ _
    rw [h1, Subgroup.mem_map_equiv, hQ]
    exact Subgroup.mem_subgroupOf
  obtain ⟨F₀, hF₀N, hF₀, hF₀c⟩ := hX Q'
  let f : X →* Y := A.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := A.subtype_injective.comp e.injective
  refine ⟨F₀.map f, ?_, ?_, uc22p20d_isElemAbelian_map f hf hF₀, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (e y).2
  · rintro _ ⟨y, hy, rfl⟩
    have hyN := Subgroup.mem_normalizer_iff.1 (hF₀N hy)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hx : (f y : Y) ∈ A := (e y).2
    by_cases hh : h ∈ A
    · have key := hyN (e.symm ⟨h, hh⟩)
      rw [hmem, hmem] at key
      have e1 : ((e (e.symm ⟨h, hh⟩) : ↥A) : Y) = h := by simp
      have e2 : ((e (y * e.symm ⟨h, hh⟩ * y⁻¹) : ↥A) : Y) = f y * h * (f y)⁻¹ := by
        simp [f]
      rw [e1, e2] at key
      exact key
    · have h1 : h ∉ P := fun hP' => hh (hP.le hP')
      have h2 : f y * h * (f y)⁻¹ ∉ P := by
        intro hP'
        apply hh
        have hA : f y * h * (f y)⁻¹ ∈ A := hP.le hP'
        have := A.mul_mem (A.mul_mem (A.inv_mem hx) hA) hx
        simpa [mul_assoc] using this
      exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
  · rw [Subgroup.card_map_of_injective hf, hF₀c]

theorem uc22p20p_inf_mem_center {X Y : Type} [Group X] [Group Y] {A₁ A₂ : Subgroup Y} (e : X ≃* ↥A₁)
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) {x : Y} (hx : x ∈ A₁ ⊓ A₂) :
    e.symm ⟨x, hx.1⟩ ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro z
  apply e.injective
  apply Subtype.ext
  simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
  exact hcomm (e z) (e z).2 x hx.2

theorem uc22p20p_inf_trivial {X Y : Type} [Group X] [Group Y] {A₁ A₂ : Subgroup Y} (e : X ≃* ↥A₁)
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center X)) : ∀ x ∈ A₁ ⊓ A₂, x ^ p = 1 → x = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro x hx hxp
  have hxc := uc22p20p_inf_mem_center e hcomm hx
  by_contra hx1
  have hc1 : e.symm ⟨x, hx.1⟩ ≠ 1 := by
    intro h
    apply hx1
    have := congrArg (fun w => ((e w : ↥A₁) : Y)) h
    simpa using this
  have hcp : (e.symm ⟨x, hx.1⟩) ^ p = 1 := by
    apply e.injective
    apply Subtype.ext
    simp [map_pow, hxp]
  have hord : orderOf (e.symm ⟨x, hx.1⟩) = p := orderOf_eq_prime hcp hc1
  apply hZ
  have := orderOf_dvd_natCard (⟨_, hxc⟩ : Subgroup.center X)
  rwa [Subgroup.orderOf_mk, hord] at this

theorem uc22p20p_inf_eq_bot {X Y : Type} [Group X] [Group Y] {A₁ A₂ : Subgroup Y} (e : X ≃* ↥A₁)
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hZ : Subgroup.center X = ⊥) : A₁ ⊓ A₂ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxc := uc22p20p_inf_mem_center e hcomm hx
  rw [hZ, Subgroup.mem_bot] at hxc
  have := congrArg (fun w => ((e w : ↥A₁) : Y)) hxc
  simpa using this

theorem uc22p20p_prod_equiv {Y : Type} [Group Y] {A₁ A₂ : Subgroup Y}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hsup : A₁ ⊔ A₂ = ⊤) (hbot : A₁ ⊓ A₂ = ⊥) :
    Nonempty (Y ≃* ↥A₁ × ↥A₂) := by
  have hc : ∀ (a : ↥A₁) (b : ↥A₂), Commute (A₁.subtype a) (A₂.subtype b) := fun a b =>
    hcomm a a.2 b b.2
  set μ : ↥A₁ × ↥A₂ →* Y := MonoidHom.noncommCoprod A₁.subtype A₂.subtype hc with hμdef
  have hsurj : Function.Surjective μ := by
    have hrange : μ.range = ⊤ := by
      rw [hμdef, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype, hsup]
    exact MonoidHom.range_eq_top.1 hrange
  have hinj : Function.Injective μ := by
    rw [hμdef, MonoidHom.noncommCoprod_injective]
    refine ⟨A₁.subtype_injective, A₂.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.2 hbot
  exact ⟨(MulEquiv.ofBijective μ ⟨hinj, hsurj⟩).symm⟩

theorem uc22p20p_lieModel_of_center_bot {X : Type} [Group X] {t : StatedLieTag} {m p n : ℕ}
    (h : Subgroup.center X = ⊥) (hM : LieModel (X ⧸ Subgroup.center X) t m p n) :
    LieModel X t m p n :=
  CFSG.Blueprint.LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot) hM

theorem uc22p20p_isAlt_of_center_bot {X : Type} [Group X] {n : ℕ} (h : Subgroup.center X = ⊥)
    (hM : IsAlt (X ⧸ Subgroup.center X) n) : IsAlt X n := by
  obtain ⟨e⟩ := hM
  exact ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).symm.trans e⟩

end GroupTheory

section Components

variable {G : Type} [Group G] [Finite G]

theorem uc22p20p_cComp_eq_range (D : Data G) {L K : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hK : K ∈ calC L) (hLK : L = uc22p20bOrb D.T K) :
    CFSG.Quasithin.cComp L = Set.range (fun t : D.T => uc22p20bCj (t : G) K) := by
  have hLH : L ≤ L ⊔ D.T := le_sup_left
  have hTH : D.T ≤ L ⊔ D.T := le_sup_right
  have hLn : (L.subgroupOf (L ⊔ D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 (sup_le Subgroup.le_normalizer hL.1)
  have hsub : CFSG.Open.IsSubnormal L (L ⊔ D.T) := .step hLH hLn (.refl _)
  have hKc : K ∈ CFSG.Quasithin.cComp L := uc22p20e_cComp_of_calC hK
  have hKH : K ∈ CFSG.Quasithin.cComp (L ⊔ D.T) := CFSG.Quasithin.cComp_mem_of_subnormal hsub hKc
  have h := uc22p20b_cComp_orb hKH hTH
  have e : uc22p20bOrb D.T K = L := hLK.symm
  rwa [e] at h

theorem uc22p20p_mem_calC (D : Data G) {L C : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hC : C ∈ CFSG.Quasithin.cComp L) : C ∈ calC L :=
  ⟨CFSG.Quasithin.subnormal_of_mem_cComp hC, CFSG.Quasithin.perfect_of_mem_cComp hC,
    uc22p20b_isQuasisimple_bar2 (uc22p20o_oTwoE_top D hL) hC⟩

theorem uc22p20p_orb_eq_of_fixed {T K : Subgroup G} (h : ∀ t ∈ T, uc22p20bCj t K = K) :
    uc22p20bOrb T K = K :=
  le_antisymm (iSup_le fun t => (h t t.2).le) (uc22p20b_le_orb T K)

theorem uc22p20p_orbit_cases (D : Data G) (hQ : QuasisimpleDichotomy) (hB : ListBNonabelian)
    (h20_1 : S20_1_124 D) (h1930 : H1930 D) {L K : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hK : K ∈ calC L) (hLK : L = uc22p20bOrb D.T K) :
    L = K ∨ ∃ K₂ : Subgroup G, K₂ ∈ calC L ∧ K₂ ≠ K ∧ L = K ⊔ K₂ ∧
      ∃ t ∈ D.T, K₂ = uc22p20bCj t K := by
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  have hOT := uc22p20o_oTwoE_top D hL
  have hcC := uc22p20p_cComp_eq_range D hL hK hLK
  set O : Set (Subgroup G) := Set.range (fun t : D.T => uc22p20bCj (t : G) K) with hO
  obtain ⟨k, hk⟩ := uc22p20o_orbit_card D K
  have hKO : K ∈ O := ⟨⟨1, D.T.one_mem⟩, uc22p20b_cj_one K⟩
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have hk2' : 2 ≤ k := by omega
    have h4 : 4 ≤ Nat.card O := by
      rw [hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2'
    haveI : Fintype O := Fintype.ofFinite O
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := O)
      (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; exact h4)
    choose t ht using fun i => (e i).2
    refine uc22p20o_four_comps D hQ hB h20_1 h1930 hL hOT hK hLK (fun i => (t i : G))
      (fun i => (t i).2) ?_
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact (ht i).symm.trans (hij.trans (ht j))
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · left
    have h1 : O.ncard = 1 := by
      rw [← Nat.card_coe_set_eq, hk]
      norm_num
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
    have hKa : K = a := by
      have := hKO
      rw [ha] at this
      exact this
    have hfix : ∀ t ∈ D.T, uc22p20bCj t K = K := by
      intro t ht
      have h' : uc22p20bCj t K ∈ O := ⟨⟨t, ht⟩, rfl⟩
      rw [ha] at h'
      exact h'.trans hKa.symm
    rw [hLK]
    exact uc22p20p_orb_eq_of_fixed hfix
  · right
    have h2 : O.ncard = 2 := by
      rw [← Nat.card_coe_set_eq, hk]
      norm_num
    obtain ⟨x, y, hxy, hOxy⟩ := Set.ncard_eq_two.1 h2
    obtain ⟨K₂, hK₂ne, hOK⟩ : ∃ K₂ : Subgroup G, K₂ ≠ K ∧ O = {K, K₂} := by
      have hKx : K ∈ ({x, y} : Set (Subgroup G)) := hOxy ▸ hKO
      rcases hKx with rfl | hKy
      · exact ⟨y, fun h => hxy h.symm, hOxy⟩
      · rw [Set.mem_singleton_iff] at hKy
        subst hKy
        exact ⟨x, hxy, by rw [hOxy, Set.pair_comm]⟩
    have hK₂O : K₂ ∈ O := by
      rw [hOK]
      exact Or.inr rfl
    obtain ⟨⟨t, ht⟩, hKt⟩ := hK₂O
    have hK₂c : K₂ ∈ CFSG.Quasithin.cComp L := by
      rw [hcC]
      exact ⟨⟨t, ht⟩, hKt⟩
    refine ⟨K₂, uc22p20p_mem_calC D hL hK₂c, hK₂ne, ?_, t, ht, hKt.symm⟩
    apply le_antisymm
    · rw [hLK]
      refine iSup_le fun s => ?_
      have h' : uc22p20bCj (s : G) K ∈ O := ⟨s, rfl⟩
      rw [hOK] at h'
      rcases h' with h' | h'
      · rw [h']
        exact le_sup_left
      · rw [Set.mem_singleton_iff.1 h']
        exact le_sup_right
    · exact sup_le (hLK ▸ uc22p20b_le_orb D.T K) (CFSG.Quasithin.le_of_mem_cComp hK₂c)

theorem uc22p20p_two_setup (D : Data G) {L K K₂ : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hK : K ∈ calC L) (hK₂ : K₂ ∈ calC L) (hne : K₂ ≠ K) (hLK : L = K ⊔ K₂) {t : G}
    (ht : K₂ = uc22p20bCj t K) :
    ∃ A₁ A₂ : Subgroup (Bar2 L), (∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) ∧ A₁ ⊔ A₂ = ⊤ ∧
      Nonempty (Bar2 K ≃* ↥A₁) ∧ Nonempty (Bar2 K ≃* ↥A₂) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT := uc22p20o_oTwoE_top D hL
  have hKc := uc22p20e_cComp_of_calC hK
  have hK₂c := uc22p20e_cComp_of_calC hK₂
  have hKL : K ≤ L := CFSG.Quasithin.le_of_mem_cComp hKc
  have hK₂L : K₂ ≤ L := CFSG.Quasithin.le_of_mem_cComp hK₂c
  refine ⟨(K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
    (K₂.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
    uc22p20d_commute_images hOT hKc hK₂c hne.symm, ?_, ?_, ?_⟩
  · have hsup : K.subgroupOf L ⊔ K₂.subgroupOf L = ⊤ := by
      apply Subgroup.map_injective L.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKL,
        Subgroup.map_subgroupOf_eq_of_le hK₂L, ← hLK, Subgroup.map_top, Subgroup.range_subtype]
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  · obtain ⟨e, -⟩ := uc22p20d_bar2Equiv hKL (CFSG.Quasithin.subnormal_of_mem_cComp hKc)
    exact ⟨e⟩
  · obtain ⟨e, -⟩ := uc22p20d_bar2Equiv hK₂L (CFSG.Quasithin.subnormal_of_mem_cComp hK₂c)
    obtain ⟨f⟩ := uc22p20d_bar2_conj t K
    rw [← ht] at f
    exact ⟨f.trans e⟩

theorem uc22p20p_barInf_equiv {K : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    Nonempty (BarInf K ≃* Bar2 K ⧸ Subgroup.center (Bar2 K)) := by
  haveI : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  haveI hs : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := uc22p20d_pCore_solvable K
  exact CFSG.Quasithin.A314.solvableRadical_quotient_equiv hs
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hq)

theorem uc22p20p_S_on_listB (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) {L K : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hK : K ∈ calC L) (hLK : L = uc22p20bOrb D.T K) :
    Asc1930ListB (Bar2 K ⧸ Subgroup.center (Bar2 K)) := by
  obtain ⟨C, hC, hlist⟩ := uc22p20i_listB D hB h1930 hL
  rw [uc22p20p_cComp_eq_range D hL hK hLK] at hC
  obtain ⟨t, rfl⟩ := hC
  obtain ⟨e⟩ := uc22p20c_barInf_equiv_map K (t : G)
  obtain ⟨f⟩ := uc22p20p_barInf_equiv hK.2.2
  exact uc22p20i_listB_of_mulEquiv (e.symm.trans f) hlist

end Components

section TwoComponents

variable {G : Type} [Group G] [Finite G]

theorem uc22p20p_quotCenter_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nonempty ((X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y)) := by
  have h : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ Subgroup.center X := hx
      rw [Subgroup.mem_center_iff] at hx'
      show e x ∈ Subgroup.center Y
      rw [Subgroup.mem_center_iff]
      intro w
      apply e.symm.injective
      simpa using hx' (e.symm w)
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      rw [Subgroup.mem_center_iff] at hy
      show e.symm y ∈ Subgroup.center X
      rw [Subgroup.mem_center_iff]
      intro w
      apply e.injective
      simpa using hy (e w)
  exact ⟨QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e h⟩

theorem uc22p20p_isSU3_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {f : ℕ}
    (h : IsSU3 X f) : IsSU3 Y f := by
  obtain ⟨hq, hU⟩ := h
  obtain ⟨c⟩ := uc22p20p_quotCenter_equiv e
  exact ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq, CFSG.Blueprint.LieModel.of_mulEquiv c hU⟩

theorem uc22p20p_sylowBar_isSylowOf (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    CFSG.ABGLocalTools.IsSylowOf 2 (uc22p20iSylowBar D L) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  exact ⟨le_top, uc22p20i_sylowBar_isPGroup D, by
    rw [Subgroup.relIndex_top_right]
    exact uc22p20i_sylowBar_index D hL⟩

theorem uc22p20p_isSylowOf_inf_left {Y : Type} [Group Y] [Finite Y] {A₁ A₂ S : Subgroup Y}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hsup : A₁ ⊔ A₂ = ⊤)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ A₁) A₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn₁ : (⊤ : Subgroup Y) ≤ normalizer (A₁ : Set Y) := by
    rw [← hsup]
    refine sup_le Subgroup.le_normalizer (fun b hb => ?_)
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun a ha => hcomm a ha b hb)
  exact hS.inf_of_le_normalizer (le_top : A₁ ≤ ⊤) hn₁

theorem uc22p20p_normalizer_of_split {Y : Type} [Group Y] [Finite Y] {A₁ A₂ S : Subgroup Y}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hsup : A₁ ⊔ A₂ = ⊤)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {x : Y} (hx : x ∈ A₁)
    (hxN : x ∈ normalizer ((S ⊓ A₁ : Subgroup Y) : Set Y)) : x ∈ normalizer (S : Set Y) := by
  have hsplit := uc22p20p_sylow_split hcomm hsup hS
  have := uc22p20p_normalizer_sup hxN (fun b hb => hcomm x hx b hb) (inf_le_right : S ⊓ A₂ ≤ A₂)
  rwa [← hsplit] at this

theorem uc22p20p_two_E {Y : Type} [Group Y] [Finite Y] {A₁ A₂ : Subgroup Y} {X : Type} [Group X]
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (e₁ : X ≃* ↥A₁) (e₂ : X ≃* ↥A₂) {p k : ℕ}
    (hX : uc22p20oRankWit X p k) (hdisj : ∀ x ∈ A₁ ⊓ A₂, x ^ p = 1 → x = 1) :
    ∃ E : Subgroup Y, IsElemAbelian p E ∧ Nat.card E = p ^ (k + k) := by
  obtain ⟨E₁, hE₁A, hE₁, hE₁c⟩ := uc22p20p_embed_rankWit e₁ hX
  obtain ⟨E₂, hE₂A, hE₂, hE₂c⟩ := uc22p20p_embed_rankWit e₂ hX
  exact ⟨E₁ ⊔ E₂, uc22p20p_sup_elemAbelian hcomm hE₁A hE₂A hE₁ hE₂ hE₁c hE₂c hdisj⟩

theorem uc22p20p_excl_false_two (hG : Global22f) (hB : ListBNonabelian) (D : Data G)
    (h20_1 : S20_1_124 D) (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {A₁ A₂ : Subgroup (Bar2 L)} (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hsup : A₁ ⊔ A₂ = ⊤)
    {X : Type} [Group X] [Finite X] (e₁ : X ≃* ↥A₁) (hq : CFSG.Open.IsQuasisimple X)
    (hodd : Odd (Nat.card (Subgroup.center X))) {t : StatedLieTag} {m n : ℕ}
    (hex : uc22p20oExcl t m n ∨ (t = .PSU ∧ m = 5 ∧ n = 2 ∧ Subgroup.center X ≠ ⊥))
    (hM : LieModel (X ⧸ Subgroup.center X) t m 2 n) : False := by
  obtain ⟨p, hp, hp2, h⟩ := hG.excl X hq hodd t m n hex hM
  rcases h with ⟨rfl, hX⟩ | ⟨hX, hBor⟩
  · obtain ⟨E, -, hE, hEc⟩ := uc22p20p_embed_rankWit e₁ hX
    exact uc22p20o_core D hB h1930 h20_1 hL Nat.prime_three hp2 E hE hEc (Or.inl rfl)
  · obtain ⟨E, -, hE, hEc⟩ := uc22p20p_embed_rankWit e₁ hX
    have hS := uc22p20p_sylowBar_isSylowOf D hL
    obtain ⟨F, hFA, hFN, hF, hFc⟩ := uc22p20p_embed_borelWit e₁
      (uc22p20p_isSylowOf_inf_left hcomm hsup hS) hBor
    exact uc22p20o_core D hB h1930 h20_1 hL hp hp2 E hE hEc
      (Or.inr ⟨F, hF, hFc, fun x hx => uc22p20p_normalizer_of_split hcomm hsup hS (hFA hx) (hFN hx)⟩)

theorem uc22p20p_two_false (hG : Global22f) (hB : ListBNonabelian) (D : Data G)
    (h20_1 : S20_1_124 D) (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {A₁ A₂ : Subgroup (Bar2 L)} (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hsup : A₁ ⊔ A₂ = ⊤)
    {X : Type} [Group X] [Finite X] (e₁ : X ≃* ↥A₁) (e₂ : X ≃* ↥A₂)
    (hq : CFSG.Open.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X)))
    {t : StatedLieTag} {m n : ℕ} (htwo : uc22p20oTwo t m n)
    (hM : LieModel (X ⧸ Subgroup.center X) t m 2 n) (hq3 : ¬ (t = .PSU ∧ m = 3 ∧ n = 3)) :
    False := by
  obtain ⟨p, hp, hp2, hpZ, hX, hloc⟩ := hG.two X hq hodd t m n htwo hM hq3
  have hdisj := uc22p20p_inf_trivial e₁ hcomm hp hpZ
  obtain ⟨E, hE, hEc⟩ := uc22p20p_two_E hcomm e₁ e₂ hX hdisj
  have hEc' : Nat.card E = p ^ 4 := hEc
  rcases hloc with rfl | hBor
  · exact uc22p20o_core D hB h1930 h20_1 hL hp hp2 E hE hEc' (Or.inl rfl)
  · have hS := uc22p20p_sylowBar_isSylowOf D hL
    obtain ⟨F₁, hF₁A, hF₁N, hF₁, hF₁c⟩ := uc22p20p_embed_borelWit e₁
      (uc22p20p_isSylowOf_inf_left hcomm hsup hS) hBor
    have hcomm' : ∀ a ∈ A₂, ∀ b ∈ A₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
    have hsup' : A₂ ⊔ A₁ = ⊤ := by rw [sup_comm]; exact hsup
    obtain ⟨F₂, hF₂A, hF₂N, hF₂, hF₂c⟩ := uc22p20p_embed_borelWit e₂
      (uc22p20p_isSylowOf_inf_left hcomm' hsup' hS) hBor
    obtain ⟨hF, hFc⟩ := uc22p20p_sup_elemAbelian hcomm hF₁A hF₂A hF₁ hF₂ hF₁c hF₂c hdisj
    refine uc22p20o_core D hB h1930 h20_1 hL hp hp2 E hE hEc'
      (Or.inr ⟨F₁ ⊔ F₂, hF, hFc, sup_le (fun x hx => ?_) (fun x hx => ?_)⟩)
    · exact uc22p20p_normalizer_of_split hcomm hsup hS (hF₁A hx) (hF₁N hx)
    · exact uc22p20p_normalizer_of_split hcomm' hsup' hS (hF₂A hx) (hF₂N hx)

theorem uc22p20p_u38_two (hG : Global22f) (hB : ListBNonabelian) (D : Data G)
    (h20_1 : S20_1_124 D) (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {A₁ A₂ : Subgroup (Bar2 L)} (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hsup : A₁ ⊔ A₂ = ⊤)
    {X : Type} [Group X] [Finite X] (e₁ : X ≃* ↥A₁) (e₂ : X ≃* ↥A₂)
    (hq : CFSG.Open.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X)))
    (hM : IsU3 (X ⧸ Subgroup.center X) 3) : IsSU3CentralSquare (Bar2 L) := by
  obtain ⟨hdvd, hX⟩ := hG.u38 X hq hodd hM
  have hW : Nat.card (A₁ ⊓ A₂ : Subgroup (Bar2 L)) ∣ Nat.card (Subgroup.center X) := by
    set W₁ : Subgroup X := ((A₁ ⊓ A₂).subgroupOf A₁).map e₁.symm.toMonoidHom with hW₁def
    have hW₁ : W₁ ≤ Subgroup.center X := by
      rintro _ ⟨a, ha, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro z
      apply e₁.injective
      apply Subtype.ext
      simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
      exact hcomm (e₁ z) (e₁ z).2 a (Subgroup.mem_subgroupOf.1 ha).2
    have hc1 : Nat.card W₁ = Nat.card (A₁ ⊓ A₂ : Subgroup (Bar2 L)) := by
      rw [hW₁def, Subgroup.card_map_of_injective e₁.symm.injective]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [← hc1]
    exact Subgroup.card_dvd_of_le hW₁
  rcases (Nat.dvd_prime Nat.prime_three).1 (hW.trans hdvd) with h1 | h3
  · exfalso
    have hbot : A₁ ⊓ A₂ = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hdisj : ∀ x ∈ A₁ ⊓ A₂, x ^ 3 = 1 → x = 1 := fun x hx _ => by
      rw [hbot] at hx
      exact Subgroup.mem_bot.1 hx
    obtain ⟨E, hE, hEc⟩ := uc22p20p_two_E hcomm e₁ e₂ hX hdisj
    exact uc22p20o_core D hB h1930 h20_1 hL Nat.prime_three (by norm_num) E hE hEc (Or.inl rfl)
  · exact ⟨A₁, A₂, hsup, hcomm, uc22p20p_isSU3_of_mulEquiv e₁ ⟨hq, hM⟩,
      uc22p20p_isSU3_of_mulEquiv e₂ ⟨hq, hM⟩, h3⟩

theorem uc22p20p_alt_two_false (hG : Global22f) (hB : ListBNonabelian) (D : Data G)
    (h20_1 : S20_1_124 D) (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {A₁ A₂ : Subgroup (Bar2 L)} (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    {X : Type} [Group X] [Finite X] (e₁ : X ≃* ↥A₁) (e₂ : X ≃* ↥A₂)
    (hq : CFSG.Open.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X)))
    (hA : IsAlt (X ⧸ Subgroup.center X) 9) : False := by
  obtain ⟨hZ, hX⟩ := hG.a9 X hq hodd hA
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  have hdisj := uc22p20p_inf_trivial e₁ hcomm Nat.prime_three hZ3
  obtain ⟨E, hE, hEc⟩ := uc22p20p_two_E hcomm e₁ e₂ hX hdisj
  exact uc22p20o_core D hB h1930 h20_1 hL Nat.prime_three (by norm_num) E hE hEc (Or.inl rfl)

end TwoComponents

end CFSG.LocalAnalysis.UniquenessCase.UC22
