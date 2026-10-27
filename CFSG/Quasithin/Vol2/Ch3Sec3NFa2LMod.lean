module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LChief
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure SecHyp (X N₀ N₁ : Subgroup G) : Prop where
  le : N₀ ≤ N₁
  norm₀ : X ≤ Subgroup.normalizer (N₀ : Set G)
  norm₁ : X ≤ Subgroup.normalizer (N₁ : Set G)
  normal : N₁ ≤ Subgroup.normalizer (N₀ : Set G)
  comm : ∀ a ∈ N₁, ∀ b ∈ N₁, a * b * a⁻¹ * b⁻¹ ∈ N₀
  sq : ∀ a ∈ N₁, a * a ∈ N₀

theorem IsChiefPair.secHyp {X N₀ N₁ : Subgroup G} (h : IsChiefPair X N₀ N₁)
    (hp : IsPGroup 2 ↥N₁) : SecHyp X N₀ N₁ :=
  ⟨h.lt.le, h.norm₀, h.norm₁, h.normal, h.comm_mem hp, h.sq_mem hp⟩

structure SecRep (X N₀ N₁ : Subgroup G) (W : Type) [AddCommGroup W] [Module (ZMod 2) W] where
  ρ : ↥X →* (W ≃ₗ[ZMod 2] W)
  cls : ↥N₁ →* Multiplicative W
  surj : Function.Surjective cls
  ker : ∀ n : ↥N₁, cls n = 1 ↔ (n : G) ∈ N₀
  act : ∀ (x : ↥X) (n m : ↥N₁), (m : G) = (x : G) * n * (x : G)⁻¹ →
    ρ x (Multiplicative.toAdd (cls n)) = Multiplicative.toAdd (cls m)

theorem exists_secRep {X N₀ N₁ : Subgroup G} (h : SecHyp X N₀ N₁) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W),
      Nonempty (SecRep X N₀ N₁ W) := by
  classical
  haveI hN : (N₀.subgroupOf N₁).Normal := ⟨fun z hz v => by
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    have h1 : (v : G) * z * (v : G)⁻¹ ∈ N₀ :=
      (Subgroup.mem_normalizer_iff.mp (h.normal v.2) z).mp hz
    simpa using h1⟩
  let _ : CommGroup (↥N₁ ⧸ N₀.subgroupOf N₁) :=
    { (QuotientGroup.Quotient.group (N₀.subgroupOf N₁)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
              Subgroup.mem_subgroupOf]
            have h1 := h.comm _ (N₁.inv_mem b.2) _ (N₁.inv_mem a.2)
            have he : (((a * b)⁻¹ * (b * a) : ↥N₁) : G) =
                (b : G)⁻¹ * (a : G)⁻¹ * (b : G) * (a : G) := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv]
              group
            rw [he]
            have he2 : (b : G)⁻¹ * (a : G)⁻¹ * (b : G) * (a : G) =
                (b : G)⁻¹ * (a : G)⁻¹ * ((b : G)⁻¹)⁻¹ * ((a : G)⁻¹)⁻¹ := by group
            rw [he2]
            exact h1 }
  have hmk : ∀ q : Additive (↥N₁ ⧸ N₀.subgroupOf N₁), ∃ v : ↥N₁,
      q = Additive.ofMul (v : ↥N₁ ⧸ N₀.subgroupOf N₁) := fun q => by
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    exact ⟨v, by rw [hv]; rfl⟩
  have h2 : ∀ q : Additive (↥N₁ ⧸ N₀.subgroupOf N₁), 2 • q = 0 := by
    intro q
    obtain ⟨v, rfl⟩ := hmk q
    rw [← ofMul_pow, ← ofMul_one, ← QuotientGroup.mk_pow]
    congr 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, pow_two]
    exact h.sq _ v.2
  let _ : Module (ZMod 2) (Additive (↥N₁ ⧸ N₀.subgroupOf N₁)) := AddCommGroup.zmodModule h2
  have hfin : Finite (Additive (↥N₁ ⧸ N₀.subgroupOf N₁)) :=
    Finite.of_surjective (fun v : ↥N₁ => Additive.ofMul (v : ↥N₁ ⧸ N₀.subgroupOf N₁)) fun q => by
      obtain ⟨v, rfl⟩ := hmk q
      exact ⟨v, rfl⟩
  refine ⟨Additive (↥N₁ ⧸ N₀.subgroupOf N₁), inferInstance, inferInstance, hfin, ?_⟩
  let cj : ↥X → (↥N₁ →* ↥N₁) := fun x =>
    { toFun := fun v => ⟨(x : G) * v * (x : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (h.norm₁ x.2) v).mp v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hcj : ∀ (x : ↥X) (v : ↥N₁), ((cj x v : ↥N₁) : G) = (x : G) * v * (x : G)⁻¹ :=
    fun x v => rfl
  let cq : ↥X → ((↥N₁ ⧸ N₀.subgroupOf N₁) →* (↥N₁ ⧸ N₀.subgroupOf N₁)) := fun x =>
    QuotientGroup.map (N₀.subgroupOf N₁) (N₀.subgroupOf N₁) (cj x) (fun z hz => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hcj]
      exact (Subgroup.mem_normalizer_iff.mp (h.norm₀ x.2) z).mp (Subgroup.mem_subgroupOf.mp hz))
  have hcq : ∀ (x : ↥X) (v : ↥N₁), cq x (v : ↥N₁ ⧸ N₀.subgroupOf N₁) =
      ((cj x v : ↥N₁) : ↥N₁ ⧸ N₀.subgroupOf N₁) := fun x v => rfl
  let act : ↥X →* (Additive (↥N₁ ⧸ N₀.subgroupOf N₁) →ₗ[ZMod 2]
      Additive (↥N₁ ⧸ N₀.subgroupOf N₁)) :=
    { toFun := fun x => (MonoidHom.toAdditive (cq x)).toZModLinearMap 2
      map_one' := by
        refine LinearMap.ext fun q => ?_
        obtain ⟨v, rfl⟩ := hmk q
        show Additive.ofMul (cq 1 (v : ↥N₁ ⧸ N₀.subgroupOf N₁)) = Additive.ofMul _
        rw [hcq]
        congr 2
        exact Subtype.ext (by rw [hcj]; simp)
      map_mul' := fun x x' => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨v, rfl⟩ := hmk q
        show Additive.ofMul (cq (x * x') (v : ↥N₁ ⧸ N₀.subgroupOf N₁)) =
          Additive.ofMul (cq x (cq x' (v : ↥N₁ ⧸ N₀.subgroupOf N₁)))
        rw [hcq, hcq, hcq]
        congr 2
        exact Subtype.ext (by rw [hcj, hcj, hcj]; simp [mul_assoc]) }
  have hact : ∀ (x : ↥X) (v : ↥N₁), act x (Additive.ofMul (v : ↥N₁ ⧸ N₀.subgroupOf N₁)) =
      Additive.ofMul ((cj x v : ↥N₁) : ↥N₁ ⧸ N₀.subgroupOf N₁) := fun x v => rfl
  let ρ : ↥X →* (Additive (↥N₁ ⧸ N₀.subgroupOf N₁) ≃ₗ[ZMod 2]
      Additive (↥N₁ ⧸ N₀.subgroupOf N₁)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (Additive (↥N₁ ⧸ N₀.subgroupOf N₁))).toMonoidHom.comp act.toHomUnits
  have hρ : ∀ (x : ↥X) (q : Additive (↥N₁ ⧸ N₀.subgroupOf N₁)), ρ x q = act x q := fun x q => rfl
  refine ⟨⟨ρ, ?_, ?_, ?_, ?_⟩⟩
  · exact
      { toFun := fun v => Multiplicative.ofAdd (Additive.ofMul (v : ↥N₁ ⧸ N₀.subgroupOf N₁))
        map_one' := rfl
        map_mul' := fun a b => rfl }
  · intro y
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul (Multiplicative.toAdd y))
    exact ⟨v, by
      show Multiplicative.ofAdd (Additive.ofMul (v : ↥N₁ ⧸ N₀.subgroupOf N₁)) = y
      rw [hv]
      rfl⟩
  · intro n
    show (n : ↥N₁ ⧸ N₀.subgroupOf N₁) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · intro x n m hm
    show ρ x (Additive.ofMul (n : ↥N₁ ⧸ N₀.subgroupOf N₁)) = Additive.ofMul (m : ↥N₁ ⧸ N₀.subgroupOf N₁)
    rw [hρ, hact]
    congr 2
    exact Subtype.ext (by rw [hcj]; exact hm.symm)

namespace SecRep

variable {X N₀ N₁ : Subgroup G} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

abbrev cl (s : SecRep X N₀ N₁ W) (n : ↥N₁) : W := Multiplicative.toAdd (s.cls n)

theorem cl_mul (s : SecRep X N₀ N₁ W) (a b : ↥N₁) : s.cl (a * b) = s.cl a + s.cl b := by
  simp [cl, map_mul]

theorem cl_inv (s : SecRep X N₀ N₁ W) (a : ↥N₁) : s.cl a⁻¹ = - s.cl a := by
  simp [cl, map_inv]

theorem cl_eq_zero_iff (s : SecRep X N₀ N₁ W) (n : ↥N₁) : s.cl n = 0 ↔ (n : G) ∈ N₀ := by
  rw [← s.ker n]
  constructor
  · intro h
    exact toAdd_eq_zero.mp h
  · intro h
    exact toAdd_eq_zero.mpr h

theorem exists_cl (s : SecRep X N₀ N₁ W) (w : W) : ∃ n : ↥N₁, s.cl n = w := by
  obtain ⟨n, hn⟩ := s.surj (Multiplicative.ofAdd w)
  exact ⟨n, by simp [cl, hn]⟩

theorem cl_eq_iff (s : SecRep X N₀ N₁ W) (n m : ↥N₁) :
    s.cl m = s.cl n ↔ ((n : G)⁻¹ * (m : G)) ∈ N₀ := by
  have : s.cl (n⁻¹ * m) = s.cl m - s.cl n := by
    rw [cl_mul, cl_inv]; abel
  rw [← sub_eq_zero, ← this, cl_eq_zero_iff]
  simp

def conjN (h : SecHyp X N₀ N₁) (x : ↥X) (n : ↥N₁) : ↥N₁ :=
  ⟨(x : G) * n * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (h.norm₁ x.2) n).mp n.2⟩

theorem ρ_cl (h : SecHyp X N₀ N₁) (s : SecRep X N₀ N₁ W) (x : ↥X) (n : ↥N₁) :
    s.ρ x (s.cl n) = s.cl (conjN h x n) := s.act x n (conjN h x n) rfl

theorem fix_iff (h : SecHyp X N₀ N₁) (s : SecRep X N₀ N₁ W) (x : ↥X) (n : ↥N₁) :
    s.ρ x (s.cl n) = s.cl n ↔ (x : G) * n * (x : G)⁻¹ * (n : G)⁻¹ ∈ N₀ := by
  rw [ρ_cl h, cl_eq_iff]
  have hn := Subgroup.mem_normalizer_iff.mp (h.normal (N₁.inv_mem n.2))
  have := hn ((x : G) * n * (x : G)⁻¹ * (n : G)⁻¹)
  rw [this]
  have e : (n : G)⁻¹ * ((x : G) * n * (x : G)⁻¹ * (n : G)⁻¹) * ((n : G)⁻¹)⁻¹ =
      (n : G)⁻¹ * (conjN h x n : G) := by
    simp only [conjN]
    group
  rw [e]

def preS (s : SecRep X N₀ N₁ W) (S : Submodule (ZMod 2) W) : Subgroup G where
  carrier := {g | ∃ n : ↥N₁, (n : G) = g ∧ s.cl n ∈ S}
  one_mem' := ⟨1, rfl, by simp [cl, S.zero_mem]⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩
    exact ⟨a * b, rfl, by rw [cl_mul]; exact S.add_mem ha hb⟩
  inv_mem' := by
    rintro _ ⟨a, rfl, ha⟩
    exact ⟨a⁻¹, rfl, by rw [cl_inv]; exact S.neg_mem ha⟩

theorem irreducible (h : IsChiefPair X N₀ N₁) (hh : SecHyp X N₀ N₁) (s : SecRep X N₀ N₁ W)
    (S : Submodule (ZMod 2) W) (hS : ∀ x : ↥X, ∀ w ∈ S, s.ρ x w ∈ S) : S = ⊥ ∨ S = ⊤ := by
  have hN₀ : N₀ ≤ preS s S := by
    intro g hg
    refine ⟨⟨g, hh.le hg⟩, rfl, ?_⟩
    rw [(cl_eq_zero_iff s ⟨g, hh.le hg⟩).mpr hg]
    exact S.zero_mem
  have hN₁ : preS s S ≤ N₁ := by
    rintro _ ⟨n, rfl, -⟩
    exact n.2
  have key : ∀ (y : ↥X), ∀ g ∈ preS s S, (y : G) * g * (y : G)⁻¹ ∈ preS s S := by
    rintro y _ ⟨n, rfl, hn⟩
    exact ⟨conjN hh y n, rfl, by rw [← ρ_cl hh]; exact hS y _ hn⟩
  have hXN : X ≤ Subgroup.normalizer (preS s S : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => key ⟨x, hx⟩ g hg, fun hg => ?_⟩
    have := key ⟨x⁻¹, X.inv_mem hx⟩ _ hg
    simpa [mul_assoc] using this
  rcases h.min (preS s S) hN₀ hN₁ hXN with e | e
  · left
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := exists_cl s w
    have hn : (n : G) ∈ preS s S := ⟨n, rfl, hw⟩
    rw [e] at hn
    rw [(cl_eq_zero_iff s n).mpr hn]
    exact zero_mem _
  · right
    rw [eq_top_iff]
    intro w _
    obtain ⟨n, rfl⟩ := exists_cl s w
    have hn : (n : G) ∈ preS s S := by rw [e]; exact n.2
    obtain ⟨m, hm, hmS⟩ := hn
    have hmn : m = n := Subtype.ext hm
    rw [hmn] at hmS
    exact hmS

theorem ρ_eq_one_of_normal_pgroup [Finite W] (h : IsChiefPair X N₀ N₁) (hh : SecHyp X N₀ N₁)
    (s : SecRep X N₀ N₁ W) {P : Subgroup G} (hPX : P ≤ X) (hP : IsPGroup 2 ↥P)
    (hPn : ∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P) :
    ∀ p : ↥X, (p : G) ∈ P → s.ρ p = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Submodule (ZMod 2) W :=
    { carrier := {w | ∀ p : ↥X, (p : G) ∈ P → s.ρ p w = w}
      add_mem' := fun {a b} ha hb p hp => by rw [map_add, ha p hp, hb p hp]
      zero_mem' := fun p hp => by simp
      smul_mem' := fun c w hw p hp => by rw [map_smul, hw p hp] }
  have hFinv : ∀ x : ↥X, ∀ w ∈ F, s.ρ x w ∈ F := by
    intro x w hw p hp
    have hp' : ((x⁻¹ * p * x : ↥X) : G) ∈ P := by
      have := hPn ((x⁻¹ : ↥X) : G) (X.inv_mem x.2) p hp
      simpa using this
    have e : p * x = x * (x⁻¹ * p * x) := by group
    calc s.ρ p (s.ρ x w) = s.ρ (p * x) w := by rw [map_mul]; rfl
      _ = s.ρ (x * (x⁻¹ * p * x)) w := by rw [e]
      _ = s.ρ x (s.ρ (x⁻¹ * p * x) w) := by rw [map_mul]; rfl
      _ = s.ρ x w := by rw [hw _ hp']
  have hFne : F ≠ ⊥ := by
    intro hF
    obtain ⟨g, hgN₁, hgN₀⟩ := SetLike.exists_of_lt h.lt
    have hW : Nontrivial W := ⟨⟨s.cl ⟨g, hgN₁⟩, 0, fun h0 => hgN₀ ((cl_eq_zero_iff s ⟨g, hgN₁⟩).mp h0)⟩⟩
    letI : MulAction ↥P W := MulAction.compHom W (s.ρ.comp (Subgroup.inclusion hPX))
    have hmod := hP.card_modEq_card_fixedPoints (α := W)
    haveI : Module.Finite (ZMod 2) W := Module.finite_iff_finite.mpr inferInstance
    have hcardW : 2 ∣ Nat.card W := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod]
      exact dvd_pow_self 2 (Module.finrank_pos (R := ZMod 2) (M := W)).ne'
    have hdvd : 2 ∣ Nat.card (MulAction.fixedPoints ↥P W) :=
      (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hcardW)))
    have h0 : ∀ w : W, w ∈ MulAction.fixedPoints ↥P W → w = 0 := by
      intro w hw
      have hwF : w ∈ F := by
        intro p hp
        exact MulAction.mem_fixedPoints.mp hw ⟨(p : G), hp⟩
      rw [hF] at hwF
      exact (Submodule.mem_bot _).mp hwF
    have hcard1 : Nat.card (MulAction.fixedPoints ↥P W) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ((h0 a.1 a.2).trans (h0 b.1 b.2).symm)⟩, ⟨⟨0, ?_⟩⟩⟩
      exact MulAction.mem_fixedPoints.mpr fun m => by
        show s.ρ (Subgroup.inclusion hPX m) 0 = 0
        simp
    rw [hcard1] at hdvd
    exact absurd (Nat.le_of_dvd one_pos hdvd) (by norm_num)
  rcases irreducible h hh s F hFinv with hF | hF
  · exact absurd hF hFne
  · intro p hp
    refine LinearEquiv.ext fun w => ?_
    have hw : w ∈ F := by rw [hF]; trivial
    exact hw p hp

private theorem relIndex_ne_zero' (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem finrank_range_le_mIdx [Finite W] (hh : SecHyp X N₀ N₁) (s : SecRep X N₀ N₁ W)
    {A Z₀ : Subgroup G} (hA : IsPGroup 2 ↥A) (hN₁A : N₁ ≤ A) (hZ₀ : Z₀ ≤ N₀) (c : ↥X) :
    Module.finrank (ZMod 2) (LinearMap.range ((s.ρ c).toLinearMap - LinearMap.id)) ≤
      mIdx A (centralizerMod Z₀ A (Subgroup.zpowers (c : G))) := by
  classical
  haveI : Module.Finite (ZMod 2) W := Module.finite_iff_finite.mpr inferInstance
  set f : W →ₗ[ZMod 2] W := (s.ρ c).toLinearMap - LinearMap.id with hf
  have hfap : ∀ w, f w = s.ρ c w - w := fun w => by simp [hf]
  let ψ : ↥N₁ →* Multiplicative W :=
    (AddMonoidHom.toMultiplicative f.toAddMonoidHom).comp s.cls
  have hψ : ∀ n : ↥N₁, Multiplicative.toAdd (ψ n) = f (s.cl n) := fun n => rfl
  have hcard : Nat.card ψ.range = 2 ^ Module.finrank (ZMod 2) (LinearMap.range f) := by
    have e : Nat.card ψ.range = Nat.card (LinearMap.range f) := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun x : ψ.range => (⟨Multiplicative.toAdd x.1, ?_⟩ : LinearMap.range f)) ⟨?_, ?_⟩)
      · obtain ⟨n, hn⟩ := x.2
        exact ⟨s.cl n, by rw [← hn, hψ]⟩
      · intro a b hab
        have h' := Subtype.ext_iff.mp hab
        exact Subtype.ext (Multiplicative.toAdd.injective h')
      · rintro ⟨w, ⟨v, hv⟩⟩
        obtain ⟨n, rfl⟩ := exists_cl s v
        exact ⟨⟨ψ n, ⟨n, rfl⟩⟩, Subtype.ext (by simpa [hψ] using hv)⟩
    rw [e, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  set C := centralizerMod Z₀ A (Subgroup.zpowers (c : G)) with hC
  have hker : C.subgroupOf N₁ ≤ ψ.ker := by
    intro n hn
    have hnC : (n : G) ∈ C := Subgroup.mem_subgroupOf.mp hn
    have hcomm : (n : G) * (c : G) * (n : G)⁻¹ * (c : G)⁻¹ ∈ Z₀ :=
      hnC.2.2 (c : G) (Subgroup.mem_zpowers _)
    have h1 : (c : G) * n * (c : G)⁻¹ * (n : G)⁻¹ ∈ N₀ := by
      have := N₀.inv_mem (hZ₀ hcomm)
      have e : ((n : G) * (c : G) * (n : G)⁻¹ * (c : G)⁻¹)⁻¹ =
          (c : G) * n * (c : G)⁻¹ * (n : G)⁻¹ := by group
      rwa [e] at this
    have h2 : s.ρ c (s.cl n) = s.cl n := (fix_iff hh s c n).mpr h1
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    rw [hψ, hfap, h2, sub_self]
    rfl
  have hidx : ψ.ker.index ≤ (C.subgroupOf N₁).index := by
    refine Nat.le_of_dvd ?_ (Subgroup.index_dvd_of_le hker)
    exact Nat.pos_of_ne_zero (relIndex_ne_zero' C N₁)
  have h1 : ψ.ker.index = 2 ^ Module.finrank (ZMod 2) (LinearMap.range f) := by
    rw [Subgroup.index_ker, hcard]
  have h2 : (C.subgroupOf N₁).index ≤ C.relIndex A := by
    have := Subgroup.relIndex_le_of_le_right hN₁A (relIndex_ne_zero' C A)
    exact this
  have h3 : C.relIndex A = 2 ^ mIdx A C := HypF98.relIndex_eq_two_pow_mIdx hA
  rw [h1] at hidx
  have : 2 ^ Module.finrank (ZMod 2) (LinearMap.range f) ≤ 2 ^ mIdx A C :=
    hidx.trans (h2.trans h3.le)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

end SecRep

end CFSG.Quasithin.H13.NFa2
