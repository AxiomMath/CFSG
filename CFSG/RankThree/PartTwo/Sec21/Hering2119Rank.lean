module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119Odd
public import CFSG.RankThree.PartTwo.Sec21.Hering2119Loc
import CFSG.RankThree.PartTwo.Sec21.Item221ProofCover
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL localRank)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits diagUnits_mul)

section Model

variable {G : Type} [Group G] [Finite G]

theorem exists_model {A K : Subgroup G} (hC : Sec4.IsTypeCOn A K)
    (hθ : aschbacherSolvableCore 3 K = ⊥) {n : ℕ} (hn : 2 ≤ n)
    (eL : lBar K ≃* projSL 3 (GaloisField 2 n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (Ψ : K ≃* projectiveSL 3 F) (τ : Fˣ),
      Nat.card F = 2 ^ n ∧ τ ^ 3 = 1 ∧ τ ≠ 1 ∧
      (∀ (a : G) (haN : a ∈ Subgroup.normalizer (K : Set G)), a ∈ A →
        ∃ s t : Fˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧ ∀ z : K,
          Ψ (K.normalizerMonoidHom ⟨a, haN⟩ z) = conjAut 3 F (diagUnits 1 s t) (Ψ z)) ∧
      (∀ s t : Fˣ, s ^ 3 = 1 → t ^ 3 = 1 → ∃ (a : G)
        (haN : a ∈ Subgroup.normalizer (K : Set G)), a ∈ A ∧ ∀ z : K,
          Ψ (K.normalizerMonoidHom ⟨a, haN⟩ z) = conjAut 3 F (diagUnits 1 s t) (Ψ z)) := by
  obtain ⟨F, instF, hFin, Φ, g, τ, hFcard, hτ3, hτ1, hpart1, hpart2⟩ :=
    exists_typeC_model hC hn eL
  have hinj : Function.Injective (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : x ∈ aschbacherSolvableCore 3 K := (QuotientGroup.eq_one_iff x).mp hx
    rw [hθ] at h1
    exact Subgroup.mem_bot.mp h1
  let mkE : K ≃* lBar K :=
    MulEquiv.ofBijective (QuotientGroup.mk' (aschbacherSolvableCore 3 K))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  let Ψ : K ≃* projectiveSL 3 F := (mkE.trans Φ).trans (conjAut 3 F g⁻¹)
  have hΨ : ∀ z : K, Ψ z = conjAut 3 F g⁻¹ (Φ (z : lBar K)) := fun z => rfl
  have hcomb : ∀ (y : GL (Fin 3) F) (w : projectiveSL 3 F),
      conjAut 3 F g⁻¹ (conjAut 3 F (g * y * g⁻¹) w) = conjAut 3 F y (conjAut 3 F g⁻¹ w) := by
    intro y w
    rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  have hact : ∀ (a : G) (haN : a ∈ Subgroup.normalizer (K : Set G)) (y : GL (Fin 3) F),
      (∀ w, Φ (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨a, haN⟩) w) =
        conjAut 3 F (g * y * g⁻¹) (Φ w)) →
      ∀ z : K, Ψ (K.normalizerMonoidHom ⟨a, haN⟩ z) = conjAut 3 F y (Ψ z) := by
    intro a haN y h z
    rw [hΨ, hΨ, ← hcomb, ← h]
    rfl
  refine ⟨F, instF, hFin, Ψ, τ, hFcard, hτ3, hτ1, ?_, ?_⟩
  · intro a haN haA
    obtain ⟨s, t, hs, ht, hst⟩ := hpart1 a haA haN
    exact ⟨s, t, hs, ht, hact a haN _ hst⟩
  · intro s t hs ht
    obtain ⟨a, haA, haN, hst⟩ := hpart2 s t hs ht
    exact ⟨a, haN, haA, hact a haN _ hst⟩

end Model


section Torus

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {F : Type} [Field F]

@[expose] def embK (Ψ : K ≃* projectiveSL 3 F) : projectiveSL 3 F →* G :=
  K.subtype.comp Ψ.symm.toMonoidHom

theorem embK_injective (Ψ : K ≃* projectiveSL 3 F) : Function.Injective (embK Ψ) :=
  K.subtype_injective.comp Ψ.symm.injective

theorem embK_mem (Ψ : K ≃* projectiveSL 3 F) (z : projectiveSL 3 F) : embK Ψ z ∈ K :=
  (Ψ.symm z).2

theorem conj_embK (Ψ : K ≃* projectiveSL 3 F) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (z : projectiveSL 3 F) :
    g * embK Ψ z * g⁻¹ = embK Ψ (MulAut.congr Ψ (K.normalizerMonoidHom ⟨g, hg⟩) z) := by
  have h1 : MulAut.congr Ψ (K.normalizerMonoidHom ⟨g, hg⟩) z =
      Ψ (K.normalizerMonoidHom ⟨g, hg⟩ (Ψ.symm z)) := rfl
  rw [h1]
  simp only [embK, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  exact (Sec4.normalizerMonoidHom_apply_coe hg (Ψ.symm z)).symm

@[expose] noncomputable def torusIn (Ψ : K ≃* projectiveSL 3 F) (p : ℕ) : Subgroup G :=
  (torSub p F).map (embK Ψ)

@[expose] noncomputable def rootIn (Ψ : K ≃* projectiveSL 3 F) : Subgroup G :=
  (rootSub F).map (embK Ψ)

theorem mem_torusIn {Ψ : K ≃* projectiveSL 3 F} {p : ℕ} {x : G} :
    x ∈ torusIn Ψ p ↔ ∃ z ∈ torSub p F, embK Ψ z = x := Subgroup.mem_map

theorem mem_rootIn {Ψ : K ≃* projectiveSL 3 F} {x : G} :
    x ∈ rootIn Ψ ↔ ∃ z ∈ rootSub F, embK Ψ z = x := Subgroup.mem_map

theorem congr_eq_conjAut {Ψ : K ≃* projectiveSL 3 F} {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) {y : GL (Fin 3) F}
    (h : ∀ z : K, Ψ (K.normalizerMonoidHom ⟨a, haN⟩ z) = conjAut 3 F y (Ψ z)) :
    MulAut.congr Ψ (K.normalizerMonoidHom ⟨a, haN⟩) = conjAut 3 F y := by
  ext w
  have h1 : MulAut.congr Ψ (K.normalizerMonoidHom ⟨a, haN⟩) w =
      Ψ (K.normalizerMonoidHom ⟨a, haN⟩ (Ψ.symm w)) := rfl
  rw [h1]
  have := h (Ψ.symm w)
  rwa [Ψ.apply_symm_apply] at this

end Torus


section Rank

theorem le_localRank_of_le_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 1 < p)
    {U : Subgroup G} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) {E : Subgroup G}
    (hEc : IsMulCommutative E) (hEp : ∀ w ∈ E, w ^ p = 1)
    (hEU : E ≤ Subgroup.normalizer (U : Set G)) {r : ℕ} (hr : Nat.card E = p ^ r) :
    r ≤ CFSG.Assembly.RankThreeEven.localRank p G := by
  have hbdd : BddAbove
      {k | ∃ H : Subgroup G, CFSG.Assembly.IsTwoLocal H ∧ CFSG.Assembly.pRank p H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨H, -, rfl⟩
    obtain ⟨F, -, -, hF⟩ := CFSG.SectionRank.exists_pRank hp H
    have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    change CFSG.Open.pRank p H ≤ Nat.card G
    omega
  exact (CFSG.SectionRank.le_pRank hp hEU ⟨hEc, hEp⟩ hr).trans
    (le_csSup hbdd ⟨_, ⟨U, hU, hU2, rfl⟩, rfl⟩)

end Rank


section Main

variable {G : Type} [Group G] [Finite G] {A K : Subgroup G} {F : Type} [Field F]
  {Ψ : K ≃* projectiveSL 3 F} {p : ℕ}

theorem torusIn_isElemAbelian (hp : p.Prime) : IsElemAbelian p (torusIn Ψ p) :=
  Item2119End5Proof.isElemAbelian_map
    ⟨⟨⟨fun a b => Subtype.ext (torSub_comm _ a.2 _ b.2)⟩⟩, torSub_pow_eq_one hp⟩ (embK Ψ)

theorem card_torusIn [Finite F] (hp : p.Prime) (hp3 : p ≠ 3) (hpF : p ∣ Nat.card F - 1) :
    Nat.card (torusIn Ψ p) = p ^ 2 := by
  rw [torusIn, Subgroup.card_map_of_injective (embK_injective Ψ), card_torSub hp hp3 hpF]

theorem torusIn_le : torusIn Ψ p ≤ K := by
  rintro _ ⟨z, -, rfl⟩
  exact embK_mem Ψ z

theorem torusIn_le_centralizer (hp : p.Prime)
    (hact : ∀ (a : G) (haN : a ∈ Subgroup.normalizer (K : Set G)), a ∈ A →
      ∃ s t : Fˣ, ∀ z : K,
        Ψ (K.normalizerMonoidHom ⟨a, haN⟩ z) = conjAut 3 F (diagUnits 1 s t) (Ψ z))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    torusIn Ψ p ≤ Subgroup.centralizer (A : Set G) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨s, t, hst⟩ := hact a (hAK ha) ha
  have h1 := conj_embK Ψ (hAK ha) z
  rw [congr_eq_conjAut (hAK ha) hst, conjAut_diagUnits_of_mem_torSub hp _ _ _ hz] at h1
  calc a * embK Ψ z = a * embK Ψ z * a⁻¹ * a := by group
    _ = embK Ψ z * a := by rw [h1]


theorem eq_torusIn [Finite F] (hp : p.Prime) (hp3 : p ≠ 3) (hpF : p ∣ Nat.card F - 1) {τ : Fˣ}
    (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hact : ∃ (a : G) (haN : a ∈ Subgroup.normalizer (K : Set G)), a ∈ A ∧ ∀ z : K,
      Ψ (K.normalizerMonoidHom ⟨a, haN⟩ z) = conjAut 3 F (diagUnits 1 τ (τ ^ 2)) (Ψ z))
    {P' : Subgroup G} (hP'K : P' ≤ K) (hP'C : P' ≤ Subgroup.centralizer (A : Set G))
    (hP'e : IsElemAbelian p P') (hP'card : Nat.card P' = p ^ 2) : P' = torusIn Ψ p := by
  obtain ⟨a, haN, haA, ha⟩ := hact
  set Pbar : Subgroup (projectiveSL 3 F) := (P'.subgroupOf K).map Ψ.toMonoidHom with hPbar
  have hcard : Nat.card Pbar = p ^ 2 := by
    rw [hPbar, Subgroup.card_map_of_injective Ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'K).toEquiv, hP'card]
  have hexp : ∀ z ∈ Pbar, z ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow]
    have : y ^ p = 1 := Subtype.ext (hP'e.2 y hy)
    rw [this, map_one]
  have hcomm : ∀ z ∈ Pbar, conjAut 3 F (diagUnits 1 τ (τ ^ 2)) z = z := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← ha y]
    congr 1
    apply Subtype.ext
    have hya : a * (y : G) = (y : G) * a := Subgroup.mem_centralizer_iff.mp (hP'C hy) a haA
    rw [Sec4.normalizerMonoidHom_apply_coe haN]
    calc a * (y : G) * a⁻¹ = (y : G) * a * a⁻¹ := by rw [hya]
      _ = (y : G) := by group
  have hPb : Pbar = torSub p F :=
    eq_torSub_of_centralized hp hp3 hpF hτ3 hτ1 Pbar hcard hexp hcomm
  ext x
  constructor
  · intro hx
    have hxK : x ∈ K := hP'K hx
    have hy : (⟨x, hxK⟩ : K) ∈ P'.subgroupOf K := hx
    have h1 : Ψ ⟨x, hxK⟩ ∈ torSub p F := hPb ▸ Subgroup.mem_map_of_mem _ hy
    refine mem_torusIn.mpr ⟨Ψ ⟨x, hxK⟩, h1, ?_⟩
    simp [embK]
  · intro hx
    obtain ⟨z, hz, rfl⟩ := mem_torusIn.mp hx
    rw [← hPb] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hy' : (y : G) ∈ P' := Subgroup.mem_subgroupOf.mp hy
    simpa [embK] using hy'


theorem mem_normalizer_of_conj_mem {U : Subgroup G} {x : G} (h : ∀ u ∈ U, x * u * x⁻¹ ∈ U) :
    x ∈ Subgroup.normalizer (U : Set G) := by
  have hle : U.map (MulAut.conj x).toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  have heq : U.map (MulAut.conj x).toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

@[expose] def mulOfCommute (P Q : Subgroup G) (h : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) :
    Subgroup G where
  carrier := {g | ∃ x ∈ P, ∃ y ∈ Q, g = x * y}
  mul_mem' := by
    rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
    refine ⟨x₁ * x₂, P.mul_mem hx₁ hx₂, y₁ * y₂, Q.mul_mem hy₁ hy₂, ?_⟩
    calc x₁ * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
      _ = x₁ * (x₂ * y₁) * y₂ := by rw [← h x₂ hx₂ y₁ hy₁]
      _ = x₁ * x₂ * (y₁ * y₂) := by group
  one_mem' := ⟨1, P.one_mem, 1, Q.one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    refine ⟨x⁻¹, P.inv_mem hx, y⁻¹, Q.inv_mem hy, ?_⟩
    calc (x * y)⁻¹ = (y * x)⁻¹ := by rw [h x hx y hy]
      _ = x⁻¹ * y⁻¹ := _root_.mul_inv_rev y x

theorem le_mulOfCommute_left {P Q : Subgroup G} {h : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x} :
    P ≤ mulOfCommute P Q h := fun x hx => ⟨x, hx, 1, Q.one_mem, by simp⟩

theorem le_mulOfCommute_right {P Q : Subgroup G} {h : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x} :
    Q ≤ mulOfCommute P Q h := fun y hy => ⟨1, P.one_mem, y, hy, by simp⟩

theorem mulOfCommute_isElemAbelian {P Q : Subgroup G} (h : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x)
    (hP : IsElemAbelian p P) (hQ : IsElemAbelian p Q) : IsElemAbelian p (mulOfCommute P Q h) := by
  have hPc : ∀ x ∈ P, ∀ x' ∈ P, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hP.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hQc : ∀ y ∈ Q, ∀ y' ∈ Q, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hQ.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, x₁, hx₁, y₁, hy₁, h₁⟩ := a
    obtain ⟨_, x₂, hx₂, y₂, hy₂, h₂⟩ := b
    apply Subtype.ext
    subst h₁ h₂
    change x₁ * y₁ * (x₂ * y₂) = x₂ * y₂ * (x₁ * y₁)
    calc x₁ * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
      _ = x₁ * (x₂ * y₁) * y₂ := by rw [← h x₂ hx₂ y₁ hy₁]
      _ = (x₁ * x₂) * (y₁ * y₂) := by group
      _ = (x₂ * x₁) * (y₂ * y₁) := by rw [hPc x₁ hx₁ x₂ hx₂, hQc y₁ hy₁ y₂ hy₂]
      _ = x₂ * (x₁ * y₂) * y₁ := by group
      _ = x₂ * (y₂ * x₁) * y₁ := by rw [h x₁ hx₁ y₂ hy₂]
      _ = x₂ * y₂ * (x₁ * y₁) := by group
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    have hxy : Commute x y := h x hx y hy
    rw [hxy.mul_pow, hP.2 x hx, hQ.2 y hy, one_mul]


theorem congr_nm_commute {x a : G} (hx : x ∈ Subgroup.normalizer (K : Set G))
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (h : x * a = a * x) :
    MulAut.congr Ψ (K.normalizerMonoidHom ⟨x, hx⟩) *
        MulAut.congr Ψ (K.normalizerMonoidHom ⟨a, ha⟩) =
      MulAut.congr Ψ (K.normalizerMonoidHom ⟨a, ha⟩) *
        MulAut.congr Ψ (K.normalizerMonoidHom ⟨x, hx⟩) := by
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  have : (⟨x, hx⟩ : Subgroup.normalizer (K : Set G)) * ⟨a, ha⟩ = ⟨a, ha⟩ * ⟨x, hx⟩ :=
    Subtype.ext h
  rw [this]

theorem action_of_centralizes [Finite F] (hp : p.Prime) (hp3 : 3 < p)
    (hpF : p ∣ Nat.card F - 1) {τ : Fˣ} (hτ1 : τ ≠ 1)
    (hact₂ : ∃ (a : G) (haN : a ∈ Subgroup.normalizer (K : Set G)), a ∈ A ∧ ∀ z : K,
      Ψ (K.normalizerMonoidHom ⟨a, haN⟩ z) = conjAut 3 F (diagUnits 1 1 τ) (Ψ z))
    (hact₃ : ∃ (a : G) (haN : a ∈ Subgroup.normalizer (K : Set G)), a ∈ A ∧ ∀ z : K,
      Ψ (K.normalizerMonoidHom ⟨a, haN⟩ z) = conjAut 3 F (diagUnits 1 τ 1) (Ψ z))
    {x : G} (hxC : x ∈ Subgroup.centralizer (A : Set G))
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hxp : x ^ p = 1) :
    (∀ z ∈ torSub p F, MulAut.congr Ψ (K.normalizerMonoidHom ⟨x, hxN⟩) z = z) ∧
      ∀ u ∈ rootSub F, MulAut.congr Ψ (K.normalizerMonoidHom ⟨x, hxN⟩) u ∈ rootSub F := by
  obtain ⟨a₂, haN₂, haA₂, ha₂⟩ := hact₂
  obtain ⟨a₃, haN₃, haA₃, ha₃⟩ := hact₃
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
  set β := MulAut.congr Ψ (K.normalizerMonoidHom ⟨x, hxN⟩) with hβ
  have hβp : β ^ p = 1 := by
    rw [hβ, ← map_pow, ← map_pow]
    have : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 := Subtype.ext hxp
    rw [this, map_one, map_one]
  have hxa : ∀ a ∈ A, x * a = a * x := fun a ha =>
    (Subgroup.mem_centralizer_iff.mp hxC a ha).symm
  have hc₂ : β * conjAut 3 F (diagUnits 1 1 τ) = conjAut 3 F (diagUnits 1 1 τ) * β := by
    rw [← congr_eq_conjAut haN₂ ha₂]
    exact congr_nm_commute hxN haN₂ (hxa a₂ haA₂)
  have hc₃ : β * conjAut 3 F (diagUnits 1 τ 1) = conjAut 3 F (diagUnits 1 τ 1) * β := by
    rw [← congr_eq_conjAut haN₃ ha₃]
    exact congr_nm_commute hxN haN₃ (hxa a₃ haA₃)
  obtain ⟨B, σ, hβB, hB⟩ := odd_aut_diag hodd hτ1 hβp hc₂ hc₃
  rw [hβB] at hβp
  refine ⟨fun z hz => ?_, fun u hu => ?_⟩
  · rw [hβB]
    exact aut_fixes_torus hp hpF hB hβp hz
  · rw [hβB]
    exact aut_maps_rootSub hB σ hu


theorem le_of_centralizes [Finite F] [CharP F 2] (hp : p.Prime) (hp3 : 3 < p)
    (hpF : p ∣ Nat.card F - 1) {τ : Fˣ} (hτ1 : τ ≠ 1)
    (hact₂ : ∃ (a : G) (haN : a ∈ Subgroup.normalizer (K : Set G)), a ∈ A ∧ ∀ z : K,
      Ψ (K.normalizerMonoidHom ⟨a, haN⟩ z) = conjAut 3 F (diagUnits 1 1 τ) (Ψ z))
    (hact₃ : ∃ (a : G) (haN : a ∈ Subgroup.normalizer (K : Set G)), a ∈ A ∧ ∀ z : K,
      Ψ (K.normalizerMonoidHom ⟨a, haN⟩ z) = conjAut 3 F (diagUnits 1 τ 1) (Ψ z))
    (hCK : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hrank : localRank p G < 3) {P : Subgroup G} (hPC : P ≤ Subgroup.centralizer (A : Set G))
    (hPe : IsElemAbelian p P) : P ≤ K := by
  by_contra hPK
  have hp3' : p ≠ 3 := hp3.ne'
  have hdata : ∀ (x : G) (hx : x ∈ P),
      (∀ z ∈ torSub p F, MulAut.congr Ψ (K.normalizerMonoidHom ⟨x, hCK (hPC hx)⟩) z = z) ∧
      ∀ u ∈ rootSub F, MulAut.congr Ψ (K.normalizerMonoidHom ⟨x, hCK (hPC hx)⟩) u ∈ rootSub F :=
    fun x hx => action_of_centralizes hp hp3 hpF hτ1 hact₂ hact₃ (hPC hx) (hCK (hPC hx))
      (hPe.2 x hx)
  have hcomm : ∀ x ∈ P, ∀ y ∈ torusIn Ψ p, x * y = y * x := by
    intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := mem_torusIn.mp hy
    have h1 := conj_embK Ψ (hCK (hPC hx)) z
    rw [(hdata x hx).1 z hz] at h1
    calc x * embK Ψ z = x * embK Ψ z * x⁻¹ * x := by group
      _ = embK Ψ z * x := by rw [h1]
  set U := rootIn Ψ with hU
  have hUne : U ≠ ⊥ := by
    intro h
    exact rootSub_ne_bot
      ((Subgroup.map_eq_bot_iff_of_injective (rootSub F) (embK_injective Ψ)).mp h)
  have hU2 : IsPGroup 2 U := by
    rintro ⟨_, r, hr, rfl⟩
    obtain ⟨k, hk⟩ := rootSub_isPGroup (F := F) ⟨r, hr⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : r ^ 2 ^ k = 1 := congrArg Subtype.val hk
    change (embK Ψ r) ^ 2 ^ k = 1
    rw [← map_pow, h1, map_one]
  have hxU : ∀ x ∈ P, x ∈ Subgroup.normalizer (U : Set G) := by
    intro x hx
    apply mem_normalizer_of_conj_mem
    intro u hu
    obtain ⟨r, hr, rfl⟩ := mem_rootIn.mp hu
    rw [conj_embK Ψ (hCK (hPC hx)) r]
    exact mem_rootIn.mpr ⟨_, (hdata x hx).2 r hr, rfl⟩
  have hyU : ∀ y ∈ torusIn Ψ p, y ∈ Subgroup.normalizer (U : Set G) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_torusIn.mp hy
    obtain ⟨a, b, c, h, ha, hb, hc, rfl⟩ := (mem_torSub_iff hp).mp hz
    apply mem_normalizer_of_conj_mem
    intro u hu
    obtain ⟨r, hr, rfl⟩ := mem_rootIn.mp hu
    refine mem_rootIn.mpr ⟨_, proj_diagSL_conj_mem_rootSub a b c h hr, ?_⟩
    simp [map_mul, map_inv]
  set PK := torusIn Ψ p with hPK'
  set R := mulOfCommute P PK hcomm with hR
  have hRe : IsElemAbelian p R :=
    mulOfCommute_isElemAbelian hcomm hPe (torusIn_isElemAbelian hp)
  have hRU : R ≤ Subgroup.normalizer (U : Set G) := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact Subgroup.mul_mem _ (hxU x hx) (hyU y hy)
  haveI : Fact p.Prime := ⟨hp⟩
  have hRp : IsPGroup p R := fun g => ⟨1, Subtype.ext (by simpa using hRe.2 g g.2)⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hRp
  have hPKcard : Nat.card PK = p ^ 2 := card_torusIn hp hp3' hpF
  have hPKR : PK ≤ R := le_mulOfCommute_right
  have hcardle : p ^ 2 ≤ p ^ r := by
    rw [← hPKcard, ← hr]
    exact Subgroup.card_le_of_le hPKR
  have hr2 : 2 ≤ r := (Nat.pow_le_pow_iff_right hp.one_lt).mp hcardle
  have hr3 : 3 ≤ r := by
    by_contra hlt
    have hreq : r = 2 := by omega
    have hRPK : PK = R := Subgroup.eq_of_le_of_card_ge hPKR (by rw [hr, hPKcard, hreq])
    apply hPK
    intro x hx
    have hxR : x ∈ R := le_mulOfCommute_left hx
    rw [← hRPK] at hxR
    exact torusIn_le hxR
  have := le_localRank_of_le_normalizer hp.one_lt hUne hU2 hRe.1 hRe.2 hRU hr
  omega


end Main

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem exists_torus {A K : Subgroup G} (hC : Sec4.IsTypeCOn A K)
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hCK : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hθ : aschbacherSolvableCore 3 K = ⊥) {n : ℕ} (hn : 2 ≤ n)
    (eL : lBar K ≃* projSL 3 (GaloisField 2 n)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpn : p ∣ 2 ^ n - 1) (hrank : localRank p G < 3) :
    ∃ PK : Subgroup G, PK ≤ K ∧ IsElemAbelian p PK ∧ Nat.card PK = p ^ 2 ∧
      PK ≤ Subgroup.centralizer (A : Set G) ∧
      (∀ P' : Subgroup G, P' ≤ K → P' ≤ Subgroup.centralizer (A : Set G) →
        IsElemAbelian p P' → Nat.card P' = p ^ 2 → P' = PK) ∧
      (∀ P : Subgroup G, P ≤ Subgroup.centralizer (A : Set G) → IsElemAbelian p P → P ≤ K) := by
  obtain ⟨F, instF, hFin, Ψ, τ, hFcard, hτ3, hτ1, hpart1, hpart2⟩ := exists_model hC hθ hn eL
  have hp3' : p ≠ 3 := hp3.ne'
  have hpF : p ∣ Nat.card F - 1 := by rw [hFcard]; exact hpn
  haveI : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hFcard
  have hactA : ∀ (a : G) (haN : a ∈ Subgroup.normalizer (K : Set G)), a ∈ A →
      ∃ s t : Fˣ, ∀ z : K,
        Ψ (K.normalizerMonoidHom ⟨a, haN⟩ z) = conjAut 3 F (diagUnits 1 s t) (Ψ z) :=
    fun a haN haA => by
      obtain ⟨s, t, -, -, h⟩ := hpart1 a haN haA
      exact ⟨s, t, h⟩
  have hτ23 : (τ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτ3, one_pow]
  have hact1 := hpart2 τ (τ ^ 2) hτ3 hτ23
  have hact2 := hpart2 1 τ (one_pow 3) hτ3
  have hact3 := hpart2 τ 1 hτ3 (one_pow 3)
  obtain ⟨a₁, haN₁, haA₁, ha₁⟩ := hact1
  obtain ⟨a₂, haN₂, haA₂, ha₂⟩ := hact2
  obtain ⟨a₃, haN₃, haA₃, ha₃⟩ := hact3
  refine ⟨torusIn Ψ p, torusIn_le, torusIn_isElemAbelian hp, card_torusIn hp hp3' hpF,
    torusIn_le_centralizer hp hactA hAK, ?_, ?_⟩
  · intro P' hP'K hP'C hP'e hP'card
    exact eq_torusIn hp hp3' hpF hτ3 hτ1 ⟨a₁, haN₁, haA₁, ha₁⟩ hP'K hP'C hP'e hP'card
  · intro P hPC hPe
    exact le_of_centralizes hp hp3 hpF hτ1 ⟨a₂, haN₂, haA₂, ha₂⟩ ⟨a₃, haN₃, haA₃, ha₃⟩ hCK hrank
      hPC hPe

end Assembly


section Theta

variable {G : Type} [Group G] [Finite G]

theorem exceptionalOrders_PSL_three {n : ℕ} (hn : 3 ≤ n) :
    Blueprint.Multiplier.exceptionalOrders .PSL 3 2 n = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (simp_all; omega) | omega

theorem theta_eq_bot_of_lthree
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Subgroup G} (hq : CFSG.IsQuasisimple K) {n : ℕ} (hn : 3 ≤ n)
    (eL : lBar K ≃* projSL 3 (GaloisField 2 n)) : aschbacherSolvableCore 3 K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (projSL 3 (GaloisField 2 n)) :=
    Item222Proof.isSimpleGroup_projSL_three _
  haveI : IsSimpleGroup (lBar K) := eL.isSimpleGroup
  have hZT : Subgroup.center K = aschbacherSolvableCore 3 K :=
    Item221Proof.center_eq_theta hq (Item221Proof.center_lBar_eq_bot hq)
  have eZ : K ⧸ Subgroup.center K ≃* projSL 3 (GaloisField 2 n) :=
    (QuotientGroup.quotientMulEquivOfEq hZT).trans eL
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 3 2 n := by
    refine ⟨Nat.prime_two, by omega, ?_⟩
    change 2 ≤ 3 ∧ (3, 2 ^ n) ≠ (2, 2) ∧ (3, 2 ^ n) ≠ (2, 3)
    exact ⟨by norm_num, by simp, by simp⟩
  have hm := KFacts.KS21Mult.lieModel_projSL hadm
  have hdvd := Item221Proof.card_center_dvd_table hGA hq.1 eZ hm
  have hex : Blueprint.Multiplier.exceptionalOrders .PSL 3 2 n = (1, 1) :=
    exceptionalOrders_PSL_three hn
  have hgen : Blueprint.Multiplier.genericOrders .PSL 3 2 n = (Nat.gcd 3 (2 ^ n - 1), 1) := rfl
  rw [hex, hgen] at hdvd
  have h3 : Nat.card (Subgroup.center K) ∣ 3 := by
    have h1 : Nat.card (Subgroup.center K) ∣ Nat.gcd 3 (2 ^ n - 1) := by simpa using hdvd
    exact h1.trans (Nat.gcd_dvd_left _ _)
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 K) :=
    (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.1
  rw [← hZT] at hθ3
  have h1 : Nat.card (Subgroup.center K) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact h
    · exact (hθ3 (by rw [h])).elim
  rw [hZT] at h1
  exact Subgroup.eq_bot_of_card_eq _ h1

end Theta


section Final

variable {G : Type} [Group G] [Finite G]


theorem item2126LocTorus_of (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116)
    (h218 : Item218) (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h66 : Sec6.Item6_6) (hStar : Item2125Star) (h213 : Item213)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    Item2126LocTorus := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf n p hLn hp hp3 hpd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 : d ≠ 1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  obtain ⟨n', hn'0, hn'e, ⟨eL'⟩⟩ := hcfg.lthree
  obtain ⟨eLn⟩ := hLn
  have hnn : n' = max n 1 := eq_max_of_equiv hn'0 (eLn.symm.trans eL')
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hn'e
    omega
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn2' : n = 2 := by omega
    subst hn2'
    have h3p : p ∣ 3 := by simpa using hpd
    have := Nat.le_of_dvd (by norm_num) h3p
    omega
  have hrank : localRank p G < 3 := hpair.standing.toTheoremFourHyp.localRank_lt p hp hp3
  have hex : ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∃ PK : Subgroup G, PK ≤ Lf e ∧
      IsElemAbelian p PK ∧ Nat.card PK = p ^ 2 ∧ PK ≤ Subgroup.centralizer (A : Set G) ∧
      (∀ P' : Subgroup G, P' ≤ Lf e → P' ≤ Subgroup.centralizer (A : Set G) →
        IsElemAbelian p P' → Nat.card P' = p ^ 2 → P' = PK) ∧
      (∀ P : Subgroup G, P ≤ Subgroup.centralizer (A : Set G) → IsElemAbelian p P →
        P ≤ Lf e) ∧ aschbacherSolvableCore 3 (Lf e) = ⊥ := by
    intro e he hed
    obtain ⟨U', hcfgK⟩ := exists_config_Le h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar hE h23
      h24 hLf he hed
    have hLe := hLf e he hed
    have hAK : A ≤ Subgroup.normalizer (Lf e : Set G) := fun x hx =>
      mem_normalizer_of_fix hLe (by rw [hcomm x hx e he]; group)
    have hCK : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Lf e : Set G) :=
      fun x hx => mem_normalizer_of_fix hLe
        (by rw [← Subgroup.mem_centralizer_iff.mp hx e he]; group)
    obtain ⟨eLe⟩ := hLe.2.2.2.1
    have eLe' : lBar (Lf e) ≃* projSL 3 (GaloisField 2 n) := eLe.trans eLn
    have hθ := theta_eq_bot_of_lthree hGA (h213 G A E U' e (Lf e) hcfgK.pair) hn3 eLe'
    obtain ⟨PK, h1, h2, h3', h4, h5, h6⟩ :=
      exists_torus hcfgK.typeC hAK hCK hθ hn2 eLe' hp (by omega) hpd hrank
    exact ⟨PK, h1, h2, h3', h4, h5, h6, hθ⟩
  have hexe : ∃ e₀ ∈ A, e₀ ∉ Subgroup.zpowers d := by
    by_contra hcon
    have hle : A ≤ Subgroup.zpowers d := fun x hx => by
      by_contra hxd
      exact hcon ⟨x, hx, hxd⟩
    have h10 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1, h27] at h10
    omega
  obtain ⟨e₀, he₀A, he₀d⟩ := hexe
  obtain ⟨P, -, hPe, hPcard, hPC, -, -, -⟩ := hex e₀ he₀A he₀d
  refine ⟨P, hPe, hPcard, hPC, fun e he hed => ?_⟩
  obtain ⟨PK, -, -, -, -, hPKuniq, hcont, hθ⟩ := hex e he hed
  have hPle : P ≤ Lf e := hcont P hPC hPe
  have hPeq : P = PK := hPKuniq P hPle hPC hPe hPcard
  refine ⟨hPle, ?_, fun P' hP'K hP'C hP'e hP'card => ?_⟩
  · intro x hx _ hx1
    have h1 : (⟨x, hx⟩ : Lf e) ∈ aschbacherSolvableCore 3 (Lf e) :=
      (QuotientGroup.eq_one_iff _).mp hx1
    rw [hθ] at h1
    exact congrArg Subtype.val (Subgroup.mem_bot.mp h1)
  · rw [hPKuniq P' hP'K hP'C hP'e hP'card, hPeq]

end Final

end CFSG.RankThree.PartTwo.Sec21.Hering2119

namespace CFSG.RankThree.PartTwo.Sec21

section Holds


theorem item2126Loc_holds (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116)
    (h218 : Item218) (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h66 : Sec6.Item6_6) (hStar : Item2125Star) (h213 : Item213)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) : Item2126Loc :=
  Hering2119.item2126Loc_of_torus h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar
    (Hering2119.item2126LocTorus_of h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar h213 hGA)

theorem item2126_holds (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116)
    (h218 : Item218) (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h66 : Sec6.Item6_6) (hStar : Item2125Star) (h213 : Item213)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) : Item2126 :=
  item2126_of (item2126Torus_of h211 h2116 h45 h66
    (item2126P_of_loc (item2126Loc_holds h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar h213 hGA)))

end Holds

end CFSG.RankThree.PartTwo.Sec21
