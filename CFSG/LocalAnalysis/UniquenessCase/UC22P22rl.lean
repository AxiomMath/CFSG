module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rf
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rh
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ri
import CFSG.Goldschmidt.Steps.Components
import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.GLTheoremB (quotAutHom quotAutHom_mk)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

abbrev uc22p22rKt (K : Subgroup G) : Type := Bar2 K ⧸ Subgroup.center (Bar2 K)

noncomputable def uc22p22rPsi (K : Subgroup G) : ↥K →* uc22p22rKt K :=
  (QuotientGroup.mk' (Subgroup.center (Bar2 K))).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))

theorem uc22p22rPsi_surjective (K : Subgroup G) : Function.Surjective (uc22p22rPsi K) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem uc22p22r_sup_le_normalizer {K X : Subgroup G} (hXK : X ≤ normalizer (K : Set G)) :
    K ⊔ X ≤ normalizer (K : Set G) :=
  sup_le Subgroup.le_normalizer hXK

noncomputable def uc22p22rRho0 (K X : Subgroup G) (hXK : X ≤ normalizer (K : Set G)) :
    ↥(K ⊔ X) →* MulAut ↥K :=
  K.normalizerMonoidHom.comp (Subgroup.inclusion (uc22p22r_sup_le_normalizer hXK))

theorem uc22p22rRho0_apply {K X : Subgroup G} (hXK : X ≤ normalizer (K : Set G)) (n : ↥(K ⊔ X))
    (k : ↥K) : ((uc22p22rRho0 K X hXK n k : ↥K) : G) = (n : G) * (k : G) * (n : G)⁻¹ := by
  simp [uc22p22rRho0]

noncomputable def uc22p22rRho1 (K X : Subgroup G) (hXK : X ≤ normalizer (K : Set G)) :
    ↥(K ⊔ X) →* MulAut (Bar2 K) :=
  quotAutHom (CFSG.pCore 2 ↥K) (uc22p22rRho0 K X hXK) (fun γ => by
    have h := Subgroup.characteristic_iff_map_eq.1
      (CFSG.pCore_characteristic (p := 2) (G := ↥K)) (uc22p22rRho0 K X hXK γ)
    exact h)

noncomputable def uc22p22rRho (K X : Subgroup G) (hXK : X ≤ normalizer (K : Set G)) :
    ↥(K ⊔ X) →* MulAut (uc22p22rKt K) :=
  quotAutHom (Subgroup.center (Bar2 K)) (uc22p22rRho1 K X hXK) (fun γ =>
    Subgroup.characteristic_iff_map_eq.1 inferInstance (uc22p22rRho1 K X hXK γ))

theorem uc22p22rRho_psi {K X : Subgroup G} (hXK : X ≤ normalizer (K : Set G)) (n : ↥(K ⊔ X)) (k : ↥K) :
    uc22p22rRho K X hXK n (uc22p22rPsi K k) = uc22p22rPsi K (uc22p22rRho0 K X hXK n k) := by
  unfold uc22p22rRho uc22p22rPsi
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [quotAutHom_mk, uc22p22rRho1, quotAutHom_mk]

section KtFacts

variable {K : Subgroup G}

theorem uc22p22r_center_Kt (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    Subgroup.center (uc22p22rKt K) = ⊥ := by
  haveI : Group.IsPerfect (Bar2 K) := ⟨hKq.1⟩
  exact Group.IsPerfect.center_quotient_center_eq_bot (Bar2 K)

theorem uc22p22r_Kt_simple (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) : IsSimpleGroup (uc22p22rKt K) :=
  hKq.2

theorem uc22p22r_Kt_nonab (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    ∃ a b : uc22p22rKt K, a * b ≠ b * a := by
  haveI : Group.IsPerfect (Bar2 K) := ⟨hKq.1⟩
  haveI : IsSimpleGroup (uc22p22rKt K) := hKq.2
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative (uc22p22rKt K) := ⟨⟨fun a b => hcon a b⟩⟩
  haveI : Group.IsPerfect (uc22p22rKt K) := inferInstance
  have h1 : commutator (uc22p22rKt K) = ⊥ := commutator_eq_bot _
  have h2 : commutator (uc22p22rKt K) = ⊤ := Group.IsPerfect.commutator_eq_top
  have : (⊥ : Subgroup (uc22p22rKt K)) = ⊤ := h1.symm.trans h2
  exact bot_ne_top this

def uc22p22rZK (K : Subgroup G) : Subgroup ↥K :=
  (Subgroup.center (Bar2 K)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))

theorem uc22p22rZK_eq_ker (K : Subgroup G) : uc22p22rZK K = (uc22p22rPsi K).ker := by
  ext k
  simp [uc22p22rZK, uc22p22rPsi, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]

theorem uc22p22rZK_isSolvable (K : Subgroup G) : Group.IsSolvable ↥(uc22p22rZK K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : CFSG.pCore 2 ↥K ≤ uc22p22rZK K := by
    intro z hz
    show (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) z ∈ Subgroup.center (Bar2 K)
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) z = 1 := (QuotientGroup.eq_one_iff z).2 hz
    rw [h1]
    exact Subgroup.one_mem _
  let f : ↥(CFSG.pCore 2 ↥K) →* ↥(uc22p22rZK K) := Subgroup.inclusion hle
  let g : ↥(uc22p22rZK K) →* ↥(Subgroup.center (Bar2 K)) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (uc22p22rZK K).subtype).codRestrict
      (Subgroup.center (Bar2 K)) (fun z => z.2)
  have hnil : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) := CFSG.pCore_isNilpotent
  haveI : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := inferInstance
  haveI : Group.IsSolvable ↥(Subgroup.center (Bar2 K)) := inferInstance
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro z hz
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (z : ↥K) = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 hz)
    exact this
  exact ⟨⟨(z : ↥K), (QuotientGroup.eq_one_iff _).1 h1⟩, rfl⟩

theorem uc22p22rZK_le_oinf {K H : Subgroup G} (hKH : IsSubnormal K H) :
    (uc22p22rZK K).map K.subtype ≤ OInf H := by
  refine uc22p22r_le_oinf_of_normal_subnormal (Subgroup.map_subtype_le _) ?_ ?_ hKH
  · have h : ((uc22p22rZK K).map K.subtype).subgroupOf K = uc22p22rZK K :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [h, uc22p22rZK_eq_ker]
    exact MonoidHom.normal_ker _
  · haveI := uc22p22rZK_isSolvable K
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective (uc22p22rZK K) K.subtype K.subtype_injective)

end KtFacts

section GroupPart

variable {K X : Subgroup G} (hXK : X ≤ normalizer (K : Set G))

theorem uc22p22rRho_incl (n : ↥(K ⊔ X)) (k : ↥K) (hnk : (n : G) = (k : G)) :
    uc22p22rRho K X hXK n = MulAut.conj (uc22p22rPsi K k) := by
  ext a
  obtain ⟨k', rfl⟩ := uc22p22rPsi_surjective K a
  rw [uc22p22rRho_psi]
  have h : uc22p22rRho0 K X hXK n k' = k * k' * k⁻¹ :=
    Subtype.ext (by rw [uc22p22rRho0_apply]; simp [hnk])
  rw [h, map_mul, map_mul, map_inv, MulAut.conj_apply]

theorem uc22p22r_conj_range_le :
    (MulAut.conj : uc22p22rKt K →* MulAut (uc22p22rKt K)).range ≤ (uc22p22rRho K X hXK).range := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨k, rfl⟩ := uc22p22rPsi_surjective K a
  exact ⟨⟨(k : G), Subgroup.mem_sup_left k.2⟩, (uc22p22rRho_incl hXK _ k rfl)⟩

theorem uc22p22r_conj_injective (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    Function.Injective (MulAut.conj : uc22p22rKt K →* MulAut (uc22p22rKt K)) := by
  intro a b hab
  have h : ∀ g, a * g * a⁻¹ = b * g * b⁻¹ := fun g => by
    simpa [MulAut.conj_apply] using DFunLike.congr_fun hab g
  have hz : b⁻¹ * a ∈ Subgroup.center (uc22p22rKt K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := h g
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h1]
      _ = (b⁻¹ * a) * g := by group
  rw [uc22p22r_center_Kt hKq, Subgroup.mem_bot] at hz
  exact (inv_mul_eq_one.1 hz).symm

abbrev uc22p22rGh (K X : Subgroup G) (hXK : X ≤ normalizer (K : Set G)) : Type :=
  ↥(uc22p22rRho K X hXK).range

noncomputable def uc22p22rS (K X : Subgroup G) (hXK : X ≤ normalizer (K : Set G)) : Subgroup (uc22p22rGh K X hXK) :=
  (MulAut.conj : uc22p22rKt K →* MulAut (uc22p22rKt K)).range.subgroupOf (uc22p22rRho K X hXK).range

noncomputable def uc22p22rSEquiv (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    uc22p22rKt K ≃* ↥(uc22p22rS K X hXK) :=
  (MonoidHom.ofInjective (uc22p22r_conj_injective hKq)).trans
    (Subgroup.subgroupOfEquivOfLe (uc22p22r_conj_range_le hXK)).symm

theorem uc22p22rS_normal : (uc22p22rS K X hXK).Normal := by
  constructor
  intro n hn g
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.1 hn
  refine Subgroup.mem_subgroupOf.2 ⟨g.1 a, ?_⟩
  have h : (g : MulAut (uc22p22rKt K)) * (MulAut.conj a) * (g : MulAut (uc22p22rKt K))⁻¹ =
      MulAut.conj (g.1 a) := by
    ext x
    simp [MulAut.conj_apply]
  show _ = (g : MulAut (uc22p22rKt K)) * (n : MulAut (uc22p22rKt K)) * (g : MulAut (uc22p22rKt K))⁻¹
  rw [← ha]
  exact h.symm

end GroupPart

section Images

variable {K X : Subgroup G} (hXK : X ≤ normalizer (K : Set G))

theorem uc22p22rS_centralizer (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    centralizer ((uc22p22rS K X hXK : Subgroup (uc22p22rGh K X hXK)) : Set (uc22p22rGh K X hXK)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  ext a
  have hcomm : ∀ b : uc22p22rKt K, ∀ y : uc22p22rKt K,
      b * (g.1 y) * b⁻¹ = g.1 (b * y * b⁻¹) := by
    intro b y
    have h := Subgroup.mem_centralizer_iff.1 hg ⟨MulAut.conj b, uc22p22r_conj_range_le hXK ⟨b, rfl⟩⟩
      (Subgroup.mem_subgroupOf.2 ⟨b, rfl⟩)
    have h2 := DFunLike.congr_fun (congrArg Subtype.val h) y
    simpa [MulAut.conj_apply] using h2
  have h2 : MulAut.conj (g.1 a) = MulAut.conj a := by
    ext x
    obtain ⟨y, rfl⟩ := g.1.surjective x
    rw [MulAut.conj_apply, MulAut.conj_apply, hcomm a y, map_mul, map_mul, map_inv]
  have h3 := uc22p22r_conj_injective hKq h2
  simpa using h3

theorem uc22p22rS_simple (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    IsSimpleGroup ↥(uc22p22rS K X hXK) := by
  haveI := uc22p22r_Kt_simple hKq
  exact (uc22p22rSEquiv hXK hKq).symm.isSimpleGroup

theorem uc22p22rS_nonab (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    ∃ a b : ↥(uc22p22rS K X hXK), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := uc22p22r_Kt_nonab hKq
  refine ⟨uc22p22rSEquiv hXK hKq a, uc22p22rSEquiv hXK hKq b, fun h => hab ?_⟩
  apply (uc22p22rSEquiv hXK hKq).injective
  simpa using h

end Images

section Final

variable {K X : Subgroup G} (hXK : X ≤ normalizer (K : Set G))

noncomputable def uc22p22rPi (K X : Subgroup G) (hXK : X ≤ normalizer (K : Set G)) :
    ↥(K ⊔ X) →* uc22p22rGh K X hXK :=
  (uc22p22rRho K X hXK).rangeRestrict

theorem uc22p22rPi_surjective : Function.Surjective (uc22p22rPi K X hXK) :=
  MonoidHom.rangeRestrict_surjective _

theorem uc22p22rPi_eq_one_iff (n : ↥(K ⊔ X)) :
    uc22p22rPi K X hXK n = 1 ↔ uc22p22rRho K X hXK n = 1 := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    simpa [uc22p22rPi] using this
  · intro h
    apply Subtype.ext
    simpa [uc22p22rPi] using h

theorem uc22p22rPi_mem_S (n : ↥(K ⊔ X)) (hn : (n : G) ∈ K) : uc22p22rPi K X hXK n ∈ uc22p22rS K X hXK :=
  Subgroup.mem_subgroupOf.2 ⟨uc22p22rPsi K ⟨n, hn⟩, (uc22p22rRho_incl hXK n ⟨n, hn⟩ rfl).symm⟩

noncomputable def uc22p22rImg (A : Subgroup G) : Subgroup (uc22p22rGh K X hXK) :=
  (A.subgroupOf (K ⊔ X)).map (uc22p22rPi K X hXK)

theorem uc22p22r_mem_img {A : Subgroup G} {g : uc22p22rGh K X hXK} :
    g ∈ uc22p22rImg hXK A ↔ ∃ n : ↥(K ⊔ X), (n : G) ∈ A ∧ uc22p22rPi K X hXK n = g := by
  unfold uc22p22rImg
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem uc22p22r_zpowers_comm {x : G} : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact (Commute.zpow_zpow_self x i j).eq

theorem uc22p22r_ker_le {M : Subgroup G} (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) (hXM : X ≤ M)
    (hZ : ∀ k : ↥K, uc22p22rPsi K k = 1 → (k : G) ∈ M)
    (h0 : ∀ Y : Subgroup G, X ≤ Y → Y ≤ M → ∀ n ∈ K ⊔ X, n ∈ normalizer (Y : Set G) → n ∈ M)
    (n : ↥(K ⊔ X)) (hn : uc22p22rRho K X hXK n = 1) : (n : G) ∈ M := by
  have hnmem : (n : G) ∈ (K : Set G) * (X : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left K X hXK]
    exact n.2
  have hcomm : ∀ y ∈ X, ∃ c : ↥K, (c : G) = (n : G) * y * (n : G)⁻¹ * y⁻¹ ∧ uc22p22rPsi K c = 1 := by
    intro y hy
    obtain ⟨k₁, hk₁, x₁, hx₁, hnk⟩ := hnmem
    have hyk : y * k₁⁻¹ * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hXK hy) k₁⁻¹).1 (K.inv_mem hk₁)
    have hc : (n : G) * y * (n : G)⁻¹ * y⁻¹ = k₁ * (y * k₁⁻¹ * y⁻¹) := by
      rw [← hnk]
      have hx : x₁ * y = y * x₁ := hXc x₁ hx₁ y hy
      calc k₁ * x₁ * y * (k₁ * x₁)⁻¹ * y⁻¹ = k₁ * (x₁ * y) * x₁⁻¹ * k₁⁻¹ * y⁻¹ := by group
        _ = k₁ * (y * x₁) * x₁⁻¹ * k₁⁻¹ * y⁻¹ := by rw [hx]
        _ = k₁ * (y * k₁⁻¹ * y⁻¹) := by group
    have hcK : (n : G) * y * (n : G)⁻¹ * y⁻¹ ∈ K := by
      rw [hc]
      exact K.mul_mem hk₁ hyk
    have hyN : y ∈ K ⊔ X := Subgroup.mem_sup_right hy
    set y' : ↥(K ⊔ X) := ⟨y, hyN⟩ with hy'
    set c' : ↥(K ⊔ X) := n * y' * n⁻¹ * y'⁻¹ with hc'
    have hc'val : (c' : G) = (n : G) * y * (n : G)⁻¹ * y⁻¹ := rfl
    have hρ : uc22p22rRho K X hXK c' = 1 := by
      simp [hc', hn]
    refine ⟨⟨_, hcK⟩, rfl, ?_⟩
    have h1 : MulAut.conj (uc22p22rPsi K ⟨_, hcK⟩) = MulAut.conj (1 : uc22p22rKt K) := by
      rw [map_one, ← uc22p22rRho_incl hXK c' ⟨_, hcK⟩ hc'val]
      exact hρ
    exact uc22p22r_conj_injective hKq h1
  set Z0 : Subgroup G := (uc22p22rZK K).map K.subtype with hZ0
  have hZ0M : Z0 ≤ M := by
    rintro _ ⟨k, hk, rfl⟩
    exact hZ k (by rw [← MonoidHom.mem_ker, ← uc22p22rZK_eq_ker]; exact hk)
  have hYM : Z0 ⊔ X ≤ M := sup_le hZ0M hXM
  have hZ0n : ∀ z ∈ Z0, (n : G) * z * (n : G)⁻¹ ∈ Z0 := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨uc22p22rRho0 K X hXK n k, ?_, by simp [uc22p22rRho0_apply]⟩
    have hk' : uc22p22rPsi K k = 1 := by
      rw [uc22p22rZK_eq_ker] at hk
      exact MonoidHom.mem_ker.1 hk
    rw [uc22p22rZK_eq_ker]
    show uc22p22rPsi K (uc22p22rRho0 K X hXK n k) = 1
    rw [← uc22p22rRho_psi, hk', map_one]
  have hnY : (n : G) ∈ normalizer ((Z0 ⊔ X : Subgroup G) : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro y' hy'
    have hle : (Z0 ⊔ X).map (MulAut.conj (n : G)).toMonoidHom ≤ Z0 ⊔ X := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        exact Subgroup.mem_sup_left (hZ0n z hz)
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨c, hc, hcψ⟩ := hcomm y hy
        have hcZ : (c : G) ∈ Z0 := ⟨c, by rw [uc22p22rZK_eq_ker]; exact hcψ, rfl⟩
        have h : (MulAut.conj (n : G)).toMonoidHom y = (c : G) * y := by
          simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
          rw [hc]
          group
        rw [h]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcZ) (Subgroup.mem_sup_right hy)
    exact hle ⟨y', hy', rfl⟩
  exact h0 (Z0 ⊔ X) le_sup_right hYM n n.2 hnY

end Final

section Nontrivial

variable {K X : Subgroup G} (hXK : X ≤ normalizer (K : Set G))

theorem uc22p22rRho1_mk (n : ↥(K ⊔ X)) (k : ↥K) :
    uc22p22rRho1 K X hXK n (QuotientGroup.mk k : Bar2 K) =
      (QuotientGroup.mk (uc22p22rRho0 K X hXK n k) : Bar2 K) :=
  quotAutHom_mk _ _ _ n k

theorem uc22p22rRho_mk (n : ↥(K ⊔ X)) (k : Bar2 K) :
    uc22p22rRho K X hXK n (QuotientGroup.mk k : uc22p22rKt K) =
      (QuotientGroup.mk (uc22p22rRho1 K X hXK n k) : uc22p22rKt K) :=
  quotAutHom_mk _ _ _ n k

theorem uc22p22r_rho_ne_one {M : Subgroup G} {x : G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hX : X = Subgroup.zpowers x) (hxq : x ^ q = 1) (hKq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hO2 : pCoreOf 2 K ≤ M)
    (h0 : ∀ Y : Subgroup G, X ≤ Y → Y ≤ M → ∀ n ∈ K ⊔ X, n ∈ normalizer (Y : Set G) → n ∈ M)
    (hXM : X ≤ M) (hKM : ¬ K ≤ M) :
    uc22p22rRho K X hXK ⟨x, Subgroup.mem_sup_right (hX ▸ Subgroup.mem_zpowers x)⟩ ≠ 1 := by
  intro h1
  apply hKM
  have hxX : x ∈ X := hX ▸ Subgroup.mem_zpowers x
  have hxK : x ∈ normalizer (K : Set G) := hXK hxX
  set nx : ↥(K ⊔ X) := ⟨x, Subgroup.mem_sup_right hxX⟩ with hnx
  have hα : ∀ k : Bar2 K, uc22p22rRho1 K X hXK nx k * k⁻¹ ∈ Subgroup.center (Bar2 K) := by
    intro k
    have h2 : uc22p22rRho K X hXK nx (QuotientGroup.mk k : uc22p22rKt K) =
        (QuotientGroup.mk k : uc22p22rKt K) := by
      rw [h1]
      rfl
    rw [uc22p22rRho_mk] at h2
    have h3 := QuotientGroup.eq.1 h2
    have hz := Subgroup.inv_mem _ h3
    have hc := Subgroup.mem_center_iff.1 hz (uc22p22rRho1 K X hXK nx k)
    have e : uc22p22rRho1 K X hXK nx k * k⁻¹ =
        (uc22p22rRho1 K X hXK nx k) * ((uc22p22rRho1 K X hXK nx k)⁻¹ * k)⁻¹ *
          (uc22p22rRho1 K X hXK nx k)⁻¹ := by group
    rw [e, hc]
    simpa using hz
  have hα1 : uc22p22rRho1 K X hXK nx = 1 := CFSG.Goldschmidt.N8f (Bar2 K) hKq _ hα
  have htriv : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
    intro k hk
    have h2 := DFunLike.congr_fun hα1 (QuotientGroup.mk ⟨k, hk⟩ : Bar2 K)
    rw [uc22p22rRho1_mk] at h2
    have h3 := QuotientGroup.eq.1 (show (QuotientGroup.mk (uc22p22rRho0 K X hXK nx ⟨k, hk⟩) : Bar2 K) =
      QuotientGroup.mk ⟨k, hk⟩ from h2)
    have h4 : (x * k * x⁻¹)⁻¹ * k ∈ pCoreOf 2 K := by
      have h5 : (((uc22p22rRho0 K X hXK nx ⟨k, hk⟩)⁻¹ * ⟨k, hk⟩ : ↥K)) ∈ CFSG.pCore 2 ↥K := h3
      have h6 : ((((uc22p22rRho0 K X hXK nx ⟨k, hk⟩)⁻¹ * ⟨k, hk⟩ : ↥K)) : G) ∈ pCoreOf 2 K :=
        ⟨_, h5, rfl⟩
      have e : ((((uc22p22rRho0 K X hXK nx ⟨k, hk⟩)⁻¹ * ⟨k, hk⟩ : ↥K)) : G) = (x * k * x⁻¹)⁻¹ * k := by
        simp [uc22p22rRho0_apply, hnx]
      rw [e] at h6
      exact h6
    have h7 := uc22p22f_conj_mem_pCoreOf_self hk ((pCoreOf 2 K).inv_mem h4)
    have e : k * ((x * k * x⁻¹)⁻¹ * k)⁻¹ * k⁻¹ = x * k * x⁻¹ * k⁻¹ := by group
    rwa [e] at h7
  have hC : ∀ k ∈ K, x * k * x⁻¹ = k → k ∈ M := by
    intro k hk hcomm
    have hkc : ∀ a ∈ X, k * a * k⁻¹ = a := by
      intro a ha
      rw [hX] at ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      have hc : Commute k x := by
        have : x * k = k * x := by
          calc x * k = (x * k * x⁻¹) * x := by group
            _ = k * x := by rw [hcomm]
        exact this.symm
      exact (hc.zpow_right i).eq ▸ by group
    have hkN : k ∈ normalizer (X : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        rw [hkc a ha]
        exact ha
      · intro ha
        have h2 : k * (k * a * k⁻¹) * k⁻¹ = k * a * k⁻¹ := hkc _ ha
        have h3 : a = k * a * k⁻¹ := by
          calc a = k⁻¹ * (k * a * k⁻¹) * k := by group
            _ = k⁻¹ * (k * (k * a * k⁻¹) * k⁻¹) * k := by rw [h2]
            _ = k * a * k⁻¹ := by group
        rw [h3]
        exact ha
    exact h0 X le_rfl hXM k (Subgroup.mem_sup_left hk) hkN
  exact uc22p22r_le_of_trivial_action hq hq2 hxq hxK htriv hC hO2

end Nontrivial

section Last

variable {K X : Subgroup G} (hXK : X ≤ normalizer (K : Set G))

theorem uc22p22r_img_mono {A B : Subgroup G} (h : A ≤ B) : uc22p22rImg hXK A ≤ uc22p22rImg hXK B :=
  Subgroup.map_mono fun n hn => h hn

theorem uc22p22r_sylow_img {T' : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hXq : Nat.card X = q)
    (hT' : CFSG.ABGLocalTools.IsSylowOf 2 T' K) :
    CFSG.ABGLocalTools.IsSylowOf 2 (uc22p22rImg hXK T') ⊤ := by
  have hT'K := hT'.le
  have hKN : K ≤ K ⊔ X := le_sup_left
  haveI : (K.subgroupOf (K ⊔ X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).2 (uc22p22r_sup_le_normalizer hXK)
  have hsurj : Function.Surjective ((QuotientGroup.mk' (K.subgroupOf (K ⊔ X))).comp
      (Subgroup.inclusion (le_sup_right : X ≤ K ⊔ X))) := by
    intro c
    obtain ⟨⟨n, hn⟩, rfl⟩ := QuotientGroup.mk'_surjective _ c
    have hnmem : n ∈ (K : Set G) * (X : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K X hXK]
      exact hn
    obtain ⟨k, hk, x₁, hx₁, rfl⟩ := hnmem
    refine ⟨⟨x₁, hx₁⟩, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := (Subgroup.mem_normalizer_iff.1 (hXK (Subgroup.inv_mem _ hx₁)) k).1 hk
    simpa [mul_assoc] using h
  have hdvd : Nat.card (↥(K ⊔ X) ⧸ K.subgroupOf (K ⊔ X)) ∣ Nat.card ↥X :=
    Subgroup.card_dvd_of_surjective hsurj
  have hodd2 : ¬ 2 ∣ K.relIndex (K ⊔ X) := by
    intro h2
    have h3 : K.relIndex (K ⊔ X) = Nat.card (↥(K ⊔ X) ⧸ K.subgroupOf (K ⊔ X)) := by
      rw [Subgroup.relIndex, Subgroup.index_eq_card]
    rw [h3] at h2
    have h4 := h2.trans hdvd
    rw [hXq] at h4
    exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 h4).symm
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T'.subgroupOf (K ⊔ X)) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hT'.isPGroup.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    have h1 : (T'.subgroupOf (K ⊔ X)).index = T'.relIndex (K ⊔ X) := rfl
    rw [h1, ← Subgroup.relIndex_mul_relIndex T' K (K ⊔ X) hT'K hKN]
    have hodd1 : ¬ 2 ∣ T'.relIndex K := (CFSG.ABGLocalTools.isSylowOf_iff.1 hT').2.2
    intro hdvd'
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hdvd' with h | h
    · exact hodd1 h
    · exact hodd2 h
  exact uc22p22r_isSylowOf_map_top (uc22p22rPi_surjective hXK) hSyl

end Last

section Closing

variable {K X : Subgroup G} (hXK : X ≤ normalizer (K : Set G))

theorem uc22p22r_permutes_img {T' : Subgroup G} (hT'K : T' ≤ K) (hperm : Permutes X T') :
    Permutes (uc22p22rImg hXK X) (uc22p22rImg hXK T') := by
  unfold Permutes at hperm ⊢
  have hXN : X ≤ K ⊔ X := le_sup_right
  have hTN : T' ≤ K ⊔ X := hT'K.trans le_sup_left
  ext z
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨n₁, hn₁, rfl⟩ := (uc22p22r_mem_img hXK).1 ha
    obtain ⟨n₂, hn₂, rfl⟩ := (uc22p22r_mem_img hXK).1 hb
    have hmem : (n₁ : G) * (n₂ : G) ∈ (T' : Set G) * (X : Set G) := by
      rw [← hperm]
      exact ⟨n₁, hn₁, n₂, hn₂, rfl⟩
    obtain ⟨t, ht, y, hy, hty⟩ := hmem
    refine ⟨uc22p22rPi K X hXK ⟨t, hTN ht⟩, (uc22p22r_mem_img hXK).2 ⟨_, ht, rfl⟩,
      uc22p22rPi K X hXK ⟨y, hXN hy⟩, (uc22p22r_mem_img hXK).2 ⟨_, hy, rfl⟩, ?_⟩
    beta_reduce
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hty)
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨n₁, hn₁, rfl⟩ := (uc22p22r_mem_img hXK).1 ha
    obtain ⟨n₂, hn₂, rfl⟩ := (uc22p22r_mem_img hXK).1 hb
    have hmem : (n₁ : G) * (n₂ : G) ∈ (X : Set G) * (T' : Set G) := by
      rw [hperm]
      exact ⟨n₁, hn₁, n₂, hn₂, rfl⟩
    obtain ⟨y, hy, t, ht, hyt⟩ := hmem
    refine ⟨uc22p22rPi K X hXK ⟨y, hXN hy⟩, (uc22p22r_mem_img hXK).2 ⟨_, hy, rfl⟩,
      uc22p22rPi K X hXK ⟨t, hTN ht⟩, (uc22p22r_mem_img hXK).2 ⟨_, ht, rfl⟩, ?_⟩
    beta_reduce
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hyt)

end Closing

end CFSG.LocalAnalysis.UniquenessCase.UC22
