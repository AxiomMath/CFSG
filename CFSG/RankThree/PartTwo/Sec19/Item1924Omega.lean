module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.RankThree.PartTwo.Sec18.Item189K0Generic
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
import CFSG.RankThree.PartTwo.Sec19.Item1924Fusion

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem item1924Omega_inv_conj_mem_iff {H : Subgroup G} {k : G}
    (h : ∀ x ∈ H, k⁻¹ * x * k ∈ H) (w : G) : k⁻¹ * w * k ∈ H ↔ w ∈ H := by
  refine ⟨fun hw => ?_, fun hw => h w hw⟩
  have hle : H.map (MulAut.conj k⁻¹).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using h x hx
  have hcard : Nat.card (H.map (MulAut.conj k⁻¹).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
  have heq : H.map (MulAut.conj k⁻¹).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hw' : k⁻¹ * w * k ∈ H.map (MulAut.conj k⁻¹).toMonoidHom := by
    rw [heq]
    exact hw
  obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.mp hw'
  have h2 : k⁻¹ * x * k = k⁻¹ * w * k := by
    rw [← hxw]
    simp [MulAut.conj_apply]
  have hxw' : x = w := mul_left_cancel (mul_right_cancel h2)
  rw [← hxw']
  exact hx

private theorem item1924Omega_mem_normalizer {H : Subgroup G} {n : G}
    (h : ∀ x ∈ H, n⁻¹ * x * n ∈ H) : n ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff'']
  exact fun w => (item1924Omega_inv_conj_mem_iff h w).symm

private theorem item1924Omega_conj_mem (hA : IsE27 A) {P₀ : Subgroup G}
    (hP₀ : IsSylowOf 3 P₀ M) (hΩ : ∀ y ∈ P₀, y ^ 3 = 1 → y ∈ A)
    (hPM : ∀ Q : Subgroup G, IsPGroup 3 Q → A ≤ Q → Q ≤ M)
    (hNA : Subgroup.normalizer (A : Set G) ≤ M) (hMK : M ≤ Subgroup.normalizer (K : Set G))
    {x g : G} (hxA : x ∈ A) (hxK : x ∈ K) (hx3 : x ^ 3 = 1) (hg : g * x * g⁻¹ ∈ P₀) :
    g * x * g⁻¹ ∈ A ⊓ K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcube : ∀ a ∈ A, a ^ 3 = 1 := fun a ha => hA.1.2 a ha
  have hgx3 : (g * x * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hyA : g * x * g⁻¹ ∈ A := hΩ _ hg hgx3
  have hmemC : ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) ↔ x * z = z * x := by
    intro z
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hz
      exact hz x (Set.mem_singleton x)
    · intro hz y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact hz
  have hAC : A ≤ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    rw [hmemC]
    exact hcomm x hxA a ha
  have hA'C : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer ({x} : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hmemC]
    have hconj : (MulAut.conj g⁻¹).toMonoidHom a = g⁻¹ * a * g := by
      simp [MulAut.conj_apply]
    rw [hconj]
    have e1 : x * (g⁻¹ * a * g) = g⁻¹ * (g * x * g⁻¹ * a) * g := by group
    have e2 : g⁻¹ * a * g * x = g⁻¹ * (a * (g * x * g⁻¹)) * g := by group
    rw [e1, e2, hcomm _ hyA a ha]
  obtain ⟨P₁, hP₁, hAP₁⟩ := Sec18.exists_isSylowOf_ge hA.isPGroup hAC
  obtain ⟨P', hP', hA'P'⟩ :=
    Sec18.exists_isSylowOf_ge (hA.isPGroup.map (MulAut.conj g⁻¹).toMonoidHom) hA'C
  obtain ⟨k, hkC, hk⟩ := hP₁.exists_mem_conj hP'
  have hkx : x * k = k * x := (hmemC k).mp hkC
  have hP₁M : P₁ ≤ M := hPM P₁ hP₁.isPGroup hAP₁
  obtain ⟨P₂, hP₂, hP₁P₂⟩ := Sec18.exists_isSylowOf_ge hP₁.isPGroup hP₁M
  have hAP₂ : A ≤ P₂ := hAP₁.trans hP₁P₂
  have hΩ₂ : ∀ z ∈ P₂, z ^ 3 = 1 → z ∈ A := by
    obtain ⟨m, -, hm⟩ := hP₀.exists_mem_conj hP₂
    have hmA : ∀ a ∈ A, m⁻¹ * a * m ∈ A := fun a ha =>
      hΩ _ ((hm a).mp (hAP₂ ha)) (item1924_cube_conj m a (hcube a ha))
    intro z hz hz3
    exact (item1924Omega_inv_conj_mem_iff hmA z).mp
      (hΩ _ ((hm z).mp hz) (item1924_cube_conj m z hz3))
  have hn : ∀ a ∈ A, (g * k)⁻¹ * a * (g * k) ∈ P₂ := by
    intro a ha
    have h1 : g⁻¹ * a * g ∈ A.map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a, ha, by simp [MulAut.conj_apply]⟩
    have h2 : k⁻¹ * (g⁻¹ * a * g) * k ∈ P₁ := (hk _).mp (hA'P' h1)
    have e : (g * k)⁻¹ * a * (g * k) = k⁻¹ * (g⁻¹ * a * g) * k := by group
    rw [e]
    exact hP₁P₂ h2
  have hnN : g * k ∈ Subgroup.normalizer (A : Set G) :=
    item1924Omega_mem_normalizer fun a ha =>
      hΩ₂ _ (hn a ha) (item1924_cube_conj _ a (hcube a ha))
  have hnK : g * k ∈ Subgroup.normalizer (K : Set G) := hMK (hNA hnN)
  have hxK' : g * k * x * (g * k)⁻¹ ∈ K := (Subgroup.mem_set_normalizer_iff.mp hnK x).mp hxK
  have hkx' : k * x * k⁻¹ = x := by
    rw [← hkx, mul_inv_cancel_right]
  have hconj_eq : g * k * x * (g * k)⁻¹ = g * x * g⁻¹ := by
    calc g * k * x * (g * k)⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [hkx']
  refine Subgroup.mem_inf.mpr ⟨hyA, ?_⟩
  rw [← hconj_eq]
  exact hxK'

private theorem item1924Omega_zpowers_conj (hA : IsE27 A) {P₀ : Subgroup G}
    (hP₀ : IsSylowOf 3 P₀ M) (hΩ : ∀ y ∈ P₀, y ^ 3 = 1 → y ∈ A)
    (hPM : ∀ Q : Subgroup G, IsPGroup 3 Q → A ≤ Q → Q ≤ M)
    (hNA : Subgroup.normalizer (A : Set G) ≤ M) (hMK : M ≤ Subgroup.normalizer (K : Set G))
    (hAK : A ⊓ K = Subgroup.zpowers c) (hc3 : c ^ 3 = 1) (hcK : c ∈ K)
    {P : Subgroup G} (hP : IsSylowOf 3 P M) (hcP : c ∈ P) {g : G} (hgc : g * c * g⁻¹ ∈ P) :
    Subgroup.zpowers (g * c * g⁻¹) = Subgroup.zpowers c := by
  obtain ⟨m, hmM, hm⟩ := hP₀.exists_mem_conj hP
  have hmK : m ∈ Subgroup.normalizer (K : Set G) := hMK hmM
  have hc₀K : m⁻¹ * c * m ∈ K := (Subgroup.mem_set_normalizer_iff''.mp hmK c).mp hcK
  have hc₀3 : (m⁻¹ * c * m) ^ 3 = 1 := item1924_cube_conj m c hc3
  have hc₀A : m⁻¹ * c * m ∈ A := hΩ _ ((hm c).mp hcP) hc₀3
  have hc₀Z : m⁻¹ * c * m ∈ Subgroup.zpowers c := by
    rw [← hAK]
    exact Subgroup.mem_inf.mpr ⟨hc₀A, hc₀K⟩
  have hord : orderOf (m⁻¹ * c * m) = orderOf c := by
    have h := item1924_orderOf_conj m⁻¹ c
    rwa [inv_inv] at h
  have hzc : Subgroup.zpowers (m⁻¹ * c * m) = Subgroup.zpowers c :=
    item1924_zpowers_eq_of_mem hc₀Z hord
  have hg0 : m⁻¹ * g * m * (m⁻¹ * c * m) * (m⁻¹ * g * m)⁻¹ = m⁻¹ * (g * c * g⁻¹) * m := by
    group
  have hgP₀ : m⁻¹ * g * m * (m⁻¹ * c * m) * (m⁻¹ * g * m)⁻¹ ∈ P₀ := by
    rw [hg0]
    exact (hm _).mp hgc
  have hcore := item1924Omega_conj_mem hA hP₀ hΩ hPM hNA hMK hc₀A hc₀K hc₀3 hgP₀
  rw [hg0, hAK] at hcore
  have hd : m⁻¹ * (g * c * g⁻¹) * m ∈ Subgroup.zpowers (m⁻¹ * c * m) := by
    rw [hzc]
    exact hcore
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hd
  have hdc : g * c * g⁻¹ = c ^ j := by
    calc g * c * g⁻¹ = m * (m⁻¹ * (g * c * g⁻¹) * m) * m⁻¹ := by group
      _ = m * (m⁻¹ * c * m) ^ j * m⁻¹ := by rw [hj]
      _ = (m * (m⁻¹ * c * m) * m⁻¹) ^ j := by rw [conj_zpow]
      _ = c ^ j := by rw [show m * (m⁻¹ * c * m) * m⁻¹ = c by group]
  exact item1924_zpowers_eq_of_mem (Subgroup.mem_zpowers_iff.mpr ⟨j, hdc.symm⟩)
    (item1924_orderOf_conj g c)

theorem item1924_of_omega (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hcK : c ∈ K) (hAK : A ⊓ K = Subgroup.zpowers c)
    (hKM : M ≤ Subgroup.normalizer (K : Set G))
    {P₀ : Subgroup G} (hP₀ : IsSylowOf 3 P₀ M) (hAP : A ≤ P₀)
    (hΩ : Sec18.omegaOneThree P₀ = A) :
    ∀ P : Subgroup G, IsSylowOf 3 P M → c ∈ P →
      Sec18.conjugatesIn (Subgroup.zpowers c) P = {Subgroup.zpowers c} := by
  intro P hP hcP
  have hA : IsE27 A := h.isE27
  have hΩ' : ∀ y ∈ P₀, y ^ 3 = 1 → y ∈ A := fun y hy hy3 => by
    rw [← hΩ]
    exact Subgroup.subset_closure (show y ∈ {x | x ∈ P₀ ∧ x ^ 3 = 1} from ⟨hy, hy3⟩)
  have hPM : ∀ Q : Subgroup G, IsPGroup 3 Q → A ≤ Q → Q ≤ M :=
    fun Q hQ hAQ => le_of_isPGroup_of_le h.hyp191 hA h.mem_scriptM hQ hAQ
  have hk2 : (2 : ℕ) ≤ CFSG.Open.pRank 3 A := by
    rw [hA.pRank_eq]
    norm_num
  have hNA : Subgroup.normalizer (A : Set G) ≤ M :=
    (normalizer_le_gamma le_rfl hk2).trans h.mem_scriptM.2
  have hc3 : c ^ 3 = 1 := by
    have h3 := pow_orderOf_eq_one c
    rwa [hF.orderOf_c] at h3
  ext F'
  rw [Set.mem_singleton_iff, Sec18.mem_conjugatesIn_iff]
  constructor
  · rintro ⟨⟨g, rfl⟩, hle⟩
    rw [MonoidHom.map_zpowers] at hle ⊢
    have hgc : g * c * g⁻¹ ∈ P := Subgroup.zpowers_le.mp hle
    exact item1924Omega_zpowers_conj hA hP₀ hΩ' hPM hNA hKM hAK hc3 hcK hP hcP hgc
  · rintro rfl
    refine ⟨⟨1, ?_⟩, Subgroup.zpowers_le.mpr hcP⟩
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]

end CFSG.RankThree.PartTwo.Late
