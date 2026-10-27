module

public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Late.Defs
public import CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset
public import CFSG.GroupTheory.WielandtProductBasic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem isPGroup_zpowers_of_cube_eq_one {a : G} (ha : a ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers a) := by
  have hcard : Nat.card ↥(Subgroup.zpowers a) = orderOf a := Nat.card_zpowers a
  have hdvd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [hcard, h]; simp)
  · exact IsPGroup.of_card (n := 1) (by rw [hcard, h]; simp)

@[expose] def conjTrivialOnQuotient (K O : Subgroup G) (hOK : O ≤ K) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (K : Set G) ∧
    ∀ x ∈ K, g * x * g⁻¹ * x⁻¹ ∈ O}
  one_mem' := ⟨Subgroup.one_mem _, by intro x _; simp⟩
  mul_mem' := by
    rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
    refine ⟨Subgroup.mul_mem _ hgN hhN, fun x hx => ?_⟩
    have hcx : h * x * h⁻¹ * x⁻¹ ∈ O := hh x hx
    have hgconj : g * (h * x * h⁻¹ * x⁻¹) * g⁻¹ ∈ O := by
      have heq : g * (h * x * h⁻¹ * x⁻¹) * g⁻¹ =
          (g * (h * x * h⁻¹ * x⁻¹) * g⁻¹ * (h * x * h⁻¹ * x⁻¹)⁻¹) *
            (h * x * h⁻¹ * x⁻¹) := by group
      rw [heq]
      exact O.mul_mem (hg _ (hOK hcx)) hcx
    have heq : (g * h) * x * (g * h)⁻¹ * x⁻¹ =
        (g * (h * x * h⁻¹ * x⁻¹) * g⁻¹) * (g * x * g⁻¹ * x⁻¹) := by group
    rw [heq]
    exact O.mul_mem hgconj (hg x hx)
  inv_mem' := by
    rintro g ⟨hgN, hg⟩
    refine ⟨Subgroup.inv_mem _ hgN, fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ K := by
      refine ((Subgroup.mem_normalizer_iff.mp hgN) (g⁻¹ * x * g)).mpr ?_
      have hconv : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [hconv]
      exact hx
    have h1 : g * (g⁻¹ * x * g) * g⁻¹ * (g⁻¹ * x * g)⁻¹ = (g⁻¹ * x * g * x⁻¹)⁻¹ := by
      group
    have h2 := hg (g⁻¹ * x * g) hx'
    rw [h1] at h2
    simpa using O.inv_mem h2

theorem mem_conjTrivialOnQuotient_iff {K O : Subgroup G} {hOK : O ≤ K} {g : G} :
    g ∈ conjTrivialOnQuotient K O hOK ↔
      g ∈ Subgroup.normalizer (K : Set G) ∧
        ∀ x ∈ K, g * x * g⁻¹ * x⁻¹ ∈ O :=
  Iff.rfl

theorem conj_mem_of_mem_conjTrivialOnQuotient {K O : Subgroup G} {hOK : O ≤ K} {g : G}
    (hg : g ∈ conjTrivialOnQuotient K O hOK) {y : G} (hy : y ∈ O) :
    g * y * g⁻¹ ∈ O := by
  have hg' := (mem_conjTrivialOnQuotient_iff.mp hg).2
  have heq : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
  rw [heq]
  exact O.mul_mem (hg' y (hOK hy)) hy

@[expose] noncomputable def conjAutK (K A : Subgroup G)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) : ↥A →* MulAut ↥K :=
  (Subgroup.normalizerMonoidHom (H := K)).comp (Subgroup.inclusion hAK)

theorem conjAutK_apply_coe (K A : Subgroup G) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (a : ↥A) (x : ↥K) :
    ((conjAutK K A hAK a) x : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
  rw [conjAutK, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.coe_inclusion]

variable [Finite G]

theorem not_three_dvd_card_inf_pPrimeCoreOf (K Q : Subgroup G) :
    ¬ 3 ∣ Nat.card ↥(pPrimeCoreOf 3 K ⊓ Q) := by
  have hnot : ¬ 3 ∣ Nat.card ↥(pPrimeCoreOf 3 K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  intro h3
  exact hnot (h3.trans (Subgroup.card_dvd_of_le inf_le_left))

theorem exists_fixed_mul_inv_mem_pPrimeCoreOf {K Q : Subgroup G} {a : G}
    (haQ : a ∈ Subgroup.normalizer (Q : Set G)) (hQK : Q ≤ K) (ha3 : a ^ 3 = 1)
    (hcent : ∀ x ∈ K, a * x * a⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 K) {x : G} (hx : x ∈ Q) :
    ∃ y ∈ Q, y * x⁻¹ ∈ pPrimeCoreOf 3 K ∧ a * y * a⁻¹ = y := by
  classical
  let O : Subgroup G := pPrimeCoreOf 3 K
  have hOK : O ≤ K := pPrimeCoreOf_le 3 K
  have haK : a ∈ Subgroup.normalizer (K : Set G) :=
    CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem fun y hy => by
      rw [show a * y * a⁻¹ = (a * y * a⁻¹ * y⁻¹) * y by group]
      exact K.mul_mem (hOK (hcent y hy)) hy
  have hB_le : Subgroup.zpowers a ≤ conjTrivialOnQuotient K O hOK :=
    Subgroup.zpowers_le.mpr ((mem_conjTrivialOnQuotient_iff (hOK := hOK)).mpr ⟨haK, hcent⟩)
  let ρ : ↥(Subgroup.zpowers a) →* MulAut ↥Q :=
    conjAutK Q (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haQ)
  have hρ_apply : ∀ (b : ↥(Subgroup.zpowers a)) (y : ↥Q),
      ((ρ b) y : G) = (b : G) * (y : G) * (b : G)⁻¹ :=
    conjAutK_apply_coe Q (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haQ)
  have hBp : IsPGroup 3 ↥(Subgroup.zpowers a) := isPGroup_zpowers_of_cube_eq_one ha3
  have hRnorm : (O.subgroupOf Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hQK.trans (le_normalizer_pPrimeCoreOf 3 K))
  have hRrho : ∀ (b : ↥(Subgroup.zpowers a)), ∀ r ∈ O.subgroupOf Q,
      ρ b r ∈ O.subgroupOf Q := by
    intro b r hr
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    rw [hρ_apply b r]
    exact conj_mem_of_mem_conjTrivialOnQuotient (hB_le b.2) hr
  have hp : ¬ 3 ∣ Nat.card ↥(O.subgroupOf Q) := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective Q),
      Subgroup.subgroupOf_map_subtype]
    exact not_three_dvd_card_inf_pPrimeCoreOf K Q
  have hxρ : ∀ b : ↥(Subgroup.zpowers a),
      ρ b ⟨x, hx⟩ * ⟨x, hx⟩⁻¹ ∈ O.subgroupOf Q := by
    intro b
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hρ_apply]
    exact (mem_conjTrivialOnQuotient_iff.mp (hB_le b.2)).2 x (hQK hx)
  obtain ⟨y, hyx, hfix⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset.exists_fixed
      (p := 3) hBp ρ (O.subgroupOf Q) hRnorm hRrho hp ⟨x, hx⟩ hxρ
  refine ⟨y.1, y.2, by simpa using Subgroup.mem_subgroupOf.mp hyx, ?_⟩
  have hfixa := congrArg Subtype.val (hfix ⟨a, Subgroup.mem_zpowers a⟩)
  rwa [hρ_apply] at hfixa

theorem le_inf_centralizer_sup_pPrimeCoreOf {A K Q : Subgroup G} {LB : Subgroup G → Subgroup G}
    {a : G} (ha : a ∈ A) (ha3 : a ^ 3 = 1)
    (hcent : ∀ x ∈ K, a * x * a⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 K)
    (hQ : Q ∈ collectionIn (scriptQ A LB) K) :
    Q ≤ (Q ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ pPrimeCoreOf 3 K := by
  intro x hxQ
  obtain ⟨y, hyQ, hyx, hfixa⟩ :=
    exists_fixed_mul_inv_mem_pPrimeCoreOf ((mem_scriptQ_iff.mp hQ.1).2.1 ha) hQ.2 ha3 hcent hxQ
  have hya : y ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : a * y = y * a := by
      calc a * y = (a * y * a⁻¹) * a := by group
        _ = y * a := by rw [hfixa]
    exact h1.symm
  have hx_eq : x = (y * x⁻¹)⁻¹ * y := by group
  rw [hx_eq]
  exact ((Q ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ pPrimeCoreOf 3 K).mul_mem
    (Subgroup.mem_sup_right ((pPrimeCoreOf 3 K).inv_mem hyx))
    (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hyQ, hya⟩))

theorem exists_le_delta_cover {A K : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A) (hKΔ : K = delta A LB K) {a : G} (ha : a ∈ A)
    (hcent : ∀ x ∈ K, a * x * a⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 K) :
    ∃ D : Subgroup G, D ≤ K ∧ D ≤ delta A LB (Subgroup.centralizer ({a} : Set G)) ∧
      K ≤ D ⊔ pPrimeCoreOf 3 K := by
  classical
  let O : Subgroup G := pPrimeCoreOf 3 K
  let C : Subgroup G := Subgroup.centralizer ({a} : Set G)
  let 𝒬 : Set (Subgroup G) := collectionIn (scriptQ A LB) K
  let D : Subgroup G := sSup ((fun Q : Subgroup G => Q ⊓ C) '' 𝒬)
  have hAC : A ≤ C := fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val ((hA.1.1.is_comm).comm ⟨b, hb⟩ ⟨a, ha⟩))
  have hAnormC : A ≤ Subgroup.normalizer (C : Set G) := hAC.trans Subgroup.le_normalizer
  refine ⟨D, ?_, ?_, ?_⟩
  ·
    refine sSup_le ?_
    rintro X ⟨Q, hQ, rfl⟩
    exact inf_le_left.trans hQ.2
  ·
    refine sSup_le ?_
    rintro X ⟨Q, hQ, rfl⟩
    have hQscript : Q ∈ scriptQ A LB := hQ.1
    have hAnormQ : A ≤ Subgroup.normalizer (Q : Set G) := (mem_scriptQ_iff.mp hQscript).2.1
    have hAnorm : A ≤ Subgroup.normalizer ((Q ⊓ C : Subgroup G) : Set G) := by
      intro b hb
      exact Subgroup.inf_normalizer_le_normalizer_inf
        (Subgroup.mem_inf.mpr ⟨hAnormQ hb, hAnormC hb⟩)
    exact le_delta (mem_scriptQ_of_le hQscript inf_le_left hAnorm) inf_le_right
  ·
    conv_lhs => rw [hKΔ, delta]
    refine sSup_le ?_
    rintro Q hQ
    refine (le_inf_centralizer_sup_pPrimeCoreOf ha (hA.1.2 a ha) hcent hQ).trans
      (sup_le_sup_right ?_ O)
    exact le_sSup ⟨Q, hQ, rfl⟩

omit [Finite G] in
theorem exists_surj_of_le_sup {K D : Subgroup G} (hDK : D ≤ K)
    (hKD : K ≤ D ⊔ pPrimeCoreOf 3 K) {S : Type} [Group S]
    (φ : ↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* S) :
    ∃ f : ↥D →* S, Function.Surjective f := by
  classical
  let N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let O : Subgroup G := pPrimeCoreOf 3 K
  have hON : O = N.map K.subtype := rfl
  have hOK : O ≤ K := pPrimeCoreOf_le 3 K
  let f : ↥D →* S :=
    φ.toMonoidHom.comp ((QuotientGroup.mk' N).comp (Subgroup.inclusion hDK))
  refine ⟨f, ?_⟩
  intro s
  obtain ⟨q, rfl⟩ := φ.surjective s
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N q
  have hOsub : O.subgroupOf K = N := by
    ext x
    rw [Subgroup.mem_subgroupOf, hON, Subgroup.mem_map]
    constructor
    · rintro ⟨n, hn, hnx⟩
      rwa [← Subtype.ext hnx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hk : k ∈ D.subgroupOf K ⊔ N := by
    have h1 : k ∈ (D ⊔ O).subgroupOf K := Subgroup.mem_subgroupOf.mpr (hKD k.2)
    rwa [Subgroup.subgroupOf_sup hDK hOK, hOsub] at h1
  obtain ⟨d, hd, n, hn, hdn⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := D.subgroupOf K) (t := N)).mp hk
  have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
  refine ⟨⟨(d : G), hdD⟩, ?_⟩
  have hinc : (Subgroup.inclusion hDK ⟨(d : G), hdD⟩ : ↥K) = d := by
    apply Subtype.ext
    rw [Subgroup.coe_inclusion]
  have hmk : QuotientGroup.mk' N k = QuotientGroup.mk' N d := by
    rw [← hdn, map_mul,
      show QuotientGroup.mk' N n = 1 from (QuotientGroup.eq_one_iff n).mpr hn, mul_one]
  have hf : f ⟨(d : G), hdD⟩ = φ.toMonoidHom (QuotientGroup.mk' N d) := by
    simp only [f, MonoidHom.comp_apply, hinc]
  rw [hf, hmk, MulEquiv.coe_toMonoidHom]

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1
