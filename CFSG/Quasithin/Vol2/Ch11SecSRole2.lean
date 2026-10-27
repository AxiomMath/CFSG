module

public import CFSG.Quasithin.Vol2.Ch11SecSFacts4
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT5
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_mk {J A : Subgroup G} (hAJ : A ≤ J) (hO : pCoreOf 2 J ≤ A) {x : G}
    (hx : x ∈ J) (h : QuotientGroup.mk' (CFSG.pCore 2 ↥J) ⟨x, hx⟩ ∈
      Subgroup.normalizer (modO2Image J A : Set (↥J ⧸ CFSG.pCore 2 ↥J))) :
    x ∈ Subgroup.normalizer (A : Set G) := by
  have hpre := map_comap_modO2Image hAJ
  rw [sup_eq_left.mpr hO] at hpre
  have key : ∀ y : G, ∀ hy : y ∈ J, QuotientGroup.mk' (CFSG.pCore 2 ↥J) ⟨y, hy⟩ ∈
      Subgroup.normalizer (modO2Image J A : Set (↥J ⧸ CFSG.pCore 2 ↥J)) →
        ∀ a ∈ A, y * a * y⁻¹ ∈ A := by
    intro y hy hyN a ha
    have hya : y * a * y⁻¹ ∈ J := J.mul_mem (J.mul_mem hy (hAJ ha)) (J.inv_mem hy)
    have hm : QuotientGroup.mk' (CFSG.pCore 2 ↥J) ⟨y * a * y⁻¹, hya⟩ ∈ modO2Image J A := by
      have h1 := (Subgroup.mem_normalizer_iff.mp hyN _).mp ⟨⟨a, hAJ ha⟩, ha, rfl⟩
      convert h1 using 1
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [← hpre]
    exact ⟨⟨y * a * y⁻¹, hya⟩, hm, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨key x hx h a, fun ha => ?_⟩
  have h1 := key x⁻¹ (J.inv_mem hx) (by
    have := Subgroup.inv_mem _ h
    convert this using 1
    rw [← map_inv]
    rfl) _ ha
  simpa [mul_assoc] using h1

theorem exists_card_eq_mul {J A : Subgroup G} (hAJ : A ≤ J) :
    ∃ t : ℕ, Nat.card ↥A = Nat.card ↥(modO2Image J A) * 2 ^ t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := (QuotientGroup.mk' (CFSG.pCore 2 ↥J)).comp (A.subgroupOf J).subtype with hφ
  have h1 : modO2Image J A = φ.range := by
    unfold modO2Image
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hp : IsPGroup 2 ↥φ.ker := by
    intro k
    have hk : ((k : ↥(A.subgroupOf J)) : ↥J) ∈ CFSG.pCore 2 ↥J := by
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥J) ((k : ↥(A.subgroupOf J)) : ↥J) = 1 := k.2
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) ⟨_, hk⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp hp
  refine ⟨t, ?_⟩
  rw [h1, ← ht, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv).symm

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem isCartanX_J (hB : FactBorelShape) (hLevi : FactL34Levi) (hT : FactPGL34Torus)
    (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) (hP : ParData T K (LOf L V₁) P₁ P₂) {J I' : Subgroup G}
    (hJ : Hyp11 G T J I' 2) (hK₀J : k0Of K P₂ ≤ J) (hL₂J : LOf L V₂ ≤ J) (hXJ : X ≤ J)
    (hn : ¬ IsPSL 3 2 2 (↥J ⧸ CFSG.pCore 2 ↥J)) : IsCartanX T J X := by
  have hTJ := hJ.normal
  have hD := h.inspData_k0Of hLevi hT hN h1102 cL hP hTJ hK₀J hL₂J hXJ
  obtain ⟨hNS, hcardS⟩ := hB _ hJ.shape hn _ hD.syl _ _ hD.ne ⟨hD.ne₁, hD.p₁, hD.n₁, hD.sl₁⟩
    ⟨hD.ne₂, hD.p₂, hD.n₂, hD.sl₂⟩
  have hSI : QuasithinUnique.IsSylowTwoOf (T ⊓ J) J :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer hTJ)
  have hOJ : pCoreOf 2 J ≤ T ⊓ J := pCoreOf_two_le_of_isSylowTwoOf hSI
  have hXS : X ≤ Subgroup.normalizer ((T ⊓ J : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_of_mk inf_le_right hOJ (hXJ hx)
      (hNS ⟨hD.e₁ ⟨⟨x, hXJ hx⟩, hx, rfl⟩, hD.e₂ ⟨⟨x, hXJ hx⟩, hx, rfl⟩⟩)
  have hXT : X ≤ Subgroup.normalizer (TL T J : Set G) := by
    rw [tL_eq_sup hJ]
    refine le_normalizer_sup' (fun x hx => ?_) hXS
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (J ⊔ T)
      ((le_sup_left : J ≤ J ⊔ T) (hXJ hx))
  have hXo : Odd (Nat.card ↥X) := h.cartan.2.1
  have hX9 : Nat.card ↥X = 9 := card_cartan cL
    (fun _ hx => cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan hx)
    (cartan_inf_lOf_inf_sectionCentralizer hN h1102 h.hyp h.v₁ h.cartan)
  set A := J ⊓ Subgroup.normalizer (TL T J : Set G) with hA
  have hXA : X ≤ A := le_inf hXJ hXT
  have hAS : A ≤ Subgroup.normalizer ((T ⊓ J : Subgroup G) : Set G) := by
    intro a ha
    have h1 := Subgroup.inf_normalizer_le_normalizer_inf
      ⟨ha.2, Subgroup.le_normalizer ha.1⟩
    rwa [tL_inf] at h1
  have hAbar := modO2Image_le_normalizer (K := J) hAS
  obtain ⟨t, ht⟩ := exists_card_eq_mul (inf_le_left : A ≤ J)
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp hD.syl.2.1
  have hdvd : Nat.card ↥(modO2Image J A) ∣ 2 ^ s * 9 := by
    rw [← hs, ← hcardS]
    exact Subgroup.card_dvd_of_le hAbar
  have h9 : 9 ∣ Nat.card ↥A := hX9 ▸ Subgroup.card_dvd_of_le hXA
  obtain ⟨r, hr⟩ := h9
  have hr2 : r ∣ 2 ^ (s + t) := by
    have h1 : Nat.card ↥A ∣ 2 ^ s * 9 * 2 ^ t := ht ▸ Nat.mul_dvd_mul_right hdvd _
    rw [hr] at h1
    have h2 : 9 * r ∣ 9 * 2 ^ (s + t) := by
      rw [pow_add]
      convert h1 using 1
      ring
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hr2
  refine ⟨hXA, hXo, a, ?_⟩
  change X.relIndex A = 2 ^ a
  have h3 := Subgroup.relIndex_mul_card X A
  rw [inf_eq_left.mpr hXA, hX9, hr] at h3
  omega

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
