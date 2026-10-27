module

public import CFSG.RankThree.PartTwo.Sec13.F135LastDefs
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSL3

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup

theorem lift_card_sq_one_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card {a : G | a ^ 2 = 1} = Nat.card {b : H | b ^ 2 = 1} := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (p := fun a : G => a ^ 2 = 1)
    (q := fun b : H => b ^ 2 = 1) fun a => ?_)
  show a ^ 2 = 1 ↔ e a ^ 2 = 1
  rw [← map_pow, e.map_eq_one_iff]

theorem lift_injective_of_disjoint {X Q : Type*} [Group X] [Group Q] (π : X →* Q)
    (Y : Subgroup X) (hd : Disjoint Y π.ker) : Function.Injective (π.comp Y.subtype) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨t, ht⟩ h
  exact Subtype.ext (Subgroup.disjoint_def.mp hd ht h)

theorem lift_card_map_of_disjoint {X Q : Type*} [Group X] [Group Q] (π : X →* Q)
    (Y : Subgroup X) (hd : Disjoint Y π.ker) : Nat.card (Y.map π) = Nat.card Y := by
  have hinj := lift_injective_of_disjoint π Y hd
  let g : Y → Y.map π := fun t => ⟨π t, Subgroup.mem_map_of_mem π t.2⟩
  have hg : Function.Bijective g := by
    refine ⟨fun a b hab => hinj ?_, fun y => ?_⟩
    · exact congrArg Subtype.val hab
    · obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨t, ht⟩, Subtype.ext hty⟩
  exact (Nat.card_congr (Equiv.ofBijective g hg)).symm

theorem lift_fourCubeSeven_map {G S : Type*} [Group G] [Group S] (φ : G →* S)
    (hφ : Function.Injective φ) {A : Subgroup G} {x : G} (h : FourCubeSeven A x) :
    FourCubeSeven (A.map φ) (φ x) := by
  unfold FourCubeSeven at h ⊢
  obtain ⟨hcomm, hcard, hexp, hinv, hord, hnorm, hfpf⟩ := h
  have hx : ∀ a ∈ A, x * a * x⁻¹ ∈ A := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hnorm a).mp ha
  have hx' : ∀ a ∈ A, x⁻¹ * a * x ∈ A := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hnorm (x⁻¹ * a * x)).mpr (by
      have e : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
      rw [e]
      exact ha)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rw [Subgroup.card_map_of_injective hφ]
    exact hcard
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hexp a ha, map_one]
  · exact (lift_card_sq_one_eq (Subgroup.equivMapOfInjective A φ hφ)).symm.trans hinv
  · rw [orderOf_injective φ hφ x]
    exact hord
  · rw [Subgroup.mem_normalizer_iff]
    intro s
    simp only [SetLike.mem_coe, Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨x * a * x⁻¹, hx a ha, by simp only [map_mul, map_inv]⟩
    · rintro ⟨a, ha, hsa⟩
      refine ⟨x⁻¹ * a * x, hx' a ha, ?_⟩
      simp only [map_mul, map_inv]
      rw [hsa]
      group
  · rintro _ ⟨a, ha, rfl⟩ hsq hconj
    have hsq' : a ^ 2 = 1 := by
      rw [← map_pow] at hsq
      exact (map_eq_one_iff φ hφ).mp hsq
    have hconj' : x * a * x⁻¹ = a := by
      apply hφ
      simp only [map_mul, map_inv]
      exact hconj
    rw [hfpf a ha hsq' hconj', map_one]

theorem lift_fourCubeSeven_of_injective {G S : Type*} [Group G] [Group S] (φ : G →* S)
    (hφ : Function.Injective φ) {A₀ : Subgroup G} {x₀ : G} {A : Subgroup S} {x : S}
    (hA : A₀.map φ = A) (hx : φ x₀ = x) (h : FourCubeSeven A x) : FourCubeSeven A₀ x₀ := by
  unfold FourCubeSeven at h ⊢
  obtain ⟨hcomm, hcard, hexp, hinv, hord, hnorm, hfpf⟩ := h
  have hmem : ∀ g : G, g ∈ A₀ ↔ φ g ∈ A := fun g => by
    rw [← hA, Subgroup.mem_map_iff_mem hφ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    apply hφ
    rw [map_mul, map_mul]
    exact hcomm _ ((hmem a).mp ha) _ ((hmem b).mp hb)
  · have h1 := Subgroup.card_map_of_injective (K := A₀) hφ
    rw [hA] at h1
    exact h1.symm.trans hcard
  · intro a ha
    apply hφ
    rw [map_pow, map_one]
    exact hexp _ ((hmem a).mp ha)
  · exact (lift_card_sq_one_eq ((Subgroup.equivMapOfInjective A₀ φ hφ).trans
      (MulEquiv.subgroupCongr hA))).trans hinv
  · rw [← orderOf_injective φ hφ x₀, hx]
    exact hord
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    show g ∈ A₀ ↔ x₀ * g * x₀⁻¹ ∈ A₀
    rw [hmem, hmem, map_mul, map_mul, map_inv, hx]
    exact Subgroup.mem_normalizer_iff.mp hnorm (φ g)
  · intro a ha hsq hconj
    apply hφ
    rw [map_one]
    have hsq' : φ a ^ 2 = 1 := by rw [← map_pow, hsq, map_one]
    have hconj' : x * φ a * x⁻¹ = φ a := by
      have h2 := congrArg φ hconj
      simpa only [map_mul, map_inv, hx] using h2
    exact hfpf (φ a) ((hmem a).mp ha) hsq' hconj'

theorem HasTwoSix.of_mulEquiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') (h : HasTwoSix S) :
    HasTwoSix S' := by
  unfold HasTwoSix at h ⊢
  obtain ⟨T, hT, hcard⟩ := h
  refine ⟨T.map e.toMonoidHom, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
    rw [← map_mul, hT s hs, map_one]
  · have hinj : Function.Injective e.toMonoidHom := e.injective
    rw [Subgroup.card_map_of_injective hinj]
    exact hcard

theorem hasTwoSix_lift {K S : Type*} [Group K] [Finite K] [Group S] (π : K →* S)
    (hπ : Function.Surjective π) (hodd : Odd (Nat.card π.ker)) (h : HasTwoSix S) : HasTwoSix K := by
  unfold HasTwoSix at h ⊢
  obtain ⟨T, hT, hcard⟩ := h
  have hcop : Nat.Coprime (Nat.card π.ker) (Nat.card T) := by
    rw [hcard]
    exact Nat.Coprime.pow_right 6 (Nat.coprime_two_right.mpr hodd)
  obtain ⟨Y', hY'map, hY'disj⟩ :=
    CFSG.RankThree.PartTwo.Sec6.BThreeCensus.exists_lift_of_coprime hπ T hcop
  refine ⟨Y', ?_, ?_⟩
  · intro t ht
    have hπt : π t ∈ T := by
      rw [← hY'map]
      exact Subgroup.mem_map_of_mem π ht
    have h1 : t * t ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, hT _ hπt]
    exact Subgroup.disjoint_def.mp hY'disj (Y'.mul_mem ht ht) h1
  · rw [← lift_card_map_of_disjoint π Y' hY'disj, hY'map, hcard]

theorem lift_le_normalizer_self {S : Type*} [Group S] {A : Subgroup S} :
    A ≤ Subgroup.normalizer (A : Set S) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)
  · intro hb
    have h1 := A.mul_mem (A.mul_mem (A.inv_mem ha) hb) ha
    have e : a⁻¹ * (a * b * a⁻¹) * a = b := by group
    rw [e] at h1
    exact h1

theorem lift_orderOf_subtype {S : Type*} [Group S] {B : Subgroup S} {x₀ : B} {x : S}
    (hx₀ : (x₀ : S) = x) (hord : orderOf x = 7) : orderOf x₀ = 7 := by
  have h3 := orderOf_injective B.subtype B.subtype_injective x₀
  have h4 : B.subtype x₀ = x := hx₀
  rw [h4] at h3
  rw [← h3]
  exact hord

theorem lift_index_dvd_of_gen {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {g : G}
    (hord : orderOf g = 7) (hgen : ∀ y : G ⧸ N, y ∈ Subgroup.zpowers (QuotientGroup.mk' N g)) :
    N.index ∣ 7 := by
  have htop : Subgroup.zpowers (QuotientGroup.mk' N g) = ⊤ :=
    (Subgroup.eq_top_iff' _).mpr hgen
  have hcardq : Nat.card (G ⧸ N) = orderOf (QuotientGroup.mk' N g) := by
    rw [← Nat.card_zpowers, htop]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
  have h1 := orderOf_map_dvd (QuotientGroup.mk' N) g
  rw [hord] at h1
  have h5 : N.index = Nat.card (G ⧸ N) := rfl
  rw [h5, hcardq]
  exact h1

theorem lift_mem_zpowers_sup {S : Type*} [Group S] {A : Subgroup S} {x : S}
    {B : Subgroup S} (hBdef : B = A ⊔ Subgroup.zpowers x) {N : Subgroup B}
    (hNmem : ∀ n : B, n ∈ N ↔ (n : S) ∈ A) {x₀ : B} (hx₀ : (x₀ : S) = x) (γ : B) :
    γ ∈ Subgroup.zpowers x₀ ⊔ N := by
  have hsub : A ≤ (Subgroup.zpowers x₀ ⊔ N).map B.subtype := by
    intro a ha
    have haB : a ∈ B := by
      rw [hBdef]
      exact Subgroup.mem_sup_left ha
    exact Subgroup.mem_map.mpr
      ⟨⟨a, haB⟩, Subgroup.mem_sup_right ((hNmem ⟨a, haB⟩).mpr ha), rfl⟩
  have hz : Subgroup.zpowers x ≤ (Subgroup.zpowers x₀ ⊔ N).map B.subtype := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_map.mpr ⟨x₀, Subgroup.mem_sup_left (Subgroup.mem_zpowers x₀), hx₀⟩
  have hle : B ≤ (Subgroup.zpowers x₀ ⊔ N).map B.subtype := by
    intro s hs
    have hs' : s ∈ A ⊔ Subgroup.zpowers x := by
      rw [← hBdef]
      exact hs
    exact (sup_le hsub hz) hs'
  obtain ⟨m, hm, hmγ⟩ := Subgroup.mem_map.mp (hle γ.2)
  have hmγ' : m = γ := Subtype.ext hmγ
  rw [← hmγ']
  exact hm

theorem lift_card_sup_dvd {S : Type*} [Group S] {A : Subgroup S} {x : S}
    (h : FourCubeSeven A x) : Nat.card ↥(A ⊔ Subgroup.zpowers x) ∣ 448 := by
  unfold FourCubeSeven at h
  obtain ⟨-, hcardA, -, -, hord, hnorm, -⟩ := h
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup S, B = A ⊔ Subgroup.zpowers x := ⟨_, rfl⟩
  rw [← hBdef]
  have hAB : A ≤ B := by
    rw [hBdef]
    exact le_sup_left
  have hxB : x ∈ B := by
    rw [hBdef]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hBn : B ≤ Subgroup.normalizer (A : Set S) := by
    rw [hBdef]
    exact sup_le lift_le_normalizer_self (Subgroup.zpowers_le.mpr hnorm)
  have hN : (A.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAB]
    intro n g hn hg
    exact (Subgroup.mem_normalizer_iff.mp (hBn hg) n).mp hn
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup B, N = A.subgroupOf B := ⟨_, rfl⟩
  have hNN : N.Normal := by
    rw [hNdef]
    exact hN
  haveI := hNN
  have hNmem : ∀ n : B, n ∈ N ↔ (n : S) ∈ A := fun n => by
    rw [hNdef, Subgroup.mem_subgroupOf]
  have hNcard : Nat.card N = Nat.card A := by
    rw [hNdef]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : B, (x₀ : S) = x := ⟨⟨x, hxB⟩, rfl⟩
  have hgen : ∀ y : ↥B ⧸ N, y ∈ Subgroup.zpowers (QuotientGroup.mk' N x₀) := by
    intro y
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨z, hz', n, hn, hzn⟩ := Subgroup.mem_sup_of_normal_right.mp
      (lift_mem_zpowers_sup hBdef hNmem hx₀ γ)
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [← hzn, map_mul, hn1, mul_one]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
    rw [map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hidx : N.index ∣ 7 :=
    lift_index_dvd_of_gen N (lift_orderOf_subtype hx₀ hord) hgen
  have hBcard : Nat.card B = Nat.card N * N.index := (Subgroup.card_mul_index N).symm
  rw [hBcard, hNcard, hcardA]
  have h448 : (448 : ℕ) = 4 ^ 3 * 7 := by norm_num
  rw [h448]
  exact mul_dvd_mul_left _ hidx

theorem fourCubeSeven_lift {K S : Type*} [Group K] [Finite K] [Group S] (π : K →* S)
    (hπ : Function.Surjective π) (hcop : Nat.Coprime (Nat.card π.ker) 14) {A : Subgroup S} {x : S}
    (h : FourCubeSeven A x) : ∃ (A' : Subgroup K) (x' : K), FourCubeSeven A' x' := by
  have hdvd := lift_card_sup_dvd h
  have h14 : Nat.card ↥(A ⊔ Subgroup.zpowers x) ∣ 14 ^ 6 := hdvd.trans (by norm_num)
  have hcopB : Nat.Coprime (Nat.card π.ker) (Nat.card ↥(A ⊔ Subgroup.zpowers x)) :=
    Nat.Coprime.coprime_dvd_right h14 (Nat.Coprime.pow_right 6 hcop)
  obtain ⟨B', hB'map, hB'disj⟩ :=
    CFSG.RankThree.PartTwo.Sec6.BThreeCensus.exists_lift_of_coprime hπ _ hcopB
  have hφinj : Function.Injective (π.comp B'.subtype) :=
    lift_injective_of_disjoint π B' hB'disj
  have hxB : x ∈ B'.map π := by
    rw [hB'map]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : B', π x₀ = x := by
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hxB
    exact ⟨⟨k, hk⟩, hkx⟩
  have hA₀ : (A.comap (π.comp B'.subtype)).map (π.comp B'.subtype) = A := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hs
      have hsB : s ∈ B'.map π := by
        rw [hB'map]
        exact Subgroup.mem_sup_left hs
      obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.mp hsB
      have hkA : π k ∈ A := by
        rw [hks]
        exact hs
      exact Subgroup.mem_map.mpr ⟨⟨k, hk⟩, hkA, hks⟩
  have h₀ : FourCubeSeven (A.comap (π.comp B'.subtype)) x₀ :=
    lift_fourCubeSeven_of_injective (π.comp B'.subtype) hφinj hA₀ hx₀ h
  exact ⟨(A.comap (π.comp B'.subtype)).map B'.subtype, B'.subtype x₀,
    lift_fourCubeSeven_map B'.subtype B'.subtype_injective h₀⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last
