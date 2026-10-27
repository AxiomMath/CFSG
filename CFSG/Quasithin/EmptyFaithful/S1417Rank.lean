module

public import CFSG.Quasithin.Background.D2Fourteen
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.EmptyFaithful.S1417System

public section

namespace CFSG.Quasithin

namespace S1417

open CFSG.Open

universe u

section Cover

variable {V : Type*} [CommGroup V] [Finite V]

theorem a131_of_faithful_cover {P A : Subgroup (MulAut V)} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hPp : IsPGroup p P) (hA2 : IsElemAbelian2 A) (hAn : ∀ a ∈ A, ∀ y ∈ P, a * y * a⁻¹ ∈ P)
    (hfaith : ∀ a ∈ A, (∀ y ∈ P, a * y = y * a) → a = 1)
    (hcov : ∃ (S : Type u) (_ : Group S) (_ : Finite S),
      (∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2) ∧
        ∃ φ : S →* ↥(P ⊔ A), Function.Surjective φ) :
    A1c.A131Concl p ↥(P ⊔ A) := by
  obtain ⟨S, _, _, hS, φ, hφ⟩ := hcov
  have hPK : P ≤ P ⊔ A := le_sup_left
  have hAK : A ≤ P ⊔ A := le_sup_right
  have hle : P.subgroupOf (P ⊔ A) ≤ CFSG.Open.pCore p ↥(P ⊔ A) := subgroupOf_le_pCore hPp hAn
  have hF : Subgroup.centralizer (CFSG.Open.pCore p ↥(P ⊔ A) : Set ↥(P ⊔ A)) ≤
      CFSG.Open.pCore p ↥(P ⊔ A) := by
    intro g hg
    have hsup : (P.subgroupOf (P ⊔ A)) ⊔ (A.subgroupOf (P ⊔ A)) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hPK hAK, Subgroup.subgroupOf_self]
    have hgtop : g ∈ (P.subgroupOf (P ⊔ A)) ⊔ (A.subgroupOf (P ⊔ A)) := by
      rw [hsup]; exact Subgroup.mem_top g
    have hnormK : (P.subgroupOf (P ⊔ A)).Normal := normal_subgroupOf_sup hAn
    obtain ⟨n, hn, h, hh, hnh⟩ := Subgroup.mem_sup_of_normal_left.mp hgtop
    have hnP : (n : MulAut V) ∈ P := hn
    have hhA : (h : MulAut V) ∈ A := hh
    have hgc : ∀ z ∈ P, ((n : MulAut V) * (h : MulAut V)) * z =
        z * ((n : MulAut V) * (h : MulAut V)) := by
      intro z hz
      have hzK : z ∈ P ⊔ A := hPK hz
      have hzmem : (⟨z, hzK⟩ : ↥(P ⊔ A)) ∈ CFSG.Open.pCore p ↥(P ⊔ A) := hle hz
      have := Subgroup.mem_centralizer_iff.mp hg _ hzmem
      have h2 := congrArg (fun w : ↥(P ⊔ A) => (w : MulAut V)) this
      have h3 : ((g : ↥(P ⊔ A)) : MulAut V) = (n : MulAut V) * (h : MulAut V) := by
        rw [← hnh]; rfl
      simp only [Subgroup.coe_mul] at h2
      rw [h3] at h2
      exact h2.symm
    have hh1 : (h : MulAut V) = 1 := eq_one_of_centralizes_of_faithful hp hPp hfaith hA2.2 hnP
      hhA (hAn _ hhA) hgc
    have hh2 : h = 1 := Subtype.ext hh1
    rw [hh2, mul_one] at hnh
    rw [← hnh]
    exact hle hn
  exact A1c.A131Concl_of_surjective hp hF _ S φ hφ rfl (hS p (Fact.out) hp)

theorem isCyclic_of_faithful_cover {P A : Subgroup (MulAut V)} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hPp : IsPGroup p P) (hA2 : IsElemAbelian2 A) (hAn : ∀ a ∈ A, ∀ y ∈ P, a * y * a⁻¹ ∈ P)
    (hfaith : ∀ a ∈ A, (∀ y ∈ P, a * y = y * a) → a = 1)
    (hcov : ∃ (S : Type u) (_ : Group S) (_ : Finite S),
      (∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2) ∧
        ∃ φ : S →* ↥(P ⊔ A), Function.Surjective φ)
    {a : MulAut V} (haA : a ∈ A) (ha1 : a ≠ 1) :
    IsCyclic ↥(P ⊓ Subgroup.centralizer ({a} : Set (MulAut V))) := by
  have h131 := a131_of_faithful_cover hp hPp hA2 hAn hfaith hcov
  set K := P ⊔ A with hK
  have haK : a ∈ K := (le_sup_right : A ≤ K) haA
  have hPK : P ≤ K := le_sup_left
  let ā : ↥K := ⟨a, haK⟩
  have hā2 : ā ^ 2 = 1 := Subtype.ext (hA2.2 a haA)
  have hT2 : IsPGroup 2 (Subgroup.zpowers ā) := A1c.isPGroup_two_zpowers hā2
  have hT1 : Subgroup.zpowers ā ≠ ⊥ := by
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    exact ha1 (congrArg Subtype.val h)
  have hcyc := h131.1 (Subgroup.zpowers ā) hT2 hT1
  have hsub : (P ⊓ Subgroup.centralizer ({a} : Set (MulAut V))).subgroupOf K ≤
      CFSG.Open.pCore p ↥K ⊓ Subgroup.centralizer ((Subgroup.zpowers ā : Subgroup ↥K) : Set ↥K) := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    refine ⟨subgroupOf_le_pCore hPp hAn (by rw [Subgroup.mem_subgroupOf]; exact hz.1),
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc : Commute ā z := by
      apply Subtype.ext
      exact ((Subgroup.mem_centralizer_singleton_iff.mp hz.2)).symm
    exact (hc.zpow_left k).eq
  have hc1 : IsCyclic ↥((P ⊓ Subgroup.centralizer ({a} : Set (MulAut V))).subgroupOf K) :=
    isCyclic_of_injective (Subgroup.inclusion hsub) (Subgroup.inclusion_injective hsub)
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hPK)).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hPK)).surjective

end Cover


section Three

variable {V : Type*} [CommGroup V] [Finite V]

theorem comm_of_mem_closure_comm {G : Type*} [Group G] {S : Set G}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {x y : G} (hx : x ∈ Subgroup.closure S)
    (hy : y ∈ Subgroup.closure S) : x * y = y * x := by
  have h1 : ∀ z ∈ Subgroup.closure S, ∀ b ∈ S, z * b = b * z := by
    intro z hz b hb
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {b} := by
      rw [Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hS a ha b hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
  have hle : Subgroup.closure S ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.closure_le]
    intro b hb
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (h1 x hx b hb).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

theorem pow_eq_one_of_mem_closure_comm {G : Type*} [Group G] {S : Set G} {n : ℕ}
    (hS : ∀ x ∈ S, x ^ n = 1) (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {g : G}
    (hg : g ∈ Subgroup.closure S) : g ^ n = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact one_pow n
  | mul x y hx hy ihx ihy =>
    rw [Commute.mul_pow (comm_of_mem_closure_comm hc hx hy) n, ihx, ihy, mul_one]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem eq_or_of_mem_zpowers_two {G : Type*} [Group G] {s : G} (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1)
    {a : G} (ha : a ∈ Subgroup.zpowers s) : a = 1 ∨ a = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [← zpow_mod_orderOf, ho]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    simp [h]
  · right
    simp [h]

theorem not_isCyclic_of_four_cubes {C : Type*} [Group C] [Finite C] {α β : C} (hα : α ^ 3 = 1)
    (hβ : β ^ 3 = 1) (h1 : α ≠ 1) (h2 : β ≠ 1) (h3 : β ≠ α) (h4 : β ≠ α⁻¹) :
    ¬ IsCyclic C := by
  classical
  intro hcyc
  have : Fintype C := Fintype.ofFinite C
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 3) (by norm_num)
  have hα3 : α⁻¹ ^ 3 = 1 := by rw [inv_pow, hα, inv_one]
  have hαinv : α⁻¹ ≠ α := by
    intro h
    apply h1
    have h5 : α * α = 1 := by
      nth_rewrite 1 [← h]
      exact inv_mul_cancel α
    have h6 : α ^ 3 = α := by rw [pow_succ, pow_two, h5, one_mul]
    rw [← h6]
    exact hα
  have e1 : (1 : C) ≠ α := h1.symm
  have e2 : (1 : C) ≠ α⁻¹ := fun h => h1 (inv_eq_one.mp h.symm)
  have e3 : (1 : C) ≠ β := h2.symm
  have e4 : α ≠ α⁻¹ := hαinv.symm
  have e5 : α ≠ β := h3.symm
  have e6 : α⁻¹ ≠ β := h4.symm
  have hsub : ({1, α, α⁻¹, β} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 3 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with h | h | h | h <;> rw [h]
    · exact one_pow 3
    · exact hα
    · exact hα3
    · exact hβ
  have hcard : ({1, α, α⁻¹, β} : Finset C).card = 4 := by
    simp [Finset.card_insert_of_notMem, e1, e2, e3, e4, e5, e6]
  have := Finset.card_le_card hsub
  omega

theorem false_of_three_blocks {L₁ L₂ L₃ : Subgroup (MulAut V)} {U₁ U₂ U₃ : Subgroup V}
    (hN₁ : ActsAsNaturalL2 L₁ U₁) (hN₂ : ActsAsNaturalL2 L₂ U₂) (hN₃ : ActsAsNaturalL2 L₃ U₃)
    (h12 : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h13 : ∀ a ∈ L₁, ∀ b ∈ L₃, a * b = b * a)
    (h23 : ∀ a ∈ L₂, ∀ b ∈ L₃, a * b = b * a) (hinf : L₂ ⊓ L₃ = ⊥)
    (hcov : ∀ B : Subgroup (MulAut V), B ≤ L₁ ⊔ L₂ ⊔ L₃ →
      ∃ (S : Type u) (_ : Group S) (_ : Finite S),
        (∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2) ∧
          ∃ φ : S →* ↥B, Function.Surjective φ) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₁, hx₁, hx₁3, hx₁1⟩ := exists_orderThree hN₁
  obtain ⟨x₂, hx₂, hx₂3, hx₂1⟩ := exists_orderThree hN₂
  obtain ⟨x₃, hx₃, hx₃3, hx₃1⟩ := exists_orderThree hN₃
  obtain ⟨s, hs, hs2, hs1⟩ := exists_involution hN₁
  have hsx₁ : s * x₁ * s⁻¹ = x₁⁻¹ := conj_inv hN₁ hs hs2 hs1 hx₁ hx₁3 hx₁1
  have hsx₂ : s * x₂ = x₂ * s := h12 s hs x₂ hx₂
  have hsx₃ : s * x₃ = x₃ * s := h13 s hs x₃ hx₃
  set Sg : Set (MulAut V) := {x₁, x₂, x₃} with hSg
  have hcomm : ∀ a ∈ Sg, ∀ b ∈ Sg, a * b = b * a := by
    intro a ha b hb
    simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rw [ha, hb]
    · exact h12 _ hx₁ _ hx₂
    · exact h13 _ hx₁ _ hx₃
    · exact (h12 _ hx₁ _ hx₂).symm
    · exact h23 _ hx₂ _ hx₃
    · exact (h13 _ hx₁ _ hx₃).symm
    · exact (h23 _ hx₂ _ hx₃).symm
  have hS3 : ∀ x ∈ Sg, x ^ 3 = 1 := by
    intro x hx
    simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h <;> rw [h]
    exacts [hx₁3, hx₂3, hx₃3]
  set P : Subgroup (MulAut V) := Subgroup.closure Sg with hP
  set A : Subgroup (MulAut V) := Subgroup.zpowers s with hA
  have hx₁P : x₁ ∈ P := Subgroup.subset_closure (by simp [hSg])
  have hx₂P : x₂ ∈ P := Subgroup.subset_closure (by simp [hSg])
  have hx₃P : x₃ ∈ P := Subgroup.subset_closure (by simp [hSg])
  have hPp : IsPGroup 3 P := by
    intro g
    refine ⟨1, ?_⟩
    have := pow_eq_one_of_mem_closure_comm hS3 hcomm g.2
    exact Subtype.ext (by simpa using this)
  have hss : s * s = 1 := by rw [← pow_two]; exact hs2
  have hconj : ∀ y ∈ P, s * y * s⁻¹ ∈ P := by
    have hle : P ≤ P.comap (MulAut.conj s).toMonoidHom := by
      rw [hP, Subgroup.closure_le]
      intro z hz
      show s * z * s⁻¹ ∈ P
      simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h | h <;> rw [h]
      · rw [hsx₁]
        exact P.inv_mem hx₁P
      · rw [hsx₂, mul_assoc, mul_inv_cancel, mul_one]
        exact hx₂P
      · rw [hsx₃, mul_assoc, mul_inv_cancel, mul_one]
        exact hx₃P
    exact fun y hy => hle hy
  have hAn : ∀ a ∈ A, ∀ y ∈ P, a * y * a⁻¹ ∈ P := by
    intro a ha y hy
    rcases eq_or_of_mem_zpowers_two hs2 hs1 ha with h | h
    · rw [h]
      simpa using hy
    · rw [h]
      exact hconj y hy
  have hfaith : ∀ a ∈ A, (∀ y ∈ P, a * y = y * a) → a = 1 := by
    intro a ha hc
    rcases eq_or_of_mem_zpowers_two hs2 hs1 ha with h | h
    · exact h
    · exfalso
      have h1 : s * x₁ = x₁ * s := by rw [← h]; exact hc x₁ hx₁P
      have h2 : x₁ = x₁⁻¹ := by
        rw [← hsx₁, h1]
        group
      have h3 : x₁ * x₁ = 1 := by
        nth_rewrite 2 [h2]
        exact mul_inv_cancel x₁
      have h4 : x₁ ^ 3 = x₁ := by rw [pow_succ, pow_two, h3, one_mul]
      exact hx₁1 (h4 ▸ hx₁3)
  have hA2 : IsElemAbelian2 A := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self s i j).eq
    · rcases eq_or_of_mem_zpowers_two hs2 hs1 ha with h | h
      · rw [h, one_pow]
      · rw [h]
        exact hs2
  have hPQ : P ≤ L₁ ⊔ L₂ ⊔ L₃ := by
    rw [hP, Subgroup.closure_le]
    intro z hz
    simp only [hSg, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h | h <;> rw [h]
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hx₁)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hx₂)
    · exact Subgroup.mem_sup_right hx₃
  have hAQ : A ≤ L₁ ⊔ L₂ ⊔ L₃ := by
    rw [hA, Subgroup.zpowers_le]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hs)
  have hcyc := isCyclic_of_faithful_cover (p := 3) (by norm_num) hPp hA2 hAn hfaith
    (hcov (P ⊔ A) (sup_le hPQ hAQ)) (a := s) (Subgroup.mem_zpowers s) hs1
  have hx₂C : x₂ ∈ P ⊓ Subgroup.centralizer ({s} : Set (MulAut V)) :=
    ⟨hx₂P, Subgroup.mem_centralizer_singleton_iff.mpr hsx₂.symm⟩
  have hx₃C : x₃ ∈ P ⊓ Subgroup.centralizer ({s} : Set (MulAut V)) :=
    ⟨hx₃P, Subgroup.mem_centralizer_singleton_iff.mpr hsx₃.symm⟩
  refine not_isCyclic_of_four_cubes (α := (⟨x₂, hx₂C⟩ : ↥(P ⊓ Subgroup.centralizer ({s} : Set (MulAut V)))))
    (β := ⟨x₃, hx₃C⟩) ?_ ?_ ?_ ?_ ?_ ?_ hcyc
  · exact Subtype.ext (by simpa using hx₂3)
  · exact Subtype.ext (by simpa using hx₃3)
  · intro h
    exact hx₂1 (congrArg Subtype.val h)
  · intro h
    exact hx₃1 (congrArg Subtype.val h)
  · intro h
    have h' : x₃ = x₂ := congrArg Subtype.val h
    have : x₃ ∈ L₂ ⊓ L₃ := ⟨h' ▸ hx₂, hx₃⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact hx₃1 this
  · intro h
    have h' : x₃ = x₂⁻¹ := by simpa using congrArg Subtype.val h
    have : x₃ ∈ L₂ ⊓ L₃ := ⟨h' ▸ L₂.inv_mem hx₂, hx₃⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact hx₃1 this

end Three


section GroupLevel

variable {G : Type u} [Group G] [Finite G]

theorem exists_cover {V K M : Subgroup G} (hV : IsElemAbelian 2 V) (hKM : K ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) {B : Subgroup (MulAut (IntMod V hV))}
    (hB : B ≤ autI hV K)
    (hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup ↥M) ≤ 2) :
    ∃ (S : Type u) (_ : Group S) (_ : Finite S),
      (∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2) ∧
        ∃ φ : S →* ↥B, Function.Surjective φ := by
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKM.trans hMN
  set K₀ := preI hV K hKN B with hK₀
  have hK₀K : K₀ ≤ K := preI_le hV
  have hK₀N : K₀ ≤ Subgroup.normalizer (V : Set G) := hK₀K.trans hKN
  refine ⟨↥K₀, inferInstance, inferInstance, fun q hq hq2 => ?_, ?_⟩
  · exact (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt
      (Subgroup.inclusion (hK₀K.trans hKM)) (Subgroup.inclusion_injective _)).trans
      (hrank q hq hq2)
  · have hrange : (convHom hV K₀ hK₀N).range = B := by
      rw [range_convHom, hK₀, autI_preI hV hB]
    refine ⟨(convHom hV K₀ hK₀N).codRestrict B
      (fun k => (SetLike.ext_iff.mp hrange _).mp ⟨k, rfl⟩), fun b => ?_⟩
    have hb : (b : MulAut (IntMod V hV)) ∈ (convHom hV K₀ hK₀N).range := by
      rw [hrange]
      exact b.2
    obtain ⟨k, hk⟩ := hb
    exact ⟨k, Subtype.ext hk⟩

theorem BlockSystem.card_le_two {V M : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup ↥M) ≤ 2)
    {I : Finset (Subgroup (MulAut (IntMod V hV)))}
    (hS : BlockSystem (autI hV M) (autI hV (thompsonJ M)) I) : I.card ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨L₁, h1, L₂, h2, L₃, h3, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
  have hinf : L₂ ⊓ L₃ = ⊥ := by
    have := hS.indep L₃ h3
    refine le_bot_iff.mp ?_
    rw [← this, inf_comm]
    exact inf_le_inf_left _ (le_iSup₂_of_le L₂ h2 (le_iSup_of_le h23 le_rfl))
  refine false_of_three_blocks (hS.nat L₁ h1) (hS.nat L₂ h2) (hS.nat L₃ h3)
    (hS.comm L₁ h1 L₂ h2 h12) (hS.comm L₁ h1 L₃ h3 h13) (hS.comm L₂ h2 L₃ h3 h23) hinf ?_
  intro B hB
  have hBY : B ≤ autI hV (thompsonJ M) :=
    hB.trans (sup_le (sup_le (hS.le_Y h1) (hS.le_Y h2)) (hS.le_Y h3))
  exact exists_cover hV (iSup₂_le fun _ hA => hA.1 : thompsonJ M ≤ M) hMN hBY hrank

end GroupLevel

end S1417

end CFSG.Quasithin
