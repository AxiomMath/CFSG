module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.L827X.LBModule2

open scoped commutatorElement

variable {G : Type} [Group G]

theorem ch827_le_normalizer_inf {Λ A B : Subgroup G}
    (hA : Λ ≤ Subgroup.normalizer (A : Set G)) (hB : Λ ≤ Subgroup.normalizer (B : Set G)) :
    Λ ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro l hl
  have hA' : ∀ g, g ∈ A ↔ l * g * l⁻¹ ∈ A := fun g => Subgroup.mem_normalizer_iff.mp (hA hl) g
  have hB' : ∀ g, g ∈ B ↔ l * g * l⁻¹ ∈ B := fun g => Subgroup.mem_normalizer_iff.mp (hB hl) g
  rw [Subgroup.mem_normalizer_iff]
  intro g
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (hA' g) (hB' g)

theorem ch827_normal [Finite G] {Λ W₀ W₁ : Subgroup G} (hW0W1 : W₀ < W₁)
    (hP : IsPGroup 2 W₁) (hΛ0 : Λ ≤ Subgroup.normalizer (W₀ : Set G))
    (hΛ1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (hch : ∀ B : Subgroup G, W₀ ≤ B → B ≤ W₁ →
      Λ ≤ Subgroup.normalizer (B : Set G) → B = W₀ ∨ B = W₁) :
    (W₀.subgroupOf W₁).Normal := by
  have hΛN : Λ ≤ Subgroup.normalizer ((Subgroup.normalizer (W₀ : Set G) : Subgroup G) : Set G) :=
    hΛ0.trans Subgroup.le_normalizer
  have hΛNW := ch827_le_normalizer_inf hΛ1 hΛN
  have hW0NW : W₀ ≤ W₁ ⊓ Subgroup.normalizer (W₀ : Set G) :=
    le_inf hW0W1.le Subgroup.le_normalizer
  rcases hch _ hW0NW inf_le_left hΛNW with hEq | hEq
  · exfalso
    have hlt : W₀.subgroupOf W₁ < ⊤ := by
      obtain ⟨x, hxW1, hxW0⟩ := SetLike.exists_of_lt hW0W1
      refine lt_top_iff_ne_top.mpr fun htop => hxW0 ?_
      have hmem : (⟨x, hxW1⟩ : ↥W₁) ∈ W₀.subgroupOf W₁ := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    haveI : Group.IsNilpotent ↥W₁ := hP.isNilpotent
    have hNC : NormalizerCondition ↥W₁ := Group.normalizerCondition_of_isNilpotent
    obtain ⟨x, hxN, hxH⟩ := SetLike.exists_of_lt (hNC _ hlt)
    have key : ∀ z : ↥W₁,
        z ∈ Subgroup.normalizer ((W₀.subgroupOf W₁ : Subgroup ↥W₁) : Set ↥W₁) →
        ∀ g : G, g ∈ W₀ → (z : G) * g * (z : G)⁻¹ ∈ W₀ := by
      intro z hz g hg
      have h1 := (Subgroup.mem_normalizer_iff.mp hz ⟨g, hW0W1.le hg⟩).mp
        (Subgroup.mem_subgroupOf.mpr hg)
      exact Subgroup.mem_subgroupOf.mp h1
    have hxN' : (x : G) ∈ Subgroup.normalizer (W₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · exact key x hxN g
      · intro hg
        have h2 := key x⁻¹ (inv_mem hxN) _ hg
        have e : ((x⁻¹ : ↥W₁) : G) * ((x : G) * g * (x : G)⁻¹) * ((x⁻¹ : ↥W₁) : G)⁻¹ = g := by
          simp only [Subgroup.coe_inv]
          group
        rwa [e] at h2
    have hxNW : (x : G) ∈ W₁ ⊓ Subgroup.normalizer (W₀ : Set G) := ⟨x.2, hxN'⟩
    rw [hEq] at hxNW
    exact hxH (Subgroup.mem_subgroupOf.mpr hxNW)
  · constructor
    intro n hn g
    have hg0 : (g : G) ∈ Subgroup.normalizer (W₀ : Set G) := by
      have hgW : (g : G) ∈ W₁ ⊓ Subgroup.normalizer (W₀ : Set G) := by
        rw [hEq]
        exact g.2
      exact hgW.2
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp hg0 (n : G)).mp hn

@[expose] def ch827ConjSub (W : Subgroup G) {l : G} (hl : l ∈ Subgroup.normalizer (W : Set G)) :
    ↥W →* ↥W where
  toFun w := ⟨l * (w : G) * l⁻¹, (Subgroup.mem_normalizer_iff.mp hl (w : G)).mp w.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

abbrev ch827Quot (W₀ W₁ : Subgroup G) : Type := ↥W₁ ⧸ W₀.subgroupOf W₁

@[expose] def ch827ConjQ (W₀ W₁ : Subgroup G) [hN : (W₀.subgroupOf W₁).Normal] {l : G}
    (hl1 : l ∈ Subgroup.normalizer (W₁ : Set G)) (hl0 : l ∈ Subgroup.normalizer (W₀ : Set G)) :
    ch827Quot W₀ W₁ →* ch827Quot W₀ W₁ :=
  QuotientGroup.map (W₀.subgroupOf W₁) (W₀.subgroupOf W₁) (ch827ConjSub W₁ hl1)
    (fun w hw => by
      rw [Subgroup.mem_comap]
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hl0 (w : G)).mp (Subgroup.mem_subgroupOf.mp hw)))

@[expose] def ch827CQ (Λ W₀ W₁ : Subgroup G) [hN : (W₀.subgroupOf W₁).Normal]
    (hΛ1 : Λ ≤ Subgroup.normalizer (W₁ : Set G)) (hΛ0 : Λ ≤ Subgroup.normalizer (W₀ : Set G))
    (l : Λ) : ch827Quot W₀ W₁ →* ch827Quot W₀ W₁ :=
  ch827ConjQ W₀ W₁ (hΛ1 l.2) (hΛ0 l.2)

theorem ch827CQ_mk (Λ W₀ W₁ : Subgroup G) [hN : (W₀.subgroupOf W₁).Normal]
    (hΛ1 : Λ ≤ Subgroup.normalizer (W₁ : Set G)) (hΛ0 : Λ ≤ Subgroup.normalizer (W₀ : Set G))
    (l : Λ) (w : ↥W₁) :
    ch827CQ Λ W₀ W₁ hΛ1 hΛ0 l (w : ch827Quot W₀ W₁) =
      ((ch827ConjSub W₁ (hΛ1 l.2) w : ↥W₁) : ch827Quot W₀ W₁) :=
  rfl

theorem ch827CQ_mul (Λ W₀ W₁ : Subgroup G) [hN : (W₀.subgroupOf W₁).Normal]
    (hΛ1 : Λ ≤ Subgroup.normalizer (W₁ : Set G)) (hΛ0 : Λ ≤ Subgroup.normalizer (W₀ : Set G))
    (l l' : Λ) (q : ch827Quot W₀ W₁) :
    ch827CQ Λ W₀ W₁ hΛ1 hΛ0 (l * l') q =
      ch827CQ Λ W₀ W₁ hΛ1 hΛ0 l (ch827CQ Λ W₀ W₁ hΛ1 hΛ0 l' q) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  rw [ch827CQ_mk, ch827CQ_mk, ch827CQ_mk]
  congr 1
  apply Subtype.ext
  simp only [ch827ConjSub, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul]
  group

theorem ch827CQ_one (Λ W₀ W₁ : Subgroup G) [hN : (W₀.subgroupOf W₁).Normal]
    (hΛ1 : Λ ≤ Subgroup.normalizer (W₁ : Set G)) (hΛ0 : Λ ≤ Subgroup.normalizer (W₀ : Set G))
    (q : ch827Quot W₀ W₁) : ch827CQ Λ W₀ W₁ hΛ1 hΛ0 1 q = q := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  rw [ch827CQ_mk]
  congr 1
  apply Subtype.ext
  simp [ch827ConjSub]

theorem ch827_nontrivial_quot {W₀ W₁ : Subgroup G} [(W₀.subgroupOf W₁).Normal] (hW0W1 : W₀ < W₁) :
    Nontrivial (ch827Quot W₀ W₁) := by
  obtain ⟨x0, hx0W1, hx0W0⟩ := SetLike.exists_of_lt hW0W1
  refine ⟨⟨((⟨x0, hx0W1⟩ : ↥W₁) : ch827Quot W₀ W₁), 1, fun h => hx0W0 ?_⟩⟩
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)

theorem ch827CQ_inv (Λ W₀ W₁ : Subgroup G) [hN : (W₀.subgroupOf W₁).Normal]
    (hΛ1 : Λ ≤ Subgroup.normalizer (W₁ : Set G)) (hΛ0 : Λ ≤ Subgroup.normalizer (W₀ : Set G))
    (l : Λ) (q : ch827Quot W₀ W₁) :
    ch827CQ Λ W₀ W₁ hΛ1 hΛ0 l (ch827CQ Λ W₀ W₁ hΛ1 hΛ0 l⁻¹ q) = q := by
  rw [← ch827CQ_mul, mul_inv_cancel, ch827CQ_one]

theorem ch827_comm_quot [Finite G] {Λ W₀ W₁ : Subgroup G} [hN : (W₀.subgroupOf W₁).Normal]
    (hW0W1 : W₀ < W₁) (hP : IsPGroup 2 W₁) (hΛ0 : Λ ≤ Subgroup.normalizer (W₀ : Set G))
    (hΛ1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (hch : ∀ B : Subgroup G, W₀ ≤ B → B ≤ W₁ →
      Λ ≤ Subgroup.normalizer (B : Set G) → B = W₀ ∨ B = W₁) :
    ∀ a b : ch827Quot W₀ W₁, a * b = b * a := by
  classical
  obtain ⟨n, hn⟩ := hP.index (W₀.subgroupOf W₁)
  have hcard : Nat.card (ch827Quot W₀ W₁) = 2 ^ n := by
    rw [← hn, Subgroup.index_eq_card]
  have hQp : IsPGroup 2 (ch827Quot W₀ W₁) := IsPGroup.iff_card.mpr ⟨n, hcard⟩
  haveI := ch827_nontrivial_quot hW0W1
  haveI := IsPGroup.center_nontrivial hQp
  obtain ⟨⟨z, hz⟩, hne⟩ := exists_ne (1 : Subgroup.center (ch827Quot W₀ W₁))
  have hz1 : z ≠ 1 := fun h => hne (Subtype.ext h)
  let M : Subgroup G :=
    { carrier := {g | ∃ h : ↥W₁, (h : G) = g ∧
        (h : ch827Quot W₀ W₁) ∈ Subgroup.center (ch827Quot W₀ W₁)}
      one_mem' := ⟨1, rfl, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩
        refine ⟨a * b, rfl, ?_⟩
        rw [QuotientGroup.mk_mul]
        exact Subgroup.mul_mem _ ha hb
      inv_mem' := by
        rintro _ ⟨a, rfl, ha⟩
        refine ⟨a⁻¹, rfl, ?_⟩
        rw [QuotientGroup.mk_inv]
        exact Subgroup.inv_mem _ ha }
  have hM : ∀ g : G, g ∈ M ↔ ∃ h : ↥W₁, (h : G) = g ∧
      (h : ch827Quot W₀ W₁) ∈ Subgroup.center (ch827Quot W₀ W₁) := fun g => Iff.rfl
  have hcen : ∀ l : Λ, ∀ q ∈ Subgroup.center (ch827Quot W₀ W₁),
      ch827CQ Λ W₀ W₁ hΛ1 hΛ0 l q ∈ Subgroup.center (ch827Quot W₀ W₁) := by
    intro l q hq
    rw [Subgroup.mem_center_iff] at hq ⊢
    intro r
    have hr : r = ch827CQ Λ W₀ W₁ hΛ1 hΛ0 l (ch827CQ Λ W₀ W₁ hΛ1 hΛ0 l⁻¹ r) :=
      (ch827CQ_inv Λ W₀ W₁ hΛ1 hΛ0 l r).symm
    rw [hr, ← map_mul, ← map_mul, hq]
  have hfwd : ∀ l ∈ Λ, ∀ g ∈ M, l * g * l⁻¹ ∈ M := by
    rintro l hl g ⟨h, rfl, hh⟩
    refine ⟨ch827ConjSub W₁ (hΛ1 hl) h, rfl, ?_⟩
    have := hcen ⟨l, hl⟩ _ hh
    rwa [ch827CQ_mk] at this
  have hΛM : Λ ≤ Subgroup.normalizer (M : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hfwd l hl g
    · intro hg
      have h2 := hfwd l⁻¹ (inv_mem hl) _ hg
      simpa [mul_assoc] using h2
  have hMW0 : W₀ ≤ M := by
    intro g hg
    refine ⟨⟨g, hW0W1.le hg⟩, rfl, ?_⟩
    have h1 : ((⟨g, hW0W1.le hg⟩ : ↥W₁) : ch827Quot W₀ W₁) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hg)
    rw [h1]
    exact Subgroup.one_mem _
  have hMW1 : M ≤ W₁ := by
    rintro g ⟨h, rfl, -⟩
    exact h.2
  rcases hch M hMW0 hMW1 hΛM with hM0 | hM1
  · exfalso
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
    have hh : (h : G) ∈ M := (hM _).mpr ⟨h, rfl, hz⟩
    rw [hM0] at hh
    exact hz1 ((QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hh))
  · have hall : ∀ a : ch827Quot W₀ W₁, a ∈ Subgroup.center (ch827Quot W₀ W₁) := by
      intro a
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective a
      have hh : (h : G) ∈ M := by
        rw [hM1]
        exact h.2
      obtain ⟨h', hh', hmem⟩ := (hM _).mp hh
      have : h' = h := Subtype.ext hh'
      rw [← this]
      exact hmem
    intro a b
    exact ((Subgroup.mem_center_iff.mp (hall a)) b).symm

theorem ch827_exp2_quot [Finite G] {Λ W₀ W₁ : Subgroup G} [hN : (W₀.subgroupOf W₁).Normal]
    (hW0W1 : W₀ < W₁) (hP : IsPGroup 2 W₁) (hΛ0 : Λ ≤ Subgroup.normalizer (W₀ : Set G))
    (hΛ1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (hch : ∀ B : Subgroup G, W₀ ≤ B → B ≤ W₁ →
      Λ ≤ Subgroup.normalizer (B : Set G) → B = W₀ ∨ B = W₁)
    (hcomm : ∀ a b : ch827Quot W₀ W₁, a * b = b * a) :
    ∀ a : ch827Quot W₀ W₁, a ^ 2 = 1 := by
  classical
  letI : CommGroup (ch827Quot W₀ W₁) :=
    { (inferInstance : Group (ch827Quot W₀ W₁)) with mul_comm := hcomm }
  obtain ⟨n, hn⟩ := hP.index (W₀.subgroupOf W₁)
  have hcard : Nat.card (ch827Quot W₀ W₁) = 2 ^ n := by
    rw [← hn, Subgroup.index_eq_card]
  haveI := ch827_nontrivial_quot hW0W1
  have h2dvd : 2 ∣ Nat.card (ch827Quot W₀ W₁) := by
    have h1 : 1 < Nat.card (ch827Quot W₀ W₁) := Finite.one_lt_card
    rw [hcard] at h1 ⊢
    have hn0 : n ≠ 0 := by
      rintro rfl
      norm_num at h1
    exact dvd_pow_self 2 hn0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  let M : Subgroup G :=
    { carrier := {g | ∃ h : ↥W₁, (h : G) = g ∧ (h : ch827Quot W₀ W₁) ^ 2 = 1}
      one_mem' := ⟨1, rfl, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩
        refine ⟨a * b, rfl, ?_⟩
        rw [QuotientGroup.mk_mul, mul_pow, ha, hb, one_mul]
      inv_mem' := by
        rintro _ ⟨a, rfl, ha⟩
        refine ⟨a⁻¹, rfl, ?_⟩
        rw [QuotientGroup.mk_inv, inv_pow, ha, inv_one] }
  have hM : ∀ g : G, g ∈ M ↔ ∃ h : ↥W₁, (h : G) = g ∧ (h : ch827Quot W₀ W₁) ^ 2 = 1 :=
    fun g => Iff.rfl
  have hfwd : ∀ l ∈ Λ, ∀ g ∈ M, l * g * l⁻¹ ∈ M := by
    rintro l hl g ⟨h, rfl, hh⟩
    refine ⟨ch827ConjSub W₁ (hΛ1 hl) h, rfl, ?_⟩
    rw [← ch827CQ_mk Λ W₀ W₁ hΛ1 hΛ0 ⟨l, hl⟩ h, ← map_pow, hh, map_one]
  have hΛM : Λ ≤ Subgroup.normalizer (M : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hfwd l hl g
    · intro hg
      have h2 := hfwd l⁻¹ (inv_mem hl) _ hg
      simpa [mul_assoc] using h2
  have hMW0 : W₀ ≤ M := by
    intro g hg
    refine ⟨⟨g, hW0W1.le hg⟩, rfl, ?_⟩
    have h1 : ((⟨g, hW0W1.le hg⟩ : ↥W₁) : ch827Quot W₀ W₁) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hg)
    rw [h1, one_pow]
  have hMW1 : M ≤ W₁ := by
    rintro g ⟨h, rfl, -⟩
    exact h.2
  rcases hch M hMW0 hMW1 hΛM with hM0 | hM1
  · exfalso
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective y
    have hyy : (h : ch827Quot W₀ W₁) ^ 2 = 1 := by
      rw [hh]
      have := pow_orderOf_eq_one y
      rwa [hy] at this
    have hmemM : (h : G) ∈ M := (hM _).mpr ⟨h, rfl, hyy⟩
    rw [hM0] at hmemM
    have h1 : (h : ch827Quot W₀ W₁) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hmemM)
    rw [hh] at h1
    rw [h1, orderOf_one] at hy
    norm_num at hy
  · intro a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective a
    have hmemM : (h : G) ∈ M := by
      rw [hM1]
      exact h.2
    obtain ⟨h', hh', hsq⟩ := (hM _).mp hmemM
    have : h' = h := Subtype.ext hh'
    rw [← this]
    exact hsq

theorem ch827_pi_one {W : Type} [AddCommGroup W] (W₁ : Subgroup G) (π : ↥W₁ → W)
    (hπ : ∀ a b : ↥W₁, π (a * b) = π a + π b) : π 1 = 0 := by
  have h := hπ 1 1
  rw [mul_one] at h
  simpa using h

theorem ch827_pi_inv {W : Type} [AddCommGroup W] (W₁ : Subgroup G) (π : ↥W₁ → W)
    (hπ : ∀ a b : ↥W₁, π (a * b) = π a + π b) (a : ↥W₁) : π a⁻¹ = -π a := by
  have h := hπ a a⁻¹
  rw [mul_inv_cancel, ch827_pi_one W₁ π hπ] at h
  exact eq_neg_of_add_eq_zero_right h.symm

@[expose] def ch827Preim {W : Type} [AddCommGroup W] [Module (ZMod 2) W] (W₁ : Subgroup G)
    (π : ↥W₁ → W) (hπ : ∀ a b : ↥W₁, π (a * b) = π a + π b) (S : Submodule (ZMod 2) W) :
    Subgroup G where
  carrier := {g | ∃ h : ↥W₁, (h : G) = g ∧ π h ∈ S}
  one_mem' := ⟨1, rfl, by rw [ch827_pi_one W₁ π hπ]; exact S.zero_mem⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩
    refine ⟨a * b, rfl, ?_⟩
    rw [hπ]
    exact S.add_mem ha hb
  inv_mem' := by
    rintro _ ⟨a, rfl, ha⟩
    refine ⟨a⁻¹, rfl, ?_⟩
    rw [ch827_pi_inv W₁ π hπ]
    exact S.neg_mem ha

theorem mem_ch827Preim {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {W₁ : Subgroup G}
    {π : ↥W₁ → W} {hπ : ∀ a b : ↥W₁, π (a * b) = π a + π b} {S : Submodule (ZMod 2) W}
    {g : G} : g ∈ ch827Preim W₁ π hπ S ↔ ∃ h : ↥W₁, (h : G) = g ∧ π h ∈ S :=
  Iff.rfl

theorem ch827_two_dvd_natCard (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Nontrivial W] : 2 ∣ Nat.card W := by
  have h1 : 1 < Nat.card W := Finite.one_lt_card
  have h2 : Nat.card W = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) W :=
    Module.natCard_eq_pow_finrank
  rw [Nat.card_zmod] at h2
  rcases Nat.eq_zero_or_pos (Module.finrank (ZMod 2) W) with h0 | hpos
  · rw [h0, pow_zero] at h2
    omega
  · rw [h2]
    exact dvd_pow_self 2 (by omega)

theorem ch827_exists_fixed_ne_zero {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Nontrivial W] (P : Type) [Group P] (hP : IsPGroup 2 P) [MulAction P W]
    (h0 : ∀ g : P, g • (0 : W) = 0) : ∃ w : W, w ≠ 0 ∧ ∀ g : P, g • w = w := by
  classical
  by_contra hcon
  have hsub : ∀ w ∈ MulAction.fixedPoints P W, w = 0 := by
    intro w hw
    by_contra hw0
    exact hcon ⟨w, hw0, MulAction.mem_fixedPoints.mp hw⟩
  have h1 : Nat.card (MulAction.fixedPoints P W) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((hsub a a.2).trans (hsub b b.2).symm)⟩,
      ⟨⟨0, MulAction.mem_fixedPoints.mpr h0⟩⟩⟩
  have hmod := hP.card_modEq_card_fixedPoints W
  rw [h1] at hmod
  have h2 := ch827_two_dvd_natCard W
  unfold Nat.ModEq at hmod
  omega

end CFSG.Quasithin.H13.L827X.LBModule2
