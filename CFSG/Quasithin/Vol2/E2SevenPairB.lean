module

public import CFSG.Quasithin.Vol2.E2SevenPair

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_commutator_eq_bot {A B : Subgroup G} (h : ⁅A, B⁆ = ⊥) :
    A ≤ Subgroup.normalizer (B : Set G) := fun _ ha =>
  mem_normalizer_of_forall_commute fun _ hb => commute_of_commutator_eq_bot h ha hb

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_le_normalizer {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAB] at hx'
  obtain ⟨a, ha, b, hb, hab⟩ := hx'
  exact ⟨a, ha, b, hb, hab.symm⟩

omit [Finite G] in
theorem mem_normalizer_inf_of_mem {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro z
  exact and_congr (hA z) (hB z)

theorem proj_le_inf_centralizer {A B T V : Subgroup G} (hAB : ⁅A, B⁆ = ⊥) (hinf : A ⊓ B = ⊥)
    (hVN : V ≤ A ⊔ B) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hVc : ∀ v ∈ V, ∀ x ∈ T ⊓ A, v * x = x * v) (hS : IsSylowTwoOf (T ⊓ A) A) :
    A ⊓ (V ⊔ B) ≤ T ⊓ A ∧
      A ⊓ (V ⊔ B) ≤ Subgroup.centralizer ((T ⊓ A : Subgroup G) : Set G) ∧
      ∀ a ∈ A ⊓ (V ⊔ B), a ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBN : A ⊔ B ≤ Subgroup.normalizer (B : Set G) :=
    sup_le (le_normalizer_of_commutator_eq_bot hAB) Subgroup.le_normalizer
  have key : ∀ a ∈ A ⊓ (V ⊔ B), (∀ x ∈ T ⊓ A, x * a = a * x) ∧ a ^ 2 = 1 := by
    rintro a ⟨haA, haV⟩
    obtain ⟨v, hv, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer (hVN.trans hBN) haV
    refine ⟨fun x hx => ?_, ?_⟩
    · have h1 := hVc v hv x hx
      have h2 : x * b = b * x := commute_of_commutator_eq_bot hAB hx.2 hb
      calc x * (v * b) = (x * v) * b := by group
        _ = (v * x) * b := by rw [← h1]
        _ = v * (x * b) := by group
        _ = v * (b * x) := by rw [h2]
        _ = v * b * x := by group
    · have hc : (v * b) * b⁻¹ = b⁻¹ * (v * b) :=
        commute_of_commutator_eq_bot hAB haA (B.inv_mem hb)
      have hv' : v = (v * b) * b⁻¹ := by group
      have h1 : (v * b) ^ 2 * (b⁻¹) ^ 2 = 1 := by
        rw [← Commute.mul_pow hc 2, ← hv']
        exact hV2 v hv
      have h2 : (v * b) ^ 2 = ((b⁻¹) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : (v * b) ^ 2 ∈ A ⊓ B :=
        ⟨A.pow_mem haA 2, by rw [h2]; exact B.inv_mem (B.pow_mem (B.inv_mem hb) 2)⟩
      rw [hinf, Subgroup.mem_bot] at h3
      exact h3
  refine ⟨fun a ha => ?_, fun a ha => Subgroup.mem_centralizer_iff.mpr (key a ha).1,
    fun a ha => (key a ha).2⟩
  obtain ⟨hc, ha2⟩ := key a ha
  have hoa : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha2
  have hza : IsPGroup 2 (Subgroup.zpowers a) := fun g => ⟨1, Subtype.ext (by
    simpa using orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers g.2).trans hoa))⟩
  have hN : Subgroup.zpowers a ≤ Subgroup.normalizer ((T ⊓ A : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_of_forall_commute fun u hu => (hc u hu).symm)
  have hsup := IsPGroup.to_sup_of_normal_right' hza hS.2.1 hN
  have hle : Subgroup.zpowers a ⊔ (T ⊓ A) ≤ A := sup_le (Subgroup.zpowers_le.mpr ha.1) inf_le_right
  exact (A4.isSylowTwoOf_iff_maximal.mp hS).2.2 _ hle hsup le_sup_right
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))

omit [Finite G] in
theorem sup_conjSub_eq_sup_proj {K L V I₁ : Subgroup G} (hKL : ⁅K, L⁆ = ⊥) (hinf : K ⊓ L = ⊥)
    (hVN : V ≤ K ⊔ L) {h : G} (hhK : h ∈ K)
    (hI₁ : I₁ = K ⊓ (V ⊔ L) ⊔ conjSub h (K ⊓ (V ⊔ L)))
    (hc : ∀ a ∈ K ⊓ (V ⊔ L), ∀ b ∈ K ⊓ (V ⊔ L), a * b = b * a)
    (hs : IsSimpleGroup ↥I₁) (hnab : ∃ a b : ↥I₁, a * b ≠ b * a) :
    V ⊔ conjSub h V = I₁ ⊔ L ⊓ (V ⊔ K) := by
  set V₁ := K ⊓ (V ⊔ L) with hV₁
  set V₂ := L ⊓ (V ⊔ K) with hV₂
  have hLK : ⁅L, K⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hKL
  have hKNL := le_normalizer_of_commutator_eq_bot hKL
  have hLNK := le_normalizer_of_commutator_eq_bot hLK
  have hNK : K ⊔ L ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hLNK
  have hNL : K ⊔ L ≤ Subgroup.normalizer (L : Set G) := sup_le hKNL Subgroup.le_normalizer
  have hhN : ∀ X : Subgroup G, X ≤ L → conjSub h X = X := fun X hX =>
    conjSub_eq_self (mem_normalizer_of_forall_commute fun x hx =>
      commute_of_commutator_eq_bot hKL hhK (hX hx))
  have hhK' : conjSub h K = K := conjSub_eq_self (Subgroup.le_normalizer hhK)
  have hhKL : conjSub h (K ⊔ L) = K ⊔ L :=
    conjSub_eq_self (Subgroup.le_normalizer (Subgroup.mem_sup_left hhK))
  have hF1 : V ≤ V₁ ⊔ V₂ := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hKNL (hVN hv)
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ha, ?_⟩) (Subgroup.mem_sup_right ⟨hb, ?_⟩)
    · have := (V ⊔ L).mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right (L.inv_mem hb))
      simpa using this
    · have := (V ⊔ K).mul_mem (Subgroup.mem_sup_right (K.inv_mem ha)) (Subgroup.mem_sup_left hv)
      simpa using this
  have hV₁K : V₁ ≤ K := inf_le_left
  have hV₂L : V₂ ≤ L := inf_le_left
  have hI₁K : I₁ ≤ K := by
    rw [hI₁]
    refine sup_le hV₁K ?_
    rw [← hhK']
    exact (conjSub h).monotone hV₁K
  have hle : V ⊔ conjSub h V ≤ I₁ ⊔ V₂ := by
    have hV₁I₁ : V₁ ≤ I₁ := by rw [hI₁]; exact le_sup_left
    have h1 : V₁ ⊔ V₂ ≤ I₁ ⊔ V₂ := sup_le_sup_right hV₁I₁ _
    refine sup_le (hF1.trans h1) ?_
    calc conjSub h V ≤ conjSub h (V₁ ⊔ V₂) := (conjSub h).monotone hF1
      _ = conjSub h V₁ ⊔ conjSub h V₂ := map_sup (conjSub h) V₁ V₂
      _ = conjSub h V₁ ⊔ V₂ := by rw [hhN V₂ hV₂L]
      _ ≤ I₁ ⊔ V₂ := sup_le_sup_right (by rw [hI₁]; exact le_sup_right) _
  set I := V ⊔ conjSub h V with hIdef
  have hIKL : I ≤ K ⊔ L := sup_le hVN (by
    rw [← hhKL]
    exact (conjSub h).monotone hVN)
  set D := I ⊓ K with hD
  have hDI₁ : D ≤ I₁ := by
    rintro x ⟨hxI, hxK⟩
    have hxI' := hle hxI
    have hI₁NV₂ : I₁ ≤ Subgroup.normalizer (V₂ : Set G) := fun y hy =>
      mem_normalizer_of_forall_commute fun w hw =>
        commute_of_commutator_eq_bot hKL (hI₁K hy) (hV₂L hw)
    obtain ⟨y, hy, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hI₁NV₂ hxI'
    have hwK : w ∈ K := by
      have := K.mul_mem (K.inv_mem (hI₁K hy)) hxK
      simpa using this
    have : w ∈ K ⊓ L := ⟨hwK, hV₂L hw⟩
    rw [hinf, Subgroup.mem_bot] at this
    rw [this, mul_one]
    exact hy
  have hI₁IL : I₁ ≤ I ⊔ L := by
    rw [hI₁]
    refine sup_le ((inf_le_right).trans (sup_le_sup_right le_sup_left L)) ?_
    calc conjSub h V₁ ≤ conjSub h (V ⊔ L) := (conjSub h).monotone inf_le_right
      _ = conjSub h V ⊔ conjSub h L := map_sup (conjSub h) V L
      _ = conjSub h V ⊔ L := by rw [hhN L le_rfl]
      _ ≤ I ⊔ L := sup_le_sup_right le_sup_right _
  have hILN : I ⊔ L ≤ Subgroup.normalizer (D : Set G) := by
    refine sup_le (fun y hy => mem_normalizer_inf_of_mem (Subgroup.le_normalizer hy)
      (hNK (hIKL hy))) (fun y hy => mem_normalizer_of_forall_commute fun x hx =>
        (commute_of_commutator_eq_bot hKL hx.2 hy).symm)
  have hDn : (D.subgroupOf I₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDI₁).mpr (hI₁IL.trans hILN)
  have hDne : D ≠ ⊥ := by
    intro hD0
    obtain ⟨x, y, hxy⟩ := hnab
    apply hxy
    have hcomm : ∀ a ∈ V₁, h * a = a * h := by
      intro a ha
      obtain ⟨v, hv, b, hb, hab⟩ :=
        exists_mul_of_mem_sup_of_le_normalizer (hVN.trans hNL) ha.2
      have hbh : h * b = b * h := commute_of_commutator_eq_bot hKL hhK hb
      have hvI : v ∈ I := Subgroup.mem_sup_left hv
      have hvhI : h * v * h⁻¹ ∈ I := Subgroup.mem_sup_right (by
        rw [mem_conjSub]
        simpa [mul_assoc] using hv)
      have hd : v * (h * v * h⁻¹)⁻¹ = a * (h * a * h⁻¹)⁻¹ := by
        rw [hab]
        calc v * (h * v * h⁻¹)⁻¹ = v * h * v⁻¹ * h⁻¹ := by group
          _ = v * (h * b) * b⁻¹ * v⁻¹ * h⁻¹ := by group
          _ = v * (b * h) * b⁻¹ * v⁻¹ * h⁻¹ := by rw [hbh]
          _ = v * b * (h * (v * b) * h⁻¹)⁻¹ := by group
      have hdK : v * (h * v * h⁻¹)⁻¹ ∈ D := ⟨I.mul_mem hvI (I.inv_mem hvhI), by
        rw [hd]
        exact K.mul_mem ha.1 (K.inv_mem (K.mul_mem (K.mul_mem hhK ha.1) (K.inv_mem hhK)))⟩
      rw [hD0, Subgroup.mem_bot, hd, mul_inv_eq_one] at hdK
      calc h * a = h * a * h⁻¹ * h := by group
        _ = a * h := by rw [← hdK]
    have hV₁h : conjSub h V₁ = V₁ := conjSub_eq_self (mem_normalizer_of_forall_commute hcomm)
    have hI₁V₁ : I₁ = V₁ := by rw [hI₁, hV₁h, sup_idem]
    have hx : (x : G) ∈ V₁ := hI₁V₁ ▸ x.2
    have hy : (y : G) ∈ V₁ := hI₁V₁ ▸ y.2
    exact Subtype.ext (hc _ hx _ hy)
  have hDeq : I₁ ≤ I := by
    rcases hs.eq_bot_or_eq_top_of_normal (D.subgroupOf I₁) with h0 | h0
    · exfalso
      apply hDne
      rw [Subgroup.subgroupOf_eq_bot] at h0
      exact eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr
        ((Subgroup.disjoint_def.mp h0) hx (hDI₁ hx))
    · rw [Subgroup.subgroupOf_eq_top] at h0
      exact h0.trans inf_le_left
  have hV₂I : V₂ ≤ I := by
    rintro b ⟨hbL, hbV⟩
    obtain ⟨v, hv, k, hk, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer (hVN.trans hNK) hbV
    have hkV₁ : k ∈ V₁ := ⟨hk, by
      have := (V ⊔ L).mul_mem (Subgroup.mem_sup_left (V.inv_mem hv)) (Subgroup.mem_sup_right hbL)
      simpa using this⟩
    have hkI₁ : k ∈ I₁ := by rw [hI₁]; exact Subgroup.mem_sup_left hkV₁
    exact I.mul_mem (Subgroup.mem_sup_left hv) (hDeq hkI₁)
  exact le_antisymm hle (sup_le hDeq hV₂I)

omit [Finite G] in
theorem isBorelIn_top_subgroupOf {I S B : Subgroup G} (hS : IsSylowTwoOf S I)
    (hB : B = I ⊓ Subgroup.normalizer (S : Set G)) : IsBorelIn ⊤ (B.subgroupOf I) := by
  refine ⟨S.subgroupOf I, ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩,
    ?_⟩
  · have e1 : ((S.subgroupOf I).subgroupOf ⊤).index = (S.subgroupOf I).index :=
      Subgroup.relIndex_top_right _
    rw [e1]
    exact hS.2.2
  · rw [top_inf_eq, hB]
    ext y
    constructor
    · intro hy
      replace hy : (y : G) ∈ Subgroup.normalizer (S : Set G) := (Subgroup.mem_subgroupOf.mp hy).2
      rw [Subgroup.mem_normalizer_iff]
      intro z
      exact Subgroup.mem_normalizer_iff.mp hy z
    · intro hy
      show (y : G) ∈ I ⊓ Subgroup.normalizer (S : Set G)
      refine ⟨y.2, ?_⟩
      show (y : G) ∈ Subgroup.normalizer (S : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have hzI := hS.1 hz
        exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hy ⟨z, hzI⟩).mp
          (Subgroup.mem_subgroupOf.mpr hz))
      · intro hz
        have hzI : z ∈ I := by
          have := I.mul_mem (I.mul_mem (I.inv_mem y.2) (hS.1 hz)) y.2
          simpa [mul_assoc] using this
        exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hy ⟨z, hzI⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hz))

theorem isInIHTVC_of_simple_mul {H T M V I I₁ U : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTM : T ≤ M) (hIH : I ≤ H) {h : G} (hhI : h ∈ I) (hI : I = V ⊔ conjSub h V)
    (hIU : I = I₁ ⊔ U) (hUc : ∀ x ∈ I₁, ∀ u ∈ U, x * u = u * x)
    (hU2 : IsPGroup 2 U) (hUT : U ≤ T) (hsyl : IsSylowTwoOf (T ⊓ I₁) I₁) (hT1 : T ⊓ I₁ ≠ ⊥)
    {k : ℕ} (hk : 1 < k) (hY : IsPSL 2 2 k ↥I₁ ∨ IsSz k ↥I₁)
    (hMI : M ⊓ I₁ = I₁ ⊓ Subgroup.normalizer ((T ⊓ I₁ : Subgroup G) : Set G))
    (hn : ∃ m : ℕ, E1.nParam H = ((k * m : ℕ) : ℕ∞)) : ASInputs.IsInIHTVC H T M V I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := isSimpleGroup_of_psl_or_sz hY
  have hnab := nonabelian_of_psl_or_sz hk hY
  have hI₁I : I₁ ≤ I := by rw [hIU]; exact le_sup_left
  have hUI : U ≤ I := by rw [hIU]; exact le_sup_right
  have hI₁NU : I₁ ≤ Subgroup.normalizer (U : Set G) := fun x hx =>
    mem_normalizer_of_forall_commute fun u hu => hUc x hx u hu
  have hUNI₁ : U ≤ Subgroup.normalizer (I₁ : Set G) := fun u hu =>
    mem_normalizer_of_forall_commute fun x hx => (hUc x hx u hu).symm
  have hINU : I ≤ Subgroup.normalizer (U : Set G) := by
    rw [hIU]
    exact sup_le hI₁NU Subgroup.le_normalizer
  have hINI₁ : I ≤ Subgroup.normalizer (I₁ : Set G) := by
    rw [hIU]
    exact sup_le Subgroup.le_normalizer hUNI₁
  have hdec : ∀ x ∈ I, ∃ y ∈ I₁, ∃ u ∈ U, x = y * u := fun x hx =>
    exists_mul_of_mem_sup_of_le_normalizer hI₁NU (by rw [← hIU]; exact hx)
  have hUker : U ≤ kerIn (M ⊓ I) I := le_kerIn_of_le_normalizer (le_inf (hUT.trans hTM) hUI) hINU
  have hkerI : kerIn (M ⊓ I) I ≤ I := kerIn_le.trans inf_le_right
  have hkerN : I ≤ Subgroup.normalizer (kerIn (M ⊓ I) I : Set G) := le_normalizer_kerIn (M ⊓ I) I
  have hkerI₁ : kerIn (M ⊓ I) I ⊓ I₁ = ⊥ := by
    have hnorm : ((kerIn (M ⊓ I) I ⊓ I₁).subgroupOf I₁).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun x hx =>
        mem_normalizer_inf_of_mem (hkerN (hI₁I hx)) (Subgroup.le_normalizer hx)
    rcases hs.eq_bot_or_eq_top_of_normal ((kerIn (M ⊓ I) I ⊓ I₁).subgroupOf I₁) with h0 | h0
    · rw [Subgroup.subgroupOf_eq_bot] at h0
      exact eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr
        ((Subgroup.disjoint_def.mp h0) hx hx.2)
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h0
      have hI₁M : I₁ ≤ M := fun x hx => (kerIn_le (h0 hx).1).1
      obtain ⟨g, hgI, hgN⟩ := exists_not_mem_normalizer_of_simple hs hnab hsyl hT1
      have : g ∈ M ⊓ I₁ := ⟨hI₁M hgI, hgI⟩
      rw [hMI] at this
      exact hgN this.2
  have hkerU : kerIn (M ⊓ I) I = U := by
    refine le_antisymm (fun x hx => ?_) hUker
    obtain ⟨y, hy, u, hu, rfl⟩ := hdec x (hkerI hx)
    have hyk : y ∈ kerIn (M ⊓ I) I := by
      have := (kerIn (M ⊓ I) I).mul_mem hx ((kerIn (M ⊓ I) I).inv_mem (hUker hu))
      simpa using this
    have : y ∈ kerIn (M ⊓ I) I ⊓ I₁ := ⟨hyk, hy⟩
    rw [hkerI₁, Subgroup.mem_bot] at this
    rw [this, one_mul]
    exact hu
  have hTI : (T ⊓ I) ⊓ I₁ = T ⊓ I₁ := by rw [inf_assoc, inf_eq_right.mpr hI₁I]
  have hsylI : IsSylowTwoOf (T ⊓ I) I := by
    refine isSylowTwoOf_of_sup inf_le_right hI₁I (inf_le_right.trans hINI₁)
      (hT2.to_le inf_le_left) (by rw [hTI]; exact hsyl) ?_
    have hsup : (T ⊓ I) ⊔ I₁ = I := le_antisymm (sup_le inf_le_right hI₁I) (by
      rw [hIU]
      exact sup_le le_sup_right (le_sup_of_le_left (le_inf hUT le_sup_right)))
    rw [hsup, Subgroup.relIndex_self]
    norm_num
  have h2cl : IsSylowTwoOf (pCoreOf 2 (kerIn (M ⊓ I) I)) (kerIn (M ⊓ I) I) := by
    rw [hkerU]
    have hKK : pCoreOf 2 U = U :=
      le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 U)
        (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hU2)
    rw [hKK]
    refine ⟨le_rfl, hU2, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    norm_num
  set φ : ↥I₁ →* StarQuot (M ⊓ I) I :=
    (QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I)).comp (Subgroup.inclusion hI₁I) with hφ
  have hφeq : ∀ (x : ↥I) (y : G) (hy : y ∈ I₁) (u : G), u ∈ U → (x : G) = y * u →
      φ ⟨y, hy⟩ = QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) x := by
    intro x y hy u hu hxyu
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (((Subgroup.inclusion hI₁I ⟨y, hy⟩)⁻¹ * x : ↥I) : G) = u := by
      simp [hxyu]
    rw [e]
    exact hUker hu
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy
    have : (y : G) ∈ kerIn (M ⊓ I) I ⊓ I₁ := ⟨hy, y.2⟩
    rw [hkerI₁, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hφsurj : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨y, hy, u, hu, hxyu⟩ := hdec x x.2
    exact ⟨⟨y, hy⟩, hφeq x y hy u hu hxyu⟩
  set e := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩ with he
  have hYs : IsPSL 2 2 k (StarQuot (M ⊓ I) I) ∨ IsSz k (StarQuot (M ⊓ I) I) :=
    hY.imp (isPSL_of_mulEquiv e.symm) (isSz_of_mulEquiv' e.symm)
  have hstar : star (M ⊓ I) I (M ⊓ I) = ((M ⊓ I₁).subgroupOf I₁).map e.toMonoidHom := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      replace hx : (x : G) ∈ M ⊓ I := Subgroup.mem_subgroupOf.mp hx
      obtain ⟨y, hy, u, hu, hxyu⟩ := hdec x x.2
      have hyM : y ∈ M := by
        have e1 : y = (x : G) * u⁻¹ := by rw [hxyu]; group
        rw [e1]
        exact M.mul_mem hx.1 (M.inv_mem (hTM (hUT hu)))
      exact ⟨⟨y, hy⟩, Subgroup.mem_subgroupOf.mpr ⟨hyM, hy⟩, hφeq x y hy u hu hxyu⟩
    · rintro ⟨y, hy, rfl⟩
      replace hy : (y : G) ∈ M ⊓ I₁ := Subgroup.mem_subgroupOf.mp hy
      exact ⟨Subgroup.inclusion hI₁I y, Subgroup.mem_subgroupOf.mpr ⟨hy.1, hI₁I y.2⟩, rfl⟩
  have hBor : IsBorelIn ⊤ (star (M ⊓ I) I (M ⊓ I)) := by
    rw [hstar]
    apply isBorelIn_of_map_equiv e.symm
    rw [map_symm_map_equiv]
    exact isBorelIn_top_subgroupOf hsyl hMI
  exact ⟨hIH, ⟨h, hhI, hI⟩, hsylI, h2cl, k, hn, Or.inl ⟨hk, hYs, hBor⟩⟩

variable {H T M V : Subgroup G}

theorem exists_isInIHTVC_of_bender_two (hKG1 : KGBenderInnerTwo) (hKG2L2 : KGBenderSubL2)
    (hKG2Sz : KGBenderSubSz)
    (h : Hyp28 H T M V) (hJ : kerIn M H = ⊥) {K : Subgroup G} (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) {t : G} (htT : t ∈ T) (hne : cjSub t K ≠ K)
    (hM : M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T) {n : ℕ} (hn2 : 2 ≤ n)
    (hK : IsPSL 2 2 n ↥(star M H K) ∨ IsSz n ↥(star M H K))
    (hB : IsBorelIn (star M H K) (star M H (M ⊓ K))) (hnH : E1.nParam H = n)
    (hV4 : 4 ≤ Nat.card V) : ∃ I : Subgroup G, ASInputs.IsInIHTVC H T M V I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := h.minParabolic.isSylow.1
  have htH : t ∈ H := hTH htT
  have hP := pairCase_of h hJ hKc hHK htT hne (isSimpleGroup_of_psl_or_sz hK)
  have eK := equivStarOfKerInEqBot hJ hKH
  have hK' : IsPSL 2 2 n ↥K ∨ IsSz n ↥K := hK.imp (isPSL_of_mulEquiv eK) (isSz_of_mulEquiv' eK)
  have hMK := inf_eq_of_isBorelIn_star h.minParabolic hJ (subnormal_of_mem_cComp hKc) hKH hB
  set L := cjSub t K with hLdef
  obtain ⟨hO, hinv⟩ := hKG1 G H T M K t n h.minParabolic hJ htT hKH hne hP.norm hP.cent hP.inf
    hP.comm hHK.symm hn2 hK' hM hMK
  have hVN : V ≤ K ⊔ L := h.le_pCoreOf.trans hO
  have hVc : ∀ v ∈ V, ∀ x ∈ T ⊓ (K ⊔ L), v * x = x * v := fun v hv x hx =>
    ((Subgroup.mem_centralizer_iff.mp (hinv v ⟨h.le_T hv, hVN hv⟩ (h.elem.2 v hv))) x hx).symm
  have hS₁ : IsSylowTwoOf (T ⊓ K) K :=
    E2P.isSylowTwoOf_inf_of_subnormal h.minParabolic.isSylow (subnormal_of_mem_cComp hKc)
  have hS₂ : IsSylowTwoOf (T ⊓ L) L :=
    E2P.isSylowTwoOf_inf_of_subnormal h.minParabolic.isSylow (subnormal_of_mem_cComp hP.comp')
  have hLK : ⁅L, K⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hP.comm
  obtain ⟨hV₁S, hV₁C, hV₁2⟩ := proj_le_inf_centralizer hP.comm hP.inf hVN h.elem.2
    (fun v hv x hx => hVc v hv x ⟨hx.1, Subgroup.mem_sup_left hx.2⟩) hS₁
  obtain ⟨hV₂S, hV₂C, hV₂2⟩ := proj_le_inf_centralizer hLK (by rw [inf_comm]; exact hP.inf)
    (by rw [sup_comm]; exact hVN) h.elem.2
    (fun v hv x hx => hVc v hv x ⟨hx.1, Subgroup.mem_sup_right hx.2⟩) hS₂
  set V₁ := K ⊓ (V ⊔ L) with hV₁
  set V₂ := L ⊓ (V ⊔ K) with hV₂
  have hLt : cjSub t L = K := by
    rcases hP.orbit (t * t) (H.mul_mem htH htH) with h1 | h1
    · rw [hLdef, cjSub_cjSub]
      exact h1
    · exfalso
      apply hne
      have h3 := congrArg (cjSub t⁻¹) h1
      rw [cjSub_cjSub, cjSub_cjSub, inv_mul_cancel_left, inv_mul_cancel, cjSub_one] at h3
      exact h3
  have hVt : cjSub t V = V := Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.normal_T htT)
  have hV₂t : V₂ = cjSub t V₁ := by
    rw [hV₁, hV₂]
    show L ⊓ (V ⊔ K) = (K ⊓ (V ⊔ L)).map (MulAut.conj t).toMonoidHom
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective]
    change L ⊓ (V ⊔ K) = cjSub t K ⊓ cjSub t (V ⊔ L)
    rw [cjSub_sup, hVt, hLt]
  have hcard₂ : Nat.card V₂ = Nat.card V₁ := by rw [hV₂t, card_cjSub]
  have hKNL := le_normalizer_of_commutator_eq_bot hP.comm
  have hF1 : V ≤ V₁ ⊔ V₂ := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hKNL (hVN hv)
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ha, ?_⟩) (Subgroup.mem_sup_right ⟨hb, ?_⟩)
    · have := (V ⊔ L).mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right (L.inv_mem hb))
      simpa using this
    · have := (V ⊔ K).mul_mem (Subgroup.mem_sup_right (K.inv_mem ha)) (Subgroup.mem_sup_left hv)
      simpa using this
  have hV₁c : ∀ a ∈ V₁, ∀ b ∈ V₁, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hV₁C hb)) a (hV₁S ha)
  have hV₁p : IsPGroup 2 V₁ := fun x => ⟨1, Subtype.ext (by simpa using hV₁2 x x.2)⟩
  have hV₂p : IsPGroup 2 V₂ := fun x => ⟨1, Subtype.ext (by simpa using hV₂2 x x.2)⟩
  have hdisj : V₁ ⊓ V₂ = ⊥ := eq_bot_iff.mpr fun x hx => by
    have : x ∈ K ⊓ L := ⟨hx.1.1, hx.2.1⟩
    rwa [hP.inf] at this
  have hcard12 : Nat.card ↥(V₁ ⊔ V₂) = Nat.card V₁ * Nat.card V₂ :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer V₁ V₂
      (fun b hb => mem_normalizer_of_forall_commute fun a ha =>
        (commute_of_commutator_eq_bot hP.comm ha.1 hb.1).symm)
      (by rw [disjoint_iff]; exact hdisj)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV₁p
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  ·
    have hm1 : m = 1 := by
      rcases Nat.lt_or_ge m 1 with hm0 | hm1
      · exfalso
        have hm0' : m = 0 := by omega
        rw [hm0', pow_zero] at hm
        have h4 := Subgroup.card_le_of_le hF1
        rw [hcard12, hcard₂, hm] at h4
        omega
      · omega
    rw [hm1, pow_one] at hm
    have hVeq : V = V₁ ⊔ V₂ := Subgroup.eq_of_le_of_card_ge hF1 (by
      rw [hcard12, hcard₂, hm]
      omega)
    have hVK : V ⊓ K = V₁ := le_antisymm (fun x hx => ⟨hx.2, Subgroup.mem_sup_left hx.1⟩)
      (le_inf (le_sup_left.trans hVeq.ge) inf_le_left)
    have hVL : V ⊓ L = V₂ := le_antisymm (fun x hx => ⟨hx.2, Subgroup.mem_sup_left hx.1⟩)
      (le_inf (le_sup_right.trans hVeq.ge) inf_le_left)
    refine exists_isInIHTVC_of_pair_dihedral h hP ?_ (by rw [hVK, hm]) ⟨n, hnH⟩
    rw [hVK, hVL]
    exact hVeq
  ·
    have hV₁4 : 4 ≤ Nat.card V₁ := by
      rw [hm]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hV₁ne : V₁ ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hV₁4
      omega
    have hS1ne : T ⊓ K ≠ ⊥ := fun h0 => hV₁ne (le_bot_iff.mp (h0 ▸ hV₁S))
    obtain ⟨g₀, hg₀K, hg₀N⟩ := exists_not_mem_normalizer_of_simple hP.simple hP.nonab hS₁ hS1ne
    have hV₁elem : IsElemAbelian 2 V₁ :=
      ⟨Subgroup.le_centralizer_iff_isMulCommutative.mp fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun b hb => hV₁c b hb a ha, hV₁2⟩
    have hBenK : IsBenderOf n ↥K := ⟨hn2, hK'.elim Or.inl fun hsz => Or.inr (Or.inl hsz)⟩
    have hbK : ∀ g ∈ K, g ∉ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
        ∃ k : ℕ, 2 ≤ k ∧ k ∣ n ∧
          (IsPSL 2 2 k ↥(V₁ ⊔ conjSub g V₁) ∨ IsSz k ↥(V₁ ⊔ conjSub g V₁)) := by
      intro g hgK hgN
      rcases hK' with hL2 | hSz
      · exact hKG2L2 G K (T ⊓ K) V₁ n g hn2 hL2 hS₁ hV₁S hV₁C hV₁elem hV₁4 hgK hgN
      · exact hKG2Sz G K (T ⊓ K) V₁ n g hn2 hSz hS₁ hV₁S hV₁C hV₁elem hV₁4 hgK hgN
    obtain ⟨g, hgK, hgN, hsyl, ⟨k, hk2, hkn, hYk⟩, hBor, ⟨h', hh', hI₁h⟩⟩ :=
      exists_member_of_bender hBenK hS₁ hV₁S hV₁4 hg₀K hg₀N hbK
    set I₁ := V₁ ⊔ conjSub g V₁ with hI₁def
    have hgKN : g ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hgK
    have hI₁K : I₁ ≤ K := sup_le inf_le_left (by
      rw [← conjSub_eq_self hgKN]
      exact (conjSub g).monotone inf_le_left)
    have hsI₁ : IsSimpleGroup ↥I₁ := isSimpleGroup_of_psl_or_sz hYk
    have hnabI₁ := nonabelian_of_psl_or_sz (by omega) hYk
    have hh'K : h' ∈ K := hI₁K hh'
    have hIeq : V ⊔ conjSub h' V = I₁ ⊔ V₂ :=
      sup_conjSub_eq_sup_proj hP.comm hP.inf hVN hh'K hI₁h hV₁c hsI₁ hnabI₁
    have hV₁I₁ : V₁ ≤ I₁ := le_sup_left
    have hTI₁ : (T ⊓ K) ⊓ I₁ = T ⊓ I₁ := by rw [inf_assoc, inf_eq_right.mpr hI₁K]
    have hMI : M ⊓ I₁ = I₁ ⊓ Subgroup.normalizer ((T ⊓ I₁ : Subgroup G) : Set G) := by
      rw [← hTI₁, ← hBor, ← hMK, inf_assoc, inf_eq_right.mpr hI₁K]
    have hIH : I₁ ⊔ V₂ ≤ H := sup_le (hI₁K.trans hKH) ((inf_le_left).trans
      (le_of_mem_cComp hP.comp'))
    obtain ⟨m', hm'⟩ := hkn
    refine ⟨V ⊔ conjSub h' V, isInIHTVC_of_simple_mul h.minParabolic.isSylow.2.1
      h.minParabolic.le (hIeq ▸ hIH) (hIeq ▸ Subgroup.mem_sup_left hh') rfl hIeq ?_ hV₂p
      (hV₂S.trans inf_le_left) (by rw [← hTI₁]; exact hsyl) ?_ (by omega) hYk hMI
      ⟨m', by rw [hnH, hm']⟩⟩
    · exact fun x hx u hu => commute_of_commutator_eq_bot hP.comm (hI₁K hx) hu.1
    · intro h0
      apply hV₁ne
      exact le_bot_iff.mp (h0 ▸ le_inf (hV₁S.trans inf_le_left) hV₁I₁)

end E2

end CFSG.Quasithin
