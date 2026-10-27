module

public import CFSG.RankThree.GF2n.Tim77Prop24TwoD
public import CFSG.RankThree.GF2n.Tim77.Sec3Conj
public import CFSG.RankThree.GF2n.Tim77.Sec3Basic

public section

namespace CFSG.RankThree.GF2n.Tim77

variable {G : Type} [Group G]

theorem sec53_mul_mem_of_relIndex_two {A K : Subgroup G}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1)
    (hq : K.relIndex A = 2) {a b : G} (ha : a ∈ A) (hb : b ∈ A) (haK : a ∉ K) (hbK : b ∉ K) :
    a * b ∈ K := by
  have h2 : (K.subgroupOf A).index = 2 := hq
  obtain ⟨c, hc1, hc2⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp h2
  have key : ∀ d ∈ A, d ∉ K → d * (c : G) ∈ K := by
    intro d hd hdK
    rcases hc2 ⟨d, hd⟩ with h | h
    · exact Subgroup.mem_subgroupOf.mp h
    · exact absurd (Subgroup.mem_subgroupOf.mp h) hdK
  have hcA : (c : G) ∈ A := c.2
  have hcc : (c : G) * (c : G) = 1 := hsq _ hcA
  have e : a * (c : G) * (b * (c : G)) = a * b := by
    calc a * (c : G) * (b * (c : G)) = a * ((c : G) * b) * (c : G) := by group
      _ = a * (b * (c : G)) * (c : G) := by rw [hA _ hcA b hb]
      _ = a * b * ((c : G) * (c : G)) := by group
      _ = a * b := by rw [hcc, mul_one]
  rw [← e]
  exact K.mul_mem (key a ha haK) (key b hb hbK)

theorem sec53_commutator_mul_left {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {x : G} (hx : x ∈ Subgroup.normalizer (A : Set G)) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b * x * (a * b)⁻¹ * x⁻¹ = (a * x * a⁻¹ * x⁻¹) * (b * x * b⁻¹ * x⁻¹) := by
  have hconj : ∀ y ∈ A, x * y⁻¹ * x⁻¹ ∈ A := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hx y⁻¹).mp (A.inv_mem hy)
  have hα : x * a⁻¹ * x⁻¹ ∈ A := hconj a ha
  have hβ : x * b⁻¹ * x⁻¹ ∈ A := hconj b hb
  have hcomm : (b * (x * b⁻¹ * x⁻¹)) * (x * a⁻¹ * x⁻¹) =
      (x * a⁻¹ * x⁻¹) * (b * (x * b⁻¹ * x⁻¹)) :=
    hA _ (A.mul_mem hb hβ) _ hα
  calc a * b * x * (a * b)⁻¹ * x⁻¹
      = a * ((b * (x * b⁻¹ * x⁻¹)) * (x * a⁻¹ * x⁻¹)) := by group
    _ = a * ((x * a⁻¹ * x⁻¹) * (b * (x * b⁻¹ * x⁻¹))) := by rw [hcomm]
    _ = (a * x * a⁻¹ * x⁻¹) * (b * x * b⁻¹ * x⁻¹) := by group

theorem sec53_commutator_mul_right {t n m : G}
    (hnc : n * (t * m * t⁻¹ * m⁻¹) = (t * m * t⁻¹ * m⁻¹) * n) :
    t * (n * m) * t⁻¹ * (n * m)⁻¹ = (t * n * t⁻¹ * n⁻¹) * (t * m * t⁻¹ * m⁻¹) := by
  calc t * (n * m) * t⁻¹ * (n * m)⁻¹
      = (t * n * t⁻¹ * n⁻¹) * (n * (t * m * t⁻¹ * m⁻¹) * n⁻¹) := by group
    _ = (t * n * t⁻¹ * n⁻¹) * (t * m * t⁻¹ * m⁻¹) := by rw [hnc]; group

def sec53Chi [Finite G] {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M) {t : G}
    (ht : t ∈ A) : Lb →* L where
  toFun n := ⟨t * (n : G) * t⁻¹ * (n : G)⁻¹, S.commutator_mem_L ht n.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' n m := Subtype.ext (by
    show t * ((n : G) * (m : G)) * t⁻¹ * ((n : G) * (m : G))⁻¹ =
      (t * (n : G) * t⁻¹ * (n : G)⁻¹) * (t * (m : G) * t⁻¹ * (m : G)⁻¹)
    exact sec53_commutator_mul_right (S.comm_L_Lb (S.commutator_mem_L ht m.2) n.2).symm)

theorem sec53_hyperplane [Finite G] {A Ab L Lb M Ab' L' Lb' M' : Subgroup G}
    (S : Prop24Setup A Ab L Lb M) (S' : Prop24Setup A Ab' L' Lb' M') (hq : L.relIndex A = 2)
    (hq' : L'.relIndex A = 2) (hne : L' ≠ L) :
    ∃ F : Subgroup G, F ≤ Lb' ∧ F.relIndex Lb' = 2 ∧
      (∀ x ∈ F, ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ L ⊓ L') ∧
      F ≤ Subgroup.normalizer (L : Set G) ∧ (F = ⊥ ↔ Nat.card L = 2) := by
  have hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => S.comm_A hx hy
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => S.sq_A hx
  obtain ⟨t, ht, htL'⟩ : ∃ t ∈ A, t ∉ L' := by
    by_contra h
    push Not at h
    exact S'.ne (le_antisymm S'.L_le (fun x hx => h x hx))
  obtain ⟨l', hl'L', hl'L⟩ : ∃ l' ∈ L', l' ∉ L := by
    by_contra h
    push Not at h
    apply hne
    have hle : L' ≤ L := fun x hx => h x hx
    have e1 := Subgroup.relIndex_mul_relIndex (H := L') (K := L) (L := A) hle S.L_le
    rw [hq, hq'] at e1
    have h1 : L'.relIndex L = 1 := by omega
    exact le_antisymm hle ((Subgroup.relIndex_eq_one (H := L') (K := L)).mp h1)
  have hLL' : L.relIndex L' = 2 := by
    show (L.subgroupOf L').index = 2
    refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr ⟨⟨l', hl'L'⟩, ?_, ?_⟩
    · intro h
      exact hl'L (Subgroup.mem_subgroupOf.mp h)
    · intro d
      by_cases hdL : (d : G) ∈ L
      · exact Or.inr (Subgroup.mem_subgroupOf.mpr hdL)
      · refine Or.inl (Subgroup.mem_subgroupOf.mpr ?_)
        exact sec53_mul_mem_of_relIndex_two hA hsq hq (S'.L_le d.2) (S'.L_le hl'L') hdL hl'L
  have cosetL' : ∀ a b : G, a ∈ A → b ∈ A → a ∉ L' → b ∉ L' → a * b ∈ L' :=
    fun a b ha hb haL hbL => sec53_mul_mem_of_relIndex_two hA hsq hq' ha hb haL hbL
  have hinj : Function.Injective (sec53Chi S' ht) := S'.commutator_injective ht htL'
  have hχsurj : Function.Surjective (sec53Chi S' ht) :=
    (Function.Injective.bijective_of_nat_card_le hinj S'.card_Lb_eq.ge).2
  obtain ⟨F', hF'⟩ : ∃ F' : Subgroup Lb', F' = (L.subgroupOf L').comap (sec53Chi S' ht) :=
    ⟨_, rfl⟩
  have hF'idx : F'.index = 2 := by
    rw [hF', Subgroup.index_comap_of_surjective _ hχsurj]
    exact hLL'
  have hkey : ∀ n ∈ F', t * (n : G) * t⁻¹ * (n : G)⁻¹ ∈ L := by
    intro n hn
    rw [hF', Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hn
    exact hn
  have hP : ∀ x ∈ F'.map Lb'.subtype, ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ L ⊓ L' := by
    intro x hx a ha
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    show a * (n : G) * a⁻¹ * (n : G)⁻¹ ∈ L ⊓ L'
    have hnLb : (n : G) ∈ Lb' := n.2
    have hnN : (n : G) ∈ Subgroup.normalizer (A : Set G) := (S'.mem_Lb.mp hnLb).2
    have htL_mem : t * (n : G) * t⁻¹ * (n : G)⁻¹ ∈ L ⊓ L' :=
      Subgroup.mem_inf.mpr ⟨hkey n hn, S'.commutator_mem_L ht n.2⟩
    by_cases haL' : a ∈ L'
    ·
      have hcomm : a * (n : G) = (n : G) * a := S'.comm_L_Lb haL' hnLb
      have e : a * (n : G) * a⁻¹ * (n : G)⁻¹ = 1 := by
        calc a * (n : G) * a⁻¹ * (n : G)⁻¹ = (n : G) * a * a⁻¹ * (n : G)⁻¹ := by rw [hcomm]
          _ = 1 := by group
      rw [e]
      exact Subgroup.one_mem _
    ·
      have hat : a * t ∈ L' := cosetL' a t ha ht haL' htL'
      have hatA : a * t ∈ A := A.mul_mem ha ht
      have hcomm : (a * t) * (n : G) = (n : G) * (a * t) := S'.comm_L_Lb hat hnLb
      have h1 : (a * t) * (n : G) * (a * t)⁻¹ * (n : G)⁻¹ = 1 := by
        calc (a * t) * (n : G) * (a * t)⁻¹ * (n : G)⁻¹
            = (n : G) * (a * t) * (a * t)⁻¹ * (n : G)⁻¹ := by rw [hcomm]
          _ = 1 := by group
      have ea : a * t * t = a := by rw [mul_assoc, hsq t ht, mul_one]
      have e2 : a * (n : G) * a⁻¹ * (n : G)⁻¹ = t * (n : G) * t⁻¹ * (n : G)⁻¹ := by
        calc a * (n : G) * a⁻¹ * (n : G)⁻¹
            = (a * t * t) * (n : G) * (a * t * t)⁻¹ * (n : G)⁻¹ := by rw [ea]
          _ = ((a * t) * (n : G) * (a * t)⁻¹ * (n : G)⁻¹) * (t * (n : G) * t⁻¹ * (n : G)⁻¹) :=
              sec53_commutator_mul_left hA hnN hatA ht
          _ = t * (n : G) * t⁻¹ * (n : G)⁻¹ := by rw [h1, one_mul]
      rw [e2]
      exact htL_mem
  have hfwd : ∀ x ∈ F'.map Lb'.subtype, ∀ h ∈ L, x * h * x⁻¹ ∈ L := by
    intro x hx h hh
    have hc : h * x * h⁻¹ * x⁻¹ ∈ L := (Subgroup.mem_inf.mp (hP x hx h (S.L_le hh))).1
    have e : x * h * x⁻¹ = (h * x * h⁻¹ * x⁻¹)⁻¹ * h := by group
    rw [e]
    exact L.mul_mem (L.inv_mem hc) hh
  have hsub : (F'.map Lb'.subtype).subgroupOf Lb' = F' := by
    ext n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, hmn⟩
      have hmn' : m = n := Subtype.ext hmn
      rw [← hmn']
      exact hm
    · intro hn
      exact ⟨n, hn, rfl⟩
  have hrel : (F'.map Lb'.subtype).relIndex Lb' = 2 := by
    show ((F'.map Lb'.subtype).subgroupOf Lb').index = 2
    rw [hsub]
    exact hF'idx
  have hle : F'.map Lb'.subtype ≤ Lb' := Subgroup.map_subtype_le F'
  have hA_L : 2 * Nat.card L = Nat.card A := by
    have h := Subgroup.relIndex_mul_card (H := L) (K := A)
    rw [hq, inf_eq_left.mpr S.L_le] at h
    exact h
  have hA_L' : 2 * Nat.card L' = Nat.card A := by
    have h := Subgroup.relIndex_mul_card (H := L') (K := A)
    rw [hq', inf_eq_left.mpr S'.L_le] at h
    exact h
  have hF_card : 2 * Nat.card (F'.map Lb'.subtype) = Nat.card Lb' := by
    have h := Subgroup.relIndex_mul_card (H := F'.map Lb'.subtype) (K := Lb')
    rw [hrel, inf_eq_left.mpr hle] at h
    exact h
  have hLb_card : Nat.card Lb' = Nat.card L' := S'.card_Lb_eq
  have hFcard : 2 * Nat.card (F'.map Lb'.subtype) = Nat.card L := by omega
  refine ⟨F'.map Lb'.subtype, hle, hrel, hP, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hfwd x hx h hh
    · intro hh
      have h1 := hfwd x⁻¹ ((F'.map Lb'.subtype).inv_mem hx) (x * h * x⁻¹) hh
      have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rw [e] at h1
      exact h1
  · constructor
    · intro hbot
      have h1 := Subgroup.card_eq_one.mpr hbot
      omega
    · intro h2
      apply Subgroup.card_eq_one.mp
      omega

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions

theorem sec53_hyperplane_sec3 [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hq : Section3.q A Abar = 2) {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    (hne : conjSubgroup g (Section3.A0 A Abar) ≠ Section3.A0 A Abar) :
    ∃ F : Subgroup G, F ≤ conjSubgroup g (Section3.Abar0 A Abar) ∧
      F.relIndex (conjSubgroup g (Section3.Abar0 A Abar)) = 2 ∧
      (∀ x ∈ F, ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈
        Section3.A0 A Abar ⊓ conjSubgroup g (Section3.A0 A Abar)) ∧
      F ≤ Subgroup.normalizer (Section3.A0 A Abar : Set G) ∧
      (F = ⊥ ↔ Nat.card (Section3.A0 A Abar) = 2) := by
  have hgA : conjSubgroup g A = A := conjSubgroup_eq_self_iff.mpr hg
  have h' : Sec3Ctx A (conjSubgroup g Abar) (conjSubgroup g S₀) (conjSubgroup g B) := by
    have hc := h.conj g
    rwa [hgA] at hc
  have hA0 : Section3.A0 A (conjSubgroup g Abar) = conjSubgroup g (Section3.A0 A Abar) := by
    have hc := section3_A0_conj A Abar g
    rwa [hgA] at hc
  have hB0 : Section3.Abar0 A (conjSubgroup g Abar) =
      conjSubgroup g (Section3.Abar0 A Abar) := by
    have hc := section3_Abar0_conj A Abar g
    rwa [hgA] at hc
  have hq1 : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [← h.setup.relIndex_Lb]
    exact hq
  have hq2 : (Section3.A0 A (conjSubgroup g Abar)).relIndex A = 2 := by
    rw [hA0]
    have hc := relIndex_conjSubgroup_t77 g (Section3.A0 A Abar) A
    rw [hgA] at hc
    rw [hc]
    exact hq1
  have hne' : Section3.A0 A (conjSubgroup g Abar) ≠ Section3.A0 A Abar := by
    rw [hA0]
    exact hne
  obtain ⟨F, h1, h2, h3, h4, h5⟩ := sec53_hyperplane h.setup h'.setup hq1 hq2 hne'
  rw [hB0] at h1 h2
  rw [hA0] at h3
  exact ⟨F, h1, h2, h3, h4, h5⟩

end CFSG.RankThree.GF2n.Tim77
