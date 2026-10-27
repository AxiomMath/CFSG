module

public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S59

open CFSG
open scoped commutatorElement

theorem ext_commutator_mem_center {P : Type} [Group P]
    (hcomm : commutator P = Subgroup.center P) (x y : P) :
    ⁅x, y⁆ ∈ Subgroup.center P := by
  rw [← hcomm, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

theorem ext_card_eq_card_filter {G : Type} [Group G] [Fintype G] (H : Subgroup G)
    [DecidablePred (· ∈ H)] : Nat.card H = (Finset.univ.filter (· ∈ H)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem ext_two_mul_card_ker {G H : Type} [Group G] [Group H]
    (f : G →* H) (hH : Nat.card H = 2) (hf : ∃ g, f g ≠ 1) :
    2 * Nat.card f.ker = Nat.card G := by
  have hprod := Subgroup.card_ker_mul_card_range f
  have hdvd : Nat.card f.range ∣ 2 := by
    have h := Subgroup.card_subgroup_dvd_card f.range
    rwa [hH] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · obtain ⟨g, hg⟩ := hf
    have hbot : f.range = ⊥ := (Subgroup.card_eq_one (H := f.range)).1 h1
    have hmem : f g ∈ f.range := MonoidHom.mem_range.2 ⟨g, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact absurd hmem hg
  · rw [h2] at hprod
    rw [← hprod]
    ring

theorem ext_hom_right {P : Type} [Group P]
    (hcen : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P) (x : P) :
    ∃ f : P →* Subgroup.center P, ∀ y : P, (f y : P) = ⁅x, y⁆ := by
  refine ⟨MonoidHom.mk' (fun y => ⟨⁅x, y⁆, hcen x y⟩)
    (fun y z => Subtype.ext ?_), fun y => rfl⟩
  show ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆
  have hc : y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ := by
    rw [Subgroup.mem_center_iff.1 (hcen x z) y, mul_inv_cancel_right]
  calc ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by rw [hc]

theorem ext_hom_left {P : Type} [Group P]
    (hcen : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P) (y : P) :
    ∃ f : P →* Subgroup.center P, ∀ b : P, (f b : P) = ⁅b, y⁆ := by
  refine ⟨MonoidHom.mk' (fun b => ⟨⁅b, y⁆, hcen b y⟩)
    (fun b b' => Subtype.ext ?_), fun b => rfl⟩
  show ⁅b * b', y⁆ = ⁅b, y⁆ * ⁅b', y⁆
  have hc : b * ⁅b', y⁆ * b⁻¹ = ⁅b', y⁆ := by
    rw [Subgroup.mem_center_iff.1 (hcen b' y) b, mul_inv_cancel_right]
  have hz : ⁅b, y⁆ * ⁅b', y⁆ = ⁅b', y⁆ * ⁅b, y⁆ :=
    (Subgroup.mem_center_iff.1 (hcen b y) ⁅b', y⁆).symm
  calc ⁅b * b', y⁆ = (b * ⁅b', y⁆ * b⁻¹) * ⁅b, y⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅b', y⁆ * ⁅b, y⁆ := by rw [hc]
    _ = ⁅b, y⁆ * ⁅b', y⁆ := hz.symm

theorem ext_two_mul_card_centralizer_singleton {P : Type} [Group P] [Finite P]
    (hcen : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P) (hZ : Nat.card (Subgroup.center P) = 2)
    (b : P) (hb : b ∉ Subgroup.center P) :
    2 * Nat.card (Subgroup.centralizer ({b} : Set P)) = Nat.card P := by
  obtain ⟨f, hf⟩ := ext_hom_right hcen b
  have key : ∀ y : P, f y = 1 ↔ b * y = y * b := by
    intro y
    have h1 : f y = 1 ↔ ⁅b, y⁆ = 1 := by
      constructor
      · intro h
        have h' : ((f y : Subgroup.center P) : P) = 1 := congrArg Subtype.val h
        rw [hf y] at h'
        exact h'
      · intro h
        exact Subtype.ext ((hf y).trans h)
    rw [h1, commutatorElement_eq_one_iff_mul_comm]
  have hne : ∃ y : P, f y ≠ 1 := by
    by_contra hcon
    have hall : ∀ y : P, f y = 1 := fun y => by
      by_contra hy
      exact hcon ⟨y, hy⟩
    apply hb
    rw [Subgroup.mem_center_iff]
    intro g
    exact ((key g).1 (hall g)).symm
  have hdim := ext_two_mul_card_ker f hZ hne
  have hker : f.ker = Subgroup.centralizer ({b} : Set P) := by
    ext y
    rw [MonoidHom.mem_ker, key y, Subgroup.mem_centralizer_iff]
    simp
  rw [hker] at hdim
  exact hdim

theorem card_centralizer_mul_card {P : Type} [Group P] [Finite P]
    (hP : IsExtraspecialPGroup 2 P) (B : Subgroup P) (hB : Subgroup.center P ≤ B) :
    Nat.card (Subgroup.centralizer (B : Set P)) * Nat.card B = 2 * Nat.card P := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  obtain ⟨-, hcomm, -, hZ⟩ := hP
  have hcen : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P := ext_commutator_mem_center hcomm
  have hZf : (Finset.univ.filter (· ∈ Subgroup.center P)).card = 2 :=
    (ext_card_eq_card_filter (Subgroup.center P)).symm.trans hZ
  have hBf : (Finset.univ.filter (· ∈ B)).card = Nat.card B :=
    (ext_card_eq_card_filter B).symm
  have hZB : (Finset.univ.filter (· ∈ B)).filter (· ∈ Subgroup.center P)
      = Finset.univ.filter (· ∈ Subgroup.center P) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hB h, h⟩⟩
  have hA : ∀ b ∈ Finset.univ.filter (· ∈ B),
      2 * (Finset.univ.filter (fun y => b * y = y * b)).card
        = Nat.card P + (if b ∈ Subgroup.center P then Nat.card P else 0) := by
    intro b _
    by_cases hb : b ∈ Subgroup.center P
    · have hall : Finset.univ.filter (fun y => b * y = y * b) = Finset.univ :=
        Finset.filter_true_of_mem (fun y _ => ((Subgroup.mem_center_iff.1 hb) y).symm)
      rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card, if_pos hb]
      ring
    · have hc : Nat.card (Subgroup.centralizer ({b} : Set P))
          = (Finset.univ.filter (fun y => b * y = y * b)).card := by
        rw [ext_card_eq_card_filter]
        congr 1
        ext y
        simp [Subgroup.mem_centralizer_iff]
      rw [← hc, if_neg hb, add_zero]
      exact ext_two_mul_card_centralizer_singleton hcen hZ b hb
  have hBy : ∀ y : P,
      2 * ((Finset.univ.filter (· ∈ B)).filter (fun b => b * y = y * b)).card
        = Nat.card B + (if y ∈ Subgroup.centralizer (B : Set P) then Nat.card B else 0) := by
    intro y
    by_cases hy : y ∈ Subgroup.centralizer (B : Set P)
    · have hall : (Finset.univ.filter (· ∈ B)).filter (fun b => b * y = y * b)
          = Finset.univ.filter (· ∈ B) := by
        apply Finset.filter_true_of_mem
        intro b hb
        exact (Subgroup.mem_centralizer_iff.1 hy) b (Finset.mem_filter.1 hb).2
      rw [hall, hBf, if_pos hy]
      ring
    · obtain ⟨f, hf⟩ := ext_hom_left hcen y
      have key : ∀ b : P, f b = 1 ↔ b * y = y * b := by
        intro b
        have h1 : f b = 1 ↔ ⁅b, y⁆ = 1 := by
          constructor
          · intro h
            have h' : ((f b : Subgroup.center P) : P) = 1 := congrArg Subtype.val h
            rw [hf b] at h'
            exact h'
          · intro h
            exact Subtype.ext ((hf b).trans h)
        rw [h1, commutatorElement_eq_one_iff_mul_comm]
      have hne : ∃ x : B, (f.comp B.subtype) x ≠ 1 := by
        have hex : ∃ b : P, b ∈ B ∧ b * y ≠ y * b := by
          by_contra hcon
          apply hy
          refine Subgroup.mem_centralizer_iff.2 fun b hb => ?_
          by_contra hne'
          exact hcon ⟨b, hb, hne'⟩
        obtain ⟨b, hbB, hby⟩ := hex
        exact ⟨⟨b, hbB⟩, fun h => hby ((key b).1 h)⟩
      have hdim := ext_two_mul_card_ker (f.comp B.subtype) hZ hne
      have hk : ∀ x : B, x ∈ (f.comp B.subtype).ker ↔ (x : P) * y = y * (x : P) := by
        intro x
        rw [MonoidHom.mem_ker]
        exact key x
      have hcardg : Nat.card (f.comp B.subtype).ker
          = ((Finset.univ.filter (· ∈ B)).filter (fun b => b * y = y * b)).card := by
        have hmap : Nat.card ((f.comp B.subtype).ker.map B.subtype)
            = Nat.card (f.comp B.subtype).ker :=
          Subgroup.card_map_of_injective B.subtype_injective
        rw [← hmap, ext_card_eq_card_filter]
        congr 1
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hp
          obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
          exact ⟨x.2, (hk x).1 hx⟩
        · rintro ⟨hpB, hpy⟩
          exact Subgroup.mem_map.2 ⟨⟨p, hpB⟩, (hk ⟨p, hpB⟩).2 hpy, rfl⟩
      rw [if_neg hy, add_zero, ← hcardg]
      exact hdim
  have hswap : ∑ b ∈ Finset.univ.filter (· ∈ B),
        (Finset.univ.filter (fun y => b * y = y * b)).card
      = ∑ y ∈ Finset.univ,
        ((Finset.univ.filter (· ∈ B)).filter (fun b => b * y = y * b)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hS1 : 2 * (∑ b ∈ Finset.univ.filter (· ∈ B),
        (Finset.univ.filter (fun y => b * y = y * b)).card)
      = Nat.card B * Nat.card P + 2 * Nat.card P := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hA, Finset.sum_add_distrib, Finset.sum_const,
      smul_eq_mul, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, hZB, hZf, hBf]
  have hS2 : 2 * (∑ y ∈ Finset.univ,
        ((Finset.univ.filter (· ∈ B)).filter (fun b => b * y = y * b)).card)
      = Nat.card P * Nat.card B
        + Nat.card (Subgroup.centralizer (B : Set P)) * Nat.card B := by
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun y _ => hBy y), Finset.sum_add_distrib,
      Finset.sum_const, smul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Finset.sum_filter, Finset.sum_const, smul_eq_mul,
      ← ext_card_eq_card_filter (Subgroup.centralizer (B : Set P))]
  have hcomm' : Nat.card B * Nat.card P = Nat.card P * Nat.card B := Nat.mul_comm _ _
  omega


theorem ext_sq_mem_center {P : Type} [Group P] [Finite P] (hP : IsExtraspecialPGroup 2 P)
    (x : P) : x ^ 2 ∈ Subgroup.center P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, -, hfr, -⟩ := hP
  haveI : Fact (IsPGroup 2 P) := ⟨hp⟩
  rw [← hfr, CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
  exact Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)

theorem ext_center_sq {P : Type} [Group P] [Finite P] (hP : IsExtraspecialPGroup 2 P)
    {z : P} (hz : z ∈ Subgroup.center P) : z ^ 2 = 1 := by
  have h1 : (⟨z, hz⟩ : Subgroup.center P) ^ Nat.card (Subgroup.center P) = 1 :=
    pow_card_eq_one'
  rw [hP.2.2.2] at h1
  exact congrArg Subtype.val h1

theorem card_sq_eq_one_extraspecial {P : Type} [Group P] [Finite P]
    (hP : IsExtraspecialPGroup 2 P) (hcard : Nat.card P = 2 ^ 9) (A : Subgroup P)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAcard : Nat.card A = 2 ^ 5) : Nat.card {x : P // x ^ 2 = 1} = 272 := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' := hP
  obtain ⟨hp, hcomm, hfr, hZ⟩ := hP
  have hcen : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P := ext_commutator_mem_center hcomm
  have hsqc : ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
    intro x
    haveI : Fact (IsPGroup 2 P) := ⟨hp⟩
    rw [← hfr, CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
    exact Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)
  have hZ2 : ∀ z ∈ Subgroup.center P, z ^ 2 = 1 := by
    intro z hz
    have h1 : (⟨z, hz⟩ : Subgroup.center P) ^ Nat.card (Subgroup.center P) = 1 :=
      pow_card_eq_one'
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hZA : Subgroup.center P ≤ A := by
    have hab : ∀ b ∈ A ⊔ Subgroup.center P, ∀ b' ∈ A ⊔ Subgroup.center P, b * b' = b' * b := by
      intro b hb b' hb'
      obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
      obtain ⟨a', ha', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb'
      have h1 := Subgroup.mem_center_iff.mp hz
      have h2 := Subgroup.mem_center_iff.mp hz'
      have e1 : a * z * (a' * z') = a * a' * (z * z') := by
        calc a * z * (a' * z') = a * (z * a') * z' := by group
          _ = a * (a' * z) * z' := by rw [(h1 a').symm]
          _ = a * a' * (z * z') := by group
      have e2 : a' * z' * (a * z) = a' * a * (z' * z) := by
        calc a' * z' * (a * z) = a' * (z' * a) * z := by group
          _ = a' * (a * z') * z := by rw [(h2 a).symm]
          _ = a' * a * (z' * z) := by group
      rw [e1, e2, hAc a ha a' ha', h1 z']
    have hBB : A ⊔ Subgroup.center P ≤
        Subgroup.centralizer ((A ⊔ Subgroup.center P : Subgroup P) : Set P) := fun b hb =>
      Subgroup.mem_centralizer_iff.mpr fun b' hb' => hab b' hb' b hb
    have hdc := card_centralizer_mul_card hP' (A ⊔ Subgroup.center P) le_sup_right
    have hle := Subgroup.card_le_of_le hBB
    have hBle : Nat.card ↥(A ⊔ Subgroup.center P) ≤ 32 := by
      rw [hcard] at hdc
      nlinarith
    have heq : A = A ⊔ Subgroup.center P :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hAcard]; omega)
    rw [heq]
    exact le_sup_right
  have hCA : Subgroup.centralizer (A : Set P) = A := by
    have hdc := card_centralizer_mul_card hP' A hZA
    rw [hcard, hAcard] at hdc
    have hA' : A ≤ Subgroup.centralizer (A : Set P) := fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun b hb => hAc b hb a ha
    refine (Subgroup.eq_of_le_of_card_ge hA' ?_).symm
    omega
  have hx2 : ∀ x : P, x ^ 2 * x ^ 2 = 1 := fun x => by
    rw [← pow_two]
    exact hZ2 _ (hsqc x)
  have hn_mem : ∀ x : P, x ∈ A →
      (Finset.univ.filter (fun a : A => (x * (a : P)) ^ 2 = 1)).card = 2 ^ 5 := by
    intro x hx
    have hall : Finset.univ.filter (fun a : A => (x * (a : P)) ^ 2 = 1) = Finset.univ :=
      Finset.filter_true_of_mem fun a _ => hA2 _ (A.mul_mem hx a.2)
    rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card, hAcard]
  have hn_nmem : ∀ x : P, x ∉ A →
      (Finset.univ.filter (fun a : A => (x * (a : P)) ^ 2 = 1)).card = 2 ^ 4 := by
    intro x hx
    obtain ⟨f, hf⟩ := ext_hom_right hcen x⁻¹
    let κ : A →* Subgroup.center P := f.comp A.subtype
    have hκ : ∀ a : A, ((κ a : Subgroup.center P) : P) = ⁅x⁻¹, (a : P)⁆ := fun a => hf a
    have hsq : ∀ a : A, (x * (a : P)) ^ 2 = x ^ 2 * ((κ a : Subgroup.center P) : P) := by
      intro a
      rw [hκ a]
      have ha2 := hA2 _ a.2
      calc (x * (a : P)) ^ 2 = x ^ 2 * ⁅x⁻¹, (a : P)⁆ * (a : P) ^ 2 := by
            simp only [commutatorElement_def, pow_two]
            group
        _ = x ^ 2 * ⁅x⁻¹, (a : P)⁆ := by rw [ha2, mul_one]
    have hcond : ∀ a : A, (x * (a : P)) ^ 2 = 1 ↔ κ a = ⟨x ^ 2, hsqc x⟩ := by
      intro a
      rw [hsq a]
      have hinv : (x ^ 2)⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right (hx2 x)
      constructor
      · intro h1
        apply Subtype.ext
        show ((κ a : Subgroup.center P) : P) = x ^ 2
        calc ((κ a : Subgroup.center P) : P)
            = (x ^ 2)⁻¹ * (x ^ 2 * ((κ a : Subgroup.center P) : P)) := by group
          _ = x ^ 2 := by rw [h1, mul_one, hinv]
      · intro h1
        have : ((κ a : Subgroup.center P) : P) = x ^ 2 := congrArg Subtype.val h1
        rw [this]
        exact hx2 x
    have hnt : ∃ a : A, κ a ≠ 1 := by
      have hxi : x⁻¹ ∉ Subgroup.centralizer (A : Set P) := by
        rw [hCA]
        intro h
        exact hx (by simpa using A.inv_mem h)
      by_contra hcon
      push Not at hcon
      apply hxi
      refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      have h1 : ((κ ⟨a, ha⟩ : Subgroup.center P) : P) = 1 := by rw [hcon ⟨a, ha⟩]; rfl
      rw [hκ] at h1
      have h2 : x⁻¹ * a * x * a⁻¹ = 1 := by
        simpa [commutatorElement_def, inv_inv] using h1
      have h3 : x⁻¹ * a * x = a := by
        calc x⁻¹ * a * x = (x⁻¹ * a * x * a⁻¹) * a := by group
          _ = a := by rw [h2, one_mul]
      calc a * x⁻¹ = (x⁻¹ * a * x) * x⁻¹ := by rw [h3]
        _ = x⁻¹ * a := by group
    have hrange : κ.range = ⊤ := by
      obtain ⟨a, ha⟩ := hnt
      have hcardr : Nat.card κ.range ∣ 2 := by
        have := Subgroup.card_subgroup_dvd_card κ.range
        rwa [hZ] at this
      rcases (Nat.dvd_prime Nat.prime_two).1 hcardr with h1 | h2
      · exfalso
        have hbot : κ.range = ⊥ := Subgroup.card_eq_one.1 h1
        have hmem : κ a ∈ κ.range := ⟨a, rfl⟩
        rw [hbot] at hmem
        exact ha (Subgroup.mem_bot.1 hmem)
      · exact Subgroup.eq_top_of_card_eq _ (by rw [h2, hZ])
    have hc : (⟨x ^ 2, hsqc x⟩ : Subgroup.center P) ∈ Set.range κ := by
      have : (⟨x ^ 2, hsqc x⟩ : Subgroup.center P) ∈ κ.range := by rw [hrange]; trivial
      exact this
    have h1 : (1 : Subgroup.center P) ∈ Set.range κ := ⟨1, map_one κ⟩
    have hfib := MonoidHom.card_fiber_eq_of_mem_range κ hc h1
    have hker : (Finset.univ.filter (fun a : A => κ a = 1)).card = Nat.card κ.ker := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    have hdim := Subgroup.card_ker_mul_card_range κ
    rw [hrange, Subgroup.card_top, hZ, hAcard] at hdim
    have hker16 : Nat.card κ.ker = 2 ^ 4 := by omega
    calc (Finset.univ.filter (fun a : A => (x * (a : P)) ^ 2 = 1)).card
        = (Finset.univ.filter (fun a : A => κ a = ⟨x ^ 2, hsqc x⟩)).card := by
          congr 1
          exact Finset.filter_congr fun a _ => hcond a
      _ = (Finset.univ.filter (fun a : A => κ a = 1)).card := hfib
      _ = 2 ^ 4 := by rw [hker, hker16]
  have hsum : ∑ x : P, (Finset.univ.filter (fun a : A => (x * (a : P)) ^ 2 = 1)).card =
      Nat.card A * Nat.card {x : P // x ^ 2 = 1} := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    have hsh : ∀ a : A, ∑ x : P, (if (x * (a : P)) ^ 2 = 1 then 1 else 0) =
        ∑ x : P, (if x ^ 2 = 1 then 1 else 0) := fun a =>
      Fintype.sum_equiv (Equiv.mulRight (a : P)) _ _ (fun x => rfl)
    simp only [hsh]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
    congr 1
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp
  have hsum2 : ∑ x : P, (Finset.univ.filter (fun a : A => (x * (a : P)) ^ 2 = 1)).card =
      Nat.card A * 2 ^ 5 + (Nat.card P - Nat.card A) * 2 ^ 4 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ A)]
    rw [Finset.sum_congr rfl (fun x hx => hn_mem x (Finset.mem_filter.mp hx).2),
      Finset.sum_congr rfl (fun x hx => hn_nmem x (Finset.mem_filter.mp hx).2)]
    simp only [Finset.sum_const, smul_eq_mul]
    have hc1 : (Finset.univ.filter (· ∈ A)).card = Nat.card A :=
      (ext_card_eq_card_filter A).symm
    have hc2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset P))
      (· ∈ A)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hc1] at hc2
    have hc3 : (Finset.univ.filter (fun x => ¬ x ∈ A)).card = Nat.card P - Nat.card A := by
      omega
    rw [hc1, hc3]
  rw [hsum] at hsum2
  rw [hAcard, hcard] at hsum2
  omega

end CFSG.RankThree.PartTwo.Sec21.FF81.S59
