module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Leaves

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.Open
open scoped commutatorElement

theorem eq_one_of_mem_center_of_pow_three {K : Type} [Group K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center K)) {c : K} (hc : c ∈ Subgroup.center K)
    (h : c ^ 3 = 1) : c = 1 := by
  have h1 : orderOf (⟨c, hc⟩ : Subgroup.center K) ∣ Nat.card (Subgroup.center K) :=
    orderOf_dvd_natCard _
  have h2 : orderOf (⟨c, hc⟩ : Subgroup.center K) ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using h
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center K)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have h4 : orderOf (⟨c, hc⟩ : Subgroup.center K) ∣ Nat.gcd 3 (Nat.card (Subgroup.center K)) :=
    Nat.dvd_gcd h2 h1
  rw [Nat.Coprime.gcd_eq_one hcop] at h4
  have h5 : (⟨c, hc⟩ : Subgroup.center K) = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  simpa using congrArg Subtype.val h5

theorem commute_of_commute_mk_center {K : Type} [Group K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center K)) {x f : K} (hf : f ^ 3 = 1)
    (h : (QuotientGroup.mk' (Subgroup.center K)) x * (QuotientGroup.mk' (Subgroup.center K)) f =
      (QuotientGroup.mk' (Subgroup.center K)) f * (QuotientGroup.mk' (Subgroup.center K)) x) :
    x * f = f * x := by
  set c : K := x * f * x⁻¹ * f⁻¹ with hc
  have hcA : c ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq_one_iff]
    have : (QuotientGroup.mk' (Subgroup.center K)) c = 1 := by
      simp only [hc, map_mul, map_inv]
      rw [h]
      group
    simpa using this
  have hxf : x * f * x⁻¹ = c * f := by rw [hc]; group
  have hcf : Commute c f := (Subgroup.mem_center_iff.1 hcA f).symm
  have h3c : c ^ 3 = 1 := by
    have h1 : (x * f * x⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hf]
      simp
    rw [hxf, hcf.mul_pow, hf, mul_one] at h1
    exact h1
  have hc1 : c = 1 := eq_one_of_mem_center_of_pow_three h3 hcA h3c
  rw [hc1] at hxf
  have : x * f = f * x := by
    calc x * f = x * f * x⁻¹ * x := by group
      _ = 1 * f * x := by rw [hxf]
      _ = f * x := by group
  exact this

theorem exists_mulEquiv_map {A B : Type} [Group A] [Group B] (f : A →* B) {X : Subgroup A}
    (h : ∀ x ∈ X, f x = 1 → x = 1) :
    ∃ e : ↥X ≃* ↥(X.map f), ∀ x : X, ((e x : X.map f) : B) = f x := by
  have hinj : Function.Injective (f.comp X.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (h x x.2 hx)
  have hrange : (f.comp X.subtype).range = X.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun x => rfl⟩

theorem eq_one_of_mk_eq_one_of_card_center {K : Type} [Group K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center K)) {X : Subgroup K}
    (hcen : Nat.card (Subgroup.center ↥X) = 3) :
    ∀ x ∈ X, (QuotientGroup.mk' (Subgroup.center K)) x = 1 → x = 1 := by
  intro x hx hx1
  have hxA : x ∈ Subgroup.center K := (QuotientGroup.eq_one_iff x).1 hx1
  have hxX : (⟨x, hx⟩ : X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 hxA y)
  have h1 : (⟨⟨x, hx⟩, hxX⟩ : Subgroup.center ↥X) ^ Nat.card (Subgroup.center ↥X) = 1 :=
    pow_card_eq_one'
  rw [hcen] at h1
  have h2 : x ^ 3 = 1 := by
    have := congrArg (fun y : Subgroup.center ↥X => ((y : X) : K)) h1
    simpa using this
  exact eq_one_of_mem_center_of_pow_three h3 hxA h2

theorem pos_map_central_quotient {K : Type} [Group K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center K)) {Z X : Subgroup K} (h : Pos K Z X) :
    Pos (K ⧸ Subgroup.center K) (Z.map (QuotientGroup.mk' (Subgroup.center K)))
      (X.map (QuotientGroup.mk' (Subgroup.center K))) := by
  obtain ⟨hZ, hZX, hXC, hsub, hqs, hcen, hlie⟩ := h
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  have hinjX : ∀ x ∈ X, π x = 1 → x = 1 := eq_one_of_mk_eq_one_of_card_center h3 hcen
  obtain ⟨eX, -⟩ := exists_mulEquiv_map π hinjX
  obtain ⟨eZ, -⟩ := exists_mulEquiv_map π (X := Z) fun z hz => hinjX z (hZX hz)
  set C : Subgroup K := Subgroup.centralizer (Z : Set K) with hC
  set C' : Subgroup (K ⧸ Subgroup.center K) :=
    Subgroup.centralizer ((Z.map π : Subgroup (K ⧸ Subgroup.center K)) : Set _) with hC'
  have hmapC : ∀ c ∈ C, π c ∈ C' := by
    intro c hc
    rw [hC', Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hc z hz]
  let π' : ↥C →* ↥C' := (π.comp C.subtype).codRestrict C' fun c => hmapC c c.2
  have hsurj : Function.Surjective π' := by
    rintro ⟨y', hy'⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y'
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [hC, Subgroup.mem_centralizer_iff]
    intro z hz
    have hz3 : z ^ 3 = 1 := by
      have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
      rw [hZ] at this
      simpa using congrArg Subtype.val this
    have hcomm := Subgroup.mem_centralizer_iff.1 hy' (π z) (Subgroup.mem_map_of_mem π hz)
    exact (commute_of_commute_mk_center h3 hz3 hcomm.symm).symm
  have hmapX : (X.subgroupOf C).map π' = (X.map π).subgroupOf C' := by
    ext ⟨y', hy'⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨⟨c, hc⟩, hcX, hcy⟩
      have : π c = y' := congrArg Subtype.val hcy
      exact ⟨c, hcX, this⟩
    · rintro ⟨x, hxX, rfl⟩
      exact ⟨⟨x, hXC hxX⟩, hxX, rfl⟩
  refine ⟨?_, Subgroup.map_mono hZX, ?_, ?_, isQuasisimple_of_mulEquiv' eX hqs, ?_, ?_⟩
  · rw [← hZ]
    exact (Nat.card_congr eZ.toEquiv).symm
  · rintro _ ⟨x, hxX, rfl⟩
    exact hmapC x (hXC hxX)
  · have := Subgroup.IsSubnormal.map (f := π') hsurj hsub
    rwa [hmapX] at this
  · rw [← hcen]
    exact (Nat.card_congr (Subgroup.centerCongr eX).toEquiv).symm
  · let f := QuotientGroup.congr (Subgroup.center X) (Subgroup.center (X.map π)) eX
      (Subgroup.map_center_eq eX)
    rcases hlie with hl | hl
    · exact Or.inl (LieModel.of_mulEquiv f hl)
    · exact Or.inr (LieModel.of_mulEquiv f hl)

theorem center_mul_mul_inv {K : Type} [Group K] {z : K} (hz : z ∈ Subgroup.center K) (g : K) :
    z * g * z⁻¹ = g := by
  rw [mul_inv_eq_iff_eq_mul]
  exact (Subgroup.mem_center_iff.1 hz g).symm

theorem eq_top_of_perfect_of_sup_center {K : Type} [Group K] (hK : commutator K = ⊤)
    {M : Subgroup K}
    (h : ∀ k : K, ∃ m ∈ M, ∃ z ∈ Subgroup.center K, k = m * z) : M = ⊤ := by
  rw [eq_top_iff, ← hK, commutator_def]
  refine Subgroup.commutator_le.2 fun a _ b _ => ?_
  obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := h a
  obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := h b
  have key : ⁅m₁ * z₁, m₂ * z₂⁆ = ⁅m₁, m₂⁆ := by
    calc ⁅m₁ * z₁, m₂ * z₂⁆
        = m₁ * (z₁ * (m₂ * z₂) * z₁⁻¹) * m₁⁻¹ * (m₂ * z₂)⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = m₁ * (m₂ * z₂) * m₁⁻¹ * (m₂ * z₂)⁻¹ := by rw [center_mul_mul_inv hz₁]
      _ = m₁ * m₂ * (z₂ * m₁⁻¹ * z₂⁻¹) * m₂⁻¹ := by group
      _ = ⁅m₁, m₂⁆ := by
          rw [center_mul_mul_inv hz₂]
          simp only [commutatorElement_def]
  rw [key, commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)

theorem iSup_centralizer_eq_top_of_central_quotient {K : Type} [Group K] [Finite K]
    (hK : commutator K = ⊤) (h3 : ¬ 3 ∣ Nat.card (Subgroup.center K))
    (hbar : ∀ Eb : Subgroup (K ⧸ Subgroup.center K), IsElemAbelian 3 Eb → Nat.card Eb = 9 →
      (⨆ (F : Subgroup (K ⧸ Subgroup.center K)) (_ : F ≤ Eb) (_ : Nat.card F = 3),
        Subgroup.centralizer (F : Set (K ⧸ Subgroup.center K))) = ⊤)
    {E : Subgroup K} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 9) :
    (⨆ (F : Subgroup K) (_ : F ≤ E) (_ : Nat.card F = 3),
      Subgroup.centralizer (F : Set K)) = ⊤ := by
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  set M : Subgroup K :=
    ⨆ (F : Subgroup K) (_ : F ≤ E) (_ : Nat.card F = 3), Subgroup.centralizer (F : Set K) with hM
  have hinjE : ∀ x ∈ E, π x = 1 → x = 1 := fun x hx hx1 =>
    eq_one_of_mem_center_of_pow_three h3 ((QuotientGroup.eq_one_iff x).1 hx1) (hE.2 x hx)
  obtain ⟨eE, -⟩ := exists_mulEquiv_map π hinjE
  have hEc : Nat.card (E.map π) = 9 := by rw [← hc]; exact (Nat.card_congr eE.toEquiv).symm
  have hbar' := hbar (E.map π) (hE.map π) hEc
  have hle : (⨆ (F : Subgroup (K ⧸ Subgroup.center K)) (_ : F ≤ E.map π) (_ : Nat.card F = 3),
      Subgroup.centralizer (F : Set (K ⧸ Subgroup.center K))) ≤ M.map π := by
    refine iSup_le fun Fb => iSup_le fun hFbE => iSup_le fun hFb3 => ?_
    set F : Subgroup K := Fb.comap π ⊓ E with hF
    have hFE : F ≤ E := inf_le_right
    have hFmap : F.map π = Fb := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact hx.1
      · intro yb hyb
        obtain ⟨e, he, rfl⟩ := hFbE hyb
        exact ⟨e, ⟨hyb, he⟩, rfl⟩
    obtain ⟨eF, -⟩ := exists_mulEquiv_map π (X := F) fun x hx hx1 => hinjE x (hFE hx) hx1
    have hF3 : Nat.card F = 3 := by
      rw [← hFb3, ← hFmap]
      exact Nat.card_congr eF.toEquiv
    have hCF : Subgroup.centralizer (Fb : Set (K ⧸ Subgroup.center K)) ≤
        (Subgroup.centralizer (F : Set K)).map π := by
      intro yb hyb
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
      refine ⟨y, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro f hf
      have hcomm := Subgroup.mem_centralizer_iff.1 hyb (π f) hf.1
      exact (commute_of_commute_mk_center h3 (hE.2 f (hFE hf)) hcomm.symm).symm
    refine hCF.trans (Subgroup.map_mono ?_)
    exact le_iSup_of_le F (le_iSup_of_le hFE (le_iSup_of_le hF3 le_rfl))
  have htop : M.map π = ⊤ := by
    rw [eq_top_iff, ← hbar']
    exact hle
  refine eq_top_of_perfect_of_sup_center hK fun k => ?_
  obtain ⟨m, hm, hmk⟩ : π k ∈ M.map π := by rw [htop]; exact Subgroup.mem_top _
  refine ⟨m, hm, m⁻¹ * k, ?_, by group⟩
  rw [← QuotientGroup.eq]
  exact hmk

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
