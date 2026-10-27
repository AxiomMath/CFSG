module

public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

section Lift

variable {M : Type*} [Group M]

theorem card_le_pow_of_isPGroup_of_not_dvd {R : Type*} [Group R] [Finite R] {p s : ℕ}
    (hp : p.Prime) (hR : ¬ p ^ (s + 1) ∣ Nat.card R) {Q : Subgroup R} (hQ : IsPGroup p Q) :
    Nat.card Q ≤ p ^ s := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : p ^ n ∣ Nat.card R := hn ▸ Subgroup.card_subgroup_dvd_card Q
  have hns : n ≤ s := by
    by_contra h
    exact hR ((pow_dvd_pow p (by omega : s + 1 ≤ n)).trans hdvd)
  rw [hn]
  exact Nat.pow_le_pow_right hp.pos hns

theorem exists_noncyclic_pGroup_map_le [Finite M] {M' : Type*} [Group M'] (φ : M →* M')
    {p : ℕ} (hp : p.Prime) {Eb : Subgroup M'} (hEb : Eb ≤ φ.range) (hEp : IsPGroup p Eb)
    (hEc : ¬ IsCyclic ↥Eb) :
    ∃ B : Subgroup M, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B, φ b ∈ Eb := by
  haveI : Fact p.Prime := ⟨hp⟩
  set H : Subgroup M := Eb.comap φ with hH
  let ψ : H →* Eb := (φ.comp H.subtype).codRestrict Eb fun h => h.2
  have hψ : Function.Surjective ψ := fun e => by
    obtain ⟨g, hg⟩ := hEb e.2
    exact ⟨⟨g, by rw [hH, Subgroup.mem_comap, hg]; exact e.2⟩, Subtype.ext hg⟩
  obtain ⟨P⟩ : Nonempty (Sylow p H) := inferInstance
  have htop : IsPGroup p (⊤ : Subgroup Eb) := hEp.of_equiv Subgroup.topEquiv.symm
  have hQ : (⊤ : Subgroup Eb) = P.mapSurjective hψ :=
    (P.mapSurjective hψ).is_maximal' htop le_top
  have hQ' : (⊤ : Subgroup Eb) = (P : Subgroup H).map ψ := by
    rw [hQ]
    rfl
  refine ⟨(P : Subgroup H).map H.subtype, P.2.map H.subtype, fun hcyc => hEc ?_, ?_⟩
  · let f : ↥((P : Subgroup H).map H.subtype) →* Eb :=
      (φ.comp ((P : Subgroup H).map H.subtype).subtype).codRestrict Eb fun b => by
        obtain ⟨h, -, hb⟩ := b.2
        have : (b : M) = (h : M) := hb.symm
        show φ b ∈ Eb
        rw [this]
        exact h.2
    have hf : Function.Surjective f := fun e => by
      have he : e ∈ (P : Subgroup H).map ψ := hQ' ▸ Subgroup.mem_top e
      obtain ⟨h, hhP, hhe⟩ := he
      refine ⟨⟨(h : M), h, hhP, rfl⟩, Subtype.ext ?_⟩
      exact congrArg Subtype.val hhe
    exact isCyclic_of_surjective f hf
  · rintro _ ⟨h, -, rfl⟩
    exact h.2

theorem card_map_eq_of_kernel_trick [Finite M] {R : Type*} [Group R] [Finite R] (ψ : M →* R)
    {p s : ℕ} (hp : p.Prime) {E : Subgroup M} (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ (s + 1)) (hR : ¬ p ^ (s + 1) ∣ Nat.card R)
    (hY : ∀ Y : Subgroup M, IsElemAbelian p Y → Y ≤ ψ.ker → Nat.card Y ≤ p) :
    Nat.card (E.map ψ) = p ^ s ∧ ∃ Y : Subgroup M, Y ≤ E ∧ Y ≤ ψ.ker ∧ Nat.card Y = p := by
  set ψE : E →* R := ψ.comp E.subtype with hψE
  have hmul := Subgroup.card_ker_mul_card_range ψE
  have hrange : ψE.range = E.map ψ := by
    rw [hψE, MonoidHom.range_comp, Subgroup.range_subtype]
  set Y : Subgroup M := ψE.ker.map E.subtype with hYdef
  have hYcard : Nat.card Y = Nat.card ψE.ker :=
    Subgroup.card_map_of_injective E.subtype_injective
  have hYE : Y ≤ E := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hYker : Y ≤ ψ.ker := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hY1 : Nat.card Y ≤ p := hY Y (hE.mono hYE) hYker
  have hQ : Nat.card (E.map ψ) ≤ p ^ s :=
    card_le_pow_of_isPGroup_of_not_dvd hp hR (hE.isPGroup.map ψ)
  rw [hrange, ← hYcard, hEcard, pow_succ] at hmul
  have hpos : 0 < Nat.card (E.map ψ) := Nat.card_pos
  have hps : 0 < p ^ s := pow_pos hp.pos s
  have hb : Nat.card (E.map ψ) = p ^ s := by
    by_contra hne
    have hlt : Nat.card (E.map ψ) < p ^ s := lt_of_le_of_ne hQ hne
    nlinarith [hp.pos]
  refine ⟨hb, Y, hYE, hYker, ?_⟩
  rw [hb] at hmul
  exact Nat.eq_of_mul_eq_mul_right hps (by linarith)

theorem exists_noncyclic_pGroup_of_kernel_trick_surjective [Finite M] {R : Type*} [Group R]
    (ψ : M →* R) (hψ : Function.Surjective ψ) {p s : ℕ} (hp : p.Prime) {E : Subgroup M}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ (s + 1))
    (hR : ¬ p ^ (s + 1) ∣ Nat.card R)
    (hY : ∀ Y : Subgroup M, IsElemAbelian p Y → Y ≤ ψ.ker → Nat.card Y ≤ p) {y : R}
    (hyp : y ^ p = 1) (hy1 : y ≠ 1) :
    ∃ B : Subgroup M, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B, ψ b ∈ Subgroup.zpowers y := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite R := Finite.of_surjective ψ hψ
  obtain ⟨S₁, hyS⟩ := (isElemAbelian_zpowers hyp).isPGroup.exists_le_sylow
  obtain ⟨P₁, hP₁⟩ := Sylow.mapSurjective_surjective hψ p S₁
  obtain ⟨P₀, hEP₀⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P₀ P₁
  set E' : Subgroup M := E.map (MulAut.conj g).toMonoidHom with hE'def
  have hE' : IsElemAbelian p E' := hE.map _
  have hE'card : Nat.card E' = p ^ (s + 1) := by
    rw [hE'def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hEcard]
  have hE'P : E' ≤ P₁ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hg]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P₀ : Subgroup M) (hEP₀ hx)
  obtain ⟨hcardE', Y', hY'E', hY'ker, hY'card⟩ :=
    card_map_eq_of_kernel_trick ψ hp hE' hE'card hR hY
  have hmapP : (S₁ : Subgroup R) = (P₁ : Subgroup M).map ψ := by
    rw [← hP₁]
    rfl
  have hle : E'.map ψ ≤ S₁ := hmapP ▸ Subgroup.map_mono hE'P
  have hS₁card : Nat.card S₁ ≤ p ^ s := card_le_pow_of_isPGroup_of_not_dvd hp hR S₁.2
  have heq : E'.map ψ = S₁ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardE']; exact hS₁card)
  have hyE : y ∈ E'.map ψ := heq ▸ hyS (Subgroup.mem_zpowers y)
  obtain ⟨y', hy'E', hy'⟩ := hyE
  set B : Subgroup M := Subgroup.zpowers y' ⊔ Y' with hBdef
  have hBE' : B ≤ E' := sup_le (Subgroup.zpowers_le.2 hy'E') hY'E'
  refine ⟨B, hE'.isPGroup.to_le hBE', fun hcyc => ?_, ?_⟩
  · have hexp : ∀ b : B, b ^ p = 1 := fun b => Subtype.ext (hE'.2 b (hBE' b.2))
    have hle1 : Nat.card B ≤ p := by
      have h1 : Monoid.exponent B ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
      rw [← IsCyclic.exponent_eq_card]
      exact Nat.le_of_dvd hp.pos h1
    have hYB : Y' ≤ B := le_sup_right
    have hYeq : Y' = B :=
      Subgroup.eq_of_le_of_card_ge hYB (by rw [hY'card]; exact hle1)
    have hy'B : y' ∈ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers y')
    rw [← hYeq] at hy'B
    have : ψ y' = 1 := hY'ker hy'B
    exact hy1 (hy' ▸ this)
  · intro b hb
    have hle2 : B ≤ (Subgroup.zpowers y).comap ψ := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) fun k hk => ?_
      · rw [Subgroup.mem_comap, hy']
        exact Subgroup.mem_zpowers y
      · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 (hY'ker hk)]
        exact one_mem _
    exact hle2 hb

theorem exists_noncyclic_pGroup_of_kernel_trick [Finite M] {M' : Type*} [Group M']
    (φ : M →* M') {p s : ℕ} (hp : p.Prime) {E : Subgroup M} (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ (s + 1)) (hR : ¬ p ^ (s + 1) ∣ Nat.card φ.range)
    (hY : ∀ Y : Subgroup M, IsElemAbelian p Y → Y ≤ φ.ker → Nat.card Y ≤ p) {y : M'}
    (hy : y ∈ φ.range) (hyp : y ^ p = 1) (hy1 : y ≠ 1) :
    ∃ B : Subgroup M, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B, φ b ∈ Subgroup.zpowers y := by
  have hker : φ.rangeRestrict.ker = φ.ker := MonoidHom.ker_rangeRestrict φ
  obtain ⟨B, hBp, hBc, hB⟩ := exists_noncyclic_pGroup_of_kernel_trick_surjective φ.rangeRestrict
    φ.rangeRestrict_surjective hp hE hEcard hR (fun Y hY' hYk => hY Y hY' (hker ▸ hYk))
    (y := ⟨y, hy⟩) (Subtype.ext hyp) (fun h => hy1 (congrArg Subtype.val h))
  refine ⟨B, hBp, hBc, fun b hb => ?_⟩
  have h := hB b hb
  have h2 := Subgroup.map_mono (f := (φ.range).subtype) (Subgroup.zpowers_le.2
    (show (⟨y, hy⟩ : φ.range) ∈ Subgroup.zpowers (⟨y, hy⟩ : φ.range) from
      Subgroup.mem_zpowers _))
  have h3 : φ b ∈ (Subgroup.zpowers (⟨y, hy⟩ : φ.range)).map (φ.range).subtype :=
    ⟨φ.rangeRestrict b, h, rfl⟩
  rwa [MonoidHom.map_zpowers] at h3

end Lift

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
