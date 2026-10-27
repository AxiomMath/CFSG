module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGL44iiiMarking (p : ℕ) (Bs : Subgroup G) (x : G) (X K : Subgroup G) : Prop :=
  LargeEvenMarking K (fun _ _ _ I F θ => Bs ≤ Subgroup.normalizer (K : Set G) ∧
    (∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), ∃ φ ∈ I,
      LargeEvenInduces θ (fun k k' => (k' : G) = b⁻¹ * k * b) φ) ∧
    ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
      LargeEvenInduces θ (fun k k' => (k' : G) = x⁻¹ * k * x) (u * f * u⁻¹))

end Defs

@[expose] def GGL44iiiMarkingInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G),
    GGFieldCaseNoBL5 p B Bs x L D J X → GGTableBModule p Bs x L B₂ → GGL43 Bs x X →
      GGL44i p Bs x X → GGL44ii Bs x X B₂ →
      ∀ d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)), d ≠ 1 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        Subgroup.zpowers y = Subgroup.zpowers d → GGL44iiiMarking p Bs x X K

@[expose] def GGL44iiiNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G),
    GGFieldCaseNoBL5 p B Bs x L D J X → GGTableBModule p Bs x L B₂ → GGL43 Bs x X →
      GGL44i p Bs x X → GGL44ii Bs x X B₂ →
      ∀ d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)), d ≠ 1 →
      ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
        Subgroup.zpowers y = Subgroup.zpowers d

@[expose] def GGRawInnField (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    (∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) ∧ (∀ φ ∈ I, φ⁻¹ ∈ I) ∧ (∀ r : R, MulAut.conj r ∈ I) ∧
      ∀ f ∈ F, orderOf f = p → f ∉ I

@[expose] def GGRawInnFieldInput : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (GGRawInnField p)

section Proofs

variable {G : Type} [Group G] [Finite G]

theorem ggL44iii_iff {p : ℕ} {B Bs : Subgroup G} {x : G} {D J X : Subgroup G} {d y : G}
    {K : Subgroup G} :
    GGL44iii p B Bs x D J X d y K ↔
      D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) = Subgroup.zpowers d ∧ d ≠ 1 ∧
        GGNbr p B x D J y K ∧ Subgroup.zpowers y = Subgroup.zpowers d ∧
        GGL44iiiMarking p Bs x X K :=
  Iff.rfl

omit [Finite G] in
theorem not_mem_sup_of_raw {p : ℕ} {B₁ K : Subgroup G} {x : G}
    (h : LargeEvenMarking K (fun _ R _ I F θ => B₁ ≤ Subgroup.normalizer (K : Set G) ∧
      GGRawInnField p R I F ∧
      (∀ b ∈ B₁, ∃ φ ∈ I, LargeEvenInduces θ (fun k k' => (k' : G) = b⁻¹ * k * b) φ) ∧
      ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
        LargeEvenInduces θ (fun k k' => (k' : G) = x⁻¹ * k * x) (u * f * u⁻¹))) :
    x ∉ B₁ ⊔ K := by
  intro hx
  obtain ⟨-, lab, -, hraw⟩ := h
  obtain ⟨R, _, I, F, hs, hna, θ, hB₁K, hfacts, hB, f, hf, u, hu, hord, hxind⟩ :=
    largeEvenRawDatum_exists hraw
  obtain ⟨hmul, hinv, hinn, hF⟩ := hfacts hs hna
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right B₁ K hB₁K] at hx
  obtain ⟨b, hb, k, hk, rfl⟩ := hx
  obtain ⟨φ, hφ, hbφ⟩ := hB b hb
  set t : R := θ (QuotientGroup.mk (⟨k, hk⟩ : K)) with ht
  have heq : u * f * u⁻¹ = MulAut.conj t⁻¹ * φ := by
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hbK : b⁻¹ * (l : G) * b ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hB₁K hb)) l).mp l.2
      simpa using this
    have hxK : (b * k)⁻¹ * (l : G) * (b * k) ∈ K := by
      have e : (b * k)⁻¹ * (l : G) * (b * k) = k⁻¹ * (b⁻¹ * (l : G) * b) * k := by group
      rw [e]
      exact K.mul_mem (K.mul_mem (K.inv_mem hk) hbK) hk
    have h1 := hxind l ⟨_, hxK⟩ rfl
    have h2 := hbφ l ⟨_, hbK⟩ rfl
    rw [h1, MulAut.mul_apply, MulAut.conj_apply, h2, ht, inv_inv, ← map_inv, ← map_mul, ← map_mul,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  apply hF f hf hord
  have hf' : f = u⁻¹ * (MulAut.conj t⁻¹ * φ) * u := by
    rw [← heq]
    group
  rw [hf']
  exact hmul _ (hmul _ (hinv u hu) _ (hmul _ (hinn _) _ hφ)) _ hu

theorem ggFieldNbrFieldAut_of_inputs (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (hmk : GGL44iiiMarkingInput)
    (hraw : GGRawInnFieldInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) : GGFieldNbrFieldAut p B Bs x D J := by
  intro X hXN hCX hXn hXp hXC d hd hd1 y K hnbr hyd
  have hFC : GGFieldCaseNoBL5 p B Bs x L D J X := ⟨hcfg, hXN, hCX, hXn, hXp, hXC⟩
  have hβ := hcfg.1.2.2.2.2.2.1
  have : Fact p.Prime := ⟨hβ.1⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have h43 := ggL43_noBL5 hTB hNN hTBM hTBA hFC
  have h44 := ggL44i_of_ggL43 hBs hxBs hXN hXp h43
  obtain ⟨B₂, hM⟩ := hTBM G p B Bs x L D J hcfg
  have h44ii := ggL44ii_of_ggL43_noBL5 hFC hM h43 h44
  have hK := hmk G p B Bs x L D J X B₂ hFC hM h43 h44 h44ii d hd hd1 y K hnbr hyd
  have hK' := largeEvenMarking_and_labelAll (S := fun _ => True)
    (fun lab hlab _ => hraw p hβ.1 hβ.2.1 lab hlab) (fun _ _ _ _ _ _ _ => trivial) hK
  refine not_mem_sup_of_raw (p := p) (largeEvenMarking_mono ?_ hK')
  rintro lab R _ I F θ ⟨⟨hN, hB₁, hx⟩, hfacts⟩
  exact ⟨inf_le_left.trans hN, hfacts, hB₁, hx⟩

theorem exists_inf_eq_zpowers_of_ggL43 {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (h43 : GGL43 Bs x X) :
    ∃ d : G, D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) = Subgroup.zpowers d ∧ d ≠ 1 := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  obtain ⟨hDB, -, hDcard, hxD, -⟩ := hcfg.2.2.1
  have hDBs : D ≤ Bs := hDB.trans hcfg.2.1.1
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hxBs : x ∈ Bs := hDBs hxD
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  have hZcard : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  have hpp : p < p ^ 2 := by nlinarith [hp.two_le]
  obtain ⟨e, heD, heZ⟩ : ∃ e ∈ D, e ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers x from h)
    rw [hDcard, hZcard] at this
    omega
  have hxB : ∀ b ∈ B₁, x * b = b * x := fun b hb => mul_comm_of_isElemAbelian hBs hxBs hb.1
  have heS : e ∈ B₁ ⊔ Subgroup.zpowers x := by
    rw [← h43.2]
    exact hDBs heD
  obtain ⟨b, hb, i, rfl⟩ := exists_mem_mul_pow_of_mem_sup hxB heS
  have hbD : b ∈ D := by
    have := D.mul_mem heD (D.inv_mem (D.pow_mem hxD i))
    simpa using this
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact heZ (by simp)
  refine ⟨b, ?_, hb1⟩
  have hbp : b ^ p = 1 := hBs.2 b hb.1
  have hle : Nat.card (D ⊓ B₁ : Subgroup G) ≤ p := by
    have hdvd : Nat.card (D ⊓ B₁ : Subgroup G) ∣ p ^ 2 :=
      hDcard ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, -, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hlt : Nat.card (D ⊓ B₁ : Subgroup G) < p ^ 2 := by
      rw [← hDcard]
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => h43.1 ?_)
      have hx' : x ∈ D ⊓ B₁ := by rw [h]; exact hxD
      exact hx'.2
    rw [hkeq] at hlt ⊢
    have hk : k < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hbD, hb⟩) ?_
  rw [Nat.card_zpowers, orderOf_eq_prime hbp hb1]
  exact hle

theorem ggL44iiiInput_of_noBL5 (hnb : GGL44iiiNbrInput) (hmk : GGL44iiiMarkingInput) :
    GGL44iiiInput := by
  intro G _ _ p B Bs x L D J X B₂ hFC hM h43 h44 h44ii
  have hFC' := hFC.noBL5
  obtain ⟨d, hd, hd1⟩ := exists_inf_eq_zpowers_of_ggL43 hFC'.1 h43
  have hdmem : d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [hd]
    exact Subgroup.mem_zpowers d
  obtain ⟨y, K, hnbr, hyd⟩ := hnb G p B Bs x L D J X B₂ hFC' hM h43 h44 h44ii d hdmem hd1
  exact ⟨d, y, K, hd, hd1, hnbr, hyd,
    hmk G p B Bs x L D J X B₂ hFC' hM h43 h44 h44ii d hdmem hd1 y K hnbr hyd⟩

end Proofs

end CFSG.StandardType

end
