module

public import CFSG.RankThree.PartOne.S12.Sec1511Y2Quot
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace Sec1511

@[expose] def KF1511Aut : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → Census3.TheoremThreeHyp ↥S →
      Subgroup.centralizer (S : Set H) = ⊥ →
      ∀ P : Subgroup H, IsSylowOf p P ⊤ → IsElementaryAbelian p (omegaOne p P) →
        (Nat.card (omegaOne p P) = p ^ 2 ∨ Nat.card (omegaOne p P) = p ^ 3) →
        ((∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 2 ∧ Census3.IsoLie ↥S (.A 1 q)) →
          Nat.card (omegaOne p P) = p ^ 2 ∧
            ∃ g ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H),
              OrderModC (omegaOne p P) g ((p ^ 2 - 1) / 2)) ∧
        ((∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 3 ∧ Census3.IsoLie ↥S (.A 1 q)) →
          Nat.card (omegaOne p P) = p ^ 3 ∧
            ∃ g ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H),
              OrderModC (omegaOne p P) g ((p ^ 3 - 1) / 2)) ∧
        (p = 5 → Nonempty (↥S ≃* alternatingGroup (Fin 10)) →
          Nat.card (omegaOne p P) = 25 ∧
            ∃ g ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H),
              OrderModC (omegaOne p P) g 8) ∧
        (p = 5 → Census3.IsoLie ↥S .tits →
          Nat.card (omegaOne p P) = 25 ∧
            ∃ F : Finset H, F.card = 48 ∧
              (∀ x ∈ F, x ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H)) ∧
              ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
                x⁻¹ * y ∉ Subgroup.centralizer ((omegaOne p P : Subgroup H) : Set H)) ∧
        (p = 5 → Census3.IsoLie ↥S (.suzuki 2) →
          Nat.card (omegaOne p P) = 25 ∧
            ∃ g ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H),
              OrderModC (omegaOne p P) g 5)

@[expose] def KFL225 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal →
    Subgroup.centralizer (S : Set H) = ⊥ →
    (∃ q : TauCeti.PrimePower, q.p = 5 ∧ q.exponent = 2 ∧ Census3.IsoLie ↥S (.A 1 q)) →
    ∀ Y₀ : Subgroup H, IsStronglyPEmbedded 5 Y₀ →
      ∀ P : Subgroup H, IsSylowOf 5 P ⊤ → IsElementaryAbelian 5 (omegaOne 5 P) →
        Nat.card (omegaOne 5 P) = 25 →
        Nat.card ↥P = 25 ∧
        (∀ V : Subgroup H, IsPGroup 2 ↥V →
          omegaOne 5 P ≤ Subgroup.normalizer (V : Set H) → V = ⊥) ∧
        Group.IsSolvable ↥Y₀ ∧
        ∃ g ∈ Subgroup.normalizer ((omegaOne 5 P : Subgroup H) : Set H), OrderModC (omegaOne 5 P) g 3

section Tools

@[expose] def HasNonabSimpleSection (q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (A : Subgroup X) (S : Type) (_ : Group S) (φ : ↥A →* S), Function.Surjective φ ∧ IsSimpleGroup S ∧
    (∃ a b : S, a * b ≠ b * a) ∧ q ∣ Nat.card S

theorem HasNonabSimpleSection.of_surjective {X Y : Type} [Group X] [Group Y] {q : ℕ} (π : X →* Y)
    (hπ : Function.Surjective π) (h : HasNonabSimpleSection q Y) : HasNonabSimpleSection q X := by
  obtain ⟨A, S, hSg, φ, hφ, hs, hn, hq⟩ := h
  let A' : Subgroup X := A.comap π
  let ψ : ↥A' →* ↥A := (π.comp A'.subtype).codRestrict A fun x => x.2
  have hψ : Function.Surjective ψ := fun y => by
    obtain ⟨x, hx⟩ := hπ (y : Y)
    exact ⟨⟨x, by simp [A', Subgroup.mem_comap, hx]⟩, Subtype.ext hx⟩
  exact ⟨A', S, hSg, φ.comp ψ, hφ.comp hψ, hs, hn, hq⟩

theorem HasNonabSimpleSection.of_injective {X Y : Type} [Group X] [Group Y] {q : ℕ} (ι : X →* Y)
    (hι : Function.Injective ι) (h : HasNonabSimpleSection q X) : HasNonabSimpleSection q Y := by
  obtain ⟨A, S, hSg, φ, hφ, hs, hn, hq⟩ := h
  let e : ↥A ≃* ↥(A.map ι) := A.equivMapOfInjective ι hι
  exact ⟨A.map ι, S, hSg, φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective, hs, hn, hq⟩

theorem not_hasNonabSimpleSection {X Q : Type} [Group X] [Finite X] [Group Q] {q : ℕ} (f : X →* Q)
    (hQ : Group.IsSolvable Q) (hk : ¬ q ∣ Nat.card f.ker) : ¬ HasNonabSimpleSection q X := by
  rintro ⟨A, S, hSg, φ, hφ, hsimple, ⟨a, b, hab⟩, hq⟩
  classical
  let ψ : ↥A →* Q := f.comp A.subtype
  have hNn : ψ.ker.Normal := ψ.normal_ker
  have hmapN : (ψ.ker.map φ).Normal := Subgroup.Normal.map hNn φ hφ
  rcases hsimple.eq_bot_or_eq_top_of_normal (ψ.ker.map φ) with hbot | htop
  · have hle : ψ.ker ≤ φ.ker := (Subgroup.map_eq_bot_iff _).1 hbot
    let ρ : ↥A ⧸ ψ.ker →* S := QuotientGroup.lift ψ.ker φ hle
    have hρ : Function.Surjective ρ := fun y => by
      obtain ⟨x, rfl⟩ := hφ y
      exact ⟨(x : ↥A ⧸ ψ.ker), rfl⟩
    have hrange : Group.IsSolvable ↥ψ.range :=
      Group.isSolvable_of_isSolvable_injective (f := ψ.range.subtype) ψ.range.subtype_injective
    have h1 : Group.IsSolvable (↥A ⧸ ψ.ker) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (QuotientGroup.quotientKerEquivRange ψ).toMonoidHom)
        (QuotientGroup.quotientKerEquivRange ψ).injective
    have h2 : Group.IsSolvable S := Group.isSolvable_of_surjective hρ
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 h2 a b)
  · have hsurj : Function.Surjective (φ.comp ψ.ker.subtype) := fun y => by
      have hy : y ∈ ψ.ker.map φ := htop ▸ Subgroup.mem_top y
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have h1 : Nat.card S ∣ Nat.card ψ.ker := Subgroup.card_dvd_of_surjective hsurj
    have hle2 : ψ.ker.map A.subtype ≤ f.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have h2 : Nat.card ψ.ker ∣ Nat.card f.ker := by
      have := Subgroup.card_dvd_of_le hle2
      rwa [Subgroup.card_map_of_injective A.subtype_injective] at this
    exact hk (hq.trans (h1.trans h2))

theorem isKGroup_subgroup_quotient {A : Type} [Group A] (hA : CFSG.IsKGroup A) (O : Subgroup A)
    [O.Normal] (S : Subgroup (A ⧸ O)) : CFSG.IsKGroup ↥S :=
  (hA.quotient O).subgroup S

theorem map_mem_normalizer {G H : Type*} [Group G] [Group H] (f : G →* H) {A : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (A : Set G)) :
    f n ∈ Subgroup.normalizer ((A.map f : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨n * a * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn a).1 ha, by simp⟩
  · rintro ⟨a, ha, hay⟩
    refine ⟨n⁻¹ * a * n, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (A : Set G)).inv_mem hn) a).1 ha
      simpa using this
    · have h1 : f a = f n * y * (f n)⁻¹ := hay
      rw [map_mul, map_mul, map_inv, h1]
      group

end Tools

section Arith

theorem arith_l2sq {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (h : (p ^ 2 - 1) / 2 ∣ Nat.lcm (p - 1) m) : p = 5 := by
  have hlcm : Nat.lcm (p - 1) m ≤ (p - 1) * m :=
    Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) (Nat.lcm_dvd_mul _ _)
  have hlpos : 0 < Nat.lcm (p - 1) m := Nat.lcm_pos (by omega) (by omega)
  have hle : (p ^ 2 - 1) / 2 ≤ (p - 1) * m := (Nat.le_of_dvd hlpos h).trans hlcm
  have hp7 : p ≤ 7 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 8 := ⟨p - 8, by omega⟩
    have h1 : (a + 8) ^ 2 - 1 = a ^ 2 + 16 * a + 63 := by
      have : (a + 8) ^ 2 = a ^ 2 + 16 * a + 64 := by ring
      omega
    have h2 : (a + 8 - 1) * m ≤ (a + 7) * 4 := by
      have : a + 8 - 1 = a + 7 := by omega
      rw [this]
      exact Nat.mul_le_mul_left _ hm4
    have h3 : (a ^ 2 + 16 * a + 63) / 2 ≤ (a + 7) * 4 := by
      rw [h1] at hle
      exact hle.trans h2
    omega
  interval_cases p
  · rfl
  · exact absurd hp (by norm_num)
  · exfalso
    interval_cases m <;> simp [Nat.lcm] at h

theorem arith_l2cube {p m : ℕ} (hp5 : 5 ≤ p) (hm1 : 1 ≤ m) (hm6 : m ≤ 6)
    (h : (p ^ 3 - 1) / 2 ∣ Nat.lcm (p - 1) m) : False := by
  have hlcm : Nat.lcm (p - 1) m ≤ (p - 1) * m :=
    Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) (Nat.lcm_dvd_mul _ _)
  have hlpos : 0 < Nat.lcm (p - 1) m := Nat.lcm_pos (by omega) (by omega)
  have hle : (p ^ 3 - 1) / 2 ≤ (p - 1) * m := (Nat.le_of_dvd hlpos h).trans hlcm
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 5 := ⟨p - 5, by omega⟩
  have h1 : (a + 5) ^ 3 - 1 = a ^ 3 + 15 * a ^ 2 + 75 * a + 124 := by
    have : (a + 5) ^ 3 = a ^ 3 + 15 * a ^ 2 + 75 * a + 125 := by ring
    omega
  have h2 : (a + 5 - 1) * m ≤ (a + 4) * 6 := by
    have : a + 5 - 1 = a + 4 := by omega
    rw [this]
    exact Nat.mul_le_mul_left _ hm6
  have h3 : (a ^ 3 + 15 * a ^ 2 + 75 * a + 124) / 2 ≤ (a + 4) * 6 := by
    rw [h1] at hle
    exact hle.trans h2
  omega

theorem arith_eight {m : ℕ} (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (h : 8 ∣ Nat.lcm (5 - 1) m) : False := by
  interval_cases m <;> simp [Nat.lcm] at h

theorem arith_five {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) (h : 5 ∣ Nat.lcm (5 - 1) m) : False := by
  interval_cases m <;> simp [Nat.lcm] at h

end Arith

section Main

variable {M : Type} [Group M] [Finite M] {p : ℕ}

structure Y2Cfg (p : ℕ) (M₀ P B : Subgroup M) : Prop where
  prime : p.Prime
  p5 : 5 ≤ p
  syl : IsSylowOf p P ⊤
  omega : omegaOne p P = B
  Bel : IsElementaryAbelian p ↥B
  card : Nat.card ↥B = p ^ 2 ∨ Nat.card ↥B = p ^ 3
  spe : IsStronglyPEmbedded p M₀
  coprime : ∀ V : Subgroup M, V.Normal → ¬ p ∣ Nat.card ↥V → V ≤ M₀

structure Y2Aut (p : ℕ) (B : Subgroup M) : Prop where
  ord6 : ∀ n ∈ Subgroup.normalizer (B : Set M), ∃ m : ℕ, 1 ≤ m ∧ m ≤ 6 ∧
    n ^ Nat.lcm (p - 1) m ∈ Subgroup.centralizer (B : Set M)
  ord4 : Nat.card ↥B = p ^ 2 → ∀ n ∈ Subgroup.normalizer (B : Set M), ∃ m : ℕ, 1 ≤ m ∧ m ≤ 4 ∧
    n ^ Nat.lcm (p - 1) m ∈ Subgroup.centralizer (B : Set M)
  count : Nat.card ↥B = 25 → ∀ F : Finset M, (∀ x ∈ F, x ∈ Subgroup.normalizer (B : Set M)) →
    (∀ x ∈ F, ∀ y ∈ F, x ≠ y → x⁻¹ * y ∉ Subgroup.centralizer (B : Set M)) → F.card ≤ 32

structure L225Out (p : ℕ) (M₀ P B O : Subgroup M) : Prop where
  p5 : p = 5
  card : Nat.card ↥B = 25
  PB : P = B
  two : ∀ V : Subgroup M, IsPGroup 2 ↥V → B ≤ Subgroup.normalizer (V : Set M) → V ≤ O
  simple5 : ∃ (Q : Type) (_ : Group Q) (f : ↥M₀ →* Q), Group.IsSolvable Q ∧ ¬ 5 ∣ Nat.card f.ker
  three : ∃ n ∈ Subgroup.normalizer (B : Set M), OrderModC B n 3

theorem exists_dvd_lcm_of_orderModC [Fact p.Prime] {O : Subgroup M} [O.Normal] {B : Subgroup M}
    (hBp : IsPGroup p ↥B) (hO : ¬ p ∣ Nat.card O) {g : M ⧸ O}
    (hg : g ∈ Subgroup.normalizer ((B.map (QuotientGroup.mk' O) : Subgroup (M ⧸ O)) : Set (M ⧸ O)))
    {r : ℕ} (hr : OrderModC (B.map (QuotientGroup.mk' O)) g r) {M₁ : ℕ}
    (hn : ∀ n ∈ Subgroup.normalizer (B : Set M), ∃ m : ℕ, 1 ≤ m ∧ m ≤ M₁ ∧
      n ^ Nat.lcm (p - 1) m ∈ Subgroup.centralizer (B : Set M)) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ M₁ ∧ r ∣ Nat.lcm (p - 1) m := by
  obtain ⟨n, hnN, rfl⟩ := exists_lift_normalizer hBp hO hg
  obtain ⟨m, hm1, hm2, hnm⟩ := hn n hnN
  exact ⟨m, hm1, hm2, orderModC_dvd hr ((pow_mem_centralizer_iff hBp hO hnN _).1 hnm)⟩

theorem y2_aux (hSPE : ExtSPE) (hAut : KF1511Aut) (hL : KFL225) {O : Subgroup M} [O.Normal]
    (hOcop : ¬ p ∣ Nat.card O) (hObot : pPrimeCore p (M ⧸ O) = ⊥) {M₀ P B : Subgroup M}
    (hOM₀ : O ≤ M₀) (hc : Y2Cfg p M₀ P B) (ha : Y2Aut p B) (hK : CFSG.IsKGroup M)
    (hrk : IsStronglyPEmbedded p (M₀.map (QuotientGroup.mk' O)) →
      CFSG.twoLocalOddRank ↥(generalizedFitting (M ⧸ O)) ≤ 3) : L225Out p M₀ P B O := by
  classical
  have hp : p.Prime := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  have hY₀ : IsStronglyPEmbedded p (M₀.map (QuotientGroup.mk' O)) :=
    spe_map_quotient hc.spe hOM₀ hOcop
  obtain ⟨hSsimple, hSnonab, hSnormal, hSC⟩ := spe_fstar hp hObot hY₀
  have hS3 : Census3.TheoremThreeHyp ↥(generalizedFitting (M ⧸ O)) :=
    ⟨hSsimple, hSnonab, isKGroup_subgroup_quotient hK O _, hrk hY₀⟩
  have hBp : IsPGroup p ↥B := by
    have := hc.Bel
    exact IsElementaryAbelian.isPGroup p ↥B
  have hPp : IsPGroup p ↥P := hc.syl.2.1
  have hPhat : IsSylowOf p (P.map (QuotientGroup.mk' O)) ⊤ := isSylowOf_map_mk' hc.syl
  have hΩ : omegaOne p (P.map (QuotientGroup.mk' O)) = B.map (QuotientGroup.mk' O) := by
    rw [omegaOne_map_mk' hPp hOcop, hc.omega]
  have hBel : IsElementaryAbelian p ↥(B.map (QuotientGroup.mk' O)) := by
    have := hc.Bel
    exact IsElementaryAbelian.map _
  have hBcard : Nat.card ↥(B.map (QuotientGroup.mk' O)) = Nat.card ↥B := card_map_mk' hBp hOcop
  have hΩel : IsElementaryAbelian p ↥(omegaOne p (P.map (QuotientGroup.mk' O))) := by
    rw [hΩ]; exact hBel
  have hΩcard : Nat.card ↥(omegaOne p (P.map (QuotientGroup.mk' O))) = p ^ 2 ∨
      Nat.card ↥(omegaOne p (P.map (QuotientGroup.mk' O))) = p ^ 3 := by
    rw [hΩ, hBcard]; exact hc.card
  have hspe := hSPE p hp hc.p5 (M ⧸ O) _ hSnormal hS3 hSC _ hY₀ _ hPhat hΩel hΩcard
  obtain ⟨hA2, hA3, hA10, hAT, hASz⟩ :=
    hAut p hp hc.p5 (M ⧸ O) _ hSnormal hS3 hSC _ hPhat hΩel hΩcard
  rw [hΩ] at hA2 hA3 hA10 hAT hASz
  have hfinal : p = 5 → (∃ q : TauCeti.PrimePower, q.p = 5 ∧ q.exponent = 2 ∧
      Census3.IsoLie ↥(generalizedFitting (M ⧸ O)) (.A 1 q)) → Nat.card ↥B = 25 →
      L225Out p M₀ P B O := by
    intro hp5 hq hB25
    subst hp5
    have hΩel' : IsElementaryAbelian 5 ↥(omegaOne 5 (P.map (QuotientGroup.mk' O))) := hΩel
    have hΩcard' : Nat.card ↥(omegaOne 5 (P.map (QuotientGroup.mk' O))) = 25 := by
      rw [hΩ, hBcard]; exact hB25
    obtain ⟨hP25, h1, h2, g, hg, hgo⟩ := hL (M ⧸ O) _ hSnormal hSC hq _ hY₀ _ hPhat hΩel' hΩcard'
    rw [hΩ] at h1 hg hgo
    have hP25' : Nat.card ↥P = 25 := by rw [← card_map_mk' hPp hOcop]; exact hP25
    have hBP : B ≤ P := by
      rw [← hc.omega]
      exact (Subgroup.closure_le _).2 fun x hx => hx.1
    refine ⟨rfl, hB25, (Subgroup.eq_of_le_of_card_ge hBP (by rw [hP25', hB25])).symm, ?_, ?_, ?_⟩
    · intro V hV hBV
      have hnorm : B.map (QuotientGroup.mk' O) ≤
          Subgroup.normalizer ((V.map (QuotientGroup.mk' O) : Subgroup (M ⧸ O)) : Set (M ⧸ O)) := by
        rintro _ ⟨b, hb, rfl⟩
        exact map_mem_normalizer _ (hBV hb)
      have hVbot := h1 (V.map (QuotientGroup.mk' O)) (hV.map _) hnorm
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hVbot
      exact hVbot
    · refine ⟨↥(M₀.map (QuotientGroup.mk' O)), inferInstance,
        (QuotientGroup.mk' O).subgroupMap M₀, h2, ?_⟩
      intro hdvd
      apply hOcop
      have hle : ((QuotientGroup.mk' O).subgroupMap M₀).ker.map M₀.subtype ≤ O := by
        rintro _ ⟨x, hx, rfl⟩
        have hx1 : (QuotientGroup.mk' O).subgroupMap M₀ x = 1 := hx
        have hx2 : QuotientGroup.mk' O (x : M) = 1 := congrArg Subtype.val hx1
        exact (QuotientGroup.eq_one_iff _).1 hx2
      have := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective M₀.subtype_injective] at this
      exact hdvd.trans this
    · obtain ⟨n, hn, hnπ⟩ := exists_lift_normalizer hBp hOcop hg
      subst hnπ
      obtain ⟨h0, h3, hmin⟩ := hgo
      refine ⟨n, hn, h0, ?_, fun k hk0 hk3 hkc => hmin k hk0 hk3 ?_⟩
      · exact (pow_mem_centralizer_iff hBp hOcop hn 3).2 h3
      · exact (pow_mem_centralizer_iff hBp hOcop hn k).1 hkc
  rcases hspe with ⟨q, hqp, hq23, hq⟩ | ⟨hp5, hcase⟩
  · rcases hq23 with hq2 | hq3
    · obtain ⟨hcard2, g, hg, hgo⟩ := hA2 ⟨q, hqp, hq2, hq⟩
      have hBc : Nat.card ↥B = p ^ 2 := by rw [← hBcard]; exact hcard2
      obtain ⟨m, hm1, hm4, hdvd⟩ :=
        exists_dvd_lcm_of_orderModC hBp hOcop hg hgo (ha.ord4 hBc)
      have hp5 : p = 5 := arith_l2sq hp hc.p5 hm1 hm4 hdvd
      subst hp5
      exact hfinal rfl ⟨q, hqp, hq2, hq⟩ (by rw [hBc]; norm_num)
    · obtain ⟨hcard3, g, hg, hgo⟩ := hA3 ⟨q, hqp, hq3, hq⟩
      obtain ⟨m, hm1, hm6, hdvd⟩ := exists_dvd_lcm_of_orderModC hBp hOcop hg hgo ha.ord6
      exact (arith_l2cube hc.p5 hm1 hm6 hdvd).elim
  · subst hp5
    rcases hcase with hA | hT | hSz
    · obtain ⟨hc25, g, hg, hgo⟩ := hA10 rfl hA
      have hB25 : Nat.card ↥B = 5 ^ 2 := by rw [← hBcard]; exact hc25
      obtain ⟨m, hm1, hm4, hdvd⟩ := exists_dvd_lcm_of_orderModC hBp hOcop hg hgo (ha.ord4 hB25)
      exact (arith_eight hm1 (hm4.trans (by norm_num)) hdvd).elim
    · obtain ⟨hc25, F, hFc, hFN, hFne⟩ := hAT rfl hT
      have hB25 : Nat.card ↥B = 25 := by rw [← hBcard]; exact hc25
      have hlift : ∀ y ∈ F, ∃ n ∈ Subgroup.normalizer (B : Set M),
          QuotientGroup.mk' O n = y := fun y hy => exists_lift_normalizer hBp hOcop (hFN y hy)
      choose! f hf using hlift
      have hinj : Set.InjOn f ↑F := fun a ha' b hb hab => by
        rw [← (hf a ha').2, ← (hf b hb).2, hab]
      have hcard' : (F.image f).card = 48 := by rw [Finset.card_image_of_injOn hinj]; exact hFc
      have hle := ha.count hB25 (F.image f)
        (by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
          exact (hf y hy).1)
        (by
          intro x hx y hy hxy hxy'
          obtain ⟨a, ha', rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
          have hab : a ≠ b := fun h => hxy (by rw [h])
          apply hFne a ha' b hb hab
          have := map_mem_centralizer (O := O) hxy'
          simpa [map_mul, map_inv, (hf a ha').2, (hf b hb).2] using this)
      omega
    · obtain ⟨hc25, g, hg, hgo⟩ := hASz rfl hSz
      have hB25 : Nat.card ↥B = 5 ^ 2 := by rw [← hBcard]; exact hc25
      obtain ⟨m, hm1, hm4, hdvd⟩ := exists_dvd_lcm_of_orderModC hBp hOcop hg hgo (ha.ord4 hB25)
      exact (arith_five hm1 hm4 hdvd).elim

end Main

end Sec1511

end CFSG.RankThree.PartOne
