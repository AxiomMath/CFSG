module

public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15SPL
public import CFSG.RankThree.PartOne.S12.Sec12FusSyl
public import CFSG.RankThree.PartOne.S12.Sec12FusChoice
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace Sec1511

variable {G : Type} [Group G]

theorem elemAbelian_of_le {p : ℕ} {A K : Subgroup G} (hA : IsElementaryAbelian p ↥A) (hKA : K ≤ A) :
    IsElementaryAbelian p ↥K := CFSG.IsElementaryAbelian.of_le hA hKA

theorem omegaOne_ne_bot [Finite G] {q : ℕ} [Fact q.Prime] {R : Subgroup G} (hR : IsPGroup q ↥R) (hR1 : R ≠ ⊥) :
    omegaOne q R ≠ ⊥ := by
  have hdvd : q ∣ Nat.card ↥R := by
    rcases hR.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hR1
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) q hdvd
  intro hbot
  have hxmem : (x : G) ∈ omegaOne q R :=
    Subgroup.subset_closure ⟨x.2, by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Subtype.val this⟩
  rw [hbot, Subgroup.mem_bot] at hxmem
  have : x = 1 := Subtype.ext hxmem
  rw [this, orderOf_one] at hx
  exact (Fact.out : q.Prime).one_lt.ne hx

theorem sq_dvd_card_of_not_isCyclic [Finite G] {p : ℕ} (hp : p.Prime) {B : Subgroup G}
    (hB : IsElementaryAbelian p ↥B) (hnc : ¬ IsCyclic ↥B) : p ^ 2 ∣ Nat.card ↥B := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p ↥B).exists_card_eq
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · exfalso
    apply hnc
    interval_cases k
    · have : Nat.card ↥B = 1 := by simpa using hk
      have : Subsingleton ↥B := (Nat.card_eq_one_iff_unique.1 this).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (by simpa using hk)
  · rw [hk]
    exact pow_dvd_pow p hk2

theorem le_normalizer_of_le_comm {E B : Subgroup G} [IsMulCommutative ↥E] (hBE : B ≤ E) :
    E ≤ Subgroup.normalizer (B : Set G) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro b
  have hcomm : ∀ b' ∈ E, e * b' * e⁻¹ = b' := fun b' hb' => by
    have := (mul_comm' (⟨e, he⟩ : ↥E) ⟨b', hb'⟩)
    have h2 : e * b' = b' * e := congrArg Subtype.val this
    rw [h2]; group
  constructor
  · intro hb
    rw [hcomm b (hBE hb)]; exact hb
  · intro hb
    by_cases hbE : b ∈ E
    · rwa [hcomm b hbE] at hb
    · exfalso
      apply hbE
      have h2 : e * b * e⁻¹ ∈ E := hBE hb
      have : b = e⁻¹ * (e * b * e⁻¹) * e := by group
      rw [this]
      exact E.mul_mem (E.mul_mem (E.inv_mem he) h2) he

theorem conj_omegaOne_mem {p : ℕ} {T Q : Subgroup G} {k : G} (h : ∀ a ∈ T, k⁻¹ * a * k ∈ Q)
    {x : G} (hx : x ∈ omegaOne p T) : k⁻¹ * x * k ∈ omegaOne p Q := by
  refine Subgroup.closure_induction (p := fun x _ => k⁻¹ * x * k ∈ omegaOne p Q) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨hyT, hyp⟩
    refine Subgroup.subset_closure ⟨h y hyT, ?_⟩
    have : (k⁻¹ * y * k) ^ p = k⁻¹ * y ^ p * k := by
      have := conj_pow (a := k⁻¹) (b := y) (i := p)
      simpa [mul_assoc] using this
    rw [this, hyp]; group
  · simp
  · intro a b _ _ ha hb
    have : k⁻¹ * (a * b) * k = (k⁻¹ * a * k) * (k⁻¹ * b * k) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    have : k⁻¹ * a⁻¹ * k = (k⁻¹ * a * k)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem isSylowOf_conjSub {p : ℕ} {P Y : Subgroup G} (h : IsSylowOf p P Y) (g : G) :
    IsSylowOf p (conjSub g P) (conjSub g Y) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map _, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact h.2.2

theorem mem_normalizer_map_subtype {Y' : Subgroup G} {R : Subgroup ↥Y'} {g : ↥Y'}
    (hg : g ∈ Subgroup.normalizer (R : Set ↥Y')) :
    (g : G) ∈ Subgroup.normalizer ((R.map Y'.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨g * r * g⁻¹, (hg r).1 hr, rfl⟩
  · intro hx
    obtain ⟨r, hr, hrx⟩ := (Subgroup.mem_map).1 hx
    have hr' : g * (g⁻¹ * r * g) * g⁻¹ ∈ R := by simpa [mul_assoc] using hr
    have h1 : g⁻¹ * r * g ∈ R := (hg (g⁻¹ * r * g)).2 hr'
    refine ⟨g⁻¹ * r * g, h1, ?_⟩
    have : (g : G) * x * (g : G)⁻¹ = (r : G) := hrx.symm
    show (g : G)⁻¹ * (r : G) * (g : G) = x
    rw [← this]; group

structure Setting (p : ℕ) (E N : Subgroup G) : Prop where
  prime : p.Prime
  Eel : IsElementaryAbelian p ↥E
  WN : Subgroup.normalizer (E : Set G) ≤ N
  hN : ∀ U : Subgroup G, U ≤ E → U ≠ ⊥ → Subgroup.normalizer (U : Set G) ≤ N
  rank : ∀ F : Subgroup G, IsElementaryAbelian p ↥F →
    (∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ F ≤ Subgroup.normalizer (S : Set G)) →
    Nat.card ↥F ≤ p ^ 3

@[expose] def OmegaHyp (p : ℕ) (E : Subgroup G) : Prop :=
  ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q → omegaOne p Q = E

@[expose] def KAHyp (p : ℕ) (E N A₀ : Subgroup G) : Prop :=
  ∀ Y P : Subgroup G, (∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ Y ≤ Subgroup.normalizer (S : Set G)) →
    ¬ Y ≤ N → IsSylowOf p P Y → P ⊓ E = A₀ →
    ∀ x ∈ P, x ∈ Subgroup.normalizer (A₀ : Set G) → x ^ p = 1 → x ∈ Subgroup.centralizer (A₀ : Set G)

structure Y1Out (p : ℕ) (E N Y' P : Subgroup G) : Prop where
  syl : IsSylowOf p P Y'
  noncyc : ¬ IsCyclic ↥(P ⊓ E)
  omega : omegaOne p P = P ⊓ E
  normal : P ≤ Subgroup.normalizer ((P ⊓ E : Subgroup G) : Set G)
  card : Nat.card ↥(P ⊓ E) = p ^ 2 ∨ Nat.card ↥(P ⊓ E) = p ^ 3
  PN : P ≤ N
  spe : IsStronglyPEmbedded p ((N ⊓ Y').subgroupOf Y')
  coprime : ∀ V : Subgroup G, V ≤ Y' → (∀ y ∈ Y', ∀ v ∈ V, y * v * y⁻¹ ∈ V) → ¬ p ∣ Nat.card ↥V →
    V ≤ N

theorem y1Out_of_omega [Finite G] {p : ℕ} {E N Y' P : Subgroup G} (hS : Setting p E N)
    (hY2 : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ Y' ≤ Subgroup.normalizer (S : Set G))
    (hYN : ¬ Y' ≤ N) (hP : IsSylowOf p P Y') (hnc : ¬ IsCyclic ↥(P ⊓ E))
    (hT : omegaOne p (P ⊓ Subgroup.normalizer ((P ⊓ E : Subgroup G) : Set G)) = P ⊓ E) :
    Y1Out p E N Y' P := by
  classical
  have hp : p.Prime := hS.prime
  have : Fact p.Prime := ⟨hp⟩
  set B : Subgroup G := P ⊓ E with hB
  have hBE : B ≤ E := inf_le_right
  have hBP : B ≤ P := inf_le_left
  have hBel : IsElementaryAbelian p ↥B := elemAbelian_of_le hS.Eel hBE
  have hB1 : B ≠ ⊥ := by
    intro h
    apply hnc
    have : IsCyclic ↥B := by rw [h]; infer_instance
    exact this
  have hNB : Subgroup.normalizer (B : Set G) ≤ N := hS.hN B hBE hB1
  set T : Subgroup G := P ⊓ Subgroup.normalizer (B : Set G) with hTdef
  have hTP : T = P := by
    by_contra hne
    obtain ⟨y, hyP, hyT, hyN⟩ := Sec12Fus.exists_mem_normalizer_sdiff (p := p) (inf_le_left : T ≤ P)
      hP.2.1 hne
    have hyB : y ∈ Subgroup.normalizer (B : Set G) := by
      have := Sec12Fus.mem_normalizer_omegaOne (p := p) hyN
      rwa [hT] at this
    exact hyT ⟨hyP, hyB⟩
  have hPnorm : P ≤ Subgroup.normalizer (B : Set G) := fun x hx => by
    have : x ∈ T := by rw [hTP]; exact hx
    exact this.2
  have hΩ : omegaOne p P = B := by
    calc omegaOne p P = omegaOne p T := by rw [hTP]
      _ = B := hT
  have hPN : P ≤ N := hPnorm.trans hNB
  have hdvd := sq_dvd_card_of_not_isCyclic hp hBel hnc
  have hcard : Nat.card ↥B = p ^ 2 ∨ Nat.card ↥B = p ^ 3 := by
    have hle : Nat.card ↥B ≤ p ^ 3 := by
      obtain ⟨S, hS1, hS2, hS3⟩ := hY2
      exact hS.rank B hBel ⟨S, hS1, hS2, (hBP.trans hP.1).trans hS3⟩
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p ↥B).exists_card_eq
    have hk2 : 2 ≤ k := by
      rw [hk] at hdvd
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
    have hk3 : k ≤ 3 := by
      rw [hk] at hle
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
    interval_cases k
    · exact Or.inl hk
    · exact Or.inr hk
  have hPY : P ≤ Y' := hP.1
  have hspe : IsStronglyPEmbedded p ((N ⊓ Y').subgroupOf Y') := by
    refine stronglyPEmbedded_of_normalizers_le hp (P := P.subgroupOf Y')
      (H := (N ⊓ Y').subgroupOf Y') ?_ ?_ ?_ ?_ ?_
    · refine ⟨le_top, ?_, ?_⟩
      · exact hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm
      · rw [Subgroup.relIndex_top_right]
        exact hP.2.2
    · intro h
      apply hB1
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hPY (hBP hx)⟩ : ↥Y') ∈ P.subgroupOf Y' := Subgroup.mem_subgroupOf.2 (hBP hx)
      rw [h] at this
      simpa using this
    · intro x hx
      exact Subgroup.mem_subgroupOf.2 ⟨hPN (Subgroup.mem_subgroupOf.1 hx), x.2⟩
    · intro h
      apply hYN
      intro y hy
      have : (⟨y, hy⟩ : ↥Y') ∈ (N ⊓ Y').subgroupOf Y' := by rw [h]; trivial
      exact (Subgroup.mem_subgroupOf.1 this).1
    · intro R hR hR1 g hg
      have hRP : R.map Y'.subtype ≤ P := by
        rintro _ ⟨r, hr, rfl⟩
        exact Subgroup.mem_subgroupOf.1 (hR hr)
      have hR'1 : R.map Y'.subtype ≠ ⊥ := fun h => hR1 (by
        rw [eq_bot_iff]
        intro r hr
        have h1 : (r : G) ∈ R.map Y'.subtype := ⟨r, hr, rfl⟩
        rw [h, Subgroup.mem_bot] at h1
        exact Subgroup.mem_bot.2 (Subtype.ext h1))
      have hRp : IsPGroup p ↥(R.map Y'.subtype) := hP.2.1.to_le hRP
      have hΩ1 : omegaOne p (R.map Y'.subtype) ≠ ⊥ := omegaOne_ne_bot hRp hR'1
      have hΩE : omegaOne p (R.map Y'.subtype) ≤ E := by
        refine (Subgroup.closure_le _).2 ?_
        rintro x ⟨hxR, hxp⟩
        have : x ∈ omegaOne p P := Subgroup.subset_closure ⟨hRP hxR, hxp⟩
        rw [hΩ] at this
        exact hBE this
      have hgn := Sec12Fus.mem_normalizer_omegaOne (p := p) (mem_normalizer_map_subtype hg)
      exact Subgroup.mem_subgroupOf.2 ⟨hS.hN _ hΩE hΩ1 hgn, g.2⟩
  have hcop : ∀ V : Subgroup G, V ≤ Y' → (∀ y ∈ Y', ∀ v ∈ V, y * v * y⁻¹ ∈ V) →
      ¬ p ∣ Nat.card ↥V → V ≤ N := by
    intro V hVY hVn hVp
    obtain ⟨B₂', hB₂'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥B) p (n := 2) hdvd
    set B₂ : Subgroup G := B₂'.map B.subtype with hB₂
    have hB₂B : B₂ ≤ B := Subgroup.map_subtype_le _
    have hB₂c : Nat.card ↥B₂ = p ^ 2 := by
      rw [hB₂, Subgroup.card_map_of_injective B.subtype_injective, hB₂']
    have hpow : ∀ x ∈ B, x ^ p = 1 := fun x hx => by
      have := hBel
      exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := B) x hx
    have hB₂n : B₂ ≤ Subgroup.normalizer (V : Set G) := fun b hb => by
      have hbY : b ∈ Y' := hPY (hBP (hB₂B hb))
      rw [Subgroup.mem_normalizer_iff]
      intro v
      constructor
      · intro hv; exact hVn b hbY v hv
      · intro hv
        have := hVn b⁻¹ (Y'.inv_mem hbY) _ hv
        simpa [mul_assoc] using this
    have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p hp
      B₂ V (fun m => Subtype.ext (hpow m (hB₂B m.2))) hB₂c hVp hB₂n
    refine hgen.le.trans (iSup₂_le fun m hm => ?_)
    refine inf_le_right.trans ?_
    have hm1 : (m : G) ≠ 1 := fun h => hm (Subtype.ext h)
    have hzE : Subgroup.zpowers (m : G) ≤ E := Subgroup.zpowers_le.2 (hBE (hB₂B m.2))
    have hz1 : Subgroup.zpowers (m : G) ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]; exact hm1
    exact (centralizer_singleton_le_normalizer_zpowers (m : G)).trans (hS.hN _ hzE hz1)
  exact ⟨hP, hnc, hΩ, hPnorm, hcard, hPN, hspe, hcop⟩

theorem conjSub_le_normalizer {Y S : Subgroup G} (h : Y ≤ Subgroup.normalizer (S : Set G)) (n : G) :
    conjSub n Y ≤ Subgroup.normalizer ((conjSub n S : Subgroup G) : Set G) := by
  intro y hy
  rw [mem_conjSub_iff] at hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_conjSub_iff, mem_conjSub_iff]
  have h1 := (Subgroup.mem_normalizer_iff.1 (h hy) (n⁻¹ * x * n))
  have e : n⁻¹ * y * n * (n⁻¹ * x * n) * (n⁻¹ * y * n)⁻¹ = n⁻¹ * (y * x * y⁻¹) * n := by group
  have e' : n⁻¹ * x * n = n⁻¹ * x * n := rfl
  rw [e] at h1
  exact h1

theorem not_isCyclic_conjSub {B : Subgroup G} (hB : ¬ IsCyclic ↥B) (g : G) :
    ¬ IsCyclic ↥(conjSub g B) := fun h =>
  hB ((Subgroup.equivMapOfInjective B (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).isCyclic.2 h)

theorem not_isCyclic_of_conjSub_le {B K : Subgroup G} (hB : ¬ IsCyclic ↥B) {g : G}
    (h : conjSub g B ≤ K) : ¬ IsCyclic ↥K := fun _hK => by
  have : IsCyclic ↥(conjSub g B) := Subgroup.isCyclic_of_le h
  exact not_isCyclic_conjSub hB g this

theorem not_isCyclic_of_le {B K : Subgroup G} (hB : ¬ IsCyclic ↥B) (h : B ≤ K) :
    ¬ IsCyclic ↥K := fun _hK => hB (Subgroup.isCyclic_of_le h)

theorem lemmaY1_II [Finite G] {p : ℕ} {E N Y B₀ : Subgroup G} (hS : Setting p E N)
    (hY2 : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ Y ≤ Subgroup.normalizer (S : Set G))
    (hYN : ¬ Y ≤ N) (hB₀Y : B₀ ≤ Y) (hB₀E : B₀ ≤ E) (hB₀ : ¬ IsCyclic ↥B₀)
    (hcard : Nat.card ↥B₀ = p ^ 3) (hKA : KAHyp p E N B₀) :
    ∃ n ∈ N, ∃ P : Subgroup G, Y1Out p E N (conjSub n Y) P ∧ Nat.card ↥B₀ ≤ Nat.card ↥(P ⊓ E) := by
  classical
  have hp : p.Prime := hS.prime
  have : Fact p.Prime := ⟨hp⟩
  have hB₀el : IsElementaryAbelian p ↥B₀ := elemAbelian_of_le hS.Eel hB₀E
  obtain ⟨P, hP, hB₀P⟩ :=
    Sec12Fus.exists_isSylowOf_ge (p := p) hB₀Y (IsElementaryAbelian.isPGroup p ↥B₀)
  obtain ⟨S, hS1, hS2, hS3⟩ := hY2
  have hBcard : Nat.card ↥(P ⊓ E) ≤ p ^ 3 :=
    hS.rank (P ⊓ E) (elemAbelian_of_le hS.Eel inf_le_right)
      ⟨S, hS1, hS2, (inf_le_left.trans hP.1).trans hS3⟩
  have hBeq : B₀ = P ⊓ E :=
    Subgroup.eq_of_le_of_card_ge (le_inf hB₀P hB₀E) (by rw [hcard]; exact hBcard)
  have hnc : ¬ IsCyclic ↥(P ⊓ E) := by rw [← hBeq]; exact hB₀
  have hT : omegaOne p (P ⊓ Subgroup.normalizer ((P ⊓ E : Subgroup G) : Set G)) = P ⊓ E := by
    rw [← hBeq]
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      rintro y ⟨hyT, hyp⟩
      have hyc : y ∈ Subgroup.centralizer (B₀ : Set G) :=
        hKA Y P ⟨S, hS1, hS2, hS3⟩ hYN hP hBeq.symm y hyT.1 hyT.2 hyp
      have hel : IsElementaryAbelian p ↥(B₀ ⊔ Subgroup.zpowers y) := by
        have := hB₀el
        have := IsElementaryAbelian.zpowers_of_pow_eq_one hyp
        exact IsElementaryAbelian.sup_of_le_centralizer
          (Subgroup.zpowers_le.2 hyc)
      have hKP : B₀ ⊔ Subgroup.zpowers y ≤ P := sup_le hB₀P (Subgroup.zpowers_le.2 hyT.1)
      have hcardK := hS.rank _ hel ⟨S, hS1, hS2, (hKP.trans hP.1).trans hS3⟩
      have hKeq : B₀ = B₀ ⊔ Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcard]; exact hcardK)
      rw [hKeq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    · intro x hx
      refine Subgroup.subset_closure ⟨⟨hB₀P hx, Subgroup.le_normalizer hx⟩, ?_⟩
      have := hB₀el
      exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := B₀) x hx
  refine ⟨1, N.one_mem, P, ?_, hBeq ▸ le_rfl⟩
  rw [conjSub_one]
  exact y1Out_of_omega hS ⟨S, hS1, hS2, hS3⟩ hYN hP hnc hT

theorem exists_conj_omega_le [Finite G] {p : ℕ} {E P' : Subgroup G} (hp : p.Prime)
    (hEel : IsElementaryAbelian p ↥E)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    (hΩ : OmegaHyp p E) (hP'p : IsPGroup p ↥P') :
    ∃ k ∈ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G),
      ∀ x ∈ omegaOne p (P' ⊓ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G)),
        k⁻¹ * x * k ∈ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hEcomm : IsMulCommutative ↥E := hEel.toIsMulCommutative
  have hEH : E ≤ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G) :=
    le_normalizer_of_le_comm (inf_le_right : P' ⊓ E ≤ E)
  have hEQ0 : E ≤ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G) ⊓
      Subgroup.normalizer (E : Set G) := le_inf hEH Subgroup.le_normalizer
  obtain ⟨Q, hQ, hEQ⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hEQ0
    (IsElementaryAbelian.isPGroup p ↥E)
  have hQH : IsSylowOf p Q (Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G)) :=
    Sec15FA.sylow_of_torus_normalizer hJ hQ hEQ
  have hTH : P' ⊓ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G) := inf_le_right
  have hTp : IsPGroup p ↥(P' ⊓ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G)) :=
    hP'p.to_le inf_le_left
  obtain ⟨k, hkH, hk⟩ := CFSG.ComponentClassification.FooteLit.exists_conj_le_of_isSylowOf
    (p := p) (CFSG.ABGLocalTools.isSylowOf_iff.2 hQH) hTH hTp
  have hΩQ : omegaOne p Q = E := hΩ Q hEQ (hQ.1.trans inf_le_right) hQ.2.1
  refine ⟨k, hkH, fun x hx => ?_⟩
  have := conj_omegaOne_mem (p := p) hk hx
  rwa [hΩQ] at this

theorem exists_pair_max [Finite G] {p : ℕ} {E N Y B₀ : Subgroup G} (hp : p.Prime)
    (hnc : ¬ IsCyclic ↥B₀) (hB₀Y : B₀ ≤ Y) (hB₀E : B₀ ≤ E) (hB₀p : IsPGroup p ↥B₀) :
    ∃ (n : G) (P' : Subgroup G), n ∈ N ∧ IsSylowOf p P' (conjSub n Y) ∧ ¬ IsCyclic ↥(P' ⊓ E) ∧
      (∀ (n' : G) (P'' : Subgroup G), n' ∈ N → IsSylowOf p P'' (conjSub n' Y) →
        ¬ IsCyclic ↥(P'' ⊓ E) → Nat.card ↥(P'' ⊓ E) ≤ Nat.card ↥(P' ⊓ E)) ∧
      Nat.card ↥B₀ ≤ Nat.card ↥(P' ⊓ E) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let Pairs : Set (Subgroup G × Subgroup G) :=
    {x | ∃ n ∈ N, x.1 = conjSub n Y ∧ IsSylowOf p x.2 x.1 ∧ ¬ IsCyclic ↥(x.2 ⊓ E)}
  obtain ⟨P₀, hP₀, hB₀P₀⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hB₀Y hB₀p
  have hne : Pairs.Nonempty :=
    ⟨(Y, P₀), 1, N.one_mem, conjSub_one.symm, hP₀, not_isCyclic_of_le hnc (le_inf hB₀P₀ hB₀E)⟩
  obtain ⟨⟨Y', P'⟩, ⟨n, hnN, hY', hP', hnc'⟩, hmax⟩ :=
    Set.exists_max_image Pairs (fun x => Nat.card ↥(x.2 ⊓ E)) (Set.toFinite Pairs) hne
  refine ⟨n, P', hnN, hY' ▸ hP', hnc', fun n' P'' hn' hP'' hnc'' => ?_, ?_⟩
  · exact hmax (conjSub n' Y, P'') ⟨n', hn', rfl, hP'', hnc''⟩
  · have h1 : Nat.card ↥B₀ ≤ Nat.card ↥(P₀ ⊓ E) := Subgroup.card_le_of_le (le_inf hB₀P₀ hB₀E)
    exact h1.trans (hmax (Y, P₀) ⟨1, N.one_mem, conjSub_one.symm, hP₀,
      not_isCyclic_of_le hnc (le_inf hB₀P₀ hB₀E)⟩)

theorem two_local_conj [Finite G] {Y : Subgroup G}
    (hY2 : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ Y ≤ Subgroup.normalizer (S : Set G)) (n : G) :
    ∃ S' : Subgroup G, S' ≠ ⊥ ∧ IsPGroup 2 ↥S' ∧
      conjSub n Y ≤ Subgroup.normalizer (S' : Set G) := by
  obtain ⟨S, hS1, hS2, hS3⟩ := hY2
  refine ⟨conjSub n S, fun h => hS1 ?_, hS2.map _, conjSub_le_normalizer hS3 n⟩
  have h1 : Nat.card ↥(conjSub n S) = 1 := by rw [h]; exact Subgroup.card_bot
  rw [card_conjSub] at h1
  exact Subgroup.card_eq_one.1 h1

theorem le_of_conjSub_le {Y N : Subgroup G} {n : G} (hn : n ∈ N) (h : conjSub n Y ≤ N) : Y ≤ N :=
  fun y hy => by
    have h1 : n * y * n⁻¹ ∈ N := h ⟨y, hy, by simp [MulAut.conj_apply]⟩
    have h2 : n⁻¹ * (n * y * n⁻¹) * n ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hn) h1) hn
    simpa [mul_assoc] using h2

theorem lemmaY1_I [Finite G] {p : ℕ} {E N Y B₀ : Subgroup G} (hS : Setting p E N)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    (hΩ : OmegaHyp p E)
    (hY2 : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ Y ≤ Subgroup.normalizer (S : Set G))
    (hYN : ¬ Y ≤ N) (hB₀Y : B₀ ≤ Y) (hB₀E : B₀ ≤ E) (hB₀ : ¬ IsCyclic ↥B₀) :
    ∃ n ∈ N, ∃ P : Subgroup G, Y1Out p E N (conjSub n Y) P ∧
      Nat.card ↥B₀ ≤ Nat.card ↥(P ⊓ E) := by
  classical
  have hp : p.Prime := hS.prime
  have : Fact p.Prime := ⟨hp⟩
  have hB₀el : IsElementaryAbelian p ↥B₀ := elemAbelian_of_le hS.Eel hB₀E
  obtain ⟨n, P', hnN, hP', hnc', hmax, hB₀le⟩ :=
    exists_pair_max (N := N) hp hB₀ hB₀Y hB₀E (IsElementaryAbelian.isPGroup p ↥B₀)
  have hY2' := two_local_conj hY2 n
  have hYN' : ¬ conjSub n Y ≤ N := fun h => hYN (le_of_conjSub_le hnN h)
  have hBE : P' ⊓ E ≤ E := inf_le_right
  have hBP : P' ⊓ E ≤ P' := inf_le_left
  have hBel : IsElementaryAbelian p ↥(P' ⊓ E) := elemAbelian_of_le hS.Eel hBE
  have hB1 : P' ⊓ E ≠ ⊥ := fun h => hnc' (by rw [h]; infer_instance)
  have hNB : Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G) ≤ N := hS.hN _ hBE hB1
  obtain ⟨k, hkH, hFE⟩ := exists_conj_omega_le hp hS.Eel hJ hΩ hP'.2.1
  have hBF : P' ⊓ E ≤ omegaOne p (P' ⊓ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G)) :=
    fun x hx => Subgroup.subset_closure ⟨⟨hBP hx, Subgroup.le_normalizer hx⟩, by
      have := hBel
      exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := P' ⊓ E) x hx⟩
  have hkN : k ∈ N := hNB hkH
  have hP'' := isSylowOf_conjSub hP' k⁻¹
  have hY'' : conjSub k⁻¹ (conjSub n Y) = conjSub (k⁻¹ * n) Y := conjSub_mul
  have hFP : omegaOne p (P' ⊓ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G)) ≤ P' := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxT, -⟩
    exact hxT.1
  have hFle : conjSub k⁻¹
      (omegaOne p (P' ⊓ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G))) ≤
      conjSub k⁻¹ P' ⊓ E := by
    intro z hz
    have hz1 : k * z * k⁻¹ ∈ omegaOne p
        (P' ⊓ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G)) := by
      have := (mem_conjSub_iff (g := k⁻¹)).1 hz
      simpa using this
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact (mem_conjSub_iff (g := k⁻¹)).2 (by simpa using hFP hz1)
    · have := hFE _ hz1
      simpa [mul_assoc] using this
  have hnc'' : ¬ IsCyclic ↥(conjSub k⁻¹ P' ⊓ E) :=
    not_isCyclic_of_conjSub_le hnc' (g := k⁻¹) ((Subgroup.map_mono hBF).trans hFle)
  have hcard1 : Nat.card ↥(conjSub k⁻¹ P' ⊓ E) ≤ Nat.card ↥(P' ⊓ E) :=
    hmax (k⁻¹ * n) (conjSub k⁻¹ P') (N.mul_mem (N.inv_mem hkN) hnN) (hY'' ▸ hP'') hnc''
  have hcard2 : Nat.card ↥(conjSub k⁻¹
      (omegaOne p (P' ⊓ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G)))) ≤
      Nat.card ↥(conjSub k⁻¹ P' ⊓ E) := Subgroup.card_le_of_le hFle
  have hcard3 : Nat.card ↥(conjSub k⁻¹
      (omegaOne p (P' ⊓ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G)))) =
      Nat.card ↥(omegaOne p (P' ⊓ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G))) :=
    card_conjSub
  have hBeqF : P' ⊓ E =
      omegaOne p (P' ⊓ Subgroup.normalizer ((P' ⊓ E : Subgroup G) : Set G)) :=
    Subgroup.eq_of_le_of_card_ge hBF (by rw [← hcard3]; exact hcard2.trans hcard1)
  exact ⟨n, hnN, P', y1Out_of_omega hS hY2' hYN' hP' hnc' hBeqF.symm, hB₀le⟩

theorem lemmaY1 [Finite G] {p : ℕ} {E N Y B₀ : Subgroup G} (hS : Setting p E N)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    (hY2 : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ Y ≤ Subgroup.normalizer (S : Set G))
    (hYN : ¬ Y ≤ N) (hB₀Y : B₀ ≤ Y) (hB₀E : B₀ ≤ E) (hB₀ : ¬ IsCyclic ↥B₀)
    (hΩ : OmegaHyp p E ∨ (Nat.card ↥B₀ = p ^ 3 ∧ KAHyp p E N B₀)) :
    ∃ n ∈ N, ∃ P : Subgroup G, Y1Out p E N (conjSub n Y) P ∧
      Nat.card ↥B₀ ≤ Nat.card ↥(P ⊓ E) := by
  rcases hΩ with h | ⟨hc, hKA⟩
  · exact lemmaY1_I hS hJ h hY2 hYN hB₀Y hB₀E hB₀
  · exact lemmaY1_II hS hY2 hYN hB₀Y hB₀E hB₀ hc hKA

end Sec1511

end CFSG.RankThree.PartOne
