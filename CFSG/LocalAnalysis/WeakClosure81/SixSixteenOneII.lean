module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.GroupTheory.SteinbergCBFTCores
public import CFSG.LocalAnalysis.GL83PartI.Goldschmidt_2_5

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SixSixteenOneII

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_wClos_of_le {V S R L : Subgroup G} {j : ℕ} (hRS : R ≤ S)
    (hA_le_R : ∀ A ∈ E3.gammaSet V j S, A ≤ R) (hL : L ≤ normalizer (R : Set G)) :
    L ≤ normalizer (E3.wClos V j S : Set G) := by
  have heq : E3.wClos V j S = E3.wClos V j R :=
    le_antisymm (E3.wClos_le_of_forall fun A hA => E3.le_wClos ⟨hA_le_R A hA, hA.2⟩)
      (E3.wClos_mono hRS)
  rw [heq]
  exact hL.trans (E3.normalizer_le_normalizer_wClos R)

theorem conj_mem_sup_pCore_aux {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    [Fact (Nat.Prime 2)] (hp2 : p ≠ 2) (hsolv : Group.IsSolvable Y)
    (hcard : ∀ q : ℕ, q.Prime → q ∣ Nat.card Y → q = 2 ∨ q = p) (P : Sylow p Y)
    (hab : ∀ x ∈ (P : Subgroup Y), ∀ y ∈ (P : Subgroup Y), x * y = y * x) :
    ∀ g : Y, ∀ x ∈ (P : Subgroup Y), g * x * g⁻¹ ∈ (P : Subgroup Y) ⊔ CFSG.pCore 2 Y := by
  set N : Subgroup Y := CFSG.pCore 2 Y with hN
  set π : Y →* Y ⧸ N := QuotientGroup.mk' N with hπ
  have hO : CFSG.pCore 2 (Y ⧸ N) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hsolv' : Group.IsSolvable (Y ⧸ N) := inferInstance
  have hcard' : ∀ q : ℕ, q.Prime → q ∣ Nat.card (Y ⧸ N) → q = 2 ∨ q = p := fun q hq hd =>
    hcard q hq (hd.trans (Subgroup.card_quotient_dvd_card N))
  have hpp : CFSG.pPrimeCore p (Y ⧸ N) = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro K hKn hKc
    have hKn' : K.Normal := hKn
    have hpos : 0 < Nat.card K := Nat.card_pos
    have h2 : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card K → d = 2 := by
      intro d hd hdK
      rcases hcard' d hd (hdK.trans (Subgroup.card_subgroup_dvd_card K)) with h | h
      · exact h
      · exact absurd (h ▸ hdK) ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hKc)
    have hK2 : IsPGroup 2 K := by
      have := Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' h2
      exact IsPGroup.of_card this
    have : K ≤ CFSG.pCore 2 (Y ⧸ N) := le_sSup ⟨hKn', hK2⟩
    rwa [hO, le_bot_iff] at this
  have hcent : Subgroup.centralizer (CFSG.pCore p (Y ⧸ N) : Set (Y ⧸ N)) ≤
      CFSG.pCore p (Y ⧸ N) :=
    CFSG.GroupTheory.FT63ChII.centralizer_pCore_le_pCore
      (GL83.Goldschmidt.isPiSeparable_of_isSolvable _ hsolv') hpp
  set Pb : Sylow p (Y ⧸ N) := P.mapSurjective (QuotientGroup.mk'_surjective N) with hPb
  have hle : CFSG.pCore p (Y ⧸ N) ≤ (Pb : Subgroup (Y ⧸ N)) := CFSG.fitting_pCore_le_sylow Pb
  have hPbab : ∀ x ∈ (Pb : Subgroup (Y ⧸ N)), ∀ y ∈ (Pb : Subgroup (Y ⧸ N)), x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hab a ha b hb]
  have hPble : (Pb : Subgroup (Y ⧸ N)) ≤ CFSG.pCore p (Y ⧸ N) := by
    intro x hx
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hPbab z (hle hz) x hx
  have hnorm : (Pb : Subgroup (Y ⧸ N)).Normal :=
    ⟨fun n hn g => by
      have := hle ((inferInstance : (CFSG.pCore p (Y ⧸ N)).Normal).conj_mem n (hPble hn) g)
      exact this⟩
  intro g x hx
  have hmem : π (g * x * g⁻¹) ∈ (Pb : Subgroup (Y ⧸ N)) := by
    have hx' : π x ∈ (Pb : Subgroup (Y ⧸ N)) := ⟨x, hx, rfl⟩
    have := hnorm.conj_mem _ hx' (π g)
    simpa [map_mul, map_inv] using this
  obtain ⟨x', hx', hxx⟩ := hmem
  have hq : x'⁻¹ * (g * x * g⁻¹) ∈ N := by
    rw [← QuotientGroup.eq]
    exact hxx
  have : g * x * g⁻¹ = x' * (x'⁻¹ * (g * x * g⁻¹)) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hx' hq

theorem conj_le_sup_pCoreOf {X S : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXp : IsPGroup p X) (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hS2 : IsPGroup 2 S)
    (hperm : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G)) :
    ∀ g ∈ X ⊔ S, ∀ x ∈ X, g * x * g⁻¹ ∈ X ⊔ pCoreOf 2 (X ⊔ S) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := X ⊔ S with hK
  have hXK : X ≤ K := le_sup_left
  have hSK : S ≤ K := le_sup_right
  have hdisj : X ⊓ S = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne p 2 hp2 X S hXp hS2
    rwa [disjoint_iff] at hd
  have hcardNat : Nat.card K = Nat.card X * Nat.card S := by
    have hrel : S.relIndex K = Nat.card X := by
      rw [hK, CFSG.ABGTheoremB.TotallyInverted.Omnibus.relIndex_sup_of_mul_comm
        (A := X) (B := S) hperm]
      have h := Subgroup.relIndex_mul_card (H := S) (K := X)
      rw [inf_comm, hdisj, Subgroup.card_bot, mul_one] at h
      exact h
    have h := Subgroup.relIndex_mul_card (H := S) (K := K)
    rw [inf_eq_left.mpr hSK, hrel] at h
    exact h.symm
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hXp
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hS2
  have hcardK : Nat.card K = p ^ a * 2 ^ b := by rw [hcardNat, ha, hb]
  have hsolv : Group.IsSolvable ↥K := by
    haveI : Fintype ↥K := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      hp Nat.prime_two hp2 (by rw [← Nat.card_eq_fintype_card, hcardK])
  have hcard : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥K → q = 2 ∨ q = p := by
    intro q hq hd
    rw [hcardK] at hd
    rcases (Nat.Prime.dvd_mul hq).1 hd with h | h
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h))
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  have hcardX' : Nat.card (X.subgroupOf K) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
  have hfac : (Nat.card ↥K).factorization p = a := by
    rw [hcardK, Nat.factorization_mul (pow_pos hp.pos a).ne' (pow_pos Nat.two_pos b).ne']
    simp [Nat.Prime.factorization_pow hp, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_apply, Ne.symm hp2]
  let P : Sylow p ↥K := Sylow.ofCard (X.subgroupOf K) (by rw [hcardX', ha, hfac])
  have hP : (P : Subgroup ↥K) = X.subgroupOf K := rfl
  have hab : ∀ x ∈ (P : Subgroup ↥K), ∀ y ∈ (P : Subgroup ↥K), x * y = y * x := by
    intro x hx y hy
    rw [hP, Subgroup.mem_subgroupOf] at hx hy
    exact Subtype.ext (hXab _ hx _ hy)
  intro g hg x hx
  have h := conj_mem_sup_pCore_aux (p := p) hp2 hsolv hcard P hab ⟨g, hg⟩ ⟨x, hXK hx⟩
    (by rw [hP, Subgroup.mem_subgroupOf]; exact hx)
  have h2 := Subgroup.mem_map_of_mem K.subtype h
  rw [Subgroup.map_sup, hP, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXK] at h2
  exact h2

theorem le_omega1_of_mem_gammaSet {V S A : Subgroup G} (hV : IsElemAbelian 2 V) {j : ℕ}
    (hA : A ∈ E3.gammaSet V j S) : A ≤ F11.Omega1p 2 S := by
  have hAe : IsElemAbelian 2 A := (E3.isInvColl_gammaSet hV j S).isElemAbelian A hA
  exact fun a ha => Subgroup.subset_closure ⟨hA.1 ha, hAe.2 a ha⟩

theorem cyc_sq_unique {H : Type} [Group H] [Finite H] [IsCyclic H] {a b : H} (ha : a ≠ 1)
    (hb : b ≠ 1) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) : a = b := by
  by_contra hab
  classical
  have := Fintype.ofFinite H
  have h := IsCyclic.card_pow_eq_one_le (α := H) (n := 2) two_pos
  have hsub : ({1, a, b} : Finset H) ⊆ Finset.filter (fun x : H => x ^ 2 = 1) Finset.univ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [*]
  have h3 : ({1, a, b} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ha.symm, hb.symm]), Finset.card_pair hab]
  have := Finset.card_le_card hsub
  omega

theorem sq_dichotomy {S Q : Subgroup G} (hQS : Q ≤ S)
    (hQn : S ≤ normalizer (Q : Set G))
    (hcyc : ∃ a ∈ F11.Omega1p 2 S, F11.Omega1p 2 S =
      Subgroup.zpowers a ⊔ (F11.Omega1p 2 S ⊓ Q))
    {t : G} (htS : t ∈ S) (ht2 : t ^ 2 = 1) (htQ : t ∉ Q) {x : G} (hxS : x ∈ S)
    (hx2 : x ^ 2 = 1) : x ∈ Q ∨ t⁻¹ * x ∈ Q := by
  obtain ⟨a, haΩ, hΩ⟩ := hcyc
  set N : Subgroup G := normalizer (Q : Set G) with hN
  haveI : (Q.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  let f : ↥N →* (↥N ⧸ Q.subgroupOf N) := QuotientGroup.mk' (Q.subgroupOf N)
  have hΩS : F11.Omega1p 2 S ≤ S := (Subgroup.closure_le _).2 (fun y hy => hy.1)
  have hSN : ∀ y ∈ S, y ∈ N := fun y hy => hQn hy
  let c : ↥N ⧸ Q.subgroupOf N := f ⟨a, hSN a (hΩS haΩ)⟩
  have hker : ∀ y : ↥N, f y = 1 ↔ (y : G) ∈ Q := fun y => by
    simp only [f, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  set L : Subgroup G := Subgroup.map N.subtype ((Subgroup.zpowers c).comap f) with hL
  have hΩL : F11.Omega1p 2 S ≤ L := by
    rw [hΩ]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨a, hSN a (hΩS haΩ)⟩, ?_, rfl⟩
      exact Subgroup.mem_zpowers c
    · intro m hm
      refine ⟨⟨m, hSN m (hQS hm.2)⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, (hker _).2 hm.2]
      exact one_mem _
  have hmemL : ∀ y ∈ S, y ^ 2 = 1 → ∃ h : ↥N, (h : G) = y ∧ f h ∈ Subgroup.zpowers c := by
    intro y hy hy2
    have : y ∈ F11.Omega1p 2 S := Subgroup.subset_closure ⟨hy, hy2⟩
    obtain ⟨h, hh, rfl⟩ := hΩL this
    exact ⟨h, rfl, hh⟩
  obtain ⟨ht, htN, htc⟩ := hmemL t htS ht2
  obtain ⟨hx, hxN, hxc⟩ := hmemL x hxS hx2
  haveI : IsCyclic (Subgroup.zpowers c) := inferInstance
  have ht1 : f ht ≠ 1 := fun h => htQ (by rw [← htN]; exact (hker _).1 h)
  have hsq : ∀ y : ↥N, (y : G) ^ 2 = 1 → f y ^ 2 = 1 := fun y hy => by
    rw [← map_pow]
    have : y ^ 2 = 1 := Subtype.ext (by simpa using hy)
    rw [this, map_one]
  by_cases hx1 : f hx = 1
  · left
    rw [← hxN]; exact (hker _).1 hx1
  · right
    have key : (⟨f hx, hxc⟩ : Subgroup.zpowers c) = ⟨f ht, htc⟩ := by
      refine cyc_sq_unique ?_ ?_ ?_ ?_
      · intro h; exact hx1 (congrArg Subtype.val h)
      · intro h; exact ht1 (congrArg Subtype.val h)
      · exact Subtype.ext (hsq hx (by rw [hxN]; exact hx2))
      · exact Subtype.ext (hsq ht (by rw [htN]; exact ht2))
    have key' : f hx = f ht := congrArg Subtype.val key
    have : f (ht⁻¹ * hx) = 1 := by rw [map_mul, map_inv, key', inv_mul_cancel]
    have h2 := (hker _).1 this
    simpa [hxN, htN] using h2

theorem omega1_le_sup_of_cyclic {S Q : Subgroup G} (hQS : Q ≤ S)
    (hQn : S ≤ normalizer (Q : Set G))
    (hcyc : ∃ a ∈ F11.Omega1p 2 S, F11.Omega1p 2 S =
      Subgroup.zpowers a ⊔ (F11.Omega1p 2 S ⊓ Q))
    {t : G} (htS : t ∈ S) (ht2 : t ^ 2 = 1) (htQ : t ∉ Q) :
    F11.Omega1p 2 S ≤ zpowers t ⊔ Q ∧ ∀ s ∈ S, s * t * s⁻¹ * t⁻¹ ∈ Q := by
  have hd := fun {x : G} (hxS : x ∈ S) (hx2 : x ^ 2 = 1) =>
    sq_dichotomy hQS hQn hcyc htS ht2 htQ hxS hx2
  have htn : ∀ q, q ∈ Q ↔ t * q * t⁻¹ ∈ Q := fun q => (mem_normalizer_iff.1 (hQn htS)) q
  refine ⟨?_, ?_⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxS, hx2⟩
    rcases hd hxS hx2 with h | h
    · exact Subgroup.mem_sup_right h
    · have : x = t * (t⁻¹ * x) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)) (Subgroup.mem_sup_right h)
  · intro s hs
    have hsS : s * t * s⁻¹ ∈ S := mul_mem (mul_mem hs htS) (inv_mem hs)
    have hsq : (s * t * s⁻¹) ^ 2 = 1 := by
      have : (s * t * s⁻¹) ^ 2 = s * t ^ 2 * s⁻¹ := by simp [pow_two, mul_assoc]
      rw [this, ht2]; simp
    rcases hd hsS hsq with h | h
    · exfalso
      apply htQ
      have := (mem_normalizer_iff.1 (hQn (inv_mem hs))) (s * t * s⁻¹)
      have h' := this.1 h
      simpa [mul_assoc] using h'
    · have h' := (htn _).1 h
      have : t * (t⁻¹ * (s * t * s⁻¹)) * t⁻¹ = s * t * s⁻¹ * t⁻¹ := by group
      rwa [this] at h'

theorem exists_X0 {X Q : Subgroup G} {t : G}
    (hQ : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) :
    ∃ X₀ : Subgroup G, ∀ x, x ∈ X₀ ↔ x ∈ X ∧ t * x * t⁻¹ * x⁻¹ ∈ Q := by
  refine ⟨{ carrier := ({x | x ∈ X ∧ t * x * t⁻¹ * x⁻¹ ∈ Q} : Set G),
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨X.mul_mem hx hy, ?_⟩
    have : t * (x * y) * t⁻¹ * (x * y)⁻¹ =
        (t * x * t⁻¹ * x⁻¹) * (x * (t * y * t⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [this]; exact Q.mul_mem hx' (hQ x hx _ hy')
  · exact ⟨X.one_mem, by simpa using Q.one_mem⟩
  · rintro x ⟨hx, hx'⟩
    refine ⟨X.inv_mem hx, ?_⟩
    have : t * x⁻¹ * t⁻¹ * x⁻¹⁻¹ = x⁻¹ * (t * x * t⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [this]; exact hQ _ (X.inv_mem hx) _ (Q.inv_mem hx')

theorem exists_Y {X Q : Subgroup G} {t : G}
    (hQ : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    ∃ Y : Subgroup G, ∀ x, x ∈ Y ↔ x ∈ X ∧ t * x * t⁻¹ * x ∈ Q := by
  refine ⟨{ carrier := ({x | x ∈ X ∧ t * x * t⁻¹ * x ∈ Q} : Set G),
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨X.mul_mem hx hy, ?_⟩
    have hc : x⁻¹ * y⁻¹ * x * y = 1 := by
      rw [show x⁻¹ * y⁻¹ * x * y = (y * x)⁻¹ * (x * y) by group, hXab x hx y hy]; simp
    have : t * (x * y) * t⁻¹ * (x * y) =
        (t * x * t⁻¹ * x) * (x⁻¹ * (t * y * t⁻¹ * y) * x) * (x⁻¹ * y⁻¹ * x * y) := by group
    rw [this, hc, mul_one]
    have h3 := hQ x⁻¹ (X.inv_mem hx) _ hy'
    rw [inv_inv] at h3
    exact Q.mul_mem hx' h3
  · exact ⟨X.one_mem, by simpa using Q.one_mem⟩
  · rintro x ⟨hx, hx'⟩
    refine ⟨X.inv_mem hx, ?_⟩
    have : t * x⁻¹ * t⁻¹ * x⁻¹ = x * (t * x * t⁻¹ * x)⁻¹ * x⁻¹ := by group
    rw [this]; exact hQ _ hx _ (Q.inv_mem hx')

theorem mem_normalizer_of_conj {R : Subgroup G} {g : G}
    (h1 : ∀ h ∈ R, g * h * g⁻¹ ∈ R) (h2 : ∀ h ∈ R, g⁻¹ * h * g ∈ R) :
    g ∈ normalizer (R : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨h1 h, fun hh => ?_⟩
  have := h2 _ hh
  simpa [mul_assoc] using this

theorem conj_mem_sup {Q : Subgroup G} {t g : G} (hQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (ht : g * t * g⁻¹ ∈ zpowers t ⊔ Q) : ∀ h ∈ zpowers t ⊔ Q, g * h * g⁻¹ ∈ zpowers t ⊔ Q := by
  have : zpowers t ⊔ Q ≤ (zpowers t ⊔ Q).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]; simpa using ht
    · intro q hq
      exact Subgroup.mem_comap.mpr (le_sup_right (a := zpowers t) (by simpa using hQ q hq))
  intro h hh
  simpa using this hh

theorem exists_split {X S : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hexp : ∀ x ∈ X, x ^ p = 1) (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hS2 : IsPGroup 2 S)
    (hperm : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G))
    (hnorm : ∀ g ∈ X ⊔ S, ∀ x ∈ X, g * x * g⁻¹ ∈ X ⊔ pCoreOf 2 (X ⊔ S))
    {t : G} (htS : t ∈ S) (ht2 : t ^ 2 = 1) (htQ : t ∉ pCoreOf 2 (X ⊔ S))
    (hcent : ∀ s ∈ S, s * t * s⁻¹ * t⁻¹ ∈ pCoreOf 2 (X ⊔ S)) :
    ∃ X₀ Y : Subgroup G, X₀ ≤ X ∧ Y ≤ X ∧ (∀ x ∈ X, ∃ a ∈ X₀, ∃ b ∈ Y, x = a * b) ∧
      Y ≠ ⊥ ∧ X₀ ≤ normalizer ((zpowers t ⊔ pCoreOf 2 (X ⊔ S) : Subgroup G) : Set G) ∧
      (Y : Set G) * (S : Set G) = (S : Set G) * (Y : Set G) ∧
      (∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y ⊔ pCoreOf 2 (X ⊔ S)) ∧
      ∀ y ∈ Y, t * y * t⁻¹ * y ∈ pCoreOf 2 (X ⊔ S) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hXp : IsPGroup p X := isPGroup_of_pow_eq_one hexp
  have hSyl : IsSylowIn 2 S (X ⊔ S) := isSylowIn_sup_of_mul_comm hp hp2 hXp hS2 hperm
  have hQS : pCoreOf 2 (X ⊔ S) ≤ S := E1.pCoreOf_two_le_of_isSylowIn hSyl
  have hQK : pCoreOf 2 (X ⊔ S) ≤ X ⊔ S := CFSG.LieType.BorelTits.pCoreOf_le 2 (X ⊔ S)
  have hKQ : X ⊔ S ≤ normalizer (pCoreOf 2 (X ⊔ S) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ S)
  generalize hQdef : pCoreOf 2 (X ⊔ S) = Q at *
  have hXK : X ≤ X ⊔ S := le_sup_left
  have hSK : S ≤ X ⊔ S := le_sup_right
  have htK : t ∈ X ⊔ S := hSK htS
  have hconj : ∀ g ∈ X ⊔ S, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hKQ hg) q).mp hq
  have hconj' : ∀ g ∈ X ⊔ S, ∀ q ∈ Q, g⁻¹ * q * g ∈ Q := fun g hg q hq => by
    simpa using hconj g⁻¹ (inv_mem hg) q hq
  have hXQcoe : ((X ⊔ Q : Subgroup G) : Set G) = (X : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X Q (hXK.trans hKQ)
  have hXQmem : ∀ k ∈ X ⊔ Q, ∃ x' ∈ X, ∃ q ∈ Q, k = x' * q := fun k hk => by
    rw [← SetLike.mem_coe, hXQcoe] at hk
    obtain ⟨x', hx', q, hq, rfl⟩ := hk
    exact ⟨x', hx', q, hq, rfl⟩
  have hinv : ∀ b : G, t * (t * b * t⁻¹) * t⁻¹ = b := fun b => by
    have : t * (t * b * t⁻¹) * t⁻¹ = (t * t) * b * (t * t)⁻¹ := by simp [mul_assoc]
    rw [this, ← pow_two, ht2]; simp
  obtain ⟨X₀, hX₀⟩ := exists_X0 (X := X) (Q := Q) (t := t)
    (fun g hg q hq => hconj g (hXK hg) q hq)
  obtain ⟨Y, hY⟩ := exists_Y (X := X) (Q := Q) (t := t)
    (fun g hg q hq => hconj g (hXK hg) q hq) hXab
  have hX₀X : X₀ ≤ X := fun x hx => ((hX₀ x).1 hx).1
  have hYX : Y ≤ X := fun x hx => ((hY x).1 hx).1
  have hsplit : ∀ x ∈ X, ∃ a ∈ X₀, ∃ b ∈ Y, x = a * b := by
    intro x hx
    obtain ⟨x', hx', q1, hq1, h1⟩ := hXQmem _ (hnorm t htK x hx)
    have e1 : x' = t * x * t⁻¹ * q1⁻¹ := by rw [h1]; group
    have h2 : t * x' * t⁻¹ = x * (t * q1⁻¹ * t⁻¹) := by
      rw [e1]
      calc t * (t * x * t⁻¹ * q1⁻¹) * t⁻¹
          = (t * (t * x * t⁻¹) * t⁻¹) * (t * q1⁻¹ * t⁻¹) := by group
        _ = x * (t * q1⁻¹ * t⁻¹) := by rw [hinv]
    obtain ⟨q2, hq2, h2'⟩ : ∃ q2 ∈ Q, t * x' * t⁻¹ = x * q2 :=
      ⟨_, hconj t htK _ (Q.inv_mem hq1), h2⟩
    have hxK : x ∈ X ⊔ S := hXK hx
    have hx'K : x' ∈ X ⊔ S := hXK hx'
    have hc : x * x' = x' * x := hXab x hx x' hx'
    have hz : x * x' ∈ X₀ := by
      refine (hX₀ _).2 ⟨X.mul_mem hx hx', ?_⟩
      have : t * (x * x') * t⁻¹ * (x * x')⁻¹ = (x * x') * ((x⁻¹ * q1 * x) * q2) * (x * x')⁻¹ := by
        calc t * (x * x') * t⁻¹ * (x * x')⁻¹
            = (t * x * t⁻¹) * (t * x' * t⁻¹) * (x * x')⁻¹ := by group
          _ = (x' * q1) * (x * q2) * (x * x')⁻¹ := by rw [h1, h2']
          _ = (x' * x) * ((x⁻¹ * q1 * x) * q2) * (x * x')⁻¹ := by group
          _ = _ := by rw [← hc]
      rw [this]
      exact hconj _ (Subgroup.mul_mem _ hxK hx'K) _ (Q.mul_mem (hconj' x hxK q1 hq1) hq2)
    have hu : x * x'⁻¹ ∈ Y := by
      refine (hY _).2 ⟨X.mul_mem hx (X.inv_mem hx'), ?_⟩
      have : t * (x * x'⁻¹) * t⁻¹ * (x * x'⁻¹) = x' * (q1 * q2⁻¹) * x'⁻¹ := by
        calc t * (x * x'⁻¹) * t⁻¹ * (x * x'⁻¹)
            = (t * x * t⁻¹) * (t * x' * t⁻¹)⁻¹ * (x * x'⁻¹) := by group
          _ = (x' * q1) * (x * q2)⁻¹ * (x * x'⁻¹) := by rw [h1, h2']
          _ = x' * (q1 * q2⁻¹) * x'⁻¹ := by group
      rw [this]
      exact hconj _ hx'K _ (Q.mul_mem hq1 (Q.inv_mem hq2))
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    refine ⟨(x * x') ^ (k + 1), X₀.pow_mem hz _, (x * x'⁻¹) ^ (k + 1), Y.pow_mem hu _, ?_⟩
    have hcomm : (x * x') * (x * x'⁻¹) = (x * x'⁻¹) * (x * x') :=
      hXab _ (X.mul_mem hx hx') _ (X.mul_mem hx (X.inv_mem hx'))
    rw [← Commute.mul_pow hcomm]
    have hzu : x * x' * (x * x'⁻¹) = x * x := by
      rw [show x * x' * (x * x'⁻¹) = x * (x' * x) * x'⁻¹ by group, ← hc]; group
    rw [hzu, ← pow_two, ← pow_mul]
    have : 2 * (k + 1) = p + 1 := by omega
    rw [this, pow_succ, hexp x hx, one_mul]
  have hRN : ∀ g ∈ X ⊔ S, g * t * g⁻¹ ∈ zpowers t ⊔ Q → g⁻¹ * t * g ∈ zpowers t ⊔ Q →
      g ∈ normalizer ((zpowers t ⊔ Q : Subgroup G) : Set G) := by
    intro g hg h1 h2
    refine mem_normalizer_of_conj (conj_mem_sup (fun q hq => hconj g hg q hq) h1) ?_
    intro h hh
    have := conj_mem_sup (Q := Q) (t := t) (g := g⁻¹)
      (fun q hq => by rw [inv_inv]; exact hconj' g hg q hq) (by rw [inv_inv]; exact h2) h hh
    rwa [inv_inv] at this
  have hR1 : ∀ x ∈ X₀, x * t * x⁻¹ ∈ zpowers t ⊔ Q := by
    intro x hx
    obtain ⟨hxX, hx1⟩ := (hX₀ x).1 hx
    obtain ⟨-, hx2⟩ := (hX₀ x⁻¹).1 (X₀.inv_mem hx)
    have hxK := hXK hxX
    have h3 : x * t * x⁻¹ * t⁻¹ ∈ Q := by
      have := hconj x hxK _ hx2
      have e : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹ * x⁻¹⁻¹) * x⁻¹ := by group
      rw [e]; exact this
    have e : x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h3) (Subgroup.mem_sup_left (mem_zpowers t))
  have hX₀N : ∀ x ∈ X₀, x ∈ normalizer ((zpowers t ⊔ Q : Subgroup G) : Set G) := by
    intro x hx
    refine hRN x (hXK (hX₀X hx)) (hR1 x hx) ?_
    have := hR1 x⁻¹ (X₀.inv_mem hx)
    rwa [inv_inv] at this
  have hYS : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y ⊔ Q := by
    intro s hs y hy
    obtain ⟨hyX, hy1⟩ := (hY y).1 hy
    have hsK := hSK hs
    obtain ⟨y', hy', q, hq, hk⟩ := hXQmem _ (hnorm s hsK y hyX)
    have hkK : s * y * s⁻¹ ∈ X ⊔ S :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hsK (hXK hyX)) (inv_mem hsK)
    have hc2 : t * s * t⁻¹ * s⁻¹ ∈ Q := by
      have e : t * s * t⁻¹ * s⁻¹ = (s * t * s⁻¹ * t⁻¹)⁻¹ := by group
      rw [e]; exact Q.inv_mem (hcent s hs)
    have hm : t * (s * y * s⁻¹) * t⁻¹ * (s * y * s⁻¹) ∈ Q := by
      have e : t * (s * y * s⁻¹) * t⁻¹ * (s * y * s⁻¹) =
          (t * s * t⁻¹ * s⁻¹) * (s * (t * y * t⁻¹ * y) * s⁻¹) *
            ((s * y * s⁻¹)⁻¹ * (t * s * t⁻¹ * s⁻¹)⁻¹ * (s * y * s⁻¹)) := by group
      rw [e]
      exact Q.mul_mem (Q.mul_mem hc2 (hconj s hsK _ hy1)) (hconj' _ hkK _ (Q.inv_mem hc2))
    have hy'e : y' = (s * y * s⁻¹) * q⁻¹ := by rw [hk]; group
    have hy'Y : y' ∈ Y := by
      refine (hY y').2 ⟨hy', ?_⟩
      rw [hy'e]
      have e : ∀ k : G, t * (k * q⁻¹) * t⁻¹ * (k * q⁻¹) =
          (t * k * t⁻¹ * k) * (k⁻¹ * (t * q⁻¹ * t⁻¹) * k) * q⁻¹ := fun k => by group
      rw [e]
      exact Q.mul_mem (Q.mul_mem hm (hconj' _ hkK _ (hconj t htK _ (Q.inv_mem hq))))
        (Q.inv_mem hq)
    rw [hk]
    exact Subgroup.mul_mem_sup hy'Y hq
  have hYQcoe : ((Y ⊔ Q : Subgroup G) : Set G) = (Y : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Y Q ((hYX.trans hXK).trans hKQ)
  have hYQmem : ∀ k ∈ Y ⊔ Q, ∃ y' ∈ Y, ∃ q ∈ Q, k = y' * q := fun k hk => by
    rw [← SetLike.mem_coe, hYQcoe] at hk
    obtain ⟨y', hy', q, hq, rfl⟩ := hk
    exact ⟨y', hy', q, hq, rfl⟩
  have hYSset : (Y : Set G) * (S : Set G) = (S : Set G) * (Y : Set G) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, s, hs, rfl⟩
      obtain ⟨y', hy', q, hq, hk⟩ := hYQmem _ (hYS s⁻¹ (S.inv_mem hs) y hy)
      have hye : y = s * (y' * q) * s⁻¹ := by rw [← hk]; group
      refine ⟨s * (y' * q * y'⁻¹), S.mul_mem hs
        (hQS (hconj y' (hXK (hYX hy')) q hq)), y', hy', ?_⟩
      show s * (y' * q * y'⁻¹) * y' = y * s
      rw [hye]; group
    · rintro _ ⟨s, hs, y, hy, rfl⟩
      obtain ⟨y', hy', q, hq, hk⟩ := hYQmem _ (hYS s hs y hy)
      refine ⟨y', hy', q * s, S.mul_mem (hQS hq) hs, ?_⟩
      show y' * (q * s) = s * y
      have : y' * (q * s) = (y' * q) * s := by group
      rw [this, ← hk]; group
  have hYne : Y ≠ ⊥ := by
    intro hYbot
    have hYone : ∀ y ∈ Y, y = 1 := fun y hy => by rw [hYbot] at hy; simpa using hy
    have hXX₀ : ∀ x ∈ X, x ∈ X₀ := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hsplit x hx
      rw [hYone b hb, mul_one]; exact ha
    have hRS : zpowers t ⊔ Q ≤ S := sup_le (by rw [zpowers_le]; exact htS) hQS
    have key : ∀ s ∈ S, s * t * s⁻¹ ∈ zpowers t ⊔ Q := by
      intro s hs
      have e : s * t * s⁻¹ = (s * t * s⁻¹ * t⁻¹) * t := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcent s hs)) (Subgroup.mem_sup_left (mem_zpowers t))
    have hSN : ∀ s ∈ S, s ∈ normalizer ((zpowers t ⊔ Q : Subgroup G) : Set G) := by
      intro s hs
      refine hRN s (hSK hs) (key s hs) ?_
      have := key s⁻¹ (S.inv_mem hs)
      rwa [inv_inv] at this
    have hRK : X ⊔ S ≤ normalizer ((zpowers t ⊔ Q : Subgroup G) : Set G) :=
      sup_le (fun x hx => hX₀N x (hXX₀ x hx)) hSN
    have hRp : IsPGroup 2 (zpowers t ⊔ Q : Subgroup G) := hS2.to_le hRS
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hRS.trans hSK) hRK hRp
    rw [hQdef] at hle
    exact htQ (hle (Subgroup.mem_sup_left (mem_zpowers t)))
  refine ⟨X₀, Y, hX₀X, hYX, hsplit, hYne, fun x hx => hX₀N x hx, ?_, hYS, ?_⟩
  · exact hYSset
  · intro y hy
    exact ((hY y).1 hy).2

theorem le_twoResidual_of_isPGroup {Y H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hYp : IsPGroup p Y) (hYH : Y ≤ H) : Y ≤ twoResidual H := by
  intro y hy
  rw [CFSG.Quasithin.mem_twoResidual_iff]
  intro N _ _ h2
  obtain ⟨k, hk⟩ := h2 y (hYH hy)
  obtain ⟨m, hm⟩ := hYp ⟨y, hy⟩
  have hdvd : orderOf y ∣ p ^ m := by
    apply orderOf_dvd_of_pow_eq_one
    simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime (2 ^ k) (orderOf y) :=
    Nat.Coprime.coprime_dvd_right hdvd
      (Nat.Coprime.pow k m ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hn]
  exact N.pow_mem hk n

theorem isE_one_sup {X S Y A : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXp : IsPGroup p X) (hS2 : IsPGroup 2 S)
    (hperm : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G))
    (hYX : Y ≤ X) (hY : Y ≠ ⊥) (hYperm : (Y : Set G) * (S : Set G) = (S : Set G) * (Y : Set G))
    (hYn : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y ⊔ pCoreOf 2 (X ⊔ S))
    (hAS : A ≤ S) {t : G} (htA : t ∈ A) (ht2 : t ^ 2 = 1)
    (hAt : A ≤ zpowers t ⊔ pCoreOf 2 (X ⊔ S))
    (hinv : ∀ y ∈ Y, t * y * t⁻¹ * y ∈ pCoreOf 2 (X ⊔ S)) :
    E1.IsE 1 (X ⊔ S) S A (Y ⊔ S) := by
  have hp' : Odd p := hp.odd_of_ne_two hp2
  have hYp : IsPGroup p Y := hXp.to_le hYX
  have hSK : S ≤ X ⊔ S := le_sup_right
  have hYK : Y ≤ X ⊔ S := hYX.trans le_sup_left
  have hSylK : IsSylowIn 2 S (X ⊔ S) := isSylowIn_sup_of_mul_comm hp hp2 hXp hS2 hperm
  have hSylJ : IsSylowIn 2 S (Y ⊔ S) := isSylowIn_sup_of_mul_comm hp hp2 hYp hS2 hYperm
  have hJK : Y ⊔ S ≤ X ⊔ S := sup_le hYK hSK
  have hSJ : S ≤ Y ⊔ S := le_sup_right
  have hYJ : Y ≤ Y ⊔ S := le_sup_left
  set Q := pCoreOf 2 (X ⊔ S) with hQ
  set D := pCoreOf 2 (Y ⊔ S) with hD
  have hQN : X ⊔ S ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQS : Q ≤ S := E1.pCoreOf_two_le_of_isSylowIn hSylK
  have hDN : Y ⊔ S ≤ Subgroup.normalizer (D : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hD2 : IsPGroup 2 D := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hDJ : D ≤ Y ⊔ S := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hQD : Q ≤ D :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQS.trans hSJ) (hJK.trans hQN) hQ2
  have hYD : Y ⊓ D = ⊥ := E1.inf_eq_bot_of_isPGroup hp hp2 hYp hD2
  have hYND : Y ≤ Subgroup.normalizer (D : Set G) := hYJ.trans hDN
  have hQconj : ∀ g ∈ X ⊔ S, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hQN hg) q).mp hq
  have hDconj : ∀ g ∈ Y ⊔ S, ∀ q ∈ D, g * q * g⁻¹ ∈ D := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hDN hg) q).mp hq
  have hsq : ∀ y ∈ Y, ∃ j : ℕ, (y ^ j) ^ 2 = y := by
    intro y hy
    obtain ⟨k, hk⟩ := hYp ⟨y, hy⟩
    have hk' : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨m, hm⟩ := hp'.pow (n := k)
    refine ⟨m + 1, ?_⟩
    rw [← pow_mul, show (m + 1) * 2 = p ^ k + 1 by omega, pow_succ, hk', one_mul]
  set R := Y ⊔ D with hR
  have hRJ : R ≤ Y ⊔ S := sup_le hYJ hDJ
  have hYR : Y ≤ R := le_sup_left
  have hDR : D ≤ R := le_sup_right
  have hSR : S ≤ Subgroup.normalizer (R : Set G) := by
    intro s hs
    apply E1.mem_normalizer_of_conj_mem
    intro x hx
    have hsJ : s ∈ Y ⊔ S := hSJ hs
    have hmap : (R.map (MulAut.conj s).toMonoidHom) ≤ R := by
      rw [hR, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        have h1 := hYn s hs y hy
        have h2 : Y ⊔ Q ≤ R := sup_le hYR (hQD.trans hDR)
        exact h2 h1
      · rintro _ ⟨d, hd, rfl⟩
        exact hDR (hDconj s hsJ d hd)
    have := hmap (Subgroup.mem_map_of_mem _ hx)
    simpa [MulAut.conj_apply] using this
  have hJR : Y ⊔ S ≤ Subgroup.normalizer (R : Set G) :=
    sup_le (hYR.trans Subgroup.le_normalizer) hSR
  have ht : t ∈ Y ⊔ S := hSJ (hAS htA)
  have htK : t ∈ X ⊔ S := hSK (hAS htA)
  have htD : t ∉ D := by
    intro htD
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hY
    apply hy1
    have hyJ : y ∈ Y ⊔ S := hYJ hy
    have h1 : t * (y * t⁻¹ * y⁻¹) ∈ D := by
      have := hDconj y hyJ t⁻¹ (D.inv_mem htD)
      exact D.mul_mem htD this
    have h2 : t * y * t⁻¹ * y ∈ D := hQD (hinv y hy)
    have h3 : y ^ 2 ∈ D := by
      have := D.mul_mem (D.inv_mem h1) h2
      have e : (t * (y * t⁻¹ * y⁻¹))⁻¹ * (t * y * t⁻¹ * y) = y ^ 2 := by simp only [sq]; group
      rwa [e] at this
    obtain ⟨j, hj⟩ := hsq y hy
    have h4 : y ∈ D := by
      rw [← hj, ← pow_mul, mul_comm, pow_mul]
      exact D.pow_mem h3 j
    have h5 : y ∈ Y ⊓ D := ⟨hy, h4⟩
    rw [hYD, Subgroup.mem_bot] at h5
    exact Subtype.ext h5
  have htK' : zpowers t ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr (hQN htK)
  have hrel : D.relIndex A = 2 := by
    have hle2 : D.relIndex A ≤ 2 := by
      have hsurj : Function.Surjective
          (fun b : Bool => if b then (((⟨t, htA⟩ : A) : A) : A ⧸ D.subgroupOf A) else (((1 : A) : A) : A ⧸ D.subgroupOf A)) := by
        intro x
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        have ha : (a : G) ∈ zpowers t ⊔ Q := hAt a.2
        rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ htK'] at ha
        obtain ⟨z, hz, q, hq, hzq⟩ := ha
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq]; exact ht2
        have hi : t ^ i = 1 ∨ t ^ i = t := by
          obtain ⟨m, hm⟩ : ∃ m : ℤ, i = 2 * m ∨ i = 2 * m + 1 := ⟨i / 2, by omega⟩
          rcases hm with rfl | rfl
          · left; rw [zpow_mul, h2, one_zpow]
          · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
        rcases hi with hi | hi
        · refine ⟨false, ?_⟩
          simp only [Bool.false_eq_true, if_false]
          symm
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          rw [hi] at hzq
          have hzq' : q = (a : G) := by simpa using hzq
          show ((a⁻¹ * 1 : A) : G) ∈ D
          simp only [mul_one, Subgroup.coe_inv]
          rw [← hzq']
          exact D.inv_mem (hQD hq)
        · refine ⟨true, ?_⟩
          simp only [if_true]
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          rw [hi] at hzq
          show (((⟨t, htA⟩ : A)⁻¹ * a : A) : G) ∈ D
          have hzq' : t * q = (a : G) := by simpa using hzq
          have : (((⟨t, htA⟩ : A)⁻¹ * a : A) : G) = q := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hzq']
            group
          rw [this]
          exact hQD hq
      have := Nat.card_le_card_of_surjective _ hsurj
      have e : D.relIndex A = Nat.card (A ⧸ D.subgroupOf A) := rfl
      rw [e]
      simpa using this
    have hne1 : D.relIndex A ≠ 1 := fun h =>
      htD (Subgroup.relIndex_eq_one.mp h htA)
    have hne0 : D.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hEamb : E1.EOneAmb (Y ⊔ S) A := by
    refine ⟨p, hp, hp2, R, hRJ, hJR, hDR, ?_, ?_, ?_, ?_, hrel⟩
    · intro x hx
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hYND] at hx
      obtain ⟨v, hv, n, hn, rfl⟩ := hx
      obtain ⟨k, hk⟩ := hYp ⟨v, hv⟩
      have hvk : v ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨n', hn', hvn⟩ := E1.mul_pow_eq_of_mem_normalizer (O := D) (hYND hv) hn (p ^ k)
      refine ⟨k, ?_⟩
      rw [hvn, hvk, one_mul]
      exact hn'
    · intro s hs
      have hs' : s ∈ R ⊔ S := (sup_le_sup_right hYR S) hs
      exact E1.exists_pow_mem_of_mem_sup hS2 hSR hs'
    · intro h
      apply hY
      have : Y ≤ D := hYR.trans h.le
      rw [← hYD]
      exact (inf_eq_left.mpr this).symm
    · refine sup_le ?_ le_sup_right
      intro y hy
      obtain ⟨j, hj⟩ := hsq y hy
      set y' := y ^ j with hy'
      have hy'Y : y' ∈ Y := Y.pow_mem hy j
      have hy'K : y' ∈ X ⊔ S := hYK hy'Y
      have hq : t * y'⁻¹ * t⁻¹ * y'⁻¹ ∈ Q := by
        simpa using hinv y'⁻¹ (Y.inv_mem hy'Y)
      have hq' : y'⁻¹ * (t * y'⁻¹ * t⁻¹ * y'⁻¹)⁻¹ * y' ∈ Q := by
        have := hQconj y'⁻¹ (Subgroup.inv_mem _ hy'K) _ (Q.inv_mem hq)
        simpa using this
      have e : y = ⁅y', t⁆ * (y'⁻¹ * (t * y'⁻¹ * t⁻¹ * y'⁻¹)⁻¹ * y') := by
        rw [← hj]
        simp only [commutatorElement_def, sq]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left
        (Subgroup.commutator_mem_commutator (hYR hy'Y) htA)) (Subgroup.mem_sup_right (hQD hq'))
  have hAJ : A ≤ Y ⊔ S := hAS.trans hSJ
  have hE := E1.eOne_of_eOneAmb hAJ hEamb
  refine ⟨hJK, fun x hx => Subgroup.mem_inf.mpr ⟨E1.tauOf_le _ _ _ hx,
    hSJ (E1.tauOf_le _ _ _ hx)⟩, ?_, Or.inl ⟨hE, ?_⟩⟩
  · rw [inf_eq_left.mpr hSJ]
    exact hSylJ
  · obtain ⟨-, -, -, -, -, -, h⟩ := hE
    rw [h]
    norm_num

theorem six_sixteen_ii_key {V S X : Subgroup G} (hV : IsElemAbelian 2 V) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ x ∈ X, x ^ p = 1)
    (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hS2 : IsPGroup 2 S)
    (hperm : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G))
    (hcyc : ∃ a ∈ F11.Omega1p 2 S, F11.Omega1p 2 S =
      Subgroup.zpowers a ⊔ (F11.Omega1p 2 S ⊓ pCoreOf 2 (X ⊔ S)))
    {i : ℕ} (hi : i + 1 < E3.sParam hV) :
    X ≤ normalizer (E3.wClos V i S : Set G) ∨
      X ≤ normalizer (centerOf (E3.wClos V (i + 1) S) : Set G) := by
  have hXp : IsPGroup p X := isPGroup_of_pow_eq_one hexp
  have hSK : IsSylowIn 2 S (X ⊔ S) := isSylowIn_sup_of_mul_comm hp hp2 hXp hS2 hperm
  have hQS : pCoreOf 2 (X ⊔ S) ≤ S := E1.pCoreOf_two_le_of_isSylowIn hSK
  have hQn : X ⊔ S ≤ normalizer (pCoreOf 2 (X ⊔ S) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ S)
  by_cases hcase : ∀ A ∈ E3.gammaSet V i S, A ≤ pCoreOf 2 (X ⊔ S)
  · exact Or.inl (le_normalizer_wClos_of_le hQS hcase (le_sup_left.trans hQn))
  right
  push Not at hcase
  obtain ⟨A, hA, hAQ⟩ := hcase
  obtain ⟨t, htA, htQ⟩ := SetLike.not_le_iff_exists.mp hAQ
  have htS : t ∈ S := hA.1 htA
  have ht2 : t ^ 2 = 1 := ((E3.isInvColl_gammaSet hV i S).isElemAbelian A hA).2 t htA
  obtain ⟨hΩ, hcent⟩ := omega1_le_sup_of_cyclic hQS (le_sup_right.trans hQn) hcyc htS ht2 htQ
  have hnorm := conj_le_sup_pCoreOf hp hp2 hXp hXab hS2 hperm
  obtain ⟨X₀, Y, hX₀X, hYX, hsplit, hY, hX₀N, hYperm, hYn, hinv⟩ :=
    exists_split hp hp2 hexp hXab hS2 hperm hnorm htS ht2 htQ hcent
  have hE := isE_one_sup hp hp2 hXp hS2 hperm hYX hY hYperm hYn hA.1 htA ht2
    ((le_omega1_of_mem_gammaSet hV hA).trans hΩ) hinv
  have hcomm := E3.e3_19_comm hV hSK (i := i) (j := 1) hi hA hE
  have hYC : Y ≤ centralizer (E3.cClos V (i + 1) S : Set G) :=
    (le_twoResidual_of_isPGroup hp hp2 (hXp.to_le hYX) le_sup_left).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
  have hYN : Y ≤ normalizer (centerOf (E3.wClos V (i + 1) S) : Set G) :=
    hYC.trans ((centralizer_le (centerOf_wClos_le_cClos_self (i + 1) S)).trans
      (centralizer_le_normalizer _))
  have hX₀N' : X₀ ≤ normalizer (centerOf (E3.wClos V (i + 1) S) : Set G) :=
    (le_normalizer_wClos_of_le (sup_le ((zpowers_le (H := S)).2 htS) hQS)
      (fun A' hA' => (le_omega1_of_mem_gammaSet hV hA').trans hΩ) hX₀N).trans
      (E3.normalizer_le_normalizer_centerOf _)
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hsplit x hx
  exact Subgroup.mul_mem _ (hX₀N' ha) (hYN hb)

theorem six_sixteen_close_NZ {V M H S : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hS : IsSylowIn 2 S H) {k : ℕ} (hk : 1 ≤ k)
    (hH : E1.InE k H) (hW0 : E3.wClos V 0 S ≠ ⊥) (hgt : k + 1 < E3.sParam hV)
    (hdag : ∀ i : ℕ, (i = 0 ∨ i = k) →
      InCalU M (M ⊓ normalizer (E3.wClos V i S : Set G)) ∨
        InCalU M (M ⊓ normalizer (centerOf (E3.wClos V (i + 1) S) : Set G))) :
    H ≤ M := by
  by_contra hHM
  have hsV : E3.sParam hV ≤ rk ↥V := E3.sParam_le_rk hV
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hfac0 := e3_19_of_inE hV hS (i := 0) (j := k) hH (by omega)
  have hfac1 := e3_19_of_inE hV hS (i := 1) (j := k) hH (by omega)
  have hCk1 : centralizer (E3.cClos V (1 + k) S : Set G) ≤ M := by
    rcases hdag k (Or.inr rfl) with h | h
    · exfalso
      have h3 := six_fifteen_three hV hM hS2 hW0 (i := k) (by omega) h
      apply hHM
      rw [← hfac0]
      exact sup_le (by simpa using inf_le_right.trans (h3.2 0 (Nat.zero_le k)))
        (by simpa using inf_le_right.trans (h3.1 0 (by omega)))
    · have hZne : centerOf (E3.wClos V (k + 1) S) ≠ ⊥ :=
        E3.centerOf_ne_bot_of_isPGroup (hS2.to_le (E3.wClos_le (k + 1) S))
          (wClos_ne_bot_of_zero hV hW0 (by omega))
      have hNZ : normalizer (centerOf (E3.wClos V (k + 1) S) : Set G) ≤ M :=
        normalizer_le_of_inCalU h inf_le_right hZne
          ((hS2.to_le (E3.wClos_le (k + 1) S)).to_le inf_le_left)
      have h := (centralizer_le (centerOf_wClos_le_cClos_self (k + 1) S)).trans
        ((centralizer_le_normalizer _).trans hNZ)
      simpa [Nat.add_comm] using h
  have hN1 : normalizer (E3.wClos V 1 S : Set G) ≤ M := by
    rcases hdag 0 (Or.inl rfl) with h | h
    · have h3 := six_fifteen_three hV hM hS2 hW0 (i := 0) (by omega) h
      exact h3.1 1 (by omega)
    · have hZ1ne : centerOf (E3.wClos V 1 S) ≠ ⊥ :=
        E3.centerOf_ne_bot_of_isPGroup (hS2.to_le (E3.wClos_le 1 S))
          (wClos_ne_bot_of_zero hV hW0 (by omega))
      have hNZ : normalizer (centerOf (E3.wClos V 1 S) : Set G) ≤ M :=
        normalizer_le_of_inCalU h inf_le_right hZ1ne
          ((hS2.to_le (E3.wClos_le 1 S)).to_le inf_le_left)
      exact (E3.normalizer_le_normalizer_centerOf _).trans hNZ
  apply hHM
  rw [← hfac1]
  exact sup_le (by simpa using inf_le_right.trans hCk1) (by simpa using inf_le_right.trans hN1)

theorem w3Lem616_1ii_of_key
    (hkey : ∀ {V S X : Subgroup G} (hV : IsElemAbelian 2 V) {p : ℕ}, p.Prime → p ≠ 2 →
      (∀ x ∈ X, x ^ p = 1) → (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → IsPGroup 2 S →
      (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G) →
      (∃ a ∈ F11.Omega1p 2 S, F11.Omega1p 2 S =
        Subgroup.zpowers a ⊔ (F11.Omega1p 2 S ⊓ pCoreOf 2 (X ⊔ S))) →
      ∀ {i : ℕ}, i + 1 < E3.sParam hV →
      X ≤ normalizer (E3.wClos V i S : Set G) ∨
        X ≤ normalizer (centerOf (E3.wClos V (i + 1) S) : Set G)) :
    PartTwo.W3Lem616_1ii G := by
  intro V M H S X hV hM _ _ hS k hk hH hW0 hgt p hp hp2 hXM hexp hXnc hperm hUY hcyc
  by_cases hbig : p ^ 2 < Nat.card X
  · exact six_sixteen_one_i_uncond hV hM hS hk hH hW0 hgt hp hp2 hXM hexp hbig hperm hUY
  have hXp : IsPGroup p X := isPGroup_of_pow_eq_one hexp
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hXp
  have hn2 : n = 2 := by
    have hle : n ≤ 2 := by
      by_contra h
      apply hbig
      rw [hn]
      exact Nat.pow_lt_pow_right hp.one_lt (by omega)
    interval_cases n
    · haveI : Subsingleton X := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
      exact absurd (isCyclic_of_subsingleton (α := X)) hXnc
    · exact absurd (isCyclic_of_prime_card (by simpa using hn) : IsCyclic X) hXnc
    · rfl
  subst hn2
  have hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    have h := IsPGroup.commutative_of_card_eq_prime_sq hn ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg Subtype.val h
  refine six_sixteen_close_NZ hV hM hS hk hH hW0 hgt ?_
  intro i hi
  have hi1 : i + 1 < E3.sParam hV := by rcases hi with rfl | rfl <;> omega
  have hUX := hUY X le_rfl hXnc
  rcases hkey hV hp hp2 hexp hXab hS.isPGroup hperm hcyc hi1 with h | h
  · exact Or.inl (InCalU.mono hM hUX (fun x hx => ⟨hXM hx, h hx⟩) inf_le_left)
  · exact Or.inr (InCalU.mono hM hUX (fun x hx => ⟨hXM hx, h hx⟩) inf_le_left)

theorem w3Lem616_1ii : PartTwo.W3Lem616_1ii G :=
  w3Lem616_1ii_of_key fun hV _ hp hp2 hexp hXab hS2 hperm hcyc _ hi =>
    six_sixteen_ii_key hV hp hp2 hexp hXab hS2 hperm hcyc hi

end CFSG.LocalAnalysis.WeakClosure81.SixSixteenOneII
