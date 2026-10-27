module

public import CFSG.Quasithin.Background.BlueprintB2Thompson


public section

namespace CFSG.Quasithin

open CFSG CFSG.Quasithin.BlueprintB2
open scoped Pointwise

namespace BlueprintB2

section PPrime

variable {G : Type*} [Group G] {p : ℕ}

@[expose] def pPrimeGen (p : ℕ) (Y : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ Y ∧ (orderOf x).Coprime p}

theorem pPrimeGen_le (Y : Subgroup G) : pPrimeGen p Y ≤ Y :=
  (Subgroup.closure_le Y).mpr fun _ hx => hx.1

theorem pPrimeGen_mono {X Y : Subgroup G} (h : X ≤ Y) : pPrimeGen p X ≤ pPrimeGen p Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem mem_pPrimeGen_of_coprime {Y : Subgroup G} {x : G} (hx : x ∈ Y)
    (h : (orderOf x).Coprime p) : x ∈ pPrimeGen p Y :=
  Subgroup.subset_closure ⟨hx, h⟩

private theorem mem_zpowers_pow_of_coprime_orderOf {x : G} {n : ℕ}
    (h : Nat.Coprime n (orderOf x)) : x ∈ Subgroup.zpowers (x ^ n) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  refine ⟨a, ?_⟩
  have hxo : x ^ (orderOf x : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  have h1 : x ^ (a * n + b * (orderOf x : ℤ)) = x := by rw [hab, zpow_one]
  have h2 : x ^ (a * n + b * (orderOf x : ℤ)) = x ^ (a * n) := by
    rw [zpow_add, mul_comm b, zpow_mul x _ b, hxo, one_zpow, mul_one]
  calc (x ^ n) ^ a = x ^ (a * n) := by rw [← zpow_natCast, ← zpow_mul, mul_comm]
    _ = x := h2.symm.trans h1

theorem pPrimeGen_le_of_pow_mem {X N : Subgroup G} (h : ∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k ∈ N) :
    pPrimeGen p X ≤ N := by
  refine (Subgroup.closure_le N).mpr fun x hx => ?_
  obtain ⟨k, hk⟩ := h x hx.1
  have hcop : Nat.Coprime (p ^ k) (orderOf x) := Nat.Coprime.pow_left k hx.2.symm
  exact (Subgroup.zpowers_le.mpr hk) (mem_zpowers_pow_of_coprime_orderOf hcop)

theorem exists_pow_mem_pPrimeGen [Finite G] [Fact p.Prime] {X : Subgroup G} {x : G}
    (hx : x ∈ X) : ∃ k : ℕ, x ^ p ^ k ∈ pPrimeGen p X := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p
    (Fact.out : p.Prime).ne_one
  refine ⟨k, mem_pPrimeGen_of_coprime (X.pow_mem hx _) ?_⟩
  have hpk : (p ^ k : ℕ) ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  rw [orderOf_pow' _ hpk, hkm, Nat.gcd_mul_right_left,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hpk)]
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hm).symm

theorem pPrimeGen_map [Finite G] [Fact p.Prime] {G' : Type*} [Group G'] (f : G →* G')
    (X : Subgroup G) : pPrimeGen p (X.map f) = (pPrimeGen p X).map f := by
  apply le_antisymm
  · refine pPrimeGen_le_of_pow_mem fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, hk⟩ := exists_pow_mem_pPrimeGen (p := p) hx
    exact ⟨k, ⟨_, hk, by rw [map_pow]⟩⟩
  · rw [pPrimeGen, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨hx, ho⟩, rfl⟩
    exact mem_pPrimeGen_of_coprime (Subgroup.mem_map_of_mem f hx)
      (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd f x) ho)

theorem pPrimeGen_top_normal : (pPrimeGen p (⊤ : Subgroup G)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    refine mem_pPrimeGen_of_coprime (Subgroup.mem_top _) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx.2
  | one => simp
  | mul x y _ _ ihx ihy => simpa [mul_assoc] using (pPrimeGen p ⊤).mul_mem ihx ihy
  | inv x _ ih => simpa [mul_assoc] using (pPrimeGen p ⊤).inv_mem ih

theorem exists_mul_mem_ker_of_map_le [Finite G] [Fact p.Prime] {H : Type*} [Group H] (f : G →* H)
    {I : Subgroup G} (h : (pPrimeGen p (⊤ : Subgroup G)).map f ≤ I.map f) :
    ∀ l ∈ pPrimeGen p (⊤ : Subgroup G), ∃ d ∈ pPrimeGen p I, f (d⁻¹ * l) = 1 := by
  have hle : (pPrimeGen p (⊤ : Subgroup G)).map f ≤ pPrimeGen p (I.map f) := by
    rw [pPrimeGen, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact mem_pPrimeGen_of_coprime
      (h (Subgroup.mem_map_of_mem f (mem_pPrimeGen_of_coprime (Subgroup.mem_top x) hx)))
      (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd f x) hx)
  intro l hl
  have hfl : f l ∈ (pPrimeGen p I).map f := by
    rw [← pPrimeGen_map]
    exact hle (Subgroup.mem_map_of_mem f hl)
  obtain ⟨d, hd, hdl⟩ := hfl
  exact ⟨d, hd, by rw [map_mul, map_inv, hdl, inv_mul_cancel]⟩

theorem pPrimeGen_top_le_of_forall {Q I : Subgroup G} [I.Normal] (hQ : IsPGroup p Q)
    (h : ∀ l ∈ pPrimeGen p (⊤ : Subgroup G), ∃ q ∈ Q, ∃ i ∈ I, l = q * i) :
    pPrimeGen p (⊤ : Subgroup G) ≤ I := by
  refine (Subgroup.closure_le I).mpr fun g hg => ?_
  obtain ⟨q, hq, i, hi, hgqi⟩ := h g (mem_pPrimeGen_of_coprime (Subgroup.mem_top g) hg.2)
  obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
  have hqk : q ^ p ^ k = 1 := congrArg Subtype.val hk
  have hi1 : QuotientGroup.mk' I i = 1 := (QuotientGroup.eq_one_iff i).mpr hi
  have hπg : QuotientGroup.mk' I g = QuotientGroup.mk' I q := by
    rw [hgqi, map_mul, hi1, mul_one]
  have hd1 : orderOf (QuotientGroup.mk' I g) ∣ orderOf g := orderOf_map_dvd _ g
  have hd2 : orderOf (QuotientGroup.mk' I g) ∣ p ^ k := by
    rw [hπg]
    exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hqk, map_one])
  have hcop : Nat.Coprime (orderOf g) (p ^ k) := Nat.Coprime.pow_right k hg.2
  have h1 : orderOf (QuotientGroup.mk' I g) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact (QuotientGroup.eq_one_iff g).mp (orderOf_eq_one_iff.mp h1)

end PPrime

theorem exists_mul_mem_pCore_of_frattini {L : Type*} [Group L] [Finite L] (p : ℕ)
    (D C : Subgroup L) (hDC : ∀ l : L, ∃ d ∈ D, d⁻¹ * l ∈ C)
    (hΦ : C.map (QuotientGroup.mk' (CFSG.pCore p L)) ≤ frattini (L ⧸ CFSG.pCore p L)) :
    ∀ l : L, ∃ d ∈ D, d⁻¹ * l ∈ CFSG.pCore p L := by
  intro l0
  have hsup : D.map (QuotientGroup.mk' (CFSG.pCore p L)) ⊔ frattini (L ⧸ CFSG.pCore p L) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore p L) x
    obtain ⟨d, hd, hc⟩ := hDC l
    have hl : QuotientGroup.mk' (CFSG.pCore p L) l =
        QuotientGroup.mk' (CFSG.pCore p L) d * QuotientGroup.mk' (CFSG.pCore p L) (d⁻¹ * l) := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [hl]
    exact Subgroup.mul_mem_sup ⟨d, hd, rfl⟩ (hΦ ⟨_, hc, rfl⟩)
  have htop : D.map (QuotientGroup.mk' (CFSG.pCore p L)) = ⊤ := frattini_nongenerating hsup
  have hmem : QuotientGroup.mk' (CFSG.pCore p L) l0 ∈
      D.map (QuotientGroup.mk' (CFSG.pCore p L)) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨d, hd, hdl⟩ := hmem
  refine ⟨d, hd, (QuotientGroup.eq_one_iff _).mp ?_⟩
  have : QuotientGroup.mk' (CFSG.pCore p L) (d⁻¹ * l0) = 1 := by
    rw [map_mul, map_inv, hdl, inv_mul_cancel]
  exact this

section Conj

variable {G : Type*} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have : g * (MulAut.conj g⁻¹).toMonoidHom h * g⁻¹ = h := by
      simp [mul_assoc]
    rw [this]
    exact hh
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem conjugate_mul (H : Subgroup G) (g h : G) :
    conjugate H (g * h) = conjugate (conjugate H g) h := by
  ext x
  simp only [mem_conjugate_iff]
  rw [show g * h * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ by group]

theorem conjugate_mono {H K : Subgroup G} (h : H ≤ K) (g : G) : conjugate H g ≤ conjugate K g :=
  Subgroup.map_mono h

theorem conjugate_eq_self_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : conjugate H g = H := by
  ext x
  rw [mem_conjugate_iff]
  exact (Subgroup.mem_normalizer_iff.mp hg x).symm

theorem conjugate_le_normalClosure (J : Subgroup G) (g : G) :
    conjugate J g ≤ Subgroup.normalClosure (J : Set G) := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  have h1 : g * x * g⁻¹ ∈ Subgroup.normalClosure (J : Set G) := Subgroup.subset_normalClosure hx
  have := (Subgroup.normalClosure_normal (s := (J : Set G))).conj_mem _ h1 g⁻¹
  simpa [mul_assoc] using this

theorem sup_eq_top_iff_forall_mul {L R : Subgroup G} [L.Normal] :
    L ⊔ R = ⊤ ↔ ∀ g : G, ∃ l ∈ L, ∃ r ∈ R, g = l * r := by
  constructor
  · intro h g
    have hg : g ∈ (↑(L ⊔ R) : Set G) := by
      rw [h]
      exact Subgroup.mem_top g
    rw [Subgroup.normal_mul] at hg
    obtain ⟨l, hl, r, hr, rfl⟩ := Set.mem_mul.mp hg
    exact ⟨l, hl, r, hr, rfl⟩
  · intro h
    refine eq_top_iff.mpr fun g _ => ?_
    obtain ⟨l, hl, r, hr, rfl⟩ := h g
    exact Subgroup.mul_mem_sup hl hr

theorem forall_exists_conjugate_eq {J L R Q I : Subgroup G} [L.Normal] (hLR : L ⊔ R = ⊤)
    (hR : ∀ r ∈ R, conjugate J r = J) (hQR : Q ≤ R)
    (hLQI : ∀ l ∈ L, ∃ q ∈ Q, ∃ i ∈ I, l = q * i) :
    ∀ g : G, ∃ i ∈ I, conjugate J g = conjugate J i := by
  intro g
  have hg : g ∈ (↑(L ⊔ R) : Set G) := by
    rw [hLR]
    exact Subgroup.mem_top g
  rw [Subgroup.normal_mul] at hg
  obtain ⟨l, hl, r, hr, rfl⟩ := Set.mem_mul.mp hg
  have hl' : r⁻¹ * l * r ∈ L := by
    simpa using (inferInstance : L.Normal).conj_mem l hl r⁻¹
  obtain ⟨q, hq, i, hi, hqi⟩ := hLQI _ hl'
  refine ⟨i, hi, ?_⟩
  have hlr : l * r = r * (r⁻¹ * l * r) := by group
  rw [hlr, conjugate_mul, hR r hr, hqi, conjugate_mul, hR q (hQR hq)]

theorem normalClosure_le_of_forall_exists_conjugate_eq {J I : Subgroup G} (hJI : J ≤ I)
    (h : ∀ g : G, ∃ i ∈ I, conjugate J g = conjugate J i) :
    Subgroup.normalClosure (J : Set G) ≤ I := by
  rw [Subgroup.normalClosure, Subgroup.closure_le]
  intro x hx
  rw [SetLike.mem_coe]
  obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨c, hcx⟩ := isConj_iff.mp hc
  obtain ⟨i, hi, hconj⟩ := h c⁻¹
  have hx1 : x ∈ conjugate J c⁻¹ := by
    rw [mem_conjugate_iff]
    have : c⁻¹ * x * c⁻¹⁻¹ = a := by rw [← hcx]; group
    rw [this]
    exact ha
  rw [hconj, mem_conjugate_iff] at hx1
  have := I.mul_mem (I.mul_mem (I.inv_mem hi) (hJI hx1)) hi
  simpa [mul_assoc] using this

theorem mem_centralizer_of_conjNormal_eq_one {V : Subgroup G} [V.Normal] {g : G}
    (h : MulAut.conjNormal (H := V) g = 1) : g ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) h
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

end Conj

theorem map_subtype_eq_self_iff {G : Type*} [Group G] {X : Subgroup G} (K : Subgroup X) :
    K.map X.subtype = X ↔ K = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ K.map X.subtype := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  · rintro rfl
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

section Thompson

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem le_normalizer_map_elemThompson (R : Subgroup G) :
    R ≤ Subgroup.normalizer (((elemThompson R p).map R.subtype : Subgroup G) : Set G) := by
  have key : ∀ r ∈ R, ∀ x ∈ (elemThompson R p).map R.subtype,
      r * x * r⁻¹ ∈ (elemThompson R p).map R.subtype := by
    intro r hr x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 := Subgroup.mem_comap.mp
      (Subgroup.characteristic_iff_le_comap.mp (elemThompson_characteristic R p)
        (MulAut.conj (⟨r, hr⟩ : R)) hy)
    exact ⟨_, h1, by simp⟩
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨key r hr x, fun hx => by simpa [mul_assoc] using key r⁻¹ (R.inv_mem hr) _ hx⟩

omit [Finite G] [Fact p.Prime] in
theorem le_conjugate_inv_of_conjugate_le {R X : Subgroup G} {l : G}
    (hXJ : (elemThompson X p).map X.subtype = X) (hXe : pRank p X = pRank p R)
    (hl : conjugate X l ≤ R) :
    X ≤ conjugate ((elemThompson R p).map R.subtype) l⁻¹ := by
  calc X = (elemThompson X p).map X.subtype := hXJ.symm
    _ ≤ _ := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun A hA => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      have hBX : A.map X.subtype ≤ X := by
        rintro _ ⟨a, -, rfl⟩
        exact a.2
      have hB'R : conjugate (A.map X.subtype) l ≤ R := (conjugate_mono hBX l).trans hl
      have hBe : IsElementaryAbelian p (A.map X.subtype) := isElementaryAbelian_map hA.1 _
      have hB'e : IsElementaryAbelian p (conjugate (A.map X.subtype) l) :=
        isElementaryAbelian_map hBe _
      have hcard : Nat.card (conjugate (A.map X.subtype) l) = Nat.card A := by
        unfold conjugate
        rw [Subgroup.card_map_of_injective (MulAut.conj l⁻¹).injective,
          Subgroup.card_map_of_injective X.subtype_injective]
      have hmem : (conjugate (A.map X.subtype) l).subgroupOf R ∈ elemThompsonFamily R p :=
        ⟨isElementaryAbelian_subgroupOf hB'e, by rw [card_subgroupOf_eq hB'R, hcard, hA.2, hXe]⟩
      have hB'J : conjugate (A.map X.subtype) l ≤ (elemThompson R p).map R.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hB'R]
        exact Subgroup.map_mono (le_elemThompson hmem)
      intro x hx
      rw [mem_conjugate_iff]
      have hx' : l⁻¹ * x * l ∈ conjugate (A.map X.subtype) l := by
        rw [mem_conjugate_iff]
        simpa [mul_assoc] using hx
      simpa using hB'J hx'

end Thompson

end BlueprintB2

theorem qt_nq_frattini_thompson_normal_closure_generation {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (V : Subgroup G) [V.Normal] (_hV : IsElementaryAbelian p V)
    (R : Subgroup G) (hR : IsPGroup p R) (_hVR : V ≤ R)
    (L : Subgroup G) (hL : L = Subgroup.closure {g : G | Nat.Coprime (orderOf g) p})
    (hLR : L ⊔ R = ⊤) (Q P : Subgroup G) (hQ : Q = R ⊓ Subgroup.centralizer (V : Set G))
    (hP : P = inSubgroup (pCore p) L) (hPQ : P ≤ Q)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hΦ : ((Subgroup.centralizer (V : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore p L)) ≤ frattini (L ⧸ CFSG.pCore p L))
    (n : ℕ) (_hn : 1 ≤ n) (X : Fin n → Subgroup G)
    (hXL : ∀ i, ∃ l ∈ L, conjugate (X i) l ≤ R)
    (hXJ : ∀ i, (elemThompson (X i) p).map (X i).subtype = X i)
    (hXe : ∀ i, pRank p (X i) = pRank p R)
    (I : Subgroup G) (hI : I = ⨆ i, X i)
    (hρ : L.map (MulAut.conjNormal (H := V)) ≤ I.map (MulAut.conjNormal (H := V)))
    (J : Subgroup G) (hJ : J = (elemThompson R p).map R.subtype) (hJI : J ≤ I) :
    Q.Normal ∧ (I = Subgroup.normalClosure (J : Set G) ∧ I.Normal) ∧ L ≤ I ∧
      {K : Subgroup G | ∃ g : G, K = conjugate J g} =
        {K : Subgroup G | ∃ i ∈ I, K = conjugate J i} := by
  have hL' : L = BlueprintB2.pPrimeGen p (⊤ : Subgroup G) := by
    rw [hL, BlueprintB2.pPrimeGen]
    congr 1
    ext x
    simp
  have hLn : L.Normal := hL' ▸ BlueprintB2.pPrimeGen_top_normal
  have hQR : Q ≤ R := hQ ▸ inf_le_left
  have hRQ : R ≤ Subgroup.normalizer (Q : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro q
    subst hQ
    constructor
    · rintro ⟨hqR, hqC⟩
      exact ⟨R.mul_mem (R.mul_mem hr hqR) (R.inv_mem hr),
        (inferInstance : (Subgroup.centralizer (V : Set G)).Normal).conj_mem _ hqC r⟩
    · rintro ⟨hqR, hqC⟩
      refine ⟨?_, ?_⟩
      · simpa [mul_assoc] using R.mul_mem (R.mul_mem (R.inv_mem hr) hqR) hr
      · simpa [mul_assoc] using
          (inferInstance : (Subgroup.centralizer (V : Set G)).Normal).conj_mem _ hqC r⁻¹
  have hQn : Q.Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr ?_)
    rw [← hLR]
    exact sup_le hLQ hRQ
  have hρ' := BlueprintB2.exists_mul_mem_ker_of_map_le (p := p) (MulAut.conjNormal (H := V))
    (I := I) (by rw [← hL']; exact hρ)
  have hDL : BlueprintB2.pPrimeGen p I ≤ L := hL' ▸ BlueprintB2.pPrimeGen_mono le_top
  have hD : ∀ l ∈ L, ∃ d ∈ BlueprintB2.pPrimeGen p I,
      d⁻¹ * l ∈ Subgroup.centralizer (V : Set G) := by
    intro l hl
    obtain ⟨d, hd, h1⟩ := hρ' l (hL' ▸ hl)
    exact ⟨d, hd, BlueprintB2.mem_centralizer_of_conjNormal_eq_one h1⟩
  have hDC : ∀ l : L, ∃ d ∈ (BlueprintB2.pPrimeGen p I).subgroupOf L,
      d⁻¹ * l ∈ (Subgroup.centralizer (V : Set G)).subgroupOf L := by
    intro l
    obtain ⟨d, hd, hdc⟩ := hD l l.2
    exact ⟨⟨d, hDL hd⟩, hd, hdc⟩
  have hfr := BlueprintB2.exists_mul_mem_pCore_of_frattini p _ _ hDC hΦ
  have hP' : ∀ l ∈ L, ∃ d ∈ BlueprintB2.pPrimeGen p I, d⁻¹ * l ∈ P := by
    intro l hl
    obtain ⟨d, hd, hdp⟩ := hfr ⟨l, hl⟩
    exact ⟨d, hd, by rw [hP]; exact ⟨_, hdp, rfl⟩⟩
  have hLQI : ∀ l ∈ L, ∃ q ∈ Q, ∃ i ∈ I, l = q * i := by
    intro l hl
    obtain ⟨d, hd, hdP⟩ := hP' l hl
    exact ⟨d * (d⁻¹ * l) * d⁻¹, hQn.conj_mem _ (hPQ hdP) d, d,
      BlueprintB2.pPrimeGen_le I hd, by group⟩
  have hRJ : ∀ r ∈ R, conjugate J r = J := fun r hr => by
    rw [hJ]
    exact BlueprintB2.conjugate_eq_self_of_mem_normalizer
      (BlueprintB2.le_normalizer_map_elemThompson R hr)
  have hconj := BlueprintB2.forall_exists_conjugate_eq hLR hRJ hQR hLQI
  have hN_le : Subgroup.normalClosure (J : Set G) ≤ I :=
    BlueprintB2.normalClosure_le_of_forall_exists_conjugate_eq hJI hconj
  have hI_le : I ≤ Subgroup.normalClosure (J : Set G) := by
    rw [hI]
    refine iSup_le fun i => ?_
    obtain ⟨l, -, hlR⟩ := hXL i
    rw [hJ] at *
    exact (BlueprintB2.le_conjugate_inv_of_conjugate_le (hXJ i) (hXe i) hlR).trans
      (BlueprintB2.conjugate_le_normalClosure _ l⁻¹)
  have hIN : I = Subgroup.normalClosure (J : Set G) := le_antisymm hI_le hN_le
  have hIn : I.Normal := hIN ▸ Subgroup.normalClosure_normal
  refine ⟨hQn, ⟨hIN, hIn⟩, ?_, ?_⟩
  · rw [hL']
    exact BlueprintB2.pPrimeGen_top_le_of_forall (hR.to_le hQR)
      (fun l hl => hLQI l (hL' ▸ hl))
  · ext K
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨i, hi, h⟩ := hconj g
      exact ⟨i, hi, h⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩

end CFSG.Quasithin
