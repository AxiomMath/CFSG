module

public import CFSG.Quasithin.H13.L32A705a
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFixROver

public section

namespace CFSG.Quasithin.H13.L32A.M76

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem isPGroup_preimage (h : HypF91 T V L V₁ Vp H)
    {P : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))} (hP : IsPGroup 2 P) :
    IsPGroup 2 ((P.comap (FixR.rho h)).map H.subtype) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨k, hk⟩ := hP ⟨FixR.rho h y, hy⟩
  have h1 : FixR.rho h (y ^ 2 ^ k) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hk
  obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨_, (FixR.rho_eq_one_iff h _).mp h1⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have h2 : (((y : G) ^ 2 ^ k) ^ 2 ^ j : G) = 1 := by simpa using congrArg Subtype.val hj
  simp only [Subgroup.subtype_apply, SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [pow_add, pow_mul]
  exact h2

theorem pCoreOf_autOn_eq_bot' (h : HypF91 T V L V₁ Vp H) :
    pCoreOf 2 (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)) with hX
  set N := ((pCoreOf 2 X).comap (FixR.rho h)).map H.subtype with hN
  have hNH : N ≤ H := Subgroup.map_subtype_le _
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * y * (⟨g, hg⟩ : ↥H)⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hgX : FixR.rho h ⟨g, hg⟩ ∈ X :=
      (FixR.mem_autOn_tilde_iff h le_rfl).mpr ⟨⟨g, hg⟩, hg, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 X hgX) _).mp hy
  have hNQ : N ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 hNH hHN (isPGroup_preimage h (pCoreOf_isPGroup 2 X))
  refine eq_bot_iff.mpr fun a ha => ?_
  obtain ⟨y, -, rfl⟩ := (FixR.mem_autOn_tilde_iff h le_rfl).mp (pCoreOf_le 2 X ha)
  rw [Subgroup.mem_bot]
  exact (FixR.rho_eq_one_iff h y).mpr (hNQ (Subgroup.mem_map.mpr ⟨y, ha, rfl⟩))

theorem exists_conj_le (h : HypF91 T V L V₁ Vp H) {S : Subgroup G} (hS : IsSylowTwoOf S H)
    {A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))}
    (hAX : A ≤ autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) (hA : IsPGroup 2 A) :
    ∃ x : ↥H, ∀ a ∈ A, (FixR.rho h x)⁻¹ * a * FixR.rho h x ∈
      autOn (tildeOf V₁ S) (tildeOf V₁ (conjClosure Vp H)) := by
  obtain ⟨x, hxH, hBx⟩ :=
    F7.isSylowTwoOf_exists_conj_le hS (Subgroup.map_subtype_le _) (isPGroup_preimage h hA)
  refine ⟨⟨x, hxH⟩, fun a ha => ?_⟩
  obtain ⟨y, -, hy⟩ := (FixR.mem_autOn_tilde_iff h le_rfl).mp (hAX ha)
  have hyB :=
    hBx (Subgroup.mem_map.mpr ⟨y, by rw [Subgroup.mem_comap, hy]; exact ha, rfl⟩)
  rw [CFSG.Quasithin.mem_conjSub] at hyB
  refine (FixR.mem_autOn_tilde_iff h hS.1).mpr ⟨(⟨x, hxH⟩ : ↥H)⁻¹ * y * ⟨x, hxH⟩, by
    simpa using hyB, ?_⟩
  rw [map_mul, map_mul, hy, map_inv]

theorem mk_eq_of_rho_eq (h : HypF91 T V L V₁ Vp H) {x y : ↥H}
    (hxy : FixR.rho h x = FixR.rho h y) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) x = QuotientGroup.mk' (CFSG.pCore 2 ↥H) y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← pCoreOf_subgroupOf',
    Subgroup.mem_subgroupOf]
  have h1 : FixR.rho h (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
  simpa using (FixR.rho_eq_one_iff h _).mp h1

theorem rho_eq_of_mk_eq (h : HypF91 T V L V₁ Vp H) {x y : ↥H}
    (hxy : QuotientGroup.mk' (CFSG.pCore 2 ↥H) x = QuotientGroup.mk' (CFSG.pCore 2 ↥H) y) :
    FixR.rho h x = FixR.rho h y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← pCoreOf_subgroupOf',
    Subgroup.mem_subgroupOf] at hxy
  have h1 := (FixR.rho_eq_one_iff h (x⁻¹ * y)).mpr (by simpa using hxy)
  rw [map_mul, map_inv] at h1
  exact (inv_mul_eq_one.mp h1)

theorem eq_of_minimal (h : HypF91 T V L V₁ Vp H) {Y : Subgroup G} (hYH : Y ≤ H)
    (hmin : ∀ N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), N.Normal → N ≠ ⊥ → N ≤ modO2Image H Y →
      N = modO2Image H Y)
    {N : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))}
    (hNY : N ≤ autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H)))
    (hXN : autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)) ≤ Subgroup.normalizer (N : Set _))
    (hN1 : N ≠ ⊥) : N = autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H)) := by
  set N' := (N.comap (FixR.rho h)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) with hN'
  have hnorm : (N.comap (FixR.rho h)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hgX : FixR.rho h g ∈ autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)) :=
      (FixR.mem_autOn_tilde_iff h le_rfl).mpr ⟨g, g.2, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hXN hgX) _).mp hn⟩
  have hN'n : N'.Normal := hnorm.map _ (QuotientGroup.mk'_surjective _)
  have hN'1 : N' ≠ ⊥ := by
    obtain ⟨⟨a, haN⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hN1
    obtain ⟨y, -, hy⟩ := (FixR.mem_autOn_tilde_iff h hYH).mp (hNY haN)
    intro hbot
    have hyN' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) y ∈ N' :=
      Subgroup.mem_map.mpr ⟨y, by rw [Subgroup.mem_comap, hy]; exact haN, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hyN'
    have h1 := rho_eq_of_mk_eq h (hyN'.trans (map_one _).symm)
    rw [map_one, hy] at h1
    exact ha1 (Subtype.ext h1)
  have hN'Y : N' ≤ modO2Image H Y := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hyY, hy⟩ := (FixR.mem_autOn_tilde_iff h hYH).mp (hNY hx)
    exact mem_modO2Image'.mpr ⟨y, hyY, mk_eq_of_rho_eq h hy⟩
  have heq := hmin N' hN'n hN'1 hN'Y
  refine le_antisymm hNY fun a ha => ?_
  obtain ⟨y, hyY, rfl⟩ := (FixR.mem_autOn_tilde_iff h hYH).mp ha
  have hy : QuotientGroup.mk' (CFSG.pCore 2 ↥H) y ∈ N' := by
    rw [heq]
    exact mem_modO2Image'.mpr ⟨y, hyY, rfl⟩
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  rw [← rho_eq_of_mk_eq h hxy]
  exact hx

theorem comm_of_minimal (h : HypF91 T V L V₁ Vp H) {Y : Subgroup G} (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G))
    (hmin : ∀ N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), N.Normal → N ≠ ⊥ → N ≤ modO2Image H Y →
      N = modO2Image H Y) {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p (autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H))))
    (hne : autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H)) ≠ ⊥) :
    ∀ a ∈ autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H)),
      ∀ b ∈ autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H)), a * b = b * a := by
  set E := autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H)) with hE
  set X := autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)) with hX
  have hXE : ∀ g ∈ X, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg e he
    obtain ⟨x, -, rfl⟩ := (FixR.mem_autOn_tilde_iff h le_rfl).mp hg
    obtain ⟨y, hyY, rfl⟩ := (FixR.mem_autOn_tilde_iff h hYH).mp he
    refine (FixR.mem_autOn_tilde_iff h hYH).mpr ⟨x * y * x⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHY x.2) _).mp hyY
  set Z := E ⊓ Subgroup.centralizer (E : Set (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) with hZ
  have hZ1 : Z ≠ ⊥ := by
    have : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hne
    have : Finite (MulAut ↥(tildeOf V₁ (conjClosure Vp H))) :=
      Finite.of_injective _ MulEquiv.toEquiv_injective
    have := hp.center_nontrivial
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center ↥E)
    refine (Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨(z : MulAut _), z.2, fun e he => ?_⟩, ?_⟩
    · have := (Subgroup.mem_center_iff.mp hz) ⟨e, he⟩
      exact congrArg Subtype.val this
    · intro h1
      apply hz1
      have h2 : ((z : ↥E) : MulAut ↥(tildeOf V₁ (conjClosure Vp H))) = 1 :=
        congrArg Subtype.val h1
      exact Subtype.ext (Subtype.ext h2)
  have hXZ : X ≤ Subgroup.normalizer (Z : Set _) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun z hz => ⟨hXE g hg z hz.1, fun e he => ?_⟩
    have h1 := hz.2 (g⁻¹ * e * g) (by simpa using hXE g⁻¹ (X.inv_mem hg) e he)
    calc e * (g * z * g⁻¹) = g * ((g⁻¹ * e * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * e := by group
  have hZE := eq_of_minimal h hYH hmin inf_le_left hXZ hZ1
  intro a ha b hb
  have haZ : a ∈ Z := (congrArg (fun S => a ∈ S) hZE).mpr ha
  exact (haZ.2 b hb).symm

theorem le_pRank' {p : ℕ} (hp : p.Prime) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H :=
  CFSG.SectionRank.le_pRank hp.one_lt hEH hE hk

theorem exists_card_img_eq (h : HypF91 T V L V₁ Vp H) {Y : Subgroup G} (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hc : ∀ a ∈ autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H)),
      ∀ b ∈ autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H)), a * b = b * a)
    (hexp : ∀ y ∈ Y, y ^ p ∈ pCoreOf 2 Y) :
    ∃ k, k ≤ CFSG.Open.pRank p H ∧
      Nat.card (autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H))) = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H)) with hE
  have hYQ : pCoreOf 2 Y = Y ⊓ pCoreOf 2 H := S152Y.pCoreOf_eq_inf_of_normalizer hYH hHY
  have hEp : IsPGroup p E := by
    rintro ⟨a, ha⟩
    obtain ⟨y, hyY, rfl⟩ := (FixR.mem_autOn_tilde_iff h hYH).mp ha
    refine ⟨1, Subtype.ext ?_⟩
    have h1 : FixR.rho h (y ^ p) = 1 := (FixR.rho_eq_one_iff h _).mpr (by
      have := hexp y hyY
      rw [hYQ] at this
      simpa using this.2)
    simpa [map_pow] using h1
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  obtain ⟨S⟩ : Nonempty (Sylow p ↥Y) := inferInstance
  set P := (S : Subgroup ↥Y).map Y.subtype with hP
  have hPY : P ≤ Y := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := S.isPGroup'.map Y.subtype
  have hPcard : Nat.card P = Nat.card S := Subgroup.card_map_of_injective Y.subtype_injective
  have hinj : ∀ x ∈ P, x ∈ pCoreOf 2 H → x = 1 := by
    intro x hxP hxQ
    obtain ⟨i, hi⟩ := hPp ⟨x, hxP⟩
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨x, hxQ⟩
    have hi' : x ^ p ^ i = 1 := by simpa using congrArg Subtype.val hi
    have hj' : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.Coprime (p ^ i) (2 ^ j) :=
      Nat.Coprime.pow i j ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have h1 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hi') hcop)
      (orderOf_dvd_of_pow_eq_one hj')
    exact orderOf_eq_one_iff.mp h1
  have hYcard : Nat.card Y = Nat.card (pCoreOf 2 Y) * Nat.card E := by
    rw [hE, HypF91.card_autOn_tilde h hYH, ← hYQ,
      ← Subgroup.card_mul_index ((pCoreOf 2 Y).subgroupOf Y)]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 Y)).toEquiv
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 Y).exists_card_eq
  have hScard : Nat.card S = p ^ k := by
    rw [Sylow.card_eq_multiplicity, hYcard, ha, hk, Nat.factorization_mul
      (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow hp,
      Finsupp.single_apply, Finsupp.single_apply]
    simp [hp2.symm]
  have hPE : ∀ x ∈ P, ∀ hxH : x ∈ H, FixR.rho h ⟨x, hxH⟩ ∈ E := fun x hxP hxH =>
    (FixR.mem_autOn_tilde_iff h hYH).mpr ⟨⟨x, hxH⟩, hPY hxP, rfl⟩
  have hρinj : ∀ x ∈ P, ∀ y ∈ P, ∀ (hxH : x ∈ H) (hyH : y ∈ H),
      FixR.rho h ⟨x, hxH⟩ = FixR.rho h ⟨y, hyH⟩ → x = y := by
    intro x hxP y hyP hxH hyH hxy
    have h1 : FixR.rho h (⟨x, hxH⟩⁻¹ * ⟨y, hyH⟩) = 1 := by
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 := hinj _ (P.mul_mem (P.inv_mem hxP) hyP)
      (by simpa using (FixR.rho_eq_one_iff h _).mp h1)
    rw [inv_mul_eq_one] at h2
    exact h2
  have hPE' : IsElemAbelian p P := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hxP => ?_⟩
    · have haH := hYH (hPY a.2)
      have hbH := hYH (hPY b.2)
      have h1 := hc _ (hPE _ a.2 haH) _ (hPE _ b.2 hbH)
      rw [← map_mul, ← map_mul] at h1
      exact hρinj _ (P.mul_mem a.2 b.2) _ (P.mul_mem b.2 a.2) (H.mul_mem haH hbH)
        (H.mul_mem hbH haH) h1
    · have hxH := hYH (hPY hxP)
      have h1 : FixR.rho h (⟨x, hxH⟩ ^ p) = 1 := (FixR.rho_eq_one_iff h _).mpr (by
        have := hexp x (hPY hxP)
        rw [hYQ] at this
        simpa using this.2)
      exact hρinj _ (P.pow_mem hxP p) _ P.one_mem (H.pow_mem hxH p) H.one_mem
        (h1.trans (map_one _).symm)
  exact ⟨k, le_pRank' hp (hPY.trans hYH) hPE' (by rw [hPcard, hScard]), hk⟩

end CFSG.Quasithin.H13.L32A.M76
