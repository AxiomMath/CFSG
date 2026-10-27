module

public import CFSG.Quasithin.Vol2.Ch11SecS12K
public import CFSG.Quasithin.Vol2.Ch11SecS12X
public import CFSG.Quasithin.Vol2.Ch11SecSCartan
public import CFSG.Quasithin.Vol2.Ch11SecSXCard

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_comm_ne_one {P : Subgroup G} (hP : IsPGroup 2 ↥P) {y c : G} (hy3 : y ^ 3 = 1)
    (hyP : y ∈ Subgroup.normalizer (P : Set G)) (hc : c ∈ P) (hne : y * c * y⁻¹ * c⁻¹ ≠ 1) :
    y * (y * c * y⁻¹ * c⁻¹) * y⁻¹ * (y * c * y⁻¹ * c⁻¹)⁻¹ ≠ 1 := by
  intro h
  set d := y * c * y⁻¹ * c⁻¹ with hd
  have hyd : y * d * y⁻¹ = d := mul_inv_eq_one.mp h
  have e1 : y * c * y⁻¹ = d * c := by rw [hd]; group
  have e2 : y * (d * c) * y⁻¹ = d * (d * c) := by
    calc y * (d * c) * y⁻¹ = (y * d * y⁻¹) * (y * c * y⁻¹) := by group
      _ = d * (d * c) := by rw [hyd, e1]
  have e3 : y * (d * (d * c)) * y⁻¹ = d * (d * (d * c)) := by
    calc y * (d * (d * c)) * y⁻¹ = (y * d * y⁻¹) * (y * (d * c) * y⁻¹) := by group
      _ = d * (d * (d * c)) := by rw [hyd, e2]
  have e4 : y * (y * (y * c * y⁻¹) * y⁻¹) * y⁻¹ = c := by
    calc y * (y * (y * c * y⁻¹) * y⁻¹) * y⁻¹ = (y * (y * y)) * c * (y * (y * y))⁻¹ := by group
      _ = c := by rw [← pow_three, hy3]; group
  rw [e1, e2, e3] at e4
  have hd3 : d ^ 3 = 1 := by
    have : d * (d * (d * c)) * c⁻¹ = d * (d * d) := by group
    rw [pow_three, ← this, e4, mul_inv_cancel]
  have hdP : d ∈ P :=
    P.mul_mem ((Subgroup.mem_normalizer_iff.mp hyP c).mp hc) (P.inv_mem hc)
  obtain ⟨k, hk⟩ := hP ⟨d, hdP⟩
  have hk' : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
  have h2 : orderOf d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h5 : orderOf d = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)) h1 h2
  exact hne (orderOf_eq_one_iff.mp h5)

abbrev lXOne (L X₁ : Subgroup G) : Subgroup G :=
  perfectCore (L ⊓ Subgroup.normalizer (X₁ : Set G))

omit [Finite G] in
theorem exists_pow_eq_mul {P : Subgroup G} {l o : G} (hl : l ∈ P)
    (ho : o ∈ Subgroup.normalizer (P : Set G)) (n : ℕ) : ∃ l' ∈ P, (l * o) ^ n = l' * o ^ n := by
  induction n with
  | zero => exact ⟨1, P.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', e⟩ := ih
    refine ⟨l' * (o ^ n * l * (o ^ n)⁻¹), P.mul_mem hl' ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ho n) l).mp hl
    · rw [pow_succ, e]
      group

theorem map_perfectCore_eq_top {L X₁ : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hcov : ∀ l ∈ L, ∃ b ∈ pCoreOf 2 L, l * b ∈ Subgroup.normalizer (X₁ : Set G)) :
    (perfectCore ((L ⊓ Subgroup.normalizer (X₁ : Set G)).subgroupOf L)).map
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)) = ⊤ := by
  set N' := (L ⊓ Subgroup.normalizer (X₁ : Set G)).subgroupOf L with hN'
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπN : N'.map π = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨l, rfl⟩ := hπs q
    obtain ⟨b, hb, hlb⟩ := hcov l l.2
    obtain ⟨b', hb', rfl⟩ := hb
    refine ⟨l * b', Subgroup.mem_subgroupOf.mpr ⟨(l * b').2, hlb⟩, ?_⟩
    rw [map_mul, show π b' = 1 from (QuotientGroup.eq_one_iff b').mpr hb', mul_one]
  have hperfL : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = (⊤ : Subgroup ↥L) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hL]
  have hperfQ : ⁅(⊤ : Subgroup (↥L ⧸ CFSG.Open.pCore 2 ↥L)),
      (⊤ : Subgroup (↥L ⧸ CFSG.Open.pCore 2 ↥L))⁆ = ⊤ := by
    rw [← Subgroup.map_top_of_surjective π hπs, ← Subgroup.map_commutator, hperfL]
  rw [map_perfectCore, hπN, perfectCore_eq_self_of_perfect hperfQ]

theorem exists_lXOne_mul {L X₁ : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hcov : ∀ l ∈ L, ∃ b ∈ pCoreOf 2 L, l * b ∈ Subgroup.normalizer (X₁ : Set G)) {l : G}
    (hl : l ∈ L) : ∃ l' ∈ lXOne L X₁, l'⁻¹ * l ∈ pCoreOf 2 L := by
  have hPmap : lXOne L X₁ =
      (perfectCore ((L ⊓ Subgroup.normalizer (X₁ : Set G)).subgroupOf L)).map L.subtype := by
    rw [map_perfectCore L.subtype _, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  obtain ⟨l', hl', hll⟩ : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L) ⟨l, hl⟩ ∈
      (perfectCore ((L ⊓ Subgroup.normalizer (X₁ : Set G)).subgroupOf L)).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)) :=
    (map_perfectCore_eq_top hL hcov) ▸ Subgroup.mem_top _
  have ho2 : l'⁻¹ * ⟨l, hl⟩ ∈ CFSG.Open.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff]
    show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L) (l'⁻¹ * ⟨l, hl⟩) = 1
    rw [map_mul, map_inv, hll, inv_mul_cancel]
  refine ⟨l', hPmap ▸ ⟨l', hl', rfl⟩, ⟨_, ho2, ?_⟩⟩
  simp

theorem mem_lXOne {L X₁ : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hcov : ∀ l ∈ L, ∃ b ∈ pCoreOf 2 L, l * b ∈ Subgroup.normalizer (X₁ : Set G))
    {y : G} (hyN : y ∈ L ⊓ Subgroup.normalizer (X₁ : Set G)) (hy3 : y ^ 3 = 1) :
    y ∈ lXOne L X₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' := (L ⊓ Subgroup.normalizer (X₁ : Set G)).subgroupOf L with hN'
  have hPmap : lXOne L X₁ = (perfectCore N').map L.subtype := by
    rw [map_perfectCore L.subtype _, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L) with hπ
  have hπP : (perfectCore N').map π = ⊤ := map_perfectCore_eq_top hL hcov
  have hyL : y ∈ L := hyN.1
  obtain ⟨l, hl, hly⟩ : π ⟨y, hyL⟩ ∈ (perfectCore N').map π := hπP ▸ Subgroup.mem_top _
  have ho2 : l⁻¹ * ⟨y, hyL⟩ ∈ CFSG.Open.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff]
    show π (l⁻¹ * ⟨y, hyL⟩) = 1
    rw [map_mul, map_inv, hly, inv_mul_cancel]
  have hlN : l ∈ N' := perfectCore_le N' hl
  have hoN : l⁻¹ * ⟨y, hyL⟩ ∈ N' := N'.mul_mem (N'.inv_mem hlN) (Subgroup.mem_subgroupOf.mpr hyN)
  have hoNorm : l⁻¹ * ⟨y, hyL⟩ ∈ Subgroup.normalizer ((perfectCore N' : Subgroup ↥L) : Set ↥L) :=
    normalizer_le_normalizer_perfectCore N' (Subgroup.le_normalizer hoN)
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥L)) ⟨_, ho2⟩
  have hom : (l⁻¹ * ⟨y, hyL⟩) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨l', hl', e⟩ := exists_pow_eq_mul hl hoNorm (2 ^ m)
  rw [mul_inv_cancel_left, hom, mul_one] at e
  have hpow : (⟨y, hyL⟩ : ↥L) ^ 2 ^ m ∈ perfectCore N' := e ▸ hl'
  have hy3' : (⟨y, hyL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  have hmod : (⟨y, hyL⟩ : ↥L) ^ 2 ^ m = ⟨y, hyL⟩ ^ (2 ^ m % 3) := by
    conv_lhs => rw [← Nat.div_add_mod (2 ^ m) 3, pow_add, pow_mul, hy3', one_pow, one_mul]
  have hmod3 : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
    have : 2 ^ m % 3 ≠ 0 := by
      intro h0
      have h3 : 3 ∣ 2 ^ m := Nat.dvd_of_mod_eq_zero h0
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    omega
  have hyP : (⟨y, hyL⟩ : ↥L) ∈ perfectCore N' := by
    rcases hmod3 with h1 | h2
    · rwa [hmod, h1, pow_one] at hpow
    · rw [hmod, h2] at hpow
      have e2 : (⟨y, hyL⟩ : ↥L) = (⟨y, hyL⟩ ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hy3', one_mul, pow_one]
      rw [e2]
      exact Subgroup.pow_mem _ hpow 2
  rw [hPmap]
  exact ⟨_, hyP, rfl⟩

variable {T L I V₁ V₂ X K : Subgroup G}

theorem exists_comm_lXOne (hC : SecS.CartanFacts) (hN : SecA.NatFacts)
    (hG2 : SecA.FactG2DerivedOrder) (hFb : SecA.Facts12b) (h1102 : Stmt11_0_2)
    (h : SecS.StarHyp G T L I V₁ V₂ X K) (hSL3 : KindSL3 L (fsuV T I) 2)
    (hU : conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤ pCoreOf 2 (L ⊔ T))
    {y : G} (hy : y ∈ X ⊓ LOf L V₁) {e : G}
    (he : e ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
      Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G)) (hye : y * e * y⁻¹ ≠ e) :
    ∃ q ∈ pCoreOf 2 (lXOne L (SecA.xOne X (LOf L V₁))),
      ∃ l ∈ lXOne L (SecA.xOne X (LOf L V₁)), l * q * l⁻¹ * q⁻¹ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := (SecS.cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan).1
  have hXN : X ≤ Subgroup.normalizer (LOf L V₁ : Set G) := fun _ hx =>
    SecS.cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan hx
  have hX9 : Nat.card ↥X = 9 := SecS.card_cartan hc hXN
    (SecS.cartan_inf_lOf_inf_sectionCentralizer hN h1102 h.hyp h.v₁ h.cartan)
  have hcomm : IsMulCommutative ↥X :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hX9]; norm_num)
  have hL₁L : LOf L V₁ ≤ L := (perfectCore_le _).trans inf_le_left
  have hyL : y ∈ L := hL₁L hy.2
  have hyC : y ∈ Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have := hcomm.is_comm.comm (⟨x, hx.1⟩ : ↥X) ⟨y, hy.1⟩
    simpa using congrArg Subtype.val this
  have hy3 : y ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(X ⊓ LOf L V₁)) (x := ⟨y, hy⟩)
    rw [hc.card₁] at this
    simpa using congrArg Subtype.val this
  have hSL := SecS.C11AmS.S12.isSL3_four_of h1102 h.hyp hSL3
  have hX₁p : IsPGroup 3 ↥(SecA.xOne X (LOf L V₁)) := IsPGroup.of_card (n := 1) (by
    rw [hc.cardX₁, pow_one])
  have hcov : ∀ l ∈ L, ∃ b ∈ pCoreOf 2 L,
      l * b ∈ Subgroup.normalizer (SecA.xOne X (LOf L V₁) : Set G) := by
    intro l hl
    obtain ⟨b, hb, hlb⟩ := exists_mul_mem_centralizer hX₁p
      (fun x hx => Subgroup.le_normalizer ((h.cartan.1 hx.1).1)) (fun x hx l hl =>
        SecA.C11P9B.commutator_mem_of_isSL3 hFb hN h1102 h.hyp h.v₁ h.v₂ h.cartan hSL hx hl) hl
    exact ⟨b, hb, Subgroup.centralizer_le_normalizer _ hlb⟩
  have hyX : y ∈ lXOne L (SecA.xOne X (LOf L V₁)) :=
    mem_lXOne (SecD.perfect_of_hyp11 h.hyp) hcov
      ⟨hyL, Subgroup.centralizer_le_normalizer _ hyC⟩ hy3
  have hP : IsPGroup 2 ↥(pCoreOf 2 (L ⊔ T)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hLTn : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hyP : y ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    hLTn ((le_sup_left : L ≤ L ⊔ T) hyL)
  have heP : e ∈ pCoreOf 2 (L ⊔ T) := hU he.1
  have hne : y * e * y⁻¹ * e⁻¹ ≠ 1 := fun h1 => hye (mul_inv_eq_one.mp h1)
  have hcP : y * e * y⁻¹ * e⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
    (pCoreOf 2 (L ⊔ T)).mul_mem ((Subgroup.mem_normalizer_iff.mp hyP e).mp heP)
      ((pCoreOf 2 (L ⊔ T)).inv_mem heP)
  have hc' := comm_comm_ne_one hP hy3 hyP heP hne
  have hc'' := comm_comm_ne_one hP hy3 hyP hcP hc'
  have hLLT : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer h.hyp.normal
  have heL : e ∈ Subgroup.normalizer (L : Set G) :=
    hLLT (CFSG.LieType.BorelTits.pCoreOf_le 2 _ heP)
  have hcL : y * e * y⁻¹ * e⁻¹ ∈ L := by
    have h1 : e * y⁻¹ * e⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp heL _).mp (L.inv_mem hyL)
    have e1 : y * e * y⁻¹ * e⁻¹ = y * (e * y⁻¹ * e⁻¹) := by group
    rw [e1]
    exact L.mul_mem hyL h1
  have hcC : y * e * y⁻¹ * e⁻¹ ∈ Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyC he.2) (Subgroup.inv_mem _ hyC))
      (Subgroup.inv_mem _ he.2)
  have hcN : y * e * y⁻¹ * e⁻¹ ∈ Subgroup.normalizer
      ((lXOne L (SecA.xOne X (LOf L V₁)) : Subgroup G) : Set G) :=
    normalizer_le_normalizer_perfectCore _
      (Subgroup.le_normalizer ⟨hcL, Subgroup.centralizer_le_normalizer _ hcC⟩)
  set c := y * e * y⁻¹ * e⁻¹ with hcdef
  have hc'X : y * c * y⁻¹ * c⁻¹ ∈ lXOne L (SecA.xOne X (LOf L V₁)) := by
    have h1 : c * y⁻¹ * c⁻¹ ∈ lXOne L (SecA.xOne X (LOf L V₁)) :=
      (Subgroup.mem_normalizer_iff.mp hcN _).mp (Subgroup.inv_mem _ hyX)
    have e1 : y * c * y⁻¹ * c⁻¹ = y * (c * y⁻¹ * c⁻¹) := by group
    rw [e1]
    exact Subgroup.mul_mem _ hyX h1
  have hc'P : y * c * y⁻¹ * c⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
    (pCoreOf 2 (L ⊔ T)).mul_mem ((Subgroup.mem_normalizer_iff.mp hyP c).mp hcP)
      ((pCoreOf 2 (L ⊔ T)).inv_mem hcP)
  have hXL : lXOne L (SecA.xOne X (LOf L V₁)) ≤ L := (perfectCore_le _).trans inf_le_left
  have hO : pCoreOf 2 (L ⊔ T) ⊓ lXOne L (SecA.xOne X (LOf L V₁)) ≤
      pCoreOf 2 (lXOne L (SecA.xOne X (LOf L V₁))) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (hP.to_le inf_le_left)
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hLTn ((le_sup_left : L ≤ L ⊔ T) (hXL hg)), Subgroup.le_normalizer hg⟩
  exact ⟨_, hO ⟨hc'P, hc'X⟩, y, hyX, hc''⟩

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
