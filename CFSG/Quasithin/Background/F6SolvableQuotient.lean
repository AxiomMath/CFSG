module

public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.Open.SQTKSimpleListTauCeti
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem exists_pow_mem_centralizer_pCore_three {Ĝ : Type*} [Group Ĝ] [Finite Ĝ] (φ : Ĝ →* D)
    (hφ : Function.Surjective φ) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Ĝ) ≤ 2) :
    ∃ k : ℕ, 0 < k ∧ (∀ q : ℕ, q.Prime → q ∣ k → q = 2 ∨ q = 3) ∧
      ∀ g : D, g ^ k ∈ Subgroup.centralizer (Open.pCore 3 D : Set D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO3n : (Open.pCore 3 D).Normal := CFSG.LieType.BorelTits.pCore_normal 3
  have hNn : ((Open.pCore 3 D).comap φ).Normal := hO3n.comap φ
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥((Open.pCore 3 D).comap φ)) := inferInstance
  set N := (Open.pCore 3 D).comap φ
  set P' : Subgroup Ĝ := (P : Subgroup N).map N.subtype
  let ψ : ↥N →* ↥(Open.pCore 3 D) :=
    (φ.comp N.subtype).codRestrict (Open.pCore 3 D) (fun x => x.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨⟨x, hy⟩, rfl⟩
  have himg : ∀ y ∈ Open.pCore 3 D, ∃ x ∈ P', φ x = y := by
    intro y hy
    have htop : IsPGroup 3 (⊤ : Subgroup ↥(Open.pCore 3 D)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 3).of_equiv Subgroup.topEquiv.symm
    have hmax := (P.mapSurjective hψ).is_maximal' htop le_top
    have hmem : (⟨y, hy⟩ : ↥(Open.pCore 3 D)) ∈ ((P.mapSurjective hψ : Subgroup _)) := by
      rw [← hmax]
      exact Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨x, hx, hxy⟩ := hmem
    exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩
  have hsurj : ∀ g : D, ∃ n ∈ Subgroup.normalizer (P' : Set Ĝ), φ n = g := by
    intro g
    obtain ⟨x, rfl⟩ := hφ g
    have hx : x ∈ ((Subgroup.normalizer (P' : Set Ĝ) ⊔ N : Subgroup Ĝ) : Set Ĝ) := by
      rw [Sylow.normalizer_sup_eq_top P]
      exact Subgroup.mem_top x
    rw [Subgroup.mul_normal] at hx
    obtain ⟨n, hn, m, hm, rfl⟩ := hx
    obtain ⟨y, hy, hym⟩ := himg (φ m) hm
    refine ⟨n * y, Subgroup.mul_mem _ hn (Subgroup.le_normalizer hy), ?_⟩
    rw [map_mul, map_mul, hym]
  have hP3 : IsPGroup 3 ↥P' := P.isPGroup'.map N.subtype
  have hrP : CFSG.Open.pRank 3 (⊤ : Subgroup ↥P') ≤ 2 := by
    rw [pRank_top_subtype]
    exact (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_top).trans hr
  refine ⟨Nat.card (MulAut ↥P'), Nat.card_pos,
    fun q hq hqd => prime_dvd_card_aut_of_three hP3 hrP hq hqd, fun g => ?_⟩
  obtain ⟨n, hn, rfl⟩ := hsurj g
  have h1 : P'.normalizerMonoidHom (⟨n, hn⟩ ^ Nat.card (MulAut ↥P')) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one'
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := himg y hy
  have h2 := congrArg (fun a : MulAut ↥P' => ((a ⟨x, hx⟩ : ↥P') : Ĝ)) h1
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply,
    SubmonoidClass.mk_pow] at h2
  have h3 : φ (n ^ Nat.card (MulAut ↥P') * x * (n ^ Nat.card (MulAut ↥P'))⁻¹) = φ x := by
    rw [h2]
  rw [map_mul, map_mul, map_inv, map_pow] at h3
  calc φ x * φ n ^ Nat.card (MulAut ↥P') =
        φ n ^ Nat.card (MulAut ↥P') * φ x * (φ n ^ Nat.card (MulAut ↥P'))⁻¹ *
          φ n ^ Nat.card (MulAut ↥P') := by rw [h3]
    _ = φ n ^ Nat.card (MulAut ↥P') * φ x := by group

omit [Finite D] in
theorem opResidual_normal_of_normal (p : ℕ) {A : Subgroup D} [hA : A.Normal] :
    (opResidual p A).Normal := by
  refine ⟨fun x hx g => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine mem_opResidual_of_coprime (hA.conj_mem y hy.1 g) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy.2
  | one => simp
  | mul y z _ _ ihy ihz =>
    have := (opResidual p A).mul_mem ihy ihz
    simpa [mul_assoc] using this
  | inv y _ ih =>
    have := (opResidual p A).inv_mem ih
    simpa [mul_assoc] using this

omit [Finite D] in
theorem exists_mul_eq_pPart [Finite D] {p : ℕ} (hp : p.Prime) (x : D) :
    ∃ a b : D, a * b = x ∧ Commute a b ∧ (∃ e : ℕ, a ^ p ^ e = 1) ∧
      Nat.Coprime (orderOf b) p ∧ a ∈ Subgroup.zpowers x ∧ b ∈ Subgroup.zpowers x := by
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.one_lt.ne'
  have hcop : Nat.Coprime (p ^ e) m :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  obtain ⟨α, β, hab⟩ : ∃ α β : ℤ, α * (m : ℤ) + β * ((p ^ e : ℕ) : ℤ) = 1 := by
    have := Nat.isCoprime_iff_coprime.mpr hcop.symm
    obtain ⟨u, v, huv⟩ := this
    exact ⟨u, v, huv⟩
  refine ⟨x ^ (α * m), x ^ (β * ((p ^ e : ℕ) : ℤ)), ?_, ?_, ⟨e, ?_⟩, ?_, ?_, ?_⟩
  · rw [← zpow_add, hab, zpow_one]
  · exact Commute.zpow_zpow_self x _ _
  · rw [← zpow_natCast, ← zpow_mul]
    have : α * m * ((p ^ e : ℕ) : ℤ) = α * (orderOf x : ℤ) := by
      rw [he]; push_cast; ring
    rw [this, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · have h1 : (x ^ (β * ((p ^ e : ℕ) : ℤ))) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : β * ((p ^ e : ℕ) : ℤ) * m = β * (orderOf x : ℤ) := by
        rw [he]; push_cast; ring
      rw [this, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem mem_pCoreOf_of_isNilpotent {p : ℕ} [Fact p.Prime] {H : Subgroup D}
    [Group.IsNilpotent H] {x : D} (hx : x ∈ H) {e : ℕ} (he : x ^ p ^ e = 1) :
    x ∈ pCoreOf p H := by
  have h1 : (⟨x, hx⟩ : H) ^ p ^ e = 1 := Subtype.ext (by simpa using he)
  have hz : IsPGroup p (Subgroup.zpowers (⟨x, hx⟩ : H)) := by
    rintro ⟨y, n, rfl⟩
    refine ⟨e, Subtype.ext ?_⟩
    have h2 : ((⟨x, hx⟩ : H) ^ n) ^ p ^ e = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact h2
  obtain ⟨P, hP⟩ := hz.exists_le_sylow
  have hPn : (P : Subgroup H).Normal := inferInstance
  have hle : (P : Subgroup H) ≤ Open.pCore p H := le_pCore p hPn P.isPGroup'
  exact ⟨⟨x, hx⟩, hle (hP (Subgroup.mem_zpowers _)), rfl⟩

theorem exists_pow_coprime_six (z : D) :
    ∃ N : ℕ, 0 < N ∧ (∀ r : ℕ, r.Prime → r ∣ N → r = 2 ∨ r = 3) ∧
      Nat.Coprime (orderOf (z ^ N)) 6 := by
  obtain ⟨a, b, rfl, hab, ⟨e, he⟩, hb, -, -⟩ := exists_mul_eq_pPart Nat.prime_two z
  obtain ⟨c, d, rfl, hcd, ⟨f, hf⟩, hd, -, hdz⟩ := exists_mul_eq_pPart Nat.prime_three b
  refine ⟨2 ^ e * 3 ^ f, by positivity, ?_, ?_⟩
  · intro r hr hrd
    rcases (Nat.Prime.dvd_mul hr).mp hrd with h1 | h1
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h1))
  · have h1 : (a * (c * d)) ^ (2 ^ e * 3 ^ f) = d ^ (2 ^ e * 3 ^ f) := by
      rw [hab.mul_pow, pow_mul a, he, one_pow, one_mul, hcd.mul_pow, mul_comm (2 ^ e),
        pow_mul c, hf, one_pow, one_mul]
    rw [h1]
    have hd2 : Nat.Coprime (orderOf d) 2 :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_mem_zpowers hdz) hb
    exact Nat.Coprime.coprime_dvd_left (orderOf_pow_dvd _)
      (by rw [show (6 : ℕ) = 2 * 3 by norm_num]; exact Nat.Coprime.mul_right hd2 hd)

omit [Finite D] in
@[expose] def coprimeSixPart (Z : Subgroup D) (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) :
    Subgroup D where
  carrier := {z | z ∈ Z ∧ Nat.Coprime (orderOf z) 6}
  mul_mem' := by
    rintro a b ⟨ha, ha6⟩ ⟨hb, hb6⟩
    refine ⟨Z.mul_mem ha hb, ?_⟩
    have hc : Commute a b := hZ a ha b hb
    exact Nat.Coprime.coprime_dvd_left hc.orderOf_mul_dvd_mul_orderOf (Nat.Coprime.mul_left ha6 hb6)
  one_mem' := ⟨Z.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha6⟩
    exact ⟨Z.inv_mem ha, by rwa [orderOf_inv]⟩

omit [Finite D] in
theorem mem_coprimeSixPart {Z : Subgroup D} {hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a} {z : D} :
    z ∈ coprimeSixPart Z hZ ↔ z ∈ Z ∧ Nat.Coprime (orderOf z) 6 := Iff.rfl

theorem prime_eq_two_or_three_of_pow_mem_centralizer (h : IsGoldschmidtTriple G₁ G₂)
    (hsolv : Group.IsSolvable D) {k : ℕ} (hk0 : 0 < k)
    (hk : ∀ q : ℕ, q.Prime → q ∣ k → q = 2 ∨ q = 3)
    (hkc : ∀ g : D, g ^ k ∈ Subgroup.centralizer (Open.pCore 3 D : Set D))
    (hL : twoResidual G₁ ≤
      Subgroup.centralizer (opResidual 3 (genFittingFitting D) : Set D))
    {q : ℕ} (hq : q.Prime) (hqd : q ∣ Nat.card D) : q = 2 ∨ q = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFn : (genFittingFitting D).Normal := CFSG.fittingSubgroup_normal
  have hFnil : Group.IsNilpotent ↥(genFittingFitting D) := CFSG.fittingSubgroup_nilpotent
  have hF'n : (opResidual 3 (genFittingFitting D)).Normal := opResidual_normal_of_normal 3
  set F := genFittingFitting D with hFdef
  set F' := opResidual 3 F with hF'def
  set X := Subgroup.centralizer (F' : Set D) with hXdef
  have hXn : X.Normal := Subgroup.normal_centralizer
  have hF3 : ∀ a ∈ F, (∃ e : ℕ, a ^ 3 ^ e = 1) → a ∈ Open.pCore 3 D := by
    rintro a ha ⟨e, he⟩
    have h1 : a ∈ pCoreOf 3 F := mem_pCoreOf_of_isNilpotent ha he
    have h2 : pCoreOf 3 F ≤ Open.pCore 3 D := by
      refine le_pCore 3 ?_ (pCoreOf_isPGroup 3 F)
      rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff]
      exact (Subgroup.normalizer_eq_top_iff.mpr hFn).ge.trans
        (normalizer_le_normalizer_pCoreOf 3 F)
    exact h2 h1
  have hcF : ∀ x : D, x ∈ X → x ∈ Subgroup.centralizer (Open.pCore 3 D : Set D) → x ∈ F := by
    intro x hxX hx3
    apply centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    obtain ⟨a, b, rfl, -, ha, hb, haz, hbz⟩ := exists_mul_eq_pPart Nat.prime_three f
    have haF : a ∈ F := (Subgroup.zpowers_le.mpr hf) haz
    have hbF : b ∈ F := (Subgroup.zpowers_le.mpr hf) hbz
    have hb' : b ∈ F' := mem_opResidual_of_coprime hbF hb
    have ha' : a ∈ Open.pCore 3 D := hF3 a haF ha
    rw [Subgroup.mem_centralizer_iff] at hxX hx3
    rw [mul_assoc, hxX b hb', ← mul_assoc, hx3 a ha', mul_assoc]
  have hZc : ∀ a ∈ X ⊓ Subgroup.centralizer (X : Set D), ∀ b ∈ X ⊓ Subgroup.centralizer
      (X : Set D), a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp hb.2 a ha.1)
  set R := coprimeSixPart (X ⊓ Subgroup.centralizer (X : Set D)) hZc with hRdef
  have hRX : R ≤ X := fun z hz => hz.1.1
  have hRn : R.Normal := by
    refine ⟨fun z hz g => ?_⟩
    rw [mem_coprimeSixPart, Subgroup.mem_inf]
    refine ⟨⟨hXn.conj_mem z hz.1.1 g, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : g⁻¹ * y * g ∈ X := by
        have := hXn.conj_mem y hy g⁻¹
        simpa [mul_assoc] using this
      have hc := Subgroup.mem_centralizer_iff.mp hz.1.2 _ hy'
      calc y * (g * z * g⁻¹) = g * (g⁻¹ * y * g * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
        _ = g * z * g⁻¹ * y := by group
    · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hz.2
  have hXR : ∀ x ∈ X, ∃ M : ℕ, 0 < M ∧ (∀ r : ℕ, r.Prime → r ∣ M → r = 2 ∨ r = 3) ∧
      x ^ M ∈ R := by
    intro x hx
    have hxk : x ^ k ∈ F := hcF _ (X.pow_mem hx k) (hkc x)
    obtain ⟨a, b, hab, hcomm, ⟨e, he⟩, hb, -, hbz⟩ := exists_mul_eq_pPart Nat.prime_three (x ^ k)
    have hpow : x ^ (k * 3 ^ e) = b ^ 3 ^ e := by
      rw [pow_mul, ← hab, hcomm.mul_pow, he, one_mul]
    have hbF : b ∈ F := (Subgroup.zpowers_le.mpr hxk) hbz
    have hbX : b ∈ X := (Subgroup.zpowers_le.mpr (X.pow_mem hx k)) hbz
    have hb' : b ^ 3 ^ e ∈ F' := F'.pow_mem (mem_opResidual_of_coprime hbF hb) _
    have hZ : b ^ 3 ^ e ∈ X ⊓ Subgroup.centralizer (X : Set D) := by
      rw [Subgroup.mem_inf]
      refine ⟨X.pow_mem hbX _, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((Subgroup.mem_centralizer_iff.mp hy) _ hb').symm
    obtain ⟨N, hN0, hN, hN6⟩ := exists_pow_coprime_six (b ^ 3 ^ e)
    refine ⟨k * 3 ^ e * N, Nat.mul_pos (Nat.mul_pos hk0 (by positivity)) hN0, ?_, ?_⟩
    · intro r hr hrd
      rcases (Nat.Prime.dvd_mul hr).mp hrd with h1 | h1
      · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
        · exact hk r hr h2
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
            (hr.dvd_of_dvd_pow h2))
      · exact hN r hr h1
    · rw [pow_mul, hpow]
      exact ⟨Subgroup.pow_mem _ hZ _, hN6⟩
  set N : Subgroup ↥X := R.subgroupOf X with hNdef
  have hNn : N.Normal := Subgroup.Normal.subgroupOf hRn X
  have hNcop : ∀ r : ℕ, r.Prime → r ∣ Nat.card N → r ≠ 2 ∧ r ≠ 3 := by
    intro r hr hrd
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' r hrd
    have h6 : Nat.Coprime (orderOf (((n : ↥X) : D))) 6 := (Subgroup.mem_subgroupOf.mp n.2).2
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hn] at h6
    constructor <;> rintro rfl <;> norm_num at h6
  have hidx : ∀ r : ℕ, r.Prime → r ∣ N.index → r = 2 ∨ r = 3 := by
    intro r hr hrd
    have : Fact r.Prime := ⟨hr⟩
    rw [Subgroup.index_eq_card] at hrd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hrd
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨M, -, hM, hxM⟩ := hXR x x.2
    have hpow : (x : ↥X ⧸ N) ^ M = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hxM
    have := orderOf_dvd_of_pow_eq_one hpow
    rw [hy] at this
    exact hM r hr this
  have hcop : Nat.Coprime (Nat.card N) N.index := Nat.coprime_of_dvd fun r hr h1 h2 => by
    rcases hidx r hr h2 with rfl | rfl
    · exact (hNcop 2 hr h1).1 rfl
    · exact (hNcop 3 hr h1).2 rfl
  obtain ⟨H, hH⟩ := Subgroup.exists_left_complement'_of_coprime hcop
  have hHcard : Nat.card H = N.index := hH.index_eq_card.symm
  have hH23 : ∀ a ∈ H, ∀ r : ℕ, r.Prime → r ∣ orderOf a → r = 2 ∨ r = 3 := fun a ha r hr hrd =>
    hidx r hr (hHcard ▸ hrd.trans (Subgroup.orderOf_dvd_natCard H ha))
  have hKmem : ∀ x : ↥X, (∀ r : ℕ, r.Prime → r ∣ orderOf x → r = 2 ∨ r = 3) → x ∈ H := by
    intro x hx
    obtain ⟨⟨⟨a, ha⟩, ⟨n, hn⟩⟩, hxa, -⟩ := (Subgroup.isComplement'_def.mp hH).existsUnique x
    simp only at hxa
    have hnZ : ((n : ↥X) : D) ∈ Subgroup.centralizer (X : Set D) :=
      (Subgroup.mem_subgroupOf.mp hn).1.2
    have hcomm : Commute a n := Subtype.ext (Subgroup.mem_centralizer_iff.mp hnZ a a.2)
    have hn6 : Nat.Coprime (orderOf n) 6 := by
      have := (Subgroup.mem_subgroupOf.mp hn).2
      rwa [Subgroup.orderOf_coe] at this
    have hcop' : Nat.Coprime (orderOf a) (orderOf n) := Nat.coprime_of_dvd fun r hr h1 h2 => by
      have h6 : r ∣ 6 := by rcases hH23 a ha r hr h1 with rfl | rfl <;> norm_num
      exact hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hn6) h6)
    have hord := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop'
    rw [hxa] at hord
    have hn1 : orderOf n = 1 := by
      by_contra hne
      obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
      have h1 : r ∣ orderOf x := hord ▸ dvd_mul_of_dvd_right hrd _
      have h6 : r ∣ 6 := by rcases hx r hr h1 with rfl | rfl <;> norm_num
      exact hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hrd hn6) h6)
    rw [orderOf_eq_one_iff] at hn1
    rw [← hxa, hn1, mul_one]
    exact ha
  set K := H.map X.subtype with hKdef
  have hKcard : Nat.card K = N.index := by
    rw [← hHcard]
    exact Nat.card_congr (H.equivMapOfInjective _ X.subtype_injective).toEquiv.symm
  have hKmem' : ∀ y ∈ X, (∀ r : ℕ, r.Prime → r ∣ orderOf y → r = 2 ∨ r = 3) → y ∈ K :=
    fun y hy hy23 => ⟨⟨y, hy⟩, hKmem ⟨y, hy⟩ (by rwa [Subgroup.orderOf_mk]), rfl⟩
  have hKn : K.Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨a, ha, rfl⟩ := hy
    refine hKmem' _ (hXn.conj_mem _ a.2 g) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    simpa [Subgroup.orderOf_coe] using hH23 a ha
  have hLK : twoResidual G₁ ≤ K := by
    rw [twoResidual_eq_oTwoUpper]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hxL : x ∈ twoResidual G₁ := mem_twoResidual_of_odd hx.1 hx.2
    refine hKmem' x (hL hxL) fun r hr hrd => ?_
    have h3 := orderOf_dvd_three_of_odd h hx.1 hx.2
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hrd.trans h3))
  have htop : G₂ ⊔ K = ⊤ := by
    refine top_le_iff.mp (h.gen ▸ sup_le ?_ le_sup_left)
    rw [← inf_sup_twoResidual_left h]
    exact sup_le (inf_le_right.trans le_sup_left) (hLK.trans le_sup_right)
  have hcardD : Nat.card D = K.relIndex G₂ * Nat.card K := by
    have h1 := Subgroup.relIndex_mul_card (H := K) (K := G₂ ⊔ K)
    rw [inf_eq_left.mpr le_sup_right, Subgroup.relIndex_sup_right, htop] at h1
    rw [h1, Subgroup.card_top]
  rw [hcardD] at hqd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h1 | h1
  · have h2 : q ∣ Nat.card G₂ := h1.trans (Subgroup.index_dvd_card _)
    obtain ⟨a, ha⟩ := exists_card_inf_eq h
    rw [card_right h, ha] at h2
    rcases (Nat.Prime.dvd_mul hq).mp h2 with h3 | h3
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3)
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h3))
  · exact hidx q hq (hKcard ▸ h1)

theorem prime_eq_two_or_three_of_pRank_le_two (h : IsGoldschmidtTriple G₁ G₂)
    (hsolv : Group.IsSolvable D) {Ĝ : Type*} [Group Ĝ] [Finite Ĝ] (φ : Ĝ →* D)
    (hφ : Function.Surjective φ) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Ĝ) ≤ 2)
    (hL : twoResidual G₁ ≤ Subgroup.centralizer (opResidual 3 (genFittingFitting D) : Set D) ∨
      twoResidual G₂ ≤ Subgroup.centralizer (opResidual 3 (genFittingFitting D) : Set D))
    {q : ℕ} (hq : q.Prime) (hqd : q ∣ Nat.card D) : q = 2 ∨ q = 3 := by
  obtain ⟨k, hk0, hk, hkc⟩ := exists_pow_mem_centralizer_pCore_three φ hφ hr
  rcases hL with hL | hL
  · exact prime_eq_two_or_three_of_pow_mem_centralizer h hsolv hk0 hk hkc hL hq hqd
  · exact prime_eq_two_or_three_of_pow_mem_centralizer h.symm hsolv hk0 hk hkc hL hq hqd

theorem prime_eq_two_or_three_of_sqtk (h : IsGoldschmidtTriple G₁ G₂)
    (hsolv : Group.IsSolvable D)
    (hD : ∃ (Ĝ : Type) (_ : Group Ĝ) (_ : Finite Ĝ) (φ : Ĝ →* D), Function.Surjective φ ∧
      SQTKTauCeti.StronglyQuasithin Ĝ ∧ CFSG.SectionRank.IsKGroupCat Ĝ)
    (hL : twoResidual G₁ ≤ Subgroup.centralizer (opResidual 3 (genFittingFitting D) : Set D) ∨
      twoResidual G₂ ≤ Subgroup.centralizer (opResidual 3 (genFittingFitting D) : Set D))
    {q : ℕ} (hq : q.Prime) (hqd : q ∣ Nat.card D) : q = 2 ∨ q = 3 := by
  obtain ⟨Ĝ, _, _, φ, hφ, hSQT, -⟩ := hD
  exact prime_eq_two_or_three_of_pRank_le_two h hsolv φ hφ
    (hSQT 3 Nat.prime_three (by norm_num)) hL hq hqd

end F6

end CFSG.Quasithin
