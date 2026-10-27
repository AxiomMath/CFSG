module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldFix
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSU
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalUField

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff gramSU unitarySU_eq_gramSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryPlane (ordNegQ)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace OrdPFieldNsU

section Descent

variable {K : Type} [Field K]

theorem exists_unitaryFieldData_fixed {f : ℕ} (h : UnitaryFieldData 2 f K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {θ : K ≃+* K} (hθ : orderOf θ = p) :
    ∃ f₀ : ℕ, f = p * f₀ ∧
      UnitaryFieldData 2 f₀ (FixedPoints.subfield (Subgroup.zpowers θ) K) := by
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := OrdPFieldNs.card_eq_card_fixed_pow hθ
  have : Fintype (FixedPoints.subfield (Subgroup.zpowers θ) K) := Fintype.ofFinite _
  obtain ⟨m, -, hm⟩ := FiniteField.card (FixedPoints.subfield (Subgroup.zpowers θ) K) 2
  rw [Nat.card_eq_fintype_card (α := FixedPoints.subfield (Subgroup.zpowers θ) K), hm, h.card,
    ← pow_mul] at hcard
  have hmp : 2 * f = (m : ℕ) * p := Nat.pow_right_injective le_rfl hcard
  have hpf : p ∣ f := by
    have h1 : p ∣ 2 * f := ⟨m, by rw [hmp, mul_comm]⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) h1
  obtain ⟨f₀, rfl⟩ := hpf
  have hm2 : (m : ℕ) = 2 * f₀ := by
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    rw [← hmp]
    ring
  refine ⟨f₀, rfl, ⟨Nat.prime_two, ?_, ?_⟩⟩
  · rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · have h1 := h.one_le
      rw [h0, mul_zero] at h1
      omega
    · exact h0
  · rw [Nat.card_eq_fintype_card, hm, hm2]

theorem bar_coe {K₀ : Type} [Field K₀] {p f₀ : ℕ} (h : UnitaryFieldData 2 (p * f₀) K)
    (h₀ : UnitaryFieldData 2 f₀ K₀) (hp : Odd p) (ι : K₀ →+* K) (a : K₀) :
    h.bar (ι a) = ι (h₀.bar a) := by
  have : Finite K₀ := h₀.finite
  have : Fintype K₀ := Fintype.ofFinite K₀
  have hc : Fintype.card K₀ = 2 ^ (2 * f₀) := by rw [← Nat.card_eq_fintype_card, h₀.card]
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, ← map_pow]
  congr 1
  obtain ⟨k, rfl⟩ := hp
  have he : 2 ^ ((2 * k + 1) * f₀) = Fintype.card K₀ ^ k * 2 ^ f₀ := by
    rw [hc, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [he, pow_mul, FiniteField.pow_card_pow]

theorem mem_unitarySU_map_iff {K₀ : Type} [Field K₀] {f f₀ : ℕ} (h : UnitaryFieldData 2 f K)
    (h₀ : UnitaryFieldData 2 f₀ K₀) (ι : K₀ →+* K) (hbar : ∀ a, h.bar (ι a) = ι (h₀.bar a))
    {n : ℕ} (x : GL (Fin n) K₀) :
    Matrix.GeneralLinearGroup.map ι x ∈ unitarySU 2 f K n ↔ x ∈ unitarySU 2 f₀ K₀ n := by
  rw [mem_unitarySU_iff h, mem_unitarySU_iff h₀]
  have hc : ((Matrix.GeneralLinearGroup.map ι x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (x : Matrix (Fin n) (Fin n) K₀).map ι := rfl
  have hb : ((x : Matrix (Fin n) (Fin n) K₀).map ι).map h.bar =
      ((x : Matrix (Fin n) (Fin n) K₀).map h₀.bar).map ι := by
    ext i j
    exact hbar _
  have he : (((x : Matrix (Fin n) (Fin n) K₀).map h₀.bar)ᵀ *
      (x : Matrix (Fin n) (Fin n) K₀)).map ι =
      (((x : Matrix (Fin n) (Fin n) K₀).map ι).map h.bar)ᵀ *
        (x : Matrix (Fin n) (Fin n) K₀).map ι := by
    rw [Matrix.map_mul, Matrix.transpose_map, hb]
  have hdet : ((x : Matrix (Fin n) (Fin n) K₀).map ι).det = ι (x : Matrix (Fin n) (Fin n) K₀).det :=
    (RingHom.map_det ι _).symm
  have h1 : (1 : Matrix (Fin n) (Fin n) K) = (1 : Matrix (Fin n) (Fin n) K₀).map ι :=
    (Matrix.map_one _ (map_zero ι) (map_one ι)).symm
  rw [hc, hdet, ← he, h1]
  exact Iff.and (map_eq_one_iff ι ι.injective) (Matrix.map_injective ι.injective).eq_iff

end Descent

section Fixed

variable {f n : ℕ} {K : Type} [Field K]

theorem exists_fixed_elemAb (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ f + 1) {θ : K ≃+* K} (hθ : orderOf θ = p)
    (hpS : p ∣ Nat.card ↥(unitarySU 2 f K n)) :
    ∃ E : Subgroup ↥(unitarySU 2 f K n), (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a ^ p = 1) ∧ (∀ a ∈ E, glAut θ (a : GL (Fin n) K) = a) ∧
      p ^ (n / ordNegQ 2 f p) ≤ Nat.card E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := h.finite
  obtain ⟨f₀, hf₀, h₀⟩ := exists_unitaryFieldData_fixed h hp hp2 hθ
  set K₀ := FixedPoints.subfield (Subgroup.zpowers θ) K with hK₀
  set ι : K₀ →+* K := K₀.subtype with hι
  have hbar : ∀ a : K₀, h.bar (ι a) = ι (h₀.bar a) := by
    subst hf₀
    exact bar_coe h h₀ (hp.odd_of_ne_two hp2) ι
  have hιinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) ι) := by
    intro a b hab
    apply Units.ext
    exact Matrix.map_injective Subtype.val_injective
      (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hab)
  have hz : (2 : ZMod p) ^ f = 2 ^ f₀ := by rw [hf₀, mul_comm, pow_mul, ZMod.pow_card]
  have hpq₀ : ¬ p ∣ 2 ^ f₀ + 1 := by
    intro hd
    apply hpq
    rw [← ZMod.natCast_eq_zero_iff] at hd ⊢
    push_cast at hd ⊢
    rw [hz]
    exact hd
  have he : ordNegQ 2 f₀ p = ordNegQ 2 f p := by
    simp only [ordNegQ, Nat.cast_ofNat, hz]
  have hΦp : (glAut θ : MulAut (GL (Fin n) K)) ^ p = 1 := by
    rw [← map_pow, ← hθ, pow_orderOf_eq_one, map_one]
  have hΦS : ∀ g ∈ unitarySU 2 f K n, glAut θ g ∈ unitarySU 2 f K n := by
    intro g hg
    rw [unitarySU_eq_gramSU h] at hg ⊢
    exact glAut_mem_gramSU h isPrimeFormGram_one θ hg
  obtain ⟨x, hxS, hxo, hxθ⟩ :=
    OrdPFieldNs.exists_orderOf_eq_fixed_of_le (S := unitarySU 2 f K n) (v := 1) hp (glAut θ)
      (by rwa [pow_one]) hΦS hpS
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have hxσ : Matrix.GeneralLinearGroup.map (θ : K →+* K) x = x := by
    apply Units.ext
    have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hxθ
    simp only [coe_glAut] at h1
    exact h1
  obtain ⟨x₀, hx₀⟩ := OrdPFieldNs.exists_gl_map_eq x hxσ
  have hx₀S : x₀ ∈ unitarySU 2 f₀ K₀ n := (mem_unitarySU_map_iff h h₀ ι hbar x₀).mp (hx₀ ▸ hxS)
  set u₀ : ↥(unitarySU 2 f₀ K₀ n) := ⟨x₀, hx₀S⟩ with hu₀def
  have hu₀p : u₀ ^ p = 1 := by
    apply Subtype.ext
    apply hιinj
    rw [Subgroup.coe_pow, map_pow, OneMemClass.coe_one, map_one]
    change (Matrix.GeneralLinearGroup.map ι x₀) ^ p = 1
    rw [hx₀, hxp]
  have hu₀1 : u₀ ≠ 1 := by
    intro h1
    have h2 : x₀ = 1 := congrArg Subtype.val h1
    rw [h2, map_one] at hx₀
    rw [← hx₀, orderOf_one] at hxo
    exact hp.one_lt.ne hxo
  obtain ⟨E₀, hE₀, hu₀E⟩ := OrdPNsU.exists_maxElemAb_mem h₀ hp hp2 hpq₀ hu₀p
  have hcard₀ := OrdPNsU.pow_ordNegQ_le_card h₀ hE₀ ⟨u₀, hu₀E, hu₀1⟩
  rw [he] at hcard₀
  have hmem : ∀ g : ↥(unitarySU 2 f₀ K₀ n),
      Matrix.GeneralLinearGroup.map ι (g : GL (Fin n) K₀) ∈ unitarySU 2 f K n :=
    fun g => (mem_unitarySU_map_iff h h₀ ι hbar _).mpr g.2
  set κ : ↥(unitarySU 2 f₀ K₀ n) →* ↥(unitarySU 2 f K n) :=
    MonoidHom.codRestrict ((Matrix.GeneralLinearGroup.map ι).comp (unitarySU 2 f₀ K₀ n).subtype)
      _ hmem with hκdef
  have hκ : ∀ g, ((κ g : ↥(unitarySU 2 f K n)) : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.map ι (g : GL (Fin n) K₀) := fun g => rfl
  have hκinj : Function.Injective κ := by
    intro a b hab
    have h1 := congrArg (fun z : ↥(unitarySU 2 f K n) => (z : GL (Fin n) K)) hab
    simp only [hκ] at h1
    exact Subtype.ext (hιinj h1)
  refine ⟨E₀.map κ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hE₀.comm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE₀.pow a ha, map_one]
  · rintro _ ⟨a, -, rfl⟩
    apply Units.ext
    rw [coe_glAut, hκ]
    exact congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
      (OrdPFieldNs.gl_map_fixed (a : GL (Fin n) K₀))
  · rw [Subgroup.card_map_of_injective hκinj]
    exact hcard₀

end Fixed

section Setting

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

include hF in
theorem eq_one_of_frame {G : Type} [Group G] {p : ℕ} (hf : 1 ≤ f) (hp : p.Prime)
    (hpq : ¬ p ∣ 2 ^ f + 1) (hn : 4 ≤ n) {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(SU (unitaryInvolution F 2 f) n)) {P₀ : GL (Fin n) F}
    (hP₀ : conjTr (unitaryInvolution F 2 f) (P₀ : Matrix (Fin n) (Fin n) F) *
      (P₀ : Matrix (Fin n) (Fin n) F) = antidiag n)
    (z : ↥(unitarySU 2 f F n)) (hz : SURep.ggFrameU hF ψ P₀ hP₀ z = 1) (hzp : z ^ p = 1) :
    z = 1 := by
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hn3 : 3 ≤ n := by omega
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have hker₁ := SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker
  obtain ⟨e, he⟩ := SURep.ggFrameKer_of_ker_le_center hF hn3 hnq hker₁ z hz
  obtain ⟨-, huni⟩ := (mem_unitarySU_iff h).mp z.2
  rw [he, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at huni
  have hbar := congrFun (Matrix.diagonal_injective huni) ⟨0, by omega⟩
  simp only [UnitaryFieldData.bar_apply] at hbar
  have heq : e ^ (2 ^ f + 1) = 1 := by rw [pow_succ]; exact hbar
  have hep : e ^ p = 1 := by
    have h1 := congrArg (fun g : ↥(unitarySU 2 f F n) =>
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hzp
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, he, ← map_pow, OneMemClass.coe_one,
      Units.val_one] at h1
    have h2 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa [Matrix.scalar_apply] using h2
  have he1 : e = 1 := by
    have h1 := pow_gcd_eq_one.mpr ⟨hep, heq⟩
    rwa [((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq).gcd_eq_one, pow_one] at h1
  apply Subtype.ext
  apply Units.ext
  rw [he, he1, map_one]
  rfl

include hF in
theorem card_bstar_le {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} (hf : 1 ≤ f)
    {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hS : GGSixFusionSetting p Bs G₀ (Unitary.rootDatum hF n) .PSU n f ψ)
    (hpq : ¬ p ∣ 2 ^ f + 1) : Nat.card Bs ≤ p ^ (n / ordNegQ 2 f p) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hrk : 2 ≤ n / 2 := hrank
  have hn : 4 ≤ n := by omega
  have hpp := hS.prime
  have hp2 := hS.ne_two
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hcop : Nat.Coprime p (Nat.gcd n (2 ^ f + 1)) :=
    (Nat.Prime.coprime_iff_not_dvd hpp).mpr fun hd => hpq (hd.trans (Nat.gcd_dvd_right _ _))
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
  set φ := SURep.ggFrameU hF ψ P₀ hP₀ with hφ
  have hnp : ∀ z : ↥(unitarySU 2 f F n), φ z = 1 → z ^ p = 1 → z = 1 :=
    fun z hz hzp => eq_one_of_frame hF hf hpp hpq hn hker hP₀ z hz hzp
  have hBsφ : Bs ≤ φ.range := fun b hb => by
    obtain ⟨s, hs, -⟩ := OrdPInnerSU.exists_eq_frame_of_innerDiag hF hf hn hker hC hP₀ hcop
      (hS.innerDiag b hb) (hS.elem.2 b hb)
    exact ⟨s, hs⟩
  have hAb : IsElemAbelian p (Bs.subgroupOf φ.range) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
    · exact TableB.IsElemAbelian.comm hS.elem (Subgroup.mem_subgroupOf.mp a.2)
        (Subgroup.mem_subgroupOf.mp b.2)
    · simpa using hS.elem.2 _ (Subgroup.mem_subgroupOf.mp ha)
  have hnp' : ∀ z ∈ φ.rangeRestrict.ker, z ^ p = 1 → z = 1 := fun z hz hzp => by
    rw [MonoidHom.ker_rangeRestrict] at hz
    exact hnp z hz hzp
  obtain ⟨A, hAmap, -, hA, hAcard⟩ := TableBUE.exists_lift_of_noTorsion φ.rangeRestrict
    φ.rangeRestrict_surjective hpp hnp' hAb
  have hlift : ∀ b ∈ Bs, ∃ a ∈ A, φ a = b := by
    intro b hb
    have hb' : (⟨b, hBsφ hb⟩ : φ.range) ∈ Bs.subgroupOf φ.range := Subgroup.mem_subgroupOf.mpr hb
    rw [← hAmap] at hb'
    obtain ⟨a, ha, hae⟩ := hb'
    exact ⟨a, ha, congrArg Subtype.val hae⟩
  have hAmax : SUTB.MaxElemAb p A := by
    refine ⟨hpp, hp2, hpq, fun a ha => hA.2 a ha,
      fun a ha b hb => TableB.IsElemAbelian.comm hA ha hb, fun g hgp hgA => ?_⟩
    have hgc : φ g ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨a, haA, rfl⟩ := hlift b hb
      rw [← map_mul, ← map_mul, hgA a haA]
    have hgB : φ g ∈ Bs := hS.omega _ hgc (by rw [← map_pow, hgp, map_one])
    obtain ⟨a, haA, hag⟩ := hlift _ hgB
    have h1 : a⁻¹ * g = 1 := by
      refine hnp _ (by rw [map_mul, map_inv, hag, inv_mul_cancel]) ?_
      have hcomm : Commute a⁻¹ g := (show Commute g a from hgA a haA).symm.inv_left
      rw [hcomm.mul_pow, inv_pow, hA.2 a haA, hgp, inv_one, one_mul]
    rw [← inv_mul_eq_one.mp h1]
    exact haA
  have hAcard' : Nat.card A = Nat.card Bs := by
    rw [hAcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsφ).toEquiv
  rw [← hAcard']
  exact OrdPNsU.card_le_pow_ordNegQ h hAmax

include hF in
theorem exists_conj_mem_centralizer_nonsplit {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} (hf : 1 ≤ f) {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hS : GGSixFusionSetting p Bs G₀ (Unitary.rootDatum hF n) .PSU n f ψ)
    (hpq : ¬ p ∣ 2 ^ f + 1) {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G))
    (hyp : y ^ p = 1) (hyI : ¬ GGPsiInnerDiag (Unitary.rootDatum hF n) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hrk : 2 ≤ n / 2 := hrank
  have hn : 4 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have hpp := hS.prime
  have hp2 := hS.ne_two
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hcop : Nat.Coprime p (Nat.gcd n (2 ^ f + 1)) :=
    (Nat.Prime.coprime_iff_not_dvd hpp).mpr fun hd => hpq (hd.trans (Nat.gcd_dvd_right _ _))
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
  set φ := SURep.ggFrameU hF ψ P₀ hP₀ with hφ
  have hrφ : φ.range = G₀ := (SURep.range_ggFrameU hF ψ P₀ hP₀).trans hrange
  have hker₁ : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f F n) :=
    SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker
  have hC₁ : Subgroup.centralizer (φ.range : Set G) = ⊥ := by
    rw [hrφ]
    exact hS.centralizer_eq_bot
  set π := OrdPFieldSU.projP h hn1 with hπdef
  have hk : π.ker = φ.ker := by
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hπdef, OrdPFieldSU.projP_eq_one_iff]
    constructor
    · rintro ⟨c, hc⟩
      have hz : φ z ∈ Subgroup.centralizer (φ.range : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨u, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← hc, TypeA.PGLTor.scalar_mul_comm]
      rw [hC₁, Subgroup.mem_bot] at hz
      exact hz
    · intro hz
      obtain ⟨e, he⟩ := SURep.ggFrameKer_of_ker_le_center hF hn3 hnq hker₁ z hz
      have he0 : e ≠ 0 := by
        rintro rfl
        have h1 := (z : GL (Fin n) F).det_ne_zero
        rw [he, map_zero, det_zero] at h1
        exact h1 rfl
      refine ⟨Units.mk0 e he0, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, he, Units.val_mk0]
  set Θ := AutSt.modelEquiv φ π (OrdPFieldSU.projP_surjective h hn1) hk with hΘdef
  have hΘ : ∀ x, ((Θ (π x) : φ.range) : G) = φ x :=
    AutSt.modelEquiv_apply φ π (OrdPFieldSU.projP_surjective h hn1) hk
  have hyM' : y ∈ Subgroup.normalizer (φ.range : Set G) := by
    rw [hrφ]
    exact hyM
  set a : MulAut φ.range := φ.range.normalizerMonoidHom ⟨y⁻¹, inv_mem hyM'⟩ with hadef
  have ha : ∀ x : φ.range, ((a x : φ.range) : G) = y⁻¹ * x * y :=
    OrdPGraph.normalizerMonoidHom_inv_apply hyM'
  have hap : a ^ p = 1 := by
    rw [hadef, ← map_pow]
    have e : (⟨y⁻¹, inv_mem hyM'⟩ : Subgroup.normalizer (φ.range : Set G)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, inv_pow, hyp, inv_one]; rfl)
    rw [e, map_one]
  set β : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    MulAut.congr Θ.symm a with hβdef
  have hβ : ∀ x, Θ (β x) = a (Θ x) := fun x => by
    rw [hβdef, MulAut.congr_apply]
    simp
  have hβp : β ^ p = 1 := by
    rw [hβdef, ← map_pow, hap, map_one]
  have hrel : ∀ x x' : ↥(unitarySU 2 f F n), β (π x) = π x' → y⁻¹ * φ x * y = φ x' := by
    intro x x' hxx'
    have e := congrArg (fun z => ((Θ z : φ.range) : G)) hxx'
    simp only [hβ, ha, hΘ] at e
    exact e
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) F) := isPrimeFormGram_one
  obtain ⟨⟨A, θ⟩, hAθ⟩ := primeFormPsi_surjective h hC1 hn3 hq β
  rw [primeFormPsi_apply] at hAθ
  have hθ1 : θ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hAθ
    apply hyI
    have hpair : (y⁻¹, (A : GL (Fin n) F)) ∈ SUTorus.suPairs φ := by
      refine ⟨SUTorus.mem_normalizer_of_mem_primeFormUnitary h A.2, fun u v hv => ?_⟩
      rw [inv_inv]
      refine hrel u v ?_
      rw [← hAθ, hπdef, OrdPFieldSU.projP_apply h hn1 u (OrdPFieldSU.mem_gramSU_one h u),
        primeFormConjHom_mk, OrdPFieldSU.projP_apply h hn1 v (OrdPFieldSU.mem_gramSU_one h v)]
      congr 1
      apply Subtype.ext
      exact hv.symm
    obtain ⟨s, hs, -⟩ := OrdPInnerSU.exists_eq_of_mem_suPairs h hn hker₁ hC₁ hcop A.2 hpair hyp
    refine ⟨y⁻¹, ψ.range.inv_mem ⟨_, hs⟩, fun γ _ => ⟨1, one_mem _, fun z _ => ?_⟩⟩
    simp
  obtain ⟨hθo, H, hH⟩ := RecipeFieldSpU.primeForm_conj_of_pow_eq_one h hn3 hq hpp hp2 A θ hθ1
    (by rw [hAθ]; exact hβp)
  have hβH : β = primeFormConjHom h _ H * primeFormFieldHom h hC1 θ *
      (primeFormConjHom h _ H)⁻¹ := by
    rw [← hAθ]
    exact hH
  by_cases hB1 : ∀ b ∈ Bs, b = 1
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [hB1 b hb]
    simp
  push Not at hB1
  obtain ⟨b, hb, hb1⟩ := hB1
  obtain ⟨s, hs, hsp⟩ := OrdPInnerSU.exists_eq_frame_of_innerDiag hF hf hn hker hC hP₀ hcop
    (hS.innerDiag b hb) (hS.elem.2 b hb)
  rw [← hφ] at hs
  have hs1 : s ≠ 1 := fun h1 => hb1 (by rw [← hs, h1, map_one])
  have hpS : p ∣ Nat.card ↥(unitarySU 2 f F n) := by
    have : Fact p.Prime := ⟨hpp⟩
    rw [← orderOf_eq_prime hsp hs1]
    exact orderOf_dvd_natCard s
  obtain ⟨E, hEc, hEp, hEθ, hEcard⟩ := exists_fixed_elemAb h hpp hp2 hpq hθo hpS
  have hHmem : ∀ x : ↥(unitarySU 2 f F n),
      (H : GL (Fin n) F) * x * (H : GL (Fin n) F)⁻¹ ∈ unitarySU 2 f F n := fun x => by
    have h1 := conj_mem_gramSU h _ H.2 (OrdPFieldSU.mem_gramSU_one h x)
    have h2 : ∀ g : GL (Fin n) F, g ∈ gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) →
        g ∈ unitarySU 2 f F n := fun g hg => by
      rw [unitarySU_eq_gramSU h]
      exact hg
    exact h2 _ h1
  set cH : ↥(unitarySU 2 f F n) →* ↥(unitarySU 2 f F n) :=
    MonoidHom.codRestrict ((MulAut.conj (H : GL (Fin n) F)).toMonoidHom.comp
      (unitarySU 2 f F n).subtype) _ hHmem with hcHdef
  have hcH : ∀ x, ((cH x : ↥(unitarySU 2 f F n)) : GL (Fin n) F) =
      (H : GL (Fin n) F) * x * (H : GL (Fin n) F)⁻¹ := fun x => rfl
  have hcHinj : Function.Injective cH := by
    intro u v huv
    have h1 := congrArg (fun z : ↥(unitarySU 2 f F n) => (z : GL (Fin n) F)) huv
    simp only [hcH, mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext h1
  have hinjE : Function.Injective ((φ.comp cH).comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : cH x = 1 := eq_one_of_frame hF hf hpp hpq hn hker hP₀ (cH x) hx
      (by rw [← map_pow, hEp x x.2, map_one])
    exact Subtype.ext (hcHinj (h1.trans (map_one cH).symm))
  have hEcard' : Nat.card (E.map (φ.comp cH)) = Nat.card E := by
    have hr : ((φ.comp cH).comp E.subtype).range = E.map (φ.comp cH) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr]
    exact (Nat.card_congr (MonoidHom.ofInjective hinjE).toEquiv).symm
  refine OrdPNS.exists_conj_mem_centralizer_of_card hS (E := E.map (φ.comp cH)) ?_ ?_ ?_ ?_
  · rintro _ ⟨t, -, rfl⟩
    exact Subgroup.le_normalizer (hrφ ▸ ⟨_, rfl⟩)
  · refine ⟨⟨⟨fun c d => ?_⟩⟩, ?_⟩
    · obtain ⟨_, t, ht, rfl⟩ := c
      obtain ⟨_, u, hu, rfl⟩ := d
      apply Subtype.ext
      change (φ.comp cH) t * (φ.comp cH) u = (φ.comp cH) u * (φ.comp cH) t
      rw [← map_mul, ← map_mul, hEc t ht u hu]
    · rintro _ ⟨t, ht, rfl⟩
      rw [← map_pow, hEp t ht, map_one]
  · rw [hEcard']
    exact (card_bstar_le hF hf hS hpq).trans hEcard
  · rintro _ ⟨t, ht, rfl⟩
    have hfD : primeFormFieldHom h hC1 θ (π t) = π t := by
      rw [hπdef, OrdPFieldSU.projP_apply h hn1 t (OrdPFieldSU.mem_gramSU_one h t)]
      change primeFormFieldAut h hC1 θ _ = _
      rw [primeFormFieldAut_mk]
      congr 1
      apply Subtype.ext
      change glAut θ (t : GL (Fin n) F) = t
      exact hEθ t ht
    have hcD : primeFormConjHom h _ H (π t) = π (cH t) := by
      rw [hπdef, OrdPFieldSU.projP_apply h hn1 t (OrdPFieldSU.mem_gramSU_one h t),
        primeFormConjHom_mk, OrdPFieldSU.projP_apply h hn1 (cH t) (OrdPFieldSU.mem_gramSU_one h _)]
      rfl
    have hfix : β (π (cH t)) = π (cH t) := by
      have hinv : ∀ z, (primeFormConjHom h _ H)⁻¹ (primeFormConjHom h _ H z) = z := fun z => by
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      rw [← hcD, hβH, MulAut.mul_apply, MulAut.mul_apply, hinv, hfD]
    have h2 := hrel _ _ hfix
    change y * φ (cH t) = φ (cH t) * y
    calc y * φ (cH t) = y * (y⁻¹ * φ (cH t) * y) := by rw [h2]
      _ = φ (cH t) * y := by group

end Setting

end OrdPFieldNsU

section Family

theorem ggOrdPFieldConjPSUNonsplit_holds : ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (Bs G₀ : Subgroup G) (n f : ℕ) (ψ : (ggU .PSU n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSU n f).D .PSU n f ψ → ¬ p ∣ 2 ^ f + 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      ¬ GGPsiInnerDiag (ggU .PSU n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f ψ hS hpq y hyM hyo hyI
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hf : 1 ≤ f := hS.presents.1.1.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  exact OrdPFieldNsU.exists_conj_mem_centralizer_nonsplit
    (F := GaloisField 2 (2 * (f + 1))) (card_galoisField_two_mul 2 (f + 1) (by omega)) (by omega)
    hS hpq hyM hyp hyI

end Family

end CFSG.StandardType
