module

public import CFSG.RankThree.S4Free.Stellmacher29
public import CFSG.Timmesfeld.Orders.Bang
import CFSG.LocalAnalysis.SectionRank.SuzukiCover
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport

public section

namespace CFSG.RankThree.S4Free.Stell

open CFSG.Quasithin Subgroup CFSG.Timmesfeld

variable {V : Type*} [CommGroup V] [Finite V]

theorem forall_mem_of_relIndex_eq_two_pow {U₁ U₂ : Subgroup V} (h21 : U₂ ≤ U₁) {y : MulAut V}
    (hy1 : y ∈ stabSub U₁) (hy2 : y ∈ stabSub U₂) {n p e : ℕ} (hp : IsPrimitivePrimeDivisor p n)
    (hn : 0 < n) (hy : y ^ p ^ e = 1) (hidx : U₂.relIndex U₁ = 2 ^ n)
    (hnt : ¬ ∀ w ∈ U₁, y w * w⁻¹ ∈ U₂) : ∀ w ∈ U₁, y w * w⁻¹ ∈ U₂ → w ∈ U₂ := by
  haveI : Fact p.Prime := ⟨hp.prime⟩
  set N := U₂.subgroupOf U₁ with hN
  set eU := resHom U₁ ⟨y, hy1⟩ with heU
  have he : N.map (eU : ↥U₁ →* ↥U₁) = N := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      simp only [hN, SetLike.mem_coe, Subgroup.mem_subgroupOf] at hv ⊢
      exact (hy2 _).mpr hv
    · intro hu
      refine ⟨eU⁻¹ u, ?_, by simp⟩
      simp only [hN, SetLike.mem_coe, Subgroup.mem_subgroupOf] at hu ⊢
      have h1 : ((eU⁻¹ u : U₁) : V) = y⁻¹ (u : V) := by
        rw [heU, ← map_inv]
        rfl
      rw [h1]
      exact (((stabSub U₂).inv_mem hy2) _).mpr hu
  set yQ : MulAut (↥U₁ ⧸ N) := QuotientGroup.congr N N eU he with hyQ
  have hpow : ∀ k : ℕ, ∀ u : U₁, (yQ ^ k) (u : ↥U₁ ⧸ N) = ((eU ^ k) u : ↥U₁ ⧸ N) := by
    intro k
    induction k with
    | zero => intro u; rfl
    | succ k ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, ih, hyQ, QuotientGroup.congr_mk, pow_succ',
        MulAut.mul_apply]
  have heU1 : eU ^ p ^ e = 1 := by
    have : (⟨y, hy1⟩ : stabSub U₁) ^ p ^ e = 1 := Subtype.ext (by simpa using hy)
    rw [heU, ← map_pow, this, map_one]
  have hyQ1 : yQ ^ p ^ e = 1 := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H u => rw [hpow, heU1]; rfl
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.prime).mp (orderOf_dvd_of_pow_eq_one hyQ1)
  have hmod := AutQ8D8.card_modEq_fixSub yQ hj
  have hcardQ : Nat.card (↥U₁ ⧸ N) = 2 ^ n := hidx
  have hfdvd : Nat.card (AutQ8D8.fixSub yQ) ∣ 2 ^ n := hcardQ ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨f, hfn, hf⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hfdvd
  have hfix : ∀ u : U₁, (u : ↥U₁ ⧸ N) ∈ AutQ8D8.fixSub yQ ↔ y u * (u : V)⁻¹ ∈ U₂ := by
    intro u
    rw [AutQ8D8.mem_fixSub, hyQ, QuotientGroup.congr_mk, QuotientGroup.eq, hN,
      Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, heU, resHom_apply]
    constructor
    · intro h
      have := U₂.inv_mem h
      rwa [mul_inv_rev, inv_inv, mul_comm] at this
    · intro h
      have := U₂.inv_mem h
      rwa [mul_inv_rev, inv_inv, mul_comm] at this
  have hfne : f ≠ n := by
    rintro rfl
    apply hnt
    intro w hw
    have htop : AutQ8D8.fixSub yQ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hf, hcardQ])
    exact (hfix ⟨w, hw⟩).mp (htop ▸ Subgroup.mem_top _)
  intro w hw hyw
  by_contra hwU
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h1 : ((⟨w, hw⟩ : U₁) : ↥U₁ ⧸ N) ∈ AutQ8D8.fixSub yQ := (hfix ⟨w, hw⟩).mpr hyw
    rw [pow_zero, Subgroup.card_eq_one] at hf
    rw [hf, Subgroup.mem_bot, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf] at h1
    exact hwU h1
  rw [hcardQ, hf] at hmod
  have hlt : f < n := lt_of_le_of_ne hfn hfne
  have hdvd : p ∣ 2 ^ (n - f) - 1 := by
    have h1 : 2 ^ f * 1 ≡ 2 ^ f * 2 ^ (n - f) [MOD p] := by
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' hlt.le]
      exact hmod.symm
    have hcop : Nat.gcd p (2 ^ f) = 1 :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp.prime Nat.prime_two).mpr (hp.ne_two hn))
    have h2 := Nat.ModEq.cancel_left_of_coprime hcop h1
    exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp h2
  have := (hp.dvd_sub_one_iff hn (n - f)).mp hdvd
  have hpos : 0 < n - f := by omega
  exact absurd (Nat.le_of_dvd hpos this) (by omega)

theorem forall_mem_of_chief {L R : Subgroup (MulAut V)} {U C : Subgroup V} {y : MulAut V}
    {n p e : ℕ} (hp : IsPrimitivePrimeDivisor p n) (hn : 0 < n) (hyL : y ∈ L)
    (hy : y ^ p ^ e = 1) (hyR : y ∉ R) (hCU : C ≤ U) (hLC : L ≤ stabSub C)
    (hchief : ∀ U₁ U₂ : Subgroup V, C ≤ U₂ → U₂ ≤ U₁ → U₁ ≤ U → L ≤ stabSub U₁ →
      L ≤ stabSub U₂ → U₂ < U₁ →
      (∀ X : Subgroup V, U₂ ≤ X → X ≤ U₁ → L ≤ stabSub X → X = U₂ ∨ X = U₁) →
      U₂.relIndex U₁ = 2 ^ n ∧ ∀ l ∈ L, (∀ w ∈ U₁, l w * w⁻¹ ∈ U₂) → l ∈ R)
    (hLU : L ≤ stabSub U) : ∀ w ∈ U, y w * w⁻¹ ∈ C → w ∈ C := by
  classical
  have : Finite (Subgroup V) :=
    Finite.of_injective (fun H : Subgroup V => (H : Set V)) SetLike.coe_injective
  suffices key : ∀ k : ℕ, ∀ U₁ : Subgroup V, Nat.card U₁ = k → C ≤ U₁ → U₁ ≤ U →
      L ≤ stabSub U₁ → ∀ w ∈ U₁, y w * w⁻¹ ∈ C → w ∈ C from key _ U rfl hCU le_rfl hLU
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U₁ hk hCU₁ hU₁U hLU₁ w hw hyw
  by_cases hC1 : U₁ = C
  · exact hC1 ▸ hw
  have hlt1 : C < U₁ := lt_of_le_of_ne hCU₁ (Ne.symm hC1)
  obtain ⟨U₂, ⟨hCU₂, hU₂U₁, hLU₂⟩, hmax⟩ := Set.exists_max_image
    {X : Subgroup V | C ≤ X ∧ X < U₁ ∧ L ≤ stabSub X} (fun X => Nat.card X) (Set.toFinite _)
    ⟨C, le_rfl, hlt1, hLC⟩
  have hchief' : ∀ X : Subgroup V, U₂ ≤ X → X ≤ U₁ → L ≤ stabSub X → X = U₂ ∨ X = U₁ := by
    intro X h2X hX1 hLX
    by_cases hX : X = U₁
    · exact Or.inr hX
    · left
      have hXlt : X < U₁ := lt_of_le_of_ne hX1 hX
      have hcard := hmax X ⟨hCU₂.trans h2X, hXlt, hLX⟩
      exact (Subgroup.eq_of_le_of_card_ge h2X hcard).symm
  obtain ⟨hidx, hker⟩ := hchief U₁ U₂ hCU₂ hU₂U₁.le hU₁U hLU₁ hLU₂ hU₂U₁ hchief'
  have hnt : ¬ ∀ w ∈ U₁, y w * w⁻¹ ∈ U₂ := fun h => hyR (hker y hyL h)
  have hwU₂ : w ∈ U₂ := forall_mem_of_relIndex_eq_two_pow hU₂U₁.le (hLU₁ hyL) (hLU₂ hyL) hp hn hy
    hidx hnt w hw (hCU₂ hyw)
  have hcardlt : Nat.card U₂ < k := hk ▸ Subgroup.card_lt_of_lt hU₂U₁
  exact ih _ hcardlt U₂ rfl hCU₂ (hU₂U₁.le.trans hU₁U) hLU₂ w hwU₂ hyw

theorem dimOn_le_dimOn_add_of_relIndex_le {A A₀ : Subgroup (MulAut V)} (hA : IsPGroup 2 A)
    (hA₀ : A₀ ≤ A) {k : ℕ} (hidx : A₀.relIndex A ≤ 2 ^ k) (U : Subgroup V) :
    dimOn A U ≤ dimOn A₀ U + k := by
  have h1 := Subgroup.relIndex_mul_relIndex (centSub U ⊓ A₀) A₀ A inf_le_right hA₀
  rw [Subgroup.inf_relIndex_right] at h1
  have h2 : (centSub U).relIndex A ≤ (centSub U ⊓ A₀).relIndex A :=
    Subgroup.relIndex_le_of_le_left inf_le_left (relIndex_ne_zero_of_finite _ _)
  have h3 : (centSub U).relIndex A ≤ 2 ^ (dimOn A₀ U + k) := by
    rw [pow_add]
    calc (centSub U).relIndex A ≤ (centSub U ⊓ A₀).relIndex A := h2
      _ = (centSub U).relIndex A₀ * A₀.relIndex A := h1.symm
      _ ≤ 2 ^ dimOn A₀ U * 2 ^ k := by
        rw [relIndex_eq_two_pow (hA.to_le hA₀)]
        exact Nat.mul_le_mul_left _ hidx
  rw [relIndex_eq_two_pow hA] at h3
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3

theorem inf_oTwo_le_quotTriv_of_sup {S M A L : Subgroup (MulAut V)} {Z₀ U : Subgroup V}
    (hOS : (oTwo ↥L).map L.subtype ≤ S) (hSZ : S ≤ stabSub Z₀) (hMZ : M ≤ stabSub Z₀)
    (hq : IsQuadratic A) (hZA : Z₀ ≤ fixV A) (hAL : A ≤ L)
    (hsup : ∀ x ∈ L, x ∉ M → A ⊔ A.map (MulAut.conj x).toMonoidHom = L) (hZU : Z₀ ≤ U)
    (hLU : L ≤ stabSub U)
    (hgen : ∀ W : Subgroup V, (∀ l ∈ L, Z₀.map l.toMonoidHom ≤ W) → U ≤ W) :
    A ⊓ (oTwo ↥L).map L.subtype ≤ quotTriv U (U ⊓ fixV L) := by
  rintro b ⟨hbA, hbO⟩
  have hbL : b ∈ L := hAL hbA
  have hbU : b ∈ stabSub U := hLU hbL
  refine ⟨hbU, ?_⟩
  let W : Subgroup V := U ⊓ (U ⊓ fixV L).comap (commMulHom b)
  suffices hUW : U ≤ W from fun w hw => (hUW hw).2
  refine hgen W fun l hl => ?_
  rintro _ ⟨z, hz, rfl⟩
  have hlz : l z ∈ U := (hLU hl z).2 (hZU hz)
  refine ⟨hlz, ?_⟩
  change b (l z) * (l z)⁻¹ ∈ U ⊓ fixV L
  refine ⟨U.mul_mem ((hbU _).2 hlz) (U.inv_mem hlz), ?_⟩
  by_cases hlM : l ∈ M
  · have hlz' : l z ∈ Z₀ := (hMZ hlM z).2 hz
    rw [hZA hlz' b hbA, mul_inv_cancel]
    exact (fixV L).one_mem
  · rw [← hsup l hl hlM, fixV_sup_eq_inf]
    refine ⟨hq (Subgroup.subset_closure ⟨b, hbA, l z, rfl⟩), ?_⟩
    rw [fixV_map_conj]
    have hb' : l⁻¹ * b * l ∈ S := by
      have := conj_mem_map_oTwo (L := L) (L.inv_mem hl) hbO
      rw [inv_inv] at this
      exact hOS this
    have hz' : (l⁻¹ * b * l) z ∈ Z₀ := (hSZ hb' z).2 hz
    refine ⟨(l⁻¹ * b * l) z * z⁻¹, hZA (Z₀.mul_mem hz' (Z₀.inv_mem hz)), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulAut.mul_apply,
      MulAut.apply_inv_self]

theorem false_of_szCore (hV : ∀ v : V, v ^ 2 = 1) {S M A L : Subgroup (MulAut V)}
    {Z₀ U : Subgroup V} (hS : IsPGroup 2 S) (hSM : S ≤ M) (hMZ : M ≤ stabSub Z₀)
    (hLM : L ⊓ stabSub Z₀ ≤ M) (hAel : CFSG.Open.IsElemAbelian 2 A) (hq : IsQuadratic A)
    (hZA : Z₀ ≤ fixV A) (hgt : AGt S Z₀ 1) (hAL : A ≤ L) (hLnM : ¬ L ≤ M)
    (hsup : ∀ x ∈ L, x ∉ M → A ⊔ A.map (MulAut.conj x).toMonoidHom = L)
    (hOS : (oTwo ↥L).map L.subtype ≤ S) (hZU : Z₀ ≤ U) (hLU : L ≤ stabSub U)
    (hgen : ∀ W : Subgroup V, (∀ l ∈ L, Z₀.map l.toMonoidHom ≤ W) → U ≤ W)
    (hAU : codimOn A U ≤ dimOn A U)
    (h25a : ∀ x ∈ L, x ∉ M →
      (U ⊓ fixV A) ⊔ (U ⊓ fixV (A.map (MulAut.conj x).toMonoidHom)) = U)
    {a : MulAut V} (haA : a ∈ A)
    (h25b : commSub U (Subgroup.zpowers a) ⊔ (U ⊓ fixV L) = U ⊓ fixV A ∧
      commSub U (Subgroup.zpowers a) ⊓ (U ⊓ fixV L) = ⊥ ∧
      2 * rk ↥(commSub U (Subgroup.zpowers a)) = mRel (U ⊓ fixV L) U)
    {m : ℕ} (hm : 0 < m) (hidx : (A ⊓ (oTwo ↥L).map L.subtype).relIndex A ≤ 2 ^ m)
    {p e : ℕ} (hp : IsPrimitivePrimeDivisor p (4 * m)) {y : MulAut V} (hyL : y ∈ L)
    (hy : y ^ p ^ e = 1) (hyfpf : ∀ w ∈ U, y w * w⁻¹ ∈ U ⊓ fixV L → w ∈ U ⊓ fixV L) :
    False := by
  haveI : Fact p.Prime := ⟨hp.prime⟩
  have hp2 : p ≠ 2 := hp.ne_two (by omega)
  have hSZ : S ≤ stabSub Z₀ := hSM.trans hMZ
  have hCU : U ⊓ fixV L ≤ U := inf_le_left
  have hLC : ∀ l ∈ L, ∀ c ∈ U ⊓ fixV L, l c = c := fun l hl c hc => hc.2 l hl
  obtain ⟨x, hxL, hxM⟩ := Set.not_subset.mp hLnM
  have haL : a ∈ L := hAL haA
  have ha2 : a ^ 2 = 1 := hAel.2 a haA
  obtain ⟨b2, b4, b5⟩ := h25b
  have hsup' := h25a x hxL hxM
  have hr1 := rk_sup_add_rk_inf (commSub U (Subgroup.zpowers a)) (U ⊓ fixV L)
  rw [b2, b4, rk_bot] at hr1
  have hr2 : codimOn A U + rk ↥(U ⊓ fixV A) = rk U := by
    have := mRel_add_rk_of_le (inf_le_left : U ⊓ fixV A ≤ U)
    rwa [show mRel (U ⊓ fixV A) U = codimOn A U by
      unfold codimOn mRel; rw [inf_comm, Subgroup.inf_relIndex_right]] at this
  have hr3 := mRel_add_rk_of_le hCU
  have hUC : mRel (U ⊓ fixV L) U = 2 * codimOn A U := by omega
  have hs1 : 1 ≤ codimOn A U := by
    by_contra h0
    have hC0 : mRel (U ⊓ fixV L) U = 0 := by omega
    rw [mRel_eq_zero_iff (isPGroup_subgroup hV U)] at hC0
    exact hxM (hLM ⟨hxL, centSub_le_stabSub Z₀ fun z hz => (hC0 (hZU hz)).2 x hxL⟩)
  have hA2 : IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa using hAel.2 g g.2)⟩
  have hdA := dimOn_le_dimOn_add_of_relIndex_le hA2 inf_le_left hidx U
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup (MulAut V),
      Q = (oTwo ↥L).map L.subtype ⊓ quotTriv U (U ⊓ fixV L) := ⟨_, rfl⟩
  have hQO : Q ≤ (oTwo ↥L).map L.subtype := hQ ▸ inf_le_left
  have hQT : Q ≤ quotTriv U (U ⊓ fixV L) := hQ ▸ inf_le_right
  have hQS : Q ≤ S := hQO.trans hOS
  have hQ2 : IsPGroup 2 Q := hS.to_le hQS
  have hQL : Q ≤ L := hQO.trans (Subgroup.map_subtype_le _)
  have hQC : ∀ q ∈ Q, ∀ c ∈ U ⊓ fixV L, q c = c := fun q hq => hLC q (hQL hq)
  have hQU : Q ≤ stabSub U := hQL.trans hLU
  have hconj : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q := by
    intro l hl q hq
    rw [hQ] at hq ⊢
    exact ⟨conj_mem_map_oTwo hl hq.1, conj_mem_quotTriv (hLU hl) (hLC l hl) hq.2⟩
  have hQN : L ≤ Subgroup.normalizer (Q : Set (MulAut V)) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hconj l hl q, fun h => ?_⟩
    have := hconj l⁻¹ (L.inv_mem hl) _ h
    rwa [show l⁻¹ * (l * q * l⁻¹) * l⁻¹⁻¹ = q by group] at this
  have hel := elemAbOn_of_le_quotTriv hV hQT hQC
  have hA₀Q : A ⊓ (oTwo ↥L).map L.subtype ≤ Q := by
    rw [hQ]
    exact le_inf inf_le_right
      (inf_oTwo_le_quotTriv_of_sup hOS hSZ hMZ hq hZA hAL hsup hZU hLU hgen)
  obtain ⟨B₀, hB₀⟩ : ∃ B : Subgroup (MulAut V), B = Q ⊓ centSub (U ⊓ fixV A) := ⟨_, rfl⟩
  have hB₀Q : B₀ ≤ Q := hB₀ ▸ inf_le_left
  have hB₀F : B₀ ≤ centSub (U ⊓ fixV A) := hB₀ ▸ inf_le_right
  have hA₀B₀ : A ⊓ (oTwo ↥L).map L.subtype ≤ B₀ := by
    rw [hB₀]
    exact le_inf hA₀Q fun b hb w hw => hw.2 b hb.1
  have hdA₀ : dimOn (A ⊓ (oTwo ↥L).map L.subtype) U ≤ dimOn B₀ U :=
    mRel_le_of_le_right (hQ2.to_le hB₀Q) hA₀B₀
  have hcB₀ : codimOn B₀ U ≤ codimOn A U := by
    have h1 : fixV A ⊓ U ≤ fixV B₀ := fun v hv b hb => hB₀F hb v ⟨hv.2, hv.1⟩
    have h2 := mRel_le_of_le_left (isPGroup_subgroup hV U) h1
    rwa [show mRel (fixV A ⊓ U) U = codimOn A U by
      unfold codimOn mRel; rw [Subgroup.inf_relIndex_right]] at h2
  have hdB₀ : dimOn B₀ U < codimOn A U := by
    by_cases hfix : U ≤ fixV B₀
    · have h0 : dimOn B₀ U = 0 := by
        rw [mRel_eq_zero_iff (hQ2.to_le hB₀Q)]
        exact fun g hg u hu => hfix hu g hg
      omega
    · have h := mul_dimOn_lt_codimOn hV (H := L) hQ2 hQS hQN hLU hZU hgen hgt (A := B₀) hB₀Q
        (hel.mono hB₀Q le_rfl) hfix
      rw [one_mul] at h
      have h' : dimOn B₀ U < codimOn B₀ U := by exact_mod_cast h
      omega
  obtain ⟨B₀x, hB₀x⟩ : ∃ B : Subgroup (MulAut V), B = B₀.map (MulAut.conj x).toMonoidHom :=
    ⟨_, rfl⟩
  have hB₀xQ : B₀x ≤ Q := by
    rw [hB₀x]
    rintro _ ⟨b, hb, rfl⟩
    exact hconj x hxL b (hB₀Q hb)
  have hB₀xF : B₀x ≤ centSub (U ⊓ fixV (A.map (MulAut.conj x).toMonoidHom)) := by
    rw [hB₀x]
    rintro _ ⟨b, hb, rfl⟩
    intro w hw
    obtain ⟨hwU, hwA⟩ := hw
    rw [fixV_map_conj] at hwA
    obtain ⟨v, hv, rfl⟩ := hwA
    have hvU : v ∈ U := ((hLU hxL) v).1 hwU
    have hbv : b v = v := hB₀F hb v ⟨hvU, hv⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.inv_apply_self, hbv]
  have hdB₀x : dimOn B₀x U = dimOn B₀ U := by
    have h := dimOn_map_conj x B₀ U
    rwa [map_eq_self_of_mem_stabSub (hLU hxL), ← hB₀x] at h
  have hlow := dimOn_add_dimOn_le hQU hQ2 hB₀Q hB₀xQ hB₀F hB₀xF hsup'
  have hup := dimOn_le_two_mul_dimOn hV hQ2 hQT hQC (hLU haL) ha2 (hQN haL) (hLC a haL)
  rw [b2, ← hB₀] at hup
  have hQk : dimOn Q U = 2 * dimOn B₀ U := by omega
  have hc1 := card_modEq_of_forall_mem (hLU hyL) hy hCU (hLC y hyL) hyfpf
  rw [card_eq_two_pow hV U, card_eq_two_pow hV (U ⊓ fixV L),
    show rk U = rk ↥(U ⊓ fixV L) + 2 * codimOn A U by omega, pow_add] at hc1
  have hgcd : Nat.gcd p (2 ^ rk ↥(U ⊓ fixV L)) = 1 :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp.prime Nat.prime_two).mpr hp2)
  have h4s : 1 ≡ 2 ^ (2 * codimOn A U) [MOD p] :=
    (Nat.ModEq.cancel_left_of_coprime hgcd (by rwa [mul_one])).symm
  have hc2 := card_autSub_modEq_one hV hQT hQC (hLU hyL) hy (hQN hyL) hCU (hLC y hyL) hyfpf
  rw [card_autSub_eq_two_pow hQU hQ2, hQk] at hc2
  have hds : 4 * m ∣ 2 * codimOn A U :=
    (hp.dvd_sub_one_iff (by omega) _).mp ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h4s)
  have hdd : 4 * m ∣ 2 * dimOn B₀ U :=
    (hp.dvd_sub_one_iff (by omega) _).mp ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hc2.symm)
  obtain ⟨k₁, hk₁⟩ := hds
  obtain ⟨k₂, hk₂⟩ := hdd
  have hlt : k₂ < k₁ := by
    by_contra h
    push Not at h
    have := Nat.mul_le_mul_left (4 * m) h
    omega
  have := Nat.mul_le_mul_left (4 * m) (Nat.succ_le_of_lt hlt)
  nlinarith

theorem exists_pow_eq_one_not_mem {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    {R : Subgroup L} [R.Normal] {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : ↥L ⧸ R ≃* CFSG.Blueprint.suzukiGroup a K) {p : ℕ}
    (hp : IsPrimitivePrimeDivisor p (4 * (2 * a + 1))) :
    ∃ y ∈ L, ∃ t : ℕ, y ^ p ^ t = 1 ∧ y ∉ R.map L.subtype := by
  haveI : Fact p.Prime := ⟨hp.prime⟩
  have hcard : Nat.card (↥L ⧸ R) =
      ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr
      (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).toEquiv]
    exact CFSG.SectionRank.card_suzukiMatrixGroup (m := a) (by omega)
  have hpq : p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
    rw [← pow_mul]
    refine (hp.dvd_add_one_iff (by omega) _).mpr ⟨⟨1, by ring⟩, fun h => ?_⟩
    have := Nat.le_of_dvd (by omega) h
    omega
  have hpL : p ∣ Nat.card (↥L ⧸ R) := by
    rw [hcard]
    exact (hpq.mul_right _).mul_right _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpL
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨t, n', hn', hz⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' p hp.prime.one_lt.ne'
  refine ⟨((z ^ n' : ↥L) : G), (z ^ n').2, t, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  · rintro ⟨w, hw, hwz⟩
    have hwz' : w = z ^ n' := Subtype.ext hwz
    rw [hwz'] at hw
    have h1 : (z : ↥L ⧸ R) ^ n' = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hw
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hg] at this
    exact hn' this

theorem false_of_szData (hV : ∀ v : V, v ^ 2 = 1) {S M A L : Subgroup (MulAut V)}
    {Z₀ U : Subgroup V} (hS : IsPGroup 2 S) (hSM : S ≤ M) (hMZ : M ≤ stabSub Z₀)
    (hLM : L ⊓ stabSub Z₀ ≤ M) (hAel : CFSG.Open.IsElemAbelian 2 A) (hq : IsQuadratic A)
    (hZA : Z₀ ≤ fixV A) (hgt : AGt S Z₀ 1) (hAL : A ≤ L) (hLnM : ¬ L ≤ M)
    (hsup : ∀ x ∈ L, x ∉ M → A ⊔ A.map (MulAut.conj x).toMonoidHom = L)
    (hOS : (oTwo ↥L).map L.subtype ≤ S) (hZU : Z₀ ≤ U) (hLU : L ≤ stabSub U)
    (hgen : ∀ W : Subgroup V, (∀ l ∈ L, Z₀.map l.toMonoidHom ≤ W) → U ≤ W)
    (hAU : codimOn A U ≤ dimOn A U) (R : Subgroup ↥L) [R.Normal] {a : ℕ} (ha : 1 ≤ a)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : ↥L ⧸ R ≃* CFSG.Blueprint.suzukiGroup a K)
    (h25a : ∀ x ∈ L, x ∉ M →
      (U ⊓ fixV A) ⊔ (U ⊓ fixV (A.map (MulAut.conj x).toMonoidHom)) = U)
    {b : MulAut V} (hbA : b ∈ A)
    (h25b : commSub U (Subgroup.zpowers b) ⊔ (U ⊓ fixV L) = U ⊓ fixV A ∧
      commSub U (Subgroup.zpowers b) ⊓ (U ⊓ fixV L) = ⊥ ∧
      2 * rk ↥(commSub U (Subgroup.zpowers b)) = mRel (U ⊓ fixV L) U)
    (hchief : ∀ U₁ U₂ : Subgroup V, U ⊓ fixV L ≤ U₂ → U₂ ≤ U₁ → U₁ ≤ U → L ≤ stabSub U₁ →
      L ≤ stabSub U₂ → U₂ < U₁ →
      (∀ X : Subgroup V, U₂ ≤ X → X ≤ U₁ → L ≤ stabSub X → X = U₂ ∨ X = U₁) →
      U₂.relIndex U₁ = 2 ^ (4 * (2 * a + 1)) ∧
        ∀ l ∈ L, (∀ w ∈ U₁, l w * w⁻¹ ∈ U₂) → l ∈ R.map L.subtype)
    (hidx : (A ⊓ (oTwo ↥L).map L.subtype).relIndex A ≤ 2 ^ (2 * a + 1)) : False := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 4 * (2 * a + 1)) (by omega) (by omega)
  obtain ⟨y, hyL, t, hy, hyR⟩ := exists_pow_eq_one_not_mem ha hK e hp
  have hLC : L ≤ stabSub (U ⊓ fixV L) :=
    le_stabSub_of_forall_apply_mem fun l hl c hc => by rw [hc.2 l hl]; exact hc
  have hyfpf := forall_mem_of_chief hp (by omega) hyL hy hyR inf_le_left hLC hchief hLU
  exact false_of_szCore hV hS hSM hMZ hLM hAel hq hZA hgt hAL hLnM hsup hOS hZU hLU hgen hAU
    h25a hbA h25b (by omega) hidx hp hyL hy hyfpf

end CFSG.RankThree.S4Free.Stell
