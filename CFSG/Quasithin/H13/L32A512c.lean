module

public import CFSG.Quasithin.H13.L32A512b
public import CFSG.Quasithin.H13.L32A511Gold
public import CFSG.Quasithin.H13.L32A512P
public import CFSG.Quasithin.H13.L32A512a
public import CFSG.Quasithin.H13.L32A513a

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

theorem s3_inv : ∀ a b : Equiv.Perm (Fin 3), a ^ 2 = 1 → a ≠ 1 → b ^ 3 = 1 →
    a * b * a⁻¹ = b⁻¹ := by decide

theorem eq_of_mem_of_card_eq_two {M : Type*} [Group M] {S : Subgroup M} (hS : Nat.card S = 2)
    {a b : M} (ha : a ∈ S) (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨s, -, hs⟩ := (Nat.card_eq_two_iff' (1 : ↥S)).mp hS
  have e1 : (⟨a, ha⟩ : ↥S) = s := hs _ fun h => ha1 (congrArg Subtype.val h)
  have e2 : (⟨b, hb⟩ : ↥S) = s := hs _ fun h => hb1 (congrArg Subtype.val h)
  exact congrArg Subtype.val (e1.trans e2.symm)

theorem pCore_quotient_pPrimeCore_eq_bot {D : Type*} [Group D] [Finite D] {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) : Open.pCore p (D ⧸ CFSG.pPrimeCore 3 D) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := CFSG.pPrimeCore 3 D
  set P := Open.pCore p (D ⧸ X)
  have hP : P.Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hY : (P.comap (QuotientGroup.mk' X)).Normal := hP.comap _
  have hXY : X ≤ P.comap (QuotientGroup.mk' X) := by
    intro x hx
    rw [Subgroup.mem_comap]
    have : (QuotientGroup.mk' X) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [this]
    exact P.one_mem
  have hmap : (P.comap (QuotientGroup.mk' X)).map (QuotientGroup.mk' X) = P :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective X) P
  have hcard : Nat.card ↥(P.comap (QuotientGroup.mk' X)) = Nat.card ↥P * Nat.card ↥X := by
    have h1 := Subgroup.relIndex_mul_card (H := X) (K := P.comap (QuotientGroup.mk' X))
    rw [inf_eq_left.mpr hXY, ← F6.card_map_mk, hmap] at h1
    exact h1.symm
  have hcop : Nat.Coprime 3 (Nat.card ↥(P.comap (QuotientGroup.mk' X))) := by
    rw [hcard]
    refine Nat.Coprime.mul_right ?_ (CFSG.pPrimeCore_coprime_card (p := 3) (G := D))
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := D ⧸ X) p).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  have hle : P.comap (QuotientGroup.mk' X) ≤ X := F6.le_pPrimeCore_of_normal hcop
  rw [eq_bot_iff, ← hmap, ← QuotientGroup.map_mk'_self X]
  exact Subgroup.map_mono hle

section K

variable {G : Type} [Group G] [Finite G]

theorem exists_eq_pow_of_odd' {Q : Type*} [Group Q] {H K : Subgroup G} (hKH : K ≤ H)
    (hK : quasithinO2QuotientIso K (Equiv.Perm (Fin 3))) (π : ↥H →* Q)
    (hker : ∀ g (hg : g ∈ pCoreOf 2 K), π ⟨g, hKH (pCoreOf_le 2 K hg)⟩ = 1)
    {k₁ k₂ : G} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (ho₁ : Odd (orderOf k₁))
    (ho₂ : Odd (orderOf k₂)) (hπ : π ⟨k₁, hKH hk₁⟩ ≠ 1) :
    ∃ j : ℕ, π ⟨k₂, hKH hk₂⟩ = π ⟨k₁, hKH hk₁⟩ ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc₁ := cube_of_odd hK hk₁ ho₁
  have hc₂ := cube_of_odd hK hk₂ ho₂
  obtain ⟨φ, -, hφk⟩ := hK
  have hmem : ∀ q : ↥K, φ q = 1 → (q : G) ∈ pCoreOf 2 K := fun q hq => by
    have : q ∈ Open.pCore 2 ↥K := by rw [← hφk]; exact hq
    exact ⟨q, this, rfl⟩
  have hφ₁ : φ ⟨k₁, hk₁⟩ ≠ 1 := by
    intro h
    apply hπ
    exact hker _ (hmem _ h)
  have hφc : ∀ k (hk : k ∈ K), k ^ 3 = 1 → φ ⟨k, hk⟩ ^ 3 = 1 := fun k hk h3 => by
    rw [← map_pow]
    have : (⟨k, hk⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [this, map_one]
  obtain ⟨j, hj⟩ : ∃ j : ℕ, φ ⟨k₂, hk₂⟩ = φ ⟨k₁, hk₁⟩ ^ j := by
    rcases s3_mem_powers _ _ (hφc _ hk₁ hc₁) (hφc _ hk₂ hc₂) hφ₁ with h | h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
    · exact ⟨2, h⟩
  set q : ↥K := (⟨k₁, hk₁⟩ : ↥K)⁻¹ ^ j * ⟨k₂, hk₂⟩ with hq
  have hqk : φ q = 1 := by
    rw [hq, map_mul, map_pow, map_inv, hj, inv_pow, inv_mul_cancel]
  have h1 := hker _ (hmem _ hqk)
  refine ⟨j, ?_⟩
  have e : (⟨(q : G), hKH (pCoreOf_le 2 K (hmem _ hqk))⟩ : ↥H) =
      (⟨k₁, hKH hk₁⟩ : ↥H)⁻¹ ^ j * ⟨k₂, hKH hk₂⟩ := by
    apply Subtype.ext
    simp [hq]
  rw [e, map_mul, map_pow, map_inv, mul_eq_one_iff_eq_inv, inv_pow, inv_inj] at h1
  exact h1.symm

theorem inv_of_involution' {Q : Type*} [Group Q] {H K : Subgroup G} (hKH : K ≤ H)
    (hK : quasithinO2QuotientIso K (Equiv.Perm (Fin 3))) (π : ↥H →* Q)
    (hker : ∀ g (hg : g ∈ pCoreOf 2 K), π ⟨g, hKH (pCoreOf_le 2 K hg)⟩ = 1)
    {t k : G} (ht : t ∈ K) (hk : k ∈ K) (ht2 : t ^ 2 = 1) (htO : t ∉ pCoreOf 2 K)
    (hko : Odd (orderOf k)) :
    π ⟨t, hKH ht⟩ * π ⟨k, hKH hk⟩ * (π ⟨t, hKH ht⟩)⁻¹ = (π ⟨k, hKH hk⟩)⁻¹ := by
  have hk3 := cube_of_odd hK hk hko
  obtain ⟨φ, -, hφk⟩ := hK
  have hmem : ∀ q : ↥K, φ q = 1 → (q : G) ∈ pCoreOf 2 K := fun q hq => by
    have : q ∈ Open.pCore 2 ↥K := by rw [← hφk]; exact hq
    exact ⟨q, this, rfl⟩
  have hφt : φ ⟨t, ht⟩ ≠ 1 := fun h => htO (hmem _ h)
  have hφt2 : φ ⟨t, ht⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨t, ht⟩ : ↥K) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [this, map_one]
  have hφk3 : φ ⟨k, hk⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨k, hk⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
    rw [this, map_one]
  have h1 := s3_inv _ _ hφt2 hφt hφk3
  set q : ↥K := ⟨t, ht⟩ * ⟨k, hk⟩ * (⟨t, ht⟩ : ↥K)⁻¹ * ⟨k, hk⟩ with hq
  have hqk : φ q = 1 := by
    rw [hq, map_mul, map_mul, map_mul, map_inv, h1, inv_mul_cancel]
  have h2 := hker _ (hmem _ hqk)
  have e : (⟨(q : G), hKH (pCoreOf_le 2 K (hmem _ hqk))⟩ : ↥H) =
      ⟨t, hKH ht⟩ * ⟨k, hKH hk⟩ * (⟨t, hKH ht⟩ : ↥H)⁻¹ * ⟨k, hKH hk⟩ := by
    apply Subtype.ext
    simp [hq]
  rw [e, map_mul, map_mul, map_mul, map_inv] at h2
  exact eq_inv_of_mul_eq_one_left h2

end K

section Aut

variable {V : Type*} [CommGroup V] [Finite V]

theorem rk_commV_zpowers_conj (g a : MulAut V) :
    rk (commV (Subgroup.zpowers (g * a * g⁻¹))) = rk (commV (Subgroup.zpowers a)) := by
  rw [← rkIdx_fixV_zpowers, ← rkIdx_fixV_zpowers, fixV_zpowers_conj]
  unfold rkIdx
  exact congrArg (padicValNat 2) (Subgroup.index_map_equiv (fixV (Subgroup.zpowers a)) g)

theorem cube_of_involutions (hV : ∀ v : V, v ^ 2 = 1) {S : Subgroup (MulAut V)}
    (hT : ∀ u ∈ S, ∀ w ∈ S, u ^ 2 = 1 → w ^ 2 = 1 → u ≠ 1 → w ≠ 1 → u * w = w * u → u = w)
    (h5 : ∀ g ∈ S, orderOf g ≠ 5) {d₁ d₂ : MulAut V} (hS₁ : d₁ ∈ S) (hS₂ : d₂ ∈ S)
    (h₁ : d₁ ^ 2 = 1) (h₂ : d₂ ^ 2 = 1) (h₁1 : d₁ ≠ 1) (h₂1 : d₂ ≠ 1)
    (hrk : rk (commV (Subgroup.zpowers d₁)) ≤ 2) : (d₁ * d₂) ^ 3 = 1 := by
  have : Finite (MulAut V) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut V))
  have hodd := odd_orderOf_mul_of_involutions hT hS₁ hS₂ h₁ h₂ h₁1 h₂1
  by_cases h1 : d₁ * d₂ = 1
  · rw [h1, one_pow]
  have h₁₁ : d₁ * d₁ = 1 := by rw [← sq]; exact h₁
  have hi1 : d₁⁻¹ = d₁ := inv_eq_of_mul_eq_one_right h₁₁
  have hi2 : d₂⁻¹ = d₂ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h₂)
  have hinv : d₁ * (d₁ * d₂) * d₁⁻¹ = (d₁ * d₂)⁻¹ := by
    rw [mul_inv_rev, hi1, hi2]
    calc d₁ * (d₁ * d₂) * d₁ = (d₁ * d₁) * d₂ * d₁ := by group
      _ = d₂ * d₁ := by rw [h₁₁, one_mul]
  obtain ⟨-, -, h3⟩ := d2_11_core hV h₁ hrk h1 hodd hinv
  have h3' : orderOf (d₁ * d₂) = 3 := by
    rcases h3 with ⟨-, h⟩ | ⟨-, h | h⟩
    · exact h
    · exact h
    · exact absurd h (h5 _ (S.mul_mem hS₁ hS₂))
  rw [← h3']
  exact pow_orderOf_eq_one _

theorem mul_cube_of_inverts (hV : ∀ v : V, v ^ 2 = 1) {S : Subgroup (MulAut V)}
    (hT : ∀ u ∈ S, ∀ w ∈ S, u ^ 2 = 1 → w ^ 2 = 1 → u ≠ 1 → w ≠ 1 → u * w = w * u → u = w)
    (h5 : ∀ g ∈ S, orderOf g ≠ 5) {a b t : MulAut V} (ha : a ∈ S) (hb : b ∈ S) (ht : t ∈ S)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hta : t * a * t⁻¹ = a⁻¹) (htb : t * b * t⁻¹ = b⁻¹)
    (hrk : rk (commV (Subgroup.zpowers t)) ≤ 2) : (a * b) ^ 3 = 1 := by
  have haaa : a * a * a = 1 := by rw [← pow_three']; exact ha3
  have hbbb : b * b * b = 1 := by rw [← pow_three']; exact hb3
  have htt : t * t = 1 := by rw [← sq]; exact ht2
  have hconj : ∀ g ∈ S, g * t * g⁻¹ ∈ S ∧ (g * t * g⁻¹) ^ 2 = 1 ∧ g * t * g⁻¹ ≠ 1 := by
    intro g hg
    refine ⟨S.mul_mem (S.mul_mem hg ht) (S.inv_mem hg), by
      rw [conj_pow, ht2, mul_one, mul_inv_cancel], fun h => ht1 ?_⟩
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hta1 : t * a⁻¹ = a * t := by
    calc t * a⁻¹ = (t * a * t⁻¹)⁻¹ * t := by group
      _ = a * t := by rw [hta, inv_inv]
  have htb1 : t * b⁻¹ = b * t := by
    calc t * b⁻¹ = (t * b * t⁻¹)⁻¹ * t := by group
      _ = b * t := by rw [htb, inv_inv]
  obtain ⟨hd₁S, hd₁2, hd₁1⟩ := hconj _ (S.mul_mem ha ha)
  obtain ⟨hd₂S, hd₂2, hd₂1⟩ := hconj _ hb
  have e₁ : a * a * t * (a * a)⁻¹ = a * t := by
    calc a * a * t * (a * a)⁻¹ = a * a * (t * a⁻¹) * a⁻¹ := by group
      _ = a * a * (a * t) * a⁻¹ := by rw [hta1]
      _ = a * a * a * (t * a⁻¹) := by group
      _ = a * t := by rw [haaa, one_mul, hta1]
  have e₂ : b * t * b⁻¹ = t * b := by
    calc b * t * b⁻¹ = t * b⁻¹ * b⁻¹ := by rw [← htb1]
      _ = t * (b * b * b)⁻¹ * b := by group
      _ = t * b := by rw [hbbb, inv_one, mul_one]
  have hP : a * a * t * (a * a)⁻¹ * (b * t * b⁻¹) = a * b := by
    rw [e₁, e₂]
    calc a * t * (t * b) = a * (t * t) * b := by group
      _ = a * b := by rw [htt, mul_one]
  have hrk₁ : rk (commV (Subgroup.zpowers (a * a * t * (a * a)⁻¹))) ≤ 2 := by
    rw [rk_commV_zpowers_conj]
    exact hrk
  rw [← hP]
  exact cube_of_involutions hV hT h5 hd₁S hd₂S hd₁2 hd₂2 hd₁1 hd₂1 hrk₁

end Aut

theorem lemma14_5_12CaseOne_holds : Lemma14_5_12CaseOne := by
  intro G _ _ T L V V₂ Y C hXS3 _ hQ hsolv _ hX1 h311 hGA hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsMulCommutative ↥V := C.isMulCommutative_V
  have S := C.set14
  set H := hY T L V₂ Y with hHdef
  set W := vH T L V V₂ Y with hWdef
  have hWe : IsElemAbelian 2 W := (C.vH_le_center hQ).2
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure _ _
  have hXH : xL L V₂ ⊔ T ≤ H := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hYH : Y ⊔ T ≤ H := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hTH : T ≤ H := le_sup_right
  have hV1W : fsuV1 T V ≤ W := le_conjClosure _ _
  have hV2W : V₂ ≤ W := by
    rw [← C.conjClosure_V1_X]
    exact conjClosure_mono le_rfl (le_sup_left.trans le_sup_left)
  have : Finite (MulAut (IntMod W hWe)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := MulAut (IntMod W hWe)))
  set ψ : ↥H →* MulAut (IntMod W hWe) := (convI hWe).comp (Subgroup.inclusion hHW) with hψ
  have hψ1 : ∀ h : ↥H, ψ h = 1 ↔ (h : G) ∈ Subgroup.centralizer (W : Set G) := fun h =>
    convI_eq_one_iff hWe _
  have hψval : ∀ (h : ↥H) (u : IntMod W hWe), ((ψ h) u).val = (h : G) * u.val * (h : G)⁻¹ :=
    fun h u => convI_apply_val hWe _ u
  have hψv : ∀ (h : ↥H) (w : G) (hw : w ∈ W),
      ((ψ h) (IntMod.mk hWe ⟨w, hw⟩)).val = (h : G) * w * (h : G)⁻¹ := fun h w hw =>
    hψval h _
  have hψS : ∀ h : ↥H, ψ h ∈ autI hWe H := fun h => convI_mem_autI hWe h.2 (hHW h.2)
  have hψS' : ∀ P ∈ autI hWe H, ∃ h : ↥H, ψ h = P := by
    intro P hP
    obtain ⟨g, hg, rfl⟩ := (mem_autI hWe).1 hP
    exact ⟨⟨g, hg⟩, rfl⟩
  have hcomm : ∀ h k : ↥H, ψ h * ψ k = ψ k * ψ h →
      ⁅(h : G), (k : G)⁆ ∈ Subgroup.centralizer (W : Set G) := fun h k hhk => by
    have : ψ ⁅h, k⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hhk
    rw [hψ1] at this
    exact this
  have hNψ : CFSG.pPrimeCore 3 ↥H ≤ ψ.ker := by
    intro h hh
    rw [MonoidHom.mem_ker, hψ1]
    exact h311 ⟨h, hh, rfl⟩
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) with hπ
  set ψ' := QuotientGroup.lift (CFSG.pPrimeCore 3 ↥H) ψ hNψ with hψ'
  have hQX : pCoreOf 2 (xL L V₂ ⊔ T) = pCoreOf 2 H := C.pCoreOf_xT_eq hO
  have hQY : pCoreOf 2 (Y ⊔ T) = pCoreOf 2 H := hO.symm.trans hQX
  have hTC : T ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 H := C.inf_T_eq hXS3 hQ hX1 hO
  have hQC : pCoreOf 2 H ≤ Subgroup.centralizer (W : Set G) := by
    rw [← hTC]
    exact inf_le_right
  have hkerX : ∀ g (hg : g ∈ pCoreOf 2 (xL L V₂ ⊔ T)),
      ψ ⟨g, hXH (pCoreOf_le 2 _ hg)⟩ = 1 := fun g hg =>
    (hψ1 _).mpr (hQC (by rw [← hQX]; exact hg))
  have hkerY : ∀ g (hg : g ∈ pCoreOf 2 (Y ⊔ T)),
      ψ ⟨g, hYH (pCoreOf_le 2 _ hg)⟩ = 1 := fun g hg =>
    (hψ1 _).mpr (hQC (by rw [← hQY]; exact hg))
  have hT2 : Nat.card (autI hWe T) = 2 := by
    rw [card_autI_eq hWe (hTH.trans hHW), hTC, ← hQX]
    exact C.relIndex_pCoreOf_xT hXS3
  obtain ⟨A, hAT, hA, hmax, hAC⟩ := C.exists_J1 hXS3 hX1
  have hAN : A ≤ Subgroup.normalizer (W : Set G) := (hAT.trans hTH).trans hHW
  have hA2 : (A ⊓ Subgroup.centralizer (W : Set G)).relIndex A = 2 := by
    rw [← card_autI_eq hWe hAN]
    have hdvd : Nat.card (autI hWe A) ∣ 2 := by
      rw [← hT2]
      exact Subgroup.card_dvd_of_le (autI_mono hWe hAT)
    have hne : Nat.card (autI hWe A) ≠ 1 := by
      intro h1
      apply hAC
      rw [← autI_eq_bot_iff hWe hAN]
      exact Subgroup.card_eq_one.mp h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hcard4 : Nat.card W ≤ 4 * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) :=
    C.card_le_four_mul hQ hAT hA hmax hA2
  obtain ⟨t₀, ht₀A, ht₀C⟩ := IsConcreteLE.not_le_iff_exists.mp hAC
  have ht₀2 : t₀ ^ 2 = 1 := hA.2 t₀ ht₀A
  have ht₀T : t₀ ∈ T := hAT ht₀A
  set σt := ψ ⟨t₀, hTH ht₀T⟩ with hσt
  have hσt1 : σt ≠ 1 := fun h => ht₀C ((hψ1 _).mp h)
  have hσt2 : σt ^ 2 = 1 := by
    rw [hσt, ← map_pow]
    have : (⟨t₀, hTH ht₀T⟩ : ↥H) ^ 2 = 1 := Subtype.ext (by simpa using ht₀2)
    rw [this, map_one]
  have hσtA : σt ∈ autI hWe A := convI_mem_autI hWe ht₀A (hAN ht₀A)
  have hσtT : σt ∈ autI hWe T := convI_mem_autI hWe ht₀T (hAN ht₀A)
  have hrk : rk (commV (Subgroup.zpowers σt)) ≤ 2 := by
    have hz : Subgroup.zpowers σt = autI hWe A := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hσtA) ?_
      rw [card_autI_eq hWe hAN, hA2, Nat.card_zpowers, orderOf_eq_prime hσt2 hσt1]
    rw [← rkIdx_fixV_zpowers, hz]
    unfold rkIdx
    have e1 := (fixV (autI hWe A)).index_mul_card
    rw [card_fixV_autI hWe hAN] at e1
    have e2 : Nat.card (IntMod W hWe) = Nat.card W := rfl
    rw [e2] at e1
    have hpos : 0 < Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
    have hidx : (fixV (autI hWe A)).index ≤ 4 :=
      Nat.le_of_mul_le_mul_right (e1.le.trans hcard4) hpos
    have hidx0 : (fixV (autI hWe A)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_contra h
    have h8 : 2 ^ 3 ∣ (fixV (autI hWe A)).index :=
      (Nat.pow_dvd_pow 2 (by omega)).trans pow_padicValNat_dvd
    have h8' := Nat.le_of_dvd (Nat.pos_of_ne_zero hidx0) h8
    norm_num at h8'
    omega
  obtain ⟨x₀, hx₀, hx₀o, y, hy, hyo, hb₀⟩ := C.exists_comm_not_mem
  obtain ⟨z, a, x, hz, hz1, ha, haV, hx, hx3, hxz, hxa⟩ := C.exists_rot_X
  have hxXT : x ∈ xL L V₂ ⊔ T := Subgroup.mem_sup_left hx
  have hxo : Odd (orderOf x) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx3)
  have hzW : z ∈ W := hV1W hz
  have haW : a ∈ W := hV2W ha
  have hyY : y ∈ Y := by
    rw [← C.oTwoUpper_yT]
    exact Subgroup.subset_closure ⟨hy, hyo⟩
  have hyz : y * z * y⁻¹ = z := by
    rw [← Subgroup.mem_centralizer_iff.mp (C.le_centralizer_V1 hyY) z hz, mul_inv_cancel_right]
  set hx' : ↥H := ⟨x, hXH hxXT⟩ with hhx'
  set hy' : ↥H := ⟨y, hYH hy⟩ with hhy'
  set hx₀' : ↥H := ⟨x₀, hXH hx₀⟩ with hhx₀'
  set σx := ψ hx' with hσx
  set σy := ψ hy' with hσy
  have hσx1 : σx ≠ 1 := by
    intro h
    rw [hσx, hψ1] at h
    apply haV
    have h2 : x * z = z * x := (Subgroup.mem_centralizer_iff.mp h z hzW).symm
    rw [← hxz, h2, mul_inv_cancel_right]
    exact hz
  obtain ⟨j, hj⟩ := exists_eq_pow_of_odd' hXH hXS3 ψ hkerX hxXT hx₀ hxo hx₀o hσx1
  have hψx₀ : ψ hx₀' = σx ^ j := hj
  have hσy1 : σy ≠ 1 := by
    intro h
    apply hb₀
    refine hcomm hx₀' hy' ?_
    rw [← hσy, h, one_mul, mul_one]
  have hσx3 : σx ^ 3 = 1 := by
    rw [hσx, ← map_pow]
    have : hx' ^ 3 = 1 := Subtype.ext (by simpa [hhx'] using hx3)
    rw [this, map_one]
  have hσy3 : σy ^ 3 = 1 := by
    rw [hσy, ← map_pow]
    have : hy' ^ 3 = 1 := Subtype.ext (by simpa [hhy'] using cube_of_odd C.hS3 hy hyo)
    rw [this, map_one]
  have ht₀Q : t₀ ∉ pCoreOf 2 (xL L V₂ ⊔ T) := fun h => ht₀C (hQC (by rw [← hQX]; exact h))
  have ht₀Q' : t₀ ∉ pCoreOf 2 (Y ⊔ T) := fun h => ht₀C (hQC (by rw [← hQY]; exact h))
  have htx : σt * σx * σt⁻¹ = σx⁻¹ :=
    inv_of_involution' hXH hXS3 ψ hkerX (Subgroup.mem_sup_right ht₀T) hxXT ht₀2 ht₀Q hxo
  have hty : σt * σy * σt⁻¹ = σy⁻¹ :=
    inv_of_involution' hYH C.hS3 ψ hkerY (Subgroup.mem_sup_right ht₀T) hy ht₀2 ht₀Q' hyo
  have hTsyl : IsSylowTwoOf T H := C.isSylowTwoOf_T le_sup_right
  have hSyl := B2F.isSylowTwoOf_autI hWe hHW hTsyl
  have hTS : ∀ u ∈ autI hWe H, ∀ w ∈ autI hWe H, u ^ 2 = 1 → w ^ 2 = 1 → u ≠ 1 → w ≠ 1 →
      u * w = w * u → u = w := by
    intro u hu w hw hu2 hw2 hu1 hw1 huw
    have hKe : IsElemAbelian 2 (Subgroup.closure ({u, w} : Set (MulAut (IntMod W hWe)))) := by
      refine B2F.isElemAbelian_closure ?_ ?_
      · rintro p (rfl | rfl) q (rfl | rfl)
        · rfl
        · exact huw
        · exact huw.symm
        · rfl
      · rintro p (rfl | rfl)
        · exact hu2
        · exact hw2
    have hKH : Subgroup.closure ({u, w} : Set (MulAut (IntMod W hWe))) ≤ autI hWe H := by
      rw [Subgroup.closure_le]
      rintro p (rfl | rfl)
      · exact hu
      · exact hw
    obtain ⟨g, -, hg⟩ :=
      exists_conj_le_of_isSylowTwoOf hSyl hKH (B2F.isPGroup_of_isElemAbelian hKe)
    have hmem : ∀ p ∈ ({u, w} : Set (MulAut (IntMod W hWe))), g * p * g⁻¹ ∈ autI hWe T := by
      intro p hp
      refine hg (mem_cjSub.mpr ?_)
      rw [show g⁻¹ * (g * p * g⁻¹) * g = p by group]
      exact Subgroup.subset_closure hp
    have hne : ∀ p : MulAut (IntMod W hWe), p ≠ 1 → g * p * g⁻¹ ≠ 1 := by
      intro p hp h
      apply hp
      calc p = g⁻¹ * (g * p * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have := eq_of_mem_of_card_eq_two hT2 (hmem u (Set.mem_insert u _))
      (hmem w (Set.mem_insert_of_mem u rfl)) (hne u hu1) (hne w hw1)
    exact mul_left_cancel (mul_right_cancel this)
  have hr : Open.pRank 3 (⊤ : Subgroup ↥H) ≤ 2 :=
    stronglyQuasithin_of_pCoreOf_ne_bot C.hyp.fsu.qtke hQ 3 Nat.prime_three (by norm_num)
  have hsolvD : Group.IsSolvable (↥H ⧸ CFSG.pPrimeCore 3 ↥H) := by
    have := hsolv
    infer_instance
  have hL : twoResidual (((xL L V₂ ⊔ T).subgroupOf H).map π) ≤
      Subgroup.centralizer (opResidual 3 (genFittingFitting (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) :
        Set (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) := by
    refine le_centralizer_opResidual F6.pCore_quotient_pPrimeCore ?_
    intro p hp hp5 e he k _
    rw [pCore_quotient_pPrimeCore_eq_bot hp (by omega), Subgroup.mem_bot] at he
    rw [he, mul_one, one_mul]
  have h23 : ∀ q : ℕ, q.Prime → q ∣ Nat.card (↥H ⧸ CFSG.pPrimeCore 3 ↥H) → q = 2 ∨ q = 3 :=
    fun q hq hqd => F6.prime_eq_two_or_three_of_pRank_le_two hGA.toIsGoldschmidtTriple hsolvD
      π (QuotientGroup.mk'_surjective _) hr (Or.inl hL) hq hqd
  have h5 : ∀ P ∈ autI hWe H, orderOf P ≠ 5 := by
    intro P hP hP5
    obtain ⟨h, rfl⟩ := hψS' P hP
    have h1 : orderOf (ψ h) ∣ Nat.card (↥H ⧸ CFSG.pPrimeCore 3 ↥H) :=
      (orderOf_map_dvd ψ' (π h)).trans (orderOf_dvd_natCard _)
    rw [hP5] at h1
    rcases h23 5 (by norm_num) h1 with he | he <;> omega
  have hV : ∀ w : IntMod W hWe, w ^ 2 = 1 := fun w => IntMod.sq_eq_one (hV := hWe) w
  have hσtS : σt ∈ autI hWe H := hψS _
  have hxy3 : (σx * σy) ^ 3 = 1 :=
    mul_cube_of_inverts hV hTS h5 (hψS hx') (hψS hy') hσtS hσx3 hσy3 hσt2 hσt1 htx hty hrk
  have hxy'3 : (σx * σy⁻¹) ^ 3 = 1 := by
    refine mul_cube_of_inverts hV hTS h5 (hψS hx') ((autI hWe H).inv_mem (hψS hy')) hσtS hσx3
      (by rw [inv_pow, hσy3, inv_one]) hσt2 hσt1 htx ?_ hrk
    rw [inv_inv, show σt * σy⁻¹ * σt⁻¹ = (σt * σy * σt⁻¹)⁻¹ by group, hty, inv_inv]
  set c := ψ ⁅hx', hy'⁆ with hc
  have hc' : c = ⁅σx, σy⁆ := map_commutatorElement ψ hx' hy'
  have hcx : c * σx = σx * c := by
    rw [hc']
    exact (b23_comm_left hσx3 hσy3 hxy3 hxy'3).symm
  have hcy : c * σy = σy * c := by
    rw [hc']
    exact (b23_comm_right hσx3 hσy3 hxy3 hxy'3).symm
  have hc3 : c ^ 3 = 1 := by
    rw [hc']
    exact b23_cube hσx3 hσy3 hxy3 hxy'3
  have hct : c * σt = σt * c := by
    have h1 : σt * c * σt⁻¹ = c := by
      rw [hc', show σt * ⁅σx, σy⁆ * σt⁻¹ = ⁅σt * σx * σt⁻¹, σt * σy * σt⁻¹⁆ by
        simp only [commutatorElement_def]; group, htx, hty, b23_inv_comm hσx3 hσy3 hxy'3]
    calc c * σt = σt * c * σt⁻¹ * σt := by rw [h1]
      _ = σt * c := by group
  set Zc : Subgroup G :=
    ((Subgroup.centralizer ({c} : Set (MulAut (IntMod W hWe)))).comap ψ).map H.subtype with hZc
  have hXZ : xL L V₂ ≤ Zc := by
    rw [← C.oTwoUpper_xT]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hg, hgo⟩
    refine ⟨⟨g, hXH hg⟩, ?_, rfl⟩
    obtain ⟨i, hi⟩ := exists_eq_pow_of_odd' hXH hXS3 ψ hkerX hxXT hg hxo hgo hσx1
    show ψ ⟨g, hXH hg⟩ ∈ Subgroup.centralizer ({c} : Set (MulAut (IntMod W hWe)))
    rw [hi, Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.pow_left (hcx.symm : Commute σx c) i).eq
  have hYZ : Y ≤ Zc := by
    rw [← C.oTwoUpper_yT]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hg, hgo⟩
    refine ⟨⟨g, hYH hg⟩, ?_, rfl⟩
    obtain ⟨i, hi⟩ := exists_eq_pow_of_odd' hYH C.hS3 ψ hkerY hy hg hyo hgo hσy1
    show ψ ⟨g, hYH hg⟩ ∈ Subgroup.centralizer ({c} : Set (MulAut (IntMod W hWe)))
    rw [hi, Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.pow_left (hcy.symm : Commute σy c) i).eq
  have hTZ : T ≤ Zc := by
    intro t' ht'
    refine ⟨⟨t', hTH ht'⟩, ?_, rfl⟩
    show ψ ⟨t', hTH ht'⟩ ∈ Subgroup.centralizer ({c} : Set (MulAut (IntMod W hWe)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases h1 : ψ ⟨t', hTH ht'⟩ = 1
    · rw [h1, one_mul, mul_one]
    · have hmemT : ψ ⟨t', hTH ht'⟩ ∈ autI hWe T := convI_mem_autI hWe ht' (hHW (hTH ht'))
      rw [eq_of_mem_of_card_eq_two hT2 hmemT hσtT h1 hσt1]
      exact hct.symm
  have hHZ : H ≤ Zc := sup_le (sup_le hXZ hYZ) hTZ
  have hcent : ∀ h : ↥H, c * ψ h = ψ h * c := by
    intro h
    obtain ⟨h', hh', he⟩ := hHZ h.2
    obtain rfl : h' = h := Subtype.ext he
    have hh'' : ψ h' ∈ Subgroup.centralizer ({c} : Set (MulAut (IntMod W hWe))) := hh'
    exact (Subgroup.mem_centralizer_singleton_iff.mp hh'').symm
  set v : IntMod W hWe := IntMod.mk hWe ⟨z, hzW⟩ with hv
  have hyv : σy v = v := by
    apply IntMod.val_injective
    rw [hσy, hv, hψv]
    exact hyz
  have hxv : v * σx v * σx (σx v) = 1 := by
    have h1 : σx v = IntMod.mk hWe ⟨a, haW⟩ := by
      apply IntMod.val_injective
      rw [hσx, hv, hψv]
      exact hxz
    have h2 : σx (σx v) = IntMod.mk hWe ⟨z * a, W.mul_mem hzW haW⟩ := by
      apply IntMod.val_injective
      rw [h1, hσx, hψv]
      exact hxa
    rw [h2, h1]
    apply IntMod.val_injective
    simp only [IntMod.val_mul, IntMod.val_one]
    show z * a * (z * a) = 1
    have hza : z * a = a * z := S.comm_V (Subgroup.mem_inf.mp hz).1 (S.hV2.2.1 ha)
    have hz2 : z * z = 1 := S.mul_self_V (Subgroup.mem_inf.mp hz).1
    have ha2 : a * a = 1 := S.mul_self_V (S.hV2.2.1 ha)
    calc z * a * (z * a) = z * (a * z) * a := by group
      _ = z * (z * a) * a := by rw [← hza]
      _ = (z * z) * (a * a) := by group
      _ = 1 := by rw [hz2, ha2, one_mul]
  have hcdef : c = σx * σy * σx⁻¹ * σy⁻¹ := by rw [hc', commutatorElement_def]
  have hcv : c v = v := fix_of_comm_triple hV hcdef hcx hcy hc3 hyv hxv
  have hbz : ∀ h : ↥H, c (ψ h v) = ψ h v := by
    intro h
    rw [← MulAut.mul_apply, hcent h, MulAut.mul_apply, hcv]
  have hWC : W ≤ Subgroup.centralizer ({⁅x, y⁆} : Set G) := by
    refine conjClosure_le fun h hh w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rcases S.eq_of_mem_V1 hz hz1 hw with hw1 | hw1
    · rw [hw1]
      simp
    · rw [hw1]
      have h1 := congrArg IntMod.val (hbz ⟨h, hh⟩)
      rw [hc, hψval, hψval] at h1
      have h2 : ⁅x, y⁆ * (h * z * h⁻¹) * ⁅x, y⁆⁻¹ = h * z * h⁻¹ := h1
      calc ⁅x, y⁆ * (h * z * h⁻¹) = ⁅x, y⁆ * (h * z * h⁻¹) * ⁅x, y⁆⁻¹ * ⁅x, y⁆ := by group
        _ = h * z * h⁻¹ * ⁅x, y⁆ := by rw [h2]
  have hxyC : ⁅x, y⁆ ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWC hw) _ rfl).symm
  apply hb₀
  have h1 : ψ ⁅hx', hy'⁆ = 1 := (hψ1 _).mpr hxyC
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  refine hcomm hx₀' hy' ?_
  rw [hψx₀]
  exact (Commute.pow_left h1 j).eq

end CFSG.Quasithin.H13.L32A.T53

end
