module

public import CFSG.Quasithin.Background.Ordering
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

@[expose] def IsTwoReducedIn (H V : Subgroup G) : Prop :=
  V ≤ H ∧ H ≤ Subgroup.normalizer (V : Set G) ∧ IsElemAbelian 2 V ∧
    ∀ D : Subgroup G, D ≤ H → H ≤ Subgroup.normalizer (D : Set G) →
      (∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ Subgroup.centralizer (V : Set G)) →
      D ≤ Subgroup.centralizer (V : Set G)

@[expose] def centerOf (X : Subgroup G) : Subgroup G := X ⊓ Subgroup.centralizer (X : Set G)

private theorem omegaOneCenter_le_centerOf_self (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1

private theorem pow_eq_one_of_mem_closure {S : Set G} {n : ℕ} (hS : ∀ x ∈ S, x ^ n = 1)
    (hc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x)
    {x : G} (hx : x ∈ Subgroup.closure S) : x ^ n = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact one_pow n
  | mul x y hx hy ihx ihy =>
    rw [Commute.mul_pow (hc x hx y hy) n, ihx, ihy, mul_one]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

private theorem conj_mem_centralizer {S : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (hc : c ∈ Subgroup.centralizer (S : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
  have key := hc _ hs'
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * s := by group

private theorem conj_mem_centerOf {O : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (O : Set G)) (hc : c ∈ centerOf O) :
    g * c * g⁻¹ ∈ centerOf O :=
  ⟨(Subgroup.mem_normalizer_iff.mp hg c).mp hc.1, conj_mem_centralizer hg hc.2⟩

private theorem normalizer_le_normalizer_centralizer (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => conj_mem_centralizer hg hc, fun hc => ?_⟩
  simpa [mul_assoc] using conj_mem_centralizer (inv_mem hg) hc

variable [Finite G]

theorem pCoreOf_two_le_sylow (H : Subgroup G) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) :
    pCoreOf 2 H ≤ T := by
  have : (pCore 2 H).Normal := pCore_normal 2
  have hle : pCore 2 H ≤ (T.subtype hTH : Subgroup H) :=
    (pCore_isPGroup 2).le_sylow_of_normal (T.subtype hTH)
  rintro _ ⟨y, hy, rfl⟩
  have hy' := hle hy
  rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hy'
  exact hy'

theorem omegaOneCenter_le_centerOf_pCoreOf (H : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H)
    (hF : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H) :
    quasithinOmegaOneCenter (T : Subgroup G) ≤ centerOf (pCoreOf 2 H) := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  rintro z ⟨⟨hzT, hzC⟩, -⟩
  have hO : (pCoreOf 2 H : Set G) ⊆ ((T : Subgroup G) : Set G) :=
    pCoreOf_two_le_sylow H T hTH
  have hzC' : z ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := Subgroup.centralizer_le hO hzC
  exact ⟨hF ⟨hTH hzT, hzC'⟩, hzC'⟩

omit [Finite G] in
theorem sq_eq_one_of_mem_omegaOneCenter (T : Subgroup G) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) : z ^ 2 = 1 := by
  have hle := omegaOneCenter_le_centerOf_self T
  refine pow_eq_one_of_mem_closure
    (S := {z | z ∈ T ⊓ Subgroup.centralizer (T : Set G) ∧ z ^ 2 = 1}) (fun x hx => hx.2) ?_ hz
  intro x hx y hy
  exact (hle hy).2 x (hle hx).1

theorem conjClosure_le_centerOf_pCoreOf (H : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H)
    (hF : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H)
    {Z : Subgroup G} (hZ : Z ≤ quasithinOmegaOneCenter (T : Subgroup G)) :
    conjClosure Z H ≤ centerOf (pCoreOf 2 H) ∧ IsElemAbelian 2 (conjClosure Z H) := by
  have hZc : Z ≤ centerOf (pCoreOf 2 H) :=
    hZ.trans (omegaOneCenter_le_centerOf_pCoreOf H T hTH hF)
  have hle : conjClosure Z H ≤ centerOf (pCoreOf 2 H) :=
    conjClosure_le fun h hh z hz => conj_mem_centerOf (le_normalizer_pCoreOf 2 H hh) (hZc hz)
  have hcomm : ∀ x ∈ conjClosure Z H, ∀ y ∈ conjClosure Z H, x * y = y * x :=
    fun x hx y hy => (hle hy).2 x (hle hx).1
  refine ⟨hle, ⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, fun x hx => ?_⟩
  refine pow_eq_one_of_mem_closure
    (S := {x | ∃ h ∈ H, ∃ z ∈ Z, h * z * h⁻¹ = x}) ?_ hcomm hx
  rintro _ ⟨h, -, z, hz, rfl⟩
  rw [conj_pow, sq_eq_one_of_mem_omegaOneCenter _ (hZ hz), mul_one, mul_inv_cancel]

omit [Finite G] in
private theorem relIndex_sup_eq_of_le_normalizer {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

private theorem not_two_dvd_relIndex_inf {S D : Subgroup G} (hS : ¬ 2 ∣ S.index)
    (hSN : S ≤ Subgroup.normalizer (D : Set G)) : ¬ 2 ∣ (S ⊓ D).relIndex D := by
  have h1 : (S ⊓ D).relIndex S * S.relIndex (S ⊔ D) = (S ⊓ D).relIndex (S ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have h2 : (S ⊓ D).relIndex D * D.relIndex (S ⊔ D) = (S ⊓ D).relIndex (S ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h3 : D.relIndex (S ⊔ D) = (S ⊓ D).relIndex S :=
    (relIndex_sup_eq_of_le_normalizer hSN).trans (Subgroup.inf_relIndex_left S D).symm
  have h4 : 0 < (S ⊓ D).relIndex S :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ((S ⊓ D).subgroupOf S)))
  have h5 : (S ⊓ D).relIndex D = S.relIndex (S ⊔ D) := by
    refine Nat.eq_of_mul_eq_mul_left h4 ?_
    rw [h3] at h2
    rw [mul_comm ((S ⊓ D).relIndex S) ((S ⊓ D).relIndex D), h2, ← h1]
  rw [h5]
  exact fun h => hS (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))

private theorem exists_relIndex_eq_two_pow {K D : Subgroup G}
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ K) :
    ∃ n : ℕ, K.relIndex D = 2 ^ n := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hDK
  have hp : IsPGroup 2 (D ⧸ K.subgroupOf D) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H d =>
      obtain ⟨k, hk⟩ := hD d d.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  exact ⟨n, hn⟩

private theorem le_sup_inf_of_two_power {K D : Subgroup G} (T : Sylow 2 G)
    (hTD : (T : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ K) :
    D ≤ (K ⊓ D) ⊔ ((T : Subgroup G) ⊓ D) := by
  obtain ⟨n, hn⟩ := exists_relIndex_eq_two_pow hDK hD
  have hodd := not_two_dvd_relIndex_inf T.not_dvd_index hTD
  rw [← Subgroup.relIndex_eq_one]
  have h1 : ((K ⊓ D) ⊔ ((T : Subgroup G) ⊓ D)).relIndex D ∣ 2 ^ n :=
    ((Subgroup.inf_relIndex_right K D).trans hn) ▸ Subgroup.relIndex_dvd_of_le_left D le_sup_left
  have h2 : ((K ⊓ D) ⊔ ((T : Subgroup G) ⊓ D)).relIndex D ∣ ((T : Subgroup G) ⊓ D).relIndex D :=
    Subgroup.relIndex_dvd_of_le_left D le_sup_right
  have hcop : Nat.Coprime (2 ^ n) (((T : Subgroup G) ⊓ D).relIndex D) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  exact Nat.eq_one_of_dvd_coprimes hcop h1 h2

theorem isTwoReducedIn_conjClosure (H : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H)
    (hF : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H)
    {Z : Subgroup G} (hZ : Z ≤ quasithinOmegaOneCenter (T : Subgroup G)) :
    IsTwoReducedIn H (conjClosure Z H) := by
  obtain ⟨hle, hel⟩ := conjClosure_le_centerOf_pCoreOf H T hTH hF hZ
  refine ⟨hle.trans (inf_le_left.trans (pCoreOf_le 2 H)), le_normalizer_conjClosure Z H, hel, ?_⟩
  intro D hDH hDN hD
  have hTZ : (T : Subgroup G) ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.mp
      ((hZ.trans (omegaOneCenter_le_centerOf_self _)).trans inf_le_right)
  have hDle := le_sup_inf_of_two_power T (hTH.trans hDN)
    (hDH.trans ((le_normalizer_conjClosure Z H).trans (normalizer_le_normalizer_centralizer _))) hD
  have hDZ : D ≤ Subgroup.centralizer (Z : Set G) :=
    hDle.trans (sup_le (inf_le_left.trans (Subgroup.centralizer_le (le_conjClosure Z H)))
      (inf_le_left.trans hTZ))
  rw [Subgroup.le_centralizer_iff]
  refine conjClosure_le fun h hh z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : h⁻¹ * d * h ∈ D := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hDN (H.inv_mem hh)) d).mp hd
  have hcomm : z * (h⁻¹ * d * h) = (h⁻¹ * d * h) * z := hDZ hd' z hz
  calc d * (h * z * h⁻¹) = h * ((h⁻¹ * d * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * d * h)) * h⁻¹ := by rw [hcomm]
    _ = h * z * h⁻¹ * d := by group

theorem pCoreOf_two_le_of_sylowIn {H T : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (hTodd : ¬ 2 ∣ T.relIndex H) : pCoreOf 2 H ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (T.subgroupOf H) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have : (pCore 2 H).Normal := pCore_normal 2
  have hle : pCore 2 H ≤ T.subgroupOf H := by
    have := (pCore_isPGroup 2 (G := H)).le_sylow_of_normal (hp.toSylow hTodd)
    rwa [IsPGroup.toSylow_coe hp hTodd] at this
  rintro _ ⟨y, hy, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (hle hy)

theorem omegaOneCenter_le_centerOf_pCoreOf_of_sylowIn {H T : Subgroup G} (hTH : T ≤ H)
    (hT2 : IsPGroup 2 T) (hTodd : ¬ 2 ∣ T.relIndex H)
    (hF : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H) :
    quasithinOmegaOneCenter T ≤ centerOf (pCoreOf 2 H) := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  rintro z ⟨⟨hzT, hzC⟩, -⟩
  have hO : (pCoreOf 2 H : Set G) ⊆ (T : Set G) := pCoreOf_two_le_of_sylowIn hTH hT2 hTodd
  have hzC' : z ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := Subgroup.centralizer_le hO hzC
  exact ⟨hF ⟨hTH hzT, hzC'⟩, hzC'⟩

theorem conjClosure_le_centerOf_pCoreOf_of_sylowIn {H T : Subgroup G} (hTH : T ≤ H)
    (hT2 : IsPGroup 2 T) (hTodd : ¬ 2 ∣ T.relIndex H)
    (hF : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H)
    {Z : Subgroup G} (hZ : Z ≤ quasithinOmegaOneCenter T) :
    conjClosure Z H ≤ centerOf (pCoreOf 2 H) ∧ IsElemAbelian 2 (conjClosure Z H) := by
  have hZc : Z ≤ centerOf (pCoreOf 2 H) :=
    hZ.trans (omegaOneCenter_le_centerOf_pCoreOf_of_sylowIn hTH hT2 hTodd hF)
  have hle : conjClosure Z H ≤ centerOf (pCoreOf 2 H) :=
    conjClosure_le fun h hh z hz => conj_mem_centerOf (le_normalizer_pCoreOf 2 H hh) (hZc hz)
  have hcomm : ∀ x ∈ conjClosure Z H, ∀ y ∈ conjClosure Z H, x * y = y * x :=
    fun x hx y hy => (hle hy).2 x (hle hx).1
  refine ⟨hle, ⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, fun x hx => ?_⟩
  refine pow_eq_one_of_mem_closure
    (S := {x | ∃ h ∈ H, ∃ z ∈ Z, h * z * h⁻¹ = x}) ?_ hcomm hx
  rintro _ ⟨h, -, z, hz, rfl⟩
  rw [conj_pow, sq_eq_one_of_mem_omegaOneCenter _ (hZ hz), mul_one, mul_inv_cancel]

private theorem not_two_dvd_relIndex_inf_of_le {H S D : Subgroup G} (hSH : S ≤ H) (hDH : D ≤ H)
    (hS : ¬ 2 ∣ S.relIndex H) (hSN : S ≤ Subgroup.normalizer (D : Set G)) :
    ¬ 2 ∣ (S ⊓ D).relIndex D := by
  have h1 : (S ⊓ D).relIndex S * S.relIndex (S ⊔ D) = (S ⊓ D).relIndex (S ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have h2 : (S ⊓ D).relIndex D * D.relIndex (S ⊔ D) = (S ⊓ D).relIndex (S ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h3 : D.relIndex (S ⊔ D) = (S ⊓ D).relIndex S :=
    (relIndex_sup_eq_of_le_normalizer hSN).trans (Subgroup.inf_relIndex_left S D).symm
  have h4 : 0 < (S ⊓ D).relIndex S :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ((S ⊓ D).subgroupOf S)))
  have h5 : (S ⊓ D).relIndex D = S.relIndex (S ⊔ D) := by
    refine Nat.eq_of_mul_eq_mul_left h4 ?_
    rw [h3] at h2
    rw [mul_comm ((S ⊓ D).relIndex S) ((S ⊓ D).relIndex D), h2, ← h1]
  rw [h5]
  have h6 : S.relIndex (S ⊔ D) * (S ⊔ D).relIndex H = S.relIndex H :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hSH hDH)
  exact fun h => hS (h6 ▸ dvd_mul_of_dvd_left h _)

private theorem le_sup_inf_of_two_power_of_sylowIn {H T K D : Subgroup G} (hTH : T ≤ H)
    (hDH : D ≤ H) (hTodd : ¬ 2 ∣ T.relIndex H)
    (hTD : T ≤ Subgroup.normalizer (D : Set G))
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ K) :
    D ≤ (K ⊓ D) ⊔ (T ⊓ D) := by
  obtain ⟨n, hn⟩ := exists_relIndex_eq_two_pow hDK hD
  have hodd := not_two_dvd_relIndex_inf_of_le hTH hDH hTodd hTD
  rw [← Subgroup.relIndex_eq_one]
  have h1 : ((K ⊓ D) ⊔ (T ⊓ D)).relIndex D ∣ 2 ^ n :=
    ((Subgroup.inf_relIndex_right K D).trans hn) ▸ Subgroup.relIndex_dvd_of_le_left D le_sup_left
  have h2 : ((K ⊓ D) ⊔ (T ⊓ D)).relIndex D ∣ (T ⊓ D).relIndex D :=
    Subgroup.relIndex_dvd_of_le_left D le_sup_right
  have hcop : Nat.Coprime (2 ^ n) ((T ⊓ D).relIndex D) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  exact Nat.eq_one_of_dvd_coprimes hcop h1 h2

theorem isTwoReducedIn_conjClosure_of_sylowIn {H T : Subgroup G} (hTH : T ≤ H)
    (hT2 : IsPGroup 2 T) (hTodd : ¬ 2 ∣ T.relIndex H)
    (hF : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H)
    {Z : Subgroup G} (hZ : Z ≤ quasithinOmegaOneCenter T) :
    IsTwoReducedIn H (conjClosure Z H) := by
  obtain ⟨hle, hel⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hTH hT2 hTodd hF hZ
  refine ⟨hle.trans (inf_le_left.trans (pCoreOf_le 2 H)), le_normalizer_conjClosure Z H, hel, ?_⟩
  intro D hDH hDN hD
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.mp
      ((hZ.trans (omegaOneCenter_le_centerOf_self _)).trans inf_le_right)
  have hDle := le_sup_inf_of_two_power_of_sylowIn hTH hDH hTodd (hTH.trans hDN)
    (hDH.trans ((le_normalizer_conjClosure Z H).trans (normalizer_le_normalizer_centralizer _))) hD
  have hDZ : D ≤ Subgroup.centralizer (Z : Set G) :=
    hDle.trans (sup_le (inf_le_left.trans (Subgroup.centralizer_le (le_conjClosure Z H)))
      (inf_le_left.trans hTZ))
  rw [Subgroup.le_centralizer_iff]
  refine conjClosure_le fun h hh z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : h⁻¹ * d * h ∈ D := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hDN (H.inv_mem hh)) d).mp hd
  have hcomm : z * (h⁻¹ * d * h) = (h⁻¹ * d * h) * z := hDZ hd' z hz
  calc d * (h * z * h⁻¹) = h * ((h⁻¹ * d * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * d * h)) * h⁻¹ := by rw [hcomm]
    _ = h * z * h⁻¹ * d := by group

end CFSG.Quasithin
