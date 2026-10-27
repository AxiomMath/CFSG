module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem838KG
public import CFSG.Quasithin.Background.PSL2TwoNilpotent
public import CFSG.Quasithin.H13.NParamRootFourLift

public section

namespace CFSG.Quasithin.H13.Ch838

open CFSG.Open CFSG.Quasithin.E1.LiftS5

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_of_pow_mem_of_twoResidual_eq {I N : Subgroup G} (hI : twoResidual I = I)
    (hIN : I ≤ Subgroup.normalizer (N : Set G)) (h2 : ∀ y ∈ I, ∃ k : ℕ, y ^ 2 ^ k ∈ N) :
    I ≤ N := by
  have h := twoResidual_le_of_isTwoQuotient (H := I) (N := N ⊓ I) inf_le_right
    (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hIN hg, Subgroup.le_normalizer hg⟩)
    (fun y hy => by
      obtain ⟨k, hk⟩ := h2 y hy
      exact ⟨k, hk, I.pow_mem hy _⟩)
  rw [hI] at h
  exact h.trans inf_le_left

omit [Finite G] in
theorem le_normalizer_map_comap {N : Subgroup G} {Q : Type*} [Group Q] (A : ↥N →* Q)
    {B : Subgroup Q} (hB : B.Normal) :
    N ≤ Subgroup.normalizer (((B.comap A).map N.subtype : Subgroup G) : Set G) := by
  have hn : (B.comap A).Normal := hB.comap A
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, hn.conj_mem y' hy' _, rfl⟩
  · rintro ⟨y', hy', hye⟩
    refine ⟨⟨x, hx⟩⁻¹ * y' * ⟨x, hx⟩, ?_, ?_⟩
    · have := hn.conj_mem y' hy' ⟨x, hx⟩⁻¹
      rwa [inv_inv] at this
    · change x⁻¹ * N.subtype y' * x = y
      rw [hye]
      group

theorem range_conj_normal (Q : Type*) [Group Q] : (MulAut.conj : Q →* MulAut Q).range.Normal := by
  refine ⟨fun x hx f => ?_⟩
  obtain ⟨k, rfl⟩ := hx
  refine ⟨f k, ?_⟩
  ext y
  change f k * y * (f k)⁻¹ = f (k * f⁻¹ y * k⁻¹)
  rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]

omit [Finite G] in
theorem quotConj_mem_range {K I : Subgroup G} (hOut : OutIsTwoGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hIK : I ≤ Subgroup.normalizer (K : Set G)) (hI : twoResidual I = I)
    (g : ↥(Subgroup.normalizer (K : Set G))) (hg : (g : G) ∈ I) :
    quotConj K g ∈ (MulAut.conj : _ →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K)).range := by
  set Inn := (MulAut.conj : _ →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K)).range with hInn
  set N₀ : Subgroup G := (Inn.comap (quotConj K)).map (Subgroup.normalizer (K : Set G)).subtype
    with hN₀
  have hle : I ≤ N₀ := by
    refine le_of_pow_mem_of_twoResidual_eq hI
      (hIK.trans (le_normalizer_map_comap _ (range_conj_normal _))) fun y hy => ?_
    obtain ⟨k, hk⟩ := hOut (quotConj K ⟨y, hIK hy⟩)
    have hmem : (⟨y, hIK hy⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ k ∈
        Inn.comap (quotConj K) := by
      rw [Subgroup.mem_comap, map_pow]
      exact hk
    exact ⟨k, Subgroup.mem_map.mpr ⟨_, hmem, by simp⟩⟩
  obtain ⟨g', hg', hg'e⟩ := hle hg
  have : g' = g := Subtype.ext hg'e
  rw [← this]
  exact hg'

@[expose] noncomputable def projQ (K I : Subgroup G) : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
  ((I.subgroupOf (Subgroup.normalizer (K : Set G))).map (quotConj K)).comap MulAut.conj

omit [Finite G] in
theorem mem_projQ {K I : Subgroup G} {x : ↥K ⧸ CFSG.pCore 2 ↥K} :
    x ∈ projQ K I ↔ ∃ g : ↥(Subgroup.normalizer (K : Set G)), (g : G) ∈ I ∧
      quotConj K g = MulAut.conj x := by
  simp only [projQ, Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem conj_injective_of_center_eq_bot {Q : Type*} [Group Q] (hcen : Subgroup.center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : x ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut Q => φ y) hx
    change x * y * x⁻¹ = y at this
    calc y * x = x * y * x⁻¹ * x := by rw [this]
      _ = x * y := by group
  rw [hcen, Subgroup.mem_bot] at hxc
  exact hxc

omit [Finite G] in
theorem map_conj_projQ {K I : Subgroup G} (hOut : OutIsTwoGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hIK : I ≤ Subgroup.normalizer (K : Set G)) (hI : twoResidual I = I) :
    (projQ K I).map MulAut.conj =
      (I.subgroupOf (Subgroup.normalizer (K : Set G))).map (quotConj K) := by
  refine Subgroup.map_comap_eq_self ?_
  rintro _ ⟨g, hg, rfl⟩
  exact quotConj_mem_range hOut hIK hI g hg

omit [Finite G] in
theorem card_projQ_dvd {K I : Subgroup G} (hOut : OutIsTwoGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hcen : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hIK : I ≤ Subgroup.normalizer (K : Set G)) (hI : twoResidual I = I) :
    Nat.card (projQ K I) ∣ Nat.card I := by
  have h1 : Nat.card ↥((projQ K I).map MulAut.conj) = Nat.card (projQ K I) :=
    (Nat.card_congr ((projQ K I).equivMapOfInjective MulAut.conj
      (conj_injective_of_center_eq_bot hcen)).toEquiv).symm
  rw [map_conj_projQ hOut hIK hI] at h1
  rw [← h1]
  refine (Subgroup.card_map_dvd _ _).trans ?_
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIK).toEquiv).dvd

omit [Finite G] in
theorem le_normalizer_projQ {K I S : Subgroup G} (hSK : S ≤ K)
    (hSI : S ≤ Subgroup.normalizer (I : Set G)) :
    (S.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ≤
      Subgroup.normalizer ((projQ K I : Subgroup _) : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  have hKN : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
  have key : ∀ (s : G) (hs : s ∈ S), ∀ x ∈ projQ K I,
      (QuotientGroup.mk' _ ⟨s, hSK hs⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) * x *
        (QuotientGroup.mk' _ ⟨s, hSK hs⟩)⁻¹ ∈ projQ K I := by
    intro s hs x hx
    obtain ⟨g, hgI, hg⟩ := mem_projQ.mp hx
    rw [mem_projQ]
    refine ⟨⟨s, hKN (hSK hs)⟩ * g * ⟨s, hKN (hSK hs)⟩⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hSI hs) g).mp hgI, ?_⟩
    rw [map_mul, map_mul, map_inv, hg, quotConj_of_mem K _ (hSK hs), map_mul, map_mul, map_inv]
    rfl
  rintro _ ⟨⟨s, hsK⟩, hs, rfl⟩
  have hs' : s ∈ S := hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key s hs' x, fun h => ?_⟩
  have := key s⁻¹ (S.inv_mem hs') _ h
  have e : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨s⁻¹, hSK (S.inv_mem hs')⟩ :
      ↥K ⧸ CFSG.pCore 2 ↥K) = (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨s, hsK⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e] at this
  simpa [mul_assoc] using this

theorem twoNilpotent_of_isPGroup {A : Type*} [Group A] (h : IsPGroup 2 A) : TwoNilpotent A := by
  refine ⟨⊥, inferInstance, by rw [Subgroup.card_bot]; exact odd_one, fun a => ?_⟩
  obtain ⟨k, hk⟩ := h a
  exact ⟨k, by rw [hk]; exact Subgroup.one_mem _⟩

omit [Finite G] in
theorem quotConj_eq_one_of_twoNilpotent {K I : Subgroup G}
    (hOut : OutIsTwoGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hcen : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hIK : I ≤ Subgroup.normalizer (K : Set G)) (hI : twoResidual I = I)
    (hnil : TwoNilpotent ↥(projQ K I)) (g : ↥(Subgroup.normalizer (K : Set G)))
    (hg : (g : G) ∈ I) {n : ℕ} (hgn : (g : G) ^ 2 ^ n = 1) : quotConj K g = 1 := by
  obtain ⟨O, hO, hodd, h2⟩ := hnil
  have hinj := conj_injective_of_center_eq_bot hcen
  let O' : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := O.map (projQ K I).subtype
  have hrep : ∀ h : ↥(Subgroup.normalizer (K : Set G)), (h : G) ∈ I →
      ∃ y ∈ projQ K I, quotConj K h = MulAut.conj y := by
    intro h hh
    obtain ⟨y, hy⟩ := quotConj_mem_range hOut hIK hI h hh
    exact ⟨y, mem_projQ.mpr ⟨h, hh, hy.symm⟩, hy.symm⟩
  have hconjO : ∀ y ∈ projQ K I, ∀ o ∈ O', y * o * y⁻¹ ∈ O' := by
    rintro y hy _ ⟨o, ho, rfl⟩
    exact ⟨⟨y, hy⟩ * o * ⟨y, hy⟩⁻¹, hO.conj_mem o ho _, rfl⟩
  let Nx : Subgroup G := ((O'.map MulAut.conj).comap (quotConj K)).map
    (Subgroup.normalizer (K : Set G)).subtype
  have hmemNx : ∀ x : ↥(Subgroup.normalizer (K : Set G)),
      (∃ o ∈ O', quotConj K x = MulAut.conj o) → (x : G) ∈ Nx := by
    rintro x ⟨o, ho, hxo⟩
    exact ⟨x, ⟨o, ho, hxo.symm⟩, rfl⟩
  have hNxmem : ∀ x ∈ Nx, ∃ hx : x ∈ Subgroup.normalizer (K : Set G), ∃ o ∈ O',
      quotConj K ⟨x, hx⟩ = MulAut.conj o := by
    rintro _ ⟨x, ⟨o, ho, hxo⟩, rfl⟩
    exact ⟨x.2, o, ho, hxo.symm⟩
  have hINx : I ≤ Subgroup.normalizer (Nx : Set G) := by
    have key : ∀ h ∈ I, ∀ x ∈ Nx, h * x * h⁻¹ ∈ Nx := by
      intro h hh x hx
      obtain ⟨hxN, o, ho, hxo⟩ := hNxmem x hx
      obtain ⟨y, hyY, hyh⟩ := hrep ⟨h, hIK hh⟩ hh
      refine hmemNx (⟨h, hIK hh⟩ * ⟨x, hxN⟩ * ⟨h, hIK hh⟩⁻¹)
        ⟨y * o * y⁻¹, hconjO y hyY o ho, ?_⟩
      rw [map_mul, map_mul, map_inv, hyh, hxo, map_mul, map_mul, map_inv]
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key h hh x, fun hx => ?_⟩
    have := key h⁻¹ (I.inv_mem hh) _ hx
    simpa [mul_assoc] using this
  have hle : I ≤ Nx := by
    refine le_of_pow_mem_of_twoResidual_eq hI hINx fun h hh => ?_
    obtain ⟨y, hyY, hyh⟩ := hrep ⟨h, hIK hh⟩ hh
    obtain ⟨k, hk⟩ := h2 ⟨y, hyY⟩
    refine ⟨k, hmemNx (⟨h, hIK hh⟩ ^ 2 ^ k) ⟨y ^ 2 ^ k, ⟨_, hk, rfl⟩, ?_⟩⟩
    rw [map_pow, hyh, map_pow]
  obtain ⟨hgN, o, ho, hgo⟩ := hNxmem _ (hle hg)
  have hgg : (⟨(g : G), hgN⟩ : ↥(Subgroup.normalizer (K : Set G))) = g := rfl
  rw [hgg] at hgo
  rw [hgo]
  have ho1 : o = 1 := by
    have h1 : MulAut.conj (o ^ 2 ^ n) = 1 := by
      rw [map_pow, ← hgo, ← map_pow]
      have : g ^ 2 ^ n = 1 := Subtype.ext hgn
      rw [this, map_one]
    have h2o : o ^ 2 ^ n = 1 := hinj (h1.trans (map_one _).symm)
    have h3 : orderOf o ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2o
    have h4 : orderOf o ∣ Nat.card O := by
      obtain ⟨o₀, ho₀, rfl⟩ := ho
      have e1 : orderOf ((projQ K I).subtype o₀) = orderOf o₀ := Subgroup.orderOf_coe o₀
      have e2 : orderOf (⟨o₀, ho₀⟩ : ↥O) = orderOf o₀ := Subgroup.orderOf_mk o₀ ho₀
      rw [e1, ← e2]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ n) (Nat.card O) := by
      refine Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr hodd
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h3 h4)
  rw [ho1, map_one]

theorem le_pCoreOf_sup_of_commutator_mem {D T W : Subgroup G} (hT : IsPGroup 2 T)
    (hTD : T ≤ Subgroup.normalizer (D : Set G)) (hWT : W ≤ T)
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hW : ∀ w ∈ W, ∀ d ∈ D, w * d * w⁻¹ * d⁻¹ ∈ pCoreOf 2 D) : W ≤ pCoreOf 2 (D ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pCoreOf 2 D with hOdef
  have hDO : D ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D
  have hTO : T ≤ Subgroup.normalizer (O : Set G) :=
    hTD.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D)
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D
  have hQ2 : IsPGroup 2 ↥(W ⊔ O) :=
    IsPGroup.to_sup_of_normal_right' (hT.to_le hWT) hO2 (hWT.trans hTO)
  have hQle : W ⊔ O ≤ D ⊔ T :=
    sup_le (hWT.trans le_sup_right) ((CFSG.LieType.BorelTits.pCoreOf_le 2 D).trans le_sup_left)
  have hD : ∀ d ∈ D, ∀ q ∈ W ⊔ O, d * q * d⁻¹ ∈ W ⊔ O := by
    intro d hd
    have h1 : W ⊔ O ≤ (W ⊔ O).comap (MulAut.conj d).toMonoidHom := by
      refine sup_le (fun w hw => ?_) (fun o ho => ?_)
      · change d * w * d⁻¹ ∈ W ⊔ O
        have h2 := hW w⁻¹ (W.inv_mem hw) d hd
        rw [inv_inv] at h2
        have e : d * w * d⁻¹ = w * (w⁻¹ * d * w * d⁻¹) := by group
        rw [e]
        exact (W ⊔ O).mul_mem (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right h2)
      · change d * o * d⁻¹ ∈ W ⊔ O
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hDO hd) o).mp ho)
    exact fun q hq => h1 hq
  have hT' : ∀ t ∈ T, ∀ q ∈ W ⊔ O, t * q * t⁻¹ ∈ W ⊔ O := by
    intro t ht
    have h1 : W ⊔ O ≤ (W ⊔ O).comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (fun w hw => ?_) (fun o ho => ?_)
      · change t * w * t⁻¹ ∈ W ⊔ O
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hTW ht) w).mp hw)
      · change t * o * t⁻¹ ∈ W ⊔ O
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hTO ht) o).mp ho)
    exact fun q hq => h1 hq
  have hnorm : D ⊔ T ≤ Subgroup.normalizer ((W ⊔ O : Subgroup G) : Set G) := by
    have hle : ∀ X : Subgroup G, (∀ x ∈ X, ∀ q ∈ W ⊔ O, x * q * x⁻¹ ∈ W ⊔ O) →
        X ≤ Subgroup.normalizer ((W ⊔ O : Subgroup G) : Set G) := by
      intro X hX x hx
      rw [Subgroup.mem_normalizer_iff]
      intro q
      refine ⟨hX x hx q, fun h => ?_⟩
      have := hX x⁻¹ (X.inv_mem hx) _ h
      simpa [mul_assoc] using this
    exact sup_le (hle D hD) (hle T hT')
  exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQle hnorm hQ2)

end CFSG.Quasithin.H13.Ch838
