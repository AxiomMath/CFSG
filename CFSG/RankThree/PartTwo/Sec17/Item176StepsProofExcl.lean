module

public import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTools
public import CFSG.RankThree.PartTwo.Sec17.Item176ProofOne
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof
import CFSG.RankThree.PartTwo.KFacts.KS18A7M22Proof
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

@[expose] def KS176GTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec4.IsoGTwoPrime X → ∀ Z : Subgroup X, Nat.card Z = 3 →
    (∀ g : X, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set X) →
      Z.map (MulAut.conj g).toMonoidHom = Z) →
    Proof176Steps.HasCommOfZ Z

namespace Proof176Steps

variable {G : Type} [Group G] [Finite G]

theorem hasCommOfZ_of_j2
    {X : Type} [Group X]
    [Finite X] (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {Z : Subgroup X}
    (hZ3 : Nat.card Z = 3)
    (hwc : ∀ g : X, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set X) →
      Z.map (MulAut.conj g).toMonoidHom = Z) : HasCommOfZ Z := by
  refine hasCommOfZ_of_sylow (fun P => ?_) hZ3 hwc
  obtain ⟨⟨⟨⟨-, hcomm, -, hcen⟩, -, hexp⟩, -⟩, -⟩ := Sec4.Sporadic.rank3II_4_15 X hX P _ rfl _ rfl
  refine ⟨hcomm, hcen, fun x hx => ?_⟩
  have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥(P : Subgroup X))
  rw [hexp] at h
  exact congrArg Subtype.val h

theorem exists_lift_of_hasComm {K : Subgroup G} {c : G} (hc : orderOf c = 3) (hcK : c ∈ K)
    (h : HasCommOfZ ((Subgroup.zpowers (⟨c, hcK⟩ : ↥K)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)))) :
    ∃ x y : G, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * c = c * x ∧ y * c = c * y ∧
      ⁅x, y⁆ ∈ Subgroup.zpowers c ∧ ⁅x, y⁆ ≠ 1 ∧
      IsPGroup 3 (Subgroup.closure ({x, y} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pPrimeCore 3 ↥K with hN
  set π := QuotientGroup.mk' N with hπ
  set c' : ↥K := ⟨c, hcK⟩ with hc'
  obtain ⟨x, y, hx3, hy3, hxc, hyc, hxyZ, hxy1, hp⟩ := h
  set R := Subgroup.closure ({x, y} : Set (↥K ⧸ N)) with hR
  have hZeq : (Subgroup.zpowers c').map π = Subgroup.zpowers (π c') := MonoidHom.map_zpowers π c'
  have hxR : x ∈ R := Subgroup.subset_closure (by simp)
  have hyR : y ∈ R := Subgroup.subset_closure (by simp)
  have hxyR : ⁅x, y⁆ ∈ R := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxR hyR) (inv_mem hxR)) (inv_mem hyR)
  have h3 : Nat.card (Subgroup.zpowers (π c')) = 3 := by
    rw [← hZeq]
    exact Proof176.card_map_zpowers hc hcK
  have hcR : π c' ∈ R := by
    have hxyZ' : ⁅x, y⁆ ∈ Subgroup.zpowers (π c') := hZeq ▸ hxyZ
    have heq := eq_zpowers_of_card_three h3 hxyZ' hxy1
    have hmem : π c' ∈ Subgroup.zpowers ⁅x, y⁆ := heq ▸ Subgroup.mem_zpowers _
    exact (Subgroup.zpowers_le.mpr hxyR) hmem
  set W := R.comap π with hW
  have hc'W : Subgroup.zpowers c' ≤ W := Subgroup.zpowers_le.mpr hcR
  have hc'o : orderOf c' = 3 := (Proof176.orderOf_mk_eq hcK).trans hc
  have hc'3 : IsPGroup 3 (Subgroup.zpowers c') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc'o, pow_one])
  obtain ⟨S, hS, hcS⟩ := Item134SylowBarProof.exists_isSylowOf_le hc'W hc'3
  have hc'S : c' ∈ S := hcS (Subgroup.mem_zpowers c')
  have hSR : ∀ r ∈ R, ∃ s ∈ S, π s = r := by
    obtain ⟨Q, hQ⟩ := hS
    set f : ↥W →* ↥R := (π.comp W.subtype).codRestrict R (fun w => w.2) with hf
    have hfs : Function.Surjective f := by
      rintro ⟨r, hr⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N r
      exact ⟨⟨k, hr⟩, rfl⟩
    set Q' : Sylow 3 ↥R := Q.mapSurjective hfs with hQ'
    have htop : (Q' : Subgroup ↥R) = ⊤ :=
      (Q'.3 (hp.of_equiv Subgroup.topEquiv.symm) le_top).symm
    intro r hr
    have hmem : (⟨r, hr⟩ : ↥R) ∈ (Q' : Subgroup ↥R) := htop ▸ Subgroup.mem_top _
    rw [hQ', Sylow.coe_mapSurjective] at hmem
    obtain ⟨q, hq, hqr⟩ := hmem
    exact ⟨q, hQ ▸ ⟨q, hq, rfl⟩, congrArg Subtype.val hqr⟩
  have hinj : Set.InjOn π (S : Set ↥K) := Proof176.injOn_mk_pPrimeCore hS.isPGroup
  obtain ⟨x', hx'S, hx'⟩ := hSR x hxR
  obtain ⟨y', hy'S, hy'⟩ := hSR y hyR
  have hcZ : π c' ∈ (Subgroup.zpowers c').map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_zpowers c')
  have hx'3 : x' ^ 3 = 1 :=
    hinj (pow_mem hx'S 3) (one_mem S) (by rw [map_pow, hx', hx3, map_one])
  have hy'3 : y' ^ 3 = 1 :=
    hinj (pow_mem hy'S 3) (one_mem S) (by rw [map_pow, hy', hy3, map_one])
  have hx'c : x' * c' = c' * x' := by
    refine hinj (mul_mem hx'S hc'S) (mul_mem hc'S hx'S) ?_
    rw [map_mul, map_mul, hx']
    exact (Subgroup.mem_centralizer_iff.mp hxc (π c') hcZ).symm
  have hy'c : y' * c' = c' * y' := by
    refine hinj (mul_mem hy'S hc'S) (mul_mem hc'S hy'S) ?_
    rw [map_mul, map_mul, hy']
    exact (Subgroup.mem_centralizer_iff.mp hyc (π c') hcZ).symm
  obtain ⟨z, hz, hzxy⟩ := hxyZ
  have hzS : z ∈ S := hcS hz
  have hcomS : ⁅x', y'⁆ ∈ S := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx'S hy'S) (inv_mem hx'S)) (inv_mem hy'S)
  have hπcom : π ⁅x', y'⁆ = ⁅x, y⁆ := by
    rw [commutatorElement_def, commutatorElement_def, map_mul, map_mul, map_mul, map_inv,
      map_inv, hx', hy']
  have hcomz : ⁅x', y'⁆ = z := hinj hcomS hzS (by rw [hπcom, hzxy])
  have hcom1 : ⁅x', y'⁆ ≠ 1 := fun h1 => hxy1 (by rw [← hπcom, h1, map_one])
  have hcl : Subgroup.closure ({(x' : G), (y' : G)} : Set G) =
      (Subgroup.closure ({x', y'} : Set ↥K)).map K.subtype := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
    rfl
  have hclS : Subgroup.closure ({x', y'} : Set ↥K) ≤ S := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hx'S
    · exact hy'S
  refine ⟨x', y', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, hx'3, Subgroup.coe_one]
  · rw [← Subgroup.coe_pow, hy'3, Subgroup.coe_one]
  · exact congrArg Subtype.val hx'c
  · exact congrArg Subtype.val hy'c
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hcomz
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_zpow] at this
    rw [commutatorElement_def, this]
  · intro h1
    apply hcom1
    apply Subtype.ext
    simpa [commutatorElement_def] using h1
  · rw [hcl]
    exact (hS.isPGroup.to_le hclS).map _

omit [Finite G] in
theorem commutatorElement_mul_of_commute {u v s t : G} (hus : Commute u s) (hut : Commute u t)
    (huv : Commute u v) (hvs : Commute v s) (hvt : Commute v t) :
    ⁅u * s, v * t⁆ = ⁅s, t⁆ := by
  have hX : Commute u (s * v * t * s⁻¹) :=
    ((hus.mul_right huv).mul_right hut).mul_right hus.inv_right
  have hvst : Commute v ⁅s, t⁆ := by
    rw [commutatorElement_def]
    exact ((hvs.mul_right hvt).mul_right hvs.inv_right).mul_right hvt.inv_right
  have e : s * v = v * s := hvs.eq.symm
  calc ⁅u * s, v * t⁆ = u * (s * v * t * s⁻¹) * u⁻¹ * (t⁻¹ * v⁻¹) := by
        rw [commutatorElement_def]; group
    _ = s * v * t * s⁻¹ * (t⁻¹ * v⁻¹) := by rw [hX.eq]; group
    _ = (s * v) * t * s⁻¹ * t⁻¹ * v⁻¹ := by group
    _ = (v * s) * t * s⁻¹ * t⁻¹ * v⁻¹ := by rw [e]
    _ = v * ⁅s, t⁆ * v⁻¹ := by rw [commutatorElement_def]; group
    _ = ⁅s, t⁆ := by rw [hvst.eq]; group

theorem false_of_dec {L T : Subgroup G} {c : G} (hc : orderOf c = 3) (hcL : c ∉ L)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hT : IsSylowOf 3 T (Subgroup.centralizer ({c} : Set G)))
    (hdec : ∀ x ∈ T, x ^ 3 = 1 → ∃ k : ℤ, ∃ s ∈ L, x = c ^ k * s)
    {x y : G} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxc : x * c = c * x) (hyc : y * c = c * y)
    (hxy : ⁅x, y⁆ ∈ Subgroup.zpowers c) (hxy1 : ⁅x, y⁆ ≠ 1)
    (hp : IsPGroup 3 (Subgroup.closure ({x, y} : Set G))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := Subgroup.closure ({x, y} : Set G) with hR
  have hRC : R ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hxc
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hyc
  obtain ⟨Q, hQ, hRQ⟩ := Item134SylowBarProof.exists_isSylowOf_le hRC hp
  obtain ⟨m, hmC, hQm⟩ := Item134SylowBarProof.exists_conj_of_isSylowOf hT hQ
  have hconjT : ∀ z ∈ R, m⁻¹ * z * m ∈ T := by
    intro z hz
    have hz' : z ∈ T.map (MulAut.conj m).toMonoidHom := hQm ▸ hRQ hz
    obtain ⟨t, ht, hte⟩ := hz'
    have : t = m⁻¹ * z * m := by
      rw [← hte]
      simp [MulAut.conj_apply, mul_assoc]
    exact this ▸ ht
  have hcube : ∀ z : G, z ^ 3 = 1 → (m⁻¹ * z * m) ^ 3 = 1 := fun z hz => by
    rw [show m⁻¹ * z * m = m⁻¹ * z * m⁻¹⁻¹ by rw [inv_inv], conj_pow, hz, mul_one,
      mul_inv_cancel]
  obtain ⟨a, s, hsL, hxa⟩ := hdec _ (hconjT x (Subgroup.subset_closure (by simp))) (hcube x hx3)
  obtain ⟨b, t, htL, hyb⟩ := hdec _ (hconjT y (Subgroup.subset_closure (by simp))) (hcube y hy3)
  have hcomm : ∀ w ∈ L, Commute c w := fun w hw =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLc hw)).symm
  have h2 : ⁅c ^ a * s, c ^ b * t⁆ = ⁅s, t⁆ :=
    commutatorElement_mul_of_commute ((hcomm s hsL).zpow_left a) ((hcomm t htL).zpow_left a)
      ((Commute.refl c).zpow_zpow a b) ((hcomm s hsL).zpow_left b) ((hcomm t htL).zpow_left b)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxy
  have hmc : m⁻¹ * c ^ j * m = c ^ j := by
    have hmc' : Commute m (c ^ j) :=
      (show Commute m c from Subgroup.mem_centralizer_singleton_iff.mp hmC).zpow_right j
    rw [mul_assoc, ← hmc'.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 : m⁻¹ * ⁅x, y⁆ * m = ⁅m⁻¹ * x * m, m⁻¹ * y * m⁆ := by
    simp only [commutatorElement_def]
    group
  have hmemL : ⁅x, y⁆ ∈ L := by
    have heq : ⁅x, y⁆ = ⁅s, t⁆ :=
      calc ⁅x, y⁆ = m⁻¹ * ⁅x, y⁆ * m := by rw [← hj, hmc]
        _ = ⁅m⁻¹ * x * m, m⁻¹ * y * m⁆ := h1
        _ = ⁅c ^ a * s, c ^ b * t⁆ := by rw [hxa, hyb]
        _ = ⁅s, t⁆ := h2
    rw [heq, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hsL htL) (inv_mem hsL)) (inv_mem htL)
  have h3 : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc]
  have hzeq := eq_zpowers_of_card_three h3 hxy hxy1
  have hcmem : c ∈ Subgroup.zpowers ⁅x, y⁆ := hzeq ▸ Subgroup.mem_zpowers c
  exact hcL ((Subgroup.zpowers_le.mpr hmemL) hcmem)


theorem exists_sylow_dec {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L) (hMeets : MeetsY4 A (lB A) L Y₀)
    (h1511 : Item1511 A (lB A) c L) (hΩ : omegaA A = {Subgroup.zpowers c}) :
    ∃ T : Subgroup G, IsSylowOf 3 T (Subgroup.centralizer ({c} : Set G)) ∧
      ∀ x ∈ T, x ^ 3 = 1 → ∃ k : ℤ, ∃ s ∈ L, x = c ^ k * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hprod, hM12⟩ := Proof175.prod_of_item1514 h h1514 hMeets hΩ
  have htypes := (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1
  have hZ := Sec15.center_eq_bot_of_types h.mem_lA.1 htypes
  obtain ⟨-, hAeq, T, hT, hAT, hTL, hS⟩ := Proof175.setup_of_prod h hprod hZ
  have hinner : (∀ σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L), ∀ k : ℕ, σ ^ 3 ^ k = 1 →
      ∃ q, MulAut.conj q = σ) →
      ∃ T : Subgroup G, IsSylowOf 3 T (Subgroup.centralizer ({c} : Set G)) ∧
        ∀ x ∈ T, x ^ 3 = 1 → ∃ k : ℤ, ∃ s ∈ L, x = c ^ k * s := fun hinn =>
    ⟨T, hT, fun x hx hx3 => by
      obtain ⟨k, s, hs, -, hxs⟩ := Proof175.exists_zpow_mul_of_pow_eq_one hZ hinn
        h.mem_partTwoF hAeq h.le_centralizer_c hT.isPGroup hAT hT.le hTL hS hx hx3
      exact ⟨k, s, hs.2, hxs⟩⟩
  rcases htypes with hJ | ⟨p, e, hp, he, hiso⟩ | hA7 | hM22 | hM12'
  · exact hinner fun σ k hσ => Item134SylowBarProof.mem_range_conj_of_pow_three_pow hJ σ hσ
  ·
    have hc := h.toSec13Data.orderOf_eq
    have hCH : Subgroup.centralizer ({c} : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      centralizer_singleton_le_normalizer_zpowers c
    have hCle : Subgroup.centralizer ({c} : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y₀ : Set G) :=
      le_inf hCH (hCH.trans h.normalizer_c_le)
    obtain ⟨P, hP, hAP⟩ := Item134SylowBarProof.exists_isSylowOf_le
      (h.toSec13Data.A_le_centralizer.trans hCle) h.isE27.isPGroup
    have hAP' : A = omegaOneThree P :=
      (h1511 p e he hiso Y₀ h.mem_y0Star.prop hMeets P hAP hP).2.2.2.2
    have hPC : P ≤ Subgroup.centralizer ({c} : Set G) := by
      intro x hx
      obtain ⟨n, hn⟩ := hP.isPGroup ⟨x, hx⟩
      exact Proof175.mem_centralizer_of_mem_normalizer hc (Subgroup.mem_inf.mp (hP.le hx)).1
        (by simpa using congrArg Subtype.val hn)
    refine ⟨P, hP.of_le hPC hCle, fun x hx hx3 => ?_⟩
    have hxA : x ∈ A := by
      rw [hAP']
      exact Subgroup.subset_closure ⟨hx, hx3⟩
    have hcAL : c ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun e he =>
        (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c he.2))
    rw [hAeq] at hxA
    obtain ⟨k, s, hs, hxs⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hcAL hxA
    exact ⟨k, s, hs.2, hxs⟩
  · exact hinner (Proof175.a7m22_facts KFacts.KS14.ks18A7M22 (Or.inl hA7)).2.1
  · exact hinner (Proof175.a7m22_facts KFacts.KS14.ks18A7M22 (Or.inr hM22)).2.1
  · exact (hM12.false hM12'.some).elim

end Proof176Steps

open Proof176Steps in
theorem step176Excl_of (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h1511 : Item1511S17)
    (hG2 : KS176GTwo) : Step176Excl := by
  intro G _ _ A c L Y₀ h h175 hΩ K _ hcK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : orderOf c = 3 := h.toSec13Data.orderOf_eq
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  obtain ⟨T, hT, hdec⟩ := exists_sylow_dec h (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h)
    (h1511 G A c L Y₀ h) hΩ
  set N := CFSG.pPrimeCore 3 ↥K with hN
  set Zt := (Subgroup.zpowers (⟨c, hcK⟩ : ↥K)).map (QuotientGroup.mk' N) with hZt
  set H := Subgroup.normalClosure (Zt : Set (↥K ⧸ N)) with hH
  have hZ3 : Nat.card Zt = 3 := Proof176.card_map_zpowers hc hcK
  have hwc := Proof176.weaklyClosed_quot hc (h175 hΩ) hcK
  have hZH : Zt ≤ H := Subgroup.subset_normalClosure
  have hZ3' : Nat.card (Zt.subgroupOf H) = 3 := by rw [card_subgroupOf_eq hZH, hZ3]
  have hwc' := weaklyClosed_subgroupOf hZH hwc
  have key : HasCommOfZ (Zt.subgroupOf H) → False := fun hh => by
    obtain ⟨x, y, hx3, hy3, hxc, hyc, hxy, hxy1, hp⟩ :=
      exists_lift_of_hasComm hc hcK (hasCommOfZ_of_subgroupOf hZH hh)
    exact false_of_dec hc hcL h.le_centralizer_c hT hdec hx3 hy3 hxc hyc hxy hxy1 hp
  exact ⟨fun hG => key (hG2 _ hG _ hZ3' hwc'), ⟨fun e => key (hasCommOfZ_of_j2 ⟨e⟩ hZ3' hwc')⟩⟩

end CFSG.RankThree.PartTwo.Sec17
