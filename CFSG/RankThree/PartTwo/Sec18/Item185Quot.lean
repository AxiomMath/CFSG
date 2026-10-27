module

public import CFSG.RankThree.PartTwo.Sec18.Item185Ctx
public import CFSG.RankThree.PartTwo.Sec18.Item185Leaves
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Transport
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.Sec18.Item186a

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec19.SimsC198 (RankHyp)
open CFSG.RankThree.PartTwo.Sec19.SimsC198 (quotAct actImage mem_actImage quotAct_eq_one_iff)

variable {G : Type} [Group G] [Finite G]

private theorem card_comap_quot185 {H : Type} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (E : Subgroup (H ⧸ N)) :
    Nat.card (E.comap (QuotientGroup.mk' N)) = Nat.card E * Nat.card N := by
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have h1 := Subgroup.card_mul_index (H := E.comap (QuotientGroup.mk' N))
  have h2 := Subgroup.index_comap_of_surjective (H := E) hsurj
  have h3 := Subgroup.card_mul_index (H := E)
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (s := N)
  have hidx : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite (H := E)
  rw [h2] at h1
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx)
  rw [h1, h4, ← h3]
  ring

private theorem isElemAbelian_of_injOn185 {H Y : Type} [Group H] [Group Y] {p : ℕ}
    (f : H →* Y) {E' : Subgroup Y} (hE : IsElemAbelian p E') {Q : Subgroup H}
    (hmaps : ∀ x ∈ Q, f x ∈ E') (hinj : Set.InjOn f Q) : IsElemAbelian p Q := by
  have hcomm : ∀ u ∈ E', ∀ v ∈ E', u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨u, hu⟩ : E') ⟨v, hv⟩)
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · refine Subtype.ext (hinj (Q.mul_mem a.2 b.2) (Q.mul_mem b.2 a.2) ?_)
    rw [map_mul, Subgroup.coe_mul, map_mul]
    exact hcomm _ (hmaps _ a.2) _ (hmaps _ b.2)
  · refine hinj (Q.pow_mem hx p) Q.one_mem ?_
    rw [map_pow, map_one]
    exact hE.2 _ (hmaps _ hx)

private theorem lift185 {K : Subgroup G} {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {E : Subgroup (K ⧸ CFSG.pCore 2 K)} (hE : IsElemAbelian p E) :
    ∃ P : Subgroup G, P ≤ K ∧ IsElemAbelian p P ∧ Nat.card P = Nat.card E := by
  haveI : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE.isPGroup
  set N : Subgroup K := CFSG.pCore 2 K with hN
  set F : Subgroup K := E.comap (QuotientGroup.mk' N) with hF
  have hcard : Nat.card F = Nat.card E * Nat.card N := card_comap_quot185 N E
  have hdvd : p ^ k ∣ Nat.card F := by
    rw [hcard, hk]
    exact dvd_mul_right _ _
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  set π : F →* (K ⧸ N) := (QuotientGroup.mk' N).comp F.subtype with hπ
  have hπE : ∀ x ∈ Q, π x ∈ E := fun x _ => x.2
  have hQp : IsPGroup p Q := IsPGroup.iff_card.mpr ⟨k, hQ⟩
  have hinj : Set.InjOn π (Q : Set F) := by
    intro x hx y hy hxy
    have hz : x⁻¹ * y ∈ Q := Q.mul_mem (Q.inv_mem hx) hy
    have hπz : π (x⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hzN : ((x⁻¹ * y : F) : K) ∈ N :=
      (QuotientGroup.eq_one_iff ((x⁻¹ * y : F) : K)).mp hπz
    obtain ⟨a, ha⟩ := hQp ⟨x⁻¹ * y, hz⟩
    have hPg : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
    obtain ⟨b, hb⟩ := hPg ⟨((x⁻¹ * y : F) : K), hzN⟩
    have ha' : (x⁻¹ * y) ^ p ^ a = 1 := by
      have h1 := congrArg Subtype.val ha
      simpa using h1
    have hb' : (x⁻¹ * y) ^ 2 ^ b = 1 := by
      have h1 := congrArg Subtype.val hb
      have h2 : ((x⁻¹ * y : F) : K) ^ 2 ^ b = 1 := by simpa using h1
      exact Subtype.ext (by simpa using h2)
    have hcop : Nat.Coprime (p ^ a) (2 ^ b) :=
      Nat.Coprime.pow a b ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    have hd1 : orderOf (x⁻¹ * y) ∣ p ^ a := orderOf_dvd_of_pow_eq_one ha'
    have hd2 : orderOf (x⁻¹ * y) ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hb'
    have h1 : orderOf (x⁻¹ * y) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
    exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp h1)
  have hQe : IsElemAbelian p Q := isElemAbelian_of_injOn185 π hE hπE hinj
  have hι : Function.Injective (K.subtype.comp F.subtype) := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  refine ⟨Q.map (K.subtype.comp F.subtype), ?_, hQe.map _, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.1.2
  · rw [Subgroup.card_map_of_injective hι, hQ, hk]

private theorem pRank_le_of_lift185 {K : Subgroup G} {p k : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2)
    (hk : ∀ (j : ℕ) (P : Subgroup G), P ≤ K → IsElemAbelian p P → Nat.card P = p ^ j → j ≤ k) :
    CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K)) ≤ k := by
  unfold CFSG.Open.pRank
  apply csSup_le'
  rintro j ⟨E, -, hE, hEj⟩
  obtain ⟨P, hPK, hP, hPc⟩ := lift185 hp2 hE
  exact hk j P hPK hP (hPc.trans hEj)

private theorem innerAut_normal185 (X : Type) [Group X] : (innerAut X).Normal := by
  constructor
  rintro _ ⟨g, rfl⟩ β
  refine ⟨β g, ?_⟩
  ext x
  simp [MulAut.conj_apply]

private theorem bot_normal185 (X : Type) [Group X] : (⊥ : Subgroup X).Normal :=
  ⟨fun n hn g => by rw [Subgroup.mem_bot] at hn ⊢; rw [hn, mul_one, mul_inv_cancel]⟩

private theorem conj_eq_one_iff185 {X : Type} [Group X] (x : X) :
    MulAut.conj x = 1 ↔ x ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have hg : MulAut.conj x g = g := by rw [h, MulAut.one_apply]
    rw [MulAut.conj_apply] at hg
    calc g * x = x * g * x⁻¹ * x := by rw [hg]
      _ = x * g := by group
  · intro h
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, ← h g]
    group

private theorem cube_mul185 {X : Type} [Group X] {t s u : X} (hu : u ∈ Subgroup.center X)
    (ht : t ^ 3 ∈ Subgroup.center X) (hst : s * t = u * (t * s)) :
    (t * s) ^ 3 = t ^ 3 * s ^ 3 := by
  have hc : ∀ g : X, g * u = u * g := fun g => Subgroup.mem_center_iff.mp hu g
  have hcu : ∀ g : X, g * (u * u) = u * u * g := fun g =>
    Subgroup.mem_center_iff.mp ((Subgroup.center X).mul_mem hu hu) g
  have hsconj : s * t * s⁻¹ = u * t := by
    rw [hst]
    group
  have hpow : s * t ^ 3 * s⁻¹ = u ^ 3 * t ^ 3 := by
    rw [← conj_pow, hsconj, Commute.mul_pow (show Commute u t from (hc t).symm)]
  have hcen : s * t ^ 3 * s⁻¹ = t ^ 3 := by
    rw [Subgroup.mem_center_iff.mp ht s]
    group
  have hu3 : u ^ 3 = 1 := by
    have h1 : u ^ 3 * t ^ 3 = 1 * t ^ 3 := by
      rw [one_mul, ← hpow, hcen]
    exact mul_right_cancel h1
  have hcu' : ∀ Y : X, t * (u * u * Y) = u * u * (t * Y) := fun Y => by
    have h := hcu t
    calc t * (u * u * Y) = (t * (u * u)) * Y := by group
      _ = (u * u * t) * Y := by rw [h]
      _ = u * u * (t * Y) := by group
  have key2 : s * s * t = u * u * (t * s * s) := by
    calc s * s * t = s * (s * t) := by group
      _ = s * (u * (t * s)) := by rw [hst]
      _ = u * (s * (t * s)) := by
        rw [← mul_assoc s u (t * s), hc s, mul_assoc u s (t * s)]
      _ = u * (s * t * s) := by rw [mul_assoc s t s]
      _ = u * (u * (t * s) * s) := by rw [hst]
      _ = u * u * (t * s * s) := by group
  have key : s * t * s * t = t * t * s * s := by
    calc s * t * s * t = u * (t * s) * s * t := by rw [hst]
      _ = u * t * (s * s * t) := by group
      _ = u * t * (u * u * (t * s * s)) := by rw [key2]
      _ = u * (t * (u * u * (t * s * s))) := by group
      _ = u * (u * u * (t * (t * s * s))) := by rw [hcu']
      _ = u ^ 3 * (t * (t * s * s)) := by simp only [pow_three, mul_assoc]
      _ = t * t * s * s := by
        rw [hu3, one_mul]
        group
  calc (t * s) ^ 3 = t * (s * t * s * t) * s := by simp only [pow_three, mul_assoc]
    _ = t * (t * t * s * s) * s := by rw [key]
    _ = t ^ 3 * s ^ 3 := by simp only [pow_three, mul_assoc]

private theorem quotAct_mul185 (K : Subgroup G) {g h : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hh : h ∈ Subgroup.normalizer (K : Set G))
    (hgh : g * h ∈ Subgroup.normalizer (K : Set G)) :
    quotAct K ⟨g * h, hgh⟩ = quotAct K ⟨g, hg⟩ * quotAct K ⟨h, hh⟩ := by
  have e : (⟨g * h, hgh⟩ : Subgroup.normalizer (K : Set G)) = ⟨g, hg⟩ * ⟨h, hh⟩ := rfl
  rw [e, map_mul]

private theorem quotAct_one185 (K : Subgroup G)
    {h : (1 : G) ∈ Subgroup.normalizer (K : Set G)} : quotAct K ⟨1, h⟩ = 1 := by
  have e : (⟨1, h⟩ : Subgroup.normalizer (K : Set G)) = 1 := rfl
  rw [e, map_one]

private theorem quotAct_inv185 (K : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hgi : g⁻¹ ∈ Subgroup.normalizer (K : Set G)) :
    quotAct K ⟨g⁻¹, hgi⟩ = (quotAct K ⟨g, hg⟩)⁻¹ := by
  have e : (⟨g⁻¹, hgi⟩ : Subgroup.normalizer (K : Set G)) =
      (⟨g, hg⟩ : Subgroup.normalizer (K : Set G))⁻¹ := rfl
  rw [e, map_inv (quotAct K)]

private noncomputable def preimAct185 (K B : Subgroup G)
    (T : Subgroup (MulAut (K ⧸ CFSG.pCore 2 K))) : Subgroup G where
  carrier := {g | g ∈ B ∧ ∃ hg : g ∈ Subgroup.normalizer (K : Set G), quotAct K ⟨g, hg⟩ ∈ T}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2, ha3⟩ := ha
    obtain ⟨hb1, hb2, hb3⟩ := hb
    refine ⟨B.mul_mem ha1 hb1, (Subgroup.normalizer (K : Set G)).mul_mem ha2 hb2, ?_⟩
    rw [quotAct_mul185 K ha2 hb2]
    exact T.mul_mem ha3 hb3
  one_mem' := by
    refine ⟨B.one_mem, (Subgroup.normalizer (K : Set G)).one_mem, ?_⟩
    rw [quotAct_one185 K]
    exact T.one_mem
  inv_mem' := by
    intro a ha
    obtain ⟨ha1, ha2, ha3⟩ := ha
    refine ⟨B.inv_mem ha1, (Subgroup.normalizer (K : Set G)).inv_mem ha2, ?_⟩
    rw [quotAct_inv185 K ha2]
    exact T.inv_mem ha3

private theorem mem_preimAct185 {K B : Subgroup G}
    {T : Subgroup (MulAut (K ⧸ CFSG.pCore 2 K))} {g : G} :
    g ∈ preimAct185 K B T ↔
      g ∈ B ∧ ∃ hg : g ∈ Subgroup.normalizer (K : Set G), quotAct K ⟨g, hg⟩ ∈ T :=
  Iff.rfl

private theorem preimAct_conj185 {K B S : Subgroup G}
    {T : Subgroup (MulAut (K ⧸ CFSG.pCore 2 K))} (hT : T.Normal)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hSB : S ≤ Subgroup.normalizer (B : Set G))
    {s v : G} (hs : s ∈ S) (hv : v ∈ preimAct185 K B T) :
    s * v * s⁻¹ ∈ preimAct185 K B T := by
  obtain ⟨hvB, hvN, hvT⟩ := mem_preimAct185.mp hv
  have hsN : s ∈ Subgroup.normalizer (K : Set G) := hSK hs
  have hmem : s * v * s⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).mul_mem
      ((Subgroup.normalizer (K : Set G)).mul_mem hsN hvN)
      ((Subgroup.normalizer (K : Set G)).inv_mem hsN)
  refine mem_preimAct185.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hSB hs) v).mp hvB, hmem, ?_⟩
  have hsv : s * v ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).mul_mem hsN hvN
  have hsi : s⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).inv_mem hsN
  rw [quotAct_mul185 K hsv hsi, quotAct_mul185 K hsN hvN, quotAct_inv185 K hsN]
  exact hT.conj_mem _ hvT _

private theorem le_normalizer_preimAct185 {K B S : Subgroup G}
    {T : Subgroup (MulAut (K ⧸ CFSG.pCore 2 K))} (hT : T.Normal)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hSB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer ((preimAct185 K B T : Subgroup G) : Set G) := by
  intro s hs
  refine Subgroup.mem_normalizer_iff.mpr
    (fun v => ⟨fun hv => preimAct_conj185 hT hSK hSB hs hv, fun hv => ?_⟩)
  have h' := preimAct_conj185 hT hSK hSB (S.inv_mem hs) hv
  have e : s⁻¹ * (s * v * s⁻¹) * s⁻¹⁻¹ = v := by group
  rw [e] at h'
  exact h'

theorem rankHyp_of_mem {A M : Subgroup G} (h : Sec18Std G A M) {K : Subgroup G}
    (hK : K ∈ oTwoComponentsIn M) : RankHyp (K ⧸ CFSG.pCore 2 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
  have hKM : K ≤ M := CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn hK
  have hMtop : M ≠ ⊤ := by
    haveI : IsSimpleGroup G := h.isSimpleGroup
    exact ne_top_of_pCoreOf_ne_bot h.nonabelian
      (pCoreOf_ne_bot_of_isMaximalTwoLocal h.mem_scriptM.1)
  have hKtop : K ≠ ⊤ := by
    rintro rfl
    exact hMtop (top_le_iff.mp hKM)
  have hKG : CFSG.IsKGroup ↥K := (h.toTheoremFourHyp.sectionFourHyp hKtop).kGroup
  refine ⟨CFSG.RankThree.PartTwo.Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK,
    CFSG.RankThree.PartTwo.Sec18.pCore_quotient_pCore_eq_bot 2, hKG.quotient _, ?_, ?_⟩
  · refine pRank_le_of_lift185 (k := 3) (by norm_num) ?_
    intro j P hPK hP hPj
    have h27 : Nat.card P ≤ 27 := card_le_of_le_M h (hPK.trans hKM) hP
    have hle : 3 ^ j ≤ 3 ^ 3 := by
      rw [← hPj]
      exact h27.trans (by norm_num)
    exact (pow_le_pow_iff_right₀ (by norm_num)).mp hle
  · intro p hp hp3
    haveI : Fact p.Prime := ⟨hp⟩
    refine pRank_le_of_lift185 (k := 2) (by omega) ?_
    intro j P hPK hP hPj
    have hsq : Nat.card P ≤ p ^ 2 := card_le_sq_of_le_M h hp hp3 (hPK.trans hKM) hP
    have hle : p ^ j ≤ p ^ 2 := by
      rw [← hPj]
      exact hsq
    exact (pow_le_pow_iff_right₀ (by omega)).mp hle

theorem faithful_B {A M : Subgroup G} (h : Sec18Std G A M) {K B S : Subgroup G}
    (hK : K ∈ oTwoComponentsIn M) (hBS : B ≤ S) (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hSB : S ≤ Subgroup.normalizer (B : Set G))
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn S B))
    (hnc : ∃ b ∈ B, ∃ k ∈ K, b * k * b⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M) :
    ∀ b ∈ B, (∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → b = 1 := by
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBS.trans hSK
  have hVB : preimAct185 K B ⊥ ≤ B := fun g hg => (mem_preimAct185.mp hg).1
  have hSV := le_normalizer_preimAct185 (bot_normal185 _) hSK hSB
  intro b hb hbK
  rcases CFSG.RankThree.PartTwo.Sec13.eq_bot_or_eq_of_isIrreducibleOn hirr hVB hSV with
    hV | hV
  · have hbV : b ∈ preimAct185 K B ⊥ :=
      mem_preimAct185.mpr
        ⟨hb, hBN hb, Subgroup.mem_bot.mpr ((quotAct_eq_one_iff K ⟨b, hBN hb⟩).mpr hbK)⟩
    rw [hV] at hbV
    exact Subgroup.mem_bot.mp hbV
  · exfalso
    obtain ⟨b', hb', k, hk, hnot⟩ := hnc
    have hb'V : b' ∈ preimAct185 K B ⊥ := by
      rw [hV]
      exact hb'
    obtain ⟨-, hN, h1⟩ := mem_preimAct185.mp hb'V
    have h2 : quotAct K ⟨b', hN⟩ = 1 := Subgroup.mem_bot.mp h1
    have h3 := (quotAct_eq_one_iff K ⟨b', hN⟩).mp h2
    exact hnot
      (CFSG.RankThree.PartTwo.Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK (h3 k hk))

theorem exists_elemAbelian_of_inner {X : Type} [Group X] [Finite X] {D : Subgroup (MulAut X)}
    (hD : IsElemAbelian 3 D) (h9 : Nat.card D = 9) (hDi : D ≤ innerAut X) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ 9 ≤ Nat.card E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm (⟨a, ha⟩ : D) ⟨b, hb⟩)
  set T : Subgroup X := D.comap (MulAut.conj : X →* MulAut X) with hT
  set Z : Subgroup X := Subgroup.center X with hZ
  have hkerZ : ∀ x : X, MulAut.conj x = 1 ↔ x ∈ Z := fun x => conj_eq_one_iff185 x
  have hZT : Z ≤ T := by
    intro x hx
    show MulAut.conj x ∈ D
    rw [(hkerZ x).mpr hx]
    exact D.one_mem
  have hcubeZ : ∀ t ∈ T, t ^ 3 ∈ Z := by
    intro t ht
    rw [← hkerZ, map_pow]
    exact hD.2 (MulAut.conj t) ht
  have hcommZ : ∀ t ∈ T, ∀ s ∈ T, s * t * (t * s)⁻¹ ∈ Z := by
    intro t ht s hs
    rw [← hkerZ, map_mul, map_inv, map_mul, map_mul]
    exact mul_inv_eq_one.mpr (hDc (MulAut.conj s) hs (MulAut.conj t) ht)
  have hcube : ∀ t ∈ T, ∀ s ∈ T, (t * s) ^ 3 = t ^ 3 * s ^ 3 := by
    intro t ht s hs
    exact cube_mul185 (t := t) (s := s) (u := s * t * (t * s)⁻¹) (hcommZ t ht s hs)
      (hcubeZ t ht) (by group)
  let f : T →* X := MonoidHom.mk' (fun t : T => (t : X) ^ 3) (fun a b => by
    show ((a : X) * (b : X)) ^ 3 = (a : X) ^ 3 * (b : X) ^ 3
    exact hcube a a.2 b b.2)
  have hfmem : ∀ t : T, f t ∈ Z := fun t => hcubeZ t t.2
  have hrange_le : f.range ≤ Z := by
    intro y hy
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hy
    exact hfmem t
  have hrange_card : Nat.card f.range ≤ Nat.card Z := Subgroup.card_le_of_le hrange_le
  have hidx : Nat.card f.ker * Nat.card f.range = Nat.card T := by
    rw [← Subgroup.index_ker f]
    exact Subgroup.card_mul_index (H := f.ker)
  set φ : T →* D :=
    ((MulAut.conj : X →* MulAut X).comp T.subtype).codRestrict D (fun t => t.2) with hφ
  have hφsurj : Function.Surjective φ := by
    rintro ⟨d, hd⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hDi hd)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show MulAut.conj x ∈ D
      rw [hx]
      exact hd
    · apply Subtype.ext
      exact hx
  have hker : φ.ker.map T.subtype = Z := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have h1 : MulAut.conj (t : X) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp ht)
        exact this
      exact (hkerZ _).mp h1
    · intro hx
      refine ⟨⟨x, hZT hx⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      apply Subtype.ext
      exact (hkerZ x).mpr hx
  have hTinj : Function.Injective T.subtype := Subtype.val_injective
  have hkercard : Nat.card φ.ker = Nat.card Z := by
    rw [← hker, Subgroup.card_map_of_injective hTinj]
  have hcardT : Nat.card T = 9 * Nat.card Z := by
    rw [← hkercard, ← h9, Subgroup.card_eq_card_quotient_mul_card_subgroup (s := φ.ker)]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv
  have h9le : 9 ≤ Nat.card f.ker := by
    have hpos : 0 < Nat.card Z := Nat.card_pos
    have key : 9 * Nat.card Z ≤ Nat.card f.ker * Nat.card Z := by
      calc 9 * Nat.card Z = Nat.card T := hcardT.symm
        _ = Nat.card f.ker * Nat.card f.range := hidx.symm
        _ ≤ Nat.card f.ker * Nat.card Z := Nat.mul_le_mul le_rfl hrange_card
    exact Nat.le_of_mul_le_mul_right key hpos
  have hΩ3 : ∀ y : f.ker, y ^ 3 = 1 := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    have hy : ((y.1 : T) : X) ^ 3 = 1 := MonoidHom.mem_ker.mp y.2
    simpa using hy
  have hΩp : IsPGroup 3 f.ker := by
    intro y
    exact ⟨1, by rw [pow_one]; exact hΩ3 y⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hΩp
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push_neg at hlt
    rw [hm] at h9le
    interval_cases m <;> norm_num at h9le
  have hdvd9 : 3 ^ 2 ∣ Nat.card f.ker := by
    rw [hm]
    exact pow_dvd_pow 3 hm2
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd9
  have hQe : IsElemAbelian 3 Q :=
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ, fun x _ => hΩ3 x⟩
  have hι : Function.Injective (T.subtype.comp f.ker.subtype) := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  refine ⟨Q.map (T.subtype.comp f.ker.subtype), hQe.map _, ?_⟩
  rw [Subgroup.card_map_of_injective hι, hQ] <;> norm_num

theorem exists_nine_of_leafF1 (hF1 : LeafF1) {A M : Subgroup G} (h : Sec18Std G A M)
    {K B S : Subgroup G} (hK : K ∈ oTwoComponentsIn M) (hBe : IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) (hBM : B ≤ M) (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hSB : S ≤ Subgroup.normalizer (B : Set G)) (hSM : S ≤ M) (hBS : B ≤ S)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn S B))
    (hnc : ∃ b ∈ B, ∃ k ∈ K, b * k * b⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M) :
    ∃ E ≤ K, IsElemAbelian 3 E ∧ 9 ≤ Nat.card E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBS.trans hSK
  have hfaith := faithful_B h hK hBS hSK hSB hirr hnc
  have hD9 : Nat.card (actImage K B) = 9 :=
    CFSG.RankThree.PartTwo.Sec19.SimsC198.Transport.card_actImage hBN hB9 hfaith
  have hDe : IsElemAbelian 3 (actImage K B) :=
    (hBe.subgroupOf (Subgroup.normalizer (K : Set G))).map (quotAct K)
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K)) ≤ 1 := by
    refine pRank_le_of_lift185 (k := 1) (by norm_num) ?_
    intro j P hPK hP hPj
    by_contra hj
    refine hcon ⟨P, hPK, hP, ?_⟩
    rw [hPj]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLeaf := hF1 (K ⧸ CFSG.pCore 2 K) (rankHyp_of_mem h hK) hrank (actImage K B) hDe hD9
  have hinn : (innerAut (K ⧸ CFSG.pCore 2 K)).Normal := innerAut_normal185 _
  have hSV := le_normalizer_preimAct185 hinn hSK hSB
  have hVB : preimAct185 K B (innerAut (K ⧸ CFSG.pCore 2 K)) ≤ B :=
    fun g hg => (mem_preimAct185.mp hg).1
  obtain ⟨d, hdmem, hd1⟩ : ∃ d ∈ actImage K B ⊓ innerAut (K ⧸ CFSG.pCore 2 K), d ≠ 1 := by
    by_contra hcon'
    push_neg at hcon'
    exact hLeaf ((Subgroup.eq_bot_iff_forall (H := _)).mpr hcon')
  obtain ⟨b, hbN, hbB, hbd⟩ := mem_actImage hdmem.1
  have hbV : b ∈ preimAct185 K B (innerAut (K ⧸ CFSG.pCore 2 K)) :=
    mem_preimAct185.mpr ⟨hbB, hbN, by rw [hbd]; exact hdmem.2⟩
  have hV_ne : preimAct185 K B (innerAut (K ⧸ CFSG.pCore 2 K)) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hbV
    have hb1 : b = 1 := Subgroup.mem_bot.mp hbV
    subst hb1
    apply hd1
    rw [← hbd]
    exact quotAct_one185 K
  have hVeq : preimAct185 K B (innerAut (K ⧸ CFSG.pCore 2 K)) = B :=
    (CFSG.RankThree.PartTwo.Sec13.eq_bot_or_eq_of_isIrreducibleOn hirr hVB hSV).resolve_left
      hV_ne
  have hDi : actImage K B ≤ innerAut (K ⧸ CFSG.pCore 2 K) := by
    intro d' hd'
    obtain ⟨b', hb'N, hb'B, hb'd⟩ := mem_actImage hd'
    have hb'V : b' ∈ preimAct185 K B (innerAut (K ⧸ CFSG.pCore 2 K)) := by
      rw [hVeq]
      exact hb'B
    obtain ⟨-, hg, hq⟩ := mem_preimAct185.mp hb'V
    rw [← hb'd]
    exact hq
  obtain ⟨E', hE'e, hE'9⟩ := exists_elemAbelian_of_inner hDe hD9 hDi
  obtain ⟨P, hPK, hPe, hPc⟩ := lift185 (K := K) (p := 3) (by norm_num) hE'e
  exact hcon ⟨P, hPK, hPe, by rw [hPc]; exact hE'9⟩

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
