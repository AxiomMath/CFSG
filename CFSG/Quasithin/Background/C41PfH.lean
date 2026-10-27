module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace C41Pf

section Rank

theorem false_of_card_elemAbelian {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.SQTKTauCeti.StronglyQuasithin Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup Y} (hE : IsElemAbelian p E) (hc : Nat.card ↥E = p ^ 3) : False := by
  have h := hY p hp hp2
  have h3 : 3 ≤ CFSG.Assembly.pRank p (⊤ : Subgroup Y) := by
    refine le_csSup ?_ ⟨E, le_top, ⟨hE.1, hE.2⟩, hc⟩
    refine ⟨Nat.card Y, ?_⟩
    rintro j ⟨F, -, -, hF⟩
    have h1 : p ^ j ≤ Nat.card Y :=
      hF ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card F)
    exact (Nat.lt_pow_self hp.one_lt).le.trans h1
  exact absurd (h3.trans h) (by norm_num)

end Rank

variable {G : Type} [Group G] [Finite G]

section Pair

omit [Finite G] in
theorem eq_one_of_pow_eq_one_of_mem {N : Subgroup G} (hN : IsPGroup 2 N) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : G} (hxN : x ∈ N) (hx : x ^ p = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hN ⟨x, hxN⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp this

theorem false_of_elemAbelian_pair {H K K' : Subgroup G} (hH : IsSQTKIn H) (hKH : K ≤ H)
    (hK'H : K' ≤ H) (hcomm : ⁅K, K'⁆ ≤ pCoreOf 2 H)
    (hint : (K ⊔ pCoreOf 2 H) ⊓ (K' ⊔ pCoreOf 2 H) = pCoreOf 2 H) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hEK : E ≤ K) (hE : IsElemAbelian p E)
    (hEc : Nat.card ↥E = p ^ 2) {y : G} (hyK' : y ∈ K') (hy : orderOf y = p) : False := by
  have : Fact p.Prime := ⟨hp⟩
  set N := pCoreOf 2 H with hN
  have hN2 : IsPGroup 2 ↥N := pCoreOf_isPGroup 2 H
  set Q := ↥H ⧸ CFSG.pCore 2 ↥H with hQ
  set π : ↥H →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hQsq : CFSG.Open.SQTKTauCeti.StronglyQuasithin Q := (SQTKHyp.of_sqtkGroup ↥H hH).sqt
  have hmemN : ∀ h : ↥H, h ∈ CFSG.pCore 2 ↥H ↔ (h : G) ∈ N := by
    intro h
    rw [hN, C2A3Orbits.pCoreOf_eq_map_pCore H]
    constructor
    · intro hh
      exact ⟨h, hh, rfl⟩
    · rintro ⟨h', hh', he⟩
      rwa [show h = h' from Subtype.ext he.symm]
  have hπ1 : ∀ h : ↥H, π h = 1 ↔ (h : G) ∈ N := by
    intro h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmemN]
  have hyp : y ^ p = 1 := hy ▸ pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact hp.one_lt.ne hy
  have hyN : y ∉ N := fun h => hy1 (eq_one_of_pow_eq_one_of_mem hN2 hp hp2 h hyp)
  set E' := E.subgroupOf H with hE'
  let f : ↥E' →* Q := π.comp E'.subtype
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : ((x : ↥H) : G) ∈ N := (hπ1 _).mp hx
    have h2 : ((x : ↥H) : G) ^ p = 1 := hE.2 _ x.2
    have h3 := eq_one_of_pow_eq_one_of_mem hN2 hp hp2 h1 h2
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext h3))
  set Ehat := f.range with hEhat
  have hEhatc : Nat.card ↥Ehat = p ^ 2 := by
    rw [hEhat, Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm, hE',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEK.trans hKH)).toEquiv, hEc]
  have hEhatE : IsElemAbelian p Ehat := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨z, hz⟩ := b.2
      apply Subtype.ext
      show (a : Q) * b = b * a
      rw [← hx, ← hz, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      show ((x : ↥H) : G) * ((z : ↥H) : G) = ((z : ↥H) : G) * ((x : ↥H) : G)
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, x.2⟩ ⟨_, z.2⟩)
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ p = 1 := Subtype.ext (Subtype.ext (hE.2 _ x.2))
      rw [this, map_one]
  set yh : Q := π ⟨y, hK'H hyK'⟩ with hyh
  have hyh1 : yh ≠ 1 := fun h => hyN ((hπ1 _).mp h)
  have hyhp : orderOf yh = p := by
    refine orderOf_eq_prime ?_ hyh1
    rw [hyh, ← map_pow]
    have : (⟨y, hK'H hyK'⟩ : ↥H) ^ p = 1 := Subtype.ext (by simpa using hyp)
    rw [this, map_one]
  have hcommh : ∀ e ∈ Ehat, Commute e yh := by
    rintro _ ⟨x, rfl⟩
    show f x * yh = yh * f x
    have hxK : ((x : ↥H) : G) ∈ K := hEK x.2
    have hc : ⁅((x : ↥H) : G), y⁆ ∈ N := hcomm (Subgroup.commutator_mem_commutator hxK hyK')
    have hc' : π (⁅(x : ↥H), (⟨y, hK'H hyK'⟩ : ↥H)⁆) = 1 := (hπ1 _).mpr hc
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hc'
    exact hc'
  have hyhE : yh ∉ Ehat := by
    rintro ⟨x, hx⟩
    have h1 : π ((x : ↥H)⁻¹ * ⟨y, hK'H hyK'⟩) = 1 := by
      rw [map_mul, map_inv]
      show (f x)⁻¹ * yh = 1
      rw [hx, inv_mul_cancel]
    have h2 : ((x : ↥H) : G)⁻¹ * y ∈ N := by simpa using (hπ1 _).mp h1
    have hyKN : y ∈ K ⊔ N := by
      have e : y = ((x : ↥H) : G) * (((x : ↥H) : G)⁻¹ * y) := by group
      rw [e]
      exact (K ⊔ N).mul_mem (Subgroup.mem_sup_left (hEK x.2)) (Subgroup.mem_sup_right h2)
    have hyK'N : y ∈ K' ⊔ N := Subgroup.mem_sup_left hyK'
    have : y ∈ N := by
      rw [← hint]
      exact ⟨hyKN, hyK'N⟩
    exact hyN this
  obtain ⟨hE3, hE3c⟩ := exists_elemAbelian_sup_zpowers hEhatE hyhp hcommh hyhE
  rw [hEhatc] at hE3c
  exact false_of_card_elemAbelian hQsq hp hp2 hE3 (by rw [hE3c]; ring)

end Pair

section Lift

omit [Finite G] in
theorem card_map_subtype {K : Subgroup G} (P : Subgroup ↥K) :
    Nat.card ↥(P.map K.subtype) = Nat.card ↥P :=
  Nat.card_congr (Subgroup.equivMapOfInjective P K.subtype K.subtype_injective).toEquiv.symm

theorem exists_elemAbelian_lift {K : Subgroup G} {X : Type*} [Group X] [Finite X]
    (α : ↥K →* X) (hα : Function.Surjective α) (hker : IsPGroup 2 ↥α.ker) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup X} (hE : IsElemAbelian p E) (hEc : Nat.card ↥E = p ^ 2) :
    ∃ F : Subgroup G, F ≤ K ∧ IsElemAbelian p F ∧ Nat.card ↥F = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  set D := E.comap α with hD
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥D))
  set α' : ↥D →* ↥E := (α.comp D.subtype).codRestrict E fun d => d.2 with hα'
  have hα's : Function.Surjective α' := by
    intro e
    obtain ⟨k, hk⟩ := hα e
    exact ⟨⟨k, show α k ∈ E by rw [hk]; exact e.2⟩, Subtype.ext hk⟩
  have hker' : IsPGroup 2 ↥α'.ker := by
    intro x
    have hx : ((x : ↥D) : ↥K) ∈ α.ker := by
      have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
      exact MonoidHom.mem_ker.mpr h1
    obtain ⟨k, hk⟩ := hker ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥α.ker => (z : ↥K)) hk
    simpa using this
  have hPinj : Function.Injective (α'.comp (P : Subgroup ↥D).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨n, hn⟩ := P.isPGroup' x
    have hxp : ((x : ↥D)) ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hxk : ((x : ↥D)) ∈ α'.ker := MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx)
    obtain ⟨m, hm⟩ := hker' ⟨(x : ↥D), hxk⟩
    have hx2' : ((x : ↥D)) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h1 : orderOf ((x : ↥D)) ∣ p ^ n := orderOf_dvd_of_pow_eq_one hxp
    have h2 : orderOf ((x : ↥D)) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hx2'
    have hcop : Nat.Coprime (p ^ n) (2 ^ m) :=
      Nat.Coprime.pow n m ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have h3 : orderOf ((x : ↥D)) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact Subgroup.mem_bot.mpr (Subtype.ext (orderOf_eq_one_iff.mp h3))
  have hDcard : Nat.card ↥D = Nat.card ↥α'.ker * p ^ 2 := by
    rw [← hEc, Subgroup.card_eq_card_quotient_mul_card_subgroup α'.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α' hα's).toEquiv, mul_comm]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hker'
  have hPcard : Nat.card ↥(P : Subgroup ↥D) = p ^ 2 := by
    rw [P.card_eq_multiplicity, hDcard, ha]
    congr 1
    rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ hp.ne_zero),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Nat.Prime.factorization_pow hp]
    simp [hp2]
  set F : Subgroup G := ((P : Subgroup ↥D).map D.subtype).map K.subtype with hF
  refine ⟨F, Subgroup.map_subtype_le _, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩, hxa⟩ := a.2
    obtain ⟨_, ⟨z, hz, rfl⟩, hzb⟩ := b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← hxa, ← hzb]
    have hc : (α'.comp (P : Subgroup ↥D).subtype) (⟨x, hx⟩ * ⟨z, hz⟩) =
        (α'.comp (P : Subgroup ↥D).subtype) (⟨z, hz⟩ * ⟨x, hx⟩) := by
      rw [map_mul, map_mul]
      exact hE.1.is_comm.comm _ _
    have := congrArg (fun w : ↥(P : Subgroup ↥D) => (((w : ↥D) : ↥K) : G)) (hPinj hc)
    simpa using this
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hc : (α'.comp (P : Subgroup ↥D).subtype) (⟨x, hx⟩ ^ p) = 1 := by
      rw [map_pow]
      exact Subtype.ext (hE.2 _ (α' x).2)
    have h1 : (⟨x, hx⟩ : ↥(P : Subgroup ↥D)) ^ p = 1 := hPinj (by rw [hc, map_one])
    have := congrArg (fun w : ↥(P : Subgroup ↥D) => (((w : ↥D) : ↥K) : G)) h1
    simpa using this
  · rw [hF, card_map_subtype, Nat.card_congr (Subgroup.equivMapOfInjective _ D.subtype
      D.subtype_injective).toEquiv.symm, hPcard]

end Lift

section Simple

theorem isSimpleGroup_of_not_le_normalizer
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) {H K : Subgroup G}
    (hH : IsSQTKIn H) (hK : K ∈ cComp H) (hn : ¬ H ≤ Subgroup.normalizer (K : Set G)) :
    IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  set Q := ↥H with hQ
  set N := CFSG.pCore 2 Q with hN
  have hGb : SQTKHyp (Q ⧸ N) := SQTKHyp.of_sqtkGroup Q hH
  have h38 := hA38 _ hGb
  have hNsolv : Group.IsSolvable ↥N := by
    have := (CFSG.pCore_isPGroup (G := Q) (p := 2)).isNilpotent
    infer_instance
  set π : Q →* Q ⧸ N := QuotientGroup.mk' N with hπ
  set L := K.subgroupOf H with hL
  have hLc : L ∈ cComp (⊤ : Subgroup Q) := (cComp_subgroupOf_bijOn H).mapsTo hK
  have hbij := cComp_quotient_bijOn N hNsolv
  have hLb : L.map π ∈ cComp (⊤ : Subgroup (Q ⧸ N)) := hbij.mapsTo hLc
  obtain ⟨hfirst, -⟩ := h38 (L.map π) hLb
  rcases hfirst with hnorm | ⟨htypes, -⟩
  · exfalso
    apply hn
    intro h hh
    set g : Q := ⟨h, hh⟩ with hg
    have hgL : L.map (MulAut.conj g).toMonoidHom = L := by
      have h1 : (L.map π).map (MulAut.conj (π g)).toMonoidHom = L.map π :=
        A38.map_conj_eq_iff.mpr (by
          rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]
          exact Subgroup.mem_top _)
      rw [C2A3Orbits.map_conj_map] at h1
      exact hbij.injOn (C2A3Orbits.conj_mem_cComp_top hLc g) hLc h1
    have h2 : g ∈ Subgroup.normalizer (L : Set Q) := A38.map_conj_eq_iff.mp hgL
    have h3 := (C2A3Orbits.mem_normalizer_map_subtype H L g).mpr h2
    rwa [hL, Subgroup.map_subgroupOf_eq_of_le hKH] at h3
  · have hS : IsSimpleGroup ↥(L.map π) := Vol2Native.L122A.isSimpleGroup_of_a38Types htypes
    let ψ : ↥K →* ↥(L.map π) :=
      { toFun := fun k => ⟨π ⟨k, hKH k.2⟩, ⟨⟨k, hKH k.2⟩, k.2, rfl⟩⟩
        map_one' := Subtype.ext (map_one π)
        map_mul' := fun a b => Subtype.ext (by
          simp only [Subgroup.coe_mul]
          rw [← map_mul]
          rfl) }
    have hψ : Function.Surjective ψ := by
      rintro ⟨_, ⟨x, hx, rfl⟩⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hker : ψ.ker = CFSG.pCore 2 ↥K := by
      ext k
      rw [MonoidHom.mem_ker]
      have hiff : ψ k = 1 ↔ (k : G) ∈ pCoreOf 2 H := by
        constructor
        · intro h1
          have h2 : π ⟨k, hKH k.2⟩ = 1 := congrArg Subtype.val h1
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
          rw [C2A3Orbits.pCoreOf_eq_map_pCore H]
          exact ⟨_, h2, rfl⟩
        · intro h1
          apply Subtype.ext
          show π ⟨k, hKH k.2⟩ = 1
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          rw [C2A3Orbits.pCoreOf_eq_map_pCore H] at h1
          obtain ⟨k', hk', he⟩ := h1
          rwa [show (⟨k, hKH k.2⟩ : Q) = k' from Subtype.ext he.symm]
      rw [hiff]
      have hO : pCoreOf 2 K ≤ pCoreOf 2 H :=
        A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
      have hO' : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
        refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
          ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
        exact (le_inf Subgroup.le_normalizer (hKH.trans (le_normalizer_pCoreOf 2 H))).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have hmem : (k : G) ∈ pCoreOf 2 K ↔ k ∈ CFSG.pCore 2 ↥K := by
        rw [C2A3Orbits.pCoreOf_eq_map_pCore K]
        constructor
        · rintro ⟨k', hk', he⟩
          rwa [show k = k' from Subtype.ext he.symm]
        · intro hk
          exact ⟨k, hk, rfl⟩
      rw [← hmem]
      exact ⟨fun h => hO' ⟨k.2, h⟩, fun h => hO h⟩
    let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(L.map π) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    exact e.isSimpleGroup

end Simple

end C41Pf

end CFSG.Quasithin
