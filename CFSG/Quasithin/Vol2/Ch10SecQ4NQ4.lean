module

public import CFSG.Quasithin.Vol2.Ch10SecQ4NQ3
public import CFSG.Quasithin.Vol2.Ch10SecQ4A19

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_centralizer {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) := by
  have key : ∀ h : G, h ∈ Subgroup.normalizer (Q : Set G) →
      ∀ c ∈ Subgroup.centralizer (Q : Set G), h * c * h⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
    intro h hh c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro q hq
    have hq' : h⁻¹ * q * h ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) q).mp hq
      simpa using this
    have h1 := hc _ hq'
    calc q * (h * c * h⁻¹) = h * ((h⁻¹ * q * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * q * h)) * h⁻¹ := by rw [h1]
      _ = h * c * h⁻¹ * q := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun h => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ h
  simpa [mul_assoc] using this

theorem exists_D (h36 : Vol2Native.A36CoreForSQTKCat) (h113 : ASInputs.AS_C_1_13)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    {K : Subgroup G} (hK : Ch10.IsLi T L K) (hKs : IsShort2 K) (hKa : IsAltType K 5)
    {X J : Subgroup G} (hXs : CFSG.SectionRank.IsSQTKCat ↥X)
    (hsyl : IsSylowTwoOf (Ch10.T1 T L) X) (hJ : J ∈ cComp X) (hKJ : K ≤ J)
    (hq : ¬ CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hUQ : blockU K ≤ pCoreOf 2 J)
    {z : G} (hzK : z ∈ K) (hzC : z ∈ Subgroup.centralizer (K : Set G))
    (hzQ : z ∉ pCoreOf 2 J) (hz2 : z * z = 1) :
    ∃ D : Subgroup G, D ≠ ⊥ ∧ Odd (Nat.card D) ∧ ¬ 3 ∣ Nat.card D ∧
      D ≤ Subgroup.centralizer (pCoreOf 2 J : Set G) ∧
      K ≤ Subgroup.normalizer (D : Set G) ∧ ⁅D, Subgroup.zpowers z⁆ = D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE1, hEodd, hE3, hEE, hzE, hKE, hlift⟩ :=
    exists_E h36 h113 h37 h38 hyp hK hKs hKa hXs hsyl hJ hKJ hq hUQ hzK hzC hzQ hz2
  have hTK := C10E4.T1_le_normalizer_of_isLi h37 h38 hyp hK
  have hQT : pCoreOf 2 J ≤ Ch10.T1 T L :=
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hJ) hsyl)).trans inf_le_left
  have hQK := hQT.trans hTK
  have hWel := C10E4.isElemAbelian_conjClosure hKs hKJ hQK hUQ
  have hQ2 : IsPGroup 2 (pCoreOf 2 J) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
  have hJQ : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
  set EJ : Subgroup G := (E.comap (quotTop J)).map J.subtype with hEJ
  have hmemEJ : ∀ {x : G}, x ∈ EJ ↔ ∃ hx : x ∈ J, quotTop J ⟨x, hx⟩ ∈ E := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hxE⟩
      exact ⟨⟨x, hx⟩, hxE, rfl⟩
  set C2 := EJ ⊓ Subgroup.centralizer (pCoreOf 2 J : Set G) with hC2
  set D0 := A37.oddCoreOf C2 with hD0
  have hC2J : C2 ≤ J := fun x hx => (hmemEJ.mp hx.1).1
  have hnorm : ∀ g : ↥J, quotTop J g ∈ Subgroup.normalizer (E : Set _) →
      (g : G) ∈ Subgroup.normalizer (D0 : Set G) := by
    intro g hg
    have hgEJ : ∀ h : ↥J, quotTop J h ∈ Subgroup.normalizer (E : Set _) →
        ∀ x ∈ EJ, (h : G) * x * (h : G)⁻¹ ∈ EJ := by
      intro h hh x hx
      obtain ⟨hxJ, hxE⟩ := hmemEJ.mp hx
      refine hmemEJ.mpr ⟨J.mul_mem (J.mul_mem h.2 hxJ) (J.inv_mem h.2), ?_⟩
      have e : (⟨(h : G) * x * (h : G)⁻¹, J.mul_mem (J.mul_mem h.2 hxJ) (J.inv_mem h.2)⟩ : ↥J) =
          h * ⟨x, hxJ⟩ * h⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hh _).mp hxE
    have hgEJn : (g : G) ∈ Subgroup.normalizer (EJ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hgEJ g hg x, fun hx => ?_⟩
      have hg' : quotTop J g⁻¹ ∈ Subgroup.normalizer (E : Set _) := by
        rw [map_inv]; exact Subgroup.inv_mem _ hg
      have := hgEJ g⁻¹ hg' _ hx
      simpa [mul_assoc] using this
    have hgN : (g : G) ∈ Subgroup.normalizer (C2 : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hgEJn, mem_normalizer_centralizer (hJQ g.2)⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => A37.conj_mem_oddCoreOf hgN hx, fun hx => ?_⟩
    have := A37.conj_mem_oddCoreOf (Subgroup.inv_mem _ hgN) hx
    simpa [mul_assoc] using this
  set ψ : ↥C2 →* ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) :=
    (quotTop J).comp (Subgroup.inclusion hC2J) with hψ
  have hψE : ψ.range ≤ E := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨hxJ, hxE⟩ := hmemEJ.mp x.2.1
    exact hxE
  have hψk : ψ.ker = (C2 ⊓ pCoreOf 2 J).subgroupOf C2 := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show quotTop J ⟨(x : G), hC2J x.2⟩ = 1 ↔ _
    rw [quotTop_eq_one_iff]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hidx : ¬ 2 ∣ (C2 ⊓ pCoreOf 2 J).relIndex C2 := by
    rw [Subgroup.relIndex, ← hψk, Subgroup.index_ker]
    intro h2
    have := h2.trans (Subgroup.card_dvd_of_le hψE)
    exact (Nat.not_even_iff_odd.mpr hEodd) (even_iff_two_dvd.mpr this)
  have hpre : ∀ e ∈ E, ∃ x : ↥J, (x : G) ∈ D0 ∧ quotTop J x = e := by
    intro e he
    obtain ⟨c, hcW, hce⟩ := hlift e he
    have heodd : Odd (orderOf e) := hEodd.of_dvd_nat (by
      have := orderOf_dvd_natCard (⟨e, he⟩ : ↥E)
      rwa [Subgroup.orderOf_mk] at this)
    obtain ⟨c', hc'z, hc'odd, hc'e⟩ := exists_odd_preimage (quotTop J) (orderOf_pos c)
      (hce ▸ heodd)
    have hc'W : (c' : G) ∈ Subgroup.centralizer (conjClosure (blockU K) J : Set G) := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'z
      exact Subgroup.zpow_mem _ hcW n
    have hc'odd' : Odd (orderOf (c' : G)) := by rwa [Subgroup.orderOf_coe]
    have hc'Q : (c' : G) ∈ Subgroup.centralizer (pCoreOf 2 J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      refine (commute_of_odd_of_mem (W := conjClosure (blockU K) J)
        (fun w hw => by rw [← sq]; exact hWel.2 w hw) hc'odd'
        (fun w hw => (Subgroup.mem_centralizer_iff.mp hc'W w hw).symm)
        (C10E4.commutator_mem_conjClosure hKs hKJ hQK hKa hJ c'.2 hq)).symm
    have hc'C2 : (c' : G) ∈ C2 := ⟨hmemEJ.mpr ⟨c'.2, by rw [hc'e, hce]; exact he⟩, hc'Q⟩
    refine ⟨c', mem_oddCoreOf_of_central inf_le_left (hQ2.to_le inf_le_right)
      (fun s hs c hc => Subgroup.mem_centralizer_iff.mp (show c ∈ C2 from hc).2 s
        (show s ∈ C2 ⊓ pCoreOf 2 J from hs).2) hidx hc'C2 hc'odd',
      by rw [hc'e, hce]⟩
  have hzJ := hKJ hzK
  have hzD0 : z ∈ Subgroup.normalizer (D0 : Set G) := hnorm ⟨z, hzJ⟩ hzE
  have hD0odd : Odd (Nat.card D0) := A37.odd_card_oddCoreOf C2
  have hD0C2 : D0 ≤ C2 := A37.oddCoreOf_le C2
  have hDD0 := commutator_zpowers_le hzD0
  have hD0Q : D0 ⊓ pCoreOf 2 J = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx0, hxQ⟩
    have h1 : orderOf x ∣ Nat.card D0 := by
      have := orderOf_dvd_natCard (⟨x, hx0⟩ : ↥D0)
      rwa [Subgroup.orderOf_mk] at this
    exact Subgroup.mem_bot.mpr (C10E4.eq_one_of_pow_odd hQ2 hxQ hD0odd
      (orderOf_dvd_iff_pow_eq_one.mp h1))
  have hD03 : ¬ 3 ∣ Nat.card D0 := by
    set ψ0 : ↥D0 →* ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) :=
      (quotTop J).comp (Subgroup.inclusion (hD0C2.trans hC2J)) with hψ0
    have hinj : Function.Injective ψ0 := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxQ : (x : G) ∈ pCoreOf 2 J := (quotTop_eq_one_iff J _).mp hx
      have : (x : G) ∈ D0 ⊓ pCoreOf 2 J := ⟨x.2, hxQ⟩
      rw [hD0Q] at this
      exact Subtype.ext this
    have hrange : ψ0.range ≤ E := by
      rintro _ ⟨x, rfl⟩
      exact (hmemEJ.mp (hD0C2 x.2).1).2
    have hcard : Nat.card D0 = Nat.card ψ0.range :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv)
    rw [hcard]
    exact fun h3 => hE3 (h3.trans (Subgroup.card_dvd_of_le hrange))
  refine ⟨⁅D0, Subgroup.zpowers z⁆, ?_, hD0odd.of_dvd_nat (Subgroup.card_dvd_of_le hDD0),
    fun h3 => hD03 (h3.trans (Subgroup.card_dvd_of_le hDD0)),
    hDD0.trans (hD0C2.trans inf_le_right), ?_, commutator_zpowers_idem hD0odd hz2 hzD0⟩
  ·
    obtain ⟨e, he, hez⟩ : ∃ e ∈ E, ⁅e, quotTop J ⟨z, hzJ⟩⁆ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hE1
      rw [← hEE, eq_bot_iff, Subgroup.commutator_le]
      intro e he y hy
      rcases eq_one_or_eq_of_mem_zpowers'
          (by rw [← map_mul]; exact (by
            have : (⟨z, hzJ⟩ : ↥J) * ⟨z, hzJ⟩ = 1 := Subtype.ext hz2
            rw [this, map_one])) hy with h | h
      · rw [h, commutatorElement_one_right]; exact Subgroup.one_mem _
      · rw [h, hcon e he]; exact Subgroup.one_mem _
    obtain ⟨x, hx0, hxe⟩ := hpre e he
    intro hb
    apply hez
    have h1 : ⁅(x : G), z⁆ ∈ ⁅D0, Subgroup.zpowers z⁆ :=
      Subgroup.commutator_mem_commutator hx0 (Subgroup.mem_zpowers z)
    rw [hb, Subgroup.mem_bot] at h1
    have h2 : ⁅x, (⟨z, hzJ⟩ : ↥J)⁆ = 1 := Subtype.ext h1
    rw [← hxe, ← map_commutatorElement, h2, map_one]
  ·
    intro k hk
    have hkD0 := hnorm ⟨k, hKJ hk⟩ (hKE ⟨k, hKJ hk⟩ hk)
    have hkz : k ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hc : Commute k z := Subgroup.mem_centralizer_iff.mp hzC k hk
      exact (hc.zpow_right n).eq.symm
    exact SecA.le_normalizer_commutator (Subgroup.zpowers_le.mpr hkD0)
      (Subgroup.zpowers_le.mpr hkz) (Subgroup.mem_zpowers k)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
