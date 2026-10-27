module

public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsElementaryAbelian p A) : CFSG.IsElementaryAbelian p B :=
  CFSG.IsElementaryAbelian.of_mulEquiv e h

theorem isPOnePlusTwo_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsPOnePlusTwo p A) : IsPOnePlusTwo p B := by
  obtain ⟨hex, hcard, hpow⟩ := h
  have hc : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B :=
    Subgroup.map_center_eq e
  let f : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
    QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e hc
  refine ⟨⟨?_, ?_, ?_⟩, by rw [← Nat.card_congr e.toEquiv]; exact hcard, fun b => ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hex.center_order_p
  · exact isElementaryAbelian_of_mulEquiv f hex.quotient_elementary_abelian
  · have := hex.quotient_nontrivial
    exact f.toEquiv.nontrivial_congr.mp this
  · obtain ⟨a, rfl⟩ := e.surjective b
    rw [← map_pow, hpow, map_one]

namespace E2

variable {Y : Type*} [Group Y] [Finite Y]

theorem twoResidual_eq_pCore {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2)
    (h2P : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ CFSG.Open.pCore p Y) :
    twoResidual (⊤ : Subgroup Y) = CFSG.Open.pCore p Y := by
  have hPn : (CFSG.Open.pCore p Y).Normal := CFSG.LieType.BorelTits.pCore_normal p
  apply le_antisymm
  · exact twoResidual_le_of_isTwoQuotient le_top
      (Subgroup.normalizer_eq_top_iff.mpr hPn).ge fun y _ => h2P y
  · refine le_twoResidual_of_odd ?_
    have : Fact p.Prime := ⟨hpp⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCore_isPGroup (G := Y) p)
    rw [hn]
    exact (hpp.odd_of_ne_two hp2).pow

theorem prime_dvd_card {p : ℕ} (hpp : p.Prime)
    (h2P : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ CFSG.Open.pCore p Y) {q : ℕ} (hq : q.Prime)
    (hqY : q ∣ Nat.card Y) : q = 2 ∨ q = p := by
  by_cases hq2 : q = 2
  · exact Or.inl hq2
  right
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) q hqY
  obtain ⟨k, hk⟩ := h2P y
  have hcop : (orderOf y).Coprime (2 ^ k) := by
    rw [hy]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  have hord : orderOf (y ^ 2 ^ k) = q := by rw [hcop.orderOf_pow, hy]
  have hdvd : q ∣ Nat.card (CFSG.Open.pCore p Y) := by
    have := orderOf_dvd_natCard (⟨y ^ 2 ^ k, hk⟩ : CFSG.Open.pCore p Y)
    rwa [Subgroup.orderOf_mk, hord] at this
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCore_isPGroup (G := Y) p)
  rw [hn] at hdvd
  exact (Nat.prime_dvd_prime_iff_eq hq hpp).mp (hq.dvd_of_dvd_pow hdvd)

theorem centralizer_pCore_le {p : ℕ} (hpp : p.Prime)
    (h2P : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ CFSG.Open.pCore p Y) (hO2 : CFSG.Open.pCore 2 Y = ⊥)
    (hsolv : Group.IsSolvable Y) :
    Subgroup.centralizer (CFSG.Open.pCore p Y : Set Y) ≤ CFSG.Open.pCore p Y := by
  have : Fact p.Prime := ⟨hpp⟩
  have hpp' : CFSG.pPrimeCore p Y = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro K hK hcop
    have hK2 : IsPGroup 2 K := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
      intro d hd hdK
      rcases prime_dvd_card hpp h2P hd (hdK.trans (Subgroup.card_subgroup_dvd_card K)) with h | h
      · exact h
      · exfalso
        rw [h] at hdK
        exact (Nat.Prime.coprime_iff_not_dvd hpp).mp hcop hdK
    have := CFSG.LieType.BorelTits.le_pCore 2 hK hK2
    rw [hO2] at this
    exact le_bot_iff.mp this
  have hFit : CFSG.fittingSubgroup Y = CFSG.Open.pCore p Y := by
    rw [CFSG.Fitting_eq_pcore Y p hpp']
  rw [← hFit]
  exact CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv

theorem eq_one_of_mem_centralizer {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2)
    (h2P : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ CFSG.Open.pCore p Y) (hO2 : CFSG.Open.pCore 2 Y = ⊥)
    (hsolv : Group.IsSolvable Y) {r : Y} {k : ℕ} (hk : r ^ 2 ^ k = 1)
    (hr : r ∈ Subgroup.centralizer (CFSG.Open.pCore p Y : Set Y)) : r = 1 := by
  have : Fact p.Prime := ⟨hpp⟩
  have hrP := centralizer_pCore_le hpp h2P hO2 hsolv hr
  obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := Y) p ⟨r, hrP⟩
  have h1 : orderOf r ∣ p ^ n :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
  have h2 : orderOf r ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (p ^ n) (2 ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hpp Nat.prime_two).mpr hp2)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

end E2

open E2 in
theorem E2_1 {X : Type*} [Group X] [Finite X] {T M : Subgroup X}
    (h : MinParabolic (⊤ : Subgroup X) T M)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2)
    (hsolv : Group.IsSolvable X)
    (hR : ¬ pCoreOf 2 M ≤ CFSG.Open.pCore 2 X ∨
      ∃ t ∈ T, (∀ j ∈ kerIn M ⊤, t * j * t⁻¹ * j⁻¹ ∈ pCoreOf 2 (kerIn M ⊤)) ∧
        t ∉ CFSG.Open.pCore 2 X) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      (Nonempty (twoResidual (⊤ : Subgroup (X ⧸ CFSG.Open.pCore 2 X)) ≃* Multiplicative (ZMod p)) ∨
        IsElemAbelianOfRank p 2 (twoResidual (⊤ : Subgroup (X ⧸ CFSG.Open.pCore 2 X))) ∨
        IsPOnePlusTwo p (twoResidual (⊤ : Subgroup (X ⧸ CFSG.Open.pCore 2 X)))) := by
  obtain ⟨p, hpp, hp2, hO2p2, hJbar, -, -⟩ := h.solvable_structure hsolv
  have : Fact p.Prime := ⟨hpp⟩
  refine ⟨p, hpp, hp2, ?_⟩
  set Q := CFSG.Open.pCore 2 X with hQ
  set φ := QuotientGroup.mk' Q with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective Q
  have hker : φ.ker ≤ M := by
    rw [hφ, QuotientGroup.ker_mk']
    exact h.pCore_le_M
  have hmp := h.map_of_surjective hφs hker
  set P := CFSG.Open.pCore p (X ⧸ Q) with hP
  have hPp : IsPGroup p P := CFSG.LieType.BorelTits.pCore_isPGroup p
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal p
  have h2P : ∀ y : X ⧸ Q, ∃ k : ℕ, y ^ 2 ^ k ∈ P := by
    intro y
    obtain ⟨x, rfl⟩ := hφs y
    obtain ⟨k, hk⟩ := (B6.upperTwo_eq_top_iff (O2p X p)).mp hO2p2 x
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_comap.mp hk⟩
  have hKP : twoResidual (⊤ : Subgroup (X ⧸ Q)) = P := twoResidual_eq_pCore hpp hp2 h2P
  have hO2 : CFSG.Open.pCore 2 (X ⧸ Q) = ⊥ := B6.pCore_quotient_pCore
  have hsolvY : Group.IsSolvable (X ⧸ Q) := inferInstance
  set J := kerIn M ⊤ with hJ
  have hQJ : pCoreOf 2 J ≤ Q := by
    rw [← h.pCoreOf_eq_pCoreOf_kerIn, pCoreOf_top]
  obtain ⟨r, hrT, hrJ, hrQ⟩ : ∃ t ∈ T,
      (∀ j ∈ J, t * j * t⁻¹ * j⁻¹ ∈ pCoreOf 2 J) ∧ t ∉ Q := by
    rcases hR with hM | hex
    · obtain ⟨t, htM, htQ⟩ := Set.not_subset.mp hM
      have hTM : IsSylowTwoOf T M := isSylowTwoOf_mono h.isSylow h.le le_top
      refine ⟨t, pCoreOf_two_le_of_isSylowTwoOf hTM htM, fun j hj => ?_, htQ⟩
      have hjM : j ∈ M := kerIn_le hj
      have hJn : J.Normal := inferInstance
      have hle : pCoreOf 2 M ⊓ J ≤ pCoreOf 2 J := by
        refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
          ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left)
        intro g hg
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (kerIn_le hg),
            Subgroup.le_normalizer hg⟩
      apply hle
      constructor
      · have h1 : j * t⁻¹ * j⁻¹ ∈ pCoreOf 2 M :=
          (Subgroup.mem_normalizer_iff.mp
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hjM) t⁻¹).mp
            ((pCoreOf 2 M).inv_mem htM)
        have := (pCoreOf 2 M).mul_mem htM h1
        simpa [mul_assoc] using this
      · exact J.mul_mem (hJn.conj_mem j hj t) (J.inv_mem hj)
    · exact hex
  set rb := φ r with hrb
  have hrb1 : rb ≠ 1 := by
    rw [hrb, hφ, Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hrQ
  obtain ⟨m, hm⟩ := h.isSylow.2.1 ⟨r, hrT⟩
  have hrbm : rb ^ 2 ^ m = 1 := by
    rw [hrb, ← map_pow]
    have : r ^ 2 ^ m = 1 := congrArg Subtype.val hm
    rw [this, map_one]
  have hrbF : ∀ z ∈ (frattini P).map P.subtype, rb * z = z * rb := by
    intro z hz
    rw [← hJbar] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    have hc : φ (r * j * r⁻¹ * j⁻¹) = 1 := by
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hQJ (hrJ j hj)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hc
    rw [hrb]
    calc φ r * φ j = (φ r * φ j * (φ r)⁻¹ * (φ j)⁻¹) * (φ j * φ r) := by group
      _ = φ j * φ r := by rw [hc, one_mul]
  obtain ⟨X0, hX0, hX0faith⟩ := exists_isSupercritical_faithful (P := P) hp2 hPp
  have hX0top : X0 = ⊤ := by
    apply frattini_nongenerating
    set W : Subgroup (X ⧸ Q) := (X0 ⊔ frattini P).map P.subtype with hW
    have hX0c : X0.Characteristic := hX0.characteristic
    have hWn : W.Normal := by
      refine ⟨fun w hw g => ?_⟩
      obtain ⟨x, hx, rfl⟩ := hw
      have hmap : (X0 ⊔ frattini P).map (MulAut.conjNormal g).toMonoidHom = X0 ⊔ frattini P := by
        rw [Subgroup.map_sup]
        have h1 : X0.map (MulAut.conjNormal g).toMonoidHom = X0 :=
          (Subgroup.characteristic_iff_map_eq.mp hX0c) (MulAut.conjNormal g)
        have h2 : (frattini P).map (MulAut.conjNormal g).toMonoidHom = frattini P :=
          (Subgroup.characteristic_iff_map_eq.mp inferInstance) (MulAut.conjNormal g)
        rw [h1, h2]
      have hmem : (MulAut.conjNormal g) x ∈ X0 ⊔ frattini P := by
        rw [← hmap]
        exact ⟨x, hx, rfl⟩
      exact ⟨_, hmem, by simp [MulAut.conjNormal_apply]⟩
    rcases hmp.le_kerIn_or_twoResidual_le le_top (Subgroup.normalizer_eq_top_iff.mpr hWn).ge with
      hWJ | hKW
    · exfalso
      rw [kerIn_map_top hφs hker, hJbar] at hWJ
      have hX0F : X0 ≤ frattini P := by
        intro x hx
        obtain ⟨y, hy, hyx⟩ := hWJ ⟨x, Subgroup.mem_sup_left hx, rfl⟩
        have : y = x := Subtype.ext hyx
        rwa [← this]
      set α : MulAut P := MulAut.conjNormal rb with hα
      have hαcop : (orderOf α).Coprime p := by
        have h1 : orderOf α ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one (by rw [hα, ← map_pow, hrbm,
          map_one])
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
        rw [hi]
        exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hpp).mpr (Ne.symm hp2))
      have hα1 : α = 1 := by
        refine hX0faith α hαcop fun x hx => ?_
        have hxF : (x : X ⧸ Q) ∈ (frattini P).map P.subtype := ⟨x, hX0F hx, rfl⟩
        have hαx : α x = x := by
          apply Subtype.ext
          rw [hα, MulAut.conjNormal_apply, hrbF _ hxF, mul_inv_cancel_right]
        rw [hαx, inv_mul_cancel]
        exact Subgroup.one_mem _
      apply hrb1
      refine eq_one_of_mem_centralizer hpp hp2 h2P hO2 hsolvY hrbm ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have := congrArg (fun β : MulAut P => ((β ⟨z, hz⟩ : P) : X ⧸ Q)) hα1
      simp only [hα, MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc z * rb = rb * z * rb⁻¹ * rb := by rw [this]
        _ = rb * z := by group
    · rw [hKP] at hKW
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, hy, hyx⟩ := hKW x.2
      have : y = x := Subtype.ext hyx
      rwa [← this]
  have hnt : Nontrivial P := by
    rw [← hKP]
    exact (Subgroup.nontrivial_iff_ne_bot _).mpr hmp.twoResidual_ne_bot
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup P) ≤ 2 := by
    rw [pRank_top_subtype]
    have hQp : ¬ p ∣ Nat.card Q := by
      intro hd
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCore_isPGroup (G := X) 2)
      rw [hn] at hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hd))
    calc CFSG.Open.pRank p P ≤ CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ Q)) :=
          CFSG.SectionRank.pRank_mono hpp.one_lt le_top
      _ = CFSG.Open.pRank p (⊤ : Subgroup X) := CFSG.SectionRank.pRank_quotient_eq Q hQp
      _ ≤ 2 := hSQT p hpp hp2
  have hcases := (hX0top ▸ hX0).iso_cases hp2 hPp hrk
  let e : twoResidual (⊤ : Subgroup (X ⧸ Q)) ≃* (⊤ : Subgroup P) :=
    (MulEquiv.subgroupCongr hKP).trans Subgroup.topEquiv.symm
  rcases hcases with h1 | h2 | h3
  · obtain ⟨f⟩ := h1
    exact Or.inl ⟨e.trans f⟩
  · obtain ⟨f⟩ := h2
    exact Or.inr (Or.inl ⟨e.trans f⟩)
  · exact Or.inr (Or.inr (isPOnePlusTwo_of_mulEquiv e.symm h3))

end CFSG.Quasithin
