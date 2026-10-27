module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCCore

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_inj614 {Q : Type} [Group Q] (hZ : Subgroup.center Q = ⊥) {p q : Q}
    (h : MulAut.conj p = MulAut.conj q) : p = q := by
  have hz : ∀ z : Q, p * z * p⁻¹ = q * z * q⁻¹ := fun z => by
    have := congrArg (fun φ : MulAut Q => φ z) h
    simpa using this
  have hc : q⁻¹ * p ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    calc g * (q⁻¹ * p) = q⁻¹ * (q * g * q⁻¹) * p := by group
      _ = q⁻¹ * (p * g * p⁻¹) * p := by rw [hz g]
      _ = q⁻¹ * p * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem conj_comm614 {Q : Type} [Group Q] (α : MulAut Q) (q : Q) :
    MulAut.conj (α q) = α * MulAut.conj q * α⁻¹ := by
  ext z
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem conj_map_mem614 {K A : Subgroup G} (hA : A ≤ Subgroup.normalizer (K : Set G))
    {e : ↥(Subgroup.normalizer (K : Set G))} (he : (e : G) ∈ Subgroup.normalizer (A : Set G))
    {a : MulAut (ModO2 K)}
    (ha : a ∈ (A.subgroupOf (Subgroup.normalizer (K : Set G))).map (actModO2_614 K)) :
    actModO2_614 K e * a * (actModO2_614 K e)⁻¹ ∈
      (A.subgroupOf (Subgroup.normalizer (K : Set G))).map (actModO2_614 K) := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  rw [← map_inv, ← map_mul, ← map_mul]
  refine Subgroup.mem_map.mpr ⟨e * x * e⁻¹, ?_, rfl⟩
  refine Subgroup.mem_subgroupOf.mpr ?_
  have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
  have := (Subgroup.mem_normalizer_iff.mp he (x : G)).mp hxA
  simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this

theorem map_normalizes614 {K A : Subgroup G} (hA : A ≤ Subgroup.normalizer (K : Set G))
    {e : ↥(Subgroup.normalizer (K : Set G))} (he : (e : G) ∈ Subgroup.normalizer (A : Set G)) :
    actModO2_614 K e ∈ Subgroup.normalizer
      (((A.subgroupOf (Subgroup.normalizer (K : Set G))).map (actModO2_614 K) :
        Subgroup (MulAut (ModO2 K))) : Set (MulAut (ModO2 K))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact conj_map_mem614 hA he
  · intro ha
    have he' : ((e⁻¹ : ↥(Subgroup.normalizer (K : Set G))) : G) ∈
        Subgroup.normalizer (A : Set G) := by
      rw [Subgroup.coe_inv]
      exact Subgroup.inv_mem _ he
    have h2 := conj_map_mem614 hA he' ha
    rw [map_inv] at h2
    have e2 : (actModO2_614 K e)⁻¹ * (actModO2_614 K e * a * (actModO2_614 K e)⁻¹) *
        ((actModO2_614 K e)⁻¹)⁻¹ = a := by group
    rw [e2] at h2
    exact h2

theorem card_sylImg614 {K T : Subgroup G} (hT0 : TitsOrderFact) (htits : IsTits (ModO2 K))
    (hS : IsSylowTwoOf (sylImg614 K T) ⊤) : Nat.card ↥(sylImg614 K T) = 2 ^ 11 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS.2.1
  have hmul := Subgroup.relIndex_mul_card (H := sylImg614 K T) (K := (⊤ : Subgroup (ModO2 K)))
  rw [inf_top_eq, Subgroup.card_top, hT0 _ htits, hn] at hmul
  have hodd : ¬ 2 ∣ (sylImg614 K T).relIndex ⊤ := hS.2.2
  set idx := (sylImg614 K T).relIndex ⊤ with hidx
  have hprod : idx * 2 ^ n = 2 ^ 11 * 8775 := by
    rw [hmul]
    norm_num
  have hcop1 : Nat.Coprime (2 ^ 11) idx :=
    Nat.Coprime.pow_left 11 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h11 : 2 ^ 11 ∣ 2 ^ n * idx := ⟨8775, by rw [mul_comm, hprod]⟩
  have hle1 : 11 ≤ n := by
    have := Nat.Coprime.dvd_of_dvd_mul_right hcop1 h11
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hcop2 : Nat.Coprime (2 ^ n) 8775 := Nat.Coprime.pow_left n (by norm_num)
  have hdvd2 : 2 ^ n ∣ 2 ^ 11 * 8775 := ⟨idx, by rw [← hprod, mul_comm]⟩
  have hle2 : n ≤ 11 := by
    have := Nat.Coprime.dvd_of_dvd_mul_right hcop2 hdvd2
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  rw [hn, show n = 11 by omega]

theorem card_hImg614 {K T X : Subgroup G} (hT0 : TitsOrderFact) (htits : IsTits (ModO2 K))
    (hS1 : IsSylowTwoOf (sylImg614 K T) ⊤)
    (hS2 : sylImg614 K T ≤ hImg614 K (X ⊔ (T ⊓ K)))
    (hS3 : (sylImg614 K T).relIndex (hImg614 K (X ⊔ (T ⊓ K))) = 5) :
    Nat.card ↥(hImg614 K (X ⊔ (T ⊓ K))) = 2 ^ 11 * 5 := by
  have h1 := Subgroup.relIndex_mul_card (H := sylImg614 K T)
    (K := hImg614 K (X ⊔ (T ⊓ K)))
  rw [inf_eq_left.mpr hS2, hS3, card_sylImg614 hT0 htits hS1] at h1
  omega

@[expose] noncomputable def phiImg614 (K A : Subgroup G) : Subgroup (MulAut (ModO2 K)) :=
  (A.subgroupOf (Subgroup.normalizer (K : Set G))).map (actModO2_614 K)

theorem phiImg614_mono {K A B : Subgroup G} (h : A ≤ B) : phiImg614 K A ≤ phiImg614 K B :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

theorem phiImg614_isPGroup {K A : Subgroup G} (hA : IsPGroup 2 A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    IsPGroup 2 ↥(phiImg614 K A) := by
  have hY2 : IsPGroup 2 ↥(A.subgroupOf (Subgroup.normalizer (K : Set G))) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hA ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  exact hY2.map (actModO2_614 K)

theorem phiImg614_normalizes {K X O : Subgroup G} (hXK : X ≤ K) (hON : O ≤ Subgroup.normalizer (X : Set G))
    (hOK : O ≤ Subgroup.normalizer (K : Set G)) :
    phiImg614 K O ≤ Subgroup.normalizer ((phiImg614 K X : Subgroup (MulAut (ModO2 K))) :
      Set (MulAut (ModO2 K))) := by
  have hXΓ : X ≤ Subgroup.normalizer (K : Set G) := fun x hx => Subgroup.le_normalizer (hXK hx)
  intro b hb
  unfold phiImg614 at hb ⊢
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hb
  exact map_normalizes614 (K := K) (A := X) hXΓ (hON (Subgroup.mem_subgroupOf.mp hg))

theorem oTwoUpper_phiSup614 {K X O : Subgroup G} (hXK : X ≤ K) (hO2 : IsPGroup 2 O)
    (hOK : O ≤ Subgroup.normalizer (K : Set G)) (hON : O ≤ Subgroup.normalizer (X : Set G))
    (hX2 : X = oTwoUpper X) :
    oTwoUpper (phiImg614 K (X ⊔ O)) = phiImg614 K X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXΓ : X ≤ Subgroup.normalizer (K : Set G) := fun x hx => Subgroup.le_normalizer (hXK hx)
  have hXh_O2 : oTwoUpper (phiImg614 K X) = phiImg614 K X := by
    unfold phiImg614
    rw [oTwoUpper_map, A4.oTwoUpper_subgroupOf hXΓ, ← hX2]
  apply le_antisymm
  · apply oTwoUpper_le_of_pow_mem
    intro w hw
    have hsup : w ∈ phiImg614 K X ⊔ phiImg614 K O := by
      unfold phiImg614 at hw ⊢
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hw
      have hgW : (g : G) ∈ X ⊔ O := Subgroup.mem_subgroupOf.mp hg
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left X O hON] at hgW
      obtain ⟨x, hx, o, ho, hxo⟩ := hgW
      have hxΓ : x ∈ Subgroup.normalizer (K : Set G) := hXΓ hx
      have hoΓ : o ∈ Subgroup.normalizer (K : Set G) := hOK ho
      have hgeq : g = (⟨x, hxΓ⟩ : ↥(Subgroup.normalizer (K : Set G))) * ⟨o, hoΓ⟩ :=
        Subtype.ext hxo.symm
      rw [hgeq, map_mul]
      exact Subgroup.mul_mem_sup
        (Subgroup.mem_map.mpr ⟨⟨x, hxΓ⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)
        (Subgroup.mem_map.mpr ⟨⟨o, hoΓ⟩, Subgroup.mem_subgroupOf.mpr ho, rfl⟩)
    exact CFSG.Quasithin.E1.exists_pow_mem_of_mem_sup
      (phiImg614_isPGroup hO2 hOK) (phiImg614_normalizes hXK hON hOK) hsup
  · exact (le_of_eq hXh_O2.symm).trans (oTwoUpper_mono (phiImg614_mono le_sup_left))

theorem xbar_invariant614 {K X : Subgroup G} (hXK : X ≤ K) (htits : IsTits (ModO2 K))
    (hB : TitsBasicFact) (α : MulAut (ModO2 K))
    (hα : ∀ y ∈ phiImg614 K X, α * y * α⁻¹ ∈ phiImg614 K X) :
    ∀ q ∈ (X.subgroupOf K).map (mk614 K), α q ∈ (X.subgroupOf K).map (mk614 K) := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
  have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
  have hxΓ : (x : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer (hXK hxX)
  have hΦx : actModO2_614 K ⟨(x : G), hxΓ⟩ = MulAut.conj (mk614 K x) :=
    actModO2_614_of_mem K (x : K).2
  have hmem : actModO2_614 K ⟨(x : G), hxΓ⟩ ∈ phiImg614 K X :=
    Subgroup.mem_map.mpr ⟨⟨(x : G), hxΓ⟩, Subgroup.mem_subgroupOf.mpr hxX, rfl⟩
  have h1 := hα _ hmem
  rw [hΦx, ← conj_comm614] at h1
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp h1
  have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
  have hyK : (y : G) ∈ K := hXK hyX
  have hΦy : actModO2_614 K y = MulAut.conj (mk614 K ⟨(y : G), hyK⟩) :=
    actModO2_614_of_mem K hyK
  have hmk : mk614 K ⟨(y : G), hyK⟩ = α (mk614 K x) := by
    apply conj_inj614 (hB _ htits).2.2
    rw [← hΦy]
    exact hyeq
  exact Subgroup.mem_map.mpr ⟨⟨(y : G), hyK⟩, Subgroup.mem_subgroupOf.mpr hyX, hmk⟩

theorem phi_normalizes_phiSup614 {K X O : Subgroup G} (hXK : X ≤ K)
    (hOKn : O ≤ Subgroup.normalizer (K : Set G)) {d : G} (hdK : d ∈ Subgroup.normalizer (K : Set G))
    (hdX : d ∈ Subgroup.normalizer ((X ⊔ O : Subgroup G) : Set G)) :
    actModO2_614 K ⟨d, hdK⟩ ∈ Subgroup.normalizer
      ((phiImg614 K (X ⊔ O) : Subgroup (MulAut (ModO2 K))) : Set (MulAut (ModO2 K))) := by
  unfold phiImg614
  exact map_normalizes614 (K := K) (A := X ⊔ O)
    (sup_le (fun x hx => Subgroup.le_normalizer (hXK hx)) hOKn) (e := ⟨d, hdK⟩) hdX

theorem phi_phiX614 {K X O : Subgroup G} (hXK : X ≤ K) (hO2 : IsPGroup 2 O)
    (hOKn : O ≤ Subgroup.normalizer (K : Set G)) (hON : O ≤ Subgroup.normalizer (X : Set G))
    (hX2 : X = oTwoUpper X) {d : G} (hdK : d ∈ Subgroup.normalizer (K : Set G))
    (hdX : d ∈ Subgroup.normalizer ((X ⊔ O : Subgroup G) : Set G)) (y : MulAut (ModO2 K))
    (hy : y ∈ phiImg614 K X) :
    actModO2_614 K ⟨d, hdK⟩ * y * (actModO2_614 K ⟨d, hdK⟩)⁻¹ ∈ phiImg614 K X := by
  have hO := oTwoUpper_phiSup614 hXK hO2 hOKn hON hX2
  have hφN := phi_normalizes_phiSup614 (O := O) hXK hOKn hdK hdX
  have hy' : y ∈ oTwoUpper (phiImg614 K (X ⊔ O)) := by rw [hO]; exact hy
  have := conj_mem_oTwoUpper hφN hy'
  rwa [hO] at this

theorem phi_xbar614 {K X O : Subgroup G} (hXK : X ≤ K) (hO2 : IsPGroup 2 O)
    (hOKn : O ≤ Subgroup.normalizer (K : Set G)) (hON : O ≤ Subgroup.normalizer (X : Set G))
    (hX2 : X = oTwoUpper X) (htits : IsTits (ModO2 K)) (hB : TitsBasicFact)
    {d : G} (hdK : d ∈ Subgroup.normalizer (K : Set G))
    (hdX : d ∈ Subgroup.normalizer ((X ⊔ O : Subgroup G) : Set G)) :
    ((X.subgroupOf K).map (mk614 K)).map (actModO2_614 K ⟨d, hdK⟩).toMonoidHom =
      (X.subgroupOf K).map (mk614 K) := by
  have hφX := phi_phiX614 hXK hO2 hOKn hON hX2 hdK hdX
  have hφX' : ∀ y ∈ phiImg614 K X, (actModO2_614 K ⟨d, hdK⟩)⁻¹ * y *
      ((actModO2_614 K ⟨d, hdK⟩)⁻¹)⁻¹ ∈ phiImg614 K X := by
    intro y hy
    have hO := oTwoUpper_phiSup614 hXK hO2 hOKn hON hX2
    have hφN := phi_normalizes_phiSup614 (O := O) hXK hOKn hdK hdX
    have hy' : y ∈ oTwoUpper (phiImg614 K (X ⊔ O)) := by rw [hO]; exact hy
    have := conj_mem_oTwoUpper (Subgroup.inv_mem _ hφN) hy'
    rwa [hO] at this
  apply le_antisymm
  · rintro _ ⟨q, hq, rfl⟩
    exact xbar_invariant614 hXK htits hB _ hφX q hq
  · intro q hq
    refine ⟨(actModO2_614 K ⟨d, hdK⟩)⁻¹ q, xbar_invariant614 hXK htits hB _ hφX' q hq, ?_⟩
    exact MulEquiv.apply_symm_apply (actModO2_614 K ⟨d, hdK⟩) q

set_option maxHeartbeats 400000 in
theorem actModO2_d_eq_one614 (hT4 : TitsParabolicNormalizerFact) (hT0 : TitsOrderFact)
    (hB : TitsBasicFact) {T K X O : Subgroup G} (hO2 : IsPGroup 2 O) (hOK : O ≤ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hsyl : IsSylowTwoOf T (K ⊔ T))
    (hXK : X ≤ K) (hX2 : X = oTwoUpper X) (hX5 : (X ⊓ T).relIndex X = 5)
    (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (htits : IsTits (ModO2 K)) {d : G} (hd3 : d ^ 3 = 1)
    (hdK : d ∈ Subgroup.normalizer (K : Set G))
    (hdX : d ∈ Subgroup.normalizer ((X ⊔ O : Subgroup G) : Set G)) :
    actModO2_614 K ⟨d, hdK⟩ = 1 := by
  have hON : O ≤ Subgroup.normalizer (X : Set G) := hOK.trans hTX
  have hOKn : O ≤ Subgroup.normalizer (K : Set G) := hOK.trans hTK
  have hφbar := phi_xbar614 hXK hO2 hOKn hON hX2 htits hB hdK hdX
  obtain ⟨hS1, hS2, hS3⟩ := sylImg614_spec hXK hTK hsyl hTX hX5
  have hO2P : oTwoUpper (((X ⊔ (T ⊓ K)).subgroupOf K).map (mk614 K)) =
      (X.subgroupOf K).map (mk614 K) := oTwoUpper_hImg614 hXK hsyl hTX hX2
  have hP : Nat.card ↥(((X ⊔ (T ⊓ K)).subgroupOf K).map (mk614 K)) = 2 ^ 11 * 5 :=
    card_hImg614 hT0 htits hS1 hS2 hS3
  have h3 : (⟨d, hdK⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hd3)
  have hφ3 : (actModO2_614 K ⟨d, hdK⟩) ^ 3 = 1 := by
    rw [← map_pow, h3, map_one]
  have hφN : (oTwoUpper (((X ⊔ (T ⊓ K)).subgroupOf K).map (mk614 K))).map
      (actModO2_614 K ⟨d, hdK⟩).toMonoidHom =
      oTwoUpper (((X ⊔ (T ⊓ K)).subgroupOf K).map (mk614 K)) := by
    rw [hO2P]
    exact hφbar
  exact hT4 (ModO2 K) htits _ hP _ hφ3 hφN

end CFSG.Quasithin.H13.T614

end
