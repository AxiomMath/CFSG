module

public import CFSG.Quasithin.EmptyFaithful.S152ZFA5
public import CFSG.Quasithin.Background.F1Cartan
public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Quasithin.F7
open Equiv CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card {L : Subgroup G}
    (hF : Nat.card (OTwoQuot L) = 10 ∨ Nat.card (OTwoQuot L) = 20) : ¬ 3 ∣ Nat.card L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card L = Nat.card (OTwoQuot L) * Nat.card (CFSG.Open.pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥L)
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2).exists_card_eq
  intro h3
  rw [h1, ha] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
  · rcases hF with hF | hF <;> rw [hF] at h <;> omega
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega

theorem alt5_pow : ∀ y : Perm (Fin 5), Perm.sign y = 1 → y ^ 10 = 1 ∨ y ^ 3 = 1 := by
  decide +kernel

theorem pow_ten_of_not_three_dvd (y : Alt5) (h : ¬ 3 ∣ orderOf y) : y ^ 10 = 1 := by
  rcases alt5_pow y (Perm.mem_alternatingGroup.mp y.2) with h' | h'
  · exact Subtype.ext (by simpa using h')
  · by_cases h1 : y = 1
    · rw [h1]; simp
    · exfalso
      apply h
      have h3 : y ^ 3 = 1 := Subtype.ext (by simpa using h')
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [orderOf_eq_prime h3 h1]

theorem card_eq_four_of_sylow {T : Subgroup Alt5} (hT : IsPGroup 2 T) (hodd : ¬ 2 ∣ T.index) :
    Nat.card T = 4 := by
  obtain ⟨a, ha⟩ := hT.exists_card_eq
  have h := Subgroup.card_mul_index T
  rw [a5_card, ha] at h
  have ha2 : a ≤ 2 := by
    by_contra hlt
    have h8 : 2 ^ 3 ∣ 60 := by
      rw [← h]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    norm_num at h8
  interval_cases a
  · exfalso
    apply hodd
    simp at h
    omega
  · exfalso
    apply hodd
    simp at h
    omega
  · simpa using ha

@[expose] noncomputable def piA5 {L : Subgroup G} (e : OTwoQuot L ≃* Alt5) : ↥L →* Alt5 :=
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L))

omit [Finite G] in
theorem piA5_surjective {L : Subgroup G} (e : OTwoQuot L ≃* Alt5) :
    Function.Surjective (piA5 e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem piA5_apply {L : Subgroup G} (e : OTwoQuot L ≃* Alt5) (x : ↥L) :
    piA5 e x = e (QuotientGroup.mk x) := rfl

omit [Finite G] in
theorem piA5_eq_one_iff {L : Subgroup G} (e : OTwoQuot L ≃* Alt5) (x : ↥L) :
    piA5 e x = 1 ↔ x ∈ CFSG.Open.pCore 2 ↥L := by
  rw [piA5_apply, ← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]

omit [Finite G] in
theorem piA5_eq_iff {L : Subgroup G} (e : OTwoQuot L ≃* Alt5) (x y : ↥L) :
    piA5 e x = piA5 e y ↔ y⁻¹ * x ∈ CFSG.Open.pCore 2 ↥L := by
  rw [← piA5_eq_one_iff, map_mul, map_inv, inv_mul_eq_one, eq_comm]

variable {L1 L2 S : Subgroup G}

theorem image_sylow {S L : Subgroup G} (hsyl : IsSylowTwoOf (S ⊓ L) L) (e : OTwoQuot L ≃* Alt5) :
    Nat.card (((S ⊓ L).subgroupOf L).map (piA5 e)) = 4 ∧
      (((borelOf L S).subgroupOf L).map (piA5 e)) =
        Subgroup.normalizer ((((S ⊓ L).subgroupOf L).map (piA5 e) : Subgroup Alt5) : Set Alt5) := by
  obtain ⟨hp, hodd, hmap⟩ := F1.map_borelOf_eq_normalizer hsyl
  set mk : ↥L →* OTwoQuot L := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L) with hmk
  have hπ : piA5 e = (e : OTwoQuot L →* Alt5).comp mk := rfl
  have hV : ((S ⊓ L).subgroupOf L).map (piA5 e) =
      (((S ⊓ L).subgroupOf L).map mk).map (e : OTwoQuot L →* Alt5) := by
    rw [hπ, Subgroup.map_map]
  have hB : ((borelOf L S).subgroupOf L).map (piA5 e) =
      (((borelOf L S).subgroupOf L).map mk).map (e : OTwoQuot L →* Alt5) := by
    rw [hπ, Subgroup.map_map]
  refine ⟨?_, ?_⟩
  · apply card_eq_four_of_sylow
    · rw [hV]; exact hp.map _
    · rw [hV, Subgroup.index_map_equiv]
      exact hodd
  · rw [hB, hV, hmap]
    exact Subgroup.map_normalizer_eq_of_bijective _ e.bijective

theorem image_inf_mem (hS1 : S ≤ Subgroup.normalizer (L1 : Set G))
    (hsyl : IsSylowTwoOf (S ⊓ L2) L2) (e : OTwoQuot L2 ≃* Alt5) (h3 : ¬ 3 ∣ Nat.card L1) :
    ∀ a : ↥L2, (a : G) ∈ L1 → piA5 e a ∈ ((S ⊓ L2).subgroupOf L2).map (piA5 e) := by
  set π := piA5 e with hπ
  set P' : Subgroup ↥L2 := (S ⊓ L2).subgroupOf L2 with hP'
  set V : Subgroup Alt5 := P'.map π with hV
  have hV4 : Nat.card V = 4 := (image_sylow hsyl e).1
  have hA10 : ∀ a : ↥L2, (a : G) ∈ L1 → (π a) ^ 10 = 1 := by
    intro a ha1
    apply pow_ten_of_not_three_dvd
    intro hd
    apply h3
    have h1 : orderOf (π a) ∣ orderOf a := orderOf_map_dvd π a
    have h2 : orderOf (a : G) = orderOf a := Subgroup.orderOf_coe a
    have h4 : orderOf (a : G) ∣ Nat.card L1 := by
      have := orderOf_dvd_natCard (⟨(a : G), ha1⟩ : ↥L1)
      rwa [← Subgroup.orderOf_coe (⟨(a : G), ha1⟩ : ↥L1)] at this
    exact hd.trans (h1.trans (h2 ▸ h4))
  intro a ha1
  by_contra hx
  rcases closure_aux hV4 hx with h | ⟨v, hv, w, hw, h⟩
  · exact h (hA10 a ha1)
  · obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hw
    apply h
    have hpS : (p : G) ∈ S := (Subgroup.mem_inf.mp hp).1
    have hp'S : (p' : G) ∈ S := (Subgroup.mem_inf.mp hp').1
    have hm1 : ((p * a * p⁻¹ : ↥L2) : G) ∈ L1 := by
      have := (Subgroup.mem_normalizer_iff.mp (hS1 hpS) (a : G)).mp ha1
      simpa using this
    have hm2 : ((p' * a * p'⁻¹ : ↥L2) : G) ∈ L1 := by
      have := (Subgroup.mem_normalizer_iff.mp (hS1 hp'S) (a : G)).mp ha1
      simpa using this
    have := hA10 (p * a * p⁻¹ * (p' * a * p'⁻¹)⁻¹)
      (by
        have := L1.mul_mem hm1 (L1.inv_mem hm2)
        simpa using this)
    simpa [map_mul, map_inv] using this

omit [Finite G] in
theorem map_pCore_normalizer (L : Subgroup G) (r : G) (hr : r ∈ Subgroup.normalizer (L : Set G)) :
    (CFSG.Open.pCore 2 ↥L).map ((L.normalizerMonoidHom ⟨r, hr⟩ : ↥L ≃* ↥L) : ↥L →* ↥L) =
      CFSG.Open.pCore 2 ↥L :=
  map_pCore_mulEquiv 2 _

@[expose] noncomputable def actA5 {L : Subgroup G} (e : OTwoQuot L ≃* Alt5) (r : G)
    (hr : r ∈ Subgroup.normalizer (L : Set G)) : Alt5 ≃* Alt5 :=
  e.symm.trans ((QuotientGroup.congr (CFSG.Open.pCore 2 ↥L) (CFSG.Open.pCore 2 ↥L)
    (L.normalizerMonoidHom ⟨r, hr⟩) (map_pCore_normalizer L r hr)).trans e)

omit [Finite G] in
theorem actA5_apply {L : Subgroup G} (e : OTwoQuot L ≃* Alt5) (r : G)
    (hr : r ∈ Subgroup.normalizer (L : Set G)) (x : ↥L) :
    actA5 e r hr (piA5 e x) = piA5 e (L.normalizerMonoidHom ⟨r, hr⟩ x) := by
  unfold actA5
  rw [piA5_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    QuotientGroup.congr_mk, piA5_apply]

omit [Finite G] in
theorem coe_conj_apply {L : Subgroup G} (r : G) (hr : r ∈ Subgroup.normalizer (L : Set G))
    (x : ↥L) : ((L.normalizerMonoidHom ⟨r, hr⟩ x : ↥L) : G) = r * x * r⁻¹ :=
  L.normalizerMonoidHom_apply_apply_coe ⟨r, hr⟩ x

omit [Finite G] in
theorem iterate_conj_apply {L : Subgroup G} (r : G) (hr : r ∈ Subgroup.normalizer (L : Set G))
    (m : ℕ) (x : ↥L) :
    (((⇑(L.normalizerMonoidHom ⟨r, hr⟩ : ↥L ≃* ↥L))^[m] x : ↥L) : G) = r ^ m * x * (r ^ m)⁻¹ := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, coe_conj_apply]
    simp [pow_succ]
    group

omit [Finite G] in
theorem iterate_actA5 {L : Subgroup G} (e : OTwoQuot L ≃* Alt5) (r : G)
    (hr : r ∈ Subgroup.normalizer (L : Set G)) (m : ℕ) (x : ↥L) :
    (⇑(actA5 e r hr))^[m] (piA5 e x) =
      piA5 e ((⇑(L.normalizerMonoidHom ⟨r, hr⟩ : ↥L ≃* ↥L))^[m] x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, actA5_apply, ih, Function.iterate_succ_apply]

theorem mem_pCoreOf_sup_of_comm (hS2 : S ≤ Subgroup.normalizer (L2 : Set G))
    (hS : IsPGroup 2 S) (hsyl : IsSylowTwoOf (S ⊓ L2) L2) {q : G} (hqS : q ∈ S)
    (hq : ∀ l ∈ L2, l⁻¹ * (q * l * q⁻¹) ∈ pCoreOf 2 L2) : q ∈ pCoreOf 2 (L2 ⊔ S) := by
  have hOS : pCoreOf 2 L2 ≤ S ⊓ L2 := isSylowTwoOf_pCoreOf_le hsyl
  set P₂ : Subgroup G := L2 ⊔ S with hP₂
  let D : Subgroup G :=
    { carrier := {x | x ∈ P₂ ∧ ∀ g ∈ P₂, g⁻¹ * x * g ∈ S}
      mul_mem' := fun {a b} ha hb => ⟨P₂.mul_mem ha.1 hb.1, fun g hg => by
        have := S.mul_mem (ha.2 g hg) (hb.2 g hg)
        simpa [mul_assoc] using this⟩
      one_mem' := ⟨P₂.one_mem, fun g _ => by simp⟩
      inv_mem' := fun {a} ha => ⟨P₂.inv_mem ha.1, fun g hg => by
        have := S.inv_mem (ha.2 g hg)
        simpa [mul_assoc] using this⟩ }
  have hDS : D ≤ S := fun x hx => by simpa using hx.2 1 P₂.one_mem
  have hDP : D ≤ P₂ := fun x hx => hx.1
  have hDconj : ∀ h ∈ P₂, ∀ x ∈ D, h * x * h⁻¹ ∈ D := by
    intro h hh x hx
    refine ⟨P₂.mul_mem (P₂.mul_mem hh hx.1) (P₂.inv_mem hh), fun g hg => ?_⟩
    have := hx.2 (h⁻¹ * g) (P₂.mul_mem (P₂.inv_mem hh) hg)
    simpa [mul_assoc] using this
  have hDnorm : P₂ ≤ Subgroup.normalizer (D : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hDconj h hh y hy, fun hy => ?_⟩
    have := hDconj h⁻¹ (P₂.inv_mem hh) _ hy
    simpa [mul_assoc] using this
  have hDp : IsPGroup 2 D := hS.to_le hDS
  have hDle : D ≤ pCoreOf 2 P₂ := le_pCoreOf_of_le_normalizer 2 hDP hDnorm hDp
  apply hDle
  refine ⟨(le_sup_right : S ≤ L2 ⊔ S) hqS, fun g hg => ?_⟩
  obtain ⟨l, hl, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hS2).mp hg
  have hz : l⁻¹ * (q * l * q⁻¹) ∈ S := (Subgroup.mem_inf.mp (hOS (hq l hl))).1
  have h1 : l⁻¹ * q * l ∈ S := by
    have := S.mul_mem hz hqS
    simpa [mul_assoc] using this
  have := S.mul_mem (S.mul_mem (S.inv_mem hs) h1) hs
  simpa [mul_assoc] using this

theorem inf_le_sup_pCore (hS1 : S ≤ Subgroup.normalizer (L1 : Set G))
    (hS2 : S ≤ Subgroup.normalizer (L2 : Set G)) (hS : IsPGroup 2 S)
    (hsyl : IsSylowTwoOf (S ⊓ L2) L2) (hB : borelOf L2 S ≤ Subgroup.normalizer (L1 : Set G))
    (e : OTwoQuot L2 ≃* Alt5) (h3 : ¬ 3 ∣ Nat.card L1) :
    S ⊓ L1 ≤ (S ⊓ L2) ⊔ pCoreOf 2 (L2 ⊔ S) := by
  intro r hr
  have hrS : r ∈ S := hr.1
  have hrL1 : r ∈ L1 := hr.2
  have hrN : r ∈ Subgroup.normalizer (L2 : Set G) := hS2 hrS
  set π := piA5 e with hπ
  set P' : Subgroup ↥L2 := (S ⊓ L2).subgroupOf L2 with hP'
  set V : Subgroup Alt5 := P'.map π with hV
  obtain ⟨hV4, hBV⟩ := image_sylow hsyl e
  set c : ↥L2 ≃* ↥L2 := L2.normalizerMonoidHom ⟨r, hrN⟩ with hc
  set α : Alt5 ≃* Alt5 := actA5 e r hrN with hα
  have hαπ : ∀ x : ↥L2, α (π x) = π (c x) := actA5_apply e r hrN
  have hcoe : ∀ x : ↥L2, ((c x : ↥L2) : G) = r * x * r⁻¹ := coe_conj_apply r hrN
  have h1 : ∀ v ∈ V, α v ∈ V := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hv
    rw [hαπ]
    refine Subgroup.mem_map.mpr ⟨c p, ?_, rfl⟩
    have hpS : (p : G) ∈ S := (Subgroup.mem_inf.mp hp).1
    have hpL : (p : G) ∈ L2 := p.2
    show ((c p : ↥L2) : G) ∈ S ⊓ L2
    rw [hcoe]
    refine ⟨S.mul_mem (S.mul_mem hrS hpS) (S.inv_mem hrS), ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp hrN (p : G)).mp hpL
    simpa using this
  have h2 : ∀ n ∈ Subgroup.normalizer (V : Set Alt5), α n * n⁻¹ ∈ V := by
    intro n hn
    have hn' : n ∈ ((borelOf L2 S).subgroupOf L2).map π := by rw [hBV]; exact hn
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hn'
    rw [hαπ, ← map_inv, ← map_mul]
    apply image_inf_mem hS1 hsyl e h3
    have hbN : (b : G) ∈ Subgroup.normalizer (L1 : Set G) := hB hb
    have h4 := (Subgroup.mem_normalizer_iff.mp hbN (r⁻¹)).mp (L1.inv_mem hrL1)
    have h5 := L1.mul_mem hrL1 h4
    rw [show (((c b * b⁻¹ : ↥L2)) : G) = r * (b * r⁻¹ * b⁻¹) by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe]; group]
    exact h5
  obtain ⟨k, hk⟩ : ∃ k : ℕ, r ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hS ⟨r, hrS⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hkα : ∀ a : Alt5, (⇑α)^[2 ^ k] a = a := by
    intro a
    obtain ⟨x, rfl⟩ := piA5_surjective e a
    rw [iterate_actA5]
    congr 1
    apply Subtype.ext
    rw [iterate_conj_apply, hk]
    simp
  obtain ⟨v, hvV, hv⟩ := sigma_aux hV4 α k hkα h1 h2
  obtain ⟨p, hp, hpv⟩ := Subgroup.mem_map.mp hvV
  have hpS : (p : G) ∈ S := (Subgroup.mem_inf.mp hp).1
  have hpL : (p : G) ∈ L2 := p.2
  have hqS : r * (p : G)⁻¹ ∈ S := S.mul_mem hrS (S.inv_mem hpS)
  have hq : ∀ l ∈ L2, l⁻¹ * ((r * (p : G)⁻¹) * l * (r * (p : G)⁻¹)⁻¹) ∈ pCoreOf 2 L2 := by
    intro l hl
    set x : ↥L2 := ⟨l, hl⟩ with hx
    set y : ↥L2 := p⁻¹ * x * p with hy
    have hπy : π y = (π p)⁻¹ * π x * π p := by simp [hy, map_mul, map_inv]
    have h6 : π (c y) = π x := by
      rw [← hαπ, hv, hπy, hpv]
      group
    have h7 : x⁻¹ * c y ∈ CFSG.Open.pCore 2 ↥L2 := (piA5_eq_iff e (c y) x).mp h6
    have h8 := (F1.mem_pCore_iff_coe _).mp h7
    have h9 : (((x⁻¹ * c y : ↥L2)) : G) = l⁻¹ * ((r * (p : G)⁻¹) * l * (r * (p : G)⁻¹)⁻¹) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe, hy]
      simp [hx]
      group
    rwa [h9] at h8
  have hqP := mem_pCoreOf_sup_of_comm hS2 hS hsyl hqS hq
  have hrq : r = (r * (p : G)⁻¹) * (p : G) := by group
  rw [hrq, sup_comm]
  exact Subgroup.mul_mem_sup hqP (show (p : G) ∈ S ⊓ L2 from hp)

end CFSG.Quasithin.F204
