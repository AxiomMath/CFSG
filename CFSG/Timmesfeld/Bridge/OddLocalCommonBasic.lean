module

public import CFSG.Timmesfeld.Bridge.OddLocalBlock
public import CFSG.Timmesfeld.Bridge.OddLocalRoot
public import CFSG.Timmesfeld.Bridge.OddTranspBasic
public import CFSG.Timmesfeld.Closure.Bender

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

namespace OddLocal

variable {G : Type*} [Group G] {D : Set G}

theorem conj_mem_zpowers_mul' {d x : G} (hd : d * d = 1) (hx : x * x = 1) {k : G}
    (hk : k ∈ Subgroup.zpowers (d * x)) : d * k * d ∈ Subgroup.zpowers (d * x) := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have hr : d * (d * x) * d⁻¹ = (d * x)⁻¹ := by
    rw [hdinv, mul_inv_rev, inv_eq_of_mul_eq_one_right hx, hdinv, ← mul_assoc, hd, one_mul]
  have key : d * (d * x) ^ n * d = ((d * x)⁻¹) ^ n := by
    rw [← hr, conj_zpow, hdinv]
  rw [key]
  exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) n

theorem mem_zpowers_or_mul_mem {d x : G} (hd : d * d = 1) (hx : x * x = 1) {g : G}
    (hg : g ∈ Subgroup.closure {d, x}) :
    g ∈ Subgroup.zpowers (d * x) ∨ d * g ∈ Subgroup.zpowers (d * x) := by
  set H := Subgroup.zpowers (d * x) with hH
  have hc : ∀ k ∈ H, d * k * d ∈ H := fun k hk => conj_mem_zpowers_mul' hd hx hk
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · right
      rw [hd]
      exact H.one_mem
    · rw [Set.mem_singleton_iff.1 hy]
      exact Or.inr (Subgroup.mem_zpowers _)
  | one => exact Or.inl H.one_mem
  | mul g h _ _ hg hh =>
    rcases hg with hg | hg <;> rcases hh with hh | hh
    · exact Or.inl (H.mul_mem hg hh)
    · right
      have : d * (g * h) = d * g * d * (d * h) := by
        rw [show d * g * d * (d * h) = d * g * (d * d) * h by group, hd, mul_one, mul_assoc]
      rw [this]
      exact H.mul_mem (hc g hg) hh
    · right
      rw [← mul_assoc]
      exact H.mul_mem hg hh
    · left
      have : g * h = d * (d * g) * d * (d * h) := by
        rw [show d * (d * g) * d * (d * h) = (d * d) * g * (d * d) * h by group, hd, one_mul,
          mul_one]
      rw [this]
      exact H.mul_mem (hc _ hg) hh
  | inv g _ hg =>
    rcases hg with hg | hg
    · exact Or.inl (H.inv_mem hg)
    · right
      have : d * g⁻¹ = d * (d * g)⁻¹ * d := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hd]
        rw [show d * (g⁻¹ * d) * d = d * g⁻¹ * (d * d) by group, hd, mul_one]
      rw [this]
      exact hc _ (H.inv_mem hg)

theorem mul_mem_zpowers_of_mem_closure (hD : IsOddTransp D) {d x : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) {y : G} (hy : y ∈ D) (hyc : y ∈ Subgroup.closure {d, x}) :
    d * y ∈ Subgroup.zpowers (d * x) := by
  rcases mem_zpowers_or_mul_mem (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hx) hyc
    with h | h
  · exfalso
    have hodd : Odd (orderOf (d * x)) := hD.odd_of_not_commute hd hx hdx
    have h1 := orderOf_dvd_of_mem_zpowers h
    rw [hD.orderOf_eq_two hy] at h1
    exact (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hodd h1)) even_two
  · exact h

theorem conj_eq_or_eq_inv_of_mem_closure {e x ρ : G} (he : e * ρ * e⁻¹ = ρ)
    (hx : x * ρ * x⁻¹ = ρ⁻¹) {h : G} (hh : h ∈ Subgroup.closure {e, x}) :
    h * ρ * h⁻¹ = ρ ∨ h * ρ * h⁻¹ = ρ⁻¹ := by
  induction hh using Subgroup.closure_induction with
  | mem k hk =>
    rcases hk with rfl | rfl
    · exact Or.inl he
    · exact Or.inr hx
  | one => left; group
  | mul a b _ _ ha hb =>
    have e1 : a * b * ρ * (a * b)⁻¹ = a * (b * ρ * b⁻¹) * a⁻¹ := by group
    have e2 : a * ρ⁻¹ * a⁻¹ = (a * ρ * a⁻¹)⁻¹ := by group
    rw [e1]
    rcases hb with hb | hb <;> rw [hb]
    · exact ha
    · rw [e2]
      rcases ha with ha | ha
      · exact Or.inr (by rw [ha])
      · exact Or.inl (by rw [ha, inv_inv])
  | inv a _ ha =>
    have e1 : ρ = a⁻¹ * (a * ρ * a⁻¹) * a⁻¹⁻¹ := by group
    rcases ha with ha | ha
    · left
      conv_rhs => rw [e1, ha]
    · right
      have e2 : ρ⁻¹ = a⁻¹ * (a * ρ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
      rw [ha, inv_inv] at e2
      exact e2.symm

theorem commute_of_commute_of_mem_closure (hD : IsOddTransp D) {d x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x) {y : G} (hy : y ∈ D) (hyc : y ∈ Subgroup.closure {d, x})
    (hdy : ¬ Commute d y) {e : G} (he : e ∈ D) (hed : Commute e d) (hey : Commute e y) :
    Commute e x := by
  set ρ := d * y with hρ
  have hρz := mul_mem_zpowers_of_mem_closure hD hd hx hdx hy hyc
  have hx2 := hD.mul_self_eq_one hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxρ : x * ρ * x⁻¹ = ρ⁻¹ := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hρz
    have h1 : x * (d * x) * x⁻¹ = (d * x)⁻¹ := by
      rw [hxi, mul_inv_rev, hxi, hD.inv_eq hd]
      calc x * (d * x) * x = x * d * (x * x) := by group
        _ = x * d := by rw [hx2, mul_one]
    rw [hρ, ← hm, ← conj_zpow, h1, inv_zpow]
  have heρ : e * ρ * e⁻¹ = ρ := by rw [(hed.mul_right hey).eq, mul_inv_cancel_right]
  by_contra hex
  obtain ⟨g, hg, hge⟩ := hD.exists_conj he hx hex
  have hxρ' : x * ρ * x⁻¹ = ρ := by
    have hgi : g⁻¹ ∈ Subgroup.closure {e, x} := Subgroup.inv_mem _ hg
    have e0 : x * ρ * x⁻¹ = g * (e * (g⁻¹ * ρ * g⁻¹⁻¹) * e⁻¹) * g⁻¹ := by rw [← hge]; group
    rcases conj_eq_or_eq_inv_of_mem_closure heρ hxρ hgi with h | h
    · rw [e0, h, heρ]
      have e1 : ρ = g * (g⁻¹ * ρ * g⁻¹⁻¹) * g⁻¹ := by group
      rw [h] at e1
      exact e1.symm
    · have heρ' : e * ρ⁻¹ * e⁻¹ = ρ⁻¹ := by
        rw [show e * ρ⁻¹ * e⁻¹ = (e * ρ * e⁻¹)⁻¹ by group, heρ]
      rw [e0, h, heρ']
      have e1 : ρ⁻¹ = g * (g⁻¹ * ρ * g⁻¹⁻¹)⁻¹ * g⁻¹ := by group
      rw [h, inv_inv] at e1
      rw [show g * ρ⁻¹ * g⁻¹ = (g * ρ * g⁻¹)⁻¹ by group, ← e1, inv_inv]
  have hρ2 : ρ * ρ = 1 := by
    have h1 : ρ = ρ⁻¹ := hxρ'.symm.trans hxρ
    calc ρ * ρ = ρ⁻¹ * ρ := by rw [← h1]
      _ = 1 := inv_mul_cancel ρ
  have hodd : Odd (orderOf ρ) :=
    Odd.of_dvd_nat (hD.odd_of_not_commute hd hx hdx) (orderOf_dvd_of_mem_zpowers hρz)
  have h1 : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hρ2)
  have h2 : orderOf ρ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [orderOf_eq_one_iff] at h2
  exact hdy (hD.eq_of_mul_eq_one hd h2 ▸ Commute.refl d)

theorem IsBenderGroup.commute_trans {K : Type*} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) {i j k : K} (hi : orderOf i = 2)
    (hj : orderOf j = 2) (hk : orderOf k = 2) (hij : Commute i j) (hjk : Commute j k) :
    Commute i k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, m, hB, -⟩ := Asc72.IsBenderGroup.exists_fusionBenderBorel hK
  have hjp : IsPGroup 2 (Subgroup.zpowers j) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hj, pow_one])
  obtain ⟨Q, hQ⟩ := hjp.exists_le_sylow
  have hjQ : j ∈ Q := hQ (Subgroup.mem_zpowers j)
  have hM := (hB Q).1
  have hmemQ : ∀ {t : K}, orderOf t = 2 → Commute t j → t ∈ Q := by
    intro t ht htj
    have htM : t ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) :=
      Connectivity.mem_of_commute_of_stronglyEmbedded hM (Subgroup.le_normalizer hjQ) hj htj
    have htp : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have h2 : IsPGroup 2 ((Q : Subgroup K) ⊔ Subgroup.zpowers t : Subgroup K) :=
      Q.isPGroup'.to_sup_of_normal_left' htp (Subgroup.zpowers_le.mpr htM)
    have heq := Q.is_maximal' h2 le_sup_left
    show t ∈ (Q : Subgroup K)
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hiQ := hmemQ hi hij
  have hkQ := hmemQ hk hjk.symm
  have hi2 : i * i = 1 := by rw [← pow_two, ← hi, pow_orderOf_eq_one]
  exact Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q hiQ hi2 k hkQ

theorem mem_sylow_of_commute [Finite G] (hS : Setup G D) (S : Sylow 2 G) {e : G} (he : e ∈ D)
    (h : ∀ f ∈ D, f ∈ S → Commute e f) : e ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := Subgroup.closure (D ∩ (S : Set G)) with hP
  have hPS : P ≤ S := (Subgroup.closure_le _).mpr fun f hf => hf.2
  set N := Subgroup.normalizer (P : Set G) with hN
  have hSN : (S : Subgroup G) ≤ N := by
    intro s hs
    refine mem_normalizer_closure ?_ ?_
    · rintro f ⟨hfD, hfS⟩
      exact ⟨hS.normal s f hfD, S.mul_mem (S.mul_mem hs hfS) (S.inv_mem hs)⟩
    · rintro f ⟨hfD, hfS⟩
      refine ⟨by simpa using hS.normal s⁻¹ f hfD, S.mul_mem (S.mul_mem (S.inv_mem hs) hfS) hs⟩
  have hcomm : ∀ p ∈ P, Commute e p := by
    intro p hp
    have hle : P ≤ Subgroup.centralizer {e} := by
      rw [hP, Subgroup.closure_le]
      intro f hf
      exact Subgroup.mem_centralizer_singleton_iff.mpr (h f hf.1 hf.2).eq.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hp)).symm
  have heN : e ∈ N := mem_normalizer_of_forall_commute hcomm
  have he2 : IsPGroup 2 (Subgroup.zpowers (⟨e, heN⟩ : N)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hS.oddT.orderOf_eq_two he, pow_one])
  obtain ⟨T', hT'⟩ := he2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N (S.subtype hSN) T'
  have heT : (⟨e, heN⟩ : N) ∈ T' := hT' (Subgroup.mem_zpowers _)
  rw [← hg, ← SetLike.mem_coe, Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem] at heT
  have heS' : g⁻¹ * ⟨e, heN⟩ * g ∈ S.subtype hSN := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using heT
  have h1 : (g : G)⁻¹ * e * g ∈ D ∩ (S : Set G) := by
    refine ⟨by simpa using hS.normal (g : G)⁻¹ e he, ?_⟩
    have h0 : g⁻¹ * ⟨e, heN⟩ * g ∈ (S : Subgroup G).subgroupOf N := heS'
    rw [Subgroup.mem_subgroupOf] at h0
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h0
    exact h0
  have h2 : (g : G)⁻¹ * e * g ∈ P := Subgroup.subset_closure h1
  have h3 := (Subgroup.mem_normalizer_iff.mp g.2 _).mp h2
  have e3 : (g : G) * ((g : G)⁻¹ * e * g) * (g : G)⁻¹ = e := by group
  rw [e3] at h3
  exact hPS h3

theorem exists_conj_mem_sylow [Finite G] (hS : Setup G D) (S T : Sylow 2 G) {a d : G}
    (ha : a ∈ D) (hd : d ∈ D) (haS : a ∈ S) (hdS : d ∈ S) (haT : a ∈ T) (hdT : d ∈ T) {t : G}
    (htD : t ∈ D) (htT : t ∈ T) : ∃ c : G, Commute c a ∧ Commute c d ∧ c * t * c⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.centralizer ({a, d} : Set G) with hK
  have hmemK : ∀ {f : G}, Commute f a → Commute f d → f ∈ K := by
    intro f hfa hfd
    rw [Subgroup.mem_centralizer_iff]
    rintro w (rfl | rfl)
    · exact hfa.eq.symm
    · exact hfd.eq.symm
  have hcommS : ∀ f ∈ D, f ∈ S → Commute f a ∧ Commute f d := fun f hf hfS =>
    ⟨hS.oddT.commute_of_isPGroup S.isPGroup' hf ha hfS haS,
      hS.oddT.commute_of_isPGroup S.isPGroup' hf hd hfS hdS⟩
  set P := Subgroup.closure (D ∩ (S : Set G))
  have hPK : P ≤ K := (Subgroup.closure_le _).mpr fun f hf =>
    hmemK (hcommS f hf.1 hf.2).1 (hcommS f hf.1 hf.2).2
  have hPS : P ≤ S := (Subgroup.closure_le _).mpr fun f hf => hf.2
  have hP2 : IsPGroup 2 (P.subgroupOf K) :=
    (S.isPGroup'.to_le hPS).comap_of_injective K.subtype Subtype.coe_injective
  obtain ⟨R, hR⟩ := hP2.exists_le_sylow
  have htK : t ∈ K := hmemK (hS.oddT.commute_of_isPGroup T.isPGroup' htD ha htT haT)
    (hS.oddT.commute_of_isPGroup T.isPGroup' htD hd htT hdT)
  have ht2 : IsPGroup 2 (Subgroup.zpowers (⟨t, htK⟩ : K)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hS.oddT.orderOf_eq_two htD, pow_one])
  obtain ⟨R', hR'⟩ := ht2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K R R'
  have htR : (⟨t, htK⟩ : K) ∈ R' := hR' (Subgroup.mem_zpowers _)
  rw [← hg, ← SetLike.mem_coe, Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem] at htR
  have htR' : g⁻¹ * ⟨t, htK⟩ * g ∈ R := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using htR
  refine ⟨(g : G)⁻¹, ?_, ?_, ?_⟩
  · have := Subgroup.mem_centralizer_iff.mp (K.inv_mem g.2) a (by simp)
    exact this.symm
  · have := Subgroup.mem_centralizer_iff.mp (K.inv_mem g.2) d (by simp)
    exact this.symm
  ·
    set R₀ := (R : Subgroup K).map K.subtype
    have hR₀2 : IsPGroup 2 R₀ := R.isPGroup'.map K.subtype
    have hmem : (g : G)⁻¹ * t * (g : G)⁻¹⁻¹ ∈ R₀ := ⟨_, htR', by simp⟩
    have hD' : (g : G)⁻¹ * t * (g : G)⁻¹⁻¹ ∈ D := hS.normal _ t htD
    refine mem_sylow_of_commute hS S hD' fun f hf hfS => ?_
    have hfR₀ : f ∈ R₀ := by
      refine ⟨⟨f, hmemK (hcommS f hf hfS).1 (hcommS f hf hfS).2⟩, ?_, rfl⟩
      exact hR (Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨hf, hfS⟩))
    exact hS.oddT.commute_of_isPGroup hR₀2 hD' hf hmem hfR₀

theorem mem_normalizer_of_commute_of_isBlock {F : Set G}
    (hF : MulAction.IsBlock (ConjAct G) F) {f c : G} (hf : f ∈ F) (hcf : Commute c f) :
    c ∈ Subgroup.normalizer F :=
  (isBlock_conj_iff.mp hF) c f hf (by rw [hcf.eq, mul_inv_cancel_right]; exact hf)

theorem commute_of_mem_normalizer_of_not_mem (hD : IsOddTransp D) {F : Set G}
    (hF : MulAction.IsBlock (ConjAct G) F) (hFD : F ⊆ D) {c : G} (hc : c ∈ D)
    (hcN : c ∈ Subgroup.normalizer F) (hcF : c ∉ F) {f : G} (hf : f ∈ F) : Commute c f := by
  by_contra h
  exact hcF (mem_of_not_commute hD (hFD hf) hc (fun h' => h h'.symm) hf
    (mem_normalizer_of_commute_of_isBlock hF hf (Commute.refl f)) hcN)

theorem exists_isMaxOrbit [Finite G] {d : G} (h : (commSet D d).Nonempty) :
    ∃ E, IsMaxOrbit D d E := by
  obtain ⟨e, he, hmax⟩ := Set.exists_max_image (commSet D d) (fun e => (orbitIn D d e).ncard)
    (Set.toFinite _) h
  exact ⟨orbitIn D d e, e, he, rfl, hmax⟩

theorem exists_bad_pair {x d : G} (hd : d ∈ D) (hdx : ¬ Commute d x)
    (hno : ¬ ∃ e ∈ D, Commute e d ∧ Commute e x) (hreach : Reach D d x) :
    ∃ d' ∈ D, ¬ Commute d' x ∧ (¬ ∃ e ∈ D, Commute e d' ∧ Commute e x) ∧
      ∃ d₁ ∈ D, Commute d' d₁ ∧ d₁ ≠ d' ∧ ¬ Commute d₁ x ∧
        ∃ ℓ ∈ D, Commute ℓ d₁ ∧ Commute ℓ x := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd (Commute.refl x) hdx
  | head hvw hwx ih =>
    rename_i v w
    obtain ⟨hv, hw, hvw'⟩ := hvw
    by_cases hbad : ¬ Commute w x ∧ ¬ ∃ e ∈ D, Commute e w ∧ Commute e x
    · exact ih hw hbad.1 hbad.2
    · refine ⟨v, hv, hdx, hno, w, hw, hvw', fun h => ?_, ?_⟩
      · subst h
        exact hbad ⟨hdx, hno⟩
      · by_cases hwx' : Commute w x
        · exact absurd ⟨w, hw, hvw'.symm, hwx'⟩ hno
        · have : ∃ e ∈ D, Commute e w ∧ Commute e x := by
            by_contra h
            exact hbad ⟨hwx', h⟩
          exact ⟨hwx', this⟩

@[expose] def hClass (H : Subgroup G) (y : G) : Set G := {g | ∃ h ∈ H, g = h * y * h⁻¹}

theorem hClass_subset (hN : IsNormalSet D) {H : Subgroup G} {y : G} (hy : y ∈ D) :
    hClass H y ⊆ D := by
  rintro _ ⟨h, -, rfl⟩
  exact hN h y hy

theorem hClass_subset_subgroup {H : Subgroup G} {y : G} (hy : y ∈ H) :
    hClass H y ⊆ (H : Set G) := by
  rintro _ ⟨h, hh, rfl⟩
  exact H.mul_mem (H.mul_mem hh hy) (H.inv_mem hh)

theorem self_mem_hClass (H : Subgroup G) (y : G) : y ∈ hClass H y :=
  ⟨1, H.one_mem, by group⟩

theorem setup_hClass (hD : IsOddTransp D) (hN : IsNormalSet D) {H : Subgroup G} {y : G}
    (hyH : y ∈ H) (hyD : y ∈ D) (hgen : H ≤ Subgroup.closure (hClass H y)) :
    Setup H (((↑) : H → G) ⁻¹' hClass H y) := by
  refine ⟨⟨⟨y, hyH⟩, ?_⟩, (hD.mono (hClass_subset hN hyD)).preimage H, ?_⟩
  · ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h, hh, he⟩
      exact isConj_iff.mpr ⟨⟨h, hh⟩, Subtype.ext (by simpa using he.symm)⟩
    · intro hg
      obtain ⟨c, rfl⟩ := isConj_iff.mp hg
      exact ⟨c, c.2, by simp⟩
  · apply eq_top_of_le_map
    rw [MonoidHom.map_closure]
    refine hgen.trans (Subgroup.closure_mono ?_)
    intro g hg
    exact ⟨⟨g, hClass_subset_subgroup hyH hg⟩, hg, rfl⟩

theorem reach_preimage_iff {H : Subgroup G} {K : Set G} (hKH : K ⊆ H) {a b : H} :
    Reach (((↑) : H → G) ⁻¹' K) a b ↔ Reach K (a : G) (b : G) := by
  constructor
  · intro h
    induction h with
    | refl => exact reach_refl _
    | tail _ hbc ih =>
      exact reach_trans ih (reach_of_commute hbc.1 hbc.2.1 (hbc.2.2.map H.subtype))
  · intro h
    suffices key : ∀ c : G, Reach K (a : G) c → ∀ hc : c ∈ H,
        Reach (((↑) : H → G) ⁻¹' K) a ⟨c, hc⟩ from key _ h b.2
    intro c hc
    induction hc with
    | refl => intro _; exact reach_refl _
    | tail hac hbc ih =>
      rename_i u v
      intro hv
      have hu : u ∈ H := hKH hbc.1
      refine reach_trans (ih hu)
        (reach_of_commute (x := (⟨u, hu⟩ : H)) (y := (⟨v, hv⟩ : H)) hbc.1 hbc.2.1 ?_)
      exact Subtype.ext hbc.2.2.eq

theorem eq_one_of_odd_of_mem_pCore {K : Type*} [Group K] {g : K} (hg : g ∈ CFSG.pCore 2 K)
    (hodd : Odd (orderOf g)) : g = 1 := by
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases i with _ | i
  · rw [pow_zero, orderOf_eq_one_iff] at hi
    exact hi
  · rw [hi, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.not_odd_iff_even])

theorem commute_iff_mod_zStar {K : Type} [Group K] {C : Set K} (hC : IsOddTransp C) {a b : K}
    (ha : a ∈ C) (hb : b ∈ C) :
    Commute (QuotientGroup.mk' (zStar K) a) (QuotientGroup.mk' (zStar K) b) ↔ Commute a b := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  by_contra hnc
  have hodd := hC.odd_of_not_commute ha hb hnc
  set π := QuotientGroup.mk' (zStar K)
  have h1 : π (a * b) = 1 := by
    have h2 : orderOf (π (a * b)) ∣ 2 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_two, map_mul]
      calc π a * π b * (π a * π b) = π a * π a * (π b * π b) := by
            rw [show π a * π b * (π a * π b) = π a * (π b * π a) * π b by group, ← h.eq]
            group
        _ = 1 := by rw [← map_mul, ← map_mul, hC.mul_self_eq_one ha, hC.mul_self_eq_one hb,
            map_one, one_mul]
    have h3 : Odd (orderOf (π (a * b))) := Odd.of_dvd_nat hodd (orderOf_map_dvd π _)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h' | h'
    · exact orderOf_eq_one_iff.mp h'
    · rw [h'] at h3
      exact absurd h3 (by decide)
  have hZ : a * b ∈ zStar K := by
    rw [← QuotientGroup.ker_mk' (zStar K)]
    exact h1
  have hc := (OddTransp.mem_zStar_iff.mp hZ) a
  have e : ⁅a * b, a⁆ = (a * b) * (a * b) := by
    rw [commutatorElement_def, mul_inv_rev, hC.inv_eq ha, hC.inv_eq hb]
    calc a * b * a * (b * a) * a = a * b * a * b * (a * a) := by group
      _ = (a * b) * (a * b) := by rw [hC.mul_self_eq_one ha, mul_one]; group
  rw [e] at hc
  have hodd2 : Odd (orderOf ((a * b) * (a * b))) := by
    rw [← pow_two, orderOf_pow' _ (by norm_num)]
    exact Odd.of_dvd_nat hodd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  have h4 := eq_one_of_odd_of_mem_pCore hc hodd2
  have h5 : orderOf (a * b) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h4)
  have h6 : orderOf (a * b) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h5 with h' | h'
    · exact h'
    · rw [h'] at hodd
      exact absurd hodd (by decide)
  rw [orderOf_eq_one_iff] at h6
  exact hnc (hC.eq_of_mul_eq_one ha h6 ▸ Commute.refl a)

theorem reach_map {K : Type*} [Group K] (φ : G →* K) {a b : G} (h : Reach D a b) :
    Reach (φ '' D) (φ a) (φ b) := by
  induction h with
  | refl => exact reach_refl _
  | tail _ hbc ih =>
    exact reach_trans ih (reach_of_commute ⟨_, hbc.1, rfl⟩ ⟨_, hbc.2.1, rfl⟩ (hbc.2.2.map φ))

end OddLocal

end CFSG.Timmesfeld.Bridge
