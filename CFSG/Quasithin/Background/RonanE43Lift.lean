module

public import CFSG.Quasithin.Background.RonanE43Central

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42

variable {G : Type} [Group G]

@[expose] def GoodAt (T H : Subgroup G) : Prop :=
  ∀ Y : Subgroup G, Y ≤ H → (∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) → ¬ (Y ⊓ T ≤ pCoreOf 2 H) →
    H ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y)

@[expose] def GoodFamily [Finite G] (T : Subgroup G) (c : ℕ) : Prop :=
  ∃ Δ : Finset (Subgroup G), Δ.Nonempty ∧ (∀ H ∈ Δ, T ≤ H) ∧ (⨆ H ∈ Δ, H) = ⊤ ∧
    (∀ H ∈ Δ, GoodAt T H) ∧
    ∑ H ∈ Δ, CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ c

section Family

variable [Finite G]

theorem aParam_le_of_goodFamily (V : Type) [CommGroup V] [Finite V] (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T L : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hLT : L ⊔ T = ⊤) (hlt : fixV ρ.range < fixV (T.map ρ)) {c : ℕ}
    (hGF : GoodFamily T c) : aParam ρ.range ≤ c := by
  classical
  obtain ⟨Δ, -, hΔT, hΔ, hgood, hsum⟩ := hGF
  have hfix := exists_moved_of_lt ρ hLT hlt
  have hmain := e4_2_of_good G V ρ hρ hO2 T L (↑Δ : Set (Subgroup G)) hT hLF hLq
    (by simpa using hΔ) (fun H hH => hΔT H hH)
    (fun H hH Y hYH hYn hYT => hgood H hH Y hYH hYn hYT) hfix
  refine hmain.trans ?_
  rw [finsum_mem_coe_finset]
  exact hsum

theorem goodAt_of_card_le {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (h2 : Nat.card T ≤ 2 * Nat.card (pCoreOf 2 H)) : GoodAt T H :=
  fun _ hYH hYn hYT => good_of_card_le hT hTH h2 hYH hYn hYT

end Family

section Central

variable {Γ : Type} [Group Γ]

theorem mem_of_map_mem_map (π : G →* Γ) (hker : π.ker ≤ Subgroup.center G)
    (hodd : Nat.Coprime (Nat.card π.ker) 2) {Q : Subgroup G} (hQ : IsPGroup 2 Q) {y : G}
    (hy : π y ∈ Q.map π) {n : ℕ} (hyn : y ^ 2 ^ n = 1) : y ∈ Q := by
  obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hy
  have hz : q⁻¹ * y ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqy, inv_mul_cancel]
  obtain ⟨m, hm⟩ := hQ ⟨q, hq⟩
  have hqm : q ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcomm : Commute q (q⁻¹ * y) := Subgroup.mem_center_iff.mp (hker hz) q
  have hyq : y = q * (q⁻¹ * y) := by group
  have hpow : (q⁻¹ * y) ^ 2 ^ (m + n) = 1 := by
    have h := hcomm.mul_pow (2 ^ (m + n))
    rw [← hyq, pow_add, pow_mul', hyn, one_pow, pow_mul, hqm, one_pow, one_mul] at h
    rw [pow_add]
    exact h.symm
  have hord : orderOf (q⁻¹ * y) = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (π.ker.orderOf_dvd_natCard hz) (Nat.Coprime.pow_right _ hodd))
      (orderOf_dvd_of_pow_eq_one hpow)
  rw [orderOf_eq_one_iff] at hord
  rw [hyq, hord, mul_one]
  exact hq

theorem mem_normalizer_of_map_mem (π : G →* Γ) (hker : π.ker ≤ Subgroup.center G)
    (hodd : Nat.Coprime (Nat.card π.ker) 2) {T : Subgroup G} (hT : IsPGroup 2 T) {g : G}
    (hg : π g ∈ Subgroup.normalizer ((T.map π : Subgroup Γ) : Set Γ)) :
    g ∈ Subgroup.normalizer (T : Set G) := by
  have key : ∀ g : G, π g ∈ Subgroup.normalizer ((T.map π : Subgroup Γ) : Set Γ) →
      ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro g hg t ht
    have h1 : π (g * t * g⁻¹) ∈ T.map π := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp (Subgroup.mem_map_of_mem π ht)
    obtain ⟨n, hn⟩ := hT ⟨t, ht⟩
    have htn : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine mem_of_map_mem_map π hker hodd hT h1 (n := n) ?_
    rw [conj_pow, htn, mul_one, mul_inv_cancel]
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨key g hg t, fun ht => ?_⟩
  have hg' : π g⁻¹ ∈ Subgroup.normalizer ((T.map π : Subgroup Γ) : Set Γ) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hg
  simpa [mul_assoc] using key g⁻¹ hg' _ ht

variable [Finite G] [Finite Γ]

theorem map_pCoreOf_comap_eq (π : G →* Γ) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hodd : Nat.Coprime (Nat.card π.ker) 2)
    (M : Subgroup Γ) : (pCoreOf 2 (M.comap π)).map π = pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (pCoreOf 2 (M.comap π)).map π ≤ pCoreOf 2 M := by
    have := CFSG.LieType.BorelTits.map_pCoreOf_le (r := 2) π (M.comap π)
    rwa [Subgroup.map_comap_eq_self_of_surjective hπ] at this
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_map_eq_of_odd_ker π hodd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (M.comap π))]
  exact card_pCoreOf_le_comap π hπ hker hodd M

theorem goodAt_comap (π : G →* Γ) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hodd : Nat.Coprime (Nat.card π.ker) 2)
    {T : Subgroup G} (hT : IsPGroup 2 T) {M : Subgroup Γ} (hgood : GoodAt (T.map π) M) :
    GoodAt T (M.comap π) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Y hYH hYn hYT
  have hpc := map_pCoreOf_comap_eq π hπ hker hodd M
  have hYM : Y.map π ≤ M := by
    rw [Subgroup.map_le_iff_le_comap]
    exact hYH
  have hYMn : ∀ m ∈ M, ∀ y ∈ Y.map π, m * y * m⁻¹ ∈ Y.map π := by
    intro m hm y hy
    obtain ⟨g, rfl⟩ := hπ m
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨g * y' * g⁻¹, hYn g hm y' hy', ?_⟩
    simp
  have hYT' : ¬ (Y.map π ⊓ T.map π ≤ pCoreOf 2 M) := by
    intro hle
    apply hYT
    intro y hy
    have h1 : π y ∈ Y.map π ⊓ T.map π :=
      ⟨Subgroup.mem_map_of_mem π hy.1, Subgroup.mem_map_of_mem π hy.2⟩
    have h2 := hle h1
    rw [← hpc] at h2
    obtain ⟨n, hn⟩ := hT ⟨y, hy.2⟩
    have hyn : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact mem_of_map_mem_map π hker hodd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) h2 hyn
  have hM := hgood (Y.map π) hYM hYMn hYT'
  intro g hg
  set N : Subgroup G := Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) with hN
  have hkerN : π.ker ≤ N := fun z hz =>
    Subgroup.mem_sup_left ((Subgroup.center_le_normalizer (T : Set G)) (hker hz))
  have hle : Subgroup.normalizer ((T.map π : Subgroup Γ) : Set Γ) ⊔ (T.map π ⊔ Y.map π) ≤
      N.map π := by
    refine sup_le ?_ ?_
    · intro γ hγ
      obtain ⟨g', rfl⟩ := hπ γ
      exact ⟨g', Subgroup.mem_sup_left (mem_normalizer_of_map_mem π hker hodd hT hγ), rfl⟩
    · rw [← Subgroup.map_sup]
      exact Subgroup.map_mono le_sup_right
  obtain ⟨n, hnN, hnπ⟩ := Subgroup.mem_map.mp (hle (hM (show π g ∈ M from hg)))
  have hz : n⁻¹ * g ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnπ, inv_mul_cancel]
  have : g = n * (n⁻¹ * g) := by group
  rw [this]
  exact N.mul_mem hnN (hkerN hz)

theorem pRank_comap_le (π : G →* Γ) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hodd : Nat.Coprime (Nat.card π.ker) 2)
    (M : Subgroup Γ) :
    CFSG.Open.pRank 2 (⊤ : Subgroup (↥(M.comap π) ⧸ CFSG.pCore 2 ↥(M.comap π))) ≤
      CFSG.Open.pRank 2 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := M.comap π with hH
  let πH : ↥H →* ↥M := (π.comp H.subtype).codRestrict M (fun x => x.2)
  have hπHs : Function.Surjective πH := by
    intro m
    obtain ⟨g, hg⟩ := hπ (m : Γ)
    exact ⟨⟨g, by rw [hH, Subgroup.mem_comap, hg]; exact m.2⟩, Subtype.ext hg⟩
  have hπH : ∀ x : ↥H, ((πH x : ↥M) : Γ) = π (x : G) := fun x => rfl
  set P := CFSG.pCore 2 ↥H with hP
  set Q := CFSG.pCore 2 ↥M with hQ
  have hPQ' : P.map πH ≤ Q := CFSG.LieType.BorelTits.map_pCore_le 2 πH hπHs
  have hPQ : P ≤ Q.comap πH := fun x hx => hPQ' (Subgroup.mem_map_of_mem πH hx)
  have hPQeq : P.map πH = Q := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_map]
    have hcomp : M.subtype.comp πH = π.comp H.subtype := rfl
    rw [hcomp, ← Subgroup.map_map]
    exact map_pCoreOf_comap_eq π hπ hker hodd M
  let ψ : ↥H ⧸ P →* ↥M ⧸ Q := QuotientGroup.map P Q πH hPQ
  have hψ : ∀ h : ↥H, ψ (QuotientGroup.mk h) = QuotientGroup.mk (πH h) := fun h => rfl
  have hinj : ∀ x : ↥H ⧸ P, ψ x = 1 → x ^ 2 = 1 → x = 1 := by
    intro x hψx hx2
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : (QuotientGroup.mk (πH h) : ↥M ⧸ Q) = 1 := by rw [← hψ]; exact hψx
    rw [QuotientGroup.eq_one_iff, ← hPQeq] at h1
    obtain ⟨r, hr, hrh⟩ := Subgroup.mem_map.mp h1
    have hz : r⁻¹ * h ∈ πH.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrh, inv_mul_cancel]
    have hzπ : (((r⁻¹ * h : ↥H) : G)) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have := congrArg (fun m : ↥M => (m : Γ)) (MonoidHom.mem_ker.mp hz)
      simpa [hπH] using this
    have hzc : ∀ y : ↥H, y * (r⁻¹ * h) = (r⁻¹ * h) * y := fun y =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hker hzπ) y)
    have hh : h ^ 2 = r ^ 2 * (r⁻¹ * h) ^ 2 := by
      have hrh' : h = r * (r⁻¹ * h) := by group
      conv_lhs => rw [hrh']
      exact (Commute.mul_pow (hzc r) 2)
    have hh2 : h ^ 2 ∈ P := by
      have := hx2
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at this
      exact this
    have hz2 : (r⁻¹ * h) ^ 2 ∈ P := by
      have : (r⁻¹ * h) ^ 2 = (r ^ 2)⁻¹ * h ^ 2 := by
        rw [hh]; group
      rw [this]
      exact P.mul_mem (P.inv_mem (P.pow_mem hr 2)) hh2
    have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCore_isPGroup 2
    obtain ⟨a, ha⟩ := hP2 ⟨_, hz2⟩
    have hza : (r⁻¹ * h) ^ 2 ^ (a + 1) = 1 := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [pow_succ', pow_mul]
      exact this
    have hzG : ((r⁻¹ * h : ↥H) : G) ^ 2 ^ (a + 1) = 1 := by
      have := congrArg Subtype.val hza
      simpa using this
    have hord : orderOf ((r⁻¹ * h : ↥H) : G) = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (π.ker.orderOf_dvd_natCard hzπ)
          (Nat.Coprime.pow_right _ hodd))
        (orderOf_dvd_of_pow_eq_one hzG)
    rw [orderOf_eq_one_iff] at hord
    have hz1 : r⁻¹ * h = 1 := Subtype.ext hord
    have : h = r := by
      have : r * (r⁻¹ * h) = r * 1 := by rw [hz1]
      simpa using this
    rw [QuotientGroup.eq_one_iff, this]
    exact hr
  have hbdd : BddAbove {k | ∃ E : Subgroup (↥M ⧸ Q), E ≤ ⊤ ∧ IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card (↥M ⧸ Q), ?_⟩
    rintro k ⟨E, -, -, hE⟩
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : Nat.card E ≤ Nat.card (↥M ⧸ Q) := Subgroup.card_le_card_group E
    omega
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, -, hE, hEk⟩
  haveI := hE.1
  have hψE : Function.Injective (ψ.comp E.subtype) := by
    intro a b hab
    have hab' : ψ (a : ↥H ⧸ P) = ψ (b : ↥H ⧸ P) := hab
    have hsq : ((a : ↥H ⧸ P) * (b : ↥H ⧸ P)⁻¹) ^ 2 = 1 := by
      have h1 : ((a * b⁻¹ : E) : ↥H ⧸ P) ^ 2 = 1 := by
        have := hE.2 _ (a * b⁻¹).2
        exact this
      simpa using h1
    have hψab : ψ ((a : ↥H ⧸ P) * (b : ↥H ⧸ P)⁻¹) = 1 := by
      rw [map_mul, map_inv, hab', mul_inv_cancel]
    have := hinj _ hψab hsq
    apply Subtype.ext
    exact mul_inv_eq_one.mp this
  have hcard : Nat.card (E.map ψ) = 2 ^ k := by
    have hrange : (ψ.comp E.subtype).range = E.map ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← hEk]
    exact (Nat.card_congr (MonoidHom.ofInjective hψE).toEquiv).symm
  have hE' : IsElemAbelian 2 (E.map ψ) := by
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hE.2 e he, map_one]
  exact le_csSup hbdd ⟨E.map ψ, le_top, hE', hcard⟩

theorem goodFamily_of_central (π : G →* Γ) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hodd : Nat.Coprime (Nat.card π.ker) 2)
    {T : Subgroup G} (hT : IsPGroup 2 T) {c : ℕ} (hGF : GoodFamily (T.map π) c) :
    GoodFamily T c := by
  classical
  obtain ⟨Δ, hne, hΔT, hΔ, hgood, hsum⟩ := hGF
  refine ⟨Δ.image (Subgroup.comap π), hne.image _, ?_, ?_, ?_, ?_⟩
  · intro H hH
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hH
    intro t ht
    exact hΔT M hM (Subgroup.mem_map_of_mem π ht)
  · obtain ⟨M0, hM0⟩ := hne
    set X : Subgroup G := ⨆ H ∈ Δ.image (Subgroup.comap π), H with hX
    have hle : ∀ M ∈ Δ, M.comap π ≤ X := fun M hM =>
      le_iSup₂_of_le (M.comap π) (Finset.mem_image.mpr ⟨M, hM, rfl⟩) le_rfl
    have hXker : π.ker ≤ X := by
      intro g hg
      apply hle M0 hM0
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hg]
      exact Subgroup.one_mem _
    have hXmap : X.map π = ⊤ := by
      rw [eq_top_iff]
      have h1 : (⨆ M ∈ Δ, M) ≤ X.map π := by
        refine iSup₂_le fun M hM => ?_
        calc M = (M.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπ _).symm
          _ ≤ X.map π := Subgroup.map_mono (hle M hM)
      rwa [hΔ] at h1
    have := Subgroup.comap_map_eq_self hXker
    rw [hXmap, Subgroup.comap_top] at this
    exact this.symm
  · intro H hH
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hH
    exact goodAt_comap π hπ hker hodd hT (hgood M hM)
  · rw [Finset.sum_image (fun M₁ _ M₂ _ h => Subgroup.comap_injective hπ h)]
    exact (Finset.sum_le_sum fun M _ => pRank_comap_le π hπ hker hodd M).trans hsum

end Central

end CFSG.Quasithin.RonanE43
