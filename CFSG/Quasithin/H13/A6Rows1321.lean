module

public import CFSG.Quasithin.H13.A6RowsModels
public import CFSG.Quasithin.H13.A6S1521Four
public import CFSG.Quasithin.H13.A6S1521Six
public import CFSG.Quasithin.Background.FFC2Ident

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def FactCentA6 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)), B4Hyp G L →
      (B42Case6 G L A ∨ BinaryNaturalSp4 (ffJ G) ⊤ ⊥ 1) →
      ∀ v : MulAut V, A5.Cond1321 G L v → rkIdx (fixV (Subgroup.zpowers v)) = 2 →
        ¬ 9 ∣ Nat.card ↥(L ⊓ Subgroup.centralizer {v})

@[expose] def FactCentA8 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)), B4Hyp G L → B42Case10 G L A →
      ∀ v : MulAut V, A5.Cond1321 G L v → rkIdx (fixV (Subgroup.zpowers v)) = 2 →
        ¬ 9 ∣ Nat.card ↥(L ⊓ Subgroup.centralizer {v})

@[expose] def FactCentG2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)), B4Hyp G L →
      (G2Natural (ffJ G) ⊤ ⊥ 1 ∨ G2NaturalDerived L ⊤ ⊥ 1) →
      ∀ v : MulAut V, A5.Cond1321 G L v → rkIdx (fixV (Subgroup.zpowers v)) = 2 →
        ¬ 9 ∣ Nat.card ↥(L ⊓ Subgroup.centralizer {v})

theorem factCentRows1321_of (h6 : FactCentA6) (h8 : FactCentA8) (hg : FactCentG2) :
    FactCentRows1321 := by
  intro V _ _ hV G L A hB4 hrow v hcond hrk
  rcases hrow with h | h | h | h | h
  · exact h6 V hV G L A hB4 (Or.inl h) v hcond hrk
  · exact h6 V hV G L A hB4 (Or.inr h) v hcond hrk
  · exact h8 V hV G L A hB4 h v hcond hrk
  · exact hg V hV G L hB4 (Or.inl h) v hcond hrk
  · exact hg V hV G L hB4 (Or.inr h) v hcond hrk

@[expose] def FactCommA6 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)), B4Hyp G L →
      (B42Case6 G L A ∨ BinaryNaturalSp4 (ffJ G) ⊤ ⊥ 1) →
      ∀ v : MulAut V, A5.Cond1321 G L v → rkIdx (fixV (Subgroup.zpowers v)) = 2 →
        ∀ S X : Subgroup (MulAut V), IsSylowTwoOf S L → S ≤ Subgroup.centralizer {v} →
          X ≤ L → X ≤ Subgroup.centralizer {v} →
          S ≤ Subgroup.normalizer (X : Set (MulAut V)) → X ≤ oTwoRes X → X ≠ ⊥ →
            A5.commSubOf ⊤ X = ⊤

@[expose] def FactCommA8 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)), B4Hyp G L → B42Case10 G L A →
      ∀ v : MulAut V, A5.Cond1321 G L v → rkIdx (fixV (Subgroup.zpowers v)) = 2 →
        ∀ S X : Subgroup (MulAut V), IsSylowTwoOf S L → S ≤ Subgroup.centralizer {v} →
          X ≤ L → X ≤ Subgroup.centralizer {v} →
          S ≤ Subgroup.normalizer (X : Set (MulAut V)) → X ≤ oTwoRes X → X ≠ ⊥ →
            A5.commSubOf ⊤ X = ⊤

@[expose] def FactCommG2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)), B4Hyp G L →
      (G2Natural (ffJ G) ⊤ ⊥ 1 ∨ G2NaturalDerived L ⊤ ⊥ 1) →
      ∀ v : MulAut V, A5.Cond1321 G L v → rkIdx (fixV (Subgroup.zpowers v)) = 2 →
        ∀ S X : Subgroup (MulAut V), IsSylowTwoOf S L → S ≤ Subgroup.centralizer {v} →
          X ≤ L → X ≤ Subgroup.centralizer {v} →
          S ≤ Subgroup.normalizer (X : Set (MulAut V)) → X ≤ oTwoRes X → X ≠ ⊥ →
            A5.commSubOf ⊤ X = ⊤

theorem factCommRows1321_of (h6 : FactCommA6) (h8 : FactCommA8) (hg : FactCommG2) :
    FactCommRows1321 := by
  intro V _ _ hV G L A hB4 hrow v hcond hrk
  rcases hrow with h | h | h | h | h
  · exact h6 V hV G L A hB4 (Or.inl h) v hcond hrk
  · exact h6 V hV G L A hB4 (Or.inr h) v hcond hrk
  · exact h8 V hV G L A hB4 h v hcond hrk
  · exact hg V hV G L hB4 (Or.inl h) v hcond hrk
  · exact hg V hV G L hB4 (Or.inr h) v hcond hrk

theorem isPGroup_sup_zpowers {Γ : Type} [Group Γ] {p : ℕ} [Fact p.Prime] {x y : Γ}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x) :
    IsPGroup p ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
  have hz : ∀ z : Γ, z ^ p = 1 → IsPGroup p ↥(Subgroup.zpowers z) := by
    rintro z hz ⟨g, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (z ^ k) ^ p ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine IsPGroup.to_sup_of_normal_right' (hz x hx) (hz y hy) ?_
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    change y ^ m = x * y ^ m * x⁻¹
    rw [(Commute.zpow_right hxy m).eq, mul_inv_cancel_right]
  · intro hh
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have hc : x * y ^ m = y ^ m * x := (Commute.zpow_right hxy m).eq
    have e : h = x⁻¹ * (x * h * x⁻¹) * x := by group
    rw [e, ← hm, mul_assoc, ← hc, inv_mul_cancel_left]

theorem isPGroup_sup_zpowers_mk {n : ℕ} {K : Subgroup (Perm (Fin n))} {a b : Perm (Fin n)}
    (ha : a ∈ K) (hb : b ∈ K) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a) :
    IsPGroup 3 ↥(Subgroup.zpowers (⟨a, ha⟩ : ↥K) ⊔ Subgroup.zpowers ⟨b, hb⟩) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  isPGroup_sup_zpowers (Subtype.ext (by rw [Subgroup.coe_pow]; exact ha3))
    (Subtype.ext (by rw [Subgroup.coe_pow]; exact hb3))
    (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hab))

theorem factorization_three_eq_two {n : ℕ} (hn : n ≠ 0) (h9 : 9 ∣ n) (h27 : ¬ 27 ∣ n) :
    n.factorization 3 = 2 := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have h2 : 2 ≤ n.factorization 3 := (h3.pow_dvd_iff_le_factorization hn).1 (by simpa using h9)
  have h3' : ¬ 3 ≤ n.factorization 3 := fun h =>
    h27 (by simpa using (h3.pow_dvd_iff_le_factorization hn).2 h)
  omega

theorem card_alt8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  have h := two_mul_card_alternatingGroup (α := Fin 8)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  rw [Nat.card_eq_fintype_card]
  have : Nat.factorial 8 = 40320 := by decide
  omega

theorem card_sym6 : Nat.card (Perm (Fin 6)) = 720 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem three_pow_factorization_alt6 :
    3 ^ (Nat.card (alternatingGroup (Fin 6))).factorization 3 = 9 := by
  rw [card_alt6, factorization_three_eq_two (by norm_num) (by decide) (by decide)]
  norm_num

theorem three_pow_factorization_sym6 : 3 ^ (Nat.card (Perm (Fin 6))).factorization 3 = 9 := by
  rw [card_sym6, factorization_three_eq_two (by norm_num) (by decide) (by decide)]
  norm_num

theorem three_pow_factorization_alt8 :
    3 ^ (Nat.card (alternatingGroup (Fin 8))).factorization 3 = 9 := by
  rw [card_alt8, factorization_three_eq_two (by norm_num) (by decide) (by decide)]
  norm_num

theorem exists_sub_nine {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}
    {v : MulAut V} (h9 : 9 ∣ Nat.card ↥(L ⊓ Subgroup.centralizer {v})) :
    ∃ P : Subgroup (MulAut V), P ≤ L ∧ P ≤ Subgroup.centralizer {v} ∧ Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₁, hP₁⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2)
    (G := ↥(L ⊓ Subgroup.centralizer {v})) (by rw [show (3 : ℕ) ^ 2 = 9 from rfl]; exact h9)
  refine ⟨P₁.map (L ⊓ Subgroup.centralizer {v}).subtype, ?_, ?_, ?_⟩
  · exact (Subgroup.map_subtype_le P₁).trans inf_le_left
  · exact (Subgroup.map_subtype_le P₁).trans inf_le_right
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hP₁]
    rfl

theorem exists_conj_comm {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} (π : Γ →* ↥H) (hπ : Function.Bijective π) {x y : Γ}
    (hxy : IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y)) {v : MulAut V}
    {P : Subgroup (MulAut V)} (hPH : P ≤ H) (hPC : P ≤ Subgroup.centralizer {v})
    (hP9 : Nat.card P = 3 ^ (Nat.card Γ).factorization 3) :
    ∃ g : Γ, ((π (g * x * g⁻¹) : ↥H) : MulAut V) * v = v * ((π (g * x * g⁻¹) : ↥H) : MulAut V) ∧
      ((π (g * y * g⁻¹) : ↥H) : MulAut V) * v = v * ((π (g * y * g⁻¹) : ↥H) : MulAut V) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hxy.exists_le_sylow
  set P₀ : Subgroup Γ := (P.subgroupOf H).comap π with hP₀
  have hmap : P₀.map π = P.subgroupOf H := Subgroup.map_comap_eq_self_of_surjective hπ.2 _
  have hcard : Nat.card P₀ = Nat.card P := by
    rw [← Subgroup.card_map_of_injective hπ.1, hmap]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  let S : Sylow 3 Γ := Sylow.ofCard P₀ (hcard.trans hP9)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Q S
  have hconj : ∀ z ∈ (Q : Subgroup Γ), ((π (g * z * g⁻¹) : ↥H) : MulAut V) * v =
      v * ((π (g * z * g⁻¹) : ↥H) : MulAut V) := by
    intro z hz
    have h1 : g * z * g⁻¹ ∈ ((g • Q : Sylow 3 Γ) : Subgroup Γ) := ⟨z, hz, rfl⟩
    rw [hg] at h1
    have h2 : π (g * z * g⁻¹) ∈ P.subgroupOf H := h1
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPC (Subgroup.mem_subgroupOf.mp h2))
  exact ⟨g, hconj x (hQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))),
    hconj y (hQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))⟩

theorem conj_comm_aux {K : Type*} [Group K] {Φ R C : K}
    (h : Φ * (R * C * R⁻¹) = R * C * R⁻¹ * Φ) : R⁻¹ * Φ * R * C = C * (R⁻¹ * Φ * R) := by
  calc R⁻¹ * Φ * R * C = R⁻¹ * (Φ * (R * C * R⁻¹)) * R := by group
    _ = R⁻¹ * (R * C * R⁻¹ * Φ) * R := by rw [h]
    _ = C * (R⁻¹ * Φ * R) := by group

theorem conj_sq_aux {K : Type*} [Group K] {Φ R : K} (h : Φ * Φ = 1) :
    R⁻¹ * Φ * R * (R⁻¹ * Φ * R) = 1 := by
  calc R⁻¹ * Φ * R * (R⁻¹ * Φ * R) = R⁻¹ * (Φ * Φ) * R := by group
    _ = 1 := by rw [h]; group

theorem conj_eq_one_aux {K : Type*} [Group K] {Φ R : K} (h : R⁻¹ * Φ * R = 1) : Φ = 1 := by
  calc Φ = R * (R⁻¹ * Φ * R) * R⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem sq_model {V M : Type} [CommGroup V] [Group M] (e : V ≃* M) {v : MulAut V}
    (hv2 : v * v = 1) : (e.symm.trans (v.trans e) : MulAut M) * e.symm.trans (v.trans e) = 1 := by
  refine MulEquiv.ext fun q => ?_
  have hw := congrArg (fun f : MulAut V => f (e.symm q)) hv2
  simp only [MulAut.mul_apply, MulAut.one_apply] at hw ⊢
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hw, MulEquiv.apply_symm_apply]

theorem eq_one_of_model_eq_one {V M : Type} [CommGroup V] [Group M] (e : V ≃* M)
    {v : MulAut V} (h : (e.symm.trans (v.trans e) : MulAut M) = 1) : v = 1 := by
  refine MulEquiv.ext fun w => ?_
  have := congrArg (fun f : MulAut M => f (e w)) h
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at this
  simpa using e.injective this

theorem conj_comm_model {Γ : Type} [Group Γ] {n : ℕ} (ι : Γ →* Perm (Fin n)) {M : Type}
    [Group M] (ρ : Perm (Fin n) →* MulAut M) {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} (π : Γ →* ↥H) (e : V ≃* M)
    (he : ∀ γ w, e (((π γ : ↥H) : MulAut V) w) = ρ (ι γ) (e w)) {v : MulAut V} (g z : Γ)
    (hz : ((π (g * z * g⁻¹) : ↥H) : MulAut V) * v = v * ((π (g * z * g⁻¹) : ↥H) : MulAut V)) :
    (ρ (ι g))⁻¹ * (e.symm.trans (v.trans e) : MulAut M) * ρ (ι g) * ρ (ι z) =
      ρ (ι z) * ((ρ (ι g))⁻¹ * (e.symm.trans (v.trans e) : MulAut M) * ρ (ι g)) := by
  have hK : (e.symm.trans (v.trans e) : MulAut M) * ρ (ι (g * z * g⁻¹)) =
      ρ (ι (g * z * g⁻¹)) * e.symm.trans (v.trans e) := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨w, rfl⟩ := e.surjective q
    have hw := congrArg (fun f : MulAut V => f w) hz
    simp only [MulAut.mul_apply] at hw ⊢
    rw [← he]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [← he, hw]
  simp only [map_mul, map_inv] at hK
  exact conj_comm_aux hK

@[expose] noncomputable def D6.aut6 : Perm (Fin 6) →* MulAut D6.Mod6 :=
  (FFModel.symDn_isActionModel 6).modAct

theorem D6.aut6_apply (σ : Perm (Fin 6)) (q : D6.Mod6) : D6.aut6 σ q = D6.act6 σ q := rfl

@[expose] noncomputable def D8.aut8 : Perm (Fin 8) →* MulAut B5FinS8.Mod8 :=
  (FFModel.symDn_isActionModel 8).modAct

theorem D8.aut8_apply (σ : Perm (Fin 8)) (q : B5FinS8.Mod8) :
    D8.aut8 σ q = B5FinS8.act8 σ q := rfl

theorem eq_one_of_model6 {Γ : Type} [Group Γ] [Finite Γ] (ι : Γ →* Perm (Fin 6))
    {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} (π : Γ →* ↥H) (hπ : Function.Bijective π)
    (e : V ≃* D6.Mod6) (he : ∀ γ w, e (((π γ : ↥H) : MulAut V) w) = D6.aut6 (ι γ) (e w))
    {x y : Γ} (hx : ι x = D6.ca) (hy : ι y = D6.cb)
    (hxy : IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y))
    {v : MulAut V} (hv2 : v * v = 1) {P : Subgroup (MulAut V)} (hPH : P ≤ H)
    (hPC : P ≤ Subgroup.centralizer {v}) (hP9 : Nat.card P = 3 ^ (Nat.card Γ).factorization 3) :
    v = 1 := by
  obtain ⟨g, hgx, hgy⟩ := exists_conj_comm π hπ hxy hPH hPC hP9
  have ha := conj_comm_model ι D6.aut6 π e he g x hgx
  have hb := conj_comm_model ι D6.aut6 π e he g y hgy
  have h2 := conj_sq_aux (R := D6.aut6 (ι g)) (sq_model e hv2)
  rw [hx] at ha
  rw [hy] at hb
  set Φ' : MulAut D6.Mod6 :=
    (D6.aut6 (ι g))⁻¹ * (e.symm.trans (v.trans e) : MulAut D6.Mod6) * D6.aut6 (ι g) with hΦ'
  have hfix := D6.eq_of_comm_sylow Φ'.toMonoidHom Φ'.injective
    (fun q => by
      simpa [MulAut.mul_apply, D6.aut6_apply] using
        congrArg (fun f : MulAut D6.Mod6 => f q) ha)
    (fun q => by
      simpa [MulAut.mul_apply, D6.aut6_apply] using
        congrArg (fun f : MulAut D6.Mod6 => f q) hb)
    (fun q => by simpa [MulAut.mul_apply] using congrArg (fun f : MulAut D6.Mod6 => f q) h2)
  have hΦ'1 : Φ' = 1 := MulEquiv.ext fun q => by simpa using hfix q
  exact eq_one_of_model_eq_one e (conj_eq_one_aux hΦ'1)

theorem rkIdx_le_one_of_model8 {Γ : Type} [Group Γ] [Finite Γ] (ι : Γ →* Perm (Fin 8))
    {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} (π : Γ →* ↥H)
    (hπ : Function.Bijective π) (e : V ≃* B5FinS8.Mod8)
    (he : ∀ γ w, e (((π γ : ↥H) : MulAut V) w) = D8.aut8 (ι γ) (e w))
    {x y : Γ} (hx : ι x = D8.ca) (hy : ι y = D8.cb)
    (hxy : IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y))
    {v : MulAut V} (hv2 : v * v = 1) {P : Subgroup (MulAut V)} (hPH : P ≤ H)
    (hPC : P ≤ Subgroup.centralizer {v}) (hP9 : Nat.card P = 3 ^ (Nat.card Γ).factorization 3) :
    rkIdx (fixV (Subgroup.zpowers v)) ≤ 1 := by
  obtain ⟨g, hgx, hgy⟩ := exists_conj_comm π hπ hxy hPH hPC hP9
  have ha := conj_comm_model ι D8.aut8 π e he g x hgx
  have hb := conj_comm_model ι D8.aut8 π e he g y hgy
  have h2 := conj_sq_aux (R := D8.aut8 (ι g)) (sq_model e hv2)
  rw [hx] at ha
  rw [hy] at hb
  set R := D8.aut8 (ι g) with hR
  set Φ' : MulAut B5FinS8.Mod8 :=
    R⁻¹ * (e.symm.trans (v.trans e) : MulAut B5FinS8.Mod8) * R with hΦ'
  obtain ⟨c, hc⟩ := D8.exists_comm_values Φ'.toMonoidHom Φ'.injective
    (fun q => by
      simpa [MulAut.mul_apply, D8.aut8_apply] using
        congrArg (fun f : MulAut B5FinS8.Mod8 => f q) ha)
    (fun q => by
      simpa [MulAut.mul_apply, D8.aut8_apply] using
        congrArg (fun f : MulAut B5FinS8.Mod8 => f q) hb)
    (fun q => by
      simpa [MulAut.mul_apply] using congrArg (fun f : MulAut B5FinS8.Mod8 => f q) h2)
  have hval : ∀ w : V, v w * w⁻¹ = 1 ∨ v w * w⁻¹ = e.symm (R c) := by
    intro w
    have key : R⁻¹ (e (v w * w⁻¹)) = Φ' (R⁻¹ (e w)) * (R⁻¹ (e w))⁻¹ := by
      rw [hΦ', MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, MulEquiv.trans_apply,
        MulEquiv.trans_apply, MulEquiv.symm_apply_apply, map_mul, map_inv, map_mul, map_inv]
    have hcw := hc (R⁻¹ (e w))
    rw [MulEquiv.coe_toMonoidHom, ← key] at hcw
    rcases hcw with h | h
    · exact Or.inl ((MulEquiv.map_eq_one_iff e).1 ((MulEquiv.map_eq_one_iff R⁻¹).1 h))
    · right
      rw [MulEquiv.eq_symm_apply, ← h, MulAut.apply_inv_self]
  let f : V →* V :=
    { toFun := fun w => v w * w⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hker : f.ker = fixV (Subgroup.zpowers v) := by
    ext w
    rw [MonoidHom.mem_ker]
    change v w * w⁻¹ = 1 ↔ w ∈ fixV (Subgroup.zpowers v)
    rw [mul_inv_eq_one]
    constructor
    · intro h
      refine mem_fixV.mpr fun y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hst : v ∈ MulAction.stabilizer (MulAut V) w := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact h
      have := (MulAction.stabilizer (MulAut V) w).zpow_mem hst k
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
    · intro h
      exact mem_fixV.mp h v (Subgroup.mem_zpowers v)
  have hrange : ((f.range : Subgroup V) : Set V) ⊆ {1, e.symm (R c)} := by
    intro u hu
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hu
    exact hval w
  have hcard : Nat.card f.range ≤ 2 := by
    calc Nat.card f.range = Nat.card ↥((f.range : Subgroup V) : Set V) := rfl
      _ ≤ Nat.card ↥({1, e.symm (R c)} : Set V) := Nat.card_mono (Set.toFinite _) hrange
      _ = ({1, e.symm (R c)} : Set V).ncard := Nat.card_coe_set_eq _
      _ ≤ ({e.symm (R c)} : Set V).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hidx : (fixV (Subgroup.zpowers v)).index ≤ 2 := by
    rw [← hker, Subgroup.index_ker]
    exact hcard
  have hpos : (fixV (Subgroup.zpowers v)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  unfold rkIdx
  rcases (by omega : (fixV (Subgroup.zpowers v)).index = 1 ∨
      (fixV (Subgroup.zpowers v)).index = 2) with h | h
  · rw [h, padicValNat_one_right]
    omega
  · rw [h, padicValNat.self (by norm_num)]

theorem ca_mem6 : D6.ca ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, D6.ca]
  decide

theorem cb_mem6 : D6.cb ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, D6.cb]
  decide

theorem d6_three : D6.ca ^ 3 = 1 ∧ D6.cb ^ 3 = 1 ∧ D6.ca * D6.cb = D6.cb * D6.ca := by
  decide

theorem ca_mem8 : D8.ca ∈ alternatingGroup (Fin 8) :=
  Equiv.Perm.mem_alternatingGroup.2 (B5FinS8.sign_cyc 0 1 2 (by decide) (by decide))

theorem cb_mem8 : D8.cb ∈ alternatingGroup (Fin 8) :=
  Equiv.Perm.mem_alternatingGroup.2 (B5FinS8.sign_cyc 3 4 5 (by decide) (by decide))

theorem d8_three : D8.ca ^ 3 = 1 ∧ D8.cb ^ 3 = 1 ∧ D8.ca * D8.cb = D8.cb * D8.ca := by
  decide +kernel

theorem factCentA6 : FactCentA6 := by
  intro V _ _ hV G L A hB4 hrow v hcond hrk h9
  obtain ⟨P, hPL, hPC, hP9⟩ := exists_sub_nine h9
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ha3, hb3, hab⟩ := d6_three
  rcases hrow with ⟨-, ⟨π, hπ⟩, -⟩ | hSp
  ·
    have hinj := G64.RealizesVia.injective_of_faithful' (G64.altDn_faithful (by norm_num)) hπ
    obtain ⟨e₀, he₀⟩ := G64.RealizesVia.exists_modEquiv hπ
    let e : V ≃* D6.Mod6 := e₀
    have he : ∀ (γ : ↥(alternatingGroup (Fin 6))) (w : V),
        e (((π γ : ↥L) : MulAut V) w) = D6.aut6 ((alternatingGroup (Fin 6)).subtype γ) (e w) := by
      intro γ w
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e w)
      rw [← hm, D6.aut6_apply, D6.act6_mk]
      exact he₀ γ w m (G6.permAct_mem_coreMod (γ : Perm (Fin 6)) m.2) hm.symm
    exact hcond.ne_one (eq_one_of_model6 (alternatingGroup (Fin 6)).subtype π ⟨hinj, hπ.1⟩ e he
      (x := ⟨D6.ca, ca_mem6⟩) (y := ⟨D6.cb, cb_mem6⟩) rfl rfl
      (isPGroup_sup_zpowers_mk ca_mem6 cb_mem6 ha3 hb3 hab) hcond.sq hPL hPC
      (hP9.trans three_pow_factorization_alt6.symm))
  ·
    obtain ⟨-, -, hGJ⟩ := FFC.ident_sp4 hB4 hSp
    have hLG : L ≤ G := hB4.2.1 ▸ quasithinGenFitting_le G
    obtain ⟨π, hπ⟩ := asSp4S6 V _ ⊤ ⊥ hSp
    have hinj := G64.RealizesVia.injective_of_faithful' (G64.symDn_faithful (by norm_num)) hπ
    obtain ⟨e₀, he₀⟩ := G64.RealizesVia.exists_modEquiv hπ
    let e : V ≃* D6.Mod6 := e₀
    have he : ∀ (γ : Perm (Fin 6)) (w : V),
        e (((π γ : ↥(ffJ G)) : MulAut V) w) = D6.aut6 (MonoidHom.id _ γ) (e w) := by
      intro γ w
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e w)
      rw [← hm, MonoidHom.id_apply, D6.aut6_apply, D6.act6_mk]
      exact he₀ γ w m (G6.permAct_mem_coreMod γ m.2) hm.symm
    exact hcond.ne_one (eq_one_of_model6 (MonoidHom.id _) π ⟨hinj, hπ.1⟩ e he
      (x := D6.ca) (y := D6.cb) rfl rfl (isPGroup_sup_zpowers ha3 hb3 hab) hcond.sq
      (hPL.trans (hLG.trans hGJ.le)) hPC (hP9.trans three_pow_factorization_sym6.symm))

theorem factCentA8 : FactCentA8 := by
  intro V _ _ hV G L A hB4 hrow v hcond hrk h9
  obtain ⟨P, hPL, hPC, hP9⟩ := exists_sub_nine h9
  obtain ⟨ha3, hb3, hab⟩ := d8_three
  obtain ⟨π, hπ⟩ := A5.alternatingNatural_eight_of_extSq hrow.1
  have hinj := G64.RealizesVia.injective_of_faithful' (G64.altDn_faithful (by norm_num)) hπ
  obtain ⟨e₀, he₀⟩ := G64.RealizesVia.exists_modEquiv hπ
  let e : V ≃* B5FinS8.Mod8 := e₀
  have he : ∀ (γ : ↥(alternatingGroup (Fin 8))) (w : V),
      e (((π γ : ↥L) : MulAut V) w) = D8.aut8 ((alternatingGroup (Fin 8)).subtype γ) (e w) := by
    intro γ w
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e w)
    rw [← hm, D8.aut8_apply, B5FinS8.act8_mk]
    exact he₀ γ w m (G6.permAct_mem_coreMod (γ : Perm (Fin 8)) m.2) hm.symm
  have := rkIdx_le_one_of_model8 (alternatingGroup (Fin 8)).subtype π ⟨hinj, hπ.1⟩ e he
    (x := ⟨D8.ca, ca_mem8⟩) (y := ⟨D8.cb, cb_mem8⟩) rfl rfl
    (isPGroup_sup_zpowers_mk ca_mem8 cb_mem8 ha3 hb3 hab) hcond.sq hPL hPC
    (hP9.trans three_pow_factorization_alt8.symm)
  omega

end CFSG.Quasithin.H13.A6
