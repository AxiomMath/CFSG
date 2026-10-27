module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIO1Main
public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFAll

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

section Generic

theorem card_modEq_centralizer_prime {G : Type*} [Group G] [Finite G] {V : Subgroup G} {f : G}
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ z ∈ V, f * z * f⁻¹ ∈ V) (hfp : f ^ p = 1) :
    Nat.card V ≡ Nat.card (V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) [MOD p] := by
  classical
  let σ : Function.End V := fun z => ⟨f * z * f⁻¹, hf z z.2⟩
  have h5 : ∀ (n : ℕ) (z : V), ((σ ^ n) z : G) = f ^ n * z * (f ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro z; simp; rfl
    | succ n ih =>
      intro z
      rw [pow_succ]
      show (((σ ^ n) (σ z) : V) : G) = _
      rw [ih]
      show f ^ n * (f * (z : G) * f⁻¹) * (f ^ n)⁻¹ = _
      simp only [pow_succ]
      group
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext z
    apply Subtype.ext
    have := h5 p z
    rw [hfp] at this
    rw [this]
    simp
    rfl
  have : Fintype V := Fintype.ofFinite V
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := V) (f := σ) (p := p) (n := 1) hσ
  have e : (Function.fixedPoints σ : Set V) ≃
      (V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) :=
    { toFun := fun z => ⟨z.1.1, z.1.2, by
        have h2 : f * (z.1 : G) * f⁻¹ = z.1 := congrArg Subtype.val z.2
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        calc (z.1 : G) * f = (f * z.1 * f⁻¹) * f := by rw [h2]
          _ = f * z.1 := by group⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, by
        apply Subtype.ext
        have h3 : (z.1 : G) * f = f * z.1 := Subgroup.mem_centralizer_singleton_iff.mp z.2.2
        show f * z.1 * f⁻¹ = z.1
        rw [← h3]; group⟩
      left_inv := fun z => rfl
      right_inv := fun z => rfl }
  have : Fintype ↥(V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) := Fintype.ofFinite _
  have : Fintype ↑(Function.fixedPoints σ) := Fintype.ofFinite _
  have hc : Fintype.card ↑(Function.fixedPoints σ) =
      Fintype.card ↥(V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) := Fintype.card_congr e
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← hc]
  convert hmod using 2

theorem phi_eq_one_of_centralizes {G : Type*} [Group G] {V L : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    (hnc : ∃ l : L, ∃ v ∈ V, ¬ Commute (l : G) v) (l : L)
    (hl : ∀ v ∈ V, (l : G) * v = v * (l : G)) : φ l = 1 := by
  classical
  let H : Subgroup L := (Subgroup.centralizer (V : Set G)).comap L.subtype
  have hmem : ∀ m : L, m ∈ H ↔ ∀ v ∈ V, v * (m : G) = (m : G) * v := by
    intro m
    exact Subgroup.mem_centralizer_iff
  have hnormal : H.Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [hmem] at hm ⊢
    intro v hv
    have hg : (g : G)⁻¹ * v * (g : G) ∈ V := by
      refine (Subgroup.mem_normalizer_iff.mp (hLV g.2) _).mpr ?_
      have e : (g : G) * ((g : G)⁻¹ * v * (g : G)) * (g : G)⁻¹ = v := by group
      rw [e]
      exact hv
    have hw := hm _ hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have e1 : v * ((g : G) * (m : G) * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * v * (g : G)) * (m : G)) * (g : G)⁻¹ := by group
    have e2 : ((g : G) * (m : G) * (g : G)⁻¹) * v
        = (g : G) * ((m : G) * ((g : G)⁻¹ * v * (g : G))) * (g : G)⁻¹ := by group
    rw [e1, e2, hw]
  have hker' : ∀ k : L, φ k = 1 → k ∈ H := fun k hk =>
    (hmem k).mpr fun v hv => Subgroup.mem_centralizer_iff.mp (hker k hk) v hv
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have := Subgroup.Normal.map hnormal φ hφ
  rcases Subgroup.Normal.eq_bot_or_eq_top (H.map φ) with hb | ht
  · have h2 : φ l ∈ H.map φ := Subgroup.mem_map_of_mem φ ((hmem l).mpr fun v hv => (hl v hv).symm)
    rw [hb, Subgroup.mem_bot] at h2
    exact h2
  · exfalso
    have hall : ∀ m : L, m ∈ H := fun m =>
      mem_of_map_mem_of_ker H φ hker' m (by rw [ht]; exact Subgroup.mem_top _)
    obtain ⟨l0, v, hv, hnot⟩ := hnc
    exact hnot ((hmem l0).mp (hall l0) v hv).symm


theorem map_conj_eq_of_mem_normalizer {N : Type*} [Group N] (K : Subgroup N) {x : N}
    (hx : x ∈ Subgroup.normalizer (K : Set N)) : K.map (MulAut.conj x).toMonoidHom = K := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx k).mp hk
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by simp [MulAut.conj_apply]; group⟩
    refine (Subgroup.mem_normalizer_iff.mp hx _).mpr ?_
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [e]; exact hy

theorem mem_normalizer_map_conj {N : Type*} [Group N] (K : Subgroup N) {x w : N}
    (h : w⁻¹ * x * w ∈ Subgroup.normalizer (K : Set N)) :
    x ∈ Subgroup.normalizer ((K.map (MulAut.conj w).toMonoidHom : Subgroup N) : Set N) := by
  have hmem : ∀ y : N, y ∈ K.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * y * w ∈ K := by
    intro y
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hk
    · intro hy
      exact ⟨w⁻¹ * y * w, hy, by simp [MulAut.conj_apply]; group⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [hmem, hmem]
  have := Subgroup.mem_normalizer_iff.mp h (w⁻¹ * y * w)
  have e : (w⁻¹ * x * w) * (w⁻¹ * y * w) * (w⁻¹ * x * w)⁻¹ = w⁻¹ * (x * y * x⁻¹) * w := by group
  rw [e] at this
  exact this


end Generic

section FixThree

variable {G : Type*} [Group G] [Finite G] {V L : Subgroup G}

theorem CV_conj_mem (hLV : L ≤ Subgroup.normalizer (V : Set G)) (l : L) (T : Subgroup L) {k : G}
    (hk : k ∈ V ⊓ Subgroup.centralizer ((T.map L.subtype : Subgroup G) : Set G)) :
    (l : G) * k * (l : G)⁻¹ ∈ V ⊓
      Subgroup.centralizer (((T.map (MulAut.conj l).toMonoidHom).map L.subtype : Subgroup G) :
        Set G) := by
  rw [mem_inf_centralizer_iff] at hk ⊢
  obtain ⟨hkV, hkc⟩ := hk
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hLV l.2) k).mp hkV, fun t' ht' => ?_⟩
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ht'
  have := hkc t ht
  have e : ((((MulAut.conj l).toMonoidHom t : L)) : G) = (l : G) * (t : G) * (l : G)⁻¹ := by
    simp [MulAut.conj_apply]
  rw [e]
  calc (l : G) * k * (l : G)⁻¹ * ((l : G) * (t : G) * (l : G)⁻¹)
      = (l : G) * (k * (t : G)) * (l : G)⁻¹ := by group
    _ = (l : G) * ((t : G) * k) * (l : G)⁻¹ := by rw [this]
    _ = (l : G) * (t : G) * (l : G)⁻¹ * ((l : G) * k * (l : G)⁻¹) := by group


theorem fix_three_abs
    (hV2 : ∀ a ∈ V, a * a = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    (hnc : ∃ l : L, ∃ v ∈ V, ¬ Commute (l : G) v)
    (h16 : Nat.card V = 16 * Nat.card (V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G))
    (hC4 : ∀ T : Subgroup L, Nat.card (T.map φ) = 4 →
      Nat.card (V ⊓ Subgroup.centralizer ((T.map L.subtype : Subgroup G) : Set G) : Subgroup G) =
        4 * Nat.card (V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G))
    (hmeet : ∀ T₁ T₂ : Subgroup L, Nat.card (T₁.map φ) = 4 → Nat.card (T₂.map φ) = 4 →
      T₁.map φ ≠ T₂.map φ →
      (V ⊓ Subgroup.centralizer ((T₁.map L.subtype : Subgroup G) : Set G)) ⊓
        (V ⊓ Subgroup.centralizer ((T₂.map L.subtype : Subgroup G) : Set G)) =
        V ⊓ Subgroup.centralizer (L : Set G))
    {T₁ : Subgroup L} (hT₁ : Nat.card (T₁.map φ) = 4) {r : L} (hr3 : r ^ 3 = 1)
    (hrT : φ r ∈ Subgroup.normalizer ((T₁.map φ : Subgroup (alternatingGroup (Fin 5))) :
      Set (alternatingGroup (Fin 5))))
    (hr1 : φ r ≠ 1) :
    ∀ v ∈ V, (r : G) * v = v * (r : G) → v ∈ Subgroup.centralizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C₀ : Subgroup G := V ⊓ Subgroup.centralizer (L : Set G) with hC₀
  have hVcomm := comm_of_sq_one hV2
  have hVp : IsPGroup 2 V := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (by simpa using hV2 g.1 g.2)
  have hc3 : ¬ 3 ∣ Nat.card C₀ := by
    obtain ⟨n, hn⟩ := hVp.exists_card_eq
    have h1 : Nat.card C₀ ∣ 2 ^ n := by
      rw [← hn]; exact Subgroup.card_dvd_of_le inf_le_left
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h3.trans h1)
    omega
  have hc0 : 0 < Nat.card C₀ := Nat.card_pos
  have hρ3 : φ r ^ 3 = 1 := by rw [← map_pow, hr3, map_one]
  obtain ⟨w0, hw02, hw0ρ⟩ := alt5_exists_inverter (φ r) hρ3
  have hw0N := alt5_inverter_not_mem_normalizer hT₁ hrT hρ3 hr1 hw02 hw0ρ
  obtain ⟨w, hw⟩ := hφ w0
  set T₂ : Subgroup L := T₁.map (MulAut.conj w).toMonoidHom with hT₂
  have hT₂map : T₂.map φ = (T₁.map φ).map (MulAut.conj w0).toMonoidHom := by
    rw [hT₂, map_map_conj, hw]
  have hT₂4 : Nat.card (T₂.map φ) = 4 := by
    rw [hT₂map, Subgroup.card_map_of_injective (MulAut.conj w0).injective, hT₁]
  have hne : T₁.map φ ≠ T₂.map φ := by
    rw [hT₂map]; exact (map_conj_ne _ w0 hw0N).symm
  have hD₁ := hC4 T₁ hT₁
  have hD₂ := hC4 T₂ hT₂4
  have hD12 := hmeet T₁ T₂ hT₁ hT₂4 hne
  set D₁ : Subgroup G := V ⊓ Subgroup.centralizer ((T₁.map L.subtype : Subgroup G) : Set G) with hD₁def
  set D₂ : Subgroup G := V ⊓ Subgroup.centralizer ((T₂.map L.subtype : Subgroup G) : Set G) with hD₂def
  have hD₁V : D₁ ≤ V := inf_le_left
  have hD₂V : D₂ ≤ V := inf_le_left
  have hC₀D₁ : C₀ ≤ D₁ := by
    refine le_inf inf_le_left (le_trans inf_le_right (Subgroup.centralizer_le ?_))
    rintro _ ⟨t, -, rfl⟩; exact t.2
  have hC₀D₂ : C₀ ≤ D₂ := by
    refine le_inf inf_le_left (le_trans inf_le_right (Subgroup.centralizer_le ?_))
    rintro _ ⟨t, -, rfl⟩; exact t.2
  have hVD : ∀ v ∈ V, ∃ k ∈ D₁, ∃ q ∈ D₂, v = k * q := by
    have hnorm : (D₂.subgroupOf V).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have : ((g * n * g⁻¹ : ↥V) : G) = n := by
        have := hVcomm g g.2 n (hD₂V (Subgroup.mem_subgroupOf.mp ((Subgroup.mem_subgroupOf).mpr hn)))
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [this]; group
      rw [this]; exact hn⟩
    let φ' : ↥V →* ↥V ⧸ D₂.subgroupOf V := QuotientGroup.mk' _
    have hker' : ∀ p : ↥V, φ' p = 1 ↔ (p : G) ∈ D₂ := fun p => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; rfl
    have key := exists_mul_ker_of_card (P := V) (K := D₁) (M := V) (Q := D₂) φ' hker' hD₁V le_rfl (by
      rw [hD12, inf_eq_right.mpr hD₂V, hD₁, hD₂, h16]; ring)
    intro v hv
    obtain ⟨k, hk, hkq⟩ := key v hv
    exact ⟨k, hk, k⁻¹ * v, hkq, by group⟩
  have hνmap : ∀ T : Subgroup L, φ r ∈ Subgroup.normalizer
      ((T.map φ : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5))) →
      (T.map (MulAut.conj r).toMonoidHom).map φ = T.map φ := by
    intro T hT
    rw [map_map_conj]
    exact map_conj_eq_of_mem_normalizer _ hT
  have hD₁r : ∀ k ∈ D₁, (r : G) * k * (r : G)⁻¹ ∈ D₁ := by
    intro k hk
    have h1 := CV_conj_mem hLV r T₁ hk
    rwa [inf_centralizer_eq_of_map_eq φ hker (hνmap T₁ hrT)] at h1
  have hρT₂ : φ r ∈ Subgroup.normalizer ((T₂.map φ : Subgroup (alternatingGroup (Fin 5))) :
      Set (alternatingGroup (Fin 5))) := by
    rw [hT₂map]
    apply mem_normalizer_map_conj (K := T₁.map φ)
    have : w0⁻¹ * φ r * w0 = (φ r)⁻¹ := by
      have h := hw0ρ
      have hw0inv : w0⁻¹ = w0 := inv_eq_of_mul_eq_one_right hw02
      rw [hw0inv]
      rw [hw0inv] at h
      exact h
    rw [this]
    exact (Subgroup.normalizer _).inv_mem hrT
  have hD₂r : ∀ k ∈ D₂, (r : G) * k * (r : G)⁻¹ ∈ D₂ := by
    intro k hk
    have h1 := CV_conj_mem hLV r T₂ hk
    rwa [inf_centralizer_eq_of_map_eq φ hker (hνmap T₂ hρT₂)] at h1
  have hcount : ∀ D : Subgroup G, D ≤ V → C₀ ≤ D → Nat.card D = 4 * Nat.card C₀ →
      (∀ k ∈ D, (r : G) * k * (r : G)⁻¹ ∈ D) →
      D ⊓ Subgroup.centralizer ({(r : G)} : Set G) = C₀ ∨
        ∀ k ∈ D, (r : G) * k = k * (r : G) := by
    intro D hDV hCD hDcard hDr
    have hr3' : (r : G) ^ 3 = 1 := by
      have := congrArg Subtype.val hr3
      simpa using this
    have hmod := card_modEq_centralizer_prime (V := D) (f := (r : G)) 3 hDr hr3'
    set E : Subgroup G := D ⊓ Subgroup.centralizer ({(r : G)} : Set G) with hE
    have hC₀E : C₀ ≤ E := by
      refine le_inf hCD (le_trans inf_le_right (Subgroup.centralizer_le ?_))
      rintro _ rfl; exact r.2
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hC₀E
    have hEdvd : Nat.card E ∣ 4 * Nat.card C₀ := hDcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hmdvd : m ∣ 4 := by
      rw [hm] at hEdvd
      have : Nat.card C₀ * m ∣ Nat.card C₀ * 4 := by rw [mul_comm (Nat.card C₀) 4]; exact hEdvd
      exact Nat.dvd_of_mul_dvd_mul_left hc0 this
    have hmod' : Nat.card C₀ * 4 ≡ Nat.card C₀ * m [MOD 3] := by
      rw [mul_comm (Nat.card C₀) 4, ← hDcard, ← hm]; exact hmod
    have hcop : Nat.Coprime (Nat.card C₀) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hc3).symm
    have h43 := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hcop) hmod'
    have hm4 : m = 1 ∨ m = 4 := by
      obtain ⟨i, hi, hmi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (show m ∣ 2 ^ 2 by norm_num; exact hmdvd)
      have h43' : 4 % 3 = m % 3 := h43
      interval_cases i
      · left; simpa using hmi
      · exfalso; rw [hmi] at h43'; norm_num at h43'
      · right; simpa using hmi
    rcases hm4 with h1 | h4
    · left
      subst h1
      exact (Subgroup.eq_of_le_of_card_ge hC₀E (by rw [hm]; simp)).symm
    · right
      subst h4
      have hED : E = D := Subgroup.eq_of_le_of_card_ge (inf_le_left : E ≤ D) (by rw [hm, hDcard]; omega)
      intro k hk
      have : k ∈ E := hED ▸ hk
      exact (Subgroup.mem_centralizer_singleton_iff.mp this.2).symm
  have hκ : φ (r * (w⁻¹ * r * w)) = 1 := by
    have hw0inv : w0⁻¹ = w0 := inv_eq_of_mul_eq_one_right hw02
    have h1 : w0⁻¹ * φ r * w0 = (φ r)⁻¹ := by
      rw [hw0inv]; rw [hw0inv] at hw0ρ; exact hw0ρ
    rw [map_mul, map_mul, map_mul, map_inv, hw, h1]
    group
  have hκV := Subgroup.mem_centralizer_iff.mp (hker _ hκ)
  set R : G := (r : G) with hR
  set W : G := (w : G) with hW
  have hRR3 : R ^ 3 = 1 := by
    have := congrArg Subtype.val hr3
    simpa using this
  have hrel : W⁻¹ * R * W = R⁻¹ * (R * (W⁻¹ * R * W)) := by group
  have hκc : ∀ v ∈ V, (R * (W⁻¹ * R * W)) * v = v * (R * (W⁻¹ * R * W)) := by
    intro v hv
    have := hκV v hv
    simpa using this.symm
  have hD₁D₂ : ∀ k ∈ D₁, W * k * W⁻¹ ∈ D₂ := fun k hk => CV_conj_mem hLV w T₁ hk
  have hD₂D₁ : ∀ k₂ ∈ D₂, W⁻¹ * k₂ * W ∈ D₁ := by
    intro k₂ hk₂
    have h1 := CV_conj_mem hLV w⁻¹ T₂ hk₂
    have e : T₂.map (MulAut.conj w⁻¹).toMonoidHom = T₁ := by
      rw [hT₂, Subgroup.map_map]
      have : (MulAut.conj w⁻¹).toMonoidHom.comp (MulAut.conj w).toMonoidHom = MonoidHom.id L := by
        ext x; (simp [MulAut.conj_apply]; group)
      rw [this, Subgroup.map_id]
    rw [e] at h1
    have e2 : (((w⁻¹ : L) : G)) * k₂ * ((w⁻¹ : L) : G)⁻¹ = W⁻¹ * k₂ * W := by simp [hW]
    rw [e2] at h1
    exact h1
  have hcentD₁D₂ : (∀ k ∈ D₁, R * k = k * R) → ∀ k₂ ∈ D₂, R * k₂ = k₂ * R := by
    intro h k₂ hk₂
    have hk := hD₂D₁ k₂ hk₂
    have hkV : W⁻¹ * k₂ * W ∈ V := hD₁V hk
    have h1 := h _ hk
    have h2 := hκc _ hkV
    have e : k₂ = W * (W⁻¹ * k₂ * W) * W⁻¹ := by group
    set k := W⁻¹ * k₂ * W with hk'
    have hconj : R * (W * k * W⁻¹) * R⁻¹ = W * k * W⁻¹ := by
      calc R * (W * k * W⁻¹) * R⁻¹ = W * (W⁻¹ * R * W) * k * (W⁻¹ * R * W)⁻¹ * W⁻¹ := by group
        _ = W * (R⁻¹ * (R * (W⁻¹ * R * W))) * k * (R⁻¹ * (R * (W⁻¹ * R * W)))⁻¹ * W⁻¹ := by
            rw [← hrel]
        _ = W * R⁻¹ * ((R * (W⁻¹ * R * W)) * k * (R * (W⁻¹ * R * W))⁻¹) * R * W⁻¹ := by group
        _ = W * R⁻¹ * k * R * W⁻¹ := by rw [h2]; group
        _ = W * k * W⁻¹ := by
            have : R⁻¹ * k * R = k := by
              calc R⁻¹ * k * R = R⁻¹ * (k * R) := by group
                _ = R⁻¹ * (R * k) := by rw [h1]
                _ = k := by group
            calc W * R⁻¹ * k * R * W⁻¹ = W * (R⁻¹ * k * R) * W⁻¹ := by group
              _ = W * k * W⁻¹ := by rw [this]
    rw [← e] at hconj
    calc R * k₂ = (R * k₂ * R⁻¹) * R := by group
      _ = k₂ * R := by rw [hconj]
  have hcentD₂D₁ : (∀ k ∈ D₂, R * k = k * R) → ∀ k ∈ D₁, R * k = k * R := by
    intro h k hk
    have hk₂ := hD₁D₂ k hk
    have hkV : k ∈ V := hD₁V hk
    have h1 := h _ hk₂
    have h2 := hκc _ hkV
    have hconj : W⁻¹ * R * W * k * (W⁻¹ * R * W)⁻¹ = k := by
      calc W⁻¹ * R * W * k * (W⁻¹ * R * W)⁻¹ = W⁻¹ * (R * (W * k * W⁻¹) * R⁻¹) * W := by group
        _ = W⁻¹ * (W * k * W⁻¹) * W := by
            have : R * (W * k * W⁻¹) = (W * k * W⁻¹) * R := h1
            rw [this]; group
        _ = k := by group
    rw [hrel] at hconj
    have hk3 : R⁻¹ * k * R = k := by
      calc R⁻¹ * k * R = R⁻¹ * ((R * (W⁻¹ * R * W)) * k * (R * (W⁻¹ * R * W))⁻¹) * R := by
            rw [h2]; group
        _ = R⁻¹ * (R * (W⁻¹ * R * W)) * k * (R * (W⁻¹ * R * W))⁻¹ * R := by group
        _ = (R⁻¹ * (R * (W⁻¹ * R * W))) * k * (R⁻¹ * (R * (W⁻¹ * R * W)))⁻¹ := by group
        _ = k := hconj
    have h5 : R * (R⁻¹ * k * R) = k * R := by group
    rw [hk3] at h5
    exact h5
  have hcentV : (∀ k ∈ D₁, R * k = k * R) → False := by
    intro h1
    have h2 := hcentD₁D₂ h1
    apply hr1
    refine phi_eq_one_of_centralizes hLV φ hφ hker hnc r (fun v hv => ?_)
    obtain ⟨k, hk, q, hq, rfl⟩ := hVD v hv
    calc (r : G) * (k * q) = (r : G) * k * q := by group
      _ = k * (r : G) * q := by rw [h1 k hk]
      _ = k * ((r : G) * q) := by group
      _ = k * (q * (r : G)) := by rw [h2 q hq]
      _ = k * q * (r : G) := by group
  have hfix₁ : D₁ ⊓ Subgroup.centralizer ({R} : Set G) = C₀ :=
    (hcount D₁ hD₁V hC₀D₁ hD₁ hD₁r).resolve_right hcentV
  have hfix₂ : D₂ ⊓ Subgroup.centralizer ({R} : Set G) = C₀ :=
    (hcount D₂ hD₂V hC₀D₂ hD₂ hD₂r).resolve_right (fun h => hcentV (hcentD₂D₁ h))
  intro v hv hRv
  obtain ⟨k, hk, q, hq, hvkq⟩ := hVD v hv
  have ha : R * k * R⁻¹ ∈ D₁ := hD₁r k hk
  have hb : R * q * R⁻¹ ∈ D₂ := hD₂r q hq
  have hab : (R * k * R⁻¹) * (R * q * R⁻¹) = k * q := by
    calc (R * k * R⁻¹) * (R * q * R⁻¹) = R * (k * q) * R⁻¹ := by group
      _ = R * v * R⁻¹ := by rw [hvkq]
      _ = v := by rw [hRv]; group
      _ = k * q := hvkq
  set u : G := k⁻¹ * (R * k * R⁻¹) with hu
  have huD₁ : u ∈ D₁ := D₁.mul_mem (D₁.inv_mem hk) ha
  have huq : u = q * (R * q * R⁻¹)⁻¹ := by
    have h6 : k⁻¹ * ((R * k * R⁻¹) * (R * q * R⁻¹)) = q := by rw [hab]; group
    calc u = k⁻¹ * ((R * k * R⁻¹) * (R * q * R⁻¹)) * (R * q * R⁻¹)⁻¹ := by rw [hu]; group
      _ = q * (R * q * R⁻¹)⁻¹ := by rw [h6]
  have huD₂ : u ∈ D₂ := by rw [huq]; exact D₂.mul_mem hq (D₂.inv_mem hb)
  have huC₀ : u ∈ C₀ := by rw [← hD12]; exact ⟨huD₁, huD₂⟩
  have hu2 : u * u = 1 := hV2 u (hD₁V huD₁)
  have huR : R * u = u * R := Subgroup.mem_centralizer_iff.mp huC₀.2 R r.2
  have hk1 : R * k * R⁻¹ = k * u := by rw [hu]; group
  have hRRR : R * R * R = 1 := by
    have := hRR3
    simpa [pow_succ] using this
  have e1 : R⁻¹ = R * R := by
    calc R⁻¹ = R⁻¹ * (R * R * R) := by rw [hRRR]; group
      _ = R * R := by group
  have hk2 : R⁻¹ * k * R = k := by
    have h7 : R * (R * k * R⁻¹) * R⁻¹ = k := by
      rw [hk1]
      calc R * (k * u) * R⁻¹ = (R * k * R⁻¹) * (R * u * R⁻¹) := by group
        _ = (k * u) * u := by
            rw [hk1, huR]; group
        _ = k := by rw [mul_assoc, hu2, mul_one]
    have h8 : R * (R * k * R⁻¹) * R⁻¹ = (R * R) * k * (R * R)⁻¹ := by group
    rw [h8, ← e1] at h7
    simpa using h7
  have hRk : R * k = k * R := by
    have h5 : R * (R⁻¹ * k * R) = k * R := by group
    rw [hk2] at h5
    exact h5
  have hu1 : u = 1 := by
    rw [hu]
    have : R * k * R⁻¹ = k := by
      calc R * k * R⁻¹ = (k * R) * R⁻¹ := by rw [hRk]
        _ = k := by group
    rw [this]; group
  have hRq : R * q = q * R := by
    have h9 : R * q * R⁻¹ = q := by
      rw [hu1] at huq
      have := huq.symm
      have h10 : q * (R * q * R⁻¹)⁻¹ = 1 := this
      have h11 : q = R * q * R⁻¹ := by
        have := mul_inv_eq_one.mp h10
        exact this
      exact h11.symm
    calc R * q = (R * q * R⁻¹) * R := by group
      _ = q * R := by rw [h9]
  have hkC : k ∈ C₀ := by
    rw [← hfix₁]
    exact ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr hRk.symm⟩
  have hqC : q ∈ C₀ := by
    rw [← hfix₂]
    exact ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr hRq.symm⟩
  rw [hvkq]
  exact (C₀.mul_mem hkC hqC).2

end FixThree

end CFSG.Quasithin.Kleidman.F204
