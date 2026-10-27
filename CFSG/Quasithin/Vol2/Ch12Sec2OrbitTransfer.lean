module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import CFSG.Quasithin.Background.HMathieuStatements

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu

variable {V : Type*} [CommGroup V] {D : FFModel} {H : Subgroup (MulAut V)}
  {π : D.Gam →* ↥H} {β : ↥(⊤ : Subgroup V) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec}

abbrev coordOf (β : ↥(⊤ : Subgroup V) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec) (v : V) :
    ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
  β ⟨v, Subgroup.mem_top v⟩

theorem coordOf_injective (hR : RealizesBy D H ⊤ ⊥ π β) : Function.Injective (coordOf β) := by
  intro v w h
  have h1 : β ((⟨v, Subgroup.mem_top v⟩ : ↥(⊤ : Subgroup V))⁻¹ * ⟨w, Subgroup.mem_top w⟩) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact h
  have h2 := (hR.2.2.2.2.2.2.2.2.1 _).1 h1
  rw [Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.1 h2

theorem coordOf_surjective (hR : RealizesBy D H ⊤ ⊥ π β) : Function.Surjective (coordOf β) := by
  intro q
  obtain ⟨u, rfl⟩ := hR.2.2.2.2.2.2.2.1 q
  exact ⟨u, rfl⟩

theorem coordOf_mul (v w : V) : coordOf β (v * w) = coordOf β v * coordOf β w := by
  rw [coordOf, coordOf, coordOf, ← map_mul]
  rfl

theorem coordOf_one : coordOf β 1 = 1 := map_one β

theorem coordOf_act (hR : RealizesBy D H ⊤ ⊥ π β) (γ : D.Gam) (v : V) (m : ↥D.sec)
    (hv : coordOf β v = QuotientGroup.mk m) :
    coordOf β (((π γ : ↥H) : MulAut V) v) =
      QuotientGroup.mk ⟨D.act γ m, hR.2.2.2.2.2.1 γ m m.2⟩ :=
  hR.2.2.2.2.2.2.2.2.2 γ ⟨v, Subgroup.mem_top v⟩ m (Subgroup.mem_top _) _ hv

theorem classFn_eq_of_mk_eq {I : Type*} (f : D.Amb → I)
    (hker : ∀ m ∈ D.sec, ∀ k ∈ D.ker, f (m * k) = f m) {a b : ↥D.sec}
    (h : (QuotientGroup.mk a : ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk b) :
    f b = f a := by
  have hk : ((a⁻¹ * b : ↥D.sec) : D.Amb) ∈ D.ker :=
    Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h)
  have := hker a a.2 _ hk
  rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this

section ClassFn

variable {I : Type*} (f : D.Amb → I)

theorem exists_eq_iff_of_classFn (hR : RealizesBy D H ⊤ ⊥ π β)
    (hker : ∀ m ∈ D.sec, ∀ k ∈ D.ker, f (m * k) = f m)
    (hact : ∀ γ : D.Gam, ∀ m ∈ D.sec, f (D.act γ m) = f m)
    (htrans : ∀ m ∈ D.sec, ∀ m' ∈ D.sec, f m = f m' →
      ∃ γ : D.Gam, ∃ k ∈ D.ker, D.act γ m = m' * k)
    {v w : V} {m m' : ↥D.sec} (hv : coordOf β v = QuotientGroup.mk m)
    (hw : coordOf β w = QuotientGroup.mk m') :
    (∃ h ∈ H, (h : MulAut V) v = w) ↔ f m = f m' := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨γ, hγ⟩ := hR.1 ⟨h, hh⟩
    have e : coordOf β (h v) = QuotientGroup.mk ⟨D.act γ m, hR.2.2.2.2.2.1 γ m m.2⟩ := by
      rw [← coordOf_act hR γ v m hv, hγ]
    rw [hw] at e
    rw [← hact γ m m.2]
    exact classFn_eq_of_mk_eq f hker e
  · intro hf
    obtain ⟨γ, k, hk, he⟩ := htrans m m.2 m' m'.2 hf
    refine ⟨π γ, (π γ).2, coordOf_injective hR ?_⟩
    rw [coordOf_act hR γ v m hv, hw]
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    change (D.act γ m)⁻¹ * (m' : D.Amb) ∈ D.ker
    rw [he, mul_inv_rev, inv_mul_cancel_right]
    exact D.ker.inv_mem hk

theorem card_orbitIn_of_classFn (hR : RealizesBy D H ⊤ ⊥ π β)
    (hker : ∀ m ∈ D.sec, ∀ k ∈ D.ker, f (m * k) = f m)
    (hact : ∀ γ : D.Gam, ∀ m ∈ D.sec, f (D.act γ m) = f m)
    (htrans : ∀ m ∈ D.sec, ∀ m' ∈ D.sec, f m = f m' →
      ∃ γ : D.Gam, ∃ k ∈ D.ker, D.act γ m = m' * k)
    {v : V} {m : ↥D.sec} (hv : coordOf β v = QuotientGroup.mk m) :
    Nat.card ↥D.ker * Nat.card (orbitIn H v) = Nat.card {m' : ↥D.sec // f m' = f m} := by
  set t : Set (↥D.sec ⧸ D.ker.subgroupOf D.sec) :=
    {q | ∃ m' : ↥D.sec, QuotientGroup.mk m' = q ∧ f m' = f m} with ht
  have h1 : orbitIn H v = coordOf β ⁻¹' t := by
    ext w
    obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective (coordOf β w)
    change (∃ h ∈ H, (h : MulAut V) v = w) ↔ coordOf β w ∈ t
    rw [exists_eq_iff_of_classFn f hR hker hact htrans hv hm'.symm]
    constructor
    · intro h
      exact ⟨m', hm', h.symm⟩
    · rintro ⟨m'', h1, h2⟩
      rw [← h2]
      exact (classFn_eq_of_mk_eq f hker (h1.trans hm'.symm)).symm
  have h2 : Nat.card ↥(coordOf β ⁻¹' t) = Nat.card t :=
    Nat.card_congr ((Equiv.ofBijective _
      ⟨coordOf_injective hR, coordOf_surjective hR⟩).subtypeEquiv fun _ => Iff.rfl)
  have h3 : Nat.card ↥(QuotientGroup.mk ⁻¹' t : Set ↥D.sec) =
      Nat.card ↥(D.ker.subgroupOf D.sec) * Nat.card t := by
    rw [Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet _ t), Nat.card_prod]
  have h4 : Nat.card ↥(D.ker.subgroupOf D.sec) = Nat.card ↥D.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR.2.2.1).toEquiv
  have h5 : Nat.card ↥(QuotientGroup.mk ⁻¹' t : Set ↥D.sec) =
      Nat.card {m' : ↥D.sec // f m' = f m} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro m'
    change (∃ m'' : ↥D.sec, QuotientGroup.mk m'' = QuotientGroup.mk m' ∧ f m'' = f m) ↔ _
    constructor
    · rintro ⟨m'', h1, h2⟩
      rw [← h2]
      exact classFn_eq_of_mk_eq f hker h1
    · intro h
      exact ⟨m', rfl, h⟩
  rw [h1, h2, ← h4, ← h3, h5]

end ClassFn

theorem exists_coordOf_eq (hR : RealizesBy D H ⊤ ⊥ π β) {v : V} (hv : v ≠ 1) :
    ∃ m : ↥D.sec, coordOf β v = QuotientGroup.mk m ∧ (m : D.Amb) ∉ D.ker := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (coordOf β v)
  refine ⟨m, hm.symm, fun hk => hv (coordOf_injective hR ?_)⟩
  rw [← hm, coordOf_one, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.2 hk

theorem orbits_of_classFn (hR : RealizesBy D H ⊤ ⊥ π β) (f : D.Amb → ℕ)
    (hker : ∀ m ∈ D.sec, ∀ k ∈ D.ker, f (m * k) = f m)
    (hact : ∀ γ : D.Gam, ∀ m ∈ D.sec, f (D.act γ m) = f m)
    (htrans : ∀ m ∈ D.sec, ∀ m' ∈ D.sec, f m = f m' →
      ∃ γ : D.Gam, ∃ k ∈ D.ker, D.act γ m = m' * k)
    (S : Finset ℕ) (N : ℕ → ℕ) (ℓ : List ℕ) (hk0 : Nat.card ↥D.ker ≠ 0)
    (hS : ∀ m : ↥D.sec, (m : D.Amb) ∉ D.ker → f m ∈ S)
    (hN : ∀ m : ↥D.sec, Nat.card {m' : ↥D.sec // f m' = f m} = N (f m))
    (hℓ : ∀ c ∈ S, ∃ l ∈ ℓ, Nat.card ↥D.ker * l = N c)
    (hinj : ∀ c ∈ S, ∀ c' ∈ S, N c = N c' → c = c') :
    OrbitLengthsIn H ℓ ∧ OrbitsSeparated H := by
  refine ⟨fun v hv => ?_, fun v w hv hw hvw => ?_⟩
  · obtain ⟨m, hm, hmk⟩ := exists_coordOf_eq hR hv
    obtain ⟨l, hl, hlN⟩ := hℓ _ (hS m hmk)
    have hc := card_orbitIn_of_classFn f hR hker hact htrans hm
    rw [hN, ← hlN] at hc
    rwa [Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0) hc]
  · obtain ⟨m, hm, hmk⟩ := exists_coordOf_eq hR hv
    obtain ⟨m', hm', hmk'⟩ := exists_coordOf_eq hR hw
    rw [exists_eq_iff_of_classFn f hR hker hact htrans hm hm']
    apply hinj _ (hS m hmk) _ (hS m' hmk')
    rw [← hN m, ← hN m', ← card_orbitIn_of_classFn f hR hker hact htrans hm,
      ← card_orbitIn_of_classFn f hR hker hact htrans hm', hvw]

theorem orbitsMod_of_classFn (hR : RealizesBy D H ⊤ ⊥ π β) (f : D.Amb → ℕ)
    (hker : ∀ m ∈ D.sec, ∀ k ∈ D.ker, f (m * k) = f m)
    (hact : ∀ γ : D.Gam, ∀ m ∈ D.sec, f (D.act γ m) = f m)
    (htrans : ∀ m ∈ D.sec, ∀ m' ∈ D.sec, f m = f m' →
      ∃ γ : D.Gam, ∃ k ∈ D.ker, D.act γ m = m' * k)
    {z : V} (z₀ : ↥D.sec) (hz : coordOf β z = QuotientGroup.mk z₀)
    (S : Finset ℕ) (N : ℕ → ℕ) (ℓ : List ℕ) (hk0 : Nat.card ↥D.ker ≠ 0)
    (hS : ∀ m : ↥D.sec, (m : D.Amb) ∉ D.ker → ((m⁻¹ * z₀ : ↥D.sec) : D.Amb) ∉ D.ker → f m ∈ S)
    (hN : ∀ m : ↥D.sec, Nat.card {m' : ↥D.sec // f m' = f m} = N (f m))
    (hℓ : ∀ c ∈ S, ∃ l ∈ ℓ, Nat.card ↥D.ker * l = N c)
    (hsep : ∀ m m' : ↥D.sec, f m ∈ S → f m' ∈ S → N (f m) = N (f m') →
      f m = f m' ∨ f m = f (m' * z₀ : ↥D.sec)) :
    OrbitLengthsInMod H z ℓ ∧ OrbitsSeparatedMod H z := by
  have key : ∀ v : V, v ≠ 1 → v ≠ z → ∃ m : ↥D.sec, coordOf β v = QuotientGroup.mk m ∧
      f m ∈ S := by
    intro v hv hvz
    obtain ⟨m, hm, hmk⟩ := exists_coordOf_eq hR hv
    refine ⟨m, hm, hS m hmk fun hk => hvz (coordOf_injective hR ?_)⟩
    rw [hm, hz]
    exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hk)
  refine ⟨fun v hv hvz => ?_, fun v w hv hw hvz hwz hvw => ?_⟩
  · obtain ⟨m, hm, hmS⟩ := key v hv hvz
    obtain ⟨l, hl, hlN⟩ := hℓ _ hmS
    have hc := card_orbitIn_of_classFn f hR hker hact htrans hm
    rw [hN, ← hlN] at hc
    rwa [Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0) hc]
  · obtain ⟨m, hm, hmS⟩ := key v hv hvz
    obtain ⟨m', hm', hmS'⟩ := key w hw hwz
    have hNN : N (f m) = N (f m') := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0)
      rw [← hN m, ← hN m', ← card_orbitIn_of_classFn f hR hker hact htrans hm,
        ← card_orbitIn_of_classFn f hR hker hact htrans hm', hvw]
    have hwz' : coordOf β (w * z) = QuotientGroup.mk (m' * z₀) := by
      rw [coordOf_mul, hm', hz, QuotientGroup.mk_mul]
    rcases hsep m m' hmS hmS' hNN with h | h
    · obtain ⟨g, hg, hgv⟩ := (exists_eq_iff_of_classFn f hR hker hact htrans hm hm').2 h
      exact ⟨g, hg, Or.inl hgv⟩
    · obtain ⟨g, hg, hgv⟩ := (exists_eq_iff_of_classFn f hR hker hact htrans hm hwz').2 h
      exact ⟨g, hg, Or.inr hgv⟩

end CFSG.Quasithin.H13.Orbit
