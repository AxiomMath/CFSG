module

public import CFSG.Quasithin.Vol2.KGFactC31NoM22FusMain

public section

namespace CFSG.Quasithin.KGC31

@[expose] def SylowAutBoundAll (ℓ m : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ P : Sylow ℓ G, (∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x) ∧
    ∀ u ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
      u ^ m ∈ Subgroup.centralizer ((P : Subgroup G) : Set G)

theorem sylow_mem_smul_iff {ℓ : ℕ} {G : Type*} [Group G] {g x : G} {P : Sylow ℓ G} :
    x ∈ ((g • P : Sylow ℓ G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem sylow_exists_smul_eq_of_le {ℓ : ℕ} [Fact ℓ.Prime] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {P Q : Sylow ℓ G} (hP : (P : Subgroup G) ≤ H) (hQ : (Q : Subgroup G) ≤ H) :
    ∃ c ∈ H, c • P = Q := by
  haveI : Finite (Sylow ℓ G) := Sylow.finite_of_finiteIndex P
  haveI : Finite (Sylow ℓ H) := Sylow.instFiniteSubtypeMemSubgroup H
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥H) (P.subtype hP) (Q.subtype hQ)
  refine ⟨(c : G), c.2, ?_⟩
  have hcP : ((c : G) • P : Sylow ℓ G) ≤ H := Sylow.smul_le hP c
  have h1 : (c : H) • P.subtype hP = ((c : G) • P).subtype hcP := Sylow.smul_subtype hP c
  have h2 : ((c : G) • P).subtype hcP = Q.subtype hQ := by
    rw [← h1]
    exact hc
  have h3 := congrArg (fun S : Sylow ℓ H => (S : Subgroup H).map H.subtype) h2
  simp only [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype] at h3
  rw [inf_eq_left.2 hcP, inf_eq_left.2 hQ] at h3
  exact Sylow.ext h3

theorem SylowAutBoundAll.of_sylow {ℓ m : ℕ} [Fact ℓ.Prime] {G : Type*} [Group G] [Finite G]
    (P : Sylow ℓ G) (hab : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x)
    (hN : ∀ u ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
      u ^ m ∈ Subgroup.centralizer ((P : Subgroup G) : Set G)) :
    SylowAutBoundAll ℓ m G := by
  haveI : Finite (Sylow ℓ G) := Sylow.finite_of_finiteIndex P
  intro Q
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨fun x hx y hy => ?_, fun u hu => ?_⟩
  · have hx' := sylow_mem_smul_iff.1 hx
    have hy' := sylow_mem_smul_iff.1 hy
    have hc := hab _ hx' _ hy'
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = y * x := by group
  · set w : G := g⁻¹ * u * g with hw
    have hu' : ∀ z : G, z ∈ ((g • P : Sylow ℓ G) : Subgroup G) ↔
        u * z * u⁻¹ ∈ ((g • P : Sylow ℓ G) : Subgroup G) :=
      fun z => Subgroup.mem_set_normalizer_iff.1 hu z
    have e1 : ∀ t : G, t ∈ (P : Subgroup G) ↔
        g * t * g⁻¹ ∈ ((g • P : Sylow ℓ G) : Subgroup G) := by
      intro t
      rw [sylow_mem_smul_iff]
      have : g⁻¹ * (g * t * g⁻¹) * g = t := by group
      rw [this]
    have hwN : w ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro z
      have e2 : u * (g * z * g⁻¹) * u⁻¹ = g * (w * z * w⁻¹) * g⁻¹ := by
        rw [hw]
        group
      simp only [SetLike.mem_coe]
      rw [e1 z, e1 (w * z * w⁻¹), hu' (g * z * g⁻¹), e2]
    have hwm : w ^ m ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := hN w hwN
    have hu_eq : g * w * g⁻¹ = u := by
      rw [hw]
      group
    have hum : u ^ m = g * w ^ m * g⁻¹ := by
      rw [← hu_eq, conj_pow]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' := sylow_mem_smul_iff.1 hx
    have hc := Subgroup.mem_centralizer_iff.1 hwm _ hx'
    rw [hum]
    calc x * (g * w ^ m * g⁻¹) = g * ((g⁻¹ * x * g) * w ^ m) * g⁻¹ := by group
      _ = g * (w ^ m * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = (g * w ^ m * g⁻¹) * x := by group

theorem sylowAutBound_iff_all {ℓ m : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] [Finite G] :
    SylowAutBound ℓ m G ↔ SylowAutBoundAll ℓ m G := by
  constructor
  · rintro ⟨P, hab, hN⟩
    exact SylowAutBoundAll.of_sylow P hab hN
  · intro h
    obtain ⟨P⟩ : Nonempty (Sylow ℓ G) := inferInstance
    exact ⟨P, h P⟩

theorem centralizer_le_normalizer_of_set {G : Type*} [Group G] (S : Set G) :
    Subgroup.centralizer S ≤ Subgroup.normalizer S := by
  intro c hc
  rw [Subgroup.mem_set_normalizer_iff]
  intro s
  have hc' : c⁻¹ ∈ Subgroup.centralizer S := inv_mem hc
  constructor
  · intro hs
    have h1 := Subgroup.mem_centralizer_iff.1 hc s hs
    have e : c * s * c⁻¹ = s := by
      rw [← h1]
      group
    rw [e]
    exact hs
  · intro hs
    have h2 := Subgroup.mem_centralizer_iff.1 hc' _ hs
    have e : c * s * c⁻¹ = s := by
      calc c * s * c⁻¹ = c * s * c⁻¹ * c⁻¹ * c := by group
        _ = c⁻¹ * (c * s * c⁻¹) * c := by rw [h2]
        _ = s := by group
    rw [← e]
    exact hs

theorem mul_pow_mem_centralizer {G : Type*} [Group G] {R : Subgroup G} {c v : G} {m : ℕ}
    (hc : c ∈ Subgroup.centralizer (R : Set G)) (hv : v ∈ Subgroup.normalizer (R : Set G))
    (h : v ^ m ∈ Subgroup.centralizer (R : Set G)) :
    (c * v) ^ m ∈ Subgroup.centralizer (R : Set G) := by
  have key : ∀ k : ℕ, ∀ x ∈ R, (c * v) ^ k * x = (v ^ k * x * (v ^ k)⁻¹) * (c * v) ^ k := by
    intro k
    induction k with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      have hy : v ^ k * x * (v ^ k)⁻¹ ∈ R :=
        (Subgroup.mem_set_normalizer_iff.1 (pow_mem hv k) x).1 hx
      have hy' : v * (v ^ k * x * (v ^ k)⁻¹) * v⁻¹ ∈ R :=
        (Subgroup.mem_set_normalizer_iff.1 hv _).1 hy
      have hcy : (v * (v ^ k * x * (v ^ k)⁻¹) * v⁻¹) * c
          = c * (v * (v ^ k * x * (v ^ k)⁻¹) * v⁻¹) :=
        Subgroup.mem_centralizer_iff.1 hc _ hy'
      calc (c * v) ^ (k + 1) * x = c * v * ((c * v) ^ k * x) := by
            rw [pow_succ', mul_assoc]
        _ = c * v * ((v ^ k * x * (v ^ k)⁻¹) * (c * v) ^ k) := by rw [ih x hx]
        _ = (c * (v * (v ^ k * x * (v ^ k)⁻¹) * v⁻¹)) * v * (c * v) ^ k := by group
        _ = ((v * (v ^ k * x * (v ^ k)⁻¹) * v⁻¹) * c) * v * (c * v) ^ k := by rw [← hcy]
        _ = (v * (v ^ k * x * (v ^ k)⁻¹) * v⁻¹) * (c * v) ^ (k + 1) := by
            rw [pow_succ']
            simp only [mul_assoc]
        _ = (v ^ (k + 1) * x * (v ^ (k + 1))⁻¹) * (c * v) ^ (k + 1) := by
            rw [pow_succ' v k]
            group
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxv : x * v ^ m = v ^ m * x := Subgroup.mem_centralizer_iff.1 h x hx
  have hconj : v ^ m * x * (v ^ m)⁻¹ = x := by
    rw [← hxv]
    group
  have hk := key m x hx
  rw [hconj] at hk
  exact hk.symm

theorem SylowAutBoundAll.of_isPGroup {ℓ m : ℕ} [Fact ℓ.Prime] {G : Type*} [Group G] [Finite G]
    (h : SylowAutBoundAll ℓ m G) {R : Subgroup G} (hR : IsPGroup ℓ R) :
    (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧
      ∀ u ∈ Subgroup.normalizer (R : Set G), u ^ m ∈ Subgroup.centralizer (R : Set G) := by
  obtain ⟨Q, hRQ⟩ := IsPGroup.exists_le_sylow hR
  obtain ⟨hQab, hQN⟩ := h Q
  have hQC : (Q : Subgroup G) ≤ Subgroup.centralizer (R : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact hQab r (hRQ hr) x hx
  refine ⟨fun x hx y hy => hQab x (hRQ hx) y (hRQ hy), fun u hu => ?_⟩
  have hQ'C : ((u • Q : Sylow ℓ G) : Subgroup G) ≤ Subgroup.centralizer (R : Set G) := by
    intro x hx
    have hy := sylow_mem_smul_iff.1 hx
    have hyC := hQC hy
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro r hr
    have hr' : u⁻¹ * r * u ∈ R := by
      have := (Subgroup.mem_set_normalizer_iff.1 (inv_mem hu) r).1 hr
      simpa using this
    have hcomm := hyC _ hr'
    calc r * x = u * ((u⁻¹ * r * u) * (u⁻¹ * x * u)) * u⁻¹ := by group
      _ = u * ((u⁻¹ * x * u) * (u⁻¹ * r * u)) * u⁻¹ := by rw [hcomm]
      _ = x * r := by group
  obtain ⟨c, hcC, hc⟩ := sylow_exists_smul_eq_of_le hQC hQ'C
  have hcN : c ∈ Subgroup.normalizer (R : Set G) := centralizer_le_normalizer_of_set _ hcC
  obtain ⟨v, hv⟩ : ∃ v : G, v = c⁻¹ * u := ⟨_, rfl⟩
  have hvQ_eq : v • Q = Q := by
    rw [hv, mul_smul, ← hc, inv_smul_smul]
  have hvQ : v ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
    Sylow.smul_eq_iff_mem_normalizer.1 hvQ_eq
  have hvC : v ^ m ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.1 (hQN v hvQ) x (hRQ hx)
  have hvR : v ∈ Subgroup.normalizer (R : Set G) := by
    rw [hv]
    exact mul_mem (inv_mem hcN) hu
  have huv : u = c * v := by
    rw [hv]
    group
  rw [huv]
  exact mul_pow_mem_centralizer hcC hvR hvC

theorem map_mem_normalizer_map {G H : Type*} [Group G] [Group H] (f : G →* H) {P : Subgroup G}
    {u : G} (hu : u ∈ Subgroup.normalizer (P : Set G)) :
    f u ∈ Subgroup.normalizer ((P.map f : Subgroup H) : Set H) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hh
    exact Subgroup.mem_map.2
      ⟨u * x * u⁻¹, (Subgroup.mem_set_normalizer_iff.1 hu x).1 hx, by simp⟩
  · intro hh
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hh
    refine Subgroup.mem_map.2 ⟨u⁻¹ * y * u, ?_, ?_⟩
    · have := (Subgroup.mem_set_normalizer_iff.1 (inv_mem hu) y).1 hy
      simpa using this
    · rw [map_mul, map_mul, map_inv, hyeq]
      group

theorem SylowAutBoundAll.of_injective {ℓ m : ℕ} [Fact ℓ.Prime] {G H : Type*} [Group G]
    [Finite G] [Group H] [Finite H] (f : G →* H) (hf : Function.Injective f)
    (h : SylowAutBoundAll ℓ m H) : SylowAutBoundAll ℓ m G := by
  intro P
  obtain ⟨hR1, hR2⟩ := SylowAutBoundAll.of_isPGroup h (IsPGroup.map P.isPGroup' f)
  refine ⟨fun x hx y hy => hf ?_, fun u hu => ?_⟩
  · rw [map_mul, map_mul]
    exact hR1 (f x) (Subgroup.mem_map.2 ⟨x, hx, rfl⟩) (f y) (Subgroup.mem_map.2 ⟨y, hy, rfl⟩)
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply hf
    rw [map_mul, map_mul, map_pow]
    exact Subgroup.mem_centralizer_iff.1 (hR2 (f u) (map_mem_normalizer_map f hu)) (f x)
      (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)

theorem SylowAutBoundAll.of_surjective {ℓ m : ℕ} [Fact ℓ.Prime] {G N : Type*} [Group G]
    [Finite G] [Group N] (f : G →* N) (hf : Function.Surjective f)
    (h : SylowAutBoundAll ℓ m G) : SylowAutBoundAll ℓ m N := by
  haveI : Finite N := Finite.of_surjective f hf
  intro Pb
  obtain ⟨P, hPb⟩ : ∃ P : Sylow ℓ G, (P : Subgroup G).map f = (Pb : Subgroup N) := by
    obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf ℓ Pb
    refine ⟨P, ?_⟩
    have := Sylow.coe_mapSurjective hf P
    rw [hP] at this
    exact this.symm
  obtain ⟨hPab, hPN⟩ := h P
  have hPbab : ∀ x ∈ (Pb : Subgroup N), ∀ y ∈ (Pb : Subgroup N), x * y = y * x := by
    intro x hx y hy
    rw [← hPb] at hx hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_mul, ← map_mul, hPab a ha b hb]
  refine ⟨hPbab, fun ub hub => ?_⟩
  obtain ⟨u, rfl⟩ := hf ub
  have hPY : (P : Subgroup G) ≤ Subgroup.comap f (Pb : Subgroup N) := by
    intro x hx
    rw [Subgroup.mem_comap, ← hPb]
    exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  have huY : ((u • P : Sylow ℓ G) : Subgroup G) ≤ Subgroup.comap f (Pb : Subgroup N) := by
    intro x hx
    have hz := sylow_mem_smul_iff.1 hx
    have hfz : f (u⁻¹ * x * u) ∈ (Pb : Subgroup N) := by
      rw [← hPb]
      exact Subgroup.mem_map.2 ⟨_, hz, rfl⟩
    have hconj := (Subgroup.mem_set_normalizer_iff.1 hub _).1 hfz
    have e : f x = f u * f (u⁻¹ * x * u) * (f u)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [Subgroup.mem_comap, e]
    exact hconj
  obtain ⟨y, hyY, hy⟩ := sylow_exists_smul_eq_of_le hPY huY
  have hv : (y⁻¹ * u) • P = P := by
    rw [mul_smul, ← hy, inv_smul_smul]
  have hvN : y⁻¹ * u ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    Sylow.smul_eq_iff_mem_normalizer.1 hv
  have hvC := hPN _ hvN
  have hfy : f y ∈ (Pb : Subgroup N) := Subgroup.mem_comap.1 hyY
  have hfyC : f y ∈ Subgroup.centralizer ((Pb : Subgroup N) : Set N) :=
    Subgroup.mem_centralizer_iff.2 (fun b hb => hPbab b hb (f y) hfy)
  have hfvN : f (y⁻¹ * u) ∈ Subgroup.normalizer ((Pb : Subgroup N) : Set N) := by
    rw [map_mul, map_inv]
    exact mul_mem (inv_mem (centralizer_le_normalizer_of_set _ hfyC)) hub
  have hfvC : f (y⁻¹ * u) ^ m ∈ Subgroup.centralizer ((Pb : Subgroup N) : Set N) := by
    rw [← map_pow, Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hPb] at hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hb
    have hxv := Subgroup.mem_centralizer_iff.1 hvC x hx
    rw [← map_mul, ← map_mul, hxv]
  have key := mul_pow_mem_centralizer hfyC hfvN hfvC
  have e2 : f y * f (y⁻¹ * u) = f u := by
    rw [← map_mul, mul_inv_cancel_left]
  rw [e2] at key
  exact key

theorem SylowAutBoundAll.mono {ℓ e m : ℕ} {G : Type*} [Group G]
    (h : SylowAutBoundAll ℓ e G) (he : e ∣ m) : SylowAutBoundAll ℓ m G := by
  intro P
  obtain ⟨hab, hN⟩ := h P
  refine ⟨hab, fun u hu => ?_⟩
  obtain ⟨k, rfl⟩ := he
  rw [pow_mul]
  exact pow_mem (hN u hu) k

theorem SylowAutBoundAll.of_abelian_index {ℓ m : ℕ} [Fact ℓ.Prime] {G : Type*} [Group G]
    [Finite G] {D : Subgroup G} (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hidx : ¬ ℓ ∣ D.index)
    (hN : ∀ P : Sylow ℓ G, (P : Subgroup G) ≤ D →
      ∀ u ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
        u ^ m ∈ Subgroup.centralizer ((P : Subgroup G) : Set G)) :
    SylowAutBoundAll ℓ m G := by
  obtain ⟨S⟩ : Nonempty (Sylow ℓ D) := inferInstance
  have hS1 : IsPGroup ℓ ((S : Subgroup D).map D.subtype) :=
    IsPGroup.map (Sylow.isPGroup' S) D.subtype
  have hS2 : ¬ ℓ ∣ ((S : Subgroup D).map D.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro hdvd
    rcases (Nat.Prime.dvd_mul (Fact.out : Nat.Prime ℓ)).1 hdvd with h1 | h2
    · exact Sylow.not_dvd_index S h1
    · exact hidx h2
  have hPcoe : ((hS1.toSylow hS2 : Sylow ℓ G) : Subgroup G) = (S : Subgroup D).map D.subtype :=
    IsPGroup.toSylow_coe hS1 hS2
  have hPD : ((hS1.toSylow hS2 : Sylow ℓ G) : Subgroup G) ≤ D := by
    rw [hPcoe]
    intro y hy
    obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.1 hy
    exact x.2
  have hab : ∀ x ∈ ((hS1.toSylow hS2 : Sylow ℓ G) : Subgroup G),
      ∀ y ∈ ((hS1.toSylow hS2 : Sylow ℓ G) : Subgroup G), x * y = y * x :=
    fun x hx y hy => hD x (hPD hx) y (hPD hy)
  exact SylowAutBoundAll.of_sylow _ hab (hN _ hPD)

end CFSG.Quasithin.KGC31
