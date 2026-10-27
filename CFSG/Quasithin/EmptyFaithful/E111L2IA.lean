module

public import CFSG.Quasithin.EmptyFaithful.E111L2B
public import CFSG.Quasithin.EmptyFaithful.E111RMain

public section

namespace CFSG.Quasithin.E2.E22N.E111L.KMI

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R DihedralGroup

open CFSG.Quasithin.E22L2 in
theorem partner_unique {H : Type*} [Group H] {T : Subgroup H} {m : ℕ} (hm : 2 ≤ m)
    (e : ↥T ≃* DihedralGroup (2 ^ m)) {V W₁ W₂ : Subgroup H} (hVT : V ≤ T)
    (hV : IsKleinFour ↥V) (hW₁T : W₁ ≤ T) (hW₁ : IsKleinFour ↥W₁) (hW₂T : W₂ ≤ T)
    (hW₂ : IsKleinFour ↥W₂) (hne₁ : W₁ ≠ V) (hne₂ : W₂ ≠ V)
    (hN₁ : W₁ ≤ Subgroup.normalizer (V : Set H)) (hN₂ : W₂ ≤ Subgroup.normalizer (V : Set H)) :
    W₁ = W₂ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨ι, hι, hιT⟩ := e22pd1_exists_embedding e
  obtain ⟨V₀, rfl⟩ := e22pd1_exists_map_eq (hιT ▸ hVT)
  obtain ⟨U₁, rfl⟩ := e22pd1_exists_map_eq (hιT ▸ hW₁T)
  obtain ⟨U₂, rfl⟩ := e22pd1_exists_map_eq (hιT ▸ hW₂T)
  obtain ⟨j, rfl⟩ := e22pd1_exists_kf_eq_of_isKleinFour (e22pd1_isKleinFour_of_map ι hι hV)
  obtain ⟨i₁, rfl⟩ := e22pd1_exists_kf_eq_of_isKleinFour (e22pd1_isKleinFour_of_map ι hι hW₁)
  obtain ⟨i₂, rfl⟩ := e22pd1_exists_kf_eq_of_isKleinFour (e22pd1_isKleinFour_of_map ι hι hW₂)
  have key : ∀ i, (e22pd1_kf k i).map ι ≠ (e22pd1_kf k j).map ι →
      (e22pd1_kf k i).map ι ≤
        Subgroup.normalizer (((e22pd1_kf k j).map ι : Subgroup H) : Set H) →
      2 * (i - j) = 2 ^ (k + 1) := by
    intro i hne hN
    have hsr : sr i ∈ e22pd1_kf k i := e22pd1_mem_kf.mpr (Or.inr (Or.inr (Or.inl rfl)))
    have h1 : ι (sr i) ∈
        ι.range ⊓ Subgroup.normalizer (((e22pd1_kf k j).map ι : Subgroup H) : Set H) :=
      ⟨⟨sr i, rfl⟩, hN (Subgroup.mem_map_of_mem ι hsr)⟩
    rw [e22pd1_range_inf_normalizer_map ι hι] at h1
    have h2 : sr i ∈ Subgroup.normalizer (e22pd1_kf k j : Set (DihedralGroup (2 ^ (k + 2)))) := by
      obtain ⟨y, hy, hyi⟩ := h1
      rwa [← hι hyi]
    rcases e22pd1_ref_mem_normalizer_iff.mp h2 with h | h
    · exfalso
      apply hne
      rcases (e22pd1_two_mul_eq_zero_iff k _).mp h with h' | h'
      · obtain rfl : i = j := by linear_combination h'
        rfl
      · obtain rfl : i = j + 2 ^ (k + 1) := by linear_combination h'
        rw [e22pd1_kf_add_h]
    · exact h
  have h3 : 2 * (i₁ - i₂) = 0 := by
    linear_combination key i₁ hne₁ hN₁ - key i₂ hne₂ hN₂
  rcases (e22pd1_two_mul_eq_zero_iff k _).mp h3 with h' | h'
  · obtain rfl : i₁ = i₂ := by linear_combination h'
    rfl
  · obtain rfl : i₁ = i₂ + 2 ^ (k + 1) := by linear_combination h'
    rw [e22pd1_kf_add_h]

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_centralizer (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) s).mp hs
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * s := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun h => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ h
  simpa [mul_assoc] using this

@[expose] def innerImage (A S : Subgroup G) : Subgroup G :=
  S ⊓ ((A ⊓ Subgroup.normalizer (S : Set G)) ⊔ Subgroup.centralizer (S : Set G))

theorem innerImage_le_left (A S : Subgroup G) : innerImage A S ≤ S := inf_le_left

theorem mem_innerImage_of {A S : Subgroup G} {v s : G}
    (hv : v ∈ A ⊓ Subgroup.normalizer (S : Set G)) (hs : s ∈ S)
    (hsv : s⁻¹ * v ∈ Subgroup.centralizer (S : Set G)) : s ∈ innerImage A S := by
  refine ⟨hs, ?_⟩
  have : s = v * (s⁻¹ * v)⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv)
    (Subgroup.mem_sup_right (Subgroup.inv_mem _ hsv))

theorem exists_of_mem_innerImage {A S : Subgroup G} {s : G} (hs : s ∈ innerImage A S) :
    ∃ v ∈ A ⊓ Subgroup.normalizer (S : Set G), s⁻¹ * v ∈ Subgroup.centralizer (S : Set G) := by
  have hN : A ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) :=
    inf_le_right.trans (normalizer_le_normalizer_centralizer S)
  obtain ⟨c, hc, v, hv, rfl⟩ := exists_mul_of_mem_sup hN (by rw [sup_comm]; exact hs.2)
  refine ⟨v, hv, ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hN hv)) _).mp
    (Subgroup.inv_mem _ hc)
  simpa [mul_assoc] using this

theorem sup_innerImage {A S : Subgroup G}
    (hinn : ∀ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S,
      s⁻¹ * a ∈ Subgroup.centralizer (S : Set G)) :
    (A ⊓ Subgroup.normalizer (S : Set G)) ⊔ Subgroup.centralizer (S : Set G) =
      innerImage A S ⊔ Subgroup.centralizer (S : Set G) := by
  refine le_antisymm (sup_le (fun v hv => ?_) le_sup_right) (sup_le inf_le_right le_sup_right)
  obtain ⟨s, hs, hsv⟩ := hinn v hv
  have : v = s * (s⁻¹ * v) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_innerImage_of hv hs hsv))
    (Subgroup.mem_sup_right hsv)

theorem eq_one_of_mem_centralizer {X S : Subgroup G} (hS : IsComp X S) {x : G} (hx : x ∈ S)
    (hxc : x ∈ Subgroup.centralizer (S : Set G)) : x = 1 := by
  have := hS.simple
  have hZ := Vol2.Ch11.SecE3.center_eq_bot_of_simple hS.nonabelian
  have hc : (⟨x, hx⟩ : ↥S) ∈ Subgroup.center ↥S :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc y y.2)
  rw [hZ, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val hc

theorem conj_eq_of_mem_innerImage {S : Subgroup G} {s v : G}
    (hsv : s⁻¹ * v ∈ Subgroup.centralizer (S : Set G)) {x : G} (hx : x ∈ S) :
    s * x * s⁻¹ = v * x * v⁻¹ := by
  have h1 := Subgroup.mem_centralizer_iff.mp hsv x hx
  calc s * x * s⁻¹ = s * (x * (s⁻¹ * v)) * v⁻¹ := by group
    _ = s * ((s⁻¹ * v) * x) * v⁻¹ := by rw [h1]
    _ = v * x * v⁻¹ := by group

theorem mul_self_of_mem_innerImage {X A S : Subgroup G} (hS : IsComp X S)
    (hA : IsElemAbelian 2 A) {s : G} (hs : s ∈ innerImage A S) : s * s = 1 := by
  obtain ⟨v, hv, hsv⟩ := exists_of_mem_innerImage hs
  have hv2 : v * v = 1 := by
    have := hA.2 v hv.1
    rwa [pow_two] at this
  apply eq_one_of_mem_centralizer hS (S.mul_mem hs.1 hs.1)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hvx : v * x * v⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hv.2 x).mp hx
  have e1 : s * s * x * (s * s)⁻¹ = x := by
    calc s * s * x * (s * s)⁻¹ = s * (s * x * s⁻¹) * s⁻¹ := by group
      _ = s * (v * x * v⁻¹) * s⁻¹ := by rw [conj_eq_of_mem_innerImage hsv hx]
      _ = v * (v * x * v⁻¹) * v⁻¹ := conj_eq_of_mem_innerImage hsv hvx
      _ = (v * v) * x * (v * v)⁻¹ := by group
      _ = x := by rw [hv2]; group
  calc x * (s * s) = (s * s * x * (s * s)⁻¹) * (s * s) := by rw [e1]
    _ = s * s * x := by group

theorem innerImage_le [Finite G] {X T A S : Subgroup G} (hR : E111Reduced G X T)
    (hS : IsComp X S) (hAT : A ≤ T) (hA : IsElemAbelian 2 A) : innerImage A S ≤ T ⊓ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro s hs
  obtain ⟨v, hv, hsv⟩ := exists_of_mem_innerImage hs
  have hsS : s ∈ S := hs.1
  have hvT : v ∈ T := hAT hv.1
  have hss := mul_self_of_mem_innerImage hS hA hs
  have hsN : Subgroup.zpowers s ≤ Subgroup.normalizer ((T ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyT, hyS⟩
      rw [conj_eq_of_mem_innerImage hsv hyS]
      exact ⟨T.mul_mem (T.mul_mem hvT hyT) (T.inv_mem hvT),
        (Subgroup.mem_normalizer_iff.mp hv.2 y).mp hyS⟩
    · rintro ⟨h1, h2⟩
      have hyS : y ∈ S := by
        have := S.mul_mem (S.mul_mem (S.inv_mem hsS) h2) hsS
        simpa [mul_assoc] using this
      rw [conj_eq_of_mem_innerImage hsv hyS] at h1
      refine ⟨?_, hyS⟩
      have := T.mul_mem (T.mul_mem (T.inv_mem hvT) h1) hvT
      simpa [mul_assoc] using this
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers s) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨1, Subtype.ext ?_⟩
    have h2 : s ^ 2 = 1 := by rw [pow_two, hss]
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  have hTS := isSylowIn_inf hR hS
  have hQ := IsPGroup.to_sup_of_normal_left' hTS.isPGroup hz2 hsN
  have hQS : T ⊓ S ⊔ Subgroup.zpowers s ≤ S :=
    sup_le inf_le_right (Subgroup.zpowers_le.mpr hsS)
  have heq := eq_of_le_of_isPGroup hTS le_sup_left hQS hQ
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)

end CFSG.Quasithin.E2.E22N.E111L.KMI
