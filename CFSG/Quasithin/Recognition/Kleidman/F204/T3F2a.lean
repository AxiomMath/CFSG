module

public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFAll
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIO1Basic

public section

namespace CFSG.Quasithin.Kleidman.F204

open Subgroup

theorem card_mul_le_card_mul_card_inf {G : Type*} [Group G] [Finite G] {V C₁ C₂ : Subgroup G}
    (h1 : C₁ ≤ V) (h2 : C₂ ≤ V) :
    Nat.card C₁ * Nat.card C₂ ≤ Nat.card V * Nat.card (C₁ ⊓ C₂ : Subgroup G) := by
  have e1 : (C₂.relIndex C₁) * Nat.card (C₂ ⊓ C₁ : Subgroup G) = Nat.card C₁ :=
    Subgroup.relIndex_mul_card C₂ C₁
  have e2 : (C₂.relIndex V) * Nat.card (C₂ ⊓ V : Subgroup G) = Nat.card V :=
    Subgroup.relIndex_mul_card C₂ V
  rw [inf_eq_left.mpr h2] at e2
  have hle : C₂.relIndex C₁ ≤ C₂.relIndex V :=
    Subgroup.relIndex_le_of_le_right h1 (by unfold Subgroup.relIndex; exact index_ne_zero_of_finite)
  rw [inf_comm] at e1
  calc Nat.card C₁ * Nat.card C₂
      = (C₂.relIndex C₁ * Nat.card (C₁ ⊓ C₂ : Subgroup G)) * Nat.card C₂ := by rw [e1]
    _ ≤ (C₂.relIndex V * Nat.card (C₁ ⊓ C₂ : Subgroup G)) * Nat.card C₂ :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
    _ = Nat.card V * Nat.card (C₁ ⊓ C₂ : Subgroup G) := by rw [← e2]; ring

theorem sixteen_mul_le_card_of_fix {W : Type*} [Group W] [Finite W] (hW : IsPGroup 2 W)
    (σ : Equiv.Perm W) (hσ5 : σ ^ 5 = 1) (hσ : σ ≠ 1) (C : Subgroup W)
    (hC : ∀ w, w ∈ C ↔ σ w = w) : 16 * Nat.card C ≤ Nat.card W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := W)).mp hW
  have hdvd : Nat.card C ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.card_subgroup_dvd_card C
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hfixeq : Nat.card {x : W // σ x = x} = Nat.card C := by
    apply Nat.card_congr
    exact (Equiv.subtypeEquivRight fun w => (hC w).symm)
  have hcong : 2 ^ n ≡ 2 ^ k [MOD 5] := by
    have h := card_modEq_fix_five σ hσ5
    rw [hfixeq, hk, hn] at h
    exact h
  have hkle : k ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
    (by rw [← hk]; exact hdvd)
  have hkn : k < n := by
    by_contra hle
    have hkn' : k = n := by omega
    have hCtop : C = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hk, hn, hkn']
    apply hσ
    ext w
    have := (hC w).mp (by rw [hCtop]; exact Subgroup.mem_top w)
    simpa using this
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hmod : 2 ^ d % 5 = 1 := by
    have h1 : 2 ^ k * 2 ^ d ≡ 2 ^ k * 1 [MOD 5] := by
      rw [mul_one, ← pow_add]
      exact hcong
    have hcop : Nat.Coprime (2 ^ k) 5 := by
      apply Nat.Coprime.pow_left
      norm_num
    have h2 := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hcop) h1
    exact h2
  have h4 : 4 ∣ d := four_dvd_of_two_pow_mod_five d hmod
  rw [hn, hk]
  have hpow : 2 ^ 4 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by
    obtain ⟨c, rfl⟩ := h4
    omega)
  calc 16 * 2 ^ k = 2 ^ k * 2 ^ 4 := by ring
    _ ≤ 2 ^ k * 2 ^ d := Nat.mul_le_mul_left _ hpow
    _ = 2 ^ (k + d) := by rw [pow_add]

theorem sixteen_mul_le_card_of_five {G : Type*} [Group G] [Finite G] {V : Subgroup G} {x : G}
    (hV2 : ∀ a ∈ V, a * a = 1) (hx : x ∈ Subgroup.normalizer (V : Set G))
    (h5 : ∀ v ∈ V, Commute (x ^ 5) v) (v0 : G) (hv0 : v0 ∈ V) (hnot : ¬ Commute x v0) :
    16 * Nat.card (V ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≤ Nat.card V := by
  have hVp : IsPGroup 2 V := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (by simpa using hV2 g.1 g.2)
  have hconj : ∀ w : V, ((conjPerm hx w : V) : G) = x * (w : G) * x⁻¹ := by
    intro w
    have := conjPerm_pow_apply hx 1 w
    simpa using this
  have hσ1 : conjPerm hx ≠ 1 := by
    intro h
    have h' : ((conjPerm hx ⟨v0, hv0⟩ : V) : G) = v0 := by rw [h]; rfl
    rw [hconj] at h'
    change x * v0 * x⁻¹ = v0 at h'
    apply hnot
    change x * v0 = v0 * x
    calc x * v0 = (x * v0 * x⁻¹) * x := by group
      _ = v0 * x := by rw [h']
  let C : Subgroup V := (Subgroup.centralizer ({x} : Set G)).subgroupOf V
  have hC : ∀ w : V, w ∈ C ↔ conjPerm hx w = w := by
    intro w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subtype.ext_iff, hconj]
    constructor
    · intro h
      rw [h x (Set.mem_singleton x)]
      group
    · intro h y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      calc y * (w : G) = (y * w * y⁻¹) * y := by group
        _ = w * y := by rw [h]
  have := sixteen_mul_le_card_of_fix hVp (conjPerm hx) (conjPerm_five hx h5) hσ1 C hC
  have hcard : Nat.card C = Nat.card (V ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
    have e : C = (V ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf V := by
      rw [Subgroup.inf_subgroupOf_left]
    rw [e]
    exact natCard_subgroupOf' inf_le_left
  rw [hcard] at this
  exact this


theorem sixteen_mul_le_card_V {G : Type*} [Group G] [Finite G] {V L : Subgroup G}
    (hV2 : ∀ a ∈ V, a * a = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    (hnc : ∃ l : L, ∃ v ∈ V, ¬ Commute (l : G) v) :
    16 * Nat.card (V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) ≤ Nat.card V := by
  obtain ⟨x, hx5, -, v0, hv0, hnot⟩ := exists_five_noncentral hLV φ hφ hker hnc
  have h5 : ∀ v ∈ V, Commute ((x : G) ^ 5) v := by
    intro v hv
    have h := (Subgroup.mem_centralizer_iff.mp (hker (x ^ 5) (by rw [map_pow, hx5]))) v hv
    push_cast at h
    exact h.symm
  have h1 := sixteen_mul_le_card_of_five hV2 (hLV x.2) h5 v0 hv0 hnot
  have hle : (V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) ≤
      V ⊓ Subgroup.centralizer ({(x : G)} : Set G) :=
    inf_le_inf_left V (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x.2))
  have h2 := Subgroup.card_le_of_le hle
  omega

theorem fixed_centralizes {G : Type*} [Group G] {V L : Subgroup G}
    (φ : L →* alternatingGroup (Fin 5))
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    {A₁ A₂ : Subgroup L} (hsup : A₁.map φ ⊔ A₂.map φ = ⊤)
    (v : G) (hv : v ∈ V) (h1 : ∀ a ∈ A₁, v * (a : G) = (a : G) * v)
    (h2 : ∀ a ∈ A₂, v * (a : G) = (a : G) * v) : ∀ m : L, v * (m : G) = (m : G) * v := by
  classical
  let S : Subgroup L := (Subgroup.centralizer ({v} : Set G)).comap L.subtype
  have hmemS : ∀ m : L, m ∈ S ↔ v * (m : G) = (m : G) * v := by
    intro m
    show (m : G) ∈ Subgroup.centralizer ({v} : Set G) ↔ _
    rw [Subgroup.mem_centralizer_iff]
    simp
  have hkerS : ∀ k : L, φ k = 1 → k ∈ S := fun k hk =>
    (hmemS k).mpr (Subgroup.mem_centralizer_iff.mp (hker k hk) v hv)
  have hA1 : A₁ ≤ S := fun a ha => (hmemS a).mpr (h1 a ha)
  have hA2 : A₂ ≤ S := fun a ha => (hmemS a).mpr (h2 a ha)
  have htop : S.map φ = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hsup, ← Subgroup.map_sup]
    exact Subgroup.map_mono (sup_le hA1 hA2)
  have hall : ∀ m : L, m ∈ S := fun m =>
    mem_of_map_mem_of_ker S φ hkerS m (by rw [htop]; exact Subgroup.mem_top _)
  exact fun m => (hmemS m).mp (hall m)

theorem card_arith_16 {n c c₁ : ℕ} (hn : n = 4 * c₁) (hsq : c₁ * c₁ ≤ n * c) (h16 : 16 * c ≤ n) :
    n = 16 * c ∧ c₁ = 4 * c := by
  have hc₁ : c₁ ≤ 4 * c := by
    rcases Nat.eq_zero_or_pos c₁ with h0 | hpos
    · omega
    · have : c₁ * c₁ ≤ c₁ * (4 * c) := by
        calc c₁ * c₁ ≤ n * c := hsq
          _ = c₁ * (4 * c) := by rw [hn]; ring
      exact Nat.le_of_mul_le_mul_left this hpos
  omega


theorem fa5_ff_card' {G : Type*} [Group G] [Finite G] {V L : Subgroup G}
    (hV2 : ∀ a ∈ V, a * a = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    {A : Subgroup L} (hA : IsPGroup 2 A)
    (hAnt : ∃ a ∈ A, ∃ v ∈ V, (a : G) * v ≠ v * (a : G))
    (hidx : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V
      ≤ Nat.card (A.map φ)) :
    Nat.card V = 16 * Nat.card (V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) ∧
      Nat.card (A.map φ) = 4 ∧
      Nat.card ((V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G) : Subgroup G))
        = 4 * Nat.card (V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) ∧
      ∃ A₂ : Subgroup L, IsPGroup 2 A₂ ∧ Nat.card (A₂.map φ) = 4 ∧ A₂.map φ ≠ A.map φ ∧
        Nat.card ((V ⊓ Subgroup.centralizer ((A₂.map L.subtype : Subgroup G) : Set G) :
          Subgroup G)) = 4 * Nat.card (V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) ∧
        (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)) ⊓
          (V ⊓ Subgroup.centralizer ((A₂.map L.subtype : Subgroup G) : Set G)) =
          V ⊓ Subgroup.centralizer (L : Set G) := by
  obtain ⟨a, ha, v0, hv0, hne0⟩ := hAnt
  have hnc : ∃ l : L, ∃ v ∈ V, ¬ Commute (l : G) v := ⟨a, v0, hv0, hne0⟩
  have h16 := sixteen_mul_le_card_V hV2 hLV φ hφ hker hnc
  have hK1 : Nat.card (A.map φ) = 4 :=
    card_image_eq_four hV2 hLV φ hφ hker hA ⟨a, ha, v0, hv0, hne0⟩ hidx
  have hr1 : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V = 4 :=
    relIndex_eq_four hV2 hLV φ hφ hker hA ⟨a, ha, v0, hv0, hne0⟩ hidx
  obtain ⟨x, hx⟩ := exists_not_mem_normalizer_of_card_four (A.map φ) hK1
  obtain ⟨g, hg⟩ := hφ x
  have hA₂ : IsPGroup 2 (A.map (MulAut.conj g).toMonoidHom) := hA.map _
  have hmapA₂ : (A.map (MulAut.conj g).toMonoidHom).map φ =
      (A.map φ).map (MulAut.conj x).toMonoidHom := by
    rw [map_map_conj, hg]
  have hinjx : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have hK₂ : Nat.card ((A.map (MulAut.conj g).toMonoidHom).map φ) = 4 := by
    rw [hmapA₂, Subgroup.card_map_of_injective hinjx, hK1]
  have hne : (A.map (MulAut.conj g).toMonoidHom).map φ ≠ A.map φ := by
    rw [hmapA₂]
    exact map_conj_ne _ x hx
  have hgN : (g : G) ∈ Subgroup.normalizer (V : Set G) := hLV g.2
  have hS : ((A.map (MulAut.conj g).toMonoidHom).map L.subtype : Subgroup G) =
      (A.map L.subtype).map (MulAut.conj (g : G)).toMonoidHom := map_subtype_conj A g
  have hcardC : Nat.card ((V ⊓ Subgroup.centralizer
      ((((A.map (MulAut.conj g).toMonoidHom).map L.subtype : Subgroup G)) : Set G) :
        Subgroup G)) =
      Nat.card ((V ⊓ Subgroup.centralizer
      ((A.map L.subtype : Subgroup G) : Set G) : Subgroup G)) := by
    rw [hS]
    exact (card_inf_centralizer_conj hgN _).symm
  have e1 : Nat.card V = 4 * Nat.card ((V ⊓ Subgroup.centralizer
      ((A.map L.subtype : Subgroup G) : Set G) : Subgroup G)) := by
    rw [card_eq_relIndex_mul (V := V)
      (Z := Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)), hr1]
  have hinf : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)) ⊓
      (V ⊓ Subgroup.centralizer
        ((((A.map (MulAut.conj g).toMonoidHom).map L.subtype : Subgroup G)) : Set G)) =
      V ⊓ Subgroup.centralizer (L : Set G) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.mp hv
      obtain ⟨hvV, hvC1⟩ := Subgroup.mem_inf.mp hv1
      obtain ⟨-, hvC2⟩ := Subgroup.mem_inf.mp hv2
      have k1 : ∀ a ∈ A, v * (a : G) = (a : G) * v := fun a ha' =>
        (Subgroup.mem_centralizer_iff.mp hvC1 (a : G)
          (Subgroup.mem_map.mpr ⟨a, ha', rfl⟩)).symm
      have k2 : ∀ a ∈ A.map (MulAut.conj g).toMonoidHom,
          v * (a : G) = (a : G) * v := fun a ha' =>
        (Subgroup.mem_centralizer_iff.mp hvC2 (a : G)
          (Subgroup.mem_map.mpr ⟨a, ha', rfl⟩)).symm
      have hall := fixed_centralizes φ hker
        (klein_sup_eq_top hK1 hK₂ hne.symm) v hvV k1 k2
      refine Subgroup.mem_inf.mpr ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact (hall ⟨h, hh⟩).symm
    · intro v hv
      obtain ⟨hvV, hvL⟩ := Subgroup.mem_inf.mp hv
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hvV, ?_⟩, Subgroup.mem_inf.mpr ⟨hvV, ?_⟩⟩
      · intro h hh
        obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hh
        exact Subgroup.mem_centralizer_iff.mp hvL _ a.2
      · intro h hh
        obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hh
        exact Subgroup.mem_centralizer_iff.mp hvL _ a.2
  have hprod := card_mul_le_card_mul_card_inf
    (inf_le_left : V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G) ≤ V)
    (inf_le_left : V ⊓ Subgroup.centralizer
      ((((A.map (MulAut.conj g).toMonoidHom).map L.subtype : Subgroup G)) : Set G) ≤ V)
  rw [hcardC, hinf] at hprod
  have hn := card_arith_16 e1 hprod h16
  refine ⟨hn.1, hK1, by omega, A.map (MulAut.conj g).toMonoidHom, hA₂, hK₂, hne, ?_, hinf⟩
  rw [hcardC]
  omega


theorem fa5_ff_all' {G : Type*} [Group G] [Finite G] {V L : Subgroup G}
    (hV2 : ∀ a ∈ V, a * a = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    {A : Subgroup L} (hA : IsPGroup 2 A)
    (hAnt : ∃ a ∈ A, ∃ v ∈ V, (a : G) * v ≠ v * (a : G))
    (hidx : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V
      ≤ Nat.card (A.map φ)) :
    Nat.card V = 16 * Nat.card (V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) ∧
      Nat.card (A.map φ) = 4 ∧
      (∀ T : Subgroup L, Nat.card (T.map φ) = 4 →
        Nat.card ((V ⊓ Subgroup.centralizer ((T.map L.subtype : Subgroup G) : Set G) :
          Subgroup G)) = 4 * Nat.card (V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G)) ∧
      (∀ T₁ T₂ : Subgroup L, Nat.card (T₁.map φ) = 4 → Nat.card (T₂.map φ) = 4 →
        T₁.map φ ≠ T₂.map φ →
        (V ⊓ Subgroup.centralizer ((T₁.map L.subtype : Subgroup G) : Set G)) ⊓
          (V ⊓ Subgroup.centralizer ((T₂.map L.subtype : Subgroup G) : Set G)) =
          V ⊓ Subgroup.centralizer (L : Set G)) := by
  obtain ⟨hV16, hK1, hC4, -⟩ := fa5_ff_card' hV2 hLV φ hφ hker hA hAnt hidx
  refine ⟨hV16, hK1, ?_, ?_⟩
  · intro T hT
    obtain ⟨x, hx⟩ := exists_conj_map_eq_alt5 (A.map φ) (T.map φ) hK1 hT
    obtain ⟨g, hg⟩ := hφ x
    have hBφ : (A.map (MulAut.conj g).toMonoidHom).map φ = T.map φ := by
      rw [map_map_conj, hg, hx]
    rw [inf_centralizer_eq_of_map_eq φ hker hBφ.symm,
      card_inf_centralizer_conj_L hLV g, hC4]
  · intro T₁ T₂ h1 h2 hne
    apply le_antisymm
    · intro v hv
      obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.mp hv
      obtain ⟨hvV, hvC1⟩ := Subgroup.mem_inf.mp hv1
      obtain ⟨-, hvC2⟩ := Subgroup.mem_inf.mp hv2
      have k1 : ∀ a ∈ T₁, v * (a : G) = (a : G) * v := fun a ha' =>
        (Subgroup.mem_centralizer_iff.mp hvC1 (a : G)
          (Subgroup.mem_map.mpr ⟨a, ha', rfl⟩)).symm
      have k2 : ∀ a ∈ T₂, v * (a : G) = (a : G) * v := fun a ha' =>
        (Subgroup.mem_centralizer_iff.mp hvC2 (a : G)
          (Subgroup.mem_map.mpr ⟨a, ha', rfl⟩)).symm
      have hall := fixed_centralizes φ hker (klein_sup_eq_top h1 h2 hne) v hvV k1 k2
      refine Subgroup.mem_inf.mpr ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact (hall ⟨h, hh⟩).symm
    · intro v hv
      obtain ⟨hvV, hvL⟩ := Subgroup.mem_inf.mp hv
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hvV, ?_⟩, Subgroup.mem_inf.mpr ⟨hvV, ?_⟩⟩
      · intro h hh
        obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hh
        exact Subgroup.mem_centralizer_iff.mp hvL _ a.2
      · intro h hh
        obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hh
        exact Subgroup.mem_centralizer_iff.mp hvL _ a.2

end CFSG.Quasithin.Kleidman.F204
