module

public import CFSG.Quasithin.SteinbergBSConjugateOrbits
public import CFSG.Quasithin.SteinbergBSResidualCentralizer

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G]

theorem conj_mem_iSup_conjugate {X : Subgroup G} {P : G → Prop} {n : G}
    (hP : ∀ s, P s → P (s * n⁻¹)) {x : G} (hx : x ∈ ⨆ (s : G) (_ : P s), conjugate X s) :
    n * x * n⁻¹ ∈ ⨆ (s : G) (_ : P s), conjugate X s := by
  have hle : (⨆ (s : G) (_ : P s), conjugate X s) ≤
      (⨆ (s : G) (_ : P s), conjugate X s).comap (MulAut.conj n).toMonoidHom := by
    refine iSup₂_le fun s hs y hy => ?_
    show n * y * n⁻¹ ∈ (⨆ (s : G) (_ : P s), conjugate X s : Subgroup G)
    refine le_iSup₂ (f := fun s (_ : P s) => conjugate X s) (s * n⁻¹) (hP s hs) ?_
    rw [mem_conjugate_iff]
    rw [show s * n⁻¹ * (n * y * n⁻¹) * (s * n⁻¹)⁻¹ = s * y * s⁻¹ by group]
    exact mem_conjugate_iff.1 hy
  exact hle hx

theorem mem_normalizer_of_conj_mem {X : Subgroup G} {n : G} (h1 : ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (h2 : ∀ x ∈ X, n⁻¹ * x * n⁻¹⁻¹ ∈ X) : n ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this

theorem le_pRank_of_card {p : ℕ} (hp : 1 < p) {X : Type*} [Group X] [Finite X]
    {E : Subgroup X} (hE : IsElementaryAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ pRank p X := by
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card X := Subgroup.card_le_card_group B

theorem ti_conjugate_commutation_excludes_small_rank_minimal_sylow_escape [Finite G]
    (T : Sylow 2 G) {V : Subgroup G} [IsElementaryAbelian 2 V] {d : ℕ} (hVd : Nat.card V = 2 ^ d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) {M : Subgroup G}
    (hWM : normalizer (((⨆ (g : G) (_ : conjugate V g ≤ T), conjugate V g : Subgroup G)) :
      Set G) ≤ M)
    (hCM : centralizer (V : Set G) ≤ M)
    (hcomm : ∀ g : G, conjugate V g ⊓ normalizer (V : Set G) ≠ ⊥ → ⁅V, conjugate V g⁆ = ⊥) :
    ¬ ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧ ¬ H ≤ M ∧
      ((T : Subgroup G) ≤ H ⊓ M ∧ H ⊓ M < H ∧
        ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y → Y < H → Y ≤ H ⊓ M) ∧
      pRank 2 (H ⧸ pCore 2 H) < d := by
  classical
  rintro ⟨H, hTH, hHM, ⟨-, -, hmax⟩, hrank⟩
  set W := (⨆ (g : G) (_ : conjugate V g ≤ T), conjugate V g : Subgroup G) with hWdef
  set R := inSubgroup (pCore 2) H with hRdef
  have hRT : R ≤ T := by
    have h1 := (pCore_isPGroup (p := 2) (G := H)).le_sylow_of_normal (T.subtype hTH)
    rintro _ ⟨x, hx, rfl⟩
    exact h1 hx
  have hHR : H ≤ normalizer (R : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_map_characteristic H (pCore 2 H))
  have hWconj : ∀ n : G, (∀ g, conjugate V g ≤ T → conjugate V (g * n⁻¹) ≤ T) →
      (∀ g, conjugate V g ≤ T → conjugate V (g * n⁻¹⁻¹) ≤ T) → n ∈ normalizer (W : Set G) :=
    fun n h1 h2 => mem_normalizer_of_conj_mem
      (fun x hx => conj_mem_iSup_conjugate (P := fun g => conjugate V g ≤ T) h1 hx)
      (fun x hx => conj_mem_iSup_conjugate (P := fun g => conjugate V g ≤ T) h2 hx)
  have hWR : ¬ W ≤ R := by
    intro hWR
    apply hHM
    intro h hh
    have hmem : ∀ g, conjugate V g ≤ T → ∀ y ∈ conjugate V g, y ∈ R := fun g hg y hy =>
      hWR (le_iSup₂ (f := fun g (_ : conjugate V g ≤ T) => conjugate V g) g hg hy)
    refine hWM (hWconj h (fun g hg x hx => hRT ?_) (fun g hg x hx => hRT ?_))
    · have hxg : h⁻¹ * x * h ∈ conjugate V g := by
        rw [mem_conjugate_iff] at hx ⊢
        simpa [mul_assoc] using hx
      have h2 := (mem_normalizer_iff.mp (hHR hh) (h⁻¹ * x * h)).mp (hmem g hg _ hxg)
      simpa [mul_assoc] using h2
    · have hxg : h * x * h⁻¹ ∈ conjugate V g := by
        rw [mem_conjugate_iff] at hx ⊢
        simpa [mul_assoc] using hx
      have h2 := (mem_normalizer_iff.mp (hHR (inv_mem hh)) (h * x * h⁻¹)).mp (hmem g hg _ hxg)
      simpa [mul_assoc] using h2
  obtain ⟨g, hgT, hgR⟩ : ∃ g : G, conjugate V g ≤ T ∧ ¬ conjugate V g ≤ R := by
    by_contra h
    push Not at h
    exact hWR (iSup₂_le fun g hg => h g hg)
  have hAH : conjugate V g ≤ H := hgT.trans hTH
  have hAe : IsElementaryAbelian 2 (conjugate V g) :=
    IsElementaryAbelian.map (MulAut.conj g⁻¹).toMonoidHom
  have hAcard : Nat.card (conjugate V g) = 2 ^ d := by
    rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hVd]
  have hAR : conjugate V g ⊓ R ≠ ⊥ := by
    intro hAR
    have : IsElementaryAbelian 2 ((conjugate V g).subgroupOf H) :=
      IsElementaryAbelian.subgroupOf hAH
    set f := (QuotientGroup.mk' (pCore 2 H)).comp ((conjugate V g).subgroupOf H).subtype
      with hf
    have hfi : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : (x : H) ∈ pCore 2 H := (QuotientGroup.eq_one_iff _).1 hx
      have h1 : ((x : H) : G) ∈ conjugate V g ⊓ R := mem_inf.2 ⟨x.2, ⟨x, hx', rfl⟩⟩
      rw [hAR, mem_bot] at h1
      exact Subtype.ext (Subtype.ext h1)
    have hEmap : ((conjugate V g).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) = f.range := by
      rw [hf, MonoidHom.range_comp, range_subtype]
    have hE : IsElementaryAbelian 2
        (((conjugate V g).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) :=
      IsElementaryAbelian.map _
    have hEcard :
        Nat.card (((conjugate V g).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 ^ d := by
      rw [hEmap, ← Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv, hAcard]
    have := le_pRank_of_card (by norm_num) hE hEcard
    omega
  obtain ⟨a, haAR, ha1⟩ : ∃ a ∈ conjugate V g ⊓ R, a ≠ 1 := by
    obtain ⟨⟨a, ha⟩, ha1⟩ := (ne_bot_iff_exists_ne_one).1 hAR
    exact ⟨a, ha, fun h => ha1 (Subtype.ext h)⟩
  have hAhC : ∀ h ∈ H, conjugate (conjugate V g) h ≤ centralizer (V : Set G) := by
    intro h hh
    have hb : h⁻¹ * a * h ∈ conjugate V (g * h) ⊓ normalizer (V : Set G) := by
      refine mem_inf.2 ⟨?_, hTV (hRT ?_)⟩
      · rw [mem_conjugate_iff,
          show g * h * (h⁻¹ * a * h) * (g * h)⁻¹ = g * a * g⁻¹ by group]
        exact mem_conjugate_iff.1 (mem_inf.1 haAR).1
      · have := (mem_normalizer_iff.mp (hHR (inv_mem hh)) a).mp (mem_inf.1 haAR).2
        simpa using this
    have hne : conjugate V (g * h) ⊓ normalizer (V : Set G) ≠ ⊥ := by
      intro hbot
      rw [hbot, mem_bot] at hb
      apply ha1
      calc a = h * (h⁻¹ * a * h) * h⁻¹ := by group
        _ = 1 := by rw [hb]; group
    have h2 := le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 (hcomm (g * h) hne))
    rwa [conjugate_mul] at h2
  set N := ⨆ (h : G) (_ : h ∈ H), conjugate (conjugate V g) h with hNdef
  have hNC : N ≤ centralizer (V : Set G) := iSup₂_le hAhC
  have hNH : N ≤ H := iSup₂_le fun h hh x hx => by
    have h1 := hAH (mem_conjugate_iff.1 hx)
    have h2 := mul_mem (mul_mem (inv_mem hh) h1) hh
    simpa [mul_assoc] using h2
  have hHN : H ≤ normalizer (N : Set G) := fun n hn => mem_normalizer_of_conj_mem
    (fun x hx => conj_mem_iSup_conjugate (P := fun s => s ∈ H)
      (fun s hs => mul_mem hs (inv_mem hn)) hx)
    (fun x hx => conj_mem_iSup_conjugate (P := fun s => s ∈ H)
      (fun s hs => mul_mem hs (inv_mem (inv_mem hn))) hx)
  have hAN : conjugate V g ≤ N := by
    refine le_trans ?_ (le_iSup₂ (f := fun h (_ : h ∈ H) => conjugate (conjugate V g) h) 1
      (one_mem H))
    rw [conjugate_one]
  have hNn : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).2 hHN
  set T' : Sylow 2 H := T.subtype hTH with hT'
  have hT'mem : ∀ {x : G} (hx : x ∈ H), (⟨x, hx⟩ : H) ∈ (T' : Subgroup H) ↔ x ∈ T :=
    fun hx => by rw [hT', Sylow.coe_subtype, mem_subgroupOf]; exact Iff.rfl
  have hsyl : IsSylowOf 2 ((T' : Subgroup H) ⊓ N.subgroupOf H) (N.subgroupOf H) := by
    have h1 : IsSylowOf 2 (T' : Subgroup H) ⊤ := by
      rw [isSylowOf_iff]
      refine ⟨le_top, T'.isPGroup', ?_⟩
      rw [relIndex_top_right]
      exact T'.not_dvd_index
    exact h1.inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.2 hNn])
  obtain ⟨P, hP⟩ := hsyl
  have hfr := Sylow.normalizer_sup_eq_top P
  rw [hP] at hfr
  set Y := (normalizer ((((T' : Subgroup H) ⊓ N.subgroupOf H : Subgroup H)) : Set H)).map
    H.subtype with hYdef
  have hH' : H = (⊤ : Subgroup H).map H.subtype := by rw [← MonoidHom.range_eq_map, range_subtype]
  have hY : Y ⊔ N = H := by
    have h1 := congrArg (map H.subtype) hfr
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hNH, ← hH'] at h1
    exact h1
  have hTnorm : (T' : Subgroup H) ≤
      normalizer ((((T' : Subgroup H) ⊓ N.subgroupOf H : Subgroup H)) : Set H) := fun x hx =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hx, by
      rw [normalizer_eq_top_iff.2 hNn]
      trivial⟩
  have hTY : (T : Subgroup G) ≤ Y := fun x hx => ⟨⟨x, hTH hx⟩, hTnorm ((hT'mem _).2 hx), rfl⟩
  by_cases hYH : Y = H
  ·
    have hnt := map_injective H.subtype_injective (hYH.trans hH')
    have : (((T' : Subgroup H) ⊓ N.subgroupOf H : Subgroup H)).Normal :=
      normalizer_eq_top_iff.1 hnt
    have hle : (T' : Subgroup H) ⊓ N.subgroupOf H ≤ pCore 2 H :=
      le_pCore_of_normal T'.isPGroup'.to_inf_left
    refine hgR fun x hx => ⟨⟨x, hAH hx⟩, hle (mem_inf.2 ⟨(hT'mem _).2 (hgT hx), hAN hx⟩), rfl⟩
  ·
    have hYM := hmax Y hTY (lt_of_le_of_ne (map_subtype_le _) hYH)
    apply hHM
    rw [← hY]
    exact sup_le (hYM.trans inf_le_right) (hNC.trans hCM)

end CFSG.Quasithin.SteinbergBS
