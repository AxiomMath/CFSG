module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMa
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34UniqueP
public import CFSG.Goldschmidt.Steps.G37Proj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private lemma s16h_mb_conj_eq_self {K : Subgroup G} {g : G}
    (h : ∀ z ∈ K, g * z = z * g) {z : G} (hz : z ∈ K) :
    g * z * g⁻¹ = z := by
  rw [h z hz]
  group

private lemma s16h_mb_map_conj_eq_of_centralizes {K : Subgroup G} {g : G}
    (h : ∀ z ∈ K, g * z = z * g) : K.map (MulAut.conj g).toMonoidHom = K := by
  apply le_antisymm
  · intro z hz
    obtain ⟨z', hz', hz'eq⟩ := Subgroup.mem_map.mp hz
    rw [← hz'eq]
    change g * z' * g⁻¹ ∈ K
    rw [s16h_mb_conj_eq_self h hz']
    exact hz'
  · intro z hz
    refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
    change g * z * g⁻¹ = z
    exact s16h_mb_conj_eq_self h hz

private lemma s16h_mb_Z₁_le {M B₀ Y Z₁ : Subgroup G} {x : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) : Z₁ ≤ Y := by
  rw [hB.sup]; exact le_sup_left

private lemma s16h_mb_Z₂_le {M B₀ Y Z₁ : Subgroup G} {x : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) :
    Z₁.map (MulAut.conj x).toMonoidHom ≤ Y := by
  rw [hB.sup]; exact le_sup_right

private lemma s16h_mb_Z₂_ne_Z₁ {Z₁ : Subgroup G} {x e : G}
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) :
    Z₁.map (MulAut.conj x).toMonoidHom ≠ Z₁ := by
  intro h
  obtain ⟨z, hz, hne⟩ := heZ₂
  exact hne (heZ₁ z (h ▸ hz))

private lemma s16h_mb_Z₂_map_conj_e {M B₀ Y Z₁ : Subgroup G} {x e : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) (heM : e ∈ M)
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) :
    (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj e).toMonoidHom =
      Z₁.map (MulAut.conj x).toMonoidHom := by
  rcases hB.perm e heM with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2
  · exact absurd (h1 ▸ s16h_mb_map_conj_eq_of_centralizes heZ₁)
      (s16h_mb_Z₂_ne_Z₁ heZ₁ heZ₂)

private lemma s16h_mb_Z₂_map_conj_x {M B₀ Y Z₁ : Subgroup G} {x e : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x)
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) :
    (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom = Z₁ := by
  rcases hB.perm x hB.mem with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd h1 (s16h_mb_Z₂_ne_Z₁ heZ₁ heZ₂)
  · exact h2

private lemma s16h_mb_f_mem_M {M B₀ Y Z₁ : Subgroup G} {x e : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) (heM : e ∈ M) : x * e * x⁻¹ ∈ M :=
  M.mul_mem (M.mul_mem hB.mem heM) (M.inv_mem hB.mem)

private lemma s16h_mb_f_pow {x e : G} {q : ℕ} (heq : e ^ q = 1) :
    (x * e * x⁻¹) ^ q = 1 := by
  have h : ((MulAut.conj x).toMonoidHom e) ^ q = 1 := by
    rw [← map_pow, heq, map_one]
  simpa using h

private lemma s16h_mb_f_centralizes_Z₂ {Z₁ : Subgroup G} {x e : G}
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e) :
    ∀ z ∈ Z₁.map (MulAut.conj x).toMonoidHom,
      (x * e * x⁻¹) * z = z * (x * e * x⁻¹) := by
  intro z hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  change (MulAut.conj x).toMonoidHom e * (MulAut.conj x).toMonoidHom z' =
    (MulAut.conj x).toMonoidHom z' * (MulAut.conj x).toMonoidHom e
  rw [← map_mul, heZ₁ z' hz', map_mul]

private lemma s16h_mb_f_moves_Z₁ {M B₀ Y Z₁ : Subgroup G} {x e : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x)
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) :
    ∃ z₁ ∈ Z₁, (x * e * x⁻¹) * z₁ * (x * e * x⁻¹)⁻¹ ≠ z₁ := by
  have heZ₂' := heZ₂
  obtain ⟨z₂, hz₂, hne⟩ := heZ₂'
  refine ⟨x * z₂ * x⁻¹, ?_, ?_⟩
  · have hZ₂x : (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom = Z₁ :=
      s16h_mb_Z₂_map_conj_x (M := M) (B₀ := B₀) (Y := Y) (Z₁ := Z₁) (x := x) (e := e)
        hB heZ₁ heZ₂
    rw [← hZ₂x]
    exact Subgroup.mem_map_of_mem _ hz₂
  · intro h
    apply hne
    have h' := congrArg (fun t => x⁻¹ * t * x) h
    have hconj : e * z₂ * e⁻¹ = z₂ := by
      rw [show x⁻¹ * ((x * e * x⁻¹) * (x * z₂ * x⁻¹) * (x * e * x⁻¹)⁻¹) * x
            = e * z₂ * e⁻¹ from by group,
          show x⁻¹ * (x * z₂ * x⁻¹) * x = z₂ from by group] at h'
      exact h'
    calc e * z₂ = e * z₂ * e⁻¹ * e := by group
      _ = z₂ * e := by rw [hconj]

private lemma s16h_mb_f_mem_B₀ {M B₀ Y Z₁ : Subgroup G} {x e : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) (heM : e ∈ M)
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) :
    x * e * x⁻¹ ∈ B₀ := by
  rw [hB.stab _ (s16h_mb_f_mem_M hB heM)]
  rcases hB.perm (x * e * x⁻¹) (s16h_mb_f_mem_M hB heM) with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h1
  · exfalso
    have hZ₂f : (Z₁.map (MulAut.conj x).toMonoidHom).map
        (MulAut.conj (x * e * x⁻¹)).toMonoidHom = Z₁.map (MulAut.conj x).toMonoidHom :=
      s16h_mb_map_conj_eq_of_centralizes
        (K := Z₁.map (MulAut.conj x).toMonoidHom) (g := x * e * x⁻¹)
        (s16h_mb_f_centralizes_Z₂ (x := x) heZ₁)
    exact (s16h_mb_Z₂_ne_Z₁ heZ₁ heZ₂) (h2.symm.trans hZ₂f).symm

private lemma s16h_mb_dvd_of_zpow_centralizes {x z : G} {q : ℕ} (hq : q.Prime)
    (hxq : x ^ q = 1) (hxz : x * z ≠ z * x) {k : ℤ}
    (hk : x ^ k * z = z * x ^ k) : (q : ℤ) ∣ k := by
  have hx1 : x ≠ 1 := by
    intro h1
    exact hxz (by rw [h1]; simp)
  have hord_dvd : orderOf x ∣ q := orderOf_dvd_of_pow_eq_one hxq
  have hord_ne1 : orderOf x ≠ 1 := fun h1 => hx1 (orderOf_eq_one_iff.mp h1)
  have hord : orderOf x = q := by
    rcases (Nat.dvd_prime hq).mp hord_dvd with h1 | h1
    · exact absurd h1 hord_ne1
    · exact h1
  let P : Subgroup G := Subgroup.zpowers x
  haveI : Fact (Nat.card ↥P).Prime := ⟨by rw [Nat.card_zpowers, hord]; exact hq⟩
  let K : Subgroup ↥P := (Subgroup.centralizer ({z} : Set G)).subgroupOf P
  have hKne : K ≠ ⊤ := by
    intro htop
    have hxP : (⟨x, Subgroup.mem_zpowers x⟩ : ↥P) ∈ K := by rw [htop]; trivial
    have hxcent : x ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mem_subgroupOf.mp hxP
    exact hxz ((Subgroup.mem_centralizer_iff.mp hxcent) z (by simp)).symm
  have hKbot : K = ⊥ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card K with h1 | h1
    · exact h1
    · exact absurd h1 hKne
  have hxkP : x ^ k ∈ P := Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hmemK : (⟨x ^ k, hxkP⟩ : ↥P) ∈ K := by
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_centralizer_iff.mpr (fun w hw => ?_)
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact hk.symm
  have hxk1 : x ^ k = 1 := by
    have h := hmemK
    rw [hKbot] at h
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp h)
  have hdvd : (orderOf x : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr hxk1
  rwa [hord] at hdvd
private lemma s16h_mb_commutator_mem_centralizer {M B₀ Y Z₁ : Subgroup G} {x e : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) (heM : e ∈ M)
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) :
    e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹ ∈ centralizer (Y : Set G) := by
  have hfM : x * e * x⁻¹ ∈ M := s16h_mb_f_mem_M hB heM
  have hfB : x * e * x⁻¹ ∈ B₀ := s16h_mb_f_mem_B₀ hB heM heZ₁ heZ₂
  have hfZ₁map : Z₁.map (MulAut.conj (x * e * x⁻¹)).toMonoidHom = Z₁ :=
    (hB.stab _ hfM).mp hfB
  have heZ₂map : (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj e).toMonoidHom =
      Z₁.map (MulAut.conj x).toMonoidHom := s16h_mb_Z₂_map_conj_e hB heM heZ₁ heZ₂
  have hfN : x * e * x⁻¹ ∈ normalizer (Z₁ : Set G) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hfZ₁map
  have hf_invN : (x * e * x⁻¹)⁻¹ ∈ normalizer (Z₁ : Set G) :=
    (normalizer (Z₁ : Set G)).inv_mem hfN
  have hfconj : ∀ z ∈ Z₁, (x * e * x⁻¹) * z * (x * e * x⁻¹)⁻¹ ∈ Z₁ :=
    fun z hz => (Subgroup.mem_normalizer_iff.mp hfN z).1 hz
  have hfinvconj : ∀ z ∈ Z₁, (x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹) ∈ Z₁ :=
    fun z hz => by
      simpa using (Subgroup.mem_normalizer_iff.mp hf_invN z).1 hz
  have heN₂ : e ∈ normalizer (Z₁.map (MulAut.conj x).toMonoidHom : Set G) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mpr heZ₂map
  have he_invN₂ : e⁻¹ ∈ normalizer (Z₁.map (MulAut.conj x).toMonoidHom : Set G) :=
    (normalizer _).inv_mem heN₂
  have he_invconj₂ : ∀ z ∈ Z₁.map (MulAut.conj x).toMonoidHom,
      e⁻¹ * z * e ∈ Z₁.map (MulAut.conj x).toMonoidHom :=
    fun z hz => by
      simpa using (Subgroup.mem_normalizer_iff.mp he_invN₂ z).1 hz
  have heZ₁conj : ∀ z ∈ Z₁, e * z * e⁻¹ = z := by
    intro z hz
    have h := heZ₁ z hz
    calc e * z * e⁻¹ = z * e * e⁻¹ := by rw [h]
      _ = z := by group
  have heZ₁invconj : ∀ z ∈ Z₁, e⁻¹ * z * e = z := by
    intro z hz
    have h := heZ₁ z hz
    calc e⁻¹ * z * e = e⁻¹ * (z * e) := by group
      _ = e⁻¹ * (e * z) := by rw [h]
      _ = z := by group
  have hZ₁pt : ∀ z ∈ Z₁,
      (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) * z *
        (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹)⁻¹ = z := by
    intro z hz
    have h1 : (x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹) ∈ Z₁ := hfinvconj z hz
    have h2 : e⁻¹ * ((x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹)) * e =
        (x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹) := heZ₁invconj _ h1
    have h3 : (x * e * x⁻¹) * ((x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹)) *
        (x * e * x⁻¹)⁻¹ ∈ Z₁ := hfconj _ h1
    have h4 : e * ((x * e * x⁻¹) * ((x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹)) *
        (x * e * x⁻¹)⁻¹) * e⁻¹ =
        (x * e * x⁻¹) * ((x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹)) * (x * e * x⁻¹)⁻¹ :=
      heZ₁conj _ h3
    calc
      (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) * z *
          (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹)⁻¹
          = e * (x * e * x⁻¹) * e⁻¹ * ((x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹)) *
              e * (x * e * x⁻¹)⁻¹ * e⁻¹ := by group
      _ = e * (x * e * x⁻¹) * (e⁻¹ * ((x * e * x⁻¹)⁻¹ * z *
              (x * e * x⁻¹)) * e) * (x * e * x⁻¹)⁻¹ * e⁻¹ := by group
      _ = e * (x * e * x⁻¹) * ((x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹)) *
              (x * e * x⁻¹)⁻¹ * e⁻¹ := by rw [h2]
      _ = e * ((x * e * x⁻¹) * ((x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹)) *
              (x * e * x⁻¹)⁻¹) * e⁻¹ := by group
      _ = (x * e * x⁻¹) * ((x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹)) *
              (x * e * x⁻¹)⁻¹ := h4
      _ = z := by group
  have hZ₂pt : ∀ z ∈ Z₁.map (MulAut.conj x).toMonoidHom,
      (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) * z *
        (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹)⁻¹ = z := by
    intro z hz
    have hfcent := s16h_mb_f_centralizes_Z₂ (x := x) heZ₁
    have h1 : (x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹) = z := by
      have h := hfcent z hz
      calc (x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹) =
            (x * e * x⁻¹)⁻¹ * (z * (x * e * x⁻¹)) := by group
        _ = (x * e * x⁻¹)⁻¹ * ((x * e * x⁻¹) * z) := by rw [h]
        _ = z := by group
    have h2 : e⁻¹ * z * e ∈ Z₁.map (MulAut.conj x).toMonoidHom := he_invconj₂ z hz
    have h3 : (x * e * x⁻¹) * (e⁻¹ * z * e) * (x * e * x⁻¹)⁻¹ = e⁻¹ * z * e := by
      have h := hfcent (e⁻¹ * z * e) h2
      calc (x * e * x⁻¹) * (e⁻¹ * z * e) * (x * e * x⁻¹)⁻¹ =
            (e⁻¹ * z * e) * (x * e * x⁻¹) * (x * e * x⁻¹)⁻¹ := by rw [h]
        _ = e⁻¹ * z * e := by group
    calc
      (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) * z *
          (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹)⁻¹
          = e * (x * e * x⁻¹) * e⁻¹ * ((x * e * x⁻¹)⁻¹ * z * (x * e * x⁻¹)) *
              e * (x * e * x⁻¹)⁻¹ * e⁻¹ := by group
      _ = e * (x * e * x⁻¹) * e⁻¹ * z * e * (x * e * x⁻¹)⁻¹ * e⁻¹ := by rw [h1]
      _ = e * ((x * e * x⁻¹) * (e⁻¹ * z * e) * (x * e * x⁻¹)⁻¹) * e⁻¹ := by
        group
      _ = e * (e⁻¹ * z * e) * e⁻¹ := by rw [h3]
      _ = z := by group
  have hZ₁c : Z₁ ≤ Subgroup.centralizer
      ({e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    simp only [Set.mem_singleton_iff] at hw
    subst w
    have h := hZ₁pt z hz
    calc (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) * z =
          ((e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) * z *
            (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹)⁻¹) *
            (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) := by group
      _ = z * (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) := by rw [h]
  have hZ₂c : Z₁.map (MulAut.conj x).toMonoidHom ≤ Subgroup.centralizer
      ({e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    simp only [Set.mem_singleton_iff] at hw
    subst w
    have h := hZ₂pt z hz
    calc (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) * z =
          ((e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) * z *
            (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹)⁻¹) *
            (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) := by group
      _ = z * (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) := by rw [h]
  have hYc : Y ≤ Subgroup.centralizer
      ({e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹} : Set G) := by
    rw [hB.sup]
    exact sup_le hZ₁c hZ₂c
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyc : y ∈ Subgroup.centralizer
      ({e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹} : Set G) := hYc hy
  exact ((Subgroup.mem_centralizer_iff.mp hyc)
    (e * (x * e * x⁻¹) * e⁻¹ * (x * e * x⁻¹)⁻¹) (by simp)).symm

theorem s16h_mixed_uniqueMax (D : Data G) (h61 : UC6.R6_1 D) {B₀ Y Z₁ : Subgroup G} {x : G}
    (hB : s16h_MixedCfg D.M B₀ Y Z₁ x) {q : ℕ} (hq : q ∈ D.sig) {e : G} (heM : e ∈ D.M)
    (heq : e ^ q = 1) (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) :
    UniqueMax D.M (D.M ⊓ normalizer ((D.T ⊓ centralizer (Y : Set G) : Subgroup G) : Set G)) := by
  classical
  have hqp : q.Prime := (D.sig_prime q hq).1
  haveI : Fact (Nat.Prime q) := ⟨hqp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := D.M ⊓ centralizer (Y : Set G)
  let S : Subgroup G := D.T ⊓ centralizer (Y : Set G)
  let N : Subgroup G := D.M ⊓ normalizer (S : Set G)
  change UniqueMax D.M N
  let f : G := x * e * x⁻¹
  have hfM : f ∈ D.M := s16h_mb_f_mem_M hB heM
  have hnormC : D.M ≤ normalizer (C : Set G) := by
    have h1 : D.M ≤ normalizer (D.M : Set G) := D.M.le_normalizer
    have h2 : D.M ≤ normalizer (centralizer (Y : Set G) : Set G) :=
      CFSG.Goldschmidt.G37.normalizer_le_normalizer_centralizer hB.norm
    have h3 := (le_inf h1 h2).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := D.M)
        (K := centralizer (Y : Set G)))
    simpa [C] using h3
  haveI hCnormal : (C.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hnormC
  have hSyleq : D.T ⊓ C = S := by
    ext g
    simp only [S, C, Subgroup.mem_inf]
    constructor
    · rintro ⟨ht, -, hc⟩; exact ⟨ht, hc⟩
    · rintro ⟨ht, hc⟩; exact ⟨ht, D.sylowM.le ht, hc⟩
  have hSylC : CFSG.ABGLocalTools.IsSylowOf 2 S C := by
    have h := D.sylowM.inf_of_le_normalizer (N := C) inf_le_left hnormC
    rwa [hSyleq] at h
  have hfr : D.M ≤ C ⊔ N :=
    uc22p22t_frattini_sup (q := 2) (H := D.M) (K := C) (S := S) inf_le_left hnormC hSylC
  have hsup : C ⊔ N = D.M := le_antisymm (sup_le inf_le_left inf_le_left) hfr
  let C' : Subgroup ↥D.M := C.subgroupOf D.M
  let N' : Subgroup ↥D.M := N.subgroupOf D.M
  have htop : C' ⊔ N' = ⊤ := by
    change C.subgroupOf D.M ⊔ N.subgroupOf D.M = ⊤
    rw [← Subgroup.subgroupOf_sup (A := C) (A' := N) (B := D.M) inf_le_left inf_le_left,
      hsup, Subgroup.subgroupOf_self]
  let e' : ↥D.M := ⟨e, heM⟩
  let f' : ↥D.M := ⟨f, hfM⟩
  let Hq := ↥D.M ⧸ C'
  let φ : ↥N' →* Hq := (QuotientGroup.mk' C').comp N'.subtype
  let ehat : Hq := QuotientGroup.mk' C' e'
  let fhat : Hq := QuotientGroup.mk' C' f'
  let E : Subgroup Hq := Subgroup.closure ({ehat, fhat} : Set Hq)
  have hdecomp : ∀ g : ↥D.M, ∃ c ∈ C', ∃ n ∈ N', c * n = g := by
    intro g
    have hg : g ∈ (C' ⊔ N') := by rw [htop]; trivial
    exact Subgroup.mem_sup_of_normal_left.mp hg
  obtain ⟨ce, hce, ne, hne, hcen⟩ := hdecomp e'
  have hehat_range : ehat ∈ φ.range := by
    refine ⟨⟨ne, hne⟩, ?_⟩
    have hce1 : (QuotientGroup.mk' C') ce = 1 := (QuotientGroup.eq_one_iff ce).mpr hce
    change (QuotientGroup.mk' C') (ne : ↥D.M) = (QuotientGroup.mk' C') e'
    rw [← hcen, map_mul, hce1, one_mul]
  obtain ⟨cf, hcf, nf, hnf, hcfn⟩ := hdecomp f'
  have hfhat_range : fhat ∈ φ.range := by
    refine ⟨⟨nf, hnf⟩, ?_⟩
    have hcf1 : (QuotientGroup.mk' C') cf = 1 := (QuotientGroup.eq_one_iff cf).mpr hcf
    change (QuotientGroup.mk' C') (nf : ↥D.M) = (QuotientGroup.mk' C') f'
    rw [← hcfn, map_mul, hcf1, one_mul]
  have hehatq : ehat ^ q = 1 := by
    change ((QuotientGroup.mk' C') e') ^ q = 1
    rw [← map_pow, show e' ^ q = 1 from Subtype.ext heq, map_one]
  have hfhatq : fhat ^ q = 1 := by
    change ((QuotientGroup.mk' C') f') ^ q = 1
    rw [← map_pow, show f' ^ q = 1 from Subtype.ext (s16h_mb_f_pow (x := x) heq), map_one]
  have he_notC : e ∉ C := by
    intro hmem
    obtain ⟨z, hz, hne'⟩ := heZ₂
    exact hne' (((Subgroup.mem_centralizer_iff.mp hmem.2) z
      (s16h_mb_Z₂_le hB hz)).symm)
  have hehatne : ehat ≠ 1 := by
    intro h1
    apply he_notC
    have h2 : e' ∈ C' := (QuotientGroup.eq_one_iff e').mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  have hf_notC : f ∉ C := by
    intro hmem
    obtain ⟨z₁, hz₁, hne₁⟩ := s16h_mb_f_moves_Z₁ hB heZ₁ heZ₂
    have hcommz := (Subgroup.mem_centralizer_iff.mp hmem.2) z₁ (s16h_mb_Z₁_le hB hz₁)
    apply hne₁
    calc f * z₁ * f⁻¹ = z₁ * f * f⁻¹ := by rw [← hcommz]
      _ = z₁ := by group
  have hfhatne : fhat ≠ 1 := by
    intro h1
    apply hf_notC
    have h2 : f' ∈ C' := (QuotientGroup.eq_one_iff f').mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  have hmemCommG : e * f * e⁻¹ * f⁻¹ ∈ C := by
    refine ⟨?_, ?_⟩
    · exact D.M.mul_mem (D.M.mul_mem (D.M.mul_mem heM hfM) (D.M.inv_mem heM))
        (D.M.inv_mem hfM)
    · exact s16h_mb_commutator_mem_centralizer hB heM heZ₁ heZ₂
  have hcomm_quot : ehat * fhat = fhat * ehat := by
    have hmemC' : e' * f' * e'⁻¹ * f'⁻¹ ∈ C' := by
      rw [Subgroup.mem_subgroupOf]
      simpa [e', f'] using hmemCommG
    have h1 : ehat * fhat * ehat⁻¹ * fhat⁻¹ = 1 := by
      have hcomp : ehat * fhat * ehat⁻¹ * fhat⁻¹ =
          (QuotientGroup.mk' C') (e' * f' * e'⁻¹ * f'⁻¹) := by
        simp [ehat, fhat, map_mul]
      rw [hcomp]
      exact (QuotientGroup.eq_one_iff _).mpr hmemC'
    calc ehat * fhat = (ehat * fhat * ehat⁻¹ * fhat⁻¹) * (fhat * ehat) := by group
      _ = 1 * (fhat * ehat) := by rw [h1]
      _ = fhat * ehat := one_mul _
  have hpair : ({ehat, fhat} : Set Hq).Pairwise Commute := by
    intro a ha b hb hne'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hne'
    · exact hcomm_quot
    · exact hcomm_quot.symm
    · exact absurd rfl hne'
  haveI hEcomm : IsMulCommutative ↥E :=
    Subgroup.isMulCommutative_closure (k := ({ehat, fhat} : Set Hq)) hpair
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val
      ((isMulCommutative_iff.mp hEcomm) (⟨a, ha⟩ : ↥E) (⟨b, hb⟩ : ↥E))
  have hExp : Monoid.exponent ↥E ∣ q := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    apply Subtype.ext
    refine Subgroup.closure_induction (k := ({ehat, fhat} : Set Hq))
      (p := fun z _ => z ^ q = 1) ?_ ?_ ?_ ?_ a.2
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hehatq
      · exact hfhatq
    · exact one_pow q
    · intro u v hu hv huq hvq
      have hc : Commute u v := hcommE u hu v hv
      rw [hc.mul_pow, huq, hvq, mul_one]
    · intro u hu huq
      rw [inv_pow, huq, inv_one]
  have hEq : IsPGroup q E :=
    IsPGroup.of_exponent_dvd_pow (p := q) (n := 1) (by simpa using hExp)
  have hfhat_not_z : fhat ∉ Subgroup.zpowers ehat := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : (QuotientGroup.mk' C') (e' ^ k) = (QuotientGroup.mk' C') f' := by
      rw [map_zpow]
      exact hk
    have hdiv : f' / (e' ^ k) ∈ C' := by
      rw [← QuotientGroup.eq_iff_div_mem]
      exact hk'.symm
    have hmemC' : f' * (e' ^ k)⁻¹ ∈ C' := by
      simpa [div_eq_mul_inv] using hdiv
    have hmemG : f * (e ^ k)⁻¹ ∈ C := by
      have h := Subgroup.mem_subgroupOf.mp hmemC'
      simpa [e', f'] using h
    obtain ⟨z₂, hz₂, hne₂⟩ := heZ₂
    have hcentral : f * (e ^ k)⁻¹ ∈ centralizer (Y : Set G) := hmemG.2
    have hcommz := (Subgroup.mem_centralizer_iff.mp hcentral) z₂ (s16h_mb_Z₂_le hB hz₂)
    have hfz₂ : f * z₂ = z₂ * f := s16h_mb_f_centralizes_Z₂ (x := x) heZ₁ z₂ hz₂
    have h1 : z₂ * (f * (e ^ k)⁻¹) = f * z₂ * (e ^ k)⁻¹ := by
      rw [hfz₂]; group
    have hzb : z₂ * (e ^ k)⁻¹ = (e ^ k)⁻¹ * z₂ := by
      have h3 : f * z₂ * (e ^ k)⁻¹ = f * (e ^ k)⁻¹ * z₂ := by
        rw [← h1, hcommz]
      have h4 := congrArg (fun t => f⁻¹ * t) h3
      simpa [mul_assoc] using h4
    have hzpow : z₂ * (e ^ k) = (e ^ k) * z₂ := by
      have h : Commute z₂ (e ^ k) := by
        simpa using (show Commute z₂ ((e ^ k)⁻¹) from hzb).inv_right
      exact (commute_iff_eq z₂ (e ^ k)).mp h
    have hkq : (q : ℤ) ∣ k :=
      s16h_mb_dvd_of_zpow_centralizes (x := e) (z := z₂) hqp heq hne₂ hzpow.symm
    obtain ⟨m, hm⟩ := hkq
    have hek1 : e ^ k = 1 := by
      rw [hm, zpow_mul, zpow_natCast, heq, one_zpow]
    apply hf_notC
    rwa [hek1, inv_one, mul_one] at hmemG
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    haveI : IsCyclic ↥E := hcyc
    have hexp_eq : Monoid.exponent ↥E = Nat.card ↥E := IsCyclic.exponent_eq_card
    have hcard : Nat.card ↥E = q := by
      have hne1 : Monoid.exponent ↥E ≠ 1 := by
        intro h1
        have hnt : Nontrivial ↥E := by
          refine ⟨⟨ehat, Subgroup.subset_closure (by simp)⟩, ⟨1, E.one_mem⟩, ?_⟩
          intro h
          exact hehatne (congrArg Subtype.val h)
        have := Monoid.one_lt_exponent (G := ↥E)
        omega
      rcases (Nat.dvd_prime hqp).mp hExp with h1 | h1
      · exact absurd h1 hne1
      · rw [← hexp_eq, h1]
    let ehatE : ↥E := ⟨ehat, Subgroup.subset_closure (by simp)⟩
    let fhatE : ↥E := ⟨fhat, Subgroup.subset_closure (by simp)⟩
    have hehatE_ne : ehatE ≠ 1 := by
      intro h1
      exact hehatne (congrArg Subtype.val h1)
    have hmemz : fhatE ∈ Subgroup.zpowers ehatE :=
      mem_zpowers_of_prime_card (G := ↥E) (p := q) hcard hehatE_ne
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmemz
    have hk' : ehat ^ k = fhat := by
      simpa [ehatE, fhatE] using congrArg Subtype.val hk
    exact hfhat_not_z (Subgroup.mem_zpowers_iff.mpr ⟨k, hk'⟩)
  have hE_range : E ≤ φ.range := by
    change Subgroup.closure ({ehat, fhat} : Set Hq) ≤ φ.range
    refine (Subgroup.closure_le φ.range).mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hehat_range
    · exact hfhat_range
  obtain ⟨S₀, hS₀p, hS₀c⟩ := s16h_exists_noncyclic_of_le_range φ hqp hE_range hEq hEnc
  let gmap : ↥N' →* G := D.M.subtype.comp N'.subtype
  let S₁ : Subgroup G := S₀.map gmap
  have hS₁p : IsPGroup q S₁ := hS₀p.map gmap
  have hgmap_inj : Function.Injective gmap := by
    intro a b h
    exact Subtype.ext (Subtype.ext h)
  have hS₁c : ¬ IsCyclic ↥S₁ := by
    intro hc
    exact hS₀c ((Subgroup.equivMapOfInjective S₀ gmap hgmap_inj).isCyclic.2 hc)
  have hS₁N : S₁ ≤ N := by
    rintro a ⟨b, hb, rfl⟩
    exact Subgroup.mem_subgroupOf.mp b.2
  exact s16c34_uniqueMax_of_noncyclic D h61 hq hS₁p hS₁c hS₁N inf_le_left

theorem s16h_inCalW_of_mixed (D : Data G) (h61 : UC6.R6_1 D) {B₀ Y Z₁ : Subgroup G} {x : G}
    (hB : s16h_MixedCfg D.M B₀ Y Z₁ x) {q : ℕ} (hq : q ∈ D.sig) {e : G} (heM : e ∈ D.M)
    (heq : e ^ q = 1) (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e)
    (hc : ∀ K : Subgroup G, K ≤ B₀ → (∀ g ∈ B₀, ∀ k ∈ K, g * k * g⁻¹ ∈ K) →
      (∀ k ∈ K, ∃ n : ℕ, k ^ 2 ^ n ∈ centralizer (Z₁ : Set G)) →
      (∃ f ∈ B₀, ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ f ∉ centralizer (Z₁ : Set G) ∧
        f ^ r ∈ centralizer (Z₁ : Set G)) → K ≤ centralizer (Z₁ : Set G)) :
    InCalW D.M D.T Y := by
  have hpp := D.sig_prime q hq
  have hcard : 8 ≤ Nat.card ↥Y :=
    s16h_mixed_card_ge_eight hB hpp.1 hpp.2 heM heq heZ₁ heZ₂
  have hum : UniqueMax D.M
      (D.M ⊓ normalizer ((D.T ⊓ centralizer (Y : Set G) : Subgroup G) : Set G)) :=
    s16h_mixed_uniqueMax D h61 hB hq heM heq heZ₁ heZ₂
  have htr : TwoReduced D.M Y :=
    s16h_mixed_two_reduced hB hpp.1 hpp.2 heM heq heZ₁ heZ₂ hc
  have hYne : Y ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  exact ⟨⟨⟨hYne, hB.le, hB.norm, hB.elem⟩, hum⟩, hcard, htr⟩
