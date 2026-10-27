module

public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux

public section

namespace CFSG.Quasithin.SteinbergBQ

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def conjSub (g : G) (X : Subgroup G) : Subgroup G := X.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {g x : G} {X : Subgroup G} : x ∈ conjSub g X ↔ g⁻¹ * x * g ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩

theorem conjSub_conjSub (g h : G) (X : Subgroup G) :
    conjSub h (conjSub g X) = conjSub (h * g) X := by
  ext x
  simp only [mem_conjSub, mul_inv_rev, mul_assoc]

theorem conjSub_one (X : Subgroup G) : conjSub 1 X = X := by
  ext x
  simp [mem_conjSub]

theorem conjSub_mono {g : G} {X Y : Subgroup G} (h : X ≤ Y) : conjSub g X ≤ conjSub g Y :=
  Subgroup.map_mono h

theorem conjSub_inv_conjSub (g : G) (X : Subgroup G) : conjSub g⁻¹ (conjSub g X) = X := by
  rw [conjSub_conjSub, inv_mul_cancel, conjSub_one]

theorem conjSub_inf (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊓ Y) = conjSub g X ⊓ conjSub g Y := by
  ext x
  simp only [mem_conjSub, Subgroup.mem_inf]

theorem conjSub_centralizer (g : G) (X : Subgroup G) :
    Subgroup.centralizer (conjSub g X : Set G) = conjSub g (Subgroup.centralizer (X : Set G)) := by
  ext x
  rw [mem_conjSub, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have := h (g * y * g⁻¹) (mem_conjSub.2 (by simpa [mul_assoc] using hy))
    have e : y * (g⁻¹ * x * g) = g⁻¹ * (g * y * g⁻¹ * x) * g := by group
    rw [e, this]
    group
  · intro h y hy
    have := h (g⁻¹ * y * g) (mem_conjSub.1 hy)
    have e : y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    rw [e, this]
    group

theorem conjSub_normalizer (g : G) (X : Subgroup G) :
    Subgroup.normalizer (conjSub g X : Set G) = conjSub g (Subgroup.normalizer (X : Set G)) := by
  ext x
  rw [mem_conjSub, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (g * y * g⁻¹)
    simp only [mem_conjSub] at this
    have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    have e2 : g⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) * g = g⁻¹ * x * g * y * (g⁻¹ * x * g)⁻¹ := by group
    rw [e1, e2] at this
    exact this
  · intro h y
    have := h (g⁻¹ * y * g)
    simp only [mem_conjSub]
    have e2 : g⁻¹ * (x * y * x⁻¹) * g = g⁻¹ * x * g * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ := by group
    rw [e2]
    exact this

theorem relIndex_conjSub (g : G) (B W : Subgroup G) :
    (conjSub g B).relIndex (conjSub g W) = B.relIndex W :=
  Subgroup.relIndex_map_map_of_injective B W (MulAut.conj g).injective

theorem card_conjSub (g : G) (X : Subgroup G) : Nat.card (conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjSub_eq_of_mem_normalizer {n : G} {X : Subgroup G}
    (hn : n ∈ Subgroup.normalizer (X : Set G)) : conjSub n X = X := by
  ext x
  rw [mem_conjSub]
  have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) x)
  rw [inv_inv] at this
  exact this.symm

theorem exists_le_conjSub_of_le_normalizer [Finite G] (T : Sylow 2 G) {N : Subgroup G}
    (hTN : (T : Subgroup G) ≤ N) {W : Subgroup G} (hWN : W ≤ N) (hW : IsPGroup 2 W) :
    ∃ n ∈ N, W ≤ conjSub n T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW' : IsPGroup 2 (W.subgroupOf N) := hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWN).symm
  obtain ⟨Q, hQ⟩ := hW'.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N (T.subtype hTN) Q
  rw [Sylow.smul_subtype] at hn
  refine ⟨n, n.2, fun w hw => ?_⟩
  have h1 : (⟨w, hWN hw⟩ : N) ∈ (Q : Subgroup N) := hQ hw
  rw [← hn, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h1
  exact h1

@[expose] def twoResidualOf (K : Subgroup G) : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : N ≤ K) (_ : (N.subgroupOf K).Normal)
    (_ : ∃ m : ℕ, N.relIndex K = 2 ^ m), N

theorem relIndex_twoResidualOf [Finite G] (K : Subgroup G) :
    twoResidualOf K ≤ K ∧ ∃ m : ℕ, (twoResidualOf K).relIndex K = 2 ^ m := by
  classical
  let S : Set (Subgroup G) :=
    {N | N ≤ K ∧ (N.subgroupOf K).Normal ∧ ∃ m : ℕ, N.relIndex K = 2 ^ m}
  have hK : K ∈ S := ⟨le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance,
    0, by rw [Subgroup.relIndex_self, pow_zero]⟩
  have hinf : ∀ N₁ ∈ S, ∀ N₂ ∈ S, N₁ ⊓ N₂ ∈ S := by
    rintro N₁ ⟨h1K, h1n, m₁, hm₁⟩ N₂ ⟨h2K, h2n, m₂, hm₂⟩
    have heq : (N₁ ⊓ N₂).subgroupOf K = N₁.subgroupOf K ⊓ N₂.subgroupOf K :=
      Subgroup.ext fun _ => Iff.rfl
    refine ⟨inf_le_left.trans h1K, by rw [heq]; infer_instance, ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex (N₁ ⊓ N₂) N₁ K inf_le_left h1K
    rw [Subgroup.inf_relIndex_left] at h1
    have h2 : N₂.relIndex N₁ ∣ N₂.relIndex K := by
      rw [← Subgroup.relIndex_subgroupOf h1K]
      exact Subgroup.relIndex_dvd_index_of_normal _ _
    have hdvd : (N₁ ⊓ N₂).relIndex K ∣ 2 ^ (m₂ + m₁) := by
      rw [← h1, pow_add, hm₁, ← hm₂]
      exact Nat.mul_dvd_mul_right h2 _
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨m, hm⟩
  obtain ⟨N₀, hN₀⟩ := S.toFinite.exists_minimal ⟨K, hK⟩
  have hle : ∀ N ∈ S, N₀ ≤ N := fun N hN =>
    (hN₀.2 (hinf N₀ hN₀.1 N hN) inf_le_left).trans inf_le_right
  have heq : twoResidualOf K = N₀ := by
    refine le_antisymm ?_ ?_
    · obtain ⟨h1, h2, h3⟩ := hN₀.1
      exact iInf_le_of_le N₀ (iInf_le_of_le h1 (iInf_le_of_le h2 (iInf_le_of_le h3 le_rfl)))
    · exact le_iInf fun N => le_iInf fun h1 => le_iInf fun h2 => le_iInf fun h3 =>
        hle N ⟨h1, h2, h3⟩
  rw [heq]
  exact ⟨hN₀.1.1, hN₀.1.2.2⟩

theorem conjugate_core_generated_subgroup_confinement [Finite G] (T : Sylow 2 G)
    {V : Subgroup G} (_hVT : V ≤ T) [IsElementaryAbelian 2 V] {d : ℕ} (hVd : Nat.card V = 2 ^ d)
    (hTV : (T : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) {M : Subgroup G}
    (hVM : Subgroup.normalizer (V : Set G) ≤ M) {j r : ℕ} (hjr : j < r) (_hrd : r ≤ d)
    (h1 : ∀ F : Subgroup G, F ≤ V → F.relIndex V < 2 ^ r →
      Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (V : Set G))
    (h2 : ∀ (g : G) (B : Subgroup G), B ≤ (T : Subgroup G) ⊓ conjSub g V →
      B.relIndex (conjSub g V) ≤ 2 ^ j → B ≤ Subgroup.centralizer (V : Set G))
    {H : Subgroup G} (_hTH : (T : Subgroup G) ≤ H) {D : Subgroup G} (hD : D ≤ H ⊓ M)
    (P : Finset (Subgroup G × Subgroup G)) (_hPH : ∀ AK ∈ P, AK.1 ≤ H ∧ AK.2 ≤ H)
    (hgen : H = D ⊔ ⨆ AK ∈ P, AK.2)
    (hP : ∀ AK ∈ P, (∃ g : G, AK.1 = conjSub g V) ∧ AK.1 ≤ AK.2 ∧
      IsSylowTwoOf ((T : Subgroup G) ⊓ AK.2) AK.2 ∧
      (AK.1 ⊓ pCoreOf 2 AK.2).relIndex AK.1 ≤ 2 ^ j ∧
      twoResidualOf AK.2 ≤ Subgroup.closure (⋃ k ∈ AK.2, (conjSub k AK.1 : Set G))) :
    H ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : (T : Subgroup G) ≤ M := hTV.trans hVM
  have hV2 : IsPGroup 2 V := IsPGroup.of_card hVd
  have hW2 : ∀ g : G, IsPGroup 2 (conjSub g V) := fun g =>
    IsPGroup.of_card ((card_conjSub g V).trans hVd)
  have hTg : ∀ g : G, (conjSub g T : Subgroup G) = ((g • T : Sylow 2 G) : Subgroup G) :=
    fun g => rfl
  have h1g : ∀ g : G, ∀ F : Subgroup G, F ≤ conjSub g V → F.relIndex (conjSub g V) < 2 ^ r →
      Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (conjSub g V : Set G) := by
    intro g F hF hFr
    have hF' : conjSub g⁻¹ F ≤ V := by
      have := conjSub_mono (g := g⁻¹) hF
      rwa [conjSub_inv_conjSub] at this
    have hr' : (conjSub g⁻¹ F).relIndex V < 2 ^ r := by
      rw [← conjSub_inv_conjSub g V, relIndex_conjSub]
      exact hFr
    have h := conjSub_mono (g := g) (h1 _ hF' hr')
    rw [← conjSub_centralizer, conjSub_conjSub, mul_inv_cancel, conjSub_one,
      ← conjSub_normalizer] at h
    exact h
  have h2g : ∀ g : G, ∀ (h : G) (B : Subgroup G), B ≤ conjSub g T ⊓ conjSub h V →
      B.relIndex (conjSub h V) ≤ 2 ^ j → B ≤ Subgroup.centralizer (conjSub g V : Set G) := by
    intro g h B hB hBj
    have hB' : conjSub g⁻¹ B ≤ (T : Subgroup G) ⊓ conjSub (g⁻¹ * h) V := by
      have := conjSub_mono (g := g⁻¹) hB
      rwa [conjSub_inf, conjSub_inv_conjSub, conjSub_conjSub] at this
    have hBj' : (conjSub g⁻¹ B).relIndex (conjSub (g⁻¹ * h) V) ≤ 2 ^ j := by
      rw [← conjSub_conjSub, relIndex_conjSub]
      exact hBj
    have h := conjSub_mono (g := g) (h2 _ _ hB' hBj')
    rwa [conjSub_conjSub, mul_inv_cancel, conjSub_one, ← conjSub_centralizer] at h
  have hstep : ∀ g h : G, conjSub h V ≤ Subgroup.normalizer (conjSub g V : Set G) →
      conjSub h V ≤ Subgroup.centralizer (conjSub g V : Set G) := by
    intro g h hW
    have hTgN : ((g • T : Sylow 2 G) : Subgroup G) ≤
        Subgroup.normalizer (conjSub g V : Set G) := by
      rw [← hTg, conjSub_normalizer]
      exact conjSub_mono hTV
    obtain ⟨n, hn, hle⟩ := exists_le_conjSub_of_le_normalizer (g • T) hTgN hW (hW2 h)
    have hle' : conjSub (n⁻¹ * h) V ≤ conjSub g T := by
      have := conjSub_mono (g := n⁻¹) hle
      rw [conjSub_conjSub, conjSub_conjSub, inv_mul_cancel, conjSub_one] at this
      exact this
    have hcent := h2g g (n⁻¹ * h) (conjSub (n⁻¹ * h) V) (le_inf hle' le_rfl)
      (by rw [Subgroup.relIndex_self]; exact Nat.one_le_two_pow)
    have := conjSub_mono (g := n) hcent
    rw [conjSub_conjSub, mul_inv_cancel_left, ← conjSub_centralizer,
      conjSub_eq_of_mem_normalizer hn] at this
    exact this
  have hKM : ∀ AK ∈ P, AK.2 ≤ M := by
    intro AK hAK
    obtain ⟨⟨g, hAg⟩, hAK', hSyl, hcore, hres⟩ := hP AK hAK
    set A := AK.1
    set K := AK.2
    have hO2T : pCoreOf 2 K ≤ T := (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl).trans
      inf_le_left
    have hO2n : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 K
    have hAk : ∀ k ∈ K, conjSub k A ≤ Subgroup.centralizer (V : Set G) := by
      intro k hk
      set W := conjSub k A with hWdef
      have hWV : W = conjSub (k * g) V := by rw [hWdef, hAg, conjSub_conjSub]
      set B := W ⊓ pCoreOf 2 K with hB
      have hBk : B = conjSub k (A ⊓ pCoreOf 2 K) := by
        rw [hB, conjSub_inf, conjSub_eq_of_mem_normalizer (hO2n hk)]
      have hBj : B.relIndex W ≤ 2 ^ j := by
        rw [hBk, hWdef, relIndex_conjSub]
        exact hcore
      have hBV : B ≤ Subgroup.centralizer (V : Set G) := by
        refine h2 (k * g) B (le_inf (inf_le_right.trans hO2T) ?_) (hWV ▸ hBj)
        rw [← hWV]
        exact inf_le_left
      have hNW : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (W : Set G) := by
        rw [hWV]
        refine h1g (k * g) B (hWV ▸ inf_le_left) ?_
        rw [← hWV]
        exact lt_of_le_of_lt hBj (Nat.pow_lt_pow_right (by norm_num) hjr)
      have hVN : conjSub 1 V ≤ Subgroup.normalizer (conjSub (k * g) V : Set G) := by
        rw [conjSub_one, ← hWV]
        exact (Subgroup.le_centralizer_iff.1 hBV).trans hNW
      have := hstep (k * g) 1 hVN
      rw [conjSub_one, ← hWV] at this
      exact Subgroup.le_centralizer_iff.1 this
    have hYM : Subgroup.closure (⋃ k ∈ K, (conjSub k A : Set G)) ≤ M := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨k, hk, hxk⟩ := hx
      exact hVM (Subgroup.centralizer_le_normalizer _ (hAk k hk hxk))
    obtain ⟨-, m, hm⟩ := relIndex_twoResidualOf K
    set Y := Subgroup.closure (⋃ k ∈ K, (conjSub k A : Set G)) ⊓ K with hY
    have hYK : Y ≤ K := inf_le_right
    have hresY : twoResidualOf K ≤ Y := le_inf hres (relIndex_twoResidualOf K).1
    have hY2 : Y.relIndex K ∣ 2 ^ m := hm ▸ Subgroup.relIndex_dvd_of_le_left K hresY
    set Z := Y ⊔ ((T : Subgroup G) ⊓ K) with hZ
    have hZK : Z ≤ K := sup_le hYK inf_le_right
    have hZ2 : Z.relIndex K ∣ 2 ^ m := (Subgroup.relIndex_dvd_of_le_left K le_sup_left).trans hY2
    have hZodd : ¬ 2 ∣ Z.relIndex K := by
      intro h
      apply hSyl.2.2
      have := Subgroup.relIndex_dvd_of_le_left K (le_sup_right : (T : Subgroup G) ⊓ K ≤ Z)
      exact h.trans this
    have hZ1 : Z.relIndex K = 1 := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hZ2
      rcases i with _ | i
      · simpa using hi
      · exact absurd (hi ▸ dvd_pow_self 2 (Nat.succ_ne_zero i)) hZodd
    have hKZ : K ≤ Z := Subgroup.relIndex_eq_one.1 hZ1
    exact hKZ.trans (sup_le (inf_le_left.trans hYM) (inf_le_left.trans hTM))
  rw [hgen]
  exact sup_le (hD.trans inf_le_right) (iSup₂_le fun AK hAK => hKM AK hAK)

end CFSG.Quasithin.SteinbergBQ
