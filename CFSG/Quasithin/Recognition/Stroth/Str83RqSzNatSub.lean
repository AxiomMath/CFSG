module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame
import CFSG.Quasithin.Recognition.Stroth.Str83RqSzNatural
import CFSG.Quasithin.Recognition.Stroth.Str83RqSzNatCount
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexSz

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

private theorem szs_eq_of_minimal_admissible {H Z Y M M' : Subgroup G}
    (hM : IsNormalIn H Z M)
    (hmin : ∀ K : Subgroup G, IsNormalIn H Z K → K ≠ ⊥ → K ≤ M → M ≤ K)
    (hM' : IsNormalIn H Z M')
    (hmin' : ∀ K : Subgroup G, IsNormalIn H Z K → K ≠ ⊥ → K ≤ M' → M' ≤ K)
    (hYM : Y ≤ M) (hYM' : Y ≤ M') (hY : Y ≠ ⊥) : M = M' := by
  have hN : IsNormalIn H Z (M ⊓ M') := by
    refine ⟨inf_le_left.trans hM.1, ?_⟩
    intro g hg x hx
    exact Subgroup.mem_inf.mpr
      ⟨hM.2 g hg x (Subgroup.mem_inf.mp hx).1, hM'.2 g hg x (Subgroup.mem_inf.mp hx).2⟩
  have hNne : M ⊓ M' ≠ ⊥ := fun hbot =>
    hY (bot_unique (hbot ▸ le_inf hYM hYM'))
  exact le_antisymm
    ((hmin (M ⊓ M') hN hNne inf_le_left).trans inf_le_right)
    ((hmin' (M ⊓ M') hN hNne inf_le_right).trans inf_le_left)

private theorem szs_conjSub_isNormalIn {H Z M : Subgroup G} {g : G}
    (hGH : g ∈ Subgroup.normalizer (H : Set G))
    (hGZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hM : IsNormalIn H Z M) : IsNormalIn H Z (B6.conjSub g M) := by
  refine ⟨?_, ?_⟩
  · calc B6.conjSub g M ≤ B6.conjSub g Z := (B6.conjSub g).monotone hM.1
      _ = Z := B6.conjSub_eq_self hGZ
  · intro h hh x hx
    rw [B6.mem_conjSub] at hx ⊢
    have hinv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).inv_mem hGH
    have hy : g⁻¹ * h * g ∈ H := by
      simpa using (Subgroup.mem_normalizer_iff.mp hinv h).mp hh
    have hconj : (g⁻¹ * h * g) * (g⁻¹ * x * g) * (g⁻¹ * h * g)⁻¹ ∈ M :=
      hM.2 (g⁻¹ * h * g) hy (g⁻¹ * x * g) hx
    have heq : (g⁻¹ * h * g) * (g⁻¹ * x * g) * (g⁻¹ * h * g)⁻¹ =
        g⁻¹ * (h * x * h⁻¹) * g := by group
    rwa [heq] at hconj

private theorem szs_conjSub_minimal {H Z M : Subgroup G} {g : G}
    (hGH : g ∈ Subgroup.normalizer (H : Set G))
    (hGZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hmin : ∀ K : Subgroup G, IsNormalIn H Z K → K ≠ ⊥ → K ≤ M → M ≤ K) :
    ∀ K : Subgroup G, IsNormalIn H Z K → K ≠ ⊥ →
      K ≤ B6.conjSub g M → B6.conjSub g M ≤ K := by
  intro K hK hKne hKle
  have hinvH : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normalizer (H : Set G)).inv_mem hGH
  have hinvZ : g⁻¹ ∈ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.normalizer (Z : Set G)).inv_mem hGZ
  have hK' : IsNormalIn H Z (B6.conjSub g⁻¹ K) :=
    szs_conjSub_isNormalIn hinvH hinvZ hK
  have hK'ne : B6.conjSub g⁻¹ K ≠ ⊥ := by
    intro hbot
    exact hKne ((B6.conjSub g⁻¹).injective
      (hbot.trans (OrderIso.map_bot (B6.conjSub g⁻¹)).symm))
  have hK'le : B6.conjSub g⁻¹ K ≤ M := by
    have hm := (B6.conjSub g⁻¹).monotone hKle
    rw [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one] at hm
    exact hm
  have hm := (B6.conjSub g).monotone (hmin (B6.conjSub g⁻¹ K) hK' hK'ne hK'le)
  rw [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one] at hm
  exact hm

variable [Finite G]

private theorem szs_exists_minimal_admissible {H Z : Subgroup G}
    (hHZ : H ≤ Subgroup.normalizer (Z : Set G)) (hZ : Z ≠ ⊥) :
    ∃ M : Subgroup G, IsNormalIn H Z M ∧ M ≠ ⊥ ∧
      ∀ K : Subgroup G, IsNormalIn H Z K → K ≠ ⊥ → K ≤ M → M ≤ K := by
  have hZadm : IsNormalIn H Z Z :=
    ⟨le_rfl, fun g hg x hx => (Subgroup.mem_set_normalizer_iff.mp (hHZ hg) x).mp hx⟩
  obtain ⟨M, hM⟩ :=
    (Set.toFinite {M : Subgroup G | IsNormalIn H Z M ∧ M ≠ ⊥}).exists_minimal
      ⟨Z, hZadm, hZ⟩
  exact ⟨M, hM.1.1, hM.1.2, fun K hK hKne hKM => hM.2 ⟨hK, hKne⟩ hKM⟩

private theorem szs_isSzNaturalSection_and_inf_eq
    {H T C Z Y M : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥H ≃* Sz a)) (hT : IsSylowTwoOf T H) (hCH : C ≤ H)
    (hC : ∀ x ∈ T, x * x ∈ pCoreOf 2 H → x ∈ C ⊔ pCoreOf 2 H)
    (hZQ : Z ≤ pCoreOf 2 H) (hquad : ⁅⁅Z, C⁆, C⁆ = ⊥)
    (hcen : Z ⊓ Subgroup.centralizer (H : Set G) = ⊥)
    (hY : Z ⊓ Subgroup.centralizer (T : Set G) ≤ Y)
    (hYc : Nat.card Y ≤ 2 ^ (2 * a + 1))
    (hM : IsNormalIn H Z M) (hMne : M ≠ ⊥)
    (hmin : ∀ K : Subgroup G, IsNormalIn H Z K → K ≠ ⊥ → K ≤ M → M ≤ K) :
    IsSzNaturalSection H M ⊥ a ∧ M ⊓ Subgroup.centralizer (T : Set G) = Y := by
  classical
  have hbotN : IsNormalIn H Z (⊥ : Subgroup G) := by
    refine ⟨bot_le, ?_⟩
    intro g hg x hx
    rw [Subgroup.mem_bot] at hx ⊢
    simp [hx]
  have hstep : IsChiefStep H Z ⊥ M := by
    refine ⟨hM, hbotN, bot_lt_iff_ne_bot.mpr hMne, ?_⟩
    intro K hK _ hKM
    by_cases hKbot : K = ⊥
    · exact Or.inl hKbot
    · exact Or.inr (le_antisymm hKM (hmin K hK hKbot hKM))
  have hnc : ¬ IsCentralStep H ⊥ M := by
    intro hc
    refine hMne (bot_unique ?_)
    rw [← hcen]
    refine le_inf hM.1 ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : y * x * y⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) := hc y hy x hx
    rw [Subgroup.mem_bot] at h1
    calc y * x = (y * x * y⁻¹ * x⁻¹) * (x * y) := by group
      _ = 1 * (x * y) := by rw [h1]
      _ = x * y := by group
  have hquadM : ⁅⁅M, C⁆, C⁆ ≤ ⊥ := by
    rw [← hquad]
    exact Subgroup.commutator_mono (Subgroup.commutator_mono hM.1 le_rfl) le_rfl
  have hnat : IsSzNaturalSection H M ⊥ a :=
    isSzNaturalSection_of_quadratic_of_sz ha hSz hT hCH hC hZQ hstep hquadM hnc
  have hcard := natCard_inf_centralizer_sylow_of_isSzNaturalSection hnat
    (D14.le_normalizer_of_isNormalIn hM) hT
  have hMY : M ⊓ Subgroup.centralizer (T : Set G) ≤ Y :=
    (inf_le_inf hM.1 le_rfl).trans hY
  refine ⟨hnat, Subgroup.eq_of_le_of_card_ge hMY ?_⟩
  rw [hcard]
  exact hYc

theorem exists_isSzNaturalSection_le_of_quadratic_of_sz
    {H T C Z Y : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥H ≃* Sz a)) (hT : IsSylowTwoOf T H) (hCH : C ≤ H)
    (hC : ∀ x ∈ T, x * x ∈ pCoreOf 2 H → x ∈ C ⊔ pCoreOf 2 H)
    (hZQ : Z ≤ pCoreOf 2 H) (hHZ : H ≤ Subgroup.normalizer (Z : Set G)) (hZ : Z ≠ ⊥)
    (hquad : ⁅⁅Z, C⁆, C⁆ = ⊥) (hcen : Z ⊓ Subgroup.centralizer (H : Set G) = ⊥)
    (hY : Z ⊓ Subgroup.centralizer (T : Set G) ≤ Y) (hYc : Nat.card Y ≤ 2 ^ (2 * a + 1)) :
    ∃ U : Subgroup G, U ≤ Z ∧ H ≤ Subgroup.normalizer (U : Set G) ∧
      IsSzNaturalSection H U ⊥ a ∧ U ⊓ Subgroup.centralizer (T : Set G) = Y ∧
      ∀ g ∈ Subgroup.normalizer (H : Set G), g ∈ Subgroup.normalizer (Z : Set G) →
        g ∈ Subgroup.normalizer (U : Set G) := by
  classical
  obtain ⟨M, hM, hMne, hmin⟩ := szs_exists_minimal_admissible hHZ hZ
  obtain ⟨hNat, hMY⟩ :=
    szs_isSzNaturalSection_and_inf_eq ha hSz hT hCH hC hZQ hquad hcen hY hYc hM hMne hmin
  have hYM : Y ≤ M := by rw [← hMY]; exact inf_le_left
  have hcardMT : Nat.card ↥(M ⊓ Subgroup.centralizer (T : Set G)) = 2 ^ (2 * a + 1) :=
    natCard_inf_centralizer_sylow_of_isSzNaturalSection hNat
      (D14.le_normalizer_of_isNormalIn hM) hT
  have hcardY : Nat.card ↥Y = 2 ^ (2 * a + 1) := by rw [← hMY, hcardMT]
  have hYne : Y ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hcardY]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨M, hM.1, D14.le_normalizer_of_isNormalIn hM, hNat, hMY, ?_⟩
  intro g hgH hgZ
  have hMg : IsNormalIn H Z (B6.conjSub g M) := szs_conjSub_isNormalIn hgH hgZ hM
  have hMgne : B6.conjSub g M ≠ ⊥ := by
    intro hbot
    exact hMne ((B6.conjSub g).injective
      (hbot.trans (OrderIso.map_bot (B6.conjSub g)).symm))
  have hminMg := szs_conjSub_minimal hgH hgZ hmin
  obtain ⟨-, hMYMg⟩ :=
    szs_isSzNaturalSection_and_inf_eq ha hSz hT hCH hC hZQ hquad hcen hY hYc
      hMg hMgne hminMg
  have hYMg : Y ≤ B6.conjSub g M := by rw [← hMYMg]; exact inf_le_left
  have hMeq : M = B6.conjSub g M :=
    szs_eq_of_minimal_admissible hM hmin hMg hminMg hYM hYMg hYne
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMeq.symm

theorem le_of_le_centralizer_of_sz
    {L T P : Subgroup G} {a : ℕ} {x : G} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L)
    (hxT : T ≤ Subgroup.centralizer ({x} : Set G))
    (hxQ : pCoreOf 2 L ≤ Subgroup.centralizer ({x} : Set G))
    (hxL : ¬ L ≤ Subgroup.centralizer ({x} : Set G))
    (hP : IsPGroup 2 P) (hPL : P ≤ L) (hPx : P ≤ Subgroup.centralizer ({x} : Set G)) :
    P ≤ T := by
  classical
  let X : Subgroup G := L ⊓ Subgroup.centralizer ({x} : Set G)
  have hTX : T ≤ X := le_inf hT.1 hxT
  have hTsylX : IsSylowTwoOf T X := B6.isSylowTwoOf_mono hT hTX inf_le_left
  have hPX : P ≤ X := le_inf hPL hPx
  obtain ⟨T', hT'sylX, hPT'⟩ := B6.exists_isSylowTwoOf_ge hP hPX
  have hT'sylL : IsSylowTwoOf T' L := by
    obtain ⟨k, hkX, hkT⟩ := B6.isSylowTwoOf_exists_conj hTsylX hT'sylX
    have hkX' : k ∈ L ⊓ Subgroup.centralizer ({x} : Set G) := hkX
    have hkL : k ∈ L := (Subgroup.mem_inf.mp hkX').1
    have h := B6.isSylowTwoOf_conjSub hT k
    rw [B6.conjSub_eq_self (Subgroup.le_normalizer hkL)] at h
    rw [← hkT] at h
    exact h
  by_cases hT'T : T' = T
  · rw [hT'T] at hPT'
    exact hPT'
  · exfalso
    apply hxL
    have hcoverT : ∀ y ∈ T, y * y ∈ pCoreOf 2 L → y ∈ X ⊔ pCoreOf 2 L :=
      fun y hy _ => Subgroup.mem_sup_left (hTX hy)
    have hcoverT' : ∀ y ∈ T', y * y ∈ pCoreOf 2 L → y ∈ X ⊔ pCoreOf 2 L :=
      fun y hy _ => Subgroup.mem_sup_left (hT'sylX.1 hy)
    have hLle : L ≤ X ⊔ pCoreOf 2 L :=
      le_sup_pCoreOf_of_sylow_ne_of_sz ha hSz hT hT'sylL
        (fun heq => hT'T heq.symm) hcoverT hcoverT'
    exact hLle.trans (sup_le inf_le_right hxQ)

end CFSG.Quasithin.Stroth

end
