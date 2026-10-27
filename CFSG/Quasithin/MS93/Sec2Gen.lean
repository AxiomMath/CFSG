module

public import CFSG.Quasithin.Background.Equivariance
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.Quasithin

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_map_conj {K : Subgroup G} {g x : G} :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩

theorem conj_mem_map_conj {K : Subgroup G} {g x : G} (hx : x ∈ K) :
    g * x * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom :=
  ⟨x, hx, by simp⟩

theorem map_conj_map_conj (K : Subgroup G) (g h : G) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      K.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

@[simp] theorem map_conj_one (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp

theorem map_conj_inv_map_conj (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = K := by
  rw [map_conj_map_conj, inv_mul_cancel, map_conj_one]

theorem map_conj_map_conj_inv (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
  rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]

theorem map_conj_le_map_conj_iff {H K : Subgroup G} (g : G) :
    H.map (MulAut.conj g).toMonoidHom ≤ K.map (MulAut.conj g).toMonoidHom ↔ H ≤ K :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

theorem map_conj_le_iff {H K : Subgroup G} (g : G) :
    H.map (MulAut.conj g).toMonoidHom ≤ K ↔ H ≤ K.map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [Subgroup.map_le_iff_le_comap]
  constructor <;> intro h x hx
  · have := h hx
    rw [mem_map_conj, inv_inv]
    simpa using this
  · have := h hx
    rw [mem_map_conj, inv_inv] at this
    simpa using this

theorem map_conj_eq_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : K.map (MulAut.conj g).toMonoidHom = K := by
  ext x
  rw [mem_map_conj]
  have := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g))
  rw [this]
  simp [mul_assoc]

theorem mem_normalizer_of_map_conj_le {K : Subgroup G} {g : G}
    (h₁ : K.map (MulAut.conj g).toMonoidHom ≤ K) (h₂ : K.map (MulAut.conj g⁻¹).toMonoidHom ≤ K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h₁ (conj_mem_map_conj hx)
  · intro hx
    have := h₂ (conj_mem_map_conj (g := g⁻¹) hx)
    simpa [mul_assoc] using this

theorem le_normalizer_of_map_conj_le {Z K : Subgroup G}
    (h : ∀ z ∈ Z, K.map (MulAut.conj z).toMonoidHom ≤ K) :
    Z ≤ Subgroup.normalizer (K : Set G) := fun z hz =>
  mem_normalizer_of_map_conj_le (h z hz) (h z⁻¹ (Z.inv_mem hz))

theorem normalizer_map_conj (K : Subgroup G) (g : G) :
    Subgroup.normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (K : Set G)).map (MulAut.conj g).toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq K (MulAut.conj g)).symm

theorem le_normalizer_map_conj_iff {Z K : Subgroup G} (g : G) :
    Z ≤ Subgroup.normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ↔
      Z.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G) := by
  rw [normalizer_map_conj, map_conj_le_iff, inv_inv]

theorem le_normalizer_sup {Z A B : Subgroup G} (hA : Z ≤ Subgroup.normalizer (A : Set G))
    (hB : Z ≤ Subgroup.normalizer (B : Set G)) : Z ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) :
      Set G) := by
  refine le_normalizer_of_map_conj_le fun z hz => ?_
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hA hz),
    map_conj_eq_of_mem_normalizer (hB hz)]

theorem le_normalizer_iSup_conj (F Z : Subgroup G) :
    F ≤ Subgroup.normalizer
      (((⨆ g ∈ F, Z.map (MulAut.conj g).toMonoidHom : Subgroup G)) : Set G) := by
  refine le_normalizer_of_map_conj_le fun f hf => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun g => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hg => ?_
  rw [map_conj_map_conj]
  exact le_iSup₂_of_le (f * g) (F.mul_mem hf hg) le_rfl

private theorem le_gen_of_not_le {F K Z : Subgroup G} {g : G} (hg : g ∈ F)
    (hgK : ¬ Z.map (MulAut.conj g).toMonoidHom ≤ K) :
    Z.map (MulAut.conj g).toMonoidHom ≤ ⨆ g ∈ F, ⨆ (_ : ¬ Z.map (MulAut.conj g).toMonoidHom ≤ K),
      Z.map (MulAut.conj g).toMonoidHom :=
  le_iSup₂_of_le g hg (iSup_pos (f := fun _ => Z.map (MulAut.conj g).toMonoidHom) hgK).ge

theorem ms110_rel {F K Z T : Subgroup G} (hKF : K ≤ F)
    (hF : F = (⨆ g ∈ F, Z.map (MulAut.conj g).toMonoidHom) ⊔ T)
    (hK : ¬ (⨆ g ∈ F, Z.map (MulAut.conj g).toMonoidHom) ≤ K) :
    F = (⨆ g ∈ F, ⨆ (_ : ¬ Z.map (MulAut.conj g).toMonoidHom ≤ K),
      Z.map (MulAut.conj g).toMonoidHom) ⊔ T := by
  set F₀ := ⨆ g ∈ F, Z.map (MulAut.conj g).toMonoidHom with hF₀
  set F₁ := ⨆ g ∈ F, ⨆ (_ : ¬ Z.map (MulAut.conj g).toMonoidHom ≤ K),
    Z.map (MulAut.conj g).toMonoidHom with hF₁
  have hF₀F : F₀ ≤ F := hF ▸ le_sup_left
  have hTF : T ≤ F := hF ▸ le_sup_right
  have hF₁F₀ : F₁ ≤ F₀ :=
    iSup₂_le fun g hg => iSup_le fun _ => le_iSup₂_of_le g hg le_rfl
  have hKN : K ≤ Subgroup.normalizer (F₁ : Set G) := by
    refine le_normalizer_of_map_conj_le fun k hk => ?_
    rw [hF₁, Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hg => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hgK => ?_
    rw [map_conj_map_conj]
    refine le_gen_of_not_le (F.mul_mem (hKF hk) hg) ?_
    intro hkg
    apply hgK
    have e : (Z.map (MulAut.conj (k * g)).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom =
        Z.map (MulAut.conj g).toMonoidHom := by
      rw [map_conj_map_conj, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [← e]
    calc _ ≤ K.map (MulAut.conj k⁻¹).toMonoidHom := Subgroup.map_mono hkg
      _ = K := map_conj_eq_of_mem_normalizer (Subgroup.inv_mem _ (Subgroup.le_normalizer hk))
  have hF₀N : F₀ ≤ Subgroup.normalizer (F₁ : Set G) := by
    refine iSup₂_le fun g hg => ?_
    by_cases hgK : Z.map (MulAut.conj g).toMonoidHom ≤ K
    · exact hgK.trans hKN
    · exact (le_gen_of_not_le hg hgK).trans Subgroup.le_normalizer
  obtain ⟨g₀, hg₀, hg₀K⟩ : ∃ g₀ ∈ F, ¬ Z.map (MulAut.conj g₀).toMonoidHom ≤ K := by
    by_contra hcon
    push Not at hcon
    exact hK (iSup₂_le hcon)
  have hg₀F₁ : Z.map (MulAut.conj g₀).toMonoidHom ≤ F₁ := le_gen_of_not_le hg₀ hg₀K
  have hTN : T ≤ Subgroup.normalizer (F₀ : Set G) := hTF.trans (le_normalizer_iSup_conj F Z)
  have key : F₀ ≤ F₁ ⊔ T := by
    refine iSup₂_le fun h hh => ?_
    have hmem : h * g₀⁻¹ ∈ ((T ⊔ F₀ : Subgroup G) : Set G) := by
      rw [sup_comm, ← hF]
      exact F.mul_mem hh (F.inv_mem hg₀)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T F₀ hTN] at hmem
    obtain ⟨t, ht, f, hf, htf⟩ := hmem
    have htf' : t * f = h * g₀⁻¹ := htf
    have hh' : h = t * (f * g₀) := by
      rw [← mul_assoc, htf']
      group
    rw [hh', ← map_conj_map_conj, ← map_conj_map_conj]
    have h1 : (Z.map (MulAut.conj g₀).toMonoidHom).map (MulAut.conj f).toMonoidHom ≤ F₁ := by
      calc _ ≤ F₁.map (MulAut.conj f).toMonoidHom := Subgroup.map_mono hg₀F₁
        _ = F₁ := map_conj_eq_of_mem_normalizer (hF₀N hf)
    calc _ ≤ (F₁ ⊔ T).map (MulAut.conj t).toMonoidHom := Subgroup.map_mono (h1.trans le_sup_left)
      _ = F₁ ⊔ T := map_conj_eq_of_mem_normalizer
          (Subgroup.le_normalizer (Subgroup.mem_sup_right ht))
  refine le_antisymm ?_ (sup_le (hF₁F₀.trans hF₀F) hTF)
  calc F = F₀ ⊔ T := hF
    _ ≤ F₁ ⊔ T := sup_le key le_sup_right

theorem normalClosure_eq_iSup_map_conj (Z : Subgroup G) :
    Subgroup.normalClosure (Z : Set G) = ⨆ g : G, Z.map (MulAut.conj g).toMonoidHom := by
  have e : (⨆ g : G, Z.map (MulAut.conj g).toMonoidHom) =
      ⨆ g ∈ (⊤ : Subgroup G), Z.map (MulAut.conj g).toMonoidHom := by
    simp
  apply le_antisymm
  · have : (⨆ g : G, Z.map (MulAut.conj g).toMonoidHom).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hN := le_normalizer_iSup_conj (⊤ : Subgroup G) Z (Subgroup.mem_top g)
      rw [← e] at hN
      exact (Subgroup.mem_normalizer_iff.mp hN n).mp hn
    refine Subgroup.normalClosure_le_normal fun z hz => ?_
    exact Subgroup.mem_iSup_of_mem 1 (by simpa using hz)
  · refine iSup_le fun g => ?_
    rintro _ ⟨z, hz, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance z (Subgroup.subset_normalClosure hz) g

theorem exists_conj_not_le_normalizer {F Z T X₁ X₂ : Subgroup G}
    (hF : F = (⨆ g ∈ F, Z.map (MulAut.conj g).toMonoidHom) ⊔ T)
    (h₁ : T ≤ Subgroup.normalizer (X₁ : Set G)) (h₁' : ¬ F ≤ Subgroup.normalizer (X₁ : Set G))
    (h₂ : T ≤ Subgroup.normalizer (X₂ : Set G)) (h₂' : ¬ F ≤ Subgroup.normalizer (X₂ : Set G)) :
    ∃ g ∈ F,
      ¬ Z ≤ Subgroup.normalizer ((X₁.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ∧
      ¬ Z ≤ Subgroup.normalizer ((X₂.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  set K := F ⊓ Subgroup.normalizer (X₁ : Set G)
  have hZF : ∀ g ∈ F, Z.map (MulAut.conj g).toMonoidHom ≤ F := fun g hg =>
    (le_iSup₂_of_le g hg le_rfl).trans (hF ▸ le_sup_left)
  have hK : ¬ (⨆ g ∈ F, Z.map (MulAut.conj g).toMonoidHom) ≤ K := by
    intro hle
    apply h₁'
    rw [hF]
    exact sup_le (hle.trans inf_le_right) h₁
  have hgen := ms110_rel inf_le_left hF hK
  obtain ⟨g, hg, hgK, hgX₂⟩ : ∃ g ∈ F, ¬ Z.map (MulAut.conj g).toMonoidHom ≤ K ∧
      ¬ Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (X₂ : Set G) := by
    by_contra hcon
    push Not at hcon
    apply h₂'
    rw [hgen]
    exact sup_le (iSup₂_le fun g hg => iSup_le fun hgK => hcon g hg hgK) h₂
  have hgX₁ : ¬ Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (X₁ : Set G) :=
    fun h => hgK (le_inf (hZF g hg) h)
  refine ⟨g⁻¹, F.inv_mem hg, ?_, ?_⟩
  · rw [le_normalizer_map_conj_iff, inv_inv]
    exact hgX₁
  · rw [le_normalizer_map_conj_iff, inv_inv]
    exact hgX₂

theorem eq_of_le_sup_commutator {P W Y Q : Subgroup G} (hP : Group.IsNilpotent P)
    (hW : W ≤ P) (hY : Y ≤ P) (hQ : Q ≤ P) (hQW : Q ≤ Subgroup.normalizer (W : Set G))
    (hWY : W ≤ Y) (h : Y ≤ W ⊔ ⁅Y, Q⁆) : Y = W := by
  have hN : ∀ n, P ≤ Subgroup.normalizer ((P.lowerCentralSeries n : Subgroup G) : Set G) :=
    P.self_le_normalizer_lowerCentralSeries
  have step : ∀ n, Y ≤ W ⊔ P.lowerCentralSeries n := by
    intro n
    induction n with
    | zero => rw [Subgroup.lowerCentralSeries_zero]; exact hY.trans le_sup_right
    | succ n ih =>
      refine h.trans (sup_le le_sup_left ?_)
      rw [Subgroup.commutator_le]
      intro y hy q hq
      have hy' : y ∈ ((W ⊔ P.lowerCentralSeries n : Subgroup G) : Set G) := ih hy
      rw [Subgroup.coe_mul_of_left_le_normalizer_right W _ (hW.trans (hN n))] at hy'
      obtain ⟨w, hw, l, hl, hwl⟩ := hy'
      have hwl' : w * l = y := hwl
      rw [← hwl', commutatorElement_mul_left_eq_conj_mul]
      refine Subgroup.mul_mem _ ?_ ?_
      · refine Subgroup.mem_sup_right ?_
        have hc : ⁅l, q⁆ ∈ P.lowerCentralSeries (n + 1) := by
          rw [Subgroup.lowerCentralSeries_succ]
          exact Subgroup.commutator_mem_commutator hl (hQ hq)
        exact (Subgroup.mem_normalizer_iff.mp (hN (n + 1) (hW hw)) _).mp hc
      · refine Subgroup.mem_sup_left ?_
        have h1 : q * w⁻¹ * q⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hQW hq) _).mp (W.inv_mem hw)
        have h2 : ⁅w, q⁆ = w * (q * w⁻¹ * q⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [h2]
        exact W.mul_mem hw h1
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries P).mp hP
  refine le_antisymm ?_ hWY
  have := step n
  rwa [hn, sup_bot_eq] at this

theorem isElemAbelian_of_le {p : ℕ} {E F : Subgroup G} (hF : IsElemAbelian p F) (hEF : E ≤ F) :
    IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hF hEF

theorem isElemAbelian_sup {H K : Subgroup G} (hH : IsElemAbelian 2 H) (hK : IsElemAbelian 2 K)
    (hHK : H ≤ Subgroup.centralizer (K : Set G)) : IsElemAbelian 2 (H ⊔ K) := by
  unfold IsElemAbelian at *
  rw [isMulCommutative_subgroup_iff] at *
  have hHN : H ≤ Subgroup.normalizer (K : Set G) :=
    hHK.trans (Subgroup.centralizer_le_normalizer _)
  have hdec : ∀ x ∈ H ⊔ K, ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
    intro x hx
    have hx' : x ∈ ((H ⊔ K : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H K hHN] at hx'
    obtain ⟨h, hh, k, hk, hhk⟩ := hx'
    exact ⟨h, hh, k, hk, hhk⟩
  have hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h := fun h hh k hk =>
    (Subgroup.mem_centralizer_iff.mp (hHK hh) k hk).symm
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := hdec x hx
    obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := hdec y hy
    calc h₁ * k₁ * (h₂ * k₂) = (h₁ * h₂) * (k₁ * k₂) := by
          rw [mul_assoc, ← mul_assoc k₁, ← hcomm h₂ hh₂ k₁ hk₁]; group
      _ = (h₂ * h₁) * (k₂ * k₁) := by rw [hH.1 h₁ hh₁ h₂ hh₂, hK.1 k₁ hk₁ k₂ hk₂]
      _ = h₂ * k₂ * (h₁ * k₁) := by
          rw [mul_assoc, ← mul_assoc h₁, hcomm h₁ hh₁ k₂ hk₂]; group
  · intro x hx
    obtain ⟨h, hh, k, hk, rfl⟩ := hdec x hx
    calc (h * k) ^ 2 = h * (k * h) * k := by rw [sq]; group
      _ = h ^ 2 * k ^ 2 := by rw [← hcomm h hh k hk, sq, sq]; group
      _ = 1 := by rw [hH.2 h hh, hK.2 k hk, one_mul]

end CFSG.Quasithin.MS93
