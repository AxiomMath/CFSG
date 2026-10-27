module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFCount

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

theorem alt5_exists_inverter : ∀ ρ : alternatingGroup (Fin 5), ρ ^ 3 = 1 →
    ∃ w : alternatingGroup (Fin 5), w * w = 1 ∧ w * ρ * w⁻¹ = ρ⁻¹ := by
  decide +kernel

theorem alt5_inverter_not_mem_normalizer {T : Subgroup (alternatingGroup (Fin 5))}
    (hT : Nat.card T = 4) {ρ w : alternatingGroup (Fin 5)}
    (hρT : ρ ∈ Subgroup.normalizer (T : Set (alternatingGroup (Fin 5)))) (hρ3 : ρ ^ 3 = 1)
    (hρ1 : ρ ≠ 1) (hw2 : w * w = 1) (hwρ : w * ρ * w⁻¹ = ρ⁻¹) :
    w ∉ Subgroup.normalizer (T : Set (alternatingGroup (Fin 5))) := by
  intro hwN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT]; norm_num)
  have hidx : ¬ 2 ∣ T.index := by
    intro h2
    have h := Subgroup.card_mul_index (H := T)
    rw [hT, natCard_alt5] at h
    omega
  let Q : Sylow 2 (alternatingGroup (Fin 5)) := hT2.toSylow hidx
  have hw2' : w ^ 2 = 1 := by rw [pow_two]; exact hw2
  have hW : IsPGroup 2 (Subgroup.zpowers w) := by
    have hc : Nat.card (Subgroup.zpowers w) = orderOf w := Nat.card_zpowers w
    have hd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw2'
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [hc, h]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [hc, h]; norm_num)
  have hwmem : w ∈ Subgroup.zpowers w ⊓
      Subgroup.normalizer (Q : Set (alternatingGroup (Fin 5))) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers w, hwN⟩
  rw [hW.inf_normalizer_sylow Q] at hwmem
  have hwT : w ∈ T := hwmem.2
  have hc : w * ρ * w⁻¹ * ρ⁻¹ ∈ T := by
    have h1 : ρ * w⁻¹ * ρ⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hρT _).mp (T.inv_mem hwT)
    have : w * ρ * w⁻¹ * ρ⁻¹ = w * (ρ * w⁻¹ * ρ⁻¹) := by group
    rw [this]
    exact T.mul_mem hwT h1
  rw [hwρ] at hc
  have hρ' : ρ ∈ T := by
    have : ρ⁻¹ * ρ⁻¹ = ρ := by
      have h3 : ρ ^ 3 = 1 := hρ3
      calc ρ⁻¹ * ρ⁻¹ = ρ⁻¹ * ρ⁻¹ * ρ ^ 3 := by rw [h3, mul_one]
        _ = ρ := by group
    rwa [this] at hc
  have h4 : ρ ^ 4 = 1 := by
    have := pow_card_eq_one' (G := ↥T) (x := ⟨ρ, hρ'⟩)
    rw [hT] at this
    simpa using congrArg Subtype.val this
  apply hρ1
  calc ρ = ρ ^ 4 * (ρ ^ 3)⁻¹ := by group
    _ = 1 := by rw [h4, hρ3]; group

theorem exists_central_of_acts_trivially {P : Type*} [Group P]
    (φ : P →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    {A K Ŝ : Subgroup P} [A.Normal] (hA1 : A ≠ ⊥)
    (hAQ : ∀ a ∈ A, ∀ q ∈ φ.ker, a * q = q * a)
    {r : P} (hr3 : r ^ 3 = 1) (hr1 : φ r ≠ 1)
    {T : Subgroup (alternatingGroup (Fin 5))} (hT : Nat.card T = 4)
    (hrT : φ r ∈ Subgroup.normalizer (T : Set (alternatingGroup (Fin 5))))
    (hS : ∀ k ∈ T, ∃ s ∈ Ŝ, φ s = k)
    (hiii : ∀ a ∈ A, ⁅a, r⁆ ∈ K)
    (hiv : ∀ x ∈ A, x ∈ K → ∀ s ∈ Ŝ, x * s = s * x) :
    ∃ m ∈ A, m ≠ 1 ∧ ∀ g : P, m * g = g * m := by
  by_contra hcon
  push Not at hcon
  have hconj : ∀ y ∈ A, ∀ g : P, g * y * g⁻¹ ∈ A := fun y hy g =>
    Subgroup.Normal.conj_mem inferInstance y hy g
  have hcomA : ∀ a ∈ A, ⁅a, r⁆ ∈ A := by
    intro a ha
    have : ⁅a, r⁆ = a * (r * a⁻¹ * r⁻¹) := by simp [commutatorElement_def]; group
    rw [this]
    exact A.mul_mem ha (hconj a⁻¹ (A.inv_mem ha) r)
  have hρ3 : φ r ^ 3 = 1 := by rw [← map_pow, hr3, map_one]
  obtain ⟨w0, hw02, hw0ρ⟩ := alt5_exists_inverter (φ r) hρ3
  have hw0N := alt5_inverter_not_mem_normalizer hT hrT hρ3 hr1 hw02 hw0ρ
  obtain ⟨w, hw⟩ := hφ w0
  have hq : r * (w * r * w⁻¹) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hw, hw0ρ]
    group
  set q := r * (w * r * w⁻¹) with hqdef
  have hr1' : w * r * w⁻¹ = r⁻¹ * q := by rw [hqdef]; group
  set g₂ : P := r * w with hg₂
  have hg₂N : φ g₂ ∉ Subgroup.normalizer (T : Set (alternatingGroup (Fin 5))) := by
    intro h
    apply hw0N
    have : w0 = (φ r)⁻¹ * φ g₂ := by rw [hg₂, map_mul, hw]; group
    rw [this]
    exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem hrT) h
  set T₂ : Subgroup (alternatingGroup (Fin 5)) :=
    T.map (MulAut.conj (φ g₂)).toMonoidHom with hT₂
  have hT₂4 : Nat.card T₂ = 4 := by
    rw [hT₂, Subgroup.card_map_of_injective (MulAut.conj (φ g₂)).injective, hT]
  have hT₂ne : T₂ ≠ T := map_conj_ne T (φ g₂) hg₂N
  have hsup : T ⊔ T₂ = ⊤ := klein_sup_eq_top hT hT₂4 hT₂ne.symm
  have key : ∀ a ∈ A, ∀ g : P, ⁅a, r⁆ * g = g * ⁅a, r⁆ := by
    intro a ha
    set e : P := ⁅a, r⁆ with hedef
    have heA : e ∈ A := hcomA a ha
    set H : Subgroup P := Subgroup.centralizer ({e} : Set P) with hH
    have hmemH : ∀ y : P, y ∈ H ↔ e * y = y * e := by
      intro y
      rw [hH, Subgroup.mem_centralizer_singleton_iff]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    have hkerH : φ.ker ≤ H := fun y hy => (hmemH y).mpr (hAQ e heA y hy)
    have hSH : ∀ s ∈ Ŝ, s ∈ H := fun s hs => (hmemH s).mpr (hiv e heA (hiii a ha) s hs)
    have hg₂H : ∀ s ∈ Ŝ, g₂ * s * g₂⁻¹ ∈ H := by
      intro s hs
      have ha₁A : w⁻¹ * a * w ∈ A := by simpa using hconj a ha w⁻¹
      set a₁ : P := w⁻¹ * a * w with ha₁
      set e₁ : P := ⁅a₁, r⁆ with he₁
      have hc₁ : e₁ * s = s * e₁ := hiv e₁ (hcomA a₁ ha₁A) (hiii a₁ ha₁A) s hs
      have id1 : w * e₁ * w⁻¹ = ⁅a, w * r * w⁻¹⁆ := by
        simp only [he₁, ha₁, commutatorElement_def]; group
      have hq' : a * q = q * a := hAQ a ha q hq
      have hq'' : q * a⁻¹ * q⁻¹ = a⁻¹ := by
        have h := hAQ a⁻¹ (A.inv_mem ha) q hq
        rw [mul_inv_eq_iff_eq_mul]
        exact h.symm
      have id2 : ⁅a, w * r * w⁻¹⁆ = r⁻¹ * e⁻¹ * r := by
        rw [hr1', hedef]
        simp only [commutatorElement_def]
        calc a * (r⁻¹ * q) * a⁻¹ * (r⁻¹ * q)⁻¹
            = a * r⁻¹ * (q * a⁻¹ * q⁻¹) * r := by group
          _ = a * r⁻¹ * a⁻¹ * r := by rw [hq'']
          _ = r⁻¹ * (a * r * a⁻¹ * r⁻¹)⁻¹ * r := by group
      have hX : Commute (r⁻¹ * e⁻¹ * r) (w * s * w⁻¹) := by
        have : Commute (w * e₁ * w⁻¹) (w * s * w⁻¹) :=
          (Commute.map (show Commute e₁ s from hc₁) (MulAut.conj w).toMonoidHom)
        rw [id1, id2] at this
        exact this
      have hY := (hX.inv_left).map (MulAut.conj r).toMonoidHom
      have : e * (g₂ * s * g₂⁻¹) = (g₂ * s * g₂⁻¹) * e := by
        have h2 : Commute (r * (r⁻¹ * e⁻¹ * r)⁻¹ * r⁻¹) (r * (w * s * w⁻¹) * r⁻¹) := by
          simpa [MulAut.conj_apply] using hY
        have e3 : r * (r⁻¹ * e⁻¹ * r)⁻¹ * r⁻¹ = e := by group
        have e4 : r * (w * s * w⁻¹) * r⁻¹ = g₂ * s * g₂⁻¹ := by rw [hg₂]; group
        rw [e3, e4] at h2
        exact h2
      exact (hmemH _).mpr this
    have hHtop : ∀ g : P, g ∈ H := by
      intro g
      have hmem : φ g ∈ T ⊔ T₂ := by rw [hsup]; trivial
      have hle : T ⊔ T₂ ≤ H.map φ := by
        refine sup_le ?_ ?_
        · intro k hk
          obtain ⟨s, hs, rfl⟩ := hS k hk
          exact ⟨s, hSH s hs, rfl⟩
        · rintro _ ⟨k0, hk0, rfl⟩
          obtain ⟨s, hs, rfl⟩ := hS k0 hk0
          exact ⟨g₂ * s * g₂⁻¹, hg₂H s hs, by simp [map_mul, map_inv]⟩
      obtain ⟨h, hh, hφh⟩ := hle hmem
      have hk : g * h⁻¹ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφh]; group
      have : g = (g * h⁻¹) * h := by group
      rw [this]
      exact H.mul_mem (hkerH hk) hh
    intro g
    exact (hmemH g).mp (hHtop g)
  have hrcomm : ∀ a ∈ A, ⁅a, r⁆ = 1 := by
    intro a ha
    by_contra hne
    obtain ⟨g, hg⟩ := hcon _ (hcomA a ha) hne
    exact hg (key a ha g)
  set C : Subgroup P := Subgroup.centralizer (A : Set P) with hC
  have hmemC : ∀ y : P, y ∈ C ↔ ∀ a ∈ A, a * y = y * a := by
    intro y
    rw [hC, Subgroup.mem_centralizer_iff]
    exact ⟨fun h a ha => h a ha, fun h a ha => h a ha⟩
  have hCn : C.Normal := ⟨fun n hn g => by
    rw [hmemC] at hn ⊢
    intro a ha
    have h1 := hn (g⁻¹ * a * g) (by simpa using hconj a ha g⁻¹)
    calc a * (g * n * g⁻¹) = g * ((g⁻¹ * a * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = (g * n * g⁻¹) * a := by group⟩
  have hkerC : φ.ker ≤ C := fun y hy => (hmemC y).mpr (fun a ha => hAQ a ha y hy)
  have hrC : r ∈ C := (hmemC r).mpr (fun a ha => by
    have := hrcomm a ha
    simp only [commutatorElement_def] at this
    calc a * r = (a * r * a⁻¹ * r⁻¹) * r * a := by group
      _ = r * a := by rw [this]; group)
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : (C.map φ).Normal := Subgroup.Normal.map hCn φ hφ
  have hCtop : C.map φ = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (C.map φ) with h | h
    · exfalso
      apply hr1
      have : φ r ∈ C.map φ := ⟨r, hrC, rfl⟩
      rw [h] at this
      simpa using this
    · exact h
  have hCall : ∀ g : P, g ∈ C := by
    intro g
    have hmem : φ g ∈ C.map φ := by rw [hCtop]; trivial
    obtain ⟨h, hh, hφh⟩ := hmem
    have hk : g * h⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφh]; group
    have : g = (g * h⁻¹) * h := by group
    rw [this]
    exact C.mul_mem (hkerC hk) hh
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
  obtain ⟨g, hg⟩ := hcon a ha (fun h => ha1 (Subtype.ext h))
  exact hg ((hmemC g).mp (hCall g) a ha)

end CFSG.Quasithin.Kleidman.F204
