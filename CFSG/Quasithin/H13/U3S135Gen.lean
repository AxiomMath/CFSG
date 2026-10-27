module

public import CFSG.Quasithin.H13.L32NModule
public import CFSG.Quasithin.H13.L32NInputs
public import CFSG.Quasithin.H13.A6Assembly
public import CFSG.Quasithin.H13.U3FrameProducer

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem not_centralizer_le_of_conj {M : Subgroup G} {v w g : G} (hg : g ∈ M)
    (hgv : g * v * g⁻¹ = w) (h : ¬ centralizer ({v} : Set G) ≤ M) :
    ¬ centralizer ({w} : Set G) ≤ M := by
  intro hw
  apply h
  intro x hx
  rw [mem_centralizer_singleton_iff] at hx
  have h1 : g * x * g⁻¹ ∈ centralizer ({w} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hgv]
    calc g * x * g⁻¹ * (g * v * g⁻¹) = g * (x * v) * g⁻¹ := by group
      _ = g * (v * x) * g⁻¹ := by rw [hx]
      _ = g * v * g⁻¹ * (g * x * g⁻¹) := by group
  have h2 := mul_mem (mul_mem (inv_mem hg) (hw h1)) hg
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h2

theorem centralizer_le_normalizer_zpowers (v : G) :
    centralizer ({v} : Set G) ≤ normalizer ((zpowers v : Subgroup G) : Set G) := by
  intro x hx
  apply centralizer_le_normalizer
  rw [zpowers_eq_closure, centralizer_closure]
  exact hx

theorem eq_one_or_eq_of_mem_zpowers {v x : G} (hv : v ^ 2 = 1) (hx : x ∈ zpowers v) :
    x = 1 ∨ x = v := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have h2 : v ^ (2 : ℤ) = 1 := by simpa using hv
  rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
  · exact Or.inl (zpow_zero v)
  · exact Or.inr (zpow_one v)

variable [Finite G]

theorem hyp1223_of_fsu {T L V : Subgroup G} (hH : QTH13 G T L)
    (hTL : T ≤ normalizer (L : Set G)) (hmax : quasithinIsMaximalLocal T L) (hfsu : FSU G T L V)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) : Hyp1223 G T L V where
  simple := hH.simple
  nonabelian := hH.nonabelian
  qtke := hH.qtke
  sylow := hH.sylow
  notAlt := fun hA => hH.not_excluded (Hyp14310One.qt13Excluded_of_alt hA)
  maximal := hmax
  faithful := hH.faithful
  quasisimple := hfsu.quasisimple
  normalizes := hTL
  irrPlus := hV

theorem hyp1223_of (h1332 : Stmt13_3_2) {T L V : Subgroup G} (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) : Hyp1223 G T L V := by
  obtain ⟨-, ⟨hTL, hmax, -, -⟩, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, hfsu, -⟩ := hall V hV
  exact hyp1223_of_fsu hH hTL hmax hfsu hV

theorem exists_centralizer_not_le (h12213 : Stmt12_2_13) {T L V : Subgroup G}
    (hH : QTH13 G T L) (hyp : Hyp1223 G T L V) :
    ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  rcases (stmt12_2_13_iff.mp h12213) G T L V hyp with h | ⟨n, hn, -, hlie⟩ | ⟨-, hA9⟩ |
      ⟨-, hM24⟩
  · exact h
  · exfalso
    apply hH.not_excluded
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl (Or.inl hlie))
    · exact Or.inr (Or.inl (Or.inr hlie))
  · exact absurd (Or.inr (Or.inr (Or.inl hA9))) hH.not_excluded
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM24)))))) hH.not_excluded

theorem normalizer_le_of_uniq {T L X : Subgroup G} (hX : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    (hLT : L ⊔ T ≤ normalizer (X : Set G))
    (huniq : ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → L ⊔ T ≤ M →
      M = normalizer (L : Set G)) :
    normalizer (X : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨M', hM', hle⟩ :=
    exists_maxTwoLocal_ge (⟨X, hX, hX2, rfl⟩ : IsTwoLocal (normalizer (X : Set G)))
  have := huniq M' hM' (hLT.trans hle)
  exact this ▸ hle

theorem sq_of_irr {T L V : Subgroup G} (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    {v : G} (hv : v ∈ V) : v ^ 2 = 1 :=
  (mem_reducedAggregate (hV.1 hv)).2.2

omit [Finite G] in
theorem not_le_centralizer_of_irr {T L V : Subgroup G}
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) :
    ¬ L ≤ centralizer (V : Set G) := by
  intro hle
  have h1 : ⁅V, L⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hle)
  exact hV.2.1 (hV.2.2.2.1.symm.trans h1)

theorem not_five_dvd_card_autOn_U3 {L V : Subgroup G}
    (hu : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hLV : L ≤ normalizer (V : Set G)) : ¬ 5 ∣ Nat.card (autOn L V) := by
  intro h5
  rw [card_autOn_eq_relIndex hLV] at h5
  have hdvd := relIndex_dvd_card (L ⊓ centralizer (V : Set G)) L
  have hL : Nat.card ↥L = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) * Nat.card (CFSG.pCore 2 ↥L) :=
    card_eq_card_quotient_mul_card_subgroup _
  rw [card_of_lieModel_PSU_three_three hu] at hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  rw [hk] at hL
  have h5L : 5 ∣ 6048 * 2 ^ k := hL ▸ h5.trans hdvd
  have hp5 : Nat.Prime 5 := by norm_num
  rcases (Nat.Prime.dvd_mul hp5).mp h5L with h | h
  · norm_num at h
  · have := Nat.Prime.dvd_of_dvd_pow hp5 h
    norm_num at this

omit [Finite G] in
theorem a6CentralQuotient_of_mulEquiv {L : Subgroup G}
    (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(alternatingGroup (Fin 6))) : A6.A6CentralQuotient L := by
  have hZ : center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : e z ∈ center ↥(alternatingGroup (Fin 6)) :=
      A6.map_center_le_center e.toMonoidHom e.surjective ⟨z, hz, rfl⟩
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at h1
    rw [mem_bot]
    exact e.injective (h1.trans (map_one e).symm)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩

theorem a5Quot_of_autOn {L V : Subgroup G} (hLV : L ≤ normalizer (V : Set G))
    (h5 : QT13Five (↥L ⧸ CFSG.pCore 2 ↥L))
    (hA5 : Nonempty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5)))) :
    quasithinO2QuotientIso L (alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := hA5
  obtain ⟨φ, hφ⟩ := A6.exists_surjective_autOn hLV
  have h5L : 5 ∣ Nat.card (autOn L V) := by
    rw [Nat.card_congr e.toEquiv, A6.card_alt5]
    norm_num
  rcases h5 with he5 | h32 | he6 | hhat | hu
  · exact (quasithinO2QuotientIso_iff L _).2 he5
  · exact absurd h5L (not_five_dvd_card_autOn h32 hLV)
  · obtain ⟨e6⟩ := he6
    exact (A6.false_of_surjective_alt5 (a6CentralQuotient_of_mulEquiv e6)
      (e.toMonoidHom.comp φ) (e.surjective.comp hφ)).elim
  · exact (A6.false_of_surjective_alt5 hhat.2.2 (e.toMonoidHom.comp φ)
      (e.surjective.comp hφ)).elim
  · exact absurd h5L (not_five_dvd_card_autOn_U3 hu hLV)

end CFSG.Quasithin.H13.U3
