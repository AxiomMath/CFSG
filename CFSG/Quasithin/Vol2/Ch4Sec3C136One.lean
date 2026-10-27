module

public import CFSG.Quasithin.Vol2.Ch4Sec3L439
public import CFSG.Quasithin.Vol2.Ch4Sec3NatMod
public import CFSG.Quasithin.Vol2.Ch4Sec3SL3

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

section NatSum

variable {L V : Subgroup G} {F : Type} [Field F] {k : ℕ} {α : ↥L →* ↥(StatedSL 3 F)}

theorem mul_comm_of_isSumOfNaturalModulesVia (hN : IsSumOfNaturalModulesVia L V ⊥ α false k)
    {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x := by
  obtain ⟨-, -, β, -, hβker, -⟩ := hN
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  have h := hβinj (show β (⟨x, hx⟩ * ⟨y, hy⟩) = β (⟨y, hy⟩ * ⟨x, hx⟩) by
    rw [map_mul, map_mul, mul_comm])
  exact congrArg Subtype.val h

theorem conj_eq_of_isSumOfNaturalModulesVia (hN : IsSumOfNaturalModulesVia L V ⊥ α false k)
    {a : ↥L} (ha : α a = 1) {u : G} (hu : u ∈ V) : (a : G) * u * (a : G)⁻¹ = u := by
  obtain ⟨hLV, -, β, -, hβker, hβeq⟩ := hN
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  have hmem : (a : G) * u * (a : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hLV a.2) u).mp hu
  have h1 : β ⟨_, hmem⟩ = β ⟨u, hu⟩ := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [hβeq a ⟨u, hu⟩ ⟨_, hmem⟩ rfl i, ha]
    simp [moduleAct]
  exact congrArg Subtype.val (hβinj h1)

theorem map_eq_one_of_mem_centralizer (hN : IsSumOfNaturalModulesVia L V ⊥ α false k) (hk : k ≠ 0)
    {a : ↥L} (ha : (a : G) ∈ Subgroup.centralizer (V : Set G)) : α a = 1 := by
  obtain ⟨-, -, β, hβ, -, hβeq⟩ := hN
  have hfix : ∀ x : Fin 3 → F,
      ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x = x := by
    intro x
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd (fun _ => x))
    have hcomm : (u : G) = a * u * (a : G)⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.mp ha u u.2]
      group
    have h := hβeq a u u hcomm ⟨0, Nat.pos_of_ne_zero hk⟩
    rw [hu] at h
    simpa [moduleAct] using h.symm
  have hM : ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_one, hfix x]
    rfl
  apply Subtype.ext
  apply Units.ext
  exact hM

end NatSum

variable [Finite G]

omit [Finite G] in
theorem le_normalizer_c134Q {G₀ L : Subgroup G} (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) :
    G₀ ≤ Subgroup.normalizer (c134Q G₀ L : Set G) := fun _ hg =>
  mem_normalizer_commutator (le_normalizer_pCoreOf 2 G₀ hg) (hGL hg)

omit [Finite G] in
theorem c134Q_le {G₀ L : Subgroup G} (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) :
    c134Q G₀ L ≤ L :=
  commutator_le_right_of_le_normalizer ((pCoreOf_le 2 G₀).trans hGL)

section Centralizer

variable {G₀ L : Subgroup G} {F : Type} [Field F] {k : ℕ} {α : ↥L →* ↥(StatedSL 3 F)}

theorem centralizer_c134Q_eq {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hcc : c * c ≠ 1)
    (hα : IsModO2Surj L α) (hLG : L ≤ G₀) (hGL : G₀ ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) (hk : k ≠ 0) (hN : IsSumOfNaturalModulesVia L (c134Q G₀ L) ⊥ α false k)
    (hCL : G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    G₀ ⊓ Subgroup.centralizer (c134Q G₀ L : Set G) = c134Q G₀ L := by
  set Q := c134Q G₀ L with hQ
  set V := G₀ ⊓ Subgroup.centralizer (Q : Set G) with hV
  have hOO : pCoreOf 2 L ≤ pCoreOf 2 G₀ :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLG)
      (hGL.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  have hOLQ : ⁅pCoreOf 2 L, L⁆ ≤ Q := Subgroup.commutator_mono hOO le_rfl
  have hGQ : G₀ ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_c134Q hGL
  have hGV : G₀ ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg) (mem_normalizer_centralizer_of_mem (hGQ hg))
  have hQG : Q ≤ G₀ := (c134Q_le hGL).trans hLG
  have hQab : ∀ {x y : G}, x ∈ Q → y ∈ Q → x * y = y * x := fun hx hy =>
    mul_comm_of_isSumOfNaturalModulesVia hN hx hy
  have hVG : V ≤ G₀ := inf_le_left
  have hVL : V ⊓ L ≤ pCoreOf 2 L := by
    rintro x ⟨hxV, hxL⟩
    have h1 : (⟨x, hxL⟩ : ↥L) ∈ α.ker := map_eq_one_of_mem_centralizer hN hk hxV.2
    rw [hα.2] at h1
    exact (mem_pCoreOf_iff' ⟨x, hxL⟩).mpr h1
  have hVLQ : ⁅V, L⁆ ≤ Q := by
    have h1 : ⁅V, L⁆ ≤ pCoreOf 2 L :=
      (le_inf (commutator_le_left_of_le_normalizer (hLG.trans hGV))
        (commutator_le_right_of_le_normalizer (hVG.trans hGL))).trans hVL
    rw [commutator_eq_commutator_commutator_of_perfect' hperf (hVG.trans hGL)]
    exact (Subgroup.commutator_mono h1 le_rfl).trans hOLQ
  have hvK : ∀ v ∈ V, ∀ g ∈ L, v⁻¹ * (g * v * g⁻¹) ∈ Q := by
    intro v hv g hg
    have h1 : ⁅v⁻¹, g⁆ ∈ ⁅V, L⁆ := Subgroup.commutator_mem_commutator (V.inv_mem hv) hg
    have e : ⁅v⁻¹, g⁆ = v⁻¹ * (g * v * g⁻¹) := by
      simp only [commutatorElement_def, inv_inv]; group
    rw [e] at h1
    exact hVLQ h1
  have hvker : ∀ v ∈ V, ∀ a : ↥L, α a = 1 → (a : G) * v = v * a := by
    intro v hv a ha
    have haO : (a : G) ∈ pCoreOf 2 L := by
      have h2 : a ∈ α.ker := ha
      rw [hα.2] at h2
      exact (mem_pCoreOf_iff' a).mpr h2
    have haQ : ∀ q ∈ Q, q * (a : G) = a * q := fun q hq => by
      have h := conj_eq_of_isSumOfNaturalModulesVia hN ha hq
      calc q * (a : G) = (a : G) * q * (a : G)⁻¹ * a := by rw [h]
        _ = a * q := by group
    have hvQ : ∀ q ∈ Q, q * v = v * q := fun q hq => Subgroup.mem_centralizer_iff.mp hv.2 q hq
    obtain ⟨w, hw⟩ : ∃ w, w = v * a * v⁻¹ * (a : G)⁻¹ := ⟨_, rfl⟩
    have hwC : w ∈ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
      obtain ⟨q₁, hq₁Q, hgv⟩ : ∃ q₁ ∈ Q, g * v * g⁻¹ = v * q₁ :=
        ⟨v⁻¹ * (g * v * g⁻¹), hvK v hv g hg, by group⟩
      obtain ⟨q₂, hq₂Q, hga⟩ : ∃ q₂ ∈ Q, g * (a : G) * g⁻¹ = a * q₂ := by
        refine ⟨(a : G)⁻¹ * (g * a * g⁻¹), ?_, by group⟩
        have h1 : ⁅(a : G)⁻¹, g⁆ ∈ ⁅pCoreOf 2 L, L⁆ :=
          Subgroup.commutator_mem_commutator ((pCoreOf 2 L).inv_mem haO) hg
        have e : ⁅(a : G)⁻¹, g⁆ = (a : G)⁻¹ * (g * a * g⁻¹) := by
          simp only [commutatorElement_def, inv_inv]; group
        rw [e] at h1
        exact hOLQ h1
      have h12 : q₁ * q₂ = q₂ * q₁ := hQab hq₁Q hq₂Q
      have h1a : q₁ * (a : G) = a * q₁ := haQ q₁ hq₁Q
      have h2v : q₂ * v⁻¹ = v⁻¹ * q₂ := by
        calc q₂ * v⁻¹ = v⁻¹ * (v * q₂) * v⁻¹ := by group
          _ = v⁻¹ * (q₂ * v) * v⁻¹ := by rw [hvQ q₂ hq₂Q]
          _ = v⁻¹ * q₂ := by group
      have key : g * w * g⁻¹ = w := by
        calc g * w * g⁻¹ =
              (g * v * g⁻¹) * (g * a * g⁻¹) * (g * v * g⁻¹)⁻¹ * (g * a * g⁻¹)⁻¹ := by
              rw [hw]; group
          _ = (v * q₁) * (a * q₂) * (v * q₁)⁻¹ * (a * q₂)⁻¹ := by rw [hgv, hga]
          _ = v * (q₁ * a) * q₂ * q₁⁻¹ * v⁻¹ * q₂⁻¹ * (a : G)⁻¹ := by group
          _ = v * (a * q₁) * q₂ * q₁⁻¹ * v⁻¹ * q₂⁻¹ * (a : G)⁻¹ := by rw [h1a]
          _ = v * a * (q₁ * q₂) * q₁⁻¹ * v⁻¹ * q₂⁻¹ * (a : G)⁻¹ := by group
          _ = v * a * (q₂ * q₁) * q₁⁻¹ * v⁻¹ * q₂⁻¹ * (a : G)⁻¹ := by rw [h12]
          _ = v * a * (q₂ * v⁻¹) * q₂⁻¹ * (a : G)⁻¹ := by group
          _ = v * a * (v⁻¹ * q₂) * q₂⁻¹ * (a : G)⁻¹ := by rw [h2v]
          _ = w := by rw [hw]; group
      calc g * w = g * w * g⁻¹ * g := by group
        _ = w * g := by rw [key]
    have hw1 : w = 1 := by
      have h : w ∈ G₀ ⊓ Subgroup.centralizer (L : Set G) := by
        refine ⟨?_, hwC⟩
        rw [hw]
        exact G₀.mul_mem (G₀.mul_mem (G₀.mul_mem hv.1 (hLG a.2)) (G₀.inv_mem hv.1))
          (G₀.inv_mem (hLG a.2))
      rw [hCL] at h
      exact Subgroup.mem_bot.mp h
    calc (a : G) * v = (v * a * v⁻¹ * (a : G)⁻¹)⁻¹ * (v * a) := by group
      _ = v * a := by rw [← hw, hw1, inv_one, one_mul]
  refine le_antisymm (fun v hv => ?_)
    (fun x hx => ⟨hQG hx, Subgroup.mem_centralizer_iff.mpr fun y hy => hQab hy hx⟩)
  obtain ⟨n₁, hn₁Q, hvn⟩ :=
    exists_mul_mem_centralizer_of_natural hc0 hc1 hcc hα.1 hN (hvker v hv) (hvK v hv)
  have h1 : v * n₁ ∈ G₀ ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨G₀.mul_mem hv.1 (hQG hn₁Q), hvn⟩
  rw [hCL] at h1
  have h3 : v = n₁⁻¹ := eq_inv_of_mul_eq_one_left (Subgroup.mem_bot.mp h1)
  rw [h3]
  exact Q.inv_mem hn₁Q

theorem pCoreOf_eq_c134Q {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hcc : c * c ≠ 1)
    (hα : IsModO2Surj L α) (hLG : L ≤ G₀) (hGL : G₀ ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) (hk : k ≠ 0) (hN : IsSumOfNaturalModulesVia L (c134Q G₀ L) ⊥ α false k)
    (hCL : G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    pCoreOf 2 L = c134Q G₀ L := by
  have hV := centralizer_c134Q_eq hc0 hc1 hcc hα hLG hGL hperf hk hN hCL
  refine le_antisymm (fun u hu => ?_) ?_
  · rw [← hV]
    have huL : u ∈ L := pCoreOf_le 2 L hu
    refine ⟨hLG huL, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have h1 : (⟨u, huL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (mem_pCoreOf_iff' ⟨u, huL⟩).mp hu
    rw [← hα.2] at h1
    have h2 : u * q * u⁻¹ = q := conj_eq_of_isSumOfNaturalModulesVia hN h1 hq
    calc q * u = u * q * u⁻¹ * u := by rw [h2]
      _ = u * q := by group
  · have hQO : c134Q G₀ L ≤ pCoreOf 2 G₀ :=
      commutator_le_left_of_le_normalizer (hLG.trans (le_normalizer_pCoreOf 2 G₀))
    exact le_pCoreOf_of_le_normalizer 2 (c134Q_le hGL) (hLG.trans (le_normalizer_c134Q hGL))
      ((pCoreOf_isPGroup 2 G₀).to_le hQO)

end Centralizer

end CFSG.Quasithin.H13.Ch4
