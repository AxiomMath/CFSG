module

public import CFSG.RankThree.PartOne.S12.Sec158Defs
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S12.Sec12A
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.Sec15FA

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

namespace Sec158

theorem conjBy_mem_thetaCompZeroE {p : ℕ} (hp : p.Prime) {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) {X : Subgroup G} (hX : X ∈ thetaCompZeroE p E) :
    conjBy w X ∈ thetaCompZeroE p E := by
  obtain ⟨B, hB, hXB⟩ := hX
  exact ⟨conjBy w B, conjBy_mem_admissibleTriples hw hB, conjBy_mem_sectionTenZero hp w hXB⟩

omit [Finite G] in
theorem zeroLayer_le_centralizer (p : ℕ) (E : Subgroup G) (b : G) :
    zeroLayer p E b ≤ Subgroup.centralizer ({b} : Set G) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨Y, -, hY, hx⟩
  exact (mem_thetaComponentsAt_iff.1 hY).1 hx

theorem zeroLayer_le_lieGenerated (h156 : KF156') {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152 p E A (lieGenerated p E)) (b : G) : zeroLayer p E b ≤ lieGenerated p E := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨Y, hY0, -, hx⟩
  exact h156 G p A c L E h15 hF hout Y hY0 hx

theorem zeroLayer_conj_le {p : ℕ} (hp : p.Prime) {E : Subgroup G} {b z : G}
    (hz : z ∈ Subgroup.centralizer ({b} : Set G))
    (hL0 : ∀ Y ∈ thetaCompZeroE p E, Y ∈ thetaComponentsAt p b → conjBy z Y ∈ thetaCompZeroE p E) :
    conjBy z (zeroLayer p E b) ≤ zeroLayer p E b := by
  unfold conjBy zeroLayer
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨Y, hY0, hYb, hx⟩, rfl⟩
  refine ⟨conjBy z Y, hL0 Y hY0 hYb, ?_, Subgroup.mem_map_of_mem _ hx⟩
  have hzb : z * b * z⁻¹ = b := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 hz
    calc z * b * z⁻¹ = b * z * z⁻¹ := by rw [← h]
      _ = b := by group
  have := conjBy_mem_thetaComponentsAt hp z b hYb
  rwa [hzb] at this

theorem centralizer_le_normalizer_zeroLayer {p : ℕ} (hp : p.Prime) {E : Subgroup G} {b : G}
    (hL0 : ∀ z ∈ Subgroup.centralizer ({b} : Set G), ∀ Y ∈ thetaCompZeroE p E,
      Y ∈ thetaComponentsAt p b → conjBy z Y ∈ thetaCompZeroE p E) :
    Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (zeroLayer p E b : Set G) := by
  intro z hz
  have h1 := zeroLayer_conj_le hp hz (hL0 z hz)
  have hz' : z⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
    (Subgroup.centralizer ({b} : Set G)).inv_mem hz
  have h2 := zeroLayer_conj_le hp hz' (hL0 z⁻¹ hz')
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h1 (Subgroup.mem_map_of_mem _ hx)
  · intro hx
    have := h2 (Subgroup.mem_map_of_mem _ hx)
    simpa [mul_assoc] using this

theorem zeroLayer_conjBy {p : ℕ} (hp : p.Prime) {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) (b : G) :
    zeroLayer p E (w * b * w⁻¹) = conjBy w (zeroLayer p E b) := by
  have key : ∀ w : G, w ∈ Subgroup.normalizer (E : Set G) → ∀ b : G,
      conjBy w (zeroLayer p E b) ≤ zeroLayer p E (w * b * w⁻¹) := by
    intro w hw b
    unfold conjBy zeroLayer
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨Y, hY0, hYb, hx⟩, rfl⟩
    exact ⟨conjBy w Y, conjBy_mem_thetaCompZeroE hp hw hY0, conjBy_mem_thetaComponentsAt hp w b hYb,
      Subgroup.mem_map_of_mem _ hx⟩
  apply le_antisymm
  · have h := key w⁻¹ ((Subgroup.normalizer (E : Set G)).inv_mem hw) (w * b * w⁻¹)
    have hb : w⁻¹ * (w * b * w⁻¹) * w⁻¹⁻¹ = b := by group
    rw [hb] at h
    calc zeroLayer p E (w * b * w⁻¹)
        = conjBy w (conjBy w⁻¹ (zeroLayer p E (w * b * w⁻¹))) :=
          (Equivariance.conjBy_conjBy_inv w _).symm
      _ ≤ conjBy w (zeroLayer p E b) := Subgroup.map_mono h
  · exact key w hw b

omit [Finite G] in
theorem mem_centralizer_sup {S T : Subgroup G} {c : G} :
    c ∈ Subgroup.centralizer ((S ⊔ T : Subgroup G) : Set G) ↔
      c ∈ Subgroup.centralizer (S : Set G) ∧ c ∈ Subgroup.centralizer (T : Set G) := by
  constructor
  · intro h
    exact ⟨Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) h,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right) h⟩
  · rintro ⟨hS, hT⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction (p := fun x _ => x * c = c * x) ?_ ?_ ?_ ?_ hx
    · rintro x (hx | hx)
      · exact Subgroup.mem_centralizer_iff.1 hS x hx
      · exact Subgroup.mem_centralizer_iff.1 hT x hx
    · simp
    · intro x y _ _ hx hy
      calc x * y * c = x * (y * c) := by group
        _ = x * (c * y) := by rw [hy]
        _ = (x * c) * y := by group
        _ = (c * x) * y := by rw [hx]
        _ = c * (x * y) := by group
    · intro x _ hx
      have : c * x⁻¹ = x⁻¹ * c := by
        calc c * x⁻¹ = x⁻¹ * (x * c) * x⁻¹ := by group
          _ = x⁻¹ * (c * x) * x⁻¹ := by rw [hx]
          _ = x⁻¹ * c := by group
      exact this.symm

omit [Finite G] in
theorem mem_normalizer_centralizer {S : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (S : Set G)) :
    h ∈ Subgroup.normalizer ((Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
  have hone : ∀ {h : G}, h ∈ Subgroup.normalizer (S : Set G) →
      ∀ c ∈ Subgroup.centralizer (S : Set G), h * c * h⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro h hh c hc
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : h⁻¹ * s * h ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (S : Set G)).inv_mem hh) s).1 hs
      simpa [mul_assoc] using this
    have := Subgroup.mem_centralizer_iff.1 hc _ hs'
    calc s * (h * c * h⁻¹) = h * ((h⁻¹ * s * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * s * h)) * h⁻¹ := by rw [this]
      _ = (h * c * h⁻¹) * s := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact hone hh c
  · intro hc
    have := hone ((Subgroup.normalizer (S : Set G)).inv_mem hh) _ hc
    simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {h : G} (hA : h ∈ Subgroup.normalizer (A : Set G))
    (hB : h ∈ Subgroup.normalizer (B : Set G)) :
    h ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem E_le_layer_mul_centralizer {p : ℕ} {E : Subgroup G} {b : G} (hbE : b ∈ E)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (h157 : ∀ Y ∈ thetaCompZeroE p E, ∀ e ∈ E,
      ∃ x ∈ Y, ∃ y ∈ Subgroup.centralizer (Y : Set G), e = x * y)
    (hComm : ∀ Y₁ ∈ thetaCompZeroE p E, Y₁ ∈ thetaComponentsAt p b →
      ∀ Y₂ ∈ thetaCompZeroE p E, Y₂ ∈ thetaComponentsAt p b → Y₁ ≠ Y₂ →
        Y₁ ≤ Subgroup.centralizer (Y₂ : Set G)) :
    E ≤ zeroLayer p E b ⊔
      Subgroup.centralizer ((zeroLayer p E b ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
  classical
  set 𝒴 : Set (Subgroup G) := {Y | Y ∈ thetaCompZeroE p E ∧ Y ∈ thetaComponentsAt p b} with h𝒴
  have hfin : 𝒴.Finite := Set.toFinite 𝒴
  have key : ∀ F : Finset (Subgroup G), (↑F : Set (Subgroup G)) ⊆ 𝒴 → ∀ e ∈ E,
      ∃ x ∈ F.sup id, ∃ c ∈ Subgroup.centralizer ((F.sup id : Subgroup G) : Set G), e = x * c := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _ e _
      refine ⟨1, Subgroup.one_mem _, e, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ (⊥ : Subgroup G) := by simpa using hh
      rw [Subgroup.mem_bot.1 hh']
      simp
    | insert Y' F hY'F ih =>
      intro hsub e he
      have hY'𝒴 : Y' ∈ 𝒴 := hsub (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      have hFsub : (↑F : Set (Subgroup G)) ⊆ 𝒴 := fun Y hY =>
        hsub (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hY)))
      obtain ⟨x₁, hx₁, c₁, hc₁, hec₁⟩ := ih hFsub e he
      obtain ⟨x', hx', y', hy', hexy⟩ := h157 Y' hY'𝒴.1 e he
      have hFC : F.sup id ≤ Subgroup.centralizer (Y' : Set G) := by
        refine Finset.sup_le fun Y hY => ?_
        have hYne : Y ≠ Y' := fun h => hY'F (h ▸ hY)
        have hY𝒴 := hFsub (Finset.mem_coe.2 hY)
        exact hComm Y hY𝒴.1 hY𝒴.2 Y' hY'𝒴.1 hY'𝒴.2 hYne
      have hx₁Y' : x₁ ∈ Subgroup.centralizer (Y' : Set G) := hFC hx₁
      have hcomm : x' * x₁ = x₁ * x' := Subgroup.mem_centralizer_iff.1 hx₁Y' x' hx'
      have hY'C : x' ∈ Subgroup.centralizer ((F.sup id : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.1 (hFC hz) x' hx').symm
      refine ⟨x₁ * x', ?_, x₁⁻¹ * y', ?_, ?_⟩
      · rw [Finset.sup_insert, sup_comm]
        exact Subgroup.mul_mem_sup hx₁ hx'
      · rw [Finset.sup_insert, mem_centralizer_sup]
        refine ⟨(Subgroup.centralizer (Y' : Set G)).mul_mem
          ((Subgroup.centralizer (Y' : Set G)).inv_mem hx₁Y') hy', ?_⟩
        have hc₂ : x₁⁻¹ * y' = x'⁻¹ * c₁ := by
          have h1 : x₁ * c₁ = x' * y' := hec₁.symm.trans hexy
          calc x₁⁻¹ * y' = x₁⁻¹ * (x'⁻¹ * (x' * y')) := by group
            _ = x₁⁻¹ * (x'⁻¹ * (x₁ * c₁)) := by rw [h1]
            _ = x'⁻¹ * (x₁⁻¹ * x₁) * c₁ * 1 := by
              have : x₁⁻¹ * x'⁻¹ = x'⁻¹ * x₁⁻¹ := by
                calc x₁⁻¹ * x'⁻¹ = (x' * x₁)⁻¹ := by group
                  _ = (x₁ * x')⁻¹ := by rw [hcomm]
                  _ = x'⁻¹ * x₁⁻¹ := by group
              calc x₁⁻¹ * (x'⁻¹ * (x₁ * c₁)) = (x₁⁻¹ * x'⁻¹) * (x₁ * c₁) := by group
                _ = (x'⁻¹ * x₁⁻¹) * (x₁ * c₁) := by rw [this]
                _ = x'⁻¹ * (x₁⁻¹ * x₁) * c₁ * 1 := by group
            _ = x'⁻¹ * c₁ := by group
        rw [hc₂]
        exact (Subgroup.centralizer ((F.sup id : Subgroup G) : Set G)).mul_mem
          ((Subgroup.centralizer ((F.sup id : Subgroup G) : Set G)).inv_mem hY'C) hc₁
      · have h2 : x₁ * x' * x₁⁻¹ = x' := by rw [← hcomm]; group
        calc e = x' * y' := hexy
          _ = (x₁ * x' * x₁⁻¹) * y' := by rw [h2]
          _ = x₁ * x' * (x₁⁻¹ * y') := by group
  have hsub : (↑hfin.toFinset : Set (Subgroup G)) ⊆ 𝒴 := by simp
  have hsup : hfin.toFinset.sup id = zeroLayer p E b := by
    apply le_antisymm
    · refine Finset.sup_le fun Y hY => ?_
      have hY𝒴 : Y ∈ 𝒴 := hfin.mem_toFinset.1 hY
      exact fun x hx => Subgroup.subset_closure ⟨Y, hY𝒴.1, hY𝒴.2, hx⟩
    · refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨Y, hY0, hYb, hx⟩
      have hYF : Y ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨hY0, hYb⟩
      exact (Finset.le_sup (f := id) hYF) hx
  intro e he
  obtain ⟨x, hx, c, hc, hec⟩ := key hfin.toFinset hsub e he
  rw [hsup] at hx hc
  have hxb : x ∈ Subgroup.centralizer ({b} : Set G) := zeroLayer_le_centralizer p E b hx
  have hcb : c ∈ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 hxb
    have h2 : c = x⁻¹ * e := by rw [hec]; group
    have hxb' : x⁻¹ * b = b * x⁻¹ := by
      calc x⁻¹ * b = x⁻¹ * (b * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * b) * x⁻¹ := by rw [h1]
        _ = b * x⁻¹ := by group
    rw [h2]
    calc x⁻¹ * e * b = x⁻¹ * (e * b) := by group
      _ = x⁻¹ * (b * e) := by rw [hEab b hbE e he]
      _ = (x⁻¹ * b) * e := by group
      _ = (b * x⁻¹) * e := by rw [hxb']
      _ = b * (x⁻¹ * e) := by group
  rw [hec]
  exact Subgroup.mul_mem_sup hx ((mem_centralizer_sup).2 ⟨hc, hcb⟩)

theorem centralizer_le_of_layer {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElementaryAbelian p ↥E)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    {b : G} {X N : Subgroup G} (hXb : X ≤ Subgroup.centralizer ({b} : Set G))
    (hXnorm : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hEX : E ≤ X ⊔ Subgroup.centralizer ((X ⊔ Subgroup.zpowers b : Subgroup G) : Set G))
    (hXN : X ≤ N)
    (hCN : Subgroup.centralizer ((X ⊔ Subgroup.zpowers b : Subgroup G) : Set G) ≤ N)
    (hWN : Subgroup.normalizer (E : Set G) ≤ N) : Subgroup.centralizer ({b} : Set G) ≤ N := by
  have hbS : b ∈ X ⊔ Subgroup.zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hhS : ∀ h ∈ Subgroup.centralizer ({b} : Set G),
      h ∈ Subgroup.normalizer ((X ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
    intro h hh
    refine mem_normalizer_sup (hXnorm hh) ?_
    have hh' : h ∈ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hh
    exact Subgroup.centralizer_le_normalizer _ hh'
  refine Sec15FA.frattini_torus_le hp hE hJ (H := Subgroup.centralizer ({b} : Set G))
    (H₁ := X ⊔ Subgroup.centralizer ((X ⊔ Subgroup.zpowers b : Subgroup G) : Set G)) hEX ?_ ?_
    (sup_le hXN hCN) hWN
  · refine sup_le hXb fun c hc => ?_
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbS) hc
  · intro h hh
    exact mem_normalizer_sup (hXnorm hh) (mem_normalizer_centralizer (hhS h hh))

theorem centralizer_le_of_good {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElementaryAbelian p ↥E)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    {b : G} {X N : Subgroup G} (hXb : X ≤ Subgroup.centralizer ({b} : Set G))
    (hXnorm : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hEX : E ≤ X ⊔ Subgroup.zpowers b) (hXN : X ≤ N)
    (hWN : Subgroup.normalizer (E : Set G) ≤ N) : Subgroup.centralizer ({b} : Set G) ≤ N := by
  have hbC : b ∈ Subgroup.centralizer ((X ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
    rw [mem_centralizer_sup]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.1 (hXb hx)
    · rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff]
  have hCE : Subgroup.centralizer ((X ⊔ Subgroup.zpowers b : Subgroup G) : Set G) ≤
      Subgroup.centralizer (E : Set G) := Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hEX)
  refine centralizer_le_of_layer hp hE hJ hXb hXnorm ?_ hXN
    (hCE.trans ((Subgroup.centralizer_le_normalizer _).trans hWN)) hWN
  exact hEX.trans (sup_le le_sup_left ((Subgroup.zpowers_le.2 hbC).trans le_sup_right))

omit [Finite G] in
theorem mem_thetaComponentsAt_subgroupOf_of_centralizer {p : ℕ} (hp : p.Prime)
    {H D' J : Subgroup G} (y : ↥H)
    (hD : (Subgroup.centralizer ({y} : Set ↥H)).map H.subtype = D') (hJD' : J ≤ D')
    (hJ : J.subgroupOf D' ∈ thetaComponents p ↥D') [Finite G] :
    J.subgroupOf H ∈ thetaComponentsAt p y := by
  classical
  set C : Subgroup ↥H := Subgroup.centralizer ({y} : Set ↥H) with hC
  let σ : ↥D' ≃* ↥C :=
    (MulEquiv.subgroupCongr hD.symm).trans
      (Subgroup.equivMapOfInjective C H.subtype H.subtype_injective).symm
  have hσ : ∀ g : ↥D', (((σ g : ↥C) : ↥H) : G) = (g : G) := by
    intro g
    have h1 : (Subgroup.equivMapOfInjective C H.subtype H.subtype_injective) (σ g) =
        MulEquiv.subgroupCongr hD.symm g := by
      simp [σ]
    have h2 := congrArg (fun z : ↥(C.map H.subtype) => (z : G)) h1
    simpa using h2
  have hmap := map_mulEquiv_mem_thetaComponents hp σ hJ
  rw [mem_thetaComponentsAt_iff]
  refine ⟨?_, ?_⟩
  · intro g hg
    have hgD' : (g : G) ∈ D' := hJD' hg
    rw [← hD] at hgD'
    obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.1 hgD'
    have : c = g := Subtype.ext hcg
    exact this ▸ hc
  · have heq : (J.subgroupOf H).subgroupOf C = (J.subgroupOf D').map σ.toMonoidHom := by
      ext g
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv,
        Subgroup.mem_subgroupOf]
      have h1 := hσ (σ.symm g)
      rw [MulEquiv.apply_symm_apply] at h1
      rw [← h1]
    rw [heq]
    exact hmap

theorem layer_ge_of_KF158A (hS : SchreierFor InCatalog) (h82 : LocalThetaComponentEmbeddingFrontier)
    {p : ℕ} {A : Subgroup G} {c : G} {L E J : Subgroup G} (h15 : Sec15Hyp G p A c L E)
    (hcard : p * Nat.card ↥(A ⊓ Subgroup.centralizer (J : Set G)) = Nat.card ↥A)
    (hJθ : J ∈ thetaCompCentralizer p (A ⊓ Subgroup.centralizer (J : Set G)))
    (hS2 : ∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      S = ⁅S, A⁆)
    {b : G} (hbD : b ∈ A ⊓ Subgroup.centralizer (J : Set G)) (hb1 : b ≠ 1) :
    J ≤ zeroLayer p E b := by
  classical
  have h := h15.h12
  have hp := h.prime
  have hp3 := h.three_lt
  have : Fact p.Prime := ⟨hp⟩
  have hAel : IsElementaryAbelian p ↥A := h.A_elem
  set D : Subgroup G := A ⊓ Subgroup.centralizer (J : Set G) with hDdef
  have hDA : D ≤ A := inf_le_left
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) x hx
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDcard : Nat.card ↥D = p ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
    rw [hcard, h.A_card]
    ring
  have hbA : b ∈ A := hbD.1
  have hbord : orderOf b = p := orderOf_eq_prime (hApow b hbA) hb1
  have hzb : Nat.card ↥(Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hbord]
  obtain ⟨x, hxD, hxb⟩ : ∃ x ∈ D, x ∉ Subgroup.zpowers b := by
    by_contra hcon
    have hle : D ≤ Subgroup.zpowers b := fun x hx => by_contra fun hxb => hcon ⟨x, hx, hxb⟩
    have := Subgroup.card_le_of_le hle
    rw [hDcard, hzb] at this
    have h2 : p ^ 2 ≤ p := this
    have := hp.two_le
    nlinarith
  have hMD : Subgroup.zpowers b ⊔ Subgroup.zpowers x = D := by
    set M := Subgroup.zpowers b ⊔ Subgroup.zpowers x with hM
    have hMD' : M ≤ D := sup_le (Subgroup.zpowers_le.2 hbD) (Subgroup.zpowers_le.2 hxD)
    have hbM : Subgroup.zpowers b ≤ M := le_sup_left
    have hdvd : Nat.card ↥M ∣ p ^ 2 := hDcard ▸ Subgroup.card_dvd_of_le hMD'
    obtain ⟨k, hk, hMk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hle1 : p ≤ Nat.card ↥M := hzb ▸ Subgroup.card_le_of_le hbM
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hMk
      have := hp.two_le
      omega
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [pow_one] at hMk
      have heq : Subgroup.zpowers b = M :=
        Subgroup.eq_of_le_of_card_ge hbM (by rw [hMk, hzb])
      exact hxb (heq ▸ (le_sup_right : Subgroup.zpowers x ≤ M) (Subgroup.mem_zpowers x))
    have hk2 : k = 2 := by omega
    subst hk2
    exact Subgroup.eq_of_le_of_card_ge hMD' (by rw [hDcard, hMk])
  have hxbc : x * b = b * x := hAcomm x (hDA hxD) b hbA
  have hxH : x ∈ Subgroup.centralizer ({b} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hxbc
  set H : Subgroup G := Subgroup.centralizer ({b} : Set G) with hH
  let y : ↥H := ⟨x, hxH⟩
  have hx1 : x ≠ 1 := fun h1 => hxb (h1 ▸ Subgroup.one_mem _)
  have hyord : orderOf y = p := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hApow x (hDA hxD)) hx1
  obtain ⟨hJC, hJθ'⟩ := mem_image_map_subtype_iff_of_le.1 hJθ
  have hDC : (Subgroup.centralizer ({y} : Set ↥H)).map H.subtype =
      Subgroup.centralizer (D : Set G) := by
    ext g
    rw [← hMD]
    constructor
    · rintro ⟨hh, hhc, rfl⟩
      rw [mem_centralizer_sup, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        Subgroup.centralizer_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      refine ⟨Subgroup.mem_centralizer_singleton_iff.1 hh.2, ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.1 hhc
      exact congrArg Subtype.val this
    · intro hg
      rw [mem_centralizer_sup, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        Subgroup.centralizer_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff] at hg
      have hgH : g ∈ H := Subgroup.mem_centralizer_singleton_iff.2 hg.1
      have hy' : (⟨g, hgH⟩ : ↥H) ∈ Subgroup.centralizer ({y} : Set ↥H) :=
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hg.2)
      exact ⟨_, hy', rfl⟩
  have hJy : J.subgroupOf H ∈ thetaComponentsAt p y :=
    mem_thetaComponentsAt_subgroupOf_of_centralizer hp y hDC hJC hJθ'
  have hsimple : IsSimpleGroup G := h.setup.1
  have hHK : CFSG.IsKGroup ↥H :=
    h.setup.2.2.1 _ (EmbeddingFixedResidual.centralizer_ne_top_of_simple h.setup.2.1 hb1)
  have hHE : evenRank ↥H ≤ 3 := (Sec9A.evenRank_subgroup_le _).trans h.evenRank_eq.le
  obtain ⟨L', hL', hJL'⟩ := h82 hS ↥H hHK hHE p hp hp3 y hyord _ hJy
  have hIb : L'.map H.subtype ∈ thetaComponentsAt p b := ⟨L', hL', rfl⟩
  obtain ⟨S, hSJ, hS0, hS2', hAS, hSA⟩ := hS2
  have hJIb : J ≤ L'.map H.subtype := by
    intro g hg
    have hgH : g ∈ H :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbD) (hJC hg)
    exact ⟨⟨g, hgH⟩, hJL' hg, rfl⟩
  have hAadm : A ∈ admissibleTriples p E :=
    ⟨h.A_le_E, hAel, h.A_card, S, hS0, hS2', hAS⟩
  have hIb0 : L'.map H.subtype ∈ thetaCompZeroE p E :=
    ⟨A, hAadm, mem_thetaComponentFamily_iff.2 ⟨b, hbA, hb1, hIb⟩, S, hSJ.trans hJIb, hS0, hS2', hAS,
      hSA⟩
  exact hJIb.trans (fun g hg => Subgroup.subset_closure ⟨_, hIb0, hIb, hg⟩)

structure Ctx158 (p : ℕ) (E : Subgroup G) : Prop where
  prime : p.Prime
  elem : IsElementaryAbelian p ↥E
  hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
    thompsonElem p Q = E
  layer_le : ∀ b : G, zeroLayer p E b ≤ lieGenerated p E
  L0 : ∀ b ∈ E, b ≠ 1 → ∀ z ∈ Subgroup.centralizer ({b} : Set G), ∀ Y ∈ thetaCompZeroE p E,
    Y ∈ thetaComponentsAt p b → conjBy z Y ∈ thetaCompZeroE p E
  B2 : ∀ b ∈ E, b ≠ 1 → E ≤ zeroLayer p E b ⊔
    Subgroup.centralizer ((zeroLayer p E b ⊔ Subgroup.zpowers b : Subgroup G) : Set G)

theorem centralizer_le_N_of_layer {p : ℕ} {E : Subgroup G} (hc : Ctx158 p E) {b : G} (hbE : b ∈ E)
    (hb1 : b ≠ 1)
    (hCN : Subgroup.centralizer ((zeroLayer p E b ⊔ Subgroup.zpowers b : Subgroup G) : Set G) ≤
      lieNormalizer p E) :
    Subgroup.centralizer ({b} : Set G) ≤ lieNormalizer p E :=
  centralizer_le_of_layer hc.prime hc.elem hc.hJ (zeroLayer_le_centralizer p E b)
    (centralizer_le_normalizer_zeroLayer hc.prime (hc.L0 b hbE hb1)) (hc.B2 b hbE hb1)
    ((hc.layer_le b).trans Subgroup.le_normalizer) hCN (torusNormalizer_le_lieNormalizer hc.prime E)

theorem root_centralizer_le {p : ℕ} {E : Subgroup G} (hc : Ctx158 p E) {a : G} (haE : a ∈ E)
    (ha1 : a ≠ 1)
    (hcov : (E ≤ zeroLayer p E a ⊔ Subgroup.zpowers a) ∨
      (∃ d ∈ E, d ≠ 1 ∧ d ∈ zeroLayer p E a ⊔ Subgroup.zpowers a ∧
        E ≤ zeroLayer p E d ⊔ Subgroup.zpowers d) ∨
      (∃ w ∈ torusNormalizer E, w * a * w⁻¹ ∈ zeroLayer p E a ∧
        zeroLayer p E a ⊔ conjBy w (zeroLayer p E a) = lieGenerated p E)) :
    Subgroup.centralizer ({a} : Set G) ≤ lieNormalizer p E := by
  have hWN : Subgroup.normalizer (E : Set G) ≤ lieNormalizer p E :=
    torusNormalizer_le_lieNormalizer hc.prime E
  have hXN : ∀ b : G, zeroLayer p E b ≤ lieNormalizer p E := fun b =>
    (hc.layer_le b).trans Subgroup.le_normalizer
  have hgood : ∀ b ∈ E, b ≠ 1 → E ≤ zeroLayer p E b ⊔ Subgroup.zpowers b →
      Subgroup.centralizer ({b} : Set G) ≤ lieNormalizer p E := fun b hbE hb1 hEb =>
    centralizer_le_of_good hc.prime hc.elem hc.hJ (zeroLayer_le_centralizer p E b)
      (centralizer_le_normalizer_zeroLayer hc.prime (hc.L0 b hbE hb1)) hEb (hXN b) hWN
  rcases hcov with hEa | ⟨d, hdE, hd1, hdXa, hEd⟩ | ⟨w, hw, hwa, hI⟩
  · exact hgood a haE ha1 hEa
  · have hCd := hgood d hdE hd1 hEd
    refine centralizer_le_N_of_layer hc haE ha1 ?_
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hdXa)).trans hCd
  · refine centralizer_le_N_of_layer hc haE ha1 ?_
    intro z hz
    rw [mem_centralizer_sup] at hz
    obtain ⟨hzX, -⟩ := hz
    have hzXa : z ∈ Subgroup.normalizer (zeroLayer p E a : Set G) :=
      Subgroup.centralizer_le_normalizer _ hzX
    have hzaw : z ∈ Subgroup.centralizer ({w * a * w⁻¹} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 hwa) hzX
    have hawE : w * a * w⁻¹ ∈ E := by
      have := Equivariance.conjBy_eq_of_mem_normalizer hw
      rw [← this]
      exact Subgroup.mem_map_of_mem _ haE
    have haw1 : w * a * w⁻¹ ≠ 1 := fun h1 => ha1 (by
      have : a = w⁻¹ * (w * a * w⁻¹) * w := by group
      rw [this, h1]
      group)
    have hz2 : z ∈ Subgroup.normalizer (conjBy w (zeroLayer p E a) : Set G) := by
      rw [← zeroLayer_conjBy hc.prime hw a]
      exact centralizer_le_normalizer_zeroLayer hc.prime (hc.L0 _ hawE haw1) hzaw
    have hzI : z ∈ Subgroup.normalizer ((zeroLayer p E a ⊔ conjBy w (zeroLayer p E a) : Subgroup G) :
        Set G) := mem_normalizer_sup hzXa hz2
    rw [hI] at hzI
    exact hzI

theorem hyperplane_centralizer_le {p : ℕ} {E : Subgroup G} (hc : Ctx158 p E) {J : Subgroup G} {a b : G}
    (hbE : b ∈ E) (hb1 : b ≠ 1) (haJ : a ∈ J) (hJX : J ≤ zeroLayer p E b)
    (hCa : Subgroup.centralizer ({a} : Set G) ≤ lieNormalizer p E) :
    Subgroup.centralizer ({b} : Set G) ≤ lieNormalizer p E := by
  refine centralizer_le_N_of_layer hc hbE hb1 ?_
  intro z hz
  rw [mem_centralizer_sup] at hz
  have haX : a ∈ zeroLayer p E b := hJX haJ
  exact hCa (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haX) hz.1)

omit [Finite G] in
theorem exists_ne_one_mem_inf [Finite G] {p : ℕ} (hp : p.Prime) {A B D : Subgroup G}
    (hAel : IsElementaryAbelian p ↥A) (hBA : B ≤ A) (hDA : D ≤ A) (hBcyc : ¬ IsCyclic ↥B)
    (hcard : p * Nat.card ↥D = Nat.card ↥A) : ∃ b ∈ B ⊓ D, b ≠ 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  have hbot : B ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    exact hcon ⟨x, hx, fun h1 => hx1 (by rw [h1]; exact Subgroup.one_mem _)⟩
  have hDA' : D.relIndex A = p := by
    have h1 := (D.subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv] at h1
    have h2 : (D.subgroupOf A).index * Nat.card ↥D = p * Nat.card ↥D := h1.trans hcard.symm
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hDB : D.relIndex B = Nat.card ↥B := by
    have hbot' : D.subgroupOf B = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (x : G) ∈ B ⊓ D := ⟨x.2, hx⟩
      rw [hbot] at hx'
      have : x = 1 := Subtype.ext (Subgroup.mem_bot.1 hx')
      rw [this]
      exact Subgroup.one_mem _
    have h1 := (D.subgroupOf B).index_mul_card
    have hc1 : Nat.card ↥(D.subgroupOf B) = 1 := by
      rw [hbot']
      exact Subgroup.card_bot
    rw [hc1, mul_one] at h1
    exact h1
  have hle : Nat.card ↥B ≤ p := by
    have := Subgroup.relIndex_le_of_le_right hBA (H := D) (by
      rw [hDA']
      exact hp.ne_zero)
    rw [hDB, hDA'] at this
    exact this
  have hBp : IsPGroup p ↥B := by
    have : IsPGroup p ↥A := hAel.isPGroup p ↥A
    exact this.to_le hBA
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  have hn1 : n ≤ 1 := by
    by_contra hn2
    have h2 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos (by omega)
    have := hp.two_le
    nlinarith
  interval_cases n
  · have : Nat.card ↥B = 1 := by simpa using hn
    have hsub : Subsingleton ↥B := (Nat.card_eq_one_iff_unique.1 this).1
    exact hBcyc (isCyclic_of_subsingleton)
  · exact hBcyc (isCyclic_of_prime_card (by simpa using hn))

end Sec158

end CFSG.RankThree.PartOne
