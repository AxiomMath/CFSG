module

public import CFSG.Milestones.ASVolI.C135.Coc
public import CFSG.Quasithin.Vol2.Ch4Sec3C136
public import CFSG.Quasithin.Vol2.Ch4Sec3C135H1

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13.Ch4
open CFSG.Quasithin.H13.Ch4.C135 (slNat coe_slNat moduleAct_false_eq)
open scoped commutatorElement

variable {G : Type} [Group G]

section One

variable [Finite G] {G₀ L : Subgroup G} {F : Type} [Field F] {α : ↥L →* ↥(StatedSL 3 F)}

theorem burnsideC135_centralizer_conj (hα : IsModO2Surj L α) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅L, L⁆ = L) {k : ℕ} (hk : k ≠ 0)
    (hN : IsSumOfNaturalModulesVia L (c134Q G₀ L) ⊥ α false k)
    (hCL : G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) {v : G}
    (hv : v ∈ G₀ ⊓ Subgroup.centralizer (c134Q G₀ L : Set G)) :
    (∀ g ∈ L, v⁻¹ * (g * v * g⁻¹) ∈ c134Q G₀ L) ∧ (∀ a : ↥L, α a = 1 → (a : G) * v = v * a) := by
  set Q := c134Q G₀ L with hQ
  set V := G₀ ⊓ Subgroup.centralizer (Q : Set G) with hV
  have hOO : pCoreOf 2 L ≤ pCoreOf 2 G₀ :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLG)
      (hGL.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  have hOLQ : ⁅pCoreOf 2 L, L⁆ ≤ Q := Subgroup.commutator_mono hOO le_rfl
  have hGQ : G₀ ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_c134Q hGL
  have hGV : G₀ ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg) (mem_normalizer_centralizer_of_mem (hGQ hg))
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
  refine ⟨hvK v hv, fun a ha => ?_⟩
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

theorem burnsideC135_isElemAbelian_centralizer [Fintype F] [CharP F 2] (hα : IsModO2Surj L α)
    (hLG : L ≤ G₀) (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅L, L⁆ = L) {k : ℕ}
    (hk : k ≠ 0) (hN : IsSumOfNaturalModulesVia L (c134Q G₀ L) ⊥ α false k)
    (hCL : G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    IsElemAbelian 2 (G₀ ⊓ Subgroup.centralizer (c134Q G₀ L : Set G)) := by
  set Q := c134Q G₀ L with hQ
  set V := G₀ ⊓ Subgroup.centralizer (Q : Set G) with hV
  have hQab : ∀ {x y : G}, x ∈ Q → y ∈ Q → x * y = y * x := fun hx hy =>
    mul_comm_of_isSumOfNaturalModulesVia hN hx hy
  have hQsq : ∀ q ∈ Q, q * q = 1 := by
    intro q hq
    obtain ⟨-, -, β, -, hβk, -⟩ := hN
    have hβinj : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
    have h1 : β (⟨q, hq⟩ * ⟨q, hq⟩) = 1 := by
      rw [map_mul]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      funext i j
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    have h2 : (⟨q, hq⟩ : ↥Q) * ⟨q, hq⟩ = 1 := hβinj (h1.trans (map_one β).symm)
    exact congrArg Subtype.val h2
  have hvQ : ∀ v ∈ V, ∀ q ∈ Q, q * v = v * q := fun v hv q hq =>
    Subgroup.mem_centralizer_iff.mp hv.2 q hq
  have hconj := fun {v : G} (hv : v ∈ V) =>
    (burnsideC135_centralizer_conj hα hLG hGL hperf hk hN hCL hv).1
  have hone : ∀ x ∈ G₀, (∀ g ∈ L, g * x * g⁻¹ = x) → x = 1 := by
    intro x hx h
    have h1 : x ∈ G₀ ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h g hg]
    rw [hCL] at h1
    exact Subgroup.mem_bot.mp h1
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have h := hone (x * y * x⁻¹ * y⁻¹)
      (G₀.mul_mem (G₀.mul_mem (G₀.mul_mem hx.1 hy.1) (G₀.inv_mem hx.1)) (G₀.inv_mem hy.1))
      (fun g hg => by
        obtain ⟨q₁, hq₁, h₁⟩ : ∃ q₁ ∈ Q, g * x * g⁻¹ = x * q₁ :=
          ⟨x⁻¹ * (g * x * g⁻¹), hconj hx g hg, by group⟩
        obtain ⟨q₂, hq₂, h₂⟩ : ∃ q₂ ∈ Q, g * y * g⁻¹ = y * q₂ :=
          ⟨y⁻¹ * (g * y * g⁻¹), hconj hy g hg, by group⟩
        have hq₁x := hvQ x hx q₁ hq₁
        have hq₁y := hvQ y hy q₁ hq₁
        have hq₂x := hvQ x hx q₂ hq₂
        have hq₂y := hvQ y hy q₂ hq₂
        have hq12 := hQab hq₁ hq₂
        calc g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ =
              (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
          _ = (x * q₁) * (y * q₂) * (x * q₁)⁻¹ * (y * q₂)⁻¹ := by rw [h₁, h₂]
          _ = x * (q₁ * y) * q₂ * q₁⁻¹ * x⁻¹ * q₂⁻¹ * y⁻¹ := by group
          _ = x * (y * q₁) * q₂ * q₁⁻¹ * x⁻¹ * q₂⁻¹ * y⁻¹ := by rw [hq₁y]
          _ = x * y * (q₁ * q₂) * q₁⁻¹ * x⁻¹ * q₂⁻¹ * y⁻¹ := by group
          _ = x * y * (q₂ * q₁) * q₁⁻¹ * x⁻¹ * q₂⁻¹ * y⁻¹ := by rw [hq12]
          _ = x * y * (q₂ * x⁻¹) * q₂⁻¹ * y⁻¹ := by group
          _ = x * y * (x⁻¹ * q₂) * q₂⁻¹ * y⁻¹ := by
              rw [show q₂ * x⁻¹ = x⁻¹ * q₂ by
                calc q₂ * x⁻¹ = x⁻¹ * (x * q₂) * x⁻¹ := by group
                  _ = x⁻¹ * (q₂ * x) * x⁻¹ := by rw [hq₂x]
                  _ = x⁻¹ * q₂ := by group]
          _ = x * y * x⁻¹ * y⁻¹ := by group)
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h, one_mul]
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  have h := hone (x * x) (G₀.mul_mem hx.1 hx.1) (fun g hg => by
    obtain ⟨q, hq, h₁⟩ : ∃ q ∈ Q, g * x * g⁻¹ = x * q :=
      ⟨x⁻¹ * (g * x * g⁻¹), hconj hx g hg, by group⟩
    have hqx := hvQ x hx q hq
    calc g * (x * x) * g⁻¹ = (g * x * g⁻¹) * (g * x * g⁻¹) := by group
      _ = (x * q) * (x * q) := by rw [h₁]
      _ = x * (q * x) * q := by group
      _ = x * (x * q) * q := by rw [hqx]
      _ = x * x * (q * q) := by group
      _ = x * x := by rw [hQsq q hq, mul_one])
  rw [sq]
  exact h

theorem burnsideC135_slNat_surj {K : Type*} [Group K] {α : K →* ↥(StatedSL 3 F)}
    (hα : Function.Surjective α) : Function.Surjective (slNat α) := by
  intro γ
  obtain ⟨g, hg⟩ := hα (specialLinearGroupEquivStatedSL 3 F γ)
  refine ⟨g, ?_⟩
  simp only [slNat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hg, MulEquiv.symm_apply_apply]

theorem burnsideC135_mem_of_commute_invol [Fintype F] (hF2 : Fintype.card F = 2)
    (hα : IsModO2Surj L α) (hLG : L ≤ G₀) (hGL : G₀ ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) {k : ℕ} (hk : k ≠ 0)
    (hN : IsSumOfNaturalModulesVia L (c134Q G₀ L) ⊥ α false k)
    (hCL : G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) {v : G}
    (hv : v ∈ G₀ ⊓ Subgroup.centralizer (c134Q G₀ L : Set G)) {l : ↥L}
    (hl1 : slNat α l ≠ 1) (hl2 : slNat α l * slNat α l = 1) (hlv : (l : G) * v = v * l) :
    v ∈ c134Q G₀ L := by
  obtain ⟨hvK, hvker⟩ := burnsideC135_centralizer_conj hα hLG hGL hperf hk hN hCL hv
  have hQG : c134Q G₀ L ≤ G₀ := (c134Q_le hGL).trans hLG
  set Q := c134Q G₀ L with hQ
  obtain ⟨hLQ, -, β, hβs, hβk, hβeq⟩ := hN
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  let cj : ↥L → ↥Q → ↥Q := fun g u =>
    ⟨g * u * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLQ g.2) u).mp u.2⟩
  have hcj : ∀ (g : ↥L) (u : ↥Q), Multiplicative.toAdd (β (cj g u)) =
      dact ((slNat α g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        (Multiplicative.toAdd (β u)) := by
    intro g u
    funext i
    rw [hβeq g u (cj g u) rfl i, moduleAct_false_eq]
    rfl
  let c : ↥L → ↥Q := fun g => ⟨v⁻¹ * (g * v * (g : G)⁻¹), hvK g g.2⟩
  let f : ↥L → Fin k → Fin 3 → F := fun g => Multiplicative.toAdd (β (c g))
  have hcmul : ∀ g h : ↥L, c (g * h) = c g * cj g (c h) := by
    intro g h
    apply Subtype.ext
    show v⁻¹ * ((g : G) * h * v * ((g : G) * h)⁻¹) =
      v⁻¹ * (g * v * (g : G)⁻¹) * ((g : G) * (v⁻¹ * (h * v * (h : G)⁻¹)) * (g : G)⁻¹)
    group
  have hf : ∀ g h, f (g * h) = f g + dact ((slNat α g : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) (f h) := by
    intro g h
    show Multiplicative.toAdd (β (c (g * h))) = _
    rw [hcmul, map_mul, toAdd_mul, hcj]
  have hker : ∀ a, slNat α a = 1 → f a = 0 := by
    intro a ha
    have ha' : α a = 1 := by
      have : (specialLinearGroupEquivStatedSL 3 F).symm (α a) = 1 := ha
      simpa using this
    have hca : c a = 1 := by
      apply Subtype.ext
      show v⁻¹ * ((a : G) * v * (a : G)⁻¹) = 1
      rw [hvker a ha']
      group
    show Multiplicative.toAdd (β (c a)) = 0
    rw [hca, map_one]
    rfl
  have hft : f l = 0 := by
    have hcl : c l = 1 := by
      apply Subtype.ext
      show v⁻¹ * ((l : G) * v * (l : G)⁻¹) = 1
      rw [hlv]
      group
    show Multiplicative.toAdd (β (c l)) = 0
    rw [hcl, map_one]
    rfl
  obtain ⟨m, hm⟩ := burnsideC135_exists_coboundary_two hF2 (burnsideC135_slNat_surj hα.1) hf hker
    hl1 hl2 hft
  obtain ⟨n₀, hn₀⟩ := hβs (Multiplicative.ofAdd (-m))
  have hcent : v * n₀ ∈ G₀ ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨G₀.mul_mem hv.1 (hQG n₀.2), Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    have h1 : c ⟨g, hg⟩ * cj ⟨g, hg⟩ n₀ = n₀ := by
      apply hβinj
      apply Multiplicative.toAdd.injective
      rw [map_mul, toAdd_mul, hcj, hn₀]
      show f ⟨g, hg⟩ + _ = _
      rw [hm, toAdd_ofAdd, CFSG.Quasithin.H13.Ch4.C135.dact_neg]
      abel
    have h2 : g * (v * n₀) * g⁻¹ = v * n₀ := by
      have h3 := congrArg Subtype.val h1
      have h4 : (v⁻¹ * (g * v * g⁻¹)) * (g * (n₀ : G) * g⁻¹) = n₀ := h3
      calc g * (v * n₀) * g⁻¹ = v * ((v⁻¹ * (g * v * g⁻¹)) * (g * (n₀ : G) * g⁻¹)) := by group
        _ = v * n₀ := by rw [h4]
    calc g * (v * n₀) = g * (v * n₀) * g⁻¹ * g := by group
      _ = v * n₀ * g := by rw [h2]
  rw [hCL, Subgroup.mem_bot] at hcent
  have hv' : v = (n₀ : G)⁻¹ := eq_inv_of_mul_eq_one_left hcent
  rw [hv']
  exact Q.inv_mem n₀.2

theorem burnsideC135_eq_one_of_dact {Y : Matrix.SpecialLinearGroup (Fin 3) F}
    (h : ∀ v : Fin 2 → Fin 3 → F, dact (Y : Matrix (Fin 3) (Fin 3) F) v = v) : Y = 1 := by
  have hfix : ∀ x : Fin 3 → F, (Y : Matrix (Fin 3) (Fin 3) F).mulVec x = x := fun x =>
    congrFun (h fun _ => x) 0
  apply Subtype.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one, hfix x]
  rfl

theorem burnsideC135_card_le_one [Finite F] [CharP F 2] {Q : Subgroup G}
    (hα : IsModO2Surj L α) (hLG : L ≤ G₀) (hGL : G₀ ≤ Subgroup.normalizer (L : Set G))
    (hGN : G₀ ≤ Subgroup.normalizer (Q : Set G))
    (hQV : Q ≤ G₀ ⊓ Subgroup.centralizer (Q : Set G))
    (hVab : ∀ x ∈ G₀ ⊓ Subgroup.centralizer (Q : Set G),
      ∀ y ∈ G₀ ⊓ Subgroup.centralizer (Q : Set G), x * y = y * x)
    (hcoc : ∀ v ∈ G₀ ⊓ Subgroup.centralizer (Q : Set G), ∀ l : ↥L, slNat α l ≠ 1 →
      slNat α l * slNat α l = 1 → (l : G) * v = v * l → v ∈ Q)
    (β : ↥Q ≃* Multiplicative (Fin 2 → Fin 3 → F))
    (hβ : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (β u) i))
    {B : Subgroup G} (hBG : B ≤ G₀) (hB : IsElemAbelian 2 B) :
    Nat.card B ≤ Nat.card ↥(G₀ ⊓ Subgroup.centralizer (Q : Set G)) ∧
      (Nat.card B = Nat.card ↥(G₀ ⊓ Subgroup.centralizer (Q : Set G)) →
        B = G₀ ⊓ Subgroup.centralizer (Q : Set G) ∨ G₀ ⊓ Subgroup.centralizer (Q : Set G) = Q) := by
  classical
  set V := G₀ ⊓ Subgroup.centralizer (Q : Set G) with hV
  set N := Subgroup.normalizer (Q : Set G) with hN
  have hBN : B ≤ N := hBG.trans hGN
  have hLN : L ≤ N := hLG.trans hGN
  set B' := B.subgroupOf N with hB'
  set φ := (cHom β).comp B'.subtype with hφ
  set E := φ.range with hE
  have hcardB : Nat.card B = Nat.card B' :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv).symm
  have hadd : E ≤ addPerms F := by
    rintro _ ⟨b, rfl⟩
    exact cHom_mem_addPerms β _
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have := hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact hcommB _ x.2 _ y.2
  have hinv : ∀ e ∈ E, e * e = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have h1 : x * x = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have := hB.2 _ x.2
      rw [sq] at this
      exact this
    rw [h1, map_one]
  let e₀ := specialLinearGroupEquivStatedSL 3 F
  have hnorm : ∀ e ∈ E, NormalizesDact ⇑e := by
    rintro _ ⟨b, rfl⟩ X
    obtain ⟨l, hl⟩ := hα.1 (e₀ X)
    have hbG : ((b : ↥N) : G) ∈ G₀ := hBG b.2
    have hlbl : ((b : ↥N) : G) * l * ((b : ↥N) : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hGL hbG) _).mp l.2
    refine ⟨e₀.symm (α ⟨_, hlbl⟩), fun v => ?_⟩
    have hX : (X : Matrix (Fin 3) (Fin 3) F) =
        ((α l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [hl]
      exact (specialLinearGroupEquivStatedSL_coe 3 F X).symm
    have hY : ((e₀.symm (α ⟨_, hlbl⟩) : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = ((α ⟨_, hlbl⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      have h1 := specialLinearGroupEquivStatedSL_coe 3 F (e₀.symm (α ⟨_, hlbl⟩))
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1.symm
    rw [hX, hY]
    let lN : ↥N := ⟨l, hLN l.2⟩
    let mN : ↥N := ⟨_, hLN hlbl⟩
    have h1 : ∀ w, cHom β lN w = dact ((α l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) w :=
      fun w => cHom_of_mem hβ lN l.2 w
    have h2 : ∀ w, cHom β mN w =
        dact ((α ⟨_, hlbl⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) w :=
      fun w => cHom_of_mem hβ mN hlbl w
    have h3 : (b : ↥N) * lN = mN * (b : ↥N) := by
      apply Subtype.ext
      show ((b : ↥N) : G) * l = ((b : ↥N) : G) * l * ((b : ↥N) : G)⁻¹ * ((b : ↥N) : G)
      group
    show cHom β (b : ↥N) (dact _ v) = dact _ (cHom β (b : ↥N) v)
    rw [← h1, ← h2, ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, ← map_mul, h3]
  obtain ⟨hbound, heq⟩ := card_mul_card_fixPts_le hadd hnorm hcomm hinv
  set fx := Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) with hfx
  have hkerV : ∀ b : ↥B', b ∈ φ.ker → (((b : ↥N) : G)) ∈ V := by
    intro b hb
    have h1 : cHom β (b : ↥N) = 1 := hb
    rw [cHom_eq_one_iff] at h1
    exact ⟨hBG b.2, h1⟩
  set C := V ⊓ Subgroup.centralizer (B : Set G) with hC
  have hkerC : Nat.card φ.ker ≤ Nat.card C :=
    Nat.card_le_card_of_injective
      (fun x : ↥φ.ker => (⟨(((x : ↥B') : ↥N) : G), hkerV x x.2,
        Subgroup.mem_centralizer_iff.mpr fun y hy => hcommB _ hy _ (x : ↥B').2⟩ : ↥C))
      (fun x y hxy => Subtype.ext (Subtype.ext (Subtype.ext
        (congrArg (fun z : ↥C => (z : G)) hxy))))
  have hQCfix : Nat.card ↥(Q ⊓ C) ≤ fx := by
    refine Nat.card_le_card_of_injective
      (fun u : ↥(Q ⊓ C) => (⟨crd β ⟨u, u.2.1⟩, ?_⟩ :
        ↥(fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))))) fun x y hxy => ?_
    · rintro _ ⟨c, rfl⟩
      show cHom β (c : ↥N) (crd β _) = _
      rw [cHom_apply, cAct_crd]
      congr 1
      apply Subtype.ext
      show ((c : ↥N) : G) * (u : G) * ((c : ↥N) : G)⁻¹ = u
      have hcu : ((c : ↥N) : G) * (u : G) = (u : G) * ((c : ↥N) : G) :=
        Subgroup.mem_centralizer_iff.mp u.2.2.2 _ c.2
      rw [hcu]
      group
    · have h1 := crd_injective β (congrArg Subtype.val hxy)
      exact Subtype.ext (congrArg (fun z : ↥Q => (z : G)) h1)
  have hcardB' : Nat.card B' = Nat.card φ.ker * Nat.card E := by
    rw [hE, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, mul_comm]
  have hQcard : Nat.card Q = Nat.card F ^ 6 := by
    rw [Nat.card_congr (β.toEquiv.trans Multiplicative.toAdd), card_pairs]
  have hCrel : Q.relIndex C * Nat.card ↥(Q ⊓ C) = Nat.card C := Subgroup.relIndex_mul_card Q C
  have hVrel : Q.relIndex V * Nat.card Q = Nat.card V := by
    have h := Subgroup.relIndex_mul_card Q V
    rwa [inf_eq_left.mpr hQV] at h
  have hrel : Q.relIndex C ≤ Q.relIndex V :=
    Subgroup.relIndex_le_of_le_right inf_le_left Subgroup.index_ne_zero_of_finite
  have hle : Nat.card B ≤ Q.relIndex V * (Nat.card E * fx) := by
    calc Nat.card B = Nat.card φ.ker * Nat.card E := by rw [hcardB, hcardB']
      _ ≤ Nat.card C * Nat.card E := Nat.mul_le_mul_right _ hkerC
      _ = Q.relIndex C * Nat.card ↥(Q ⊓ C) * Nat.card E := by rw [hCrel]
      _ ≤ Q.relIndex V * fx * Nat.card E :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul hrel hQCfix)
      _ = Q.relIndex V * (Nat.card E * fx) := by ring
  have hVq : Nat.card V = Q.relIndex V * Nat.card F ^ 6 := by rw [← hVrel, hQcard]
  refine ⟨hle.trans (by rw [hVq]; exact Nat.mul_le_mul_left _ hbound), fun hBV => ?_⟩
  have hrelpos : 0 < Q.relIndex V := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hE6 : Nat.card E * fx = Nat.card F ^ 6 := by
    refine le_antisymm hbound ?_
    have h1 : Q.relIndex V * Nat.card F ^ 6 ≤ Q.relIndex V * (Nat.card E * fx) := by
      rw [← hVq, ← hBV]
      exact hle
    exact Nat.le_of_mul_le_mul_left h1 hrelpos
  obtain ⟨hdiag, hEcases⟩ := heq hE6
  by_cases hEbot : E = ⊥
  ·
    left
    have hBV' : B ≤ V := by
      intro b hb
      have h1 : φ ⟨⟨b, hBN hb⟩, hb⟩ = 1 := by
        have : φ ⟨⟨b, hBN hb⟩, hb⟩ ∈ E := ⟨_, rfl⟩
        rw [hEbot] at this
        exact this
      exact hkerV ⟨⟨b, hBN hb⟩, hb⟩ h1
    exact Subgroup.eq_of_le_of_card_ge hBV' hBV.ge
  ·
    right
    obtain ⟨e, he, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hEbot (eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hcon x hx))
    obtain ⟨b, rfl⟩ := he
    obtain ⟨X, hX⟩ := hdiag ⟨b, rfl⟩
    obtain ⟨l, hl⟩ := hα.1 (e₀ X)
    have hlX : slNat α l = X := by
      show (specialLinearGroupEquivStatedSL 3 F).symm (α l) = X
      rw [hl]
      exact MulEquiv.symm_apply_apply _ _
    have hX1 : X ≠ 1 := by
      intro h
      apply he1
      refine Equiv.ext fun v => ?_
      rw [hX v, h, Matrix.SpecialLinearGroup.coe_one, dact_one]
      rfl
    have hXX : X * X = 1 := by
      apply burnsideC135_eq_one_of_dact
      intro v
      have h1 := congrArg (fun f : Equiv.Perm (Fin 2 → Fin 3 → F) => f v) (hinv (φ b) ⟨b, rfl⟩)
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h1
      rw [hX, hX] at h1
      rw [Matrix.SpecialLinearGroup.coe_mul, ← dact_dact]
      exact h1
    let lN : ↥N := ⟨l, hLN l.2⟩
    have h1 : cHom β (b : ↥N) = cHom β lN := by
      refine Equiv.ext fun v => ?_
      rw [show cHom β (b : ↥N) v = φ b v from rfl, hX v, cHom_of_mem hβ lN l.2 v, hl]
      rfl
    have h2 : cHom β (lN⁻¹ * (b : ↥N)) = 1 := by
      rw [map_mul, h1, map_inv, inv_mul_cancel]
    rw [cHom_eq_one_iff] at h2
    have hlb : (l : G)⁻¹ * ((b : ↥N) : G) ∈ V :=
      ⟨G₀.mul_mem (G₀.inv_mem (hLG l.2)) (hBG b.2), h2⟩
    have hCQ : C ≤ Q := by
      intro c hc
      have hcb : c * ((b : ↥N) : G) = ((b : ↥N) : G) * c :=
        (Subgroup.mem_centralizer_iff.mp hc.2 _ b.2).symm
      have hclb := hVab c hc.1 _ hlb
      refine hcoc c hc.1 l (hlX ▸ hX1) (by rw [hlX]; exact hXX) ?_
      have e1 : (l : G) = ((b : ↥N) : G) * ((l : G)⁻¹ * ((b : ↥N) : G))⁻¹ := by group
      rw [e1]
      calc ((b : ↥N) : G) * ((l : G)⁻¹ * ((b : ↥N) : G))⁻¹ * c =
            ((b : ↥N) : G) * (((l : G)⁻¹ * ((b : ↥N) : G))⁻¹ * c) := by group
        _ = ((b : ↥N) : G) * (c * ((l : G)⁻¹ * ((b : ↥N) : G))⁻¹) := by
            congr 1
            rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hclb, mul_assoc, mul_inv_cancel, mul_one]
        _ = (((b : ↥N) : G) * c) * ((l : G)⁻¹ * ((b : ↥N) : G))⁻¹ := by group
        _ = c * ((b : ↥N) : G) * ((l : G)⁻¹ * ((b : ↥N) : G))⁻¹ := by rw [← hcb]
        _ = c * (((b : ↥N) : G) * ((l : G)⁻¹ * ((b : ↥N) : G))⁻¹) := by group
    have hrel1 : Q.relIndex C = 1 := Subgroup.relIndex_eq_one.mpr hCQ
    have hVQ : Nat.card V ≤ Nat.card Q := by
      calc Nat.card V = Nat.card B := hBV.symm
        _ = Nat.card φ.ker * Nat.card E := by rw [hcardB, hcardB']
        _ ≤ Nat.card C * Nat.card E := Nat.mul_le_mul_right _ hkerC
        _ = Nat.card ↥(Q ⊓ C) * Nat.card E := by rw [← hCrel, hrel1, one_mul]
        _ ≤ fx * Nat.card E := Nat.mul_le_mul_right _ hQCfix
        _ = Nat.card Q := by rw [mul_comm, hE6, hQcard]
    exact (Subgroup.eq_of_le_of_card_ge hQV hVQ).symm

theorem burnsideC135_centralizer_eq_one [Fintype F] (hF2 : Fintype.card F = 2)
    {R₀ S : Subgroup G} (hMS : IsMSPair G₀ R₀) (hS : IsSylowTwoOf S G₀)
    (hα : IsModO2Surj L α) (hLG : L ≤ G₀) (hGL : G₀ ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) (hN : IsSumOfNaturalModulesVia L (c134Q G₀ L) ⊥ α false 2)
    (hCL : G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    G₀ ⊓ Subgroup.centralizer (c134Q G₀ L : Set G) = c134Q G₀ L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime hF2
  have hQG : c134Q G₀ L ≤ G₀ := (c134Q_le hGL).trans hLG
  have hGQ : G₀ ≤ Subgroup.normalizer (c134Q G₀ L : Set G) := le_normalizer_c134Q hGL
  have hVel := burnsideC135_isElemAbelian_centralizer hα hLG hGL hperf two_ne_zero hN hCL
  have hcoc : ∀ v ∈ G₀ ⊓ Subgroup.centralizer (c134Q G₀ L : Set G), ∀ l : ↥L, slNat α l ≠ 1 →
      slNat α l * slNat α l = 1 → (l : G) * v = v * l → v ∈ c134Q G₀ L :=
    fun v hv l hl1 hl2 hlv =>
      burnsideC135_mem_of_commute_invol hF2 hα hLG hGL hperf two_ne_zero hN hCL hv hl1 hl2 hlv
  have hQab : ∀ {x y : G}, x ∈ c134Q G₀ L → y ∈ c134Q G₀ L → x * y = y * x := fun hx hy =>
    mul_comm_of_isSumOfNaturalModulesVia hN hx hy
  set Q := c134Q G₀ L with hQdef
  set V := G₀ ⊓ Subgroup.centralizer (Q : Set G) with hV
  obtain ⟨-, -, β₀, hβs, hβk, hβeq⟩ := hN
  have hβinj : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  let β : ↥Q ≃* Multiplicative (Fin 2 → Fin 3 → F) := MulEquiv.ofBijective β₀ ⟨hβinj, hβs⟩
  have hβ : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β u) i) := by
    intro a u v huv i
    have h := hβeq a u v huv i
    have hb : ∀ w, β w = β₀ w := fun _ => rfl
    rw [hb, hb]
    simpa [moduleAct] using h
  have hQV : Q ≤ V := fun x hx =>
    ⟨hQG hx, Subgroup.mem_centralizer_iff.mpr fun y hy => hQab hy hx⟩
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbound := fun {B : Subgroup G} (hBG : B ≤ G₀) (hB : IsElemAbelian 2 B) =>
    burnsideC135_card_le_one hα hLG hGL hGQ hQV hVab hcoc β hβ hBG hB
  have hGV : G₀ ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg) (mem_normalizer_centralizer_of_mem (hGQ hg))
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hVel.2 x x.2)⟩
  have hVO : V ≤ pCoreOf 2 G₀ := le_pCoreOf_of_le_normalizer 2 inf_le_left hGV hVp
  have hQcard : Nat.card Q = Nat.card F ^ 6 := by
    rw [Nat.card_congr (β.toEquiv.trans Multiplicative.toAdd), card_pairs]
  have hV1 : V ≠ ⊥ := by
    intro h
    have h1 : Q ≤ ⊥ := h ▸ hQV
    have h2 : Nat.card Q = 1 := by
      rw [le_bot_iff.mp h1, Subgroup.card_bot]
    rw [hQcard] at h2
    have h3 := two_le_card_field (F := F)
    have h4 : 2 ^ 6 ≤ Nat.card F ^ 6 := Nat.pow_le_pow_left h3 6
    omega
  obtain ⟨A, hA, hAV⟩ := exists_isMaxElemAbelian_ne hMS hS hVO hGV hV1 hVel
    fun B hBG hB => (hbound hBG hB).1
  have hVS : V ≤ S := hVO.trans (pCoreOf_two_le_of_isSylowTwoOf hS)
  have hAcard : Nat.card A = Nat.card V :=
    le_antisymm (hbound (hA.1.trans hS.1) hA.2.1).1 (hA.2.2 V hVS hVel)
  rcases (hbound (hA.1.trans hS.1) hA.2.1).2 hAcard with h | h
  · exact absurd h hAV
  · exact h

theorem burnsideC135_pCoreOf_eq_one [Fintype F] (hF2 : Fintype.card F = 2)
    {R₀ S : Subgroup G} (hMS : IsMSPair G₀ R₀) (hS : IsSylowTwoOf S G₀)
    (hα : IsModO2Surj L α) (hLG : L ≤ G₀) (hGL : G₀ ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) (hN : IsSumOfNaturalModulesVia L (c134Q G₀ L) ⊥ α false 2)
    (hCL : G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    pCoreOf 2 L = c134Q G₀ L := by
  have hV := burnsideC135_centralizer_eq_one hF2 hMS hS hα hLG hGL hperf hN hCL
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

theorem burnsideC135_c136_of_centralizer [Fintype F] [CharP F 2] {R₀ S : Subgroup G}
    (hMS : IsMSPair G₀ R₀) (hα : IsModO2Surj L α) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hS : IsSylowTwoOf S G₀)
    (hN : IsSumOfNaturalModulesVia L (c134Q G₀ L) ⊥ α false 2)
    (hQ1 : G₀ ⊓ Subgroup.centralizer (c134Q G₀ L : Set G) = c134Q G₀ L)
    (hQO : pCoreOf 2 L = c134Q G₀ L) :
    G₀ ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) = pCoreOf 2 L ∧
      IsMaxElemAbelian S (pCoreOf 2 L) ∧
      ∃ A : Subgroup G, A ≤ L ∧ IsMaxElemAbelian S A ∧
        (∀ B : Subgroup G, IsMaxElemAbelian S B → B = pCoreOf 2 L ∨ B = A) ∧
        Nat.card ↥(A ⊓ pCoreOf 2 L) = Nat.card F ^ 4 := by
  classical
  set Q := c134Q G₀ L with hQdef
  obtain ⟨-, -, β₀, hβs, hβk, hβeq⟩ := hN
  have hβinj : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  let β : ↥Q ≃* Multiplicative (Fin 2 → Fin 3 → F) := MulEquiv.ofBijective β₀ ⟨hβinj, hβs⟩
  have hβ : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β u) i) := by
    intro a u v huv i
    have h := hβeq a u v huv i
    have hb : ∀ w, β w = β₀ w := fun _ => rfl
    rw [hb, hb]
    simpa [moduleAct] using h
  have hQL : Q ≤ L := c134Q_le hGL
  have hGQ : G₀ ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_c134Q hGL
  have hbound : ∀ {B : Subgroup G}, B ≤ G₀ → IsElemAbelian 2 B →
      Nat.card B ≤ Nat.card F ^ 6 ∧
        (Nat.card B = Nat.card F ^ 6 →
          B = Q ∨ (B ≤ L ∧ Nat.card ↥(B ⊓ Q) = Nat.card F ^ 4 ∧
            Nat.card ↥(Q ⊓ Subgroup.centralizer (B : Set G)) = Nat.card F ^ 4)) :=
    fun hBG hB => card_le_of_c136 hα hLG hGL hQL hGQ hQ1 β hβ hBG hB
  have hQcard : Nat.card Q = Nat.card F ^ 6 := by
    rw [Nat.card_congr (β.toEquiv.trans Multiplicative.toAdd), card_pairs]
  have hQel : IsElemAbelian 2 Q := by
    refine ⟨⟨⟨fun x y => β.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩, fun x hx => ?_⟩
    have h1 : β (⟨x, hx⟩ ^ 2) = 1 := by
      rw [map_pow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_nsmul]
      exact CharTwo.add_self_eq_zero _
    have h2 : (⟨x, hx⟩ : ↥Q) ^ 2 = 1 := β.injective (h1.trans (map_one β).symm)
    have h3 := congrArg Subtype.val h2
    simpa using h3
  have hQO2 : Q ≤ pCoreOf 2 G₀ :=
    commutator_le_left_of_le_normalizer (hLG.trans (le_normalizer_pCoreOf 2 G₀))
  have hQS : Q ≤ S := hQO2.trans (pCoreOf_two_le_of_isSylowTwoOf hS)
  have hQmax : IsMaxElemAbelian S Q :=
    ⟨hQS, hQel, fun B hBS hB => (hbound (hBS.trans hS.1) hB).1.trans hQcard.ge⟩
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQcard
    have h2 := two_le_card_field (F := F)
    have h3 : 2 ^ 6 ≤ Nat.card F ^ 6 := Nat.pow_le_pow_left h2 6
    omega
  obtain ⟨A, hAmax, hAQ⟩ := exists_isMaxElemAbelian_ne hMS hS hQO2 hGQ hQne hQel
    fun B hBG hB => (hbound hBG hB).1.trans hQcard.ge
  have hstruct : ∀ B : Subgroup G, IsMaxElemAbelian S B → B ≠ Q →
      B ≤ L ∧ Nat.card B = Nat.card F ^ 6 ∧ Nat.card ↥(B ⊓ Q) = Nat.card F ^ 4 ∧
        Nat.card ↥(Q ⊓ Subgroup.centralizer (B : Set G)) = Nat.card F ^ 4 := by
    intro B hB hBQ
    have hcard : Nat.card B = Nat.card F ^ 6 :=
      le_antisymm (hbound (hB.1.trans hS.1) hB.2.1).1 (hQcard ▸ hB.2.2 Q hQS hQel)
    rcases (hbound (hB.1.trans hS.1) hB.2.1).2 hcard with h | ⟨h1, h2, h3⟩
    · exact absurd h hBQ
    · exact ⟨h1, hcard, h2, h3⟩
  obtain ⟨hAL, hAcard, hAQcard, hACcard⟩ := hstruct A hAmax hAQ
  refine ⟨?_, ?_, A, hAL, hAmax, fun B hB => ?_, ?_⟩
  · rw [hQO]
    exact hQ1
  · rw [hQO]
    exact hQmax
  · rw [hQO]
    by_cases hBQ : B = Q
    · exact Or.inl hBQ
    · right
      obtain ⟨hBL, hBcard, hBQcard, hBCcard⟩ := hstruct B hB hBQ
      exact eq_of_offenders_c136 hα hQO β hβ hS.2.1 (le_inf hB.1 hBL) (le_inf hAmax.1 hAL)
        hB.2.1 hAmax.2.1 hBcard hAcard hBQcard hAQcard hBCcard hACcard
  · rw [hQO, hAQcard]

theorem burnsideC135_lemmaC136_one [Fintype F] (hF2 : Fintype.card F = 2)
    {R₀ S : Subgroup G} (hMS : IsMSPair G₀ R₀) (hL : L ∈ cComp G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hα : IsModO2Surj L α)
    (hS : IsSylowTwoOf S G₀) (hCL : G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hN : IsSumOfNaturalModulesVia L (c134Q G₀ L) ⊥ α false 2) :
    G₀ ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) = pCoreOf 2 L ∧
      IsMaxElemAbelian S (pCoreOf 2 L) ∧
      ∃ A : Subgroup G, A ≤ L ∧ IsMaxElemAbelian S A ∧
        (∀ B : Subgroup G, IsMaxElemAbelian S B → B = pCoreOf 2 L ∨ B = A) ∧
        Nat.card ↥(A ⊓ pCoreOf 2 L) = 2 ^ (4 * 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime hF2
  have hLG : L ≤ G₀ := le_of_mem_cComp hL
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hL
  have hQ1 := burnsideC135_centralizer_eq_one hF2 hMS hS hα hLG hGL hperf hN hCL
  have hQO := burnsideC135_pCoreOf_eq_one hF2 hMS hS hα hLG hGL hperf hN hCL
  obtain ⟨h1, h2, A, hAL, hA, hAll, hcard⟩ :=
    burnsideC135_c136_of_centralizer hMS hα hLG hGL hS hN hQ1 hQO
  refine ⟨h1, h2, A, hAL, hA, hAll, ?_⟩
  rw [hcard, Nat.card_eq_fintype_card, hF2]

end One

end CFSG.ASVolI

end
