module

public import CFSG.RankThree.PartOne.S12.Node126
public import CFSG.RankThree.PartOne.S12.LinAlg
public import CFSG.RankThree.PartOne.S12.BaseNodes
import CFSG.RankThree.PartOne.S12.RowFacts
import CFSG.RankThree.PartOne.S12.Sec126a
import CFSG.RankThree.PartOne.S12.Sec127
import CFSG.RankThree.PartOne.S12.Sec12Three

public section

namespace CFSG.RankThree.PartOne

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Sec126g

@[expose] def fixedSpace {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (Y : Subgroup (V ≃ₗ[ZMod p] V)) : Submodule (ZMod p) V where
  carrier := {x | ∀ y ∈ Y, y x = x}
  add_mem' {a b} ha hb y hy := by rw [map_add, ha y hy, hb y hy]
  zero_mem' y _ := map_zero y
  smul_mem' c x hx y hy := by rw [map_smul, hx y hy]

theorem fixedSpace_invariant {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {Y Γ : Subgroup (V ≃ₗ[ZMod p] V)}
    (hYn : ∀ g ∈ Γ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ Γ)
    {x : V} (hx : x ∈ fixedSpace Y) : g x ∈ fixedSpace Y := by
  intro y hy
  have hy' : g⁻¹ * y * g ∈ Y := by simpa using hYn g⁻¹ (inv_mem hg) y hy
  have h := hx _ hy'
  calc y (g x) = g ((g⁻¹ * y * g) x) := by simp [LinearEquiv.mul_apply]
    _ = g x := by rw [h]

theorem exists_line_of_fixed {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {Γ Y : Subgroup (V ≃ₗ[ZMod p] V)}
    {U : Submodule (ZMod p) V}
    (hU : Module.finrank (ZMod p) U + 1 = Module.finrank (ZMod p) V)
    (hUinv : ∀ g ∈ Γ, ∀ b ∈ U, g b ∈ U)
    (hirr : ∀ B' ≤ U, (∀ g ∈ Γ, ∀ b ∈ B', g b ∈ B') → B' = ⊥ ∨ B' = U)
    (hfaith : ∀ g ∈ Γ, (∀ b ∈ U, g b = b) → g = 1)
    (hYΓ : Y ≤ Γ) (hYn : ∀ g ∈ Γ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (hY1 : Y ≠ ⊥)
    {v : V} (hvU : v ∉ U) (hvY : ∀ y ∈ Y, y v = v) :
    ∃ ℓ : Submodule (ZMod p) V, Module.finrank (ZMod p) ℓ = 1 ∧ Disjoint ℓ U ∧
      ∀ g ∈ Γ, ∀ x ∈ ℓ, g x ∈ ℓ := by
  have hCU : fixedSpace Y ⊓ U = ⊥ := by
    rcases hirr (fixedSpace Y ⊓ U) inf_le_right
      (fun g hg b hb => ⟨fixedSpace_invariant hYn hg hb.1, hUinv g hg b hb.2⟩) with h | h
    · exact h
    · exfalso
      apply hY1
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      exact hfaith y (hYΓ hy) fun b hb => (inf_eq_right.mp h hb) y hy
  refine ⟨fixedSpace Y, ?_, disjoint_iff.mpr hCU, fun g hg x hx => fixedSpace_invariant hYn hg hx⟩
  have hv0 : v ≠ 0 := fun h0 => hvU (h0 ▸ U.zero_mem)
  have hle : Module.finrank (ZMod p) (fixedSpace Y) ≤ 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace Y) U
    rw [hCU, finrank_bot] at h1
    have h2 := Submodule.finrank_le (fixedSpace Y ⊔ U)
    omega
  have hpos : 0 < Module.finrank (ZMod p) (fixedSpace Y) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨v, hvY⟩, fun h0 => hv0 (congrArg Subtype.val h0)⟩
  omega

theorem eq_neg_of_central_involution {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {Γ Λ : Subgroup (V ≃ₗ[ZMod p] V)}
    {U : Submodule (ZMod p) V} (hΛΓ : Λ ≤ Γ) (hUinv : ∀ g ∈ Γ, ∀ b ∈ U, g b ∈ U)
    (hirr : ∀ B' ≤ U, (∀ l ∈ Λ, ∀ b ∈ B', l b ∈ B') → B' = ⊥ ∨ B' = U)
    (hfaith : ∀ g ∈ Γ, (∀ b ∈ U, g b = b) → g = 1)
    {s : V ≃ₗ[ZMod p] V} (hsΛ : s ∈ Λ) (hs1 : s ≠ 1) (hss : s * s = 1)
    (hcent : ∀ l ∈ Λ, l * s = s * l) : ∀ b ∈ U, s b = -b := by
  have hss' : ∀ x, s (s x) = x := fun x => by
    simpa using congrArg (fun t : V ≃ₗ[ZMod p] V => t x) hss
  have hKinv : ∀ l ∈ Λ, ∀ b ∈ (LinearMap.eqLocus (s : V →ₗ[ZMod p] V) LinearMap.id ⊓ U),
      l b ∈ (LinearMap.eqLocus (s : V →ₗ[ZMod p] V) LinearMap.id ⊓ U) := by
    intro l hl b hb
    have h0 := Submodule.mem_inf.mp hb
    have h1 : s b = b := h0.1
    have h2 := congrArg (fun t : V ≃ₗ[ZMod p] V => t b) (hcent l hl)
    simp only [LinearEquiv.mul_apply] at h2
    refine Submodule.mem_inf.mpr ⟨?_, hUinv l (hΛΓ hl) b h0.2⟩
    show s (l b) = l b
    rw [← h2, h1]
  rcases hirr _ inf_le_right hKinv with hK | hK
  · intro b hb
    have h1 : b + s b ∈ (LinearMap.eqLocus (s : V →ₗ[ZMod p] V) LinearMap.id ⊓ U) := by
      refine Submodule.mem_inf.mpr ⟨?_, U.add_mem hb (hUinv s (hΛΓ hsΛ) b hb)⟩
      show s (b + s b) = b + s b
      rw [map_add, hss', add_comm]
    rw [hK, Submodule.mem_bot] at h1
    exact eq_neg_of_add_eq_zero_right h1
  · exact absurd (hfaith s (hΛΓ hsΛ) fun b hb => (Submodule.mem_inf.mp (hK.ge hb)).1) hs1

theorem central_of_neg {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {Γ : Subgroup (V ≃ₗ[ZMod p] V)} {U : Submodule (ZMod p) V}
    (hUinv : ∀ g ∈ Γ, ∀ b ∈ U, g b ∈ U) (hfaith : ∀ g ∈ Γ, (∀ b ∈ U, g b = b) → g = 1)
    {s : V ≃ₗ[ZMod p] V} (hsΓ : s ∈ Γ) (hss : s * s = 1) (hneg : ∀ b ∈ U, s b = -b) :
    ∀ g ∈ Γ, g * s = s * g := by
  intro g hg
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have h1 : g * s * g⁻¹ * s⁻¹ = 1 := by
    apply hfaith _ (Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hg hsΓ) (Γ.inv_mem hg)) (Γ.inv_mem hsΓ))
    intro b hb
    have hgb : g⁻¹ b ∈ U := hUinv g⁻¹ (Γ.inv_mem hg) b hb
    calc (g * s * g⁻¹ * s⁻¹) b = g (s (g⁻¹ (s b))) := by simp [LinearEquiv.mul_apply, hsinv]
      _ = b := by rw [hneg b hb, map_neg, map_neg, hneg _ hgb, neg_neg]; simp
  calc g * s = (g * s * g⁻¹ * s⁻¹) * (s * g) := by group
    _ = s * g := by rw [h1, one_mul]

theorem mem_span_of_central {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {U : Submodule (ZMod p) V} {v : V}
    (hcompl : IsCompl (Submodule.span (ZMod p) {v}) U) (h2 : (2 : ZMod p) ≠ 0)
    {s g : V ≃ₗ[ZMod p] V} (hsv : s v = v) (hneg : ∀ b ∈ U, s b = -b)
    (hcomm : g * s = s * g) : g v ∈ Submodule.span (ZMod p) {v} := by
  have hx : g v ∈ Submodule.span (ZMod p) {v} ⊔ U := by
    rw [hcompl.sup_eq_top]; trivial
  obtain ⟨y, hy, b, hb, hyb⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have h1 : s (g v) = g v := by
    have := congrArg (fun t : V ≃ₗ[ZMod p] V => t v) hcomm
    simp only [LinearEquiv.mul_apply] at this
    rw [← this, hsv]
  rw [← hyb, map_add, map_smul, hsv, hneg b hb] at h1
  have hb0 : b = 0 := by
    have h3 : (2 : ZMod p) • b = 0 := by
      rw [two_smul]
      have := add_left_cancel h1
      calc b + b = -b + b := by rw [this]
        _ = 0 := neg_add_cancel b
    exact (smul_eq_zero.mp h3).resolve_left h2
  rw [← hyb, hb0, add_zero]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self v)

theorem line_invariant_of_central_involution {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {Γ Λ : Subgroup (V ≃ₗ[ZMod p] V)} {U : Submodule (ZMod p) V} {v : V}
    (hΛΓ : Λ ≤ Γ) (hUinv : ∀ g ∈ Γ, ∀ b ∈ U, g b ∈ U)
    (hirr : ∀ B' ≤ U, (∀ l ∈ Λ, ∀ b ∈ B', l b ∈ B') → B' = ⊥ ∨ B' = U)
    (hfaith : ∀ g ∈ Γ, (∀ b ∈ U, g b = b) → g = 1)
    (hcompl : IsCompl (Submodule.span (ZMod p) {v}) U) (h2 : (2 : ZMod p) ≠ 0)
    {s : V ≃ₗ[ZMod p] V} (hsΛ : s ∈ Λ) (hs1 : s ≠ 1) (hss : s * s = 1)
    (hcent : ∀ l ∈ Λ, l * s = s * l) (hsv : s v = v) :
    ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} := fun g hg =>
  have hneg := eq_neg_of_central_involution hΛΓ hUinv hirr hfaith hsΛ hs1 hss hcent
  mem_span_of_central hcompl h2 hsv hneg
    (central_of_neg hUinv hfaith (hΛΓ hsΛ) hss hneg g hg)

section Coordinates

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {n : ℕ} {E : Subgroup G}
  (f : Multiplicative (Fin n → ZMod p) ≃* E)

theorem isCompl_bsub {c : G} {B : Subgroup G} {v : Fin n → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c)
    (hcE : Subgroup.zpowers c ≤ E) (hBE : B ≤ E)
    (hsup : E = Subgroup.zpowers c ⊔ B) (hinf : Subgroup.zpowers c ⊓ B = ⊥) :
    IsCompl (Submodule.span (ZMod p) {v}) (LinAlg.bsub f B) := by
  rw [← Sec127.bsub_zpowers_eq_span f hv]
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff, ← Sec127.bsub_inf, hinf, LinAlg.bsub_bot]
  · rw [codisjoint_iff, ← Sec127.bsub_sup f hcE hBE, ← hsup, LinAlg.bsub_self]

theorem invariant_bsub {B : Subgroup G} (hBE : B ≤ E) (hBinv : torusInvariant E ⊤ B) :
    ∀ g ∈ (torusWeyl E).map (LinAlg.coordHom f), ∀ b ∈ LinAlg.bsub f B,
      g b ∈ LinAlg.bsub f B := by
  intro g hg b hb
  obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
  exact (LinAlg.torusInvariant_top_iff f hBE).mp hBinv φ hφ (Submodule.mem_map_of_mem hb)

theorem no_invariant_line {B : Subgroup G}
    (hdim : Module.finrank (ZMod p) (LinAlg.bsub f B) + 1 = n) (hBE : B ≤ E)
    (hno : ∀ C : Subgroup G, C ≤ E → torusInvariant E ⊤ C → C ⊓ B = ⊥ → C ⊔ B = E → False) :
    ¬ ∃ ℓ : Submodule (ZMod p) (Fin n → ZMod p), Module.finrank (ZMod p) ℓ = 1 ∧
      Disjoint ℓ (LinAlg.bsub f B) ∧
      ∀ g ∈ (torusWeyl E).map (LinAlg.coordHom f), ∀ x ∈ ℓ, g x ∈ ℓ := by
  rintro ⟨ℓ, hℓ1, hℓU, hℓinv⟩
  obtain ⟨C, hCE, rfl⟩ := LinAlg.exists_bsub_eq f ℓ
  have hsupℓ : LinAlg.bsub f C ⊔ LinAlg.bsub f B = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinAlg.bsub f C) (LinAlg.bsub f B)
    rw [disjoint_iff.mp hℓU, finrank_bot] at h1
    rw [Module.finrank_fin_fun]
    omega
  refine hno C hCE ?_ ?_ ?_
  · rw [LinAlg.torusInvariant_top_iff f hCE]
    intro φ hφ y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    exact hℓinv _ (Subgroup.mem_map_of_mem _ hφ) z hz
  · apply (LinAlg.bsub_injective f (inf_le_left.trans hCE) bot_le).mp
    rw [Sec127.bsub_inf, disjoint_iff.mp hℓU, LinAlg.bsub_bot]
  · apply (LinAlg.bsub_injective f (sup_le hCE hBE) le_rfl).mp
    rw [Sec127.bsub_sup f hCE hBE, hsupℓ, LinAlg.bsub_self]

theorem irreducible_bsub {L B : Subgroup G} (hBE : B ≤ E)
    (hirrL : ∀ B' : Subgroup G, B' ≤ B → torusInvariant E L B' → B' = ⊥ ∨ B' = B) :
    ∀ U' ≤ LinAlg.bsub f B,
      (∀ l ∈ (torusImage E L).map (LinAlg.coordHom f), ∀ b ∈ U', l b ∈ U') →
      U' = ⊥ ∨ U' = LinAlg.bsub f B := by
  intro U' hU' hinv
  obtain ⟨C, hCE, rfl⟩ := LinAlg.exists_bsub_eq f U'
  have hCB : C ≤ B := (LinAlg.bsub_le_bsub_iff f hCE hBE).mp hU'
  have hCL : torusInvariant E L C := by
    rw [LinAlg.torusInvariant_iff f L hCE]
    intro φ hφ y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    exact hinv _ (Subgroup.mem_map_of_mem _ hφ) z hz
  rcases hirrL C hCB hCL with rfl | rfl
  · exact Or.inl (LinAlg.bsub_bot f)
  · exact Or.inr rfl

include f in
theorem core [Finite G] {A L : Subgroup G} {c : G} (h : Sec12Hyp G p A c L E)
    (hLAF : LAFaithful p) (hLA : LA126) (hD : ExtDickson) (hB : ExtBloomPrime)
    (hJP : ExtJonesParshall) (hKF : KF126)
    (hcore : CFSG.pCore p ↥(torusWeyl E) = ⊥) {B : Subgroup G} (hBinv : torusInvariant E ⊤ B)
    (hBE : B ≤ E) (hsup : E = Subgroup.zpowers c ⊔ B) (hinf : Subgroup.zpowers c ⊓ B = ⊥)
    (hirrL : ∀ B' : Subgroup G, B' ≤ B → torusInvariant E L B' → B' = ⊥ ∨ B' = B)
    (hno : ∀ C : Subgroup G, C ≤ E → torusInvariant E ⊤ C → C ⊓ B = ⊥ → C ⊔ B = E → False)
    (h11 : RowModel p L 11 → False) (hn : n = 3 ∨ n = 4)
    {r : ℕ} (hr12 : r ≤ 12) (hmodel : RowModel p L r)
    (hweyl : RowWeylIso E (torusImage E L) r) (hr8 : r ≤ 8 → E = A) :
    p = 5 ∧ RowModel p L 9 ∧ Nat.card E = p ^ 4 ∧ E ≠ A ∧ RowWeylIso E (torusImage E L) 9 := by
  have h5 : 5 ≤ p := Sec12Three.five_le h
  have hcE : c ∈ E := h.A_le_E h.c_mem
  obtain ⟨v, hv⟩ := Sec127.exists_vec f hcE
  have hv0 : v ≠ 0 := Sec127.vec_ne_zero f h.c_ne_one hv
  have hczE : Subgroup.zpowers c ≤ E := Subgroup.zpowers_le.mpr hcE
  have hdim : Module.finrank (ZMod p) (LinAlg.bsub f B) + 1 = n :=
    Sec127.finrank_bsub_add_one f hv hv0 hczE hBE hsup hinf
  have hVdim : Module.finrank (ZMod p) (Fin n → ZMod p) = n := Module.finrank_fin_fun _
  have hdimV : Module.finrank (ZMod p) (LinAlg.bsub f B) + 1 =
      Module.finrank (ZMod p) (Fin n → ZMod p) := by rw [hVdim]; exact hdim
  have hcompl := isCompl_bsub f hv hczE hBE hsup hinf
  have hUinv := invariant_bsub f hBE hBinv
  have hΓcore := Sec127.pCore_map_eq_bot f hcore
  have hnoline := no_invariant_line f hdim hBE hno
  have hfaith := hLAF (Fin n → ZMod p) ((torusWeyl E).map (LinAlg.coordHom f))
    (LinAlg.bsub f B) hdimV hUinv hΓcore hnoline
  have hirrΛ := irreducible_bsub f hBE hirrL
  have hΛΓ : (torusImage E L).map (LinAlg.coordHom f) ≤ (torusWeyl E).map (LinAlg.coordHom f) :=
    Subgroup.map_mono (Sec127.torusImage_le_torusWeyl E L)
  have hirrΓ : ∀ U' ≤ LinAlg.bsub f B,
      (∀ g ∈ (torusWeyl E).map (LinAlg.coordHom f), ∀ b ∈ U', g b ∈ U') →
      U' = ⊥ ∨ U' = LinAlg.bsub f B := fun U' hle hinv =>
    hirrΛ U' hle fun l hl b hb => hinv l (hΛΓ hl) b hb
  obtain ⟨hp5, hU3, Y, hYΓ, hYn, hY60, hYperf, -, -, -⟩ := hLA hD hB hJP hKF p h5 (Fin n → ZMod p)
    ((torusWeyl E).map (LinAlg.coordHom f)) (LinAlg.bsub f B) hdimV (by omega) hUinv hΓcore
    hfaith hirrΓ hnoline
  have hn4 : n = 4 := by omega
  have hcardE : Nat.card E = p ^ 4 := by rw [LinAlg.natCard_eq_pow_of_coords f, hn4]
  have hEA : E ≠ A := by
    intro hEA
    have h3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
    rw [hcardE] at h3
    exact absurd (Nat.pow_right_injective (by omega : 2 ≤ p) h3) (by norm_num)
  have hr9 : 9 ≤ r := by
    by_contra hlt
    exact hEA (hr8 (by omega))
  have hcomm := Sec127.fixes_of_mem_map f hv (Sec12Three.comm_c_L h)
  have hvU : v ∉ LinAlg.bsub f B := fun hvU =>
    hv0 (Submodule.disjoint_def.mp hcompl.disjoint v (Submodule.mem_span_singleton_self v) hvU)
  interval_cases r
  · exact ⟨hp5, hmodel, hcardE, hEA, hweyl⟩
  ·
    exfalso
    obtain ⟨z, hz, hz1, hzz, hzc⟩ := rowWeylIso_central_involution_of_ten hweyl
    have hsΛ : LinAlg.coordHom f z ∈ (torusImage E L).map (LinAlg.coordHom f) :=
      Subgroup.mem_map_of_mem _ hz
    have hs1 : LinAlg.coordHom f z ≠ 1 := fun h1 =>
      hz1 (LinAlg.coordHom_injective f (h1.trans (map_one _).symm))
    have hss : LinAlg.coordHom f z * LinAlg.coordHom f z = 1 := by
      rw [← map_mul, hzz, map_one]
    have hcent : ∀ l ∈ (torusImage E L).map (LinAlg.coordHom f),
        l * LinAlg.coordHom f z = LinAlg.coordHom f z * l := by
      intro l hl
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hl
      rw [← map_mul, ← map_mul, hzc g hg]
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h0
      have h0' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at h0'
      have := Nat.le_of_dvd (by norm_num) h0'
      omega
    have hline := line_invariant_of_central_involution hΛΓ hUinv hirrΛ hfaith hcompl h2 hsΛ hs1
      hss hcent (hcomm _ hsΛ)
    refine hnoline ⟨Submodule.span (ZMod p) {v}, finrank_span_singleton hv0, hcompl.disjoint, ?_⟩
    intro g hg x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul]
    exact Submodule.smul_mem _ a (hline g hg)
  · exact absurd hmodel h11
  ·
    exfalso
    obtain ⟨Λ0, hΛ0le, hΛ0perf, hΛ0card⟩ := rowWeylIso_perfect_subgroup_of_twelve hweyl
    have hperf : Group.IsPerfect ↥(Λ0.map (LinAlg.coordHom f)) :=
      Group.IsPerfect.map (LinAlg.coordHom f)
    have hΛ0Γ : Λ0.map (LinAlg.coordHom f) ≤ (torusWeyl E).map (LinAlg.coordHom f) :=
      (Subgroup.map_mono hΛ0le).trans hΛΓ
    have hΛ0Y : Λ0.map (LinAlg.coordHom f) ≤ Y := hYperf _ hΛ0Γ hperf
    have hcard' : Nat.card ↥(Λ0.map (LinAlg.coordHom f)) = 60 := by
      rw [Subgroup.card_map_of_injective (LinAlg.coordHom_injective f), hΛ0card]
    have hfin : Finite ↥Y := Nat.finite_of_card_ne_zero (by omega)
    have hΛ0eq : Λ0.map (LinAlg.coordHom f) = Y :=
      Subgroup.eq_of_le_of_card_ge hΛ0Y (by omega)
    have hYv : ∀ y ∈ Y, y v = v := by
      intro y hy
      rw [← hΛ0eq] at hy
      exact hcomm y (Subgroup.map_mono hΛ0le hy)
    have hY1 : Y ≠ ⊥ := fun hY => by rw [hY] at hY60; simp at hY60
    exact hnoline (exists_line_of_fixed hdimV hUinv hirrΓ hfaith hYΓ hYn hY1 hvU hYv)

end Coordinates

end Sec126g

theorem node126g_full_of_inputs (h123 : Node123) (h124 : Node124) (h124b : Node124b)
    (h125 : Node125) (hLAF : ∀ (p : ℕ) [Fact p.Prime], LAFaithful p) (hLA : LA126)
    (hD : ExtDickson) (hB : ExtBloomPrime) (hJP : ExtJonesParshall) (hKF : KF126) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec12Hyp G p A c L E → ¬ torusIrreducible E → ¬ torusWeylHasPCore p E →
        p = 5 ∧ RowModel p L 9 ∧ Nat.card E = p ^ 4 ∧ E ≠ A ∧
          RowWeylIso E (torusImage E L) 9 := by
  intro G _ _ p A c L E h hirr hcore
  have hpf : Fact p.Prime := ⟨h.prime⟩
  have hel := h.E_elem
  have hcore' : CFSG.pCore p ↥(torusWeyl E) = ⊥ := by
    by_contra hne
    exact hcore hne
  obtain ⟨hBinv, hB0, hBE', hBE, hsup, hinf⟩ := sec126_a h124 h125 h hirr
  obtain ⟨-, r, -, hr12, hmodel, hweyl, hr8, hr9⟩ := h123 G p A c L E h
  have h11 : RowModel p L 11 → False := by
    intro hm
    obtain ⟨hp5, hcen, -⟩ := hm
    exact hBE' (h124b G p A c L E h (by rw [hcen, hp5]))
  obtain ⟨n, ⟨f⟩, hn⟩ : ∃ n : ℕ, Nonempty (Multiplicative (Fin n → ZMod p) ≃* E) ∧
      (n = 3 ∨ n = 4) := by
    by_cases hr : r ≤ 8
    · have hcard : Nat.card E = p ^ 3 := by
        rw [hr8 hr]
        exact h.A_card
      obtain ⟨f⟩ := LinAlg.exists_coords E hcard
      exact ⟨3, ⟨f⟩, Or.inl rfl⟩
    · have hcard : Nat.card E = p ^ 4 := hr9 (by omega)
      obtain ⟨f⟩ := LinAlg.exists_coords E hcard
      exact ⟨4, ⟨f⟩, Or.inr rfl⟩
  exact Sec126g.core f h (hLAF p) hLA hD hB hJP hKF hcore' hBinv hBE hsup hinf
    (fun B' hle hBL => sec126_c_irredL h124 h hinf hBE hBE' hle hBL)
    (fun C hCE hCinv hCB hsupC =>
      sec126_d_no_complement h124 h125 h hB0 hBE' hBE hCE hCinv hCB hsupC)
    h11 hn hr12 hmodel hweyl hr8

theorem node126g_of_inputs (h123 : Node123) (h124 : Node124) (h124b : Node124b)
    (h125 : Node125) (hLAF : ∀ (p : ℕ) [Fact p.Prime], LAFaithful p) (hLA : LA126)
    (hD : ExtDickson) (hB : ExtBloomPrime) (hJP : ExtJonesParshall) (hKF : KF126) :
    Node126g := by
  intro G _ _ p A c L E h hirr hcore
  obtain ⟨h5, h9, hE4, hEA, -⟩ := node126g_full_of_inputs h123 h124 h124b h125 hLAF hLA hD hB hJP
    hKF G p A c L E h hirr hcore
  exact ⟨h5, h9, hE4, hEA⟩

theorem node126g_weyl_of_inputs (h123 : Node123) (h124 : Node124) (h124b : Node124b)
    (h125 : Node125) (hLAF : ∀ (p : ℕ) [Fact p.Prime], LAFaithful p) (hLA : LA126)
    (hD : ExtDickson) (hB : ExtBloomPrime) (hJP : ExtJonesParshall) (hKF : KF126) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec12Hyp G p A c L E → ¬ torusIrreducible E → ¬ torusWeylHasPCore p E →
        RowWeylIso E (torusImage E L) 9 := by
  intro G _ _ p A c L E h hirr hcore
  exact (node126g_full_of_inputs h123 h124 h124b h125 hLAF hLA hD hB hJP hKF G p A c L E h hirr
    hcore).2.2.2.2

end CFSG.RankThree.PartOne
