module

public import CFSG.Quasithin.Vol2.Ch12Sec4A5Data
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.H13.A5Mod

open Equiv CFSG.Open

variable {G : Type} [Group G] {K W : Subgroup G}

namespace Data

variable (d : Data K W)

theorem β_one : d.β 1 = 0 := by
  have h := d.β_mul 1 W.one_mem 1 W.one_mem
  rw [mul_one] at h
  have h2 : d.β 1 + d.β 1 = d.β 1 + 0 := by rw [← h, add_zero]
  exact add_left_cancel h2

theorem eq_one_of_β_eq_zero {w : G} (hw : w ∈ W) (h : d.β w = 0) : w = 1 :=
  d.β_inj w hw 1 W.one_mem (by rw [h, d.β_one])

theorem q_mem_alt5 (k : ↥K) : ((d.q k : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) ∈ alt5 :=
  mem_alt5.2 (Equiv.Perm.mem_alternatingGroup.1 (d.q k).2)

theorem exists_q_eq {g : Perm (Fin 5)} (hg : g ∈ alt5) :
    ∃ k : ↥K, ((d.q k : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) = g := by
  obtain ⟨k, hk⟩ := d.q_surj ⟨g, Equiv.Perm.mem_alternatingGroup.2 (mem_alt5.1 hg)⟩
  exact ⟨k, congrArg Subtype.val hk⟩

include d in
theorem conj_mem (k : ↥K) {w : G} (hw : w ∈ W) : (k : G) * w * (k : G)⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.1 (d.normalizes k.2) w).1 hw

include d in
theorem le_of_mem {U : Subgroup G} (hU : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U) {w : G} (hw : w ∈ W)
    (hwU : w ∈ U) (hw1 : w ≠ 1) : W ≤ U := by
  intro w' hw'
  have hx0 : d.β w ≠ 0 := fun h => hw1 (d.eq_one_of_β_eq_zero hw h)
  obtain ⟨g₁, hg₁, g₂, hg₂, h⟩ := mem_orbit_sum (d.β w) (d.β_mem w hw) hx0 (d.β w')
    (d.β_mem w' hw')
  obtain ⟨k₁, rfl⟩ := d.exists_q_eq hg₁
  obtain ⟨k₂, rfl⟩ := d.exists_q_eq hg₂
  rw [← d.β_conj k₁ w hw, ← d.β_conj k₂ w hw,
    ← d.β_mul _ (d.conj_mem k₁ hw) _ (d.conj_mem k₂ hw)] at h
  rcases h with e | e
  · rw [d.β_inj w' hw' _ (d.conj_mem k₁ hw) e]
    exact hU k₁ k₁.2 w hwU
  · rw [d.β_inj w' hw' _ (W.mul_mem (d.conj_mem k₁ hw) (d.conj_mem k₂ hw)) e]
    exact U.mul_mem (hU k₁ k₁.2 w hwU) (hU k₂ k₂.2 w hwU)

open Classical in
noncomputable def qG (g : G) : Perm (Fin 5) :=
  if hg : g ∈ K then ((d.q ⟨g, hg⟩ : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) else 1

theorem qG_of_mem {g : G} (hg : g ∈ K) :
    d.qG g = ((d.q ⟨g, hg⟩ : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) :=
  dite_eq_left hg

theorem qG_coe (k : ↥K) :
    d.qG (k : G) = ((d.q k : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) :=
  d.qG_of_mem k.2

theorem qG_mul {a b : G} (ha : a ∈ K) (hb : b ∈ K) : d.qG (a * b) = d.qG a * d.qG b := by
  rw [d.qG_of_mem (K.mul_mem ha hb), d.qG_of_mem ha, d.qG_of_mem hb]
  have : (⟨a * b, K.mul_mem ha hb⟩ : ↥K) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [this, map_mul]
  rfl

theorem qG_inv {a : G} (ha : a ∈ K) : d.qG a⁻¹ = (d.qG a)⁻¹ := by
  rw [d.qG_of_mem (K.inv_mem ha), d.qG_of_mem ha]
  have : (⟨a⁻¹, K.inv_mem ha⟩ : ↥K) = (⟨a, ha⟩)⁻¹ := rfl
  rw [this, map_inv]
  rfl

theorem qG_eq_one_iff {a : G} (ha : a ∈ K) :
    d.qG a = 1 ↔ a ∈ Subgroup.centralizer (W : Set G) := by
  rw [d.qG_of_mem ha, ← d.q_eq_one ⟨a, ha⟩]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    rw [h]
    rfl

theorem qG_mem_alt5 {a : G} (ha : a ∈ K) : d.qG a ∈ alt5 := by
  rw [d.qG_of_mem ha]
  exact d.q_mem_alt5 ⟨a, ha⟩

theorem exists_qG_eq {g : Perm (Fin 5)} (hg : g ∈ alt5) : ∃ k ∈ K, d.qG k = g := by
  obtain ⟨k, hk⟩ := d.exists_q_eq hg
  exact ⟨k, k.2, by rw [d.qG_coe, hk]⟩

theorem β_conj' {k w : G} (hk : k ∈ K) (hw : w ∈ W) :
    d.β (k * w * k⁻¹) = act5 (d.qG k) (d.β w) := by
  rw [d.qG_of_mem hk]
  exact d.β_conj ⟨k, hk⟩ w hw

include d in
theorem conj_mem' {k w : G} (hk : k ∈ K) (hw : w ∈ W) : k * w * k⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.1 (d.normalizes hk) w).1 hw

theorem exists_perm [Finite G] {h : G} (hhK : h ∈ Subgroup.normalizer (K : Set G))
    (hC : ∀ k ∈ K, k ∈ Subgroup.centralizer (W : Set G) →
      h * k * h⁻¹ ∈ Subgroup.centralizer (W : Set G)) :
    ∃ σ : Perm (Fin 5), ∀ k ∈ K, d.qG (h * k * h⁻¹) = σ * d.qG k * σ⁻¹ := by
  classical
  let cK : ↥K →* ↥K :=
    { toFun := fun k => ⟨h * k * h⁻¹, (Subgroup.mem_normalizer_iff.1 hhK k).1 k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let g := d.q.comp cK
  have hg : d.q.ker ≤ g.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    exact (d.q_eq_one (cK k)).2 (hC k k.2 ((d.q_eq_one k).1 hk))
  let θ := d.q.liftOfSurjective d.q_surj ⟨g, hg⟩
  have hθ : ∀ k, θ (d.q k) = d.q (cK k) := fun k =>
    d.q.liftOfRightInverse_comp_apply _ _ ⟨g, hg⟩ k
  have hθs : Function.Surjective θ := by
    intro γ
    obtain ⟨k, rfl⟩ := d.q_surj γ
    have hk' : h⁻¹ * k * h⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem hhK) k).1 k.2
    refine ⟨d.q ⟨h⁻¹ * k * h⁻¹⁻¹, hk'⟩, ?_⟩
    rw [hθ]
    congr 1
    apply Subtype.ext
    show h * (h⁻¹ * k * h⁻¹⁻¹) * h⁻¹ = k
    group
  have hθi : Function.Injective θ := Finite.injective_iff_surjective.2 hθs
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    le_rfl (by norm_num)).2 (MulEquiv.ofBijective θ ⟨hθi, hθs⟩)
  refine ⟨σ, fun k hk => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥(alternatingGroup (Fin 5)) =>
    ((φ (d.q ⟨k, hk⟩) : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5))) hσ
  simp only [MulAut.conjNormal_apply] at h1
  have h2 : ((MulEquiv.ofBijective θ ⟨hθi, hθs⟩) (d.q ⟨k, hk⟩) : ↥(alternatingGroup (Fin 5))) =
      d.q (cK ⟨k, hk⟩) := hθ ⟨k, hk⟩
  rw [h2] at h1
  rw [d.qG_of_mem hk, d.qG_of_mem ((Subgroup.mem_normalizer_iff.1 hhK k).1 hk)]
  exact h1.symm

theorem perm_unique {σ τ : Perm (Fin 5)} {X : G → Perm (Fin 5)}
    (hσ : ∀ k ∈ K, X k = σ * d.qG k * σ⁻¹) (hτ : ∀ k ∈ K, X k = τ * d.qG k * τ⁻¹) : σ = τ := by
  apply (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)).1
  apply MulEquiv.ext
  intro γ
  obtain ⟨k, rfl⟩ := d.q_surj γ
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply, ← d.qG_coe, ← hσ k k.2, ← hτ k k.2]

theorem β_conj_of_perm {y : G} (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hyW : y ∈ Subgroup.normalizer (W : Set G)) {σ : Perm (Fin 5)}
    (hσ : ∀ k ∈ K, d.qG (y * k * y⁻¹) = σ * d.qG k * σ⁻¹) :
    ∀ w ∈ W, d.β (y * w * y⁻¹) = act5 σ (d.β w) := by
  have hyw : ∀ w ∈ W, y * w * y⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.1 hyW w).1 hw
  let f : G → Fin 5 → ZMod 2 := fun w => act5 σ⁻¹ (d.β (y * w * y⁻¹))
  have hfmul : ∀ w₁ ∈ W, ∀ w₂ ∈ W, f (w₁ * w₂) = f w₁ + f w₂ := by
    intro w₁ hw₁ w₂ hw₂
    simp only [f]
    rw [show y * (w₁ * w₂) * y⁻¹ = (y * w₁ * y⁻¹) * (y * w₂ * y⁻¹) by group,
      d.β_mul _ (hyw w₁ hw₁) _ (hyw w₂ hw₂), act5_add]
  have hfeq : ∀ k ∈ K, ∀ w ∈ W, f (k * w * k⁻¹) = act5 (d.qG k) (f w) := by
    intro k hk w hw
    simp only [f]
    have hk' : y * k * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hyK k).1 hk
    rw [show y * (k * w * k⁻¹) * y⁻¹ = (y * k * y⁻¹) * (y * w * y⁻¹) * (y * k * y⁻¹)⁻¹ by group,
      d.β_conj' hk' (hyw w hw), hσ k hk, ← act5_mul, ← act5_mul]
    congr 1
    group
  have hfinj : ∀ w₁ ∈ W, ∀ w₂ ∈ W, f w₁ = f w₂ → w₁ = w₂ := by
    intro w₁ hw₁ w₂ hw₂ h12
    have h1 : d.β (y * w₁ * y⁻¹) = d.β (y * w₂ * y⁻¹) := by
      have := congrArg (act5 σ) h12
      simp only [f] at this
      rwa [← act5_mul, ← act5_mul, mul_inv_cancel, act5_one, act5_one] at this
    have h2 := d.β_inj _ (hyw w₁ hw₁) _ (hyw w₂ hw₂) h1
    simpa using h2
  obtain ⟨w₀, hw₀, hβw₀⟩ := d.β_surj u5 u5_mem
  have hf₀ : f w₀ = u5 := by
    have hmem : f w₀ ∈ ev5 := act5_mem _ (d.β_mem _ (hyw w₀ hw₀))
    have hstab : ∀ g ∈ alt5, act5 g u5 = u5 → act5 g (f w₀) = f w₀ := by
      intro g hg hgu
      obtain ⟨k, hk, rfl⟩ := d.exists_qG_eq hg
      have hkw₀ : k * w₀ * k⁻¹ = w₀ :=
        d.β_inj _ (d.conj_mem' hk hw₀) _ hw₀ (by rw [d.β_conj' hk hw₀, hβw₀, hgu])
      rw [← hfeq k hk w₀ hw₀, hkw₀]
    rcases stab_fix (f w₀) hmem hstab with h0 | h0
    · exfalso
      have h1 : f w₀ = f 1 := by
        rw [h0]
        simp only [f, mul_one, mul_inv_cancel, d.β_one, act5_zero]
      have h2 := hfinj w₀ hw₀ 1 W.one_mem h1
      rw [h2, d.β_one] at hβw₀
      exact u5_ne_zero hβw₀.symm
    · exact h0
  intro w hw
  have hfw : f w = d.β w := by
    obtain ⟨g₁, hg₁, g₂, hg₂, h⟩ := mem_orbit_sum u5 u5_mem u5_ne_zero (d.β w) (d.β_mem w hw)
    obtain ⟨k₁, hk₁, rfl⟩ := d.exists_qG_eq hg₁
    obtain ⟨k₂, hk₂, rfl⟩ := d.exists_qG_eq hg₂
    rw [← hβw₀, ← d.β_conj' hk₁ hw₀, ← d.β_conj' hk₂ hw₀,
      ← d.β_mul _ (d.conj_mem' hk₁ hw₀) _ (d.conj_mem' hk₂ hw₀)] at h
    rcases h with e | e
    · rw [d.β_inj _ hw _ (d.conj_mem' hk₁ hw₀) e, hfeq k₁ hk₁ w₀ hw₀, hf₀, ← hβw₀,
        ← d.β_conj' hk₁ hw₀]
    · rw [d.β_inj _ hw _ (W.mul_mem (d.conj_mem' hk₁ hw₀) (d.conj_mem' hk₂ hw₀)) e,
        hfmul _ (d.conj_mem' hk₁ hw₀) _ (d.conj_mem' hk₂ hw₀), hfeq k₁ hk₁ w₀ hw₀,
        hfeq k₂ hk₂ w₀ hw₀, hf₀, d.β_mul _ (d.conj_mem' hk₁ hw₀) _ (d.conj_mem' hk₂ hw₀),
        d.β_conj' hk₁ hw₀, d.β_conj' hk₂ hw₀, hβw₀]
  have h1 : act5 σ (f w) = d.β (y * w * y⁻¹) := by
    simp only [f]
    rw [← act5_mul, mul_inv_cancel, act5_one]
  rw [← h1, hfw]

end Data

theorem card_le_of_subset_finset {S : Subgroup (Perm (Fin 5))} {T : Finset (Perm (Fin 5))}
    (h : (S : Set (Perm (Fin 5))) ⊆ T) : Nat.card S ≤ T.card := by
  have h1 : Nat.card S = (S : Set (Perm (Fin 5))).ncard := Nat.card_coe_set_eq _
  rw [h1]
  calc (S : Set (Perm (Fin 5))).ncard ≤ (T : Set (Perm (Fin 5))).ncard :=
        Set.ncard_le_ncard h (Finset.finite_toSet T)
    _ = T.card := Set.ncard_coe_finset T

theorem mem_centralizer_sup_zpowers {D : Subgroup G} {z w : G}
    (hD : D ≤ Subgroup.centralizer ({w} : Set G)) (hz : z * w * z⁻¹ = w) :
    w ∈ Subgroup.centralizer ((D ⊔ Subgroup.zpowers z : Subgroup G) : Set G) := by
  have hzw : z ∈ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    calc w * z = (z * w * z⁻¹) * z := by rw [hz]
      _ = z * w := by group
  have hle : D ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer ({w} : Set G) :=
    sup_le hD ((Subgroup.zpowers_le).2 hzw)
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (Subgroup.mem_centralizer_iff.1 (hle hb) w rfl).symm

theorem false_of_a5Module [Finite G] {H K VH W A : Subgroup G}
    (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (h2K : ∀ h ∈ H, ∃ j : ℕ, h ^ 2 ^ j ∈ K) (hred : IsTwoReducedIn H VH)
    (hWV : W ≤ VH) (hW : IsA5ModuleUnder K W)
    (hCW : K ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (VH : Set G))
    (hAH : A ≤ H) (hA : IsElemAbelian 2 A) (hAV : ¬ A ≤ Subgroup.centralizer (VH : Set G))
    (hA2 : ∀ B : Subgroup G, B ≤ A → E3.mQuot A B ≤ 1 →
      VH ⊓ Subgroup.centralizer (B : Set G) = VH ⊓ Subgroup.centralizer (A : Set G)) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d⟩ := exists_data hW
  obtain ⟨-, hHVH, -, hred'⟩ := hred
  have hCVW : Subgroup.centralizer (VH : Set G) ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.centralizer_le hWV
  have hconjC : ∀ h ∈ H, ∀ x ∈ Subgroup.centralizer (VH : Set G),
      h * x * h⁻¹ ∈ Subgroup.centralizer (VH : Set G) := by
    intro h hh x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hv' : h⁻¹ * v * h⁻¹⁻¹ ∈ VH := (Subgroup.mem_normalizer_iff.1 (hHVH (inv_mem hh)) v).1 hv
    have h1 := hx _ hv'
    calc v * (h * x * h⁻¹) = h * ((h⁻¹ * v * h⁻¹⁻¹) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * v * h⁻¹⁻¹)) * h⁻¹ := by rw [h1]
      _ = h * x * h⁻¹ * v := by group
  have hHC : ∀ h ∈ H, ∀ k ∈ K, k ∈ Subgroup.centralizer (W : Set G) →
      h * k * h⁻¹ ∈ Subgroup.centralizer (W : Set G) := fun h hh k hk hkW =>
    hCVW (hconjC h hh k (hCW ⟨hk, hkW⟩))
  have hex : ∀ h : ↥H, ∃ σ : Perm (Fin 5), ∀ k ∈ K,
      d.qG ((h : G) * k * (h : G)⁻¹) = σ * d.qG k * σ⁻¹ := fun h =>
    d.exists_perm (hHK h.2) (hHC h h.2)
  choose σ hσ using hex
  have hσmul : ∀ h₁ h₂ : ↥H, σ (h₁ * h₂) = σ h₁ * σ h₂ := by
    intro h₁ h₂
    refine d.perm_unique (hσ (h₁ * h₂)) (fun k hk => ?_)
    have hk₂ : (h₂ : G) * k * (h₂ : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hHK h₂.2) k).1 hk
    rw [show ((h₁ * h₂ : ↥H) : G) * k * ((h₁ * h₂ : ↥H) : G)⁻¹ =
      (h₁ : G) * ((h₂ : G) * k * (h₂ : G)⁻¹) * (h₁ : G)⁻¹ by simp only [Subgroup.coe_mul]; group,
      hσ h₁ _ hk₂, hσ h₂ k hk]
    group
  have hσone : σ 1 = 1 := by
    have h1 := hσmul 1 1
    rw [mul_one] at h1
    exact (mul_eq_left.1 h1.symm)
  let σH : ↥H →* Perm (Fin 5) :=
    { toFun := σ, map_one' := hσone, map_mul' := hσmul }
  have hσH : ∀ h, σH h = σ h := fun h => rfl
  have hσK : ∀ h : ↥H, (h : G) ∈ K → σ h = d.qG h := by
    intro h hhK'
    refine d.perm_unique (hσ h) (fun k hk => ?_)
    rw [d.qG_mul (K.mul_mem hhK' hk) (K.inv_mem hhK'), d.qG_mul hhK' hk, d.qG_inv hhK']
  have hσker : ∀ h : ↥H, σ h = 1 ↔ (h : G) ∈ Subgroup.centralizer (VH : Set G) := by
    intro h
    constructor
    · intro h1
      let D := σH.ker.map H.subtype
      have hDH : D ≤ H := fun x hx => by
        obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
        exact y.2
      have hHD : H ≤ Subgroup.normalizer (D : Set G) := by
        intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro n
        constructor
        · intro hn
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hn
          refine Subgroup.mem_map.2 ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, ?_, rfl⟩
          rw [MonoidHom.mem_ker] at hy ⊢
          rw [map_mul, map_mul, hy, mul_one, map_inv, mul_inv_cancel]
        · intro hn
          obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.1 hn
          refine Subgroup.mem_map.2 ⟨⟨x, hx⟩⁻¹ * y * ⟨x, hx⟩, ?_, ?_⟩
          · rw [MonoidHom.mem_ker] at hy ⊢
            rw [map_mul, map_mul, hy, mul_one, map_inv, inv_mul_cancel]
          · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hye ⊢
            rw [hye]
            group
      have hD2 : ∀ x ∈ D, ∃ j : ℕ, x ^ 2 ^ j ∈ Subgroup.centralizer (VH : Set G) := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
        obtain ⟨j, hj⟩ := h2K y y.2
        refine ⟨j, ?_⟩
        have h2 : σ (y ^ 2 ^ j) = 1 := by
          rw [← hσH, map_pow, (MonoidHom.mem_ker).1 hy, one_pow]
        rw [hσK _ (by simpa using hj)] at h2
        have h3 := (d.qG_eq_one_iff (by simpa using hj)).1 (by simpa using h2)
        exact hCW ⟨by simpa using hj, by simpa using h3⟩
      have hDC := hred' D hDH hHD hD2
      exact hDC (Subgroup.mem_map.2 ⟨h, (MonoidHom.mem_ker).2 h1, rfl⟩)
    · intro hC
      refine (d.perm_unique (hσ h) (fun k hk => ?_)).trans rfl
      rw [one_mul, inv_one, mul_one]
      have hk' : (h : G) * k * (h : G)⁻¹ * k⁻¹ ∈ K :=
        K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hHK h.2) k).1 hk) (K.inv_mem hk)
      have hkC : (h : G) * k * (h : G)⁻¹ * k⁻¹ ∈ Subgroup.centralizer (VH : Set G) := by
        rw [show (h : G) * k * (h : G)⁻¹ * k⁻¹ = (h : G) * (k * (h : G)⁻¹ * k⁻¹) by group]
        exact Subgroup.mul_mem _ hC (hconjC k (hKH hk) _ (inv_mem hC))
      have h1 := (d.qG_eq_one_iff hk').2 (hCVW hkC)
      have hk'' : (h : G) * k * (h : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hHK h.2) k).1 hk
      rw [d.qG_mul hk'' (K.inv_mem hk), d.qG_inv hk, mul_inv_eq_one] at h1
      exact h1
  have hApg : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  have hAsq : ∀ y : ↥A, y * y = 1 := fun y => Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two, Subgroup.coe_one]
    exact hA.2 y y.2)
  have hAab : ∀ y z : ↥A, y * z = z * y := fun y z => by
    have := hA.1
    exact mul_comm' y z
  let D := A ⊓ Subgroup.centralizer (VH : Set G)
  let σA : ↥A →* Perm (Fin 5) := σH.comp (Subgroup.inclusion hAH)
  have hσA : ∀ y : ↥A, σA y = σ ⟨y, hAH y.2⟩ := fun y => rfl
  have hσAker : σA.ker = D.subgroupOf A := by
    ext y
    rw [MonoidHom.mem_ker, hσA, hσker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
  have hidx : D.relIndex A = Nat.card σA.range := by
    rw [Subgroup.relIndex, ← hσAker, Subgroup.index_ker]
  have h2pow := E3.relIndex_eq_two_pow hApg D
  have hsqA : ∀ y : ↥A, σA y * σA y = 1 := fun y => by rw [← map_mul, hAsq, map_one]
  have hcommA : ∀ y z : ↥A, σA y * σA z = σA z * σA y := fun y z => by
    rw [← map_mul, ← map_mul, hAab]
  have hmD : 2 ≤ E3.mQuot A D := by
    by_contra hlt
    push Not at hlt
    have h1 := hA2 D inf_le_left (by omega)
    apply hAV
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv1 : v ∈ VH ⊓ Subgroup.centralizer (D : Set G) := by
      refine ⟨hv, ?_⟩
      show v ∈ Subgroup.centralizer (D : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.1 hx.2 v hv).symm
    rw [h1] at hv1
    exact (Subgroup.mem_centralizer_iff.1 hv1.2 a ha).symm
  have hcard4 : 4 ≤ Nat.card σA.range := by
    rw [← hidx, h2pow]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ E3.mQuot A D := Nat.pow_le_pow_right (by norm_num) hmD
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ↥A, σA y₁ ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : (σA.range : Set (Perm (Fin 5))) ⊆ ({1} : Finset (Perm (Fin 5))) := by
      rintro _ ⟨y, rfl⟩
      simp [h y]
    have h2 := card_le_of_subset_finset h1
    rw [Finset.card_singleton] at h2
    omega
  obtain ⟨y₂, hy₂1, hy₂2⟩ : ∃ y₂ : ↥A, σA y₂ ≠ 1 ∧ σA y₂ ≠ σA y₁ := by
    by_contra h
    push Not at h
    have h1 : (σA.range : Set (Perm (Fin 5))) ⊆ ({1, σA y₁} : Finset (Perm (Fin 5))) := by
      rintro _ ⟨y, rfl⟩
      by_cases hy : σA y = 1
      · simp [hy]
      · simp [h y hy]
    have h2 := card_le_of_subset_finset h1
    have h3 : ({1, σA y₁} : Finset (Perm (Fin 5))).card ≤ 2 := Finset.card_le_two
    omega
  have hall : ∀ y : ↥A, σA y = 1 ∨ σA y = σA y₁ ∨ σA y = σA y₂ ∨ σA y = σA y₁ * σA y₂ :=
    fun y => elemAbelian_le_four (σA y₁) (mem_invs5.2 (hsqA y₁)) (σA y₂)
      (mem_invs5.2 (hsqA y₂)) (σA y) (mem_invs5.2 (hsqA y))
      ⟨hcommA y₁ y₂, hcommA y₁ y, hcommA y₂ y, hy₁, hy₂1, hy₂2.symm⟩
  have hcard_le : Nat.card σA.range ≤ 4 := by
    have h1 : (σA.range : Set (Perm (Fin 5))) ⊆
        ([1, σA y₁, σA y₂, σA y₁ * σA y₂].toFinset : Finset (Perm (Fin 5))) := by
      rintro _ ⟨y, rfl⟩
      rcases hall y with h | h | h | h <;> simp [h]
    exact (card_le_of_subset_finset h1).trans (List.toFinset_card_le _)
  have hmD2 : E3.mQuot A D ≤ 2 := by
    have h1 : 2 ^ E3.mQuot A D ≤ 2 ^ 2 := by
      rw [← h2pow, hidx]
      exact hcard_le
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hB1 : ∀ z : ↥A, σA z ≠ 1 → E3.mQuot A (D ⊔ Subgroup.zpowers (z : G)) ≤ 1 := by
    intro z hz
    have hBA : D ⊔ Subgroup.zpowers (z : G) ≤ A :=
      sup_le inf_le_left ((Subgroup.zpowers_le).2 z.2)
    have hadd := E3.mQuot_add (le_sup_left : D ≤ D ⊔ Subgroup.zpowers (z : G)) hBA
    have hne : E3.mQuot (D ⊔ Subgroup.zpowers (z : G)) D ≠ 0 := by
      intro h0
      rw [E3.mQuot_eq_zero_iff (hApg.to_le hBA) le_sup_left] at h0
      apply hz
      have hzD : (z : G) ∈ D :=
        h0 ▸ (le_sup_right : Subgroup.zpowers (z : G) ≤ _) (Subgroup.mem_zpowers _)
      rw [hσA]
      exact (hσker _).2 hzD.2
    omega
  have hBle : ∀ z : ↥A, D ⊔ Subgroup.zpowers (z : G) ≤ A := fun z =>
    sup_le inf_le_left ((Subgroup.zpowers_le).2 z.2)
  have hCB : ∀ z ∈ A, ∀ w ∈ VH, z * w * z⁻¹ = w →
      w ∈ VH ⊓ Subgroup.centralizer ((D ⊔ Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro z hz w hw hzw
    refine ⟨hw, mem_centralizer_sup_zpowers ?_ hzw⟩
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.mem_centralizer_iff.1 hx.2 w hw
  obtain ⟨z, hz1, hzalt⟩ : ∃ z : ↥A, σA z ≠ 1 ∧ σA z ∈ alt5 := by
    rcases Int.units_eq_one_or (Perm.sign (σA y₁)) with hs | hs
    · exact ⟨y₁, hy₁, mem_alt5.2 hs⟩
    rcases Int.units_eq_one_or (Perm.sign (σA y₂)) with ht | ht
    · exact ⟨y₂, hy₂1, mem_alt5.2 ht⟩
    refine ⟨y₁ * y₂, ?_, ?_⟩
    · rw [map_mul]
      intro h
      apply hy₂2
      calc σA y₂ = σA y₁ * (σA y₁ * σA y₂) := by rw [← mul_assoc, hsqA, one_mul]
        _ = σA y₁ := by rw [h, mul_one]
    · rw [map_mul, mem_alt5, Perm.sign_mul, hs, ht]
      rfl
  obtain ⟨k, hk, hkz⟩ := d.exists_qG_eq hzalt
  have hσk : σ ⟨k, hKH hk⟩ = σA z := (hσK ⟨k, hKH hk⟩ hk).trans hkz
  have hzk : (z : G) * k⁻¹ ∈ Subgroup.centralizer (VH : Set G) := by
    have h1 : σ (⟨z, hAH z.2⟩ * (⟨k, hKH hk⟩ : ↥H)⁻¹) = 1 := by
      rw [← hσH, map_mul, map_inv, hσH, hσH, hσk, ← hσA, mul_inv_cancel]
    exact (hσker _).1 h1
  obtain ⟨x, hx, hx0, hxz⟩ := exists_fix_of_involution (σA z) (mem_invs5.2 (hsqA z)) hz1
  obtain ⟨w, hw, hβw⟩ := d.β_surj x hx
  have hkw : k * w * k⁻¹ = w :=
    d.β_inj _ (d.conj_mem' hk hw) _ hw (by rw [d.β_conj' hk hw, hkz, hβw, hxz])
  have hzw : (z : G) * w * (z : G)⁻¹ = w := by
    have h1 := Subgroup.mem_centralizer_iff.1 hzk w (hWV hw)
    calc (z : G) * w * (z : G)⁻¹ = ((z : G) * k⁻¹) * (k * w * k⁻¹) * ((z : G) * k⁻¹)⁻¹ := by
          group
      _ = ((z : G) * k⁻¹) * w * ((z : G) * k⁻¹)⁻¹ := by rw [hkw]
      _ = w * ((z : G) * k⁻¹) * ((z : G) * k⁻¹)⁻¹ := by rw [← h1]
      _ = w := by group
  have hw1 : w ≠ 1 := fun h => hx0 (by rw [← hβw, h, d.β_one])
  have hwA : w ∈ Subgroup.centralizer (A : Set G) := by
    have h1 := hCB z z.2 w (hWV hw) hzw
    rw [hA2 _ (hBle z) (hB1 z hz1)] at h1
    exact h1.2
  have hyW' : ∀ y ∈ A, ∀ u ∈ W, y * u * y⁻¹ ∈ W := by
    intro y hy
    let U : Subgroup G := W ⊓ W.comap (MulAut.conj y).toMonoidHom
    have hU : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U := by
      intro k hk u hu
      refine ⟨d.conj_mem' hk hu.1, ?_⟩
      have hu2 : y * u * y⁻¹ ∈ W := hu.2
      show y * (k * u * k⁻¹) * y⁻¹ ∈ W
      have hk' : y * k * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hHK (hAH hy)) k).1 hk
      rw [show y * (k * u * k⁻¹) * y⁻¹ = (y * k * y⁻¹) * (y * u * y⁻¹) * (y * k * y⁻¹)⁻¹ by
        group]
      exact d.conj_mem' hk' hu2
    have hwU : w ∈ U := by
      refine ⟨hw, ?_⟩
      show y * w * y⁻¹ ∈ W
      rw [Subgroup.mem_centralizer_iff.1 hwA y hy, mul_inv_cancel_right]
      exact hw
    intro u hu
    exact (d.le_of_mem hU hw hwU hw1 hu).2
  have hyW : ∀ y ∈ A, y ∈ Subgroup.normalizer (W : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hyW' y hy n, fun hn => ?_⟩
    have := hyW' y⁻¹ (inv_mem hy) _ hn
    simpa [mul_assoc] using this
  have hβy : ∀ y : ↥A, ∀ u ∈ W, d.β ((y : G) * u * (y : G)⁻¹) = act5 (σA y) (d.β u) :=
    fun y => d.β_conj_of_perm (hHK (hAH y.2)) (hyW y y.2) (hσ ⟨y, hAH y.2⟩)
  obtain ⟨r, hr, x', hx', hrx, hpqx⟩ := exists_fix_not_fix (σA y₁) (mem_invs5.2 (hsqA y₁))
    (σA y₂) (mem_invs5.2 (hsqA y₂)) ⟨hy₁, hy₂1, hy₂2.symm, hcommA y₁ y₂⟩
  obtain ⟨ŷ, hŷr, hŷ1⟩ : ∃ ŷ : ↥A, σA ŷ = r ∧ σA ŷ ≠ 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨y₁, rfl, hy₁⟩
    · exact ⟨y₂, rfl, hy₂1⟩
    · refine ⟨y₁ * y₂, map_mul _ _ _, ?_⟩
      rw [map_mul]
      intro h
      apply hy₂2
      calc σA y₂ = σA y₁ * (σA y₁ * σA y₂) := by rw [← mul_assoc, hsqA, one_mul]
        _ = σA y₁ := by rw [h, mul_one]
  obtain ⟨w', hw', hβw'⟩ := d.β_surj x' hx'
  have hŷw : (ŷ : G) * w' * (ŷ : G)⁻¹ = w' :=
    d.β_inj _ (hyW' ŷ ŷ.2 w' hw') _ hw' (by rw [hβy ŷ w' hw', hβw', hŷr, hrx])
  have h1 := hCB ŷ ŷ.2 w' (hWV hw') hŷw
  rw [hA2 _ (hBle ŷ) (hB1 ŷ hŷ1)] at h1
  have hfix : ∀ y : ↥A, act5 (σA y) x' = x' := by
    intro y
    have h2 := Subgroup.mem_centralizer_iff.1 h1.2 y y.2
    rw [← hβw', ← hβy y w' hw']
    congr 1
    rw [h2, mul_inv_cancel_right]
  rcases hpqx with h | h
  · exact h (hfix y₁)
  · exact h (hfix y₂)

end CFSG.Quasithin.H13.A5Mod
