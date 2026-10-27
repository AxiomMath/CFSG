module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

@[expose] def Lem1216Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) → ∀ v : G,
      V₁ ⊓ Subgroup.centralizer
          ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) = Subgroup.zpowers v →
        ∀ x ∈ conjClosure V (Subgroup.centralizer ({v} : Set G)),
          ∀ y ∈ conjClosure V (Subgroup.centralizer ({v} : Set G)), x * y = y * x

namespace Sec1216

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem mem_conjugate_iff {g x : G} : x ∈ CFSG.conjugate V g ↔ g * x * g⁻¹ ∈ V := by
  simp only [CFSG.conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by group⟩

omit [Finite G] in
theorem conj_mem_conjClosure {m v x : G} (hm : m ∈ Subgroup.normalizer (V : Set G))
    (hx : x ∈ conjClosure V (Subgroup.centralizer ({m * v * m⁻¹} : Set G))) :
    m⁻¹ * x * m ∈ conjClosure V (Subgroup.centralizer ({v} : Set G)) := by
  set K := conjClosure V (Subgroup.centralizer ({v} : Set G)) with hK
  set K' : Subgroup G := K.comap (MulAut.conj m⁻¹).toMonoidHom with hK'
  have hle : conjClosure V (Subgroup.centralizer ({m * v * m⁻¹} : Set G)) ≤ K' := by
    refine conjClosure_le fun c hc z hz => ?_
    show m⁻¹ * (c * z * c⁻¹) * m⁻¹⁻¹ ∈ K
    have hc' : m⁻¹ * c * m ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      have e : m⁻¹ * c * m * v = m⁻¹ * (c * (m * v * m⁻¹)) * m := by group
      rw [e, hc]
      group
    have hz' : m⁻¹ * z * m ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) z).mp hz
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V _ hc')
      (m⁻¹ * z * m)).mp (le_conjClosure V _ hz')
    have e : m⁻¹ * (c * z * c⁻¹) * m⁻¹⁻¹ =
        m⁻¹ * c * m * (m⁻¹ * z * m) * (m⁻¹ * c * m)⁻¹ := by group
    rw [e]
    exact h1
  have h2 := hle hx
  rw [hK', Subgroup.mem_comap] at h2
  simpa using h2

theorem lem1216_one_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (hH91 : LemH91)
    (hGen : Lem1216Gen) (hyp : Hyp121 G T L V V₁ V₂ n) {v : G} (hvO : v ∈ V₁ ∨ v ∈ V₂)
    (hv1 : v ≠ 1) {x y : G} (hx : x ∈ conjClosure V (Subgroup.centralizer ({v} : Set G)))
    (hy : y ∈ conjClosure V (Subgroup.centralizer ({v} : Set G))) : x * y = y * x := by
  obtain ⟨hTL, -⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  obtain ⟨⟨v₁, hv₁⟩, β, hβ, horb⟩ := hH91 G T L V V₁ V₂ n hyp hTL
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  have hv₁V₁ : v₁ ∈ V₁ := by
    have : v₁ ∈ Subgroup.zpowers v₁ := Subgroup.mem_zpowers v₁
    rw [← hv₁] at this
    exact this.1
  have hv₁1 : v₁ ≠ 1 := by
    intro h0
    apply Sec1215.inf_centralizer_ne_bot hyp hTL
    rw [hv₁, h0, Subgroup.zpowers_one_eq_bot]
  have hvV : v ∈ V := hvO.elim (fun h => hV₁V h) (fun h => hV₂V h)
  have hsing : ∀ w, (w ∈ V₁ ∨ w ∈ V₂) → ¬ IsNonsingular121 V₁ V₂ β w := fun w hw hns => by
    obtain ⟨h1, h2⟩ := Sec1215.not_mem_of_nonsingular hyp hβ hns
    exact hw.elim h1 h2
  obtain ⟨m, hmM, hmv⟩ := (horb v₁ (hV₁V hv₁V₁) v hvV hv₁1 hv1).mpr
    ⟨iff_of_true (Or.inl hv₁V₁) hvO,
      iff_of_false (hsing v₁ (Or.inl hv₁V₁)) (hsing v hvO)⟩
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := Sec121Q.normalizer_le_of_hyp121 hyp hmM
  rw [← hmv] at hx hy
  have hx' := conj_mem_conjClosure hmV hx
  have hy' := conj_mem_conjClosure hmV hy
  have hc := hGen G T L V V₁ V₂ n hyp hTL v₁ hv₁ _ hx' _ hy'
  calc x * y = m * ((m⁻¹ * x * m) * (m⁻¹ * y * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * y * m) * (m⁻¹ * x * m)) * m⁻¹ := by rw [hc]
    _ = y * x := by group

theorem lem1216_two_of (h1215 : Lem1215) (hyp : Hyp121 G T L V V₁ V₂ n)
    (hone : ∀ v : G, (v ∈ V₁ ∨ v ∈ V₂) → v ≠ 1 →
      ∀ x ∈ conjClosure V (Subgroup.centralizer ({v} : Set G)),
        ∀ y ∈ conjClosure V (Subgroup.centralizer ({v} : Set G)), x * y = y * x)
    (g : G) (hg : V₁ ⊓ CFSG.conjugate V g ≠ ⊥) : ⁅V, CFSG.conjugate V g⁆ = ⊥ := by
  obtain ⟨⟨v, hvV₁, hvg⟩, hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
  have hv1 : v ≠ 1 := fun h0 => hv1' (Subtype.ext h0)
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hgv : g * v * g⁻¹ ∈ V := mem_conjugate_iff.mp hvg
  obtain ⟨m, hmM, hmv⟩ := (h1215 G T L V V₁ V₂ n hyp).2 v (hV₁V hvV₁) _ hgv hv1 g rfl
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := Sec121Q.normalizer_le_of_hyp121 hyp hmM
  have hc : m⁻¹ * g ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m⁻¹ * g * v = m⁻¹ * (g * v * g⁻¹) * g := by group
      _ = m⁻¹ * (m * v * m⁻¹) * g := by rw [hmv]
      _ = v * (m⁻¹ * g) := by group
  have hVg : ∀ x ∈ CFSG.conjugate V g, x ∈ conjClosure V (Subgroup.centralizer ({v} : Set G)) := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ V := mem_conjugate_iff.mp hx
    have h2 : (m⁻¹ * g) * x * (m⁻¹ * g)⁻¹ ∈ V := by
      have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmV) _).mp h1
      have e : (m⁻¹ * g) * x * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * x * g⁻¹) * m⁻¹⁻¹ := by group
      rw [e]
      exact h3
    have h3 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V _
      (Subgroup.inv_mem _ hc)) _).mp (le_conjClosure V _ h2)
    have e : (m⁻¹ * g)⁻¹ * ((m⁻¹ * g) * x * (m⁻¹ * g)⁻¹) * (m⁻¹ * g)⁻¹⁻¹ = x := by group
    rwa [e] at h3
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hone v (Or.inl hvV₁) hv1 a (le_conjClosure V _ ha) b (hVg b hb)

end Sec1216

theorem lem1216_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (hH91 : LemH91) (h1215 : Lem1215)
    (hGen : Lem1216Gen) : Lem1216 := by
  intro G _ _ T L V V₁ V₂ n hyp
  have hone : ∀ v : G, (v ∈ V₁ ∨ v ∈ V₂) → v ≠ 1 →
      ∀ x ∈ conjClosure V (Subgroup.centralizer ({v} : Set G)),
        ∀ y ∈ conjClosure V (Subgroup.centralizer ({v} : Set G)), x * y = y * x :=
    fun v hvO hv1 x hx y hy => Sec1216.lem1216_one_of h1001 h331 hH91 hGen hyp hvO hv1 hx hy
  exact ⟨hone, fun g hg => Sec1216.lem1216_two_of h1215 hyp hone g hg⟩

end CFSG.Quasithin.H13
