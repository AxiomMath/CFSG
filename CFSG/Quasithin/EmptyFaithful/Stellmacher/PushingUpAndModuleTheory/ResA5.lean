module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA4

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def conjClosure (X : Subgroup G) (c : G) : Subgroup G :=
  Subgroup.closure {x | ∃ g ∈ X, x = g * c * g⁻¹}

@[expose] def normClosure (X V₀ : Subgroup G) : Subgroup G :=
  Subgroup.closure {y | ∃ g ∈ X, ∃ v ∈ V₀, y = g * v * g⁻¹}

section Basic

variable {X K V₀ : Subgroup G} {c : G}

theorem conj_mem_normClosure {y : G} (hy : y ∈ normClosure X V₀) {g : G} (hg : g ∈ X) :
    g * y * g⁻¹ ∈ normClosure X V₀ := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g', hg', v, hv, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨g * g', X.mul_mem hg hg', v, hv, by group⟩
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ ha

theorem V0_le_normClosure : V₀ ≤ normClosure X V₀ := fun v hv =>
  Subgroup.subset_closure ⟨1, X.one_mem, v, hv, by group⟩

theorem conj_mem_conjClosure {y : G} (hy : y ∈ conjClosure X c) {g : G} (hg : g ∈ X) :
    g * y * g⁻¹ ∈ conjClosure X c := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g', hg', rfl⟩ := hx
    exact Subgroup.subset_closure ⟨g * g', X.mul_mem hg hg', by group⟩
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ ha

variable (hX : X ≤ Subgroup.normalizer (K : Set G)) (hKd : KData K V₀ c)

include hX hKd

theorem conj_mem_K {k g : G} (hk : k ∈ K) (hg : g ∈ X) : g * k * g⁻¹ ∈ K :=
  (Subgroup.mem_normalizer_iff.mp (hX hg) k).mp hk

theorem conj_inv_mem_K {k g : G} (hk : k ∈ K) (hg : g ∈ X) : g⁻¹ * k * g ∈ K := by
  have := (Subgroup.mem_normalizer_iff.mp (hX (X.inv_mem hg)) k).mp hk
  simpa using this

theorem normClosure_le_K : normClosure X V₀ ≤ K := by
  refine (Subgroup.closure_le K).mpr ?_
  rintro _ ⟨g, hg, v, hv, rfl⟩
  exact conj_mem_K hX hKd (hKd.V_le hv) hg

theorem normClosure_central {y : G} (hy : y ∈ normClosure X V₀) {k : G} (hk : k ∈ K) :
    y * k = k * y := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, v, hv, rfl⟩ := hx
    have hk' : g⁻¹ * k * g ∈ K := conj_inv_mem_K hX hKd hk hg
    have h1 := hKd.V_cen v hv _ hk'
    calc g * v * g⁻¹ * k = g * (v * (g⁻¹ * k * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * k * g) * v) * g⁻¹ := by rw [h1]
      _ = k * (g * v * g⁻¹) := by group
  | one => simp
  | mul a b _ _ ha hb =>
    calc a * b * k = a * (b * k) := by group
      _ = a * (k * b) := by rw [hb]
      _ = (a * k) * b := by group
      _ = k * a * b := by rw [ha]
      _ = k * (a * b) := by group
  | inv a _ ha =>
    have : a⁻¹ * k = k * a⁻¹ := by
      calc a⁻¹ * k = a⁻¹ * (k * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * k) * a⁻¹ := by rw [ha]
        _ = k * a⁻¹ := by group
    exact this

theorem normClosure_sq {y : G} (hy : y ∈ normClosure X V₀) : y * y = 1 := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, v, hv, rfl⟩ := hx
    calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [hKd.V_sq v hv]; group
  | one => simp
  | mul a b ha' hb' ha hb =>
    have hbK : b ∈ K := normClosure_le_K hX hKd hb'
    have hab : a * b = b * a := (normClosure_central hX hKd ha' hbK)
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb]; group
  | inv a _ ha =>
    have : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [this, ha]; simp

theorem comm_c_mem {k : G} (hk : k ∈ K) : c * k * c⁻¹ * k⁻¹ ∈ V₀ := by
  obtain ⟨v, hv, z, hz, hzc, rfl⟩ := hKd.K_dec k hk
  have hz' : c * z * c⁻¹ = z := by rw [← hzc]; group
  have : c * (v * z) * c⁻¹ * (v * z)⁻¹ = (c * v * c⁻¹) * v⁻¹ := by
    calc c * (v * z) * c⁻¹ * (v * z)⁻¹ = (c * v * c⁻¹) * (c * z * c⁻¹) * z⁻¹ * v⁻¹ := by group
      _ = (c * v * c⁻¹) * v⁻¹ := by rw [hz']; group
  rw [this]
  exact V₀.mul_mem (hKd.V_norm v hv) (V₀.inv_mem hv)

theorem comm_pow_mem (n : ℕ) {k : G} (hk : k ∈ K) : c ^ n * k * (c ^ n)⁻¹ * k⁻¹ ∈ V₀ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : c ^ (n + 1) * k * (c ^ (n + 1))⁻¹ * k⁻¹ =
        (c * (c ^ n * k * (c ^ n)⁻¹ * k⁻¹) * c⁻¹) * (c * k * c⁻¹ * k⁻¹) := by group
    rw [this]
    exact V₀.mul_mem (hKd.V_norm _ ih) (comm_c_mem hX hKd hk)

theorem comm_conjClosure_mem (hcX : c ∈ X) {l : G} (hl : l ∈ conjClosure X c) :
    l ∈ X ∧ ∀ k ∈ K, l * k * l⁻¹ * k⁻¹ ∈ normClosure X V₀ := by
  induction hl using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    refine ⟨X.mul_mem (X.mul_mem hg hcX) (X.inv_mem hg), fun k hk => ?_⟩
    have hk' : g⁻¹ * k * g ∈ K := conj_inv_mem_K hX hKd hk hg
    have h1 := comm_c_mem hX hKd hk'
    have h2 : g * (c * (g⁻¹ * k * g) * c⁻¹ * (g⁻¹ * k * g)⁻¹) * g⁻¹ ∈ normClosure X V₀ :=
      Subgroup.subset_closure ⟨g, hg, _, h1, rfl⟩
    have : g * (c * (g⁻¹ * k * g) * c⁻¹ * (g⁻¹ * k * g)⁻¹) * g⁻¹ =
        (g * c * g⁻¹) * k * (g * c * g⁻¹)⁻¹ * k⁻¹ := by group
    rwa [this] at h2
  | one => exact ⟨X.one_mem, fun k hk => by simp⟩
  | mul a b _ _ ha hb =>
    refine ⟨X.mul_mem ha.1 hb.1, fun k hk => ?_⟩
    have h1 := conj_mem_normClosure (hb.2 k hk) ha.1
    have h2 := ha.2 k hk
    have : a * b * k * (a * b)⁻¹ * k⁻¹ =
        (a * (b * k * b⁻¹ * k⁻¹) * a⁻¹) * (a * k * a⁻¹ * k⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ h1 h2
  | inv a _ ha =>
    refine ⟨X.inv_mem ha.1, fun k hk => ?_⟩
    have h1 := conj_mem_normClosure (Subgroup.inv_mem _ (ha.2 k hk)) (X.inv_mem ha.1)
    have : a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ = a⁻¹ * (a * k * a⁻¹ * k⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [this]; exact h1

theorem commutator_le_normClosure (hcX : c ∈ X) :
    ⁅K, conjClosure X c⁆ ≤ normClosure X V₀ := by
  rw [Subgroup.commutator_le]
  intro k hk l hl
  have h1 := Subgroup.inv_mem _ ((comm_conjClosure_mem hX hKd hcX hl).2 k hk)
  have : ⁅k, l⁆ = (l * k * l⁻¹ * k⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  rw [this]; exact h1

theorem normClosure_le_commutator :
    normClosure X V₀ ≤ ⁅K, conjClosure X c⁆ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, v, hv, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hKd.V_comm v hv
  have hwK : g * w * g⁻¹ ∈ K := conj_mem_K hX hKd (hKd.V_le hw) hg
  have hcl : g * c * g⁻¹ ∈ conjClosure X c := Subgroup.subset_closure ⟨g, hg, rfl⟩
  have := Subgroup.commutator_mem_commutator hwK hcl
  have hw2 := hKd.V_sq w hw
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have e : ⁅g * w * g⁻¹, g * c * g⁻¹⁆ = g * (w * (c * w * c⁻¹)) * g⁻¹ := by
    rw [commutatorElement_def]
    calc g * w * g⁻¹ * (g * c * g⁻¹) * (g * w * g⁻¹)⁻¹ * (g * c * g⁻¹)⁻¹
        = g * (w * c * w⁻¹ * c⁻¹) * g⁻¹ := by group
      _ = g * (w * (c * w * c⁻¹)) * g⁻¹ := by rw [hwi]; group
  rw [e] at this
  exact this

theorem derived_commute {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K) {l : G}
    (hl : l ∈ conjClosure X c) :
    (k * k' * k⁻¹ * k'⁻¹) * l = l * (k * k' * k⁻¹ * k'⁻¹) := by
  have hmem : conjClosure X c ≤ Subgroup.centralizer
      {x : G | ∃ a ∈ K, ∃ b ∈ K, x = a * b * a⁻¹ * b⁻¹} := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha1 : g⁻¹ * a * g ∈ K := conj_inv_mem_K hX hKd ha hg
    have hb1 : g⁻¹ * b * g ∈ K := conj_inv_mem_K hX hKd hb hg
    obtain ⟨v, hv, z, hz, hzc, he⟩ := hKd.K_dec _ ha1
    obtain ⟨v', hv', z', hz', hzc', he'⟩ := hKd.K_dec _ hb1
    have hvK : v ∈ K := hKd.V_le hv
    have hv'K : v' ∈ K := hKd.V_le hv'
    have e1 : (v * z) * (v' * z') * (v * z)⁻¹ * (v' * z')⁻¹ = z * z' * z⁻¹ * z'⁻¹ := by
      have hA : z * v' * z' * z⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem (K.mul_mem hz hv'K) hz') (K.inv_mem hz)
      have hB : z' * z⁻¹ * z'⁻¹ ∈ K := K.mul_mem (K.mul_mem hz' (K.inv_mem hz)) (K.inv_mem hz')
      have c1 : v * (z * v' * z' * z⁻¹) * v⁻¹ = z * v' * z' * z⁻¹ := by
        rw [hKd.V_cen v hv _ hA]; group
      have c2 : v' * (z' * z⁻¹ * z'⁻¹) * v'⁻¹ = z' * z⁻¹ * z'⁻¹ := by
        rw [hKd.V_cen v' hv' _ hB]; group
      calc (v * z) * (v' * z') * (v * z)⁻¹ * (v' * z')⁻¹
          = (v * (z * v' * z' * z⁻¹) * v⁻¹) * z'⁻¹ * v'⁻¹ := by group
        _ = (z * v' * z' * z⁻¹) * z'⁻¹ * v'⁻¹ := by rw [c1]
        _ = z * (v' * (z' * z⁻¹ * z'⁻¹) * v'⁻¹) := by group
        _ = z * z' * z⁻¹ * z'⁻¹ := by rw [c2]; group
    have e2 : (g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹ =
        z * z' * z⁻¹ * z'⁻¹ := by rw [he, he']; exact e1
    have e3 : a * b * a⁻¹ * b⁻¹ = g * (z * z' * z⁻¹ * z'⁻¹) * g⁻¹ := by
      rw [← e2]; group
    have hcz : (z * z' * z⁻¹ * z'⁻¹) * c = c * (z * z' * z⁻¹ * z'⁻¹) := by
      have Hz : Commute z c := hzc
      have Hz' : Commute z' c := hzc'
      exact ((((Hz.mul_left Hz').mul_left Hz.inv_left).mul_left Hz'.inv_left)).eq
    rw [e3]
    calc g * (z * z' * z⁻¹ * z'⁻¹) * g⁻¹ * (g * c * g⁻¹)
        = g * ((z * z' * z⁻¹ * z'⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (z * z' * z⁻¹ * z'⁻¹)) * g⁻¹ := by rw [hcz]
      _ = (g * c * g⁻¹) * (g * (z * z' * z⁻¹ * z'⁻¹) * g⁻¹) := by group
  have := hmem hl
  rw [Subgroup.mem_centralizer_iff] at this
  exact this _ ⟨k, hk, k', hk', rfl⟩

end Basic

end CFSG.Quasithin.F53
