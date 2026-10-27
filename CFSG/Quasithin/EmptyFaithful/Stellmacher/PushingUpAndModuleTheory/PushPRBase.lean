module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FrattiniBasic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreConj

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conj_commutator (g a b : G) : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
  simp only [commutatorElement_def]; group

@[expose] def phi (R : Subgroup G) : Subgroup G :=
  Subgroup.closure ({x | ∃ a ∈ R, x = a * a} ∪ {x | ∃ a ∈ R, ∃ b ∈ R, x = ⁅a, b⁆})

theorem sq_mem_phi {R : Subgroup G} {a : G} (ha : a ∈ R) : a * a ∈ phi R :=
  Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩)

theorem comm_mem_phi {R : Subgroup G} {a b : G} (ha : a ∈ R) (hb : b ∈ R) : ⁅a, b⁆ ∈ phi R :=
  Subgroup.subset_closure (Or.inr ⟨a, ha, b, hb, rfl⟩)

theorem phi_le_of {R K : Subgroup G} (hsq : ∀ a ∈ R, a * a ∈ K)
    (hcomm : ∀ a ∈ R, ∀ b ∈ R, ⁅a, b⁆ ∈ K) : phi R ≤ K := by
  refine (Subgroup.closure_le K).mpr ?_
  rintro x (⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
  · exact hsq a ha
  · exact hcomm a ha b hb

theorem phi_le_self (R : Subgroup G) : phi R ≤ R :=
  phi_le_of (fun _ ha => R.mul_mem ha ha) (fun a ha b hb => by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb))

theorem phi_mono {R S : Subgroup G} (h : R ≤ S) : phi R ≤ phi S :=
  phi_le_of (fun _ ha => sq_mem_phi (h ha)) (fun _ ha _ hb => comm_mem_phi (h ha) (h hb))

theorem commutator_le_phi (R : Subgroup G) : ⁅R, R⁆ ≤ phi R :=
  Subgroup.commutator_le.mpr fun _ ha _ hb => comm_mem_phi ha hb

theorem phi_cj (g : G) (R : Subgroup G) : phi (cj g R) = cj g (phi R) := by
  have key : ∀ (g : G) (R : Subgroup G), phi (cj g R) ≤ cj g (phi R) := by
    intro g R
    refine phi_le_of (fun a ha => ?_) (fun a ha b hb => ?_)
    · rw [mem_cj] at ha ⊢
      have := sq_mem_phi ha
      simpa [mul_assoc] using this
    · rw [mem_cj] at ha hb ⊢
      have h1 : g⁻¹ * ⁅a, b⁆ * g⁻¹⁻¹ = ⁅g⁻¹ * a * g⁻¹⁻¹, g⁻¹ * b * g⁻¹⁻¹⁆ := conj_commutator _ _ _
      simp only [inv_inv] at h1
      rw [h1]
      exact comm_mem_phi ha hb
  refine le_antisymm (key g R) ?_
  have h1 := key g⁻¹ (cj g R)
  rw [cj_cj, inv_mul_cancel, cj_one] at h1
  have h2 := cj_mono g h1
  rw [cj_cj, mul_inv_cancel, cj_one] at h2
  exact h2

theorem cj_phi_eq {g : G} {R : Subgroup G} (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    cj g (phi R) = phi R := by
  rw [← phi_cj, cj_eq_of_mem_normalizer hg]

theorem conj_mem_phi {g : G} {R : Subgroup G} (hg : g ∈ Subgroup.normalizer (R : Set G)) {x : G}
    (hx : x ∈ phi R) : g * x * g⁻¹ ∈ phi R := by
  rw [← cj_phi_eq hg, mem_cj]
  simpa [mul_assoc] using hx

theorem le_normalizer_phi {R S : Subgroup G} (h : S ≤ Subgroup.normalizer (R : Set G)) :
    S ≤ Subgroup.normalizer (phi R : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_phi (h hg), fun hx => ?_⟩
  have := conj_mem_phi (h (S.inv_mem hg)) hx
  simpa [mul_assoc] using this

theorem phi_eq_of_decomp {R R₀ Z : Subgroup G} (hR₀ : R₀ ≤ R) (hZR : Z ≤ R)
    (hZc : ∀ z ∈ Z, ∀ a ∈ R, z * a = a * z) (hZe : ∀ z ∈ Z, z * z = 1)
    (hdec : ∀ a ∈ R, ∃ r ∈ R₀, ∃ z ∈ Z, a = r * z) : phi R = phi R₀ := by
  refine le_antisymm ?_ (phi_mono hR₀)
  have hcz : ∀ z ∈ Z, ∀ a ∈ R, z * a * z⁻¹ = a := fun z hz a ha => by
    rw [hZc z hz a ha]; group
  refine phi_le_of (fun a ha => ?_) (fun a ha b hb => ?_)
  · obtain ⟨r, hr, z, hz, rfl⟩ := hdec a ha
    have : r * z * (r * z) = r * r := by
      have h1 : z * r = r * z := hZc z hz r (hR₀ hr)
      calc r * z * (r * z) = r * (z * r) * z := by group
        _ = r * (r * z) * z := by rw [h1]
        _ = r * r * (z * z) := by group
        _ = r * r := by rw [hZe z hz, mul_one]
    rw [this]
    exact sq_mem_phi hr
  · obtain ⟨r, hr, z, hz, rfl⟩ := hdec a ha
    obtain ⟨s, hs, w, hw, rfl⟩ := hdec b hb
    have hzs : z * s = s * z := hZc z hz s (hR₀ hs)
    have hwr : w * r = r * w := hZc w hw r (hR₀ hr)
    have hwz : w * z = z * w := hZc w hw z (hZR hz)
    have : ⁅r * z, s * w⁆ = ⁅r, s⁆ := by
      simp only [commutatorElement_def]
      have hzs' : z * s = s * z := hzs
      calc r * z * (s * w) * (r * z)⁻¹ * (s * w)⁻¹
          = r * (z * s) * w * z⁻¹ * r⁻¹ * w⁻¹ * s⁻¹ := by group
        _ = r * (s * z) * w * z⁻¹ * r⁻¹ * w⁻¹ * s⁻¹ := by rw [hzs']
        _ = r * s * (z * w) * z⁻¹ * r⁻¹ * w⁻¹ * s⁻¹ := by group
        _ = r * s * (w * z) * z⁻¹ * r⁻¹ * w⁻¹ * s⁻¹ := by rw [hwz]
        _ = r * s * w * r⁻¹ * w⁻¹ * s⁻¹ := by group
        _ = r * s * (w * r⁻¹) * w⁻¹ * s⁻¹ := by group
        _ = r * s * r⁻¹ * s⁻¹ := by
          have hwr' : w * r⁻¹ = r⁻¹ * w := by
            have := hZc w hw r⁻¹ (R₀.inv_mem hr |> hR₀)
            exact this
          rw [hwr']
          group
    rw [this]
    exact comm_mem_phi hr hs

theorem card_cj (g : G) (H : Subgroup G) : Nat.card (cj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

section Finite

variable [Finite G]

theorem cj_eq_of_cj_le {g : G} {H : Subgroup G} (h : cj g H ≤ H) : cj g H = H :=
  Subgroup.eq_of_le_of_card_ge h (by rw [card_cj])

theorem mem_normalizer_of_cj_le {g : G} {H : Subgroup G} (h : cj g H ≤ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  have he := cj_eq_of_cj_le h
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    apply h
    rw [mem_cj]
    simpa [mul_assoc] using hx
  · intro hx
    have : g * x * g⁻¹ ∈ cj g H := by rw [he]; exact hx
    rw [mem_cj] at this
    simpa [mul_assoc] using this

end Finite

theorem relIndex_cj {g : G} {H K : Subgroup G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    (cj g H).relIndex K = H.relIndex K := by
  have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) H K
    (MulAut.conj g).injective
  rw [CFSG.Quasithin.map_conj_eq_of_mem_normalizer hg] at this
  exact this

theorem le_or_le_of_forall_mem {A B E : Subgroup G} (h : ∀ e ∈ E, e ∈ A ∨ e ∈ B) :
    E ≤ A ∨ E ≤ B := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨⟨e₁, he₁, he₁A⟩, ⟨e₂, he₂, he₂B⟩⟩ :=
    And.intro (IsConcreteLE.not_le_iff_exists.mp hcon.1) (IsConcreteLE.not_le_iff_exists.mp hcon.2)
  have h1 : e₁ ∈ B := (h e₁ he₁).resolve_left he₁A
  have h2 : e₂ ∈ A := (h e₂ he₂).resolve_right he₂B
  rcases h (e₁ * e₂) (E.mul_mem he₁ he₂) with h3 | h3
  · apply he₁A
    have := A.mul_mem h3 (A.inv_mem h2)
    simpa using this
  · apply he₂B
    have := B.mul_mem (B.inv_mem h1) h3
    simpa using this

end CFSG.Quasithin.F53Push
