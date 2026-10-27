module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Frat
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1One

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem GoldHyp.eq_bot_of_normalizes (h : GoldHyp G₁ G₂) {N : Subgroup D}
    (h1 : G₁ ≤ Subgroup.normalizer (N : Set D)) (h2 : G₂ ≤ Subgroup.normalizer (N : Set D))
    (hle : N ≤ G₁ ⊓ G₂) : N = ⊥ := by
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (N : Set D) :=
      (sup_le h1 h2) (h.amalgam.gen ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.1 hg n).1 hn
  have := h.amalgam.toIsGoldschmidtVTriple.le_pCore_of_normal_le_inf hle
  rw [h.amalgam.pCore_eq_bot] at this
  exact le_bot_iff.mp this

theorem GoldHyp.relIndex_inf_left (h : GoldHyp G₁ G₂) (hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) :
    (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) (pCoreOf 2 G₁)
    (G₁ ⊓ G₂) inf_le_left h.pCoreOf_left_le
  rw [h.relIndex_inf_pCoreOf hne, h.relIndex_pCoreOf_T_left] at h1
  omega

theorem GoldHyp.relIndex_inf_right (h : GoldHyp G₁ G₂) (hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) :
    (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex (pCoreOf 2 G₂) = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) (pCoreOf 2 G₂)
    (G₁ ⊓ G₂) inf_le_right h.pCoreOf_right_le
  rw [h.relIndex_inf_pCoreOf hne, h.relIndex_pCoreOf_T_right] at h1
  omega

theorem GoldHyp.coset_left (h : GoldHyp G₁ G₂) (hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) {v : D}
    (hvQ : v ∈ pCoreOf 2 G₁) (hv : v ∉ pCoreOf 2 G₂) :
    ∀ q ∈ pCoreOf 2 G₁, q ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ∨
      ∃ r ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂, q = v * r := fun _ hq =>
  index_two_decomp (h.relIndex_inf_left hne) hvQ (fun hr => hv hr.2) hq

theorem GoldHyp.coset_right (h : GoldHyp G₁ G₂) (hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) {v : D}
    (hvQ : v ∈ pCoreOf 2 G₂) (hv : v ∉ pCoreOf 2 G₁) :
    ∀ q ∈ pCoreOf 2 G₂, q ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ∨
      ∃ r ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂, q = v * r := fun _ hq =>
  index_two_decomp (h.relIndex_inf_right hne) hvQ (fun hr => hv hr.1) hq

theorem GoldHyp.sqCommSub_inf_eq_bot (h : GoldHyp G₁ G₂) (hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂)
    {v₁ v₂ : D} (hv₁Q : v₁ ∈ pCoreOf 2 G₁) (hv₁ : v₁ ∉ pCoreOf 2 G₂)
    (hv₂Q : v₂ ∈ pCoreOf 2 G₂) (hv₂ : v₂ ∉ pCoreOf 2 G₁)
    (hv₁c : ∀ q ∈ pCoreOf 2 G₁, v₁ * q = q * v₁) (hv₂c : ∀ q ∈ pCoreOf 2 G₂, v₂ * q = q * v₂)
    (hv₁2 : v₁ * v₁ = 1) (hv₂2 : v₂ * v₂ = 1) :
    sqCommSub (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) = ⊥ := by
  have e₁ := sqCommSub_eq_of_coset inf_le_left hv₁c hv₁2 (h.coset_left hne hv₁Q hv₁)
  have e₂ := sqCommSub_eq_of_coset inf_le_right hv₂c hv₂2 (h.coset_right hne hv₂Q hv₂)
  refine h.eq_bot_of_normalizes ?_ ?_ ?_
  · intro g hg
    rw [← e₁]
    exact le_normalizer_sqCommSub (le_normalizer_pCoreOf 2 G₁ hg)
  · intro g hg
    rw [← e₂]
    exact le_normalizer_sqCommSub (le_normalizer_pCoreOf 2 G₂ hg)
  · exact (sqCommSub_le_self _).trans (inf_le_left.trans h.pCoreOf_left_le)

theorem Vertex.comm_mem_V {H T : Subgroup D} (hv : Vertex H T) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt H T z V) {R : Subgroup D} {v w : D}
    (hRidx : R.relIndex (pCoreOf 2 H) = 2) (hvV : v ∈ V) (hvR : v ∉ R)
    (hwT : w ∈ T) (hwQ : w ∉ pCoreOf 2 H) (hwv : w * v * w⁻¹ = v * z)
    (hRw : ∀ r ∈ R, r * w = w * r)
    (hQab : ∀ a ∈ pCoreOf 2 H, ∀ b ∈ pCoreOf 2 H, a * b = b * a) :
    ∀ g ∈ H, ∀ q ∈ pCoreOf 2 H, g * q * g⁻¹ * q⁻¹ ∈ V := by
  have hTH : T ≤ H := hv.T_le
  have hQT : pCoreOf 2 H ≤ T := hv.pCoreOf_le
  have hQN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set D) := le_normalizer_pCoreOf 2 H
  have hVN : H ≤ Subgroup.normalizer (V : Set D) := hn.reduced.2.1
  have hvQ : v ∈ pCoreOf 2 H := hn.le_pCoreOf hvV
  have hzV : z ∈ V := hn.z_mem_V
  have hvz : v * z = z * v := Subgroup.mem_centralizer_iff.mp hn.z_mem.2 v (hQT hvQ)
  have hwq : ∀ q ∈ pCoreOf 2 H, w * q * w⁻¹ * q⁻¹ ∈ V := by
    intro q hq
    rcases index_two_decomp hRidx hvQ hvR hq with h | ⟨r, hr, rfl⟩
    · have : w * q * w⁻¹ * q⁻¹ = 1 := by
        have h1 : w * q = q * w := (hRw q h).symm
        rw [h1]; group
      rw [this]; exact V.one_mem
    · have hrw : w * r * w⁻¹ = r := by
        have h1 : w * r = r * w := (hRw r hr).symm
        rw [h1]; group
      have : w * (v * r) * w⁻¹ * (v * r)⁻¹ = z := by
        calc w * (v * r) * w⁻¹ * (v * r)⁻¹ = (w * v * w⁻¹) * (w * r * w⁻¹) * r⁻¹ * v⁻¹ := by
              group
          _ = (v * z) * r * r⁻¹ * v⁻¹ := by rw [hwv, hrw]
          _ = v * z * v⁻¹ := by group
          _ = z := by rw [hvz]; group
      rw [this]; exact hzV
  have hTq : ∀ t ∈ T, ∀ q ∈ pCoreOf 2 H, t * q * t⁻¹ * q⁻¹ ∈ V := by
    intro t ht q hq
    rcases index_two_decomp hv.relIndex_pCoreOf_T hwT hwQ ht with h | ⟨q', hq', rfl⟩
    · have : t * q * t⁻¹ * q⁻¹ = 1 := by
        have h1 : t * q = q * t := hQab t h q hq
        rw [h1]; group
      rw [this]; exact V.one_mem
    · have h1 : q' * q = q * q' := hQab q' hq' q hq
      have : w * q' * q * (w * q')⁻¹ * q⁻¹ = w * q * w⁻¹ * q⁻¹ := by
        calc w * q' * q * (w * q')⁻¹ * q⁻¹ = w * (q' * q) * q'⁻¹ * w⁻¹ * q⁻¹ := by group
          _ = w * (q * q') * q'⁻¹ * w⁻¹ * q⁻¹ := by rw [h1]
          _ = w * q * w⁻¹ * q⁻¹ := by group
      rw [this]; exact hwq q hq
  let H₀ : Subgroup D :=
    { carrier := {g | g ∈ H ∧ ∀ q ∈ pCoreOf 2 H, g * q * g⁻¹ * q⁻¹ ∈ V}
      one_mem' := ⟨H.one_mem, fun q _ => by simp⟩
      mul_mem' := by
        rintro g g' ⟨hgH, hg⟩ ⟨hg'H, hg'⟩
        refine ⟨H.mul_mem hgH hg'H, fun q hq => ?_⟩
        have e : (g * g') * q * (g * g')⁻¹ * q⁻¹ =
            (g * (g' * q * g'⁻¹ * q⁻¹) * g⁻¹) * (g * q * g⁻¹ * q⁻¹) := by group
        rw [e]
        exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVN hgH) _).mp (hg' q hq)) (hg q hq)
      inv_mem' := by
        rintro g ⟨hgH, hg⟩
        refine ⟨H.inv_mem hgH, fun q hq => ?_⟩
        have hq' : g⁻¹ * q * g ∈ pCoreOf 2 H := by
          have := (Subgroup.mem_normalizer_iff.mp (hQN (H.inv_mem hgH)) q).mp hq
          simpa using this
        have e : g⁻¹ * q * g⁻¹⁻¹ * q⁻¹ =
            (g * (g⁻¹ * q * g) * g⁻¹ * (g⁻¹ * q * g)⁻¹)⁻¹ := by group
        rw [e]
        exact V.inv_mem (hg _ hq') }
  have hH₀H : H₀ ≤ H := fun g hg => hg.1
  have hTH₀ : T ≤ H₀ := fun t ht => ⟨hTH ht, hTq t ht⟩
  have hH₀N : ∀ h' ∈ H, ∀ g ∈ H₀, h' * g * h'⁻¹ ∈ H₀ := by
    intro h' hh' g hg
    obtain ⟨hgH, hg'⟩ := hg
    refine ⟨H.mul_mem (H.mul_mem hh' hgH) (H.inv_mem hh'), fun q hq => ?_⟩
    have hq' : h'⁻¹ * q * h' ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (hQN (H.inv_mem hh')) q).mp hq
      simpa using this
    have e : (h' * g * h'⁻¹) * q * (h' * g * h'⁻¹)⁻¹ * q⁻¹ =
        h' * (g * (h'⁻¹ * q * h') * g⁻¹ * (h'⁻¹ * q * h')⁻¹) * h'⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hVN hh') _).mp (hg' _ hq')
  have h3 := Subgroup.relIndex_mul_relIndex T H₀ H hTH₀ hH₀H
  rw [hv.index_eq] at h3
  have hdvd : T.relIndex H₀ ∣ 3 := Dvd.intro _ h3
  have hH₀ : H ≤ H₀ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h4 | h4
    · exfalso
      have hH₀T : H₀ ≤ T := Subgroup.relIndex_eq_one.mp h4
      have hTN : H ≤ Subgroup.normalizer (T : Set D) := by
        intro h' hh'
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          exact hH₀T (hH₀N h' hh' y (hTH₀ hy))
        · intro hy
          have := hH₀N h'⁻¹ (H.inv_mem hh') _ (hTH₀ hy)
          simpa [mul_assoc] using hH₀T this
      have hTQ : T ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer 2 hTH hTN hv.isPGroup
      have h5 : (pCoreOf 2 H).relIndex T = 1 := Subgroup.relIndex_eq_one.mpr hTQ
      have h6 := hv.relIndex_pCoreOf_T
      omega
    · rw [h4] at h3
      exact Subgroup.relIndex_eq_one.mp (by omega)
  intro g hg q hq
  exact (hH₀ hg).2 q hq

theorem Vertex.exists_mul_of_comm_mem_V {H T : Subgroup D} (hv : Vertex H T) {z : D}
    {V : Subgroup D} {R : Subgroup D}
    (hRQ : R ≤ pCoreOf 2 H) (hRZ : R ≤ centerOf T) (hZR : centerOf T ≤ R)
    (hR2 : ∀ r ∈ R, r * r = 1)
    (hQab : ∀ a ∈ pCoreOf 2 H, ∀ b ∈ pCoreOf 2 H, a * b = b * a)
    (hcomm : ∀ g ∈ H, ∀ q ∈ pCoreOf 2 H, g * q * g⁻¹ * q⁻¹ ∈ V)
    (hRV : ∀ u ∈ V, u ∈ R → u = 1 ∨ u = z) :
    ∀ r ∈ R, ∃ k ∈ R ⊓ Subgroup.centralizer (H : Set D), ∃ e ∈ Subgroup.zpowers z,
      r = k * e := by
  intro r hr
  by_cases hfix : ∀ g ∈ H, g * r * g⁻¹ = r
  · refine ⟨r, ⟨hr, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩, 1, Subgroup.one_mem _,
      by simp⟩
    exact mul_eq_of_conj_eq (hfix g hg)
  · push Not at hfix
    obtain ⟨g, hg, hgr⟩ := hfix
    have hrZ : r ∈ centerOf T := hRZ hr
    have hr2' : r ^ 2 = 1 := by rw [pow_two]; exact hR2 r hr
    obtain ⟨x, z', V', hxH, hx3, hxr, hz', hn', -⟩ :=
      exists_natural_data hv hrZ hr2' ⟨g, hg, hgr⟩
    have hTH : T ≤ H := hv.T_le
    have hQN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set D) := le_normalizer_pCoreOf 2 H
    have hrQ : r ∈ pCoreOf 2 H := hRQ hr
    have hz'Z : z' ∈ centerOf T := hn'.z_mem
    have hz'R : z' ∈ R := hZR hz'Z
    have hz'2 : z' * z' = 1 := by have := hn'.z_sq; rwa [pow_two] at this
    have hNZ : r * z' ∈ centerOf T := (centerOf T).mul_mem hrZ hz'Z
    obtain ⟨w₁, hw₁⟩ : ∃ w : D, w = x * r * x⁻¹ := ⟨_, rfl⟩
    obtain ⟨w₂, hw₂⟩ : ∃ w : D, w = x * x * r * (x * x)⁻¹ := ⟨_, rfl⟩
    have hw₁Q : w₁ ∈ pCoreOf 2 H := by
      rw [hw₁]; exact (Subgroup.mem_normalizer_iff.mp (hQN hxH) r).mp hrQ
    have hw₂Q : w₂ ∈ pCoreOf 2 H := by
      rw [hw₂]; exact (Subgroup.mem_normalizer_iff.mp (hQN (H.mul_mem hxH hxH)) r).mp hrQ
    have hz'e : z' = w₁ * w₂ := by rw [hz', hw₁, hw₂]
    have hxN : x * (r * z') * x⁻¹ = r * z' := by
      have hx₁ : x * w₁ * x⁻¹ = w₂ := by rw [hw₁, hw₂]; group
      have hx₂ : x * w₂ * x⁻¹ = r := by
        rw [hw₂]
        calc x * (x * x * r * (x * x)⁻¹) * x⁻¹ = (x * x * x) * r * (x * x * x)⁻¹ := by group
          _ = r := by rw [hx3]; group
      calc x * (r * z') * x⁻¹ = (x * r * x⁻¹) * ((x * w₁ * x⁻¹) * (x * w₂ * x⁻¹)) := by
            rw [hz'e]; group
        _ = w₁ * (w₂ * r) := by rw [hx₁, hx₂, ← hw₁]
        _ = r * (w₁ * w₂) := by
            calc w₁ * (w₂ * r) = w₁ * (r * w₂) := by rw [hQab w₂ hw₂Q r hrQ]
              _ = (w₁ * r) * w₂ := (mul_assoc _ _ _).symm
              _ = (r * w₁) * w₂ := by rw [hQab w₁ hw₁Q r hrQ]
              _ = r * (w₁ * w₂) := mul_assoc _ _ _
        _ = r * z' := by rw [hz'e]
    have hxT : x ∉ T := fun hxT => hxr ((Subgroup.mem_centralizer_iff.mp hrZ.2 x hxT).symm ▸
      by group)
    have hNH : ∀ y ∈ H, y * (r * z') = (r * z') * y := by
      let C : Subgroup D := H ⊓ Subgroup.centralizer ({r * z'} : Set D)
      have hTC : T ≤ C := fun t ht => ⟨hTH ht, Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact (Subgroup.mem_centralizer_iff.mp hNZ.2 t ht).symm⟩
      have hxC : x ∈ C := ⟨hxH, Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact (mul_eq_of_conj_eq hxN).symm⟩
      have hCH : C ≤ H := inf_le_left
      have h3 := Subgroup.relIndex_mul_relIndex T C H hTC hCH
      rw [hv.index_eq] at h3
      have hdvd : T.relIndex C ∣ 3 := Dvd.intro _ h3
      have hHC : H ≤ C := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h4 | h4
        · exact absurd (Subgroup.relIndex_eq_one.mp h4 hxC) hxT
        · rw [h4] at h3
          exact Subgroup.relIndex_eq_one.mp (by omega)
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hHC hy).2 (r * z') rfl).symm
    have hz'V : z' ∈ V := by
      have hu₁ := hcomm x hxH r hrQ
      have hu₂ := hcomm (x * x) (H.mul_mem hxH hxH) r hrQ
      have hr1 : r⁻¹ = r := inv_eq_of_mul_eq_one_right (hR2 r hr)
      rw [← hw₁, hr1] at hu₁
      rw [← hw₂, hr1] at hu₂
      have : z' = (w₁ * r) * (w₂ * r) := by
        rw [hz'e]
        calc w₁ * w₂ = w₁ * w₂ * (r * r) := by rw [hR2 r hr, mul_one]
          _ = w₁ * (w₂ * r) * r := by group
          _ = w₁ * (r * w₂) * r := by rw [hQab w₂ hw₂Q r hrQ]
          _ = (w₁ * r) * (w₂ * r) := by group
      rw [this]
      exact V.mul_mem hu₁ hu₂
    have hz'zp : z' ∈ Subgroup.zpowers z := by
      rcases hRV z' hz'V hz'R with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers z
    refine ⟨r * z', ⟨R.mul_mem hr hz'R, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩, z',
      hz'zp, ?_⟩
    · exact hNH y hy
    · rw [mul_assoc, hz'2, mul_one]

omit [Finite D] in
theorem card_sup_mul_card_inf_of_commute' {A B : Subgroup D}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have hBN : B ≤ Subgroup.normalizer (A : Set D) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact h a ha b hb
  have h1 := F1.relIndex_sup_eq_of_le_normalizer hBN
  have h2 := Subgroup.relIndex_mul_card A (B ⊔ A)
  have h3 := Subgroup.relIndex_mul_card A B
  have h4 : A ⊓ (B ⊔ A) = A := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [sup_comm] at h2
  rw [← h2, ← h3, inf_comm]
  ring

theorem card_le_four_of_factorizations {R K₁ K₂ : Subgroup D} {z : D} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hK₁R : K₁ ≤ R) (hK₂R : K₂ ≤ R)
    (hR₁ : ∀ r ∈ R, ∃ k ∈ K₁, ∃ e ∈ Subgroup.zpowers z, r = k * e)
    (hR₂ : ∀ r ∈ R, ∃ k ∈ K₂, ∃ e ∈ Subgroup.zpowers z, r = k * e)
    (hc₁ : ∀ k ∈ K₁, ∀ e ∈ Subgroup.zpowers z, k * e = e * k)
    (hc₂ : ∀ k ∈ K₂, ∀ e ∈ Subgroup.zpowers z, k * e = e * k)
    (hc₁₂ : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hK : K₁ ⊓ K₂ = ⊥) : Nat.card R ≤ 4 := by
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have key : ∀ K : Subgroup D, (∀ r ∈ R, ∃ k ∈ K, ∃ e ∈ Subgroup.zpowers z, r = k * e) →
      (∀ k ∈ K, ∀ e ∈ Subgroup.zpowers z, k * e = e * k) → Nat.card R ≤ 2 * Nat.card K := by
    intro K hR hc
    have hle : R ≤ K ⊔ Subgroup.zpowers z := by
      intro r hr
      obtain ⟨k, hk, e, he, rfl⟩ := hR r hr
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right he)
    have h1 := card_sup_mul_card_inf_of_commute' hc
    have hpos : 0 < Nat.card ↥(K ⊓ Subgroup.zpowers z) := Nat.card_pos
    have h2 : Nat.card R ≤ Nat.card ↥(K ⊔ Subgroup.zpowers z) := Subgroup.card_le_of_le hle
    rw [hzcard] at h1
    nlinarith
  have h₁ := key K₁ hR₁ hc₁
  have h₂ := key K₂ hR₂ hc₂
  have h12 := card_sup_mul_card_inf_of_commute' hc₁₂
  rw [hK, Subgroup.card_bot, mul_one] at h12
  have h3 : Nat.card ↥(K₁ ⊔ K₂) ≤ Nat.card R := Subgroup.card_le_of_le (sup_le hK₁R hK₂R)
  have hRpos : 0 < Nat.card R := Nat.card_pos
  rw [h12] at h3
  nlinarith [Nat.mul_le_mul h₁ h₂]

omit [Finite D] in
theorem IsNaturalAt.eq_one_or_eq_of_mem {H T : Subgroup D} {z : D} {V : Subgroup D}
    (hn : IsNaturalAt H T z V) {Q : Subgroup D} (hzQ : z ∈ Q) (hVQ : ¬ V ≤ Q) {u : D}
    (hu : u ∈ V) (huQ : u ∈ Q) : u = 1 ∨ u = z := by
  obtain ⟨a, -, -, hVset⟩ := hn.basis
  have hmemV : ∀ u, u ∈ V ↔ u = 1 ∨ u = z ∨ u = a ∨ u = z * a := by
    intro u
    have := Set.ext_iff.mp hVset u
    simpa using this
  have haQ : a ∈ Q → V ≤ Q := by
    intro haQ y hy
    rcases (hmemV y).mp hy with h | h | h | h
    · rw [h]; exact Q.one_mem
    · rw [h]; exact hzQ
    · rw [h]; exact haQ
    · rw [h]; exact Q.mul_mem hzQ haQ
  rcases (hmemV u).mp hu with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (haQ (h ▸ huQ)) hVQ
  · refine absurd (haQ ?_) hVQ
    have : a = z⁻¹ * u := by rw [h]; group
    rw [this]
    exact Q.mul_mem (Q.inv_mem hzQ) huQ

theorem card_le_sixteen_of_b_one (h : GoldHyp G₁ G₂) {z₁ z₂ : D} {V₁ V₂ : Subgroup D}
    (hn₁ : IsNaturalAt G₁ (G₁ ⊓ G₂) z₁ V₁) (hn₂ : IsNaturalAt G₂ (G₁ ⊓ G₂) z₂ V₂)
    (hV₁ : ¬ V₁ ≤ pCoreOf 2 G₂) (hV₂ : ¬ V₂ ≤ pCoreOf 2 G₁) :
    Nat.card ↥(G₁ ⊓ G₂) ≤ 16 := by
  obtain ⟨hzz, v₁, hv₁V, v₂, hv₂V, hv₁Q, hv₂Q, hv₁2, hv₂2, hc₁, hc₂, hRc, hT⟩ :=
    b_one_structure h hn₁ hn₂ hV₁ hV₂
  subst hzz
  have hv₁Q₁ : v₁ ∈ pCoreOf 2 G₁ := hn₁.le_pCoreOf hv₁V
  have hv₂Q₂ : v₂ ∈ pCoreOf 2 G₂ := hn₂.le_pCoreOf hv₂V
  have hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂ := fun e => hv₁Q (e ▸ hv₁Q₁)
  have hv₁T : v₁ ∈ G₁ ⊓ G₂ := h.pCoreOf_left_le hv₁Q₁
  have hv₂T : v₂ ∈ G₁ ⊓ G₂ := h.pCoreOf_right_le hv₂Q₂
  have hv₁c : ∀ q ∈ pCoreOf 2 G₁, v₁ * q = q * v₁ := fun q hq =>
    (Subgroup.mem_centralizer_iff.mp (hn₁.le_center hv₁V).2 q hq).symm
  have hv₂c : ∀ q ∈ pCoreOf 2 G₂, v₂ * q = q * v₂ := fun q hq =>
    (Subgroup.mem_centralizer_iff.mp (hn₂.le_center hv₂V).2 q hq).symm
  obtain ⟨hR1, hR2⟩ := elemAbelian_of_sqCommSub_eq_bot
    (h.sqCommSub_inf_eq_bot hne hv₁Q₁ hv₁Q hv₂Q₂ hv₂Q hv₁c hv₂c hv₁2 hv₂2)
  have hQ₁ := elemAbelian_of_coset inf_le_left hv₁c hv₁2 (h.coset_left hne hv₁Q₁ hv₁Q) hR1 hR2
  have hQ₂ := elemAbelian_of_coset inf_le_right hv₂c hv₂2 (h.coset_right hne hv₂Q₂ hv₂Q) hR1 hR2
  have hRv₁ : ∀ r ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂, r * v₁ = v₁ * r := fun r hr =>
    (hRc hr v₁ (Set.mem_insert _ _)).symm
  have hRv₂ : ∀ r ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂, r * v₂ = v₂ * r := fun r hr =>
    (hRc hr v₂ (Set.mem_insert_of_mem _ (Set.mem_singleton _))).symm
  have hRZ : pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ≤ centerOf (G₁ ⊓ G₂) := by
    intro r hr
    refine ⟨(inf_le_left.trans h.pCoreOf_left_le) hr, Subgroup.mem_centralizer_iff.mpr ?_⟩
    have hcent : G₁ ⊓ G₂ ≤ Subgroup.centralizer ({r} : Set D) := by
      rw [hT]
      refine sup_le (sup_le ?_ ?_) ?_
      · intro s hs
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact hR2 r hr s hs
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact hRv₁ r hr
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact hRv₂ r hr
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (hcent ht) r rfl).symm
  have hZR : centerOf (G₁ ⊓ G₂) ≤ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ := fun x hx =>
    ⟨h.centerOf_le_pCoreOf_left hx, h.centerOf_le_pCoreOf_right hx⟩
  have hR1' : ∀ r ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂, r * r = 1 := hR1
  have hcomm₁ := h.vertex_left.comm_mem_V hn₁ (R := pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂)
    (h.relIndex_inf_left hne) hv₁V (fun hr => hv₁Q hr.2) hv₂T hv₂Q hc₁ hRv₂ hQ₁.1
  have hcomm₂ := h.vertex_right.comm_mem_V hn₂ (R := pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂)
    (h.relIndex_inf_right hne) hv₂V (fun hr => hv₂Q hr.1) hv₁T hv₁Q hc₂ hRv₁ hQ₂.1
  have hz₁Q₂ : z₁ ∈ pCoreOf 2 G₂ := h.centerOf_le_pCoreOf_right hn₁.z_mem
  have hz₁Q₁ : z₁ ∈ pCoreOf 2 G₁ := h.centerOf_le_pCoreOf_left hn₁.z_mem
  have hK₁ := h.vertex_left.exists_mul_of_comm_mem_V (z := z₁) (V := V₁)
    (R := pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) inf_le_left hRZ hZR hR1' hQ₁.1 hcomm₁
    (fun u hu huR => hn₁.eq_one_or_eq_of_mem hz₁Q₂ hV₁ hu huR.2)
  have hK₂ := h.vertex_right.exists_mul_of_comm_mem_V (z := z₁) (V := V₂)
    (R := pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) inf_le_right hRZ hZR hR1' hQ₂.1 hcomm₂
    (fun u hu huR => hn₂.eq_one_or_eq_of_mem hz₁Q₁ hV₂ hu huR.1)
  have hz₁2 : z₁ * z₁ = 1 := by have := hn₁.z_sq; rwa [pow_two] at this
  have hTz : z₁ ∈ G₁ ⊓ G₂ := hn₁.z_mem.1
  have hRT : pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ≤ G₁ ⊓ G₂ := inf_le_left.trans h.pCoreOf_left_le
  have hK : ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) ⊓ Subgroup.centralizer (G₁ : Set D)) ⊓
      ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) ⊓ Subgroup.centralizer (G₂ : Set D)) = ⊥ := by
    refine h.eq_bot_of_normalizes ?_ ?_ ?_
    · have : ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) ⊓ Subgroup.centralizer (G₁ : Set D)) ⊓
          ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) ⊓ Subgroup.centralizer (G₂ : Set D)) ≤
          Subgroup.centralizer (G₁ : Set D) := inf_le_left.trans inf_le_right
      exact (Subgroup.le_centralizer_iff.mp this).trans (Subgroup.centralizer_le_normalizer _)
    · have : ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) ⊓ Subgroup.centralizer (G₁ : Set D)) ⊓
          ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) ⊓ Subgroup.centralizer (G₂ : Set D)) ≤
          Subgroup.centralizer (G₂ : Set D) := inf_le_right.trans inf_le_right
      exact (Subgroup.le_centralizer_iff.mp this).trans (Subgroup.centralizer_le_normalizer _)
    · exact (inf_le_left.trans inf_le_left).trans hRT
  have hc₁ : ∀ k ∈ (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) ⊓ Subgroup.centralizer (G₁ : Set D),
      ∀ e ∈ Subgroup.zpowers z₁, k * e = e * k := by
    intro k hk e he
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have hkz : k * z₁ = z₁ * k := (Subgroup.mem_centralizer_iff.mp hk.2 z₁ hTz.1).symm
    exact (show Commute k z₁ from hkz).zpow_right m
  have hc₂ : ∀ k ∈ (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) ⊓ Subgroup.centralizer (G₂ : Set D),
      ∀ e ∈ Subgroup.zpowers z₁, k * e = e * k := by
    intro k hk e he
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have hkz : k * z₁ = z₁ * k := (Subgroup.mem_centralizer_iff.mp hk.2 z₁ hTz.2).symm
    exact (show Commute k z₁ from hkz).zpow_right m
  have hc₁₂ : ∀ a ∈ (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) ⊓ Subgroup.centralizer (G₁ : Set D),
      ∀ b ∈ (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) ⊓ Subgroup.centralizer (G₂ : Set D), a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp ha.2 b (hRT hb.1).1).symm
  have hcard := card_le_four_of_factorizations hz₁2 hn₁.z_ne inf_le_left inf_le_left hK₁ hK₂
    hc₁ hc₂ hc₁₂ hK
  have h4 := h.relIndex_inf_pCoreOf hne
  have h5 := Subgroup.relIndex_mul_card (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) (G₁ ⊓ G₂)
  rw [inf_of_le_left hRT, h4] at h5
  omega

end GoldAmL

end F6

end CFSG.Quasithin
