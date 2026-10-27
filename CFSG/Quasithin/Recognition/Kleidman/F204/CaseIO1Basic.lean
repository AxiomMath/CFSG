module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CritB2

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

section Generic

variable {G : Type*} [Group G]

theorem natCard_subgroupOf' {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem card_map_mul_card_inf {N : Type*} [Group N] (φ : G →* N) (K : Subgroup G) :
    Nat.card (K.map φ) * Nat.card (K ⊓ φ.ker : Subgroup G) = Nat.card K := by
  have h1 := Subgroup.card_ker_mul_card_range (φ.comp K.subtype)
  have h2 : (φ.comp K.subtype).range = K.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h3 : (φ.comp K.subtype).ker = φ.ker.subgroupOf K := rfl
  rw [h3, h2] at h1
  have h4 : Nat.card (φ.ker.subgroupOf K) = Nat.card (K ⊓ φ.ker : Subgroup G) := by
    have : φ.ker.subgroupOf K = (K ⊓ φ.ker).subgroupOf K := by
      rw [Subgroup.inf_subgroupOf_left]
    rw [this, natCard_subgroupOf' inf_le_left]
  rw [h4] at h1
  rw [mul_comm]; exact h1

theorem exists_mul_ker_of_card [Finite G] {P K M Q : Subgroup G} {N : Type*} [Group N]
    (φ : ↥P →* N) (hker : ∀ p : ↥P, φ p = 1 ↔ (p : G) ∈ Q) (hKM : K ≤ M) (hMP : M ≤ P)
    (h : Nat.card (K ⊓ Q : Subgroup G) * Nat.card M =
      Nat.card K * Nat.card (M ⊓ Q : Subgroup G)) :
    ∀ m ∈ M, ∃ k ∈ K, k⁻¹ * m ∈ Q := by
  have hKP : K ≤ P := hKM.trans hMP
  have hkerQ : φ.ker = Q.subgroupOf P := by
    ext p; rw [MonoidHom.mem_ker, hker]; rfl
  set K₀ : Subgroup ↥P := K.subgroupOf P with hK₀
  set M₀ : Subgroup ↥P := M.subgroupOf P with hM₀
  have e1 := card_map_mul_card_inf φ K₀
  have e2 := card_map_mul_card_inf φ M₀
  have hinf : ∀ A : Subgroup G, A ≤ P →
      Nat.card (A.subgroupOf P ⊓ φ.ker : Subgroup ↥P) = Nat.card (A ⊓ Q : Subgroup G) := by
    intro A hA
    have : A.subgroupOf P ⊓ φ.ker = (A ⊓ Q).subgroupOf P := by
      ext p; rw [hkerQ]; simp [Subgroup.mem_subgroupOf]
    rw [this, natCard_subgroupOf' (inf_le_left.trans hA)]
  have cK : Nat.card (K₀ ⊓ φ.ker : Subgroup ↥P) = Nat.card (K ⊓ Q : Subgroup G) := hinf K hKP
  have cM : Nat.card (M₀ ⊓ φ.ker : Subgroup ↥P) = Nat.card (M ⊓ Q : Subgroup G) := hinf M hMP
  have cK' : Nat.card K₀ = Nat.card K := natCard_subgroupOf' hKP
  have cM' : Nat.card M₀ = Nat.card M := natCard_subgroupOf' hMP
  rw [cK, cK'] at e1
  rw [cM, cM'] at e2
  have hpa : 0 < Nat.card (K ⊓ Q : Subgroup G) := Nat.card_pos
  have hpb : 0 < Nat.card (M ⊓ Q : Subgroup G) := Nat.card_pos
  have hcard : Nat.card (K₀.map φ) = Nat.card (M₀.map φ) := by
    have : Nat.card (K₀.map φ) * Nat.card (K ⊓ Q : Subgroup G) * Nat.card (M ⊓ Q : Subgroup G) =
        Nat.card (M₀.map φ) * Nat.card (M ⊓ Q : Subgroup G) * Nat.card (K ⊓ Q : Subgroup G) := by
      rw [e1, e2]; linarith
    have h5 : Nat.card (K₀.map φ) * (Nat.card (K ⊓ Q : Subgroup G) * Nat.card (M ⊓ Q : Subgroup G))
        = Nat.card (M₀.map φ) * (Nat.card (K ⊓ Q : Subgroup G) * Nat.card (M ⊓ Q : Subgroup G)) := by
      calc _ = Nat.card (K₀.map φ) * Nat.card (K ⊓ Q : Subgroup G) *
            Nat.card (M ⊓ Q : Subgroup G) := by ring
        _ = Nat.card (M₀.map φ) * Nat.card (M ⊓ Q : Subgroup G) *
            Nat.card (K ⊓ Q : Subgroup G) := this
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpa hpb) h5
  have hle : K₀.map φ ≤ M₀.map φ :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono P hKM)
  have : Finite ↥(M₀.map φ) := Finite.of_surjective
    (fun m : M₀ => (⟨φ m, m, m.2, rfl⟩ : ↥(M₀.map φ)))
    (by rintro ⟨_, m, hm, rfl⟩; exact ⟨⟨m, hm⟩, rfl⟩)
  have heq : K₀.map φ = M₀.map φ := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  intro m hm
  have hmem : φ ⟨m, hMP hm⟩ ∈ M₀.map φ := ⟨⟨m, hMP hm⟩, hm, rfl⟩
  rw [← heq] at hmem
  obtain ⟨k₀, hk₀, hφ⟩ := hmem
  refine ⟨(k₀ : G), hk₀, ?_⟩
  have : φ (k₀⁻¹ * ⟨m, hMP hm⟩) = 1 := by rw [map_mul, map_inv, hφ]; group
  exact (hker _).mp this

end Generic

section FrameFacts

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

abbrev Z2q (L1 L2 S : Subgroup G) : Subgroup G := Frame.Z2 L1 L2 S (quasithinOmegaOneCenter S)

structure NotLe (L1 L2 S : Subgroup G) (g : G) : Prop where
  left : ¬ conjSub g (Z2q L1 L2 S) ≤ Q2 L1 L2 S
  right : ¬ Z2q L1 L2 S ≤ conjSub g (Q2 L1 L2 S)

structure O1Hyp (L1 L2 S : Subgroup G) : Prop where
  norm1 : ∀ p ∈ P1 L1 L2 S, ∀ z ∈ quasithinOmegaOneCenter S,
    p * z * p⁻¹ ∈ quasithinOmegaOneCenter S
  card16 : Nat.card (Z2q L1 L2 S) = 16
  faith : ∀ s ∈ S, (∀ z ∈ Z2q L1 L2 S, s * z = z * s) → s ∈ Q2 L1 L2 S
  crit : ∀ g ∈ P1 L1 L2 S, g ∉ bigB L1 L2 S → NotLe L1 L2 S g →
    (conjSub g (Z2q L1 L2 S) ⊓ Q2 L1 L2 S).relIndex (conjSub g (Z2q L1 L2 S)) = 4 ∧
    (Z2q L1 L2 S ⊓ conjSub g (Q2 L1 L2 S)).relIndex (Z2q L1 L2 S) = 4
  exists_crit : ∃ g ∈ P1 L1 L2 S, g ∉ bigB L1 L2 S ∧ NotLe L1 L2 S g

variable (F : Frame L1 L2 S D X)
include F

omit F in
theorem Z_le_Z2q : quasithinOmegaOneCenter S ≤ Z2q L1 L2 S := le_conjClosure _ _

theorem Z2q_le_Q2 : Z2q L1 L2 S ≤ Q2 L1 L2 S := F.Z2_le_Q2 (zData_omega F)

theorem Z2q_le_Q1 : Z2q L1 L2 S ≤ Q1 L1 L2 S := Z2_le_Q1 F (zData_omega F)

theorem Z2q_comm : ∀ a ∈ Z2q L1 L2 S, ∀ y ∈ Q2 L1 L2 S, a * y = y * a :=
  F.Z2_comm (zData_omega F)

theorem Z2q_sq : ∀ a ∈ Z2q L1 L2 S, a * a = 1 := F.Z2_sq (zData_omega F)

omit F in
theorem Z2q_normal {p z : G} (hp : p ∈ P2 L1 L2 S) (hz : z ∈ Z2q L1 L2 S) :
    p * z * p⁻¹ ∈ Z2q L1 L2 S :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hp) z).mp hz

omit F in
theorem card_inf_of_relIndex {A B : Subgroup G} {n : ℕ} (h : (A ⊓ B).relIndex A = n) :
    n * Nat.card (A ⊓ B : Subgroup G) = Nat.card A := by
  have := Subgroup.relIndex_mul_card (H := A ⊓ B) (K := A)
  rwa [inf_eq_left.mpr (inf_le_left : A ⊓ B ≤ A), h] at this

omit F in
theorem comm_of_conj {a b g : G} (h : (g⁻¹ * a * g) * (g⁻¹ * b * g) = (g⁻¹ * b * g) * (g⁻¹ * a * g)) :
    a * b = b * a := by
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
    _ = b * a := by group

theorem S_le_P2 : S ≤ P2 L1 L2 S := fun _ hs =>
  (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) (F.mem_B_of_mem_S hs)

theorem conjSub_Q1 {g : G} (hg : g ∈ P1 L1 L2 S) : conjSub g (Q1 L1 L2 S) = Q1 L1 L2 S :=
  conjSub_eq_of_mem_normalizer (P1_le_normalizer_Q1 L1 L2 S hg)

theorem conjZ2q_le_Q1 {g : G} (hg : g ∈ P1 L1 L2 S) : conjSub g (Z2q L1 L2 S) ≤ Q1 L1 L2 S := by
  have := conjSub_mono g (Z2q_le_Q1 F)
  rwa [conjSub_Q1 F hg] at this

theorem conjZ2q_le_S {g : G} (hg : g ∈ P1 L1 L2 S) : conjSub g (Z2q L1 L2 S) ≤ S :=
  (conjZ2q_le_Q1 F hg).trans F.Q1_le_S

theorem conjZ2q_comm {g : G} : ∀ z ∈ conjSub g (Z2q L1 L2 S), ∀ y ∈ conjSub g (Q2 L1 L2 S),
    z * y = y * z := by
  intro z hz y hy
  rw [mem_conjSub] at hz hy
  exact comm_of_conj (Z2q_comm F _ hz _ hy)

theorem Z_le_conjZ2q (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S) :
    quasithinOmegaOneCenter S ≤ conjSub g (Z2q L1 L2 S) := by
  intro z hz
  rw [mem_conjSub]
  have := h.norm1 g⁻¹ ((P1 L1 L2 S).inv_mem hg) z hz
  rw [inv_inv] at this
  exact Z_le_Z2q this

theorem S_eq_mul (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S) (hgB : g ∉ bigB L1 L2 S)
    (hnot : NotLe L1 L2 S g) :
    ∀ s ∈ S, ∃ z ∈ conjSub g (Z2q L1 L2 S), ∃ q ∈ Q2 L1 L2 S, s = z * q := by
  obtain ⟨hr1, -⟩ := h.crit g hg hgB hnot
  obtain ⟨φ, -, hφk⟩ := exists_phi_P2 F
  have hK16 : Nat.card (conjSub g (Z2q L1 L2 S)) = 16 := by
    rw [CosetGeom.card_conjSub]; exact h.card16
  have hk4 : Nat.card (conjSub g (Z2q L1 L2 S) ⊓ Q2 L1 L2 S : Subgroup G) = 4 := by
    have := card_inf_of_relIndex hr1
    omega
  have hS4 : 4 * Nat.card (Q2 L1 L2 S) = Nat.card S := by
    have := Subgroup.relIndex_mul_card (H := Q2 L1 L2 S) (K := S)
    rwa [relIndex_Q2_S F, inf_eq_left.mpr F.Q2_le_S] at this
  have hSQ : S ⊓ Q2 L1 L2 S = Q2 L1 L2 S := inf_eq_right.mpr F.Q2_le_S
  have key := exists_mul_ker_of_card (P := P2 L1 L2 S) (K := conjSub g (Z2q L1 L2 S)) (M := S)
    (Q := Q2 L1 L2 S) φ hφk (conjZ2q_le_S F hg) (S_le_P2 F) (by
      rw [hk4, hK16, hSQ, ← hS4]; ring)
  intro s hs
  obtain ⟨k, hk, hkq⟩ := key s hs
  exact ⟨k, hk, k⁻¹ * s, hkq, by group⟩

theorem pair_data (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S) (hgB : g ∉ bigB L1 L2 S)
    (hnot : NotLe L1 L2 S g) :
    Nat.card (quasithinOmegaOneCenter S) = 4 ∧
    Z2q L1 L2 S ⊓ conjSub g (Q2 L1 L2 S) = quasithinOmegaOneCenter S ∧
    conjSub g (Z2q L1 L2 S) ⊓ Q2 L1 L2 S = quasithinOmegaOneCenter S := by
  obtain ⟨hr1, hr2⟩ := h.crit g hg hgB hnot
  have hY4 : Nat.card (Z2q L1 L2 S ⊓ conjSub g (Q2 L1 L2 S) : Subgroup G) = 4 := by
    have := card_inf_of_relIndex hr2
    rw [h.card16] at this
    omega
  have hYZ : Z2q L1 L2 S ⊓ conjSub g (Q2 L1 L2 S) ≤ quasithinOmegaOneCenter S := by
    rintro y ⟨hyZ, hyQ⟩
    have hyS : y ∈ S := F.Q2_le_S (Z2q_le_Q2 F hyZ)
    have hcent : y ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      obtain ⟨z, hz, q, hq, rfl⟩ := S_eq_mul F h hg hgB hnot s hs
      calc z * q * y = z * (q * y) := by group
        _ = z * (y * q) := by rw [← Z2q_comm F y hyZ q hq]
        _ = (z * y) * q := by group
        _ = (y * z) * q := by rw [conjZ2q_comm F z hz y hyQ]
        _ = y * (z * q) := by group
    have hsq : y ^ 2 = 1 := by rw [pow_two]; exact Z2q_sq F y hyZ
    exact Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hyS, hcent⟩, hsq⟩
  have hZY : quasithinOmegaOneCenter S ≤ Z2q L1 L2 S ⊓ conjSub g (Q2 L1 L2 S) :=
    le_inf Z_le_Z2q ((Z_le_conjZ2q F h hg).trans (conjSub_mono g (Z2q_le_Q2 F)))
  have heq1 : Z2q L1 L2 S ⊓ conjSub g (Q2 L1 L2 S) = quasithinOmegaOneCenter S :=
    le_antisymm hYZ hZY
  have hZ4 : Nat.card (quasithinOmegaOneCenter S) = 4 := by rw [← heq1]; exact hY4
  refine ⟨hZ4, heq1, ?_⟩
  have hK16 : Nat.card (conjSub g (Z2q L1 L2 S)) = 16 := by
    rw [CosetGeom.card_conjSub]; exact h.card16
  have hk4 : Nat.card (conjSub g (Z2q L1 L2 S) ⊓ Q2 L1 L2 S : Subgroup G) = 4 := by
    have := card_inf_of_relIndex hr1
    omega
  have hle : quasithinOmegaOneCenter S ≤ conjSub g (Z2q L1 L2 S) ⊓ Q2 L1 L2 S :=
    le_inf (Z_le_conjZ2q F h hg) (Z_le_Z2q.trans (Z2q_le_Q2 F))
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hk4, hZ4])).symm

theorem conj_inv_mem_Q1 {g x : G} (hg : g ∈ P1 L1 L2 S) (hx : x ∈ Q1 L1 L2 S) :
    g⁻¹ * x * g ∈ Q1 L1 L2 S := by
  have : x ∈ conjSub g (Q1 L1 L2 S) := by rw [conjSub_Q1 F hg]; exact hx
  rwa [mem_conjSub] at this

theorem comm_Q1Q2_conjZ (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hgB : g ∉ bigB L1 L2 S) (hnot : NotLe L1 L2 S g) :
    ∀ x ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S, ∀ z ∈ conjSub g (Z2q L1 L2 S),
      ⁅x, z⁆ ∈ quasithinOmegaOneCenter S := by
  intro x hx z hz
  obtain ⟨hxQ1, hxQ2⟩ := Subgroup.mem_inf.mp hx
  have hzS : z ∈ S := conjZ2q_le_S F hg hz
  have hzP : z ∈ P2 L1 L2 S := S_le_P2 F hzS
  have hxP : g⁻¹ * x * g ∈ P2 L1 L2 S := S_le_P2 F (F.Q1_le_S (conj_inv_mem_Q1 F hg hxQ1))
  have h1 : x * z * x⁻¹ ∈ conjSub g (Z2q L1 L2 S) := by
    rw [mem_conjSub] at hz ⊢
    have := Z2q_normal hxP hz
    convert this using 1
    group
  have h2 : ⁅x, z⁆ ∈ conjSub g (Z2q L1 L2 S) := by
    have : ⁅x, z⁆ = (x * z * x⁻¹) * z⁻¹ := by simp [commutatorElement_def]
    rw [this]
    exact (conjSub g (Z2q L1 L2 S)).mul_mem h1 ((conjSub g (Z2q L1 L2 S)).inv_mem hz)
  have h3 : ⁅x, z⁆ ∈ Q2 L1 L2 S := by
    have : ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) := by simp [commutatorElement_def]; group
    rw [this]
    refine (Q2 L1 L2 S).mul_mem hxQ2 ?_
    exact (Subgroup.mem_normalizer_iff.mp (P2_le_normalizer_Q2 L1 L2 S hzP) x⁻¹).mp
      ((Q2 L1 L2 S).inv_mem hxQ2)
  rw [← (pair_data F h hg hgB hnot).2.2]
  exact ⟨h2, h3⟩

theorem Q1_le_mul (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hgB : g ∉ bigB L1 L2 S) (hnot : NotLe L1 L2 S g) :
    ∀ y ∈ Q1 L1 L2 S, ∃ z ∈ Z2q L1 L2 S, ∃ q ∈ conjSub g (Q2 L1 L2 S), y = z * q := by
  obtain ⟨-, hr2⟩ := h.crit g hg hgB hnot
  have hg' : g⁻¹ ∈ P1 L1 L2 S := (P1 L1 L2 S).inv_mem hg
  have hg'B : g⁻¹ ∉ bigB L1 L2 S := fun hh => hgB (by simpa using (bigB L1 L2 S).inv_mem hh)
  have hnot' : NotLe L1 L2 S g⁻¹ := by
    refine ⟨?_, fun hle => hnot.left ((conjSub_le_iff g).mpr hle)⟩
    intro hle
    have h1 : Z2q L1 L2 S ≤ conjSub g (Q2 L1 L2 S) := by
      have := conjSub_mono g hle
      rwa [conjSub_inv_conjSub] at this
    rw [inf_eq_left.mpr h1, Subgroup.relIndex_self] at hr2
    omega
  intro y hy
  have hy1 : g⁻¹ * y * g ∈ S := F.Q1_le_S (conj_inv_mem_Q1 F hg hy)
  obtain ⟨z, hz, q, hq, hzq⟩ := S_eq_mul F h hg' hg'B hnot' _ hy1
  refine ⟨g * z * g⁻¹, ?_, g * q * g⁻¹, ?_, ?_⟩
  · rw [mem_conjSub] at hz
    simpa using hz
  · rw [mem_conjSub]
    have e : g⁻¹ * (g * q * g⁻¹) * g = q := by group
    rw [e]; exact hq
  · calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = g * (z * q) * g⁻¹ := by rw [hzq]
      _ = _ := by group

end FrameFacts

end CFSG.Quasithin.Kleidman.F204
