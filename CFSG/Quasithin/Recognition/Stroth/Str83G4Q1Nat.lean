module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Shape
public import CFSG.Quasithin.Recognition.Stroth.Str83G4C2
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CP2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem str83G4_conj_eq_of_mem_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {g z : G}
    (hg : g ∈ L1 ⊔ S) (hz : z ∈ Z1 L1 L2 S) : g * z * g⁻¹ = z := by
  have h := Subgroup.mem_centralizer_iff.mp (str83G4_sup_le_centralizer_z1 hfr hg) z hz
  rw [← h]
  group

private theorem str83G4_commutator_mem_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {u : G}
    (hu : u ∈ Q1 L1 L2 S) {t : G} (ht : t ∈ L1 ⊔ S) : ⁅u, t⁆ ∈ Q1 L1 L2 S := by
  have htu : t * u * t⁻¹ ∈ Q1 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp
      ((sup_left_le_p1 L1 L2 S).trans
        (le_normalizer_pCoreOf 2 (P1 L1 L2 S)) ht) u).mp hu
  have e : ⁅u, t⁆ = u * (t * u * t⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Q1 L1 L2 S).mul_mem hu ((Q1 L1 L2 S).inv_mem htu)

theorem str83G4_phi_mul_left
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {u : G}
    (hu : u ∈ Q1 L1 L2 S) {x y : G} (hx : x ∈ str83X L1 L2 S)
    (hy : y ∈ str83X L1 L2 S) :
    ⁅x * y, u⁆ = ⁅x, u⁆ * ⁅y, u⁆ := by
  have hXH : str83X L1 L2 S ≤ L1 ⊔ S := str83G4_x_le_sup hfr
  have hcomm : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S :=
    str83G4_commutator_x_q1_le hfr
  have hZx : ⁅x, u⁆ ∈ Z1 L1 L2 S := hcomm (Subgroup.commutator_mem_commutator hx hu)
  have hZy : ⁅y, u⁆ ∈ Z1 L1 L2 S := hcomm (Subgroup.commutator_mem_commutator hy hu)
  have hZab : IsElemAbelian 2 (Z1 L1 L2 S) := B2F.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  calc ⁅x * y, u⁆ = x * ⁅y, u⁆ * x⁻¹ * ⁅x, u⁆ :=
        commutatorElement_mul_left_eq_conj_mul x y u
    _ = (x * ⁅y, u⁆ * x⁻¹) * ⁅x, u⁆ := by group
    _ = ⁅y, u⁆ * ⁅x, u⁆ := by rw [str83G4_conj_eq_of_mem_z1 hfr (hXH hx) hZy]
    _ = ⁅x, u⁆ * ⁅y, u⁆ :=
        ((B6.isElemAbelian_iff.mp hZab).1 _ hZx _ hZy).symm

theorem str83G4_phi_mul_right
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {u v : G}
    (hu : u ∈ Q1 L1 L2 S) (hv : v ∈ Q1 L1 L2 S) {x : G} (hx : x ∈ str83X L1 L2 S) :
    ⁅x, u * v⁆ = ⁅x, u⁆ * ⁅x, v⁆ := by
  have hQH : Q1 L1 L2 S ≤ L1 ⊔ S := (str83G4_q1_le_s hfr).trans le_sup_right
  have hcomm : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S :=
    str83G4_commutator_x_q1_le hfr
  have hZv : ⁅x, v⁆ ∈ Z1 L1 L2 S := hcomm (Subgroup.commutator_mem_commutator hx hv)
  calc ⁅x, u * v⁆ = ⁅x, u⁆ * u * ⁅x, v⁆ * u⁻¹ := commutatorElement_mul_right_eq_mul_conj x u v
    _ = ⁅x, u⁆ * (u * ⁅x, v⁆ * u⁻¹) := by group
    _ = ⁅x, u⁆ * ⁅x, v⁆ := by rw [str83G4_conj_eq_of_mem_z1 hfr (hQH hu) hZv]

theorem str83G4_phi_inv_left
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {u : G}
    (hu : u ∈ Q1 L1 L2 S) {x : G} (hx : x ∈ str83X L1 L2 S) :
    ⁅x⁻¹, u⁆ = (⁅x, u⁆)⁻¹ := by
  have h := str83G4_phi_mul_left hfr hu ((str83X L1 L2 S).inv_mem hx) hx
  rw [inv_mul_cancel, commutatorElement_one_left] at h
  exact eq_inv_iff_mul_eq_one.mpr h.symm

theorem str83G4_phi_inv_right
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {u : G}
    (hu : u ∈ Q1 L1 L2 S) {x : G} (hx : x ∈ str83X L1 L2 S) :
    ⁅x, u⁻¹⁆ = (⁅x, u⁆)⁻¹ := by
  have h := str83G4_phi_mul_right hfr hu ((Q1 L1 L2 S).inv_mem hu) hx
  rw [mul_inv_cancel, commutatorElement_one_right] at h
  exact mul_eq_one_iff_eq_inv'.mp h.symm

theorem str83G4_phi_conj
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {g : G}
    (hg : g ∈ L1 ⊔ S) {u : G} (hu : u ∈ Q1 L1 L2 S) {x : G}
    (hx : x ∈ str83X L1 L2 S) :
    ⁅x, g * u * g⁻¹⁆ = ⁅g⁻¹ * x * g, u⁆ := by
  have hHX : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    str83G4_sup_le_normalizer_x hfr
  have hx' : g⁻¹ * x * g ∈ str83X L1 L2 S := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hHX ((L1 ⊔ S).inv_mem hg)) x).mp hx
  have hZ : ⁅g⁻¹ * x * g, u⁆ ∈ Z1 L1 L2 S :=
    str83G4_commutator_x_q1_le hfr (Subgroup.commutator_mem_commutator hx' hu)
  calc ⁅x, g * u * g⁻¹⁆ = g * ⁅g⁻¹ * x * g, u⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅g⁻¹ * x * g, u⁆ := str83G4_conj_eq_of_mem_z1 hfr hg hZ

private theorem str83G4_phi_commutator
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    {u : G} (hu : u ∈ Q1 L1 L2 S) {t : G}
    (ht : t ∈ CFSG.conjugate (str83X L1 L2 S) d.w) (ht2 : t * t = 1) {x : G}
    (hx : x ∈ str83X L1 L2 S) :
    ⁅x, ⁅u, t⁆⁆ = ⁅⁅x, t⁆, u⁆ := by
  have hHX : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    str83G4_sup_le_normalizer_x hfr
  have hWleS : CFSG.conjugate (str83X L1 L2 S) d.w ≤ S :=
    str83G4_conjugate_x_le_s hfr d hX
  have htH : t ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) (hWleS ht)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
  have htu : t * u * t⁻¹ ∈ Q1 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp
      ((sup_left_le_p1 L1 L2 S).trans
        (le_normalizer_pCoreOf 2 (P1 L1 L2 S)) htH) u).mp hu
  have htui : (t * u * t⁻¹)⁻¹ ∈ Q1 L1 L2 S := (Q1 L1 L2 S).inv_mem htu
  have htx : t * x⁻¹ * t⁻¹ ∈ str83X L1 L2 S := by
    have h : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
    rw [h]
    exact ((str83X L1 L2 S).inv_mem
      ((Subgroup.mem_normalizer_iff.mp (hHX htH) x).mp hx))
  have htx' : t * x * t⁻¹ ∈ str83X L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hHX htH) x).mp hx
  have e1 : ⁅u, t⁆ = u * (t * u * t⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  have e2 : ⁅x, t⁆ = x * (t * x⁻¹ * t⁻¹) := by
    simp only [commutatorElement_def]
    group
  calc ⁅x, ⁅u, t⁆⁆ = ⁅x, u * (t * u * t⁻¹)⁻¹⁆ := by rw [e1]
    _ = ⁅x, u⁆ * ⁅x, (t * u * t⁻¹)⁻¹⁆ := str83G4_phi_mul_right hfr hu htui hx
    _ = ⁅x, u⁆ * (⁅x, t * u * t⁻¹⁆)⁻¹ := by rw [str83G4_phi_inv_right hfr htu hx]
    _ = ⁅x, u⁆ * (⁅t⁻¹ * x * t, u⁆)⁻¹ := by rw [str83G4_phi_conj hfr htH hu hx]
    _ = ⁅x, u⁆ * (⁅t * x * t⁻¹, u⁆)⁻¹ := by
          rw [show t⁻¹ * x * t = t * x * t⁻¹ from by rw [htinv, ← htinv]]
    _ = ⁅x, u⁆ * ⁅(t * x * t⁻¹)⁻¹, u⁆ := by
          rw [← str83G4_phi_inv_left hfr hu htx']
    _ = ⁅x, u⁆ * ⁅t * x⁻¹ * t⁻¹, u⁆ := by
          rw [show (t * x * t⁻¹)⁻¹ = t * x⁻¹ * t⁻¹ from by group]
    _ = ⁅x * (t * x⁻¹ * t⁻¹), u⁆ := (str83G4_phi_mul_left hfr hu hx htx).symm
    _ = ⁅⁅x, t⁆, u⁆ := by rw [e2]

theorem str83G4_commutator_q1_q1_le_y
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    ⁅Q1 L1 L2 S, Q1 L1 L2 S⁆ ≤ str83Y L1 L2 S := by
  have hQH : Q1 L1 L2 S ≤ L1 ⊔ S := (str83G4_q1_le_s hfr).trans le_sup_right
  have hHZ : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    str83G4_sup_le_centralizer_z1 hfr
  have hZQ : ⁅Z1 L1 L2 S, Q1 L1 L2 S⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp (hQH.trans hHZ)
  have h1 : ⁅⁅str83X L1 L2 S, Q1 L1 L2 S⁆, Q1 L1 L2 S⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono (str83G4_commutator_x_q1_le hfr) le_rfl).trans
      (le_of_eq hZQ))
  have h2 : ⁅⁅Q1 L1 L2 S, str83X L1 L2 S⁆, Q1 L1 L2 S⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (H₁ := Q1 L1 L2 S) (H₂ := str83X L1 L2 S)]
    exact h1
  have h3 : ⁅⁅Q1 L1 L2 S, Q1 L1 L2 S⁆, str83X L1 L2 S⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := Q1 L1 L2 S) (H₂ := Q1 L1 L2 S)
      (H₃ := str83X L1 L2 S) h2 h1
  have h4 : ⁅Q1 L1 L2 S, Q1 L1 L2 S⁆ ≤
      Subgroup.centralizer (str83X L1 L2 S : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hQcomm : ⁅Q1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Q1 L1 L2 S := by
    simpa using Subgroup.commutator_le_sup (H₁ := Q1 L1 L2 S) (H₂ := Q1 L1 L2 S)
  exact le_inf hQcomm h4

theorem str83G4_commutator_commutator_q1_conjugate_x_le_y
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    ⁅⁅Q1 L1 L2 S, CFSG.conjugate (str83X L1 L2 S) d.w⁆,
      CFSG.conjugate (str83X L1 L2 S) d.w⁆ ≤ str83Y L1 L2 S := by
  classical
  set Q : Subgroup G := Q1 L1 L2 S with hQdef
  set X : Subgroup G := str83X L1 L2 S with hXdef
  set W : Subgroup G := CFSG.conjugate (str83X L1 L2 S) d.w with hWdef
  set Y : Subgroup G := str83Y L1 L2 S with hYdef
  have hQH : Q ≤ L1 ⊔ S := (str83G4_q1_le_s hfr).trans le_sup_right
  have hQN : L1 ⊔ S ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]
    exact (sup_left_le_p1 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hYn : IsNormalIn (L1 ⊔ S) Q Y := by
    rw [hQdef, hYdef]
    exact str83G4_isNormalIn_y hfr
  have hWleS : W ≤ S := by
    rw [hWdef]
    exact str83G4_conjugate_x_le_s hfr d hX
  have hWH : W ≤ L1 ⊔ S := hWleS.trans le_sup_right
  have hWabel : IsElemAbelian 2 W := by
    rw [hWdef]
    exact str83G4_isElemAbelian_conjugate_x d hX
  have hW2 : ∀ t ∈ W, t * t = 1 := by
    intro t ht
    have h := (B6.isElemAbelian_iff.mp hWabel).2 t ht
    simpa [pow_two] using h
  have hCP5 : ⁅⁅X, W⁆, W⁆ = ⊥ := by
    rw [hXdef, hWdef]
    exact str83G4_commutator_commutator_x_conjugate_eq_bot hfr d hX
  have hXW : ⁅X, W⁆ ≤ X := by
    have h := str83G4_commutator_x_conjugate_le hfr d hX
    rw [hXdef, hWdef]
    exact fun z hz => (h hz).1
  let K : Subgroup G :=
    { carrier := {c | c ∈ Q ∧ ∀ t' ∈ W, ⁅c, t'⁆ ∈ Y}
      one_mem' := by
        refine ⟨Q.one_mem, fun t' _ => ?_⟩
        simp
      mul_mem' := by
        rintro c₁ c₂ ⟨hc₁Q, hc₁⟩ ⟨hc₂Q, hc₂⟩
        refine ⟨Q.mul_mem hc₁Q hc₂Q, fun t' ht' => ?_⟩
        have h1 : c₁ * ⁅c₂, t'⁆ * c₁⁻¹ ∈ Y :=
          hYn.2 c₁ (hQH hc₁Q) _ (hc₂ t' ht')
        have h2 : ⁅c₁, t'⁆ ∈ Y := hc₁ t' ht'
        have e : ⁅c₁ * c₂, t'⁆ = c₁ * ⁅c₂, t'⁆ * c₁⁻¹ * ⁅c₁, t'⁆ :=
          commutatorElement_mul_left_eq_conj_mul c₁ c₂ t'
        rw [e]
        exact Y.mul_mem h1 h2
      inv_mem' := by
        rintro c ⟨hcQ, hc⟩
        refine ⟨Q.inv_mem hcQ, fun t' ht' => ?_⟩
        have hz : ⁅c, t'⁆ ∈ Y := hc t' ht'
        have h1 : c⁻¹ * ⁅c, t'⁆⁻¹ * c ∈ Y := by
          simpa using hYn.2 c⁻¹ ((L1 ⊔ S).inv_mem (hQH hcQ)) _ (Y.inv_mem hz)
        have e : ⁅c⁻¹, t'⁆ = c⁻¹ * ⁅c, t'⁆⁻¹ * c := by
          rw [commutatorElement_inv_left, commutatorElement_inv]
        rw [e]
        exact h1 }
  have hKmem : ∀ c : G, c ∈ K ↔ c ∈ Q ∧ ∀ t' ∈ W, ⁅c, t'⁆ ∈ Y := fun c => Iff.rfl
  have hmemK : ∀ u ∈ Q, ∀ t ∈ W, ⁅u, t⁆ ∈ K := by
    intro u hu t ht
    have huQ : ⁅u, t⁆ ∈ Q := str83G4_commutator_mem_q1 hfr hu (hWH ht)
    refine (hKmem ⁅u, t⁆).mpr ⟨huQ, fun t' ht' => ?_⟩
    refine ⟨str83G4_commutator_mem_q1 hfr huQ (hWH ht'), ?_⟩
    change ⁅⁅u, t⁆, t'⁆ ∈ Subgroup.centralizer (str83X L1 L2 S : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxt' : ⁅x, t'⁆ ∈ X :=
      hXW (Subgroup.commutator_mem_commutator hx ht')
    have hid1 : ⁅x, ⁅⁅u, t⁆, t'⁆⁆ = ⁅⁅x, t'⁆, ⁅u, t⁆⁆ :=
      str83G4_phi_commutator hfr d hX huQ ht' (hW2 t' ht') hx
    have hid2 : ⁅⁅x, t'⁆, ⁅u, t⁆⁆ = ⁅⁅⁅x, t'⁆, t⁆, u⁆ :=
      str83G4_phi_commutator hfr d hX hu ht (hW2 t ht) hxt'
    have hzero : ⁅⁅x, t'⁆, t⁆ = 1 := by
      have hmem : ⁅⁅x, t'⁆, t⁆ ∈ ⁅⁅X, W⁆, W⁆ :=
        Subgroup.commutator_mem_commutator
          (Subgroup.commutator_mem_commutator (hXdef ▸ hx) (hWdef ▸ ht')) (hWdef ▸ ht)
      rw [hCP5, Subgroup.mem_bot] at hmem
      exact hmem
    have hone : ⁅x, ⁅⁅u, t⁆, t'⁆⁆ = 1 := by
      rw [hid1, hid2, hzero, commutatorElement_one_left]
    exact (commutatorElement_eq_one_iff_mul_comm).mp hone
  have hQWK : ⁅Q, W⁆ ≤ K := Subgroup.commutator_le.mpr hmemK
  refine Subgroup.commutator_le.mpr fun c hc t' ht' => ?_
  exact ((hKmem c).mp (hQWK hc)).2 t' ht'

theorem str83N_eq_x_of_isChiefStep
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hXnc : ¬ twoResidual (L1 ⊔ S) ≤
      centralizerMod (Z1 L1 L2 S) (L1 ⊔ S) (str83X L1 L2 S)) :
    str83N L1 L2 S = str83X L1 L2 S := by
  classical
  have hNn : IsNormalIn (L1 ⊔ S) (str83X L1 L2 S) (str83N L1 L2 S) :=
    str83N_normal hfr
  have hNX : str83N L1 L2 S ≤ str83X L1 L2 S := str83N_le_x hfr
  have hZN : Z1 L1 L2 S ≤ str83N L1 L2 S := str83Z1_le_n L1 L2 S
  rcases hXstep.2.2.2 (str83N L1 L2 S) hNn hZN hNX with h | h
  · exfalso
    apply hXnc
    intro g hg
    have hgH : g ∈ L1 ⊔ S := twoResidual_le (L1 ⊔ S) hg
    refine ⟨hgH, str83G4_sup_le_normalizer_z1 hfr hgH, fun u hu => ?_⟩
    have hgo : g ∈ oTwoUpper (L1 ⊔ S) := by
      rwa [← F6.twoResidual_eq_oTwoUpper]
    have hmem : ⁅u, g⁆ ∈ str83N L1 L2 S :=
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu hgo)
    have hmemZ : ⁅u, g⁆ ∈ Z1 L1 L2 S := h ▸ hmem
    have e : g * u * g⁻¹ * u⁻¹ = ⁅u, g⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Z1 L1 L2 S).inv_mem hmemZ
  · exact h

@[expose] def str83G4SecPart
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {M : Subgroup G} (hM : M ≤ Q1 L1 L2 S) (Z' : Subgroup G) : Subgroup G where
  carrier := {u | u ∈ M ∧ ∀ x ∈ str83X L1 L2 S, ⁅x, u⁆ ∈ Z'}
  one_mem' := ⟨M.one_mem, fun x _ => by simp⟩
  mul_mem' := by
    intro u v hu hv
    exact ⟨M.mul_mem hu.1 hv.1, fun x hx => by
      rw [str83G4_phi_mul_right hfr (hM hu.1) (hM hv.1) hx]
      exact Z'.mul_mem (hu.2 x hx) (hv.2 x hx)⟩
  inv_mem' := by
    intro u hu
    exact ⟨M.inv_mem hu.1, fun x hx => by
      rw [str83G4_phi_inv_right hfr (hM hu.1) hx]
      exact Z'.inv_mem (hu.2 x hx)⟩

theorem mem_str83G4SecPart
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {M : Subgroup G} (hM : M ≤ Q1 L1 L2 S) (Z' : Subgroup G) {u : G} :
    u ∈ str83G4SecPart hfr hM Z' ↔ u ∈ M ∧ ∀ x ∈ str83X L1 L2 S, ⁅x, u⁆ ∈ Z' :=
  Iff.rfl

theorem str83G4SecPart_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {M : Subgroup G} (hM : M ≤ Q1 L1 L2 S) (Z' : Subgroup G) :
    str83G4SecPart hfr hM Z' ≤ M := fun _ hu => hu.1

theorem str83G4SecPart_mono
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {M : Subgroup G} (hM : M ≤ Q1 L1 L2 S) {Z'' Z' : Subgroup G} (h : Z'' ≤ Z') :
    str83G4SecPart hfr hM Z'' ≤ str83G4SecPart hfr hM Z' :=
  fun _ hu => ⟨hu.1, fun x hx => h (hu.2 x hx)⟩

theorem str83G4SecPart_bot
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {M : Subgroup G} (hM : M ≤ Q1 L1 L2 S) (hYM : str83Y L1 L2 S ≤ M) :
    str83G4SecPart hfr hM ⊥ = str83Y L1 L2 S := by
  refine le_antisymm (fun u hu => ?_) (fun y hy => ?_)
  · have huQ : u ∈ Q1 L1 L2 S := hM hu.1
    refine ⟨huQ, ?_⟩
    change u ∈ Subgroup.centralizer (str83X L1 L2 S : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : ⁅x, u⁆ = 1 := by simpa using hu.2 x hx
    exact (commutatorElement_eq_one_iff_mul_comm).mp h1
  · refine ⟨hYM hy, fun x hx => ?_⟩
    have h1 : ⁅x, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hy.2 x hx)
    rw [h1]
    exact Subgroup.mem_bot.mpr rfl

theorem str83G4SecPart_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {M : Subgroup G} (hM : M ≤ Q1 L1 L2 S) :
    str83G4SecPart hfr hM (Z1 L1 L2 S) = M := by
  refine le_antisymm (str83G4SecPart_le hfr hM _) (fun u hu => ?_)
  exact ⟨hu, fun x hx =>
    str83G4_commutator_x_q1_le hfr (Subgroup.commutator_mem_commutator hx (hM hu))⟩

theorem str83G4SecPart_normal
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {M : Subgroup G} (hM : IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) M) (Z' : Subgroup G) :
    IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) (str83G4SecPart hfr hM.1 Z') := by
  refine ⟨fun u hu => hM.1 (str83G4SecPart_le hfr hM.1 Z' hu),
    fun g hg u hu => ?_⟩
  refine ⟨hM.2 g hg u hu.1, fun x hx => ?_⟩
  have hx' : g⁻¹ * x * g ∈ str83X L1 L2 S := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      (str83G4_sup_le_normalizer_x hfr ((L1 ⊔ S).inv_mem hg)) x).mp hx
  rw [show ⁅x, g * u * g⁻¹⁆ = ⁅g⁻¹ * x * g, u⁆ from
    str83G4_phi_conj hfr hg (hM.1 hu.1) hx]
  exact hu.2 _ hx'

theorem str83G4_phi_conj_left
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {g : G}
    (hg : g ∈ L1 ⊔ S) {u : G} (hu : u ∈ Q1 L1 L2 S) {x : G}
    (hx : x ∈ str83X L1 L2 S) :
    ⁅g * x * g⁻¹, u⁆ = ⁅x, g⁻¹ * u * g⁆ := by
  have hgu : g⁻¹ * u * g ∈ Q1 L1 L2 S := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      ((sup_left_le_p1 L1 L2 S).trans
        (le_normalizer_pCoreOf 2 (P1 L1 L2 S)) ((L1 ⊔ S).inv_mem hg)) u).mp hu
  have hZ : ⁅x, g⁻¹ * u * g⁆ ∈ Z1 L1 L2 S :=
    str83G4_commutator_x_q1_le hfr (Subgroup.commutator_mem_commutator hx hgu)
  calc ⁅g * x * g⁻¹, u⁆ = g * ⁅x, g⁻¹ * u * g⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, g⁻¹ * u * g⁆ := str83G4_conj_eq_of_mem_z1 hfr hg hZ

@[expose] def str83G4XPart
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {A : Subgroup G} (hA : A ≤ Q1 L1 L2 S) (Z'' : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ str83X L1 L2 S ∧ ∀ u ∈ A, ⁅x, u⁆ ∈ Z''}
  one_mem' := ⟨(str83X L1 L2 S).one_mem, fun u _ => by simp⟩
  mul_mem' := by
    intro x y hx hy
    exact ⟨(str83X L1 L2 S).mul_mem hx.1 hy.1, fun u hu => by
      rw [str83G4_phi_mul_left hfr (hA hu) hx.1 hy.1]
      exact Z''.mul_mem (hx.2 u hu) (hy.2 u hu)⟩
  inv_mem' := by
    intro x hx
    exact ⟨(str83X L1 L2 S).inv_mem hx.1, fun u hu => by
      rw [str83G4_phi_inv_left hfr (hA hu) hx.1]
      exact Z''.inv_mem (hx.2 u hu)⟩

theorem mem_str83G4XPart
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {A : Subgroup G} (hA : A ≤ Q1 L1 L2 S) (Z'' : Subgroup G) {x : G} :
    x ∈ str83G4XPart hfr hA Z'' ↔
      x ∈ str83X L1 L2 S ∧ ∀ u ∈ A, ⁅x, u⁆ ∈ Z'' :=
  Iff.rfl

theorem str83G4XPart_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {A : Subgroup G} (hA : A ≤ Q1 L1 L2 S) (Z'' : Subgroup G) :
    str83G4XPart hfr hA Z'' ≤ str83X L1 L2 S := fun _ hx => hx.1

theorem str83G4XPart_normal
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {A : Subgroup G} (hA : A ≤ Q1 L1 L2 S)
    (hAn : L1 ⊔ S ≤ Subgroup.normalizer (A : Set G)) (Z'' : Subgroup G) :
    IsNormalIn (L1 ⊔ S) (str83X L1 L2 S) (str83G4XPart hfr hA Z'') := by
  refine ⟨str83G4XPart_le hfr hA Z'', fun g hg x hx => ?_⟩
  have hxX : x ∈ str83X L1 L2 S := hx.1
  have hgx : g * x * g⁻¹ ∈ str83X L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (str83G4_sup_le_normalizer_x hfr hg) x).mp hxX
  refine ⟨hgx, fun u hu => ?_⟩
  rw [str83G4_phi_conj_left hfr hg (hA hu) hxX]
  exact hx.2 _ (by
    simpa using (Subgroup.mem_normalizer_iff.mp (hAn ((L1 ⊔ S).inv_mem hg)) u).mp hu)

@[expose] def str83G4XFibre
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {u : G} (hu : u ∈ Q1 L1 L2 S) (Z'' : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ str83X L1 L2 S ∧ ⁅x, u⁆ ∈ Z''}
  one_mem' := ⟨(str83X L1 L2 S).one_mem, by simp⟩
  mul_mem' := by
    intro x y hx hy
    exact ⟨(str83X L1 L2 S).mul_mem hx.1 hy.1, by
      rw [str83G4_phi_mul_left hfr hu hx.1 hy.1]
      exact Z''.mul_mem hx.2 hy.2⟩
  inv_mem' := by
    intro x hx
    exact ⟨(str83X L1 L2 S).inv_mem hx.1, by
      rw [str83G4_phi_inv_left hfr hu hx.1]
      exact Z''.inv_mem hx.2⟩

theorem mem_str83G4XFibre
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {u : G} (hu : u ∈ Q1 L1 L2 S) (Z'' : Subgroup G) {x : G} :
    x ∈ str83G4XFibre hfr hu Z'' ↔ x ∈ str83X L1 L2 S ∧ ⁅x, u⁆ ∈ Z'' :=
  Iff.rfl

