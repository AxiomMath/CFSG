module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapPieces
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapQuasi

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (swapDiagHom swapDiagHom_apply)

section Structure

variable {G : Type*} [Group G]

structure SwapCover (t : G) (T D E : Subgroup G) where
  Kc : Subgroup G
  perfect : ⁅Kc, Kc⁆ = Kc
  le_centralizer : Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G)
  sup_eq : Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = E
  normalizer_le : ∀ s ∈ centralizer (T : Set G), Odd (orderOf s) → s ∈ normalizer (Kc : Set G)
  diag_mem : ∀ k ∈ Kc, k * (t * k * t⁻¹) ∈ D
  diag_surj : ∀ d ∈ D, ∃ k ∈ Kc, k * (t * k * t⁻¹) = d

variable {t : G} {T D E : Subgroup G}

theorem SwapCover.diag_mul (h : SwapCover t T D E) {a b : G} (ha : a ∈ h.Kc) (hb : b ∈ h.Kc) :
    (a * b) * (t * (a * b) * t⁻¹) = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by
  have hc : b * (t * a * t⁻¹) = t * a * t⁻¹ * b :=
    mem_centralizer_iff.1 (h.le_centralizer ⟨a, ha, rfl⟩) b hb
  calc (a * b) * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
    _ = a * (t * a * t⁻¹ * b) * (t * b * t⁻¹) := by rw [hc]
    _ = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by group

theorem SwapCover.diag_inv (h : SwapCover t T D E) {a : G} (ha : a ∈ h.Kc) :
    a⁻¹ * (t * a⁻¹ * t⁻¹) = (a * (t * a * t⁻¹))⁻¹ := by
  have hc : a * (t * a * t⁻¹) = t * a * t⁻¹ * a :=
    mem_centralizer_iff.1 (h.le_centralizer ⟨a, ha, rfl⟩) a ha
  rw [hc]
  group

theorem SwapCover.mem_map_conj_of_diag_eq_one (h : SwapCover t T D E) {k : G} (hk : k ∈ h.Kc)
    (h1 : k * (t * k * t⁻¹) = 1) : k ∈ h.Kc.map (MulAut.conj t).toMonoidHom := by
  refine ⟨k⁻¹, inv_mem hk, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc t * k⁻¹ * t⁻¹ = (t * k * t⁻¹)⁻¹ := by group
    _ = k := (eq_inv_of_mul_eq_one_left h1).symm

theorem SwapCover.inf_le_centralizer (h : SwapCover t T D E) {P : Subgroup G} (hP : P ≤ h.Kc) :
    h.Kc ⊓ h.Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (P : Set G) := fun _ hz =>
  centralizer_le (SetLike.coe_subset_coe.2 hP) (h.le_centralizer hz.2)

theorem SwapCover.inf_le_centralizer_self (h : SwapCover t T D E) :
    h.Kc ⊓ h.Kc.map (MulAut.conj t).toMonoidHom ≤
      centralizer ((h.Kc ⊓ h.Kc.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
  fun _ hz => mem_centralizer_iff.2 fun w hw => mem_centralizer_iff.1 (h.le_centralizer hz.2) w hw.1

theorem SwapCover.le_sup (h : SwapCover t T D E) : D ≤ E := by
  intro d hd
  obtain ⟨k, hk, rfl⟩ := h.diag_surj d hd
  rw [← h.sup_eq]
  exact mul_mem (mem_sup_left hk) (mem_sup_right ⟨k, hk, rfl⟩)

end Structure

section Piece

variable {G : Type*} [Group G] {t : G} {T D E : Subgroup G}

@[expose] noncomputable def SwapCover.piece (h : SwapCover t T D E) (X : Subgroup G) :
    Subgroup G :=
  perfectCore (h.Kc ⊓ centralizer (X : Set G))

theorem SwapCover.piece_le (h : SwapCover t T D E) (X : Subgroup G) : h.piece X ≤ h.Kc :=
  (CFSG.Quasithin.perfectCore_le _).trans inf_le_left

theorem SwapCover.piece_le_centralizer (h : SwapCover t T D E) (X : Subgroup G) :
    h.piece X ≤ centralizer (X : Set G) :=
  (CFSG.Quasithin.perfectCore_le _).trans inf_le_right

theorem SwapCover.commutator_piece [Finite G] (h : SwapCover t T D E) (X : Subgroup G) :
    ⁅h.piece X, h.piece X⁆ = h.piece X :=
  CFSG.Quasithin.perfectCore_perfect _

theorem SwapCover.map_le_centralizer_piece (h : SwapCover t T D E) (X : Subgroup G) :
    h.Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (h.piece X : Set G) :=
  h.le_centralizer.trans (centralizer_le (SetLike.coe_subset_coe.2 (h.piece_le X)))

theorem SwapCover.map_piece_le_centralizer_piece (h : SwapCover t T D E) (X Y : Subgroup G) :
    (h.piece Y).map (MulAut.conj t).toMonoidHom ≤ centralizer (h.piece X : Set G) :=
  (map_mono (h.piece_le Y)).trans (h.map_le_centralizer_piece X)

theorem swapConj_mem_centralizer_of_le {X : Subgroup G} (hXt : X ≤ centralizer ({t} : Set G))
    {x : G}
    (hx : x ∈ centralizer (X : Set G)) : t * x * t⁻¹ ∈ centralizer (X : Set G) := by
  rw [mem_centralizer_iff] at hx ⊢
  intro τ hτ
  have h1 : τ * t = t * τ := mem_centralizer_singleton_iff.1 (hXt hτ)
  have h2 : τ * t⁻¹ = t⁻¹ * τ := by
    calc τ * t⁻¹ = t⁻¹ * (t * τ) * t⁻¹ := by group
      _ = t⁻¹ * (τ * t) * t⁻¹ := by rw [h1]
      _ = t⁻¹ * τ := by group
  calc τ * (t * x * t⁻¹) = (τ * t) * x * t⁻¹ := by group
    _ = t * (τ * x) * t⁻¹ := by rw [h1]; group
    _ = t * (x * τ) * t⁻¹ := by rw [hx τ hτ]
    _ = t * x * (τ * t⁻¹) := by group
    _ = t * x * t⁻¹ * τ := by rw [h2]; group

theorem SwapCover.diag_mem_centralizer (h : SwapCover t T D E) {X : Subgroup G}
    (hXt : X ≤ centralizer ({t} : Set G)) {k : G} (hk : k ∈ h.piece X) :
    k * (t * k * t⁻¹) ∈ centralizer (X : Set G) :=
  mul_mem (h.piece_le_centralizer X hk)
    (swapConj_mem_centralizer_of_le hXt (h.piece_le_centralizer X hk))

theorem SwapCover.diag_mem_inf (h : SwapCover t T D E) {X : Subgroup G}
    (hXt : X ≤ centralizer ({t} : Set G)) {k : G} (hk : k ∈ h.piece X) :
    k * (t * k * t⁻¹) ∈ D ⊓ centralizer (X : Set G) :=
  ⟨h.diag_mem k (h.piece_le X hk), h.diag_mem_centralizer hXt hk⟩

theorem SwapCover.le_normalizer (h : SwapCover t T D E) {X : Subgroup G}
    (hXT : X ≤ centralizer (T : Set G)) (hXo : ∀ x ∈ X, Odd (orderOf x)) :
    X ≤ normalizer (h.Kc : Set G) := fun x hx => h.normalizer_le x (hXT hx) (hXo x hx)

theorem SwapCover.pieceCore_eq_sup [Finite G] (h : SwapCover t T D E) (htt : t * t = 1)
    {X : Subgroup G} (hXN : X ≤ normalizer (h.Kc : Set G)) (hXt : X ≤ centralizer ({t} : Set G)) :
    perfectCore (E ⊓ centralizer (X : Set G)) = h.piece X ⊔ (h.piece X).map
      (MulAut.conj t).toMonoidHom := by
  have h1 := E6Pilot.swapPerfectCore_centralizer_eq h.le_centralizer htt hXN hXt
  rwa [h.sup_eq] at h1

theorem SwapCover.exists_mem_piece_diag_eq [Finite G] (h : SwapCover t T D E) {X : Subgroup G}
    (hXN : X ≤ normalizer (h.Kc : Set G)) (hXt : X ≤ centralizer ({t} : Set G))
    {P : Subgroup G} (hPD : P ≤ D) (hPX : P ≤ centralizer (X : Set G)) (hPp : ⁅P, P⁆ = P) :
    ∀ y ∈ P, ∃ k ∈ h.piece X, k * (t * k * t⁻¹) = y := by
  set δ := swapDiagHom h.le_centralizer with hδ
  have hrange : P ≤ δ.range := fun y hy => by
    obtain ⟨k, hk, rfl⟩ := h.diag_surj y (hPD hy)
    exact ⟨⟨k, hk⟩, rfl⟩
  set Q : Subgroup h.Kc := P.comap δ with hQ
  have hQP : (perfectCore Q).map δ = P := by
    rw [CFSG.Quasithin.map_perfectCore, hQ, map_comap_eq_self hrange,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect hPp]
  have hQp : ⁅(perfectCore Q).map h.Kc.subtype, (perfectCore Q).map h.Kc.subtype⁆ =
      (perfectCore Q).map h.Kc.subtype := by
    rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
  have hle : (perfectCore Q).map h.Kc.subtype ≤ h.piece X := by
    refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf (map_subtype_le _) ?_) hQp
    rw [← le_centralizer_iff]
    intro τ hτ
    refine E6Pilot.swapMem_centralizer_of_perfect hQp (h.inf_le_centralizer (map_subtype_le _))
      h.inf_le_centralizer_self fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := hx
    have hτN := hXN hτ
    have hτt : τ * t = t * τ := mem_centralizer_singleton_iff.1 (hXt hτ)
    have hτt' : t⁻¹ * τ⁻¹ = τ⁻¹ * t⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hτt]
    have hk' : τ * (k : G) * τ⁻¹ ∈ h.Kc := (mem_normalizer_iff.1 hτN k).1 k.2
    have hkP : δ k ∈ P := CFSG.Quasithin.perfectCore_le Q hk
    have hδk : (k : G) * (t * k * t⁻¹) ∈ P := hkP
    have hc : τ * ((k : G) * (t * k * t⁻¹)) * τ⁻¹ = (k : G) * (t * k * t⁻¹) := by
      rw [mem_centralizer_iff.1 (hPX hδk) τ hτ, mul_inv_cancel_right]
    have hδ' : (τ * (k : G) * τ⁻¹) * (t * (τ * k * τ⁻¹) * t⁻¹) =
        τ * ((k : G) * (t * k * t⁻¹)) * τ⁻¹ := by
      calc (τ * (k : G) * τ⁻¹) * (t * (τ * k * τ⁻¹) * t⁻¹) =
          τ * (k : G) * τ⁻¹ * ((t * τ) * k * (τ⁻¹ * t⁻¹)) := by group
        _ = τ * (k : G) * τ⁻¹ * ((τ * t) * k * (t⁻¹ * τ⁻¹)) := by rw [hτt, hτt']
        _ = τ * ((k : G) * (t * k * t⁻¹)) * τ⁻¹ := by group
    have hmem : (k : G)⁻¹ * (τ * k * τ⁻¹) ∈ h.Kc := mul_mem (inv_mem k.2) hk'
    have h1 : ((k : G)⁻¹ * (τ * k * τ⁻¹)) * (t * ((k : G)⁻¹ * (τ * k * τ⁻¹)) * t⁻¹) = 1 := by
      rw [h.diag_mul (inv_mem k.2) hk', h.diag_inv k.2, hδ', hc, inv_mul_cancel]
    exact ⟨hmem, h.mem_map_conj_of_diag_eq_one hmem h1⟩
  intro y hy
  rw [← hQP] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  exact ⟨k, hle ⟨k, hk, rfl⟩, rfl⟩

theorem SwapCover.piece_le_centralizer_piece [Finite G] (h : SwapCover t T D E) {X Y : Subgroup G}
    (hc : ∀ x ∈ h.piece X, ∀ c ∈ h.piece Y,
      (x * (t * x * t⁻¹)) * (c * (t * c * t⁻¹)) = (c * (t * c * t⁻¹)) * (x * (t * x * t⁻¹))) :
    h.piece Y ≤ centralizer (h.piece X : Set G) := by
  intro c hc'
  refine E6Pilot.swapMem_centralizer_of_perfect (h.commutator_piece X)
    (h.inf_le_centralizer (h.piece_le X)) h.inf_le_centralizer_self fun x hx => ?_
  have hxK := h.piece_le X hx
  have hcK := h.piece_le Y hc'
  have hm1 : c * x * c⁻¹ ∈ h.Kc := mul_mem (mul_mem hcK hxK) (inv_mem hcK)
  have hmem : x⁻¹ * (c * x * c⁻¹) ∈ h.Kc := mul_mem (inv_mem hxK) hm1
  have h1 : (x⁻¹ * (c * x * c⁻¹)) * (t * (x⁻¹ * (c * x * c⁻¹)) * t⁻¹) = 1 := by
    rw [h.diag_mul (inv_mem hxK) hm1, h.diag_inv hxK, h.diag_mul (mul_mem hcK hxK) (inv_mem hcK),
      h.diag_mul hcK hxK, h.diag_inv hcK, ← hc x hx c hc']
    group
  exact ⟨hmem, h.mem_map_conj_of_diag_eq_one hmem h1⟩

theorem SwapCover.piece_le_centralizer_piece_of_le [Finite G] (h : SwapCover t T D E)
    {X Y P Q : Subgroup G} (hP : ∀ x ∈ h.piece X, x * (t * x * t⁻¹) ∈ P)
    (hQ : ∀ c ∈ h.piece Y, c * (t * c * t⁻¹) ∈ Q) (hPQ : Q ≤ centralizer (P : Set G)) :
    h.piece Y ≤ centralizer (h.piece X : Set G) :=
  h.piece_le_centralizer_piece fun x hx c hc => mem_centralizer_iff.1 (hPQ (hQ c hc)) _ (hP x hx)

theorem SwapCover.piece_dichotomy [Finite G] (h : SwapCover t T D E) {X S : Subgroup G}
    (hS : IsSimpleGroup S) (hδS : ∀ k ∈ h.piece X, k * (t * k * t⁻¹) ∈ S)
    (hSδ : ∀ s ∈ S, ∃ k ∈ h.piece X, k * (t * k * t⁻¹) = s) :
    ∀ M : Subgroup G, M ≤ h.piece X → h.piece X ≤ normalizer (M : Set G) →
      M ≤ centralizer (h.piece X : Set G) ∨ h.piece X ≤ M := by
  let φ : h.piece X →* S :=
    { toFun := fun k => ⟨(k : G) * (t * k * t⁻¹), hδS k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        exact h.diag_mul (h.piece_le X a.2) (h.piece_le X b.2)) }
  have hφ : Function.Surjective φ := by
    rintro ⟨s, hs⟩
    obtain ⟨k, hk, hks⟩ := hSδ s hs
    exact ⟨⟨k, hk⟩, Subtype.ext hks⟩
  have hker : ∀ x : h.piece X, φ x = 1 → (x : G) ∈ centralizer (h.piece X : Set G) := by
    intro x hx
    have h1 : (x : G) * (t * x * t⁻¹) = 1 := congrArg Subtype.val hx
    exact h.map_le_centralizer_piece X (h.mem_map_conj_of_diag_eq_one (h.piece_le X x.2) h1)
  intro M hMF hFM
  exact E6Pilot.swapNormal_le_centralizer_or_le φ hφ hker (h.commutator_piece X) hMF hFM

theorem dichotomy_map_conj' {F : Subgroup G} (t : G)
    (hF : ∀ M : Subgroup G, M ≤ F → F ≤ normalizer (M : Set G) →
      M ≤ centralizer (F : Set G) ∨ F ≤ M) :
    ∀ M : Subgroup G, M ≤ F.map (MulAut.conj t).toMonoidHom →
      F.map (MulAut.conj t).toMonoidHom ≤ normalizer (M : Set G) →
      M ≤ centralizer (F.map (MulAut.conj t).toMonoidHom : Set G) ∨
        F.map (MulAut.conj t).toMonoidHom ≤ M := by
  have hF' : ∀ M : Subgroup G, M ≤ F → F ≤ normalizer (M : Set G) →
      M ≤ centralizer (F : Set G) ∨ M = F :=
    fun M hMF hFM => (hF M hMF hFM).imp id fun h => le_antisymm hMF h
  intro M hMF hFM
  exact (F4Pilot.dichotomy_map_mulAut (MulAut.conj t) hF' M hMF hFM).imp id fun h => h.ge

theorem SwapCover.piece_eq_or_eq_conj [Finite G] (h : SwapCover t T D E) {T' D' E' : Subgroup G}
    (h' : SwapCover t T' D' E') {X : Subgroup G}
    (hsup : h'.piece X ⊔ (h'.piece X).map (MulAut.conj t).toMonoidHom =
      h.piece X ⊔ (h.piece X).map (MulAut.conj t).toMonoidHom)
    (hqs : ∀ M : Subgroup G, M ≤ h.piece X → h.piece X ≤ normalizer (M : Set G) →
      M ≤ centralizer (h.piece X : Set G) ∨ h.piece X ≤ M) (hne : h'.piece X ≠ ⊥) :
    h'.piece X = h.piece X ∨ h'.piece X = (h.piece X).map (MulAut.conj t).toMonoidHom :=
  E6Pilot.swapEq_or_eq_conj ((map_mono (h.piece_le X)).trans (h.map_le_centralizer_piece X))
    ((map_mono (h'.piece_le X)).trans (h'.map_le_centralizer_piece X)) hsup
    (h.commutator_piece X) (by rw [← map_commutator, h.commutator_piece])
    (h'.commutator_piece X) hne hqs (dichotomy_map_conj' t hqs)

theorem SwapCover.sup_le_centralizer_sup (h : SwapCover t T D E) {X Y : Subgroup G}
    (h1 : h.piece Y ≤ centralizer (h.piece X : Set G)) :
    h.piece Y ⊔ (h.piece Y).map (MulAut.conj t).toMonoidHom ≤
      centralizer ((h.piece X ⊔ (h.piece X).map (MulAut.conj t).toMonoidHom : Subgroup G) :
        Set G) := by
  have h2 : (h.piece Y).map (MulAut.conj t).toMonoidHom ≤ centralizer (h.piece X : Set G) :=
    h.map_piece_le_centralizer_piece X Y
  have h3 : h.piece Y ≤ centralizer ((h.piece X).map (MulAut.conj t).toMonoidHom : Set G) :=
    le_centralizer_iff.1 (h.map_piece_le_centralizer_piece Y X)
  have h4 : (h.piece Y).map (MulAut.conj t).toMonoidHom ≤
      centralizer ((h.piece X).map (MulAut.conj t).toMonoidHom : Set G) :=
    F4Pilot.map_le_centralizer_map _ h1
  refine sup_le ?_ ?_ <;>
    refine (le_inf ?_ ?_).trans F4Pilot.centralizer_inf_centralizer_le_centralizer_sup
  exacts [h1, h3, h2, h4]

end Piece

section Transport

variable {G : Type*} [Group G] {t : G} {T D E : Subgroup G}

theorem map_conj_map_conj_of_mul_self (htt : t * t = 1) (H : Subgroup G) :
    (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = H := by
  rw [F4Pilot.map_conj_map_conj_toMonoidHom, htt]
  exact F4Pilot.map_conj_one_toMonoidHom H

@[expose] def SwapCover.flip (h : SwapCover t T D E) (htT : t ∈ centralizer (T : Set G))
    (htt : t * t = 1) : SwapCover t T D E where
  Kc := h.Kc.map (MulAut.conj t).toMonoidHom
  perfect := by rw [← map_commutator, h.perfect]
  le_centralizer := by
    rw [map_conj_map_conj_of_mul_self htt]
    exact le_centralizer_iff.1 h.le_centralizer
  sup_eq := by rw [map_conj_map_conj_of_mul_self htt, sup_comm, h.sup_eq]
  normalizer_le := by
    intro s hs hso
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have hs' : t⁻¹ * s * t ∈ centralizer (T : Set G) := by
      have h1 : t⁻¹ ∈ centralizer (T : Set G) := inv_mem htT
      exact mul_mem (mul_mem h1 hs) htT
    have hso' : Odd (orderOf (t⁻¹ * s * t)) := by
      have h1 := MulEquiv.orderOf_eq (MulAut.conj t⁻¹) s
      rw [MulAut.conj_apply, inv_inv] at h1
      rw [h1]
      exact hso
    have h1 := E6Pilot.conj_mem_normalizer_map_conj t (h.normalizer_le _ hs' hso')
    rwa [show t * (t⁻¹ * s * t) * t⁻¹ = s by group] at h1
  diag_mem := by
    rintro _ ⟨k, hk, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc : (k : G) * (t * k * t⁻¹) = t * k * t⁻¹ * k :=
      mem_centralizer_iff.1 (h.le_centralizer ⟨k, hk, rfl⟩) k hk
    have e : t * k * t⁻¹ * (t * (t * k * t⁻¹) * t⁻¹) = k * (t * k * t⁻¹) := by
      calc t * k * t⁻¹ * (t * (t * k * t⁻¹) * t⁻¹) = t * k * t⁻¹ * ((t * t) * k * (t * t)⁻¹) := by
            group
        _ = t * k * t⁻¹ * k := by rw [htt]; group
        _ = k * (t * k * t⁻¹) := hc.symm
    rw [e]
    exact h.diag_mem k hk
  diag_surj := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := h.diag_surj d hd
    refine ⟨t * k * t⁻¹, ⟨k, hk, rfl⟩, ?_⟩
    have hc : (k : G) * (t * k * t⁻¹) = t * k * t⁻¹ * k :=
      mem_centralizer_iff.1 (h.le_centralizer ⟨k, hk, rfl⟩) k hk
    calc t * k * t⁻¹ * (t * (t * k * t⁻¹) * t⁻¹) = t * k * t⁻¹ * ((t * t) * k * (t * t)⁻¹) := by
          group
      _ = t * k * t⁻¹ * k := by rw [htt]; group
      _ = k * (t * k * t⁻¹) := hc.symm

theorem SwapCover.flip_Kc (h : SwapCover t T D E) (htT : t ∈ centralizer (T : Set G))
    (htt : t * t = 1) : (h.flip htT htt).Kc = h.Kc.map (MulAut.conj t).toMonoidHom :=
  rfl

theorem swapMap_conj_eq_of_le_centralizer {H : Subgroup G} (htH : H ≤ centralizer ({t} : Set G)) :
    H.map (MulAut.conj t).toMonoidHom = H := by
  refine le_antisymm ?_ fun τ hτ => ⟨τ, hτ, ?_⟩
  · rintro _ ⟨τ, hτ, rfl⟩
    have hτt : τ * t = t * τ := mem_centralizer_singleton_iff.1 (htH hτ)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hτt, mul_inv_cancel_right]
    exact hτ
  · have hτt : τ * t = t * τ := mem_centralizer_singleton_iff.1 (htH hτ)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hτt, mul_inv_cancel_right]

theorem SwapCover.piece_flip [Finite G] (h : SwapCover t T D E) (htT : t ∈ centralizer (T : Set G))
    (htt : t * t = 1) {X : Subgroup G} (hXt : X ≤ centralizer ({t} : Set G)) :
    (h.flip htT htt).piece X = (h.piece X).map (MulAut.conj t).toMonoidHom := by
  rw [SwapCover.piece, SwapCover.piece, CFSG.Quasithin.map_perfectCore,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective, F4Pilot.map_centralizer_mulEquiv,
    swapMap_conj_eq_of_le_centralizer hXt, h.flip_Kc]

@[expose] def SwapCover.conj (h : SwapCover t T D E) (n : G) (hnt : n * t = t * n) :
    SwapCover t (T.map (MulAut.conj n).toMonoidHom) (D.map (MulAut.conj n).toMonoidHom)
      (E.map (MulAut.conj n).toMonoidHom) where
  Kc := h.Kc.map (MulAut.conj n).toMonoidHom
  perfect := by rw [← map_commutator, h.perfect]
  le_centralizer := by
    rw [E6Pilot.map_conj_map_conj_comm (Commute.symm hnt), ← F4Pilot.map_centralizer_mulEquiv]
    exact map_mono h.le_centralizer
  sup_eq := by
    rw [E6Pilot.map_conj_map_conj_comm (Commute.symm hnt), ← Subgroup.map_sup, h.sup_eq]
  normalizer_le := by
    intro s hs hso
    have hs' := E6Pilot.conj_inv_mem_centralizer_of_mem_centralizer_map_conj hs
    have hso' : Odd (orderOf (n⁻¹ * s * n)) := by
      have h1 := MulEquiv.orderOf_eq (MulAut.conj n⁻¹) s
      rw [MulAut.conj_apply, inv_inv] at h1
      rw [h1]
      exact hso
    have h1 := E6Pilot.conj_mem_normalizer_map_conj n (h.normalizer_le _ hs' hso')
    rwa [show n * (n⁻¹ * s * n) * n⁻¹ = s by group] at h1
  diag_mem := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨k * (t * k * t⁻¹), h.diag_mem k hk, ?_⟩
    have hnt' : t⁻¹ * n = n * t⁻¹ := by
      calc t⁻¹ * n = t⁻¹ * (n * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * n) * t⁻¹ := by rw [hnt]
        _ = n * t⁻¹ := by group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc n * (k * (t * k * t⁻¹)) * n⁻¹ = n * k * n⁻¹ * ((n * t) * k * (t⁻¹ * n⁻¹)) := by group
      _ = n * k * n⁻¹ * ((t * n) * k * (n⁻¹ * t⁻¹)) := by
          rw [hnt, show t⁻¹ * n⁻¹ = n⁻¹ * t⁻¹ by
            rw [← mul_inv_rev, ← mul_inv_rev, hnt]]
      _ = n * k * n⁻¹ * (t * (n * k * n⁻¹) * t⁻¹) := by group
  diag_surj := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨k, hk, rfl⟩ := h.diag_surj d hd
    refine ⟨n * k * n⁻¹, ⟨k, hk, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc n * k * n⁻¹ * (t * (n * k * n⁻¹) * t⁻¹) =
        n * k * n⁻¹ * ((t * n) * k * (n⁻¹ * t⁻¹)) := by group
      _ = n * k * n⁻¹ * ((n * t) * k * (t⁻¹ * n⁻¹)) := by
          rw [← hnt, show n⁻¹ * t⁻¹ = t⁻¹ * n⁻¹ by
            rw [← mul_inv_rev, ← mul_inv_rev, hnt]]
      _ = n * (k * (t * k * t⁻¹)) * n⁻¹ := by group

@[expose] def SwapCover.cast (h : SwapCover t T D E) {T' D' E' : Subgroup G} (hT : T = T')
    (hD : D = D') (hE : E = E') : SwapCover t T' D' E' :=
  hT ▸ hD ▸ hE ▸ h

theorem nonempty_quotient_center_mulEquiv_of_swapDiag' {G₁ L : Subgroup G}
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y)
    (hZ : center L = ⊥) : Nonempty (G₁ ⧸ center G₁ ≃* L) := by
  set δ := swapDiagHom h₁₂ with hδdef
  have hrange : δ.range = L := by
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, rfl⟩
      exact hδ x x.2
    · obtain ⟨x, hx, rfl⟩ := hsurj y hy
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : center G₁ = δ.ker := by
    refine le_antisymm (fun z hz => ?_) fun x hx => ?_
    · have hzL : δ z ∈ L := hrange ▸ ⟨z, rfl⟩
      have hzc : (⟨δ z, hzL⟩ : L) ∈ center L := by
        rw [mem_center_iff]
        rintro ⟨y, hy⟩
        rw [← hrange] at hy
        obtain ⟨g, rfl⟩ := hy
        apply Subtype.ext
        change δ g * δ z = δ z * δ g
        rw [← map_mul, ← map_mul, (mem_center_iff.1 hz g)]
      rw [hZ, mem_bot] at hzc
      exact congrArg Subtype.val hzc
    · rw [MonoidHom.mem_ker, swapDiagHom_apply] at hx
      have hxt : (x : G) ∈ G₁.map (MulAut.conj t).toMonoidHom := by
        refine ⟨(x : G)⁻¹, inv_mem x.2, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc t * (x : G)⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
          _ = x := (eq_inv_of_mul_eq_one_left hx).symm
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 (h₁₂ hxt) g g.2)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivRange δ)).trans (MulEquiv.subgroupCongr hrange)⟩

end Transport

end CFSG.SeitzReduction.TwistedE6Pilot
