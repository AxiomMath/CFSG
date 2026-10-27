module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapBasic
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapTriangle

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono perfectCore_perfect
  le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_def swapDiagHom)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Overlap

variable {G : Type*} [Group G]

theorem centralizer_sup_eq_inf_coverTriangle (X Y : Subgroup G) :
    centralizer ((X ⊔ Y : Subgroup G) : Set G) =
      centralizer (X : Set G) ⊓ centralizer (Y : Set G) :=
  le_antisymm
    (le_inf (centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))
      (centralizer_le (SetLike.coe_subset_coe.2 le_sup_right)))
    F4Pilot.centralizer_inf_centralizer_le_centralizer_sup

theorem perfectCore_centralizerPerfectCore_inf_coverTriangle [Finite G] (X Y : Subgroup G) :
    perfectCore (centralizerPerfectCore X ⊓ centralizer (Y : Set G)) =
      centralizerPerfectCore (X ⊔ Y) := by
  rw [centralizerPerfectCore_def (X ⊔ Y), centralizer_sup_eq_inf_coverTriangle,
    centralizerPerfectCore_def X]
  refine le_antisymm (perfectCore_mono (inf_le_inf_right _ (perfectCore_le _)))
    (le_perfectCore_of_perfect (le_inf ?_ ((perfectCore_le _).trans inf_le_right))
      (perfectCore_perfect _))
  exact le_perfectCore_of_perfect ((perfectCore_le _).trans inf_le_left) (perfectCore_perfect _)

end Overlap

section Piece

variable {G : Type*} [Group G] {t : G} {T D E : Subgroup G}

theorem SwapCover.diag_mem_perfectCore_coverTriangle [Finite G] (h : SwapCover t T D E)
    {Y : Subgroup G} (hYt : Y ≤ centralizer ({t} : Set G)) :
    ∀ k ∈ h.piece Y, k * (t * k * t⁻¹) ∈ perfectCore (D ⊓ centralizer (Y : Set G)) := by
  set P : Subgroup G := ((h.piece Y).subgroupOf h.Kc).map (swapDiagHom h.le_centralizer) with hP
  have hPp : ⁅P, P⁆ = P := by
    rw [hP, ← map_commutator,
      CFSG.SeitzReduction.commutator_subgroupOf_eq_self (h.piece_le Y) (h.commutator_piece Y)]
  have hPle : P ≤ D ⊓ centralizer (Y : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    exact h.diag_mem_inf hYt (mem_subgroupOf.1 hk)
  intro k hk
  exact le_perfectCore_of_perfect hPle hPp ⟨⟨k, h.piece_le Y hk⟩, mem_subgroupOf.2 hk, rfl⟩

theorem SwapCover.exists_mem_piece_diag_eq_perfectCore_coverTriangle [Finite G]
    (h : SwapCover t T D E) {Y : Subgroup G} (hYN : Y ≤ normalizer (h.Kc : Set G))
    (hYt : Y ≤ centralizer ({t} : Set G)) :
    ∀ y ∈ perfectCore (D ⊓ centralizer (Y : Set G)), ∃ k ∈ h.piece Y, k * (t * k * t⁻¹) = y :=
  h.exists_mem_piece_diag_eq hYN hYt ((perfectCore_le _).trans inf_le_left)
    ((perfectCore_le _).trans inf_le_right) (perfectCore_perfect _)

theorem SwapCover.piece_dichotomy_coverTriangle [Finite G] (h : SwapCover t T D E)
    {Y : Subgroup G} (hYN : Y ≤ normalizer (h.Kc : Set G)) (hYt : Y ≤ centralizer ({t} : Set G))
    (hS : IsSimpleGroup (perfectCore (D ⊓ centralizer (Y : Set G)))) :
    ∀ M : Subgroup G, M ≤ h.piece Y → h.piece Y ≤ normalizer (M : Set G) →
      M ≤ centralizer (h.piece Y : Set G) ∨ h.piece Y ≤ M :=
  h.piece_dichotomy hS (h.diag_mem_perfectCore_coverTriangle hYt)
    (h.exists_mem_piece_diag_eq_perfectCore_coverTriangle hYN hYt)

theorem SwapCover.piece_ne_bot_coverTriangle [Finite G] (h : SwapCover t T D E)
    {Y : Subgroup G} (hYN : Y ≤ normalizer (h.Kc : Set G)) (hYt : Y ≤ centralizer ({t} : Set G))
    (hS : IsSimpleGroup (perfectCore (D ⊓ centralizer (Y : Set G)))) : h.piece Y ≠ ⊥ := by
  intro hbot
  obtain ⟨y, hy⟩ := exists_ne (1 : perfectCore (D ⊓ centralizer (Y : Set G)))
  obtain ⟨k, hk, hky⟩ := h.exists_mem_piece_diag_eq_perfectCore_coverTriangle hYN hYt y y.2
  rw [hbot, mem_bot] at hk
  subst hk
  apply hy
  apply Subtype.ext
  rw [← hky]
  simp

theorem SwapCover.piece_eq_or_eq_conj_coverTriangle [Finite G] (h : SwapCover t T D E)
    {T' D' E' : Subgroup G} (h' : SwapCover t T' D' E') {Y Y' : Subgroup G}
    (hsup : h'.piece Y' ⊔ (h'.piece Y').map (MulAut.conj t).toMonoidHom =
      h.piece Y ⊔ (h.piece Y).map (MulAut.conj t).toMonoidHom)
    (hqs : ∀ M : Subgroup G, M ≤ h.piece Y → h.piece Y ≤ normalizer (M : Set G) →
      M ≤ centralizer (h.piece Y : Set G) ∨ h.piece Y ≤ M) (hne : h'.piece Y' ≠ ⊥) :
    h'.piece Y' = h.piece Y ∨ h'.piece Y' = (h.piece Y).map (MulAut.conj t).toMonoidHom :=
  E6Pilot.swapEq_or_eq_conj ((map_mono (h.piece_le Y)).trans (h.map_le_centralizer_piece Y))
    ((map_mono (h'.piece_le Y')).trans (h'.map_le_centralizer_piece Y')) hsup
    (h.commutator_piece Y) (by rw [← map_commutator, h.commutator_piece])
    (h'.commutator_piece Y') hne hqs (dichotomy_map_conj' t hqs)

theorem SwapCover.map_le_centralizer_of_eq_piece_coverTriangle (h : SwapCover t T D E)
    {A B Fa Fb : Subgroup G} (ha : Fa = h.piece A) (hb : Fb = h.piece B) :
    Fb.map (MulAut.conj t).toMonoidHom ≤ centralizer (Fa : Set G) := by
  rw [ha, hb]
  exact h.map_piece_le_centralizer_piece A B

end Piece

section Neighbour

variable {G : Type*} [Group G] {t : G} {X D : Subgroup G}

theorem SwapCover.le_centralizer_coverTriangle
    (h : SwapCover t X D (centralizerPerfectCore X)) : D ≤ centralizer (X : Set G) :=
  h.le_sup.trans (perfectCore_le _)

theorem SwapCover.le_normalizer_coverTriangle (h : SwapCover t X D (centralizerPerfectCore X))
    {Y : Subgroup G} (hYD : Y ≤ D) (hYo : ∀ y ∈ Y, Odd (orderOf y)) :
    Y ≤ normalizer (h.Kc : Set G) :=
  h.le_normalizer (hYD.trans h.le_centralizer_coverTriangle) hYo

theorem SwapCover.centralizerPerfectCore_sup_eq_coverTriangle [Finite G]
    (h : SwapCover t X D (centralizerPerfectCore X)) (htt : t * t = 1) {Y : Subgroup G}
    (hYD : Y ≤ D) (hYt : Y ≤ centralizer ({t} : Set G)) (hYo : ∀ y ∈ Y, Odd (orderOf y)) :
    centralizerPerfectCore (X ⊔ Y) =
      h.piece Y ⊔ (h.piece Y).map (MulAut.conj t).toMonoidHom := by
  rw [← perfectCore_centralizerPerfectCore_inf_coverTriangle]
  exact h.pieceCore_eq_sup htt (h.le_normalizer_coverTriangle hYD hYo) hYt

theorem SwapCover.exists_aligned_coverTriangle [Finite G] {X₁ X₂ D₁ D₂ : Subgroup G}
    (h₁ : SwapCover t X₁ D₁ (centralizerPerfectCore X₁))
    (h₂ : SwapCover t X₂ D₂ (centralizerPerfectCore X₂)) (htt : t * t = 1)
    (htX₂ : t ∈ centralizer (X₂ : Set G)) (hX₁t : X₁ ≤ centralizer ({t} : Set G))
    (hX₂t : X₂ ≤ centralizer ({t} : Set G)) (hX₁o : ∀ x ∈ X₁, Odd (orderOf x))
    (hX₂o : ∀ x ∈ X₂, Odd (orderOf x)) (h₂₁ : X₂ ≤ D₁) (h₁₂ : X₁ ≤ D₂)
    (hS : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₂ : Set G)))) :
    ∃ h₂' : SwapCover t X₂ D₂ (centralizerPerfectCore X₂), h₂'.piece X₁ = h₁.piece X₂ := by
  have hsup : h₂.piece X₁ ⊔ (h₂.piece X₁).map (MulAut.conj t).toMonoidHom =
      h₁.piece X₂ ⊔ (h₁.piece X₂).map (MulAut.conj t).toMonoidHom := by
    rw [← h₂.centralizerPerfectCore_sup_eq_coverTriangle htt h₁₂ hX₁t hX₁o,
      ← h₁.centralizerPerfectCore_sup_eq_coverTriangle htt h₂₁ hX₂t hX₂o, sup_comm X₂ X₁]
  have hN := h₁.le_normalizer_coverTriangle h₂₁ hX₂o
  have hne : h₂.piece X₁ ≠ ⊥ := by
    intro hbot
    refine h₁.piece_ne_bot_coverTriangle hN hX₂t hS (le_bot_iff.1 ?_)
    calc h₁.piece X₂ ≤ h₁.piece X₂ ⊔ (h₁.piece X₂).map (MulAut.conj t).toMonoidHom :=
          le_sup_left
      _ = ⊥ := by rw [← hsup, hbot, Subgroup.map_bot, sup_bot_eq]
  rcases h₁.piece_eq_or_eq_conj_coverTriangle h₂ hsup
      (h₁.piece_dichotomy_coverTriangle hN hX₂t hS) hne with h1 | h1
  · exact ⟨h₂, h1⟩
  · refine ⟨h₂.flip htX₂ htt, ?_⟩
    rw [h₂.piece_flip htX₂ htt hX₁t, h1, map_conj_map_conj_of_mul_self htt]

end Neighbour

section ThirdEdge

variable {G : Type*} [Group G] {t : G} {T D E : Subgroup G}

theorem SwapCover.commutator_eq_of_diag_eq_coverTriangle (h : SwapCover t T D E) {a b a' b' : G}
    (ha : a ∈ h.Kc) (hb : b ∈ h.Kc) (ha' : a' ∈ h.Kc) (hb' : b' ∈ h.Kc)
    (hδa : a * (t * a * t⁻¹) = a' * (t * a' * t⁻¹))
    (hδb : b * (t * b * t⁻¹) = b' * (t * b' * t⁻¹)) :
    a * b * a⁻¹ * b⁻¹ = a' * b' * a'⁻¹ * b'⁻¹ := by
  have hcen : ∀ {x x' : G}, x ∈ h.Kc → x' ∈ h.Kc → x * (t * x * t⁻¹) = x' * (t * x' * t⁻¹) →
      x⁻¹ * x' ∈ centralizer (h.Kc : Set G) := by
    intro x x' hx hx' hδ
    have hmem : x⁻¹ * x' ∈ h.Kc := mul_mem (inv_mem hx) hx'
    have h1 : (x⁻¹ * x') * (t * (x⁻¹ * x') * t⁻¹) = 1 := by
      rw [h.diag_mul (inv_mem hx) hx', h.diag_inv hx, hδ, inv_mul_cancel]
    exact h.le_centralizer (h.mem_map_conj_of_diag_eq_one hmem h1)
  have hu := hcen ha ha' hδa
  have hv := hcen hb hb' hδb
  obtain ⟨u, rfl⟩ : ∃ u, a' = a * u := ⟨a⁻¹ * a', by group⟩
  obtain ⟨v, rfl⟩ : ∃ v, b' = b * v := ⟨b⁻¹ * b', by group⟩
  rw [inv_mul_cancel_left] at hu hv
  have hvK : v ∈ h.Kc := by simpa using mul_mem (inv_mem hb) hb'
  have h1 : b * u = u * b := mem_centralizer_iff.1 hu b hb
  have h2 : v * u = u * v := mem_centralizer_iff.1 hu v hvK
  have h3 : a⁻¹ * v = v * a⁻¹ := mem_centralizer_iff.1 hv a⁻¹ (inv_mem ha)
  symm
  calc a * u * (b * v) * (a * u)⁻¹ * (b * v)⁻¹
      = a * (u * b) * v * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by group
    _ = a * (b * u) * v * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by rw [h1]
    _ = a * b * (u * v) * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by group
    _ = a * b * (v * u) * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by rw [h2]
    _ = a * b * (v * a⁻¹) * v⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * v) * v⁻¹ * b⁻¹ := by rw [h3]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem SwapCover.diag_conj_eq_coverTriangle (h : SwapCover t T D E) (htt : t * t = 1) {k : G}
    (hk : k ∈ h.Kc) : (t * k * t⁻¹) * (t * (t * k * t⁻¹) * t⁻¹) = k * (t * k * t⁻¹) := by
  have hc : k * (t * k * t⁻¹) = t * k * t⁻¹ * k :=
    mem_centralizer_iff.1 (h.le_centralizer ⟨k, hk, rfl⟩) k hk
  calc t * k * t⁻¹ * (t * (t * k * t⁻¹) * t⁻¹) =
        t * k * t⁻¹ * ((t * t) * k * (t * t)⁻¹) := by group
    _ = t * k * t⁻¹ * k := by rw [htt]; group
    _ = k * (t * k * t⁻¹) := hc.symm

theorem SwapCover.diag_eq_one_of_conj_eq_coverTriangle (h : SwapCover t T D E)
    (hZ : center D = ⊥) {c : G} (hc : c ∈ h.Kc) (hct : t * c * t⁻¹ = c) :
    c * (t * c * t⁻¹) = 1 := by
  have hcK : c ∈ centralizer (h.Kc : Set G) := by
    refine h.le_centralizer ⟨c, hc, ?_⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hct
  have hz : (⟨c * (t * c * t⁻¹), h.diag_mem c hc⟩ : D) ∈ center D := by
    rw [mem_center_iff]
    rintro ⟨d, hd⟩
    obtain ⟨k, hk, rfl⟩ := h.diag_surj d hd
    apply Subtype.ext
    show k * (t * k * t⁻¹) * (c * (t * c * t⁻¹)) = c * (t * c * t⁻¹) * (k * (t * k * t⁻¹))
    have hkc : k * c = c * k := mem_centralizer_iff.1 hcK k hk
    rw [← h.diag_mul hk hc, ← h.diag_mul hc hk, hkc]
  rw [hZ, mem_bot] at hz
  exact congrArg Subtype.val hz

theorem commute_of_swapCover_triangle {T₁ T₂ T₃ D₁ D₂ D₃ E₁ E₂ E₃ : Subgroup G}
    (h₁ : SwapCover t T₁ D₁ E₁) (h₂ : SwapCover t T₂ D₂ E₂) (h₃ : SwapCover t T₃ D₃ E₃)
    (htt : t * t = 1) (hZ₁ : center D₁ = ⊥) {y y' z z' w w' : G}
    (hy₁ : y ∈ h₁.Kc) (hy'₁ : y' ∈ h₁.Kc) (hz₁ : z ∈ h₁.Kc) (hz'₁ : z' ∈ h₁.Kc)
    (hy₂ : y ∈ h₂.Kc) (hy'₂ : y' ∈ h₂.Kc) (hw₂ : w ∈ h₂.Kc) (hw'₂ : w' ∈ h₂.Kc)
    (hz₃ : z ∈ h₃.Kc) (hz'₃ : z' ∈ h₃.Kc) (hw₃ : t * w * t⁻¹ ∈ h₃.Kc)
    (hw'₃ : t * w' * t⁻¹ ∈ h₃.Kc)
    (hyz : y * (t * y * t⁻¹) = z * (t * z * t⁻¹)) (hyw : y * (t * y * t⁻¹) = w * (t * w * t⁻¹))
    (hy'z' : y' * (t * y' * t⁻¹) = z' * (t * z' * t⁻¹))
    (hy'w' : y' * (t * y' * t⁻¹) = w' * (t * w' * t⁻¹)) :
    (y * (t * y * t⁻¹)) * (y' * (t * y' * t⁻¹)) =
      (y' * (t * y' * t⁻¹)) * (y * (t * y * t⁻¹)) := by
  have e₁ : y * y' * y⁻¹ * y'⁻¹ = z * z' * z⁻¹ * z'⁻¹ :=
    h₁.commutator_eq_of_diag_eq_coverTriangle hy₁ hy'₁ hz₁ hz'₁ hyz hy'z'
  have e₂ : y * y' * y⁻¹ * y'⁻¹ = w * w' * w⁻¹ * w'⁻¹ :=
    h₂.commutator_eq_of_diag_eq_coverTriangle hy₂ hy'₂ hw₂ hw'₂ hyw hy'w'
  have e₃ : z * z' * z⁻¹ * z'⁻¹ =
      (t * w * t⁻¹) * (t * w' * t⁻¹) * (t * w * t⁻¹)⁻¹ * (t * w' * t⁻¹)⁻¹ := by
    refine h₃.commutator_eq_of_diag_eq_coverTriangle hz₃ hz'₃ hw₃ hw'₃ ?_ ?_
    · rw [h₂.diag_conj_eq_coverTriangle htt hw₂, ← hyw, hyz]
    · rw [h₂.diag_conj_eq_coverTriangle htt hw'₂, ← hy'w', hy'z']
  have hct : t * (y * y' * y⁻¹ * y'⁻¹) * t⁻¹ = y * y' * y⁻¹ * y'⁻¹ := by
    calc t * (y * y' * y⁻¹ * y'⁻¹) * t⁻¹ = t * (w * w' * w⁻¹ * w'⁻¹) * t⁻¹ := by rw [e₂]
      _ = (t * w * t⁻¹) * (t * w' * t⁻¹) * (t * w * t⁻¹)⁻¹ * (t * w' * t⁻¹)⁻¹ := by group
      _ = z * z' * z⁻¹ * z'⁻¹ := e₃.symm
      _ = y * y' * y⁻¹ * y'⁻¹ := e₁.symm
  have hyy' : y * y' ∈ h₁.Kc := mul_mem hy₁ hy'₁
  have hyy'y : y * y' * y⁻¹ ∈ h₁.Kc := mul_mem hyy' (inv_mem hy₁)
  have h1 := h₁.diag_eq_one_of_conj_eq_coverTriangle hZ₁ (mul_mem hyy'y (inv_mem hy'₁)) hct
  rw [h₁.diag_mul hyy'y (inv_mem hy'₁), h₁.diag_mul hyy' (inv_mem hy₁), h₁.diag_mul hy₁ hy'₁,
    h₁.diag_inv hy₁, h₁.diag_inv hy'₁, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

end ThirdEdge

section Triangle

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem exists_swapFactors_of_swapCover_triangle (hL : IsSimpleGroup L) (htt : t * t = 1)
    (htL : t ∈ centralizer (L : Set G)) {X₁ X₂ X₃ D₁ D₂ D₃ : Subgroup G}
    (h₁ : SwapCover t X₁ D₁ (centralizerPerfectCore X₁))
    (h₂ : SwapCover t X₂ D₂ (centralizerPerfectCore X₂))
    (h₃ : SwapCover t X₃ D₃ (centralizerPerfectCore X₃))
    (hX₁L : X₁ ≤ L) (hX₂L : X₂ ≤ L) (hX₃L : X₃ ≤ L)
    (hX₁o : ∀ x ∈ X₁, Odd (orderOf x)) (hX₂o : ∀ x ∈ X₂, Odd (orderOf x))
    (hX₃o : ∀ x ∈ X₃, Odd (orderOf x))
    (h₂₁ : X₂ ≤ D₁) (h₃₁ : X₃ ≤ D₁) (h₁₂ : X₁ ≤ D₂) (h₃₂ : X₃ ≤ D₂) (h₁₃ : X₁ ≤ D₃)
    (h₂₃ : X₂ ≤ D₃) (hZ₁ : center D₁ = ⊥)
    (hS₁₂ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₂ : Set G))))
    (hS₁₃ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₃ : Set G))))
    (hS₂₃ : IsSimpleGroup (perfectCore (D₂ ⊓ centralizer (X₃ : Set G))))
    {q q' : G} (hq₁₂ : q ∈ perfectCore (D₁ ⊓ centralizer (X₂ : Set G)))
    (hq₁₃ : q ∈ perfectCore (D₁ ⊓ centralizer (X₃ : Set G)))
    (hq₂₃ : q ∈ perfectCore (D₂ ⊓ centralizer (X₃ : Set G)))
    (hq'₁₂ : q' ∈ perfectCore (D₁ ⊓ centralizer (X₂ : Set G)))
    (hq'₁₃ : q' ∈ perfectCore (D₁ ⊓ centralizer (X₃ : Set G)))
    (hq'₂₃ : q' ∈ perfectCore (D₂ ⊓ centralizer (X₃ : Set G))) (hqq' : q * q' ≠ q' * q)
    (hgen : perfectCore (D₁ ⊓ centralizer (X₂ : Set G)) ⊔
      perfectCore (D₁ ⊓ centralizer (X₃ : Set G)) ⊔
        perfectCore (D₂ ⊓ centralizer (X₃ : Set G)) = L) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        centralizerPerfectCore (X₁ ⊔ X₂) ⊔ centralizerPerfectCore (X₁ ⊔ X₃) ⊔
          centralizerPerfectCore (X₂ ⊔ X₃) := by
  have hLt : L ≤ centralizer ({t} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL x hx)
  have hX₁t := hX₁L.trans hLt
  have hX₂t := hX₂L.trans hLt
  have hX₃t := hX₃L.trans hLt
  have htX₂ : t ∈ centralizer (X₂ : Set G) := centralizer_le (SetLike.coe_subset_coe.2 hX₂L) htL
  have htX₃ : t ∈ centralizer (X₃ : Set G) := centralizer_le (SetLike.coe_subset_coe.2 hX₃L) htL
  obtain ⟨h₂', a₁₂⟩ := SwapCover.exists_aligned_coverTriangle h₁ h₂ htt htX₂ hX₁t hX₂t hX₁o hX₂o
    h₂₁ h₁₂ hS₁₂
  obtain ⟨h₃', a₁₃⟩ := SwapCover.exists_aligned_coverTriangle h₁ h₃ htt htX₃ hX₁t hX₃t hX₁o hX₃o
    h₃₁ h₁₃ hS₁₃
  have hN₁₂ := h₁.le_normalizer_coverTriangle h₂₁ hX₂o
  have hN₁₃ := h₁.le_normalizer_coverTriangle h₃₁ hX₃o
  have hN₂₃ := h₂'.le_normalizer_coverTriangle h₃₂ hX₃o
  have a₂₃ : h₃'.piece X₂ = h₂'.piece X₃ := by
    have hsup : h₃'.piece X₂ ⊔ (h₃'.piece X₂).map (MulAut.conj t).toMonoidHom =
        h₂'.piece X₃ ⊔ (h₂'.piece X₃).map (MulAut.conj t).toMonoidHom := by
      rw [← h₃'.centralizerPerfectCore_sup_eq_coverTriangle htt h₂₃ hX₂t hX₂o,
        ← h₂'.centralizerPerfectCore_sup_eq_coverTriangle htt h₃₂ hX₃t hX₃o, sup_comm X₃ X₂]
    have hne : h₃'.piece X₂ ≠ ⊥ := by
      intro hbot
      refine h₂'.piece_ne_bot_coverTriangle hN₂₃ hX₃t hS₂₃ (le_bot_iff.1 ?_)
      calc h₂'.piece X₃ ≤ h₂'.piece X₃ ⊔ (h₂'.piece X₃).map (MulAut.conj t).toMonoidHom :=
            le_sup_left
        _ = ⊥ := by rw [← hsup, hbot, Subgroup.map_bot, sup_bot_eq]
    rcases h₂'.piece_eq_or_eq_conj_coverTriangle h₃' hsup
        (h₂'.piece_dichotomy_coverTriangle hN₂₃ hX₃t hS₂₃) hne with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨y, hy, hyq⟩ :=
        h₁.exists_mem_piece_diag_eq_perfectCore_coverTriangle hN₁₂ hX₂t q hq₁₂
      obtain ⟨y', hy', hy'q⟩ :=
        h₁.exists_mem_piece_diag_eq_perfectCore_coverTriangle hN₁₂ hX₂t q' hq'₁₂
      obtain ⟨z, hz, hzq⟩ :=
        h₁.exists_mem_piece_diag_eq_perfectCore_coverTriangle hN₁₃ hX₃t q hq₁₃
      obtain ⟨z', hz', hz'q⟩ :=
        h₁.exists_mem_piece_diag_eq_perfectCore_coverTriangle hN₁₃ hX₃t q' hq'₁₃
      obtain ⟨w, hw, hwq⟩ :=
        h₂'.exists_mem_piece_diag_eq_perfectCore_coverTriangle hN₂₃ hX₃t q hq₂₃
      obtain ⟨w', hw', hw'q⟩ :=
        h₂'.exists_mem_piece_diag_eq_perfectCore_coverTriangle hN₂₃ hX₃t q' hq'₂₃
      have hF₁₂ : h₁.piece X₂ ≤ h₂'.Kc := by
        rw [← a₁₂]
        exact h₂'.piece_le X₁
      have hF₁₃ : h₁.piece X₃ ≤ h₃'.Kc := by
        rw [← a₁₃]
        exact h₃'.piece_le X₁
      have hF₂₃ : (h₂'.piece X₃).map (MulAut.conj t).toMonoidHom ≤ h₃'.Kc := by
        rw [← h1]
        exact h₃'.piece_le X₂
      apply hqq'
      have hc := commute_of_swapCover_triangle h₁ h₂' h₃' htt hZ₁ (h₁.piece_le X₂ hy)
        (h₁.piece_le X₂ hy') (h₁.piece_le X₃ hz) (h₁.piece_le X₃ hz') (hF₁₂ hy) (hF₁₂ hy')
        (h₂'.piece_le X₃ hw) (h₂'.piece_le X₃ hw') (hF₁₃ hz) (hF₁₃ hz') (hF₂₃ ⟨w, hw, rfl⟩)
        (hF₂₃ ⟨w', hw', rfl⟩) (hyq.trans hzq.symm) (hyq.trans hwq.symm) (hy'q.trans hz'q.symm)
        (hy'q.trans hw'q.symm)
      rwa [hyq, hy'q] at hc
  set F : Fin 3 → Subgroup G := ![h₁.piece X₂, h₁.piece X₃, h₂'.piece X₃] with hF
  set O : Fin 3 → Subgroup G := ![perfectCore (D₁ ⊓ centralizer (X₂ : Set G)),
    perfectCore (D₁ ⊓ centralizer (X₃ : Set G)), perfectCore (D₂ ⊓ centralizer (X₃ : Set G))]
    with hO
  have hcomm : ∀ k l, (F l).map (MulAut.conj t).toMonoidHom ≤ centralizer (F k : Set G) := by
    intro k l
    fin_cases k <;> fin_cases l
    · exact h₁.map_le_centralizer_of_eq_piece_coverTriangle rfl rfl
    · exact h₁.map_le_centralizer_of_eq_piece_coverTriangle rfl rfl
    · exact h₂'.map_le_centralizer_of_eq_piece_coverTriangle a₁₂.symm rfl
    · exact h₁.map_le_centralizer_of_eq_piece_coverTriangle rfl rfl
    · exact h₁.map_le_centralizer_of_eq_piece_coverTriangle rfl rfl
    · exact h₃'.map_le_centralizer_of_eq_piece_coverTriangle a₁₃.symm a₂₃.symm
    · exact h₂'.map_le_centralizer_of_eq_piece_coverTriangle rfl a₁₂.symm
    · exact h₃'.map_le_centralizer_of_eq_piece_coverTriangle a₂₃.symm a₁₃.symm
    · exact h₂'.map_le_centralizer_of_eq_piece_coverTriangle rfl rfl
  have hperf : ∀ k, ⁅F k, F k⁆ = F k := by
    intro k
    fin_cases k
    · exact h₁.commutator_piece _
    · exact h₁.commutator_piece _
    · exact h₂'.commutator_piece _
  have hδ : ∀ k, ∀ x ∈ F k, x * (t * x * t⁻¹) ∈ O k := by
    intro k
    fin_cases k
    · exact h₁.diag_mem_perfectCore_coverTriangle hX₂t
    · exact h₁.diag_mem_perfectCore_coverTriangle hX₃t
    · exact h₂'.diag_mem_perfectCore_coverTriangle hX₃t
  have hsurjO : ∀ k, ∀ y ∈ O k, ∃ x ∈ F k, x * (t * x * t⁻¹) = y := by
    intro k
    fin_cases k
    · exact h₁.exists_mem_piece_diag_eq_perfectCore_coverTriangle hN₁₂ hX₂t
    · exact h₁.exists_mem_piece_diag_eq_perfectCore_coverTriangle hN₁₃ hX₃t
    · exact h₂'.exists_mem_piece_diag_eq_perfectCore_coverTriangle hN₂₃ hX₃t
  have hgen' : ⨆ k, O k = L := by
    rw [E8Pilot.iSup_fin_three_subgroup]
    exact hgen
  obtain ⟨hq'', h₁₂', hδL, hsurjL⟩ :=
    SeitzQ2.isQuasisimple_iSup_of_diag hL F O hcomm hperf hδ hsurjO hgen'
  refine ⟨⨆ k, F k, hq'', h₁₂', hδL, hsurjL, ?_⟩
  have hE₁₂ := h₁.centralizerPerfectCore_sup_eq_coverTriangle htt h₂₁ hX₂t hX₂o
  have hE₁₃ := h₁.centralizerPerfectCore_sup_eq_coverTriangle htt h₃₁ hX₃t hX₃o
  have hE₂₃ := h₂'.centralizerPerfectCore_sup_eq_coverTriangle htt h₃₂ hX₃t hX₃o
  rw [E8Pilot.iSup_fin_three_subgroup, Subgroup.map_sup, Subgroup.map_sup, hE₁₂, hE₁₃, hE₂₃]
  exact E8Pilot.sup_three_sup_three_subgroup _ _ _ _ _ _

theorem exists_swapFactors_unique_of_swapCover_triangle {P : Type} [Group P] [Finite P]
    (hset : SeitzSetting G L) (hOut : Group.IsSolvable (Outer L)) (e : L ≃* P)
    (hP : SeitzQ2.SwapPairExclusion P) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X₁ X₂ X₃ D₁ D₂ D₃ : Subgroup G}
    (h₁ : SwapCover t X₁ D₁ (centralizerPerfectCore X₁))
    (h₂ : SwapCover t X₂ D₂ (centralizerPerfectCore X₂))
    (h₃ : SwapCover t X₃ D₃ (centralizerPerfectCore X₃))
    (hX₁L : X₁ ≤ L) (hX₂L : X₂ ≤ L) (hX₃L : X₃ ≤ L)
    (hX₁o : ∀ x ∈ X₁, Odd (orderOf x)) (hX₂o : ∀ x ∈ X₂, Odd (orderOf x))
    (hX₃o : ∀ x ∈ X₃, Odd (orderOf x))
    (h₂₁ : X₂ ≤ D₁) (h₃₁ : X₃ ≤ D₁) (h₁₂ : X₁ ≤ D₂) (h₃₂ : X₃ ≤ D₂) (h₁₃ : X₁ ≤ D₃)
    (h₂₃ : X₂ ≤ D₃) (hZ₁ : center D₁ = ⊥)
    (hS₁₂ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₂ : Set G))))
    (hS₁₃ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₃ : Set G))))
    (hS₂₃ : IsSimpleGroup (perfectCore (D₂ ⊓ centralizer (X₃ : Set G))))
    {q q' : G} (hq₁₂ : q ∈ perfectCore (D₁ ⊓ centralizer (X₂ : Set G)))
    (hq₁₃ : q ∈ perfectCore (D₁ ⊓ centralizer (X₃ : Set G)))
    (hq₂₃ : q ∈ perfectCore (D₂ ⊓ centralizer (X₃ : Set G)))
    (hq'₁₂ : q' ∈ perfectCore (D₁ ⊓ centralizer (X₂ : Set G)))
    (hq'₁₃ : q' ∈ perfectCore (D₁ ⊓ centralizer (X₃ : Set G)))
    (hq'₂₃ : q' ∈ perfectCore (D₂ ⊓ centralizer (X₃ : Set G))) (hqq' : q * q' ≠ q' * q)
    (hgen : perfectCore (D₁ ⊓ centralizer (X₂ : Set G)) ⊔
      perfectCore (D₁ ⊓ centralizer (X₃ : Set G)) ⊔
        perfectCore (D₂ ⊓ centralizer (X₃ : Set G)) = L) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        centralizerPerfectCore (X₁ ⊔ X₂) ⊔ centralizerPerfectCore (X₁ ⊔ X₃) ⊔
          centralizerPerfectCore (X₂ ⊔ X₃) ∧
      ∀ g : G, g⁻¹ * t * g ∈
          normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
        g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hL := SeitzQ2.isSimpleGroup_of_seitzSetting hset
  have htL := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨G₁, hq'', h₁₂', hδ, hsurj, hspan⟩ := exists_swapFactors_of_swapCover_triangle hL htt
    htL h₁ h₂ h₃ hX₁L hX₂L hX₃L hX₁o hX₂o hX₃o h₂₁ h₃₁ h₁₂ h₃₂ h₁₃ h₂₃ hZ₁ hS₁₂ hS₁₃ hS₂₃ hq₁₂
    hq₁₃ hq₂₃ hq'₁₂ hq'₁₃ hq'₂₃ hqq' hgen
  have hD₁ := h₁.le_centralizer_coverTriangle
  have hD₂ := h₂.le_centralizer_coverTriangle
  have hcen : ∀ {O A B : Subgroup G}, O ≤ centralizer (A : Set G) →
      O ≤ centralizer (B : Set G) → O ≤ centralizer ((A ⊔ B : Subgroup G) : Set G) :=
    fun hA hB => le_centralizer_iff.2 (sup_le (le_centralizer_iff.1 hA) (le_centralizer_iff.1 hB))
  refine ⟨G₁, hq'', h₁₂', hδ, hsurj, hspan,
    SeitzQ2.unique_of_swapFactors_of_neighbours_of_swapPairExclusion hset hOut e hP ht hKt hq''
      h₁₂' hδ hsurj ![X₁ ⊔ X₂, X₁ ⊔ X₃, X₂ ⊔ X₃]
      ![perfectCore (D₁ ⊓ centralizer (X₂ : Set G)), perfectCore (D₁ ⊓ centralizer (X₃ : Set G)),
        perfectCore (D₂ ⊓ centralizer (X₃ : Set G))] (fun k => ?_) (fun k => ?_) (fun k => ?_) ?_
      (fun k => ?_)⟩
  · fin_cases k
    · exact sup_le hX₁L hX₂L
    · exact sup_le hX₁L hX₃L
    · exact sup_le hX₂L hX₃L
  · fin_cases k
    · exact hcen (((perfectCore_le _).trans inf_le_left).trans hD₁)
        ((perfectCore_le _).trans inf_le_right)
    · exact hcen (((perfectCore_le _).trans inf_le_left).trans hD₁)
        ((perfectCore_le _).trans inf_le_right)
    · exact hcen (((perfectCore_le _).trans inf_le_left).trans hD₂)
        ((perfectCore_le _).trans inf_le_right)
  · fin_cases k <;> exact perfectCore_perfect _
  · rw [E8Pilot.iSup_fin_three_subgroup]
    exact hgen
  · rw [hspan]
    fin_cases k
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right

theorem false_of_swapCover_triangle {P : Type} [Group P] [Finite P] (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* P) (hP : SeitzQ2.SwapPairExclusion P)
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X₁ X₂ X₃ D₁ D₂ D₃ : Subgroup G}
    (h₁ : SwapCover t X₁ D₁ (F4Pilot.centralizerPerfectCore X₁))
    (h₂ : SwapCover t X₂ D₂ (F4Pilot.centralizerPerfectCore X₂))
    (h₃ : SwapCover t X₃ D₃ (F4Pilot.centralizerPerfectCore X₃))
    (hX₁L : X₁ ≤ L) (hX₂L : X₂ ≤ L) (hX₃L : X₃ ≤ L) (_hD₁L : D₁ ≤ L) (_hD₂L : D₂ ≤ L)
    (_hD₃L : D₃ ≤ L)
    (hX₁o : ∀ x ∈ X₁, Odd (orderOf x)) (hX₂o : ∀ x ∈ X₂, Odd (orderOf x))
    (hX₃o : ∀ x ∈ X₃, Odd (orderOf x))
    (h₂₁ : X₂ ≤ D₁) (h₃₁ : X₃ ≤ D₁) (h₁₂ : X₁ ≤ D₂) (h₃₂ : X₃ ≤ D₂) (h₁₃ : X₁ ≤ D₃)
    (h₂₃ : X₂ ≤ D₃)
    (hZ₁ : center D₁ = ⊥)
    (hS₁₂ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₂ : Set G))))
    (hS₁₃ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₃ : Set G))))
    (hS₂₃ : IsSimpleGroup (perfectCore (D₂ ⊓ centralizer (X₃ : Set G))))
    {q q' : G} (hq₁₂ : q ∈ perfectCore (D₁ ⊓ centralizer (X₂ : Set G)))
    (hq₁₃ : q ∈ perfectCore (D₁ ⊓ centralizer (X₃ : Set G)))
    (hq₂₃ : q ∈ perfectCore (D₂ ⊓ centralizer (X₃ : Set G)))
    (hq'₁₂ : q' ∈ perfectCore (D₁ ⊓ centralizer (X₂ : Set G)))
    (hq'₁₃ : q' ∈ perfectCore (D₁ ⊓ centralizer (X₃ : Set G)))
    (hq'₂₃ : q' ∈ perfectCore (D₂ ⊓ centralizer (X₃ : Set G))) (hqq' : q * q' ≠ q' * q)
    (hgen : perfectCore (D₁ ⊓ centralizer (X₂ : Set G)) ⊔
      perfectCore (D₁ ⊓ centralizer (X₃ : Set G)) ⊔
        perfectCore (D₂ ⊓ centralizer (X₃ : Set G)) = L) : False := by
  obtain ⟨G₁, hq'', h₁₂', -, -, -, huniq⟩ := exists_swapFactors_unique_of_swapCover_triangle hset
    hOut e hP ht hKt h₁ h₂ h₃ hX₁L hX₂L hX₃L hX₁o hX₂o hX₃o h₂₁ h₃₁ h₁₂ h₃₂ h₁₃ h₂₃ hZ₁ hS₁₂
    hS₁₃ hS₂₃ hq₁₂ hq₁₃ hq₂₃ hq'₁₂ hq'₁₃ hq'₂₃ hqq' hgen
  have : IsSimpleGroup G := hset.1
  exact F4Pilot.false_of_simple_of_swap_of_isQuasisimple ht hq'' h₁₂' rfl huniq

end Triangle

end CFSG.SeitzReduction.TwistedE6Pilot
