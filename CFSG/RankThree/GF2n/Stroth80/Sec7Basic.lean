module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec5Core
public import CFSG.CGT.Timmesfeld75.WeaklyClosed
public import CFSG.RankThree.GF2n.Stroth80.Sec5Comm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_isCentrePre {R : Subgroup G} (hQR : Q ≤ R) :
    ∃ Z0 : Subgroup G, IsCentrePre Z0 R Q := by
  obtain ⟨S, hS⟩ := sec51_exists_subgroup R Q hQR
  refine ⟨S ⊓ R, fun x => ?_⟩
  rw [Subgroup.mem_inf, hS, and_comm]

theorem IsCentrePre.le {Z0 R : Subgroup G} (h : IsCentrePre Z0 R Q) : Z0 ≤ R :=
  fun _ hx => ((h _).mp hx).1

theorem IsCentrePre.comm_mem {Z0 R : Subgroup G} (h : IsCentrePre Z0 R Q) {x r : G} (hx : x ∈ Z0)
    (hr : r ∈ R) : ⁅x, r⁆ ∈ Q := ((h _).mp hx).2 r hr

theorem IsCentrePre.mem_iff {Z0 R : Subgroup G} (h : IsCentrePre Z0 R Q) {x : G} :
    x ∈ Z0 ↔ x ∈ R ∧ ∀ r ∈ R, ⁅x, r⁆ ∈ Q := h x

theorem IsCentrePre.Q_le {Z0 R : Subgroup G} (h : IsCentrePre Z0 R Q) (hQR : Q ≤ R)
    (hnorm : ∀ r ∈ R, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q) : Q ≤ Z0 := by
  intro x hx
  refine (h x).mpr ⟨hQR hx, fun r hr => ?_⟩
  have e : ⁅x, r⁆ = x * (r * x⁻¹ * r⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact Q.mul_mem hx (hnorm r hr x⁻¹ (Q.inv_mem hx))

theorem IsCentrePre.mem_of_mem_LB {hc : Ctx M Q Z B} {t : G} (ht : t ∈ LB M Q B)
    {Z0 : Subgroup G} (h : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : t ∈ Z0 := by
  refine (h t).mpr ⟨le_Rt (M := M) (LB M Q B) ht ht, fun r hr => ?_⟩
  have := hc.Rt_comm_mem_Q hr
  rw [← commutatorElement_inv]
  exact Q.inv_mem this

theorem Ctx.exists_centre (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    ∃ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q :=
  exists_isCentrePre (hc.Q_le_Rt ht)

theorem ConjMod.of_mem {t : G} (ht : t ∈ M) : ConjMod M Q t t := by
  unfold ConjMod
  refine ⟨ht, 1, M.one_mem, ?_⟩
  have e : t * (1 * t * 1⁻¹)⁻¹ = 1 := by group
  rw [e]
  exact Q.one_mem

theorem comm_mul_Q_mem_iff (hc : Ctx M Q Z B) {V : Subgroup G} (hZV : Z ≤ V) {x q w : G}
    (hx : x ∈ M) (hq : q ∈ Q) (hw : w ∈ Q) : ⁅x * q, w⁆ ∈ V ↔ ⁅x, w⁆ ∈ V := by
  have hqw : ⁅q, w⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hq hw
  have hcz : x * ⁅q, w⁆ * x⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hx) ⁅q, w⁆).mp hqw
  have hcV : x * ⁅q, w⁆ * x⁻¹ ∈ V := hZV hcz
  have e : ⁅x * q, w⁆ = (x * ⁅q, w⁆ * x⁻¹) * ⁅x, w⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact V.mul_mem_cancel_left hcV

theorem comm_mul_Q_mem_Z_iff (hc : Ctx M Q Z B) {x q v : G} (hx : x ∈ M) (hq : q ∈ Q)
    (hv : v ∈ Q) : ⁅x * q, v⁆ ∈ Z ↔ ⁅x, v⁆ ∈ Z :=
  comm_mul_Q_mem_iff (V := Z) hc le_rfl hx hq hv

theorem commutator_zpowers_le_Z (hc : Ctx M Q Z B) {V : Subgroup G} (hVQ : V ≤ Q) {x : G}
    (hxM : x ∈ M) (hx : ∀ v ∈ V, ⁅x, v⁆ ∈ Z) : ⁅Subgroup.zpowers x, V⁆ ≤ Z := by
  refine Subgroup.commutator_le.mpr fun a ha v hv => ?_
  have h1 : v ∈ Q1 hc x := (hc.mem_Q1_iff hxM).mpr ⟨hVQ hv, hx v hv⟩
  exact h1.2 a ha

theorem Ut_le_Wt_of_vanish (hc : Ctx M Q Z B) {V : Subgroup G} (hVQ : V ≤ Q) {x : G}
    (hxH : x ∈ H0 M Z) (hx : ∀ v ∈ V, ⁅x, v⁆ ∈ Z) : Ut Q Z x ≤ Wt Q V := by
  have hxM : x ∈ M := hxH.1
  refine sup_le ?_ ?_
  · have hQ : ⁅Q, Subgroup.zpowers x⁆ ≤ Q :=
      Subgroup.commutator_le.mpr fun y hy a ha => by
        have haM : a ∈ M := (Subgroup.zpowers_le.mpr hxM) ha
        exact hc.comm_mem_Q haM hy
    have hcent : ⁅⁅Q, Subgroup.zpowers x⁆, V⁆ = ⊥ := by
      refine Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := Q)
        (H₂ := Subgroup.zpowers x) (H₃ := V) ?_ ?_
      · refine eq_bot_iff.mpr ((Subgroup.commutator_mono_left
          (commutator_zpowers_le_Z hc hVQ hxM hx)).trans (le_of_eq ?_))
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro z hz
        exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (hc.hyp.toHyp79.V_central hz hy).symm
      · have hVZ : ⁅V, Q⁆ ≤ Z :=
          Subgroup.commutator_le.mpr fun v hv y hy => hc.hyp.toHyp79.comm_mem_V (hVQ hv) hy
        refine eq_bot_iff.mpr ((Subgroup.commutator_mono_left hVZ).trans (le_of_eq ?_))
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro z hz a ha
        have : x ∈ Subgroup.centralizer (Z : Set G) := hxH.2
        have h2 : Subgroup.zpowers x ≤ Subgroup.centralizer (Z : Set G) :=
          Subgroup.zpowers_le.mpr this
        exact (Subgroup.mem_centralizer_iff.mp (h2 ha) z hz).symm
    refine fun u hu => ⟨hQ hu, ?_⟩
    have := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcent) hu
    exact this
  · intro z hz
    refine ⟨hc.Z_le_Q hz, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm

theorem Fgen_le (M Q L Z0 : Subgroup G) : Fgen M Q L Z0 ≤ L :=
  (Subgroup.closure_le L).mpr fun _ hx => hx.1

theorem Z0_le_Fgen {L Z0 : Subgroup G} (hZL : Z0 ≤ L) (hZM : Z0 ≤ M) (Q : Subgroup G) :
    Z0 ≤ Fgen M Q L Z0 := fun z hz =>
  Subgroup.subset_closure ⟨hZL hz, z, hz, hZM hz, 1, M.one_mem, by simpa using Q.one_mem⟩

theorem Q_le_Fgen {L Z0 : Subgroup G} (hQL : Q ≤ L) (hQM : Q ≤ M) :
    Q ≤ Fgen M Q L Z0 := fun q hq =>
  Subgroup.subset_closure ⟨hQL hq, 1, Z0.one_mem, hQM hq, 1, M.one_mem, by simpa using hq⟩

theorem Ut_conj_of_normalizes {g : G} (hgQ : conjSubgroup g Q = Q)
    (hgZ : conjSubgroup g Z = Z) (u : G) :
    Ut Q Z (g * u * g⁻¹) = conjSubgroup g (Ut Q Z u) := by
  have hzp : conjSubgroup g (Subgroup.zpowers u) = Subgroup.zpowers (g * u * g⁻¹) := by
    have h : (MulAut.conj g).toMonoidHom u = g * u * g⁻¹ := rfl
    rw [← h]
    exact MonoidHom.map_zpowers _ _
  unfold Ut
  rw [conjSubgroup_sup', conjSubgroup_commutator, hgQ, hgZ, hzp]

theorem card_Ut_conj (hc : Ctx M Q Z B) {g : G} (hg : g ∈ M) (u : G) :
    Nat.card ↥(Ut Q Z (g * u * g⁻¹)) = Nat.card ↥(Ut Q Z u) := by
  rw [Ut_conj_of_normalizes (hc.conj_Q_eq hg) (hc.conj_Z_eq hg) u,
    CFSG.CGT.Timmesfeld75.card_conjSubgroup]

theorem stronglyClosedMod_of_card (hc : Ctx M Q Z B) {L N : Subgroup G} (c : ℕ)
    (hα : ∀ x ∈ N, Nat.card ↥(Ut Q Z x) ≤ c)
    (hβ : ∀ y ∈ L, y ∉ N → c < Nat.card ↥(Ut Q Z y)) :
    StronglyClosedMod M N L := by
  unfold StronglyClosedMod
  intro x hx g hg hy
  by_contra hn
  have h1 := hβ _ hy hn
  have h2 := card_Ut_conj hc hg x
  have h3 := hα x hx
  rw [h2] at h1
  exact lt_irrefl c (lt_of_lt_of_le h1 h3)

theorem conj_Vt_le_Wt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (hV : Vt M (LB M Q B) B Z t = Ut Q Z t) {g : G} (hg : g ∈ M)
    (hvan : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z) :
    conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  have htM : t ∈ M := hc.LB_le_M ht
  have hxM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
  have hxC : g * t * g⁻¹ ∈ Subgroup.centralizer (Z : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hw : g⁻¹ * z * g ∈ Z := by
      refine mem_conjSubgroup.mp ?_
      rw [hc.conj_Z_eq hg]
      exact hz
    have hcomm : t * (g⁻¹ * z * g) = (g⁻¹ * z * g) * t :=
      mul_inv_eq_iff_eq_mul.mp (hc.LB_centralizes_Z ht _ hw)
    calc z * (g * t * g⁻¹) = g * (g⁻¹ * z * g) * g⁻¹ * (g * t * g⁻¹) := by group
      _ = g * ((g⁻¹ * z * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * z * g)) * g⁻¹ := by rw [hcomm]
      _ = g * t * g⁻¹ * z := by group
  have hxH : g * t * g⁻¹ ∈ H0 M Z := ⟨hxM, hxC⟩
  have hUt := Ut_le_Wt_of_vanish hc (hc.Vt_le_Q t) hxH hvan
  have hEq : conjSubgroup g (Vt M (LB M Q B) B Z t) = Ut Q Z (g * t * g⁻¹) := by
    rw [Ut_conj_of_normalizes (hc.conj_Q_eq hg) (hc.conj_Z_eq hg) t, hV]
  rw [hEq]
  exact hUt

theorem IsCentrePre.mem_normalizer {Z0 R : Subgroup G} (h : IsCentrePre Z0 R Q)
    (hnorm : ∀ ρ ∈ R, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q) {r : G} (hr : r ∈ R) :
    r ∈ Subgroup.normalizer (Z0 : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hz' : z ∈ Z0 := hz
  have hrz : r * z * r⁻¹ ∈ Z0 := by
    refine (h.mem_iff (x := r * z * r⁻¹)).mpr
      ⟨R.mul_mem (R.mul_mem hr (h.le hz')) (R.inv_mem hr), fun ρ hρ => ?_⟩
    have hσ : r⁻¹ * ρ * r ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hr) hρ) hr
    have hq : ⁅z, r⁻¹ * ρ * r⁆ ∈ Q := h.comm_mem hz' hσ
    have e : ⁅r * z * r⁻¹, ρ⁆ = r * ⁅z, r⁻¹ * ρ * r⁆ * r⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hnorm r hr _ hq
  exact hrz

theorem Ctx.Q_le_centre (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {Z0 : Subgroup G}
    (h : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : Q ≤ Z0 :=
  h.Q_le (hc.Q_le_Rt ht) fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy

theorem Ctx.centre_le_M (hc : Ctx M Q Z B) (t : G) {Z0 : Subgroup G}
    (h : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : Z0 ≤ M :=
  h.le.trans (hc.Rt_le_M t)

end CFSG.RankThree.GF2n.Stroth80
