module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Six_conj_wSub_le_M (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    {g : G} (hg : s15SixAdm D V g) :
    conjSubgroup (wSub V₀ V hV L) g ≤ conjSubgroup V g ∧ conjSubgroup (wSub V₀ V hV L) g ≤ D.M :=
  ⟨E3.conjSubgroup_mono_left g (preTil_le V₀ V hV _),
    (E3.conjSubgroup_mono_left g (preTil_le V₀ V hV _)).trans hg.2⟩

theorem s15_Six_mem_normalizer_of_comm_v1 (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {w x : G} (hw : w ∈ wSub V₀ V hV L)
    (hwV₁ : w ∉ v1Sub D.M V₀ V hV L) (hx : x ∈ D.M)
    (hc : x * w * x⁻¹ * w⁻¹ ∈ v1Sub D.M V₀ V hV L) : x ∈ normalizer (wSub V₀ V hV L : Set G) := by
  by_contra hxn
  have hxn' : x ∉ nBar D.M V₀ V hV L := by
    intro hmem
    rw [← inf_normalizer_wSub_eq_nBar D h hV] at hmem
    exact hxn (Subgroup.mem_inf.1 hmem).2
  exact hwV₁ (mem_v1Sub_of_commutator_mem D h hV hx hxn' (Subgroup.mem_sup_left hw) hc)

theorem s15_Six_two_le_mQuot_ker (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {g : G} (hg : s15SixAdm D V g)
    (hδ : delta15 D.M V₀ V hV L + 2 ≤ gamma15 D.M V₀ V hV L)
    (hW : ¬ wSub V₀ V hV L ≤ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) :
    2 ≤ E3.mQuot (conjSubgroup (wSub V₀ V hV L) g)
      (s15SixKer (conjSubgroup (wSub V₀ V hV L) g)
        ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G) (v1Sub D.M V₀ V hV L)) := by
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hV₁V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  obtain ⟨hBA, hBM⟩ := s15_Six_conj_wSub_le_M (V₀ := V₀) (L := L) D hV hg
  have hB2 : IsPGroup 2 (conjSubgroup (wSub V₀ V hV L) g) :=
    E3.isPGroup_conjSubgroup (hV.isPGroup.to_le hWV) g
  obtain ⟨w, hwW, hwN, hwV₁⟩ := s15_Six_exists_not_mem (W := wSub V₀ V hV L)
    (H₁ := normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G))
    (H₂ := v1Sub D.M V₀ V hV L) hW (s15_Six_not_wSub_le_v1Sub D h hV hL)
  have h1 := s15_Six_le_mQuot_conj D h hV (hg.1 (hWV hwW)) hwN
  have horb : ∀ e ∈ s15SixKer (conjSubgroup (wSub V₀ V hV L) g) ({w} : Set G)
      (v1Sub D.M V₀ V hV L), w⁻¹ * (e⁻¹ * w * e) ∈
        v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L := by
    intro e he
    have hei := Subgroup.inv_mem _ he
    have hc : e⁻¹ * w * e * w⁻¹ ∈ v1Sub D.M V₀ V hV L := by
      have := hei.2.2 w rfl
      rwa [inv_inv] at this
    have hec : e * w * e⁻¹ * w⁻¹ ∈ v1Sub D.M V₀ V hV L := he.2.2 w rfl
    have hen : e ∈ normalizer (wSub V₀ V hV L : Set G) :=
      s15_Six_mem_normalizer_of_comm_v1 D h hV hwW hwV₁ (hBM he.1) hec
    exact s15_Tools_orbit_mem D h.hyp125 hV (Subgroup.inv_mem _ hen) hwW hc
  have h2 := s15_Tools_mQuot_inf_centralizer_le_add (B := conjSubgroup (wSub V₀ V hV L) g)
    (D := s15SixKer (conjSubgroup (wSub V₀ V hV L) g) ({w} : Set G) (v1Sub D.M V₀ V hV L))
    (F := v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) (v := w) hB2 (fun x hx => hx.1)
    (hV.isPGroup.to_le (inf_le_left.trans hV₁V)) horb
  have h3 : E3.mQuot (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) ⊥ = delta15 D.M V₀ V hV L :=
    s15_FiveTen_mQuot_bot_eq_rk _
  have hle : s15SixKer (conjSubgroup (wSub V₀ V hV L) g)
      ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G) (v1Sub D.M V₀ V hV L) ≤
      s15SixKer (conjSubgroup (wSub V₀ V hV L) g) ({w} : Set G) (v1Sub D.M V₀ V hV L) := by
    intro x hx
    refine ⟨hx.1, hx.2.1, fun d hd => hx.2.2 d ?_⟩
    rw [Set.mem_singleton_iff] at hd
    subst hd
    exact Subgroup.mem_sup_left hwW
  have h4 := E3.mQuot_mono (V := conjSubgroup (wSub V₀ V hV L) g) hle
  omega

theorem s15_Six_comm_cancel {V : Subgroup G} (hV : IsElemAbelian 2 V) {b x y : G}
    (hb : b ∈ normalizer (V : Set G)) (hx : x ∈ V) (hy : y ∈ V)
    (h : b * y * b⁻¹ * y⁻¹ = b * x * b⁻¹ * x⁻¹) :
    b * (y * x⁻¹) * b⁻¹ * (y * x⁻¹)⁻¹ = 1 := by
  have hX : b * x * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hb x).1 hx
  have hc : ∀ p ∈ V, ∀ q ∈ V, Commute p q := fun p hp q hq => B2F.isElemAbelian_comm hV hp hq
  have hyz : y * (b * x * b⁻¹)⁻¹ * x * y⁻¹ = (b * x * b⁻¹)⁻¹ * x := by
    have hc1 : Commute y ((b * x * b⁻¹)⁻¹ * x) :=
      Commute.mul_right (Commute.inv_right (hc y hy _ hX)) (hc y hy x hx)
    calc y * (b * x * b⁻¹)⁻¹ * x * y⁻¹ = (y * ((b * x * b⁻¹)⁻¹ * x)) * y⁻¹ := by group
      _ = ((b * x * b⁻¹)⁻¹ * x) * y * y⁻¹ := by rw [hc1.eq]
      _ = (b * x * b⁻¹)⁻¹ * x := by group
  have hxX : x⁻¹ * (b * x * b⁻¹)⁻¹ = (b * x * b⁻¹)⁻¹ * x⁻¹ :=
    ((hc x hx _ hX).inv_inv).eq
  calc b * (y * x⁻¹) * b⁻¹ * (y * x⁻¹)⁻¹
      = (b * y * b⁻¹ * y⁻¹) * (y * (b * x * b⁻¹)⁻¹ * x * y⁻¹) := by group
    _ = (b * x * b⁻¹ * x⁻¹) * ((b * x * b⁻¹)⁻¹ * x) := by rw [h, hyz]
    _ = (b * x * b⁻¹) * (x⁻¹ * (b * x * b⁻¹)⁻¹) * x := by group
    _ = 1 := by rw [hxX]; group

theorem s15_Six_comm_mem_v1Sub (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {g : G} (hg : s15SixAdm D V g) {b b' x : G}
    (hb : b ∈ conjSubgroup (wSub V₀ V hV L) g) (hbN : b ∉ normalizer (wSub V₀ V hV L : Set G))
    (hb' : b' ∈ conjSubgroup (wSub V₀ V hV L) g)
    (hb'N : b' ∈ normalizer (wSub V₀ V hV L : Set G)) (hx : x ∈ wSub V₀ V hV L) :
    b' * x * b'⁻¹ * x⁻¹ ∈ v1Sub D.M V₀ V hV L := by
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  obtain ⟨hBA, hBM⟩ := s15_Six_conj_wSub_le_M (V₀ := V₀) (L := L) D hV hg
  have hA := E3.isElemAbelian_conjSubgroup hV g
  have hN := h.hyp125.pairFacts.le_normalizer
  have hu := s15_Six_comm_mem_inf hN hg.1 hg.2 (hWV hx) (hBA hb)
  have hbb' : b' * b = b * b' := B2F.isElemAbelian_comm hA (hBA hb') (hBA hb)
  have hb'u : b' * (b * x * b⁻¹ * x⁻¹) = (b * x * b⁻¹ * x⁻¹) * b' :=
    B2F.isElemAbelian_comm hA (hBA hb') (Subgroup.mem_inf.1 hu).2
  have hyW : b' * x * b'⁻¹ ∈ wSub V₀ V hV L := (Subgroup.mem_normalizer_iff.1 hb'N x).1 hx
  have hcomm : b * (b' * x * b'⁻¹) * b⁻¹ * (b' * x * b'⁻¹)⁻¹ = b * x * b⁻¹ * x⁻¹ := by
    have h1 : b' * b * b'⁻¹ = b := by rw [hbb']; group
    have e : b' * (b * x * b⁻¹ * x⁻¹) * b'⁻¹ =
        b * (b' * x * b'⁻¹) * b⁻¹ * (b' * x * b'⁻¹)⁻¹ := by
      calc b' * (b * x * b⁻¹ * x⁻¹) * b'⁻¹
          = (b' * b * b'⁻¹) * (b' * x * b'⁻¹) * (b' * b * b'⁻¹)⁻¹ * (b' * x * b'⁻¹)⁻¹ := by group
        _ = _ := by rw [h1]
    rw [← e, hb'u]
    group
  have hz := s15_Six_comm_cancel hV (hN (hBM hb)) (hWV hx) (hWV hyW) hcomm
  have hbn' : b ∉ nBar D.M V₀ V hV L := by
    intro hmem
    rw [← inf_normalizer_wSub_eq_nBar D h hV] at hmem
    exact hbN (Subgroup.mem_inf.1 hmem).2
  refine mem_v1Sub_of_commutator_mem D h hV (hBM hb) hbn'
    (Subgroup.mem_sup_left ((wSub V₀ V hV L).mul_mem hyW ((wSub V₀ V hV L).inv_mem hx))) ?_
  rw [hz]
  exact Subgroup.one_mem _

theorem s15_Six_le_normalizer_of_ker (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {g : G} (hg : s15SixAdm D V g)
    (hs : s15 D.M V₀ V hV L ≤ 3)
    (hker : 2 ≤ E3.mQuot (conjSubgroup (wSub V₀ V hV L) g)
      (s15SixKer (conjSubgroup (wSub V₀ V hV L) g)
        ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G) (v1Sub D.M V₀ V hV L))) :
    conjSubgroup (wSub V₀ V hV L) g ≤ normalizer (wSub V₀ V hV L : Set G) := by
  by_contra hBN
  obtain ⟨b, hbB, hbN⟩ := SetLike.not_le_iff_exists.1 hBN
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hV₁V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  obtain ⟨hBA, hBM⟩ := s15_Six_conj_wSub_le_M (V₀ := V₀) (L := L) D hV hg
  have hB2 : IsPGroup 2 (conjSubgroup (wSub V₀ V hV L) g) :=
    E3.isPGroup_conjSubgroup (hV.isPGroup.to_le hWV) g
  have hN₁ : ∀ x ∈ D.M, x ∈ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    fun x hx => s15_Infra_le_normalizer_v1Sub h.hyp125 hV hx
  have hle : conjSubgroup (wSub V₀ V hV L) g ⊓ normalizer (wSub V₀ V hV L : Set G) ≤
      s15SixKer (conjSubgroup (wSub V₀ V hV L) g)
        ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G)
        (v1Sub D.M V₀ V hV L) := by
    intro b' hb'
    obtain ⟨hb'B, hb'N⟩ := Subgroup.mem_inf.1 hb'
    refine ⟨hb'B, hN₁ _ (hBM hb'B), fun d hd => ?_⟩
    obtain ⟨x, hx, v, hv, rfl⟩ :=
      s15_Six_mem_sup_of_commute (fun x hx y hy => B2F.isElemAbelian_comm hV (hWV hx) (hV₁V hy)) hd
    have hxM : x ∈ D.M := h.hyp125.pairFacts.le_M (hWV hx)
    have h1 := s15_Six_comm_mem_v1Sub D h hV hg hbB hbN hb'B hb'N hx
    have h2 : b' * v * b'⁻¹ * v⁻¹ ∈ v1Sub D.M V₀ V hV L :=
      (v1Sub D.M V₀ V hV L).mul_mem
        ((Subgroup.mem_normalizer_iff.1 (hN₁ _ (hBM hb'B)) v).1 hv)
        ((v1Sub D.M V₀ V hV L).inv_mem hv)
    have h3 : x * (b' * v * b'⁻¹ * v⁻¹) * x⁻¹ ∈ v1Sub D.M V₀ V hV L :=
      (Subgroup.mem_normalizer_iff.1 (hN₁ _ hxM) _).1 h2
    have e : b' * (x * v) * b'⁻¹ * (x * v)⁻¹ =
        (b' * x * b'⁻¹ * x⁻¹) * (x * (b' * v * b'⁻¹ * v⁻¹) * x⁻¹) := by group
    rw [e]
    exact (v1Sub D.M V₀ V hV L).mul_mem h1 h3
  have h1 := E3.mQuot_mono (V := conjSubgroup (wSub V₀ V hV L) g) hle
  have h2 := s15_Six_mQuot_inf_normalizer_le_one D h hV hBM hB2 hs
  omega

theorem s15_Six_inf_conj_wSub_eq_bot (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {g : G} (hg : g ∉ D.M) :
    wSub V₀ V hV L ⊓ conjSubgroup (wSub V₀ V hV L) g = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf le_sup_left (E3.conjSubgroup_mono_left g le_sup_left)).trans
    (s15_Six_inf_conj_eq_bot D h hV hg).le)

theorem s15_Six_comm_mem_v1Sub_of_mem_axis (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) {g : G} (hgM : g ∉ D.M)
    (hg : s15SixAdm D V g)
    (hBN : conjSubgroup (wSub V₀ V hV L) g ≤ normalizer (wSub V₀ V hV L : Set G)) {x k : G}
    (hx : x ∈ conjSubgroup (wSub V₀ V hV L) g)
    (hk : k ∈ (wSub V₀ V hV L ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) ⊔
      v1Sub D.M V₀ V hV L) :
    x * k * x⁻¹ * k⁻¹ ∈ v1Sub D.M V₀ V hV L := by
  have h125 := h.hyp151.hyp125
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hV₁V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h125 hV
  obtain ⟨-, hBM⟩ := s15_Six_conj_wSub_le_M (V₀ := V₀) (L := L) D hV hg
  have hN₁ : ∀ y ∈ D.M, y ∈ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    fun y hy => s15_Infra_le_normalizer_v1Sub h125 hV hy
  obtain ⟨n, hn, v, hv, rfl⟩ := s15_Six_mem_sup_of_commute
    (fun a ha c hc => B2F.isElemAbelian_comm hV (hWV (Subgroup.mem_inf.1 ha).1) (hV₁V hc)) hk
  have hnM : n ∈ D.M := h125.pairFacts.le_M (hWV (Subgroup.mem_inf.1 hn).1)
  have h1 : x * n * x⁻¹ * n⁻¹ = 1 :=
    s15_Six_comm_of_normalizers (s15_Six_inf_conj_wSub_eq_bot D h hV hgM)
      (Subgroup.mem_inf.2 ⟨hx, hBN hx⟩) hn
  have h2 : x * v * x⁻¹ * v⁻¹ ∈ v1Sub D.M V₀ V hV L :=
    (v1Sub D.M V₀ V hV L).mul_mem ((Subgroup.mem_normalizer_iff.1 (hN₁ _ (hBM hx)) v).1 hv)
      ((v1Sub D.M V₀ V hV L).inv_mem hv)
  have h3 : n * (x * v * x⁻¹ * v⁻¹) * n⁻¹ ∈ v1Sub D.M V₀ V hV L :=
    (Subgroup.mem_normalizer_iff.1 (hN₁ _ hnM) _).1 h2
  have e : x * (n * v) * x⁻¹ * (n * v)⁻¹ =
      (x * n * x⁻¹ * n⁻¹) * (n * (x * v * x⁻¹ * v⁻¹) * n⁻¹) := by group
  rw [e, h1, one_mul]
  exact h3

theorem s15_Six_mQuot_axis_eq_one (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {g : G} (hgM : g ∉ D.M) (hg : s15SixAdm D V g)
    (hs : s15 D.M V₀ V hV L ≤ 3)
    (hBN : conjSubgroup (wSub V₀ V hV L) g ≤ normalizer (wSub V₀ V hV L : Set G))
    (hker : 2 ≤ E3.mQuot (conjSubgroup (wSub V₀ V hV L) g)
      (s15SixKer (conjSubgroup (wSub V₀ V hV L) g)
        ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G) (v1Sub D.M V₀ V hV L))) :
    E3.mQuot (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L)
      ((wSub V₀ V hV L ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) ⊔
        v1Sub D.M V₀ V hV L) = 1 := by
  have h125 := h.hyp151.hyp125
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hV₁V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h125 hV
  have hWV₁ : IsPGroup 2 ↥(wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) :=
    hV.isPGroup.to_le (sup_le hWV hV₁V)
  obtain ⟨-, hBM⟩ := s15_Six_conj_wSub_le_M (V₀ := V₀) (L := L) D hV hg
  have hB2 : IsPGroup 2 (conjSubgroup (wSub V₀ V hV L) g) :=
    E3.isPGroup_conjSubgroup (hV.isPGroup.to_le hWV) g
  have hN₁ : ∀ y ∈ D.M, y ∈ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    fun y hy => s15_Infra_le_normalizer_v1Sub h125 hV hy
  have hKle : (wSub V₀ V hV L ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) ⊔
      v1Sub D.M V₀ V hV L ≤ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L :=
    sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hle1 : E3.mQuot (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L)
      ((wSub V₀ V hV L ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) ⊔
        v1Sub D.M V₀ V hV L) ≤ 1 := by
    have h1 := s15_Six_mQuot_sup_le (W := wSub V₀ V hV L) (Q := v1Sub D.M V₀ V hV L)
      (K := (wSub V₀ V hV L ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) ⊔
        v1Sub D.M V₀ V hV L) le_sup_right hWV₁
      (fun x hx y hy => B2F.isElemAbelian_comm hV (hWV hx) (hV₁V hy))
    have h2 := E3.mQuot_mono (V := wSub V₀ V hV L)
      (le_sup_left : wSub V₀ V hV L ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G) ≤
        (wSub V₀ V hV L ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) ⊔
          v1Sub D.M V₀ V hV L)
    have h3 := s15_Six_mQuot_inf_normalizer_conj_le_one D h.hyp151 hV
      (hWV.trans hg.1) (hV.isPGroup.to_le hWV) hs
    omega
  have hpos : E3.mQuot (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L)
      ((wSub V₀ V hV L ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) ⊔
        v1Sub D.M V₀ V hV L) ≠ 0 := by
    intro h0
    have hKeq := (E3.mQuot_eq_zero_iff hWV₁ hKle).1 h0
    have hBker : conjSubgroup (wSub V₀ V hV L) g ≤
        s15SixKer (conjSubgroup (wSub V₀ V hV L) g)
          ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G)
          (v1Sub D.M V₀ V hV L) := fun x hx =>
      ⟨hx, hN₁ _ (hBM hx), fun d hd =>
        s15_Six_comm_mem_v1Sub_of_mem_axis D h hV hgM hg hBN hx (by rw [hKeq]; exact hd)⟩
    have hkerB : s15SixKer (conjSubgroup (wSub V₀ V hV L) g)
        ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G)
        (v1Sub D.M V₀ V hV L) ≤ conjSubgroup (wSub V₀ V hV L) g := fun x hx => hx.1
    have h1 := (E3.mQuot_eq_zero_iff hB2 hkerB).2 (le_antisymm hkerB hBker)
    omega
  omega

theorem s15_Six_gamma_eq_three (D : Data G) (hT7 : RT7 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {g : G}
    (hgM : g ∉ D.M) (hg : s15SixAdm D V g) (hs : s15 D.M V₀ V hV L = 2)
    (hδ : delta15 D.M V₀ V hV L + 2 ≤ gamma15 D.M V₀ V hV L)
    (hW : ¬ wSub V₀ V hV L ≤ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) :
    gamma15 D.M V₀ V hV L = 3 := by
  have h151 := h.hyp151
  have h125 := h151.hyp125
  obtain ⟨hBA, hBM⟩ := s15_Six_conj_wSub_le_M (V₀ := V₀) (L := L) D hV hg
  have hker := s15_Six_two_le_mQuot_ker D h151 hV hL hg hδ hW
  have hBN := s15_Six_le_normalizer_of_ker D h151 hV hg (by omega) hker
  have hK := s15_Six_mQuot_axis_eq_one D h hV hgM hg (by omega) hBN hker
  have hN₁ : ∀ y ∈ D.M, y ∈ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    fun y hy => s15_Infra_le_normalizer_v1Sub h125 hV hy
  have hKle : (wSub V₀ V hV L ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) ⊔
      v1Sub D.M V₀ V hV L ≤ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L :=
    sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have key := hT7 V₀ V L h hL 1 (wSub V₀ V hV L) ⟨1, D.M.one_mem, (conjSubgroup_one _).symm⟩
    (conjSubgroup (wSub V₀ V hV L) g)
    (s15SixKer (conjSubgroup (wSub V₀ V hV L) g)
      ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G) (v1Sub D.M V₀ V hV L))
    ((wSub V₀ V hV L ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) ⊔
      v1Sub D.M V₀ V hV L)
    ((E3.isElemAbelian_conjSubgroup hV g).mono hBA)
    (by rw [conjSubgroup_one]; exact hBM) (fun x hx => hx.1)
    (by
      rw [conjSubgroup_one]
      intro x hx
      have hx' : x ∈ D.M ⊓ normalizer (wSub V₀ V hV L : Set G) :=
        Subgroup.mem_inf.2 ⟨hBM hx, hBN hx⟩
      rw [inf_normalizer_wSub_eq_nBar D h151 hV,
        ← inf_normalizer_wSub_sup_v1Sub_eq_nBar D h151 hV] at hx'
      exact (Subgroup.mem_inf.1 hx').2)
    (by
      intro x hx
      rw [conjSubgroup_one, conjSubgroup_one]
      exact ⟨fun hxC d hd => hxC.2.2 d hd, fun hall => ⟨hx, hN₁ _ (hBM hx), hall⟩⟩)
    (by rw [conjSubgroup_one]; exact le_sup_right)
    (by rw [conjSubgroup_one]; exact hKle)
    (by rw [conjSubgroup_one]; exact hK)
    (by
      intro x hx k hk
      rw [conjSubgroup_one]
      exact s15_Six_comm_mem_v1Sub_of_mem_axis D h hV hgM hg hBN hx hk)
    hker
  exact key.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
