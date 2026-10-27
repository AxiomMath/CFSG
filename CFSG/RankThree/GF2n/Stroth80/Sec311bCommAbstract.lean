module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

theorem sec311b_conj_one {G : Type} [Group G] (L : Subgroup G) :
    conjSubgroup (1 : G) L = L := by
  ext x
  simp [mem_conjSubgroup]

theorem sec311b_comm_mem_inf {G : Type} [Group G] {N K : Subgroup G} {l n : G} (hl : l ∈ K)
    (hn : n ∈ N) (hlN : l * n * l⁻¹ ∈ N) (hNK : ∀ m ∈ N, ∀ x ∈ K, m * x * m⁻¹ ∈ K) :
    ⁅l, n⁆ ∈ K ⊓ N := by
  refine ⟨?_, ?_⟩
  · have e : ⁅l, n⁆ = l * (n * l⁻¹ * n⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem hl (hNK n hn _ (K.inv_mem hl))
  · have e : ⁅l, n⁆ = (l * n * l⁻¹) * n⁻¹ := commutatorElement_def l n
    rw [e]
    exact N.mul_mem hlN (N.inv_mem hn)

theorem sec311b_sup_conj {G : Type} [Group G] {H K₁ K₂ : Subgroup G} {n : G}
    (h₁ : ∀ x ∈ K₁, n * x * n⁻¹ ∈ H) (h₂ : ∀ x ∈ K₂, n * x * n⁻¹ ∈ H) :
    ∀ x ∈ K₁ ⊔ K₂, n * x * n⁻¹ ∈ H := by
  have hle : K₁ ⊔ K₂ ≤ H.comap (MulAut.conj n).toMonoidHom :=
    sup_le (fun x hx => h₁ x hx) (fun x hx => h₂ x hx)
  intro x hx
  exact hle hx

theorem sec311b_le_normalizer {G : Type} [Group G] {K P : Subgroup G}
    (h : ∀ g ∈ K, ∀ x ∈ P, g * x * g⁻¹ ∈ P) : K ≤ Subgroup.normalizer (P : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h g hg y hy, fun hy => ?_⟩
  have h' := h g⁻¹ (K.inv_mem hg) _ hy
  have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  rw [e] at h'
  exact h'

theorem sec311b_exists_left {G : Type} [Group G] {R T : Subgroup G}
    (hTR : ∀ s ∈ R, ∀ x ∈ T, s * x * s⁻¹ ∈ T) (Y : Set G) :
    ∃ S : Subgroup G, ∀ a, a ∈ S ↔ a ∈ R ∧ ∀ y ∈ Y, ⁅a, y⁆ ∈ T := by
  refine ⟨{ carrier := {a | a ∈ R ∧ ∀ y ∈ Y, ⁅a, y⁆ ∈ T}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun a => Iff.rfl⟩
  · intro a b ha hb
    refine ⟨R.mul_mem ha.1 hb.1, fun y hy => ?_⟩
    have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact T.mul_mem (hTR a ha.1 _ (hb.2 y hy)) (ha.2 y hy)
  · refine ⟨R.one_mem, fun y _ => ?_⟩
    rw [commutatorElement_one_left]
    exact T.one_mem
  · intro a ha
    refine ⟨R.inv_mem ha.1, fun y hy => ?_⟩
    have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h' := hTR a⁻¹ (R.inv_mem ha.1) _ (T.inv_mem (ha.2 y hy))
    rw [inv_inv] at h'
    exact h'

theorem sec311b_exists_right {G : Type} [Group G] {R T : Subgroup G}
    (hTR : ∀ s ∈ R, ∀ x ∈ T, s * x * s⁻¹ ∈ T) (X : Set G) :
    ∃ S : Subgroup G, ∀ b, b ∈ S ↔ b ∈ R ∧ ∀ x ∈ X, ⁅x, b⁆ ∈ T := by
  refine ⟨{ carrier := {b | b ∈ R ∧ ∀ x ∈ X, ⁅x, b⁆ ∈ T}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun b => Iff.rfl⟩
  · intro b c hb hc
    refine ⟨R.mul_mem hb.1 hc.1, fun x hx => ?_⟩
    have e : ⁅x, b * c⁆ = ⁅x, b⁆ * (b * ⁅x, c⁆ * b⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact T.mul_mem (hb.2 x hx) (hTR b hb.1 _ (hc.2 x hx))
  · refine ⟨R.one_mem, fun x _ => ?_⟩
    rw [commutatorElement_one_right]
    exact T.one_mem
  · intro b hb
    refine ⟨R.inv_mem hb.1, fun x hx => ?_⟩
    have e : ⁅x, b⁻¹⁆ = b⁻¹ * ⁅x, b⁆⁻¹ * b := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h' := hTR b⁻¹ (R.inv_mem hb.1) _ (T.inv_mem (hb.2 x hx))
    rw [inv_inv] at h'
    exact h'

theorem sec311b_L'_le_R {G : Type} [Group G] {R L L' : Subgroup G} {r : G} (hLR : L ≤ R)
    (hr : r ∈ R) (hL' : L' = conjSubgroup r L) : L' ≤ R := by
  intro x hx
  rw [hL', mem_conjSubgroup] at hx
  have e : x = r * (r⁻¹ * x * r) * r⁻¹ := by group
  rw [e]
  exact R.mul_mem (R.mul_mem hr (hLR hx)) (R.inv_mem hr)

theorem sec311b_comm_L' {G : Type} [Group G] {R Q L L' : Subgroup G} {r : G}
    (hQR : ∀ s ∈ R, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q) (hLL : ⁅L, L⁆ ≤ Q) (hr : r ∈ R)
    (hL' : L' = conjSubgroup r L) : ⁅L', L'⁆ ≤ Q := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [hL', mem_conjSubgroup] at ha hb
  have e : ⁅a, b⁆ = r * ⁅r⁻¹ * a * r, r⁻¹ * b * r⁆ * r⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact hQR r hr _ (Subgroup.commutator_le.mp hLL _ ha _ hb)

theorem sec311b_Q_le_T {G : Type} [Group G] {R Q L T : Subgroup G}
    (hQR : ∀ s ∈ R, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q) (hQL : Q ≤ L)
    (hT : ∀ x, x ∈ T ↔ x ∈ L ∧ ∀ s ∈ R, ⁅s, x⁆ ∈ Q) : Q ≤ T := by
  intro q hq
  refine (hT q).mpr ⟨hQL hq, fun s hs => ?_⟩
  have e : ⁅s, q⁆ = (s * q * s⁻¹) * q⁻¹ := commutatorElement_def s q
  rw [e]
  exact Q.mul_mem (hQR s hs q hq) (Q.inv_mem hq)

theorem sec311b_T_invariant {G : Type} [Group G] {R Q L T : Subgroup G}
    (hQT : Q ≤ T) (hT : ∀ x, x ∈ T ↔ x ∈ L ∧ ∀ s ∈ R, ⁅s, x⁆ ∈ Q) :
    ∀ s ∈ R, ∀ x ∈ T, s * x * s⁻¹ ∈ T := by
  intro s hs x hx
  have hc : ⁅s, x⁆ ∈ Q := ((hT x).mp hx).2 s hs
  have e : s * x * s⁻¹ = ⁅s, x⁆ * x := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact T.mul_mem (hQT hc) hx

theorem sec311b_R_le_sup {G : Type} [Group G] {R N L L' : Subgroup G}
    (hgen : R ≤ N ⊔ (L ⊔ L'))
    (hN : N = ⨆ (h : G) (_ : h ∈ R), conjSubgroup h L ⊓ N)
    (hNL : ∀ n ∈ N, ∀ x ∈ L, n * x * n⁻¹ ∈ L)
    (hNL' : ∀ n ∈ N, ∀ x ∈ L', n * x * n⁻¹ ∈ L') :
    R ≤ L ⊔ L' := by
  have hNH : N ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup G) : Set G) := by
    apply sec311b_le_normalizer
    intro n hn
    apply sec311b_sup_conj
    · intro x hx
      exact (le_sup_left : L ≤ L ⊔ L') (hNL n hn x hx)
    · intro x hx
      exact (le_sup_right : L' ≤ L ⊔ L') (hNL' n hn x hx)
  have hLH : L ⊔ L' ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  have hNLH : N ⊔ (L ⊔ L') ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup G) : Set G) :=
    sup_le hNH hLH
  have hconj : ∀ h ∈ R, conjSubgroup h L ≤ L ⊔ L' := by
    intro h hh x hx
    refine (Subgroup.mem_normalizer_iff.mp (hNLH (hgen (R.inv_mem hh))) x).mpr ?_
    rw [inv_inv]
    exact (le_sup_left : L ≤ L ⊔ L') (mem_conjSubgroup.mp hx)
  have hNle : N ≤ L ⊔ L' :=
    hN.le.trans (iSup₂_le fun h hh => inf_le_left.trans (hconj h hh))
  exact hgen.trans (sup_le hNle le_rfl)

theorem sec311b_P_normal {G : Type} [Group G] {R N L L' : Subgroup G}
    (hRH : R ≤ L ⊔ L') (hLR : L ≤ R) (hL'R : L' ≤ R)
    (hNnorm : ∀ s ∈ R, ∀ x ∈ N, s * x * s⁻¹ ∈ N)
    (hNL : ∀ n ∈ N, ∀ x ∈ L, n * x * n⁻¹ ∈ L)
    (hNL' : ∀ n ∈ N, ∀ x ∈ L', n * x * n⁻¹ ∈ L') :
    ∀ s ∈ R, ∀ x ∈ (L ⊓ N) ⊔ (L' ⊓ N), s * x * s⁻¹ ∈ (L ⊓ N) ⊔ (L' ⊓ N) := by
  have hLP : ∀ g ∈ L, ∀ x ∈ (L ⊓ N) ⊔ (L' ⊓ N), g * x * g⁻¹ ∈ (L ⊓ N) ⊔ (L' ⊓ N) := by
    intro g hg
    apply sec311b_sup_conj
    · intro x hx
      have hm : g * x * g⁻¹ ∈ L ⊓ N :=
        ⟨L.mul_mem (L.mul_mem hg hx.1) (L.inv_mem hg), hNnorm g (hLR hg) x hx.2⟩
      exact (le_sup_left : L ⊓ N ≤ (L ⊓ N) ⊔ (L' ⊓ N)) hm
    · intro x hx
      have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by
        simp only [commutatorElement_def]; group
      have hc : ⁅g, x⁆ ∈ L ⊓ N :=
        sec311b_comm_mem_inf hg hx.2 (hNnorm g (hLR hg) x hx.2) hNL
      rw [e]
      exact ((L ⊓ N) ⊔ (L' ⊓ N)).mul_mem ((le_sup_left : L ⊓ N ≤ (L ⊓ N) ⊔ (L' ⊓ N)) hc)
        ((le_sup_right : L' ⊓ N ≤ (L ⊓ N) ⊔ (L' ⊓ N)) hx)
  have hL'P : ∀ g ∈ L', ∀ x ∈ (L ⊓ N) ⊔ (L' ⊓ N), g * x * g⁻¹ ∈ (L ⊓ N) ⊔ (L' ⊓ N) := by
    intro g hg
    apply sec311b_sup_conj
    · intro x hx
      have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by
        simp only [commutatorElement_def]; group
      have hc : ⁅g, x⁆ ∈ L' ⊓ N :=
        sec311b_comm_mem_inf hg hx.2 (hNnorm g (hL'R hg) x hx.2) hNL'
      rw [e]
      exact ((L ⊓ N) ⊔ (L' ⊓ N)).mul_mem ((le_sup_right : L' ⊓ N ≤ (L ⊓ N) ⊔ (L' ⊓ N)) hc)
        ((le_sup_left : L ⊓ N ≤ (L ⊓ N) ⊔ (L' ⊓ N)) hx)
    · intro x hx
      have hm : g * x * g⁻¹ ∈ L' ⊓ N :=
        ⟨L'.mul_mem (L'.mul_mem hg hx.1) (L'.inv_mem hg), hNnorm g (hL'R hg) x hx.2⟩
      exact (le_sup_right : L' ⊓ N ≤ (L ⊓ N) ⊔ (L' ⊓ N)) hm
  have hRP : R ≤ Subgroup.normalizer (((L ⊓ N) ⊔ (L' ⊓ N) : Subgroup G) : Set G) :=
    hRH.trans (sup_le (sec311b_le_normalizer hLP) (sec311b_le_normalizer hL'P))
  intro s hs x hx
  exact (Subgroup.mem_normalizer_iff.mp (hRP hs) x).mp hx

theorem sec311b_comm_mem_P {G : Type} [Group G] {R N L L' : Subgroup G}
    (hRH : R ≤ L ⊔ L') (hLR : L ≤ R) (hL'R : L' ≤ R)
    (hNnorm : ∀ s ∈ R, ∀ x ∈ N, s * x * s⁻¹ ∈ N)
    (hNL : ∀ n ∈ N, ∀ x ∈ L, n * x * n⁻¹ ∈ L)
    (hNL' : ∀ n ∈ N, ∀ x ∈ L', n * x * n⁻¹ ∈ L')
    (hPR : ∀ s ∈ R, ∀ x ∈ (L ⊓ N) ⊔ (L' ⊓ N), s * x * s⁻¹ ∈ (L ⊓ N) ⊔ (L' ⊓ N)) :
    ∀ s ∈ R, ∀ y ∈ N, ⁅s, y⁆ ∈ (L ⊓ N) ⊔ (L' ⊓ N) := by
  obtain ⟨S, hS⟩ := sec311b_exists_left hPR (N : Set G)
  have hLS : L ≤ S := by
    intro l hl
    refine (hS l).mpr ⟨hLR hl, fun y hy => ?_⟩
    have hc : ⁅l, y⁆ ∈ L ⊓ N := sec311b_comm_mem_inf hl hy (hNnorm l (hLR hl) y hy) hNL
    exact (le_sup_left : L ⊓ N ≤ (L ⊓ N) ⊔ (L' ⊓ N)) hc
  have hL'S : L' ≤ S := by
    intro l hl
    refine (hS l).mpr ⟨hL'R hl, fun y hy => ?_⟩
    have hc : ⁅l, y⁆ ∈ L' ⊓ N := sec311b_comm_mem_inf hl hy (hNnorm l (hL'R hl) y hy) hNL'
    exact (le_sup_right : L' ⊓ N ≤ (L ⊓ N) ⊔ (L' ⊓ N)) hc
  have hRS : R ≤ S := hRH.trans (sup_le hLS hL'S)
  intro s hs y hy
  exact ((hS s).mp (hRS hs)).2 y hy

theorem sec311b_N_le_P {G : Type} [Group G] {R N L L' : Subgroup G}
    (hN : N = ⨆ (h : G) (_ : h ∈ R), conjSubgroup h L ⊓ N)
    (hNnorm : ∀ s ∈ R, ∀ x ∈ N, s * x * s⁻¹ ∈ N)
    (hcomm : ∀ s ∈ R, ∀ y ∈ N, ⁅s, y⁆ ∈ (L ⊓ N) ⊔ (L' ⊓ N)) :
    N ≤ (L ⊓ N) ⊔ (L' ⊓ N) := by
  refine hN.le.trans (iSup₂_le fun h hh y hy => ?_)
  have hyL : h⁻¹ * y * h ∈ L := mem_conjSubgroup.mp hy.1
  have hyN : h⁻¹ * y * h ∈ N := by
    have h1 := hNnorm h⁻¹ (R.inv_mem hh) y hy.2
    rwa [inv_inv] at h1
  have hz : h⁻¹ * y * h ∈ L ⊓ N := ⟨hyL, hyN⟩
  have e : y = ⁅h, h⁻¹ * y * h⁆ * (h⁻¹ * y * h) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact ((L ⊓ N) ⊔ (L' ⊓ N)).mul_mem (hcomm h hh _ hyN)
    ((le_sup_left : L ⊓ N ≤ (L ⊓ N) ⊔ (L' ⊓ N)) hz)

theorem sec311bComm_abstract {G : Type} [Group G] {Q R N L L' T : Subgroup G} {r : G}
    (hQR : ∀ s ∈ R, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q) (hQL : Q ≤ L)
    (hNR : N ≤ R) (hLR : L ≤ R) (hr : r ∈ R) (hL' : L' = conjSubgroup r L)
    (hNnorm : ∀ s ∈ R, ∀ x ∈ N, s * x * s⁻¹ ∈ N)
    (hNconj : ∀ h ∈ R, ∀ n ∈ N, ∀ x ∈ conjSubgroup h L, n * x * n⁻¹ ∈ conjSubgroup h L)
    (hLL : ⁅L, L⁆ ≤ Q)
    (hN : N = ⨆ (h : G) (_ : h ∈ R), conjSubgroup h L ⊓ N)
    (hgen : R ≤ N ⊔ (L ⊔ L'))
    (hT : ∀ x, x ∈ T ↔ x ∈ L ∧ ∀ s ∈ R, ⁅s, x⁆ ∈ Q) :
    ⁅N, N⁆ ≤ T := by
  have hL'R : L' ≤ R := sec311b_L'_le_R hLR hr hL'
  have hNL : ∀ n ∈ N, ∀ x ∈ L, n * x * n⁻¹ ∈ L := by
    intro n hn x hx
    have hx1 : x ∈ conjSubgroup (1 : G) L := by
      rw [sec311b_conj_one]
      exact hx
    have h1 := hNconj 1 R.one_mem n hn x hx1
    rwa [sec311b_conj_one] at h1
  have hNL' : ∀ n ∈ N, ∀ x ∈ L', n * x * n⁻¹ ∈ L' := by
    intro n hn x hx
    rw [hL'] at hx ⊢
    exact hNconj r hr n hn x hx
  have hRH : R ≤ L ⊔ L' := sec311b_R_le_sup hgen hN hNL hNL'
  have hQT : Q ≤ T := sec311b_Q_le_T hQR hQL hT
  have hL'Q : ⁅L', L'⁆ ≤ Q := sec311b_comm_L' hQR hLL hr hL'
  have hTR : ∀ s ∈ R, ∀ x ∈ T, s * x * s⁻¹ ∈ T := sec311b_T_invariant hQT hT
  have hPR := sec311b_P_normal hRH hLR hL'R hNnorm hNL hNL'
  have hcomm := sec311b_comm_mem_P hRH hLR hL'R hNnorm hNL hNL' hPR
  have hNP : N ≤ (L ⊓ N) ⊔ (L' ⊓ N) := sec311b_N_le_P hN hNnorm hcomm
  have hY : ∀ x, x ∈ L → x ∈ L' → x ∈ T := by
    intro x hxL hxL'
    refine (hT x).mpr ⟨hxL, fun s hs => ?_⟩
    obtain ⟨S, hS⟩ := sec311b_exists_left hQR ({x} : Set G)
    have hLS : L ≤ S := by
      intro l hl
      refine (hS l).mpr ⟨hLR hl, fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.mp hy]
      exact Subgroup.commutator_le.mp hLL l hl x hxL
    have hL'S : L' ≤ S := by
      intro l hl
      refine (hS l).mpr ⟨hL'R hl, fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.mp hy]
      exact Subgroup.commutator_le.mp hL'Q l hl x hxL'
    have hRS : R ≤ S := hRH.trans (sup_le hLS hL'S)
    exact ((hS s).mp (hRS hs)).2 x (Set.mem_singleton x)
  have hAA : ∀ a ∈ L ⊓ N, ∀ b ∈ L ⊓ N, ⁅a, b⁆ ∈ T := fun a ha b hb =>
    hQT (Subgroup.commutator_le.mp hLL a ha.1 b hb.1)
  have hBB : ∀ a ∈ L' ⊓ N, ∀ b ∈ L' ⊓ N, ⁅a, b⁆ ∈ T := fun a ha b hb =>
    hQT (Subgroup.commutator_le.mp hL'Q a ha.1 b hb.1)
  have hAB : ∀ a ∈ L ⊓ N, ∀ b ∈ L' ⊓ N, ⁅a, b⁆ ∈ T := by
    intro a ha b hb
    have hL1 : ⁅a, b⁆ ∈ L := by
      have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact L.mul_mem ha.1 (hNL b hb.2 a⁻¹ (L.inv_mem ha.1))
    have hL2 : ⁅a, b⁆ ∈ L' := by
      have e : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := commutatorElement_def a b
      rw [e]
      exact L'.mul_mem (hNL' a ha.2 b hb.1) (L'.inv_mem hb.1)
    exact hY _ hL1 hL2
  have hBA : ∀ a ∈ L' ⊓ N, ∀ b ∈ L ⊓ N, ⁅a, b⁆ ∈ T := by
    intro a ha b hb
    have h1 := T.inv_mem (hAB b hb a ha)
    rwa [commutatorElement_inv] at h1
  have hAll : ∀ a, (a ∈ L ⊓ N ∨ a ∈ L' ⊓ N) → ∀ b, (b ∈ L ⊓ N ∨ b ∈ L' ⊓ N) →
      ⁅a, b⁆ ∈ T := by
    rintro a (ha | ha) b (hb | hb)
    · exact hAA a ha b hb
    · exact hAB a ha b hb
    · exact hBA a ha b hb
    · exact hBB a ha b hb
  have hB : ∀ b, (b ∈ L ⊓ N ∨ b ∈ L' ⊓ N) → ∀ a ∈ (L ⊓ N) ⊔ (L' ⊓ N), ⁅a, b⁆ ∈ T := by
    intro b hb
    obtain ⟨S, hS⟩ := sec311b_exists_left hTR ({b} : Set G)
    have hgenS : ∀ a, (a ∈ L ⊓ N ∨ a ∈ L' ⊓ N) → a ∈ S := by
      intro a ha
      refine (hS a).mpr ⟨?_, fun y hy => ?_⟩
      · rcases ha with ha | ha
        · exact hLR ha.1
        · exact hL'R ha.1
      · rw [Set.mem_singleton_iff.mp hy]
        exact hAll a ha b hb
    have hPS : (L ⊓ N) ⊔ (L' ⊓ N) ≤ S :=
      sup_le (fun a ha => hgenS a (Or.inl ha)) (fun a ha => hgenS a (Or.inr ha))
    intro a ha
    exact ((hS a).mp (hPS ha)).2 b (Set.mem_singleton b)
  have hC : ∀ a ∈ (L ⊓ N) ⊔ (L' ⊓ N), ∀ b ∈ (L ⊓ N) ⊔ (L' ⊓ N), ⁅a, b⁆ ∈ T := by
    intro a ha
    obtain ⟨S, hS⟩ := sec311b_exists_right hTR ({a} : Set G)
    have hPS : (L ⊓ N) ⊔ (L' ⊓ N) ≤ S := by
      have key : ∀ b, (b ∈ L ⊓ N ∨ b ∈ L' ⊓ N) → b ∈ S := by
        intro b hb
        refine (hS b).mpr ⟨?_, fun x hx => ?_⟩
        · rcases hb with hb | hb <;> exact hNR hb.2
        · rw [Set.mem_singleton_iff.mp hx]
          exact hB b hb a ha
      exact sup_le (fun b hb => key b (Or.inl hb)) (fun b hb => key b (Or.inr hb))
    intro b hb
    exact ((hS b).mp (hPS hb)).2 a (Set.mem_singleton a)
  exact Subgroup.commutator_le.mpr fun a ha b hb => hC a (hNP ha) b (hNP hb)

end CFSG.RankThree.GF2n.Stroth80
