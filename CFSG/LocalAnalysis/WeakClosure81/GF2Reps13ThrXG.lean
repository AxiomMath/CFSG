module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXFC
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXGT

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def s13XSupp (X : Subgroup (MulAut W)) (B : Set (Subgroup W)) : Subgroup (MulAut W) :=
  X ⊓ ⨅ (U : Subgroup W) (_ : U ∈ s13IsoComps X ∧ U ∉ B), s13KerOn X U

theorem mem_s13XSupp {X : Subgroup (MulAut W)} {B : Set (Subgroup W)} {x : MulAut W} :
    x ∈ s13XSupp X B ↔ x ∈ X ∧ ∀ U ∈ s13IsoComps X, U ∉ B → x ∈ s13KerOn X U := by
  simp only [s13XSupp, Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨hxX, hxall⟩
    exact ⟨hxX, fun U hU hUB => hxall U ⟨hU, hUB⟩⟩
  · rintro ⟨hxX, hxall⟩
    exact ⟨hxX, fun U hUP => hxall U hUP.1 hUP.2⟩

theorem s13XSupp_le {X : Subgroup (MulAut W)} {B : Set (Subgroup W)} : s13XSupp X B ≤ X :=
  inf_le_left

theorem le_s13XSupp_iff (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) {L : Subgroup (MulAut W)} (hLX : L ≤ X)
    {B : Set (Subgroup W)} : L ≤ s13XSupp X B ↔ s13Supp X L ⊆ B := by
  have hcomm_iff : ∀ U ∈ s13IsoComps X, (commSub U L = ⊥ ↔ L ≤ s13KerOn X U) := by
    intro U hU
    constructor
    · intro hcomm
      by_contra hnk
      have hUeq := (s13IsoComps_commSub_eq hW hp hp2 hX hLX hU).2 hnk
      rw [hcomm] at hUeq
      obtain ⟨U₀, hIrr, -, rfl⟩ := hU
      have hU₀le : U₀ ≤ s13IsoSum X U₀ := w16g_le_s13IsoSum_self hIrr
      have hU₀bot : U₀ = ⊥ := le_bot_iff.mp (hUeq ▸ hU₀le)
      exact hIrr.1.ne' hU₀bot
    · intro hL
      exact (s13IsoComps_commSub_eq hW hp hp2 hX hLX hU).1 hL
  constructor
  · intro hle U hU
    by_contra hUB
    have hLker : L ≤ s13KerOn X U := by
      intro x hx
      exact (mem_s13XSupp.mp (hle hx)).2 U hU.1 hUB
    exact hU.2 ((hcomm_iff U hU.1).mpr hLker)
  · intro hsub x hxL
    refine mem_s13XSupp.mpr ⟨hLX hxL, ?_⟩
    intro U hU hUB
    have hnot : U ∉ s13Supp X L := fun h => hUB (hsub h)
    have hcomm : commSub U L = ⊥ := by
      by_contra hne
      exact hnot ⟨hU, hne⟩
    exact (hcomm_iff U hU).mp hcomm hxL

theorem card_s13XSupp_singleton_le (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) {U : Subgroup W}
    (hU : U ∈ s13IsoComps X) : Nat.card ↥(s13XSupp X {U}) ≤ p := by
  obtain ⟨lam, hl⟩ := exists_coord hW hp hp2 hX
  let f : ↥(s13XSupp X {U}) → ZMod p := fun x =>
    lam ⟨U, hU⟩ (Additive.ofMul ⟨(x : MulAut W), (mem_s13XSupp.mp x.2).1⟩)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxX : (x : MulAut W) ∈ X := (mem_s13XSupp.mp x.2).1
    have hyX : (y : MulAut W) ∈ X := (mem_s13XSupp.mp y.2).1
    have hcoord : ∀ V : s13IsoComps X,
        lam V (Additive.ofMul ⟨(x : MulAut W), hxX⟩) =
        lam V (Additive.ofMul ⟨(y : MulAut W), hyX⟩) := by
      intro V
      by_cases hVU : V = ⟨U, hU⟩
      · rw [hVU]
        exact hxy
      · have hxV : (x : MulAut W) ∈ s13KerOn X V.1 :=
          (mem_s13XSupp.mp x.2).2 V.1 V.2 (by simpa [Subtype.ext_iff] using hVU)
        have hyV : (y : MulAut W) ∈ s13KerOn X V.1 :=
          (mem_s13XSupp.mp y.2).2 V.1 V.2 (by simpa [Subtype.ext_iff] using hVU)
        have hx0 : lam V (Additive.ofMul ⟨(x : MulAut W), hxX⟩) = 0 := ((hl V).2 _).mpr hxV
        have hy0 : lam V (Additive.ofMul ⟨(y : MulAut W), hyX⟩) = 0 := ((hl V).2 _).mpr hyV
        rw [hx0, hy0]
    have hxyX : (⟨(x : MulAut W), hxX⟩ : ↥X) = ⟨(y : MulAut W), hyX⟩ :=
      coord_injective hW hp hp2 hX hl hcoord
    exact Subtype.ext (congrArg (fun z : ↥X => (z : MulAut W)) hxyX)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  calc Nat.card ↥(s13XSupp X {U})
      ≤ Nat.card (ZMod p) := Nat.card_le_card_of_injective f hf_inj
    _ = p := Nat.card_zmod p

variable {A X Q : Subgroup (MulAut W)} {t : MulAut W} {p : ℕ}

theorem s13_seven_pair (h : HAb A X Q t 7) :
    ∃ U₀ U₁ : Subgroup W, U₀ ≠ U₁ ∧ s13Supp X Q = {U₀, U₁} ∧ U₁ = U₀.map t.toMonoidHom ∧
      (∀ U ∈ s13IsoComps X, U ≠ U₀ → U ≠ U₁ → commSub U (Subgroup.zpowers t) = ⊥) ∧
      commSub (fixV X) (Subgroup.zpowers t) = ⊥ := by
  classical
  have hQne : s13Supp X Q ≠ ∅ := by
    intro hbot
    have hcomm : commSub ⊤ Q = ⊥ := by
      rw [commSub_top_eq_iSup_s13Supp h.hW (by norm_num) (by norm_num) h.hXe h.hQX]
      rw [hbot]
      simp
    have hQbot : Q = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      rw [Subgroup.mem_bot]
      ext w
      have hw : w ∈ fixV Q := (commSub_eq_bot_iff.mp hcomm) (Subgroup.mem_top w)
      exact (mem_fixV.mp hw) q hq
    exact h.hQ1 hQbot
  have htQ : Q.map (MulAut.conj t).toMonoidHom = Q := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      change (MulAut.conj t) q ∈ Q
      rw [MulAut.conj_apply, h.hQinv q hq]
      exact Q.inv_mem hq
    · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have hsupp_conj : s13Supp X Q = (fun U : Subgroup W => U.map t.toMonoidHom) '' s13Supp X Q := by
    have h1 := s13Supp_conj (X := X) (L := Q) (g := t)
      (fun x hx => h.hXA t h.htA x hx)
      (fun x hx => by simpa using h.hXA t⁻¹ (A.inv_mem h.htA) x hx)
    rw [htQ] at h1
    exact h1
  have ht_perm : ∀ U ∈ s13Supp X Q, U.map t.toMonoidHom ∈ s13Supp X Q := by
    intro U hU
    rw [hsupp_conj]
    exact ⟨U, hU, rfl⟩
  have ht_no_fixed : ∀ U ∈ s13Supp X Q, U.map t.toMonoidHom ≠ U := by
    intro U hU
    have hU' : U ∈ s13Supp X (Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom) := by
      convert hU using 2
      ext x
      simp [MulAut.conj_apply]
    have h1 := not_fixed_comp h (a := 1) (Subgroup.one_mem A) (U := U) hU'
    simpa using h1
  have hrk3 : ∀ U ∈ s13Supp X Q, rk ↥U = 3 := by
    intro U hU
    exact rk_s13IsoComps_eq_three h hU.1
  have hsum3 : rk ↥(commSub ⊤ Q) = 3 * (s13Supp X Q).ncard := by
    rw [rk_commSub_top_eq_sum h.hW (by norm_num) (by norm_num) h.hXe h.hQX]
    haveI : Fintype {U : Subgroup W // U ∈ s13Supp X Q} := Fintype.ofFinite _
    rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
    have hcongr : ∀ U : {U : Subgroup W // U ∈ s13Supp X Q}, rk ↥(U : Subgroup W) = 3 :=
      fun U => hrk3 U U.2
    rw [Finset.sum_congr rfl (fun U _ => hcongr U)]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hcard_le : (s13Supp X Q).ncard ≤ 2 := by
    have h6 : rk ↥(commSub ⊤ Q) ≤ 6 := (cost_commSub_Q h).2
    rw [hsum3] at h6
    exact Nat.le_of_mul_le_mul_left h6 (by norm_num : 0 < 3)
  have hcard_pos : 0 < (s13Supp X Q).ncard := by
    rw [Set.ncard_pos]
    exact Set.nonempty_iff_ne_empty.mpr hQne
  have hcard_ne_one : (s13Supp X Q).ncard ≠ 1 := by
    intro h1
    obtain ⟨U, hU⟩ := Set.ncard_eq_one.mp h1
    have hU_supp : U ∈ s13Supp X Q := by rw [hU]; exact Set.mem_singleton U
    have hUt_supp : U.map t.toMonoidHom ∈ s13Supp X Q := ht_perm U hU_supp
    rw [hU] at hUt_supp
    have : U.map t.toMonoidHom = U := Set.mem_singleton_iff.mp hUt_supp
    exact ht_no_fixed U hU_supp this
  have hcard_two : (s13Supp X Q).ncard = 2 := by
    omega
  obtain ⟨U₀, U₁, hU₀U₁, hsupp⟩ := Set.ncard_eq_two.mp hcard_two
  have hU₀_supp : U₀ ∈ s13Supp X Q := by rw [hsupp]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hU₁_supp : U₁ ∈ s13Supp X Q := by rw [hsupp]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hU₀t_supp : U₀.map t.toMonoidHom ∈ s13Supp X Q := ht_perm U₀ hU₀_supp
  have hU₀t_ne_U₀ : U₀.map t.toMonoidHom ≠ U₀ := ht_no_fixed U₀ hU₀_supp
  have hU₁_eq : U₁ = U₀.map t.toMonoidHom := by
    rw [hsupp] at hU₀t_supp
    rcases Set.mem_insert_iff.mp hU₀t_supp with h | h
    · exact absurd h hU₀t_ne_U₀
    · exact (Set.mem_singleton_iff.mp h).symm
  have hcost_eq : rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)) = 3 := by
    have h1 := (cost_commSub_Q h).1
    have h2 : rk ↥(commSub ⊤ Q) = 6 := by
      rw [hsum3, hcard_two]
    linarith
  have hconj1 : MulAut.conj (1 : MulAut W) = 1 := by
    ext x
    simp [MulAut.conj_apply]
  have hQmap1 : Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom = Q := by
    rw [hconj1]
    exact Subgroup.map_id Q
  have ht1 : (1 : MulAut W) * t * 1⁻¹ = t := by simp
  have hcost_eq' : rk ↥(commSub (commSub ⊤ (Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom))
      (Subgroup.zpowers (1 * t * 1⁻¹))) = 3 := by
    rw [hQmap1, ht1]
    exact hcost_eq
  have hsat := saturation h (a := 1) (Subgroup.one_mem A) hcost_eq'
  exact ⟨U₀, U₁, hU₀U₁, hsupp, hU₁_eq,
    fun U hU hUne0 hUne1 => by
      have hUnot : U ∉ s13Supp X Q := by
        rw [hsupp]
        simp [hUne0, hUne1]
      have hUnot' : U ∉ s13Supp X (Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom) := by
        rw [hQmap1]
        exact hUnot
      exact hsat.1 U hU hUnot', hsat.2⟩

@[expose] def s13SuppGraph (A X Q : Subgroup (MulAut W)) : SimpleGraph ↥(s13IsoComps X) :=
  SimpleGraph.fromRel fun U U' =>
    ∃ a ∈ A, s13Supp X (Q.map (MulAut.conj a).toMonoidHom) = {(U : Subgroup W), (U' : Subgroup W)}

@[expose] def s13CompSet (A X Q : Subgroup (MulAut W))
    (c : (s13SuppGraph A X Q).ConnectedComponent) : Set (Subgroup W) :=
  Subtype.val '' c.supp

private theorem w16g_hab_prime (h : HAb A X Q t p) : p.Prime := by
  obtain rfl | rfl := h.hp <;> norm_num

private theorem w16g_hab_ne_two (h : HAb A X Q t p) : p ≠ 2 := by
  obtain rfl | rfl := h.hp <;> norm_num

private theorem w16g_conj_le_X (h : HAb A X Q t p) {a : MulAut W} (ha : a ∈ A) :
    Q.map (MulAut.conj a).toMonoidHom ≤ X := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
  show a * q * a⁻¹ ∈ X
  exact h.hXA a ha q (h.hQX hq)

private theorem w16g_s13XSupp_mono {X : Subgroup (MulAut W)} {B B' : Set (Subgroup W)}
    (hBB' : B ⊆ B') : s13XSupp X B ≤ s13XSupp X B' := by
  intro x hx
  rw [mem_s13XSupp] at hx ⊢
  exact ⟨hx.1, fun U hU hUB' => hx.2 U hU fun hUB => hUB' (hBB' hUB)⟩

private theorem w16g_s13CompSet_disjoint {A X Q : Subgroup (MulAut W)}
    {c c' : (s13SuppGraph A X Q).ConnectedComponent} (hne : c ≠ c') :
    Disjoint (s13CompSet A X Q c) (s13CompSet A X Q c') := by
  rw [s13CompSet, s13CompSet]
  exact Set.disjoint_image_of_injective Subtype.val_injective
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent (s13SuppGraph A X Q) hne)

private theorem w16g_mem_s13IsoComps_of_mem_compSet {A X Q : Subgroup (MulAut W)}
    {c : (s13SuppGraph A X Q).ConnectedComponent} {U : Subgroup W}
    (hU : U ∈ s13CompSet A X Q c) : U ∈ s13IsoComps X := by
  obtain ⟨k, -, hkU⟩ := hU
  rw [← hkU]
  exact k.2

private theorem w16g_eq_one_of_forall_mem_kerOn (h : HAb A X Q t p) {x : MulAut W}
    (hxX : x ∈ X) (hx : ∀ U ∈ s13IsoComps X, x ∈ s13KerOn X U) : x = 1 := by
  obtain ⟨lam, hl⟩ := exists_coord h.hW (w16g_hab_prime h) (w16g_hab_ne_two h) h.hXe
  have hcoord : ∀ U : s13IsoComps X,
      lam U (Additive.ofMul ⟨x, hxX⟩) = lam U (Additive.ofMul (1 : ↥X)) := by
    intro U
    have hx0 : lam U (Additive.ofMul ⟨x, hxX⟩) = 0 := ((hl U).2 _).mpr (hx U.1 U.2)
    have h10 : lam U (Additive.ofMul (1 : ↥X)) = 0 := map_zero (lam U)
    rw [hx0, h10]
  have hxy : (⟨x, hxX⟩ : ↥X) = 1 :=
    coord_injective h.hW (w16g_hab_prime h) (w16g_hab_ne_two h) h.hXe hl hcoord
  exact congrArg (fun z : ↥X => (z : MulAut W)) hxy

private theorem w16g_conj_le_XSupp (h : HAb A X Q t p)
    (h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2)
    {a : MulAut W} (ha : a ∈ A) :
    ∃ c : (s13SuppGraph A X Q).ConnectedComponent,
      Q.map (MulAut.conj a).toMonoidHom ≤ s13XSupp X (s13CompSet A X Q c) := by
  classical
  have hp := w16g_hab_prime h
  have hp2 := w16g_hab_ne_two h
  have hQaX := w16g_conj_le_X h ha
  obtain ⟨U, U', hUU', hS⟩ := Set.ncard_eq_two.mp (h2 a ha)
  have hU_supp : U ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) := by
    rw [hS]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hU'_supp : U' ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) := by
    rw [hS]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  let u : ↥(s13IsoComps X) := ⟨U, hU_supp.1⟩
  let u' : ↥(s13IsoComps X) := ⟨U', hU'_supp.1⟩
  have hadj : (s13SuppGraph A X Q).Adj u u' := by
    rw [s13SuppGraph, SimpleGraph.fromRel_adj]
    exact ⟨fun hcontra => hUU' (Subtype.ext_iff.mp hcontra),
      Or.inl ⟨a, ha, by simpa [u, u'] using hS⟩⟩
  let c := (s13SuppGraph A X Q).connectedComponentMk u
  refine ⟨c, ?_⟩
  rw [le_s13XSupp_iff (B := s13CompSet A X Q c) h.hW hp hp2 h.hXe hQaX]
  intro V hV
  have hc_eq : (s13SuppGraph A X Q).connectedComponentMk u' = c :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
  rw [hS] at hV
  rcases Set.mem_insert_iff.mp hV with hVU | hVU'
  · rw [hVU]
    exact ⟨u, by simp [c], rfl⟩
  · rw [Set.mem_singleton_iff.mp hVU']
    exact ⟨u', by simpa [c] using hc_eq, rfl⟩

private theorem w16g_graph_coord_inj (h : HAb A X Q t p)
    {lam : s13IsoComps X → Additive ↥X →+ ZMod p} (hl : IsCoord X p lam)
    (c : (s13SuppGraph A X Q).ConnectedComponent) :
    Function.Injective (fun x : ↥(s13XSupp X (s13CompSet A X Q c)) =>
      fun k : ↥c.supp => lam k.1 (Additive.ofMul ⟨(x : MulAut W), s13XSupp_le x.2⟩)) := by
  have hp := w16g_hab_prime h
  have hp2 := w16g_hab_ne_two h
  intro x y hxy
  have hxX : (x : MulAut W) ∈ X := s13XSupp_le x.2
  have hyX : (y : MulAut W) ∈ X := s13XSupp_le y.2
  have hcoord : ∀ U : s13IsoComps X,
      lam U (Additive.ofMul ⟨(x : MulAut W), hxX⟩) =
      lam U (Additive.ofMul ⟨(y : MulAut W), hyX⟩) := by
    intro U
    by_cases hU : (U : Subgroup W) ∈ s13CompSet A X Q c
    · obtain ⟨k, hk, hkU⟩ := hU
      have hUk : U = k := Subtype.ext hkU.symm
      rw [hUk]
      simpa using congrFun hxy ⟨k, hk⟩
    · have hx0 : lam U (Additive.ofMul ⟨(x : MulAut W), hxX⟩) = 0 :=
        ((hl U).2 _).mpr ((mem_s13XSupp.mp x.2).2 U.1 U.2 hU)
      have hy0 : lam U (Additive.ofMul ⟨(y : MulAut W), hyX⟩) = 0 :=
        ((hl U).2 _).mpr ((mem_s13XSupp.mp y.2).2 U.1 U.2 hU)
      rw [hx0, hy0]
  have hxyX : (⟨(x : MulAut W), hxX⟩ : ↥X) = ⟨(y : MulAut W), hyX⟩ :=
    coord_injective h.hW hp hp2 h.hXe hl hcoord
  exact Subtype.ext (congrArg (fun z : ↥X => (z : MulAut W)) hxyX)

private theorem w16g_card_supp_eq {A X Q : Subgroup (MulAut W)}
    (c : (s13SuppGraph A X Q).ConnectedComponent) :
    Nat.card ↥c.supp = (s13CompSet A X Q c).ncard := by
  rw [Nat.card_coe_set_eq, s13CompSet]
  exact (Set.ncard_image_of_injective c.supp Subtype.val_injective).symm

private theorem w16g_edge_generator (h : HAb A X Q t p)
    (h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2)
    (hQp : Nat.card ↥Q = p) {lam : s13IsoComps X → Additive ↥X →+ ZMod p}
    (hl : IsCoord X p lam) (c : (s13SuppGraph A X Q).ConnectedComponent)
    (i j : ↥c.supp) {a : MulAut W} (ha : a ∈ A)
    (hS : s13Supp X (Q.map (MulAut.conj a).toMonoidHom) = {i.1.1, j.1.1}) :
    ∃ q : ↥X, (q : MulAut W) ∈ s13XSupp X (s13CompSet A X Q c) ∧
      ∀ k : ↥c.supp, lam k.1 (Additive.ofMul q) ≠ 0 ↔ (k = i ∨ k = j) := by
  classical
  have hp := w16g_hab_prime h
  have hp2 := w16g_hab_ne_two h
  haveI : Fact p.Prime := ⟨hp⟩
  have hQaX := w16g_conj_le_X h ha
  obtain ⟨c', hc'⟩ := w16g_conj_le_XSupp h h2 ha
  have hsupp_sub : s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ⊆ s13CompSet A X Q c' :=
    (le_s13XSupp_iff (B := s13CompSet A X Q c') h.hW hp hp2 h.hXe hQaX).mp hc'
  have hi_c' : i.1.1 ∈ s13CompSet A X Q c' := by
    apply hsupp_sub
    rw [hS]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hc'_eq : c' = c := by
    by_contra hne
    exact (Set.disjoint_left.mp (w16g_s13CompSet_disjoint hne)) hi_c'
      (show i.1.1 ∈ s13CompSet A X Q c from ⟨i.1, i.2, rfl⟩)
  have hQac : Q.map (MulAut.conj a).toMonoidHom ≤ s13XSupp X (s13CompSet A X Q c) :=
    hc'_eq ▸ hc'
  have hcardQa : Nat.card ↥(Q.map (MulAut.conj a).toMonoidHom) = p := by
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective, hQp]
  have hcyc : IsCyclic ↥(Q.map (MulAut.conj a).toMonoidHom) := isCyclic_of_prime_card hcardQa
  obtain ⟨q, hq⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top
    (Q.map (MulAut.conj a).toMonoidHom)).mp hcyc
  have hqQa : q ∈ Q.map (MulAut.conj a).toMonoidHom := hq ▸ Subgroup.mem_zpowers q
  refine ⟨⟨q, hQaX hqQa⟩, hQac hqQa, ?_⟩
  intro k
  rw [coord_ne_zero_iff hl ⟨q, hQaX hqQa⟩ k.1, hq]
  constructor
  · intro hne
    have hmem : k.1.1 ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) := ⟨k.1.2, hne⟩
    rw [hS] at hmem
    rcases Set.mem_insert_iff.mp hmem with hh | hh
    · left; exact Subtype.ext (Subtype.ext hh)
    · right; exact Subtype.ext (Subtype.ext (Set.mem_singleton_iff.mp hh))
  · intro hk
    rcases hk with hk | hk
    · rw [hk]
      exact (show i.1.1 ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) by
        rw [hS]; exact Set.mem_insert_iff.mpr (Or.inl rfl)).2
    · rw [hk]
      exact (show j.1.1 ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) by
        rw [hS]; exact Set.mem_insert_iff.mpr (Or.inr rfl)).2

private theorem w16g_graph_vertex_on_edge (h : HAb A X Q t p)
    (h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2) :
    ∀ U : ↥(s13IsoComps X), ∃ V, (s13SuppGraph A X Q).Adj U V := by
  intro U
  obtain ⟨a, ha, hU⟩ := exists_conj_supp h U.2
  have h2a := h2 a ha
  obtain ⟨x, y, hxy, hS⟩ := Set.ncard_eq_two.mp h2a
  have hU_mem : U.1 ∈ ({x, y} : Set (Subgroup W)) := by rw [← hS]; exact hU
  rcases Set.mem_insert_iff.mp hU_mem with hx | hy
  · refine ⟨⟨y, ?_⟩, ?_⟩
    · have hy_supp : y ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) := by
        rw [hS]
        exact Set.mem_insert_iff.mpr (Or.inr rfl)
      exact hy_supp.1
    · rw [s13SuppGraph, SimpleGraph.fromRel_adj]
      exact ⟨fun hcontra => hxy (by rw [← hx, hcontra]), Or.inl ⟨a, ha, hS.trans (by rw [hx])⟩⟩
  · refine ⟨⟨x, ?_⟩, ?_⟩
    · have hx_supp : x ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) := by
        rw [hS]
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
      exact hx_supp.1
    · rw [s13SuppGraph, SimpleGraph.fromRel_adj]
      exact ⟨fun hcontra => hxy (by rw [← hy, hcontra]),
        Or.inl ⟨a, ha, hS.trans (by rw [hy]; exact Set.pair_comm x y)⟩⟩

private theorem w16g_graph_independent (h : HAb A X Q t p)
    (h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2) :
    iSupIndep (fun c : (s13SuppGraph A X Q).ConnectedComponent =>
      s13XSupp X (s13CompSet A X Q c)) := by
  classical
  rw [iSupIndep_def]
  intro c
  let B : Set (Subgroup W) :=
    {V | ∃ c' : (s13SuppGraph A X Q).ConnectedComponent, c' ≠ c ∧ V ∈ s13CompSet A X Q c'}
  have hle : (⨆ (c' : (s13SuppGraph A X Q).ConnectedComponent) (_ : c' ≠ c),
      s13XSupp X (s13CompSet A X Q c')) ≤ s13XSupp X B := by
    refine iSup_le fun c' => iSup_le fun hc' => w16g_s13XSupp_mono ?_
    intro V hV
    exact ⟨c', hc', hV⟩
  rw [disjoint_iff]
  apply le_bot_iff.mp
  intro x hx
  rw [Subgroup.mem_bot]
  refine w16g_eq_one_of_forall_mem_kerOn h (mem_s13XSupp.mp hx.1).1 fun U hU => ?_
  by_cases hUc : U ∈ s13CompSet A X Q c
  · have hx2 : x ∈ s13XSupp X B := hle hx.2
    have hUnB : U ∉ B := by
      rintro ⟨c', hc'ne, hUc'⟩
      exact (Set.disjoint_left.mp (w16g_s13CompSet_disjoint hc'ne)) hUc' hUc
    exact (mem_s13XSupp.mp hx2).2 U hU hUnB
  · exact (mem_s13XSupp.mp hx.1).2 U hU hUc

private theorem w16g_graph_iSup_eq_X (h : HAb A X Q t p)
    (h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2) :
    (⨆ c : (s13SuppGraph A X Q).ConnectedComponent, s13XSupp X (s13CompSet A X Q c)) = X := by
  apply le_antisymm
  · exact iSup_le fun c => s13XSupp_le
  · have hgen : conjClosure A Q ≤ ⨆ c : (s13SuppGraph A X Q).ConnectedComponent,
        s13XSupp X (s13CompSet A X Q c) := by
      unfold conjClosure
      rw [Subgroup.closure_le]
      rintro x ⟨g, hg, y, hy, rfl⟩
      obtain ⟨c, hc⟩ := w16g_conj_le_XSupp h h2 hg
      refine le_iSup (fun c : (s13SuppGraph A X Q).ConnectedComponent =>
        s13XSupp X (s13CompSet A X Q c)) c (hc ?_)
      rw [← MulAut.conj_apply]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact h.hXgen.symm ▸ hgen

private theorem w16g_graph_supp_eq (h : HAb A X Q t p)
    (h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2)
    (c : (s13SuppGraph A X Q).ConnectedComponent) :
    s13Supp X (s13XSupp X (s13CompSet A X Q c)) = s13CompSet A X Q c := by
  classical
  have hp := w16g_hab_prime h
  have hp2 := w16g_hab_ne_two h
  apply Set.Subset.antisymm
  · have hsub := (le_s13XSupp_iff (B := s13CompSet A X Q c) h.hW hp hp2 h.hXe
      (s13XSupp_le (X := X) (B := s13CompSet A X Q c))).mp le_rfl
    exact hsub
  · intro U hU
    have hUiso : U ∈ s13IsoComps X := w16g_mem_s13IsoComps_of_mem_compSet hU
    obtain ⟨a, ha, hU_supp⟩ := exists_conj_supp h hUiso
    obtain ⟨c', hc'⟩ := w16g_conj_le_XSupp h h2 ha
    have hQaX := w16g_conj_le_X h ha
    have hsupp_sub : s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ⊆
        s13CompSet A X Q c' :=
      (le_s13XSupp_iff (B := s13CompSet A X Q c') h.hW hp hp2 h.hXe hQaX).mp hc'
    have hU_c' : U ∈ s13CompSet A X Q c' := hsupp_sub hU_supp
    have hc'_eq : c' = c := by
      by_contra hne
      exact (Set.disjoint_left.mp (w16g_s13CompSet_disjoint hne)) hU_c' hU
    have hc'' : Q.map (MulAut.conj a).toMonoidHom ≤ s13XSupp X (s13CompSet A X Q c) :=
      hc'_eq ▸ hc'
    refine ⟨hUiso, ?_⟩
    intro hbot
    have hcomm : commSub U (Q.map (MulAut.conj a).toMonoidHom) = ⊥ :=
      le_bot_iff.mp (hbot ▸ commSub_mono le_rfl hc'')
    exact hU_supp.2 hcomm

private theorem w16g_graph_card_le (h : HAb A X Q t p)
    (h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2)
    (c : (s13SuppGraph A X Q).ConnectedComponent) :
    Nat.card ↥(s13XSupp X (s13CompSet A X Q c)) ≤ p ^ (s13CompSet A X Q c).ncard := by
  classical
  have hp := w16g_hab_prime h
  have hp2 := w16g_hab_ne_two h
  obtain ⟨lam, hl⟩ := exists_coord h.hW hp hp2 h.hXe
  let ι := ↥c.supp
  haveI : Fintype ι := Fintype.ofFinite _
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (ι → ZMod p) := (inferInstance : Fintype (ι → ZMod p)).finite
  let φ : ↥(s13XSupp X (s13CompSet A X Q c)) → (ι → ZMod p) := fun x k =>
    lam k.1 (Additive.ofMul ⟨(x : MulAut W), s13XSupp_le x.2⟩)
  have hφ_inj : Function.Injective φ := w16g_graph_coord_inj h hl c
  calc Nat.card ↥(s13XSupp X (s13CompSet A X Q c))
      ≤ Nat.card (ι → ZMod p) := Nat.card_le_card_of_injective φ hφ_inj
    _ = p ^ Nat.card ι := by rw [Nat.card_fun, Nat.card_zmod]
    _ = p ^ (s13CompSet A X Q c).ncard := by rw [w16g_card_supp_eq c]

private theorem w16g_graph_card_ge (h : HAb A X Q t p) (hQp : Nat.card ↥Q = p)
    (h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2)
    (c : (s13SuppGraph A X Q).ConnectedComponent) :
    p ^ ((s13CompSet A X Q c).ncard - 1) ≤ Nat.card ↥(s13XSupp X (s13CompSet A X Q c)) := by
  classical
  have hp := w16g_hab_prime h
  have hp2 := w16g_hab_ne_two h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨lam, hl⟩ := exists_coord h.hW hp hp2 h.hXe
  let G : SimpleGraph ↥c.supp := c.toSimpleGraph
  let ι := ↥c.supp
  haveI : Fintype ι := Fintype.ofFinite _
  haveI : DecidableEq ι := Classical.decEq _
  have hgen : ∀ (i j : ι), G.Adj i j →
      ∃ q : ↥X, (q : MulAut W) ∈ s13XSupp X (s13CompSet A X Q c) ∧
        ∀ k : ι, lam k.1 (Additive.ofMul q) ≠ 0 ↔ (k = i ∨ k = j) := by
    intro i j hij
    have hadj : (s13SuppGraph A X Q).Adj i.1 j.1 := by
      have hh : c.toSimpleGraph.Adj i j := by simpa [G] using hij
      exact (SimpleGraph.ConnectedComponent.toSimpleGraph_adj c i.2 j.2).mp hh
    have hadj' : (SimpleGraph.fromRel (fun (U U' : ↥(s13IsoComps X)) =>
        ∃ a ∈ A, s13Supp X (Q.map (MulAut.conj a).toMonoidHom) =
          {(U : Subgroup W), (U' : Subgroup W)})).Adj i.1 j.1 := hadj
    rw [SimpleGraph.fromRel_adj] at hadj'
    obtain ⟨-, hrel | hrel⟩ := hadj'
    · obtain ⟨a, ha, hS⟩ := hrel
      exact w16g_edge_generator h h2 hQp hl c i j ha hS
    · obtain ⟨a, ha, hS⟩ := hrel
      exact w16g_edge_generator h h2 hQp hl c i j ha (by rw [hS, Set.pair_comm])
  let gen : ∀ (i j : ι), G.Adj i j → ↥X := fun i j h => Classical.choose (hgen i j h)
  let v : ι → ι → ι → ZMod p := fun i j k =>
    if h : G.Adj i j then lam k.1 (Additive.ofMul (gen i j h)) else 0
  have hv : ∀ i j, G.Adj i j → ∀ k, v i j k ≠ 0 ↔ (k = i ∨ k = j) := by
    intro i j hij k
    simp only [v, dif_pos hij]
    exact (Classical.choose_spec (hgen i j hij)).2 k
  have hbound := w16t_card_span_edges G c.connected_toSimpleGraph v hv
  let inc : ↥(s13XSupp X (s13CompSet A X Q c)) →* ↥X := Subgroup.inclusion s13XSupp_le
  let φ : ↥(s13XSupp X (s13CompSet A X Q c)) → (ι → ZMod p) := fun x k =>
    lam k.1 (Additive.ofMul (inc x))
  have hφ_inj : Function.Injective φ := w16g_graph_coord_inj h hl c
  have hφ_one : φ 1 = 0 := by
    funext k
    simp [φ]
  have hφ_mul : ∀ x y, φ (x * y) = φ x + φ y := by
    intro x y
    funext k
    simp only [φ, Pi.add_apply]
    rw [map_mul, ofMul_mul, map_add]
  have hφ_inv : ∀ x, φ x⁻¹ = -φ x := by
    intro x
    funext k
    simp only [φ, Pi.neg_apply]
    rw [map_inv, ofMul_inv, map_neg]
  let Tadd : AddSubgroup (ι → ZMod p) :=
    { carrier := Set.range φ
      zero_mem' := ⟨1, hφ_one⟩
      add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, hφ_mul x y⟩
      neg_mem' := by rintro _ ⟨x, rfl⟩; exact ⟨x⁻¹, hφ_inv x⟩ }
  let T : Submodule (ZMod p) (ι → ZMod p) := Tadd.toZModSubmodule p
  have hspan_le : Submodule.span (ZMod p) {w : ι → ZMod p | ∃ i j, G.Adj i j ∧ w = v i j} ≤ T := by
    rw [Submodule.span_le]
    rintro w ⟨i, j, hij, rfl⟩
    refine ⟨⟨gen i j hij, (Classical.choose_spec (hgen i j hij)).1⟩, ?_⟩
    funext k
    simp only [v, dif_pos hij, φ]
    rw [show inc ⟨(gen i j hij : MulAut W),
        (Classical.choose_spec (hgen i j hij)).1⟩ = gen i j hij from
      Subtype.ext rfl]
  have hcard_le :
      Nat.card ↥(Submodule.span (ZMod p) {w : ι → ZMod p | ∃ i j, G.Adj i j ∧ w = v i j}) ≤
        Nat.card ↥(s13XSupp X (s13CompSet A X Q c)) := by
    have h1 : Nat.card ↥(Submodule.span (ZMod p) {w : ι → ZMod p | ∃ i j, G.Adj i j ∧ w = v i j})
        ≤ Nat.card ↥T :=
      Nat.card_le_card_of_injective (Set.inclusion hspan_le) (Set.inclusion_injective hspan_le)
    have h2 : Nat.card ↥T = Nat.card ↥(s13XSupp X (s13CompSet A X Q c)) :=
      (Nat.card_congr (Equiv.ofInjective φ hφ_inj)).symm
    exact le_trans h1 (le_of_eq h2)
  calc p ^ ((s13CompSet A X Q c).ncard - 1)
      = p ^ (Fintype.card ι - 1) := by rw [← w16g_card_supp_eq c, Nat.card_eq_fintype_card]
    _ ≤ Nat.card ↥(Submodule.span (ZMod p) {w : ι → ZMod p | ∃ i j, G.Adj i j ∧ w = v i j}) :=
        hbound
    _ ≤ Nat.card ↥(s13XSupp X (s13CompSet A X Q c)) := hcard_le

theorem s13_graph_decomp (h : HAb A X Q t p) (hQp : Nat.card ↥Q = p)
    (h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2) :
    (∀ U : ↥(s13IsoComps X), ∃ V, (s13SuppGraph A X Q).Adj U V) ∧
      iSupIndep (fun c : (s13SuppGraph A X Q).ConnectedComponent =>
        s13XSupp X (s13CompSet A X Q c)) ∧
      (⨆ c : (s13SuppGraph A X Q).ConnectedComponent, s13XSupp X (s13CompSet A X Q c)) = X ∧
      ∀ c : (s13SuppGraph A X Q).ConnectedComponent,
        s13Supp X (s13XSupp X (s13CompSet A X Q c)) = s13CompSet A X Q c ∧
          p ^ ((s13CompSet A X Q c).ncard - 1) ≤ Nat.card ↥(s13XSupp X (s13CompSet A X Q c)) ∧
          Nat.card ↥(s13XSupp X (s13CompSet A X Q c)) ≤ p ^ (s13CompSet A X Q c).ncard := by
  exact ⟨w16g_graph_vertex_on_edge h h2, w16g_graph_independent h h2, w16g_graph_iSup_eq_X h h2,
    fun c => ⟨w16g_graph_supp_eq h h2 c, w16g_graph_card_ge h hQp h2 c, w16g_graph_card_le h h2 c⟩⟩

end CFSG.LocalAnalysis.WeakClosure81
