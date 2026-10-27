module

public import CFSG.Timmesfeld.Transvection.TriangleCrux

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.LeviQuot CFSG.Timmesfeld.ARS.NaturalModule
open scoped Matrix

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G}

structure Coords (S : TriangleSetting Δ A E B t) where
  k : ℕ
  card_eq : Nat.card A = 2 ^ k
  mat : G → Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)
  mat_mul : ∀ {x y : G}, x ∈ A ⊔ E → y ∈ A ⊔ E → mat (x * y) = mat x * mat y
  mat_surj : ∀ g, ∃ x ∈ A ⊔ E, mat x = g
  mat_inj : ∀ {x : G}, x ∈ A ⊔ E → mat x = 1 → x = 1
  mem_A_iff : ∀ {x : G}, x ∈ A ⊔ E → (x ∈ A ↔ mat x ∈ lowerUnipotent (GaloisField 2 k))
  mem_E_iff : ∀ {x : G}, x ∈ A ⊔ E → (x ∈ E ↔ mat x ∈ upperUnipotent (GaloisField 2 k))
  vec : G → (Fin 2 → GaloisField 2 k)
  vec_mul : ∀ {n n' : G}, n ∈ corrN A E t → n' ∈ corrN A E t → vec (n * n') = vec n + vec n'
  vec_surj : ∀ v, ∃ n ∈ corrN A E t, vec n = v
  vec_eq_zero_iff : ∀ {n : G}, n ∈ corrN A E t →
    (vec n = 0 ↔ n ∈ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G))
  vec_conj : ∀ {x n : G}, x ∈ A ⊔ E → n ∈ corrN A E t →
    vec (x * n * x⁻¹) = (mat x : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)) *ᵥ vec n
  commute_A_iff : ∀ {n : G}, n ∈ corrN A E t → ((∀ a ∈ A, Commute n a) ↔ vec n 0 = 0)
  commute_E_iff : ∀ {n : G}, n ∈ corrN A E t → ((∀ e ∈ E, Commute n e) ↔ vec n 1 = 0)
  bijOn_graph : Set.BijOn vec (graph A t) {v | v 0 = 0}

variable (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
include S htY

theorem eq_one_of_mem_E_of_mem_corrN [Finite G] (hq : 4 ≤ Nat.card A) {e : G} (he : e ∈ E)
    (heN : e ∈ corrN A E t) : e = 1 := by
  obtain ⟨w, hw, hwE⟩ := S.exists_conjSub_eq_E
  have ha : w⁻¹ * e * w ∈ A := by
    rw [← hwE] at he
    obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff.1 he
    rwa [show w⁻¹ * (w * a * w⁻¹) * w = a by group]
  have haN : w⁻¹ * e * w ∈ corrN A E t := by
    have := conj_mem_corrN (Subgroup.inv_mem _ hw) heN
    rwa [inv_inv] at this
  have h1 := S.eq_one_of_mem_of_mem_corrN htY hq ha haN
  calc e = w * (w⁻¹ * e * w) * w⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem commute_of_conjSub_eq_E [Finite G] (hq : 4 ≤ Nat.card A) {n : G}
    (hn : n ∈ corrN A E t) (hnE : conjSub E n = E) {e : G} (he : e ∈ E) : Commute n e := by
  have h1 : n * e * n⁻¹ * e⁻¹ ∈ E := E.mul_mem (hnE ▸ conj_mem_conjSub n he) (E.inv_mem he)
  have h2 : n * e * n⁻¹ * e⁻¹ ∈ corrN A E t := by
    have : e * n⁻¹ * e⁻¹ ∈ corrN A E t :=
      conj_mem_corrN (Subgroup.mem_sup_right he) (Subgroup.inv_mem _ hn)
    rw [show n * e * n⁻¹ * e⁻¹ = n * (e * n⁻¹ * e⁻¹) by group]
    exact Subgroup.mul_mem _ hn this
  have h3 := S.eq_one_of_mem_E_of_mem_corrN htY hq h1 h2
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem conjSub_E_eq_of_forall_commute_quotMap [Finite G] (m : ↥(A ⊔ E ⊔ B))
    (hm : ∀ y ∈ quotMap (A ⊔ E ⊔ B) E,
      Commute (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m) y) :
    conjSub E (m : G) = E := by
  have hE := (S.mem_triClass htY).2.1
  refine S.injOn_quotMap' htY (conjSub_mem_triClass hE m.2) hE ?_
  rw [quotMap_conjSub E m.2]
  exact conjSub_of_forall_commute hm

omit htY in
theorem eq_one_of_mem_sup_of_mem_center [Finite G] {x : ↥(A ⊔ E ⊔ B)} (hx : (x : G) ∈ A ⊔ E)
    (hc : x ∈ Subgroup.center ↥(A ⊔ E ⊔ B)) : x = 1 := by
  have hXY : A ⊔ E ≤ A ⊔ E ⊔ B := le_sup_left
  refine Subtype.ext (S.tri.oppA.symm.eq_one_of_mem_centralizer (S.cls.root.mul_self A S.tri.memA)
    hx (Subgroup.mem_centralizer_iff.2 fun y hy => ?_))
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨y, hXY hy⟩)

theorem nonempty_coords [Finite G] (hq : 4 ≤ Nat.card A) : Nonempty S.Coords := by
  classical
  obtain ⟨e₀, he₀, he₀1⟩ := S.cls.root.exists_ne_one S.tri.memE
  obtain ⟨k, hk, φ, hφE, hφA, θ, hθ, hθN, hlift, -, hF⟩ := S.exists_coords htY hq he₀ he₀1
  have hNY := S.corrN_le_sup
  have hXY : A ⊔ E ≤ A ⊔ E ⊔ B := le_sup_left
  have hAY : A ≤ A ⊔ E ⊔ B := le_sup_left.trans le_sup_left
  have hEY : E ≤ A ⊔ E ⊔ B := le_sup_right.trans le_sup_left
  have hXq : ∀ {x : G} (hx : x ∈ A ⊔ E), QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))
      ⟨x, hXY hx⟩ ∈ quotMap (A ⊔ E ⊔ B) E ⊔ quotMap (A ⊔ E ⊔ B) A := by
    intro x hx
    rw [sup_comm (quotMap (A ⊔ E ⊔ B) E), ← TriangleSetting.quotMap_sup_left]
    exact mk_mem_quotMap hx
  let mat : G → Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k) := fun x =>
    if hx : x ∈ A ⊔ E then φ ⟨_, hXq hx⟩ else 1
  let vec : G → (Fin 2 → GaloisField 2 k) := fun n =>
    if hn : n ∈ A ⊔ E ⊔ B then Function.invFun θ (QuotientGroup.mk' _ ⟨n, hn⟩) else 0
  have hmat : ∀ {x : G} (hx : x ∈ A ⊔ E), mat x = φ ⟨_, hXq hx⟩ := fun hx => dite_eq_left hx
  have hvec : ∀ {n : G} (hn : n ∈ corrN A E t),
      θ (vec n) = QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨n, hNY hn⟩ := by
    intro n hn
    simp only [vec, dite_eq_left (hNY hn)]
    obtain ⟨v, hv⟩ := hθN ⟨n, hNY hn⟩ hn
    exact Function.invFun_eq ⟨v, hv⟩
  have hvec_iff : ∀ {n : G} (hn : n ∈ corrN A E t) (v : Fin 2 → GaloisField 2 k),
      vec n = v ↔ θ v = QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨n, hNY hn⟩ := by
    intro n hn v
    rw [← hvec hn]
    exact ⟨fun h => h ▸ rfl, fun h => hθ.injective h.symm⟩
  have hmk_one : ∀ {x : G} (hx : x ∈ A ⊔ E),
      QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨x, hXY hx⟩ = 1 → x = 1 := by
    intro x hx h1
    exact congrArg Subtype.val
      (S.eq_one_of_mem_sup_of_mem_center hx
        ((QuotientGroup.eq_one_iff (⟨x, hXY hx⟩ : ↥(A ⊔ E ⊔ B))).1 h1))
  have hmem_quot : ∀ {P : Subgroup G}, P ≤ A ⊔ E → ∀ {x : G} (hx : x ∈ A ⊔ E),
      (x ∈ P ↔ QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨x, hXY hx⟩ ∈
        quotMap (A ⊔ E ⊔ B) P) := by
    intro P hP x hx
    refine ⟨fun h => mk_mem_quotMap h, fun h => ?_⟩
    obtain ⟨y, hy, hyx⟩ := exists_of_mem_quotMap h
    have h1 : (y : G)⁻¹ * x = 1 := by
      have hm : (y : G)⁻¹ * x ∈ A ⊔ E := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hP hy)) hx
      refine hmk_one hm ?_
      have : (⟨(y : G)⁻¹ * x, hXY hm⟩ : ↥(A ⊔ E ⊔ B)) = y⁻¹ * ⟨x, hXY hx⟩ := rfl
      rw [this, map_mul, map_inv, hyx, inv_mul_cancel]
    rw [inv_mul_eq_one] at h1
    exact h1 ▸ hy
  refine ⟨⟨k, hk, mat, fun {x y} hx hy => ?_, fun g => ?_, fun {x} hx h1 => ?_,
    fun {x} hx => ?_, fun {x} hx => ?_, vec, fun {n n'} hn hn' => ?_, fun v => ?_,
    fun {n} hn => ?_, fun {x n} hx hn => ?_, fun {n} hn => ?_, fun {n} hn => ?_, ?_⟩⟩
  ·
    rw [hmat hx, hmat hy, hmat (Subgroup.mul_mem _ hx hy), ← map_mul]
    rfl
  ·
    have h1 : ((φ.symm g : ↥(quotMap (A ⊔ E ⊔ B) E ⊔ quotMap (A ⊔ E ⊔ B) A)) :
        ↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B)) ∈ quotMap (A ⊔ E ⊔ B) (A ⊔ E) := by
      rw [TriangleSetting.quotMap_sup_left, sup_comm (quotMap (A ⊔ E ⊔ B) A)]
      exact (φ.symm g).2
    obtain ⟨y, hy, hyg⟩ := exists_of_mem_quotMap h1
    refine ⟨y, hy, ?_⟩
    rw [hmat hy]
    have : (⟨_, hXq hy⟩ : ↥(quotMap (A ⊔ E ⊔ B) E ⊔ quotMap (A ⊔ E ⊔ B) A)) = φ.symm g :=
      Subtype.ext hyg
    rw [this, MulEquiv.apply_symm_apply]
  ·
    rw [hmat hx, map_eq_one_iff φ φ.injective] at h1
    exact hmk_one hx (congrArg Subtype.val h1)
  ·
    rw [hmem_quot le_sup_left hx, hmat hx]
    exact NaturalModule.coe_mem_iff hφA ⟨_, hXq hx⟩
  ·
    rw [hmem_quot le_sup_right hx, hmat hx]
    exact NaturalModule.coe_mem_iff hφE ⟨_, hXq hx⟩
  ·
    refine (hvec_iff (Subgroup.mul_mem _ hn hn') _).2 ?_
    rw [hθ.map_add, hvec hn, hvec hn', ← map_mul]
    rfl
  ·
    obtain ⟨m, hm, hmv⟩ := hlift v
    exact ⟨m, hm, (hvec_iff hm v).2 hmv.symm⟩
  ·
    rw [hvec_iff hn, hθ.map_zero, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hc
      exact Subgroup.mem_centralizer_iff.2 fun y hy =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨y, hXY hy⟩)
    · intro hc
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (S.commute_of_mem_corrN_inf_centralizer htY hq ⟨hn, hc⟩ g.2).symm.eq
  ·
    have hxn : x * n * x⁻¹ ∈ corrN A E t := conj_mem_corrN hx hn
    refine (hvec_iff hxn _).2 ?_
    rw [hmat hx, hθ.map_mulVec, hvec hn]
    show _ = QuotientGroup.mk' _ ((⟨x, hXY hx⟩ : ↥(A ⊔ E ⊔ B)) * ⟨n, hNY hn⟩ *
      (⟨x, hXY hx⟩ : ↥(A ⊔ E ⊔ B))⁻¹)
    rw [map_mul, map_mul, map_inv]
  ·
    rw [← hθ.forall_commute_lower_iff hφA le_sup_right, hvec hn]
    constructor
    · intro hc y hy
      obtain ⟨a, ha, rfl⟩ := exists_of_mem_quotMap hy
      exact Commute.map (show Commute a ⟨n, hNY hn⟩ from Subtype.ext (hc a ha).symm) _
    · intro hc a ha
      have hnA := S.conjSub_eq_of_forall_commute_quotMap htY ⟨n, hNY hn⟩ fun y hy => (hc y hy).symm
      exact S.commute_of_conjSub_eq htY hq hn hnA ha
  ·
    rw [← hθ.forall_commute_upper_iff hφE le_sup_left, hvec hn]
    constructor
    · intro hc y hy
      obtain ⟨e, he, rfl⟩ := exists_of_mem_quotMap hy
      exact Commute.map (show Commute e ⟨n, hNY hn⟩ from Subtype.ext (hc e he).symm) _
    · intro hc e he
      have hnE := S.conjSub_E_eq_of_forall_commute_quotMap htY ⟨n, hNY hn⟩
        fun y hy => (hc y hy).symm
      exact S.commute_of_conjSub_eq_E htY hq hn hnE he
  ·
    have hFN : ∀ {f : G}, f ∈ graph A t → f ∈ corrN A E t := fun hf =>
      corrM_le_corrN (graph_le_corrM hf)
    refine ⟨fun f hf => ?_, fun f hf f' hf' hff' => ?_, fun v hv => ?_⟩
    · show vec f 0 = 0
      rw [← hθ.forall_commute_lower_iff hφA le_sup_right, hvec (hFN hf)]
      intro y hy
      obtain ⟨a, ha, rfl⟩ := exists_of_mem_quotMap hy
      exact Commute.map (show Commute a ⟨f, hNY (hFN hf)⟩ from
        Subtype.ext (S.commute_graph_left hf ha).symm) _
    · have hm : f⁻¹ * f' ∈ graph A t := Subgroup.mul_mem _ (Subgroup.inv_mem _ hf) hf'
      have h1 : vec (f⁻¹ * f') = 0 := by
        refine (hvec_iff (hFN hm) 0).2 ?_
        rw [hθ.map_zero]
        have : (⟨f⁻¹ * f', hNY (hFN hm)⟩ : ↥(A ⊔ E ⊔ B)) =
            (⟨f, hNY (hFN hf)⟩)⁻¹ * ⟨f', hNY (hFN hf')⟩ := rfl
        rw [this, map_mul, map_inv, ← hvec (hFN hf), ← hvec (hFN hf'), hff', inv_mul_cancel]
      have h2 : f⁻¹ * f' = 1 := by
        have hc := (hvec_iff (hFN hm) 0).1 h1
        rw [hθ.map_zero, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
        exact S.eq_one_of_mem_graph_of_commute hm fun e he =>
          (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨e, hEY he⟩)).symm
      rw [inv_mul_eq_one] at h2
      exact h2
    · obtain ⟨f, hf, hfv⟩ := hF (v 1)
      refine ⟨f, hf, (hvec_iff (hFN hf) v).2 ?_⟩
      have hfv' : QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))
          (⟨(f : G), hNY (hFN hf)⟩ : ↥(A ⊔ E ⊔ B)) = θ ![0, v 1] := hfv
      rw [hfv']
      congr 1
      ext i
      fin_cases i
      · exact hv
      · rfl

noncomputable def coords [Finite G] (hq : 4 ≤ Nat.card A) : S.Coords :=
  Classical.choice (S.nonempty_coords htY hq)

end TriangleSetting

namespace TriangleSetting.Coords

variable {A E B : Subgroup G} {t : G} {S : TriangleSetting Δ A E B t} (c : S.Coords)

theorem mat_one : c.mat 1 = 1 := by
  have h := c.mat_mul (Subgroup.one_mem (A ⊔ E)) (Subgroup.one_mem (A ⊔ E))
  rw [one_mul] at h
  exact mul_left_cancel (a := c.mat 1) (by rw [mul_one]; exact h.symm)

theorem mat_inv {x : G} (hx : x ∈ A ⊔ E) : c.mat x⁻¹ = (c.mat x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← c.mat_mul hx (Subgroup.inv_mem _ hx), mul_inv_cancel, c.mat_one]

theorem vec_one : c.vec 1 = 0 := by
  have h := c.vec_mul (Subgroup.one_mem (corrN A E t)) (Subgroup.one_mem (corrN A E t))
  rw [one_mul] at h
  exact add_left_cancel (a := c.vec 1) (by rw [add_zero]; exact h.symm)

theorem vec_inv {n : G} (hn : n ∈ corrN A E t) : c.vec n⁻¹ = -c.vec n := by
  refine eq_neg_of_add_eq_zero_right ?_
  rw [← c.vec_mul hn (Subgroup.inv_mem _ hn), mul_inv_cancel, c.vec_one]

theorem exists_torus [Finite G] (μ : (GaloisField 2 c.k)ˣ) :
    ∃ h ∈ A ⊔ E, c.mat h = diagElt μ ∧ conjSub A h = A ∧ conjSub E h = E ∧
      conjSub (corrN A E t) h = corrN A E t := by
  obtain ⟨h, hX, hh⟩ := c.mat_surj (diagElt μ)
  have key : ∀ {P : Subgroup G}, P ≤ A ⊔ E →
      ∀ {U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 c.k))},
      (∀ {x : G}, x ∈ A ⊔ E → (x ∈ P ↔ c.mat x ∈ U)) →
      diagElt μ ∈ Subgroup.normalizer (U : Set _) → conjSub P h = P := by
    intro P hP U hU hnorm
    have hle : conjSub P h ≤ P := by
      rintro _ ⟨a, ha, rfl⟩
      show h * a * h⁻¹ ∈ P
      have haX : a ∈ A ⊔ E := hP ha
      have hX' : h * a ∈ A ⊔ E := Subgroup.mul_mem _ hX haX
      rw [hU (Subgroup.mul_mem _ hX' (Subgroup.inv_mem _ hX)), c.mat_mul hX'
        (Subgroup.inv_mem _ hX), c.mat_mul hX haX, c.mat_inv hX, hh]
      exact (Subgroup.mem_normalizer_iff.1 hnorm _).1 ((hU haX).1 ha)
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj h).injective).ge
  exact ⟨h, hX, hh, key le_sup_left (fun hx => c.mem_A_iff hx)
    (diagElt_mem_normalizer_lowerUnipotent μ), key le_sup_right (fun hx => c.mem_E_iff hx)
    (diagElt_mem_normalizer_upperUnipotent μ), conjSub_corrN hX⟩

end TriangleSetting.Coords

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G} (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
include S htY

theorem mem_graph_sup_of_commute [Finite G] (hq : 4 ≤ Nat.card A) {n : G}
    (hn : n ∈ corrN A E t) (hnA : ∀ a ∈ A, Commute n a) :
    n ∈ graph A t ⊔ (corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) := by
  let c := S.coords htY hq
  obtain ⟨f, hf, hfv⟩ := c.bijOn_graph.surjOn ((c.commute_A_iff hn).1 hnA)
  have hfN : f ∈ corrN A E t := corrM_le_corrN (graph_le_corrM hf)
  have hm : f⁻¹ * n ∈ corrN A E t := Subgroup.mul_mem _ (Subgroup.inv_mem _ hfN) hn
  have hz := (c.vec_eq_zero_iff hm).1 (by
    rw [c.vec_mul (Subgroup.inv_mem _ hfN) hn, c.vec_inv hfN, hfv, neg_add_cancel])
  rw [show n = f * (f⁻¹ * n) by group]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hf) (Subgroup.mem_sup_right ⟨hm, hz⟩)

theorem card_corrN_inf_centralizer_eq [Finite G] (hq : 4 ≤ Nat.card A)
    (hpts : PointsDetermined Δ) :
    Nat.card ↥(corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) =
      Nat.card A := by
  refine le_antisymm (S.card_corrN_inf_centralizer_le htY hq hpts) ?_
  set Z := corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G) with hZ
  have hAN : A ≤ Subgroup.normalizer ((corrN A E t : Subgroup G) : Set G) := fun a ha =>
    conjSub_eq_self_iff.1 (conjSub_corrN (Subgroup.mem_sup_left ha))
  have hle : corrL A E t ≤ A ⊔ (graph A t ⊔ Z) := by
    intro l hl
    have hlAN : l ∈ ((A ⊔ corrN A E t : Subgroup G) : Set G) := S.corrL_le_sup_corrN htY hq hl
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A _ hAN] at hlAN
    obtain ⟨a, ha, n, hn, hlan⟩ := hlAN
    obtain rfl : a * n = l := hlan
    have hnL : n ∈ corrL A E t := by
      rw [show n = a⁻¹ * (a * n) by group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (le_corrL ha)) hl
    have hnA : ∀ a' ∈ A, Commute n a' := fun a' ha' =>
      S.commute_of_mem_corrL' htY hq hnL (le_corrL ha')
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right (S.mem_graph_sup_of_commute htY hq hn hnA))
  have hcFZ : Commuting (graph A t) Z := fun f hf z hz =>
    (S.commute_of_mem_corrN_inf_centralizer htY hq hz (S.graph_le_sup hf)).symm
  have hcA : Commuting A (graph A t ⊔ Z) := by
    refine Commuting.sup_right (fun a ha f hf => (S.commute_graph_left hf ha).symm) ?_
    exact fun a ha z hz => (S.commute_of_mem_corrN_inf_centralizer htY hq hz
      ((le_sup_left.trans le_sup_left : A ≤ A ⊔ E ⊔ B) ha)).symm
  have hcard : Nat.card ↥(A ⊔ (graph A t ⊔ Z)) ≤ Nat.card A * (Nat.card A * Nat.card Z) := by
    calc Nat.card ↥(A ⊔ (graph A t ⊔ Z)) ≤ Nat.card A * Nat.card ↥(graph A t ⊔ Z) :=
          card_sup_le_of_commuting hcA
      _ ≤ Nat.card A * (Nat.card (graph A t) * Nat.card Z) :=
          Nat.mul_le_mul_left _ (card_sup_le_of_commuting hcFZ)
      _ = Nat.card A * (Nat.card A * Nat.card Z) := by rw [S.card_graph]
  have h1 : Nat.card A ^ 3 ≤ Nat.card A * (Nat.card A * Nat.card Z) := by
    rw [← S.card_corrL htY hq hpts]
    exact (Subgroup.card_le_of_le hle).trans hcard
  have hpos : 0 < Nat.card A * Nat.card A := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card A * Nat.card A * Nat.card A = Nat.card A ^ 3 := by ring
    _ ≤ Nat.card A * (Nat.card A * Nat.card Z) := h1
    _ = Nat.card A * Nat.card A * Nat.card Z := by ring

theorem sup_corrN_inf_centralizer_eq [Finite G] (hq : 4 ≤ Nat.card A)
    (hpts : PointsDetermined Δ) :
    A ⊔ B ⊔ (corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) =
      corrL A E t := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le (sup_le le_corrL S.le_corrL_right)
    (S.corrN_inf_centralizer_le_corrL htY hq)) ?_
  have h1 := card_mul_card_le_card_sup (H := A ⊔ B)
    (K := corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G))
    (by rw [inf_comm]; exact S.corrN_inf_centralizer_inf_sup_eq_bot)
  have h2 : Nat.card A * Nat.card A ≤ Nat.card ↥(A ⊔ B) := by
    have := card_mul_card_le_card_sup (S.cls.inf_eq_bot S.iso S.tri.memA S.tri.memB S.tri.ne)
    rwa [S.cls.root.card_eq S.tri.memB S.tri.memA] at this
  rw [S.card_corrL htY hq hpts]
  calc Nat.card A ^ 3 = Nat.card A * Nat.card A *
        Nat.card ↥(corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) := by
        rw [S.card_corrN_inf_centralizer_eq htY hq hpts]
        ring
    _ ≤ Nat.card ↥(A ⊔ B) *
        Nat.card ↥(corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) :=
        Nat.mul_le_mul_right _ h2
    _ ≤ _ := h1

end TriangleSetting

structure SL2Coords (A E : Subgroup G) (k : ℕ) where
  card_eq : Nat.card A = 2 ^ k
  mat : G → Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)
  mat_mul : ∀ {x y : G}, x ∈ A ⊔ E → y ∈ A ⊔ E → mat (x * y) = mat x * mat y
  mat_surj : ∀ g, ∃ x ∈ A ⊔ E, mat x = g
  mat_inj : ∀ {x : G}, x ∈ A ⊔ E → mat x = 1 → x = 1
  mem_A_iff : ∀ {x : G}, x ∈ A ⊔ E → (x ∈ A ↔ mat x ∈ lowerUnipotent (GaloisField 2 k))
  mem_E_iff : ∀ {x : G}, x ∈ A ⊔ E → (x ∈ E ↔ mat x ∈ upperUnipotent (GaloisField 2 k))

namespace SL2Coords

variable {A E : Subgroup G} {k : ℕ} (φ : SL2Coords A E k)

theorem mat_one : φ.mat 1 = 1 := by
  have h := φ.mat_mul (Subgroup.one_mem (A ⊔ E)) (Subgroup.one_mem (A ⊔ E))
  rw [one_mul] at h
  exact mul_left_cancel (a := φ.mat 1) (by rw [mul_one]; exact h.symm)

theorem mat_inv {x : G} (hx : x ∈ A ⊔ E) : φ.mat x⁻¹ = (φ.mat x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← φ.mat_mul hx (Subgroup.inv_mem _ hx), mul_inv_cancel, φ.mat_one]

theorem mat_injOn {x y : G} (hx : x ∈ A ⊔ E) (hy : y ∈ A ⊔ E) (h : φ.mat x = φ.mat y) :
    x = y := by
  have h1 := φ.mat_inj (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hx)
    (by rw [φ.mat_mul (Subgroup.inv_mem _ hy) hx, φ.mat_inv hy, h, inv_mul_cancel])
  rwa [inv_mul_eq_one, eq_comm] at h1

@[expose] def toMonoidHom : ↥(A ⊔ E) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k) where
  toFun x := φ.mat x
  map_one' := φ.mat_one
  map_mul' x y := φ.mat_mul x.2 y.2

@[expose] noncomputable def toMulEquiv :
    ↥(A ⊔ E) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k) :=
  MulEquiv.ofBijective φ.toMonoidHom
    ⟨fun x y h => Subtype.ext (φ.mat_injOn x.2 y.2 h), fun g => by
      obtain ⟨x, hx, rfl⟩ := φ.mat_surj g
      exact ⟨⟨x, hx⟩, rfl⟩⟩

@[simp] theorem toMulEquiv_apply (x : ↥(A ⊔ E)) : φ.toMulEquiv x = φ.mat x := rfl

end SL2Coords

theorem nonempty_sl2Coords [Finite G] (hR : IsRootClass Δ) {A E : Subgroup G} (hA : A ∈ Δ)
    (hE : E ∈ Δ) (hEA : Opposite E A) {k : ℕ} (hk : Nat.card A = 2 ^ k) :
    Nonempty (SL2Coords A E k) := by
  classical
  obtain ⟨n, -, hcard, φ, hφE, hφA⟩ := ARS.Opposite.exists_mulEquiv_SL2' hR hE hEA
  have hcardA : Nat.card A = 2 ^ n := by
    rw [← hcard]
    exact hR.card_eq hA hE
  obtain rfl : n = k := Nat.pow_right_injective le_rfl (hcardA.symm.trans hk)
  have hXX : ∀ {x : G}, x ∈ A ⊔ E → x ∈ E ⊔ A := fun hx => sup_comm A E ▸ hx
  let mat : G → Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) := fun x =>
    if hx : x ∈ A ⊔ E then φ ⟨x, hXX hx⟩ else 1
  have hmat : ∀ {x : G} (hx : x ∈ A ⊔ E), mat x = φ ⟨x, hXX hx⟩ := fun hx => dite_eq_left hx
  refine ⟨⟨hcardA, mat, fun {x y} hx hy => ?_, fun g => ?_, fun {x} hx h1 => ?_,
    fun {x} hx => ?_, fun {x} hx => ?_⟩⟩
  · rw [hmat hx, hmat hy, hmat (Subgroup.mul_mem _ hx hy), ← map_mul]
    rfl
  · obtain ⟨y, rfl⟩ := φ.surjective g
    have hy : (y : G) ∈ A ⊔ E := by
      rw [sup_comm]
      exact y.2
    exact ⟨y, hy, by rw [hmat hy]⟩
  · rw [hmat hx, map_eq_one_iff φ φ.injective] at h1
    exact congrArg Subtype.val h1
  · rw [hmat hx]
    exact NaturalModule.coe_mem_iff hφA ⟨x, hXX hx⟩
  · rw [hmat hx]
    exact NaturalModule.coe_mem_iff hφE ⟨x, hXX hx⟩

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G}

variable (S : TriangleSetting Δ A E B t)
include S

theorem exists_isNaturalModule_corrN_of [Finite G] (h4 : FourTerm A E t) (hq : 4 ≤ Nat.card A)
    (hZ : ∀ z : G, (∀ y ∈ A, Commute z y) → (∀ y ∈ E, Commute z y) → (∀ y ∈ B, Commute z y) →
      z = 1)
    {K : Type*} [Field K] [CharP K 2] [PerfectRing K 2]
    (φ : ↥(E ⊔ A) ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hφE : (E.subgroupOf (E ⊔ A)).map φ.toMonoidHom = upperUnipotent K) :
    ∃ θ : (Fin 2 → K) → G, IsNaturalModule φ θ ∧ Set.range θ = (corrN A E t : Set G) := by
  obtain ⟨e, he, he1⟩ := S.cls.root.exists_ne_one S.tri.memE
  set s := partnerElt A E B e with hs_def
  have hs : s ∈ corrN A E t := corrM_le_corrN (S.partnerElt_mem_corrM he he1)
  have hXN : ∀ x ∈ E ⊔ A, ∀ m ∈ corrN A E t, x * m * x⁻¹ ∈ corrN A E t := fun x hx m hm =>
    conj_mem_corrN (sup_comm E A ▸ hx) hm
  obtain ⟨θ, hθ, hrange, -⟩ := exists_natural_of_quadratic_conj φ hφE
    (fun m hm m' hm' => S.commute_of_mem_corrN h4 hq hZ hm hm') hXN
    (fun m hm hX => S.eq_one_of_mem_corrN h4 hq hZ hm
      (fun a ha => hX a (Subgroup.mem_sup_right ha)) (fun e he => hX e (Subgroup.mem_sup_left he)))
    (fun m hm e he e' he' => S.commute_commutatorElement_corrN h4 hq hm he he')
    hs (fun y hy => (S.commute_partnerElt he he1 hy).symm) (S.partnerElt_ne_one he he1)
  refine ⟨θ, hθ, ?_⟩
  rw [hrange]
  congr 1
  set W := Subgroup.closure (Set.range fun x : ↥(E ⊔ A) => (x : G) * s * (x : G)⁻¹) with hW
  have hWN : W ≤ corrN A E t := by
    rw [hW, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    exact hXN x x.2 s hs
  have hWX : ∀ x ∈ E ⊔ A, ∀ m ∈ W, x * m * x⁻¹ ∈ W := by
    intro x hx m hm
    induction hm using Subgroup.closure_induction with
    | mem m hm =>
      obtain ⟨y, rfl⟩ := hm
      exact Subgroup.subset_closure ⟨⟨x, hx⟩ * y, by simp [mul_assoc]⟩
    | one => simp
    | mul a b _ _ ha hb =>
      rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ha
  have hsW : s ∈ W := Subgroup.subset_closure ⟨1, by simp⟩
  have hFW : ∀ f ∈ graph A t, f ∈ W := by
    intro f hf
    rw [S.graph_eq_of_setting (S.partnerSetting he he1)] at hf
    obtain ⟨a, ha, rfl⟩ := (mem_graph_iff (S.partnerSetting he he1).commuting_conjSub).1 hf
    have haa : a * a = 1 := S.cls.mul_self S.tri.memA ha
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    rw [show a * (s * a * s⁻¹) = (a * s * a⁻¹) * s⁻¹ by rw [hainv]; group]
    exact Subgroup.mul_mem _ (hWX a (Subgroup.mem_sup_right ha) s hsW) (Subgroup.inv_mem _ hsW)
  refine le_antisymm hWN ((Subgroup.closure_le W).2 ?_)
  rintro _ ⟨x, hx, f, hf, rfl⟩
  exact hWX x (sup_comm A E ▸ hx) f (hFW f hf)

variable (htY : t ∈ A ⊔ E ⊔ B)
include htY

omit htY in
@[expose] noncomputable def quotX [Finite G] :
    ↥(A ⊔ E) ≃* ↥(quotMap (A ⊔ E ⊔ B) E ⊔ quotMap (A ⊔ E ⊔ B) A) :=
  MulEquiv.ofBijective
    (MonoidHom.codRestrict ((QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))).comp
      (Subgroup.inclusion (le_sup_left : A ⊔ E ≤ A ⊔ E ⊔ B))) _ fun x => by
        rw [sup_comm (quotMap (A ⊔ E ⊔ B) E), ← TriangleSetting.quotMap_sup_left]
        exact mk_mem_quotMap x.2)
    ⟨(injective_iff_map_eq_one _).2 fun x h1 => by
      have h1' : QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))
          (Subgroup.inclusion (le_sup_left : A ⊔ E ≤ A ⊔ E ⊔ B) x) = 1 :=
        congrArg Subtype.val h1
      have h2 := S.eq_one_of_mem_sup_of_mem_center x.2 ((QuotientGroup.eq_one_iff _).1 h1')
      have h3 : ((Subgroup.inclusion (le_sup_left : A ⊔ E ≤ A ⊔ E ⊔ B) x :
          ↥(A ⊔ E ⊔ B)) : G) = 1 := congrArg Subtype.val h2
      exact Subtype.ext h3,
    fun y => by
      have hy : (y : ↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B)) ∈
          quotMap (A ⊔ E ⊔ B) (A ⊔ E) := by
        rw [TriangleSetting.quotMap_sup_left, sup_comm (quotMap (A ⊔ E ⊔ B) A)]
        exact y.2
      obtain ⟨x, hx, hxy⟩ := exists_of_mem_quotMap hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

omit htY in
theorem coe_quotX [Finite G] (x : ↥(A ⊔ E)) :
    ((S.quotX x : ↥(quotMap (A ⊔ E ⊔ B) E ⊔ quotMap (A ⊔ E ⊔ B) A)) :
      ↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B)) =
      QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))
        ⟨x, (le_sup_left : A ⊔ E ≤ A ⊔ E ⊔ B) x.2⟩ := rfl

omit htY in
@[expose] noncomputable def quotSL2 [Finite G] {k : ℕ} (φ : SL2Coords A E k) :
    ↥(quotMap (A ⊔ E ⊔ B) E ⊔ quotMap (A ⊔ E ⊔ B) A) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k) :=
  S.quotX.symm.trans φ.toMulEquiv

omit htY in
theorem quotSL2_quotX [Finite G] {k : ℕ} (φ : SL2Coords A E k) (x : ↥(A ⊔ E)) :
    S.quotSL2 φ (S.quotX x) = φ.mat x := by
  rw [quotSL2, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, SL2Coords.toMulEquiv_apply]

omit htY in
theorem mem_of_mem_quotMap [Finite G] {P : Subgroup G} (hP : P ≤ A ⊔ E) (x : ↥(A ⊔ E))
    (h : QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))
      ⟨x, (le_sup_left : A ⊔ E ≤ A ⊔ E ⊔ B) x.2⟩ ∈
      quotMap (A ⊔ E ⊔ B) P) : (x : G) ∈ P := by
  obtain ⟨y, hy, hyx⟩ := exists_of_mem_quotMap h
  have hyX : (y : G) ∈ A ⊔ E := hP hy
  have h1 : S.quotX ⟨y, hyX⟩ = S.quotX x := Subtype.ext hyx
  have h2 : (⟨y, hyX⟩ : ↥(A ⊔ E)) = x := S.quotX.injective h1
  rw [← h2]
  exact hy

omit htY in
theorem map_quotSL2_E [Finite G] {k : ℕ} (φ : SL2Coords A E k) :
    ((quotMap (A ⊔ E ⊔ B) E).subgroupOf (quotMap (A ⊔ E ⊔ B) E ⊔
      quotMap (A ⊔ E ⊔ B) A)).map (S.quotSL2 φ).toMonoidHom = upperUnipotent (GaloisField 2 k) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := S.quotX.surjective y
    have hxE : (x : G) ∈ E := S.mem_of_mem_quotMap le_sup_right x (Subgroup.mem_subgroupOf.1 hy)
    show S.quotSL2 φ (S.quotX x) ∈ _
    rw [S.quotSL2_quotX]
    exact (φ.mem_E_iff x.2).1 hxE
  · intro hg
    obtain ⟨x, hx, rfl⟩ := φ.mat_surj g
    refine ⟨S.quotX ⟨x, hx⟩, ?_, S.quotSL2_quotX φ ⟨x, hx⟩⟩
    rw [Subgroup.mem_subgroupOf, S.coe_quotX]
    exact mk_mem_quotMap ((φ.mem_E_iff hx).2 hg)

omit htY in
theorem map_quotSL2_A [Finite G] {k : ℕ} (φ : SL2Coords A E k) :
    ((quotMap (A ⊔ E ⊔ B) A).subgroupOf (quotMap (A ⊔ E ⊔ B) E ⊔
      quotMap (A ⊔ E ⊔ B) A)).map (S.quotSL2 φ).toMonoidHom = lowerUnipotent (GaloisField 2 k) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := S.quotX.surjective y
    have hxA : (x : G) ∈ A := S.mem_of_mem_quotMap le_sup_left x (Subgroup.mem_subgroupOf.1 hy)
    show S.quotSL2 φ (S.quotX x) ∈ _
    rw [S.quotSL2_quotX]
    exact (φ.mem_A_iff x.2).1 hxA
  · intro hg
    obtain ⟨x, hx, rfl⟩ := φ.mat_surj g
    refine ⟨S.quotX ⟨x, hx⟩, ?_, S.quotSL2_quotX φ ⟨x, hx⟩⟩
    rw [Subgroup.mem_subgroupOf, S.coe_quotX]
    exact mk_mem_quotMap ((φ.mem_A_iff hx).2 hg)

theorem exists_isNaturalModule_quotSL2 [Finite G] (hq : 4 ≤ Nat.card A) {k : ℕ}
    (φ : SL2Coords A E k) :
    ∃ θ : (Fin 2 → GaloisField 2 k) → ↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B),
      IsNaturalModule (S.quotSL2 φ) θ ∧ Set.range θ = (corrN (quotMap (A ⊔ E ⊔ B) A)
        (quotMap (A ⊔ E ⊔ B) E) (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))
          ⟨t, htY⟩) : Set (↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B))) := by
  have hq' : 4 ≤ Nat.card (quotMap (A ⊔ E ⊔ B) A) := by rw [S.card_quotMap]; exact hq
  exact (S.quotSetting htY).exists_isNaturalModule_corrN_of (S.quotFourTerm htY) hq'
    (fun z hzA hzE hzB => S.eq_one_of_commute_quot htY (fun y hy => hzA y hy)
      (fun y hy => hzE y hy) (fun y hy => hzB y hy)) (S.quotSL2 φ) (S.map_quotSL2_E φ)

open scoped Classical in
@[expose] noncomputable def vecOf [Finite G] (hq : 4 ≤ Nat.card A) {k : ℕ} (φ : SL2Coords A E k) :
    G → (Fin 2 → GaloisField 2 k) := fun n =>
  if hn : n ∈ A ⊔ E ⊔ B then
    Function.invFun (Classical.choose (S.exists_isNaturalModule_quotSL2 htY hq φ))
      (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨n, hn⟩)
  else 0

theorem vecOf_spec [Finite G] (hq : 4 ≤ Nat.card A) {k : ℕ} (φ : SL2Coords A E k) :
    (∀ {n n' : G}, n ∈ corrN A E t → n' ∈ corrN A E t →
      S.vecOf htY hq φ (n * n') = S.vecOf htY hq φ n + S.vecOf htY hq φ n') ∧
    (∀ v, ∃ n ∈ corrN A E t, S.vecOf htY hq φ n = v) ∧
    (∀ {n : G}, n ∈ corrN A E t → (S.vecOf htY hq φ n = 0 ↔
      n ∈ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G))) ∧
    (∀ {x n : G}, x ∈ A ⊔ E → n ∈ corrN A E t → S.vecOf htY hq φ (x * n * x⁻¹) =
      (φ.mat x : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)) *ᵥ S.vecOf htY hq φ n) ∧
    (∀ {n : G}, n ∈ corrN A E t → ((∀ a ∈ A, Commute n a) ↔ S.vecOf htY hq φ n 0 = 0)) ∧
    (∀ {n : G}, n ∈ corrN A E t → ((∀ e ∈ E, Commute n e) ↔ S.vecOf htY hq φ n 1 = 0)) ∧
    Set.BijOn (S.vecOf htY hq φ) (graph A t) {v | v 0 = 0} := by
  classical
  have hNY := S.corrN_le_sup
  have hXY : A ⊔ E ≤ A ⊔ E ⊔ B := le_sup_left
  have hspec := Classical.choose_spec (S.exists_isNaturalModule_quotSL2 htY hq φ)
  set θ := Classical.choose (S.exists_isNaturalModule_quotSL2 htY hq φ) with hθdef
  obtain ⟨hθ, hrange⟩ := hspec
  have hφE := S.map_quotSL2_E φ
  have hφA := S.map_quotSL2_A φ
  have hθN : ∀ m : ↥(A ⊔ E ⊔ B), (m : G) ∈ corrN A E t →
      ∃ v, θ v = QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m := by
    intro m hm
    have h1 : QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m ∈
        (corrN (quotMap (A ⊔ E ⊔ B) A) (quotMap (A ⊔ E ⊔ B) E)
          (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨t, htY⟩) : Set _) := by
      rw [SetLike.mem_coe, ← S.quotMap_corrN htY]
      exact mk_mem_quotMap hm
    rw [← hrange] at h1
    exact h1
  have hlift : ∀ v, ∃ m : ↥(A ⊔ E ⊔ B), (m : G) ∈ corrN A E t ∧
      QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m = θ v := by
    intro v
    have h1 : θ v ∈ (corrN (quotMap (A ⊔ E ⊔ B) A) (quotMap (A ⊔ E ⊔ B) E)
        (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨t, htY⟩) : Set _) :=
      hrange ▸ ⟨v, rfl⟩
    rw [SetLike.mem_coe, ← S.quotMap_corrN htY] at h1
    exact exists_of_mem_quotMap h1
  have hvec : ∀ {n : G} (hn : n ∈ corrN A E t),
      θ (S.vecOf htY hq φ n) = QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨n, hNY hn⟩ := by
    intro n hn
    simp only [vecOf, dite_eq_left (hNY hn), ← hθdef]
    obtain ⟨v, hv⟩ := hθN ⟨n, hNY hn⟩ hn
    exact Function.invFun_eq ⟨v, hv⟩
  have hvec_iff : ∀ {n : G} (hn : n ∈ corrN A E t) (v : Fin 2 → GaloisField 2 k),
      S.vecOf htY hq φ n = v ↔
        θ v = QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨n, hNY hn⟩ := by
    intro n hn v
    rw [← hvec hn]
    exact ⟨fun h => h ▸ rfl, fun h => hθ.injective h.symm⟩
  have hF : ∀ c, ∃ f : ↥(A ⊔ E ⊔ B), (f : G) ∈ graph A t ∧
      QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) f = θ ![0, c] := by
    have hfix : ∀ f : ↥(A ⊔ E ⊔ B), (f : G) ∈ graph A t →
        ∃ c, θ ![0, c] = QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) f := by
      intro f hf
      refine (hθ.mem_fixed_lower_iff hφA le_sup_right).1
        ⟨hθN f (corrM_le_corrN (graph_le_corrM hf)), fun a ha => ?_⟩
      obtain ⟨a', ha', rfl⟩ := exists_of_mem_quotMap ha
      exact Commute.map (show Commute a' f from
        Subtype.ext (S.commute_graph_left hf ha').symm) _
    set T : Set (↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B)) :=
      (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))) ''
        ((graph A t).subgroupOf (A ⊔ E ⊔ B) : Set ↥(A ⊔ E ⊔ B)) with hT
    have hTsub : T ⊆ Set.range fun c => θ ![0, c] := by
      rintro _ ⟨f, hf, rfl⟩
      obtain ⟨c, hc⟩ := hfix f (Subgroup.mem_subgroupOf.1 hf)
      exact ⟨c, hc⟩
    have hinj : Set.InjOn (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)))
        ((graph A t).subgroupOf (A ⊔ E ⊔ B) : Set ↥(A ⊔ E ⊔ B)) := by
      intro f hf f' hf' h
      have h1 : f⁻¹ * f' ∈ Subgroup.center ↥(A ⊔ E ⊔ B) := by
        rw [← QuotientGroup.eq_one_iff]
        show QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) (f⁻¹ * f') = 1
        rw [map_mul, map_inv, h, inv_mul_cancel]
      have h2 : ((f⁻¹ * f' : ↥(A ⊔ E ⊔ B)) : G) ∈ graph A t :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hf))
          (Subgroup.mem_subgroupOf.1 hf')
      have hEY : E ≤ A ⊔ E ⊔ B := le_sup_right.trans le_sup_left
      have h3 := S.eq_one_of_mem_graph_of_commute h2 fun e he =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 h1 ⟨e, hEY he⟩)).symm
      have h4 : f⁻¹ * f' = 1 := Subtype.ext h3
      rw [inv_mul_eq_one] at h4
      exact h4
    have hk0 : k ≠ 0 := by
      intro h0
      have := φ.card_eq
      rw [h0, pow_zero] at this
      omega
    have hcardT : T.ncard = Nat.card A := by
      rw [hT, hinj.ncard_image, ← S.card_graph, ← card_subgroupOf_of_le S.graph_le_sup]
      rfl
    have hcardR : (Set.range fun c : GaloisField 2 k => θ ![0, c]).ncard = Nat.card A := by
      rw [Set.ncard_range_of_injective, GaloisField.card 2 k hk0, φ.card_eq]
      intro c c' h
      have := congrFun (hθ.injective h) 1
      simpa using this
    have heq := Set.eq_of_subset_of_ncard_le hTsub (by rw [hcardT, hcardR]) (Set.toFinite _)
    intro c
    have : θ ![0, c] ∈ T := heq ▸ ⟨c, rfl⟩
    obtain ⟨f, hf, hfc⟩ := this
    exact ⟨f, Subgroup.mem_subgroupOf.1 hf, hfc⟩
  refine ⟨fun {n n'} hn hn' => ?_, fun v => ?_, fun {n} hn => ?_, fun {x n} hx hn => ?_,
    fun {n} hn => ?_, fun {n} hn => ?_, ?_⟩
  ·
    refine (hvec_iff (Subgroup.mul_mem _ hn hn') _).2 ?_
    rw [hθ.map_add, hvec hn, hvec hn', ← map_mul]
    rfl
  ·
    obtain ⟨m, hm, hmv⟩ := hlift v
    exact ⟨m, hm, (hvec_iff hm v).2 hmv.symm⟩
  ·
    rw [hvec_iff hn, hθ.map_zero, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hc
      exact Subgroup.mem_centralizer_iff.2 fun y hy =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨y, hXY hy⟩)
    · intro hc
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (S.commute_of_mem_corrN_inf_centralizer htY hq ⟨hn, hc⟩ g.2).symm.eq
  ·
    have hxn : x * n * x⁻¹ ∈ corrN A E t := conj_mem_corrN hx hn
    refine (hvec_iff hxn _).2 ?_
    rw [← S.quotSL2_quotX φ ⟨x, hx⟩, hθ.map_mulVec, hvec hn, S.coe_quotX]
    show _ = QuotientGroup.mk' _ ((⟨x, hXY hx⟩ : ↥(A ⊔ E ⊔ B)) * ⟨n, hNY hn⟩ *
      (⟨x, hXY hx⟩ : ↥(A ⊔ E ⊔ B))⁻¹)
    rw [map_mul, map_mul, map_inv]
  ·
    rw [← hθ.forall_commute_lower_iff hφA le_sup_right, hvec hn]
    constructor
    · intro hc y hy
      obtain ⟨a, ha, rfl⟩ := exists_of_mem_quotMap hy
      exact Commute.map (show Commute a ⟨n, hNY hn⟩ from Subtype.ext (hc a ha).symm) _
    · intro hc a ha
      have hnA := S.conjSub_eq_of_forall_commute_quotMap htY ⟨n, hNY hn⟩ fun y hy =>
        (hc y hy).symm
      exact S.commute_of_conjSub_eq htY hq hn hnA ha
  ·
    rw [← hθ.forall_commute_upper_iff hφE le_sup_left, hvec hn]
    constructor
    · intro hc y hy
      obtain ⟨e, he, rfl⟩ := exists_of_mem_quotMap hy
      exact Commute.map (show Commute e ⟨n, hNY hn⟩ from Subtype.ext (hc e he).symm) _
    · intro hc e he
      have hnE := S.conjSub_E_eq_of_forall_commute_quotMap htY ⟨n, hNY hn⟩
        fun y hy => (hc y hy).symm
      exact S.commute_of_conjSub_eq_E htY hq hn hnE he
  ·
    have hFN : ∀ {f : G}, f ∈ graph A t → f ∈ corrN A E t := fun hf =>
      corrM_le_corrN (graph_le_corrM hf)
    have hEY : E ≤ A ⊔ E ⊔ B := le_sup_right.trans le_sup_left
    refine ⟨fun f hf => ?_, fun f hf f' hf' hff' => ?_, fun v hv => ?_⟩
    · show S.vecOf htY hq φ f 0 = 0
      rw [← hθ.forall_commute_lower_iff hφA le_sup_right, hvec (hFN hf)]
      intro y hy
      obtain ⟨a, ha, rfl⟩ := exists_of_mem_quotMap hy
      exact Commute.map (show Commute a ⟨f, hNY (hFN hf)⟩ from
        Subtype.ext (S.commute_graph_left hf ha).symm) _
    · have hm : f⁻¹ * f' ∈ graph A t := Subgroup.mul_mem _ (Subgroup.inv_mem _ hf) hf'
      have h1 : S.vecOf htY hq φ (f⁻¹ * f') = 0 := by
        refine (hvec_iff (hFN hm) 0).2 ?_
        rw [hθ.map_zero]
        have : (⟨f⁻¹ * f', hNY (hFN hm)⟩ : ↥(A ⊔ E ⊔ B)) =
            (⟨f, hNY (hFN hf)⟩)⁻¹ * ⟨f', hNY (hFN hf')⟩ := rfl
        rw [this, map_mul, map_inv, ← hvec (hFN hf), ← hvec (hFN hf'), hff', inv_mul_cancel]
      have h2 : f⁻¹ * f' = 1 := by
        have hc := (hvec_iff (hFN hm) 0).1 h1
        rw [hθ.map_zero, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
        exact S.eq_one_of_mem_graph_of_commute hm fun e he =>
          (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨e, hEY he⟩)).symm
      rw [inv_mul_eq_one] at h2
      exact h2
    · obtain ⟨f, hf, hfv⟩ := hF (v 1)
      refine ⟨f, hf, (hvec_iff (hFN hf) v).2 ?_⟩
      have hfv' : QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))
          (⟨(f : G), hNY (hFN hf)⟩ : ↥(A ⊔ E ⊔ B)) = θ ![0, v 1] := hfv
      rw [hfv']
      congr 1
      ext i
      fin_cases i
      · exact hv
      · rfl

@[expose] noncomputable def coordsOf [Finite G] (hq : 4 ≤ Nat.card A) {k : ℕ}
    (φ : SL2Coords A E k) :
    S.Coords where
  k := k
  card_eq := φ.card_eq
  mat := φ.mat
  mat_mul := φ.mat_mul
  mat_surj := φ.mat_surj
  mat_inj := φ.mat_inj
  mem_A_iff := φ.mem_A_iff
  mem_E_iff := φ.mem_E_iff
  vec := S.vecOf htY hq φ
  vec_mul := (S.vecOf_spec htY hq φ).1
  vec_surj := (S.vecOf_spec htY hq φ).2.1
  vec_eq_zero_iff := (S.vecOf_spec htY hq φ).2.2.1
  vec_conj := (S.vecOf_spec htY hq φ).2.2.2.1
  commute_A_iff := (S.vecOf_spec htY hq φ).2.2.2.2.1
  commute_E_iff := (S.vecOf_spec htY hq φ).2.2.2.2.2.1
  bijOn_graph := (S.vecOf_spec htY hq φ).2.2.2.2.2.2

end TriangleSetting

end CFSG.Timmesfeld.Transvection
