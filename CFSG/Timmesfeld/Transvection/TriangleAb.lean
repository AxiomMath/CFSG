module

public import CFSG.Timmesfeld.Transvection.TriangleRad
public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.RankOne
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem commute_of_mem_closure {k : Set G} (hcomm : k.Pairwise Commute) {x y : G}
    (hx : x ∈ Subgroup.closure k) (hy : y ∈ Subgroup.closure k) : Commute x y :=
  Set.centralizer_centralizer_comm_of_comm hcomm _
    (Subgroup.closure_le_centralizer_centralizer k hx) _
    (Subgroup.closure_le_centralizer_centralizer k hy)

theorem mem_conjSub_iff {H : Subgroup G} {g x : G} :
    x ∈ conjSub H g ↔ ∃ h ∈ H, x = g * h * g⁻¹ := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact conj_mem_conjSub g hh

structure TriangleSetting (Δ : Set (Subgroup G)) (A E B : Subgroup G) (t : G) : Prop where
  cls : IsTransvectionClass Δ
  iso : NoIsolated Δ
  tri : IsTriangle Δ A E B
  sq : t * t = 1
  centE : ∀ y ∈ E, Commute t y
  conjA : conjSub A t = B

@[expose] def FourTerm (A E : Subgroup G) (t : G) : Prop :=
  ∀ e ∈ E, ∀ f ∈ graph A t, ∀ f' ∈ graph A t, Commute (e * f * e * f) f'

@[expose] def corrSet (A E : Subgroup G) (t : G) : Set G :=
  {x | ∃ e ∈ E, ∃ f ∈ graph A t, x = e * f * e⁻¹}

@[expose] def corrM (A E : Subgroup G) (t : G) : Subgroup G :=
  Subgroup.closure (corrSet A E t)

@[expose] def corrLSet (A E : Subgroup G) (t : G) : Set (Subgroup G) :=
  {D | ∃ m ∈ corrM A E t, D = conjSub A m}

@[expose] def corrL (A E : Subgroup G) (t : G) : Subgroup G :=
  ⨆ D ∈ corrLSet A E t, D

@[expose] def corrRSet (A E : Subgroup G) (t : G) : Set G :=
  {g | ∃ x ∈ A ⊔ E, conjSub A x ≠ A ∧ ∃ f ∈ graph A t, g = x * f * x⁻¹}

@[expose] def corrR (A E : Subgroup G) (t : G) : Subgroup G :=
  Subgroup.closure (corrRSet A E t)

@[expose] def corrN (A E : Subgroup G) (t : G) : Subgroup G :=
  Subgroup.closure {g | ∃ x ∈ A ⊔ E, ∃ f ∈ graph A t, g = x * f * x⁻¹}

@[expose] noncomputable def partnerElt (A E B : Subgroup G) (e : G) : G :=
  e * (partner E A e * partner E B e) * e * (partner E A e * partner E B e)

section Generic

variable {A E : Subgroup G} {t : G}

theorem graph_le_corrM : graph A t ≤ corrM A E t := fun f hf =>
  Subgroup.subset_closure ⟨1, E.one_mem, f, hf, by group⟩

theorem conj_mem_corrM {e : G} (he : e ∈ E) {f : G} (hf : f ∈ graph A t) :
    e * f * e⁻¹ ∈ corrM A E t :=
  Subgroup.subset_closure ⟨e, he, f, hf, rfl⟩

theorem corrM_le_corrN : corrM A E t ≤ corrN A E t := by
  rw [corrM, Subgroup.closure_le]
  rintro _ ⟨e, he, f, hf, rfl⟩
  exact Subgroup.subset_closure ⟨e, Subgroup.mem_sup_right he, f, hf, rfl⟩

theorem conj_mem_corrN {x : G} (hx : x ∈ A ⊔ E) {n : G} (hn : n ∈ corrN A E t) :
    x * n * x⁻¹ ∈ corrN A E t := by
  induction hn using Subgroup.closure_induction with
  | mem n hn =>
    obtain ⟨y, hy, f, hf, rfl⟩ := hn
    exact Subgroup.subset_closure ⟨x * y, Subgroup.mul_mem _ hx hy, f, hf, by group⟩
  | one => simp
  | mul n n' _ _ h h' =>
    have : x * (n * n') * x⁻¹ = x * n * x⁻¹ * (x * n' * x⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ h h'
  | inv n _ h =>
    have : x * n⁻¹ * x⁻¹ = (x * n * x⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ h

theorem conjSub_corrN {x : G} (hx : x ∈ A ⊔ E) : conjSub (corrN A E t) x = corrN A E t := by
  ext y
  rw [mem_conjSub_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact conj_mem_corrN hx hn
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by group⟩
    have := conj_mem_corrN (Subgroup.inv_mem _ hx) hy
    rwa [inv_inv] at this

theorem conjSub_partner_conj (hΔ : IsTransvectionClass Δ) {A E B : Subgroup G} (hA : A ∈ Δ)
    (hE : E ∈ Δ) (hcAB : Commuting A B) (hEA : Opposite E A) (hEB : Opposite E B) {e : G}
    (he : e ∈ E) (he1 : e ≠ 1) :
    conjSub A (e * (partner E A e * partner E B e) * e) = B := by
  set a := partner E A e
  set b := partner E B e
  have ha : a ∈ A := partner_mem hEA he he1
  have hb : b ∈ B := partner_mem hEB he he1
  have haa : a * a = 1 := hΔ.mul_self hA ha
  have hee : e * e = 1 := hΔ.mul_self hE he
  have hab : a * b = b * a := (hcAB a ha b hb).eq
  rw [conjSub_mul, ← conjSub_partner hEA he he1, ← conjSub_mul]
  have h1 : e * (a * b) * a = e * b := by
    rw [hab, mul_assoc, mul_assoc, haa, mul_one]
  rw [h1, conjSub_mul, conjSub_partner hEB he he1, ← conjSub_mul, hee, conjSub_one]

theorem SL2.eq_upperElt_mul_lowerElt_mul_upperElt {K : Type*} [Field K]
    (g : Matrix.SpecialLinearGroup (Fin 2) K) (hc : g 1 0 ≠ 0) :
    g = upperElt K ((g 0 0 - 1) / g 1 0) * lowerElt K (g 1 0) *
      upperElt K ((g 1 1 - 1) / g 1 0) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [upperElt, lowerElt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination hdet | linear_combination (-1 : K) * hdet

theorem SL2.conj_upperElt_mem {K : Type*} [Field K] (g : Matrix.SpecialLinearGroup (Fin 2) K)
    (hc : g 1 0 = 0) (s : K) :
    g * upperElt K s * g⁻¹ ∈ upperUnipotent K := by
  have hdet : g 0 0 * g 1 1 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at this
    exact this
  rw [mem_upperUnipotent_iff]
  refine ⟨g 0 0 * g 0 0 * s, ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp only [upperElt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hc] <;>
    first | ring1 | linear_combination hdet

theorem exists_mul_mul_of_conjSub_ne [Finite G] (hΔ : IsTransvectionClass Δ) {A E : Subgroup G}
    (hA : A ∈ Δ) (hAE : Opposite A E) {x : G} (hx : x ∈ A ⊔ E) (hxA : conjSub A x ≠ A) :
    ∃ a ∈ A, ∃ e ∈ E, e ≠ 1 ∧ ∃ a' ∈ A, x = a * e * a' := by
  obtain ⟨n, -, -, φ, hφA, hφE⟩ := ARS.Opposite.exists_mulEquiv_SL2' hΔ.root hA hAE
  have hup : ∀ s, ((φ.symm (upperElt (GaloisField 2 n) s) : ↥(A ⊔ E)) : G) ∈ A := by
    intro s
    have hs : upperElt (GaloisField 2 n) s ∈ (A.subgroupOf (A ⊔ E)).map φ.toMonoidHom := by
      rw [hφA, mem_upperUnipotent_iff]
      exact ⟨s, rfl⟩
    obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.1 hs
    have : φ.symm (upperElt (GaloisField 2 n) s) = y := by
      rw [← hys]
      simp
    rw [this]
    exact hy
  have hlow : ∀ s, ((φ.symm (lowerElt (GaloisField 2 n) s) : ↥(A ⊔ E)) : G) ∈ E := by
    intro s
    have hs : lowerElt (GaloisField 2 n) s ∈ (E.subgroupOf (A ⊔ E)).map φ.toMonoidHom := by
      rw [hφE, mem_lowerUnipotent_iff]
      exact ⟨s, rfl⟩
    obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.1 hs
    have : φ.symm (lowerElt (GaloisField 2 n) s) = y := by
      rw [← hys]
      simp
    rw [this]
    exact hy
  set g := φ ⟨x, hx⟩ with hg
  by_cases hc : g 1 0 = 0
  · exfalso
    apply hxA
    have hle : conjSub A x ≤ A := by
      rintro _ ⟨a, ha, rfl⟩
      have hmem : φ ⟨a, Subgroup.mem_sup_left ha⟩ ∈ upperUnipotent (GaloisField 2 n) := by
        rw [← hφA]
        exact ⟨⟨a, Subgroup.mem_sup_left ha⟩, ha, rfl⟩
      obtain ⟨s, hs⟩ := (mem_upperUnipotent_iff (GaloisField 2 n)).1 hmem
      obtain ⟨s', hs'⟩ := (mem_upperUnipotent_iff (GaloisField 2 n)).1
        (SL2.conj_upperElt_mem g hc s)
      have hxa : (⟨x, hx⟩ * ⟨a, Subgroup.mem_sup_left ha⟩ * (⟨x, hx⟩ : ↥(A ⊔ E))⁻¹ : ↥(A ⊔ E)) =
          φ.symm (upperElt (GaloisField 2 n) s') := by
        rw [← hs', ← hs, hg]
        simp
      have := hup s'
      rw [← hxa] at this
      simpa using this
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (Subgroup.card_map_of_injective
      (MulAut.conj x).injective).symm)
  · have hdec := SL2.eq_upperElt_mul_lowerElt_mul_upperElt g hc
    have hx' : (⟨x, hx⟩ : ↥(A ⊔ E)) = φ.symm (upperElt (GaloisField 2 n) ((g 0 0 - 1) / g 1 0)) *
        φ.symm (lowerElt (GaloisField 2 n) (g 1 0)) *
        φ.symm (upperElt (GaloisField 2 n) ((g 1 1 - 1) / g 1 0)) := by
      rw [← map_mul, ← map_mul, ← hdec, hg]
      simp
    refine ⟨_, hup _, _, hlow (g 1 0), ?_, _, hup _, congrArg Subtype.val hx'⟩
    intro h1
    have h2 : φ.symm (lowerElt (GaloisField 2 n) (g 1 0)) = 1 := Subtype.ext h1
    rw [MulEquiv.symm_apply_eq, map_one] at h2
    have := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) => m 1 0) h2
    simp [lowerElt] at this
    exact hc this

theorem conjSub_iSup_eq {𝒮 : Set (Subgroup G)} {g : G} (h : ∀ D ∈ 𝒮, conjSub D g ∈ 𝒮)
    (h' : ∀ D ∈ 𝒮, conjSub D g⁻¹ ∈ 𝒮) : conjSub (⨆ D ∈ 𝒮, D) g = ⨆ D ∈ 𝒮, D := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun D hD => ?_)
    exact Subgroup.map_le_iff_le_comap.1 (le_iSup₂_of_le (conjSub D g) (h D hD) le_rfl)
  · refine iSup₂_le fun D hD => ?_
    have h1 : D = conjSub (conjSub D g⁻¹) g := by
      rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
    rw [h1]
    exact Subgroup.map_mono (le_iSup₂_of_le (conjSub D g⁻¹) (h' D hD) le_rfl)

theorem exists_mem_ne_ne [Finite G] {H : Subgroup G} (h : 3 ≤ Nat.card H) (x y : G) :
    ∃ z ∈ H, z ≠ x ∧ z ≠ y := by
  by_contra hcon
  push Not at hcon
  have hsub : (H : Set G) ⊆ {x, y} := by
    intro z hz
    by_cases hzx : z = x
    · exact Or.inl hzx
    · exact Or.inr (hcon z hz hzx)
  have h1 : Nat.card H = (H : Set G).ncard := (Nat.card_coe_set_eq _)
  have h2 : (H : Set G).ncard ≤ ({x, y} : Set G).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({x, y} : Set G).ncard ≤ 2 :=
    (Set.ncard_insert_le x {y}).trans (by rw [Set.ncard_singleton])
  omega

theorem commute_of_mem_iSup {𝒮 : Set (Subgroup G)} (h𝒮 : ∀ D ∈ 𝒮, ∀ D' ∈ 𝒮, Commuting D D')
    {x y : G} (hx : x ∈ ⨆ D ∈ 𝒮, D) (hy : y ∈ ⨆ D ∈ 𝒮, D) : Commute x y := by
  have hcl : (⨆ D ∈ 𝒮, D) = Subgroup.closure (⋃ D ∈ 𝒮, (D : Set G)) := by
    rw [Subgroup.closure_iUnion]
    simp only [Subgroup.closure_iUnion, Subgroup.closure_eq]
  rw [hcl] at hx hy
  refine commute_of_mem_closure ?_ hx hy
  intro u hu v hv _
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hu hv
  obtain ⟨D, hD, hu⟩ := hu
  obtain ⟨D', hD', hv⟩ := hv
  exact h𝒮 D hD D' hD' u hu v hv

theorem commute_of_mem_sup {H K : Subgroup G} (hH : Commuting H H) (hK : Commuting K K)
    (hHK : Commuting H K) {x y : G} (hx : x ∈ H ⊔ K) (hy : y ∈ H ⊔ K) : Commute x y := by
  rw [Subgroup.sup_eq_closure] at hx hy
  refine commute_of_mem_closure ?_ hx hy
  rintro u (hu | hu) v (hv | hv) -
  · exact hH u hu v hv
  · exact hHK u hu v hv
  · exact (hHK v hv u hu).symm
  · exact hK u hu v hv

theorem mem_corrLSet_self : A ∈ corrLSet A E t := ⟨1, Subgroup.one_mem _, by rw [conjSub_one]⟩

theorem conj_mem_corrR_of_conjSub_eq {y : G} (hy : y ∈ A ⊔ E) (hyA : conjSub A y = A)
    {r : G} (hr : r ∈ corrR A E t) : y * r * y⁻¹ ∈ corrR A E t := by
  have hyA' : conjSub A y⁻¹ = A := by
    conv_lhs => rw [← hyA]
    exact Aux.conjSub_conjSub_inv A y
  induction hr using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨x, hx, hxA, f, hf, rfl⟩ := hg
    refine Subgroup.subset_closure ⟨y * x, Subgroup.mul_mem _ hy hx, ?_, f, hf, by group⟩
    intro h
    apply hxA
    rw [conjSub_mul] at h
    have h' := congrArg (fun H => conjSub H y⁻¹) h
    rwa [Aux.conjSub_conjSub_inv, hyA'] at h'
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    rw [show y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ha

theorem le_corrL : A ≤ corrL A E t := le_iSup₂_of_le A mem_corrLSet_self le_rfl

theorem conjSub_sup_inf_le {N P P' : Subgroup G} {x : G} (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hxP : x ∈ P) (hP : ∀ {a b}, a ∈ P → b ∈ P → Commute a b)
    (hNP : ∀ n ∈ N, conjSub P n = P) :
    conjSub ((N ⊓ P) ⊔ (N ⊓ P')) x ≤ (N ⊓ P) ⊔ (N ⊓ P') := by
  rw [conjSub, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    refine Subgroup.mem_sup_left ⟨hxN u hu.1, ?_⟩
    show x * u * x⁻¹ ∈ P
    rw [(hP hxP hu.2).eq, mul_inv_cancel_right]
    exact hu.2
  · rintro _ ⟨v, hv, rfl⟩
    show x * v * x⁻¹ ∈ _
    have hc : x * v * x⁻¹ * v⁻¹ ∈ N ⊓ P := by
      refine ⟨N.mul_mem (hxN v hv.1) (N.inv_mem hv.1), ?_⟩
      have h1 : v * x⁻¹ * v⁻¹ ∈ P := by
        have := conj_mem_conjSub v (P.inv_mem hxP)
        rwa [hNP v hv.1] at this
      rw [show x * v * x⁻¹ * v⁻¹ = x * (v * x⁻¹ * v⁻¹) by group]
      exact P.mul_mem hxP h1
    rw [show x * v * x⁻¹ = x * v * x⁻¹ * v⁻¹ * v by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hv)

end Generic

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G} (S : TriangleSetting Δ A E B t)
include S

theorem commuting_conjSub : Commuting A (conjSub A t) := S.conjA ▸ S.tri.comm

theorem ne_conjSub : A ≠ conjSub A t := S.conjA ▸ S.tri.ne

theorem commute_graph_left {f : G} (hf : f ∈ graph A t) {y : G} (hy : y ∈ A) : Commute f y :=
  commute_of_mem_graph S.cls S.tri S.conjA hf (Or.inl hy)

theorem commute_graph_right {f : G} (hf : f ∈ graph A t) {y : G} (hy : y ∈ B) : Commute f y :=
  commute_of_mem_graph S.cls S.tri S.conjA hf (Or.inr hy)

theorem graph_mul_self {f : G} (hf : f ∈ graph A t) : f * f = 1 :=
  mul_self_of_mem_graph S.cls S.tri S.conjA hf

theorem commute_graph {f f' : G} (hf : f ∈ graph A t) (hf' : f' ∈ graph A t) :
    Commute f f' := by
  obtain ⟨a, ha, rfl⟩ := (mem_graph_iff S.commuting_conjSub).1 hf'
  have hb : t * a * t⁻¹ ∈ B := S.conjA ▸ conj_mem_conjSub t ha
  exact (S.commute_graph_left hf ha).mul_right (S.commute_graph_right hf hb)

theorem conjSub_graph_left {f : G} (hf : f ∈ graph A t) : conjSub A f = A :=
  Aux.conjSub_eq_of_commute fun _ hy => S.commute_graph_left hf hy

section StepThree

variable (h4 : FourTerm A E t)
include h4

theorem commute_conj_graph {e : G} (he : e ∈ E) {f f' : G} (hf : f ∈ graph A t)
    (hf' : f' ∈ graph A t) : Commute f' (e * f * e⁻¹) := by
  have hee := S.cls.mul_self S.tri.memE he
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have h : e * f * e⁻¹ = e * f * e * f * f := by
    rw [heinv, mul_assoc (e * f * e) f f, S.graph_mul_self hf, mul_one]
  rw [h]
  exact ((h4 e he f hf f' hf').symm).mul_right (S.commute_graph hf' hf)

theorem commute_of_mem_corrM {m m' : G} (hm : m ∈ corrM A E t) (hm' : m' ∈ corrM A E t) :
    Commute m m' := by
  refine commute_of_mem_closure ?_ hm hm'
  rintro _ ⟨e, he, f, hf, rfl⟩ _ ⟨e', he', f', hf', rfl⟩ -
  have h := (S.commute_conj_graph h4 (E.mul_mem (E.inv_mem he) he') hf' hf).map
    (MulAut.conj e).toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  have e2 : e * (e⁻¹ * e' * f' * (e⁻¹ * e')⁻¹) * e⁻¹ = e' * f' * e'⁻¹ := by group
  rwa [e2] at h

theorem conj_graph_of_mem_corrM {m : G} (hm : m ∈ corrM A E t) {f : G} (hf : f ∈ graph A t) :
    m * f * m⁻¹ = f := by
  rw [(S.commute_of_mem_corrM h4 hm (graph_le_corrM hf)).eq, mul_inv_cancel_right]

theorem commute_of_mem_conjSub_corrM {m : G} (hm : m ∈ corrM A E t) {x : G}
    (hx : x ∈ conjSub A m) {f : G} (hf : f ∈ graph A t) : Commute x f := by
  obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff.1 hx
  have h := ((S.commute_graph_left hf ha).symm).map (MulAut.conj m).toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rwa [S.conj_graph_of_mem_corrM h4 hm hf] at h

theorem commuting_conjSub_corrM [Finite G] {m : G} (hm : m ∈ corrM A E t) :
    Commuting (conjSub A m) A ∧ Commuting (conjSub A m) B := by
  have hD : conjSub A m ∈ Δ := S.cls.root.conjSub_mem S.tri.memA m
  have key : ∀ x ∈ conjSub A m, ∀ a ∈ A, Commute x a ∧ Commute x (t * a * t⁻¹) := by
    intro x hx a ha
    have hb : t * a * t⁻¹ ∈ B := S.conjA ▸ conj_mem_conjSub t ha
    by_cases hx1 : x = 1
    · subst hx1
      exact ⟨Commute.one_left a, Commute.one_left _⟩
    by_cases ha1 : a = 1
    · subst ha1
      simp
    have hb1 : t * a * t⁻¹ ≠ 1 := fun h => ha1 (conj_eq_one_iff.1 h)
    have hf : a * (t * a * t⁻¹) ∈ graph A t :=
      (mem_graph_iff S.commuting_conjSub).2 ⟨a, ha, rfl⟩
    exact (commute_mul_iff S.cls S.iso hD S.tri.memA S.tri.memB S.tri.ne S.tri.comm hx hx1 ha
      ha1 hb hb1).1 (S.commute_of_mem_conjSub_corrM h4 hm hx hf)
  refine ⟨fun x hx a ha => (key x hx a ha).1, fun x hx b hb => ?_⟩
  have ha : t⁻¹ * b * t ∈ A := by
    rw [← S.conjA] at hb
    obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff.1 hb
    rwa [show t⁻¹ * (t * a * t⁻¹) * t = a by group]
  have := (key x hx _ ha).2
  rwa [show t * (t⁻¹ * b * t) * t⁻¹ = b by group] at this

theorem commuting_conjSub_corrM_corrM [Finite G] {m m' : G} (hm : m ∈ corrM A E t)
    (hm' : m' ∈ corrM A E t) : Commuting (conjSub A m) (conjSub A m') := by
  have h := (S.commuting_conjSub_corrM h4
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hm')).1.symm.conjSub m
  rwa [← conjSub_mul, mul_inv_cancel_left] at h

end StepThree

section PartnerElt

variable [Finite G] {e : G} (he : e ∈ E) (he1 : e ≠ 1)
include he he1

theorem partner_mul_mem_graph :
    partner E A e * partner E B e ∈ graph A t := by
  have hEB : Opposite E (conjSub A t) := S.conjA ▸ S.tri.oppB
  have ha : partner E A e ∈ A := partner_mem S.tri.oppA he he1
  have hb : partner E (conjSub A t) e ∈ conjSub A t := partner_mem hEB he he1
  have h := (commuting_conjSub_iff_mem_graph S.cls S.iso S.tri.memA S.tri.memE
    S.commuting_conjSub S.ne_conjSub S.tri.oppA S.centE ha hb).1
    (commuting_conjSub_partner_mul S.cls S.tri.memA S.commuting_conjSub S.tri.oppA hEB he he1)
  rwa [S.conjA] at h

theorem conjSub_partnerElt : conjSub A (partnerElt A E B e) = B := by
  have hf := S.partner_mul_mem_graph he he1
  rw [partnerElt, conjSub_mul, S.conjSub_graph_left hf]
  exact conjSub_partner_conj S.cls S.tri.memA S.tri.memE S.tri.comm S.tri.oppA S.tri.oppB he he1

theorem partnerElt_mem_corrM : partnerElt A E B e ∈ corrM A E t := by
  have hf := S.partner_mul_mem_graph he he1
  have hee := S.cls.mul_self S.tri.memE he
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have h : partnerElt A E B e = e * (partner E A e * partner E B e) * e⁻¹ *
      (partner E A e * partner E B e) := by rw [heinv]; rfl
  rw [h]
  exact Subgroup.mul_mem _ (conj_mem_corrM he hf) (graph_le_corrM hf)

theorem commute_partnerElt {y : G} (hy : y ∈ E) :
    Commute (partnerElt A E B e) y := by
  have hf := S.partner_mul_mem_graph he he1
  set f := partner E A e * partner E B e
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right (S.graph_mul_self hf)
  have hmem : f * e * f ∈ conjSub E f := by
    have := conj_mem_conjSub f he
    rwa [hfinv] at this
  have hc : Commute (f * e * f) y :=
    commuting_conjSub_of_mem_graph S.cls S.iso S.tri S.centE S.conjA hf _ hmem y hy
  have h : partnerElt A E B e = e * (f * e * f) := by
    simp only [partnerElt, f, mul_assoc]
  rw [h]
  exact (S.cls.root.commute S.tri.memE he hy).mul_left hc

theorem partnerElt_mul_self : partnerElt A E B e * partnerElt A E B e = 1 :=
  commutator_mul_self S.cls S.iso S.tri S.centE S.conjA he (S.partner_mul_mem_graph he he1)

theorem partnerElt_ne_one : partnerElt A E B e ≠ 1 := by
  intro h
  have := S.conjSub_partnerElt he he1
  rw [h, conjSub_one] at this
  exact S.tri.ne this

end PartnerElt

theorem partnerSetting [Finite G] {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    TriangleSetting Δ A E B (partnerElt A E B e) :=
  ⟨S.cls, S.iso, S.tri, S.partnerElt_mul_self he he1, fun _ hy => S.commute_partnerElt he he1 hy,
    S.conjSub_partnerElt he he1⟩

theorem graph_eq_of_setting [Finite G] {s : G} (S' : TriangleSetting Δ A E B s) :
    graph A t = graph A s := by
  have key : ∀ {t s : G}, TriangleSetting Δ A E B t → TriangleSetting Δ A E B s →
      graph A t ≤ graph A s := by
    intro t s S S' f hf
    obtain ⟨a, ha, rfl⟩ := (mem_graph_iff S.commuting_conjSub).1 hf
    have hb : t * a * t⁻¹ ∈ conjSub A s := by
      rw [S'.conjA, ← S.conjA]
      exact conj_mem_conjSub t ha
    exact (commuting_conjSub_iff_mem_graph S'.cls S'.iso S.tri.memA S.tri.memE
      S'.commuting_conjSub S'.ne_conjSub S.tri.oppA S'.centE ha hb).1
      ((commuting_conjSub_iff_mem_graph S.cls S.iso S.tri.memA S.tri.memE S.commuting_conjSub
        S.ne_conjSub S.tri.oppA S.centE ha (conj_mem_conjSub t ha)).2 hf)
  exact le_antisymm (key S S') (key S' S)

theorem conjSub_ne_of_mem {e : G} (he : e ∈ E) (he1 : e ≠ 1) : conjSub A e ≠ A :=
  fun h => he1 (S.tri.oppA.eq_one_of_conjSub_eq he h)

section StepFive

variable [Finite G] (h4 : FourTerm A E t)
include h4

theorem conjSub_mem_corrLSet_of_mem_corrRSet {g : G} (hg : g ∈ corrRSet A E t)
    {D : Subgroup G} (hD : D ∈ corrLSet A E t) : conjSub D g ∈ corrLSet A E t := by
  obtain ⟨x, hx, hxA, f, hf, rfl⟩ := hg
  obtain ⟨a, ha, e, he, -, a', ha', rfl⟩ :=
    exists_mul_mul_of_conjSub_ne S.cls S.tri.memA S.tri.oppA.symm hx hxA
  obtain ⟨m, hm, rfl⟩ := hD
  have hu : e * f * e⁻¹ ∈ corrM A E t := conj_mem_corrM he hf
  have hfix : ∀ {m'}, m' ∈ corrM A E t → ∀ {y}, y ∈ A →
      conjSub (conjSub A m') y = conjSub A m' := fun hm' y hy =>
    Aux.conjSub_eq_of_commute fun z hz => ((S.commuting_conjSub_corrM h4 hm').1 z hz y hy).symm
  have hx' : a * e * a' * f * (a * e * a')⁻¹ = a * (e * f * e⁻¹) * a⁻¹ := by
    have h1 : a' * f * a'⁻¹ = f := by
      rw [← (S.commute_graph_left hf ha').eq, mul_inv_cancel_right]
    calc a * e * a' * f * (a * e * a')⁻¹ = a * e * (a' * f * a'⁻¹) * e⁻¹ * a⁻¹ := by group
      _ = a * (e * f * e⁻¹) * a⁻¹ := by rw [h1]; group
  refine ⟨e * f * e⁻¹ * m, Subgroup.mul_mem _ hu hm, ?_⟩
  rw [hx', conjSub_mul, conjSub_mul, hfix hm (A.inv_mem ha), ← conjSub_mul A (e * f * e⁻¹) m,
    hfix (Subgroup.mul_mem _ hu hm) ha]

theorem conjSub_mem_corrLSet_of_mem_corrR {r : G} (hr : r ∈ corrR A E t) :
    ∀ D ∈ corrLSet A E t, conjSub D r ∈ corrLSet A E t ∧ conjSub D r⁻¹ ∈ corrLSet A E t := by
  induction hr using Subgroup.closure_induction with
  | mem g hg =>
    have hginv : g⁻¹ ∈ corrRSet A E t := by
      obtain ⟨x, hx, hxA, f, hf, rfl⟩ := hg
      refine ⟨x, hx, hxA, f, hf, ?_⟩
      rw [show (x * f * x⁻¹)⁻¹ = x * f⁻¹ * x⁻¹ by group,
        inv_eq_of_mul_eq_one_right (S.graph_mul_self hf)]
    exact fun D hD => ⟨S.conjSub_mem_corrLSet_of_mem_corrRSet h4 hg hD,
      S.conjSub_mem_corrLSet_of_mem_corrRSet h4 hginv hD⟩
  | one =>
    intro D hD
    rw [inv_one, conjSub_one]
    exact ⟨hD, hD⟩
  | mul x y _ _ hx hy =>
    intro D hD
    constructor
    · rw [conjSub_mul]
      exact (hx _ (hy D hD).1).1
    · rw [mul_inv_rev, conjSub_mul]
      exact (hy _ (hx D hD).2).2
  | inv x _ hx =>
    intro D hD
    rw [inv_inv]
    exact ⟨(hx D hD).2, (hx D hD).1⟩

theorem conjSub_corrL_of_mem_corrR {r : G} (hr : r ∈ corrR A E t) :
    conjSub (corrL A E t) r = corrL A E t :=
  conjSub_iSup_eq (fun D hD => (S.conjSub_mem_corrLSet_of_mem_corrR h4 hr D hD).1)
    (fun D hD => (S.conjSub_mem_corrLSet_of_mem_corrR h4 hr D hD).2)

theorem graph_le_corrR (hq : 4 ≤ Nat.card A) : graph A t ≤ corrR A E t := by
  intro f hf
  have hcard : Nat.card E = Nat.card A := S.cls.root.card_eq S.tri.memE S.tri.memA
  obtain ⟨e₁, he₁, he₁1, -⟩ := exists_mem_ne_ne (H := E) (by omega) 1 1
  obtain ⟨e₂, he₂, he₂1, he₂₁⟩ := exists_mem_ne_ne (H := E) (by omega) 1 e₁
  have hee₁ := S.cls.mul_self S.tri.memE he₁
  have hee₂ := S.cls.mul_self S.tri.memE he₂
  have hff := S.graph_mul_self hf
  have he₁inv : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right hee₁
  have he₂inv : e₂⁻¹ = e₂ := inv_eq_of_mul_eq_one_right hee₂
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have h12 : Commute e₁ e₂ := S.cls.root.commute S.tri.memE he₁ he₂
  have he12 : e₁ * e₂ ∈ E := E.mul_mem he₁ he₂
  have he121 : e₁ * e₂ ≠ 1 := by
    intro h
    apply he₂₁
    have := eq_inv_of_mul_eq_one_right h
    rw [this, he₁inv]
  have hmem : ∀ {e}, e ∈ E → e ≠ 1 → e * f * e⁻¹ ∈ corrR A E t := fun he he1 =>
    Subgroup.subset_closure ⟨_, Subgroup.mem_sup_right he, S.conjSub_ne_of_mem he he1, f, hf, rfl⟩
  have hα : Commute (f * e₁ * f) e₂ := by
    have hm : f * e₁ * f ∈ conjSub E f := by
      have := conj_mem_conjSub f he₁
      rwa [hfinv] at this
    exact commuting_conjSub_of_mem_graph S.cls S.iso S.tri S.centE S.conjA hf _ hm e₂ he₂
  have hS3 : Commute f (e₂ * f * e₂⁻¹) := S.commute_conj_graph h4 he₂ hf hf
  have key : (e₁ * e₂) * f * (e₁ * e₂)⁻¹ * f = (e₁ * f * e₁⁻¹) * (e₂ * f * e₂⁻¹) := by
    rw [mul_inv_rev, he₁inv, he₂inv, ← h12.eq]
    calc e₁ * e₂ * f * (e₁ * e₂) * f = e₁ * e₂ * (f * e₁ * f) * (f * e₂ * f) := by
          rw [show e₁ * e₂ * (f * e₁ * f) * (f * e₂ * f) =
            e₁ * e₂ * f * e₁ * (f * f) * e₂ * f by group, hff]
          group
      _ = e₁ * (f * e₁ * f) * e₂ * (f * e₂ * f) := by
          rw [mul_assoc e₁ e₂, hα.symm.eq]
          group
      _ = (e₁ * f * e₁) * (f * (e₂ * f * e₂)) * f := by group
      _ = (e₁ * f * e₁) * ((e₂ * f * e₂) * f) * f := by
          rw [show e₂ * f * e₂ = e₂ * f * e₂⁻¹ by rw [he₂inv], hS3.eq]
      _ = (e₁ * f * e₁) * (e₂ * f * e₂) := by
          rw [mul_assoc (e₁ * f * e₁), mul_assoc (e₂ * f * e₂), hff, mul_one]
  have hfeq : f = ((e₁ * e₂) * f * (e₁ * e₂)⁻¹)⁻¹ * ((e₁ * f * e₁⁻¹) * (e₂ * f * e₂⁻¹)) :=
    eq_inv_mul_of_mul_eq key
  rw [hfeq]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hmem he12 he121))
    (Subgroup.mul_mem _ (hmem he₁ he₁1) (hmem he₂ he₂1))

theorem corrM_le_corrR (hq : 4 ≤ Nat.card A) : corrM A E t ≤ corrR A E t := by
  rw [corrM, Subgroup.closure_le]
  rintro _ ⟨e, he, f, hf, rfl⟩
  by_cases he1 : e = 1
  · subst he1
    rw [one_mul, inv_one, mul_one]
    exact S.graph_le_corrR h4 hq hf
  · exact Subgroup.subset_closure ⟨e, Subgroup.mem_sup_right he, S.conjSub_ne_of_mem he he1, f,
      hf, rfl⟩

theorem conjSub_corrL_of_conjSub_eq (hq : 4 ≤ Nat.card A) {y : G} (hy : y ∈ A ⊔ E)
    (hyA : conjSub A y = A) : conjSub (corrL A E t) y = corrL A E t := by
  have hmap : ∀ {z}, z ∈ A ⊔ E → conjSub A z = A →
      ∀ D ∈ corrLSet A E t, conjSub D z ∈ corrLSet A E t := by
    intro z hz hzA D hD
    obtain ⟨m, hm, rfl⟩ := hD
    have hr : z * m * z⁻¹ ∈ corrR A E t :=
      conj_mem_corrR_of_conjSub_eq hz hzA (S.corrM_le_corrR h4 hq hm)
    have h2 : z * m = z * m * z⁻¹ * z := by group
    have h1 : conjSub (conjSub A m) z = conjSub A (z * m * z⁻¹) := by
      calc conjSub (conjSub A m) z = conjSub A (z * m) := (conjSub_mul A z m).symm
        _ = conjSub A (z * m * z⁻¹ * z) := by rw [← h2]
        _ = conjSub (conjSub A z) (z * m * z⁻¹) := conjSub_mul A _ _
        _ = conjSub A (z * m * z⁻¹) := by rw [hzA]
    rw [h1]
    exact (S.conjSub_mem_corrLSet_of_mem_corrR h4 hr A mem_corrLSet_self).1
  have hyA' : conjSub A y⁻¹ = A := by
    conv_lhs => rw [← hyA]
    exact Aux.conjSub_conjSub_inv A y
  exact conjSub_iSup_eq (hmap hy hyA) (hmap (Subgroup.inv_mem _ hy) hyA')

theorem conjSub_corrL_of_mem_corrN (hq : 4 ≤ Nat.card A) {n : G} (hn : n ∈ corrN A E t) :
    conjSub (corrL A E t) n = corrL A E t := by
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨x, hx, f, hf, rfl⟩ := hg
    by_cases hxA : conjSub A x = A
    · have hxA' : conjSub A x⁻¹ = A := by
        conv_lhs => rw [← hxA]
        exact Aux.conjSub_conjSub_inv A x
      rw [conjSub_mul, conjSub_mul,
        S.conjSub_corrL_of_conjSub_eq h4 hq (Subgroup.inv_mem _ hx) hxA',
        S.conjSub_corrL_of_mem_corrR h4 (S.graph_le_corrR h4 hq hf),
        S.conjSub_corrL_of_conjSub_eq h4 hq hx hxA]
    · exact S.conjSub_corrL_of_mem_corrR h4 (Subgroup.subset_closure ⟨x, hx, hxA, f, hf, rfl⟩)
  | one => rw [conjSub_one]
  | mul a b _ _ ha hb => rw [conjSub_mul, hb, ha]
  | inv a _ ha =>
    conv_lhs => rw [← ha]
    exact Aux.conjSub_conjSub_inv _ a

theorem commute_of_mem_corrL {x y : G} (hx : x ∈ corrL A E t) (hy : y ∈ corrL A E t) :
    Commute x y := by
  refine commute_of_mem_iSup ?_ hx hy
  rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩
  exact S.commuting_conjSub_corrM_corrM h4 hm hm'

end StepFive

theorem exists_conjSub_eq_E : ∃ w ∈ A ⊔ E, conjSub A w = E := by
  obtain ⟨e, he, he1⟩ := S.cls.root.exists_ne_one S.tri.memE
  refine ⟨(partner E A e)⁻¹ * e, Subgroup.mul_mem _
    (Subgroup.inv_mem _ (Subgroup.mem_sup_left (partner_mem S.tri.oppA he he1)))
    (Subgroup.mem_sup_right he), ?_⟩
  rw [conjSub_mul, ← conjSub_partner S.tri.oppA he he1, Aux.conjSub_conjSub_inv]

section EndFourThree

variable [Finite G] (h4 : FourTerm A E t) (hq : 4 ≤ Nat.card A)
  (hZ : ∀ z : G, (∀ y ∈ A, Commute z y) → (∀ y ∈ E, Commute z y) → (∀ y ∈ B, Commute z y) →
    z = 1)
include h4 hq hZ

omit h4 hq hZ in
theorem le_corrL_right : B ≤ corrL A E t := by
  obtain ⟨e, he, he1⟩ := S.cls.root.exists_ne_one S.tri.memE
  refine le_iSup₂_of_le B ⟨partnerElt A E B e, S.partnerElt_mem_corrM he he1, ?_⟩ le_rfl
  rw [S.conjSub_partnerElt he he1]

omit hZ in
theorem conjSub_conjSub_corrL {w : G} (hw : w ∈ A ⊔ E) {n : G} (hn : n ∈ corrN A E t) :
    conjSub (conjSub (corrL A E t) w) n = conjSub (corrL A E t) w := by
  have hn' : w⁻¹ * n * w ∈ corrN A E t := by
    have := conj_mem_corrN (Subgroup.inv_mem _ hw) hn
    rwa [inv_inv] at this
  rw [← conjSub_mul, show n * w = w * (w⁻¹ * n * w) by group, conjSub_mul,
    S.conjSub_corrL_of_mem_corrN h4 hq hn']

theorem commute_of_mem_inf {w : G} (hw : w ∈ A ⊔ E) (hwE : conjSub A w = E) {u v : G}
    (hu : u ∈ corrN A E t ⊓ corrL A E t)
    (hv : v ∈ corrN A E t ⊓ conjSub (corrL A E t) w) : Commute u v := by
  set L := corrL A E t
  set L' := conjSub L w
  have hL : ∀ {x y}, x ∈ L → y ∈ L → Commute x y := fun hx hy =>
    S.commute_of_mem_corrL h4 hx hy
  have hL' : ∀ {x y}, x ∈ L' → y ∈ L' → Commute x y := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact (hL hx hy).map (MulAut.conj w).toMonoidHom
  have hEL' : E ≤ L' := hwE ▸ Subgroup.map_mono le_corrL
  set c := u * v * u⁻¹ * v⁻¹ with hc
  have hcN : c ∈ corrN A E t :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu.1 hv.1)
      (Subgroup.inv_mem _ hu.1)) (Subgroup.inv_mem _ hv.1)
  have hcL : c ∈ L := by
    have h1 : v * u⁻¹ * v⁻¹ ∈ L := by
      have := conj_mem_conjSub v (L.inv_mem hu.2)
      rwa [S.conjSub_corrL_of_mem_corrN h4 hq hv.1] at this
    rw [hc, show u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) by group]
    exact L.mul_mem hu.2 h1
  have hcL' : c ∈ L' := by
    have h1 : u * v * u⁻¹ ∈ L' := by
      have := conj_mem_conjSub u hv.2
      rwa [S.conjSub_conjSub_corrL h4 hq hw hu.1] at this
    exact L'.mul_mem h1 (L'.inv_mem hv.2)
  have hc1 : c = 1 := hZ c (fun y hy => hL hcL (le_corrL hy))
    (fun y hy => hL' hcL' (hEL' hy)) (fun y hy => hL hcL (S.le_corrL_right hy))
  rw [hc] at hc1
  calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
    _ = v * u := by rw [hc1, one_mul]

omit hZ in
theorem corrN_eq_sup {w : G} (hw : w ∈ A ⊔ E) (hwE : conjSub A w = E) :
    corrN A E t = (corrN A E t ⊓ corrL A E t) ⊔ (corrN A E t ⊓ conjSub (corrL A E t) w) := by
  set N := corrN A E t
  set L := corrL A E t
  set L' := conjSub L w
  set N₀ := (N ⊓ L) ⊔ (N ⊓ L')
  have hL : ∀ {x y}, x ∈ L → y ∈ L → Commute x y := fun hx hy =>
    S.commute_of_mem_corrL h4 hx hy
  have hL' : ∀ {x y}, x ∈ L' → y ∈ L' → Commute x y := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact (hL hx hy).map (MulAut.conj w).toMonoidHom
  have hEL' : E ≤ L' := hwE ▸ Subgroup.map_mono le_corrL
  have hN₀N : N₀ ≤ N := sup_le inf_le_left inf_le_left
  have hcardeq : ∀ x : G, Nat.card (conjSub N₀ x) = Nat.card N₀ := fun x =>
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hnorm : ∀ x ∈ (A : Set G) ∪ E, conjSub N₀ x = N₀ := by
    rintro x (hx | hx)
    · exact Subgroup.eq_of_le_of_card_ge (conjSub_sup_inf_le
        (fun n hn => conj_mem_corrN (Subgroup.mem_sup_left hx) hn) (le_corrL hx) hL
        (fun n hn => S.conjSub_corrL_of_mem_corrN h4 hq hn)) (hcardeq x).ge
    · have h := conjSub_sup_inf_le (N := N) (P := L') (P' := L)
        (fun n hn => conj_mem_corrN (Subgroup.mem_sup_right hx) hn) (hEL' hx) hL'
        (fun n hn => S.conjSub_conjSub_corrL h4 hq hw hn)
      rw [sup_comm] at h
      exact Subgroup.eq_of_le_of_card_ge h (hcardeq x).ge
  have hnormX : ∀ x ∈ A ⊔ E, conjSub N₀ x = N₀ := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hnorm x hx
    | one => rw [conjSub_one]
    | mul a b _ _ ha hb => rw [conjSub_mul, hb, ha]
    | inv a _ ha =>
      conv_lhs => rw [← ha]
      exact Aux.conjSub_conjSub_inv _ a
  have hF : ∀ f ∈ graph A t, f ∈ N₀ := by
    intro f hf
    refine Subgroup.mem_sup_left ⟨Subgroup.subset_closure ⟨1, Subgroup.one_mem _, f, hf,
      by group⟩, ?_⟩
    obtain ⟨a, ha, rfl⟩ := (mem_graph_iff S.commuting_conjSub).1 hf
    exact L.mul_mem (le_corrL ha) (S.le_corrL_right (S.conjA ▸ conj_mem_conjSub t ha))
  refine le_antisymm ((Subgroup.closure_le N₀).2 ?_) hN₀N
  rintro _ ⟨x, hx, f, hf, rfl⟩
  rw [SetLike.mem_coe, ← hnormX x hx]
  exact conj_mem_conjSub x (hF f hf)

theorem commute_of_mem_corrN {x y : G} (hx : x ∈ corrN A E t) (hy : y ∈ corrN A E t) :
    Commute x y := by
  obtain ⟨w, hw, hwE⟩ := S.exists_conjSub_eq_E
  rw [S.corrN_eq_sup h4 hq hw hwE] at hx hy
  refine commute_of_mem_sup ?_ ?_ ?_ hx hy
  · intro u hu v hv
    exact S.commute_of_mem_corrL h4 hu.2 hv.2
  · rintro _ ⟨hu, ⟨u, hu', rfl⟩⟩ _ ⟨hv, ⟨v, hv', rfl⟩⟩
    exact (S.commute_of_mem_corrL h4 hu' hv').map (MulAut.conj w).toMonoidHom
  · intro u hu v hv
    exact S.commute_of_mem_inf h4 hq hZ hw hwE hu hv

theorem eq_one_of_mem_corrN {n : G} (hn : n ∈ corrN A E t) (hnA : ∀ a ∈ A, Commute a n)
    (hnE : ∀ e ∈ E, Commute e n) : n = 1 := by
  obtain ⟨e, he, he1⟩ := S.cls.root.exists_ne_one S.tri.memE
  have hs : partnerElt A E B e ∈ corrN A E t :=
    corrM_le_corrN (S.partnerElt_mem_corrM he he1)
  have hns : Commute n (partnerElt A E B e) := S.commute_of_mem_corrN h4 hq hZ hn hs
  refine hZ n (fun y hy => (hnA y hy).symm) (fun y hy => (hnE y hy).symm) (fun y hy => ?_)
  rw [← S.conjSub_partnerElt he he1] at hy
  obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff.1 hy
  exact (hns.mul_right (hnA a ha).symm).mul_right hns.inv_right

omit hZ in
theorem commute_commutatorElement_corrN {n : G} (hn : n ∈ corrN A E t) {e e' : G} (he : e ∈ E)
    (he' : e' ∈ E) : Commute e' ⁅e, n⁆ := by
  obtain ⟨w, hw, hwE⟩ := S.exists_conjSub_eq_E
  set L' := conjSub (corrL A E t) w
  have hL' : ∀ {x y}, x ∈ L' → y ∈ L' → Commute x y := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact (S.commute_of_mem_corrL h4 hx hy).map (MulAut.conj w).toMonoidHom
  have hEL' : E ≤ L' := hwE ▸ Subgroup.map_mono le_corrL
  have h1 : n * e⁻¹ * n⁻¹ ∈ L' := by
    have := conj_mem_conjSub n (L'.inv_mem (hEL' he))
    rwa [S.conjSub_conjSub_corrL h4 hq hw hn] at this
  have hmem : ⁅e, n⁆ ∈ L' := by
    rw [commutatorElement_def, show e * n * e⁻¹ * n⁻¹ = e * (n * e⁻¹ * n⁻¹) by group]
    exact L'.mul_mem (hEL' he) h1
  exact hL' (hEL' he') hmem

theorem exists_isNaturalModule_corrN : ∃ n : ℕ, Nat.card A = 2 ^ n ∧
    ∃ φ : ↥(E ⊔ A) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      (E.subgroupOf (E ⊔ A)).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
      (A.subgroupOf (E ⊔ A)).map φ.toMonoidHom = lowerUnipotent (GaloisField 2 n) ∧
      ∃ θ : (Fin 2 → GaloisField 2 n) → G, IsNaturalModule φ θ ∧
        Set.range θ = (corrN A E t : Set G) := by
  obtain ⟨n, -, hcard, φ, hφE, hφA⟩ :=
    ARS.Opposite.exists_mulEquiv_SL2' S.cls.root S.tri.memE S.tri.oppA
  have hcardA : Nat.card A = 2 ^ n := by
    rw [← hcard]
    exact S.cls.root.card_eq S.tri.memA S.tri.memE
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
  refine ⟨n, hcardA, φ, hφE, hφA, θ, hθ, ?_⟩
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

end EndFourThree

end TriangleSetting

end CFSG.Timmesfeld.Transvection
