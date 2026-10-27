module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmD
public import Certificates.Certificate7135

public section

namespace CFSG.Quasithin.H13.KGAntiflag

open Certificates.Antiflag Matrix
open CFSG.Quasithin.SLnTwo (vec_ext_dot matOf matOf_mulVec zmod_two_cases)

section Concrete

variable {n : ℕ}

theorem getD_mem_or {α : Type*} (l : List α) (i : ℕ) (d : α) :
    l.getD i d ∈ l ∨ l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact Or.inr rfl
  | some x => exact Or.inl (List.mem_of_getElem? h)

theorem mem_globalGens {g : Pt n → Pt n} (hg : g ∈ globalGens n) :
    g = sw ∨ ∃ i j : Fin n, i ≠ j ∧ g = tv i j := by
  simp only [globalGens, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq] at hg
  rcases hg with rfl | ⟨i, j, hj, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, j, Ne.symm hj, rfl⟩

theorem mem_stabGens {g : Pt n → Pt n} (hg : g ∈ stabGens n) :
    g = sw ∨ ∃ i j : Fin n, i ≠ j ∧ i.val ≠ 0 ∧ j.val ≠ 0 ∧ g = tv i j := by
  simp only [stabGens, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq] at hg
  rcases hg with rfl | ⟨i, hi, j, ⟨hj, hj0⟩, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, j, Ne.symm hj, hi, hj0, rfl⟩

theorem tv_base {i j : Fin n} (hi : i.val ≠ 0) (hj : j.val ≠ 0) : tv i j (base n) = base n := by
  simp [tv, base, ev, hi, hj]

theorem transvection_mulVec {i j : Fin n} (x : Fin n → ZMod 2) :
    Matrix.transvection i j (1 : ZMod 2) *ᵥ x = x + Pi.single i (x j) := by
  ext k
  simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, Function.update_apply,
    Pi.single_apply]


def tSL {i j : Fin n} (hij : i ≠ j) : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  ⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j hij 1⟩

theorem tSL_mul_self {i j : Fin n} (hij : i ≠ j) : tSL hij * tSL hij = 1 := by
  apply Subtype.ext
  show Matrix.transvection i j (1 : ZMod 2) * Matrix.transvection i j 1 = 1
  rw [Matrix.transvection_mul_transvection_same i j hij, show (1 : ZMod 2) + 1 = 0 from rfl,
    Matrix.transvection_zero]

theorem graph_tSL {i j : Fin n} (hij : i ≠ j) :
    (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2) (tSL hij) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = Matrix.transvection j i 1 := by
  rw [CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix,
    inv_eq_of_mul_eq_one_right (tSL_mul_self hij)]
  show (Matrix.transvection i j (1 : ZMod 2))ᵀ = _
  rw [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
  rfl

end Concrete

section Abstract

open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}
  (S : KGH91.Setting G T L V V₁ V₂ n)

def Rep (u : G) (p : Pt n) : Prop :=
  ∃ a ∈ V₁, ∃ c ∈ V₂, u = a * c ∧ S.C₁.E a = p.1 ∧ S.C₂.E c = p.2

def Compat (m : G) (f : Pt n → Pt n) : Prop :=
  ∀ u p, Rep S u p → Rep S (m * u * m⁻¹) (f p)

theorem rep_exists (p : Pt n) : Rep S (S.C₁.inv p.1 * S.C₂.inv p.2) p :=
  ⟨_, S.C₁.inv_mem _, _, S.C₂.inv_mem _, rfl, S.C₁.E_inv _, S.C₂.E_inv _⟩

theorem rep_inj {u u' : G} {p : Pt n} (hu : Rep S u p) (hu' : Rep S u' p) : u = u' := by
  obtain ⟨a, ha, c, hc, rfl, h1, h2⟩ := hu
  obtain ⟨a', ha', c', hc', rfl, h1', h2'⟩ := hu'
  rw [S.C₁.inj a ha a' ha' (h1.trans h1'.symm), S.C₂.inj c hc c' hc' (h2.trans h2'.symm)]

theorem rep_unique {u : G} {p q : Pt n} (hp : Rep S u p) (hq : Rep S u q) : p = q := by
  obtain ⟨a, ha, c, hc, rfl, h1, h2⟩ := hp
  obtain ⟨a', ha', c', hc', he, h1', h2'⟩ := hq
  obtain ⟨rfl, rfl⟩ := S.decomp_unique ha ha' hc hc' he
  exact Prod.ext (h1.symm.trans h1') (h2.symm.trans h2')

theorem exists_rep {u : G} (hu : u ∈ V) : ∃ p, Rep S u p := by
  obtain ⟨a, ha, c, hc, rfl⟩ := S.exists_decomp hu
  exact ⟨(S.C₁.E a, S.C₂.E c), a, ha, c, hc, rfl, rfl, rfl⟩

theorem compat_one : Compat S 1 id := fun u p hu => by simpa using hu

theorem compat_mul {m m' : G} {f f' : Pt n → Pt n} (h : Compat S m f) (h' : Compat S m' f') :
    Compat S (m * m') (f ∘ f') := by
  intro u p hu
  have e : m * m' * u * (m * m')⁻¹ = m * (m' * u * m'⁻¹) * m⁻¹ := by group
  rw [e]
  exact h _ _ (h' u p hu)

theorem compat_L (l : ↥L) : Compat S l (fun p =>
    ((S.C₁.ρ l : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ p.1,
      (S.C₂.ρ l : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ p.2)) := by
  intro u p hu
  obtain ⟨a, ha, c, hc, rfl, h1, h2⟩ := hu
  refine ⟨(l : G) * a * (l : G)⁻¹, S.C₁.conj_mem l ha, (l : G) * c * (l : G)⁻¹,
    S.C₂.conj_mem l hc, by group, ?_, ?_⟩
  · rw [S.C₁.conj l a ha, h1]
  · rw [S.C₂.conj l c hc, h2]

theorem exists_compat_tv {i j : Fin n} (hij : i ≠ j) : ∃ l ∈ L, Compat S l (tv i j) := by
  obtain ⟨l, hl⟩ := S.C₁.ρ_surj (tSL hij)
  refine ⟨l, l.2, fun u p hu => ?_⟩
  have h := compat_L S l u p hu
  have e : tv i j p = ((S.C₁.ρ l : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ p.1,
      (S.C₂.ρ l : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ p.2) := by
    rw [S.dual l, hl, graph_tSL hij]
    show (p.1 + _, p.2 + _) = ((tSL hij : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ p.1, _)
    show (p.1 + _, p.2 + _) = (Matrix.transvection i j 1 *ᵥ p.1, Matrix.transvection j i 1 *ᵥ p.2)
    rw [transvection_mulVec, transvection_mulVec]
  rw [e]
  exact h

include S in
theorem exists_ne_one₂ : ∃ c ∈ V₂, c ≠ 1 := by
  have hn : 0 < n := by have := S.hn; omega
  refine ⟨S.C₂.inv (Pi.single ⟨0, hn⟩ 1), S.C₂.inv_mem _, fun h => ?_⟩
  have := S.C₂.E_inv (Pi.single ⟨0, hn⟩ 1)
  rw [h, S.C₂.E_one] at this
  have h1 := congrFun this ⟨0, hn⟩
  simp at h1

theorem exists_compat_sw (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ m ∈ L ⊔ T, Compat S m sw := by
  have : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (S.comm a.2 b.2)⟩⟩
  obtain ⟨t, htT, htN⟩ := Sec121Swap.exists_mem_not_normalizer S.hyp hTL
  have htM : t ∈ Subgroup.normalizer (L : Set G) := hTL htT
  have h₂ : ∀ c ∈ V₂, t * c * t⁻¹ ∈ V₁ := by
    rcases S.fix_or_swap htM with ⟨h, -⟩ | h
    · exact absurd h htN
    · exact fun c hc => (h.2 c).1 hc
  let φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) :=
    AddMonoidHom.mk' (fun y => S.C₁.E (t * S.C₂.inv y * t⁻¹)) fun y y' => by
      have e : t * (S.C₂.inv y * S.C₂.inv y') * t⁻¹ =
          (t * S.C₂.inv y * t⁻¹) * (t * S.C₂.inv y' * t⁻¹) := by group
      rw [S.C₂.inv_add, e, S.C₁.map_mul _ (h₂ _ (S.C₂.inv_mem y)) _ (h₂ _ (S.C₂.inv_mem y'))]
  have hφ : ∀ y, matOf φ *ᵥ y = S.C₁.E (t * S.C₂.inv y * t⁻¹) := fun y => matOf_mulVec φ y
  have hdet : (matOf φ).det = 1 := by
    rcases zmod_two_cases (matOf φ).det with h0 | h1
    · exfalso
      obtain ⟨y, hy, hy0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      rw [hφ] at hy0
      have h1 := S.C₁.eq_one_of_E (h₂ _ (S.C₂.inv_mem y)) hy0
      have h2 : S.C₂.inv y = 1 := by
        calc S.C₂.inv y = t⁻¹ * (t * S.C₂.inv y * t⁻¹) * t := by group
          _ = 1 := by rw [h1]; group
      apply hy
      rw [← S.C₂.E_inv y, h2, S.C₂.E_one]
    · exact h1
  let P : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) := ⟨matOf φ, hdet⟩
  obtain ⟨l, hl⟩ := S.C₁.ρ_surj P⁻¹
  have hPP : ((P⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) * matOf φ = 1 := by
    show ((P⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (P : Matrix (Fin n) (Fin n) (ZMod 2)) = 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hmM : (l : G) * t ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer l.2) htM
  have hc : ∀ c ∈ V₂, (l : G) * t * c * ((l : G) * t)⁻¹ ∈ V₁ ∧
      S.C₁.E ((l : G) * t * c * ((l : G) * t)⁻¹) = S.C₂.E c := by
    intro c hc
    have htc : t * c * t⁻¹ ∈ V₁ := h₂ c hc
    have e : (l : G) * t * c * ((l : G) * t)⁻¹ = (l : G) * (t * c * t⁻¹) * (l : G)⁻¹ := by
      group
    rw [e]
    refine ⟨S.C₁.conj_mem l htc, ?_⟩
    rw [S.C₁.conj l _ htc, hl]
    have h3 : S.C₁.E (t * c * t⁻¹) = matOf φ *ᵥ S.C₂.E c := by rw [hφ, S.C₂.inv_E hc]
    rw [h3, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  obtain ⟨hm₁, hm₂⟩ : (∀ a, a ∈ V₁ ↔ (l : G) * t * a * ((l : G) * t)⁻¹ ∈ V₂) ∧
      ∀ c, c ∈ V₂ ↔ (l : G) * t * c * ((l : G) * t)⁻¹ ∈ V₁ := by
    rcases S.fix_or_swap hmM with ⟨-, h⟩ | h
    · exfalso
      obtain ⟨c, hc2, hc1⟩ := exists_ne_one₂ S
      have h1 : (l : G) * t * c * ((l : G) * t)⁻¹ ∈ V₁ ⊓ V₂ :=
        ⟨(hc c hc2).1, (Subgroup.mem_normalizer_iff.1 h c).1 hc2⟩
      rw [S.hyp.inf, Subgroup.mem_bot] at h1
      apply hc1
      calc c = ((l : G) * t)⁻¹ * ((l : G) * t * c * ((l : G) * t)⁻¹) * ((l : G) * t) := by group
        _ = 1 := by rw [h1]; group
    · exact h
  have ha : ∀ a ∈ V₁, S.C₂.E ((l : G) * t * a * ((l : G) * t)⁻¹) = S.C₁.E a := by
    intro a ha
    refine vec_ext_dot fun y => ?_
    have hp := S.pairing_conj_swap hmM hm₁ hm₂ a ha (S.C₂.inv y) (S.C₂.inv_mem y)
    simp only [KGH91.pairing] at hp
    rw [(hc _ (S.C₂.inv_mem y)).2, S.C₂.E_inv] at hp
    rw [dotProduct_comm, hp, dotProduct_comm]
  refine ⟨(l : G) * t, Subgroup.mul_mem _ (Subgroup.mem_sup_left l.2)
    (Subgroup.mem_sup_right htT), fun u p hu => ?_⟩
  obtain ⟨a, ha', c, hc', rfl, h1, h2⟩ := hu
  refine ⟨(l : G) * t * c * ((l : G) * t)⁻¹, (hc c hc').1,
    (l : G) * t * a * ((l : G) * t)⁻¹, (hm₁ a).1 ha', ?_, ?_, ?_⟩
  · have e : (l : G) * t * (a * c) * ((l : G) * t)⁻¹ =
        ((l : G) * t * a * ((l : G) * t)⁻¹) * ((l : G) * t * c * ((l : G) * t)⁻¹) := by group
    rw [e, S.comm (S.le₂ ((hm₁ a).1 ha')) (S.le₁ (hc c hc').1)]
  · rw [(hc c hc').2, h2]
    rfl
  · rw [ha a ha', h1]
    rfl

theorem exists_compat_word (H : Subgroup G) (gens : List (Pt n → Pt n))
    (hg : ∀ g ∈ gens, ∃ m ∈ H, Compat S m g) (w : List ℕ) :
    ∃ m ∈ H, Compat S m (applyWord gens w) := by
  induction w with
  | nil => exact ⟨1, H.one_mem, compat_one S⟩
  | cons i w ih =>
    obtain ⟨m, hm, hmc⟩ := ih
    obtain ⟨m', hm', hm'c⟩ : ∃ m' ∈ H, Compat S m' (gens.getD i id) := by
      rcases getD_mem_or gens i id with h | h
      · exact hg _ h
      · rw [h]
        exact ⟨1, H.one_mem, compat_one S⟩
    exact ⟨m' * m, H.mul_mem hm' hm, compat_mul S hm'c hmc⟩

theorem exists_compat_globalGens (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∀ g ∈ globalGens n, ∃ m ∈ L ⊔ T, Compat S m g := by
  intro g hg
  rcases mem_globalGens hg with rfl | ⟨i, j, hij, rfl⟩
  · exact exists_compat_sw S hTL
  · obtain ⟨l, hl, hlc⟩ := exists_compat_tv S hij
    exact ⟨l, Subgroup.mem_sup_left hl, hlc⟩

theorem mem_centralizer_of_compat {m v' : G} {f : Pt n → Pt n} {p : Pt n} (hm : Compat S m f)
    (hv' : Rep S v' p) (hf : f p = p) : m ∈ Subgroup.centralizer ({v'} : Set G) := by
  have h := rep_inj S (hf ▸ hm v' p hv') hv'
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc m * v' = (m * v' * m⁻¹) * m := by group
    _ = v' * m := by rw [h]

theorem exists_compat_stabGens (hTL : T ≤ Subgroup.normalizer (L : Set G)) {v' : G}
    (hv' : Rep S v' (base n)) : ∀ g ∈ stabGens n,
      ∃ m ∈ (L ⊔ T) ⊓ Subgroup.centralizer ({v'} : Set G), Compat S m g := by
  intro g hg
  rcases mem_stabGens hg with rfl | ⟨i, j, hij, hi, hj, rfl⟩
  · obtain ⟨m, hm, hmc⟩ := exists_compat_sw S hTL
    exact ⟨m, ⟨hm, mem_centralizer_of_compat S hmc hv' rfl⟩, hmc⟩
  · obtain ⟨l, hl, hlc⟩ := exists_compat_tv S hij
    exact ⟨l, ⟨Subgroup.mem_sup_left hl, mem_centralizer_of_compat S hlc hv' (tv_base hi hj)⟩,
      hlc⟩

theorem mem_antiflags {p : Pt n} : p ∈ antiflags n ↔ p.1 ⬝ᵥ p.2 = 1 := by
  simp [antiflags]

theorem mem_antiflags_of_conj {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G)) {u : G}
    {p q : Pt n} (hu : Rep S u p) (hp : p ∈ antiflags n) (hq : Rep S (m * u * m⁻¹) q) :
    q ∈ antiflags n := by
  obtain ⟨a, ha, c, hc, rfl, h1, h2⟩ := hu
  rw [mem_antiflags, ← h1, ← h2] at hp
  have e : m * (a * c) * m⁻¹ = (m * a * m⁻¹) * (m * c * m⁻¹) := by group
  rw [e] at hq
  rw [mem_antiflags]
  rcases S.fix_or_swap hm with ⟨hn₁, hn₂⟩ | ⟨hs₁, hs₂⟩
  · have ha' : m * a * m⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.1 hn₁ a).1 ha
    have hc' : m * c * m⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.1 hn₂ c).1 hc
    have hr : Rep S ((m * a * m⁻¹) * (m * c * m⁻¹))
        (S.C₁.E (m * a * m⁻¹), S.C₂.E (m * c * m⁻¹)) := ⟨_, ha', _, hc', rfl, rfl, rfl⟩
    rw [← rep_unique S hr hq]
    have := S.pairing_conj hm hn₁ hn₂ a ha c hc
    simp only [KGH91.pairing] at this
    rw [this, hp]
  · have ha' : m * a * m⁻¹ ∈ V₂ := (hs₁ a).1 ha
    have hc' : m * c * m⁻¹ ∈ V₁ := (hs₂ c).1 hc
    have hr : Rep S ((m * a * m⁻¹) * (m * c * m⁻¹))
        (S.C₁.E (m * c * m⁻¹), S.C₂.E (m * a * m⁻¹)) :=
      ⟨_, hc', _, ha', S.comm (S.le₂ ha') (S.le₁ hc'), rfl, rfl⟩
    rw [← rep_unique S hr hq]
    have := S.pairing_conj_swap hm hs₁ hs₂ a ha c hc
    simp only [KGH91.pairing] at this
    rw [this, hp]

theorem mem_of_rep {u : G} {p : Pt n} (hu : Rep S u p) : u ∈ V := by
  obtain ⟨a, ha, c, hc, rfl, -, -⟩ := hu
  exact V.mul_mem (S.le₁ ha) (S.le₂ hc)

omit [Finite G] in
theorem mem_centralizer_of_conj_eq {x y v' : G} (h : x * v' * x⁻¹ = y * v' * y⁻¹) :
    x⁻¹ * y ∈ Subgroup.centralizer ({v'} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e : y * v' = x * v' * x⁻¹ * y := by rw [h]; group
  calc x⁻¹ * y * v' = x⁻¹ * (y * v') := by group
    _ = x⁻¹ * (x * v' * x⁻¹ * y) := by rw [e]
    _ = v' * (x⁻¹ * y) := by group

include S in
theorem base_mem : base n ∈ antiflags n := by
  have hn : 0 < n := by have := S.hn; omega
  have e : ev n 0 = Pi.single (⟨0, hn⟩ : Fin n) 1 := by
    funext i
    simp only [ev, Pi.single_apply, Fin.ext_iff]
  rw [mem_antiflags]
  show ev n 0 ⬝ᵥ ev n 0 = 1
  rw [e, dotProduct_single, Pi.single_eq_same, mul_one]

theorem le_of_facts (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hF : Facts n) {v' : G}
    (hv' : Rep S v' (base n)) (K : Subgroup G)
    (hK1 : (L ⊔ T) ⊓ Subgroup.centralizer ({v'} : Set G) ≤ K) (hK2 : K ≤ L ⊔ T)
    {k : G} (hk : k ∈ K) (hkv : k * v' * k⁻¹ ≠ v') : L ⊔ T ≤ K := by
  obtain ⟨-, -, hF3, hF4⟩ := hF
  have hLTM : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hbase := base_mem S
  have hstabK : ∀ g ∈ stabGens n, ∃ m ∈ K, Compat S m g := fun g hg => by
    obtain ⟨m, hm, hmc⟩ := exists_compat_stabGens S hTL hv' g hg
    exact ⟨m, hK1 hm, hmc⟩
  have hkV : k * v' * k⁻¹ ∈ V := S.conj_mem (hLTM (hK2 hk)) (mem_of_rep S hv')
  obtain ⟨ω, hω⟩ := exists_rep S hkV
  have hωne : ω ≠ base n := fun h => hkv (rep_inj S (h ▸ hω) hv')
  obtain ⟨r, hr, w, hw⟩ :=
    hF3 ω (mem_antiflags_of_conj S (hLTM (hK2 hk)) hv' hbase hω) hωne
  obtain ⟨h, hhK, hhc⟩ := exists_compat_word S K (stabGens n) hstabK w
  obtain ⟨w₀, hw₀, hw₀'⟩ := hF4 r hr
  obtain ⟨gr, hgrA, hgrc⟩ :=
    exists_compat_word S (L ⊔ T) (globalGens n) (exists_compat_globalGens S hTL) w₀
  have e1 : (h * gr) * v' * (h * gr)⁻¹ = k * v' * k⁻¹ := by
    have h1 := hhc _ _ (hgrc v' (base n) hv')
    rw [hw₀, hw] at h1
    have e : h * (gr * v' * gr⁻¹) * h⁻¹ = (h * gr) * v' * (h * gr)⁻¹ := by group
    rw [← e]
    exact rep_inj S h1 hω
  have hx : (h * gr)⁻¹ * k ∈ (L ⊔ T) ⊓ Subgroup.centralizer ({v'} : Set G) :=
    ⟨(L ⊔ T).mul_mem ((L ⊔ T).inv_mem ((L ⊔ T).mul_mem (hK2 hhK) hgrA)) (hK2 hk),
      mem_centralizer_of_conj_eq e1⟩
  have hgrK : gr ∈ K := by
    have := K.mul_mem (K.mul_mem (K.inv_mem hhK) hk) (K.inv_mem (hK1 hx))
    have e : h⁻¹ * k * ((h * gr)⁻¹ * k)⁻¹ = gr := by group
    rwa [e] at this
  have hextK : ∀ g ∈ stabGens n ++ [applyWord (globalGens n) w₀], ∃ m ∈ K, Compat S m g := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hstabK g hg
    · rw [List.mem_singleton] at hg
      rw [hg]
      exact ⟨gr, hgrK, hgrc⟩
  intro a ha
  have haV : a * v' * a⁻¹ ∈ V := S.conj_mem (hLTM ha) (mem_of_rep S hv')
  obtain ⟨q, hq⟩ := exists_rep S haV
  obtain ⟨w', hw'⟩ := hw₀' q (mem_antiflags_of_conj S (hLTM ha) hv' hbase hq)
  obtain ⟨κ, hκK, hκc⟩ := exists_compat_word S K _ hextK w'
  have e2 : κ * v' * κ⁻¹ = a * v' * a⁻¹ := by
    have h1 := hκc v' (base n) hv'
    rw [hw'] at h1
    exact rep_inj S h1 hq
  have hy : κ⁻¹ * a ∈ (L ⊔ T) ⊓ Subgroup.centralizer ({v'} : Set G) :=
    ⟨(L ⊔ T).mul_mem ((L ⊔ T).inv_mem (hK2 hκK)) ha, mem_centralizer_of_conj_eq e2⟩
  have := K.mul_mem hκK (hK1 hy)
  rwa [mul_inv_cancel_left] at this

theorem lem1211NormalMax_holds : Lem1211NormalMax := by
  intro G _ _ T L V V₁ V₂ n β hyp hTL hβ v hv hns
  obtain ⟨S⟩ := KGH91.Setting.nonempty hyp
  have hF : Facts n := by
    rcases hyp.rank with rfl | rfl
    · exact Certificates.certificate7135.1
    · exact Certificates.certificate7135.2
  have hne : ∃ a ∈ V₁, ∃ c ∈ V₂, β a c ≠ 0 := by
    obtain ⟨a, ha, ha1⟩ := S.exists_ne_one₁
    obtain ⟨c, hc, hac⟩ := hβ.2.2.1 a ha ha1
    exact ⟨a, ha, c, hc, by rw [hac]; exact one_ne_zero⟩
  have hβp := KGH91.eq_pairing S.hn S.C₁ S.C₂ S.dual hβ.1 hβ.2.1 hβ.2.2.2.2 hne
  obtain ⟨a₀, ha₀, c₀, hc₀, rfl, h1⟩ := hns
  have hp : (S.C₁.E a₀, S.C₂.E c₀) ∈ antiflags n := by
    rw [mem_antiflags]
    rw [hβp a₀ ha₀ c₀ hc₀] at h1
    exact h1
  have hrep : Rep S (a₀ * c₀) (S.C₁.E a₀, S.C₂.E c₀) := ⟨a₀, ha₀, c₀, hc₀, rfl, rfl, rfl⟩
  have hv' : Rep S (S.C₁.inv (base n).1 * S.C₂.inv (base n).2) (base n) := rep_exists S (base n)
  set v' := S.C₁.inv (base n).1 * S.C₂.inv (base n).2 with hv'def
  have hglob := exists_compat_globalGens S hTL (n := n)
  obtain ⟨w, hw⟩ := hF.2.1 _ hp
  obtain ⟨g, hgA, hgc⟩ := exists_compat_word S (L ⊔ T) (globalGens n) hglob w
  have hg : g * v' * g⁻¹ = a₀ * c₀ := by
    have h2 := hgc v' (base n) hv'
    rw [hw] at h2
    exact rep_inj S h2 hrep
  constructor
  ·
    rw [IsConcreteLE.lt_iff_le_and_exists]
    refine ⟨inf_le_left, ?_⟩
    have hn2 : 1 < n := by have := S.hn; omega
    obtain ⟨b, hbA, hb⟩ : ∃ b ∈ L ⊔ T, b * (a₀ * c₀) * b⁻¹ ≠ a₀ * c₀ := by
      by_cases hpb : (S.C₁.E a₀, S.C₂.E c₀) = base n
      ·
        have hr₁ : (ev n 0 + ev n 1, ev n 0) ∈ reps n := List.mem_cons_self
        obtain ⟨w₁, hw₁⟩ := hF.2.1 _ (hF.1 _ hr₁)
        obtain ⟨g₁, hg₁A, hg₁c⟩ := exists_compat_word S (L ⊔ T) (globalGens n) hglob w₁
        refine ⟨g₁ * g⁻¹, (L ⊔ T).mul_mem hg₁A ((L ⊔ T).inv_mem hgA), fun h => ?_⟩
        have h2 := hg₁c v' (base n) hv'
        rw [hw₁] at h2
        have e : g₁ * g⁻¹ * (a₀ * c₀) * (g₁ * g⁻¹)⁻¹ = g₁ * v' * g₁⁻¹ := by
          rw [← hg]
          group
        rw [e] at h
        rw [h] at h2
        have := rep_unique S h2 hrep
        rw [hpb] at this
        have h3 := congrFun (congrArg Prod.fst this) ⟨1, hn2⟩
        simp [base, ev] at h3
      · refine ⟨g⁻¹, (L ⊔ T).inv_mem hgA, fun h => hpb ?_⟩
        have e : g⁻¹ * (a₀ * c₀) * g⁻¹⁻¹ = v' := by
          rw [← hg]
          group
        rw [e] at h
        rw [← h] at hrep
        exact rep_unique S hrep hv'
    refine ⟨b, hbA, fun hb' => hb ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 hb'.2
    rw [this, mul_inv_cancel_right]
  · intro K hK1 hK2
    obtain ⟨-, k, hkK, hkN⟩ := IsConcreteLE.lt_iff_le_and_exists.1 hK1
    have hkv : k * (a₀ * c₀) * k⁻¹ ≠ a₀ * c₀ := by
      intro h
      apply hkN
      refine Subgroup.mem_inf.2 ⟨hK2 hkK, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc k * (a₀ * c₀) = (k * (a₀ * c₀) * k⁻¹) * k := by group
        _ = a₀ * c₀ * k := by rw [h]
    let K' := K.comap (MulAut.conj g).toMonoidHom
    have hmem : ∀ y, y ∈ K' ↔ g * y * g⁻¹ ∈ K := fun y => Iff.rfl
    have hK1' : (L ⊔ T) ⊓ Subgroup.centralizer ({v'} : Set G) ≤ K' := by
      intro x hx
      obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.1 hx
      rw [hmem]
      refine hK1.le (Subgroup.mem_inf.2
        ⟨(L ⊔ T).mul_mem ((L ⊔ T).mul_mem hgA hxA) ((L ⊔ T).inv_mem hgA), ?_⟩)
      rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
      rw [← hg]
      calc g * x * g⁻¹ * (g * v' * g⁻¹) = g * (x * v') * g⁻¹ := by group
        _ = g * (v' * x) * g⁻¹ := by rw [hxC]
        _ = g * v' * g⁻¹ * (g * x * g⁻¹) := by group
    have hK2' : K' ≤ L ⊔ T := by
      intro y hy
      have := (L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((L ⊔ T).inv_mem hgA) (hK2 ((hmem y).1 hy))) hgA
      have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rwa [e] at this
    have hk' : g⁻¹ * k * g ∈ K' := by
      rw [hmem]
      have e : g * (g⁻¹ * k * g) * g⁻¹ = k := by group
      rw [e]
      exact hkK
    have hkv' : (g⁻¹ * k * g) * v' * (g⁻¹ * k * g)⁻¹ ≠ v' := by
      intro h
      apply hkv
      rw [← hg]
      calc k * (g * v' * g⁻¹) * k⁻¹ = g * ((g⁻¹ * k * g) * v' * (g⁻¹ * k * g)⁻¹) * g⁻¹ := by group
        _ = g * v' * g⁻¹ := by rw [h]
    have hle := le_of_facts S hTL hF hv' K' hK1' hK2' hk' hkv'
    refine le_antisymm hK2 fun b hb => ?_
    have := (hmem _).1 (hle ((L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((L ⊔ T).inv_mem hgA) hb) hgA))
    have e : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
    rwa [e] at this

end Abstract

end CFSG.Quasithin.H13.KGAntiflag
