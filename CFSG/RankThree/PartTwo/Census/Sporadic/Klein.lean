module

public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Coxeter

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.QuasithinUnique.SQTK
open scoped commutatorElement

section Klein

variable {G : Type} [Group G]

theorem sq_eq_one_of_mem_closure_pair {a b : G} (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hab : a * b = b * a) {g : G} (hg : g ∈ Subgroup.closure ({a, b} : Set G)) : g ^ 2 = 1 := by
  have hcomm : ({a, b} : Set G).Pairwise Commute := by
    rintro x (rfl | rfl) y (rfl | rfl) -
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have : IsMulCommutative (Subgroup.closure ({a, b} : Set G)) :=
    Subgroup.isMulCommutative_closure hcomm
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ha2
    · exact hb2
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x :=
      congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Subgroup.closure ({a, b} : Set G)) ⟨y, hy⟩)
    rw [(Commute.mul_pow hxy 2), ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem conj_mem_closure_pair {a b x : G}
    (hxa : x * a * x⁻¹ ∈ Subgroup.closure ({a, b} : Set G))
    (hxb : x * b * x⁻¹ ∈ Subgroup.closure ({a, b} : Set G)) {g : G}
    (hg : g ∈ Subgroup.closure ({a, b} : Set G)) :
    x * g * x⁻¹ ∈ Subgroup.closure ({a, b} : Set G) := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact hxa
    · exact hxb
  | one => simp
  | mul y z _ _ ihy ihz =>
    have h := Subgroup.mul_mem _ ihy ihz
    rwa [show x * y * x⁻¹ * (x * z * x⁻¹) = x * (y * z) * x⁻¹ by group] at h
  | inv y _ ihy =>
    have h := Subgroup.inv_mem _ ihy
    rwa [show (x * y * x⁻¹)⁻¹ = x * y⁻¹ * x⁻¹ by group] at h

variable [Finite G]

theorem four_le_localRank_three_of_klein (x : Fin 4 → G)
    (φ : (Fin 4 → Multiplicative (ZMod 3)) →* G) (hφ : Function.Injective φ)
    (hφs : ∀ i a, φ (Pi.mulSingle i a) = x i ^ (Multiplicative.toAdd a).val)
    {a b : G} (ha : a ≠ 1) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (hx0 : x 0 ^ 3 = 1)
    (h0a : x 0 * a * (x 0)⁻¹ = b * a) (h0b : x 0 * b * (x 0)⁻¹ = a)
    (hxa : ∀ i, i ≠ 0 → x i * a = a * x i) (hxb : ∀ i, i ≠ 0 → x i * b = b * x i) :
    4 ≤ localRank 3 G := by
  set V := Subgroup.closure ({a, b} : Set G) with hVdef
  have haV : a ∈ V := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbV : b ∈ V := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hab : a * b = b * a := by
    have h3 : x 0 * (x 0 * (x 0 * b * (x 0)⁻¹) * (x 0)⁻¹) * (x 0)⁻¹ = a * (b * a) := by
      rw [h0b, h0a, show x 0 * (b * a) * (x 0)⁻¹ = (x 0 * b * (x 0)⁻¹) * (x 0 * a * (x 0)⁻¹) by
        group, h0b, h0a]
    have hx0' : x 0 * x 0 * x 0 = 1 := by rw [← pow_three', hx0]
    have h3' : x 0 * (x 0 * (x 0 * b * (x 0)⁻¹) * (x 0)⁻¹) * (x 0)⁻¹ =
        (x 0 * x 0 * x 0) * b * (x 0 * x 0 * x 0)⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    rw [h3', hx0', one_mul, inv_one, mul_one] at h3
    have ha' : a * a = 1 := by rw [← sq, ha2]
    calc a * b = a * (a * (b * a)) := by rw [← h3]
      _ = (a * a) * (b * a) := by group
      _ = b * a := by rw [ha', one_mul]
  have hV1 : V ≠ ⊥ := fun h => ha ((Subgroup.mem_bot).1 (h ▸ haV))
  have hV2 : IsPGroup 2 V := fun g =>
    ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact sq_eq_one_of_mem_closure_pair ha2 hb2 hab g.2)⟩
  set E := φ.range
  have hE : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun g h => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨f, hf⟩ := MonoidHom.mem_range.1 g.2
      obtain ⟨f', hf'⟩ := MonoidHom.mem_range.1 h.2
      apply Subtype.ext
      change (g : G) * h = h * g
      rw [← hf, ← hf', ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨f, rfl⟩ := MonoidHom.mem_range.1 hy
      have : f ^ 3 = 1 := by
        funext i
        rw [Pi.pow_apply, Pi.one_apply]
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one]
        generalize Multiplicative.toAdd (f i) = z
        revert z
        decide
      rw [← map_pow, this, map_one]
  have hEc : Nat.card E = 3 ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hxN : ∀ i, x i ∈ Subgroup.normalizer (V : Set G) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      have hfwd : ∀ g ∈ V, x 0 * g * (x 0)⁻¹ ∈ V := fun g hg =>
        conj_mem_closure_pair (by rw [h0a]; exact V.mul_mem hbV haV) (by rw [h0b]; exact haV) hg
      have hinv : (x 0)⁻¹ = x 0 * x 0 := by
        rw [inv_eq_iff_mul_eq_one, ← pow_three, hx0]
      rw [Subgroup.mem_normalizer_iff]
      intro g
      refine ⟨hfwd g, fun hg => ?_⟩
      have h1 := hfwd _ (hfwd _ hg)
      have hx0' : x 0 * x 0 * x 0 = 1 := by rw [← pow_three', hx0]
      rwa [show x 0 * (x 0 * (x 0 * g * (x 0)⁻¹) * (x 0)⁻¹) * (x 0)⁻¹ =
          (x 0 * x 0 * x 0) * g * (x 0 * x 0 * x 0)⁻¹ by simp only [mul_inv_rev, mul_assoc],
        hx0', one_mul, inv_one, mul_one] at h1
    · have hVC : V ≤ Subgroup.centralizer ({x i} : Set G) := by
        rw [hVdef, Subgroup.closure_le]
        rintro g (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.2 (hxa i hi).symm
        · exact Subgroup.mem_centralizer_singleton_iff.2 (hxb i hi).symm
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun g hg => ?_)
      exact Subgroup.mem_centralizer_singleton_iff.1 (hVC hg)
  have hEN : E ≤ Subgroup.normalizer (V : Set G) := by
    rintro _ ⟨f, rfl⟩
    have hf : f = Pi.mulSingle (0 : Fin 4) (f 0) * Pi.mulSingle (1 : Fin 4) (f 1) *
        Pi.mulSingle (2 : Fin 4) (f 2) * Pi.mulSingle (3 : Fin 4) (f 3) := by
      funext i
      fin_cases i <;> simp
    rw [hf, map_mul, map_mul, map_mul, hφs, hφs, hφs, hφs]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (hxN 0) _) (Subgroup.pow_mem _ (hxN 1) _))
      (Subgroup.pow_mem _ (hxN 2) _)) (Subgroup.pow_mem _ (hxN 3) _)
  exact le_localRank_of_le_normalizer Nat.prime_three hV1 hV2 hE hEc hEN

end Klein

section Coxeter

variable {Y : Type*} [Group Y]

theorem braid_of_pow_three {u c : Y} (hu : u ^ 2 = 1) (hc : c ^ 2 = 1) (h : (u * c) ^ 3 = 1) :
    u * c * u = c * u * c := by
  have h1 : u * c * u * (c * u * c) = 1 := by rw [← h, pow_three]; group
  rw [eq_inv_of_mul_eq_one_left h1, mul_inv_rev, mul_inv_rev,
    CFSG.SectionRank.inv_eq_self_of_sq_eq_one hu, CFSG.SectionRank.inv_eq_self_of_sq_eq_one hc,
    mul_assoc]

theorem klein_conj_fst {u c w : Y} (hu : u ^ 2 = 1) (hc : c ^ 2 = 1)
    (hucu : u * c * u = c * u * c) (hcwc : c * w * c = w * c * w) (huw : u * w = w * u) :
    u * c * (u * w) * (u * c)⁻¹ = c * (u * w) * c * (u * w) := by
  rw [mul_inv_rev, CFSG.SectionRank.inv_eq_self_of_sq_eq_one hu,
    CFSG.SectionRank.inv_eq_self_of_sq_eq_one hc]
  calc u * c * (u * w) * (c * u) = u * c * u * w * c * u := by group
    _ = c * u * c * w * c * u := by rw [hucu]
    _ = c * u * (c * w * c) * u := by group
    _ = c * u * (w * c * w) * u := by rw [hcwc]
    _ = c * u * w * c * (w * u) := by group
    _ = c * u * w * c * (u * w) := by rw [huw]
    _ = c * (u * w) * c * (u * w) := by group

theorem klein_conj_snd {u c w : Y} (hu : u ^ 2 = 1) (hc : c ^ 2 = 1) (huw : u * w = w * u) :
    u * c * (c * (u * w) * c) * (u * c)⁻¹ = u * w := by
  rw [mul_inv_rev, CFSG.SectionRank.inv_eq_self_of_sq_eq_one hu,
    CFSG.SectionRank.inv_eq_self_of_sq_eq_one hc]
  have hcc : c * c = 1 := by rw [← sq, hc]
  have huu : u * u = 1 := by rw [← sq, hu]
  calc u * c * (c * (u * w) * c) * (c * u) = u * (c * c) * u * w * (c * c) * u := by group
    _ = u * u * w * u := by rw [hcc]; group
    _ = w * u := by rw [huu, one_mul]
    _ = u * w := huw.symm

open CFSG.QuasithinUnique.SQTK.Coxeter in
theorem mul_mem_commutator_of_pow_three {p q : Y} (hp : p ^ 2 = 1) (hq : q ^ 2 = 1)
    (h : (p * q) ^ 3 = 1) : p * q ∈ commutator Y := by
  have hc : ⁅p, q⁆ ∈ commutator Y :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [CFSG.SectionRank.commutatorElement_eq_sq hp hq] at hc
  have hpq : p * q = ((p * q) ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, h, one_mul]
  rw [hpq]
  exact Subgroup.pow_mem _ hc _

open CFSG.QuasithinUnique.SQTK.Coxeter in
theorem four_le_localRank_three_of_coxeter {n : ℕ} (edges : List (Fin n × Fin n))
    (M : CoxeterMatrix (Fin n))
    (hM : ∀ i j, M i j = if i = j then 1 else if (i, j) ∈ edges ∨ (j, i) ∈ edges then 3 else 2)
    (hconn : (edgeGraph edges).Connected) (htri : (edgeGraph edges).CliqueFree 3)
    (s : Fin n → Y) (hgen : Subgroup.closure (Set.range s) = ⊤)
    (hrel : ∀ i j, (s i * s j) ^ M i j = 1) {K : Subgroup Y} (hK : commutator Y ≤ K)
    {G : Type} [Group G] [Finite G] (e : G ≃* K) (hG : ∃ g h : G, g * h ≠ h * g)
    (a b : Fin 4 → Fin n) (hab : ∀ i, (edgeGraph edges).Adj (a i) (b i))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ [a i, b i], ∀ y ∈ [a j, b j], ¬ (edgeGraph edges).Adj x y)
    (w v : Fin n) (hcw : (edgeGraph edges).Adj (b 0) w) (huw : ¬ (edgeGraph edges).Adj (a 0) w)
    (hvu : (edgeGraph edges).Adj v (a 0)) (hvw : ¬ (edgeGraph edges).Adj v w)
    (hw : ∀ i, i ≠ 0 → ∀ x ∈ [a i, b i], ¬ (edgeGraph edges).Adj x w) :
    4 ≤ localRank 3 G := by
  set Γ := edgeGraph edges
  obtain ⟨hs, hedge, hnon⟩ := coxeter_relations_of_matrix edges M hM s hrel
  have hY : commutator Y ≠ ⊥ := commutator_ne_bot_of_mulEquiv e hG
  have hc : ∀ x y : Fin n, ¬ Γ.Adj x y → Commute (s x) (s y) := fun x y h => by
    by_cases hxy : x = y
    · subst hxy
      exact Commute.refl _
    · exact hnon x y hxy h
  have hord : ∀ {x y : Fin n}, Γ.Adj x y → orderOf (s x * s y) = 3 := fun h =>
    CFSG.SectionRank.orderOf_mul_eq_three_of_adj Γ hconn htri s hgen hs hedge hnon hY h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφ, hφY, hφs⟩ := CFSG.SectionRank.independent_dihedral_odd_subgroups (p := 3)
    (by norm_num) (fun i => s (a i)) (fun i => s (b i)) (fun i => hs _) (fun i => hs _)
    (fun i => hord (hab i))
    (fun i j hij => hc _ _ (hsep i j hij (a i) (by simp) (a j) (by simp)))
    (fun i j hij => hc _ _ (hsep i j hij (a i) (by simp) (b j) (by simp)))
    (fun i j hij => hc _ _ (hsep i j hij (b i) (by simp) (b j) (by simp)))
  set u := s (a 0)
  set c := s (b 0)
  set x : Fin 4 → Y := fun i => s (a i) * s (b i) with hxdef
  set α := u * s w
  set β := c * α * c
  have hcwc : c * s w * c = s w * c * s w := braid_of_pow_three (hs _) (hs _) (hedge _ _ hcw)
  have hucu : u * c * u = c * u * c := braid_of_pow_three (hs _) (hs _) (hedge _ _ (hab 0))
  have huw' : u * s w = s w * u := (hc _ _ huw).eq
  have hα : α ≠ 1 := by
    intro h1
    have heq : u = s w := by
      have := eq_inv_of_mul_eq_one_left h1
      rwa [CFSG.SectionRank.inv_eq_self_of_sq_eq_one (hs w)] at this
    have h2 : (s v * u) ^ 2 = 1 := by
      rw [heq, (hc v w hvw).mul_pow, hs, hs, one_mul]
    have h3 := hord hvu
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rw [h3] at hdvd
    omega
  have hα2 : α ^ 2 = 1 := by rw [(hc _ _ huw).mul_pow, hs, hs, one_mul]
  have hβ2 : β ^ 2 = 1 := by
    have hcc : c * c = 1 := by rw [← sq, hs]
    have hαα : α * α = 1 := by rw [← sq, hα2]
    show (c * α * c) ^ 2 = 1
    rw [sq, show c * α * c * (c * α * c) = c * (α * (c * c) * α) * c by group, hcc, mul_one,
      hαα, mul_one, hcc]
  have hx0 : x 0 ^ 3 = 1 := hedge _ _ (hab 0)
  have h0a : x 0 * α * (x 0)⁻¹ = β * α := klein_conj_fst (hs _) (hs _) hucu hcwc huw'
  have h0b : x 0 * β * (x 0)⁻¹ = α := klein_conj_snd (hs _) (hs _) huw'
  have hxc : ∀ i, i ≠ 0 → ∀ y ∈ [u, c, s w], Commute (x i) y := by
    intro i hi y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    have h1 : ∀ z ∈ [a i, b i], Commute (s z) u := fun z hz =>
      hc _ _ (hsep i 0 hi z hz (a 0) (by simp))
    have h2 : ∀ z ∈ [a i, b i], Commute (s z) c := fun z hz =>
      hc _ _ (hsep i 0 hi z hz (b 0) (by simp))
    have h3 : ∀ z ∈ [a i, b i], Commute (s z) (s w) := fun z hz => hc _ _ (hw i hi z hz)
    rcases hy with rfl | rfl | rfl
    · exact (h1 _ (by simp)).mul_left (h1 _ (by simp))
    · exact (h2 _ (by simp)).mul_left (h2 _ (by simp))
    · exact (h3 _ (by simp)).mul_left (h3 _ (by simp))
  have hxa : ∀ i, i ≠ 0 → x i * α = α * x i := fun i hi =>
    ((hxc i hi u (by simp)).mul_right (hxc i hi (s w) (by simp))).eq
  have hxb : ∀ i, i ≠ 0 → x i * β = β * x i := fun i hi =>
    (((hxc i hi c (by simp)).mul_right ((hxc i hi u (by simp)).mul_right
      (hxc i hi (s w) (by simp)))).mul_right (hxc i hi c (by simp))).eq
  have hφK : ∀ f, φ f ∈ K := fun f => hK (hφY ⟨f, rfl⟩)
  have hxK : ∀ i, x i ∈ K := fun i => by
    have := hφK (Pi.mulSingle i (Multiplicative.ofAdd 1))
    rwa [hφs, toAdd_ofAdd, ZMod.val_one, pow_one] at this
  have hαK : α ∈ K := by
    have h1 := mul_mem_commutator_of_pow_three (hs _) (hs _) (hedge _ _ (hab 0))
    have h2 := mul_mem_commutator_of_pow_three (hs _) (hs _) (hedge _ _ hcw)
    have h3 := Subgroup.mul_mem _ h1 h2
    have hcc : c * c = 1 := by rw [← sq, hs]
    rw [show u * c * (c * s w) = u * (c * c) * s w by group, hcc, mul_one] at h3
    exact hK h3
  have hβK : β ∈ K := by
    have h1 : c * α * c⁻¹ ∈ commutator Y := by
      have hα' : α ∈ commutator Y := by
        have h1 := mul_mem_commutator_of_pow_three (hs _) (hs _) (hedge _ _ (hab 0))
        have h2 := mul_mem_commutator_of_pow_three (hs _) (hs _) (hedge _ _ hcw)
        have h3 := Subgroup.mul_mem _ h1 h2
        have hcc : c * c = 1 := by rw [← sq, hs]
        rwa [show u * c * (c * s w) = u * (c * c) * s w by group, hcc, mul_one] at h3
      exact (inferInstance : (commutator Y).Normal).conj_mem α hα' c
    rw [CFSG.SectionRank.inv_eq_self_of_sq_eq_one (hs _)] at h1
    exact hK h1
  let ι : K →* G := e.symm.toMonoidHom
  have hι : Function.Injective ι := e.symm.injective
  let kx : Fin 4 → K := fun i => ⟨x i, hxK i⟩
  let ka : K := ⟨α, hαK⟩
  let kb : K := ⟨β, hβK⟩
  refine four_le_localRank_three_of_klein (fun i => ι (kx i))
    (ι.comp (φ.codRestrict K hφK)) (hι.comp fun f g h => hφ (congrArg Subtype.val h))
    (fun i k => ?_) (a := ι ka) (b := ι kb) ?_ ?_ ?_ ?_ ?_ ?_ (fun i hi => ?_) (fun i hi => ?_)
  · change ι ⟨φ (Pi.mulSingle i k), _⟩ = ι (kx i) ^ (Multiplicative.toAdd k).val
    rw [← map_pow]
    congr 1
    exact Subtype.ext (hφs i k)
  · intro h
    exact hα (congrArg Subtype.val (hι (h.trans (map_one ι).symm)))
  · rw [← map_pow, show ka ^ 2 = 1 from Subtype.ext hα2, map_one]
  · rw [← map_pow, show kb ^ 2 = 1 from Subtype.ext hβ2, map_one]
  · rw [← map_pow, show kx 0 ^ 3 = 1 from Subtype.ext hx0, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg ι (Subtype.ext h0a)
  · rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg ι (Subtype.ext h0b)
  · rw [← map_mul, ← map_mul]
    exact congrArg ι (Subtype.ext (hxa i hi))
  · rw [← map_mul, ← map_mul]
    exact congrArg ι (Subtype.ext (hxb i hi))

end Coxeter

end CFSG.RankThree.PartTwo.Census
