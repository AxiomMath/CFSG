module

public import CFSG.Quasithin.EmptyFaithful.ModGWord
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S146yBorelBase

public section

namespace CFSG.Quasithin.ModH

open CFSG.Quasithin.ModG CFSG.QuasithinUnique CFSG.Open

section Words

variable {G : Type*} [Group G]

@[expose] def evcg (comp : ℕ → ℕ → ℕ) (kId : ℕ) (cs : List ℕ) (w : List ℕ) : ℕ :=
  w.foldr (fun l acc => comp (cs.getD l kId) acc) kId

theorem c_evg (c : G → ℕ) (comp : ℕ → ℕ → ℕ) (kId : ℕ)
    (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId) (ls : List G) (w : List ℕ) :
    c (ev ls w) = evcg comp kId (ls.map c) w := by
  induction w with
  | nil => rw [ev_nil, hone]; rfl
  | cons l w ih =>
    rw [ev_cons, hmul, ih]
    have h := List.getD_map ls 1 (n := l) c
    rw [hone] at h
    simp only [evcg, List.foldr_cons]
    rw [← h]

theorem map_c_evg (c : G → ℕ) (comp : ℕ → ℕ → ℕ) (kId : ℕ)
    (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId) (A : List G)
    (ws : List (List ℕ)) : (ws.map (ev A)).map c = ws.map (evcg comp kId (A.map c)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, c_evg c comp kId hmul hone A w, ih]

attribute [irreducible] evcg

end Words

section Closure

variable {G : Type} [Group G] [Finite G]
variable (c : G → ℕ) (comp : ℕ → ℕ → ℕ) (kId : ℕ)

omit [Finite G] in
theorem code_mul_pow (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) {K : List ℕ} {y : G}
    (hcl : ∀ k ∈ K, comp k (c y) ∈ K) {x : G} (hx : c x ∈ K) : ∀ j : ℕ, c (x * y ^ j) ∈ K := by
  intro j
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    have : x * y ^ (j + 1) = (x * y ^ j) * y := by rw [pow_succ, mul_assoc]
    rw [this, hmul]
    exact hcl _ ih

theorem mem_closure_iff_code (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId)
    (hinj : Function.Injective c) (gens : List G) (W : List (List ℕ)) (K : List ℕ)
    (hK : W.map (evcg comp kId (gens.map c)) = K) (h1 : kId ∈ K)
    (hcl : ∀ k ∈ K, ∀ g ∈ gens, comp k (c g) ∈ K) (x : G) :
    x ∈ Subgroup.closure {y | y ∈ gens} ↔ c x ∈ K := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction_right with
    | one => rw [hone]; exact h1
    | mul_right x hx y hy ih =>
      rw [hmul]
      exact hcl _ ih y hy
    | mul_inv_cancel x hx y hy ih =>
      have hy' : y⁻¹ = y ^ (orderOf y - 1) := by
        have h : y ^ (orderOf y - 1) * y = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos y), pow_orderOf_eq_one]
        exact (eq_inv_of_mul_eq_one_left h).symm
      rw [hy']
      exact code_mul_pow c comp hmul (fun k hk => hcl k hk y hy) ih _
  · intro hx
    rw [← hK, List.mem_map] at hx
    obtain ⟨w, -, hw⟩ := hx
    have h2 : c (ev gens w) = c x := by rw [c_evg c comp kId hmul hone, hw]
    have h3 : ev gens w = x := hinj h2
    rw [← h3]
    exact ev_mem (fun y hy => Subgroup.subset_closure hy) w

theorem card_closure_code (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId)
    (hinj : Function.Injective c) (gens : List G) (W : List (List ℕ)) (K : List ℕ)
    (hK : W.map (evcg comp kId (gens.map c)) = K) (h1 : kId ∈ K)
    (hcl : ∀ k ∈ K, ∀ g ∈ gens, comp k (c g) ∈ K) (hnd : K.Nodup) :
    Nat.card (Subgroup.closure {y | y ∈ gens}) = K.length := by
  have hiff := mem_closure_iff_code c comp kId hmul hone hinj gens W K hK h1 hcl
  have e1 : Nat.card (Subgroup.closure {y | y ∈ gens}) = Nat.card {x : G // c x ∈ K} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [e1]
  have e2 : Nat.card {x : G // c x ∈ K} = Nat.card ↥K.toFinset := by
    apply Nat.card_eq_of_bijective (fun x => ⟨c x.1, List.mem_toFinset.2 x.2⟩)
    constructor
    · intro x y hxy
      exact Subtype.ext (hinj (congrArg Subtype.val hxy))
    · rintro ⟨k, hk⟩
      have hk' : k ∈ K := List.mem_toFinset.1 hk
      have hk'' := hk'
      rw [← hK, List.mem_map] at hk''
      obtain ⟨w, -, hw⟩ := hk''
      have hc : c (ev gens w) = k := by rw [c_evg c comp kId hmul hone, hw]
      refine ⟨⟨ev gens w, by rw [hc]; exact hk'⟩, ?_⟩
      apply Subtype.ext
      exact hc
  rw [e2, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

theorem isSylowTwoOf_closure (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId)
    (hinj : Function.Injective c) (gens : List G) (W : List (List ℕ)) (K : List ℕ)
    (hK : W.map (evcg comp kId (gens.map c)) = K) (h1 : kId ∈ K)
    (hcl : ∀ k ∈ K, ∀ g ∈ gens, comp k (c g) ∈ K) (hnd : K.Nodup) (k m : ℕ)
    (hlen : K.length = 2 ^ k) (hcard : Nat.card G = K.length * m) (hm : ¬ 2 ∣ m) :
    IsSylowTwoOf (Subgroup.closure {y | y ∈ gens}) ⊤ := by
  have hT := card_closure_code c comp kId hmul hone hinj gens W K hK h1 hcl hnd
  rw [K1.isSylowTwoOf_top_iff]
  refine ⟨IsPGroup.of_card (n := k) (by rw [hT, hlen]), ?_⟩
  have h2 := Subgroup.card_mul_index (Subgroup.closure {y | y ∈ gens})
  rw [hT, hcard] at h2
  have hpos : 0 < K.length := by rw [hlen]; exact Nat.two_pow_pos k
  have h3 : (Subgroup.closure {y | y ∈ gens}).index = m := Nat.eq_of_mul_eq_mul_left hpos h2
  rw [h3]
  exact hm

@[expose] def CenterSmall (G : Type) [Group G] : Prop :=
  ∀ T : Subgroup G, IsSylowTwoOf T ⊤ → ∀ x y : G, x ∈ T → y ∈ T →
    (∀ t ∈ T, x * t = t * x) → (∀ t ∈ T, y * t = t * y) → x = 1 ∨ y = 1 ∨ x = y

theorem center_small_closure (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId)
    (hinj : Function.Injective c) (gens : List G) (W : List (List ℕ)) (K : List ℕ)
    (hK : W.map (evcg comp kId (gens.map c)) = K) (h1 : kId ∈ K)
    (hcl : ∀ k ∈ K, ∀ g ∈ gens, comp k (c g) ∈ K) (z : ℕ)
    (hcen : ∀ k ∈ K, (∀ g ∈ gens, comp k (c g) = comp (c g) k) → k = kId ∨ k = z)
    (x y : G) (hx : x ∈ Subgroup.closure {y | y ∈ gens}) (hy : y ∈ Subgroup.closure {y | y ∈ gens})
    (hxc : ∀ t ∈ Subgroup.closure {y | y ∈ gens}, x * t = t * x)
    (hyc : ∀ t ∈ Subgroup.closure {y | y ∈ gens}, y * t = t * y) : x = 1 ∨ y = 1 ∨ x = y := by
  have hiff := mem_closure_iff_code c comp kId hmul hone hinj gens W K hK h1 hcl
  have key : ∀ u : G, u ∈ Subgroup.closure {y | y ∈ gens} →
      (∀ t ∈ Subgroup.closure {y | y ∈ gens}, u * t = t * u) → c u = kId ∨ c u = z := by
    intro u hu huc
    refine hcen _ ((hiff u).1 hu) fun g hg => ?_
    have := huc g (Subgroup.subset_closure hg)
    rw [← hmul, ← hmul, this]
  have hone' : ∀ u : G, c u = kId → u = 1 := fun u hu => hinj (hu.trans hone.symm)
  rcases key x hx hxc with h | h
  · exact Or.inl (hone' x h)
  · rcases key y hy hyc with h' | h'
    · exact Or.inr (Or.inl (hone' y h'))
    · exact Or.inr (Or.inr (hinj (h.trans h'.symm)))

theorem centerSmall_of_one {T₀ : Subgroup G} (hT₀ : IsSylowTwoOf T₀ ⊤)
    (h : ∀ x y : G, x ∈ T₀ → y ∈ T₀ → (∀ t ∈ T₀, x * t = t * x) → (∀ t ∈ T₀, y * t = t * y) →
      x = 1 ∨ y = 1 ∨ x = y) : CenterSmall G := by
  intro T hT x y hx hy hxc hyc
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hT₀ hT
  have hmem : ∀ u : G, u ∈ T ↔ g⁻¹ * u * g ∈ T₀ := by
    intro u
    rw [← hg]
    constructor
    · intro hu
      obtain ⟨v, hv, rfl⟩ := hu
      have e : g⁻¹ * (g * v * g⁻¹) * g = v := by group
      change g⁻¹ * (g * v * g⁻¹) * g ∈ T₀
      rw [e]
      exact hv
    · intro hu
      exact ⟨g⁻¹ * u * g, hu, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hcomm : ∀ u : G, (∀ t ∈ T, u * t = t * u) → ∀ t ∈ T₀, (g⁻¹ * u * g) * t = t * (g⁻¹ * u * g) := by
    intro u hu t ht
    have h1 : g * t * g⁻¹ ∈ T := by
      rw [hmem]
      simpa [mul_assoc] using ht
    have h2 := hu _ h1
    calc g⁻¹ * u * g * t = g⁻¹ * (u * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * u) * g := by rw [h2]
      _ = t * (g⁻¹ * u * g) := by group
  rcases h (g⁻¹ * x * g) (g⁻¹ * y * g) ((hmem x).1 hx) ((hmem y).1 hy) (hcomm x hxc) (hcomm y hyc) with
    h1 | h1 | h1
  · left
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h1]; group
  · right; left
    have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [this, h1]; group
  · right; right
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    have h3 : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [this, h3, h1]

theorem centerSmall_of_data (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId)
    (hinj : Function.Injective c) (gens : List G) (W : List (List ℕ)) (K : List ℕ)
    (hK : W.map (evcg comp kId (gens.map c)) = K) (h1 : kId ∈ K)
    (hcl : ∀ k ∈ K, ∀ g ∈ gens, comp k (c g) ∈ K) (hnd : K.Nodup) (k m : ℕ)
    (hlen : K.length = 2 ^ k) (hcard : Nat.card G = K.length * m) (hm : ¬ 2 ∣ m) (z : ℕ)
    (hcen : ∀ k ∈ K, (∀ g ∈ gens, comp k (c g) = comp (c g) k) → k = kId ∨ k = z) :
    CenterSmall G :=
  centerSmall_of_one (isSylowTwoOf_closure c comp kId hmul hone hinj gens W K hK h1 hcl hnd k m hlen hcard hm)
    (fun x y hx hy hxc hyc =>
      center_small_closure c comp kId hmul hone hinj gens W K hK h1 hcl z hcen x y hx hy hxc hyc)

@[expose] def bucket (K : List ℕ) (j i : ℕ) : List ℕ := K.filter (fun k => Nat.beq (dg k j) i)

@[expose] def buckets (K : List ℕ) (j : ℕ) : List (List ℕ) := (List.range 32).map (bucket K j)

@[expose] def memBk (Kb : List (List ℕ)) (j x : ℕ) : Bool := memB x (Kb.getD (dg x j) [])

theorem buckets_getD (K : List ℕ) (j x : ℕ) : (buckets K j).getD (dg x j) [] = bucket K j (dg x j) := by
  have hlt : dg x j < 32 := by rw [dg_eq]; exact Nat.mod_lt _ (by norm_num)
  rw [buckets, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_range]

theorem mem_bucket_iff (K : List ℕ) (j x : ℕ) : x ∈ bucket K j (dg x j) ↔ x ∈ K := by
  simp [bucket]

theorem memBk_iff (K : List ℕ) (j x : ℕ) : memBk (buckets K j) j x = true ↔ x ∈ K := by
  rw [memBk, memB_iff, buckets_getD, mem_bucket_iff]

theorem nodup_of_buckets (K : List ℕ) (j : ℕ) (h : (buckets K j).all (fun b => nodupB b) = true) : K.Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro x
  have hlt : dg x j < 32 := by rw [dg_eq]; exact Nat.mod_lt _ (by norm_num)
  have hb : (bucket K j (dg x j)).Nodup := by
    have := List.all_eq_true.1 h (bucket K j (dg x j)) (by
      rw [buckets, List.mem_map]
      exact ⟨dg x j, List.mem_range.2 hlt, rfl⟩)
    exact nodupB_iff.1 this
  have hc : K.count x = (bucket K j (dg x j)).count x := by
    rw [bucket, List.count_filter]
    simp
  rw [hc]
  exact List.nodup_iff_count_le_one.1 hb x

@[expose] def dataOK (comp : ℕ → ℕ → ℕ) (kId : ℕ) (gC K : List ℕ) (Kb : List (List ℕ)) (j z : ℕ) : Bool :=
  Kb.all (fun b => nodupB b) && memBk Kb j kId &&
    allL (fun k => allL (fun g => memBk Kb j (comp k g)) gC) K &&
    allL (fun k => !(allL (fun g => Nat.beq (comp k g) (comp g k)) gC) || Nat.beq k kId || Nat.beq k z) K

theorem centerSmall_of_dataOK (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId)
    (hinj : Function.Injective c) (gens : List G) (W : List (List ℕ)) (K gC : List ℕ) (z : ℕ)
    (hg : gens.map c = gC) (hK : W.map (evcg comp kId gC) = K) (j : ℕ) (Kb : List (List ℕ)) (hKb : Kb = buckets K j)
    (hOK : dataOK comp kId gC K Kb j z = true)
    (k m : ℕ) (hlen : K.length = 2 ^ k) (hcard : Nat.card G = K.length * m) (hm : ¬ 2 ∣ m) :
    CenterSmall G := by
  subst hKb
  simp only [dataOK, Bool.and_eq_true] at hOK
  obtain ⟨⟨⟨hnd, h1⟩, hcl⟩, hcen⟩ := hOK
  have hK' : W.map (evcg comp kId (gens.map c)) = K := by rw [hg]; exact hK
  have hnd' : K.Nodup := nodup_of_buckets K j hnd
  have h1' : kId ∈ K := (memBk_iff K j kId).1 h1
  have hcl' : ∀ k ∈ K, ∀ g ∈ gens, comp k (c g) ∈ K := by
    intro k hk g hg'
    have := allL_iff.1 (allL_iff.1 hcl k hk) (c g) (by rw [← hg]; exact List.mem_map_of_mem hg')
    exact (memBk_iff K j _).1 this
  have hcen' : ∀ k ∈ K, (∀ g ∈ gens, comp k (c g) = comp (c g) k) → k = kId ∨ k = z := by
    intro k hk hkc
    have := allL_iff.1 hcen k hk
    simp only [Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq] at this
    rcases this with (h | h) | h
    · exfalso
      have h' : allL (fun g => Nat.beq (comp k g) (comp g k)) gC = true := by
        rw [allL_iff]
        intro g hgC
        rw [← hg] at hgC
        obtain ⟨g', hg'', rfl⟩ := List.mem_map.1 hgC
        have := hkc g' hg''
        rw [this]
        exact Nat.beq_refl _
      rw [h'] at h
      exact Bool.noConfusion h
    · exact Or.inl h
    · exact Or.inr h
  exact centerSmall_of_data c comp kId hmul hone hinj gens W K hK' h1' hcl' hnd' k m hlen hcard hm z hcen'

end Closure

end CFSG.Quasithin.ModH
