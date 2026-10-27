
module

public import CFSG.Quasithin.Vol2.KGFactC31OrbSound
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck
public import CFSG.Quasithin.Vol2.KGFactC31Fix

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native Matrix

theorem EBasis.of_map {Γ B : Type*} [Group Γ] [Group B] {n : ℕ} {v : Fin n → Γ} {f : Γ →* B}
    (hf : Function.Injective f) (h : EBasis fun i => f (v i)) : EBasis v where
  sq i := hf (by rw [map_mul, h.sq i, map_one])
  comm i j := hf (by rw [map_mul, map_mul]; exact (h.comm i j).eq)
  ne_one c hc := h.ne_one c (by rw [← map_eElt, hc, map_one])

theorem mem_eNorm_iff {Γ : Type*} [Group Γ] [Finite Γ] {n : ℕ} {v : Fin n → Γ} (hv : EBasis v)
    (x : Γ) : x ∈ eNorm hv ↔ ∀ i, ∃ c, x * v i * x⁻¹ = eElt v c := by
  constructor
  · intro hx i
    obtain ⟨c, hc⟩ := (mem_eSub_iff hv _).mp
      ((Subgroup.mem_normalizer_iff.mp hx _).mp (mem_eSub hv i))
    exact ⟨c, hc.symm⟩
  · intro h
    choose cs hcs using h
    exact mem_eNorm hv (Matrix.of fun r i => cs i r) fun i => by rw [hcs i]; rfl

theorem centralizer_le_of_card {Γ : Type*} [Group Γ] [Finite Γ] {n : ℕ} {v : Fin n → Γ}
    (hv : EBasis v) (h : Nat.card (Subgroup.centralizer (eSub hv : Set Γ)) = 2 ^ n) :
    Subgroup.centralizer (eSub hv : Set Γ) ≤ eSub hv := by
  have hle : eSub hv ≤ Subgroup.centralizer (eSub hv : Set Γ) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm hv _ _ hy hx
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h, card_eSub])).symm.le

theorem simple_of_surj {Γ : Type} [Group Γ] {U L : Subgroup Γ} {H : Type*} [Group H]
    [IsSimpleGroup H] (φ : ↥L →* H) (hφ : Function.Surjective φ) (hker : φ.ker = U.subgroupOf L) :
    ∀ K : Subgroup Γ, U ≤ K → K ≤ L → L ≤ Subgroup.normalizer (K : Set Γ) → K = U ∨ K = L := by
  have hn : (U.subgroupOf L).Normal := hker ▸ φ.normal_ker
  have hs : IsSimpleGroup (↥L ⧸ U.subgroupOf L) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)).isSimpleGroup
  exact forall_eq_of_simple hs

theorem card_range_eq {Γ : Type*} [Group Γ] {U L : Subgroup Γ} (hUL : U ≤ L) {H : Type*} [Group H]
    (φ : ↥L →* H) (hker : φ.ker = U.subgroupOf L) :
    Nat.card φ.range * Nat.card U = Nat.card L := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv] at h1
  exact h1.symm

theorem simple_map {G₀ Γ : Type*} [Group G₀] [Group Γ] (ι : G₀ →* Γ) (hι : Function.Injective ι)
    {U M' : Subgroup G₀}
    (hs : ∀ K : Subgroup G₀, U ≤ K → K ≤ M' → M' ≤ Subgroup.normalizer (K : Set G₀) →
      K = U ∨ K = M') :
    ∀ K : Subgroup Γ, U.map ι ≤ K → K ≤ M'.map ι →
      M'.map ι ≤ Subgroup.normalizer (K : Set Γ) → K = U.map ι ∨ K = M'.map ι := by
  intro K hUK hKM hMK
  have hKr : K ≤ ι.range := hKM.trans (Subgroup.map_le_range ι M')
  set K' := K.comap ι with hK'
  have hK : K'.map ι = K := by rw [hK', Subgroup.map_comap_eq, inf_eq_right.mpr hKr]
  have hUK' : U ≤ K' := fun u hu => hUK ⟨u, hu, rfl⟩
  have hKM' : K' ≤ M' := fun k hk => by
    obtain ⟨m, hm, hmk⟩ := hKM hk
    rwa [← hι hmk]
  have hMK' : M' ≤ Subgroup.normalizer (K' : Set G₀) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro k
    have h1 := (Subgroup.mem_normalizer_iff.mp (hMK ⟨m, hm, rfl⟩) (ι k))
    simp only [Subgroup.mem_comap, map_mul, map_inv, hK'] at h1 ⊢
    exact h1
  rcases hs K' hUK' hKM' hMK' with h | h
  · left; rw [← hK, h]
  · right; rw [← hK, h]

theorem mem_normalizer_sup {G : Type*} [Group G] {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

variable {n : ℕ}

theorem rep_apply {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) (i : Fin n) :
    ap T i.val = (g i).val := by
  rw [hT i.val i.isLt, idx_of_lt g i.isLt]
  rfl

theorem all_iff_of_forall₂ {k : ℕ} {v : Fin k → Equiv.Perm (Fin n)} {bs : List Table}
    (h : List.Forall₂ (Rep n) bs (List.ofFn v)) {f : Table → Bool}
    {Q : Equiv.Perm (Fin n) → Prop} (hfQ : ∀ b g, Rep n b g → (f b = true ↔ Q g)) :
    bs.all f = true ↔ ∀ i, Q (v i) := by
  rw [List.all_eq_true]
  constructor
  · intro hall i
    obtain ⟨b, hb, hbi⟩ := exists_tab_of_mem h (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (hfQ b _ hbi).mp (hall b hb)
  · intro hall b hb
    obtain ⟨g, hg, hbg⟩ := exists_rep_of_mem h hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact (hfQ b _ hbg).mpr (hall i)

theorem rep_conjTab {c ci b : Table} {g x : Equiv.Perm (Fin n)} (hc : Rep n c g)
    (hci : Rep n ci g⁻¹) (hb : Rep n b x) : Rep n (conjTab n c ci b) (g * x * g⁻¹) :=
  Rep.compT (Rep.compT hc hb) hci

theorem forall₂_conjTab {k : ℕ} {bs : List Table} {v : Fin k → Equiv.Perm (Fin n)}
    (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) {c ci : Table} {g : Equiv.Perm (Fin n)}
    (hc : Rep n c g) (hci : Rep n ci g⁻¹) :
    List.Forall₂ (Rep n) (bs.map (conjTab n c ci)) (List.ofFn fun i => g * v i * g⁻¹) := by
  have h : (List.ofFn fun i => g * v i * g⁻¹) = (List.ofFn v).map fun x => g * x * g⁻¹ := by
    rw [List.map_ofFn]; rfl
  rw [h, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hbs.imp fun _ _ hb => rep_conjTab hc hci hb

theorem exists_conj_of_cosetOK (hn : n < 2 ^ 32) {k : ℕ} {v : Fin k → Equiv.Perm (Fin n)}
    (hv : EBasis v) {bs : List Table} (hbs : List.Forall₂ (Rep n) bs (List.ofFn v))
    {bT : Table} {b : Equiv.Perm (Fin n)} (hb : Rep n bT b) {rsT : List Table}
    {rsG : List (Equiv.Perm (Fin n))} (hrs : List.Forall₂ (Rep n) rsT rsG)
    (hok : cosetOK n bT bs rsT = true) {x : Equiv.Perm (Fin n)} (hx : x ∈ eSub hv)
    (hx1 : x ≠ 1) : ∃ r ∈ rsG, x = r * b * r⁻¹ := by
  have hlen : bs.length = k := by rw [hbs.length_eq, List.length_ofFn]
  have hlen' : rsT.length = rsG.length := hrs.length_eq
  unfold cosetOK at hok
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hl, hall⟩ := hok
  rw [hlen] at hl
  obtain ⟨c, rfl⟩ := (mem_eSub_iff hv x).mp hx
  obtain ⟨mask, hmask, rfl⟩ := exists_maskVec c
  have hm0 : mask ≠ 0 := by
    rintro rfl
    apply hx1
    have : maskVec k 0 = 0 := by funext i; simp [maskVec]
    rw [this, eElt_zero]
  have hm : mask - 1 < rsT.length := by omega
  have h1 := hall (mask - 1) (List.mem_range.mpr hm)
  rw [Bool.and_eq_true] at h1
  obtain ⟨hinv, heq⟩ := h1
  have hr : Rep n (rsT.getD (mask - 1) (idT n)) (rsG[mask - 1]'(by omega)) := by
    rw [List.getD_eq_getElem _ _ hm]
    have := (List.forall₂_iff_get.mp hrs).2 (mask - 1) hm (by omega)
    simpa using this
  have hri := Rep.inv_of_invOK hr hinv
  have h2 := (tblEq_iff_eq (rep_conjTab hr hri hb)
    (rep_maskProd hn v bs hbs (mask - 1 + 1))).mp heq
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)] at h2
  exact ⟨_, List.getElem_mem _, h2.symm⟩

theorem eq_eElt_of_coords (hn : n < 2 ^ 32) {k m : ℕ} {v : Fin k → Equiv.Perm (Fin n)}
    {u : Fin m → Equiv.Perm (Fin n)} {bs cs : List Table}
    (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) (hcs : List.Forall₂ (Rep n) cs (List.ofFn u))
    {coords : List ℕ}
    (h : (cs.length == coords.length && (cs.zip coords).all fun p =>
      tblEq n p.1 (maskProd n bs p.2)) = true) (i : Fin m) :
    ∃ c, u i = eElt v c := by
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hl, hall⟩ := h
  have hlen : cs.length = m := by rw [hcs.length_eq, List.length_ofFn]
  have hi : i.val < cs.length := by rw [hlen]; exact i.2
  have hi' : i.val < coords.length := by rw [← hl]; exact hi
  have hmem : (cs[i.val], coords[i.val]) ∈ cs.zip coords := by
    rw [List.mem_iff_getElem]
    exact ⟨i.val, by rw [List.length_zip]; omega, by rw [List.getElem_zip]⟩
  have hsi : Rep n cs[i.val] (u i) := by
    have := (List.forall₂_iff_get.mp hcs).2 i.val hi (by rw [List.length_ofFn]; exact i.2)
    simpa using this
  exact ⟨_, (tblEq_iff_eq hsi (rep_maskProd hn v bs hbs coords[i.val])).mp (hall _ hmem)⟩

theorem fixesAll_iff {pts : List ℕ} (hpts : ∀ i ∈ pts, i < n) {T : Table}
    {g : Equiv.Perm (Fin n)} (hT : Rep n T g) :
    fixesAll T pts = true ↔ ∀ i : Fin n, i.val ∈ pts → g i = i := by
  unfold fixesAll
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    have h1 := h i.val hi
    rw [beq_iff_eq, rep_apply hT i] at h1
    exact Fin.ext h1
  · intro h i hi
    have h1 := rep_apply hT ⟨i, hpts i hi⟩
    rw [beq_iff_eq]
    rw [h ⟨i, hpts i hi⟩ hi] at h1
    exact h1

theorem fixSetIs_iff {k : ℕ} {bs : List Table} {v : Fin k → Equiv.Perm (Fin n)}
    (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) {pts : List ℕ}
    (h : fixSetIs n bs pts = true) (i : Fin n) : (∀ j, v j i = i) ↔ i.val ∈ pts := by
  unfold fixSetIs at h
  rw [List.all_eq_true] at h
  have h1 := h i.val (List.mem_range.mpr i.isLt)
  rw [beq_iff_eq] at h1
  have h2 : (bs.all fun b => ap b i.val == i.val) = true ↔ ∀ j, v j i = i :=
    all_iff_of_forall₂ hbs (f := fun b => ap b i.val == i.val) (Q := fun g => g i = i)
      fun b g hb => by
        rw [beq_iff_eq, rep_apply hb i]
        exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  rw [← h2, h1, List.contains_iff_mem]

@[expose] def ptStab (n : ℕ) (pts : List ℕ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ i : Fin n, i.val ∈ pts → g i = i}
  mul_mem' := fun {a b} ha hb i hi => by rw [Equiv.Perm.mul_apply, hb i hi, ha i hi]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {a} ha i hi => by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (ha i hi).symm

theorem mem_ptStab {pts : List ℕ} {g : Equiv.Perm (Fin n)} :
    g ∈ ptStab n pts ↔ ∀ i : Fin n, i.val ∈ pts → g i = i := Iff.rfl

theorem fix_of_closure {k : ℕ} {v : Fin k → Equiv.Perm (Fin n)} {i : Fin n}
    (h : ∀ j, v j i = i) : ∀ u ∈ Subgroup.closure (Set.range v), u i = i := by
  let F : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {g | g i = i}
      mul_mem' := fun {a b} ha hb => by
        show (a * b) i = i
        rw [Equiv.Perm.mul_apply, hb, ha]
      one_mem' := rfl
      inv_mem' := fun {a} ha => by
        show a⁻¹ i = i
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact ha.symm }
  have hle : Subgroup.closure (Set.range v) ≤ F := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact h j
  exact fun u hu => hle hu

theorem fix_eSub_iff {k : ℕ} {v : Fin k → Equiv.Perm (Fin n)} (hv : EBasis v) (i : Fin n) :
    (∀ u ∈ eSub hv, u i = i) ↔ ∀ j, v j i = i :=
  ⟨fun h j => h _ (mem_eSub hv j), fun h u hu => fix_of_closure h u (eSub_eq_closure hv ▸ hu)⟩

@[expose] def setStab {α : Type*} (T : Finset α) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ i, i ∈ T ↔ g i ∈ T}
  mul_mem' := fun {_ b} ha hb i => (hb i).trans (ha (b i))
  one_mem' := fun _ => Iff.rfl
  inv_mem' := fun {a} ha i => by
    have e : a (a⁻¹ i) = i := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have := ha (a⁻¹ i)
    rw [e] at this
    exact this.symm

@[expose] noncomputable def setAct {α : Type*} (T : Finset α) {m : ℕ} (hT : T.card = m) :
    ↥(setStab T) →* Equiv.Perm (Fin m) where
  toFun g := (T.equivFinOfCardEq hT).permCongr
    ((g : Equiv.Perm α).subtypePerm fun x => (g.2 x).symm)
  map_one' := by ext x; simp
  map_mul' := fun a b => by ext x; simp [Equiv.permCongr_apply]

theorem setAct_eq_one_iff {α : Type*} (T : Finset α) {m : ℕ} (hT : T.card = m)
    (g : ↥(setStab T)) : setAct T hT g = 1 ↔ ∀ i ∈ T, (g : Equiv.Perm α) i = i := by
  constructor
  · intro h i hi
    have h2 := congrArg (fun σ : Equiv.Perm (Fin m) => σ (T.equivFinOfCardEq hT ⟨i, hi⟩)) h
    simp only [setAct, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.permCongr_apply,
      Equiv.symm_apply_apply, Equiv.Perm.coe_one, id_eq] at h2
    have h3 := congrArg Subtype.val ((T.equivFinOfCardEq hT).injective h2)
    simpa only [Equiv.Perm.subtypePerm_apply] using h3
  · intro h
    ext x
    simp only [setAct, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.permCongr_apply,
      Equiv.Perm.coe_one, id_eq]
    have h1 : ((g : Equiv.Perm α).subtypePerm fun x => (g.2 x).symm)
        ((T.equivFinOfCardEq hT).symm x) = (T.equivFinOfCardEq hT).symm x := by
      apply Subtype.ext
      rw [Equiv.Perm.subtypePerm_apply]
      exact h _ ((T.equivFinOfCardEq hT).symm x).2
    rw [h1, Equiv.apply_symm_apply]

theorem mem_setStab_of_normalizer {k : ℕ} {v : Fin k → Equiv.Perm (Fin n)} (hv : EBasis v)
    {T : Finset (Fin n)} (hT : ∀ i, (∀ u ∈ eSub hv, u i = i) ↔ i ∈ T) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ eNorm hv) : g ∈ setStab T := by
  intro i
  constructor
  · intro hi
    exact (hT _).mp (fix_of_normalizer hg ((hT i).mpr hi))
  · intro hi
    have h1 := fix_of_normalizer (Subgroup.inv_mem _ hg) ((hT _).mpr hi)
    rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply] at h1
    exact (hT i).mp h1

@[expose] def matStep {k : ℕ} (M₁ M₂ : Matrix (Fin k) (Fin k) (ZMod 2))
    (S : Finset (Fin k → ZMod 2)) : Finset (Fin k → ZMod 2) :=
  S ∪ S.image (M₁ *ᵥ ·) ∪ S.image (M₂ *ᵥ ·)

theorem forall_mem_matStep_iterate {k : ℕ} {M₁ M₂ : Matrix (Fin k) (Fin k) (ZMod 2)}
    {P : (Fin k → ZMod 2) → Prop} (h₁ : ∀ c, P c → P (M₁ *ᵥ c)) (h₂ : ∀ c, P c → P (M₂ *ᵥ c))
    {c : Fin k → ZMod 2} (hc : P c) : ∀ m, ∀ d ∈ (matStep M₁ M₂)^[m] {c}, P d := by
  intro m
  induction m with
  | zero =>
    intro d hd
    rw [Function.iterate_zero, id, Finset.mem_singleton] at hd
    rw [hd]
    exact hc
  | succ m ih =>
    intro d hd
    rw [Function.iterate_succ_apply'] at hd
    simp only [matStep, Finset.mem_union, Finset.mem_image] at hd
    rcases hd with (hd | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
    · exact ih d hd
    · exact h₁ e (ih e he)
    · exact h₂ e (ih e he)

theorem conj_eElt_of {Γ : Type*} [Group Γ] {k : ℕ} {v : Fin k → Γ} (hv : EBasis v) {g : Γ}
    {M : Matrix (Fin k) (Fin k) (ZMod 2)} (hg : ∀ i, g * v i * g⁻¹ = eElt v fun r => M r i)
    (d : Fin k → ZMod 2) : g * eElt v d * g⁻¹ = eElt v (M *ᵥ d) := by
  rw [conj_eElt, ← eElt_mulVec hv]
  congr 1
  funext i
  exact hg i

theorem eq_bot_or_eq_of_trans {Γ : Type*} [Group Γ] {k : ℕ} {v : Fin k → Γ} (hv : EBasis v)
    {M₁ M₂ : Matrix (Fin k) (Fin k) (ZMod 2)} {m : ℕ}
    (htr : ∀ c : Fin k → ZMod 2, c ≠ 0 → (matStep M₁ M₂)^[m] {c} = Finset.univ.erase 0)
    {g₁ g₂ : Γ} (hg₁ : ∀ i, g₁ * v i * g₁⁻¹ = eElt v fun r => M₁ r i)
    (hg₂ : ∀ i, g₂ * v i * g₂⁻¹ = eElt v fun r => M₂ r i) {W : Subgroup Γ} (hW : W ≤ eSub hv)
    (hn₁ : g₁ ∈ Subgroup.normalizer (W : Set Γ)) (hn₂ : g₂ ∈ Subgroup.normalizer (W : Set Γ)) :
    W = ⊥ ∨ W = eSub hv := by
  rcases W.bot_or_exists_ne_one with hb | ⟨x, hxW, hx1⟩
  · exact Or.inl hb
  right
  obtain ⟨c, rfl⟩ := (mem_eSub_iff hv x).mp (hW hxW)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hx1 (eElt_zero v)
  have hP : ∀ d ∈ (matStep M₁ M₂)^[m] {c}, eElt v d ∈ W :=
    forall_mem_matStep_iterate (P := fun d => eElt v d ∈ W)
      (fun d hd => by
        rw [← conj_eElt_of hv hg₁]
        exact (Subgroup.mem_normalizer_iff.mp hn₁ _).mp hd)
      (fun d hd => by
        rw [← conj_eElt_of hv hg₂]
        exact (Subgroup.mem_normalizer_iff.mp hn₂ _).mp hd)
      hxW m
  refine le_antisymm hW fun y hy => ?_
  obtain ⟨d, rfl⟩ := (mem_eSub_iff hv y).mp hy
  by_cases hd : d = 0
  · rw [hd, eElt_zero]
    exact W.one_mem
  · exact hP d (by rw [htr c hc0]; exact Finset.mem_erase.mpr ⟨hd, Finset.mem_univ _⟩)

end CFSG.Quasithin.KGC31

end
