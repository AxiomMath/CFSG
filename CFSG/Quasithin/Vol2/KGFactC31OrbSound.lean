
module

public import CFSG.Quasithin.Vol2.KGFactC31Act
public import CFSG.Quasithin.Vol2.KGFactC31Orb
public import CFSG.Quasithin.Vol2.KGFactC31OrbCheck
public import CFSG.Quasithin.Vol2.KGFactC31EBasis

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Certificates CFSG.Quasithin.KGC31.Native Matrix

variable {n : ℕ}

theorem tblEq_iff_eq {S T : Table} {g h : Equiv.Perm (Fin n)} (hS : Rep n S g) (hT : Rep n T h) :
    tblEq n S T = true ↔ g = h := by
  constructor
  · intro he
    exact rep_unique (rep_of_tblEq hT he) hS |>.symm
  · rintro rfl
    rw [tblEq_iff]
    intro i hi
    rw [hS i hi, hT i hi]

theorem compEq_iff {T b u : Table} {g x w : Equiv.Perm (Fin n)} (hT : Rep n T g) (hb : Rep n b x)
    (hu : Rep n u w) : compEq n T b u = true ↔ g * x = w * g := by
  rw [← tblEq_iff_eq (Rep.compT hT hb) (Rep.compT hu hT), compEq, allIn_eq_true, tblEq_iff]
  have h1 : ∀ i < n, ap T (ap b i) = ap (compT n T b) i := fun i hi => by
    rw [Rep.compT hT hb i hi, hb i hi, hT _ (idx_lt x hi), idx_mul]
  have h2 : ∀ i < n, ap u (ap T i) = ap (compT n u T) i := fun i hi => by
    rw [Rep.compT hu hT i hi, hT i hi, hu _ (idx_lt g hi), idx_mul]
  constructor
  · intro h i hi
    rw [← h1 i hi, ← h2 i hi]
    exact beq_iff_eq.mp (h i (Nat.zero_le _) hi)
  · intro h i _ hi
    rw [beq_iff_eq, h1 i hi, h2 i hi]
    exact h i hi

@[expose] def maskVec (k mask : ℕ) : Fin k → ZMod 2 := fun i => ((mask / 2 ^ i.val) % 2 : ℕ)

theorem maskVec_zero (k mask : ℕ) : maskVec (k + 1) mask 0 = ((mask % 2 : ℕ) : ZMod 2) := by
  simp [maskVec]

theorem maskVec_succ (k mask : ℕ) :
    (fun i : Fin k => maskVec (k + 1) mask i.succ) = maskVec k (mask / 2) := by
  funext i
  simp only [maskVec, Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul]
  rw [mul_comm (2 ^ i.val) 2, ← Nat.div_div_eq_div_mul]

theorem rep_maskProd (hn : n < 2 ^ 32) :
    ∀ {k : ℕ} (v : Fin k → Equiv.Perm (Fin n)) (bs : List Table),
      List.Forall₂ (Rep n) bs (List.ofFn v) → ∀ mask,
        Rep n (maskProd n bs mask) (eElt v (maskVec k mask))
  | 0, v, bs, h, mask => by
    rw [List.ofFn_zero, List.forall₂_nil_right_iff] at h
    subst h
    rw [show eElt v (maskVec 0 mask) = 1 by simp [eElt]]
    exact Rep.idT hn
  | k + 1, v, bs, h, mask => by
    rw [List.ofFn_succ] at h
    cases h with
    | cons hb hbs =>
      rw [maskProd, eElt_succ, maskVec_succ, maskVec_zero]
      refine Rep.compT ?_ (rep_maskProd hn (fun i => v i.succ) _ hbs (mask / 2))
      have hval : ((mask % 2 : ℕ) : ZMod 2).val = mask % 2 :=
        ZMod.val_cast_of_lt (Nat.mod_lt _ (by norm_num))
      rw [hval]
      split_ifs with h1
      · rw [h1, pow_one]; exact hb
      · have h0 : mask % 2 = 0 := by omega
        rw [h0, pow_zero]; exact Rep.idT hn

theorem exists_maskVec : ∀ {k : ℕ} (c : Fin k → ZMod 2), ∃ mask < 2 ^ k, maskVec k mask = c
  | 0, c => ⟨0, by norm_num, funext fun i => i.elim0⟩
  | k + 1, c => by
    obtain ⟨m', hm', hc⟩ := exists_maskVec (fun i : Fin k => c i.succ)
    have hc0 : (c 0).val < 2 := ZMod.val_lt _
    refine ⟨(c 0).val + 2 * m', by rw [pow_succ]; omega, funext fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [maskVec_zero]
      have : ((c 0).val + 2 * m') % 2 = (c 0).val := by omega
      rw [this, ZMod.natCast_zmod_val]
    · have h1 := congrFun (maskVec_succ k ((c 0).val + 2 * m')) j
      rw [h1]
      have : ((c 0).val + 2 * m') / 2 = m' := by omega
      rw [this, hc]

theorem mem_spanTabs_iff (hn : n < 2 ^ 32) {k : ℕ} {v : Fin k → Equiv.Perm (Fin n)}
    {bs : List Table} (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) {f : Table → Bool}
    {P : Equiv.Perm (Fin n) → Prop} (hfP : ∀ T g, Rep n T g → (f T = true ↔ P g)) :
    (spanTabs n bs).any f = true ↔ ∃ c, P (eElt v c) := by
  have hlen : bs.length = k := by rw [hbs.length_eq, List.length_ofFn]
  rw [List.any_eq_true]
  constructor
  · rintro ⟨u, hu, hfu⟩
    obtain ⟨mask, -, rfl⟩ := List.mem_map.mp hu
    exact ⟨_, (hfP _ _ (rep_maskProd hn v bs hbs mask)).mp hfu⟩
  · rintro ⟨c, hc⟩
    obtain ⟨mask, hmask, rfl⟩ := exists_maskVec c
    refine ⟨maskProd n bs mask, List.mem_map.mpr ⟨mask, ?_, rfl⟩,
      (hfP _ _ (rep_maskProd hn v bs hbs mask)).mpr hc⟩
    rw [List.mem_range, hlen]
    exact hmask

theorem exists_tab_of_mem {bs : List Table} {gs : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) bs gs) {g : Equiv.Perm (Fin n)} (hg : g ∈ gs) :
    ∃ b ∈ bs, Rep n b g := by
  induction h with
  | nil => exact absurd hg List.not_mem_nil
  | cons hr _ ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨b, hb, hbg⟩ := ih hg
      exact ⟨b, List.mem_cons_of_mem _ hb, hbg⟩

theorem exists_rep_of_mem {bs : List Table} {gs : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) bs gs) {b : Table} (hb : b ∈ bs) : ∃ g ∈ gs, Rep n b g := by
  induction h with
  | nil => exact absurd hb List.not_mem_nil
  | cons hr _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨g, hg, hbg⟩ := ih hb
      exact ⟨g, List.mem_cons_of_mem _ hg, hbg⟩

theorem ebasis_of_ebasisOK (hn : n < 2 ^ 32) {k : ℕ} {v : Fin k → Equiv.Perm (Fin n)}
    {bs : List Table} (hbs : List.Forall₂ (Rep n) bs (List.ofFn v))
    (h : ebasisOK n bs = true) : EBasis v := by
  have hlen : bs.length = k := by rw [hbs.length_eq, List.length_ofFn]
  simp only [ebasisOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hsq, hcomm⟩, hne⟩ := h
  have hrep : ∀ i : Fin k, ∃ b ∈ bs, Rep n b (v i) := fun i =>
    exists_tab_of_mem hbs (List.mem_ofFn.mpr ⟨i, rfl⟩)
  refine ⟨fun i => ?_, fun i j => ?_, fun c hc => ?_⟩
  · obtain ⟨b, hb, hbi⟩ := hrep i
    exact (tblEq_iff_eq (Rep.compT hbi hbi) (Rep.idT hn)).mp (hsq b hb)
  · obtain ⟨b, hb, hbi⟩ := hrep i
    obtain ⟨b', hb', hbj⟩ := hrep j
    exact (tblEq_iff_eq (Rep.compT hbi hbj) (Rep.compT hbj hbi)).mp (hcomm b hb b' hb')
  · obtain ⟨mask, hmask, rfl⟩ := exists_maskVec c
    have h1 := hne mask (by rw [List.mem_range, hlen]; exact hmask)
    rw [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h0 | h1
    · subst h0
      funext i
      simp [maskVec]
    · exfalso
      rw [Bool.not_eq_true'] at h1
      have h2 := (tblEq_iff_eq (rep_maskProd hn v bs hbs mask) (Rep.idT hn)).mpr hc
      rw [h1] at h2
      exact absurd h2 (by decide)

theorem normAll_iff (hn : n < 2 ^ 32) {k : ℕ} {v : Fin k → Equiv.Perm (Fin n)} (h : EBasis v)
    {bs : List Table} (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) {T : Table}
    {g : Equiv.Perm (Fin n)} (hT : Rep n T g) : normAll n bs T = true ↔ g ∈ eNorm h := by
  have key : ∀ (b : Table) (x : Equiv.Perm (Fin n)), Rep n b x →
      (((spanTabs n bs).any fun u => compEq n T b u) = true ↔
        ∃ c, g * x = eElt v c * g) := fun b x hb =>
    mem_spanTabs_iff hn hbs (f := fun u => compEq n T b u)
      (P := fun u => g * x = u * g)
      fun U u hU => compEq_iff hT hb hU
  show (bs.all fun b => (spanTabs n bs).any fun u => compEq n T b u) = true ↔ _
  rw [List.all_eq_true]
  constructor
  · intro hall
    have hc : ∀ i : Fin k, ∃ c, g * v i * g⁻¹ = eElt v c := fun i => by
      obtain ⟨b, hb, hbi⟩ : ∃ b ∈ bs, Rep n b (v i) :=
        exists_tab_of_mem hbs (List.mem_ofFn.mpr ⟨i, rfl⟩)
      obtain ⟨c, hc⟩ := (key b (v i) hbi).mp (hall b hb)
      exact ⟨c, by rw [hc, mul_inv_cancel_right]⟩
    choose cs hcs using hc
    exact mem_eNorm h (Matrix.of fun r i => cs i r) fun i => by rw [hcs i]; rfl
  · intro hg b hb
    obtain ⟨x, hx, hbx⟩ := exists_rep_of_mem hbs hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨c, hc⟩ := (mem_eSub_iff h _).mp
      ((Subgroup.mem_normalizer_iff.mp hg _).mp (mem_eSub h i))
    exact (key b (v i) hbx).mpr ⟨c, by rw [hc, inv_mul_cancel_right]⟩

theorem conj_of_masksOK (hn : n < 2 ^ 32) {k : ℕ} {v : Fin k → Equiv.Perm (Fin n)}
    {bs : List Table} (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) {T : Table}
    {g : Equiv.Perm (Fin n)} (hT : Rep n T g) {masks : List ℕ}
    (hm : masksOK n bs T masks = true) (i : Fin k) :
    g * v i * g⁻¹ = eElt v (maskVec k (masks.getD i 0)) := by
  have hlen : bs.length = k := by rw [hbs.length_eq, List.length_ofFn]
  unfold masksOK at hm
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hm
  obtain ⟨hl, hall⟩ := hm
  have hik : i.val < bs.length := by rw [hlen]; exact i.2
  have him : i.val < masks.length := by rw [← hl]; exact hik
  have hmem : (bs[i.val], masks[i.val]) ∈ bs.zip masks := by
    rw [List.mem_iff_getElem]
    exact ⟨i.val, by rw [List.length_zip]; omega, by simp⟩
  have h1 := hall _ hmem
  have hbi : Rep n bs[i.val] (v i) := by
    have := (List.forall₂_iff_get.mp hbs).2 i.val hik (by rw [List.length_ofFn]; exact i.2)
    simpa using this
  have h2 := (tblEq_iff_eq (Rep.compT hT hbi)
    (Rep.compT (rep_maskProd hn v bs hbs masks[i.val]) hT)).mp h1
  rw [List.getD_eq_getElem _ _ him, h2, mul_inv_cancel_right]

theorem card_subtype_eq_countProducts (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {f : Table → Bool} {P : Equiv.Perm (Fin n) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep n T g → (f T = true ↔ P g)) :
    Nat.card {x : Q.originalSubgroup // P x} = countProducts n f (levelTables Q) (idT n) := by
  have hspec := countProducts_spec hfP (forall₂_levelTables hn Q) (Rep.idT hn)
  rw [hspec, card_subtype_eq_countP Q.originalSubgroup (enumeration Q) (enumeration_nodup Q hQ)
    (mem_enumeration_iff Q hQ) P]
  simp only [one_mul, List.map_id']
  rfl

theorem orbSub_eq_of_orbCheck (hn : n < 2 ^ 32) {m : ℕ} {invs els : List Table}
    {cands : List (List Table)} (hchk : orbCheck n m invs els cands = true)
    {candG : List (List (Equiv.Perm (Fin n)))}
    (hcands : List.Forall₂ (List.Forall₂ (Rep n)) cands candG) {e T : Table} (he : e ∈ els)
    (hT : T ∈ invs) {y t : Equiv.Perm (Fin n)} (hy : Rep n e y) (ht : Rep n T t)
    (hm : 0 < m) (hym : y ^ m = 1) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j < m, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    ∃ cg ∈ candG, orbSub y t = Subgroup.closure {x | x ∈ cg} := by
  unfold orbCheck at hchk
  rw [List.all_eq_true] at hchk
  have h1 := hchk e he
  rw [Bool.and_eq_true, List.all_eq_true] at h1
  have hyi : Rep n (invT n e) y⁻¹ := Rep.inv_of_invOK hy h1.1
  have h2 := h1.2 T hT
  rw [badAct_eq_true hn hy hyi ht m hmove hcomm, Bool.not_true, Bool.false_or,
    List.any_eq_true] at h2
  obtain ⟨cand, hcand, hok⟩ := h2
  obtain ⟨cg, hcg, hrel⟩ : ∃ cg ∈ candG, List.Forall₂ (Rep n) cand cg :=
    exists_mem_of_forall₂ hcands.flip hcand |>.imp fun _ h => ⟨h.1, h.2⟩
  refine ⟨cg, hcg, ?_⟩
  let orbv : Fin (List.range m).length → Equiv.Perm (Fin n) := fun j =>
    y ^ j.val * t * y⁻¹ ^ j.val
  have horb : List.Forall₂ (Rep n) (orbTabs n m e (invT n e) T) (List.ofFn orbv) := by
    unfold orbTabs
    rw [List.forall₂_iff_get]
    refine ⟨by simp [orbv], fun i h₁ h₂ => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, List.getElem_ofFn,
      orbv]
    exact Rep.compT (Rep.compT (Rep.powT hn hy i) ht) (Rep.powT hn hyi i)
  let cgv : Fin cg.length → Equiv.Perm (Fin n) := fun i => cg.get i
  have hcgv : List.ofFn cgv = cg := List.ofFn_get cg
  rw [← hcgv] at hrel
  unfold orbIs at hok
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hok
  obtain ⟨hsub, hsup⟩ := hok
  have hclo : ∀ {k : ℕ} (w : Fin k → Equiv.Perm (Fin n)) (c : Fin k → ZMod 2)
      (K : Subgroup (Equiv.Perm (Fin n))), (∀ i, w i ∈ K) → eElt w c ∈ K := by
    intro k w c K hK
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact Subgroup.pow_mem _ (hK i) _
  apply le_antisymm
  · rw [orbSub, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    have hj : j % m < m := Nat.mod_lt _ hm
    have hyj : y ^ j = y ^ (j % m) := by
      conv_lhs => rw [← Nat.mod_add_div j m, pow_add, pow_mul, hym, one_pow, mul_one]
    have hoj : conjTab n (powT n (j % m) e) (powT n (j % m) (invT n e)) T ∈
        orbTabs n m e (invT n e) T :=
      List.mem_map.mpr ⟨j % m, List.mem_range.mpr hj, rfl⟩
    have h3 := hsub _ hoj
    have hrepo : Rep n (conjTab n (powT n (j % m) e) (powT n (j % m) (invT n e)) T)
        (y ^ (j % m) * t * y⁻¹ ^ (j % m)) :=
      Rep.compT (Rep.compT (Rep.powT hn hy _) ht) (Rep.powT hn hyi _)
    obtain ⟨c, hc⟩ := (mem_spanTabs_iff hn hrel (P := fun x => y ^ (j % m) * t * y⁻¹ ^ (j % m) = x)
      fun U u hU => tblEq_iff_eq hrepo hU).mp h3
    have : y ^ j * t * (y ^ j)⁻¹ = eElt cgv c := by rw [hyj, ← inv_pow, hc]
    show y ^ j * t * (y ^ j)⁻¹ ∈ _
    rw [SetLike.mem_coe, this]
    exact hclo cgv c _ fun i => Subgroup.subset_closure (List.get_mem cg i)
  · rw [Subgroup.closure_le]
    intro x hx
    rw [← hcgv] at hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨b, hb, hbi⟩ : ∃ b ∈ cand, Rep n b (cgv i) :=
      exists_tab_of_mem hrel (List.mem_ofFn.mpr ⟨i, rfl⟩)
    obtain ⟨c, hc⟩ := (mem_spanTabs_iff hn horb (P := fun x => cgv i = x)
      fun U u hU => tblEq_iff_eq hbi hU).mp (hsup b hb)
    rw [SetLike.mem_coe, hc]
    refine hclo orbv c _ fun j => ?_
    have : orbv j = y ^ j.val * t * (y ^ j.val)⁻¹ := by simp [orbv, inv_pow]
    rw [this]
    exact conj_mem_orbSub y t j.val

end CFSG.Quasithin.KGC31

end
