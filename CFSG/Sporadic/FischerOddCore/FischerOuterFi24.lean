
module

public import CFSG.Sporadic.FischerOddCore.FischerOuterFi24Check
public import CFSG.Sporadic.FischerOddCore.Fi23LocalComp
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs
public import CFSG.Sporadic.Fi22.InvCent
public import CFSG.Sporadic.Fi22.LH.Facts
public import CFSG.Sporadic.Fi23.Tr.Facts
public import CFSG.Sporadic.Fi24.Complete
public import CFSG.Sporadic.Fi24.EdgeSwapCert
public import CFSG.Sporadic.Fi24.Out
public import CFSG.Sporadic.FischerOddCore.Fi24Cent
public import CFSG.Sporadic.FischerOddCore.NoCompLemmas

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.LocalCores CFSG.Blueprint.Fischer CFSG.Fischer
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native
open CFSG.Sporadic.Fi24 (R J M MR JR tR D24 jR cls)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)
open CFSG.Fischer (polarFacts hyperovalFacts)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

section Transport

theorem component_transport {X Y : Type*} [Group X] [Group Y] (K : Subgroup X) (L : Subgroup Y)
    (e : K ≃* L) {B : Subgroup K} (hB : IsComponent B) :
    ∃ B' : Subgroup L, IsComponent B' ∧
      Nat.card (B ⧸ Subgroup.center B) = Nat.card (B' ⧸ Subgroup.center B') :=
  ⟨_, (component_quotient_mulEquiv e hB).1, (component_quotient_mulEquiv e hB).2⟩

theorem component_restrict {X : Type*} [Group X] (K L : Subgroup X) (hLK : L ≤ K)
    {B : Subgroup K} (hB : IsComponent B) (hBL : ∀ b ∈ B, (b : X) ∈ L) :
    ∃ B' : Subgroup L, IsComponent B' ∧
      Nat.card (B ⧸ Subgroup.center B) = Nat.card (B' ⧸ Subgroup.center B') := by
  have hBL' : B ≤ L.subgroupOf K := fun b hb => Subgroup.mem_subgroupOf.2 (hBL b hb)
  obtain ⟨B', hB', hc⟩ := component_transport (L.subgroupOf K) L
    (Subgroup.subgroupOfEquivOfLe hLK) (component_overgroup hB hBL')
  exact ⟨B', hB', (card_quotient_center_mulEquiv (Subgroup.subgroupOfEquivOfLe hBL').symm).trans hc⟩

theorem conj_commute_conj {G : Type*} [Group G] (g x y : G) (h : x * y = y * x) :
    g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹) := by
  calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [h]
    _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

end Transport

section Fi23Inf

@[expose] def infCentralizerConj {G : Type*} [Group G] (h x y : G) :
    ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) ≃*
      ↥(Subgroup.centralizer ({h * x * h⁻¹} : Set G) ⊓ Subgroup.centralizer {h * y * h⁻¹}) where
  toFun g := ⟨h * g * h⁻¹, Subgroup.mem_inf.2
    ⟨Subgroup.mem_centralizer_singleton_iff.2 (by
      have hg := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).1
      calc h * ↑g * h⁻¹ * (h * x * h⁻¹) = h * (↑g * x) * h⁻¹ := by group
        _ = h * (x * ↑g) * h⁻¹ := by rw [hg]
        _ = h * x * h⁻¹ * (h * ↑g * h⁻¹) := by group),
    Subgroup.mem_centralizer_singleton_iff.2 (by
      have hg := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
      calc h * ↑g * h⁻¹ * (h * y * h⁻¹) = h * (↑g * y) * h⁻¹ := by group
        _ = h * (y * ↑g) * h⁻¹ := by rw [hg]
        _ = h * y * h⁻¹ * (h * ↑g * h⁻¹) := by group)⟩⟩
  invFun g := ⟨h⁻¹ * g * h, Subgroup.mem_inf.2
    ⟨Subgroup.mem_centralizer_singleton_iff.2 (by
      have hg := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).1
      calc h⁻¹ * ↑g * h * x = h⁻¹ * (↑g * (h * x * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * x * h⁻¹) * ↑g) * h := by rw [hg]
        _ = x * (h⁻¹ * ↑g * h) := by group),
    Subgroup.mem_centralizer_singleton_iff.2 (by
      have hg := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
      calc h⁻¹ * ↑g * h * y = h⁻¹ * (↑g * (h * y * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * y * h⁻¹) * ↑g) * h := by rw [hg]
        _ = y * (h⁻¹ * ↑g * h) := by group)⟩⟩
  left_inv g := Subtype.ext (by simp only; group)
  right_inv g := Subtype.ext (by simp only; group)
  map_mul' g g' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem fi23_card_component_inf {e e' : CFSG.Sporadic.Fi23.J} (he : e ∈ CFSG.Sporadic.Fi23.D23)
    (he' : e' ∈ LocalClass CFSG.Sporadic.Fi23.D23 e)
    {B : Subgroup ↥(Subgroup.centralizer ({e} : Set CFSG.Sporadic.Fi23.J) ⊓
      Subgroup.centralizer {e'})}
    (hB : IsComponent B) : Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  obtain ⟨h, hd, hd1⟩ := CFSG.Sporadic.Fi23.exists_conj_pair he he'
  have hx : h⁻¹ * e * h⁻¹⁻¹ = CFSG.Sporadic.Fi23.d := by rw [← hd]; group
  have hy : h⁻¹ * e' * h⁻¹⁻¹ = CFSG.Sporadic.Fi23.d1 := by rw [← hd1]; group
  have eq : ↥(Subgroup.centralizer ({e} : Set CFSG.Sporadic.Fi23.J) ⊓ Subgroup.centralizer {e'}) ≃*
      ↥(Subgroup.centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J) ⊓
        Subgroup.centralizer {CFSG.Sporadic.Fi23.d1}) :=
    (infCentralizerConj h⁻¹ e e').trans (MulEquiv.subgroupCongr (by rw [hx, hy]))
  obtain ⟨B', hB', hcard⟩ := component_transport _ _ eq hB
  rw [hcard]
  obtain ⟨ρ, hρ, hρk⟩ := exists_hom_fi23_inf
  have hker : Group.IsSolvable ρ.ker := by
    have h2 : IsPGroup 2 ρ.ker := fun u => ⟨2, Subtype.ext (by
      have h := hρk u u.2
      rw [SubmonoidClass.coe_pow, show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, sq, sq]
      exact h)⟩
    exact @IsNilpotent.to_isSolvable _ _ h2.isNilpotent
  rw [@card_quotient_center_of_component_simple
    ↥(Subgroup.centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J) ⊓
      Subgroup.centralizer {CFSG.Sporadic.Fi23.d1}) CFSG.Fischer.T46
    inferInstance inferInstance inferInstance ρ hρ hker CFSG.Fischer.isSimpleGroup_T46
    exists_noncomm_T46 B' hB', CFSG.Fischer.card_T46]

end Fi23Inf

section Tree

@[expose] def fo24GenG (l : ℕ) : J := if l = 1 then CFSG.Sporadic.Fi24.a else CFSG.Sporadic.Fi24.b

theorem rep_fo24Gens (l : ℕ) :
    Rep 306936 (fo24Gens CFSG.Sporadic.Fi24.orb l) (fo24GenG l) := by
  unfold fo24Gens fo24GenG
  by_cases h : l = 1
  · rw [ite_eq_left h, ite_eq_left h]
    exact CFSG.Sporadic.Fi24.rep_alpha
  · rw [ite_eq_right h, ite_eq_right h]
    exact CFSG.Sporadic.Fi24.rep_beta

abbrev fo24BInv : Table := invT nPts CFSG.Sporadic.Fi24.orb.beta

theorem rep_fo24GensInv (l : ℕ) :
    Rep 306936 (fo24GensInv CFSG.Sporadic.Fi24.orb fo24BInv l) (fo24GenG l)⁻¹ := by
  unfold fo24GensInv fo24GenG
  by_cases h : l = 1
  · rw [ite_eq_left h, ite_eq_left h, CFSG.Sporadic.Fi24.a_inv]
    exact CFSG.Sporadic.Fi24.rep_alpha
  · rw [ite_eq_right h, ite_eq_right h]
    exact Rep.inv_of_invOK CFSG.Sporadic.Fi24.rep_beta CFSG.Sporadic.Fi24.actionFacts.beta_inv

abbrev fo24PL : Table := fo24Packed CFSG.Sporadic.Fi24.orb

abbrev fo24Cls (k : ℕ) (q : Array ℕ) : Array ℕ :=
  fo24ClsAt CFSG.Sporadic.Fi24.orb fo24BInv fo24PL fi24TP k q

@[expose] def fo24W (k : ℕ) : J := treeElt fo24PL fo24GenG k

theorem fo24W_root : ∀ k < 306936, idx 306936 (fo24W k) 0 = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    unfold fo24W
    rw [treeElt.eq_def]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      have : ¬ (0 < 0 ∧ treePar (fo24PL[0]!).toNat < 0) := by omega
      rw [dite_eq_right this, idx_one]
    · obtain ⟨hpar, hlab⟩ := fo24Packed_facts k hk hpos
      obtain ⟨hlt, hcase⟩ := CFSG.Sporadic.Fi24.tree_facts k hk hpos
      have hp : treePar (fo24PL[k]!).toNat = ap CFSG.Sporadic.Fi24.orb.par k := hpar
      have hl : treeLab (fo24PL[k]!).toNat = ap CFSG.Sporadic.Fi24.orb.lab k := hlab
      have hcond : 0 < k ∧ treePar (fo24PL[k]!).toNat < k := ⟨hpos, by rw [hp]; exact hlt⟩
      rw [dite_eq_left hcond, idx_mul]
      have ih' := ih (treePar (fo24PL[k]!).toNat) hcond.2 (by omega)
      have hpk : ap CFSG.Sporadic.Fi24.orb.par k < 306936 := by omega
      rw [show treeElt fo24PL fo24GenG (treePar (fo24PL[k]!).toNat) =
        fo24W (treePar (fo24PL[k]!).toNat) from rfl, ih', hp, hl,
        ← rep_fo24Gens (ap CFSG.Sporadic.Fi24.orb.lab k) (ap CFSG.Sporadic.Fi24.orb.par k) hpk]
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1]
        exact h2
      · rw [h1]
        exact h2

theorem fo24W_smul_root (k : Fin 306936) : fo24W k • CFSG.Sporadic.Fi24.root = k := by
  apply Fin.ext
  rw [← idx_of_lt (fo24W k) (show (0 : ℕ) < 306936 by norm_num)]
  exact fo24W_root k k.2

theorem cls_eq_fo24W (k : Fin 306936) :
    cls k = jR (fo24W k) * tR * (jR (fo24W k))⁻¹ :=
  CFSG.Sporadic.Fi24.cls_eq_conj_of_smul_root (by
    rw [CFSG.Sporadic.Fi24.jR_smul]
    exact fo24W_smul_root k)

theorem fo24Cls_spec (k : Fin 306936) (q : Array ℕ) (hq : ∀ j < q.size, q[j]! < 306936) :
    (fo24Cls k q).size = q.size ∧
      ∀ j < q.size, (fo24Cls k q)[j]! = idx 306936 (cls k) q[j]! := by
  obtain ⟨h1s, h1⟩ := applyTreeInv_spec (n := 306936) rep_fo24GensInv fo24PL k q hq
  show (applyTree fo24PL (fo24Gens CFSG.Sporadic.Fi24.orb) k (apT fi24TP
      (applyTreeInv fo24PL (fo24GensInv CFSG.Sporadic.Fi24.orb fo24BInv) k q))).size = q.size ∧
    ∀ j < q.size, (applyTree fo24PL (fo24Gens CFSG.Sporadic.Fi24.orb) k (apT fi24TP
      (applyTreeInv fo24PL (fo24GensInv CFSG.Sporadic.Fi24.orb fo24BInv) k q)))[j]! =
        idx 306936 (cls k) q[j]!
  generalize hdef : applyTreeInv fo24PL (fo24GensInv CFSG.Sporadic.Fi24.orb fo24BInv) k q = q₁
    at h1s h1 ⊢
  have hq₁ : ∀ j < q₁.size, q₁[j]! < 306936 := fun j hj => by
    rw [h1 j (h1s ▸ hj)]
    exact idx_lt _ (hq j (h1s ▸ hj))
  have h2 : ∀ j < q₁.size, (apT fi24TP q₁)[j]! = idx 306936 tR q₁[j]! := fun j hj => by
    rw [apT_get _ _ hj, rep_fi24TP _ (hq₁ j hj)]
  have hq₂ : ∀ j < (apT fi24TP q₁).size, (apT fi24TP q₁)[j]! < 306936 := fun j hj => by
    rw [apT_size] at hj
    rw [h2 j hj]
    exact idx_lt _ (hq₁ j hj)
  obtain ⟨h3s, h3⟩ := applyTree_spec (n := 306936) rep_fo24Gens fo24PL k (apT fi24TP q₁) hq₂
  refine ⟨by rw [h3s, apT_size, h1s], fun j hj => ?_⟩
  have hj₁ : j < q₁.size := by rw [h1s]; exact hj
  have hj₂ : j < (apT fi24TP q₁).size := by rw [apT_size]; exact hj₁
  rw [h3 j hj₂, h2 j hj₁, h1 j hj, cls_eq_fo24W, idx_mul, idx_mul, ← map_inv,
    CFSG.Sporadic.Fi24.idx_jR, CFSG.Sporadic.Fi24.idx_jR]
  rfl

theorem rep_fo24Cls (k : Fin 306936) :
    ∀ x < 306936, (fo24Cls k (Array.range nPts))[x]! = idx 306936 (cls k) x := by
  intro x hx
  have hq : ∀ j < (Array.range nPts).size, (Array.range nPts)[j]! < 306936 := fun j hj => by
    rw [getElem!_pos (Array.range nPts) j hj, Array.getElem_range]
    rw [Array.size_range] at hj
    exact hj
  have hxs : x < (Array.range nPts).size := by rw [Array.size_range]; exact hx
  rw [(fo24Cls_spec k _ hq).2 x hxs, getElem!_pos _ x hxs, Array.getElem_range]

theorem cls_smul_eq_iff (k l : Fin 306936) :
    cls k • l = l ↔ cls k * cls l = cls l * cls k := by
  constructor
  · intro h
    have := CFSG.Sporadic.Fi24.cls_smul_R (cls k) l
    rw [h] at this
    calc cls k * cls l = cls k * cls l * (cls k)⁻¹ * cls k := by group
      _ = cls l * cls k := by rw [← this]
  · intro h
    apply CFSG.Sporadic.Fi24.cls_injective
    rw [CFSG.Sporadic.Fi24.cls_smul_R, h, mul_inv_cancel_right]

end Tree

section Triple

theorem conj_eq_of_perfect_of_invariant_hom {G H : Type*} [Group G] [Group H] (f : H →* G)
    {Y : Set G} (hY : Y.Finite) (hY3 : Y.ncard ≤ 3)
    (hinv : ∀ c : H, ∀ y ∈ Y, f c * y * (f c)⁻¹ ∈ Y) {B : Subgroup H}
    (hB : Group.IsPerfect B) {b : H} (hb : b ∈ B) {y : G} (hy : y ∈ Y) :
    f b * y * (f b)⁻¹ = y := by
  have := hB
  have hB' : Group.IsPerfect (B.map f.rangeRestrict) := Group.IsPerfect.map f.rangeRestrict
  exact conj_eq_of_perfect_of_invariant (H := f.range) hY hY3
    (fun c hc y hy => by obtain ⟨c', rfl⟩ := hc; exact hinv c' y hy) hB'
    (b := f.rangeRestrict b) ⟨b, hb, rfl⟩ hy

@[expose] def fi24CJ (r : R) : Subgroup J := (Subgroup.centralizer ({r} : Set R)).comap jR

theorem mem_fi24CJ {r : R} {g : J} : g ∈ fi24CJ r ↔ jR g * r = r * jR g :=
  CFSG.Sporadic.Fi24.mem_centralizer_R

@[expose] def triCent (a b c : R) : Subgroup J :=
  (Subgroup.centralizer ({a} : Set R) ⊓ Subgroup.centralizer {b} ⊓
    Subgroup.centralizer {c}).comap jR

theorem mem_triCent {a b c : R} {g : J} :
    g ∈ triCent a b c ↔ jR g * a = a * jR g ∧ jR g * b = b * jR g ∧ jR g * c = c * jR g := by
  rw [triCent, Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf,
    CFSG.Sporadic.Fi24.mem_centralizer_R, CFSG.Sporadic.Fi24.mem_centralizer_R,
    CFSG.Sporadic.Fi24.mem_centralizer_R, and_assoc]

@[expose] def triCentConj (h : J) (a b c : R) :
    ↥(triCent a b c) ≃* ↥(triCent (jR h * a * (jR h)⁻¹) (jR h * b * (jR h)⁻¹)
      (jR h * c * (jR h)⁻¹)) where
  toFun g := ⟨h * g * h⁻¹, by
    obtain ⟨h1, h2, h3⟩ := mem_triCent.1 g.2
    rw [mem_triCent, map_mul, map_mul, map_inv]
    exact ⟨conj_commute_conj (jR h) (jR (g : J)) a h1, conj_commute_conj (jR h) (jR (g : J)) b h2,
      conj_commute_conj (jR h) (jR (g : J)) c h3⟩⟩
  invFun g := ⟨h⁻¹ * g * h, by
    obtain ⟨h1, h2, h3⟩ := mem_triCent.1 g.2
    have key : ∀ {x : R}, jR (g : J) * (jR h * x * (jR h)⁻¹) =
        jR h * x * (jR h)⁻¹ * jR (g : J) → jR (h⁻¹ * g * h) * x = x * jR (h⁻¹ * g * h) := by
      intro x hx
      have := conj_commute_conj (jR h)⁻¹ (jR (g : J)) (jR h * x * (jR h)⁻¹) hx
      rw [map_mul, map_mul, map_inv]
      calc (jR h)⁻¹ * jR (g : J) * jR h * x =
          (jR h)⁻¹ * jR (g : J) * (jR h)⁻¹⁻¹ * ((jR h)⁻¹ * (jR h * x * (jR h)⁻¹) * (jR h)⁻¹⁻¹) := by
            group
        _ = (jR h)⁻¹ * (jR h * x * (jR h)⁻¹) * (jR h)⁻¹⁻¹ * ((jR h)⁻¹ * jR (g : J) * (jR h)⁻¹⁻¹) :=
            this
        _ = x * ((jR h)⁻¹ * jR (g : J) * jR h) := by group
    exact mem_triCent.2 ⟨key h1, key h2, key h3⟩⟩
  left_inv g := Subtype.ext (by simp only; group)
  right_inv g := Subtype.ext (by simp only; group)
  map_mul' g g' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem fo24Triple_facts {Rt : Table} {r : R} (hR : Rep 306936 Rt r) {u : Array ℕ}
    (h : fo24TripleOK CFSG.Sporadic.Fi24.orb fo24BInv fo24PL fi24TP Rt u = true)
    (hu : u[0]! ≠ u[1]! ∧ u[0]! ≠ u[2]! ∧ u[1]! ≠ u[2]!) :
    ∃ k₁ k₂ k₃ : Fin 306936, (k₁ ≠ k₂ ∧ k₁ ≠ k₃ ∧ k₂ ≠ k₃) ∧ r = cls k₁ * cls k₂ * cls k₃ ∧
      (∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), r • k = k) ∧
      (∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), ∀ l : Fin 306936, r • l = l →
        cls k * cls l = cls l * cls k) ∧
      (∀ k : Fin 306936, r • k = k → (∀ l : Fin 306936, r • l = l →
        cls k * cls l = cls l * cls k) → k ∈ ({k₁, k₂, k₃} : Set (Fin 306936))) := by
  unfold fo24TripleOK fo24TripleAt fo24CommOK fo24ProdOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, -⟩, hu3⟩, hcomm⟩, hprod⟩ := h
  have hu' : ∀ i < 3, u[i]! < 306936 ∧ ap Rt u[i]! = u[i]! := fun i hi => by
    have := allIn_eq_true.1 hu3 i (Nat.zero_le _) hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this
  set F := (Array.range nPts).filter fun i => ap Rt i == i with hFdef
  have hsmul : ∀ x : Fin 306936, (r • x).val = ap Rt x.val := fun x => by
    rw [hR x.val x.2, idx_of_lt r x.2]
  have hFmem : ∀ x : ℕ, x ∈ F ↔ x < nPts ∧ ap Rt x = x := fun x => by
    simp only [hFdef, Array.mem_filter, Array.mem_range, beq_iff_eq]
  have hFget : ∀ j (hj : j < F.size), F[j] < 306936 ∧ ap Rt F[j] = F[j] := fun j hj =>
    (hFmem F[j]).1 (Array.getElem_mem hj)
  have hFlt : ∀ j < F.size, F[j]! < 306936 := fun j hj => by
    rw [getElem!_pos F j hj]
    exact (hFget j hj).1
  have hFfull : ∀ l : Fin 306936, r • l = l → ∃ j < F.size, F[j]! = l.val := fun l hl => by
    have hm : l.val ∈ F := (hFmem l.val).2 ⟨l.2, by rw [← hsmul l, hl]⟩
    obtain ⟨j, hj, hjl⟩ := Array.mem_iff_getElem.1 hm
    exact ⟨j, hj, by rw [getElem!_pos F j hj]; exact hjl⟩
  have hrow : ∀ (k : Fin 306936), (fo24Cls k F = F ↔
      ∀ l : Fin 306936, r • l = l → cls k * cls l = cls l * cls k) := by
    intro k
    obtain ⟨hs, he⟩ := fo24Cls_spec k F hFlt
    constructor
    · intro h l hl
      obtain ⟨j, hj, hjl⟩ := hFfull l hl
      rw [← cls_smul_eq_iff]
      apply Fin.ext
      have := he j hj
      rw [h, hjl, idx_of_lt _ l.2] at this
      exact this.symm
    · intro h
      apply Array.ext hs
      intro j h1 h2
      have := he j h2
      rw [getElem!_pos _ j h1, getElem!_pos F j h2] at this
      rw [this]
      have hfx : r • (⟨F[j], (hFget j h2).1⟩ : Fin 306936) = ⟨F[j], (hFget j h2).1⟩ := by
        apply Fin.ext
        rw [hsmul]
        exact (hFget j h2).2
      have hc := (cls_smul_eq_iff k _).2 (h _ hfx)
      rw [idx_of_lt _ (hFget j h2).1, hc]
  obtain ⟨k₁, hk₁⟩ : ∃ k : Fin 306936, k.val = u[0]! := ⟨⟨u[0]!, (hu' 0 (by norm_num)).1⟩, rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k : Fin 306936, k.val = u[1]! := ⟨⟨u[1]!, (hu' 1 (by norm_num)).1⟩, rfl⟩
  obtain ⟨k₃, hk₃⟩ : ∃ k : Fin 306936, k.val = u[2]! := ⟨⟨u[2]!, (hu' 2 (by norm_num)).1⟩, rfl⟩
  have hmemK : ∀ k : Fin 306936, k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)) ↔
      (k.val = u[0]! ∨ k.val = u[1]!) ∨ k.val = u[2]! := fun k => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff, hk₁, hk₂, hk₃, or_assoc]
  have hfixk : ∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), r • k = k := by
    intro k hk
    apply Fin.ext
    rw [hsmul]
    rcases (hmemK k).1 hk with (h | h) | h <;> rw [h]
    · exact (hu' 0 (by norm_num)).2
    · exact (hu' 1 (by norm_num)).2
    · exact (hu' 2 (by norm_num)).2
  have htest : ∀ k : Fin 306936, r • k = k → (fo24Cls k F = F ↔
      k ∈ ({k₁, k₂, k₃} : Set (Fin 306936))) := by
    intro k hk
    obtain ⟨j, hj, hjk⟩ := hFfull k hk
    have h1 : (fo24Cls k F == F) = (k.val == u[0]! || k.val == u[1]! || k.val == u[2]!) := by
      have := allIn_eq_true.1 hcomm j (Nat.zero_le _) hj
      rw [beq_iff_eq, hjk] at this
      exact this
    rw [hmemK]
    refine beq_iff_eq.symm.trans ?_
    rw [h1]
    simp only [Bool.or_eq_true, beq_iff_eq]
  refine ⟨k₁, k₂, k₃, ⟨fun e => hu.1 (by rw [← hk₁, ← hk₂, e]),
      fun e => hu.2.1 (by rw [← hk₁, ← hk₃, e]), fun e => hu.2.2 (by rw [← hk₂, ← hk₃, e])⟩,
    ?_, hfixk, fun k hk l hl => (hrow k).1 ((htest k (hfixk k hk)).2 hk) l hl,
    fun k hk hc => (htest k hk).1 ((hrow k).2 hc)⟩
  refine fi24_rep_unique hR fun x hx => ?_
  have := allIn_eq_true.1 hprod x (Nat.zero_le _) hx
  simp only [beq_iff_eq] at this
  rw [← hk₁, ← hk₂, ← hk₃] at this
  rw [rep_fo24Cls k₃ x hx, rep_fo24Cls k₂ _ (idx_lt (cls k₃) hx),
    rep_fo24Cls k₁ _ (idx_lt (cls k₂) (idx_lt (cls k₃) hx))] at this
  rw [this, idx_mul, idx_mul]

theorem fo24_triple_perm {r : R} {K : Set (Fin 306936)}
    (hfix : ∀ k ∈ K, r • k = k)
    (hcomm : ∀ k ∈ K, ∀ l : Fin 306936, r • l = l → cls k * cls l = cls l * cls k)
    (hchar : ∀ k : Fin 306936, r • k = k → (∀ l : Fin 306936, r • l = l →
      cls k * cls l = cls l * cls k) → k ∈ K)
    {c : R} (hc : c * r = r * c) {k : Fin 306936} (hk : k ∈ K) : c • k ∈ K := by
  have hc' : c⁻¹ * r = r * c⁻¹ := by
    calc c⁻¹ * r = c⁻¹ * (r * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * r) * c⁻¹ := by rw [hc]
      _ = r * c⁻¹ := by group
  apply hchar
  · rw [← mul_smul, ← hc, mul_smul, hfix k hk]
  · intro l hl
    have hl' : r • (c⁻¹ • l) = c⁻¹ • l := by
      rw [← mul_smul, ← hc', mul_smul, hl]
    have h1 := hcomm k hk _ hl'
    have e2 := CFSG.Sporadic.Fi24.cls_smul_R c (c⁻¹ • l)
    rw [smul_inv_smul] at e2
    rw [CFSG.Sporadic.Fi24.cls_smul_R, e2]
    exact conj_commute_conj c (cls k) (cls (c⁻¹ • l)) h1

end Triple

section Star

@[expose] def starTr {x : R} (hx : x ∈ LocalClass D24 tR) : CFSG.Sporadic.Fi23.J :=
  CFSG.Sporadic.Fi24.fi23EquivJMR ⟨x * tR, CFSG.Sporadic.Fi24.mul_tR_mem_MR hx⟩

theorem triCent_tR_map {x y : R} (hx : x ∈ LocalClass D24 tR) (hy : y ∈ LocalClass D24 tR) :
    (triCent tR x y).map jR =
      (Subgroup.centralizer ({starTr hx} : Set CFSG.Sporadic.Fi23.J) ⊓
        Subgroup.centralizer {starTr hy}).map CFSG.Sporadic.Fi24.fromFi23 := by
  ext ℓ
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨h1, h2, h3⟩ := mem_triCent.1 hg
    have hm : jR g ∈ MR := ⟨g, (CFSG.Sporadic.Fi24.commute_tR_iff g).1 h1, rfl⟩
    refine Subgroup.mem_map.2 ⟨CFSG.Sporadic.Fi24.fi23EquivJMR ⟨jR g, hm⟩,
      Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · rw [CFSG.Sporadic.Fi24.mem_centralizer_Fi23, starTr, ← map_mul, ← map_mul]
      refine congrArg _ (Subtype.ext ?_)
      show jR g * (x * tR) = x * tR * jR g
      rw [← mul_assoc, h2, mul_assoc, h1, mul_assoc]
    · rw [CFSG.Sporadic.Fi24.mem_centralizer_Fi23, starTr, ← map_mul, ← map_mul]
      refine congrArg _ (Subtype.ext ?_)
      show jR g * (y * tR) = y * tR * jR g
      rw [← mul_assoc, h3, mul_assoc, h1, mul_assoc]
    · rw [CFSG.Sporadic.Fi24.fromFi23_apply, MulEquiv.symm_apply_apply]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
    have hm : CFSG.Sporadic.Fi24.fromFi23 w ∈ MR := (CFSG.Sporadic.Fi24.fi23EquivJMR.symm w).2
    obtain ⟨g, hgM, hg⟩ := hm
    have hT := (CFSG.Sporadic.Fi24.commute_tR_iff g).2 hgM
    have key : ∀ {z : R} (hz : z ∈ LocalClass D24 tR),
        w ∈ Subgroup.centralizer ({starTr hz} : Set CFSG.Sporadic.Fi23.J) →
        jR g * z = z * jR g := by
      intro z hz hwz
      have hc := CFSG.Sporadic.Fi24.mem_centralizer_Fi23.1 hwz
      have hc' : jR g * (z * tR) = z * tR * jR g := by
        have := congrArg (fun v => ((CFSG.Sporadic.Fi24.fi23EquivJMR.symm v : MR) : R)) hc
        simp only [map_mul, Subgroup.coe_mul, starTr, MulEquiv.symm_apply_apply] at this
        rw [← CFSG.Sporadic.Fi24.fromFi23_apply, ← hg] at this
        exact this
      calc jR g * z = jR g * (z * tR) * tR := by
            rw [mul_assoc, mul_assoc, CFSG.Sporadic.Fi24.tR_mul_tR, mul_one]
        _ = z * tR * jR g * tR := by rw [hc']
        _ = z * (tR * jR g * tR) := by simp only [mul_assoc]
        _ = z * jR g := by rw [← hT, mul_assoc, CFSG.Sporadic.Fi24.tR_mul_tR, mul_one]
    exact Subgroup.mem_map.2 ⟨g, mem_triCent.2 ⟨hT, key hx hw1, key hy hw2⟩, hg⟩

theorem triCent_tR_component {x y : R} (hx : x ∈ LocalClass D24 tR)
    (hy : y ∈ LocalClass D24 tR) (hxy : x * y = y * x) (hne : x ≠ y)
    {B : Subgroup (triCent tR x y)} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  have eqv : ↥(triCent tR x y) ≃*
      ↥(Subgroup.centralizer ({starTr hx} : Set CFSG.Sporadic.Fi23.J) ⊓
        Subgroup.centralizer {starTr hy}) :=
    ((triCent tR x y).equivMapOfInjective jR CFSG.Sporadic.Fi24.jR_injective).trans
      ((MulEquiv.subgroupCongr (triCent_tR_map hx hy)).trans
        (Subgroup.equivMapOfInjective _ CFSG.Sporadic.Fi24.fromFi23
          CFSG.Sporadic.Fi24.fromFi23_injective).symm)
  obtain ⟨B', hB', hc⟩ := component_transport _ _ eqv hB
  rw [hc]
  have hne' : starTr hy ≠ starTr hx := by
    intro h
    apply hne
    have h' := CFSG.Sporadic.Fi24.fi23EquivJMR.injective h
    simp only [Subtype.mk.injEq] at h'
    exact (mul_right_cancel h').symm
  have hcomm : starTr hy * starTr hx = starTr hx * starTr hy := by
    unfold starTr
    rw [← map_mul, ← map_mul]
    refine congrArg _ (Subtype.ext ?_)
    show y * tR * (x * tR) = x * tR * (y * tR)
    rw [CFSG.Sporadic.Fi24.mul_tR_mul_mul_tR hx, CFSG.Sporadic.Fi24.mul_tR_mul_mul_tR hy, hxy]
  exact fi23_card_component_inf (e := starTr hx) (e' := starTr hy)
    (CFSG.Sporadic.Fi24.isConj_d_fi23EquivJMR hx)
    ⟨CFSG.Sporadic.Fi24.isConj_d_fi23EquivJMR hy, hne', hcomm⟩ hB'

theorem triCent_component {k₁ k₂ k₃ : Fin 306936} (hne : k₁ ≠ k₂ ∧ k₁ ≠ k₃ ∧ k₂ ≠ k₃)
    (h21 : cls k₂ * cls k₁ = cls k₁ * cls k₂) (h31 : cls k₃ * cls k₁ = cls k₁ * cls k₃)
    (h23 : cls k₂ * cls k₃ = cls k₃ * cls k₂)
    {B : Subgroup (triCent (cls k₁) (cls k₂) (cls k₃))} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  obtain ⟨h, hh⟩ := CFSG.Sporadic.Fi24.exists_conj_eq_tR (CFSG.Sporadic.Fi24.cls_mem k₁)
  have hmemD : ∀ k, jR h * cls k * (jR h)⁻¹ ∈ D24 := fun k => by
    rw [← CFSG.Sporadic.Fi24.cls_smul_R]
    exact CFSG.Sporadic.Fi24.cls_mem _
  have hne' : ∀ {a b : Fin 306936}, a ≠ b → jR h * cls a * (jR h)⁻¹ ≠ jR h * cls b * (jR h)⁻¹ :=
    fun hab e => hab (CFSG.Sporadic.Fi24.cls_injective (mul_left_cancel (mul_right_cancel e)))
  have hx : jR h * cls k₂ * (jR h)⁻¹ ∈ LocalClass D24 tR :=
    ⟨hmemD k₂, by rw [← hh]; exact hne' hne.1.symm,
      by rw [← hh]; exact conj_commute_conj (jR h) (cls k₂) (cls k₁) h21⟩
  have hy : jR h * cls k₃ * (jR h)⁻¹ ∈ LocalClass D24 tR :=
    ⟨hmemD k₃, by rw [← hh]; exact hne' hne.2.1.symm,
      by rw [← hh]; exact conj_commute_conj (jR h) (cls k₃) (cls k₁) h31⟩
  have e : ↥(triCent (cls k₁) (cls k₂) (cls k₃)) ≃*
      ↥(triCent tR (jR h * cls k₂ * (jR h)⁻¹) (jR h * cls k₃ * (jR h)⁻¹)) :=
    (triCentConj h (cls k₁) (cls k₂) (cls k₃)).trans (MulEquiv.subgroupCongr (by rw [hh]))
  obtain ⟨B', hB', hc⟩ := component_transport _ _ e hB
  rw [hc]
  exact triCent_tR_component hx hy (conj_commute_conj (jR h) (cls k₂) (cls k₃) h23)
    (hne' hne.2.2) hB'

end Star

section Fix

theorem conjJ_surjective : Function.Surjective CFSG.Sporadic.Fi24.conjJ :=
  MonoidHom.range_eq_top.1 (CFSG.Sporadic.Fi24.range_conjJ_eq_top
    (CFSG.Sporadic.Fi24.pow_mem_innerAut_J polarFacts CFSG.Sporadic.Fi22.card_fixed_involution_D
      CFSG.Sporadic.Fi22.eq_of_commute_centralizer CFSG.Sporadic.Fi24.edgeSwap_a
      CFSG.Sporadic.Fi23.d1_mem_localClass CFSG.Sporadic.Fi23.involution_cover)
    (CFSG.Sporadic.Fi24.complete_R polarFacts hyperovalFacts
      (CFSG.Sporadic.Fi22.fi22Facts polarFacts hyperovalFacts)
      (CFSG.Sporadic.Fi23.fi23Facts (CFSG.Sporadic.Fi22.fi22Facts polarFacts hyperovalFacts))))

@[expose] def fixSubEquivCJ {G : Type*} [Group G] (θ : G ≃* J) (α : MulAut G) (r : R)
    (hr : ∀ x, θ (α x) = CFSG.Sporadic.Fi24.conjJ r (θ x)) : fixSub α ≃* fi24CJ r where
  toFun g := ⟨θ g, by
    have h : α g = g := g.2
    rw [mem_fi24CJ]
    have h2 := congrArg jR ((hr g).symm.trans (congrArg θ h))
    rw [CFSG.Sporadic.Fi24.jR_conjJ] at h2
    calc jR (θ g) * r = r * jR (θ g) * r⁻¹ * r := by rw [h2]
      _ = r * jR (θ g) := by group⟩
  invFun y := ⟨θ.symm y, by
    show α (θ.symm y) = θ.symm y
    apply θ.injective
    rw [hr, MulEquiv.apply_symm_apply]
    apply CFSG.Sporadic.Fi24.jR_injective
    rw [CFSG.Sporadic.Fi24.jR_conjJ, ← mem_fi24CJ.1 y.2, mul_inv_cancel_right]⟩
  left_inv g := Subtype.ext (θ.symm_apply_apply g)
  right_inv y := Subtype.ext (θ.apply_symm_apply y)
  map_mul' g h := Subtype.ext (map_mul θ (g : G) (h : G))

@[expose] def fi24CJConj (c r : R) : fi24CJ r ≃* fi24CJ (c * r * c⁻¹) where
  toFun g := ⟨CFSG.Sporadic.Fi24.conjJ c g, by
    rw [mem_fi24CJ, CFSG.Sporadic.Fi24.jR_conjJ]
    exact conj_commute_conj c (jR (g : J)) r (mem_fi24CJ.1 g.2)⟩
  invFun g := ⟨CFSG.Sporadic.Fi24.conjJ c⁻¹ g, by
    rw [mem_fi24CJ, CFSG.Sporadic.Fi24.jR_conjJ]
    have h := conj_commute_conj c⁻¹ (jR (g : J)) (c * r * c⁻¹) (mem_fi24CJ.1 g.2)
    rwa [show c⁻¹ * (c * r * c⁻¹) * c⁻¹⁻¹ = r by group] at h⟩
  left_inv g := Subtype.ext (CFSG.Sporadic.Fi24.jR_injective (by
    show jR (CFSG.Sporadic.Fi24.conjJ c⁻¹ (CFSG.Sporadic.Fi24.conjJ c g)) = jR g
    rw [CFSG.Sporadic.Fi24.jR_conjJ, CFSG.Sporadic.Fi24.jR_conjJ]
    group))
  right_inv g := Subtype.ext (CFSG.Sporadic.Fi24.jR_injective (by
    show jR (CFSG.Sporadic.Fi24.conjJ c (CFSG.Sporadic.Fi24.conjJ c⁻¹ g)) = jR g
    rw [CFSG.Sporadic.Fi24.jR_conjJ, CFSG.Sporadic.Fi24.jR_conjJ]
    group))
  map_mul' g h := Subtype.ext (map_mul _ _ _)

end Fix

section Classes

theorem fi24CJ_tR : fi24CJ tR = M := by
  ext g
  rw [mem_fi24CJ, CFSG.Sporadic.Fi24.commute_tR_iff]

theorem fi24CJ_tR_component {B : Subgroup (fi24CJ tR)} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 4089470473293004800 := by
  obtain ⟨B', hB', hc⟩ := component_transport _ _ (MulEquiv.subgroupCongr fi24CJ_tR) hB
  rw [hc]
  have hs := CFSG.Sporadic.Fi24.isSimpleGroup_M
  refine (@card_quotient_center_of_component_simple M M inferInstance inferInstance inferInstance
    (MonoidHom.id M) Function.surjective_id ?_ hs
    (exists_noncomm_of_isSimpleGroup hs (by rw [CFSG.Sporadic.Fi24.card_M]; norm_num))
    B' hB').trans CFSG.Sporadic.Fi24.card_M
  rw [(MonoidHom.ker_eq_bot_iff _).2 Function.injective_id]
  infer_instance

theorem fi24D_mul_tR_mem :
    fi24D * tR ∈ D24 :=
  fo24_facts.1

theorem fi24U2T_triple :
    TripleFacts (fi24U2 * tR) :=
  fo24_facts.2.1

theorem fi24U3T_triple :
    TripleFacts (fi24U3 * tR) :=
  fo24_facts.2.2

theorem fi24CJ_DT_component {B : Subgroup (fi24CJ (fi24D * tR))} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 4089470473293004800 := by
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Fi24.exists_conj_eq_tR fi24D_mul_tR_mem
  have e : fi24CJ (fi24D * tR) ≃* fi24CJ tR :=
    (fi24CJConj (jR g) (fi24D * tR)).trans (MulEquiv.subgroupCongr (by rw [hg]))
  obtain ⟨B', hB', hc⟩ := component_transport _ _ e hB
  rw [hc]
  exact fi24CJ_tR_component hB'

theorem fi24CJ_triple_component {r : R} {k₁ k₂ k₃ : Fin 306936}
    (hne : k₁ ≠ k₂ ∧ k₁ ≠ k₃ ∧ k₂ ≠ k₃) (hr : r = cls k₁ * cls k₂ * cls k₃)
    (hfix : ∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), r • k = k)
    (hcomm : ∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), ∀ l : Fin 306936, r • l = l →
      cls k * cls l = cls l * cls k)
    (hchar : ∀ k : Fin 306936, r • k = k → (∀ l : Fin 306936, r • l = l →
      cls k * cls l = cls l * cls k) → k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)))
    {B : Subgroup (fi24CJ r)} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  have m1 : k₁ ∈ ({k₁, k₂, k₃} : Set (Fin 306936)) := by simp
  have m2 : k₂ ∈ ({k₁, k₂, k₃} : Set (Fin 306936)) := by simp
  have m3 : k₃ ∈ ({k₁, k₂, k₃} : Set (Fin 306936)) := by simp
  have hY : (cls '' ({k₁, k₂, k₃} : Set (Fin 306936))).Finite := (Set.toFinite _).image cls
  have hY3 : (cls '' ({k₁, k₂, k₃} : Set (Fin 306936))).ncard ≤ 3 := by
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    have h1 := Set.ncard_insert_le k₁ ({k₂, k₃} : Set (Fin 306936))
    have h2 := Set.ncard_insert_le k₂ ({k₃} : Set (Fin 306936))
    rw [Set.ncard_singleton] at h2
    omega
  have hinv : ∀ c : fi24CJ r, ∀ y ∈ cls '' ({k₁, k₂, k₃} : Set (Fin 306936)),
      (jR.comp (fi24CJ r).subtype) c * y * ((jR.comp (fi24CJ r).subtype) c)⁻¹ ∈
        cls '' ({k₁, k₂, k₃} : Set (Fin 306936)) := by
    rintro c _ ⟨k, hk, rfl⟩
    exact ⟨jR c • k, fo24_triple_perm hfix hcomm hchar (mem_fi24CJ.1 c.2) hk,
      CFSG.Sporadic.Fi24.cls_smul_R (jR c) k⟩
  have key : ∀ b ∈ B, ∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)),
      jR (b : J) * cls k = cls k * jR (b : J) := by
    intro b hb k hk
    have h0 : jR (b : J) * cls k * (jR (b : J))⁻¹ = cls k :=
      @conj_eq_of_perfect_of_invariant_hom R (fi24CJ r) inferInstance inferInstance
        (jR.comp (fi24CJ r).subtype) _ hY hY3 hinv B hB.1.1 b hb (cls k) ⟨k, hk, rfl⟩
    calc jR (b : J) * cls k = jR (b : J) * cls k * (jR (b : J))⁻¹ * jR (b : J) := by group
      _ = cls k * jR (b : J) := by rw [h0]
  have hLC : triCent (cls k₁) (cls k₂) (cls k₃) ≤ fi24CJ r := by
    intro g hg
    obtain ⟨h1, h2, h3⟩ := mem_triCent.1 hg
    rw [mem_fi24CJ, hr]
    calc jR g * (cls k₁ * cls k₂ * cls k₃) = jR g * cls k₁ * cls k₂ * cls k₃ := by
          simp only [mul_assoc]
      _ = cls k₁ * (jR g * cls k₂) * cls k₃ := by rw [h1]; simp only [mul_assoc]
      _ = cls k₁ * cls k₂ * (jR g * cls k₃) := by rw [h2]; simp only [mul_assoc]
      _ = cls k₁ * cls k₂ * cls k₃ * jR g := by rw [h3]; simp only [mul_assoc]
  obtain ⟨B', hB', hc⟩ := component_restrict (fi24CJ r) (triCent (cls k₁) (cls k₂) (cls k₃)) hLC
    hB fun b hb => mem_triCent.2 ⟨key b hb k₁ m1, key b hb k₂ m2, key b hb k₃ m3⟩
  rw [hc]
  have hfx : ∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), ∀ k' ∈ ({k₁, k₂, k₃} : Set (Fin 306936)),
      cls k * cls k' = cls k' * cls k := fun k hk k' hk' => hcomm k hk k' (hfix k' hk')
  exact triCent_component hne (hfx k₂ m2 k₁ m1) (hfx k₃ m3 k₁ m1) (hfx k₂ m2 k₃ m3) hB'

theorem fi24CJ_U2T_component {B : Subgroup (fi24CJ (fi24U2 * tR))} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  obtain ⟨k₁, k₂, k₃, hne, hr, hfix, hcomm, hchar⟩ := fi24U2T_triple
  exact fi24CJ_triple_component hne hr hfix hcomm hchar hB

theorem fi24CJ_U3T_component {B : Subgroup (fi24CJ (fi24U3 * tR))} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  obtain ⟨k₁, k₂, k₃, hne, hr, hfix, hcomm, hchar⟩ := fi24U3T_triple
  exact fi24CJ_triple_component hne hr hfix hcomm hchar hB

theorem fi24_outer_components {r : R} (hr2 : r * r = 1) (hrJ : r ∉ JR)
    {B : Subgroup (fi24CJ r)} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 4089470473293004800 ∨
      Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  have hr1 : r ≠ 1 := fun h => hrJ (h ▸ JR.one_mem)
  obtain ⟨s, hs, hsr⟩ := fi24_involution_class hr2 hr1
  obtain ⟨c, hc⟩ := (isConj_iff (α := R)).1 hsr
  have e : fi24CJ r ≃* fi24CJ s :=
    (MulEquiv.subgroupCongr (by rw [hc])).trans (fi24CJConj c s).symm
  obtain ⟨B', hB', hc'⟩ := component_transport _ _ e hB
  rw [hc']
  have hsJ : s ∉ JR := fun h => hrJ (by
    rw [← hc]
    exact CFSG.Sporadic.Fi24.normal_JR.conj_mem s h c)
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (CFSG.Sporadic.Fi24.MR_le_JR (fi23ToR_mem _)) hsJ
  · exact absurd (CFSG.Sporadic.Fi24.MR_le_JR (fi23ToR_mem _)) hsJ
  · exact absurd (CFSG.Sporadic.Fi24.MR_le_JR (fi23ToR_mem _)) hsJ
  · exact Or.inl (fi24CJ_tR_component hB')
  · exact Or.inl (fi24CJ_DT_component hB')
  · exact Or.inr (fi24CJ_U2T_component hB')
  · exact Or.inr (fi24CJ_U3T_component hB')

end Classes

theorem fi24J_outer_components {G : Type*} [Group G] (θ : G ≃* J) (α : MulAut G)
    (hα2 : α * α = 1) (hαn : α ∉ inner G) {B : Subgroup (fixSub α)} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 4089470473293004800 ∨
      Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  obtain ⟨r, hr⟩ := conjJ_surjective ((θ.symm.trans α).trans θ)
  have hrx : ∀ x : G, θ (α x) = CFSG.Sporadic.Fi24.conjJ r (θ x) := fun x => by
    rw [hr]
    show θ (α x) = θ (α (θ.symm (θ x)))
    rw [MulEquiv.symm_apply_apply]
  have hr2 : r * r = 1 := by
    apply CFSG.Sporadic.Fi24.conjJ_injective
    rw [map_mul, map_one, hr]
    refine MulEquiv.ext fun x => ?_
    show θ (α (θ.symm (θ (α (θ.symm x))))) = x
    rw [MulEquiv.symm_apply_apply, ← MulAut.mul_apply, hα2, MulAut.one_apply,
      MulEquiv.apply_symm_apply]
  have hrJ : r ∉ JR := by
    intro hJ
    obtain ⟨j, rfl⟩ : r ∈ jR.range := by rw [CFSG.Sporadic.Fi24.range_jR]; exact hJ
    apply hαn
    refine ⟨θ.symm j, MulEquiv.ext fun x => θ.injective ?_⟩
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hrx,
      CFSG.Sporadic.Fi24.conjJ_jR, MulAut.conj_apply]
  obtain ⟨B', hB', hc⟩ := component_transport _ _ (fixSubEquivCJ θ α r hrx) hB
  rw [hc]
  exact fi24_outer_components hr2 hrJ hB'

open CFSG.ComponentClassification.RestrictedStd.Spor in
theorem fi24primeOuterComponentsInput_holds : Fi24primeOuterComponentsInput := by
  intro G _ ⟨e⟩ α hα2 hαn B hB
  exact fi24J_outer_components (e.trans CFSG.Sporadic.Fi24.fi24EquivJ) α hα2 hαn hB

end CFSG.Sporadic.FischerOddCore
