module

public import CFSG.YGroups.DoubleCosetPoints
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.YGroups

variable {G : Type*} [Group G]

namespace DoubleCosetData

variable {H C : Subgroup G} {t : G} {r : ℕ} (D : DoubleCosetData H C t r)

@[expose] noncomputable def cosetMap : (Σ i : Fin r, H ⧸ (D.S i).subgroupOf H) → G ⧸ H := fun p =>
  Quotient.liftOn' p.2 (fun k : H => ((k * (D.x p.1)⁻¹ : G) : G ⧸ H)) (by
    intro k k' hkk'
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hkk'
    exact D.mk_mul_inv_eq (by simpa using hkk'))

theorem cosetMap_mk (i : Fin r) (k : H) :
    D.cosetMap ⟨i, (QuotientGroup.mk k : H ⧸ (D.S i).subgroupOf H)⟩ =
      ((k * (D.x i)⁻¹ : G) : G ⧸ H) := rfl

theorem cosetMap_surjective (hCH : C ≤ H) (ht : t * t = 1) (htC : ∀ c ∈ C, t * c = c * t)
    (hgen : Subgroup.closure ((H : Set G) ∪ {t}) = ⊤) : Function.Surjective D.cosetMap := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨i, a, ha, b, hb, hab⟩ := D.exists_eq_of_doubleCoset_data hCH ht htC hgen g⁻¹
    refine ⟨⟨i, QuotientGroup.mk (⟨b⁻¹, H.inv_mem hb⟩ : H)⟩, ?_⟩
    rw [cosetMap_mk]
    show ((b⁻¹ * (D.x i)⁻¹ : G) : G ⧸ H) = (g : G ⧸ H)
    rw [QuotientGroup.eq]
    have hg : g = b⁻¹ * (D.x i)⁻¹ * a⁻¹ := by
      rw [← inv_inv g, hab]; group
    rw [hg]
    have : (b⁻¹ * (D.x i)⁻¹)⁻¹ * (b⁻¹ * (D.x i)⁻¹ * a⁻¹) = a⁻¹ := by group
    rw [this]
    exact H.inv_mem ha

theorem card_domain [Finite G] :
    Nat.card (Σ i : Fin r, H ⧸ (D.S i).subgroupOf H) = ∑ i, (D.S i).relIndex H := by
  rw [Nat.card_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subgroup.relIndex, Subgroup.index_eq_card]

theorem cosetMap_bijective [Finite G] (hCH : C ≤ H) (ht : t * t = 1)
    (htC : ∀ c ∈ C, t * c = c * t) (hgen : Subgroup.closure ((H : Set G) ∪ {t}) = ⊤)
    (s : Fin r → ℕ) (hs : ∀ i, (D.S i).relIndex H ≤ s i) (hsum : ∑ i, s i ≤ H.index) :
    Function.Bijective D.cosetMap := by
  refine (D.cosetMap_surjective hCH ht htC hgen).bijective_of_nat_card_le ?_
  rw [card_domain, ← Subgroup.index_eq_card]
  exact (Finset.sum_le_sum fun i _ => hs i).trans hsum

theorem relIndex_eq [Finite G] (hCH : C ≤ H) (ht : t * t = 1)
    (htC : ∀ c ∈ C, t * c = c * t) (hgen : Subgroup.closure ((H : Set G) ∪ {t}) = ⊤)
    (s : Fin r → ℕ) (hs : ∀ i, (D.S i).relIndex H ≤ s i) (hsum : ∑ i, s i ≤ H.index) :
    (∀ i, (D.S i).relIndex H = s i) ∧ H.index = ∑ i, s i := by
  have hle := (D.index_le_sum hCH ht htC hgen).2
  have h1 : ∑ i, (D.S i).relIndex H = ∑ i, s i :=
    le_antisymm (Finset.sum_le_sum fun i _ => hs i) (hsum.trans hle)
  refine ⟨fun i => ?_, le_antisymm (hle.trans h1.le) hsum⟩
  exact (Finset.sum_eq_sum_iff_of_le fun i _ => hs i).1 h1 i (Finset.mem_univ i)

@[expose] noncomputable def idxIn (L : Subgroup G) : Finset (Fin r) :=
  by classical exact Finset.univ.filter fun i => (D.x i)⁻¹ ∈ L

theorem mem_idxIn {L : Subgroup G} {i : Fin r} : i ∈ D.idxIn L ↔ (D.x i)⁻¹ ∈ L := by
  classical
  unfold idxIn
  simp

@[expose] noncomputable def cosetMapIn {L : Subgroup G} (hHL : H ≤ L) :
    {p : Σ i : Fin r, H ⧸ (D.S i).subgroupOf H // p.1 ∈ D.idxIn L} → L ⧸ H.subgroupOf L :=
  fun p => Quotient.liftOn' p.1.2
    (fun k : H => (QuotientGroup.mk (⟨(k : G) * (D.x p.1.1)⁻¹,
      L.mul_mem (hHL k.2) ((D.mem_idxIn).1 p.2)⟩ : L) : L ⧸ H.subgroupOf L))
    (by
      intro k k' hkk'
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hkk'
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have := D.S_conj p.1.1 _ (by simpa using hkk')
      simpa [mul_assoc] using this)

theorem cosetMapIn_mk {L : Subgroup G} (hHL : H ≤ L) (i : Fin r) (k : H)
    (hi : i ∈ D.idxIn L) :
    D.cosetMapIn hHL ⟨⟨i, QuotientGroup.mk k⟩, hi⟩ =
      QuotientGroup.mk (⟨(k : G) * (D.x i)⁻¹, L.mul_mem (hHL k.2) ((D.mem_idxIn).1 hi)⟩ : L) :=
  rfl

theorem relIndex_eq_sum [Finite G] (hCH : C ≤ H) (ht : t * t = 1)
    (htC : ∀ c ∈ C, t * c = c * t) (hgen : Subgroup.closure ((H : Set G) ∪ {t}) = ⊤)
    (s : Fin r → ℕ) (hs : ∀ i, (D.S i).relIndex H ≤ s i) (hsum : ∑ i, s i ≤ H.index)
    {L : Subgroup G} (hHL : H ≤ L) : H.relIndex L = ∑ i ∈ D.idxIn L, s i := by
  classical
  have hbij := D.cosetMap_bijective hCH ht htC hgen s hs hsum
  have hrel := (D.relIndex_eq hCH ht htC hgen s hs hsum).1
  have hinj : Function.Injective (D.cosetMapIn hHL) := by
    rintro ⟨⟨i, q⟩, hi⟩ ⟨⟨i', q'⟩, hi'⟩ heq
    induction q using QuotientGroup.induction_on with
    | H k =>
    induction q' using QuotientGroup.induction_on with
    | H k' =>
    rw [cosetMapIn_mk, cosetMapIn_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at heq
    have h2 : D.cosetMap ⟨i, QuotientGroup.mk k⟩ = D.cosetMap ⟨i', QuotientGroup.mk k'⟩ := by
      rw [cosetMap_mk, cosetMap_mk, QuotientGroup.eq]
      simpa using heq
    have h3 := hbij.1 h2
    exact Subtype.ext h3
  have hsurj : Function.Surjective (D.cosetMapIn hHL) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H ℓ =>
    obtain ⟨⟨i, q⟩, hq⟩ := hbij.2 ((ℓ : G) : G ⧸ H)
    induction q using QuotientGroup.induction_on with
    | H k =>
    rw [cosetMap_mk, QuotientGroup.eq] at hq
    have hi : i ∈ D.idxIn L := by
      rw [mem_idxIn]
      have h1 : (k : G)⁻¹ * ((k : G) * (D.x i)⁻¹) = (D.x i)⁻¹ := by group
      have h2 : (k : G) * (D.x i)⁻¹ ∈ L := by
        have := L.mul_mem ℓ.2 (L.inv_mem (hHL hq))
        simpa [mul_assoc] using this
      rw [← h1]
      exact L.mul_mem (L.inv_mem (hHL k.2)) h2
    refine ⟨⟨⟨i, QuotientGroup.mk k⟩, hi⟩, ?_⟩
    rw [cosetMapIn_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hq
  have hcard := Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
  rw [Subgroup.relIndex, Subgroup.index_eq_card, ← hcard,
    Nat.card_congr (Equiv.subtypeSigmaEquiv _ fun i => i ∈ D.idxIn L), Nat.card_sigma]
  rw [← Finset.sum_coe_sort (D.idxIn L) s]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hrel i.1, Subgroup.relIndex, Subgroup.index_eq_card]

theorem eq_or_eq_top [Finite G] (hCH : C ≤ H) (ht : t * t = 1)
    (htC : ∀ c ∈ C, t * c = c * t) (hgen : Subgroup.closure ((H : Set G) ∪ {t}) = ⊤)
    (s : Fin r → ℕ) (hs : ∀ i, (D.S i).relIndex H ≤ s i) (hsum : ∑ i, s i ≤ H.index)
    (harith : ∀ u : Finset (Fin r), D.base ∈ u → (∑ i ∈ u, s i) ∣ ∑ i, s i →
      u = {D.base} ∨ u = Finset.univ)
    (L : Subgroup G) (hHL : H ≤ L) : L = H ∨ L = ⊤ := by
  classical
  have hidx := (D.relIndex_eq hCH ht htC hgen s hs hsum).2
  have hrelL := D.relIndex_eq_sum hCH ht htC hgen s hs hsum hHL
  have hbase : D.base ∈ D.idxIn L := by
    rw [mem_idxIn]
    exact L.inv_mem (hHL D.base_mem)
  have hdvd : (∑ i ∈ D.idxIn L, s i) ∣ ∑ i, s i := by
    rw [← hrelL, ← hidx]
    exact Subgroup.relIndex_dvd_index_of_le hHL
  rcases harith _ hbase hdvd with hu | hu
  · left
    refine le_antisymm (fun g hg => ?_) hHL
    obtain ⟨i, a, ha, b, hb, hab⟩ := D.exists_eq_of_doubleCoset_data hCH ht htC hgen g⁻¹
    have hi : i ∈ D.idxIn L := by
      rw [mem_idxIn]
      have : (D.x i)⁻¹ = b * g * a := by
        rw [show D.x i = a⁻¹ * g⁻¹ * b⁻¹ by rw [hab]; group]
        group
      rw [this]
      exact L.mul_mem (L.mul_mem (hHL hb) hg) (hHL ha)
    rw [hu, Finset.mem_singleton] at hi
    subst hi
    have : g = b⁻¹ * (D.x D.base)⁻¹ * a⁻¹ := by
      rw [← inv_inv g, hab]; group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hb) (H.inv_mem D.base_mem)) (H.inv_mem ha)
  · right
    rw [eq_top_iff]
    intro g _
    obtain ⟨i, a, ha, b, hb, hab⟩ := D.exists_eq_of_doubleCoset_data hCH ht htC hgen g⁻¹
    have hi : i ∈ D.idxIn L := by
      rw [hu]
      exact Finset.mem_univ i
    rw [mem_idxIn] at hi
    have : g = b⁻¹ * (D.x i)⁻¹ * a⁻¹ := by
      rw [← inv_inv g, hab]; group
    rw [this]
    exact L.mul_mem (L.mul_mem (L.inv_mem (hHL hb)) hi) (L.inv_mem (hHL ha))

end DoubleCosetData

namespace SymGen.Setup

variable {G E Ω : Type*} [Group G] [Group E] [MulAction E Ω] (S : Setup G E Ω)

theorem exists_pointsData (r : ℕ) (x : ℕ → G) (hx0 : x 0 ∈ S.H)
    (P : ℕ → Subgroup E) (hP : ∀ j < r, ∀ e ∈ P j, x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (R : ℕ → Finset Ω) (hR : ∀ j < r, ∀ p : Ω, ∃ q ∈ R j, ∃ e ∈ P j, e • q = p)
    (tgt : ℕ → Ω → ℕ) (u : ℕ → Ω → E)
    (htgt : ∀ j < r, ∀ q ∈ R j, tgt j q < r ∧ S.RCoset (x j * S.T q) (x (tgt j q) * S.ψ (u j q)))
    (hr : 0 < r) :
    ∃ D : DoubleCosetData S.H ((MulAction.stabilizer E S.o).map S.ψ) S.t r,
      (∀ i, D.x i = x i) ∧ (∀ i, D.S i = (P i).map S.ψ) ∧ D.base = ⟨0, hr⟩ := by
  classical
  let C : Subgroup G := (MulAction.stabilizer E S.o).map S.ψ
  let pick : Fin r → G → Ω := fun i k =>
    if hk : ∃ q ∈ R i, S.ψ (S.w q) = k then Classical.choose hk else S.o
  have pick_spec : ∀ i : Fin r, ∀ k ∈ (R i).image (fun q => S.ψ (S.w q)),
      pick i k ∈ R i ∧ S.ψ (S.w (pick i k)) = k := by
    intro i k hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hk
    have hex : ∃ q' ∈ R i, S.ψ (S.w q') = S.ψ (S.w q) := ⟨q, hq, rfl⟩
    simp only [pick, dite_eq_left hex]
    exact Classical.choose_spec hex
  let tgtF : Fin r → G → Fin r := fun i k =>
    if h : pick i k ∈ R i then ⟨tgt i (pick i k), (htgt i i.2 _ h).1⟩ else ⟨0, hr⟩
  let eltF : Fin r → G → G := fun i k =>
    if h : pick i k ∈ R i then S.ψ (u i (pick i k) * S.w (pick i k)) else 1
  have tgtF_eq : ∀ (i : Fin r) (k : G), pick i k ∈ R i →
      ((tgtF i k : Fin r) : ℕ) = tgt i (pick i k) := by
    intro i k h
    simp only [tgtF, dite_eq_left h]
  have eltF_eq : ∀ (i : Fin r) (k : G), pick i k ∈ R i →
      eltF i k = S.ψ (u i (pick i k) * S.w (pick i k)) := by
    intro i k h
    simp only [eltF, dite_eq_left h]
  let D : DoubleCosetData S.H C S.t r :=
    { x := fun i => x i
      S := fun i => (P i).map S.ψ
      rep := fun i => (R i).image (fun q => S.ψ (S.w q))
      tgt := tgtF
      tgtElt := eltF
      base := ⟨0, hr⟩
      base_mem := hx0
      S_le := fun i => Subgroup.map_le_range _ _
      S_conj := by
        intro i s hs
        obtain ⟨e, he, rfl⟩ := hs
        exact hP i i.2 e he
      rep_le := by
        intro i k hk
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hk
        exact ⟨S.w q, rfl⟩
      rep_cover := by
        intro i h hh
        obtain ⟨e, rfl⟩ := hh
        obtain ⟨q, hq, f, hf, hfq⟩ := hR i i.2 (e • S.o)
        refine ⟨S.ψ (S.w q), Finset.mem_image_of_mem _ hq, S.ψ f, Subgroup.mem_map_of_mem _ hf,
          S.ψ ((f * S.w q)⁻¹ * e), Subgroup.mem_map.2 ⟨(f * S.w q)⁻¹ * e, ?_, rfl⟩, ?_⟩
        · rw [MulAction.mem_stabilizer_iff, mul_smul, ← hfq, mul_inv_rev, mul_smul, inv_smul_smul,
            inv_smul_eq_iff, S.w_smul]
        · rw [← map_mul, ← map_mul, mul_inv_cancel_left]
      tgtElt_mem := by
        intro i k hk
        have hq := (pick_spec i k hk).1
        rw [eltF_eq i k hq]
        exact ⟨_, rfl⟩
      tgt_spec := by
        intro i k hk
        obtain ⟨hq, hwq⟩ := pick_spec i k hk
        show (x i : G) * k * S.t * (x ((tgtF i k : Fin r) : ℕ) * eltF i k)⁻¹ ∈ S.H
        rw [tgtF_eq i k hq, eltF_eq i k hq]
        have hrc := (S.rcoset_iff_mem _ _).1 (htgt i i.2 _ hq).2
        generalize pick i k = q at hq hwq hrc ⊢
        subst hwq
        have key : x i * S.ψ (S.w q) * S.t *
            (x (tgt i q) * S.ψ (u i q * S.w q))⁻¹ =
            x i * S.T q * (x (tgt i q) * S.ψ (u i q))⁻¹ := by
          unfold Setup.T
          rw [map_mul]
          group
        rw [key]
        exact hrc }
  exact ⟨D, fun _ => rfl, fun _ => rfl, rfl⟩

theorem exact_of_points [Finite G] [Finite E] (r : ℕ) (x : ℕ → G) (hx0 : x 0 ∈ S.H)
    (P : ℕ → Subgroup E) (hP : ∀ j < r, ∀ e ∈ P j, x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (R : ℕ → Finset Ω) (hR : ∀ j < r, ∀ p : Ω, ∃ q ∈ R j, ∃ e ∈ P j, e • q = p)
    (tgt : ℕ → Ω → ℕ) (u : ℕ → Ω → E)
    (htgt : ∀ j < r, ∀ q ∈ R j, tgt j q < r ∧ S.RCoset (x j * S.T q) (x (tgt j q) * S.ψ (u j q)))
    (hgen : Subgroup.closure ((S.H : Set G) ∪ {S.t}) = ⊤) (hr : 0 < r)
    (s : ℕ → ℕ) (hs : ∀ j < r, (P j).index ≤ s j)
    (hsum : ∑ j ∈ Finset.range r, s j ≤ S.H.index) :
    (∀ j < r, (P j).index = s j) ∧
      ∀ i < r, ∀ j < r, ∀ a b : E,
        ((S.ψ a * (x i)⁻¹ : G) : G ⧸ S.H) = ((S.ψ b * (x j)⁻¹ : G) : G ⧸ S.H) → i = j := by
  classical
  have hCH : (MulAction.stabilizer E S.o).map S.ψ ≤ S.H := Subgroup.map_le_range _ _
  have htC : ∀ c ∈ (MulAction.stabilizer E S.o).map S.ψ, S.t * c = c * S.t := by
    rintro _ ⟨e, he, rfl⟩
    exact (S.stab_comm e he).symm
  obtain ⟨D, hDx, hDS, -⟩ := S.exists_pointsData r x hx0 P hP R hR tgt u htgt hr
  have hs' : ∀ i : Fin r, (D.S i).relIndex S.H ≤ s i := fun i => by
    rw [hDS]
    exact (relIndex_map_range_le S.ψ (P i)).trans (hs i i.2)
  have hsum' : ∑ i : Fin r, s i ≤ S.H.index := by
    rw [Fin.sum_univ_eq_sum_range (fun j => s j) r]
    exact hsum
  refine ⟨fun j hj => le_antisymm (hs j hj) ?_, fun i hi j hj a b hab => ?_⟩
  · have h1 := (D.relIndex_eq hCH S.t_mul_t htC hgen (fun i => s i) hs' hsum').1 ⟨j, hj⟩
    rw [hDS] at h1
    rw [← h1]
    exact relIndex_map_range_le S.ψ (P j)
  · have hinj := (D.cosetMap_bijective hCH S.t_mul_t htC hgen (fun i => s i) hs' hsum').1
    have ha : S.ψ a ∈ S.H := ⟨a, rfl⟩
    have hb : S.ψ b ∈ S.H := ⟨b, rfl⟩
    have h2 := @hinj ⟨⟨i, hi⟩, QuotientGroup.mk (⟨S.ψ a, ha⟩ : S.H)⟩
      ⟨⟨j, hj⟩, QuotientGroup.mk (⟨S.ψ b, hb⟩ : S.H)⟩ (by
        rw [DoubleCosetData.cosetMap_mk, DoubleCosetData.cosetMap_mk, hDx, hDx]
        exact hab)
    have h3 := congrArg (fun p => (p.1 : ℕ)) h2
    exact h3

theorem eq_or_eq_top_of_points [Finite G] [Finite E] (r : ℕ) (x : ℕ → G) (hx0 : x 0 ∈ S.H)
    (P : ℕ → Subgroup E) (hP : ∀ j < r, ∀ e ∈ P j, x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (R : ℕ → Finset Ω) (hR : ∀ j < r, ∀ p : Ω, ∃ q ∈ R j, ∃ e ∈ P j, e • q = p)
    (tgt : ℕ → Ω → ℕ) (u : ℕ → Ω → E)
    (htgt : ∀ j < r, ∀ q ∈ R j, tgt j q < r ∧ S.RCoset (x j * S.T q) (x (tgt j q) * S.ψ (u j q)))
    (hgen : Subgroup.closure ((S.H : Set G) ∪ {S.t}) = ⊤) (hr : 0 < r)
    (s : ℕ → ℕ) (hs : ∀ j < r, (P j).index ≤ s j)
    (hsum : ∑ j ∈ Finset.range r, s j ≤ S.H.index)
    (harith : ∀ U : Finset ℕ, U ⊆ Finset.range r → 0 ∈ U →
      (∑ j ∈ U, s j) ∣ ∑ j ∈ Finset.range r, s j → U = {0} ∨ U = Finset.range r)
    (L : Subgroup G) (hHL : S.H ≤ L) : L = S.H ∨ L = ⊤ := by
  classical
  have hCH : (MulAction.stabilizer E S.o).map S.ψ ≤ S.H := Subgroup.map_le_range _ _
  have htC : ∀ c ∈ (MulAction.stabilizer E S.o).map S.ψ, S.t * c = c * S.t := by
    rintro _ ⟨e, he, rfl⟩
    exact (S.stab_comm e he).symm
  obtain ⟨D, -, hDS, hDb⟩ := S.exists_pointsData r x hx0 P hP R hR tgt u htgt hr
  have hs' : ∀ i : Fin r, (D.S i).relIndex S.H ≤ s i := fun i => by
    rw [hDS]
    exact (relIndex_map_range_le S.ψ (P i)).trans (hs i i.2)
  have hsum' : ∑ i : Fin r, s i ≤ S.H.index := by
    rw [Fin.sum_univ_eq_sum_range (fun j => s j) r]
    exact hsum
  refine D.eq_or_eq_top hCH S.t_mul_t htC hgen (fun i => s i) hs' hsum' ?_ L hHL
  intro U hbase hdvd
  have hU := harith (U.map Fin.valEmbedding) (by
      intro j hj
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
      exact Finset.mem_range.2 i.2)
    (Finset.mem_map.2 ⟨D.base, hbase, by rw [hDb]; rfl⟩) (by
      rw [Finset.sum_map, ← Fin.sum_univ_eq_sum_range (fun j => s j) r]
      exact hdvd)
  rcases hU with hU | hU
  · left
    ext i
    simp only [Finset.mem_singleton]
    constructor
    · intro hi
      have : (i : ℕ) ∈ U.map Fin.valEmbedding := Finset.mem_map.2 ⟨i, hi, rfl⟩
      rw [hU, Finset.mem_singleton] at this
      rw [hDb]
      exact Fin.ext this
    · rintro rfl
      exact hbase
  · right
    ext i
    simp only [Finset.mem_univ, iff_true]
    have : (i : ℕ) ∈ U.map Fin.valEmbedding := by
      rw [hU]
      exact Finset.mem_range.2 i.2
    obtain ⟨i', hi', he⟩ := Finset.mem_map.1 this
    rw [Fin.valEmbedding_apply, Fin.val_inj] at he
    rwa [he] at hi'

end SymGen.Setup

end CFSG.YGroups
