module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.Quasithin.Background.G64C512Ext
public import CFSG.Quasithin.Background.G64ProofBasic

public section

namespace CFSG.Quasithin.H13.A6.L13825

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Groups

variable {M : Type} [Group M]

theorem le_classClosure_of_simple {GH GK : Subgroup M} {a : M} (ha : a ∈ GH) (hKH : GK ≤ GH)
    (hKn : GH ≤ Subgroup.normalizer (GK : Set M)) (hs : IsSimpleGroup ↥GK)
    (haK : ∃ k ∈ GK, a * k ≠ k * a) : GK ≤ conjClosure (Subgroup.zpowers a) GH := by
  set C := conjClosure (Subgroup.zpowers a) GH with hC
  have hCn : GH ≤ Subgroup.normalizer (C : Set M) := le_normalizer_conjClosure _ _
  have hn : ((C ⊓ GK).subgroupOf GK).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxC, hxK⟩ := Subgroup.mem_inf.mp hx
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hCn (hKH g.2)) x).mp hxC,
      GK.mul_mem (GK.mul_mem g.2 hxK) (GK.inv_mem g.2)⟩⟩
  obtain ⟨k, hk, hka⟩ := haK
  have haC : a ∈ C := le_conjClosure _ _ (Subgroup.mem_zpowers a)
  have hmem : a * k * a⁻¹ * k⁻¹ ∈ C ⊓ GK := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : k * a⁻¹ * k⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hCn (hKH hk)) a⁻¹).mp (C.inv_mem haC)
      have e : a * k * a⁻¹ * k⁻¹ = a * (k * a⁻¹ * k⁻¹) := by group
      rw [e]
      exact C.mul_mem haC h1
    · have h1 : a * k * a⁻¹ ∈ GK := (Subgroup.mem_normalizer_iff.mp (hKn ha) k).mp hk
      exact GK.mul_mem h1 (GK.inv_mem hk)
  have hne : a * k * a⁻¹ * k⁻¹ ≠ 1 := by
    intro h
    apply hka
    calc a * k = a * k * a⁻¹ * k⁻¹ * (k * a) := by group
      _ = k * a := by rw [h, one_mul]
  have := hs
  have := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((C ⊓ GK).subgroupOf GK) with h | h
  · exfalso
    have : (⟨a * k * a⁻¹ * k⁻¹, hmem.2⟩ : ↥GK) ∈ (C ⊓ GK).subgroupOf GK :=
      Subgroup.mem_subgroupOf.mpr hmem
    rw [h, Subgroup.mem_bot] at this
    exact hne (congrArg Subtype.val this)
  · intro x hx
    have : (⟨x, hx⟩ : ↥GK) ∈ (C ⊓ GK).subgroupOf GK := by rw [h]; exact Subgroup.mem_top _
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).1

theorem mem_normalizer_of_comm {A B : Subgroup M} (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    {y : M} (hy : y ∈ B) : y ∈ Subgroup.normalizer (A : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hcomm x hx y hy, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := hcomm _ hx y⁻¹ (B.inv_mem hy)
    have e : x = y⁻¹ * (y * x * y⁻¹) * y := by group
    rw [e, ← h1, mul_assoc, inv_mul_cancel, mul_one]
    exact hx

theorem inf_eq_bot_of_conj {GK A B : Subgroup M} {t : M}
    (htK : t ∈ Subgroup.normalizer (GK : Set M)) (hAB : A.map (MulAut.conj t).toMonoidHom = B)
    (hdis : A ⊓ B = ⊥) (hne : GK ≠ ⊥) (hnA : GK ≤ Subgroup.normalizer (A : Set M))
    (hs : IsSimpleGroup ↥GK) : GK ⊓ A = ⊥ := by
  have hn : ((GK ⊓ A).subgroupOf GK).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxK, hxA⟩ := Subgroup.mem_inf.mp hx
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_inf.mpr ⟨GK.mul_mem (GK.mul_mem g.2 hxK) (GK.inv_mem g.2),
      (Subgroup.mem_normalizer_iff.mp (hnA g.2) x).mp hxA⟩⟩
  have := hs
  have := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((GK ⊓ A).subgroupOf GK) with h | h
  · refine le_bot_iff.mp fun x hx => ?_
    have : (⟨x, hx.1⟩ : ↥GK) ∈ (GK ⊓ A).subgroupOf GK := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    have hKA : GK ≤ A := fun x hx => by
      have : (⟨x, hx⟩ : ↥GK) ∈ (GK ⊓ A).subgroupOf GK := by rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).2
    have hKB : GK ≤ B := by
      rw [← hAB, ← CFSG.Quasithin.A38.map_conj_eq_iff.mpr htK]
      exact Subgroup.map_mono hKA
    apply hne
    rw [eq_bot_iff, ← hdis]
    exact le_inf hKA hKB

theorem comm_of_inf_eq_bot {GK A : Subgroup M} (h : GK ⊓ A = ⊥)
    (hnA : GK ≤ Subgroup.normalizer (A : Set M)) (hnK : A ≤ Subgroup.normalizer (GK : Set M)) :
    ∀ g ∈ GK, ∀ y ∈ A, g * y = y * g := by
  intro g hg y hy
  have h1 : g * y * g⁻¹ * y⁻¹ ∈ GK ⊓ A := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have : y * g⁻¹ * y⁻¹ ∈ GK :=
        (Subgroup.mem_normalizer_iff.mp (hnK hy) g⁻¹).mp (GK.inv_mem hg)
      have e : g * y * g⁻¹ * y⁻¹ = g * (y * g⁻¹ * y⁻¹) := by group
      rw [e]
      exact GK.mul_mem hg this
    · exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hnA hg) y).mp hy) (A.inv_mem hy)
  rw [h, Subgroup.mem_bot] at h1
  calc g * y = g * y * g⁻¹ * y⁻¹ * (y * g) := by group
    _ = y * g := by rw [h1, one_mul]

theorem false_of_two_factors_simple {GK K₁ K₂ : Subgroup M} {t : M}
    (hKK : GK ≤ K₁ ⊔ K₂) (hdis : K₁ ⊓ K₂ = ⊥) (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (htK : t ∈ Subgroup.normalizer (GK : Set M))
    (ht : K₁.map (MulAut.conj t).toMonoidHom = K₂)
    (hKn : K₁ ⊔ K₂ ≤ Subgroup.normalizer (GK : Set M)) (hs : IsSimpleGroup ↥GK)
    (hna : ∃ x ∈ GK, ∃ y ∈ GK, x * y ≠ y * x) : False := by
  have hcomm' : ∀ x ∈ K₂, ∀ y ∈ K₁, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hn₁ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set M) :=
    sup_le Subgroup.le_normalizer fun y hy => mem_normalizer_of_comm hcomm hy
  have hn₂ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set M) :=
    sup_le (fun y hy => mem_normalizer_of_comm hcomm' hy) Subgroup.le_normalizer
  have hne : GK ≠ ⊥ := by
    rintro rfl
    obtain ⟨x, hx, y, hy, hxy⟩ := hna
    rw [Subgroup.mem_bot] at hx hy
    exact hxy (by rw [hx, hy])
  have ht' : K₂.map (MulAut.conj t⁻¹).toMonoidHom = K₁ := by
    rw [← ht, Subgroup.map_map]
    convert Subgroup.map_id K₁ using 2
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  have h₁ := inf_eq_bot_of_conj htK ht hdis hne (hKK.trans hn₁) hs
  have h₂ := inf_eq_bot_of_conj (Subgroup.inv_mem _ htK) ht' (by rw [inf_comm, hdis]) hne
    (hKK.trans hn₂) hs
  have c₁ := comm_of_inf_eq_bot h₁ (hKK.trans hn₁) (le_sup_left.trans hKn)
  have c₂ := comm_of_inf_eq_bot h₂ (hKK.trans hn₂) (le_sup_right.trans hKn)
  have hC : K₁ ⊔ K₂ ≤ Subgroup.centralizer (GK : Set M) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_) <;> rw [Subgroup.mem_centralizer_iff] <;>
      intro g hg
    · exact c₁ g hg y hy
    · exact c₂ g hg y hy
  obtain ⟨x, hx, y, hy, hxy⟩ := hna
  exact hxy (Subgroup.mem_centralizer_iff.mp (hC (hKK hy)) x hx)

theorem eq_alternatingGroup_of_normal {m : ℕ} (hm : 5 ≤ m) {N : Subgroup (Equiv.Perm (Fin m))}
    (hN : N.Normal) (hs : IsSimpleGroup ↥N) (hna : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x) :
    N = alternatingGroup (Fin m) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hm)
  have hNA : ((N ⊓ alternatingGroup (Fin m)).subgroupOf N).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxN, hxA⟩ := Subgroup.mem_inf.mp hx
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_inf.mpr ⟨N.mul_mem (N.mul_mem g.2 hxN) (N.inv_mem g.2),
      (alternatingGroup.normal (α := Fin m)).conj_mem _ hxA _⟩⟩
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((N ⊓ alternatingGroup (Fin m)).subgroupOf N) with h | h
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := hna
    have hc : x * y * x⁻¹ * y⁻¹ ∈ N ⊓ alternatingGroup (Fin m) := by
      refine Subgroup.mem_inf.mpr ⟨N.mul_mem (N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx))
        (N.inv_mem hy), ?_⟩
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [mul_comm (Equiv.Perm.sign x) (Equiv.Perm.sign y), mul_assoc, mul_assoc,
        ← mul_assoc (Equiv.Perm.sign x), mul_inv_cancel, one_mul, mul_inv_cancel]
    have : (⟨x * y * x⁻¹ * y⁻¹, hc.1⟩ : ↥N) ∈ (N ⊓ alternatingGroup (Fin m)).subgroupOf N :=
      Subgroup.mem_subgroupOf.mpr hc
    rw [h, Subgroup.mem_bot] at this
    have h1 : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val this
    apply hxy
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  · have hNA' : N ≤ alternatingGroup (Fin m) := fun x hx => by
      have : (⟨x, hx⟩ : ↥N) ∈ (N ⊓ alternatingGroup (Fin m)).subgroupOf N := by
        rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).2
    have hn' : (N.subgroupOf (alternatingGroup (Fin m))).Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hN.conj_mem _ hx _⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin m)))
      with h' | h'
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := hna
      have h1 : (⟨x, hNA' hx⟩ : ↥(alternatingGroup (Fin m))) ∈
          N.subgroupOf (alternatingGroup (Fin m)) := Subgroup.mem_subgroupOf.mpr hx
      have h2 : (⟨y, hNA' hy⟩ : ↥(alternatingGroup (Fin m))) ∈
          N.subgroupOf (alternatingGroup (Fin m)) := Subgroup.mem_subgroupOf.mpr hy
      rw [h', Subgroup.mem_bot] at h1 h2
      have hx1 : x = 1 := congrArg Subtype.val h1
      have hy1 : y = 1 := congrArg Subtype.val h2
      exact hxy (by rw [hx1, hy1])
    · refine le_antisymm hNA' fun x hx => ?_
      have : (⟨x, hx⟩ : ↥(alternatingGroup (Fin m))) ∈ N.subgroupOf (alternatingGroup (Fin m)) :=
        by rw [h']; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this

end Groups

section G64

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def Sym8Data (GH GK : Subgroup (MulAut V)) : Prop :=
  ∃ (Z : Subgroup (G6.PermMod 8)) (π : Equiv.Perm (Fin 8) →* ↥GH)
    (β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 8) ⧸ Z.subgroupOf (G6.coreMod 8)),
    Z ≤ Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8 ∧
    Function.Surjective π ∧ Function.Surjective β ∧ (∀ u, β u = 1 → u = 1) ∧
    (∀ (σ : Equiv.Perm (Fin 8)) (u : ↥(⊤ : Subgroup V)) (m : ↥(G6.coreMod 8)),
      β u = QuotientGroup.mk m →
      β ⟨((π σ : ↥GH) : MulAut V) (u : V), trivial⟩ =
        QuotientGroup.mk ⟨G6.permAct 8 σ (m : G6.PermMod 8), G6.permAct_mem_coreMod σ m.2⟩) ∧
    ∀ σ : Equiv.Perm (Fin 8), ((π σ : ↥GH) : MulAut V) ∈ GK ↔ σ ∈ alternatingGroup (Fin 8)

theorem card_sl_ge (n : ℕ) (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    168 ≤ Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega), Nat.card_zmod]
  interval_cases n <;> decide

omit [Finite V] in
theorem sym_case {GH GK : Subgroup (MulAut V)} (hKH : GK ≤ GH)
    (hKn : GH ≤ Subgroup.normalizer (GK : Set (MulAut V))) {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5)
    (e : ↥GK ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (hs : IsSimpleGroup ↥GK)
    (hna : ∃ x ∈ GK, ∃ y ∈ GK, x * y ≠ y * x) {m : ℕ} (hm5 : 5 ≤ m) (hm8 : m ≤ 8)
    {π : Equiv.Perm (Fin m) →* ↥GH} (hsurj : Function.Surjective π)
    (hinj : Function.Injective π) :
    m = 8 ∧ n = 4 ∧
      ∀ σ : Equiv.Perm (Fin m), ((π σ : ↥GH) : MulAut V) ∈ GK ↔ σ ∈ alternatingGroup (Fin m) := by
  set N := (GK.subgroupOf GH).comap π with hN
  have hKnorm : (GK.subgroupOf GH).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hKn g.2) x).mp hx⟩
  have hNn : N.Normal := hKnorm.comap π
  have hmap : N.map π = GK.subgroupOf GH := Subgroup.map_comap_eq_self_of_surjective hsurj _
  let eN : ↥N ≃* ↥GK := (N.equivMapOfInjective π hinj).trans
    ((MulEquiv.subgroupCongr hmap).trans (Subgroup.subgroupOfEquivOfLe hKH))
  have hNs : IsSimpleGroup ↥N := eN.isSimpleGroup
  have hNna : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hna
    refine ⟨(eN.symm ⟨x, hx⟩ : _), (eN.symm ⟨x, hx⟩).2, (eN.symm ⟨y, hy⟩ : _),
      (eN.symm ⟨y, hy⟩).2, fun h => hxy ?_⟩
    have h1 : eN.symm ⟨x, hx⟩ * eN.symm ⟨y, hy⟩ = eN.symm ⟨y, hy⟩ * eN.symm ⟨x, hx⟩ :=
      Subtype.ext h
    have h2 := congrArg (fun z => ((eN z : ↥GK) : MulAut V)) h1
    simpa using h2
  have hNA := eq_alternatingGroup_of_normal hm5 hNn hNs hNna
  have hcard : Nat.card ↥GK = Nat.card ↥(alternatingGroup (Fin m)) := by
    rw [← hNA]
    exact (Nat.card_congr eN.toEquiv).symm
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard' : Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = m.factorial / 2 := by
    rw [← Nat.card_congr e.toEquiv, hcard, nat_card_alternatingGroup, Nat.card_fin]
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega), Nat.card_zmod]
    at hcard'
  have hmn : m = 8 ∧ n = 4 := by
    interval_cases m <;> interval_cases n <;>
      first | exact ⟨rfl, rfl⟩ | (exfalso; revert hcard'; decide)
  refine ⟨hmn.1, hmn.2, fun σ => ?_⟩
  rw [← hNA, hN, Subgroup.mem_comap, Subgroup.mem_subgroupOf]

theorem g64_cases (h64 : G64.LemmaG64) (hV2 : ∀ v : V, v ^ 2 = 1)
    {GH GK : Subgroup (MulAut V)} {a : MulAut V} (hyp : G64.Hyp61 GH a)
    (htr : Nat.card ↥(commV (Subgroup.zpowers a)) = 2) (hKH : GK ≤ GH)
    (hKn : GH ≤ Subgroup.normalizer (GK : Set (MulAut V))) {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5)
    (e : ↥GK ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (hcomm : commV GK = ⊤)
    (haK : ∃ k ∈ GK, a * k ≠ k * a) :
    (GK = GH ∧ BinaryNaturalSL GK ⊤ ⊥ n 1) ∨ (n = 4 ∧ Sym8Data GH GK) := by
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) hn3
  have hs : IsSimpleGroup ↥GK := e.isSimpleGroup
  have hna : ∃ x ∈ GK, ∃ y ∈ GK, x * y ≠ y * x := by
    obtain ⟨x₀, y₀, hxy₀⟩ :=
      CFSG.QuasithinUnique.Vol2Native.A312L.sl_nonabelian_of_card_two (Nat.card_zmod 2) hn3
    refine ⟨(e.symm x₀ : _), (e.symm x₀).2, (e.symm y₀ : _), (e.symm y₀).2, fun h => hxy₀ ?_⟩
    have h1 : e.symm x₀ * e.symm y₀ = e.symm y₀ * e.symm x₀ := Subtype.ext h
    have h2 := congrArg e h1
    simpa using h2
  have hKC := le_classClosure_of_simple hyp.mem hKH hKn hs haK
  have hCH : conjClosure (Subgroup.zpowers a) GH ≤ GH := G64.classK_le hyp
  obtain ⟨s, Ks, -, hsup, hind, hcK, -, -, -, -, -, hmod, h3, -⟩ := h64 V hV2 GH a hyp htr
  rcases h3 with ⟨rfl, hGHK⟩ | ⟨rfl, -, t, htG, -, -, -, hswap⟩
  swap
  ·
    exfalso
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have hsup2 : (⨆ i, Ks i) = Ks 0 ⊔ Ks 1 := by
      refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup Ks 0) (le_iSup Ks 1))
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    have hdis : Ks 0 ⊓ Ks 1 = ⊥ := disjoint_iff.mp (hind.pairwiseDisjoint h01)
    have hKK : GK ≤ Ks 0 ⊔ Ks 1 := hsup2 ▸ hsup ▸ hKC
    have hKn' : Ks 0 ⊔ Ks 1 ≤ Subgroup.normalizer (GK : Set (MulAut V)) :=
      ((hsup2 ▸ hsup ▸ le_refl _ : Ks 0 ⊔ Ks 1 ≤ conjClosure (Subgroup.zpowers a) GH).trans
        hCH).trans hKn
    exact false_of_two_factors_simple hKK hdis (hcK 0 1 h01) (hKn htG) (hswap 0 1 h01) hKn' hs
      hna
  have hK0 : Ks 0 = conjClosure (Subgroup.zpowers a) GH := by
    rw [← hsup]
    refine le_antisymm (le_iSup Ks 0) (iSup_le fun i => ?_)
    rw [Subsingleton.elim i 0]
  have hGH : GH = Ks 0 := hGHK.trans hK0.symm
  have hcommGH : commV GH = ⊤ := eq_top_iff.mpr (hcomm ▸ CFSG.Quasithin.G6.commV_mono hKH)
  have hmod0 := hmod 0
  rw [← hGH, hcommGH] at hmod0
  have hKeq : IsSimpleGroup ↥GH → GK = GH := by
    intro hsG
    have hKnorm : (GK.subgroupOf GH).Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hKn g.2) x).mp hx⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GK.subgroupOf GH) with h | h
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := hna
      have h1 : (⟨x, hKH hx⟩ : ↥GH) ∈ GK.subgroupOf GH := Subgroup.mem_subgroupOf.mpr hx
      have h2 : (⟨y, hKH hy⟩ : ↥GH) ∈ GK.subgroupOf GH := Subgroup.mem_subgroupOf.mpr hy
      rw [h, Subgroup.mem_bot] at h1 h2
      have hx1 : x = 1 := congrArg Subtype.val h1
      have hy1 : y = 1 := congrArg Subtype.val h2
      exact hxy (by rw [hx1, hy1])
    · refine le_antisymm hKH fun x hx => ?_
      have : (⟨x, hx⟩ : ↥GH) ∈ GK.subgroupOf GH := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  rcases hmod0 with ⟨m, hm2, hm5, hnat⟩ | ⟨m, hm5, hm8, hsym⟩ | ⟨m, hm68, hcore⟩
  ·
    left
    obtain ⟨F, hF, hFf, hF2, π, hπ⟩ := id hnat
    have hF2' : Nat.card F = 2 := by simpa using hF2
    have hinj : Function.Injective π :=
      FFModel.RealizesVia.injective_of_faithful (FFModel.nat_faithful _) hπ
    let eG : ↥(StatedSL m F) ≃* ↥GH := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
    have hcardK : 168 ≤ Nat.card ↥GK := by
      rw [Nat.card_congr e.toEquiv]
      exact card_sl_ge n hn3 hn5
    have hcardG : Nat.card ↥GH = Nat.card (Matrix.SpecialLinearGroup (Fin m) F) := by
      rw [← Nat.card_congr eG.toEquiv,
        Nat.card_congr (specialLinearGroupEquivStatedSL m F).toEquiv]
    have hm3 : 3 ≤ m := by
      by_contra hm
      have hm2' : m = 2 := by omega
      subst hm2'
      have h6 : Nat.card ↥GH = 6 := by
        rw [← Nat.card_congr eG.toEquiv]
        exact G64.card_statedSL_two hF2'
      have := Subgroup.card_le_of_le hKH
      omega
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin m) F) :=
      CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two hF2' hm3
    have hsG : IsSimpleGroup ↥GH :=
      (eG.symm.trans (specialLinearGroupEquivStatedSL m F).symm).isSimpleGroup
    have hKG := hKeq hsG
    have hc1 : Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) =
        Nat.card (Matrix.SpecialLinearGroup (Fin m) F) := by
      rw [← Nat.card_congr e.toEquiv, ← hcardG, hKG]
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega),
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega), Nat.card_zmod,
      hF2'] at hc1
    have hmn : m = n := by
      interval_cases m <;> interval_cases n <;> first | rfl | (exfalso; revert hc1; decide)
    subst hmn
    refine ⟨hKG, ?_⟩
    rw [hKG]
    exact hnat
  ·
    right
    obtain ⟨π, hπ⟩ := hsym
    have hinj : Function.Injective π :=
      FFModel.RealizesVia.injective_of_faithful (G64.symDn_faithful hm5) hπ
    obtain ⟨rfl, hn4, hA⟩ := sym_case hKH hKn hn3 hn5 e hs hna hm5 hm8 hπ.1 hinj
    obtain ⟨hsurj, -, -, -, -, -, -, β₀, hβs, hβk, hβe⟩ := hπ
    exact ⟨hn4, _, π, β₀, le_rfl, hsurj, hβs,
      fun u hu => Subtype.ext (by simpa using (hβk u).1 hu),
      fun σ u m h => hβe σ u m trivial _ h, hA⟩
  ·
    right
    obtain ⟨π, hπ⟩ := hcore
    have hm5 : 5 ≤ m := by omega
    have hinj : Function.Injective π :=
      FFModel.RealizesVia.injective_of_faithful (G64.symCore_faithful (by omega)) hπ
    obtain ⟨rfl, hn4, hA⟩ := sym_case hKH hKn hn3 hn5 e hs hna hm5 (by omega) hπ.1 hinj
    obtain ⟨hsurj, -, -, -, -, -, -, β₀, hβs, hβk, hβe⟩ := hπ
    exact ⟨hn4, ⊥, π, β₀, bot_le, hsurj, hβs,
      fun u hu => Subtype.ext (by simpa using (hβk u).1 hu),
      fun σ u m h => hβe σ u m trivial _ h, hA⟩

@[expose] def sig3 : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def sig7 : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5 *
    Equiv.swap 5 6

theorem sig3_mem : sig3 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, sig3, map_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  decide

theorem sig7_mem : sig7 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, sig7]
  simp only [map_mul, Equiv.Perm.sign_swap (show (0 : Fin 8) ≠ 1 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 8) ≠ 2 by decide),
    Equiv.Perm.sign_swap (show (2 : Fin 8) ≠ 3 by decide),
    Equiv.Perm.sign_swap (show (3 : Fin 8) ≠ 4 by decide),
    Equiv.Perm.sign_swap (show (4 : Fin 8) ≠ 5 by decide),
    Equiv.Perm.sign_swap (show (5 : Fin 8) ≠ 6 by decide)]
  decide

theorem fix_d8 : ∀ x : G6.PermMod 8, ∑ i, Multiplicative.toAdd x i = 0 →
    (G6.permAct 8 sig3 x * x⁻¹ = 1 ∨ G6.permAct 8 sig3 x * x⁻¹ = G6.allOnes 8) →
    (G6.permAct 8 sig7 x * x⁻¹ = 1 ∨ G6.permAct 8 sig7 x * x⁻¹ = G6.allOnes 8) →
    x = 1 ∨ x = G6.allOnes 8 := by
  decide +kernel

theorem mem_zpowers_allOnes {n : ℕ} {y : G6.PermMod n} :
    y ∈ Subgroup.zpowers (G6.allOnes n) ↔ y = 1 ∨ y = G6.allOnes n := by
  constructor
  · rintro ⟨k, rfl⟩
    have hk : ((k : ZMod 2) = 0) ∨ ((k : ZMod 2) = 1) := by
      generalize (k : ZMod 2) = c
      revert c
      decide
    rcases hk with hk | hk
    · left
      apply Multiplicative.toAdd.injective
      funext i
      simp only [toAdd_zpow, G6.allOnes, toAdd_ofAdd, Pi.smul_apply, zsmul_eq_mul, mul_one,
        toAdd_one, Pi.zero_apply]
      exact hk
    · right
      apply Multiplicative.toAdd.injective
      funext i
      simp only [toAdd_zpow, G6.allOnes, toAdd_ofAdd, Pi.smul_apply, zsmul_eq_mul, mul_one]
      exact hk
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem permAct_allOnes (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    G6.permAct n σ (G6.allOnes n) = G6.allOnes n := by
  apply Multiplicative.toAdd.injective
  funext i
  rfl

theorem permAct_mem_d8ker (σ : Equiv.Perm (Fin 8)) {m : G6.PermMod 8}
    (hm : m ∈ Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8) :
    G6.permAct 8 σ m ∈ Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8 := by
  obtain ⟨hm1, -⟩ := Subgroup.mem_inf.mp hm
  rcases mem_zpowers_allOnes.mp hm1 with rfl | rfl
  · rw [map_one]
    exact Subgroup.one_mem _
  · rw [permAct_allOnes]
    exact hm

omit [Finite V] in
theorem realizesVia_altDn8 {GK : Subgroup (MulAut V)} {Z' : Subgroup V}
    (π' : ↥(alternatingGroup (Fin 8)) →* ↥GK) (hπ' : Function.Surjective π')
    (hZ' : ∀ k : ↥GK, ∀ z ∈ Z', (k : MulAut V) z ∈ Z')
    (β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 8) ⧸
      (Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8).subgroupOf (G6.coreMod 8))
    (hβs : Function.Surjective β) (hβk : ∀ u, β u = 1 ↔ (u : V) ∈ Z')
    (hβe : ∀ (γ : ↥(alternatingGroup (Fin 8))) (u : ↥(⊤ : Subgroup V)) (m : ↥(G6.coreMod 8)),
      β u = QuotientGroup.mk m →
      β ⟨((π' γ : ↥GK) : MulAut V) (u : V), trivial⟩ =
        QuotientGroup.mk ⟨G6.permAct 8 (γ : Equiv.Perm (Fin 8)) (m : G6.PermMod 8),
          G6.permAct_mem_coreMod _ m.2⟩) :
    (FFModel.altDn 8).RealizesVia GK ⊤ Z' π' :=
  ⟨hπ', le_top, inf_le_right, fun _ _ _ => trivial, hZ', fun _ _ hm => G6.permAct_mem_coreMod _ hm,
    fun _ _ hm => permAct_mem_d8ker _ hm, β, hβs, hβk, fun γ u m _ _ h => hβe γ u m h⟩

omit [Finite V] in
theorem alternatingNatural_of_sym8 {GH GK : Subgroup (MulAut V)} (hKH : GK ≤ GH)
    (h : Sym8Data GH GK) : AlternatingNatural GK ⊤ (fixV GK) 8 := by
  obtain ⟨Z, π, β₀, hZle, hsurj, hβs, hβi, hβe, hA⟩ := h
  set D8 : Subgroup (G6.PermMod 8) := Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8 with hD8
  let π' : ↥(alternatingGroup (Fin 8)) →* ↥GK :=
    { toFun := fun σ => ⟨((π σ : ↥GH) : MulAut V), (hA σ).2 σ.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun σ τ => by
        apply Subtype.ext
        simp }
  let q : ↥(G6.coreMod 8) ⧸ Z.subgroupOf (G6.coreMod 8) →*
      ↥(G6.coreMod 8) ⧸ D8.subgroupOf (G6.coreMod 8) :=
    QuotientGroup.map _ _ (MonoidHom.id _) (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hZle (Subgroup.mem_subgroupOf.mp hx)))
  have hq : ∀ m : ↥(G6.coreMod 8), q (QuotientGroup.mk m) = QuotientGroup.mk m := fun _ => rfl
  refine ⟨π', realizesVia_altDn8 π' (fun k => ?_) (fun k z hz => ?_) (q.comp β₀) ?_
    (fun u => ?_) ?_⟩
  ·
    obtain ⟨σ, hσ⟩ := hsurj ⟨k, hKH k.2⟩
    have hσv : ((π σ : ↥GH) : MulAut V) = k := congrArg Subtype.val hσ
    have hσA : σ ∈ alternatingGroup (Fin 8) := (hA σ).1 (hσv ▸ k.2)
    exact ⟨⟨σ, hσA⟩, Subtype.ext hσv⟩
  ·
    rw [hz k k.2]
    exact hz
  ·
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
    exact ⟨u, by rw [MonoidHom.comp_apply, hu, hq]⟩
  ·
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₀ u)
    rw [MonoidHom.comp_apply, ← hm, hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hmD k hk
      obtain ⟨σ, hσ⟩ := hsurj ⟨k, hKH hk⟩
      have hσv : ((π σ : ↥GH) : MulAut V) = k := congrArg Subtype.val hσ
      obtain ⟨hm1, -⟩ := Subgroup.mem_inf.mp hmD
      have hfix : G6.permAct 8 σ (m : G6.PermMod 8) = m := by
        rcases mem_zpowers_allOnes.mp hm1 with h1 | h1
        · rw [h1, map_one]
        · rw [h1, permAct_allOnes]
      have he := hβe σ u m hm.symm
      have he' : β₀ ⟨((π σ : ↥GH) : MulAut V) (u : V), trivial⟩ = β₀ u := by
        rw [he, ← hm]
        congr 1
        exact Subtype.ext hfix
      have h2 : (⟨((π σ : ↥GH) : MulAut V) (u : V), trivial⟩ : ↥(⊤ : Subgroup V)) = u := by
        have h3 := hβi (⟨((π σ : ↥GH) : MulAut V) (u : V), trivial⟩ * u⁻¹) (by
          rw [map_mul, map_inv, he', mul_inv_cancel])
        rw [mul_inv_eq_one] at h3
        exact h3
      have h4 := congrArg Subtype.val h2
      simp only at h4
      rw [hσv] at h4
      exact h4
    · intro hu
      have hstep : ∀ σ ∈ alternatingGroup (Fin 8),
          G6.permAct 8 σ (m : G6.PermMod 8) * (m : G6.PermMod 8)⁻¹ = 1 ∨
            G6.permAct 8 σ (m : G6.PermMod 8) * (m : G6.PermMod 8)⁻¹ = G6.allOnes 8 := by
        intro σ hσ
        have hfix : ((π σ : ↥GH) : MulAut V) (u : V) = u := hu _ ((hA σ).2 hσ)
        have he := hβe σ u m hm.symm
        have h2 : (⟨((π σ : ↥GH) : MulAut V) (u : V), trivial⟩ : ↥(⊤ : Subgroup V)) = u :=
          Subtype.ext hfix
        rw [h2, ← hm, QuotientGroup.eq] at he
        have h3 := hZle (Subgroup.mem_subgroupOf.mp he)
        have e1 : ((m⁻¹ * ⟨G6.permAct 8 σ (m : G6.PermMod 8), G6.permAct_mem_coreMod σ m.2⟩ :
            ↥(G6.coreMod 8)) : G6.PermMod 8) =
            G6.permAct 8 σ (m : G6.PermMod 8) * (m : G6.PermMod 8)⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_comm]
          rfl
        rw [e1] at h3
        exact mem_zpowers_allOnes.mp (Subgroup.mem_inf.mp h3).1
      have hm8 := fix_d8 (m : G6.PermMod 8) (G6.mem_coreMod.mp m.2) (hstep _ sig3_mem)
        (hstep _ sig7_mem)
      exact Subgroup.mem_inf.mpr ⟨mem_zpowers_allOnes.mpr hm8, m.2⟩
  ·
    intro γ u m hβum
    obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (β₀ u)
    have he := hβe (γ : Equiv.Perm (Fin 8)) u m₀ hm₀.symm
    simp only [MonoidHom.comp_apply] at hβum ⊢
    have hu' : (⟨((π' γ : ↥GK) : MulAut V) (u : V), trivial⟩ : ↥(⊤ : Subgroup V)) =
        ⟨((π (γ : Equiv.Perm (Fin 8)) : ↥GH) : MulAut V) (u : V), trivial⟩ := rfl
    rw [hu', he, hq, QuotientGroup.eq]
    rw [← hm₀, hq, QuotientGroup.eq] at hβum
    rw [Subgroup.mem_subgroupOf] at hβum ⊢
    have h1 := permAct_mem_d8ker (γ : Equiv.Perm (Fin 8)) hβum
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul] at h1 ⊢
    exact h1

end G64

end CFSG.Quasithin.H13.A6.L13825
