module

public import CFSG.RankThree.GF2n.Tim81.Sec5.I6Planes
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Sec5

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V H : Subgroup G} {h₀ : G}

theorem conjSubgroup_xOf_eq_of_conj_eq {V H : Subgroup G} {b y : G}
    (hbH : conjSubgroup b H = H) (hy : y ∈ H) (hby : conjSubgroup b V = conjSubgroup y V) :
    conjSubgroup b (Tim79a.xOf V H) = Tim79a.xOf V H := by
  have hbN : b ∈ Subgroup.normalizer (H : Set G) :=
    mem_normalizer_iff_conjSubgroup_eq.mpr hbH
  have hmap : conjSubgroup b (Tim79a.xOf V H) =
      ⨆ U ∈ Tim79a.omegaOf V H, conjSubgroup b U := by
    unfold CGT.Timmesfeld75.conjSubgroup Tim79a.xOf
    simp only [Subgroup.map_iSup]
  rw [hmap]
  have hle : (⨆ U ∈ Tim79a.omegaOf V H, conjSubgroup b U) ≤ Tim79a.xOf V H := by
    refine iSup₂_le fun U hU => ?_
    obtain ⟨h, hh, rfl⟩ := hU
    have hmem : b * h * b⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hbN h).mp hh
    have heq : conjSubgroup b (conjSubgroup h V) =
        conjSubgroup ((b * h * b⁻¹) * y) V := by
      rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      calc conjSubgroup (b * h) V
          = conjSubgroup ((b * h * b⁻¹) * b) V := by
            congr 1
            group
        _ = conjSubgroup (b * h * b⁻¹) (conjSubgroup b V) := by
            rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
        _ = conjSubgroup (b * h * b⁻¹) (conjSubgroup y V) := by rw [hby]
        _ = conjSubgroup ((b * h * b⁻¹) * y) V := by
            rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    rw [heq]
    exact Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf (H := H) (H.mul_mem hmem hy))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [← hmap, card_conjSubgroup]

theorem mem_normalizer_kOf_of_conj_eq {V H : Subgroup G} {b y : G}
    (hbH : conjSubgroup b H = H) (hy : y ∈ H) (hby : conjSubgroup b V = conjSubgroup y V) :
    b ∈ Subgroup.normalizer (kOf V H : Set G) := by
  rw [mem_normalizer_iff_conjSubgroup_eq]
  unfold kOf
  rw [conjSubgroup_inf, ← centralizer_conjSubgroup_eq,
    conjSubgroup_xOf_eq_of_conj_eq hbH hy hby, hbH]

theorem hBarConj_map_imgK {V H : Subgroup G} {b : G}
    (hbH : b ∈ Subgroup.normalizer (H : Set G))
    (hbK : b ∈ Subgroup.normalizer (kOf V H : Set G)) {X : Subgroup G} (hX : X ≤ H) :
    (imgK V H X).map (hBarConj hbH hbK).toMonoidHom = imgK V H (conjSubgroup b X) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hxX, hxeq⟩ := (mem_imgK_iff).mp hz
    rw [← hxeq]
    change hBarConj hbH hbK (piK V H x) ∈ imgK V H (conjSubgroup b X)
    rw [hBarConj_piK]
    refine Subgroup.mem_map.mpr
      ⟨⟨b * (x : G) * b⁻¹, (Subgroup.mem_normalizer_iff.mp hbH (x : G)).mp (hX hxX)⟩, ?_, rfl⟩
    refine mem_conjSubgroup.mpr ?_
    show b⁻¹ * (b * (x : G) * b⁻¹) * b ∈ X
    rw [show b⁻¹ * (b * (x : G) * b⁻¹) * b = (x : G) by group]
    exact hxX
  · intro hy
    obtain ⟨x, hxX, rfl⟩ := (mem_imgK_iff).mp hy
    have hxconj : b⁻¹ * (x : G) * b ∈ X := mem_conjSubgroup.mp hxX
    let w : ↥H := ⟨b⁻¹ * (x : G) * b, hX hxconj⟩
    refine Subgroup.mem_map.mpr ⟨piK V H w, ?_, ?_⟩
    · exact (mem_imgK_iff).mpr ⟨w, hxconj, rfl⟩
    · change hBarConj hbH hbK (piK V H w) = piK V H x
      rw [hBarConj_piK]
      congr 1
      apply Subtype.ext
      show b * (b⁻¹ * (x : G) * b) * b⁻¹ = (x : G)
      group

theorem hBarConj_mul {V H : Subgroup G} {b c : G}
    (hbH : b ∈ Subgroup.normalizer (H : Set G)) (hbK : b ∈ Subgroup.normalizer (kOf V H : Set G))
    (hcH : c ∈ Subgroup.normalizer (H : Set G)) (hcK : c ∈ Subgroup.normalizer (kOf V H : Set G)) :
    hBarConj (V := V) (Subgroup.mul_mem _ hbH hcH) (Subgroup.mul_mem _ hbK hcK) =
      hBarConj hbH hbK * hBarConj hcH hcK := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨z, rfl⟩ := piK_surjective V H y
  rw [hBarConj_piK, MulAut.mul_apply, hBarConj_piK, hBarConj_piK]
  congr 1
  apply Subtype.ext
  show (b * c) * (z : G) * (b * c)⁻¹ = b * (c * (z : G) * c⁻¹) * b⁻¹
  group

theorem hBarConj_one {V H : Subgroup G} :
    hBarConj (V := V) (H := H) (Subgroup.one_mem _) (Subgroup.one_mem _) = 1 := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨z, rfl⟩ := piK_surjective V H y
  change hBarConj (V := V) (H := H) (Subgroup.one_mem _) (Subgroup.one_mem _) (piK V H z) =
    piK V H z
  rw [hBarConj_piK]
  congr 1
  apply Subtype.ext
  show (1 : G) * (z : G) * (1 : G)⁻¹ = (z : G)
  group

theorem hBarConj_of_mem {V H : Subgroup G} {b : G} (hb : b ∈ H) :
    hBarConj (Subgroup.le_normalizer hb) (le_normalizer_kOf V H hb) =
      MulAut.conj (piK V H ⟨b, hb⟩) := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨z, rfl⟩ := piK_surjective V H y
  rw [hBarConj_piK, MulAut.conj_apply]
  rw [← map_mul, ← map_inv, ← map_mul]
  congr 1

private theorem piK_conj_eq_of_commutator_mem_kOf {V H : Subgroup G} {u x : G}
    (huH : u ∈ Subgroup.normalizer (H : Set G))
    (hxH : x ∈ H) (hux : ⁅u, x⁆ ∈ kOf V H) :
    piK V H ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.mp huH x).1 hxH⟩ =
      piK V H ⟨x, hxH⟩ := by
  refine (QuotientGroup.eq_iff_div_mem).mpr ?_
  have hdiv : (⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.mp huH x).1 hxH⟩ /
      ⟨x, hxH⟩ : ↥H) = ⟨⁅u, x⁆, kOf_le V H hux⟩ := by
    apply Subtype.ext
    simp only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk,
      commutatorElement_def]
  rw [hdiv]
  exact Subgroup.mem_subgroupOf.mpr hux

private theorem hBarConj_eq_self_of_mem_imgK_Pc {u : G}
    (huP : ∀ p ∈ Pc M V, ⁅u, p⁆ ∈ kOf V H)
    (huH : u ∈ Subgroup.normalizer (H : Set G))
    (huK : u ∈ Subgroup.normalizer (kOf V H : Set G)) {y : HBar V H}
    (hy : y ∈ imgK V H (Pc M V)) :
    hBarConj huH huK y = y := by
  obtain ⟨z, hz, rfl⟩ := (mem_imgK_iff).mp hy
  rw [hBarConj_piK]
  exact piK_conj_eq_of_commutator_mem_kOf huH z.2 (huP (z : G) hz)

private theorem hBarConj_mem_imgK_conj {u : G}
    (huPc : u ∈ Subgroup.normalizer
      (CGT.Timmesfeld75.conjSubgroup h₀ (Pc M V) : Set G))
    (huH : u ∈ Subgroup.normalizer (H : Set G))
    (huK : u ∈ Subgroup.normalizer (kOf V H : Set G)) {y : HBar V H}
    (hy : y ∈ imgK V H (CGT.Timmesfeld75.conjSubgroup h₀ (Pc M V))) :
    hBarConj huH huK y ∈
      imgK V H (CGT.Timmesfeld75.conjSubgroup h₀ (Pc M V)) := by
  obtain ⟨z, hz, rfl⟩ := (mem_imgK_iff).mp hy
  rw [hBarConj_piK]
  exact (mem_imgK_iff).mpr
    ⟨⟨u * (z : G) * u⁻¹, (Subgroup.mem_normalizer_iff.mp huH (z : G)).1 z.2⟩,
      (Subgroup.mem_normalizer_iff.mp huPc (z : G)).1 hz, rfl⟩

private theorem imgK_conj_image_sq_eq_one_and_card (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) :
    (∀ x ∈ (imgK V H (CGT.Timmesfeld75.conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom,
        x * x = 1) ∧
      Nat.card ((imgK V H (CGT.Timmesfeld75.conjSubgroup h₀ (Pc M V))).map
        ψ.toMonoidHom) = Fintype.card F := by
  obtain ⟨-, -, a, b, -, hA'eq, -⟩ :=
    h.imgK_map_sl2 hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ
  constructor
  · intro x hx
    rw [hA'eq] at hx
    have hx' : b⁻¹ * x * b ∈ utri F := mem_conjSubgroup.mp hx
    have hxeq : x = b * (b⁻¹ * x * b) * b⁻¹ := by group
    obtain ⟨t, ht⟩ := mem_utri_iff.mp hx'
    rw [hxeq, ht]
    rw [show b * utriElt t * b⁻¹ * (b * utriElt t * b⁻¹) =
      b * (utriElt t * utriElt t) * b⁻¹ by group,
      utriElt_mul_self, mul_one, mul_inv_cancel]
  · rw [hA'eq, card_conjSubgroup, card_utri, Nat.card_eq_fintype_card]

private theorem imgK_Pc_image_ne_imgK_conj_image (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) :
    (imgK V H (Pc M V)).map ψ.toMonoidHom ≠
      (imgK V H (CGT.Timmesfeld75.conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom := by
  obtain ⟨-, -, a, b, hAeq, hA'eq, hne⟩ :=
    h.imgK_map_sl2 hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ
  intro heq
  rw [hAeq, hA'eq] at heq
  exact hne heq

private theorem hBarConj_eq_one_of_mem_normalizer (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {u : G} (huP : ∀ p ∈ Pc M V, ⁅u, p⁆ ∈ kOf V H)
    (huPc : u ∈ Subgroup.normalizer
      (CGT.Timmesfeld75.conjSubgroup h₀ (Pc M V) : Set G))
    (huH : u ∈ Subgroup.normalizer (H : Set G))
    (huK : u ∈ Subgroup.normalizer (kOf V H : Set G)) :
    hBarConj huH huK = 1 := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  let θ : MulAut (HBar V H) := hBarConj huH huK
  let Θ : MulAut (SL(2, F)) := ψ.symm.trans (θ.trans ψ)
  have hΘ_apply : ∀ x : HBar V H, Θ (ψ x) = ψ (θ x) := by
    intro x
    simp [Θ]
  obtain ⟨hA2, hAcard, a, b, hAeq, hA'eq, hne⟩ :=
    h.imgK_map_sl2 hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ
  let A : Subgroup (SL(2, F)) := (imgK V H (Pc M V)).map ψ.toMonoidHom
  let A' : Subgroup (SL(2, F)) :=
    (imgK V H (CGT.Timmesfeld75.conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom
  have hfixA : ∀ x ∈ A, Θ x = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    change Θ (ψ y) = ψ y
    rw [hΘ_apply, hBarConj_eq_self_of_mem_imgK_Pc huP huH huK hy]
  have hleA' : A'.map Θ.toMonoidHom ≤ A' := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    change Θ (ψ z) ∈ A'
    rw [hΘ_apply]
    exact Subgroup.mem_map.mpr
      ⟨hBarConj huH huK z, hBarConj_mem_imgK_conj huPc huH huK hz, rfl⟩
  have hcardA' : Nat.card (A'.map Θ.toMonoidHom) = Nat.card A' :=
    Subgroup.card_map_of_injective Θ.injective
  have hnormA' : A'.map Θ.toMonoidHom = A' :=
    Subgroup.eq_of_le_of_card_ge hleA' (by rw [hcardA'])
  have hA'2 : ∀ x ∈ A', x * x = 1 :=
    (imgK_conj_image_sq_eq_one_and_card h hS ψ).1
  have hA'card : Nat.card A' = Fintype.card F :=
    (imgK_conj_image_sq_eq_one_and_card h hS ψ).2
  have hne' : A ≠ A' := imgK_Pc_image_ne_imgK_conj_image h hS ψ
  have hΘ : Θ = 1 :=
    CFSG.RankThree.GF2n.Tim81.Sec2.MulAut.eq_one_of_fix_sylow
      hA2 hAcard hA'2 hA'card hne' hfixA hnormA'
  have hθ : θ = 1 := by
    ext x
    have h := congrArg (fun φ : MulAut (SL(2, F)) => φ (ψ x)) hΘ
    have h2 : ψ (θ x) = ψ x := by
      rw [← hΘ_apply x]
      exact h
    exact ψ.injective h2
  exact hθ

private theorem hBarConj_eq_one_of_fix_Pc (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {u : G} (huM : u ∈ M)
    (huP : ∀ p ∈ Pc M V, ⁅u, p⁆ ∈ kOf V H)
    (huPc : u ∈ Subgroup.normalizer
      (CGT.Timmesfeld75.conjSubgroup h₀ (Pc M V) : Set G)) :
    ∃ (huH : u ∈ Subgroup.normalizer (H : Set G))
      (huK : u ∈ Subgroup.normalizer (kOf V H : Set G)),
      hBarConj huH huK = 1 := by
  classical
  have huP' : u ∈ Subgroup.normalizer (Pc M V : Set G) := h.toHyp.le_normalizer_Pc huM
  have huH : u ∈ Subgroup.normalizer (H : Set G) := by
    rw [hS.hH]
    exact Subgroup.inf_normalizer_le_normalizer_sup (Pc M V)
      (CGT.Timmesfeld75.conjSubgroup h₀ (Pc M V)) ⟨huP', huPc⟩
  have huV : u ∈ Subgroup.normalizer (V : Set G) := h.toHyp.le_normalizer huM
  have huK : u ∈ Subgroup.normalizer (kOf V H : Set G) :=
    mem_normalizer_kOf_of_conj_eq (mem_normalizer_iff_conjSubgroup_eq.mp huH) H.one_mem
      (by rw [conjSubgroup_one]; exact conjSubgroup_eq_self_iff.mpr huV)
  exact ⟨huH, huK, hBarConj_eq_one_of_mem_normalizer h hS huP huPc huH huK⟩

theorem Sec45Shape.commutator_mem_kOf_of_fix_Pc (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {u : G} (huM : u ∈ M)
    (huP : ∀ p ∈ Pc M V, ⁅u, p⁆ ∈ kOf V H)
    (huPc : u ∈ Subgroup.normalizer
      (CGT.Timmesfeld75.conjSubgroup h₀ (Pc M V) : Set G)) :
    ∀ x ∈ H, ⁅u, x⁆ ∈ kOf V H := by
  obtain ⟨huH, huK, hθ⟩ := hBarConj_eq_one_of_fix_Pc h hS huM huP huPc
  exact (hBarConj_eq_one_iff huH huK).mp hθ

theorem Sec45Shape.mem_centralizer_xOf_of_fix_Pc (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {u : G} (huM : u ∈ M)
    (huP : ∀ p ∈ Pc M V, ⁅u, p⁆ ∈ kOf V H)
    (huPc : u ∈ Subgroup.normalizer
      (CGT.Timmesfeld75.conjSubgroup h₀ (Pc M V) : Set G))
    {k : ℕ} (hu2 : u ^ 2 ^ k = 1) :
    u ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) := by
  have hbK : ∀ x ∈ H, ⁅u, x⁆ ∈ kOf V H :=
    Sec45Shape.commutator_mem_kOf_of_fix_Pc h hS huM huP huPc
  exact Sec45Shape.mem_centralizer_xOf_of_commutator_mem_kOf h hS hbK hu2

end CFSG.RankThree.GF2n.Tim81
