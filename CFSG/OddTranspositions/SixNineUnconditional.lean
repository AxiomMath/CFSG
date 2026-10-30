module

public import CFSG.OddTranspositions.SixNine
public import CFSG.OddTranspositions.BlockGraph
public import CFSG.OddTranspositions.BlockUnion
public import CFSG.OddTranspositions.BlockGraph

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem mem_cenOrbit_iff {hC : HypothesisC D} {a b : G} :
    b ∈ cenOrbit hC a ↔ ∃ x ∈ cenGen hC, b = x * a * x⁻¹ := Iff.rfl

theorem mem_GammaComp_of_commute {hC : HypothesisC D} {a b c : G} (ha : a ∈ Gamma hC)
    (hb : b ∈ GammaComp hC a) (hc : c ∈ Gamma hC) (hbc : Commute b c) :
    c ∈ GammaComp hC a :=
  Relation.ReflTransGen.tail hb ⟨GammaComp_mem_Gamma ha hb, hc, hbc⟩

theorem GammaComp_subset_of_closed {hC : HypothesisC D} {x : G} {S : Set G} (hx : x ∈ S)
    (hS : ∀ z ∈ S, ∀ w ∈ Gamma hC, z ∈ Gamma hC → Commute z w → w ∈ S) :
    GammaComp hC x ⊆ S := by
  intro y hy
  change Relation.ReflTransGen (GammaComm hC) x y at hy
  induction hy with
  | refl => exact hx
  | @tail z w _ hzw ih => exact hS z ih w hzw.2.1 hzw.1 hzw.2.2

end CFSG.OddTranspositions

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] {D : Set G}

theorem mem_normalizer_of_mem_block {α : Set G} (hα : IsBlock D α) {x : G} (hx : x ∈ α) :
    x ∈ Subgroup.normalizer α := by
  by_contra h
  have hdis := hα.2.2.2 x h
  exact Set.disjoint_left.mp hdis hx ⟨x, hx, by group⟩

theorem mem_block_of_normalizes_of_not_commute (hD : IsOddTransp D) {β : Set G}
    (hβ : IsBlock D β) {x y : G} (hx : x ∈ β) (hy : y ∈ D)
    (hyβ : y ∈ Subgroup.normalizer β) (hxy : ¬ Commute x y) : y ∈ β := by
  obtain ⟨h, hh, hhx⟩ := hD.exists_conj (hβ.subset hx) hy hxy
  have hcl : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.normalizer β := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact mem_normalizer_of_mem_block hβ hx
    · exact hyβ
  have himg := Subgroup.mem_normalizer_iff_conj_image_eq.mp (hcl hh)
  rw [← hhx, ← himg]
  exact ⟨x, hx, rfl⟩

end CFSG.OddTranspositions


namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddLocal
open CFSG.Timmesfeld.Connectivity
open scoped Pointwise

variable {G : Type} [Group G] {D : Set G}

abbrev cimg (g : G) (S : Set G) : Set G := (fun x => g * x * g⁻¹) '' S

theorem mem_cimg {g x : G} {S : Set G} : x ∈ cimg g S ↔ g⁻¹ * x * g ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by group⟩

theorem conj_mem_D_iff (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (g x : G) :
    g * x * g⁻¹ ∈ D ↔ x ∈ D :=
  ⟨fun h => by simpa [mul_assoc] using hN g⁻¹ _ h, hN g x⟩

theorem inv_conj_mem_D_iff (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (g x : G) :
    g⁻¹ * x * g ∈ D ↔ x ∈ D := by
  simpa using conj_mem_D_iff hN g⁻¹ x

theorem commSet_conj (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (g d : G) :
    commSet D (g * d * g⁻¹) = cimg g (commSet D d) := by
  ext x
  rw [mem_cimg]
  have h1 : Commute x (g * d * g⁻¹) ↔ Commute (g⁻¹ * x * g) d := by
    rw [← Commute.conj_iff g⁻¹]; simp [mul_assoc]
  have h2 : x ≠ g * d * g⁻¹ ↔ g⁻¹ * x * g ≠ d := by
    constructor
    · intro h h'; apply h; rw [← h']; group
    · intro h h'; apply h; rw [h']; group
  simp only [commSet, Set.mem_setOf_eq]
  rw [inv_conj_mem_D_iff hN, h1, h2]

theorem closure_cimg (g : G) (S : Set G) :
    Subgroup.closure (cimg g S) = (Subgroup.closure S).map (MulAut.conj g).toMonoidHom := by
  rw [MonoidHom.map_closure]
  rfl

theorem orbitIn_conj (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (g d e : G) :
    orbitIn D (g * d * g⁻¹) (g * e * g⁻¹) = cimg g (orbitIn D d e) := by
  ext x
  simp only [orbitIn, Set.mem_setOf_eq, mem_cimg, commSet_conj hN, closure_cimg]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hh
    exact ⟨k, hk, by simp [MulAut.conj_apply]; group⟩
  · rintro ⟨k, hk, hx⟩
    refine ⟨g * k * g⁻¹, Subgroup.mem_map.mpr ⟨k, hk, by simp [MulAut.conj_apply]⟩, ?_⟩
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * k * g⁻¹ * (g * e * g⁻¹) * (g * k * g⁻¹)⁻¹ := by rw [hx]; group

theorem ncard_cimg (g : G) (S : Set G) : (cimg g S).ncard = S.ncard :=
  Set.ncard_image_of_injective _ (fun x y h => by simpa using h)

theorem IsMaxOrbit.conj (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) {d : G} {E : Set G}
    (hE : IsMaxOrbit D d E) (g : G) : IsMaxOrbit D (g * d * g⁻¹) (cimg g E) := by
  obtain ⟨e, he, rfl, hmax⟩ := hE
  refine ⟨g * e * g⁻¹, ?_, (orbitIn_conj hN g d e).symm, ?_⟩
  · rw [commSet_conj hN]; exact ⟨e, he, rfl⟩
  · intro e' he'
    rw [commSet_conj hN, mem_cimg] at he'
    have := hmax _ he'
    have heq : e' = g * (g⁻¹ * e' * g) * g⁻¹ := by group
    rw [heq, orbitIn_conj hN, ncard_cimg, ncard_cimg]
    exact this

theorem normalizer_cimg {g x : G} {S : Set G} :
    x ∈ Subgroup.normalizer (cimg g S) ↔ g⁻¹ * x * g ∈ Subgroup.normalizer S := by
  rw [Subgroup.mem_set_normalizer_iff, Subgroup.mem_set_normalizer_iff]
  constructor
  · intro h y
    have := h (g * y * g⁻¹)
    rw [mem_cimg, mem_cimg] at this
    simpa [mul_assoc] using this
  · intro h y
    have := h (g⁻¹ * y * g)
    rw [mem_cimg, mem_cimg]
    simpa [mul_assoc] using this

theorem normSet_diff_conj (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (g : G) (E : Set G) :
    normSet D (cimg g E) \ cimg g E = cimg g (normSet D E \ E) := by
  ext x
  simp only [Set.mem_diff, normSet, Set.mem_setOf_eq]
  rw [mem_cimg, mem_cimg, normalizer_cimg]
  simp only [Set.mem_diff, Set.mem_setOf_eq, inv_conj_mem_D_iff hN]

@[expose] def HypothesisC.conj (hC : HypothesisC D) (g : G) : HypothesisC D where
  setup := hC.setup
  conn := hC.conn
  d := g * hC.d * g⁻¹
  hd := hC.setup.normal g _ hC.hd
  E := cimg g hC.E
  hE := IsMaxOrbit.conj hC.setup.normal hC.hE g

theorem HypothesisC.conj_d (hC : HypothesisC D) (g : G) : (hC.conj g).d = g * hC.d * g⁻¹ := rfl

theorem HypothesisC.conj_alpha (hC : HypothesisC D) (g : G) :
    (hC.conj g).alpha = cimg g hC.alpha :=
  normSet_diff_conj hC.setup.normal g hC.E

end CFSG.OddTranspositions


namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddLocal
open CFSG.Timmesfeld.Connectivity
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commute_conj_iff (g x d : G) :
    Commute x (g * d * g⁻¹) ↔ Commute (g⁻¹ * x * g) d := by
  rw [← Commute.conj_iff g⁻¹]; simp [mul_assoc]

theorem mem_Gamma_conj_iff (hC : HypothesisC D) (g x : G) :
    x ∈ Gamma (hC.conj g) ↔ g⁻¹ * x * g ∈ Gamma hC := by
  rw [mem_Gamma_iff, mem_Gamma_iff, HypothesisC.conj_d, HypothesisC.conj_alpha, mem_cimg,
    inv_conj_mem_D_iff hC.setup.normal, commute_conj_iff]

theorem cenGen_conj (hC : HypothesisC D) (g : G) :
    cenGen (hC.conj g) = (cenGen hC).map (MulAut.conj g).toMonoidHom := by
  rw [cenGen, cenGen, ← closure_cimg]
  congr 1
  ext x
  rw [mem_cimg]
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff,
    HypothesisC.conj_d, inv_conj_mem_D_iff hC.setup.normal]
  have := commute_conj_iff g x hC.d
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, this.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, this.mpr h2⟩

theorem cenOrbit_conj (hC : HypothesisC D) (g a : G) :
    cenOrbit (hC.conj g) (g * a * g⁻¹) = cimg g (cenOrbit hC a) := by
  ext x
  rw [mem_cimg]
  simp only [mem_cenOrbit_iff, cenGen_conj]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨k, hk, by simp [MulAut.conj_apply]; group⟩
  · rintro ⟨k, hk, hx⟩
    refine ⟨g * k * g⁻¹, Subgroup.mem_map.mpr ⟨k, hk, by simp [MulAut.conj_apply]⟩, ?_⟩
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * k * g⁻¹ * (g * a * g⁻¹) * (g * k * g⁻¹)⁻¹ := by rw [hx]; group

theorem GammaComp_subset_Gamma_conj (hC : HypothesisC D) {a c g : G} (ha : a ∈ Gamma hC)
    (hc : c ∈ Gamma hC) (hcB : c ∉ GammaComp hC a)
    (hAB : cenOrbit hC a = GammaComp hC a) (hg : g * hC.d * g⁻¹ = c) :
    GammaComp hC a ⊆ Gamma (hC.conj g) := by
  set B := GammaComp hC a with hBdef
  set αc := (hC.conj g).alpha with hαcdef
  have hαc : IsBlock D αc := (hC.conj g).isBlock_alpha
  have hcαc : c ∈ αc := hg ▸ (hC.conj g).d_mem_alpha
  have hnc : ∀ x ∈ B, ¬ Commute x c := by
    intro x hx hxc
    exact hcB (mem_GammaComp_of_commute ha hx hc hxc)
  have hstay : ∀ x ∈ αc, ∀ y ∈ D, ¬ Commute y c → Commute x y → y ∈ αc := by
    intro x hx y hy hyc hxy
    by_contra hyα
    obtain ⟨β, hβ, hyβ⟩ := exists_mem_blockClass_of_mem hC.setup.isClass hαc hy
    obtain ⟨g', rfl⟩ := mem_blockClass_iff'.mp hβ
    have hne : g' • αc ≠ αc := fun h => hyα (by rw [h] at hyβ; exact hyβ)
    exact hyc (commute_block_of_mem hC.setup.normal hC.setup.oddT hαc hne hx hyβ hxy
      c hcαc y hyβ).symm
  have hall : ∀ x ∈ B, x ∈ αc → B ⊆ αc := by
    intro x hx hxα
    have hBx : GammaComp hC x = B := GammaComp_eq_of_mem hx
    have hsub : GammaComp hC x ⊆ αc ∩ B := by
      refine GammaComp_subset_of_closed ⟨hxα, hx⟩ ?_
      rintro z ⟨hzα, hzB⟩ w hw _ hzw
      have hwB : w ∈ B := mem_GammaComp_of_commute ha hzB hw hzw
      exact ⟨hstay z hzα w (Gamma_subset_D hw) (hnc w hwB) hzw, hwB⟩
    intro y hy
    rw [← hBx] at hy
    exact (hsub hy).1
  have hdisj : ∀ x ∈ B, x ∉ αc := by
    intro x hx hxα
    have hBα := hall x hx hxα
    have haα : a ∈ αc := hBα (GammaComp_self_mem a)
    have hda : hC.d * a * hC.d⁻¹ ∈ αc :=
      hBα (by show _ ∈ B; rw [← hAB]; exact mem_cenOrbit_iff.mpr ⟨hC.d, d_mem_cenGen hC, rfl⟩)
    have hdN : hC.d ∈ Subgroup.normalizer αc := by
      by_contra h
      exact Set.disjoint_left.mp (hαc.disjoint_conj h) hda ⟨a, haα, rfl⟩
    have hdα : hC.d ∈ αc := mem_block_of_normalizes_of_not_commute hC.setup.oddT hαc haα
      hC.hd hdN (fun h => not_commute_d_of_mem_Gamma ha h)
    rw [hαcdef, HypothesisC.conj_alpha] at hdα hcαc
    have hgN : g ∈ Subgroup.normalizer hC.alpha := by
      by_contra h
      exact Set.disjoint_left.mp (hC.isBlock_alpha.disjoint_conj h) hC.d_mem_alpha hdα
    have himg := Subgroup.mem_normalizer_iff_conj_image_eq.mp hgN
    have hcα : c ∈ hC.alpha := by
      rw [← himg]; exact hcαc
    exact not_mem_alpha_of_mem_Gamma hc hcα
  intro x hx
  rw [mem_Gamma_iff]
  refine ⟨Gamma_subset_D (GammaComp_mem_Gamma ha hx), ?_, hdisj x hx⟩
  rw [HypothesisC.conj_d, hg]
  exact hnc x hx

end CFSG.OddTranspositions

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddLocal

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem key3_of_containment (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    {a c : G} (hCc : HypothesisC D) (hCc_d : hCc.d = c)
    (ha : a ∈ Gamma hC) (hc : c ∈ Gamma hC)
    {A : Set G} (hA : A = GammaComp hC a) (hcA : c ∉ A)
    (hmaxc : (cenOrbit hCc a).ncard ≤ (GammaComp hC a).ncard)
    (hBΓc : GammaComp hC a ⊆ Gamma hCc) :
    ∀ d ∈ D, Commute d c → (fun x => d * x * d⁻¹) '' GammaComp hC a = GammaComp hC a := by
  classical
  set B : Set G := GammaComp hC a with hB
  set Ac : Set G := cenOrbit hCc a with hAc
  set Bc : Set G := GammaComp hCc a with hBc
  have haΓc : a ∈ Gamma hCc := hBΓc (by rw [hB]; exact GammaComp_self_mem a)
  have hBsub : B ⊆ Bc := by
    intro b hb
    rw [hB] at hb
    change Relation.ReflTransGen (GammaComm hC) a b at hb
    rw [hBc]
    change Relation.ReflTransGen (GammaComm hCc) a b
    induction hb with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y hpath hxy ih =>
      have hx : x ∈ B := hpath
      have hy : y ∈ B := hpath.tail hxy
      exact ih.tail ⟨hBΓc hx, hBΓc hy, hxy.2.2⟩
  have hBcSub : Bc ⊆ Ac := by
    rw [hBc, hAc]
    exact GammaComp_subset_cenOrbit hCc hsecond haΓc
  have hBBc : B = Bc := by
    apply Set.eq_of_subset_of_ncard_le hBsub
    exact le_trans (Set.ncard_le_ncard hBcSub) hmaxc
  have hBcAc : Bc = Ac := by
    apply Set.eq_of_subset_of_ncard_le hBcSub
    rwa [hBBc] at hmaxc
  have hBAc : B = Ac := hBBc.trans hBcAc
  intro d hdD hdc
  have hdX : d ∈ cenGen hCc := by
    refine Subgroup.subset_closure ⟨hdD, ?_⟩
    rw [hCc_d]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hdc.eq
  have hdXinv : d⁻¹ ∈ cenGen hCc := Subgroup.inv_mem _ hdX
  apply Set.Subset.antisymm
  · rintro y ⟨b, hb, rfl⟩
    have hbAc : b ∈ Ac := by rwa [hBAc] at hb
    rw [hBAc]
    exact cenOrbit_invariant (hC := hCc) (a := a) (x := d) hdX b hbAc
  · intro y hy
    have hyAc : y ∈ Ac := by rwa [hBAc] at hy
    have hy' : d⁻¹ * y * d ∈ B := by
      rw [hBAc]
      simpa only [inv_inv] using
        cenOrbit_invariant (hC := hCc) (a := a) (x := d⁻¹) hdXinv y hyAc
    exact ⟨d⁻¹ * y * d, hy', by group⟩


theorem hstep3 (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
 :
    ∀ (A : Set G) (a : G),
      (∃ a₀ ∈ Gamma hC, A = cenOrbit hC a₀) → a ∈ A →
      (∀ B : Set G, (∃ b₀ ∈ Gamma hC, B = cenOrbit hC b₀) → B.ncard ≤ A.ncard) →
      A ≠ Gamma hC → GammaComp hC a ≠ A := by
  rintro A a ⟨a₀, ha₀, hA⟩ haA hmax hne hBA
  have haA' : a ∈ cenOrbit hC a₀ := by
    rwa [hA] at haA
  have hAeq : A = cenOrbit hC a := by
    rw [hA]
    exact (cenOrbit_eq_of_mem hC haA').symm
  have haΓ : a ∈ Gamma hC := cenOrbit_subset_Gamma hC ha₀ haA' 
  set B : Set G := GammaComp hC a with hBdef
  have hBΓ : B ⊆ Gamma hC := by
    intro b hb
    exact GammaComp_mem_Gamma haΓ hb
  have hBne : B.Nonempty := ⟨a, by rw [hBdef]; exact GammaComp_self_mem a⟩
  have hBne_top : B ≠ Gamma hC := by
    intro h
    exact hne ((hBdef.trans hBA).symm.trans h)
  have hc_exists : ∃ c ∈ Gamma hC, c ∉ B := by
    by_contra h
    push Not at h
    exact hBne_top (Set.Subset.antisymm hBΓ h)
  obtain ⟨c, hcΓ, hcB⟩ := hc_exists
  have hc_not_comp : c ∉ GammaComp hC a := by
    rwa [← hBdef]
  have hcD : c ∈ D := Gamma_subset_D hcΓ
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_isClass hC.setup.isClass hC.hd hcD)
  have hAcen : cenOrbit hC a = GammaComp hC a := hAeq.symm.trans hBA.symm
  have hBΓc : GammaComp hC a ⊆ Gamma (hC.conj g) :=
    GammaComp_subset_Gamma_conj hC haΓ hcΓ hc_not_comp hAcen hg
  have hmaxc : (cenOrbit (hC.conj g) a).ncard ≤ (GammaComp hC a).ncard := by
    have haΓc : a ∈ Gamma (hC.conj g) := hBΓc (GammaComp_self_mem a)
    have ha' : g⁻¹ * a * g ∈ Gamma hC := (mem_Gamma_conj_iff hC g a).mp haΓc
    have hco : cenOrbit (hC.conj g) a = cimg g (cenOrbit hC (g⁻¹ * a * g)) := by
      rw [← cenOrbit_conj]; congr 1; group
    rw [hco, ncard_cimg, ← hBdef, hBA]
    exact hmax _ ⟨_, ha', rfl⟩
  have hkey3 : ∀ d ∈ D, Commute d c →
      (fun x => d * x * d⁻¹) '' GammaComp hC a = GammaComp hC a :=
    key3_of_containment hC hsecond (hC.conj g) (by rw [HypothesisC.conj_d, hg]) haΓ hcΓ rfl
      hc_not_comp hmaxc hBΓc
  have hXB : cenGen hC ≤ Subgroup.normalizer B := by
    rw [cenGen, Subgroup.closure_le]
    intro x hx
    have hxS : x ∈ cenGen hC := Subgroup.subset_closure hx
    have hxaA : x * a * x⁻¹ ∈ A := by
      rw [hAeq]
      exact ⟨x, hxS, rfl⟩
    have hAcomp : A = GammaComp hC a := hBA.symm.trans hBdef
    have hxaB : x * a * x⁻¹ ∈ B := by
      rw [hBdef]
      rwa [hAcomp] at hxaA
    apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
    rw [show (⇑(MulAut.conj x) : G → G) = (fun y => x * y * x⁻¹) by
      funext y; rw [MulAut.conj_apply]]
    rw [hBdef, GammaComp_conj hC hxS a]
    exact GammaComp_eq_of_mem hxaB
  let Cu : Set G := (D : Set G) ∩ (Subgroup.centralizer ({hC.d} : Set G) : Set G)
  let Cc : Set G := (D : Set G) ∩ (Subgroup.centralizer ({c} : Set G) : Set G)
  let Y : Subgroup G := Subgroup.closure (Cu ∪ Cc)
  have hY_N : Y ≤ Subgroup.normalizer B := by
    rw [show Y = Subgroup.closure (Cu ∪ Cc) from rfl, Subgroup.closure_le]
    intro z hz
    rcases hz with hz | hz
    · exact hXB (Subgroup.subset_closure hz)
    · apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
      rw [show (⇑(MulAut.conj z) : G → G) = (fun y => z * y * z⁻¹) by
        funext y; rw [MulAut.conj_apply]]
      exact hkey3 z hz.1 (Subgroup.mem_centralizer_singleton_iff.mp hz.2)
  have hdY : hC.d ∈ Y := by
    refine Subgroup.subset_closure (Or.inl ⟨hC.hd, ?_⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hEY : hC.E ⊆ (Y : Set G) :=
    (DalphaStar_subset_cenGen hC).trans (Subgroup.closure_mono Set.subset_union_left)
  have hcY : c ∈ Y := by
    refine Subgroup.subset_closure (Or.inr ⟨hcD, ?_⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hY_D : Y = Subgroup.closure ((Y : Set G) ∩ D) := by
    apply le_antisymm
    · rw [show Y = Subgroup.closure (Cu ∪ Cc) from rfl, Subgroup.closure_le]
      intro z hz
      have hzD : z ∈ D := by
        rcases hz with hz | hz <;> exact hz.1
      exact Subgroup.subset_closure ⟨Subgroup.subset_closure hz, hzD⟩
    · rw [Subgroup.closure_le]
      exact Set.inter_subset_left
  have hYtop : Y = ⊤ := eq_top_of_mem_Gamma hC hY_D hdY hEY hcΓ hcY
  have hNtop : Subgroup.normalizer B = ⊤ :=
    top_le_iff.mp (hYtop ▸ hY_N)
  exact normalizer_comp_ne_top hC hBΓ hBne hNtop


end CFSG.OddTranspositions


namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddLocal
open CFSG.Timmesfeld.Connectivity
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_mem_Dalpha (hC : HypothesisC D) : ∃ δ, δ ∈ Dalpha D hC.alpha := by
  obtain ⟨e, -, hEe, -⟩ := hC.hE
  have heE : e ∈ hC.E := hEe ▸ self_mem_orbitIn (D := D) hC.d e
  rw [← hC.DalphaStar_alpha] at heE
  obtain ⟨β, hβ, -⟩ := heE
  exact ⟨β, hβ⟩

theorem blockClass_nonempty {α β : Set G} (hα : α.Nonempty) (hβ : β ∈ blockClass α) :
    β.Nonempty := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hβ
  obtain ⟨x, hx⟩ := hα
  exact ⟨g * x * g⁻¹, x, hx, rfl⟩

theorem Walpha_alpha_eq_singleton (hC : HypothesisC D) :
    Walpha D hC.alpha = {hC.alpha} := by
  obtain ⟨δ, hδ⟩ := exists_mem_Dalpha hC
  apply Walpha_eq_singleton_of_isMaxBlock_of_ne hC.setup.normal hC.isMaxBlock_alpha
  intro hW
  have hδW : δ ∈ Walpha D hC.alpha := by rw [hW]; exact hδ.1
  have hαδ : hC.alpha ∈ Dalpha D δ :=
    ⟨mem_blockClass_of_mem_blockClass hδ.1 (mem_blockClass_self _), hC.isBlock_alpha.subset,
      (Dalpha.ne_self hδ).symm, fun x hx y hy => (hδ.2.2.2 y hy x hx).symm⟩
  rw [hδW.2] at hαδ
  exact Dalpha.ne_self hαδ rfl

theorem ncard_Dalpha_conj (hN : IsNormalSet D) (g : G) (β : Set G) :
    (Dalpha D ((fun x => g * x * g⁻¹) '' β)).ncard = (Dalpha D β).ncard := by
  rw [← Dalpha_conj_image hN g]
  refine Set.ncard_image_of_injective _ ?_
  intro γ γ' h
  have := congrArg (fun S => (fun x => g⁻¹ * x * g) '' S) h
  simpa [Set.image_image, mul_assoc] using this

theorem ncard_perp_conj (hN : IsNormalSet D) (g : G) (β : Set G) :
    (perp D ((fun x => g * x * g⁻¹) '' β)).ncard = (perp D β).ncard := by
  rw [← perp_conj_image hN g]
  refine Set.ncard_image_of_injective _ ?_
  intro γ γ' h
  have := congrArg (fun S => (fun x => g⁻¹ * x * g) '' S) h
  simpa [Set.image_image, mul_assoc] using this

theorem exists_DalphaStar_not_commute (hC : HypothesisC D) {a : G} (ha : a ∈ Gamma hC) :
    ∃ d ∈ DalphaStar D hC.alpha, ¬ Commute d a := by
  classical
  by_contra h
  push Not at h
  obtain ⟨β, hβc, haβ⟩ :=
    exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha (Gamma_subset_D ha)
  have hβα : β ≠ hC.alpha := fun e => not_mem_alpha_of_mem_Gamma ha (e ▸ haβ)
  obtain ⟨g, hg⟩ := mem_blockClass_iff'.mp hβc
  have hβb : IsBlock D β := hg ▸ hC.isBlock_alpha.conj hC.setup.normal g
  have hsub : Dalpha D hC.alpha ⊆ Dalpha D β := by
    intro δ hδ
    have hδβ : δ ∈ blockClass β := mem_blockClass_of_mem_blockClass hβc hδ.1
    have hne : δ ≠ β := by
      rintro rfl
      exact not_commute_d_of_mem_Gamma ha
        (hC.DalphaStar_subset_commute ⟨_, hδ, haβ⟩).2
    obtain ⟨y, hy⟩ := blockClass_nonempty hC.isBlock_alpha.nonempty hδ.1
    obtain ⟨k, hk⟩ := mem_blockClass_iff'.mp hδβ
    have hkne : k • β ≠ β := hk ▸ hne
    have hall := commute_block_of_mem hC.setup.normal hC.setup.oddT hβb hkne haβ (hk ▸ hy)
      (h y ⟨δ, hδ, hy⟩).symm
    refine ⟨hδβ, hδ.2.1, hne, fun x hx z hz => hall x hx z (hk ▸ hz)⟩
  have hcard : (Dalpha D β).ncard = (Dalpha D hC.alpha).ncard := by
    obtain ⟨g', hg'⟩ := mem_blockClass_iff.mp hβc
    rw [hg']; exact ncard_Dalpha_conj hC.setup.normal g' _
  have heq : Dalpha D hC.alpha = Dalpha D β :=
    Set.eq_of_subset_of_ncard_le hsub hcard.le (Set.toFinite _)
  have hβW : β ∈ Walpha D hC.alpha := ⟨hβc, heq.symm⟩
  rw [Walpha_alpha_eq_singleton hC] at hβW
  exact hβα hβW

end CFSG.OddTranspositions


namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddLocal
open CFSG.Timmesfeld.Connectivity
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem cenGen_le_normalizer_cenOrbit (hC : HypothesisC D) (b : G) :
    cenGen hC ≤ Subgroup.normalizer (cenOrbit hC b) := by
  intro x hx
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · exact cenOrbit_invariant hC hx h
  · intro hh
    have := cenOrbit_invariant hC (Subgroup.inv_mem _ hx) _ hh
    simpa [mul_assoc] using this

theorem mem_blockClass_trans {α β γ : Set G} (hβ : β ∈ blockClass α) (hγ : γ ∈ blockClass β) :
    γ ∈ blockClass α :=
  mem_blockClass_of_mem_blockClass (mem_blockClass_of_mem_blockClass hβ (mem_blockClass_self α))
    hγ

theorem hstep4 (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4) :
    ∀ (A : Set G) (a : G),
      (∃ a₀ ∈ Gamma hC, A = cenOrbit hC a₀) → a ∈ A →
      (∀ B : Set G, (∃ b₀ ∈ Gamma hC, B = cenOrbit hC b₀) → B.ncard ≤ A.ncard) →
      A ≠ Gamma hC →
      Disjoint (GammaComp hC a) ((fun y => hC.d * y * hC.d) '' GammaComp hC a) →
      (cenOrbit hC a).ncard = 2 * (GammaComp hC a).ncard → False := by
  classical
  rintro A a ⟨a₀, ha₀, hA⟩ haA hmax _hne hdis _hcard
  have haA' : a ∈ cenOrbit hC a₀ := hA ▸ haA
  have hAeq : A = cenOrbit hC a := by rw [hA]; exact (cenOrbit_eq_of_mem hC haA').symm
  have haΓ : a ∈ Gamma hC := cenOrbit_subset_Gamma hC ha₀ haA'
  set B := GammaComp hC a with hB
  set Bu := (fun y => hC.d * y * hC.d) '' B with hBu
  have hAB : A = B ∪ Bu := by rw [hAeq]; exact cenOrbit_eq_comp_union_conj hC hsecond haΓ
  have hAΓ : A ⊆ Gamma hC := by rw [hAeq]; exact cenOrbit_subset_Gamma hC haΓ
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hui : hC.d⁻¹ = hC.d := hC.setup.oddT.inv_eq hC.hd
  obtain ⟨d, ⟨δ, hδ, hdδ⟩, hda⟩ := exists_DalphaStar_not_commute hC haΓ
  have hdD : d ∈ D := hδ.2.1 hdδ
  have hdu : Commute d hC.d := (hC.DalphaStar_subset_commute ⟨δ, hδ, hdδ⟩).2
  have hd2 : d * d = 1 := hC.setup.oddT.mul_self_eq_one hdD
  have hdi : d⁻¹ = d := hC.setup.oddT.inv_eq hdD
  have hdne : d ≠ hC.d := by
    intro h
    rw [h] at hdδ
    exact Dalpha.ne_self hδ (eq_of_mem_of_mem_blockClass hC.isBlock_alpha hδ.1
      (mem_blockClass_self _) ⟨_, hdδ, hC.d_mem_alpha⟩)
  have hudX : hC.d * d ∈ cenGen hC :=
    Subgroup.mul_mem _ (d_mem_cenGen hC)
      (Subgroup.subset_closure ⟨hdD, Subgroup.mem_centralizer_singleton_iff.mpr hdu.eq⟩)
  have hsk := secondKind_middle_conj_commute hC hsecond haΓ hdD hdu hdne hda
  obtain ⟨hQ, hQa, -⟩ := hsk
  have hcomm : Commute ((hC.d * d) * a * (hC.d * d)⁻¹) a := hQa _ hQ
  have hmemΓ : (hC.d * d) * a * (hC.d * d)⁻¹ ∈ Gamma hC := cenGen_maps_Gamma hC hudX haΓ
  have hmemB : (hC.d * d) * a * (hC.d * d)⁻¹ ∈ B :=
    mem_GammaComp_of_commute haΓ (GammaComp_self_mem a) hmemΓ hcomm.symm
  have hBud : (fun y => (hC.d * d) * y * (hC.d * d)⁻¹) '' B = B := by
    rw [hB, GammaComp_conj hC hudX a]; exact GammaComp_eq_of_mem hmemB
  have hBd : (fun y => d * y * d⁻¹) '' B = Bu := by
    conv_lhs => rw [← hBud]
    rw [Set.image_image, hBu]
    congr 1
    funext y
    rw [mul_inv_rev, hdi, hui]
    calc d * (hC.d * d * y * (d * hC.d)) * d = (d * hC.d * d) * y * (d * hC.d * d) := by group
      _ = hC.d * y * hC.d := by rw [hdu.eq, mul_assoc hC.d d d, hd2, mul_one]
  have hBud' : (fun y => d * y * d⁻¹) '' Bu = B := by
    rw [← hBd, Set.image_image, hdi]
    have : (fun y => d * (d * y * d) * d) = id := by
      funext y
      calc d * (d * y * d) * d = (d * d) * y * (d * d) := by group
        _ = y := by rw [hd2]; group
    rw [this, Set.image_id]
  have hAd : ∀ x ∈ A, ¬ Commute x d := by
    intro x hx hxd
    have hfix : d * x * d⁻¹ = x := by rw [← hxd.eq]; group
    rw [hAB] at hx
    rcases hx with hxB | hxBu
    · have h1 : d * x * d⁻¹ ∈ Bu := hBd ▸ ⟨x, hxB, rfl⟩
      rw [hfix] at h1
      exact Set.disjoint_left.mp hdis hxB h1
    · have h1 : d * x * d⁻¹ ∈ B := hBud' ▸ ⟨x, hxBu, rfl⟩
      rw [hfix] at h1
      exact Set.disjoint_left.mp hdis h1 hxBu
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_isClass hC.setup.isClass hC.hd hdD)
  have hCd_d : (hC.conj g).d = d := by rw [HypothesisC.conj_d, hg]
  have hαdc : (hC.conj g).alpha ∈ blockClass hC.alpha := by
    rw [HypothesisC.conj_alpha]; exact mem_blockClass_iff.mpr ⟨g, rfl⟩
  have hdαd : d ∈ (hC.conj g).alpha := hCd_d ▸ (hC.conj g).d_mem_alpha
  have hαd : (hC.conj g).alpha = δ :=
    eq_of_mem_of_mem_blockClass hC.isBlock_alpha hαdc hδ.1 ⟨d, hdαd, hdδ⟩
  have hAΓd : A ⊆ Gamma (hC.conj g) := by
    intro x hx
    have hxΓ : x ∈ Gamma hC := hAΓ hx
    rw [mem_Gamma_iff]
    refine ⟨Gamma_subset_D hxΓ, by rw [hCd_d]; exact hAd x hx, ?_⟩
    rw [hαd]
    intro hxδ
    exact not_commute_d_of_mem_Gamma hxΓ (hδ.2.2.2 hC.d hC.d_mem_alpha x hxδ).symm
  have haΓd : a ∈ Gamma (hC.conj g) := hAΓd haA
  have hBsub : B ⊆ GammaComp (hC.conj g) a := by
    have h : GammaComp hC a ⊆ GammaComp (hC.conj g) a ∩ B := by
      refine GammaComp_subset_of_closed ⟨GammaComp_self_mem a, GammaComp_self_mem a⟩ ?_
      rintro z ⟨hz1, hz2⟩ w hw _ hzw
      have hwB : w ∈ B := mem_GammaComp_of_commute haΓ hz2 hw hzw
      have hwA : w ∈ A := by rw [hAB]; exact Or.inl hwB
      exact ⟨mem_GammaComp_of_commute haΓd hz1 (hAΓd hwA) hzw, hwB⟩
    exact fun x hx => (h hx).1
  set O := cenOrbit (hC.conj g) a with hO
  have hBO : B ⊆ O := hBsub.trans (GammaComp_subset_cenOrbit (hC.conj g) hsecond haΓd)
  have hdX : d ∈ cenGen (hC.conj g) := hCd_d ▸ d_mem_cenGen (hC.conj g)
  have hBuO : Bu ⊆ O := by
    rw [← hBd]
    rintro _ ⟨y, hy, rfl⟩
    exact cenOrbit_invariant (hC.conj g) hdX y (hBO hy)
  have hAO : A ⊆ O := by rw [hAB]; exact Set.union_subset hBO hBuO
  have hOA : O.ncard ≤ A.ncard := by
    have ha' : g⁻¹ * a * g ∈ Gamma hC := (mem_Gamma_conj_iff hC g a).mp haΓd
    have hco : O = cimg g (cenOrbit hC (g⁻¹ * a * g)) := by
      rw [hO, ← cenOrbit_conj]; congr 1; group
    rw [hco, ncard_cimg]
    exact hmax _ ⟨_, ha', rfl⟩
  have hAOeq : A = O := Set.eq_of_subset_of_ncard_le hAO hOA (Set.toFinite _)
  let Cu : Set G := (D : Set G) ∩ (Subgroup.centralizer ({hC.d} : Set G) : Set G)
  let Cd : Set G := (D : Set G) ∩ (Subgroup.centralizer ({d} : Set G) : Set G)
  let Y : Subgroup G := Subgroup.closure (Cu ∪ Cd)
  have hYN : Y ≤ Subgroup.normalizer A := by
    rw [show Y = Subgroup.closure (Cu ∪ Cd) from rfl, Subgroup.closure_le]
    rintro z (hz | hz)
    · rw [hAeq]
      exact cenGen_le_normalizer_cenOrbit hC a (Subgroup.subset_closure hz)
    · rw [hAOeq, hO]
      refine cenGen_le_normalizer_cenOrbit (hC.conj g) a (Subgroup.subset_closure ?_)
      rw [hCd_d]; exact hz
  have hdY : hC.d ∈ Y :=
    Subgroup.subset_closure (Or.inl ⟨hC.hd, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
  have hEY : hC.E ⊆ (Y : Set G) :=
    (DalphaStar_subset_cenGen hC).trans (Subgroup.closure_mono Set.subset_union_left)
  have hY_D : Y = Subgroup.closure ((Y : Set G) ∩ D) := by
    apply le_antisymm
    · rw [show Y = Subgroup.closure (Cu ∪ Cd) from rfl, Subgroup.closure_le]
      intro z hz
      have hzD : z ∈ D := by rcases hz with hz | hz <;> exact hz.1
      exact Subgroup.subset_closure ⟨Subgroup.subset_closure hz, hzD⟩
    · rw [Subgroup.closure_le]; exact Set.inter_subset_left
  have hproper : Y ≠ ⊤ := by
    intro h
    exact normalizer_comp_ne_top hC hAΓ ⟨a, haA⟩ (top_le_iff.mp (h ▸ hYN))
  have h68 := inter_D_subset_perp hC hY_D hdY hEY hproper
  have hδne : δ.Nonempty := ⟨d, hdδ⟩
  have hperp : perp D δ ⊆ perp D hC.alpha := by
    intro γ hγ
    rcases mem_perp_iff.mp hγ with hγD | rfl
    · obtain ⟨y, hy⟩ := blockClass_nonempty hδne hγD.1
      have hyD : y ∈ D := hγD.2.1 hy
      have hyd : Commute d y := hγD.2.2.2 d hdδ y hy
      have hyY : y ∈ Y := Subgroup.subset_closure
        (Or.inr ⟨hyD, Subgroup.mem_centralizer_singleton_iff.mpr hyd.eq.symm⟩)
      have hγc : γ ∈ blockClass hC.alpha := mem_blockClass_trans hδ.1 hγD.1
      rcases h68 ⟨hyY, hyD⟩ with hyα | ⟨γ', hγ', hyγ'⟩
      · exact mem_perp_iff.mpr (Or.inr (eq_of_mem_of_mem_blockClass hC.isBlock_alpha hγc
          (mem_blockClass_self _) ⟨y, hy, hyα⟩))
      · have : γ = γ' :=
          eq_of_mem_of_mem_blockClass hC.isBlock_alpha hγc hγ'.1 ⟨y, hy, hyγ'⟩
        exact mem_perp_iff.mpr (Or.inl (this ▸ hγ'))
    · exact mem_perp_iff.mpr (Or.inl hδ)
  have hperpcard : (perp D hC.alpha).ncard ≤ (perp D δ).ncard := by
    obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hδ.1
    rw [hk, ncard_perp_conj hC.setup.normal]
  have hperpeq : perp D δ = perp D hC.alpha :=
    Set.eq_of_subset_of_ncard_le hperp hperpcard (Set.toFinite _)
  have hδV : δ ∈ Valpha D hC.alpha := ⟨hδ.1, hperpeq⟩
  obtain ⟨β, hβc, haβ⟩ :=
    exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha (Gamma_subset_D haΓ)
  have hVne : Valpha D hC.alpha ≠ blockClass hC.alpha := by
    intro hV
    have hβV : β ∈ Valpha D hC.alpha := by rw [hV]; exact hβc
    have hαβ : hC.alpha ∈ perp D β := by
      rw [hβV.2]; exact mem_perp_iff.mpr (Or.inr rfl)
    rcases mem_perp_iff.mp hαβ with hD' | heq
    · exact not_commute_d_of_mem_Gamma haΓ (hD'.2.2.2 a haβ hC.d hC.d_mem_alpha)
    · exact not_mem_alpha_of_mem_Gamma haΓ (by rw [heq]; exact haβ)
  rw [Valpha_eq_singleton_of_isMaxBlock_of_ne hC.setup.normal hC.isMaxBlock_alpha hVne] at hδV
  exact Dalpha.ne_self hδ hδV

theorem cenGen_transitive_AalphaStar_unconditional (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4) :
    ∀ a ∈ AalphaStar D hC.alpha, ∀ b ∈ AalphaStar D hC.alpha,
      ∃ x ∈ Subgroup.closure ((D : Set G) ∩ Subgroup.centralizer ({hC.d} : Set G)),
        x * a * x⁻¹ = b :=
  cenGen_transitive_AalphaStar_of_step3_step4 hC hsecond (hstep3 hC hsecond) (hstep4 hC hsecond)

end CFSG.OddTranspositions
