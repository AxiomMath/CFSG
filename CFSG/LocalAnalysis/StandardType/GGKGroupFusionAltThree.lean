module

public import CFSG.RankThree.PartOne.CTP.AltGen
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.StandardType

open Equiv Equiv.Perm CFSG.RankThree.PartOne.CTP.Alt

section Three

variable {V : Type} [DecidableEq V]

theorem ggSwap_mul_swap_four {P Q R S : V} (hPQ : P ≠ Q) (hPR : P ≠ R) (hPS : P ≠ S)
    (hQR : Q ≠ R) (hQS : Q ≠ S) (hRS : R ≠ S) :
    swap P Q * swap Q R = (swap Q R * swap R S) * (swap P R * swap R S)⁻¹ := by
  have := hPQ.symm
  have := hPR.symm
  have := hPS.symm
  have := hQR.symm
  have := hQS.symm
  have := hRS.symm
  ext v
  simp only [Perm.coe_mul, Function.comp_apply, mul_inv_rev, swap_inv]
  by_cases h1 : v = P
  · subst h1
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h2 : v = Q
  · subst h2
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h3 : v = R
  · subst h3
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h4 : v = S
  · subst h4
    simp [swap_apply_of_ne_of_ne, *]
  simp [swap_apply_of_ne_of_ne, *]

@[expose] def GGContains3 (N : Subgroup (Perm V)) (x y z : V) : Prop :=
  swap x y * swap y z ∈ N

variable {N : Subgroup (Perm V)} {x y z : V}

theorem GGContains3.rot (h : GGContains3 N x y z) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    GGContains3 N y z x := by
  unfold GGContains3 at *
  rwa [swap_mul_swap_rot hxy hyz hxz] at h

theorem GGContains3.flip (h : GGContains3 N x y z) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    GGContains3 N x z y := by
  have := N.inv_mem h
  unfold GGContains3
  rwa [swap_mul_swap_inv hxy hyz hxz] at this

theorem GGContains3.comm {p q r s u : V} (h1 : GGContains3 N p q r) (h2 : GGContains3 N r s u)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s)
    (hqu : q ≠ u) (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u) : GGContains3 N p s r := by
  have := N.mul_mem (N.mul_mem (N.mul_mem h1 h2) (N.inv_mem h1)) (N.inv_mem h2)
  unfold GGContains3
  rwa [swap_commutator hpq hpr hps hpu hqr hqs hqu hrs hru hsu] at this

theorem ggContains3_four {P Q R S : V} (h1 : GGContains3 N Q R S)
    (h2 : GGContains3 N P R S) (hPQ : P ≠ Q) (hPR : P ≠ R) (hPS : P ≠ S) (hQR : Q ≠ R)
    (hQS : Q ≠ S) (hRS : R ≠ S) : GGContains3 N P Q R := by
  unfold GGContains3 at *
  rw [ggSwap_mul_swap_four hPQ hPR hPS hQR hQS hRS]
  exact N.mul_mem h1 (N.inv_mem h2)

@[expose] def GGAltIn (N : Subgroup (Perm V)) (X : Finset V) : Prop :=
  ∀ ⦃a⦄, a ∈ X → ∀ ⦃b⦄, b ∈ X → ∀ ⦃c⦄, c ∈ X → a ≠ b → b ≠ c → a ≠ c → GGContains3 N a b c

theorem GGAltIn.mono {X Y : Finset V} (h : GGAltIn N Y) (hXY : X ⊆ Y) :
    GGAltIn N X :=
  fun _ ha _ hb _ hc hab hbc hac => h (hXY ha) (hXY hb) (hXY hc) hab hbc hac

theorem GGAltIn.mono_left {N' : Subgroup (Perm V)} {X : Finset V} (h : GGAltIn N X)
    (hNN' : N ≤ N') : GGAltIn N' X :=
  fun _ ha _ hb _ hc hab hbc hac => hNN' (h ha hb hc hab hbc hac : swap _ _ * swap _ _ ∈ N)

theorem ggExists_mem_ne_ne {X : Finset V} (hX : 3 ≤ X.card) (a b : V) :
    ∃ x ∈ X, x ≠ a ∧ x ≠ b := by
  obtain ⟨x, hx, hxab⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {a, b}) (t := X) (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxab
  exact ⟨x, hx, hxab.1, hxab.2⟩

theorem ggAltIn_union_mixed {X Y : Finset V} (hX : GGAltIn N X)
    (hY : GGAltIn N Y) (hX3 : 3 ≤ X.card) (hY3 : 3 ≤ Y.card) {a b s : V} (ha : a ∈ X)
    (haY : a ∉ Y) (hb : b ∈ Y) (hbX : b ∉ X) (hsX : s ∈ X) (hsY : s ∈ Y) :
    GGContains3 N a b s := by
  have hab : a ≠ b := by rintro rfl; exact haY hb
  have has : a ≠ s := by rintro rfl; exact haY hsY
  have hbs : b ≠ s := by rintro rfl; exact hbX hsX
  by_cases hc : ∃ c ∈ X, c ∈ Y ∧ c ≠ s
  · obtain ⟨c, hcX, hcY, hcs⟩ := hc
    have hac : a ≠ c := by rintro rfl; exact haY hcY
    have hbc : b ≠ c := by rintro rfl; exact hbX hcX
    exact ggContains3_four (hY hb hsY hcY hbs hcs.symm hbc) (hX ha hsX hcX has hcs.symm hac)
      hab has hac hbs hbc hcs.symm
  · push Not at hc
    obtain ⟨x, hxX, hxa, hxs⟩ := ggExists_mem_ne_ne hX3 a s
    obtain ⟨y, hyY, hyb, hys⟩ := ggExists_mem_ne_ne hY3 b s
    have hxY : x ∉ Y := fun h => hxs (hc x hxX h)
    have hyX : y ∉ X := fun h => hys (hc y h hyY)
    have hxb : x ≠ b := by rintro rfl; exact hbX hxX
    have hay : a ≠ y := by rintro rfl; exact haY hyY
    have hxy : x ≠ y := by rintro rfl; exact hxY hyY
    exact (hX ha hxX hsX hxa.symm hxs has).comm (hY hsY hb hyY hbs.symm hyb.symm hys.symm)
      hxa.symm has hab hay hxs hxb hxy hbs.symm hys.symm hyb.symm

theorem ggAltIn_union {X Y : Finset V} (hX : GGAltIn N X)
    (hY : GGAltIn N Y) (hX3 : 3 ≤ X.card) (hY3 : 3 ≤ Y.card) (hXY : (X ∩ Y).Nonempty) :
    GGAltIn N (X ∪ Y) := by
  obtain ⟨s, hs⟩ := hXY
  rw [Finset.mem_inter] at hs
  obtain ⟨hsX, hsY⟩ := hs
  have key : ∀ a, a ∈ X → a ∉ Y → ∀ b, b ∈ Y → b ∉ X → ∀ c, c ∈ X ∪ Y → a ≠ c → b ≠ c →
      GGContains3 N a b c := by
    intro a ha haY b hb hbX c hc hac hbc
    have hab : a ≠ b := by rintro rfl; exact haY hb
    have has : a ≠ s := by rintro rfl; exact haY hsY
    have hbs : b ≠ s := by rintro rfl; exact hbX hsX
    by_cases hcX : c ∈ X
    · by_cases hcY : c ∈ Y
      · exact ggAltIn_union_mixed hX hY hX3 hY3 ha haY hb hbX hcX hcY
      · have hcs : c ≠ s := by rintro rfl; exact hcY hsY
        have h1 : GGContains3 N b c s := by
          have h0 := ggAltIn_union_mixed hX hY hX3 hY3 hcX hcY hb hbX hsX hsY
          have h0' := h0.flip hbc.symm hbs hcs
          exact (h0'.rot hcs hbs.symm hbc.symm).rot hbs.symm hbc hcs.symm
        exact ggContains3_four h1 (hX ha hcX hsX hac hcs has) hab hac has hbc hbs hcs
    · have hcY : c ∈ Y := (Finset.mem_union.mp hc).resolve_left hcX
      have hcs : c ≠ s := by rintro rfl; exact hcX hsX
      exact ggContains3_four (hY hb hcY hsY hbc hcs hbs)
        (ggAltIn_union_mixed hX hY hX3 hY3 ha haY hcY hcX hsX hsY) hab hac has hbc hbs hcs
  intro u hu v hv w hw huv hvw huw
  by_cases huY : u ∈ Y
  · by_cases hvY : v ∈ Y
    · by_cases hwY : w ∈ Y
      · exact hY huY hvY hwY huv hvw huw
      · have hwX : w ∈ X := (Finset.mem_union.mp hw).resolve_right hwY
        by_cases huX : u ∈ X
        · by_cases hvX : v ∈ X
          · exact hX huX hvX hwX huv hvw huw
          · have h := key w hwX hwY v hvY hvX u hu (Ne.symm huw) (Ne.symm huv)
            exact (h.flip (Ne.symm hvw) huv.symm huw.symm).rot huw.symm huv hvw.symm
        · have h := key w hwX hwY u huY huX v hv (Ne.symm hvw) huv
          exact h.rot huw.symm huv hvw.symm
    · have hvX : v ∈ X := (Finset.mem_union.mp hv).resolve_right hvY
      by_cases huX : u ∈ X
      · by_cases hwX : w ∈ X
        · exact hX huX hvX hwX huv hvw huw
        · have hwY' : w ∈ Y := (Finset.mem_union.mp hw).resolve_left hwX
          have h := key v hvX hvY w hwY' hwX u hu (Ne.symm huv) (Ne.symm huw)
          exact (h.rot hvw (Ne.symm huw) (Ne.symm huv)).rot (Ne.symm huw) huv (Ne.symm hvw)
      · have h := key v hvX hvY u huY huX w hw hvw huw
        exact ((h.flip huv.symm huw hvw).rot hvw huw.symm huv.symm).rot huw.symm huv hvw.symm
  · have huX : u ∈ X := (Finset.mem_union.mp hu).resolve_right huY
    by_cases hvX : v ∈ X
    · by_cases hwX : w ∈ X
      · exact hX huX hvX hwX huv hvw huw
      · have hwY : w ∈ Y := (Finset.mem_union.mp hw).resolve_left hwX
        have h := key u huX huY w hwY hwX v hv huv (Ne.symm hvw)
        exact h.flip huw (Ne.symm hvw) huv
    · have hvY : v ∈ Y := (Finset.mem_union.mp hv).resolve_left hvX
      exact key u huX huY v hvY hvX w hw huw hvw

theorem ggAltIn_map {X : Finset V} (hX : GGAltIn N X) {g : Perm V} (hg : g ∈ N) :
    GGAltIn N (X.map g.toEmbedding) := by
  intro a ha b hb c hc hab hbc hac
  simp only [Finset.mem_map_equiv] at ha hb hc
  have hab' : g.symm a ≠ g.symm b := fun h => hab (g.symm.injective h)
  have hbc' : g.symm b ≠ g.symm c := fun h => hbc (g.symm.injective h)
  have hac' : g.symm a ≠ g.symm c := fun h => hac (g.symm.injective h)
  have h := hX ha hb hc hab' hbc' hac'
  unfold GGContains3 at h ⊢
  have e1 := swap_apply_apply g (g.symm a) (g.symm b)
  have e2 := swap_apply_apply g (g.symm b) (g.symm c)
  simp only [Equiv.apply_symm_apply] at e1 e2
  rw [e1, e2]
  have := N.mul_mem (N.mul_mem hg h) (N.inv_mem hg)
  simpa [mul_assoc] using this

theorem ggAltIn_image {X : Finset V} (hX : GGAltIn N X) {g : Perm V} (hg : g ∈ N) :
    GGAltIn N (X.image g) := by
  have h : X.image g = X.map g.toEmbedding := by
    ext v
    simp [Finset.mem_map_equiv, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hv
      exact ⟨g.symm v, hv, by simp⟩
  rw [h]
  exact ggAltIn_map hX hg

variable [Fintype V]

theorem ggAltIn_of_commute {a : Perm V} (hNa : ∀ k ∈ alternatingGroup V, k * a = a * k → k ∈ N)
    {X : Finset V} (hX : ∀ v ∈ X, a v = v) : GGAltIn N X := by
  intro x hx y hy z hz hxy hyz hxz
  have hnd : [x, y, z].Nodup := by simp [hxy, hyz, hxz]
  have hsupp := Equiv.Perm.support_swap_mul_swap hnd
  apply hNa
  · have h3 : (swap x y * swap y z).IsThreeCycle := by
      rw [← card_support_eq_three_iff, hsupp]
      simp [hxy, hyz, hxz]
    exact h3.mem_alternatingGroup
  · have hd : Disjoint (swap x y * swap y z) a := by
      rw [disjoint_iff_disjoint_support, hsupp, Finset.disjoint_left]
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rw [Equiv.Perm.notMem_support]
      rcases hv with rfl | rfl | rfl
      · exact hX _ hx
      · exact hX _ hy
      · exact hX _ hz
    exact hd.commute.eq

theorem ggAlternatingGroup_le_of_altIn (h : GGAltIn N Finset.univ) : alternatingGroup V ≤ N := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro σ hσ
  have hσ3 : σ.IsThreeCycle := hσ
  obtain ⟨c, hc⟩ : σ.support.Nonempty := by
    rw [← Finset.card_pos, hσ3.card_support]
    norm_num
  have h1 := (hσ3.eq_swap_mul_swap_iff_mem_support (a := c)).mpr hc
  obtain ⟨hc1, hc2⟩ := List.nodup_cons.mp (hσ3.nodup_iff_mem_support.mpr hc)
  obtain ⟨hc3, -⟩ := List.nodup_cons.mp hc2
  simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hc1 hc3
  have h3 := h (Finset.mem_univ c) (Finset.mem_univ (σ c)) (Finset.mem_univ (σ (σ c)))
    hc1.1 hc3 hc1.2
  unfold GGContains3 at h3
  rw [← h1] at h3
  exact h3

end Three

section Commutator

variable {V : Type} [DecidableEq V]

theorem ggCommutator_eq_swap_mul_swap {c d : Perm V} {r : V}
    (hr : ∀ z, c z ≠ z → d z ≠ z → z = r) (hcr : c r ≠ r) (hdr : d r ≠ r) :
    c * d * c⁻¹ * d⁻¹ = swap r (c r) * swap (c r) (d r) := by
  have hca : c (c r) ≠ c r := fun h => hcr (c.injective h)
  have hdb : d (d r) ≠ d r := fun h => hdr (d.injective h)
  have hda : d (c r) = c r := by
    by_contra h
    exact hcr (hr _ hca h)
  have hcb : c (d r) = d r := by
    by_contra h
    exact hdr (hr _ h hdb)
  have hab : c r ≠ d r := by
    intro h
    apply hdb
    rw [← h, hda]
  set r₁ := c⁻¹ r with hr₁
  have hcr₁ : c r₁ = r := by simp [hr₁]
  have hr₁r : r₁ ≠ r := fun h => hcr (by rw [← h, hcr₁, h])
  have hdr₁ : d r₁ = r₁ := by
    by_contra h
    exact hr₁r (hr _ (by rw [hcr₁]; exact hr₁r.symm) h)
  set r₂ := d⁻¹ r with hr₂
  have hdr₂ : d r₂ = r := by simp [hr₂]
  have hr₂r : r₂ ≠ r := fun h => hdr (by rw [← h, hdr₂, h])
  have hcr₂ : c r₂ = r₂ := by
    by_contra h
    exact hr₂r (hr _ h (by rw [hdr₂]; exact hr₂r.symm))
  ext z
  simp only [Perm.coe_mul, Function.comp_apply]
  by_cases hz : z = r
  · subst hz
    have e1 : d⁻¹ z = r₂ := rfl
    have e2 : c⁻¹ r₂ = r₂ := by rw [Perm.inv_eq_iff_eq, hcr₂]
    rw [e1, e2, hdr₂, swap_apply_of_ne_of_ne (Ne.symm hcr) (Ne.symm hdr), swap_apply_left]
  by_cases hza : z = c r
  · subst hza
    have e1 : d⁻¹ (c r) = c r := by rw [Perm.inv_eq_iff_eq, hda]
    have e2 : c⁻¹ (c r) = r := by simp
    rw [e1, e2, hcb, swap_apply_left,
      swap_apply_of_ne_of_ne hdr (Ne.symm hab)]
  by_cases hzb : z = d r
  · subst hzb
    have e1 : d⁻¹ (d r) = r := by simp
    rw [e1]
    change c (d r₁) = _
    rw [hdr₁, hcr₁, swap_apply_right, swap_apply_right]
  rw [swap_apply_of_ne_of_ne hza hzb, swap_apply_of_ne_of_ne hz hza]
  by_cases hdz : d z = z
  · have e1 : d⁻¹ z = z := by rw [Perm.inv_eq_iff_eq, hdz]
    rw [e1]
    by_cases hcz : c z = z
    · have e2 : c⁻¹ z = z := by rw [Perm.inv_eq_iff_eq, hcz]
      rw [e2, hdz, hcz]
    · set y := c⁻¹ z with hy
      have hcy : c y = z := by simp [hy]
      have hyz : y ≠ z := fun h => hcz (by rw [← h, hcy, h])
      have hyr : y ≠ r := fun h => hza (by rw [← hcy, h])
      have hdy : d y = y := by
        by_contra h
        exact hyr (hr _ (by rw [hcy]; exact hyz.symm) h)
      rw [hdy, hcy]
  · set w := d⁻¹ z with hw
    have hdw : d w = z := by simp [hw]
    have hwz : w ≠ z := fun h => hdz (by rw [← h, hdw, h])
    have hwr : w ≠ r := fun h => hzb (by rw [← hdw, h])
    have hcw : c w = w := by
      by_contra h
      exact hwr (hr _ h (by rw [hdw]; exact hwz.symm))
    have e2 : c⁻¹ w = w := by rw [Perm.inv_eq_iff_eq, hcw]
    have hcz : c z = z := by
      by_contra h
      exact hz (hr _ h hdz)
    rw [e2, hdw, hcz]

end Commutator

end CFSG.StandardType
